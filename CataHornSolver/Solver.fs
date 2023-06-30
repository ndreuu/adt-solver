module ProofBased.Solver

open CataHornSolver
open Microsoft.FSharp.Core
open Microsoft.Z3
open Z3Interpreter.AST

let mutable dbgPath = None

open System
open System.Collections.Generic
open System.IO
open Microsoft.Z3
open SMTLIB2

open Tree.Tree
open ProofBased.Utils
open Z3Interpreter.Interpreter
open Z3Interpreter.AST
open Approximation

let emptyEnv argss =
  { ctxSlvr = new Context (argss |> dict |> Dictionary)
    ctxVars = Map.empty
    ctxFuns = Map.empty
    ctxDecfuns = Map.empty
    actives = []
    ctxDataType = Map.empty }

let proofTree hProof =
  let rec helper (HyperProof (_, hyperProofs, head)) =
    match hyperProofs with
    | [] -> head |> smtExpr2expr |> (fun x -> Node (x, []))
    | _ -> Node (head |> smtExpr2expr, hyperProofs |> List.map helper)

  helper hProof

let notAppRestrictions =
  let rec helper acc =
    function
    | Eq _
    | Lt _
    | Gt _
    | Le _
    | Ge _
    | Not _ as c -> c :: acc
    | Apply (name, [ x; y ]) as c when name = "distinct" -> Not (Eq (x, y)) :: acc
    | And exprs -> Array.fold helper acc exprs
    | Or exprs -> Array.fold helper acc exprs
    | ForAll (_, expr)
    | Implies (expr, _) -> helper acc expr

    | _ -> acc

  helper []

let appRestrictions =
  let rec helper acc =
    function
    | App _ as app -> app :: acc
    | And exprs -> Array.fold helper acc exprs
    | Or exprs -> Array.fold helper acc exprs
    | Not expr
    | ForAll (_, expr)
    | Implies (expr, _) -> helper acc expr
    | _ -> acc

  helper []

let impliesAsserts clarify asserts name =
  asserts
  |> List.filter (function
    | Assert (ForAll (_, Implies (_, App (n, _))))
    | Assert (Implies (_, App (n, _))) when n = name -> true
    | _ -> false)
  |> clarify

let axiomAsserts clarify asserts name =
  asserts
  |> List.filter (function
    | Assert (Implies (body, App (n, _)))
    | Assert (ForAll (_, Implies (body, App (n, _)))) when body |> appRestrictions |> List.isEmpty && n = name -> true
    | Assert (App (n, _))
    | Assert (ForAll (_, App (n, _))) when n = name -> true
    | _ -> false)
  |> clarify

let queryAssert clarify asserts =
  asserts
  |> List.filter (function
    | Assert (ForAll (_, Implies (_, Bool false)))
    | Assert (Implies (_, Bool false)) -> true
    | _ -> false)
  |> clarify

let renameVar =
  let rec helper oldName newName =
    let this x = helper oldName newName x

    function
    | Var name when name = oldName -> Var newName
    | Eq (expr1, expr2) -> Eq (this expr1, this expr2)
    | Lt (expr1, expr2) -> Lt (this expr1, this expr2)
    | Gt (expr1, expr2) -> Gt (this expr1, this expr2)
    | Le (expr1, expr2) -> Le (this expr1, this expr2)
    | Ge (expr1, expr2) -> Ge (this expr1, this expr2)
    | Add (expr1, expr2) -> Add (this expr1, this expr2)
    | Subtract (expr1, expr2) -> Subtract (this expr1, this expr2)
    | Neg expr -> Neg (this expr)
    | Mul (expr1, expr2) -> Mul (this expr1, this expr2)
    | Mod (expr1, expr2) -> Mod (this expr1, this expr2)
    | Implies (expr1, expr2) -> Implies (this expr1, this expr2)
    | And exprs -> And (Array.map this exprs)
    | Or exprs -> Or (Array.map this exprs)
    | Not expr -> Not (this expr)
    | Apply (name, exprs) -> Apply (name, exprs |> List.map this)
    | ForAll (names, expr) -> ForAll (names |> Array.map (fun x -> if x = oldName then newName else x), this expr)
    | App (name, exprs) -> App ((if name = oldName then newName else name), exprs |> List.map this)
    | Ite (expr1, expr2, expr3) -> Ite (this expr1, this expr2, this expr3)
    | expr -> expr

  helper

let vars =
  let rec helper acc =
    function
    | Var _ as v -> v :: acc
    | Eq (expr1, expr2)
    | Lt (expr1, expr2)
    | Gt (expr1, expr2)
    | Le (expr1, expr2)
    | Ge (expr1, expr2)
    | Add (expr1, expr2)
    | Mul (expr1, expr2)
    | Mod (expr1, expr2)
    | Subtract (expr1, expr2)
    | Implies (expr1, expr2) -> helper (helper acc expr1) expr2
    | ForAll (_, expr)
    | Neg expr
    | Not expr -> helper acc expr
    | Ite (expr1, expr2, expr3) -> helper (helper (helper acc expr1) expr2) expr3
    | App (_, exprs) -> List.fold helper acc exprs
    | And exprs
    | Or exprs -> Array.fold helper acc exprs
    | Apply (_, exprs) -> List.fold helper acc exprs
    | Int _
    | Bool _ -> acc

  helper []

type apps = Map<Name, Expr list>

let getApp name (apps: apps) =
  apps
  |> Map.find name
  |> fun exprs ->
      let apps' value =
        apps
        |> Map.change name (function
          | None -> None
          | _ -> Some value)

      match exprs with
      | App (_, args) :: tl -> (args, apps' tl)
      | _ -> ([], apps)

let forAll expr =
  let rec helper acc =
    function
    | Int _
    | Bool _ -> acc
    | Eq (expr1, expr2)
    | Lt (expr1, expr2)
    | Gt (expr1, expr2)
    | Le (expr1, expr2)
    | Ge (expr1, expr2)
    | Add (expr1, expr2)
    | Subtract (expr1, expr2)
    | Mod (expr1, expr2)
    | Implies (expr1, expr2)
    | Mul (expr1, expr2) -> helper (helper acc expr1) expr2
    | App (_, exprs) -> List.fold helper acc exprs
    | And exprs
    | Or exprs -> Array.fold helper acc exprs
    | ForAll (_, expr)
    | Not expr
    | Neg expr -> helper acc expr
    | Var n -> acc |> Set.add n
    | Apply (_, exprs) -> List.fold helper acc exprs
    | Ite (expr1, expr2, expr3) -> List.fold helper acc [ expr1; expr2; expr3 ]

  ForAll(helper Set.empty expr |> Set.toArray, expr)

let defFunBody args i =
  List.zip args [ i + 1 .. i + 1 + args.Length - 1 ]
  |> List.map (fun (n, i) -> Mul (Apply ($"c_{i}", []), Var n))
  |> List.fold (fun (acc, i) arg -> (Add (acc, arg), i + 1)) ((Apply ($"c_{i}", [])), i)

let branch i =
  function
  | Def (n, args, _, body) when args.Length > 0 ->
    let cond, i' = defFunBody args i |> fun (e, i) -> (Eq (e, Int 0), i)

    let elseBody, _ = defFunBody args (i' + 1)

    Def (n, args, Integer, Ite (cond, body, elseBody))
  | otherwise -> otherwise

let redlog definitions formula =
  match Redlog.runRedlog definitions formula with
  | Ok v -> Assert(smtExpr2expr' v)
  | Error e -> failwith $"redlog-output: {e}"

let decConst =
  function
  | Def (n, _, _, _) -> DeclIntConst n
  | otherwise -> otherwise

let mapTreeOfLists f = Tree.fmap (List.map f)

let rec assertsTreeNew asserts consts decs =
  function
  | Node (Apply (name, _), []) ->
    printfn $">>{name}"
    let axioms = axiomAsserts id asserts name
    for x in axioms do
      printfn $"{axioms}"
    Node (axioms, [])
  | Node (Apply (name, _), ts) ->
    let value =
      name
      |> impliesAsserts id asserts
    
    let appRestrictions =
      List.choose
        (function
          | Assert (ForAll (_, x))
          | Assert x ->
            appRestrictions x 
            |> List.choose (function App (n, _) -> Some n | _ -> None) |> Some | _ -> None) value
        |> List.concat
    
    let kidNames = ts |> List.choose (function Node (Apply (name, _), _) -> Some name | _ -> None)

    let countOf x = List.filter (fun y -> y = x) >> List.length
    
    let genVals src diff =
      List.choose
        (fun x -> countOf x src |> flip List.replicate x |> Some) diff
      |> List.concat
    
    let restoreExistsKids (kidNames: _ list) (source: _ list)   =
      let rec helper acc =
        function
          | [] -> acc
          | x :: xs -> helper (acc @ List.replicate (countOf x source - countOf x kidNames) x) xs
      helper kidNames []
    
    let recoveredKids =
      List.except kidNames appRestrictions
      |> genVals appRestrictions
      |> List.append (restoreExistsKids appRestrictions kidNames) 
      |> List.map (fun n -> Node (Apply (n, []), []))
      |> List.append ts

    Node (value, recoveredKids |> List.map (assertsTreeNew asserts consts decs))
  | Node (Bool false, ts) ->
    let query = queryAssert (List.head >> List.singleton) asserts
    
    let appRestrictions =
      List.choose
        (function
          | Assert (ForAll (_, x))
          | Assert x ->
            x |> appRestrictions
            |> List.choose (function App (n, _) -> Some n | _ -> None) |> Some | _ -> None) query
        |> List.concat
    let kidNames = ts |> List.choose (function Node (Apply (name, _), _) -> Some name | _ -> None)
    
    let countOf x = List.filter (fun y -> y = x) >> List.length

    let genVals src diff =
      List.choose
        (fun x -> countOf x src |> flip List.replicate x |> Some) diff
      |> List.concat
    
    let restoreExistsKids (kidNames: _ list) (source: _ list)   =
      let rec helper acc =
        function
          | [] -> acc
          | x :: xs -> helper (acc @ List.replicate (countOf x source - countOf x kidNames) x) xs
      helper kidNames []
    
    let recoveredKids =
      List.except kidNames appRestrictions
      |> fun x ->
        for x in appRestrictions do
          printfn $" appRestrictions:: {x}"
        
        for x in kidNames do
          printfn $" kidNames:: {x}"

        for x in x do
          printfn $" diff:: {x}"
        x
      |> genVals appRestrictions
      |> fun x -> printfn $"{x}"; x 
      |> List.append (restoreExistsKids appRestrictions kidNames) 
      |> fun xs ->
        for x in xs do printfn $"REC {x}"
        xs
      |> List.map (fun n -> Node (Apply (n, []), []))
      |> fun xs->
        for x in xs do printfn $"NEW LEF {x}"
        xs
      |> List.append ts
      |> fun xs->
        for x in xs do printfn $"BRANCH {x}"
        xs
      
    Node (query,  List.map (assertsTreeNew asserts consts decs) recoveredKids)
  | _ -> __unreachable__ ()

let treeOfExprs =
  Tree.fmap (List.choose (function
      | Assert (ForAll (_, x)) -> Some x
      | Assert x -> Some x
      | _ -> None))

let uniqVarNames =
  let rec varNames acc =
    function
    | Var name -> acc |> Set.add name
    | Int _
    | Bool _ -> acc
    | Eq (expr1, expr2)
    | Lt (expr1, expr2)
    | Gt (expr1, expr2)
    | Le (expr1, expr2)
    | Ge (expr1, expr2)
    | Add (expr1, expr2)
    | Subtract (expr1, expr2)
    | Mul (expr1, expr2)
    | Mod (expr1, expr2)
    | Subtract (expr1, expr2)
    | Implies (expr1, expr2) -> varNames (varNames acc expr1) expr2
    | ForAll (_, expr)
    | Neg expr
    | Not expr -> varNames acc expr
    | App (_, exprs) -> List.fold varNames acc exprs
    | And exprs
    | Or exprs -> Array.fold varNames acc exprs
    | Apply (_, exprs) -> List.fold varNames acc exprs
    | Ite (expr1, expr2, expr3) -> List.fold varNames acc [ expr1; expr2; expr3 ]

  let varNamesMany (exprs: Expr list) = List.map (varNames Set.empty) exprs

  let rename i exprs =
    Set.fold (fun (acc, i) n -> (renameVar n $"x{i}" acc, i + 1)) (exprs, i)

  let renameMany idx (exprs: Expr list) (names: Set<Name> list) =
    let exprsNames = List.zip exprs names

    List.foldBack
      (fun (expr, names) (acc, i) ->
        let expr', i' = (rename i expr names)
        (expr' :: acc), i')
      exprsNames
      ([], idx)

  let rec numLine i (line: Expr list tree list) =
    List.foldBack
      (fun (x: Expr list tree) (acc, i) ->
        match x with
        | Node (v, ts) ->
          varNamesMany v
          |> renameMany i v
          |> fun (e, i') ->
              let ts', i'' = numLine i' ts
              (Node (e, ts') :: acc, i''))
      line
      ([], i)

  function
  | Node (x, ts) ->
    let x', i = varNamesMany x |> renameMany 0 x
    Node (x', numLine i ts |> fst)

let argsBind x ys =
  let bind = List.map2 (fun x y -> Eq (x, y))
  match x with
  | App (name, args) when not <| List.isEmpty args ->
    ys
    |> List.choose (function App (n, args') when n = name -> Some(bind args args') | _ -> None)
    |> List.map Expr.And
    |> Expr.Or |> List.singleton
  | _ -> []

let conclusion =
  function
  | Implies (_, expr) -> expr
  | otherwise -> otherwise

let collectApps (kids: Expr list list) =
  let add k v map =
    map
    |> Map.change k (function
      | Some vs -> Some (v :: vs)
      | None -> Some [ v ])

  kids
  |> List.map (List.map conclusion)
  |> List.fold
    (fun acc -> function App (name, _) :: _ as apps -> add name apps acc | _ -> acc)
    Map.empty
  |> Map.map (fun _ -> List.rev)

let singleArgsBinds appsOfSingleParent (kids: Expr list list) =
  let get k map =
    printfn $"{k}"
    (map |> Map.find k |> List.head,
     map |> Map.change k (function Some (_ :: vs) -> Some vs | _ -> None))

  appsOfSingleParent
  |> List.fold
    (fun (acc, apps as otherwise) ->
      function
      | App (name, _) as x ->
        let ys, apps' = get name apps
        (acc @ (argsBind x ys), apps')
      | _ -> otherwise)
    ([], collectApps kids)
  |> fst
  |> Expr.And

let argsBinds appsOfParents kids =
  appsOfParents
  |> List.map (fun parent -> singleArgsBinds parent kids)
  |> Expr.Or

let rec resolvent = function
  | Node (_, []) -> []
  | Node (xs, ts) ->
    let kids = List.map Tree.value ts
    let notAppRestrictions = List.collect notAppRestrictions xs |> Expr.And
    let appRestrictions = List.map appRestrictions xs
    argsBinds appRestrictions kids :: notAppRestrictions :: List.collect resolvent ts


module Simplifier =
  let emptyFilter =
    Array.filter (function
      | And [||]
      | Or [||] -> false
      | _ -> true)

  let rec rmEmpty =
    function
    | And args -> args |> emptyFilter |> Array.map rmEmpty |> And
    | Or args -> args |> emptyFilter |> Array.map rmEmpty |> Or
    | otherwise -> otherwise

  let rec private rmNestedOrs =
    function
    | Or [| x |] -> x
    | Or args ->
      args
      |> Array.toList
      |> List.fold
        (fun acc arg ->
          match arg with
          | Or args' ->
            Array.toList args'
            |> List.map (rmNestedAnds >> rmNestedOrs)
            |> fun x -> x @ acc
          | otherwise -> (rmNestedAnds >> rmNestedOrs <| otherwise) :: acc)
        []
      |> List.rev
      |> List.toArray
      |> Or
    | And _ as andExpr -> rmNestedAnds andExpr
    | otherwise -> otherwise

  and private rmNestedAnds =
    function
    | And [| x |] -> x
    | And args ->
      args
      |> Array.toList
      |> List.fold
        (fun acc arg ->
          match arg with
          | And args' ->
            Array.toList args'
            |> List.map (rmNestedAnds >> rmNestedOrs)
            |> fun x -> x @ acc
          | otherwise -> (rmNestedAnds >> rmNestedOrs <| otherwise) :: acc)
        []
      |> List.rev
      |> List.toArray
      |> And
    | Or _ as orExpr -> rmNestedOrs orExpr
    | otherwise -> otherwise

  let normalize = rmNestedAnds >> rmEmpty


  let private eqVarConditions =
    let rec helper acc =
      function
      | And args -> args |> Array.toList |> List.fold helper acc
      | Eq (Var _, _)
      | Eq (_, Var _) as eq -> eq :: acc
      | Or _
      | _ -> acc

    helper []

  let add (k: Expr) (v: Expr) used (t: Expr list list) =
    let kv =
      match k with
      | _ when used |> List.contains k -> Some (k, v)
      | _ when used |> List.contains v -> Some (v, k)
      | _ -> None


    match kv with
    | Some (k, v) when used |> List.contains k && used |> List.contains v -> (t, used)
    | Some (k, v) ->
      let t' =
        t
        |> List.map (function
          | xs when xs |> List.contains k -> v :: xs
          | xs -> xs)

      (t', v :: used)
    | None -> ([ k; v ] :: t, k :: v :: used)


  let map vs =
    let applyTester =
      function
      | Apply _ -> true
      | _ -> false

    let applies = List.filter applyTester
    let vars = List.filter (not << applyTester)

    let helper vs =
      List.fold
        (fun (acc, used) eq ->
          match eq with
          | Eq (x, y) -> add x y used acc
          | _ -> (acc, used))
        ([], [])
        vs

    helper vs
    |> fst
    |> List.map (fun xs ->
      xs
      |> applies
      |> function
        | [] -> (xs, List.head xs)
        | vs -> (vars xs, List.head vs))


  let substitute v (map: (Expr list * Expr) list) =
    map
    |> List.fold (fun acc (vars, v) -> List.fold (fun acc var -> substituteVar var v acc) acc vars) v

  let substituteNew =
    let rec helper m =
      function
      | Or args -> Or (Array.map (helper []) args)
      | And args as andExpr ->
        let m' = andExpr |> eqVarConditions |> map
        And (Array.map (helper m') args)
      | expr -> substitute expr m

    helper []

  let rec rmEqs =
    function
    | And args ->
      And (
        args
        |> Array.filter (function
          | Eq (x, y) when x = y -> false
          | _ -> true)
        |> Array.map rmEqs
      )
    | Or args ->
      Or (
        args
        |> Array.filter (function
          | Eq (x, y) when x = y -> false
          | _ -> true)
        |> Array.map rmEqs
      )
    | otherwise -> otherwise


module TypeClarification =
  type exprType =
    | Any
    | Int
    | Bool
    | ADT of string
    static member (+) (x, y) =
      match x, y with
      | Any, t
      | t, Any -> t
      | x, y when x = y -> x 
      | _ -> failwith "wrong types"
  
  let rec constrFuns2apps (adts: Map<ident,(symbol * Type list)>) =
    function 
      | Eq (e1, e2) -> Eq (constrFuns2apps adts e1, constrFuns2apps adts e2)
      | Lt (e1, e2) -> Lt (constrFuns2apps adts e1, constrFuns2apps adts e2)
      | Gt (e1, e2) -> Gt (constrFuns2apps adts e1, constrFuns2apps adts e2)
      | Le (e1, e2) -> Le (constrFuns2apps adts e1, constrFuns2apps adts e2)
      | Ge (e1, e2) -> Ge (constrFuns2apps adts e1, constrFuns2apps adts e2)
      | Mod (e1, e2) -> Mod (constrFuns2apps adts e1, constrFuns2apps adts e2)
      | Add (e1, e2) -> Add (constrFuns2apps adts e1, constrFuns2apps adts e2)
      | Subtract (e1, e2) -> Subtract (constrFuns2apps adts e1, constrFuns2apps adts e2)
      | Neg e -> Neg (constrFuns2apps adts e)
      | Mul (e1, e2) -> Mul (constrFuns2apps adts e1, constrFuns2apps adts e2)
      | And exprs -> And (Array.map (constrFuns2apps adts) exprs)
      | Or exprs -> Or (Array.map (constrFuns2apps adts) exprs)
      | Not e -> Not (constrFuns2apps adts e)
      | Implies (e1, e2) -> Subtract (constrFuns2apps adts e1, constrFuns2apps adts e2)
      | Apply (n, es) when adts |> Map.containsKey n -> App (n, List.map (constrFuns2apps adts) es)
      | App (n, es) -> App (n, List.map (constrFuns2apps adts) es)
      | ForAll (ns, e) -> ForAll (ns, constrFuns2apps adts e) 
      | ForAllTyped (vars, e) -> ForAllTyped (vars, constrFuns2apps adts e)
      | Ite (e1, e2, e3) -> Ite (constrFuns2apps adts e1, constrFuns2apps adts e2, constrFuns2apps adts e3) 
      | otherwise -> otherwise 
    
  let argTypes (adts: Map<ident,(symbol * Type list)>) = 
    let rec helper acc =
      function
        | App (name, args) when adts |> Map.containsKey name ->
          let _, argTypes = adts |> Map.find name
          List.fold2 (fun acc arg t -> match arg with Var n -> acc |> Set.add (n, t) | _ -> helper acc arg) acc (args) argTypes
        | App (_, exprs) -> List.fold helper acc exprs
        | Apply (_, args) ->
            List.fold (fun acc arg -> match arg with Var n -> acc |> Set.add (n, Integer) | _ -> helper acc arg) acc args        
        | Lt (e1, e2)
        | Gt (e1, e2)
        | Le (e1, e2)
        | Ge (e1, e2)
        | Mod (e1, e2)
        | Add (e1, e2)
        | Subtract (e1, e2)
        | Mul (e1, e2)
        | Implies (e1, e2)
        | Eq (e1, e2) -> helper acc e2 |> flip helper e1 
        | Not e
        | Neg e -> helper acc e
        | And exprs
        | Or exprs -> Array.fold helper acc exprs
        | _ -> acc
    helper Set.empty >> Map

  let predicateArgTypes (adts: Map<ident,(symbol * Type list)>) typedVars =
    let rec helper adts = 
      function
        | Eq (expr1, expr2) 
        | Lt (expr1, expr2)
        | Gt (expr1, expr2)
        | Le (expr1, expr2)
        | Ge (expr1, expr2)
        | Mod (expr1, expr2)
        | Add (expr1, expr2)
        | Subtract (expr1, expr2)
        | Implies (expr1, expr2) 
        | Mul (expr1, expr2) -> helper adts expr1 + helper adts expr2
        | Neg _ -> Int 
        | Not _ -> Bool
        | Or exprs
        | And exprs -> Array.fold (fun acc x -> acc + helper adts x) Any exprs
        | Var n when typedVars |> Map.containsKey n ->
          match typedVars |> Map.find n with
          | Integer -> Int
          | Boolean -> Bool
          | Type.ADT name -> ADT name
        | Var _ -> Any
        | App (name, _) when adts |> Map.containsKey name ->
          adts
          |> Map.tryFind name
          |> function
            | None _ -> Any
            | Some (tName, _) -> ADT tName  
        | Expr.Int _
        | Apply _ -> Int   
        | Expr.Bool _ 
        | ForAll _ 
        | App _ -> Bool
        | Ite (_, expr2, expr3) -> helper adts expr2 + helper adts expr3
    
    helper adts >> function ADT tName -> Some (Type.ADT tName) | Int -> Some Integer | Bool -> Some Boolean | _ -> None   
  
  let farmTypes (adts: Map<ident,(symbol * Type list)>) typedVars =
    let varNames = List.choose (function Var n -> n |> Some | _ -> None)
    let rec helper (acc: _ Set) expr =
      match expr with
        | Eq (e1, e2)
        | Gt (e1, e2) 
        | Lt (e1, e2)
        | Le (e1, e2)
        | Ge (e1, e2) ->
          let names = Set.union (Set (vars e1 |> varNames )) (Set (vars e2 |> varNames ))
          let nameTypes = 
            names
            |> Set.filter (fun n -> typedVars |> Map.containsKey n |> not)
            |> Set.map (fun n -> (n, predicateArgTypes adts typedVars expr))
            |> Set.toList
            |> List.choose (fun (x, y) -> match y with Some y' -> Some (x, y') | None -> None)
          acc |> Set.union (Set nameTypes)
        | Not expr -> helper acc expr
        | And exprs
        | Or exprs -> Array.fold helper acc exprs
        | a -> printfn $"{a}"; __unreachable__ ()
    helper Set.empty   
  
  let eqs =
    let rec helper acc =
      function
        | Eq (Var _, Var _) as eq -> acc |> Set.add eq 
        | Eq _ -> acc  
        | Not expr -> helper acc expr
        | And exprs
        | Or exprs -> Array.fold helper acc exprs
        | _ -> acc
    helper Set.empty

  let transitiveEqs (eqs: Expr Set) (typedVars: (Name * Type) Set) =
    let clause name eqs =
      let rec helper name (acc: Name list) used =
        eqs
        |> List.fold 
             (fun acc -> function
                | Eq (Var x, Var y) | Eq (Var y, Var x) when x = name && used |> Set.contains y |> not ->
                  (helper y (y :: acc) (used |> Set.add y))  
                | _ -> acc)
             acc
      helper name []        
        
    let eqs = Set.toList eqs
    let typedVarNames, _ = Set.toList typedVars |> List.unzip
    
    eqs
    |> List.choose
         (function
            | Eq (Var x, Var y)
            | Eq (Var y, Var x) when
              typedVarNames |> List.contains x &&
              typedVarNames |> List.contains y |> not -> Some (Map typedVars |> Map.find x, clause x eqs (Set [ x ]))
            | _ -> None)
    |> List.map (fun (t, ns) -> ns |> List.map (fun n -> (n, t)))
    |> List.concat
    |> Set 
    |> Set.union typedVars 
  
  let appendIntVars (names: Name list) vars =
    (Set names |> Set.difference <| (Set.map fst vars))
    |> Set.map (fun n -> (n, Integer))
    |> Set.union vars
  
  let clarify  (adts: Map<ident,(symbol * Type list)>) expr varNames =
    let appConstrExpr = constrFuns2apps adts expr
    let typedVars =
      constrFuns2apps adts appConstrExpr
      |> argTypes adts
    let ss = farmTypes adts typedVars appConstrExpr
    let vars = typedVars |> Map.toList |> Set |> Set.union ss

    (appConstrExpr, transitiveEqs (eqs appConstrExpr) vars |> appendIntVars varNames)
    
  
  let rec expr2adtSmtExpr adtConstrs =
    function
    | Expr.Int i -> Number i
    | Expr.Bool b -> BoolConst b
    | Eq (expr1, expr2) -> smtExpr.Apply (IntOps.eqOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Gt (expr1, expr2) -> smtExpr.Apply (IntOps.grOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Lt (expr1, expr2) -> smtExpr.Apply (IntOps.lsOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Le (expr1, expr2) -> smtExpr.Apply (IntOps.leqOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Ge (expr1, expr2) -> smtExpr.Apply (IntOps.geqOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Add (expr1, expr2) -> smtExpr.Apply (IntOps.addOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Subtract (expr1, expr2) -> smtExpr.Apply (IntOps.minusOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Neg expr -> smtExpr.Apply (IntOps.negOp, [ expr2adtSmtExpr adtConstrs expr ])
    | Mod (expr1, expr2) -> smtExpr.Apply (IntOps.modOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Mul (expr1, expr2) -> smtExpr.Apply (IntOps.mulOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | And exprs -> Array.map (expr2adtSmtExpr adtConstrs) exprs |> Array.toList |> smtExpr.And
    | Or exprs -> Array.map (expr2adtSmtExpr adtConstrs) exprs |> Array.toList |> smtExpr.Or
    | Not expr -> expr2adtSmtExpr adtConstrs expr |> smtExpr.Not
    | Implies (expr1, expr2) -> Hence (expr2adtSmtExpr adtConstrs expr1, expr2adtSmtExpr adtConstrs expr2)
    | Var n -> Ident (n, IntSort)
    | App (n, exprs) ->
      smtExpr.Apply (UserDefinedOperation (n, [], IntSort), List.map (expr2adtSmtExpr adtConstrs) exprs)
    | Apply (n, exprs) when adtConstrs |> Map.containsKey n ->
      let _, op = adtConstrs |> Map.find n
      smtExpr.Apply (op, List.map (expr2adtSmtExpr adtConstrs) exprs)
    | Apply (n, exprs) -> smtExpr.Apply (UserDefinedOperation (n, [], IntSort), List.map (expr2adtSmtExpr adtConstrs) exprs)
    | ForAll (names, e) ->
      QuantifierApplication (
        [ names |> Array.map (fun n -> (n, IntSort)) |> Array.toList |> ForallQuantifier ],
        expr2adtSmtExpr adtConstrs e
      )
    | Ite (expr1, expr2, expr3) -> smtExpr.Ite (expr2adtSmtExpr adtConstrs expr1, expr2adtSmtExpr adtConstrs expr2, expr2adtSmtExpr adtConstrs expr3)

// let chc () =
//   // [z nil; ]
//   TypeClarification.clarify
//     (Map [("nil", ("list", [] )); ("cons", ("list", [Integer; ADT "list"] ))])
//     (
//       And [| Eq (Var "z", Apply ("nil", [])); Eq (Var "x", Var "y"); Eq (Var "y", Var "z")
//              Or ([|Eq (Var "j", Var "xx"); Eq (Apply ("cons", [Var "v"; Apply ("cons", [Var "xx"; Var ("nil")]) ] ), Var "o")|]) |])
//     []
//   |> fun xs -> for x in snd xs do printfn $"{x}"
  
let unsatQuery funDefs adtDecs adtConstrs resolvent typedVars =
  let clause = Assert (ForAllTyped (typedVars, resolvent))
  funDefs @ adtDecs |> List.addLast clause  

let feasible adtDecs adtConstrs funDefs resolvent =
  let qNames = vars resolvent |> List.choose (function Var n -> Some n | _ -> None)
  let env = emptyEnv [||]
  let solver = env.ctxSlvr.MkSolver "HORN"
  let x, vars = TypeClarification.clarify adtConstrs resolvent qNames
  let env, solver, cmds = SoftSolver.setCommands env solver (unsatQuery funDefs (adtDecs) adtConstrs x (Set.toList vars)) 
  z3solve
    { env = env
      solver = solver
      unsat = fun _ _ -> ()
      sat = fun _ _ -> ()
      cmds = cmds
    }
  

let hyperProof2clauseNew defConsts decFuns hyperProof asserts =
  let resolvent' =
    proofTree hyperProof
    |> assertsTreeNew asserts defConsts decFuns
    |> fun x -> printfn $"{x}"; x
    |> treeOfExprs
    |> uniqVarNames
    |> resolvent
    |> List.toArray
  
  let resolvent =   
    resolvent'
    |> And
    |> Simplifier.normalize
  
  resolvent

let terms =
  let rec helper acc =
    function
    | Add (x, y) -> helper (x :: acc) y
    | v -> v :: acc

  helper [] >> List.rev

let notZeroFunConsts defs =
  let consts =
    function
    | Add _ as add ->
      terms add
      |> List.tail
      |> List.map (function
        | Mul (Apply (c, []), _) -> Some c
        | _ -> None)
      |> List.fold
        (fun acc ->
          function
          | Some x -> x :: acc
          | _ -> acc)
        []
      |> List.rev
    | _ -> []

  let notZeros =
    let rec helper acc =
      function
      | Ite (cond, ifExpr, elseExpr) -> helper acc cond |> flip helper elseExpr |> flip helper ifExpr
      | Eq (expr, _) -> helper acc expr
      | Add _ as add ->
        (consts add |> List.map (fun n -> Not (Eq (Var n, Int 0))) |> List.toArray |> Or)
        :: acc
      | _ -> acc

    helper []

  defs
  |> List.fold
    (fun acc def ->
      match def with
      | Def (_, args, _, expr) when args.Length > 0 -> acc @ notZeros expr
      | _ -> acc)
    []
  |> List.map Assert

let constNumber (str: String) = $"%s{str[2..]}" |> Int64.Parse

let maxConstIndex =
  List.map (function
    | Def (n, _, _, _) -> constNumber n
    | _ -> Int64.MinValue)
  >> List.fold max Int64.MinValue

let newConstNames from n =
  if from > n then
    []
  else
    List.unfold
      (fun state ->
        if state = n then
          None
        else
          Some ($"c_{state}", state + 1L))
      from

let constNames startIdx =
  function
  | Some expr ->
    expr
    |> terms
    |> List.length
    |> int64
    |> (fun d -> newConstNames startIdx (startIdx + d))
  | None -> []


let addition term =
  function
  | t :: ts -> List.fold (fun acc x -> Add (acc, x)) t ts |> fun add -> Add (term, add)
  | [] -> term

let addBranch consts def =
  let expr =
    match def with
    | Def (_, _, _, Ite (_, _, expr)) -> Some expr
    | Def (_, _, _, expr) -> Some expr
    | _ -> None

  let xExpr constNames (args: Name list) =
    constNames
    |> List.tail
    |> List.zip args
    |> List.map (fun (n, c) -> Mul (Apply (c, []), Var n))
    |> addition (List.head constNames |> fun x -> Apply (x, []))

  let condition constNames args = Eq (xExpr constNames args, Int 0)

  match def with
  | Def (x, args, _, body) ->
    let fstNewIdx = maxConstIndex consts + 1L
    let condConstNames = fstNewIdx |> flip constNames expr

    let elseConstNames =
      condConstNames |> List.length |> int64 |> (+) fstNewIdx |> flip constNames expr

    let ite = Ite (condition condConstNames args, body, xExpr elseConstNames args)

    let constDefs = List.map (fun n -> Def (n, [], Integer, Int 0))
    let newConsts = constDefs condConstNames @ constDefs elseConstNames

    (newConsts, consts @ newConsts, Def (x, args, Integer, ite))
  | _ -> ([], consts, def)

let branching constDefs funDefs =
  let isDefConstFn =
    function
    | Def (_, args, _, _) when args.Length = 0 -> true
    | _ -> false

  let funDefs' = funDefs |> List.filter isDefConstFn

  funDefs
  |> List.filter (not << isDefConstFn)
  |> List.fold
    (fun (newConsts, consts, funs) def ->
      addBranch consts def
      |> fun (newConsts', consts', def') -> (newConsts @ newConsts', consts', def' :: funs))
    ([], constDefs, funDefs')
  |> fun (newConsts, _, funDefs) -> (newConsts, funDefs)

let decConsts = List.map decConst

let writeDbg file (content: string) iteration =
  match dbgPath with
  | Some dbgPath ->
    let path = Path.Join [| dbgPath; toString iteration; file |]

    if not <| Directory.Exists (Path.GetDirectoryName path) then
      Directory.CreateDirectory (Path.GetDirectoryName path) |> ignore

    File.AppendAllText ($"{path}", $"{content}\n")
  | None -> ()

let banOldValues constDefs =
  Assert (Implies (And (List.choose (function Def (n, _, _, v) -> Some ((Eq (Var n, v))) | _ -> None) constDefs |> List.toArray),
           Bool false))

let rec learner adtDecs (adtConstrs: Map<ident,(symbol * Type list)>) funDefs (solver: Solver) env asserts constDefs constrDefs funDecls proof pushed iteration =
  match proof with
  | [ Command (Proof (hyperProof, _, _)) ] ->
    let resolvent =
      hyperProof2clauseNew constDefs funDecls hyperProof asserts
    
    
    match feasible adtDecs adtConstrs funDefs resolvent with
    | SAT _ -> Error "UNSAT"
    | UNSAT _ ->
        let clause = Implies (resolvent, Bool false) |> forAll
        printfn $"RESOLVENTTTTT : : : {expr2smtExpr clause}"

        
        writeDbg "redlog-input.smt2" $"{Redlog.redlogQuery (funDefs @ def2decVars constrDefs) clause}" iteration
    
        let redlogResult = redlog (funDefs @ def2decVars constrDefs) clause
    
        writeDbg "redlog-output.smt2" $"{program2originalCommand redlogResult}" iteration
        let env, solver, setCmds = SoftSolver.setCommands env solver [ redlogResult; banOldValues constDefs ]
    
        writeDbg
          "smt-input.smt2"
          (let c =
            List.map (program2originalCommand >> toString) (pushed @ setCmds) |> join "\n" in
    
           let actives = join " " (List.map toString env.actives) in
           $"(set-logic NIA)\n{c}\n(check-sat-assuming ({actives}))\n(get-model)")
          iteration
    
        let pushed' = pushed @ [ redlogResult ]
    
    
        match SoftSolver.solve env solver with
        | Ok (env', solver', defConsts') -> Ok (env', solver', defConsts', constrDefs, pushed')
        | Error e -> Error e
        
  | _ -> Error "PROOF_FORMAT"


let tst () =
  let envTeacher = emptyEnv [| ("proof", "true") |]
  let teacherSolver = envTeacher.ctxSlvr.MkSolver "HORN"
  teacherSolver.Set ("fp.spacer.global", true)
  teacherSolver.Set ("fp.xform.inline_eager", false)
  teacherSolver.Set ("fp.xform.inline_linear", false)
  
  let cmds =
    [ Def ("Z_2017", [], Integer, Int 0L)
      Def ("S_457", ["x"], Integer, Add (Var "x", Int 1L))
      Def ("Z_2013", [], Integer, Int 0L)
      Def ("S_456", ["x"], Integer, Add (Var "x", Int 1L))
      Def ("c_5", [], Integer, Int 1L)
      Def ("c_4", [], Integer, Int 0L)
      Def ("c_3", [], Integer, Int 0L)
      Def ("c_2", [], Integer, Int 0L)
      Def ("c_1", [], Integer, Int 0L)
      Def ("c_0", [], Integer, Int 1L)
      Def ("false_334", [], Integer, Apply ("c_0", []))
      Def ("true_334", [], Integer, Apply ("c_1", []))
      Def ("nil_268", [], Integer, Apply ("c_2", []))
      Def
        ("cons_238", ["head_476"; "tail_476"], Integer,
         Add
           (Add (Apply ("c_3", []), Mul (Apply ("c_4", []), Var "head_476")),
            Mul (Apply ("c_5", []), Var "tail_476")))
      Decl ("unS_669", 2)
      Decl ("isZ_424", 1)
      Decl ("isS_424", 1)
      Decl ("add_360", 3)
      Decl ("minus_355", 3)
      Decl ("le_334", 2)
      Decl ("ge_334", 2)
      Decl ("lt_354", 2)
      Decl ("gt_337", 2)
      Decl ("mult_334", 3)
      Decl ("div_334", 3)
      Decl ("mod_336", 3)
      Decl ("diseqBool_154", 2)
      Decl ("isfalse_154", 1)
      Decl ("istrue_154", 1)
      Decl ("and_334", 3)
      Decl ("or_341", 3)
      Decl ("hence_334", 3)
      Decl ("not_339", 2)
      Decl ("diseqlist_238", 2)
      Decl ("head_477", 2)
      Decl ("tail_477", 2)
      Decl ("isnil_268", 1)
      Decl ("iscons_238", 1)
      Decl ("projS_179", 2)
      Decl ("isZ_423", 1)
      Decl ("isS_423", 1)
      Decl ("length_47", 2)
      Decl ("even_3", 2)
      Decl ("x_54976", 3)
      Decl ("x_54978", 3)
      Assert
        (ForAll
           ([|"x_54980"; "x_54994"; "x_54995"; "x_54996"; "x_54997"; "x_54998";
              "x_54999"; "x_55000"; "y_2253"|],
            Implies
              (And
                 [|App ("diseqBool_154", [Var "x_54996"; Var "x_55000"]);
                   App ("x_54978", [Var "x_54994"; Var "x_54980"; Var "y_2253"]);
                   App ("length_47", [Var "x_54995"; Var "x_54994"]);
                   App ("even_3", [Var "x_54996"; Var "x_54995"]);
                   App ("length_47", [Var "x_54997"; Var "y_2253"]);
                   App ("length_47", [Var "x_54998"; Var "x_54980"]);
                   App ("x_54976", [Var "x_54999"; Var "x_54997"; Var "x_54998"]);
                   App ("even_3", [Var "x_55000"; Var "x_54999"])|], Bool false)))
      Assert
        (ForAll
           ([|"x_54990"|],
            App ("x_54976", [Var "x_54990"; Apply ("Z_2013", []); Var "x_54990"])))
      Assert
        (ForAll
           ([|"x_54993"|],
            App ("x_54978", [Var "x_54993"; Apply ("nil_268", []); Var "x_54993"])))
      Assert
        (ForAll
           ([|"x_54984"; "z_2014"|],
            Implies
              (App ("even_3", [Var "x_54984"; Var "z_2014"]),
               App
                 ("even_3",
                  [Var "x_54984"; Apply ("S_456", [Apply ("S_456", [Var "z_2014"])])]))))
      Assert
        (ForAll
           ([|"x_54982"; "xs_645"; "y_2249"|],
            Implies
              (App ("length_47", [Var "x_54982"; Var "xs_645"]),
               App
                 ("length_47",
                  [Apply ("S_456", [Var "x_54982"]);
                   Apply ("cons_238", [Var "y_2249"; Var "xs_645"])]))))
      Assert
        (ForAll
           ([|"x_54989"; "y_2251"; "z_2015"|],
            Implies
              (App ("x_54976", [Var "x_54989"; Var "z_2015"; Var "y_2251"]),
               App
                 ("x_54976",
                  [Apply ("S_456", [Var "x_54989"]); Apply ("S_456", [Var "z_2015"]);
                   Var "y_2251"]))))
      Assert
        (ForAll
           ([|"x_54992"; "xs_646"; "y_2252"; "z_2016"|],
            Implies
              (App ("x_54978", [Var "x_54992"; Var "xs_646"; Var "y_2252"]),
               App
                 ("x_54978",
                  [Apply ("cons_238", [Var "z_2016"; Var "x_54992"]);
                   Apply ("cons_238", [Var "z_2016"; Var "xs_646"]); Var "y_2252"]))))
      Assert
        (App ("diseqBool_154", [Apply ("false_334", []); Apply ("true_334", [])]))
      Assert
        (App ("diseqBool_154", [Apply ("true_334", []); Apply ("false_334", [])]))
      Assert
        (App
           ("even_3",
            [Apply ("false_334", []); Apply ("S_456", [Apply ("Z_2013", [])])]))
      Assert (App ("even_3", [Apply ("true_334", []); Apply ("Z_2013", [])]))
      Assert (App ("length_47", [Apply ("Z_2013", []); Apply ("nil_268", [])])) ]
  
  let unsat env (solver: Solver) =
    let p = Parser.Parser false
  
    for d in env.ctxDecfuns.Values do
      p.ParseLine <| d.ToString () |> ignore
  
    p.ParseLine (
      proof (fun _ -> ()) (solver.Proof.ToString()))
  
  z3solve
    { env = envTeacher
      solver = teacherSolver
      unsat = unsat
      // unsat = fun env solver -> ()
      cmds = cmds
      sat = fun _ _ -> () }
  |> function
    | SAT _ -> failwith "SAT?"
    | UNSAT proof -> printfn $"PROOF:\n{proof}"
  
  ()

let unsat env (solver: Solver) iteration =
  let p = Parser.Parser false

  for d in env.ctxDecfuns.Values do
    p.ParseLine <| d.ToString () |> ignore

  p.ParseLine (
    proof (fun _ -> ()) (solver.Proof.ToString())
    |> fun prettyProof ->
        writeDbg "proof-api.smt2" $"{solver.Proof}\nPRETTY:\n{prettyProof}" iteration
        $"{prettyProof}"
  )

let rec teacher
  adtDecs
  (adtConstrs: Map<ident, symbol * Type list>)
  funDefs
  (solverLearner: Solver)
  envLearner
  constDefs
  constrDefs
  funDecls
  (asserts: Program list)
  pushed
  iteration
  =
  let envTeacher = emptyEnv [| ("proof", "true") |]
  let teacherSolver = envTeacher.ctxSlvr.MkSolver "HORN"
  
  teacherSolver.Set ("fp.spacer.global", true)
  teacherSolver.Set ("fp.xform.inline_eager", false)
  teacherSolver.Set ("fp.xform.inline_linear", false)

  let cmds = (funDefs @ constDefs @ constrDefs @ funDecls @ asserts)

  for cmd in cmds do printfn $"CMD::{cmd}"
  
  writeDbg
    "horn-input.smt2"
    (let c = List.map (program2originalCommand >> toString) cmds |> join "\n" in
     $"(set-logic HORN)\n(set-option :produce-proofs true)\n{c}\n(check-sat)\n(get-proof)")
    iteration

  let toOrigCmds = List.map program2originalCommand
  
  for x in constDefs do printfn $">>>>>>>>{x}"

  z3solve
    { env = envTeacher
      solver = teacherSolver
      unsat = fun env solver -> unsat env solver iteration; ()
      // unsat = fun env solver -> ()
      cmds = cmds
      sat = fun _ _ -> () }
  |> function
    | SAT _ -> 
      for x in constDefs do printfn $"{x}"
    
      "SAT"
    | UNSAT proof ->
      
      
      let proof, dbgProof = z3Process.z3proof (toOrigCmds funDefs) (toOrigCmds constDefs) (toOrigCmds constrDefs) (toOrigCmds funDecls) (toOrigCmds asserts)
      
      writeDbg
        "proof.smt2"
        dbgProof
        iteration
 

      
      match
        learner adtDecs adtConstrs funDefs solverLearner envLearner asserts constDefs constrDefs funDecls proof pushed (iteration + 1)
      with
      | Ok (envLearner', solverLearner', defConsts', defConstrs', pushed') ->
        teacher adtDecs adtConstrs funDefs solverLearner' envLearner' defConsts' defConstrs' funDecls asserts pushed' (iteration + 1)
      | Error e -> e


let newLearner () =
  let envLearner = emptyEnv [| ("model", "true") |]
  let solverLearner = envLearner.ctxSlvr.MkSolver "NIA"
  envLearner, solverLearner

module AssertsMinimization =
  let bodyAppNames =
    let rec helper acc =
      function
      | Implies (expr1, _) -> helper acc expr1
      | App (name, _) -> name :: acc
      | ForAll (_, expr)
      | Not expr -> helper acc expr
      | And args
      | Or args -> Array.fold helper acc args
      | _ -> acc

    helper []

  let rec assertsMinimize (asserts: Program list) query =
    let rec helper used queue (acc: _ Set) =
      List.fold
        (fun (acc: _ Set, used) n ->
          let facts = axiomAsserts id asserts n |> Set
          let implies = impliesAsserts id asserts n
          let used' = used |> Set.add n

          let q' =
            List.fold
              (fun acc impl ->
                match impl with
                | Assert x -> acc @ (List.filter (fun n -> Set.contains n used' |> not) (bodyAppNames x))
                | _ -> acc)
              []
              implies

          let acc', used'' = helper used' q' Set.empty
          (Set.unionMany [ acc; acc'; facts; Set implies ], used''))
        (acc, used)
        queue

    match query with
    | Assert x ->
      let q = bodyAppNames x
      helper Set.empty q Set.empty |> fst |> (fun xs -> query :: Set.toList xs)
    | _ -> []

module HenceNormalization =
  let decNames =
    List.fold
      (fun acc x ->
        match x with
        | Decl (n, _) -> n :: acc
        | _ -> acc)
      []

  let assertsOf name asserts =
    axiomAsserts id asserts name @ impliesAsserts id asserts name

  let bindArgs args args' expr =
    List.fold2 (fun acc x y -> substituteVar x y acc) expr args args'

  let normalize name arguments srcArguments =
    function
    | Assert (App (_, args)) ->
      bindArgs srcArguments args (App (name, arguments))
      |> Assert
    | Assert (ForAll (names, App (_, args))) ->
      ForAll (names, bindArgs srcArguments args (App (name, arguments)))
      |> Assert
    | Assert (Implies (body, (App (_, args) as head))) ->
      bindArgs srcArguments args (Implies (And [| body; head |], App (name, arguments)))
      |> Assert
    | Assert (ForAll (names, Implies (body, (App (_, args) as head)))) ->
      bindArgs
        srcArguments
        args
        (ForAll (names, Implies (And [| body; head |], App (name, arguments))))
      |> Assert
    | _ -> Assert (Bool true)

  let trivialImplies asserts name =
    let isTrivial name =
      function
      | Assert (Implies (App (n', _), App (n, _)))
      | Assert (ForAll (_, Implies (App (n', _), App (n, _)))) when n' <> name && n = name -> true
      | _ -> false

    impliesAsserts id asserts name |> List.filter (isTrivial name)

  let normalizeAsserts funDecs asserts =
    let withoutFacts = List.filter (fun n -> axiomAsserts id asserts n |> List.isEmpty)

    let withoutFacts = funDecs |> decNames |> withoutFacts

    let asserts' =
      withoutFacts
      |> List.fold (fun acc n -> List.filter ((trivialImplies asserts n |> flip List.contains) >> not) acc) asserts

    let normalized =
      withoutFacts
      |> List.fold
        (fun acc n ->
          trivialImplies asserts n
          |> List.fold
            (fun acc ->
              function
              | Assert (ForAll (_, Implies (App (name', args'), App (name, args)))) ->
                (assertsOf name' asserts' |> List.map (normalize name args args')) @ acc
              | _ -> acc)
            acc)
        []

    normalized @ asserts'


  let substTrivialImpls (funDecs: Program list) asserts =
    let trivialImpls =
      funDecs
      |> List.fold
        (fun acc ->
          function
          | Decl (name, _) -> acc @ trivialImplies asserts name
          | _ -> acc)
        []

    let asserts' =
      List.filter (fun x -> trivialImpls |> List.contains x |> not) asserts 

    let newAsserts =
      trivialImpls
      |> List.fold
        (fun acc ->
          function
          | Assert (Implies (App (lName, lArgs) as l, App (rName, rArgs)))
          | Assert (ForAll (_, Implies (App (lName, lArgs) as l, App (rName, rArgs)))) ->
            let lFacts =
              axiomAsserts id asserts' lName
              |> List.filter (function
                | Assert (ForAll (_, Implies (_, x)))
                | Assert (Implies (_, x))
                | Assert (ForAll (_, x))
                | Assert x -> x.EqualsAnon l
                | _ -> false)
              |> List.map (function
                | Assert (App (_, fArgs))
                | Assert (ForAll (_, App (_, fArgs))) ->
                  bindArgs ( lArgs) ( fArgs) (App (rName, rArgs))
                  |> Assert
                | Assert (Implies (body, App (_, fArgs)))
                | Assert (ForAll (_, Implies (body, App (_, fArgs)))) ->
                  bindArgs ( lArgs) ( fArgs) (Implies (body, App (rName, rArgs)))
                  |> Assert
                | _ -> failwith "__unimplemented__ ()")


            acc @ lFacts
          | _ -> acc)
        []

    newAsserts @ asserts'


  let uniqQuery funDecs asserts =
    match queryAssert id asserts with
    | [ _ ] -> funDecs, asserts
    | xs ->
      let asserts' = asserts |> List.filter (fun x -> xs |> List.contains x |> not)
      let qDec = Decl ("q", 1)
      let qApp = App ("q", [ Var "aaaa" ])

      let quryImpls =
        xs
        |> List.choose (function
          | Assert (ForAll (_, Implies (body, Bool false)))
          | Assert (Implies (body, Bool false)) -> Implies (body, qApp) |> Assert |> Some
          | _ -> None)

      qDec :: funDecs, Assert (Implies (qApp, Bool false)) :: asserts' @ quryImpls

  let restoreVarNames =
    let nameVars =
      List.choose (function
        | Var n -> Some n
        | _ -> None)
      >> List.toArray

    function
    | Assert (ForAll (names, expr)) ->
      let names' = vars expr |> nameVars |> Set |> Set.union (Set names)
      Assert (ForAll (Set.toArray names', expr))
    | Assert expr as assrt ->
      match vars expr with
      | [] -> assrt
      | vars -> Assert (ForAll (nameVars vars, expr))
    | otherwise -> otherwise






let solver adtDecs (adtConstrs: Map<ident,(symbol * Type list)>) funDefs constDefs constrDefs funDecls (asserts: Program list) =
  let funDecls, asserts =
    let funDecls', asserts' =
      HenceNormalization.uniqQuery funDecls asserts
      |> fun (decs, asserts) ->
        decs, List.map HenceNormalization.restoreVarNames asserts
        
    funDecls',
    AssertsMinimization.assertsMinimize asserts' (queryAssert List.head asserts')
    |> HenceNormalization.normalizeAsserts funDecls'
    |> HenceNormalization.substTrivialImpls funDecls'
    |> List.map HenceNormalization.restoreVarNames
  
  for x in asserts do printfn $"ASSERT: {program2originalCommand x}"
  
  let envLearner, solverLearner = newLearner ()
  let decConsts = decConsts constDefs
  
  let startCmds = funDefs @ decConsts @ (notZeroFunConsts constrDefs)
  
  solverLearner.Push ()
  
  let envLearner, solverLearner, setCmds =
    SoftSolver.setCommands envLearner solverLearner startCmds


  let envLearner, solverLearner, setSofts =
    SoftSolver.setSoftAsserts envLearner solverLearner constDefs


  writeDbg
    "smt-input.smt2"
    (let c =
      List.map (program2originalCommand >> toString) (setCmds @ setSofts) |> join "\n" in

     let actives = join " " (List.map toString envLearner.actives) in
     $"(set-logic NIA)\n{c}\n(check-sat-assuming ({actives}))\n(get-model)")
    0

  writeDbg "redlog-input.smt2" "" 0
  writeDbg "redlog-output.smt2" "" 0

  match SoftSolver.evalModel envLearner solverLearner constDefs with
  | SAT (env, solver, model) -> teacher adtDecs adtConstrs funDefs solver env model constrDefs funDecls asserts (setCmds @ setSofts) 0
  | _ -> "UNKNOWN"

let sort2type =
  function
    | BoolSort -> Boolean
    | ADTSort name -> ADT name
    | _ -> Integer

let approximation file =
  let _, _, _, dataTypes, _, _, _, _ = Linearization.linearization file
  let p = Parser.Parser false
  let cmds = p.ParseFile file

  let adtDecs =
    cmds
    |> List.mapi (fun i -> function
      | Command (DeclareDatatypes adts) ->
        adts
        |> List.map (fun (adtName, decl) ->
          decl
          |> List.choose (function
            | ElementaryOperation (constrName, sorts, _), _, _ -> Some (constrName, (adtName, i, List.map sort2type sorts))
            | _ -> None) )
        |> List.concat
        |> Some
      | Command (DeclareDatatype (adtName, decl)) ->
        decl
        |> List.choose (function
            | ElementaryOperation (constrName, sorts, _), _, _ -> Some (constrName, (adtName, i, List.map sort2type sorts))
            | _ -> None)
        |> Some
      | _ -> None)
    |> List.filter Option.isSome
    |> List.map Option.get
    |> List.concat
    |> Map




  let defConstants =
    let rec helper = function
      | smtExpr.Apply (ElementaryOperation (ident, _, _), _)
      | smtExpr.Apply (UserDefinedOperation (ident, _, _), _) when ident.Contains "c_" -> [Def (ident, [], Integer, Int 0)]
      | smtExpr.Apply (_, exprs) -> List.collect helper exprs
      | smtExpr.And exprs -> List.collect helper exprs
      | smtExpr.Or exprs -> List.collect helper exprs
      | smtExpr.Not expr -> helper expr
      | smtExpr.Hence (expr1, expr2) -> helper expr1 @ helper expr2
      | smtExpr.QuantifierApplication (_, expr) -> helper expr
      | _ -> []

    List.collect (function Definition (DefineFun (_, _, _, expr)) -> helper expr | _ -> [])

  let decFuns =
    List.choose (function Command (DeclareFun _) as x -> Some x | _ -> None)

  let rec asserts =
    List.choose (function originalCommand.Assert _ as x -> Some x | _ -> None)

  let rec defFuns =
    List.choose (function Definition _ as x -> Some x | _ -> None)

  (adtDecs, defFuns cmds, dataTypes, defConstants dataTypes, decFuns cmds, asserts cmds)

let apply2app appNames =
  let rec helper =
    function
    | App _
    | Int _
    | Bool _
    | Var _ as expr -> expr
    | Eq (expr1, expr2) -> Eq (helper expr1, helper expr2)
    | Lt (expr1, expr2) -> Lt (helper expr1, helper expr2)
    | Gt (expr1, expr2) -> Gt (helper expr1, helper expr2)
    | Le (expr1, expr2) -> Le (helper expr1, helper expr2)
    | Ge (expr1, expr2) -> Ge (helper expr1, helper expr2)
    | Mod (expr1, expr2) -> Mod (helper expr1, helper expr2)
    | Add (expr1, expr2) -> Add (helper expr1, helper expr2)
    | Subtract (expr1, expr2) -> Subtract (helper expr1, helper expr2)
    | Neg expr -> Neg (helper expr)
    | Mul (expr1, expr2) -> Mul (helper expr1, helper expr2)
    | And exprs -> And (Array.map helper exprs)
    | Or exprs -> Or (Array.map helper exprs)
    | Not expr -> Not (helper expr)
    | Implies (expr1, expr2) -> Implies (helper expr1, helper expr2)
    | Apply (name, exprs) when appNames |> List.contains name -> App (name, List.map helper exprs)
    | Apply (name, exprs) -> Apply (name, List.map helper exprs)
    | ForAll (names, expr) -> ForAll (names, helper expr)
    | Ite (expr1, expr2, expr3) -> Ite (helper expr1, helper expr2, helper expr3)

  helper


let run file dbg =
  dbgPath <- dbg

  let adtConstrs, defFuns, liaTypes, defConstants, declFuns, asserts = approximation file
  let funDecls = List.map origCommand2program declFuns
  
  let adtDecs =
    adtConstrs
    |> Map.fold
         (fun (acc: Map<string, (int * Constructor list)>) constrName (adtName, i, argTypes) ->
            acc
            |> Map.change adtName (function Some constrs -> Some <| (i, (constrName, argTypes) :: snd constrs) | None -> Some (i, [(constrName, argTypes)])))
         Map.empty
    |> Map.toList
    |> List.sortBy (fun (_, (i, _)) -> i)
    |> List.map (fun (x, (_, y)) -> (x, y))
    // |> List.rev
    |> List.map DeclDataType
    
  
  let adtConstrs = adtConstrs |> Map.map (fun k (n, _, ts) -> (n, ts))
  
  let asserts' = List.map origCommand2program asserts

  let appNames =
    funDecls
    |> List.choose (function Decl (n, _) -> Some n | _ -> None)

  let asserts'' =
    asserts' |> List.choose (function Assert x -> Some (Assert (apply2app appNames x)) | _ -> None)
  let toPrograms = List.map origCommand2program




  solver adtDecs adtConstrs (toPrograms defFuns) defConstants (toPrograms liaTypes) funDecls asserts''
