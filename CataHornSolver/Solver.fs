module ProofBased.Solver
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

let assert1 =
  [ Assert (ForAll ([| "x1" |], App ("diseqInt", [| Apply ("Z", []); Apply ("S", [ Var "x1" ]) |]))) ]

let assert2 =
  [ Assert (ForAll ([| "x2" |], App ("diseqInt", [| Apply ("S", [ Var "x2" ]); Apply ("Z", []) |]))) ]

let assert3 =
  [ Assert (
      ForAll (
        [| "x3"; "y3" |],
        Implies (
          App ("diseqInt", [| Var "x3"; Var "y3" |]),
          App ("diseqInt", [| Apply ("S", [ Var "x3" ]); Apply ("S", [ Var "y3" ]) |])
        )
      )
    ) ]

let assert4 =
  [
    Assert (ForAll ([| "x4" |], Implies (App ("diseqInt", [| Var "x4"; Var "x4" |]), Bool false))) ]

let assert5 = [ Assert (Eq (Int 1, Int 2)) ]

let listConst =
  [ Def ("c_0", [], Int 0)
    Def ("c_1", [], Int 1)
    Def ("c_2", [], Int 1)
    Def ("c_3", [], Int 1) ]


let shiza =
  [ Def ("c_0", [], Int 1)
    Def ("c_1", [], Int 1)
    Def ("c_2", [], Int 1)
    Def ("c_3", [], Int 1)
    Def ("c_4", [], Int 1)
    Def ("c_5", [], Int 1)
    Def ("c_6", [], Int 1)
    Def ("c_7", [], Int 1)
    Def ("c_8", [], Int 1)
    Def ("c_9", [], Int 1) ]


let listDefFunsShiza =
  [ Def ("nil", [], Apply ("c_0", []))
    Def (
      "cons",
      [ "x"; "y" ],
      Ite (
        Eq (Add (Apply ("c_4", []), Add (Mul (Apply ("c_5", []), Var "x"), Mul (Apply ("c_6", []), Var "y"))), Int 0),
        Add (Apply ("c_1", []), Add (Mul (Apply ("c_2", []), Var "x"), Mul (Apply ("c_3", []), Var "y"))),
        Add (Apply ("c_7", []), Add (Mul (Apply ("c_8", []), Var "x"), Mul (Apply ("c_9", []), Var "y")))
      )
    ) ]


let listDefFuns =
  [ Def ("nil", [], Apply ("c_0", []))
    Def (
      "cons",
      [ "x"; "y" ],
      Add (Apply ("c_1", []), Add (Mul (Apply ("c_2", []), Var "x"), Mul (Apply ("c_3", []), Var "y")))
    ) ]

let listDeclFuns = [ Decl ("app", 3); Decl ("last", 2) ]

let listAssert1 =
  Assert (ForAll ([| "ys1" |], App ("app", [| Apply ("nil", []); Var "ys1"; Var "ys1" |])))

let listAssert2 =
  Assert (
    ForAll (
      [| "x2"; "xs2"; "ys2"; "zs2" |],
      Implies (
        App ("app", [| Var "xs2"; Var "ys2"; Var "zs2" |]),
        App (
          "app",
          [| Apply ("cons", [ Var "x2"; Var "xs2" ])
             Var "ys2"
             Apply ("cons", [ Var "x2"; Var "zs2" ]) |]
        )
      )
    )
  )
let listAssert3 =
  Assert (ForAll ([| "x3" |], App ("last", [| Apply ("cons", [ Var "x3"; Apply ("nil", []) ]); Var "x3" |])))
let listAssert4 =
  Assert (
    ForAll (
      [| "xs4"; "n4"; "x4" |],
      Implies (
        And
          [| Not (Eq (Var "xs4", Apply ("nil", [])))
             App ("last", [| Var "xs4"; Var "n4" |]) |],
        App ("last", [| Apply ("cons", [ Var "x4"; Var "xs4" ]); Var "n4" |])
      )
    )
  )

let listAssert5 =
  Assert (
    ForAll (
      [| "ys5"; "zs5"; "m5"; "xs5"; "n5" |],
      Implies (
        And
          [| App ("app", [| Var "xs5"; Var "ys5"; Var "zs5" |])
             App ("last", [| Var "ys5"; Var "n5" |])
             App ("last", [| Var "zs5"; Var "m5" |])
             Not (Eq (Var "ys5", Apply ("nil", [])))
             Not (Eq (Var "n5", Var "m5")) |],
        Bool false
      )
    )
  )


let emptyEnv argss =
  { ctxSlvr = new Context (argss |> dict |> Dictionary)
    ctxVars = Map.empty
    ctxFuns = Map.empty
    ctxDecfuns = Map.empty
    actives = [] }

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
    | Assert (ForAll (_, Implies (_, Bool false))) -> true
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
    | App (name, exprs) -> App ((if name = oldName then newName else name), exprs |> Array.map this)
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
    | App (_, exprs)
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
      | _ -> ([||], apps)

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
    | App (_, exprs)
    | And exprs
    | Or exprs -> Array.fold helper acc exprs
    | ForAll (_, expr)
    | Not expr
    | Neg expr -> helper acc expr
    | Var n -> acc |> Set.add n
    | Apply (_, exprs) -> List.fold helper acc exprs
    | Ite (expr1, expr2, expr3) -> List.fold helper acc [ expr1; expr2; expr3 ]

  helper Set.empty expr |> Set.toArray |> (fun ns -> ForAll (ns, expr))

let defFunBody args i =
  List.zip args [ i + 1 .. i + 1 + args.Length - 1 ]
  |> List.map (fun (n, i) -> Mul (Apply ($"c_{i}", []), Var n))
  |> List.fold (fun (acc, i) arg -> (Add (acc, arg), i + 1)) ((Apply ($"c_{i}", [])), i)

let branch i =
  function
  | Def (n, args, body) when args.Length > 0 ->
    let cond, i' = defFunBody args i |> fun (e, i) -> (Eq (e, Int 0), i)

    let elseBody, _ = defFunBody args (i' + 1)

    Def (n, args, Ite (cond, body, elseBody))
  | otherwise -> otherwise

let redlog definitions formula =
  Redlog.runRedlog definitions formula
  |> function
    | Ok v ->
      Assert <| (smtExpr2expr' v)
    | Error e ->
      failwith $"redlog-output: {e}"

let decConst =
  function
  | Def (n, _, _) -> DeclIntConst n
  | otherwise -> otherwise

let mapTreeOfLists f = Tree.fmap (List.map f)

let rec assertsTreeNew asserts consts decs =
  function
  | Node (Apply (name, _), []) ->
    name |> axiomAsserts id asserts |> (fun x -> Node (x, []))
  | Node (Apply (name, _), ts) ->
    name
    |> impliesAsserts id asserts
    |> fun x -> Node (x, ts |> List.map (assertsTreeNew asserts consts decs))
  | Node (Bool false, ts) ->
    Node (queryAssert (List.head >> fun x -> [ x ]) asserts, ts |> List.map (assertsTreeNew asserts consts decs))
  | _ -> __unreachable__ ()
  
let treeOfExprs =
  mapTreeOfLists (function
    | Assert (ForAll (_, x)) -> x
    | Assert x -> x
    | _ -> __unreachable__ ())

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
    | App (_, exprs)
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
  | App (name, args) when args |> Array.length > 0 ->
    ys
    |> List.fold
      (fun acc y ->
        match y with
        | App (n, args') when n = name -> (bind (Array.toList args) (Array.toList args')) :: acc
        | _ -> acc)
      []
    |> function
      | [ x ] -> x
      | xs ->
        xs
        |> List.rev
        |> List.map (function
          | [ x ] -> x
          | xs -> And (xs |> List.toArray))
        |> function
          | xs when xs |> List.length > 1 -> [ Or (xs |> List.toArray) ]
          | otherwise -> otherwise
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
    (fun acc heads ->
      match heads with
      | App (name, _) :: _ as apps -> acc |> add name apps
      | _ -> acc)
    Map.empty
  |> Map.map (fun _ v -> List.rev v)

let singleArgsBinds appsOfSingleParent (kids: Expr list list) =
  let get k map =
    (map |> Map.find k |> List.head,
     map
     |> Map.change k (function
       | Some [ _ ]
       | Some []
       | None -> None
       | Some (_ :: vs) -> Some vs))

  appsOfSingleParent
  |> List.fold
    (fun (acc, apps as otherwise) x ->
      match x with
      | App (name, _) ->
        let ys, apps' = apps |> get name
        (acc @ (argsBind x ys), apps')
      | _ -> otherwise)
    ([], collectApps kids)
  |> fst
  |> function
    | [ x ] -> x
    | xs -> xs |> List.toArray |> And

let argsBinds appsOfParents kids =
  appsOfParents
  |> List.fold (fun acc parent -> (singleArgsBinds parent kids) :: acc) []
  |> List.rev
  |> function
    | [ x ] -> x
    | xs -> xs |> List.toArray |> Or

let resolvent =
  let rec helper acc =
    function
    | Node (_, []) -> acc
    | Node (xs: Expr list, ts) ->
      let kids = List.map Tree.value ts

      let notAppRestrictions =
        List.map notAppRestrictions xs
        |> List.fold (@) []
        |> function
          | [] -> []
          | [ x ] -> [ x ]
          | xs -> [ xs |> List.toArray |> And ]

      let appRestrictions = List.map appRestrictions xs

      ts
      |> List.fold
        (fun (acc: Expr list) (t: Expr list tree) -> helper acc t)
        ((argsBinds appRestrictions kids :: notAppRestrictions) @ acc)

  helper [] >> List.rev

module Storage =
  let addPush k v map =
    map
    |> Map.change k (function
      | Some vs -> Some (v :: vs)
      | None -> Some [ v ])

  let getPop k map =
    let v =
      map
      |> Map.tryFind k
      |> function
        | Some xs -> xs |> List.head |> Some
        | None -> None

    (v,
     map
     |> Map.change
       k
       (match v with
        | None -> fun _ -> None
        | Some _ ->
          function
          | Some [ _ ]
          | Some []
          | None -> None
          | Some (_ :: vs) -> Some vs))



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

  let normalize =
    rmNestedAnds >> rmEmpty


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


let hyperProof2clauseNew defConsts constrDefs decFuns hyperProof asserts =
  let treeOfExprs =
    proofTree hyperProof
    |> assertsTreeNew asserts defConsts decFuns
    |> treeOfExprs

  let clause =
    treeOfExprs
    |> uniqVarNames
    |> resolvent
    |> List.toArray
    |> And
    |> Simplifier.normalize

  clause

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
      | Def (_, args, expr) when args.Length > 0 -> acc @ notZeros expr
      | _ -> acc)
    []
  |> List.map Assert

let constNumber (str: String) = $"%s{str[2..]}" |> Int64.Parse

let maxConstIndex =
  List.map (function
    | Def (n, _, _) -> constNumber n
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
    | Def (_, _, Ite (_, _, expr)) -> Some expr
    | Def (_, _, expr) -> Some expr
    | _ -> None

  let xExpr constNames (args: Name list) =
    constNames
    |> List.tail
    |> List.zip args
    |> List.map (fun (n, c) -> Mul (Apply (c, []), Var n))
    |> addition (List.head constNames |> fun x -> Apply (x, []))

  let condition constNames args = Eq (xExpr constNames args, Int 0)

  match def with
  | Def (x, args, body) ->
    let fstNewIdx = maxConstIndex consts + 1L
    let condConstNames = fstNewIdx |> flip constNames expr

    let elseConstNames =
      condConstNames |> List.length |> int64 |> (+) fstNewIdx |> flip constNames expr

    let ite = Ite (condition condConstNames args, body, xExpr elseConstNames args)

    let constDefs = List.map (fun n -> Def (n, [], Int 0))
    let newConsts = constDefs condConstNames @ constDefs elseConstNames

    (newConsts, consts @ newConsts, Def (x, args, ite))
  | _ -> ([], consts, def)

let branching constDefs funDefs =
  let isDefConstFn =
    function
    | Def (_, args, _) when args.Length = 0 -> true
    | _ -> false

  let funDefs' = funDefs |> List.filter isDefConstFn

  funDefs
  |> List.filter (not << isDefConstFn)
  |> List.fold
    (fun (newConsts, consts, funs) def ->
      addBranch consts def
      |> fun (newConsts', consts', def') -> (newConsts @ newConsts', consts', def' :: funs))
    ([], constDefs, funDefs')
  |> fun (newConsts, _, funDefs) ->
      (newConsts, funDefs)

let decConsts = List.map decConst

let writeDbg file (content: string) iteration =
  match dbgPath with
  | Some dbgPath ->
      let path = Path.Join [| dbgPath; toString iteration; file |]
      if not <| Directory.Exists (Path.GetDirectoryName path) then Directory.CreateDirectory (Path.GetDirectoryName path) |> ignore      
      File.AppendAllText ($"{path}", $"{content}\n")    
  | None -> ()

let rec learner
  funDefs
  (solver: Solver)
  env
  asserts
  constDefs
  constrDefs
  funDecls
  proof
  pushed
  iteration
  =
  match proof with
  | [ Command (Proof (hyperProof, _, _)) ] ->
    let clause =
      hyperProof2clauseNew constDefs constrDefs funDecls hyperProof asserts
      |> fun x ->
        Implies (x, Bool false)
        |> forAll
    
    writeDbg "redlog-input.smt2" $"{Redlog.redlogQuery (def2decVars constrDefs) clause}" iteration
    
    let redlogResult = redlog (funDefs @ def2decVars constrDefs) clause

    writeDbg "redlog-output.smt2" $"{program2originalCommand redlogResult}" iteration
    
    let env, solver, setCmds = SoftSolver.setCommands env solver [ redlogResult ]

    writeDbg "smt-input.smt2" (let c = List.map (program2originalCommand >> toString) (pushed @ setCmds) |> join "\n" in let actives = join " " (List.map toString env.actives) in $"(set-logic NIA)\n{c}\n(check-sat-assuming ({actives}))\n(get-model)") iteration
    
    let pushed' = pushed @ [ redlogResult ]


    match SoftSolver.solve env solver with
    | env', solver', defConsts' ->
      Ok (env', solver', defConsts', constrDefs, pushed')

  | _ -> Error "PROOF_FORMAT"

let unsat env (solver: Solver) iteration =
  let p = Parser.Parser false

  for d in env.ctxDecfuns.Values do
    p.ParseLine <| d.ToString () |> ignore

  p.ParseLine (
    solver.Proof.ToString ()
    |> proof
      (fun _ -> ())
    |> fun prettyProof ->
        writeDbg "proof.smt2" $"{solver.Proof}\nPRETTY:\n{prettyProof}" iteration
        prettyProof |> sprintf "%s"
  )

let rec teacher
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

  writeDbg "horn-input.smt2" (let c = List.map (program2originalCommand >> toString) cmds |> join "\n" in $"(set-logic HORN)\n(set-option :produce-proofs true)\n{c}\n(check-sat)\n(get-proof)") iteration

  z3solve
    { env = envTeacher
      solver = teacherSolver
      unsat = fun env solver -> unsat env solver iteration
      cmds = cmds
      sat = fun _ _ -> () }
  |> function
    | SAT _ ->
      // let model = List.map (program2originalCommand >> toString) constDefs |> join "\n"
      // printfn $"{model}"
      "SAT"
    | UNSAT proof ->
      match
        learner funDefs solverLearner envLearner asserts constDefs constrDefs funDecls proof pushed (iteration + 1)
      with
      | Ok (envLearner', solverLearner', defConsts', defConstrs', pushed') ->
        teacher funDefs solverLearner' envLearner' defConsts' defConstrs' funDecls asserts pushed' (iteration + 1)
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
    let rec helper used queue acc =
      List.fold
        (fun (acc, used) n ->
          let facts = axiomAsserts id asserts n
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

          let acc', used'' = helper used' q' []
          (acc @ acc' @ facts @ implies, used''))
        (acc, used)
        queue

    match query with
    | Assert x ->
      let q = bodyAppNames x
      helper Set.empty q [] |> fst |> (fun xs -> query :: xs)
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
      bindArgs (Array.toList srcArguments) (Array.toList args) (App (name, arguments))
      |> Assert
    | Assert (ForAll (names, App (_, args))) ->
      ForAll (names, bindArgs (Array.toList srcArguments) (Array.toList args) (App (name, arguments)))
      |> Assert
    | Assert (Implies (body, (App (_, args) as head))) ->
      bindArgs (Array.toList srcArguments) (Array.toList args) (Implies (And [| body; head |], App (name, arguments)))
      |> Assert
    | Assert (ForAll (names, Implies (body, (App (_, args) as head)))) ->
      bindArgs
        (Array.toList srcArguments)
        (Array.toList args)
        (ForAll (names, Implies (And [| body; head |], App (name, arguments))))
      |> Assert
    | _ -> Assert (Bool true)

  let normalizeAsserts funDecs asserts =
    let withoutFacts = List.filter (fun n -> axiomAsserts id asserts n |> List.isEmpty)

    let trivialImplies name =
      let isTrivial name =
        function
        | Assert (Implies (App (n', _), App (n, _)))
        | Assert (ForAll (_, Implies (App (n', _), App (n, _)))) when n' <> name && n = name -> true
        | _ -> false

      impliesAsserts id asserts name |> List.filter (isTrivial name)

    let withoutFacts = funDecs |> decNames |> withoutFacts

    let asserts' =
      withoutFacts
      |> List.fold (fun acc n -> List.filter ((trivialImplies n |> flip List.contains) >> not) acc) asserts

    let normalized =
      withoutFacts
      |> List.fold
        (fun acc n ->
          trivialImplies n
          |> List.fold
            (fun acc ->
              function
              | Assert (ForAll (_, Implies (App (name', args'), App (name, args)))) ->
                (assertsOf name' asserts' |> List.map (normalize name args args')) @ acc
              | _ -> acc)
            acc)
        []

    normalized @ asserts'

let solver funDefs constDefs constrDefs funDecls (asserts: Program list) =
  let asserts =
    AssertsMinimization.assertsMinimize asserts (queryAssert List.head asserts)
    |> HenceNormalization.normalizeAsserts funDecls

  let envLearner, solverLearner = newLearner ()
  let decConsts = decConsts constDefs

  let startCmds =
    funDefs
    @ decConsts
    @ (notZeroFunConsts constrDefs)

  solverLearner.Push ()

  let envLearner, solverLearner, setCmds =
    SoftSolver.setCommands envLearner solverLearner startCmds

  let envLearner, solverLearner, setSofts =
    SoftSolver.setSoftAsserts envLearner solverLearner constDefs

  writeDbg "smt-input.smt2" (let c = List.map (program2originalCommand >> toString) (setCmds @ setSofts) |> join "\n" in let actives = join " " (List.map toString envLearner.actives) in $"(set-logic NIA)\n{c}\n(check-sat-assuming ({actives}))\n(get-model)") 0
  writeDbg "redlog-input.smt2" "" 0
  writeDbg "redlog-output.smt2" "" 0

  match SoftSolver.evalModel envLearner solverLearner constDefs with
  | SAT (env, solver, model) -> teacher funDefs solver env model constrDefs funDecls asserts (setCmds @ setSofts) 0
  | _ -> "UNKNOWN"

let approximation file =
  let _, _, _, dataTypes, _, _, _, _ = Linearization.linearization file
  let p = Parser.Parser false
  let cmds = p.ParseFile file


  let defConstants =
    let rec helper acc =
      function
      | Number _
      | BoolConst _
      | Match _
      | smtExpr.Ite _
      | Ident _
      | Let _ -> acc
      | smtExpr.Apply (ElementaryOperation (ident, _, _), _)
      | smtExpr.Apply (UserDefinedOperation (ident, _, _), _) when ident.Contains "c_" -> ident :: acc
      | smtExpr.Apply (_, exprs) -> List.fold helper acc exprs
      | smtExpr.And exprs -> List.fold helper acc exprs
      | smtExpr.Or exprs -> List.fold helper acc exprs
      | smtExpr.Not expr -> helper acc expr
      | smtExpr.Hence (expr1, expr2) -> helper (helper acc expr2) expr1
      | smtExpr.QuantifierApplication (_, expr) -> helper acc expr

    List.fold
      (fun acc def ->
        match def with
        | Definition (DefineFun (_, _, _, expr)) -> helper acc expr
        | _ -> acc)
      []
    >> List.map (fun n -> Def (n, [], Int 0))
    >> List.rev

  let decFuns =
    let rec helper acc =
      function
      | Command (DeclareFun _) as x -> x :: acc
      | _ -> acc

    List.fold helper [] >> List.rev

  let rec asserts =
    let rec helper acc =
      function
      | originalCommand.Assert _ as x -> x :: acc
      | _ -> acc

    List.fold helper [] >> List.rev

  let rec defFuns =
    let rec helper acc =
      function
      | originalCommand.Definition _ as x -> x :: acc
      | _ -> acc

    List.fold helper [] >> List.rev

  (defFuns cmds, dataTypes, defConstants dataTypes, decFuns cmds, asserts cmds)

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
    | Apply (name, exprs) when appNames |> List.contains name -> App (name, List.map helper exprs |> List.toArray)
    | Apply (name, exprs) -> Apply (name, List.map helper exprs)
    | ForAll (names, expr) -> ForAll (names, helper expr)
    | Ite (expr1, expr2, expr3) -> Ite (helper expr1, helper expr2, helper expr3)

  helper


let run file dbg =
  dbgPath <- dbg

  let defFuns, liaTypes, defConstants, declFuns, asserts = approximation file
  let funDecls = List.map origCommand2program declFuns

  let asserts' = List.map origCommand2program asserts

  let appNames =
    funDecls
    |> List.fold
      (fun acc ->
        function
        | Decl (n, _) -> n :: acc
        | _ -> acc)
      []
    |> List.rev

  let asserts'' =
    (asserts'
     |> List.fold
       (fun acc ->
         function
         | Program.Assert x -> Assert (apply2app appNames x) :: acc
         | _ -> acc)
       [])
    |> List.rev
  let toPrograms = List.map origCommand2program

  solver (toPrograms defFuns) defConstants (toPrograms liaTypes) funDecls asserts''

let ads () =
  run "/home/andrew/adt-solver/many-branches-search/benchmarks-search/CAV2022Orig(13)/rewrite-diseq-asserts/rep/TIP-no-NAT-main(1)/TIP-no-NAT-main/chc/tip2015_bin_nat_plus_assoc.smt2" (None)
  |> printfn "%O"
// let chck () =
  // let run consts defFns decFns asserts =
  //   solver [] consts defFns decFns asserts

  // run listConst listDefFuns listDeclFuns [ listAssert1; listAssert2; listAssert3; listAssert4; listAssert5 ]
  // run shiza listDefFunsShiza listDeclFuns [ listAssert1; listAssert2; listAssert3; listAssert4; listAssert5 ]
  // run dConsts dDefFuns dDeclFuns [ dA2; dA1; dA3; dA4 ]
  // |> printfn "%O"

