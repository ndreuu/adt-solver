module ProofBased.Solver

open System
open System.Diagnostics
open System.Threading
open System.Threading.Tasks
open CataHornSolver
open CataHornSolver.z3Process
open CataHornSolver.z3Process.Instances
open CataHornSolver.z3Process.Interpreter
open Microsoft.FSharp.Core
open Microsoft.VisualStudio.TestPlatform.TestHost
open Microsoft.Z3
open NUnit.Framework
open Process
open Tree
open Z3Interpreter.AST

let mutable dbgPath = None

open System.Collections.Generic
open System.IO
open SMTLIB2

open Process
open Tree.Tree
open ProofBased.Utils
open Z3Interpreter.Interpreter
open Z3Interpreter.AST
open Approximation
open State

let mutable durations: (string * int64) list = []
let mutable curDuration = ""

let kek cmds =
  let content = List.map toString cmds |> join "\n"
  File.AppendAllText ($"/home/andrew/Downloads/jjj/shiza.smt2", $"\n\n{content}")

let state = StateBuilder ()

type statement =
  { iteration: int
    env: Env
    solver: Solver
    stopwatch: Stopwatch
    context: z3Process.context }

  static member Init env solver =
    { iteration = 0
      env = env
      solver = solver
      stopwatch = Stopwatch ()
      context = context.Init () }

let emptyEnv argss =
  { ctxSlvr = new Context (argss |> dict |> Dictionary)
    ctxVars = Map.empty
    ctxFuns = Map.empty
    ctxDecfuns = Map.empty
    actives = []
    ctxDataType = Map.empty }



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
    | App _ as app -> List.addLast app acc
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

  ForAll (helper Set.empty expr |> Set.toArray, expr)

let defFunBody args i =
  List.zip args [ i + 1 .. i + 1 + args.Length - 1 ]
  |> List.map (fun (n, i) -> Mul (Apply ($"c_{i}", []), Var n))
  |> List.fold (fun (acc, i) arg -> (Add (acc, arg), i + 1)) (Apply ($"c_{i}", []), i)

let branch i =
  function
  | Def (n, args, _, body) when args.Length > 0 ->
    let cond, i' = defFunBody args i |> fun (e, i) -> (Eq (e, Int 0), i)
    let elseBody, _ = defFunBody args (i' + 1)
    Def (n, args, Integer, Ite (cond, body, elseBody))
  | otherwise -> otherwise


type timeout<'a> =
  | Timeout
  | Ok of 'a
  
  
let redlog definitions formula =
  match Redlog.runRedlog definitions formula |> Some with
  | Some (Result.Ok v) -> timeout.Ok (Assert (smtExpr2expr' v))
  | None -> timeout.Timeout 
  | Some (Error e) -> failwith $"redlog-output: {e}"

let decConst =
  function
  | Def (n, _, _, _) -> DeclIntConst n
  | otherwise -> otherwise

let mapTreeOfLists f = fmap (List.map f)


let argsBind x ys =
  let bind = List.map2 (fun x y -> Eq (x, y))

  match x with
  | App (name, args) when not <| List.isEmpty args ->
    ys
    |> List.choose (function
      | App (n, args') when n = name -> Some (bind args args')
      | _ -> None)
    |> List.map Expr.And
    |> Expr.Or
    |> List.singleton
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
    (fun acc ->
      function
      | App (name, _) :: _ as apps -> add name apps acc
      | _ -> acc)
    Map.empty
  |> Map.map (fun _ -> List.rev)

let singleArgsBinds appsOfSingleParent (kids: Expr list list) =
  try
    let get k map =
      // printfn $"{k}"

      (map |> Map.find k |> List.head,
       map
       |> Map.change k (function
         | Some (_ :: vs) -> Some vs
         | _ -> None))

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
  with _ ->
    printfn "ERR NO_SIMPLEST"
    Environment.Exit 0

    Expr.Int 1

let argsBinds appsOfParents kids =
  appsOfParents |> List.map (fun parent -> singleArgsBinds parent kids) |> Expr.Or

module Implies =
  let bodyArgs' =
    function
    | And args -> List.ofArray args
    | otherwise -> [ otherwise ]

  let bodyArgs =
    function
    | Implies (b, _) -> Some (bodyArgs' b)
    | _ -> None

let rec foldTreeResolvent =
  function
  | Node (xs, []) -> List.map notAppRestrictions xs |> List.concat
  | Node (xs, ts) ->
    let kids = List.map Tree.value ts
    let notAppRestrictions = List.collect notAppRestrictions xs |> Expr.And
    let appRestrictions = List.map appRestrictions xs

    argsBinds appRestrictions kids
    :: notAppRestrictions
    :: List.collect foldTreeResolvent ts

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

  let rec constrFuns2apps (adts: Map<ident, (symbol * Type list)>) =
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

  let argTypes (adts: Map<ident, (symbol * Type list)>) =
    let rec helper acc =
      function
      | App (name, args) when adts |> Map.containsKey name ->
        let _, argTypes = adts |> Map.find name

        List.fold2
          (fun acc arg t ->
            match arg with
            | Var n -> acc |> Set.add (n, t)
            | _ -> helper acc arg)
          acc
          (args)
          argTypes
      | App (_, exprs) -> List.fold helper acc exprs
      | Apply (_, args) ->
        List.fold
          (fun acc arg ->
            match arg with
            | Var n -> acc |> Set.add (n, Integer)
            | _ -> helper acc arg)
          acc
          args
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

  let predicateArgTypes (adts: Map<ident, (symbol * Type list)>) typedVars =
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

    helper adts
    >> function
      | ADT tName -> Some (Type.ADT tName)
      | Int -> Some Integer
      | Bool -> Some Boolean
      | _ -> None

  let farmTypes (adts: Map<ident, (symbol * Type list)>) typedVars =
    let varNames =
      List.choose (function
        | Var n -> n |> Some
        | _ -> None)

    let rec helper (acc: _ Set) expr =
      match expr with
      | Eq (e1, e2)
      | Gt (e1, e2)
      | Lt (e1, e2)
      | Le (e1, e2)
      | Ge (e1, e2) ->
        let names = Set.union (Set (vars e1 |> varNames)) (Set (vars e2 |> varNames))

        let nameTypes =
          names
          |> Set.filter (fun n -> typedVars |> Map.containsKey n |> not)
          |> Set.map (fun n -> (n, predicateArgTypes adts typedVars expr))
          |> Set.toList
          |> List.choose (fun (x, y) ->
            match y with
            | Some y' -> Some (x, y')
            | None -> None)

        acc |> Set.union (Set nameTypes)
      | Not expr -> helper acc expr
      | And exprs
      | Or exprs -> Array.fold helper acc exprs
      | a ->
        printfn $"{a}"
        __unreachable__ ()

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
          (fun acc ->
            function
            | Eq (Var x, Var y)
            | Eq (Var y, Var x) when x = name && used |> Set.contains y |> not ->
              (helper y (y :: acc) (used |> Set.add y))
            | _ -> acc)
          acc

      helper name []

    let eqs = Set.toList eqs
    let typedVarNames, _ = Set.toList typedVars |> List.unzip

    eqs
    |> List.choose (function
      | Eq (Var x, Var y)
      | Eq (Var y, Var x) when typedVarNames |> List.contains x && typedVarNames |> List.contains y |> not ->
        Some (Map typedVars |> Map.find x, clause x eqs (Set [ x ]))
      | _ -> None)
    |> List.map (fun (t, ns) -> ns |> List.map (fun n -> (n, t)))
    |> List.concat
    |> Set
    |> Set.union typedVars

  let appendIntVars (names: Name list) vars =
    (Set names |> Set.difference <| (Set.map fst vars))
    |> Set.map (fun n -> (n, Integer))
    |> Set.union vars

  let clarify (adts: Map<ident, (symbol * Type list)>) expr varNames =
    let appConstrExpr = constrFuns2apps adts expr
    let typedVars = constrFuns2apps adts appConstrExpr |> argTypes adts
    // let ss = farmTypes adts typedVars appConstrExpr
    let vars =
      typedVars |> Map.toList |> Set |> Set.union
      <| farmTypes adts typedVars appConstrExpr

    (appConstrExpr, transitiveEqs (eqs appConstrExpr) vars |> appendIntVars varNames)


  let rec expr2adtSmtExpr adtConstrs =
    function
    | Expr.Int i -> Number i
    | Expr.Bool b -> BoolConst b
    | Eq (expr1, expr2) ->
      smtExpr.Apply (IntOps.eqOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Gt (expr1, expr2) ->
      smtExpr.Apply (IntOps.grOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Lt (expr1, expr2) ->
      smtExpr.Apply (IntOps.lsOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Le (expr1, expr2) ->
      smtExpr.Apply (IntOps.leqOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Ge (expr1, expr2) ->
      smtExpr.Apply (IntOps.geqOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Add (expr1, expr2) ->
      smtExpr.Apply (IntOps.addOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Subtract (expr1, expr2) ->
      smtExpr.Apply (IntOps.minusOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Neg expr -> smtExpr.Apply (IntOps.negOp, [ expr2adtSmtExpr adtConstrs expr ])
    | Mod (expr1, expr2) ->
      smtExpr.Apply (IntOps.modOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
    | Mul (expr1, expr2) ->
      smtExpr.Apply (IntOps.mulOp, [ expr2adtSmtExpr adtConstrs expr1; expr2adtSmtExpr adtConstrs expr2 ])
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
    | Apply (n, exprs) ->
      smtExpr.Apply (UserDefinedOperation (n, [], IntSort), List.map (expr2adtSmtExpr adtConstrs) exprs)
    | ForAll (names, e) ->
      QuantifierApplication (
        [ names |> Array.map (fun n -> (n, IntSort)) |> Array.toList |> ForallQuantifier ],
        expr2adtSmtExpr adtConstrs e
      )
    | Ite (expr1, expr2, expr3) ->
      smtExpr.Ite (expr2adtSmtExpr adtConstrs expr1, expr2adtSmtExpr adtConstrs expr2, expr2adtSmtExpr adtConstrs expr3)

// let chc () =
//   // [z nil; ]
//   TypeClarification.clarify
//     (Map [("nil", ("list", [] )); ("cons", ("list", [Integer; ADT "list"] ))])
//     (
//       And [| Eq (Var "z", Apply ("nil", [])); Eq (Var "x", Var "y"); Eq (Var "y", Var "z")
//              Or ([|Eq (Var "j", Var "xx"); Eq (Apply ("cons", [Var "v"; Apply ("cons", [Var "xx"; Var ("nil")]) ] ), Var "o")|]) |])
//     []
//   |> fun xs -> for x in snd xs do printfn $"{x}"



module Simplifier =
  let private emptyFilter =
    Array.filter (function
      | And [||]
      | Or [||] -> false
      | _ -> true)

  let rec private rmEmpty =
    function
    | And args -> args |> emptyFilter |> Array.map rmEmpty |> And
    | Or args -> args |> emptyFilter |> Array.map rmEmpty |> Or
    | otherwise -> otherwise

  let rec private rm = rmNestedAnds >> rmNestedOrs

  and private rmNestedOrs =
    function
    | Or [| x |] -> x
    | Or args ->
      args
      |> Array.toList
      |> List.choose (function
        | Or args' -> Array.toList args' |> List.map rm |> Some
        | otherwise -> Some [ rm otherwise ])
      |> List.concat
      |> List.toArray
      |> Or
    | And _ as andExpr -> rmNestedAnds andExpr
    | otherwise -> otherwise

  and private rmNestedAnds =
    function
    | And [| x |] -> x
    | And args ->
      let rm = rmNestedAnds >> rmNestedOrs

      args
      |> Array.toList
      |> List.choose (function
        | And args' ->
          Array.toList args'
          |> List.map (
            rm
            >> function
              | And e -> e
              | otherwise -> [| otherwise |]
          )
          |> Array.concat
          |> List.ofArray
          |> Some
        | otherwise ->
          (rm otherwise
           |> function
             | And e -> e
             | otherwise -> [| otherwise |])
          |> List.ofArray
          |> Some)
      |> List.concat
      |> List.toArray
      |> And
    | Or _ as orExpr -> rmNestedOrs orExpr
    | otherwise -> otherwise

  let normalize = rmNestedAnds >> rmEmpty

  let isOr =
    function
    | Or _ -> true
    | _ -> false

  let cutLayer =
    function
    | And exprs -> Array.filter (not << isOr) exprs, Array.filter isOr exprs
    | _ -> ([||], [||])

  let equals =
    Array.choose (function
      | Eq _ as e -> Some e
      | _ -> None)
    >> Set
    >> Set.toList

  let heads =
    List.choose (function
      | Eq (Apply _ as a, _)
      | Eq (_, (Apply _ as a)) -> Some a
      | _ -> None)


  let haveVar expr var =
    let rec helper acc =
      function
      | Var _ as x -> var = x
      | And exprs
      | Or exprs -> Array.fold (fun acc arg -> acc || helper acc arg) acc exprs
      | Apply (_, exprs)
      | App (_, exprs) -> List.fold (fun acc arg -> acc || helper acc arg) acc exprs
      | Eq (x, y)
      | Lt (x, y)
      | Gt (x, y)
      | Le (x, y)
      | Ge (x, y)
      | Mod (x, y)
      | Add (x, y)
      | Subtract (x, y)
      | Mul (x, y)
      | Implies (x, y) -> helper acc x || helper acc y
      | ForAllTyped (_, x)
      | ForAll (_, x)
      | Not x
      | Neg x -> helper acc x
      | Ite (x, y, z) -> helper acc x || helper acc y || helper acc z
      | _ -> acc

    helper false expr

  let isUsingByOrs cmds var =
    Array.choose
      (function
      | Or _ as x -> Some x
      | _ -> None)
      cmds
    |> Array.fold (fun acc expr -> acc || haveVar expr var) false

  let transitiveEqs eqs =
    let rec helper eqs from =
      match from with
      | Apply _ as a ->
        let xs =
          List.choose
            (function
            | Eq (app, x)
            | Eq (x, app) when app = a -> Some x
            | _ -> None)
            eqs

        let eqs' =
          List.filter
            (function
            | Eq (app, _)
            | Eq (_, app) -> app <> a
            | _ -> true)
            eqs

        let eqs'' =
          List.filter
            (function
            | Eq (Apply _, _)
            | Eq (_, Apply _) -> false
            | _ -> true)
            eqs'

        List.map (fun x -> [ x ] @ (helper eqs'' x |> fst)) xs |> List.concat, eqs'
      | var ->
        match
          List.tryFind
            (function
            | Eq (x, _)
            | Eq (_, x) when x = var -> true
            | _ -> false)
            eqs
        with
        | Some (Eq (var', value) as e)
        | Some (Eq (value, var') as e) when var' = var ->
          let xs =
            List.choose
              (function
              | Eq (v, x)
              | Eq (x, v) when v = value -> Some x
              | _ -> None)
              eqs

          let eqs' =
            List.filter
              (function
              | v -> e <> v)
              eqs

          List.map (fun x -> (helper eqs' x |> fst)) xs
          |> fun xs -> ([ var ] :: [ value ] :: xs) |> List.concat, []
        | _ -> [ from ], []

    let heads = heads eqs |> Set.ofList |> Set.toList

    List.zip
      heads
      (List.fold
        (fun (acc, eqs) x ->
          match eqs with
          | [] -> (acc, eqs)
          | _ -> let a, eqs' = helper eqs x in (List.addLast (Set.ofList a) acc, eqs'))
        ([], eqs)
        heads
       |> fst)
    |> List.map (fun (e, xs) -> Set.toList xs |> List.map (fun x -> (x, e)))
    |> List.concat

  let notEqs =
    Array.choose (function
      | Eq _ -> None
      | otherwise -> Some otherwise)

  let subst transitiveEqs exprs =
    List.fold (fun acc (var, x) -> substituteVar var x acc) (And exprs) transitiveEqs

  let substituteMany transitiveEqs expr =
    List.fold (fun expr (var, value) -> substituteVar var value expr) expr transitiveEqs


  let mkEq x y = Eq (x, y)

  let rmObviousEqs =
    Array.filter (function
      | Eq (x, y) -> x <> y
      | _ -> true)

  let simplify' exprs ors =
    let equals = equals exprs
    let transitiveEqs = transitiveEqs equals

    let unusedEquals =
      equals
      |> List.filter (function
        | Eq (x, _)
        | Eq (_, x) -> not <| isUsingByOrs ors x
        | _ -> false)
      |> List.toArray

    let notEq = notEqs exprs

    let usedVars =
      Array.fold
        (fun acc ->
          function
          | Eq (x, _)
          | Eq (_, x) when isUsingByOrs ors x -> Set.add x acc
          | _ -> acc)
        Set.empty
        (Array.ofList equals)
      |> Set.toList

    let varsInTransitiveEqs = List.unzip transitiveEqs |> fst

    let usedVarsInTransitiveEqs =
      List.filter (fun var -> List.contains var varsInTransitiveEqs) usedVars

    let usedVarsOutTransitiveEqs =
      List.filter (fun var -> not <| List.contains var varsInTransitiveEqs) usedVars

    let usedEqualssssssss =
      Array.filter
        (function
        | Eq (x, y) when
          List.contains x usedVarsOutTransitiveEqs
          && List.contains y usedVarsOutTransitiveEqs
          ->
          true
        | _ -> false)
        (Array.ofList equals)

    let usedEquals' =
      let map = Map transitiveEqs

      List.map (fun x -> Eq (x, substituteMany transitiveEqs (map |> Map.find x))) usedVarsInTransitiveEqs
      |> List.toArray

    [| subst transitiveEqs unusedEquals; subst transitiveEqs notEq |]
    |> Array.choose (function
      | And exprs -> Some exprs
      | _ -> None)
    |> Array.concat
    |> rmObviousEqs
    |> Array.append usedEquals'
    |> Array.append usedEqualssssssss

  let substituteFirstLayer layer ors =
    let simpleExprs = simplify' layer ors
    let eqs = equals simpleExprs

    List.fold
      (fun exprs ->
        function
        | Eq (Var _ as var, x) -> Array.map (substituteVar var x) exprs
        | _ -> exprs)
      (Array.append simpleExprs ors)
      eqs
    |> rmObviousEqs

  let simplify resolvent =
    let layer, ors = cutLayer resolvent
    And (Array.append (substituteFirstLayer layer ors) ors)

let unsatQuery funDefs adtDecs resolvent typedVars =
  let clause =
    seq {
      yield! List.map DeclConst typedVars
      yield! Assert resolvent |> List.singleton
    }
    |> Seq.toList

  adtDecs @ funDefs @ clause



module Solver =
  let setCommands cmds =
    State (fun st ->
      (), let env, solver, _ = SoftSolver.setCommands st.env st.solver cmds in { st with env = env; solver = solver })


  let setCommandsKEK (cmds: Program list) =
    State (fun st ->
      (),
      { st with
          context =
            { st.context with
                snapshot = st.context.cmds
                cmds = st.context.cmds @ cmds } })

  let unsetCommands =
    State (fun st ->
      (),
      { st with
          context =
            { st.context with
                cmds = st.context.snapshot } })

  let setSoftConsts cmds =
    State (fun st ->
      let env, solver, cmds' = SoftSolver.setSoftAsserts st.env st.solver cmds
      cmds', { st with env = env; solver = solver })

  let setSoftConstsKEK cmds =
    State (fun st ->
      let cmds' = SoftSolver.setSoftAssertsKEK cmds
      
      // printfn $"........................"
      // for x in cmds' do
        // printfn $"{x}"
      // for x in List.choose (function Def (n, [], _, _) -> Some $"soft_{n}" | _ -> None) cmds' do
      //   printfn $"{x}"
      // printfn $"........................"
      cmds',
      { st with
          context = { st.context with softConsts = cmds |> List.choose (function Def (n, _, _, _) -> Some $"{n}" | _ -> None) } })


  //deprecated should use setC...; solve;
  let evalModel cmds =
    State (fun st ->
      let m, env, solver =
        match SoftSolver.evalModel st.env st.solver cmds with
        | SAT (env, solver, model) -> Result.Ok model, env, solver
        | UNSAT _ -> Error (), st.env, st.solver in

      m,
      match m with
      | Result.Ok _ -> { st with env = env; solver = solver }
      | Error _ -> st)



  let solveFeasible =
    State (fun st ->
      match solve -1 instance.Checker st.context.cmds [] [] with
      | Some (Interpreter.SAT _, _) -> Result.Ok (), st
      | _ -> Error (), st)

  let solveLearner defConsts =
    State (fun st ->
        
      // (5000, (fun _ -> solve instance.Learner st.context.cmds defConsts))
      // ||> runWithTimeout
      // let action =  async { return (solve instance.Learner st.context.cmds defConsts) } 
      // let r = try Async.RunSynchronously ((withTimeout 30000 action), 30000) |> Some with _ -> None
              // |> function Interpreter.SAT x -> x
      // match r with
      // | Some (Interpreter.SAT (Some xs)) -> timeout.Ok (Result.Ok xs), st
      // | Some (Interpreter.UNSAT (Some _)) -> timeout.Ok (Result.Error "UNKNEONWOWN"), st 
      //
      // | None -> printfn "YYYYYYYYYYYYYYYY"; Timeout, st)
      //
      // let r =
      //   Async.AwaitTask((Task.Delay 500)
      //                         .ContinueWith(fun _ ->
      //                           let r = solve instance.Learner st.context.cmds defConsts st.context.softConsts
      //                          // execute "pkill" "z3" |> ignore
      //                           r), 20000) |> Async.RunSynchronously
      //
      // Async.AwaitTask
      //       ((Task.Delay 500)
      //          .ContinueWith (fun _ -> execute "pkill" "z3"), 2000)
      //     |> Async.RunSynchronously |> ignore
          
      
      match solve 20 instance.Learner st.context.cmds defConsts st.context.softConsts  with
      | Some (Interpreter.SAT (Some xs), softs) -> timeout.Ok (Result.Ok xs), { st with context = { st.context with softConsts = softs } }
      | Some (Interpreter.UNSAT (Some _), softs) -> timeout.Ok (Result.Error "UNKNEONWOWN"), { st with context = { st.context with softConsts = softs } }
      | None ->  Timeout, st)
      // match solve instance.Learner st.context.cmds defConsts with
      // | Interpreter.SAT (Some xs) -> timeout.Ok (Result.Ok xs), st
      // | Interpreter.UNSAT (Some _) -> timeout.Ok (Result.Error "UNKNEONWOWN"), st)

  let solve =
    State (fun st ->
      let m, env, solver =
        match SoftSolver.solve st.env st.solver with
        | Result.Ok (env, solver, model) -> Result.Ok model, env, solver
        | Error e -> Error e, st.env, st.solver in

      m,
      match m with
      | Result.Ok _ -> { st with env = env; solver = solver }
      | Error _ -> st)


module Debug =
  module Duration =
    let private runStopWatch durationName =
      State (fun st ->
        curDuration <- durationName
        printfn $"{curDuration}"
        st.stopwatch.Start ()
        ((), st))

    let private stopStopwatch =
      State (fun st ->
        st.stopwatch.Stop ()
        let duration = st.stopwatch.ElapsedMilliseconds
        printfn $"{duration}"
        st.stopwatch.Reset ()
        durations <- (curDuration, duration) :: durations
        ((), st))

    let go (f: State<_, _> Lazy) name =
      state {
        do! runStopWatch name
        let! r = f.Force ()
        do! stopStopwatch
        return r
      }

  module Print =
    let writeDbg file (content: string) iteration =
      match dbgPath with
      | Some dbgPath ->
        let path = Path.Join [| dbgPath; "lol"; toString iteration; file |]

        if not <| Directory.Exists (Path.GetDirectoryName path) then
          Directory.CreateDirectory (Path.GetDirectoryName path) |> ignore

        File.AppendAllText ($"{path}", $"{content}\n")
      | None -> ()

    let next = State (fun st -> (), { st with iteration = st.iteration + 1 })

    let private write file s =
      State (fun st -> (writeDbg file s st.iteration), st)

    let smtInput s =
      State (fun st ->
        let actives = join " " (List.map toString st.env.actives)
        (writeDbg "smt-input.smt2" $"{s}\n(check-sat-assuming ({actives}))\n(get-model)" st.iteration), st)

    let redlogInput = write "redlog-input.smt2"
    let redlogOutput = write "redlog-output.smt2"
    let hornInput = write "horn-input.smt2"
    let smtADTLIA = write "smt-ADT-LIA.smt2"
    let smtADTLIABBB = write "smt-ADT-LIABBBBBBBBBB.smt2"
    let proof = write "proof.smt2"


let feasible (adtDecs, (recs: symbol list list)) adtConstrs funDefs resolvent =
  let env = emptyEnv [||]
  let solver = env.ctxSlvr.MkSolver "ALL"
  solver.Push ()

  let nonRec =
    List.filter
      (function
      | DeclDataType [ n, _ ] when (not <| List.contains n (List.concat recs)) -> true
      | _ -> false)
      adtDecs

  let recs =
    List.map
      (List.map (fun n ->
        List.find
          (function
          | DeclDataType [ n', _ ] when n = n' -> true
          | _ -> false)
          adtDecs))
      recs
    |> List.map (fun ds ->
      DeclDataType (
        List.choose
          (function
          | DeclDataType [ n', b ] -> Some (n', b)
          | _ -> None)
          ds
      ))

  let adtDecs = recs @ nonRec
  // List.map (fun n -> ) recs
  // let adtDecs =

  state {
    let qNames =
      vars resolvent
      |> List.choose (function
        | Var n -> Some n
        | _ -> None)

    let expr, vars = TypeClarification.clarify adtConstrs resolvent qNames

    let q = unsatQuery funDefs adtDecs expr (Set.toList vars)
    // do! Solver.setCommands q
    do! Solver.setCommandsKEK q
    // let! r = Solver.solve
    let! r = Solver.solveFeasible
    return (r, q)
  }
  |> run (statement.Init env solver)

module App =
  let appNames =
    List.choose (function
      | App (n, _) -> Some n
      | _ -> None)

module Assert =
  let asserts =
    List.filter (function
      | Assert _ -> true
      | _ -> false)

  let bodies =
    List.choose (function
      | Assert x -> Some x
      | _ -> None)

module Resolvent =
  let proofTree proof =
    let rec helper (HyperProof (_, hyperProofs, head)) =
      match hyperProofs with
      | [] -> head |> smtExpr2expr |> (fun x -> Node (x, []))
      | _ -> Node (head |> smtExpr2expr, hyperProofs |> List.map helper)

    helper proof

  let implsWhichContains appNames cmds name =
    let impls =
      impliesAsserts id cmds name |> Assert.bodies |> List.choose Expr.forallBody

    let bodyAppNames = Implies.bodyArgs' >> App.appNames
    let isContainsApps = bodyAppNames >> List.sort >> (appNames |> List.sort |> (=))

    List.filter
      (function
      | Implies (b, _) -> isContainsApps b
      | _ -> false)
      impls

  let kidVals: Expr Tree.tree -> Expr list = Tree.kids >> List.map Tree.value

  let rec assertsTree asserts consts decs =
    function
    | Node (Bool false, ts) ->
      let query =
        queryAssert (Assert.bodies >> List.choose Expr.forallBody >> List.head >> List.singleton) asserts

      Node (query, List.map (assertsTree asserts consts decs) ts)
    | Node (Apply (name, _), []) ->
      let axioms =
        axiomAsserts (Assert.bodies >> List.choose Expr.forallBody) asserts name

      Node (axioms, [])
    | Node (Apply (name, _), ts) ->
      let from =
        List.map Tree.value ts
        |> List.choose (function
          | Apply (n, _) -> Some n
          | _ -> None)

      // printfn $"--------------------"
      // printfn $"{Node (Apply (name, []), ts)}"
      // for x in from do printfn $">> {x}"
      // printfn $"--------------------"

      Node (implsWhichContains from asserts name, List.map (assertsTree asserts consts decs) ts)
    | _ -> __unreachable__ ()

  let treeOfExprs =
    Tree.fmap (
      List.choose (function
        | Assert (ForAll (_, x)) -> Some x
        | Assert x -> Some x
        | _ -> None)
    )

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

  let rmQueryChain =
    function
    | Node (Bool false, [ Node (Apply ("query!0", []), tl) ]) -> Node (Bool false, tl)
    | otherwise -> otherwise

  let resolvent defConsts decFuns hyperProof asserts =
    proofTree hyperProof
    |> rmQueryChain
    |> assertsTree asserts defConsts decFuns
    |> uniqVarNames
    |> foldTreeResolvent
    |> Set




let resolvent defConsts decFuns hyperProof asserts =
  let resolvent' =
    Resolvent.proofTree hyperProof
    |> Resolvent.rmQueryChain
    |> fun x ->
        // printfn $"{x}"

        x
        |> Resolvent.assertsTree asserts defConsts decFuns
        |> fun x ->
            // printfn $"{x}"

            x
            // |> Resolvent.treeOfExprs
            // |> fun x ->
            // printfn $"{x}"

            // x
            |> Resolvent.uniqVarNames
            |> fun x ->
                // printfn $"{x}"

                x
                |> foldTreeResolvent
                |> fun xs ->
                    // for x in xs do printfn $"folded: {expr2smtExpr x}"
                    xs |> List.toArray

  let resolvent = resolvent' |> And |> Simplifier.normalize

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


let banOldValues constDefs =
  Assert (
    Implies (
      And (
        List.choose
          (function
          | Def (n, _, _, v) -> Some (Eq (Var n, v))
          | _ -> None)
          constDefs
        |> List.toArray
      ),
      Bool false
    )
  )



let rec learner
  (adtDecs, recs)
  (adtConstrs: Map<ident, symbol * Type list>)
  funDefs
  asserts
  constDefs
  constrDefs
  funDecls
  proof
  pushed
  =
  state {
    match proof with
    | [ Command (Proof (hyperProof, _, _)) ] ->
      let resolvent =
        resolvent constDefs funDecls hyperProof asserts |> Simplifier.simplify

      let! (feasible, smtADTLIAcContent), _ =
        Debug.Duration.go (lazy state.Return (feasible (adtDecs, recs) adtConstrs funDefs resolvent)) "Z3.ADT(LIA)"

      do!
        Debug.Print.smtADTLIA (
          let content =
            List.map (program2originalCommand >> toString) smtADTLIAcContent |> join "\n" in

          $"(set-option :produce-proofs true)\n{content}\n(check-sat)"
        )

      match feasible with
      | Result.Ok _ -> return Error "UNSAT"
      | Error _ ->
        let clause = Implies (resolvent, Bool false) |> forAll

        do! Debug.Print.redlogInput $"{Redlog.redlogQuery (funDefs @ def2decVars constrDefs) clause}"

        let! redlogResult =
          Debug.Duration.go (lazy state.Return (redlog (funDefs @ def2decVars constrDefs) clause)) "REDLOG"

        match redlogResult with
        | Timeout ->
          return
            Result.Ok (randomValues (List.choose (function
              | Def (n, _, _, _) -> Some n
              | _ -> None) constDefs)
                       |> List.map (fun (n, v) -> Def (n, [], Integer, Int v)), constrDefs, pushed)
        | timeout.Ok redlogResult -> 
          do! Debug.Print.redlogOutput $"{program2originalCommand redlogResult}"
  
          let setCmds = [ redlogResult; banOldValues constDefs ]
          // let setCmds = [ redlogResult ]
  
          do kek <| setCmds
          do! Solver.setCommandsKEK setCmds
  
          do!
            Debug.Print.smtInput (
              let content =
                List.map (program2originalCommand >> toString) (pushed @ setCmds) |> join "\n" in
  
              $"(set-logic NIA)\n{content}"
            )
  
          let pushed' = pushed @ setCmds
  
          match! Debug.Duration.go (lazy Solver.solveLearner constDefs) "Z3.NIA" with
          | timeout.Timeout ->
            do! Solver.unsetCommands
            return
              Result.Ok (randomValues (List.choose (function
                | Def (n, _, _, _) -> Some n
                | _ -> None) constDefs)
                         |> List.map (fun (n, v) -> Def (n, [], Integer, Int v)), constrDefs, pushed)
          | timeout.Ok (Result.Ok defConsts') -> return Result.Ok (defConsts', constrDefs, pushed')
          | timeout.Ok (Error e) -> return Error e

    | _ ->
      printfn $"ERR-PROOF_FORMAT"
      Environment.Exit 0
      return Error $"PROOF_FORMAT"
  }



// let tst () =
//   let p = Parser.Parser (false)
//   // let cmds =
//   //   p.ParseFile "/home/andrew/Downloads/jjj/smt-input.smt2"
//   //   |> List.filter (function originalCommand.Assert _ -> true | _ -> false)
//   //   |> List.map aboba
//   //   |> function [x1; x2; x3; x4 ;x5 ;x6] as l ->
//   //     printfn $"{x1}"
//   //     printfn $"{x2}"
//   //     printfn $"{x3}"
//   //     printfn $"{x4}"
//   //     printfn $"{x5}"
//   //     l
//   // let env = emptyEnv [| ("model", "true") |]
//   // let solver = env.ctxSlvr.MkSolver "NIA"
//   // state {
//   //   do! Solver.setCommands
//   //         ([ DeclIntConst "c_3"; DeclIntConst "c_0"
//   //            DeclIntConst "c_1"; DeclIntConst "c_2"
//   //            DeclConst ("soft_c_0", Boolean); DeclConst ("soft_c_1", Boolean)
//   //            DeclConst ("soft_c_2", Boolean); DeclConst ("soft_c_3", Boolean)  ] @ cmds)
//   //   let! _ =
//   //     Solver.setSoftConsts
//   //       [ Def ("c_2", [], Integer, Int 0); Def ("c_3", [], Integer, Int 0)
//   //         Def ("c_0", [], Integer, Int 0); Def ("c_1", [], Integer, Int 0) ]
//   //   return! Solver.evalModel []
//   // } |> run (statement.Init env solver)
//   // |> fst
//   // |> printfn "%O"
//
//   let env = emptyEnv [| ("model", "true") |]
//   let solver = env.ctxSlvr.MkSolver "ALL"
//
//   state {
//     let cmds =
//       ([ DeclConst ("c0", Integer)
//          DeclConst ("c1", Integer)
//          DeclConst ("c2", Integer)
//          DeclConst ("c3", Integer)
//          // Assert (Not (Implies (And ([|Eq (Int 1, Var "soft_c_3") ; Var "soft_c_0"|]), Var "soft_c_1")))
//          Assert (
//            ForAll (
//              [| "x"; "y" |],
//              Implies (
//                Implies (And [| Gt (Var "x", Int 0); Lt (Var "y", Int 0) |], Bool true),
//                ForAll ([||], Apply ("distinct", [ Var "x"; Var "y" ]))
//              )
//            )
//          )
//          // (Implies (Eq (Int 0, Var "c0"), (Implies (Eq (Int 2, Var "c2"), Eq (Int 2, Var "c1")) )  ))
//          ])
//
//     return! Solver.evalModel cmds
//   }
//   |> run (statement.Init env solver)
//   |> fst
//   |> function
//     | Ok ok ->
//       for x in ok do
//         printfn "A %O" x
//     | Error e -> printfn "%O" e

let rec teacher
  (adtDecs, recs)
  (adtConstrs: Map<ident, symbol * Type list>)
  funDefs
  constDefs
  constrDefs
  funDecls
  (asserts: Program list)
  pushed
  =
  // let envTeacher = emptyEnv [| ("proof", "true") |]
  // let teacherSolver = envTeacher.ctxSlvr.MkSolver "HORN"
  let cmds = (funDefs @ constDefs @ constrDefs @ funDecls @ asserts)

  // teacherSolver.Set ("fp.spacer.global", true)
  // teacherSolver.Set ("fp.xform.inline_eager", false)
  // teacherSolver.Set ("fp.xform.inline_linear", false)

  // let teacherRes =
  //   state {
  //     return
  //       z3solve
  //         { env = envTeacher
  //           solver = teacherSolver
  //           unsat = fun _ _ -> ()
  //           cmds = cmds
  //           sat = fun _ _ -> () }
  //   }
  let teacherRes =
    state {
      return
        solve -1 instance.Teacher (funDefs @ constDefs @ constrDefs @ funDecls @ asserts) constDefs []
    }


  // do for x in (funDefs
  // @ constDefs
  // @ constrDefs
  // @ funDecls
  // @ asserts) do
  // printfn $"xxx {program2originalCommand x}"

  // let toOrigCmds = List.map program2originalCommand

  state {
    do!
      Debug.Print.hornInput (
        let content = List.map (program2originalCommand >> toString) cmds |> join "\n" in
        $"(set-logic HORN)\n(set-option :produce-proofs true)\n{content}\n(check-sat)\n(get-proof)"
      )

    match! Debug.Duration.go (lazy teacherRes) "HORN.LIA" with
    | Some (result.SAT _, _) -> return "SAT"
    | Some (result.UNSAT (Some (proof, dbgProof)), _) ->
      // let proof, dbgProof =
      //   z3Process.z3proof
      //     (toOrigCmds funDefs)
      //     (toOrigCmds constDefs)
      //     (toOrigCmds constrDefs)
      //     (toOrigCmds funDecls)
      //     (toOrigCmds asserts)

      do! Debug.Print.proof dbgProof
      do! Debug.Print.next

      match! learner (adtDecs, recs) adtConstrs funDefs asserts constDefs constrDefs funDecls proof pushed with
      | Result.Ok (defConsts', defConstrs', pushed') ->
        return! teacher (adtDecs, recs) adtConstrs funDefs defConsts' defConstrs' funDecls asserts pushed'
      | Error e -> return e
    | o ->
      failwith $"{o}"
      return "failwith A"
  }


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

      helper Set.empty q Set.empty
      |> fst
      |> fun xs -> Set.toList xs |> List.addLast query
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
    | Assert (App (_, args)) -> bindArgs srcArguments args (App (name, arguments)) |> Assert
    | Assert (ForAll (names, App (_, args))) ->
      ForAll (names, bindArgs srcArguments args (App (name, arguments))) |> Assert
    | Assert (Implies (body, (App (_, args) as head))) ->
      bindArgs srcArguments args (Implies (And [| body; head |], App (name, arguments)))
      |> Assert
    | Assert (ForAll (names, Implies (body, (App (_, args) as head)))) ->
      bindArgs srcArguments args (ForAll (names, Implies (And [| body; head |], App (name, arguments))))
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

    let asserts' = List.filter (fun x -> trivialImpls |> List.contains x |> not) asserts

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
                | Assert x -> x.StructEq l
                | _ -> false)
              |> List.map (function
                | Assert (App (_, fArgs))
                | Assert (ForAll (_, App (_, fArgs))) -> bindArgs (lArgs) (fArgs) (App (rName, rArgs)) |> Assert
                | Assert (Implies (body, App (_, fArgs)))
                | Assert (ForAll (_, Implies (body, App (_, fArgs)))) ->
                  bindArgs (lArgs) (fArgs) (Implies (body, App (rName, rArgs))) |> Assert
                | _ -> failwith "__unimplemented__ ()")


            acc @ lFacts
          | _ -> acc)
        []

    newAsserts @ asserts'

  let mkSingleQuery funDecs asserts =
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



module ImpliesWalker =
  let assertBodies =
    List.choose (function
      | Assert b -> Some b
      | _ -> None)

  let implBody =
    List.choose (function
      | Implies (b, _) -> Some b
      | _ -> None)

  let funcDecls =
    List.filter (function
      | Decl _ -> true
      | _ -> false)

  let asserts =
    List.filter (function
      | Assert _ -> true
      | _ -> false)

  let declNames =
    List.choose (function
      | Decl (n, _) -> Some n
      | _ -> None)

  let axioms = axiomAsserts id
  let implications = impliesAsserts id

  let withoutAxioms cmds =
    let appNames = funcDecls cmds |> declNames
    List.filter (fun x -> axioms (asserts cmds) x |> List.isEmpty) appNames

  let haveApp name =
    Array.tryFind (function
      | App (n, _) when n = name -> true
      | _ -> false)
    >> function
      | Some _ -> true
      | None -> false

  let isRecClause =
    function
    | Assert (Implies (And body, App (name, _)))
    | Assert (ForAll (_, Implies (And body, App (name, _)))) -> haveApp name body
    | Assert (Implies (body, App (name, _)))
    | Assert (ForAll (_, Implies (body, App (name, _)))) -> haveApp name [| body |]
    | _ -> false

  let roots cmds =
    List.map (implications cmds) (withoutAxioms cmds)
    |> List.concat
    |> List.filter (not << isRecClause)

  type kids<'a> = 'a tree list list

  and tree<'a> =
    | Node of 'a tree * 'a kids
    | Leaf of 'a

  let tst =
    Node (
      Leaf "B A -> P",
      [ [ Leaf "B"; Leaf "B'"; Leaf "B''" ]
        [ Node (
            Leaf "C B -> A",
            [ [ Node (Leaf "x x -> C", [ [ Leaf "X"; Leaf "X'" ]; [ Leaf "X"; Leaf "X'" ] ]) ]
              [ Node (Leaf "y -> B", [ [ Leaf "y"; Leaf "y'"; Leaf "y''" ] ]) ]
              [ Leaf "B" ] ]
          )
          Node (Leaf "B B -> A", [ [ Leaf "B"; Leaf "B'" ]; [ Leaf "B"; Leaf "B'" ] ]) ] ]
    )

  let uniqVars =
    let rec helper i =
      function
      | Leaf e ->
        let e, i =
          List.fold (fun (e, i) var -> substituteVar var (Var $"fld-{i}-{expr2smtExpr var}") e, i + 1) (e, i) (vars e)

        Leaf e, i
      | Node (x, xs) ->
        let x, i = helper i x

        let xs, i =
          List.fold
            (fun (acc: _ tree list list, i) (xs: _ tree list) ->
              let x, i =
                List.fold
                  (fun (acc, i) x ->
                    let xs, i = helper i x
                    (acc @ [ xs ], i + 1))
                  ([], i)
                  xs

              (acc @ [ x ], i))
            ([], i)
            xs

        Node (x, xs), i

    helper 0 >> fst

  let collect cmds =
    let queue = roots cmds |> assertBodies

    let rec collect' used =
      function
      | ForAll (_, Implies (body, App (name, _))) as value
      | (Implies (body, App (name, _)) as value) ->
        let appNames' = Implies.bodyArgs' body |> App.appNames
        let facts = List.map (axioms cmds) appNames'

        let impls =
          List.map
            (implications cmds
             >> List.filter (function
               | Assert (ForAll (_, Implies (body, App (n, _))))
               | Assert (Implies (body, App (n, _))) ->
                 App.appNames (Implies.bodyArgs' body)
                 |> List.fold (fun acc b -> acc && not <| List.contains b (n :: name :: used)) true
               | _ -> false))
            appNames'

        Node (
          Leaf value,
          List.zip facts impls
          |> List.map (function
            | [], is -> List.map (collect' (name :: used)) (assertBodies is)
            | fs, _ -> List.map Leaf (assertBodies fs))
        )

    List.map (collect' []) queue

  let eqs = List.map Eq

  let andVal =
    function
    | [ x ] -> x
    | xs -> Expr.And xs

  let orVal =
    function
    | [ x ] -> x
    | xs -> Expr.Or xs

  let rec bind x (kids: 'a tree list list) =
    match x with
    | Leaf (Implies (b, App _))
    | Leaf (ForAll (_, Implies (b, App _))) ->
      let restrictions = notAppRestrictions b
      let appRestrictions = appRestrictions b

      List.zip appRestrictions kids
      |> List.choose (function
        | App (_, args), xs
        | ForAll (_, App (_, args)), xs ->
          List.choose
            (function
            | Leaf (App (_, args'))
            | Leaf (ForAll (_, App (_, args'))) -> Some (List.zip args args' |> eqs)
            | Leaf (Implies (restriction, App (_, args')))
            | Leaf (ForAll (_, Implies (restriction, App (_, args')))) ->
              Some (List.zip args args' |> eqs |> List.append (Implies.bodyArgs' restriction))
            | Node (Leaf (Implies (_, App (_, args'))), _)
            | Node (Leaf (ForAll (_, Implies (_, App (_, args')))), _) as x ->
              Some (List.zip args args' |> eqs |> List.append (formula x))
            | _ -> None)
            xs
          |> List.map (List.append restrictions >> andVal)
          |> orVal
          |> Some
        | _ -> None)
    | _ -> []

  and formula =
    let rec helper =
      function
      | Node (impl, kids) -> bind impl kids
      | _ -> []

    helper

  let recoverFacts cmds =
    let collected = collect cmds
    let collected' = List.map uniqVars (collect cmds)

    let toRm =
      List.choose
        (function
        | Node (Leaf x, _) -> Some (Assert x)
        | _ -> None)
        collected

    let heads =
      List.choose
        (function
        | Node (Leaf (Implies (_, h)), _)
        | Node (Leaf (ForAll (_, Implies (_, h))), _) -> Some h
        | _ -> None)
        collected'

    List.map (formula >> Expr.And) collected'
    |> flip List.zip heads
    |> List.map (fun (b, h) ->
      Implies (andVal (notAppRestrictions b @ Implies.bodyArgs' b), h)
      |> forAll
      |> Assert)
    |> fun xs -> xs @ (List.filter (not << flip List.contains toRm) cmds)
// xs

let rec solver
  (adtDecs, recs)
  (adtConstrs: Map<ident, symbol * Type list>)
  funDefs
  constDefs
  constrDefs
  funDecls
  (asserts: Program list)
  =

  let funDecls, asserts =
    let funDecls', asserts' =
      HenceNormalization.mkSingleQuery funDecls asserts
      |> fun (decs, asserts) -> decs, List.map HenceNormalization.restoreVarNames asserts

    funDecls', AssertsMinimization.assertsMinimize asserts' (queryAssert List.head asserts')

  let envLearner, solverLearner = newLearner ()
  let decConsts = decConsts constDefs
  let startCmds = funDefs @ decConsts @ (notZeroFunConsts constrDefs)

  solverLearner.Push ()


  state {
    do kek startCmds
    // do! Solver.setCommands startCmds
    do! Solver.setCommandsKEK startCmds
    // let! setSofts = Solver.setSoftConsts constDefs
    
    let! setSofts = Solver.setSoftConstsKEK constDefs
    do kek setSofts
    do! Debug.Print.redlogInput ""
    do! Debug.Print.redlogOutput ""

    do!
      Debug.Print.smtInput (
        let content =
          List.map (program2originalCommand >> toString) (startCmds @ setSofts)
          |> join "\n" in

        $"(set-logic NIA)\n{content}"
      )

    match! Debug.Duration.go (lazy Solver.solveLearner constDefs) "(INIT)SMT.NIA" with
    | timeout.Timeout ->
          let x = randomValues (List.choose (function
              | Def (n, _, _, _) -> Some n
              | _ -> None) constDefs)
                       |> List.map (fun (n, v) -> Def (n, [], Integer, Int v))
          return! teacher (adtDecs, recs) adtConstrs funDefs x constrDefs funDecls asserts (startCmds @ setSofts)
    | timeout.Ok (Result.Ok x) ->
      return! teacher (adtDecs, recs) adtConstrs funDefs x constrDefs funDecls asserts (startCmds @ setSofts)
    | timeout.Ok (Error _) -> return "UNKNOWN"
  }
  |> run (statement.Init envLearner solverLearner)

let sort2type =
  function
  | BoolSort -> Boolean
  | ADTSort name -> ADT name
  | _ -> Integer

let approximation file =
  let recs, _, _, _, dataTypes, _, _, _, _ = Linearization.linearization file
  let p = Parser.Parser false
  let cmds = p.ParseFile file

  let adtDecs =
    cmds
    |> List.mapi (fun i ->
      function
      | Command (DeclareDatatypes adts) ->
        adts
        |> List.map (fun (adtName, decl) ->
          decl
          |> List.choose (function
            | ElementaryOperation (constrName, sorts, _), _, _ ->
              Some (constrName, (adtName, i, List.map sort2type sorts))
            | _ -> None))
        |> List.concat
        |> Some
      | Command (DeclareDatatype (adtName, decl)) ->
        decl
        |> List.choose (function
          | ElementaryOperation (constrName, sorts, _), _, _ ->
            Some (constrName, (adtName, i, List.map sort2type sorts))
          | _ -> None)
        |> Some
      | _ -> None)
    |> List.filter Option.isSome
    |> List.map Option.get
    |> List.concat
    |> Map

  let defConstants =
    let rec helper =
      function
      | smtExpr.Apply (ElementaryOperation (ident, _, _), _)
      | smtExpr.Apply (UserDefinedOperation (ident, _, _), _) when ident.Contains "c_" ->
        [ Def (ident, [], Integer, Int 0) ]
      | smtExpr.Apply (_, exprs) -> List.collect helper exprs
      | smtExpr.And exprs -> List.collect helper exprs
      | smtExpr.Or exprs -> List.collect helper exprs
      | smtExpr.Not expr -> helper expr
      | smtExpr.Hence (expr1, expr2) -> helper expr1 @ helper expr2
      | smtExpr.QuantifierApplication (_, expr) -> helper expr
      | _ -> []

    List.collect (function
      | Definition (DefineFun (_, _, _, expr)) -> helper expr
      | _ -> [])

  let decFuns =
    List.choose (function
      | Command (DeclareFun _) as x -> Some x
      | _ -> None)

  let rec asserts =
    List.choose (function
      | originalCommand.Assert _ as x -> Some x
      | _ -> None)

  let rec defFuns =
    List.choose (function
      | Definition _ as x -> Some x
      | _ -> None)

  (recs, adtDecs, defFuns cmds, dataTypes, defConstants dataTypes, decFuns cmds, asserts cmds)

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


let run file dbg timeLimit =
  dbgPath <- dbg

  let recs, adtConstrs, defFuns, liaTypes, defConstants, declFuns, asserts =
    // try
    approximation file
  // with _ ->
  // printfn "ERR APPROXIMATION"
  // Environment.Exit 0
  // (Map.empty, [], [], [], [], [])
  let funDecls = List.map origCommand2program declFuns

  let adtDecs =
    adtConstrs
    |> Map.fold
      (fun (acc: Map<string, int * Constructor list>) constrName (adtName, i, argTypes) ->
        acc
        |> Map.change adtName (function
          | Some constrs -> Some <| (i, (constrName, argTypes) :: snd constrs)
          | None -> Some (i, [ (constrName, argTypes) ])))
      Map.empty
    |> Map.toList
    |> List.sortBy (fun (_, (i, _)) -> i)
    |> List.map (fun (x, (_, y)) -> (x, y))
    |> List.map (List.singleton >> DeclDataType)

  let adtConstrs = adtConstrs |> Map.map (fun k (n, _, ts) -> (n, ts))
  let asserts' = List.map origCommand2program asserts

  let appNames =
    funDecls
    |> List.choose (function
      | Decl (n, _) -> Some n
      | _ -> None)

  let asserts'' =
    asserts'
    |> List.choose (function
      | Assert x -> Some (Assert (apply2app appNames x))
      | _ -> None)

  let toPrograms = List.map origCommand2program

  let v, _ =
    solver (adtDecs, recs) adtConstrs (toPrograms defFuns) defConstants (toPrograms liaTypes) funDecls asserts''

  v, durations, ""
