module ProofBased.Solver

open System.Collections
open System.Collections.Generic
open System.Diagnostics
open System
open System.IO
open System.Numerics
open System.Text.RegularExpressions
open CataHornSolver
open CataHornSolver.z3Process
open CataHornSolver.z3Process.Instances
open CataHornSolver.z3Process.Interpreter
open CataHornSolver.Scheme

open Microsoft.FSharp.Core
open NUnit.Framework
open Process
open SMTLIB2
open SMTLIB2.Parser
open Tree
open Z3Interpreter
open Z3Interpreter.AST

let mutable dbgPath = None
// let mutable dbgPath = Some ("/home/andrew/adt-solver/benchs/results/out")


open Tree.Tree
open ProofBased.Utils
open Z3Interpreter.Interpreter
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
    learner: Instances.learner
    stopwatch: Stopwatch
    context: z3Process.context
    fTimes: string option }

  static member Init env learner fTimes =
    { iteration = 0
      env = env
      learner = learner
      stopwatch = Stopwatch ()
      context = context.Init ()
      fTimes = fTimes }

let emptyEnv = { ctxFuns = Map.empty; actives = [] }



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
    | ForAllTyped (_, expr)
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
    | ForAllTyped (_, expr)
    | Implies (expr, _) -> helper acc expr
    | _ -> acc

  helper []


let impliesAsserts clarify asserts name =
  asserts
  |> List.filter (function
    | Assert (ForAllTyped (_, Implies (_, App (n, _))))
    | Assert (Implies (_, App (n, _))) when n = name -> true
    | _ -> false)
  |> clarify

let axiomAsserts clarify asserts name =
  asserts
  |> List.filter (function
    | Assert (Implies (body, App (n, _)))
    | Assert (ForAllTyped (_, Implies (body, App (n, _)))) when body |> appRestrictions |> List.isEmpty && n = name ->
      true
    | Assert (App (n, _))
    | Assert (ForAllTyped (_, App (n, _))) when n = name -> true
    | _ -> false)
  |> clarify

let queryAssert clarify asserts =
  asserts
  |> List.filter (function
    | Assert (ForAllTyped (_, Implies (_, Bool false)))
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
    | ForAllTyped (vars, expr) ->
      ForAllTyped (List.map (fun (n, t) -> (if n = oldName then newName else n), t) vars, this expr)
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
    // | ForAll (_, expr)
    | ForAllTyped (_, expr)
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

// let forAllInt expr =
//   let rec helper acc =
//     function
//     | Int _
//     | Bool _ -> acc
//     | Eq (expr1, expr2)
//     | Lt (expr1, expr2)
//     | Gt (expr1, expr2)
//     | Le (expr1, expr2)
//     | Ge (expr1, expr2)
//     | Add (expr1, expr2)
//     | Subtract (expr1, expr2)
//     | Mod (expr1, expr2)
//     | Implies (expr1, expr2)
//     | Mul (expr1, expr2) -> helper (helper acc expr1) expr2
//     | App (_, exprs) -> List.fold helper acc exprs
//     | And exprs
//     | Or exprs -> Array.fold helper acc exprs
//     | ForAllTyped (_, expr)
//     | Not expr
//     | Neg expr -> helper acc expr
//     | Var n -> acc |> Set.add n
//     | Apply (_, exprs) -> List.fold helper acc exprs
//     | Ite (expr1, expr2, expr3) -> List.fold helper acc [ expr1; expr2; expr3 ]
//
//   ForAllTyped (helper Set.empty expr |> Set.toArray, expr)

let defFunBody args i =
  List.zip args [ i + 1 .. i + 1 + args.Length - 1 ]
  |> List.map (fun (n, i) -> Mul (Apply ($"c_{i}", []), Var n))
  |> List.fold (fun (acc, i) arg -> (Add (acc, arg), i + 1)) (Apply ($"c_{i}", []), i)



type timeout<'a> =
  | Timeout
  | Ok of 'a


let banValues constDefs =
  match constDefs with
  | [] -> Assert (Bool true)
  | _ ->
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

let redlog t definitions formula (fTimes: string option) = timeout.Timeout
// match Redlog.runRedlog t definitions formula fTimes with
// | Some (Result.Ok v) -> timeout.Ok (Assert (smtExpr2expr' v))
// | None -> timeout.Timeout
// | Some (Error e) -> failwith $"redlog-output: {e}"

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
    failwith "ERR NO_SIMPLEST"
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

  let head =
    function
    | Implies (_, h) -> Some h
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
  let rec ops2applies =
    function
    | Eq (expr1, expr2) -> Apply ("=", [ ops2applies expr1; ops2applies expr2 ])
    | Lt (expr1, expr2) -> Apply ("<", [ ops2applies expr1; ops2applies expr2 ])
    | Gt (expr1, expr2) -> Apply (">", [ ops2applies expr1; ops2applies expr2 ])
    | Le (expr1, expr2) -> Apply ("<=", [ ops2applies expr1; ops2applies expr2 ])
    | Ge (expr1, expr2) -> Apply (">=", [ ops2applies expr1; ops2applies expr2 ])
    | Mod (expr1, expr2) -> Apply ("mod", [ ops2applies expr1; ops2applies expr2 ])
    | Add (expr1, expr2) -> Apply ("+", [ ops2applies expr1; ops2applies expr2 ])
    | Subtract (expr1, expr2) -> Apply ("+", [ ops2applies expr1; ops2applies <| Neg expr2 ])
    | Mul (expr1, expr2) -> Apply ("*", [ ops2applies expr1; ops2applies expr2 ])
    | Neg expr -> Apply ("-", [ ops2applies expr ])
    | And exprs -> Apply ("and", List.ofArray <| Array.map ops2applies exprs)
    | Or exprs -> Apply ("or", List.ofArray <| Array.map ops2applies exprs)
    | Not expr -> Apply ("not", [ ops2applies expr ])
    | Implies (expr1, expr2) -> Apply ("=>", [ ops2applies expr1; ops2applies expr2 ])
    | Apply (n, exprs) -> Apply (n, List.map ops2applies exprs)
    | ForAllTyped (vars, expr) -> ForAllTyped (vars, ops2applies expr)
    | App (n, exprs) -> App (n, List.map ops2applies exprs)
    | Ite (expr1, expr2, expr3) -> Apply ("ite", [ ops2applies expr1; ops2applies expr2; ops2applies expr3 ])
    | otherwise -> otherwise


  type raw =
    | Int
    | Bool
    | ADT of string
    | Any

    static member (+) (x, y) =
      match x, y with
      | Any, t
      | t, Any -> t
      | x, y when x = y -> x
      | _ -> failwith $"wrong types {x} {y}"

  let type2raw =
    function
    | Integer -> raw.Int
    | Boolean -> raw.Bool
    | Type.ADT n -> raw.ADT n

  let adtSig (c, (adt, ts)) =
    (c, (raw.ADT adt, List.map type2raw ts))

  let defined args =
    [ ("<", (raw.Bool, [ raw.Int; raw.Int ]))
      (">", (raw.Bool, [ raw.Int; raw.Int ]))
      ("<=", (raw.Bool, [ raw.Int; raw.Int ]))
      (">=", (raw.Bool, [ raw.Int; raw.Int ]))
      ("=", (raw.Bool, [ raw.Any; raw.Any ]))
      ("distinct", (raw.Bool, [ raw.Any; raw.Any ]))
      ("mod", (raw.Int, [ raw.Int; raw.Int ]))
      ("div", (raw.Int, [ raw.Int; raw.Int ]))
      ("+", (raw.Int, [ raw.Int; raw.Int ]))
      ("-", (raw.Int, [ raw.Int ]))
      ("*", (raw.Int, [ raw.Int; raw.Int ]))
      ("and", (raw.Bool, List.map (fun _ -> raw.Bool) args))
      ("or", (raw.Bool, List.map (fun _ -> raw.Bool) args))
      ("not", (raw.Bool, [ raw.Bool ]))
      ("=>", (raw.Bool, [ raw.Bool; raw.Bool ]))
      ("ite", (raw.Any, [ raw.Bool; raw.Any; raw.Any ])) ]

  let applyIntFn n args =
    (n, (raw.Int, List.map (fun _ -> raw.Int) args))

  let intFuns adts expr =
    let rec helper defined acc =
      function
      | Apply (n, exprs) when not <| List.contains n defined ->
        Seq.fold (helper defined) (flip Set.add acc <| applyIntFn n exprs) exprs
      | Apply (_, exprs) -> Seq.fold (helper defined) acc exprs
      | _ -> acc

    helper (List.map fst <| adts @ defined []) Set.empty expr

  let resolveAny: (Name * raw) list -> Map<Name, raw> =
    Seq.groupBy fst
    >> Seq.map (fun (k, vs) -> k, vs |> Seq.map snd |> Seq.toList |> Seq.fold (+) raw.Any)
    >> Map.ofSeq

  //adtsSIG INTFNS
  let clarifyInternal fns =
    let rec helper t acc =
      function
      | Apply (n, args) ->
        let ts =
          Map.tryFind n (Map <| defined args)
          |> function
            | Some (_, ts) -> ts
            | None -> snd <| Map.find n fns

        List.fold (fun acc (arg, t) -> helper t acc arg) acc (List.zip args ts)
      | Var n -> (n, t) :: acc
      | _ -> acc

    helper raw.Any [] >> resolveAny

  let clarifyExternal fns =
    let rec helper acc =
      function
      | Apply ("=", [ Var x; Apply (n, args) ])
      | Apply ("=", [ Apply (n, args); Var x ])
      | Apply ("distinct", [ Var x; Apply (n, args) ])
      | Apply ("distinct", [ Apply (n, args); Var x ]) ->
        let t =
          Map.tryFind n (Map <| defined args)
          |> function
            | Some (t, _) -> t
            | None -> fst <| Map.find n fns

        List.fold helper ((x, t) :: acc) args
      | Apply (_, args) -> List.fold helper acc args
      | _ -> acc

    helper [] >> resolveAny

  let pSort (a, b) = (min a b, max a b)

  let transitiveVals =
    let rec helper acc =
      function
      | Apply ("=", [ Var x; Var y ])
      | Apply ("distinct", [ Var y; Var x ]) when x <> y -> flip Set.add acc <| pSort (x, y)
      | Apply (_, args) -> List.fold helper acc args
      | _ -> acc

    helper Set.empty
    >> fun xs -> Set <| (List.map swap (Set.toList xs)) @ (Set.toList xs)

  let rec chain (q: _ Set) (ps: (Name * Name) list) used acc =
    match List.ofSeq q with
    | [] -> acc
    | _ ->
      let neighbours v =
        Seq.choose
          (function
          | x, y when x = v && not <| List.contains v used -> Some y
          | _ -> None)
          ps
        |> Set

      let v = q.MinimumElement
      let used' = v :: used
      let q' = Set (q.Remove v |> Seq.append <| neighbours v)
      chain q' ps used' <| Set (Seq.append (Set.add v acc) <| neighbours v)

  let chains ps =
    let rec helper (q: _ Set) acc =
      match List.ofSeq q with
      | [] -> acc
      | _ ->
        let v = q.MinimumElement
        let chain = chain (Set.singleton v) ps [] Set.empty

        helper (Set.difference q chain) <| chain :: acc

    flip helper []
    <| List.fold (fun acc (x, y) -> Set.add x acc |> Set.add y) Set.empty ps

  let clarifyTransitive clarified expr =
    transitiveVals expr
    |> List.ofSeq
    |> chains
    |> List.map List.ofSeq
    |> fun nss ->
        List.map
          (fun ns ->
            List.map
              (fun n ->
                Map.tryFind n clarified
                |> function
                  | Some t -> t
                  | _ -> raw.Any)
              ns
            |> List.fold (+) raw.Any)
          nss
        |> List.map2 (fun ns t -> List.map (fun n -> n, t) ns) nss
        |> List.concat

  let collect = resolveAny >> Map.toList >> Set

  let raw2type =
    function
    | raw.Int
    | raw.Any -> Integer
    | raw.Bool -> Boolean
    | raw.ADT n -> Type.ADT n

  let clarify: (string * sort) list -> Map<ident, symbol * Type list> -> Expr -> Expr * (Name * Type) list =
    fun sortVars (adts: Map<ident, symbol * Type list>) expr ->
      let constrSigs = List.map adtSig <| Map.toList adts
      let expr' = ops2applies expr
      let intFuns = intFuns constrSigs <| expr'
      let funSymbols = constrSigs @ List.ofSeq intFuns
      let clarifiedInternal = flip clarifyInternal expr' <| Map funSymbols
      let clarifiedExternal = flip clarifyExternal expr' <| Map funSymbols

      let clarifiedByFuns =
        collect <| Map.toList clarifiedInternal @ Map.toList clarifiedExternal

      // printfn $"clarifiedByFuns"
      // for x in clarifiedByFuns do printfn $"{x}"
      // printfn $"{expr2smtExpr expr}"
      // printfn $"-----------------"
      // printfn $"{expr2smtExpr expr'}"

      expr,
      collect
      <| Set.toList clarifiedByFuns @ clarifyTransitive (Map clarifiedByFuns) expr'
      |> Set.toList
      |> List.map (fun (n, t) ->
        n,
        Map.tryFind n (Map sortVars)
        |> function
          | None -> raw2type t
          | Some s ->
            match s with
            | IntSort -> Integer
            | ADTSort adt -> Type.ADT adt
            | _ -> Type.Boolean)

let tttt () =
  TypeClarification.clarify
    []
    (Map
      [ "%Account-0", ("%Account", [ Integer ])
        "~mut<%Account>", ("~Mut<%Account>", [ ADT "%Account"; ADT "%Account" ]) ])
    (And
      [| Eq (Var "xYYYY", Apply ("~mut<%Account>", [ Var "x19"; Var "x20" ]))
         Eq (Var "xYYYY", Var "xxxxxxx")
         Eq (Var "x18", Var "x25")
         Eq (Var "x18", Var "x42")
         Eq (Var "x30", Var "x43")
         Eq (
           Apply ("~mut<%Account>", [ Var "x19"; Var "x20" ]),
           Apply (
             "~mut<%Account>",
             [ Apply ("%Account-0", [ Var "x16" ])
               Apply ("%Account-0", [ Add (Var "x16", Var "x18") ]) ]
           )
         )
         Eq (
           Apply ("~mut<%Account>", [ Var "x26"; Var "x27" ]),
           Apply (
             "~mut<%Account>",
             [ Apply ("%Account-0", [ Var "x23" ])
               Apply ("%Account-0", [ Subtract (Var "x23", Var "x25") ]) ]
           )
         )
         Eq (Apply ("~mut<%Account>", [ Var "x5"; Var "x41" ]), Apply ("~mut<%Account>", [ Var "x19"; Var "x20" ]))
         Eq (
           Apply ("~mut<%Account>", [ Apply ("%Account-0", [ Var "x30" ]); Apply ("%Account-0", [ Var "x11" ]) ]),
           Apply ("~mut<%Account>", [ Var "x26"; Var "x27" ])
         )
         Eq (
           Ite (Eq (Ite (Eq (Var "x11", Subtract (Var "x30", Var "x18")), Int 1L, Int 0L), Int 0L), Int 1L, Int 0L),
           Int 1L
         ) |])
  |> fun (_, xs) -> ()

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

// let doesExist funDefs adtDecs resolvent typedVars =
//   let clause =
//     seq {
//       yield! List.map DeclConst typedVars
//       yield! Assert resolvent |> List.singleton
//     }
//     |> Seq.toList
//
//   adtDecs @ funDefs @ clause

let smtEQuery header query vars =
  let clause =
    seq {
      yield! List.map DeclConst vars
      yield! Assert query |> List.singleton
    }
    |> Seq.toList

  header @ clause



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

module State =
  let curState = State (fun st -> st, st)

  let setState s = State (fun st -> (), s)


module Solver =
  let cmds = State (fun st -> st.context.cmds, st)

  let fTimes = State (fun st -> st.fTimes, st)

  let sortByQuantifiers xs = xs
  // Assert.bodies xs
  // |> List.map (function
  // | ForAll (ns, _) as e -> Array.length ns, e
  // | ForAllTyped (ns, _) as e -> List.length ns, e
  // | e -> (0, e))
  // |> List.sortByDescending fst
  // |> List.map (snd >> Assert)


  let rememberConstraint x =
    State (fun st ->
      (),
      { st with
          context =
            { st.context with
                lastConsraint = sortByQuantifiers <| x :: st.context.lastConsraint } })

  let rmRememberedConstraint =
    State (fun st ->
      (),
      { st with
          context =
            { st.context with
                lastConsraint =
                  match st.context.lastConsraint with
                  | _ :: xs -> xs
                  | _ -> []
                cmds =
                  match st.context.lastConsraint with
                  | [] -> st.context.cmds
                  | c :: _ -> List.filter ((<>) c) st.context.cmds } })

  let setCommandsKEK (cmds: Program list) =
    State (fun st ->
      (),
      { st with
          context =
            { st.context with
                snapshot =
                  { st.context.snapshot with
                      cmds = st.context.cmds }
                cmds = st.context.cmds @ cmds } })

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
          context =
            { st.context with
                softConsts =
                  cmds
                  |> List.choose (function
                    | Def (n, _, _, _) -> Some $"{n}"
                    | _ -> None) } })


  let solveFeasible tl =
    State (fun st ->
      match solve tl [] [] instance.Checker st.context.cmds [] [] dbgPath -1 st.fTimes with
      | Some (Interpreter.SAT _, _), _ -> Result.Ok (), st
      | _ -> Error (), st)

  let solveLearner tl defConsts =
    State (fun st ->
      match
        solveLearner
          tl
          []
          []
          st.context.cmds
          (defNames defConsts)
          st.context.softConsts
          (dbgPath)
          st.iteration
          st.learner
          st.fTimes
      with
      | Some (UNKNOWN, _), inputs -> (timeout.Ok (Result.Error "UNKNOWN~"), inputs), st

      | Some (Interpreter.SAT (Some xs), softs), inputs ->
        (timeout.Ok (Result.Ok xs), inputs),
        { st with
            context =
              // printfn "------------------------->>>>>"
              // for x in xs do printfn $"{x}";
              // printfn "<<<<<-------------------------"
              { st.context with
                  softConsts = softs

                  snapshot = { st.context.snapshot with consts = xs } } }
      | Some (Interpreter.UNSAT (None), softs), inputs ->
        failwith "unknown"

        (timeout.Ok (Result.Error "UNKNEONWOWN"), inputs),
        { st with
            context = { st.context with softConsts = softs } }
      | None, inputs -> (Timeout, inputs), st

    )

// match solve instance.Learner st.context.cmds defConsts with
// | Interpreter.SAT (Some xs) -> timeout.Ok (Result.Ok xs), st
// | Interpreter.UNSAT (Some _) -> timeout.Ok (Result.Error "UNKNEONWOWN"), st)

module Debug =
  module Duration =
    let private runStopWatch durationName =
      State (fun st ->
        curDuration <- durationName
        // printfn $"{curDuration}"
        st.stopwatch.Start ()
        ((), st))

    let private stopStopwatch =
      State (fun st ->
        st.stopwatch.Stop ()
        let duration = st.stopwatch.ElapsedMilliseconds
        // printfn $"{duration}"
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

    let iteration = State (fun st -> st.iteration, st)

    let private write file s =
      State (fun st -> (writeDbg file s st.iteration), st)

    let private writeMany files xs =
      State (fun st ->
        for f, x in List.zip files xs do
          writeDbg f x st.iteration

        (), st)

    let smtInput s =
      State (fun st ->
        let actives = join " " (List.map toString st.env.actives)
        (writeDbg "smt-input.smt2" $"{s}\n(check-sat-assuming ({actives}))\n(get-model)" st.iteration), st)

    let smtInputs inputs = State (fun st -> (), st)
    // writeMany (List.mapi (fun i _ -> $"smt-input-{i}.smt2") inputs) inputs

    let redlogInput = write "redlog-input.smt2"
    let redlogOutput = write "redlog-output.smt2"
    let hornInput = write "horn-input.smt2"
    let smtADTLIA = write "smt-ADT-LIA.smt2"
    let proof = write "proof.smt2"

let adtDecls (adtDecs, recs: symbol list list) =
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

  recs @ nonRec


let feasible tl (adtDecs, (recs: symbol list list)) funDefs vars resolvent fTimes =
  let env = emptyEnv
  // let solver = env.ctxSlvr.MkSolver "ALL"
  // solver.Push ()

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

  state {
    let q = smtEQuery (funDefs @ adtDecs) resolvent vars

    do! Solver.setCommandsKEK q
    let! r = Solver.solveFeasible tl
    return (r, q)
  }
  |> run (statement.Init env CVC fTimes)


module Resolvent =
  let proofTree proof =
    let rec helper (HyperProof (_, hyperProofs, head)) =
      match hyperProofs with
      | [] -> head |> smtExpr2expr |> (fun x -> Node (x, []))
      | _ -> Node (head |> smtExpr2expr, hyperProofs |> List.map helper)

    helper proof

  let implsWhichContains appNames cmds name =
    let impls = impliesAsserts id cmds name |> Assert.bodies

    let bodyAppNames = Implies.bodyArgs' >> App.appNames
    let isContainsApps = bodyAppNames >> List.sort >> (appNames |> List.sort |> (=))

    List.filter
      (function
      | Implies (b, _) -> isContainsApps b
      | _ -> false)
      impls

  let kidVals: Expr Tree.tree -> Expr list = Tree.kids >> List.map Tree.value

  let assertId headArgs = List.last headArgs

  let assertBy asserts id =
    List.find
      (function
      | Assert (Implies (_, App (_, args)))
      | Assert (ForAllTyped (_, Implies (_, App (_, args))))
      | Assert (App (_, args))
      | Assert (ForAllTyped (_, App (_, args))) when (not <| List.isEmpty args) && assertId args = id -> true
      | _ -> false)
      asserts


  let rec assertsTree asserts consts decs =
    function
    | Node (Bool false, ts) ->
      let query = queryAssert (Assert.bodies >> List.head >> List.singleton) asserts

      Node (query, List.map (assertsTree asserts consts decs) ts)
    | Node (Apply (name, _), []) ->
      let axioms = axiomAsserts (Assert.bodies) asserts name

      Node (axioms, [])
    // | Node (Apply (name, args), []) ->
    // printfn $"{name}"
    // Node (List.choose Expr.forallBody (Assert.bodies [ assertBy asserts <| assertId args ]), [])
    | Node (Apply (name, args), ts) ->
      let from =
        List.map Tree.value ts
        |> List.choose (function
          | Apply (n, _) -> Some n
          | _ -> None)

      Node (implsWhichContains from asserts name, List.map (assertsTree asserts consts decs) ts)
    // Node (List.choose Expr.forallBody (Assert.bodies [ assertBy asserts <| assertId args ]), List.map (assertsTree asserts consts decs) ts)
    | _ -> __unreachable__ ()

  let treeOfExprs =
    Tree.fmap (
      List.choose (function
        | Assert (ForAllTyped (vars, x)) -> Some (vars, x)
        | Assert x -> Some ([], x)
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
      | ForAllTyped (_, expr)
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

  let varNames =
    vars
    >> List.choose (function
      | Var n -> Some n
      | _ -> None)

  let smtEQuery sortVars adtConstrs funDefs adtDecs resolvent =
    TypeClarification.clarify sortVars adtConstrs resolvent
    ||> smtEQuery (funDefs @ adtDecs)


let forallTyped (origAsserts: ((symbol * Type) list * Expr) list) expr =
  // let map =
  //   List.map (fun (vars, e) -> (toString <| expr2smtExpr e, vars)) origAsserts
  //   |> Map
  // for x in List.map snd origAsserts do printfn $"x : {x}"
  let name =
    function
    | Implies (e, _)
    | e ->
      List.choose (function
        | App (n, _)
        | Apply (n, _) when n.Contains "$name_" -> Some n
        | _ -> None)
      <| Implies.bodyArgs' e

  // List.choose
  match expr with
  | App (n, []) as app when n.Contains "$name_" -> Assert app
  | Implies (App ("q", []), Bool false) as q -> Assert q
  // | Apwp (n, vars) as app when n = "q" -> Assert (ForAllTyped (vars, app))
  | o ->
    match
      List.find
        (fun (_, e) -> name e = name expr)
        (List.filter
          (function
          | _, App (n, _)
          | _, Apply (n, _) when n.Contains "$name_" -> false
          | _ -> true)
          origAsserts)
    with
    | [], expr -> Assert expr
    | vars, expr -> Assert (ForAllTyped (vars, expr))
// match Map.tryFind (toString <| expr2smtExpr expr) map with
// | Some ts -> Assert (ForAllTyped (ts, expr))
// | None -> Assert expr

let rec restoreOrigAssertExpr =
  function
  | smtExpr.Apply (op, _) when (Operation.opName op).[0] = '$' -> BoolConst true
  | smtExpr.Apply (op, args) when (Operation.opName op).Contains '$' ->
    smtExpr.Apply (Operation.changeName (((Operation.opName op).Split '$')[0]) op, args)
  | smtExpr.And exprs -> smtExpr.And (List.map restoreOrigAssertExpr exprs)
  | smtExpr.Or exprs -> smtExpr.Or (List.map restoreOrigAssertExpr exprs)
  | smtExpr.Not expr -> restoreOrigAssertExpr expr
  | Hence (expr1, expr2) -> Hence (restoreOrigAssertExpr expr1, restoreOrigAssertExpr expr2)
  | QuantifierApplication ([ ForallQuantifier vars ], expr) ->
    QuantifierApplication ([ ForallQuantifier vars ], restoreOrigAssertExpr expr)
  | otherwise -> otherwise


let restoreOrigExprTree = Tree.fmap <| List.map restoreOrigAssertExpr

let clarifySortsFromTree (tree: Expr tree) (origDecs: (symbol * sort list) list) =
  let origDecs = ("div", [ IntSort; IntSort ]) :: origDecs

  let rec collect acc =
    function
    | Apply ("distinct", [ expr1; expr2 ]) -> collect acc expr1 |> Set.union <| collect acc expr2
    | App ("q", _) -> acc
    | App (n, args)
    | Apply (n, args) ->
      List.fold2
        (fun acc arg sort ->
          match arg with
          | Var var -> Set.add (var, sort) acc
          | otherwise -> collect acc otherwise)
        acc
        args
        (Map.find n <| Map origDecs)
    | Eq (expr1, expr2)
    | Lt (expr1, expr2)
    | Gt (expr1, expr2)
    | Le (expr1, expr2)
    | Ge (expr1, expr2)
    | Mod (expr1, expr2)
    | Add (expr1, expr2)
    | Subtract (expr1, expr2)
    | Implies (expr1, expr2)
    | Mul (expr1, expr2) -> collect acc expr1 |> Set.union <| collect acc expr2
    | Neg expr
    | Not expr -> collect acc expr
    | And exprs
    | Or exprs -> Array.fold collect acc exprs
    | Ite (expr1, expr2, expr3) -> List.fold collect acc [ expr1; expr2; expr3 ]
    | _ -> acc

  fmap (collect Set.empty) tree

module ContractOut =
  let declareArgSorts =
    List.choose (function
      | Command (DeclareFun (name, sorts, _)) -> Some (name, sorts)
      | _ -> None)

  let rec proofBoolArgs cmds =
    function
    | HyperProof (a, hps, smtExpr.Apply (op, [])) when Operation.opName op = "q" ->
      HyperProof (a, List.map (proofBoolArgs cmds) hps, smtExpr.Apply (op, []))
    | HyperProof (a, hps, smtExpr.Apply (op, exprs)) ->
      // printfn $"{Operation.opName op}\n{(Map <| declareArgSorts cmds)}"
      let sorts = Map.find (Operation.opName op) (Map <| declareArgSorts cmds)

      HyperProof (
        a,
        List.map (proofBoolArgs cmds) hps,
        smtExpr.Apply (
          op,
          List.map2
            (fun e s ->
              match s with
              | BoolSort ->
                smtExpr.Apply (ElementaryOperation ("=", [ IntSort; IntSort ], BoolSort), [ e; Number BigInteger.One ])
              | _ -> e)
            exprs
            sorts
        )
      )
    | HyperProof (a, hps, otherwise) -> HyperProof (a, List.map (proofBoolArgs cmds) hps, otherwise)

  let rec rmHelpers (HyperProof (Asserted a, hps, expr)) =
    HyperProof (Asserted (restoreOrigAssertExpr a), List.map rmHelpers hps, restoreOrigAssertExpr expr)

  let rec substitute n f =
    function
    | Ident (ident, sort) when ident = n -> f <| Ident (ident, sort)
    | smtExpr.Apply (op, exprs) -> smtExpr.Apply (op, List.map (substitute n f) exprs)
    | smtExpr.Ite (expr1, expr2, expr3) ->
      smtExpr.Ite (substitute n f expr1, substitute n f expr2, substitute n f expr3)
    | smtExpr.And exprs -> smtExpr.And <| List.map (substitute n f) exprs
    | smtExpr.Or exprs -> smtExpr.Or <| List.map (substitute n f) exprs
    | smtExpr.Not expr -> smtExpr.Not <| substitute n f expr
    | Hence (expr1, expr2) -> Hence (substitute n f expr1, substitute n f expr2)
    | QuantifierApplication (qs, expr) -> QuantifierApplication (qs, substitute n f expr)
    | otherwise -> otherwise

  let modelBoolArgs cmds =
    List.map (function
      | Definition (DefineFun (symbol, argSorts, BoolSort, expr)) when
        Map.containsKey symbol <| Map (declareArgSorts cmds)
        ->
        let sorts = Map.find symbol <| Map (declareArgSorts cmds)
        let vars = List.zip (List.map fst argSorts) sorts

        let boolVars =
          List.filter
            (function
            | _, BoolSort -> true
            | _ -> false)
            vars

        Definition (
          DefineFun (
            symbol,
            vars,
            BoolSort,
            List.fold
              (fun acc (n, _) ->
                substitute
                  n
                  (fun var ->
                    smtExpr.Ite (
                      smtExpr.Apply (
                        ElementaryOperation ("=", [ IntSort; BoolSort ], BoolSort),
                        [ var; BoolConst true ]
                      ),
                      smtExpr.Number BigInteger.One,
                      smtExpr.Number BigInteger.Zero
                    ))

                  acc)
              expr
              boolVars
          )
        )
      | otherwise -> otherwise)

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


let decConsts = List.map decConst






// r
//   T nia
//

//  (ban)
//   T nia
//





module NIA =
  let rec nia tl constDefs constrDefs pushed' (cmdOps: Lazy<_>) =
    state {
      do! cmdOps.Force ()

      match! Debug.Duration.go (lazy Solver.solveLearner tl constDefs) "Z3.NIA" with
      | Timeout, inputs ->
        do! Debug.Print.smtInputs inputs
        do! Solver.rmRememberedConstraint

        // printfn "nia"
        match! Debug.Duration.go (lazy Solver.solveLearner tl constDefs) "Z3.NIA" with
        | timeout.Ok (Result.Ok defConsts'), inputs ->
          let! cs = Solver.cmds



          do! Debug.Print.smtInputs inputs

          do!
            Debug.Print.smtInput (
              let content = List.map (program2originalCommand >> toString) cs |> join "\n" in

              $"(set-logic NIA)\n{content}"
            )

          return Result.Ok (defConsts', constrDefs, pushed')
        | _ -> return! nia tl constDefs constrDefs pushed' (lazy State (fun st -> (), st))
      | timeout.Ok (Result.Ok defConsts'), inputs ->
        let! cs = Solver.cmds

        do! Debug.Print.smtInputs inputs

        do!
          Debug.Print.smtInput (
            let content = List.map (program2originalCommand >> toString) cs |> join "\n" in

            $"(set-logic NIA)\n{content}"
          )

        // for x in defConsts' do printfn $"{x}"

        return Result.Ok (defConsts', constrDefs, pushed')
      | timeout.Ok (Error "UNKNOWN~"), inputs ->
        // printfn "UNKNOWN~"
        do! Solver.rmRememberedConstraint
        return! nia tl constDefs constrDefs pushed' (lazy state { do! state.Return () })

      // do! Debug.Print.smtInputs inputs
      // printfn $"{e}"
      // return Error e
      | timeout.Ok (Error e), inputs ->
        do! Debug.Print.smtInputs inputs
        // printfn $"{e}"
        return Error (e, "")
    }

  and tlAfterRedlog tl constDefs constrDefs pushed' =
    (lazy
      state {
        do! Solver.setCommandsKEK [ banValues constDefs ]
      // do! state.Return ()
      })
    |> nia tl constDefs constrDefs pushed'

  let tlAfterRedlogTl tl constDefs constrDefs pushed' =
    (lazy state { do! Solver.setCommandsKEK [ banValues constDefs ] })
    |> nia tl constDefs constrDefs pushed'

let niaFst tLearner tRedlog funDefs constDefs constrDefs clause pushed withRedlog =
  state {
    do! Solver.setCommandsKEK [ Assert clause ]
    do! Solver.rememberConstraint <| Assert clause

    match! Solver.solveLearner tLearner constDefs with
    | Timeout, _
    | timeout.Ok (Result.Error "UNKNOWN~"), _ ->
      do! Solver.rmRememberedConstraint
      let! fTimes = Solver.fTimes

      match!
        Debug.Duration.go
          (lazy
            state.Return (
              if withRedlog then
                redlog tRedlog (funDefs @ def2decVars constrDefs) clause fTimes
              else
                timeout.Timeout
            ))
          "REDLOG"
      with
      // match! Debug.Duration.go (lazy state.Return (redlog 0.1 (funDefs @ def2decVars constrDefs) clause)) "REDLOG" with
      | Timeout -> return! NIA.tlAfterRedlogTl tLearner constDefs constrDefs pushed

      | timeout.Ok redlogResult ->
        do! Debug.Print.redlogOutput <| toString (program2originalCommand redlogResult)
        do! Solver.setCommandsKEK [ redlogResult ]
        do! Solver.rememberConstraint redlogResult

        return! NIA.tlAfterRedlog tLearner constDefs constrDefs (pushed |> List.addLast redlogResult)

    | timeout.Ok (Result.Ok consts), _ ->
      do! Solver.setCommandsKEK [ banValues constDefs ]

      return Result.Ok (consts, constrDefs, pushed)
  }

let redlogFst tLearner tRedlog funDefs constDefs constrDefs clause pushed withRedlog =
  state {
    // do! Solver.setCommandsKEK [ Assert clause ]
    // do! Solver.rememberConstraint <| Assert clause
    let! fTimes = Solver.fTimes

    match!
      Debug.Duration.go
        (lazy
          state.Return (
            if withRedlog then
              redlog tRedlog (funDefs @ def2decVars constrDefs) clause fTimes
            else
              timeout.Timeout
          ))
        "REDLOG"
    with
    // match! Debug.Duration.go (lazy state.Return (redlog 0.1 (funDefs @ def2decVars constrDefs) clause)) "REDLOG" with
    | Timeout ->
      do! Solver.setCommandsKEK [ Assert clause ]
      do! Solver.rememberConstraint <| Assert clause
      return! NIA.tlAfterRedlogTl tLearner constDefs constrDefs pushed

    | timeout.Ok redlogResult ->
      do! Debug.Print.redlogOutput <| toString (program2originalCommand redlogResult)
      do! Solver.setCommandsKEK [ redlogResult ]
      do! Solver.rememberConstraint redlogResult

      return! NIA.tlAfterRedlog tLearner constDefs constrDefs (pushed |> List.addLast redlogResult)


  // match! Solver.solveLearner constDefs with
  // | Timeout, _ | timeout.Ok (Result.Error "UNKNOWN~"), _ ->
  //    do! Solver.rmRememberedConstraint
  //    let! fTimes = Solver.fTimes
  //
  // | timeout.Ok (Result.Ok consts), _ ->
  //   do! Solver.setCommandsKEK [ banValues constDefs ]
  //
  //   return Result.Ok (consts, constrDefs, pushed)
  }


let anotherConsts tLearner tRedlog funDefs constDefs constrDefs clause pushed withRedlog =
  state {
    // do! Debug.Print.redlogInput $"{Redlog.redlogQuery (funDefs @ def2decVars constrDefs) clause}"
    // return! niaFst funDefs constDefs constrDefs clause pushed withRedlog
    return! redlogFst tLearner tRedlog funDefs constDefs constrDefs clause pushed withRedlog


  // do! Solver.setCommandsKEK [ Assert clause ]
  // do! Solver.rememberConstraint <| Assert clause
  // match! Solver.solveLearner constDefs with
  // | Timeout, _ | timeout.Ok (Result.Error "UNKNOWN~"), _ ->
  //    do! Solver.rmRememberedConstraint
  //    let! fTimes = Solver.fTimes
  //    match! Debug.Duration.go (lazy state.Return (if withRedlog then redlog 10 (funDefs @ def2decVars constrDefs) clause fTimes else timeout.Timeout)) "REDLOG" with
  //    // match! Debug.Duration.go (lazy state.Return (redlog 0.1 (funDefs @ def2decVars constrDefs) clause)) "REDLOG" with
  //    | Timeout ->
  //      return! NIA.tlAfterRedlogTl constDefs constrDefs pushed
  //
  //    | timeout.Ok redlogResult ->
  //      do! Debug.Print.redlogOutput <| toString (program2originalCommand redlogResult)
  //      do! Solver.setCommandsKEK [ redlogResult ]
  //      do! Solver.rememberConstraint redlogResult
  //
  //      return! NIA.tlAfterRedlog constDefs constrDefs (pushed |> List.addLast redlogResult)
  //
  // | timeout.Ok (Result.Ok consts), _ ->
  //   do! Solver.setCommandsKEK [ banValues constDefs ]
  //
  //   return Result.Ok (consts, constrDefs, pushed)
  //
  }


let proofModelQuery dbgPath iteration sortVars (adtDecs, recs) funDefs adtConstrs resolvent fTimes =
  let q = Resolvent.smtEQuery sortVars adtConstrs funDefs adtDecs resolvent


  let notInterpreted =
    List.choose (function
      | Decl (n, _)
      | DeclIntConst n
      | DeclConst (n, _) -> Some n
      | _ -> None)



  solve
    Int32.MaxValue
    []
    (List.map (program2originalCommand >> toString) (adtDecls (adtDecs, recs)))
    instance.ADTModel
    (Resolvent.smtEQuery sortVars adtConstrs funDefs adtDecs resolvent)
    (notInterpreted q)
    []
    dbgPath
    iteration
    fTimes
  |> function
    | Some (result.SAT (Some m), _), _ -> m
    | a ->
      failwith "ERR:\nAAAAAAAAAAAAA "
      // printfn "ERR:\nAAAAAAAAAAAAA {a}"
      // Environment.Exit 0
      // printfn $"AAAAAAAAAAAAA {a}"
      []

module Proof =
  let getId =
    List.choose (function
      | App (n, _)
      | Apply (n, _) when n.Contains "$name" -> Some n
      | _ -> None)
    >> List.head

  let numberOf e =
    match Implies.bodyArgs e with
    | Some args -> Some (getId args)
    | None -> None

  let numerateAsserts =
    Map
    << List.choose (function
      | Program.Assert (ForAllTyped (_, e) as expr)
      | Program.Assert (e as expr) ->
        match numberOf e with
        | Some id -> Some (id, expr)
        | None -> None
      | _ -> None)

  let rename e n i = $"x{i}", substituteVar (Var n) (Var $"x{i}") e

  let uniqVars =
    let rec helper' i' ts =
      List.fold
        (fun (i, acc) v ->
          let i', x = helper i v
          (i', x :: acc))
        (i', [])
        ts

    and helper i =
      function
      | Node (expr, ts) ->
        match expr with
        | ForAllTyped (vars, e) ->
          let e', vars', i' =
            List.fold
              (fun (e, vars, i) (n, t) ->
                let n, e' = rename e n i
                (e', List.addLast (n, t) vars, i + 1))
              (e, [], i)
              vars
          let i, ts = helper' i' ts

          i, Node ((ForAllTyped (vars', e')), ts)
        | _ ->
          let i, ts = helper' i ts
          i, Node (expr, ts)
    // Node ((expr), List.map (helper i) ts)

    helper 0 >> snd

  let rmQueryChain = function
    | Node (Bool false, [ Node (Apply ("query!0", []), tl) ]) -> Node (Bool false, tl)
    | otherwise -> otherwise
  
  let headsTree =
    let rec helper =
      function
      | HyperProof (_, proofs, e) -> Node (smtExpr2expr e, List.map helper proofs)

    helper >> rmQueryChain
    
  let cutTree =
    let rec helper =
      function
      | Node (x, ts) ->
        Node (
          x,
          List.map helper
          <| List.filter
            (function
            | Node (Some _, _) -> true
            | _ -> false)
            ts
        )

    helper >> Tree.fmap Option.get

  let clauseNamesTree =
    let rec helper =
      function
      | Node (_, ts) ->
        let v =
          List.choose
            (function
            | App (n, _)
            | Apply (n, _) when n.Contains "$name" -> Some n
            | _ -> None)
            (layer ts)
          |> List.tryHead

        Node (v, List.map helper ts)
    
    let rec rmSpacerPs: Name option tree -> Name option tree = function
      | Node (None, [ Node _ as tree ]) -> rmSpacerPs tree
      | Node (Some _, _) as tree -> tree
      
    helper  >> cutTree

  let exprTree cmds proof =
    let clauseNamesTree = headsTree >> clauseNamesTree
    let exprs = numerateAsserts cmds

    let rec helper =
      function
      | Node (v, ts) -> Node (Map.find v exprs, List.map helper ts)

    clauseNamesTree proof |> helper

  let UniqVarsExprTree cmds proof = exprTree cmds proof |> uniqVars

  let ops = [ "="; "distinct"; ">"; "<"; ">="; "<="; "not" ]
  
  let forallBody =
    function
    | ForAllTyped (_, b) -> b
    | otherwise -> otherwise

  let isDefinedPredicate =
    function
    | Apply (n, _)
    | App (n, _) when List.contains n ops -> true
    | Lt _
    | Gt _
    | Le _
    | Ge _
    | Not _
    | Eq _ -> true
    | _ -> false

  let definedPredicates = List.filter isDefinedPredicate

  let predicates =
    List.choose (function
      | App (n, args)
      | Apply (n, args) as x when (not << isDefinedPredicate) x -> Some (n, args)
      | _ -> None)

  let bind layer (n, args) =
    let args' =
      List.choose (function
        | App (n', args')
        | Apply (n', args') when n' = n -> Some args'
        | _ -> None)
      <| List.map (Option.get << Implies.head) layer

    match args' with
    | [ args' ] -> List.map2 (fun arg arg' -> Eq (arg, arg')) args args'
    | [] -> []
    | _ -> failwith "-????-"

  let eqs node layer =
    let xs = Option.get <| Implies.bodyArgs node
    List.append (definedPredicates xs) (List.concat <| List.map (bind layer) (predicates xs))

  let resolventBody cmds proof =
    let rec helper =
      function
      | Node (v, ts) -> (eqs (forallBody v) <| List.map forallBody (layer ts)) @ List.collect helper ts
    UniqVarsExprTree cmds proof
    |> fun x ->
      x
      |> helper

  let resolventVars cmds proof =
    let rec helper acc =
      function
      | Node (ForAllTyped (vars, _), tl) -> acc @ vars @ List.collect (helper []) tl
      | Node (_, tl) -> List.collect (helper acc) tl

    UniqVarsExprTree cmds proof
    |> fun x ->
      // printfn $"VVVVARS VVVVARS VVVVARS VVVVARS \n{x}"
      x |> helper []
  
  module Simplify =
    let isEqWithVar = function
        | Eq (Var _, Var _)
        | Eq (Var _, Apply _)
        | Eq (Apply _, Var _)
        | Eq (Var _, Int _)
        | Eq (Int _, Var _)
        | Eq (Var _, Bool _)
        | Eq (Bool _, Var _)
        | Eq (Var _, Not _)
        | Eq (Not _, Var _)
        | Eq (Var _, Eq _)
        | Eq (Eq _, Var _)
        | Eq (Var _, Lt _)
        | Eq (Lt _, Var _)
        | Eq (Var _, Gt _)
        | Eq (Gt _, Var _)
        | Eq (Var _, Le _)
        | Eq (Le _, Var _)
        | Eq (Var _, Ge _)
        | Eq (Ge _, Var _)
        | Eq (Var _, Mod _)
        | Eq (Mod _, Var _)
        | Eq (Var _, Add _)
        | Eq (Add _, Var _)
        | Eq (Var _, Subtract _)
        | Eq (Subtract _, Var _)
        | Eq (Var _, Neg _)
        | Eq (Neg _, Var _)
        | Eq (Var _, Mul _)
        | Eq (Mul _, Var _)
        | Eq (Var _, And _)
        | Eq (And _, Var _)
        | Eq (Var _, Or _)
        | Eq (Or _, Var _)
        | Eq (Var _, Not _)
        | Eq (Not _, Var _)
        | Eq (Var _, Implies _)
        | Eq (Implies _, Var _)
        | Eq (Var _, Ite _)
        | Eq (Ite _, Var _) -> true
        | _ -> false  

    let resolventBody = function
      | And xs -> xs
      | _ -> [||]
         
    let couldBeSimpler =
      resolventBody
      >> Array.filter isEqWithVar
      >> Array.isEmpty
      >> not
    
    let rec transitiveSubst resolvent =
      match Array.tryFind isEqWithVar <| resolventBody resolvent with
      | Some (Eq (Var n, x))
      | Some (Eq (x, Var n)) when Var n <> x ->
        transitiveSubst <| substituteVar (Var n) x resolvent
      | _ -> resolvent
    
    let isTautology = function
      | Eq (x, y) when x = y -> true 
      | _ -> false
    
    let simplify =
      transitiveSubst
      >> resolventBody
      >> Array.filter (not << isTautology)
      >> And
  
  module BuildContract =
    
    let head = function
      | ForAllTyped (_, e) 
      | e -> Option.defaultWith (fun () -> e) (Implies.head e)
    
    let (===) x y =
      match (x, y) with
      | Apply (n, _),  Apply (n', _) 
      | App (n, _), Apply (n', _)
      | Apply (n', _), App (n, _) 
      | App (n', _), App (n, _)  when n = n' -> true
      | _ -> x = y
    
    let asserted cmds expr =
      let map = numerateAsserts cmds
      let asserted =
        // printfn $"EE {expr}"
        let e =
          match expr with
          | ForAllTyped (_, e)
          | e -> e
      
        match numberOf e with
        | Some n -> Map.find n map
        | _ ->
          List.choose (function
            | Assert (ForAllTyped (_, Implies (_, Bool false)) as e) 
            | Assert (Implies (_, Bool false) as e) -> Some e
            | _ -> None)
            cmds
          |> List.head 
      Asserted <| expr2smtExpr asserted
      // match List.find (function Assert e' when head e' === head e -> true | _ -> false) cmds with
      // | Assert e -> Asserted <| expr2smtExpr e
      // | _ -> __unreachable__ ()
    
    let build cmds =
      let rec helper = function
        | Node (e, ts) ->
          HyperProof
            (asserted cmds e,
             List.map helper ts,
             expr2smtExpr <| head e)
      helper

let learner
  (tLearner, tChecker, tRedlog)
  (origCMDsNonBoolApproximated: originalCommand list)
  origDecs
  origAsserts
  (adtDecs, recs)
  (adtConstrs: Map<ident, symbol * Type list>)
  funDefs
  domainADT
  (asserts: Program list)
  constDefs
  constrDefs
  funDecls
  proof
  pushed
  withRedlog
  =
  state {
    let! fTimes = Solver.fTimes
    let! iter = Debug.Print.iteration
    
    match proof with
    | [ Command (Proof (hyperProof, _, _)) ] ->
      let constRestriction =
        let asserts = List.map (program2originalCommand >> origCommand2program) asserts
        let resolvent =
          Proof.Simplify.simplify
          // id
          <| And (Array.ofSeq <| Proof.resolventBody asserts hyperProof)
        let vars = Proof.resolventVars asserts hyperProof
        
        ForAllTyped (vars, Implies (resolvent, Bool false))
      
      let origAsserts =
        List.choose
          (function
          | originalCommand.Assert _ as a -> Some (origCommand2program a)
          | _ -> None)
          origCMDsNonBoolApproximated

      let! ((feasible, smtADTLIAcContent), _), typedVars, resolvent =
        let resolvent = Proof.resolventBody origAsserts hyperProof
        let vars = Proof.resolventVars origAsserts hyperProof
        
        Debug.Duration.go
          (lazy
            state.Return (
              feasible tChecker (adtDecs, recs) funDefs vars (And (Array.ofSeq resolvent)) fTimes,
              vars,
              resolvent
            ))
          "Z3.ADT(LIA)"
      
      do!
        Debug.Print.smtADTLIA (
          let content =
            List.map (program2originalCommand >> toString) smtADTLIAcContent |> join "\n" in

          $"(set-option :produce-proofs true)\n{content}\n(check-sat)"
        )
      
      match feasible with
      | Result.Ok ok ->
      
        let defines =
          proofModelQuery
            dbgPath
            iter
            (List.map (fun (n, t: Type) -> (n, t.toSort)) typedVars)
            (adtDecs, recs)
            funDefs
            adtConstrs
            (And (Array.ofSeq resolvent))
            fTimes
          |> List.map (program2originalCommand >> toString)
          |> join "\n"
        
                
        // printfn $"hyperProofhyperProofhyperProofhyperProofhyperProof\n{Proof.UniqVarsExprTree origAsserts hyperProof}"
        // printfn $"hyperProofhyperProofhyperProofhyperProofhyperProof\n{hyperProof}"
      
        // printfn $"defines ? / {defines}"
        // printfn $"{Proof.BuildContract.build origAsserts <| Proof.UniqVarsExprTree origAsserts hyperProof}"
        let proof = Proof.BuildContract.build origAsserts <| Proof.UniqVarsExprTree origAsserts hyperProof
        return Error ("unsat", $"{defines}\n{proof}\n")

      | Error _ ->
        return! anotherConsts tLearner tRedlog funDefs constDefs constrDefs constRestriction pushed withRedlog














    // let sortVars, resolvent, proof =
    //   resolvent origCMDsNonBoolApproximated origDecs origAsserts constDefs funDecls hyperProof asserts iter
    //
    //
    // let simpResolvent = Simplifier.simplify resolvent |> Simplifier.simplify
    //
    // let! (feasible, smtADTLIAcContent), _ =
    //   Debug.Duration.go
    //     (lazy
    //       state.Return (
    //         feasible tChecker (Set.toList sortVars) (adtDecs, recs) adtConstrs funDefs simpResolvent fTimes
    //       ))
    //     "Z3.ADT(LIA)"
    //
    // do!
    //   Debug.Print.smtADTLIA (
    //     let content =
    //       List.map (program2originalCommand >> toString) smtADTLIAcContent |> join "\n" in
    //
    //     $"(set-option :produce-proofs true)\n{content}\n(check-sat)"
    //   )
    //
    // match feasible with
    // | Result.Ok ok ->
    //   let defines =
    //     proofModelQuery dbgPath iter (Set.toList sortVars) (adtDecs, recs) funDefs adtConstrs resolvent fTimes
    //     |> List.map (program2originalCommand >> toString)
    //     |> join "\n"
    //
    //   return Error ("unsat", $"{defines}\n{proof}\n")
    // //return Error $"UNSAT"
    // | Error _ ->
    //   return!
    //     anotherConsts
    //       tLearner
    //       tRedlog
    //       funDefs
    //       constDefs
    //       constrDefs
    //       (Implies (Bool false, Bool false) |> id)
    //       // (Implies (simpResolvent, Bool false) |> id)
    //       // (Implies (simpResolvent, Bool false) |> forAllInt)
    //       pushed
    //       withRedlog

    | _ ->
      failwith $"ERR-PROOF_FORMAT"
      // Environment.Exit 0
      return Error ("", $"PROOF_FORMAT")
  }


module Model =
  let alg =
    List.choose (function
      | Def (n, x, y, z) -> Some (Def ($"alg_{n}", x, y, z))
      | _ -> None)

  let fCata n x : smtExpr =
    smtExpr.Apply (ElementaryOperation ($"cata_{n}", [], IntSort), [ Ident (x, IntSort) ])

  let constr n args =
    smtExpr.Apply (n, List.map (fun arg -> Ident (Operation.opName arg, IntSort)) args)

  let appAlg n args =
    smtExpr.Apply (
      ElementaryOperation ($"alg_{n}", [], IntSort),
      List.map
        (fun arg ->
          match Operation.toTuple arg with
          | n, _, ADTSort adt -> fCata adt n
          | n, _, _ -> Ident (n, IntSort))
        args
    )

  let catas domain ts =
    List.map program2originalCommand ts
    |> List.choose (function
      | Command (command.DeclareDatatypes [ n, xs ]) ->
        originalCommand.Definition (
          DefineFunRec (
            $"cata_{n}",
            [ "x", ADTSort n ],
            domain,
            Match (
              Ident ("x", ADTSort n),
              List.map
                (function
                | n', _, args -> (constr n' args, appAlg n' args))
                xs
            )
          )
        )
        |> Some
      | _ -> None)

  let rec subst op name =
    function
    | Ident (n, _) as x when n = name -> smtExpr.Apply (op, [ x ])
    | smtExpr.Apply (x, exprs) -> smtExpr.Apply (x, List.map (subst op name) exprs)
    | Let (xs, expr) -> Let (List.map (fun (var, e) -> (var, subst op name e)) xs, subst op name expr)
    | Match (expr, exprs) ->
      Match (subst op name expr, List.map (fun (e1, e2) -> (subst op name e1, subst op name e2)) exprs)
    | smtExpr.Ite (expr1, expr2, expr3) -> smtExpr.Ite (subst op name expr1, subst op name expr2, subst op name expr3)
    | smtExpr.And exprs -> smtExpr.And <| List.map (subst op name) exprs
    | smtExpr.Or exprs -> smtExpr.Or <| List.map (subst op name) exprs
    | smtExpr.Not expr -> smtExpr.Not <| subst op name expr
    | Hence (expr1, expr2) -> Hence (subst op name expr1, subst op name expr2)
    | QuantifierApplication (qs, expr) -> QuantifierApplication (qs, subst op name expr)
    | Tester (op', e) -> Tester (op', subst op name e)
    | otherwise -> otherwise


  let lia2adt origDecs ps (m: _ list) =
    // for p in ps do printfn $"p: {p}"

    let m =
      let pVars =
        List.choose (function
          | originalCommand.Command (command.DeclareFun (n, _, sorts, _)) ->
            Some (n, List.mapi (fun i sort -> $"x!{i}", sort2type sort) sorts)
          | _ -> None)

      let mNames =
        List.choose (function
          | Def (n, _, _, _) -> Some n
          | _ -> None)

      let delta = List.filter (fun (p, _) -> not <| List.contains p (mNames m)) (pVars ps)

      m @ List.map (fun (p, args) -> Def (p, args, Boolean, Bool true)) delta


    let ps =
      if m.Length > ps.Length then
        Command (DeclareFun ("q", [], BoolSort)) :: ps
      else
        ps

    List.choose
      (function
      | Def (n, args, _, e) -> Some (n, args, expr2smtExpr e)
      | _ -> None)
      m
    |> List.sortBy (fun (x, _, _) -> x)
    |> List.zip
    <| (List.choose
          (function
          | Command (DeclareFun (n, sorts, _)) -> Some (n, sorts)
          | _ -> None)
          ps
        |> List.sortBy fst)
    |> List.map (fun ((n, vars, e), (_, sorts)) ->
      let args = List.zip (List.map fst vars) sorts

      Definition (
        DefineFun (
          n,
          args,
          BoolSort,
          List.choose
            (function
            | n, ADTSort adt -> Some (n, ElementaryOperation ($"cata_{adt}", [], BoolSort))
            | _ -> None)
            args
          |> List.fold (fun e (n, f) -> subst f n e) e
        )
      ))



  let model (domainADT: Program list) origCMDsNonBoolApproximated adtLiaDecs (ts, recs) ps constDefs constrDefs m =
    let domainADT2Sort x =
      opt {
        match! x with
        | DeclDataType [ n, _ ] -> return (sort.ADTSort n)
        | _ -> return! None
      }

    let domainSort =
      List.tryHead domainADT
      |> domainADT2Sort
      |> Option.defaultWith (fun () -> IntSort)

    $"""{join "\n" <| List.map (program2originalCommand >> toString) domainADT}
{join "\n" <| List.map (program2originalCommand >> toString) constDefs}
{join "\n" <| List.map (program2originalCommand >> toString) (alg constrDefs)}
{join "\n" <| List.map toString (catas domainSort ts)}
{join "\n"
 <| List.map toString (ContractOut.modelBoolArgs origCMDsNonBoolApproximated (lia2adt adtLiaDecs ps m))}"""


let rec teacher
  (tLearner, tTeacher, tChecker, tRedlog)
  (origCMDsNonBoolApproximated: originalCommand list)
  origDecs
  origAsserts
  origPs
  (adtDecs, recs)
  (adtConstrs: Map<ident, symbol * Type list>)
  funDefs
  domainADT
  constDefs
  constrDefs
  funDecls
  (asserts: Program list)
  pushed
  withRedlog
  =
  let cmds = funDefs @ domainADT @ constDefs @ constrDefs @ funDecls @ asserts

  let teacherRes domain i fTimes =
    state {
      return
        solve
          tTeacher
          domain
          []
          instance.Teacher
          (funDefs @ domainADT @ constDefs @ constrDefs @ funDecls @ asserts)
          (defNames constDefs)
          []
          dbgPath
          i
          fTimes

    }

  // printfn "TEACHER"
  // for x in constDefs do printfn $" >> {x}"
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

    let! ittt = Debug.Print.iteration
    let! fTimes = Solver.fTimes

    match! Debug.Duration.go (lazy teacherRes (List.map program2originalCommand domainADT) ittt fTimes) "HORN.LIA" with
    | Some (result.SAT _, _), _ ->
      // printfn $"SAT"
      match
        solve
          Int32.MaxValue
          (List.map program2originalCommand domainADT)
          []
          instance.TeacherModel
          (funDefs @ domainADT @ constDefs @ constrDefs @ funDecls @ asserts)
          (List.choose
            (function
            | Decl (n, _) -> Some n
            | _ -> None)
            funDecls)
          []
          dbgPath
          1123
          fTimes
      with
      | Some (result.SAT (Some model), _), _ ->
        // let! i = Debug.Print.iteration
        // return $"SAT"

        return
          ("sat",
           $"{Model.model domainADT origCMDsNonBoolApproximated origDecs (adtDecs, recs) origPs constDefs constrDefs model}")
      | o ->
        // failwith $"solve-Int32.MaxValue\n{o}"
        // return "", ""
        match! NIA.tlAfterRedlog tLearner constDefs constrDefs pushed with
        | Result.Ok (defConsts, constrDefs, pushed) ->
          return!
            teacher
              (tLearner, tTeacher, tChecker, tRedlog)
              origCMDsNonBoolApproximated
              origDecs
              origAsserts
              origPs
              (adtDecs, recs)
              adtConstrs
              funDefs
              domainADT
              defConsts
              constrDefs
              funDecls
              asserts
              pushed
              withRedlog
        //
        //
        
    // | o, [] ->
    // printfn ">>"
    // printfn $"{o}"
    // printfn "<<<"
    // failwith $"!\n{o}"
    // return ("?SAT", "")
                  
    // return "SAT"
    | Some (result.UNSAT (Some (proof, dbgProof)), _), _ ->
      // let proof, dbgProof =
      //   z3Process.z3proof
      //     (toOrigCmds funDefs)
      //     (toOrigCmds constDefs)
      //     (toOrigCmds constrDefs)
      //     (toOrigCmds funDecls)
      //     (toOrigCmds asserts)

      // printfn $"{proof} \n**********\n {dbgProof}\n\n"

      do! Debug.Print.proof dbgProof
      do! Debug.Print.next
      // printfn $"<<< {dbgProof}"
      // for x in constDefs do printfn $"<<<<<<<<<<< {x}"

      match!
        learner
          (tLearner, tChecker, tRedlog)
          origCMDsNonBoolApproximated
          origDecs
          origAsserts
          (adtDecs, recs)
          adtConstrs
          funDefs
          domainADT
          asserts
          constDefs
          constrDefs
          funDecls
          proof
          pushed
          withRedlog
      with
      | Result.Ok (defConsts', defConstrs', pushed') ->
        return!
          teacher
            (tLearner, tTeacher, tChecker, tRedlog)
            origCMDsNonBoolApproximated
            origDecs
            origAsserts
            origPs
            (adtDecs, recs)
            adtConstrs
            funDefs
            domainADT
            defConsts'
            defConstrs'
            funDecls
            asserts
            pushed'
            withRedlog
      | Error err ->
        let! i = Debug.Print.iteration
        return err
    // return e + $", {i - 1}"
    | _ ->
      // for x in constDefs do printfn $"{x}"
      // do! Solver.setCommandsKEK [ banValues constDefs ]
      // let defConsts', constrDefs, pushed' =
      match! NIA.tlAfterRedlog tLearner constDefs constrDefs pushed with
      | Result.Ok (defConsts, constrDefs, pushed) ->
        return!
          teacher
            (tLearner, tTeacher, tChecker, tRedlog)
            origCMDsNonBoolApproximated
            origDecs
            origAsserts
            origPs
            (adtDecs, recs)
            adtConstrs
            funDefs
            domainADT
            defConsts
            constrDefs
            funDecls
            asserts
            pushed
            withRedlog
      // | o ->
      //   failwith $"NIA.tlAfterRedlog\n{o}"
      //   return "failwith A", ""
  }


let newLearner () =
  let envLearner = emptyEnv
  let solverLearner = 123
  envLearner, solverLearner

module AssertsMinimization =
  let bodyAppNames =
    let rec helper acc =
      function
      | Implies (expr1, _) -> helper acc expr1
      | App (name, _) -> name :: acc
      | ForAllTyped (_, expr)
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

module PredicateMinimiztion =
  let contains' p =
    let rec helper acc =
      function
      | Eq (e1, e2)
      | Lt (e1, e2)
      | Gt (e1, e2)
      | Le (e1, e2)
      | Ge (e1, e2)
      | Mod (e1, e2)
      | Add (e1, e2)
      | Mul (e1, e2)
      | Implies (e1, e2)
      | Subtract (e1, e2) -> acc || helper acc e1 || helper acc e2
      | ForAllTyped (_, e1)
      | ForAllTyped (_, e1)
      | Not e1
      | Neg e1 -> acc || helper acc e1
      | And exprs
      | Or exprs -> Array.fold (fun a e -> a || helper a e) acc exprs
      | App (n, _) when n = p -> true
      | Ite (e1, e2, e3) -> acc || helper acc e1 || helper acc e2 || helper acc e3
      | _ -> acc

    helper false

  let contains p cmds =
    List.fold (fun acc cmd -> acc || contains' p cmd) false cmds

  let minimize ps cmds =
    List.choose
      (function
      | Decl (n, _) as d when contains n cmds -> Some d
      | _ -> None)
      ps


module HenceNormalization =
  let mkSingleQuery file =
    let p = Parser false
    let cmds = p.ParseFile file
    let asserts =
      List.filter (function originalCommand.Assert _ -> true | _ -> false) cmds
      |> List.map origCommand2program
    let funDecs =
      List.filter (function originalCommand.Command (command.DeclareFun _) -> true | _ -> false) cmds
      |> List.map origCommand2program
    match queryAssert id asserts with
    | [ _ ] | [] -> join "\n" <| List.map toString cmds
    | xs ->
      // for x in xs do printfn $"SSSSSSSSSSSSS{x}"
      let asserts' = asserts |> List.filter (fun x -> xs |> List.contains x |> not)
      let qDec = Decl ("q", [])
      let qApp = App ("q", [])

      let quryImpls =
        xs
        |> List.choose (function
          | Assert (ForAllTyped (vars, Implies (body, Bool false))) -> Some (Assert (ForAllTyped (vars, Implies (body, qApp))))  
          | Assert (Implies (body, Bool false)) -> Some (Assert (Implies (body, qApp)))  
          | _ -> None)
      
      let adts =
        List.filter
          (function
            | Command (DeclareDatatype _)
            | Command (DeclareDatatypes _) ->
              true
            | _ ->
              false)
          cmds
        |> List.map toString
    
      let defs =
        List.filter
          (function
            | Definition _ ->
              true 
            | _ ->
              false)
          cmds
        |> List.map toString
      
      let cmds' = defs @ adts @ (List.map (program2originalCommand >> toString) <| (qDec :: funDecs) @ Assert (Implies (qApp, Bool false)) :: asserts' @ quryImpls)
      join "\n" cmds' 
      // qDec :: funDecs, Assert (Implies (qApp, Bool false)) :: asserts' @ quryImpls
  
  let adts =
    List.filter
      (function
        | Command (DeclareDatatype _)
        | Command (DeclareDatatypes _) ->
          true
        | _ ->
          false)
    >> List.map toString
    
  let defs =
    List.filter
      (function
        | Definition _ ->
          true 
        | _ ->
          false)
    >> List.map toString
  
  let funDecs =
    List.filter
      (function | originalCommand.Command (command.DeclareFun _) -> true | _ -> false) 
    >> List.map origCommand2program
    
  let asserts =
    List.filter (function originalCommand.Assert _ -> true | _ -> false) 
    >> List.map origCommand2program
  
  let query =
    List.find (function
      | Assert (Implies (_, Bool false))
      | Assert (ForAllTyped (_, Implies (_, Bool false))) -> true
      | _ -> false )
  
  let apps = List.filter (function Apply _ | App _ -> true | _ -> false)
  
  let reachable cmds = function
    | Apply (n, _) | App (n, _) ->
      List.filter (function
        | Assert (ForAllTyped (_, Apply (n' , _)))
        | Assert (ForAllTyped (_, App (n' , _)))
        | Assert (Apply (n' , _))
        | Assert (App (n' , _))
        | Assert (Implies (_, Apply (n' , _)))
        | Assert (Implies (_, App (n' , _)))
        | Assert (ForAllTyped (_, Implies (_, App (n' , _)))) 
        | Assert (ForAllTyped (_, Implies (_, Apply (n' , _)))) when n = n' -> true
        | _ -> false)
        cmds
    | _ ->
      []
  // a b -> p1  
  // p1 p2 p3 -> F
  
  let prog2str = List.map (program2originalCommand >> toString)
  let origCmd2str = List.map toString
  
  let minimize file =
    let p = Parser false
    let cmds = p.ParseFile file
    
    let rec helper acc = function
      | Assert (Implies (b, _))
      | Assert (ForAllTyped (_, Implies (b, _))) ->
        let b = Implies.bodyArgs' b
        let reachable =
          reachable (asserts cmds)
          >> List.filter (not << flip List.contains acc)
        List.fold
          (fun acc x ->
            let acc' = helper acc x
            acc')
          (acc @ (List.concat <| List.map reachable b))
          (List.concat <| List.map reachable b)
        
      | _ ->
        acc
    (origCmd2str <| adts cmds) @
    (origCmd2str <| defs cmds) @
    (prog2str <| funDecs cmds) @
    prog2str [ query <| asserts cmds ] @
    (prog2str <| helper [] (query <| asserts cmds))   
    |> join "\n"
    
    
  let notFF file =
    let p = Parser false
    let cmds = p.ParseFile file
    
    List.choose
      (function
        | originalCommand.Assert (smtExpr.Not (smtExpr.Apply (op, []))) when Operation.opName op = "ff" ->
          // Some (originalCommand.Assert (smtExpr.Hence (smtExpr.Apply (op, []), BoolConst false)))
          Some (originalCommand.Assert (smtExpr.Hence (smtExpr.And [ smtExpr.Apply (op, []) ], BoolConst false)))
        | otherwise -> Some otherwise)
      cmds
    |> List.map toString
    |> join "\n"
  
//   let restoreVarNames =
//     let nameVars =
//       List.choose (function
//         | Var n -> Some n
//         | _ -> None)
//       >> List.toArray
//
//     function
//     | Assert (ForAllTyped (args, expr)) ->
//       let names' = vars expr |> nameVars |> Set |> Set.union (Set args)
//       let typeOfVar n = n,  Map args |> Map.find n
//
//       Assert (ForAllTyped (List.map typeOfVar <| Set.toList names', expr))
//     | Assert expr as assrt ->
//       match vars expr with
//       | [] -> assrt
//       | vars -> Assert (ForAllTyped (nameVars vars, expr))
//     | otherwise -> otherwise
//
//
//
// module ImpliesWalker =
//   let assertBodies =
//     List.choose (function
//       | Assert b -> Some b
//       | _ -> None)
//
//   let implBody =
//     List.choose (function
//       | Implies (b, _) -> Some b
//       | _ -> None)
//
//   let funcDecls =
//     List.filter (function
//       | Decl _ -> true
//       | _ -> false)
//
//   let asserts =
//     List.filter (function
//       | Assert _ -> true
//       | _ -> false)
//
//   let declNames =
//     List.choose (function
//       | Decl (n, _) -> Some n
//       | _ -> None)
//
//   let axioms = axiomAsserts id
//   let implications = impliesAsserts id
//
//   let withoutAxioms cmds =
//     let appNames = funcDecls cmds |> declNames
//     List.filter (fun x -> axioms (asserts cmds) x |> List.isEmpty) appNames
//
//   let haveApp name =
//     Array.tryFind (function
//       | App (n, _) when n = name -> true
//       | _ -> false)
//     >> function
//       | Some _ -> true
//       | None -> false
//
//   let isRecClause =
//     function
//     | Assert (Implies (And body, App (name, _)))
//     | Assert (ForAllTyped (_, Implies (And body, App (name, _)))) -> haveApp name body
//     | Assert (Implies (body, App (name, _)))
//     | Assert (ForAllTyped (_, Implies (body, App (name, _)))) -> haveApp name [| body |]
//     | _ -> false
//
//   let roots cmds =
//     List.map (implications cmds) (withoutAxioms cmds)
//     |> List.concat
//     |> List.filter (not << isRecClause)
//
//   type kids<'a> = 'a tree list list
//
//   and tree<'a> =
//     | Node of 'a tree * 'a kids
//     | Leaf of 'a
//
//   let tst =
//     Node (
//       Leaf "B A -> P",
//       [ [ Leaf "B"; Leaf "B'"; Leaf "B''" ]
//         [ Node (
//             Leaf "C B -> A",
//             [ [ Node (Leaf "x x -> C", [ [ Leaf "X"; Leaf "X'" ]; [ Leaf "X"; Leaf "X'" ] ]) ]
//               [ Node (Leaf "y -> B", [ [ Leaf "y"; Leaf "y'"; Leaf "y''" ] ]) ]
//               [ Leaf "B" ] ]
//           )
//           Node (Leaf "B B -> A", [ [ Leaf "B"; Leaf "B'" ]; [ Leaf "B"; Leaf "B'" ] ]) ] ]
//     )
//
//   let uniqVars =
//     let rec helper i =
//       function
//       | Leaf e ->
//         let e, i =
//           List.fold (fun (e, i) var -> substituteVar var (Var $"fld-{i}-{expr2smtExpr var}") e, i + 1) (e, i) (vars e)
//
//         Leaf e, i
//       | Node (x, xs) ->
//         let x, i = helper i x
//
//         let xs, i =
//           List.fold
//             (fun (acc: _ tree list list, i) (xs: _ tree list) ->
//               let x, i =
//                 List.fold
//                   (fun (acc, i) x ->
//                     let xs, i = helper i x
//                     (acc @ [ xs ], i + 1))
//                   ([], i)
//                   xs
//
//               (acc @ [ x ], i))
//             ([], i)
//             xs
//
//         Node (x, xs), i
//
//     helper 0 >> fst
//
//   let collect cmds =
//     let queue = roots cmds |> assertBodies
//
//     let rec collect' used = function
//       | ForAllTyped (_, Implies (body, App (name, _))) as value
//       | (Implies (body, App (name, _)) as value) ->
//         let appNames' = Implies.bodyArgs' body |> App.appNames
//         let facts = List.map (axioms cmds) appNames'
//
//         let impls =
//           List.map
//             (implications cmds
//              >> List.filter (function
//                | Assert (ForAllTyped (_, Implies (body, App (n, _))))
//                | Assert (Implies (body, App (n, _))) ->
//                  App.appNames (Implies.bodyArgs' body)
//                  |> List.fold (fun acc b -> acc && not <| List.contains b (n :: name :: used)) true
//                | _ -> false))
//             appNames'
//
//         Node (
//           Leaf value,
//           List.zip facts impls
//           |> List.map (function
//             | [], is -> List.map (collect' (name :: used)) (assertBodies is)
//             | fs, _ -> List.map Leaf (assertBodies fs))
//         )
//
//     List.map (collect' []) queue
//
//   let eqs = List.map Eq
//
//   let andVal =
//     function
//     | [ x ] -> x
//     | xs -> Expr.And xs
//
//   let orVal =
//     function
//     | [ x ] -> x
//     | xs -> Expr.Or xs
//
//   let rec bind x (kids: 'a tree list list) =
//     match x with
//     | Leaf (Implies (b, App _))
//     | Leaf (ForAllTyped (_, Implies (b, App _))) ->
//       let restrictions = notAppRestrictions b
//       let appRestrictions = appRestrictions b
//
//       List.zip appRestrictions kids
//       |> List.choose (function
//         | App (_, args), xs
//         | ForAllTyped (_, App (_, args)), xs ->
//           List.choose
//             (function
//             | Leaf (App (_, args'))
//             | Leaf (ForAllTyped (_, App (_, args'))) -> Some (List.zip args args' |> eqs)
//             | Leaf (Implies (restriction, App (_, args')))
//             | Leaf (ForAllTyped (_, Implies (restriction, App (_, args')))) ->
//               Some (List.zip args args' |> eqs |> List.append (Implies.bodyArgs' restriction))
//             | Node (Leaf (Implies (_, App (_, args'))), _)
//             | Node (Leaf (ForAllTyped (_, Implies (_, App (_, args')))), _) as x ->
//               Some (List.zip args args' |> eqs |> List.append (formula x))
//             | _ -> None)
//             xs
//           |> List.map (List.append restrictions >> andVal)
//           |> orVal
//           |> Some
//         | _ -> None)
//     | _ -> []
//
//   and formula =
//     let rec helper =
//       function
//       | Node (impl, kids) -> bind impl kids
//       | _ -> []
//
//     helper
//
//   let recoverFacts cmds =
//     let collected = collect cmds
//     let collected' = List.map uniqVars (collect cmds)
//
//     let toRm =
//       List.choose
//         (function
//         | Node (Leaf x, _) -> Some (Assert x)
//         | _ -> None)
//         collected
//
//     let heads =
//       List.choose
//         (function
//         | Node (Leaf (Implies (_, h)), _)
//         | Node (Leaf (ForAllTyped (_, Implies (_, h))), _) -> Some h
//         | _ -> None)
//         collected'
//
//     List.map (formula >> Expr.And) collected'
//     |> flip List.zip heads
//     |> List.map (fun (b, h) ->
//       Implies (andVal (notAppRestrictions b @ Implies.bodyArgs' b), h)
//       // |> forAllInt
//       |> Assert)
//     |> fun xs -> xs @ (List.filter (not << flip List.contains toRm) cmds)
// // xs



let rec solver
  (tLearner, tTeacher, tChecker, tRedlog)
  (origCMDsNonBoolApproximated: originalCommand list)
  origDecs
  origAsserts
  declFuns
  (adtDecs, recs)
  (adtConstrs: Map<ident, symbol * Type list>)
  funDefs
  domainADT
  constDefs
  constrDefs
  funDecls
  (asserts: Program list)
  learnerInstance
  withRedlog
  (fTimes: string option)
  =
  // for x in asserts do printfn $"<<< {x}"

  // let funDecls, asserts =
  //   let funDecls', asserts' =
  //     HenceNormalization.mkSingleQuery funDecls asserts
  //     |> fun (decs, asserts) -> decs, List.map HenceNormalization.restoreVarNames asserts
  //
  //   let asserts'' =
  //     AssertsMinimization.assertsMinimize asserts' (queryAssert List.head asserts')
  //
  //   // for x in asserts'' do printfn $"<<< {x}"
  //
  //   PredicateMinimiztion.minimize funDecls' (Assert.bodies asserts''), asserts''

  // let funDecls, asserts = HenceNormalization.mkSingleQuery funDecls asserts
  
  
  let envLearner, solverLearner = newLearner ()
  let decConsts = decConsts constDefs
  // let startCmds = funDefs @ decConsts @ constrDefs @ (notZeroFunConsts constrDefs)

  // ?????? let startCmds = funDefs @ domainADT @ decConsts @ constrDefs
  let startCmds = funDefs @ domainADT @ decConsts @ constrDefs



  state {
    // do kek startCmds
    // do! Solver.setCommands startCmds
    do! Solver.setCommandsKEK startCmds
    // let! setSofts = Solver.setSoftConsts constDefs

    let! setSofts = Solver.setSoftConstsKEK constDefs
    // do kek setSofts
    do! Debug.Print.redlogInput ""
    do! Debug.Print.redlogOutput ""

    do!
      Debug.Print.smtInput (
        let content =
          List.map (program2originalCommand >> toString) (startCmds @ setSofts)
          |> join "\n" in

        $"(set-logic NIA)\n{content}"
      )

    match! Debug.Duration.go (lazy Solver.solveLearner tLearner constDefs) "(INIT)SMT.NIA" with
    | timeout.Timeout, inputs ->
      do! Debug.Print.smtInputs inputs

      let x =
        randomValues (
          List.choose
            (function
            | Def (n, _, _, _) -> Some n
            | _ -> None)
            constDefs
        )
        // |> List.map (fun (n, v) -> Def (n, [], Integer, Int v))
        |> List.map (fun (n, v) -> Def (n, [], Integer, Int BigInteger.Zero))

      return!
        teacher
          (tLearner, tTeacher, tChecker, tRedlog)
          (origCMDsNonBoolApproximated)
          origDecs
          origAsserts
          declFuns
          (adtDecs, recs)
          adtConstrs
          funDefs
          domainADT
          x
          constrDefs
          funDecls
          asserts
          (startCmds @ setSofts)
          withRedlog
    | timeout.Ok (Result.Ok x), inputs ->
      do! Debug.Print.smtInputs inputs

      return!
        teacher
          (tLearner, tTeacher, tChecker, tRedlog)
          origCMDsNonBoolApproximated
          origDecs
          origAsserts
          declFuns
          (adtDecs, recs)
          adtConstrs
          funDefs
          domainADT
          x
          constrDefs
          funDecls
          asserts
          (startCmds @ setSofts)
          withRedlog
    | timeout.Ok (Error err), inputs ->
      printfn $"eeeeeeeeeeeeeeeeeeeeeeee {err}"
      // return!
      //   teacher
      //     (tLearner, tTeacher, tChecker, tRedlog)
      //     origDecs
      //     origAsserts
      //     declFuns
      //     (adtDecs, recs)
      //     adtConstrs
      //     funDefs
      //     (List.choose (function
      //       | Def (n, [], Integer, _) -> Some (Def (n, [], Integer, Int BigInteger.Zero))
      //       | _ -> None) constDefs)
      //     constrDefs
      //     funDecls
      //     asserts
      //     (startCmds @ setSofts)
      //     withRedlog
      do! Debug.Print.smtInputs inputs
      return "UNKNOWN", ""
  }
  |> run (statement.Init envLearner learnerInstance fTimes)

let sort2type =
  function
  | BoolSort -> Boolean
  | ADTSort name -> ADT name
  | _ -> Integer

let sortedVar2typedVar (n, symbol) = n, sort2type symbol


module Preprocessing =
  module Query =
    let queries =
      List.choose (function
        | originalCommand.Assert (Hence (_, BoolConst false))
        | originalCommand.Assert (QuantifierApplication (_, Hence (_, BoolConst false))) as q -> Some q
        | _ -> None)

    let changeQueryHeads =
      function
      | originalCommand.Assert (Hence (b, BoolConst false)) ->
        originalCommand.Assert (Hence (b, smtExpr.Apply (UserDefinedOperation ("q", [], BoolSort), [])))
      | originalCommand.Assert (QuantifierApplication (qs, Hence (b, BoolConst false))) ->
        originalCommand.Assert (
          QuantifierApplication (qs, (Hence (b, smtExpr.Apply (UserDefinedOperation ("q", [], BoolSort), []))))
        )
      | otherwise -> otherwise

    let addQuery cmds =
      let rec declQ =
        function
        | originalCommand.Command (command.DeclareFun _) as d :: tl ->
          originalCommand.Command (DeclareFun ("q", [], BoolSort)) :: d :: tl
        | h :: tl -> h :: declQ tl
        | [] -> [ originalCommand.Command (DeclareFun ("q", [], BoolSort)) ]

      declQ cmds
      |> List.addLast (
        originalCommand.Assert (Hence (smtExpr.Apply (UserDefinedOperation ("q", [], BoolSort), []), BoolConst false))
      )


    let singleQuery cmds =
      match queries cmds with
      | h :: tl as qs ->
        let cmds' = List.filter (not << flip List.contains qs) cmds
        List.map changeQueryHeads cmds |> addQuery
      | [] -> []

  module GhostVals =
    let body =
      function
      | smtExpr.And args -> args
      | otherwise -> [ otherwise ]

    let pop =
      function
      | h :: tl -> h, tl
      | _ -> failwith "A"

    let toBody =
      function
      | [ x ] -> x
      | xs -> smtExpr.And xs

    let transformHence idx b h =
      let newFrees =
        body b
        |> List.filter (function
          | smtExpr.Apply (UserDefinedOperation (n, a, s), args) -> true
          | _ -> false)
        |> List.mapi (fun i _ -> $"ppp_{i}")

      let b' =
        match newFrees with
        | [] -> [ b ]
        | _ ->
          List.mapFold
            (fun (frees: string list) ->
              function
              | smtExpr.Apply (UserDefinedOperation (n, a, s), args) ->
                let free, newFrees' = pop frees
                smtExpr.Apply (UserDefinedOperation (n, a, s), List.addLast (Ident (free, IntSort)) args), newFrees'
              | otherwise -> otherwise, frees)
            newFrees
            (body b)
          |> fst

      let h', idx' =
        match h with
        | smtExpr.Apply (UserDefinedOperation (n, a, s), args) ->
          smtExpr.Apply (UserDefinedOperation (n, a, s), List.addLast (Number idx) args), idx + BigInteger.One
        | otherwies -> otherwies, idx

      b', h', List.map (fun n -> (n, IntSort)) newFrees, idx'

    let transformExpr idx =
      function
      | Hence (b, h) ->
        let b', h', fs, idx' = transformHence idx b h

        match fs with
        | [] -> Hence (toBody b', h'), idx'
        | vars -> QuantifierApplication ([ quantifier.ForallQuantifier vars ], Hence (toBody b', h')), idx'
      | QuantifierApplication ([ quantifier.ForallQuantifier vars ], Hence (b, h)) ->
        let b', h', fs, idx' = transformHence idx b h
        QuantifierApplication ([ quantifier.ForallQuantifier (vars @ fs) ], Hence (toBody b', h')), idx'
      | smtExpr.Apply _ as app ->
        let b', h', fs, idx' = transformHence idx (BoolConst true) app

        match fs with
        | [] -> h', idx'
        | vars -> QuantifierApplication ([ quantifier.ForallQuantifier vars ], h'), idx'
      | QuantifierApplication ([ quantifier.ForallQuantifier vars ], (smtExpr.Apply _ as app)) as x ->
        let b', h', fs, idx' = transformHence idx (BoolConst true) app

        match fs with
        | [] -> QuantifierApplication ([ quantifier.ForallQuantifier vars ], h'), idx'
        | vars -> QuantifierApplication ([ quantifier.ForallQuantifier <| vars @ fs ], h'), idx'

      | otherwise -> otherwise, idx

    let transformAsserts acc =
      function
      | originalCommand.Assert e -> let e', idx' = transformExpr acc e in originalCommand.Assert e', idx'
      | otherwise -> otherwise, acc

    let transformCommand =
      function
      | Command (command.DeclareFun (n, b, sorts, rSort)) ->
        Command (command.DeclareFun (n, b, List.addLast IntSort sorts, rSort))
      | otherwise -> otherwise

    let addGhostVals =
      List.mapFold (fun idx ->
        function
        | Command _ as c -> transformCommand c, idx
        | originalCommand.Assert _ as a ->
          let a', idx' = transformAsserts idx a
          a', idx'
        | otherwise -> otherwise, idx)

  let body =
    function
    | smtExpr.And xs -> xs
    | otherwise -> [ otherwise ]

  module NamedAsserts =
    let addInBody x =
      function
      | smtExpr.Hence (b, h) -> smtExpr.Hence (smtExpr.And (x :: body b), h)
      | smtExpr.QuantifierApplication (qs, smtExpr.Hence (b, h)) ->
        smtExpr.QuantifierApplication (qs, smtExpr.Hence (smtExpr.And (x :: body b), h))
      | smtExpr.Apply _ as app -> smtExpr.Hence (x, app)
      | smtExpr.QuantifierApplication (qs, (smtExpr.Apply _ as app)) ->
        smtExpr.QuantifierApplication (qs, smtExpr.Hence (x, app))
      | otherwise -> failwith $"{otherwise}"

    let addNames =
      List.mapFold
        (fun i ->
          function
          | originalCommand.Assert x ->
            [ originalCommand.Command (DeclareFun ($"$name_{i}", [], BoolSort))
              originalCommand.Assert (smtExpr.Apply (UserDefinedOperation ($"$name_{i}", [], BoolSort), []))
              originalCommand.Assert (
                addInBody (smtExpr.Apply (UserDefinedOperation ($"$name_{i}", [], BoolSort), [])) x
              ) ],
            i + 1
          | otherwise -> [ otherwise ], i)
        0
      >> fst
      >> List.concat

  module UniqBodyPredicates =
    let forCmds f g =
      List.mapi (fun i ->
        function
        | originalCommand.Assert b -> f i b
        | otherwise -> g otherwise)

    let decNames =
      List.choose (function
        | originalCommand.Command (command.DeclareFun (n, _, _, _)) -> Some n
        | _ -> None)

    let clause op nOp' =
      let types = Operation.argumentTypes op

      match types with
      | [] -> Hence (smtExpr.Apply (op, List.map Ident []), smtExpr.Apply (Operation.changeName nOp' op, []))
      | ts ->
        let vars = List.mapi (fun i t -> ($"x_{i}", t)) types

        smtExpr.QuantifierApplication (
          [ ForallQuantifier vars ],
          Hence (
            smtExpr.Apply (op, List.map Ident vars),
            smtExpr.Apply (Operation.changeName nOp' op, List.map Ident vars)
          )
        )

    let decUniqs cmds idx b =
      List.mapi
        (fun i ->
          function
          | smtExpr.Apply (op, _) when List.contains (Operation.opName op) (decNames cmds) ->
            [ originalCommand.Command (
                DeclareFun ($"{Operation.opName op}$_{idx}_{i}", Operation.argumentTypes op, Operation.returnType op)
              )
              originalCommand.Assert (clause op $"{Operation.opName op}$_{idx}_{i}") ]
            |> Some
          | otherwise -> None)
        (body b)
      |> List.choose (function
        | Some x -> Some x
        | _ -> None)
      |> List.concat

    let applyUniqs cmds idx b =
      List.mapi
        (fun i ->
          function
          | smtExpr.Apply (op, args) when List.contains (Operation.opName op) (decNames cmds) ->
            smtExpr.Apply (Operation.changeName $"{Operation.opName op}$_{idx}_{i}" op, args)
          | otherwise -> otherwise)
        (body b)
      |> function
        | [ x ] -> x
        | xs -> smtExpr.And xs

    let run cmds =
      forCmds
        (fun i ->
          function
          | QuantifierApplication (qs, Hence (b, h)) as expr ->
            decUniqs cmds i b
            |> List.addLast (originalCommand.Assert (QuantifierApplication (qs, Hence (applyUniqs cmds i b, h))))
          | Hence (b, h) ->
            decUniqs cmds i b
            |> List.addLast (originalCommand.Assert (Hence (applyUniqs cmds i b, h)))
          | fact -> [ originalCommand.Assert fact ])
        List.singleton
        cmds
      |> List.concat
      |> fun cmds ->
          let decls =
            List.filter
              (function
              | originalCommand.Command (command.DeclareFun _) -> true
              | _ -> false)
              cmds
            |> Set
            |> Set.toList

          let adtDecls =
            List.filter
              (function
              | originalCommand.Command (command.DeclareDatatype _)
              | originalCommand.Command (command.DeclareDatatypes _) -> true
              | _ -> false)
              cmds

          let defines =
            List.filter
              (function
              | originalCommand.Definition _ -> true
              | _ -> false)
              cmds

          adtDecls
          @ decls
          @ defines
          @ (List.filter
            (function
            | originalCommand.Assert _ -> true
            | _ -> false)
            cmds)

  module chcFF =
    let notFF =
      List.choose (function
        | originalCommand.Assert (smtExpr.Not (smtExpr.Apply (op, []))) when Operation.opName op = "ff" ->
          // Some (originalCommand.Assert (smtExpr.Hence (smtExpr.Apply (op, []), BoolConst false)))
          Some (originalCommand.Assert (smtExpr.Hence (smtExpr.And [ smtExpr.Apply (op, []) ], BoolConst false)))
        | otherwise -> Some otherwise)

  module ApproximateBooleans =
    let bool2int =
      function
      | BoolSort -> IntSort
      | otherwise -> otherwise

    let bools2ints = List.map bool2int

    let eqInt x y =
      smtExpr.Apply (ElementaryOperation ("=", [ IntSort; IntSort ], BoolSort), [ x; y ])

    let distinctInt x y =
      smtExpr.Not (smtExpr.Apply (ElementaryOperation ("=", [ IntSort; IntSort ], BoolSort), [ x; y ]))


    let isTrue x = eqInt x <| Number BigInteger.One
    let isFalse x = eqInt x <| Number BigInteger.Zero
    // let isFalse x = distinctInt x <| Number 1

    let rec rwrtArg =
      function
      | BoolConst false -> Number BigInteger.Zero
      | BoolConst true -> Number BigInteger.One
      | smtExpr.Apply (ElementaryOperation ("=", sorts, BoolSort), [ x; y ]) ->
        smtExpr.Ite (
          smtExpr.Apply (ElementaryOperation ("=", sorts, BoolSort), [ rwrtArg x; rwrtArg y ]),
          Number BigInteger.One,
          Number BigInteger.Zero
        )
      | smtExpr.Apply (ElementaryOperation ("distinct", sorts, BoolSort), [ x; y ]) ->
        smtExpr.Ite (
          smtExpr.Apply (ElementaryOperation ("distinct", sorts, BoolSort), [ rwrtArg x; rwrtArg y ]),
          Number BigInteger.One,
          Number BigInteger.Zero
        )
      | smtExpr.Apply (ElementaryOperation (">", sorts, BoolSort), [ x; y ]) ->
        smtExpr.Ite (
          smtExpr.Apply (ElementaryOperation (">", sorts, BoolSort), [ rwrtArg x; rwrtArg y ]),
          Number BigInteger.One,
          Number BigInteger.Zero
        )
      | smtExpr.Apply (ElementaryOperation (">=", sorts, BoolSort), [ x; y ]) ->
        smtExpr.Ite (
          smtExpr.Apply (ElementaryOperation (">=", sorts, BoolSort), [ rwrtArg x; rwrtArg y ]),
          Number BigInteger.One,
          Number BigInteger.Zero
        )
      | smtExpr.Apply (ElementaryOperation ("<", sorts, BoolSort), [ x; y ]) ->
        smtExpr.Ite (
          smtExpr.Apply (ElementaryOperation ("<", sorts, BoolSort), [ rwrtArg x; rwrtArg y ]),
          Number BigInteger.One,
          Number BigInteger.Zero
        )
      | smtExpr.Apply (ElementaryOperation ("<=", sorts, BoolSort), [ x; y ]) ->
        smtExpr.Ite (
          smtExpr.Apply (ElementaryOperation ("<=", sorts, BoolSort), [ rwrtArg x; rwrtArg y ]),
          Number BigInteger.One,
          Number BigInteger.Zero
        )
      | smtExpr.Let (varExprs, expr) ->
        smtExpr.Let (List.map (fun (var, expr) -> var, rwrtArg expr) varExprs, rwrtArg expr)
      | smtExpr.Match (expr, varExprs) ->
        smtExpr.Match (isTrue <| rwrtArg expr, List.map (fun (expr1, expr2) -> rwrtArg expr1, rwrtArg expr2) varExprs)
      | smtExpr.Ite (expr1, expr2, expr3) -> smtExpr.Ite (isTrue <| rwrtArg expr1, rwrtArg expr2, rwrtArg expr3)
      | smtExpr.And exprs ->
        smtExpr.Ite (smtExpr.And (List.map (rwrtArg >> isTrue) exprs), Number BigInteger.One, Number BigInteger.Zero)
      | smtExpr.Or exprs ->
        smtExpr.Ite (smtExpr.Or (List.map (rwrtArg >> isTrue) exprs), Number BigInteger.One, Number BigInteger.Zero)
      | smtExpr.Not expr -> smtExpr.Ite (isFalse <| rwrtArg expr, Number BigInteger.One, Number BigInteger.Zero)
      | Hence (expr1, expr2) -> Hence (isTrue <| rwrtArg expr1, isTrue <| rwrtArg expr2)
      | QuantifierApplication (quantifiers, expr) ->
        smtExpr.Ite (
          isTrue <| QuantifierApplication (quantifiers, rwrtArg expr),
          Number BigInteger.One,
          Number BigInteger.Zero
        )
      | otherwise -> otherwise

    let rec rwrtExpr boolVars =
      function
      // | smtExpr.BoolConst false -> smtExpr.Number BigInteger.Zero
      // | smtExpr.BoolConst true -> smtExpr.Number BigInteger.One

      | smtExpr.Ident (n, s) when List.contains n boolVars ->
        smtExpr.Ite (isTrue <| smtExpr.Ident (n, s), BoolConst true, BoolConst false)
      | smtExpr.Apply (op, args) -> smtExpr.Apply (op, List.map rwrtArg args)
      | smtExpr.And exprs -> smtExpr.And (List.map (rwrtExpr boolVars) exprs)
      | smtExpr.Or exprs -> smtExpr.Or (List.map (rwrtExpr boolVars) exprs)
      | smtExpr.Not expr -> smtExpr.Not (rwrtExpr boolVars <| expr)
      | Hence (expr1, expr2) -> Hence (rwrtExpr boolVars <| expr1, rwrtExpr boolVars <| expr2)
      // | QuantifierApplication ([ ForallQuantifier vars ], expr) ->
      //   QuantifierApplication (
      //     [ ForallQuantifier (
      //         List.map
      //           (function
      //           | n, sort when sort = BoolSort -> n, IntSort
      //           | otherwise -> otherwise)
      //           vars
      //       ) ],
      //     rwrtExpr
      //       (List.choose
      //         (function
      //         | n, sort when sort = BoolSort -> Some n
      //         | _ -> None)
      //         vars)
      //       expr
      //   )
      | otherwise -> otherwise


    let booleanVarNames =
      List.choose (function
        | n, BoolSort -> Some n
        | _ -> None)

    let bool2intRestrictions =
      List.map (fun n ->
        isTrue
        <| rwrtArg (
          smtExpr.Or
            [ eqInt (Ident (n, IntSort)) (Number BigInteger.Zero)
              eqInt (Ident (n, IntSort)) (Number BigInteger.One) ]
        ))


    let addRestrictions rs =
      function
      | expr when List.isEmpty rs -> expr
      | smtExpr.And exprs -> smtExpr.And (rs @ exprs)
      | expr -> smtExpr.And (List.addLast expr rs)

    let rwrtVarSorts vars =
      List.map
        (function
        | n, sort when sort = BoolSort -> n, IntSort
        | otherwise -> otherwise)
        vars

    let mkQuery fact bNames =
      let rs =
        List.map (fun n -> Ident (n, IntSort) |> distinctInt <| Number BigInteger.Zero) bNames
        @ List.map (fun n -> Ident (n, IntSort) |> distinctInt <| Number BigInteger.One) bNames

      Hence (smtExpr.And (List.addLast fact rs), BoolConst false)

    let rwrt =
      List.map (function
        | originalCommand.Command (DeclareFun (s, sorts, rSort)) ->
          originalCommand.Command (DeclareFun (s, bools2ints sorts, rSort))
        | originalCommand.Assert (QuantifierApplication ([ ForallQuantifier vars ], Hence (body, head))) ->
          let bVarNames = booleanVarNames vars

          originalCommand.Assert (
            QuantifierApplication (
              [ ForallQuantifier (rwrtVarSorts vars) ],
              Hence (
                bool2intRestrictions bVarNames |> flip addRestrictions (rwrtExpr bVarNames body),
                rwrtExpr bVarNames head
              )
            )
          )
        | originalCommand.Assert (Hence (body, head)) ->
          originalCommand.Assert (Hence ((rwrtExpr [] body), (rwrtExpr [] head)))
        | originalCommand.Assert (QuantifierApplication ([ ForallQuantifier vars ], expr)) when
          not <| List.isEmpty (booleanVarNames vars)
          ->
          let bVarNames = booleanVarNames vars

          originalCommand.Assert (
            QuantifierApplication (
              [ ForallQuantifier (rwrtVarSorts vars) ],
              mkQuery (rwrtExpr bVarNames expr) bVarNames
            )
          )

        | originalCommand.Assert (QuantifierApplication ([ ForallQuantifier vars ], expr)) ->
          let bVarNames = booleanVarNames vars

          originalCommand.Assert (
            QuantifierApplication ([ ForallQuantifier (rwrtVarSorts vars) ], (rwrtExpr bVarNames expr))
          )



        | originalCommand.Assert expr -> originalCommand.Assert (rwrtExpr [] expr)

        // | originalCommand.Assert (QuantifierApplication ([ ForallQuantifier vars ], expr)) ->
        //   originalCommand.Assert (rwrtExpr [] expr)

        // | originalCommand.Assert expr -> originalCommand.Assert (rwrtExpr [] expr)
        | d -> d)

  module Parametrized =
    let pars (s: string) =
      let pars = (Regex "par").Matches s
      let pars' = (Regex "par \(\)").Matches s

      if Seq.length pars = Seq.length pars' then
        Seq.toList pars
      else
        printfn "HAVE PARAMETRIZED DATATYPE"
        failwith "HAVE PARAMETRIZED DATATYPE"

    let go (s: string) =
      let rmPar s =
        (Regex "\(\) ").Matches s
        |> Seq.toList
        |> List.head
        |> fun x -> s.Substring <| x.Index + "() ".Length

      let strs =
        List.choose (fun (x: Match) -> balancedBracket (s.Substring <| x.Index - 1)) (pars s)

      List.fold (fun (acc: string) str -> acc.Replace (str + ")", rmPar str)) s strs

  module Selectors =
    let selectors =
      let collect =
        List.concat << List.map (fun (c, _, s) -> List.map (fun s' -> s', (c, s)) s)

      List.choose (function
        | Command (DeclareDatatype (_, vs)) -> Some (collect vs)
        | Command (DeclareDatatypes adts) -> Some (List.concat <| List.map (fun (_, vs) -> collect vs) adts)
        | _ -> None)
      >> List.concat
      >> Map

    let rec rwrt (selectors: Map<_, _>) acc =
      function
      | smtExpr.Apply (op, [ arg ]) when Map.containsKey op selectors ->
        let var, (accVars, acc') = rwrt selectors acc arg
        let c, ss = Map.find op selectors
        let varNames = List.map (fun s -> $"{s}{var}") ss

        let acc'' =
          Set.add
            (smtExpr.Apply (
              ElementaryOperation ("=", [ Operation.returnType c; Operation.returnType c ], BoolSort),
              [ var
                smtExpr.Apply (c, List.map2 (fun s n -> Ident (n, Operation.returnType s)) ss varNames) ]
            ))
            acc'

        Ident ($"{op}{var}", Operation.returnType op),
        (Set
         <| Set.toList accVars
            @ List.map2 (fun n s -> Ident (n, Operation.returnType s)) varNames ss,
         acc'')
      | smtExpr.Ite (expr1, expr2, expr3) ->
        let [ expr1'; expr2'; expr3' ], acc' =
          List.mapFold (rwrt selectors) acc [ expr1; expr2; expr3 ]

        smtExpr.Ite (expr1', expr2', expr3'), acc'
      | smtExpr.And exprs ->
        let exprs', acc' = List.mapFold (rwrt selectors) acc exprs
        smtExpr.And exprs', acc'
      | smtExpr.Or exprs ->
        let exprs', acc' = List.mapFold (rwrt selectors) acc exprs
        smtExpr.Or exprs', acc'
      | smtExpr.Not expr ->
        let expr', acc' = rwrt selectors acc expr
        smtExpr.Not expr', acc'
      | Hence (expr1, expr2) ->
        let expr1', acc' = rwrt selectors acc expr1
        let expr2', acc'' = rwrt selectors acc' expr2
        Hence (expr1', expr2'), acc''
      | smtExpr.Apply (op, args) ->
        let args', acc' = List.mapFold (rwrt selectors) acc args
        smtExpr.Apply (op, args'), acc'
      | otherwise -> otherwise, acc

    let addConstraints xs =
      function
      | Hence (smtExpr.And exprs, h) -> Hence (smtExpr.And (xs @ exprs), h)
      | Hence (expr, h) -> Hence (smtExpr.And (List.addLast expr xs), h)
      | expr when List.length xs = 1 -> Hence (List.head xs, expr)
      | expr when List.length xs > 1 -> Hence (smtExpr.And xs, expr)
      | otherwise -> otherwise

    let run cmds =
      let rwrt = rwrt (selectors cmds) (Set.empty, Set.empty)

      List.choose
        (function
        | originalCommand.Assert (QuantifierApplication ([ ForallQuantifier vars ], expr)) ->
          let expr', (vars', eqs) = rwrt expr

          Some (
            originalCommand.Assert (
              QuantifierApplication (
                [ ForallQuantifier (
                    vars
                    @ List.choose
                        (function
                        | Ident (x, y) -> Some (x, y)
                        | o ->
                          printfn $"OO{o}"
                          None)
                        (List.ofSeq vars')
                  ) ],
                addConstraints (List.ofSeq eqs) expr'
              )
            )
          )
        | originalCommand.Assert expr ->
          let expr', (vars', eqs) = rwrt expr

          Some (
            originalCommand.Assert (
              QuantifierApplication (
                [ ForallQuantifier (
                    List.choose
                      (function
                      | Ident (x, y) -> Some (x, y)
                      | _ -> None)
                      (List.ofSeq vars')
                  ) ],
                addConstraints (List.ofSeq eqs) expr'
              )
            )
          )
        | otherwise -> Some otherwise)
        cmds

let approximation abstrSort file =
  let recs, _, _, _, dataTypes, _, _, _, _ =
    Linearization.linearization abstrSort file

  let p = Parser.Parser false

  let cmds' = p.ParseFile file
  let cmds = Preprocessing.UniqBodyPredicates.run cmds'
  let cmds = Preprocessing.Selectors.run cmds
  let cmds = Preprocessing.NamedAsserts.addNames cmds

  let origCMDsNonBoolApproximated: originalCommand list =
    Preprocessing.UniqBodyPredicates.run cmds'
    |> Preprocessing.Selectors.run
    |> Preprocessing.NamedAsserts.addNames

  let origCMDsNonBoolApproximated =
    if
      List.filter
        (function
        | originalCommand.Assert (QuantifierApplication (_, Hence (_, BoolConst false)))
        | originalCommand.Assert (Hence (_, BoolConst false)) -> true
        | _ -> false)
        origCMDsNonBoolApproximated
      |> List.length = 1
    then
      origCMDsNonBoolApproximated
    else
      originalCommand.Command (DeclareFun ("q", [], BoolSort))
      :: List.choose
        (function
        | originalCommand.Assert (QuantifierApplication (q, Hence (b, BoolConst false))) ->
          Some (
            originalCommand.Assert (
              QuantifierApplication (q, Hence (b, smtExpr.Apply (ElementaryOperation ("q", [], BoolSort), [])))
            )
          )
        | originalCommand.Assert (Hence (b, BoolConst false)) ->
          Some (originalCommand.Assert (Hence (b, smtExpr.Apply (ElementaryOperation ("q", [], BoolSort), []))))
        | otherwise -> Some otherwise)
        origCMDsNonBoolApproximated
      @ [ originalCommand.Assert (Hence (smtExpr.Apply (ElementaryOperation ("q", [], BoolSort), []), BoolConst false)) ]

  // let cmds =
  //   p.ParseFile file
  //   |> Preprocessing.UniqBodyPredicates.run
  //   |> Preprocessing.chcFF.notFF
  //   |> Preprocessing.ApproximateBooleans.rwrt
  //   |> Preprocessing.Selectors.run
  //   |> Preprocessing.NamedAsserts.addNames

  let origDecs =
    List.choose
      (function
      | Command (DeclareFun (n, sorts, _)) -> Some (n, sorts)
      | Definition (DefineFun (n, sorts, _, _)) -> Some (n, List.map snd sorts)
      | _ -> None)
      cmds

  // for x in origDecs do printfn $"----- {x}"

  let p = Parser.Parser false

  for x in List.map toString cmds do
    p.ParseLine x |> ignore

  let rec origExpr = id
  // function
  // | smtExpr.Apply (op, _) when (Operation.opName op).Contains "$name" -> BoolConst true
  // | smtExpr.Apply (op, args) when (Operation.opName op).Contains "$" ->
  //   smtExpr.Apply (Operation.changeName (((Operation.opName op).Split '$')[0]) op, args)
  // | smtExpr.And exprs -> smtExpr.And <| List.map origExpr exprs
  // | smtExpr.Or exprs -> smtExpr.Or <| List.map origExpr exprs
  // | smtExpr.Not expr -> smtExpr.Not <| origExpr expr
  // | Hence (expr1, expr2) -> Hence (origExpr expr1, origExpr expr2)
  // | QuantifierApplication (qs, expr) -> QuantifierApplication (qs, origExpr expr)
  // | otherwise -> otherwise

  let origAsserts =
    List.choose
      (function
      | originalCommand.Assert (QuantifierApplication ([ ForallQuantifier vars ], expr)) ->
        Some (List.map sortedVar2typedVar vars, smtExpr2expr <| origExpr expr)
      | originalCommand.Assert expr -> Some ([], smtExpr2expr <| origExpr expr)
      | _ -> None)
      origCMDsNonBoolApproximated
  // cmds

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

  // for x in adtDecs do printfn $">>>>> {x}"
  let origDecs =
    origDecs
    @ (Map.toList adtDecs
       |> List.map (fun (n, (_, _, ts: Type list)) -> n, List.map (fun (t: Type) -> t.toSort) ts))

  let defConstants =
    let rec helper =
      function
      | smtExpr.Apply (ElementaryOperation (ident, _, _), _)
      | smtExpr.Apply (UserDefinedOperation (ident, _, _), _) when ident.Contains "c_" ->
        [ Def (ident, [], Integer, Int BigInteger.Zero) ]
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

  (origCMDsNonBoolApproximated,
   origDecs,
   origAsserts,
   recs,
   adtDecs,
   defFuns cmds,
   dataTypes,
   defConstants dataTypes,
   decFuns cmds,
   asserts cmds)

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
    | ForAllTyped (names, expr) -> ForAllTyped (names, helper expr)
    | Ite (expr1, expr2, expr3) -> Ite (helper expr1, helper expr2, helper expr3)
    | o -> failwith $"{o}"

  helper



let run times file1 dbg timeLimit learnerInstance redlog (fTimes: string option) =
  // dbgPath <- dbg
  let file = Path.GetTempPath () + Path.GetRandomFileName () + ".smt2"
  File.WriteAllText (file, Preprocessing.Parametrized.go <| File.ReadAllText file1)
  File.WriteAllText (file, HenceNormalization.notFF file)
  File.WriteAllText (file, HenceNormalization.mkSingleQuery file)
  File.WriteAllText (file, HenceNormalization.minimize file)
    

  
  // printfn $"{Preprocessing.Parametrized.go <| File.ReadAllText file}"
  // let ppp = Parser false
  // for x in ppp.ParseFile file do printfn $"<>>><<>><><><> {x}"
  // printfn $"{Preprocessing.RmParametrized.go <| File.ReadAllText file}"
  
  
  let (origCMDsNonBoolApproximated,
       origDecs,
       origAsserts,
       recs,
       adtConstrs,
       defFuns,
       liaTypes,
       defConstants,
       declFuns,
       asserts) =
    approximation IntSort file

  
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

  // printfn "(set-logic ALL)"
  // for x in (List.map (function Def (n, _, _, _ ) -> originalCommand.Command (DeclareFun (n, [], IntSort))) defConstants) @  (List.map program2originalCommand <| toPrograms liaTypes @ toPrograms defFuns @ funDecls @  asserts'') do
  //   printfn $"{x}"
  // printfn "(check-sat)"


  let domain: IAbstractDomain = OptionAbstr (approximation, file)
  // let domain: IAbstractDomain = INTAbsrt (approximation, file)

  // let domain: IAbstractDomain = INTAbsrt(approximation, file)
//   printfn
//     $"
//         defConstants(apprximation) : {domain.Constants}\n
//         liaTypes(approximation) : {(domain.Approximations)}\n
//         funDecls(approximation) : {domain.Declarations}\n
//         asserts(approximation) : {domain.Asserts}\n
// "
  

  match Map.toList adtConstrs with
  | [] ->
    let r =
      (Process.execute "./z3" $"fp.spacer.global=true {file1}").StdOut.Split ("\n")
    // for x in r do  printfn $"{x}"
    (((Process.execute "./z3" $"fp.spacer.global=true {file1}").StdOut.Split ("\n"))[0], ""), [], ""
  | _ ->
    let rec choice asyncs =
      asyncs
      |> Async.Choice
      |> Async.RunSynchronously
      |> function
        | Some x -> x
        | None ->
          printfn "unknown"
          Environment.Exit 0
          failwith ""
    
    
    // return try Some (f.Force()) with _ -> None
    printfn $"###############"
    for i, x in List.mapi (fun i x -> i, x) domain.Approximations do
      printfn $"#{i}"
      for x in x do
          printfn $"{program2originalCommand x}"
          // printfn $"{List.map program2originalCommand x}"
      
    let asyncs =
      List.map
        (fun (x: Program list) ->
            lazy
              solver
                times
                origCMDsNonBoolApproximated
                origDecs
                origAsserts
                declFuns
                (adtDecs, recs)
                adtConstrs
                domain.Definitions
                domain.DomainADT
                domain.Constants
                x
                domain.Declarations
                domain.Asserts
                learnerInstance
                redlog
                fTimes)
        domain.Approximations
        // [  (Array.ofList domain.Approximations)[1] ]
      |> Seq.map
           (fun f ->
              (async { return try Some (f.Force()) with e -> (); None }))

    let v, _ = choice asyncs
    
    // let v, _ =
    //   solver
    //     times
    //     origCMDsNonBoolApproximated
    //     origDecs
    //     origAsserts
    //     declFuns
    //     (adtDecs, recs)
    //     adtConstrs
    //     domain.Definitions
    //     // (toPrograms defFuns)
    //     domain.DomainADT
    //     domain.Constants
    //     // defConstants
    //     domain.Approximations
    //     // (toPrograms liaTypes)
    //     // funDecls
    //     domain.Declarations
    //     // asserts''
    //     domain.Asserts
    //     learnerInstance
    //     redlog
    //     fTimes

    v, durations, ""


module Shiza =
  let pp file =
    let p = Parser false
    let cmds = p.ParseFile file

    List.map
      (function
      | originalCommand.Assert (Hence _)
      | originalCommand.Assert (QuantifierApplication (_, Hence _)) as x -> x
      | originalCommand.Assert (QuantifierApplication (vars, e)) ->
        originalCommand.Assert (QuantifierApplication (vars, Hence (smtExpr.And [ BoolConst true ], e)))
      | originalCommand.Assert e -> originalCommand.Assert (Hence (smtExpr.And [ BoolConst true ], e))
      | otherwise -> otherwise)
      cmds
    |> List.map toString
    |> join "\n"

  let qs =
    List.filter (function
      | originalCommand.Assert (Hence (_, BoolConst false))
      | originalCommand.Assert (QuantifierApplication (_, Hence (_, BoolConst false))) -> true
      | _ -> false)

  let withHead h =
    List.filter (function
      | originalCommand.Assert (Hence (_, smtExpr.Apply (n, _)))
      | originalCommand.Assert (QuantifierApplication (_, Hence (_, smtExpr.Apply (n, _)))) when n = h -> true
      | _ -> false)

  let body =
    function
    | originalCommand.Assert (Hence (smtExpr.And b, _))
    | originalCommand.Assert (QuantifierApplication (_, Hence (smtExpr.And b, _))) -> b
    | originalCommand.Assert (Hence (b, _))
    | originalCommand.Assert (QuantifierApplication (_, Hence (b, _))) -> [ b ]
    | _ -> []



let ttt () =
  let p = Parser.Parser false

  for c in p.ParseFile "/home/andrew/RiderProjects/adt-solver-smr/CataHornSolver/Tests/Source/racer.horn.smt2" do
    printfn $"{c}"


let sdf () =
  let files = Directory.GetFiles "/home/andrew/Downloads/adt_lia(6)/cata-sats"

  for file in files do
    File.WriteAllText (
      $"/home/andrew/adt-solver/v/vv/vvv/athena/benchmarks/test/out-{Path.GetFileName file}",
      Shiza.pp file
    )

let ppppp () =
  let p = Parser.Parser false
  let cmds = p.ParseFile "/home/andrew/adt-solver/smr/tts.smt2"

  for x in cmds do
    printfn $">> {x}"


let rlslsls () =
  let files =
    Directory.GetFiles "/home/andrew/Downloads/TIP-no-NAT-main(11)/TIP-no-NAT-main/adt_lia"

  for file in files do
    // printfn $"{file}"
    let file1 = Path.GetTempPath () + Path.GetRandomFileName () + ".smt2"
    File.WriteAllText (file1, Preprocessing.Parametrized.go <| File.ReadAllText file)
    let p = Parser.Parser false
    let cmds = p.ParseFile (file1)

    if
      List.choose
        (function
        | Command (command.DeclareDatatype _)
        | Command (command.DeclareDatatypes _) -> Some ()
        | _ -> None)
        cmds
      |> List.isEmpty
    then
      printfn $"{file}"


// let aaaaaaaaaaa () =
//   let dir =
//     Directory.GetFiles "/home/andrew/adt-solver/benchs/tests/is-approximation-exist"
//
//   for file in dir do
//     printfn $"{Path.GetFileName file}"
//
//     let p = Parser.Parser false
//     let path = file
//
//     let file = Path.GetTempPath () + Path.GetRandomFileName () + ".smt2"
//     File.WriteAllText (file, Preprocessing.Parametrized.go <| File.ReadAllText path)
//     let cmds = p.ParseFile file
//
//     let (origCMDsNonBoolApproximated,
//          origDecs,
//          origAsserts,
//          recs,
//          adtConstrs,
//          defFuns,
//          liaTypes,
//          defConstants,
//          declFuns,
//          asserts) =
//       approximation file
//
//     let toPrograms = List.map origCommand2program
//     let funDecls = List.map origCommand2program declFuns
//
//     // printfn $"(set-logic ALL)"
//     // for x in List.map program2originalCommand <| decConsts defConstants @ toPrograms liaTypes @ toPrograms defFuns  do
//     // printfn $"{x}"
//     let aa =
//       "\n"
//       + (String.Join (
//         "\n",
//         List.map
//           (fun x -> x.ToString ())
//           (List.map program2originalCommand
//            <| ((decConsts defConstants) @ (toPrograms liaTypes) @ (toPrograms defFuns)))
//       ))
//       + "\n"
//
//     let content =
//       "(set-logic UFDTNIA)"
//       + aa
//       + (List.choose (function
//            | originalCommand.Command (command.DeclareFun (symbol, b, sorts, sort)) ->
//              Some (
//                originalCommand.Command (
//                  command.DeclareFun (
//                    symbol,
//                    b,
//                    List.map
//                      (function
//                      | ADTSort _ -> IntSort
//                      | otherwise -> otherwise)
//                      sorts,
//                    sort
//                  )
//                )
//              )
//            | originalCommand.Command (command.DeclareConst _) as c -> Some c
//            | originalCommand.Assert (QuantifierApplication ([ ForallQuantifier vars ], expr)) ->
//              Some (
//                originalCommand.Assert (
//                  QuantifierApplication (
//                    [ ForallQuantifier (
//                        List.map
//                          (fun (n, sort) ->
//                            match sort with
//                            | ADTSort _ -> (n, IntSort)
//                            | otherwise -> (n, otherwise))
//                          vars
//                      ) ],
//                    expr
//                  )
//                )
//              )
//            | originalCommand.Assert _ as a -> Some a
//            | _ -> None)
//          <| Preprocessing.Selectors.run cmds
//          |> List.map toString
//          |> join "\n")
//       + "\n(check-sat)"
//
//     File.WriteAllText (
//       $"/home/andrew/adt-solver/benchs/tests/is-approximation-exist/{Path.GetFileName path}-apprxmt.smt2",
//       content
//     )

let chch () =
  let eqOpSorts =
    function
    | ElementaryOperation ("=", [ typ1; typ2 ], BoolSort) -> Some typ1
    | _ -> None

  let distinctOpSorts =
    function
    | ElementaryOperation ("distinct", [ typ1; typ2 ], BoolSort) -> Some typ1
    | _ -> None

  let isDistinctTerm =
    function
    | smtExpr.Apply (op, _) when Operation.opName op = "distinct" ->
      match distinctOpSorts op with
      | Some t when t <> IntSort && t <> BoolSort -> true
      | _ -> false
    | smtExpr.Not (smtExpr.Apply (eqOp, _)) when Operation.opName eqOp = "=" ->
      match eqOpSorts eqOp with
      | Some t when t <> IntSort && t <> BoolSort -> true
      | _ -> false
    | _ -> false

  let exprHaveDistinct =
    function
    | Hence (expr, _) ->
      match expr with
      | smtExpr.And exprs -> List.fold (fun acc expr -> acc || isDistinctTerm expr) false exprs
      | _ -> isDistinctTerm expr
    | _ -> false


  let dir =
    Directory.GetFiles "/home/andrew/adt-solver/benchs/tests/pretty-named-tests"

  for file in dir do
    printfn $"{Path.GetFileName file}"

    let p = Parser.Parser false
    let file' = Path.GetTempPath () + Path.GetRandomFileName () + ".smt2"
    File.WriteAllText (file', Preprocessing.Parametrized.go <| File.ReadAllText file)

    let cmds = p.ParseFile file'

    let cmdsHaveDistinct cmds =
      List.fold
        (fun acc ->
          function
          | originalCommand.Assert (QuantifierApplication (_, expr)) -> acc || exprHaveDistinct expr
          | originalCommand.Assert expr -> acc || exprHaveDistinct expr
          | _ -> acc)
        false
        cmds

    File.AppendAllText (
      "/home/andrew/adt-solver/benchs/tests/out.csv",
      $"chc/{Path.GetFileName file}, {cmdsHaveDistinct cmds}\n"
    )



let suka () =
  let c =
    """(define-fun $name_5 () Bool    true)
(define-fun $name_8 () Bool    true)
(define-fun $name_6 () Bool    true)
(define-fun $name_13 () Bool    true)
(define-fun $name_0 () Bool    true)
(define-fun $name_1 () Bool    true)
(define-fun $name_9 () Bool    true)
(define-fun $name_10 () Bool    true)
(define-fun $name_3 () Bool    true)
(define-fun ff$_8_0 () Bool    false)
(define-fun $name_7 () Bool    true)
(define-fun $name_11 () Bool    true)
(define-fun $name_4 () Bool    true)
(define-fun ff () Bool    false)
(define-fun $name_2 () Bool    true)
(define-fun $name_14 () Bool    true)
(define-fun $name_12 () Bool    true)
(define-fun id_list$_9_1 ((x!0 Int) (x!1 Int)) Bool    (and (not (>= (+ x!0 (* (- 1) x!1)) 1))         (not (<= (+ x!0 (* (- 1) x!1)) (- 1)))))
(define-fun len ((x!0 Int) (x!1 Int)) Bool    (and (or (not (= x!0 14)) (not (= (mod x!1 2) 0)))         (not (<= x!0 0))         (or (not (<= x!0 1)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 3)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 2)) (not (= (mod x!1 2) 0)))         (or (not (= x!0 4)) (not (= (mod x!1 2) 0)))         (or (not (= x!0 5)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 6)) (not (= (mod x!1 2) 0)))         (or (not (= x!0 7)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 8)) (not (= (mod x!1 2) 0)))         (or (not (= x!0 9)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= (mod x!0 2) 1)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 10)) (not (= (mod x!1 2) 0)))         (or (not (= (mod (+ 1 x!0) 2) 0)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= (mod x!0 2) 0)) (not (= (mod x!1 2) 0)))         (or (not (= x!0 11)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 13)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 12)) (not (= (mod x!1 2) 0)))         (or (not (= x!0 15)) (not (= (mod (+ 1 x!1) 2) 0)))))
(define-fun len$_15_1 ((x!0 Int) (x!1 Int)) Bool    (and (or (not (= x!0 14)) (not (= (mod x!1 2) 0)))         (not (<= x!0 0))         (or (not (= x!0 2)) (not (= (mod x!1 2) 0)))         (or (not (<= x!0 1)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 3)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 4)) (not (= (mod x!1 2) 0)))         (or (not (= x!0 5)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 6)) (not (= (mod x!1 2) 0)))         (or (not (= x!0 7)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 8)) (not (= (mod x!1 2) 0)))         (or (not (<= x!0 9))             (not (= (mod x!0 2) 1))             (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 10)) (not (= (mod x!1 2) 0)))         (or (not (= x!0 9)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= (mod x!0 2) 0)) (not (= (mod x!1 2) 0)))         (or (not (= (mod (+ 1 x!0) 2) 0)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 12)) (not (= (mod x!1 2) 0)))))
(define-fun append$_9_2 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool    (and (or (not (<= (+ (* 2 x!0) (* (- 1) x!2)) (- 1)))             (not (<= (+ (* 2 x!1) (* (- 1) x!2)) 0)))         (or (not (>= x!0 2)) (not (>= x!1 2)) (not (<= x!2 2)))         (or (not (= x!2 4)) (not (<= x!1 2)) (not (<= x!0 2)))         (or (not (>= x!0 4)) (not (>= x!1 4)) (not (<= x!2 6)))         (or (not (<= (+ (* 3 x!0) (* (- 1) x!2)) 1))             (not (<= x!1 3))             (not (<= (+ (* 3 x!1) (* (- 1) x!2)) 3))             (not (<= x!0 3)))         (or (not (>= (+ (* 2 x!1) (* (- 1) x!2)) 2))             (not (>= (+ x!0 (* (- 1) x!1)) 0)))         (or (not (= x!0 x!1)) (not (= (+ (* 2 x!1) (* (- 1) x!2)) 0)))         (or (not (= x!2 16)) (not (<= x!1 8)) (not (= x!0 8)))         (or (not (<= x!0 10)) (not (>= x!2 20)) (not (<= x!1 10)))         (or (not (>= (+ (* (/ 1.0 2.0) 2.0)                         (* (- 1.0) 2.0))                      0.0))             (not (<= x!1 8))             (not (<= (+ x!0 (* (- 1) x!1)) 0)))))
(define-fun id_list ((x!0 Int) (x!1 Int)) Bool    (and (not (>= (+ x!0 (* (- 1) x!1)) 1))         (or (not (<= x!0 1)) (not (<= x!1 0)))         (not (<= (+ x!0 (* (- 1) x!1)) (- 1)))))
(define-fun id_list$_11_0 ((x!0 Int) (x!1 Int)) Bool    (and (not (>= (+ x!0 (* (- 1) x!1)) 1))         (or (not (<= x!0 1)) (not (<= x!1 0)))         (not (<= (+ x!0 (* (- 1) x!1)) (- 1)))))
(define-fun append ((x!0 Int) (x!1 Int) (x!2 Int)) Bool    (and (not (<= (+ x!0 x!1 (* (- 1) x!2)) 0))         (not (<= x!0 0))         (not (>= (+ x!0 x!1 (* (- 1) x!2)) 2))))
(define-fun len$_9_3 ((x!0 Int) (x!1 Int)) Bool    (and (or (not (= x!0 15)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (<= x!0 1)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 3)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 5)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 7)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 9)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 11)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= (mod x!0 2) 1)) (not (= (mod (+ 1 x!1) 2) 0)))         (or (not (= x!0 13)) (not (= (mod (+ 1 x!1) 2) 0)))))
(define-fun append$_13_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool    (and (not (<= (+ x!0 x!1 (* (- 1) x!2)) 0))         (not (>= (+ x!1 (* (- 1) x!2)) 1))         (not (>= (+ x!0 x!1 (* (- 1) x!2)) 2))))
(define-fun map_not ((x!0 Bool) (x!1 Bool)) Bool    false)
(define-fun even ((x!0 Int) (x!1 Bool)) Bool    false)
(define-fun leq ((x!0 Int) (x!1 Int) (x!2 Bool)) Bool    false)
"""
    |> split "\n"
  
  for x in c do
    printfn $"{x}" 

  let p = Parser.Parser false
  
  for x in c do
    printfn $"{x}"
    p.ParseLine $"{x}" |> ignore 
  
  // let _, r = p.ParseModel c
  // for x in r do 
  //   printfn $"{x}"  