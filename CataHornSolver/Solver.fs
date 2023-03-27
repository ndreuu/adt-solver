module ProofBased.Solver

open System
open System.Collections.Generic
open System.IO
open Microsoft.FSharp.Quotations
open Microsoft.Z3
open SMTLIB2

open Tree.Tree
open ProofBased.Utils
open Z3Interpreter.Interpreter
open Z3Interpreter.AST
open Approximation

let defConstants =
  [ Def ("c_0", [], Int 0); Def ("c_1", [], Int 0); Def ("c_2", [], Int 0) ]

let defFuns =
  [ Def ("Z", [], Apply ("c_0", []))
    Def ("S", [ "x" ], Add (Apply ("c_1", []), Mul (Apply ("c_2", []), Var "x"))) ]

let declFuns = [ Decl ("diseqInt", 2) ]

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
    // DeclConst "x4"
    Assert (ForAll ([| "x4" |], Implies (App ("diseqInt", [| Var "x4"; Var "x4" |]), Bool false))) ]

let assert5 = [ Assert (Eq (Int 1, Int 2)) ]


// let listConst =
// [ Def ("c_0", [], Int 0)
// Def ("c_1", [], Int 1)
// Def ("c_2", [], Int 1)
// Def ("c_3", [], Int 0) ]

let listConst =
  [ Def ("c_0", [], Int 1)
    Def ("c_1", [], Int 1)
    Def ("c_2", [], Int 1)
    Def ("c_3", [], Int 1) ]


let shiza =
  [ Def ("c_0", [], Int 1)
    Def ("c_1", [], Int 1)
    Def ("c_2", [], Int 1)
    Def ("c_3", [], Int 1)
    Def ("c_4", [], Int 1)
    Def ("c_5", [], Int 0)
    Def ("c_6", [], Int 0)
    Def ("c_7", [], Int 0)
    Def ("c_8", [], Int 0)
    Def ("c_9", [], Int 0) ]

// let shiza =
//   [ Def ("c_0", [], Int 1L)
//     Def ("c_1", [], Int 1L)
//     Def ("c_2", [], Int 1L)
//     Def ("c_3", [], Int 1L)
//     Def ("c_4", [], Int 0L)
//     Def ("c_5", [], Int 0L)
//     Def ("c_6", [], Int 1L)
//     Def ("c_7", [], Int 0L)
//     Def ("c_8", [], Int 1L)
//     Def ("c_9", [], Int 0L) ]

// let shiza =
//   [ Def ("c_0", [], Int 0)
//     Def ("c_1", [], Int 1)
//     Def ("c_2", [], Int 1)
//     Def ("c_3", [], Int 1)
//     Def ("c_4", [], Int 0)
//     Def ("c_5", [], Int 1)
//     Def ("c_6", [], Int 0)
//     Def ("c_7", [], Int 1)
//     Def ("c_8", [], Int 0)
//     Def ("c_9", [], Int 1) ]




// let listConst =
//    [ Def ("c_0", [], Int 5L)
//      Def ("c_1", [], Int -31L)
//      Def ("c_2", [], Int 5L)
//      Def ("c_3", [], Int 4L) ]


//horn; proof; redlog; smt

//
// let listDeclConst =
//   [ DeclConst ("c_0")
//     DeclConst ("c_1")
//     DeclConst ("c_2")
//     DeclConst ("c_3") ]
//

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
//
//
// let listDefFunsLearher =
//   [ Def ("nil", [], Var ("c_0"))
//     Def (
//       "cons",
//       [ "x"; "y" ],
//       Add (Var ("c_1"), Add (Mul (Var ("c_2"), Var "x"), Mul (Var ("c_3"), Var "y")))
//     ) ]
//
let listDeclFuns = [ Decl ("app", 3); Decl ("last", 2) ]
//
let listAssert1 =
  Assert (ForAll ([| "ys1" |], App ("app", [| Apply ("nil", []); Var "ys1"; Var "ys1" |])))
//
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
//
let listAssert3 =
  Assert (ForAll ([| "x3" |], App ("last", [| Apply ("cons", [ Var "x3"; Apply ("nil", []) ]); Var "x3" |])))
//
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



let dConsts =
  [ Def ("c_0", [], Int 1); Def ("c_1", [], Int 1); Def ("c_2", [], Int 1) ]

let dDefFuns =
  [ Def ("Z", [], Apply ("c_0", []))
    Def ("S", [ "x" ], Add (Apply ("c_1", []), Mul (Apply ("c_2", []), Var "x"))) ]


let dDeclFuns = [ Decl ("diseqInt", 2) ]

let dA1 =
  Assert (ForAll ([| "x1" |], App ("diseqInt", [| Apply ("Z", []); Apply ("S", [ Var "x1" ]) |])))
// Assert (ForAll ([| "x" |], App ("diseqInt", [| Apply ("Z", []); Apply ("S", [ Var "x" ]) |])))

let dA2 =
  Assert (ForAll ([| "x2" |], App ("diseqInt", [| Apply ("S", [ Var "x2" ]); Apply ("Z", []) |])))
// Assert (ForAll ([| "x" |], App ("diseqInt", [| Apply ("S", [ Var "x" ]); Apply ("Z", []) |])))

let dA3 =
  Assert (
    ForAll (
      [| "x3"; "y3" |],
      Implies (
        App ("diseqInt", [| Var "x3"; Var "y3" |]),
        App ("diseqInt", [| Apply ("S", [ Var "x3" ]); Apply ("S", [ Var "y3" ]) |])
      )
    )
  )
// Assert (
// ForAll (
// [| "x"; "y" |],
// Implies (
// App ("diseqInt", [| Var "x"; Var "y" |]),
// App ("diseqInt", [| Apply ("S", [ Var "x" ]); Apply ("S", [ Var "y" ]) |])
// )
// )
// )

let dA4 =
  Assert (ForAll ([| "x4" |], Implies (App ("diseqInt", [| Var "x4"; Var "x4" |]), Bool false)))
// Assert (ForAll ([| "x" |], Implies (App ("diseqInt", [| Var "x"; Var "x" |]), Bool false)))





let emptyEnv params =
  { ctxSlvr = new Context (params |> dict |> Dictionary)
    ctxVars = Map.empty
    ctxFuns = Map.empty
    ctxDecfuns = Map.empty }
// Microsoft.Z3.Global.SetParameter("asd", "true")
// let tststs = (emptyEnv ()).ctxSlvr.MkParams ()
// let () = tststs.Context.ProbeNames |> fun vs -> for v in vs do printfn "%O" v


let proofTree hProof =
  let rec helper (HyperProof (_, hyperProofs, head)) =
    match hyperProofs with
    | [] -> head |> smtExpr2expr |> (fun x -> Node (x, []))
    | _ -> Node (head |> smtExpr2expr, hyperProofs |> List.map helper)

  helper hProof

let impliesAsserts clarify asserts name =
  asserts
  |> List.filter (function
    | Assert (ForAll (_, Implies (_, App (n, _)))) when n = name -> true
    | Assert (Implies (_, App (n, _))) when n = name -> true
    | _ -> false)
  |> clarify

let axiomAsserts clarify asserts name =
  asserts
  |> List.filter (function
    | Assert (ForAll (_, App (n, _))) when n = name -> true
    | Assert (App (n, _)) when n = name -> true
    | _ -> false)
  |> fun x ->
       printfn $"!!!!!!{x}"
       clarify x

let queryAssert asserts =
  asserts
  |> List.filter (function
    | Assert (ForAll (_, Implies (_, Bool false))) -> true
    | _ -> false)
  |> List.head

let rec assertsTree asserts consts defs decs =
  function
  | Node (Apply (name, _), []) ->
    printfn $">>>>>{asserts}"
    name |> axiomAsserts List.head asserts |> (fun x -> Node (x, []))
  | Node (Apply (name, _), ts) ->
    name
    |> impliesAsserts List.head asserts
    |> fun x -> Node (x, ts |> List.map (assertsTree asserts consts defs decs))
  | Node (Bool false, ts) -> Node (queryAssert asserts, ts |> List.map (assertsTree asserts consts defs decs))
  | _ -> failwith "123"

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






// let varNames = List.map (function Var n -> n | otherwise -> failwith $"Var expected {otherwise}")


type apps = Map<Name, Expr list>

let getApp name (apps: apps) =
  printfn $"NNNN:: {name}"

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

let exprTree =
  Tree.fmap (function
    | Assert (ForAll (_, x)) -> x
    | Assert (x) -> x
    | _ -> failwith "Assert forall expected")

let appBody =
  let appNames =
    let rec helper (acc: Set<Name>) =
      function
      | App (n, exprs) -> Array.fold helper acc exprs |> Set.add n
      | Int _
      | Var _
      | Bool _ -> acc
      | Eq (expr1, expr2)
      | Lt (expr1, expr2)
      | Gt (expr1, expr2)
      | Le (expr1, expr2)
      | Ge (expr1, expr2)
      | Add (expr1, expr2)
      | Mod (expr1, expr2)
      | Mul (expr1, expr2) -> helper acc expr1 |> fun acc -> helper acc expr2
      | Implies (expr1, _) -> helper acc expr1
      | And exprs
      | Or exprs -> Array.fold helper acc exprs
      | Not expr
      | Neg expr
      | ForAll (_, expr) -> helper acc expr
      | Apply (_, exprs) -> List.fold helper acc exprs
      | Ite (expr1, expr2, expr3) ->
        helper acc expr1 |> Set.union <| helper acc expr2 |> Set.union
        <| helper acc expr3

    helper Set.empty

  Tree.fmap appNames

let appHead =
  Tree.fmap (function
    | App _ as app -> app
    | Implies (_, h) -> h
    | _ -> failwith "appHead")

let findApp name (tree: (Set<Name> * Expr) tree list) =
  List.filter
    (function
    | Node ((_, App (n, _)), _) when n = name -> true
    | _ -> false)
    tree
  |> List.map (function
    | Node ((_, app), _) -> app)

let rec mapAppsTree (tree: (Set<Name> * Expr) tree) =
  match tree with
  | Node ((appNames, _), ts) ->
    let map =
      Set.fold
        (fun (acc: apps) name ->
          let apps = findApp name ts

          match apps with
          | [] -> acc
          | _ -> acc |> Map.add name apps)
        Map.empty
        appNames

    Node (map, ts |> List.map mapAppsTree)


let updVars =
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
    | Mul (expr1, expr2)
    | Mod (expr1, expr2)
    | Implies (expr1, expr2) -> varNames (varNames acc expr1) expr2
    | ForAll (_, expr)
    | Neg expr
    | Not expr -> varNames acc expr
    | App (_, exprs)
    | And exprs
    | Or exprs -> Array.fold varNames acc exprs
    | Apply (_, exprs) -> List.fold varNames acc exprs
    | Ite (expr1, expr2, expr3) -> List.fold varNames acc [ expr1; expr2; expr3 ]

  let rename i expr =
    Set.fold (fun (acc, i) n -> (renameVar n $"x{i}" acc, i + 1)) (expr, i)

  let rec numLine i (line: Expr tree list) =
    List.foldBack
      (fun x (acc, i) ->
        match x with
        | Node (v, ts) ->
          varNames Set.empty v
          |> rename i v
          |> fun (e, i') ->
               let ts', i'' = numLine i' ts
               (Node (e, ts') :: acc, i''))
      line
      ([], i)

  function
  | Node (x, ts) ->
    let x', i = varNames Set.empty x |> rename 0 x
    let ts' = numLine i ts |> fst
    Node (x', ts')


let constraint =
  let rec helper acc =
    function
    | Var _
    | Int _
    | Apply _
    | App _
    | Ite _
    | Add _
    | Neg _
    | Mod _
    | Bool _ -> acc
    | Eq _
    | Lt _
    | Gt _
    | Le _
    | Ge _
    | Not _
    | Mul _ as c -> c :: acc
    | And exprs -> Array.fold helper acc exprs
    | Or exprs -> Array.fold helper acc exprs
    | ForAll (_, expr)
    | Implies (expr, _) -> helper acc expr

  helper []



//(forall ((x0 Int) (x1 Int) (x10 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int) (x6 Int) (x7 Int) (x8 Int) (x9 Int))
// (=> (and
// (not (= x1 x0))
// (not (= x3 nil))
// (not (= x7 nil))
// (= x2 nil)
// (= x3 (cons x10 nil))
// (= x4 (cons x6 x7))
// (= x7 (cons x8 nil))

// (= x3 x9)
// (= x4 x9)

// (= x1 x10)
// (= x0 x5)
// (= x5 x8))
// false))

let isVar =
  function
  | Var _ -> true
  | _ -> false

let matchEqEquivalents equivalents expr =
  List.fold
    (fun _ x ->
      match expr with
      | Eq (e, y)
      | Eq (y, e) when x = y -> Some e
      | _ -> None)
    None
    equivalents

let varVarEqs exprs =
  exprs
  |> List.filter (function
    | Eq (Var _, Var _) -> true
    | _ -> false)


let transitiveEqVars (exprs: Expr list) =
  let eq =
    List.fold (fun acc expr ->
      match matchEqEquivalents acc expr with
      | Some x -> x :: acc
      | None -> acc)

  let vars =
    varVarEqs exprs
    |> List.map vars
    |> List.fold (@) []
    |> List.map (fun v -> (v, None))

  List.fold
    (fun map (var, _) ->
      map
      |> Map.tryFind var
      |> function
        | Some _ -> map
        | None ->
          let eqVars =
            varVarEqs exprs
            |> List.fold
                 (fun acc x ->
                   match x with
                   | Eq (x, y) when x = var || y = var -> (eq [ x; y ] exprs)
                   | _ -> acc)
                 []

          eqVars |> List.fold (fun acc x -> acc |> Map.add x var) map)
    Map.empty
    vars


let simplify' (exprs: Expr list) : Expr list =
  printfn "AAAAAAAAAAA!"

  let substituteVals varVals exprs =
    exprs
    |> List.map (fun expr -> varVals |> List.fold (fun acc (var, value) -> substituteVar var value acc) expr)

  let varValEqs exprs =
    let varVals =
      exprs
      |> List.fold
           (fun acc x ->
             (match x with
              | Eq (Var _ as x, y)
              | Eq (y, (Var _ as x)) when y |> (isVar >> not) -> (x, y) :: acc
              | _ -> acc))
           []

    let vars, values = List.unzip varVals

    substituteVals varVals values |> List.zip vars

  let substitutedValExprs = substituteVals (varValEqs exprs) exprs

  let equivalentVars = transitiveEqVars substitutedValExprs

  let rmEqWithSameArgs =
    List.fold
      (fun acc x ->
        match x with
        | Eq (x, y) when x = y -> acc
        | _ -> x :: acc)
      []

  substitutedValExprs
  |> List.map (fun expr ->
    vars expr
    |> List.fold
         (fun acc x ->
           equivalentVars
           |> Map.tryFind x
           |> function
             | None -> acc
             | Some v -> substituteVar x v acc)
         expr)
  |> rmEqWithSameArgs
  |> List.rev
  |> fun v -> substituteVals (varValEqs v) v |> rmEqWithSameArgs


let asdf () =
  simplify'
    [ Not (Eq (Var "x1", Var "x0"))
      Not (Eq (Var "x3", Apply ("nil", [])))
      Eq (Var "x2", Apply ("nil", []))
      Eq (Var "x3", Var "x9")
      Eq (Var "x4", Var "x9")
      Eq (Var "x3", Apply ("cons", [ Var "x10"; Apply ("nil", []) ]))
      Eq (Var "x1", Var "x10")
      Eq (Var "x4", Apply ("cons", [ Var "x6"; Var "x7" ]))
      Eq (Var "x0", Var "x5")
      Not (Eq (Var "x7", Apply ("nil", [])))
      Eq (Var "x7", Apply ("cons", [ Var "x8"; Apply ("nil", []) ]))
      Eq (Var "x5", Var "x8") ]
  |> fun vs ->
       for v in vs do
         printfn $"{v}"

  ()

let simplify (exprs: Expr list) : Expr list =
  List.map expr2smtExpr exprs
  |> fun vs ->
       for v in vs do
         printfn $"{v}"

  simplify' exprs
// exprs



let resolvent =
  let rec helper acc =
    function
    | apps, expr when Map.empty <> apps ->
      let constraint = constraint expr

      let rec appArgs apps acc =
        function
        | Var _
        | Int _
        | Apply _
        | Ite _
        | Bool _ -> (acc, apps)
        | Eq (expr1, expr2)
        | Lt (expr1, expr2)
        | Gt (expr1, expr2)
        | Le (expr1, expr2)
        | Ge (expr1, expr2)
        | Add (expr1, expr2)
        | Mod (expr1, expr2)
        | Mul (expr1, expr2) -> (appArgs apps acc expr1) |> fun (acc, apps) -> appArgs apps acc expr2
        | And exprs
        | Or exprs -> Array.fold (fun (acc, apps) e -> appArgs apps acc e) (acc, apps) exprs
        | Not expr
        | Neg expr
        | ForAll (_, expr)
        | Implies (expr, _) -> appArgs apps acc expr
        | App (name, args) ->
          getApp name apps
          |> fun (args', apps') -> (acc @ (Array.map2 (fun x y -> Eq (x, y)) args args' |> Array.toList), apps')

      appArgs apps constraint expr |> fst
    | _ -> acc

  Tree.fold (fun acc x -> helper acc x @ acc) []
  >> simplify
  >> List.toArray
  >> And

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


let clause mapTree =
  match resolvent mapTree with
  | And [||] -> Bool false
  | otherwise -> Implies (otherwise, Bool false) |> forAll

// Implies (resolvent mapTree, Bool false) |> forAll



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


let ands =
  let rec helper acc =
    function
    | And [| x; y |] -> helper (y :: acc) x
    | v -> v :: acc

  helper [] >> List.toArray

let ors =
  let rec helper acc =
    function
    | Or [| x; y |] -> helper (y :: acc) x
    | v -> v :: acc

  helper [] >> List.toArray

let rec rmAndOrRepeats =
  function
  | And _ as and' -> And (ands and' |> Array.map rmAndOrRepeats)
  | Or _ as or' -> Or (ors or' |> Array.map rmAndOrRepeats)
  | Implies (expr1, expr2) -> Implies (rmAndOrRepeats expr1, rmAndOrRepeats expr2)
  | Int _
  | Var _
  | Bool _ as expr -> expr
  | Eq (expr1, expr2) -> Eq (rmAndOrRepeats expr1, rmAndOrRepeats expr2)
  | Lt (expr1, expr2) -> Lt (rmAndOrRepeats expr1, rmAndOrRepeats expr2)
  | Gt (expr1, expr2) -> Gt (rmAndOrRepeats expr1, rmAndOrRepeats expr2)
  | Le (expr1, expr2) -> Le (rmAndOrRepeats expr1, rmAndOrRepeats expr2)
  | Ge (expr1, expr2) -> Ge (rmAndOrRepeats expr1, rmAndOrRepeats expr2)
  | Mod (expr1, expr2) -> Mod (rmAndOrRepeats expr1, rmAndOrRepeats expr2)
  | Add (expr1, expr2) -> Add (rmAndOrRepeats expr1, rmAndOrRepeats expr2)
  | Mul (expr1, expr2) -> Mul (rmAndOrRepeats expr1, rmAndOrRepeats expr2)
  | Not expr
  | Neg expr -> rmAndOrRepeats expr
  | Apply (name, exprs) -> Apply (name, List.map rmAndOrRepeats exprs)
  | ForAll (names, expr) -> ForAll (names, rmAndOrRepeats expr)
  | App (name, exprs) -> App (name, Array.map rmAndOrRepeats exprs)
  | Ite (expr1, expr2, expr3) -> Ite (rmAndOrRepeats expr1, rmAndOrRepeats expr2, rmAndOrRepeats expr3)

let redlog definitions formula =
  Redlog.runRedlog definitions formula
  |> function
    | Some v ->
      // printfn $"..............\n{smtExpr2expr' v |> expr2smtExpr  }..............\n"
      Assert <| (smtExpr2expr' v)
    | None -> Assert <| (Bool false)
// failwith "redlog nothing"

let decConst =
  function
  | Def (n, _, _) -> DeclConst n
  | otherwise -> otherwise

let hyperProof2clause defConsts decFuns hyperProof asserts =
  let progTree = proofTree hyperProof |> assertsTree asserts defConsts defFuns decFuns
  let updVars = exprTree progTree |> updVars
  let bodiesHeads = Tree.zip (appBody updVars) (appHead updVars)
  let mapTree = Tree.zip (mapAppsTree bodiesHeads) updVars
  clause mapTree



let terms =
  let rec helper acc =
    function
    | Add (x, y) -> helper (x :: acc) y
    | v -> v :: acc

  helper [] >> List.rev

let factors =
  let rec helper acc =
    function
    | Mul (x, y) -> helper (x :: acc) y
    | v -> v :: acc

  helper [] >> List.rev

// let factorsWithVars =
//   let tail =
//     function
//     | _ :: xs -> xs
//     | _ -> []
//
//   let rec helper acc =
//     function
//     | Ite (Eq (expr, _), then', else') -> helper (acc @ (terms expr |> tail) @ (terms else' |> tail)) then'
//     | Add _ as add -> acc @ (terms add |> tail)
//     | _ -> acc
//
//   function
//   | Def (_, _, e) -> helper [] e
//   | _ -> []

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
// |> List.toArray
// |> And
// |> Assert






let asfd () =
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

    helper [] >> List.toArray >> And

  // let notZeroConsts =
  // function
  // | Def (_, _, expr) ->
  // match expr with
  // | Add _ -> consts expr
  // | Ite (cond, ifExpr, elseExpr) ->

  let ite =
    Ite (
      Eq (Add (Apply ("c_4", []), Add (Mul (Apply ("c_5", []), Var "x"), Mul (Apply ("c_6", []), Var "y"))), Int 0L),
      Add (Apply ("c_1", []), Add (Mul (Apply ("c_2", []), Var "x"), Mul (Apply ("c_3", []), Var "y"))),
      Add (Apply ("c_7", []), Add (Mul (Apply ("c_8", []), Var "x"), Mul (Apply ("c_9", []), Var "y")))
    )

  let e =
    Add (Apply ("c_7", []), Add (Mul (Apply ("c_8", []), Var "x"), Mul (Apply ("c_9", []), Var "y")))

  let def =
    Def (
      "cons",
      [ "x"; "y" ],
      Ite (
        Eq (Add (Apply ("c_4", []), Add (Mul (Apply ("c_5", []), Var "x"), Mul (Apply ("c_6", []), Var "y"))), Int 0L),
        Add (Apply ("c_1", []), Add (Mul (Apply ("c_2", []), Var "x"), Mul (Apply ("c_3", []), Var "y"))),
        Add (Apply ("c_7", []), Add (Mul (Apply ("c_8", []), Var "x"), Mul (Apply ("c_9", []), Var "y")))
      )
    )

  // consts
  // (Add (Apply ("c_7", []),
  // Add
  // (Mul (Apply ("c_8", []), Var "x"), Mul (Apply ("c_9", []), Var "y")) ))
  // |> printfn "%O"
  notZeroFunConsts listDefFunsShiza |> printfn "%O"
  // notZeroConsts [def] |> printfn "%O"
  // (and (or (c_5 != 0) (c_6 != 0)) (or (c_2 != 0) (c_3 != 0)) (or (c_8 != 0) (c_9 != 0)))

  ()

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

let constNames from =
  function
  | Some expr ->
    expr
    |> terms
    |> List.length
    |> int64
    |> (fun d -> newConstNames from (from + d))
  | None -> []


// Add (Mul (Apply ("c_15", []), Var "y"),  Add (Mul (Apply ("c_14", []), Var "x"), Apply ("c_13", [])))))


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
       printfn $"{newConsts}"
       (newConsts, funDefs)

let asdsdf () =
  maxConstIndex shiza + 1L
  |> flip
       constNames
       (Some (Add (Apply ("c_7", []), Add (Mul (Apply ("c_8", []), Var "x"), Mul (Apply ("c_9", []), Var "y")))))
  |> fun constNames ->
       constNames
       |> List.tail
       |> List.zip [ "x"; "y" ]
       |> List.map (fun (n, c) -> Mul (Apply (c, []), Var n))
       |> fun terms ->
            List.foldBack
              (fun acc x -> Add (x, acc))
              (terms |> List.rev)
              (List.head constNames |> fun x -> Apply (x, []))
            |> ignore

  addBranch
    shiza
    (Def (
      "cons",
      [ "x"; "y" ],
      Ite (
        Eq (Add (Apply ("c_4", []), Add (Mul (Apply ("c_5", []), Var "x"), Mul (Apply ("c_6", []), Var "y"))), Int 0),
        Add (Apply ("c_1", []), Add (Mul (Apply ("c_2", []), Var "x"), Mul (Apply ("c_3", []), Var "y"))),
        Add (Apply ("c_7", []), Add (Mul (Apply ("c_8", []), Var "x"), Mul (Apply ("c_9", []), Var "y")))
      )
    ))
  // |> ignore
  |> fun (_, xs, y) ->
       printfn "%O" y

       for x in xs do
         printfn $"{x}"

  // branching shiza listDefFunsShiza
  // |> fun (cs, xs, ys) ->
  //     for c in cs do
  //       printfn $"{c}"
  //     for y in ys do
  //       printfn $"{y}"
  //     for x in xs do
  //       printfn $"{x}"
  //

  // addBranch shiza ((Array.ofList listDefFunsShiza)[1])
  // |> fun (_, _, x) -> printfn "%O" x

  ()

// let ite expr =
// expr
// expr


let decConsts = List.map decConst

let zeroOrOneValsOfVars =
  decConsts
  >> List.fold
       (fun acc ->
         function
         | DeclConst n -> Or [| Eq (Var n, Int 0); Eq (Var n, Int 1) |] :: acc
         | _ -> acc)
       []
  >> List.map Assert


let pushZeroOrOne (solver: Solver) env constDefs =
  solver.Push ()
  printfn $"{solver.NumScopes}"

  z3solve
    { env = env
      solver = solver
      unsat = fun env _ -> (env, [])
      sat = fun env solver -> (env, model env solver)
      cmds = zeroOrOneValsOfVars constDefs }

type Mode =
  | ZeroOnes
  | Any

  member x.isZeroOnes =
    match x with
    | ZeroOnes -> true
    | Any -> false



let rec learner (solver: Solver) env asserts constDefs constrDefs funDecls proof pushed (mode: Mode) =
  match proof with
  | [ Command (Proof (hyperProof, _, _)) ] ->
    printfn "%O" hyperProof
    let clause = hyperProof2clause constDefs funDecls hyperProof asserts

    printfn $"{clause}"
    printfn $"{expr2smtExpr clause}"

    printfn "SOLVING"

    File.AppendAllText (
      "/home/andrew/adt-solver/many-branches-search/dbg/redlog-input.smt2",
      $"{Redlog.redlogQuery (def2decVars constrDefs) clause}\n\n"
    )

    File.AppendAllText (
      "/home/andrew/adt-solver/many-branches-search/dbg/redlog-input.smt2",
      $"--------------------\n\n\n"
    )

    let redlogResult = redlog (def2decVars constrDefs) clause

    File.AppendAllText (
      "/home/andrew/adt-solver/many-branches-search/dbg/redlog-output.smt2",
      $"{program2originalCommand redlogResult}\n\n"
    )

    File.AppendAllText (
      "/home/andrew/adt-solver/many-branches-search/dbg/redlog-output.smt2",
      $"--------------------\n\n\n"
    )

    for v in List.map program2originalCommand ((constDefs |> List.map decConst) @ pushed @ [ redlogResult ]) do
      File.AppendAllText ("/home/andrew/adt-solver/many-branches-search/dbg/smt-input.smt2", $"{(v.ToString ())}\n\n")

    File.AppendAllText (
      "/home/andrew/adt-solver/many-branches-search/dbg/smt-input.smt2",
      $"--------------------\n\n\n"
    )

    let pushed' = pushed @ [ redlogResult ]
    printfn "<<<>>>><<>>>%O" <| solver.Assertions.Length

    solver.Push ()

    match
      z3solve
        { env = env
          solver = solver
          unsat = (fun env _ -> (env, []))
          sat = fun env solver -> (env, model env solver)
          cmds = [ redlogResult ] }
    with
    | SAT ((env', defConsts')) ->
      printfn "<<<>>>><<>>>%O" <| solver.Assertions.Length

      for v in List.rev defConsts' do
        printfn $"{v}"


      (env', defConsts', constrDefs, pushed', mode)
    | UNSAT ((env', _)) when mode.isZeroOnes ->

      printfn "<<<>>>><<>>>%O" <| solver.Assertions.Length

      solver.Pop 2u // rm coflict assert & zeroOnes restriction
      // printfn "<<<>>>><<>>>%O" <| solver.Check ()
      // printfn "<<<>>>><<>>>%O" <| solver.Model
      z3solve
        { env = env
          solver = solver
          unsat = (fun env _ -> (env, []))
          sat = fun env solver -> (env, model env solver)
          cmds = [] }
      |> function
        | SAT (env, model) ->
          // printfn "<<<>>>><<>>>%O" <| model
          (env, model, constrDefs, pushed', Any)
        | UNSAT (env, _) ->
          // (env, constDefs, funDefs, pushed', Any)
          failwith "?"


    // learner solver env asserts constDefs funDefs funDecls proof pushed' Any

    | UNSAT ((env, _)) ->
      // failwith "1234"
      for v in List.map program2originalCommand constrDefs do
        printfn "constrDef:: %O" v

      // for v in List.map program2originalCommand funDefs do
      // printfn "funDef:: %O" v

      let newConsts, constrDefs' = branching constDefs constrDefs
      printfn $"{constrDefs'}"

      solver.Pop () // rm conflict assert
      solver.Push ()

      let envDecConsts =
        z3solve
          { env = env
            solver = solver
            unsat = fun env _ -> env
            sat = fun env _ -> env
            cmds = (decConsts newConsts) @ (notZeroFunConsts constrDefs') }
        |> function
          | SAT env'
          | UNSAT env' -> env'

      pushZeroOrOne solver envDecConsts newConsts
      |> function
        // | SAT (env'', defConsts') -> (env'', defConsts', constrDefs, pushed', ZeroOnes)
        | SAT (env'', defConsts') -> (env'', defConsts', constrDefs', pushed', ZeroOnes)
        | _ ->
          failwith "?"
          (env, constDefs, constrDefs, pushed', ZeroOnes)


        // z3solve
        // { env = env
        // solver = solver
        // sat = fun env solver -> (env, model env solver)
        // unsat = fun env _ -> (env, [])
        // cmds = (decConsts newConsts) @ (notZeroFunConsts funDefs')
        // @ (newConsts |> zeroOrOne)
        // }
        // |> function
        // | SAT (env', constDefs'') ->
        // solver.Push ()
        // for v in vs do printfn "%O" v
        // let constDefs'' = vs |> Map.toList |> List.map (fun (n, i) -> Def (n, [], Int i))
        // solver.Push ()

        // (env', constDefs'', funDefs', pushed')
        // learner solver env' asserts constDefs'' funDefs' funDecls proof pushed' ZeroOne
        | _ -> failwith "1234"







// [ c = 0 or c = 1 ]
// если ансат то убрать и продолжить без этого
// до второго ансата и тогда ветвиться


// если смт солвер дает ансат на n-том ассерте,
let unsat env (solver: Solver) =
  let p = Parser.Parser false

  for d in env.ctxDecfuns.Values do
    p.ParseLine <| d.ToString ()

  match solver.Proof with
  | null ->
    failwith "OOO"
    []
  | _ ->
    p.ParseLine (
      solver.Proof.ToString ()
      |> proof
        // id
        (fun _ ->
          File.AppendAllText (
            "/home/andrew/adt-solver/many-branches-search/dbg/proof",
            $"{solver.Proof.ToString ()}\n\n"
          ))
      // (File.AppendAllText
      // ("/home/andrew/adt-solver/many-branches-search/dbg/proof.smt2", $"{solver.Proof.ToString ()}\n\n\n") ))
      |> fun prettyProof ->
           File.AppendAllText (
             "/home/andrew/adt-solver/many-branches-search/dbg/proof",
             $"PRETTY:\n{prettyProof.ToString ()}\n\n"
           )

           File.AppendAllText ("/home/andrew/adt-solver/many-branches-search/dbg/proof", $"--------------------\n\n\n")
           prettyProof |> sprintf "%s"
    )


// c0 +      c1 * x + c2 * y + c3 * z
// ADD(c0, ADD(c1 * x, ADD(c2 * y, c3 * z) ))




// for v in List.map (program2originalCommand) (notZeroConsts listDefFuns) do
//   File.AppendAllText ("/home/andrew/adt-solver/many-branches-search/dbg/no-zero-consts.smt2", $"{(v.ToString ())}\n")







// solverLearner.Assert (notZeroConsts listDefFuns)




let rec teacher funDefs solverLearner envLearner constDefs constrDefs funDecls (asserts: Program list) pushed mode =
  let envTeacher = emptyEnv [| ("proof", "true") |]
  let teacherSolver = envTeacher.ctxSlvr.MkSolver "HORN"
  teacherSolver.Set ("spacer.global", true)

  let cmds = (funDefs @ constDefs @ constrDefs @ funDecls @ asserts)

  for v in List.map program2originalCommand cmds do
    File.AppendAllText ("/home/andrew/adt-solver/many-branches-search/dbg/horn-input.smt2", $"{(v.ToString ())}\n\n")

  File.AppendAllText ("/home/andrew/adt-solver/many-branches-search/dbg/horn-input.smt2", $"--------------------\n\n\n")


  z3solve
    { env = envTeacher
      solver = teacherSolver
      unsat = unsat
      cmds = cmds
      sat = fun _ _ -> [] }
  |> function
    | SAT _ -> printfn "SAT"
    | UNSAT proof ->
      let envLearner', defConsts', defConstrs', pushed', mode =
        learner solverLearner envLearner asserts constDefs constrDefs funDecls proof pushed mode

      for v in List.map program2originalCommand defConstrs' do
        printfn $"{v}"

      teacher funDefs solverLearner envLearner' defConsts' defConstrs' funDecls asserts pushed' mode


let newLearner () =
  let envLearner = emptyEnv [| ("model", "true") |]
  let solverLearner = envLearner.ctxSlvr.MkSolver "NIA"
  envLearner, solverLearner




let solver funDefs constDefs constrDefs funDecls (asserts: Program list) =
  let envLearner, solverLearner = newLearner ()
  let decConsts = decConsts constDefs

  let startCmds =
    funDefs @ decConsts @ notZeroFunConsts constrDefs
    |> List.filter (function
      | (Assert (Or [||])) -> false
      | _ -> true)
  // @ [ Assert ( And
  // [|Eq (Var "c_0", Int 1)
  // Eq (Var "c_1", Int 1)
  // Eq (Var "c_2", Int 1)
  // Eq (Var "c_3", Int 1) |] ) ]

  // @ (notZeroFunConsts funDefs)
  // @ (constDefs |> zeroOrOne)
  // @
  // [ Assert ( And
  // [|Eq (Var "c_0", Int 1)
  // Eq (Var "c_1", Int 1)
  // Eq (Var "c_2", Int 1)
  // Eq (Var "c_3", Int 1) |] ) ]

  for v in List.map program2originalCommand startCmds do
    File.AppendAllText ("/home/andrew/adt-solver/many-branches-search/dbg/smt-input.smt2", $"{(v.ToString ())}\n\n")

  File.AppendAllText ("/home/andrew/adt-solver/many-branches-search/dbg/smt-input.smt2", $"--------------------\n\n\n")

  let envDecConsts =
    z3solve
      { env = envLearner
        solver = solverLearner
        unsat = fun env _ -> env
        sat = fun env _ -> env
        cmds = startCmds }
    |> function
      | SAT env'
      | UNSAT env' -> env'

  printfn "<<<>>>><<>>>%O" <| solverLearner.Assertions.Length

  pushZeroOrOne solverLearner envDecConsts constDefs
  |> function
    | SAT (env'', defConsts') ->
      printfn $"{defConsts'}"
      printfn "<<<>>>><<>>>%O" <| solverLearner.Assertions.Length

      for v in List.map program2originalCommand constrDefs do
        printfn "v111111 %O" v
      // teacher solverLearner env'' defConsts' funDefs funDecls asserts startCmds ZeroOne
      teacher funDefs solverLearner env'' defConsts' constrDefs funDecls asserts startCmds ZeroOnes
    | UNSAT _ -> failwith "?"
// teacher solverLearner envDecConsts constDefs funDefs funDecls asserts startCmds ZeroOnes


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
      | smtExpr.Apply (_, exprs) -> List.fold (fun acc x -> helper acc x) acc exprs
      | smtExpr.And exprs -> List.fold (fun acc x -> helper acc x) acc exprs
      | smtExpr.Or exprs -> List.fold (fun acc x -> helper acc x) acc exprs
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
    | Eq (expr1, expr2) -> Eq (helper expr1, helper expr1)
    | Lt (expr1, expr2) -> Lt (helper expr1, helper expr2)
    | Gt (expr1, expr2) -> Gt (helper expr1, helper expr2)
    | Le (expr1, expr2) -> Le (helper expr1, helper expr2)
    | Ge (expr1, expr2) -> Ge (helper expr1, helper expr2)
    | Mod (expr1, expr2) -> Mod (helper expr1, helper expr2)
    | Add (expr1, expr2) -> Add (helper expr1, helper expr2)
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

let run file =
  let defFuns, liaTypes, defConstants, declFuns, asserts = approximation file
  // for v in  linTypes do
  // printfn $"linType>>{origCommand2program v}"

  // printfn "defFuns>>>>"
  // for v in  defFuns do
  // printfn $"defFun: {origCommand2program v}"

  // for v in defConstants do
  // printfn $"{ v}"

  let funDecls = List.map origCommand2program declFuns
  // for v in declFuns do
  // printfn $"{origCommand2program v}"

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

  for v in asserts'' do
    printfn $"{v}"
  
  let toPrograms = List.map origCommand2program

  solver
    (toPrograms defFuns)
    defConstants
    (toPrograms liaTypes)
    funDecls
    asserts''




let afds () =
  let file = "/home/andrew/adt-solver/many-branches-search/run/false_graph_d5.smt2"

  // let file = "/home/andrew/adt-solver/many-branches-search/run/isaplanner_prop_16.smt2"

  // let file = "/home/andrew/adt-solver/many-branches-search/run/test.smt2"
  // let file = "/home/andrew/adt-solver/many-branches-search/benchmarks-search/CAV2022Orig(13)/repo/TIP-no-NAT/TIP.not-only-nat-constructors/isaplanner_prop_16.smt2"
  let defFuns, linTypes, defConstants, declFuns, asserts = approximation file

  for v in linTypes do
    printfn $"linType>>{origCommand2program v}"


  printfn "defFuns>>>>"

  for v in defFuns do
    printfn $"defFun: {origCommand2program v}"

  for v in defConstants do
    printfn $"{v}"

  let funDecls = List.map origCommand2program declFuns

  for v in declFuns do
    printfn $"{origCommand2program v}"

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
    (List.map
      (function
      | Program.Assert x -> apply2app appNames x |> Assert)
      asserts')

  for v in asserts'' do
    printfn $"{v}"


  solver
    (List.map origCommand2program defFuns)
    defConstants
    ((List.map origCommand2program linTypes))
    funDecls
    asserts''

  // let defFunctions, defConstants, decConstants, dataTypes, functions, asserts, skAsserts, notSkAsserts = Linearization.linearization file

  // pr/intfn "defFunctions"
  // for l in defFunctions do
  // printfn "%O" <| l
  //
  // printfn "defConstants"
  // for l in defConstants do
  //   printfn "%O" <| l
  //
  // printfn "decConstants"
  // for l in decConstants do
  //   printfn "%O" <| l
  //
  // printfn "dataTypes"
  // for l in dataTypes do
  // printfn "%O" <| l
  //
  // printfn "functions"
  // for l in functions do
  //   printfn "%O" <| l
  //
  // printfn "asserts"
  // for l in asserts do
  //   printfn "%O" <| l
  //
  // printfn "skAsserts"
  // for l in skAsserts do
  //   printfn "%O" <| l
  //
  // printfn "notSkAsserts"
  // for l in notSkAsserts do
  //   printfn "%O" <| l
  //

  ()





// solverLearner.Push ()
// z3solve
// { env = envLearner
// solver = solverLearner
// unsat = fun _ _ -> None
// sat = fun env solver -> Some (env, model env solver)
// cmds = startCmds  }
// |> function
// | SAT (Some (envLearner', vs)) ->
// let defConsts' = vs |> Map.toList |> List.map (fun (n, i) -> Def (n, [], Int i))
// teacher solverLearner envLearner' constDefs funDefs funDecls asserts cmds
// teacher solverLearner envLearner' defConsts' funDefs funDecls asserts startCmds
// | SAT _ | UNSAT _ ->  failwith "first push?"




// match proof with
// | [ Command (Proof (hyperProof, _, _)) ] ->
//   proofTree hyperProof
//   |> fun proofTree ->
// printfn "PROOF_TREE:\n%O" proofTree
// let progTree = assertsTree listAsserts listConst listDefFuns listDeclFuns proofTree
// let exprTree = exprTree progTree
// let updVars = updVars exprTree
// let bodyTree = appBody updVars
// let headTree = appHead updVars
// let bodiesHeads = Tree.zip bodyTree headTree
// let map = mapAppsTree bodiesHeads
//
// updVars |> printfn "\n.................\n%O\n\n"
// map |> printfn "\n\n%O\n\n"
// // let mapTree = Tree.zip map tree
// let mapTree = Tree.zip map updVars
// printfn "\n\n%O\n\n" mapTree
//
// // resolvent mapTree |> printfn "\n>>>>>>>>>>>>\n%O\n\n"
//
// let clause = clause mapTree
//
// printfn $"{clause}"
// printfn $"{program2originalCommand clause}"



// let envLearner, _, v =
//   eval_cmds envLearner (listDeclConst @ listDefFunsLearher @ [ clause ])
//
// learner.Add (v :?> BoolExpr)
//
// printfn "!!!\n%d" learner.Assertions.Length
//
// match learner.Check () with
// | Status.UNKNOWN -> printf "UNKNOWN"
// | Status.SATISFIABLE ->
//   printf "SATISFIABLE"
//   printfn "\n%s\n\n\n" <| v.ToString ()
// | Status.UNSATISFIABLE ->
//   printfn "\nOPOPOP"


//redlog
// | otherwise -> printfn "----------------->>%O" otherwise

// let uniqVars i vs =
//   List.fold
//     (fun (acc, i) v ->
//       vars v
//       |> List.fold (fun (acc, i) name -> (renameVar name $"var{i}" acc, i + 1)) (v, i)
//       |> fun (v, i) -> (v :: acc, i))
//     ([], i)
//     vs




let chck () =
  let run consts defFns decFns asserts =
    // for v in List.map (program2originalCommand) defFns do
    // File.AppendAllText ("/home/andrew/adt-solver/many-branches-search/dbg/def-funs.smt2", $"{(v.ToString ())}\n")


    // for v in List.map (decConst >> program2originalCommand) consts do
    // File.AppendAllText ("/home/andrew/adt-solver/many-branches-search/dbg/dec-consts.smt2", $"{(v.ToString ())}\n")

    // for v in List.map program2originalCommand decFns do
    // File.AppendAllText ("/home/andrew/adt-solver/many-branches-search/dbg/dec-funs.smt2", $"{(v.ToString ())}\n")


    // for v in List.map program2originalCommand asserts do
    // File.AppendAllText ("/home/andrew/adt-solver/many-branches-search/dbg/asserts.smt2", $"{(v.ToString ())}\n")

    solver [] consts defFns decFns asserts

  run listConst listDefFuns listDeclFuns [ listAssert1; listAssert2; listAssert3; listAssert4; listAssert5 ]
// run shiza listDefFunsShiza listDeclFuns [ listAssert1; listAssert2; listAssert3; listAssert4; listAssert5 ]
// run dConsts dDefFuns dDeclFuns [ dA2; dA1; dA3; dA4 ]

// solve listConst listDefFuns listDeclFuns [ listAssert1; listAssert2; listAssert3; listAssert4; listAssert5 ] []
// solve shiza listDefFunsShiza listDeclFuns [ listAssert1; listAssert2; listAssert3; listAssert4; listAssert5 ] []
// solve dConsts dDefFuns dDeclFuns [ dA2;dA1;     dA3; dA4 ] []







// let ppp () =
//   proof
//     @"(let ((a!1 (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
//              (! (=> (and (last B C)
//                          (app D A B)
//                          (last A E)
//                          (not (= E C))
//                          (not (= A (- 1))))
//                     (query!0 A B C D E))
//                 :weight 0)) )
//       (a!2 (asserted (forall ((A Int) (B Int) (C Int) (D Int))
//                        (! (let ((a!1 (and (last B C)
//                                           (= A (+ 1 (* 3 D) (* (- 2) B)))
//                                           (not (= B (- 1))))))
//                             (=> a!1 (last A C)))
//                           :weight 0)) ))
//       (a!3 (forall ((A Int) (B Int))
//              (! (=> (= A (+ 3 (* 3 B))) (last A B)) :weight 0)))
//       (a!4 (asserted (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int))
//                        (! (let ((a!1 (and (app D E F)
//                                           (= B (+ 1 (* 3 C) (* (- 2) D)))
//                                           (= A (+ 1 (* 3 C) (* (- 2) F))))))
//                             (=> a!1 (app B E A)))
//                           :weight 0))))
//       (a!5 ((_ hyper-res 0 0)
//              (asserted (forall ((A Int)) (! (app (- 1) A A) :weight 0)))
//              (app (- 1) 3 3))))
// (let ((a!6 ((_ hyper-res 0 0 0 1 0 2 0 3)
//              (asserted a!1)
//              ((_ hyper-res 0 0 0 1)
//                a!2
//                ((_ hyper-res 0 0) (asserted a!3) (last (- 3) (- 2)))
//                (last (- 2) (- 2)))
//              ((_ hyper-res 0 0 0 1) a!4 a!5 (app 6 3 (- 2)))
//              ((_ hyper-res 0 0) (asserted a!3) (last 3 0))
//              (query!0 3 (- 2) (- 2) 6 0))))
//   (mp ((_ hyper-res 0 0 0 1 0 2 0 3)
//              (asserted a!1)
//              ((_ hyper-res 0 0 0 1)
//                a!2
//                ((_ hyper-res 0 0) (asserted a!3) (last (- 3) (- 2)))
//                (last (- 2) (- 2)))
//              ((_ hyper-res 0 0 0 1) (asserted (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int))
//                        (! (let ((a!1 (and (app D E F)
//                                           (= B (+ 1 (* 3 C) (* (- 2) D)))
//                                           (= A (+ 1 (* 3 C) (* (- 2) F))))))
//                             (=> a!1 (app B E A)))
//                           :weight 0))) ((_ hyper-res 0 0)
//              (asserted (forall ((A Int)) (! (app (- 1) A A) :weight 0)))
//              (app (- 1) 3 3)) (app 6 3 (- 2)))
//              ((_ hyper-res 0 0) (asserted a!3) (last 3 0))
//              (query!0 3 (- 2) (- 2) 6 0))
//         (asserted (=> (query!0 3 (- 2) (- 2) 6 0) false)) false)))"
//   |> printf "%s"
//


let dfdss =
  Node (
    Implies (
      And
        [| App ("app", [| Var "xs5"; Var "ys5"; Var "zs5" |])
           App ("last", [| Var "ys5"; Var "n5" |])
           App ("last", [| Var "zs5"; Var "m5" |])
           Not (Eq (Var "ys5", Apply ("nil", [])))
           Not (Eq (Var "n5", Var "m5")) |],
      Bool false
    ),
    [ Node (
        Implies (
          And
            [| Not (Eq (Var "xs4", Apply ("nil", [])))
               App ("last", [| Var "xs4"; Var "n4" |]) |],
          App ("last", [| Apply ("cons", [ Var "x4"; Var "xs4" ]); Var "n4" |])
        ),
        []
      )
      Node (
        Implies (
          App ("app", [| Var "xs2"; Var "ys2"; Var "zs2" |]),
          App (
            "app",
            [| Apply ("cons", [ Var "x2"; Var "xs2" ])
               Var "ys2"
               Apply ("cons", [ Var "x2"; Var "zs2" ]) |]
          )
        ),
        []
      )
      Node (
        Implies (
          And
            [| Not (Eq (Var "xs4", Apply ("nil", [])))
               App ("last", [| Var "xs4"; Var "n4" |]) |],
          App ("last", [| Apply ("cons", [ Var "x4"; Var "xs4" ]); Var "n4" |])
        ),
        [ Node (
            Implies (
              And
                [| Not (Eq (Var "xs4", Apply ("nil", [])))
                   App ("last", [| Var "xs4"; Var "n4" |]) |],
              App ("last", [| Apply ("cons", [ Var "x4"; Var "xs4" ]); Var "n4" |])
            ),
            []
          ) ]
      ) ]
  )



//walk in expr and find apps, substitute and return updated expr
// let shiza: apps -> Expr -> Expr = _
// fun apps acc expr


// for each mapped :
//  Map most!!!!!!
// let _ =
//       (Map [
//          ("app",
//          [App
//          ("app",
//          [|Apply ("cons", [Var "x2"; Var "xs2"]); Var "ys2";
//          Apply ("cons", [Var "x2"; Var "zs2"])|])]);
//         ("last",
//          [App ("last", [|Apply ("cons", [Var "x4"; Var "xs4"]); Var "n4"|]);
//           App ("last", [|Apply ("cons", [Var "x4"; Var "xs4"]); Var "n4"|])])])
// let _ =
//     (Implies
//        (And
//           [|
//             App ("app", [|_; Var "ys5"; Var "zs5"|]);
//             App ("last", [|Var "ys5"; Var "n5"|]);
//             App ("last", [|Var "zs5"; Var "m5"|]);
//             Not (Eq (Var "ys5", Apply ("nil", []))); Not (Eq (Var "n5", Var "m5"))
//             |],
//         Bool false))
