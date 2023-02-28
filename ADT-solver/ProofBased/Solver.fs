module ProofBased.Solver

open System
open System.Collections.Generic
open Microsoft.FSharp.Collections
open Microsoft.VisualStudio.TestPlatform.TestHost
open Microsoft.Z3
open SMTLIB2
open FParsec

open ProofBased.Utils
open Z3Interpreter.Interpreter
open Z3Interpreter.AST

let env_teacher =
  { ctxSlvr = new Context ([| ("proof", "true") |] |> dict |> Dictionary)
    ctxVars = Map.empty
    ctxFuns = Map.empty
    ctxDecfuns = Map.empty }

let teacher = env_teacher.ctxSlvr.MkSolver "HORN"

let defConstants =
  [ Def ("c_0", [], Int 0); Def ("c_1", [], Int 0); Def ("c_2", [], Int 0) ]

let defFuns =
  [ Def ("Z", [], Apply ("c_0", []))
    Def ("S", [ "x" ], Add (Apply ("c_1", []), Mul (Apply ("c_2", []), Var "x"))) ]

let declFuns = [ Decl ("diseqInt", 2) ]

let assert1 =
  [
    // DeclConst "x1"
    Assert (ForAll ([| "x1" |], App ("diseqInt", [| Apply ("Z", []); Apply ("S", [ Var "x1" ]) |]))) ]

let assert2 =
  [
    // DeclConst "x2"
    Assert (ForAll ([| "x2" |], App ("diseqInt", [| Apply ("S", [ Var "x2" ]); Apply ("Z", []) |]))) ]

let assert3 =
  [
    // DeclConst "x3"
    // DeclConst "y3"
    Assert (
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


let bb () =
  let c_0 = teacher.Context.MkInt 0
  let c_1 = teacher.Context.MkInt 1
  let c_2 = teacher.Context.MkInt 0

  let Z = c_0

  let S x =
    teacher.Context.MkAdd (c_1, teacher.Context.MkMul (c_2, x))

  let diseqInt =
    let sorts: Sort[] = [| env_teacher.ctxSlvr.IntSort; env_teacher.ctxSlvr.IntSort |]
    env_teacher.ctxSlvr.MkFuncDecl (env_teacher.ctxSlvr.MkSymbol "diseqInt", sorts, env_teacher.ctxSlvr.BoolSort)

  let x1 = teacher.Context.MkIntConst ("x1")

  let a1: BoolExpr =
    let vals: Microsoft.Z3.Expr[] = [| Z; S x1 |]
    teacher.Context.MkForall ([| x1 |], teacher.Context.MkApp (diseqInt, vals))


  let x2 = teacher.Context.MkIntConst ("x2")

  let a2: BoolExpr =
    let vals: Microsoft.Z3.Expr[] = [| S x2; Z |]
    teacher.Context.MkForall ([| x2 |], teacher.Context.MkApp (diseqInt, vals))


  let x3 = teacher.Context.MkIntConst ("x3")
  let y3 = teacher.Context.MkIntConst ("y3")

  let a3: BoolExpr =
    let vals1: Microsoft.Z3.Expr[] = [| x3; y3 |]
    let vals2: Microsoft.Z3.Expr[] = [| S x3; S y3 |]

    let body: BoolExpr = teacher.Context.MkApp (diseqInt, vals1) :?> BoolExpr
    let head: BoolExpr = teacher.Context.MkApp (diseqInt, vals2) :?> BoolExpr

    teacher.Context.MkForall ([| x3; y3 |], teacher.Context.MkImplies (body, head))

  let x4 = teacher.Context.MkIntConst ("x4")

  let a4: BoolExpr =
    let vals1: Microsoft.Z3.Expr[] = [| x4; x4 |]

    let body: BoolExpr = teacher.Context.MkApp (diseqInt, vals1) :?> BoolExpr
    let head: BoolExpr = teacher.Context.MkBool false

    teacher.Context.MkForall ([| x4 |], teacher.Context.MkImplies (body, head))

  teacher.Assert ([| a1; a2; a3; a4 |])

  for v in teacher.Assertions do
    printfn "%O" v

  match teacher.Check () with
  | Status.UNKNOWN -> printf "bbb"
  | Status.SATISFIABLE ->
    printf "bbb22222"
    printfn "sdf\n\n\n"
  | Status.UNSATISFIABLE -> printf "\n\n\n%O" <| (teacher.Proof.ToString () |> proof)





let listConst =
  [ Def ("c_0", [], Int 0)
    Def ("c_1", [], Int 0)
    Def ("c_2", [], Int 1)
    Def ("c_3", [], Int 0) ]


//
// let listDeclConst =
//   [ DeclConst ("c_0")
//     DeclConst ("c_1")
//     DeclConst ("c_2")
//     DeclConst ("c_3") ]
//
// let listDefFuns =
//   [ Def ("nil", [], Apply ("c_0", []))
//     Def (
//       "cons",
//       [ "x"; "y" ],
//       Add (Apply ("c_1", []), Add (Mul (Apply ("c_2", []), Var "x"), Mul (Apply ("c_3", []), Var "y")))
//     ) ]
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
// let listDeclFuns = [ Decl ("app", 3); Decl ("last", 2) ]
//
// let listAssert1 =
//   Assert (ForAll ([| "ys1" |], App ("app", [| Apply ("nil", []); Var "ys1"; Var "ys1" |])))
//
// let listAssert2 =
//   Assert (
//     ForAll (
//       [| "x2"; "xs2"; "ys2"; "zs2" |],
//       Implies (
//         App ("app", [| Var "xs2"; Var "ys2"; Var "zs2" |]),
//         App (
//           "app",
//           [| Apply ("cons", [ Var "x2"; Var "xs2" ])
//              Var "ys2"
//              Apply ("cons", [ Var "x2"; Var "zs2" ]) |]
//         )
//       )
//     )
//   )
//
// let listAssert3 =
//   Assert (ForAll ([| "x3" |], App ("last", [| Apply ("cons", [ Var "x3"; Apply ("nil", []) ]); Var "x3" |])))
//
// let listAssert4 =
//   Assert (
//     ForAll (
//       [| "xs4"; "n4"; "x4" |],
//       Implies (
//         And (
//           [| Not (Eq (Var "xs4", Apply ("nil", [])))
//              App ("last", [| Var "xs4"; Var "n4" |]) |]
//         ),
//         App ("last", [| Apply ("cons", [ Var "x4"; Var "xs4" ]); Var "n4" |])
//       )
//     )
//   )
//
// let listAssert5 =
//   Assert (
//     ForAll (
//       [| "ys5"; "zs5"; "m5"; "xs5"; "n5" |],
//       Implies (
//         And (
//           [| App ("app", [| Var "xs5"; Var "ys5"; Var "zs5" |])
//              App ("last", [| Var "ys5"; Var "n5" |])
//              App ("last", [| Var "zs5"; Var "m5" |])
//              Not (Eq (Var "ys5", Apply ("nil", [])))
//              Not (Eq (Var "n5", Var "m5")) |]
//         ),
//         Bool false
//       )
//     )
//   )



let dConsts =
    [ Def ("c_0", [], Int 0)
      Def ("c_1", [], Int 1)
      Def ("c_2", [], Int 0) ]

let dDefFuns =
  [ Def ("Z", [], Apply ("c_0", []))
    Def (
      "S",
      [ "x" ],
      Add (Apply ("c_1", []), Mul (Apply ("c_2", []), Var "x"))
    ) ]


let dDeclFuns = [ Decl ("diseqInt", 2) ]

let dA1 =
  Assert (ForAll ( [| "x1" |], App ("diseqInt", [| Apply ("Z", []); Apply ("S", [ Var "x1" ]) |])))

let dA2 =
  Assert (ForAll ( [| "x2" |], App ("diseqInt", [| Apply ("S", [ Var "x2" ]); Apply ("Z", []) |])))

let dA3 =
  Assert
    (ForAll ([| "x3"; "y3" |],
     Implies (
       App ("diseqInt", [| Var "x3"; Var "y3" |]),
       App ("diseqInt", [| Apply ("S", [ Var "x3"]); Apply ("S", [ Var "y3"]) |] )  )))

let dA4=
  Assert
    (ForAll ([| "x4" |],
     Implies (
       App ("diseqInt", [| Var "x4"; Var "x4" |]),
       Bool false )))
  

  
  

// let wtf =
  // Assert (Eq (Int 1, Int 4))

let emptyEnv () =
  { ctxSlvr = new Context ([| ("proof", "true") |] |> dict |> Dictionary)
    ctxVars = Map.empty
    ctxFuns = Map.empty
    ctxDecfuns = Map.empty }
// Microsoft.Z3.Global.SetParameter("asd", "true")
// let tststs = (emptyEnv ()).ctxSlvr.MkParams ()
// let () = tststs.Context.ProbeNames |> fun vs -> for v in vs do printfn "%O" v

type 'T tree = Node of 'T * 'T tree list

module Tree =
  let rec fmap f =
    function
    | Node (x, ts) -> Node (f x, List.map (fmap f) ts)

  let rec fmap2 f t1 t2 =
    match (t1, t2) with
    | Node (x1, ts1), Node (x2, ts2) -> Node (f x1 x2, List.map2 (fmap2 f) ts1 ts2)

  let zip t1 t2 = fmap2 (fun x y -> (x, y)) t1 t2

  let rec fold f a =
    function
    | Node (x, ts) -> f (List.fold (fun a y -> fold f a y) a ts) x

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
    | _ -> false)
  |> clarify

let axiomAsserts clarify asserts name =
  asserts
  |> List.filter (function
    | Assert (ForAll (_, App (n, _))) when n = name -> true
    | _ -> false)
  |> clarify

let queryAssert asserts =
  asserts
  |> List.filter (function
    | Assert (ForAll (_, Implies (_, Bool false))) -> true
    | _ -> false)
  |> List.head

let rec assertsTree asserts consts defs decs =
  let clarifyAxiom: Program list -> 'a =
    fun ps ->
      // let envClarifier = emptyEnv ()
      // let clarifier = envClarifier.ctxSlvr.MkSolver "HORN"

      List.head ps
    
  function
  | Node (Apply (name, _), []) -> name |> axiomAsserts List.head asserts |> (fun x -> Node (x, []))
  | Node (Apply (name, _), ts) ->
    name
    |> impliesAsserts List.head asserts
    |> fun x -> Node (x, ts |> List.map (assertsTree asserts consts defs decs))
  | Node (Bool false, ts) -> Node (queryAssert asserts, ts |> List.map (assertsTree asserts consts defs decs))
  | _ -> failwith "123"

let renameVar =
  let rec helper oldName newName =
    let helper' x = helper oldName newName x

    function
    | Var name when name = oldName -> Var newName
    | Eq (expr1, expr2) -> Eq (helper' expr1, helper' expr2)
    | Ge (expr1, expr2) -> Ge (helper' expr1, helper' expr2)
    | Add (expr1, expr2) -> Add (helper' expr1, helper' expr2)
    | Mul (expr1, expr2) -> Mul (helper' expr1, helper' expr2)
    | Implies (expr1, expr2) -> Implies (helper' expr1, helper' expr2)
    | And exprs -> And (Array.map helper' exprs)
    | Not expr -> Not (helper' expr)
    | Apply (name, exprs) -> Apply (name, exprs |> List.map helper')
    | ForAll (names, expr) -> ForAll (names |> Array.map (fun x -> if x = oldName then newName else x), helper' expr)
    | App (name, exprs) -> App ((if name = oldName then newName else name), exprs |> Array.map helper')
    | Ite (expr1, expr2, expr3) -> Ite (helper' expr1, helper' expr2, helper' expr3)
    | Int _
    | Bool _
    | Var _ as expr -> expr

  helper

let vars =
  let rec helper acc =
    function
    | Var name -> name :: acc
    | Ge (expr1, expr2)
    | Eq (expr1, expr2)
    | Add (expr1, expr2)
    | Mul (expr1, expr2)
    | Implies (expr1, expr2) -> helper (helper acc expr1) expr2
    | ForAll (_, expr)
    | Not expr -> helper acc expr
    | Ite (expr1, expr2, expr3) -> helper (helper (helper acc expr1) expr2) expr3
    | App (_, exprs)
    | And exprs -> Array.fold helper acc exprs
    | Apply (_, exprs) -> List.fold helper acc exprs
    | Int _
    | Bool _ -> acc

  helper []

let substituteVar =
  let rec helper name value =
    let helper' x = helper name value x

    let notAVar =
      function
      | Var _ -> false
      | _ -> true

    function
    // | Var n when n = name && notAVar value -> value
    | Var n when n = name -> value
    | Eq (expr1, expr2) -> Eq (helper' expr1, helper' expr2)
    | Ge (expr1, expr2) -> Ge (helper' expr1, helper' expr2)
    | Add (expr1, expr2) -> Add (helper' expr1, helper' expr2)
    | Mul (expr1, expr2) -> Mul (helper' expr1, helper' expr2)
    | Implies (expr1, expr2) -> Implies (helper' expr1, helper' expr2)
    | And exprs -> And (Array.map helper' exprs)
    | Not expr -> Not (helper' expr)
    | Apply (n, exprs) -> Apply (n, exprs |> List.map helper')
    | ForAll (ns, expr) -> ForAll (ns, helper' expr)
    | App (n, exprs) -> App (n, exprs |> Array.map helper')
    | Ite (expr1, expr2, expr3) -> Ite (helper' expr1, helper' expr2, helper' expr3)
    | Int _
    | Bool _
    | Var _ as expr -> expr

  helper





// let varNames = List.map (function Var n -> n | otherwise -> failwith $"Var expected {otherwise}")
let varNames exprs =
  let rec helper acc exprs =
    exprs
    |> List.fold
         (fun (acc) expr ->
           match expr with
           | Var n -> n :: acc
           | Apply (asd, args) -> failwith $"AHDFDHDF {asd}")
         acc

  helper [] exprs |> List.rev


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

let exprTree =
  Tree.fmap (function
    | Assert (ForAll (_, x)) -> x
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
      | Ge (expr1, expr2)
      | Add (expr1, expr2)
      | Mul (expr1, expr2) -> helper acc expr1 |> fun acc -> helper acc expr2
      | Implies (expr1, _) -> helper acc expr1
      | And exprs -> Array.fold helper acc exprs
      | Not expr
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
    | Ge (expr1, expr2)
    | Add (expr1, expr2)
    | Mul (expr1, expr2)
    | Implies (expr1, expr2) -> varNames (varNames acc expr1) expr2
    | ForAll (_, expr)
    | Not expr -> varNames acc expr
    | App (_, exprs)
    | And exprs -> Array.fold varNames acc exprs
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
    | Bool _ -> acc
    | Eq _
    | Ge _
    | Not _
    | Mul _ as c -> c :: acc
    | And exprs -> Array.fold helper acc exprs
    | ForAll (_, expr)
    | Implies (expr, _) -> helper acc expr

  helper []


let simplify = id

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
        | Ge (expr1, expr2)
        | Add (expr1, expr2)
        | Mul (expr1, expr2) -> (appArgs apps acc expr1) |> fun (acc, apps) -> appArgs apps acc expr2
        | And exprs -> Array.fold (fun (acc, apps) e -> appArgs apps acc e) (acc, apps) exprs
        | Not expr
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
    | Ge (expr1, expr2)
    | Add (expr1, expr2)
    | Implies (expr1, expr2)
    | Mul (expr1, expr2) -> helper (helper acc expr1) expr2
    | App (_, exprs)
    | And exprs -> Array.fold helper acc exprs
    | ForAll (_, expr)
    | Not expr -> helper acc expr
    | Var n -> acc |> Set.add n
    | Apply (_, exprs) -> List.fold helper acc exprs
    | Ite (expr1, expr2, expr3) -> List.fold helper acc [ expr1; expr2; expr3 ]

  helper Set.empty expr |> Set.toArray |> (fun ns -> ForAll (ns, expr))


let clause mapTree =
  Implies (resolvent mapTree, Bool false) |> forAll |> Assert



let solve listConst listDefFuns listDeclFuns (listAsserts: Program list) =
  let envTeacher = emptyEnv ()
  let teacher = envTeacher.ctxSlvr.MkSolver "HORN"
  // teacher.Set ("spacer.global", true)
  
  // let envClarifier = emptyEnv ()
  // let clarifier = envTeacher.ctxSlvr.MkSolver "HORN"
  // teacher.Set ("spacer.global", true)
  
  printfn "ASDSADADS<><><>\n\n"
  
  let env, _, v =
    listAsserts
    |> List.fold
         (fun _ assrt ->
           eval_cmds envTeacher (listConst @ listDefFuns @ listDeclFuns @ [ assrt ])
           |> fun (env, vars, v) ->
                teacher.Add (v :?> BoolExpr)
                (env, vars, v))
         (envTeacher, [], envTeacher.ctxSlvr.MkInt 0)

  printfn "\n\n\n%d\n\n\n" <| teacher.Assertions.Length

  
  
  
  let envLearner = emptyEnv ()
  let learner = envLearner.ctxSlvr.MkSolver "NIA"
  
  
  for v in teacher.Assertions do
    printfn "%O" <| v

  match teacher.Check () with
  | Status.UNKNOWN -> printf "UNKNOWN"
  | Status.SATISFIABLE ->
    printf "SATISFIABLE"
    printfn "\n%s\n\n\n" <| v.ToString ()
  | Status.UNSATISFIABLE ->
    let p = Parser.Parser false

    for d in env.ctxDecfuns.Values do
      p.ParseLine <| d.ToString ()

    let proof = p.ParseLine (teacher.Proof.ToString () |> proof |> sprintf "%s")
    printfn "%O" proof

    match proof with
    | [ Command (Proof (hyperProof, _, _)) ] ->
      proofTree hyperProof
      |> fun proofTree ->
           printfn "PROOF_TREE:\n%O" proofTree  
           let tree' = assertsTree listAsserts listConst listDefFuns listDeclFuns proofTree 
           let tree = exprTree tree' 
           // let bodyTree = appBody tree
           // let headTree = appHead tree
           // let bodiesHeads = Tree.zip bodyTree headTree
           // let map = mapAppsTree bodiesHeads
           // tree' |> printfn "\n\n%O\n\n"
           
           // printfn "%O" teacher.Context.
           printfn "..........."
           // printfn "%s" <| envTeacher.ctxSlvr..ToString ()
           printfn "%O" envTeacher.ctxSlvr.MkParams 
           printfn "%O" envTeacher.ctxSlvr.SimplifyParameterDescriptions

           
           let updVars = updVars tree
           let bodyTree = appBody updVars
           let headTree = appHead updVars
           let bodiesHeads = Tree.zip bodyTree headTree
           let map = mapAppsTree bodiesHeads

           updVars |> printfn "\n.................\n%O\n\n"
           map |> printfn "\n\n%O\n\n"
           // let mapTree = Tree.zip map tree
           let mapTree = Tree.zip map updVars
           printfn "\n\n%O\n\n" mapTree

           // resolvent mapTree |> printfn "\n>>>>>>>>>>>>\n%O\n\n"
           
           let clause = clause mapTree
           
           printfn $"{clause}"
           
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
    | otherwise -> printfn "----------------->>%O" otherwise

let uniqVars i vs =
  List.fold
    (fun (acc, i) v ->
      vars v
      |> List.fold (fun (acc, i) name -> (renameVar name $"var{i}" acc, i + 1)) (v, i)
      |> fun (v, i) -> (v :: acc, i))
    ([], i)
    vs




let chck () =
  // solve listConst listDefFuns listDeclFuns [ listAssert1; listAssert2; listAssert3; listAssert4; listAssert5 ]
  solve dConsts dDefFuns dDeclFuns [ dA2; dA1; dA3; dA4 ]
  










//
// let aa () =
//
//   eval_cmds env_teacher (listConst @ listDefFuns @ listDeclFuns @ [ listAssert1 ])
//   |> fun (env, vars, v) ->
//        teacher.Add (v :?> BoolExpr)
//
//        eval_cmds env_teacher (listConst @ listDefFuns @ listDeclFuns @ [ listAssert2 ])
//        |> fun (env, vars, v) -> teacher.Add (v :?> BoolExpr)
//
//        eval_cmds env_teacher (listConst @ listDefFuns @ listDeclFuns @ [ listAssert3 ])
//        |> fun (env, vars, v) -> teacher.Add (v :?> BoolExpr)
//
//        eval_cmds env_teacher (listConst @ listDefFuns @ listDeclFuns @ [ listAssert4 ])
//        |> fun (env, vars, v) -> teacher.Add (v :?> BoolExpr)
//
//        eval_cmds env_teacher (listConst @ listDefFuns @ listDeclFuns @ [ listAssert5 ])
//        |> fun (env, vars, v) -> teacher.Add (v :?> BoolExpr)
//
//
//        printfn "\n\n\n%d\n\n\n" <| teacher.Assertions.Length
//
//        for v in teacher.Assertions do
//          printfn "%O" <| v
//
//        let proofTree (HyperProof (_, hyperProofs, head) as hProof) =
//          let body (HyperProof (_, hyperProofs, _)) =
//            List.map
//              (function
//              | HyperProof (_, _, head) -> head)
//              hyperProofs
//            |> smtExpr.And
//
//          let rec helper acc (HyperProof (_, hyperProofs, head) as curProof) =
//            match hyperProofs with
//            | [] -> acc
//            | h :: tl ->
//              let layout = curProof |> body |> (fun body -> Hence (body, head))
//
//              helper (layout :: acc) h
//              |> (@) (tl |> List.fold (fun acc x -> (helper [] x) @ acc) [])
//
//          helper [] hProof
//
//
//
//        match teacher.Check () with
//        | Status.UNKNOWN -> printf "1111"
//        | Status.SATISFIABLE ->
//          printf "22222"
//          printfn "%s\n\n\n" <| v.ToString ()
//        | Status.UNSATISFIABLE ->
//          let p = Parser.Parser false
//
//          for d in env.ctxDecfuns.Values do
//            p.ParseLine <| d.ToString ()
//
//          match p.ParseLine (teacher.Proof.ToString () |> proof |> sprintf "%s") with
//          | [ Command (Proof (hyperProof, _, _)) ] -> proofTree hyperProof |> printfn "-----------------%O"
//          | otherwise -> printfn "----------------->>%O" otherwise

let test p str =
  match run p str with
  | Success (result, _, _) -> printfn "Success: %A" result
  | Failure (errorMsg, _, _) -> printfn "Failure: %s" errorMsg



let floatBetweenBrackets: Parser<'a, unit> =
  many skipAnyChar >>. pfloat .>> many skipAnyChar

let skipTo str p = skipNoneOf str |> many >>. p



type AST =
  | Letter of string
  | Int of int64

let ident: Parser<'a, unit> = regex @"([0-9]|[A-Za-z])+"

let opArgs: Parser<_, unit> = ident |> sepBy <| skipChar ' '

let op name =
  pstring $"({name} " .>>. opArgs .>> pstring ")"

let findOps =
  anyChar |> manyCharsTill <| skipString "(+ " >>. opArgs .>> pstring ")"

let correctOps str =
  match run (many findOps) str with
  | Success (result, _, _) -> printfn "Success: %A" result
  | Failure (errorMsg, _, _) -> printfn "Failure: %s" errorMsg

let ppp () =
  proof
    @"(let ((a!1 (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
             (! (=> (and (last B C)
                         (app D A B)
                         (last A E)
                         (not (= E C))
                         (not (= A (- 1))))
                    (query!0 A B C D E))
                :weight 0)) )
      (a!2 (asserted (forall ((A Int) (B Int) (C Int) (D Int))
                       (! (let ((a!1 (and (last B C)
                                          (= A (+ 1 (* 3 D) (* (- 2) B)))
                                          (not (= B (- 1))))))
                            (=> a!1 (last A C)))
                          :weight 0)) ))
      (a!3 (forall ((A Int) (B Int))
             (! (=> (= A (+ 3 (* 3 B))) (last A B)) :weight 0)))
      (a!4 (asserted (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int))
                       (! (let ((a!1 (and (app D E F)
                                          (= B (+ 1 (* 3 C) (* (- 2) D)))
                                          (= A (+ 1 (* 3 C) (* (- 2) F))))))
                            (=> a!1 (app B E A)))
                          :weight 0))))
      (a!5 ((_ hyper-res 0 0)
             (asserted (forall ((A Int)) (! (app (- 1) A A) :weight 0)))
             (app (- 1) 3 3))))
(let ((a!6 ((_ hyper-res 0 0 0 1 0 2 0 3)
             (asserted a!1)
             ((_ hyper-res 0 0 0 1)
               a!2
               ((_ hyper-res 0 0) (asserted a!3) (last (- 3) (- 2)))
               (last (- 2) (- 2)))
             ((_ hyper-res 0 0 0 1) a!4 a!5 (app 6 3 (- 2)))
             ((_ hyper-res 0 0) (asserted a!3) (last 3 0))
             (query!0 3 (- 2) (- 2) 6 0))))
  (mp ((_ hyper-res 0 0 0 1 0 2 0 3)
             (asserted a!1)
             ((_ hyper-res 0 0 0 1)
               a!2
               ((_ hyper-res 0 0) (asserted a!3) (last (- 3) (- 2)))
               (last (- 2) (- 2)))
             ((_ hyper-res 0 0 0 1) (asserted (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int))
                       (! (let ((a!1 (and (app D E F)
                                          (= B (+ 1 (* 3 C) (* (- 2) D)))
                                          (= A (+ 1 (* 3 C) (* (- 2) F))))))
                            (=> a!1 (app B E A)))
                          :weight 0))) ((_ hyper-res 0 0)
             (asserted (forall ((A Int)) (! (app (- 1) A A) :weight 0)))
             (app (- 1) 3 3)) (app 6 3 (- 2)))
             ((_ hyper-res 0 0) (asserted a!3) (last 3 0))
             (query!0 3 (- 2) (- 2) 6 0)) 
        (asserted (=> (query!0 3 (- 2) (- 2) 6 0) false)) false)))"
  |> printf "%s"



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
