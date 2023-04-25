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
    | App (name, exprs) -> App ((if name = oldName then newName else name), exprs |> List.map this)
    | Ite (expr1, expr2, expr3) -> Ite (this expr1, this expr2, this expr3)
    | expr -> expr

  helper

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

let redlog definitions formula =
  match Redlog.runRedlog definitions formula with
  | Ok v -> Assert(smtExpr2expr' v)
  | Error e -> failwith $"redlog-output: {e}"

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
    Node (queryAssert (List.head >> List.singleton) asserts, ts |> List.map (assertsTreeNew asserts consts decs))
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


let hyperProof2clauseNew defConsts constrDefs decFuns hyperProof asserts =
  proofTree hyperProof
  |> assertsTreeNew asserts defConsts decFuns
  |> treeOfExprs
  |> uniqVarNames
  |> resolvent
  |> Expr.And

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
        $"{prettyProof}" 
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
    | SAT _ -> "SAT"
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
    let rec helper = function
      | smtExpr.Apply (ElementaryOperation (ident, _, _), _)
      | smtExpr.Apply (UserDefinedOperation (ident, _, _), _) when ident.Contains "c_" -> [Def (ident, [], Int 0)]
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
    | Apply (name, exprs) when appNames |> List.contains name -> App (name, List.map helper exprs)
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
    |> List.choose (function Decl (n, _) -> Some n | _ -> None)

  let asserts'' =
    asserts' |> List.choose (function Assert x -> Some (Assert (apply2app appNames x)) | _ -> None)
  let toPrograms = List.map origCommand2program

  solver (toPrograms defFuns) defConstants (toPrograms liaTypes) funDecls asserts''
