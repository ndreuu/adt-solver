module Approximation

open Microsoft.FSharp.Collections
open Microsoft.Z3
open SMTLIB2.Parser
open SMTLIB2.Prelude
open Operation


module Linearization =
  let linearization file =
    let p = Parser(false)
    let commands = p.ParseFile file

    let plus =
      makeElementaryOperationFromSorts "+" [ IntSort; IntSort ] IntSort

    let mul =
      makeElementaryOperationFromSorts "*" [ IntSort; IntSort ] IntSort

    let constants pdng (xs: _ list) =
      let _, cnsts =
        List.fold
          (fun (i, acc) _ ->
            (i - 1,
             (sprintf "c_%s" <| (i + pdng + 1).ToString ())
             :: acc))
          (xs.Length - 1, [])
          xs

      cnsts

    let terms pdng args =
      List.map2
        (fun c (x, _) ->
          Apply (
            mul,
            [ Apply (UserDefinedOperation (sprintf "%s" c, [], IntSort), [])
              Ident (x, IntSort) ]
          ))
        (constants pdng args)
        args

    let sum pdng =
      function
      | [] -> Apply (UserDefinedOperation (sprintf "c_%s" <| pdng.ToString (), [], IntSort), [])
      | t :: ts ->
        Apply (
          plus,
          [ Apply (UserDefinedOperation (sprintf "c_%s" <| pdng.ToString (), [], IntSort), [])
            List.fold (fun acc x ->
                       // printfn ">>>>>>%O" x
                       Apply (plus, [ x; acc ])) t ts ]
        )

    let pdng_defs =
      fun cs pdng ->
        cs
        |> List.fold
             (fun (pd, acc) (name, _, (args: operation list)) ->
               (args.Length + pd + 1,
                Definition (
                  DefineFun (
                    name.ToString (),
                    List.map (fun arg -> (arg.ToString (), IntSort)) args,
                    IntSort,
                    sum pd
                    <| List.rev (terms pd (List.map (fun x -> (opName x, ())) args))
                  )
                )
                :: acc))
             (pdng, [])
    
    let padding, dataTypes =
      let pdng, defs =
        List.fold
          (fun (pdng, acc) x ->
            match x with
            | Command (DeclareDatatype (_, cs)) ->
              let pdng', def = pdng_defs cs pdng
              (pdng', def @ acc)
            | Command (DeclareDatatypes [ _, cs ]) ->
              let pdng', def = pdng_defs cs pdng
              (pdng', def @ acc)
            | Command (DeclareDatatypes _) -> failwith "???"
            | _ -> (pdng, acc))
          (0, [])
          commands

      (pdng, defs |> List.rev)

    let padding, functions =
      let padding, functions =
        List.fold
          (fun (pdng, acc as r) cmd ->
            match cmd with
            | Command (DeclareFun (name, sorts, _)) ->
              let _, args =
                sorts
                |> List.fold
                     (fun (i, acc) _ -> (i - 1, (sprintf "x_%s" <| i.ToString (), IntSort) :: acc))
                     (sorts.Length - 1, [])

              (pdng + args.Length + 1,
               Definition (DefineFun (name.ToString (), args, IntSort, sum pdng <| List.rev (terms pdng args)))
               :: acc)
            | _ -> r)
          (padding, [])
          commands

      (padding, functions |> List.rev)

    let asserts =
      let quantiInt =
        List.map (fun (name, _) -> name, IntSort) in

      let geq_op typ =
        Operation.makeElementaryRelationFromSorts ">=" [ typ; typ ]

      let eq_op typ =
        Operation.makeElementaryRelationFromSorts "=" [ typ; typ ]

      let rec helper smt =
        match smt with
        | Apply (UserDefinedOperation _, _) as app -> Apply (eq_op IntSort, [ app; Number 0 ])
        | And smtExprs -> And (smtExprs |> List.map (fun x -> helper x))
        | Or smtExprs -> Or (smtExprs |> List.map (fun x -> helper x))
        | Not smtExpr -> Not (helper smtExpr)
        | Hence (smtExpr1, smtExpr2) -> Hence (helper smtExpr1, helper smtExpr2)
        | QuantifierApplication (quantifier, smtExpr) ->
          QuantifierApplication (
            quantifier
            |> List.map (function
              | ForallQuantifier vars -> ForallQuantifier (quantiInt vars)
              | ExistsQuantifier vars -> ExistsQuantifier (quantiInt vars)
              | StableForallQuantifier vars -> StableForallQuantifier (quantiInt vars)),
            helper smtExpr
          )
        | _ -> smt

      commands
      |> List.fold
           (fun acc x ->
             match x with
             | Assert expr -> Assert (helper expr) :: acc
             | _ -> acc)
           []
      |> List.rev

    let asserts' =
      fun f ->
        asserts
        |> List.map (fun asrt ->
          match asrt with
          | Assert (QuantifierApplication (quantifiers, smtExpr)) ->
            (quantifiers
             |> List.fold
                  (fun acc x ->
                    match x with
                    | ForallQuantifier vars
                    | ExistsQuantifier vars
                    | StableForallQuantifier vars ->
                      acc
                      @ (vars
                         |> List.map (fun x -> Command (DeclareConst x))))
                  [],
             Assert (f smtExpr))
          | Assert expr -> ([], Assert (f expr))
          | _ -> ([], asrt))

    let skAsserts = asserts' Not

    let notSkAsserts = asserts' id

    let defConstants =
      (padding - 1)
      |> List.unfold (fun i -> if i >= 0 then Some (i, i - 1) else None)
      |> List.map (fun i -> Definition (DefineFun (sprintf "c_%s" <| i.ToString (), [], IntSort, Number 0)))
      |> List.rev

    let decConstants =
      (padding - 1)
      |> List.unfold (fun i -> if i >= 0 then Some (i, i - 1) else None)
      |> List.map (fun i -> Command (DeclareConst (sprintf "c_%s" <| i.ToString (), IntSort)))
      |> List.rev

    let defFunctions =
      commands |> List.filter (function | Definition (DefineFun _) -> true | _ -> false)
    
    // dataTypes
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())
    //
    // functions
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())
    //
    // asserts
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())
    //
    // defConstants
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())
    //
    // decConstants
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())
    //
    // skAsserts
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())

    (defFunctions, defConstants, decConstants, dataTypes, functions, asserts, skAsserts, notSkAsserts)


module Result =
  let (>>=) x f = Result.bind f x

  let ( *> ) x f = x >>= fun _ -> f
  let just = Result.Ok
  let error = Result.Error

module SolverDeprecated =
  open System.Collections.Generic
  open Result

  module Evaluation =
 
    module Solver =
      open Z3Interpreter.Interpreter
      open Z3Interpreter.AST

      type Status =
        | SAT of Map<Name, int64>
        | UNSAT

      let model =
        fun env (solver: Solver) push pop cmds ->
          cmds
          |> eval_cmds env
          |> fun (_, vars, v) ->
               push ()

               solver.Add (v :?> BoolExpr)

               match solver.Check () with
               | Status.SATISFIABLE ->
                 let map =
                   vars
                   |> List.fold
                        (fun acc (n, v) ->
                          (n,
                           solver.Model.Double (solver.Model.Eval (v, true))
                           |> int64)
                          :: acc)
                        []
                   |> Map

                 pop ()

                 SAT map
               | Status.UNSATISFIABLE ->
                 pop ()
                 UNSAT
               | _ ->
                 pop ()
                 UNSAT

      let constants =
        fun vs ->
          List.fold
            (fun (acc, i) v ->
              (Def (sprintf "c_%s" <| i.ToString (), [], Int v)
               :: acc,
               i + 1))
            ([], 0)
            vs
          |> fun (vs, _) -> vs |> List.rev

      let converse_defs =
        let rec to_var =
          function
          | Apply (n, _) -> Var n
          | Int _
          | Bool _
          | Var _ as v -> v
          | Eq (e1, e2) -> Eq (to_var e1, to_var e2)
          | Ge (e1, e2) -> Ge (to_var e1, to_var e2)
          | Add (e1, e2) -> Add (to_var e1, to_var e2)
          | Mul (e1, e2) -> Mul (to_var e1, to_var e2)
          | And es -> es |> Array.map (fun e -> to_var e) |> And
          | Not e -> to_var e |> Not
          | Implies (e1, e2) -> Implies (to_var e1, to_var e2)

        List.map (function
          | Def (n, args, e) -> Def (n, args, e |> to_var)
          | otherwise -> otherwise)

      let rec var_names =
        fun expr ->
          let rec helper =
            fun acc ->
              function
              | Apply (_, vs) -> List.fold helper acc vs
              | Int _
              | Bool _ -> acc
              | Var n -> acc |> Set.add n
              | Eq (e1, e2)
              | Ge (e1, e2)
              | Add (e1, e2)
              | Mul (e1, e2)
              | Implies (e1, e2) -> helper (helper acc e2) e1
              | And es -> es |> Array.fold helper acc
              | Not e -> helper acc e

          helper Set.empty expr

      let declares =
        fun expr -> var_names expr |> Set.toList |> declConsts

      let const_decls =
        List.unfold (fun i ->
          if i < 0 then
            None
          else
            Some (DeclIntConst (sprintf "c_%i" i), i - 1))

      let rec subst =
        fun map ->
          function
          | Int _
          | Bool _ as v -> v
          | Eq (e1, e2) -> Eq (subst map e1, subst map e2)
          | Ge (e1, e2) -> Ge (subst map e1, subst map e2)
          | Add (e1, e2) -> Add (subst map e1, subst map e2)
          | Mul (e1, e2) -> Mul (subst map e1, subst map e2)
          | And es -> es |> Array.map (fun e -> subst map e) |> And
          | Not e -> subst map e |> Not
          | Implies (e1, e2) -> Implies (subst map e1, subst map e2)
          | Var n -> map |> Map.find n |> Int
          | Apply (n, es) -> Apply (n, es |> List.map (fun e -> subst map e))


      let env_var =
        { ctxSlvr = new Context ([| ("model", "true") |] |> dict |> Dictionary)
          ctxVars = Map.empty
          ctxFuns = Map.empty
          ctxDecfuns = Map.empty }

      let env_const =
        { ctxSlvr = new Context ([| ("model", "true") |] |> dict |> Dictionary)
          ctxVars = Map.empty
          ctxFuns = Map.empty
          ctxDecfuns = Map.empty }

      let cnsts_cnt =
        List.fold
          (fun acc x ->
            match x with
            | Def (_, args, _) -> args |> List.length |> (+) <| acc + 1
            | _ -> acc)
          0

      let eval_consts =
        fun hard_defs ds (assrts: Expr list) ->
          let cs =
            cnsts_cnt ds
            |> List.unfold (function 0 -> None | i -> Some (int64 0, i - 1)) 
            |> constants
            
          let env_vars =
            { ctxSlvr = new Context ([| ("model", "true") |] |> dict |> Dictionary)
              ctxVars = Map.empty
              ctxFuns = Map.empty
              ctxDecfuns = Map.empty }

          let env_consts =
            { ctxSlvr = new Context ([| ("model", "true") |] |> dict |> Dictionary)
              ctxVars = Map.empty
              ctxFuns = Map.empty
              ctxDecfuns = Map.empty }

          let solver_vars =
            env_vars.ctxSlvr.MkSolver "LIA"

          let solver_consts =
            env_consts.ctxSlvr.MkSolver "NIA"

          let rec loop =
            fun cs ds assrt ->
              model
                env_vars
                solver_vars
                solver_vars.Push
                solver_vars.Pop
                (hard_defs @ cs
                 @ ds @ (declares assrt) @ [ assrt |> Not |> Assert ])
              |> function
                | SAT vs ->
                  let const_decls =
                    cs |> List.length |> (-) <| 1 |> const_decls

                  let assert' =
                    Assert (subst vs assrt) :: converse_defs ds
                    |> List.rev
                  
                  hard_defs @ const_decls @ assert'
                  |> model env_consts solver_consts solver_consts.Push id
                  |> function
                    | SAT vs ->
                      let constants =
                        vs
                        |> Map.fold (fun acc _ v -> v :: acc) []
                        |> List.rev
                        |> constants

                      loop constants ds assrt
                    | UNSAT -> error "Was started since constants"

                | UNSAT -> just cs


          let rec check =
            fun (cs: Program list) defs assrts f ->
              let env =
                { ctxSlvr = new Context ([| ("model", "true") |] |> dict |> Dictionary)
                  ctxVars = Map.empty
                  ctxFuns = Map.empty
                  ctxDecfuns = Map.empty }


              let solver = env.ctxSlvr.MkSolver "LIA"

              assrts
              |> List.map (fun assrt ->
                model
                  env
                  solver
                  solver.Push
                  solver.Pop
                  (hard_defs@ cs
                   @ defs
                     @ (declares assrt) @ [ assrt |> Not |> Assert ])
                |> function
                  | SAT _ ->
                    false
                  | UNSAT ->
                    true)
              |> List.fold (&&) true
              |> function
                | false -> f cs >>= fun cs -> check cs defs assrts f
                | true -> just cs

          (fun cs ->
            assrts
            |> List.fold (fun cs assrt -> cs >>= fun cs -> loop cs ds assrt) (just cs))
          |> check cs ds assrts

      open Linearization

      let assrt = function originalCommand.Assert (smtExpr.Not e) -> smtExpr2expr e

      let defs =
        let args = List.map fst
        List.map (function | Definition (DefineFun (symbol, args', _, smtExpr)) -> Def (symbol, args args', smtExpr2expr smtExpr))

      let run =
        fun path ->
          let hardDefs, _, _, dataTypes, functions, _, skAsserts, _ =
            linearization path
          eval_consts
          <| defs hardDefs
          <| defs (dataTypes@functions)
          <| List.map (snd >> assrt) (skAsserts |> List.rev)
          >>= fun cs ->
            cs
            |> List.fold (fun acc c -> sprintf "%s\n%O" acc c) ""
            |> just
      

  open Evaluation

  let defs = Solver.defs
  
  let run = Solver.run
  

module Solver =
  ()
