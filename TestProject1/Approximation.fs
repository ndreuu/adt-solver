module Approximation

open System
open Microsoft.FSharp.Collections
open Microsoft.VisualBasic.CompilerServices
open Microsoft.Z3
open NUnit.Framework
open SMTLIB2.Parser
open SMTLIB2.Prelude
open Operation
open SMTLIB2.Operations



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

      // equal_op
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

    ////// WRONG FOR EXIST QUANTIFIER
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
  // Result.t

  let (>>=) x f = Result.bind f x

  let ( *> ) x f = x >>= fun _ -> f
  let pure = Result.Ok
  let error = Result.Error

module SolverDeprecated =
  open System.Collections.Generic
  open Result

  module Evaluation =
    module AST =
      type Name = string

      type Expr =
        | Int of int64
        | Bool of bool
        | Eq of Expr * Expr
        | Ge of Expr * Expr
        | Add of Expr * Expr
        | Mul of Expr * Expr
        | And of Expr array
        | Not of Expr
        | Implies of Expr * Expr
        | Var of Name
        | Apply of Name * Expr list

      type Definition = Name * Name list * Expr

      type VarCtx = Map<Name, Microsoft.Z3.Expr>

      type FunCtx = Map<Name, Function>

      and Env =
        { ctx_slvr: Context
          ctx_vars: VarCtx
          ctx_funs: FunCtx }

      and Function = Name list * Expr

      type Program =
        | Def of Definition
        | Declare of Name
        | Assert of Expr

    open AST

    module Interpreter =
      let update =
        fun k v map ->
          Map.containsKey k map
          |> function
            | true -> Map.remove k map |> Map.add k v
            | false -> Map.add k v map

      let define =
        fun env (name, args, expr) -> env.ctx_funs.Add (name, (args, expr))

      let declare = List.map Declare

      let rec eval_expr: Env -> Expr -> Microsoft.Z3.Expr =
        fun env ->
          function
          | Int x -> env.ctx_slvr.MkInt x
          | Bool x -> env.ctx_slvr.MkBool x
          | Eq (expr1, expr2) -> env.ctx_slvr.MkEq (eval_expr env expr1, eval_expr env expr2)
          | Ge (expr1, expr2) -> env.ctx_slvr.MkGe (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
          | Add (expr1, expr2) ->
            env.ctx_slvr.MkAdd (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
          | Mul (expr1, expr2) ->
            env.ctx_slvr.MkMul (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
          | And exprs ->
            exprs
            |> Array.map (fun x -> eval_expr env x :?> BoolExpr)
            |> fun x -> env.ctx_slvr.MkAnd x
          | Not expr -> env.ctx_slvr.MkNot (eval_expr env expr :?> BoolExpr)
          | Implies (expr1, expr2) ->
            env.ctx_slvr.MkImplies (eval_expr env expr1 :?> BoolExpr, eval_expr env expr2 :?> BoolExpr)
          | Var x -> env.ctx_vars |> Map.find x

          | Apply (n, vs) ->
            let args, body = env.ctx_funs |> Map.find n
            let bindings = List.zip args vs

            let ctx_vars =
              bindings
              |> List.fold (fun acc (arg, v) -> acc |> update arg (eval_expr env v)) env.ctx_vars

            eval_expr { env with ctx_vars = ctx_vars } body

      let eval_cmds =
        fun env ->
          List.fold
            (fun (env, var_map, expr) cmd ->
              match cmd with
              | Declare n ->
                let int_const = env.ctx_slvr.MkIntConst n

                ({ env with ctx_vars = env.ctx_vars |> Map.add n int_const }, (n, int_const) :: var_map, expr)
              | Assert e -> (env, var_map, eval_expr env e)
              | Def d -> ({ env with ctx_funs = define env d }, var_map, expr))
            (env, [], env.ctx_slvr.MkInt 0)

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
                 // printfn "SAT"

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
                 // printfn "UNSAT"
                 pop ()
                 UNSAT
               | _ ->
                 // printfn "UNKNOWN"
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
        fun expr -> var_names expr |> Set.toList |> declare

      let const_decls =
        List.unfold (fun i ->
          if i < 0 then
            None
          else
            Some (Declare (sprintf "c_%i" i), i - 1))

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
        { ctx_slvr = new Context ([| ("model", "true") |] |> dict |> Dictionary)
          ctx_vars = Map.empty
          ctx_funs = Map.empty }

      let env_const =
        { ctx_slvr = new Context ([| ("model", "true") |] |> dict |> Dictionary)
          ctx_vars = Map.empty
          ctx_funs = Map.empty }

      let cnts = constants [ 0; 0; 0; 0 ]
      
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
            { ctx_slvr = new Context ([| ("model", "true") |] |> dict |> Dictionary)
              ctx_vars = Map.empty
              ctx_funs = Map.empty }

          let env_consts =
            { ctx_slvr = new Context ([| ("model", "true") |] |> dict |> Dictionary)
              ctx_vars = Map.empty
              ctx_funs = Map.empty }

          let solver_vars =
            env_vars.ctx_slvr.MkSolver "LIA"

          let solver_consts =
            env_consts.ctx_slvr.MkSolver "NIA"

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
                  // for v in vs do
                    // printfn "%O" v

                  let const_decls =
                    cs |> List.length |> (-) <| 1 |> const_decls

                  let assert' =
                    Assert (subst vs assrt) :: converse_defs ds
                    |> List.rev
                  
                  // for v in ds do printfn "%O" v
                  // printfn "______________SsdfDF________"
                  // for v in assert' do printfn "%O" v
                  // printfn ""
                  
                  hard_defs @ const_decls @ assert'
                  |> model env_consts solver_consts solver_consts.Push id
                  |> function
                    | SAT vs ->
                      // for v in vs do
                        // printfn "%O" v

                      let constants =
                        vs
                        |> Map.fold (fun acc _ v -> v :: acc) []
                        |> List.rev
                        |> constants

                      loop constants ds assrt
                    | UNSAT -> error "Was started since constants"

                | UNSAT -> pure cs


          let rec check =
            fun (cs: Program list) defs assrts f ->
              let env =
                { ctx_slvr = new Context ([| ("model", "true") |] |> dict |> Dictionary)
                  ctx_vars = Map.empty
                  ctx_funs = Map.empty }

              let solver = env.ctx_slvr.MkSolver "LIA"

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
                    // printfn "SAT"
                    false
                  | UNSAT ->
                    // printfn "UNSAT"
                    true)
              |> List.fold (&&) true
              |> function
                | false -> f cs >>= fun cs -> check cs defs assrts f
                // | false -> check (f cs) defs assrts f
                | true -> pure cs

          (fun cs ->
            assrts
            |> List.fold (fun cs assrt -> cs >>= fun cs -> loop cs ds assrt) (pure cs))
            // |> List.fold (fun cs assrt ->  loop cs ds assrt) ( cs))
          |> check cs ds assrts

      open Linearization

      // let defConstants, decConstants, dataTypes, functions, asserts, skAsserts, notSkAsserts =
      //   // linearization "/home/andrew/Downloads/CAV2022Orig(3)/TIP.Original.Linear/isaplanner_prop_23.smt2"
      //   linearization "/home/andrew/sys/len.orig.smt2"


      let rec expr =
        function
        | Number i -> Int i
        | BoolConst b -> Bool b
        | Ident (ident, _) -> Var ident
        | smtExpr.Apply (operation, exprs) ->
          match operation, exprs with
          | ElementaryOperation (ident, _, _), [e1; e2] when ident = "+" -> Add (expr e1, expr e2)
          | ElementaryOperation (ident, _, _), [e1; e2] when ident = "*" -> Mul (expr e1, expr e2)
          | ElementaryOperation (ident, _, _), [e1; e2] when ident = "=" -> Eq (expr e1, expr e2)
          | ElementaryOperation (ident, _, _), [e1; e2] when ident = ">=" -> Ge (expr e1, expr e2)
          | ElementaryOperation (ident, _, _), es
          | UserDefinedOperation (ident, _, _), es -> Apply (ident, es |> List.map expr)
        | smtExpr.And e -> e |> List.toArray |> Array.map expr |> And
        | smtExpr.Not e -> expr e |> Not
        | Hence (e1, e2) -> Implies (expr e1, expr e2)
        // | Or smtExprs -> smtExprs |> List.toArray |> Array.map expr |> Or
        // | _ -> failwith "AAAA"
      // | Let of (sorted_var * smtExpr) list * smtExpr
      // | Match of smtExpr * (smtExpr * smtExpr) list
      // | Ite of smtExpr * smtExpr * smtExpr
      // | QuantifierApplication of quantifiers * smtExpr
      let assrt = function originalCommand.Assert (smtExpr.Not e) -> expr e

      //////////////////////////////////////////////////////////////////
      let defs =
        let args = List.map fst
        List.map (function | Definition (DefineFun (symbol, args', _, smtExpr)) -> Def (symbol, args args', expr smtExpr))
      // 0
      //////////////////////////////////////////////////////////////////

      // match dataTypes |> List.head with
      // | Assert

      let f_defs =
        [ Def ("nil_0", [], Apply ("c_0", []))
          Def (
            "cons_0",
            [ "car_0"; "cdr_0" ],
            Add (Apply ("c_1", []), Add (Mul (Apply ("c_2", []), Var "car_0"), Mul (Apply ("c_3", []), Var "cdr_0")))
          ) ]

      let f_defs1 =
        [ Def ("nil_0", [], Apply ("c_0", []))
          Def (
            "cons_0",
            [ "car_0"; "cdr_0" ],
            Add (Apply ("c_1", []), Add (Mul (Apply ("c_2", []), Var "car_0"), Mul (Apply ("c_3", []), Var "cdr_0")))
          )
          Def (
            "len_0",
            [ "x_0"; "x_1" ],
            Add (Apply ("c_4", []), Add (Mul (Apply ("c_5", []), Var "x_0"), Mul (Apply ("c_6", []), Var "x_1")))
          ) ]


      let assert1 =
        Implies (
          Eq (Apply ("len_0", [ Var "xs_01"; Var "n_01" ]), Int 0),
          Eq (
            Apply (
              "len_0",
              [ Apply ("cons_0", [ Var "x_01"; Var "xs_01" ])
                Add (Var "n_01", Int 1) ]
            ),
            Int 0
          )
        )

      let assert2 =
        Implies (
          And [| Eq (Apply ("len_0", [ Var "xs_2"; Var "x_2" ]), Int 0)
                 Eq (
                   Apply (
                     "len_0",
                     [ Apply ("cons_0", [ Var "y_2"; Var "xs_2" ])
                       Var "z_2" ]
                   ),
                   Int 0
                 )
                 Eq (Var "x_2", Var "z_2") |],
          Bool false
        )

      let assert3 =
        Eq (Apply ("len", [ Apply ("nil", []); Int 0 ]), Int 0)

      
      let assert11 =
        Implies (
          Eq (Apply ("len", [ Var "xs"; Var "n" ]), Int 0),
          Eq (
            Apply (
              "len",
              [ Apply ("cons", [ Var "x"; Var "xs" ])
                Add (Var "n", Int 1) ]
            ),
            Int 0
          )
        )

      let assert22 =
        Implies (
          And [| Eq (Apply ("len", [ Var "xs"; Var "x" ]), Int 0)
                 Eq (
                   Apply (
                     "len",
                     [ Apply ("cons", [ Var "y"; Var "xs" ])
                       Var "z" ]
                   ),
                   Int 0
                 )
                 Eq (Var "x", Var "z") |],
          Bool false
        )

      let assert33 =
        Eq (Apply ("len", [ Apply ("nil", []); Int 0 ]), Int 0)

      
      let cur_assert =
        Implies (
          And [| Eq (Var "cdr_1", Var "x")
                 Eq (Apply ("cons_0", [ Var "car_1"; Var "cdr_1" ]), Var "z")
                 Eq (Var "x", Var "z") |],
          Bool false
        )

      let assert_with_end =
        Implies (Eq (Var "cdr_1", Var "n"), Eq (Apply ("cons_0", [ Var "car_1"; Var "cdr_1" ]), Add (Var "n", Int 1)))

      let assert_f_vars =
        declare [ "car_1"; "cdr_1"; "x"; "z" ]
        @ [ cur_assert |> Not |> Assert ]

      let cmds = f_defs @ assert_f_vars

      let run =
        fun path ->
          let defFuns, _, _, dataTypes, functions, _, skAsserts, _ =
            linearization path
          eval_consts
          <| defs defFuns
          <| defs (dataTypes@functions)
          <| List.map (snd >> assrt) skAsserts
          >>= fun cs ->
            cs
            |> List.fold (fun acc c -> sprintf "%s\n%O" acc c) ""
            |> pure
      
      let test_eval () =
        let defFuns, defConstants, decConstants, dataTypes, functions, asserts, skAsserts, notSkAsserts =
          linearization "/home/andrew/adt-solver/d/versions/41010/len.smt2"
        eval_consts
        <| defs defFuns
        <| defs (dataTypes@functions)
        <| List.map (snd >> assrt) skAsserts
        >>= fun cs ->
          for c in cs do
            printfn "%O" c
          pure ()
    
      let test_defs () =
        let defFuns, defConstants, decConstants, dataTypes, functions, asserts, skAsserts, notSkAsserts =
          linearization "/home/andrew/adt-solver/d/versions/41010/isaplanner_prop_16.smt2"
        
        for v in defs defFuns do
          printfn "%O" v
        
  open Evaluation

  let ttt = Interpreter.test_eval 

  let defs = Interpreter.defs
  
  let run = Interpreter.run
  

module Solver =
  ()
