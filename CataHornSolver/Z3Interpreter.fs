module Z3Interpreter

open System.Collections.Generic
open Microsoft.FSharp.Collections
open Microsoft.Z3
open ProofBased
open SMTLIB2.Prelude
open SMTLIB2
open Utils.IntOps

module AST =
  type Name = string

  type ArgsNum = int

  type Expr =
    | Int of int64
    | Bool of bool
    | Eq of Expr * Expr
    | Lt of Expr * Expr
    | Gt of Expr * Expr
    | Le of Expr * Expr
    | Ge of Expr * Expr
    | Mod of Expr * Expr
    | Add of Expr * Expr
    | Subtract of Expr * Expr
    | Neg of Expr
    | Mul of Expr * Expr
    | And of Expr array
    | Or of Expr array
    | Not of Expr
    | Implies of Expr * Expr
    | Var of Name
    | Apply of Name * Expr list
    | ForAll of Name array * Expr
    | App of Name * Expr array
    | Ite of Expr * Expr * Expr

  let rec expr2smtExpr =
    function
    | Int i -> Number i
    | Bool b -> BoolConst b
    | Eq (expr1, expr2) -> smtExpr.Apply (eqOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Gt (expr1, expr2) -> smtExpr.Apply (grOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Lt (expr1, expr2) -> smtExpr.Apply (lsOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Le (expr1, expr2) -> smtExpr.Apply (leqOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Ge (expr1, expr2) -> smtExpr.Apply (geqOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Add (expr1, expr2) -> smtExpr.Apply (addOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Subtract (expr1, expr2) -> smtExpr.Apply (minusOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Neg expr -> smtExpr.Apply (negOp, [ expr2smtExpr expr ])
    | Mod (expr1, expr2) -> smtExpr.Apply (modOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Mul (expr1, expr2) -> smtExpr.Apply (mulOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | And exprs -> Array.map expr2smtExpr exprs |> Array.toList |> smtExpr.And
    | Or exprs -> Array.map expr2smtExpr exprs |> Array.toList |> smtExpr.Or
    | Not expr -> expr2smtExpr expr |> smtExpr.Not
    | Implies (expr1, expr2) -> Hence (expr2smtExpr expr1, expr2smtExpr expr2)
    | Var n -> Ident (n, IntSort)
    | App (n, exprs) ->
      smtExpr.Apply (UserDefinedOperation (n, [], IntSort), Array.map expr2smtExpr exprs |> Array.toList)
    | Apply (n, exprs) -> smtExpr.Apply (UserDefinedOperation (n, [], IntSort), List.map expr2smtExpr exprs)
    | ForAll (names, e) ->
      QuantifierApplication (
        [ names |> Array.map (fun n -> (n, IntSort)) |> Array.toList |> ForallQuantifier ],
        expr2smtExpr e
      )
    | Ite (expr1, expr2, expr3) -> smtExpr.Ite (expr2smtExpr expr1, expr2smtExpr expr2, expr2smtExpr expr3)

  type Definition = Name * Name list * Expr

  type VarCtx = Map<Name, Microsoft.Z3.Expr>
  type DecFunsCtx = Map<Name, FuncDecl>

  type FunCtx = Map<Name, Function>

  and Env =
    { ctxSlvr: Context
      ctxVars: VarCtx
      ctxFuns: FunCtx
      ctxDecfuns: DecFunsCtx
      actives: Name list }

  and Function = Name list * Expr

  let newEnv args =
    { ctxSlvr = new Context (args |> dict |> Dictionary)
      ctxVars = Map.empty
      ctxFuns = Map.empty
      ctxDecfuns = Map.empty
      actives = [] }


  type Type =
    | Boolean
    | Integer

  type Program =
    | Def of Definition
    | DeclIntConst of Name
    | DeclConst of Name * Type
    | Decl of Name * ArgsNum
    | Assert of Expr

  let program2originalCommand =
    function
    | Def (n, ns, e) ->
      originalCommand.Definition (DefineFun (n, List.map (fun n -> (n, IntSort)) ns, IntSort, expr2smtExpr e))
    | DeclIntConst n -> originalCommand.Command (command.DeclareConst (n, IntSort))
    | DeclConst (n, t) ->
      let t' =
        match t with
        | Integer -> IntSort
        | Boolean -> BoolSort

      originalCommand.Command (command.DeclareConst (n, t'))
    | Decl (n, num) ->
      let args =
        List.unfold (fun state ->
          if state = 0 then
            None
          else
            Some (IntSort, state - 1))

      Command (DeclareFun (n, args num, BoolSort))
    | Assert e -> originalCommand.Assert (expr2smtExpr e)

  let rec smtExpr2expr =
    function
    | Number i -> Int i
    | BoolConst b -> Bool b
    | Ident (ident, _) -> Var ident
    | smtExpr.Apply (operation, exprs) ->
      match operation, exprs with
      | UserDefinedOperation (ident, _, _), [ e1; e2 ] when ident = "mod" -> Mod (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "+" -> Add (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "-" -> Subtract (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), [ e ] when ident = "-" -> Neg (smtExpr2expr e)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "*" -> Mul (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "=" -> Eq (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "<" -> Lt (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = ">" -> Gt (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "<=" -> Le (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = ">=" -> Ge (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "mod" -> Mod (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), es
      | UserDefinedOperation (ident, _, _), es -> Apply (ident, es |> List.map smtExpr2expr)
    | smtExpr.And e -> e |> List.toArray |> Array.map smtExpr2expr |> And
    | smtExpr.Or e -> e |> List.toArray |> Array.map smtExpr2expr |> Or
    | smtExpr.Not e -> smtExpr2expr e |> Not
    | Hence (e1, e2) -> Implies (smtExpr2expr e1, smtExpr2expr e2)
    | QuantifierApplication ([ ForallQuantifier args ], expr) ->
      ForAll (List.map fst args |> List.toArray, smtExpr2expr expr)
    | _ -> __notImplemented__()

  let rec smtExpr2expr' =
    function
    | Number i -> Int i
    | BoolConst b -> Bool b
    | Ident (ident, _) -> Var ident
    | smtExpr.Apply (operation, exprs) ->
      match operation, exprs with
      | UserDefinedOperation (ident, _, _), [ e1; e2 ] when ident = "mod" -> Mod (smtExpr2expr' e1, smtExpr2expr' e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "+" -> Add (smtExpr2expr' e1, smtExpr2expr' e2)
      | ElementaryOperation (ident, _, _), [ e ] when ident = "-" -> Neg (smtExpr2expr' e)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "*" -> Mul (smtExpr2expr' e1, smtExpr2expr' e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "=" -> Eq (smtExpr2expr' e1, smtExpr2expr' e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "<" -> Lt (smtExpr2expr' e1, smtExpr2expr' e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = ">" -> Gt (smtExpr2expr' e1, smtExpr2expr' e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "<=" -> Le (smtExpr2expr' e1, smtExpr2expr' e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = ">=" -> Ge (smtExpr2expr' e1, smtExpr2expr' e2)
      | ElementaryOperation (ident, _, _), [ e1; e2 ] when ident = "mod" -> Mod (smtExpr2expr' e1, smtExpr2expr' e2)
      | ElementaryOperation (ident, _, _), _
      | UserDefinedOperation (ident, _, _), _ -> Var ident
    | smtExpr.And e -> e |> List.toArray |> Array.map smtExpr2expr' |> And
    | smtExpr.Or e -> e |> List.toArray |> Array.map smtExpr2expr' |> Or
    | smtExpr.Not e -> smtExpr2expr' e |> Not
    | Hence (e1, e2) -> Implies (smtExpr2expr' e1, smtExpr2expr' e2)
    | QuantifierApplication ([ ForallQuantifier args ], expr) ->
      ForAll (List.map fst args |> List.toArray, smtExpr2expr' expr)
    | _ -> __notImplemented__()

  let rec origCommand2program =
    function
    | Definition (DefineFun (name, args, _, body)) -> Def (name, List.map (fun (n, _) -> n) args, smtExpr2expr body)
    | Command (DeclareFun (name, args, _)) -> Decl (name, args.Length)
    | originalCommand.Assert expr -> Assert (smtExpr2expr expr)
    | _ -> __notImplemented__()



  let def2decVars =
    let rec toVar =
      function
      | Apply (n, _) -> Var n
      | Int _
      | Bool _
      | Var _ as v -> v
      | Eq (e1, e2) -> Eq (toVar e1, toVar e2)
      | Lt (e1, e2) -> Lt (toVar e1, toVar e2)
      | Gt (e1, e2) -> Gt (toVar e1, toVar e2)
      | Le (e1, e2) -> Le (toVar e1, toVar e2)
      | Ge (e1, e2) -> Ge (toVar e1, toVar e2)
      | Add (e1, e2) -> Add (toVar e1, toVar e2)
      | Subtract (e1, e2) -> Subtract (toVar e1, toVar e2)
      | Neg e -> Neg (toVar e)
      | Mod (e1, e2) -> Mod (toVar e1, toVar e2)
      | Mul (e1, e2) -> Mul (toVar e1, toVar e2)
      | And es -> es |> Array.map toVar |> And
      | Or es -> es |> Array.map toVar |> Or
      | Not e -> toVar e |> Not
      | Implies (e1, e2) -> Implies (toVar e1, toVar e2)
      | Ite (e1, e2, e3) -> Ite (toVar e1, toVar e2, toVar e3)
      | ForAll _
      | App _ as otherwise -> otherwise

    List.map (function
      | Def (n, args, e) -> Def (n, args, e |> toVar)
      | otherwise -> otherwise)


  let substituteVar =
    let rec helper var value =
      let helper' x = helper var value x

      function
      | Var _ as x when x = var -> value
      | Eq (expr1, expr2) -> Eq (helper' expr1, helper' expr2)
      | Lt (expr1, expr2) -> Lt (helper' expr1, helper' expr2)
      | Gt (expr1, expr2) -> Gt (helper' expr1, helper' expr2)
      | Le (expr1, expr2) -> Le (helper' expr1, helper' expr2)
      | Ge (expr1, expr2) -> Ge (helper' expr1, helper' expr2)
      | Add (expr1, expr2) -> Add (helper' expr1, helper' expr2)
      | Subtract (expr1, expr2) -> Subtract (helper' expr1, helper' expr2)
      | Neg expr -> Neg (helper' expr)
      | Mul (expr1, expr2) -> Mul (helper' expr1, helper' expr2)
      | Mod (expr1, expr2) -> Mod (helper' expr1, helper' expr2)
      | Implies (expr1, expr2) -> Implies (helper' expr1, helper' expr2)
      | And exprs -> And (Array.map helper' exprs)
      | Or exprs -> Or (Array.map helper' exprs)
      | Not expr -> Not (helper' expr)
      | Apply (n, exprs) -> Apply (n, exprs |> List.map helper')
      | ForAll (ns, expr) -> ForAll (ns, helper' expr)
      | App (n, exprs) -> App (n, exprs |> Array.map helper')
      | Ite (expr1, expr2, expr3) -> Ite (helper' expr1, helper' expr2, helper' expr3)
      | Int _
      | Bool _
      | Var _ as expr -> expr

    helper

open AST

module Interpreter =
  let update =
    fun k v map ->
      Map.containsKey k map
      |> function
        | true -> Map.remove k map |> Map.add k v
        | false -> Map.add k v map

  let define = fun env (name, args, expr) -> env.ctxFuns.Add (name, (args, expr))

  let declConsts = List.map DeclIntConst


  let rec evalExpr: Env -> Expr -> Microsoft.Z3.Expr =
    fun env ->
      function
      | Int x -> env.ctxSlvr.MkInt x
      | Bool x -> env.ctxSlvr.MkBool x
      | Eq (expr1, expr2) -> env.ctxSlvr.MkEq (evalExpr env expr1, evalExpr env expr2)
      | Lt (expr1, expr2) -> env.ctxSlvr.MkLt (evalExpr env expr1 :?> ArithExpr, evalExpr env expr2 :?> ArithExpr)
      | Gt (expr1, expr2) -> env.ctxSlvr.MkGt (evalExpr env expr1 :?> ArithExpr, evalExpr env expr2 :?> ArithExpr)
      | Le (expr1, expr2) -> env.ctxSlvr.MkLe (evalExpr env expr1 :?> ArithExpr, evalExpr env expr2 :?> ArithExpr)
      | Ge (expr1, expr2) -> env.ctxSlvr.MkGe (evalExpr env expr1 :?> ArithExpr, evalExpr env expr2 :?> ArithExpr)
      | Mod (expr1, expr2) -> env.ctxSlvr.MkMod (evalExpr env expr1 :?> IntExpr, evalExpr env expr2 :?> IntExpr)
      | Add (expr1, expr2) -> env.ctxSlvr.MkAdd (evalExpr env expr1 :?> ArithExpr, evalExpr env expr2 :?> ArithExpr)
      | Subtract (expr1, expr2) ->
        env.ctxSlvr.MkSub (evalExpr env expr1 :?> ArithExpr, evalExpr env expr2 :?> ArithExpr)
      | Neg expr -> env.ctxSlvr.MkSub (env.ctxSlvr.MkInt 0, evalExpr env expr :?> ArithExpr)
      | Mul (expr1, expr2) -> env.ctxSlvr.MkMul (evalExpr env expr1 :?> ArithExpr, evalExpr env expr2 :?> ArithExpr)
      | And exprs ->
        exprs
        |> Array.map (fun x -> evalExpr env x :?> BoolExpr)
        |> fun x -> env.ctxSlvr.MkAnd x
      | Or exprs ->
        exprs
        |> Array.map (fun x -> evalExpr env x :?> BoolExpr)
        |> fun x -> env.ctxSlvr.MkOr x
      | Not expr -> env.ctxSlvr.MkNot (evalExpr env expr :?> BoolExpr)
      | Implies (expr1, expr2) ->
        env.ctxSlvr.MkImplies (evalExpr env expr1 :?> BoolExpr, evalExpr env expr2 :?> BoolExpr)
      | Var x -> env.ctxVars |> Map.find x
      | App (name, expr) ->
        let decFun = env.ctxDecfuns |> Map.find name in
        let args: Microsoft.Z3.Expr[] = Array.map (evalExpr env) expr
        env.ctxSlvr.MkApp (decFun, args)
      | Apply (n, [ x; y ]) when n = "distinct" -> evalExpr env (Not (Eq (x, y)))
      | Apply (n, vs) ->
        env.ctxFuns
        |> Map.find n
        |> fun (args, body) ->
            let bindings = List.zip args vs

            let ctx_vars =
              bindings
              |> List.fold (fun acc (arg, v) -> acc |> update arg (evalExpr env v)) env.ctxVars

            evalExpr { env with ctxVars = ctx_vars } body
      | ForAll ([||], expr) -> evalExpr env expr
      | ForAll (names, expr) ->
        let vars: Microsoft.Z3.Expr[] =
          names
          |> Array.map (fun name ->
            env.ctxSlvr.MkIntConst name) in

        let ctxVars =
          Array.zip names vars
          |> Array.fold (fun acc (name, value) -> acc |> Map.add name value) env.ctxVars in

        env.ctxSlvr.MkForall (vars, evalExpr { env with ctxVars = ctxVars } expr)
      | Ite (exprIf, exprThen, exprElse) ->
        env.ctxSlvr.MkITE (evalExpr env exprIf :?> BoolExpr, evalExpr env exprThen, evalExpr env exprElse)


  let evalCmds =
    fun env (solver: Solver) ->
      List.fold
        (fun (env, solver: Solver, expr) cmd ->
          match cmd with
          | DeclConst (n, t) ->
            match t with
            | Integer ->
              let intConst = env.ctxSlvr.MkIntConst n

              ({ env with
                  ctxVars = env.ctxVars |> Map.add n intConst },
               solver,
               expr)
            | Boolean ->
              let boolConst = env.ctxSlvr.MkBoolConst n

              ({ env with
                  ctxVars = env.ctxVars |> Map.add n boolConst },
               solver,
               expr)
          | DeclIntConst n ->
            let intConst = env.ctxSlvr.MkIntConst n

            ({ env with
                ctxVars = env.ctxVars |> Map.add n intConst },
             solver,
             expr)
          | Assert e ->

            let assrt = evalExpr env e in
            solver.Add [| assrt :?> BoolExpr |]
            (env, solver, evalExpr env e)
          | Def d -> ({ env with ctxFuns = define env d }, solver, expr)
          | Decl (name, n) ->
            let intsNum: Sort[] =
              n
              |> Array.unfold (fun state ->
                if state = 0 then
                  None
                else
                  Some (env.ctxSlvr.IntSort, state - 1))

            let declFun =
              env.ctxSlvr.MkFuncDecl (env.ctxSlvr.MkSymbol name, intsNum, env.ctxSlvr.MkBoolSort ())

            ({ env with
                ctxDecfuns = env.ctxDecfuns |> Map.add name declFun },
             solver,
             expr))
        (env, solver, env.ctxSlvr.MkInt 0)

  type Status<'a, 'b> =
    | SAT of 'a
    | UNSAT of 'b

  type z3solve<'a, 'b> =
    { env: Env
      solver: Solver
      unsat: Env -> Solver -> 'a
      sat: Env -> Solver -> 'b
      cmds: Program list }


  let z3solve x =
    let env, solver, _ = evalCmds x.env x.solver x.cmds

    match x.solver.Check () with
    | Status.SATISFIABLE -> SAT <| x.sat env solver
    | Status.UNSATISFIABLE -> UNSAT <| x.unsat env solver
    | _ -> failwith "UNKNOWN"


  let model (env: Env) (solver: Solver) =
    env.ctxVars
    |> Map.toList
    |> List.fold (fun acc (n, v) -> (n, solver.Model.Double (solver.Model.Eval (v, true)) |> int64) :: acc) []
    |> List.map (fun (n, i) -> Def (n, [], Int i))

  module SoftSolver =
    let hardConstants (env: Env) =
      env.ctxVars |> Map.filter (fun k _ -> k.Contains "soft" |> not)

    let model (env: Env) (solver: Solver) =
      hardConstants env
      |> Map.toList
      |> List.fold (fun acc (n, v) -> (n, solver.Model.Double (solver.Model.Eval (v, true)) |> int64) :: acc) []
      |> List.map (fun (n, i) -> Def (n, [], Int i))

    type z3SoftSolve<'a, 'b> =
      { env: Env
        solver: Solver
        unsat: Env -> Solver -> 'a
        sat: Env -> Solver -> 'b
        cmds: Program list }

    let z3softSolver (x: z3SoftSolve<_, _>) =
      let env, solver, _ = evalCmds x.env x.solver x.cmds

      let softVars =
        env.actives |> List.map (fun n -> env.ctxVars |> Map.find n) |> List.toArray

      match x.solver.Check softVars with
      | Status.SATISFIABLE -> SAT <| x.sat env solver
      | Status.UNSATISFIABLE -> UNSAT <| x.unsat env solver
      | _ -> failwith "UNKNOWN"

    let softUnsat env (solver: Solver) =
      let unsatCoreNames = solver.UnsatCore |> Array.map string |> Set
      let intersection = Set env.actives |> Set.intersect unsatCoreNames

      if intersection.IsEmpty then
        failwith "UNKNOWN"
      else
        ({ env with
            actives = env.actives |> List.tail },
         solver)

    let setCommands env (solver: Solver) cmds =
      z3softSolver
        { env = env
          solver = solver
          unsat = fun env solver -> (env, solver)
          sat = fun env solver -> (env, solver)
          cmds = cmds }
      |> function
        | SAT (env, solver)
        | UNSAT (env, solver) -> (env, solver, cmds)

    let evalModel env (solver: Solver) cmds =
      z3softSolver
        { env = env
          solver = solver
          unsat = fun env solver -> (env, solver)
          sat = fun env solver -> (env, solver, model env solver)
          cmds = cmds }

    let rec solve env (solver: Solver) =
      z3softSolver
        { env = env
          solver = solver
          unsat = softUnsat
          sat = fun env solver -> (env, solver, model env solver)
          cmds = [] }
      |> function
        | SAT x -> x
        | UNSAT (env', solver') -> solve env' solver'

    let setSoftAsserts env (solver: Solver) (constants: Program list) =
      let constNames =
        constants
        |> List.fold
          (fun acc x ->
            match x with
            | Def (n, [], _) -> n :: acc
            | _ -> acc)
          []
        |> List.rev

      let softNames = constNames |> List.map (fun n -> $"soft_{n}")

      constNames
      |> List.map2
        (fun softn n -> Assert (Implies (Var softn, Or [| Eq (Var n, Int 0); Eq (Var n, Int 1) |])))
        softNames
      |> ((@) (softNames |> List.map (fun n -> DeclConst (n, Boolean))))
      |> setCommands { env with actives = softNames } solver


  let emptyEnv argss =
    { ctxSlvr = new Context (argss |> dict |> Dictionary)
      ctxVars = Map.empty
      ctxFuns = Map.empty
      ctxDecfuns = Map.empty
      actives = [] }
