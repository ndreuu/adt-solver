module Z3Interpreter

open System
open System.Collections.Generic
open Microsoft.FSharp.Collections
open Microsoft.Z3
open NUnit.Framework
open SMTLIB2.Prelude
open IntOps

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
    | Neg expr -> smtExpr.Apply (negOp, [ expr2smtExpr expr ])
    | Mod (expr1, expr2) -> smtExpr.Apply (modOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Mul (expr1, expr2) -> smtExpr.Apply (mulOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | And exprs -> Array.map expr2smtExpr exprs |> Array.toList |> smtExpr.And
    | Or exprs -> Array.map expr2smtExpr exprs |> Array.toList |> smtExpr.Or
    | Not expr -> expr2smtExpr expr |> smtExpr.Not
    | Implies (expr1, expr2) -> Hence (expr2smtExpr expr1, expr2smtExpr expr2)
    | Var n -> Ident (n, IntSort)
    | App (n, exprs) -> smtExpr.Apply (UserDefinedOperation (n, [], IntSort), Array.map expr2smtExpr exprs |> Array.toList)
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
      ctxDecfuns: DecFunsCtx }

  and Function = Name list * Expr

  let newEnv args =
    { ctxSlvr = new Context (args |> dict |> Dictionary)
      ctxVars = Map.empty
      ctxFuns = Map.empty
      ctxDecfuns = Map.empty }
    
  
  type Type = Boolean | Integer
  
  type Program =
    | Def of Definition
    | DeclIntConst of Name
    | DeclConst of Name * Type
    | Decl of Name * ArgsNum
    | Assert of Expr

  let program2originalCommand =
    function
      | Def (n, ns, e) -> originalCommand.Definition (DefineFun (n, List.map (fun n -> (n, IntSort)) ns, IntSort, expr2smtExpr e))
      | DeclIntConst n -> originalCommand.Command (command.DeclareConst (n, IntSort))
      | DeclConst (n, t) ->
        let t' = match t with Integer -> IntSort | Boolean -> BoolSort
        originalCommand.Command (command.DeclareConst (n, t'))
      | Decl (n, num) ->
        let args = List.unfold (fun state -> if state = 0 then None else Some (IntSort, state - 1))
        Command (DeclareFun (n, args num, BoolSort))
      | Assert e -> originalCommand.Assert (expr2smtExpr e)

  // let rec withFuns ident exprs = Apply (ident, exprs |> List.map (smtExpr2expr usedOps))
  // and withConsts ident _ = Var ident
  
  // and f: Name list -> (Name -> smtExpr list -> Expr) = withConsts
  
  // let rec withFuns usedOps ident exprs = Apply (ident, exprs |> List.map (smtExpr2expr withFuns usedOps))
  // and withConsts _ ident _ = Var ident
  
  let rec smtExpr2expr =
    function
    | Number i -> Int i
    | BoolConst b -> Bool b
    | Ident (ident, _) ->
      // printfn $"iiiiiiiiiiiii{ident}"
      Var ident
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
    | QuantifierApplication ([ ForallQuantifier args ], expr) -> ForAll (List.map fst args |> List.toArray, smtExpr2expr expr)
    | otherwise -> failwith $"{otherwise.ToString()}"

  let rec smtExpr2expr' =
    function
    | Number i -> Int i
    | BoolConst b -> Bool b
    | Ident (ident, _) ->
      printfn $"iiiiiiiiiiiii{ident}"
      Var ident
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
    | QuantifierApplication ([ ForallQuantifier args ], expr) -> ForAll (List.map fst args |> List.toArray, smtExpr2expr' expr)
    | otherwise -> failwith $"{otherwise.ToString()}"

  let rec origCommand2program =
    function
      | Definition (DefineFun (name, args, _, body)) -> Def (name, List.map (fun (n, _) -> n) args, smtExpr2expr body )
      | Command (DeclareFun (name, args, _)) -> Decl (name, args.Length) 
      | originalCommand.Assert expr -> Assert (smtExpr2expr expr)
      | _ -> failwith "!"

  
          
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
      | Neg e -> Neg (toVar e)
      | Mod (e1, e2) -> Mod (toVar e1, toVar e2)
      | Mul (e1, e2) -> Mul (toVar e1, toVar e2)
      | And es -> es |> Array.map (fun e -> toVar e) |> And
      | Or es -> es |> Array.map (fun e -> toVar e) |> Or
      | Not e -> toVar e |> Not
      | Implies (e1, e2) -> Implies (toVar e1, toVar e2)
      | Ite (e1, e2, e3) -> Ite (toVar e1, toVar e2, toVar e3)
      | ForAll _ | App _ as otherwise -> otherwise
    
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


  let rec eval_expr: Env -> Expr -> Microsoft.Z3.Expr =
    fun env ->
      function
      | Int x -> env.ctxSlvr.MkInt x
      | Bool x -> env.ctxSlvr.MkBool x
      | Eq (expr1, expr2) -> env.ctxSlvr.MkEq (eval_expr env expr1, eval_expr env expr2)
      | Lt (expr1, expr2) -> env.ctxSlvr.MkLt (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
      | Gt (expr1, expr2) -> env.ctxSlvr.MkGt (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
      | Le (expr1, expr2) -> env.ctxSlvr.MkLe (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
      | Ge (expr1, expr2) -> env.ctxSlvr.MkGe (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
      | Mod (expr1, expr2) -> env.ctxSlvr.MkMod (eval_expr env expr1 :?> IntExpr, eval_expr env expr2 :?> IntExpr)
      | Add (expr1, expr2) -> env.ctxSlvr.MkAdd (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
      | Subtract (expr1, expr2) -> env.ctxSlvr.MkSub (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
      | Neg expr -> env.ctxSlvr.MkSub (eval_expr env expr :?> ArithExpr)
      | Mul (expr1, expr2) -> env.ctxSlvr.MkMul (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
      | And exprs ->
        exprs
        |> Array.map (fun x -> eval_expr env x :?> BoolExpr)
        |> fun x -> env.ctxSlvr.MkAnd x
      | Or exprs ->
        exprs
        |> Array.map (fun x -> eval_expr env x :?> BoolExpr)
        |> fun x -> env.ctxSlvr.MkOr x
      | Not expr -> env.ctxSlvr.MkNot (eval_expr env expr :?> BoolExpr)
      | Implies (expr1, expr2) ->
        env.ctxSlvr.MkImplies (eval_expr env expr1 :?> BoolExpr, eval_expr env expr2 :?> BoolExpr)
      | Var x -> env.ctxVars |> Map.find x
      | App (name, expr) ->
        let decFun = env.ctxDecfuns |> Map.find name in
        let args: Microsoft.Z3.Expr[] = Array.map (eval_expr env) expr
        env.ctxSlvr.MkApp (decFun, args)
      | Apply (n, [ x; y ]) when n = "distinct" -> eval_expr env (Not (Eq (x, y)))
      | Apply (n, vs) ->
        printfn $"{n}"
        env.ctxFuns
        |> Map.find n
        |> fun (args, body) ->
             let bindings = List.zip args vs

             let ctx_vars =
               bindings
               |> List.fold (fun acc (arg, v) -> acc |> update arg (eval_expr env v)) env.ctxVars

             eval_expr { env with ctxVars = ctx_vars } body
      | ForAll ([||], expr) -> eval_expr env expr
      | ForAll (names, expr) ->
        let vars: Microsoft.Z3.Expr[] =
          names
          |> Array.map
               (fun name ->
                  // for n in names do
                    // printfn $"{n}"
                  env.ctxSlvr.MkIntConst name) in

        let ctxVars =
          Array.zip names vars
          |> Array.fold (fun acc (name, value) -> acc |> Map.add name value) env.ctxVars in

        env.ctxSlvr.MkForall (vars, eval_expr { env with ctxVars = ctxVars } expr)
      | Ite (exprIf, exprThen, exprElse) ->
        env.ctxSlvr.MkITE (eval_expr env exprIf :?> BoolExpr, eval_expr env exprThen, eval_expr env exprElse)

  let eval_cmds =
    fun env ->
      List.fold
        (fun (env, varMap, expr) cmd ->
          match cmd with
          | DeclIntConst n ->
            let intConst = env.ctxSlvr.MkIntConst n

            ({ env with ctxVars = env.ctxVars |> Map.add n intConst }, (n, intConst) :: varMap, expr)
          | Assert e -> (env, varMap, eval_expr env e)
          | Def d -> ({ env with ctxFuns = define env d }, varMap, expr)
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

            ({ env with ctxDecfuns = env.ctxDecfuns |> Map.add name declFun }, varMap, expr))
        (env, [], env.ctxSlvr.MkInt 0)

  let evalCmds =
    fun env (solver: Solver) ->
      List.fold
        (fun (env, expr) cmd ->
          match cmd with
          | DeclConst (n, t) ->
            match t with
            | Integer -> 
              let intConst = env.ctxSlvr.MkIntConst n
  
              ({ env with ctxVars = env.ctxVars |> Map.add n intConst }, expr)
            | Boolean -> 
              let boolConst = env.ctxSlvr.MkBoolConst n
  
              ({ env with ctxVars = env.ctxVars |> Map.add n boolConst }, expr)
          | DeclIntConst n ->
            let intConst = env.ctxSlvr.MkIntConst n

            ({ env with ctxVars = env.ctxVars |> Map.add n intConst }, expr)
          | Assert e ->
            
            let assrt = eval_expr env e in
            solver.Add [|assrt :?> BoolExpr|]
            (env, eval_expr env e)
          | Def d -> ({ env with ctxFuns = define env d }, expr)
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

            ({ env with ctxDecfuns = env.ctxDecfuns |> Map.add name declFun }, expr))
        (env, env.ctxSlvr.MkInt 0)

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
    let env,  _ = evalCmds x.env x.solver (x.cmds)
  
    match x.solver.Check () with
    | Status.SATISFIABLE -> SAT <| x.sat env x.solver
    | Status.UNSATISFIABLE -> UNSAT <| x.unsat env x.solver
    // | _ -> UNSAT <| x.unsat env x.solver

  let model (env: Env) (solver: Solver) =
    env.ctxVars
    |> Map.toList
    |> List.fold
        (fun acc (n, v) ->
          (n, solver.Model.Double (solver.Model.Eval (v, true)) |> int64) :: acc)
        []
    |> List.map (fun (n, i) -> Def (n, [], Int i))


  module MaxSat =
    type z3SoftSolve<'a> =
      { env: Env
        solver: Solver
        unsat: Env -> Solver -> 'a
        sat: Env -> Solver -> 'a
        cmds: Program list
        actives: Program list }

    let hardConstants (env: Env) =
      env.ctxVars |> Map.filter (fun k _ -> k.Contains "soft" |> not)
 
    let model' (env: Env) (solver: Solver) softGroups =
      hardConstants env 
      |> fun xs ->
        for x in xs do
          printfn $"A:\n{x}"
        xs
      |> Map.toList
      |> List.fold
          (fun acc (n, v) ->
            printfn $">>>{n}"
            (n, solver.Model.Double (solver.Model.Eval (v, true)) |> int64) :: acc)
          []
      |> List.map (fun (n, i) -> Def (n, [], Int i))
    
    let z3softSolver' (x: z3solve<_, _>) softNames =
      let env, _ = evalCmds x.env x.solver x.cmds
      let softExprs =
        softNames
         |> List.map
              (fun n ->
                env.ctxVars
                |> Map.find n)  
          |> List.toArray
      
      match x.solver.Check softExprs with
      | Status.SATISFIABLE ->
        SAT <| x.sat env x.solver
      | Status.UNSATISFIABLE ->
        UNSAT <| x.unsat env x.solver

    let rmElements elements xs = List.fold (fun acc e -> acc |> List.filter ((<>) e)) xs elements    

    let decls = List.map (fun n -> DeclConst (n, Boolean))
    let names = List.fold (fun acc x -> match x with | DeclConst (n, Boolean) -> n :: acc | _ -> acc) [] >> List.rev
    
    let rec z3softSolver env solver cmds (actives: Program list) =
      z3softSolver'
        { env = env
          solver = solver
          unsat = fun env solver ->
            (env, solver.UnsatCore |> Array.toList |> List.map (fun x -> DeclConst (x.ToString(), Boolean)))
          sat = fun env solver -> (env, actives, model' env solver (names actives))
          cmds = cmds }
        (names actives)
      |> function
        | SAT (env, core, model) ->
          printfn $"SAT {core}"
          printfn $"{model}"
          SAT (env, core, model)
        | UNSAT (env', []) ->
          UNSAT (env', [])
        | UNSAT (env', core) ->
          let actives' = rmElements core actives
          z3softSolver env' solver cmds actives'
          
let aaa () =
  let cmds =
      [ DeclConst ("soft1", Boolean)
        DeclConst ("soft2", Boolean)
        
        DeclConst ("x", Integer)
        DeclConst ("y", Integer)
        
        Assert (And [| Apply ("distinct", [ Var "x"; Int 0 ]); Apply ("distinct", [ Var "x"; Int 1 ]) |])
        Assert (And [| Apply ("distinct", [ Var "y"; Int 0 ]); Apply ("distinct", [ Var "y"; Int 0 ]) |])
        
        Assert (Implies (Var "soft1", Or [| Eq(Var "x", Int 0); Eq(Var "x", Int 1) |] ))
        Assert (Implies (Var "soft2", Or [| Eq(Var "y", Int 0); Eq(Var "y", Int 1) |])) ]
  
  let emptyEnv = newEnv []
  let solver = emptyEnv.ctxSlvr.MkSolver "NIA"
  let softGroups =
    [  "soft2" ]
    
  Interpreter.MaxSat.z3softSolver'
    { env = emptyEnv
      solver = solver
      unsat = fun env solver ->
        (env, solver.UnsatCore |> Array.toList)
      sat = fun env solver -> (env, [])
      cmds = cmds }
    softGroups
  |> function
    | Interpreter.UNSAT (_, core) -> printfn $"UNSAT {core}"
    | Interpreter.SAT (_, core) -> printfn $"SAT> {core}"
  
  let rmElements elements xs =
    List.fold (fun acc e -> acc |> List.filter ((<>) e)) xs elements
  
  printfn $"{rmElements [1;2;3] [1;2;3;4;5]}"
  
  let rec helper env solver cmds actives =
    Interpreter.MaxSat.z3softSolver'
      { env = env
        solver = solver
        unsat = fun env solver ->
          (env, solver.UnsatCore |> Array.toList |> List.map (fun x -> x.ToString ()))
        sat = fun env solver -> (env, actives)
        cmds = cmds }
      actives
    |> function
      | Interpreter.SAT (_, core) ->
        printfn $"SAT {core}"
      | Interpreter.UNSAT (env', core) ->
        let actives' = rmElements core actives
        helper env' solver cmds actives'
  
  Interpreter.MaxSat.z3softSolver emptyEnv solver cmds [ DeclConst ("soft1", Boolean); DeclConst ("soft2", Boolean) ]
  function | Interpreter.SAT (_,_,model) -> printfn $"{model}"
  
    
  // let env, solver =
  //   Interpreter.z3solve
  // { env = emptyEnv
  // solver = solver
  // unsat = fun env solver -> (env, solver)
  // sat = fun env solver -> (env, solver)
  // cmds = cmds }
  //   |> function Interpreter.SAT v | Interpreter.UNSAT v -> v
  
  // Interpreter.MaxSat.z3softSolver'
  //   { env = emptyEnv
  //     solver = solver
  //     unsat = fun env solver ->
  //       solver.UnsatCore |> fun vs -> for v in vs do printfn $"{v}"
  //       (env, solver)
  //     sat = fun env solver -> (env, solver)
  //     cmds = cmds }
  //   softGroups
  //
  printfn ""
  
    
    
    
  // Interpreter.MaxSat.z3softSolver emptyEnv solver cmds softGroups
  // |> printfn "%O"
    
    
  
  
  // Interpreter.MaxSat.z3softSolver
  //   { env = emptyEnv
  //     solver = solver
  //     unsat = fun env solver -> (env, solver)
  //     sat = fun env solver -> (env, solver)
  //     cmds = cmds }
  //   softGroups 
      

  ()

let chck () = Eq (Int 1, Int 2) |> printfn "%O"

let sd () =
  let line=
    """(!*fof (pasf) (and (or ((ncong ((c3 . 1) . 1)) (((c0 . 1) ((c2 . 2) . 1)((c2 . 1) . -1)) ((c1 . 1) ((c2 . 1) . 1))) nil) (equal (((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) (equal (((c2 . 1) . 1) . 1) nil) (equal (((c2 . 1). 1)) nil) (equal (((c3 . 1) . 1)) nil)) (or ((ncong ((c3 . 1) . 1)) (((c0 . 1)((c2 . 2) . 1)) ((c1 . 1) ((c2 . 1) . 1) . 1)) nil) (equal (((c0 . 1) ((c2 . 1). 1) . -1) ((c1 . 1) . 1)) nil) (equal (((c0 . 1) ((c2 . 1) . 1)) ((c1 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((c0 . 1) ((c2 . 1) . 1)) ((c1 . 1) . 1)) nil) (equal (((c0 . 1) . 1)) nil) (equal (((c3 . 1) . 1)) nil)) (or ((ncong ((c2 . 1)((c3 . 1) . 1))) (((c0 . 1) ((c2 . 2) . 1)) ((c1 . 1) ((c2 . 1) . 1) . 1)) nil)(equal (((c0 . 1) ((c2 . 1) . 1)) ((c1 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((c0 . 1) ((c2 . 1) . 1)) ((c1 . 1) . 1)) nil) (equal (((c0 . 1) . 1)) nil) (equal (((c1 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((c3 . 1) . 1))nil)) (ball !_k99 (ball !_k98 (ball !_k97 (ball !_k96 (ball !_k95 (ball !_k94 (ball !_k93 (or (ball !_k62 (ball !_k61 (ball !_k59 (ball !_k54 (ball !_k50 (ball!_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((!_k93 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) (equal (((!_k59 . 1) ((c2 . 1) . 1) . -1) ((!_k93 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2. 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil) ((ncong ((c2 . 2) ((c3 . 1) . 1)) ((c2 . 1) ((c3 . 1) . -1))) (((!_k59 . 1) ((c2 . 1) . 1) . -1) ((!_k93 . 1) . 1) ((c0 . 1) ((c2 . 3) . -1) ((c2 . 2) . 1)) ((c1 . 1) ((c2 . 2) . -1))) nil) ((ncong ((c2 . 1) ((c3 . 2) . 1))) (((!_k59 . 1) ((c2 . 1) ((c3 . 1) . 1)))) nil)(neq (((!_k50 . 1) . 1)) nil) (neq (((!_k4 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((!_k59 . 1) . 1) ((!_k93 . 1) . -1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil)(equal (((!_k4 . 1) . 1) . -1) nil))) (or (and (leq (((!_k50 . 1) . 1) ((c3 . 1). 1)) nil) (geq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or(and (leq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k54 . 1) . 1) ((c3 .1) . -1)) nil)) (and (geq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k54. 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) .-1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 .1) . -1))) nil)))) (or (and (leq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k61 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k61 . 1) . 1) ((c3 . 1) .1)) nil) (leq (((!_k61 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k62. 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k62 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k62 . 1) . 1) ((c3 .1) . -1)) nil)))) (equal (((c2 . 1) . 1) . -1) nil) ((ncong ((c2 . 1) . 1) . -1)(((!_k93 . 1) . 1) ((c1 . 1) . -1)) nil)) (or (and (leq (((!_k93 . 1) . 1) ((!_k94 . 1) ((c2 . 1) ((c3 . 1) . -1))) ((!_k97 . 1) . -1) ((c2 . 3) ((c3 . 2) .1)) ((c2 . 2) ((c3 . 2) . -1)) ((c2 . 1) . 1) . -1) nil) (geq (((!_k93 . 1) . 1)((!_k94 . 1) ((c2 . 1) ((c3 . 1) . -1))) ((!_k97 . 1) . -1) ((c2 . 3) ((c3 . 2). -1)) ((c2 . 2) ((c3 . 2) . 1)) ((c2 . 1) . -1) . 1) nil)) (and (greaterp (((!_k93 . 1) . 1) ((!_k94 . 1) ((c2 . 1) ((c3 . 1) . -1))) ((!_k97 . 1) . -1) ((c2. 3) ((c3 . 2) . 1)) ((c2 . 2) ((c3 . 2) . -1)) ((c2 . 1) . 1)) nil) (lessp (((!_k93 . 1) . 1) ((!_k94 . 1) ((c2 . 1) ((c3 . 1) . -1))) ((!_k97 . 1) . -1) ((c2. 3) ((c3 . 2) . -1)) ((c2 . 2) ((c3 . 2) . 1)) ((c2 . 1) . -1)) nil)))) (or (equal (((!_k94 . 1) . 1) . 1) nil) (equal (((!_k94 . 1) . 1) . -1) nil))) (or (and (leq (((!_k95 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k95 . 1) . 1) ((c3 .1) . -1)) nil)) (and (geq (((!_k95 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k95. 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k96 . 1) . 1) ((c3 . 1) .1)) nil) (geq (((!_k96 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k96 . 1). 1) ((c3 . 1) . 1)) nil) (leq (((!_k96 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k97 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq(((!_k97 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k97 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k97 .1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)))) (or (and (leq (((!_k98 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k98 . 1) . 1) ((c3 . 1) . -1))nil)) (and (geq (((!_k98 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k98 . 1) . 1)((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k99 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k99 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k99 . 1) . 1) ((c3. 1) . 1)) nil) (leq (((!_k99 . 1) . 1) ((c3 . 1) . -1)) nil)))) (ball !_k99 (ball !_k98 (ball !_k97 (ball !_k96 (ball !_k95 (ball !_k93 (ball !_k62 (ball!_k61 (ball !_k59 (ball !_k54 (ball !_k50 (ball !_k4 (or (equal (((c3 . 1) . 1))nil) (equal (((c2 . 1) . 1)) nil) (equal (((!_k93 . 1) . 1) ((c0 . 1) ((c2 . 2). 1) . -1) ((c1 . 1) ((c2 . 1) . 1) . 1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k59 . 1) . 1) ((!_k93 . 1) . 1)) nil) (equal (((!_k59 . 1) . 1) ((!_k93 .1) . 1) ((c0 . 1) ((c2 . 2) . 1) ((c2 . 1) . -1)) ((c1 . 1) ((c2 . 1) . 1))) nil) ((ncong ((c2 . 1) ((c3 . 2) . 1))) (((!_k59 . 1) ((c2 . 1) ((c3 . 1) . 1))))nil) (neq (((!_k50 . 1) . 1)) nil) (neq (((!_k4 . 1) ((c2 . 1) ((c3 . 1) . 1)))((!_k59 . 1) . 1) ((!_k93 . 1) ((c2 . 1) . -1) . 1) ((c0 . 1) ((c2 . 3) . -1) ((c2 . 2) . 1)) ((c1 . 1) ((c2 . 2) . -1))) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1) nil))) (or (and (leq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k50 . 1) . 1) ((c3 . 1) . -1))nil)))) (or (and (leq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k54 . 1). 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k54 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k59 . 1) . 1)((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k59 . 1) . 1) ((c2 . 1)((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3). -1) ((c3 . 1) . -1))) nil)))) (or (and (leq (((!_k61 . 1) . 1) ((c3 . 1) . 1))nil) (geq (((!_k61 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k61 . 1) . 1)((c3 . 1) . 1)) nil) (leq (((!_k61 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k62 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k62 . 1) . 1) ((c3 . 1) .-1)) nil)) (and (geq (((!_k62 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k62 . 1). 1) ((c3 . 1) . -1)) nil)))) (and (geq (((!_k93 . 1) . 1) ((!_k97 . 1) . 1) ((c2 . 2) ((c3 . 2) . 1)) . 1) nil) (leq (((!_k93 . 1) . 1) ((!_k97 . 1) . 1) ((c2. 2) ((c3 . 2) . -1)) . -1) nil))) (or (and (leq (((!_k95 . 1) . 1) ((c3 . 1) .1)) nil) (geq (((!_k95 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k95 . 1). 1) ((c3 . 1) . 1)) nil) (leq (((!_k95 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k96 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k96 . 1) . 1) ((c3 .1) . -1)) nil)) (and (geq (((!_k96 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k96. 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k97 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k97 . 1) . 1) ((c2 . 1) ((c3 . 3) .-1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k97 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k97 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 .1) . -1))) nil)))) (or (and (leq (((!_k98 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k98 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k98 . 1) . 1) ((c3 . 1) .1)) nil) (leq (((!_k98 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k99. 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k99 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k99 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k99 . 1) . 1) ((c3 .1) . -1)) nil)))) (ball !_k99 (ball !_k98 (ball !_k97 (ball !_k96 (ball !_k95 (ball !_k93 (ball !_k62 (ball !_k61 (ball !_k59 (ball !_k54 (ball !_k50 (ball!_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((!_k93 . 1) . 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) (equal (((!_k59 . 1) . 1) ((!_k93 . 1) . 1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k59 . 1) . 1) ((!_k93 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1. 1) ((c2 . 1) . -1))) nil) ((ncong ((c2 . 1) ((c3 . 2) . 1))) (((!_k59 . 1) ((c2 . 1) ((c3 . 1) . 1)))) nil) (neq (((!_k50 . 1) . 1)) nil) (neq (((!_k4 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((!_k59 . 1) . 1) ((!_k93 . 1) ((c2 . 1) . -1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1) nil))) (or (and(leq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k50 . 1) . 1) ((c3 . 1) .-1)) nil)) (and (geq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k50 . 1). 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k54 . 1) . 1) ((c3 . 1) . 1))nil) (geq (((!_k54 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k54 . 1) . 1)((c3 . 1) . 1)) nil) (leq (((!_k54 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)))) (or (and (leq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k61 . 1) . 1) ((c3 . 1) . -1))nil)) (and (geq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k61 . 1) . 1)((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k62 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k62 . 1) . 1) ((c3. 1) . 1)) nil) (leq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)))) (and (geq (((!_k93 . 1) . 1) ((!_k97 . 1) . 1) ((c2 . 2) ((c3 . 2) . 1)) . 1) nil) (leq (((!_k93 . 1) . 1) ((!_k97 . 1) . 1) ((c2 . 2) ((c3 . 2) . -1)) . -1) nil))) (or (and (leq (((!_k95 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k95 . 1) . 1) ((c3 .1) . -1)) nil)) (and (geq (((!_k95 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k95. 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k96 . 1) . 1) ((c3 . 1) .1)) nil) (geq (((!_k96 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k96 . 1). 1) ((c3 . 1) . 1)) nil) (leq (((!_k96 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k97 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq(((!_k97 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k97 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k97 .1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)))) (or (and (leq (((!_k98 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k98 . 1) . 1) ((c3 . 1) . -1))nil)) (and (geq (((!_k98 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k98 . 1) . 1)((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k99 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k99 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k99 . 1) . 1) ((c3. 1) . 1)) nil) (leq (((!_k99 . 1) . 1) ((c3 . 1) . -1)) nil)))) (ball !_k99 (ball !_k98 (ball !_k97 (ball !_k96 (ball !_k95 (ball !_k93 (ball !_k62 (ball!_k61 (ball !_k59 (ball !_k54 (ball !_k50 (ball !_k4 (or (equal (((c3 . 1) . 1))nil) (equal (((c2 . 1) . 1)) nil) (equal (((!_k93 . 1) . 1)) nil) (equal (((!_k59 . 1) . 1) ((!_k93 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k59 . 1) . 1) ((!_k93 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) . 1) ((c1 . 1) ((c2 . 1) . -1) . -1)) nil) ((ncong ((c2. 1) ((c3 . 2) . 1))) (((!_k59 . 1) ((c2 . 1) ((c3 . 1) . 1)))) nil) (neq (((!_k50 . 1) . 1)) nil) (neq (((!_k4 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((!_k59 . 1). 1) ((!_k93 . 1) ((c2 . 1) . -1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1). -1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) .-1) nil))) (or (and (leq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k50 .1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil)(leq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k54 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq(((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k54 . 1) . 1) ((c3 . 1) . -1))nil)))) (or (and (leq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)))) (or (and (leq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k61 . 1) . 1) ((c3 .1) . -1)) nil)) (and (geq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k61. 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k62 . 1) . 1) ((c3 . 1) .1)) nil) (geq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k62 . 1). 1) ((c3 . 1) . 1)) nil) (leq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)))) (and(geq (((!_k93 . 1) . 1) ((c2 . 2) ((c3 . 2) . 1)) . 1) nil) (leq (((!_k93 . 1) .1) ((c2 . 2) ((c3 . 2) . -1)) . -1) nil))) (or (and (leq (((!_k95 . 1) . 1) ((c3. 1) . 1)) nil) (geq (((!_k95 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k95 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k95 . 1) . 1) ((c3 . 1) . -1))nil)))) (or (and (leq (((!_k96 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k96 . 1). 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k96 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k96 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k97 . 1) . 1)((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k97 . 1) . 1) ((c2 . 1)((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k97 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k97 . 1) . 1) ((c2 . 1) ((c3 . 3). -1) ((c3 . 1) . -1))) nil)))) (or (and (leq (((!_k98 . 1) . 1) ((c3 . 1) . 1))nil) (geq (((!_k98 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k98 . 1) . 1)((c3 . 1) . 1)) nil) (leq (((!_k98 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k99 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k99 . 1) . 1) ((c3 . 1) .-1)) nil)) (and (geq (((!_k99 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k99 . 1). 1) ((c3 . 1) . -1)) nil)))) (ball !_k85 (ball !_k84 (ball !_k83 (ball !_k82 (ball !_k81 (ball !_k80 (ball !_k79 (ball !_k62 (ball !_k61 (ball !_k59 (ball!_k54 (ball !_k50 (ball !_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((!_k79 .1) . 1)) nil) (equal (((!_k59 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k59 .1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c3 . 2) .1)) (((!_k59 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((!_k79 . 1) ((c3 . 1) . -1)) ((c0. 1) ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) ((c1 . 1) ((c3 . 1) . 1))) nil)(neq (((!_k50 . 1) . 1)) nil) (neq (((!_k4 . 1) ((c3 . 1) . 1)) ((!_k59 . 1) . 1) ((!_k79 . 1) . -1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1) nil))) (or (and (leq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k54 . 1) . 1) ((c3 . 1) .-1)) nil)) (and (geq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k54 . 1). 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k59 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k59 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k59 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k59. 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k61 . 1) .1) ((c3 . 1) . 1)) nil) (geq (((!_k61 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq(((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k61 . 1) . 1) ((c3 . 1) . -1))nil)))) (or (and (leq (((!_k62 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k62 . 1). 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k62 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)))) (equal (((!_k79 . 1) . 1) ((!_k80 . 1) ((c3 . 1) . -1)) ((!_k83 . 1) . -1)) nil)) (or (equal (((!_k80 . 1) .1) . 1) nil) (equal (((!_k80 . 1) . 1) . -1) nil))) (or (and (leq (((!_k81 . 1). 1) ((c3 . 1) . 1)) nil) (geq (((!_k81 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k81 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k81 . 1) . 1) ((c3 . 1) .-1)) nil)))) (or (and (leq (((!_k82 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k82. 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k82 . 1) . 1) ((c3 . 1) . 1))nil) (leq (((!_k82 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k83 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k83 . 1) . 1) ((c3 . 3) .-1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k83 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1). 1)) nil) (leq (((!_k83 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)))) (or(and (leq (((!_k84 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k84 . 1) . 1) ((c3 .1) . -1)) nil)) (and (geq (((!_k84 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k84. 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k85 . 1) . 1) ((c3 . 1) .1)) nil) (geq (((!_k85 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k85 . 1). 1) ((c3 . 1) . 1)) nil) (leq (((!_k85 . 1) . 1) ((c3 . 1) . -1)) nil)))) (ball!_k78 (ball !_k77 (ball !_k76 (ball !_k75 (ball !_k74 (ball !_k73 (ball !_k71 (ball !_k62 (ball !_k61 (ball !_k60 (ball !_k59 (ball !_k54 (ball !_k50 (ball!_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((!_k71 . 1) . 1) ((c0 . 1) ((c2 .1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k59 . 1) . 1) ((!_k71 . 1) . 1)) nil) (equal (((!_k59 . 1) . 1) ((!_k71 . 1) . 1) ((c0 . 1) ((c2. 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c3 . 2) . 1)) (((!_k59 . 1) ((c2. 1) ((c3 . 1) . 1))) ((!_k71 . 1) ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) ((c0 . 1) ((c2 . 2) ((c3 . 1) . 1)) ((c2 . 1) ((c3 . 1) . -1))) ((c1 . 1) ((c2 . 1) ((c3 . 1) . 1)))) nil) (neq (((!_k50 . 1) . 1)) nil) (neq (((!_k4 . 1) ((c3 .1) . 1)) ((!_k59 . 1) . 1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal(((!_k4 . 1) . 1) . -1) nil))) (or (and (leq (((!_k50 . 1) . 1) ((c3 . 1) . 1))nil) (geq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k50 . 1) . 1)((c3 . 1) . 1)) nil) (leq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k54 . 1) . 1) ((c3 . 1) .-1)) nil)) (and (geq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k54 . 1). 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k59 . 1) . 1) ((!_k60 . 1) ((c3. 1) . 1)) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k59 . 1) . 1) ((!_k60 .1) ((c3 . 1) . 1)) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k59 . 1) . 1) ((!_k60 . 1) ((c3 . 1) . 1)) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k59 . 1) . 1) ((!_k60 . 1) ((c3 . 1) . 1)) ((c3 . 3) . -1) ((c3 . 1) . -1))nil)))) (or (equal (((!_k60 . 1) . 1) . 1) nil) (equal (((!_k60 . 1) . 1) . -1)nil))) (or (and (leq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k61 . 1). 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k61 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k62 . 1) . 1)((c3 . 1) . 1)) nil) (geq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k62 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k62 . 1) . 1) ((c3 . 1) . -1))nil)))) (and (geq (((!_k71 . 1) . 1) ((!_k75 . 1) . 1) ((c3 . 6) . 1) ((c3 . 4). 1) ((c3 . 2) . 1) . 1) nil) (leq (((!_k71 . 1) . 1) ((!_k75 . 1) . 1) ((c3 . 6) . -1) ((c3 . 4) . -1) ((c3 . 2) . -1) . -1) nil))) (or (and (leq (((!_k73 . 1). 1) ((c3 . 1) . 1)) nil) (geq (((!_k73 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k73 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k73 . 1) . 1) ((c3 . 1) .-1)) nil)))) (or (and (leq (((!_k74 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k74. 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k74 . 1) . 1) ((c3 . 1) . 1))nil) (leq (((!_k74 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k75 . 1) . 1) ((!_k76 . 1) ((c3 . 1) . 1)) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k75 . 1) . 1) ((!_k76 . 1) ((c3 . 1) . 1)) ((c3 . 3) . -1) ((c3 . 1) . -1))nil)) (and (geq (((!_k75 . 1) . 1) ((!_k76 . 1) ((c3 . 1) . 1)) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k75 . 1) . 1) ((!_k76 . 1) ((c3 . 1) . 1)) ((c3 .3) . -1) ((c3 . 1) . -1)) nil)))) (or (equal (((!_k76 . 1) . 1) . 1) nil) (equal(((!_k76 . 1) . 1) . -1) nil))) (or (and (leq (((!_k77 . 1) . 1) ((c3 . 1) . 1))nil) (geq (((!_k77 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k77 . 1) . 1)((c3 . 1) . 1)) nil) (leq (((!_k77 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k78 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k78 . 1) . 1) ((c3 . 1) .-1)) nil)) (and (geq (((!_k78 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k78 . 1). 1) ((c3 . 1) . -1)) nil)))) (ball !_k78 (ball !_k77 (ball !_k76 (ball !_k75 (ball !_k74 (ball !_k73 (ball !_k71 (or (ball !_k62 (ball !_k61 (ball !_k60 (ball!_k59 (ball !_k54 (ball !_k50 (ball !_k4 (or (equal (((!_k71 . 1) . 1) ((c0 . 1)((c2 . 1) ((c3 . 1) . -1)) ((c3 . 1) . 1)) ((c1 . 1) ((c3 . 1) . -1))) nil) (equal (((!_k59 . 1) ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) ((!_k71 . 1) . 1)((c0 . 1) ((c2 . 1) ((c3 . 1) . -1)) ((c3 . 1) . 1)) ((c1 . 1) ((c3 . 1) . -1)))nil) ((ncong ((c2 . 1) ((c3 . 2) . 1)) ((c3 . 2) . -1)) (((!_k59 . 1) ((c2 . 1)((c3 . 1) . 1)) ((c3 . 1) . -1)) ((!_k71 . 1) . 1) ((c0 . 1) ((c2 . 2) ((c3 . 1). -1)) ((c2 . 1) ((c3 . 1) . 1))) ((c1 . 1) ((c2 . 1) ((c3 . 1) . -1)))) nil) ((ncong ((c2 . 1) ((c3 . 3) . 1)) ((c3 . 3) . -1)) (((!_k59 . 1) ((c2 . 2) ((c3 .2) . 1)) ((c2 . 1) ((c3 . 2) . -1))) ((!_k71 . 1) ((c2 . 1) ((c3 . 1) . 1)) ((c3. 1) . -1))) nil) (neq (((!_k50 . 1) . 1)) nil) (neq (((!_k4 . 1) ((c3 . 1) . 1)) ((!_k59 . 1) . 1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4. 1) . 1) . -1) nil))) (or (and (leq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k50 . 1) . 1) ((c3. 1) . 1)) nil) (leq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k54 . 1) . 1) ((c3 . 1) . -1))nil)) (and (geq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k54 . 1) . 1)((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k59 . 1) . 1) ((!_k60 . 1) ((c3 . 1). 1)) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k59 . 1) . 1) ((!_k60 . 1) ((c3 . 1) . 1)) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k59 . 1) .1) ((!_k60 . 1) ((c3 . 1) . 1)) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k59 . 1) . 1) ((!_k60 . 1) ((c3 . 1) . 1)) ((c3 . 3) . -1) ((c3 . 1) . -1))nil)))) (or (equal (((!_k60 . 1) . 1) . 1) nil) (equal (((!_k60 . 1) . 1) . -1)nil))) (or (and (leq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k61 . 1). 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k61 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k62 . 1) . 1)((c3 . 1) . 1)) nil) (geq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k62 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k62 . 1) . 1) ((c3 . 1) . -1))nil)))) (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1) . -1) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) (((!_k71 . 1) . 1) ((c1 . 1) ((c3 . 1). -1))) nil)) (or (and (leq (((!_k71 . 1) . 1) ((!_k75 . 1) ((c2 . 1) ((c3 . 1). 1))) ((c2 . 1) ((c3 . 7) . 1) ((c3 . 5) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) ((c3 . 7) . -1) ((c3 . 5) . -1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (geq (((!_k71 . 1) . 1) ((!_k75 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c2 . 1) ((c3 . 7) . -1) ((c3 . 5) . -1) ((c3 . 3) . -1) ((c3 . 1) . -1)) ((c3 . 7) . 1) ((c3 . 5) . 1)((c3 . 3) . 1) ((c3 . 1) . 1)) nil)) (and (geq (((!_k71 . 1) . 1) ((!_k75 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c2 . 1) ((c3 . 7) . 1) ((c3 . 5) . 1) ((c3 . 3) . 1)((c3 . 1) . 1)) ((c3 . 7) . -1) ((c3 . 5) . -1) ((c3 . 3) . -1) ((c3 . 1) . -1))nil) (leq (((!_k71 . 1) . 1) ((!_k75 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c2 . 1) ((c3 . 7) . -1) ((c3 . 5) . -1) ((c3 . 3) . -1) ((c3 . 1) . -1)) ((c3 . 7) . 1) ((c3 . 5) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil)))) (or (and (leq (((!_k73 . 1). 1) ((c3 . 1) . 1)) nil) (geq (((!_k73 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k73 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k73 . 1) . 1) ((c3 . 1) .-1)) nil)))) (or (and (leq (((!_k74 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k74. 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k74 . 1) . 1) ((c3 . 1) . 1))nil) (leq (((!_k74 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k75 . 1) . 1) ((!_k76 . 1) ((c3 . 1) . 1)) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k75 . 1) . 1) ((!_k76 . 1) ((c3 . 1) . 1)) ((c3 . 3) . -1) ((c3 . 1) . -1))nil)) (and (geq (((!_k75 . 1) . 1) ((!_k76 . 1) ((c3 . 1) . 1)) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k75 . 1) . 1) ((!_k76 . 1) ((c3 . 1) . 1)) ((c3 .3) . -1) ((c3 . 1) . -1)) nil)))) (or (equal (((!_k76 . 1) . 1) . 1) nil) (equal(((!_k76 . 1) . 1) . -1) nil))) (or (and (leq (((!_k77 . 1) . 1) ((c3 . 1) . 1))nil) (geq (((!_k77 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k77 . 1) . 1)((c3 . 1) . 1)) nil) (leq (((!_k77 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k78 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k78 . 1) . 1) ((c3 . 1) .-1)) nil)) (and (geq (((!_k78 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k78 . 1). 1) ((c3 . 1) . -1)) nil)))) (ball !_k78 (ball !_k77 (ball !_k76 (ball !_k75 (ball !_k74 (ball !_k73 (ball !_k71 (ball !_k62 (ball !_k61 (ball !_k60 (ball!_k59 (ball !_k54 (ball !_k50 (ball !_k4 (or (equal (((c3 . 1) . 1)) nil) (equal(((!_k71 . 1) . 1)) nil) (equal (((!_k59 . 1) . 1) ((!_k71 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k59 . 1) . 1) ((!_k71 . 1) . 1) ((c0 . 1) ((c2 . 1) .-1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c3 . 2) . 1)) (((!_k59 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((!_k71 . 1) ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) ((c0 . 1) ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) ((c1 . 1) ((c3 . 1) . 1))) nil) (neq (((!_k50 . 1) . 1)) nil) (neq (((!_k4 . 1) ((c3 . 1) . 1)) ((!_k59 . 1) . 1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1)nil))) (or (and (leq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k50 . 1). 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k54 . 1) . 1)((c3 . 1) . 1)) nil) (geq (((!_k54 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k54 . 1) . 1) ((c3 . 1) . -1))nil)))) (or (and (leq (((!_k59 . 1) . 1) ((!_k60 . 1) ((c3 . 1) . 1)) ((c3 . 3). 1) ((c3 . 1) . 1)) nil) (geq (((!_k59 . 1) . 1) ((!_k60 . 1) ((c3 . 1) . 1)) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k59 . 1) . 1) ((!_k60 . 1)((c3 . 1) . 1)) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k59 . 1) . 1) ((!_k60 . 1) ((c3 . 1) . 1)) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)))) (or (equal (((!_k60 . 1) . 1) . 1) nil) (equal (((!_k60 . 1) . 1) . -1) nil))) (or (and (leq(((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k61 . 1) . 1) ((c3 . 1) . -1))nil)) (and (geq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k61 . 1) . 1)((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k62 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k62 . 1) . 1) ((c3. 1) . 1)) nil) (leq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (geq (((!_k71 . 1) . 1) ((!_k75 . 1) . 1) ((c3 . 6) . 1) ((c3 . 4) . 1) ((c3 . 2) . 1). 1) nil) (leq (((!_k71 . 1) . 1) ((!_k75 . 1) . 1) ((c3 . 6) . -1) ((c3 . 4) .-1) ((c3 . 2) . -1) . -1) nil)) (and (geq (((!_k71 . 1) . 1) ((c3 . 6) . 1) ((c3. 4) . 1) ((c3 . 2) . 1) . 1) nil) (leq (((!_k71 . 1) . 1) ((c3 . 6) . -1) ((c3. 4) . -1) ((c3 . 2) . -1) . -1) nil)))) (or (and (leq (((!_k73 . 1) . 1) ((c3 .1) . 1)) nil) (geq (((!_k73 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k73. 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k73 . 1) . 1) ((c3 . 1) . -1)) nil))))(or (and (leq (((!_k74 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k74 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k74 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k74 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k75 . 1) . 1) ((!_k76 . 1) ((c3 . 1) . 1)) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k75 . 1) . 1) ((!_k76 . 1) ((c3 . 1) . 1)) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)) (and(geq (((!_k75 . 1) . 1) ((!_k76 . 1) ((c3 . 1) . 1)) ((c3 . 3) . 1) ((c3 . 1) .1)) nil) (leq (((!_k75 . 1) . 1) ((!_k76 . 1) ((c3 . 1) . 1)) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)))) (or (equal (((!_k76 . 1) . 1) . 1) nil) (equal (((!_k76 .1) . 1) . -1) nil))) (or (and (leq (((!_k77 . 1) . 1) ((c3 . 1) . 1)) nil) (geq(((!_k77 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k77 . 1) . 1) ((c3 . 1). 1)) nil) (leq (((!_k77 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k78 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k78 . 1) . 1) ((c3 . 1) . -1))nil)) (and (geq (((!_k78 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k78 . 1) . 1)((c3 . 1) . -1)) nil)))) (ball !_k62 (ball !_k61 (ball !_k60 (ball !_k59 (ball!_k54 (ball !_k50 (ball !_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((c0 . 1). 1)) nil) (equal (((!_k59 . 1) . 1) ((c0 . 1) . -1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k59 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1)) ((c1 . 1) . -1)) nil) ((ncong ((c3 . 2) . 1)) (((!_k59 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c1 . 1) ((c3 . 1) . 1))) nil) (neq (((!_k50 . 1) . 1)) nil) (neq (((!_k4 . 1) ((c3 . 1) . 1)) ((!_k59. 1) . 1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1). -1) nil))) (or (and (leq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k50. 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k50 . 1) . 1) ((c3 . 1) . 1))nil) (leq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k54 . 1) . 1) ((c3 . 1) . -1)) nil)) (and(geq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k54 . 1) . 1) ((c3 . 1) .-1)) nil)))) (or (and (leq (((!_k59 . 1) . 1) ((!_k60 . 1) ((c3 . 1) . 1)) ((c3. 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k59 . 1) . 1) ((!_k60 . 1) ((c3 . 1) .1)) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k59 . 1) . 1) ((!_k60. 1) ((c3 . 1) . 1)) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k59 . 1) . 1)((!_k60 . 1) ((c3 . 1) . 1)) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)))) (or (equal(((!_k60 . 1) . 1) . 1) nil) (equal (((!_k60 . 1) . 1) . -1) nil))) (or (and (leq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k61 . 1) . 1) ((c3 . 1) .-1)) nil)) (and (geq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k61 . 1). 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k62 . 1) . 1) ((c3 . 1) . 1))nil) (geq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k62 . 1) . 1)((c3 . 1) . 1)) nil) (leq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)))) (ball!_k62 (ball !_k61 (ball !_k59 (ball !_k54 (ball !_k50 (ball !_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((c0 . 1) . 1)) nil) (equal (((!_k59 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1)) ((c1 . 1) . -1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k59 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1)) ((c1 . 1) ((c2 . 1) . -1) . -1)) nil) ((ncong ((c2 . 1) ((c3 . 2) . 1))) (((!_k59. 1) ((c2 . 1) ((c3 . 1) . 1)))) nil) (neq (((!_k50 . 1) . 1)) nil) (neq (((!_k4. 1) ((c2 . 1) ((c3 . 1) . 1))) ((!_k59 . 1) . 1) ((c1 . 1) . -1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1) nil))) (or (and(leq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k50 . 1) . 1) ((c3 . 1) .-1)) nil)) (and (geq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k50 . 1). 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k54 . 1) . 1) ((c3 . 1) . 1))nil) (geq (((!_k54 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k54 . 1) . 1)((c3 . 1) . 1)) nil) (leq (((!_k54 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k59 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)))) (or (and (leq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k61 . 1) . 1) ((c3 . 1) . -1))nil)) (and (geq (((!_k61 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k61 . 1) . 1)((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k62 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k62 . 1) . 1) ((c3. 1) . 1)) nil) (leq (((!_k62 . 1) . 1) ((c3 . 1) . -1)) nil)))) (ball !_k38 (ball !_k37 (or (ball !_k30 (or (equal (((c3 . 1) . 1)) nil) (equal (((!_k37 . 1). 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c2 . 1) ((c3. 1) . 1)) ((c3 . 1) . -1)) (((!_k37 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 .1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil) (neq (((!_k30 . 1) ((c2 . 1) . 1)) ((!_k37 . 1) . 1)) nil) (equal (((!_k30 . 1) ((c2 . 1) . 1) . -1) ((!_k37 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c2 . 1) ((c3 .1) . 1)) ((c3 . 1) . -1)) (((!_k30 . 1) ((c2 . 1) . 1) . -1) ((!_k37 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil)) (or (and (leq (((!_k30 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k30 . 1) . 1) ((c3 .1) . -1)) nil) (neq (((!_k30 . 1) . 1)) nil)) (and (geq (((!_k30 . 1) . 1) ((c3. 1) . 1)) nil) (leq (((!_k30 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k30 . 1). 1)) nil)))) (equal (((c2 . 1) . 1) . -1) nil) ((ncong ((c2 . 1) . 1) . -1) (((!_k37 . 1) . 1) ((c1 . 1) . -1)) nil)) (or (and (leq (((!_k37 . 1) . 1) ((!_k38. 1) ((c2 . 1) . 1)) ((c2 . 1) ((c3 . 2) . 1) . 1) ((c3 . 2) . -1) . -1) nil) (geq (((!_k37 . 1) . 1) ((!_k38 . 1) ((c2 . 1) . 1)) ((c2 . 1) ((c3 . 2) . -1) .-1) ((c3 . 2) . 1) . 1) nil)) (and (greaterp (((!_k37 . 1) . 1) ((!_k38 . 1) ((c2 . 1) . 1)) ((c2 . 1) ((c3 . 2) . 1) . 1) ((c3 . 2) . -1)) nil) (lessp (((!_k37 . 1) . 1) ((!_k38 . 1) ((c2 . 1) . 1)) ((c2 . 1) ((c3 . 2) . -1) . -1) ((c3 . 2) . 1)) nil)))) (or (and (leq (((!_k38 . 1) . 1) ((c3 . 1) . 1)) nil) (geq(((!_k38 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k38 . 1) . 1)) nil)) (and (geq (((!_k38 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k38 . 1) . 1) ((c3 . 1) .-1)) nil) (neq (((!_k38 . 1) . 1)) nil)))) (ball !_k38 (ball !_k37 (ball !_k30 (or (equal (((c3 . 1) . 1)) nil) (equal (((!_k37 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k37 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil)(equal (((!_k30 . 1) . 1) ((!_k37 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k30 . 1) . 1) ((!_k37 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) (neq (((!_k30 . 1) ((c2 . 1) . 1)) ((!_k37 . 1) ((c2 . 1) . 1) . -1) ((c0. 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil)) (or (and (leq (((!_k30 . 1) . 1)((c3 . 1) . 1)) nil) (geq (((!_k30 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k30. 1) . 1)) nil)) (and (geq (((!_k30 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k30. 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k30 . 1) . 1)) nil)))) (or (and (geq (((!_k37 . 1) . 1) ((!_k38 . 1) . 1) ((c3 . 2) . 1) . 1) nil) (leq (((!_k37 . 1). 1) ((!_k38 . 1) . 1) ((c3 . 2) . -1) . -1) nil)) (and (geq (((!_k37 . 1) . 1)((c3 . 2) . 1) . 1) nil) (leq (((!_k37 . 1) . 1) ((c3 . 2) . -1) . -1) nil)))) (or (and (leq (((!_k38 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k38 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k38 . 1) . 1)) nil)) (and (geq (((!_k38 . 1) . 1)((c3 . 1) . 1)) nil) (leq (((!_k38 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k38. 1) . 1)) nil)))) (ball !_k38 (ball !_k37 (ball !_k30 (or (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k37 . 1) . 1)) nil) (equal (((!_k37 . 1) .1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k30 . 1) . 1) ((!_k37 . 1) . 1)) nil) (equal (((!_k30 . 1) . 1) ((!_k37 . 1). 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) (neq (((!_k30 . 1) ((c2. 1) . 1)) ((!_k37 . 1) ((c2 . 1) . 1) . -1) ((c0 . 1) ((c2 . 2) . 1) ((c2 . 1). -1)) ((c1 . 1) ((c2 . 1) . 1))) nil)) (or (and (leq (((!_k30 . 1) . 1) ((c3 .1) . 1)) nil) (geq (((!_k30 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k30 . 1) .1)) nil)) (and (geq (((!_k30 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k30 . 1) .1) ((c3 . 1) . -1)) nil) (neq (((!_k30 . 1) . 1)) nil)))) (or (and (geq (((!_k37. 1) . 1) ((!_k38 . 1) . 1) ((c3 . 2) . 1) . 1) nil) (leq (((!_k37 . 1) . 1) ((!_k38 . 1) . 1) ((c3 . 2) . -1) . -1) nil)) (and (geq (((!_k37 . 1) . 1) ((c3 .2) . 1) . 1) nil) (leq (((!_k37 . 1) . 1) ((c3 . 2) . -1) . -1) nil)))) (or (and(leq (((!_k38 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k38 . 1) . 1) ((c3 . 1) .-1)) nil) (neq (((!_k38 . 1) . 1)) nil)) (and (geq (((!_k38 . 1) . 1) ((c3 . 1). 1)) nil) (leq (((!_k38 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k38 . 1) . 1)) nil)))) (ball !_k34 (ball !_k33 (ball !_k30 (or (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k33 . 1) . 1)) nil) (equal (((!_k33 . 1) . 1) ((c0 .1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k30 .1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) (equal (((!_k30 . 1) . 1) ((!_k33 . 1) . -1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) (neq (((!_k30 . 1) ((c2 . 1) . 1)) ((!_k33 . 1) . -1)) nil)) (or (and (leq (((!_k30 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k30 . 1) . 1) ((c3 . 1) . -1))nil) (neq (((!_k30 . 1) . 1)) nil)) (and (geq (((!_k30 . 1) . 1) ((c3 . 1) . 1))nil) (leq (((!_k30 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k30 . 1) . 1)) nil)))) (equal (((!_k33 . 1) . 1) ((!_k34 . 1) ((c2 . 1) . -1))) nil)) (or (and (leq(((!_k34 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k34 . 1) . 1) ((c3 . 1) . -1))nil) (neq (((!_k34 . 1) . 1)) nil)) (and (geq (((!_k34 . 1) . 1) ((c3 . 1) . 1))nil) (leq (((!_k34 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k34 . 1) . 1)) nil)))) (ball !_k32 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k32 . 1) . 1)) nil) (equal (((!_k32 . 1) .1) ((c0 . 1) ((c2 . 2) . 1) . -1) ((c1 . 1) ((c2 . 1) . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k32 . 1) . 1) ((c0 . 1) ((c2 . 2) . 1) ((c2 . 1) . -1)) ((c1. 1) ((c2 . 1) . 1))) nil) (equal (((!_k32 . 1) . 1) ((c0 . 1) ((c2 . 2) . 1) ((c2 . 1) . -1)) ((c1 . 1) ((c2 . 1) . 1))) nil) (equal (((!_k32 . 1) ((c2 . 1) .1) . -1) ((c0 . 1) ((c2 . 3) . 1) ((c2 . 2) . -1)) ((c1 . 1) ((c2 . 2) . 1)))nil)) (and (geq (((!_k32 . 1) . 1) ((c2 . 2) ((c3 . 4) . 1) ((c3 . 2) . 1)) ((c3. 2) . 1) . 1) nil) (leq (((!_k32 . 1) . 1) ((c2 . 2) ((c3 . 4) . -1) ((c3 . 2). -1)) ((c3 . 2) . -1) . -1) nil))) (ball !_k32 (or (equal (((c3 . 1) . 1)) nil)(equal (((c2 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k32 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) (equal (((!_k32 . 1) . 1) ((c0 . 1)((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k32 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) . 1) ((c1 . 1) ((c2 . 1) . -1) . -1))nil) (equal (((!_k32 . 1) ((c2 . 1) . 1) . -1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil)) (and (geq (((!_k32 . 1) . 1) ((c2 . 2) ((c3 . 4) . 1) ((c3 .2) . 1)) ((c3 . 2) . 1) . 1) nil) (leq (((!_k32 . 1) . 1) ((c2 . 2) ((c3 . 4) .-1) ((c3 . 2) . -1)) ((c3 . 2) . -1) . -1) nil) (neq (((!_k32 . 1) . 1)) nil)))(ball !_k32 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k32 . 1) . 1)) nil) (equal (((!_k32 . 1) . 1) ((c0 .1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1)))(((!_k32 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1). -1))) nil) (equal (((!_k32 . 1) ((c2 . 1) . 1) . -1) ((c0 . 1) ((c2 . 2) . 1)((c2 . 1) . -1)) ((c1 . 1) ((c2 . 1) . 1))) nil)) (and (geq (((!_k32 . 1) . 1) ((c2 . 2) ((c3 . 4) . 1) ((c3 . 2) . 1)) ((c3 . 2) . 1) . 1) nil) (leq (((!_k32 .1) . 1) ((c2 . 2) ((c3 . 4) . -1) ((c3 . 2) . -1)) ((c3 . 2) . -1) . -1) nil) (neq (((!_k32 . 1) . 1)) nil))) (ball !_k32 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((c2 . 1) . 1) . -1) nil) ((ncong ((c2 . 1). 1) . -1) (((!_k32 . 1) . 1) ((c1 . 1) . -1)) nil) (equal (((!_k32 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c2 . 1) ((c3 . 1) .1)) ((c3 . 1) . -1)) (((!_k32 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil) (equal (((!_k32 . 1) . 1) ((c0 . 1) ((c2 . 2). -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil) ((ncong ((c2 . 2) ((c3 .1) . 1)) ((c2 . 1) ((c3 . 1) . -1))) (((!_k32 . 1) . 1) ((c0 . 1) ((c2 . 3) . -1) ((c2 . 2) . 1)) ((c1 . 1) ((c2 . 2) . -1))) nil)) (or (and (leq (((!_k32 . 1). 1) ((c2 . 3) ((c3 . 4) . 1) ((c3 . 2) . 1)) ((c2 . 2) ((c3 . 4) . -1) ((c3 . 2) . -1)) ((c2 . 1) ((c3 . 2) . 1) . 1) ((c3 . 2) . -1) . -1) nil) (geq (((!_k32. 1) . 1) ((c2 . 3) ((c3 . 4) . -1) ((c3 . 2) . -1)) ((c2 . 2) ((c3 . 4) . 1) ((c3 . 2) . 1)) ((c2 . 1) ((c3 . 2) . -1) . -1) ((c3 . 2) . 1) . 1) nil) (neq (((!_k32 . 1) . 1)) nil)) (and (greaterp (((!_k32 . 1) . 1) ((c2 . 3) ((c3 . 4) . 1) ((c3 . 2) . 1)) ((c2 . 2) ((c3 . 4) . -1) ((c3 . 2) . -1)) ((c2 . 1) ((c3 . 2). 1) . 1) ((c3 . 2) . -1)) nil) (lessp (((!_k32 . 1) . 1) ((c2 . 3) ((c3 . 4) .-1) ((c3 . 2) . -1)) ((c2 . 2) ((c3 . 4) . 1) ((c3 . 2) . 1)) ((c2 . 1) ((c3 . 2) . -1) . -1) ((c3 . 2) . 1)) nil) (neq (((!_k32 . 1) . 1)) nil)))) (ball !_k30(or (equal (((c3 . 1) . 1)) nil) (equal (((c0 . 1) . 1)) nil) ((ncong ((c3 . 1). 1)) (((c0 . 1) ((c2 . 1) . 1)) ((c1 . 1) . 1)) nil) (equal (((!_k30 . 1) . 1)((c0 . 1) . -1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k30 . 1) . 1) ((c0 . 1) ((c2. 1) . -1)) ((c1 . 1) . -1)) nil) (neq (((!_k30 . 1) ((c2 . 1) . 1)) ((c1 . 1) .1)) nil)) (or (and (leq (((!_k30 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k30 .1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k30 . 1) . 1)) nil)) (and (geq (((!_k30. 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k30 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k30 . 1) . 1)) nil)))) (ball !_k27 (or (equal (((c3 . 1) . 1)) nil) (equal (((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k27 . 1) . 1)) nil) (equal (((!_k27 . 1) . 1) ((c0 . 1) ((c2 . 2) . 1) .-1) ((c1 . 1) ((c2 . 1) . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k27 . 1) .1) ((c0 . 1) ((c2 . 2) . 1) ((c2 . 1) . -1)) ((c1 . 1) ((c2 . 1) . 1))) nil) (equal (((!_k27 . 1) . 1) ((c0 . 1) ((c2 . 2) . 1) ((c2 . 1) . -1)) ((c1 . 1) ((c2 . 1) . 1))) nil)) (and (geq (((!_k27 . 1) . 1) ((c3 . 2) . 1) . 1) nil) (leq(((!_k27 . 1) . 1) ((c3 . 2) . -1) . -1) nil))) (ball !_k27 (or (equal (((c3 . 1) . 1)) nil) (equal (((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong((c3 . 1) . 1)) (((!_k27 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) (equal (((!_k27 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k27 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) . 1)((c1 . 1) ((c2 . 1) . -1) . -1)) nil)) (and (geq (((!_k27 . 1) . 1) ((c3 . 2) .1) . 1) nil) (leq (((!_k27 . 1) . 1) ((c3 . 2) . -1) . -1) nil) (neq (((!_k27 .1) . 1)) nil))) (ball !_k27 (or (equal (((c3 . 1) . 1)) nil) (equal (((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k27 . 1) .1)) nil) (equal (((!_k27 . 1) . 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k27 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2. 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil)) (and (geq (((!_k27 . 1) . 1) ((c3 .2) . 1) . 1) nil) (leq (((!_k27 . 1) . 1) ((c3 . 2) . -1) . -1) nil) (neq (((!_k27 . 1) . 1)) nil))) (ball !_k25 (ball !_k24 (or (ball !_k13 (or (equal (((!_k24 . 1) . 1) ((c0 . 1) ((c2 . 1) ((c3 . 1) . -1)) ((c3 . 1) . 1)) ((c1 . 1) ((c3 . 1) . -1))) nil) ((ncong ((c2 . 1) ((c3 . 2) . 1)) ((c3 . 2) . -1)) (((!_k24 . 1) . 1) ((c0 . 1) ((c2 . 2) ((c3 . 1) . -1)) ((c2 . 1) ((c3 . 1) . 1)))((c1 . 1) ((c2 . 1) ((c3 . 1) . -1)))) nil) (equal (((!_k13 . 1) ((c2 . 1) ((c3. 1) . 1)) ((c3 . 1) . -1)) ((!_k24 . 1) . 1) ((c0 . 1) ((c2 . 1) ((c3 . 1) . -1)) ((c3 . 1) . 1)) ((c1 . 1) ((c3 . 1) . -1))) nil) ((ncong ((c2 . 1) ((c3 . 2). 1)) ((c3 . 2) . -1)) (((!_k13 . 1) ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1))((!_k24 . 1) . 1) ((c0 . 1) ((c2 . 2) ((c3 . 1) . -1)) ((c2 . 1) ((c3 . 1) . 1))) ((c1 . 1) ((c2 . 1) ((c3 . 1) . -1)))) nil) ((ncong ((c2 . 1) ((c3 . 3) . 1))((c3 . 3) . -1)) (((!_k13 . 1) ((c2 . 2) ((c3 . 2) . 1)) ((c2 . 1) ((c3 . 2) .-1))) ((!_k24 . 1) ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1))) nil)) (or (and (leq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k13 . 1) .1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)) (and (geq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k13 . 1) .1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)))) (equal(((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1) . -1) nil) ((ncong ((c2 . 1) ((c3 .1) . 1)) ((c3 . 1) . -1)) (((!_k24 . 1) . 1) ((c1 . 1) ((c3 . 1) . -1))) nil)) (or (and (leq (((!_k24 . 1) . 1) ((!_k25 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c2 . 1) ((c3 . 7) . 1) ((c3 . 5) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) ((c3 . 7) . -1) ((c3 . 5) . -1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (geq (((!_k24 . 1) . 1) ((!_k25 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c2 . 1) ((c3 . 7) . -1) ((c3 . 5) . -1)((c3 . 3) . -1) ((c3 . 1) . -1)) ((c3 . 7) . 1) ((c3 . 5) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil)) (and (geq (((!_k24 . 1) . 1) ((!_k25 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c2 . 1) ((c3 . 7) . 1) ((c3 . 5) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))((c3 . 7) . -1) ((c3 . 5) . -1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (leq (((!_k24 . 1) . 1) ((!_k25 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c2 . 1) ((c3 . 7) . -1) ((c3 . 5) . -1) ((c3 . 3) . -1) ((c3 . 1) . -1)) ((c3 . 7) . 1) ((c3 . 5) . 1)((c3 . 3) . 1) ((c3 . 1) . 1)) nil)))) (or (and (leq (((!_k25 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k25 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) .-1)) nil) (neq (((!_k25 . 1) . 1)) nil)) (and (geq (((!_k25 . 1) . 1) ((c3 . 3). 1) ((c3 . 1) . 1)) nil) (leq (((!_k25 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k25 . 1) . 1)) nil)))) (ball !_k25 (ball !_k24 (ball !_k13 (or(equal (((c3 . 1) . 1)) nil) (equal (((!_k24 . 1) . 1)) nil) ((ncong ((c3 . 1) .1)) (((!_k24 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) (equal (((!_k13 . 1) . 1) ((!_k24 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k13 . 1) . 1) ((!_k24 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c3 . 2) . 1)) (((!_k13 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((!_k24. 1) ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) ((c0 . 1) ((c2 . 1) ((c3 . 1) .1)) ((c3 . 1) . -1)) ((c1 . 1) ((c3 . 1) . 1))) nil)) (or (and (leq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k13 . 1) . 1) ((c3 . 3) .-1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)) (and (geq (((!_k13 . 1). 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k13 . 1) . 1) ((c3 . 3) . -1)((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)))) (or (and (geq (((!_k24 .1) . 1) ((!_k25 . 1) . 1) ((c3 . 6) . 1) ((c3 . 4) . 1) ((c3 . 2) . 1) . 1) nil)(leq (((!_k24 . 1) . 1) ((!_k25 . 1) . 1) ((c3 . 6) . -1) ((c3 . 4) . -1) ((c3 .2) . -1) . -1) nil)) (and (geq (((!_k24 . 1) . 1) ((c3 . 6) . 1) ((c3 . 4) . 1)((c3 . 2) . 1) . 1) nil) (leq (((!_k24 . 1) . 1) ((c3 . 6) . -1) ((c3 . 4) . -1)((c3 . 2) . -1) . -1) nil)))) (or (and (leq (((!_k25 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k25 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)(neq (((!_k25 . 1) . 1)) nil)) (and (geq (((!_k25 . 1) . 1) ((c3 . 3) . 1) ((c3. 1) . 1)) nil) (leq (((!_k25 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k25 . 1) . 1)) nil)))) (ball !_k25 (ball !_k24 (ball !_k13 (or (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k24 . 1) . 1)) nil) (equal (((!_k24 . 1) . 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c3. 1) . 1)) (((!_k13 . 1) . 1) ((!_k24 . 1) . 1)) nil) (equal (((!_k13 . 1) . 1)((!_k24 . 1) . 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c3 . 2) . 1)) (((!_k13 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((!_k24 . 1) ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) ((c0 . 1) ((c2 . 2) ((c3 . 1) . 1)) ((c2 . 1) ((c3 . 1) . -1))) ((c1 . 1) ((c2 . 1) ((c3 . 1) . 1)))) nil)) (or (and (leq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k13 . 1) . 1) ((c3. 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)) (and (geq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k13 . 1) . 1) ((c3. 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)))) (or (and (geq(((!_k24 . 1) . 1) ((!_k25 . 1) . 1) ((c3 . 6) . 1) ((c3 . 4) . 1) ((c3 . 2) . 1) . 1) nil) (leq (((!_k24 . 1) . 1) ((!_k25 . 1) . 1) ((c3 . 6) . -1) ((c3 . 4). -1) ((c3 . 2) . -1) . -1) nil)) (and (geq (((!_k24 . 1) . 1) ((c3 . 6) . 1) ((c3 . 4) . 1) ((c3 . 2) . 1) . 1) nil) (leq (((!_k24 . 1) . 1) ((c3 . 6) . -1) ((c3 . 4) . -1) ((c3 . 2) . -1) . -1) nil)))) (or (and (leq (((!_k25 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k25 . 1) . 1) ((c3 . 3) . -1) ((c3 .1) . -1)) nil) (neq (((!_k25 . 1) . 1)) nil)) (and (geq (((!_k25 . 1) . 1) ((c3. 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k25 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1). -1)) nil) (neq (((!_k25 . 1) . 1)) nil)))) (ball !_k21 (ball !_k20 (ball !_k13(or (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k20 . 1) . 1)) nil) (equal (((!_k20 . 1) . 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil)((ncong ((c3 . 1) . 1)) (((!_k13 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 .1) . -1)) nil) (equal (((!_k13 . 1) . 1) ((!_k20 . 1) . -1) ((c0 . 1) ((c2 . 1). -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c3 . 2) . 1)) (((!_k13 . 1) ((c2 . 1)((c3 . 1) . 1))) ((!_k20 . 1) ((c3 . 1) . -1))) nil)) (or (and (leq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k13 . 1) . 1) ((c3 . 3) .-1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)) (and (geq (((!_k13 . 1). 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k13 . 1) . 1) ((c3 . 3) . -1)((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)))) (and (geq (((!_k20 . 1) .1) ((c3 . 6) . 1) ((c3 . 4) . 1) ((c3 . 2) . 1) . 1) nil) (leq (((!_k20 . 1) . 1) ((c3 . 6) . -1) ((c3 . 4) . -1) ((c3 . 2) . -1) . -1) nil))) (or (and (leq (((!_k21 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k21 . 1) . 1) ((c3. 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k21 . 1) . 1)) nil)) (and (geq (((!_k21 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k21 . 1) . 1) ((c3. 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k21 . 1) . 1)) nil)))) (ball !_k21 (ball !_k20 (or (ball !_k13 (or ((ncong ((c3 . 2) . 1)) (((!_k20 . 1) . 1)) nil)(equal (((!_k20 . 1) . 1) ((c0 . 1) ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) ((c1 . 1) ((c3 . 1) . 1))) nil) ((ncong ((c3 . 1) . 1)) (((!_k13 . 1) . 1) ((c0 .1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) (equal (((!_k13 . 1) ((c3 . 1) . 1)) ((!_k20 . 1) . -1) ((c0 . 1) ((c2 . 1) ((c3 . 1) . -1)) ((c3 . 1) . 1)) ((c1. 1) ((c3 . 1) . -1))) nil) ((ncong ((c3 . 3) . 1)) (((!_k13 . 1) ((c2 . 1) ((c3. 2) . 1))) ((!_k20 . 1) ((c3 . 1) . -1))) nil)) (or (and (leq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k13 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)) (and (geq (((!_k13 . 1) . 1)((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k13 . 1) . 1) ((c3 . 3) . -1) ((c3. 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)))) (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k20 . 1) . 1) ((c0 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c1 . 1) ((c3 . 1) . 1))) nil)) (or (and (leq (((!_k20 . 1) . 1) ((!_k21 . 1) ((c2 . 1) ((c3 . 1) . -1))) ((c3 . 7) . 1) ((c3 . 5) . 1) ((c3 . 3) . 1) ((c3 . 1). 1)) nil) (geq (((!_k20 . 1) . 1) ((!_k21 . 1) ((c2 . 1) ((c3 . 1) . -1))) ((c3. 7) . -1) ((c3 . 5) . -1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k20 . 1) . 1) ((!_k21 . 1) ((c2 . 1) ((c3 . 1) . -1))) ((c3 . 7) . 1) ((c3 . 5) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k20 . 1) . 1) ((!_k21 . 1)((c2 . 1) ((c3 . 1) . -1))) ((c3 . 7) . -1) ((c3 . 5) . -1) ((c3 . 3) . -1) ((c3. 1) . -1)) nil)))) (or (and (leq (((!_k21 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) .1)) nil) (geq (((!_k21 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k21 . 1) . 1)) nil)) (and (geq (((!_k21 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k21 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k21 . 1) . 1)) nil)))) (ball !_k21 (ball !_k20 (ball !_k13 (or (equal (((c3 .1) . 1)) nil) (equal (((!_k20 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k20 .1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c3 . 1) .1)) (((!_k13 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) (equal (((!_k13 . 1) . 1) ((!_k20 . 1) . -1)) nil) ((ncong ((c3 . 2) . 1)) (((!_k13 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((!_k20 . 1) ((c3 . 1) . -1)) ((c0 . 1) ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) ((c1 . 1) ((c3 . 1) . 1))) nil)) (or (and (leq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k13 .1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)) (and (geq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k13 .1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)))) (or (and (geq (((!_k20 . 1) . 1) ((!_k21 . 1) . -1) ((c3 . 6) . 1) ((c3 . 4) . 1)((c3 . 2) . 1) . 1) nil) (leq (((!_k20 . 1) . 1) ((!_k21 . 1) . -1) ((c3 . 6) .-1) ((c3 . 4) . -1) ((c3 . 2) . -1) . -1) nil)) (and (geq (((!_k20 . 1) . 1) ((c3 . 6) . 1) ((c3 . 4) . 1) ((c3 . 2) . 1) . 1) nil) (leq (((!_k20 . 1) . 1) ((c3 . 6) . -1) ((c3 . 4) . -1) ((c3 . 2) . -1) . -1) nil)))) (or (and (leq (((!_k21 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k21 . 1) . 1) ((c3. 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k21 . 1) . 1)) nil)) (and (geq (((!_k21 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k21 . 1) . 1) ((c3. 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k21 . 1) . 1)) nil)))) (ball !_k17 (ball !_k16 (ball !_k13 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1))nil) (equal (((!_k16 . 1) . 1) ((c0 . 1) ((c2 . 2) . 1) . -1) ((c1 . 1) ((c2 . 1) . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k16 . 1) . 1) ((c0 . 1) ((c2 . 2). 1) ((c2 . 1) . -1)) ((c1 . 1) ((c2 . 1) . 1))) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k13 . 1) . 1) ((!_k16 . 1) . 1)) nil) (equal (((!_k13 . 1) . 1) ((!_k16 . 1) . 1) ((c0 . 1) ((c2 . 2) . 1) ((c2 . 1) . -1)) ((c1 . 1) ((c2 . 1) .1))) nil) (equal (((!_k13 . 1) . 1) ((!_k16 . 1) ((c2 . 1) . -1) . 1) ((c0 . 1)((c2 . 3) . -1) ((c2 . 2) . 1)) ((c1 . 1) ((c2 . 2) . -1))) nil) ((ncong ((c2 .1) ((c3 . 2) . 1))) (((!_k13 . 1) ((c2 . 1) ((c3 . 1) . 1)))) nil)) (or (and (leq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)))) (and (geq (((!_k16 .1) . 1) ((!_k17 . 1) . 1) ((c2 . 2) ((c3 . 4) . 1) ((c3 . 2) . 1)) ((c3 . 2) . 1) . 1) nil) (leq (((!_k16 . 1) . 1) ((!_k17 . 1) . 1) ((c2 . 2) ((c3 . 4) . -1)((c3 . 2) . -1)) ((c3 . 2) . -1) . -1) nil))) (or (and (leq (((!_k17 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k17 . 1) . 1) ((c2 . 1)((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k17 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k17 . 1) . 1) ((c2 . 1) ((c3 . 3). -1) ((c3 . 1) . -1))) nil)))) (ball !_k17 (ball !_k16 (ball !_k13 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((!_k16 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k16 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1. 1) . -1)) nil) (equal (((!_k13 . 1) . 1) ((!_k16 . 1) . 1) ((c0 . 1) ((c2 . 1). -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k13 . 1) . 1) ((!_k16 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) . 1) ((c1 . 1) ((c2 . 1) . -1) . -1)) nil) (equal (((!_k13 . 1) . 1) ((!_k16 . 1) ((c2 . 1) . -1) . 1) ((c0 .1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c2 . 1) ((c3 . 2) . 1)))(((!_k13 . 1) ((c2 . 1) ((c3 . 1) . 1)))) nil)) (or (and (leq (((!_k13 . 1) . 1)((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k13 . 1) . 1) ((c2 . 1)((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3). -1) ((c3 . 1) . -1))) nil)))) (and (geq (((!_k16 . 1) . 1) ((c2 . 2) ((c3 . 4). 1) ((c3 . 2) . 1)) ((c3 . 2) . 1) . 1) nil) (leq (((!_k16 . 1) . 1) ((c2 . 2)((c3 . 4) . -1) ((c3 . 2) . -1)) ((c3 . 2) . -1) . -1) nil))) (or (and (leq (((!_k17 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k17 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k17 . 1). 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k17 . 1) . 1) ((c2. 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)))) (ball !_k17 (ball !_k16 (ball!_k13 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) ((ncong ((c3. 1) . 1)) (((!_k16 . 1) . 1)) nil) (equal (((!_k16 . 1) . 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) (equal (((!_k13 . 1) . 1) ((!_k16 . 1) . 1))nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k13 . 1) . 1) ((!_k16 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil) (equal(((!_k13 . 1) . 1) ((!_k16 . 1) ((c2 . 1) . -1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil) ((ncong ((c2 . 1) ((c3 . 2) . 1))) (((!_k13 . 1) ((c2 . 1) ((c3 . 1) . 1)))) nil)) (or (and (leq (((!_k13 . 1) .1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k13 . 1) . 1) ((c2 .1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 .3) . -1) ((c3 . 1) . -1))) nil)))) (or (and (geq (((!_k16 . 1) . 1) ((!_k17 . 1). 1) ((c2 . 2) ((c3 . 4) . 1) ((c3 . 2) . 1)) ((c3 . 2) . 1) . 1) nil) (leq (((!_k16 . 1) . 1) ((!_k17 . 1) . 1) ((c2 . 2) ((c3 . 4) . -1) ((c3 . 2) . -1)) ((c3 . 2) . -1) . -1) nil)) (and (geq (((!_k16 . 1) . 1) ((c2 . 2) ((c3 . 4) . 1)((c3 . 2) . 1)) ((c3 . 2) . 1) . 1) nil) (leq (((!_k16 . 1) . 1) ((c2 . 2) ((c3. 4) . -1) ((c3 . 2) . -1)) ((c3 . 2) . -1) . -1) nil)))) (or (and (leq (((!_k17. 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k17 . 1) . 1)((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k17 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k17 . 1) . 1) ((c2 . 1)((c3 . 3) . -1) ((c3 . 1) . -1))) nil)))) (ball !_k17 (ball !_k16 (or (ball!_k13 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((!_k16 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) (((!_k16 . 1) . 1) ((c0 . 1) ((c2 . 2). -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil) (equal (((!_k13 . 1) . 1)((!_k16 . 1) . -1)) nil) (equal (((!_k13 . 1) ((c2 . 1) . 1) . -1) ((!_k16 . 1). 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil)((ncong ((c2 . 2) ((c3 . 1) . 1)) ((c2 . 1) ((c3 . 1) . -1))) (((!_k13 . 1) ((c2. 1) . 1) . -1) ((!_k16 . 1) . 1) ((c0 . 1) ((c2 . 3) . -1) ((c2 . 2) . 1)) ((c1. 1) ((c2 . 2) . -1))) nil) ((ncong ((c2 . 1) ((c3 . 2) . 1))) (((!_k13 . 1) ((c2 . 1) ((c3 . 1) . 1)))) nil)) (or (and (leq (((!_k13 . 1) . 1) ((c2 . 1) ((c3. 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1)((c3 . 1) . 1))) nil) (leq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)))) (equal (((c2 . 1) . 1) . -1) nil) ((ncong ((c2 . 1) . 1) . -1)(((!_k16 . 1) . 1) ((c1 . 1) . -1)) nil)) (or (and (leq (((!_k16 . 1) . 1) ((!_k17 . 1) . -1) ((c2 . 3) ((c3 . 4) . 1) ((c3 . 2) . 1)) ((c2 . 2) ((c3 . 4) .-1) ((c3 . 2) . -1)) ((c2 . 1) ((c3 . 2) . 1) . 1) ((c3 . 2) . -1) . -1) nil) (geq (((!_k16 . 1) . 1) ((!_k17 . 1) . -1) ((c2 . 3) ((c3 . 4) . -1) ((c3 . 2) .-1)) ((c2 . 2) ((c3 . 4) . 1) ((c3 . 2) . 1)) ((c2 . 1) ((c3 . 2) . -1) . -1) ((c3 . 2) . 1) . 1) nil)) (and (greaterp (((!_k16 . 1) . 1) ((!_k17 . 1) . -1) ((c2 . 3) ((c3 . 4) . 1) ((c3 . 2) . 1)) ((c2 . 2) ((c3 . 4) . -1) ((c3 . 2) . -1)) ((c2 . 1) ((c3 . 2) . 1) . 1) ((c3 . 2) . -1)) nil) (lessp (((!_k16 . 1) . 1)((!_k17 . 1) . -1) ((c2 . 3) ((c3 . 4) . -1) ((c3 . 2) . -1)) ((c2 . 2) ((c3 . 4) . 1) ((c3 . 2) . 1)) ((c2 . 1) ((c3 . 2) . -1) . -1) ((c3 . 2) . 1)) nil)))) (or (and (leq (((!_k17 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k17 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k17 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k17 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)))) (ball !_k150(ball !_k149 (ball !_k146 (or (equal (((!_k149 . 1) . 1) ((c0 . 1) ((c2 . 2) . 1) . -1) ((c1 . 1) ((c2 . 1) . 1) . 1)) nil) (neq (((!_k149 . 1) . 1) ((c0 . 1) ((c2 . 2) . 1) ((c2 . 1) . -1)) ((c1 . 1) ((c2 . 1) . 1))) nil) (equal (((!_k146. 1) ((c3 . 1) . 1)) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) (neq (((!_k146 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((!_k149 . 1) . -1)) nil)) (or (equal (((!_k146 . 1) . 1) . 1) nil) (equal (((!_k146 . 1) . 1) . -1) nil))) (equal (((!_k149 . 1) . 1) ((!_k150 . 1) ((c2 . 1) ((c3 . 1) . -1)))) nil)) (or (equal (((!_k150 . 1) . 1) . 1) nil) (equal (((!_k150 . 1) . 1) . -1) nil))) (ball !_k148(ball !_k147 (ball !_k146 (or (and (neq (((!_k148 . 1) . 1)) nil) (neq (((c2 . 1) . 1)) nil)) (and (neq (((!_k146 . 1) . 1)) nil) (neq (((c2 . 1) . 1)) nil)) (equal (((c3 . 1) . 1)) nil) (equal (((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) (neq (((!_k148 . 1) ((c2 . 1) . 1))) nil) (neq (((!_k147 . 1) . 1)) nil)((ncong ((c3 . 1) . 1)) (((!_k146 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1. 1) . -1)) nil) (equal (((!_k146 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1. 1) . -1)) nil)) (or (and (leq (((!_k146 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k146 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k146 . 1) . 1)) nil)) (and (geq (((!_k146 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k146 . 1) . 1) ((c3 . 1). -1)) nil) (neq (((!_k146 . 1) . 1)) nil)))) (equal (((!_k147 . 1) . 1) ((!_k148 . 1) ((c2 . 1) . -1))) nil)) (or (and (leq (((!_k148 . 1) . 1) ((c3 . 1). 1)) nil) (geq (((!_k148 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k148 . 1) .1)) nil)) (and (geq (((!_k148 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k148 . 1). 1) ((c3 . 1) . -1)) nil) (neq (((!_k148 . 1) . 1)) nil)))) (ball !_k143 (ball!_k137 (or (equal (((c3 . 1) . 1)) nil) (equal (((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) (equal (((!_k137 . 1) ((c3 . 1) . 1)) ((c0 . 1) ((c2 . 1) .1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k137 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c0 . 1) ((c2 . 2) . 1) ((c2 . 1) . -1)) ((c1 . 1) ((c2 . 1) .1))) nil)) (and (geq (((!_k137 . 1) . 1) ((c3 . 2) . 1) . 1) nil) (leq (((!_k137. 1) . 1) ((c3 . 2) . -1) . -1) nil) (neq (((!_k137 . 1) . 1)) nil))) (and (geq(((!_k143 . 1) . 1) ((c3 . 2) . 1) . 1) nil) (leq (((!_k143 . 1) . 1) ((c3 . 2). -1) . -1) nil) (neq (((!_k143 . 1) . 1)) nil))) (ball !_k141 (ball !_k137 (or(equal (((c3 . 1) . 1)) nil) (equal (((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) .1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k137 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) .1) ((c1 . 1) . -1)) nil) (equal (((!_k137 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) .1) ((c1 . 1) . -1)) nil) ((ncong ((c3 . 2) . 1)) (((!_k137 . 1) ((c2 . 1) ((c3 .1) . 1)))) nil)) (or (and (leq (((!_k137 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k137 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k137 . 1) . 1)) nil)) (and (geq (((!_k137 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) .1)) nil) (leq (((!_k137 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k137 . 1) . 1)) nil)))) (or (and (leq (((!_k141 . 1) . 1) ((c3 . 3) . 1) ((c3. 1) . 1)) nil) (geq (((!_k141 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k141 . 1) . 1)) nil)) (and (geq (((!_k141 . 1) . 1) ((c3 . 3) . 1) ((c3. 1) . 1)) nil) (leq (((!_k141 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k141 . 1) . 1)) nil)))) (ball !_k139 (ball !_k137 (or (equal (((c3 . 1). 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k137 . 1) . 1) ((c0. 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil) (equal (((!_k137 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1) .-1))) nil) ((ncong ((c2 . 1) ((c3 . 2) . 1))) (((!_k137 . 1) ((c2 . 1) ((c3 . 1). 1)))) nil)) (or (and (leq (((!_k137 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 .1) . 1))) nil) (geq (((!_k137 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil) (neq (((!_k137 . 1) . 1)) nil)) (and (geq (((!_k137 . 1) . 1) ((c2 . 1)((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k137 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil) (neq (((!_k137 . 1) . 1)) nil)))) (or (and (leq (((!_k139 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq (((!_k139. 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k139. 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k139 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)))) (ball !_k13 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((c0 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((c0 . 1) ((c2 . 1) . 1)) ((c1 . 1) . 1)) nil) (equal (((!_k13 . 1) . 1) ((c1 . 1) . -1)) nil) (equal (((!_k13 . 1) . 1) ((c0 . 1) ((c2 .1) . -1)) ((c1 . 1) . -1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k13 . 1). 1) ((c0 . 1) ((c2 . 2) . -1)) ((c1 . 1) ((c2 . 1) . -1) . -1)) nil) ((ncong ((c2 . 1) ((c3 . 2) . 1))) (((!_k13 . 1) ((c2 . 1) ((c3 . 1) . 1)))) nil)) (or (and (leq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (geq(((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k13 . 1) . 1) ((c2 . 1) ((c3 . 3) . 1) ((c3 . 1) . 1))) nil) (leq (((!_k13 .1) . 1) ((c2 . 1) ((c3 . 3) . -1) ((c3 . 1) . -1))) nil)))) (ball !_k13 (or (equal (((c3 . 1) . 1)) nil) (equal (((c0 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1))(((c0 . 1) ((c2 . 1) . 1)) ((c1 . 1) . 1)) nil) (equal (((!_k13 . 1) . 1) ((c0 .1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k13 . 1) . 1) ((c0 . 1) ((c2 . 1) .-1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c3 . 2) . 1)) (((!_k13 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c0 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c1 . 1) ((c3 . 1) . 1)))nil)) (or (and (leq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq(((!_k13 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)) (and (geq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k13 . 1) . 1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1))nil)))) (ball !_k13 (or (equal (((c3 . 1) . 1)) nil) (equal (((c0 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((c0 . 1) ((c2 . 1) . 1)) ((c1 . 1) . 1)) nil) (equal(((!_k13 . 1) . 1) ((c0 . 1) . -1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k13 . 1) .1) ((c0 . 1) ((c2 . 1) . -1)) ((c1 . 1) . -1)) nil) ((ncong ((c3 . 2) . 1)) (((!_k13 . 1) ((c2 . 1) ((c3 . 1) . 1))) ((c1 . 1) ((c3 . 1) . 1))) nil)) (or (and(leq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k13 . 1) .1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)) (and (geq (((!_k13 . 1) . 1) ((c3 . 3) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k13 . 1) .1) ((c3 . 3) . -1) ((c3 . 1) . -1)) nil) (neq (((!_k13 . 1) . 1)) nil)))) (ball!_k128 (ball !_k127 (ball !_k4 (or (equal (((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 .1) . 1)) nil) (equal (((!_k127 . 1) . 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) (neq (((!_k127 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1))((c1 . 1) ((c2 . 1) . -1))) nil) (neq (((!_k127 . 1) . 1) ((!_k4 . 1) ((c3 . 1). -1))) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) .-1) nil))) (equal (((!_k127 . 1) . 1) ((!_k128 . 1) ((c3 . 1) . -1))) nil)) (or(equal (((!_k128 . 1) . 1) . 1) nil) (equal (((!_k128 . 1) . 1) . -1) nil))) (ball !_k126 (ball !_k125 (ball !_k124 (or (ball !_k108 (ball !_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((!_k124 . 1) . 1) ((c0. 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) (equal (((!_k124 . 1) . 1) ((c0. 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil) ((ncong ((c2 . 2) ((c3 . 1) . 1)) ((c2 . 1) ((c3 . 1) . -1))) (((!_k124 . 1) . 1) ((c0 . 1) ((c2 . 3) . -1) ((c2 . 2) . 1)) ((c1 . 1) ((c2 . 2) . -1))) nil) (neq (((!_k124 . 1) . 1) ((!_k4 . 1) ((c2 . 1) ((c3 . 1) . -1)))) nil) (neq (((!_k108 .1) . 1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) .-1) nil))) (or (and (leq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) . 1))) nil) (geq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k108 .1) . 1) ((c2 . 1) ((c3 . 1) . 1))) nil) (leq (((!_k108 . 1) . 1) ((c2 . 1) ((c3. 1) . -1))) nil)))) (equal (((c2 . 1) . 1) . -1) nil) ((ncong ((c2 . 1) . 1) .-1) (((!_k124 . 1) . 1) ((c1 . 1) . -1)) nil)) (or (and (leq (((!_k124 . 1) . 1)((!_k125 . 1) ((c2 . 1) ((c3 . 1) . -1))) ((c2 . 3) ((c3 . 2) . 1)) ((c2 . 2) ((c3 . 2) . -1)) ((c2 . 1) . 1) . -1) nil) (geq (((!_k124 . 1) . 1) ((!_k125 . 1)((c2 . 1) ((c3 . 1) . -1))) ((c2 . 3) ((c3 . 2) . -1)) ((c2 . 2) ((c3 . 2) . 1))((c2 . 1) . -1) . 1) nil)) (and (greaterp (((!_k124 . 1) . 1) ((!_k125 . 1) ((c2. 1) ((c3 . 1) . -1))) ((c2 . 3) ((c3 . 2) . 1)) ((c2 . 2) ((c3 . 2) . -1)) ((c2. 1) . 1)) nil) (lessp (((!_k124 . 1) . 1) ((!_k125 . 1) ((c2 . 1) ((c3 . 1) .-1))) ((c2 . 3) ((c3 . 2) . -1)) ((c2 . 2) ((c3 . 2) . 1)) ((c2 . 1) . -1)) nil)))) (or (equal (((!_k125 . 1) . 1) . 1) nil) (equal (((!_k125 . 1) . 1) . -1)nil))) (or (and (leq (((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1) . 1))) nil) (geq (((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1) . 1))) nil) (leq (((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1) .-1))) nil)))) (ball !_k126 (ball !_k124 (ball !_k108 (ball !_k4 (or (equal (((c3. 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((!_k124 . 1) . 1)) nil) (equal (((!_k124 . 1) . 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k124 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2 . 1) . -1))) nil) (neq (((!_k124 . 1) ((c2 . 1) .1) . -1) ((!_k4 . 1) ((c2 . 1) ((c3 . 1) . -1))) ((c0 . 1) ((c2 . 2) . 1) ((c2 .1) . -1)) ((c1 . 1) ((c2 . 1) . 1))) nil) (neq (((!_k108 . 1) . 1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1) nil))) (or (and(leq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) . 1))) nil) (geq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k108 . 1) . 1) ((c2 . 1) ((c3. 1) . 1))) nil) (leq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) . -1))) nil)))) (and (geq (((!_k124 . 1) . 1) ((c2 . 2) ((c3 . 2) . 1)) . 1) nil) (leq (((!_k124. 1) . 1) ((c2 . 2) ((c3 . 2) . -1)) . -1) nil))) (or (and (leq (((!_k126 . 1) .1) ((c2 . 1) ((c3 . 1) . 1))) nil) (geq (((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1). -1))) nil)) (and (geq (((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1) . 1))) nil) (leq(((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1) . -1))) nil)))) (ball !_k126 (ball!_k124 (ball !_k108 (ball !_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((!_k124 . 1) . 1)) nil) (equal (((!_k124 . 1) . 1) ((c0 .1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1)))(((!_k124 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) . 1) ((c1 . 1) ((c2 . 1) . -1) .-1)) nil) (neq (((!_k124 . 1) ((c2 . 1) . 1) . -1) ((!_k4 . 1) ((c2 . 1) ((c3 .1) . -1))) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) (neq (((!_k108 .1) . 1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) .-1) nil))) (or (and (leq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) . 1))) nil) (geq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k108 .1) . 1) ((c2 . 1) ((c3 . 1) . 1))) nil) (leq (((!_k108 . 1) . 1) ((c2 . 1) ((c3. 1) . -1))) nil)))) (and (geq (((!_k124 . 1) . 1) ((c2 . 2) ((c3 . 2) . 1)) . 1) nil) (leq (((!_k124 . 1) . 1) ((c2 . 2) ((c3 . 2) . -1)) . -1) nil))) (or (and(leq (((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1) . 1))) nil) (geq (((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k126 . 1) . 1) ((c2 . 1) ((c3. 1) . 1))) nil) (leq (((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1) . -1))) nil)))) (ball !_k126 (ball !_k124 (ball !_k108 (ball !_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((!_k124 . 1). 1)) nil) (equal (((!_k124 . 1) . 1) ((c0 . 1) ((c2 . 2) . 1) . -1) ((c1 . 1) ((c2 . 1) . 1) . 1)) nil) (equal (((!_k124 . 1) . 1) ((c0 . 1) ((c2 . 2) . 1) ((c2 . 1) . -1)) ((c1 . 1) ((c2 . 1) . 1))) nil) (neq (((!_k124 . 1) ((c2 . 1) . 1) . -1) ((!_k4 . 1) ((c2 . 1) ((c3 . 1) . -1))) ((c0 . 1) ((c2 . 3) . 1) ((c2 .2) . -1)) ((c1 . 1) ((c2 . 2) . 1))) nil) (neq (((!_k108 . 1) . 1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1) nil))) (or (and(leq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) . 1))) nil) (geq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k108 . 1) . 1) ((c2 . 1) ((c3. 1) . 1))) nil) (leq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) . -1))) nil)))) (and (geq (((!_k124 . 1) . 1) ((c2 . 2) ((c3 . 2) . 1)) . 1) nil) (leq (((!_k124. 1) . 1) ((c2 . 2) ((c3 . 2) . -1)) . -1) nil))) (or (and (leq (((!_k126 . 1) .1) ((c2 . 1) ((c3 . 1) . 1))) nil) (geq (((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1). -1))) nil)) (and (geq (((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1) . 1))) nil) (leq(((!_k126 . 1) . 1) ((c2 . 1) ((c3 . 1) . -1))) nil)))) (ball !_k120 (ball!_k118 (ball !_k108 (ball !_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((!_k118. 1) . 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) (equal (((!_k108 .1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k108 . 1) . 1) ((c0 . 1) ((c2 . 1) .-1) . 1) ((c1 . 1) . -1)) nil) (neq (((!_k108 . 1) . 1) ((!_k118 . 1) . -1) ((!_k4 . 1) ((c3 . 1) . 1)) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) (neq (((!_k108 . 1) ((c2 . 1) . 1)) ((!_k118 . 1) . -1)) nil)) (or (equal (((!_k4. 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1) nil))) (or (and (leq (((!_k108 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k108 . 1) . 1) ((c3 . 1) . -1))nil)) (and (geq (((!_k108 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k108 . 1) . 1) ((c3 . 1) . -1)) nil)))) (equal (((!_k118 . 1) . 1) ((!_k120 . 1) ((c2 . 1) .-1))) nil)) (or (and (leq (((!_k120 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k120 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k120 . 1) . 1) ((c3 . 1). 1)) nil) (leq (((!_k120 . 1) . 1) ((c3 . 1) . -1)) nil)))) (ball !_k117 (ball!_k116 (ball !_k114 (ball !_k109 (ball !_k108 (ball !_k4 (or (equal (((c3 . 1) .1)) nil) (equal (((!_k114 . 1) . 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) (neq (((!_k108 . 1) . 1) ((!_k4 . 1) ((c3 . 1) . 1))) nil) ((ncong ((c3. 1) . 1)) (((!_k108 . 1) . 1) ((!_k114 . 1) . 1)) nil) (equal (((!_k108 . 1) .1) ((!_k114 . 1) . 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) (neq (((!_k108 . 1) ((c2 . 1) . 1)) ((!_k114 . 1) ((c2 . 1) . 1) . -1) ((c0 . 1) ((c2. 2) . 1) ((c2 . 1) . -1)) ((c1 . 1) ((c2 . 1) . 1))) nil)) (or (equal (((!_k4 .1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1) nil))) (or (and (leq (((!_k108. 1) . 1) ((!_k109 . 1) ((c3 . 1) . 1)) ((c3 . 1) . 1)) nil) (geq (((!_k108 . 1). 1) ((!_k109 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) nil)) (and (geq (((!_k108 .1) . 1) ((!_k109 . 1) ((c3 . 1) . 1)) ((c3 . 1) . 1)) nil) (leq (((!_k108 . 1) .1) ((!_k109 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) nil)))) (or (equal (((!_k109 .1) . 1) . 1) nil) (equal (((!_k109 . 1) . 1) . -1) nil))) (and (geq (((!_k114 .1) . 1) ((!_k116 . 1) . 1) ((c3 . 2) . 1) . 1) nil) (leq (((!_k114 . 1) . 1) ((!_k116 . 1) . 1) ((c3 . 2) . -1) . -1) nil))) (or (and (leq (((!_k116 . 1) . 1)((!_k117 . 1) ((c3 . 1) . 1)) ((c3 . 1) . 1)) nil) (geq (((!_k116 . 1) . 1) ((!_k117 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) nil)) (and (geq (((!_k116 . 1) . 1)((!_k117 . 1) ((c3 . 1) . 1)) ((c3 . 1) . 1)) nil) (leq (((!_k116 . 1) . 1) ((!_k117 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) nil)))) (or (equal (((!_k117 . 1) .1) . 1) nil) (equal (((!_k117 . 1) . 1) . -1) nil))) (ball !_k117 (ball !_k116 (ball !_k114 (or (ball !_k109 (ball !_k108 (ball !_k4 (or (equal (((c3 . 1) . 1))nil) (equal (((!_k114 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1))nil) (neq (((!_k108 . 1) . 1) ((!_k4 . 1) ((c3 . 1) . 1))) nil) (neq (((!_k108 .1) ((c2 . 1) . 1)) ((!_k114 . 1) . 1)) nil) (equal (((!_k108 . 1) ((c2 . 1) . 1). -1) ((!_k114 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) . -1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) (((!_k108 . 1) ((c2 . 1) . 1) .-1) ((!_k114 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1 . 1) ((c2. 1) . -1))) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) .1) . -1) nil))) (or (and (leq (((!_k108 . 1) . 1) ((!_k109 . 1) ((c3 . 1) . 1))((c3 . 1) . 1)) nil) (geq (((!_k108 . 1) . 1) ((!_k109 . 1) ((c3 . 1) . 1)) ((c3. 1) . -1)) nil)) (and (geq (((!_k108 . 1) . 1) ((!_k109 . 1) ((c3 . 1) . 1)) ((c3 . 1) . 1)) nil) (leq (((!_k108 . 1) . 1) ((!_k109 . 1) ((c3 . 1) . 1)) ((c3 .1) . -1)) nil)))) (or (equal (((!_k109 . 1) . 1) . 1) nil) (equal (((!_k109 . 1). 1) . -1) nil))) (equal (((c2 . 1) . 1) . -1) nil) ((ncong ((c2 . 1) . 1) . -1)(((!_k114 . 1) . 1) ((c1 . 1) . -1)) nil)) (or (and (leq (((!_k114 . 1) . 1) ((!_k116 . 1) ((c2 . 1) . 1)) ((c2 . 1) ((c3 . 2) . 1) . 1) ((c3 . 2) . -1) . -1)nil) (geq (((!_k114 . 1) . 1) ((!_k116 . 1) ((c2 . 1) . 1)) ((c2 . 1) ((c3 . 2). -1) . -1) ((c3 . 2) . 1) . 1) nil)) (and (greaterp (((!_k114 . 1) . 1) ((!_k116 . 1) ((c2 . 1) . 1)) ((c2 . 1) ((c3 . 2) . 1) . 1) ((c3 . 2) . -1)) nil)(lessp (((!_k114 . 1) . 1) ((!_k116 . 1) ((c2 . 1) . 1)) ((c2 . 1) ((c3 . 2) .-1) . -1) ((c3 . 2) . 1)) nil)))) (or (and (leq (((!_k116 . 1) . 1) ((!_k117 . 1) ((c3 . 1) . 1)) ((c3 . 1) . 1)) nil) (geq (((!_k116 . 1) . 1) ((!_k117 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) nil)) (and (geq (((!_k116 . 1) . 1) ((!_k117 . 1)((c3 . 1) . 1)) ((c3 . 1) . 1)) nil) (leq (((!_k116 . 1) . 1) ((!_k117 . 1) ((c3. 1) . 1)) ((c3 . 1) . -1)) nil)))) (or (equal (((!_k117 . 1) . 1) . 1) nil) (equal (((!_k117 . 1) . 1) . -1) nil))) (ball !_k117 (ball !_k116 (ball !_k114 (ball !_k109 (ball !_k108 (ball !_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((!_k114 . 1) . 1)) nil) (neq (((!_k108 . 1) . 1) ((!_k4 . 1) ((c3 . 1) . 1))) nil) (equal (((!_k108 . 1) . 1) ((!_k114 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k108 . 1) . 1) ((!_k114 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1) . 1) ((c1 . 1) .-1)) nil) (neq (((!_k108 . 1) ((c2 . 1) . 1)) ((!_k114 . 1) ((c2 . 1) . 1) . -1)((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1) nil))) (or (and (leq (((!_k108 . 1) .1) ((!_k109 . 1) ((c3 . 1) . 1)) ((c3 . 1) . 1)) nil) (geq (((!_k108 . 1) . 1) ((!_k109 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) nil)) (and (geq (((!_k108 . 1) . 1) ((!_k109 . 1) ((c3 . 1) . 1)) ((c3 . 1) . 1)) nil) (leq (((!_k108 . 1) . 1) ((!_k109 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) nil)))) (or (equal (((!_k109 . 1) .1) . 1) nil) (equal (((!_k109 . 1) . 1) . -1) nil))) (or (and (geq (((!_k114 . 1) . 1) ((!_k116 . 1) . 1) ((c3 . 2) . 1) . 1) nil) (leq (((!_k114 . 1) . 1) ((!_k116 . 1) . 1) ((c3 . 2) . -1) . -1) nil)) (and (geq (((!_k114 . 1) . 1) ((c3. 2) . 1) . 1) nil) (leq (((!_k114 . 1) . 1) ((c3 . 2) . -1) . -1) nil)))) (or (and (leq (((!_k116 . 1) . 1) ((!_k117 . 1) ((c3 . 1) . 1)) ((c3 . 1) . 1)) nil)(geq (((!_k116 . 1) . 1) ((!_k117 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) nil)) (and (geq (((!_k116 . 1) . 1) ((!_k117 . 1) ((c3 . 1) . 1)) ((c3 . 1) . 1)) nil)(leq (((!_k116 . 1) . 1) ((!_k117 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) nil))))(or (equal (((!_k117 . 1) . 1) . 1) nil) (equal (((!_k117 . 1) . 1) . -1) nil)))(ball !_k109 (ball !_k108 (ball !_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((c0 . 1) . 1)) nil) (equal (((!_k108 . 1) . 1) ((c0 . 1) . -1)) nil) ((ncong ((c3. 1) . 1)) (((!_k108 . 1) . 1) ((c0 . 1) ((c2 . 1) . -1)) ((c1 . 1) . -1)) nil)(neq (((!_k108 . 1) . 1) ((!_k4 . 1) ((c3 . 1) . 1))) nil) (neq (((!_k108 . 1) ((c2 . 1) . 1)) ((c1 . 1) . 1)) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1) nil))) (or (and (leq (((!_k108 . 1) . 1) ((!_k109. 1) ((c3 . 1) . 1)) ((c3 . 1) . 1)) nil) (geq (((!_k108 . 1) . 1) ((!_k109 . 1)((c3 . 1) . 1)) ((c3 . 1) . -1)) nil)) (and (geq (((!_k108 . 1) . 1) ((!_k109 .1) ((c3 . 1) . 1)) ((c3 . 1) . 1)) nil) (leq (((!_k108 . 1) . 1) ((!_k109 . 1) ((c3 . 1) . 1)) ((c3 . 1) . -1)) nil)))) (or (equal (((!_k109 . 1) . 1) . 1) nil)(equal (((!_k109 . 1) . 1) . -1) nil))) (ball !_k108 (ball !_k4 (or (equal (((c3. 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (equal (((c0 . 1) . 1)) nil) (equal(((c0 . 1) ((c2 . 1) . 1)) ((c1 . 1) . 1)) nil) ((ncong ((c2 . 1) ((c3 . 1) . 1))) (((c0 . 1) ((c2 . 2) . 1)) ((c1 . 1) ((c2 . 1) . 1) . 1)) nil) (neq (((!_k4 .1) ((c2 . 1) ((c3 . 1) . 1))) ((c1 . 1) . -1)) nil) (neq (((!_k108 . 1) . 1))nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1) nil))) (or (and (leq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) . 1))) nil) (geq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) . -1))) nil)) (and (geq (((!_k108 . 1) . 1)((c2 . 1) ((c3 . 1) . 1))) nil) (leq (((!_k108 . 1) . 1) ((c2 . 1) ((c3 . 1) .-1))) nil)))) (ball !_k103 (ball !_k102 (ball !_k101 (ball !_k100 (ball !_k54 (ball !_k50 (ball !_k4 (or (equal (((c3 . 1) . 1)) nil) (equal (((c0 . 1) ((c2 .1) . 1) . -1) ((c1 . 1) . 1)) nil) (neq (((!_k50 . 1) . 1)) nil) (equal (((!_k100 . 1) . 1) ((c0 . 1) ((c2 . 1) . 1) . -1) ((c1 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k100 . 1) . 1) ((c0 . 1) ((c2 . 2) . -1) ((c2 . 1) . 1)) ((c1. 1) ((c2 . 1) . -1))) nil) (neq (((!_k100 . 1) . 1) ((!_k4 . 1) ((c3 . 1) . -1))) nil)) (or (equal (((!_k4 . 1) . 1) . 1) nil) (equal (((!_k4 . 1) . 1) . -1)nil))) (or (and (leq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k50 . 1). 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k50 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k50 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k54 . 1) . 1)((c3 . 1) . 1)) nil) (geq (((!_k54 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k54 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k54 . 1) . 1) ((c3 . 1) . -1))nil)))) (equal (((!_k100 . 1) . 1) ((!_k101 . 1) ((c3 . 1) . -1))) nil)) (or (equal (((!_k101 . 1) . 1) . 1) nil) (equal (((!_k101 . 1) . 1) . -1) nil))) (or(and (leq (((!_k102 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k102 . 1) . 1) ((c3. 1) . -1)) nil)) (and (geq (((!_k102 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k102 . 1) . 1) ((c3 . 1) . -1)) nil)))) (or (and (leq (((!_k103 . 1) . 1) ((c3. 1) . 1)) nil) (geq (((!_k103 . 1) . 1) ((c3 . 1) . -1)) nil)) (and (geq (((!_k103 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k103 . 1) . 1) ((c3 . 1) . -1))nil))))) t)"""
  
  
  let emptyEnv argss =
    { ctxSlvr = new Context (argss |> dict |> Dictionary)
      ctxVars = Map.empty
      ctxFuns = Map.empty
      ctxDecfuns = Map.empty }
  
  let envTeacher = emptyEnv [| ("proof", "true") |]
  let teacherSolver = envTeacher.ctxSlvr.MkSolver "HORN"
  
  
  let forall =
    ForAll ([|"x"|],
            Implies (Ge (Var "x", Int 0),
                     ForAll ([|"y"|], Eq (Add (Var "x", Var "y"), Add (Var "x", Var "y")))) )
  
  let assert' = Assert forall
  
  

  // let lexer = RedTraceLexer (CharStreams.fromString line)
  // let tokens = CommonTokenStream lexer
  // let parser = RedTraceParser tokens

  // let tree: RedTraceParser.ProgContext = parser.prog ()
  // Parser.translateToSmt line |> smtExpr2expr
  // |> printfn "%O"
  // match tree.GetChild 1 with
  // | :? RedTraceParser.ExprContext as expr -> parseVars expr |> fun vs -> for v in vs do  printfn "%O" v
  // | :? RedTraceParser.ExprContext as expr -> translateToSmt expr |> printfn "%O"
  // match tree.GetChild 1  with
  // | :? RedTraceParser.ExprContext as e ->

  // | _  -> printfn "!"
  // let and' = expr.GetChild 0
  // printfn $"{and'}"

  ()
