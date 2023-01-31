module Z3Interpreter

open Microsoft.Z3

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

  let define = fun env (name, args, expr) -> env.ctx_funs.Add (name, (args, expr))

  let declare = List.map Declare

  let rec eval_expr: Env -> Expr -> Microsoft.Z3.Expr =
    fun env ->
      function
      | Int x -> env.ctx_slvr.MkInt x
      | Bool x -> env.ctx_slvr.MkBool x
      | Eq (expr1, expr2) -> env.ctx_slvr.MkEq (eval_expr env expr1, eval_expr env expr2)
      | Ge (expr1, expr2) -> env.ctx_slvr.MkGe (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
      | Add (expr1, expr2) -> env.ctx_slvr.MkAdd (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
      | Mul (expr1, expr2) -> env.ctx_slvr.MkMul (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
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
