module Z3Interpreter

// open Interpreter
open Microsoft.FSharp.Collections
open Microsoft.Z3
open SMTLIB2.Prelude

module AST =
  type Name = string

  type ArgsNum = int

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
    | ForAll of Name array * Expr
    | App of Name * Expr array
    | Ite of Expr * Expr * Expr
  
      
  
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
  
  type Program =
    | Def of Definition
    | DeclConst of Name
    | Decl of Name * ArgsNum
    | Assert of Expr

  let rec smtExpr2expr =
    function
    | Number i -> Int i
    | BoolConst b -> Bool b
    | Ident (ident, _) -> Var ident
    | smtExpr.Apply (operation, exprs) ->
      match operation, exprs with
      | ElementaryOperation (ident, _, _), [e1; e2] when ident = "+" -> Add (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), [e1; e2] when ident = "*" -> Mul (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), [e1; e2] when ident = "=" -> Eq (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), [e1; e2] when ident = ">=" -> Ge (smtExpr2expr e1, smtExpr2expr e2)
      | ElementaryOperation (ident, _, _), es
      | UserDefinedOperation (ident, _, _), es -> Apply (ident, es |> List.map smtExpr2expr)
    | smtExpr.And e -> e |> List.toArray |> Array.map smtExpr2expr |> And
    | smtExpr.Not e -> smtExpr2expr e |> Not
    | Hence (e1, e2) -> Implies (smtExpr2expr e1, smtExpr2expr e2)

open AST

module Interpreter =
  let update =
    fun k v map ->
      Map.containsKey k map
      |> function
        | true -> Map.remove k map |> Map.add k v
        | false -> Map.add k v map

  let define = fun env (name, args, expr) -> env.ctxFuns.Add (name, (args, expr))

  let declConsts = List.map DeclConst
        
  
  
  // let rec eval_expr: Env -> Expr -> Blyat =
  let rec eval_expr: Env -> Expr -> Microsoft.Z3.Expr =
    fun env ->
      function
      | Int x -> env.ctxSlvr.MkInt x
      | Bool x -> env.ctxSlvr.MkBool x
      | Eq (expr1, expr2) -> env.ctxSlvr.MkEq (eval_expr env expr1, eval_expr env expr2)
      | Ge (expr1, expr2) ->
        env.ctxSlvr.MkGe (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
      | Add (expr1, expr2) -> env.ctxSlvr.MkAdd (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
      | Mul (expr1, expr2) -> env.ctxSlvr.MkMul (eval_expr env expr1 :?> ArithExpr, eval_expr env expr2 :?> ArithExpr)
      | And exprs ->
        exprs
        |> Array.map (fun x -> eval_expr env x :?> BoolExpr)
        |> fun x -> env.ctxSlvr.MkAnd x
      | Not expr -> env.ctxSlvr.MkNot (eval_expr env expr :?> BoolExpr)
      | Implies (expr1, expr2) ->
        env.ctxSlvr.MkImplies (eval_expr env expr1 :?> BoolExpr, eval_expr env expr2 :?> BoolExpr)
      | Var x -> env.ctxVars |> Map.find x 
      | App (name, expr) ->
        let decFun = env.ctxDecfuns |> Map.find name in
        let args: Microsoft.Z3.Expr[] = Array.map (eval_expr env) expr
        env.ctxSlvr.MkApp (decFun, args)
      | Apply (n, vs) ->
        env.ctxFuns |> Map.find n
        |> fun (args, body) ->
            let bindings = List.zip args vs
            let ctx_vars = bindings |> List.fold (fun acc (arg, v) -> acc |> update arg (eval_expr env v)) env.ctxVars
            eval_expr { env with ctxVars = ctx_vars } body        
        | ForAll (names, expr) ->
          let vars: Microsoft.Z3.Expr[] = names |> Array.map (fun name -> env.ctxSlvr.MkIntConst name) in 
          let ctxVars =
            Array.zip names vars
            |> Array.fold
                 (fun acc (name, value) -> acc |> Map.add name value)
                 env.ctxVars
          in
          env.ctxSlvr.MkForall(vars, eval_expr {env with ctxVars = ctxVars} expr)
      | Ite (exprIf, exprThen, exprElse) ->
        env.ctxSlvr.MkITE (eval_expr env exprIf :?> BoolExpr, eval_expr env exprThen, eval_expr env exprElse)

  let eval_cmds =
    fun env ->
      List.fold
        (fun (env, varMap, expr) cmd ->
          match cmd with
          | DeclConst n ->
            let intConst = env.ctxSlvr.MkIntConst n

            ({ env with ctxVars = env.ctxVars |> Map.add n intConst }, (n, intConst) :: varMap, expr)
          | Assert e -> (env, varMap, eval_expr env e)
          | Def d -> ({ env with ctxFuns = define env d }, varMap, expr)
          | Decl (name, n) ->
            let intsNum: Sort[] = n |> Array.unfold (fun state -> if state = 0 then None else Some (env.ctxSlvr.IntSort, state - 1))  
            let declFun = env.ctxSlvr.MkFuncDecl(env.ctxSlvr.MkSymbol(name), intsNum, env.ctxSlvr.MkBoolSort())

            ({ env with ctxDecfuns = env.ctxDecfuns |> Map.add name declFun }, varMap, expr))
        (env, [], env.ctxSlvr.MkInt 0)




