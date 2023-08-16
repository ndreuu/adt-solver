module Z3Interpreter

open System
open System.Collections.Generic
open System.IO
open Microsoft.FSharp.Collections
open Microsoft.Z3
open ProofBased
open SMTLIB2.Prelude
open SMTLIB2
open Utils.IntOps

module AST =
  type Name = string

  type ArgsNum = int

  type  Type =
    | Boolean
    | Integer
    | ADT of Name
    member x.toSort =
      match x with
      | Boolean -> BoolSort
      | Integer -> IntSort
      | ADT n -> ADTSort n
  
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
    | ForAllTyped of (Name * Type) list * Expr
    | ForAll of Name array * Expr
    | App of Name * Expr list
    | Ite of Expr * Expr * Expr
    | SMTExpr of smtExpr
    
    member x.StructEq y =
      let rec helper (x,y) = 
        match x, y with
        | Var _, Var _ -> true
        | Int x, Int y -> x = y 
        | Bool x, Bool y -> x = y 
        | Eq (x1, y1), Eq (x2, y2) 
        | Lt (x1, y1), Eq (x2, y2)
        | Gt (x1, y1), Gt (x2, y2)
        | Le (x1, y1), Le (x2, y2)
        | Ge (x1, y1), Ge (x2, y2)
        | Mod (x1, y1), Mod (x2, y2)
        | Add (x1, y1), Add (x2, y2)
        | Subtract (x1, y1), Subtract (x2, y2)
        | Mul (x1, y1), Mul (x2, y2)
        | Implies (x1, y1), Implies (x2, y2) -> helper (x1, x2) && helper (y1, y2)
        | And exprs1, And exprs2
        | Or exprs1, Or exprs2 when Array.length exprs1 = Array.length exprs2 ->
          Array.fold2 (fun acc x y -> acc && helper (x, y)) true exprs1 exprs2
        | Apply (name1, args1), Apply (name2, args2) when name1 = name2 ->
          List.fold2 (fun acc x y -> acc && helper (x, y)) true args1 args2
        | ForAll (names1, expr1), ForAll (names2, expr2) when names1 = names2 -> helper (expr1, expr2)
        | Neg expr1, Neg expr2
        | Not expr1, Not expr2 -> helper (expr1, expr2)
        | App (name1, args1), App (name2, args2) when name1 = name2 ->
          List.fold2 (fun acc x y -> acc && helper (x, y)) true args1 args2
        | Ite (x1, y1, z1), Ite (x2, y2, z2) -> helper (x1, x2) && helper (y1, y2) && helper (z1, z2) 
        | _ -> false
      helper (x, y)
  
  module Expr =
    let forallBody =
      function
        | ForAllTyped (_, x) | ForAll (_, x) -> Some x
        | x -> Some x
        
    let And = function
      | [ expr ] -> expr
      | exprs -> And (Array.ofList exprs)
    let Or = function
      | [ expr ] -> expr
      | exprs -> Or (Array.ofList exprs)

  
  let rec expr2smtExpr =
    function
    | Int i -> Number i
    | Bool b -> BoolConst b
    | Eq (expr1, expr2) -> smtExpr.Apply (eqOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Gt (expr1, expr2) -> smtExpr.Apply (grOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Lt (expr1, expr2) -> smtExpr.Apply (lsOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Le (expr1, expr2) -> smtExpr.Apply (leqOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Ge (expr1, expr2) -> smtExpr.Apply (geqOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Add (expr1, expr2) -> add (expr2smtExpr expr1) (expr2smtExpr expr2)
    | Subtract (expr1, expr2) -> smtExpr.Apply (minusOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Neg expr -> neg (expr2smtExpr expr)
    | Mod (expr1, expr2) -> smtExpr.Apply (modOp, [ expr2smtExpr expr1; expr2smtExpr expr2 ])
    | Mul (expr1, expr2) -> mult (expr2smtExpr expr1) (expr2smtExpr expr2)
    | And exprs -> Array.map expr2smtExpr exprs |> Array.toList |> smtExpr.And
    | Or exprs -> Array.map expr2smtExpr exprs |> Array.toList |> smtExpr.Or
    | Not expr -> expr2smtExpr expr |> smtExpr.Not
    | Implies (expr1, expr2) -> Hence (expr2smtExpr expr1, expr2smtExpr expr2)
    | Var n -> Ident (n, IntSort)
    | App (n, exprs)
    | Apply (n, exprs) -> smtExpr.Apply (UserDefinedOperation (n, [], IntSort), List.map expr2smtExpr exprs)
    | ForAll (names, e) ->
      QuantifierApplication (
        names |> Array.map (fun n -> (n, IntSort)) |> Array.toList |> Quantifiers.forall,
        expr2smtExpr e
      )
    | ForAllTyped (vars, e) ->
      QuantifierApplication (
        vars |> List.map (fun (n, (t: Type)) -> (n, t.toSort)) |> Quantifiers.forall,
        expr2smtExpr e
      )
    
    | Ite (expr1, expr2, expr3) -> smtExpr.Ite (expr2smtExpr expr1, expr2smtExpr expr2, expr2smtExpr expr3)
    | SMTExpr e -> e
    | o -> failwith $"{o}" 
  type Definition = Name * Name list * Type * Expr

  type VarCtx = Map<Name, Microsoft.Z3.Expr>
  type DecFunsCtx = Map<Name, FuncDecl>
  type DataTypeCtx = Map<Name, DatatypeSort>
  type FunCtx = Map<Name, Function>

  and Env =
    { ctxSlvr: Context
      ctxVars: VarCtx
      ctxFuns: FunCtx
      ctxDecfuns: DecFunsCtx
      actives: Name list
      ctxDataType: DataTypeCtx }

  and Function = Name list * Expr

  let newEnv args =
    { ctxSlvr = new Context (args |> dict |> Dictionary)
      ctxVars = Map.empty
      ctxFuns = Map.empty
      ctxDecfuns = Map.empty
      ctxDataType = Map.empty
      actives = [] }

  type Constructor =  Name * Type list
    
  
  type Program =
    | Def of Definition
    | DeclIntConst of Name
    | DeclConst of Name * Type
    | Decl of Name * ArgsNum
    | Assert of Expr
    | DeclDataType of (Name * Constructor list) list 

  let defNames =
    List.choose (function
      | Def (n, _, _, _) -> Some n
      | _ -> None)

  
  
  let program2originalCommand = function
    | Def (n, ns, t, e) ->
      Definition (DefineFun (n, List.map (fun n -> (n, IntSort)) ns, t.toSort, expr2smtExpr e))
    | DeclIntConst n -> Command (DeclareConst (n, IntSort))
    | DeclConst (n, t) ->
      let t' =
        match t with
        | Integer -> IntSort
        | Boolean -> BoolSort
        | ADT s -> ADTSort s
      Command (DeclareConst (n, t'))
    | Decl (n, num) ->
      Command (DeclareFun (n, List.init num (fun _ -> IntSort), BoolSort))
    | Assert e -> originalCommand.Assert (expr2smtExpr e)
    | DeclDataType (*n, cs*) ds as k ->
      Command (command.DeclareDatatypes
        (ds |> List.map ( fun (n, cs) ->
        let constructor p name argSorts adtName =
          ElementaryOperation (name, argSorts, ADTSort adtName),
          ElementaryOperation ($"is-{name}", [ADTSort adtName], BoolSort),
          List.mapi (fun i s -> ElementaryOperation ($"{n}x{i + p}", [ADTSort n], s)) argSorts 
        
        let args = List.map (fun (t: Type) -> t.toSort)
        (n,
            (0, cs) ||> List.mapFold (fun acc (n', t) -> constructor acc n' (args t) n, List.length t + acc)
            |> fst)
        )))

      // Command (command.DeclareDatatype
           // (n,
            // (0, cs) ||> List.mapFold (fun acc (n', t) -> constructor acc n' (args t) n, List.length t + acc)
            // |> fst)) 
    
  let rec smtExpr2expr =
    function
    | Number i when i >= 0 -> Int i
    | Number i when i < 0 -> Neg (Int (-1L * i))
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
    | a -> SMTExpr a
      // __notImplemented__()
    | _ -> __notImplemented__()

  let rec smtExpr2expr' =
    function
    | Number i when i >= 0 -> Int i
    | Number i when i < 0 -> Neg (Int (-1L * i))
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
    | Definition (DefineFun (name, args, sort, body)) ->
      let t = 
        match sort with
        | IntSort -> Integer
        | _ -> Boolean
      Def (name, List.map fst args, t, smtExpr2expr body)
    | Command (DeclareFun (name, args, _)) -> Decl (name, args.Length)
    | originalCommand.Assert expr -> Assert (smtExpr2expr expr)
    | o ->
      printfn $"{o}"
      __notImplemented__()
    
  let rec aboba =
    function
    | Definition (DefineFun (name, args, sort, body)) ->
      let t = 
        match sort with
        | IntSort -> Integer
        | _ -> Boolean
      Def (name, List.map fst args, t, smtExpr2expr' body)
    | Command (DeclareFun (name, args, _)) -> Decl (name, args.Length)
    | originalCommand.Assert expr -> Assert (smtExpr2expr' expr)
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
      | Def (n, args, t, e) -> Def (n, args, t, e |> toVar)
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
      | App (n, exprs) -> App (n, exprs |> List.map helper')
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
  
  let rec normalizeAst (env: Env) =
    function
      | Var n ->
        env.ctxDecfuns.TryFind n
        |> function
          | Some _ ->
            App (n, [])
          | _ -> Var n
      | Eq (e1, e2) -> Eq (normalizeAst env e1, normalizeAst env e2)
      | Lt (e1, e2) -> Lt (normalizeAst env e1, normalizeAst env e2)
      | Gt (e1, e2) -> Gt (normalizeAst env e1, normalizeAst env e2)
      | Le (e1, e2) -> Le (normalizeAst env e1, normalizeAst env e2)
      | Ge (e1, e2) -> Ge (normalizeAst env e1, normalizeAst env e2)
      | Mod (e1, e2) -> Mod (normalizeAst env e1, normalizeAst env e2)
      | Add (e1, e2) -> Add (normalizeAst env e1, normalizeAst env e2)
      | Subtract (e1, e2) -> Subtract (normalizeAst env e1, normalizeAst env e2)
      | Mul (e1, e2) -> Mul (normalizeAst env e1, normalizeAst env e2)
      | Implies (e1, e2) -> Implies (normalizeAst env e1, normalizeAst env e2)
      | Neg e -> Neg (normalizeAst env e)
      | Not e -> Not (normalizeAst env e)
      | And exprs -> And (Array.map (normalizeAst env) exprs) 
      | Or exprs -> Or (Array.map (normalizeAst env) exprs)
      | Apply (n, exprs) -> Apply (n, List.map (normalizeAst env) exprs) 
      | App (n, exprs) -> App (n, List.map (normalizeAst env) exprs) 
      | ForAllTyped (vars, expr) -> ForAllTyped (vars, normalizeAst env expr) 
      | ForAll (names, expr) -> ForAll (names, normalizeAst env expr) 
      | Ite (e1, e2, e3) -> Ite (normalizeAst env e1, normalizeAst env e2, normalizeAst env e3)
      | otherwise -> otherwise
      
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
      | Var x ->
        env.ctxVars |> Map.tryFind x
        |> function
          | Some v -> v
          | None -> evalExpr env (App (x, []))
      | App (name, expr) ->
        // printfn $"{name}"
        let decFun = env.ctxDecfuns |> Map.find name in
        let args = List.map (evalExpr env) expr
        env.ctxSlvr.MkApp (decFun, Array.ofList args)
      | Apply (n, [ x; y ]) when n = "distinct" -> evalExpr env (Not (Eq (x, y)))
      | Apply (n, [ x; y ]) when n = "div" -> env.ctxSlvr.MkDiv (evalExpr env x :?> ArithExpr, evalExpr env y :?> ArithExpr) 
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
        let vars: Microsoft.Z3.Expr[] = names |> Array.map (fun name -> env.ctxSlvr.MkIntConst name)
        let ctxVars = Array.foldBack2 Map.add names vars env.ctxVars
        env.ctxSlvr.MkForall (vars, evalExpr { env with ctxVars = ctxVars } expr)
      | ForAllTyped (args, expr) ->
        let vars: Microsoft.Z3.Expr list =
          args
          |> List.map
               (fun (name, t) ->
                  match t with
                  | Integer -> env.ctxSlvr.MkIntConst name 
                  | Boolean -> env.ctxSlvr.MkBoolConst name 
                  | ADT n -> env.ctxSlvr.MkConst (name, env.ctxDataType |> Map.find n))
          
        let names, _ = List.unzip args 
        
        let ctxVars =
          List.zip names vars
          |> List.fold (fun acc (name, value) -> acc |> Map.add name value) env.ctxVars in
        
        env.ctxSlvr.MkForall (List.toArray vars, evalExpr { env with ctxVars = ctxVars } expr)
 
      | Ite (exprIf, exprThen, exprElse) ->
        env.ctxSlvr.MkITE (evalExpr env exprIf :?> BoolExpr, evalExpr env exprThen, evalExpr env exprElse)
      

  let evalCmds =
    fun env (solver: Solver) ->
      List.fold
        (fun (env, solver: Solver, expr) cmd ->
          match cmd with
          | DeclDataType (_) -> failwith ""
          // | DeclDataType (name, constructors) ->
          //   let pCtx = ref env.ctxSlvr
          //   
          //   let names, constructors' =
          //     constructors
          //     |> List.map
          //          (fun (n: String, ts) ->
          //             let mkSort: Type -> Sort = 
          //               function
          //                 | Boolean -> env.ctxSlvr.MkBoolSort ()  
          //                 | Integer -> env.ctxSlvr.MkIntSort ()  
          //                 | ADT n when n <> name ->
          //                   env.ctxDataType |> Map.tryFind n
          //                   |> function
          //                     | Some s -> s :> Sort
          //                     | None -> env.ctxSlvr.MkUninterpretedSort n
          //                 | ADT _ -> null
          //             let names, sorts = ts |> List.mapi (fun i t -> ($"x{i}", mkSort t)) |> List.toArray |> Array.unzip
          //             (n, env.ctxSlvr.MkConstructor (n, $"tester_{n}", names, sorts)) )
          //     |> List.unzip
          //   
          //   let adt = env.ctxSlvr.MkDatatypeSort (name, List.toArray constructors')
          //   
          //   let ctxDecfuns' =
          //     List.fold2 (fun ctx id n -> ctx |> Map.add n adt.Constructors[id])
          //       env.ctxDecfuns (seq { 0 .. names.Length - 1 } |> List.ofSeq)
          //       names
          //   
          //   ({ env with ctxDecfuns = ctxDecfuns'; ctxDataType = env.ctxDataType |> Map.add name adt }, solver, expr)
            
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
            | ADT tName ->
              let adtConst = env.ctxSlvr.MkConstDecl (n, env.ctxDataType |> Map.find tName) 
              
              ({ env with
                  ctxDecfuns =  env.ctxDecfuns |> Map.add n adtConst },
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
          | Def (n, args, t, b) -> ({ env with ctxFuns = define env (n, args, b) }, solver, expr)
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
    |> List.map (fun (n, i) -> Def (n, [], Integer, Int i))

  module SoftSolver =
    let hardConstants (env: Env) =
      env.ctxVars |> Map.filter (fun k _ -> k.Contains "soft" |> not)

    let model (env: Env) (solver: Solver) =
      hardConstants env
      |> Map.toList
      |> List.fold (fun acc (n, v) -> (n, solver.Model.Double (solver.Model.Eval (v, true)) |> int64) :: acc) []
      |> List.map (fun (n, i) -> Def (n, [], Integer, Int i))

    type z3SoftSolve<'a, 'b> =
      { env: Env
        solver: Solver
        unsat: Env -> Solver -> 'a
        sat: Env -> Solver -> 'b
        cmds: Program list }

    let z3softSolver (x: z3SoftSolve<_, _>) =
      let env, solver, _ = evalCmds x.env x.solver x.cmds
      
      let softVars =
        env.actives |> List.map (fun n -> Map.find n env.ctxVars) |> List.toArray
      // printfn "HERE"
      // for x in env.actives do printfn $"s {x}"
      // for x in softVars do printfn $" {x}"
      
      match x.solver.Check softVars with
      // match x.solver.Check () with
      | Status.SATISFIABLE ->
        // printfn "!!!!!!!!!!! SATISFIABLE"
        SAT <| x.sat env solver
      | Status.UNSATISFIABLE ->
        // printfn "UNSATISFIABLE"
        UNSAT <| x.unsat env solver
      | _ -> failwith "UNKNOWN"

    let softUnsat env (solver: Solver) =
      let unsatCoreNames = solver.UnsatCore |> Array.map string |> Set
      let intersection = Set env.actives |> Set.intersect unsatCoreNames
      
      
      // printfn $"{unsatCoreNames}"
      // printfn $"{intersection}"
      
      if intersection.IsEmpty then
        None // UNKNONW
      else
        Some ({ env with
            actives = env.actives |> List.tail  },
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
        | SAT x -> Ok x
        | UNSAT (Some (env', solver')) -> solve env' solver'
        | UNSAT None -> Error "!!!!!UNKNOWN"

    let setSoftAsserts env (solver: Solver) (constants: Program list) =
      let constNames = constants |> List.choose (function Def(n, [], _, _) -> Some n | _ -> None)
      let softNames = constNames |> List.map (fun n -> $"soft_{n}")
      
      constNames
      |> List.map2
        (fun softn n -> Assert (Implies (Var softn, Or [| Eq (Var n, Int 0); Eq (Var n, Int 1) |])))
        softNames
      |> List.append (softNames |> List.map (fun n -> DeclConst (n, Boolean)))
      |> setCommands { env with actives = softNames } solver
      // setCommands { env with actives = softNames } solver []

    let setSoftAssertsKEK (constants: Program list) =
      let constNames = constants |> List.choose (function Def(n, [], _, _) -> Some n | _ -> None)
      let softNames = constNames |> List.map (fun n -> $"soft_{n}")
      
      constNames
      |> List.map2
        (fun softn n -> Assert (Implies (Var softn, Or [| Eq (Var n, Int 0); Eq (Var n, Int 1) |])))
        softNames
      |> List.append (softNames |> List.map (fun n -> DeclConst (n, Boolean)))
      

  let emptyEnv argss =
    { ctxSlvr = new Context (argss |> dict |> Dictionary)
      ctxVars = Map.empty
      ctxFuns = Map.empty
      ctxDecfuns = Map.empty
      ctxDataType = Map.empty 
      actives = [] }





// let test () =
//   let emptyEnv argss =
//     { ctxSlvr = new Context (argss |> dict |> Dictionary)
//       ctxVars = Map.empty
//       ctxFuns = Map.empty
//       ctxDecfuns = Map.empty
//       actives = []
//       ctxDataType = Map.empty }
//   let env = emptyEnv [||]
//   let solver = env.ctxSlvr.MkSolver "ALL"
//   solver.Push ()
//   
//   Interpreter.evalCmds env solver
//     [
//      DeclDataType
//       ("list_407", [("nil_468", []); ("cons_401", [Integer; ADT "list_407"])])
//      DeclDataType
//        ("E_62",
//         [("V_32", [Integer]); ("N_120", [Integer]);
//          ("Mul_13", [ADT "E_62"; ADT "E_62"]); ("Eq_0", [ADT "E_62"; ADT "E_62"]);
//          ("Add_480", [ADT "E_62"; ADT "E_62"])])
//      DeclDataType
//        ("P_616",
//         [("x_126870", [Integer; ADT "E_62"]);
//          ("While_0", [ADT "E_62"; ADT "list_408"]); ("Print_0", [ADT "E_62"]);
//          ("If_0", [ADT "E_62"; ADT "list_408"; ADT "list_408"])])
//      DeclDataType
//        ("list_408", [("nil_469", []); ("cons_402", [ADT "P_616"; ADT "list_408"])])
//      Def ("Z_2776", [], Integer, Int 0L)
//      Def ("S_640", ["x"], Integer, Add (Var "x", Int 1L))
//      // DeclConst ("x0", ADT "P_616")
//      // DeclConst ("x1", ADT "list_407")
//      // DeclConst ("x10", Integer)
//      // DeclConst ("x11", ADT "list_407")
//      // DeclConst ("x12", Integer)
//      // DeclConst ("x13", ADT "E_62")
//      // DeclConst ("x14", ADT "E_62")
//      // DeclConst ("x15", ADT "list_408")
//      // DeclConst ("x16", ADT "list_408")
//      // DeclConst ("x17", ADT "E_62")
//      // DeclConst ("x2", ADT "P_616")
//      // DeclConst ("x3", ADT "list_407")
//      // DeclConst ("x4", Integer)
//      // DeclConst ("x5", ADT "list_407")
//      // DeclConst ("x6", Integer)
//      // DeclConst ("x7", ADT "list_407")
//      // DeclConst ("x8", Integer)
//      // DeclConst ("x9", ADT "list_407")
//      // Assert
//      //   (And
//      //      [|Eq
//      //          (App ("cons_402", [Var "x0"; App ("nil_469", [])]), App ("nil_469", []));
//      //        Eq
//      //          (App ("cons_402", [Var "x2"; App ("nil_469", [])]), App ("nil_469", []));
//      //        Not (Eq (Var "x4", Var "x6"));
//      //        Or
//      //          [|And
//      //              [|Eq (App ("nil_468", []), App ("nil_468", []));
//      //                Eq
//      //                  (App ("nil_468", []), App ("cons_401", [Var "x10"; Var "x11"]))|];
//      //            And
//      //              [|Eq (App ("nil_468", []), App ("cons_401", [Var "x8"; Var "x9"]));
//      //                Eq (App ("nil_468", []), App ("nil_468", []))|];
//      //            And
//      //              [|Eq (App ("nil_468", []), App ("cons_401", [Var "x4"; Var "x5"]));
//      //                Eq (App ("nil_468", []), App ("cons_401", [Var "x6"; Var "x7"]))|]|];
//      //        Or
//      //          [|And
//      //              [|Eq (Var "x2", App ("Print_0", [Var "x17"]));
//      //                Eq (Var "x0", App ("Print_0", [Var "x17"]))|];
//      //            And
//      //              [|Eq (Var "x2", App ("If_0", [Var "x14"; Var "x16"; Var "x15"]));
//      //                Eq (Var "x0", App ("If_0", [Var "x14"; Var "x15"; Var "x16"]))|];
//      //            And
//      //              [|Eq (Var "x2", App ("x_126870", [Var "x12"; Var "x13"]));
//      //                Eq (Var "x0", App ("x_126870", [Var "x12"; Var "x13"]))|]|];
//      //        Or
//      //          [|And
//      //              [|Eq (Var "x1", App ("nil_468", []));
//      //                Eq (Var "x3", App ("cons_401", [Var "x10"; Var "x11"]))|];
//      //            And
//      //              [|Eq (Var "x1", App ("cons_401", [Var "x8"; Var "x9"]));
//      //                Eq (Var "x3", App ("nil_468", []))|];
//      //            And
//      //              [|Eq (Var "x1", App ("cons_401", [Var "x4"; Var "x5"]));
//      //                Eq (Var "x3", App ("cons_401", [Var "x6"; Var "x7"]))|]|];
//      //        Or
//      //          [|And
//      //              [|Eq (Var "x2", App ("Print_0", [Var "x17"]));
//      //                Eq (Var "x0", App ("Print_0", [Var "x17"]))|];
//      //            And
//      //              [|Eq (Var "x2", App ("If_0", [Var "x14"; Var "x16"; Var "x15"]));
//      //                Eq (Var "x0", App ("If_0", [Var "x14"; Var "x15"; Var "x16"]))|];
//      //            And
//      //              [|Eq (Var "x2", App ("x_126870", [Var "x12"; Var "x13"]));
//      //                Eq (Var "x0", App ("x_126870", [Var "x12"; Var "x13"]))|]|]|])
//      ]
//   |> fun (env, solver, e) ->
//     printfn $"{env}"
//     for x in env.ctxDecfuns do printfn $"{x}"
//     printfn $"{e}"