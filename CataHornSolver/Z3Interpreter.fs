module Z3Interpreter

open System.Collections.Generic
open System.Numerics
open Microsoft.FSharp.Collections
// open Microsoft.Z3
open ProofBased
open SMTLIB2.Prelude
open SMTLIB2
open Utils.IntOps

module AST =
  type Name = string

  type ArgsNum = int

  type Type =
    | Boolean
    | Integer
    | ADT of Name
    member x.toSort =
      match x with
      | Boolean -> BoolSort
      | Integer -> IntSort
      | ADT n -> ADTSort n
  
  type Expr =
    | Int of bigint
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
  type Definition = Name * (Name) list * Type * Expr

  // type VarCtx = Map<Name, Microsoft.Z3.Expr>
  // type DecFunsCtx = Map<Name, FuncDecl>
  // type DataTypeCtx = Map<Name, DatatypeSort>
  type FunCtx = Map<Name, Function>

  and Env =
    { 
      
      ctxFuns: FunCtx
      
      actives: Name list
       }

  and Function = Name list * Expr

  let newEnv args =
    { 
      
      ctxFuns = Map.empty
      
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
    | DeclDataType ds ->
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

  let rec smtExpr2expr =
    function
    | Number i when i >= BigInteger.Zero -> Int i
    | Number i when i < BigInteger.Zero -> Neg (Int (BigInteger.MinusOne * i))
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
    | smtExpr.Ite (e1, e2, e3) -> Ite (smtExpr2expr e1, smtExpr2expr e2, smtExpr2expr e3)
    | a -> SMTExpr a

  let rec smtExpr2expr' =
    function
    | Number i when i >= BigInteger.Zero -> Int i
    | Number i when i < BigInteger.Zero -> Neg (Int (BigInteger.MinusOne * i))
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
        | ADTSort adt -> ADT adt 
        | _ -> Boolean
      Def (name, List.map fst args, t, smtExpr2expr body)
    | Command (DeclareFun (name, args, _)) -> Decl (name, args.Length)
    | originalCommand.Assert expr -> Assert (smtExpr2expr expr)
    | o ->
      printfn $"{o}"
      __notImplemented__()
    
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
  module SoftSolver =
    let setSoftAssertsKEK (constants: Program list) =
      let constNames = constants |> List.choose (function Def(n, [], _, _) -> Some n | _ -> None)
      let softNames = constNames |> List.map (fun n -> $"soft_{n}")
      
      constNames
      |> List.map2
        (fun softn n -> Assert (Implies (Var softn, Or [| Eq (Var n, Int 0); Eq (Var n, Int 1) |])))
        softNames
      |> List.append (softNames |> List.map (fun n -> DeclConst (n, Boolean)))
