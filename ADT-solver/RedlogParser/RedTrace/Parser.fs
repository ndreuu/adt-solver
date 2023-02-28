module RedlogParser.RedTrace.Parser

open System
open Antlr4.Runtime
open Antlr4.Runtime.Tree
open Microsoft.FSharp.Core
open SMTLIB2

let mulOp = ElementaryOperation ("*", [ IntSort; IntSort ], IntSort)
let addOp = ElementaryOperation ("+", [ IntSort; IntSort ], IntSort)


let parseNumber (number: RedTraceParser.NumberContext) = number.NUM().GetText () |> Int64.Parse

let parsePower (power: RedTraceParser.PowerContext) =
  match (power.GetChild 1, power.GetChild 3) with
  | (:? RedTraceParser.IdContext as id), (:? RedTraceParser.NumberContext as number) ->
    let app = Apply (UserDefinedOperation (id.GetText (), [], IntSort), [])

    let power app number =
      let rec helper app acc (n) =
        match n with
        | 0 -> acc
        | n -> helper app (Apply (mulOp, [ app; acc ])) (n - 1)

      helper app app (number - 1)

    power app (number.NUM().GetText () |> Int32.Parse)

let parseFactor (factor: RedTraceParser.FactorContext) =
  match (factor.GetChild 1, factor.GetChild 3) with
  | (:? RedTraceParser.PowerContext as pow), (:? RedTraceParser.NumberContext as number) ->
    let power = pow |> parsePower
    let coeff = Number (number |> parseNumber)
    Apply (mulOp, [ power; coeff ])

let parseNum (num: RedTraceParser.NumContext) =
  match num.GetChild 1 with
  | :? RedTraceParser.NumberContext as number -> Number (number |> parseNumber)


let parseFactorOrNum (v: IParseTree) =
  match v with
  | :? RedTraceParser.FactorContext as factor -> factor |> parseFactor
  | :? RedTraceParser.NumContext as num -> num |> parseNum

let rec parseMul (mul: RedTraceParser.MulContext) =
  match mul.GetChild 0 with
  | :? RedTraceParser.FactorContext as factor -> parseFactor factor
  | :? RedTraceParser.PowerContext as power ->
    let child = mul.GetChild 1
    let power = power |> parsePower

    match child with
    | :? RedTraceParser.FactorContext
    | :? RedTraceParser.NumContext as v ->
      let acc = Apply (mulOp, [ power; v |> parseFactorOrNum ])

      let factorNums i n =
        let rec helper acc i n =
          match acc with
          | _ when i < n ->
            match mul.GetChild i with
            | :? RedTraceParser.FactorContext
            | :? RedTraceParser.NumContext as v -> helper (parseFactorOrNum v :: acc) (i + 1) n
            | _ -> helper acc (i + 1) n
          | _ -> acc

        helper [] i n |> List.rev

      factorNums 2 mul.ChildCount
      |> List.fold (fun acc v -> Apply (addOp, [ acc; Apply (mulOp, [ power; v ]) ])) acc

    | _ ->
      let acc =
        match mul.GetChild 2 with
        | :? RedTraceParser.MulContext as mul -> Apply (mulOp, [ power; parseMul mul ])

      let muls i n =
        let rec helper acc i n =
          match acc with
          | _ when i < n ->
            match mul.GetChild i with
            | :? RedTraceParser.MulContext as m -> helper (parseFactorOrNum m :: acc) (i + 1) n
            | _ -> helper acc (i + 1) n
          | _ -> acc

        helper [] i n |> List.rev

      muls 3 mul.ChildCount
      |> List.fold (fun acc v -> Apply (addOp, [ acc; Apply (mulOp, [ power; v ]) ])) acc

let parseNcong (ncong: RedTraceParser.NcgongContext) =
  match ncong.GetChild 2 with
  | :? RedTraceParser.FactorContext
  | :? RedTraceParser.NumContext as v -> parseFactorOrNum v
  | _ ->
    match ncong.GetChild 3 with
    | :? RedTraceParser.MulContext as mul -> parseMul mul

let rec parseBody (body: RedTraceParser.BodyContext) =
  let factorNumMuls i n =
    let rec helper acc i n =
      match acc with
      | _ when i < n ->
        match body.GetChild i with
        | :? RedTraceParser.FactorContext
        | :? RedTraceParser.NumContext as v -> helper (parseFactorOrNum v :: acc) (i + 1) n
        | :? RedTraceParser.MulContext as m -> helper (parseMul m :: acc) (i + 1) n
        | _ -> helper acc (i + 1) n
      | _ -> acc

    helper [] i n |> List.rev

  match body.GetChild 1 with
  | :? RedTraceParser.FactorContext
  | :? RedTraceParser.NumContext as v ->
    let acc = parseFactorOrNum v

    factorNumMuls 2 body.ChildCount
    |> List.fold (fun acc v -> Apply (addOp, [ acc; v ])) acc

  | _ ->
    match body.GetChild 2 with
    | :? RedTraceParser.MulContext as mul ->
      let acc = parseMul mul

      factorNumMuls 4 body.ChildCount
      |> List.fold (fun acc v -> Apply (addOp, [ acc; v ])) acc


let eqOp = ElementaryOperation ("=", [ IntSort; IntSort ], BoolSort)
let leqOp = ElementaryOperation ("<=", [ IntSort; IntSort ], BoolSort)
let geqOp = ElementaryOperation (">=", [ IntSort; IntSort ], BoolSort)
let modOp = ElementaryOperation ("mod", [ IntSort; IntSort ], IntSort)

let rec exprs (expr: RedTraceParser.ExprContext) i n =
  let rec helper acc i n =
    match acc with
    | _ when i < n ->
      match expr.GetChild i with
      | :? RedTraceParser.ExprContext as e -> helper (parseExpr' e :: acc) (i + 1) n
      | _ -> helper acc (i + 1) n
    | _ -> acc

  helper [] i n |> List.rev

and parseExpr' (expr: RedTraceParser.ExprContext) =
  match expr.GetChild 1 with
  | :? RedTraceParser.AndContext -> And <| exprs expr 2 expr.ChildCount
  | :? RedTraceParser.OrContext -> Or <| exprs expr 2 expr.ChildCount
  | :? RedTraceParser.NcgongContext as ncong ->
    let m = parseNcong ncong

    let l =
      match expr.GetChild 2 with
      | :? RedTraceParser.BodyContext as body -> parseBody body

    let r =
      match expr.GetChild 3 with
      | :? RedTraceParser.NilContext -> Number 0

    Not (Apply (eqOp, [ Apply (modOp, [ l; m ]); r ]))
  | :? RedTraceParser.EqualContext ->
    let l =
      match expr.GetChild 2 with
      | :? RedTraceParser.BodyContext as body -> parseBody body

    let r =
      match expr.GetChild 3 with
      | :? RedTraceParser.NilContext -> Number 0

    Apply (eqOp, [ l; r ])
  | :? RedTraceParser.NeqContext ->
    let l =
      match expr.GetChild 2 with
      | :? RedTraceParser.BodyContext as body -> parseBody body

    let r =
      match expr.GetChild 3 with
      | :? RedTraceParser.NilContext -> Number 0

    Not (Apply (eqOp, [ l; r ]))
  | :? RedTraceParser.LeqContext ->
    let l =
      match expr.GetChild 2 with
      | :? RedTraceParser.BodyContext as body -> parseBody body

    let r =
      match expr.GetChild 3 with
      | :? RedTraceParser.NilContext -> Number 0

    Apply (leqOp, [ l; r ])
  | :? RedTraceParser.GeqContext ->
    let l =
      match expr.GetChild 2 with
      | :? RedTraceParser.BodyContext as body -> parseBody body

    let r =
      match expr.GetChild 3 with
      | :? RedTraceParser.NilContext -> Number 0

    Apply (geqOp, [ l; r ])

  | :? RedTraceParser.BallContext ->
    let head =
      match expr.GetChild 4 with
      | :? RedTraceParser.ExprContext as e -> parseExpr' e

    head

  | _ -> failwith "unreachable"

let parsePremises (expr: RedTraceParser.ExprContext) =
  let rec parsePremises' (expr: RedTraceParser.ExprContext) acc =
    let rec exprs (expr: RedTraceParser.ExprContext) i n =
      let rec helper acc' i n =
        match acc' with
        | _ when i < n ->
          match expr.GetChild i with
          | :? RedTraceParser.ExprContext as e -> helper (parsePremises' e acc :: acc') (i + 1) n
          | _ -> helper acc' (i + 1) n
        | _ -> acc'

      helper [] i n |> List.rev

    match expr.GetChild 1 with
    | :? RedTraceParser.BallContext ->
      let body =
        match expr.GetChild 4 with
        | :? RedTraceParser.ExprContext as e -> parseExpr' e

      let acc =
        match expr.GetChild 3 with
        | :? RedTraceParser.ExprContext as e -> parsePremises' e acc

      match acc, body with
      | BoolConst true, BoolConst true -> BoolConst true
      | BoolConst true, body -> body
      | acc, BoolConst true -> acc
      | _ -> And [ acc; body ]

    | :? RedTraceParser.AndContext
    | :? RedTraceParser.OrContext ->
      exprs expr 2 expr.ChildCount
      |> List.fold
           (fun acc e ->
             match acc, e with
             | BoolConst true, BoolConst true -> BoolConst true
             | BoolConst true, e -> e
             | acc, BoolConst true -> acc
             | _ -> And [ acc; e ])
           acc
    | _ -> acc

  parsePremises' expr (BoolConst true)

let parseVars (expr: RedTraceParser.ExprContext) = 
  let rec parseVars' (expr: RedTraceParser.ExprContext) acc =
    let rec exprs (expr: RedTraceParser.ExprContext) i n =
      let rec helper acc' i n =
        match acc' with
        | _ when i < n ->
          match expr.GetChild i with
          | :? RedTraceParser.ExprContext as e -> helper (parseVars' e acc :: acc') (i + 1) n
          | _ -> helper acc' (i + 1) n
        | _ -> acc'
      
      helper [] i n |> List.rev
    
    match expr.GetChild 1 with
    | :? RedTraceParser.BallContext ->
      let acc = 
        match expr.GetChild 3 with
        | :? RedTraceParser.ExprContext as e -> parseVars' e acc      
      
      
      match expr.GetChild 2 with
      | :? RedTraceParser.IdContext as id -> id.GetText() :: acc
      
    | :? RedTraceParser.AndContext | :? RedTraceParser.OrContext ->
      exprs expr 2 expr.ChildCount
      |> List.fold (@) []
    | _ -> acc
    
  (parseVars' expr []) |> Set.ofList

let translateToSmt line =
  let lexer = RedTraceLexer (CharStreams.fromString line)
  let tokens = CommonTokenStream lexer
  let parser = RedTraceParser tokens

  let tree: RedTraceParser.ProgContext = parser.prog ()

  match tree.GetChild 1 with
  | :? RedTraceParser.ExprContext as expr ->
      let head = parseExpr' expr
      let body = parsePremises expr
      let vars = parseVars expr
      
      QuantifierApplication ([ForallQuantifier (Set.map (fun v -> (v, IntSort)) vars |> Set.toList)], Hence (body, head))



  



let sd () =
  let line =
    """(!*fof (pasf) (and (or (equal (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) (
(c2 . 1) ((c5 . 1) . -1) . 12) ((c5 . 1) . 1) . -12) nil) ((ncong ((c2 . 1) ((c3
. 1) . 1))) (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c5 . 1) . 1) . -12) nil)
(equal (((c2 . 1) . 1)) nil) (equal (((c3 . 1) . 1)) nil)) (or (equal (((c1 . 1)
((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12) ((c5 . 1) . 1) .
-12) nil) ((ncong ((c2 . 1) ((c4 . 1) . 1))) (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1)
. 1)) ((c5 . 1) . 1) . -12) nil) (equal (((c2 . 1) . 1)) nil) (equal (((c4 . 1)
. 1)) nil)) (or (neq (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c5 . 1) . 1) .
-12) nil) (equal (((c5 . 1) . 1) . -12) nil)) (ball !_k8 (ball !_k7 (or (ball
!_k2 (or (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) ((c4 . 1) . 1))) (((!_k2
. 1) ((c4 . 1) . 1)) ((!_k7 . 1) ((c4 . 1) . -1))) nil) (neq (((!_k2 . 1) ((c2 .
1) . 1)) ((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12
) ((c5 . 1) . 1) . -12) nil)) (or (and (leq (((!_k2 . 1) . 1) ((c3 . 1) . 1))
nil) (geq (((!_k2 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k2 . 1) . 1)) nil))
(and (geq (((!_k2 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k2 . 1) . 1) ((c3 . 1
) . -1)) nil) (neq (((!_k2 . 1) . 1)) nil)))) (equal (((c4 . 1) . 1)) nil) ((
ncong ((c4 . 1) . 1)) (((!_k7 . 1) . 1) ((c5 . 1) . -1) . 12) nil)) (or (and (
leq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2) ((c4 . 1) . 1)) ((c4 . 1) . 1)
) nil) (geq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2) ((c4 . 1) . -1)) ((c4
. 1) . -1)) nil)) (and (geq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2) ((c4 .
1) . 1)) ((c4 . 1) . 1)) nil) (leq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2)
((c4 . 1) . -1)) ((c4 . 1) . -1)) nil)))) (or (and (leq (((!_k8 . 1) . 1) ((c3 .
1) . 1)) nil) (geq (((!_k8 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k8 . 1) . 1
)) nil)) (and (geq (((!_k8 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k8 . 1) . 1)
((c3 . 1) . -1)) nil) (neq (((!_k8 . 1) . 1)) nil)))) (ball !_k4 (or (equal (((
c4 . 1) . 1)) nil) (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (
equal (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12)
((c5 . 1) . 1) . -12) nil) ((ncong ((c2 . 1) ((c4 . 1) . 1))) (((!_k4 . 1) . 1)
((c1 . 1) ((c3 . 1) . -1) ((c4 . 1) . -1)) ((c5 . 1) . -1) . 12) nil) ((ncong ((
c2 . 2) ((c3 . 1) ((c4 . 1) . 1)))) (((!_k4 . 1) ((c2 . 1) ((c4 . 1) . 1)))) nil
)) (or (and (leq (((!_k4 . 1) . 1) ((c2 . 3) ((c3 . 2) ((c4 . 1) . 1))) ((c2 . 1
) ((c4 . 1) . 1))) nil) (geq (((!_k4 . 1) . 1) ((c2 . 3) ((c3 . 2) ((c4 . 1) .
-1))) ((c2 . 1) ((c4 . 1) . -1))) nil)) (and (geq (((!_k4 . 1) . 1) ((c2 . 3) ((
c3 . 2) ((c4 . 1) . 1))) ((c2 . 1) ((c4 . 1) . 1))) nil) (leq (((!_k4 . 1) . 1)
((c2 . 3) ((c3 . 2) ((c4 . 1) . -1))) ((c2 . 1) ((c4 . 1) . -1))) nil)))) (ball
!_k2 (or (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k2 . 1) . 1)
((c5 . 1) . -1) . 12) nil) (neq (((!_k2 . 1) ((c2 . 1) . 1)) ((c1 . 1) ((c3 . 1)
. 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12) ((c5 . 1) . 1) . -12) nil))
(or (and (leq (((!_k2 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k2 . 1) . 1) ((c3
. 1) . -1)) nil) (neq (((!_k2 . 1) . 1)) nil)) (and (geq (((!_k2 . 1) . 1) ((c3
. 1) . 1)) nil) (leq (((!_k2 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k2 . 1) .
1)) nil)))) (ball !_k10 (or (equal (((c4 . 1) . 1)) nil) ((ncong ((c4 . 1) . 1))
(((!_k10 . 1) . 1) ((c5 . 1) . -1) . 12) nil) (neq (((!_k10 . 1) ((c2 . 1) . 1))
((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12) ((c5 .
1) . 1) . -12) nil)) (or (and (leq (((!_k10 . 1) . 1) ((c4 . 1) . 1)) nil) (geq
(((!_k10 . 1) . 1) ((c4 . 1) . -1)) nil) (neq (((!_k10 . 1) . 1)) nil)) (and (
geq (((!_k10 . 1) . 1) ((c4 . 1) . 1)) nil) (leq (((!_k10 . 1) . 1) ((c4 . 1) .
-1)) nil) (neq (((!_k10 . 1) . 1)) nil))))) t)"""

  let lexer = RedTraceLexer (CharStreams.fromString line)
  let tokens = CommonTokenStream lexer
  let parser = RedTraceParser tokens

  let tree: RedTraceParser.ProgContext = parser.prog ()

  // match tree.GetChild 1 with
  // | :? RedTraceParser.ExprContext as expr -> parseVars expr |> fun vs -> for v in vs do  printfn "%O" v
  // | :? RedTraceParser.ExprContext as expr -> translateToSmt expr |> printfn "%O"
  // match tree.GetChild 1  with
  // | :? RedTraceParser.ExprContext as e ->

  // | _  -> printfn "!"
  // let and' = expr.GetChild 0
  // printfn $"{and'}"

  ()
