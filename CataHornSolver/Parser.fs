module RedlogParser.RedTrace.Parser

open System
open System.IO
open System.Numerics
open System.Text.RegularExpressions
open Antlr4.Runtime
open Antlr4.Runtime.Tree
open Microsoft.FSharp.Core
open ProofBased
open SMTLIB2
open Utils.IntOps
open Z3Interpreter

let parseNumberRaw (number: RedTraceParser.NumberContext) = number.NUM().GetText () |> BigInteger.Parse
let parseNumber (number: RedTraceParser.NumberContext) =
  parseNumberRaw number 
  |> fun i ->
    if i < BigInteger.Zero then
      smtExpr.Apply (ElementaryOperation ("-", [ IntSort ], IntSort), [ Number <| BigInteger.MinusOne * i ])
    else
      Number i

let init n v =
  let rec helper acc = function
    | z when z = BigInteger.Zero -> acc
    | n -> helper (v::acc) <| n - BigInteger.One
  helper [] n 
  
let parsePower (power: RedTraceParser.PowerContext) =
  match power.GetChild 1, power.GetChild 3 with
  | :? RedTraceParser.IdContext as id, (:? RedTraceParser.NumberContext as number) ->
    let app = Expr.makeConst (id.GetText()) IntSort
    let number = parseNumberRaw number
    init number app |> List.reduce mult
  | _ -> __unreachable__ ()

let rec substituteVar oldName newName =
  function
    | Number _
    | BoolConst _
    | Let _
    | Match _
    | Ite _ as expr -> expr 
    | Ident (ident, sort) when ident = oldName -> Ident (newName, sort)
    | Ident (ident, sort) -> Ident (ident, sort)
    | Apply (UserDefinedOperation (ident, sorts, sort ), expr) 
    | Apply (ElementaryOperation (ident, sorts, sort ), expr) when ident = oldName ->
      Apply (UserDefinedOperation (newName, sorts, sort ), expr)
    | Apply (ElementaryOperation (ident, sorts, sort), exprs) 
    | Apply (UserDefinedOperation (ident, sorts, sort), exprs) ->
      Apply (UserDefinedOperation (ident, sorts, sort), List.map (substituteVar oldName newName) exprs)
    | And exprs -> And (List.map (substituteVar oldName newName) exprs)
    | Or exprs -> Or (List.map (substituteVar oldName newName) exprs)
    | Not expr -> substituteVar oldName newName expr
    | Hence (expr1, expr2) -> Hence (substituteVar oldName newName expr1, substituteVar oldName newName expr2)
    | QuantifierApplication (quantifier, expr) -> QuantifierApplication (quantifier, substituteVar oldName newName expr)
    
let parseMonom (x: RedTraceParser.MonomContext) =
  mult (parsePower (x.power())) (parseNumber (x.number()))

let rec parsePolynom (x: RedTraceParser.PolynomContext) =
  match x.polynom() with
  | null | [||] ->
    match x.monom() with
    | null ->
      match x.number() with
      | number ->
        parseNumber number
    | monom ->
      match x.number() with
      | null -> parseMonom monom
      | number -> add (parseMonom monom) (parseNumber number)
  | polynoms ->
    let sum =
      let sum' = Array.map parsePolynom polynoms |> Array.fold add (Number 0)
      match x.number() with
      | null -> sum' 
      | number -> add sum' (parseNumber number)         
    match x.power() with
    | null -> sum
    | power -> mult (parsePower power) sum

let rec parseFormulas (x: RedTraceParser.FormulaContext) from =
  let n = x.ChildCount
  let rec helper acc i n =
    match acc with
    | _ when i < n ->
      match x.GetChild i with
      | :? RedTraceParser.FormulaContext as e -> helper (parseFormula e :: acc) (i + 1) n
      | _ -> helper acc (i + 1) n
    | _ -> acc

  helper [] from n |> List.rev

and parseFormula (x: RedTraceParser.FormulaContext) =
  match x.GetChild 1 with
  | :? RedTraceParser.AndContext ->
    Prelude.And <| (List.ofArray <| Array.map parseFormula (x.formula()))
  | :? RedTraceParser.OrContext ->
    Prelude.Or <| (List.ofArray <| Array.map parseFormula (x.formula()))
  | :? RedTraceParser.Equal_zeroContext ->
    let v = x.polynom() |> parsePolynom
      // match x.GetChild 2 with
      // | :? RedTraceParser.PolynomContext as p -> parsePolynom p
      // | _ -> __unreachable__ ()
    Apply (eqOp, [ v; Number 0 ])
  | :? RedTraceParser.CongContext as cong ->
    let r =
      match cong.polynom() with
      | null | [||] -> __unreachable__()
      | polynoms ->
        Array.map parsePolynom polynoms
        |> Array.fold add (Number 0)
    let l = x.polynom() |> parsePolynom
      // match x.GetChild 2 with
      // | :? RedTraceParser.PolynomContext as p ->
        // parsePolynom p
      // | _ -> __unreachable__()

    Apply (eqOp, [ Apply (modOp, [ l; r ]); Number 0 ])
  | :? RedTraceParser.NcgongContext as nCong ->
    let r =
      match nCong.polynom()  with
      | null | [||] -> __unreachable__()
      | polynoms ->
        Array.map parsePolynom polynoms
        |> Array.fold add (Number 0)
    let l = x.polynom() |> parsePolynom
    
    Not (Apply (eqOp, [ Apply (modOp, [ l; r ]); Number 0 ]))
  | :? RedTraceParser.GrContext ->
    let v = x.polynom() |> parsePolynom
    Apply (grOp, [ v; Number 0 ])
  | :? RedTraceParser.LsContext ->
    let v = x.polynom() |> parsePolynom
    Apply (lsOp, [ v; Number 0 ])
  | :? RedTraceParser.NeqContext ->
    let v = x.polynom() |> parsePolynom
    Not (Apply (eqOp, [ v; Number 0 ]))
  | :? RedTraceParser.LeqContext ->
    let v = x.polynom() |> parsePolynom
    Apply (leqOp, [ v; Number 0 ])
  | :? RedTraceParser.GeqContext ->
    let v = x.polynom() |> parsePolynom
    Apply (geqOp, [ v; Number 0 ])
   | :? RedTraceParser.BallContext ->
     let [| head; body |] = x.formula()
     let head = parseFormula head
     let body = parseFormula body
     let id = x.id().GetText()
     QuantifierApplication ([ForallQuantifier [ (id, IntSort) ]], Hence (body, head))
   | _ ->
     match x.GetChild 0 with
     | :? RedTraceParser.FalseContext ->
       BoolConst false
     | _ -> __unreachable__()
    
let translateToSmt line =
  // File.WriteAllText (
  //     $"/home/andrew/adt-solver/benchs/rr.rd",
  //     line
  //   )
  let lexer = RedTraceLexer (CharStreams.fromString line)
  let tokens = CommonTokenStream lexer
  let parser = RedTraceParser tokens
  let tree: RedTraceParser.ProgContext = parser.prog ()

  match tree.GetChild 1 with
  | :? RedTraceParser.FormulaContext as formula ->
      parseFormula formula
  | _ -> __unreachable__ ()


let aaaa  =
  let lexer = RedTraceLexer (CharStreams.fromString"""(!*fof (pasf) (ball !_k128 (ball !_k122 false (and (geq (((!_k122 . 1) . 1) ((c_5 . 2) . 1) . 1) nil
) (leq (((!_k122 . 1) . 1) ((c_5 . 2) . -1) . -1) nil) (neq (((!_k122 . 1) . 1)
. -1) nil) (neq (((!_k122 . 1) . 1)) nil))) (and (geq (((!_k128 . 1) . 1) ((c_5
. 2) . 1) . 1) nil) (leq (((!_k128 . 1) . 1) ((c_5 . 2) . -1) . -1) nil) (neq ((
(!_k128 . 1) . 1) . -1) nil) (neq (((!_k128 . 1) . 1)) nil))) t)""")
  let tokens = CommonTokenStream lexer
  let parser = RedTraceParser tokens
  
  let tree: RedTraceParser.ProgContext = parser.prog ()

  match tree.GetChild 1 with
  | :? RedTraceParser.FormulaContext as formula ->
      parseFormula formula
  | _ -> __unreachable__ ()
  

let chc () =
  let balancedBracket (str: string) =
    let rec helper depth acc =
      function
      | _ when depth = 0 -> Some acc
      | h :: tl ->
        let inc =
          match h with
          | '(' -> 1
          | ')' -> -1
          | _ -> 0
  
        helper (depth + inc) (h :: acc) tl
      | _ -> None
  
    str.Substring 1
    |> Seq.toList
    |> helper 1 []
    |> function
      | Some cs ->
        List.fold (fun acc c -> $"{c}{acc}") "" cs
        |> (fun str -> $"({str}" )
        |> Some
      | None -> None
  
  let result =
    """Reduce (CSL, rev 6339), 16-Jun-2022 ...



***** FANCY is not current output handler 




Redlog Revision 6288 of 2022-04-24, 14:13:40Z
(c) 1992-2022 T. Sturm and A. Dolzmann (www.redlog.eu)
type ?; for help





debug_me


(debug_me)

Enter (1) debug_me
sth := (!*fof (pasf) (and (neq (((c_0 . 1) ((c_3 . 1) . 1) . -1) ((c_1 . 1) . 1)
) nil) (or ((ncong ((c_2 . 1) . 1)) (((c_0 . 1) ((c_3 . 1) . 1) . -1) ((c_1 . 1)
. 1)) nil) (equal (((c_2 . 1) . 1)) nil))) t)
Leave (1) debug_me = (!*fof (pasf) (and (neq (((c_0 . 1) ((c_3 . 1) . 1) . -1) (
(c_1 . 1) . 1)) nil) (or ((ncong ((c_2 . 1) . 1)) (((c_0 . 1) ((c_3 . 1) . 1) .
-1) ((c_1 . 1) . 1)) nil) (equal (((c_2 . 1) . 1)) nil))) t)

"""
  let r = Regex "sth := "
  let preambula = Seq.head <| r.Matches result
  let subStr = result.Substring (preambula.Index + preambula.Length)
  subStr
  |> balancedBracket
  |> function
    | Some s -> translateToSmt s |> fun x -> printfn $"{x}"
  
