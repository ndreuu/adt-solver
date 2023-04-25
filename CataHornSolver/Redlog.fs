module Redlog

open System.IO
open System.Text.RegularExpressions
open RedlogParser.RedTrace.Parser
open SMTLIB2
open Z3Interpreter.AST
open Process.Process
open ProofBased.Utils


let rec expr2redlogExpr =
  function
    | Bool true -> "true" 
    | Bool false -> "false" 
    | Int v -> v.ToString()
    | Add (expr1, expr2) -> $"{expr2redlogExpr expr1} + {expr2redlogExpr expr2}"
    | Subtract (expr1, expr2) -> $"{expr2redlogExpr expr1} - {expr2redlogExpr expr2}"
    | Neg expr -> $"(- {expr2redlogExpr expr})"
    | Mul (expr1, expr2) -> $"{expr2redlogExpr expr1} * {expr2redlogExpr expr2}"
    | Eq (expr1, expr2) -> $"({expr2redlogExpr expr1} = {expr2redlogExpr expr2})"
    | Gt (expr1, expr2) -> $"({expr2redlogExpr expr1} > {expr2redlogExpr expr2})"
    | Lt (expr1, expr2) -> $"({expr2redlogExpr expr1} < {expr2redlogExpr expr2})"
    | Le (expr1, expr2) -> $"({expr2redlogExpr expr1} <= {expr2redlogExpr expr2})"
    | Ge (expr1, expr2) -> $"({expr2redlogExpr expr1} >= {expr2redlogExpr expr2})"
    | And exprs ->
      let s = Array.map expr2redlogExpr exprs[1..] |> Array.fold (fun acc e -> $"{acc} and {e}") (expr2redlogExpr exprs[0])
      $"({s})"
    | Or exprs ->
      let s = Array.map expr2redlogExpr exprs[1..] |> Array.fold (fun acc e -> $"{acc} or {e}") (expr2redlogExpr exprs[0])
      $"({s})"
    | Not expr -> $"not {expr2redlogExpr expr}"
    | Implies (expr1, expr2) -> $"({expr2redlogExpr expr1}) impl ({expr2redlogExpr expr2})"
    | Var n -> n.ToString()
    | App (name, [||]) -> $"{name}0()"
    | App (name, [|expr|]) -> $"{name}0({expr2redlogExpr expr})"
    | App (name, exprs) ->
      let args =
        Array.map expr2redlogExpr exprs[1..]
        |> Array.fold (fun acc e -> $"{acc}, {e}") (expr2redlogExpr exprs[0])
      $"{name}0({args})"
    | Apply (name, []) -> $"{name}0()"
    | Apply (name, [expr]) -> $"{name}0({expr2redlogExpr expr})"
    | Apply (name, e::exprs) ->
      let args =
        List.map expr2redlogExpr exprs
        |> List.fold (fun acc e -> $"{acc}, {e}") (expr2redlogExpr e)
      $"{name}0({args})"
    | ForAll (names, e) ->
      let args =
        names[1..]
        |> Array.fold (fun acc e -> $"{acc}, {e}") names[0]
      $"all({{{args}}}, {expr2redlogExpr e})"
    | Ite (expr1, expr2, expr3) ->
      $"if ({expr2redlogExpr expr1}) then ({expr2redlogExpr expr2}) else ({expr2redlogExpr expr3})"
    | otherwise  -> failwith $"{otherwise}" 
let def2redlogProc =
  function
    | Def (name, args, body) ->
      let args' =
        match args with
        | [] -> ""
        | [arg] -> arg
        | args -> join ", " args
      $"procedure {name}0({args'}); {expr2redlogExpr body}$"
    | _ -> ""

let defs2redLogProcs = def2decVars >> List.fold (fun acc def -> $"{acc}{def2redlogProc def}\n") ""


let redlogQuery definitions formula =
  $"""off echo$
off FANCY$
load_package redlog$
load_package rtrace$
off rtrace;
rlset integers$

{defs2redLogProcs definitions}
phi := {expr2redlogExpr formula}$

procedure debug_me(); sth := rlwqe phi;

rtrst debug_me;
debug_me()$

quit;"""

let runRedlog definitions formula =
  let file = Path.GetTempPath() + ".red"
  
  File.WriteAllText(file, redlogQuery definitions formula)
    
  let result = execute "redcsl" $"-w- {file}"
  let r = Regex "sth := "
  let preambula = Seq.head <| r.Matches result.StdOut
  let subStr = result.StdOut.Substring (preambula.Index + preambula.Length)
  subStr
  |> balancedBracket
  |> function
    | Some s -> translateToSmt s |> Ok 
    | _ when result.StdOut.Contains "true" -> Ok (smtExpr.BoolConst true)
    | _ when result.StdOut.Contains "false" -> Ok (smtExpr.BoolConst false)
    | _ -> Error result
  