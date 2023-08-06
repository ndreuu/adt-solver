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
    | And exprs -> exprs |> Seq.map expr2redlogExpr |> join " and " |> sprintf "(%s)"
    | Or exprs -> exprs |> Seq.map expr2redlogExpr |> join " or " |> sprintf "(%s)"
    | Not expr -> $"not {expr2redlogExpr expr}"
    | Implies (expr1, expr2) -> $"({expr2redlogExpr expr1}) impl ({expr2redlogExpr expr2})"
    | Var n -> n.ToString()
    | App (name, exprs)
    | Apply (name, exprs) -> $"""{name}0({join ", " (Seq.map expr2redlogExpr exprs)})"""
    | ForAll (names, e) ->
      let args =
        match names with
        | [||] -> ""
        | [| arg |] -> arg
        | args -> join ", " args
      $"all({{{args}}}, {expr2redlogExpr e})"
    | Ite (expr1, expr2, expr3) ->
      $"if ({expr2redlogExpr expr1}) then ({expr2redlogExpr expr2}) else ({expr2redlogExpr expr3})"
    | otherwise  -> failwith $"{otherwise}" 
let def2redlogProc =
  function
    | Def (name, args, _, body) ->
      let args' =
        match args with
        | [] -> ""
        | [arg] -> arg
        | args -> join ", " args
      $"procedure {name}0({args'}); {expr2redlogExpr body}$"
    | _ -> ""

let defs2redLogProcs = def2decVars >> List.map (fun def -> $"{def2redlogProc def}") >> join "\n"


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




let runRedlog timeout definitions formula =
  let file = Path.GetTempPath() + ".red"
  
  File.WriteAllText(file, redlogQuery definitions formula)
  
  match execute -1 "timeout" $"{timeout}s redcsl -w- {file}" with
  // match execute -1 "redcsl" $"-w- {file}" with
  // | x when x.ExitCode = 124 -> None 
  | x when x.ExitCode <> 0 -> None 
  | result -> 
    let out = Regex.Replace (result.StdOut, @"\t|\n|\r", "")
    let result = { result with StdOut = out }
    let r = Regex "sth := "
    let preambula = Seq.head <| r.Matches result.StdOut
    let subStr = result.StdOut.Substring (preambula.Index + preambula.Length)
  
    subStr
    |> balancedBracket
    |> function
      | Some s -> translateToSmt s |> Ok |> Some
      | _ when result.StdOut.Contains "true" ->
        printfn "ERR-T-REDLOG"
        System.Environment.Exit 0
        None
        // Ok (smtExpr.BoolConst true) |> Some
      | _ when result.StdOut.Contains "false" -> Ok (smtExpr.BoolConst false) |> Some
      | _ -> Error result |> Some
  