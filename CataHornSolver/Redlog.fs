module Redlog

open System
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
  | Int v -> v.ToString ()
  | Eq (Ite (i, t, e), expr)
  | Eq (expr, Ite (i, t, e)) ->
    $"((({expr2redlogExpr i}) impl ({expr2redlogExpr t} = {expr2redlogExpr expr})) and ((not ({expr2redlogExpr i})) impl ({expr2redlogExpr e} = {expr2redlogExpr expr})))"
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
  | Not expr -> $"(not {expr2redlogExpr expr})"
  | Implies (expr1, expr2) -> $"({expr2redlogExpr expr1}) impl ({expr2redlogExpr expr2})"
  | Var n -> n.ToString ()
  | Apply ("div", [ x; y ]) -> $"""({expr2redlogExpr x} / {expr2redlogExpr y})"""  
  | App (name, exprs)
  | Apply (name, exprs) -> $"""{name}0({join ", " (Seq.map expr2redlogExpr exprs)})"""
  | ForAll (names, e) ->
    let args =
      match names with
      | [||] -> ""
      | [| arg |] -> arg
      | args -> join ", " args

    $"all({{{args}}}, {expr2redlogExpr e})"
  | otherwise -> failwith $"{otherwise}"

let def2redlogProc =
  function
  | Def (name, args, _, body) ->
    let args' =
      match args with
      | [] -> ""
      | [ arg ] -> arg
      | args -> join ", " args

    $"procedure {name}0({args'}); {expr2redlogExpr body}$"
  | _ -> ""

let defs2redLogProcs =
  def2decVars >> List.map (fun def -> $"{def2redlogProc def}") >> join "\n"


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


let rdName (s: String) =
  Seq.fold (fun acc c -> if Char.IsLetterOrDigit c || c = '_' then $"{acc}{c}" else $"{acc}s{int c}") "" s
  // (((s.Replace ("~", "eqv0")).Replace ("<", "lpar0")).Replace (">", "rpar0")).Replace("-", "hyp0").Replace("%","p0").Replace("/", "s0").Replace(".","dot0")

let rec rdNames =
  function
  | Eq (expr1, expr2) -> Eq (rdNames expr1, rdNames expr2)
  | Lt (expr1, expr2) -> Lt (rdNames expr1, rdNames expr2)
  | Gt (expr1, expr2) -> Gt (rdNames expr1, rdNames expr2)
  | Le (expr1, expr2) -> Le (rdNames expr1, rdNames expr2)
  | Ge (expr1, expr2) -> Ge (rdNames expr1, rdNames expr2)
  | Mod (expr1, expr2) -> Mod (rdNames expr1, rdNames expr2)
  | Add (expr1, expr2) -> Add (rdNames expr1, rdNames expr2)
  | Subtract (expr1, expr2) -> Subtract (rdNames expr1, rdNames expr2)
  | Mul (expr1, expr2) -> Mul (rdNames expr1, rdNames expr2)
  | Implies (expr1, expr2) -> Implies (rdNames expr1, rdNames expr2)
  | Neg expr -> Neg (rdNames expr)
  | And exprs -> And (Array.map rdNames exprs)
  | Or exprs -> Or (Array.map rdNames exprs)
  | Not expr -> Not (rdNames expr)
  | Var n -> Var (rdName n)
  | Apply ("div", exprs) -> Apply ("div", List.map rdNames exprs)
  | Apply (n, exprs) -> Apply (rdName n, List.map rdNames exprs)
  | App (n, exprs) -> App (rdName n, List.map rdNames exprs)
  | Ite (expr1, expr2, expr3) -> Ite (rdNames expr1, rdNames expr2, rdNames expr3)
  | ForAll (ns, expr) -> ForAll (Array.map rdName ns, rdNames expr) 
  | otherwise -> otherwise


let runRedlog timeout definitions formula fTime =
  let file = Path.GetTempPath () + Path.GetRandomFileName () + ".red"

  // printfn $"F\n{formula}"
  let query =
    redlogQuery
      (List.choose
          (function
          | Program.Def (n, vars, ts, b) -> Some <| Program.Def (rdName n, List.map rdName vars, ts, rdNames b)
          | _ -> None)
          definitions)
        (rdNames formula)
  
  File.WriteAllText (
    file,
    query
  )

  // let r = execute "timeout" $"{timeout}s redcsl -w- {file}"
  let r = execute "timeout" $"{timeout}s ./rdlg/reduce -w- {file}"
  let time =
    r.StdErr.Split ('\n')
    |> Array.filter (fun (s: string) -> s.Contains ("real"))
    |> join "\n"

  // printfn $"{r.StdOut}"
  /////////////////////////////////////////////////////////////TTTTTTTTTTTTTTTTTTTTTTTTTTTTTT
  File.AppendAllText (fTime, $"redlog, {time}\n")
  // printfn $"redlog, {time}"
  /////////////////////////////////////////////////////////////TTTTTTTTTTTTTTTTTTTTTTTTTTTTTT
  // printfn $"RDC: {r.ExitCode}"
  // printfn $"RDE: {r.StdErr}"

  match r with
  | x when x.ExitCode <> 0 -> None
  | result ->
    let out = Regex.Replace (result.StdOut, @"\t|\n|\r", "")
    let result = { result with StdOut = out }
    let r = Regex "sth := "

    try
      let preambula = Seq.head <| r.Matches result.StdOut
      let subStr = result.StdOut.Substring (preambula.Index + preambula.Length)
      // printfn $"RDI: {redlogQuery definitions formula}"
      // printfn $"RDO: {result.StdOut}"
      subStr
      |> balancedBracket
      |> function
        | Some s -> translateToSmt s |> Ok |> Some
        | _ when result.StdOut.Contains "true" ->
          // printfn "ERR-T-REDLOG"
          // System.Environment.Exit 0
          // None
          Ok (smtExpr.BoolConst true) |> Some
        | _ when result.StdOut.Contains "false" ->
          // printfn $"ERR: -redlog-false-"
          // Environment.Exit(0);

          failwith "ERR: -redlog-false-"

          // Ok (smtExpr.BoolConst false) |> Some

        // | _ when result.StdOut.Contains "false" -> Ok (smtExpr.BoolConst false) |> Some
        // | _ when result.StdOut.Contains "false" -> Ok (smtExpr.BoolConst true) |> Some
        | _ -> Error result |> Some
    with
    | e ->
      raise e
      // failwith $"ERR: -redlog-parser- {e.Message}\n{query}"
