module Redlog

open System.IO
open System.Text.RegularExpressions
open RedlogParser.RedTrace.Parser
open SMTLIB2.FSharpExtensions
open Z3Interpreter.AST
open Process.Process



let rec expr2redlogExpr =
  function
    | Bool true -> "true" 
    | Bool false -> "false" 
    | Int v -> v.ToString()
    | Add (expr1, expr2) -> $"{expr2redlogExpr expr1} + {expr2redlogExpr expr2}"
    | Mul (expr1, expr2) -> $"{expr2redlogExpr expr1} * {expr2redlogExpr expr2}"
    | Eq (expr1, expr2) -> $"({expr2redlogExpr expr1} = {expr2redlogExpr expr2})"
    | Gt (expr1, expr2) -> $"({expr2redlogExpr expr1} > {expr2redlogExpr expr2})"
    | Lt (expr1, expr2) -> $"({expr2redlogExpr expr1} < {expr2redlogExpr expr2})"
    | Le (expr1, expr2) -> $"({expr2redlogExpr expr1} <= {expr2redlogExpr expr2})"
    | Ge (expr1, expr2) -> $"({expr2redlogExpr expr1} >= {expr2redlogExpr expr2})"
    | And exprs -> Array.map expr2redlogExpr exprs[1..] |> Array.fold (fun acc e -> $"{acc} and {e}") (expr2redlogExpr exprs[0])
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

let def2redlogProc =
  function
    | Def (name, args, body) ->
      let args' =
        match args with
        | [] -> ""
        | [arg] -> arg
        | arg::args ->  
        args
        |> List.fold (fun n acc -> $"{acc}, {n}") arg 
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
  
  // File.AppendAllText("/home/andrew/adt-solver/many-branches-search/dbg/red-query.red",
                    // $"{redlogQuery definitions formula}\n\n\n\n\n")

    
  let result = execute "redcsl" $"-w- {file}"
  let r = Regex "sth := "
  let preambula = Seq.head <| r.Matches result.StdOut
  let subStr = result.StdOut.Substring (preambula.Index + preambula.Length)
  subStr
  |> TextUtils.balancedBracket
  |> function
    | Some s -> translateToSmt s |> Some
    | _ -> None
  



let chck () =
  let expr =     (ForAll ([|"x0"; "x1"; "x10"; "x2"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9"|],
             Implies (
                    And
                      [|
                         Not (Eq(Var "x1", Var "x0"))
                         Not (Eq(Var "x3", Apply ("nil", [])))
                         Eq(Var "x2", Apply ("nil", []))
                         Eq(Var "x3", Var "x9")
                         Eq(Var "x4", Var "x9")
                         Eq(Var "x3", Apply ("cons", [Var "x10"; Apply ("nil", [])]))
                         Eq(Var "x1", Var "x10")
                         Eq(Var "x4", Apply ("cons", [Var "x6"; Var "x7"]))
                         Eq(Var "x0", Var "x5")
                         Not (Eq(Var "x7", Apply ("nil", [])))
                         Eq(Var "x7", Apply ("cons", [Var "x8"; Apply ("nil", [])]))
                         Eq(Var "x5", Var "x8")
                         |], Bool false) ) )
  
  let defs =
    [
      Def ("nil", [], Apply ("c0", []))
      Def (
      "cons",
      [ "x"; "y" ],
      Add (Apply ("c1", []), Add (Mul (Apply ("c2", []), Var "x"), Mul (Apply ("c3", []), Var "y")))
    ) ]
    
  // let f usedOps (ident: Name) exprs =
    // if usedOps |> List.contains ident then
      // withFuns usedOps ident exprs
    // else
      // withConsts usedOps ident exprs
    
  runRedlog defs expr |>
  function Some v -> smtExpr2expr v |> printfn "%O"
