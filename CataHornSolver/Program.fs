open Microsoft.FSharp.Collections
open Microsoft.FSharp.Core
open ProofBased.Solver
open SMTLIB2

module Program =
  type Result<'TSuccess, 'TFailure> =
    | Success of 'TSuccess
    | Failure of 'TFailure

    override x.ToString () =
      match x with
      | Success x -> x.ToString ()
      | Failure x -> x.ToString ()


  type CommandResult =
    { ExitCode: int
      StandardOutput: string
      StandardError: string }

  type synth =
    | SynthFun of symbol * sorted_var list * sort
    | DeclareVar of ident * sort
    | Сonstraint of smtExpr
    | CheckSynth

    override x.ToString () =
      match x with
      | SynthFun (symbol, sortedVars, sort) -> $"(synth-fun {symbol} (%s{SortedVars.toString sortedVars}) {sort})"
      | DeclareVar (ident, sort) -> $"(declare-var {ident} {sort})"
      | Сonstraint smtExpr -> $"(constraint {smtExpr})"
      | CheckSynth -> "(check-synth)"

  [<EntryPoint>]
  let main args =
    match args with
    | [| path |] ->
      run path |> printfn "%O"
      0
    | _ ->
      1
