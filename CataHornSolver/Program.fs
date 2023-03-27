open System
open System.IO
open System.Text
open System.Text.RegularExpressions
open Approximation
open Microsoft.FSharp.Collections
open Microsoft.FSharp.Core
open SMTLIB2
open System.Threading.Tasks
open Approximation.Linearization
open Approximation.SolverDeprecated


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
      match run path with
      | Ok v -> printfn $"{v}"; 0
      | _ -> -1
    | _ -> -1
