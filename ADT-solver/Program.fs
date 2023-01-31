open System.IO
open Approximation
open Microsoft.FSharp.Collections
open SMTLIB2
open System.Threading.Tasks
open Approximation.Linearization
open Approximation.SolverDeprecated
open Utils


module Program =
  type Result<'TSuccess, 'TFailure> =
    | Success of 'TSuccess
    | Failure of 'TFailure
    override x.ToString() =
      match x with
      | Success x -> x.ToString()
      | Failure x -> x.ToString()


  type CommandResult =
    { ExitCode: int
      StandardOutput: string
      StandardError: string }

  type synth =
    | SynthFun of symbol * sorted_var list * sort
    | DeclareVar of ident * sort
    | Сonstraint of smtExpr
    | CheckSynth
    override x.ToString() =
      match x with
      | SynthFun (symbol, sortedVars, sort) -> $"(synth-fun {symbol} (%s{SortedVars.toString sortedVars}) {sort})"
      | DeclareVar (ident, sort) -> $"(declare-var {ident} {sort})"
      | Сonstraint smtExpr -> $"(constraint {smtExpr})"
      | CheckSynth -> "(check-synth)"

  [<EntryPoint>]
  let main args =
    // ProofBased.aaa ()
    run ""
    1
    // match args with
    // | [| path |] ->
    //   run path
    //   |> function
    //     | Ok r ->
    //        printfn "%s" r
    //        0
    //     | Error e ->
    //         printfn "%s" e
    //         1
    // | _ ->
    //     printfn "_"
    //     1
