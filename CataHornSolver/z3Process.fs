module CataHornSolver.z3Process

open System
open System.IO
open System.Text.RegularExpressions
open Process.Process
open ProofBased
open SMTLIB2




let runZ3 funDefs constDefs constrDefs funDecls asserts =
  let file =  Path.GetTempPath() + ".smt2"
  
  let content =
    let body = 
      (List.map toString funDefs)
      @ (List.map toString constDefs)
      @ (List.map toString constrDefs)
      @ (List.map toString funDecls)
      @ (List.map toString asserts)
      |> join "\n"
    $"""(set-logic HORN)
(set-option :produce-proofs true)
{body}
(check-sat)
(get-proof)
"""
  File.WriteAllText(file, content)
  
  let result = execute "z3" $"fp.spacer.global=true fp.xform.inline_eager=true fp.xform.inline_linear=true {file}"
  
  result.StdOut

let z3proof funDefs constDefs constrDefs funDecls asserts =
  let out = runZ3 funDefs constDefs constrDefs funDecls asserts
  
  printfn $">>> {out}"
  
  let queryDecs =
    Regex(@"\(declare-fun query").Matches out
    |> Seq.map
         (fun (m: Match) ->
            m.Index
            |> out.Substring
            |> Utils.balancedBracket
            |> Option.get)
    |> Seq.toList
    
  let p = Parser.Parser false
  
  for x in queryDecs @ List.map toString funDecls do
    p.ParseLine x |> ignore
  
  let mp = 
    Regex(@"\(mp").Match out
    |> fun mps -> mps.Index
    |> out.Substring
    |> Utils.balancedBracket
    |> function
      | Some s ->
        s.Replace ("mp", "proof mp")
        |> p.ParseLine 
      | None -> []
  
  List.choose (function Command (Proof (HyperProof (a, hs, _), x, _)) -> Command ( (Proof (HyperProof (a, hs, BoolConst false), x, BoolConst false))) |> Some | _ -> None) mp
  
  // let rQuery = Regex "\(query"
  // rQuery.Matches mp.Head
  // |> Seq.toArray
  // |> fun arr ->
  //     mp.Head.Substring arr[0].Index
  //     |> balancedBracket
  //     |> function
  //       | Some s -> str.Replace (s, "false") |> fun str -> str.Replace ("mp", "proof mp")
  //       | None -> "Wrong proof format"
  
  