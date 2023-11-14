module CataHornSolver.z3Process

open System
open System.IO
open System.Text.RegularExpressions
open Antlr4.Runtime.Misc
open Process.Process
open ProofBased
open ProofBased.Utils
open SMTLIB2
open Z3Interpreter

module Instances =
  type instance =
    | Teacher
    | Checker
    | Learner
    | TeacherModel
    | ADTModel

  type logic =
    | Horn
    | All
    | NIA

    override x.ToString () =
      let l =
        match x with
        | Horn -> "HORN"
        | All -> "ALL"
        | NIA -> "NIA" in

      $"(set-logic {l})\n"

  type option =
    | Proof
    | Model
    | None
    
  type learner =
    | Z3
    | CVC
    override x.ToString() =
      match x with
        | Z3 -> "z3"
        | CVC ->  "cvc"
      
  
  let setOption x =
    function
    | Proof -> $"(set-option :produce-proofs true)\n{x}\n(check-sat)\n(get-proof)"
    | Model -> $"(set-option :produce-proofs true)\n{x}\n(check-sat)\n(get-model)"
    | None -> $"{x}\n(check-sat)"

  let instances =
    [ Teacher,
      (Horn,
       Proof,
       "fp.xform.inline_eager=false fp.xform.inline_linear=false fp.xform.subsumption_checker=false fp.spacer.global=true fp.xform.inline_eager=false fp.xform.inline_linear=false fp.xform.slice=false fp.datalog.similarity_compressor=false fp.datalog.subsumption=false fp.datalog.unbound_compressor=false fp.xform.tail_simplifier_pve=false")
      Checker, (All, None, "")
      Learner, (NIA, Model, "")

      TeacherModel, (Horn, Model, $"fp.xform.inline_eager=false fp.xform.inline_linear=false fp.xform.subsumption_checker=false fp.spacer.global=true fp.xform.inline_eager=false fp.xform.inline_linear=false fp.xform.slice=false fp.datalog.similarity_compressor=false fp.datalog.subsumption=false fp.datalog.unbound_compressor=false fp.xform.tail_simplifier_pve=false pp.max_depth={UInt64.MaxValue} pp.min_alias_size={UInt64.MaxValue}")
      ADTModel, (All, Model, "") ]
      
    |> Map
// false_productive_use_of_failure_rot_inj00.smt2
//  >> Def ("c_2", [], Integer, Int 1L)
//  >> Def ("c_5", [], Integer, Int 1L)
//  >> Def ("c_0", [], Integer, Int 0L)
//  >> Def ("c_4", [], Integer, Int 0L)
//  >> Def ("c_1", [], Integer, Int 1L)
//  >> Def ("c_3", [], Integer, Int 1L)

// isaplanner_prop_16.smt2
//  >> Def ("c_2", [], Integer, Int 1L)

  let content instance cmds =
    let logic, option, _ = instances |> Map.find instance
    $"""{logic}{setOption (join "\n" cmds) option}"""

  let run tl instance cmds fTime =
    let _, _, flags = instances |> Map.find instance
    let file = Path.GetTempPath () + Path.GetRandomFileName () + ".smt2"
    
    // printfn $"CONTENTTTTTTTTTTTTTTTt\n{content instance cmds}"
    
    File.WriteAllText (file, content instance cmds)
    
    // printfn $"{instance}---"
    // printfn $"{content instance cmds}"
    let result = execute "./z3" $"-T:{tl} {flags} {file}"
    // printfn $"---{instance}"

    // let kek = execute timeout "ls" ""
    // printfn $"Z3:\n {kek}"
    
    // printfn $"rrrrrrrrrr {result}"
    
    let time =
      result.StdErr.Split('\n')
      |> Array.filter (fun (s: string) -> s.Contains("real"))
      |> join "\n"
///////////////////////////////////////////////////////////////TTTTTTTTTTTTTTTTTTTTTTTTTTTTTT    
    File.AppendAllText(fTime, $"{instance}, {time}\n")
    // printfn $"{instance}, {time}"  
///////////////////////////////////////////////////////////////TTTTTTTTTTTTTTTTTTTTTTTTTTTTTT    
    
    if result.StdOut.Contains "timeout"
       // || result.StdErr.Contains "timeout"
       then
      Option.None
     
    else Some <| if instance=TeacherModel then (Weight.rmWeightBlocks result.StdOut) else result.StdOut

    
    // if result.ExitCode = 124 then
      // Option.None
    // elif result.ExitCode = 0 then Some result.StdOut
    // else failwith $"{result.StdErr}"


module Interpreter =
  type result<'a, 'b> =
    | SAT of 'a
    | UNSAT of 'b
    | UNKNOWN

  let constDefStrs consts (s: String) =
    let constantsWithName (def: string) = List.filter (fun c -> def.Contains $"define-fun {c}" || def.Contains $"declare-datatype") consts 
    let rec helper s acc =
      // printfn $"<<< < {s}"
      let b = Regex "\("
      let brackets = b.Matches s
      match Seq.toList brackets with
      | [] ->
        acc
      | bs ->
        let def =
          List.map (fun (s: Match) -> s.Index) bs
          |> List.sort
          |> List.head
          |> s.Substring
          |> balancedBracket
          |> fun x ->
            match x with
            | Some x -> x
            | None ->
              // printfn $"{s}"
              failwith $"{s}"
          // |> Option.get
        let acc' =
          // List.addLast (def.Replace("\n", "")) acc
          if constantsWithName def |> List.length > 0 then List.addLast (def.Replace("\n", "")) acc else acc 
          // if def.Contains "define-fun c_" then List.addLast (def.Replace("\n", "")) acc else acc
        
        helper (s.Replace(def, "")) acc'
      
    helper s []
    
  let model cmds (adts: _ list) consts (content: string) =
    let p = Parser.Parser false
    // for x in content.Split '\n' do printfn $"< < < {x}" 
    
    // for adt in adts do
      // printfn $"adt: {adt}"
      // p.ParseLine adt |> ignore
    
    // printfn "HERERERER"
    //p.ParseLine $"(declare-datatypes ((list_298 0)) (((nil_331) (cons_296 (list_298x0 Int) (list_298x1 list_298)))))" |> ignore

    // for x in List.ofArray <| content.Split '\n' do printfn $"BBBLLLL {x}"
    
    // printfn $"\n---------------content--------\n{content}"
     
    if content.Contains("unknown constant !") then
      // printfn $"ERR: -ball-unbound-var-\n{content}"
      // Environment.Exit(0);
      failwith "ERR: -ball-unbound-var-"
    
    let cmds = adts @ (List.ofArray <| content.Split '\n').[ 2..(List.ofArray <| content.Split '\n').Length - 2 ] |> join "\n"
    let file = Path.GetTempPath () + Path.GetRandomFileName () + ".smt2"
    
    // printfn $"CCCCCCC\n{cmds}"
    // File.WriteAllText (file, constDefStrs cmds |> join "\n")
    // File.WriteAllText (file, constDefStrs consts cmds |> join "\n")
    File.WriteAllText (file, constDefStrs consts cmds |> join "\n")
    // File.WriteAllText (file, cmds )
    // printfn "e"
    
    
    try 
      let cmds = p.ParseFile file
      
      // printfn $"--------------------------------------------\n\n{cmds}\\n^^^^^^^"

      cmds
      |> List.choose (function
               | originalCommand.Definition (DefineFun (n, _, _, _)) as def when List.contains n consts ->
                 Some (AST.origCommand2program <| def)
               | _o ->
                 None)
    with  
      | e ->
        let d = constDefStrs consts cmds |> join "\n"
        // printfn $"ERR: -model- {e.Message}\n{d}"
        // Environment.Exit 0
        failwith $"ERR: -model- {e.Message}\n{d}"
        
  module SoftSolver =
    let softAsserts softs =
      let softNames = List.map (fun n -> $"soft_{n}") (softs)

      List.map2
        (fun n s ->
          AST.Assert (
            AST.Implies (AST.Var s, AST.Or [| AST.Eq (AST.Var n, AST.Int 0); AST.Eq (AST.Var n, AST.Int 1) |])
          ))
        softs
        softNames,
      softNames

    let content cmds softs learnerInstance =
      let cmds = List.map (AST.program2originalCommand >> toString) cmds |> join "\n"
      let softAsserts, softNames = softAsserts softs
      let softNames' = softNames |> join " "
      let softAsserts' = List.map (AST.program2originalCommand >> toString) (List.sort softAsserts) |> join "\n" 
      let softDecls =
        List.map (fun n -> AST.DeclConst (n, AST.Boolean) |> AST.program2originalCommand |> toString) softNames
        |> join "\n"
      
      let sofCore = List.map (fun n -> $"(assert (! {n}:named _{n}))") softNames |> join "\n"
      match learnerInstance with
        | Instances.learner.CVC -> 
          $"{Instances.logic.NIA}(set-option :produce-unsat-cores true)\n{cmds}\n{softDecls}\n{softAsserts'}\n{sofCore}\n(check-sat)\n(get-unsat-core)\n(get-model)"
        | Instances.learner.Z3 ->
          $"{Instances.logic.NIA}(set-option :produce-unsat-cores true)\n{cmds}\n{softDecls}\n{softAsserts'}\n(check-sat-assuming ({softNames'}))\n(get-unsat-core)\n(get-model)"
      
    let runLearner tl inputs content learnerInstance fTime =
      let _, _, flags = Instances.instances |> Map.find Instances.instance.Learner
      // printfn $"INPUT:::::::::::::::\n{flags} {content}"
      let file = Path.GetTempPath () + Path.GetRandomFileName () + ".smt2"
      File.WriteAllText (file, content)
      
      // let result = execute timeout "./z3" $"{flags} {file}"
      let result =
        match learnerInstance with
        | Instances.learner.CVC ->
          execute "./cvc5" $"--tlimit {tl * 1000} {file}"
        | Instances.learner.Z3 ->
          execute "./z3" $"-T:{tl} {flags} {file}"
      // printfn $"INP::::\n{content}"
      // printfn $"OUT::::\n{result.StdOut}"
      
      // let kek = execute timeout "ls" ""
      // printfn $"CVC:\n{kek}"

      // printfn $"----------CVC-code: {result.ExitCode}"
      
      let time =
        result.StdErr.Split('\n')
        |> Array.filter (fun (s: string) -> s.Contains("real"))
        |> join "\n"

      
///////////////////////////////////////////////////////////////TTTTTTTTTTTTTTTTTTTTTTTTTTTTTT    
      File.AppendAllText(fTime, $"{Instances.instance.Learner}, {time}\n")
      // printfn $"{Instances.instance.Learner}, {time}"
///////////////////////////////////////////////////////////////TTTTTTTTTTTTTTTTTTTTTTTTTTTTTT    
      
      if result.StdOut.Contains "timeout" || result.StdErr.Contains "timeout" then
        Option.None, content :: inputs
      else Some result.StdOut, content :: inputs
      //   
    
    let setAssuming (content: string) assumings =
      let assumings' = join " " assumings
      Regex.Replace (content, @"\(check-sat-assuming \(.*\)\)", $"(check-sat-assuming ({assumings'}))")
    
    
    let solve tl constDefs cmds softs dbgPath iteration learnerInstance fTime =
      // let content = content cmds softs

      // printfn $"contentcontentcontentcontent\n\n{content}"
      // printfn "solveSOFT"
      let rec helper i inputs assumings =
        let isActual (soft: string) =
          List.fold (fun acc (assuming: string) -> acc || (assuming.Contains soft)) false assumings
        
        let content = content cmds (List.filter isActual softs) learnerInstance
        let softContent = setAssuming content assumings
        // let softContent = content 
        // File.AppendAllText("/home/andrew/adt-solver/v/unsat-sandbox/shiz.smt2", $"{content}\n---------------------")
        
///////////////////////////////////////////////////////////////////
        // printfn $"{iteration},   smt-input-{i}.smt2" 
        // let path = Path.Join [| Option.get dbgPath; "lol"; toString iteration; $"smt-input-{i}.smt2" |]
        // if not <| Directory.Exists (Path.GetDirectoryName path) then Directory.CreateDirectory (Path.GetDirectoryName path) |> ignore
        // File.WriteAllText ($"{path}", $"{softContent}\n")
///////////////////////////////////////////////////////////////////
        
        // printfn $"----------softContent----------\n{softContent}\n------------------"
        // printfn $"{inputs}"
        let out, inputs' = runLearner tl inputs softContent learnerInstance fTime
        
        // printfn $"{out}\n{inputs'}"
        // printfn $"{out}"
        
        match out with
        | Some out -> 
          let rSat = (Regex @"\bsat\b\n").Matches out
          let rUnknown = (Regex "unknown").Matches out
          let r =
            if rSat.Count = 1 then SAT ()
            elif rUnknown.Count = 1 then
              // printfn "??UNKNOWN??"
              // Environment.Exit 0
              UNKNOWN
            else UNSAT ()
          
          // printfn $"OUT\n{out}\n{r}"
          match r with
          | UNKNOWN ->
            // printfn $".....UNKNOWN...."
            Some (UNKNOWN, assumings), inputs'
          | SAT _ ->
            // printfn $"{out}"
            let out = out.Split "\n" |> Array.removeAt 1 |> join "\n"
            Some (SAT (Some <| model cmds [] constDefs out), (List.map (fun (s: string) -> s.Remove (0, 5)) assumings)), inputs'
          | UNSAT _ ->
            // for a in assumings do printfn $"{a}"
            // printfn $"{assumings}"
            (Regex @"soft_c_\d+").Matches out
            |> Seq.toList
            |> List.tryHead
            |> function
              | Some x ->
                List.filter (fun a -> a <> x.Value) assumings
                |> helper (i + 1) inputs' 
              | None ->
                // printfn "unknown"
                // Some (UNKNOWN, assumings), inputs'
                Some (UNSAT None, assumings), inputs'
                // Environment.Exit(0)
                // failwith ""

        // | Option.None when not <| List.isEmpty softs ->
          // solve timeout constDefs cmds (List.tail softs)
        | Option.None -> None, inputs'
      helper 0 [] (softAsserts softs |> snd)


  let proof cmds content =
    let queryDecs =
      Regex(@"\(declare-fun query").Matches content
      |> Seq.map (fun (m: Match) -> m.Index |> content.Substring |> Utils.balancedBracket |> Option.get)
      |> Seq.toList

    let mp =
      Regex(@"\(mp").Match content
      |> fun mps -> mps.Index
      |> content.Substring
      |> Utils.balancedBracket
      |> function
        | Some s -> s.Replace ("mp ", "proof mp ")
        | None -> ""

    let p = Parser.Parser false

    for x in
      queryDecs
      @ List.choose
        (function
        | AST.Decl _ as x -> Some (AST.program2originalCommand x |> toString)
        | _ -> None)
        cmds do
      p.ParseLine x |> ignore

    try
      let mp' = p.ParseLine mp
  
      (List.choose
        (function
        | Command (Proof (HyperProof (a, hs, _), x, _)) ->
          Command (Proof (HyperProof (a, hs, BoolConst false), x, BoolConst false))
          |> Some
        | _ -> None)
        mp',
       content)
      with e ->
        // printfn $"ERR: -proof- {e.Message}\n{mp}" 
        // Environment.Exit 0
        failwith $"ERR: -proof- {e.Message}\n{mp}"
        
  let solve' tl adts instance cmds constDefs softs dbgPath iteration learnerInstance fTime =
    match instance with
    | Instances.instance.Learner ->
      SoftSolver.solve tl constDefs cmds softs dbgPath iteration learnerInstance fTime
    | _ ->
      let _, option, _ = Instances.instances |> Map.find instance

      let input = List.map (AST.program2originalCommand >> toString) cmds


////////////////////////////////////////////////////////////////
      // let path = Path.Join [| Option.get dbgPath; "lol"; toString iteration; $"--{instance}-{iteration}.smt2" |]
      // if not <| Directory.Exists (Path.GetDirectoryName path) then Directory.CreateDirectory (Path.GetDirectoryName path) |> ignore
      // File.WriteAllText ($"{path}", $"""{join "\n" input}""")
//////////////////////////////////////////////////////////////////
      
      let output =
        Instances.run tl instance input fTime

      // if instance = Instances.ADTModel then 
      //   printfn $"----------------------input for {instance}----------------------"
      //   join "\n" input |> printfn "%O"
      //   printfn $"----------------------------------------------------------------"
      //
      //   printfn $"output of {instance}-----------------------------------------"
      //   printfn $"{output}"
      //   printfn $"--------------------------------------------------------------|||||||||||||||||"
      // else ()

      // printfn $"output of {instance}-----------------------------------------"
      // printfn $"{output}"
      // printfn $"--------------------------------------------------------------|||||||||||||||||"
      
      match output with
      | Option.None -> Option.None, [] 
      | Some output -> 
        let rUnsat = (Regex "unsat").Matches output
        let rSat = (Regex "sat").Matches output
        
        let r =
          if rUnsat.Count = 1 then UNSAT ()
          elif rSat.Count = 1 then SAT ()
          else UNKNOWN
        
        match option, r with
        | Instances.option.None, UNSAT _ -> Some (UNSAT None, []), []
        | Instances.option.Model, UNSAT _ -> Some (UNSAT None, []), []
        | Instances.option.Proof, UNSAT _ -> Some (UNSAT (Some <| proof cmds output), []), []
        | Instances.option.None, SAT _ -> Some (SAT None, []), []
        | Instances.option.Proof, SAT _ -> Some (SAT None, []), []
        | Instances.option.Model, SAT _ ->
          
          // join "\n" input |> printfn "%O"
          // printfn $"------>>>\n{output}"
          Some (SAT (Some <| model cmds adts constDefs output), []), []
        | _ -> Some (UNKNOWN, []), []
        
  
  let solve tl adts instance cmds constDefs softs dbgPath iteration fTimes =
    solve' tl adts instance cmds constDefs softs dbgPath iteration Instances.CVC fTimes 
  
  let solveLearner tl adts cmds constDefs softs dbgPath iteration instance fTimes =
    solve' tl adts Instances.instance.Learner cmds constDefs softs dbgPath iteration instance fTimes
    
  
type snapshot =
  { cmds: AST.Program list
    consts: AST.Program list }

type context =
  { cmds: AST.Program list
    snapshot: snapshot
    softConsts: AST.Name list
    lastConsraint: AST.Program list }

  static member Init () =
    { cmds = []
      snapshot = { cmds = []; consts = [] }
      softConsts = []
      lastConsraint = [] }

let tst () =
  let contnet =
    """sat
(
  (define-fun c_2 () Int
    0)
  (define-fun c_0 () Int
    1)
  (define-fun c_3 () Int
    2)
  (define-fun soft_c_1 () Bool
    false)
  (define-fun c_1 () Int
    6)
  (define-fun soft_c_3 () Bool
    false)
  (define-fun Z_194 () Int
    0)
  (define-fun Z_192 () Int
    0)
  (define-fun soft_c_2 () Bool
    true)
  (define-fun soft_c_0 () Bool
    true)
  (define-fun div0 ((x!0 Int) (x!1 Int)) Int
    (ite (and (= x!0 (- 2)) (= x!1 0)) 3
    (ite (and (= x!0 (- 1)) (= x!1 0)) 3
      (- 3))))
  (define-fun mod0 ((x!0 Int) (x!1 Int)) Int
    (ite (and (= x!0 (- 5)) (= x!1 0)) (- 6)
    (ite (and (= x!0 (- 2)) (= x!1 0)) (- 3)
    (ite (and (= x!0 1) (= x!1 0)) (- 3)
      3))))
)"""

  
  ()
// printfn $"{Utils.balancedBracket contnet}"

// let p = Parser.Parser false
// let xs = p.ParseFile "/home/andrew/Downloads/jjj/dbg/lol/1/a.out"
// for x in xs do printfn $"{x}"

let tstpp () =
  let p = Parser.Parser false

  for x in
    [ "(declare-fun query!0 (Int Int Int) Bool)"
      "(declare-fun Inv (Int Int Int) Bool)"
      "(declare-fun length (Int Int) Bool)" ] do
    p.ParseLine x |> ignore

  let cs =
    p.ParseLine
      """(proof mp ((_ hyper-res 0 0 0 1 0 2) (asserted (forall ((A Int) (B Int) (C Int) )(=> (and (Inv C A B) (length C B) (not (<= 0 A))) (query!0 A B C)))
 ) ((_ hyper-res 0 0 0 1 0 2 0 3) (asserted (forall ((A Int) (B Int) (C Int) (D Int) (E Int) )(=> (and (length E D) (Inv E B C) (length E C) (= A (+ (- 1) B))) (Inv E A D)))
 ) ((_ hyper-res 0 0) (asserted (length 1 0)) (length 1 0)) ((_ hyper-res 0 0 0 1) (asserted (forall ((A Int) (B Int) )(=> (length B A) (Inv B A A)))
 ) ((_ hyper-res 0 0) (asserted (length 1 0)) (length 1 0)) (Inv 1 0 0)) ((_ hyper-res 0 0) (asserted (length 1 0)) (length 1 0)) (Inv 1 (- 1) 0)) ((_ hyper-res 0 0) (asserted (length 1 0)) (length 1 0)) (query!0 (- 1) 0 1)) (asserted (=> (query!0 (- 1) 0 1) false)) false)
"""

  for x in cs do
    printfn $"... {x}"


  
let chck () =
    let p =  Parser.Parser false
    let cmds = p.ParseFile "/home/andrew/adt-solver/smr/binop-list.smt2"
    for cmd in cmds do printfn $">> {cmd}"
    
    
