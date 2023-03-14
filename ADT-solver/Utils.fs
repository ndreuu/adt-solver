module Utils

open System
open System.IO
open Microsoft.FSharp.Collections
open Microsoft.Z3
open NUnit.Framework
open SMTLIB2

module RmNats =
  open Microsoft.FSharp.Collections
  open SMTLIB2.Parser
  open SMTLIB2.Prelude


  let string: originalCommand list -> string =
    List.fold (fun acc x -> sprintf "%s\n%O" acc x) ""

  let nat_constructors =
    List.fold
      (fun acc cmd ->
        match cmd with
        | Command (DeclareDatatype (name, constructors)) when name.Contains ("nat", StringComparison.OrdinalIgnoreCase) ->
          constructors
          |> List.map (fun (name, _, args) -> (name.ToString (), List.length args))
          |> (@) acc
        | Command (DeclareDatatypes vs) ->
          List.fold
            (fun _ (name: string, constructors) ->
              if name.Contains ("nat", StringComparison.OrdinalIgnoreCase) then
                constructors
                |> List.map (fun (name, _, args) -> (name.ToString (), List.length args))
                |> (@) acc
              else
                acc)
            acc
            vs
        | _ -> acc)
      []

  let int_sorts =
    List.unfold (fun state ->
      if state = 0 then
        None
      else
        Some (IntSort, state - 1))

  // symbol * sorted_var list * sort * smtExpr
  let constructors_to_fns =
    List.map (fun (name, cnt) ->
      match cnt with
      | 0 -> Definition (DefineFun (name, [], IntSort, Number 0))
      | 1 ->
        Definition (
          DefineFun (
            name,
            [ ("x", IntSort) ],
            IntSort,
            Apply (ElementaryOperation ("+", [ IntSort; IntSort ], IntSort), [ Ident ("x", IntSort); Number 1 ])
          )
        )
      | n -> failwith ("wrong NAT constructor " + n.ToString () + name))

  let nat_names =
    let rm_nat_data' acc cmd =
      let helper nats =
        function
        | Command (DeclareDatatype (name, _)) when name.Contains ("nat", StringComparison.OrdinalIgnoreCase) ->
          name :: nats
        | Command (DeclareDatatypes vs) ->
          List.fold
            (fun nats (name: string, _) ->
              if name.Contains ("nat", StringComparison.OrdinalIgnoreCase) then
                name :: nats
              else
                acc)
            acc
            vs
        | _ -> nats

      helper acc cmd

    List.fold rm_nat_data' []

  let filter cmds nat_names =
    List.fold
      (fun acc cmd ->
        match cmd with
        | Command (DeclareDatatype (name, _)) when nat_names |> List.contains name -> acc
        | Command (DeclareDatatypes types) ->
          (types
           |> (List.filter (function
             | name, _ when nat_names |> List.contains name -> false
             | _ -> true))
           |> fun defs ->
                match List.length defs with
                | 0 -> acc
                | _ -> Command (command.DeclareDatatypes defs) :: acc)
        | Command (DeclareFun (n, _, _)) when n.Contains "diseqNat" -> acc
        | otherwise -> otherwise :: acc)
      []
      cmds
    |> List.rev

  let find k = List.filter <| (=) k >> List.head

  let replace_nat_str (nat_names: _ list) =
    List.map (fun cmd ->
      printfn $":::{cmd}"

      List.fold
        (fun (acc: string) (name: string) ->

          if (sprintf "%O" acc).Contains (name, StringComparison.OrdinalIgnoreCase) then
            (nat_names |> find name) |> fun name' -> acc.Replace (name', "Int")
          else
            acc)
        cmd
        nat_names)


  let eliminateNat natNames sort =
    match sort with
    | ADTSort n when natNames |> List.contains n -> IntSort
    | _ -> sort

  let elimNatInOp natNames =
    function
    | ElementaryOperation (ident, sorts, sort) ->
      ElementaryOperation (ident, List.map (eliminateNat natNames) sorts, eliminateNat natNames sort)
    | UserDefinedOperation (ident, sorts, sort) ->
      UserDefinedOperation (ident, List.map (eliminateNat natNames) sorts, eliminateNat natNames sort)

  let elimNatInDataTypeDef: (string list -> datatype_def -> datatype_def) =
    fun natNames ->
      function
      | n, bodies ->
        bodies
        |> List.map (fun (op1, op2, ops) ->
          (elimNatInOp natNames op1, elimNatInOp natNames op2, List.map (elimNatInOp natNames) ops))
        |> fun bodies' -> (n, bodies')

  let elimNatInQuantifier natNames =
    function
      | ForallQuantifier vars -> ForallQuantifier (List.map (fun (n, sort) -> (n, eliminateNat natNames sort)) vars)
      | ExistsQuantifier vars -> ExistsQuantifier (List.map (fun (n, sort) -> (n, eliminateNat natNames sort)) vars)
      | StableForallQuantifier vars -> StableForallQuantifier (List.map (fun (n, sort) -> (n, eliminateNat natNames sort)) vars)


  let rec elimNatInExpr natNames =
    function
      | Number _
      | Match _
      | Ite _
      | Let _ 
      | Ident _
      | BoolConst _ as expr -> expr 
      | Not expr -> Not (elimNatInExpr natNames expr)
      | And exprs -> And (List.map (elimNatInExpr natNames) exprs) 
      | Or exprs -> Or (List.map (elimNatInExpr natNames) exprs) 
      | Hence (expr1, expr2) -> Hence (elimNatInExpr natNames expr1, elimNatInExpr natNames expr2)
      | Apply (ElementaryOperation (n, _, _), args)
      | Apply (UserDefinedOperation (n, _, _), args) when (n.Contains "diseq") ->
        Apply (UserDefinedOperation ("distinct", [IntSort; IntSort], IntSort), List.map (elimNatInExpr natNames) args)
      | QuantifierApplication (quantifiers, e) ->
        QuantifierApplication (List.map (elimNatInQuantifier natNames) quantifiers, elimNatInExpr natNames e) 
      | Apply _ as expr -> expr
      | otherwise -> failwith $"{otherwise}"
  let replace (natNames: string list) =
    function
    | Definition def ->
      match def with
      | DefineFun (n, args, sort, body)
      | DefineFunRec (n, args, sort, body) ->
        DefineFun (n, List.map (fun (n, s) -> (n, eliminateNat natNames s)) args, sort, body)
        |> Definition
      | DefineFunsRec defs ->
        DefineFunsRec (
          defs
          |> List.map (fun (n, args, sort, body) ->
            (n, List.map (fun (n, s) -> (n, eliminateNat natNames s)) args, sort, body))
        )
        |> Definition
    | Command cmd ->
      match cmd with
      | CheckSat
      | GetModel
      | Exit
      | GetInfo _
      | GetProof
      | SetInfo _
      | SetLogic _
      | SetOption _
      | DeclareSort _
      | Proof _ -> cmd |> Command
      | DeclareDatatype def -> command.DeclareDatatype (elimNatInDataTypeDef natNames def) |> Command
      | DeclareDatatypes defs ->
        command.DeclareDatatypes (List.map (fun (def: symbol * (operation * operation * operation list) list) -> elimNatInDataTypeDef natNames def) defs)
        |> Command
      | DeclareFun (n, sorts, sort) -> DeclareFun (n, List.map (eliminateNat natNames) sorts, eliminateNat natNames sort) |> Command 
      | DeclareConst (n, sort) -> DeclareConst (n, eliminateNat natNames sort) |> Command
    | Assert expr -> elimNatInExpr natNames expr |> Assert
  
 
  let replace_nat cmds =
    let nat_names = nat_names cmds
    // for v in nat_names do
    // printfn "%O" v
    nat_names
    |> filter cmds // HERE SMTHING
    |> fun xs ->

         // for x in xs do
              // printfn $"{x}"
         
         // |> List.map (sprintf "%O")
         // |> fun xs ->
              // for x in xs do
                // printfn $">>{x}"

              // xs
         let ca = List.map (replace nat_names) xs
         ca |>  List.map (sprintf "%O")
         
    |> fun xs ->
         // for x in xs do
           // printfn $"<<{x}"   
         xs
         |> function
           | x :: xs ->
             x :: (nat_constructors cmds |> constructors_to_fns |> List.map (sprintf "%O"))
             @ xs
           | otherwise -> otherwise
         |> List.fold (fun acc cmd -> sprintf "%s\n%s" acc cmd) ""

  let constructors_cnt =
    let add acc =
      function
      | Command (DeclareDatatype _) -> acc + 1
      | Command (DeclareDatatypes vs) -> acc + List.length vs
      | _ -> acc

    List.fold add 0

  let nat_constructors_cnt =
    let add acc =
      function
      | Command (DeclareDatatype (name, _)) when name.Contains ("nat", StringComparison.OrdinalIgnoreCase) -> acc + 1
      | Command (DeclareDatatypes vs) ->
        (List.length
         <| List.filter (fun (name: string, _) -> name.Contains ("nat", StringComparison.OrdinalIgnoreCase)) vs)
        + acc
      | _ -> acc

    List.fold add 0

  let only_nat cmds =
    constructors_cnt cmds = nat_constructors_cnt cmds


  type eliminated =
    { natOlny: bool
      value: string }
  
  let change (file: string) =
    let p = Parser false
    let cmds = p.ParseFile file
    
    { natOlny = only_nat cmds 
      value = replace_nat cmds }
    
  let changeFromFolder input outPut =
    let natOut = $"{outPut}/TIP.only-nat-constructors"
    try
      if Directory.Exists outPut then
        if Directory.Exists natOut then
          printfn "That path exists already."
        else
          Directory.Delete outPut
          Directory.CreateDirectory $"{outPut}/TIP.only-nat-constructors" |> ignore  
      else
        Directory.CreateDirectory outPut |> ignore
        Directory.CreateDirectory $"{outPut}/TIP.only-nat-constructors" |> ignore
    with e ->
      printfn $"The process failed: {e}"

    let files = Directory.GetFiles(input, @"*.smt2")
    let changed =
      Array.map
        (fun (file: string) -> (Path.GetFileNameWithoutExtension file, change file))
        files
    
    for n, v in changed do
      if v.natOlny then
        File.WriteAllText($"{natOut}/{n}", v.value)
      else
        File.WriteAllText($"{outPut}/{n}", v.value)
        
let chck () =
  // printfn "%O" <| "diseqNat_567".Contains "diseqNat"
  // RmNats.change "/home/andrew/Downloads/CAV2022Orig(13)/benchmarks/TIP.Original.Linear/prod_prop_25.smt2"
  RmNats.changeFromFolder
    "/home/andrew/adt-solver/many-branches-search/benchmarks-search/CAV2022Orig(13)/rm-any-diseq/TIP.Original.Linear"
    "/home/andrew/adt-solver/many-branches-search/benchmarks-search/CAV2022Orig(13)/rm-any-diseq/TIP.not-only-nat-constructors"
  ()
