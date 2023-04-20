[<AutoOpen>]
module Utils

open System
open System.IO
open Microsoft.FSharp.Collections
open SMTLIB2
open SMTLIB2.Parser

let inline join s (xs: string seq) = String.Join (s, xs)

module IntOps =
  let mulOp = ElementaryOperation ("*", [ IntSort; IntSort ], IntSort)
  let negOp = ElementaryOperation ("-", [ IntSort ], IntSort)
  let minusOp = ElementaryOperation ("-", [ IntSort; IntSort ], IntSort)
  let addOp = ElementaryOperation ("+", [ IntSort; IntSort ], IntSort)
  let eqOp = ElementaryOperation ("=", [ IntSort; IntSort ], BoolSort)
  let grOp = ElementaryOperation (">", [ IntSort; IntSort ], BoolSort)

  let lsOp = ElementaryOperation ("<", [ IntSort; IntSort ], BoolSort)
  let leqOp = ElementaryOperation ("<=", [ IntSort; IntSort ], BoolSort)
  let geqOp = ElementaryOperation (">=", [ IntSort; IntSort ], BoolSort)
  let modOp = ElementaryOperation ("mod", [ IntSort; IntSort ], IntSort)

module RmNats =
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


  let distrib e L =
    let rec aux pre post =
      seq {
        match post with
        | [] -> yield (L @ [ e ])
        | h :: t ->
          yield (List.rev pre @ [ e ] @ post)
          yield! aux (h :: pre) t
      }

    aux [] L

  let rec perms =
    function
    | [] -> Seq.singleton []
    | h :: t -> Seq.collect (distrib h) (perms t)


  let eqValues x =
    List.fold (fun acc v -> acc && v = x) true


  let blockedAssert1 fName bool stmt =
    let helper acc fName bool =
      function
      | Assert (QuantifierApplication ([ ForallQuantifier [ (_, bool1); (_, IntSort); (_, IntSort) ] ],
                                       Hence (Apply (UserDefinedOperation (fName1, [ bool2; IntSort; IntSort ], BoolSort),
                                                     [ Ident (_, bool3); Ident (_, IntSort); Ident (_, IntSort) ]),
                                              Apply (UserDefinedOperation (fName2, [ bool4; IntSort; IntSort ], BoolSort),
                                                     [ Ident (_, bool5)
                                                       Apply (UserDefinedOperation (_, [ IntSort ], IntSort),
                                                              [ Ident (_, IntSort) ])
                                                       Apply (UserDefinedOperation (_, [ IntSort ], IntSort),
                                                              [ Ident (_, IntSort) ]) ])))) as x when
        eqValues bool [ bool1; bool2; bool3; bool4; bool5 ]
        && eqValues fName [ fName1; fName2 ]
        ->
        x :: acc
      | _ -> acc

    helper [] fName bool stmt
    |> function
      | xs when xs.Length > 1 -> failwith "!!!"
      | [ x ] -> Some x
      | _ -> None

  let blockedAssert2 fName bool stmt =
    let helper acc fName bool =
      function
      | Assert (QuantifierApplication ([ ForallQuantifier [ (_, IntSort) ] ],
                                       Apply (UserDefinedOperation (fName1, [ bool1; IntSort; IntSort ], BoolSort),
                                              [ Apply (ElementaryOperation (_, [], bool2), [])
                                                Apply (UserDefinedOperation (_, [ IntSort ], IntSort),
                                                       [ Ident (_, IntSort) ])
                                                Apply (UserDefinedOperation (_, [], IntSort), []) ]))) as x when
        eqValues bool [ bool1; bool2 ] && eqValues fName [ fName1 ]
        ->
        x :: acc
      | _ -> acc

    helper [] fName bool stmt
    |> function
      | xs when xs.Length > 1 -> failwith "!!!"
      | [ x ] -> Some x
      | _ -> None


  let blockedAssert3 fName bool stmt =
    let helper acc fName bool =
      function
      | Assert (QuantifierApplication ([ ForallQuantifier [ (_, IntSort) ] ],
                                       Apply (UserDefinedOperation (fName1, [ bool1; IntSort; IntSort ], BoolSort),
                                              [ Apply (ElementaryOperation (_, [], bool2), [])
                                                Apply (UserDefinedOperation (_, [], IntSort), [])
                                                Apply (UserDefinedOperation (_, [ IntSort ], IntSort),
                                                       [ Ident (_, IntSort) ]) ]))) as x when
        eqValues bool [ bool1; bool2 ] && eqValues fName [ fName1 ]
        ->
        x :: acc

      | _ -> acc

    helper [] fName bool stmt
    |> function
      | xs when xs.Length > 1 -> failwith "!!!"
      | [ x ] -> Some x
      | _ -> None

  let blockedAssert4 fName bool stmt =
    let helper acc fName bool =
      function
      | Assert (Apply (UserDefinedOperation (fName1, [ bool1; IntSort; IntSort ], BoolSort),
                       [ Apply (ElementaryOperation (_, [], bool2), [])
                         Apply (UserDefinedOperation (_, [], IntSort), [])
                         Apply (UserDefinedOperation (_, [], IntSort), []) ])) as x when
        eqValues bool [ bool1; bool2 ] && eqValues fName [ fName1 ]
        ->
        x :: acc
      | _ -> acc

    helper [] fName bool stmt
    |> function
      | xs when xs.Length > 1 -> failwith "!!!"
      | [ x ] -> Some x
      | _ -> None

  let isBlockedAssert f fName bool stmt =
    f fName bool stmt
    |> function
      | Some _ -> true
      | None -> false




  let blockedAsserts fName bool smts =
    let isEqBlockAsserts =
      (smts |> List.filter (isBlockedAssert blockedAssert1 fName bool) |> List.length > 0)
      && (smts |> List.filter (isBlockedAssert blockedAssert2 fName bool) |> List.length > 0)
      && (smts |> List.filter (isBlockedAssert blockedAssert3 fName bool) |> List.length > 0)
      && (smts |> List.filter (isBlockedAssert blockedAssert4 fName bool) |> List.length > 0)


    if isEqBlockAsserts then
      List.filter
        (fun stmt ->
          (isBlockedAssert blockedAssert1 fName bool stmt
           || isBlockedAssert blockedAssert2 fName bool stmt
           || isBlockedAssert blockedAssert3 fName bool stmt
           || isBlockedAssert blockedAssert4 fName bool stmt))
        smts
    else
      []


  let rmBlockedAsserts (blockedAsserts: _ list) (stmts: originalCommand list) =
    stmts
    |> List.filter (fun x ->
      match x with
      | _ when blockedAsserts |> List.contains x -> false
      | _ -> true)

  let substitute after values =
    List.fold
      (fun acc stmt ->
        match stmt with
        | x when x = after -> values @ x :: acc
        | x -> x :: acc)
      []
    >> List.rev

  let eqDecs =
    List.filter (function
      | Command (command.DeclareFun (_, _, [ ADTSort boolName; IntSort; IntSort ], BoolSort)) when
        boolName.Contains "Bool"
        ->
        true
      | _ -> false)




  let eqFunDecl acc =
    function
    | Command (DeclareFun (n, [ ADTSort boolName; IntSort; IntSort ], BoolSort)) when boolName.Contains "Bool" ->
      (n, boolName) :: acc
    | _ -> acc

  let transformEqAsserts f falseFun trueFun =
    [ Assert (
        QuantifierApplication (
          [ ForallQuantifier [ ("x", IntSort); ("y", IntSort) ] ],
          Hence (
            Apply (
              ElementaryOperation ("=", [ IntSort; IntSort ], IntSort),
              [ Ident ("x", IntSort); Ident ("y", IntSort) ]
            ),
            Apply (f, [ trueFun; Ident ("x", IntSort); Ident ("y", IntSort) ])
          )
        )
      )
      Assert (
        QuantifierApplication (
          [ ForallQuantifier [ ("x", IntSort); ("y", IntSort) ] ],
          Hence (
            Apply (
              ElementaryOperation ("distinct", [ IntSort; IntSort ], IntSort),
              [ Ident ("x", IntSort); Ident ("y", IntSort) ]
            ),
            Apply (f, [ falseFun; Ident ("x", IntSort); Ident ("y", IntSort) ])
          )
        )
      ) ]



  let boolOps boolName =
    List.fold
      (fun acc stmt ->
        match stmt with
        | Command (DeclareDatatypes [ (boolName1,
                                       [ (ElementaryOperation (name1, [], _), _, [])
                                         (ElementaryOperation (name2, [], _), _, []) ]) ])
        | Command (DeclareDatatypes [ (boolName1,
                                       [ (ElementaryOperation (name2, [], _), _, [])
                                         (ElementaryOperation (name1, [], _), _, []) ]) ]) when
          boolName1 = boolName && name1.Contains "false" && name2.Contains "true"
          ->
          Some (name1, name2)
        | _ when Option.isSome acc -> acc
        | _ -> None)
      None

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
        | Assert (QuantifierApplication (_, Hence (_, Apply (ElementaryOperation (ident, _, _), _))))
        | Assert (QuantifierApplication (_, Hence (_, Apply (UserDefinedOperation (ident, _, _), _))))
        | Assert (QuantifierApplication (_, Apply (ElementaryOperation (ident, _, _), _)))
        | Assert (QuantifierApplication (_, Apply (UserDefinedOperation (ident, _, _), _))) when
          ident.Contains "diseqNat"
          ->
          acc
        // | Assert (QuantifierApplication (_, Apply(ElementaryOperation (ident, _, _), _))) when ident.Contains "diseqNat" -> acc


        | otherwise -> otherwise :: acc)
      []
      cmds
    |> List.rev

  let find k = List.filter <| (=) k >> List.head

  let replace_nat_str (nat_names: _ list) =
    List.map (fun cmd ->

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
    | StableForallQuantifier vars ->
      StableForallQuantifier (List.map (fun (n, sort) -> (n, eliminateNat natNames sort)) vars)


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
    | Apply (UserDefinedOperation (n, _, _), args) when (n.Contains "diseqNat") ->
      Apply (UserDefinedOperation ("distinct", [ IntSort; IntSort ], IntSort), List.map (elimNatInExpr natNames) args)
    | QuantifierApplication (quantifiers, e) ->
      QuantifierApplication (List.map (elimNatInQuantifier natNames) quantifiers, elimNatInExpr natNames e)
    | Apply _ as expr -> expr
    | otherwise -> failwith $"{otherwise}"

  // let (|Proof|_|) _ = __notImplemented__()

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
      | DeclareDatatype def -> command.DeclareDatatype (elimNatInDataTypeDef natNames def) |> Command
      | DeclareDatatypes defs ->
        command.DeclareDatatypes (List.map (fun def -> elimNatInDataTypeDef natNames def) defs)
        |> Command
      | DeclareFun (n, sorts, sort) ->
        DeclareFun (n, List.map (eliminateNat natNames) sorts, eliminateNat natNames sort)
        |> Command
      | DeclareConst (n, sort) -> DeclareConst (n, eliminateNat natNames sort) |> Command
      | _ -> cmd |> Command

    | Assert expr -> elimNatInExpr natNames expr |> Assert


  let replace_nat cmds =
    let nat_names = nat_names cmds

    nat_names
    |> filter cmds
    |> fun xs ->
        let ca = List.map (replace nat_names) xs
        ca |> List.map (sprintf "%O")
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

  let haveRecTypes cmds =
    let argsHaveSort sort =
      List.fold (fun acc arg -> acc || arg = sort) false

    let haveRec acc =
      function
      | Command (DeclareDatatype _) -> failwith "!!"
      | Command (DeclareDatatypes defs) ->
        defs
        |> List.fold
          (fun acc (adtName, defs) ->
            defs
            |> List.fold
              (fun acc (constr, _, _) ->
                match constr with
                | ElementaryOperation (_, args, _)
                | UserDefinedOperation (_, args, _) when (adtName.Contains "Nat" |> not) ->
                  acc || argsHaveSort (ADTSort adtName) args
                | _ -> acc)
              acc)
          acc
      | _ -> acc

    List.fold (fun acc cmd -> haveRec acc cmd) false cmds

  type eliminated =
    { natOlny: bool
      haveRec: bool
      value: string }

  let change (file: string) =
    let p = Parser false
    let cmds = p.ParseFile file

    let cmds' cmds =
      eqDecs cmds
      |> fun xs ->
        xs
        |> List.fold
          (fun acc decl ->
            match decl with
            | Command (DeclareFun (fName, [ ADTSort boolName; _; _ ], _)) ->
              let bool = ADTSort boolName
              let blockedAsserts = blockedAsserts fName bool acc
              let cmds' = rmBlockedAsserts blockedAsserts acc

              let falseOpName, trueOpName =
                boolOps boolName acc
                |> function
                  | Some (x, y) -> x, y
                  | _ -> failwith "!!!!"

              let falseOp = ElementaryOperation (falseOpName, [], ADTSort boolName)
              let trueOp = ElementaryOperation (trueOpName, [], ADTSort boolName)
              let f = UserDefinedOperation (fName, [], BoolSort)
              let trueFun = Apply (trueOp, [])
              let falseFun = Apply (falseOp, [])

              match blockedAsserts with
              | [] -> acc
              | _ ->
                let newAsserts = transformEqAsserts f falseFun trueFun
                substitute decl newAsserts cmds'
            | _ -> acc)
          cmds



    { natOlny = only_nat cmds
      haveRec = haveRecTypes cmds
      value =
        replace_nat cmds
        |> fun str ->
          let p = Parser false
          let tmpFile = Path.GetTempFileName ()
          File.WriteAllText (tmpFile, str)
          let cmds'' = p.ParseFile tmpFile

          cmds' cmds'' |> List.fold (fun acc x -> $"{acc}{x}\n") "" }

  let changeFromFolder input outPut =
    let natOut = $"{outPut}/TIP.only-nat-constructors"
    let noRecOut = $"{outPut}/TIP.no-rec-types"

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
        Directory.CreateDirectory noRecOut |> ignore
    with e ->
      printfn $"The process failed: {e}"

    let files = Directory.GetFiles (input, @"*.smt2")

    let changed =
      Array.map (fun (file: string) -> (Path.GetFileNameWithoutExtension file, change file)) files

    for n, v in changed do
      match v with
      | _ when (not v.haveRec) -> File.WriteAllText ($"{noRecOut}/{n}", v.value)
      | _ when v.haveRec && v.natOlny -> File.WriteAllText ($"{natOut}/{n}", v.value)
      | _ when v.haveRec && (not v.natOlny) -> File.WriteAllText ($"{outPut}/{n}", v.value)
      | _ -> __unreachable__ ()

let go pathOrig pathLia =
  RmNats.changeFromFolder pathOrig pathLia
