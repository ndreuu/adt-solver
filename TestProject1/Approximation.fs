module Approximation

open SMTLIB2.Parser
open SMTLIB2.Prelude
open Operation
open SMTLIB2.Operations

module Linearization =
  let linearization file =
    let p = Parser()
    let commands = p.ParseFile file

    //Should be in Operations
    let plus =
      makeElementaryOperationFromSorts "+" [ IntSort; IntSort ] IntSort

    let mul =
      makeElementaryOperationFromSorts "*" [ IntSort; IntSort ] IntSort

    let constants pdng (xs: _ list) =
      let _, cnsts =
        List.fold
          (fun (i, acc) _ ->
            (i - 1,
             (sprintf "c_%s" <| (i + pdng + 1).ToString())
             :: acc))
          (xs.Length - 1, [])
          xs

      cnsts

    let terms pdng args =
      List.map2 (fun c (x, _) -> Apply(mul, [ Ident(c, IntSort); Ident(x, IntSort) ])) (constants pdng args) args

    let sum pdng =
      function
      | [] -> Ident(sprintf "c_%s" <| pdng.ToString(), IntSort)
      | t :: ts ->
        Apply(
          plus,
          [ Ident(sprintf "c_%s" <| pdng.ToString(), IntSort)
            List.fold (fun acc x -> Apply(plus, [ x; acc ])) t ts ]
        )


    let a =
      fun cs pdng ->
        cs
        |> List.fold
             (fun (pd, acc) (name, _, (args : operation list)) ->
               (args.Length + pd + 1,
                Definition(
                  DefineFun(
                    name.ToString(),
                    List.map (fun arg -> (arg.ToString(), IntSort)) args,
                    IntSort,
                    sum pd
                    <| List.rev (terms pd (List.map (fun x -> (opName x, ())) args))
                  )
                )
                :: acc))
             (pdng, [])

    let padding, dataTypes =
      let pdng, defs =
        List.fold
          (fun (pdng, acc) x ->
            match x with
            | Command (DeclareDatatype (_, cs)) ->
              let pdng', def = a cs pdng
                // cs
                // |> List.fold
                //      (fun (pd, acc) (name, _, args) ->
                //        (args.Length + pd + 1,
                //         Definition(
                //           DefineFun(
                //             name.ToString(),
                //             List.map (fun arg -> (arg.ToString(), IntSort)) args,
                //             IntSort,
                //             sum pd
                //             <| List.rev (terms pd (List.map (fun x -> (opName x, ())) args))
                //           )
                //         )
                //         :: acc))
                //      (pdng, [])

              (pdng', def @ acc)
            | Command (DeclareDatatypes [ _, cs ]) ->
              let pdng', def = a cs pdng
              // printfn $"{x}"
              // printfn $"{pdng'}"
              // printfn $"{def}"
              // failwith "AAAA"
              (pdng', def @ acc)              
            | Command (DeclareDatatypes _) -> failwith "???"
            | _ -> (pdng, acc))
          (0, [])
          commands

      (pdng, defs |> List.rev)

    let padding, functions =
      let padding, functions =
        List.fold
          (fun (pdng, acc as r) cmd ->
            match cmd with
            | Command (DeclareFun (name, sorts, _)) ->
              let _, args =
                sorts
                |> List.fold
                     (fun (i, acc) _ -> (i - 1, (sprintf "x_%s" <| i.ToString(), IntSort) :: acc))
                     (sorts.Length - 1, [])

              (pdng + args.Length + 1,
               Definition(DefineFun(name.ToString(), args, IntSort, sum pdng <| List.rev (terms pdng args)))
               :: acc)
            | _ -> r)
          (padding, [])
          commands

      (padding, functions |> List.rev)

    let asserts =
      let quantiInt =
        List.map (fun (name, _) -> name, IntSort) in

      let geq_op typ = Operation.makeElementaryRelationFromSorts ">=" [typ; typ]
      // equal_op
      let rec helper smt =
        match smt with
        | Apply (UserDefinedOperation _, _) as app -> Apply(geq_op IntSort, [ app; Number 0 ])
        | And smtExprs -> And(smtExprs |> List.map (fun x -> helper x))
        | Or smtExprs -> Or(smtExprs |> List.map (fun x -> helper x))
        | Not smtExpr -> Not(helper smtExpr)
        | Hence (smtExpr1, smtExpr2) -> Hence(helper smtExpr1, helper smtExpr2)
        | QuantifierApplication (quantifier, smtExpr) ->
          QuantifierApplication (
            quantifier
            |> List.map (function
              | ForallQuantifier vars -> ForallQuantifier(quantiInt vars)
              | ExistsQuantifier vars -> ExistsQuantifier(quantiInt vars)
              | StableForallQuantifier vars -> StableForallQuantifier(quantiInt vars)),
            helper smtExpr
          )
        | _ -> smt

      commands
      |> List.fold
           (fun acc x ->
             match x with
             | Assert expr -> Assert(helper expr) :: acc
             | _ -> acc)
           []
      |> List.rev

    ////// WRONG FOR EXIST QUANTIFIER
    let asserts' =
      fun f ->
        asserts
        |> List.map (fun asrt ->
          match asrt with
          | Assert (QuantifierApplication (quantifiers, smtExpr)) ->
            (quantifiers
             |> List.fold
                  (fun acc x ->
                    match x with
                    | ForallQuantifier vars
                    | ExistsQuantifier vars
                    | StableForallQuantifier vars ->
                      acc
                      @ (vars
                         |> List.map (fun x -> Command(DeclareConst x))))
                  [],
             Assert(f smtExpr))
          | Assert expr -> ([], Assert(f expr))
          | _ -> ([], asrt))

    let skAsserts = asserts' (fun x -> Not x)

    let notSkAsserts = asserts' (fun x -> x)

    let defConstants =
      (padding - 1)
      |> List.unfold (fun i -> if i >= 0 then Some(i, i - 1) else None)
      |> List.map (fun i -> Definition(DefineFun(sprintf "c_%s" <| i.ToString(), [], IntSort, Number 0)))
      |> List.rev

    let decConstants =
      (padding - 1)
      |> List.unfold (fun i -> if i >= 0 then Some(i, i - 1) else None)
      |> List.map (fun i -> Command(DeclareConst(sprintf "c_%s" <| i.ToString(), IntSort)))
      |> List.rev


    // dataTypes
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())
    //
    // functions
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())
    //
    // asserts
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())
    //
    // defConstants
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())
    //
    // decConstants
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())
    //
    // skAsserts
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())

    (defConstants, decConstants, dataTypes, functions, asserts, skAsserts, notSkAsserts)


module SolverDeprecated =
  open System.Collections.Generic
  open Microsoft.Z3
  open SMTLIB2.Prelude

  let ctx =
    new Context([| ("model", "true") |] |> dict |> Dictionary)

  let False: BoolExpr = ctx.MkFalse()

  let True: BoolExpr = ctx.MkTrue()

  let Eq: Expr -> Expr -> BoolExpr =
    fun l r -> ctx.MkEq(l, r)

  let Add: ArithExpr -> ArithExpr -> ArithExpr =
    fun l r -> ctx.MkAdd(l, r)

  let Mul: ArithExpr -> ArithExpr -> ArithExpr =
    fun l r -> ctx.MkMul(l, r)

  let And: BoolExpr [] -> BoolExpr =
    fun bools -> ctx.MkAnd(bools)

  let Not: BoolExpr -> BoolExpr =
    fun bool -> ctx.MkNot(bool)

  let Int: int64 -> IntNum =
    fun v -> ctx.MkInt(v)

  let Implies: BoolExpr -> BoolExpr -> BoolExpr =
    fun l r -> ctx.MkImplies(l, r)

  let c: _ array =
    [| Int 0
       Int 0
       Int 0
       Int 0
       Int 0
       Int 0
       Int 0 |]

  let nil = fun _ -> c[0]

  let cons =
    fun car_0 cdr_0 -> Add c[1] (Add (Mul c[2] car_0) (Mul c[3] cdr_0))

  let len =
    fun x0 x1 -> Add (c[4]) (Add (Mul (c[5]) (x0)) (Mul (c[6]) (x1)))

  let solver = ctx.MkSolver("QF_LIA")


  let xs_1 = ctx.MkIntConst("xs_1")
  let x_1 = ctx.MkIntConst("x_1")
  let ys_0 = ctx.MkIntConst("ys_0")
  let y_0 = ctx.MkIntConst("y_0")
  let z_0 = ctx.MkIntConst("z_0")



  solver.Push()

  let plus =
    makeElementaryOperationFromSorts "+" [ IntSort; IntSort ] IntSort

  let mul =
    makeElementaryOperationFromSorts "*" [ IntSort; IntSort ] IntSort

  let tst =
    DefineFun(
      "len",
      [ ("x_0", IntSort); ("x_1", IntSort) ],
      IntSort,
      Apply(
        plus,
        [ Ident("c_4", IntSort)
          Apply(
            plus,
            [ Apply(
                mul,
                [ Ident("c_5", IntSort)
                  Ident("x_0", IntSort) ]
              )
              Apply(
                mul,
                [ Ident("c_6", IntSort)
                  Ident("x_1", IntSort) ]
              ) ]
          ) ]
      )
    )

  printfn "\n\n%s\n\n" <| tst.ToString()


  type Result<'TSuccess, 'TFailure> =
    | Success of 'TSuccess
    | Failure of 'TFailure
    override x.ToString() =
      match x with
      | Success x -> x.ToString()
      | Failure x -> x.ToString()


  let call =
    fun name (args: _ list) (funs: Map<string, smtExpr>) ->
      let rec helper expr =
        function
        | arg :: args as argums ->
          match expr with
          | Apply (ElementaryOperation ("+", _, _), [ Ident (c, _); y ]) ->
            match helper y argums with
            | Some (r, _) -> Some(Add (ctx.MkIntConst(c)) (r), args)
            | _ -> None
          | Apply (ElementaryOperation ("+", _, _), [ x; y ]) ->
            match helper x argums with
            | Some (r, args') ->
              match helper y args' with
              | Some (r', args'') -> Some(Add r r', args'')
              | _ -> None
            | _ -> None
          | Apply (ElementaryOperation ("*", _, _), [ Ident (c, _); Ident (n, _) ]) ->
            Some(Mul (ctx.MkIntConst(c)) arg, args)
          | _ -> None
        | _ -> None

      funs
      |> Map.find name
      |> fun x ->
           match helper x args with
           | Some (r, _) -> Some r
           | _ -> None

  let map = Map.empty<string, smtExpr>

  let bb =
    match tst with
    | DefineFun (_, _, _, smtExpr) -> smtExpr

  let newMap = map |> Map.add "len" bb
  printfn "%s\n" <| newMap.ToString()

  let aaaa =
    call "len" [ Int 1; Int 2 ] newMap
    |> function
      | Some r -> Success r
      | _ -> Failure ""

  printfn "%s" <| aaaa.ToString()

  solver.Add(
    Implies
      (And [| (Eq (len xs_1 x_1) (Int 0))
              (Eq (len (cons y_0 xs_1) z_0) (Int 0))
              (Eq x_1 z_0) |])
      False
  )


  solver.Pop()


  solver.Add(
    Not(
      Implies
        (And [| (Eq (len xs_1 x_1) (Int 0))
                (Eq (len (cons y_0 xs_1) z_0) (Int 0))
                (Eq x_1 z_0) |])
        False
    )
  )




  // ctx.Dispose()

  //solver.Set("completion", true)
  //solver.Set("candidate_models", true)
  let a () =
    // printfn "%s\n" <| solver.Help
    // printfn "%O\n" <| solver.ParameterDescriptions.

    match solver.Check() with
    | Status.SATISFIABLE ->
      // printf "vvvvvvvvvvvvvvvvvvvv\n"
      // printfn "%s\n" <| solver.Model.ToString()

      printfn "xs_1>>>>>%s\n"
      <| solver.Model.Eval(xs_1, true).ToString()

      printfn "x_1>>>>>%s\n"
      <| solver.Model.Eval(x_1, true).ToString()

      printfn "ys_0>>>>>%s\n"
      <| solver.Model.Eval(ys_0, true).ToString()

      printfn "y_0>>>>>%s\n"
      <| solver.Model.Eval(y_0, true).ToString()

      printfn "z_0>>>>>%s\n"
      <| solver.Model.Eval(z_0, true).ToString()


      printfn "z_1>>>>>%s\n"
      <| solver.Model.Eval(z_0, true).ToString()

      printfn "z_2>>>>>%s\n"
      <| solver.Model.Eval(z_0, true).ToString()



      printf "S"
    | Status.UNSATISFIABLE -> printf "U"
    | _ -> printf "?"


module Solver =
  ()
