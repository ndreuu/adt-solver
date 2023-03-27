module Tests.ProofBased.Test

open System.Text.RegularExpressions
open Approximation.SolverDeprecated.Evaluation
open NUnit.Framework.Internal
open System
open NUnit.Framework
open ProofBased
open RedlogParser.RedTrace
open SMTLIB2
open Z3Interpreter.AST
open SMTLIB2.Parser
open Prelude

[<TestFixture>]
type TestClass () =

    [<Test>]
    member this.TestMethodPassing() =
        // Solver.notZeroConsts
          // (  [ Def ("nil", [], Apply ("c_0", []))
               // Def (
                 // "cons",
                 // [ "x"; "y" ],
                 // Add (Apply ("c_1", []), Add (Mul (Apply ("c_2", []), Var "x"), Mul (Apply ("c_3", []), Var "y")))
               // ) ])
        let p = SMTLIB2.Parser.Parser false
//         let line = "(forall ((!_k10 Int) (!_k2 Int) (!_k4 Int) (!_k7 Int) (!_k8 Int))
// (=> (and (and (and (and (and (or (and (<= (+ (* !_k2 1) (* c3 1)) 0) (>= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))) (and (>= (+ (* !_k2 1) (* c3 1)) 0) (<= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0)))) (or (and (<= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 1))) (* c4 1)) 0) (>= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 -1))) (* c4 -1)) 0)) (and (>= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 1))) (* c4 1)) 0) (<= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 -1))) (* c4 -1)) 0)))) (or (and (<= (+ (* !_k8 1) (* c3 1)) 0) (>= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0))) (and (>= (+ (* !_k8 1) (* c3 1)) 0) (<= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0))))) (or (and (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0)) (and (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0)))) (or (and (<= (+ (* !_k2 1) (* c3 1)) 0) (>= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))) (and (>= (+ (* !_k2 1) (* c3 1)) 0) (<= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))))) (or (and (<= (+ (* !_k10 1) (* c4 1)) 0) (>= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0))) (and (>= (+ (* !_k10 1) (* c4 1)) 0) (<= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0))))) (and (or (= (+ (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (+ (* c2 (* c5 -1)) (* c2 12))) (* c5 1)) -12) 0) (not (= (mod (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (* c5 1)) -12) (* c2 (* c3 1))) 0)) (= (* c2 1) 0) (= (* c3 1) 0)) (or (= (+ (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (+ (* c2 (* c5 -1)) (* c2 12))) (* c5 1)) -12) 0) (not (= (mod (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (* c5 1)) -12) (* c2 (* c4 1))) 0)) (= (* c2 1) 0) (= (* c4 1) 0)) (or (not (= (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (* c5 1)) -12) 0)) (= (+ (* c5 1) -12) 0)) (or (and (<= (+ (* !_k8 1) (* c3 1)) 0) (>= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0))) (and (>= (+ (* !_k8 1) (* c3 1)) 0) (<= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0)))) (or (and (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0)) (and (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0))) (or (and (<= (+ (* !_k2 1) (* c3 1)) 0) (>= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))) (and (>= (+ (* !_k2 1) (* c3 1)) 0) (<= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0)))) (or (and (<= (+ (* !_k10 1) (* c4 1)) 0) (>= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0))) (and (>= (+ (* !_k10 1) (* c4 1)) 0) (<= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0)))))))
// "
        let line = """(assert (= (- 1) 1))"""    
        let aaa = p.ParseLine line
        match aaa with
        | [originalCommand.Assert (Apply (eq, [Apply (op, [Number 1L]);_]))] -> printfn $"{op}"
        // printfn $"{aaa.Length}"
        for a in aaa do
            printfn $"{a}"
        
        // Solver.rmAndOrRepeats
          // (Implies (And [| (And [| And [|Var "1"; Or ([| Or [|Var "6"; Var "8"|]; Var "7";|]);|]; Var "3"|]); Var "5"|], Bool false ))
        // |> printfn "%O"
        
        Assert.True(true)
        
        
    [<Test>]
    member this.parseRedLog() =
        let input = """(!*fof (pasf) (and (or (equal (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) (
(c2 . 1) ((c5 . 1) . -1) . 12) ((c5 . 1) . 1) . -12) nil) ((ncong ((c2 . 1) ((c3
. 1) . 1))) (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c5 . 1) . 1) . -12) nil)
(equal (((c2 . 1) . 1)) nil) (equal (((c3 . 1) . 1)) nil)) (or (equal (((c1 . 1)
((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12) ((c5 . 1) . 1) .
-12) nil) ((ncong ((c2 . 1) ((c4 . 1) . 1))) (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1)
. 1)) ((c5 . 1) . 1) . -12) nil) (equal (((c2 . 1) . 1)) nil) (equal (((c4 . 1)
. 1)) nil)) (or (neq (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c5 . 1) . 1) .
-12) nil) (equal (((c5 . 1) . 1) . -12) nil)) (ball !_k8 (ball !_k7 (or (ball
!_k2 (or (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) ((c4 . 1) . 1))) (((!_k2
. 1) ((c4 . 1) . 1)) ((!_k7 . 1) ((c4 . 1) . -1))) nil) (neq (((!_k2 . 1) ((c2 .
1) . 1)) ((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12
) ((c5 . 1) . 1) . -12) nil)) (or (and (leq (((!_k2 . 1) . 1) ((c3 . 1) . 1))
nil) (geq (((!_k2 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k2 . 1) . 1)) nil))
(and (geq (((!_k2 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k2 . 1) . 1) ((c3 . 1
) . -1)) nil) (neq (((!_k2 . 1) . 1)) nil)))) (equal (((c4 . 1) . 1)) nil) ((
ncong ((c4 . 1) . 1)) (((!_k7 . 1) . 1) ((c5 . 1) . -1) . 12) nil)) (or (and (
leq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2) ((c4 . 1) . 1)) ((c4 . 1) . 1)
) nil) (geq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2) ((c4 . 1) . -1)) ((c4
. 1) . -1)) nil)) (and (geq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2) ((c4 .
1) . 1)) ((c4 . 1) . 1)) nil) (leq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2)
((c4 . 1) . -1)) ((c4 . 1) . -1)) nil)))) (or (and (leq (((!_k8 . 1) . 1) ((c3 .
1) . 1)) nil) (geq (((!_k8 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k8 . 1) . 1
)) nil)) (and (geq (((!_k8 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k8 . 1) . 1)
((c3 . 1) . -1)) nil) (neq (((!_k8 . 1) . 1)) nil)))) (ball !_k4 (or (equal (((
c4 . 1) . 1)) nil) (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (
equal (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12)
((c5 . 1) . 1) . -12) nil) ((ncong ((c2 . 1) ((c4 . 1) . 1))) (((!_k4 . 1) . 1)
((c1 . 1) ((c3 . 1) . -1) ((c4 . 1) . -1)) ((c5 . 1) . -1) . 12) nil) ((ncong ((
c2 . 2) ((c3 . 1) ((c4 . 1) . 1)))) (((!_k4 . 1) ((c2 . 1) ((c4 . 1) . 1)))) nil
)) (or (and (leq (((!_k4 . 1) . 1) ((c2 . 3) ((c3 . 2) ((c4 . 1) . 1))) ((c2 . 1
) ((c4 . 1) . 1))) nil) (geq (((!_k4 . 1) . 1) ((c2 . 3) ((c3 . 2) ((c4 . 1) .
-1))) ((c2 . 1) ((c4 . 1) . -1))) nil)) (and (geq (((!_k4 . 1) . 1) ((c2 . 3) ((
c3 . 2) ((c4 . 1) . 1))) ((c2 . 1) ((c4 . 1) . 1))) nil) (leq (((!_k4 . 1) . 1)
((c2 . 3) ((c3 . 2) ((c4 . 1) . -1))) ((c2 . 1) ((c4 . 1) . -1))) nil)))) (ball
!_k2 (or (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k2 . 1) . 1)
((c5 . 1) . -1) . 12) nil) (neq (((!_k2 . 1) ((c2 . 1) . 1)) ((c1 . 1) ((c3 . 1)
. 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12) ((c5 . 1) . 1) . -12) nil))
(or (and (leq (((!_k2 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k2 . 1) . 1) ((c3
. 1) . -1)) nil) (neq (((!_k2 . 1) . 1)) nil)) (and (geq (((!_k2 . 1) . 1) ((c3
. 1) . 1)) nil) (leq (((!_k2 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k2 . 1) .
1)) nil)))) (ball !_k10 (or (equal (((c4 . 1) . 1)) nil) ((ncong ((c4 . 1) . 1))
(((!_k10 . 1) . 1) ((c5 . 1) . -1) . 12) nil) (neq (((!_k10 . 1) ((c2 . 1) . 1))
((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12) ((c5 .
1) . 1) . -12) nil)) (or (and (leq (((!_k10 . 1) . 1) ((c4 . 1) . 1)) nil) (geq
(((!_k10 . 1) . 1) ((c4 . 1) . -1)) nil) (neq (((!_k10 . 1) . 1)) nil)) (and (
geq (((!_k10 . 1) . 1) ((c4 . 1) . 1)) nil) (leq (((!_k10 . 1) . 1) ((c4 . 1) .
-1)) nil) (neq (((!_k10 . 1) . 1)) nil))))) t)"""
//         let expected = "(forall ((!_k10 Int) (!_k2 Int) (!_k4 Int) (!_k7 Int) (!_k8 Int))
// (=> (and (and (and (and (and (or (and (<= (+ (* !_k2 1) (* c3 1)) 0) (>= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))) (and (>= (+ (* !_k2 1) (* c3 1)) 0) (<= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0)))) (or (and (<= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 1))) (* c4 1)) 0) (>= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 -1))) (* c4 -1)) 0)) (and (>= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 1))) (* c4 1)) 0) (<= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 -1))) (* c4 -1)) 0)))) (or (and (<= (+ (* !_k8 1) (* c3 1)) 0) (>= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0))) (and (>= (+ (* !_k8 1) (* c3 1)) 0) (<= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0))))) (or (and (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0)) (and (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0)))) (or (and (<= (+ (* !_k2 1) (* c3 1)) 0) (>= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))) (and (>= (+ (* !_k2 1) (* c3 1)) 0) (<= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))))) (or (and (<= (+ (* !_k10 1) (* c4 1)) 0) (>= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0))) (and (>= (+ (* !_k10 1) (* c4 1)) 0) (<= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0))))) (and (or (= (+ (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (+ (* c2 (* c5 -1)) (* c2 12))) (* c5 1)) -12) 0) (not (= (mod (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (* c5 1)) -12) (* c2 (* c3 1))) 0)) (= (* c2 1) 0) (= (* c3 1) 0)) (or (= (+ (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (+ (* c2 (* c5 -1)) (* c2 12))) (* c5 1)) -12) 0) (not (= (mod (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (* c5 1)) -12) (* c2 (* c4 1))) 0)) (= (* c2 1) 0) (= (* c4 1) 0)) (or (not (= (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (* c5 1)) -12) 0)) (= (+ (* c5 1) -12) 0)) (or (and (<= (+ (* !_k8 1) (* c3 1)) 0) (>= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0))) (and (>= (+ (* !_k8 1) (* c3 1)) 0) (<= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0)))) (or (and (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0)) (and (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0))) (or (and (<= (+ (* !_k2 1) (* c3 1)) 0) (>= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))) (and (>= (+ (* !_k2 1) (* c3 1)) 0) (<= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0)))) (or (and (<= (+ (* !_k10 1) (* c4 1)) 0) (>= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0))) (and (>= (+ (* !_k10 1) (* c4 1)) 0) (<= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0)))))))
// "
        let actual = $"{Parser.translateToSmt input}"
        printfn $"\n\n\n\n{actual}\n\n\n\n"
        
        // let p = SMTLIB2.Parser.Parser false
        // let aa = p.ParseLine expected
        // let bb = p.ParseLine actual 
        
        // printfn $"{expected}"
        
        Assert.True(1 = 1)
// //     

    [<Test>]
     member this.FailEveryTime() =
       let r = Regex @"\D"
       r.Replace ("c_123", "") |>  printfn "%O"
       Solver.branch 4 (Def ( "cons", [ "x"; "y" ], Add (Expr.Apply ("c_1", []), Add (Mul (Expr.Apply ("c_2", []), Var "x"), Mul (Expr.Apply ("c_3", []), Var "y"))) ))
       |> program2originalCommand
       |> printfn "%O"
       Assert.True(true)
       
       // Solver.factorsWithConsts
        // (Ite (Eq (Add (Apply ("c_4", []), Add (Mul (Apply ("c_5", []), Var "x"), Mul (Apply ("c_6", []), Var "y"))), Int 0),
        // (Add (Apply ("c_1", []), Add (Mul (Apply ("c_2", []), Var "x"), Mul (Apply ("c_3", []), Var "y")))),
        // (Add (Apply ("c_7", []), Add (Mul (Apply ("c_8", []), Var "x"), Mul (Apply ("c_9", []), Var "y"))))))
       // |> fun vs ->
         // for v in vs do
       // Solver.terms (Add (Apply ("c_4", []), Add (Mul (Apply ("c_5", []), Var "x"), Mul (Apply ("c_6", []), Var "y"))))
       // |> printfn "%O" 
     
       // Solver.factorsWithVars
        // (Ite (Eq (Add (Apply ("c_4", []), Add (Mul (Apply ("c_5", []), Var "x"), Mul (Apply ("c_6", []), Var "y"))), Int 0),
        // (Add (Apply ("c_1", []), Add (Mul (Apply ("c_2", []), Var "x"), Mul (Apply ("c_3", []), Var "y")))),
        // (Add (Apply ("c_7", []), Add (Mul (Apply ("c_8", []), Var "x"), Mul (Apply ("c_9", []), Var "y"))))))
       // |> fun vs ->
         // for v in vs do
          // printfn "%O" v
