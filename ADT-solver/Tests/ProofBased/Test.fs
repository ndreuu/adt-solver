module Tests.ProofBased.Test

open Approximation.SolverDeprecated.Evaluation
open NUnit.Framework.Internal
open System
open NUnit.Framework
open RedlogParser.RedTrace

[<TestFixture>]
type TestClass () =

    [<Test>]
    member this.TestMethodPassing() =
        Assert.True(true)
        
        
//     [<Test>]
//     member this.parseRedLog() =
//         let input = """(!*fof (pasf) (and (or (equal (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) (
// (c2 . 1) ((c5 . 1) . -1) . 12) ((c5 . 1) . 1) . -12) nil) ((ncong ((c2 . 1) ((c3
// . 1) . 1))) (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c5 . 1) . 1) . -12) nil)
// (equal (((c2 . 1) . 1)) nil) (equal (((c3 . 1) . 1)) nil)) (or (equal (((c1 . 1)
// ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12) ((c5 . 1) . 1) .
// -12) nil) ((ncong ((c2 . 1) ((c4 . 1) . 1))) (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1)
// . 1)) ((c5 . 1) . 1) . -12) nil) (equal (((c2 . 1) . 1)) nil) (equal (((c4 . 1)
// . 1)) nil)) (or (neq (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c5 . 1) . 1) .
// -12) nil) (equal (((c5 . 1) . 1) . -12) nil)) (ball !_k8 (ball !_k7 (or (ball
// !_k2 (or (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) ((c4 . 1) . 1))) (((!_k2
// . 1) ((c4 . 1) . 1)) ((!_k7 . 1) ((c4 . 1) . -1))) nil) (neq (((!_k2 . 1) ((c2 .
// 1) . 1)) ((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12
// ) ((c5 . 1) . 1) . -12) nil)) (or (and (leq (((!_k2 . 1) . 1) ((c3 . 1) . 1))
// nil) (geq (((!_k2 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k2 . 1) . 1)) nil))
// (and (geq (((!_k2 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k2 . 1) . 1) ((c3 . 1
// ) . -1)) nil) (neq (((!_k2 . 1) . 1)) nil)))) (equal (((c4 . 1) . 1)) nil) ((
// ncong ((c4 . 1) . 1)) (((!_k7 . 1) . 1) ((c5 . 1) . -1) . 12) nil)) (or (and (
// leq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2) ((c4 . 1) . 1)) ((c4 . 1) . 1)
// ) nil) (geq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2) ((c4 . 1) . -1)) ((c4
// . 1) . -1)) nil)) (and (geq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2) ((c4 .
// 1) . 1)) ((c4 . 1) . 1)) nil) (leq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2)
// ((c4 . 1) . -1)) ((c4 . 1) . -1)) nil)))) (or (and (leq (((!_k8 . 1) . 1) ((c3 .
// 1) . 1)) nil) (geq (((!_k8 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k8 . 1) . 1
// )) nil)) (and (geq (((!_k8 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k8 . 1) . 1)
// ((c3 . 1) . -1)) nil) (neq (((!_k8 . 1) . 1)) nil)))) (ball !_k4 (or (equal (((
// c4 . 1) . 1)) nil) (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (
// equal (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12)
// ((c5 . 1) . 1) . -12) nil) ((ncong ((c2 . 1) ((c4 . 1) . 1))) (((!_k4 . 1) . 1)
// ((c1 . 1) ((c3 . 1) . -1) ((c4 . 1) . -1)) ((c5 . 1) . -1) . 12) nil) ((ncong ((
// c2 . 2) ((c3 . 1) ((c4 . 1) . 1)))) (((!_k4 . 1) ((c2 . 1) ((c4 . 1) . 1)))) nil
// )) (or (and (leq (((!_k4 . 1) . 1) ((c2 . 3) ((c3 . 2) ((c4 . 1) . 1))) ((c2 . 1
// ) ((c4 . 1) . 1))) nil) (geq (((!_k4 . 1) . 1) ((c2 . 3) ((c3 . 2) ((c4 . 1) .
// -1))) ((c2 . 1) ((c4 . 1) . -1))) nil)) (and (geq (((!_k4 . 1) . 1) ((c2 . 3) ((
// c3 . 2) ((c4 . 1) . 1))) ((c2 . 1) ((c4 . 1) . 1))) nil) (leq (((!_k4 . 1) . 1)
// ((c2 . 3) ((c3 . 2) ((c4 . 1) . -1))) ((c2 . 1) ((c4 . 1) . -1))) nil)))) (ball
// !_k2 (or (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k2 . 1) . 1)
// ((c5 . 1) . -1) . 12) nil) (neq (((!_k2 . 1) ((c2 . 1) . 1)) ((c1 . 1) ((c3 . 1)
// . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12) ((c5 . 1) . 1) . -12) nil))
// (or (and (leq (((!_k2 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k2 . 1) . 1) ((c3
// . 1) . -1)) nil) (neq (((!_k2 . 1) . 1)) nil)) (and (geq (((!_k2 . 1) . 1) ((c3
// . 1) . 1)) nil) (leq (((!_k2 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k2 . 1) .
// 1)) nil)))) (ball !_k10 (or (equal (((c4 . 1) . 1)) nil) ((ncong ((c4 . 1) . 1))
// (((!_k10 . 1) . 1) ((c5 . 1) . -1) . 12) nil) (neq (((!_k10 . 1) ((c2 . 1) . 1))
// ((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12) ((c5 .
// 1) . 1) . -12) nil)) (or (and (leq (((!_k10 . 1) . 1) ((c4 . 1) . 1)) nil) (geq
// (((!_k10 . 1) . 1) ((c4 . 1) . -1)) nil) (neq (((!_k10 . 1) . 1)) nil)) (and (
// geq (((!_k10 . 1) . 1) ((c4 . 1) . 1)) nil) (leq (((!_k10 . 1) . 1) ((c4 . 1) .
// -1)) nil) (neq (((!_k10 . 1) . 1)) nil))))) t)"""
//         let expected = "(forall ((!_k10 Int) (!_k2 Int) (!_k4 Int) (!_k7 Int) (!_k8 Int))
// (=> (and (and (and (and (and (or (and (<= (+ (* !_k2 1) (* c3 1)) 0) (>= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))) (and (>= (+ (* !_k2 1) (* c3 1)) 0) (<= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0)))) (or (and (<= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 1))) (* c4 1)) 0) (>= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 -1))) (* c4 -1)) 0)) (and (>= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 1))) (* c4 1)) 0) (<= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 -1))) (* c4 -1)) 0)))) (or (and (<= (+ (* !_k8 1) (* c3 1)) 0) (>= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0))) (and (>= (+ (* !_k8 1) (* c3 1)) 0) (<= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0))))) (or (and (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0)) (and (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0)))) (or (and (<= (+ (* !_k2 1) (* c3 1)) 0) (>= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))) (and (>= (+ (* !_k2 1) (* c3 1)) 0) (<= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))))) (or (and (<= (+ (* !_k10 1) (* c4 1)) 0) (>= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0))) (and (>= (+ (* !_k10 1) (* c4 1)) 0) (<= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0))))) (and (or (= (+ (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (+ (* c2 (* c5 -1)) (* c2 12))) (* c5 1)) -12) 0) (not (= (mod (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (* c5 1)) -12) (* c2 (* c3 1))) 0)) (= (* c2 1) 0) (= (* c3 1) 0)) (or (= (+ (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (+ (* c2 (* c5 -1)) (* c2 12))) (* c5 1)) -12) 0) (not (= (mod (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (* c5 1)) -12) (* c2 (* c4 1))) 0)) (= (* c2 1) 0) (= (* c4 1) 0)) (or (not (= (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (* c5 1)) -12) 0)) (= (+ (* c5 1) -12) 0)) (or (and (<= (+ (* !_k8 1) (* c3 1)) 0) (>= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0))) (and (>= (+ (* !_k8 1) (* c3 1)) 0) (<= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0)))) (or (and (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0)) (and (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0))) (or (and (<= (+ (* !_k2 1) (* c3 1)) 0) (>= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))) (and (>= (+ (* !_k2 1) (* c3 1)) 0) (<= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0)))) (or (and (<= (+ (* !_k10 1) (* c4 1)) 0) (>= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0))) (and (>= (+ (* !_k10 1) (* c4 1)) 0) (<= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0)))))))
// "
//         let actual = $"{Parser.translateToSmt input}"
//         
//         let p = SMTLIB2.Parser.Parser false
//         let aa = p.ParseLine expected
//         let bb = p.ParseLine actual 
//         
//         printfn $"{actual}"
//         printfn $"{expected}"
//         
//         Assert.True("actual".Equals "actual")
//     

    [<Test>]
     member this.FailEveryTime() = Assert.True(false)