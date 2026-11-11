/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CASOracle.DSolve
import CASOracle.Factor
import CASOracle.Ideal
import CASOracle.Numeric
import CASOracle.Sum

/-!
# The trust boundary: wrong, broken and missing oracles are refused

`tests/oracle/run.sh` runs this file with the programs of `tests/oracle/drivers/` in place of the
real ones: a Python that answers every `sympy` task plausibly but wrongly (except three sums of
squares and one Gröbner basis, which it gets right so that their scripts and the accepted answer
can be pinned), never answers for `flint`, and prints garbage for `pari`; a Maxima whose answers
are outside the checked language, use an undeclared variable, or are too large to read; and a
Gappa that leaves a child holding its output open. `SYMLEAN_SAGE_PATH` names a program that does
not exist. Every deliberately invalid response must be refused with its reason. The last sections
check the axiom audit of the acceptance boundary, the acceptance of a right basis with a zero
element, and that the proofs the tactics and the commands suggest replay without any oracle, also
in sections whose variables could change what the printed text means.
-/

set_option linter.hashCommand false

/-! ## Wrong answers -/

/-- error: integrate: the primitive proposed by sympy, (x + 1)*exp(x), is refused -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := sympy] (x * exp x)

/-- error: factor: the factorization proposed by sympy -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := sympy] (x ^ 4 + 4)

/-- error: cas [oracle := sympy]: the cofactors proposed by sympy are refused -/
#guard_msgs (error, substring := true) in
example (x y : ℝ) (h1 : x * y = 1) (h2 : x = y) : x ^ 2 = 1 := by
  cas [oracle := sympy]

/-- error: groebner: the basis proposed by sympy is refused -/
#guard_msgs (error, substring := true) in
#cas [groebner x, y, oracle := sympy] [x ^ 2 + y ^ 2 - 5, x * y - 2]

-- The inputs themselves, with the identity as cofactors both ways: they span the ideal but are
-- not a Gröbner basis, and the check of the Gröbner property refuses them.
/--
error: groebner: the basis proposed by sympy is refused: it is not shown to be a Gröbner basis
  groebner: the basis is not a Gröbner basis for `MonomialOrder.lex`: the S-polynomial of
-/
#guard_msgs (error, substring := true, whitespace := lax) in
#cas [groebner x, y, oracle := sympy] [x ^ 2 - y, y ^ 2 - x]

-- The proposed sum of squares is `(x + y) ^ 2`, which is not `x ^ 2 + y ^ 2`.
/-- error: cas [oracle := sympy]: the sum of squares proposed by sympy is refused -/
#guard_msgs (error, substring := true) in
example (x y : ℝ) : 0 ≤ x ^ 2 + y ^ 2 := by
  cas [oracle := sympy]

-- The proposed sum is `x ^ 2` itself: the identity holds, but no term is positive.
/--
error: cas [oracle := sympy]: the sum of squares proposed by sympy is refused: no term is a
positive constant or a positive constant times strict premises
This says nothing about the inequality.
-/
#guard_msgs in
example (x : ℝ) : 0 < x ^ 2 := by
  cas [oracle := sympy]

-- Under `x ≠ 0`, `positivity` would prove `0 < x ^ 2` from the same proposed sum `x ^ 2`, and the
-- polynomial is positive there. But no term of the sum has the accepted form, a positive constant
-- or a positive constant times strict premises, so the check of the strict form refuses it
-- before `positivity` runs.
/--
error: cas [oracle := sympy]: the sum of squares proposed by sympy is refused: no term is a
positive constant or a positive constant times strict premises
This says nothing about the inequality.
-/
#guard_msgs in
example (x : ℝ) (hx : x ≠ 0) : 0 < x ^ 2 := by
  cas [oracle := sympy]

-- The multiplier `1 + y ^ 2` turns `(x * y - 1) ^ 2 + x ^ 2` into `1 + (x - y + x * y ^ 2) ^ 2`;
-- the proposed `y ^ 2` does not.
/-- error: cas [oracle := sympy]: the sum of squares proposed by sympy is refused -/
#guard_msgs (error, substring := true) in
example (x y : ℝ) : 0 < (x * y - 1) ^ 2 + x ^ 2 := by
  cas [oracle := sympy]

/-- error: solve: no solution proposed by sympy could be checked -/
#guard_msgs (error, substring := true) in
#cas [solve x, y, oracle := sympy] (x ^ 2 + y ^ 2 = 5 ∧ x * y = 2)

/-- error: nsolve: no root proposed by sympy could be certified (refused: [0.500000, 2.000000]) -/
#guard_msgs (error, substring := true) in
#cas [nsolve x in [0, 1], oracle := sympy] (cos x = x)

-- 2 is a root of x = 2, but outside the interval asked for; 0.5 is no root.
/-- error: nsolve: no root proposed by sympy could be certified (refused: [0.500000, 2.000000]) -/
#guard_msgs (error, substring := true) in
#cas [nsolve x in [0, 1], oracle := sympy] (x = 2)

/-- error: nintegrate: the value 0.750000 proposed by sympy could not be certified -/
#guard_msgs (error, substring := true) in
#cas [nintegrate x in [0, 1], oracle := sympy] (exp (-x ^ 2))

/-- error: eigenvalues: no eigenvalue proposed by sympy could be certified -/
#guard_msgs (error, substring := true) in
#cas [eigenvalues, oracle := sympy] !![2, 1; 1, 3]

/-- error: sum: the closed form proposed by sympy -/
#guard_msgs (error, substring := true) in
#cas [sum k 1 n, oracle := sympy] (k)

/-- error: dsolve: the family proposed by sympy -/
#guard_msgs (error, substring := true) in
#cas [dsolve y x, oracle := sympy] (y' = y)

-- The zero function solves `y' = 1 / y` only through `1 / 0 = 0`: its condition `0 ≠ 0` fails.
/-- error: dsolve: the conditions of the family proposed by sympy fail at every test point -/
#guard_msgs (error, substring := true) in
#cas [dsolve y x, oracle := sympy] (y' = 1 / y)

/-! ## Broken and missing oracles -/

/-- error: oracle flint did not answer within 3000 ms -/
#guard_msgs (error, substring := true) in
set_option cas.oracle.timeout 3000 in
#cas [factor, oracle := flint] (x ^ 2 - 1)

/-- Whether the processes `pids` have all exited (polled for up to three seconds, so that the
init process can reap orphans). -/
def allGone (pids : List String) : IO Bool := do
  for _ in [0:300] do
    let mut alive := false
    for pid in pids do
      let out ← IO.Process.output { cmd := "ps", args := #["-o", "stat=", "-p", pid] }
      let state := out.stdout.trimAscii.toString
      unless state.isEmpty || state.startsWith "Z" do alive := true
    unless alive do return true
    IO.sleep 10
  return false

-- The program of that timeout ignored `SIGTERM` and left a child that ignores it too: both were
-- ended with the process group (`SIGKILL` after `SIGTERM`).
/-- info: program and child ended: true -/
#guard_msgs in
#eval show IO Unit from do
  let some file ← IO.getEnv "SYMLEAN_TEST_PIDFILE" | IO.println "no pid file"
  let pids := ((← IO.FS.readFile file).trimAscii.toString.splitOn " ")
  IO.println s!"program and child ended: {← allGone pids}"

-- The cleanup DSLean's runner uses on every exit path, `terminateGroup`, on a group whose leader
-- ignores `SIGTERM` and has forked a child that ignores it too (an ignored signal is inherited):
-- the `SIGKILL` that `killGroup` sends through the system `kill` ends both.
/-- info: SIGTERM-resistant group ended: true -/
#guard_msgs in
#eval show IO Unit from do
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "trap '' TERM; sleep 60 & sleep 60"], stdin := .null,
      stdout := .null, stderr := .null, setsid := true }
  IO.sleep 300
  DSLean.terminateGroup child
  let mut gone := false
  for _ in [0:300] do
    -- `pgrep` exits with 1 exactly when no process matches; other codes are errors.
    let out ← IO.Process.output { cmd := "pgrep", args := #["-g", toString child.pid] }
    if out.exitCode == 1 && out.stdout.trimAscii.isEmpty then
      gone := true
      break
    IO.sleep 10
  IO.println s!"SIGTERM-resistant group ended: {gone}"

/-- error: oracle pari failed -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := pari] (x ^ 2 - 1)

/-- error: the oracle's answer is refused: it is outside the checked language -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (exp (-x ^ 2))

/-- error: the oracle's answer is refused: it uses z, which is not a variable of the request -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := maxima] (x ^ 2 - 1)

/-- error: integrate: maxima left the integral unevaluated -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (exp (x ^ x))

-- Answers that are expensive to read are refused before DSLean parses them (a long number, a
-- deep nesting, a long text) or before they are reflected (a tower of `tanh`, which the reifier
-- lowers by repeating its argument four times); an over-long chain of operations is refused by
-- DSLean's own depth bound.
/-- error: the oracle's answer is refused: a number in it is too long -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (x)

/-- error: the oracle's answer is refused: it nests deeper than 512 -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (x ^ 2)

/-- error: the oracle's answer is refused: it has over 20000 characters -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (cos x)

/-- error: the oracle's answer is refused: its reflection would have over 20000 nodes -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (sin x)

/-- error: the oracle's answer is refused: it is nested or chained more than 1000 deep -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (x ^ 3)

-- A child of Gappa holds both output streams open; the group is ended with Gappa, the answer
-- arrives at once, and it is wrong.
/-- error: enclose: the enclosure [0.000000, 0.100000] proposed by gappa could not be certified -/
#guard_msgs (error, substring := true) in
set_option cas.oracle.timeout 20000 in
#cas [enclose x in [0, 1], oracle := gappa] (x)

/-- error: oracle maxima has no checkable answer: maxima has no solve -/
#guard_msgs (error, substring := true) in
#cas [solve x, oracle := maxima] (x = 1)

-- Sage has no task `sos`. It is refused before it is asked, so the refusal does not end with
-- "This says nothing about the inequality.".
/-- error: cas [oracle := sage]: oracle sage has no checkable answer: sage has no sos -/
#guard_msgs in
example (x : ℝ) : 0 ≤ x ^ 2 := by
  cas [oracle := sage]

/-- error: oracle sage is unavailable -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := sage] (x ^ 2 - 1)

/-- error: unknown oracle mathematica -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := mathematica] (x ^ 2 - 1)

/-! ## Records

An answer counts only in the records its task expects, each as often as the task allows, from a
program that exited normally. -/

/-- error: oracle sympy failed: the answer has several records antiderivative -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := sympy] (cos x)

/-- error: oracle sympy failed: the answer has an unexpected record primitive -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := sympy] (sin x)

/-- error: oracle sympy failed: the oracle exited with code 3 after answering -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := sympy] (x ^ 3)

/-- error: oracle sympy failed: the answer has no record constant -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := sympy] (x ^ 2 - 4)

/-- error: the oracle's multiplicity 1234567890123 is not a small natural number -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := sympy] (x ^ 2 - 9)

/-- error: solve: sympy reports no real solution (which proves nothing) -/
#guard_msgs (error, substring := true) in
#cas [solve x, oracle := sympy] (x ^ 2 + 1 = 0)

/--
error: cas [oracle := sympy]: sympy found no sum of squares
This says nothing about the inequality.
-/
#guard_msgs in
example (x y z : ℝ) : 0 < x ^ 2 + y ^ 2 + z ^ 2 + 1 := by
  cas [oracle := sympy]

/-! ## Bounds on what is computed from an answer -/

-- A short answer whose constant has 2 ^ (10 ^ 12) as numerator is refused before any arithmetic.
/-- error: the oracle's answer is refused: its numbers could need over 100000 bits -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := maxima] (x ^ 2 - 4)

-- A real power whose exponent is a product of literals is a power with that exponent.
/-- error: the oracle's answer is refused: it has an exponent over 1000 -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := maxima] (x ^ 2 - 25)

-- Four constants of 30001 bits, each estimated at 90000: together they are over the budget of
-- the whole answer.
/-- error: the oracle's answer is refused: its numbers could need over 100000 bits -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := maxima] (x ^ 2 - 36)

/-- error: the oracle's answer has 201 factors, over 200 -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := maxima] (x ^ 2 - 16)

/-- error: the oracle's power 12345678901234 is not a small natural number -/
#guard_msgs (error, substring := true) in
example (x : ℝ) (h : x = 1) : x ^ 2 = 1 := by
  cas [oracle := sympy]

/-- error: the oracle's constant count 99999999999999 is not a small natural number -/
#guard_msgs (error, substring := true) in
#cas [dsolve y x, oracle := sympy] (y' = 2 * y)

/-- error: oracle sympy failed: the answer's basis and cofactor rows do not match -/
#guard_msgs (error, substring := true) in
#cas [groebner x, y, oracle := sympy] [x ^ 2 - y, x * y - 1]

/-- error: nsolve: sympy reports no real root (which proves nothing) -/
#guard_msgs (error, substring := true) in
#cas [nsolve x, oracle := sympy] (x ^ 2 + 1 = 0)

/-- error: eigenvalues: sympy reports no real eigenvalue (which proves nothing) -/
#guard_msgs (error, substring := true) in
#cas [eigenvalues, oracle := sympy] !![0, 1; -1, 0]

/-- error: oracle gappa failed: the oracle exited with code 2 after answering -/
#guard_msgs (error, substring := true) in
set_option cas.oracle.timeout 20000 in
#cas [enclose x in [0, 1], oracle := gappa] (x * x)

-- The derivative that the check of a primitive takes is admitted too.
/-- error: the oracle's answer is refused: its derivative: its expansion could form products of over 10000 terms -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := sympy] (x ^ 4)

/-- error: the oracle's answer is refused: its derivative: its numbers could need over 100000 bits -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := sympy] (x ^ 5)

-- Each factor is admitted, and so is the factorization with its multiplicities.
/-- error: the oracle's factorization is refused: its expansion could form products of over 10000 terms -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := sympy] (x ^ 2 - 49)

-- Powers written as products for Gappa are bounded before they are built.
/-- error: the request cannot be written for gappa: with its powers written as products it has over 20000 nodes -/
#guard_msgs (error, substring := true) in
#cas [enclose x in [0, 1], oracle := gappa] (((x ^ 64) ^ 64) ^ 64)

-- The reader of answers, directly: what it refuses and what it reads. Six nested `tanh` reflect
-- to 21841 nodes and are refused before reflection; five (5461 nodes) are refused by the bound on
-- the arguments of exponentials, since `tanh` is read through `exp`.
open Lean Elab Term in
/-- info: __import__('os').system('true'): it is outside the checked language (DSLean: Syntax error in input: unexpected trailing characters ('os').system('true'))
0.5*v0: it has a decimal number, outside the checked language
v0 + I: it uses I, which is not a variable of the request
v0;v0: it is outside the checked language (DSLean: Syntax error in input: unexpected trailing characters ;v0)
v0**2*sin(v0): read as x^2*sin(x)
2**3**2: read as 2^9
(v0**1000)**1000: its numbers could need over 100000 bits
v0**(1000+1): it has an exponent over 1000
((1**0+1**0)**1000)**100: its numbers could need over 100000 bits
tanh ×5: it has an exponential of an argument over 65536 in size
tanh ×6: its reflection would have over 20000 nodes
zero power of a tower: its numbers could need over 100000 bits
power with that exponent: its numbers could need over 100000 bits
2**log(exp(10^12)): it has an exponential of an argument over 65536 in size
v0**log(exp(1001)): it has a real power with an exponent over 1024 in size
(sin + sin + sin)**1000: its expansion could form products of over 10000 terms
(1+v0)**500*(1+v0)**500: its expansion could form products of over 10000 terms
2^96*(16 v0)**1000: its numbers could need over 100000 bits
log(exp(10^12)): it has an exponential of an argument over 65536 in size
tanh(v0): read as (exp(x) - exp(-x))/2/((exp(x) + exp(-x))/2)
exp(-v0**2): read as exp(-x^2)
exp(v0**3): read as exp(x^3)
1/(1 + exp(v0)): read as 1/(1 + exp(x))
(1 + v0)**100: read
(1 + v0)**1000: its expansion could take over 2000000 steps
(v0 - 1)*…*(v0 - 30): read
v0*(sin(1)+sin(2)+sin(3))**1000: its expansion could form products of over 10000 terms
log(exp(16384)**1000): its numbers could need over 100000 bits
log(exp(1/exp(-16))): it has an exponential of an argument over 65536 in size -/
#guard_msgs in
#eval show TermElabM Unit from do
  let tower (k : Nat) := String.join (List.replicate k "tanh(") ++ "v0" ++
    String.join (List.replicate k ")")
  for (label, text) in [("__import__('os').system('true')", "__import__('os').system('true')"),
      ("0.5*v0", "0.5*v0"), ("v0 + I", "v0 + I"), ("v0;v0", "v0;v0"),
      ("v0**2*sin(v0)", "v0**2*sin(v0)"), ("2**3**2", "2**3**2"),
      ("(v0**1000)**1000", "(v0**1000)**1000"), ("v0**(1000+1)", "v0**(1000+1)"),
      ("((1**0+1**0)**1000)**100", "((1**0+1**0)**1000)**100"), ("tanh ×5", tower 5),
      ("tanh ×6", tower 6),
      ("zero power of a tower", "((((2**1000)**1000)**1000)**1000)**0"),
      ("power with that exponent", "2**(((((2**1000)**1000)**1000)**1000)**0)"),
      ("2**log(exp(10^12))", "2**log(exp(1000*1000*1000*1000))"),
      ("v0**log(exp(1001))", "v0**log(exp(1001))"),
      ("(sin + sin + sin)**1000", "(sin(v0) + sin(2*v0) + sin(3*v0))**1000"),
      ("(1+v0)**500*(1+v0)**500", "(1 + v0)**500*(1 + v0)**500"),
      ("2^96*(16 v0)**1000", "(79228162514264337593543950336*(v0 + v0 + v0 + v0 + v0 + v0 + \
        v0 + v0 + v0 + v0 + v0 + v0 + v0 + v0 + v0 + v0))**1000"),
      ("log(exp(10^12))", "log(exp(1000000000000))"),
      ("tanh(v0)", "tanh(v0)"), ("exp(-v0**2)", "exp(-v0**2)"), ("exp(v0**3)", "exp(v0**3)"),
      ("1/(1 + exp(v0))", "1/(1 + exp(v0))"), ("(1 + v0)**100", "(1 + v0)**100"),
      ("(1 + v0)**1000", "(1 + v0)**1000"),
      ("(v0 - 1)*…*(v0 - 30)", "*".intercalate ((List.range 30).map (s!"(v0 - {· + 1})"))),
      ("v0*(sin(1)+sin(2)+sin(3))**1000", "v0*(sin(1) + sin(2) + sin(3))**1000"),
      ("log(exp(16384)**1000)", "log(exp(16384)**1000)"),
      ("log(exp(1/exp(-16)))", "log(exp(1/exp(-16)))")] do
    try
      let answer ← CASOracle.Translate.read `sympyIn (fun _ : Fin 1 ↦ "v0") text
      if label.startsWith "tanh ×" || label.startsWith "(1 + v0)" || label.startsWith "(v0 - 1)"
      then
        IO.println s!"{label}: read"
      else IO.println s!"{label}: read as \
        {(CAS.Command.FullSimplify.Form.ofExpr [`x] answer).tidy.render}"
    catch error =>
      let message ← error.toMessageData.toString
      let reason := ((message.splitOn "is refused: ").getLast!.splitOn "\n").headD message
      IO.println s!"{label}: {reason}"

-- Requests are written with every operation parenthesized and powers kept as powers (the
-- pattern of the product does not match a power through its unfolding).
open Lean Elab Term in
/-- info: ( v0 ** 2 )
( ( 1 / 3 ) - ( v0 ** ( 3 / 2 ) ) )
( ( v0 ^ 2 ) * %pi ) -/
#guard_msgs in
#eval show TermElabM Unit from do
  let v : CAS.Verified.Expr (Fin 1) := .var 0
  IO.println (← CASOracle.Translate.write `sympyOut (fun _ ↦ "v0") (.pow v 2))
  IO.println (← CASOracle.Translate.write `sympyOut (fun _ ↦ "v0") (.sub (.rat 1 3) (.rpow v (.rat 3 2))))
  IO.println (← CASOracle.Translate.write `maximaOut (fun _ ↦ "v0") (.mul (.pow v 2) .pi))

-- The expansion of a power of a sum of eleven terms in ten variables is bounded before any
-- expansion, also inside a function that simplification removes.
open Lean Elab Term in
/-- info: its expansion could form products of over 10000 terms
its expansion could form products of over 10000 terms -/
#guard_msgs in
#eval show TermElabM Unit from do
  for text in ["(1 + v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9)**1000",
      "log(exp((1 + v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9)**1000))"] do
    try
      discard <| CASOracle.Translate.read `sympyIn (fun i : Fin 10 ↦ s!"v{i.val}") text
      IO.println "read"
    catch error =>
      let message ← error.toMessageData.toString
      IO.println (((message.splitOn "is refused: ").getLast!.splitOn "\n").headD message)

-- Gappa's bounds are read exactly, annotations skipped; a box with a negative end is rounded
-- outward.
open Lean Elab Term in
/-- info: some ((-768614336404564651 : Rat)/2305843009213693952, (3 : Rat)/4)
{ v0 in [ - 0.3333333333333333333333334 , 0.1428571428571428571428572 ] -> sqrt( v0 ) in ? }
-/
#guard_msgs in
#eval show TermElabM Unit from do
  IO.println (repr (CASOracle.Translate.gappaBounds?
    "Results:\n  v0 * v0 - 1 / 3 in [-768614336404564651b-61 {-0.333333, -2^(-1.58496)}, \
      3b-2 {0.75, 2^(-0.415037)}]"))
  IO.print (← CASOracle.Translate.gappaProblem (fun _ : Fin 1 ↦ "v0") (fun _ ↦ (-1/3, 1/7))
    (.sqrt (.var 0)))

-- DSLean's runner: an output over its bound, an output that is not UTF-8, and cancellations.
/-- info: overflow 1000
not UTF-8
cancelled
cancelled -/
#guard_msgs in
#eval show IO Unit from do
  let describe (result : Except DSLean.RunFailure DSLean.RunResult) : String :=
    match result with
    | .error (.overflow bytes) => s!"overflow {bytes}"
    | .error .notUTF8 => "not UTF-8"
    | .error .cancelled => "cancelled"
    | _ => "unexpected"
  IO.println (describe (← DSLean.runProgram "sh" #["-c", "yes | head -c 100000"] ""
    { maxOutputBytes := 1000 }))
  IO.println (describe (← DSLean.runProgram "sh" #["-c", "printf '\\377'"]))
  let token ← IO.CancelToken.new
  token.set
  IO.println (describe (← DSLean.runProgram "sleep" #["5"] "" {} (some token)))
  -- A descendant that leaves the group holds standard output after the program has exited; a
  -- cancellation while the run waits for that output is reported as a cancellation.
  let later ← IO.CancelToken.new
  discard <| IO.asTask (do IO.sleep 300; later.set) .dedicated
  IO.println (describe (← DSLean.runProgram "sh" #["-c", "setsid sleep 3 & exit 0"] ""
    {} (some later)))

/-! ## The axiom audit

A proof through a fresh axiom is refused by `Accept.audit`, and a command whose evidence adds a
theorem through one is refused by `Accept.withAuditedEvidence`, its messages discarded. The
environment is restored afterwards. -/

open Lean Elab Command Meta in
/-- info: refused: the proof depends on [_testedAxiom (through _testedAxiom)] -/
#guard_msgs (info, substring := true) in
run_meta withoutModifyingEnv do
  let fact ← mkEq (← mkAppM ``HAdd.hAdd #[mkNatLit 2, mkNatLit 2]) (mkNatLit 4)
  addDecl <| .axiomDecl
    { name := `_testedAxiom, levelParams := [], type := fact, isUnsafe := false }
  try
    CASOracle.Accept.audit "audit" fact (mkConst `_testedAxiom)
    logInfo "accepted"
  catch error =>
    logInfo m!"refused: {(← error.toMessageData.toString).drop 7}"

open Lean Elab Command Meta in
/-- error: report: refused, the evidence depends on [_taintedAxiom] -/
#guard_msgs (error, substring := true) in
run_cmd CASOracle.Accept.withAuditedEvidence "report" do
  liftTermElabM do
    let fact ← mkEq (← mkAppM ``HAdd.hAdd #[mkNatLit 1, mkNatLit 1]) (mkNatLit 2)
    addDecl <| .axiomDecl
      { name := `_taintedAxiom, levelParams := [], type := fact, isUnsafe := false }
    addDecl <| .thmDecl
      { name := `_taintedEvidence, levelParams := [], type := fact,
        value := mkConst `_taintedAxiom }
  logInfo "this report must not survive"

-- A tactic proof through a local definition whose value uses a fresh axiom: the proof term
-- mentions only the local, the kernel-checked closure substitutes it, and `closeGoal` audits
-- that closure too.
open Lean Elab Tactic Meta in
/-- info: refused: closeGoal: the proof depends on [_letAxiom (through -/
#guard_msgs (info, substring := true) in
run_elab withoutModifyingEnv do
  let fact ← mkEq (← mkAppM ``HAdd.hAdd #[mkNatLit 3, mkNatLit 3]) (mkNatLit 6)
  addDecl <| .axiomDecl
    { name := `_letAxiom, levelParams := [], type := fact, isUnsafe := false }
  withLetDecl `h fact (mkConst `_letAxiom) fun h ↦ do
    let goal ← mkFreshExprMVar fact
    try
      discard <| Tactic.run goal.mvarId! <|
        CASOracle.Accept.closeGoal "closeGoal" fun copy ↦ copy.assign h
      logInfo "accepted"
    catch error =>
      logInfo m!"refused: {← error.toMessageData.toString}"

/-! ## A right basis with a zero element

The Python lists the zero polynomial between `x` and `y` in its basis for `x, y`. The answer is
accepted, and the zero is kept in the basis and in both theorems. -/

/--
info: #cas [groebner x, y, oracle := sympy]
Domain: ℚ[x, y] as MvPolynomial (Fin 2) ℚ, with x = X 0, y = X 1
Input (polynomials): x, y
Output (Gröbner basis of the same ideal (checked)): x, 0, y

[CAS.Command.details] More details
  [CAS.Command.computation] Oracle hints from sympy (not checked)
    the basis is the reduced one for the lexicographic order x > y, each element scaled to coprime
    integer coefficients with a positive leading coefficient
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The proposed basis spans the same ideal
        Proposition: Ideal.span {X 0, X 1} = Ideal.span {X 0, 0, X 1}
        Validation: proof term checked by the kernel against this proposition
      [CAS.explanation.checkedStep] The proposed basis is a Gröbner basis
        Proposition: ∀ p ∈ Ideal.span {X 0, 0, X 1}, p ≠ 0 →
          ∃ g ∈ {X 0, 0, X 1}, MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := lax) in
#cas [groebner x, y, oracle := sympy] [x, y]

/-! ## Replay without an oracle

The calls the tactics suggest close their goals with no oracle at all (here the oracle is the
wrong one). The two right sums of squares are pinned with their scripts in full, exactly as they
were suggested, parsed and run, and the scripts are pasted as proofs. The reports of the command
are pinned in full, with the `example` they print or with the `none` line that says which check
failed. -/

example : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas [integrate primitive := fun x => (-1 + x) * Real.exp x]

example (x y : ℝ) (h1 : x * y = 1) (h2 : x = y) : x ^ 2 = 1 := by
  linear_combination h1 + x * h2

example (x y : ℝ) : 0 ≤ x ^ 4 + y ^ 4 - 4 * x * y + 2 := by
  rw [show x ^ 4 + y ^ 4 - 4 * x * y + 2 = (x ^ 2 - y ^ 2) ^ 2 + 2 * (x * y - 1) ^ 2 by ring]
  positivity

-- `x ^ 2 - 1 = (x - 1) ^ 2 + 2 * (x - 1)`, where `1 < x` enters as `0 < x - 1`.
/--
info: Try this:
  [apply] (have h₁ := sub_pos.mpr h; rw [← sub_pos, show x ^ 2 - 1 = (x - 1) ^ 2 + 2 * (x - 1) by ring]; positivity)
-/
#guard_msgs (whitespace := exact) in
example (x : ℝ) (h : 1 < x) : 1 < x ^ 2 := by
  cas [oracle := sympy]

theorem sos_replay_lt (x : ℝ) (h : 1 < x) : 1 < x ^ 2 := by
  (have h₁ := sub_pos.mpr h; rw [← sub_pos, show x ^ 2 - 1 = (x - 1) ^ 2 + 2 * (x - 1) by ring]; positivity)

-- The command prints the same script, after `intro`, in an `example` of the statement it proves,
-- checked where the command is.
/--
info: #cas [sos x, oracle := sympy]
Domain: x ∈ ℝ
Input (polynomial inequality): (1 < x → 1 < x ^ 2)
Output (sum of squares with a positive term (checked)): (x - 1) ^ 2 + 2 * (x - 1)

[CAS.Command.details] More details
  [CAS.Command.computation] Oracle-free proof
    example :
        ∀ (x : ℝ), 1 < x → 1 < x ^ 2 := by
      (intro x h₁; have h₂ := sub_pos.mpr h₁; rw [← sub_pos, show x ^ 2 - 1 = (x - 1) ^ 2 + 2 * (x - 1) by ring]; positivity)
  [CAS.Command.computation] Oracle hints from sympy (not checked)
    the Gram matrix was found numerically by cvxpy and rounded to exact rationals
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of squares
        Proposition: ∀ (x : ℝ), 1 < x → 1 < x ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := exact) in
#cas [sos x, oracle := sympy] (1 < x → 1 < x ^ 2)

theorem sos_replay_command :
    ∀ (x : ℝ), 1 < x → 1 < x ^ 2 := by
  (intro x h₁; have h₂ := sub_pos.mpr h₁; rw [← sub_pos, show x ^ 2 - 1 = (x - 1) ^ 2 + 2 * (x - 1) by ring]; positivity)

section
open Real
variable (sin : ℝ → ℝ)

-- Here `sin` is the variable of the section, so the report names `Real.sin`, and the `example`
-- is checked in this section.
/--
info: #cas [sos x, oracle := sympy]
Domain: x ∈ ℝ
Input (polynomial inequality): (0 ≤ (Real.sin x) ^ 2)
Output (sum of squares (checked)): Real.sin x ^ 2

[CAS.Command.details] More details
  [CAS.Command.computation] Oracle-free proof
    example :
        ∀ (x : ℝ), 0 ≤ Real.sin x ^ 2 := by
      (intro x; rw [show Real.sin x ^ 2 = Real.sin x ^ 2 by ring]; positivity)
  [CAS.Command.computation] Oracle hints from sympy (not checked)
    the Gram matrix was found numerically by cvxpy and rounded to exact rationals
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of squares
        Proposition: ∀ (x : ℝ), 0 ≤ Real.sin x ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := exact) in
#cas [sos x, oracle := sympy] (0 ≤ (Real.sin x) ^ 2)

theorem sos_replay_section :
    ∀ (x : ℝ), 0 ≤ Real.sin x ^ 2 := by
  (intro x; rw [show Real.sin x ^ 2 = Real.sin x ^ 2 by ring]; positivity)

end

section
variable [LE ℝ]

-- The script proves the statement with the order of `ℝ`, but in this section `0 ≤ x ^ 2` is read
-- with the order of the variable, so the `example` would state another proposition.
/--
info: #cas [sos x, oracle := sympy]
Domain: x ∈ ℝ
Input (polynomial): (x ^ 2)
Output (sum of squares (checked)): x ^ 2

[CAS.Command.details] More details
  [CAS.Command.computation] Oracle-free proof
    none: the script checks on the goal, but where the command is, the `example` with it does not state the proposition proved
  [CAS.Command.computation] Oracle hints from sympy (not checked)
    the Gram matrix was found numerically by cvxpy and rounded to exact rationals
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of squares
        Proposition: ∀ (x : ℝ), 0 ≤ x ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := exact) in
#cas [sos x, oracle := sympy] (x ^ 2)

end

-- The atom `(⌊x⌋ : ℝ)` prints as `↑⌊x⌋`, which does not say to which type it is cast, so the
-- script as printed does not check on the goal, and the statement is proved from the certificate
-- over the atom as elaborated.
/--
info: #cas [sos x, oracle := sympy]
Domain: x ∈ ℝ
Input (polynomial): ((⌊x⌋ : ℝ) ^ 2)
Output (sum of squares (checked)): ↑⌊x⌋ ^ 2

[CAS.Command.details] More details
  [CAS.Command.computation] Oracle-free proof
    none: the script as printed does not check here; the statement is proved from the same certificate over the atoms as elaborated
  [CAS.Command.computation] Oracle hints from sympy (not checked)
    the Gram matrix was found numerically by cvxpy and rounded to exact rationals
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of squares
        Proposition: ∀ (x : ℝ), 0 ≤ ↑⌊x⌋ ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := exact) in
#cas [sos x, oracle := sympy] ((⌊x⌋ : ℝ) ^ 2)

noncomputable opaque sos_atom : ℝ := 0

section
variable (h : 0 < sos_atom ^ 2)

-- The statement does not use the variable, hence the name `_x`. The search does not use `h`. In
-- the `example` with the script, `positivity` proves `0 ≤ sos_atom ^ 2` from `h`, so the
-- `example` command takes `h` as an argument, and the declaration is not the proposition proved.
/--
info: #cas [sos _x, oracle := sympy]
Domain: _x ∈ ℝ
Input (polynomial inequality): (0 ≤ sos_atom ^ 2)
Output (sum of squares (checked)): sos_atom ^ 2

[CAS.Command.details] More details
  [CAS.Command.computation] Oracle-free proof
    none: the script checks on the goal, but where the command is, the declaration of the `example` with it is not the proposition proved
  [CAS.Command.computation] Oracle hints from sympy (not checked)
    the Gram matrix was found numerically by cvxpy and rounded to exact rationals
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of squares
        Proposition: ∀ (_x : ℝ), 0 ≤ sos_atom ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := exact) in
#cas [sos _x, oracle := sympy] (0 ≤ sos_atom ^ 2)

-- Like an `example`, a `def` takes the variables of the section that its proof uses (a `theorem`
-- takes those of its statement), so the type of this one shows the hypothesis that the `example`
-- with the script takes.
set_option linter.defProp false in
def sos_replay_hypothesis :
    ∀ (_x : ℝ), 0 ≤ sos_atom ^ 2 := by
  (intro _x; rw [show sos_atom ^ 2 = sos_atom ^ 2 by ring]; positivity)

/-- info: sos_replay_hypothesis (h : 0 < sos_atom ^ 2) (_x : ℝ) : 0 ≤ sos_atom ^ 2 -/
#guard_msgs (whitespace := exact) in
#check sos_replay_hypothesis

end

-- The Python answers with the premise `0 < x` as the multiplier, though `x + 1` needs none:
-- `x * (x + 1) = x ^ 2 + x`, and `0 ≤ x` rests on the premise.
/--
info: Try this:
  [apply] (intro x h₁; refine pos_of_mul_pos_right (a := x) ?_ (by positivity); rw [show x * (x + 1) = x ^ 2 + x by ring]; positivity)
-/
#guard_msgs (whitespace := exact) in
example : ∀ x : ℝ, 0 < x → 0 < x + 1 := by
  cas [oracle := sympy]

theorem sos_replay_multiplier : ∀ x : ℝ, 0 < x → 0 < x + 1 := by
  (intro x h₁; refine pos_of_mul_pos_right (a := x) ?_ (by positivity); rw [show x * (x + 1) = x ^ 2 + x by ring]; positivity)

/-- info: 'sos_replay_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := exact) in
#print axioms sos_replay_lt

/-- info: 'sos_replay_multiplier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := exact) in
#print axioms sos_replay_multiplier

/-- info: 'sos_replay_command' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := exact) in
#print axioms sos_replay_command

/-- info: 'sos_replay_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := exact) in
#print axioms sos_replay_section

/-- info: 'sos_replay_hypothesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := exact) in
#print axioms sos_replay_hypothesis
