/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import Lean.Elab.Command
import DSLean.Process
import CAS.IncludeStr

/-!
# The oracles and how they run

The commands of `CASOracle` ask an external program for a proposal (a primitive, a
factorization, cofactors, a root, a value) and then prove it in Lean, or refuse. The programs
are SymPy, SageMath, PARI/GP, FLINT, Maxima and Gappa, the constructors of `Oracle`, and
`Oracle.tasks` lists the tasks each one takes. `run` runs the program of an oracle for one
request and returns its answer; nothing it returns is trusted.

## Implementation notes

The oracles are built on DSLean, used as a Lake package: DSLean's grammars (`CASOracle.Syntax`)
write the request and read the answer, and DSLean's runner (`DSLean.Process`) runs the program
for one request, with the deadline `cas.oracle.timeout` (milliseconds), a bound on its output,
the elaborator's cancellation, and on every exit path an attempt to end its process group:
`SIGTERM`, then `SIGKILL` through the system `kill` when there is one, with bounded waits of
about five seconds in all (a descendant that leaves the group, or a process in an
uninterruptible wait, is not covered). It opens no socket and starts no server. CASOracle copies
none of DSLean's code. The revision we pin is DSLean's port to Lean 4.35.0, the branch
<https://github.com/Robertboy18/DSLean/tree/leancas>, with five changes: operand precedences that
follow the precedence option, pattern priorities that hold in `toExternal'`, a runner with a
deadline and a bounded output (`DSLean/Process.lean`), Gappa's input grammar in a module of its
own, and info trees turned off while the `gappa` tactic elaborates the proof it generates. The
files of `CASOracle` are ordinary files, not `module`s, because DSLean's are, so a `module` file
cannot import them.

The program of each oracle comes from an environment variable:

* `sympy`, `pari`, `flint`: the Python of `SYMLEAN_SYMPY_PYTHON`, `SYMLEAN_PARI_PYTHON` or
  `SYMLEAN_FLINT_PYTHON`, else of `SYMLEAN_ORACLE_PYTHON`, else `python3`, run as
  `python -c <program>`; it needs SymPy, and `cypari2` or `python-flint` for PARI and FLINT;
* `sage`: `SYMLEAN_SAGE_PATH` (default `sage`), run as `sage -c <program>`;
* `maxima`: `SYMLEAN_MAXIMA_PATH` (default `maxima`), as `maxima --very-quiet --batch-string`;
* `gappa`: `SYMLEAN_GAPPA_PATH` (default `gappa`), with the problem on standard input.

The Python programs are `oracle/symlean_oracle.py`, embedded here with `include_str`, followed
by one call. A program answers with lines `@@ key payload`; other lines are ignored. A record
`@@ unavailable reason`, `@@ unsupported reason` or `@@ failed reason` makes the run that
failure; a record whose key the task does not expect, an exit code other than 0, or no record at
all (except for the tasks whose answer is a list, which may be empty) is refused. Each command
then checks how many records of each key it reads, and `groebner` also their order. Numbers in
records are read with bounds on their length before their value is computed.

Gappa, which only the task `enclose` asks, is cited in `CASOracle.Numeric`, and the solvers
behind the sums of squares in `CASOracle.Sos`.

## References

* taterowney, *DSLean: A Bi-directional Interface Between Lean 4 and External Languages*,
  <https://github.com/taterowney/DSLean>, licensed under CC BY 4.0,
  <https://creativecommons.org/licenses/by/4.0/>. NOTICE gives the revision we pin.
* Aaron Meurer, Christopher P. Smith, Mateusz Paprocki, Ondřej Čertík, Sergey B. Kirpichev,
  Matthew Rocklin, AMiT Kumar, Sergiu Ivanov, Jason K. Moore, Sartaj Singh, Thilina Rathnayake,
  Sean Vig, Brian E. Granger, Richard P. Muller, Francesco Bonazzi, Harsh Gupta, Shivam Vats,
  Fredrik Johansson, Fabian Pedregosa, Matthew J. Curry, Andy R. Terrel, Štěpán Roučka,
  Ashutosh Saboo, Isuru Fernando, Sumith Kulal, Robert Cimrman and Anthony Scopatz, "SymPy:
  symbolic computing in Python", *PeerJ Computer Science* 3 (2017), e103,
  <https://doi.org/10.7717/peerj-cs.103>. Tested with version 1.14.0.
* The Sage Developers, *SageMath, the Sage Mathematics Software System*,
  <https://www.sagemath.org>, <https://doi.org/10.5281/zenodo.8042260>. Tested with version 10.9.
* Wolfram Decker, Gert-Martin Greuel, Gerhard Pfister and Hans Schönemann, *Singular: A computer
  algebra system for polynomial computations*, <https://www.singular.uni-kl.de>. Tested with
  version 4.4.1, the one in SageMath 10.9, which computes with it the Gröbner bases, cofactors
  and factorizations of the `sage` oracle.
* The PARI Group, *PARI/GP*, Univ. Bordeaux, <https://pari.math.u-bordeaux.fr/>. Tested with
  version 2.17.2, through cypari2.
* The FLINT team, *FLINT: Fast Library for Number Theory*, 2026, <https://flintlib.org>. Tested
  with version 3.6.0, through python-flint 0.9.0.
* Fredrik Johansson, "Arb: Efficient Arbitrary-Precision Midpoint-Radius Interval Arithmetic",
  *IEEE Transactions on Computers* 66 (2017), pp. 1281-1292,
  <https://doi.org/10.1109/TC.2017.2690633>, the ball arithmetic of the `flint` oracle.
* Maxima.sourceforge.io, *Maxima, a Computer Algebra System*, <https://maxima.sourceforge.io/>.
  Tested with version 5.49.0.
-/

namespace CASOracle

open Lean

/-- The external systems SymLean can consult. -/
inductive Oracle where
  | sympy
  | sage
  | pari
  | flint
  | maxima
  | gappa
  deriving BEq, Inhabited, Repr

namespace Oracle

/-- The oracle named by an identifier of the command syntax. -/
def ofName? : Name → Option Oracle
  | `sympy => some .sympy
  | `sage => some .sage
  | `pari => some .pari
  | `flint => some .flint
  | `maxima => some .maxima
  | `gappa => some .gappa
  | _ => none

/-- The name of the oracle in reports. -/
def name : Oracle → String
  | .sympy => "sympy"
  | .sage => "sage"
  | .pari => "pari"
  | .flint => "flint"
  | .maxima => "maxima"
  | .gappa => "gappa"

/-- The environment variable that names the oracle's program. -/
def programVariable : Oracle → String
  | .sympy => "SYMLEAN_SYMPY_PYTHON"
  | .sage => "SYMLEAN_SAGE_PATH"
  | .pari => "SYMLEAN_PARI_PYTHON"
  | .flint => "SYMLEAN_FLINT_PYTHON"
  | .maxima => "SYMLEAN_MAXIMA_PATH"
  | .gappa => "SYMLEAN_GAPPA_PATH"

/-- Whether the oracle runs in Python. -/
def isPython : Oracle → Bool
  | .sympy | .pari | .flint => true
  | _ => false

/-- The variables the oracle's program may come from, for messages. -/
def configuration (oracle : Oracle) : String :=
  if oracle.isPython then s!"{oracle.programVariable} or SYMLEAN_ORACLE_PYTHON"
  else oracle.programVariable

/-- The DSLean tool that runs the oracle: the program of its variable, else, for the Python
backends, the Python of `SYMLEAN_ORACLE_PYTHON`, else the program's usual name. -/
def tool (oracle : Oracle) : IO DSLean.ExternalTool := do
  let default ← match oracle with
    | .sympy | .pari | .flint => pure ((← IO.getEnv "SYMLEAN_ORACLE_PYTHON").getD "python3")
    | .sage => pure "sage"
    | .maxima => pure "maxima"
    | .gappa => pure "gappa"
  return { name := oracle.name, envVar := oracle.programVariable, default }

end Oracle

/-- The deadline of one external oracle run, in milliseconds. -/
register_option cas.oracle.timeout : Nat := {
  defValue := 120000
  descr := "deadline of one external oracle run of CASOracle, in milliseconds"
}

/-- The Python programs, embedded at build time. -/
def pythonProgram : String := include_str "../oracle/symlean_oracle.py"

/-- Why an oracle gave no answer. -/
inductive Failure where
  /-- The program could not be started, or lacks the package the backend needs. -/
  | unavailable (reason : String)
  /-- The backend has no answer in the checked language, or no such task. -/
  | unsupported (reason : String)
  /-- The program ran past the deadline and was ended. -/
  | timeout (milliseconds : Nat)
  /-- The program failed, or its output is not an answer. -/
  | failed (reason : String)

/-- A one-line account of a failure. -/
def Failure.render (oracle : Oracle) : Failure → String
  | .unavailable reason => s!"oracle {oracle.name} is unavailable: {reason} (configure it with \
      {oracle.configuration})"
  | .unsupported reason => s!"oracle {oracle.name} has no checkable answer: {reason}"
  | .timeout ms => s!"oracle {oracle.name} did not answer within {ms} ms \
      (option cas.oracle.timeout)"
  | .failed reason => s!"oracle {oracle.name} failed: {reason}"

/-- Fail with `failure`. -/
def fail {α : Type} (oracle : Oracle) (failure : Failure) : CoreM α :=
  throwError (failure.render oracle)

/-- At most the last `n` characters of `text`. -/
private def lastChars (text : String) (n : Nat) : String :=
  if text.length > n then (text.drop (text.length - n)).toString else text

/-- Run the oracle's program with `args` and `stdin` under `cas.oracle.timeout` and the
elaborator's cancellation (which interrupts the elaboration, as any cancellation does). -/
def run (oracle : Oracle) (args : Array String) (stdin : String := "")
    (maxErrorBytes : Nat := 4096) : CoreM DSLean.RunResult := do
  let timeoutMs := cas.oracle.timeout.get (← getOptions)
  let tool ← (oracle.tool : IO _)
  match ← (tool.run args stdin { timeoutMs, maxErrorBytes } (← read).cancelTk? : IO _) with
  | .ok result => return result
  | .error .cancelled => throwInterruptException
  | .error (.unavailable reason) => fail oracle (.unavailable reason)
  | .error (.timeout ms) => fail oracle (.timeout ms)
  | .error (.overflow bytes) => fail oracle (.failed s!"the answer is over {bytes} bytes")
  | .error .notUTF8 => fail oracle (.failed "the answer is not UTF-8")
  | .error .unclosed => fail oracle (.failed "the standard output did not close")
  | .error (.io error) => fail oracle (.failed error)

/-- One answer record `@@ key payload`. -/
structure Record where
  /-- The record's key. -/
  key : String
  /-- The rest of the line. -/
  payload : String
  deriving Inhabited

/-- The records of a run, with `keys` the keys the task expects; `allowEmpty` for a task whose
answer is a list, which may be empty. -/
def records (oracle : Oracle) (keys : List String) (result : DSLean.RunResult)
    (allowEmpty : Bool := false) : CoreM (Array Record) := do
  let found := (result.stdout.splitOn "\n").toArray.filterMap fun line ↦ do
    let line := line.trimAscii.toString
    guard (line.startsWith "@@ ")
    let key :: rest := ((line.drop 3).toString.splitOn " ") | none
    return { key, payload := (" ".intercalate rest).trimAscii.toString }
  for record in found do
    match record.key with
    | "unavailable" => fail oracle (.unavailable record.payload)
    | "unsupported" => fail oracle (.unsupported record.payload)
    | "failed" => fail oracle (.failed record.payload)
    | key => unless keys.contains key do
        fail oracle (.failed s!"the answer has an unexpected record {key}")
  if found.isEmpty && !(allowEmpty && result.exitCode == 0) then
    let detail := lastChars (if result.stderr.isEmpty then result.stdout else result.stderr) 600
    if result.exitCode == 127 then
      fail oracle (.unavailable s!"the program did not run: {detail}")
    fail oracle (.failed s!"exit code {result.exitCode}, no answer: {detail}")
  unless result.exitCode == 0 do
    fail oracle (.failed s!"the oracle exited with code {result.exitCode} after answering")
  return found

/-- The payloads of the records with `key`, at most `max` of them. -/
def payloads (oracle : Oracle) (found : Array Record) (key : String) (max : Nat) :
    CoreM (Array String) := do
  let selected := (found.filter (·.key == key)).map (·.payload)
  if selected.size > max then
    fail oracle (.failed s!"the answer has {selected.size} records {key}, over {max}")
  return selected

/-- The payload of the one record with `key`. -/
def payload (oracle : Oracle) (found : Array Record) (key : String) : CoreM String := do
  match (found.filter (·.key == key)).toList with
  | [record] => return record.payload
  | [] => fail oracle (.failed s!"the answer has no record {key}")
  | _ => fail oracle (.failed s!"the answer has several records {key}")

/-- A Python string literal of `text`. -/
def py (text : String) : String :=
  "\"" ++ String.join (text.toList.map fun c ↦
    if c == '\\' then "\\\\" else if c == '"' then "\\\"" else if c == '\n' then "\\n"
    else c.toString) ++ "\""

/-- A Python list of string literals. -/
def pyList (items : List String) : String := "[" ++ ", ".intercalate (items.map py) ++ "]"

/-- The Python expression reading the request text `text` over the variables `names`. -/
def pyRead (text : String) (names : List String) : String :=
  s!"read({py text}, {pyList names})"

/-- The Python expression of the SymPy variables `names`. -/
def pyVariables (names : List String) : String :=
  "V(" ++ ", ".intercalate (names.map py) ++ ")"

/-- The tasks of each oracle. The task `sos` of `sympy` needs cvxpy (`pip install cvxpy`) in the
oracle's Python. -/
def Oracle.tasks : Oracle → List String
  | .sympy => ["integrate", "factor", "solve", "nroots", "nintegrate", "eigenvalues", "groebner",
      "member", "dsolve", "sum", "sos"]
  | .sage => ["integrate", "factor", "solve", "nintegrate", "eigenvalues", "groebner", "member",
      "dsolve", "sum"]
  | .pari | .flint => ["factor", "nroots", "nintegrate", "eigenvalues"]
  | .maxima => ["integrate", "factor"]
  | .gappa => ["enclose"]

/-- Refuse a task the oracle does not have. -/
def requireTask (oracle : Oracle) (task : String) : CoreM Unit := do
  unless oracle.tasks.contains task do fail oracle (.unsupported s!"{oracle.name} has no {task}")

/-- Run the method `task` of the oracle's backend in `oracle/symlean_oracle.py` on the Python
`arguments`, and return its records, `keys` being the keys the task prints. -/
def askPython (oracle : Oracle) (task : String) (keys : List String) (arguments : String)
    (allowEmpty : Bool := false) : CoreM (Array Record) := do
  requireTask oracle task
  let backend ← match oracle with
    | .sympy => pure "SympyBackend"
    | .pari => pure "PariBackend"
    | .flint => pure "FlintBackend"
    | .sage => pure "SageBackend"
    | _ => fail oracle (.unsupported s!"{oracle.name} does not run in Python")
  let source := pythonProgram ++ s!"\nrun(lambda: {backend}().{task}({arguments}))\n"
  records oracle keys (← run oracle #["-c", source]) allowEmpty

/-- For the task `task`, evaluate the Maxima expression `command` and return its value as
written by Maxima's `string`, under the record `key`. Maxima echoes its batch input, whose lines begin with
`print(`, not with `@@`. -/
def askMaxima (task key command : String) : CoreM String := do
  requireTask .maxima task
  let script := s!"display2d:false$ linel:1000000$ print(\"@@\", \"{key}\", string({command}))$"
  let found ← records .maxima [key]
    (← run .maxima #["--very-quiet", "--batch-string", script])
  payload .maxima found key

end CASOracle
