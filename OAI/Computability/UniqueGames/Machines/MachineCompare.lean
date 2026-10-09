/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI

section

/-!
# A destructive equality test on two actual Bool stacks

Each loop transition pops both stacks and compares only the two finite head
registers. A sticky mismatch flag makes the loop continue after disagreement.
The final empty/empty test selects an equal or different continuation and resets
all comparison registers. The ambient state and every other tape are preserved.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCompare

open Turing
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (K : Type) : K → Type := fun _ => Bool
abbrev State (σ : Type) := σ × Bool × Option Bool × Option Bool

/-- An optional continuation, without reading or writing any tape. -/
def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

/-- Clear both head registers and the mismatch flag after choosing the exit. -/
def finish (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  .load (fun state => (state.1, false, none, none)) (exitAt exit)

/-- The only comparison performed by the program is on two `Option Bool` heads.
In particular, no statement is given a whole-list equality oracle. -/
def loop (left right : K) (loopLabel : Λ) (equalExit differentExit : Option Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ) :=
  .pop left (fun state head => (state.1, state.2.1, head, state.2.2.2))
    (.pop right (fun state head => (state.1, state.2.1, state.2.2.1, head))
      (.branch (fun state => state.2.2.1.isNone && state.2.2.2.isNone)
        (.branch (fun state => state.2.1) (finish differentExit) (finish equalExit))
        (.load (fun state =>
          (state.1, state.2.1 || decide (state.2.2.1 ≠ state.2.2.2), none, none))
          (.goto fun _ => loopLabel))))

/-- Specification-only outcome, also recording an earlier mismatch. -/
def mismatch (flag : Bool) (leftWord rightWord : List Bool) : Bool :=
  flag || decide (leftWord ≠ rightWord)

/-- Comparing the two heads and then the tails records exactly the same
sticky mismatch as comparing the original words. -/
theorem mismatch_tail (flag : Bool) (leftWord rightWord : List Bool) :
    mismatch (flag || decide (leftWord.head? ≠ rightWord.head?))
      leftWord.tail rightWord.tail = mismatch flag leftWord rightWord := by
  cases leftWord with
  | nil => cases rightWord <;> simp [mismatch]
  | cons leftHead leftTail =>
    cases rightWord with
    | nil => simp [mismatch]
    | cons rightHead rightTail =>
      by_cases same : leftTail = rightTail <;>
        cases flag <;> cases leftHead <;> cases rightHead <;> simp [mismatch, same]

@[simp] theorem stepAux_exitAt (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (exitAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) state tapes =
      ⟨exit, (state.1, false, none, none), tapes⟩ := by
  simp [finish, TM2.stepAux]

private theorem update_left (left right : K) (distinct : left ≠ right)
    (base : K → List Bool) (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) left replacement =
      tapesAt left right base replacement rightWord := by
  unfold tapesAt
  rw [Function.update_comm distinct.symm, Function.update_idem]

private theorem update_right (left right : K) (base : K → List Bool)
    (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) right replacement =
      tapesAt left right base leftWord replacement := by
  simp [tapesAt]

/-- Both exhausted operands terminate; every other transition compares their
heads and scans their tails. An exhausted operand needs no separate loop. -/
theorem loop_step (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool)
    (ambient : σ) (flag : Bool) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩ =
      some (if leftWord = [] ∧ rightWord = [] then
        ⟨if flag then differentExit else equalExit, (ambient, false, none, none),
          tapesAt left right base [] []⟩
      else
        ⟨some loopLabel,
          (ambient, flag || decide (leftWord.head? ≠ rightWord.head?), none, none),
          tapesAt left right base leftWord.tail rightWord.tail⟩) := by
  change some (TM2.stepAux (program loopLabel) _ _) = _
  rw [atLoop]
  cases leftWord <;> cases rightWord <;> cases flag <;>
    simp [loop, TM2.stepAux, distinct, update_left, update_right]

/-- The exact trace with a possibly pre-existing mismatch. Every input symbol
is consumed even when disagreement has already been detected. -/
theorem compareTrace_flag (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if mismatch flag leftWord rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  by_cases empty : leftWord = [] ∧ rightWord = []
  · rcases empty with ⟨rfl, rfl⟩
    simpa [mismatch] using
      loop_step left right distinct loopLabel equalExit differentExit program atLoop
        base [] [] ambient flag leftRegister rightRegister
  · have length : max leftWord.length rightWord.length =
        max leftWord.tail.length rightWord.tail.length + 1 := by
      cases leftWord <;> cases rightWord <;> simp_all
    rw [length, Function.iterate_succ_apply, MachineComposition.advance_some,
      loop_step left right distinct loopLabel equalExit differentExit program atLoop,
      ite_eq_right empty]
    rw [compareTrace_flag left right distinct loopLabel equalExit differentExit program atLoop
      base leftWord.tail rightWord.tail ambient
      (flag || decide (leftWord.head? ≠ rightWord.head?)) none none, mismatch_tail]
termination_by leftWord.length + rightWord.length
decreasing_by
  cases leftWord <;> cases rightWord <;> simp_all
  all_goals omega

/-- With a clear initial flag, the final continuation tests equality of the
two complete original words. Both tapes and all comparison registers are empty. -/
theorem compareTrace_fromTapes (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max (base left).length (base right).length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩) =
      some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  have trace := compareTrace_flag left right distinct loopLabel equalExit differentExit program
    atLoop base (base left) (base right) ambient false leftRegister rightRegister
  rw [tapesAt_self] at trace
  by_cases same : base left = base right <;> simpa [mismatch, same] using trace


/-- An actual timed execution witness, with the exact stored transition count. -/
def compareInTime (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩)
      (max (base left).length (base right).length + 1) where
  steps := max (base left).length (base right).length + 1
  evals_in_steps := compareTrace_fromTapes left right distinct loopLabel equalExit differentExit
    program atLoop base ambient leftRegister rightRegister
  steps_le_m := Nat.le_refl _

@[simp] theorem compareInTime_steps (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (compareInTime left right distinct loopLabel equalExit differentExit program atLoop base
      ambient leftRegister rightRegister).steps =
        max (base left).length (base right).length + 1 := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineCompare

end

end OAI
