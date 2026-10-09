/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineBinaryNameMachine
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineCopy

namespace OAI

/-!
Compare one framed binary name with an already extracted reversed key.
The candidate stream loses precisely that name frame. The key and every other
non-work stack are preserved; the three work stacks are empty again on exit.
The scanner, copy loops, and head-by-head comparison all execute actual TM2
instructions. Whole words occur only in the correctness specification.
-/

namespace UniqueGamesTheorem.BinaryNameCompare

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Bool × Option Bool) × Option Bool

def clean (ambient : A) : State A := ((ambient, false, none), none)

def scanStateEquiv (A : Type) : BinaryNameMachine.State (A × Bool) ≃ State A where
  toFun s := ((s.1.1, s.1.2, s.2.1), s.2.2)
  invFun s := ((s.1.1, s.1.2.1), s.1.2.2, s.2)
  left_inv := by rintro ⟨⟨a, b⟩, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

def compareStateEquiv (A : Type) : MachineCompare.State A ≃ State A where
  toFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  invFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

inductive Label
  | scan | copyOut | copyBack | compare
  deriving DecidableEq

instance : Fintype Label where
  elems := {.scan, .copyOut, .copyBack, .compare}
  complete x := by cases x <;> simp

/-- Tapes: candidate stream, preserved key, candidate payload, key copy, scratch. -/
def instruction (tape : Fin 5 → K) (labels : Label → Λ)
    (equalExit differentExit malformedExit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .scan => MachineStateEquiv.statement (scanStateEquiv A)
      (BinaryNameMachine.scan (tape 0) (tape 2) (labels .scan)
        (some (labels .copyOut)) malformedExit)
  | .copyOut => UniqueGamesTheorem.Reduction.MachineTransfer.loopAt (tape 1) (tape 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 4) (tape 1) (tape 3) false
      (labels .copyBack) (some (labels .compare))
  | .compare => MachineStateEquiv.statement (compareStateEquiv A)
      (MachineCompare.loop (tape 2) (tape 3) (labels .compare) equalExit differentExit)

def steps (payloadLength keyLength : Nat) : Nat :=
  (payloadLength + 1) + 2 * (keyLength + 1) + (max payloadLength keyLength + 1)

theorem steps_le (payloadLength keyLength : Nat) :
    steps payloadLength keyLength ≤ 2 * payloadLength + 3 * keyLength + 4 := by
  unfold steps
  omega

/-- The shared canonical-name scan in the comparison/literal state layout. -/
theorem scanTrace (source destination : K) (distinct : source ≠ destination)
    (again : Λ) (accepted rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atScan : program again = MachineStateEquiv.statement (scanStateEquiv A)
      (BinaryNameMachine.scan source destination again accepted rejected))
    (base : K → List Bool) (ambient : A) (bits suffix : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (sourceWord : base source = BinaryNameMachine.frame bits ++ suffix)
    (empty : base destination = []) :
    (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some again, clean ambient, base⟩) =
      some ⟨accepted, clean ambient, tapesAt source destination base suffix bits.reverse⟩ := by
  apply (MachineStateEquiv.trace_iff (scanStateEquiv A).symm program _ _ _).mp
  have atBack : MachineStateEquiv.program (scanStateEquiv A).symm program again =
      BinaryNameMachine.scan source destination again accepted rejected := by
    change MachineStateEquiv.statement (scanStateEquiv A).symm (program again) = _
    rw [atScan]
    exact MachineStateEquiv.statement_symm_statement (scanStateEquiv A) _
  have initial : tapesAt source destination base (BinaryNameMachine.frame bits ++ suffix) [] =
      base := by
    rw [← sourceWord, ← empty]
    exact tapesAt_self _ _ _
  have native := BinaryNameMachine.framedTrace source destination distinct again accepted rejected
    (MachineStateEquiv.program (scanStateEquiv A).symm program) atBack base (ambient, false)
    bits suffix [] none
  simpa only [canonical, ↓reduceIte, initial, List.append_nil,
    MachineStateEquiv.configuration, scanStateEquiv, Equiv.coe_fn_symm_mk, clean,
    BinaryNameMachine.clean] using native

/-- The name is actually scanned, the key actually copied, and the resulting
payloads actually compared. Program premises are literal instruction equations. -/
theorem compareTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (equalExit differentExit malformedExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) =
      instruction tape labels equalExit differentExit malformedExit l)
    (base : K → List Bool) (bits suffix key : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (sourceWord : base (tape 0) = BinaryNameMachine.frame bits ++ suffix)
    (keyWord : base (tape 1) = key)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) (ambient : A) :
    (advance (TM2.step program))^[steps bits.length key.length]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨if bits.reverse = key then equalExit else differentExit,
        clean ambient, Function.update base (tape 0) suffix⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let finalBase := Function.update base (tape 0) suffix
  let afterScan := Function.update finalBase (tape 2) bits.reverse
  let afterCopy := Function.update afterScan (tape 3) key
  have scanRun := scanTrace (tape 0) (tape 2) (hd 0 2 (by decide))
    (labels .scan) (some (labels .copyOut)) malformedExit program (atLabels .scan)
    base ambient bits suffix canonical sourceWord candidateEmpty
  have afterScanKey : afterScan (tape 1) = key := by
    simpa [afterScan, finalBase, hd 1 2 (by decide), hd 1 0 (by decide)] using keyWord
  have afterScanCopy : afterScan (tape 3) = [] := by
    simpa [afterScan, finalBase, hd 3 2 (by decide), hd 3 0 (by decide)] using copyEmpty
  have afterScanScratch : afterScan (tape 4) = [] := by
    simpa [afterScan, finalBase, hd 4 2 (by decide), hd 4 0 (by decide)] using scratchEmpty
  have copyRun : (advance (TM2.step program))^[2 * (key.length + 1)]
      (some ⟨some (labels .copyOut), clean ambient, afterScan⟩) =
      some ⟨some (labels .compare), clean ambient, afterCopy⟩ := by
    have h := MachineCopy.copyTrace (tape 1) (tape 3) (tape 4)
      (hd 1 3 (by decide)) (hd 1 4 (by decide)) (hd 3 4 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels .compare)) program
      (atLabels .copyOut) (atLabels .copyBack) afterScan afterScanScratch
      (ambient, false, none) none
    simpa only [afterScanKey, afterScanCopy, List.append_nil, clean, afterCopy] using h
  have candidateWord : afterCopy (tape 2) = bits.reverse := by
    simp [afterCopy, afterScan, hd 2 3 (by decide)]
  have copiedWord : afterCopy (tape 3) = key := by simp [afterCopy]
  have restored : UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt (tape 2) (tape 3)
      afterCopy [] [] = finalBase := by
    funext k
    by_cases hc : k = tape 2
    · subst k
      simp [UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, finalBase,
        hd 2 3 (by decide), hd 2 0 (by decide), candidateEmpty]
    · by_cases hk : k = tape 3
      · subst k
        simp [UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, finalBase,
          hd 3 0 (by decide), copyEmpty]
      · simp [UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, hc, hk]
  have comparisonRun : (advance (TM2.step program))^[max bits.length key.length + 1]
      (some ⟨some (labels .compare), clean ambient, afterCopy⟩) =
      some ⟨if bits.reverse = key then equalExit else differentExit,
        clean ambient, finalBase⟩ := by
    let back := MachineStateEquiv.program (compareStateEquiv A).symm program
    have atCompare : back (labels .compare) =
        MachineCompare.loop (tape 2) (tape 3) (labels .compare) equalExit differentExit := by
      change MachineStateEquiv.statement (compareStateEquiv A).symm
        (program (labels .compare)) = _
      rw [atLabels .compare]
      exact MachineStateEquiv.statement_symm_statement (compareStateEquiv A) _
    have native := MachineCompare.compareTrace_fromTapes (tape 2) (tape 3)
      (hd 2 3 (by decide)) (labels .compare) equalExit differentExit back atCompare afterCopy
      ambient none none
    rw [candidateWord, copiedWord, restored, List.length_reverse] at native
    have transported := MachineStateEquiv.trace (compareStateEquiv A) back _ _ _ native
    have backForward : MachineStateEquiv.program (compareStateEquiv A) back = program :=
      MachineStateEquiv.program_symm_program (compareStateEquiv A).symm program
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, compareStateEquiv, Equiv.coe_fn_mk, clean] using transported
  exact UniqueGamesTheorem.Foundations.Complexity.MachineComposition.iterate_trans (UniqueGamesTheorem.Foundations.Complexity.MachineComposition.iterate_trans scanRun copyRun) comparisonRun


end UniqueGamesTheorem.BinaryNameCompare

end OAI
