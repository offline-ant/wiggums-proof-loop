/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineExpanderFamilyTransferLemmas

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem clearRegister_position (state : State ρ d) :
    (clearRegister state).2 = state.2 := rfl

@[simp] theorem clearRegister_register (state : State ρ d) :
    (clearRegister state).1.2 = none := rfl

@[simp] theorem clearRegister_idempotent (state : State ρ d) :
    clearRegister (clearRegister state) = clearRegister state := rfl

theorem boundaryTapes_reverse_update (vertex remaining : Nat)
    (oldTable output countSuffix result nextOutput nextResult : List Bool) :
    Function.update
      (Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
        (.inl .output) nextOutput)
      (.inr .result) nextResult =
      boundaryTapes vertex remaining oldTable nextOutput countSuffix nextResult := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

variable [Fintype ρ]

/-- Exact execution of the entire final reverse loop, including its empty
test. No reversal-execution hypothesis is assumed. -/
theorem reverseOutputTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 1]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  have run := MachineControl.transferTrace (Γ := Alphabet)
    (.inl .output) (.inr .result) (guardStates ρ d) (by decide) id false
    (.inr .reverseOutput) (some (.inr .done)) (program positive H) rfl
    (boundaryTapes vertex remaining oldTable output countSuffix result)
    ((guardStates ρ d).symm state).1 ((guardStates ρ d).symm state).2
  have source : boundaryTapes vertex remaining oldTable output countSuffix result
      (.inl .output) = output := rfl
  have destination : boundaryTapes vertex remaining oldTable output countSuffix result
      (.inr .result) = result := rfl
  simpa only [source, destination, guardStates_apply, guardStates_symm_apply, Prod.mk.eta,
    Reduction.MachineTransfer.tapesAt, boundaryTapes_reverse_update, clearRegister,
    List.map_id] using run

/-- The actual `done` statement halts one transition after reversal completes. -/
theorem reverseOutputHaltTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 2]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  rw [show output.length + 2 = (output.length + 1) + 1 by omega,
    Function.iterate_succ_apply',
    reverseOutputTrace positive H vertex remaining oldTable output countSuffix result state]
  exact doneStep positive H
    (boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result))
    (clearRegister state)


def reverseOutputHaltInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩
      (some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩)
      (output.length + 2) where
  steps := output.length + 2
  evals_in_steps := reverseOutputHaltTrace positive H vertex remaining oldTable output countSuffix result state
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
