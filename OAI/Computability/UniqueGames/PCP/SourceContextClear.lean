/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.FinCases
import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas
import OAI.Computability.UniqueGames.PCP.SourceContextLoad

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

open Turing Complexity MachineComposition

abbrev Tape := SourceContextLoad.Tape

variable {u : Nat} {Extra : Type}

def fields : List (Tape u Extra) :=
  (List.finRange u).flatMap fun j => (List.finRange 6).map (SourceContextLoad.Tape.field j)

@[simp] theorem fields_length : (fields (u := u) (Extra := Extra)).length = 6 * u := by
  simp [fields, Nat.mul_comm]

theorem field_mem (j : Fin u) (s : Fin 6) :
    (SourceContextLoad.Tape.field j s : Tape u Extra) ∈ fields := by
  simp [fields]

theorem mem_fields_iff (p : Tape u Extra) : p ∈ fields ↔ ∃ j s, p = .field j s := by
  simp [fields, eq_comm]

def outputTapes (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .field _ _ => []
  | p => base p

@[simp] theorem output_field (base : Tape u Extra → List Bool) (j : Fin u) (s : Fin 6) :
    outputTapes base (.field j s) = [] := rfl


abbrev Label (u : Nat) (Extra : Type) :=
  MachineDrainMany.Label (fields (u := u) (Extra := Extra)) ⊕ Unit

private def entryLabel {K : Type} : (chosen : List K) → MachineDrainMany.Label chosen ⊕ Unit
  | [] => .inr ()
  | _ :: _ => .inl (.inl ())

def main : Label u Extra := entryLabel fields

variable [DecidableEq Extra]

def program : Label u Extra → TM2.Stmt (fun _ : Tape u Extra => Bool)
    (Label u Extra) (Unit × Option Bool)
  | .inl l => MachineDrainMany.instruction fields Sum.inl (some (.inr ())) l
  | .inr _ => .load (fun _ => ((), none)) .halt

private theorem entryLabel_eq {K : Type} (chosen : List K) :
    MachineDrainMany.entry chosen
      (Sum.inl : MachineDrainMany.Label chosen → MachineDrainMany.Label chosen ⊕ Unit)
      (some (.inr ())) = some (entryLabel chosen) := by
  cases chosen <;> rfl

omit [DecidableEq Extra] in
private theorem entry_eq :
    MachineDrainMany.entry (fields (u := u) (Extra := Extra)) Sum.inl (some (.inr ())) =
      some (main (u := u) (Extra := Extra)) := entryLabel_eq fields

theorem finalTapes_eq (base : Tape u Extra → List Bool) :
    MachineDrainMany.finalTapes fields base = outputTapes base := by
  funext p
  rw [MachineDrainMany.finalTapes_apply]
  cases p <;> simp [mem_fields_iff, outputTapes]

/-- Use the common drain-and-reset execution directly: the caller needs a
budget, not an equality between the budget and the number of transitions. -/
def clearInTime (base : Tape u Extra → List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some main, ((), register), base⟩
      (some ⟨none, ((), none), outputTapes base⟩)
      (MachineDrainMany.lengthSum fields base + 6 * u + 1) := by
  have run := MachineDrainMany.executionWithReset fields Sum.inl (.inr ())
    program (fun _ => rfl) ((), none) rfl base ((), register)
  refine { steps := run.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [entry_eq, finalTapes_eq] using run.evals_in_steps
  · exact run.steps_le_m.trans (Nat.add_le_add_right
      (by simpa only [fields_length] using MachineDrainMany.steps_le fields base) 1)

private theorem lengthSum_le_selected {K : Type} (chosen : List K)
    (base : K → List Bool) (B : Nat) (h : ∀ k ∈ chosen, (base k).length ≤ B) :
    MachineDrainMany.lengthSum chosen base ≤ chosen.length * B := by
  simpa [MachineDrainMany.lengthSum] using
    List.sum_le_length_nsmul (chosen.map fun k => (base k).length) B
      (by simpa only [List.forall_mem_map] using h)

theorem clauseField_length_le {n : Nat} (clause : Target.Clause n) (s : Fin 6) :
    (encodeWord ((clauseWords clause)[s.val]'(by simp))).length ≤ n + 2 := by
  have h0 := clause[0].variableIndex.isLt
  have h1 := clause[1].variableIndex.isLt
  have h2 := clause[2].variableIndex.isLt
  fin_cases s <;> simp [clauseWords, literalWords, encodeWord_length]
  all_goals first | omega | (split <;> omega)

theorem variables_add_two_le_input (F : Target.Formula) :
    F.variables + 2 ≤ (formulaBits F).length := by
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

omit [DecidableEq Extra] in
theorem loaded_field_length_le (F : Target.Formula)
    (tuple : Fin u → Fin F.clauses.length) (base : Tape u Extra → List Bool)
    (hfields : ∀ j s, base (.field j s) = []) (j : Fin u) (s : Fin 6) :
    (SourceContextLoad.stageTapes F tuple base u (.field j s)).length ≤
      (formulaBits F).length := by
  rw [SourceContextLoad.stageTapes_field, ite_eq_left j.isLt, hfields, List.append_nil]
  exact (clauseField_length_le _ s).trans (variables_add_two_le_input F)

omit [DecidableEq Extra] in
theorem loaded_cost_le (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (hfields : ∀ j s, base (.field j s) = []) :
    MachineDrainMany.lengthSum fields (SourceContextLoad.stageTapes F tuple base u) + 6 * u + 1 ≤
      6 * u * ((formulaBits F).length + 1) + 1 := by
  have h := lengthSum_le_selected fields (SourceContextLoad.stageTapes F tuple base u)
    (formulaBits F).length (by
      intro p hp
      obtain ⟨j, s, rfl⟩ := (mem_fields_iff p).mp hp
      exact loaded_field_length_le F tuple base hfields j s)
  rw [fields_length] at h
  rw [Nat.mul_add, Nat.mul_one]
  omega

def clearLoadedInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (hfields : ∀ j s, base (.field j s) = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some main, ((), register), SourceContextLoad.stageTapes F tuple base u⟩
      (some ⟨none, ((), none), outputTapes (SourceContextLoad.stageTapes F tuple base u)⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) := by
  have run := clearInTime (SourceContextLoad.stageTapes F tuple base u) register
  exact {
    toEvalsTo := run.toEvalsTo
    steps_le_m := run.steps_le_m.trans (loaded_cost_le F tuple base hfields) }

omit [DecidableEq Extra] in
theorem output_loaded_eq_base (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (hfields : ∀ j s, base (.field j s) = [])
    (hindex : base .index = []) (hwork : base .work = []) :
    outputTapes (SourceContextLoad.stageTapes F tuple base u) = base := by
  funext p
  cases p with
  | field j s => exact (hfields j s).symm
  | index => exact (SourceContextLoad.stageTapes_clean F tuple base u hindex hwork).1.trans hindex.symm
  | work => exact (SourceContextLoad.stageTapes_clean F tuple base u hindex hwork).2.trans hwork.symm
  | _ => exact SourceContextLoad.stageTapes_frame F tuple base u _ (by simp) (by simp) (by simp)

/-- With initially clean fields and lookup work tapes, loading followed by this
cleanup restores the caller's original frame exactly. -/
def clearLoadedToBaseInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (hfields : ∀ j s, base (.field j s) = [])
    (hindex : base .index = []) (hwork : base .work = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some main, ((), register), SourceContextLoad.stageTapes F tuple base u⟩
      (some ⟨none, ((), none), base⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) := by
  simpa only [output_loaded_eq_base F tuple base hfields hindex hwork] using
    clearLoadedInTime F tuple base hfields register

def machine (u : Nat) (Extra : Type) [DecidableEq Extra] [Fintype Extra] : FinTM2 where
  K := Tape u Extra
  k₀ := .formula
  k₁ := .formula
  Γ _ := Bool
  Λ := Label u Extra
  main := main
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program

end UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

end

end OAI
