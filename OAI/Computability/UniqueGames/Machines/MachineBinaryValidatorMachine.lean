/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Tactic.DeriveFintype
import OAI.Computability.UniqueGames.Machines.MachineBinaryParsingLemmas
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas

namespace OAI

/-!
A finite-state validator for the concrete ordinary-binary formula encoding.
It checks clause and literal framing, canonical name payloads, and the unique
terminal formula marker. The last-digit register starts at true for each name,
so the empty payload is accepted as zero while a nonempty payload must end in
one. Every bit following the terminal formula marker causes rejection.
-/

namespace UniqueGamesTheorem.BinaryValidatorMachine

open BinaryEncoding BinaryFormula

inductive Mode
  | clause
  | sign (slot : Fin 3)
  | name (slot : Fin 3) (last : Bool)
  | digit (slot : Fin 3)
  | done
  | reject
  deriving DecidableEq, Fintype

def afterName (slot : Fin 3) : Mode :=
  if slot = 0 then .sign 1 else if slot = 1 then .sign 2 else .clause

def nextMode : Mode → Bool → Mode
  | .clause, true => .sign 0
  | .clause, false => .done
  | .sign slot, _ => .name slot true
  | .name slot _, true => .digit slot
  | .name slot last, false => if last then afterName slot else .reject
  | .digit slot, bit => .name slot bit
  | .done, _ => .reject
  | .reject, _ => .reject

def run : Mode → List Bool → Mode
  | mode, [] => mode
  | mode, bit :: rest => run (nextMode mode bit) rest

@[simp] theorem run_reject (input : List Bool) : run .reject input = .reject := by
  induction input with
  | nil => rfl
  | cons bit input ih => simpa only [run, nextMode] using ih

theorem run_done_iff (input : List Bool) : run .done input = .done ↔ input = [] := by
  cases input with
  | nil => simp [run]
  | cons bit rest => simp [run, nextMode]

private theorem finalDigit_true_iff (bits : List Bool) :
    BinaryNameMachine.finalDigit bits (some true) = some true ↔
      BinaryNameMachine.canonical bits = true := by
  cases bits with
  | nil => simp [BinaryNameMachine.finalDigit, BinaryNameMachine.canonical]
  | cons bit bits =>
      simp only [BinaryNameMachine.finalDigit, BinaryNameMachine.canonical]
      induction bits generalizing bit with
      | nil => simp [BinaryNameMachine.finalDigit]
      | cons next bits ih => exact ih next

/-- A valid framed payload advances exactly to the next literal or clause. -/
theorem run_frame (slot : Fin 3) (bits rest : List Bool) (last : Bool)
    (valid : BinaryNameMachine.finalDigit bits (some last) = some true) :
    run (.name slot last) (frame bits ++ rest) = run (afterName slot) rest := by
  induction bits generalizing last with
  | nil =>
      have hlast : last = true := by simpa [BinaryNameMachine.finalDigit] using valid
      subst last
      simp [frame, run, nextMode]
  | cons bit bits ih =>
      have hvalid : BinaryNameMachine.finalDigit bits (some bit) = some true := valid
      simpa only [frame, List.cons_append, run, nextMode] using ih bit hvalid

theorem run_name (slot : Fin 3) (name : Nat) (rest : List Bool) :
    run (.name slot true) (nameBits name ++ rest) = run (afterName slot) rest := by
  apply run_frame
  exact (finalDigit_true_iff name.bits).mpr (BinaryParsing.canonical_nat_bits name)

theorem run_literal (slot : Fin 3) (literal : Literal) (rest : List Bool) :
    run (.sign slot) (literalBits literal ++ rest) = run (afterName slot) rest := by
  simpa only [literalBits, List.cons_append, run, nextMode] using
    run_name slot literal.name rest

theorem run_clause (clause : Clause) (rest : List Bool) :
    run (.sign 0) (clauseBits clause ++ rest) = run .clause rest := by
  simp [clauseBits, List.append_assoc, run_literal, afterName]

theorem run_clauses (clauses : List Clause) : run .clause (clausesBits clauses) = .done := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      change run (.sign 0) (clauseBits clause ++ clausesBits clauses) = .done
      rw [run_clause, ih]

theorem run_formula (formula : Formula) : run .clause (formulaBits formula) = .done :=
  run_clauses formula.clauses

/-- Any accepting name phase consumes a complete frame with a valid last digit. -/
theorem frame_inverse (slot : Fin 3) (last : Bool) (input : List Bool)
    (accepted : run (.name slot last) input = .done) :
    ∃ bits rest, input = frame bits ++ rest ∧
      BinaryNameMachine.finalDigit bits (some last) = some true ∧
      run (afterName slot) rest = .done := by
  induction input using List.twoStepInduction generalizing last with
  | nil => simp [run] at accepted
  | singleton flag =>
      cases flag with
      | false =>
          cases last with
          | false => simp [run, nextMode] at accepted
          | true =>
              exact ⟨[], [], rfl, rfl, by simpa [run, nextMode] using accepted⟩
      | true => simp [run, nextMode] at accepted
  | cons_cons flag bit input ih _ =>
      cases flag with
      | false =>
          cases last with
          | false => simp [run, nextMode] at accepted
          | true =>
              exact ⟨[], bit :: input, rfl, rfl,
                by simpa [run, nextMode] using accepted⟩
      | true =>
          have haccepted : run (.name slot bit) input = .done := by
            simpa only [run, nextMode] using accepted
          obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := ih bit haccepted
          refine ⟨bit :: bits, rest, ?_, hvalid, hrest⟩
          simp [frame, hinput]

theorem name_inverse (slot : Fin 3) (input : List Bool)
    (accepted : run (.name slot true) input = .done) :
    ∃ name rest, input = nameBits name ++ rest ∧ run (afterName slot) rest = .done := by
  obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := frame_inverse slot true input accepted
  have hcanonical := (finalDigit_true_iff bits).mp hvalid
  have hbits := (BinaryParsing.canonical_iff bits).mp hcanonical
  refine ⟨bitsValue bits, rest, ?_, hrest⟩
  simpa only [nameBits, hbits] using hinput

theorem literal_inverse (slot : Fin 3) (input : List Bool)
    (accepted : run (.sign slot) input = .done) :
    ∃ literal rest, input = literalBits literal ++ rest ∧ run (afterName slot) rest = .done := by
  cases input with
  | nil => simp [run] at accepted
  | cons sign input =>
      have haccepted : run (.name slot true) input = .done := accepted
      obtain ⟨name, rest, hinput, hrest⟩ := name_inverse slot input haccepted
      refine ⟨⟨name, sign⟩, rest, ?_, hrest⟩
      simp [literalBits, hinput]

theorem clause_inverse (input : List Bool) (accepted : run (.sign 0) input = .done) :
    ∃ clause rest, input = clauseBits clause ++ rest ∧ run .clause rest = .done := by
  obtain ⟨a, afterA, hA, acceptedA⟩ := literal_inverse 0 input accepted
  have hacceptedA : run (.sign 1) afterA = .done := by
    simpa [afterName] using acceptedA
  obtain ⟨b, afterB, hB, acceptedB⟩ := literal_inverse 1 afterA hacceptedA
  have hacceptedB : run (.sign 2) afterB = .done := by
    simpa [afterName] using acceptedB
  obtain ⟨c, rest, hC, acceptedC⟩ := literal_inverse 2 afterB hacceptedB
  have hrest : run .clause rest = .done := by simpa [afterName] using acceptedC
  refine ⟨#v[a, b, c], rest, ?_, hrest⟩
  simp [clauseBits, hA, hB, hC, List.append_assoc]

private theorem clauses_inverse (input : List Bool)
    (accepted : run .clause input = .done) :
    ∃ clauses, input = clausesBits clauses := by
  induction input using (measure (List.length (α := Bool))).wf.induction with
  | h input ih =>
      cases input with
      | nil => simp [run] at accepted
      | cons flag input =>
          cases flag with
          | false =>
              have hempty := (run_done_iff input).mp accepted
              subst input
              exact ⟨[], rfl⟩
          | true =>
              obtain ⟨clause, rest, hinput, hrest⟩ := clause_inverse input accepted
              have shorter : rest.length < (true :: input).length := by
                rw [List.length_cons, hinput, List.length_append]
                omega
              obtain ⟨clauses, hclauses⟩ := ih rest shorter hrest
              exact ⟨clause :: clauses, by simp [clausesBits, hinput, hclauses]⟩

/-- Exact language recognition, including rejection of incomplete, padded,
or trailing input. -/
theorem run_clause_iff (input : List Bool) :
    run .clause input = .done ↔ ∃ formula, input = formulaBits formula := by
  constructor
  · intro accepted
    obtain ⟨clauses, hclauses⟩ := clauses_inverse input accepted
    exact ⟨⟨clauses⟩, hclauses⟩
  · rintro ⟨formula, rfl⟩
    exact run_formula formula


end UniqueGamesTheorem.BinaryValidatorMachine

end OAI
