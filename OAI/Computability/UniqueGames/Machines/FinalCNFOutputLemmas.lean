/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Machines.FinalCNFLoopLemmas
import OAI.Computability.UniqueGames.Machines.FinalCNFMachineLemmas
import OAI.Computability.UniqueGames.Machines.FinalCNFRowPlanLemmas
import OAI.Computability.UniqueGames.Machines.FinalCNFStream
import OAI.Computability.UniqueGames.Machines.MachineCanonicalOutputLemmas
import OAI.Computability.UniqueGames.PCP.FinalTableFormula

namespace OAI


/-!
The final machine's complete output stream is the exact serialization of its
actual formula. This identity includes the two size fields, every clause and
literal field, and all unary delimiters. No desired output equality is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP

section Alphabet

open PCP.AlphabetTable


def formulaHeader (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts]

theorem formulaHeader_eq (table : GraphTables.Table) :
    formulaHeader table = encodeWords [(FinalTableFormula.output table).variables,
      (FinalTableFormula.output table).clauses.length] := by
  simp only [formulaHeader, FinalTableFormula.variable_count, FinalTableFormula.clause_count,
    Nat.mul_comm]


theorem outputStream_eq_clauseBits (table : GraphTables.Table) :
    outputStream rowPlan table (List.finRange table.darts) =
      encodeWords ((FinalTableFormula.output table).clauses.flatMap Complexity.clauseWords) := by
  calc
    _ = (List.finRange table.darts).flatMap (fun e =>
          encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) := by
      apply List.flatMap_congr
      intro e he
      exact rowPlan_bits table e
    _ = encodeWords ((List.finRange table.darts).flatMap (fun e =>
          (VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) :=
      (encodeWords_flatMap _ _).symm
    _ = _ := by
      congr 1
      rw [← List.flatMap_assoc]
      rfl

theorem header_append_outputStream (table : GraphTables.Table) :
    formulaHeader table ++ outputStream rowPlan table (List.finRange table.darts) =
      formulaBits (FinalTableFormula.output table) := by
  rw [formulaHeader_eq, outputStream_eq_clauseBits]
  exact (encodeWords_append _ _).symm


end Alphabet

noncomputable def rowTimePolynomial : Polynomial Nat :=
  Polynomial.C 860160 * (Polynomial.C 3 * (Polynomial.X + Polynomial.C 1) + Polynomial.C 3) +
    Polynomial.C 12 * Polynomial.X + Polynomial.C 15

theorem rowTimePolynomial_eval (N : Nat) :
    rowTimePolynomial.eval N = rowTime rowPlan N := by
  simp only [rowTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTime, rowPlan_length]


/-- Header, at most `N` rows with guards, and the final output reversal. -/
noncomputable def phaseTimePolynomial : Polynomial Nat :=
  headerTimePolynomial +
    (Polynomial.X * (rowTimePolynomial + Polynomial.C 1) + Polynomial.C 1) +
    (FinalTableFormula.sizePolynomial + Polynomial.C 1)

theorem phaseTimePolynomial_eval (N : Nat) :
    phaseTimePolynomial.eval N =
      headerTimePolynomial.eval N + (N * (rowTime rowPlan N + 1) + 1) +
        (FinalTableFormula.sizePolynomial.eval N + 1) := by
  simp only [phaseTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTimePolynomial_eval]


theorem phaseTime_le {N rows outputLength : Nat} (rowBound : rows ≤ N)
    (outputBound : outputLength ≤ FinalTableFormula.sizePolynomial.eval N) :
    headerTimePolynomial.eval N + (rows * (rowTime rowPlan N + 1) + 1) +
      (outputLength + 1) ≤ phaseTimePolynomial.eval N := by
  have hrows := Nat.mul_le_mul_right (rowTime rowPlan N + 1) rowBound
  rw [phaseTimePolynomial_eval]
  omega

/-- The bound specialized to the actual table and actual formula serialization. -/
theorem table_phaseTime_le (table : GraphTables.Table) :
    headerTimePolynomial.eval (GraphTables.tableBits table).length +
      (table.darts * (rowTime rowPlan (GraphTables.tableBits table).length + 1) + 1) +
      ((formulaBits (FinalTableFormula.output table)).length + 1) ≤
        phaseTimePolynomial.eval (GraphTables.tableBits table).length :=
  phaseTime_le (GraphTables.darts_le_tableBits_length table)
    (FinalTableFormula.formulaBits_length_le_polynomial table)

/-!
The complete polynomial-time machine certificate for converting a validated
64-label graph table into its actual 3CNF formula. The proof composes the real
input parser, all row executions, output reversal, and private-tape cleanup.
-/

open Turing


theorem emittedBytes_eq_formulaBits (table : GraphTables.Table) :
    emittedBytes rowPlan table = formulaBits (FinalTableFormula.output table) :=
  header_append_outputStream table

theorem rawBudget_le_phaseTime (table : GraphTables.Table) :
    rawBudget rowPlan table ≤ phaseTimePolynomial.eval (GraphTables.tableBits table).length := by
  unfold rawBudget
  rw [emittedBytes_eq_formulaBits]
  simpa only [Nat.add_assoc] using table_phaseTime_le table

/-- The existing raw program, packaged for the shared canonical-output wrapper. -/
def rawProgram : MachineCanonicalOutput.Program Tape
    (Label headerPlan.length rowPlan.length) (State Unit) where
  input := .input
  output := .output
  main := .copyFirst
  initial := (machine headerPlan rowPlan).initialState
  code := program headerPlan rowPlan

/-- Precisely the twelve non-output tapes, including input and archive. -/
def privateTapes : List Tape :=
  [.input, .accumulator, .scratch, .vertices, .darts, .tail, .head,
    .rowIndex, .archive, .reverseIndex, .scanWork, .indexWork]

theorem privateTapes_complete (tape : Tape) : tape ∈ privateTapes ↔ tape ≠ .output := by
  cases tape <;> simp [privateTapes]

/-- A concrete finite machine computes the complete CNF serialization from
the exact unary graph-table serialization, with a proved polynomial bound. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits formulaBits FinalTableFormula.output :=
  MachineCanonicalOutput.computableInPolyTime rawProgram privateTapes privateTapes_complete
    GraphTables.tableBits formulaBits FinalTableFormula.output phaseTimePolynomial fun table =>
      let raw := rawRun rowPlan table
      { state := ((raw.finalAmbient, ()), none)
        tapes := raw.finalTapes
        execution := {
          toEvalsTo := raw.execution.toEvalsTo
          steps_le_m := raw.execution.steps_le_m.trans (rawBudget_le_phaseTime table) }
        output_eq := raw.output.trans (emittedBytes_eq_formulaBits table) }

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
