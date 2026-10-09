/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.PCP.AmplificationIteration
import OAI.Computability.UniqueGames.PCP.FinalTableFormula
import OAI.Computability.UniqueGames.PCP.RawInitialTablesLemmas

namespace OAI

section

/-! Iteration of the concrete stored-table round, with the original formula's
actual initial graph size controlling the number of rounds. -/

namespace UniqueGamesTheorem.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def run (H : BaseTable) : Nat → Input → Input := AmplificationIteration.run (step H)

/-- The same data computation on all validated tables; positivity is an invariant,
and is erased from the runtime path. -/
def runTables (H : BaseTable) : Nat → GraphTables.Table → GraphTables.Table :=
  AmplificationIteration.run (build H)

theorem run_val (H : BaseTable) (n : Nat) (input : Input) :
    (run H n input).val = runTables H n input.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change build H (run H n input).val = build H (runTables H n input.val)
      rw [ih]

def iterationCount (F : Formula) : Nat := AmplificationIteration.rounds (size (initial F))

def output (H : BaseTable) (F : Formula) : Input := run H (iterationCount F) (initial F)

def outputTable (H : BaseTable) (F : Formula) : GraphTables.Table :=
  runTables H (iterationCount F) (RawInitialTables.table F)

theorem output_val (H : BaseTable) (F : Formula) : (output H F).val = outputTable H F :=
  run_val H (iterationCount F) (initial F)

def gapMap (H : BaseTable) (F : Formula) : Formula := FinalTableFormula.output (outputTable H F)


theorem run_completeness (H : BaseTable) (n : Nat) (input : Input)
    (sat : Satisfiable input) : Satisfiable (run H n input) :=
  AmplificationIteration.run_preserves (step H) Satisfiable (step_completeness H) n input sat

theorem output_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    Satisfiable (output H F) :=
  run_completeness H _ _ ((initial_satisfiable_iff F).mpr sat)

theorem gapMap_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    (gapMap H F).Satisfiable := by
  apply (FinalTableFormula.satisfiable_iff (outputTable H F)).mpr
  rw [← output_val]
  exact output_completeness H F sat

theorem output_darts_positive (H : BaseTable) (F : Formula) : 0 < (outputTable H F).darts := by
  rw [← output_val]
  exact (output H F).property

theorem gapMap_nonempty (H : BaseTable) (F : Formula) : (gapMap H F).clauses ≠ [] :=
  FinalTableFormula.nonempty (outputTable H F) (output_darts_positive H F)


end UniqueGamesTheorem.Foundations.PCP.TableIteration

end

end OAI
