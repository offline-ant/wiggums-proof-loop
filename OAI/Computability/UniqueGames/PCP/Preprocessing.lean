/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.PCP.OverlayLemmas

namespace OAI.UniqueGamesTheorem.Foundations.PCP.Preprocessing

/-! Fixed degree and linear size loss of the executable preprocessing tables.
The tables and their proofs live in `PreprocessingTablesLemmas`; there is no
second, abstract graph preprocessing construction. -/

def degree : Nat := 2 * (2 * Expanders.baseDegree ^ 2 + 1)
def sizeFactor : Nat := ExpanderFamily.growth ^ 2 * degree

theorem degree_positive : 0 < degree := by
  unfold degree
  omega

theorem sizeFactor_positive : 0 < sizeFactor := by
  have hg : 0 < ExpanderFamily.growth :=
    Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
  exact Nat.mul_pos (Nat.pow_pos hg) degree_positive

end OAI.UniqueGamesTheorem.Foundations.PCP.Preprocessing
