/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Reduction.ActualGame
import OAI.Computability.UniqueGames.Reduction.GapSemanticsLemmas
import OAI.Computability.UniqueGames.Reduction.NoiseEnumerationLemmas

namespace OAI

namespace UniqueGamesTheorem.Integration.TableReduction

open BinaryLinear NoiseTables UniqueGamesTheorem.Reduction.ActualSource
open UniqueGamesTheorem.Reduction.ActualGame UniqueGamesTheorem.Foundations.Target

variable {s d : Nat}

def tableEnumeration (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) : NoiseEnumeration (T.gadget f hf) where
  indices := List.finRange T.vectors.length
  nodup := List.nodup_finRange _
  complete i := List.mem_finRange i

/-- The projection is used only to fill an erased witness field. It is never
used when generating constraints or evaluating their permutation tables. -/
def tableSkeleton (T : Table s d) : SplitGadget s d :=
  T.gadget Prod.fst (fun _ _ => rfl)


end UniqueGamesTheorem.Integration.TableReduction

end OAI
