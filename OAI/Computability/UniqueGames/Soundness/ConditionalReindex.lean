/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Soundness.ZeroInformationLemmas

namespace OAI

section

/-! Explicit hidden-coordinate enumeration in the actual conditional law. -/

namespace UniqueGamesTheorem.Soundness.ConditionalIncidences
open scoped BigOperators

def coordinateReindex {A B X : Type} (e : B ≃ A) : (A → X) ≃ (B → X) :=
  e.symm.arrowCongr (Equiv.refl X)


end UniqueGamesTheorem.Soundness.ConditionalIncidences

end

end OAI
