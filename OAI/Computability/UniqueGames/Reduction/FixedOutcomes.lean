/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Reduction.ExplicitLemmas
import OAI.Computability.UniqueGames.Reduction.OutputTranslationsLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.FixedOutcomes

open Integration.BinaryLinear ActualHomogeneous ActualSource
open ActualEnumeration UniqueGamesTheorem.Reduction.Explicit

variable {N : Type*}

abbrev Parameter (k s d : Nat) (N : Type*) :=
  (E k →ₗ[F2] ActualEnumeration.Ambient s d) × (N × (E k →ₗ[F2] F2))

def occurrenceTuples (m k : Nat) : List (Fin k → Fin m) :=
  functions (List.finRange m) k

/-- Ambient linear map, noise occurrence index, scalar linear functional,
in exactly the original nested enumeration order. -/
def fixedParams (k s d : Nat) (indices : List N) : List (Parameter k s d N) :=
  pairs (allLinearMaps k _ (ambientVectors s d))
    (pairs indices (allLinearMaps k F2 [0, 1]))

def assemble {m k s d : Nat} (U : Fin k → Fin m) (p : Parameter k s d N) :
    Query m k s d × (N × (E k →ₗ[F2] F2)) :=
  ((U, p.1), p.2)


private theorem pairs_associate {Left Middle Right : Type*}
    (xs : List Left) (ys : List Middle) (zs : List Right) :
    pairs (pairs xs ys) zs =
      xs.flatMap (fun x => (pairs ys zs).map (fun p => ((x, p.1), p.2))) := by
  simp only [pairs, List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

theorem indexedOutcomes_factor (m k s d : Nat) (indices : List N) :
    ActualEnumeration.indexedOutcomes m k s d indices =
      (occurrenceTuples m k).flatMap (fun U => (fixedParams k s d indices).map (assemble U)) := by
  exact pairs_associate (functions (List.finRange m) k)
    (allLinearMaps k _ (ambientVectors s d))
    (pairs indices (allLinearMaps k F2 [0, 1]))


theorem fixedParams_length (k s d : Nat) (indices : List N) :
    (fixedParams k s d indices).length = 2^((2*k+1)*(s+d+1)) * indices.length := by
  simp only [fixedParams, length_pairs, length_allLinearMaps, length_ambientVectors,
    List.length_cons, List.length_nil, ← pow_mul]
  change 2^((s+d)*(2*k+1)) * (indices.length * 2^(2*k+1)) =
    2^((2*k+1)*(s+d+1)) * indices.length
  rw [show (2*k+1)*(s+d+1) = (s+d)*(2*k+1)+(2*k+1) by ring, pow_add]
  ring


def tableParams (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    List (Parameter k s d (Fin T.vectors.length)) :=
  fixedParams k s d (List.finRange T.vectors.length)

theorem tableParams_length (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    (tableParams k T).length = 2^((2*k+1)*(s+d+1)) * T.vectors.length := by
  simp only [tableParams, fixedParams_length, List.length_finRange]


end UniqueGamesTheorem.Reduction.FixedOutcomes

end

end OAI
