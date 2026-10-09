/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Data.List.OfFn
import OAI.Computability.UniqueGames.Games.SubdivisionTarget
import OAI.Computability.UniqueGames.Reduction.GameEncodingSizeLemmas

namespace OAI

section

/-!
Exact whole-output serialization of four-edge subdivision. The input occurrence
at index `e` produces the four adjacent rows at `4e,4e+1,4e+2,4e+3`.
The bit formula uses the same complete row output as the checked machine phase.
-/

namespace UniqueGamesTheorem.Explicit.SubdivisionEncoding

open UniqueGamesTheorem.Foundations Target Complexity
open SubdivisionTarget

theorem subdivide_constraints {q : Nat} (H : Instance q) :
    (subdivide H).constraints =
      (List.ofFn (fun e : Fin H.constraints.length =>
        MachineSubdivisionRows.rows (vertexFields H e)
          H.constraints[e].permutation)).flatten := by
  change List.ofFn _ = _
  rw [List.ofFn_mul']
  congr 1
  apply congrArg List.ofFn
  funext e
  rw [← rows_eq H e]
  apply congrArg List.ofFn
  funext i
  congr 1
  apply Fin.ext
  simp only [numericEdgeEquiv_symm_val]

theorem subdivide_constraints_flatMap {q : Nat} (H : Instance q) :
    (subdivide H).constraints = (List.finRange H.constraints.length).flatMap
      (fun e => MachineSubdivisionRows.rows (vertexFields H e)
        H.constraints[e].permutation) := by
  rw [subdivide_constraints, List.ofFn_eq_map]
  rfl

/-- Header and complete row words, in the original input occurrence order. -/
theorem subdivide_gameWords {q : Nat} (H : Instance q) :
    gameWords (subdivide H) =
      [H.vertices + 3 * H.constraints.length, q, 4 * H.constraints.length] ++
      (List.finRange H.constraints.length).flatMap (fun e =>
        (MachineSubdivisionRows.rows (vertexFields H e)
          H.constraints[e].permutation).flatMap constraintWords) := by
  change [H.vertices + 3 * H.constraints.length, q, (subdivide H).constraints.length] ++
    (subdivide H).constraints.flatMap
      (@constraintWords (H.vertices + 3 * H.constraints.length) q) = _
  rw [subdivide_length, subdivide_constraints_flatMap, List.flatMap_assoc]

private theorem encodeWords_flatMap {X : Type*} (xs : List X) (f : X → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Exact output bytes for the whole controller to emit: one header followed by
the verified four-row phase once per original occurrence. -/
theorem subdivide_gameBits {q : Nat} (H : Instance q) :
    gameBits (subdivide H) =
      encodeWords [H.vertices + 3 * H.constraints.length, q, 4 * H.constraints.length] ++
      (List.finRange H.constraints.length).flatMap (fun e =>
        MachineSubdivisionRows.rowBits (vertexFields H e) H.constraints[e].permutation) := by
  rw [gameBits, subdivide_gameWords, encodeWords_append, encodeWords_flatMap]
  rfl


end UniqueGamesTheorem.Explicit.SubdivisionEncoding

end

end OAI
