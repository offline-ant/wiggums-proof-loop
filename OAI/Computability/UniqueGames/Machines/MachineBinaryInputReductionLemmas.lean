/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas
import OAI.Computability.UniqueGames.Machines.MachineBinaryParsingLemmas
import OAI.Computability.UniqueGames.Machines.MachineBinaryRenameMachine
import OAI.Computability.UniqueGames.Machines.MachineBinaryTotalInputMachine
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Model
import OAI.Computability.UniqueGames.Reduction.RealTargetLemmas

namespace OAI

/-!
The complete ordinary-binary input bridge. Arbitrary raw input bits are first
validated and retained, or replaced by a fixed contradictory encoded formula.
The checked occurrence-index renamer then emits the inherited dense 3CNF
codec. Both stages and their physical handoff have actual polynomial-time
finite-alphabet machine certificates.

This is a bridge for the explicit ordinary binary 3SAT language. It is not the
PCP construction, a proof of that construction's runtime, or an NP-hardness
assertion about the eventual 2-to-1 target.
-/

namespace UniqueGamesTheorem.BinaryInputReduction

open Turing UniqueGamesTheorem.Foundations.Complexity

/-- The actual sequential machine handles every bitstring, including malformed
and noncanonical encodings, and outputs the fixed dense formula serialization. -/
noncomputable def computation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits BinaryLanguage.totalRename := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits
    (fun input => BinaryOccurrenceRename.renamed (BinaryLanguage.totalParsed input))
  exact MachineSequential.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime
    BinaryTotalInputMachine.computation_finiteAlphabet
    BinaryRenameMachine.computation_finiteAlphabet

/-- Satisfiability equivalence plus an actual raw-bit machine; no external
verifier, parsing-time assertion, or recoding hypothesis is an input. -/
noncomputable def reduction : CookLevin.PolynomialThreeSATReduction BinaryLanguage.language where
  reduce := BinaryLanguage.totalRename
  computation := computation
  correct input := (BinaryLanguage.totalRename_satisfiable_iff input).symm


end UniqueGamesTheorem.BinaryInputReduction

namespace UniqueGamesTheorem.Explicit.MachineOutputContract

open UniqueGamesTheorem.Foundations
open Target
open scoped BigOperators

/-! A canonical orientation from the false side to the true side. Injectivity
is on occurrence indices, so two distinct list entries cannot be parallel even
when their constraint tables are different. -/

/-- The full forward and inverse tables already prove the permutation laws. -/
def permutationEquiv {q : Nat} (table : PermutationTable q) : Equiv.Perm (Fin q) where
  toFun label := table.images[label]
  invFun label := table.inverseImages[label]
  left_inv := table.leftInverse
  right_inv := table.rightInverse

namespace SimpleBipartite

variable {q : Nat} {game : Instance q} (presentation : SimpleBipartite game)

include presentation in
theorem no_loops (i : Fin game.constraints.length) :
    game.constraints[i].source ≠ game.constraints[i].target := by
  intro same
  have sides := congrArg presentation.side same
  rw [presentation.sourceSide, presentation.targetSide] at sides
  cases sides


/-- The list presentation yields exactly the bipartite occurrence abstraction
used by the subdivision proof, without quotienting or discarding occurrences. -/
def toBipartiteGame : BipartiteGame
    {v : Fin game.vertices // presentation.side v = false}
    {v : Fin game.vertices // presentation.side v = true}
    (Fin game.constraints.length) (Fin q) where
  left i := ⟨game.constraints[i].source, presentation.sourceSide i⟩
  right i := ⟨game.constraints[i].target, presentation.targetSide i⟩
  permutation i := permutationEquiv game.constraints[i].permutation
  simple := by
    intro i j same
    apply presentation.endpoints_injective
    apply Prod.ext
    · exact congrArg Subtype.val (congrArg Prod.fst same)
    · exact congrArg Subtype.val (congrArg Prod.snd same)


/-- Two independently chosen side labelings give one total labeling because
every vertex has exactly one Boolean side. Isolated vertices cause no exception. -/
def mergeLabelings
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q) :
    Fin game.vertices → Fin q := fun v =>
  if h : presentation.side v = false then left ⟨v, h⟩
  else right ⟨v, by cases hs : presentation.side v <;> simp_all⟩

@[simp] theorem mergeLabelings_left
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q)
    (v : {v : Fin game.vertices // presentation.side v = false}) :
    presentation.mergeLabelings left right v.val = left v := by
  simp [mergeLabelings, v.property]

@[simp] theorem mergeLabelings_right
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q)
    (v : {v : Fin game.vertices // presentation.side v = true}) :
    presentation.mergeLabelings left right v.val = right v := by
  simp [mergeLabelings, v.property]

theorem toBipartiteGame_count (labeling : Fin game.vertices → Fin q) :
    presentation.toBipartiteGame.satisfiedCount
      (fun v => labeling v.val) (fun v => labeling v.val) =
      countSatisfied labeling game.constraints := by
  have count := Integration.GapSemantics.countSatisfied_ofFn labeling
    (fun i : Fin game.constraints.length => game.constraints[i])
  simp only [Fin.getElem_fin, List.ofFn_getElem] at count
  rw [count]
  unfold BipartiteGame.satisfiedCount
  apply Finset.sum_congr rfl
  intro e _
  simp [toBipartiteGame, permutationEquiv, Constraint.satisfied]
  rfl

theorem toBipartiteGame_count_merge
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q) :
    presentation.toBipartiteGame.satisfiedCount left right =
      countSatisfied (presentation.mergeLabelings left right) game.constraints := by
  simpa only [mergeLabelings_left, mergeLabelings_right] using
    presentation.toBipartiteGame_count (presentation.mergeLabelings left right)

theorem toBipartiteGame_maxSatisfied :
    presentation.toBipartiteGame.maxSatisfied =
      Integration.InstanceValue.maxSatisfied game := by
  classical
  apply Nat.le_antisymm
  · unfold BipartiteGame.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [presentation.toBipartiteGame_count_merge labeling.1 labeling.2]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied _ _
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [← presentation.toBipartiteGame_count labeling]
    exact BipartiteGame.satisfiedCount_le_maxSatisfied _ _ _

/-- The abstract bipartite game and the actual serialized list instance have
exactly the same value, including the same denominator of edge occurrences. -/
theorem toBipartiteGame_value :
    presentation.toBipartiteGame.value = Integration.InstanceValue.value game := by
  unfold BipartiteGame.value Integration.InstanceValue.value
  rw [presentation.toBipartiteGame_maxSatisfied]
  simp

end SimpleBipartite

/-! Every parameter, coordinate identification, program, and polynomial is
fixed before the input quantifier. The identity input encoding measures runtime
in the original raw bit length, including sparse binary variable names. -/

namespace BinaryGapReduction

variable {ε δ : ℝ} (reduction : BinaryGapReduction ε δ)


theorem no_loops (input : List Bool)
    (i : Fin (reduction.construct input).constraints.length) :
    (reduction.construct input).constraints[i].source ≠
      (reduction.construct input).constraints[i].target :=
  (reduction.simpleBipartite input).no_loops i


end BinaryGapReduction
end UniqueGamesTheorem.Explicit.MachineOutputContract

end OAI
