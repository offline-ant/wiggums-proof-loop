/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Model
import OAI.Computability.UniqueGames.Reduction.BinaryLinear
import OAI.Computability.UniqueGames.Reduction.GapSemanticsLemmas

namespace OAI

section

/-! The arbitrary-real-error target and its exact passage from encoded rational
gap reductions. The same formula map and actual machine certificate are reused;
choosing smaller error tolerances does not change the computation. -/

namespace UniqueGamesTheorem.Integration.RealTarget

open UniqueGamesTheorem.Foundations
open Target

/-- A fixed-alphabet gap reduction from 3SAT, including its actual finite-machine
polynomial runtime, with the two approximation thresholds expressed over ℝ. -/
structure PolynomialGapReduction (ε δ : ℝ) where
  alphabet : Nat
  alphabetAtLeastTwo : 2 ≤ alphabet
  reduce : Formula → Instance alphabet
  computation : Turing.TM2ComputableInPolyTime Complexity.formulaEncoding.encode
    (Complexity.gameEncoding alphabet).encode reduce
  completeness : ∀ formula : Formula, formula.Satisfiable →
    ∃ labeling, 1 - ε ≤
      (countSatisfied labeling (reduce formula).constraints : ℝ) /
        (reduce formula).constraints.length
  soundness : ∀ formula : Formula, ¬ formula.Satisfiable →
    ∀ labeling, (countSatisfied labeling (reduce formula).constraints : ℝ) /
      (reduce formula).constraints.length ≤ δ


end UniqueGamesTheorem.Integration.RealTarget

end

section

/-!
The value of the actual finite Unique Games instance is its maximum satisfied
constraint fraction. Maximization ranges over every finite vertex labeling;
the denominator counts stored constraint occurrences, including repetitions.
The natural-number maximum totalizes an empty labeling type at zero. The
attainment and threshold equivalences require a positive alphabet.
-/

namespace UniqueGamesTheorem.Integration.InstanceValue

open UniqueGamesTheorem.Foundations
open Target

/-- The maximum number of satisfied occurrences among all vertex labelings. -/
def maxSatisfied {q : Nat} (g : Instance q) : Nat :=
  Finset.univ.sup (fun labeling : Fin g.vertices → Fin q =>
    countSatisfied labeling g.constraints)

/-- The usual instance value: the largest satisfied fraction of its stored
constraint list. The denominator is positive by the `Instance` invariant. -/
noncomputable def value {q : Nat} (g : Instance q) : ℝ :=
  (maxSatisfied g : ℝ) / g.constraints.length

theorem countSatisfied_le_maxSatisfied {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    countSatisfied labeling g.constraints ≤ maxSatisfied g := by
  unfold maxSatisfied
  exact Finset.le_sup
    (f := fun labeling : Fin g.vertices → Fin q => countSatisfied labeling g.constraints)
    (Finset.mem_univ labeling)

theorem maxSatisfied_le_length {q : Nat} (g : Instance q) :
    maxSatisfied g ≤ g.constraints.length := by
  apply Finset.sup_le
  intro labeling _
  exact countSatisfied_le_length labeling g.constraints

theorem maxSatisfied_attained {q : Nat} (g : Instance q) (hq : 0 < q) :
    ∃ labeling : Fin g.vertices → Fin q,
      countSatisfied labeling g.constraints = maxSatisfied g := by
  have inhabited : (Finset.univ : Finset (Fin g.vertices → Fin q)).Nonempty :=
    ⟨fun _ => ⟨0, hq⟩, Finset.mem_univ _⟩
  obtain ⟨labeling, _, hmax⟩ := Finset.exists_mem_eq_sup Finset.univ inhabited
    (fun labeling : Fin g.vertices → Fin q => countSatisfied labeling g.constraints)
  exact ⟨labeling, hmax.symm⟩

theorem value_attained {q : Nat} (g : Instance q) (hq : 0 < q) :
    ∃ labeling : Fin g.vertices → Fin q,
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length = value g := by
  obtain ⟨labeling, hlabeling⟩ := maxSatisfied_attained g hq
  exact ⟨labeling, by rw [hlabeling]; rfl⟩

theorem labeling_rate_le_value {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤ value g := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast countSatisfied_le_maxSatisfied g labeling
  · exact Nat.cast_nonneg _

/-- This value uses the same rate already defined for the encoded gap target. -/
theorem satisfactionRate_le_value {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    (GapSemantics.satisfactionRate g labeling : ℝ) ≤ value g := by
  simpa [GapSemantics.satisfactionRate] using labeling_rate_le_value g labeling


theorem value_le_one {q : Nat} (g : Instance q) : value g ≤ 1 := by
  have hlength : (0 : ℝ) < g.constraints.length := by
    exact_mod_cast g.constraintCount_positive
  rw [value, div_le_iff₀ hlength, one_mul]
  exact_mod_cast maxSatisfied_le_length g


/-- Existential real completeness is precisely a lower bound on instance value. -/
theorem exists_rate_ge_iff {q : Nat} (g : Instance q) (hq : 0 < q) (a : ℝ) :
    (∃ labeling : Fin g.vertices → Fin q,
      a ≤ (countSatisfied labeling g.constraints : ℝ) / g.constraints.length) ↔
      a ≤ value g := by
  constructor
  · rintro ⟨labeling, hlabeling⟩
    exact hlabeling.trans (labeling_rate_le_value g labeling)
  · intro hvalue
    obtain ⟨labeling, hlabeling⟩ := value_attained g hq
    exact ⟨labeling, hlabeling.symm ▸ hvalue⟩

/-- Universal real soundness is precisely an upper bound on instance value. -/
theorem forall_rate_le_iff {q : Nat} (g : Instance q) (hq : 0 < q) (b : ℝ) :
    (∀ labeling : Fin g.vertices → Fin q,
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤ b) ↔
      value g ≤ b := by
  constructor
  · intro hall
    obtain ⟨labeling, hlabeling⟩ := value_attained g hq
    exact hlabeling ▸ hall labeling
  · intro hvalue labeling
    exact (labeling_rate_le_value g labeling).trans hvalue


end UniqueGamesTheorem.Integration.InstanceValue

end

section

namespace UniqueGamesTheorem.Integration.TranslationTarget

open UniqueGamesTheorem.Foundations
open Target

/-- The full output form asserted in Theorem 1.1, including both real gaps,
the actual polynomial-time machine, and one fixed binary alphabet. -/
structure PolynomialGapReduction (ε δ : ℝ) extends RealTarget.PolynomialGapReduction ε δ where
  dimension : Nat
  coordinates : Fin alphabet ≃ BinaryLinear.Vector dimension
  translations : ∀ formula : Formula,
    IsTranslationInstance coordinates (reduce formula)


end UniqueGamesTheorem.Integration.TranslationTarget

end

section

/-! Injective vertex addresses may leave unused output vertices. The actual
instance is obtained by mapping endpoints in the original constraint list;
constraint order, multiplicity, and permutation tables are retained exactly. -/

namespace UniqueGamesTheorem.Integration.VertexEmbedding

open UniqueGamesTheorem.Foundations.Target
open GapSemantics TranslationTarget

def embedConstraint {n m q : Nat} (f : Fin n → Fin m) (c : Constraint n q) :
    Constraint m q where
  source := f c.source
  target := f c.target
  permutation := c.permutation

@[simp] theorem embedConstraint_satisfied {n m q : Nat} (f : Fin n → Fin m)
    (c : Constraint n q) (labeling : Fin m → Fin q) :
    (embedConstraint f c).satisfied labeling = c.satisfied (labeling ∘ f) := rfl

@[simp] theorem embedConstraint_permutation {n m q : Nat} (f : Fin n → Fin m)
    (c : Constraint n q) : (embedConstraint f c).permutation = c.permutation := rfl

theorem count_map {n m q : Nat} (f : Fin n → Fin m)
    (constraints : List (Constraint n q)) (labeling : Fin m → Fin q) :
    countSatisfied labeling (constraints.map (embedConstraint f)) =
      countSatisfied (labeling ∘ f) constraints := by
  rw [countSatisfied_eq_sum, countSatisfied_eq_sum, List.map_map]
  rfl

def embedInstance {q m : Nat} (g : Instance q) (f : Fin g.vertices → Fin m)
    (_hf : Function.Injective f) : Instance q where
  vertices := m
  constraints := g.constraints.map (embedConstraint f)
  nonempty h := g.nonempty (List.map_eq_nil_iff.mp h)

@[simp] theorem embedInstance_vertices {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    (embedInstance g f hf).vertices = m := rfl


/-- The extension is only used as a semantic witness, not by the instance constructor. -/
noncomputable def extendLabeling {n m q : Nat} (f : Fin n → Fin m)
    (labeling : Fin n → Fin q) (defaultLabel : Fin q) : Fin m → Fin q :=
  Function.extend f labeling (fun _ => defaultLabel)

@[simp] theorem extendLabeling_apply {n m q : Nat} (f : Fin n → Fin m)
    (hf : Function.Injective f) (labeling : Fin n → Fin q)
    (defaultLabel : Fin q) (v : Fin n) :
    extendLabeling f labeling defaultLabel (f v) = labeling v :=
  hf.extend_apply labeling (fun _ => defaultLabel) v

theorem extendLabeling_comp {n m q : Nat} (f : Fin n → Fin m)
    (hf : Function.Injective f) (labeling : Fin n → Fin q) (defaultLabel : Fin q) :
    extendLabeling f labeling defaultLabel ∘ f = labeling := by
  funext v
  exact extendLabeling_apply f hf labeling defaultLabel v


end UniqueGamesTheorem.Integration.VertexEmbedding

end

section

namespace UniqueGamesTheorem.Reduction.ActualHomogeneous

open Integration.BinaryLinear
open scoped BigOperators

abbrev E (k : Nat) := F2 × (Fin k → F2 × F2)
abbrev Ambient (k : Nat) := F2 × (Fin k → Fin 3 → F2)

variable {dimension : Nat}

def tau : E dimension →ₗ[F2] F2 := LinearMap.fst F2 _ _
def hBasis (k : Nat) : E k := (1, 0)
def firstBasis (j : Fin dimension) : E dimension := (0, Pi.single j (1, 0))
def secondBasis (j : Fin dimension) : E dimension := (0, Pi.single j (0, 1))

@[simp] theorem tau_hBasis : tau (hBasis dimension) = 1 := rfl
@[simp] theorem tau_firstBasis (j : Fin dimension) : tau (firstBasis j) = 0 := rfl
@[simp] theorem tau_secondBasis (j : Fin dimension) : tau (secondBasis j) = 0 := rfl

theorem pair_fst_ite (p : Prop) [Decidable p] (a b : F2 × F2) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split_ifs <;> rfl
theorem pair_snd_ite (p : Prop) [Decidable p] (a b : F2 × F2) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split_ifs <;> rfl

theorem coordinate_decomposition (x : E dimension) :
    x = x.1 • hBasis dimension + ∑ j : Fin dimension,
      ((x.2 j).1 • firstBasis j + (x.2 j).2 • secondBasis j) := by
  apply Prod.ext
  · simp [hBasis, firstBasis, secondBasis, Prod.fst_sum]
  · funext j
    apply Prod.ext <;>
      simp [hBasis, firstBasis, secondBasis, Pi.single_apply,
        Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, pair_fst_ite, pair_snd_ite]

theorem linearMap_expansion {R : Type*} [AddCommGroup R] [Module F2 R]
    (X : E dimension →ₗ[F2] R) (x : E dimension) :
    X x = x.1 • X (hBasis dimension) + ∑ j : Fin dimension,
      ((x.2 j).1 • X (firstBasis j) + (x.2 j).2 • X (secondBasis j)) := by
  conv_lhs => rw [coordinate_decomposition x]
  simp


def embed (b : Fin dimension → F2) : E dimension →ₗ[F2] Ambient dimension where
  toFun x := (x.1, fun j => ![(x.2 j).1, (x.2 j).2,
    b j * x.1 + (x.2 j).1 + (x.2 j).2])
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext j i
      fin_cases i <;> simp
      ring
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · funext j i
      fin_cases i <;> simp [smul_eq_mul]
      ring


theorem finrank_E (k : Nat) : Module.finrank F2 (E k) = 1 + 2 * k := by
  simp [E, Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm]


end UniqueGamesTheorem.Reduction.ActualHomogeneous

end

end OAI
