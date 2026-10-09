/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Repetition.AnalyticRateLemmas
import OAI.Computability.UniqueGames.Repetition.CollisionLemmas
import OAI.Computability.UniqueGames.Repetition.RoundingKernel

namespace OAI

section

/-! Exact tensor identities for normalized finite projection kernels. -/

namespace UniqueGamesTheorem.Repetition
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ I : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂] [Fintype I]

theorem apply_nonnegative (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (hf : ∀ x a, 0 ≤ f x a) (y : Q₂) (b : A₂) :
    0 ≤ K.apply f y b := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg ((K.inner y).nonnegative x)
  apply Finset.sum_nonneg
  intro a _
  split
  · exact hf x a
  · exact le_rfl

theorem apply_sum (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : I → Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => ∑ i, f i x a) y b = ∑ i, K.apply (f i) y b := by
  simp_rw [apply_eq_linearCoefficient_sum, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]

theorem apply_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (r : ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => r * f x a) y b = r * K.apply f y b := by
  simp only [apply_eq_linearCoefficient_sum, Finset.mul_sum, mul_left_comm]

/-- Independent product of the outer and conditional laws. -/
def product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) :
    ProjectionKernel (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂) where
  outer := K.outer.product H.outer
  inner q := (K.inner q.1).product (H.inner q.2)
  accepts x y a b := K.accepts x.1 y.1 a.1 b.1 && H.accepts x.2 y.2 a.2 b.2
  projection x y a b b' hb hb' := by
    have h₁ := Bool.and_eq_true_iff.mp hb
    have h₂ := Bool.and_eq_true_iff.mp hb'
    exact Prod.ext (K.projection _ _ _ _ _ h₁.1 h₂.1)
      (H.projection _ _ _ _ _ h₁.2 h₂.2)

/-- Arbitrary product inputs factor through the second game operator. -/
theorem apply_product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (f : (Q₁ × R₁) → (A₁ × B₁) → ℝ)
    (y : Q₂) (z : R₂) (b : A₂) (c : B₂) :
    (K.product H).apply f (y,z) (b,c) =
      K.apply (fun x a => H.apply (fun u d => f (x,u) (a,d)) z c) y b := by
  simp only [apply_eq_linearCoefficient_sum, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  by_cases hk : K.accepts x y a b = true <;>
    by_cases hh : H.accepts u z d c = true <;>
    simp [linearCoefficient, product, FiniteDistribution.product, hk, hh, mul_assoc]


end ProjectionKernel
end
end UniqueGamesTheorem.Repetition

end

section

/-!
Independent repetitions of the actual conditional projection kernel. The
resulting game has precisely the original game's product question law. A
successor tuple is a reindexed independent product, so collision bounds on the
product apply to unrestricted strategies on whole tuples.
-/

namespace UniqueGamesTheorem.Repetition.ProjectionKernel

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def repetition (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    ProjectionKernel (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) := by
  classical
  exact
    { outer := K.outer.iid n
      inner := fun y => FiniteDistribution.table (fun i : Fin n => K.inner (y i))
      accepts := fun x y a b => decide (∀ i, K.accepts (x i) (y i) (a i) (b i) = true)
      projection := by
        intro x y a b b' hb hb'
        simp only [decide_eq_true_eq] at hb hb'
        funext i
        exact K.projection _ _ _ _ _ (hb i) (hb' i) }


@[simp] theorem toGame_repetition (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    (K.repetition n).toGame = K.toGame.repetition n := by
  classical
  have hq : (K.repetition n).toGame.questions = (K.toGame.repetition n).questions := by
    apply FiniteDistribution.eq_of_weight_eq
    intro q
    change ((∏ i, K.outer.weight (q.2 i)) *
        (∏ i, (K.inner (q.2 i)).weight (q.1 i))) =
      ∏ i, K.outer.weight (q.2 i) * (K.inner (q.2 i)).weight (q.1 i)
    exact Finset.prod_mul_distrib.symm
  change Game.mk (K.repetition n).toGame.questions
      (fun (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) =>
        decide (∀ i, K.accepts (x i) (y i) (a i) (b i) = true)) =
    Game.mk (K.toGame.repetition n).questions
      (fun (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) =>
        decide (∀ i, K.accepts (x i) (y i) (a i) (b i) = true))
  rw [hq]

theorem eq_of_data_eq {K H : ProjectionKernel Q₁ Q₂ A₁ A₂}
    (houter : K.outer = H.outer) (hinner : K.inner = H.inner)
    (haccepts : K.accepts = H.accepts) : K = H := by
  cases K
  cases H
  cases houter
  cases hinner
  cases haccepts
  rfl

/-- Separate the first coordinate without restricting answer dependence on
any coordinate of the complete local question tuple. -/
theorem repetition_succ (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    K.repetition (n + 1) =
      (K.product (K.repetition n)).reindex
        (Fin.consEquiv (fun _ : Fin (n + 1) => Q₁))
        (Fin.consEquiv (fun _ : Fin (n + 1) => Q₂))
        (Fin.consEquiv (fun _ : Fin (n + 1) => A₁))
        (Fin.consEquiv (fun _ : Fin (n + 1) => A₂)) := by
  classical
  apply eq_of_data_eq
  · apply FiniteDistribution.eq_of_weight_eq
    intro y
    change (∏ i : Fin (n + 1), K.outer.weight (y i)) =
      K.outer.weight (y 0) * ∏ i : Fin n, K.outer.weight (y i.succ)
    exact Fin.prod_univ_succ _
  · funext y
    apply FiniteDistribution.eq_of_weight_eq
    intro x
    change (∏ i : Fin (n + 1), (K.inner (y i)).weight (x i)) =
      (K.inner (y 0)).weight (x 0) *
        ∏ i : Fin n, (K.inner (y i.succ)).weight (x i.succ)
    exact Fin.prod_univ_succ _
  · funext x y a b
    apply Bool.eq_iff_iff.mpr
    change (decide (∀ i : Fin (n + 1), K.accepts (x i) (y i) (a i) (b i) = true) = true) ↔
      (K.accepts (x 0) (y 0) (a 0) (b 0) &&
        decide (∀ i : Fin n, K.accepts (x i.succ) (y i.succ) (a i.succ) (b i.succ) = true)) = true
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩
    · rintro ⟨hzero, hsucc⟩ i
      exact Fin.cases hzero hsucc i

theorem collisionValue_repetition_succ [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    (K.repetition (n + 1)).collisionValue =
      (K.product (K.repetition n)).collisionValue := by
  rw [repetition_succ, collisionValue_reindex]

theorem collisionValue_repetition_zero_le_one [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    (K.repetition 0).collisionValue ≤ 1 :=
  (K.repetition 0).collisionValue_le_one

end
end UniqueGamesTheorem.Repetition.ProjectionKernel

end

section

/-!
The tensor-domination reduction before the Dinur--Steurer rounding theorem.
Every deterministic strategy for the product gives a nonnegative vector table
for the first kernel. Its energy is exactly the product collision energy, and
each input-question mass is bounded by the second kernel's collision value.
-/

namespace UniqueGamesTheorem.Repetition
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]

/-- Apply the second game to a fixed first question and first answer. The
square-root factor changes its weighted output space into counting measure. -/
def tensorSlice (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁))
    (ω : R₂ × B₂) (x : Q₁) (a : A₁) : ℝ :=
  Real.sqrt (H.outer.weight ω.1) *
    H.apply (fun u d => assignment labels (x,u) (a,d)) ω.1 ω.2

omit [Fintype Q₁] [Fintype A₁] in
theorem tensorSlice_nonnegative (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (ω : R₂ × B₂) (x : Q₁) (a : A₁) :
    0 ≤ H.tensorSlice labels ω x a := by
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply H.apply_nonnegative
  intro u d
  unfold assignment
  split
  · exact zero_le_one
  · exact le_rfl

omit [Fintype Q₁] [Fintype R₁] [Fintype B₁] in
/-- Marginalizing the first label of a deterministic product strategy leaves
the deterministic second-label strategy. -/
theorem sum_assignment_product (labels : (Q₁ × R₁) → (A₁ × B₁))
    (x : Q₁) (u : R₁) (d : B₁) :
    (∑ a, assignment labels (x,u) (a,d)) =
      assignment (fun r => (labels (x,r)).2) u d := by
  classical
  by_cases h : (labels (x,u)).2 = d <;> simp [assignment, Prod.ext_iff, h]

omit [Fintype Q₁] in
theorem tensorSlice_label_mass (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (ω : R₂ × B₂) (x : Q₁) :
    (∑ a, H.tensorSlice labels ω x a) =
      Real.sqrt (H.outer.weight ω.1) *
        H.apply (assignment (fun r => (labels (x,r)).2)) ω.1 ω.2 := by
  unfold tensorSlice
  rw [← Finset.mul_sum, ← apply_sum]
  simp_rw [sum_assignment_product]

omit [Fintype Q₁] in
/-- The fiber mass is an actual collision energy of the second game, not a
free normalization assumption. -/
theorem vectorMass_tensorSlice (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (x : Q₁) :
    vectorMass (H.tensorSlice labels) x =
      H.assignmentEnergy (fun r => (labels (x,r)).2) := by
  classical
  unfold vectorMass assignmentEnergy energy
  simp_rw [tensorSlice_label_mass, mul_pow]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [Real.sq_sqrt (H.outer.nonnegative y), Finset.mul_sum]

omit [Fintype Q₁] in
theorem vectorMass_tensorSlice_le [Nonempty B₁]
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (x : Q₁) :
    vectorMass (H.tensorSlice labels) x ≤ H.collisionValue := by
  rw [vectorMass_tensorSlice]
  exact H.assignmentEnergy_le_collisionValue _

/-- Exact Hilbert-norm factorization, with every marginal weight retained. -/
theorem vectorEnergy_tensorSlice (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) :
    K.vectorEnergy (H.tensorSlice labels) = (K.product H).assignmentEnergy labels := by
  unfold vectorEnergy assignmentEnergy energy tensorSlice
  simp only [Fintype.sum_prod_type, apply_smul, mul_pow,
    Real.sq_sqrt (H.outer.nonnegative _), apply_product, Finset.mul_sum]
  simp only [product, Foundations.Games.FiniteDistribution.product, mul_assoc]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]

end ProjectionKernel
end
end UniqueGamesTheorem.Repetition

end

section

/-! Homogeneous normalization for finite nonnegative vector assignments. -/

namespace UniqueGamesTheorem.Repetition.ProjectionKernel
open scoped BigOperators
noncomputable section

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

omit [Fintype Q₁] in
theorem vectorMass_smul (f : Ω → Q₁ → A₁ → ℝ) (r : ℝ) (x : Q₁) :
    vectorMass (fun ω x a => r * f ω x a) x = r ^ 2 * vectorMass f x := by
  unfold vectorMass
  simp_rw [← Finset.mul_sum, mul_pow]
  exact (Finset.mul_sum _ _ _).symm

theorem energy_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (r : ℝ) :
    K.energy (fun x a => r * f x a) = r ^ 2 * K.energy f := by
  unfold energy
  simp_rw [apply_smul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro b _
  exact mul_left_comm _ _ _

theorem vectorEnergy_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) (r : ℝ) :
    K.vectorEnergy (fun ω x a => r * f ω x a) = r ^ 2 * K.vectorEnergy f := by
  unfold vectorEnergy
  simp_rw [energy_smul]
  exact (Finset.mul_sum _ _ _).symm

omit [Fintype Q₁] in
theorem entry_eq_zero_of_vectorMass_nonpositive
    (f : Ω → Q₁ → A₁ → ℝ) (hf : ∀ ω x a, 0 ≤ f ω x a)
    (hmass : ∀ x, vectorMass f x ≤ 0) (ω : Ω) (x : Q₁) (a : A₁) :
    f ω x a = 0 := by
  classical
  have hsquare : (∑ b, f ω x b) ^ 2 ≤ vectorMass f x :=
    Finset.single_le_sum (fun τ _ => sq_nonneg (∑ b, f τ x b)) (Finset.mem_univ ω)
  have hsum : ∑ b, f ω x b = 0 := by
    nlinarith [hmass x, sq_nonneg (∑ b, f ω x b)]
  have hentry : f ω x a ≤ ∑ b, f ω x b :=
    Finset.single_le_sum (fun b _ => hf ω x b) (Finset.mem_univ a)
  rw [hsum] at hentry
  exact le_antisymm hentry (hf ω x a)

theorem vectorEnergy_eq_zero_of_mass_nonpositive
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) (hf : ∀ ω x a, 0 ≤ f ω x a)
    (hmass : ∀ x, vectorMass f x ≤ 0) : K.vectorEnergy f = 0 := by
  have hfzero : f = fun _ _ _ => 0 := by
    funext ω x a
    exact entry_eq_zero_of_vectorMass_nonpositive f hf hmass ω x a
  rw [hfzero]
  simp [vectorEnergy, energy, apply]

/-- A unit-mass estimate extends to any nonnegative mass bound, including
zero. The hypothesis is precisely the unit-mass analytic estimate being
normalized; the normalization itself assumes no repetition bound. -/
theorem vectorEnergy_le_of_unit_bound
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (ρ C : ℝ)
    (unit_bound : ∀ f : Ω → Q₁ → A₁ → ℝ,
      (∀ ω x a, 0 ≤ f ω x a) → (∀ x, vectorMass f x ≤ 1) → K.vectorEnergy f ≤ ρ)
    (hC : 0 ≤ C) (f : Ω → Q₁ → A₁ → ℝ)
    (hf : ∀ ω x a, 0 ≤ f ω x a) (hmass : ∀ x, vectorMass f x ≤ C) :
    K.vectorEnergy f ≤ ρ * C := by
  rcases eq_or_lt_of_le hC with hzero | hpositive
  · have hCzero : C = 0 := hzero.symm
    subst C
    rw [K.vectorEnergy_eq_zero_of_mass_nonpositive f hf hmass, mul_zero]
  · have hsqrt : 0 ≤ (Real.sqrt C)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg C)
    have hscale : ((Real.sqrt C)⁻¹) ^ 2 = C⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hC]
    have hnorm : ∀ x, vectorMass (fun ω x a => (Real.sqrt C)⁻¹ * f ω x a) x ≤ 1 := by
      intro x
      rw [vectorMass_smul, hscale]
      have h := mul_le_mul_of_nonneg_left (hmass x) (inv_nonneg.mpr hC)
      simpa [ne_of_gt hpositive] using h
    have hbound := unit_bound (fun ω x a => (Real.sqrt C)⁻¹ * f ω x a)
      (fun ω x a => mul_nonneg hsqrt (hf ω x a)) hnorm
    rw [vectorEnergy_smul, hscale] at hbound
    have h := mul_le_mul_of_nonneg_left hbound hC
    simpa [← mul_assoc, ne_of_gt hpositive, mul_comm C ρ] using h

end
end UniqueGamesTheorem.Repetition.ProjectionKernel

end

section

/-!
Alphabet-independent repetition of ordinary finite projection games.

The game is the actual finite question distribution and its local acceptance
predicate. The proof bounds nonnegative vector assignments by finite
thresholding and correlated sampling, factors each unrestricted product
strategy through that bound, and iterates the resulting collision contraction.
No repetition bound, decoder certificate, or alphabet-size budget is a premise.

The deterministic-predicate game interface permits arbitrary real question
weights. Distinct hidden constraints on the same question pair are not encoded
by this interface. Both v2 uses have a unique predicate for each question pair:
the distinct-position equation--variable game and the final simple graph.
-/

namespace UniqueGamesTheorem.Repetition
open UniqueGamesTheorem.Foundations.Games
noncomputable section

namespace ProjectionKernel
variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]
  [Nonempty A₁] [Nonempty A₂] [Nonempty B₁] [Nonempty B₂]

omit [Nonempty B₂] in
theorem collisionValue_product_le_gap_rate
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - gap) :
    (K.product H).collisionValue ≤ (1 - gap ^ 2 / 8) * H.collisionValue := by
  apply ((K.product H).collisionValue_le_iff _).2
  intro labels
  rw [← vectorEnergy_tensorSlice]
  apply K.vectorEnergy_le_of_unit_bound (1 - gap ^ 2 / 8) H.collisionValue
    (fun f hf hmass => K.vectorEnergy_le_gap_rate f hf hmass hgap₀ hgap₁ hvalue)
    H.collisionValue_nonneg (H.tensorSlice labels)
    (H.tensorSlice_nonnegative labels) (H.vectorMass_tensorSlice_le labels)

theorem repetition_value_le_dsRate
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - gap) (n : ℕ) :
    (K.toGame.repetition n).value ≤ dsRate gap ^ n := by
  have hstep : ∀ m, (K.repetition (m + 1)).collisionValue ≤
      (1 - gap ^ 2 / 8) * (K.repetition m).collisionValue := by
    intro m
    rw [K.collisionValue_repetition_succ]
    exact K.collisionValue_product_le_gap_rate (K.repetition m) hgap₀ hgap₁ hvalue
  have h := rate_of_squared_collision_recurrence hgap₀ hgap₁
    (fun m => (K.repetition m).collisionValue)
    (fun m => (K.repetition m).toGame.value)
    K.collisionValue_repetition_zero_le_one hstep
    (fun m => (K.repetition m).value_sq_le_collisionValue) n
  simpa only [toGame_repetition] using h

end ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

/-- The v2 projection-repetition estimate, including the empty product.
The repetition exponent is independent of all question and answer cardinalities. -/
theorem projection_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    {gap : ℝ} (hgap₀ : 0 < gap) (hgap₁ : gap < 1)
    (hvalue : G.value ≤ 1 - gap) :
    (G.repetition n).value ≤ (1 - gap ^ 2 / 16) ^ n := by
  have h := (kernelOfGame G hG).repetition_value_le_dsRate hgap₀.le hgap₁.le
    (by simpa only [kernelOfGame_value] using hvalue) n
  simpa only [toGame_kernelOfGame, dsRate] using h


theorem clean_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    (hvalue : G.value ≤ (14 : ℝ) / 15) :
    (G.repetition n).value ≤ (1 - (1 : ℝ) / 3600) ^ n := by
  have hv : G.value ≤ 1 - (1 : ℝ) / 15 := by
    convert hvalue using 1
    norm_num
  have h := projection_repetition_value G hG n
    (gap := (1 : ℝ) / 15) (by norm_num) (by norm_num) hv
  norm_num at h ⊢
  exact h

theorem final_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    (hvalue : G.value ≤ 1 - (1 : ℝ) / 800) :
    (G.repetition n).value ≤ (1 - (1 : ℝ) / 10240000) ^ n := by
  have h := projection_repetition_value G hG n
    (gap := (1 : ℝ) / 800) (by norm_num) (by norm_num) hvalue
  norm_num at h ⊢
  exact h

end
end UniqueGamesTheorem.Repetition

end

end OAI
