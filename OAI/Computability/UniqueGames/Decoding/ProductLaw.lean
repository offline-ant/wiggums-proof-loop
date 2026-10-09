/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Foundations.Conditioning
import OAI.Computability.UniqueGames.Soundness.ConditionalReindex

namespace OAI

section

/-!
# Weighted conditional product law for the v2 clean coordinates

The equation distribution is arbitrary.  All identities below are identities
of finite sums of its actual weights, rather than a reduction to uniform
occurrence sampling.  The clean set is fixed by independently sampled advice;
the only subsequently exposed question data lie outside that set.  Conditioning
on such data preserves the entire joint law of the clean questions.
-/

namespace UniqueGamesTheorem.Clean.ProductLaw

open scoped BigOperators
open Foundations.Games
open Soundness.ConditionalIncidences

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P Q S : Type} [Fintype P] [DecidableEq P] [Fintype Q] [Fintype S]

/-- Restriction to the clean and nonclean coordinates is a genuine bijection. -/
def splitCoordinates (K : Finset P) :
    (P → Q) ≃ (PositionInside K → Q) × (PositionOutside K → Q) :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ K) (fun _ => Q)

/-- Independent weighted sampling splits into independent clean and nonclean
parts. This identity proves, rather than assumes, their independence. -/
theorem table_split (μ : P → FiniteDistribution Q) (K : Finset P) :
    (FiniteDistribution.table μ).transport (splitCoordinates K) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).product
        (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro pieces
  change (∏ i, (μ i).weight ((splitCoordinates K).symm pieces i)) =
    (∏ i : PositionInside K, (μ i.val).weight (pieces.1 i)) *
      ∏ i : PositionOutside K, (μ i.val).weight (pieces.2 i)
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : P => i ∈ K)
    (fun i => (μ i).weight ((splitCoordinates K).symm pieces i))
  have hi : Subtype.fintype (fun i : P => i ∈ K) =
      Finset.Subtype.fintype K := Subsingleton.elim _ _
  rw [hi] at h
  calc
    _ = (∏ i : PositionInside K,
        (μ i.val).weight ((splitCoordinates K).symm pieces i.val)) *
        ∏ i : PositionOutside K,
          (μ i.val).weight ((splitCoordinates K).symm pieces i.val) := h.symm
    _ = _ := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
        simp [splitCoordinates, Equiv.piEquivPiSubtypeProd, i.property]

theorem probability_product_and (μ : FiniteDistribution Q) (ν : FiniteDistribution S)
    (event : Q → Bool) (given : S → Bool) :
    (μ.product ν).probability (fun x => event x.1 && given x.2) =
      μ.probability event * ν.probability given := by
  classical
  simp only [FiniteDistribution.probability, FiniteDistribution.product,
    Fintype.sum_prod_type]
  calc
    _ = ∑ q, ∑ s, (if event q then μ.weight q else 0) *
        (if given s then ν.weight s else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro s _
      cases event q <;> cases given s <;> simp
    _ = _ := by rw [Finset.sum_mul_sum]


/-- Exact factorization for an arbitrary joint event of clean coordinates and
an arbitrary observation/event depending only on the nonclean coordinates. -/
theorem table_inside_outside (μ : P → FiniteDistribution Q) (K : Finset P)
    (event : (PositionInside K → Q) → Bool)
    (given : (PositionOutside K → Q) → Bool) :
    (FiniteDistribution.table μ).probability
        (fun x => event (fun i => x i.val) && given (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event *
        (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given := by
  rw [← probability_product_and, ← table_split]
  exact (FiniteDistribution.probability_transport (FiniteDistribution.table μ)
    (splitCoordinates K) (fun pieces => event pieces.1 && given pieces.2)).symm

theorem table_outside (μ : P → FiniteDistribution Q) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool) :
    (FiniteDistribution.table μ).probability (fun x => given (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given := by
  simpa using table_inside_outside μ K (fun _ => true) given

/-- The normalized conditional law is the ordinary independent product law.
The only hypothesis is that the observed outside event has positive mass. -/
theorem conditioned_inside (μ : P → FiniteDistribution Q) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool)
    (positive : 0 < (FiniteDistribution.table μ).probability
      (fun x => given (fun i => x i.val)))
    (event : (PositionInside K → Q) → Bool) :
    ((FiniteDistribution.table μ).condition
      (fun x => given (fun i => x i.val)) positive).probability
        (fun x => event (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event := by
  rw [FiniteDistribution.probability_condition]
  simp_rw [Bool.and_comm (given _)]
  rw [table_inside_outside, table_outside]
  have hne : (FiniteDistribution.table
      (fun i : PositionOutside K => μ i.val)).probability given ≠ 0 := by
    rw [table_outside] at positive
    exact ne_of_gt positive
  exact mul_div_cancel_right₀ _ hne


/-- Reindexing a finite coordinate set gives the usual `iid` law on `Fin r`. -/
theorem table_reindex (μ : FiniteDistribution Q) {A : Type} [Fintype A] [DecidableEq A]
    {r : ℕ} (e : Fin r ≃ A) :
    (FiniteDistribution.table (fun _ : A => μ)).transport (coordinateReindex e) =
      μ.iid r := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ a, μ.weight (x (e.symm a))) = ∏ i, μ.weight (x i)
  exact e.symm.prod_comp (fun i => μ.weight (x i))

/-- Fixed advice, intercept and nonclean data preserve precisely the repeated
incidence law for arbitrary occurrence weights. Repeated IDs are permitted. -/
theorem conditioned_incidence_reindex
    {O N D : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    [Zero D] [DecidableEq D]
    (μ : FiniteDistribution (O × Fin 3))
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed)))
    {r : ℕ} (e : Fin r ≃ PositionInside (zeroSet J gamma))
    (event : (Fin r → O × N) → Bool) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed))
        positive).probability
          (fun x => event (fun i => incidence name (x (e i).val))) =
      ((μ.pushforward (incidence name)).iid r).probability event := by
  classical
  let given : (PositionOutside (zeroSet J gamma) → O × Fin 3) → Bool :=
    fun x => decide ((fun i => incidence name (x i)) = observed)
  let insideEvent : (PositionInside (zeroSet J gamma) → O × Fin 3) → Bool :=
    fun x => event (fun i => incidence name (x (e i)))
  have h := conditioned_inside (fun _ : P => μ) (zeroSet J gamma)
    given positive insideEvent
  change _ = _ at h
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.probability_pushforward]
  rw [← table_reindex μ e, FiniteDistribution.probability_transport]
  exact h


end
end UniqueGamesTheorem.Clean.ProductLaw

end

end OAI
