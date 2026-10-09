/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Dimension.Free
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionPresentationLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticBlockFrequenciesLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridCoordinatesRankLemmas
import OAI.Computability.UniqueGames.Inverse.KMSKernelOrbitsFourierLemmas

namespace OAI

section

/-!
Exact Fourier slice energies and their one-point KMS recurrence. The energy
is an unnormalized sum of actual squared coefficients. Translation changes
only a unit sign, so the dependent graph terms in the point recursion have
identical slice energies, without an ambient-cardinality loss.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- Every binary trace-character phase has unit square. -/
theorem traceCharacter_re_sq (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    (linearTraceCharacter S X).re ^ 2 = 1 := by
  simp only [linearTraceCharacter_apply, binarySign]
  split_ifs <;> norm_num

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- An arbitrary actual Fourier slice; in the mixed estimate P fixes selected
frequency coordinates. -/
def sliceEnergy (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ T with P T, linearCoeff f T ^ 2


/-- Translation acts on each actual coefficient by its trace-character sign. -/
theorem coeff_translate (f : (E →ₗ[F2] F) → ℝ) (Z : E →ₗ[F2] F)
    (T : F →ₗ[F2] E) :
    linearCoeff (fun X => f (X + Z)) T =
      linearCoeff f T * (linearTraceCharacter T Z).re := by
  unfold linearCoeff
  rw [Finset.expect_mul]
  apply Fintype.expect_equiv (Equiv.addRight Z)
  intro X
  simp only [Equiv.coe_addRight, AddChar.map_add_eq_mul, Complex.mul_re]
  have hi (Y : E →ₗ[F2] F) : (linearTraceCharacter T Y).im = 0 := by simp
  simp only [hi, mul_zero, sub_zero, mul_assoc]
  rw [← sq, traceCharacter_re_sq, mul_one]

/-- No loss from translating a function before taking a fixed Fourier slice. -/
theorem sliceEnergy_translate (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (Z : E →ₗ[F2] F) :
    sliceEnergy P (fun X => f (X + Z)) = sliceEnergy P f := by
  unfold sliceEnergy
  apply Finset.sum_congr rfl
  intro T _
  rw [coeff_translate, mul_pow, traceCharacter_re_sq, mul_one]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
/-- A finite difference of functions costs only the number of summands in
its Fourier slice energy. No pointwise bound on those functions is used. -/
theorem sliceEnergy_sub_sum_le {J : Type*} [Fintype J]
    (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    (g : J → (E →ₗ[F2] F) → ℝ) :
    sliceEnergy P (fun X => f X - ∑ j, g j X) ≤
      2 * (sliceEnergy P f + (Fintype.card J : ℝ) * ∑ j, sliceEnergy P (g j)) := by
  have hc (T : F →ₗ[F2] E) :
      linearCoeff (fun X => f X - ∑ j, g j X) T =
        linearCoeff f T - ∑ j, linearCoeff (g j) T := by
    simp only [linearCoeff, sub_mul, Finset.sum_mul, Finset.expect_sub_distrib,
      Finset.expect_sum_comm]
  have hp (T : F →ₗ[F2] E) :
      (linearCoeff f T - ∑ j, linearCoeff (g j) T) ^ 2 ≤
        2 * (linearCoeff f T ^ 2 + (Fintype.card J : ℝ) *
          ∑ j, linearCoeff (g j) T ^ 2) := by
    have hcs : (∑ j, linearCoeff (g j) T) ^ 2 ≤
        (Fintype.card J : ℝ) * ∑ j, linearCoeff (g j) T ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : J => (1 : ℝ)) (fun j => linearCoeff (g j) T)
    nlinarith [sq_nonneg (linearCoeff f T + ∑ j, linearCoeff (g j) T)]
  calc
    _ ≤ ∑ T with P T, 2 * (linearCoeff f T ^ 2 + (Fintype.card J : ℝ) *
        ∑ j, linearCoeff (g j) T ^ 2) := by
      apply Finset.sum_le_sum
      intro T _
      rw [hc]
      exact hp T
    _ = _ := by
      unfold sliceEnergy
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_comm (s := Finset.univ.filter P) (t := Finset.univ)]


end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
Exact partial restrictions in product coordinates. Translating the full map
shifts both the fixed and free coordinates. The latter shift preserves every
actual Fourier slice energy, so finite differences of translated functions
cost only the finite Cauchy factor already present before restriction.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters

variable {A I F : Type*}
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

/-- Fix the first product block, leaving the second block free. -/
def partialRestrict (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    (I →ₗ[F2] F) → ℝ := fun X => f (a.coprod X)

@[simp] theorem partialRestrict_apply
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (X : I →ₗ[F2] F) : partialRestrict f a X = f (a.coprod X) := rfl

/-- The two coordinate shifts reassemble to the original full-map shift. -/
theorem coprod_add_shift (a : A →ₗ[F2] F) (X : I →ₗ[F2] F)
    (Z : (A × I) →ₗ[F2] F) :
    a.coprod X + Z =
      (a + Z.comp (LinearMap.inl F2 A I)).coprod
        (X + Z.comp (LinearMap.inr F2 A I)) := by
  apply LinearMap.prod_ext <;> simp [LinearMap.add_comp]

/-- Restriction of a translate shifts the fixed and the free blocks. -/
theorem partialRestrict_translate
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (Z : (A × I) →ₗ[F2] F) :
    partialRestrict (fun Y => f (Y + Z)) a =
      fun X => partialRestrict f (a + Z.comp (LinearMap.inl F2 A I))
        (X + Z.comp (LinearMap.inr F2 A I)) := by
  funext X
  change f (a.coprod X + Z) =
    f ((a + Z.comp (LinearMap.inl F2 A I)).coprod
      (X + Z.comp (LinearMap.inr F2 A I)))
  rw [coprod_add_shift]

/-- Partial restriction commutes exactly with a finite difference. -/
theorem partialRestrict_sub_sum {J : Type*} [Fintype J]
    (f : ((A × I) →ₗ[F2] F) → ℝ)
    (g : J → ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict (fun Y => f Y - ∑ j, g j Y) a =
      fun X => partialRestrict f a X - ∑ j, partialRestrict (g j) a X := rfl

variable [FiniteDimensional F2 I] [FiniteDimensional F2 F]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

/-- The free-block translation has unit Fourier phase, leaving only the
shift of the fixed block in the slice energy. -/
theorem sliceEnergy_partialRestrict_translate
    (P : (F →ₗ[F2] I) → Prop)
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (Z : (A × I) →ₗ[F2] F) :
    sliceEnergy P (partialRestrict (fun Y => f (Y + Z)) a) =
      sliceEnergy P (partialRestrict f (a + Z.comp (LinearMap.inl F2 A I))) := by
  rw [partialRestrict_translate, sliceEnergy_translate]

/-- The exact finite Cauchy bound after fixing a product block. Each
correction function is evaluated at its own translated fixed block. -/
theorem sliceEnergy_partialRestrict_sub_translates_le {J : Type*} [Fintype J]
    (P : (F →ₗ[F2] I) → Prop)
    (f : ((A × I) →ₗ[F2] F) → ℝ)
    (g : J → ((A × I) →ₗ[F2] F) → ℝ)
    (a : A →ₗ[F2] F) (Z : J → (A × I) →ₗ[F2] F) :
    sliceEnergy P (partialRestrict (fun Y => f Y - ∑ j, g j (Y + Z j)) a) ≤
      2 * (sliceEnergy P (partialRestrict f a) +
        (Fintype.card J : ℝ) * ∑ j, sliceEnergy P
          (partialRestrict (g j) (a + (Z j).comp (LinearMap.inl F2 A I)))) := by
  rw [partialRestrict_sub_sum]
  have h := sliceEnergy_sub_sum_le P (partialRestrict f a)
    (fun j => partialRestrict (fun Y => g j (Y + Z j)) a)
  simpa only [sliceEnergy_partialRestrict_translate] using h

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
Exact Fourier merging after fixing a primal product block. The coefficient
uses normalized expectation, while the merged frequency sum is unnormalized.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Inverse.KMSFourthMoment
open UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergyPhase

variable {A I F : Type*}
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

/-- Splitting the fixed and free frequency blocks is an exact bijection. -/
def frequencyBlockEquiv : ((F →ₗ[F2] A) × (F →ₗ[F2] I)) ≃
    (F →ₗ[F2] (A × I)) :=
  (LinearMap.prodEquiv (S := F2)).toEquiv

/-- The free frequency can be summed first, with no multiplicity factor. -/
theorem sum_frequency_blocks {M : Type*} [AddCommMonoid M]
    [Fintype (F →ₗ[F2] A)] [Fintype (F →ₗ[F2] I)]
    [Fintype (F →ₗ[F2] (A × I))]
    (g : (F →ₗ[F2] (A × I)) → M) :
    ∑ S, g S = ∑ T : F →ₗ[F2] I, ∑ alpha : F →ₗ[F2] A, g (alpha.prod T) := by
  rw [← frequencyBlockEquiv.sum_comp g, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

variable [FiniteDimensional F2 A] [FiniteDimensional F2 I]
  [FiniteDimensional F2 F]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (F →ₗ[F2] A)]

omit [Fintype (I →ₗ[F2] F)] in
/-- Fixing a primal block merges exactly its dual frequency block. -/
theorem partialRestrict_eq_synthesis
    (h : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict h a = synthesis (fun T : F →ₗ[F2] I =>
      ∑ alpha : F →ₗ[F2] A,
        linearCoeff h (alpha.prod T) * (linearTraceCharacter alpha a).re) := by
  funext X
  change h (a.coprod X) = _
  rw [← linear_fourier_inversion h (a.coprod X), sum_frequency_blocks]
  simp only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro alpha _
  rw [character_prod_coprod_re]
  ring

/-- The actual partial-restriction coefficient is an unnormalized frequency
merge; normalized Fourier expectation introduces no additional factor. -/
theorem coeff_partialRestrict
    (h : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (T : F →ₗ[F2] I) :
    linearCoeff (partialRestrict h a) T =
      ∑ alpha : F →ₗ[F2] A,
        linearCoeff h (alpha.prod T) * (linearTraceCharacter alpha a).re := by
  rw [partialRestrict_eq_synthesis, coeff_synthesis]

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-! The actual Fourier coefficient of an adapted hybrid fiber factors into
the complementary-block phase and a mixed partial-restriction coefficient. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates KMSAnalyticHybridEnergyPhase
open KMSFourthMoment

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]

def coordinateOfData (z : B →ₗ[F2] W) (α : (B × C) →ₗ[F2] A)
    (ψ : Extension (C := C) z) (v : C →ₗ[F2] D) :
    Coordinates (A := A) (D := D) (C := C) z :=
  ⟨α, ψ.val, ψ.property, v⟩

def primalA (T : (A × (W × D)) →ₗ[F2] (B × C)) : A →ₗ[F2] (B × C) :=
  T.comp (LinearMap.inl F2 A (W × D))

def primalW (T : (A × (W × D)) →ₗ[F2] (B × C)) : W →ₗ[F2] (B × C) :=
  (T.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inl F2 W D)

def primalD (T : (A × (W × D)) →ₗ[F2] (B × C)) : D →ₗ[F2] (B × C) :=
  (T.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inr F2 W D)

variable [Fintype ((B × C) →ₗ[F2] A)] [Fintype ((B × C) →ₗ[F2] W)]
  [Fintype (C →ₗ[F2] D)] [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]

theorem sum_compressedFiber (z : B →ₗ[F2] W)
    (g : ((B × C) →ₗ[F2] (A × (W × D))) → ℝ) :
    (∑ S : {S : (B × C) →ₗ[F2] (A × (W × D)) //
        compressBlock S = z.prod (0 : B →ₗ[F2] D)}, g S.val) =
      ∑ α : (B × C) →ₗ[F2] A, ∑ ψ : Extension (C := C) z,
        ∑ v : C →ₗ[F2] D, g (assemble (coordinateOfData z α ψ v)) := by
  calc
    _ = ∑ p : ((B × C) →ₗ[F2] A) × Extension (C := C) z × (C →ₗ[F2] D),
        g (assemble (coordinateOfData z p.1 p.2.1 p.2.2)) := by
      apply Fintype.sum_equiv (compressedFiberDataEquiv (A := A) (D := D) z)
      intro S
      exact congrArg g (assemble_extract z S).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]

variable [FiniteDimensional F2 A] [FiniteDimensional F2 W]
  [FiniteDimensional F2 D] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
  [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))]
  [Fintype ((W × C) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (W × C))]

omit [Fintype ((B × C) →ₗ[F2] W)] [Fintype (C →ₗ[F2] D)] in
/-- One sum over the fixed frequency block is precisely the Fourier
coefficient of the actual partially restricted small component. -/
theorem sum_alpha_hybrid_term (z : B →ₗ[F2] W) (hz : Function.Surjective z)
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))) (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × (W × D)) →ₗ[F2] (B × C))
    (ψ : Extension (C := C) z) (v : C →ₗ[F2] D) :
    (∑ α : (B × C) →ₗ[F2] A,
      (if LinearIdentities.Hybrid (assemble (coordinateOfData z α ψ v))
          (LinearMap.range (LinearMap.inl F2 A (W × D)))
          (LinearMap.range (LinearMap.inl F2 B C)) then
        linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f)
          (assemble (coordinateOfData z α ψ v)) else 0) *
        (linearTraceCharacter (assemble (coordinateOfData z α ψ v)) T).re) =
      if Function.Injective v then
        (linearTraceCharacter (v.comp (LinearMap.snd F2 B C)) (primalD T)).re *
        ((linearTraceCharacter ψ.val (primalW T)).re *
          linearCoeff (partialRestrict (smallComponent κ f) (primalA T))
            (ψ.val.prod (LinearMap.snd F2 B C))) else 0 := by
  simp_rw [hybrid_rank_coeff_assemble hz _ κ hκ f hf, character_assemble_re]
  by_cases hv : Function.Injective v
  · simp only [coordinateOfData, hv, ite_true]
    rw [coeff_partialRestrict]
    simp only [coeff_smallComponent, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    change smallCoeff κ f (α.prod (ψ.val.prod (LinearMap.snd F2 B C))) *
        ((linearTraceCharacter α (primalA T)).re *
          ((linearTraceCharacter ψ.val (primalW T)).re *
            (linearTraceCharacter (v.comp (LinearMap.snd F2 B C)) (primalD T)).re)) = _
    ring
  · simp [coordinateOfData, hv]

/-- Exact phase/frequency factorization in the adapted fiber. Every
coefficient on the right belongs to the actual mixed partial restriction. -/
theorem hybrid_fiber_coefficient_factorization
    (z : B →ₗ[F2] W) (hz : Function.Surjective z)
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))) (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) :
    (∑ S : {S : (B × C) →ₗ[F2] (A × (W × D)) //
        compressBlock S = z.prod (0 : B →ₗ[F2] D)},
      (if LinearIdentities.Hybrid S.val
          (LinearMap.range (LinearMap.inl F2 A (W × D)))
          (LinearMap.range (LinearMap.inl F2 B C)) then
        linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) S.val else 0) *
        (linearTraceCharacter S.val T).re) =
      (∑ v ∈ Finset.univ.filter (fun v : C →ₗ[F2] D => Function.Injective v),
        (linearTraceCharacter (v.comp (LinearMap.snd F2 B C)) (primalD T)).re) *
      (∑ ψ : Extension (C := C) z,
        (linearTraceCharacter ψ.val (primalW T)).re *
          linearCoeff (partialRestrict (smallComponent κ f) (primalA T))
            (ψ.val.prod (LinearMap.snd F2 B C))) := by
  rw [sum_compressedFiber z (fun S =>
    (if LinearIdentities.Hybrid S
      (LinearMap.range (LinearMap.inl F2 A (W × D)))
      (LinearMap.range (LinearMap.inl F2 B C)) then
      linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) S else 0) *
      (linearTraceCharacter S T).re), Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ((B × C) →ₗ[F2] A)))
    (t := (Finset.univ : Finset (C →ₗ[F2] D))),
    sum_alpha_hybrid_term z hz κ hκ f hf T]
  simp_rw [← Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-!
Exact sums on fixed Fourier slices and compressed-frequency extension fibers.
Fixing the last frequency block leaves each first block exactly once, and
passing between an extension subtype and a filtered sum changes no weights.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSFourthMoment

section Slice

variable {F W C : Type*}
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup W] [Module F2 W]
  [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 F] [FiniteDimensional F2 W] [FiniteDimensional F2 C]
  [Fintype ((W × C) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (W × C))]
  [Fintype (F →ₗ[F2] W)]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 W] [FiniteDimensional F2 C] in
/-- An actual slice fixing the last frequency block is parametrized by all
first blocks, with no multiplicity or normalization factor. -/
theorem sliceEnergy_fixed_snd (ν : F →ₗ[F2] C)
    (g : ((W × C) →ₗ[F2] F) → ℝ) :
    sliceEnergy (fun T => (LinearMap.snd F2 W C).comp T = ν) g =
      ∑ ψ : F →ₗ[F2] W, linearCoeff g (ψ.prod ν) ^ 2 := by
  unfold sliceEnergy
  refine Finset.sum_bij (fun T _ => (LinearMap.fst F2 W C).comp T) (by simp) ?_ ?_ ?_
  · intro S hS T hT h
    rw [Finset.mem_filter] at hS hT
    apply LinearMap.ext
    intro x
    exact Prod.ext (DFunLike.congr_fun h x)
      (DFunLike.congr_fun (hS.2.trans hT.2.symm) x)
  · intro ψ _
    exact ⟨ψ.prod ν, by simp, rfl⟩
  · intro T hT
    congr 2
    rw [← (Finset.mem_filter.mp hT).2]
    rfl

end Slice

section HybridSlice

variable {B W C : Type*}
  [AddCommGroup B] [Module F2 B]
  [AddCommGroup W] [Module F2 W]
  [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 B] [FiniteDimensional F2 W] [FiniteDimensional F2 C]
  [Fintype ((W × C) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (W × C))]
  [Fintype ((B × C) →ₗ[F2] W)]

omit [FiniteDimensional F2 B] [FiniteDimensional F2 W] [FiniteDimensional F2 C] in
theorem sliceEnergy_snd_eq_sum (g : ((W × C) →ₗ[F2] (B × C)) → ℝ) :
    sliceEnergy (fun T => (LinearMap.snd F2 W C).comp T = LinearMap.snd F2 B C) g =
      ∑ ψ : (B × C) →ₗ[F2] W,
        linearCoeff g (ψ.prod (LinearMap.snd F2 B C)) ^ 2 :=
  sliceEnergy_fixed_snd (LinearMap.snd F2 B C) g

end HybridSlice

section Extensions

variable {R B W C M : Type*} [Ring R]
  [AddCommGroup B] [Module R B]
  [AddCommGroup W] [Module R W]
  [AddCommGroup C] [Module R C]
  [AddCommMonoid M] [Fintype ((B × C) →ₗ[R] W)]

/-- Summing over actual extensions is exactly the corresponding filtered
frequency sum. This identity applies to phases and squared coefficients. -/
theorem sum_extensions_eq_filter (z : B →ₗ[R] W)
    [Fintype (Extension (C := C) z)] (H : ((B × C) →ₗ[R] W) → M) :
    (∑ ψ : Extension (C := C) z, H ψ.val) =
      ∑ ψ with ψ.comp (LinearMap.inl R B C) = z, H ψ := by
  exact (Finset.sum_subtype
    (p := fun ψ : (B × C) →ₗ[R] W => ψ.comp (LinearMap.inl R B C) = z)
    (Finset.univ.filter (fun ψ : (B × C) →ₗ[R] W =>
      ψ.comp (LinearMap.inl R B C) = z)) (by simp) H).symm

end Extensions
end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-! A single compressed-image contribution is controlled by an actual mixed
slice energy. The only losses are the explicit finite coordinate counts. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates KMSFourthMoment

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 W]
  [FiniteDimensional F2 D] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((B × C) →ₗ[F2] A)] [Fintype ((B × C) →ₗ[F2] W)]
  [Fintype ((B × C) →ₗ[F2] C)]
  [Fintype (C →ₗ[F2] D)] [Fintype (C →ₗ[F2] W)] [Fintype (B →ₗ[F2] W)]
  [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
  [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
  [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))]
  [Fintype ((W × C) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (W × C))]

def adaptedFiberCoefficient (z : B →ₗ[F2] W)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) : ℝ :=
  ∑ S : {S : (B × C) →ₗ[F2] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[F2] D)},
    (if LinearIdentities.Hybrid S.val
        (LinearMap.range (LinearMap.inl F2 A (W × D)))
        (LinearMap.range (LinearMap.inl F2 B C)) then
      linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) S.val else 0) *
      (linearTraceCharacter S.val T).re

omit [Fintype ((B × C) →ₗ[F2] C)] in
/-- The contribution of all surjective compressed maps onto one fixed image
is bounded by the actual mixed-slice energy, with its exact extension count. -/
theorem adapted_image_energy_le_mixed
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))) (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) :
    (∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] W => Function.Surjective z), adaptedFiberCoefficient z f T ^ 2) ≤
      (Fintype.card (C →ₗ[F2] D) : ℝ) ^ 2 * (Fintype.card (C →ₗ[F2] W) : ℝ) *
        sliceEnergy (fun U : (B × C) →ₗ[F2] (W × C) =>
          (LinearMap.snd F2 W C).comp U = LinearMap.snd F2 B C)
          (partialRestrict (smallComponent κ f) (primalA T)) := by
  let r : ((B × C) →ₗ[F2] W) → (B →ₗ[F2] W) :=
    fun ψ => ψ.comp (LinearMap.inl F2 B C)
  let a : (C →ₗ[F2] D) → ℝ := fun v => if Function.Injective v then
    (linearTraceCharacter (v.comp (LinearMap.snd F2 B C)) (primalD T)).re else 0
  let b : ((B × C) →ₗ[F2] W) → ℝ := fun ψ =>
    (linearTraceCharacter ψ (primalW T)).re
  let H : ((B × C) →ₗ[F2] W) → ℝ := fun ψ =>
    linearCoeff (partialRestrict (smallComponent κ f) (primalA T))
      (ψ.prod (LinearMap.snd F2 B C))
  have ha (v : C →ₗ[F2] D) : a v ^ 2 ≤ 1 := by
    dsimp [a]
    split_ifs
    · exact (traceCharacter_re_sq _ _).le
    · norm_num
  have hb (ψ : (B × C) →ₗ[F2] W) : b ψ ^ 2 ≤ 1 := by
    exact le_of_eq (traceCharacter_re_sq ψ (primalW T))
  have hr (z : B →ₗ[F2] W) :
      (Finset.univ.filter (fun ψ => r ψ = z)).card ≤ Fintype.card (C →ₗ[F2] W) := by
    exact le_of_eq (card_restriction_fiber_eq z)
  have hfactor (z : B →ₗ[F2] W) (hz : Function.Surjective z) :
      adaptedFiberCoefficient z f T =
        (∑ v, a v) * (∑ ψ with r ψ = z, b ψ * H ψ) := by
    rw [adaptedFiberCoefficient, hybrid_fiber_coefficient_factorization z hz κ hκ f hf T]
    have he : (∑ ψ : Extension (C := C) z, b ψ.val * H ψ.val) =
        ∑ ψ with r ψ = z, b ψ * H ψ := by
      exact sum_extensions_eq_filter z (fun ψ => b ψ * H ψ)
    change _ = (∑ v, a v) * _
    rw [← he]
    congr 1
    simp only [a, Finset.sum_filter]
  calc
    _ = ∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] W => Function.Surjective z),
        ((∑ v, a v) * (∑ ψ with r ψ = z, b ψ * H ψ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hfactor z (Finset.mem_filter.mp hz).2]
    _ ≤ ∑ z : B →ₗ[F2] W,
        ((∑ v, a v) * (∑ ψ with r ψ = z, b ψ * H ψ)) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun z _ _ => sq_nonneg _)
    _ ≤ (Fintype.card (C →ₗ[F2] D) : ℝ) ^ 2 *
        (Fintype.card (C →ₗ[F2] W) : ℝ) * ∑ ψ, H ψ ^ 2 :=
      sum_fiber_product_sq_le r a b H (Fintype.card (C →ₗ[F2] W)) ha hb hr
    _ = _ := by
      rw [sliceEnergy_snd_eq_sum]

omit [Fintype ((B × C) →ₗ[F2] C)] in
/-- The conditional analytic step uses an actual mixed-slice bound as its
only analytic hypothesis. -/
theorem adapted_image_energy_le_of_mixed
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))) (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) (H : ℝ)
    (hH : sliceEnergy (fun U : (B × C) →ₗ[F2] (W × C) =>
        (LinearMap.snd F2 W C).comp U = LinearMap.snd F2 B C)
      (partialRestrict (smallComponent κ f) (primalA T)) ≤ H) :
    (∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] W => Function.Surjective z), adaptedFiberCoefficient z f T ^ 2) ≤
      (Fintype.card (C →ₗ[F2] D) : ℝ) ^ 2 * (Fintype.card (C →ₗ[F2] W) : ℝ) * H := by
  apply (adapted_image_energy_le_mixed κ hκ f hf T).trans
  exact mul_le_mul_of_nonneg_left hH (by positivity)

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end OAI
