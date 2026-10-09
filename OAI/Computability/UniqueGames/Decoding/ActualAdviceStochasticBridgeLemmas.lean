/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Decoding.ActualAdviceBridgeLemmas
import OAI.Computability.UniqueGames.Decoding.AdviceImageLaw
import OAI.Computability.UniqueGames.Decoding.PaddedLaw
import OAI.Computability.UniqueGames.Decoding.StochasticBound
import OAI.Computability.UniqueGames.Decoding.TableKeysLemmas
import OAI.Computability.UniqueGames.Foundations.MixtureLemmas
import OAI.Computability.UniqueGames.Soundness.RawTargetLawLemmas

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

/-! Actual randomized point policies are transported locally into Boolean
answer kernels. Complete response tables are selected only after public advice
is fixed and before the remaining questions. No global deterministic policy
independent of public advice is asserted or needed for this upper bound. -/

namespace Clean.ActualAdviceStochasticBridge

open Foundations.Games Integration.BinaryLinear Reduction
open Soundness Soundness.ConditionalIncidences Soundness.RawPartnerTarget
open Soundness.RepeatedGameBounds
open AnswerBridge ActualAdviceBridge

attribute [local instance] Classical.propDecidable

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D]
  [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O]
  [Fintype N] [DecidableEq N] [Fintype D]

instance sourceAnswerNonempty : Nonempty (SourceAnswer k) := ⟨⟨(1, 0), rfl⟩⟩
instance targetAnswerNonempty (J : Finset (Fin k)) : Nonempty (TargetAnswer J) :=
  ⟨defaultTargetAnswer J⟩

structure Policies (k : ℕ) (g : IncidenceExtraction.Incidence O N) (D : Type)
    [AddCommGroup D] [Module F2 D] where
  first : (J : Finset (Fin k)) → (Fin k → O) →
    (ActualHomogeneous.E k →ₗ[F2] D) → FiniteDistribution (SourceAnswer k)
  second : (J : Finset (Fin k)) → RawPrivateTable.SupportedV J g.name →
    (RawPoint J →ₗ[F2] D) → FiniteDistribution (TargetAnswer J)

def extendTargetKernel (J : Finset (Fin k)) (names : O → Fin 3 → N)
    (kernel : RawPrivateTable.SupportedV J names → (RawPoint J →ₗ[F2] D) →
      FiniteDistribution (TargetAnswer J))
    (question : Fin k → Sum O N) (Y : RawPoint J →ₗ[F2] D) :
    FiniteDistribution (TargetAnswer J) :=
  if h : question ∈ Set.range
      (fun e : RawPrivateTable.Extension k O => RawPrivateTable.displayed J names e.1 e.2)
  then kernel ⟨question, h⟩ Y else FiniteDistribution.uniform (TargetAnswer J)

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem extendTargetKernel_apply (J : Finset (Fin k)) (names : O → Fin 3 → N)
    (kernel : RawPrivateTable.SupportedV J names → (RawPoint J →ₗ[F2] D) →
      FiniteDistribution (TargetAnswer J))
    (V : RawPrivateTable.SupportedV J names) (Y : RawPoint J →ₗ[F2] D) :
    extendTargetKernel J names kernel V.val Y = kernel V Y := by
  unfold extendTargetKernel
  rw [dite_eq_left V.property]
  congr 1

def firstResponse (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (qa : ZeroInformation.FirstInput (Fin k) Q O) :
    FiniteDistribution (ActualProjection.FirstAnswer (Fin k)) :=
  (policy.first J qa.question
    (coordinates.symm.toLinearMap.comp (ActualInputRows.firstMap g.rhs qa))).pushforward
      (fun x => ActualPointAnswers.firstAnswer (fun j => g.rhs (qa.question j)) x.val)

def secondResponse (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (qb : ZeroInformation.SecondInput (Fin k) Q O N) :
    FiniteDistribution (ActualProjection.SecondAnswer (Fin k)) :=
  (extendTargetKernel J g.name (policy.second J) qb.question
    (coordinates.symm.toLinearMap.comp (ActualInputRows.secondMap J qb))).pushforward
      (fun v => ActualPointAnswers.secondAnswer
        (ActualPointAnswers.displayedRhs g.rhs qb.question) J v.val)

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem decodeFirstMap_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (J : Finset (Fin k))
    (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    coordinates.symm.toLinearMap.comp (ActualInputRows.firstMap g.rhs
      (actualFirst J (encodedMapCoefficients coordinates J Y) draw)) =
      Y.comp (projection g J draw) := by
  have h := ActualInputRows.firstMap_actual J g.rhs (fun j => (draw j).1)
    (fun j => indexSlot (draw j).2) (coordinates.toLinearMap.comp Y)
  have repack : (fun j => ((draw j).1,
      ConcreteExtraction.slotIndex (indexSlot (draw j).2))) = draw := by
    funext j
    simp
  rw [repack] at h
  unfold encodedMapCoefficients projection
  rw [h]
  apply LinearMap.ext
  intro x
  exact coordinates.symm_apply_apply _

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem decodeSecondMap_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (J : Finset (Fin k))
    (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    coordinates.symm.toLinearMap.comp (ActualInputRows.secondMap J
      (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw)) = Y := by
  unfold encodedMapCoefficients
  rw [ActualInputRows.secondMap_actual]
  ext x
  simp

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem firstResponse_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    firstResponse coordinates g policy J
      (actualFirst J (encodedMapCoefficients coordinates J Y) draw) =
      (policy.first J (fun j => (draw j).1) (Y.comp (projection g J draw))).pushforward
        (fun x => ActualPointAnswers.firstAnswer (fun j => g.rhs (draw j).1) x.val) := by
  unfold firstResponse
  rw [decodeFirstMap_actual]
  rfl

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem secondResponse_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    secondResponse coordinates g policy J
      (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw) =
      (policy.second J (displayedQuestion g J draw) Y).pushforward
        (fun v => ActualPointAnswers.secondAnswer
          (ActualPointAnswers.displayedRhs g.rhs (displayedQuestion g J draw).val) J v.val) := by
  unfold secondResponse
  rw [decodeSecondMap_actual, sample_question, extendTargetKernel_apply]

/-- Two private finite answer draws, after receiving the respective actual
question and linear row map. Acceptance is equality under the real projection. -/
def fixedMapSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) : ℝ :=
  (FiniteDistribution.table (fun _ : Fin k => μ)).expectation fun draw =>
    ((policy.first J (fun j => (draw j).1) (Y.comp (projection g J draw))).product
      (policy.second J (displayedQuestion g J draw) Y)).probability
        (fun answers => decide (projection g J draw answers.1.val = answers.2.val))

omit [DecidableEq O] [DecidableEq N] [Fintype D] in
theorem fixedMapSuccess_le (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) :
    fixedMapSuccess μ g policy J Y ≤
      (StochasticBound.actualGame μ J g (encodedMapCoefficients coordinates J Y)).stochasticSuccess
        (firstResponse coordinates g policy J) (secondResponse coordinates g policy J) := by
  unfold fixedMapSuccess Game.stochasticSuccess StochasticBound.actualGame
    Simulation.weightedGame
  rw [FiniteDistribution.expectation_pushforward]
  apply expectation_mono
  intro draw
  rw [firstResponse_actual, secondResponse_actual]
  simp_rw [FiniteDistribution.expectation_pushforward]
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum,
    mul_ite, mul_one, mul_zero, decide_eq_true_eq]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro v _
  by_cases h : projection g J draw x.val = v.val
  · have accepted := ActualPointAnswers.actual_accepts J g
      (actualFirst J (encodedMapCoefficients coordinates J Y) draw)
      (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw)
      (fun j => indexSlot (draw j).2)
      (sample_question g J (encodedMapCoefficients coordinates J Y) draw)
      x.val v.val x.property h
    have firstQuestion :
        (actualFirst J (encodedMapCoefficients coordinates J Y) draw).question =
          (fun j => (draw j).1) := rfl
    rw [firstQuestion] at accepted
    have accepted' : (ActualProjection.predicateGame g (membershipBool J)).accepts
        (actualFirst J (encodedMapCoefficients coordinates J Y) draw)
        (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw)
        (ActualPointAnswers.firstAnswer (fun j => g.rhs (draw j).1) x.val)
        (ActualPointAnswers.secondAnswer
          (ActualPointAnswers.displayedRhs g.rhs (displayedQuestion g J draw).val)
          J v.val) := by
      change ActualProjection.accepts g (PartnerMapCoordinates.activeOf J) _ _ _ _
      rw [← sample_question g J (encodedMapCoefficients coordinates J Y) draw]
      exact accepted
    simp only [h, ite_eq_left, accepted', le_refl]
  · simp only [h, ite_false]
    split
    · exact mul_nonneg (FiniteDistribution.nonnegative _ _) (FiniteDistribution.nonnegative _ _)
    · rfl

def responses (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (mask : Fin k → Bool)
    (_ : RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits Q)) :
    StochasticBound.Responses (Fin k) Q O N :=
  (firstResponse coordinates g policy (NativeExperiment.maskSet mask),
   secondResponse coordinates g policy (NativeExperiment.maskSet mask))

def success (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] D)).expectation
      (fun Y => fixedMapSuccess μ g policy (NativeExperiment.maskSet mask) Y)
omit [DecidableEq O] [DecidableEq N] in
theorem success_le_native_stochastic (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    success μ g policy β hβ₀ hβ₁ ≤
      StochasticBound.nativeStochasticSuccess k μ g β hβ₀ hβ₁
        (responses coordinates g policy) := by
  unfold success StochasticBound.nativeStochasticSuccess responses
  apply expectation_mono
  intro mask
  rw [← uniform_maps_to_bits coordinates]
  exact expectation_mono _ (fun Y => fixedMapSuccess_le coordinates μ g policy _ Y)

omit [DecidableEq O] [DecidableEq N] in
theorem success_le_some_native (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    ∃ strategy : NativeExperiment.MaskStrategy k Q O N,
      success μ g policy β hβ₀ hβ₁ ≤ NativeExperiment.success k μ g β hβ₀ hβ₁ strategy := by
  obtain ⟨strategy, h⟩ := StochasticBound.native_stochastic_le_deterministic
    k μ g β hβ₀ hβ₁ (responses coordinates g policy)
  exact ⟨strategy, (success_le_native_stochastic coordinates μ g policy β hβ₀ hβ₁).trans h⟩

end Clean.ActualAdviceStochasticBridge

/-! Section 5's clean bound for actual local linear-advice policies. The
sampling correspondence, private response conversion, weighted conditional
product law, and alphabet-independent repetition estimate are all invoked as
proved theorems. No sampler or repeated-game bound is an input hypothesis. -/

namespace Clean.ActualAdviceBound

open Foundations.Games Integration.BinaryLinear
open Soundness
open AnswerBridge

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D] [Fintype D]
  [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]


/-- Arbitrary local randomized point policies obey the same bound. Complete
deterministic response tables may be chosen after the public mask/advice is
fixed, but before the remaining question pair is drawn. -/
theorem stochastic_success_le_dimension (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : ActualAdviceStochasticBridge.Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card D ≤ 2 ^ (dimW + rs)) :
    ActualAdviceStochasticBridge.success (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  have hcard' : Fintype.card (Experiment.Coefficient Q) ≤ 2 ^ (dimW + rs) :=
    (Fintype.card_congr (bitsCoordinatesEquiv coordinates).symm).le.trans hcard
  obtain ⟨strategy, h⟩ := ActualAdviceStochasticBridge.success_le_some_native coordinates
    (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁
  exact h.trans (Bound.native_clean_success_le_dimension k g ω β hβ₀ hβ₁
    strategy distinct hopt dimW rs hcard')

theorem stochastic_success_le_dimension_finite [FiniteDimensional F2 D]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : ActualAdviceStochasticBridge.Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card D ≤ 2 ^ (dimW + rs)) :
    ActualAdviceStochasticBridge.success (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k :=
  stochastic_success_le_dimension finiteCoordinates g ω policy β hβ₀ hβ₁
    distinct hopt dimW rs hcard

end Clean.ActualAdviceBound

/-!
The actual finite advice law. Uniform independent hidden/complement maps induce
the exact uniform visible-map law, including for rank-deficient public maps.
The whole-table comparison retains an arbitrary common occurrence/public-data
law, so weighted occurrence sampling is not replaced by uniform IDs.
-/

namespace Decoder.AdviceLaw

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open ConditionalIncidences RawPartnerTarget RawMapLaw
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Clean

attribute [local instance] Classical.propDecidable

section VisibleMap

variable {k : ℕ} {K W R : Type}
  [AddCommGroup K] [Module F2 K] [Fintype K]
  [AddCommGroup W] [Module F2 W] [Fintype W]
  [AddCommGroup R] [Module F2 R] [Fintype R]

/-- The precise visible table `(T,A M)`, with the second component in its
actual attainable range. The argument order is complement, hidden matrix. -/
def visibleMap (A : K →ₗ[F2] R) {J : Finset (Fin k)}
    (T : RawPoint J →ₗ[F2] W) (M : RawPoint J →ₗ[F2] K) :
    RawPoint J →ₗ[F2] (W × A.range) :=
  T.prod (A.rangeRestrict.comp M)


def rawMapPairCoefficientsEquiv (J : Finset (Fin k)) :
    ((RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K)) ≃
      (RawSlot J → W × K) :=
  (Equiv.prodCongr (rawMapEquiv J W).symm (rawMapEquiv J K).symm).trans
    (Equiv.arrowProdEquivProdArrow (RawSlot J) (fun _ => W) (fun _ => K)).symm

omit [Fintype K] [Fintype W] [Fintype R] in
theorem visibleMap_raw (A : K →ₗ[F2] R) (J : Finset (Fin k))
    (TM : (RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K)) :
    visibleMap A TM.1 TM.2 = rawMap J (W × A.range)
      (AdviceImageLaw.visibleCoefficients A (rawMapPairCoefficientsEquiv J TM)) := by
  exact (rawMap_coefficients J (W × A.range) (visibleMap A TM.1 TM.2)).symm

/-- Equality for every observable proves the whole joint visible-map law. -/
theorem uniform_visible_maps (A : K →ₗ[F2] R) (J : Finset (Fin k))
    (H : (RawPoint J →ₗ[F2] (W × A.range)) → ℝ) :
    (𝔼 TM : (RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K),
      H (visibleMap A TM.1 TM.2)) =
      𝔼 Y : RawPoint J →ₗ[F2] (W × A.range), H Y := by
  calc
    _ = 𝔼 columns : RawSlot J → W × K,
        H (rawMap J (W × A.range) (AdviceImageLaw.visibleCoefficients A columns)) := by
      apply Fintype.expect_equiv (rawMapPairCoefficientsEquiv J)
      intro TM
      rw [visibleMap_raw]
    _ = 𝔼 gamma : RawSlot J → W × A.range, H (rawMap J (W × A.range) gamma) :=
      AdviceImageLaw.uniform_visible_coefficients (I := RawSlot J) (W := W) A
        (fun gamma : RawSlot J → W × A.range => H (rawMap J (W × A.range) gamma))
    _ = _ := PaddedLaw.uniform_rawMaps J H

theorem uniform_visible_maps_expectation (A : K →ₗ[F2] R) (J : Finset (Fin k))
    (H : (RawPoint J →ₗ[F2] (W × A.range)) → ℝ) :
    (FiniteDistribution.uniform
      ((RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K))).expectation
        (fun TM => H (visibleMap A TM.1 TM.2)) =
      (FiniteDistribution.uniform (RawPoint J →ₗ[F2] (W × A.range))).expectation H := by
  simpa only [FiniteDistribution.expectation_uniform,
    ← Fintype.expect_eq_sum_div_card] using uniform_visible_maps A J H

variable {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

/-- Actual success starts with genuinely sampled hidden and complement maps.
The iid incidence law includes every slot choice, including unused choices at
full positions. Policies receive only their respective visible table. -/
def actualSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (A : K →ₗ[F2] R)
    (policy : ActualAdviceStochasticBridge.Policies k g (W × A.range))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      ((RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] W) ×
        (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] K))).expectation fun TM =>
      ActualAdviceStochasticBridge.fixedMapSuccess μ g policy
        (NativeExperiment.maskSet mask) (visibleMap A TM.1 TM.2)

omit [DecidableEq O] [Fintype N] [DecidableEq N] in
theorem actualSuccess_eq_cleanSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (A : K →ₗ[F2] R)
    (policy : ActualAdviceStochasticBridge.Policies k g (W × A.range))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    actualSuccess μ g A policy β hβ₀ hβ₁ =
      ActualAdviceStochasticBridge.success μ g policy β hβ₀ hβ₁ := by
  unfold actualSuccess ActualAdviceStochasticBridge.success
  apply FiniteDistribution.expectation_congr
  intro mask
  exact uniform_visible_maps_expectation A (NativeExperiment.maskSet mask)
    (ActualAdviceStochasticBridge.fixedMapSuccess μ g policy (NativeExperiment.maskSet mask))

end VisibleMap

section WholeTable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]
  [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

def drawDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution ((Fin k → PaddedLaw.BlockDraw V) × V) where
  weight := PaddedLaw.drawWeights β k
  nonnegative dz := mul_nonneg
    ((SparseLaw.independentWeights_isProbability _
      (PaddedLaw.blockWeights_isProbability β hβ hβ') k).1 dz.1)
    (SparseLaw.uniformWeights_pos dz.2).le
  normalized := by
    rw [Fintype.sum_prod_type]
    simp only [PaddedLaw.drawWeights, ← Finset.mul_sum,
      (SparseLaw.uniformWeights_isProbability (α := V)).2, mul_one]
    exact (SparseLaw.independentWeights_isProbability _
      (PaddedLaw.blockWeights_isProbability β hβ hβ') k).2

def paddedDistribution (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (ActualHomogeneous.E k →ₗ[F2] V) :=
  (drawDistribution β hβ hβ').pushforward (fun dz => PaddedLaw.paddedMap rhs dz.1 dz.2)

/-- Padding adds an independent uniform affine intercept. The full map's
variation is therefore exactly the sparse slope variation used in constants. -/
theorem paddedDistribution_totalVariation_eq_slope (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (paddedDistribution (V := V) rhs β hβ hβ').totalVariation
      (FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V)) =
        UniqueGamesTheorem.Foundations.Information.totalVariation
          (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
          (SparseLaw.uniformWeights (Fin k → V × V)) := by
  exact PaddedLaw.paddedMapWeights_totalVariation_eq_slope rhs β


end WholeTable

section CommonLaw

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

/-- Keep the common outer datum while sampling its conditional table law. -/
def withKernel (μ : FiniteDistribution Ω) (p : Ω → FiniteDistribution Y) :
    FiniteDistribution (Ω × Y) where
  weight xy := μ.weight xy.1 * (p xy.1).weight xy.2
  nonnegative xy := mul_nonneg (μ.nonnegative _) ((p _).nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
    exact μ.normalized

theorem withKernel_totalVariation (μ : FiniteDistribution Ω)
    (p q : Ω → FiniteDistribution Y) :
    (withKernel μ p).totalVariation (withKernel μ q) =
      ∑ x, μ.weight x * (p x).totalVariation (q x) := by
  exact Foundations.Information.totalVariation_joint_common_weights
    μ.weight (fun x => (p x).weight) (fun x => (q x).weight) μ.nonnegative


end CommonLaw


/-- Common occurrence/public randomness preserves the exact slope variation. -/
theorem wholeAdvice_totalVariation_eq_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (withKernel (occurrences.product publicLaw)
      (fun ua => paddedDistribution (V := V) (fun j => rhs (ua.1 j)) β hβ hβ')).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) =
      UniqueGamesTheorem.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) := by
  rw [withKernel_totalVariation]
  simp_rw [paddedDistribution_totalVariation_eq_slope]
  rw [← Finset.sum_mul, (occurrences.product publicLaw).normalized, one_mul]


section HiddenRows

variable {k : ℕ} {K R : Type}
  [AddCommGroup K] [Module F2 K] [Fintype K]
  [AddCommGroup R] [Module F2 R] [Fintype R]

instance observedRowsFintype (J : Finset (Fin k)) (A : K →ₗ[F2] R) :
    Fintype (AdviceFibers.ObservedRow (E := RawPoint J) A) := Fintype.ofFinite _


end HiddenRows

section ProjectionSeeds

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]

/-- The actual two-stage sampler retains both its projection choices and its
uniform map on that projected target. Thus target advice is not forgotten. -/
abbrev ProjectionSeed (k : ℕ) (V : Type) [AddCommGroup V] [Module F2 V] :=
  Σ c : Fin k → PaddedLaw.ProjectionChoice,
    RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] V

def projectionSeedDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (ProjectionSeed k V) where
  weight s := PaddedLaw.choiceTupleWeight β s.1 * SparseLaw.uniformWeights _ s.2
  nonnegative s := mul_nonneg
    ((PaddedLaw.choiceTupleWeight_isProbability β hβ hβ').1 s.1)
    (SparseLaw.uniformWeights_pos s.2).le
  normalized := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum, (SparseLaw.uniformWeights_isProbability).2, mul_one]
    exact (PaddedLaw.choiceTupleWeight_isProbability β hβ hβ').2

def projectSeedMap (rhs : Fin k → Bool) (s : ProjectionSeed k V) :
    ActualHomogeneous.E k →ₗ[F2] V :=
  s.2.comp (rawProjection rhs (PaddedLaw.choiceMask s.1) (PaddedLaw.choiceSlots s.1))

variable [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

theorem projectionSeed_expectation (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (projectionSeedDistribution β hβ hβ').expectation (fun s => H (projectSeedMap rhs s)) =
      (paddedDistribution rhs β hβ hβ').expectation H := by
  rw [paddedDistribution, FiniteDistribution.expectation_pushforward]
  change (∑ s : ProjectionSeed k V,
      PaddedLaw.choiceTupleWeight β s.1 * SparseLaw.uniformWeights _ s.2 *
        H (projectSeedMap rhs s)) =
    ∑ dz, PaddedLaw.drawWeights β k dz * H (PaddedLaw.paddedMap rhs dz.1 dz.2)
  rw [PaddedLaw.actual_projection_mixture_expectation, Fintype.sum_sigma]
  simp only [mul_assoc, ← Finset.mul_sum, PaddedLaw.sum_uniformWeights_mul,
    projectSeedMap]

theorem projectionSeed_pushforward (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (projectionSeedDistribution β hβ hβ').pushforward (projectSeedMap (V := V) rhs) =
      paddedDistribution rhs β hβ hβ' := by
  apply FiniteDistribution.eq_of_weight_eq
  intro Y
  have h := projectionSeed_expectation rhs β hβ hβ' (fun X => if X = Y then 1 else 0)
  simpa [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite,
    PaddedLaw.pushforwardWeight] using h

end ProjectionSeeds

section ActualDraw

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

/-- Convert the actual two-stage seed into the full hidden experiment. The
second summand of the seed remains available for the target-side observation. -/
def seedToActualDraw (occ : Fin k → Id) (A : K →ₗ[F2] R)
    (s : ProjectionSeed k (K × W)) : AdviceExperiment.Draw k Id K W R where
  singletons := PaddedLaw.choiceMask s.1
  occurrences := occ
  positions := PaddedLaw.choiceSlots s.1
  rowMap := A
  hiddenMatrix := (LinearMap.fst F2 K W).comp s.2
  complement := (LinearMap.snd F2 K W).comp s.2


end ActualDraw

section MaskSlots

def choiceDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution PaddedLaw.ProjectionChoice where
  weight := PaddedLaw.choiceWeight β
  nonnegative := (PaddedLaw.choiceWeight_isProbability β hβ hβ').1
  normalized := (PaddedLaw.choiceWeight_isProbability β hβ hβ').2

/-- Full positions discard their auxiliary slot; singleton positions retain it. -/
def maskSlotChoice (p : Bool × Fin 3) : PaddedLaw.ProjectionChoice :=
  if p.1 then some p.2 else none

theorem maskSlotChoice_pushforward (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((bernoulli β hβ hβ').product (FiniteDistribution.uniform (Fin 3))).pushforward
      maskSlotChoice = choiceDistribution β hβ hβ' := by
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.uniform, Clean.bernoulli, choiceDistribution]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases c <;> simp [maskSlotChoice, PaddedLaw.choiceWeight, div_eq_mul_inv]
  ring

def choicesOfMaskSlots {k : ℕ} (mask : Fin k → Bool) (slots : Fin k → Fin 3) :
    Fin k → PaddedLaw.ProjectionChoice :=
  fun j => maskSlotChoice (mask j, slots j)

/-- The Option sampler is exactly the Bernoulli-mask sampler with independent
uniform slots at every position, including the full positions. This identity
allows arbitrary functions of the retained choices. -/
theorem choices_expectation {k : ℕ} (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (H : (Fin k → PaddedLaw.ProjectionChoice) → ℝ) :
    ((choiceDistribution β hβ hβ').iid k).expectation H =
      ((bernoulli β hβ hβ').iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
          H (choicesOfMaskSlots mask slots))) := by
  rw [← maskSlotChoice_pushforward, FiniteDistribution.iid_pushforward,
    FiniteDistribution.expectation_pushforward, NativeExperiment.expectation_iid_product,
    FiniteDistribution.iid_uniform]
  rfl

theorem choices_mask {k : ℕ} (mask : Fin k → Bool) (slots : Fin k → Fin 3) :
    PaddedLaw.choiceMask (choicesOfMaskSlots mask slots) =
      NativeExperiment.maskSet mask := by
  ext j
  cases h : mask j <;>
    simp [PaddedLaw.choiceMask, NativeExperiment.maskSet, choicesOfMaskSlots,
      maskSlotChoice, h]

theorem choices_active_slot {k : ℕ} (mask : Fin k → Bool) (slots : Fin k → Fin 3)
    (j : Fin k) (hj : mask j = true) :
    PaddedLaw.choiceSlots (choicesOfMaskSlots mask slots) j = PaddedLaw.decodeSlot (slots j) := by
  simp [PaddedLaw.choiceSlots, PaddedLaw.choiceSlot, choicesOfMaskSlots, maskSlotChoice, hj]

/-- The same identity with the entire original target map retained. This is
the full two-stage seed law, not merely the law of its padded marginal. -/
theorem projectionSeed_mask_slots_expectation {k : ℕ} {V : Type}
    [AddCommGroup V] [Module F2 V] [Fintype V]
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (H : ProjectionSeed k V → ℝ) :
    (projectionSeedDistribution β hβ hβ').expectation H =
      ((bernoulli β hβ hβ').iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
          (FiniteDistribution.uniform
            (RawPoint (PaddedLaw.choiceMask (choicesOfMaskSlots mask slots)) →ₗ[F2] V)).expectation
              (fun Y => H ⟨choicesOfMaskSlots mask slots, Y⟩))) := by
  calc
    _ = ((choiceDistribution β hβ hβ').iid k).expectation (fun c =>
        (FiniteDistribution.uniform (RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] V)).expectation
          (fun Y => H ⟨c, Y⟩)) := by
      simp only [FiniteDistribution.expectation, Fintype.sum_sigma,
        projectionSeedDistribution, FiniteDistribution.iid, choiceDistribution,
        FiniteDistribution.uniform, SparseLaw.uniformWeights,
        PaddedLaw.choiceTupleWeight, Finset.mul_sum, mul_assoc]
    _ = _ := choices_expectation β hβ hβ' _

end MaskSlots

section FullSeedLaw

variable {Ω Z Y : Type*} [Fintype Ω] [Fintype Z] [Fintype Y]

theorem product_pushforward_withKernel (μ : FiniteDistribution Ω)
    (ν : FiniteDistribution Z) (f : Ω → Z → Y) :
    (μ.product ν).pushforward (fun xz => (xz.1, f xz.1 xz.2)) =
      withKernel μ (fun x => ν.pushforward (f x)) := by
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product, withKernel]
  rw [Fintype.sum_prod_type]
  simp only [Prod.mk.injEq, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum, mul_ite, mul_zero]

end FullSeedLaw

/-- A finite hidden sample whose actual Draw is `seedToActualDraw`. -/
def fullSeedLaw {k : ℕ} {Id A V : Type} [Fintype Id] [Fintype A]
    [AddCommGroup V] [Module F2 V] [Fintype V]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :=
  (occurrences.product publicLaw).product (projectionSeedDistribution (k := k) (V := V) β hβ hβ')

def fullSeedPad {k : ℕ} {Id A V : Type} [AddCommGroup V] [Module F2 V]
    (rhs : Id → Bool) (s : ((Fin k → Id) × A) × ProjectionSeed k V) :
    ((Fin k → Id) × A) × (ActualHomogeneous.E k →ₗ[F2] V) :=
  (s.1, projectSeedMap (fun j => rhs (s.1.1 j)) s.2)

theorem fullSeed_pad_law {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward (fullSeedPad rhs) =
      withKernel (occurrences.product publicLaw)
        (fun ua => paddedDistribution (V := V) (fun j => rhs (ua.1 j)) β hβ hβ') := by
  unfold fullSeedLaw fullSeedPad
  rw [product_pushforward_withKernel (occurrences.product publicLaw)
    (projectionSeedDistribution (k := k) (V := V) β hβ hβ')
    (fun ua seed => projectSeedMap (fun j => rhs (ua.1 j)) seed)]
  congr 1
  funext ua
  exact projectionSeed_pushforward (fun j => rhs (ua.1 j)) β hβ hβ'


theorem fullSeed_totalVariation_eq_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward
      (fullSeedPad rhs)).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) =
      UniqueGamesTheorem.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) := by
  rw [fullSeed_pad_law]
  exact wholeAdvice_totalVariation_eq_slope occurrences publicLaw rhs β hβ hβ'

theorem fullSeed_totalVariation_le_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward
      (fullSeedPad rhs)).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) ≤
      UniqueGamesTheorem.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) :=
  (fullSeed_totalVariation_eq_slope occurrences publicLaw rhs β hβ hβ').le

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

abbrev FullSeed (k : ℕ) (Id K W R : Type)
    [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
    [AddCommGroup R] [Module F2 R] :=
  ((Fin k → Id) × (K →ₗ[F2] R)) × ProjectionSeed k (K × W)

/-- Complete visible conditioning data: occurrences, public map, projection
choices, the entire complement map, and precisely the attainable rows. -/
abbrev CompleteData (k : ℕ) (Id K W R : Type)
    [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
    [AddCommGroup R] [Module F2 R] :=
  Σ ua : (Fin k → Id) × (K →ₗ[F2] R),
    Σ c : Fin k → PaddedLaw.ProjectionChoice,
      (RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] W) ×
        AdviceFibers.ObservedRow (E := RawPoint (PaddedLaw.choiceMask c)) ua.2

abbrev PrivateMap (d : CompleteData k Id K W R) :=
  RawPoint (PaddedLaw.choiceMask d.2.1) →ₗ[F2] d.1.2.ker

def targetObservationEquiv (J : Finset (Fin k)) (A : K →ₗ[F2] R) :
    (RawPoint J →ₗ[F2] (K × W)) ≃
      ((RawPoint J →ₗ[F2] W) × AdviceFibers.ObservedRow (E := RawPoint J) A) ×
        (RawPoint J →ₗ[F2] A.ker) :=
  (LinearMap.prodEquiv F2).toEquiv.symm |>.trans
    (Equiv.prodComm _ _) |>.trans
    (Equiv.prodCongr (Equiv.refl _) (AdviceFibers.observationEquiv A)) |>.trans
    (Equiv.prodAssoc _ _ _).symm

/-- A global bijection retains all actual visible data, with exactly one
uniform kernel-valued matrix left after conditioning. -/
def fullSeedCoordinatesEquiv :
    FullSeed k Id K W R ≃ Σ d : CompleteData k Id K W R, PrivateMap d :=
  ((Equiv.sigmaEquivProd ((Fin k → Id) × (K →ₗ[F2] R))
      (ProjectionSeed k (K × W))).symm.trans
    (Equiv.sigmaCongrRight fun (ua : (Fin k → Id) × (K →ₗ[F2] R)) =>
      Equiv.sigmaCongrRight fun c => targetObservationEquiv (PaddedLaw.choiceMask c) ua.2)).trans
    { toFun := fun p => ⟨⟨p.1, p.2.1, p.2.2.1⟩, p.2.2.2⟩
      invFun := fun p => ⟨p.1.1, p.1.2.1, p.1.2.2, p.2⟩
      left_inv := fun p => by rcases p with ⟨ua, c, ⟨T, S⟩, N⟩; rfl
      right_inv := fun p => by rcases p with ⟨⟨ua, c, T, S⟩, N⟩; rfl }

def completeObserve (s : FullSeed k Id K W R) : CompleteData k Id K W R :=
  (fullSeedCoordinatesEquiv s).1

def completeAssemble (d : CompleteData k Id K W R) (N : PrivateMap d) :
    FullSeed k Id K W R :=
  fullSeedCoordinatesEquiv.symm ⟨d, N⟩


@[simp] theorem completeObserve_assemble (d : CompleteData k Id K W R)
    (N : PrivateMap d) : completeObserve (completeAssemble d N) = d :=
  congrArg Sigma.fst (fullSeedCoordinatesEquiv.apply_symm_apply ⟨d, N⟩)

/-- Exact equivalence for a fiber of the complete observation, not just the
marginal row observation. This is the input for finite conditioning. -/
def completeFiberEquiv (d : CompleteData k Id K W R) :
    PrivateMap d ≃ {s : FullSeed k Id K W R // completeObserve s = d} :=
  ((Equiv.subtypeEquiv fullSeedCoordinatesEquiv (fun _ => Iff.rfl)).trans
    (Equiv.sigmaSubtype d)).symm

@[simp] theorem completeFiberEquiv_val (d : CompleteData k Id K W R) (N : PrivateMap d) :
    (completeFiberEquiv d N).val = completeAssemble d N := rfl

/-- The actual Draw obtained from the complete-data fiber coordinates. -/
def completeDraw (d : CompleteData k Id K W R) (N : PrivateMap d) :
    AdviceExperiment.Draw k Id K W R where
  singletons := PaddedLaw.choiceMask d.2.1
  occurrences := d.1.1
  positions := PaddedLaw.choiceSlots d.2.1
  rowMap := d.1.2
  hiddenMatrix := AdviceFibers.assemble d.1.2 (AdviceFibers.observedBase d.1.2 d.2.2.2) N
  complement := d.2.2.1

theorem completeDraw_seed (d : CompleteData k Id K W R) (N : PrivateMap d) :
    seedToActualDraw (completeAssemble d N).1.1 (completeAssemble d N).1.2
      (completeAssemble d N).2 = completeDraw d N := rfl

theorem completeDraw_rows (d : CompleteData k Id K W R) (N : PrivateMap d) :
    (completeDraw d N).rowMap.comp (completeDraw d N).hiddenMatrix = d.2.2.2.val := by
  exact (AdviceFibers.observed_assemble _ _ N).trans
    (AdviceFibers.observedBase_property _ _)

theorem completeDraw_left (rhs : Id → F2) (d : CompleteData k Id K W R)
    (N : PrivateMap d) :
    AdviceExperiment.leftObservation rhs (completeDraw d N) = {
      occurrences := d.1.1, rowMap := d.1.2,
      complement := d.2.2.1.comp (rawProjection (fun j => toBit (rhs (d.1.1 j)))
        (PaddedLaw.choiceMask d.2.1) (PaddedLaw.choiceSlots d.2.1)),
      rows := d.2.2.2.val.comp (rawProjection (fun j => toBit (rhs (d.1.1 j)))
        (PaddedLaw.choiceMask d.2.1) (PaddedLaw.choiceSlots d.2.1)) } := by
  simp only [AdviceExperiment.leftObservation, completeDraw_rows]
  rfl


variable [Fintype Id] [Fintype K] [Fintype W] [Fintype R] [Fintype (K →ₗ[F2] R)]

def completeWeight (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (d : CompleteData k Id K W R) : ℝ :=
  (occurrences.weight d.1.1 * publicLaw.weight d.1.2) *
    (PaddedLaw.choiceTupleWeight β d.2.1 *
      (1 / (Fintype.card (RawPoint (PaddedLaw.choiceMask d.2.1) →ₗ[F2] (K × W)) : ℝ)))

omit [Fintype R] in
/-- The actual law has exactly constant point weights on every fiber of all
observed data, even for arbitrary occurrence and public-map laws. -/
theorem fullSeed_weight_observed (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) (s : FullSeed k Id K W R) :
    (fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').weight s =
      completeWeight occurrences publicLaw β (completeObserve s) := rfl

omit [Fintype R] in
theorem fullSeed_weight_fiber (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) (d : CompleteData k Id K W R)
    (s : FullSeed k Id K W R) (hs : completeObserve s = d) :
    (fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').weight s =
      completeWeight occurrences publicLaw β d := by
  rw [fullSeed_weight_observed, hs]

end Decoder.AdviceLaw

end UniqueGamesTheorem

end

end OAI
