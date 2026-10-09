/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Decoding.ActualAdviceStochasticBridgeLemmas
import OAI.Computability.UniqueGames.Decoding.ActualSpectralLemmas
import OAI.Computability.UniqueGames.Decoding.AdviceImageLaw
import OAI.Computability.UniqueGames.Decoding.VisiblePoliciesLemmas
import OAI.Computability.UniqueGames.Decoding.VisibleTransferLemmas

namespace OAI

section

/-!
The clean-coordinate upper bound for the actual private-decoding policies.
At every fixed public map `A`, the visible coefficient space is
`Vector d × A.range`.  Its cardinality is at most `2^(d+rs)`, including when
`A` is rank deficient.  The true independent uniform maps `T,M`, the
Bernoulli mask, and all iid occurrence/position draws are retained by the
proved sampling equality, before averaging over the uniform public map.
-/

namespace UniqueGamesTheorem.Decoder.ActualAdviceUpper

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

instance publicMapFintype (s rs : Nat) : Fintype (Alphabet s →ₗ[F2] Vector rs) :=
  Fintype.ofInjective (fun A : Alphabet s →ₗ[F2] Vector rs => (A : Alphabet s → Vector rs))
    DFunLike.coe_injective

/-- The ordinary game uses actual occurrence IDs and actual variable names. -/
def sourceIncidence (S : Source) :
    IncidenceExtraction.Incidence (Fin S.occurrences) (Fin S.variables) where
  name := ActualGame.names S
  rhs e := (S.equation e).rhs

abbrev Visible (d : Nat) (A : Alphabet s →ₗ[F2] Vector rs) := Vector d × A.range

def complementMap {E : Type} [AddCommGroup E] [Module F2 E]
    (A : Alphabet s →ₗ[F2] Vector rs) (Y : E →ₗ[F2] Visible d A) :
    E →ₗ[F2] Vector d :=
  (LinearMap.fst F2 (Vector d) A.range).comp Y

def rowMap {E : Type} [AddCommGroup E] [Module F2 E]
    (A : Alphabet s →ₗ[F2] Vector rs) (Y : E →ₗ[F2] Visible d A) :
    E →ₗ[F2] Vector rs :=
  A.range.subtype.comp ((LinearMap.snd F2 (Vector d) A.range).comp Y)

/-- Decode only the data visible to the first player. -/
def fullInput (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (occ : Fin k → Fin S.occurrences)
    (Y : ActualHomogeneous.E k →ₗ[F2] Visible d A) :
    VisiblePolicies.LeftInput S k s d (Vector rs) where
  occurrences := occ
  rowMap := A
  complement := complementMap A Y
  rows := rowMap A Y

/-- Decode only the displayed question and the visible row/complement maps. -/
def projectedInput (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Visible d A) :
    VisiblePolicies.RightInput S J s d (Vector rs) where
  question := O
  rowMap := A
  complement := complementMap A Y
  rows := rowMap A Y

/-- Actual observation-local stochastic policies, in the exact advice space
used by the clean-coordinate experiment.  Public `A` is fixed before questions. -/
def policies (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) :
    Clean.ActualAdviceStochasticBridge.Policies k (sourceIncidence S) (Visible d A) where
  first _ occ Y := VisiblePolicies.leftPolicy good (fullInput S A occ Y)
  second J O Y := VisiblePolicies.rightPolicy S labeling J (projectedInput S A J O Y)

/-- The real draw corresponding to a fixed mask and the independently sampled
complement and hidden matrices. -/
def actualDraw (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector rs) where
  singletons := J
  occurrences := occ
  positions := slot
  rowMap := A
  hiddenMatrix := M
  complement := T

theorem fullInput_actual (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    fullInput S A occ ((AdviceLaw.visibleMap A T M).comp
      (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) =
      AdviceExperiment.leftObservation (ActualGame.rhs S) (actualDraw S A J occ slot T M) :=
  rfl

theorem projectedInput_actual (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    projectedInput S A J (RawPrivateTable.supported J (ActualGame.names S) occ slot)
        (AdviceLaw.visibleMap A T M) =
      (AdviceExperiment.rightObservation (ActualGame.names S)
        (actualDraw S A J occ slot T M)).2 :=
  rfl

/-- The product of the two local policy kernels is literally the private
decoder's observed agreement probability, before any expectations are taken. -/
theorem policyAgreement_actual (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) (J : Finset (Fin k))
    (occ : Fin k → Fin S.occurrences) (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    (((policies S labeling good A).first J occ
        ((AdviceLaw.visibleMap A T M).comp
          (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))).product
      ((policies S labeling good A).second J
        (RawPrivateTable.supported J (ActualGame.names S) occ slot)
        (AdviceLaw.visibleMap A T M))).probability
        (fun answers => decide
          (RawPrivateTable.projection J (ActualGame.rhs S) occ slot answers.1.val =
            answers.2.val)) =
      VisiblePolicies.observedAgreement S labeling good (actualDraw S A J occ slot T M) := by
  dsimp only [policies, sourceIncidence]
  rw [fullInput_actual S A J occ slot T M, projectedInput_actual S A J occ slot T M]
  rfl

/-- The clean experiment's indexed slot is exactly the actual bit projection;
this includes the third-position parity intercept. -/
theorem source_projection_eq (S : Source) (J : Finset (Fin k))
    (draw : Fin k → Fin S.occurrences × Fin 3) :
    Clean.ActualAdviceBridge.projection (sourceIncidence S) J draw =
      RawPrivateTable.projection J (ActualGame.rhs S) (fun j => (draw j).1)
        (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) := by
  simp only [Clean.ActualAdviceBridge.projection, sourceIncidence,
    RawPrivateTable.projection, ActualGame.rhs, toBit_ofBit]

theorem fixed_public_map_bound
    {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (A : Alphabet s →ₗ[F2] Vector rs)
    (policy : Clean.ActualAdviceStochasticBridge.Policies k g (Visible d A))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) :
    AdviceLaw.actualSuccess (Clean.IncidenceGap.slotLaw ω) g A policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  rw [AdviceLaw.actualSuccess_eq_cleanSuccess]
  exact Clean.ActualAdviceBound.stochastic_success_le_dimension_finite g ω policy
    β hβ₀ hβ₁ distinct hopt d rs (Clean.AdviceImageLaw.visible_card_binary_le d rs A)

/-- Rank deficiency is allowed separately at every public-map outcome. -/
theorem public_map_average_bound
    {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : (A : Alphabet s →ₗ[F2] Vector rs) →
      Clean.ActualAdviceStochasticBridge.Policies k g (Visible d A))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) :
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun A => AdviceLaw.actualSuccess (Clean.IncidenceGap.slotLaw ω) g A
          (policy A) β hβ₀ hβ₁) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  calc
    _ ≤ (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun _ => (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k) :=
      Clean.ActualAdviceBridge.expectation_mono _
        (fun A => fixed_public_map_bound g ω A (policy A) β hβ₀ hβ₁ distinct hopt)
    _ = _ := by
      rw [FiniteDistribution.expectation, ← Finset.sum_mul,
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).normalized, one_mul]


end

end UniqueGamesTheorem.Decoder.ActualAdviceUpper

end

section

/-!
The stochastic clean upper bound applies to the literal agreement of the two
actual local decoders.  The equality below retains every sampled mask, all
occurrence/position draws, and both independently uniform target maps.
-/

namespace UniqueGamesTheorem.Decoder.ActualAdviceSampling

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource ActualAdviceUpper

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}


theorem fixedMapSuccess_eq_observed (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (μ : FiniteDistribution (Fin S.occurrences × Fin 3))
    (A : Alphabet s →ₗ[F2] Vector rs) (J : Finset (Fin k))
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    Clean.ActualAdviceStochasticBridge.fixedMapSuccess μ (sourceIncidence S)
      (policies S labeling good A) J (AdviceLaw.visibleMap A T M) =
      (FiniteDistribution.table (fun _ : Fin k => μ)).expectation (fun draw =>
        VisiblePolicies.observedAgreement S labeling good
          (actualDraw S A J (fun j => (draw j).1)
            (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) T M)) := by
  unfold Clean.ActualAdviceStochasticBridge.fixedMapSuccess
  apply FiniteDistribution.expectation_congr
  intro draw
  rw [source_projection_eq]
  exact policyAgreement_actual S labeling good A J (fun j => (draw j).1)
    (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) T M


end

end UniqueGamesTheorem.Decoder.ActualAdviceSampling

end

section

/-! The complete-data conditional law of the actual projected experiment.
The residual private matrix is uniform even when the occurrence law is
weighted and the public row map has deficient rank. -/

namespace UniqueGamesTheorem.Decoder.ActualConditionalLaw

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

section Conditioning

variable {k : ℕ} {Id K W R : Type}
    [Fintype Id] [AddCommGroup K] [Module F2 K] [Fintype K]
    [AddCommGroup W] [Module F2 W] [Fintype W]
    [AddCommGroup R] [Module F2 R] [Fintype R]

theorem probability_condition_complete
    (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (d : AdviceLaw.CompleteData k Id K W R)
    (slice event : AdviceLaw.FullSeed k Id K W R → Bool)
    (positive : 0 < (AdviceLaw.fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').probability
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve d slice)) :
    ((AdviceLaw.fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').condition
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve d slice) positive).probability event =
        𝔼 N : {N : AdviceLaw.PrivateMap d // slice (AdviceLaw.completeAssemble d N) = true},
          if event (AdviceLaw.completeAssemble d N.val) then (1 : ℝ) else 0 := by
  exact UniformFibers.conditional_probability
    (AdviceLaw.fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ')
    AdviceLaw.completeObserve d slice event positive
    (AdviceLaw.completeWeight occurrences publicLaw β d)
    (AdviceLaw.fullSeed_weight_fiber occurrences publicLaw β hβ hβ' d)
    (AdviceLaw.completeFiberEquiv d)

end Conditioning

section Policy

variable {k s d r : ℕ}

/-- Both provers' answers, and their equality predicate, are fixed on the
complete observation fiber. Only the hidden matrix varies within that fiber. -/
theorem observedAgreement_completeDraw (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (N N' : AdviceLaw.PrivateMap data) :
    VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data N) =
      VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data N') := by
  unfold VisiblePolicies.observedAgreement
  rw [AdviceLaw.completeDraw_left, AdviceLaw.completeDraw_left]
  simp only [AdviceExperiment.rightObservation, AdviceLaw.completeDraw_rows]
  rfl

def datumAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) : ℝ :=
  VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data 0)

theorem datumAgreement_nonneg (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) :
    0 ≤ datumAgreement S labeling good data :=
  FiniteDistribution.probability_nonnegative _ _

/-- The actual success observable factors through the complete visible datum;
this justifies integrating a lower bound over visible-witness probability. -/
theorem observedAgreement_seed (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (x : AdviceLaw.FullSeed k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) :
    VisiblePolicies.observedAgreement S labeling good
      (AdviceLaw.seedToActualDraw x.1.1 x.1.2 x.2) =
        datumAgreement S labeling good (AdviceLaw.completeObserve x) := by
  let y := AdviceLaw.fullSeedCoordinatesEquiv x
  have hx : AdviceLaw.completeAssemble y.1 y.2 = x :=
    AdviceLaw.fullSeedCoordinatesEquiv.symm_apply_apply x
  rw [← hx, AdviceLaw.completeDraw_seed]
  change VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw y.1 y.2) =
    datumAgreement S labeling good (AdviceLaw.completeObserve (AdviceLaw.completeAssemble y.1 y.2))
  rw [AdviceLaw.completeObserve_assemble]
  exact observedAgreement_completeDraw S labeling good y.1 y.2 0

end Policy
end
end UniqueGamesTheorem.Decoder.ActualConditionalLaw

end

section

/-! The selected full-table events pulled back to the genuine projected
experiment. The comparison space forgets the projection, while complete data
retains it only for the subsequent finite conditional-law argument. -/

namespace UniqueGamesTheorem.Decoder.ActualSeedEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

abbrev Seed (S : Source) (k s d r : ℕ) :=
  AdviceLaw.FullSeed k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)

abbrev Datum (S : Source) (k s d r : ℕ) :=
  AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)

def law (S : Source) (k s d r : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (Seed S k s d r) :=
  AdviceLaw.fullSeedLaw (V := Ambient s d)
    (FiniteDistribution.uniform (ActualGame.Question S k))
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)) β hβ hβ'

def draw {S : Source} {k s d r : ℕ} (x : Seed S k s d r) :=
  AdviceLaw.seedToActualDraw x.1.1 x.1.2 x.2

def pad (S : Source) (k s d r : ℕ) (x : Seed S k s d r) : ActualEvents.Sample S k s d r :=
  ActualEvents.fullTableEquiv S k s d r
    (AdviceLaw.fullSeedPad (fun i => toBit (ActualGame.rhs S i)) x)

def slice (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    Seed S k s d r → Bool :=
  fun x => ActualEvents.sliceEvent S k s d r labeling α (pad S k s d r x)

def targetHit (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    Seed S k s d r → Bool :=
  fun x => ActualEvents.targetHit S k s d r labeling α (pad S k s d r x)


theorem slice_eq_selectedEvent (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ)
    (x : Seed S k s d r) :
    slice S k s d r labeling α x = decide
      ((Inverse.RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
        (SelectedPolicies.fullTable S labeling
          (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
        (LinearMap.toMatrix' (draw x).rowMap)
        (MatrixCoordinates.mapEquiv k s (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x)))) :=
  rfl

theorem targetHit_eq_selectedMatch (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ)
    (x : Seed S k s d r) :
    targetHit S k s d r labeling α x = decide
      ((Inverse.RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
        (SelectedPolicies.fullTable S labeling
          (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
        (LinearMap.toMatrix' (draw x).rowMap)
        (MatrixCoordinates.mapEquiv k s (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x)))) :=
  rfl

/-- Positive selected-slice mass automatically supplies actual good left
advice; goodness is not an independent projected experiment assumption. -/
theorem slice_good (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ)
    (x : Seed S k s d r) (hx : slice S k s d r labeling α x = true) :
    SelectedPolicies.GoodAdvice S labeling α
      (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x)) := by
  rw [slice_eq_selectedEvent] at hx
  have h := (Inverse.RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent_good
    (SelectedPolicies.fullTable S labeling
      (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
    (LinearMap.toMatrix' (draw x).rowMap)
    (MatrixCoordinates.mapEquiv k s (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x)))
    (of_decide_eq_true hx)
  change (Inverse.RowErasureMatrix.family s (1 + 2 * k) r).GoodAdvice
    (SelectedPolicies.fullTable S labeling
      (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
    (LinearMap.toMatrix' (draw x).rowMap)
    (MatrixCoordinates.mapEquiv k r
      ((draw x).rowMap.comp (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x))))
  rw [MatrixCoordinates.mapEquiv_rowAdvice]
  exact h

end
end UniqueGamesTheorem.Decoder.ActualSeedEvents

end

end OAI
