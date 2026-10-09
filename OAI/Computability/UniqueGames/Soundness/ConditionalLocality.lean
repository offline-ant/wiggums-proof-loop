/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Soundness.ZeroInformationLemmas

namespace OAI

/-!
# Complete local private inputs after fixing H

The constructors here consume only the appropriate zero-set question tuple:
occurrences for the first player, names for the second. A single reference sample
from the positive observation fibre is fixed once as part of H-dependent advice.
It supplies arbitrary padding at hidden positions and never depends on the actual
remaining sample. The reconstruction theorems prove equality of the complete
question-plus-row input, and the row maps restrict to the actual equation spaces
as shown in `BinaryRowTransport.actual_pullbackRow`.
-/

namespace UniqueGamesTheorem.Soundness.ConditionalIncidences

noncomputable section

instance zeroBits (R : Type) : Zero (ZeroInformation.Bits R) :=
  ⟨ZeroInformation.zero⟩

def membershipBool {P : Type} [DecidableEq P] (J : Finset P) : P → Bool :=
  fun j => decide (j ∈ J)

def fullCoefficient {P R : Type} [DecidableEq P] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) (i : Fin 2) :
    P → ZeroInformation.Bits R :=
  fun j => if hj : j ∉ J then gamma (some (.inl (⟨j, hj⟩, i))) else ZeroInformation.zero

def singleCoefficient {P R : Type} [DecidableEq P] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) : P → ZeroInformation.Bits R :=
  fun j => if hj : j ∈ J then gamma (some (.inr ⟨j, hj⟩)) else ZeroInformation.zero

def fillHidden {P X : Type} [DecidableEq P] (K : Finset P)
    (fallback : P → X) (inside : PositionInside K → X) : P → X :=
  fun j => if hj : j ∈ K then inside ⟨j, hj⟩ else fallback j

theorem singleCoefficient_zero {P R : Type} [DecidableEq P]
    [Fintype R] [DecidableEq R] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) (j : P)
    (hj : j ∈ zeroSet J gamma) : singleCoefficient J gamma j = ZeroInformation.zero := by
  obtain ⟨hjJ, hz⟩ := (mem_zeroSet J gamma j).mp hj
  change gamma (some (.inr ⟨j, hjJ⟩)) = ZeroInformation.zero at hz
  simpa only [singleCoefficient, hjJ, ↓reduceDIte] using hz

theorem zeroSet_subset {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) : zeroSet J gamma ⊆ J := by
  intro j hj
  exact ((mem_zeroSet J gamma j).mp hj).choose

variable {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  (J : Finset P) (name : O → Fin 3 → N)
  (gamma : RawCoefficients J (ZeroInformation.Bits R))
  (observed : PositionOutside (zeroSet J gamma) → O × N)

def actualFirst (sample : Draw P O) : ZeroInformation.FirstInput P R O :=
  ZeroInformation.firstInput Finset.univ.toList (membershipBool J) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fun j => (sample j).1) (fun j => (sample j).2)

def actualSecond (sample : Draw P O) : ZeroInformation.SecondInput P R O N :=
  ZeroInformation.secondInput Finset.univ.toList (membershipBool J) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fun j => (sample j).1) (fun j => name (sample j).1 (sample j).2)

def localFirstFromH (reference : RawObservationFibre J name gamma observed)
    (insideOccurrences : PositionInside (zeroSet J gamma) → O) :
    ZeroInformation.FirstInput P R O :=
  ZeroInformation.firstInput Finset.univ.toList (membershipBool J) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fillHidden (zeroSet J gamma) (fun j => (reference.val.2 j).1) insideOccurrences)
    (fun j => ZeroInformation.decodeIndex name (reference.val.2 j).1
      (name (reference.val.2 j).1 (reference.val.2 j).2))

def localSecondFromH (reference : RawObservationFibre J name gamma observed)
    (insideNames : PositionInside (zeroSet J gamma) → N) :
    ZeroInformation.SecondInput P R O N :=
  ZeroInformation.secondInput Finset.univ.toList (membershipBool J) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fun j => (reference.val.2 j).1)
    (fillHidden (zeroSet J gamma)
      (fun j => name (reference.val.2 j).1 (reference.val.2 j).2) insideNames)

omit [DecidableEq R] in
theorem localFirstFromH_question_inside
    (reference : RawObservationFibre J name gamma observed)
    (insideOccurrences : PositionInside (zeroSet J gamma) → O)
    (j : PositionInside (zeroSet J gamma)) :
    (localFirstFromH J name gamma observed reference insideOccurrences).question j.val =
      insideOccurrences j := by
  simp [localFirstFromH, ZeroInformation.firstInput, fillHidden, j.property]

omit [DecidableEq R] in
theorem localSecondFromH_question_inside
    (reference : RawObservationFibre J name gamma observed)
    (insideNames : PositionInside (zeroSet J gamma) → N)
    (j : PositionInside (zeroSet J gamma)) :
    (localSecondFromH J name gamma observed reference insideNames).question j.val =
      Sum.inr (insideNames j) := by
  have hjJ : j.val ∈ J := zeroSet_subset J gamma j.property
  simp [localSecondFromH, ZeroInformation.secondInput, ZeroInformation.partnerQuestion,
    fillHidden, membershipBool, j.property, hjJ]

omit [Fintype P] [DecidableEq R] in
theorem outside_pair_agree (reference sample : RawObservationFibre J name gamma observed)
    (j : P) (hj : j ∉ zeroSet J gamma) :
    incidence name (reference.val.2 j) = incidence name (sample.val.2 j) := by
  exact congrFun (reference.property.2.trans sample.property.2.symm) ⟨j, hj⟩

omit [Fintype P] [DecidableEq R] in
theorem fillHidden_occurrences (reference sample : RawObservationFibre J name gamma observed) :
    fillHidden (zeroSet J gamma) (fun j => (reference.val.2 j).1)
        (fun j => (sample.val.2 j.val).1) =
      (fun j => (sample.val.2 j).1) := by
  funext j
  by_cases hj : j ∈ zeroSet J gamma
  · simp [fillHidden, hj]
  · simp only [fillHidden, hj, ↓reduceDIte]
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj)

omit [Fintype P] [DecidableEq R] in
theorem fillHidden_names (reference sample : RawObservationFibre J name gamma observed) :
    fillHidden (zeroSet J gamma)
        (fun j => name (reference.val.2 j).1 (reference.val.2 j).2)
        (fun j => name (sample.val.2 j.val).1 (sample.val.2 j.val).2) =
      (fun j => name (sample.val.2 j).1 (sample.val.2 j).2) := by
  funext j
  by_cases hj : j ∈ zeroSet J gamma
  · simp [fillHidden, hj]
  · simp only [fillHidden, hj, ↓reduceDIte]
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj)

/-- Equality of the entire first private input, including its row map. -/
theorem localFirstFromH_correct
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (reference sample : RawObservationFibre J name gamma observed) :
    localFirstFromH J name gamma observed reference (fun j => (sample.val.2 j.val).1) =
      actualFirst J gamma sample.val.2 := by
  unfold localFirstFromH actualFirst
  rw [fillHidden_occurrences J name gamma observed reference sample]
  unfold ZeroInformation.firstInput
  congr 1
  funext homogeneous x
  apply ZeroInformation.pullbackRow_index_independent
  intro j _ hz
  have hj : j ∉ zeroSet J gamma := fun hj => hz (singleCoefficient_zero J gamma j hj)
  have h := outside_pair_agree J name gamma observed reference sample j hj
  rw [show name (reference.val.2 j).1 (reference.val.2 j).2 =
      name (sample.val.2 j).1 (sample.val.2 j).2 from congrArg Prod.snd h,
    show (reference.val.2 j).1 = (sample.val.2 j).1 from
      congrArg (fun p : O × N => p.1) h]
  exact ZeroInformation.decodeIndex_name name distinct _ _

omit [DecidableEq R] in
/-- Equality of the entire second private input. The constructor requires no
occurrence, equation rhs, or slot from any position in K. -/
theorem localSecondFromH_correct (reference sample : RawObservationFibre J name gamma observed) :
    localSecondFromH J name gamma observed reference
        (fun j => name (sample.val.2 j.val).1 (sample.val.2 j.val).2) =
      actualSecond J name gamma sample.val.2 := by
  unfold localSecondFromH actualSecond
  rw [fillHidden_names J name gamma observed reference sample]
  unfold ZeroInformation.secondInput
  congr 1
  funext j
  by_cases hj : j ∈ J
  · simp [ZeroInformation.partnerQuestion, membershipBool, hj]
  · have h := outside_pair_agree J name gamma observed reference sample j
      (fun h => hj (zeroSet_subset J gamma h))
    simpa [ZeroInformation.partnerQuestion, membershipBool, incidence, hj] using
      congrArg (fun p : O × N => p.1) h

end

end UniqueGamesTheorem.Soundness.ConditionalIncidences

end OAI
