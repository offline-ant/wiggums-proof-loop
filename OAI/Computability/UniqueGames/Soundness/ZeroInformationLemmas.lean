/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Std

namespace OAI

namespace UniqueGamesTheorem.Soundness.ZeroInformation

/-! ## The observation fibre is a Cartesian product -/

section Fibres

variable {P X Y : Type} (hidden : P → Bool) (reveal : P → X → Y) (observed : P → Y)


end Fibres

/-! ## Exact weighted finite counting -/


/-! ## Position-indexed row maps -/

abbrev Bits (R : Type) := R → Bool

def zero {R : Type} : Bits R := fun _ => false

def add {R : Type} (a b : Bits R) : Bits R := fun r => a r ^^ b r

def scale {R : Type} (coefficient : Bits R) (bit : Bool) : Bits R :=
  fun r => coefficient r && bit

@[simp] theorem scale_zero {R : Type} (bit : Bool) :
    scale (zero : Bits R) bit = zero := by
  funext r
  simp [scale, zero]

def rowSum {P R : Type} (positions : List P) (term : P → Bits R) : Bits R :=
  positions.foldr (fun j acc => add (term j) acc) zero

theorem rowSum_congr {P R : Type} (positions : List P) (a b : P → Bits R)
    (h : ∀ j, a j = b j) : rowSum positions a = rowSum positions b := by
  have hab : a = b := funext h
  rw [hab]

/-- Raw row application after pulling back the retained coordinates along π.
`single` records J, and `omega` is indexed by positions, never by names. -/
def pullbackRow {P R : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (indices : P → Fin 3) (homogeneous : Bool) (x : P → Fin 3 → Bool) : Bits R :=
  add (scale zeta0 homogeneous) (rowSum positions fun j =>
    if single j then scale (omega j) (x j (indices j))
    else add (scale (zeta1 j) (x j 0)) (scale (zeta2 j) (x j 1)))

/-- Changing an index where its position coefficient is zero does not change the
entire row map. This is an equality for all ambient coordinates, so also on E_U. -/
theorem pullbackRow_index_independent {P R : Type} (positions : List P)
    (single : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (i i' : P → Fin 3)
    (agrees : ∀ j, single j = true → omega j ≠ zero → i j = i' j)
    (homogeneous : Bool) (x : P → Fin 3 → Bool) :
    pullbackRow positions single zeta0 zeta1 zeta2 omega i homogeneous x =
      pullbackRow positions single zeta0 zeta1 zeta2 omega i' homogeneous x := by
  unfold pullbackRow
  congr 1
  apply rowSum_congr
  intro j
  cases hs : single j
  · simp
  · simp only [↓reduceIte]
    by_cases hz : omega j = zero
    · simp [hz]
    · rw [agrees j hs hz]


/-! ## Complete private-input reconstruction -/

/-- A raw row function on ambient first-question coordinates. Restricting it to
the equation subspace gives the supplied map `Z_B π`. -/
abbrev FirstRow (P R : Type) := Bool → (P → Fin 3 → Bool) → Bits R

/-- A raw row function on ambient partner coordinates. -/
abbrev SecondRow (P R : Type) :=
  Bool → (P → Fin 3 → Bool) → (P → Bool) → Bits R

structure FirstInput (P R O : Type) where
  question : P → O
  row : FirstRow P R

/-- `Sum.inl o` records a full occurrence and `Sum.inr n` a single named bit.
The summand tag preserves the set J without exposing any retained index. -/
structure SecondInput (P R O N : Type) where
  question : P → Sum O N
  row : SecondRow P R

def partnerQuestion {P O N : Type} (single : P → Bool) (occurrences : P → O)
    (names : P → N) : P → Sum O N :=
  fun j => if single j then .inr (names j) else .inl (occurrences j)

def partnerRow {P R : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R) : SecondRow P R :=
  fun homogeneous x y => add (scale zeta0 homogeneous) (rowSum positions fun j =>
    if single j then scale (omega j) (y j)
    else add (scale (zeta1 j) (x j 0)) (scale (zeta2 j) (x j 1)))


def firstInput {P R O : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (occurrences : P → O) (indices : P → Fin 3) : FirstInput P R O :=
  ⟨occurrences, pullbackRow positions single zeta0 zeta1 zeta2 omega indices⟩

def secondInput {P R O N : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (occurrences : P → O) (names : P → N) : SecondInput P R O N :=
  ⟨partnerQuestion single occurrences names,
    partnerRow positions single zeta0 zeta1 zeta2 omega⟩

/-- A total fixed decoder for a retained index. On supported (o,n) it is uniquely
determined by the distinctness of the three names. -/
noncomputable def decodeIndex {O N : Type} (name : O → Fin 3 → N)
    (occurrence : O) (n : N) : Fin 3 := by
  classical
  exact if h : ∃ i, name occurrence i = n then Classical.choose h else 0

theorem decodeIndex_name {O N : Type} (name : O → Fin 3 → N)
    (distinct : ∀ o i i', name o i = name o i' → i = i') (o : O) (i : Fin 3) :
    decodeIndex name o (name o i) = i := by
  classical
  unfold decodeIndex
  have he : ∃ i', name o i' = name o i := ⟨i, rfl⟩
  simp only [he, ↓reduceDIte]
  exact distinct o _ i (Classical.choose_spec he)

def projectFull {P : Type} (single : P → Bool) (x : P → Fin 3 → Bool) :
    P → Fin 3 → Bool :=
  fun j i => if single j then false else x j i

def projectSingles {P : Type} (single : P → Bool) (indices : P → Fin 3)
    (x : P → Fin 3 → Bool) : P → Bool :=
  fun j => if single j then x j (indices j) else false


end UniqueGamesTheorem.Soundness.ZeroInformation

open scoped BigOperators

namespace UniqueGamesTheorem.Soundness.ConditionalIncidences

noncomputable section

abbrev PositionInside {P : Type} (K : Finset P) := {j : P // j ∈ K}
abbrev PositionOutside {P : Type} (K : Finset P) := {j : P // j ∉ K}
abbrev Draw (P O : Type) := P → O × Fin 3

def incidence {O N : Type} (name : O → Fin 3 → N) (draw : O × Fin 3) : O × N :=
  (draw.1, name draw.1 draw.2)


def outsideRecord {P O N : Type} (K : Finset P) (name : O → Fin 3 → N)
    (sample : Draw P O) : PositionOutside K → O × N :=
  fun j => incidence name (sample j.val)

abbrev ObservationFibre {P O N : Type} (K : Finset P) (name : O → Fin 3 → N)
    (observed : PositionOutside K → O × N) :=
  {sample : Draw P O // outsideRecord K name sample = observed}

abbrev OutsideFibre {P O N : Type} (K : Finset P) (name : O → Fin 3 → N)
    (observed : PositionOutside K → O × N) :=
  {sample : PositionOutside K → O × Fin 3 //
    (fun j => incidence name (sample j)) = observed}

instance observationFibreFintype {P O N : Type} [Fintype P] [Fintype O]
    (K : Finset P) (name : O → Fin 3 → N) (observed : PositionOutside K → O × N) :
    Fintype (ObservationFibre K name observed) := Fintype.ofFinite _

instance outsideFibreFintype {P O N : Type} [Fintype P] [Fintype O]
    (K : Finset P) (name : O → Fin 3 → N) (observed : PositionOutside K → O × N) :
    Fintype (OutsideFibre K name observed) := Fintype.ofFinite _


def average {A : Type} [Fintype A] (f : A → ℚ) : ℚ :=
  (∑ a, f a) / Fintype.card A


section ConditionalLaw

variable {P O N : Type} [Fintype P] [DecidableEq P] [Fintype O]


end ConditionalLaw

/-- None is ζ₀; the left summand gives two coefficients per full position;
the right summand gives one coefficient per single position. -/
abbrev RawSlot {P : Type} (J : Finset P) :=
  Option ((PositionOutside J × Fin 2) ⊕ PositionInside J)

abbrev RawCoefficients {P : Type} (J : Finset P) (D : Type) := RawSlot J → D

def zeroSet {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) : Finset P :=
  J.attach.filter (fun j => gamma (some (.inr j)) = 0) |>.map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_zeroSet {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) (j : P) :
    j ∈ zeroSet J gamma ↔ ∃ hj : j ∈ J, gamma (some (.inr ⟨j, hj⟩)) = 0 := by
  simp [zeroSet]

abbrev RawSample {P : Type} (J : Finset P) (D O : Type) :=
  RawCoefficients J D × Draw P O

/-- H fixes gamma and the outside incidence pairs. K is a deterministic function
of gamma, so including K explicitly in H gives precisely this same event. -/
abbrev RawObservationFibre {P D O N : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N) :=
  {sample : RawSample J D O // sample.1 = gamma ∧
    outsideRecord (zeroSet J gamma) name sample.2 = observed}

instance rawObservationFibreFintype {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N) :
    Fintype (RawObservationFibre J name gamma observed) := Fintype.ofFinite _


end

end UniqueGamesTheorem.Soundness.ConditionalIncidences

end OAI
