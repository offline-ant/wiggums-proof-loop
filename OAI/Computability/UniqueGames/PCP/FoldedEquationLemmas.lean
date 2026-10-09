/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.PCP.SourceNoiseParameterLemmas
import OAI.Computability.UniqueGames.Reduction.ActualCanonicalLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.FoldedEquation

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

variable {I J : Type}

/-- Left and right stored tables have disjoint variable names. -/
abbrev Address (i₀ : I) (j₀ : J) := HalfCube i₀ ⊕ HalfCube j₀

def storedAssignment {i₀ : I} {j₀ : J}
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) :
    Address i₀ j₀ → Bool := Sum.elim tableA tableB

/-- Cancellation of the two copies of `g j₀` leaves this explicit RHS. -/
def rhsCorrection (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (μ : Cube J) : Bool := f i₀ ^^ f (π j₀) ^^ μ j₀

theorem correction_eq (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) :
    (f i₀ ^^ g j₀ ^^ thirdQuery π f g μ j₀) = rhsCorrection π i₀ j₀ f μ := by
  change (f i₀ ^^ g j₀ ^^ (g j₀ ^^ (f (π j₀) ^^ μ j₀))) =
    (f i₀ ^^ f (π j₀) ^^ μ j₀)
  cases f i₀ <;> cases g j₀ <;> cases f (π j₀) <;> cases μ j₀ <;> rfl

/-- One sampled test becomes exactly one three-occurrence equation. -/
def equation (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr (canonicalInput j₀ g)
  third := .inr (canonicalInput j₀ (thirdQuery π f g μ))
  rhs := rhsCorrection π i₀ j₀ f μ

theorem xor_corrections (a b c u v w : Bool) :
    ((a ^^ b ^^ c) == (u ^^ v ^^ w)) =
      !((a ^^ u) ^^ (b ^^ v) ^^ (c ^^ w)) := by
  cases a <;> cases b <;> cases c <;> cases u <;> cases v <;> cases w <;> rfl

/-- Exact Boolean semantics, with the three stored bits read from one assignment.
There is no distinct-address assumption. -/
theorem equation_satisfied (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      !(foldedAnswer i₀ tableA f ^^ foldedAnswer j₀ tableB g ^^
        foldedAnswer j₀ tableB (thirdQuery π f g μ)) := by
  change ((tableA (canonicalInput i₀ f) ^^ tableB (canonicalInput j₀ g) ^^
      tableB (canonicalInput j₀ (thirdQuery π f g μ))) == rhsCorrection π i₀ j₀ f μ) = _
  rw [← correction_eq π i₀ j₀ f g μ]
  exact xor_corrections _ _ _ _ _ _


/-- Repeated variable occurrences retain XOR multiplicity and cancel in pairs. -/
theorem satisfied_repeated_right {Name : Type} (e : Equation Name)
    (assignment : Name → Bool) (h : e.second = e.third) :
    satisfied e assignment = (assignment e.first == e.rhs) := by
  unfold satisfied
  rw [← h]
  cases assignment e.first <;> cases assignment e.second <;> cases e.rhs <;> rfl


theorem restrict_thirdQuery (valid : J → Bool) (π : J → I)
    (f : Cube I) (g μ : Cube J) :
    restrictQuery valid (thirdQuery π f g μ) =
      thirdQuery (fun j : {j : J // valid j = true} => π j.val) f
        (restrictQuery valid g) (restrictQuery valid μ) := rfl

/-- Conditioned storage uses only satisfying-assignment coordinates, so identical
restricted canonical inputs are the same variable, even for distinct raw queries. -/
def conditionedEquation (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) :=
  equation (fun j => π j.val) i₀ j₀ f (restrictQuery valid g) (restrictQuery valid μ)


theorem conditionedEquation_satisfied (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedEquation valid π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      !(foldedAnswer i₀ tableA f ^^ conditionedFoldedAnswer valid j₀ tableB g ^^
        conditionedFoldedAnswer valid j₀ tableB (thirdQuery π f g μ)) := by
  unfold conditionedEquation
  rw [equation_satisfied]
  simp only [conditionedFoldedAnswer, restrict_thirdQuery]


variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable section


end

end UniqueGamesTheorem.Foundations.Hastad.FoldedEquation

end

section

/-!
Actual equations for clause contexts having no valid local assignment. The
right answer is the constant false bit, represented by two occurrences of one
dummy variable. Those occurrences cancel for every assignment. The remaining
left answer is folded, so its uniform bias is exactly zero.
-/

namespace UniqueGamesTheorem.Foundations.Hastad

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

/-- Rename the three occurrences without merging or dropping any occurrence. -/
def mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) : Equation Name' where
  first := rename e.first
  second := rename e.second
  third := rename e.third
  rhs := e.rhs

theorem satisfied_mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) (assignment : Name' → Bool) :
    satisfied (mapEquation rename e) assignment = satisfied e (assignment ∘ rename) := rfl

namespace EmptyContext

variable {I : Type}

/-- A left half-table address or the one dummy address. -/
abbrev Address (i₀ : I) := HalfCube i₀ ⊕ Unit

def storedAssignment {i₀ : I} (table : HalfCube i₀ → Bool) (dummy : Bool) :
    Address i₀ → Bool := Sum.elim table (fun _ => dummy)

/-- The dummy appears twice. Its assigned bit cancels in the equation. -/
def equation (i₀ : I) (f : Cube I) : Equation (Address i₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr ()
  third := .inr ()
  rhs := f i₀

@[simp] theorem equation_second_eq_third (i₀ : I) (f : Cube I) :
    (equation i₀ f).second = (equation i₀ f).third := rfl

/-- Exact semantics for every assignment, including an arbitrary dummy bit. -/
theorem equation_satisfied (i₀ : I) (assignment : Address i₀ → Bool) (f : Cube I) :
    satisfied (equation i₀ f) assignment =
      !(foldedAnswer i₀ (fun h => assignment (.inl h)) f) := by
  rw [FoldedEquation.satisfied_repeated_right (equation i₀ f) assignment rfl]
  change (assignment (.inl (canonicalInput i₀ f)) == f i₀) =
    !(assignment (.inl (canonicalInput i₀ f)) ^^ f i₀)
  cases assignment (.inl (canonicalInput i₀ f)) <;> cases f i₀ <;> rfl


/-- The two opposite queries give an explicit balanced list of equations. -/
def pairedEquations (i₀ : I) (f : Cube I) : List (Equation (Address i₀)) :=
  [equation i₀ f, equation i₀ (cubeFlip f)]

@[simp] theorem pairedEquations_length (i₀ : I) (f : Cube I) :
    (pairedEquations i₀ f).length = 2 := rfl


variable [Fintype I] [DecidableEq I]

noncomputable section


end
end EmptyContext
end UniqueGamesTheorem.Foundations.Hastad

end

section

namespace UniqueGamesTheorem.Outer.Clone100Counting

open scoped BigOperators

abbrev Index := Fin 100
abbrev Triple := Index × Index × Index

def sign (b : Bool) : ℚ := if b then -1 else 1

def bias (f : Index → Bool) : ℚ := (∑ i, sign (f i)) / 100

/-- A deterministic majority, resolving a zero bias to `false`. -/
def majorityBit (f : Index → Bool) : Bool := decide (bias f < 0)

theorem majority_aligned_nonneg (f : Index → Bool) :
    0 ≤ sign (majorityBit f) * bias f := by
  by_cases h : bias f < 0
  · simp [majorityBit, h, sign]
    exact le_of_lt h
  · simpa [majorityBit, h, sign] using le_of_not_gt h

def parityIndicator (a b c rhs : Bool) : ℚ :=
  if (xor (xor a b) c) == rhs then 1 else 0

theorem parityIndicator_nonneg (a b c rhs : Bool) :
    0 ≤ parityIndicator a b c rhs := by
  unfold parityIndicator
  split <;> norm_num

theorem parityIndicator_le_one (a b c rhs : Bool) :
    parityIndicator a b c rhs ≤ 1 := by
  unfold parityIndicator
  split <;> norm_num

theorem parityIndicator_eq (a b c rhs : Bool) :
    parityIndicator a b c rhs =
      (1 + sign rhs * sign a * sign b * sign c) / 2 := by
  cases a <;> cases b <;> cases c <;> cases rhs <;>
    norm_num [parityIndicator, sign]

def unconditionedScore (p q r : Index → Bool) (rhs : Bool) : ℚ :=
  (∑ t : Triple, parityIndicator (p t.1) (q t.2.1) (r t.2.2) rhs) / 1000000

theorem independent_product_sum (p q r : Index → ℚ) :
    (∑ t : Triple, p t.1 * q t.2.1 * r t.2.2) =
      (∑ i, p i) * (∑ j, q j) * (∑ k, r k) := by
  simp only [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]

theorem unconditionedScore_eq (p q r : Index → Bool) (rhs : Bool) :
    unconditionedScore p q r rhs =
      (1 + sign rhs * bias p * bias q * bias r) / 2 := by
  have hp := independent_product_sum
    (fun i => sign (p i)) (fun i => sign (q i)) (fun i => sign (r i))
  have hs : (∑ t : Triple, sign rhs * sign (p t.1) * sign (q t.2.1) * sign (r t.2.2)) =
      sign rhs * ((∑ i, sign (p i)) * (∑ j, sign (q j)) * (∑ k, sign (r k))) := by
    rw [← hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  unfold unconditionedScore
  simp_rw [parityIndicator_eq, div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul]
  unfold bias
  norm_num
  ring

theorem unconditionedScore_le_one (p q r : Index → Bool) (rhs : Bool) :
    unconditionedScore p q r rhs ≤ 1 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset Triple))
    (fun t _ => parityIndicator_le_one (p t.1) (q t.2.1) (r t.2.2) rhs)
  norm_num [Fintype.card_prod, Fintype.card_fin] at h
  unfold unconditionedScore
  linarith

theorem signed_product_of_failure (a b c rhs : Bool) (x y z : ℚ)
    (h : (xor (xor a b) c == rhs) = false) :
    sign rhs * x * y * z = -((sign a * x) * (sign b * y) * (sign c * z)) := by
  cases a <;> cases b <;> cases c <;> cases rhs <;>
    simp_all [sign]

/-- An equation violated by the majority assignment is satisfied by independent
clone labels with probability at most one half. This also allows repeated
original variable names: independence belongs to the sampled clone indices. -/
theorem unconditionedScore_le_half_of_failure (p q r : Index → Bool) (rhs : Bool)
    (h : (xor (xor (majorityBit p) (majorityBit q)) (majorityBit r) == rhs) = false) :
    unconditionedScore p q r rhs ≤ 1 / 2 := by
  have hn := mul_nonneg
    (mul_nonneg (majority_aligned_nonneg p) (majority_aligned_nonneg q))
    (majority_aligned_nonneg r)
  rw [unconditionedScore_eq,
    signed_product_of_failure (majorityBit p) (majorityBit q) (majorityBit r)
      rhs (bias p) (bias q) (bias r) h]
  linarith

theorem unconditionedScore_le (p q r : Index → Bool) (rhs : Bool) :
    unconditionedScore p q r rhs ≤
      (1 + parityIndicator (majorityBit p) (majorityBit q) (majorityBit r) rhs) / 2 := by
  cases h : (xor (xor (majorityBit p) (majorityBit q)) (majorityBit r) == rhs) with
  | false =>
    have hi : parityIndicator (majorityBit p) (majorityBit q) (majorityBit r) rhs = 0 := by
      unfold parityIndicator
      rw [h]
      rfl
    rw [hi, add_zero]
    exact unconditionedScore_le_half_of_failure p q r rhs h
  | true =>
    have hi : parityIndicator (majorityBit p) (majorityBit q) (majorityBit r) rhs = 1 := by
      unfold parityIndicator
      rw [h]
      rfl
    rw [hi]
    norm_num
    exact unconditionedScore_le_one p q r rhs

/-- Conditioning a bounded function onto 970200 of one million outcomes
changes its upper expectation by at most 3/100. The exact loss is 298/10000.
Only finite sums and the actual accepted sample cardinality are needed. -/
theorem condition_970200_le {T : Type*} [Fintype T]
    (good : T → Prop) [DecidablePred good]
    (_hT : Fintype.card T = 1000000)
    (hgood : Fintype.card {t : T // good t} = 970200)
    (f : T → ℚ) (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1) :
    (∑ t : {t : T // good t}, f t.val) / 970200 ≤
      (∑ t : T, f t) / 1000000 + 3 / 100 := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype good f
  have hn : 0 ≤ ∑ t : {t : T // ¬good t}, f t.val :=
    Finset.sum_nonneg (fun t _ => hf0 t.val)
  have hle : (∑ t : {t : T // good t}, f t.val) ≤ ∑ t : T, f t := by
    linarith
  have hcap := Finset.sum_le_sum (s := (Finset.univ : Finset {t : T // good t}))
    (fun t _ => hf1 t.val)
  simp only [Finset.sum_const, Finset.card_univ, hgood, nsmul_eq_mul] at hcap
  norm_num at hcap
  linarith

def conditionedScore (good : Triple → Prop) [DecidablePred good]
    (p q r : Index → Bool) (rhs : Bool) : ℚ :=
  (∑ t : {t : Triple // good t},
    parityIndicator (p t.val.1) (q t.val.2.1) (r t.val.2.2) rhs) / 970200

theorem conditionedScore_le (good : Triple → Prop) [DecidablePred good]
    (hgood : Fintype.card {t : Triple // good t} = 970200)
    (p q r : Index → Bool) (rhs : Bool) :
    conditionedScore good p q r rhs ≤
      (1 + parityIndicator (majorityBit p) (majorityBit q) (majorityBit r) rhs) / 2 + 3 / 100 := by
  have hcond := condition_970200_le good
    (by norm_num [Fintype.card_prod, Fintype.card_fin]) hgood
    (fun t => parityIndicator (p t.1) (q t.2.1) (r t.2.2) rhs)
    (fun t => parityIndicator_nonneg _ _ _ _)
    (fun t => parityIndicator_le_one _ _ _ _)
  have hmaj := unconditionedScore_le p q r rhs
  change conditionedScore good p q r rhs ≤ unconditionedScore p q r rhs + 3 / 100 at hcond
  linarith

end UniqueGamesTheorem.Outer.Clone100Counting

end

end OAI
