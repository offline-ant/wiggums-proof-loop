/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Foundations.KernelSampling
import OAI.Computability.UniqueGames.Foundations.MixtureLemmas

namespace OAI

section

/-!
Scalar estimates for the construction. These lemmas
only perform the stated rounding/subdivision/repetition arithmetic; they do
not assume or assert an unproved repetition theorem or hardness result.
-/

namespace UniqueGamesTheorem.Explicit.FinishBounds


end UniqueGamesTheorem.Explicit.FinishBounds

end

section

/-!
Finite occurrence presentations used by the rounding/subdivision construction.
An occurrence has its own identifier: its endpoints need not be distinct and
different occurrences may have the same endpoints. The bipartite target records
injectivity of the pair of endpoints, which is precisely the required simplicity.
No hardness or analytic premise enters these structures.
-/

namespace UniqueGamesTheorem.Explicit

structure OccurrenceGame (V E A : Type*) where
  source : E → V
  target : E → V
  permutation : E → Equiv.Perm A

structure BipartiteGame (L R E A : Type*) where
  left : E → L
  right : E → R
  permutation : E → Equiv.Perm A
  simple : Function.Injective (fun e => (left e, right e))

namespace OccurrenceGame

def Satisfied {V E A : Type*} (G : OccurrenceGame V E A)
    (labeling : V → A) (e : E) : Prop :=
  labeling (G.target e) = G.permutation e (labeling (G.source e))

instance satisfiedDecidable {V E A : Type*} [DecidableEq A]
    (G : OccurrenceGame V E A) (labeling : V → A) (e : E) :
    Decidable (G.Satisfied labeling e) := inferInstanceAs (Decidable (_ = _))


end OccurrenceGame

namespace BipartiteGame

def Satisfied {L R E A : Type*} (G : BipartiteGame L R E A)
    (leftLabeling : L → A) (rightLabeling : R → A) (e : E) : Prop :=
  rightLabeling (G.right e) = G.permutation e (leftLabeling (G.left e))

instance satisfiedDecidable {L R E A : Type*} [DecidableEq A]
    (G : BipartiteGame L R E A) (a : L → A) (b : R → A) (e : E) :
    Decidable (G.Satisfied a b e) := inferInstanceAs (Decidable (_ = _))


end BipartiteGame

end UniqueGamesTheorem.Explicit

end

section

/-!
The four-edge subdivision.
Every input occurrence has its own three interior vertices, even when
the original endpoints coincide or another occurrence has the same endpoints.
The left/right presentation inverts the permutation on the fourth edge.
-/

namespace UniqueGamesTheorem.Explicit

open scoped BigOperators

namespace OccurrenceGame

variable {V E A : Type*} [Fintype E] [DecidableEq A]

def satisfiedCount (g : OccurrenceGame V E A) (a : V → A) : Nat :=
  ∑ e, if g.permutation e (a (g.source e)) = a (g.target e) then 1 else 0

theorem satisfiedCount_eq_sum_satisfied (g : OccurrenceGame V E A) (a : V → A) :
    satisfiedCount g a = ∑ e, if g.Satisfied a e then 1 else 0 := by
  apply Finset.sum_congr rfl
  intro e _
  exact if_congr eq_comm rfl rfl

variable [Fintype V] [Fintype A]

noncomputable def maxSatisfied (g : OccurrenceGame V E A) : Nat := by
  classical
  exact Finset.univ.sup (satisfiedCount g)

noncomputable def value (g : OccurrenceGame V E A) : ℝ :=
  (maxSatisfied g : ℝ) / Fintype.card E

theorem satisfiedCount_le_maxSatisfied (g : OccurrenceGame V E A) (a : V → A) :
    satisfiedCount g a ≤ maxSatisfied g := by
  classical
  exact Finset.le_sup (f := satisfiedCount g) (Finset.mem_univ a)

theorem maxSatisfied_attained [Nonempty A] (g : OccurrenceGame V E A) :
    ∃ a, satisfiedCount g a = maxSatisfied g := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (satisfiedCount g)
  exact ⟨a, ha.symm⟩

end OccurrenceGame

namespace BipartiteGame

variable {L R E A : Type*} [Fintype E] [DecidableEq A]

def satisfiedCount (g : BipartiteGame L R E A) (a : L → A) (b : R → A) : Nat :=
  ∑ e, if g.permutation e (a (g.left e)) = b (g.right e) then 1 else 0

theorem satisfiedCount_eq_sum_satisfied (g : BipartiteGame L R E A)
    (a : L → A) (b : R → A) :
    satisfiedCount g a b = ∑ e, if g.Satisfied a b e then 1 else 0 := by
  apply Finset.sum_congr rfl
  intro e _
  exact if_congr eq_comm rfl rfl

variable [Fintype L] [Fintype R] [Fintype A]

noncomputable def maxSatisfied (g : BipartiteGame L R E A) : Nat := by
  classical
  exact Finset.univ.sup (fun ab : (L → A) × (R → A) => satisfiedCount g ab.1 ab.2)

noncomputable def value (g : BipartiteGame L R E A) : ℝ :=
  (maxSatisfied g : ℝ) / Fintype.card E

theorem satisfiedCount_le_maxSatisfied (g : BipartiteGame L R E A)
    (a : L → A) (b : R → A) : satisfiedCount g a b ≤ maxSatisfied g := by
  classical
  exact Finset.le_sup (f := fun ab : (L → A) × (R → A) => satisfiedCount g ab.1 ab.2)
    (Finset.mem_univ (a, b))

theorem maxSatisfied_attained [Nonempty A] (g : BipartiteGame L R E A) :
    ∃ a b, satisfiedCount g a b = maxSatisfied g := by
  classical
  obtain ⟨⟨a, b⟩, _, hab⟩ := Finset.exists_mem_eq_sup Finset.univ
    Finset.univ_nonempty
    (fun ab : (L → A) × (R → A) => satisfiedCount g ab.1 ab.2)
  exact ⟨a, b, hab.symm⟩

end BipartiteGame

namespace Subdivision

variable {V E A : Type*}

/-- Original vertices and the middle vertices `q_e`. -/
abbrev Left (V E : Type*) := V ⊕ E

/-- `false` is `p_e`, and `true` is `r_e`. -/
abbrev Right (E : Type*) := E × Bool

abbrev Edge (E : Type*) := E × Fin 4

def left (g : OccurrenceGame V E A) (ei : Edge E) : Left V E :=
  if ei.2 = 0 then Sum.inl (g.source ei.1)
  else if ei.2 = 3 then Sum.inl (g.target ei.1)
  else Sum.inr ei.1

def right (ei : Edge E) : Right E := (ei.1, decide (2 ≤ ei.2.val))

def permutation (g : OccurrenceGame V E A) (ei : Edge E) : Equiv.Perm A :=
  if ei.2 = 3 then (g.permutation ei.1).symm else Equiv.refl A

/-- The private occurrence identifier prevents parallel edges after subdivision.
This also handles a loop, which becomes a genuine four-cycle. -/
theorem endpoints_injective (g : OccurrenceGame V E A) :
    Function.Injective (fun ei : Edge E => (left g ei, right ei)) := by
  rintro ⟨e, i⟩ ⟨f, j⟩ h
  have hef : e = f := congrArg (fun x => x.2.1) h
  subst f
  fin_cases i <;> fin_cases j <;> simp_all [left, right]

def game (g : OccurrenceGame V E A) :
    BipartiteGame (Left V E) (Right E) (Edge E) A where
  left := left g
  right := right
  permutation := permutation g
  simple := endpoints_injective g


/-- Restrict any output labeling to the original vertices. -/
def restrict (a : Left V E → A) : V → A := fun v => a (Sum.inl v)

def extendLeft (g : OccurrenceGame V E A) (a : V → A) : Left V E → A :=
  Sum.elim a (fun e => a (g.source e))

def extendRight (g : OccurrenceGame V E A) (a : V → A) : Right E → A :=
  fun eb => a (g.source eb.1)

@[simp] theorem restrict_extendLeft (g : OccurrenceGame V E A) (a : V → A) :
    restrict (extendLeft g a) = a := rfl


variable [DecidableEq A]

/-- The strongest possible path score for fixed endpoint labels is exactly
three plus the old satisfaction indicator. -/
theorem local_count_le (ρ : Equiv.Perm A) (u p q r v : A) :
    (if u = p then 1 else 0) + (if q = p then 1 else 0) +
      (if q = r then 1 else 0) + (if ρ.symm v = r then 1 else 0) ≤
        3 + (if ρ u = v then 1 else 0 : Nat) := by
  by_cases h₀ : u = p <;> by_cases h₁ : q = p <;>
    by_cases h₂ : q = r <;> by_cases h₃ : ρ.symm v = r <;>
    by_cases h : ρ u = v <;> simp_all [Equiv.symm_apply_eq]

theorem local_count_extend (ρ : Equiv.Perm A) (u v : A) :
    (if u = u then 1 else 0) + (if u = u then 1 else 0) +
      (if u = u then 1 else 0) + (if ρ.symm v = u then 1 else 0) =
        3 + (if ρ u = v then 1 else 0 : Nat) := by
  simp only
  exact congrArg (fun n : ℕ => 3 + n)
    (if_congr (ρ.symm_apply_eq.trans eq_comm) rfl rfl)

theorem count_on_occurrence_le (g : OccurrenceGame V E A)
    (a : Left V E → A) (b : Right E → A) (e : E) :
    (∑ i : Fin 4, if (game g).permutation (e, i) (a ((game g).left (e, i))) =
        b ((game g).right (e, i)) then 1 else 0) ≤
      3 + (if g.permutation e (restrict a (g.source e)) =
        restrict a (g.target e) then 1 else 0 : Nat) := by
  rw [Fin.sum_univ_four]
  exact local_count_le (g.permutation e)
      (a (Sum.inl (g.source e))) (b (e, false)) (a (Sum.inr e))
      (b (e, true)) (a (Sum.inl (g.target e)))

theorem count_on_occurrence_extend (g : OccurrenceGame V E A) (a : V → A) (e : E) :
    (∑ i : Fin 4, if (game g).permutation (e, i)
      (extendLeft g a ((game g).left (e, i))) =
        extendRight g a ((game g).right (e, i)) then 1 else 0) =
      3 + (if g.permutation e (a (g.source e)) = a (g.target e) then 1 else 0 : Nat) := by
  rw [Fin.sum_univ_four]
  simpa [game, permutation, left, right, extendLeft, extendRight] using
    local_count_extend (g.permutation e) (a (g.source e)) (a (g.target e))

variable [Fintype E]

theorem satisfiedCount_le (g : OccurrenceGame V E A)
    (a : Left V E → A) (b : Right E → A) :
    (game g).satisfiedCount a b ≤
      3 * Fintype.card E + g.satisfiedCount (restrict a) := by
  unfold BipartiteGame.satisfiedCount OccurrenceGame.satisfiedCount
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ e, (3 + (if g.permutation e (restrict a (g.source e)) =
        restrict a (g.target e) then 1 else 0 : Nat)) :=
      Finset.sum_le_sum (fun e _ => count_on_occurrence_le g a b e)
    _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_comm]

/-- Fresh interiors can be assigned independently, so the upper bound is attained. -/
theorem satisfiedCount_extend (g : OccurrenceGame V E A) (a : V → A) :
    (game g).satisfiedCount (extendLeft g a) (extendRight g a) =
      3 * Fintype.card E + g.satisfiedCount a := by
  unfold BipartiteGame.satisfiedCount OccurrenceGame.satisfiedCount
  rw [Fintype.sum_prod_type]
  simp_rw [count_on_occurrence_extend]
  simp [Finset.sum_add_distrib, Nat.mul_comm]

@[simp] theorem edge_count : Fintype.card (Edge E) = 4 * Fintype.card E := by
  simp [Edge, Nat.mul_comm]


variable [Fintype V] [Fintype A] [Nonempty A]

theorem maxSatisfied_eq (g : OccurrenceGame V E A) :
    (game g).maxSatisfied = 3 * Fintype.card E + g.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro ab _
    exact (satisfiedCount_le g ab.1 ab.2).trans
      (Nat.add_le_add_left (g.satisfiedCount_le_maxSatisfied (restrict ab.1)) _)
  · obtain ⟨a, ha⟩ := g.maxSatisfied_attained
    rw [← ha, ← satisfiedCount_extend]
    exact BipartiteGame.satisfiedCount_le_maxSatisfied _ _ _

theorem value_eq [Nonempty E] (g : OccurrenceGame V E A) :
    (game g).value = 1 - (1 - g.value) / 4 := by
  have hE : (Fintype.card E : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [BipartiteGame.value, maxSatisfied_eq, edge_count, OccurrenceGame.value]
  push_cast
  field_simp [hE]
  ring

end Subdivision

end UniqueGamesTheorem.Explicit

end

section

/-! Exact composition identities for finite distribution maps. -/
namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem weight_eq_probability_singleton [DecidableEq A] (μ : FiniteDistribution A) (a : A) :
    μ.weight a = μ.probability (fun x => decide (x = a)) := by
  classical
  simp [probability]

theorem pushforward_comp (μ : FiniteDistribution A) (f : A → B) (g : B → C) :
    (μ.pushforward f).pushforward g = μ.pushforward (fun a => g (f a)) := by
  classical
  apply eq_of_weight_eq
  intro c
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward]

theorem transport_eq_pushforward (μ : FiniteDistribution A) (e : A ≃ B) :
    μ.transport e = μ.pushforward e := by
  classical
  apply eq_of_weight_eq
  intro b
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton,
    probability_transport, probability_pushforward]

theorem expectation_pushforward (μ : FiniteDistribution A) (f : A → B) (h : B → ℝ) :
    (μ.pushforward f).expectation h = μ.expectation (fun a => h (f a)) := by
  classical
  simp only [expectation, pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem pushforward_mixture (μ : FiniteDistribution A) (ν : A → FiniteDistribution B)
    (f : B → C) :
    (μ.mixture ν).pushforward f = μ.mixture (fun a => (ν a).pushforward f) := by
  classical
  apply eq_of_weight_eq
  intro c
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward, probability_mixture]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
