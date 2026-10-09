/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import OAI.Computability.UniqueGames.Foundations.PinskerLemmas

namespace OAI

section

/-! Exact bridges between the integer-encoded target gaps and acceptance rates.
Repeated constraint entries retain their multiplicity in every definition. -/

namespace UniqueGamesTheorem.Integration.GapSemantics

open UniqueGamesTheorem.Foundations.Target


def satisfactionRate {q : Nat} (g : Instance q) (labeling : Fin g.vertices → Fin q) : ℚ :=
  (countSatisfied labeling g.constraints : ℚ) / g.constraints.length

theorem countSatisfied_eq_sum {n q : Nat} (labeling : Fin n → Fin q)
    (constraints : List (Constraint n q)) :
    countSatisfied labeling constraints =
      (constraints.map (fun c => if c.satisfied labeling then (1 : Nat) else 0)).sum := by
  induction constraints with
  | nil => rfl
  | cons c cs ih => simp [countSatisfied, ih]

theorem countSatisfied_ofFn {m n q : Nat} (labeling : Fin n → Fin q)
    (constraints : Fin m → Constraint n q) :
    countSatisfied labeling (List.ofFn constraints) =
      ∑ i, if (constraints i).satisfied labeling then (1 : Nat) else 0 := by
  rw [countSatisfied_eq_sum, List.map_ofFn, List.sum_ofFn]
  rfl


end UniqueGamesTheorem.Integration.GapSemantics

end

section

/-! The final passage from positive dyadic error tolerances to arbitrary real
error tolerances, with exact finite numerator/denominator encodings. -/

namespace UniqueGamesTheorem.Integration.DyadicErrors

open UniqueGamesTheorem.Foundations.Target
open GapSemantics


end UniqueGamesTheorem.Integration.DyadicErrors

end

section

/-! Changing finite encodings preserves the actual Unique Games instance gaps.
Vertex names may be permuted and constraint occurrences may be reordered. -/

namespace UniqueGamesTheorem.Integration.InstanceEquivalences

open UniqueGamesTheorem.Foundations.Target
open GapSemantics

def renameConstraint {n m q : Nat} (e : Fin n ≃ Fin m) (c : Constraint n q) :
    Constraint m q where
  source := e c.source
  target := e c.target
  permutation := c.permutation

@[simp] theorem renameConstraint_satisfied {n m q : Nat} (e : Fin n ≃ Fin m)
    (c : Constraint n q) (labeling : Fin m → Fin q) :
    (renameConstraint e c).satisfied labeling = c.satisfied (labeling ∘ e) := rfl

theorem rename_count {n m q : Nat} (e : Fin n ≃ Fin m)
    (constraints : List (Constraint n q)) (labeling : Fin m → Fin q) :
    countSatisfied labeling (constraints.map (renameConstraint e)) =
      countSatisfied (labeling ∘ e) constraints := by
  induction constraints with
  | nil => rfl
  | cons c cs ih =>
      by_cases hc : c.satisfied (labeling ∘ e) = true <;> simp [countSatisfied, ih, hc]


theorem countSatisfied_perm {n q : Nat} (labeling : Fin n → Fin q)
    {constraints constraints' : List (Constraint n q)}
    (h : constraints.Perm constraints') :
    countSatisfied labeling constraints = countSatisfied labeling constraints' := by
  rw [countSatisfied_eq_sum, countSatisfied_eq_sum]
  exact (h.map (fun c => if c.satisfied labeling then (1 : Nat) else 0)).sum_eq

/-- This statement is directly usable by an executable adapter: only its
vertex equivalence and its permutation of the explicit edge list are needed. -/
theorem satisfactionRate_eq_of_rename_perm {q : Nat} (g h : Instance q)
    (e : Fin g.vertices ≃ Fin h.vertices)
    (hp : h.constraints.Perm (g.constraints.map (renameConstraint e)))
    (labeling : Fin h.vertices → Fin q) :
    satisfactionRate h labeling = satisfactionRate g (labeling ∘ e) := by
  have hcount := countSatisfied_perm labeling hp
  rw [rename_count] at hcount
  have hlength := hp.length_eq
  simp only [List.length_map] at hlength
  unfold satisfactionRate
  rw [hcount, hlength]


end UniqueGamesTheorem.Integration.InstanceEquivalences

end

end OAI
