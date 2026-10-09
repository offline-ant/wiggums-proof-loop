/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import OAI.Computability.UniqueGames.PCP.AlphabetReductionLemmas
import OAI.Computability.UniqueGames.PCP.ZigzagGraphsLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VertexPadding

open scoped BigOperators

variable {V D A : Type*}

/-- Original darts use the original reversal; dummy darts stay fixed. -/
def reverseFunction (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    (V ⊕ Fin extra) × D → (V ⊕ Fin extra) × D
  | (Sum.inl v, d) => (Sum.inl (G.reverse (v, d)).1, (G.reverse (v, d)).2)
  | (Sum.inr w, d) => (Sum.inr w, d)

theorem reverseFunction_involutive (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    Function.Involutive (reverseFunction G extra) := by
  rintro ⟨v | w, d⟩
  · change (Sum.inl (G.reverse (G.reverse (v, d))).1,
      (G.reverse (G.reverse (v, d))).2) = (Sum.inl v, d)
    rw [G.reverse_involutive]
  · rfl

/-- Actual regular padding by an arbitrary finite number of dummy vertices. -/
def pad (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    ConstraintGraph (V ⊕ Fin extra) ((V ⊕ Fin extra) × D) A where
  reverse := {
    toFun := reverseFunction G extra
    invFun := reverseFunction G extra
    left_inv := reverseFunction_involutive G extra
    right_inv := reverseFunction_involutive G extra }
  reverse_involutive := reverseFunction_involutive G extra
  tail := Prod.fst
  accepts := fun e a b => match e.1 with
    | Sum.inl v => G.accepts (v, e.2) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v | w, d⟩ a b
    · change G.accepts (G.reverse (v, d)) b a = G.accepts (v, d) a b
      exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem pad_tail (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    (pad G extra).tail = Prod.fst := rfl

@[simp] theorem pad_reverse_inl (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (v : V) (d : D) :
    (pad G extra).reverse (Sum.inl v, d) =
      (Sum.inl (G.reverse (v, d)).1, (G.reverse (v, d)).2) := rfl

@[simp] theorem pad_reverse_inr (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (w : Fin extra) (d : D) :
    (pad G extra).reverse (Sum.inr w, d) = (Sum.inr w, d) := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (extra : ℕ) (labeling : V ⊕ Fin extra → A)
    (v : V) (d : D) :
    (pad G extra).edgeSatisfied labeling (Sum.inl v, d) =
      G.edgeSatisfied (fun v => labeling (Sum.inl v)) (v, d) := by
  change G.accepts (v, d) (labeling (Sum.inl v))
      (labeling (Sum.inl (G.reverse (v, d)).1)) =
    G.accepts (v, d) (labeling (Sum.inl (G.tail (v, d))))
      (labeling (Sum.inl (G.tail (G.reverse (v, d)))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (labeling : V ⊕ Fin extra → A) (w : Fin extra) (d : D) :
    (pad G extra).edgeSatisfied labeling (Sum.inr w, d) = true := rfl

def extendLabeling (extra : ℕ) (defaultA : A) (labeling : V → A) : V ⊕ Fin extra → A :=
  Sum.elim labeling (fun _ => defaultA)

@[simp] theorem extendLabeling_inl (extra : ℕ) (defaultA : A) (labeling : V → A)
    (v : V) : extendLabeling extra defaultA labeling (Sum.inl v) = labeling v := rfl

@[simp] theorem extendLabeling_inr (extra : ℕ) (defaultA : A) (labeling : V → A)
    (w : Fin extra) : extendLabeling extra defaultA labeling (Sum.inr w) = defaultA := rfl


private theorem rejectionCount_eq_sum {U E : Type*} [Fintype E]
    (G : ConstraintGraph U E A) (labeling : U → A) :
    G.rejectionCount labeling = ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]

/-- Exact counts for every padded labeling, without any condition on dummy labels. -/
theorem pad_rejectionCount [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst) (extra : ℕ)
    (labeling : V ⊕ Fin extra → A) :
    (pad G extra).rejectionCount labeling =
      G.rejectionCount (fun v => labeling (Sum.inl v)) := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [edgeSatisfied_inl G htail, edgeSatisfied_inr]
  simp

section FamilySize

variable (V : Type*) [Fintype V]

def extraVertices : ℕ := ExpanderFamily.size (Fintype.card V) - Fintype.card V

abbrev Vertex := V ⊕ Fin (extraVertices V)


variable {V}

def paddedG (G : ConstraintGraph V (V × D) A) : ConstraintGraph (Vertex V) (Vertex V × D) A :=
  pad G (extraVertices V)

@[simp] theorem paddedG_tail (G : ConstraintGraph V (V × D) A) :
    (paddedG G).tail = Prod.fst := rfl


def liftLabel (defaultA : A) (labeling : V → A) : Vertex V → A :=
  extendLabeling (extraVertices V) defaultA labeling

@[simp] theorem liftLabel_inl (defaultA : A) (labeling : V → A) (v : V) :
    liftLabel defaultA labeling (Sum.inl v) = labeling v := rfl

@[simp] theorem liftLabel_inr (defaultA : A) (labeling : V → A)
    (w : Fin (extraVertices V)) :
    liftLabel defaultA labeling (Sum.inr w) = defaultA := rfl


end FamilySize

end UniqueGamesTheorem.Foundations.PCP.VertexPadding

end

end OAI
