/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import OAI.Computability.UniqueGames.Foundations.ValueLemmas
import OAI.Computability.UniqueGames.Repetition.AnalyticCheegerLemmas

namespace OAI

section

/-!
Elementary scalar estimates used to convert a collision-norm bound into the
alphabet-independent repetition rate. These statements concern real numbers;
they do not assume or assert any repetition theorem for games.
-/

namespace UniqueGamesTheorem.Repetition


end UniqueGamesTheorem.Repetition

end

section

namespace UniqueGamesTheorem.Repetition

theorem sequence_le_power {r : ℝ} (hr : 0 ≤ r) (c : ℕ → ℝ)
    (hzero : c 0 ≤ 1) (hstep : ∀ n, c (n + 1) ≤ r * c n) :
    ∀ n, c n ≤ r ^ n := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      calc
        c (n + 1) ≤ r * c n := hstep n
        _ ≤ r * r ^ n := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (n + 1) := by rw [pow_succ, mul_comm]

theorem squared_rate_le_dsRate_sq {gap : ℝ}
    (_hgap₀ : 0 ≤ gap) (_hgap₁ : gap ≤ 1) :
    1 - gap ^ 2 / 8 ≤ dsRate gap ^ 2 := by
  dsimp [dsRate]
  nlinarith only [sq_nonneg (gap ^ 2)]

theorem rate_of_squared_collision_recurrence {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (c v : ℕ → ℝ) (hzero : c 0 ≤ 1)
    (hstep : ∀ n, c (n + 1) ≤ (1 - gap ^ 2 / 8) * c n)
    (hvalue : ∀ n, v n ^ 2 ≤ c n) :
    ∀ n, v n ≤ dsRate gap ^ n := by
  have hr : 0 ≤ 1 - gap ^ 2 / 8 := by nlinarith
  have hpow := sequence_le_power hr c hzero hstep
  intro n
  apply le_of_sq_le_sq _ (pow_nonneg (dsRate_nonneg hgap₀ hgap₁) n)
  calc
    v n ^ 2 ≤ c n := hvalue n
    _ ≤ (1 - gap ^ 2 / 8) ^ n := hpow n
    _ ≤ (dsRate gap ^ 2) ^ n :=
      pow_le_pow_left₀ hr (squared_rate_le_dsRate_sq hgap₀ hgap₁) n
    _ = (dsRate gap ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

end UniqueGamesTheorem.Repetition

end

section

/-!
Projection constraints and independent products on the existing classical game
API. A strategy receives only its own full question, even in a product game.
The projection property is an actual uniqueness property of the acceptance
predicate; it is not a premise asserting a repetition bound.
-/

namespace UniqueGamesTheorem.Repetition

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]

/-- The left answer determines at most one accepting right answer. Partial
projection predicates are included, as are total projection maps. -/
def IsProjection (G : Game Q₁ Q₂ A₁ A₂) : Prop :=
  ∀ x y a b b', G.accepts x y a b = true →
    G.accepts x y a b' = true → b = b'


/-- Parallel repetition preserves projection constraints, including at n = 0.
There is no restriction that a repeated strategy act coordinatewise. -/
theorem IsProjection.repetition {G : Game Q₁ Q₂ A₁ A₂}
    (hG : IsProjection G) (n : Nat) : IsProjection (G.repetition n) := by
  intro x y a b b' hb hb'
  have h₁ := (G.repetition_accepts_iff n x y a b).mp hb
  have h₂ := (G.repetition_accepts_iff n x y a b').mp hb'
  funext i
  exact hG (x i) (y i) (a i) (b i) (b' i) (h₁ i) (h₂ i)

/-- Total projection maps give ordinary finite classical games. Question
weights may be arbitrary nonnegative real weights summing to one. -/
def ofProjection (questions : FiniteDistribution (Q₁ × Q₂))
    (project : Q₁ → Q₂ → A₁ → A₂) : Game Q₁ Q₂ A₁ A₂ := by
  classical
  exact { questions := questions, accepts := fun x y a b => decide (project x y a = b) }


/-- Regroup independently sampled question pairs into the two local questions. -/
def productQuestionEquiv :
    ((Q₁ × Q₂) × (R₁ × R₂)) ≃ ((Q₁ × R₁) × (Q₂ × R₂)) where
  toFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  invFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Independent conjunction product. Each answer may depend on the full local
pair of questions; locality is inherited from `Game` and `Strategy`. -/
def product (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂) :
    Game (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂) where
  questions := (G.questions.product H.questions).transport productQuestionEquiv
  accepts x y a b := G.accepts x.1 y.1 a.1 b.1 && H.accepts x.2 y.2 a.2 b.2

@[simp] theorem product_question_weight
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (q : (Q₁ × R₁) × (Q₂ × R₂)) :
    (product G H).questions.weight q =
      G.questions.weight (q.1.1, q.2.1) * H.questions.weight (q.1.2, q.2.2) := rfl

@[simp] theorem product_accepts_iff
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (x : Q₁ × R₁) (y : Q₂ × R₂) (a : A₁ × B₁) (b : A₂ × B₂) :
    (product G H).accepts x y a b = true ↔
      G.accepts x.1 y.1 a.1 b.1 = true ∧ H.accepts x.2 y.2 a.2 b.2 = true := by
  simp [product]

theorem IsProjection.product {G : Game Q₁ Q₂ A₁ A₂} {H : Game R₁ R₂ B₁ B₂}
    (hG : IsProjection G) (hH : IsProjection H) : IsProjection (product G H) := by
  intro x y a b b' hb hb'
  have h₁ := (product_accepts_iff G H x y a b).mp hb
  have h₂ := (product_accepts_iff G H x y a b').mp hb'
  exact Prod.ext (hG _ _ _ _ _ h₁.1 h₂.1) (hH _ _ _ _ _ h₁.2 h₂.2)


end
end UniqueGamesTheorem.Repetition

end

end OAI
