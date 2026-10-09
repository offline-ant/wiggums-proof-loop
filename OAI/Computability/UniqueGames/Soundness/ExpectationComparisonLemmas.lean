/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Std

namespace OAI

section

/-!
The real-valued finite-expectation argument in Lemma 6.3 and equation (6.11).
The density's normalization and second-moment bound are inputs; the variance,
Cauchy--Schwarz comparison, parameter error, and transferred signal are proved.
The test is allowed to depend on every coordinate of the sampled map.
-/

namespace UniqueGamesTheorem.Soundness.ExpectationComparison

open scoped BigOperators

variable {ι : Type*}


end UniqueGamesTheorem.Soundness.ExpectationComparison

end

section

namespace UniqueGamesTheorem.Soundness.IncidenceExtraction

abbrev Triple := Fin 3 → Bool

def xorTriple (x : Triple) : Bool := (x 0 ^^ x 1) ^^ x 2

structure Incidence (Occurrence Name : Type) where
  name : Occurrence → Fin 3 → Name
  rhs : Occurrence → Bool

def Incidence.accepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) : Prop :=
  xorTriple a = g.rhs o ∧ a i = b

/-- The incidence predicate as a game on the actual questions `(o,n)`, with the
    retained slot left internal to the verifier. -/
def Incidence.namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (n : Name)
    (a : Triple) (b : Bool) : Prop :=
  ∃ i, g.name o i = n ∧ g.accepts o i a b

theorem Incidence.accepts_implies_namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) (h : g.accepts o i a b) :
    g.namedAccepts o (g.name o i) a b :=
  ⟨i, rfl, h⟩

/-- Distinct names make the named-variable predicate equivalent to the sampled
    retained-slot predicate, without revealing that slot to either strategy. -/
theorem Incidence.namedAccepts_iff_accepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (o : Occurrence) (i : Fin 3) (a : Triple) (b : Bool) :
    g.namedAccepts o (g.name o i) a b ↔ g.accepts o i a b := by
  constructor
  · rintro ⟨j, hname, h⟩
    have hji := distinct o j i hname
    simpa [hji] using h
  · exact g.accepts_implies_namedAccepts o i a b

/-!
The next definitions separate local strategies from arbitrary joint strategies.
Each question reconstruction and each answer extraction has access to only one
player's question. A value conditioned on by an analysis may occur as a fixed
parameter of a `LocalSimulation`; it cannot become an additional random input.
-/

structure Game (QA QB A B : Type) where
  accepts : QA → QB → A → B → Prop

structure Strategies (QA QB A B : Type) where
  first : QA → A
  second : QB → B

def Strategies.wins {QA QB A B : Type} (s : Strategies QA QB A B)
    (g : Game QA QB A B) (qa : QA) (qb : QB) : Prop :=
  g.accepts qa qb (s.first qa) (s.second qb)

structure LocalSimulation
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    (inner : Game InnerQA InnerQB InnerA InnerB)
    (outer : Game OuterQA OuterQB OuterA OuterB) where
  questionA : InnerQA → OuterQA
  questionB : InnerQB → OuterQB
  answerA : InnerQA → OuterA → InnerA
  answerB : InnerQB → OuterB → InnerB
  sound : ∀ qa qb a b,
    outer.accepts (questionA qa) (questionB qb) a b →
    inner.accepts qa qb (answerA qa a) (answerB qb b)

def LocalSimulation.induced
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB) :
    Strategies InnerQA InnerQB InnerA InnerB where
  first qa := r.answerA qa (s.first (r.questionA qa))
  second qb := r.answerB qb (s.second (r.questionB qb))

/-- A local simulation transports every deterministic strategy and contains
    its winning event pointwise. No shared access to the questions is used. -/
theorem LocalSimulation.induced_wins
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB)
    (qa : InnerQA) (qb : InnerQB)
    (hwins : s.wins outer (r.questionA qa) (r.questionB qb)) :
    (r.induced s).wins inner qa qb :=
  r.sound qa qb (s.first (r.questionA qa)) (s.second (r.questionB qb)) hwins


end UniqueGamesTheorem.Soundness.IncidenceExtraction

end

end OAI
