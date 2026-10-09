/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Data.Fintype.Sum
import Std
import OAI.Computability.UniqueGames.Reduction.RealTargetLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.ActualCanonical

open Integration.BinaryLinear ActualHomogeneous
open scoped BigOperators

universe u v w
variable {Name : Type u} {Id : Type v} {R : Type w}
variable {k : Nat}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

inductive Record (Name : Type u) (Id : Type v) (R : Type w)
  | blank
  | single (name : Name) (coefficient : R)
  | full (occurrence : Id) (coefficients : Fin 3 → R)
  deriving DecidableEq

def recordEquiv : Record Name Id R ≃ Unit ⊕ ((Name × R) ⊕ (Id × (Fin 3 → R))) where
  toFun r := match r with
    | .blank => .inl ()
    | .single n c => .inr (.inl (n,c))
    | .full e a => .inr (.inr (e,a))
  invFun r := match r with
    | .inl _ => .blank
    | .inr (.inl (n,c)) => .single n c
    | .inr (.inr (e,a)) => .full e a
  left_inv r := by cases r <;> rfl
  right_inv r := by rcases r with u | (p | p) <;> cases ‹_› <;> rfl

noncomputable instance [Fintype Name] [Fintype Id] [Fintype R] :
    Fintype (Record Name Id R) := Fintype.ofEquiv _ recordEquiv.symm

abbrev Data (k : Nat) (Name : Type u) (Id : Type v) (R : Type w) :=
  R × (Fin k → Record Name Id R)

def pivot (a : Fin 3 → R) : R :=
  if a 0 = a 1 then a 0 else if a 0 = a 2 then a 0 else a 2

def translate (a : Fin 3 → R) (t : R) : Fin 3 → R := fun i => a i + t
def normalize (a : Fin 3 → R) : Fin 3 → R := translate a (pivot a)

def record (names : Id → Fin 3 → Name) (e : Id) (a : Fin 3 → R) :
    Record Name Id R :=
  if a 0 = a 1 then
      if a 0 = a 2 then .blank else .single (names e 2) (a 2 + a 0)
    else if a 0 = a 2 then .single (names e 1) (a 1 + a 0)
    else if a 1 = a 2 then .single (names e 0) (a 0 + a 2)
    else .full e (normalize a)

def data (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z : R) (a : Fin k → Fin 3 → R) : Data k Name Id R :=
  (z + ∑ j, rhs (occ j) • pivot (a j), fun j => record names (occ j) (a j))

def standardTriple (X : E k →ₗ[F2] R) (j : Fin k) : Fin 3 → R :=
  ![X (firstBasis j), X (secondBasis j), 0]

def canonical (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (X : E k →ₗ[F2] R) : Data k Name Id R :=
  data occ names rhs (X (hBasis k)) (standardTriple X)

def ambientEval (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R) (x : E k) : R :=
  x.1 • z + ∑ j, ((x.2 j).1 • a j 0 + (x.2 j).2 • a j 1 +
    (b j * x.1 + (x.2 j).1 + (x.2 j).2) • a j 2)

def Represents (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R)
    (X : E k →ₗ[F2] R) : Prop := ∀ x, ambientEval b z a x = X x

omit [DecidableEq R] in
theorem add_self (x : R) : x + x = 0 := by
  calc
    x + x = (1 + 1 : F2) • x := by simp [add_smul]
    _ = 0 := by rw [show (1 + 1 : F2) = 0 by decide, zero_smul]

omit [DecidableEq R] in
theorem add_both (x y t : R) : (x + t) + (y + t) = x + y := by
  calc
    _ = (x + y) + (t + t) := by abel
    _ = _ := by rw [add_self, add_zero]

omit [Module F2 R] in
theorem pivot_translate (a : Fin 3 → R) (t : R) :
    pivot (translate a t) = pivot a + t := by
  classical
  by_cases h1 : a 0 = a 1 <;> by_cases h2 : a 0 = a 2 <;>
    simp [pivot, translate, h1, h2]

theorem normalize_translate (a : Fin 3 → R) (t : R) :
    normalize (translate a t) = normalize a := by
  unfold normalize
  rw [pivot_translate]
  funext i
  exact add_both _ _ _

theorem record_translate (names : Id → Fin 3 → Name) (e : Id) (a : Fin 3 → R) (t : R) :
    record names e (translate a t) = record names e a := by
  classical
  have hs (i : Fin 3) : translate a t i = a i + t := rfl
  simp only [record, hs, add_right_cancel_iff, add_both, normalize_translate]

theorem data_gauge (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (z : R) (a : Fin k → Fin 3 → R) (t : Fin k → R) :
    data occ names rhs (z + ∑ j, rhs (occ j) • t j) (fun j => translate (a j) (t j)) =
      data occ names rhs z a := by
  apply Prod.ext
  · simp only [data, pivot_translate, smul_add, Finset.sum_add_distrib]
    exact add_both _ _ _
  · funext j
    exact record_translate names (occ j) (a j) (t j)

theorem data_global_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (z c : R) (a : Fin k → Fin 3 → R) :
    data occ names rhs (z + c) a =
      ((data occ names rhs z a).1 + c, (data occ names rhs z a).2) := by
  apply Prod.ext
  · dsimp [data]; abel
  · rfl

theorem canonical_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (X : E k →ₗ[F2] R) (c : R) :
    canonical occ names rhs (X + tau.smulRight c) =
      ((canonical occ names rhs X).1 + c, (canonical occ names rhs X).2) := by
  have ht : standardTriple (X + tau.smulRight c) = standardTriple X := by
    funext j i
    fin_cases i <;> simp [standardTriple, tau, firstBasis, secondBasis]
  simp only [canonical, ht]
  have hg : (X + tau.smulRight c : E k →ₗ[F2] R) (hBasis k) = X (hBasis k) + c := by
    simp [hBasis, tau]
  rw [hg]
  exact data_global_shift occ names rhs _ c _

omit [DecidableEq R] in
@[simp] theorem ambientEval_hBasis (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R) :
    ambientEval b z a (hBasis k) = z + ∑ j, b j • a j 2 := by
  simp [ambientEval, hBasis]

omit [DecidableEq R] in
@[simp] theorem ambientEval_firstBasis (b : Fin k → F2) (z : R)
    (a : Fin k → Fin 3 → R) (j : Fin k) :
    ambientEval b z a (firstBasis j) = a j 0 + a j 2 := by
  classical
  simp only [ambientEval, firstBasis, zero_smul, zero_add, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

omit [DecidableEq R] in
@[simp] theorem ambientEval_secondBasis (b : Fin k → F2) (z : R)
    (a : Fin k → Fin 3 → R) (j : Fin k) :
    ambientEval b z a (secondBasis j) = a j 1 + a j 2 := by
  classical
  simp only [ambientEval, secondBasis, zero_smul, zero_add, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp


omit [DecidableEq R] in
/-- Equality on the homogeneous space forces the free-coordinate identities. -/
theorem extension_coefficients (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R)
    (X : E k →ₗ[F2] R) (h : Represents b z a X) :
    X (hBasis k) = z + ∑ j, b j • a j 2 ∧
      ∀ j, X (firstBasis j) = a j 0 + a j 2 ∧
        X (secondBasis j) = a j 1 + a j 2 := by
  constructor
  · simpa only [ambientEval_hBasis] using (h (hBasis k)).symm
  · intro j
    exact ⟨by simpa only [ambientEval_firstBasis] using (h (firstBasis j)).symm,
      by simpa only [ambientEval_secondBasis] using (h (secondBasis j)).symm⟩

/-- Every ambient extension of a genuine map gives the same canonical data. -/
theorem canonical_eq_of_extension (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z : R) (a : Fin k → Fin 3 → R) (X : E k →ₗ[F2] R)
    (h : Represents (fun j => rhs (occ j)) z a X) :
    canonical occ names rhs X = data occ names rhs z a := by
  obtain ⟨hz, ha⟩ := extension_coefficients _ z a X h
  have ht : standardTriple X = fun j => translate (a j) (a j 2) := by
    funext j i
    fin_cases i
    · exact (ha j).1
    · exact (ha j).2
    · exact (add_self (a j 2)).symm
  unfold canonical
  rw [hz, ht]
  exact data_gauge occ names rhs z a (fun j => a j 2)


def singletonTriple (i : Fin 3) (c : R) : Fin 3 → R := Pi.single i c

omit [Module F2 R] in
theorem pivot_singleton (i : Fin 3) (c : R) : pivot (singletonTriple i c) = 0 := by
  classical
  by_cases hc : c = 0 <;> fin_cases i <;> simp [singletonTriple, pivot, hc]

omit [Module F2 R] in
theorem record_singleton (names : Id → Fin 3 → Name) (e : Id) (i : Fin 3) (c : R) :
    record names e (singletonTriple i c) =
      (if c = 0 then Record.blank else Record.single (names e i) c) := by
  classical
  by_cases hc : c = 0 <;> fin_cases i <;>
    simp [record, singletonTriple, hc, eq_comm]

theorem singleton_global_adjustment (rhs : Id → F2) (e : Id) (i : Fin 3) (c : R) :
    rhs e • pivot (singletonTriple i c) = 0 := by rw [pivot_singleton, smul_zero]

omit [Module F2 R] in
/-- The hidden occurrence and its internal slot cannot affect a retained
single-variable record. The occurrence need not differ from other positions. -/
theorem singleton_locality (names : Id → Fin 3 → Name) (e e' : Id)
    (i i' : Fin 3) (c : R) (hname : names e i = names e' i') :
    record names e (singletonTriple i c) = record names e' (singletonTriple i' c) := by
  simp only [record_singleton, hname]

end UniqueGamesTheorem.Reduction.ActualCanonical

end

section

namespace UniqueGamesTheorem.Reduction.CloneGap

variable {α : Type*} {β : Type*} {Name : Type}


theorem count_const (xs : List α) (b : Bool) :
    xs.countP (fun _ => b) = if b then xs.length else 0 := by
  cases b <;> simp


abbrev Index := Nat
def indices : List Index := List.range 48
def collision (t : Index × Index × Index) : Bool :=
  (t.1 == t.2.1) || (t.1 == t.2.2) || (t.2.1 == t.2.2)


structure Equation (Name : Type) where
  first : Name
  second : Name
  third : Name
  rhs : Bool

def satisfied (e : Equation Name) (g : Name → Bool) : Bool :=
  (xor (xor (g e.first) (g e.second)) (g e.third)) == e.rhs


end UniqueGamesTheorem.Reduction.CloneGap

end

end OAI
