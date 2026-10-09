/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.PCP.SourceOccurrences
import OAI.Computability.UniqueGames.Reduction.CanonicalBodyTemplateLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceAddressArithmetic

open scoped BigOperators
open Target SourceContexts SourceOccurrences

theorem variable_rank (F : Formula) (u : ℕ) (v : VariableContext F u) :
    ((variableEncoding F u).code v).val =
      ∑ t : Fin u, (v t).val * F.variables ^ t.val := rfl

theorem clause_rank (F : Formula) (u : ℕ) (c : ClauseContext F u) :
    ((clauseEncoding F u).code c).val =
      ∑ t : Fin u, (c t).val * F.clauses.length ^ t.val := rfl

theorem left_address (F : Formula) (u : ℕ) (v : VariableContext F u) (f : Cube (I u)) :
    ((proofEncoding F u).code (.inl (v, f))).val =
      (((iEncoding u).function Encoding.bool).code f).val +
        2 ^ (2 ^ u) * ((variableEncoding F u).code v).val := rfl

theorem right_address (F : Formula) (u : ℕ) (c : ClauseContext F u) (g : Cube (J u)) :
    ((proofEncoding F u).code (.inr (.inl (c, g)))).val =
      F.variables ^ u * 2 ^ (2 ^ u) +
        ((((jEncoding u).function Encoding.bool).code g).val +
          2 ^ (8 ^ u) * ((clauseEncoding F u).code c).val) := rfl

theorem dummy_address (F : Formula) (u : ℕ) :
    (dummyIndex F u).val =
      F.variables ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u) := by
  change F.variables ^ u * 2 ^ (2 ^ u) +
    (F.clauses.length ^ u * 2 ^ (8 ^ u) + 0) = _
  omega


end UniqueGamesTheorem.Foundations.Hastad.SourceAddressArithmetic

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceBounds

open Target
open UniqueGamesTheorem.Reduction

theorem formulaBits_length (F : Formula) :
    (Complexity.formulaBits F).length = F.variables + F.clauses.length + 2 +
      (Complexity.encodeWords (F.clauses.flatMap Complexity.clauseWords)).length := by
  simp only [Complexity.formulaBits, Complexity.formulaWords,
    Complexity.encodeWords_append, List.length_append, Complexity.encodeWords,
    Complexity.encodeWord_length, List.length_nil]
  omega

theorem formulaBits_length_ge_variables (F : Formula) :
    F.variables ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

theorem formulaBits_length_ge_clauses (F : Formula) :
    F.clauses.length ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

theorem formulaBits_length_ge_two (F : Formula) :
    2 ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

/-- The two padded long-code tables and one global dummy bit. -/
def bitCountFormula (n m u : ℕ) : ℕ :=
  n ^ u * 2 ^ (2 ^ u) + m ^ u * 2 ^ (8 ^ u) + 1

/-- Depends on the fixed repetition count alone. -/
def bitCoefficient (u : ℕ) : ℕ := 2 ^ (2 ^ u) + 2 ^ (8 ^ u) + 1


theorem one_le_input_power (F : Formula) (u : ℕ) :
    1 ≤ (Complexity.formulaBits F).length ^ u := by
  apply Nat.one_le_pow
  have h := formulaBits_length_ge_two F
  omega

theorem bitCountFormula_le_input (F : Formula) (u : ℕ) :
    bitCountFormula F.variables F.clauses.length u ≤
      bitCoefficient u * (Complexity.formulaBits F).length ^ u := by
  have hn := Nat.pow_le_pow_left (formulaBits_length_ge_variables F) u
  have hm := Nat.pow_le_pow_left (formulaBits_length_ge_clauses F) u
  have hpos := one_le_input_power F u
  unfold bitCountFormula bitCoefficient
  calc
    _ ≤ (Complexity.formulaBits F).length ^ u * 2 ^ (2 ^ u) +
        (Complexity.formulaBits F).length ^ u * 2 ^ (8 ^ u) +
        (Complexity.formulaBits F).length ^ u :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ hn) (Nat.mul_le_mul_right _ hm)) hpos
    _ = _ := by ring


open SourceOccurrences SourceContexts


/-- The executable radix enumeration has the same fixed size. -/
theorem testTapeEncoding_size (u D : ℕ) :
    (SourceOccurrences.testTapeEncoding u D).size =
      2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u)) := rfl


/-- Bound on the actual variable count, including padded addresses and dummy. -/
theorem nBits_le_input (F : Formula) (u : ℕ) :
    nBits F u ≤ bitCoefficient u * (Complexity.formulaBits F).length ^ u := by
  have h := bitCountFormula_le_input F u
  simpa only [nBits_eq, bitCountFormula, Nat.add_assoc] using h


end UniqueGamesTheorem.Foundations.Hastad.SourceBounds

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.Encoding

variable {α β γ : Type}

theorem prod_decode_pair (a : Encoding α) (b : Encoding β)
    (i : Fin a.size) (j : Fin b.size) :
    (a.prod b).code.symm (finProdFinEquiv (i, j)) =
      (a.code.symm i, b.code.symm j) := by
  change (a.code.symm (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1,
    b.code.symm (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2) = _
  rw [Equiv.symm_apply_apply]

theorem prod_decode_mk (a : Encoding α) (b : Encoding β)
    (i : Fin a.size) (j : Fin b.size)
    (h : i.val * b.size + j.val < a.size * b.size) :
    (a.prod b).code.symm ⟨i.val * b.size + j.val, h⟩ =
      (a.code.symm i, b.code.symm j) := by
  have he : (⟨i.val * b.size + j.val, h⟩ : Fin (a.size * b.size)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  change (a.code.symm (finProdFinEquiv.symm (⟨i.val * b.size + j.val, h⟩ :
    Fin (a.size * b.size))).1,
    b.code.symm (finProdFinEquiv.symm (⟨i.val * b.size + j.val, h⟩ :
    Fin (a.size * b.size))).2) = _
  rw [he]
  exact prod_decode_pair a b i j

/-- Increasing product rank enumerates the first factor outside and the
second factor inside, including when either factor is empty. -/
theorem enumerate_prod (a : Encoding α) (b : Encoding β) :
    (a.prod b).enumerate =
      a.enumerate.flatMap (fun x => b.enumerate.map (fun y => (x, y))) := by
  change List.ofFn (fun q : Fin (a.size * b.size) =>
    (a.code.symm (finProdFinEquiv.symm q).1,
     b.code.symm (finProdFinEquiv.symm q).2)) = _
  rw [List.ofFn_mul]
  simp only [enumerate, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  exact prod_decode_mk a b i j _


end UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.Encoding

namespace UniqueGamesTheorem.Foundations.Hastad.SourceEnumeration

open Target SourceContexts SourceOccurrences


end UniqueGamesTheorem.Foundations.Hastad.SourceEnumeration

end

end OAI
