import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import OAI.Computability.UniqueGames.Reduction.ActualSourceLemmas

namespace OAI.UniqueGamesTheorem.Reduction.SourceCounting
open ActualSource
open scoped BigOperators

/-- Uniform finite events are counted with their occurrence multiplicities. -/
theorem sum_bool_indicator_eq_count_ofFn {n : Nat} (p : Fin n → Bool) :
    (∑ i, if p i then (1 : ℚ) else 0) = ((List.ofFn p).countP id : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.countP_cons, ih]
    cases p 0 <;> simp [add_comm]

theorem expect_bool_indicator_eq_count_ofFn {n : Nat} (p : Fin n → Bool) :
    Finset.univ.expect (fun i : Fin n => if p i then (1 : ℚ) else 0) =
      ((List.ofFn p).countP id : ℚ) / n := by
  rw [Fintype.expect_eq_sum_div_card, sum_bool_indicator_eq_count_ofFn]
  simp

theorem failure_eq_count (S : Source) (A : Fin S.variables → Bool) :
    S.failure A =
      (S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) / S.occurrences := by
  have hp := expect_bool_indicator_eq_count_ofFn
    (fun i : Fin S.occurrences => !S.satisfied A i)
  have hmap : List.ofFn (fun i : Fin S.occurrences => !S.satisfied A i) =
      S.sourceList.map (fun e => !CloneGap.satisfied e A) := by
    simp only [Source.sourceList, List.map_ofFn, Source.satisfied, Function.comp_def]
  rw [hmap] at hp
  simpa only [Source.failure, List.countP_map, Function.comp_def, id_eq,
    Bool.not_eq_true', Bool.eq_false_iff, ite_not] using hp

theorem count_complement {α : Type*} (es : List α) (p : α → Bool) :
    es.countP (fun e => !p e) + es.countP p = es.length := by
  simpa [Nat.add_comm] using (es.length_eq_countP_add_countP p).symm

theorem failure_add_satisfaction (S : Source) (A : Fin S.variables → Bool) :
    S.failure A +
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ) / S.occurrences = 1 := by
  rw [failure_eq_count, ← add_div]
  have h := count_complement S.sourceList (fun e => CloneGap.satisfied e A)
  have hc : ((S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) +
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ)) = S.occurrences := by
    exact_mod_cast (h.trans S.sourceList_length)
  rw [hc, div_self]
  exact_mod_cast Nat.ne_of_gt S.nonempty

end OAI.UniqueGamesTheorem.Reduction.SourceCounting
