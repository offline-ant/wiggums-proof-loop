import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas

namespace OAI.UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

/-- Position of a drain in the existing finite-sequence schedule. This lets
callers keep their numbered control labels while sharing the list trace. -/
def labelIndex {K : Type} : (chosen : List K) → Label chosen → Fin chosen.length
  | [], label => nomatch label
  | _ :: _, .inl _ => 0
  | _ :: chosen, .inr label => (labelIndex chosen label).succ

/-- The list implementation uses the caller's consecutive numbered labels. -/
theorem instruction_labelIndex {K Λ σ : Type} (chosen : List K)
    (labels : Fin chosen.length → Λ) (exit : Option Λ) (l : Label chosen) :
    instruction (σ := σ) chosen (fun l => labels (labelIndex chosen l)) exit l =
      MachineDrain.drain chosen[(labelIndex chosen l).val]
        (labels (labelIndex chosen l))
        (if h : (labelIndex chosen l).val + 1 < chosen.length then
          some (labels ⟨(labelIndex chosen l).val + 1, h⟩) else exit) := by
  induction chosen with
  | nil => exact nomatch l
  | cons head tail ih =>
    rcases l with u | l
    · cases tail <;> rfl
    · simpa [instruction, MachineFiniteSequence.instruction, labelIndex, Fin.val_succ,
        Nat.add_assoc, Nat.lt_iff_add_one_le] using ih (fun i => labels i.succ) l

/-- Distinct drains have exactly their entry lengths as cost: earlier drains
cannot change any later word. -/
theorem steps_of_nodup {K : Type} [DecidableEq K] (chosen : List K)
    (distinct : chosen.Nodup) (base : Tapes K) :
    steps chosen base = (chosen.map (fun k => (base k).length + 1)).sum := by
  induction chosen generalizing base with
  | nil => rfl
  | cons source chosen ih =>
    have hn := List.nodup_cons.mp distinct
    have unchanged : chosen.map (fun k => ((Function.update base source []) k).length + 1) =
        chosen.map (fun k => (base k).length + 1) := by
      apply List.map_congr_left
      intro k hk
      rw [Function.update_of_ne (show k ≠ source from fun h => hn.1 (h ▸ hk))]
    rw [steps, ih hn.2, unchanged]
    rfl

end OAI.UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany
