/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Std
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI

section

/-!
Bit-length bounds for the concrete unique-game serialization. Every stored
constraint occurrence and every entry of its forward permutation table is
encoded. These are output-size bounds, not machine running-time bounds.
-/

namespace UniqueGamesTheorem.Reduction.GameEncodingSize

open Foundations.Target Foundations.Complexity

/-- The full table has `q` labels, each with unary encoding length at most `q+1`.
The conservative bound remains valid when the alphabet is empty. -/
theorem tableBits_length_le {q : Nat} (table : PermutationTable q) :
    (encodeWords (tableWords table)).length ≤ q * (q + 1) := by
  have h := encodeWords_length_le (tableWords table) q (by
    intro value hvalue
    obtain ⟨label, _, hlabel⟩ := List.mem_map.mp hvalue
    rw [← hlabel]
    exact Nat.le_of_lt label.isLt)
  simpa only [tableWords_length] using h


end UniqueGamesTheorem.Reduction.GameEncodingSize

end

section

namespace UniqueGamesTheorem.Reduction.Incidence

structure Triple where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq


universe variableUniverse indexUniverse

structure Equation (Variable : Type variableUniverse) where
  first : Variable
  second : Variable
  third : Variable
  rhs : Bool

variable {Variable : Type variableUniverse} {Index : Type indexUniverse}

inductive Slot where
  | first
  | second
  | third
  deriving DecidableEq


end UniqueGamesTheorem.Reduction.Incidence

end

end OAI
