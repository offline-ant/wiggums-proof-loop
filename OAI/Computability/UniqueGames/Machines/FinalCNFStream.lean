/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Data.List.FinRange
import OAI.Computability.UniqueGames.Machines.FinalCNFMachineLemmas
import OAI.Computability.UniqueGames.Machines.FinalCNFRowPlanLemmas

namespace OAI

/-!
Exact row enumeration and input/output stream identities for the concrete
final-CNF machine. Rows occur in stored order, including repeated rows.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable

/-- The actual unprocessed suffix of the finite table's stored row indices. -/
def remainingEvents (table : GraphTables.Table) (r : Nat) : List (Fin table.darts) :=
  (List.finRange table.darts).drop r


def inputStream (table : GraphTables.Table) (events : List (Fin table.darts)) : List Bool :=
  events.flatMap (fun e => encodeWords (GraphTables.rowWords table.rows[e]))

def outputStream (plan : Plan) (table : GraphTables.Table)
    (events : List (Fin table.darts)) : List Bool :=
  events.flatMap (fun e => plan.flatMap (Emitter.commandBits (rowOperands table e)
    (rowRelation table e)))

@[simp] theorem remainingEvents_zero (table : GraphTables.Table) :
    remainingEvents table 0 = List.finRange table.darts := by
  simp [remainingEvents]


@[simp] theorem remainingEvents_done (table : GraphTables.Table) :
    remainingEvents table table.darts = [] := by
  simp [remainingEvents]

theorem remainingEvents_cons (table : GraphTables.Table) (r : Nat) (h : r < table.darts) :
    remainingEvents table r = ⟨r, h⟩ :: remainingEvents table (r + 1) := by
  unfold remainingEvents
  rw [List.drop_eq_getElem_cons (l := List.finRange table.darts) (i := r)
    (by simpa using h)]
  simp


@[simp] theorem inputStream_nil (table : GraphTables.Table) : inputStream table [] = [] := rfl

@[simp] theorem inputStream_cons (table : GraphTables.Table) (e : Fin table.darts)
    (events : List (Fin table.darts)) :
    inputStream table (e :: events) =
      encodeWords (GraphTables.rowWords table.rows[e]) ++ inputStream table events := rfl


@[simp] theorem outputStream_nil (plan : Plan) (table : GraphTables.Table) :
    outputStream plan table [] = [] := rfl

@[simp] theorem outputStream_cons (plan : Plan) (table : GraphTables.Table)
    (e : Fin table.darts) (events : List (Fin table.darts)) :
    outputStream plan table (e :: events) =
      plan.flatMap (Emitter.commandBits (rowOperands table e) (rowRelation table e)) ++
        outputStream plan table events := rfl


theorem inputStream_remaining_cons (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    inputStream table (remainingEvents table r) =
      encodeWords (GraphTables.rowWords table.rows[(⟨r, h⟩ : Fin table.darts)]) ++
        inputStream table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, inputStream_cons]

theorem outputStream_remaining_cons (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    outputStream plan table (remainingEvents table r) =
      plan.flatMap (Emitter.commandBits (rowOperands table ⟨r, h⟩)
        (rowRelation table ⟨r, h⟩)) ++
          outputStream plan table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, outputStream_cons]


theorem rowList_eq_finRange_map (table : GraphTables.Table) :
    GraphTables.rowList table = (List.finRange table.darts).map (fun e => table.rows[e]) := by
  rw [← List.ofFn_eq_map, ← Vector.toList_ofFn]
  change table.rows.toList = (Vector.ofFn (fun i => table.rows[i.val])).toList
  rw [Vector.ofFn_getElem]

/-- The stream starts at exactly the row suffix left by the checked header phase. -/
theorem inputStream_all (table : GraphTables.Table) :
    inputStream table (List.finRange table.darts) = tableRowsBits table := by
  change _ = encodeWords ((GraphTables.rowList table).flatMap GraphTables.rowWords)
  rw [rowList_eq_finRange_map, List.flatMap_map, encodeWords_flatMap]
  rfl

theorem inputStream_remaining_zero (table : GraphTables.Table) :
    inputStream table (remainingEvents table 0) = tableRowsBits table := by
  rw [remainingEvents_zero, inputStream_all]


end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
