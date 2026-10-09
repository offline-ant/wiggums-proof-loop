/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineExpanderRowCleanup
import OAI.Computability.UniqueGames.Machines.MachineExpanderRowDivision
import OAI.Computability.UniqueGames.Machines.MachineExpanderRowEmitLemmas

namespace OAI

section

/-!
# Concrete data and tape frames for an actual expander-row computation

Only the five actual row inputs are stored. Every address, table return and
finite control value below is computed from those inputs. The thirteen tape
frames use the existing phase-output functions, without a second normalized
representation. Concrete tape reads reduce directly. These are data identities
and size bounds, not assumed machine executions.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

structure RowData (v d : Nat) where
  oldTable : Table v (degree d)
  smallTable : Table (cloudSize d) d
  inputVertex : Fin v
  inputCloud : Fin (cloudSize d)
  inputPort : Fin (degree d)

def rowData {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) : RowData v d :=
  ⟨G, H, vertex, cloud, port⟩

namespace RowData

variable {v d : Nat} (r : RowData v d)

def control0 : Control d := start r.smallTable r.inputCloud r.inputPort
def firstRow : Fin (v * degree d) := rowIndex v (degree d) (r.inputVertex, firstOffset r.control0)
def firstValue : Nat := (reverseIndex r.oldTable r.firstRow).val
def firstPair : Fin v × Fin (degree d) := lookup r.oldTable (r.inputVertex, firstOffset r.control0)
def firstVertex : Fin v := r.firstPair.1
def firstReturn : Fin (degree d) := r.firstPair.2
def control1 : Control d := receiveFirst r.control0 r.firstReturn
def secondRow : Fin (v * degree d) := rowIndex v (degree d) (r.firstVertex, secondOffset r.control1)
def secondValue : Nat := (reverseIndex r.oldTable r.secondRow).val
def secondPair : Fin v × Fin (degree d) := lookup r.oldTable (r.firstVertex, secondOffset r.control1)
def secondVertex : Fin v := r.secondPair.1
def secondReturn : Fin (degree d) := r.secondPair.2
def control2 : Control d := receiveSecond r.smallTable r.control1 r.secondReturn
def query1 : Nat := firstAddress r.inputVertex.val r.control0
def query2 : Nat := secondAddress r.firstVertex.val r.control1
def finalValue : Nat := outputAddress r.secondVertex.val r.control2
def tableLength : Nat := (encodeWords (rotationWords r.oldTable)).length

theorem query1_eq_firstRow : r.query1 = r.firstRow.val :=
  firstAddress_eq_rowIndex r.inputVertex r.control0

theorem query2_eq_secondRow : r.query2 = r.secondRow.val :=
  secondAddress_eq_rowIndex r.firstVertex r.control1

@[simp] theorem firstValue_div_degree : r.firstValue / degree d = r.firstVertex.val := rfl
@[simp] theorem firstValue_mod_degree : r.firstValue % degree d = r.firstReturn.val := rfl
@[simp] theorem secondValue_div_degree : r.secondValue / degree d = r.secondVertex.val := rfl
@[simp] theorem secondValue_mod_degree : r.secondValue % degree d = r.secondReturn.val := rfl

theorem firstReturn_eq_residue (positive : 0 < d) :
    r.firstReturn = MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive)
      r.firstValue := Fin.ext rfl

theorem secondReturn_eq_residue (positive : 0 < d) :
    r.secondReturn = MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive)
      r.secondValue := Fin.ext rfl


theorem rows_le_tableLength : v * degree d ≤ r.tableLength := by
  simp only [tableLength, encodeWords_length, rotationWords_length]
  omega

theorem query1_le_tableLength : r.query1 ≤ r.tableLength := by
  rw [query1_eq_firstRow]
  exact r.firstRow.isLt.le.trans r.rows_le_tableLength

theorem query2_le_tableLength : r.query2 ≤ r.tableLength := by
  rw [query2_eq_secondRow]
  exact r.secondRow.isLt.le.trans r.rows_le_tableLength

theorem firstValue_le_tableLength : r.firstValue ≤ r.tableLength :=
  (reverseIndex r.oldTable r.firstRow).isLt.le.trans r.rows_le_tableLength

theorem secondValue_le_tableLength : r.secondValue ≤ r.tableLength :=
  (reverseIndex r.oldTable r.secondRow).isLt.le.trans r.rows_le_tableLength

theorem inputVertex_le_tableLength : r.inputVertex.val ≤ r.tableLength := by
  have hq : 1 ≤ degree d := Nat.zero_lt_of_lt r.inputPort.isLt
  have hv : v ≤ v * degree d := by simpa using Nat.mul_le_mul_left v hq
  exact r.inputVertex.isLt.le.trans (hv.trans r.rows_le_tableLength)

theorem firstVertex_le_tableLength : r.firstVertex.val ≤ r.tableLength := by
  rw [← firstValue_div_degree]
  exact (Nat.div_le_self r.firstValue (degree d)).trans r.firstValue_le_tableLength

theorem secondVertex_le_tableLength : r.secondVertex.val ≤ r.tableLength := by
  rw [← secondValue_div_degree]
  exact (Nat.div_le_self r.secondValue (degree d)).trans r.secondValue_le_tableLength

theorem firstReturn_le_tableLength : r.firstReturn.val ≤ r.tableLength := by
  rw [← firstValue_mod_degree]
  exact (Nat.mod_le r.firstValue (degree d)).trans r.firstValue_le_tableLength

theorem secondReturn_le_tableLength : r.secondReturn.val ≤ r.tableLength := by
  rw [← secondValue_mod_degree]
  exact (Nat.mod_le r.secondValue (degree d)).trans r.secondValue_le_tableLength

end RowData

variable {v d : Nat}

/-- The row starts with its input, table and accumulator; all work tapes are empty. -/
def frame0 (r : RowData v d) (output : List Bool) : Tape → List Bool
  | .inputVertex => encodeWord r.inputVertex.val
  | .table => encodeWords (rotationWords r.oldTable)
  | .output => output
  | _ => []

def frame1 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  initializedTapes id (frame0 r output)
def frame2 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  emittedWord .queryReverse (frame1 r output) r.query1
def frame3 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  Reduction.MachineTransfer.tapesAt .queryReverse .queryIndex (frame2 r output) []
    (encodeWord r.query1)
def frame4 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  lookupResultTapes id (frame3 r output) r.firstValue []
def frame5 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  divisionOutput d id .quotientFirst .remainderFirst (frame4 r output) r.firstValue [] [] []
def frame6 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  clearedQueryTapes id (frame5 r output)
def frame7 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  emittedWord .queryReverse (frame6 r output) r.query2
def frame8 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  Reduction.MachineTransfer.tapesAt .queryReverse .queryIndex (frame7 r output) []
    (encodeWord r.query2)
def frame9 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  lookupResultTapes id (frame8 r output) r.secondValue []
def frame10 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  divisionOutput d id .quotientSecond .remainderSecond (frame9 r output) r.secondValue [] [] []
def frame11 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  emittedWord .output (frame10 r output) r.finalValue
def frame12 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  cleanupTapes id (frame11 r output)

theorem final_frame_eq (r : RowData v d) (output : List Bool) :
    frame12 r output = emittedWord .output (frame0 r output) r.finalValue := by
  funext tape
  cases tape <;> rfl

theorem cleanupSteps_le_tableLength (r : RowData v d) (output : List Bool) :
    cleanupSteps id (frame11 r output) ≤ 6 * (r.tableLength + 1) + 6 := by
  have h1 := r.firstVertex_le_tableLength
  have h2 := r.secondVertex_le_tableLength
  have h3 := r.firstReturn_le_tableLength
  have h4 := r.secondReturn_le_tableLength
  simp [cleanupSteps, frame11, frame10, frame9, frame8, frame7, frame6, frame5,
    emittedWord, divisionOutput, MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
    MachineCopy.forkTapes, lookupResultTapes, Reduction.MachineTransfer.tapesAt,
    clearedQueryTapes, encodeWord_length]
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end

end OAI
