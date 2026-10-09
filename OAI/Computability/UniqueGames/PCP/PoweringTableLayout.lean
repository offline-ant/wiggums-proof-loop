/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Data.List.OfFn
import OAI.Computability.UniqueGames.PCP.PoweringTablesLemmas

namespace OAI

/-!
# Vertex-major serialization of the actual powering table

Each vertex contributes a fixed number of consecutive stored dart rows. The
identities below group the actual vector, including every predicate entry, and
then apply the shared word codec. They do not assume an output layout or assert
a machine running time. Unary bit lengths can vary with the stored indices.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout

open UniqueGamesTheorem.Foundations.Complexity
open PoweringTables PoweringEnumeration

/-- One adjacent orientation pair for each recorded port word. -/
def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

theorem dartCount_eq_vertex_blocks (vertices d n : Nat) :
    dartCount vertices d n = vertices * blockSize d n := by
  simp only [blockSize]
  unfold dartCount
  ac_rfl

/-- The index of a stored row within the consecutive block of vertex `v`. -/
def blockIndex {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (j : Fin (blockSize d n)) : Fin (dartCount vertices d n) :=
  Fin.cast (dartCount_eq_vertex_blocks vertices d n).symm
    (finProdFinEquiv (v, j))

@[simp] theorem blockIndex_val {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (j : Fin (blockSize d n)) :
    (blockIndex d n v j).val = blockSize d n * v.val + j.val := by
  change j.val + blockSize d n * v.val = blockSize d n * v.val + j.val
  exact Nat.add_comm _ _

/-- The consecutive block is the actual vertex-major recorded-walk order. -/
theorem blockIndex_eq_encodeDart {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) (direction : Bool) :
    blockIndex d n v (dartBlockEquiv d n (p, direction)) =
      encodeDart vertices d n (direction, (v, p)) := by
  apply Fin.ext
  erw [blockIndex_val]

/-- Exactly the stored rows at positions `B*v, ..., B*v+B-1`. -/
def vertexRows {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) :
    List (GenericGraphTables.DartRow (labelCount d n) vertices (dartCount vertices d n)) :=
  List.ofFn (fun j : Fin (blockSize d n) => (table input n).rows[blockIndex d n v j])

/-- All fields of these stored rows, in their actual codec order. -/
def vertexRowWords {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) : List Nat :=
  (vertexRows input n v).flatMap GenericGraphTables.rowWords

/-- Actual unary serialization of the complete vertex block. -/
def vertexRowBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) : List Bool :=
  encodeWords (vertexRowWords input n v)


/-- Regroup a stored vector without changing, omitting, or permuting a row. -/
private theorem vector_blocks {α : Type*} {m vertices width : Nat}
    (sameCount : m = vertices * width) (rows : Vector α m) :
    rows.toList = (List.finRange vertices).flatMap (fun v =>
      List.ofFn (fun j : Fin width =>
        rows[Fin.cast sameCount.symm (finProdFinEquiv (v, j))])) := by
  subst m
  conv_lhs => rw [← Vector.ofFn_getElem (xs := rows), Vector.toList_ofFn]
  rw [List.ofFn_mul]
  simp [List.finRange, List.flatMap_def, List.map_ofFn, finProdFinEquiv,
    Function.comp_def, Nat.add_comm, Nat.mul_comm]

/-- Every actual stored row occurs once in its vertex's consecutive block. -/
theorem rowList_eq_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.rowList (table input n) =
      (List.finRange vertices).flatMap (vertexRows input n) := by
  exact vector_blocks (dartCount_eq_vertex_blocks vertices d n) (table input n).rows

/-- The full word stream, including its two header fields, in vertex order. -/
theorem outputWords_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.tableWords (table input n) =
      [vertices, dartCount vertices d n] ++
        (List.finRange vertices).flatMap (vertexRowWords input n) := by
  change [vertices, dartCount vertices d n] ++
      (GenericGraphTables.rowList (table input n)).flatMap GenericGraphTables.rowWords = _
  rw [rowList_eq_vertexRows]
  erw [List.flatMap_assoc]
  rfl

theorem outputBits_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    outputBits input n = encodeWords [vertices, dartCount vertices d n] ++
      (List.finRange vertices).flatMap (vertexRowBits input n) := by
  unfold outputBits GenericGraphTables.tableBits
  rw [outputWords_vertexRows, encodeWords_append, UniqueGamesTheorem.Foundations.Complexity.encodeWords_flatMap]
  rfl


end UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout

end OAI
