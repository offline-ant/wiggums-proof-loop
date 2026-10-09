/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Data.List.OfFn
import OAI.Computability.UniqueGames.PCP.PreprocessingOverlayTables

namespace OAI

section

/-! Exact codec expansion of the executable lazy graph table. Each vertex
contributes its `d` always-accepting selfloops, followed by its `d` stored
constraints with the reverse field changed by the displayed div/mod map. -/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingLazyWords

open PortTables GraphTables PreprocessingOverlayTables
open UniqueGamesTheorem.Foundations.Complexity

variable {n d : Nat}

def row (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    DartRow n (n * d) :=
  ⟨v, table.reverseIndex[rowIndex n d (v, p)], table.relations[rowIndex n d (v, p)]⟩

def trueRelation : RelationTable := Vector.replicate 4096 true

def stayRow (d : Nat) (v : Fin n) (p : Fin d) : DartRow n (n * (2 * d)) :=
  ⟨v, rowIndex n (2 * d) (v, lazyPorts d (false, p)), trueRelation⟩

def moveRow (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    DartRow n (n * (2 * d)) :=
  ⟨v, rowIndex n (2 * d) ((rotation table (v, p)).1,
    lazyPorts d (true, (rotation table (v, p)).2)),
    table.relations[rowIndex n d (v, p)]⟩

/-- The machine's fixed-degree numerical map for an old reverse-row index. -/
def reverseMap (d j : Nat) : Nat := 2 * d * (j / d) + d + j % d

theorem row_lazy_stay (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    row (lazy table) v (lazyPorts d (false, p)) = stayRow d v p := by
  apply PortTables.row_eq _ _ _ _ _ (lazy_rotation_false table v p)
  intro a b
  simpa only [trueRelation, relationAt, Fin.getElem_fin, Vector.getElem_replicate] using
    lazy_accepts_false table v p a b

theorem row_lazy_move (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    row (lazy table) v (lazyPorts d (true, p)) = moveRow table v p := by
  exact PortTables.row_eq _ _ _ _ _ (lazy_rotation_true table v p)
    (lazy_accepts_true table v p)

theorem stayRow_reverse_val (v : Fin n) (p : Fin d) :
    (stayRow d v p).reverseIndex.val = 2 * d * v.val + p.val := by
  simp only [stayRow, rowIndex_val, lazyPorts_false_val]
  omega

theorem moveRow_reverse_val (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    (moveRow table v p).reverseIndex.val =
      reverseMap d (row table v p).reverseIndex.val := by
  simp only [moveRow, rowIndex_val, lazyPorts_true_val, reverseMap, row]
  change (table.reverseIndex[rowIndex n d (v, p)]).val % d + d +
      (2 * d) * ((table.reverseIndex[rowIndex n d (v, p)]).val / d) = _
  omega

theorem relationWords_true : relationWords trueRelation = List.replicate 4096 1 := by
  simp only [relationWords, trueRelation, Vector.toList_replicate,
    List.map_replicate, bitWord, ite_true]


theorem moveRow_words (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    rowWords (moveRow table v p) =
      [v.val, reverseMap d (row table v p).reverseIndex.val] ++
        relationWords (row table v p).relation := by
  rw [rowWords, moveRow_reverse_val]
  rfl

/-- Finite mixed-radix indexing agrees with the actual row-vector order. -/
theorem ofFn_rowIndex {α : Type*} (f : Fin (n * d) → α) :
    List.ofFn f = (List.ofFn fun v : Fin n =>
      List.ofFn fun p : Fin d => f (rowIndex n d (v, p))).flatten := by
  simpa only [rowIndex, finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm, Nat.add_comm] using
    List.ofFn_mul f

theorem flatRows_list (table : PortTables.Table n d) :
    (flatRows table).toList =
      (List.ofFn fun v : Fin n => List.ofFn (row table v)).flatten := by
  rw [flatRows, Vector.toList_ofFn, ofFn_rowIndex]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Boolean false precedes true in the executable lazy port numbering. -/
theorem ofFn_lazyPorts {α : Type*} (f : Fin (2 * d) → α) :
    List.ofFn f = List.ofFn (fun p => f (lazyPorts d (false, p))) ++
      List.ofFn (fun p => f (lazyPorts d (true, p))) := by
  have hf (p : Fin d) : rowIndex 2 d (0, p) = lazyPorts d (false, p) := by
    apply Fin.ext
    simp only [rowIndex_val, Fin.val_zero, Nat.mul_zero, Nat.add_zero, lazyPorts_false_val]
  have ht (p : Fin d) : rowIndex 2 d ((0 : Fin 1).succ, p) = lazyPorts d (true, p) := by
    apply Fin.ext
    simp only [rowIndex_val, Fin.val_succ, Fin.val_zero, Nat.zero_add,
      Nat.mul_one, lazyPorts_true_val]
  simpa only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, hf, ht] using (ofFn_rowIndex (n := 2) (d := d) f)

def vertexRows (table : PortTables.Table n d) (v : Fin n) :
    List (DartRow n (n * (2 * d))) :=
  List.ofFn (stayRow d v) ++ List.ofFn (moveRow table v)


/-- Every stored lazy row, with no permutation or multiset quotient. -/
theorem flatRows_lazy (table : PortTables.Table n d) :
    (flatRows (lazy table)).toList = (List.ofFn (vertexRows table)).flatten := by
  rw [flatRows_list]
  apply congrArg List.flatten
  congr 1
  funext v
  rw [ofFn_lazyPorts]
  simp only [row_lazy_stay, row_lazy_move]
  rfl


/-- The full existing word codec, including both graph header fields. -/
theorem tableWords_lazy (table : PortTables.Table n d) :
    PortTables.tableWords (lazy table) =
      [n, n * (2 * d)] ++ (List.ofFn (vertexRows table)).flatten.flatMap rowWords := by
  rw [PortTables.tableWords_eq, flatRows_lazy]

/-- The same statement for the exact unary-delimited Boolean input/output codec. -/
theorem tableBits_lazy (table : PortTables.Table n d) :
    PortTables.tableBits (lazy table) =
      encodeWords ([n, n * (2 * d)] ++
        (List.ofFn (vertexRows table)).flatten.flatMap rowWords) := by
  change encodeWords (PortTables.tableWords (lazy table)) = _
  rw [tableWords_lazy]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingLazyWords

end

end OAI
