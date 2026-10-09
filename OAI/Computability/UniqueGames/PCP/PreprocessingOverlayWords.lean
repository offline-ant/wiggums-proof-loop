/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.PCP.ExpanderRowControlLemmas
import OAI.Computability.UniqueGames.PCP.PreprocessingLazyWords

namespace OAI

section

/-! Exact stored-row and codec expansion of the executable overlay. Within
each vertex block, all original ports precede all expander ports. -/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayWords

open PortTables GraphTables PreprocessingOverlayTables
open Complexity

variable {n d e : Nat}

abbrev row := @PreprocessingLazyWords.row
abbrev trueRelation := PreprocessingLazyWords.trueRelation

def oldReverseMap (d e j : Nat) : Nat := (d + e) * (j / d) + j % d
def expanderReverseMap (d e j : Nat) : Nat := (d + e) * (j / e) + d + j % e

def oldRow (G : PortTables.Table n d) (e : Nat) (v : Fin n) (p : Fin d) :
    DartRow n (n * (d + e)) :=
  ⟨v, rowIndex n (d + e) ((rotation G (v, p)).1,
    overlayPorts d e (.inl (rotation G (v, p)).2)),
    G.relations[rowIndex n d (v, p)]⟩

def expanderRow (d : Nat) (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) :
    DartRow n (n * (d + e)) :=
  ⟨v, rowIndex n (d + e) ((ExpanderTables.lookup H (v, p)).1,
    overlayPorts d e (.inr (ExpanderTables.lookup H (v, p)).2)), trueRelation⟩

theorem row_overlay_old (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (p : Fin d) :
    row (overlay G H) v (overlayPorts d e (.inl p)) = oldRow G e v p := by
  exact PortTables.row_eq _ _ _ _ _ (overlay_rotation_old G H v p)
    (overlay_accepts_old G H v p)

theorem row_overlay_expander (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (p : Fin e) :
    row (overlay G H) v (overlayPorts d e (.inr p)) = expanderRow d H v p := by
  apply PortTables.row_eq _ _ _ _ _ (overlay_rotation_expander G H v p)
  intro a b
  simpa only [trueRelation, PreprocessingLazyWords.trueRelation, relationAt,
    Fin.getElem_fin, Vector.getElem_replicate] using overlay_accepts_expander G H v p a b

theorem oldRow_reverse_val (G : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    (oldRow G e v p).reverseIndex.val = oldReverseMap d e (row G v p).reverseIndex.val := by
  simp only [oldRow, rowIndex_val, overlayPorts_inl_val, oldReverseMap, row,
    PreprocessingLazyWords.row]
  change (G.reverseIndex[rowIndex n d (v, p)]).val % d +
      (d + e) * ((G.reverseIndex[rowIndex n d (v, p)]).val / d) = _
  omega

theorem expanderRow_reverse_val (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) :
    (expanderRow d H v p).reverseIndex.val =
      expanderReverseMap d e (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val := by
  simp only [expanderRow, rowIndex_val, overlayPorts_inr_val, expanderReverseMap]
  change d + (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val % e +
      (d + e) * ((ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val / e) = _
  omega

theorem oldRow_words (G : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    rowWords (oldRow G e v p) =
      [v.val, oldReverseMap d e (row G v p).reverseIndex.val] ++
        relationWords (row G v p).relation := by
  rw [rowWords, oldRow_reverse_val]
  rfl

theorem expanderRow_words (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) :
    rowWords (expanderRow d H v p) =
      [v.val, expanderReverseMap d e
        (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val] ++
        List.replicate 4096 1 := by
  rw [rowWords, expanderRow_reverse_val]
  exact congrArg (fun rs => [v.val, expanderReverseMap d e
    (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val] ++ rs)
      PreprocessingLazyWords.relationWords_true

theorem ofFn_overlayPorts {α : Type*} (f : Fin (d + e) → α) :
    List.ofFn f = List.ofFn (fun p => f (overlayPorts d e (.inl p))) ++
      List.ofFn (fun p => f (overlayPorts d e (.inr p))) := by
  rw [List.ofFn_add]
  rfl

def vertexRows (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (v : Fin n) :
    List (DartRow n (n * (d + e))) :=
  List.ofFn (oldRow G e v) ++ List.ofFn (expanderRow d H v)


theorem flatRows_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    (flatRows (overlay G H)).toList = (List.ofFn (vertexRows G H)).flatten := by
  rw [PreprocessingLazyWords.flatRows_list]
  apply congrArg List.flatten
  congr 1
  funext v
  rw [ofFn_overlayPorts]
  simp only [row_overlay_old, row_overlay_expander]
  rfl


theorem tableWords_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.tableWords (overlay G H) =
      [n, n * (d + e)] ++ (List.ofFn (vertexRows G H)).flatten.flatMap rowWords := by
  rw [PortTables.tableWords_eq, flatRows_overlay]

theorem tableBits_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.tableBits (overlay G H) = encodeWords
      ([n, n * (d + e)] ++ (List.ofFn (vertexRows G H)).flatten.flatMap rowWords) := by
  change encodeWords (PortTables.tableWords (overlay G H)) = _
  rw [tableWords_overlay]

/-- The expander's raw stream has the same exact per-vertex port order. -/
theorem rotationWords_vertices (H : ExpanderTables.Table n e) :
    ExpanderTableWords.rotationWords H =
      (List.ofFn fun v : Fin n => List.ofFn fun p : Fin e =>
        (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val).flatten := by
  have hflat : ExpanderTableWords.rotationWords H =
      List.ofFn (fun i : Fin (n * e) => (ExpanderTables.reverseIndex H i).val) := by
    apply List.ext_getElem
    · simp [ExpanderTableWords.rotationWords_length]
    · intro i hi hj
      rw [ExpanderTableWords.rotationWords_getElem H i (by simpa using hi)]
      simp only [List.getElem_ofFn]
  rw [hflat, PreprocessingLazyWords.ofFn_rowIndex]
  rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayWords

end

end OAI
