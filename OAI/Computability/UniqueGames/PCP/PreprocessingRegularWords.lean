/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.PCP.PreprocessingInternalRows
import OAI.Computability.UniqueGames.PCP.PreprocessingPaddingWords

namespace OAI

/-!
# Complete serialization of the actual regularized table

Each global vertex emits its internal ports in increasing order, then its
inherited port. Original darts are the first global vertices. Dummy vertices
follow in increasing owner and local-dummy order. These are identities for the
actual stored rows and existing codec, with arbitrary actual cloud tables.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

/-- Read one row of the actual output, in the chosen global coordinates. -/
def actualRow (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    GraphTables.DartRow (vertexCount t padding) (vertexCount t padding * (q + 1)) :=
  (PortTables.flatRows (ofCloudTables t padding tables))[
    PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)]

/-- A vertex emits every internal port, followed by its inherited port. -/
def vertexRows (x : Vertex t padding) :
    List (GraphTables.DartRow (vertexCount t padding) (vertexCount t padding * (q + 1))) :=
  List.ofFn (fun p : Fin q => actualRow t padding tables x (.inl p)) ++
    [actualRow t padding tables x (.inr ())]


def vertexBits (x : Vertex t padding) : List Bool :=
  encodeWords ((vertexRows t padding tables x).flatMap GraphTables.rowWords)

def originalVertexBits (e : Fin t.darts) : List Bool := vertexBits t padding tables (.inl e)
def dummyVertexBits (v : Fin t.vertices) (j : Fin (padding v)) : List Bool :=
  vertexBits t padding tables (.inr ⟨v, j⟩)


theorem actualRow_eq (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    actualRow t padding tables x p =
      ⟨vertexOrder t padding x,
        (ofCloudTables t padding tables).reverseIndex[
          PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)],
        (ofCloudTables t padding tables).relations[
          PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)]⟩ := by
  simp only [actualRow, PortTables.flatRows, Vector.getElem_ofFn,
    Fin.getElem_fin, Fin.eta, Equiv.symm_apply_apply]

@[simp] theorem actualRow_tail (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    (actualRow t padding tables x p).tail.val = (vertexOrder t padding x).val := by
  rw [actualRow_eq]

@[simp] theorem inherited_original_reverse (e : Fin t.darts) :
    (actualRow t padding tables (.inl e) (.inr ())).reverseIndex.val =
      (q + 1) * t.rows[e].reverseIndex.val + q := by
  rw [actualRow_eq]
  change ((ofCloudTables t padding tables).reverseIndex[PortTables.rowIndex _ _
    (vertexOrder t padding (.inl e), portOrder q (.inr ()))]).val = _
  rw [← PortTables.rowIndex_rotation, rotation_ofCloudTables]
  change (PortTables.rowIndex _ _
    (vertexOrder t padding (.inl (GraphTables.reverseAt t.rows e)), portOrder q (.inr ()))).val = _
  rw [PortTables.rowIndex_val, vertexOrder_original, portOrder_inherited]
  exact Nat.add_comm _ _

@[simp] theorem inherited_dummy_reverse (v : Fin t.vertices) (j : Fin (padding v)) :
    (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())).reverseIndex.val =
      (q + 1) * (t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val) + q := by
  rw [actualRow_eq]
  change ((ofCloudTables t padding tables).reverseIndex[PortTables.rowIndex _ _
    (vertexOrder t padding (.inr ⟨v, j⟩), portOrder q (.inr ()))]).val = _
  rw [← PortTables.rowIndex_rotation, rotation_ofCloudTables]
  change (PortTables.rowIndex _ _
    (vertexOrder t padding (.inr ⟨v, j⟩), portOrder q (.inr ()))).val = _
  rw [PortTables.rowIndex_val, PreprocessingPaddingOffsets.vertexOrder_dummy_val,
    portOrder_inherited]
  exact Nat.add_comm _ _

@[simp] theorem inherited_original_relation (e : Fin t.darts) :
    (actualRow t padding tables (.inl e) (.inr ())).relation = t.rows[e].relation := by
  rw [actualRow_eq]
  apply GraphTables.relation_ext
  intro a b
  exact accepts_original t padding tables e a b

@[simp] theorem inherited_dummy_relation (v : Fin t.vertices) (j : Fin (padding v)) :
    (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())).relation =
      MachineDummyRows.trueRelation := by
  rw [actualRow_eq]
  apply GraphTables.relation_ext
  intro a b
  have h := accepts_dummy t padding tables ⟨v, j⟩ a b
  simpa only [PortTables.accepts, MachineDummyRows.trueRelation,
    GraphTables.relationAt, Fin.getElem_fin, Vector.getElem_replicate] using h

/-- The inherited original row keeps the complete input predicate. -/
theorem inherited_original_words (e : Fin t.darts) :
    GraphTables.rowWords (actualRow t padding tables (.inl e) (.inr ())) =
      [e.val, (q + 1) * t.rows[e].reverseIndex.val + q] ++
        GraphTables.relationWords t.rows[e].relation := by
  simp only [GraphTables.rowWords, actualRow_tail, vertexOrder_original,
    inherited_original_reverse, inherited_original_relation]

/-- The inherited dummy row is an always-accepting self-loop. -/
theorem inherited_dummy_words (v : Fin t.vertices) (j : Fin (padding v)) :
    GraphTables.rowWords (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())) =
      [t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val,
        (q + 1) * (t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val) + q] ++
        GraphTables.relationWords MachineDummyRows.trueRelation := by
  simp only [GraphTables.rowWords, actualRow_tail,
    PreprocessingPaddingOffsets.vertexOrder_dummy_val,
    inherited_dummy_reverse, inherited_dummy_relation]

/-- Per-row serialization agrees with the generic table codec. -/
theorem actualRow_bits (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    encodeWords (GraphTables.rowWords (actualRow t padding tables x p)) =
      PreprocessingPaddingWords.rowBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) (portOrder q p) := by
  simpa only [actualRow, Equiv.symm_apply_apply] using
    PreprocessingPaddingWords.rowBits_flat (ofCloudTables t padding tables)
      (PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p))

/-- Each block uses exactly the port order of the actual stored table. -/
theorem vertexBits_eq (x : Vertex t padding) :
    vertexBits t padding tables x =
      PreprocessingPaddingWords.vertexBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) := by
  unfold vertexBits vertexRows
  rw [List.flatMap_append, encodeWords_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [UniqueGamesTheorem.Foundations.Complexity.encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun p : Fin q =>
    encodeWords (GraphTables.rowWords (actualRow t padding tables x (.inl p))))).flatten ++
      encodeWords (GraphTables.rowWords (actualRow t padding tables x (.inr ()))) = _
  simp_rw [actualRow_bits]
  unfold PreprocessingPaddingWords.vertexBits
  rw [List.ofFn_succ_last, List.flatten_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

/-- The explicit padding list is the inverse enumeration of its numeric order. -/
theorem paddingOrder_ofFn :
    List.ofFn (paddingOrder padding).symm = paddingList padding := by
  calc
    List.ofFn (paddingOrder padding).symm =
        List.ofFn (fun i : Fin (paddingList padding).length =>
          (paddingOrder padding).symm (Fin.cast (paddingList_length padding) i)) :=
      List.ofFn_congr (paddingList_length padding).symm (paddingOrder padding).symm
    _ = paddingList padding := by
      change List.ofFn (fun i => (paddingList padding).get i) = _
      exact List.ofFn_get _

/-- Any global-vertex payload follows old darts, then the explicit dummy list. -/
theorem vertexOrder_ofFn {α : Type*} (f : Vertex t padding → α) :
    List.ofFn (fun i : Fin (vertexCount t padding) => f ((vertexOrder t padding).symm i)) =
      List.ofFn (fun e : Fin t.darts => f (.inl e)) ++
        (paddingList padding).map (fun z => f (.inr z)) := by
  change List.ofFn (fun i : Fin (t.darts + ∑ v, padding v) =>
    f ((Equiv.sumCongr (Equiv.refl (Fin t.darts)) (paddingOrder padding)).symm
      (finSumFinEquiv.symm i))) = _
  rw [List.ofFn_add]
  have hold (e : Fin t.darts) :
      finSumFinEquiv.symm (e.castLE (Nat.le_add_right t.darts (∑ v, padding v))) =
        Sum.inl e := finSumFinEquiv.symm_apply_apply (Sum.inl e)
  simp only [hold, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Sum.map_inl, Sum.map_inr]
  rw [← paddingOrder_ofFn, List.map_ofFn]
  rfl

/-- The stored dummy list uses exactly the nested owner/local-index loop order. -/
theorem paddingList_flatMap {α : Type*} (f : (Σ v : Fin t.vertices, Fin (padding v)) → List α) :
    (paddingList padding).flatMap f =
      (List.ofFn (fun v : Fin t.vertices =>
        (List.ofFn (fun j : Fin (padding v) => f ⟨v, j⟩)).flatten)).flatten := by
  simp only [paddingList, List.sigma, List.finRange, List.flatMap_def,
    List.map_flatten, List.flatten_flatten, List.map_ofFn, Function.comp_def]

/-- The whole actual row stream, split into the two executable outer loops. -/
theorem rowsBits_ofCloudTables :
    PreprocessingPaddingWords.rowsBits (ofCloudTables t padding tables) =
      (List.ofFn (originalVertexBits t padding tables)).flatten ++
        (List.ofFn (fun v : Fin t.vertices =>
          (List.ofFn (dummyVertexBits t padding tables v)).flatten)).flatten := by
  rw [PreprocessingPaddingWords.rowsBits_eq_vertices]
  have hblocks :
      List.ofFn (fun i : Fin (vertexCount t padding) =>
        PreprocessingPaddingWords.vertexBits (ofCloudTables t padding tables) i) =
      List.ofFn (fun i : Fin (vertexCount t padding) =>
        vertexBits t padding tables ((vertexOrder t padding).symm i)) := by
    apply congrArg List.ofFn
    funext i
    rw [vertexBits_eq, Equiv.apply_symm_apply]
  rw [hblocks, vertexOrder_ofFn, List.flatten_append]
  change (List.ofFn (originalVertexBits t padding tables)).flatten ++
      ((paddingList padding).map (fun z => dummyVertexBits t padding tables z.1 z.2)).flatten = _
  rw [← List.flatMap_def, paddingList_flatMap]

/-- Exact complete codec identity: new headers, original blocks, then dummy blocks. -/
theorem tableBits_ofCloudTables :
    PortTables.tableBits (ofCloudTables t padding tables) =
      encodeWords [vertexCount t padding, vertexCount t padding * (q + 1)] ++
        (List.ofFn (originalVertexBits t padding tables)).flatten ++
        (List.ofFn (fun v : Fin t.vertices =>
          (List.ofFn (dummyVertexBits t padding tables v)).flatten)).flatten := by
  change encodeWords (PortTables.tableWords (ofCloudTables t padding tables)) = _
  rw [PortTables.tableWords_eq, encodeWords_append]
  change encodeWords [vertexCount t padding, vertexCount t padding * (q + 1)] ++
    PreprocessingPaddingWords.rowsBits (ofCloudTables t padding tables) = _
  rw [rowsBits_ofCloudTables, List.append_assoc]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords

end OAI
