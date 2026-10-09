/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Research.R22PcpPreprocessing
import OAI.Computability.UniqueGames.PCP.CloudRoundingLemmas
import OAI.Computability.UniqueGames.PCP.VertexPadding

namespace OAI

section

/-!
# Executable whole-vertex padding of regular constraint tables

The first `n` vertex rows retain their old rotation and complete relation
tables. Every additional vertex has one self-reversing, always-accepting loop
at each port. An explicit finite sum equivalence identifies these stored rows
with `VertexPadding.pad`; rejection counts are preserved for every labeling.

The construction materializes finite vectors. No machine runtime bound is
claimed here.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

/-- Old vertices occupy the initial interval and dummy vertices the final one. -/
def vertexEquiv (h : n ≤ m) : Fin n ⊕ Fin (m - n) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

@[simp] theorem vertexEquiv_inl (h : n ≤ m) (v : Fin n) :
    vertexEquiv h (Sum.inl v) = v.castLE h := rfl

@[simp] theorem vertexEquiv_inr_val (h : n ≤ m) (v : Fin (m - n)) :
    (vertexEquiv h (Sum.inr v)).val = n + v.val := rfl

@[simp] theorem vertexEquiv_symm_old (h : n ≤ m) (v : Fin n) :
    (vertexEquiv h).symm (v.castLE h) = Sum.inl v :=
  (vertexEquiv h).symm_apply_apply (Sum.inl v)

/-- The port number is retained by the coordinate conversion. -/
def dartEquiv (h : n ≤ m) :
    (Fin n ⊕ Fin (m - n)) × Fin d ≃ Fin m × Fin d :=
  Equiv.prodCongr (vertexEquiv h) (Equiv.refl _)

@[simp] theorem dartEquiv_apply (h : n ≤ m)
    (v : Fin n ⊕ Fin (m - n)) (p : Fin d) :
    dartEquiv h (v, p) = (vertexEquiv h v, p) := rfl

/-- Concrete sum-type padding, before converting to integer vertex indices. -/
def sumGraph (table : Table n d) (m : Nat) :
    ConstraintGraph (Fin n ⊕ Fin (m - n))
      ((Fin n ⊕ Fin (m - n)) × Fin d) Label :=
  VertexPadding.pad (baseGraph table) (m - n)

/-- The same graph, with the explicit initial/final-interval vertex ordering. -/
def paddedGraph (table : Table n d) (h : n ≤ m) :
    ConstraintGraph (Fin m) (Fin m × Fin d) Label :=
  (sumGraph table m).reindex (vertexEquiv h) (dartEquiv h) (Equiv.refl _)

theorem paddedGraph_reverse_equiv (table : Table n d) (h : n ≤ m)
    (e : (Fin n ⊕ Fin (m - n)) × Fin d) :
    (paddedGraph table h).reverse (dartEquiv h e) =
      dartEquiv h ((sumGraph table m).reverse e) := by
  change dartEquiv h ((sumGraph table m).reverse
    ((dartEquiv h).symm (dartEquiv h e))) = _
  rw [Equiv.symm_apply_apply]

theorem paddedGraph_accepts_equiv (table : Table n d) (h : n ≤ m)
    (e : (Fin n ⊕ Fin (m - n)) × Fin d) (a b : Label) :
    (paddedGraph table h).accepts (dartEquiv h e) a b =
      (sumGraph table m).accepts e a b := by
  change (sumGraph table m).accepts ((dartEquiv h).symm (dartEquiv h e)) a b = _
  rw [Equiv.symm_apply_apply]

/-- Executable materialization of every padded rotation and predicate row. -/
def pad (table : Table n d) (h : n ≤ m) : Table m d :=
  ofPortGraph
    { rot := (paddedGraph table h).reverse
      rot_involutive := (paddedGraph table h).reverse_involutive }
    (paddedGraph table h).accepts (paddedGraph table h).reverse_accepts

@[simp] theorem rotation_pad (table : Table n d) (h : n ≤ m) (e : Fin m × Fin d) :
    rotation (pad table h) e = (paddedGraph table h).reverse e := by
  exact rotation_ofPortGraph _ _ _ e

@[simp] theorem accepts_pad (table : Table n d) (h : n ≤ m)
    (e : Fin m × Fin d) (a b : Label) :
    PortTables.accepts (pad table h) e a b = (paddedGraph table h).accepts e a b := by
  exact accepts_ofPortGraph _ _ _ e a b


/-- Full semantic identity with the concrete padding and explicit reindexing. -/
@[simp] theorem baseGraph_pad (table : Table n d) (h : n ≤ m) :
    baseGraph (pad table h) = paddedGraph table h := by
  apply constraintGraph_ext
  · exact rotation_pad table h
  · funext e
    exact ((vertexEquiv h).apply_symm_apply e.1).symm
  · funext e a b
    exact accepts_pad table h e a b

theorem rotation_pad_equiv (table : Table n d) (h : n ≤ m)
    (v : Fin n ⊕ Fin (m - n)) (p : Fin d) :
    rotation (pad table h) (vertexEquiv h v, p) =
      (vertexEquiv h ((sumGraph table m).reverse (v, p)).1,
        ((sumGraph table m).reverse (v, p)).2) := by
  rw [rotation_pad]
  exact paddedGraph_reverse_equiv table h (v, p)

@[simp] theorem rotation_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    rotation (pad table h) (v.castLE h, p) =
      ((rotation table (v, p)).1.castLE h, (rotation table (v, p)).2) := by
  simpa only [sumGraph, VertexPadding.pad_reverse_inl, baseGraph_reverse,
    vertexEquiv_inl] using rotation_pad_equiv table h (Sum.inl v) p

@[simp] theorem rotation_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    rotation (pad table h) (vertexEquiv h (Sum.inr v), p) =
      (vertexEquiv h (Sum.inr v), p) := by
  simpa only [sumGraph, VertexPadding.pad_reverse_inr] using
    rotation_pad_equiv table h (Sum.inr v) p

@[simp] theorem accepts_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) (a b : Label) :
    PortTables.accepts (pad table h) (v.castLE h, p) a b =
      PortTables.accepts table (v, p) a b := by
  rw [accepts_pad]
  exact paddedGraph_accepts_equiv table h (Sum.inl v, p) a b

@[simp] theorem accepts_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) (a b : Label) :
    PortTables.accepts (pad table h) (vertexEquiv h (Sum.inr v), p) a b = true := by
  rw [accepts_pad]
  exact paddedGraph_accepts_equiv table h (Sum.inr v, p) a b

theorem reverseIndex_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    (pad table h).reverseIndex[rowIndex m d (v.castLE h, p)] =
      rowIndex m d ((rotation table (v, p)).1.castLE h, (rotation table (v, p)).2) := by
  rw [← rowIndex_rotation, rotation_pad_old]

theorem reverseIndex_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    (pad table h).reverseIndex[rowIndex m d (vertexEquiv h (Sum.inr v), p)] =
      rowIndex m d (vertexEquiv h (Sum.inr v), p) := by
  rw [← rowIndex_rotation, rotation_pad_new]

/-- The entire old 4096-bit relation row is retained. -/
theorem relations_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    (pad table h).relations[rowIndex m d (v.castLE h, p)] =
      table.relations[rowIndex n d (v, p)] := by
  apply GraphTables.relation_ext
  intro a b
  exact accepts_pad_old table h v p a b

/-- Every bit of every added relation row accepts. -/
theorem relations_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    (pad table h).relations[rowIndex m d (vertexEquiv h (Sum.inr v), p)] =
      Vector.replicate 4096 true := by
  apply GraphTables.relation_ext
  intro a b
  simpa only [PortTables.accepts, GraphTables.relationAt, Fin.getElem_fin,
    Vector.getElem_replicate] using
    accepts_pad_new table h v p a b

/-- Exact occurrence counts for arbitrary labels on all old and added vertices. -/
theorem pad_rejectionCount (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) :
    (baseGraph (pad table h)).rejectionCount labeling =
      (baseGraph table).rejectionCount (fun v => labeling (v.castLE h)) := by
  rw [baseGraph_pad]
  calc
    (paddedGraph table h).rejectionCount labeling =
        (sumGraph table m).rejectionCount (fun v => labeling (vertexEquiv h v)) := by
      simpa only [paddedGraph, ConstraintGraph.labelingEquiv, Equiv.arrowCongr,
        Equiv.coe_fn_mk, Function.comp_def, Equiv.refl_apply, Equiv.apply_symm_apply] using
        ConstraintGraph.reindex_rejectionCount (sumGraph table m)
          (vertexEquiv h) (dartEquiv h) (Equiv.refl _)
          (fun v => labeling (vertexEquiv h v))
    _ = (baseGraph table).rejectionCount (fun v => labeling (v.castLE h)) := by
      simpa only [sumGraph, vertexEquiv_inl] using
        VertexPadding.pad_rejectionCount (baseGraph table) rfl (m - n)
          (fun v => labeling (vertexEquiv h v))

/-- A particular padded labeling satisfies exactly when its old restriction does. -/
theorem pad_labeling_satisfies_iff (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) :
    (∀ e, (baseGraph (pad table h)).edgeSatisfied labeling e = true) ↔
      ∀ e, (baseGraph table).edgeSatisfied (fun v => labeling (v.castLE h)) e = true := by
  rw [← ConstraintGraph.rejectionCount_eq_zero_iff,
    ← ConstraintGraph.rejectionCount_eq_zero_iff, pad_rejectionCount]

/-- A computable extension uses label zero on every dummy vertex. -/
def extendLabeling (h : n ≤ m) (labeling : Fin n → Label) : Fin m → Label :=
  fun v => Sum.elim labeling (fun _ => 0) ((vertexEquiv h).symm v)

@[simp] theorem extendLabeling_old (h : n ≤ m) (labeling : Fin n → Label) (v : Fin n) :
    extendLabeling h labeling (v.castLE h) = labeling v := by
  simp only [extendLabeling, vertexEquiv_symm_old, Sum.elim_inl]

theorem pad_satisfiable_iff (table : Table n d) (h : n ≤ m) :
    (baseGraph (pad table h)).Satisfiable ↔ (baseGraph table).Satisfiable := by
  constructor
  · rintro ⟨labeling, hs⟩
    exact ⟨fun v => labeling (v.castLE h), (pad_labeling_satisfies_iff table h labeling).1 hs⟩
  · rintro ⟨labeling, hs⟩
    refine ⟨extendLabeling h labeling, (pad_labeling_satisfies_iff table h _).2 ?_⟩
    simpa only [extendLabeling_old] using hs

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables

end

end OAI
