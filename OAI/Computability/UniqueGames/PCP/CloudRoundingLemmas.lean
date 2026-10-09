/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.NormNum
import OAI.Computability.UniqueGames.PCP.AlphabetReductionLemmas
import OAI.Computability.UniqueGames.PCP.GraphTables
import OAI.Computability.UniqueGames.PCP.InitialGraphLemmas

namespace OAI

section

/-!
Actual finite counting for rounding copied dart labels. Minority color classes
are small enough for the cloud's directed-cut expansion. Their boundary darts
form disjoint fibers within the label disagreements. A separate endpoint charge
counts at most two affected original darts per changed copied label.
-/

namespace UniqueGamesTheorem.Foundations.PCP.CloudRounding

open scoped BigOperators

theorem dart_rejection_count_le
    {E V A : Type*} [Fintype E] [DecidableEq A]
    (tail : E → V) (reverse : E ≃ E) (accepts : E → A → A → Bool)
    (ell : E → A) (rounded : V → A) :
    (Finset.univ.filter (fun e =>
      accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)).card ≤
    (Finset.univ.filter (fun e => accepts e (ell e) (ell (reverse e)) = false)).card +
      2 * (Finset.univ.filter (fun e => ell e ≠ rounded (tail e))).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hrev := Equiv.sum_comp reverse
    (fun e => if ell e ≠ rounded (tail e) then (1 : Nat) else 0)
  have charge (e : E) :
      (if accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false then 1 else 0) ≤
      (if accepts e (ell e) (ell (reverse e)) = false then 1 else 0) +
        (if ell e ≠ rounded (tail e) then 1 else 0) +
        (if ell (reverse e) ≠ rounded (tail (reverse e)) then 1 else 0) := by
    by_cases hl : ell e = rounded (tail e) <;>
      by_cases hr : ell (reverse e) = rounded (tail (reverse e)) <;>
      simp [hl, hr] <;> split <;> omega
  have bound := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => charge e)
  simpa only [Finset.sum_add_distrib, hrev, two_mul, ← Nat.add_assoc] using bound

section CloudCounts

variable {X A D : Type*} [Fintype X] [Fintype A] [Fintype D]
variable [DecidableEq X] [DecidableEq A]

def colorSet (ell : X → A) (a : A) : Finset X :=
  Finset.univ.filter (fun x => ell x = a)

def minoritySet (ell : X → A) (m : A) : Finset X :=
  Finset.univ.filter (fun x => ell x ≠ m)

def directedCut (next : X × D → X) (S : Finset X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => xd.1 ∈ S ∧ next xd ∉ S)

def disagreementSet (ell : X → A) (next : X × D → X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => ell xd.1 ≠ ell (next xd))

abbrev Nonmajor (m : A) := {a : A // a ≠ m}

omit [DecidableEq X] in
theorem exists_max_color (ell : X → A) [Nonempty A] :
    ∃ m : A, ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun a : A => (colorSet ell a).card) Finset.univ_nonempty
  exact ⟨m, fun a => hm a (Finset.mem_univ a)⟩

noncomputable def majority (ell : X → A) [Nonempty A] : A :=
  Classical.choose (exists_max_color ell)

omit [DecidableEq X] in
theorem majority_maximal (ell : X → A) [Nonempty A] (a : A) :
    (colorSet ell a).card ≤ (colorSet ell (majority ell)).card :=
  Classical.choose_spec (exists_max_color ell) a

omit [Fintype A] in
/-- Every nonchosen color occupies at most half the cloud. -/
theorem nonchosen_color_twice_le (ell : X → A) (m : A)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (a : A) (ha : a ≠ m) :
    2 * (colorSet ell a).card ≤ Fintype.card X := by
  have hd : Disjoint (colorSet ell a) (colorSet ell m) :=
    Finset.disjoint_filter.mpr (fun x _ hxa hxm => ha (hxa.symm.trans hxm))
  have hu := Finset.card_le_card
    (Finset.subset_univ (colorSet ell a ∪ colorSet ell m))
  rw [Finset.card_union_of_disjoint hd, Finset.card_univ] at hu
  have hm := maximal a
  omega

omit [DecidableEq X] in
theorem minority_card_eq_sum (ell : X → A) (m : A) :
    (minoritySet ell m).card = ∑ a : Nonmajor m, (colorSet ell a.val).card := by
  rw [← Finset.sum_subtype (Finset.univ.filter (· ≠ m)) (by simp)
    (fun a => (colorSet ell a).card)]
  simpa [colorSet, minoritySet] using
    (Finset.sum_card_fiberwise_eq_card_filter Finset.univ
      (Finset.univ.filter (· ≠ m)) ell).symm

/-- The cuts are disjoint fibers of the tail label on disagreement darts. -/
theorem minority_cut_sum_le (ell : X → A) (next : X × D → X) (m : A) :
    (∑ a : Nonmajor m, (directedCut next (colorSet ell a.val)).card) ≤
      (disagreementSet ell next).card := by
  classical
  have fiber (a : A) : directedCut next (colorSet ell a) =
      (disagreementSet ell next).filter (fun xd => ell xd.1 = a) := by
    ext xd
    simp only [directedCut, colorSet, disagreementSet, Finset.mem_filter,
      Finset.mem_univ, true_and]
    aesop
  simp_rw [fiber]
  rw [← Finset.sum_subtype (Finset.univ.filter (· ≠ m)) (by simp)
    (fun a => ((disagreementSet ell next).filter (fun xd => ell xd.1 = a)).card),
    Finset.sum_card_fiberwise_eq_card_filter]
  exact Finset.card_filter_le _ _

/-- Sum genuine directed-cut expansion over the nonchosen color classes. -/
theorem minority_expansion_bound (ell : X → A) (next : X × D → X) (m : A)
    (h : ℚ)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (expansion : ∀ S : Finset X, S.card ≤ Fintype.card X / 2 →
      h * (S.card : ℚ) ≤ ((directedCut next S).card : ℚ)) :
    h * ((minoritySet ell m).card : ℚ) ≤ ((disagreementSet ell next).card : ℚ) := by
  have each (a : Nonmajor m) :
      h * ((colorSet ell a.val).card : ℚ) ≤
        ((directedCut next (colorSet ell a.val)).card : ℚ) := by
    apply expansion
    have ha := nonchosen_color_twice_le ell m maximal a.val a.property
    omega
  calc
    h * ((minoritySet ell m).card : ℚ) =
        ∑ a : Nonmajor m, h * ((colorSet ell a.val).card : ℚ) := by
      rw [minority_card_eq_sum, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ a : Nonmajor m, ((directedCut next (colorSet ell a.val)).card : ℚ) :=
      Finset.sum_le_sum (fun a _ => each a)
    _ ≤ ((disagreementSet ell next).card : ℚ) := by
      exact_mod_cast minority_cut_sum_le ell next m

end CloudCounts

section GraphRounding

open DegreeReplacement PoweringWalks

variable {V E A D : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype D]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

def mismatchSet (G : ConstraintGraph V E A) (ell : E → A) (rounded : V → A) :
    Finset E :=
  Finset.univ.filter (fun e => ell e ≠ rounded (G.tail e))

def copiedRejectionCount (G : ConstraintGraph V E A) (ell : E → A) : Nat :=
  (Finset.univ.filter (fun e => G.accepts e (ell e) (ell (G.reverse e)) = false)).card

def innerDisagreementSet (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) : Finset (E × D) :=
  Finset.univ.filter (fun ed => ell ed.1 ≠ ell (innerRotation G H ed).1)

noncomputable def roundLabels [Nonempty A]
    (G : ConstraintGraph V E A) (ell : E → A) : V → A :=
  fun v => majority (fun e : Cloud G v => ell e.val)

omit [Fintype A] [DecidableEq E] in
/-- Every changed dart belongs to precisely one tail fiber. -/
theorem mismatch_card_eq_sum (G : ConstraintGraph V E A) (ell : E → A)
    (rounded : V → A) :
    (mismatchSet G ell rounded).card =
      ∑ v, (minoritySet (fun e : Cloud G v => ell e.val) (rounded v)).card := by
  classical
  simp only [mismatchSet, minoritySet, Finset.card_eq_sum_ones,
    Finset.sum_filter, ← Fintype.sum_sigma']
  exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv G.tail).symm _ _ (fun _ => rfl)

omit [Fintype A] [DecidableEq E] in
/-- Reindex the sum by the existing cloud coordinates, rather than recounting darts. -/
theorem disagreement_card_eq_sum (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (innerDisagreementSet G H ell).card =
      ∑ v, (disagreementSet (fun e : Cloud G v => ell e.val)
        (fun ed => ((H v).rot ed).1)).card := by
  classical
  simp only [innerDisagreementSet, disagreementSet, Finset.card_eq_sum_ones,
    Finset.sum_filter, ← Fintype.sum_sigma']
  exact Fintype.sum_equiv (cloudIndexEquiv G) _ _ (fun _ => rfl)

/-- No uniform cloud-size hypothesis occurs in this finite sum. -/
theorem rounded_mismatch_expansion [Nonempty A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (ell : E → A) (h : ℚ)
    (expansion : ∀ v (S : Finset (Cloud G v)),
      S.card ≤ Fintype.card (Cloud G v) / 2 →
      h * (S.card : ℚ) ≤ ((directedCut (fun ed => ((H v).rot ed).1) S).card : ℚ)) :
    h * ((mismatchSet G ell (roundLabels G ell)).card : ℚ) ≤
      ((innerDisagreementSet G H ell).card : ℚ) := by
  rw [mismatch_card_eq_sum, disagreement_card_eq_sum, Nat.cast_sum, Nat.cast_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  exact minority_expansion_bound (fun e : Cloud G v => ell e.val)
    (fun ed => ((H v).rot ed).1) (roundLabels G ell v) h
    (majority_maximal (fun e : Cloud G v => ell e.val)) (expansion v)

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq E] in
theorem rounded_endpoint_bound (G : ConstraintGraph V E A)
    (ell : E → A) (rounded : V → A) :
    G.rejectionCount rounded ≤ copiedRejectionCount G ell +
      2 * (mismatchSet G ell rounded).card :=
  dart_rejection_count_le G.tail G.reverse G.accepts ell rounded

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inl (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inl d) =
      decide (ell e = ell (innerRotation G H (e, d)).1) := rfl

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inr (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inr u) =
      G.accepts e (ell e) (ell (G.reverse e)) := rfl

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq E] in
/-- Exact rejection count for arbitrary copied labels, including cloud violations. -/
theorem replacement_rejection_split (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (replacementGraph G H).rejectionCount ell =
      copiedRejectionCount G ell + (innerDisagreementSet G H ell).card := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type,
    copied_satisfied_inl, copied_satisfied_inr, decide_eq_false_iff_not,
    Fintype.sum_unique, Finset.sum_add_distrib]
  simp only [copiedRejectionCount, innerDisagreementSet, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]
  exact Nat.add_comm _ _

/-- Directed expansion by two pays for both changed endpoints exactly. -/
theorem replacement_soundness [Nonempty A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (expansion : ∀ v (S : Finset (Cloud G v)),
      S.card ≤ Fintype.card (Cloud G v) / 2 →
      2 * S.card ≤ (directedCut (fun ed => ((H v).rot ed).1) S).card)
    (ell : E → A) :
    G.rejectionCount (roundLabels G ell) ≤ (replacementGraph G H).rejectionCount ell := by
  have hc := rounded_mismatch_expansion G H ell 2 (by
    intro v S hS
    exact_mod_cast expansion v S hS)
  have hcNat : 2 * (mismatchSet G ell (roundLabels G ell)).card ≤
      (innerDisagreementSet G H ell).card := by exact_mod_cast hc
  rw [replacement_rejection_split]
  exact (rounded_endpoint_bound G ell (roundLabels G ell)).trans
    (Nat.add_le_add_left hcNat _)

/-- Padding changes the normalization, but never the rounded absolute rejection count. -/
theorem padded_replacement_soundness [Nonempty A]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    [∀ v, DecidableEq (dummy v)]
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D)
    (expansion : ∀ v (S : Finset (Cloud (paddedGraph G dummy) v)),
      S.card ≤ Fintype.card (Cloud (paddedGraph G dummy) v) / 2 →
      2 * S.card ≤ (directedCut (fun ed => ((H v).rot ed).1) S).card)
    (ell : PaddedDart G dummy → A) :
    G.rejectionCount (roundLabels (paddedGraph G dummy) ell) ≤
      (paddedReplacementGraph G dummy H).rejectionCount ell := by
  simpa only [paddedReplacementGraph, padded_rejectionCount] using
    replacement_soundness (paddedGraph G dummy) H expansion ell

end GraphRounding


end UniqueGamesTheorem.Foundations.PCP.CloudRounding

end

section

/-!
# Executable regular constraint tables on the fixed 64-label alphabet

Every pair `(vertex,port)` has one stored reverse index and one complete
4096-bit relation. Flat row `port + ports * vertex` has its tail implicitly
fixed by that pair. Rotation uses the stored vector lookup, followed by the
inverse row-index bijection. Loops and repeated directed occurrences remain
distinct rows.

Serialization uses the existing `GraphTables` codec: header `[vertices,darts]`
with `darts=vertices*ports`, then tail/reverse/4096 bit words per row.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PortTables

open PoweringWalks

abbrev Label := GraphTables.Label

def rowIndex (vertices ports : Nat) :
    Fin vertices × Fin ports ≃ Fin (vertices * ports) := finProdFinEquiv

@[simp] theorem rowIndex_val (n d : Nat) (e : Fin n × Fin d) :
    (rowIndex n d e).val = e.2.val + d * e.1.val := rfl

/-- Finite executable input data, with the two graph laws certified on lookup. -/
structure Table (vertices ports : Nat) where
  reverseIndex : Vector (Fin (vertices * ports)) (vertices * ports)
  relations : Vector GraphTables.RelationTable (vertices * ports)
  involutive : Function.Involutive
    (fun i : Fin (vertices * ports) => reverseIndex[i])
  transpose : ∀ (i : Fin (vertices * ports)) (a b : Label),
    GraphTables.relationAt relations[reverseIndex[i]] b a =
      GraphTables.relationAt relations[i] a b

variable {n d : Nat}

/-- One reverse-index lookup and the fixed mixed-radix decoding. -/
def rotation (table : Table n d) (e : Fin n × Fin d) : Fin n × Fin d :=
  (rowIndex n d).symm table.reverseIndex[rowIndex n d e]

/-- Lookup of the full stored binary predicate. -/
def accepts (table : Table n d) (e : Fin n × Fin d) (a b : Label) : Bool :=
  GraphTables.relationAt table.relations[rowIndex n d e] a b

@[simp] theorem rowIndex_rotation (table : Table n d) (e : Fin n × Fin d) :
    rowIndex n d (rotation table e) = table.reverseIndex[rowIndex n d e] := by
  exact (rowIndex n d).apply_symm_apply _

theorem rotation_involutive (table : Table n d) : Function.Involutive (rotation table) := by
  intro e
  simp only [rotation, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex n d).symm (table.involutive (rowIndex n d e))).trans
    ((rowIndex n d).symm_apply_apply e)

theorem accepts_rotation (table : Table n d) (e : Fin n × Fin d) (a b : Label) :
    accepts table (rotation table e) b a = accepts table e a b := by
  simpa only [accepts, rowIndex_rotation] using table.transpose (rowIndex n d e) a b

/-- The actual reversible regular port graph represented by the vectors. -/
def portGraph (table : Table n d) : PortGraph (Fin n) (Fin d) where
  rot :=
    { toFun := rotation table
      invFun := rotation table
      left_inv := rotation_involutive table
      right_inv := rotation_involutive table }
  rot_involutive := rotation_involutive table

@[simp] theorem portGraph_rot (table : Table n d) (e : Fin n × Fin d) :
    (portGraph table).rot e = rotation table e := rfl

/-- Constraint-graph semantics, with each vertex-port pair a distinct dart. -/
def baseGraph (table : Table n d) : ConstraintGraph (Fin n) (Fin n × Fin d) Label where
  reverse := (portGraph table).rot
  reverse_involutive := rotation_involutive table
  tail := Prod.fst
  accepts := accepts table
  reverse_accepts := accepts_rotation table

@[simp] theorem baseGraph_reverse (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).reverse e = rotation table e := rfl

@[simp] theorem baseGraph_tail (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).tail e = e.1 := rfl

@[simp] theorem baseGraph_head (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).head e = (rotation table e).1 := rfl

@[simp] theorem baseGraph_accepts (table : Table n d) (e : Fin n × Fin d) (a b : Label) :
    (baseGraph table).accepts e a b = accepts table e a b := rfl

/-- Materialize a reversible port graph and its predicates into the fixed rows. -/
def ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b) : Table n d where
  reverseIndex := Vector.ofFn (fun i => rowIndex n d (G.rot ((rowIndex n d).symm i)))
  relations := Vector.ofFn (fun i => GraphTables.relationOf (predicate ((rowIndex n d).symm i)))
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
      Equiv.symm_apply_apply]
    exact (congrArg (rowIndex n d) (G.rot_involutive ((rowIndex n d).symm i))).trans
      ((rowIndex n d).apply_symm_apply i)
  transpose := by
    intro i a b
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
      Equiv.symm_apply_apply, GraphTables.relationAt_relationOf]
    exact htranspose ((rowIndex n d).symm i) a b

@[simp] theorem rotation_ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b)
    (e : Fin n × Fin d) : rotation (ofPortGraph G predicate htranspose) e = G.rot e := by
  simp only [rotation, ofPortGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply]

@[simp] theorem accepts_ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b)
    (e : Fin n × Fin d) (a b : Label) :
    accepts (ofPortGraph G predicate htranspose) e a b = predicate e a b := by
  simp only [accepts, ofPortGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply, GraphTables.relationAt_relationOf]

def flatRows (table : Table n d) : GraphTables.Rows n (n * d) :=
  Vector.ofFn (fun i =>
    ⟨((rowIndex n d).symm i).1, table.reverseIndex[i], table.relations[i]⟩)

@[simp] theorem reverseAt_flatRows (table : Table n d) (i : Fin (n * d)) :
    GraphTables.reverseAt (flatRows table) i = table.reverseIndex[i] := by
  simp [GraphTables.reverseAt, flatRows]

@[simp] theorem acceptsAt_flatRows (table : Table n d) (i : Fin (n * d)) (a b : Label) :
    GraphTables.acceptsAt (flatRows table) i a b = GraphTables.relationAt table.relations[i] a b := by
  simp [GraphTables.acceptsAt, flatRows]

theorem flatRows_valid (table : Table n d) : GraphTables.Valid (flatRows table) := by
  constructor
  · intro i
    simpa only [reverseAt_flatRows] using table.involutive i
  · intro i a b
    simpa only [reverseAt_flatRows, acceptsAt_flatRows] using table.transpose i a b

def graphTable (table : Table n d) : GraphTables.Table :=
  ⟨n, n * d, flatRows table, flatRows_valid table⟩

/-- Existing graph codec, with header `[n,n*d]` and 4098 words in every row. -/
def tableWords (table : Table n d) : List Nat := GraphTables.tableWords (graphTable table)

def tableBits (table : Table n d) : List Bool := GraphTables.tableBits (graphTable table)

/-- Variable vertex count, with the port count fixed by the input family. -/
abbrev Input (ports : Nat) := (vertices : Nat) × Table vertices ports

def inputBits {ports : Nat} (input : Input ports) : List Bool := tableBits input.2

theorem tableWords_eq (table : Table n d) :
    tableWords table = [n, n * d] ++ (flatRows table).toList.flatMap GraphTables.rowWords := rfl


theorem vertices_le_tableBits_length (table : Table n d) : n ≤ (tableBits table).length :=
  GraphTables.vertices_le_tableBits_length (graphTable table)

end UniqueGamesTheorem.Foundations.PCP.PortTables

end

end OAI
