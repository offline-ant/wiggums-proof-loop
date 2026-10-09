/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.PCP.PoweringLabelsLemmas
import OAI.Computability.UniqueGames.PCP.PoweringOpinionsLemmas

namespace OAI

section

/-!
# Bounded first-address tables for actual powering constraints

For a graph with numbered vertices and ports, each stored local-opinion index
is the first address in `allAddresses` that reaches the requested vertex.
The search traverses bounded port words, never the ambient vertex set.

The walk table stores one base dart and two address indices per traversed
edge. Looking up the endpoint labels at those indices gives exactly the
existing `finitePortSelector` decoders, including when addresses collide.
The resulting finite table predicate equals the actual powering predicate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open scoped BigOperators

variable {X A : Type*}

/-- The standard first-match search, with its index certified in bounds. -/
def firstIndex (p : X → Prop) [DecidablePred p]
    (xs : List X) (h : ∃ a ∈ xs, p a) : Fin xs.length :=
  ⟨xs.findIdx (fun a => decide (p a)), List.findIdx_lt_length_of_exists (by simpa using h)⟩

/-- The stored index selects the very same first address as `scanWitness`,
not just an address with the same endpoint. -/
theorem get_firstIndex (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a),
      xs.get (firstIndex p xs h) = (scanWitness p xs h).val := fun _ _ => rfl

/-- A local label slot is an index into the explicit bounded address list. -/
abbrev AddressIndex (d t : Nat) := Fin (allAddresses d t).length

variable {vertices d : Nat}

def addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) : AddressIndex d t :=
  firstIndex (fun w => (wordToBall G t center w).val = u.val)
    (allAddresses d t) (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t center u
      exact ⟨w, mem_allAddresses d t w, congrArg Subtype.val hw⟩)

theorem addressIndex_get (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    (allAddresses d t).get (addressIndex G t center u) =
      (finitePortSelector G t center).address u := rfl


abbrev LabelTable (d t : Nat) (A : Type*) := Vector A (allAddresses d t).length

/-- Materialize a padded label in the common address order. -/
def labelTable {t : Nat} (a : PaddedLabel (Fin d) t A) : LabelTable d t A :=
  Vector.ofFn fun i => a ((allAddresses d t).get i)

@[simp] theorem labelTable_get {t : Nat} (a : PaddedLabel (Fin d) t A)
    (i : AddressIndex d t) :
    (labelTable a)[i] = a ((allAddresses d t).get i) := by
  simp [labelTable]

/-- Exact evaluation bridge for every local target, with no consistency
assumption on labels at distinct addresses that reach the same vertex. -/
theorem labelTable_addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) (a : PaddedLabel (Fin d) t A) :
    (labelTable a)[addressIndex G t center u] =
      decode (finitePortSelector G t center) a u := by
  rw [labelTable_get, addressIndex_get]
  rfl

/-- One finite row for each constraint checked along a recorded walk. -/
structure WalkOpinionRow (vertices d t : Nat) where
  edge : Edge (Fin vertices) (Fin d)
  tailIndex : AddressIndex d t
  headIndex : AddressIndex d t

abbrev WalkRows (vertices d n : Nat) := Vector (WalkOpinionRow vertices d (n + 1)) (n + 1)

/-- The only target vertices inspected are the actual edge endpoints. -/
def walkRows (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) : WalkRows vertices d n :=
  Vector.ofFn fun k =>
    { edge := edgeAt G n w k
      tailIndex := addressIndex G (n + 1) w.1 (tailFromStart G n w k)
      headIndex := addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) }

@[simp] theorem walkRows_edge (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    (walkRows G n w)[k].edge = edgeAt G n w k := by
  simp [walkRows]

@[simp] theorem walkRows_tail_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable a)[(walkRows G n w)[k].tailIndex] =
      decode (finitePortSelector G (n + 1) w.1) a (tailFromStart G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) w.1 (tailFromStart G n w k) a

@[simp] theorem walkRows_head_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (b : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable b)[(walkRows G n w)[k].headIndex] =
      decode (finitePortSelector G (n + 1) (endpoint G w)) b (headFromEnd G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) b


/-- Evaluate an already stored row vector by finite label lookups. The only
quantified type is the bounded set of walk positions. -/
def rowsAccepts {n : Nat} (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool)
    (rows : WalkRows vertices d n) (a b : LabelTable d (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1), accepts rows[k].edge a[rows[k].tailIndex]
    b[rows[k].headIndex] = true)

/-- The stored finite lookup predicate implements the actual powering test. -/
theorem rowsAccepts_walkRows (G : PortGraph (Fin vertices) (Fin d))
    (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (a b : PaddedLabel (Fin d) (n + 1) A) :
    rowsAccepts accepts (walkRows G n w) (labelTable a) (labelTable b) =
      PoweringTest.pathAccepts G accepts n (finitePortSelector G (n + 1)) w a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowsAccepts, decide_eq_true_iff, PoweringTest.pathAccepts_eq_true_iff,
    walkRows_edge, walkRows_tail_value, walkRows_head_value]

end UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables

end

end OAI
