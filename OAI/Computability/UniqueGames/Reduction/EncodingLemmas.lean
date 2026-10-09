/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Computability.UniqueGames.Foundations.PinskerLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Reduction.ActualCanonicalLemmas
import OAI.Computability.UniqueGames.Reduction.BinaryLinear

namespace OAI

section

/-! Computable binary alphabet indexing and full translation permutation tables.
The labels are actual `Fin (2^s)` entries in the target instance format.
-/

namespace UniqueGamesTheorem.Reduction.Encoding

open Integration.BinaryLinear
open Foundations.Target

/-- Number the left side first and the right side second. -/
def sideEquiv (n : Nat) : Bool × Fin n ≃ Fin (2*n) :=
  (finTwoEquiv.symm.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv


/-- The integer label is the packed, least-significant-bit-first coordinate word. -/
def alphabetEquiv (s : Nat) : Integration.BinaryLinear.Vector s ≃ Fin (2^s) :=
  (coordinatesEquiv s).symm.trans
    { toFun := BitVec.toFin
      invFun := BitVec.ofFin
      left_inv := BitVec.ofFin_toFin
      right_inv := BitVec.toFin_ofFin }

@[simp] theorem alphabetEquiv_symm_apply_apply (s : Nat)
    (c : Integration.BinaryLinear.Vector s) :
    (alphabetEquiv s).symm (alphabetEquiv s c) = c :=
  (alphabetEquiv s).symm_apply_apply c

@[simp] theorem alphabetEquiv_apply_symm_apply (s : Nat) (c : Fin (2^s)) :
    alphabetEquiv s ((alphabetEquiv s).symm c) = c :=
  (alphabetEquiv s).apply_symm_apply c

def translate {s : Nat} (a b : Integration.BinaryLinear.Vector s)
    (c : Fin (2^s)) : Fin (2^s) :=
  alphabetEquiv s ((alphabetEquiv s).symm c + a + b)

theorem translate_involutive {s : Nat} (a b : Integration.BinaryLinear.Vector s) :
    Function.Involutive (translate a b) := by
  intro c
  simpa only [translate, alphabetEquiv_symm_apply_apply, add_assoc, zero_add,
    add_zero, alphabetEquiv_apply_symm_apply] using congrArg (alphabetEquiv s)
      (ActualCanonical.add_both ((alphabetEquiv s).symm c) 0 (a + b))

/-- Both forward and inverse tables are explicitly generated from every alphabet
index. Characteristic two makes these two tables equal. -/
def translationTable {s : Nat} (a b : Integration.BinaryLinear.Vector s) :
    PermutationTable (2^s) where
  images := _root_.Vector.ofFn (translate a b)
  inverseImages := _root_.Vector.ofFn (translate a b)
  leftInverse c := by simpa using translate_involutive a b c
  rightInverse c := by simpa using translate_involutive a b c

@[simp] theorem translationTable_images {s : Nat}
    (a b c : Integration.BinaryLinear.Vector s) :
    (translationTable a b).images[alphabetEquiv s c] = alphabetEquiv s (c + a + b) := by
  simp [translationTable, translate]


theorem translationTable_satisfied_iff {s : Nat}
    (a b cLeft cRight : Integration.BinaryLinear.Vector s) :
    (translationTable a b).images[alphabetEquiv s cLeft] = alphabetEquiv s cRight ↔
      cLeft + a + b = cRight := by
  rw [translationTable_images]
  exact (alphabetEquiv s).injective.eq_iff

section ImageNumbering

variable {Q V : Type*} [DecidableEq V]

/-- Canonical vertex bodies are compared using their actual decidable equality.
`List.dedup` fixes a deterministic order by retaining the last occurrence. -/
def imageVertices (queries : List Q) (body : Q → V) : List V :=
  (queries.map body).dedup

theorem mem_imageVertices {queries : List Q} {body : Q → V} {v : V} :
    v ∈ imageVertices queries body ↔ ∃ q ∈ queries, body q = v := by
  simp [imageVertices]

theorem imageVertices_nodup (queries : List Q) (body : Q → V) :
    (imageVertices queries body).Nodup := List.nodup_dedup _


abbrev ImageVertex (queries : List Q) (body : Q → V) :=
  {v : V // v ∈ imageVertices queries body}

/-- A computable numbering using `idxOf`; its inverse looks up that index.
It involves no chosen `Fintype.equivFin`. -/
def imageEquiv (queries : List Q) (body : Q → V) :
    ImageVertex queries body ≃ Fin (imageVertices queries body).length :=
  (List.Nodup.getEquiv _ (imageVertices_nodup queries body)).symm


theorem imageVertices_range (queries : List Q) (body : Q → V)
    (full : ∀ q, q ∈ queries) (v : V) :
    v ∈ imageVertices queries body ↔ v ∈ Set.range body := by
  simp [mem_imageVertices, full, Set.mem_range]

end ImageNumbering

end UniqueGamesTheorem.Reduction.Encoding

end

section

/-! The finite set of realizable orbit records.  Vertices are the image of the
actual canonical-data map, so equal retained data from different questions
become one vertex.  The two sides remain distinct. -/

namespace UniqueGamesTheorem.Reduction.ActualOrbit

open UniqueGamesTheorem.Integration.BinaryLinear

universe u v

variable {Q : Type u} {T : Type v} {s d : Nat}

abbrev Ambient (s d : Nat) := Vector s × Vector d

def body (can : Q → Ambient s d × T) (q : Q) : Vector d × T :=
  ((can q).1.2, (can q).2)

def offset (can : Q → Ambient s d × T) (q : Q) : Vector s := (can q).1.1

/-- Only realized bodies are vertices; no extra formal records are added. -/
def Vertex (can : Q → Ambient s d × T) := {o : Vector d × T // ∃ q, body can q = o}

def vertex (can : Q → Ambient s d × T) (q : Q) : Vertex can :=
  ⟨body can q, q, rfl⟩

theorem vertex_surjective (can : Q → Ambient s d × T) :
    Function.Surjective (vertex can) := by
  rintro ⟨o, q, hq⟩
  exact ⟨q, Subtype.ext hq⟩

noncomputable instance vertexFintype [Fintype Q] (can : Q → Ambient s d × T) :
    Fintype (Vertex can) := by
  classical
  exact Fintype.ofSurjective (vertex can) (vertex_surjective can)

instance vertexNonempty [Nonempty Q] (can : Q → Ambient s d × T) :
    Nonempty (Vertex can) := Nonempty.map (vertex can) inferInstance

theorem vertex_eq_iff (can : Q → Ambient s d × T) (q r : Q) :
    vertex can q = vertex can r ↔ body can q = body can r := by
  constructor
  · exact congrArg Subtype.val
  · intro h
    exact Subtype.ext h

/-- `false` is the left copy and `true` is the right copy. -/
abbrev TwoSidedVertex (can : Q → Ambient s d × T) := Bool × Vertex can

noncomputable def vertexEquiv [Fintype Q] (can : Q → Ambient s d × T) :
    TwoSidedVertex can ≃ Fin (Fintype.card (TwoSidedVertex can)) :=
  Fintype.equivFin _

/-- Executable vertex numbering from an exhaustive list, preserving the same
realizable-body subtype used in the semantic statements. -/
def explicitVertexEquiv [DecidableEq (Vector d × T)]
    (can : Q → Ambient s d × T) (queries : List Q) (full : ∀ q, q ∈ queries) :
    Vertex can ≃ Fin (Encoding.imageVertices queries (body can)).length :=
  let e : Vertex can ≃ Encoding.ImageVertex queries (body can) :=
    { toFun v := ⟨v.val, (Encoding.imageVertices_range queries (body can) full v.val).mpr
        v.property⟩
      invFun v := ⟨v.val, (Encoding.imageVertices_range queries (body can) full v.val).mp
        v.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  e.trans (Encoding.imageEquiv queries (body can))

def unfold (can : Q → Ambient s d × T) (label : Vertex can → Vector s) (q : Q) :
    Vector s := label (vertex can q) + offset can q

/-- The precise orientation used by the generated edge. -/
theorem constraint_iff_unfolded (can : Q → Ambient s d × T)
    (labelL labelR : Vertex can → Vector s) (q r : Q) :
    (labelL (vertex can q) + offset can q) + offset can r = labelR (vertex can r) ↔
      unfold can labelL q = unfold can labelR r := by
  rw [← eq_sub_iff_add_eq, sub_eq_add_neg,
    neg_eq_iff_add_eq_zero.mpr (ActualCanonical.add_self _)]
  rfl


end UniqueGamesTheorem.Reduction.ActualOrbit

end

section

/-! Internal serialization of canonical orbit bodies. Each record occupies nine
natural-number words, so record boundaries are independent of the tag. The
outer complement coordinate occupies one leading word. These are injectivity,
deduplication, and output-size statements, not machine running-time claims. -/

namespace UniqueGamesTheorem.Reduction.CanonicalEncoding

open Integration.BinaryLinear
open Foundations.Complexity

abbrev Ambient (s d : Nat) := Integration.BinaryLinear.Vector s × Integration.BinaryLinear.Vector d
abbrev Record (n m s d : Nat) := ActualCanonical.Record (Fin n) (Fin m) (Ambient s d)
abbrev Body (n m k s d : Nat) := Integration.BinaryLinear.Vector d × (Fin k → Record n m s d)

def vectorWord {s : Nat} (v : Integration.BinaryLinear.Vector s) : Nat :=
  (Encoding.alphabetEquiv s v).val

theorem vectorWord_lt {s : Nat} (v : Integration.BinaryLinear.Vector s) :
    vectorWord v < 2^s := (Encoding.alphabetEquiv s v).isLt

theorem vectorWord_injective {s : Nat} :
    Function.Injective (vectorWord (s := s)) := by
  intro x y h
  apply (Encoding.alphabetEquiv s).injective
  exact Fin.ext h

@[simp] theorem vectorWord_eq_iff {s : Nat} (x y : Integration.BinaryLinear.Vector s) :
    vectorWord x = vectorWord y ↔ x = y := vectorWord_injective.eq_iff

/-- Words: tag, name, occurrence, followed by three split coefficient pairs.
Padding is zero. A single record uses only the first coefficient pair. -/
def recordWords {n m s d : Nat} : Record n m s d → List Nat
  | .blank => [0, 0, 0, 0, 0, 0, 0, 0, 0]
  | .single name coefficient =>
      [1, name.val, 0, vectorWord coefficient.1, vectorWord coefficient.2, 0, 0, 0, 0]
  | .full occurrence coefficients =>
      [2, 0, occurrence.val,
        vectorWord (coefficients 0).1, vectorWord (coefficients 0).2,
        vectorWord (coefficients 1).1, vectorWord (coefficients 1).2,
        vectorWord (coefficients 2).1, vectorWord (coefficients 2).2]

@[simp] theorem recordWords_length {n m s d : Nat} (r : Record n m s d) :
    (recordWords r).length = 9 := by
  cases r <;> rfl

theorem recordWords_injective {n m s d : Nat} :
    Function.Injective (recordWords (n := n) (m := m) (s := s) (d := d)) := by
  intro r t h
  cases r <;> cases t <;>
    simp_all [recordWords, Fin.ext_iff, Prod.ext_iff, funext_iff, Fin.forall_fin_succ]

def recordsWords {n m s d : Nat} (rs : List (Record n m s d)) : List Nat :=
  rs.flatMap recordWords

@[simp] theorem recordsWords_nil {n m s d : Nat} :
    recordsWords ([] : List (Record n m s d)) = [] := rfl

@[simp] theorem recordsWords_cons {n m s d : Nat} (r : Record n m s d)
    (rs : List (Record n m s d)) :
    recordsWords (r :: rs) = recordWords r ++ recordsWords rs := rfl

@[simp] theorem recordsWords_length {n m s d : Nat} (rs : List (Record n m s d)) :
    (recordsWords rs).length = 9 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem recordsWords_injective {n m s d : Nat} :
    Function.Injective (recordsWords (n := n) (m := m) (s := s) (d := d)) := by
  intro rs ts h
  induction rs generalizing ts with
  | nil =>
    have := congrArg List.length h
    simpa using this
  | cons r rs ih =>
    cases ts with
    | nil =>
      have := congrArg List.length h
      simp at this
    | cons t ts =>
      obtain ⟨hh, ht⟩ := List.append_inj h (by simp :
        (recordWords r).length = (recordWords t).length)
      exact congrArg₂ List.cons (recordWords_injective hh) (ih ht)

def bodyWords {n m k s d : Nat} (body : Body n m k s d) : List Nat :=
  vectorWord body.1 :: recordsWords (List.ofFn body.2)

@[simp] theorem bodyWords_length {n m k s d : Nat} (body : Body n m k s d) :
    (bodyWords body).length = 1 + 9*k := by
  simp [bodyWords, Nat.add_comm]

theorem bodyWords_injective {n m k s d : Nat} :
    Function.Injective (bodyWords (n := n) (m := m) (k := k) (s := s) (d := d)) := by
  intro x y h
  have hh := List.cons.inj h
  apply Prod.ext
  · exact vectorWord_injective hh.1
  · exact List.ofFn_injective (recordsWords_injective hh.2)


def wordBound (n m s d : Nat) : Nat := n + m + 2^s + 2^d + 3

theorem recordWords_bounded {n m s d : Nat} (r : Record n m s d)
    (w : Nat) (hw : w ∈ recordWords r) : w ≤ wordBound n m s d := by
  unfold wordBound
  cases r with
  | blank =>
    simp [recordWords] at hw
    subst w
    exact Nat.zero_le _
  | single name coefficient =>
    have hn := name.isLt
    have hc := vectorWord_lt coefficient.1
    have hd := vectorWord_lt coefficient.2
    simp only [recordWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h <;> omega
  | full occurrence coefficients =>
    have hi := occurrence.isLt
    have h0c := vectorWord_lt (coefficients 0).1
    have h0d := vectorWord_lt (coefficients 0).2
    have h1c := vectorWord_lt (coefficients 1).1
    have h1d := vectorWord_lt (coefficients 1).2
    have h2c := vectorWord_lt (coefficients 2).1
    have h2d := vectorWord_lt (coefficients 2).2
    simp only [recordWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h <;> omega

theorem bodyWords_bounded {n m k s d : Nat} (body : Body n m k s d)
    (w : Nat) (hw : w ∈ bodyWords body) : w ≤ wordBound n m s d := by
  rcases List.mem_cons.mp hw with h | h
  · subst w
    have hv := vectorWord_lt body.1
    have hs : 0 < (2 : Nat)^s := pow_pos (by decide) _
    unfold wordBound
    omega
  · obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp h
    exact recordWords_bounded r w hr


end UniqueGamesTheorem.Reduction.CanonicalEncoding

end

section

/-! Direct canonical-body addresses. The fixed list of canonical words is
interpreted in big-endian order, matching forward Horner steps `B*acc+digit`.
Unused addresses represent isolated vertices. These are semantic encoding and
polynomial-size results, not an assumed machine implementation. -/

namespace UniqueGamesTheorem.Reduction.CanonicalAddress

open CanonicalEncoding

/-- Most-significant-word first, with leading zero words retained in the
fixed-length domain. Mathlib's `ofDigits` uses the opposite list order. -/
def radix (B : Nat) (words : List Nat) : Nat := Nat.ofDigits B words.reverse

theorem radix_eq_foldl (B : Nat) (words : List Nat) :
    radix B words = words.foldl (fun acc digit => B * acc + digit) 0 := by
  unfold radix
  rw [Nat.ofDigits_eq_foldr, List.foldr_reverse]
  simp only [Nat.cast_id, Nat.add_comm]

@[simp] theorem radix_nil (B : Nat) : radix B [] = 0 := rfl


theorem radix_lt_pow_length {B : Nat} (hB : 1 < B) (words : List Nat)
    (bounded : ∀ w ∈ words, w < B) : radix B words < B ^ words.length := by
  unfold radix
  simpa only [List.length_reverse] using
    Nat.ofDigits_lt_base_pow_length hB
      (fun w hw => bounded w (List.mem_reverse.mp hw))

/-- Fixed width makes leading zero words unambiguous. -/
theorem radix_injective_of_length_eq {B : Nat} (hB : 1 < B)
    {xs ys : List Nat} (sameLength : xs.length = ys.length)
    (xsBounded : ∀ w ∈ xs, w < B) (ysBounded : ∀ w ∈ ys, w < B)
    (sameAddress : radix B xs = radix B ys) : xs = ys := by
  have reversed : xs.reverse = ys.reverse :=
    Nat.ofDigits_inj_of_len_eq hB (by simpa only [List.length_reverse] using sameLength)
      (fun w hw => xsBounded w (List.mem_reverse.mp hw))
      (fun w hw => ysBounded w (List.mem_reverse.mp hw)) sameAddress
  have h := congrArg List.reverse reversed
  simpa only [List.reverse_reverse] using h

/-- One larger than the proved bound on every canonical word. -/
def base (n m s d : Nat) : Nat := wordBound n m s d + 1

@[simp] theorem base_eq (n m s d : Nat) :
    base n m s d = n + m + 2^s + 2^d + 4 := by
  simp [base, wordBound, Nat.add_assoc]

theorem one_lt_base (n m s d : Nat) : 1 < base n m s d := by
  have h : 3 ≤ wordBound n m s d := by
    unfold wordBound
    exact Nat.le_add_left 3 _
  unfold base
  omega

theorem bodyWords_lt_base {n m k s d : Nat} (body : Body n m k s d)
    (w : Nat) (hw : w ∈ bodyWords body) : w < base n m s d :=
  Nat.lt_succ_of_le (bodyWords_bounded body w hw)

def capacity (n m k s d : Nat) : Nat := (base n m s d) ^ (1 + 9*k)


def bodyAddress {n m k s d : Nat} (body : Body n m k s d) :
    Fin (capacity n m k s d) :=
  ⟨radix (base n m s d) (bodyWords body), by
    simpa only [capacity, bodyWords_length] using
      radix_lt_pow_length (one_lt_base n m s d) (bodyWords body) (bodyWords_lt_base body)⟩

@[simp] theorem bodyAddress_val {n m k s d : Nat} (body : Body n m k s d) :
    (bodyAddress body).val = radix (base n m s d) (bodyWords body) := rfl

theorem bodyAddress_injective {n m k s d : Nat} :
    Function.Injective (bodyAddress (n := n) (m := m) (k := k) (s := s) (d := d)) := by
  intro x y h
  apply bodyWords_injective
  exact radix_injective_of_length_eq (one_lt_base n m s d)
    (by simp only [bodyWords_length]) (bodyWords_lt_base x) (bodyWords_lt_base y)
    (congrArg Fin.val h)


end UniqueGamesTheorem.Reduction.CanonicalAddress

end

section

namespace UniqueGamesTheorem.Reduction.CanonicalWordTemplate

open Foundations.Complexity CanonicalEncoding

/-- A literal word or a reference to one of the four saved input fields. -/
inductive Token
  | literal (value : Nat)
  | name (index : Fin 3)
  | occurrence
  deriving DecidableEq, Repr

def evalToken (names : Fin 3 → Nat) (occurrence : Nat) : Token → Nat
  | .literal value => value
  | .name index => names index
  | .occurrence => occurrence

def evalTemplate (names : Fin 3 → Nat) (occurrence : Nat)
    (tokens : List Token) : List Nat :=
  tokens.map (evalToken names occurrence)

def isVariable : Token → Bool
  | .literal _ => false
  | .name _ => true
  | .occurrence => true

def variableTokens (tokens : List Token) : List Token := tokens.filter isVariable

def blankTemplate : List Token :=
  [.literal 0, .literal 0, .literal 0, .literal 0, .literal 0,
    .literal 0, .literal 0, .literal 0, .literal 0]

def singleTemplate {s d : Nat} (index : Fin 3) (coefficient : Ambient s d) : List Token :=
  [.literal 1, .name index, .literal 0,
    .literal (vectorWord coefficient.1), .literal (vectorWord coefficient.2),
    .literal 0, .literal 0, .literal 0, .literal 0]

def fullTemplate {s d : Nat} (coefficients : Fin 3 → Ambient s d) : List Token :=
  [.literal 2, .literal 0, .occurrence,
    .literal (vectorWord (coefficients 0).1), .literal (vectorWord (coefficients 0).2),
    .literal (vectorWord (coefficients 1).1), .literal (vectorWord (coefficients 1).2),
    .literal (vectorWord (coefficients 2).1), .literal (vectorWord (coefficients 2).2)]

/-- Coefficient equality alone selects the record tag and the input field. -/
def template {s d : Nat} (a : Fin 3 → Ambient s d) : List Token :=
  if a 0 = a 1 then
    if a 0 = a 2 then blankTemplate else singleTemplate 2 (a 2 + a 0)
  else if a 0 = a 2 then singleTemplate 1 (a 1 + a 0)
  else if a 1 = a 2 then singleTemplate 0 (a 0 + a 2)
  else fullTemplate (ActualCanonical.normalize a)

@[simp] theorem blankTemplate_length : blankTemplate.length = 9 := rfl

@[simp] theorem singleTemplate_length {s d : Nat} (index : Fin 3)
    (coefficient : Ambient s d) : (singleTemplate index coefficient).length = 9 := rfl

@[simp] theorem fullTemplate_length {s d : Nat} (coefficients : Fin 3 → Ambient s d) :
    (fullTemplate coefficients).length = 9 := rfl

@[simp] theorem template_length {s d : Nat} (a : Fin 3 → Ambient s d) :
    (template a).length = 9 := by
  unfold template
  split_ifs <;> rfl


/-- The template evaluates to the exact existing canonical-record encoding. -/
theorem eval_template {n m s d : Nat} (names : Fin m → Fin 3 → Fin n)
    (occurrence : Fin m) (a : Fin 3 → Ambient s d) :
    evalTemplate (fun j => (names occurrence j).val) occurrence.val (template a) =
      recordWords (ActualCanonical.record names occurrence a) := by
  unfold template ActualCanonical.record
  split_ifs <;> rfl

@[simp] theorem variableTokens_blankTemplate : variableTokens blankTemplate = [] := rfl

@[simp] theorem variableTokens_singleTemplate {s d : Nat} (index : Fin 3)
    (coefficient : Ambient s d) :
    variableTokens (singleTemplate index coefficient) = [.name index] := rfl

@[simp] theorem variableTokens_fullTemplate {s d : Nat}
    (coefficients : Fin 3 → Ambient s d) :
    variableTokens (fullTemplate coefficients) = [.occurrence] := rfl


end UniqueGamesTheorem.Reduction.CanonicalWordTemplate

end

end OAI
