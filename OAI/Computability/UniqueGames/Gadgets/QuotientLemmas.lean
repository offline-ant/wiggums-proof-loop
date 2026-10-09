/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Card
import OAI.Computability.UniqueGames.Gadgets.AdaptivePathsLemmas
import OAI.Computability.UniqueGames.Gadgets.ConcatenationLemmas

namespace OAI

namespace UniqueGamesTheorem.Gadget.Quotient

variable {𝕜 P B : Type*} [Ring 𝕜]
variable [AddCommGroup P] [Module 𝕜 P] [AddCommGroup B] [Module 𝕜 B]

/-- The logical kernel viewed as a submodule of the ambient input space. -/
def shiftKernel (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) : Submodule 𝕜 P :=
  (LinearMap.ker lam).map R.subtype

abbrev Space (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) := P ⧸ shiftKernel R lam

def projection (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    P →ₗ[𝕜] Space R lam := (shiftKernel R lam).mkQ

theorem projection_surjective (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    Function.Surjective (projection R lam) := (shiftKernel R lam).mkQ_surjective

theorem mem_shiftKernel (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (x : P) :
    x ∈ shiftKernel R lam ↔ ∃ h : R, lam h = 0 ∧ (h : P) = x := Iff.rfl

theorem projection_eq_zero (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (h : R) :
    projection R lam (h : P) = 0 ↔ lam h = 0 := by
  change (Submodule.Quotient.mk (h : P) : Space R lam) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, mem_shiftKernel]
  constructor
  · rintro ⟨k, hk, hkh⟩
    have : k = h := Subtype.ext hkh
    simpa [this] using hk
  · intro hh
    exact ⟨h, hh, rfl⟩

/-- Inclusion of the quotient shift space into the ambient quotient. -/
def quotientShift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    (R ⧸ LinearMap.ker lam) →ₗ[𝕜] Space R lam :=
  (LinearMap.ker lam).liftQ ((projection R lam).comp R.subtype) (by
    intro h hh
    exact (projection_eq_zero R lam h).mpr hh)

@[simp] theorem quotientShift_mk (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (h : R) :
    quotientShift R lam (Submodule.Quotient.mk h) = projection R lam (h : P) := rfl

/-- The logical alphabet is realized as actual linear shifts of the quotient. -/
noncomputable def logicalShift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) : B →ₗ[𝕜] Space R lam :=
  (quotientShift R lam).comp (lam.quotKerEquivOfSurjective hlam).symm.toLinearMap

@[simp] theorem logicalShift_lambda (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (h : R) :
    logicalShift R lam hlam (lam h) = projection R lam (h : P) := by
  simp [logicalShift, LinearMap.quotKerEquivOfSurjective_symm_apply]

theorem logicalShift_injective (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) : Function.Injective (logicalShift R lam hlam) := by
  apply Function.Injective.comp ?_ (lam.quotKerEquivOfSurjective hlam).symm.injective
  apply (LinearMap.ker_eq_bot (f := quotientShift R lam)).mp
  apply Submodule.ker_liftQ_eq_bot
  intro h hh
  exact (projection_eq_zero R lam h).mp hh

/-- Equivariance under every allowed shift; no linearity of `C` is assumed. -/
def Equivariant (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (C : P → B) : Prop :=
  ∀ (u : P) (h : R), C (u + (h : P)) = C u + lam h


theorem output_constant_on_fibers (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (x y : P)
    (hxy : projection R lam x = projection R lam y) : C x = C y := by
  have hm : x - y ∈ shiftKernel R lam := (Submodule.Quotient.eq _).mp hxy
  obtain ⟨h, hh, hval⟩ := (mem_shiftKernel R lam _).mp hm
  have he : y + (h : P) = x := by rw [hval, add_comm, sub_add_cancel]
  simpa only [he, hh, add_zero] using hC y h

def output (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) : Space R lam → B :=
  _root_.Quotient.lift C (fun _ _ h =>
    output_constant_on_fibers R lam C hC _ _ (_root_.Quotient.sound h))

@[simp] theorem output_projection (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (u : P) :
    output R lam C hC (projection R lam u) = C u := rfl

theorem output_equivariant (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (x : Space R lam) (b : B) :
    output R lam C hC (x + logicalShift R lam hlam b) = output R lam C hC x + b := by
  obtain ⟨u, rfl⟩ := projection_surjective R lam x
  obtain ⟨h, rfl⟩ := hlam b
  rw [logicalShift_lambda, ← map_add, output_projection, output_projection]
  exact hC u h

/-- Noise pushforward preserves the change event pointwise, before averaging. -/
theorem change_iff (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (u a : P) :
    (output R lam C hC (projection R lam u + projection R lam a) ≠
      output R lam C hC (projection R lam u)) ↔ C (u + a) ≠ C u := by
  rw [← map_add, output_projection, output_projection]


/-- Every fiber has the same cardinality, justifying uniform-input pushforward. -/
theorem fiber_card (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (x : Space R lam) :
    Nat.card {u : P // projection R lam u = x} = Nat.card (shiftKernel R lam) := by
  have h := Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective
    (f := (projection R lam).toAddMonoidHom) (projection_surjective R lam) x)
  change Nat.card {u : P // projection R lam u = x} =
    Nat.card (LinearMap.ker (projection R lam)) at h
  simpa only [projection, Submodule.ker_mkQ] using h

end UniqueGamesTheorem.Gadget.Quotient

namespace UniqueGamesTheorem.Gadget

section

universe u v

/-- An equivariant finite stage, including its concrete finite noise sampler. -/
structure Stage (k : Type u) (B : Type v) [CommRing k]
    [AddCommGroup B] [Module k B] where
  Input : Type v
  Shift : Type v
  Noise : Type v
  [inputAdd : AddCommGroup Input]
  [inputModule : Module k Input]
  [shiftAdd : AddCommGroup Shift]
  [shiftModule : Module k Shift]
  [inputFinite : Finite Input]
  [shiftFinite : Finite Shift]
  [noiseFinite : Finite Noise]
  [noiseNonempty : Nonempty Noise]
  embed : Shift →ₗ[k] Input
  embed_injective : Function.Injective embed
  logical : Shift →ₗ[k] B
  logical_surjective : Function.Surjective logical
  output : Input → B
  equivariant : ∀ u h, output (u + embed h) = output u + logical h
  noise : Noise → Input

attribute [instance] Stage.inputAdd Stage.inputModule Stage.shiftAdd Stage.shiftModule
  Stage.inputFinite Stage.shiftFinite Stage.noiseFinite Stage.noiseNonempty

namespace Stage

variable {k : Type u} {B : Type v} [CommRing k]
variable [AddCommGroup B] [Module k B] [Finite B]

/-- The height-zero input, shift and uniform noise alphabet. -/
def base : Stage k B where
  Input := B
  Shift := B
  Noise := B
  embed := LinearMap.id
  embed_injective := Function.injective_id
  logical := LinearMap.id
  logical_surjective := Function.surjective_id
  output := id
  equivariant := by intros; rfl
  noise := id

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

/-- One complete recursive level, with actual single-coordinate leaf noise. -/
noncomputable def next (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B)
    (s : Stage k B) : Stage k B where
  Input := I → s.Input
  Shift := parentShifts J s.logical
  Noise := I × s.Noise
  embed := parentEmbed J s.logical s.embed
  embed_injective := parentEmbed_injective J s.logical s.embed s.embed_injective
  logical := parentLogical J s.logical
  logical_surjective := parentLogical_surjective J hJ s.logical s.logical_surjective
  output := parentOutput J s.output Q
  equivariant := parentOutput_equivariant J s.embed s.logical s.output Q s.equivariant
  noise := fun t => Pi.single t.1 (s.noise t.2)

/-- The finite stage at any natural height, using the same alphabet and block
family at every level. Surjectivity and equivariance have been proved by the
constructor, and hence are available at every height without extra hypotheses. -/
noncomputable def iterate (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) : ℕ → Stage k B
  | 0 => base
  | n + 1 => next J hJ Q (iterate J hJ Q n)

@[simp] theorem iterate_zero (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) :
    iterate J hJ Q 0 = base := rfl

@[simp] theorem iterate_succ (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) (n : ℕ) :
    iterate J hJ Q (n + 1) = next J hJ Q (iterate J hJ Q n) := rfl

end Stage

end

/-!
# Actual lifts and their descendant restrictions

Every descendant lift is constructed by a linear section of the child image.
Its detection on the child noise implies detection by the parent family on
the actual embedded noise. The common parent family is chosen before the
child index; only the image section is chosen after that index is known.
-/

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B]

/-- A linear lift of a logical character subspace to the actual stage input. -/
structure Lift (s : Stage k B) (S : Submodule k (B →ₗ[k] k)) where
  family : S →ₗ[k] (s.Input →ₗ[k] k)
  agrees : ∀ z h, family z (s.embed h) = z.val (s.logical h)

/-- Restricting a lift preserves its prescribed logical characters. -/
def Lift.restrict {s : Stage k B} {S T : Submodule k (B →ₗ[k] k)}
    (L : Lift s T) (hST : S ≤ T) : Lift s S where
  family := L.family.comp (Submodule.inclusion hST)
  agrees := by intro z h; exact L.agrees _ h

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

/-- Linear insertion into one physical input coordinate. -/
def singleInput (i : I) (P : Type v) [AddCommGroup P] [Module k P] :
    P →ₗ[k] (I → P) :=
  LinearMap.single (R := k) (φ := fun _ : I => P) i

/-- The logical map of a child, obtained from the common parent first-coordinate
map and the prescribed logical character. -/
def childCharacter (J : I → B →ₗ[k] X × B)
    {S : Submodule k (B →ₗ[k] k)} (γ : S →ₗ[k] (X →ₗ[k] k)) (i : I) :
    S →ₗ[k] (B →ₗ[k] k) where
  toFun z := (γ z).comp ((LinearMap.fst k X B).comp (J i)) +
    z.val.comp ((LinearMap.snd k X B).comp (J i))
  map_add' a b := by ext; simp; abel
  map_smul' c z := by ext; simp [smul_add]

theorem exists_common_child_character
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ i z h,
      L.family z (Pi.single i (s.embed h)) = childCharacter J γ i z (s.logical h) := by
  have hlift : ∀ z (h : parentShifts J s.logical),
      L.family z (parentEmbed J s.logical s.embed h) =
        z.val (parentLogical J s.logical h) := by
    intro z h
    exact L.agrees z h
  have hcommon := parent_lift_common_child (S := S) J hJ s.embed s.logical
    s.logical_surjective
  obtain ⟨γ, hγ⟩ := hcommon L.family S.subtype hlift
  exact ⟨γ, fun i z h => hγ i z h⟩

/-- The descendant family using a section of the actual image. -/
def descendantFamily {s : Stage k B} {S : Submodule k (B →ₗ[k] k)}
    (ψ : S →ₗ[k] ((I → s.Input) →ₗ[k] k)) (i : I)
    (φ : S →ₗ[k] (B →ₗ[k] k))
    (sectionMap : LinearMap.range φ →ₗ[k] S) :
    LinearMap.range φ →ₗ[k] (s.Input →ₗ[k] k) where
  toFun z := (ψ (sectionMap z)).comp (singleInput i s.Input)
  map_add' a b := by ext; simp
  map_smul' c z := by ext; simp

/-- Every child image carries a genuine child lift. The section is constructed
by ordinary linear algebra and is chosen without any later path or leaf symbol. -/
theorem exists_descendant_lift
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S)
    (γ : S →ₗ[k] (X →ₗ[k] k))
    (hγ : ∀ i z h, L.family z (Pi.single i (s.embed h)) =
      childCharacter J γ i z (s.logical h)) (i : I) :
    ∃ (L' : Lift s (LinearMap.range (childCharacter J γ i)))
      (sectionMap : LinearMap.range (childCharacter J γ i) →ₗ[k] S),
      (∀ z, childCharacter J γ i (sectionMap z) = z.val) ∧
      (∀ z p, L'.family z p = L.family (sectionMap z) (Pi.single i p)) := by
  let φ : S →ₗ[k] (B →ₗ[k] k) := childCharacter J γ i
  let : Module.Free k (LinearMap.range φ) :=
    Module.Free.of_divisionRing k (LinearMap.range φ)
  let : Module.Projective k (LinearMap.range φ) := Module.Projective.of_free
  obtain ⟨σ, hσ⟩ := φ.rangeRestrict.exists_rightInverse_of_surjective
    φ.range_rangeRestrict
  have hσ' (z : LinearMap.range φ) : φ (σ z) = z.val :=
    congrArg Subtype.val (congrArg (fun f => f z) hσ)
  let L' : Lift s (LinearMap.range φ) :=
    { family := descendantFamily L.family i φ σ
      agrees := by
        intro z h
        change L.family (σ z) (Pi.single i (s.embed h)) = z.val (s.logical h)
        rw [hγ, hσ'] }
  exact ⟨L', σ, hσ', fun z p => rfl⟩

/-- Pointwise containment of child detection in parent detection. Repeating
this implication along a path preserves the original family at the root. -/
theorem descendant_detection_implies_parent
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S)
    {S' : Submodule k (B →ₗ[k] k)} (L' : Lift s S')
    (sectionMap : S' →ₗ[k] S) (i : I)
    (hfamily : ∀ z p, L'.family z p = L.family (sectionMap z) (Pi.single i p))
    (n : s.Noise) (hdetect : ∃ z, L'.family z (s.noise n) ≠ 0) :
    ∃ z, L.family z ((Stage.next J hJ Q s).noise (i, n)) ≠ 0 := by
  obtain ⟨z, hz⟩ := hdetect
  refine ⟨sectionMap z, ?_⟩
  simpa only [hfamily, Stage.next] using hz

end UniqueGamesTheorem.Gadget

namespace UniqueGamesTheorem.Gadget.Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable def commonGamma (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) : S →ₗ[k] (X →ₗ[k] k) :=
  Classical.choose (exists_common_child_character J hJ Q s S L)

omit [Finite B] [FiniteDimensional k B] in
theorem commonGamma_spec (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) (z : S) (h : s.Shift) :
    L.family z (Pi.single i (s.embed h)) =
      childCharacter J (commonGamma J hJ Q s S L) i z (s.logical h) :=
  Classical.choose_spec (exists_common_child_character J hJ Q s S L) i z h

noncomputable def childDomain (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) : Submodule k (B →ₗ[k] k) :=
  LinearMap.range (childCharacter J (commonGamma J hJ Q s S L) i)

noncomputable def childLift (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    Lift s (childDomain J hJ Q s S L i) :=
  Classical.choose (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i)

noncomputable def childSection (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    childDomain J hJ Q s S L i →ₗ[k] S :=
  Classical.choose (Classical.choose_spec (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i))


omit [Finite B] [FiniteDimensional k B] in
theorem childLift_spec (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I)
    (z : childDomain J hJ Q s S L i) (p : s.Input) :
    (childLift J hJ Q s S L i).family z p =
      L.family (childSection J hJ Q s S L i z) (Pi.single i p) :=
  (Classical.choose_spec (Classical.choose_spec (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i))).2 z p

omit [Finite B] [FiniteDimensional k B] in
theorem child_detection (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) (n : s.Noise)
    (hdetect : ∃ z, (childLift J hJ Q s S L i).family z (s.noise n) ≠ 0) :
    ∃ z, L.family z ((Stage.next J hJ Q s).noise (i, n)) ≠ 0 :=
  descendant_detection_implies_parent J hJ Q s S L _ _ i
    (childLift_spec J hJ Q s S L i) n hdetect

omit [Finite B] in
theorem child_rank_le (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    Module.finrank k (childDomain J hJ Q s S L i) ≤ Module.finrank k S :=
  LinearMap.finrank_range_le _

/-- Terminal logical rank along the actual recursively sampled path. The
final uniform symbol is ignored by this rank function. -/
noncomputable def leafRank
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B) :
    (n : ℕ) → (S : Submodule k (B →ₗ[k] k)) →
    Lift (Stage.iterate J hJ Q n) S → (Stage.iterate J hJ Q n).Noise → ℕ
  | 0, S, _, _ => Module.finrank k S
  | n + 1, S, L, t => leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2

theorem leafRank_le (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q n) S) (t : (Stage.iterate J hJ Q n).Noise) :
    leafRank J hJ Q n S L t ≤ Module.finrank k S := by
  induction n generalizing S with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih _ _ _).trans (child_rank_le J hJ Q _ S L t.1)

end UniqueGamesTheorem.Gadget.Descent

/-!
# Harmonic potential for the actual recursively selected lifts

This is the adaptive induction on the concrete descendant lift construction.
The first outgoing step may begin at a bad subspace; every later orientation
is fresh. Accordingly the bound has one initial bad-space penalty, which
vanishes for the fixed generic top subspace.
-/

namespace UniqueGamesTheorem.Gadget.DescentProbability

open Harmonic Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable instance noiseFintype (n : ℕ) : Fintype (Stage.iterate J hJ Q n).Noise := by
  induction n with
  | zero => exact Fintype.ofFinite B
  | succ n ih =>
    exact inferInstanceAs (Fintype (I × (Stage.iterate J hJ Q n).Noise))

noncomputable def terminalPotential (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ :=
  average (fun t => harmonic (leafRank J hJ Q n S L t))

omit [FiniteDimensional k B] in
@[simp] theorem terminalPotential_zero (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q 0) S) :
    terminalPotential J hJ Q 0 S L = harmonic (Module.finrank k S) := by
  change average (fun _ : (Stage.iterate J hJ Q 0).Noise =>
    harmonic (Module.finrank k S)) = _
  exact average_const _

omit [FiniteDimensional k B] in
theorem terminalPotential_succ (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    terminalPotential J hJ Q (n + 1) S L =
      average (fun i => terminalPotential J hJ Q n
        (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
        (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
  unfold terminalPotential average
  change Finset.univ.expect (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    harmonic (leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2)) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]

/-- The only geometric inputs are the outgoing harmonic loss estimate for
every lift and the fresh-orientation bound for every child image. The lift may
depend on every previous orientation; the proof never declares it independent. -/
theorem expected_terminal_loss
    (bad : Submodule k (B →ₗ[k] k) → Prop) [DecidablePred bad]
    (r₀ : ℕ) (C θ ε : ℚ) (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hsmall : C * ε ≤ 1)
    (hstep : ∀ (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
      (L : Lift (Stage.next J hJ Q s) S), Module.finrank k S ≤ r₀ →
      average (fun i => harmonic (Module.finrank k S) -
        harmonic (Module.finrank k (childDomain J hJ Q s S L i))) ≤
          3 * θ + C * θ * if bad S then 1 else 0)
    (hfresh : ∀ (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
      (L : Lift (Stage.next J hJ Q s) S), Module.finrank k S ≤ r₀ →
      probability (fun i => bad (childDomain J hJ Q s S L i)) ≤ ε)
    (n : ℕ) (S : Submodule k (B →ₗ[k] k)) (L : Lift (Stage.iterate J hJ Q n) S)
    (hcap : Module.finrank k S ≤ r₀) :
    harmonic (Module.finrank k S) - terminalPotential J hJ Q n S L ≤
      4 * n * θ + C * θ * if bad S then 1 else 0 := by
  induction n generalizing S with
  | zero =>
    simp only [terminalPotential_zero, sub_self, Nat.cast_zero, mul_zero, zero_mul,
      zero_add]
    split <;> simp_all [mul_nonneg]
  | succ n ih =>
    let s := Stage.iterate J hJ Q n
    let Sc := childDomain J hJ Q s S L
    let Lc := childLift J hJ Q s S L
    have hchild : average (fun i => harmonic (Module.finrank k (Sc i)) -
        terminalPotential J hJ Q n (Sc i) (Lc i)) ≤
        4 * n * θ + C * θ * probability (fun i => bad (Sc i)) := by
      calc
        _ ≤ average (fun i => 4 * n * θ + C * θ * if bad (Sc i) then 1 else 0) := by
          apply average_mono
          intro i
          exact ih (Sc i) (Lc i) ((child_rank_le J hJ Q s S L i).trans hcap)
        _ = _ := by rw [average_add, average_const, average_mul_left]; rfl
    have hdrop := hstep s S L hcap
    have hbad := hfresh s S L hcap
    have hbad' := mul_le_mul_of_nonneg_left hbad (mul_nonneg hC hθ)
    have hsmall' := mul_le_mul_of_nonneg_right hsmall hθ
    rw [terminalPotential_succ]
    rw [average_sub] at hchild
    rw [average_sub, average_const] at hdrop
    change harmonic (Module.finrank k S) -
      average (fun i => terminalPotential J hJ Q n (Sc i) (Lc i)) ≤ _
    push_cast
    nlinarith

end UniqueGamesTheorem.Gadget.DescentProbability

namespace UniqueGamesTheorem.Gadget.LeafDetection

open Harmonic Descent DescentProbability

universe v

variable {B I X : Type v}
variable [AddCommGroup B] [Module (ZMod 2) B] [Finite B] [FiniteDimensional (ZMod 2) B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module (ZMod 2) X]

variable (J : I → B →ₗ[ZMod 2] X × B)
variable (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable def survivalProbability (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ :=
  probability (fun t => 0 < leafRank J hJ Q n S L t)

noncomputable def detectionProbability (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ := by
  classical
  exact probability (fun t => ∃ z : S, L.family z ((Stage.iterate J hJ Q n).noise t) ≠ 0)

omit [FiniteDimensional (ZMod 2) B] in
theorem detectionProbability_nonneg (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) :
    0 ≤ detectionProbability J hJ Q n S L := by
  classical
  exact probability_nonneg _

omit [FiniteDimensional (ZMod 2) B] in
/-- Restricting the logical domain can only remove detecting characters. -/
theorem detectionProbability_restrict_le (n : ℕ)
    (S T : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2)) (hST : S ≤ T)
    (L : Lift (Stage.iterate J hJ Q n) T) :
    detectionProbability J hJ Q n S (L.restrict hST) ≤
      detectionProbability J hJ Q n T L := by
  classical
  apply probability_mono
  rintro t ⟨z, hz⟩
  exact ⟨Submodule.inclusion hST z, hz⟩

omit [FiniteDimensional (ZMod 2) B] in
theorem detectionProbability_zero_of_rank_pos
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q 0) S) (hrank : 0 < Module.finrank (ZMod 2) S) :
    (1 / 2 : ℚ) ≤ detectionProbability J hJ Q 0 S L := by
  classical
  let : Fintype B := Fintype.ofFinite B
  let : Nontrivial S := Module.nontrivial_of_finrank_pos hrank
  obtain ⟨z, hz⟩ := exists_ne (0 : S)
  have hzval : z.val ≠ 0 := by
    intro he
    exact hz (Subtype.ext he)
  have hex : ∃ b : B, z.val b ≠ 0 := by
    by_contra h
    apply hzval
    ext b
    by_contra hb
    exact h ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hex
  have hagree : L.family z b = z.val b := L.agrees z b
  have hχ : L.family z b ≠ 0 := by rwa [hagree]
  change (1 / 2 : ℚ) ≤ probability (fun b : B => ∃ z : S, L.family z b ≠ 0)
  exact binary_family_detection_ge_half _ (L.family z).toAddMonoidHom b hχ
    (fun b hb => ⟨z, hb⟩)

omit [FiniteDimensional (ZMod 2) B] in
@[simp] theorem survivalProbability_zero
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q 0) S) :
    survivalProbability J hJ Q 0 S L =
      if 0 < Module.finrank (ZMod 2) S then 1 else 0 := by
  change average (fun _ : (Stage.iterate J hJ Q 0).Noise =>
    if 0 < Module.finrank (ZMod 2) S then (1 : ℚ) else 0) = _
  exact average_const _

omit [FiniteDimensional (ZMod 2) B] in
theorem survivalProbability_succ (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    survivalProbability J hJ Q (n + 1) S L =
      average (fun i => survivalProbability J hJ Q n
        (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
        (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
  unfold survivalProbability
  change probability (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    0 < leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2) = _
  exact probability_product _

omit [FiniteDimensional (ZMod 2) B] in
theorem average_child_detection_le (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    average (fun i => detectionProbability J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) ≤
        detectionProbability J hJ Q (n + 1) S L := by
  classical
  unfold detectionProbability
  change _ ≤ probability (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    ∃ z : S, L.family z ((Stage.iterate J hJ Q (n + 1)).noise t) ≠ 0)
  rw [probability_product]
  apply average_mono
  intro i
  apply probability_mono
  intro t hdetect
  exact child_detection J hJ Q (Stage.iterate J hJ Q n) S L i t hdetect

omit [FiniteDimensional (ZMod 2) B] in
/-- Detection by the root lift is at least one half the actual terminal-rank
survival probability, on precisely the recursively generated noise sample. -/
theorem half_survival_le_detection (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) :
    (1 / 2 : ℚ) * survivalProbability J hJ Q n S L ≤
      detectionProbability J hJ Q n S L := by
  induction n generalizing S with
  | zero =>
    rw [survivalProbability_zero]
    split_ifs with hrank
    · simpa only [mul_one] using detectionProbability_zero_of_rank_pos J hJ Q S L hrank
    · simpa only [mul_zero] using detectionProbability_nonneg J hJ Q 0 S L
  | succ n ih =>
    rw [survivalProbability_succ, ← average_mul_left]
    calc
      _ ≤ average (fun i => detectionProbability J hJ Q n
          (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
          (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
        apply average_mono
        intro i
        exact ih _ _
      _ ≤ detectionProbability J hJ Q (n + 1) S L :=
        average_child_detection_le J hJ Q n S L

/-- Actual quarter detection follows from retaining half the initial
harmonic potential; all leaf-to-root event containments are already proved. -/
theorem quarter_detection_of_terminal_potential (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S)
    (hrank : 0 < Module.finrank (ZMod 2) S)
    (hpotential : harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q n S L) :
    (1 / 4 : ℚ) ≤ detectionProbability J hJ Q n S L := by
  have hsurv : (1 / 2 : ℚ) ≤ survivalProbability J hJ Q n S L :=
    survival_probability_ge_half_of_potential (leafRank J hJ Q n S L)
      (Module.finrank (ZMod 2) S) hrank (leafRank_le J hJ Q n S L) hpotential
  have hdet := half_survival_le_detection J hJ Q n S L
  linarith

/-- The fixed generic top subspace may be chosen inside a full logical
family; the resulting quarter bound still concerns the original lift. -/
theorem quarter_detection_of_restricted_terminal_potential (n : ℕ)
    (S T : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2)) (hST : S ≤ T)
    (L : Lift (Stage.iterate J hJ Q n) T)
    (hrank : 0 < Module.finrank (ZMod 2) S)
    (hpotential : harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q n S (L.restrict hST)) :
    (1 / 4 : ℚ) ≤ detectionProbability J hJ Q n T L :=
  (quarter_detection_of_terminal_potential J hJ Q n S (L.restrict hST)
    hrank hpotential).trans (detectionProbability_restrict_le J hJ Q n S T hST L)

end UniqueGamesTheorem.Gadget.LeafDetection

end OAI
