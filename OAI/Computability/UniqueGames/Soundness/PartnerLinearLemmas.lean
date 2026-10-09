/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Order.Archimedean.Basic
import Std
import OAI.Computability.UniqueGames.Gadgets.AdaptivePathsLemmas
import OAI.Computability.UniqueGames.Reduction.BinaryLinear
import OAI.Computability.UniqueGames.Soundness.LinearMapDensityLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Soundness.PartnerLinear

open PartnerProjection
open UniqueGamesTheorem.Integration.BinaryLinear (F2 ofBit toBit ofBit_toBit
  toBit_ofBit ofBit_xor)

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

abbrev SourceCoordinates (P : Type) := F2 × (P → F2 × F2)
abbrev Active := {j : P // active j = true}
abbrev Inactive := {j : P // active j = false}
abbrev PartnerCoordinates := F2 × ((Inactive active → F2 × F2) × (Active active → F2))

def sourceCoordinates (x : SourcePoint rhs) : SourceCoordinates P :=
  (ofBit x.homogeneous, fun j => (ofBit (x.coordinates j).first, ofBit (x.coordinates j).second))

def sourceFromCoordinates (v : SourceCoordinates P) : SourcePoint rhs where
  homogeneous := toBit v.1
  coordinates := fun j => complete .first (rhs j && toBit v.1)
    (toBit (v.2 j).1) (toBit (v.2 j).2)
  valid := by intro j; exact parity_complete _ _ _ _

def sourceEquiv : SourcePoint rhs ≃ SourceCoordinates P where
  toFun := sourceCoordinates rhs
  invFun := sourceFromCoordinates rhs
  left_inv x := by
    apply source_ext rhs
    · exact toBit_ofBit _
    · funext j
      change complete .first (rhs j && toBit (ofBit x.homogeneous))
        (toBit (ofBit (x.coordinates j).first))
        (toBit (ofBit (x.coordinates j).second)) = x.coordinates j
      simp only [toBit_ofBit, ← x.valid j]
      exact complete_coordinates .first (x.coordinates j)
  right_inv v := by
    apply Prod.ext
    · exact ofBit_toBit _
    · funext j
      apply Prod.ext <;> exact ofBit_toBit _

def partnerCoordinates (y : PartnerPoint rhs active) : PartnerCoordinates active :=
  (ofBit y.homogeneous,
    (fun j => (ofBit (y.full j.val).first, ofBit (y.full j.val).second),
      fun j => ofBit (y.single j.val)))

def partnerFromCoordinates (v : PartnerCoordinates active) : PartnerPoint rhs active where
  homogeneous := toBit v.1
  full := fun j => if hj : active j = false then
    complete .first (rhs j && toBit v.1)
      (toBit (v.2.1 ⟨j, hj⟩).1) (toBit (v.2.1 ⟨j, hj⟩).2)
    else zeroTriple
  single := fun j => if hj : active j = true then toBit (v.2.2 ⟨j, hj⟩) else false
  full_zero := by intro j hj; simp [hj]
  full_valid := by intro j hj; simp only [dite_eq_left hj]; exact parity_complete _ _ _ _
  single_zero := by intro j hj; simp [hj]

def partnerEquiv : PartnerPoint rhs active ≃ PartnerCoordinates active where
  toFun := partnerCoordinates rhs active
  invFun := partnerFromCoordinates rhs active
  left_inv y := by
    apply partner_ext rhs active
    · exact toBit_ofBit _
    · funext j
      cases hj : active j with
      | false =>
        change (if hj' : active j = false then
          complete .first (rhs j && toBit (ofBit y.homogeneous))
            (toBit (ofBit (y.full j).first)) (toBit (ofBit (y.full j).second))
          else zeroTriple) = y.full j
        simp only [dite_eq_left hj, toBit_ofBit, ← y.full_valid j hj]
        exact complete_coordinates .first (y.full j)
      | true => simpa [partnerFromCoordinates, hj] using (y.full_zero j hj).symm
    · funext j
      cases hj : active j with
      | false => simpa [partnerFromCoordinates, hj] using (y.single_zero j hj).symm
      | true => simp [partnerFromCoordinates, partnerCoordinates, hj, toBit_ofBit]
  right_inv v := by
    apply Prod.ext
    · exact ofBit_toBit _
    · apply Prod.ext
      · funext j
        simp [partnerCoordinates, partnerFromCoordinates, j.property, complete, ofBit_toBit]
      · funext j
        simp [partnerCoordinates, partnerFromCoordinates, j.property, ofBit_toBit]

noncomputable instance sourceAddCommGroup : AddCommGroup (SourcePoint rhs) :=
  (sourceEquiv rhs).addCommGroup

noncomputable instance sourceModule : Module F2 (SourcePoint rhs) :=
  (sourceEquiv rhs).addEquiv.module F2

noncomputable instance partnerAddCommGroup : AddCommGroup (PartnerPoint rhs active) :=
  (partnerEquiv rhs active).addCommGroup

noncomputable instance partnerModule : Module F2 (PartnerPoint rhs active) :=
  (partnerEquiv rhs active).addEquiv.module F2

noncomputable def sourceLinearEquiv : SourcePoint rhs ≃ₗ[F2] SourceCoordinates P :=
  (sourceEquiv rhs).addEquiv.linearEquiv F2

noncomputable def partnerLinearEquiv : PartnerPoint rhs active ≃ₗ[F2] PartnerCoordinates active :=
  (partnerEquiv rhs active).addEquiv.linearEquiv F2

noncomputable instance sourceFintype [Fintype P] : Fintype (SourcePoint rhs) := by
  classical
  exact Fintype.ofEquiv (SourceCoordinates P) (sourceEquiv rhs).symm

noncomputable instance partnerFintype [Fintype P] : Fintype (PartnerPoint rhs active) := by
  classical
  exact Fintype.ofEquiv (PartnerCoordinates active) (partnerEquiv rhs active).symm

theorem source_add (x y : SourcePoint rhs) : x + y = addSource rhs x y := by
  apply (sourceEquiv rhs).injective
  change sourceEquiv rhs ((sourceEquiv rhs).symm (sourceEquiv rhs x + sourceEquiv rhs y)) = _
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact (ofBit_xor _ _).symm
  · funext j
    apply Prod.ext <;> exact (ofBit_xor _ _).symm

theorem partner_add (x y : PartnerPoint rhs active) : x + y = addPartner rhs active x y := by
  apply (partnerEquiv rhs active).injective
  change partnerEquiv rhs active ((partnerEquiv rhs active).symm
    (partnerEquiv rhs active x + partnerEquiv rhs active y)) = _
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact (ofBit_xor _ _).symm
  · apply Prod.ext
    · funext j
      apply Prod.ext <;> exact (ofBit_xor _ _).symm
    · funext j
      exact (ofBit_xor _ _).symm

/-- Over F₂, additivity already implies linearity. -/
noncomputable def projection : SourcePoint rhs →ₗ[F2] PartnerPoint rhs active :=
  (AddMonoidHom.mk' (project rhs active slot) (fun x y => by
    rw [source_add, partner_add]
    exact project_add rhs active slot x y)).toZModLinearMap 2

theorem projection_apply (x : SourcePoint rhs) :
    projection rhs active slot x = project rhs active slot x := rfl


noncomputable instance sourceFiniteDimensional [Fintype P] :
    FiniteDimensional F2 (SourcePoint rhs) :=
  (sourceLinearEquiv rhs).symm.finiteDimensional

noncomputable instance partnerFiniteDimensional [Fintype P] :
    FiniteDimensional F2 (PartnerPoint rhs active) :=
  (partnerLinearEquiv rhs active).symm.finiteDimensional


end UniqueGamesTheorem.Soundness.PartnerLinear

end

section

namespace UniqueGamesTheorem.Soundness.RepetitionUpper


/-- A uniformly sampled vector in a `d`-dimensional binary space is zero with
probability `2^(-d)`.  The counting justification is a separate obligation. -/
def zeroProbability (d : Nat) : Rat := (1 / 2 : Rat) ^ d

theorem zeroProbability_nonneg (d : Nat) : 0 ≤ zeroProbability d := by
  exact Rat.pow_nonneg (by grind)

theorem zeroProbability_le_one (d : Nat) : zeroProbability d ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)


def decoderThreshold (theta : Rat) (q : Nat) : Rat := theta ^ 3 / (64 * (q : Rat))

theorem decoderThreshold_pos (theta : Rat) (q : Nat)
    (htheta : 0 < theta) (hq : 0 < q) : 0 < decoderThreshold theta q := by
  unfold decoderThreshold
  positivity

/-- An elementary Archimedean bound for rational parameters. -/
theorem exists_pos_nat_gt (x : Rat) : ∃ n : Nat, 0 < n ∧ x < (n : Rat) := by
  obtain ⟨n, hn⟩ := exists_nat_gt x
  exact ⟨n + 1, Nat.succ_pos _, hn.trans_le (by exact_mod_cast Nat.le_succ n)⟩

/-- Positive powers of a rational base below one eventually fall below every
positive rational threshold; this supplies the search target in (4.4). -/
theorem exists_power_lt (b threshold : Rat) (hb : 0 ≤ b) (hb' : b < 1)
    (ht : 0 < threshold) : ∃ n : Nat, 0 < n ∧ b ^ n < threshold := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ht hb'
  refine ⟨n + 1, Nat.succ_pos _, lt_of_le_of_lt ?_ hn⟩
  exact pow_le_pow_of_le_one hb hb'.le (Nat.le_succ n)

theorem zeroProbability_pos (d : Nat) : 0 < zeroProbability d := by
  exact Rat.pow_pos (by grind)

theorem exists_repetition_length (L q : Nat) (a theta : Rat)
    (ha : 0 ≤ a) (ha' : a < 1) (htheta : 0 < theta) (hq : 0 < q) :
    ∃ t : Nat, 0 < t ∧
      (1 - zeroProbability L * (1 - a)) ^ t < decoderThreshold theta q := by
  have hp := zeroProbability_pos L
  have hp' := zeroProbability_le_one L
  have hc : 0 < 1 - a := by grind
  have hmul := Rat.mul_le_mul_of_nonneg_right hp' (Rat.le_of_lt hc)
  have hpos := Rat.mul_pos hp hc
  apply exists_power_lt
  · grind
  · grind
  · exact decoderThreshold_pos theta q htheta hq


end UniqueGamesTheorem.Soundness.RepetitionUpper

end

end OAI
