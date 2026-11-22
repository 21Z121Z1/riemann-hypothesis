import Mathlib
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
import Formalism.SharpRestriction.Divisibility.ChainOperators.Bundle0002
import Formalism.SharpRestriction.Divisibility.RankTruncation.Bundle0001
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0039
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0038
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0036
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0037
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0042
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Development.AutomorphicArithmetic.OrbitLabellings.Bundle0003
import Formalism.SharpRestriction.Divisibility.RankTruncation.RkLemmaBridge

-- bundled from Formalism.SharpRestriction.Divisibility.ChainOperators.CutDivD
section
noncomputable section

namespace Formalism.MainNotions.DIV.CutDivD

open Finset

open Finset

theorem pow_val_add {R : Type} [CommRing R] {p : ℕ} [Fact p.Prime] {ζ : R}
    (hζ : IsPrimitiveRoot ζ p) (s t : ZMod p) :
    ζ ^ (s + t).val = ζ ^ s.val * ζ ^ t.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (s.val + t.val) p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem sum_char {R : Type} [CommRing R] [IsDomain R] {p : ℕ} [hp : Fact p.Prime] {ζ : R}
    {ι : Type} [Fintype ι] [DecidableEq ι] (hζ : IsPrimitiveRoot ζ p) (w : ι → ZMod p) :
    ∑ y : ι → ZMod p, ζ ^ (∑ a, w a * y a).val =
      if w = 0 then (p : R) ^ Fintype.card ι else 0 := by
  have : Fact (1 < p) := ⟨hp.out.one_lt⟩
  split_ifs with hw
  · subst hw
    simp [ZMod.card]
  · obtain ⟨a0, ha0⟩ : ∃ a0, w a0 ≠ 0 := by
      by_contra h; push Not at h; exact hw (funext h)
    have hshift : (∑ y : ι → ZMod p, ζ ^ (∑ a, w a * y a).val) =
        (∑ y : ι → ZMod p, ζ ^ (∑ a, w a * y a).val) * ζ := by
      conv_lhs => rw [← Fintype.sum_equiv (Equiv.addRight (Pi.single a0 (w a0)⁻¹ : ι → ZMod p))
        (fun y => ζ ^ (∑ a, w a * (y + (Pi.single a0 (w a0)⁻¹ : ι → ZMod p)) a).val)
        (fun y => ζ ^ (∑ a, w a * y a).val) (fun _ => rfl)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      have e : ∑ a, w a * (y + (Pi.single a0 (w a0)⁻¹ : ι → ZMod p)) a = (∑ a, w a * y a) + 1 := by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single a0]
        · simp [ha0]
        · intro b _ hb; simp [hb]
        · simp
      rw [e, pow_val_add hζ, ZMod.val_one, pow_one]
    have hne : ζ ≠ 1 := hζ.ne_one hp.out.one_lt
    have h0 : (∑ y : ι → ZMod p, ζ ^ (∑ a, w a * y a).val) * (ζ - 1) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne

theorem l2 : ConditionalKappaBounds.L2.LocalAdditiveCharacterExpansion := by
  intro p _ f n R _ _ ζ hζ φ h1 h2
  classical
  let φb : (Fin f × Fin n → ZMod p) → R := fun v => φ (fun a => (((v a).val : ℕ) : ℚ_[p]))
  refine ⟨fun y => ∑ v : Fin f × Fin n → ZMod p, φb v * ζ ^ (∑ a, v a * (-y) a).val, fun x => ?_⟩
  by_cases h : ∀ a, ‖x a‖ ≤ 1
  · rw [dif_pos h]
    obtain ⟨xi, hxi, hxb0⟩ : ∃ xi : Fin f × Fin n → ℤ_[p], (∀ a, (xi a : ℚ_[p]) = x a) ∧
        ∀ a, PadicInt.toZMod (show ℤ_[p] from ⟨x a, h a⟩) = PadicInt.toZMod (xi a) :=
      ⟨fun a => ⟨x a, h a⟩, fun a => rfl, fun a => rfl⟩
    obtain ⟨xb, hxb⟩ : ∃ xb : Fin f × Fin n → ZMod p,
        ∀ a, PadicInt.toZMod (xi a) = xb a := ⟨_, fun a => rfl⟩
    simp only [hxb0, hxb]

    have hz : ∀ a, ∃ z : ℤ_[p], z * (p : ℤ_[p]) =
        xi a - (ZMod.cast (xb a) : ℤ_[p]) := by
      intro a
      have := PadicInt.toZMod_spec (xi a)
      rw [hxb a, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at this
      exact this
    choose z hz using hz
    have step1 : φ x = φb xb := by
      have := h2 (fun a => (((xb a).val : ℕ) : ℚ_[p])) z
      show φ x = φ (fun a => (((xb a).val : ℕ) : ℚ_[p]))
      rw [← this]
      congr 1
      funext a
      have e := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) (hz a)
      rw [PadicInt.coe_mul, PadicInt.coe_sub, ZMod.cast_eq_val, PadicInt.coe_natCast, PadicInt.coe_natCast] at e
      rw [hxi a] at e
      linear_combination (-1 : ℚ_[p]) * e
    rw [step1]

    have step2 : ∀ (y v : Fin f × Fin n → ZMod p),
        ζ ^ (∑ a, v a * (-y) a).val * ζ ^ (∑ a, xb a * y a).val = ζ ^ (∑ a, (xb - v) a * y a).val := by
      intro y v
      rw [← pow_val_add hζ, ← Finset.sum_add_distrib]
      congr 2
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Pi.neg_apply, Pi.sub_apply]
      ring
    simp_rw [Finset.sum_mul, mul_assoc, step2]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_char hζ]
    rw [Finset.sum_eq_single xb]
    · simp [Fintype.card_prod, mul_comm]
    · intro v _ hv
      rw [if_neg (sub_ne_zero.mpr (Ne.symm hv)), mul_zero]
    · simp
  · rw [dif_neg h]
    have : φ x = 0 := by
      by_contra hx
      exact h (h1 x hx)
    rw [this, mul_zero]

open Formalism.BasicNotions

theorem projector_statement_of_stability (D : D7) (hS : ThetaNormsAndLinks.SupLatticeGroupStable D) : PDVN.ConjugationNormInvariance D :=
  Formalism.MainNotions.DIV.projector_statement_of_integrality D (fun i b => IntegralHeckeForms.idempotent_scaled_integral D i b) hS

end Formalism.MainNotions.DIV.CutDivD

end
end

-- bundled from Formalism.SharpRestriction.Divisibility.ChainOperators.OrbitEntryBounds
section
namespace Formalism.MainNotions.DIV.Lemmas.OrbitEntryBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

def toEnt {D : D7} (E : OrbitPlaces.Ent D) : PI.OrbJet.Ent D :=
  ⟨E.nu, E.nu_row, E.nu_rows, E.Th, E.ep, E.be, E.sg⟩

theorem addition_bound_holds (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitsAddLowerBound E := by
  intro p _ h u i hi R hR ep sg be hbe β hβ Th hTh
  exact PI.OrbAddUp D (toEnt E) p ⟨h.five, h.even, h.two⟩ u i hi R hR ep sg be hbe β hβ Th hTh

theorem orbitsAddAtConjugate_ent (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitsAddAtConjugate E :=
  PI.OrbAddOne D (toEnt E)

theorem restriction_bound_holds (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitRestriction E := by
  intro p _ h u i R hR ep sg be hbe Th hTh r hr
  exact PI.OrbRestr D (toEnt E) p ⟨h.five, h.even, h.two⟩ u i R hR ep sg be hbe Th hTh r hr

theorem orbit_restriction_at_conjugate (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitRestrictionAtConjugate E :=
  PI.OrbRestrOne D (toEnt E)

theorem entry_divisor_bound_holds (D : D7) (E : OrbitPlaces.Ent D) (Dx : DivX D) (hs : OrbitPlaces.ThetaKernelShapeAtD E Dx) : OrbitPlaces.EntriesAtDiscriminant E Dx := by
  intro u μ w hL hc i hi L L'
  exact _root_.jet_bound_ramified_prime D Dx E.nu E.nu_row E.nu_rows E.Th hs u μ w hL hc i hi L L'

private theorem entry_number_bound_holds (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ)
    (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge C6 C K ce) : OrbitPlaces.ScaledGeneratorsInSup E L K ce := by
  intro p hp h5 hcs hpX u i hi
  exact ⟨fun Th hTh => UpperTheory.kvalGe_theta_of_shape D L X E hS p h5 hcs.1 hcs.2.2 hpX u i hi Th hTh,
    fun hL => UpperTheory.fInert_sub_eatI_le_orbit_average_sub_errors D L X K E ce C6 C hS hC hL p hp.out h5 hcs hpX i hi⟩

theorem orbit_entry_bounds_of_family (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ)
    (hF : OrbitPlaces.OrbitValuationBound E X K ce) (hs : OrbitPlaces.ThetaKernelShapeAtD E Dx) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge C6 C K ce) :
    OrbitPlaces.Core D L X K Dx E ce C :=
  ⟨addition_bound_holds D E, orbitsAddAtConjugate_ent D E, restriction_bound_holds D E, orbit_restriction_at_conjugate D E, hF, entry_divisor_bound_holds D E Dx hs,
    PI.SumOrbC D L X K ce E C6 C hS hC, entry_number_bound_holds D L X K E ce C6 C hS hC⟩

theorem orbit_entry_bounds_hold (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ)
    (hA : OrbitPlaces.OrbitLetterBoundsAll C6 C) (hs : OrbitPlaces.ThetaKernelShapeAtD E Dx) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge C6 C K ce) :
    OrbitPlaces.Core D L X K Dx E ce C :=
  orbit_entry_bounds_of_family D L X K Dx E ce C6 C (PI.OrbBoundF D L X K ce E C6 C hA hS hC) hs hS hC

end Formalism.MainNotions.DIV.Lemmas.OrbitEntryBounds
end

-- bundled from Formalism.SharpRestriction.Divisibility.ChainOperators.RankInputOfDualBound
section
namespace Formalism.MainNotions.DIV.CutRk

theorem rk_true : ConditionalKappaBounds.Rk.RkProp := by
  intro dp f m r t x Ct q d rd CRd hx hC hdp hfr hmr hrt ht2 htx hq hd hrd
  have hx0 : 0 < x := lt_trans one_pos hx
  have ht2R : (2 : ℝ) ≤ t := by exact_mod_cast ht2
  have hCt : 0 < Ct := by
    by_contra h
    push Not at h
    have : x ^ Ct ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le h
    linarith
  set A := x ^ (2 * Ct + 5) with hAdef
  have hA1 : 1 < A := Real.one_lt_rpow hx (by linarith)
  have hA0 : 0 < A := by linarith
  have hqA : A < q := hq
  have hdA : A < d := hd
  have hsq : A < Real.sqrt (q * d) := by
    rw [Real.lt_sqrt hA0.le]
    nlinarith
  have hrdA : A < rd := lt_of_lt_of_le hsq hrd
  have hrd1 : 1 ≤ rd := by linarith

  have hdpN : dp ≤ 2 * t * t := by
    have h1 : f * m ≤ t * t := Nat.mul_le_mul (by omega) (by omega)
    calc dp ≤ 2 * f * m := hdp
      _ = 2 * (f * m) := by ring
      _ ≤ 2 * (t * t) := by omega
      _ = 2 * t * t := by ring
  have hdpR : (dp : ℝ) ≤ 2 * t * t := by exact_mod_cast hdpN
  have hdp0 : (0 : ℝ) ≤ dp := Nat.cast_nonneg _
  have h1 : (dp : ℝ) ^ 2 ≤ (t : ℝ) ^ 8 := by
    have : (dp : ℝ) ^ 2 ≤ (2 * t * t) ^ 2 := pow_le_pow_left₀ hdp0 hdpR 2
    have ht4 : (16 : ℝ) ≤ (t : ℝ) ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) ht2R 4
      norm_num at this; linarith
    nlinarith
  have h2 : (t : ℝ) ^ 8 ≤ x ^ (8 * Ct) := by
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    have := pow_le_pow_left₀ ht0 htx 8
    rw [← Real.rpow_natCast (x ^ Ct) 8, ← Real.rpow_mul hx0.le] at this
    simpa [mul_comm] using this
  have h3 : x ^ (8 * Ct) ≤ A ^ (4 : ℝ) := by
    rw [hAdef, ← Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have h4 : A ^ (4 : ℝ) < rd ^ (4 : ℝ) := Real.rpow_lt_rpow hA0.le hrdA (by norm_num)
  have h5 : rd ^ (4 : ℝ) ≤ rd ^ (CRd - 2) := Real.rpow_le_rpow_of_exponent_le hrd1 (by linarith)
  linarith

open Formalism.BasicNotions Formalism.MainNotions in

theorem rank_input_of_dual_bound (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)
    (hT : ConditionalKappaBounds.Rk.DPle D X) (CRd : ℝ) (hC : 6 ≤ CRd) : ThetaNormsAndLinks.CharacterRankDiscriminant D X CRd :=
  ConditionalKappaBounds.Rk.rank_admissible_of_discriminant rk_true D L P X hT CRd hC

end Formalism.MainNotions.DIV.CutRk
end

