import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbVecAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0009
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0022
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierSizes
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle0002
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ExplicitFormulaBoundHolds

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbScale
section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

section Scale

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem isNormCut_smul (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μ : Measure (Formalism.QuantumDeterminants.Mt k r))
    {c : ℝ} (hc : 0 < c) (θ : Formalism.FourierDecayAlt.B.SS k r → ℝ) :
    Formalism.FourierDecayAlt.D.IsNormCut D γ (ENNReal.ofReal c • μ) θ ↔ Formalism.FourierDecayAlt.D.IsNormCut D γ μ (fun p => c * θ p) := by
  unfold Formalism.FourierDecayAlt.D.IsNormCut
  have hint : ∀ p, ∫ x, θ (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) p) ∂(ENNReal.ofReal c • μ) =
      ∫ x, c * θ (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) p) ∂μ := fun p => by
    rw [integral_smul_measure, ENNReal.toReal_ofReal hc.le, integral_const_mul, smul_eq_mul]
  simp only [hint]
  constructor
  · rintro ⟨hm, hpos, hone⟩
    exact ⟨hm.const_mul c, fun p => mul_nonneg hc.le (hpos p), hone⟩
  · rintro ⟨hm, hpos, hone⟩
    refine ⟨?_, fun p => ?_, hone⟩
    · have : θ = fun p => c⁻¹ * (c * θ p) := by funext p; field_simp
      rw [this]; exact hm.const_mul _
    · exact (mul_nonneg_iff_of_pos_left hc).mp (hpos p)

theorem orbJ_smul (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μ : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (hrel : Formalism.FourierDecayAlt.C6.IsRelevant D γ)
    (hH : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset γ) μ) {c : ℝ} (hc : 0 < c) :
    Formalism.FourierDecayAlt.D.orbJ D γ (ENNReal.ofReal c • μ) F = ((c⁻¹ : ℝ) : ℂ) • Formalism.FourierDecayAlt.D.orbJ D γ μ F := by
  unfold Formalism.FourierDecayAlt.D.orbJ
  by_cases h1 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ (ENNReal.ofReal c • μ) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS
  · have hc1 := (isNormCut_smul D γ μ hc _).mp h1.choose_spec.1
    have hi1 : Integrable (fun p => (c * h1.choose p) • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS := by
      simp only [mul_smul]; exact h1.choose_spec.2.smul c
    have h2 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS := ⟨_, hc1, hi1⟩
    rw [dif_pos h1, dif_pos h2]
    have hind := Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq D γ μ hrel hH F h2.choose (fun p => c * h1.choose p)
      h2.choose_spec.1 hc1 h2.choose_spec.2 hi1
    rw [hind]
    simp only [mul_smul]
    rw [integral_smul, ← Complex.coe_smul c, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne',
      Complex.ofReal_one, one_smul]
  · have h2 : ¬ ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS := by
      rintro ⟨θ, hθ, hi⟩
      apply h1
      refine ⟨fun p => c⁻¹ * θ p, (isNormCut_smul D γ μ hc _).mpr ?_, ?_⟩
      · have : (fun p => c * (c⁻¹ * θ p)) = θ := by funext p; field_simp
        rw [this]; exact hθ
      · simp only [mul_smul]; exact hi.smul c⁻¹
    rw [dif_neg h1, dif_neg h2, smul_zero]

end Scale

end Formalism.L2.SG.Pf.Bridge
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVtRZero
section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem exists_nonneg_ptG_lptOf_eq_mul (v : InfinitePlace X.B.I.F) (κ : ℂ) (hκ : star κ = -κ) (TT : ℝ)
    (w : Point D.host.E (D.R.rS + 1)) :
    ∃ c : ℝ, 0 ≤ c ∧ Formalism.FourierDecayAlt.D.ptG TT D.R.rS (Bridge.lptOf ((X.B.I.φ v).comp X.ιE.symm.toRingHom) κ D.R.rS 0 w.1) =
      c * (‖RealObj.Dl (RealObj.ZhatO (ptC X v w)) (D.R.rS + 1)‖ ^ 2 -
        TT * ‖RealObj.Dl (RealObj.ZhatO (ptC X v w)) D.R.rS‖ ^ 2) := by
  set σ : D.host.E →+* ℂ := (X.B.I.φ v).comp X.ιE.symm.toRingHom
  set Y := RealObj.ZhatO (ptC X v w)
  have hY : ptC X v w = Matrix.diagonal (fun _ => 1) * Y * Matrix.diagonal (Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS) := by
    rw [← Formalism.L2.SG.Pf.CarrierTop.zhatO_eq_mul, Formalism.L2.SG.Pf.CarrierTop.zhatO_invol]
  have hM : Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1) =
      Matrix.diagonal (fun a : Fin (D.R.rS + 1) => Bridge.Af κ D.R.rS a * 1) * Y *
        Matrix.diagonal (fun b : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS b * Bridge.Bf κ D.R.rS b) := by
    rw [Bridge.ptMatN_lptOf σ κ D.R.rS hκ w]
    show Matrix.diagonal _ * ptC X v w * Matrix.diagonal _ = _
    rw [hY]
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have hdet1 : (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)).det =
      RealObj.Dl (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)) (D.R.rS + 1) :=
    (Bridge.dl_top' _).symm
  have hdet2 : (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) D.R.rS).det =
      RealObj.Dl (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)) D.R.rS := by
    unfold RealObj.Dl; rw [dif_pos (Nat.le_succ _)]; rfl
  have hGd := Bridge.G_diag D.R.rS Y (fun a : Fin (D.R.rS + 1) => Bridge.Af κ D.R.rS a * 1)
    (fun b : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS b * Bridge.Bf κ D.R.rS b) TT
    (by simp [Bridge.Af, Bridge.Bf, Formalism.L2.SG.Pf.CarrierTop.sgnV])
  refine ⟨(‖∏ i : Fin D.R.rS, Bridge.Af κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) * 1‖ *
    ‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) *
      Bridge.Bf κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i)‖) ^ 2, sq_nonneg _, ?_⟩
  unfold Formalism.FourierDecayAlt.D.ptG
  rw [hdet1, hdet2, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hM, hGd]

variable {θ : ℝ} (C : Choice X θ)

theorem rZero_carrierInT (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hPRE : PtRepExists X u u' sc i0 i0') :
    RZero X (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)) u u'
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).fc ν' m₀ := by
  intro p w hp hng

  obtain ⟨v, hv0⟩ : ∃ v, ‖RealObj.Dl (RealObj.ZhatO (ptC X v w)) (D.R.rS + 1)‖ ^ 2 -
      Tw (D := D) u * Tw (D := D) u' * ‖RealObj.Dl (RealObj.ZhatO (ptC X v w)) D.R.rS‖ ^ 2 ≤ 0 := by
    by_cases hrep : ∃ γ, IsPtRep X u u' w γ
    · have h1 : ¬ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v := fun h => hng ⟨hrep, h⟩
      push_neg at h1
      obtain ⟨v, hv1⟩ := h1
      refine ⟨v, ?_⟩
      have hrepw : IsPtRep X u u' w (gamW X u u' w) := by
        unfold gamW; rw [dif_pos hrep]; exact hrep.choose_spec
      have hZ1 : ZX X u u' 1 (gamW X u u' w) v = RealObj.ZhatO (ptC X v w) := by
        rw [← hrepw v, Formalism.L2.SG.Pf.CarrierTop.zhatO_invol]
      change Gv (Tw (D := D) u) (Tw (D := D) u') (ZX X u u' D.host.rdE (gamW X u u' w) v) ≤ 0 at hv1
      unfold Gv at hv1
      have hcl : Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.last D.R.rS) = 1 := by
        simp [Formalism.L2.SG.Pf.CarrierTop.cS]
      have hGd := Bridge.G_diag D.R.rS (ZX X u u' 1 (gamW X u u' w) v)
        (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE) (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE)
        (Tw (D := D) u * Tw (D := D) u') (by rw [hcl]; simp)
      rw [Formalism.L2.SG.Pf.CarrierTop.zx_sc, hGd, hZ1] at hv1
      by_contra hpos
      push_neg at hpos
      have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
      have hne : (∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by
          simp [Formalism.L2.SG.Pf.CarrierTop.cS, hrd.ne']
      have hc : 0 < (‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)‖ *
          ‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)‖) ^ 2 :=
        pow_pos (mul_pos (norm_pos_iff.mpr hne) (norm_pos_iff.mpr hne)) 2
      have := mul_pos hc hpos
      linarith
    · by_contra hall
      push_neg at hall
      obtain ⟨γ, hγ, -⟩ := hPRE w (fun v => by have := hall v; unfold Gv; exact this)
      exact hrep ⟨γ, hγ⟩
  refine ⟨(tauE X e).symm v, Or.inr ?_⟩
  set j := (tauE X e).symm v with hj
  set σ : D.host.E →+* ℂ := (X.B.I.φ v).comp X.ιE.symm.toRingHom with hσ
  set gg : ℕ := D.host.g 0 * D.host.g 1 with hggdef
  set κ : ℂ := -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ) with hκ
  have hκstar : star κ = -κ := by
    rw [hκ, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]; ring

  have hpt := hp
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList at hpt
  split_ifs at hpt with hPtL
  have hw1 : w.1 = (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.swap := by
    rw [← Option.some_inj.mp hpt]; rfl
  have hfst : (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst = p.map Prod.fst :=
    Formalism.L2.SG.DataInst.sign_list_fst D.R.rS 1 p
  have hblk : ∀ b ∈ p, 1 ≤ b.1 := by
    intro b hb
    have : b.1 ∈ (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst := by
      rw [hfst]; exact List.mem_map_of_mem hb
    obtain ⟨b', hb', hbb⟩ := List.mem_map.mp this
    rw [← hbb]; exact (hPtL.2 b' hb').1
  have hsum : 0 + (p.map Prod.fst).sum ≤ D.R.rS + 1 := by rw [← hfst, hPtL.1]; omega
  have hlt := Bridge.lptOf_toStd σ D.R.rS (gg : ℝ) p 0 hblk hsum
  have hemb : (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j = σ := by
    show embE X e j = σ
    unfold embE
    rw [hj, Equiv.apply_symm_apply]
  have hstd : Formalism.FourierDecayAlt.D.toStd D.R.rS (gg : ℝ) 1
      (Formalism.FourierDecayAlt.C.loc ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j) p) =
      Bridge.lptOf σ κ D.R.rS 0 w.1 := by
    rw [hemb, hw1]; exact hlt.symm
  obtain ⟨cc, hcc, hG⟩ := exists_nonneg_ptG_lptOf_eq_mul X v κ hκstar (((D.mem u).A.T : ℝ) * ((D.mem u').A.T : ℝ)) w
  unfold Formalism.FourierDecayAlt.JC.vecPlace Formalism.FourierDecayAlt.D.vecV
  rw [dif_neg]
  · simp [Formalism.FourierDecayAlt.B.hsVec]
    exact Or.inr rfl
  · rintro ⟨-, hpos⟩
    have hT := (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).hT j
    have hT1 : Formalism.QuantumDeterminants.Tz (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.k
        (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.r
        ((carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T j).base.z = ((D.mem u).A.T : ℝ) :=
      hT.1
    have hT2 : Formalism.QuantumDeterminants.Tz (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.k
        (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.r
        ((carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T j).base.z' = ((D.mem u').A.T : ℝ) :=
      hT.2
    have hpos' : 0 < Formalism.FourierDecayAlt.D.ptG (((D.mem u).A.T : ℝ) * ((D.mem u').A.T : ℝ)) D.R.rS
        (Bridge.lptOf σ κ D.R.rS 0 w.1) := by
      convert hpos using 2
      all_goals first | rfl | exact (congrArg₂ (· * ·) hT1 hT2).symm | exact hstd.symm
    rw [hG] at hpos'
    have hpos := hpos'
    unfold Tw at hv0
    have := mul_nonpos_of_nonneg_of_nonpos hcc hv0
    linarith

end Formalism.L2.SG.Pf.Carrier.CarPinVt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTCoef
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.LocWSOf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

def coef0 (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) :
    MatKR D.R.k D.R.rS → (X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)) :=
  c • Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ'

variable {X C}

def CoefPin (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ))
    (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) : Prop :=
  PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) a ∧
  PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) b ∧
  ⟪bOf hB u τ a, ξ⟫_ℂ * ⟪ξ', bOf hB u' τ b⟫_ℂ = 1 ∧ c ≠ 0

variable (X C)

def fcT (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (u u' : D.what₂.Word)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (c : Fin (nfE D) → ℂ) (j : Fin (nfE D)) :
    Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)) :=
  fun g => coef0 X C u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) (c j)
    (torS (muT D) D.R.k D.R.rS * g * torS (muT D)⁻¹ D.R.k D.R.rS)

theorem fcT_eq (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (u u' : D.what₂.Word)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (c : Fin (nfE D) → ℂ) (j : Fin (nfE D))
    (g : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS) :
    fcT X C e u u' a b ξ ξ' c j g = c j • Formalism.MainNotions.S.Pv.BetaCut.coefM
      (sigB X (Qcs C (e (plE D j))) (Qics C (e (plE D j))) (e (plE D j))) (a j) (b j) (ξ j) (ξ' j) g := by
  simp only [fcT, coef0, Pi.smul_apply, Formalism.MainNotions.S.Pv.BetaCut.coefM, sigB, Qcs, Qics, Matrix.mul_assoc]
  rfl

abbrev carrierInTc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (Formalism.L2.SG.Pf.BaseOf.towersOf X C u u' e j).base.π
      (Formalism.L2.SG.Pf.BaseOf.towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ) : CarrierIn X u u' :=
  carrierInT X C u u' e he hv CA de de' l grid grid1 (fcT X C e u u' a b ξ ξ' cc) c ν' m₀ Θ TP A₀

end Formalism.L2.SG.Pf.CarrierT
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.RowDict Formalism.MainNotions.LeviCoordinates

namespace Formalism.L2.SG.EvalTOntoRep

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def IsContRep (f : L2X X) (φ : X.B.I.GA → ℂ) : Prop :=
  Continuous φ ∧ (∀ γ ∈ X.B.I.GFset, ∀ y, φ (γ * y) = φ y) ∧ ((f : X.B.I.GA → ℂ) =ᵐ[muX X] φ)

theorem eq_zero_of_ae (ψ : X.B.I.GA → ℂ) (hc : Continuous ψ) (hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, ψ (γ * y) = ψ y)
    (h0 : ψ =ᵐ[muX X] 0) : ψ = 0 := by
  have := X.B.sf
  have := X.B.haar
  have := Formalism.L2.SG.Count.muA_isHaar X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  set N : Set X.B.I.GA := {y | ψ y ≠ 0} with hNd
  have hN : IsOpen N := isOpen_ne_fun hc continuous_const
  have hfm : MeasurableSet X.B.fund := X.B.fund_spec.1
  have h1 : X.B.I.muA X.B.μf (N ∩ X.B.fund) = 0 := by
    have h0' : ∀ᵐ y ∂(X.B.I.muA X.B.μf), y ∈ X.B.fund → ψ y = 0 := by
      rw [← ae_restrict_iff' hfm]
      exact h0
    rw [ae_iff] at h0'
    refine measure_mono_null (fun y hy => ?_) h0'
    simp only [Set.mem_setOf_eq, Classical.not_imp]
    exact ⟨hy.2, hy.1⟩
  have hsub : N ⊆ ⋃ γ : rr_GF X.B.I, (fun y => (γ : X.B.I.GA) * y) ⁻¹' (N ∩ X.B.fund) := by
    intro y hy
    obtain ⟨γ, hγ, hγy⟩ := X.B.fund_spec.2.1 y
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_⟩
    refine ⟨?_, hγy⟩
    show ψ (γ * y) ≠ 0
    rw [hinv γ hγ y]
    exact hy
  have h2 : X.B.I.muA X.B.μf N = 0 := by
    refine measure_mono_null hsub (measure_iUnion_null fun γ => ?_)
    rw [measure_preimage_mul]
    exact h1
  have h3 : N = ∅ := (hN.measure_eq_zero_iff (X.B.I.muA X.B.μf)).1 h2
  funext y
  by_contra hne
  have : y ∈ N := hne
  rw [h3] at this
  exact this

theorem contRep_unique {f : L2X X} {φ φ' : X.B.I.GA → ℂ} (h : IsContRep X f φ) (h' : IsContRep X f φ') : φ = φ' := by
  have e := eq_zero_of_ae X (fun y => φ y - φ' y) (h.1.sub h'.1)
    (fun γ hγ y => by simp only [h.2.1 γ hγ y, h'.2.1 γ hγ y])
    ((h.2.2.symm.trans h'.2.2).mono fun y hy => by simp [hy])
  funext y
  exact sub_eq_zero.1 (congrFun e y)

theorem contRep_add {f g : L2X X} {φ ψ : X.B.I.GA → ℂ} (h : IsContRep X f φ) (h' : IsContRep X g ψ) :
    IsContRep X (f + g) (φ + ψ) :=
  ⟨h.1.add h'.1, fun γ hγ y => by simp [h.2.1 γ hγ y, h'.2.1 γ hγ y],
    (Lp.coeFn_add f g).trans (h.2.2.add h'.2.2)⟩

theorem contRep_smul (a : ℂ) {f : L2X X} {φ : X.B.I.GA → ℂ} (h : IsContRep X f φ) :
    IsContRep X (a • f) (a • φ) :=
  ⟨h.1.const_smul a, fun γ hγ y => by simp [h.2.1 γ hγ y], (Lp.coeFn_smul a f).trans (h.2.2.const_smul a)⟩

theorem contRep_zero : IsContRep X 0 0 :=
  ⟨continuous_const, fun _ _ _ => rfl, Lp.coeFn_zero ℂ 2 (muX X)⟩

theorem contRep_reg {f : L2X X} {φ : X.B.I.GA → ℂ} (h : IsContRep X f φ) (y : X.B.I.GA) :
    IsContRep X (X.B.R y f) (fun x => φ (x * y)) := by
  have hm : MemLp φ 2 (muX X) := (Lp.memLp f).ae_eq h.2.2
  have ef : f = hm.toLp φ := Lp.ext (h.2.2.trans hm.coeFn_toLp.symm)
  refine ⟨h.1.comp (continuous_mul_right y), fun γ hγ x => by simp only [mul_assoc, h.2.1 γ hγ], ?_⟩
  rw [ef]
  exact Formalism.L2.SG.EvalTReg.reg_toLp_X X φ h.2.1 hm y

end Formalism.L2.SG.EvalTOntoRep

end
end

