import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0108
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0109
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLIsoAlg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvBlock
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Formalism.FourierDecayAlt.P.NFx4.NO

section Curv

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A)

def curvTh0 : A := d.L.ζ * d.L.nab + d.L.ζb * d.L.nabs

def curvK : A := d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) +
    algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))

theorem curv_theta_split : ThetaC d = curvTh0 d + curvK d := by
  unfold ThetaC curvTh0 curvK; abel

theorem curv_fc {x y : A} (hx : x ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A))
    (hy : y ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : Commute x y :=
  d.L.fns_comm x (Or.inr hx) y (Or.inr hy)

theorem curvature_theta_commutator_zeta : curvTh0 d * d.L.ζb = d.L.ζb * curvTh0 d - d.L.ζb := by
  have h1 : Commute d.L.ζ d.L.ζb := curv_fc d (by simp) (by simp)
  unfold curvTh0
  simp only [add_mul, mul_add, mul_assoc, d.L.nab_ζb, d.L.nabs_ζb, mul_sub, mul_one]
  rw [h1.left_comm]
  abel

theorem curvature_theta_commutes_G : curvTh0 d * d.L.GG = d.L.GG * curvTh0 d := by
  have h1 : Commute d.L.ζ d.L.ζb := curv_fc d (by simp) (by simp)
  have h2 : Commute d.L.ζ d.L.GG := curv_fc d (by simp) (by simp)
  have h3 : Commute d.L.ζb d.L.GG := curv_fc d (by simp) (by simp)
  unfold curvTh0
  simp only [add_mul, mul_add, mul_assoc, d.L.nab_GG, d.L.nabs_GG, mul_sub]
  rw [h2.left_comm, h3.left_comm, h1.eq]
  abel

theorem curvature_theta_commutator_nabla : curvTh0 d * d.L.nab =
    d.L.nab * curvTh0 d - d.L.nab + d.L.ζb * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) := by
  have e1 : ∀ X : A, d.L.nab * (d.L.ζ * X) = d.L.ζ * (d.L.nab * X) + X := fun X => by
    rw [← mul_assoc, d.L.nab_ζ, add_mul, one_mul, mul_assoc]
  have e2 : ∀ X : A, d.L.nab * (d.L.ζb * X) = d.L.ζb * (d.L.nab * X) := fun X => by
    rw [← mul_assoc, d.L.nab_ζb, mul_assoc]
  unfold curvTh0
  simp only [add_mul, mul_add, mul_assoc, e1, e2, mul_sub]
  abel

theorem curv_K_comm (hRel : d.Rel) {g : A} (hg : g ∈ ({d.L.ζb, d.L.GG} : Set A)) : curvK d * g = g * curvK d := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  have hg' : g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A) := by rcases hg with rfl | rfl <;> simp
  have hk : ∀ f : M.Ty P → ℂ, Commute (d.κ f) g := fun f => kap_comm_fn hRel f (Or.inl (Or.inr hg'))
  have hGi : Commute d.L.GGi g := curv_fc d (by simp) hg'
  have ha : Commute (algebraMap ℂ A (P.TT : ℂ)) g := Algebra.commute_algebraMap_left _ _
  exact ((hk _).add_left ((ha.mul_left hGi).mul_left (hk _))).eq

theorem curv_K_nab (hRel : d.Rel) : curvK d * d.L.nab = d.L.nab * curvK d +
    algebraMap ℂ A (P.TT : ℂ) * d.L.ζb * d.L.GGi * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) := by
  have hk : ∀ f : M.Ty P → ℂ, Commute (d.κ f) d.L.nab := fun f => kap_comm_fn hRel f (Or.inr (by simp))
  have ha : Commute (algebraMap ℂ A (P.TT : ℂ)) d.L.nab := Algebra.commute_algebraMap_left _ _
  have hζ : Commute (algebraMap ℂ A (P.TT : ℂ)) d.L.ζb := Algebra.commute_algebraMap_left _ _
  unfold curvK
  rw [add_mul, mul_add, (hk _).eq]
  have : algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) * d.L.nab =
      d.L.nab * (algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))) +
      algebraMap ℂ A (P.TT : ℂ) * d.L.ζb * d.L.GGi * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) := by
    rw [mul_assoc _ _ d.L.nab, (hk _).eq, ← mul_assoc, mul_assoc _ d.L.GGi d.L.nab]
    rw [show d.L.nab * (algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))) =
      algebraMap ℂ A (P.TT : ℂ) * (d.L.nab * d.L.GGi) * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) by
        rw [← mul_assoc, ← mul_assoc, ← ha.eq]; simp only [mul_assoc]]
    rw [d.L.nab_GGi]
    rw [show d.L.GGi * d.L.nab = (d.L.GGi * d.L.nab - d.L.ζb * d.L.GGi * d.L.GGi) + d.L.ζb * d.L.GGi * d.L.GGi by abel]
    simp only [mul_add, add_mul, mul_assoc]
    rw [← mul_assoc (algebraMap ℂ A (P.TT : ℂ)) d.L.ζb, hζ.eq]
    simp only [mul_assoc]
    abel
  rw [this]
  abel

theorem curv_kap_theta (hRel : d.Rel) (f : M.Ty P → ℂ) : Commute (d.κ f) (ThetaC d) := by
  have hf : ∀ g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}, Commute (d.κ f) g := fun g hg => kap_comm_fn hRel f hg
  have hz : Commute (d.κ f) d.L.ζ := hf _ (Or.inl (by simp [R.LevelData.fns]))
  have hzb : Commute (d.κ f) d.L.ζb := hf _ (Or.inl (by simp [R.LevelData.fns]))
  have hGi : Commute (d.κ f) d.L.GGi := hf _ (Or.inl (by simp [R.LevelData.fns]))
  have hn : Commute (d.κ f) d.L.nab := hf _ (Or.inr (by simp))
  have hns : Commute (d.κ f) d.L.nabs := hf _ (Or.inr (by simp))
  have hkk : ∀ h : M.Ty P → ℂ, Commute (d.κ f) (d.κ h) := fun h => by
    show d.κ f * d.κ h = d.κ h * d.κ f
    rw [← map_mul, ← map_mul, mul_comm]
  unfold ThetaC
  exact (((hz.mul_right hn).add_right (hzb.mul_right hns)).add_right (hkk _)).add_right
    (((Algebra.commute_algebraMap_right _ _).mul_right hGi).mul_right (hkk _))

theorem curv_theta_zb (hRel : d.Rel) : ThetaC d * d.L.ζb = d.L.ζb * ThetaC d - d.L.ζb := by
  rw [curv_theta_split, add_mul, curvature_theta_commutator_zeta, curv_K_comm d hRel (by simp), mul_add]; abel

theorem curv_theta_GG (hRel : d.Rel) : ThetaC d * d.L.GG = d.L.GG * ThetaC d := by
  rw [curv_theta_split, add_mul, curvature_theta_commutes_G, curv_K_comm d hRel (by simp), mul_add]

theorem curv_theta_nab (hRel : d.Rel) : ThetaC d * d.L.nab = d.L.nab * ThetaC d - d.L.nab +
    d.L.ζb * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) +
    algebraMap ℂ A (P.TT : ℂ) * d.L.ζb * d.L.GGi * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) := by
  rw [curv_theta_split, add_mul, curvature_theta_commutator_nabla, curv_K_nab d hRel, mul_add]; abel

theorem GG_mul_l0_eq (Y : ℂ) : d.L.GG * d.L.l0 Y = -(d.L.GG * d.L.nab) - algebraMap ℂ A (Y + 1 / 2) * d.L.ζb := by
  have h3 : Commute d.L.GG d.L.ζb := curv_fc d (by simp) (by simp)
  have ha : Commute d.L.GG (algebraMap ℂ A (Y + 1 / 2)) := Algebra.commute_algebraMap_right _ _
  unfold R.LevelData.l0
  rw [mul_sub, mul_neg, ← mul_assoc, ha.eq, mul_assoc, ← mul_assoc d.L.GG, h3.eq, mul_assoc, d.L.GG_GGi, mul_one]

theorem curv_key (hRel : d.Rel) (Y : ℂ) :
    ThetaC d * (d.L.GG * d.L.l0 Y) - d.L.GG * d.L.l0 Y * ThetaC d + d.L.GG * d.L.l0 Y =
      -(d.L.GG * (d.L.ζb * ((d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) +
        algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))))) := by
  have hzbT : Commute d.L.ζb (algebraMap ℂ A (P.TT : ℂ)) := Algebra.commute_algebraMap_right _ _
  have r1 : ThetaC d * (d.L.GG * d.L.nab) = d.L.GG * (ThetaC d * d.L.nab) := by
    rw [← mul_assoc, curv_theta_GG d hRel, mul_assoc]
  have r2 : ThetaC d * (algebraMap ℂ A (Y + 1 / 2) * d.L.ζb) =
      algebraMap ℂ A (Y + 1 / 2) * (ThetaC d * d.L.ζb) := by
    rw [← mul_assoc, (Algebra.commute_algebraMap_right (Y + 1 / 2) (ThetaC d)).eq, mul_assoc]
  rw [GG_mul_l0_eq]
  simp only [mul_neg, neg_mul, mul_sub, sub_mul, r1, r2, curv_theta_nab d hRel, curv_theta_zb d hRel]
  simp only [mul_add, mul_sub, mul_assoc]
  rw [← mul_assoc d.L.ζb (algebraMap ℂ A (P.TT : ℂ)), hzbT.eq]
  simp only [mul_assoc]
  abel

theorem curvature_block_form_holds : GTCCurvBlock := by
  intro P A _ _ _ d hRel hc ρ
  have hκ : d.κ (dTy P ρ) = Pj d ρ := rfl
  rw [hκ]
  set Pp := Pj d ρ with hPp
  have hΘ : Pp * ThetaC d = ThetaC d * Pp := comm_Pj_of d (curv_kap_theta d hRel) ρ
  have hGGP : Pp * d.L.GG = d.L.GG * Pp := comm_Pj_of d (fun f => kap_GG hRel f) ρ
  have hl0P : Pp * d.L.l0 Complex.I = d.L.l0 Complex.I * Pp := comm_Pj_of d (fun f => kappa_commute_l0 hRel f _) ρ
  have hPP : Pp * Pp = Pp := Pj_idem d ρ
  have hx : M.xC P ρ Complex.I ≠ 0 := by
    unfold M.xC
    rw [Finset.prod_ne_zero_iff]
    intro i _ h
    have := congrArg Complex.im h
    simp at this
  have hPt : Pp * d.QQ Complex.I 1 0 * Pp = M.xC P ρ Complex.I • (d.L.GG * d.L.l0 Complex.I * Pp) := by
    rw [normal_form_lower_left, mul_add, add_mul, lower_sum_diagonal_zero hRel, add_zero]
    rw [← mul_assoc Pp, ← mul_assoc Pp, hGGP, mul_assoc d.L.GG Pp, Q.NFData.x, hPp, Pj_kap, ← hPp]
    rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
    congr 1
    simp only [mul_assoc]
    rw [← mul_assoc Pp, hl0P, mul_assoc, hPP]
  set W := d.L.GG * d.L.l0 Complex.I with hW
  have hv : Pp * (ThetaC d * d.QQ Complex.I 1 0 - d.QQ Complex.I 1 0 * ThetaC d) * Pp =
      Pp * (-d.QQ Complex.I 1 0) * Pp := by rw [hc]
  have e1 : Pp * (ThetaC d * d.QQ Complex.I 1 0 - d.QQ Complex.I 1 0 * ThetaC d) * Pp =
      ThetaC d * (Pp * d.QQ Complex.I 1 0 * Pp) - (Pp * d.QQ Complex.I 1 0 * Pp) * ThetaC d := by
    rw [mul_sub, sub_mul]
    congr 1
    · rw [← mul_assoc, hΘ]; simp only [mul_assoc]
    · simp only [mul_assoc]; rw [← hΘ]
  rw [e1, mul_neg, neg_mul, hPt] at hv
  have hv2 : M.xC P ρ Complex.I • ((ThetaC d * W - W * ThetaC d + W) * Pp) = 0 := by
    have : (ThetaC d * W - W * ThetaC d + W) * Pp = ThetaC d * (W * Pp) - W * Pp * ThetaC d + W * Pp := by
      rw [add_mul, sub_mul, mul_assoc, mul_assoc W, mul_assoc W, ← hΘ]
    rw [mul_smul_comm, smul_mul_assoc] at hv
    rw [this, smul_add, smul_sub, hv]
    abel
  have hv3 : (ThetaC d * W - W * ThetaC d + W) * Pp = 0 := by
    have := congrArg (fun z => (M.xC P ρ Complex.I)⁻¹ • z) hv2
    simpa only [smul_smul, inv_mul_cancel₀ hx, one_smul, smul_zero] using this
  rw [hW, curv_key d hRel, neg_mul, neg_eq_zero] at hv3
  set C := d.L.nabs * d.L.nab - d.L.nab * d.L.nabs
  have hκP : d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) * Pp = ((-2 * M.aC P ρ : ℝ) : ℂ) • Pp := by
    rw [hPp, kap_Pj]
  have hv4 : C * Pp + algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.L.GGi * (((-2 * M.aC P ρ : ℝ) : ℂ) • Pp) = 0 := by
    have e : d.L.ζbi * (d.L.GGi * (d.L.GG * (d.L.ζb * (C + algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.L.GGi *
        d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)))) * Pp)) = 0 := by
      rw [hv3, mul_zero, mul_zero]
    rw [← e]
    simp only [mul_assoc]
    rw [← mul_assoc d.L.GGi d.L.GG, d.L.GGi_GG, one_mul, ← mul_assoc d.L.ζbi d.L.ζb, d.L.ζbi_ζb, one_mul]
    rw [add_mul]
    simp only [mul_assoc]
    rw [hκP]
  have hfin : C * Pp = -(algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.L.GGi * (((-2 * M.aC P ρ : ℝ) : ℂ) • Pp)) :=
    eq_neg_of_add_eq_zero_left hv4
  rw [hfin, mul_smul_comm]
  simp only [mul_assoc]
  rw [← Algebra.smul_def, ← Algebra.smul_def, smul_smul, ← neg_smul]
  congr 1
  push_cast
  ring

end Curv

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvTop
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem thetaC_eq_thetaNF {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A)
    (hTT : d.L.TT = (P.TT : ℂ)) : ThetaC d = ThetaNF P d := by
  unfold ThetaC ThetaNF
  rw [hTT]
  congr 3
  funext ρ
  rw [aC_eq]
  push_cast
  ring

theorem gTRTopNF_of_curvPoly (h : GTCCurvPoly) : GTRTopNF := by
  intro P A _ _ _ d _ hk _ hRel hTT
  obtain ⟨⟨a, ha⟩, -⟩ := h P A d hRel hk hTT
  have hk1 : P.k - 1 + 1 = P.k := by omega
  refine ⟨fun j => if j = P.k + 1 then 1 else if j = P.k then ThetaC d else if j < P.k then a j else 0,
    fun Y => ?_, 0, ?_⟩
  · have e := ha Y
    rw [hk1] at e
    dsimp only at e ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [show P.k ≠ P.k + 1 by omega, ↓reduceIte]
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [if_neg (by have := Finset.mem_range.1 hj; omega), if_neg (by have := Finset.mem_range.1 hj; omega),
        if_pos (Finset.mem_range.1 hj)]), ← e]
    abel
  · simp only [show P.k ≠ P.k + 1 by omega, if_false, if_true, Int.cast_zero, zero_smul, add_zero]
    exact thetaC_eq_thetaNF d hTT

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

namespace AsmPf

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  ext i
  simp [B.hsVec]

theorem base (hR : GLRight) (hLf : GLLeft) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k)
    (hF : Gauge.IsFrameB P Bs e)
    (hQQ : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
        MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
          MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ)
    (ζ : ℂ) (hζ : P.TT < Complex.normSq ζ) (ρ : M.Ty P) (Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (hFr : Q.IsFrameOf P.k P.r [Bs.z, SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ] Fr) (w : ℂ) (x : Wq) :
    Q.capRep P.k P.r Bs.π Fr w (e ρ ζ x) = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • e ρ ζ x := by
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  obtain ⟨hFr', hpass⟩ := hLf Wp Wq P Bs hpl hk ζ hζ Fr hFr
  have hq : ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  obtain ⟨-, hg, hG⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hEx := Gauge.GC.lie_existence_of_iso_group Gauge.GC.KLIso.lie_algebra_isomorphism_holds Gauge.GC.lie_group_realization
  obtain ⟨E, hEfib, hEeig, hE0⟩ := hEx Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk _ hg hG.ne' _ hFr' ρ
  have hEF : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ :=
    fun p hp => hEfib p.1 hp.1 p.2 hp.2.1 hp.2.2
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hEc : ∀ (Y : ℂ) (v : Wq), E (Q.capRep P.k P.r Bs.π'
      (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) (Y + ((P.k : ℂ) - 2) / 2) v) = M.xC P ρ Y • E v := by
    intro Y v
    rw [hgl']
    exact hEeig Y v
  obtain ⟨Y₀, hY₀⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hOK
  have horth : ∀ σ, σ ≠ ρ → inner ℂ (B.hsVec (e σ ζ)) (B.hsVec E) = 0 := by
    intro σ hσ
    have h := hR Wp Wq P Bs e hpl hk hF hQQ ζ hζ _ hFr' E hEF Y₀ (M.xC P ρ (Y₀ : ℂ) • E)
      (fun v => by rw [hEc, ContinuousLinearMap.smul_apply]) σ
    rw [hsVec_smul, inner_smul_right] at h
    have h2 : (M.xC P ρ (Y₀ : ℂ) - M.xC P σ (Y₀ : ℂ)) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec E) = 0 := by
      rw [sub_mul, h, sub_self]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (hY₀ (sub_eq_zero.1 h3)).symm hσ
    · exact h3
  have hexp := (hF.2 ζ hζ).2.2 E hEF
  have hE1 : E = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec E) • e ρ ζ := by
    conv_lhs => rw [hexp]
    rw [Finset.sum_eq_single ρ (fun σ _ hσ => by rw [horth σ hσ, zero_smul])
      (fun h => absurd (Finset.mem_univ ρ) h)]
  have hc0 : inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec E) ≠ 0 := by
    intro h0
    apply hE0
    rw [hE1, h0, zero_smul]
  have heig : ∀ (Y : ℂ) (v : Wq), e ρ ζ (Q.capRep P.k P.r Bs.π'
      (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) (Y + ((P.k : ℂ) - 2) / 2) v) = M.xC P ρ Y • e ρ ζ v := by
    intro Y v
    have h := hEc Y v
    generalize hcdef : inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec E) = c at hE1 hc0
    rw [hE1] at h
    simp only [ContinuousLinearMap.smul_apply] at h
    rw [smul_comm (M.xC P ρ Y) c] at h
    exact smul_right_injective Wp hc0 h
  rw [hpass (e ρ ζ) ((hF.2 ζ hζ).1 ρ) w x]
  have hw : w = (w - ((P.k : ℂ) - 2) / 2) + ((P.k : ℂ) - 2) / 2 := by ring
  conv_lhs => rw [hw]
  exact heig _ x

end AsmPf

theorem gaugeLines_of_cut : GaugeLinesOfCut := by
  intro hR hL Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ v e hH hk ζ hζ ρ Fr hFr w x
  obtain ⟨hB, hFrame, -, hQQ⟩ := hH
  have hpl := (hB.1.2.2.2.1.2 v).2.2.2.1
  exact AsmPf.base hR hL (D.parOf S v) (T v).base e hpl hk hFrame hQQ ζ hζ ρ Fr hFr w x

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRAlgSS
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem up_ne (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {π ρ : M.Ty P} (h : M.Up P l π ρ) :
    ρ ≠ π := by
  rintro rfl
  rw [Finset.mem_Icc] at hl
  have h1 := h ⟨l - 1, by omega⟩
  have h2 : l - 1 + 1 = l := by omega
  simp [h2] at h1

theorem up_idx (P : M.Par) {j l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {π ρ : M.Ty P} (h : M.Up P l π ρ)
    (h' : M.Up P j π ρ) : j = l := by
  rw [Finset.mem_Icc] at hl
  have h1 := h ⟨l - 1, by omega⟩
  have h3 := h' ⟨l - 1, by omega⟩
  have h2 : l - 1 + 1 = l := by omega
  by_contra hne
  have hne' : ¬ l = j := fun e => hne e.symm
  simp only [h2, if_true, hne', if_false] at h1 h3
  omega

theorem up_det (P : M.Par) {j : ℕ} {σ σ' ρ : M.Ty P} (h : M.Up P j σ σ') (h' : M.Up P j σ ρ) : σ' = ρ := by
  funext i
  apply Fin.ext
  rw [h i, h' i]

theorem algebraic_shift_holds : AlgSS := by
  intro P 𝒜 _ _ _ d hR l hl π ρ hUp Y
  obtain ⟨-, hκ, -, hSS, -, -⟩ := hR
  have hne := up_ne P hl hUp
  have hmul : ∀ f : M.Ty P → ℂ, d.κ f * d.κ (Pi.single π 1) = f π • d.κ (Pi.single π 1) := by
    intro f
    rw [← map_mul, ← map_smul]
    congr 1
    funext σ
    by_cases h : σ = π
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have h0 : d.κ (Pi.single ρ 1) * d.κ (Pi.single π 1) = 0 := by
    rw [hmul, Pi.single_eq_of_ne hne.symm, zero_smul]
  have cGG : Commute (d.κ (Pi.single ρ 1)) d.L.GG := hκ _ _ (by simp [R.LevelData.fns])
  have cl0 : Commute (d.κ (Pi.single π 1)) (d.L.l0 Y) := by
    unfold R.LevelData.l0
    refine Commute.sub_right (Commute.neg_right (hκ _ _ (by simp))) (Commute.mul_right
      (Algebra.commute_algebraMap_right _ _) (Commute.mul_right (hκ _ _ (by simp [R.LevelData.fns]))
        (hκ _ _ (by simp [R.LevelData.fns]))))
  have t1 : d.κ (Pi.single ρ 1) * (d.L.GG * d.x Y * d.L.l0 Y) * d.κ (Pi.single π 1) = 0 := by
    have e : d.κ (Pi.single ρ 1) * (d.L.GG * d.x Y * d.L.l0 Y) * d.κ (Pi.single π 1) =
        d.L.GG * (d.κ (Pi.single ρ 1) * (d.x Y * d.κ (Pi.single π 1))) * d.L.l0 Y := by
      calc d.κ (Pi.single ρ 1) * (d.L.GG * d.x Y * d.L.l0 Y) * d.κ (Pi.single π 1)
          = (d.κ (Pi.single ρ 1) * d.L.GG) * d.x Y * (d.L.l0 Y * d.κ (Pi.single π 1)) := by
            simp only [mul_assoc]
        _ = (d.L.GG * d.κ (Pi.single ρ 1)) * d.x Y * (d.κ (Pi.single π 1) * d.L.l0 Y) := by
            rw [cGG.eq, cl0.eq]
        _ = _ := by simp only [mul_assoc]
    rw [e, Q.NFData.x, hmul, mul_smul_comm, h0, smul_zero, mul_zero, zero_mul]
  have t2 : ∀ j ∈ Finset.Icc 1 (P.k - 1),
      d.κ (Pi.single ρ 1) * (d.SS j * d.κ fun σ => M.xEx P {j} σ Y) * d.κ (Pi.single π 1) =
        if j = l then M.xEx P {j} π Y • (d.SS j * d.κ (Pi.single π 1)) else 0 := by
    intro j _
    have hs := hSS j (fun σ => if M.Up P j σ ρ then 1 else 0) (Pi.single ρ 1) (by
      intro σ σ' h
      by_cases hσ : σ' = ρ
      · subst hσ; simp [h]
      · rw [Pi.single_eq_of_ne hσ, if_neg]
        intro h'
        exact hσ (up_det P h h'))
    calc d.κ (Pi.single ρ 1) * (d.SS j * d.κ fun σ => M.xEx P {j} σ Y) * d.κ (Pi.single π 1)
        = (d.κ (Pi.single ρ 1) * d.SS j) * ((d.κ fun σ => M.xEx P {j} σ Y) * d.κ (Pi.single π 1)) := by
          simp only [mul_assoc]
      _ = M.xEx P {j} π Y • (d.SS j * ((d.κ fun σ => if M.Up P j σ ρ then 1 else 0) * d.κ (Pi.single π 1))) := by
          rw [hs, hmul, mul_smul_comm, mul_assoc]
      _ = M.xEx P {j} π Y • (d.SS j * ((if M.Up P j π ρ then (1 : ℂ) else 0) • d.κ (Pi.single π 1))) := by
          rw [hmul]
      _ = _ := by
          by_cases hjl : j = l
          · subst hjl; simp [hUp]
          · have hn : ¬ M.Up P j π ρ := fun h => hjl (up_idx P hl hUp h)
            simp [hn, hjl]
  have hQ : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  rw [hQ, mul_add, add_mul, t1, zero_add, Q.NFData.weightedSumBis, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl t2, Finset.sum_ite_eq', if_pos hl]

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

