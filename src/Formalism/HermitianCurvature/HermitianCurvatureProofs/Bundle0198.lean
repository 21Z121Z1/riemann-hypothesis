import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChiLIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0190
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0189

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OpNormPiLe
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section norms

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem norm_gpsi (β w : ℂ) : ‖G.psi β w‖ = 1 := by
  unfold G.psi; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _

theorem norm_psiStar (σ : Equiv.Perm (Fin p)) (z z' : Fin (2 * (p + 0 + ρ) + k + 1) → ℂ) (ξ : U.Xi k p 0 ρ σ) :
    ‖U.psiStar k ρ σ z z' ξ‖ = 1 := by
  unfold U.psiStar U.psiH
  rw [norm_mul, norm_mul, norm_star, norm_psi, norm_psi, norm_gpsi, one_mul, one_mul]

theorem opNorm_pi_le (Bs : B.RealPlaceData k ρ Wp Wq) {h : B.Mat k ρ} (hh : h ∈ UWset k ρ Bs.z) : ‖Bs.π h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by rw [Bs.π_unitary h hh v, one_mul])

theorem opNorm_pi'_le (Bs : B.RealPlaceData k ρ Wp Wq) {h : B.Mat k ρ} (hh : h ∈ UWset k ρ Bs.z') : ‖Bs.π' h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by rw [Bs.π'_unitary h hh v, one_mul])

theorem norm_pi_comp (Bs : B.RealPlaceData k ρ Wp Wq) {h : B.Mat k ρ} (hh : h ∈ UWset k ρ Bs.z) (A : Wq →L[ℂ] Wp) :
    ‖(Bs.π h).comp A‖ = ‖A‖ := by
  refine le_antisymm ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (opNorm_pi_le Bs hh) (norm_nonneg A))) ?_
  have hi : h⁻¹ ∈ UWset k ρ Bs.z := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bs.z).inv_mem h hh
  have hu : IsUnit h.det := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bs.z).unit h hh
  have e : A = (Bs.π h⁻¹).comp ((Bs.π h).comp A) := by
    rw [← ContinuousLinearMap.comp_assoc, ← Bs.π_rep.2 _ hi _ hh, Matrix.nonsing_inv_mul _ hu, Bs.π_rep.1]
    rfl
  calc ‖A‖ = ‖(Bs.π h⁻¹).comp ((Bs.π h).comp A)‖ := by rw [← e]
    _ ≤ ‖Bs.π h⁻¹‖ * ‖(Bs.π h).comp A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖(Bs.π h).comp A‖ := mul_le_mul_of_nonneg_right (opNorm_pi_le Bs hi) (norm_nonneg _)
    _ = ‖(Bs.π h).comp A‖ := one_mul _

theorem sgs_mem {P : B.SS k ρ} (Bs : B.RealPlaceData k ρ Wp Wq) (hP : Bs.inSS P) {g : B.Mat k ρ} (hg : g ∈ B.GV k ρ) :
    B.sgs P g ∈ B.GV k ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := hP
  have cG := Formalism.FourierDecayAlt.P.unitary_group_closed k ρ
  unfold B.sgs
  have g1 : (Matrix.of P.1.1 : B.Mat k ρ) ∈ B.GV k ρ := h1.1
  have g2 : (Matrix.of P.1.2 : B.Mat k ρ) ∈ B.GV k ρ := h2.1
  have g3 : (Matrix.of P.2.1 : B.Mat k ρ) ∈ B.GV k ρ := h3.1
  have g4 : (Matrix.of P.2.2 : B.Mat k ρ) ∈ B.GV k ρ := h4.1
  exact cG.mul_mem _ (cG.mul_mem _ (cG.mul_mem _ (cG.mul_mem _ (cG.inv_mem _ g1) _ (cG.inv_mem _ g2)) _ hg) _ g4) _ g3

theorem norm_fl_le (Bj : B.RealPlaceData k ρ Wp Wq) (z0 z0' : Fin (2 * (p + ρ) + k + 1) → ℂ) (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ) (q : B.SS k ρ × U.Xi k p 0 ρ σ)
    (hq : Bj.inSS q.1) :
    ‖FL Bj z0 z0' σ d H g q‖ ≤ ‖H (U.gaXi k ρ σ d q.2 (fun a => a.elim0) (B.sgs q.1 g))‖ := by
  unfold FL
  rw [norm_smul, norm_xiP, one_mul, norm_pi_comp Bj hq.1]
  have hi : (Matrix.of q.1.2.1 : B.Mat k ρ)⁻¹ ∈ UWset k ρ Bj.z' :=
    (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z').inv_mem _ hq.2.2.1
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [norm_smul, norm_psiStar, one_mul]
  simpa using mul_le_mul_of_nonneg_left (opNorm_pi'_le Bj hi) (norm_nonneg (H _))

end norms

section main

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem ae_inSS (Bs : B.RealPlaceData k ρ Wp Wq) : ∀ᵐ P ∂Bs.μSS, Bs.inSS P := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have w1 := Formalism.FourierDecayAlt.P.B5.haar_ae Bs.haarW
  have w2 := Formalism.FourierDecayAlt.P.B5.haar_ae Bs.haarN
  have w3 := Formalism.FourierDecayAlt.P.B5.haar_ae Bs.haarW'
  unfold B.RealPlaceData.μSS
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae w1),
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae w2),
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae w3),
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae w2)] with P a b c e
  exact ⟨a, b, c, e⟩

theorem ae_goodL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) : ∀ᵐ x ∂(muL Bj σ), GoodL Bj σ x := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have w1 := Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarW
  have w2 := Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarN
  unfold muL
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae w1),
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae w2)] with x a b
  exact ⟨a, b⟩

theorem ae_goodR (Bj : B.RealPlaceData k ρ Wp Wq) : ∀ᵐ y ∂(muR (p := p) Bj), GoodR Bj y := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have w1 := Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarW'
  have w2 := Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarN
  unfold muR
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae w1),
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae w2)] with x a b
  exact ⟨a, b⟩

theorem norm_cL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : ‖cL Bj σ x‖ = 1 := by
  unfold cL
  rw [norm_mul, norm_mul, norm_psi, norm_psi, norm_gpsi, one_mul, one_mul]

theorem norm_ellL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) (hx : GoodL Bj σ x)
    (A : Wq →L[ℂ] Wp) : ‖ellL Bj σ x A‖ = ‖A‖ := by
  unfold ellL
  rw [ContinuousLinearMap.smul_apply, norm_smul, norm_cL, one_mul, ContinuousLinearMap.compL_apply,
    norm_pi_comp Bj hx.1]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem core_main (hGS : GaXiSplit) (hPR : PsiRight) (hPA : PsiRnAct) (hPM : PsiMuP) (hRMP : RightMP)
    (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R)
    (hM1 : AEStronglyMeasurable (FL Bj (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') σ d H g)
      (Bj.μSS.prod (U.muXi k p 0 ρ σ)))
    (hM2 : AEStronglyMeasurable (fun q : XL k p ρ σ × XR k p ρ =>
      KrI B0 H (sxL Bj σ q.1 * U.mMap k p ρ (U.hMat σ d) g) (PsiR q.2)) ((muL Bj σ).prod (muR Bj)))
    (hM3 : ∀ x, GoodL Bj σ x →
      AEStronglyMeasurable (KrI B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g)) (B0.μW'.prod B0.μN))
    (hM4 : ∀ γ ∈ B.GV k ρ, Continuous (fun ξ : U.Xi k p 0 ρ σ =>
      U.psiStar k ρ σ (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') ξ • H (U.gaXi k ρ σ d ξ (fun a => a.elim0) γ))) :
    Integrable (fun x => ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g))) (muL Bj σ) ∧
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
      ∫ x, ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g)) ∂(muL Bj σ) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have : SigmaFinite Bj.μSS := by unfold B.RealPlaceData.μSS; infer_instance
  have : SigmaFinite (U.muXi k p 0 ρ σ) := by unfold U.muXi U.muXiH; infer_instance
  have : SigmaFinite (muL Bj σ) := by unfold muL; infer_instance
  have : SigmaFinite (muR (p := p) Bj) := by unfold muR; infer_instance
  have : BorelSpace ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) := Prod.borelSpace
  have : BorelSpace ((U.LW σ → ℂ) × (G.UT p → ℂ)) := Prod.borelSpace
  have : BorelSpace (U.XiH p 0 σ) := Prod.borelSpace
  have : BorelSpace (U.RC k p ρ × U.RC k p ρ) := Prod.borelSpace
  have : BorelSpace (U.Xi k p 0 ρ σ) := Prod.borelSpace
  set x1 := U.mMap k p ρ (U.hMat σ d) g with hx1
  set F := FL Bj (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') σ d H g with hF
  obtain ⟨M, C, R', hM0, hball, hb⟩ := slice_bound hp σ d hd H hHc R hR
  have hgG : g ∈ B.GV k ρ := hg.1
  have hSS := ae_inSS Bj

  have hS1 : ∀ γ ∈ B.GV k ρ, Integrable (fun ξ : U.Xi k p 0 ρ σ =>
      U.psiStar k ρ σ (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') ξ • H (U.gaXi k ρ σ d ξ (fun a => a.elim0) γ))
      (U.muXi k p 0 ρ σ) := by
    intro γ hγ
    refine hball.mono' (hM4 γ hγ).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
    rw [norm_smul, norm_psiStar, one_mul]
    refine (hb ξ _ γ hγ).trans ?_
    have h1 := bumpG_le_one R' γ
    have h2 : 0 ≤ M * (Metric.closedBall (0 : U.Xi k p 0 ρ σ) C).indicator (fun _ => (1 : ℝ)) ξ :=
      mul_nonneg hM0 (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    nlinarith [bumpG_nonneg R' γ]

  have hbi : Integrable (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => bumpG R' (B.sgs q.1 g) *
      (M * (Metric.closedBall (0 : U.Xi k p 0 ρ σ) C).indicator (fun _ => (1 : ℝ)) q.2))
      (Bj.μSS.prod (U.muXi k p 0 ρ σ)) := (bump_int Bj hg R').mul_prod hball
  have hFi : Integrable F (Bj.μSS.prod (U.muXi k p 0 ρ σ)) := by
    refine hbi.mono' hM1 ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hSS] with q hq
    refine (norm_fl_le Bj _ _ σ d H g q hq).trans ((hb q.2 _ _ (sgs_mem Bj hq hgG)).trans (le_of_eq ?_))
    ring

  have hL : B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
      ∫ q, F q ∂(Bj.μSS.prod (U.muXi k p 0 ρ σ)) := by
    rw [integral_prod F hFi]
    show ∫ P, JF.integrand Bj _ g P ∂Bj.μSS = _
    refine integral_congr_ae ?_
    filter_upwards [hSS] with P hP
    have hI := hS1 _ (sgs_mem Bj hP hgG)
    set L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := JF.xiP Bj P •
      ((ContinuousLinearMap.compL ℂ Wq Wp Wp (Bj.π (Matrix.of P.1.1))).comp
        ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (Bj.π' (Matrix.of P.2.1)⁻¹))) with hLdef
    have e1 : ∀ ξ, F (P, ξ) = L (U.psiStar k ρ σ (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') ξ •
        H (U.gaXi k ρ σ d ξ (fun a => a.elim0) (B.sgs P g))) := fun ξ => rfl
    simp_rw [e1]
    rw [L.integral_comp_comm hI]
    rfl

  have hmp := splitE_mp Bj σ
  have hS4 : ∫ q, F q ∂(Bj.μSS.prod (U.muXi k p 0 ρ σ)) =
      ∫ z, F ((splitE σ).symm z) ∂((muL Bj σ).prod (muR Bj)) :=
    ((hmp.symm (splitE σ)).integral_comp' F).symm

  have hgood : ∀ᵐ z ∂((muL Bj σ).prod (muR (p := p) Bj)), GoodL Bj σ z.1 ∧ GoodR Bj z.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_goodL Bj σ),
      Measure.quasiMeasurePreserving_snd.ae (ae_goodR (p := p) Bj)] with z a b
    exact ⟨a, b⟩
  set GRl : XL k p ρ σ × XR k p ρ → (Wq →L[ℂ] Wp) := fun z => ellL Bj σ z.1 (KrI B0 H (sxL Bj σ z.1 * x1) (PsiR z.2))
    with hGRl
  set GR0 : XL k p ρ σ × XR k p ρ → (Wq →L[ℂ] Wp) := fun z => KrI B0 H (sxL Bj σ z.1 * x1) (PsiR z.2) with hGR0
  have hS5 : (fun z => F ((splitE σ).symm z)) =ᵐ[(muL Bj σ).prod (muR Bj)] GRl := by
    filter_upwards [hgood] with z hz
    obtain ⟨x, y⟩ := z
    exact fl_split hGS hPR hPA hPM Bj B0 hz' hπ' σ d H g x y hz.1 hz.2

  have hFi' : Integrable (fun z => F ((splitE σ).symm z)) ((muL Bj σ).prod (muR Bj)) :=
    ((hmp.symm (splitE σ)).integrable_comp_emb (splitE σ).symm.measurableEmbedding).2 hFi
  have hGRli : Integrable GRl ((muL Bj σ).prod (muR Bj)) := hFi'.congr hS5
  have hGR0i : Integrable GR0 ((muL Bj σ).prod (muR Bj)) := by
    refine hGRli.norm.mono' hM2 ?_
    filter_upwards [hgood] with z hz
    rw [hGRl, hGR0]
    simp only
    rw [norm_ellL Bj σ z.1 hz.1]

  have hRM := hRMP k p ρ Bj.z' Bj.μW' B0.μW' Bj.haarW' hW' hW0'
  have hmap : (muR (p := p) Bj).map PsiR = B0.μW'.prod B0.μN := by
    rw [hN0]
    unfold muR
    rw [hNj]
    exact hRM.map_eq
  have hPm : Measurable (PsiR (k := k) (p := p) (ρ := ρ)) := hRM.measurable
  have hS7 : ∀ x, GoodL Bj σ x → PBG.Kr B0 H (sxL Bj σ x * x1) = ∫ y, GR0 (x, y) ∂(muR Bj) := by
    intro x hx
    have hA : AEStronglyMeasurable (KrI B0 H (sxL Bj σ x * x1)) ((muR (p := p) Bj).map PsiR) := by
      rw [hmap]; exact hM3 x hx
    rw [kr_eq_int, ← hmap, integral_map hPm.aemeasurable hA]

  have hS8 : ∀ᵐ x ∂(muL Bj σ), ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * x1)) = ∫ y, GRl (x, y) ∂(muR Bj) := by
    filter_upwards [ae_goodL Bj σ, hGR0i.prod_right_ae] with x hx hxi
    rw [hS7 x hx, ← (ellL Bj σ x).integral_comp_comm hxi]
  refine ⟨hGRli.integral_prod_left.congr (hS8.mono fun x hx => hx.symm), ?_⟩
  rw [integral_congr_ae hS8, ← integral_prod GRl hGRli, ← integral_congr_ae hS5, ← hS4, ← hL]

end main

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OuterInt
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section outer

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]

set_option maxHeartbeats 1000000 in

theorem outer_int (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) (hW1 : S.μW Set.univ = 1)
    (hW1' : S.μW' Set.univ = 1) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hFc : ContinuousOn F (B.GV k r)) (M : ℝ) (Bs : Set (U.Xi k r 0 0 σ)) (hBs : MeasurableSet Bs)
    (hBsf : U.muXi k r 0 0 σ Bs < ⊤)
    (hdom : ∀ (ξ : U.Xi k r 0 0 σ) (γ : B.Mat k 0), γ ∈ B.GV k 0 →
      ‖F (U.gaXi k 0 σ d ξ (fun a => a.elim0) γ)‖ ≤ Bs.indicator (fun _ => M) ξ) :
    Integrable (fun p => theta0 S.z σ.symm p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS ∧
      ∫ p, theta0 S.z σ.symm p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p ∂S.μSS =
        ∫ x, conjL S x.1 x.2 (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
          ((midB r 0 (Matrix.of x.1))⁻¹ * γ0 * midB r 0 (Matrix.of x.2))) ∂(S.μW.prod S.μW') := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hsW : SigmaFinite S.μW := Dx2.OrbJ.sigmaF S.haarW
  have hsW' : SigmaFinite S.μW' := Dx2.OrbJ.sigmaF S.haarW'
  have hfW : IsFiniteMeasure S.μW := ⟨by rw [hW1]; exact ENNReal.one_lt_top⟩
  have hfW' : IsFiniteMeasure S.μW' := ⟨by rw [hW1']; exact ENNReal.one_lt_top⟩
  set γ := U.mMap k r 0 (U.hMat σ d) γ0 with hγ
  have hγG : γ ∈ B.GV k r := by
    have := (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0
    exact this
  set f : B.SS k r → (Wq →L[ℂ] Wp) := fun p => theta0 S.z σ.symm p • D.orbIntegrand S γ F p with hf
  have hfm : AEStronglyMeasurable f S.μSS :=
    (theta0_meas S.z σ.symm).aestronglyMeasurable.smul (Dx3.integrand_aesm S hγG hFc)

  have hSS := muSS_eq S hN
  set P := (S.μW.prod (QN k r)).prod (S.μW'.prod (QN k r)) with hP
  have hfm' : AEStronglyMeasurable f (P.map (TN k r)) := by rw [← hSS]; exact hfm
  have hTm : AEMeasurable (TN k r) P := TN_meas.aemeasurable
  set P2 := (S.μW.prod S.μW').prod ((QN k r).prod (QN k r)) with hP2
  have hsw := Dx2.SL.measurePreserving_prod_middle_swap S.μW (QN k r) S.μW' (QN k r)
  set G2 : (Mt k r × Mt k r) × ((U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ))) → (Wq →L[ℂ] Wp) :=
    fun x => f (TN k r ((x.1.1, x.2.1), (x.1.2, x.2.2))) with hG2
  have hG2e : G2 = (f ∘ TN k r) ∘ (Dx2.SL.swap4 (α := Mt k r) (β := U.RC k r 0 × (G.UT r → ℂ)) (γ := Mt k r)
      (δ := U.RC k r 0 × (G.UT r → ℂ))).symm := by
    funext x; rfl
  have hfTm : AEStronglyMeasurable (f ∘ TN k r) P := hfm'.comp_aemeasurable hTm
  have hG2m : AEStronglyMeasurable G2 P2 := by
    rw [hG2e]
    exact hfTm.comp_measurePreserving (hsw.symm _)

  have hae : ∀ᵐ x ∂(S.μW.prod S.μW'), Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' := by
    have b1 := (Measure.quasiMeasurePreserving_fst (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW)
    have b2 := (Measure.quasiMeasurePreserving_snd (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW')
    filter_upwards [b1, b2] with x h1 h2 using ⟨h1, h2⟩
  have hin := fun x : Mt k r × Mt k r => fun hx : Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' =>
    inner_int S z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom x.1 x.2 hx.1 hx.2
  have hG2i : Integrable G2 P2 := by
    rw [integrable_prod_iff hG2m]
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with x hx using (hin x hx).1
    · refine Integrable.of_bound hG2m.norm.integral_prod_right' (M * (U.muXi k r 0 0 σ Bs).toReal) ?_
      filter_upwards [hae] with x hx
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hin x hx).2.2

  have hfTi : Integrable (f ∘ TN k r) P := by
    have := (hsw.symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := f ∘ TN k r)
    rw [← this, ← hG2e]; exact hG2i
  refine ⟨?_, ?_⟩
  · rw [hSS]; exact (integrable_map_measure hfm' hTm).2 hfTi
  · rw [hSS, integral_map hTm hfm']
    have e := (hsw.symm _).integral_comp' (f ∘ TN k r)
    change ∫ x, (f ∘ TN k r) x ∂P = _
    rw [← e]
    change ∫ x, G2 x ∂P2 = _
    rw [hP2, integral_prod G2 hG2i]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx using (hin x hx).2.1

theorem orbJ_mMap (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) (hW1 : S.μW Set.univ = 1)
    (hW1' : S.μW' Set.univ = 1) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0))
    (w : Equiv.Perm (Fin (r + 1))) (dd : Fin (r + 1) → ℂ) (hdd : ∀ a, dd a ≠ 0)
    (hZw : Zhat k r S.z S.z' (U.mMap k r 0 (U.hMat σ d) γ0) = C2.monoP w dd)
    (hw : ∀ a : Fin r, w.symm a.castSucc = (σ a).castSucc)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hFc : ContinuousOn F (B.GV k r)) (hr : 1 ≤ r) (R : ℝ)
    (hFs : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) :
    D.orbJ S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) F =
      ∫ x, conjL S x.1 x.2 (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
        ((midB r 0 (Matrix.of x.1))⁻¹ * γ0 * midB r 0 (Matrix.of x.2))) ∂(S.μW.prod S.μW') := by
  obtain ⟨M, Bs, hBs, hBsf, hdom⟩ := slice_dom k r hr σ d hd F hFc R hFs
  obtain ⟨hint, heq⟩ := outer_int S hN hW1 hW1' z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom
  have hγG : U.mMap k r 0 (U.hMat σ d) γ0 ∈ B.GV k r :=
    (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0
  have hw' : ∀ a : Fin r, w.symm a.castSucc = (σ.symm.symm a).castSucc := by simpa using hw
  have hnc := theta0_normCut S hγG hdd hZw σ.symm hw'
  have hex : ∃ θ, D.IsNormCut S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) θ ∧
      Integrable (fun p => θ p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS :=
    ⟨_, hnc, hint⟩
  unfold D.orbJ
  rw [dif_pos hex, Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq S _ _ hrel
    (Formalism.FourierDecayAlt.P.radial_measure_is_haar k r Wp Wq S _ w dd hγG hdd hZw) F hex.choose _ hex.choose_spec.1 hnc
    hex.choose_spec.2 hint, heq]

end outer

end Formalism.FourierDecayAlt.P.PBM
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSmoothOfRegularity
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ellw

variable {d : ℕ}

def pdc : List (Fin d) → ((Fin d → ℝ) → ℂ) → (Fin d → ℝ) → ℂ
  | [], u => u
  | i :: w, u => fun x => fderiv ℝ (pdc w u) x (Pi.single i 1)

structure SOp (d : ℕ) where
  ord : ℕ
  a : (k : Fin (ord + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ

def SOp.app (P : SOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x

def SOp.tr (P : SOp d) (φ : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d,
    (-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x

def SOp.symb (P : SOp d) (x ξ : Fin d → ℝ) : ℂ :=
  ∑ w : Fin P.ord → Fin d, (∏ i, (ξ (w i) : ℂ)) * P.a (Fin.last P.ord) w x

end ellw

def EllRegW : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : ι → SOp d) (U : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ),
    IsOpen U → (∀ j k w, ContDiffOn ℝ ∞ ((P j).a k w) U) → ContinuousOn u U →
    (∀ j (φ : (Fin d → ℝ) → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, u x * (P j).tr φ x = 0) →
    (∀ x ∈ U, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → ∃ j, (P j).symb x ξ ≠ 0) →
    ContDiffOn ℝ ∞ u U

def GRegJ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (u u' : ℕ → ℝ) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsType k r D.z D.π u → Q.IsType k r D.z' D.π' u' →
    J ∈ Gr.FFlM ((2 * r + k + 1 : ℕ) : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Q.CV k r (Y : ℂ) J g = c • J g) →
    Q.SmoothLev k r 0 (Q.OmPlus k r D.z D.z') J

theorem transfer_smooth_of_regularity (hR : GRegJ) : JfSmoothBuilt := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  have hce := JfS.class_eigenvalue_constant 100 E Wp Wq S T f χ ν' m₀ top A₀ le_rfl hB v
  obtain ⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩ := hB
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, hCC, _⟩ := hv v
  have hpos : 0 ≤ ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by positivity
  have hA' : 100 * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ := hA
  have hThr : JF.TransportedAlt S.G.k S.G.r A₀ (2 * S.G.r + S.G.k + 1) :=
    Formalism.FourierDecayAlt.P.CutMP.thr_of_budget S.G.k S.G.r (S.Ntop : ℝ) A₀ hk2 (Nat.cast_nonneg _) hA'
  have hF := Gr.jf_mem_FFlM (T v).base A₀ (2 * S.G.r + S.G.k + 1) (f v) hThr (hCC _)
  obtain ⟨_, _, _, _, _, hTy, hTy'⟩ := hplace
  have hS := hR S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base _ _ (B.JF (T v).base (f v)) hTy hTy' hF
    (fun Y => ⟨_, hce.2 Y⟩)
  have hsub : ∀ g, g ∈ Q.Glev S.G.k S.G.r 0 ∩ OmP S T v →
      g ∈ Q.Glev S.G.k S.G.r 0 ∩ Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun g hg => ⟨hg.1, (JfS.mem_om_of_mem_omP S T v hg.1.1 hg.2).2⟩
  obtain ⟨_, hL, hRt, hU⟩ := hF
  refine ⟨fun g₀ hg₀ => hS g₀ (hsub g₀ hg₀), fun g hg n hn => hL g (hsub g hg) n hn,
    fun g hg n hn => hRt g (hsub g hg) n hn, fun g hg h hh h' hh' => hU g (hsub g hg) h hh h' hh'⟩

theorem model_place_of_regularity (hR : GRegJ) (h3 : ModelPlaceBuilt3) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_3' (transfer_smooth_of_regularity hR) h3

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

