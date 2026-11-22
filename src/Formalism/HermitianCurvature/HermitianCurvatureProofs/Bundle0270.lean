import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0265
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0154
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.FormalDegreeBessel.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0062
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbEquiv2
section
open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbEquiv

section clm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

theorem integral_clm_leftInv (L M : E →L[ℂ] E) (hML : ∀ v, M (L v) = v) (f : α → E) :
    ∫ x, L (f x) ∂μ = L (∫ x, f x ∂μ) := by
  by_cases hf : Integrable f μ
  · exact L.integral_comp_comm hf
  · have hLf : ¬ Integrable (fun x => L (f x)) μ := by
      intro h
      apply hf
      have := M.integrable_comp h
      simpa [hML] using this
    rw [integral_undef hf, integral_undef hLf, map_zero]

end clm

section ops

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def post (A : Wp →L[ℂ] Wp) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wp Wp A

def pre (B' : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B'

theorem post_apply (A : Wp →L[ℂ] Wp) (f : Wq →L[ℂ] Wp) : post A f = A.comp f := rfl

theorem pre_apply (B' : Wq →L[ℂ] Wq) (f : Wq →L[ℂ] Wp) : pre B' f = f.comp B' := rfl

end ops

section homeo

variable {k r : ℕ}

def conjHomeo (a : B.Mat k r) (ha : IsUnit a.det) : Mt k r ≃ₜ Mt k r where
  toFun x := a * Matrix.of x * a⁻¹
  invFun x := a⁻¹ * Matrix.of x * a
  left_inv x := by
    show a⁻¹ * (a * Matrix.of x * a⁻¹) * a = x
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ ha, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha,
      Matrix.one_mul]; rfl
  right_inv x := by
    show a * (a⁻¹ * Matrix.of x * a) * a⁻¹ = x
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha,
      Matrix.one_mul]; rfl
  continuous_toFun := by
    show Continuous fun x : Mt k r => a * Matrix.of x * a⁻¹
    exact (Continuous.matrix_mul continuous_const continuous_id).matrix_mul continuous_const
  continuous_invFun := by
    show Continuous fun x : Mt k r => a⁻¹ * Matrix.of x * a
    exact (Continuous.matrix_mul continuous_const continuous_id).matrix_mul continuous_const

end homeo

section kr

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [CompleteSpace Wp]

theorem unit_of_uw {z : Fin (2 * r + k + 1) → ℂ} {w : B.Mat k r} (hw : w ∈ UWset k r z) : IsUnit w.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hw.1

theorem kr_right_uw (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x w : B.Mat k r)
    (hw : w ∈ UWset k r Bs.z') : PBG.Kr Bs F (x * w) = (PBG.Kr Bs F x).comp (Bs.π' w) := by
  have hU := unit_of_uw hw
  have hwi : w⁻¹ ∈ UWset k r Bs.z' := LieBracketMultiplication.uw_inv hw
  have := PBG.sigmaFinite_of_haar Bs.haarN
  have := PBG.sigmaFinite_of_haar Bs.haarW'
  set e1 := (PBG.lmulHomeo w hU).toMeasurableEquiv
  set e2 := (conjHomeo w hU).toMeasurableEquiv
  set Φ : Mt k r × Mt k r ≃ᵐ Mt k r × Mt k r := MeasurableEquiv.prodCongr e1 e2
  have hmp1 : MeasurePreserving e1 Bs.μW' Bs.μW' := by
    refine ⟨e1.measurable, ?_⟩
    have ee : ⇑e1 = lmulM w := by funext x; rfl
    rw [ee]; exact Bs.haarW'.left w hw
  have hmp2 : MeasurePreserving e2 Bs.μN Bs.μN := by
    refine ⟨e2.measurable, ?_⟩
    have ee : ⇑e2 = conjM w := by funext x; rfl
    rw [ee]; exact Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r Bs.z' Bs.μN Bs.z'_mem Bs.T'_pos Bs.haarN w hw
  have hmp : MeasurePreserving Φ (Bs.μW'.prod Bs.μN) (Bs.μW'.prod Bs.μN) := hmp1.prod hmp2
  set f : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p => star (psi k r Bs.z' cStd (Matrix.of p.2)) •
      (F (x * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹)
  set g : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p => star (psi k r Bs.z' cStd (Matrix.of p.2)) •
      (F (x * w * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹)
  have hK1 : PBG.Kr Bs F x = ∫ p, f (Φ p) ∂(Bs.μW'.prod Bs.μN) := (hmp.integral_comp' f).symm
  have hae : ∀ᵐ p ∂(Bs.μW'.prod Bs.μN), (Matrix.of p.1 : B.Mat k r) ∈ UWset k r Bs.z' :=
    Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B5.haar_ae Bs.haarW')
  have hK2 : ∫ p, f (Φ p) ∂(Bs.μW'.prod Bs.μN) = ∫ p, pre (Bs.π' w⁻¹) (g p) ∂(Bs.μW'.prod Bs.μN) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    have hpsi : psi k r Bs.z' cStd (w * Matrix.of p.2 * w⁻¹) = psi k r Bs.z' cStd (Matrix.of p.2) := by
      have := Formalism.FourierDecayAlt.P.PBM.psi_conj_UW Bs.z' cStd w⁻¹ hwi (Matrix.of p.2)
      rwa [Matrix.nonsing_inv_nonsing_inv _ hU] at this
    have hmat : x * (w * Matrix.of p.2 * w⁻¹) * (w * Matrix.of p.1) = x * w * Matrix.of p.2 * Matrix.of p.1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc w⁻¹ w, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
    have hpi : Bs.π' (w * Matrix.of p.1)⁻¹ = (Bs.π' (Matrix.of p.1)⁻¹).comp (Bs.π' w⁻¹) := by
      rw [Matrix.mul_inv_rev]
      exact Bs.π'_rep.2 _ (LieBracketMultiplication.uw_inv hp) _ hwi
    show star (psi k r Bs.z' cStd (w * Matrix.of p.2 * w⁻¹)) •
        (F (x * (w * Matrix.of p.2 * w⁻¹) * (w * Matrix.of p.1))).comp (Bs.π' (w * Matrix.of p.1)⁻¹) = _
    rw [hpsi, hmat, hpi, pre_apply, ContinuousLinearMap.smul_comp]
    rfl
  have hML : ∀ v : Wq →L[ℂ] Wp, pre (Bs.π' w) (pre (Bs.π' w⁻¹) v) = v := by
    intro v
    rw [pre_apply, pre_apply, ContinuousLinearMap.comp_assoc, ← Bs.π'_rep.2 _ hwi _ hw,
      Matrix.nonsing_inv_mul _ hU, Bs.π'_rep.1]
    rfl
  have hK3 : PBG.Kr Bs F x = (PBG.Kr Bs F (x * w)).comp (Bs.π' w⁻¹) := by
    rw [hK1, hK2, integral_clm_leftInv _ _ hML]
    rfl
  rw [hK3, ContinuousLinearMap.comp_assoc, ← Bs.π'_rep.2 _ hwi _ hw, Matrix.nonsing_inv_mul _ hU, Bs.π'_rep.1]
  rfl

end kr

section pb

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [CompleteSpace Wp]

theorem pbF_right_uw (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (g w : B.Mat k n) (hw : w ∈ UWset k n B0.z') :
    PBQ.pbF Bj B0 e H (g * w) = (PBQ.pbF Bj B0 e H g).comp (B0.π' w) := by
  have hU := unit_of_uw hw
  have hwi : w⁻¹ ∈ UWset k n B0.z' := LieBracketMultiplication.uw_inv hw
  have hML : ∀ v : Wq →L[ℂ] Wp, pre (B0.π' w⁻¹) (pre (B0.π' w) v) = v := by
    intro v
    rw [pre_apply, pre_apply, ContinuousLinearMap.comp_assoc, ← B0.π'_rep.2 _ hw _ hwi,
      Matrix.mul_nonsing_inv _ hU, B0.π'_rep.1]
    rfl
  unfold PBQ.pbF
  rw [← pre_apply, ← integral_clm_leftInv _ _ hML]
  congr 1
  funext x
  unfold PBQ.pbI
  rw [← Matrix.mul_assoc, kr_right_uw B0 H _ w hw, pre_apply, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_assoc]

theorem pbF_left_uw (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (h : B.Mat k ρ) (hh : h ∈ UWset k ρ Bj.z) (g : B.Mat k n) :
    PBQ.pbF Bj B0 e H (D.castM e (U.embG k p ρ h) * g) = (Bj.π h).comp (PBQ.pbF Bj B0 e H g) := by
  have hU := unit_of_uw hh
  have hi : h⁻¹ ∈ UWset k ρ Bj.z := LieBracketMultiplication.uw_inv hh
  have hiU := unit_of_uw hi
  have := PBG.sigmaFinite_of_haar Bj.haarN
  have := PBG.sigmaFinite_of_haar Bj.haarW
  haveI : SigmaFinite (U.muRC k p ρ) := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  set e1 := (PBG.lmulHomeo h⁻¹ hiU).toMeasurableEquiv
  set e2 := (conjHomeo h⁻¹ hiU).toMeasurableEquiv
  set Φ : PBQ.XP k p ρ ≃ᵐ PBQ.XP k p ρ := MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr e1 e2)
    (MeasurableEquiv.refl _)
  have hmp1 : MeasurePreserving e1 Bj.μW Bj.μW := by
    refine ⟨e1.measurable, ?_⟩
    have ee : ⇑e1 = lmulM h⁻¹ := by funext x; rfl
    rw [ee]; exact Bj.haarW.left h⁻¹ hi
  have hmp2 : MeasurePreserving e2 Bj.μN Bj.μN := by
    refine ⟨e2.measurable, ?_⟩
    have ee : ⇑e2 = conjM h⁻¹ := by funext x; rfl
    rw [ee]; exact Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k ρ Bj.z Bj.μN Bj.z_mem Bj.T_pos Bj.haarN h⁻¹ hi
  have hmp : MeasurePreserving Φ (PBQ.muXP (p := p) Bj) (PBQ.muXP (p := p) Bj) :=
    (hmp1.prod hmp2).prod (MeasurePreserving.id _)
  have hML : ∀ v : Wq →L[ℂ] Wp, post (Bj.π h⁻¹) (post (Bj.π h) v) = v := by
    intro v
    rw [post_apply, post_apply, ← ContinuousLinearMap.comp_assoc, ← Bj.π_rep.2 _ hi _ hh,
      Matrix.nonsing_inv_mul _ hU, Bj.π_rep.1]
    rfl
  have hF : PBQ.pbF Bj B0 e H g = ∫ x, PBQ.pbI Bj B0 e H g (Φ x) ∂(PBQ.muXP Bj) :=
    (hmp.integral_comp' (PBQ.pbI Bj B0 e H g)).symm
  rw [hF, ← post_apply, ← integral_clm_leftInv _ _ hML]
  unfold PBQ.pbF
  refine integral_congr_ae ?_
  filter_upwards [PBQ.ae_goodP Bj] with x hx
  have hx1 : (Matrix.of x.1.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z := hx.1
  have hx2 : (Matrix.of x.1.2 : B.Mat k ρ) ∈ Nset k ρ := hx.2
  have hΦ : PBQ.GoodP Bj (Φ x) :=
    ⟨LieBracketMultiplication.uw_mul hi hx1, (Formalism.QuantumDeterminants.uWNormal k ρ Bj.z Bj.z_mem h⁻¹ hi _ hx2).1⟩
  have hsP : D.castM e (PBQ.sP Bj x) * (D.castM e (U.embG k p ρ h) * g) = D.castM e (PBQ.sP Bj (Φ x)) * g := by
    rw [← Matrix.mul_assoc, ← PBQ.castM_mul]
    congr 2
    unfold PBQ.sP
    rw [if_pos hx, if_pos hΦ]
    show U.Rn k p ρ (-x.2) * U.embG k p ρ ((Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹) * U.embG k p ρ h =
      U.Rn k p ρ (-x.2) * U.embG k p ρ ((h⁻¹ * Matrix.of x.1.1)⁻¹ * (h⁻¹ * Matrix.of x.1.2 * h⁻¹⁻¹)⁻¹)
    rw [Matrix.mul_assoc, ← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul]
    congr 2
    rw [Matrix.nonsing_inv_nonsing_inv h hU]
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv h hU, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc h h⁻¹, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have hcP : PBQ.cP Bj (Φ x) = PBQ.cP Bj x := by
    unfold PBQ.cP
    show psi k ρ Bj.z cStd (h⁻¹ * Matrix.of x.1.2 * h⁻¹⁻¹) * _ = _
    rw [Matrix.nonsing_inv_nonsing_inv h hU, Formalism.FourierDecayAlt.P.PBM.psi_conj_UW Bj.z cStd h hh]
    rfl
  have hπ : Bj.π (Matrix.of x.1.1) = (Bj.π h).comp (Bj.π (h⁻¹ * Matrix.of x.1.1)) := by
    rw [← Bj.π_rep.2 _ hh _ (LieBracketMultiplication.uw_mul hi hx1), ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  unfold PBQ.pbI
  rw [hsP, ← hcP, hπ, post_apply, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_assoc]
  rfl

end pb

end Formalism.FourierDecayAlt.P.CutEXPbEquiv

namespace Formalism.FourierDecayAlt.P

open CutEXPbEquiv

theorem pullback_equivalence : CutEX.PbEquiv := by
  intro Wp Wq _ _ _ _ _ _ P p G _ Z _ μ _ h hh h' hh'
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hw : D.castM (by omega : P.r + (P.r - P.r) = P.r) (U.embG P.k P.r (P.r - P.r) h') ∈
      UWset P.k P.r p.T.base.z' := by
    have h1 := Formalism.FourierDecayAlt.P.Dx2.Tower.lev_UW (k := P.k) P.r (P.r - P.r) _ h' hh'
    rw [Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG] at h1
    have h2 := Formalism.FourierDecayAlt.P.Dx2.Tower.castM_UW (by omega : P.r + (P.r - P.r) = P.r) _ _ h1
    rw [p.T.z'_lev P.r le_rfl] at h2
    exact h2
  have hpi : p.T.base.π' (D.castM (by omega : P.r + (P.r - P.r) = P.r) (U.embG P.k P.r (P.r - P.r) h')) =
      (p.T.bs P.r).π' h' := by
    rw [p.T.π'_lev P.r le_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
    rfl
  unfold CutEX.pbTop PBQ.pbT CutEX.xT
  rw [LeftFubiniLemmas.embedding_map_embedded_group, PBQ.castM_mul, PBQ.castM_mul, pbF_right_uw _ _ _ _ _ _ hw, pbF_left_uw _ _ _ _ _ hh, hpi,
    ContinuousLinearMap.comp_assoc]

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbRight2
section
open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbRight

theorem castM_nset {k a b : ℕ} (e : a = b) {g : B.Mat k a} (hg : g ∈ Nset k a) : D.castM e g ∈ Nset k b := by
  subst e
  have : D.castM rfl g = g := by
    ext i j
    simp [D.castM]
  rw [this]
  exact hg

end Formalism.FourierDecayAlt.P.CutEXPbRight

namespace Formalism.FourierDecayAlt.P

open CutEX

private theorem castM_mul_eq_mul_castM {k a b : ℕ} (e : a = b) (g h : B.Mat k a) :
    D.castM e (g * h) = D.castM e g * D.castM e h := by
  subst e
  ext i j
  simp [D.castM]

theorem pullback_right_action : CutEX.PbRight := by
  intro Wp Wq _ _ _ _ _ _ P p G _ Z u μ hu
  have hm : D.castM (by omega) (U.muP P.k P.r (P.r - P.r) u) ∈ Nset P.k P.r :=
    CutEXPbRight.castM_nset _ (BigCellDiagonalMap.leviElement_nset u hu)
  unfold CutEX.pbTop CutEX.psiU PBQ.pbT CutEX.xT
  rw [← Ux4.mMap_mul_muP, castM_mul_eq_mul_castM]
  exact PBQ.pbF_right _ _ _ _ _ _ hm

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSuppHyp
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbSupp

section hyp

variable {m : ℕ}

theorem rev_cs (a b : Fin (m + 1) → ℂ) (c : ℂ) (t : ℝ) (ht : 0 < t)
    (ha : ∑ i : Fin m, ‖a i.castSucc‖ ^ 2 ≤ ‖a (Fin.last m)‖ ^ 2)
    (hb : ∑ i : Fin m, ‖b i.castSucc‖ ^ 2 ≤ ‖b (Fin.last m)‖ ^ 2 - t)
    (hc : ‖c‖ ≤ ∑ i : Fin m, ‖a i.castSucc‖ * ‖b i.castSucc‖) :
    ‖a (Fin.last m)‖ * t ≤ 2 * ‖b (Fin.last m)‖ * ‖a (Fin.last m) * b (Fin.last m) + c‖ := by
  set A := ‖a (Fin.last m)‖ with hA
  set Bn := ‖b (Fin.last m)‖ with hBn
  set P := ∑ i : Fin m, ‖a i.castSucc‖ * ‖b i.castSucc‖ with hPdef
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hCS : P ^ 2 ≤ (∑ i : Fin m, ‖a i.castSucc‖ ^ 2) * (∑ i : Fin m, ‖b i.castSucc‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsb : 0 ≤ ∑ i : Fin m, ‖b i.castSucc‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ Bn := norm_nonneg _
  have hBt : t ≤ Bn ^ 2 := by linarith
  have hP2 : P ^ 2 ≤ A ^ 2 * (Bn ^ 2 - t) := hCS.trans (mul_le_mul ha hb hsb (sq_nonneg _))
  have key : 2 * Bn * P ≤ A * (2 * Bn ^ 2 - t) := by
    have hR : 0 ≤ A * (2 * Bn ^ 2 - t) := mul_nonneg hA0 (by linarith)
    have hL : 0 ≤ 2 * Bn * P := by positivity
    have hsq : (2 * Bn * P) ^ 2 ≤ (A * (2 * Bn ^ 2 - t)) ^ 2 := by
      have e1 : (2 * Bn * P) ^ 2 = 4 * Bn ^ 2 * P ^ 2 := by ring
      have e2 : (A * (2 * Bn ^ 2 - t)) ^ 2 = 4 * Bn ^ 2 * (A ^ 2 * (Bn ^ 2 - t)) + A ^ 2 * t ^ 2 := by ring
      rw [e1, e2]
      have h4 : 4 * Bn ^ 2 * P ^ 2 ≤ 4 * Bn ^ 2 * (A ^ 2 * (Bn ^ 2 - t)) :=
        mul_le_mul_of_nonneg_left hP2 (by positivity)
      nlinarith [sq_nonneg (A * t)]
    nlinarith
  have h1 : A * Bn ≤ ‖a (Fin.last m) * b (Fin.last m) + c‖ + ‖c‖ := by
    rw [hA, hBn, ← norm_mul]
    calc ‖a (Fin.last m) * b (Fin.last m)‖ = ‖(a (Fin.last m) * b (Fin.last m) + c) - c‖ := by
          rw [add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  have h2 : A * Bn - P ≤ ‖a (Fin.last m) * b (Fin.last m) + c‖ := by linarith
  calc A * t = 2 * A * Bn ^ 2 - A * (2 * Bn ^ 2 - t) := by ring
    _ ≤ 2 * A * Bn ^ 2 - 2 * Bn * P := by linarith
    _ = 2 * Bn * (A * Bn - P) := by ring
    _ ≤ 2 * Bn * ‖a (Fin.last m) * b (Fin.last m) + c‖ := mul_le_mul_of_nonneg_left h2 (by positivity)

def dS (m : ℕ) : Fin (m + 1) → ℂ := fun i => if i = Fin.last m then -1 else 1

theorem dS_cs (i : Fin m) : dS m i.castSucc = 1 := by simp [dS, Fin.castSucc_ne_last]

theorem dS_last : dS m (Fin.last m) = -1 := by simp [dS]

theorem dS_sq : diagonal (dS m) * diagonal (dS m) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; unfold dS; split_ifs <;> norm_num

theorem sum_dS (v : Fin (m + 1) → ℂ) :
    ∑ i, star (v i) * dS m i * v i =
      ((∑ i : Fin m, ‖v i.castSucc‖ ^ 2 - ‖v (Fin.last m)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Fin.sum_univ_castSucc, dS_last]
  simp only [dS_cs, mul_one, Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_pow]
  have e : ∀ w : ℂ, star w * w = ((‖w‖ : ℝ) : ℂ) ^ 2 := fun w => by
    rw [Complex.star_def, Complex.conj_mul']
  rw [sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => e _
  · rw [mul_neg_one, neg_mul, e]

theorem quad_eq (v w : Fin (m + 1) → ℂ) :
    star w ⬝ᵥ (diagonal (dS m) *ᵥ v) = ∑ i, star (w i) * dS m i * v i := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, mul_assoc]

theorem quad_unitary (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (v : Fin (m + 1) → ℂ) :
    star (μ *ᵥ v) ⬝ᵥ (diagonal (dS m) *ᵥ (μ *ᵥ v)) = star v ⬝ᵥ (diagonal (dS m) *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hμ]

theorem row_unitary (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) :
    μ * diagonal (dS m) * μᴴ = diagonal (dS m) := by
  have h1 : (diagonal (dS m) * μᴴ * diagonal (dS m)) * μ = 1 := by
    calc (diagonal (dS m) * μᴴ * diagonal (dS m)) * μ = diagonal (dS m) * (μᴴ * diagonal (dS m) * μ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hμ, dS_sq]
  have h2 : μ * (diagonal (dS m) * μᴴ * diagonal (dS m)) = 1 := mul_eq_one_comm.mp h1
  calc μ * diagonal (dS m) * μᴴ = μ * (diagonal (dS m) * μᴴ * diagonal (dS m)) * diagonal (dS m) := by
        simp only [Matrix.mul_assoc, dS_sq, Matrix.mul_one]
    _ = diagonal (dS m) := by rw [h2, Matrix.one_mul]

theorem col_id (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (j : Fin (m + 1)) :
    ((∑ i : Fin m, ‖μ i.castSucc j‖ ^ 2 - ‖μ (Fin.last m) j‖ ^ 2 : ℝ) : ℂ) = dS m j := by
  have e := congrFun (congrFun hμ j) j
  rw [Matrix.mul_apply] at e
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at e
  rw [← sum_dS (fun i => μ i j), ← e]

theorem row_id (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (i : Fin (m + 1)) :
    ((∑ j : Fin m, ‖μ i j.castSucc‖ ^ 2 - ‖μ i (Fin.last m)‖ ^ 2 : ℝ) : ℂ) = dS m i := by
  have e := congrFun (congrFun (row_unitary μ hμ) i) i
  rw [Matrix.mul_apply] at e
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at e
  rw [← sum_dS (fun j => μ i j), ← e]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem real_of_cs {x : ℝ} (h : (x : ℂ) = 1) : x = 1 := by exact_mod_cast h

theorem real_of_last {x : ℝ} (h : (x : ℂ) = -1) : x = -1 := by exact_mod_cast h

theorem entry_le_last (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (i j : Fin (m + 1)) :
    ‖μ i j‖ ≤ ‖μ (Fin.last m) (Fin.last m)‖ := by
  have hrow := real_of_last (by rw [row_id μ hμ (Fin.last m), dS_last])
  have hsq : ‖μ i j‖ ^ 2 ≤ ‖μ (Fin.last m) (Fin.last m)‖ ^ 2 := by
    have hrow' : ∀ j0 : Fin m, ‖μ (Fin.last m) j0.castSucc‖ ^ 2 ≤ ‖μ (Fin.last m) (Fin.last m)‖ ^ 2 - 1 := by
      intro j0
      have : ‖μ (Fin.last m) j0.castSucc‖ ^ 2 ≤ ∑ j : Fin m, ‖μ (Fin.last m) j.castSucc‖ ^ 2 :=
        Finset.single_le_sum (f := fun j : Fin m => ‖μ (Fin.last m) j.castSucc‖ ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ j0)
      linarith
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j0, rfl⟩ | rfl
    · have hcol := real_of_cs (by rw [col_id μ hμ j0.castSucc, dS_cs])
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i0, rfl⟩ | rfl
      · have : ‖μ i0.castSucc j0.castSucc‖ ^ 2 ≤ ∑ i : Fin m, ‖μ i.castSucc j0.castSucc‖ ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin m => ‖μ i.castSucc j0.castSucc‖ ^ 2)
            (fun i _ => by positivity) (Finset.mem_univ i0)
        linarith [hrow' j0]
      · linarith [hrow' j0]
    · have hcol := real_of_last (by rw [col_id μ hμ (Fin.last m), dS_last])
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i0, rfl⟩ | rfl
      · have : ‖μ i0.castSucc (Fin.last m)‖ ^ 2 ≤ ∑ i : Fin m, ‖μ i.castSucc (Fin.last m)‖ ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin m => ‖μ i.castSucc (Fin.last m)‖ ^ 2)
            (fun i _ => by positivity) (Finset.mem_univ i0)
        linarith
      · exact le_rfl
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.mp hsq

theorem entry_bound (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (z z' : Fin (m + 1) → ℂ) (T T' : ℝ) (hT : 0 < T)
    (hT' : 0 < T') (hz : ∑ i : Fin m, ‖z i.castSucc‖ ^ 2 = ‖z (Fin.last m)‖ ^ 2 - T)
    (hz' : ∑ i : Fin m, ‖z' i.castSucc‖ ^ 2 = ‖z' (Fin.last m)‖ ^ 2 - T') (i j : Fin (m + 1)) :
    ‖μ i j‖ * (T * T') ≤
      4 * ‖z (Fin.last m)‖ * ‖z' (Fin.last m)‖ * ‖star z ⬝ᵥ (diagonal (dS m) *ᵥ (μ *ᵥ z'))‖ := by
  set y := μ *ᵥ z' with hy

  have hyq : ∑ i : Fin m, ‖y i.castSucc‖ ^ 2 ≤ ‖y (Fin.last m)‖ ^ 2 := by
    have e := quad_unitary μ hμ z'
    rw [quad_eq, quad_eq, sum_dS, sum_dS] at e
    have e' : ∑ i : Fin m, ‖y i.castSucc‖ ^ 2 - ‖y (Fin.last m)‖ ^ 2 =
        ∑ i : Fin m, ‖z' i.castSucc‖ ^ 2 - ‖z' (Fin.last m)‖ ^ 2 := by exact_mod_cast e
    linarith

  have h1 : ‖y (Fin.last m)‖ * T ≤ 2 * ‖z (Fin.last m)‖ *
      ‖star z ⬝ᵥ (diagonal (dS m) *ᵥ y)‖ := by
    have hb : ∑ i : Fin m, ‖(fun i => -star (z i)) i.castSucc‖ ^ 2 ≤
        ‖(fun i => -star (z i)) (Fin.last m)‖ ^ 2 - T := by
      simp only [norm_neg, norm_star]; linarith
    have := rev_cs y (fun i => -star (z i)) (∑ i : Fin m, star (z i.castSucc) * y i.castSucc) T hT hyq hb (by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [norm_mul, norm_neg, norm_star, mul_comm])
    simp only [norm_neg, norm_star] at this
    have hζ : star z ⬝ᵥ (diagonal (dS m) *ᵥ y) =
        y (Fin.last m) * -star (z (Fin.last m)) + ∑ i : Fin m, star (z i.castSucc) * y i.castSucc := by
      rw [quad_eq, Fin.sum_univ_castSucc, dS_last]
      simp only [dS_cs, mul_one]
      ring
    rw [hζ]; exact this

  have h2 : ‖μ (Fin.last m) (Fin.last m)‖ * T' ≤ 2 * ‖z' (Fin.last m)‖ * ‖y (Fin.last m)‖ := by
    have hrow := real_of_last (by rw [row_id μ hμ (Fin.last m), dS_last])
    have ha : ∑ j : Fin m, ‖(fun j => μ (Fin.last m) j) j.castSucc‖ ^ 2 ≤
        ‖(fun j => μ (Fin.last m) j) (Fin.last m)‖ ^ 2 := by simp only; linarith
    have hb : ∑ i : Fin m, ‖z' i.castSucc‖ ^ 2 ≤ ‖z' (Fin.last m)‖ ^ 2 - T' := le_of_eq hz'
    have := rev_cs (fun j => μ (Fin.last m) j) z' (∑ j : Fin m, μ (Fin.last m) j.castSucc * z' j.castSucc) T' hT'
      ha hb (by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [norm_mul])
    have hyL : y (Fin.last m) =
        μ (Fin.last m) (Fin.last m) * z' (Fin.last m) + ∑ j : Fin m, μ (Fin.last m) j.castSucc * z' j.castSucc := by
      rw [hy, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]; ring
    rw [hyL]; exact this
  have h3 := entry_le_last μ hμ i j
  have hzL : 0 ≤ ‖z (Fin.last m)‖ := norm_nonneg _
  have hz'L : 0 ≤ ‖z' (Fin.last m)‖ := norm_nonneg _
  calc ‖μ i j‖ * (T * T') ≤ ‖μ (Fin.last m) (Fin.last m)‖ * T' * T := by
        rw [mul_comm T T', ← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hT'.le) hT.le
    _ ≤ 2 * ‖z' (Fin.last m)‖ * ‖y (Fin.last m)‖ * T := mul_le_mul_of_nonneg_right h2 hT.le
    _ = 2 * ‖z' (Fin.last m)‖ * (‖y (Fin.last m)‖ * T) := by ring
    _ ≤ 2 * ‖z' (Fin.last m)‖ * (2 * ‖z (Fin.last m)‖ * ‖star z ⬝ᵥ (diagonal (dS m) *ᵥ y)‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

end hyp

end Formalism.FourierDecayAlt.P.CutEXPbSupp
end
end

