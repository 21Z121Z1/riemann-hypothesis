import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0244
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0089
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAtGq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0210
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0219
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0240
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0241
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0147
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0213
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0183
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtieLevTransportHerOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0161

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTopKr
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem emb_mu_uni {k p ρ : ℕ} (ν : B.Mat k ρ) (V : Matrix (Fin p) (Fin p) ℂ) (a : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (b : Matrix (Fin p) (Fin p) ℂ) (c : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) :
    U.embG k p ρ ν * U.muP k p ρ V * U.blk3 1 a b 0 1 c 0 0 1 =
      U.blk3 V (V * a) (V * b) 0 ν (ν * c) 0 0 (G.wMat p * Vᴴ⁻¹ * G.wMat p) := by
  unfold U.embG U.muP
  rw [Ux3.block3_mul, Ux3.block3_mul]
  congr 1 <;> simp

theorem upper_inj {p : ℕ} {u u' : G.UT p → ℂ} (h : G.upper u = G.upper u') : u = u' := by
  funext p
  have h1 := congrFun (congrFun h p.1.1) p.1.2
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_lt p.2),
    zero_add, dif_pos p.2] at h1
  exact h1

theorem kr_eq_integral_krI_psiR {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k (p + ρ))
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (y₀ : B.Mat k (p + ρ)) :
    PBG.Kr B0 H y₀ = ∫ s, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s) ∂(LeftFubiniLemmas.muR (p := p) Bj) := by
  classical
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ

  set S : Set (LeftFubiniLemmas.XR k p ρ) := {s | LeftFubiniLemmas.GoodR Bj s} with hSdef
  have hSc : IsClosed S :=
    IsClosed.and ((Formalism.FourierDecayAlt.P.B6.isClosed_UWset k ρ Bj.z').preimage (continuous_fst.comp continuous_fst))
      ((Formalism.FourierDecayAlt.P.B6.isClosed_Nset k ρ).preimage (continuous_snd.comp continuous_fst))
  have hBS : BorelSpace (LeftFubiniLemmas.XR k p ρ) := by
    have : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ × (G.UT p → ℂ)) := Prod.borelSpace
    have : BorelSpace (Mt k ρ × Mt k ρ) := Prod.borelSpace
    exact Prod.borelSpace
  have hSm : MeasurableSet S := hSc.measurableSet

  have hmp : MeasurePreserving (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) (LeftFubiniLemmas.muR Bj) (B0.μW'.prod B0.μN) := by
    have h := LeftFubiniLemmas.right_measure_preserving k p ρ Bj.z' Bj.μW' B0.μW' Bj.haarW' hW' hW0'
    unfold LeftFubiniLemmas.muR
    rw [hN0, hNj]
    exact h

  have hinj : Set.InjOn (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) S := by
    intro s hs s' hs' he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    have h11 : s.1.1 = s'.1.1 := by
      have := congrArg (Formalism.FourierDecayAlt.P.PBM.midMt p ρ rfl) he1
      simpa only [LeftFubiniLemmas.PsiR, Formalism.FourierDecayAlt.P.PBM.midMt_levMt] using this
    have hN : LeftFubiniLemmas.NR s = LeftFubiniLemmas.NR s' := Matrix.of.symm.injective he2
    obtain ⟨a, b, c, hRn⟩ : ∃ a b c, U.Rn k p ρ (LeftFubiniLemmas.rcAct (Matrix.of s.1.1) s.2.1) = U.blk3 1 a b 0 1 c 0 0 1 :=
      ⟨_, _, _, Formalism.FourierDecayAlt.P.Ux3.rn_eq _⟩
    obtain ⟨a', b', c', hRn'⟩ : ∃ a b c, U.Rn k p ρ (LeftFubiniLemmas.rcAct (Matrix.of s'.1.1) s'.2.1) = U.blk3 1 a b 0 1 c 0 0 1 :=
      ⟨_, _, _, Formalism.FourierDecayAlt.P.Ux3.rn_eq _⟩
    unfold LeftFubiniLemmas.NR at hN
    rw [hRn, hRn', emb_mu_uni, emb_mu_uni, Formalism.FourierDecayAlt.P.Ux3.block3_eq_iff] at hN
    obtain ⟨hU, hUa, hUb, -, hν, hνc, -, -, -⟩ := hN
    have hUu : IsUnit (G.upper s.2.2).det := by rw [Formalism.FourierDecayAlt.P.Ux3.det_upper]; exact isUnit_one
    have hνu : IsUnit (Matrix.of s.1.2 : B.Mat k ρ).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hs.2.1
    have hu : s.2.2 = s'.2.2 := upper_inj hU
    rw [← hU] at hUa hUb
    rw [← hν] at hνc
    have ha : a = a' := by
      have := congrArg (fun M => (G.upper s.2.2)⁻¹ * M) hUa
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul] using this
    have hb : b = b' := by
      have := congrArg (fun M => (G.upper s.2.2)⁻¹ * M) hUb
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul] using this
    have hc : c = c' := by
      have := congrArg (fun M => (Matrix.of s.1.2 : B.Mat k ρ)⁻¹ * M) hνc
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hνu, Matrix.one_mul] using this
    have hR : LeftFubiniLemmas.rcAct (Matrix.of s.1.1) s.2.1 = LeftFubiniLemmas.rcAct (Matrix.of s'.1.1) s'.2.1 :=
      (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).1 (by rw [hRn, hRn', ha, hb, hc])
    rw [← h11] at hR
    have hhu : IsUnit (Matrix.of s.1.1 : B.Mat k ρ).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hs.1.1
    have h21 : s.2.1 = s'.2.1 := by
      have e1 := congrArg Prod.fst hR
      have e2 := congrArg Prod.snd hR
      simp only [LeftFubiniLemmas.rcAct] at e1 e2
      have e1' : (Matrix.of s.1.1 : B.Mat k ρ) * Matrix.of s.2.1.1 = Matrix.of s.1.1 * Matrix.of s'.2.1.1 := by
        ext v w; exact congrFun (congrFun e1 v) w
      have e3 := congrArg (fun M => (Matrix.of s.1.1 : B.Mat k ρ)⁻¹ * M) e1'
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hhu, Matrix.one_mul] at e3
      exact Prod.ext (by ext v w; exact congrFun (congrFun e3 v) w) e2
    have h12 : s.1.2 = s'.1.2 := by
      ext v w; exact congrFun (congrFun hν v) w
    exact Prod.ext (Prod.ext h11 h12) (Prod.ext h21 hu)
  have hres : (LeftFubiniLemmas.muR (p := p) Bj).restrict S = LeftFubiniLemmas.muR Bj :=
    Measure.restrict_eq_self_of_ae_mem (LeftFubiniLemmas.ae_goodR Bj)
  have hcont : Continuous (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) := by
    unfold LeftFubiniLemmas.PsiR
    exact ((Formalism.FourierDecayAlt.P.PBM.levMt_cont p ρ rfl).comp (continuous_fst.comp continuous_fst)).prodMk LeftFubiniLemmas.NR_cont
  have hPol : PolishSpace (LeftFubiniLemmas.XR k p ρ) := {}
  have hSB : StandardBorelSpace (LeftFubiniLemmas.XR k p ρ) := inferInstance
  have : StandardBorelSpace S := hSm.standardBorel
  have hemb : MeasurableEmbedding (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) :=
    (hcont.measurable.comp measurable_subtype_coe).measurableEmbedding
      (fun a b hab => Subtype.ext (hinj a.2 b.2 hab))
  rw [LeftFubiniLemmas.kr_eq_int]
  calc ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂(B0.μW'.prod B0.μN)
      = ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂((LeftFubiniLemmas.muR (p := p) Bj).map LeftFubiniLemmas.PsiR) := by rw [hmp.map_eq]
    _ = ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂((Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)).map
          (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ))) := by
        rw [show (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) = LeftFubiniLemmas.PsiR ∘ Subtype.val from rfl,
          ← Measure.map_map hcont.measurable measurable_subtype_coe, map_comap_subtype_coe hSm, hres]
    _ = ∫ s : S, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) ∂(Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)) :=
        hemb.integral_map _
    _ = ∫ s, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s) ∂((Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)).map
          (Subtype.val : S → LeftFubiniLemmas.XR k p ρ)) :=
        ((MeasurableEmbedding.subtype_coe hSm).integral_map (fun s => LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s))).symm
    _ = _ := by rw [map_comap_subtype_coe hSm, hres]

end Formalism.FourierDecayAlt.P.PBQ
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapTP
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField PI.UnitaryGroupMassFormula.GsFr
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def kcut (t : ℝ) : ℝ := Real.smoothTransition (6 * t - 2)

theorem kcut_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) kcut :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem kcut_zero {t : ℝ} (ht : t ≤ 1 / 3) : kcut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem kcut_one {t : ℝ} (ht : 1 / 2 ≤ t) : kcut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

def NrmWFacts : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => PRho.nrmW k r z a) ∧
    ∀ h ∈ UWset k r z, ∀ a, PRho.nrmW k r z (h *ᵥ a) = PRho.nrmW k r z a

theorem nrmW_smul {k r : ℕ} (z a : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    PRho.nrmW k r z (c • a) = Complex.normSq c * PRho.nrmW k r z a := by
  unfold PRho.nrmW
  rw [SSn.Geom.prWv_eq, SSn.Geom.prW_smul, ← SSn.Geom.prWv_eq]
  rw [hm_smul_l, hm_smul_r, ← mul_assoc, Complex.star_def, Complex.mul_conj, Complex.re_ofReal_mul]

section lm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def lmul (A : Wp →L[ℂ] Wp) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wp Wp A

theorem lmul_apply (A : Wp →L[ℂ] Wp) (X : Wq →L[ℂ] Wp) : lmul A X = A.comp X := rfl

theorem hsInner_lmul (A : Wp →L[ℂ] Wp) (hA : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y)) (X Y : Wq →L[ℂ] Wp) :
    B.hsInner (lmul A X) Y = B.hsInner X (lmul A Y) := by
  simp only [B.hsInner, B.hsVec, lmul_apply, PiLp.inner_apply, ContinuousLinearMap.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA]

end lm

theorem typeProj_of (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines) (hDU : SSn.Rep.DatumUnit)
    (hNW : NrmWFacts) : TypeProj := by
  refine ⟨0, le_rfl, ?_⟩
  intro Cc _ E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  by_cases hk : 2 ≤ S.G.k
  · obtain ⟨Pr, hs, heqv, hrest⟩ := hPE (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl hk
    obtain ⟨hnc, hninv⟩ := hNW S.G.k S.G.r (T v).base.z (T v).base.z_mem (T v).base.T_pos
    refine ⟨fun σ a => ((kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) : ℝ) : ℂ) • lmul (Pr σ a), ?_, ?_, ?_, ?_⟩
    ·
      intro σ
      rw [contDiff_iff_contDiffAt]
      intro a₀
      by_cases h : 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a₀
      · have hO : IsOpen {a | 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a} :=
          isOpen_lt continuous_const hnc.continuous
        have hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun A : Wp (S.pl v) →L[ℂ] Wp (S.pl v) => (lmul A : (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] _)) :=
          (ContinuousLinearMap.compL ℂ (Wq (S.pl v)) (Wp (S.pl v)) (Wp (S.pl v))).contDiff.restrict_scalars ℝ
        have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun a => ((kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) : ℝ) : ℂ) • lmul (Pr σ a))
            {a | 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a} :=
          ((Complex.ofRealCLM.contDiff.comp (kcut_contDiff.comp hnc)).contDiffOn).smul
            (hl.comp_contDiffOn (hs σ))
        exact h1.contDiffAt (hO.mem_nhds h)
      · have hO : IsOpen {a | PRho.nrmW S.G.k S.G.r (T v).base.z a < 1 / 3} :=
          isOpen_lt hnc.continuous continuous_const
        have hmem : a₀ ∈ {a | PRho.nrmW S.G.k S.G.r (T v).base.z a < 1 / 3} := by
          simp only [Set.mem_setOf_eq]; linarith [not_lt.1 h]
        refine (contDiffAt_const (c := (0 : (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v))))).congr_of_eventuallyEq ?_
        filter_upwards [hO.mem_nhds hmem] with a ha
        simp [kcut_zero (le_of_lt ha)]
    ·
      intro σ a A B'
      dsimp only
      by_cases h : 0 < PRho.nrmW S.G.k S.G.r (T v).base.z a
      · rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, kap_hsInner_smul_left,
          kap_hsInner_smul_right, Complex.conj_ofReal, hsInner_lmul _ ((hrest a h).2.1 σ)]
      · have h0 : kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) = 0 := kcut_zero (by linarith [not_lt.1 h])
        simp [h0, B.hsInner, kap_hsVec_zero]
    ·
      intro σ h hh h' hh' a X
      have hinv : h⁻¹ ∈ UWset S.G.k S.G.r (T v).base.z := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
      have hu := WeylGroupFacts.isUnit_of_uh hh.1
      have hh1 : h⁻¹ * h = 1 := by
        first
          | exact Matrix.nonsing_inv_mul _ hu
          | exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
      have key : ∀ y, (T v).base.π h⁻¹ ((T v).base.π h y) = y := by
        intro y
        rw [← ContinuousLinearMap.comp_apply, ← (T v).base.π_rep.2 _ hinv _ hh, hh1, (T v).base.π_rep.1]
        rfl
      dsimp only
      rw [hninv h hh a, heqv h hh σ a]
      ext y
      simp [lmul_apply, key]
    ·
      intro x hx σ ρ
      dsimp only
      obtain ⟨hP1, hH1, -, -⟩ := hDU Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v x.2 hx.2
      set n0 := SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec x.2 with hn0
      have hN0 : PRho.nrmW S.G.k S.G.r (T v).base.z n0 = 1 := by
        unfold PRho.nrmW; rw [hP1, hH1]; simp
      have hph : SSn.phD x.1 ≠ 0 := by
        intro h0
        have := SSn.Geom.phD_norm hx.1
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      have hN : PRho.nrmW S.G.k S.G.r (T v).base.z (SSn.phD x.1 • n0) = 1 := by
        rw [nrmW_smul, hN0, mul_one, Complex.normSq_eq_norm_sq, SSn.Geom.phD_norm hx.1]; norm_num
      have hscale : ∀ τ, Pr τ (SSn.phD x.1 • n0) = Pr τ n0 :=
        fun τ => (hrest n0 (by rw [hN0]; norm_num)).1 τ _ hph
      have hfix : ∀ y, Pr ρ n0 (e ρ x.2 y) = e ρ x.2 y := by
        intro y
        refine ((hrest n0 (by rw [hN0]; norm_num)).2.2.2 ρ (e ρ x.2 y)).2 ?_
        intro Fr hFrm w
        rw [hP1] at hFrm
        exact hGL Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk x.2 hx.2 ρ Fr hFrm w y
      rw [ContinuousLinearMap.smul_apply, hN, kcut_one (by norm_num), lmul_apply, hscale]
      simp only [Complex.ofReal_one, one_smul]
      by_cases hσ : σ = ρ
      · subst hσ
        rw [if_pos rfl]
        ext y
        exact hfix y
      · rw [if_neg hσ]
        ext y
        have horth := (hrest n0 (by rw [hN0]; norm_num)).2.2.1 σ ρ
        rw [if_neg hσ] at horth
        rw [ContinuousLinearMap.comp_apply, ← hfix y, ← ContinuousLinearMap.comp_apply (Pr σ n0), horth]
        rfl
  ·
    have hk1 : (D.parOf S v).k - 1 = 0 := by
      have : (D.parOf S v).k = S.G.k := rfl
      omega
    have hsub : ∀ σ ρ : M.Ty (D.parOf S v), σ = ρ := by
      intro σ ρ
      funext i
      exact absurd i.2 (by omega)
    refine ⟨fun _ _ => ContinuousLinearMap.id ℂ _, fun σ => contDiff_const, fun σ a A B' => rfl,
      fun σ h _ h' _ a X => rfl, ?_⟩
    intro x _ σ ρ
    rw [if_pos (hsub σ ρ)]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjComm
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

theorem adjoint_commutation_holds : AdjComm := adjComm_of_parts fundamental_domain_group adjoint_continuity_holds adjoint_integral_identity_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomUBLTools
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ContDiff Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section tools

variable {k r : ℕ}

theorem ckOn_of_cd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Mat k r → E} (hf : ContDiff ℝ ∞ f)
    (m : ℕ∞) (UU : Set (Mat k r)) : CkOn m UU f := by
  intro g₀ _
  exact ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn, fun _ _ _ => rfl⟩

theorem lss_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)}
    {f₁ f₂ : Mat k r → E} (hl₁ : LSS f₁ S) (hl₂ : LSS f₂ S) : LSS (fun g => f₁ g + f₂ g) S := by
  intro g hg
  obtain ⟨a, ha, V, hV, hgV, hae⟩ := hl₁ g hg
  obtain ⟨b, hb, W, hW, hgW, hbe⟩ := hl₂ g hg
  refine ⟨fun g => a g + b g, ha.add hb, V ∩ W, hV.inter hW, ⟨hgV, hgW⟩, fun g' hg' hm => ?_⟩
  show f₁ g' + f₂ g' = a g' + b g'
  rw [hae g' hg' hm.1, hbe g' hg' hm.2]

theorem ubl_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {f₁ f₂ : Mat k r → E} {n e γ : ℕ} (h₁ : UBL f₁ S n e γ) (h₂ : UBL f₂ S n e γ) :
    UBL (fun g => f₁ g + f₂ g) S n e γ := by
  obtain ⟨⟨C₁, hC₁, hb₁⟩, hl₁⟩ := h₁
  obtain ⟨⟨C₂, hC₂, hb₂⟩, hl₂⟩ := h₂
  refine ⟨⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun w hw g hg => ?_⟩, lss_add hl₁ hl₂⟩
  obtain ⟨a, ha, V, hV, hgV, haa⟩ := hl₁ g hg
  obtain ⟨b, hb, W, hW, hgW, hbb⟩ := hl₂ g hg
  have hlie := admissible_word_mem_lie hw
  have hG := hSG hg
  have e0 : Dw w (fun g => f₁ g + f₂ g) g = Dw w (fun g => a g + b g) g :=
    Dw_congr_loc hlie (hV.inter hW) (fun g' hG' hg' => by simp [haa g' hG' hg'.1, hbb g' hG' hg'.2]) g hG
      ⟨hgV, hgW⟩
  rw [e0, Dw_add hlie (ckOn_of_cd ha _ _) (ckOn_of_cd hb _ _) g hG,
    ← Dw_congr_loc hlie hV haa g hG hgV, ← Dw_congr_loc hlie hW hbb g hG hgW]
  refine (norm_add_le _ _).trans ?_
  rw [add_mul]
  exact add_le_add (hb₁ w hw g hg) (hb₂ w hw g hg)

theorem ubl_sum {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    (s : Finset ι) {f : ι → Mat k r → E} {n e γ : ℕ} (h : ∀ i ∈ s, UBL (f i) S n e γ) :
    UBL (fun g => ∑ i ∈ s, f i g) S n e γ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ubl_mono hSG (ubl_const (0 : E) hSG n γ) (Nat.zero_le e) le_rfl
  | @insert a s has ih =>
    simp only [Finset.sum_insert has]
    exact ubl_add hSG (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem lss_pi {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)}
    {f : Mat k r → ι → E} (h : ∀ i, LSS (fun g => f g i) S) : LSS f S := by
  intro g hg
  choose F hF V hV hgV hFe using fun i => h i g hg
  refine ⟨fun g i => F i g, contDiff_pi.2 hF, ⋂ i, V i, isOpen_iInter_of_finite hV,
    Set.mem_iInter.2 hgV, fun g' hg' hm => funext fun i => hFe i g' hg' (Set.mem_iInter.1 hm i)⟩

theorem ubl_pi {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)}
    (hSG : S ⊆ GV k r) {f : Mat k r → ι → E} {n e γ : ℕ} (h : ∀ i, UBL (fun g => f g i) S n e γ) :
    UBL f S n e γ := by
  have h1 := fun i => (h i).1
  have hL := fun i => (h i).2
  choose C hC hB using h1
  have hCs : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hC i
  refine ⟨⟨∑ i, C i, hCs, fun w hw g hg => ?_⟩, lss_pi hL⟩
  have hlie := admissible_word_mem_lie hw
  have hgG := hSG hg
  have hgN : 0 ≤ gN g := Real.sqrt_nonneg _
  obtain ⟨F, hF, V, hV, hgV, hFe⟩ := lss_pi hL g hg
  rw [Dw_congr_loc hlie hV hFe g hgG hgV]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hCs (pow_nonneg hgN _))).2 fun i => ?_
  rw [Formalism.FourierDecayAlt.P.Ux8.Dw_pi hlie (ckOn_of_cd hF _ _) g hgG i]
  have e1 := Dw_congr_loc hlie hV (f := fun g => f g i) (f₂ := fun g => F g i)
    (fun g' hg' hm => congrFun (hFe g' hg' hm) i) g hgG hgV
  rw [← e1]
  calc ‖Dw w (fun g => f g i) g‖ ≤ C i * gN g ^ (e + γ * w.length) := hB i w hw g hg
    _ ≤ (∑ j, C j) * gN g ^ (e + γ * w.length) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))
          (pow_nonneg hgN _)

theorem ubl_star {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {f : Mat k r → ℂ} {n e γ : ℕ} (h : UBL f S n e γ) :
    UBL (fun g => star (f g)) S n e γ := by
  have hfun : (fun g => star (f g)) =
      fun g => (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap (f g) := by
    funext g; rfl
  rw [hfun]
  exact ubl_clm _ hSG h

theorem ubl_mmul {m : ℕ} {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {A B : Mat k r → Matrix (Fin m) (Fin m) ℂ} {n ea eb γ : ℕ}
    (hA : ∀ i j, UBL (fun g => A g i j) S n ea γ) (hB : ∀ i j, UBL (fun g => B g i j) S n eb γ) (i j : Fin m) :
    UBL (fun g => (A g * B g) i j) S n (ea + eb) γ := by
  have hfun : (fun g => (A g * B g) i j) = fun g => ∑ l ∈ Finset.univ, A g i l * B g l j := by
    funext g; simp [Matrix.mul_apply]
  rw [hfun]
  exact ubl_sum hSG _ fun l _ => ubl_mul hSG (hA i l) (hB l j)

end tools

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DegLiftOfParts
section
open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def KrHyp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (j : ℕ) (hj : j ≤ r) (H : B.Mat k r → (Wq →L[ℂ] Wp)),
    (∀ x ∈ B.GV k r, Dmin k r Bs.z Bs.z' x ⟨j, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) H x) →
    (∃ R : ℝ, ∀ x ∈ B.GV k r, H x ≠ 0 → B.gN x ≤ R) →
    ∀ y ∈ B.GV k r, Dmin k r Bs.z Bs.z' y ⟨j, by omega⟩ ≠ 0 →
      CapelliWordSumExpansion.Loc (⊤ : ℕ∞) (Kr Bs H) y ∧
      ∀ (l : C.Letter) (e : Fin 2), Kr Bs (D.vLet k r Bs.z Bs.z' j hj l e H) y = D.vLet k r Bs.z Bs.z' j hj l e (Kr Bs H) y

theorem liftDegAll_of (hLF : LeftFubiniLemmas.LeftFubini) (hNF : LeftFubiniLemmas.NFHypL) (hKr : KrHyp) : LiftDegAll := by
  intro Wp Wq _ _ _ _ _ _ P p F hF j s hj h τ ha w' a' b δ g hg
  have hsz : D.ptSize (h ++ [(s, τ)]) = D.ptSize h + s := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s τ
  have hs1 : 1 ≤ s := (ha.1 (s, τ) (by simp)).1
  have hj1 : 1 ≤ j := by rw [← ha.2, hsz]; omega
  obtain ⟨X, _, μ, ℓ, sx, hsx, hFubG⟩ := hLF P.k P.r Wp Wq p.T p.hT j hj hj1 (h ++ [(s, τ)]) ha
  have hgG : g ∈ B.GV P.k (P.r - j) := hg.1
  have hg' : D.castM (by rw [ha.2]) g ∈ B.GV P.k (P.r - D.ptSize (h ++ [(s, τ)])) :=
    Formalism.FourierDecayAlt.P.PBE.castM_GV _ hgG
  have hl : D.IsLocPt (h ++ [(s, τ)]) (D.ptSize (h ++ [(s, τ)])) := ⟨ha.1, rfl⟩
  obtain ⟨hx₁G, hxi, hy⟩ := hNF P.k P.r (h ++ [(s, τ)]) (by rw [ha.2]; exact hj) _ hg' hl
  set PC : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → Prop := fun H =>
    (∀ x ∈ B.GV P.k P.r, Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨j, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) H x) ∧
    (∃ R : ℝ, ∀ x ∈ B.GV P.k P.r, H x ≠ 0 → B.gN x ≤ R) with hPC
  refine liftDeg_core p.T F j s hj h τ ha w' a' b δ g X μ ℓ sx _ hsx hx₁G ?_ ?_ PC
    (fun H hH => hFubG g hg H (contOn_of_loc (fun x hx hxG => hH.1 x hxG hx)) hH.2) ?_
    (fun H hH y hyG hyD => (hKr P.k P.r Wp Wq p.T.base j hj H hH.1 hH.2 y hyG hyD).1)
    (fun H hH y hyG hyD => (hKr P.k P.r Wp Wq p.T.base j hj H hH.1 hH.2 y hyG hyD).2)
  · intro a₀ q ha₀
    rw [hxi a₀ q (by rw [hsz]; exact ha₀)]
    by_cases hq : q.val < D.ptSize h + s
    · rw [dif_pos (by rw [hsz]; exact hq), if_pos hq]
      exact hmat_zb h s τ hl a₀.val q.val _ _
    · rw [dif_neg (by rw [hsz]; exact hq), if_neg hq]
  · intro a₀ q ha₀
    rw [hy a₀ q (by rw [hsz]; exact ha₀)]
    by_cases hq : P.r + P.k < q.val ∧ 2 * P.r + P.k - q.val < D.ptSize h + s
    · rw [dif_pos (by rw [hsz]; exact hq), if_pos hq, hmat_zb h s τ hl a₀.val _ _ _]
    · rw [dif_neg (by rw [hsz]; exact hq), if_neg hq]
  · intro w e
    refine ⟨fun x hxG hxD => uwG_mem (E := Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' j hj hF.1 w e x hxD hxG, ?_⟩
    obtain ⟨R, hR⟩ := hF.2.1
    exact ⟨R, uwG_supp p.T.base.z p.T.base.z' F R hR j hj w e⟩

theorem degLift_of_parts (hLF : LeftFubiniLemmas.LeftFubini) (hKr : KrHyp) : KB.DegLift :=
  degLift_of (liftDegAll_of hLF LeftFubiniLemmas.normal_form_left_hypothesis hKr)

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PTieAll
section
namespace Formalism.FourierDecayAlt.P

theorem ptie_levTransportHer_of_sliceStep (hS : Formalism.FourierDecayAlt.P.PTie.SliceStepHer) : Formalism.FourierDecayAlt.P.PTie.LevTransportHer :=
  ptie_levTransportHer_of jacquet_scaling hS

end Formalism.FourierDecayAlt.P
end

