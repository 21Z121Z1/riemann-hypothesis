import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmu
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0297
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGCongr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0205
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0271
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0295
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmuDeg
section
namespace Formalism.FourierDecayAlt.P.CutBP.Jmu

open Formalism.FourierDecayAlt MeasureTheory Finset
open scoped ENNReal

noncomputable section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def Present (F : JFam P.k P.r Wp Wq) (μ : Fin (2 * P.r + P.k + 1) → ℤ) : Prop :=
  Formalism.QuantumDeterminants.IsHCParam (lamOf F.sh μ) ∧ (F.A μ).l (F.A μ).w0 ≠ 0 ∧ (F.A μ).l' (F.A μ).w0 ≠ 0

theorem J_eq_zero_of_not_present (Bs : B.RealPlaceData P.k P.r Wp Wq) (F : JFam P.k P.r Wp Wq)
    (μ : Fin (2 * P.r + P.k + 1) → ℤ) (h : ¬ Present F μ) : F.J Bs μ = 0 := by
  by_cases hc : Formalism.QuantumDeterminants.IsHCParam (lamOf F.sh μ)
  · rw [JFam.J_of_hc Bs F μ hc]
    apply coef_eq_zero_of
    by_contra h'
    push Not at h'
    exact h ⟨hc, h'.1, h'.2⟩
  · exact JFam.J_of_not_hc Bs F μ hc

theorem norm_sq_zero_function (p : KB.Pl P Wp Wq) : TBB.jN2 p (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) = 0 := by
  have e : (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) = fun g => (0 : ℂ) • (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) g := by
    funext g
    simp
  rw [e, norm_sq_const_smul]
  simp

theorem V_zero_fun (p : KB.Pl P Wp Wq) (γ : C.LPt) : p.V (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) γ = 0 := by
  have e : (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) = fun g => (0 : ℂ) • (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) g := by
    funext g
    simp
  rw [e, V_csmul]
  simp

def NormDeg (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ μ, LatticeNorms.N1 (μ - lam0) ≤ q0 → Present F μ →
    TBB.jN2 p (F.J p.T.base μ) = ENNReal.ofReal (c * (F.A μ).deg p.T.base.μG)

def DegPos (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∀ μ, LatticeNorms.N1 (μ - lam0) ≤ q0 → Present F μ → 0 < (F.A μ).deg p.T.base.μG

def DegRatio (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∀ μ (I : Finset (Fin (2 * P.r + P.k + 1))), I.card = P.r + 1 → LatticeNorms.N1 (μ - lam0) ≤ q0 →
    LatticeNorms.N1 (μ + LatticeNorms.eI I - lam0) ≤ q0 → Present F μ → Present F (μ + LatticeNorms.eI I) →
    (F.A (μ + LatticeNorms.eI I)).deg p.T.base.μG ≤
      (Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1) * (F.A μ).deg p.T.base.μG

theorem pieri_degree_of_family (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ)
    (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) (c0 q0 : ℕ) (H : ℝ)
    (hc0 : P.r + 1 ≤ c0) (hN : NormDeg p F lam0 q0) (hpos : DegPos p F lam0 q0) (hR : DegRatio p F lam0 q0)
    (hP0 : Present F lam0) : PieriDegreeConditions p (pieriDataOfFamily p F lam0 tau c0 q0 H) := by
  obtain ⟨c, hc, hN⟩ := hN
  have hz := J_eq_zero_of_not_present p.T.base F
  refine ⟨?_, fun μ hμ => ⟨?_, ?_⟩, ?_⟩
  · show 0 < TBB.jN2 p (F.J p.T.base lam0)
    have h0 : LatticeNorms.N1 (lam0 - lam0) ≤ q0 := by rw [sub_self, LatticeNorms.n1_zero]; exact Nat.zero_le _
    rw [hN lam0 h0 hP0]
    exact ENNReal.ofReal_pos.2 (mul_pos hc (hpos lam0 h0 hP0))
  · show TBB.jN2 p (F.J p.T.base μ) < ⊤
    by_cases hp : Present F μ
    · rw [hN μ hμ hp]
      exact ENNReal.ofReal_lt_top
    · rw [hz μ hp, norm_sq_zero_function]
      exact ENNReal.zero_lt_top
  · intro h0 cc _ _
    show p.V (F.J p.T.base μ) _ = 0
    by_cases hp : Present F μ
    · exfalso
      change TBB.jN2 p (F.J p.T.base μ) = 0 at h0
      rw [hN μ hμ hp] at h0
      exact (ENNReal.ofReal_pos.2 (mul_pos hc (hpos μ hμ hp))).ne' h0
    · rw [hz μ hp]
      exact V_zero_fun p _
  · show ∀ μ : Fin (2 * P.r + P.k + 1) → ℤ, LatticeNorms.N1 (μ - lam0) + c0 ≤ q0 → TBB.jN2 p (F.J p.T.base μ) ≠ 0 →
      ∀ I ∈ powersetCard (P.r + 1) (univ : Finset (Fin (2 * P.r + P.k + 1))),
        TBB.jN2 p (F.J p.T.base (μ + LatticeNorms.eI I)) ≤
          ENNReal.ofReal ((Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1)) * TBB.jN2 p (F.J p.T.base μ)
    intro μ hμ hne I hI
    have hp : Present F μ := by
      by_contra hp
      rw [hz μ hp, norm_sq_zero_function] at hne
      exact hne rfl
    have hcard : I.card = P.r + 1 := (mem_powersetCard.1 hI).2
    have hμ' : LatticeNorms.N1 (μ - lam0) ≤ q0 := by omega
    have hI' : LatticeNorms.N1 (μ + LatticeNorms.eI I - lam0) ≤ q0 := by
      have e : μ + LatticeNorms.eI I - lam0 = (μ - lam0) + LatticeNorms.eI I := by abel
      have h1 := LatticeNorms.n1_add_le (μ - lam0) (LatticeNorms.eI I)
      rw [LatticeNorms.n1_eI_eq_card, hcard] at h1
      rw [e]
      omega
    by_cases hq : Present F (μ + LatticeNorms.eI I)
    · have hd := hR μ I hcard hμ' hI' hp hq
      have hE : 0 ≤ (Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1) := by positivity
      rw [hN _ hI' hq, hN μ hμ' hp, ← ENNReal.ofReal_mul hE]
      apply ENNReal.ofReal_le_ofReal
      calc c * (F.A (μ + LatticeNorms.eI I)).deg p.T.base.μG
          ≤ c * ((Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1) * (F.A μ).deg p.T.base.μG) :=
            mul_le_mul_of_nonneg_left hd hc.le
        _ = _ := by ring
    · rw [hz _ hq, norm_sq_zero_function]
      exact bot_le

end

end Formalism.FourierDecayAlt.P.CutBP.Jmu
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuityAllLevels
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

theorem rr_congr_below {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) {F F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F)
    (hE : ∀ g ∈ B.GV P.k P.r, F g = F₂ g) (i : ℕ) (hi : i ≤ P.r) (hi1 : 1 ≤ i) (w : List C.Letter)
    (a b : C.LPt) : p.RR F i w a b = p.RR F₂ i w a b := by
  by_cases hl : D.IsLocPt a i ∧ D.IsLocPt b i
  · unfold KB.Pl.RR D.RRplace
    rw [dif_pos hl, dif_pos hl, dif_pos hi, dif_pos hi]
    have hU : ∀ (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV P.k P.r,
        D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e g = D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e g :=
      fun e g hg => (Formalism.FourierDecayAlt.P.CutEXUw.uwG_congrG p.T.base.z p.T.base.z' i hi isOpen_univ
        (fun x _ hx => (hE x hx).symm) w e g (Set.mem_univ _) hg)
    have hS : ∀ (q : C.LPt), D.IsLocPt q i → ∀ (e : Wd.Ix (Fin w.length)),
        ∀ γ ∈ B.GV P.k (P.r - D.ptSize q),
        D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e) q γ =
          D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e) q γ := by
      intro q hq e γ hγ
      have h1 := Formalism.FourierDecayAlt.P.PBG.sliceAt_lincomb P.k P.r Wp Wq p.T F hF i hi hi1 q hq ({()} : Finset Unit)
        (fun _ => 1) (fun _ => w) (fun _ => e) (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e)
        (fun g hg _ => by simp [hU e g hg]) γ hγ
      simp only [Finset.sum_singleton, one_smul] at h1
      exact h1.symm
    refine Formalism.FourierDecayAlt.P.PBG.formLev_congrGV p.T _ _ w _ _ _ _ (fun e g hg => ?_) (fun e g hg => ?_)
    · simp only [D.castF]
      exact hS a hl.1 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)
    · simp only [D.castF]
      exact hS b hl.2 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)
  · rw [PBL.rr_zero_of_not p F i w a b hl, PBL.rr_zero_of_not p F₂ i w a b hl]

theorem rank_below_compact : RRBelowCpt := by
  intro Wp Wq _ _ _ _ _ _ P p F hF i hi w hw h h' m hm hsz hsz'
  have hi1 : 1 ≤ i := by omega
  have hF0 := hF
  obtain ⟨hs, -, ⟨δ, hδ, hG⟩⟩ := hF
  have heq : ∀ g ∈ B.GV P.k P.r, D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ g = F g :=
    cutF_eq_on_gv p.T.base Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hG hδ le_rfl
  obtain ⟨Cs, -, hSQ⟩ := Formalism.FourierDecayAlt.P.LastBlockContinuity.sliceContQ
  have hk2 : 2 ≤ P.k := p.hl.2.2
  set N : ℕ := w.length with hN
  set A₀ : ℝ := Cs * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)
    with hA₀
  set M : ℕ := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hM
  obtain ⟨εn, hn⟩ := Formalism.FourierDecayAlt.P.PBG.nice_of_cpt p.T.base hF0
  obtain ⟨cF, hcF⟩ := hn.2.1 A₀ M
  have hcut : ContinuousOn (fun cc : ℂ × ℂ => p.RR (D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ) i w
      (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)])) (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
    refine Formalism.FourierDecayAlt.P.LastBlockContinuity.rrBelow_cont P p Formalism.FourierDecayAlt.P.Topx2.chi0 δ F i hi w N le_rfl h h' m hm hsz hsz' ?_ ?_
    · intro hh t0 ht0
      obtain ⟨ε', hε', H⟩ := hSQ Cs le_rfl P.k P.r Wp Wq p.T Formalism.FourierDecayAlt.P.Topx2.chi0 A₀ N P rfl rfl hk2
        Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation le_rfl δ hδ i hi w le_rfl h m (Formalism.FourierDecayAlt.P.LastBlockContinuity.hc_app h m hsz) hh hm hsz t0 ht0
      exact ⟨ε', hε', fun e => H e F cF hs hcF⟩
    · intro hh t0 ht0
      obtain ⟨ε', hε', H⟩ := hSQ Cs le_rfl P.k P.r Wp Wq p.T Formalism.FourierDecayAlt.P.Topx2.chi0 A₀ N P rfl rfl hk2
        Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation le_rfl δ hδ i hi w le_rfl h' m (Formalism.FourierDecayAlt.P.LastBlockContinuity.hc_app h' m hsz') hh hm hsz' t0 ht0
      exact ⟨ε', hε', fun e => H e F cF hs hcF⟩
  refine hcut.congr fun cc _ => ?_
  exact rr_congr_below p hF0 (fun g hg => (heq g hg).symm) i hi hi1 w _ _

theorem germ_continuity_all_levels : GermContAll := germContAll_of rank_below_compact

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormaliserAcrossPlaces
section
namespace Formalism.FourierDecayAlt.P.CutBP2

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section hs

variable {Wp Wq Wq' Wq'' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  [NormedAddCommGroup Wq''] [InnerProductSpace ℂ Wq''] [FiniteDimensional ℂ Wq'']

lemma hs_le_of_adj_sh (X : Wq →L[ℂ] Wp) (A : Wq' →L[ℂ] Wq) (A' : Wq'' →L[ℂ] Wq) (K : ℝ)
    (h : ∀ v : Wq, ‖v‖ ^ 2 ≤
      K * (‖(ContinuousLinearMap.adjoint A) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint A') v‖ ^ 2)) :
    ‖B.hsVec X‖ ^ 2 ≤ K * (‖B.hsVec (X.comp A)‖ ^ 2 + ‖B.hsVec (X.comp A')‖ ^ 2) := by
  rw [Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj X, Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (X.comp A),
    Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (X.comp A'), ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  exact h _

lemma hs_comp_le_sh (X : Wq →L[ℂ] Wp) (A : Wq' →L[ℂ] Wq) :
    ‖B.hsVec (X.comp A)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖B.hsVec X‖ ^ 2 := by
  rw [Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (X.comp A), Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj X, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
  have h1 := (ContinuousLinearMap.adjoint A).le_opNorm
    ((ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j))
  rw [LinearIsometryEquiv.norm_map] at h1
  calc ‖(ContinuousLinearMap.adjoint A) ((ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j))‖ ^ 2
      ≤ (‖A‖ * ‖(ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j)‖) ^ 2 := by gcongr
    _ = ‖A‖ ^ 2 * ‖(ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 := by ring

end hs

section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

lemma ttp_sh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') : TTp q = TTp p := by
  unfold TTp
  rw [hz, hz']
  rfl

lemma ew_sh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) :
    Ew q (fun _ => 1) F (P.r + 1) [] γ =
      (Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ)) * ‖B.hsVec (q.V F γ)‖ ^ 2 := by
  have h := Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top q F hγ
  rw [ttp_sh p q hz hz'] at h
  exact h

lemma V_fpmSh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (APt : C.LPt → (Wq' →L[ℂ] Wq)) (p₀ : ℕ)
    (hz : q.T.base.z = p.T.base.z) (hz' : q.T.base.z' = p.T.base.z') {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) (hG : 0 < Gp p γ)
    (hA : q.V (fun g => (f g).comp (A g)) γ = (p.V f γ).comp (APt γ)) :
    q.V (fpmSh (P := P) q f A p₀) γ = ((Gp p γ ^ p₀ : ℝ) : ℂ) • (p.V f γ).comp (APt γ) := by
  have hGq : Gp q γ = Gp p γ := by
    unfold Gp
    rw [ttp_sh p q hz hz']
    rfl
  have h := Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow q (fun g => (f g).comp (A g)) p₀ hγ (hGq ▸ hG)
  rw [hA, hGq] at h
  exact h

lemma big_sh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (APt : C.LPt → (Wq' →L[ℂ] Wq)) (n₀ p₀ : ℕ)
    (hz : q.T.base.z = p.T.base.z) (hz' : q.T.base.z' = p.T.base.z')
    (hA : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      q.V (fun g => (f g).comp (A g)) γ = (p.V f γ).comp (APt γ))
    (hn : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖APt γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀)
    (c : Fin (P.r + 1) → ℂ) :
    Ew q (fun _ => 1) (fpmSh (P := P) q f A p₀) (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c) := by
  set γ := bigPt P.r c with hγdef
  by_cases hloc : D.IsLocPt γ (P.r + 1)
  swap
  · have h0q : Ew q (fun _ => 1) (fpmSh (P := P) q f A p₀) (P.r + 1) [] γ = 0 :=
      Formalism.FourierDecayAlt.P.TBBx4.ew_not_loc q _ hloc
    rw [h0q, Formalism.FourierDecayAlt.P.TBBx4.ew_not_loc p _ hloc, mul_zero]
  have hGq : Gp q γ = Gp p γ := by
    unfold Gp
    rw [ttp_sh p q hz hz']
    rfl
  rw [ew_sh p q hz hz' _ hloc, Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p f hloc]
  set nn := Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ) with hnn_def
  have hnn : 0 ≤ nn := mul_self_nonneg _
  by_cases hG : 0 < Gp p γ
  · rw [V_fpmSh p q f A APt p₀ hz hz' hloc hG (hA γ hloc hG), Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
    have h1 := hs_comp_le_sh (p.V f γ) (APt γ)
    have h2 := hn γ hloc hG
    set X2 := ‖B.hsVec (p.V f γ)‖ ^ 2 with hX2_def
    have hX2 : 0 ≤ X2 := sq_nonneg _
    have hTT : 0 ≤ TTp p := Formalism.FourierDecayAlt.P.Qx5.place_alt_alt p.hP
    have hGd : Gp p γ ≤ ‖(D.ptMatN γ (P.r + 1)).det‖ ^ 2 := by
      show D.ptG (TTp p) P.r γ ≤ _
      unfold D.ptG
      rw [Complex.normSq_eq_norm_sq]
      have := Complex.normSq_nonneg (D.ptMatN γ P.r).det
      nlinarith
    have hTq : 0 ≤ (Tq p)⁻¹ ^ n₀ := by
      have h3 : 0 ≤ (Gp p γ / Tq p) ^ n₀ := le_trans (sq_nonneg _) h2
      rw [div_pow, div_eq_mul_inv, ← inv_pow] at h3
      exact (mul_nonneg_iff_of_pos_left (pow_pos hG n₀)).mp h3
    calc nn * ((Gp p γ ^ p₀) ^ 2 * ‖B.hsVec ((p.V f γ).comp (APt γ))‖ ^ 2)
        ≤ nn * ((Gp p γ ^ p₀) ^ 2 * (‖APt γ‖ ^ 2 * X2)) := by gcongr
      _ ≤ nn * ((Gp p γ ^ p₀) ^ 2 * ((Gp p γ / Tq p) ^ n₀ * X2)) := by gcongr
      _ = (Gp p γ) ^ (2 * p₀ + n₀) * (Tq p)⁻¹ ^ n₀ * (nn * X2) := by
        rw [div_pow]
        ring
      _ ≤ (‖(D.ptMatN γ (P.r + 1)).det‖ ^ 2) ^ (2 * p₀ + n₀) * (Tq p)⁻¹ ^ n₀ * (nn * X2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hG.le hGd _) hTq)
          (mul_nonneg hnn hX2)
      _ = _ := by rw [← pow_mul]
  · have hq0 : q.V (fpmSh (P := P) q f A p₀) γ = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dif_neg]
      rintro ⟨-, h⟩
      apply hG
      rw [← hGq]
      exact h
    have hp0 : p.V f γ = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dif_neg]
      rintro ⟨-, h⟩
      exact hG h
    have e1 := Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq 0 (0 : Wq' →L[ℂ] Wp)
    have e2 := Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq 0 (0 : Wq →L[ℂ] Wp)
    simp only [Complex.ofReal_zero, zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul] at e1 e2
    rw [hq0, hp0, e1, e2, mul_zero, mul_zero]

end sh

theorem normaliser_across_places : NormAtShOfAmaps := by
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b n₀ p₀
    hz hz' hzm hzm' hA
  obtain ⟨hAp, hAm, hadj, hnp, hnm⟩ := hA
  refine ⟨fun γ hγ hG => ?_, fun c => big_sh p pp f Ap ApPt n₀ p₀ hz hz' hAp hnp c,
    fun c => big_sh p pm f Am AmPt n₀ p₀ hzm hzm' hAm hnm c⟩
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p f hγ, ew_sh p pp hz hz' _ hγ, ew_sh p pm hzm hzm' _ hγ,
    V_fpmSh p pp f Ap ApPt p₀ hz hz' hγ hG (hAp γ hγ hG),
    V_fpmSh p pm f Am AmPt p₀ hzm hzm' hγ hG (hAm γ hγ hG),
    Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq, Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
  have hX := hs_le_of_adj_sh (p.V f γ) (ApPt γ) (AmPt γ)
    ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀) (hadj γ hγ hG)
  set nn := Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ) with hnn_def
  set a1 := ‖B.hsVec ((p.V f γ).comp (ApPt γ))‖ ^ 2 with ha1
  set a2 := ‖B.hsVec ((p.V f γ).comp (AmPt γ))‖ ^ 2 with ha2
  have hnn : 0 ≤ nn := mul_self_nonneg _
  have hcanc : (Gp p γ)⁻¹ ^ (2 * p₀) * (Gp p γ ^ p₀) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm p₀ 2, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hG.ne')]
  have e : (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
      (nn * ((Gp p γ ^ p₀) ^ 2 * a1) + nn * ((Gp p γ ^ p₀) ^ 2 * a2)) =
      nn * ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (a1 + a2)) := by
    rw [show (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
        (nn * ((Gp p γ ^ p₀) ^ 2 * a1) + nn * ((Gp p γ ^ p₀) ^ 2 * a2)) =
        nn * ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (a1 + a2)) *
          ((Gp p γ)⁻¹ ^ (2 * p₀) * (Gp p γ ^ p₀) ^ 2) by ring, hcanc, mul_one]
  rw [e]
  exact mul_le_mul_of_nonneg_left hX hnn

end

end Formalism.FourierDecayAlt.P.CutBP2
end

