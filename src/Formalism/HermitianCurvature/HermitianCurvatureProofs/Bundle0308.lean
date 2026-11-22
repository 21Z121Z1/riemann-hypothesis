import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFId
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0306
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0293
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0305
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0125

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPairPtw
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem topPD_cut_eq (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {χ χ' : ℝ → ℝ}
    (hχ : C6.IsCut0 χ) (hχ' : C6.IsCut0 χ') {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F)
    {ε : ℝ} (hε : 0 < ε) {w : List C.Letter} (hw : KB.CutWord P p.l0 w) (c : Fin (P.r + 1) → ℂ)
    (hγ : ¬ (0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (TBB.bigPt P.r c)) ∨
      ε < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (TBB.bigPt P.r c)) :
    topPD p (D.cutF p.T.base χ' F ε) (D.cutF p.T.base χ F ε) w c = topD p F w c := by
  rw [← topPD_self]
  have hV : ∀ H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      (∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g → H₁ g = H₂ g) →
      D.vecV p.T.base p.ν' p.m₀ H₁ (TBB.bigPt P.r c) = D.vecV p.T.base p.ν' p.m₀ H₂ (TBB.bigPt P.r c) :=
    fun H₁ H₂ h => vecV_congr_gt p.T.base p.ν' p.m₀ _ ε h hγ
  have hcut : ∀ χ₀ : ℝ → ℝ, C6.IsCut0 χ₀ → ∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g →
      D.cutF p.T.base χ₀ F ε g = F g := by
    intro χ₀ hχ₀ g _ hg
    have h1 : 1 ≤ Gf P.k P.r p.T.base.z p.T.base.z' g / ε := by rw [le_div_iff₀ hε]; linarith
    simp only [D.cutF, hχ₀.2.2 _ h1, Complex.ofReal_one, one_smul]
  have hP : topPair p (D.cutF p.T.base χ' F ε) (D.cutF p.T.base χ F ε) w (TBB.bigPt P.r c) =
      topPair p F F w (TBB.bigPt P.r c) := by
    unfold topPair
    by_cases h3 : w = []
    · rw [if_pos h3, if_pos h3]
      unfold KB.Pl.V
      rw [hV _ _ (hcut χ' hχ'), hV _ _ (hcut χ hχ)]
    · rw [if_neg h3, if_neg h3]
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hV _ _ (theta_cutF_gt p hCb hχ' hF hε hw e), hV _ _ (theta_cutF_gt p hCb hχ hF hε hw e)]
  unfold topPD
  rw [hP]

end place

theorem pairing_pointwise_all_levels_holds : NFPairPtwAll := by
  intro Cb
  refine ⟨0, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH χ' hχ' w hw _
  obtain ⟨hχ, hCb, hf, -, -, -⟩ := hH
  have hF : B.CkOn ⊤ (B.GV P.k P.r) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) :=
    ckOn_fpm p p₀ hf (Formalism.FourierDecayAlt.P.CutMP.ER.ckOn_const' _)
  refine Filter.Eventually.of_forall fun c => ?_
  set Gγ := D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (TBB.bigPt P.r c) with hGγ
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ (¬ (0 < Gγ) ∨ ε < Gγ) := by
    by_cases hG : 0 < Gγ
    · filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
      exact ⟨hε.1, Or.inr hε.2⟩
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ⟨hε, Or.inl hG⟩
  filter_upwards [hev] with ε hε
  exact topPD_cut_eq p hCb hχ hχ' hF hε.1 hw.1 c hε.2

theorem top_identity_of_domination_limits (hA : P5.ThmPActual) (h3 : NFTopDomAll) (s1 : NFPolFormAll) (s4 : NFBetaLimAll) :
    NFTopIdAll :=
  nfTopIdAll_of hA h3 s1 pairing_pointwise_all_levels_holds s4

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPol
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def midCut (χ' χ : ℝ → ℝ) : ℝ → ℝ := fun x => (χ' x + χ x) / 2

theorem isCut0_midCut {χ' χ : ℝ → ℝ} (h' : C6.IsCut0 χ') (h : C6.IsCut0 χ) : C6.IsCut0 (midCut χ' χ) := by
  obtain ⟨c1, ⟨d1, hd1, z1⟩, o1⟩ := h'
  obtain ⟨c2, ⟨d2, hd2, z2⟩, o2⟩ := h
  refine ⟨by unfold midCut; exact (c1.add c2).div_const 2, ⟨min d1 d2, lt_min hd1 hd2, fun x hx => ?_⟩, fun x hx => ?_⟩
  · simp only [midCut, z1 x (lt_of_lt_of_le hx (min_le_left _ _)), z2 x (lt_of_lt_of_le hx (min_le_right _ _))]
    norm_num
  · simp only [midCut, o1 x hx, o2 x hx]
    norm_num

def NFPolQuadAll : Prop :=
  P5.ThmPActual → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
      Integrable (topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w) ∧
      (pair0 p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
        (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re =
        ∫ c, topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c

def NFPairMidAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ χ' : ℝ → ℝ, C6.IsCut0 χ' → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      ∀ ε : ℝ, 0 < ε →
        (pair0 p (D.cutF p.T.base (midCut χ' χ) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base (midCut χ' χ) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re =
        (pair0 p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re / 4 +
        (pair0 p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re / 4 +
        (pair0 p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re / 2

def NFTopMidAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ χ' : ℝ → ℝ, C6.IsCut0 χ' → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      ∀ ε : ℝ, 0 < ε → ∀ c : Fin (P.r + 1) → ℂ,
        topD p (D.cutF p.T.base (midCut χ' χ) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c =
        topD p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c / 4 +
        topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c / 4 +
        topPD p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c / 2

theorem nfPolFormAll_of (s1 : NFPolQuadAll) (s2 : NFPairMidAll) (s3 : NFTopMidAll) : NFPolFormAll := by
  intro hA Cb
  obtain ⟨C1, H1⟩ := s1 hA Cb
  obtain ⟨C2, H2⟩ := s2 Cb
  obtain ⟨C3, H3⟩ := s3 Cb
  refine ⟨max C1 (max C2 C3), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH χ' hχ' w hw hN ε hε
  have m1 : C1 ≤ max C1 (max C2 C3) := le_max_left _ _
  have m2 : C2 ≤ max C1 (max C2 C3) := le_max_of_le_right (le_max_left _ _)
  have m3 : C3 ≤ max C1 (max C2 C3) := le_max_of_le_right (le_max_right _ _)
  have hχ : C6.IsCut0 χ := hH.1
  have hm := isCut0_midCut hχ' hχ
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  obtain ⟨iu, qu⟩ := H1 Wp Wq P p f A₀ p₀ χ' Y N (nfHyp_mono hH m1 hχ') w hw hN ε hε
  obtain ⟨iv, qv⟩ := H1 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH m1 hχ) w hw hN ε hε
  obtain ⟨im, qm⟩ := H1 Wp Wq P p f A₀ p₀ (midCut χ' χ) Y N (nfHyp_mono hH m1 hm) w hw hN ε hε
  have hpair := H2 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH m2 hχ) χ' hχ' w hw hN ε hε
  have htop := H3 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH m3 hχ) χ' hχ' w hw hN ε hε
  have e : topPD p (D.cutF p.T.base χ' F' ε) (D.cutF p.T.base χ F' ε) w = fun c =>
      2 * topD p (D.cutF p.T.base (midCut χ' χ) F' ε) w c - topD p (D.cutF p.T.base χ' F' ε) w c / 2 -
        topD p (D.cutF p.T.base χ F' ε) w c / 2 := by
    funext c
    have := htop c
    linarith
  have hi1 : Integrable (fun c => 2 * topD p (D.cutF p.T.base (midCut χ' χ) F' ε) w c) := im.const_mul 2
  have hi2 : Integrable (fun c => topD p (D.cutF p.T.base χ' F' ε) w c / 2) := iu.div_const 2
  have hi3 : Integrable (fun c => topD p (D.cutF p.T.base χ F' ε) w c / 2) := iv.div_const 2
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (hi1.sub hi2).sub hi3
  · have hi12 : Integrable (fun c => 2 * topD p (D.cutF p.T.base (midCut χ' χ) F' ε) w c -
        topD p (D.cutF p.T.base χ' F' ε) w c / 2) := hi1.sub hi2
    rw [e, integral_sub hi12 hi3, integral_sub hi1 hi2, integral_const_mul, integral_div, integral_div,
      ← qu, ← qv, ← qm, hpair]
    ring

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def xD (φ : ℝ → ℝ) : ℝ → ℝ := fun x => x * deriv φ x

def IsSCoef {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq) : Prop :=
  ∀ (s : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV P.k P.r) F → ∀ g ∈ C6.domL p.T.base ∅,
    ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (-s) : ℝ) : ℂ) •
        p.Θ.Θ w e (fun g' => ((Gf P.k P.r p.T.base.z p.T.base.z' g' ^ s : ℝ) : ℂ) • F g') g =
      ∑ q : Fin (Q + 1), ((s ^ (q : ℕ) : ℝ) : ℂ) • B.opApply (L q) F g

def NFUnfoldTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), w ≠ [] →
    D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      topD p H w c = (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
          Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c))) *
        ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P, Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 *
          ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c)))‖ ^ 2

def NFVMul : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (φ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt), D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) γ = ((φ (TBB.Gp p γ) : ℝ) : ℂ) • p.V F γ

def NFCutSup : Prop :=
  ∀ χ : ℝ → ℝ, C6.IsCut0 χ → ∀ q : ℕ, ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ∀ x : ℝ, 0 < x →
    |(xD^[q] (fun y => χ (y / ε))) x| ≤ K

def NFLeibV : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → ∀ w, KB.CutWord P p.l0 w → ∀ e : Wd.Ix (Fin w.length),
      ∃ (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq),
        (∀ q, B.SmoothCoef (C6.domL p.T.base ∅) (L q)) ∧ IsSCoef p w e Q L ∧
        ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ),
          B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
            p.V (p.Θ.Θ w e (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g)) γ =
              ∑ q : Fin (Q + 1), (((xD^[(q : ℕ)] φ) (TBB.Gp p γ) : ℝ) : ℂ) • p.V (B.opApply (L q) F) γ

def NFCoreN : Prop :=
  ∀ Cb : ℝ, ∃ Cc C₁ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → ∀ (Y : Finset ℝ) (w : List C.Letter), TBB.AdmW P p.l0 Y w →
    ∀ (e : Wd.Ix (Fin w.length)) (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq), IsSCoef p w e Q L →
    ∀ p₀ N : ℕ, w.length ≤ N → N ≤ 2 * p₀ →
      ∃ (m : ℕ) (Th : Fin m → B.DiffOp P.k P.r Wp Wq) (Mb : ℝ), 0 ≤ Mb ∧ (∀ t, NFOpOK C₁ p N (Th t)) ∧
        ∀ (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ), B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
            A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
          ∀ (q : Fin (Q + 1)) (ρ : M.Ty P) (c : Fin (P.r + 1) → ℂ), D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) →
            0 < TBB.Gp p (TBB.bigPt P.r c) →
            Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 *
                ‖B.hsVec ((p.TP.E ρ).comp
                  (p.V (B.opApply (L q) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀)) (TBB.bigPt P.r c)))‖ ^ 2 ≤
              Mb * TBB.Gp p (TBB.bigPt P.r c) ^ (2 * p₀ - N) *
                ∑ t, ‖B.hsVec (p.V (B.opApply (Th t) f) (TBB.bigPt P.r c))‖ ^ 2

def NFEmptyOps : Prop :=
  ∃ C₁ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (N : ℕ), ∃ Th₀ Th₁ : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th₀ ∧ NFOpOK C₁ p N Th₁ ∧
      ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r),
        B.opApply Th₀ F g = F g ∧ B.opApply Th₁ F g = ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • F g

theorem unfolding_top_term_holds : NFUnfoldTop := by
  intro Wp Wq _ _ _ _ _ _ P p H w c hw hloc _
  have hn : TBB.normC (fun _ => 1) w = 1 := by
    simp [TBB.normC]
  have hRR : p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c) =
      Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w (TBB.bigPt P.r c) (TBB.bigPt P.r c) := by
    rw [KB.Pl.RR, D.RRplace, dif_pos ⟨hloc, hloc⟩, dif_neg (Nat.not_succ_le_self _), if_pos rfl, if_neg hw]
  show (TBB.NP p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re = _
  rw [TBB.NP, hn, div_one, hRR, Top.topOf, Complex.re_ofReal_mul]
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hsq : ∀ v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp), (inner ℂ v v : ℂ).re = ‖v‖ ^ 2 :=
    fun v => by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [Complex.re_ofReal_mul, B.hsInner, hsq]
  simp only [TBB.TTp, KB.Pl.V]
  ring

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDM
section
namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def TypeNormMeas : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), JF.TransportedAlt P.k P.r A 0 → B.InCC A 0 Y → ∀ ρ : M.Ty P,
      AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        ‖B.hsVec ((p.TP.E ρ).comp (p.V Y (TBB.bigPt P.r c)))‖) volume

def VecVGPos : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (Y Y' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
    (∀ g ∈ B.GV P.k P.r, 0 < Gf P.k P.r p.T.base.z p.T.base.z' g → Y g = Y' g) → ∀ a : C.LPt, p.V Y a = p.V Y' a

def DopCC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base X → KB.CutWord P p.l0 w →
    ∀ e : Wd.Ix (Fin w.length), ∃ Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      (∀ g ∈ B.GV P.k P.r, 0 < Gf P.k P.r p.T.base.z p.T.base.z' g → Y g = p.Θ.Θ w e X g) ∧
        ∀ A : ℝ, B.InCC A 0 Y

def ScalarMeas : Prop :=
  ∀ (k r : ℕ) (TT : ℝ), Measurable (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) ∧
    Measurable (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c))

def EmptyMeas : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base X → AEStronglyMeasurable (topD p X []) volume

theorem ae_all_ne (r : ℕ) : ∀ᵐ c : Fin (r + 1) → ℂ, ∀ i, c i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  have h : volume ((fun c : Fin (r + 1) → ℂ => c i) ⁻¹' {0}) = 0 := by
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null _ (measure_singleton 0)
  have e : {a : Fin (r + 1) → ℂ | ¬a i ≠ 0} = (fun c : Fin (r + 1) → ℂ => c i) ⁻¹' {0} := by
    ext a; simp
  exact ae_iff.2 (by rw [e]; exact h)

theorem topDMeasCpt_of_parts (h1 : TypeNormMeas) (h2 : VecVGPos) (h3 : DopCC) (h4 : ScalarMeas) (h5 : EmptyMeas) :
    TopDMeasCpt := by
  intro Wp Wq _ _ _ _ _ _ P p X w Cb hD hX hw
  by_cases hw0 : w = []
  · subst hw0; exact h5 Wp Wq P p X hX
  choose Y hYe hYc using h3 Wp Wq P p X w Cb hD hX hw
  set TT : ℝ := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
  set A : ℝ := 9 * ((P.r : ℝ) + 1) * (((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + 1) with hA
  have hThr : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    have hr : (0 : ℝ) < 9 * ((P.r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hr, hA]
    nlinarith
  have hV : ∀ e a, p.V (p.Θ.Θ w e X) a = p.V (Y e) a := fun e a =>
    h2 Wp Wq P p _ _ (fun g hg hG => (hYe e g hg hG).symm) a
  obtain ⟨hn, hW⟩ := h4 P.k P.r TT
  set g : (Fin (P.r + 1) → ℂ) → ℝ := fun c =>
    ((((Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) * Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) /
        TBB.normC (fun _ => 1) w : ℝ) : ℂ) *
      ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ))).re with hg
  have hgm : AEStronglyMeasurable g volume := by
    have hdH : ∀ e ρ, Measurable (fun c : Fin (P.r + 1) → ℂ => Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ) := by
      intro e ρ
      unfold Top.dH
      exact ((hW.pow_const _).mul_const _).sqrt
    have hterm : ∀ e ρ, AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume := by
      intro e ρ
      have h1' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          ‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2) volume :=
        (h1 Wp Wq P p (Y e) A hThr (hYc e A) ρ).pow 2
      have h2' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable h1'
      have h3' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ)) volume :=
        (Complex.measurable_ofReal.comp ((hdH e ρ).mul (hdH e ρ))).aestronglyMeasurable
      exact h3'.mul h2'
    have hsum : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume :=
      Finset.aestronglyMeasurable_fun_sum _ fun e _ => Finset.aestronglyMeasurable_fun_sum _ fun ρ _ => hterm e ρ
    have hpre : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        (((Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) * Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) /
          TBB.normC (fun _ => 1) w : ℝ) : ℂ))) volume :=
      (Complex.measurable_ofReal.comp (((hn.sqrt.mul hn.sqrt).div_const _))).aestronglyMeasurable
    exact Complex.continuous_re.comp_aestronglyMeasurable (hpre.mul hsum)
  refine hgm.congr ?_
  filter_upwards [ae_all_ne P.r] with c hc
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc
  show g c = topD p X w c
  unfold topD TBB.Ew TBB.NP KB.Pl.RR D.RRplace
  rw [dif_pos ⟨hl, hl⟩, dif_neg (by omega), if_pos rfl, if_neg hw0]
  unfold Top.topOf
  simp only [hg]
  congr 3
  funext e
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self]
  show _ = _ * (((‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e X) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)
  rw [hV e]

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
end

