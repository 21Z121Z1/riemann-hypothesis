import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0305
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0302
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0057
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0193
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENFMain
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem thmBpAt_main4 (hA : P5.ThmPActual) (h1 : NFTopFormAll) (h2 : NFTopPtwAll) (h3 : NFTopDomAll)
    (h4 : NFTopIdAll) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, c₃, Cc, Cc', h⟩ := thmBpAt_main2 hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := limEvT_fpm_of_NF hA h1 h2 h3 h4 Cb
  refine ⟨C₄, c₃, Cc, Cc', Cn, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3
    hth4 hN2 hexp hWG hLG hI5 hBd
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3 hexp hWG hLG
    hI5 (hn Wp Wq P p f A₀ p₀ χ Y N ⟨hχ, hCb, hf, hfA, hth4, hN2⟩) hBd

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDom
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def NFOpOK (C : ℝ) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (N : ℕ) (Th : B.DiffOp P.k P.r Wp Wq) : Prop :=
  B.SmoothCoef (B.GPos p.T.base) Th ∧ B.Commutes p.T.base (B.GPos p.T.base) Th ∧
    CutMP.GlobCoef Th (C * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1)) ∧
    (B.opOrder Th : ℝ) ≤ C * CutMP.nDim P.k P.r * ((N : ℝ) + 1)

def NFDomZero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ),
    ¬ (D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)) → topD p H w c = 0

def NFDomPtw : Prop :=
  ∀ Cb : ℝ, ∃ Cc C₁ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ) (w : List C.Letter), TBB.AdmW P p.l0 Y w → w.length ≤ N →
      ∃ (m : ℕ) (Th : Fin m → B.DiffOp P.k P.r Wp Wq) (Mb : ℝ), 0 ≤ Mb ∧ (∀ t, NFOpOK C₁ p N (Th t)) ∧
        ∀ (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ), NFHyp Cb Cc p f A₀ p₀ χ N →
        ∀ ε : ℝ, 0 < ε → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) →
          0 < TBB.Gp p (TBB.bigPt P.r c) →
          ‖topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c‖ ≤
            Mb * ∑ t, ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
              TBB.Ew p (fun _ => 1) (B.opApply (Th t) f) (P.r + 1) [] (TBB.bigPt P.r c)

def DominatedL2OperatorBound : Prop :=
  ∀ Cb C₁ : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ Th : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th →
      Integrable (fun c : Fin (P.r + 1) → ℂ => ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
        TBB.Ew p (fun _ => 1) (B.opApply Th f) (P.r + 1) [] (TBB.bigPt P.r c))

def NFDomMeas : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
      AEStronglyMeasurable (topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w)
        volume

theorem domination_at_zero_holds : NFDomZero := by
  intro Wp Wq _ _ _ _ _ _ P p H w c hc
  unfold topD TBB.Ew TBB.NP KB.Pl.RR
  generalize TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) = a
  generalize TBB.normC (fun x => 1) w = b
  generalize TBB.bigPt P.r c = x at hc ⊢
  unfold D.RRplace
  by_cases hl : D.IsLocPt x (P.r + 1)
  · have hG : ¬ 0 < TBB.Gp p x := fun h => hc ⟨hl, h⟩
    rw [dif_pos ⟨hl, hl⟩, dif_neg (by omega)]
    have hv : ∀ H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp), D.vecV p.T.base p.ν' p.m₀ H' x = 0 := by
      intro H'
      unfold D.vecV
      rw [dif_neg]
      rintro ⟨-, h⟩
      apply hG
      unfold TBB.Gp
      exact h
    have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec
      ext i
      simp
    have hi0 : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
      simp [B.hsInner, h0]
    simp [hv]
    split_ifs with hw
    · simp [hi0]
    · unfold Top.topOf
      simp [hv, hi0]
  · simp [hl]

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopPtw
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section vec

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vecV_congr_gt (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt)
    {H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (δ : ℝ)
    (h : ∀ g ∈ B.GV k r, δ < Gf k r Bs.z Bs.z' g → H₁ g = H₂ g)
    (hq : ¬ (0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q) ∨ δ < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q) :
    D.vecV Bs ν' m₀ H₁ q = D.vecV Bs ν' m₀ H₂ q := by
  unfold D.vecV
  by_cases hq' : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos hq']
    have hδ : δ < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q := hq.resolve_left (not_not.2 hq'.2)
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose hq'.1 h'.choose_spec.2.1
      have hpos : δ < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ hδ
      have e := Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae Bs h'.choose
        (D.muR Bs h'.choose (hq'.1.2 ▸ D.ptPerm q)) H₁ H₂ 1 (by
        filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
        simp only [D.orbIntegrand, B.rho, one_smul]
        rw [h _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ) (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos)])
      rw [e, one_smul]
    · simp only [dif_neg h']
  · simp only [dif_neg hq']

end vec

section lift

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem theta_cutF_gt (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {χ : ℝ → ℝ}
    (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F) {ε : ℝ} (hε : 0 < ε)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) (e : Wd.Ix (Fin w.length)) :
    ∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g →
      p.Θ.Θ w e (D.cutF p.T.base χ F ε) g = p.Θ.Θ w e F g := by
  intro g hg hgε
  obtain ⟨nf, fib, o, κ, Dop, -, hIn, -, -, hΘ⟩ := hCb w hw e
  have hdom : g ∈ C6.domL p.T.base ∅ := ⟨hg, lt_trans hε hgε, fun l hl => by simp at hl⟩
  rw [hΘ _ g hdom, hΘ _ g hdom]
  have hlen : ∀ T ∈ Dop, T.word.length ≤ o := by
    intro T hT
    obtain ⟨_, _, _, _, _, _, _, hl, _⟩ := hIn.2.2 T hT
    omega
  have hc : B.CkOn ⊤ (B.GV P.k P.r) (D.cutF p.T.base χ F ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hF ε
  have hsub := Formalism.FourierDecayAlt.P.PBE.opApply_subGV Dop hlen (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hc)
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF) g hg
  have hGc : Continuous (fun g : B.Mat P.k P.r => Gf P.k P.r p.T.base.z p.T.base.z' g) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
  have hU : IsOpen {x : B.Mat P.k P.r | ε < Gf P.k P.r p.T.base.z p.T.base.z' x} := isOpen_lt continuous_const hGc
  have h0 := Formalism.FourierDecayAlt.P.PBE.opApply_zero_near Dop (F := D.cutF p.T.base χ F ε - F) hU (by
    intro x _ hx
    replace hx : ε < Gf P.k P.r p.T.base.z p.T.base.z' x := hx
    have h1 : 1 ≤ Gf P.k P.r p.T.base.z p.T.base.z' x / ε := by rw [le_div_iff₀ hε]; linarith
    simp only [Pi.sub_apply, D.cutF, hχ.2.2 _ h1, Complex.ofReal_one, one_smul, sub_self]) g hg hgε
  rw [hsub] at h0
  exact sub_eq_zero.1 h0

end lift

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rrTop_cutF_eq (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {χ : ℝ → ℝ}
    (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F) {ε : ℝ} (hε : 0 < ε)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) (γ : C.LPt)
    (hγ : ¬ (0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ) ∨
      ε < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ) :
    p.RR (D.cutF p.T.base χ F ε) (P.r + 1) w γ γ = p.RR F (P.r + 1) w γ γ := by
  have hV : ∀ H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      (∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g → H₁ g = H₂ g) →
      D.vecV p.T.base p.ν' p.m₀ H₁ γ = D.vecV p.T.base p.ν' p.m₀ H₂ γ :=
    fun H₁ H₂ h => vecV_congr_gt p.T.base p.ν' p.m₀ γ ε h hγ
  have hcut : ∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g → D.cutF p.T.base χ F ε g = F g := by
    intro g _ hg
    have h1 : 1 ≤ Gf P.k P.r p.T.base.z p.T.base.z' g / ε := by rw [le_div_iff₀ hε]; linarith
    simp only [D.cutF, hχ.2.2 _ h1, Complex.ofReal_one, one_smul]
  unfold KB.Pl.RR D.RRplace
  by_cases h1 : D.IsLocPt γ (P.r + 1) ∧ D.IsLocPt γ (P.r + 1)
  · rw [dif_pos h1, dif_pos h1, dif_neg (by omega), dif_neg (by omega), if_pos rfl, if_pos rfl]
    by_cases h3 : w = []
    · rw [if_pos h3, if_pos h3, hV _ _ hcut]
    · rw [if_neg h3, if_neg h3]
      unfold Top.topOf
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hV _ _ (theta_cutF_gt p hCb hχ hF hε hw e)]
  · rw [dif_neg h1, dif_neg h1]

theorem nFTopPtw_of (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {χ : ℝ → ℝ}
    (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) :
    ∀ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), topD p (D.cutF p.T.base χ F ε) w c = topD p F w c := by
  intro c
  set γ := TBB.bigPt P.r c
  set Gγ := D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ with hGγ
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ (¬ (0 < Gγ) ∨ ε < Gγ) := by
    by_cases hG : 0 < Gγ
    · filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
      exact ⟨hε.1, Or.inr hε.2⟩
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ⟨hε, Or.inl hG⟩
  filter_upwards [hev] with ε hε
  unfold topD TBB.Ew TBB.NP
  rw [rrTop_cutF_eq p hCb hχ hF hε.1 hw γ hε.2]

end place

theorem top_pointwise_all_levels_holds : NFTopPtwAll := by
  intro Cb
  refine ⟨0, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw _
  obtain ⟨hχ, hCb, hf, -, -, -⟩ := hH
  have hF : B.CkOn ⊤ (B.GV P.k P.r) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) :=
    ckOn_fpm p p₀ hf (Formalism.FourierDecayAlt.P.CutMP.ER.ckOn_const' _)
  exact Filter.Eventually.of_forall fun c => nFTopPtw_of p hCb hχ hF hw.1 c

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
section
namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory
open scoped ENNReal

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ptBound_main (hA : P5.ThmPActual) (Cb : ℝ) : ∃ C₂ c₃ Cc Cc' : ℝ, 0 < C₂ ∧
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (q : KB.Pl P Wp Wq)
      (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ A : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      1 ≤ Λ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P q.l0 q.T.base Cb q.Θ → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      TBBx5.WaveGrid q nn Y Λ K N → TBBx5.LiftGrid q nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound q nn (apx (D.cutF q.T.base χ F ε) n) Y K N) →
      (∀ w, TBB.AdmW P q.l0 Y w → w.length ≤ N → DomCut q χ F w) →
      LimBd q nn F Y N → TBB.PtBound q F (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  obtain ⟨C₂, hC₂, hPt⟩ := ptBound_dec_all hA
  obtain ⟨c₃, hc₃⟩ := limTopN_cut_of_inCC
  obtain ⟨Cc, hCc⟩ := limZeroN_of_formLimit Cb
  obtain ⟨Cc', hE⟩ := limE_of_limEvT hA Cb
  refine ⟨C₂, c₃, Cc, Cc', hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P q F Λ A χ nn Y K N hΛ hK hKN hχ hnn hCb hF hFA hth1 hth2 hth3 hWG hLG hI5 hDom hBd
  exact hPt Wp Wq P q F Λ 1 χ nn Y K N Cb hΛ one_pos hK hKN hχ hnn hCb hF hWG hLG hI5
    (hc₃ Wp Wq P q nn χ F A hth1 hχ hFA hF)
    (fun ε hε => hCc Wp Wq P q F χ ε A N nn Y hCb hχ hε hF hFA hth2)
    (hE Wp Wq P q F χ nn A N Y hCb hχ (fun y => (hnn y).le) hF hFA hth3 (limEvT_of_dom q hχ hF Y N hDom) hBd)
    (lemB_one q F)

section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

theorem ttp_eq (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') : TTp q = TTp p := by
  unfold Formalism.FourierDecayAlt.TBB.TTp
  rw [hz, hz']
  rfl

theorem isBoundedBilinearMap_compSh :
    IsBoundedBilinearMap ℝ (fun q : (Wq →L[ℂ] Wp) × (Wq' →L[ℂ] Wq) => q.1.comp q.2) where
  add_left x₁ x₂ y := ContinuousLinearMap.add_comp x₁ x₂ y
  smul_left c x y := by ext v; simp
  add_right x y₁ y₂ := ContinuousLinearMap.comp_add x y₁ y₂
  smul_right c x y := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply]
    exact ContinuousLinearMap.map_smul_of_tower x c (y v)
  bound := ⟨1, one_pos, fun x y => by simpa using ContinuousLinearMap.opNorm_comp_le x y⟩

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ckOn_compSh {k r : ℕ} {f : B.Mat k r → (Wq →L[ℂ] Wp)} {A : B.Mat k r → (Wq' →L[ℂ] Wq)}
    (hf : B.CkOn ⊤ (B.GV k r) f) (hA : B.CkOn ⊤ (B.GV k r) A) :
    B.CkOn ⊤ (B.GV k r) (fun g => (f g).comp (A g)) := by
  intro g₀ hg₀
  obtain ⟨U1, f1, hU1, hg1, hc1, he1⟩ := hf g₀ hg₀
  obtain ⟨U2, f2, hU2, hg2, hc2, he2⟩ := hA g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => (f1 g).comp (f2 g), hU1.inter hU2, ⟨hg1, hg2⟩, ?_,
    fun g hg hgv => by
      show (f g).comp (A g) = (f1 g).comp (f2 g)
      rw [he1 g hg.1 hgv, he2 g hg.2 hgv]⟩
  have hp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (f1 g, f2 g)) (U1 ∩ U2) := by
    first
    | exact (hc1.mono Set.inter_subset_left).prodMk (hc2.mono Set.inter_subset_right)
    | exact (hc1.mono Set.inter_subset_left).prod (hc2.mono Set.inter_subset_right)
  exact isBoundedBilinearMap_compSh.contDiff.comp_contDiffOn hp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ckOn_fpmSh (q : KB.Pl (shP P u u') Wp Wq') {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    {A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)} (p₀ : ℕ) (hf : B.CkOn ⊤ (B.GV P.k P.r) f)
    (hA : B.CkOn ⊤ (B.GV P.k P.r) A) : B.CkOn ⊤ (B.GV P.k P.r) (fpmSh q f A p₀) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : B.Mat P.k P.r => ((Gf P.k P.r q.T.base.z q.T.base.z' g ^ p₀ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf q.T.base.z q.T.base.z').pow p₀)
  exact Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hc (ckOn_compSh hf hA)

end sh

def PolyOp {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (d : ℕ) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  ∃ (n : ℕ) (c : Fin n → B.Mat k r → ℂ) (L : Fin n → (Wq' →L[ℂ] Wq)),
    (∀ i, U.IsPolyDeg d (c i)) ∧ ∀ g, A g = ∑ i, c i g • L i

def FpmShDecay : Prop :=
  ∀ (P : M.Par) (Wp Wq Wq' : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (u u' : ℕ → ℝ) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (A₀ : ℝ) (d p₀ : ℕ),
    (∀ m : ℕ, B.InCC A₀ m f) → PolyOp d A →
    ∀ m : ℕ, B.InCC (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d) m (fpmSh q f A p₀)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_eq (hA : P5.ThmPActual) (hN : NormAtShOfAmaps) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ)
    (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
      [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
      (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp)
      (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
      (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq))
      (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₁ : ℝ) (n₀ p₀ : ℕ)
      (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' →
      pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → B.CkOn ⊤ (B.GV P.k P.r) Ap → B.CkOn ⊤ (B.GV P.k P.r) Am →
      (∀ m : ℕ, B.InCC A₁ m (fpmSh pp f Ap p₀)) → (∀ m : ℕ, B.InCC A₁ m (fpmSh pm f Am p₀)) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₁ →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₁ →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₁ →
      AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N →
      TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) →
      (∀ w, TBB.AdmW (shP P up up') pp.l0 Yp w → w.length ≤ N → DomCut pp χ (fpmSh pp f Ap p₀) w) →
      (∀ w, TBB.AdmW (shP P um um') pm.l0 Ym w → w.length ≤ N → DomCut pm χ (fpmSh pm f Am p₀) w) →
      LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₂, c₃, Cc, Cc', hC₂, hPt⟩ := ptBound_main hA Cb
  obtain ⟨C₄, hC₄⟩ := thmBpOfPartsSh C₃ CΛ C₀ C₂ 0 hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, c₃, Cc, Cc', ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₁ n₀ p₀ χ nnp nnm
    Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf hAp hAm hdp hdm hth1 hth2
    hth3 hAms hexp hWGp hLGp hWGm hLGm hI5p hI5m hDp hDm hBdp hBdm
  have hNorm := hN P Wp Wq Wqp Wqm up up' um um' p pp pm f Ap Am ApPt AmPt b n₀ p₀ hzp hzp' hzm hzm' hAms
  have hReg := Formalism.FourierDecayAlt.P.regularity_at_place p f b C₃ (2 * p₀ + n₀) (by linarith) hexp
  have hPp := hPt Wp Wqp (shP P up up') pp (fpmSh pp f Ap p₀) Λ A₁ χ nnp Yp K N hΛ hK hKN hχ hnnp hDDp
    (ckOn_fpmSh pp p₀ hf hAp) hdp hth1 hth2 hth3 hWGp hLGp hI5p hDp hBdp
  have hPm := hPt Wp Wqm (shP P um um') pm (fpmSh pm f Am p₀) Λ A₁ χ nnm Ym K N hΛ hK hKN hχ hnnm hDDm
    (ckOn_fpmSh pm p₀ hf hAm) hdm hth1 hth2 hth3 hWGm hLGm hI5m hDm hBdm
  exact hC₄ P Wp Wq Wqp Wqm up up' um um' p pp pm f _ _ b Λ 1 n₀ p₀ hb hΛ hΛb one_pos (by simp) hT hn₀ hp₀
    (ttp_eq p pp hzp hzp') (ttp_eq p pm hzm hzm') hNorm hPp hPm hReg

end

end Formalism.FourierDecayAlt.P.CutBPEq
end

