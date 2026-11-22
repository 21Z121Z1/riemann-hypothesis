import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0178
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0177
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0070
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0181
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0202
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0187
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0132
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0063
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0191
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0189
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0042
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0034

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LocOp

def lcChi (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem lcChi_zero {x : ℝ} (hx : x < 1 / 2) : lcChi x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem lcChi_one {x : ℝ} (hx : 1 ≤ x) : lcChi x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem isCut0_lcChi : C6.IsCut0 lcChi :=
  ⟨Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const),
    ⟨1 / 2, by norm_num, fun _ hx => lcChi_zero hx⟩, fun _ hx => lcChi_one hx⟩

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem wR_lie {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) :
    ∀ x ∈ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR w, B.inLie k r x.2 :=
  fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (u := []) (by simp) hw x (by simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL] using hx)

theorem rw_congr_GV {F₀ : Type} [NormedAddCommGroup F₀] [NormedSpace ℂ F₀] {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → F₀} (h : ∀ g ∈ B.GV k r, g ∈ O → f₁ g = f₂ g) {w : List (B.Mat k r)}
    (hw : ∀ X ∈ w, B.inLie k r X) : ∀ g ∈ B.GV k r, g ∈ O → B.Rw w f₁ g = B.Rw w f₂ g := by
  intro g hg hgO
  rw [← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR, ← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_congr_loc (wR_lie hw) hO h g hg hgO

theorem opApply_congr_GV (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV k r, g ∈ O → f₁ g = f₂ g) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opApply Θ f₁ g = B.opApply Θ f₂ g := by
  intro g hg hgO
  unfold B.opApply
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [rw_congr_GV hO h T.word_lie g hg hgO]

theorem opAdj_congr_GV (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV k r, g ∈ O → f₁ g = f₂ g) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opAdj Θ f₁ g = B.opAdj Θ f₂ g := by
  intro g hg hgO
  unfold B.opAdj
  congr 1
  refine List.map_congr_left fun T _ => ?_
  have h' : ∀ x ∈ B.GV k r, x ∈ O → T.coefAdj x (f₁ x) = T.coefAdj x (f₂ x) := fun x hx hxO => by
    rw [h x hx hxO]
  have hrev : ∀ X ∈ T.word.reverse, B.inLie k r X := fun X hX => T.word_lie X (List.mem_reverse.1 hX)
  rw [rw_congr_GV hO h' hrev g hg hgO]

end gen

section place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem rep (hAg : LT.AgreeOm) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {Cb A₀ : ℝ} (hB : BuiltOW Cb S T f χ ν' m₀ top A₀) (v : Fin S.f) {A Bg δ : ℝ} {J : GFn S v}
    (hBg : 2 * ((S.G.r : ℝ) + 1) ≤ Bg) (hJ : LocCC S T v A Bg J) (hδ : 0 < δ) :
    ∃ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧ CCg S v A Bg F ∧
      (∀ g ∈ B.GV S.G.k S.G.r, Gf S.G.k S.G.r (T v).base.z (T v).base.z' g < 3 * δ / 8 → F g = 0) ∧
      ∀ g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z', 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g →
        J g = B.JF (T v).base F g := by
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  obtain ⟨F₀, hF₀c, hF₀g, hF₀e⟩ := hJ.2 (δ / 4) (by positivity)
  have hε : (0 : ℝ) < 3 * δ / 4 := by positivity
  obtain ⟨δ', -, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div isCut0_lcChi hε
  obtain ⟨hFc, hFg⟩ := gcut_graded (T v).base.z (T v).base.z' (fun x => lcChi (x / (3 * δ / 4))) (δ' * (3 * δ / 4))
    hcut hBg hF₀c hF₀g
  refine ⟨D.cutF (T v).base lcChi F₀ (3 * δ / 4), hFc, hFg, ?_, ?_⟩
  · intro g _ hg
    have h1 : Gf S.G.k S.G.r (T v).base.z (T v).base.z' g / (3 * δ / 4) < 1 / 2 := by
      rw [div_lt_iff₀ hε]; linarith
    simp [D.cutF, lcChi_zero h1]
  · intro g hg hG
    refine hAg _ _ _ _ (T v).base J _ (Set.Ioi (3 * δ / 4)) hJ.1 ?_ g hg hG
    intro q hq hGq
    have hGq' : 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) := hGq
    have hx : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT := ⟨hq.1, by rw [hTT]; exact hq.2⟩
    rw [hF₀e q hx (by unfold GfP; linarith), Formalism.FourierDecayAlt.P.JCTx2.JF_cutF]
    have h1 : 1 ≤ Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) / (3 * δ / 4) := by
      rw [le_div_iff₀ hε]; linarith
    rw [lcChi_one h1]
    simp

theorem isOpen_omPlus_inter_lt {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℝ) :
    IsOpen (Q.OmPlus k r z z' ∩ {g | c < Gf k r z z' g}) :=
  (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z').inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont z z'))

end place

end LocOp

namespace LocOp

section place2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem thr_of {k r : ℕ} {o : ℕ} {A d Bg : ℝ} (hd : 0 ≤ d) (hBg : 0 ≤ Bg)
    (hA : 12 * ((r : ℝ) + 1) * nDim k r ^ 2 + 6 * (r : ℝ) * (o : ℝ) + d + 2 * Bg * ((o : ℝ) + 1) ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r (A - Bg * o) o := by
  have ho : (0 : ℝ) ≤ (o : ℝ) := Nat.cast_nonneg o
  have hBo : 0 ≤ Bg * (o : ℝ) := mul_nonneg hBg ho
  exact jdc_thrW o (A - Bg * o) d hd (by nlinarith)

end place2

end LocOp

theorem jALocOp_of_tools (hOp : LT.OpCCg) (hAg : LT.AgreeOm) (hTh : LT.ThetaJApply) : JALocOp := by
  refine ⟨12, 2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Θ d Bg A J hd hBg hAA hCut hA hJ hFF
  have hBg0 : 0 ≤ Bg := le_trans (by positivity) hBg
  have hBo : 0 ≤ Bg * (B.opOrder Θ : ℝ) := mul_nonneg hBg0 (Nat.cast_nonneg _)
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hFc, hFg, hFz, hFe⟩ := LocOp.rep hAg hB v hBg hJ hδ
  obtain ⟨⟨hc, hg⟩, -⟩ := hOp _ _ _ _ (T v).base Θ d Bg A (3 * δ / 8) F (by positivity) hBg0 hAA.1 hCut hFc hFg hFz
  refine ⟨B.opApply Θ F, hc, fun m => inCC_antiA (by linarith) (hg m), fun x hx hG => ?_⟩
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
  have hgO := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hGx : 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := by
    have : δ ≤ Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := hG
    linarith
  rw [LocOp.opApply_congr_GV Θ (LocOp.isOpen_omPlus_inter_lt (T v).base.z (T v).base.z' (3 * δ / 4)) (f₁ := J)
    (f₂ := B.JF (T v).base F) (fun g hg hgO => hFe g ⟨hg, hgO.1⟩ hgO.2) _ hgO.1 ⟨hgO.2, hGx⟩]
  have hIn : B.InCC (A - Bg * (B.opOrder Θ : ℝ)) (B.opOrder Θ) F := hFg (B.opOrder Θ)
  exact hTh _ _ _ _ (T v).base Θ _ F (LocOp.thr_of hd hBg0 hA) hAA.1 hAA.2 hFc hIn _ hgO

theorem jALocAdj_of_tools (hOp : LT.OpCCg) (hAg : LT.AgreeOm) (hTh : LT.ThetaJ) : JALocAdj := by
  refine ⟨12, 2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Θ d Bg A J hd hBg hAA hCut hA hJ hFF
  have hBg0 : 0 ≤ Bg := le_trans (by positivity) hBg
  have hBo : 0 ≤ Bg * (B.opOrder Θ : ℝ) := mul_nonneg hBg0 (Nat.cast_nonneg _)
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hFc, hFg, hFz, hFe⟩ := LocOp.rep hAg hB v hBg hJ hδ
  obtain ⟨-, ⟨hc, hg⟩⟩ := hOp _ _ _ _ (T v).base Θ d Bg A (3 * δ / 8) F (by positivity) hBg0 hAA.1 hCut hFc hFg hFz
  refine ⟨B.opAdj Θ F, hc, fun m => inCC_antiA (by linarith) (hg m), fun x hx hG => ?_⟩
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
  have hgO := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hGx : 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := by
    have : δ ≤ Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := hG
    linarith
  rw [LocOp.opAdj_congr_GV Θ (LocOp.isOpen_omPlus_inter_lt (T v).base.z (T v).base.z' (3 * δ / 4)) (f₁ := J)
    (f₂ := B.JF (T v).base F) (fun g hg hgO => hFe g ⟨hg, hgO.1⟩ hgO.2) _ hgO.1 ⟨hgO.2, hGx⟩]
  have hIn : B.InCC (A - Bg * (B.opOrder Θ : ℝ)) (B.opOrder Θ) F := hFg (B.opOrder Θ)
  set UU : Set (B.Mat S.G.k S.G.r) := {g | g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' ∧
    3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g} with hUU
  have hCkJ : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') J := jdc_ckOn_om _ _ hJ.1.1
  have hCk : B.CkOn ⊤ UU (B.JF (T v).base F) := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hc', he⟩ := hCkJ g₀ hg₀.1
    refine ⟨U ∩ (Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
        {g | 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g}), f',
      hU.inter (LocOp.isOpen_omPlus_inter_lt _ _ _), ⟨hgU, hg₀.1.2, hg₀.2⟩, hc'.mono Set.inter_subset_left, fun g hg hgG => ?_⟩
    rw [← hFe g ⟨hgG, hg.2.1⟩ hg.2.2]
    exact he g hg.1 hgG
  exact (hTh _ _ _ _ (T v).base Θ _ F UU (LocOp.thr_of hd hBg0 hA) hAA.1 hAA.2 hFc hIn (fun g hg => hg.1)
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.sCkOn_mono le_top hCk)).2 _ ⟨hgO, hGx⟩

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocPhi
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

theorem lphi_log_deriv (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv (m + 1) Real.log x‖ = (m.factorial : ℝ) * (x ^ (m + 1))⁻¹ := by
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
  congr 1
  have e : (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_neg, zpow_natCast, norm_inv, norm_pow, Real.norm_of_nonneg hx.le]

theorem lphi_deriv_bdd {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hld : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C)
    {a : ℝ} (ha : 0 < a) (j : ℕ) : ∃ D : ℝ, ∀ x, a < x → ‖iteratedDeriv j φ x‖ ≤ D := by
  choose C hC using hld
  set Φ : ℝ → ℝ := fun u => φ (Real.exp u) with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := hφ
  set s : Set ℝ := Set.Ioi a with hs
  have hso : IsOpen s := isOpen_Ioi
  set K : ℝ := ∑ i ∈ Finset.range (j + 1), |C i| with hK
  have hKi : ∀ i ≤ j, |C i| ≤ K := fun i hi =>
    Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  set M : ℝ := max 1 a⁻¹ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  set Dd : ℝ := (j.factorial : ℝ) * M with hDd
  refine ⟨(j.factorial : ℝ) * K * Dd ^ j, fun x hx => ?_⟩
  have hx0 : 0 < x := ha.trans hx
  have hxs : x ∈ s := hx
  have hlogc : ContDiffOn ℝ ∞ Real.log s :=
    Real.contDiffOn_log.mono fun y hy => ne_of_gt (ha.trans (show a < y from hy))
  have hFdB := norm_iteratedFDerivWithin_comp_le (n := j) (N := ∞) (g := Φ) (f := Real.log) (t := Set.univ)
    hΦ.contDiffOn hlogc (by exact_mod_cast le_top) uniqueDiffOn_univ hso.uniqueDiffOn (Set.mapsTo_univ _ _) hxs
    (C := K) (D := Dd) (fun i hi => by
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have := hC i x hx0
      unfold LE.ld at this
      rw [Real.norm_eq_abs]
      exact this.trans ((le_abs_self _).trans (hKi i hi)))
    (fun i hi1 hij => by
      rw [iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [lphi_log_deriv m hx0]
      have hxi : (x ^ (m + 1))⁻¹ ≤ M ^ (m + 1) := by
        rw [← inv_pow]
        exact pow_le_pow_left₀ (inv_nonneg.2 hx0.le)
          ((inv_anti₀ ha hx.le).trans (le_max_right _ _)) _
      have hf1 : (m.factorial : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
      have hj1 : (1 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
      have hjp : (j.factorial : ℝ) ≤ (j.factorial : ℝ) ^ (m + 1) := le_self_pow₀ hj1 (by omega)
      rw [hDd, mul_pow]
      exact mul_le_mul (hf1.trans hjp) hxi (by positivity) (by positivity))
  rw [iteratedFDerivWithin_of_isOpen j hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hFdB
  have heq : (Φ ∘ Real.log) =ᶠ[nhds x] φ := by
    filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
    simp [hΦdef, Real.exp_log (show (0 : ℝ) < y from hy)]
  rw [← heq.iteratedDeriv_eq]
  exact hFdB

theorem lphi_cut {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hld : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C)
    {δ : ℝ} (hδ : 0 < δ) : ∃ (h : ℝ → ℝ) (ε' : ℝ), U.IsCutG ε' h ∧ ∀ x, δ ≤ x → h x = φ x := by
  set χ₀ : ℝ → ℝ := fun y => Real.smoothTransition (2 * y - 1) with hχ₀
  have hχ : C6.IsCut0 χ₀ := by
    refine ⟨Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const),
      ⟨1 / 2, by norm_num, fun y hy => Real.smoothTransition.zero_of_nonpos (by linarith)⟩,
      fun y hy => Real.smoothTransition.one_of_one_le (by linarith)⟩
  obtain ⟨δ₀, hδ₀, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div hχ hδ
  set ψ : ℝ → ℝ := fun x => χ₀ (x / δ) with hψ
  have hε : 0 < δ₀ * δ := mul_pos hδ₀ hδ
  have hψ1 : ∀ x, δ ≤ x → ψ x = 1 := fun x hx =>
    hχ.2.2 _ (by rw [le_div_iff₀ hδ]; linarith)
  have hψ0 : ∀ x, x < δ₀ * δ → ψ x = 0 := hcut.2.2
  have hφc := smoothLog_contDiffOn hφ
  refine ⟨fun x => ψ x * φ x, δ₀ * δ, ⟨?_, ?_, fun x hx => by simp [hψ0 x hx]⟩,
    fun x hx => by simp [hψ1 x hx]⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < δ₀ * δ
    · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      simp [hψ0 y hy]
    · have hx0 : 0 < x := lt_of_lt_of_le hε (not_lt.1 hx)
      exact hcut.1.contDiffAt.mul (hφc.contDiffAt (isOpen_Ioi.mem_nhds hx0))
  · intro q
    set a : ℝ := δ₀ * δ / 2 with ha
    have ha0 : 0 < a := by positivity
    choose cψ hcψ using hcut.2.1
    choose D hD using fun j => lphi_deriv_bdd hφ hld ha0 j
    refine ⟨∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)|, fun x => ?_⟩
    have hS0 : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)| :=
      Finset.sum_nonneg fun i _ => by positivity
    by_cases hx : x < δ₀ * δ
    · have e : (fun x => ψ x * φ x) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        simp [hψ0 y hy]
      rw [e.iteratedDeriv_eq]
      simp only [iteratedDeriv_const]
      split_ifs <;> simpa using hS0
    · have hxa : a < x := by linarith [not_lt.1 hx]
      set s : Set ℝ := Set.Ioi a with hs
      have hso : IsOpen s := isOpen_Ioi
      have hxs : x ∈ s := hxa
      have hφs : ContDiffOn ℝ ∞ φ s := hφc.mono fun y hy => ha0.trans (show a < y from hy)
      have hL := norm_iteratedFDerivWithin_mul_le (N := ∞) (hcut.1.contDiffOn (s := s)) hφs hso.uniqueDiffOn
        hxs (n := q) (by exact_mod_cast le_top)
      rw [iteratedFDerivWithin_of_isOpen q hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hL
      refine hL.trans (Finset.sum_le_sum fun i hi => ?_)
      rw [iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        iteratedFDerivWithin_of_isOpen (q - i) hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have h1 : ‖iteratedDeriv i ψ x‖ ≤ |cψ i| := (hcψ i x).trans (le_abs_self _)
      have h2 : ‖iteratedDeriv (q - i) φ x‖ ≤ |D (q - i)| := (hD (q - i) x hxa).trans (le_abs_self _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _) (by positivity)

theorem local_phi_transfer_holds : JALocPhi := by
  refine ⟨2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v φ Bg A J hφ hld hBg hJ hFF
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hF1, hF2, hF3⟩ := hJ.2 δ hδ
  obtain ⟨h, ε', hcut, hhφ⟩ := lphi_cut hφ hld hδ
  obtain ⟨hck, hcc⟩ := gcut_graded (T v).base.z (T v).base.z' h ε' hcut (A := A) hBg hF1 hF2
  refine ⟨fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g, hck, hcc, fun x hx hG => ?_⟩
  have e1 : (fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g) = D.cutF (T v).base h F 1 := by
    funext g; simp [D.cutF, GfP]
  rw [e1, Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, div_one, ← hF3 x hx hG]
  simp only [mulG]
  unfold GfP at hG
  rw [hhφ _ hG]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAQQ
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

def JAAssembleQQ : Prop :=
  JDHatOpQQ → JDHatBdd → JDJComm → JDCCLower → TransferSquareIntegrable → BoundedOperatorsSquareIntegrable → JABddOpQQ → JABddStar → JAIsAdj → JAPhiOp →
    JAStarOp → JAGroupAdj → JALocCC → JAFFStable → JAdjTrQQ

theorem jAdjTrQQ_of_leaves (hA : JAAssembleQQ) (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp)
    (h12 : JAGroupAdj) (h13 : JALocCC) (h14 : JAFFStable) : JAdjTrQQ :=
  hA h1 hat_bounded_decay_holds transfer_commutation_holds class_lower_decay_holds transfer_square_integrable_holds bounded_operators_square_integrable h7 transfer_star_bound_holds transfer_is_adjoint_holds phi_operator_transfer_holds h11
    h12 h13 h14

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACBump
section
open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem averaging_bump_holds : ACBump := by
  intro k r Wp Wq _ _ _ _ D K hK hKQ
  have : LocallyCompactSpace (B.Mat k r) :=
    (inferInstance : LocallyCompactSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  have hcont : ContinuousOn (fun q => B.gq D q) (JF.QDom k r D.z D.z') :=
    (Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D 0).continuousOn
  have hgK : IsCompact ((fun q => B.gq D q) '' K) := hK.image_of_continuousOn (hcont.mono hKQ)
  have hsub : (fun q => B.gq D q) '' K ⊆ Q.OmPlus k r D.z D.z' := by
    rintro _ ⟨q, hq, rfl⟩
    exact (Formalism.FourierDecayAlt.P.big_cell_domain k r Wp Wq D q (hKQ hq)).2
  obtain ⟨L, hLc, hKL, hLO⟩ := exists_compact_between hgK (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z') hsub
  obtain ⟨φ₀, hsupp, hsmooth, hrange⟩ :=
    (isOpen_interior : IsOpen (interior L)).exists_contDiff_support_eq (n := ⊤)
  have hts : tsupport φ₀ ⊆ L := by
    unfold tsupport
    rw [hsupp]
    exact closure_minimal interior_subset hLc.isClosed
  refine ⟨φ₀, hsmooth, fun g => (hrange ⟨g, rfl⟩).1, hLc.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hLO, fun q hq => ?_⟩
  have hin : B.gq D q ∈ Function.support φ₀ := by
    rw [hsupp]; exact hKL ⟨q, hq, rfl⟩
  exact lt_of_le_of_ne (hrange ⟨_, rfl⟩).1 (Ne.symm hin)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACHaarPos
section
open MeasureTheory
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

variable {k r : ℕ}

theorem haar_pos_nhds_one {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ)
    (hinv : ∀ u ∈ U, u⁻¹ ∈ U) (hunit : ∀ u ∈ U, IsUnit u.det) {V : Set (Mt k r)} (hV : IsOpen V)
    (h1 : ((1 : B.Mat k r) : Mt k r) ∈ V) : 0 < μ V := by
  rw [pos_iff_ne_zero]
  intro h0
  let W : B.Mat k r → Set (Mt k r) := fun u => lmulM u⁻¹ ⁻¹' V
  have hWo : ∀ u ∈ U, IsOpen (W u) := fun u _ => hV.preimage (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont _)
  have hW0 : ∀ u ∈ U, μ (W u) = 0 := by
    intro u hu
    have e := h.left u⁻¹ (hinv u hu)
    have := Measure.map_apply (μ := μ) (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont (k := k) (r := r) u⁻¹).measurable hV.measurableSet
    rw [e] at this
    show μ (lmulM u⁻¹ ⁻¹' V) = 0
    rw [← this]; exact h0
  have hcov : (U : Set (Mt k r)) ⊆ ⋃ u ∈ U, W u := by
    intro x hx
    refine Set.mem_iUnion₂.2 ⟨x, hx, ?_⟩
    have e : (lmulM x⁻¹ x : Mt k r) = ((1 : B.Mat k r) : Mt k r) := by
      show x⁻¹ * x = 1
      exact Matrix.nonsing_inv_mul x (hunit x hx)
    show lmulM x⁻¹ x ∈ V
    rw [e]; exact h1
  obtain ⟨T, hTU, hTc, hTeq⟩ := TopologicalSpace.isOpen_biUnion_countable U W hWo
  have hU0 : μ (U : Set (Mt k r)) = 0 := by
    refine measure_mono_null (hcov.trans hTeq.symm.le) ?_
    exact (measure_biUnion_null_iff hTc).2 fun u hu => hW0 u (hTU hu)
  have huniv : μ Set.univ = 0 := by
    refine measure_mono_null ?_ (measure_union_null hU0 h.conc)
    intro x _
    by_cases hx : x ∈ (U : Set (Mt k r))
    · exact Or.inl hx
    · exact Or.inr hx
  exact h.ne_zero (Measure.measure_univ_eq_zero.1 huniv)

theorem averaging_haar_positivity : ACHaarPos := by
  intro k r Wp Wq _ _ _ _ D O hO h1
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  obtain ⟨A, B', hA, hB, hoA, hoB, hAB⟩ := isOpen_prod_iff.1 hO oneP.1 oneP.2 h1
  obtain ⟨V1, V2, hV1, hV2, ho1, ho2, h12⟩ := isOpen_prod_iff.1 hA oneP.1.1 oneP.1.2 hoA
  obtain ⟨V3, V4, hV3, hV4, ho3, ho4, h34⟩ := isOpen_prod_iff.1 hB oneP.2.1 oneP.2.2 hoB
  have hsub : (V1 ×ˢ V2) ×ˢ (V3 ×ˢ V4) ⊆ O :=
    (Set.prod_mono h12 h34).trans hAB
  have uwI : ∀ (w : Fin (2 * r + k + 1) → ℂ), ∀ u ∈ UWset k r w, u⁻¹ ∈ UWset k r w :=
    fun w u hu => Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hu
  have uwU : ∀ (w : Fin (2 * r + k + 1) → ℂ), ∀ u ∈ UWset k r w, IsUnit u.det :=
    fun w u hu => WeylGroupFacts.isUnit_of_uh hu.1
  have nI : ∀ u ∈ Nset k r, u⁻¹ ∈ Nset k r := fun u hu => WeylGroupFacts.mem_n_inv hu
  have nU : ∀ u ∈ Nset k r, IsUnit u.det := fun u hu => WeylGroupFacts.isUnit_of_uh hu.1
  have p1 := haar_pos_nhds_one D.haarW (uwI _) (uwU _) hV1 ho1
  have p2 := haar_pos_nhds_one D.haarN nI nU hV2 ho2
  have p3 := haar_pos_nhds_one D.haarW' (uwI _) (uwU _) hV3 ho3
  have p4 := haar_pos_nhds_one D.haarN nI nU hV4 ho4
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  show 0 < ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) ((V1 ×ˢ V2) ×ˢ (V3 ×ˢ V4))
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  rw [pos_iff_ne_zero] at p1 p2 p3 p4 ⊢
  exact mul_ne_zero (mul_ne_zero p1 p2) (mul_ne_zero p3 p4)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

