import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGerm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0107
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0115
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0109
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLAtMost
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0293
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0290

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermParts
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def GermContAt (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) :
    Prop :=
  ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r + 1 → ∀ h : C.LPt, D.IsLocPt h (b - 1) → ∀ w, TBB.AdmW P p.l0 Y w →
    w.length + K ≤ N → ContinuousOn (fun z : ℂ => TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)])) {0}ᶜ

def GermDataAt (lev : ℕ → Prop) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (K N : ℕ) : Prop :=
  ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r + 1 → lev (b + s - 1) → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ w, TBB.AdmW P p.l0 Y w → w.length + K ≤ N →
    (∀ w', TBB.IsExt P p.l0 Y N K w w' →
      BddAbove (Set.range fun t : {t : ℂ // t ≠ 0} => TBB.Ew p nn F (b + s - 2) w' (h ++ [(s - 1, t.1)]))) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ut : ℂ → ℂ → H) (bt : ℂ → H) (β ε' η : ℂ) (SS κ₁ κ₂ : ℝ),
      0 ≤ κ₂ ∧ κ₂ ≤ Real.pi * κ₁ ∧ (η = 1 ∨ η = -1) ∧
      PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS ∧
      (∀ σ z : ℂ, P5.fsv σ z = G.psi β (η * σ * z)) ∧
      (∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
        ‖TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')])‖ =
          κ₁ * ‖PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), t⁻¹) ((), t'⁻¹)‖) ∧
      ∀ z : ℂ, z ≠ 0 → TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) = κ₂ * ‖PBK.bz s bt z‖ ^ 2

end place

def GermContAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → GermContAt p nn F Y K N

def GermDataLowAll : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    GermDataAt (fun i => i ≤ P.r) p nn F Y K N

def GermDataTopAll : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    GermDataAt (fun i => i = P.r + 1) p nn F Y K N

def PropGMean : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (s : ℕ) (β ε' η : ℂ)
    (ut : ℂ → ℂ → H) (bt : ℂ → H) (SS κ₁ κ₂ : ℝ) (E : ℂ → ℝ) (Nk : ℂ → ℂ → ℂ),
    2 ≤ s → 0 ≤ κ₂ → κ₂ ≤ Real.pi * κ₁ → (η = 1 ∨ η = -1) →
    PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS →
    (∀ σ z : ℂ, P5.fsv σ z = G.psi β (η * σ * z)) →
    (∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
      ‖Nk t t'‖ = κ₁ * ‖PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), t⁻¹) ((), t'⁻¹)‖) →
    (∀ z : ℂ, z ≠ 0 → E z = κ₂ * ‖PBK.bz s bt z‖ ^ 2) →
    Integrable E ∧
      ∀ ω₁ ω₂ : ℂ, (conj ω₁ * ω₂).im ≠ 0 → ∃ A : ℂ → ℂ, PDDual ω₁ ω₂ A ∧
        ∀ σ : ℂ, TBB.InDual ω₁ ω₂ σ →
          (‖(Real.pi⁻¹ : ℂ) * (∫ z : ℂ, P5.fsv σ z * (E z : ℂ)) + A σ‖₊ : ℝ≥0∞) ≤
            limsup (fun t : ℂ => (‖Nk t (t⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) (𝓝[≠] 0)

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem germAtPD_of_parts (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (K N : ℕ) (hC : GermContAt p nn F Y K N) (hL : GermDataAt (fun i => i ≤ P.r) p nn F Y K N)
    (hT : GermDataAt (fun i => i = P.r + 1) p nn F Y K N) (hM : PropGMean) : GermAtPD p nn F Y K N := by
  intro b s hb hs hbs h hh w hw hN hBdd
  have hcont := hC b s hb hs hbs h hh w hw hN
  have hdata : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ut : ℂ → ℂ → H) (bt : ℂ → H) (β ε' η : ℂ) (SS κ₁ κ₂ : ℝ),
      0 ≤ κ₂ ∧ κ₂ ≤ Real.pi * κ₁ ∧ (η = 1 ∨ η = -1) ∧
      PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS ∧
      (∀ σ z : ℂ, P5.fsv σ z = G.psi β (η * σ * z)) ∧
      (∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
        ‖TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')])‖ =
          κ₁ * ‖PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), t⁻¹) ((), t'⁻¹)‖) ∧
      ∀ z : ℂ, z ≠ 0 → TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) = κ₂ * ‖PBK.bz s bt z‖ ^ 2 := by
    rcases Nat.lt_or_ge (b + s - 1) (P.r + 1) with hlt | hge
    · exact hL b s hb hs hbs (by omega) h hh w hw hN hBdd
    · exact hT b s hb hs hbs (by omega) h hh w hw hN hBdd
  obtain ⟨H, _, _, _, ut, bt, β, ε', η, SS, κ₁, κ₂, hκ₂, hκ, hη, hGD, hpsi, hNk, hE⟩ := hdata
  obtain ⟨hint, hlat⟩ := hM H s β ε' η ut bt SS κ₁ κ₂
    (fun z => TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]))
    (fun t t' => TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')]))
    hs hκ₂ hκ hη hGD hpsi hNk hE
  exact ⟨hcont, hint, hlat⟩

end place

theorem germCutPD_of_parts (hA : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hχ : C6.IsCut0 χ)
    (hnn : ∀ y, 0 < nn y) (hC : GermContAll) (hL : GermDataLowAll) (hT : GermDataTopAll) (hM : PropGMean) :
    GermCutPD p nn χ F Y K N := by
  intro ε _
  have hGc : KB.CptCoef p.T.base (D.cutF p.T.base χ F ε) := cptCoef_cutF p.T.base hχ hF ε
  exact germAtPD_of_parts p nn _ Y K N (hC Wp Wq P p nn _ Y K N Cb hCb hGc hnn)
    (hL hA Wp Wq P p nn _ Y K N Cb hCb hGc hnn) (hT hA Wp Wq P p nn _ Y K N Cb hCb hGc hnn) hM

end

end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt

theorem block_growth_bound_of_germ_data (hA : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hG : KB.CptCoef p.T.base G) (hnn : ∀ y, 0 < nn y)
    (hC : GermContAll) (hL : GermDataLowAll) (hT : GermDataTopAll) (hM : PropGMean) : TBB.BlockGrowthBound p nn G Y K N :=
  block_growth_bound_of_positive_germ p nn G Y K N (posAt_of_cpt hA p nn G Y N (fun y => (hnn y).le) hG)
    (germAtPD_of_parts p nn G Y K N (hC Wp Wq P p nn G Y K N Cb hCb hG hnn) (hL hA Wp Wq P p nn G Y K N Cb hCb hG hnn)
      (hT hA Wp Wq P p nn G Y K N Cb hCb hG hnn) hM)

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConst
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

theorem line_at_most_one_holds : LineAtMost := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk Pr hPr π ζ hζ X hX Y hY hX0
  have hζT : P.TT < Complex.normSq ζ := hζ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT := Bs.T_pos
  obtain ⟨hνfix, hνν, -, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ'
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ with hνdef
  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hy : inWb P.k P.r (μ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb P.k P.r ν := by
    show inWb P.k P.r (SSn.unitH P.k P.r (SSn.prWv P.k P.r Bs.z (μ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk P.k P.r) ν Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  obtain ⟨Fr, hFr⟩ := Topx1.typ_frame_exists P.k P.r (by omega) Bs.z ν hz hT hνW hνz hνν
  obtain ⟨hFr', hpass⟩ := PRho.GL.gauge_left_line_holds Wp Wq P Bs hpl hk ζ hζT Fr hFr
  have hq : ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  obtain ⟨-, hg, hGG⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp
  have hcap : ∀ Z ∈ Line P Bs Pr π ζ, Gauge.GC.CapEig P Bs.π' (fun a => μ⁻¹ *ᵥ Fr a) π Z := by
    intro Z hZ Yc v
    have hZv : Pr π ν (Z v) = Z v := by
      have := DFunLike.congr_fun hZ.2 v
      simpa only [ContinuousLinearMap.comp_apply] using this
    have hr := ((hPr.2.2 ν hpos).2.2.2 π (Z v)).1 hZv Fr (by rw [hνfix]; exact hFr) (Yc + ((P.k : ℂ) - 2) / 2)
    rw [hpass Z hZ.1, hgl'] at hr
    have e : Yc + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Yc := by ring
    rw [e] at hr
    exact hr
  have hXF : X ∈ Gauge.GC.FibAt P.k P.r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hX.1 (h, h') ⟨hh, hh', he⟩
  have hYF : Y ∈ Gauge.GC.FibAt P.k P.r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hY.1 (h, h') ⟨hh, hh', he⟩
  exact Gauge.GC.lie_weight_at_most_holds Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk _ hg hGG.ne' _ hFr' π X Y hXF hYF
    (hcap X hX) (hcap Y hY) hX0

theorem modConst_of_cut : ModConstOfCut := by
  intro hLN hAM hDT hSR hSN hTF Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hUp
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hA.1
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  set x0 : ℝ := |P.TT| + 1 with hx0
  have hζ0 : ((x0 : ℝ) : ℂ) ∈ Gauge.GC.Ann P := by
    show P.TT < Complex.normSq ((x0 : ℝ) : ℂ)
    rw [Complex.normSq_ofReal]
    nlinarith [abs_nonneg P.TT, le_abs_self P.TT]
  obtain ⟨X0, hX0F, hX0P, hX0ne⟩ := hLN Wp Wq P Bs hpl hk Pr hPr π _ hζ0
  set ζ0 : ℂ := ((x0 : ℝ) : ℂ) with hζ0def
  set T0 := (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0)).comp
    (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0)
      (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ0) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0) X0) with hT0
  have hB0 : ‖B.hsVec X0‖ ≠ 0 := norm_ne_zero_iff.2 (Gauge.GC.hsVec_ne_zero hX0ne)
  refine ⟨M.Nrm P l π, ‖B.hsVec T0‖ ^ 2 / ‖B.hsVec X0‖ ^ 2, fun ζ hζ Xf hXf hXP => ⟨?_, ?_⟩⟩
  · have hL : Xf ∈ Line P Bs Pr π ζ := ⟨hXf, hXP⟩
    have hR := hSR Wp Wq P Bs hk X d hA l hl S hS Pr hPr π ρ hUp ζ hζ Xf hL
    rw [hR.2]
    exact hSN Wp Wq P Bs hk X d hA l hl S hS Pr hPr π ζ hζ Xf hL
  · have hζT : P.TT < Complex.normSq ζ := hζ
    have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
      rw [hTz, hTz']; exact hζT
    have hζ0T : P.TT < Complex.normSq ζ0 := hζ0
    have hζ0' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ0 := by
      rw [hTz, hTz']; exact hζ0T
    obtain ⟨h, hh, h', hh', hν, hν', hι, hst⟩ :=
      hDT P.k P.r Bs.z Bs.z' Bs.μsec hk hz hz' Bs.T_pos Bs.T'_pos Bs.sec ζ0 ζ hζ0' hζ'
    have hhi := LieBracketMultiplication.uw_inv hh
    have hh'i := LieBracketMultiplication.uw_inv hh'
    have hiso : ∀ Y, ‖B.hsVec ((Bs.π h).comp (Y.comp (Bs.π' h'⁻¹)))‖ = ‖B.hsVec Y‖ :=
      fun Y => CutBP.hsVec_norm_CinL Bs hh hh' Y
    have hinv1 : ∀ w, Bs.π h⁻¹ (Bs.π h w) = w := by
      intro w
      rw [← ContinuousLinearMap.comp_apply, ← Bs.π_rep.2 _ hhi _ hh, NFRadRedS.uw_inv_mul hh, Bs.π_rep.1]
      rfl

    have hF : (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
      refine fun p hp => ?_
      have hp1 : p.1 ∈ UWset P.k P.r Bs.z := hp.1
      have hp2 : p.2 ∈ UWset P.k P.r Bs.z' := hp.2.1
      have hm1 : h⁻¹ * p.1 * h ∈ UWset P.k P.r Bs.z := LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul hhi hp1) hh
      have hm2 : h'⁻¹ * p.2 * h' ∈ UWset P.k P.r Bs.z' := LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul hh'i hp2) hh'
      have key := hX0F _ (hst p hp)
      have e1 : (Bs.π p.1).comp (Bs.π h) = (Bs.π h).comp (Bs.π (h⁻¹ * p.1 * h)) := by
        rw [← Bs.π_rep.2 _ hp1 _ hh, ← Bs.π_rep.2 _ hh _ hm1, ← mul_assoc, ← mul_assoc,
          NFRadRedS.uw_mul_inv hh, one_mul]
      have e2 : (Bs.π' h'⁻¹).comp (Bs.π' p.2) = (Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹) := by
        rw [← Bs.π'_rep.2 _ hh'i _ hp2, ← Bs.π'_rep.2 _ hm2 _ hh'i, mul_assoc (h'⁻¹ * p.2) h' h'⁻¹,
          NFRadRedS.uw_mul_inv hh', mul_one]
      ext v
      have k1 := DFunLike.congr_fun e1 (X0 (Bs.π' h'⁻¹ (Bs.π' p.2 v)))
      have k2 := DFunLike.congr_fun e2 v
      have k3 := DFunLike.congr_fun key (Bs.π' h'⁻¹ v)
      simp only [ContinuousLinearMap.comp_apply] at k1 k2 k3 ⊢
      rw [k1, k2, k3]

    have hP : (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp ((Bs.π h).comp (X0.comp (Bs.π' h'⁻¹))) =
        (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) := by
      rw [← hν, hPr.2.1 h hh π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0)]
      ext v
      have k1 := DFunLike.congr_fun hX0P (Bs.π' h'⁻¹ v)
      simp only [ContinuousLinearMap.comp_apply] at k1 ⊢
      rw [hinv1, k1]
    have hL0 : (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) ∈ Line P Bs Pr π ζ := ⟨hF, hP⟩
    have hne : (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) ≠ 0 := by
      intro h0
      apply hB0
      have hz0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
        rw [← zero_smul ℂ (0 : Wq →L[ℂ] Wp), Gauge.GC.hsVec_smul, zero_smul]
      rw [← hiso X0, h0, hz0, norm_zero]
    obtain ⟨c, hc⟩ := hAM Wp Wq P Bs hpl hk Pr hPr π ζ hζ _ hL0 Xf ⟨hXf, hXP⟩ hne

    have hTe := ((hTF Wp Wq P Bs hpl Bw Bw' hBw hBw').2.2.2.1 h hh h' hh'
      (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0) (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ0)
      (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0) X0).1
    rw [hν, hν', hι] at hTe
    have hPT : (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
        (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
          (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
          ((Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)))) = (Bs.π h).comp (T0.comp (Bs.π' h'⁻¹)) := by
      rw [hTe]
      conv_lhs => rw [← hν]
      rw [hPr.2.1 h hh ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0), hT0]
      ext v
      simp only [ContinuousLinearMap.comp_apply]
      rw [hinv1]
    rw [hc, map_smul, ContinuousLinearMap.comp_smul, hPT, Gauge.GC.hsVec_smul, Gauge.GC.hsVec_smul,
      norm_smul, norm_smul, hiso, hiso]
    field_simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem good_positioned_of_cut {P : M.Par} {l0 : ℕ} {w : List C.Letter} (hw : KB.CutWord P l0 w) :
    Wd.Good (D.positionted w) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [D.positionted, List.map_ofFn]
    exact List.nodup_ofFn.mpr (fun a b h => h)
  · intro l hl
    simp only [D.positionted, List.mem_ofFn] at hl
    obtain ⟨a, rfl⟩ := hl
    simp [Complex.conj_ofReal]
  · rw [D.positionted, List.pairwise_ofFn]
    intro a b hab
    have key : ∀ u v : ℝ, 2 < |u - v| → ((u : ℂ) - v ≠ 1 ∧ (v : ℂ) - u ≠ 1) := by
      intro u v huv
      constructor
      · intro h
        have h' := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at h'
        rw [h'] at huv
        norm_num at huv
      · intro h
        have h' := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at h'
        rw [abs_sub_comm, h'] at huv
        norm_num at huv
    obtain ⟨k1, k2⟩ := key _ _ (hw.2 a b (ne_of_lt hab))
    simp only [Wd.RegL]
    split_ifs
    · exact k1
    · exact k2

theorem foldCV_congr {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) :
    ∀ (L : List (Bool × ℝ)) (f f₂ : B.Mat k r → E), (∀ x ∈ B.GV k r, f x = f₂ x) →
      ∀ x ∈ B.GV k r, L.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) f x =
        L.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) f₂ x
  | [], _, _, h, x, hx => h x hx
  | a :: L, f, f₂, h, x, hx => by
    simp only [List.foldr_cons]
    have ih := foldCV_congr s L f f₂ h
    exact (Formalism.FourierDecayAlt.P.Dx1.LZ.good_Tc (k := k) (r := r) (E := E) s (a.2 : ℂ)).loc _ _
      (fun y hy => ih y hy.1.1) x (Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hx)

section betaR

open Formalism.FourierDecayAlt.B

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_congr_right (Bs : RealPlaceData k r Wp Wq) {F G G₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, G g = G₂ g) : beta Bs F G = beta Bs F G₂ := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq Bs)] with q hq
  by_cases hQ : q ∈ B.Qset Bs
  · have hg : bigCell k r q.1 (Bs.μsec q.2) ∈ GV k r := (hq hQ).1
    show (bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q : ℂ) * inner ℂ (hsVec (JF Bs G (bigCell k r q.1 (Bs.μsec q.2))))
        (hsVec (JF Bs F (bigCell k r q.1 (Bs.μsec q.2)))) =
      (bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q : ℂ) * inner ℂ (hsVec (JF Bs G₂ (bigCell k r q.1 (Bs.μsec q.2))))
        (hsVec (JF Bs F (bigCell k r q.1 (Bs.μsec q.2))))
    rw [Formalism.FourierDecayAlt.P.JCx2.sq_jf_congr Bs h hg]
  · have hw : bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (Formalism.FourierDecayAlt.P.JCx2.sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q : ℂ) * _ = (bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q : ℂ) * _
    rw [hw]
    simp

end betaR

theorem residual_pairing_congr_on_group {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    {F F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (hF₂ : B.CkOn ⊤ (B.GV P.k P.r) F₂)
    (h : ∀ g ∈ B.GV P.k P.r, F g = F₂ g) {w : List C.Letter} (hw : KB.CutWord P p.l0 w) :
    p.RR F 0 w [] [] = p.RR F₂ 0 w [] [] := by
  unfold KB.Pl.RR
  rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hF (good_positioned_of_cut hw),
    Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hF₂ (good_positioned_of_cut hw)]
  unfold C7.principalHermitianLattice
  rw [Formalism.FourierDecayAlt.P.JCx2.sq_beta_congr _ (foldCV_congr _ w F F₂ h), beta_congr_right _ h]

theorem cutF_eq_on_gv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} {δ : ℝ} (hG : ∀ g ∈ B.GV k r, F g ≠ 0 → δ ≤ Gf k r Bs.z Bs.z' g) {ε : ℝ}
    (hε : 0 < ε) (hεδ : ε ≤ δ) : ∀ g ∈ B.GV k r, D.cutF Bs χ F ε g = F g := by
  intro g hg
  simp only [D.cutF]
  by_cases hF : F g = 0
  · rw [hF, smul_zero]
  · have h1 : 1 ≤ Gf k r Bs.z Bs.z' g / ε := by
      rw [le_div_iff₀ hε]
      linarith [hG g hg hF]
    rw [hχ.2.2 _ h1]
    simp

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def LimEv (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re = (p.RR F 0 w [] []).re

def LimPos (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → 0 ≤ (p.RR F 0 w [] []).re

def LimBd (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    (p.RR F 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base F F).re

theorem truncated_limit_evaluation_holds (p : KB.Pl P Wp Wq) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) (Y : Finset ℝ) (N : ℕ) : LimEv p χ F Y N := by
  intro w hw _
  obtain ⟨hCk, _, δ, hδ, hG⟩ := hF
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  rw [residual_pairing_congr_on_group p (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hCk ε) hCk
    (cutF_eq_on_gv p.T.base hχ hG hε.1 hε.2.le) hw.1]

theorem truncated_limit_positivity_holds (hA : P5.ThmPActual) (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) (Y : Finset ℝ) (N : ℕ) : LimPos p F Y N := by
  intro w hw _
  have hh : D.IsLocPt ([] : C.LPt) 0 := ⟨by simp, rfl⟩
  rw [PBL.rr_eq_form p F 0 (Nat.zero_le _) w [] [] hh hh]
  obtain ⟨ε, hε, hnv⟩ := PBL.slv_nv p hF 0 (Nat.zero_le _) w [] hh
  exact Formalism.FourierDecayAlt.P.TBBx5.form_re_nonneg p
    (Formalism.FourierDecayAlt.P.TBBx5.formNonneg_of hA (Formalism.FourierDecayAlt.P.pb_formPos : PBL.FormPos) p) 0 (Nat.zero_le _) w hw.1 hε _ hnv

theorem limE_of_parts (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (hnn : ∀ y, 0 ≤ nn y) (hEv : LimEv p χ F Y N) (hPos : LimPos p F Y N)
    (hBd : LimBd p nn F Y N) : LimE p nn χ F Y N := by
  intro w hw hl
  have hE := hEv w hw hl
  have hP := hPos w hw hl
  have hB := hBd w hw hl
  have hN : 0 ≤ TBB.normC nn w := by
    unfold TBB.normC
    exact List.prod_nonneg (fun x hx => by
      obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
      exact hnn _)
  by_cases hb : 0 < (B.beta p.T.base F F).re
  · refine ⟨(p.RR F 0 w [] []).re / (B.beta p.T.base F F).re, div_nonneg hP hb.le, (div_le_iff₀ hb).2 hB, ?_⟩
    rw [div_mul_cancel₀ _ hb.ne']
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    exact hE.mono fun ε h => h.symm
  · have hb' : (B.beta p.T.base F F).re ≤ 0 := not_lt.1 hb
    have hR0 : (p.RR F 0 w [] []).re = 0 :=
      le_antisymm (hB.trans (mul_nonpos_of_nonneg_of_nonpos hN hb')) hP
    refine ⟨0, le_refl 0, hN, ?_⟩
    rw [zero_mul]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    exact hE.mono fun ε h => (h.trans hR0).symm

theorem truncated_limit_equality_holds (hA : P5.ThmPActual) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (hnn : ∀ y, 0 ≤ nn y)
    (hF : KB.CptCoef p.T.base F) (hBd : LimBd p nn F Y N) : LimE p nn χ F Y N :=
  limE_of_parts p nn χ F Y N hnn (truncated_limit_evaluation_holds p hχ hF Y N) (truncated_limit_positivity_holds hA p hF Y N) hBd

end place

theorem thmBpAt_of_leaves_limBd (hA : P5.ThmPActual) (C₃ CΛ C₀ Cκ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ)
    (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
      (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b Λ κ₀ : ℝ) (n₀ p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ)
      (Cb : ℝ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 0 < κ₀ →
      κ₀ ≤ b ^ (Cκ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) → 1 ≤ TBB.Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base f →
      B.CkOn ⊤ (B.GV P.k P.r) Ap → B.CkOn ⊤ (B.GV P.k P.r) Am →
      Amaps p f Ap Am ApPt AmPt b n₀ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      GermCutPD p nn χ (TBBx4.fpm p f Ap p₀) Y K N → GermCutPD p nn χ (TBBx4.fpm p f Am p₀) Y K N →
      LimBd p nn (TBBx4.fpm p f Ap p₀) Y N → LimBd p nn (TBBx4.fpm p f Am p₀) Y N →
      LemB p (TBBx4.fpm p f Ap p₀) κ₀ → LemB p (TBBx4.fpm p f Am p₀) κ₀ →
      TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₄, hC₄⟩ := thmBpAt_of_leaves' hA C₃ CΛ C₀ Cκ hC₃ hCΛ hC₀
  refine ⟨C₄, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26
  exact hC₄ Wp Wq P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
    (truncated_limit_equality_holds hA p nn h11 _ Y N (fun y => (h12 y).le) (cptCoef_fpm_of p p₀ h14 h15) h23)
    (truncated_limit_equality_holds hA p nn h11 _ Y N (fun y => (h12 y).le) (cptCoef_fpm_of p p₀ h14 h16) h24) h25 h26

end

end Formalism.FourierDecayAlt.P.CutBP
end

