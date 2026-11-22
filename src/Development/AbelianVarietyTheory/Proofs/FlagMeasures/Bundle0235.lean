import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0229
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0203
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0225
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0228
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilradicalCenterIntegralCoveringRadius
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselCoefficientSmulEquivariant
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.AbsConv

variable {k r : ℕ}

theorem measurable_lmul : Measurable (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2 : Mat k r) p.1) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem lintegral_lt_top {μG μS ν : Measure (Mt k r)} [SFinite μG] [SFinite μS] [SFinite ν]
    {S : Set (Mat k r)} (hq : IsQuotMeas μG μS ν)
    (hmap : μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2 : Mat k r) p.1))
    (hS : ∀ᵐ s ∂μS, (Matrix.of s : Mat k r) ∈ S)
    (hR : ∀ s ∈ S, μS.map (rmulM s) = μS)
    {φ : Mt k r → ENNReal} (hφ : Measurable φ)
    (hfin : ∫⁻ g, ∫⁻ t, φ g * φ (lmulM (Matrix.of t : Mat k r) g) ∂μS ∂μG < ⊤)
    {Wn : Mt k r → ENNReal} (hWG : AEMeasurable Wn μG) (hWν : AEMeasurable Wn ν)
    (hinv : ∀ᵐ x ∂ν, ∀ s ∈ S, Wn (lmulM s x) = Wn x)
    (hl2 : ∫⁻ x, Wn x ^ 2 ∂ν < ⊤) :
    ∫⁻ g, φ g * Wn g ∂μG < ⊤ := by
  have hmeas2 : Measurable (fun p : Mt k r × Mt k r => φ (lmulM (Matrix.of p.2 : Mat k r) p.1)) :=
    hφ.comp GlobalTheory.SgInf.AbsConv.measurable_lmul
  have hsec : ∀ x : Mt k r, Measurable (fun t : Mt k r => φ (lmulM (Matrix.of t : Mat k r) x)) :=
    fun x => hmeas2.comp measurable_prodMk_left
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Mt k r → ENNReal,
      Φ = fun x => ∫⁻ t, φ (lmulM (Matrix.of t : Mat k r) x) ∂μS := ⟨_, rfl⟩
  have hΦx : ∀ x, Φ x = ∫⁻ t, φ (lmulM (Matrix.of t : Mat k r) x) ∂μS := fun x => by rw [hΦdef]
  have hΦm : Measurable Φ := by rw [hΦdef]; exact hmeas2.lintegral_prod_right'

  have hΦinv : ∀ s ∈ S, ∀ x, Φ (lmulM s x) = Φ x := by
    intro s hs x
    have hrm : Measurable (rmulM s : Mt k r → Mt k r) := (continuous_rmulM s).measurable
    rw [hΦx, hΦx]
    conv_rhs => rw [← hR s hs]
    rw [lintegral_map (hsec x) hrm]
    refine lintegral_congr fun t => ?_
    congr 1
    change (Matrix.of t * (s * Matrix.of x) : Mat k r) = Matrix.of t * s * Matrix.of x
    rw [Matrix.mul_assoc]

  have hΦ2 : ∫⁻ x, Φ x * Φ x ∂ν < ⊤ := by
    have hF : Measurable (fun g : Mt k r => φ g * Φ g) := hφ.mul hΦm
    have e1 : ∫⁻ g, ∫⁻ t, φ g * φ (lmulM (Matrix.of t : Mat k r) g) ∂μS ∂μG
        = ∫⁻ g, φ g * Φ g ∂μG := by
      refine lintegral_congr fun g => ?_
      rw [lintegral_const_mul _ (hsec g), hΦx]
    have e2 : ∫⁻ g, φ g * Φ g ∂μG = ∫⁻ x, ∫⁻ s, φ (lmulM (Matrix.of s : Mat k r) x) *
        Φ (lmulM (Matrix.of s : Mat k r) x) ∂μS ∂ν := hq _ hF
    have e3 : ∀ x, ∫⁻ s, φ (lmulM (Matrix.of s : Mat k r) x) * Φ (lmulM (Matrix.of s : Mat k r) x) ∂μS
        = Φ x * Φ x := by
      intro x
      rw [lintegral_congr_ae (g := fun s => φ (lmulM (Matrix.of s : Mat k r) x) * Φ x) ?_]
      · rw [lintegral_mul_const _ (hsec x), ← hΦx]
      · filter_upwards [hS] with s hs
        rw [hΦinv _ hs x]
    calc ∫⁻ x, Φ x * Φ x ∂ν
        = ∫⁻ x, ∫⁻ s, φ (lmulM (Matrix.of s : Mat k r) x) * Φ (lmulM (Matrix.of s : Mat k r) x) ∂μS ∂ν :=
          lintegral_congr fun x => (e3 x).symm
      _ = ∫⁻ g, φ g * Φ g ∂μG := e2.symm
      _ = _ := e1.symm
      _ < ⊤ := hfin

  have hWmm : Measurable (hWν.mk Wn) := hWν.measurable_mk
  have h1 : ∀ᵐ x ∂ν, (∀ s ∈ S, Wn (lmulM s x) = Wn x) ∧ Wn x = hWν.mk Wn x :=
    hinv.and hWν.ae_eq_mk
  have h1' : ∀ᵐ p ∂(ν.prod μS), (∀ s ∈ S, Wn (lmulM s p.1) = Wn p.1) ∧ Wn p.1 = hWν.mk Wn p.1 :=
    Measure.quasiMeasurePreserving_fst.ae h1
  have h2 : ∀ᵐ p ∂(ν.prod μS), (Matrix.of p.2 : Mat k r) ∈ S :=
    Measure.quasiMeasurePreserving_snd.ae hS
  have hA : AEMeasurable (fun g => φ g * Wn g)
      ((ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2 : Mat k r) p.1)) := by
    rw [← hmap]; exact hφ.aemeasurable.mul hWG
  have hmain : ∫⁻ g, φ g * Wn g ∂μG = ∫⁻ x, Φ x * hWν.mk Wn x ∂ν := by
    rw [hmap, lintegral_map' hA GlobalTheory.SgInf.AbsConv.measurable_lmul.aemeasurable]
    rw [lintegral_congr_ae (g := fun p : Mt k r × Mt k r =>
      φ (lmulM (Matrix.of p.2 : Mat k r) p.1) * hWν.mk Wn p.1) ?_]
    · rw [lintegral_prod (fun p : Mt k r × Mt k r => φ (lmulM (Matrix.of p.2 : Mat k r) p.1) * hWν.mk Wn p.1)
        (hmeas2.mul (hWmm.comp measurable_fst)).aemeasurable]
      refine lintegral_congr fun x => ?_
      dsimp only
      rw [lintegral_mul_const _ (hsec x), ← hΦx]
    · filter_upwards [h1', h2] with p hp1 hp2
      simp only [hp1.1 _ hp2, hp1.2]

  have hpt : ∀ x, Φ x * hWν.mk Wn x ≤ hWν.mk Wn x ^ 2 + Φ x * Φ x := by
    intro x
    rcases le_total (Φ x) (hWν.mk Wn x) with h | h
    · calc Φ x * hWν.mk Wn x ≤ hWν.mk Wn x * hWν.mk Wn x := by gcongr
        _ = hWν.mk Wn x ^ 2 := (sq _).symm
        _ ≤ _ := le_self_add
    · calc Φ x * hWν.mk Wn x ≤ Φ x * Φ x := by gcongr
        _ ≤ _ := le_add_self
  have hW2 : ∫⁻ x, hWν.mk Wn x ^ 2 ∂ν = ∫⁻ x, Wn x ^ 2 ∂ν :=
    lintegral_congr_ae (hWν.ae_eq_mk.symm.fun_comp (· ^ 2))
  rw [hmain]
  calc ∫⁻ x, Φ x * hWν.mk Wn x ∂ν ≤ ∫⁻ x, hWν.mk Wn x ^ 2 + Φ x * Φ x ∂ν := lintegral_mono hpt
    _ = ∫⁻ x, hWν.mk Wn x ^ 2 ∂ν + ∫⁻ x, Φ x * Φ x ∂ν := lintegral_add_left (hWmm.pow_const 2) _
    _ < ⊤ := by rw [hW2]; exact ENNReal.add_lt_top.2 ⟨hl2, hΦ2⟩

theorem enorm_star' (a : ℂ) : ‖star a‖ₑ = ‖a‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]

theorem coef_inv_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (w : H) {y g : Mat k r}
    (hy : y ∈ GG k r) (hyi : y⁻¹ ∈ GG k r) (hg : g ∈ GG k r) :
    coef σ w w (y⁻¹ * g) = coef σ w (σ y w) g := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  have hyy : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv y (isUnit_det_of_mem_GG hy)
  have key : ∀ v : H, σ y (σ y⁻¹ v) = v := by
    intro v
    have := congrArg (fun T : H →L[ℂ] H => T v) (hmul y hy y⁻¹ hyi)
    simp only [hyy, h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
    exact this.symm
  have hinner : ∀ u v : H, ⟪σ y u, σ y v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro u v
    let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ y).toLinearMap, norm_map' := hiso y hy }
    exact L.inner_map_map u v
  simp only [coef]
  rw [hmul y⁻¹ hyi g hg, ContinuousLinearMap.comp_apply, ← hinner w (σ y⁻¹ (σ g w)), key]

theorem norm_equiv {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    (hπ : IsURepOn (UWset k r z) π) {W : Mat k r → Wp} (hW : IsSPsiEquiv z (psiGen k r z c) π W)
    {s x : Mat k r} (hs : s ∈ Sset k r z) (hx : x ∈ GG k r) : ‖W (s * x)‖ₑ = ‖W x‖ₑ := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hx' : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := hx
  rw [hW h hh m hm x hx']
  obtain ⟨-, hiso, -⟩ := hπ
  have hψ : ‖psiGen k r z c m‖ = 1 := by simp [psiGen, Complex.norm_exp]
  have hn : ‖psiGen k r z c m • π h (W x)‖ = ‖W x‖ := by rw [norm_smul, hψ, one_mul, hiso h hh]
  simp only [enorm_eq_nnnorm]
  congr 1
  exact NNReal.eq hn

theorem integrable_coef_smul : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) μG := by
  classical
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hq W hWG hWν hW hl2 y hy
  have hint := GlobalTheory.T.besselForm_coeff_product_fubini_integrable k r σ w a μG d z c π μS hStd hSide
  obtain ⟨-, hσ, -, -, hHG, -, -, -, -⟩ := hStd
  obtain ⟨hz, hT, hπ, hHS, -⟩ := hSide
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  have hUS : IsUnimod (Sset k r z) μS := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hHS
  obtain ⟨hνσ, hνG, hmap, -, -⟩ := GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hHG hHS hUS hq
  have : SigmaFinite μG := hHG.1
  have : SigmaFinite μS := hHS.1
  have : SigmaFinite ν := hνσ
  have hyi : y⁻¹ ∈ GG k r := hcl.1.2.2.2.2 y hy
  have hone : (1 : Mat k r) ∈ GG k r := hcl.1.2.2.1
  have hwD : w ∈ DD σ w := by
    have := mem_DD σ w hone
    rwa [hσ.1.1, ContinuousLinearMap.one_apply] at this
  have hyD : σ y w ∈ DD σ w := mem_DD σ w hy
  have hint2 := hint w hwD w hwD (σ y w) hyD (σ y w) hyD

  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  set GGset : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∈ GG k r} with hGGdef
  have hGGmeas : MeasurableSet GGset := (hcl.1.2.1.preimage hof).measurableSet
  have hGae : ∀ᵐ x ∂μG, x ∈ GGset := ae_iff.2 hHG.2.2.1
  have hc0 : ContinuousOn (fun g : Mt k r => σ (Matrix.of g) w) GGset :=
    (hσ.2.2 w).comp hof.continuousOn (fun x hx => hx)
  have hcc : ContinuousOn (fun g : Mt k r => coef σ w (σ y w) (Matrix.of g)) GGset := by
    simp only [coef]
    exact continuousOn_const.inner hc0

  obtain ⟨φ, hφdef⟩ : ∃ φ : Mt k r → ENNReal,
      φ = GGset.piecewise (fun g => ‖coef σ w (σ y w) (Matrix.of g)‖ₑ) 0 := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφdef]
    exact ContinuousOn.measurable_piecewise (continuous_enorm.comp_continuousOn hcc)
      continuousOn_const hGGmeas
  have hφle : ∀ g, φ g ≤ ‖coef σ w (σ y w) (Matrix.of g)‖ₑ := by
    intro g
    rw [hφdef]
    by_cases hg : g ∈ GGset
    · simp [Set.piecewise, hg]
    · simp [Set.piecewise, hg]
  have hfin : ∫⁻ g, ∫⁻ t, φ g * φ (lmulM (Matrix.of t : Mat k r) g) ∂μS ∂μG < ⊤ := by
    have hfi := hint2.hasFiniteIntegral
    unfold HasFiniteIntegral at hfi
    refine lt_of_le_of_lt ?_ hfi
    refine le_trans (lintegral_mono fun g => lintegral_mono fun t => ?_) (lintegral_prod _ hint2.aestronglyMeasurable.enorm).symm.le
    dsimp only
    rw [enorm_mul, GlobalTheory.SgInf.AbsConv.enorm_star']
    exact mul_le_mul' (hφle g) (hφle _)
  have hinv : ∀ᵐ x ∂ν, ∀ s ∈ Sset k r z,
      ‖W (Matrix.of (lmulM s x))‖ₑ = ‖W (Matrix.of x)‖ₑ := by
    have : ∀ᵐ x ∂ν, x ∈ GGset := ae_iff.2 hνG
    filter_upwards [this] with x hx s hs
    exact GlobalTheory.SgInf.AbsConv.norm_equiv hπ hW hs hx
  have hl2' : ∫⁻ x, ‖W (Matrix.of x)‖ₑ ^ 2 ∂ν < ⊤ := by
    simpa only [l2SG, enorm_eq_nnnorm] using hl2
  have hbound := GlobalTheory.SgInf.AbsConv.lintegral_lt_top (S := Sset k r z) hq hmap (ae_iff.2 hHS.2.2.1)
    hUS.1 hφm hfin hWG.enorm hWν.enorm hinv hl2'

  have hcm : AEStronglyMeasurable (fun g : Mt k r => star (coef σ w (σ y w) (Matrix.of g))) μG := by
    rw [← Measure.restrict_eq_self_of_ae_mem hGae]
    exact hcc.star.aestronglyMeasurable hGGmeas
  have hsm : AEStronglyMeasurable
      (fun g : Mt k r => star (coef σ w (σ y w) (Matrix.of g)) • W (Matrix.of g)) μG := hcm.smul hWG
  have hae : (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g))
      =ᵐ[μG] (fun g : Mt k r => star (coef σ w (σ y w) (Matrix.of g)) • W (Matrix.of g)) := by
    filter_upwards [hGae] with g hg
    rw [GlobalTheory.SgInf.AbsConv.coef_inv_mul (g := Matrix.of g) hσ w hy hyi hg]
  refine Integrable.congr ⟨hsm, ?_⟩ hae.symm
  show ∫⁻ g, ‖star (coef σ w (σ y w) (Matrix.of g)) • W (Matrix.of g)‖ₑ ∂μG < ⊤
  refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hbound
  filter_upwards [hGae] with g hg
  rw [enorm_smul, GlobalTheory.SgInf.AbsConv.enorm_star', hφdef, Set.piecewise_eq_of_mem _ _ _ hg]

end GlobalTheory.SgInf.AbsConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KfinCoefMulSplit
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.KFinCoefSplit

variable {k r : ℕ}

theorem kfin_smul {R : Rep k r} (a : ℂ) {v : R.H} (hv : R.KFin v) : R.KFin (a • v) := by
  obtain ⟨S, hfd, hv, hst⟩ := hv
  exact ⟨S, hfd, S.smul_mem a hv, hst⟩

theorem kfin_sum {R : Rep k r} {ι : Type} [Fintype ι] (x : ι → R.H) (hx : ∀ c, R.KFin (x c)) :
    R.KFin (∑ c, x c) := by
  choose S hfd hS hst using hx
  refine ⟨⨆ c, S c, inferInstance, Submodule.sum_mem _ fun c _ => Submodule.mem_iSup_of_mem c (hS c),
    fun g hg y hy => ?_⟩
  have hle : (⨆ c, S c) ≤ (⨆ c, S c).comap (R.σ g : R.H →ₗ[ℂ] R.H) :=
    iSup_le fun c z hz => Submodule.mem_iSup_of_mem c (hst c g hg z hz)
  exact hle hy

theorem kfin_coef_mul_split : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (om om' : ι → ℂ) (v v' : R.H), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → R.KFin v → R.KFin v' → (∀ I, (RI I).KFin (∑ c, pr I c (tm R om v c)) ∧ (RI I).KFin (∑ c, pr I c (tm R om' v' c))) ∧ ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R om v c), (RI I).σ g (∑ c, pr I c (tm R om' v' c))⟫_ℂ := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI om om' v v' hR hRI hF hT hv hv'
  obtain ⟨-, -, -, -, hRT, -, hRK, -, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have hadj := (GlobalTheory.TensAdj.tens_adj hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT).2.2.2.2
  have hkf := (GlobalTheory.tensor_decomposition_kfinite hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw).2.1
  have hp : ∀ I (a : ι → ℂ) (w : R.H), R.KFin w → (RI I).KFin (∑ c, pr I c (tm R a w c)) := fun I a w hw =>
    kfin_sum _ fun c => hkf I c _ (kfin_smul (a c) hw)
  exact ⟨fun I => ⟨hp I om v hv, hp I om' v' hv'⟩,
    fun g hg => hadj om om' v (hRT v (hRK v hv)) v' (hRT v' (hRK v' hv')) g hg⟩

end GlobalTheory.KFinCoefSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanCovolumeFunction
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagBase.MeanCov

theorem lintegral_div_inv (κ : ℝ) (hκ : 0 < κ) (w : ℝ → ENNReal) :
    ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) / ENNReal.ofReal t
      = ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal t := by
  have himg : (fun t : ℝ => κ / t) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact div_pos hκ ht
    · intro hs
      have hs0 : s ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hs)
      refine ⟨κ / s, div_pos hκ hs, ?_⟩
      field_simp
  have hder : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => κ / t) (κ * -(t ^ 2)⁻¹) (Set.Ioi 0) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ht)
    have h1 : HasDerivAt (fun y : ℝ => κ * y⁻¹) (κ * -(t ^ 2)⁻¹) t := (hasDerivAt_inv ht0).const_mul κ
    have h2 : (fun y : ℝ => κ / y) = fun y => κ * y⁻¹ := by
      funext y
      rw [div_eq_mul_inv]
    rw [h2]
    exact h1.hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ => κ / t) (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha0 : a ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ha)
    have hb0 : b ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hb)
    have hk0 : κ ≠ 0 := ne_of_gt hκ
    simp only at hab
    field_simp at hab
    nlinarith [hab]
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj
    (fun s => w (κ / s) / ENNReal.ofReal s)
  rw [himg] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht' : 0 < t := Set.mem_Ioi.mp ht
  have hq : 0 < κ / t := div_pos hκ ht'
  have habs : |κ * -(t ^ 2)⁻¹| = κ / t * t⁻¹ := by
    rw [abs_mul, abs_neg, abs_of_pos hκ, abs_of_pos (by positivity)]
    field_simp
  have hkk : κ / (κ / t) = t := by
    field_simp
  simp only
  rw [habs, hkk, ENNReal.ofReal_mul hq.le, ENNReal.ofReal_inv_of_pos ht', div_eq_mul_inv, div_eq_mul_inv]
  have hne : ENNReal.ofReal (κ / t) ≠ 0 := by simpa using hq
  calc ENNReal.ofReal (κ / t) * (ENNReal.ofReal t)⁻¹ * (w t * (ENNReal.ofReal (κ / t))⁻¹)
      = (ENNReal.ofReal (κ / t) * (ENNReal.ofReal (κ / t))⁻¹) * (w t * (ENNReal.ofReal t)⁻¹) := by ring
    _ = w t * (ENNReal.ofReal t)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top, one_mul]

theorem measurable_detNorm (E : Type) [Field E] [NumberField E] (j : ℕ) :
    Measurable (detNorm E j) := by
  have hc : Continuous (fun x : InfinitePlace E → Fin j → Fin j → ℂ =>
      ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2) := by
    refine continuous_finset_prod _ (fun w _ => ?_)
    exact ((Continuous.matrix_det
      (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w)) (continuous_apply w)).norm).pow 2
  exact hc.measurable

theorem ae_detNorm_pos (E : Type) [Field E] [NumberField E] (j : ℕ) (hj : 1 ≤ j) :
    ∀ᵐ g ∂(haarGL E j), 0 < detNorm E j g := by
  have hm := GlobalTheory.FlagBase.MeanCov.measurable_detNorm E j
  rw [ae_iff]
  have hs : MeasurableSet {g : MatInf E j | ¬ 0 < detNorm E j g} :=
    (measurableSet_lt measurable_const hm).compl
  have hz : ∀ g ∈ {g : MatInf E j | ¬ 0 < detNorm E j g},
      ENNReal.ofReal ((detNorm E j g)⁻¹ ^ j) = 0 := by
    intro g hg
    have hnn : 0 ≤ detNorm E j g := by
      unfold detNorm
      exact Finset.prod_nonneg fun w _ => by positivity
    have h0 : detNorm E j g = 0 := le_antisymm (not_lt.mp hg) hnn
    rw [h0, _root_.inv_zero, zero_pow (by omega), ENNReal.ofReal_zero]
  unfold haarGL
  refine (withDensity_apply _ hs).trans ?_
  refine (setLIntegral_congr_fun hs hz).trans ?_
  simp

theorem latMean_covAt : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ w : ℝ → ENNReal, Measurable w → latMean E j (fun L => w (covAt E j L)) = glVol E j * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal t := by
  intro E _ _ hE j hj w hw
  unfold latMean glVol
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun c => ?_
  obtain ⟨κ, hκ, hL⟩ := (GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE j).1 (Quot.out c).1 (Quot.out c).2
  have hF : Measurable fun t : ℝ => w (κ / t) := hw.comp (measurable_const.div measurable_id)
  have hd : (haarGL E j).withDensity (fun g => w (covAt E j (latAt E j (Quot.out c).1 g)))
      = (haarGL E j).withDensity (fun g => w (κ / detNorm E j g)) := by
    refine withDensity_congr_ae ?_
    filter_upwards [GlobalTheory.FlagBase.MeanCov.ae_detNorm_pos E j hj] with g hg
    rw [(hL g hg).2.1]
  rw [hd]
  refine (GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq E hE j hj _ (Quot.out c).2 (fun t => w (κ / t)) hF).trans ?_
  congr 1
  exact GlobalTheory.FlagBase.MeanCov.lintegral_div_inv κ hκ w

end GlobalTheory.FlagBase.MeanCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicClassFunBlockDiagonalEqSumDerivativesStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicClassFun_blockDiagonal_eq_sum_derivatives : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (k : ℕ) (F : Gn g (k + 1) → ℂ), IsMirClass F → ∀ h : Gn g k, F (diag1 h (k + 1)) = ∑ i ∈ Finset.range (k + 1), hc i (k - i) (der ψ i F) (gg ψ (k - i)) k h := by
  first | exact @GlobalTheory.GLm.mirClass_diag1_eq_sum | exact GlobalTheory.GLm.mirClass_diag1_eq_sum | (intros; apply GlobalTheory.GLm.mirClass_diag1_eq_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverOfNorm
section
namespace GlobalTheory.RankSplit

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

private lemma span_prime_isMaximal' {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
private lemma liesOver_span_of_prime_natCast_mem {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (P : Ideal A) [hP : P.IsPrime]
    (h : (p : A) ∈ P) : P.LiesOver (Ideal.span {(p : ℤ)}) := by
  refine ⟨(span_prime_isMaximal' hp).eq_of_le (Ideal.IsPrime.comap (algebraMap ℤ A)).ne_top ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
  simpa using h

theorem ncard_primesOver_of_norm {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) → Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  classical
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
  haveI := span_prime_isMaximal' hp
  rw [← Ideal.sum_ramification_inertia (R := ℤ) (S := 𝓞 E) ℚ E hp0,
    ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp0] at hP
  obtain ⟨hPp, hPl⟩ := hP
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  haveI hPm : P.IsMaximal := hPp.isMaximal hPne
  have hpP : (p : 𝓞 E) ∈ P := by
    have := (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.mem_span_singleton_self _)
    simpa using this
  obtain ⟨hn, hsq⟩ := h P hPm hpP
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have he : Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [hmap, pow_one, Ideal.span_singleton_le_iff_mem]
      exact hpP
    · rw [hmap, Ideal.span_singleton_le_iff_mem]
      exact hsq
  have hf : Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) P = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    have h1 := Ideal.pow_inertiaDeg p P
    rw [hn] at h1
    exact (Nat.pow_eq_self_iff hp.one_lt).mp h1
  rw [he, hf]

theorem splitsF_of_norm : ∀ (D : D7) (p : ℕ), p.Prime →
    (∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ((p : 𝓞 D.host.E) ∈ P) →
      Ideal.absNorm P = p ∧ (p : 𝓞 D.host.E) ∉ P ^ 2) → StandardLattice.SplitsF D p := by
  intro D p hp h
  have hE := ncard_primesOver_of_norm hp h
  have hF := GlobalTheory.ColClassCompare.ncard_primesOver_of_split (F := D.host.F) hp hE
  rw [GlobalTheory.ColClassCompare.finrank_F] at hF
  refine ⟨?_, fun v hv => (GlobalTheory.ColClassCompare.unram_card_of_split (F := D.host.F) hp hE v.asIdeal hv).2⟩
  rw [← hF, ← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun v => ⟨v.1.asIdeal, v.1.isPrime, liesOver_span_of_prime_natCast_mem hp v.1.asIdeal v.2⟩
      invFun := fun P => ⟨⟨P.1, P.2.1, ?_⟩, ?_⟩
      left_inv := fun v => rfl
      right_inv := fun P => rfl }
  · have := P.2.2
    have h0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
    exact Ideal.ne_bot_of_liesOver_of_ne_bot h0 P.1
  · have := P.2.2
    have h2 := (Ideal.mem_of_liesOver P.1 (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.mem_span_singleton_self _)
    simpa using h2

end GlobalTheory.RankSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NegLogProdLValEtaLeAndPosStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_log_prod_lValEta_le_and_pos : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ n₀ n : ℕ, 2 ≤ n₀ → -Real.log (∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M) ≤ Formalism.HermitianLatticesTheory.fDeg E * (2 : ℝ) ^ ((1 : ℤ) - n₀) ∧ 0 < ∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M := by
  first | exact @GlobalTheory.FlagMeas.LProd.neg_log_prod_le | exact GlobalTheory.FlagMeas.LProd.neg_log_prod_le | (intros; apply GlobalTheory.FlagMeas.LProd.neg_log_prod_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilradicalCenterIntegralCoveringRadiusStatement
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilradicalCenter_integral_covering_radius : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → hi ^ 2 ≤ rho / 4 → ∀ Z ∈ cenReal I R, ∃ Z₀ ∈ cenInt I x R, normAt I x (Z - diagEmb I Z₀) ≤ ((I.n : ℝ) ^ 2 * I.f) * I.rd * rho / (16 * Real.sqrt I.f) := by
  first | exact @GlobalTheory.Count.CentralCover.main | exact GlobalTheory.Count.CentralCover.main | (intros; apply GlobalTheory.Count.CentralCover.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivarianceStatement
section
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_polar_decomposition_equivariance : PsiPolar := by
  first | exact @GlobalTheory.Dec.psiPolar | exact GlobalTheory.Dec.psiPolar | (intros; apply GlobalTheory.Dec.psiPolar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOneStatement
section
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_restriction_holomorphic_near_one : PsLocal := by
  first | exact @GlobalTheory.Dec.psLocal | exact GlobalTheory.Dec.psLocal | (intros; apply GlobalTheory.Dec.psLocal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallSizeCanonicalFlagPiecesPropertiesStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallSizeCanonicalFlag_pieces_properties : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i, SatX I x (S i) ∧ SatX I x (perpIn I x (S i)) ∧ S i ≤ perpIn I x (S (Fin.last a)) ∧ perpIn I x (S (Fin.last a)) ≤ perpIn I x (S i) ∧ rkK (perpIn I x (S i)) + rkK (S i) = I.n) ∧ perpIn I x (S 0) = lamX I x ∧ SizesLe I x (perpIn I x (S (Fin.last a))) (S (Fin.last a)) 2 ∧ ∀ i : Fin a, SizesGe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (perpIn I x (S i.castSucc)) (perpIn I x (S i.succ)) (τ i)⁻¹ ∧ S i.succ ≠ ⊥ ∧ largestSize (bas I) (frm I x) (S i.succ) ≤ τ i ∧ SizesGe I x (lamX I x) (S i.succ) (if h : (i : ℕ) + 1 < a then τ ⟨i + 1, h⟩ else 1 / 2) := by
  first | exact @GlobalTheory.FlagPieces.flag_pieces | exact GlobalTheory.FlagPieces.flag_pieces | (intros; apply GlobalTheory.FlagPieces.flag_pieces <;> assumption)
end

