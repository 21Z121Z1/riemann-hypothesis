import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0222
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0739
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallySmall
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

def res (H : G D p → ℝ≥0) (f : G D p → ℂ) (σ : ℝ) (h : G D p) : ℂ :=
  ((σ - p / 2 : ℝ) : ℂ) * eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) h

def ufil (p : ℕ) : Ultrafilter ℝ := Ultrafilter.of (𝓝[>] ((p : ℝ) / 2))

theorem ufil_le (p : ℕ) : ((ufil p : Ultrafilter ℝ) : Filter ℝ) ≤ 𝓝[>] ((p : ℝ) / 2) := by
  unfold ufil
  exact Ultrafilter.of_le _

def resA (H : G D p → ℝ≥0) (f : G D p → ℂ) (h : G D p) : ℂ :=
  limUnder ((ufil p : Ultrafilter ℝ) : Filter ℝ) fun σ => res H f σ h

theorem abs_pos' (u : (AE D)ˣ) : 0 < absA D u := by
  exact pos_iff_ne_zero.mpr ((Group.isUnit u).map (absA D)).ne_zero

theorem fam_law {n : ℕ} {H : G D n → ℝ≥0} (hH : IsHt H) {χ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : G D n → ℂ} (h : IsLaw χ s₁ φ)
    (z : ℂ) : IsLaw χ z (fam H φ s₁ z) := by
  intro q hq a ha g
  have hx : (0:ℝ) < (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) := NNReal.coe_pos.mpr (abs_pos' _)
  have hxne : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [fam, npow, hH.2.2 q hq a ha g, h q hq a ha g, NNReal.coe_mul, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hx.le (NNReal.coe_nonneg _)]
  have e : z + (n : ℂ) / 2 = (z - s₁) + (s₁ + (n : ℂ) / 2) := by ring
  rw [e, Complex.cpow_add (z - s₁) (s₁ + (n : ℂ) / 2) hxne]
  ring

theorem fam_cont {n : ℕ} {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} (hφ : Continuous φ) (s₁ : ℂ) :
    Continuous fun u : ℝ × G D n => fam H φ s₁ (u.1 : ℂ) u.2 := by
  unfold fam npow
  refine Continuous.mul (Continuous.cpow ?_ ?_ ?_) (hφ.comp continuous_snd)
  · exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (hH.1.comp continuous_snd))
  · exact (Complex.continuous_ofReal.comp continuous_fst).sub continuous_const
  · intro u
    exact Complex.ofReal_mem_slitPlane.mpr (NNReal.coe_pos.mpr (hH.2.1 u.2))

theorem law_sub {n : ℕ} {s : ℂ} {φ φ' : G D n → ℂ} {χ : (AE D)ˣ →* Circle} (h : IsLaw χ s φ) (h' : IsLaw χ s φ') :
    IsLaw χ s (φ - φ') := by
  intro q hq a ha g
  show φ (q * g) - φ' (q * g) = _ * (φ g - φ' g)
  rw [h q hq a ha g, h' q hq a ha g]
  ring

theorem law_right {n : ℕ} {s : ℂ} {φ : G D n → ℂ} {χ : (AE D)ˣ →* Circle} (h : IsLaw χ s φ) (x : G D n) :
    IsLaw χ s (fun g => φ (g * x)) := by
  intro q hq a ha g
  show φ (q * g * x) = _ * φ (g * x)
  rw [mul_assoc]
  exact h q hq a ha (g * x)

theorem law_bound {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {σ : ℝ}
    {s : G D p → ℂ} (hs : IsLaw 1 (σ : ℂ) s) {δ : ℝ} (hδ : ∀ c ∈ C, ‖s c‖ ≤ δ * (H c : ℝ) ^ (σ + p / 2)) (g : G D p) :
    ‖s g‖ ≤ δ * (H g : ℝ) ^ (σ + p / 2) := by
  obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hq
  have hx : (0:ℝ) < (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) := NNReal.coe_pos.mpr (abs_pos' _)
  have hHc : (0:ℝ) < (H c : ℝ) := NNReal.coe_pos.mpr (hH.2.1 c)
  rw [hs q hq a ha c, hH.2.2 q hq a ha c]
  have e1 : ((σ : ℂ) + (p : ℂ) / 2) = (((σ + p / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [norm_mul, norm_mul, e1]
  simp only [npow, MonoidHom.one_apply, Circle.coe_one, norm_one, one_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.ofReal_re, NNReal.coe_mul, Real.mul_rpow hx.le hHc.le]
  calc _ ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (σ + p / 2) * (δ * (H c : ℝ) ^ (σ + p / 2)) :=
        mul_le_mul_of_nonneg_left (hδ c hc) (Real.rpow_nonneg hx.le _)
    _ = _ := by ring

theorem exists_bound {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {σ : ℝ} {s : G D p → ℂ} (hc : Continuous s) (hs : IsLaw 1 (σ : ℂ) s) :
    ∃ δ : ℝ, ∀ g, ‖s g‖ ≤ δ * (H g : ℝ) ^ (σ + p / 2) := by
  have hcont : ContinuousOn (fun c => ‖s c‖ / (H c : ℝ) ^ (σ + p / 2)) C := by
    refine ContinuousOn.div hc.norm.continuousOn ?_ ?_
    · exact ((NNReal.continuous_coe.comp hH.1).rpow_const (fun c => Or.inl (NNReal.coe_pos.mpr (hH.2.1 c)).ne')).continuousOn
    · intro c _
      exact (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (hH.2.1 c)) _).ne'
  obtain ⟨δ, hδ⟩ := hC.exists_bound_of_continuousOn hcont
  refine ⟨δ, law_bound hH hcov hs (fun c hc => ?_)⟩
  have hpos := Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (hH.2.1 c)) (σ + p / 2)
  have := hδ c hc
  rw [Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos hpos, div_le_iff₀ hpos] at this
  exact this

theorem eis_bound (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1), ∀ h ∈ C, ∀ (s : G D p → ℂ) (δ : ℝ),
      (∀ g, ‖s g‖ ≤ δ * (H g : ℝ) ^ (σ + p / 2)) →
      CosetConv (P D p) (GF D p) s h ∧ (σ - p / 2) * ‖eisS s h‖ ≤ δ * B := by
  obtain ⟨B, hB⟩ := hS D p hp H hH C hC
  refine ⟨max B 0, le_max_right _ _, fun σ hσ h hh s δ hs => ?_⟩
  obtain ⟨hsum, hle⟩ := hB σ hσ h hh
  have hσ0 : 0 < σ - p / 2 := by linarith [hσ.1]
  have hδ : 0 ≤ δ := by
    have h1 := (norm_nonneg _).trans (hs 1)
    have h2 : 0 < (H 1 : ℝ) ^ (σ + p / 2) := Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (hH.2.1 1)) _
    exact le_of_mul_le_mul_right (by rw [zero_mul]; exact h1) h2
  have hbd : ∀ q : GlobalTheory.Eis.Cosets (P D p) (GF D p), ‖GlobalTheory.Eis.term (P D p) (GF D p) s h q‖ ≤ δ * (H (↑(Quotient.out q) * h) : ℝ) ^ (σ + p / 2) := fun q => hs _
  have hconv : CosetConv (P D p) (GF D p) s h := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd (hsum.mul_left δ)
  refine ⟨hconv, ?_⟩
  have h1 : ‖eisS s h‖ ≤ δ * ∑' q : GlobalTheory.Eis.Cosets (P D p) (GF D p), (H (↑(Quotient.out q) * h) : ℝ) ^ (σ + p / 2) := by
    unfold eisS GlobalTheory.Eis.cosetSum
    refine (norm_tsum_le_tsum_norm hconv).trans ?_
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hbd hconv (hsum.mul_left δ)
  calc (σ - p / 2) * ‖eisS s h‖ ≤ (σ - p / 2) * (δ * ∑' q : GlobalTheory.Eis.Cosets (P D p) (GF D p), (H (↑(Quotient.out q) * h) : ℝ) ^ (σ + p / 2)) := mul_le_mul_of_nonneg_left h1 hσ0.le
    _ = δ * ((σ - p / 2) * ∑' q : GlobalTheory.Eis.Cosets (P D p) (GF D p), (H (↑(Quotient.out q) * h) : ℝ) ^ (σ + p / 2)) := by ring
    _ ≤ δ * max B 0 := mul_le_mul_of_nonneg_left (hle.trans (le_max_left _ _)) hδ

theorem eis_sub {s s' : G D p → ℂ} {h : G D p} (hc : CosetConv (P D p) (GF D p) s h) (hc' : CosetConv (P D p) (GF D p) s' h) :
    eisS (s - s') h = eisS s h - eisS s' h := by
  have h1 : Summable fun q => GlobalTheory.Eis.term (P D p) (GF D p) s h q := Summable.of_norm hc
  have h2 : Summable fun q => GlobalTheory.Eis.term (P D p) (GF D p) s' h q := Summable.of_norm hc'
  unfold eisS GlobalTheory.Eis.cosetSum
  exact h1.tsum_sub h2

theorem conv_of_section (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {σ : ℝ} (hσ : σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1)) {s : G D p → ℂ}
    (hc : Continuous s) (hs : IsLaw 1 (σ : ℂ) s) (h : G D p) : CosetConv (P D p) (GF D p) s h := by
  obtain ⟨δ, hδ⟩ := exists_bound hH hC hcov hc hs
  obtain ⟨B, _, hB⟩ := eis_bound hS hp hH (isCompact_singleton (x := h))
  exact (hB σ hσ h (Set.mem_singleton h) s δ hδ).1

theorem eventually_small {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C) {T : ℝ → G D p → ℂ}
    (hc : ContinuousOn (fun u : ℝ × G D p => T u.1 u.2) (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ))
    (h0 : ∀ c, T ((p : ℝ) / 2) c = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ σ in 𝓝[>] ((p : ℝ) / 2), ∀ c ∈ C, ‖T σ c‖ ≤ ε * (H c : ℝ) ^ (σ + p / 2) := by
  have hHpos : ∀ c, (0:ℝ) < (H c : ℝ) := fun c => NNReal.coe_pos.mpr (hH.2.1 c)
  set F : ℝ × G D p → ℝ := fun u => ‖T u.1 u.2‖ / (H u.2 : ℝ) ^ (u.1 + p / 2) with hF
  have hFc : ContinuousOn F (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ) := by
    refine ContinuousOn.div hc.norm ?_ ?_
    · exact (Continuous.rpow (NNReal.continuous_coe.comp (hH.1.comp continuous_snd)) (continuous_fst.add continuous_const) (fun u => Or.inl (hHpos u.2).ne')).continuousOn
    · intro u _
      exact (Real.rpow_pos_of_pos (hHpos u.2) _).ne'
  have hP : ∀ c ∈ C, ∀ᶠ z : ℝ × G D p in 𝓝 (((p : ℝ) / 2), c), z.1 ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) → F (z.1, z.2) < ε := by
    intro c _
    have hmem : (((p : ℝ) / 2), c) ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ (univ : Set (G D p)) := ⟨⟨le_rfl, by linarith⟩, mem_univ _⟩
    have ht := (hFc _ hmem).tendsto
    have h0' : F (((p : ℝ) / 2), c) = 0 := by simp [hF, h0]
    rw [h0'] at ht
    have hh := ht.eventually (gt_mem_nhds hε)
    rw [eventually_nhdsWithin_iff] at hh
    exact hh.mono fun z hz h1 => hz ⟨h1, mem_univ _⟩
  have hev := hC.eventually_forall_of_forall_eventually (P := fun σ c => σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) → F (σ, c) < ε) hP
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, Ioc_mem_nhdsGT (show (p : ℝ) / 2 < p / 2 + 1 by linarith)] with σ hσ hI c hc
  have := hσ c hc (Ioc_subset_Icc_self hI)
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos (hHpos c) _)).mp this).le

theorem ev_Ioc (p : ℕ) : ∀ᶠ σ in 𝓝[>] ((p : ℝ) / 2), σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1) := by
  exact Ioc_mem_nhdsGT (by linarith)

theorem tendsto_diff (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {S S' : ℝ → G D p → ℂ}
    (hc : ContinuousOn (fun u : ℝ × G D p => S u.1 u.2) (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ))
    (hc' : ContinuousOn (fun u : ℝ × G D p => S' u.1 u.2) (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ))
    (hl : ∀ σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1), IsLaw 1 (σ : ℂ) (S σ))
    (hl' : ∀ σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1), IsLaw 1 (σ : ℂ) (S' σ))
    (h0 : S ((p : ℝ) / 2) = S' ((p : ℝ) / 2)) :
    Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) * (eisS (S σ) 1 - eisS (S' σ) 1)) (𝓝[>] ((p : ℝ) / 2)) (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := eis_bound hS hp hH (isCompact_singleton (x := (1 : G D p)))
  have hcont : ∀ σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1), Continuous (S σ) := fun σ hσ =>
    hc.comp_continuous (f := fun c : G D p => (σ, c)) (by fun_prop) (fun c => ⟨hσ, mem_univ _⟩)
  have hcont' : ∀ σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1), Continuous (S' σ) := fun σ hσ =>
    hc'.comp_continuous (f := fun c : G D p => (σ, c)) (by fun_prop) (fun c => ⟨hσ, mem_univ _⟩)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / (B + 1) := div_pos hε (by linarith)
  have hsmall := eventually_small (T := fun σ => S σ - S' σ) hH hC (hc.sub hc') (fun c => by simp [h0]) hε'
  filter_upwards [hsmall, ev_Ioc p] with σ hσs hσ
  have hσI : σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) := Ioc_subset_Icc_self hσ
  have hlaw : IsLaw 1 (σ : ℂ) (S σ - S' σ) := law_sub (hl σ hσI) (hl' σ hσI)
  have hall := law_bound hH hcov hlaw hσs
  obtain ⟨_, hb⟩ := hB σ hσ 1 (Set.mem_singleton _) (S σ - S' σ) (ε / (B + 1)) hall
  have hconv := conv_of_section hS hp hH hC hcov hσ (hcont σ hσI) (hl σ hσI) 1
  have hconv' := conv_of_section hS hp hH hC hcov hσ (hcont' σ hσI) (hl' σ hσI) 1
  rw [dist_zero_right, ← eis_sub hconv hconv', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hσ.1])]
  calc _ ≤ ε / (B + 1) * B := hb
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

theorem fam_bound {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} {δ : ℝ} (hf : ∀ g, ‖f g‖ ≤ δ * (H g : ℝ) ^ p) (σ : ℝ) (g : G D p) :
    ‖fam H f ((p : ℂ) / 2) (σ : ℂ) g‖ ≤ δ * (H g : ℝ) ^ (σ + p / 2) := by
  have hHg : (0:ℝ) < (H g : ℝ) := NNReal.coe_pos.mpr (hH.2.1 g)
  unfold fam npow
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hHg]
  have hre : ((σ : ℂ) - (p : ℂ) / 2).re = σ - p / 2 := by simp
  rw [hre]
  calc _ ≤ (H g : ℝ) ^ (σ - p / 2) * (δ * (H g : ℝ) ^ p) := mul_le_mul_of_nonneg_left (hf g) (Real.rpow_nonneg hHg.le _)
    _ = δ * ((H g : ℝ) ^ (σ - p / 2) * (H g : ℝ) ^ ((p : ℕ) : ℝ)) := by rw [Real.rpow_natCast]; ring
    _ = δ * (H g : ℝ) ^ (σ + p / 2) := by
      rw [← Real.rpow_add hHg]
      congr 2
      ring

theorem rho_law {f : G D p → ℂ} (hf : IsRho f) : IsLaw 1 (((p : ℝ) / 2 : ℝ) : ℂ) f := by
  have e : ((((p : ℝ) / 2 : ℝ)) : ℂ) = (p : ℂ) / 2 := by push_cast; ring
  rw [e]
  exact hf.2

theorem rho_bound {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) :
    ∃ δ : ℝ, ∀ g, ‖f g‖ ≤ δ * (H g : ℝ) ^ p := by
  obtain ⟨δ, hδ⟩ := exists_bound hH hC hcov hf.1 (rho_law hf)
  refine ⟨δ, fun g => ?_⟩
  have := hδ g
  have e : ((p : ℝ) / 2 + p / 2) = ((p : ℕ) : ℝ) := by ring
  rw [e, Real.rpow_natCast] at this
  exact this

theorem res_bound (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C' : Set (G D p)} (hC' : IsCompact C') :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : G D p → ℂ) (δ : ℝ), (∀ g, ‖f g‖ ≤ δ * (H g : ℝ) ^ p) →
      ∀ σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1), ∀ h ∈ C', ‖res H f σ h‖ ≤ δ * B := by
  obtain ⟨B, hB0, hB⟩ := eis_bound hS hp hH hC'
  refine ⟨B, hB0, fun f δ hf σ hσ h hh => ?_⟩
  obtain ⟨_, hb⟩ := hB σ hσ h hh _ δ (fam_bound hH hf σ)
  unfold res
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hσ.1])]
  exact hb

theorem res_tendsto (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (h : G D p) :
    Tendsto (fun σ => res H f σ h) ((ufil p : Ultrafilter ℝ) : Filter ℝ) (𝓝 (resA H f h)) := by
  obtain ⟨δ, hδ⟩ := rho_bound hH hC hcov hf
  obtain ⟨B, _, hB⟩ := res_bound hS hp hH (isCompact_singleton (x := h))
  have hev : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), res H f σ h ∈ Metric.closedBall (0 : ℂ) (δ * B) := by
    refine Filter.Eventually.filter_mono (ufil_le p) ((ev_Ioc p).mono fun σ hσ => ?_)
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hB f δ hδ σ hσ h (Set.mem_singleton _)
  obtain ⟨x, _, hx⟩ := (isCompact_closedBall (0 : ℂ) (δ * B)).ultrafilter_le_nhds ((ufil p).map fun σ => res H f σ h)
    (by rw [Ultrafilter.coe_map, Filter.le_principal_iff]; exact hev)
  unfold resA
  exact tendsto_nhds_limUnder ⟨x, by rw [Ultrafilter.coe_map] at hx; exact hx⟩

end GlobalTheory.CompanionTheory.ResMu
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKFiniteSubmoduleContaining
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.LocFin

section Abstract

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι κ : Type}

def stp (L : ι → Module.End ℂ V) (S : Submodule ℂ V) : Submodule ℂ V := S ⊔ ⨆ i, S.map (L i)

def fil (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) (k : ℕ) : Submodule ℂ V := (stp L)^[k] S₀

theorem fil_succ (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) (k : ℕ) :
    fil L S₀ (k + 1) = stp L (fil L S₀ k) :=
  Function.iterate_succ_apply' _ _ _

theorem le_stp (L : ι → Module.End ℂ V) (S : Submodule ℂ V) : S ≤ stp L S := le_sup_left

theorem letter_mem_stp (L : ι → Module.End ℂ V) {S : Submodule ℂ V} {u : V} (hu : u ∈ S) (i : ι) :
    L i u ∈ stp L S :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hu))

theorem span_mem_stp (L : ι → Module.End ℂ V) {S : Submodule ℂ V} {u : V} (hu : u ∈ S)
    {C : Module.End ℂ V} (hC : C ∈ Submodule.span ℂ (Set.range L)) : C u ∈ stp L S := by
  induction hC using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact letter_mem_stp L hu i
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem fil_mono (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) : Monotone (fil L S₀) :=
  monotone_nat_of_le_succ fun k => by
    rw [fil_succ]
    exact le_stp L _

theorem fil_finite [Finite ι] (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) [h₀ : FiniteDimensional ℂ S₀] (k : ℕ) :
    FiniteDimensional ℂ (fil L S₀ k) := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    rw [fil_succ]
    have : ∀ i, FiniteDimensional ℂ ((fil L S₀ k).map (L i)) := fun i => inferInstance
    have : FiniteDimensional ℂ ↥(⨆ i, (fil L S₀ k).map (L i) : Submodule ℂ V) := Submodule.finiteDimensional_iSup _
    exact Submodule.finiteDimensional_sup _ _

theorem stp_stable (L : ι → Module.End ℂ V) (K : Module.End ℂ V)
    (hK : ∀ i, K * L i - L i * K ∈ Submodule.span ℂ (Set.range L)) {S : Submodule ℂ V}
    (hS : ∀ w ∈ S, K w ∈ S) : ∀ w ∈ stp L S, K w ∈ stp L S := by
  have key : stp L S ≤ (stp L S).comap K := by
    refine sup_le (fun w hw => le_stp L S (hS w hw)) (iSup_le fun i => ?_)
    rintro _ ⟨u, hu, rfl⟩
    have h1 : L i (K u) ∈ stp L S := letter_mem_stp L (hS u hu) i
    have h2 : (K * L i - L i * K) u ∈ stp L S := span_mem_stp L hu (hK i)
    have h3 : K (L i u) = (K * L i - L i * K) u + L i (K u) := by simp
    change K (L i u) ∈ stp L S
    rw [h3]
    exact add_mem h2 h1
  exact fun w hw => key hw

theorem fil_stable (L : ι → Module.End ℂ V) (K : Module.End ℂ V)
    (hK : ∀ i, K * L i - L i * K ∈ Submodule.span ℂ (Set.range L)) {S₀ : Submodule ℂ V}
    (h₀ : ∀ w ∈ S₀, K w ∈ S₀) (k : ℕ) : ∀ w ∈ fil L S₀ k, K w ∈ fil L S₀ k := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    rw [fil_succ]
    exact stp_stable L K hK ih

theorem mem_fil_of_adjoin (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) {T : Module.End ℂ V}
    (hT : T ∈ Algebra.adjoin ℂ (Set.range L)) {f : V} (hf : f ∈ S₀) : ∃ k, T f ∈ fil L S₀ k := by
  have key : ∀ w, (∃ k, w ∈ fil L S₀ k) → ∃ k, T w ∈ fil L S₀ k := by
    induction hT using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rintro w ⟨k, hk⟩
      exact ⟨k + 1, by rw [fil_succ]; exact letter_mem_stp L hk i⟩
    | algebraMap r =>
      rintro w ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simpa [Module.algebraMap_end_apply] using Submodule.smul_mem _ r hk
    | add x y _ _ hx hy =>
      intro w hw
      obtain ⟨k, hk⟩ := hx w hw
      obtain ⟨m, hm⟩ := hy w hw
      refine ⟨max k m, ?_⟩
      simpa using add_mem (fil_mono L S₀ (le_max_left k m) hk) (fil_mono L S₀ (le_max_right k m) hm)
    | mul x y _ _ hx hy =>
      intro w hw
      simpa using hx (y w) (hy w hw)
  exact key f ⟨0, hf⟩

end Abstract

section Pair

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def letters (F1 F2 : Fin n → Fin n → Module.End ℂ V) : Bool × Fin n × Fin n → Module.End ℂ V
  | (true, a, b) => F1 a b
  | (false, a, b) => F2 a b

theorem range_letters (F1 F2 : Fin n → Fin n → Module.End ℂ V) :
    Set.range (letters F1 F2) = {x | ∃ a b, x = F1 a b ∨ x = F2 a b} := by
  ext x
  constructor
  · rintro ⟨⟨_ | _, a, b⟩, rfl⟩
    · exact ⟨a, b, Or.inr rfl⟩
    · exact ⟨a, b, Or.inl rfl⟩
  · rintro ⟨a, b, rfl | rfl⟩
    · exact ⟨(true, a, b), rfl⟩
    · exact ⟨(false, a, b), rfl⟩

theorem gl_span (F1 F2 : Fin n → Fin n → Module.End ℂ V) (e : Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hE : ∀ a b, E a b = letters F1 F2 (e, a, b)) (a b c d : Fin n) :
    (if b = c then E a d else 0) - (if d = a then E c b else 0) ∈
      Submodule.span ℂ (Set.range (letters F1 F2)) := by
  have hm : ∀ a b, E a b ∈ Submodule.span ℂ (Set.range (letters F1 F2)) := fun a b =>
    Submodule.subset_span ⟨(e, a, b), (hE a b).symm⟩
  refine sub_mem ?_ ?_
  · split_ifs
    · exact hm _ _
    · exact zero_mem _
  · split_ifs
    · exact hm _ _
    · exact zero_mem _

theorem comm_letters {F1 F2 : Fin n → Fin n → Module.End ℂ V} (h1 : Formalism.REAL.GlRel F1) (h2 : Formalism.REAL.GlRel F2)
    (hc : ∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) (a b : Fin n) (i : Bool × Fin n × Fin n) :
    kF F1 F2 a b * letters F1 F2 i - letters F1 F2 i * kF F1 F2 a b ∈
      Submodule.span ℂ (Set.range (letters F1 F2)) := by
  obtain ⟨_ | _, c, d⟩ := i
  · have h : kF F1 F2 a b * F2 c d - F2 c d * kF F1 F2 a b =
        (if b = c then F2 a d else 0) - (if d = a then F2 c b else 0) := by
      rw [← h2 a b c d]
      simp only [kF, add_mul, mul_add, hc a b c d]
      abel
    change kF F1 F2 a b * F2 c d - F2 c d * kF F1 F2 a b ∈ _
    rw [h]
    exact gl_span F1 F2 false F2 (fun _ _ => rfl) a b c d
  · have h : kF F1 F2 a b * F1 c d - F1 c d * kF F1 F2 a b =
        (if b = c then F1 a d else 0) - (if d = a then F1 c b else 0) := by
      rw [← h1 a b c d]
      simp only [kF, add_mul, mul_add, hc c d a b]
      abel
    change kF F1 F2 a b * F1 c d - F1 c d * kF F1 F2 a b ∈ _
    rw [h]
    exact gl_span F1 F2 true F1 (fun _ _ => rfl) a b c d

end Pair

theorem cyclic_locFin : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (F1 F2 : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel F1 → Formalism.REAL.GlRel F2 →
    (∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) → ∀ f : V, (∀ x : V, ∃ T ∈ alg F1 F2, T f = x) →
    ∀ S₀ : Submodule ℂ V, FiniteDimensional ℂ S₀ → f ∈ S₀ → (∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) →
    ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
  intro n V _ _ F1 F2 h1 h2 hc f hgen S₀ hfin hf hst x
  obtain ⟨T, hT, rfl⟩ := hgen x
  have hT' : T ∈ Algebra.adjoin ℂ (Set.range (letters F1 F2)) := by
    rw [range_letters]
    exact hT
  obtain ⟨k, hk⟩ := mem_fil_of_adjoin (letters F1 F2) S₀ hT' hf
  exact ⟨fil (letters F1 F2) S₀ k, fil_finite _ _ k, hk, fun a b =>
    fil_stable _ _ (comm_letters h1 h2 hc a b) (hst a b) k⟩

end GlobalTheory.CompanionTheory.ModelS.LocFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteOfCommute
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem commute_epow_of_units {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V)
    (hT : ∀ a b, T * E a b = E a b * T) (m : ℕ) (a b : Fin n) :
    Commute T (epow E m a b) := by
  induction m generalizing a b with
  | zero =>
    simp only [epow]
    split_ifs
    · exact Commute.one_right T
    · exact Commute.zero_right T
  | succ m ih =>
    simp only [epow]
    exact Commute.sum_right _ _ _ fun c _ => Commute.mul_right (hT a c) (ih c b)

theorem gelA_commute_of_units : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V),
    (∀ a b, T * E a b = E a b * T) → ∀ m : ℕ, gelA E m * T = T * gelA E m := by
  intro n V _ _ E T hT m
  have h : Commute T (gelA E m) :=
    Commute.sum_right _ _ _ fun a _ => commute_epow_of_units E T hT m a a
  exact h.eq.symm

end GlobalTheory.CompanionTheory.ModelS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandValuePermInvariant
section
theorem GlobalTheory.CompanionTheory.ModelS.gelfVal_perm :
    ∀ (n : ℕ) (χ : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ),
      GlobalTheory.Dec.gelfVal (fun a => χ (σ a)) k = GlobalTheory.Dec.gelfVal χ k :=
  fun _ χ σ k => GlobalTheory.CompanionTheory.WaveMult.gelfVal_comp_perm χ σ k
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HCoContinuousAddEquivStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homeomorph_hermR_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), ∃ e : HermR R σ n ≃ₜ+ (Idx n d → R), ∀ S, e S = hCo R σ b S := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_continuousAddEquiv | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_continuousAddEquiv | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_continuousAddEquiv <;> assumption)
end

