import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFubiniTwoLiftsModerateGrowthKernels
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.Seesaw

variable {D : D7}

theorem out_eq_sec {V : HSp D} {X : Type*} {φ : GA D V → X} (h : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (q : AutQ V) :
    φ q.out = φ (sec (GQ V) q) :=
  LeftInv.eq_of_mk_eq (Γ := GQ V) h ((Quotient.out_eq q).trans (mk_sec q).symm)

theorem measurable_out {V : HSp D} {φ : GA D V → ℂ} (h : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (hc : Continuous φ) :
    Measurable fun q : AutQ V => φ q.out := by
  have e : (fun q : AutQ V => φ q.out) = φ ∘ sec (GQ V) := funext (out_eq_sec h)
  rw [e]
  exact hc.measurable.comp measurableEmbedding_sec.measurable

theorem measurable_kernel_out {A B : HSp D} {K : GA D A → GA D B → ℂ} (hc : Continuous (Function.uncurry K))
    (hl : ∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) (hr : ∀ g, ∀ γ ∈ GQ B, ∀ h, K g (γ * h) = K g h) :
    Measurable (Function.uncurry fun (q : AutQ A) (y : AutQ B) => K q.out y.out) := by
  have e : (Function.uncurry fun (q : AutQ A) (y : AutQ B) => K q.out y.out) =
      Function.uncurry K ∘ fun p => (sec (GQ A) p.1, sec (GQ B) p.2) := by
    funext p
    show K p.1.out p.2.out = K (sec (GQ A) p.1) (sec (GQ B) p.2)
    rw [out_eq_sec (φ := fun g => K g p.2.out) (fun γ hγ g => hl γ hγ g _) p.1, out_eq_sec (hr _) p.2]
  rw [e]
  exact hc.measurable.comp ((measurableEmbedding_sec.measurable.comp measurable_fst).prodMk
    (measurableEmbedding_sec.measurable.comp measurable_snd))

theorem integrable_lift_integrand {A B : HSp D} (m : Measure (GA D A)) (hm : m.IsHaarMeasure)
    {K : GA D A → GA D B → ℂ} (hc : Continuous (Function.uncurry K)) (hl : ∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h)
    (hg : ∀ h, GlobalTheory.Grow.ModGrowth A fun g => K g h) {u : GA D A → ℂ} (hu : GlobalTheory.Grow.RapidDec A u) (h : GA D B) :
    Integrable (descend (GQ A) fun g => K g h * u g) (autMeasure A m) := by
  obtain ⟨C, a, hC⟩ := hg h
  have hb := GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => K g h) (fun γ hγ g => hl γ hγ g h) hC
  have hKc : Continuous fun g => K g h := hc.comp (continuous_id.prodMk continuous_const)
  have hmeas : Measurable (descend (GQ A) fun g => K g h * u g) :=
    measurable_out (φ := fun g => K g h * u g) (fun γ hγ g => by simp only [hl γ hγ, hu.1 γ hγ]) (hKc.mul hu.2.1)
  refine ((GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D A m hm u hu a).const_mul (C * 2 ^ a)).mono' hmeas.aestronglyMeasurable
    (ae_of_all _ fun q => ?_)
  show ‖K q.out h * u q.out‖ ≤ C * 2 ^ a * (GlobalTheory.Grow.quotHeight A q.out ^ a * ‖u q.out‖)
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)

theorem lintegral_slice_le {A B : HSp D} (mH : Measure (GA D B)) {K : GA D A → GA D B → ℂ}
    (hl : ∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) (hL2 : ∀ g, MemL2Quotient (GQ B) mH (K g))
    (hP : GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (K g) (K g)) :
    ∃ (c : ℝ) (a : ℕ), 0 ≤ c ∧ ∀ g, ∫⁻ y, ‖K g y.out‖ₑ ^ 2 ∂autMeasure B mH ≤
      ENNReal.ofReal (c * GlobalTheory.Grow.quotHeight A g ^ a) := by
  obtain ⟨C, a, hC⟩ := hP
  have hinv : ∀ γ ∈ GQ A, ∀ g, petersson B mH (K (γ * g)) (K (γ * g)) = petersson B mH (K g) (K g) :=
    fun γ hγ g => by rw [show K (γ * g) = K g from funext (hl γ hγ g)]
  refine ⟨C * 2 ^ a, a, mul_nonneg (GlobalTheory.Grow.nonneg_of_growth hC) (by positivity), fun g => ?_⟩
  have hb := GlobalTheory.Grow.norm_le_quotHeight_pow hinv hC g
  have hf := (hL2 g).2
  have hf2 : Integrable (fun y : AutQ B => ‖K g y.out‖ ^ 2) (autMeasure B mH) :=
    (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have e1 : ∫⁻ y, ‖K g y.out‖ₑ ^ 2 ∂autMeasure B mH = ENNReal.ofReal (∫ y, ‖K g y.out‖ ^ 2 ∂autMeasure B mH) := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2 (ae_of_all _ fun _ => by positivity)]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have e2 : petersson B mH (K g) (K g) = ((∫ y, ‖K g y.out‖ ^ 2 ∂autMeasure B mH : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    show ∫ y, descend (GQ B) (K g) y * conj (descend (GQ B) (K g) y) ∂autMeasure B mH = _
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show K g y.out * conj (K g y.out) = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e3 : ‖petersson B mH (K g) (K g)‖ = ∫ y, ‖K g y.out‖ ^ 2 ∂autMeasure B mH := by
    rw [e2, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => by positivity)]
  rw [e1]
  exact ENNReal.ofReal_le_ofReal (e3 ▸ hb)

theorem weight_data {A : HSp D} (m : Measure (GA D A)) (hm : m.IsHaarMeasure) {u : GA D A → ℂ}
    (hu : GlobalTheory.Grow.RapidDec A u) {c : ℝ} (hc : 0 ≤ c) (a : ℕ) :
    (∀ q : AutQ A, ENNReal.ofReal (c * GlobalTheory.Grow.quotHeight A q.out ^ a) ≤
      ENNReal.ofReal (1 + c * GlobalTheory.Grow.quotHeight A q.out ^ a) ^ 2) ∧
    ∫⁻ q, ENNReal.ofReal (1 + c * GlobalTheory.Grow.quotHeight A q.out ^ a) * ‖u q.out‖ₑ ∂autMeasure A m ≠ ⊤ := by
  have ht : ∀ q : AutQ A, 0 ≤ c * GlobalTheory.Grow.quotHeight A q.out ^ a :=
    fun q => mul_nonneg hc (pow_nonneg (GlobalTheory.Grow.quotHeight_pos A _).le _)
  refine ⟨fun q => ?_, ?_⟩
  · rw [← ENNReal.ofReal_pow (by linarith [ht q])]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [ht q])
  · have hint : Integrable (fun q : AutQ A => (1 + c * GlobalTheory.Grow.quotHeight A q.out ^ a) * ‖u q.out‖)
        (autMeasure A m) := by
      refine ((GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D A m hm u hu 0).add ((GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D A m hm u hu a).const_mul c)).congr
        (ae_of_all _ fun q => ?_)
      simp only [Pi.add_apply, pow_zero, one_mul]
      ring
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hint.lintegral_lt_top)
    refine lintegral_congr fun q => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by linarith [ht q])]

theorem seesaw_fubini : ∀ (D : D7) (A B : HSp D) (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ K₁ K₂ : GA D A → GA D B → ℂ, (∀ K ∈ ({K₁, K₂} : Set (GA D A → GA D B → ℂ)), Continuous (Function.uncurry K) ∧ (∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) ∧ (∀ g, MemL2Quotient (GQ B) mH (K g)) ∧ (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (K g) (K g)) ∧ ∀ h, GlobalTheory.Grow.ModGrowth A fun g => K g h) → ∀ u₁ u₂ : GA D A → ℂ, GlobalTheory.Grow.RapidDec A u₁ → GlobalTheory.Grow.RapidDec A u₂ → let θ₁ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₁ g h * u₁ g) q ∂autMeasure A m; let θ₂ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₂ g h * u₂ g) q ∂autMeasure A m; (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₁ g h * u₁ g) (autMeasure A m)) ∧ (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₂ g h * u₂ g) (autMeasure A m)) ∧ MemL2Quotient (GQ B) mH θ₁ ∧ MemL2Quotient (GQ B) mH θ₂ ∧ petersson B mH θ₁ θ₂ = ∫ q : AutQ A × AutQ A, petersson B mH (K₁ q.1.out) (K₂ q.2.out) * u₁ q.1.out * conj (u₂ q.2.out) ∂(autMeasure A m).prod (autMeasure A m) := by
  intro D A B m mH hm hmH K₁ K₂ hK u₁ u₂ hu₁ hu₂ θ₁ θ₂
  obtain ⟨hc₁, hl₁, hL₁, hP₁, hg₁⟩ := hK K₁ (Set.mem_insert _ _)
  obtain ⟨hc₂, hl₂, hL₂, hP₂, hg₂⟩ := hK K₂ (Set.mem_insert_of_mem _ rfl)
  have hi₁ := integrable_lift_integrand m hm hc₁ hl₁ hg₁ hu₁
  have hi₂ := integrable_lift_integrand m hm hc₂ hl₂ hg₂ hu₂
  have hr₁ : ∀ g, ∀ γ ∈ GQ B, ∀ h, K₁ g (γ * h) = K₁ g h := fun g => (hL₁ g).1
  have hr₂ : ∀ g, ∀ γ ∈ GQ B, ∀ h, K₂ g (γ * h) = K₂ g h := fun g => (hL₂ g).1
  obtain ⟨c₁, a₁, hc₁0, hs₁⟩ := lintegral_slice_le mH hl₁ hL₁ hP₁
  obtain ⟨c₂, a₂, hc₂0, hs₂⟩ := lintegral_slice_le mH hl₂ hL₂ hP₂
  obtain ⟨hw₁, hf₁⟩ := weight_data m hm hu₁ hc₁0 a₁
  obtain ⟨hw₂, hf₂⟩ := weight_data m hm hu₂ hc₂0 a₂
  have := hm
  have := hmH
  have key := GlobalTheory.T.integral_kernel_lifts_fubini_sigmaFinite (autMeasure A m) (autMeasure A m) (autMeasure B mH)
    (fun q y => K₁ q.out y.out) (fun q y => K₂ q.out y.out) (fun q => u₁ q.out) (fun q => u₂ q.out)
    (measurable_kernel_out hc₁ hl₁ hr₁) (measurable_kernel_out hc₂ hl₂ hr₂)
    (measurable_out hu₁.1 hu₁.2.1) (measurable_out hu₂.1 hu₂.2.1) _ _
    (fun q => (hs₁ q.out).trans (hw₁ q)) (fun q => (hs₂ q.out).trans (hw₂ q)) hf₁ hf₂
    (fun y => hi₁ y.out) (fun y => hi₂ y.out)
  have inv₁ : ∀ γ ∈ GQ B, ∀ h, θ₁ (γ * h) = θ₁ h := fun γ hγ h => by
    have e : (fun g => K₁ g (γ * h) * u₁ g) = fun g => K₁ g h * u₁ g := funext fun g => by rw [hr₁ g γ hγ h]
    show ∫ q, descend (GQ A) (fun g => K₁ g (γ * h) * u₁ g) q ∂autMeasure A m = _
    rw [e]
  have inv₂ : ∀ γ ∈ GQ B, ∀ h, θ₂ (γ * h) = θ₂ h := fun γ hγ h => by
    have e : (fun g => K₂ g (γ * h) * u₂ g) = fun g => K₂ g h * u₂ g := funext fun g => by rw [hr₂ g γ hγ h]
    show ∫ q, descend (GQ A) (fun g => K₂ g (γ * h) * u₂ g) q ∂autMeasure A m = _
    rw [e]
  exact ⟨hi₁, hi₂, ⟨inv₁, key.1⟩, ⟨inv₂, key.2.1⟩, key.2.2⟩

end GlobalTheory.Core.Rk.Seesaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralUnramifiedPlacesUnionEqLocalFactors
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.EulStep

theorem isOpen_openOff {D : D7} (A : HSp D) (L : Lat A) (hL : IsSelfDualC A L) (S : Finset (FinPl D)) :
    IsOpen (openOff A L S) := by
  have := hL.1
  let U : Subgroup (GA D A) :=
    ⨅ k, ⨅ (_ : k ∉ S), (stabLoc D.sp.cm.sig A.gram L k).comap (proj D.sp.cm.sig A.gram k)
  have hU : ∀ g, g ∈ U ↔ g ∈ openOff A L S := fun g => by simp [U, Subgroup.mem_iInf, openOff]
  have hUo : IsOpen (U : Set (GA D A)) :=
    Subgroup.isOpen_mono (H₁ := ⨅ k, (stabLoc D.sp.cm.sig A.gram L k).comap (proj D.sp.cm.sig A.gram k))
      (fun g hg => (hU g).2 fun k _ => Subgroup.mem_iInf.1 hg k)
      (by
        convert (isRestrGroup_GAd D.sp.cm.sig A.gram L).isOpen_all using 1
        ext g
        simp [Subgroup.mem_iInf])
  convert hUo using 1
  exact Set.ext fun g => (hU g).symm

theorem sphFun_of_param {D : D7} {V : HSp D} {Λ : Lat V} {Sf : Finset (FinPl D)} {f : GA D V → ℂ}
    {B : GlobalTheory.LFun.Fam D.host.E} (hf : GlobalTheory.LFun.IsParamFun D.sp.cm.sig V.gram Λ (Sf : Set (FinPl D)) f B) :
    SphFun V Λ Sf f := by
  intro v hv k hk g
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hx := (hf v (by simpa using hv) w hw).mem_fixed
  have := congrFun (hx ⟨k, hk⟩) g
  simpa [GlobalTheory.PRep.rightReg, LinearMap.funLeft] using this

theorem setIntegral_openOff_union : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SphFactor D → LocalZetaOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ → ∀ s : ℂ, (A.rank : ℝ) < s.re → Integrable (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s) m → ∀ S₁ S₂ : Finset (FinPl D), Sf ⊆ S₁ → Disjoint S₁ S₂ → ∀ S₃ : Finset (FinPl D), (∀ u, u ∈ S₃ ↔ u ∈ S₁ ∨ u ∈ S₂) → ∫ g in openOff A LA S₃, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m = (∏ v ∈ S₂, GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s) * ∫ g in openOff A LA S₁, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m := by
  intro hP D hSF hLZ ψ θ A B χA χB sA sB t cA a om ν 𝓕 hpair LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph
    s hs hint
  have : BorelSpace (GA D A) := ⟨rfl⟩
  have := hU.sdA.1
  have hsph₁ : SphFun A LA Sf u₁ := sphFun_of_param hpar
  have step : ∀ (S : Finset (FinPl D)) (v : FinPl D), Sf ⊆ S → v ∉ S → ∀ S' : Finset (FinPl D),
      (∀ u, u ∈ S' ↔ u = v ∨ u ∈ S) →
      ∫ g in openOff A LA S', integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m =
        GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s *
          ∫ g in openOff A LA S, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m := by
    intro S v hS hv S' hS'
    have hvf : v ∉ Sf := fun h => hv (hS h)
    rw [GlobalTheory.T.integral_unramifiedOutsideOpenSubset_insert_place D A LA hU.sdA m hm S v hv (haarLoc D.sp.cm.sig A.gram LA v) inferInstance
      (haarLoc_stabLoc D.sp.cm.sig A.gram LA v) S' hS' _ hint.integrableOn, ← integral_const_mul]
    refine setIntegral_congr_fun (isOpen_openOff A LA hU.sdA S).measurableSet fun x hx => ?_
    obtain ⟨φ, hφ, hfac⟩ := hSF ψ θ A B χA χB sA sB t cA a om ν 𝓕 hpair LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU v hvf s
    have hk : proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram LA v := hx v hv
    obtain ⟨x', hx'⟩ : ∃ x', x' = x * (emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x))⁻¹ := ⟨_, rfl⟩
    have hx1 : proj D.sp.cm.sig A.gram v x' = 1 := by
      rw [hx', map_mul, map_inv, proj_emb_self, mul_inv_cancel]
    have hxe : x = x' * emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x) := by
      rw [hx', inv_mul_cancel_right]
    have hc := GlobalTheory.T.petersson_coefficient_bounded_spherical_unramified hP D θ A cA LA hpair.setting.2.2.2.1 m hm Sf u₁ hu₁ u₂ hu₂ par hpar hsph v hvf x' hx1
    have hz := (hLZ A LA hU.sdA χB B.rank hpair.weil.hecT hpair.weil.resT v trivial
      (fun w hw => hU.unr w (by
        show ¬ (w.under (𝓞 D.host.F) ∈ (Sf : Set (FinPl D)))
        rw [hw]; simpa using hvf))
      (haarLoc D.sp.cm.sig A.gram LA v) inferInstance (haarLoc_stabLoc D.sp.cm.sig A.gram LA v) s hs φ hφ par _ hc).2
    have hφk : φ (ioAt A v (proj D.sp.cm.sig A.gram v x)) = 1 := by
      have := hφ.2.1 (ioAt A v (proj D.sp.cm.sig A.gram v x))
        ((ioH_mem_KFin (gram_hdbl A)).2 ⟨hk, one_mem _⟩) 1
      rw [one_mul, hφ.2.2] at this
      exact this
    have hr : rcoef m u₁ u₂ x = rcoef m u₁ u₂ x' := by
      have : rTr A x u₁ = rTr A x' u₁ := funext fun g => by
        simp only [rTr]
        conv_lhs => rw [hxe, ← mul_assoc]
        exact hsph₁ v hvf _ hk _
      simp only [rcoef, this]
    have hw := hfac x' hx1 (proj D.sp.cm.sig A.gram v x)
    rw [← hxe, hφk, mul_one] at hw
    simp only [← hx', integrand, hfac x' hx1, hw, hr, mul_assoc]
    rw [integral_const_mul, integral_const_mul, hz, map_one, mul_one]
    ring
  intro S₁ S₂ hS₁
  classical
  induction S₂ using Finset.induction_on with
  | empty =>
    intro _ S₃ h
    obtain rfl : S₃ = S₁ := Finset.ext fun u => by simpa using h u
    simp
  | insert v S₂ hv ih =>
    intro hd S₃ h
    rw [Finset.disjoint_insert_right] at hd
    rw [step (S₁ ∪ S₂) v (hS₁.trans Finset.subset_union_left) (by simp [hd.1, hv]) S₃
      (fun u => by rw [h u, Finset.mem_insert, Finset.mem_union]; tauto),
      ih hd.2 _ (fun u => Finset.mem_union), Finset.prod_insert hv, mul_assoc]

end GlobalTheory.Core.Rk.EulStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology

namespace GlobalTheory.Unf.MatCoef

theorem contDiff_of_partials {k : ℕ} (P : ((Fin k → ℝ) → ℂ) → Prop) (hc : ∀ F, P F → Continuous F)
    (hd : ∀ F, P F → ∀ i : Fin k, ∃ (m : ℕ) (a H : Fin m → (Fin k → ℝ) → ℂ), (∀ j, ContDiff ℝ ∞ (a j)) ∧
      (∀ j, P (H j)) ∧ ∀ t, HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (∑ j, a j t * H j t) 0) :
    ∀ F, P F → ContDiff ℝ ∞ F := by
  have key : ∀ n : ℕ, ∀ F, P F → ContDiff ℝ n F := by
    intro n
    induction n with
    | zero => intro F hF; exact contDiff_zero.2 (hc F hF)
    | succ n ih =>
      intro F hF
      choose m a H ha hH hD using hd F hF
      have hGc : ∀ i, Continuous fun t => ∑ j, a i j t * H i j t := fun i =>
        continuous_finset_sum _ fun j _ => ((ha i j).continuous).mul (hc _ (hH i j))
      have hfd := GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_partials k F (fun i t => ∑ j, a i j t * H i j t) hGc hD
      have hfe : fderiv ℝ F = fun t => ∑ i, (∑ j, a i j t * H i j t) •
          (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (1 : ℂ) := by
        funext t
        rw [(hfd t).fderiv]
        refine Finset.sum_congr rfl fun i _ => ?_
        ext x
        simp [mul_comm]
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_fderiv]
      refine ⟨fun t => (hfd t).differentiableAt, by simp, ?_⟩
      rw [hfe]
      refine ContDiff.sum fun i _ => ?_
      have hs : ContDiff ℝ n fun t => ∑ j, a i j t * H i j t :=
        ContDiff.sum fun j _ => ((ha i j).of_le (mod_cast le_top)).mul (ih _ (hH i j))
      exact hs.smul contDiff_const
  intro F hF
  exact contDiff_infty.2 fun n => key n F hF

end GlobalTheory.Unf.MatCoef

namespace GlobalTheory.Unf.MatCoef

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {S T : HSp D}

theorem form_sub {ℓ : (WO S T → ℂ) → ℂ} (hℓ : IsSobForm ψ θ S T ℓ) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) : ℓ (f - g) = ℓ f - ℓ g := by
  have e : f - g = f + (-1 : ℂ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, hℓ.add f _ hf (theta_smul (-1) hg), hℓ.smul (-1) g hg]
  ring

theorem symplOH_zero_left (u : WO S T) : symplOH S T 0 u = 0 := by
  have := symplOH_add_left (S := S) (T := T) 0 0 u
  rw [add_zero] at this
  linear_combination -this

theorem decomp (h : Chart θ σ) (a : WO S T) : (iotaW σ T S (piW θ T S a)).map (finPart D) = 0 ∧
    (a - iotaW σ T S (piW θ T S a)).map (infPart D) = 0 := by
  refine ⟨h.real_iota T S _, ?_⟩
  have hp : piW θ T S (a - iotaW σ T S (piW θ T S a)) = 0 := by rw [AddMonoidHom.map_sub, h.pi_iota, sub_self]
  ext i j
  exact ThetaCont.infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j

theorem theta_heisO_any (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (u : WO S T) : IsThetaFunO ψ S T (heisO ψ S T u f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨hr, hn⟩ := decomp h u
  have e : heisO ψ S T u f = heisO ψ S T (iotaW σ T S (piW θ T S u)) (heisO ψ S T (u - iotaW σ T S (piW θ T S u)) f) := by
    rw [heisO_heisO, (symplOH_fin_real hn hr).2, AddChar.map_zero_eq_one, one_smul, add_sub_cancel]
  rw [e]
  exact theta_heisO_real hθ hψ hr (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hn)

theorem continuous_form (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {ℓ : (WO S T → ℂ) → ℂ}
    (hℓ : IsSobForm ψ θ S T ℓ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous fun u => ℓ (heisO ψ S T u f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  haveI : IsTopologicalAddGroup (Formalism.L2.Theta.AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  haveI : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  haveI : ContinuousAdd (WO S T) := inferInstance
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  have hg : IsThetaFunO ψ S T (heisO ψ S T u₀ f) := theta_heisO_any hψ hθ hf u₀
  obtain ⟨U, hU, hl⟩ := hg.level
  obtain ⟨d, C, hC⟩ := hℓ.bound U hU
  have hgU : heisO ψ S T u₀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U := ⟨hg, hl⟩
  let r : WO S T → WO S T := fun a => iotaW σ T S (piW θ T S a)
  have hrc : Continuous r := (h.continuous_iota T S).comp (continuous_pi' hθ T S)
  have hr0 : r 0 = 0 := by simp [r]
  have hnc : Continuous fun a => a - r a := continuous_id.sub hrc
  have hev : ∀ᶠ a in 𝓝 (0 : WO S T), a - r a ∈ U :=
    hnc.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp [hr0]))
  have hform : ∀ a, a - r a ∈ U → ℓ (heisO ψ S T (u₀ + a) f) =
      ψ (-(symplOH S T a u₀)) * ℓ (heisO ψ S T (r a) (heisO ψ S T u₀ f)) := by
    intro a ha
    obtain ⟨hr, hn⟩ := decomp h a
    have e1 : heisO ψ S T (r a) (heisO ψ S T u₀ f) = heisO ψ S T a (heisO ψ S T u₀ f) := by
      have e2 : heisO ψ S T (a - r a) (heisO ψ S T (r a) (heisO ψ S T u₀ f)) = heisO ψ S T (r a) (heisO ψ S T u₀ f) :=
        heisO_comm_fin_real hn hr (hl _ ha hn)
      rw [← e2, heisO_heisO, (symplOH_fin_real hn hr).1, AddChar.map_zero_eq_one, one_smul, sub_add_cancel]
    have e3 : heisO ψ S T a (heisO ψ S T u₀ f) = ψ (symplOH S T a u₀) • heisO ψ S T (u₀ + a) f := by
      rw [heisO_heisO, add_comm]
    rw [e1, e3, hℓ.smul _ _ (theta_heisO_any hψ hθ hf _), ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  have hphase : Filter.Tendsto (fun a => ψ (-(symplOH S T a u₀))) (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun a : WO S T => ψ (-(symplOH S T a u₀)) :=
      hψ.1.1.comp (continuous_symplOH continuous_id continuous_const).neg
    simpa only [symplOH_zero_left, neg_zero, AddChar.map_zero_eq_one] using hc.tendsto 0
  have hmain : Filter.Tendsto (fun a => ℓ (heisO ψ S T (r a) (heisO ψ S T u₀ f))) (𝓝 0)
      (𝓝 (ℓ (heisO ψ S T u₀ f))) := by
    have ht := ((GlobalTheory.T.heisenbergTranslate_theta_continuous_differentiable_sobolev D ψ hψ θ hθ S T d _ hg).1).comp (hrc.tendsto' 0 0 hr0)
    have ht2 : Filter.Tendsto (fun a => (C : ℝ≥0∞) * supSob ψ θ d (heisO ψ S T (r a) (heisO ψ S T u₀ f) - heisO ψ S T u₀ f))
        (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.coe_ne_top)
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht2 (fun _ => zero_le) fun a => ?_
    have hm : heisO ψ S T (r a) (heisO ψ S T u₀ f) ∈ GlobalTheory.Size.thetaLevel ψ S T U :=
      ⟨theta_heisO_real hθ hψ (h.real_iota T S _) hg, fun u hu h0 => heisO_comm_fin_real h0 (h.real_iota T S _) (hl u hu h0)⟩
    show edist _ _ ≤ _
    rw [edist_eq_enorm_sub, ← form_sub hℓ hm.1 hg]
    exact hC _ (sub_mem hm hgU)
  have hlim : Filter.Tendsto (fun a => ℓ (heisO ψ S T (u₀ + a) f)) (𝓝 0) (𝓝 (ℓ (heisO ψ S T u₀ f))) := by
    have := hphase.mul hmain
    rw [one_mul] at this
    exact this.congr' (hev.mono fun a ha => (hform a ha).symm)
  have hc2 : Filter.Tendsto (fun u => u - u₀) (𝓝 u₀) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 Filter.tendsto_id
  exact (hlim.comp hc2).congr fun u => by simp only [Function.comp_apply, add_sub_cancel]

theorem deriv_phase (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {M : ℝ →+ WO S T} (hM : Continuous M)
    (hMf : ∀ s, (M s).map (finPart D) = 0) (w : WO S T) :
    deriv (fun s : ℝ => ψ (symplOH S T w (M s))) 0 =
      -(Real.pi * Complex.I) * (omO S T (piW θ T S w) (piW θ T S (M 1)) : ℂ) := by
  have hlin : ∀ s : ℝ, piW θ T S (M s) = s • piW θ T S (M 1) := fun s => by
    have := map_real_smul ((piW θ T S).comp M) ((continuous_pi' h.inf T S).comp hM) s 1
    simpa using this
  have e : (fun s : ℝ => ψ (symplOH S T w (M s))) = fun s : ℝ =>
      Complex.exp (-(Real.pi * Complex.I) * ((s * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ)) := by
    funext s
    rw [← h.iota_pi (hMf s), psi_symplOH h hψ, hlin, LinearMap.map_smul, smul_eq_mul]
  rw [e]
  have hd : HasDerivAt (fun s : ℝ =>
      Complex.exp (-(Real.pi * Complex.I) * ((s * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ)))
      (Complex.exp (-(Real.pi * Complex.I) * (((0 : ℝ) * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ)) *
        (-(Real.pi * Complex.I) * ((1 * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ))) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).mul_const (omO S T (piW θ T S w) (piW θ T S (M 1)))).ofReal_comp).const_mul
      (-(Real.pi * Complex.I))).cexp
  rw [hd.deriv]
  simp

theorem contDiff_phase (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {k : ℕ} {L : (Fin k → ℝ) →+ WO S T}
    (hL : Continuous L) {M : ℝ →+ WO S T} (hM : Continuous M) (hMf : ∀ s, (M s).map (finPart D) = 0) (u : WO S T) :
    ContDiff ℝ ∞ fun t => -deriv (fun s : ℝ => ψ (symplOH S T (u + L t) (M s))) 0 := by
  let A : (Fin k → ℝ) →L[ℝ] RW T S := AddMonoidHom.toRealLinearMap ((piW θ T S).comp L) ((continuous_pi' h.inf T S).comp hL)
  let B : RW T S →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((omO S T).flip (piW θ T S (M 1)))
  have hB : ∀ t, B (A t) = omO S T (piW θ T S (L t)) (piW θ T S (M 1)) := fun t => rfl
  have e : (fun t => -deriv (fun s : ℝ => ψ (symplOH S T (u + L t) (M s))) 0) = fun t =>
      (Real.pi * Complex.I) * Complex.ofRealCLM (omO S T (piW θ T S u) (piW θ T S (M 1)) + B (A t)) := by
    funext t
    rw [deriv_phase h hψ hM hMf, hB, AddMonoidHom.map_add, LinearMap.map_add₂, Complex.ofRealCLM_apply]
    ring
  rw [e]
  have hc : ContDiff ℝ ∞ fun t => omO S T (piW θ T S u) (piW θ T S (M 1)) + B (A t) :=
    contDiff_const.add (B.contDiff.comp A.contDiff)
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hc)

end GlobalTheory.Unf.MatCoef

namespace GlobalTheory.Unf.MatCoef

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

theorem matCoef_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ), IsSobForm ψ θ S T ℓ → ∀ f, IsThetaFunO ψ S T f →
    Continuous (fun u => ℓ (heisO ψ S T u f)) ∧ ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L →
      (∀ t, (L t).map (finPart D) = 0) → ∀ u, ContDiff ℝ ∞ fun t => ℓ (heisO ψ S T (u + L t) f) := by
  intro D ψ hψ θ hθ S T ℓ hℓ f hf
  refine ⟨continuous_form hψ hθ hℓ hf, fun k L hL hLf u => ?_⟩
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let P : ((Fin k → ℝ) → ℂ) → Prop := fun F =>
    ∃ (u : WO S T) (f : WO S T → ℂ), IsThetaFunO ψ S T f ∧ F = fun t => ℓ (heisO ψ S T (u + L t) f)
  refine contDiff_of_partials P ?_ ?_ _ ⟨u, f, hf, rfl⟩
  · rintro _ ⟨u, f, hf, rfl⟩
    exact (continuous_form hψ hθ hℓ hf).comp (continuous_const.add hL)
  · rintro _ ⟨u, f, hf, rfl⟩ i
    let E : ℝ →ₗ[ℝ] (Fin k → ℝ) := LinearMap.toSpanSingleton ℝ (Fin k → ℝ) (Pi.single i 1)
    let M : ℝ →+ WO S T := L.comp E.toAddMonoidHom
    have hM : Continuous M := hL.comp E.continuous_of_finiteDimensional
    have hMf : ∀ s, (M s).map (finPart D) = 0 := fun s => hLf _
    have hf' : IsThetaFunO ψ S T (fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0) :=
      ((GlobalTheory.T.heisenbergTranslate_theta_continuous_differentiable_sobolev D ψ hψ θ hθ S T 0 f hf).2 M hM hMf).1
    refine ⟨2, ![fun _ => 1, fun t => -deriv (fun s : ℝ => ψ (symplOH S T (u + L t) (M s))) 0],
      ![fun t => ℓ (heisO ψ S T (u + L t) (fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0)),
        fun t => ℓ (heisO ψ S T (u + L t) f)], fun j => ?_, fun j => ?_, fun t => ?_⟩
    · fin_cases j
      · exact contDiff_const
      · exact contDiff_phase h hψ hL hM hMf u
    · fin_cases j
      · exact ⟨u, _, hf', rfl⟩
      · exact ⟨u, f, hf, rfl⟩
    · have e : (fun s : ℝ => ℓ (heisO ψ S T (u + L (t + s • Pi.single i 1)) f)) =
          fun s => ℓ (heisO ψ S T ((u + L t) + M s) f) := by
        funext s
        have : E s = s • Pi.single i 1 := rfl
        rw [map_add, add_assoc, ← this]
        rfl
      rw [e]
      convert GlobalTheory.T.hasDerivAt_sobolevThetaForm_heisenberg_along_real_line D ψ hψ θ hθ S T ℓ hℓ f hf M hM hMf (u + L t) using 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]
      ring

end GlobalTheory.Unf.MatCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepCharsUnramifiedOffSStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_step_chars_unramified_off_S : ∀ (D : D7) (c : Com D), c.Is → ∀ k < D.R.m, ∀ v ∉ c.S, ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt (c.chS (k + 1)) w ∧ UnrAt (c.chT (k + 1)) w := by
  first | exact @GlobalTheory.ChainOnto.step_chars_unrAt | exact GlobalTheory.ChainOnto.step_chars_unrAt | (intros; apply GlobalTheory.ChainOnto.step_chars_unrAt <;> assumption)
end

