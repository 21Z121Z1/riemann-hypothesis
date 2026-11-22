import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0669
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsClosedMatrixGroupImage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0292
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0391
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionBound
section
open scoped ENNReal NNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.BesselPt

theorem sq_tsum_le {ι : Type*} (t : ι → ℝ≥0) (k : ℕ) (h : (Function.support t).encard ≤ k) :
    (∑' i, (t i : ℝ≥0∞)) ^ 2 ≤ k * ∑' i, (t i : ℝ≥0∞) ^ 2 := by
  have hfin : (Function.support t).Finite := Set.finite_of_encard_le_coe h
  set S := hfin.toFinset with hS
  have hcard : S.card ≤ k := by
    have : (S.card : ℕ∞) ≤ k := by
      rw [← Set.encard_coe_eq_coe_finsetCard, hS, hfin.coe_toFinset]; exact h
    exact_mod_cast this
  have hz : ∀ i, i ∉ S → t i = 0 := fun i hi => by simpa [hS] using hi
  have e1 : ∑' i, (t i : ℝ≥0∞) = ∑ i ∈ S, (t i : ℝ≥0∞) :=
    tsum_eq_sum (fun i hi => by simp [hz i hi])
  have e2 : ∑' i, (t i : ℝ≥0∞) ^ 2 = ∑ i ∈ S, (t i : ℝ≥0∞) ^ 2 :=
    tsum_eq_sum (fun i hi => by simp [hz i hi])
  rw [e1, e2]
  have h3 : (∑ i ∈ S, t i) ^ 2 ≤ k * ∑ i ∈ S, t i ^ 2 := by
    have h4 : ((∑ i ∈ S, (t i : ℝ)) ^ 2) ≤ S.card * ∑ i ∈ S, (t i : ℝ) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h5 : (∑ i ∈ S, t i) ^ 2 ≤ S.card * ∑ i ∈ S, t i ^ 2 := by exact_mod_cast h4
    exact h5.trans (by gcongr)
  exact_mod_cast h3

theorem sq_lintegral_mul_le {X : Type*} [MeasurableSpace X] (ν : Measure X) {f g : X → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hg : AEMeasurable g ν) :
    (∫⁻ a, f a * g a ∂ν) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂ν) * ∫⁻ a, g a ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_ofNat] at h
  refine (pow_le_pow_left' h 2).trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ _), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  norm_num

theorem encard_support_le {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (α : G → ℂ) (x w : G)
    (k : ℕ)
    (hk : {γ : G | γ ∈ Γ ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k) :
    (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊).encard ≤ k := by
  rcases (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊).eq_empty_or_nonempty with h0 | ⟨γ₀, h₀⟩
  · simp [h0]
  refine le_trans ?_ hk
  have hinj : Set.InjOn (fun γ : Γ => (γ : G) * (γ₀ : G)⁻¹)
      (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊) := by
    intro a _ b _ hab
    exact Subtype.ext (mul_right_cancel hab)
  rw [← hinj.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨γ, hγ, rfl⟩
  have mem : ∀ c : Γ, c ∈ (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊) →
      x⁻¹ * ((c : G) * w) ∈ tsupport α := fun c hc => by
    apply subset_tsupport
    simpa [Function.mem_support] using hc
  refine ⟨Γ.mul_mem γ.2 (Γ.inv_mem γ₀.2), _, mem γ hγ, _, mem γ₀ h₀, ?_⟩
  group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem sq_lintegral_le (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) {α ψ : G → ℂ} (hα : Continuous α) (hψ : Continuous ψ)
    (hinv : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (hn : (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1) (x : G) (k : ℕ)
    (hk : {γ : G | γ ∈ Γ ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k) :
    (∫⁻ y, ‖α y‖ₑ * ‖ψ (x * y)‖ₑ ∂μ) ^ 2 ≤ k * ∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ := by
  set a : G → ℝ≥0∞ := fun w => ‖α (x⁻¹ * w)‖ₑ with ha
  have ham : Measurable a := (hα.comp (continuous_const.mul continuous_id)).enorm.measurable
  have hψm : Measurable fun w => ‖ψ w‖ₑ := hψ.enorm.measurable
  have htr : ∀ γ : Γ, Measurable fun w => a ((γ : G) * w) :=
    fun γ => ham.comp (measurable_const_mul _)
  have e1 : ∫⁻ y, ‖α y‖ₑ * ‖ψ (x * y)‖ₑ ∂μ = ∫⁻ w in F, (∑' γ : Γ, a ((γ : G) * w)) * ‖ψ w‖ₑ ∂μ := by
    have h1 := lintegral_mul_left_eq_self (μ := μ) (fun w => a w * ‖ψ w‖ₑ) x
    simp only [ha, inv_mul_cancel_left] at h1
    rw [h1, hF.lintegral_eq_tsum'', ← lintegral_tsum]
    · refine lintegral_congr fun w => ?_
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      rw [Subgroup.smul_def, smul_eq_mul, hinv _ γ.2]
    · intro γ
      simp only [Subgroup.smul_def, smul_eq_mul, hinv _ γ.2]
      exact ((htr γ).mul hψm).aemeasurable
  have e2 : ∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ = ∫⁻ w in F, ∑' γ : Γ, a ((γ : G) * w) ^ 2 ∂μ := by
    have h1 := lintegral_mul_left_eq_self (μ := μ) (fun w => a w ^ 2) x
    simp only [ha, inv_mul_cancel_left] at h1
    rw [h1, hF.lintegral_eq_tsum'', ← lintegral_tsum]
    · rfl
    · intro γ
      exact ((htr γ).pow_const 2).aemeasurable
  have hK : Measurable fun w => ∑' γ : Γ, a ((γ : G) * w) := Measurable.ennreal_tsum htr
  rw [e1, e2, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top k)]
  refine (sq_lintegral_mul_le _ hK.aemeasurable hψm.aemeasurable).trans ?_
  rw [hn, mul_one]
  refine lintegral_mono fun w => ?_
  have := sq_tsum_le (fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊) k (encard_support_le Γ α x w k hk)
  simpa [ha, enorm_eq_nnnorm] using this

theorem pointwise (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (Γ : Subgroup G) [Countable Γ]
    {α : G → ℂ} {δ : ℝ} {F : Set G} (hα : Continuous α) (hc : HasCompactSupport α) (hδ : 0 < δ)
    (hF : IsFundamentalDomain Γ F μ) : ∃ C₀ : ℝ, ∀ ψ : G → ℂ, Continuous ψ → (∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) →
      (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
      ∀ (x : G) (k : ℕ), {γ : G | γ ∈ Γ ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
        ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  refine ⟨(δ ^ 2)⁻¹ * (∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ).toReal, ?_⟩
  rintro ψ hψ hinv ⟨s, hs, hrep⟩ hn x k hk
  have hA : (∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ) ≠ ⊤ := by
    have hc2 : HasCompactSupport ((fun z : ℂ => ‖z‖ ^ 2) ∘ α) :=
      HasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) hc (by simp)
    have hi : Integrable ((fun z : ℂ => ‖z‖ ^ 2) ∘ α) μ :=
      Continuous.integrable_of_hasCompactSupport ((continuous_norm.pow 2).comp hα) hc2
    have := hi.2.ne
    simpa [HasFiniteIntegral, enorm_pow] using this
  have h1 : ‖s‖ₑ * ‖ψ x‖ₑ ≤ ∫⁻ y, ‖α y‖ₑ * ‖ψ (x * y)‖ₑ ∂μ := by
    rw [← enorm_mul, ← hrep x]
    exact (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp only [enorm_mul]))
  have h3 : (‖s‖ₑ * ‖ψ x‖ₑ) ^ 2 ≤ k * ∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ :=
    (pow_le_pow_left' h1 2).trans (sq_lintegral_le μ _ hF hα hψ hinv hn x k hk)
  have h4 : (‖s‖ * ‖ψ x‖) ^ 2 ≤ k * (∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) hA) h3
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm] using this
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h5 : δ ^ 2 * ‖ψ x‖ ^ 2 ≤ (‖s‖ * ‖ψ x‖) ^ 2 := by
    rw [mul_pow]
    gcongr
  have h6 := h5.trans h4
  rw [mul_assoc, inv_mul_eq_div, le_div_iff₀ hδ2]
  nlinarith [h6]

end GlobalTheory.CompanionTheory.Conc.BesselPt

open GlobalTheory.CompanionTheory.Conc.BesselPt in

theorem GlobalTheory.CompanionTheory.Conc.besselPt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∃ C₀ : ℝ, ∀ ψ : GA E N → ℂ, Continuous ψ → (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) →
  (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
  ∀ (x : GA E N) (k : ℕ), {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
    ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  intro E _ _ _ N _ _ μ _ α δ F hα hc hδ hF
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  exact pointwise μ (latticeGL E N) hα hc hδ hF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KilledByPolynomialSmoothing
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc.SmKill

theorem ctn_sm {K : Type} [Field K] [NumberField K] {n : ℕ} [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {β : archGroup K n → ℝ}
    (hβ : Continuous β) (hβc : HasCompactSupport β) {f : AdelicGLn.AdelicGL K n → ℂ} (hf : Continuous f)
    (r : ℕ) (g : AdelicGLn.AdelicGL K n) :
    Integrable (fun y => (β y : ℂ) * An.ctn r f (g * infEmb K n y)) ν ∧
      An.ctn r (sm ν β f) g = ∫ y, (β y : ℂ) * An.ctn r f (g * infEmb K n y) ∂ν := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ (φ : AdelicGLn.AdelicGL K n → ℂ) (h : AdelicGLn.AdelicGL K n),
      An.ctn r φ h = c * constantTerm r φ h := ⟨_, fun _ _ => rfl⟩
  set F : (UPos n r → AdeleRing (𝓞 K) K) × archGroup K n → ℂ :=
    fun p => c * ((β p.2 : ℂ) * f (unipGL p.1 * g * infEmb K n p.2)) with hF
  have hFc : Continuous F :=
    continuous_const.mul ((Complex.continuous_ofReal.comp (hβ.comp continuous_snd)).mul
      (hf.comp ((continuous_unipGL.comp continuous_fst).mul continuous_const |>.mul
        (continuous_infEmb.comp continuous_snd))))
  have hint : Integrable F ((unipMeasure K n r).restrict (unipFundamentalDomain K n r) |>.prod ν) := by
    have e : ((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod ν =
        ((unipMeasure K n r).prod ν).restrict (unipFundamentalDomain K n r ×ˢ Set.univ) := by
      rw [← Measure.restrict_univ (μ := ν), Measure.prod_restrict, Measure.restrict_univ]
    rw [e]
    refine IntegrableOn.of_forall_sdiff_eq_zero
      (hFc.continuousOn.integrableOn_compact (hC.prod hβc.isCompact))
      (measurableSet_unipFundamentalDomain.prod MeasurableSet.univ) fun p hp => ?_
    have hy : p.2 ∉ tsupport β := fun hy => hp.2 ⟨hDC hp.1.1, hy⟩
    simp [hF, image_eq_zero_of_notMem_tsupport hy]
  have hval : ∀ y, ∫ X in unipFundamentalDomain K n r, F (X, y) ∂unipMeasure K n r =
      (β y : ℂ) * An.ctn r f (g * infEmb K n y) := fun y => by
    simp only [hF, hc, constantTerm, mul_assoc]
    rw [integral_const_mul, integral_const_mul]
    ring
  constructor
  · have := hint.swap.integral_prod_left
    refine this.congr (Eventually.of_forall fun y => ?_)
    exact hval y
  · have h := integral_integral_swap (f := fun X y => F (X, y)) hint
    simp only [hval] at h
    rw [← h]
    simp only [hc, constantTerm, sm, hF]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [integral_const_mul]

end GlobalTheory.CompanionTheory.Conc.SmKill

open GlobalTheory.CompanionTheory.Conc.SmKill in

theorem GlobalTheory.CompanionTheory.Conc.kill_sm : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ) (r : ℕ) (p : ℂ[X]), Ker ν β → 0 < r → r < n → Continuous f →
    An.Kill r f p → An.Kill r (sm ν β f) p := by
  intro K _ _ n _ _ ν _ β f r p hk _ _ hf hkill g
  have h1 : ∀ j ∈ Finset.range (p.natDegree + 1),
      p.coeff j * An.ctn r (sm ν β f) (An.aR K n r j * g) =
        ∫ y, p.coeff j * ((β y : ℂ) * An.ctn r f (An.aR K n r j * g * infEmb K n y)) ∂ν := fun j _ => by
    rw [(ctn_sm ν hk.cont hk.cpt hf r _).2, integral_const_mul]
  rw [Finset.sum_congr rfl h1, ← integral_finset_sum _ fun j _ =>
    ((ctn_sm ν hk.cont hk.cpt hf r _).1).const_mul _]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  have h2 := hkill (g * infEmb K n y)
  have h3 : ∑ j ∈ Finset.range (p.natDegree + 1),
      p.coeff j * ((β y : ℂ) * An.ctn r f (An.aR K n r j * g * infEmb K n y)) =
      (β y : ℂ) * ∑ j ∈ Finset.range (p.natDegree + 1),
        p.coeff j * An.ctn r f (An.aR K n r j * (g * infEmb K n y)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (An.aR K n r j)]
    ring
  simp only [Pi.zero_apply]
  rw [h3, h2, mul_zero]

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingMemLeviStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_mem_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : Levi k (fun a => Fin (d a))), leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd) := by
  first | exact @GlobalTheory.CompanionTheory.LeviBlockIdx.leviEmb_mem_levi_blockIdx | exact GlobalTheory.CompanionTheory.LeviBlockIdx.leviEmb_mem_levi_blockIdx | (intros; apply GlobalTheory.CompanionTheory.LeviBlockIdx.leviEmb_mem_levi_blockIdx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRestrictionSmoothStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_restriction_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (F : GA E (r + s) → ℂ), F ∈ Sm E (r + s) → (fun m : GA E r => F (lev (Ad E) r s (m, 1))) ∈ Sm E r := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice | exact GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraOfExpLocal
section
open Matrix Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.LinRedLie

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}

def unitsOf (hG : GlobalTheory.LinRed.IsLinRed G) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) ℂ) ∈ G}
  one_mem' := hG.one_mem
  mul_mem' := fun {a b} ha hb => hG.mul_mem _ ha _ hb
  inv_mem' := fun {u} hu => by
    have h := hG.inv_mem _ hu
    rw [← Matrix.coe_units_inv] at h
    exact h

theorem isClosed_unitsOf (hG : GlobalTheory.LinRed.IsLinRed G) :
    IsClosed (unitsOf hG : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
  refine isClosed_of_closure_subset fun u hu => ?_
  refine hG.closed _ u.isUnit ?_
  exact closure_mono (fun v hv => hv) (map_mem_closure Units.continuous_val hu (fun v hv => hv))

open scoped Matrix.Norms.L2Operator in

theorem exists_subspace (hG : GlobalTheory.LinRed.IsLinRed G) :
    ∃ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ 𝔤, NormedSpace.exp X ∈ G) ∧
      ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ (0 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧
        ∀ X ∈ U, NormedSpace.exp X ∈ G → X ∈ 𝔤 := by
  obtain ⟨𝔤, h⟩ := GlobalTheory.CompanionTheory.ClosedSubgroupUnits.exists_isExpLieAlgebra (unitsOf hG) (isClosed_unitsOf hG)
  obtain ⟨U, hUo, h0, -, hU⟩ := h.exists_nhds
  exact ⟨𝔤, fun X hX => h.expUnit_mem X hX, U, hUo, h0, fun X hXU hX => hU X hXU hX⟩

theorem exists_lieAlgebra : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    ∃ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
      (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) ∧
      ∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤 := by
  intro n G hG
  obtain ⟨𝔤, hexp, U, hUo, h0, hU⟩ := exists_subspace hG
  refine ⟨𝔤, fun X => ⟨fun hX t => hexp _ (𝔤.smul_mem t hX), fun hX => ?_⟩,
    U, hUo.mem_nhds h0, hU⟩
  have hc : Continuous fun t : ℝ => t • X := continuous_id.smul continuous_const
  have hev : ∀ᶠ t : ℝ in 𝓝 0, t • X ∈ U :=
    hc.continuousAt.eventually_mem (by simpa using hUo.mem_nhds h0)
  obtain ⟨t, htU, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin :
    ∀ᶠ t : ℝ in 𝓝[≠] 0, t • X ∈ U ∧ t ∈ ({0}ᶜ : Set ℝ)).exists
  exact (𝔤.smul_mem_iff ht).1 (hU _ htU (hX t))

end GlobalTheory.CompanionTheory.LinRedLie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearRecurrenceGrowthBound
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.LinRec

lemma eq_zero_of_natDegree_eq_zero {p : ℂ[X]} (hp : p.Monic) (hd : p.natDegree = 0)
    {u : ℕ → ℂ} (hu : aeval shift p u = 0) : u = 0 := by
  have hp1 : p = 1 := by
    have h1 : p.coeff 0 = 1 := by
      have h2 := hp.coeff_natDegree
      rwa [hd] at h2
    rw [eq_C_of_natDegree_eq_zero hd, h1, C_1]
  subst hp1
  simpa using hu

theorem uniform_aeval (D : ℕ) (κ' κ : ℝ) (hκ : κ' < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ[X], p.Monic → p.natDegree ≤ D →
      (∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp κ') → ∀ (u : ℕ → ℂ) (M : ℝ), aeval shift p u = 0 →
      (∀ j < p.natDegree, ‖u j‖ ≤ M) → 0 ≤ M →
      ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  have hδ : 0 < Real.exp κ - Real.exp κ' := sub_pos.2 (Real.exp_lt_exp.2 hκ)
  induction D with
  | zero =>
    refine ⟨0, le_rfl, fun p hp hd _ u M hu _ _ i => ?_⟩
    have hu0 := eq_zero_of_natDegree_eq_zero hp (Nat.le_zero.1 hd) hu
    simp [hu0]
  | succ D ih =>
    obtain ⟨C', hC', hB⟩ := ih
    have hE' : 0 < Real.exp κ' := Real.exp_pos _
    have hc : 0 ≤ C' * (1 + Real.exp κ') := by positivity
    have hC0 : 0 ≤ 1 + C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ') := by positivity
    refine ⟨_, hC0, fun p hp hd hr u M hu hM hM0 i => ?_⟩
    by_cases hd0 : p.natDegree = 0
    · have hu0 := eq_zero_of_natDegree_eq_zero hp hd0 hu
      have : 0 ≤ (1 + C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ')) *
          Real.exp (κ * i) * M := by positivity
      simpa [hu0] using this
    obtain ⟨z, hz⟩ : ∃ z, p.IsRoot z := IsAlgClosed.exists_root p (by
      intro h0
      exact hd0 (natDegree_eq_zero_iff_degree_le_zero.2 h0.le))
    have hzle := hr z hz
    have hzlt : ‖z‖ < Real.exp κ := hzle.trans_lt (Real.exp_lt_exp.2 hκ)
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.2 hz
    have hq : q.Monic := (monic_X_sub_C z).of_mul_monic_left hp
    have hqd : ((X - C z) * q).natDegree = q.natDegree + 1 := by
      rw [(monic_X_sub_C z).natDegree_mul hq, natDegree_X_sub_C]
      omega
    have hv : ∀ i : ℕ, ‖u (i + 1) - z * u i‖ ≤
        C' * (1 + Real.exp κ') * Real.exp (κ * i) * M := by
      intro i
      have hb := hB q hq (by omega)
        (fun w hw => hr w (by
          have hw' : eval w q = 0 := hw
          simp [IsRoot, hw']))
        (fun i => u (i + 1) - z * u i) ((1 + Real.exp κ') * M) (aeval_diff q z u hu)
        (fun j hj => ?_) (by positivity) i
      · calc ‖u (i + 1) - z * u i‖ ≤ C' * Real.exp (κ * i) * ((1 + Real.exp κ') * M) := hb
          _ = _ := by ring
      · calc ‖u (j + 1) - z * u j‖ ≤ ‖u (j + 1)‖ + ‖z * u j‖ := norm_sub_le _ _
          _ = ‖u (j + 1)‖ + ‖z‖ * ‖u j‖ := by rw [norm_mul]
          _ ≤ M + Real.exp κ' * M := add_le_add (hM _ (by omega))
              (mul_le_mul hzle (hM _ (by omega)) (norm_nonneg _) hE'.le)
          _ = _ := by ring
    have hg := geom_step z κ _ M hzlt hc hM0 u (hM 0 (by omega)) hv i
    refine hg.trans ?_
    have hdiv : C' * (1 + Real.exp κ') / (Real.exp κ - ‖z‖) ≤
        C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ') :=
      div_le_div_of_nonneg_left hc hδ (by linarith)
    have hEM : 0 ≤ Real.exp (κ * i) * M := by positivity
    calc _ = (1 + C' * (1 + Real.exp κ') / (Real.exp κ - ‖z‖)) * (Real.exp (κ * i) * M) := by ring
      _ ≤ (1 + C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ')) * (Real.exp (κ * i) * M) :=
        mul_le_mul_of_nonneg_right (by linarith) hEM
      _ = _ := by ring

theorem uniformRecBound :
    ∀ (D : ℕ) (κ' κ : ℝ), κ' < κ → ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ[X], p.Monic → p.natDegree ≤ D →
  (∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp κ') → ∀ (u : ℕ → ℂ) (M : ℝ),
  (∀ i, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * u (i + j) = 0) → (∀ j < p.natDegree, ‖u j‖ ≤ M) → 0 ≤ M →
  ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  intro D κ' κ hκ
  obtain ⟨C, hC, h⟩ := uniform_aeval D κ' κ hκ
  refine ⟨C, hC, fun p hp hd hr u M hu hM hM0 i => h p hp hd hr u M ?_ hM hM0 i⟩
  funext i
  rw [aeval_shift]
  exact hu i

end GlobalTheory.CompanionTheory.LinRec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissibleStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_of_irreducible_admissible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k := by
  first | exact @GlobalTheory.CompanionTheory.GKLocalProof.gkLocal | exact GlobalTheory.CompanionTheory.GKLocalProof.gkLocal | (intros; apply GlobalTheory.CompanionTheory.GKLocalProof.gkLocal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpCoefficientCenterNormPreservedStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lp_coefficient_center_norm_preserved : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (p : ℝ), CoeffLp p π → ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ (v : V) (l : Module.Dual ℂ V), IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} → ‖l (π z v)‖ = ‖l v‖ := by
  first | exact @GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central | exact GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central | (intros; apply GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientCartanTranslateStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_cartan_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (m : ℕ) (v : V), v ∈ fixed π (Zls.Km k N m) → ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → (π p2 v ∈ fixed π (Zls.Km k N m)) ∧ (∀ x ∈ Zls.Km k N m, (l ∘ₗ π p1) ∘ₗ π x = l ∘ₗ π p1) ∧ ∀ (D : GL (Fin N) k), ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m, l (π (p1 * x * D * y * p2) v) = (l ∘ₗ π p1) (π D (π p2 v)) := by
  first | exact @GlobalTheory.CompanionTheory.CongruenceCoef.coef_const_translated_double_coset | exact GlobalTheory.CompanionTheory.CongruenceCoef.coef_const_translated_double_coset | (intros; apply GlobalTheory.CompanionTheory.CongruenceCoef.coef_const_translated_double_coset <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEq
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem mirChar_eq_thetaA_single (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : GlobalTheory.BZMir.Fun.MirCharEq k := by
  intro ψ n
  have h : chrV k ψ n = chrA k ψ (Pi.single (Fin.last n) 1) := by
    ext v
    simp [chrV, chrA]
  rw [mirChar, thetaA, h]

end GlobalTheory.CompanionTheory.BZMir
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicRestrictionUnipotentSmooth
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat_toAdd (n : ℕ) :
    Continuous fun x : Multiplicative (Fin n → k) => colMat k n x.toAdd := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases with
    | last => simpa [colMat] using continuous_const
    | cast i =>
      have h : Continuous fun a : Multiplicative (Fin n → k) => Multiplicative.toAdd a i :=
        (continuous_apply i).comp continuous_toAdd
      simpa [colMat] using h
  · simpa [colMat, hj] using continuous_const

theorem continuous_unipMir (n : ℕ) : Continuous (unipMir k n) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat_toAdd n)
  · have h : Continuous fun x : Multiplicative (Fin n → k) => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) - colMat k n x.toAdd :=
      continuous_const.sub (continuous_colMat_toAdd n)
    exact h

theorem isSmooth_comp_unipMir : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), IsSmooth τ → IsSmooth (τ.comp (unipMir k n)) := by
  intro k _ _ _ _ n V _ _ τ h w
  exact (h w).preimage (continuous_unipMir n)

end GlobalTheory.CompanionTheory.MirFourier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZeroStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), twKer τ (MirUin k n) 1 = twKer τ (derUnipM k n n) (derCharM k ψ n n) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM | exact GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM | (intros; apply GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM <;> assumption)
end

