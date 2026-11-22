import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqSetIntegralTsumRationalTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.Periodize

theorem integral_eq_setIntegral_tsum (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (ratMx D m n) 𝓕 μ) (c : Mx D m n → ℂ)
    (hc : Integrable c μ) :
    (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun a : Matrix (Fin m) (Fin n) D.host.E => ‖c (y + a.map (incA D))‖) ∧
      ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' a : Matrix (Fin m) (Fin n) D.host.E, c (y + a.map (incA D)) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D m n) := i5
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  let e : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n :=
    Equiv.ofBijective (fun a => ⟨a.map (incA D), a, rfl⟩)
      ⟨fun a b h => Matrix.map_injective GlobalTheory.MixModel.incA_injective (congrArg Subtype.val h),
        fun γ => by obtain ⟨a, ha⟩ := γ.2; exact ⟨a, Subtype.ext ha⟩⟩
  have he : ∀ a, ((e a : ratMx D m n) : Mx D m n) = a.map (incA D) := fun _ => rfl

  have hm : ∀ γ : ratMx D m n, AEStronglyMeasurable (fun y => c (y + γ)) (μ.restrict 𝓕) := by
    intro γ
    have := hc.1.comp_quasiMeasurePreserving (measurePreserving_add_right μ (γ : Mx D m n)).quasiMeasurePreserving
    exact this.restrict

  have hl : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ = ∫⁻ y, ‖c y‖ₑ ∂μ := by
    rw [hF.lintegral_eq_tsum'' (fun y => ‖c y‖ₑ)]
    refine tsum_congr fun γ => ?_
    simp only [AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]
  have hfin : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤ := by
    rw [hl]; exact hc.2.ne

  have hae : ∀ᵐ y ∂(μ.restrict 𝓕), Summable fun γ : ratMx D m n => ‖c (y + γ)‖ := by
    have h1 : ∫⁻ y in 𝓕, ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun γ => (hm γ).enorm]; exact hfin
    have h2 : AEMeasurable (fun y => ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ) (μ.restrict 𝓕) :=
      AEMeasurable.ennreal_tsum fun γ => (hm γ).enorm
    filter_upwards [ae_lt_top' h2 h1] with y hy
    have : ∑' γ : ratMx D m n, (‖c (y + γ)‖₊ : ENNReal) ≠ ⊤ := by
      simpa only [enorm_eq_nnnorm] using hy.ne
    exact (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)).congr fun _ => rfl
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with y hy
    exact (e.summable_iff.2 hy).congr fun a => by rw [Function.comp_apply, he]
  · have h3 : ∫ y in 𝓕, ∑' γ : ratMx D m n, c (y + γ) ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ :=
      integral_tsum hm hfin
    have h4 : ∫ y, c y ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ := by
      rw [hF.integral_eq_tsum' c hc, ← (Equiv.neg (ratMx D m n)).tsum_eq]
      refine tsum_congr fun γ => ?_
      simp only [Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]
    rw [h4, ← h3]
    congr 1
    funext y
    rw [← e.tsum_eq]
    rfl

end GlobalTheory.Twist.Periodize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFiniteAdeleSupportedDivPrimeToPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem GlobalTheory.intAf_div_prime_to_place (D : D7) (v : GlobalTheory.FinPl.Pl D) (d : 𝓞 D.host.F) (hd : d ∉ v.asIdeal)
    (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (hsupp : ∀ w, ¬ w = v → evalV D.host.F w α = 0) :
    ∃ α' ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α' = 0) ∧
      α = α' * algebraMap D.host.F (Af D.host.F) (d : D.host.F) := by
  have hd0 : ((d : D.host.F)) ≠ 0 := by
    intro h
    apply hd
    have : d = 0 := by exact_mod_cast h
    rw [this]; exact v.asIdeal.zero_mem
  have hval : v.valuation D.host.F (d : D.host.F) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hd
  refine ⟨α * algebraMap D.host.F (Af D.host.F) (d : D.host.F)⁻¹, ?_, ?_, ?_⟩
  · intro w
    rw [map_mul, AlgHom.commutes]
    by_cases hw : w = v
    · subst hw
      refine (HeightOneSpectrum.adicCompletionIntegers D.host.F w).mul_mem _ _ (hα w) ?_
      have hv : Valued.v (algebraMap D.host.F (HeightOneSpectrum.adicCompletion D.host.F w) (d : D.host.F)⁻¹)
          = w.valuation D.host.F (d : D.host.F)⁻¹ :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      refine le_of_eq ?_
      refine hv.trans ?_
      rw [map_inv₀, hval, inv_one]
    · rw [hsupp w hw, zero_mul]
      exact (HeightOneSpectrum.adicCompletionIntegers D.host.F w).zero_mem
  · intro w hw
    rw [map_mul, hsupp w hw, zero_mul]
  · rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hd0, map_one, mul_one]

theorem GlobalTheory.intAf_div_prime_to_place' : ∀ (D : D7) (v : GlobalTheory.FinPl.Pl D) (d : 𝓞 D.host.F), d ∉ v.asIdeal → ∀ α ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) → ∃ α' ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α' = 0) ∧ α = α' * algebraMap D.host.F (Af D.host.F) (d : D.host.F) :=
  fun D v d hd α hα hs => GlobalTheory.intAf_div_prime_to_place D v d hd α hα hs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeftMulUnitaryMatrixAddHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.LeftHaar

def transposeCAE (D : D7) (m n : ℕ) : Mx D m n ≃ₜ+ Mx D n m where
  toAddEquiv := Matrix.transposeAddEquiv (Fin m) (Fin n) (AE D)
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

theorem map_left_unitary (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r))
    (hν : ν.IsAddHaarMeasure) :
    ν.map (fun y : Mx D W.rank r =>
      (HMul.hMul (mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)) = ν := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hJ : IsHermND D.sp.cm.sig W.gram := GlobalTheory.Mem.VolExists.isHermND D.sp.cm W
  obtain ⟨g', hg'⟩ := GlobalTheory.AdelicModulus.Row.exists_transpose (AF D.host.F) hJ h
  have hK := GlobalTheory.AdelicModulus.Row.isHermND_inv_transpose hJ
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D r W.rank) := ⟨rfl⟩
  let T := transposeCAE D W.rank r
  have hT : Measurable T := T.continuous.measurable
  have hTs : Measurable T.symm := T.symm.continuous.measurable
  haveI hμ' : (ν.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map ν
  have hm := GlobalTheory.mul_unitary_map_haar D W.rank r (W.gram⁻¹)ᵀ hK.1 hK.2 g' (ν.map T) hμ'
  set A : Matrix (Fin W.rank) (Fin W.rank) (AE D) := (HA.mat (AF D.host.F) D.sp.cm.sig (W.gram⁻¹)ᵀ g').1
  have hR : Measurable (fun x : Mx D r W.rank =>
      (HMul.hMul (x : Matrix (Fin r) (Fin W.rank) (AE D)) A : Mx D r W.rank)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hmt : mt W h = (HA.mat (AF D.host.F) D.sp.cm.sig W.gram h).1 := rfl
  have hf : (fun y : Mx D W.rank r =>
      (HMul.hMul (mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)) =
      T.symm ∘ (fun x : Mx D r W.rank => (HMul.hMul (x : Matrix (Fin r) (Fin W.rank) (AE D)) A : Mx D r W.rank)) ∘ T := by
    funext y
    simp only [Function.comp_apply, A, hg', hmt]
    show _ = ((y : Matrix (Fin W.rank) (Fin r) (AE D))ᵀ * ((HA.mat (AF D.host.F) D.sp.cm.sig W.gram h).1)ᵀ)ᵀ
    rw [← Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hf, ← Measure.map_map hTs (hR.comp hT), ← Measure.map_map hR hT, hm, Measure.map_map hTs hT]
  have : (T.symm ∘ T : Mx D W.rank r → Mx D W.rank r) = id := by
    funext y; simp
  rw [this, Measure.map_id]

theorem integral_left_unitary : ∀ (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r)),
    ν.IsAddHaarMeasure → ∀ Φ : Mx D W.rank r → ℂ,
    ∫ y, Φ (HMul.hMul (Formalism.L2.Theta.mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) ∂ν =
      ∫ y, Φ y ∂ν := by
  intro D W r h ν hν Φ
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.ae_facts D
  let u := HA.mat (AF D.host.F) D.sp.cm.sig W.gram h
  have hmt : mt W h = u.1 := rfl
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  let e : Mx D W.rank r ≃ᵐ Mx D W.rank r :=
    { toFun := fun y => (HMul.hMul u.1 (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)
      invFun := fun y => (HMul.hMul (u⁻¹).1 (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)
      left_inv := fun y => by
        show (u⁻¹).1 * (u.1 * y) = y
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun y => by
        show u.1 * ((u⁻¹).1 * y) = y
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      measurable_toFun := (continuous_const.matrix_mul continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mul continuous_id).measurable }
  have hmap := map_left_unitary D W r h ν hν
  rw [hmt] at hmap
  have he : Measure.map (⇑e) ν = ν := hmap
  have := integral_map_equiv (μ := ν) e Φ
  rw [he] at this
  rw [hmt]
  exact this.symm

end GlobalTheory.Twist.LeftHaar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralParametricUnfoldRationalTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnfoldRat

def ratEquiv (D : D7) (m n : ℕ) : Matrix (Fin m) (Fin n) D.host.E ≃ GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n :=
  Equiv.ofBijective (fun ξ => ⟨ξ.map (incA D), ξ, rfl⟩)
    ⟨fun _ _ h => GlobalTheory.MixModel.rat_injective (congrArg Subtype.val h), fun ⟨_, ξ, hξ⟩ => ⟨ξ, Subtype.ext hξ⟩⟩

theorem countable_ratMx (D : D7) (m n : ℕ) : Countable (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : DiscreteTopology (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) := i5
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

theorem countable_mat (D : D7) (m n : ℕ) : Countable (Matrix (Fin m) (Fin n) D.host.E) := by
  haveI := countable_ratMx D m n
  exact (ratEquiv D m n).injective.countable

theorem lintegral_unfold {D : D7} {m n : ℕ} {μ : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)}
    (hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨) (φ : Mx D m n → ℝ≥0∞) :
    ∫⁻ u, φ u ∂μ = ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ t in 𝓨, φ (ξ.map (incA D) + t) ∂μ := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := countable_ratMx D m n
  haveI := hcov.1
  rw [hcov.2.1.lintegral_eq_tsum'' φ, ← (ratEquiv D m n).tsum_eq]
  rfl

theorem integral_unfold {D : D7} {m n : ℕ} {μ : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)}
    (hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨) (φ : Mx D m n → ℂ) (hφ : Integrable φ μ) :
    ∫ u, φ u ∂μ = ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ t in 𝓨, φ (ξ.map (incA D) + t) ∂μ := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := countable_ratMx D m n
  haveI := hcov.1
  rw [hcov.2.1.integral_eq_tsum'' φ hφ, ← (ratEquiv D m n).tsum_eq]
  rfl

theorem unfold : ∀ (D : D7) (m n : ℕ) (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (ν : Measure X) [IsFiniteMeasure ν] (μ : Measure (Mx D m n)) (𝓨 : Set (Mx D m n)),
    IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨 → ∀ (h : X → Mx D m n → ℂ), Continuous (Function.uncurry h) →
    ∀ M : ℝ, (∀ x u, Summable (fun ξ : Matrix (Fin m) (Fin n) D.host.E => ‖h x (ξ.map (incA D) + u)‖) ∧
      ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤ M) →
    Integrable (fun u => ∫ x, h x u ∂ν) μ ∧ ∫ u, (∫ x, h x u ∂ν) ∂μ =
      ∫ t in 𝓨, (∫ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, h x (ξ.map (incA D) + t) ∂ν) ∂μ := by
  intro D m n X _ _ _ _ ν _ μ 𝓨 hcov h hc M hM
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := countable_mat D m n
  haveI := hcov.1
  haveI : FirstCountableTopology (Mx D m n) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hr0 : (0 : Matrix (Fin m) (Fin n) D.host.E).map (incA D) = 0 := Matrix.map_zero _ (map_zero (incA D))

  have hb : ∀ x u, ‖h x u‖ ≤ M := fun x u => by
    have h0 := (hM x u).1.le_tsum 0 (fun _ _ => norm_nonneg _)
    rw [hr0, zero_add] at h0
    exact h0.trans (hM x u).2
  have hcx : ∀ x, Continuous (h x) := fun x => hc.comp (continuous_const.prodMk continuous_id)
  have hcu : ∀ u, Continuous fun x => h x u := fun u => hc.comp (continuous_id.prodMk continuous_const)
  have hmeas : Measurable (Function.uncurry h) := hc.measurable

  have hmx : ∀ x (ξ : Matrix (Fin m) (Fin n) D.host.E), Measurable fun t => ‖h x (ξ.map (incA D) + t)‖ₑ :=
    fun x ξ => ((hcx x).comp (continuous_add_left _)).measurable.enorm
  have hmu : ∀ t (ξ : Matrix (Fin m) (Fin n) D.host.E), Measurable fun x => ‖h x (ξ.map (incA D) + t)‖ₑ :=
    fun t ξ => (hcu (ξ.map (incA D) + t)).measurable.enorm
  have hsum : ∀ x t, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + t)‖ₑ ≤ ENNReal.ofReal M := fun x t => by
    simp_rw [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hM x t).1]
    exact ENNReal.ofReal_le_ofReal (hM x t).2
  have hlx : ∀ x, ∫⁻ u, ‖h x u‖ₑ ∂μ ≤ ENNReal.ofReal M := fun x => by
    have e1 : ∫⁻ t in 𝓨, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + t)‖ₑ ∂μ =
        ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ t in 𝓨, ‖h x (ξ.map (incA D) + t)‖ₑ ∂μ :=
      lintegral_tsum fun ξ => (hmx x ξ).aemeasurable
    rw [lintegral_unfold hcov (fun u => ‖h x u‖ₑ), ← e1]
    refine (lintegral_mono fun t => hsum x t).trans ?_
    rw [setLIntegral_const, hcov.2.2, mul_one]

  have hGc : Continuous fun u => ∫ x, h x u ∂ν :=
    continuous_of_dominated (bound := fun _ => M) (fun u => (hcu u).aestronglyMeasurable)
      (fun u => Filter.Eventually.of_forall fun x => hb x u) (integrable_const M)
      (Filter.Eventually.of_forall fun x => hcx x)

  have hGi : Integrable (fun u => ∫ x, h x u ∂ν) μ := by
    refine ⟨hGc.aestronglyMeasurable, ?_⟩
    have h1 : ∫⁻ u, ‖∫ x, h x u ∂ν‖ₑ ∂μ ≤ ∫⁻ u, ∫⁻ x, ‖h x u‖ₑ ∂ν ∂μ :=
      lintegral_mono fun u => enorm_integral_le_lintegral_enorm _
    have h2 : ∫⁻ u, ∫⁻ x, ‖h x u‖ₑ ∂ν ∂μ = ∫⁻ x, ∫⁻ u, ‖h x u‖ₑ ∂μ ∂ν :=
      lintegral_lintegral_swap (hmeas.enorm.comp measurable_swap).aemeasurable
    have h3 : ∫⁻ x, ∫⁻ u, ‖h x u‖ₑ ∂μ ∂ν ≤ ENNReal.ofReal M * ν Set.univ := by
      rw [← lintegral_const]; exact lintegral_mono fun x => hlx x
    exact lt_of_le_of_lt (h1.trans (h2.le.trans h3)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  refine ⟨hGi, ?_⟩
  rw [integral_unfold hcov _ hGi]

  have hA : ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ t in 𝓨, ‖∫ x, h x (ξ.map (incA D) + t) ∂ν‖ₑ ∂μ ≠ ∞ := by
    rw [← lintegral_unfold hcov (fun u => ‖∫ x, h x u ∂ν‖ₑ)]; exact hGi.2.ne
  have e3 : ∫ t in 𝓨, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ x, h x (ξ.map (incA D) + t) ∂ν ∂μ =
      ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ t in 𝓨, ∫ x, h x (ξ.map (incA D) + t) ∂ν ∂μ :=
    integral_tsum (fun ξ => (hGc.comp (continuous_add_left (ξ.map (incA D)))).aestronglyMeasurable) hA
  rw [← e3]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)

  have hB : ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ x, ‖h x (ξ.map (incA D) + t)‖ₑ ∂ν ≠ ∞ := by
    have e2 : ∫⁻ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + t)‖ₑ ∂ν =
        ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ x, ‖h x (ξ.map (incA D) + t)‖ₑ ∂ν :=
      lintegral_tsum fun ξ => (hmu t ξ).aemeasurable
    rw [← e2]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x => hsum x t) ?_)
    rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have e4 : ∫ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, h x (ξ.map (incA D) + t) ∂ν =
      ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ x, h x (ξ.map (incA D) + t) ∂ν :=
    integral_tsum (fun (ξ : Matrix (Fin m) (Fin n) D.host.E) => (hcu (ξ.map (incA D) + t)).aestronglyMeasurable) hB
  exact e4.symm

end GlobalTheory.UnfoldRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfTendstoModerateGrowthSizeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFun_of_tendsto_moderateGrowthSize : ∀ (D : D7) (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ) (f : GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ (∀ γ ∈ GQ V, ∀ g, ψ n (γ * g) = ψ n g) ∧ IsCuspFun V (ψ n)) → Continuous f → (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → Filter.Tendsto (fun n => GlobalTheory.Size.growthSize V N (ψ n - f)) Filter.atTop (nhds 0) → IsCuspFun V f := by
  first | exact @GlobalTheory.CuspLimit.isCuspFun_of_tendsto | exact GlobalTheory.CuspLimit.isCuspFun_of_tendsto | (intros; apply GlobalTheory.CuspLimit.isCuspFun_of_tendsto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDiscreteSeriesConjugateReverseContragredientStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiscreteSeries_conjugate_reverse_contragredient : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mn n → (H →L[ℂ] H)), IsDS ε lam σ → IsDS (fun a => ε a.rev) (fun a => -lam a.rev) (fun g => σ ((g.map (starRingEnd ℂ)).submatrix Fin.rev Fin.rev)) := by
  first | exact @GlobalTheory.ArchRec.isDS_conj_rev | exact GlobalTheory.ArchRec.isDS_conj_rev | (intros; apply GlobalTheory.ArchRec.isDS_conj_rev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGaussEqZero
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

namespace GlobalTheory.VacDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def IsGaussEq (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (Φ : (Fin n × Fin d → AF F) → ℂ) : Prop :=
  ∃ ε : InfinitePlace F → ℤˣ, ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
    (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
    ∀ x, deriv (fun t : ℝ => M.heisLine ψ u' t Φ x) 0 = Complex.I * deriv (fun t : ℝ => M.heisLine ψ u t Φ x) 0

end GlobalTheory.VacDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualStandardFrameLineLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem isSelfDualC_span_of_norm {D : D7} (S : HSp D) (hS : S.rank = 1) (ζ : Fin S.rank → D.host.E)
    (hζ : star ζ ⬝ᵥ (HSpace.gram S *ᵥ ζ) = -1) :
    IsSelfDualC S (Submodule.span (𝓞 D.host.E) {ζ}) := by
  have hform : ∀ x y : Fin S.rank → D.host.E,
      ∑ i, ∑ j, star (x i) * HSpace.gram S i j * y j = star x ⬝ᵥ (HSpace.gram S *ᵥ y) := by
    intro x y
    simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  have hne : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  haveI : Subsingleton (Fin S.rank) := by rw [hS]; infer_instance
  obtain ⟨i₀, hi₀⟩ : ∃ i, ζ i ≠ 0 := Function.ne_iff.mp hne
  have hall : ∀ y : Fin S.rank → D.host.E, ∃ c : D.host.E, y = c • ζ := by
    intro y
    refine ⟨y i₀ / ζ i₀, funext fun i => ?_⟩
    rw [Subsingleton.elim i i₀, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hi₀]
  have hpair : ∀ a c : D.host.E, star (a • ζ) ⬝ᵥ (HSpace.gram S *ᵥ (c • ζ)) = -(star a * c) := by
    intro a c
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, hζ, smul_eq_mul, smul_eq_mul]
    ring
  have hstar : ∀ a : 𝓞 D.host.E, IsIntegral ℤ (star (a : D.host.E)) := fun a =>
    (map_isIntegral_int (starRingEnd D.host.E) a.2 : )
  refine ⟨⟨Submodule.fg_span_singleton _, ?_⟩, fun y => ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨c, rfl⟩ := hall y
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.mem_span_singleton_self _))
  · obtain ⟨c, rfl⟩ := hall y
    constructor
    · intro hy x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy
      rw [← hb, hform]
      refine ⟨-(⟨_, hstar a⟩ * b), ?_⟩
      have := hpair a b
      simp only [← algebraMap_smul D.host.E a, ← algebraMap_smul D.host.E b]
      rw [this]
      rfl
    · intro h
      obtain ⟨b, hb⟩ := h ζ (Submodule.mem_span_singleton_self _)
      have h1 := hpair 1 c
      rw [one_smul, star_one, one_mul] at h1
      rw [hform, h1] at hb
      refine Submodule.mem_span_singleton.mpr ⟨-b, ?_⟩
      rw [← algebraMap_smul D.host.E (-b)]
      congr 1
      rw [map_neg]
      exact neg_eq_iff_eq_neg.mpr hb

theorem isSelfDualC_line : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → IsSelfDualC (negSp F.Lz) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
  intro D T L sc G F hF
  refine isSelfDualC_span_of_norm (negSp F.Lz) F.rk (F.ζ 0) ?_
  have h1 := congrFun (congrFun G.sp.dec0.gram 0) 0
  have h2 : star (fun i => G.sp.dec0.a i 0) ⬝ᵥ (HSpace.gram (G.V (Node.core 0)) *ᵥ (fun i => G.sp.dec0.a i 0)) = 1 := by
    have h3 : antiDiagonalSignGramMatrix 1 (1 : D.host.E) 0 0 = 1 := by simp [antiDiagonalSignGramMatrix]
    rw [h3, Matrix.mul_assoc] at h1
    exact h1
  rw [← hF.zB, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, F.oz.isoB] at h2
  rw [negSp_gram, neg_mulVec, dotProduct_neg]
  exact congrArg Neg.neg h2

end GlobalTheory.AscFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SquareAgree

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

structure IsThetaSubG (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W)
    (N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop where

  le : N ≤ algD M ψ emb

  fin : ∀ (v : Pl F) (f : SInf F (Fin n × Fin d)) (φ : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ), f ∈ M.Pol ψ emb →
    (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) → φ v ∈ augAt om v → pure f φ ∈ N

  lie : ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol ψ emb, ∀ f₁ ∈ M.Pol ψ emb,
    ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    ∀ φ : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) →
      pure f₁ φ ∈ N

  cpt : ∀ k ∈ KInf σ X emb, ∀ f ∈ M.Pol ψ emb, ∀ f₁ ∈ M.Pol ψ emb, Acts (evI F) (om (k, 1)) f f₁ →
    ∀ φ : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) →
      pure f₁ φ - pure f φ ∈ N

  stabFin : ∀ (v : Pl F), ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N

  stabLie : ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ algD M ψ emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

  stabCpt : ∀ k ∈ KInf σ W emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N

theorem IsDatum.fun_eq (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {Z : Type}
    (crd : Matrix (Fin n) (Fin d) (AE F E) → Z) (hc : Function.Surjective crd) {Φ : (Fin n × Fin d → AF F) → ℂ} {f f' : Z → ℂ}
    (h : IsDatum M ψ crd Φ f) (h' : IsDatum M ψ crd Φ f') : f = f' := by
  funext z
  obtain ⟨u, rfl⟩ := hc z
  rw [← h.2 u, ← h'.2 u]

end GlobalTheory.SquareAgree

end
end

