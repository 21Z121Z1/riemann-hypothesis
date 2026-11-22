import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.KernelCondGlob
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.WeilEquivOfLocalDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0687
import GroundTheory.GlobalFields.CompletionAtPlace.Degree
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.KernelCond
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.Artin.OneDim
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.TateThesis.Bundle0010
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import GroundTheory.GlobalFields.TateThesis.Bundle0006

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.ExistsCompletionEquivOfHe
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions.RamifiedPlaceLift

theorem continuous_symm_of_valued_eq {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 F)}
    (ι : v.adicCompletion K ≃+* w.adicCompletion F) (hv : ∀ x, Valued.v (ι x) = Valued.v x) :
    Continuous ι.symm := by
  refine continuous_of_continuousAt_zero ι.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨x, hx⟩ : ∃ x : v.adicCompletion K, Valued.v.restrict x = γ.1 :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective _ γ.1
  have hx0 : Valued.v x ≠ 0 := by
    intro h0
    apply γ.ne_zero
    rw [← hx]
    simpa using h0
  have hy0 : Valued.v.restrict (ι x) ≠ 0 := by
    simpa [hv] using hx0
  refine Valued.mem_nhds_zero.2 ⟨Units.mk0 _ hy0, fun y hy => hγ ?_⟩
  have h1 : Valued.v y < Valued.v (ι x) := by
    simpa using hy
  have h2 : Valued.v (ι.symm y) < Valued.v x := by
    rw [← hv (ι.symm y), ← hv x, RingEquiv.apply_symm_apply]
    exact h1
  show Valued.v.restrict (ι.symm y) < γ
  rw [← hx]
  simpa using h2

section Pair

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
  {K F : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [Algebra K F] [IsScalarTower K F Ω]
  {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 F)}

omit [IsAlgClosure F Ω] in

theorem inertiaDeg_eq_one (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (hloc : ∀ (σ : Weil h) (x : F), (σ : G K Ω) (algebraMap F Ω x) = algebraMap F Ω x) :
    w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨(GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h').symm⟩
  have hn := normV_eq_of_localDegreeOne h h' hloc
  have hf : normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 K) := by
    simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm
  rw [hn] at hf
  exact Nat.pow_right_injective (one_lt_normV v) (hf.symm.trans (pow_one _).symm)

omit [IsAlgClosure F Ω] in

theorem exists_completionEquiv_of_he (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (hloc : ∀ (σ : Weil h) (x : F), (σ : G K Ω) (algebraMap F Ω x) = algebraMap F Ω x)
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    ∃ ι : v.adicCompletion K ≃+* w.adicCompletion F, Continuous ι ∧ Continuous ι.symm ∧
      (∀ x : K, ι (algebraMap K _ x) = algebraMap F _ (algebraMap K F x)) ∧
      ∀ x, Valued.v (ι x) = Valued.v x := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨(GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h').symm⟩
  let _ : Algebra (v.adicCompletion K) (w.adicCompletion F) := (GroundTheory.Global.adicCompletionMap v w).toAlgebra
  have : IsScalarTower K (v.adicCompletion K) (w.adicCompletion F) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply K F (w.adicCompletion F)]
      exact (GroundTheory.Global.adicCompletionMap_algebraMap v w x).symm
  have : ContinuousSMul (v.adicCompletion K) (w.adicCompletion F) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v w)
  have hfin : Module.finrank (v.adicCompletion K) (w.adicCompletion F) = 1 := by
    rw [GroundTheory.Global.finrank_adicCompletion v w, he, inertiaDeg_eq_one h h' hloc]
  have hbij : Function.Bijective (algebraMap (v.adicCompletion K) (w.adicCompletion F)) := by
    refine ⟨(algebraMap (v.adicCompletion K) (w.adicCompletion F)).injective, fun y => ?_⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := v.adicCompletion K) (1 : w.adicCompletion F)
      one_ne_zero).1 hfin y
    exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩
  let ι := RingEquiv.ofBijective (algebraMap (v.adicCompletion K) (w.adicCompletion F)) hbij
  have hv : ∀ x, Valued.v (ι x) = Valued.v x := fun x => by
    have := GroundTheory.Global.valued_algebraMap_adicCompletion v w x
    rw [he, pow_one] at this
    exact this
  exact ⟨ι, GroundTheory.Global.continuous_adicCompletionMap v w, continuous_symm_of_valued_eq ι hv,
    GroundTheory.Global.adicCompletionMap_algebraMap v w, hv⟩

end Pair

end PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions.RamifiedPlaceLift

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.LaurentMonomialEqOneOfCircle
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

section LocalLeaves

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end LocalLeaves

section Weights

open GlobalTheory.WeilRestrict Polynomial

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
  {K L : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in

theorem eq_resWeil_of_agree (h : IsPlaceOver A v) (h' : IsPlaceOver A v') {σ' : Weil h'} {σ : Weil h}
    (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) : σ = resWeil h h' σ' :=
  Subtype.ext (AlgEquiv.ext fun z => (hσ z).trans (resWeil_apply h h' σ' z).symm)

theorem induces_lpTwist (h : IsPlaceOver A v) (h' : IsPlaceOver A v') {X : WD h'} {Y : WD h}
    (hXY : Induces X Y) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (ξ' : Weil h' →* ℂˣ) (hξ' : IsSmooth ξ')
    (hres : ∀ σ', ξ' σ' = ξ (resWeil h h' σ')) :
    Induces (X.lpTwist ξ' hξ') (Y.lpTwist ξ hξ) := by
  obtain ⟨m, n, a, b, j, rfl, rfl, hn, hj, hspan⟩ := hXY
  refine ⟨m, n, a.twist ξ' hξ', b.twist ξ hξ, j, (WD.lpTwist_mk _ _ _).symm, (WD.lpTwist_mk _ _ _).symm, hn,
    fun σ' σ hσ u => ?_, ?_⟩
  · have e := eq_resWeil_of_agree h h' hσ
    simp only [WDRep.twist_ρ, LinearMap.smul_apply, map_smul, hj σ' σ hσ u, hres, ← e]
  · rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g, u⟩, rfl⟩
    have e : b.ρ g (j u) = ((ξ g : ℂ))⁻¹ • (b.twist ξ hξ).ρ g (j u) := by
      rw [WDRep.twist_ρ, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    show b.ρ g (j u) ∈ _
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(g, u), rfl⟩)

end Weights

section Twist

open Polynomial

theorem prod_map_finsetSum {ι : Type*} (s : Finset ι) (M : ι → Multiset ℂ) (f : ℂ → ℂ[X]) :
    ((∑ i ∈ s, M i).map f).prod = ∏ i ∈ s, ((M i).map f).prod := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, Multiset.map_add, Multiset.prod_add, ih]

theorem filter_finsetSum {ι : Type*} (s : Finset ι) (M : ι → Multiset ℂ) (p : ℂ → Prop) [DecidablePred p] :
    (∑ i ∈ s, M i).filter p = ∑ i ∈ s, (M i).filter p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Multiset.filter_add, ih]

theorem map_finsetSum {ι : Type*} (s : Finset ι) (M : ι → Multiset ℂ) (f : ℂ → ℂ) :
    (∑ i ∈ s, M i).map f = ∑ i ∈ s, (M i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Multiset.map_add, ih]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem eig_lpTwist (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (σ : Weil h) :
    (x.lpTwist ξ hξ).eig σ = (x.eig σ).map (· * (ξ σ : ℂ)) := by
  induction x using WD.ind with
  | hP n a => rw [WD.lpTwist_mk, WD.eig_mk, WD.eig_mk, WDRep.twist_ρ, GlobalTheory.RowTie.EigTwist.roots_charpoly_smul]

theorem charPol_lpTwist_of_eq_one (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) {σ : Weil h} (h1 : ξ σ = 1) :
    (x.lpTwist ξ hξ).charPol σ = x.charPol σ := by
  induction x using WD.ind with
  | hP n a => rw [WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk, WDRep.twist_ρ, h1, Units.val_one, one_smul]

theorem prod_charPol_eq {r : ℕ} (p q : Fin r → ℕ) (x y : Fin r → WD h) (σ : Weil h) :
    ∏ i, (x i).charPol σ ^ p i * (y i).charPol σ ^ q i =
      ((∑ i, (p i • (x i).eig σ + q i • (y i).eig σ)).map fun α => X - C α).prod := by
  rw [prod_map_finsetSum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_nsmul, Multiset.map_nsmul, Multiset.prod_nsmul,
    Multiset.prod_nsmul, ← WD.charPol_eq_prod, ← WD.charPol_eq_prod]

end Twist

section Assembly

open GlobalTheory.WeilRestrict

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

end Assembly

end PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

end
end

