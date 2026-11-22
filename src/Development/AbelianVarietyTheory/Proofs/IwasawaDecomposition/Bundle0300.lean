import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocDec

open Polynomial

theorem denseRange_of_isAlgClosed (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [CharZero K] (E Ω : Type) [Field E] [Algebra E K] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
    (hE : DenseRange (algebraMap E K)) (ι : Ω →ₐ[E] AlgebraicClosure K) :
    letI : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)
    DenseRange ι := by
  letI : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)
  letI : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K (AlgebraicClosure K)
  show DenseRange ι
  rw [Metric.denseRange_iff]
  intro a δ δpos
  have hint : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  set f := minpoly K a with hf
  have fmon : f.Monic := minpoly.monic hint
  have fa0 : f.aeval a = 0 := minpoly.aeval _ _
  have fnatdeg0 : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hE fmon hε
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity
  have e : (g.map (algebraMap E K)).map (algebraMap K (AlgebraicClosure K)) =
      (g.map (algebraMap E Ω)).map (ι : Ω →+* AlgebraicClosure K) := by
    rw [Polynomial.map_map, Polynomial.map_map, ι.comp_algebraMap]
    congr 1
  rw [Polynomial.aroots_def, e, Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, rfl⟩ := hb
  exact ⟨y, by rwa [dist_eq_norm]⟩

theorem exists_algEquiv_of_norm_eq (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [CharZero K] (E Ω : Type) [Field E] [Algebra E K] [Field Ω] [Algebra E Ω]
    (hE : DenseRange (algebraMap E K)) :
    letI : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)
    ∀ (j j' : Ω →ₐ[E] AlgebraicClosure K), DenseRange j → (∀ x, ‖j' x‖ = ‖j x‖) →
      ∃ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ x, τ (j x) = j' x := by
  letI : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)
  letI : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K (AlgebraicClosure K)
  intro j j' hd h
  let Kb := AlgebraicClosure K
  let C := UniformSpace.Completion Kb
  let : NormedField Ω := NormedField.induced Ω Kb j.toRingHom j.injective
  have hj : Isometry j := AddMonoidHomClass.isometry_of_norm j fun _ => rfl
  let f : Ω →+* C := (UniformSpace.Completion.coeRingHom : Kb →+* C).comp j'.toRingHom
  have hf : Isometry f := AddMonoidHomClass.isometry_of_norm f fun x => by
    change ‖((j' x : Kb) : C)‖ = ‖j x‖
    rw [UniformSpace.Completion.norm_coe, h]
  let t : Kb →+* C :=
    IsDenseInducing.extendRingHom hj.isUniformInducing hd hf.uniformContinuous
  have ht : ∀ x, t (j x) = f x := fun x =>
    uniformly_extend_of_ind hj.isUniformInducing hd hf.uniformContinuous x
  have htc : Continuous t :=
    (uniformContinuous_uniformly_extend hj.isUniformInducing hd hf.uniformContinuous).continuous
  have : IsScalarTower K Kb C := inferInstance
  have hcoe : ∀ y : Kb, algebraMap Kb C y = (y : C) := fun y => rfl
  have hq : ∀ x : K, t (algebraMap K Kb x) = algebraMap K C x := by
    have hcC : Continuous (algebraMap K C) := by
      have e : (algebraMap K C : K → C) = fun x => ((algebraMap K Kb x : Kb) : C) :=
        funext fun x => IsScalarTower.algebraMap_apply K Kb C x
      rw [e]
      exact (UniformSpace.Completion.continuous_coe Kb).comp (continuous_algebraMap K Kb)
    have := hE.equalizer (htc.comp (continuous_algebraMap K Kb)) hcC (by
      funext e
      simp only [Function.comp_apply]
      have e1 : algebraMap K Kb (algebraMap E K e) = j (algebraMap E Ω e) := by
        rw [AlgHom.commutes]; exact (IsScalarTower.algebraMap_apply E K Kb e).symm
      rw [e1, ht]
      change ((j' (algebraMap E Ω e) : Kb) : C) = ((algebraMap K Kb (algebraMap E K e) : Kb) : C)
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply E K Kb e])
    exact congrFun this
  let ta : Kb →ₐ[K] C := ⟨t, hq⟩
  refine ⟨ta.restrictNormal' Kb, fun x => ?_⟩
  apply (algebraMap Kb C).injective
  exact (ta.restrictNormal_commutes Kb (j x)).trans (ht x)

theorem isIntegral_iff_norm_le_one (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
    letI : NormedField (Kbar w) := spectralNorm.normedField (w.adicCompletion E) (Kbar w)
    ∀ y : Kbar w, IsIntegral (w.adicCompletionIntegers E) y ↔ ‖y‖ ≤ 1 := by
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  letI : NormedField (Kbar w) := spectralNorm.normedField (w.adicCompletion E) (Kbar w)
  intro y
  let K := w.adicCompletion E
  let O := w.adicCompletionIntegers E
  have hO : ∀ x : K, ‖x‖ ≤ 1 ↔ x ∈ O := fun x => by
    rw [Valued.toNormedField.norm_le_one_iff]; rfl
  have hy : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have hn : ‖y‖ = spectralValue (minpoly K y) := rfl
  rw [hn, spectralValue_le_one_iff (minpoly.monic hy)]
  constructor
  · intro hi n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hi, Polynomial.coeff_map, hO]
    exact ((minpoly O y).coeff n).2
  · intro hc
    have hl : minpoly K y ∈ Polynomial.lifts (algebraMap O K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, (hO _).1 (hc n)⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hy)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K, hq]
    exact minpoly.aeval K y

end GlobalTheory.LocDec

namespace GlobalTheory.LocDec

open GlobalTheory.LocDict

theorem norm_eq_of_le_one_iff {Ω L : Type} [Field Ω] [NormedField L] (j j' : Ω →+* L)
    (h : ∀ x, ‖j x‖ ≤ 1 ↔ ‖j' x‖ ≤ 1) (x₀ : Ω) (h₀ : ‖j' x₀‖ = ‖j x₀‖) (h₁ : 0 < ‖j x₀‖)
    (h₂ : ‖j x₀‖ < 1) (x : Ω) : ‖j' x‖ = ‖j x‖ := by
  let v : AbsoluteValue Ω ℝ := (NormedField.toAbsoluteValue L).comp j.injective
  let v' : AbsoluteValue Ω ℝ := (NormedField.toAbsoluteValue L).comp j'.injective
  have hv : ∀ y, v y = ‖j y‖ := fun _ => rfl
  have hv' : ∀ y, v' y = ‖j' y‖ := fun _ => rfl
  have he : v.IsEquiv v' := by
    intro a b
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    · have := h (a / b)
      rw [map_div₀, map_div₀, norm_div, norm_div, div_le_one (by simpa using hb),
        div_le_one (by simpa using hb)] at this
      exact this
  obtain ⟨c, hc, hcv⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have e₁ := congrFun hcv x₀
  simp only [hv, hv'] at e₁
  have hc1 : c = 1 := (Real.rpow_right_inj h₁ h₂.ne).1 ((e₁.trans h₀).trans (Real.rpow_one _).symm)
  have e₂ := congrFun hcv x
  simp only [hv, hv', hc1, Real.rpow_one] at e₂
  exact e₂.symm

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem exists_mulEquiv_galLoc (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (ι : Ω →ₐ[E] Kbar w) (hι : IsLocEmb A w ι) :
    ∃ θ : Dec (F := E) A ≃* GalLoc w, Continuous θ ∧ Continuous θ.symm ∧
      ∀ σ : Dec (F := E) A, Lifts ι (θ σ) (σ : G E Ω) := by
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  letI : NormedField (Kbar w) := spectralNorm.normedField (w.adicCompletion E) (Kbar w)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have hdE : DenseRange (algebraMap E (w.adicCompletion E)) := HeightOneSpectrum.denseRange_algebraMap E w
  have hA : ∀ z, z ∈ A ↔ ‖ι z‖ ≤ 1 := fun z => (hι z).trans (isIntegral_iff_norm_le_one E w (ι z))
  have hd : DenseRange ι := denseRange_of_isAlgClosed (w.adicCompletion E) E Ω hdE ι
  have hnorm : ∀ (g : GalLoc w) (y : Kbar w), ‖g y‖ = ‖y‖ := fun g y =>
    (spectralNorm_eq_of_equiv g y).symm
  have hcont : ∀ g : GalLoc w, Continuous g := fun g =>
    (AddMonoidHomClass.isometry_of_norm g (hnorm g)).continuous

  have hres : ∀ g : GalLoc w, ∃ σ ∈ Dec (F := E) A, Lifts ι g σ := by
    intro g
    letI : Algebra Ω (Kbar w) := ι.toRingHom.toAlgebra
    have : IsScalarTower E Ω (Kbar w) := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
    let ta : Kbar w →ₐ[E] Kbar w := g.toAlgHom.restrictScalars E
    let σ : Ω ≃ₐ[E] Ω := ta.restrictNormal' Ω
    have hσ : ∀ x, g (ι x) = ι (σ x) := fun x => (ta.restrictNormal_commutes Ω x).symm
    refine ⟨σ, ?_, hσ⟩
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hA, hA, ← hnorm g, hσ]
    simp
  choose r hr hr' using hres
  let ρ : GalLoc w →* Dec (F := E) A := MonoidHom.mk' (fun g => ⟨r g, hr g⟩) fun g g' => by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    apply ι.toRingHom.injective
    change ι (r (g * g') x) = ι (r g (r g' x))
    rw [← hr', ← hr', ← hr']
    rfl
  have hρ : ∀ (g : GalLoc w) (x : Ω), g (ι x) = ι ((ρ g : Ω ≃ₐ[E] Ω) x) := hr'
  have hinj : Function.Injective ρ := fun g g' hgg => by
    have := hd.equalizer (hcont g) (hcont g') (funext fun x => by simp only [Function.comp_apply]; rw [hρ, hρ, hgg])
    exact AlgEquiv.ext (congrFun this)

  obtain ⟨x₀, hx₀, hx₀'⟩ : ∃ x₀ : E, 0 < ‖ι (algebraMap E Ω x₀)‖ ∧ ‖ι (algebraMap E Ω x₀)‖ < 1 := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hn : ∀ y : E, ‖ι (algebraMap E Ω y)‖ = ‖algebraMap E (w.adicCompletion E) y‖ := fun y => by
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply E (w.adicCompletion E) (Kbar w)]
      exact spectralNorm_extends _
    have hv : ∀ y : E, Valued.v (algebraMap E (w.adicCompletion E) y) = w.valuation E y := fun y => by
      first | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w y | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation w y | simp | rfl
    refine ⟨(a : E), ?_, ?_⟩
    · rw [hn, norm_pos_iff, map_ne_zero]
      exact_mod_cast ha0
    · rw [hn, Valued.toNormedField.norm_lt_one_iff, hv]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha
  have hsurj : Function.Surjective ρ := fun σ => by
    let j' : Ω →ₐ[E] Kbar w := ι.comp (σ : Ω ≃ₐ[E] Ω).toAlgHom
    have hj' : ∀ x, ‖j' x‖ = ‖ι x‖ := norm_eq_of_le_one_iff ι.toRingHom j'.toRingHom
      (fun x => by
        change ‖ι x‖ ≤ 1 ↔ ‖ι ((σ : Ω ≃ₐ[E] Ω) x)‖ ≤ 1
        rw [← hA, ← hA, apply_mem_iff_of_mem_Dec σ.2])
      (algebraMap E Ω x₀) (by
        change ‖ι ((σ : Ω ≃ₐ[E] Ω) (algebraMap E Ω x₀))‖ = _
        rw [AlgEquiv.commutes]; rfl) hx₀ hx₀'
    obtain ⟨τ, hτ⟩ := exists_algEquiv_of_norm_eq (w.adicCompletion E) E Ω hdE ι j' hd hj'
    refine ⟨τ, Subtype.ext (AlgEquiv.ext fun x => ι.toRingHom.injective ?_)⟩
    change ι ((ρ τ : Ω ≃ₐ[E] Ω) x) = ι ((σ : Ω ≃ₐ[E] Ω) x)
    rw [← hρ, hτ]
    rfl
  have hc : Continuous ρ := by
    refine continuous_induced_rng.2 ?_
    refine continuous_of_continuousAt_one ((Dec (F := E) A).subtype.comp ρ) ?_
    intro s hs
    rw [map_one, krullTopology_mem_nhds_one_iff] at hs
    obtain ⟨L, hL, hsub⟩ := hs
    let b := Module.finBasis E L
    have hi : ∀ i, ∀ᶠ g : GalLoc w in nhds 1, g (ι (b i)) = ι (b i) := fun i =>
      (stabilizer_isOpen_of_isIntegral (K := w.adicCompletion E) (ι (b i))).mem_nhds
        (show (1 : GalLoc w) • ι (b i) = ι (b i) from rfl)
    rw [Filter.mem_map]
    filter_upwards [Filter.eventually_all.2 hi] with g hg
    apply hsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have : ((ρ g : Ω ≃ₐ[E] Ω).toLinearMap.comp L.val.toLinearMap) = L.val.toLinearMap :=
      b.ext fun i => ι.toRingHom.injective ((hρ g _).symm.trans (hg i))
    exact LinearMap.congr_fun this ⟨x, hx⟩
  let e := MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩
  refine ⟨e.symm, Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) hc, hc,
    fun σ x => ?_⟩
  rw [hρ]
  exact congrArg (fun σ : Dec (F := E) A => ι ((σ : Ω ≃ₐ[E] Ω) x)) (e.apply_symm_apply σ)

theorem decomposition_mulEquiv_galLoc : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∃ θ : Dec (F := E) A ≃* GalLoc w, Continuous θ ∧ Continuous θ.symm ∧ ∀ σ : Dec (F := E) A, Lifts ι (θ σ) (σ : G E Ω) :=
  fun _ _ _ _ _ _ _ A w h ι hι => exists_mulEquiv_galLoc A w h ι hι

end GlobalTheory.LocDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryAdmissibleFiniteMultiplicity
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU.admitted

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_fin_mul_inf (y : UA E n) : ∃ a ∈ finU E n, ∃ b ∈ infU E n, y = a * b := by
  let yi := GeneralLinearGroup.map (pInf E) y.1
  have hyi : yi.valᴴ * yi.val = 1 := by
    have hy : cT (conjAd E) y.1.val * 1 * y.1.val = 1 := y.2
    have h3 : (cT (conjAd E) y.1.val).map (pInf E) = yi.valᴴ := by
      ext1 i j
      rw [Matrix.conjTranspose_apply]
      exact (infEq E).symm_apply_apply _
    have h := congrArg (pInf E).mapMatrix hy
    rw [map_mul, map_mul, map_one, mul_one, RingHom.mapMatrix_apply, h3] at h
    exact h
  let b : UA E n := ⟨infGL E n yi, infGL_mem_UA yi hyi⟩
  have hb : b ∈ infU E n := MonoidHom.mem_ker.2 (pFin_infGL yi)
  have ha : b⁻¹ * y ∈ finU E n := by
    refine MonoidHom.mem_ker.2 ?_
    rw [map_mul, map_inv]
    have : cInf b = cInf y := pInf_infGL yi
    rw [this, inv_mul_cancel]
  refine ⟨b⁻¹ * y, ha, b, hb, ?_⟩
  rw [fin_mul_inf ha hb, mul_inv_cancel_left]

def X (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) := Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_mem_X (φ : UA E n → ℂ) (x : infU E n) {ξ : UA E n → ℂ} (h : ξ ∈ X φ) : RU E n x ξ ∈ X φ := by
  have : X φ ≤ (X φ).comap (RU E n x) := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨x * k, (RU_RU _ _ _).symm⟩)
  exact this h

theorem self_mem_X (φ : UA E n → ℂ) : φ ∈ X φ :=
  Submodule.subset_span ⟨1, by show RU E n 1 φ = φ; rw [map_one]; rfl⟩

def rhoX (φ : UA E n → ℂ) (x : infU E n) : Module.End ℂ (X φ) :=
  (RU E n x).restrict fun _ h => RU_mem_X φ x h

theorem rhoX_mul (φ : UA E n → ℂ) (x y : infU E n) : rhoX φ (x * y) = rhoX φ x * rhoX φ y :=
  LinearMap.ext fun ξ => Subtype.ext (RU_RU (x : UA E n) y ξ.1).symm

def coef (φ : UA E n → ℂ) : Module.Dual ℂ (Module.End ℂ (X φ)) →ₗ[ℂ] (infU E n → ℂ) :=
  LinearMap.pi fun x => LinearMap.applyₗ (rhoX φ x)

def C (φ : UA E n → ℂ) : Submodule ℂ (infU E n → ℂ) := LinearMap.range (coef φ)

theorem mem_C (φ : UA E n → ℂ) (f : X φ →ₗ[ℂ] ℂ) (ξ : X φ) : (fun x : infU E n => f (rhoX φ x ξ)) ∈ C φ :=
  ⟨f ∘ₗ LinearMap.applyₗ ξ, rfl⟩

theorem C_right (φ : UA E n → ℂ) {c : infU E n → ℂ} (hc : c ∈ C φ) (y : infU E n) :
    (fun x => c (x * y)) ∈ C φ := by
  obtain ⟨B, rfl⟩ := hc
  refine ⟨B ∘ₗ LinearMap.mulRight ℂ (rhoX φ y), funext fun x => ?_⟩
  change B (rhoX φ x * rhoX φ y) = B (rhoX φ (x * y))
  rw [rhoX_mul]

def Y (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  ⨅ g : UA E n, (C φ).comap (LinearMap.funLeft ℂ ℂ fun x : infU E n => g * (x : UA E n))

theorem mem_Y {φ ψ : UA E n → ℂ} : ψ ∈ Y φ ↔ ∀ g : UA E n, (fun x : infU E n => ψ (g * x)) ∈ C φ := by
  simp only [Y, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem le_Y (π : AutSub E n) {φ : UA E n → ℂ} (hφ : φ ∈ π.V) (h0 : φ ≠ 0) : π.V ≤ Y φ := by
  have hφY : φ ∈ Y φ := mem_Y.2 fun g =>
    mem_C φ ((LinearMap.proj g) ∘ₗ (X φ).subtype) ⟨φ, self_mem_X φ⟩
  have hst : ∀ x, ∀ ψ ∈ π.V ⊓ Y φ, RU E n x ψ ∈ π.V ⊓ Y φ := by
    intro x ψ hψ
    refine ⟨π.isAut.stable x ψ hψ.1, mem_Y.2 fun g => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_fin_mul_inf x
    have e : (fun z : infU E n => RU E n (a * b) ψ (g * z)) = fun z => ψ ((g * a) * ((z * ⟨b, hb⟩ : infU E n) : UA E n)) := by
      funext z
      rw [RU_apply, Subgroup.coe_mul, Subgroup.coe_mk, ← mul_assoc, mul_assoc g, ← fin_mul_inf ha z.2, ← mul_assoc, mul_assoc (g * a)]
    rw [e]
    exact C_right φ (mem_Y.1 hψ.2 (g * a)) ⟨b, hb⟩
  rcases π.isAut.irred (π.V ⊓ Y φ) inf_le_left hst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨hφ, hφY⟩ : φ ∈ π.V ⊓ Y φ))) h0
  · rw [← h]
    exact inf_le_right

theorem eq_zero_of_vanish {K : Subgroup (finU E n)} {S : Finset (UA E n)}
    (hS : ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ x ∈ infU E n, ∃ k ∈ K, g = γ * s * x * (k : UA E n))
    {f : UA E n → ℂ} (hl : ∀ γ ∈ ratU E n, ∀ g, f (γ * g) = f g) (hK : ∀ k ∈ K, RU E n k f = f)
    (h0 : ∀ s ∈ S, ∀ x ∈ infU E n, f (s * x) = 0) : f = 0 := by
  funext g
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  rw [mul_assoc, mul_assoc, hl γ hγ, ← mul_assoc]
  have := congrFun (hK k hk) (s * x)
  rw [RU_apply] at this
  rw [this, h0 s hs x hx]
  rfl

theorem exists_ne_zero (π : AutSub E n) : ∃ φ ∈ π.V, φ ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot π.isAut.ne_bot

theorem finiteDimensional_fixed (π : AutSub E n) (K : Subgroup (finU E n)) (hK : IsOpen (K : Set (finU E n))) :
    FiniteDimensional ℂ (fixed (π.rep.comp (finU E n).subtype) K) := by
  obtain ⟨φ, hφ, h0⟩ := exists_ne_zero π
  have : FiniteDimensional ℂ (X φ) := (π.isAut.aut φ hφ).kfin
  have : FiniteDimensional ℂ (C φ) := LinearMap.finiteDimensional_range _
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hK
  let L : fixed (π.rep.comp (finU E n).subtype) K →ₗ[ℂ] (S → C φ) :=
    LinearMap.pi fun s => LinearMap.codRestrict (C φ)
      ((LinearMap.funLeft ℂ ℂ fun x : infU E n => (s : UA E n) * x) ∘ₗ π.V.subtype ∘ₗ (fixed _ K).subtype)
      (fun ψ => mem_Y.1 (le_Y π hφ h0 ψ.1.2) s)
  refine Module.Finite.of_injective L (LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun ψ hψ => ?_))
  have hK' : ∀ k ∈ K, RU E n k ψ.1.1 = ψ.1.1 := fun k hk => by
    have e : (π.rep.comp (finU E n).subtype) k ψ.1 = (((1 : K →* ℂˣ) ⟨k, hk⟩ : ℂˣ) : ℂ) • ψ.1 := ψ.2 ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at e
    exact congrArg Subtype.val e
  have hf := eq_zero_of_vanish hS (π.isAut.aut _ ψ.1.2).left hK' fun s hs x hx =>
    congrFun (congrArg Subtype.val (congrFun hψ ⟨s, hs⟩)) ⟨x, hx⟩
  exact Subtype.ext (Subtype.ext hf)

def stab (φ : UA E n → ℂ) : Subgroup (finU E n) where
  carrier := {k | RU E n k φ = φ}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Subgroup.coe_mul, ← RU_RU, hb, ha]
  one_mem' := by
    show RU E n 1 φ = φ
    rw [map_one]
    rfl
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [RU_RU, InvMemClass.coe_inv, inv_mul_cancel, map_one]
    rfl

theorem finiteDimensional_hom (π : AutSub E n) : FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) := by
  obtain ⟨φ, hφ, h0⟩ := exists_ne_zero π
  have : FiniteDimensional ℂ (X φ) := (π.isAut.aut φ hφ).kfin
  have : FiniteDimensional ℂ (C φ) := LinearMap.finiteDimensional_range _
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n (stab φ) (π.isAut.aut φ hφ).level
  let φV : π.V := ⟨φ, hφ⟩
  have hXV : X φ ≤ π.V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact π.isAut.stable _ φ hφ)
  have hmem : ∀ (T : π.rep.IntertwiningMap (autRep E n)) (s : UA E n),
      (fun x : infU E n => (T φV).1 (s * x)) ∈ C φ := by
    intro T s
    have e : (fun x : infU E n => (T φV).1 (s * x)) = fun x => ((LinearMap.proj s) ∘ₗ (autU E n).subtype ∘ₗ
        T.toLinearMap ∘ₗ Submodule.inclusion hXV) (rhoX φ x ⟨φ, self_mem_X φ⟩) :=
      funext fun x => (congrFun (congrArg Subtype.val (LinearMap.congr_fun (T.isIntertwining' (x : UA E n)) φV)) s).symm
    rw [e]
    exact mem_C φ _ _
  let Φ : π.rep.IntertwiningMap (autRep E n) →ₗ[ℂ] (S → C φ) :=
    { toFun := fun T s => ⟨fun x : infU E n => (T φV).1 ((s : UA E n) * x), hmem T s⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ (LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun T hT => ?_))
  have hK : ∀ k ∈ stab φ, RU E n k (T φV).1 = (T φV).1 := fun k hk => by
    have e : T (π.rep k φV) = autRep E n k (T φV) := LinearMap.congr_fun (T.isIntertwining' (k : UA E n)) φV
    rw [show π.rep k φV = φV from Subtype.ext hk] at e
    exact (congrArg Subtype.val e).symm
  have hTφ : T φV = 0 := Subtype.ext (eq_zero_of_vanish hS (mem_autU.1 (T φV).2).left hK fun s hs x hx =>
    congrFun (congrArg Subtype.val (congrFun hT ⟨s, hs⟩)) ⟨x, hx⟩)
  let W : Submodule ℂ (UA E n → ℂ) := (LinearMap.ker T.toLinearMap).map π.V.subtype
  have hst : ∀ x, ∀ ψ ∈ W, RU E n x ψ ∈ W := by
    rintro x _ ⟨ψ', hψ', rfl⟩
    refine ⟨π.rep x ψ', ?_, rfl⟩
    have h1 : T ψ' = 0 := hψ'
    change T (π.rep x ψ') = 0
    have h2 : T (π.rep x ψ') = autRep E n x (T ψ') := LinearMap.congr_fun (T.isIntertwining' x) ψ'
    rw [h2, h1, map_zero]
  rcases π.isAut.irred W (Submodule.map_subtype_le _ _) hst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨φV, hTφ, rfl⟩ : φ ∈ W))) h0
  · refine DFunLike.ext _ _ fun ψ => ?_
    obtain ⟨ψ', hψ', e⟩ : ψ.1 ∈ W := h.symm ▸ ψ.2
    rw [← Subtype.ext e]
    exact hψ'

theorem admissible_finiteMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n),
    (∀ K : Subgroup (finU E n), IsOpen (K : Set (finU E n)) →
      FiniteDimensional ℂ (fixed (π.rep.comp (finU E n).subtype) K)) ∧
    FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) :=
  fun _ _ _ _ _ π => ⟨fun K hK => finiteDimensional_fixed π K hK, finiteDimensional_hom π⟩

end GlobalTheory.DefU.admitted
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFiniteStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicGL_homeomorph_infinite_finite : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ e : GA E a ≃ₜ* GL (Fin a) (Cinf E) × GL (Fin a) (Af E), ∀ g, e g = (GeneralLinearGroup.map (pInf E) g, GeneralLinearGroup.map (pFin E) g) := by
  first | exact @GlobalTheory.CuspRep.GASplit.exists_split | exact GlobalTheory.CuspRep.GASplit.exists_split | (intros; apply GlobalTheory.CuspRep.GASplit.exists_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruenceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruence_level_maps_into_lattice_congruence : ∀ (D : D7) (V : HSp D) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (hF : D.host.F = maximalRealSubfield D.host.E), StdFrame hF P → ∀ N : ℕ, 0 < N → ∃ N' : ℕ, 0 < N' ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N' κ → GlobalTheory.Member.FinCong V N (P.ψ κ) := by
  first | exact @GlobalTheory.StdFrameCong.exists_cong_finCong | exact GlobalTheory.StdFrameCong.exists_cong_finCong | (intros; apply GlobalTheory.StdFrameCong.exists_cong_finCong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddingsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_reference_characters_good_embeddings : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), T.Q.Pins → AlgTie T → R.toLevCh.Is A.μ0 → ValKs R → ∃ (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ChiAt R i σ (chiW ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ) := by
  first | exact @GlobalTheory.ConjRefChar.exists_chiAt | exact GlobalTheory.ConjRefChar.exists_chiAt | (intros; apply GlobalTheory.ConjRefChar.exists_chiAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteUnitaryInfinitePointOfUnitaryFamilStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteUnitaryInfinitePoint_of_unitary_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : InfinitePlace E → GL (Fin n) ℂ), (∀ v, ((g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ x ∈ infU E n, cAll x = g := by
  first | exact @GlobalTheory.InfSurj.exists_infU_cAll_eq | exact GlobalTheory.InfSurj.exists_infU_cAll_eq | (intros; apply GlobalTheory.InfSurj.exists_infU_cAll_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonnegStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nefFib_of_curve_degrees_nonneg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (L : HermLB p), (∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (q : ℕ) [Fact q.Prime] [Algebra (ZMod q) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1) → ArInt.NefFib L := by
  first | exact @GlobalTheory.ArInt.nefFib_of_primeField | exact GlobalTheory.ArInt.nefFib_of_primeField | (intros; apply GlobalTheory.ArInt.nefFib_of_primeField <;> assumption)
end

