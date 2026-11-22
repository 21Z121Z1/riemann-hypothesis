import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ClausesIffExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralInConeDegreeOfValuativeBound
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal.ValInt

theorem ratFunc_top_fg {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (h : (⊤ : IntermediateField K Ω).FG) :
    (⊤ : IntermediateField K (RatFunc Ω)).FG := by
  classical
  obtain ⟨S, hS⟩ := h
  refine ⟨insert RatFunc.X (S.image (algebraMap Ω (RatFunc Ω))), ?_⟩
  set F := IntermediateField.adjoin K
    (↑(insert RatFunc.X (S.image (algebraMap Ω (RatFunc Ω)))) : Set (RatFunc Ω)) with hF
  have hX : (RatFunc.X : RatFunc Ω) ∈ F := IntermediateField.subset_adjoin _ _ (by simp)
  have hc : ∀ a : Ω, algebraMap Ω (RatFunc Ω) a ∈ F := by
    intro a
    have ha : a ∈ IntermediateField.adjoin K (S : Set Ω) := hS ▸ IntermediateField.mem_top
    have hm : algebraMap Ω (RatFunc Ω) a ∈
        (IntermediateField.adjoin K (S : Set Ω)).map (IsScalarTower.toAlgHom K Ω (RatFunc Ω)) := ⟨a, ha, rfl⟩
    rw [IntermediateField.adjoin_map] at hm
    refine IntermediateField.adjoin.mono K _ _ ?_ hm
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy))
  have hp : ∀ p : Polynomial Ω, algebraMap (Polynomial Ω) (RatFunc Ω) p ∈ F := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]; exact hc a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a ih => rw [pow_succ, ← mul_assoc, map_mul, RatFunc.algebraMap_X]; exact mul_mem ih hX
  refine eq_top_iff.2 fun x _ => ?_
  rw [← RatFunc.num_div_denom x]
  exact div_mem (hp _) (hp _)

theorem isIntegral_of_map_subalgebra {K R L : Type} [Field K] [CommRing R] [Algebra K R] [CommRing L] [Algebra K L]
    (φ : R →ₐ[K] L) (hφ : Function.Injective φ) (B : Subalgebra K R) (y : R)
    (h : IsIntegral (B.map φ) (φ y)) : IsIntegral B y := by
  let e := B.equivMapOfInjective φ hφ
  obtain ⟨p, hm, hp⟩ := h
  refine ⟨p.map e.symm.toRingHom, hm.map _, hφ ?_⟩
  rw [map_zero, ← hp]
  change φ.toRingHom _ = _
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  ext x
  exact congrArg Subtype.val (e.apply_symm_apply x)

theorem coneAlg_fg {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K V] (ev : V →ₗ[K] Ω) : (coneAlg ev).FG := by
  let b := Module.finBasis K V
  let ψ : V →ₗ[K] Polynomial Ω := (LinearMap.mulLeft K (Polynomial.X : Polynomial Ω)) ∘ₗ
    (IsScalarTower.toAlgHom K Ω (Polynomial Ω)).toLinearMap ∘ₗ ev
  have e : coneAlg ev = Algebra.adjoin K (ψ '' Set.range b) := by
    rw [← Algebra.adjoin_span, ← Submodule.map_span, b.span_eq, Submodule.map_top]
    rfl
  exact Subalgebra.fg_def.2 ⟨_, (Set.finite_range b).image ψ, e.symm⟩

theorem isIntDeg_of_valBound : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω), CharZero K → FiniteDimensional K V → (⊤ : IntermediateField K Ω).FG →
    ∀ (τ : ℕ) (t : Ω), ValBound ev τ t → IsIntDeg ev τ t := by
  intro K V Ω _ _ _ _ _ ev hK hV hfg τ t hb
  haveI := hK
  haveI := hV
  let φ : Polynomial Ω →ₐ[K] RatFunc Ω := IsScalarTower.toAlgHom K (Polynomial Ω) (RatFunc Ω)
  have hφ : Function.Injective φ := RatFunc.algebraMap_injective Ω
  have hφa : ∀ p, φ p = algebraMap (Polynomial Ω) (RatFunc Ω) p := fun _ => rfl
  refine isIntegral_of_map_subalgebra φ hφ _ _ (GlobalTheory.T.isIntegral_of_forall_valuation_le_one_of_fg K (RatFunc Ω) (ratFunc_top_fg hfg)
    ((coneAlg ev).map φ) ((coneAlg_fg ev).map φ) _ fun μ hμ => ?_)
  have hK1 : ∀ a : K, a ≠ 0 → μ (algebraMap K (RatFunc Ω) a) = 1 := by
    intro a ha
    have h1 : μ (algebraMap K (RatFunc Ω) a) ≤ 1 := hμ _ (Subalgebra.algebraMap_mem _ a)
    have h2 : μ (algebraMap K (RatFunc Ω) a⁻¹) ≤ 1 := hμ _ (Subalgebra.algebraMap_mem _ a⁻¹)
    have h3 : μ (algebraMap K (RatFunc Ω) a) * μ (algebraMap K (RatFunc Ω) a⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ℝ≥0) = _ := h3.symm
      _ ≤ μ (algebraMap K (RatFunc Ω) a) := mul_le_of_le_one_right zero_le' h2
  obtain ⟨v, hv⟩ := hb (μ.comap (algebraMap Ω (RatFunc Ω))) fun a ha => by
    rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]; exact hK1 a ha
  rw [Valuation.comap_apply, Valuation.comap_apply] at hv
  have hXv : μ (RatFunc.X * algebraMap Ω (RatFunc Ω) (ev v)) ≤ 1 := by
    refine hμ _ (Subalgebra.mem_map.2 ⟨_, Algebra.subset_adjoin ⟨v, rfl⟩, ?_⟩)
    rw [hφa, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [hφa, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, map_mul, map_pow]
  calc μ RatFunc.X ^ τ * μ (algebraMap Ω (RatFunc Ω) t)
      ≤ μ RatFunc.X ^ τ * μ (algebraMap Ω (RatFunc Ω) (ev v)) ^ τ := mul_le_mul_of_nonneg_left hv zero_le'
    _ = μ (RatFunc.X * algebraMap Ω (RatFunc Ω) (ev v)) ^ τ := by rw [map_mul, mul_pow]
    _ ≤ 1 := pow_le_one₀ zero_le' hXv

end GlobalTheory.DegVal.ValInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimmersionFlatValuationSubringBaseRing
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ValLocal

theorem exists_dvd_away {A : Type} [CommRing A] [IsDedekindDomain A] (q : Ideal A) [q.IsPrime] (a b : A) (hb : b ≠ 0) :
    ∃ s r : A, s ∉ q ∧ (s * a = r * b ∨ s * b = r * a) := by
  by_cases hq : q = ⊥
  · exact ⟨b, a, by simpa [hq] using hb, Or.inl (mul_comm _ _)⟩
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq (Localization.AtPrime q)
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
    IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
  have key : ∀ (u v : A) (z : Localization.AtPrime q), algebraMap A _ u * z = algebraMap A _ v →
      ∃ s r : A, s ∉ q ∧ s * v = r * u := by
    intro u v z hz
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj q.primeCompl z
    refine ⟨s, r, s.2, hinj ?_⟩
    rw [map_mul, map_mul, ← hz, ← hrs]
    ring
  obtain ⟨z, hz | hz⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime q) a) (algebraMap A _ b)
  · obtain ⟨s, r, hs, h⟩ := key a b z hz
    exact ⟨s, r, hs, Or.inr h⟩
  · obtain ⟨s, r, hs, h⟩ := key b a z hz
    exact ⟨s, r, hs, Or.inl h⟩

theorem exists_integral_frac {F : Type} [Field F] [NumberField F] (W : ValuationSubring F) (x : W) :
    ∃ a s : W, IsIntegral ℤ (a : F) ∧ IsIntegral ℤ (s : F) ∧ IsUnit s ∧ x * s = a := by
  have hmem : ∀ y : 𝓞 F, (y : F) ∈ W := fun y => by
    have h : IsIntegral W (y : F) := y.isIntegral_coe.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h
    rw [← hz]
    exact z.2
  let φ : 𝓞 F →+* W := (algebraMap (𝓞 F) F).codRestrict W.toSubring hmem
  have hφ : ∀ y : 𝓞 F, ((φ y : W) : F) = (y : F) := fun _ => rfl
  let q : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal W).comap φ
  have hunit : ∀ s : 𝓞 F, s ∉ q → IsUnit (φ s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (x : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : (b : F) ≠ 0 := by exact_mod_cast hb0
  have hxb : (x : F) * b = a := by
    rw [← hx]
    exact div_mul_cancel₀ _ hbF
  obtain ⟨s, r, hs, h | h⟩ := exists_dvd_away q a b hb0
  · refine ⟨φ r, φ s, r.isIntegral_coe, s.isIntegral_coe, hunit s hs, Subtype.ext ?_⟩
    have h' : (s : F) * a = r * b := by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h
    show (x : F) * s = r
    apply mul_right_cancel₀ hbF
    rw [← h', ← hxb]
    ring
  · have h' : (s : F) * b = r * a := by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h
    have hxr : x * φ r = φ s := by
      apply Subtype.ext
      show (x : F) * r = s
      apply mul_right_cancel₀ hbF
      rw [h', ← hxb]
      ring
    exact ⟨φ s, φ r, s.isIntegral_coe, r.isIntegral_coe,
      isUnit_of_mul_isUnit_right (hxr ▸ hunit s hs), hxr⟩

theorem preimmersion_flat :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), IsBaseRing β → ∀ (W : ValuationSubring c.F) (b : O →+* W), W.subtype.comp b = β → IsPreimmersion (spMap b) ∧ Flat (spMap b) := by
  intro E _ _ _ H l c O _ β hβ W b hb
  haveI := c.fin
  haveI : NumberField c.F := {}
  letI : Algebra O W := b.toAlgebra
  have hbv : ∀ o : O, ((b o : W) : c.F) = β o := fun o => by rw [← hb]; rfl
  have hinj : Function.Injective b := fun u v h => hβ.1 (by rw [← hbv, ← hbv, h])
  let S : Submonoid O := (IsUnit.submonoid W).comap b
  haveI : IsLocalization S W := by
    refine (isLocalization_iff S W).2 ⟨fun y => y.2, fun z => ?_, fun {u v} h => ⟨1, by rw [hinj h]⟩⟩
    obtain ⟨a, s, ha, hs, hu, hz⟩ := exists_integral_frac W z
    obtain ⟨a', ha'⟩ := hβ.2 _ ha
    obtain ⟨s', hs'⟩ := hβ.2 _ hs
    have e1 : b a' = a := Subtype.ext (by rw [hbv, ha'])
    have e2 : b s' = s := Subtype.ext (by rw [hbv, hs'])
    refine ⟨⟨a', ⟨s', ?_⟩⟩, ?_⟩
    · show IsUnit (b s')
      rwa [e2]
    · show z * b s' = b a'
      rw [e1, e2, hz]
  refine ⟨IsPreimmersion.of_isLocalization (R := O) (S := W) S, ?_⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact (RingHom.flat_algebraMap_iff (R := O) (S := W)).2 (IsLocalization.flat W S)

end GlobalTheory.ValLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnipotentModIdealLiftLaInv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.OrbitSep

theorem unipAt_inv_liftLa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (I : Ideal (𝓞 E)) («γ» : LevelAut Dw l), l.Mb ≤ I → UnipAt I «γ» → ∃ m : ℕ, ∀ x : Dw.La, ((liftLa «γ»⁻¹ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  intro E _ _ _ H Dw l I γ hI hU
  obtain ⟨m, hm⟩ := hU
  set M : Submodule (𝓞 E) Dw.La := I • ⊤ with hMdef
  set f := liftLa γ with hfdef
  set g := liftLa γ⁻¹ with hgdef
  have hN : l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ≤ M := Submodule.smul_mono_left hI
  have hpres : ∀ φ : Dw.La →ₗ[𝓞 E] Dw.La, M ≤ M.comap φ := by
    intro φ
    rw [← Submodule.map_le_iff_le_comap, hMdef, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have hgf : ∀ x, g (f x) - x ∈ M := by
    intro x
    apply hN
    rw [← Submodule.Quotient.eq]
    have h1 := liftLa_spec (γ⁻¹) (f x)
    have h2 := liftLa_spec γ x
    simp only [Submodule.mkQ_apply] at h1 h2
    rw [hgdef, h1, hfdef, h2]
    exact γ.symm_apply_apply _
  have hfg : ∀ x, f (g x) - x ∈ M := by
    intro x
    apply hN
    rw [← Submodule.Quotient.eq]
    have h1 := liftLa_spec γ (g x)
    have h2 := liftLa_spec (γ⁻¹) x
    simp only [Submodule.mkQ_apply] at h1 h2
    rw [hfdef, h1, hgdef, h2]
    exact γ.apply_symm_apply _
  let A := M.mapQ M f (hpres f)
  let B := M.mapQ M g (hpres g)
  have hBA : B * A = 1 := by
    ext x
    simp only [Module.End.mul_apply, A, B, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq M).2 (hgf x)
  have hAB : A * B = 1 := by
    ext x
    simp only [Module.End.mul_apply, A, B, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq M).2 (hfg x)
  have hdesc : ∀ (φ : Dw.La →ₗ[𝓞 E] Dw.La) (k : ℕ) (x : Dw.La),
      M.mkQ (((φ - 1) ^ k) x) = ((M.mapQ M φ (hpres φ) - 1) ^ k) (M.mkQ x) := by
    intro φ k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
  have hA0 : (A - 1) ^ m = 0 := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
    rw [← Submodule.mkQ_apply, ← hdesc f m x, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hm x
  have hcomm : Commute B (1 - A) := by
    refine Commute.sub_right (Commute.one_right B) ?_
    exact (hBA.trans hAB.symm)
  have hB0 : (B - 1) ^ m = 0 := by
    have e : B - 1 = B * (1 - A) := by rw [mul_sub, mul_one, hBA]
    rw [e, hcomm.mul_pow, show (1 - A) = -(A - 1) by abel, neg_pow, hA0, mul_zero, mul_zero]
  refine ⟨m, fun x => ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, hdesc g m x, hB0, LinearMap.zero_apply]

end GlobalTheory.OrbitSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeFieldStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_field : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  first | exact @GlobalTheory.DeRham.ksRegular_of_isAbelianScheme | exact GlobalTheory.DeRham.ksRegular_of_isAbelianScheme | (intros; apply GlobalTheory.DeRham.ksRegular_of_isAbelianScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisRealBasisOfHolomorphicFamilyStatement
section
open GlobalTheory.ShFam.Hor.LogCh

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeBasis_realBasis_of_holomorphic_family : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (b₀ : Fin n → ℂ) (lam : Fin r → Fin g → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ → LinearIndependent ℤ lam → (∀ w, w ∈ K b₀ ↔ ∃ k : Fin r → ℤ, w = ∑ j, k j • lam j) → LinearIndependent ℝ lam ∧ Submodule.span ℝ (Set.range lam) = ⊤ := by
  first | exact @GlobalTheory.LatReal.isRealBasis_of_isLatFam | exact GlobalTheory.LatReal.isRealBasis_of_isLatFam | (intros; apply GlobalTheory.LatReal.isRealBasis_of_isLatFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSecOnto
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow

theorem lbIso_sec_onto : ∀ (X : Scheme.{0}) (A B : LB X) (w : LB.Iso A B), A.IsLB → B.IsLB → w.IsGen →
    ∀ b : B.Sec, ∃ a : A.Sec, SecMaps w a b := by
  intro X A B w hA hB hw b
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfIso b hw hA hB, fun p => ?_⟩
  obtain ⟨p, q⟩ := p
  have hV : B.U p ⊓ A.U q ≤ A.U q ⊓ B.U p := fun _ h => ⟨h.2, h.1⟩
  have e := congrArg (ReciprocityTheory.ChartRestriction.G.DVR.rs hV) (ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec b hw hA hB q p)
  rw [ReciprocityTheory.ChartRestriction.G.DVR.isoCand_rs] at e
  have hs : res (hV.trans (ReciprocityTheory.ChartRestriction.G.DVR.divLe (A := A) (B := B) q p)) (w.s (p, q)) = w.s (p, q) :=
    Units.ext (GlobalTheory.Cartier.resG_self _ _)
  rw [hs] at e
  have e2 : resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) ((ReciprocityTheory.ChartRestriction.G.DVR.secOfIso b hw hA hB).f q) =
      (((w.s (p, q))⁻¹ : Γ(X, B.U p ⊓ A.U q)ˣ) : Γ(X, B.U p ⊓ A.U q)) * resG X inf_le_left (b.f p) := by
    refine Eq.trans ?_ e
    exact (GlobalTheory.Cartier.resG_resG _ _ _).symm
  change resG X inf_le_left (b.f p) = ((@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)ˣ) : Γ(X, B.U p ⊓ A.U q)) * _
  simp only [id]
  rw [e2]
  exact (Units.mul_inv_cancel_left _ _).symm

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthUnitSizeBoundsStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_unit_size_bounds : Size → Lifts fun Fm x _ ι p i PP _ => (lenT p i PP : ℝ) * zBase (Fm.L x ι) ^ 12 ≤ unitE p ∧ 1 ≤ (Fm.L x ι).sc.L ∧ lrd (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ (nCol (dat p i) : ℝ) ≤ 20 * (Fm.D x ι).R.f * (Fm.D x ι).R.r ^ 2 ∧ 1 ≤ (Fm.D x ι).R.f ∧ 1 ≤ (Fm.D x ι).R.r := by
  first | exact @GlobalTheory.RefSum.SizeTZ.sizes | exact GlobalTheory.RefSum.SizeTZ.sizes | (intros; apply GlobalTheory.RefSum.SizeTZ.sizes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelChangeLocallyFiniteType
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

namespace GlobalTheory.FlatModel

theorem locallyOfFiniteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsQProjOver f) : LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have : IsProper (PSpace.str R N) := isProper_str R N
  infer_instance

theorem locallyOfFiniteType_spMap_inclusion {F F' : IntermediateField ℚ ℂ} [FiniteDimensional ℚ F']
    (hle : F ≤ F') : LocallyOfFiniteType (spMap (IntermediateField.inclusion hle).toRingHom) := by
  have h1 : ((IntermediateField.inclusion hle).toRingHom.comp (algebraMap ℚ F)).FiniteType := by
    have : (IntermediateField.inclusion hle).toRingHom.comp (algebraMap ℚ F) = algebraMap ℚ F' :=
      RingHom.ext fun _ => by simp
    rw [this]
    exact (RingHom.Finite.finiteType (RingHom.finite_algebraMap.mpr inferInstance))
  have h2 := RingHom.FiniteType.of_comp_finiteType h1
  exact HasRingHomProperty.Spec_iff.mpr h2

theorem locallyOfFiniteType_of_overIncl : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), GlobalTheory.FlatModel.OverIncl r hle → LocallyOfFiniteType r := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' r hle h
  haveI : FiniteDimensional ℚ c'.F := c'.fin
  haveI := locallyOfFiniteType_of_isQProjOver Xo'.qproj
  haveI := locallyOfFiniteType_spMap_inclusion hle
  haveI : LocallyOfFiniteType (r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    rw [h]; infer_instance
  exact locallyOfFiniteType_of_comp r (pullback.snd _ _)

end GlobalTheory.FlatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentIndexSumEqConst
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

theorem cover_degree_const : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E), (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0 ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ (π k₂) (δ k₂)) → ∃ N : ℕ, 0 < N ∧ ∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ pr δ hπ
  classical
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  letI : Field (CAt σ₂) := inferInstanceAs (Field ℂ)
  letI : IsAlgClosed (CAt σ₂) := inferInstanceAs (IsAlgClosed ℂ)
  have hC := GlobalTheory.T.complexFramedLifts_equiv_movedGroupCosets D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ pr δ hπ
  have hK := GlobalTheory.T.card_framed_lifts_levelCover_const D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂
  have hfin : ∀ k (k₂ : {k₂ // pr k₂ = k}), Finite (↥((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ⧸ (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).subgroupOf ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) := by
    intro k k₂
    have h := (hπ k₂.1).2.2.2.1
    rw [k₂.2] at h
    exact Subgroup.index_ne_zero_iff_finite.1 h
  have hS : ∀ k (x' : ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).dom), (∑ᶠ k₂ : {k₂ // pr k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) = Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} ∧ Finite {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} := by
    intro k x'
    obtain ⟨e⟩ := hC k x'
    haveI := hfin k
    refine ⟨?_, Finite.of_equiv _ e.symm⟩
    rw [Nat.card_congr e, Nat.card_sigma, finsum_eq_sum_of_fintype]
    rfl
  have hne : ∀ y : FrPt Xo c (CAt σ₂), Nonempty {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} := by
    intro y
    obtain ⟨-, -, -, -, -, -, hlift, -, -⟩ := hd
    obtain ⟨y₂, hy₂⟩ := hlift (CAt σ₂) (fun _ => rfl) y
    exact ⟨⟨y₂, hy₂⟩⟩
  by_cases hc : Nonempty (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp
  · obtain ⟨k₀⟩ := hc
    obtain ⟨x₀, hx₀⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k₀)
    refine ⟨Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k₀ ⟨x₀, hx₀⟩)}, ?_, fun k => ?_⟩
    · haveI := (hS k₀ ⟨x₀, hx₀⟩).2
      haveI := hne ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k₀ ⟨x₀, hx₀⟩)
      exact Nat.card_pos
    · obtain ⟨x, hx⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k)
      rw [(hS k ⟨x, hx⟩).1]
      exact hK _ _
  · refine ⟨1, one_pos, fun k => (hc ⟨k⟩).elim⟩

end GlobalTheory.LevModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGeometryWeightBoundStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_geometry_weight_bound : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E), Even G.2 → ∀ (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (AllWt.modelWt (U σ) G k) τ) ≤ w) → ∀ (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r) ∈ AllWt.framesOn (U σ) Z → AllWt.bergOn (U σ) (D.sp.W j) (dict σ) Z G y ≤ ENNReal.ofReal (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d l.M w) := by
  first | exact @GlobalTheory.BergComp.bergOn_le_supConst | exact GlobalTheory.BergComp.bergOn_le_supConst | (intros; apply GlobalTheory.BergComp.bergOn_le_supConst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVectorThreeStepDecompositionStatement
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_vector_three_step_decomposition : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Disjoint Sa St → Sa ∪ St = R.Q t → ∀ (eg ea et : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ gA : WO (Vc D i) (Wc D i) → ℂ, ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) gA ∧ ThAt R i (cA D et) gA (adjDat R i St (R.xiR t) (cA D et)) (R.vP i t) := by
  first | exact @GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition | exact GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition | (intros; apply GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryActionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_witt_model_unitary_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) (locMat t b g) (locMat t c h) (ι φ) := by
  first | exact @GlobalTheory.KSplit.om_linW_split | exact GlobalTheory.KSplit.om_linW_split | (intros; apply GlobalTheory.KSplit.om_linW_split <;> assumption)
end

