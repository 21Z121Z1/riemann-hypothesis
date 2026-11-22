import Mathlib
import GroundTheory.GlobalFields.Artin.ConductorInflation
import GroundTheory.GlobalFields.Artin.OneDim
import GroundTheory.LocalFields.ArtinConductorMax
import GroundTheory.LocalFields.SeparableClosure
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
import GroundTheory.GlobalFields.Artin.Bundle0004

-- bundled from GroundTheory.GlobalFields.Artin.ConductorOneDim
section
noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

open IdeleGroup

section LocalConductor

variable {k M : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra k M] [ValuativeExtension k M] [FiniteDimensional k M] [IsGalois k M]

theorem artinConductor_charRep_eq_sInf (ψ : (M ≃ₐ[k] M) →* ℂˣ) (hψ : Function.Injective ψ) :
    artinConductor (charRep ψ) =
      (sInf {n : ℕ | unitFiltrationUnits k n ≤ (normUnits k M).range} : ℕ) := by
  let ι : M →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let M' : IntermediateField k (SeparableClosure k) := ι.fieldRange
  let e : M ≃ₐ[k] M' := AlgEquiv.ofInjectiveField ι
  have : FiniteDimensional k M' := LinearEquiv.finiteDimensional e.toLinearEquiv
  have : IsGalois k M' := IsGalois.of_algEquiv e
  have hcomm : IsMulCommutative (M' ≃ₐ[k] M') :=
    ⟨⟨fun a b ↦ e.autCongr.symm.injective (hψ (by rw [map_mul, map_mul, map_mul, map_mul,
      mul_comm]))⟩⟩
  have : IsAbelianGalois k M' := {}
  let ψ' : (M' ≃ₐ[k] M') →* ℂˣ := ψ.comp e.autCongr.symm.toMonoidHom
  have hψ' : Function.Injective ψ' := hψ.comp e.autCongr.symm.injective
  have h1 := artinConductor_charRep_eq_conductor M' ψ' hψ'
  have h2 : artinConductor (charRep ψ) = artinConductor (charRep ψ') := by
    apply Rat.cast_injective (α := ℂ)
    rw [artinConductor_eq_charArtinConductor, artinConductor_eq_charArtinConductor,
      ← charArtinConductor_autCongr e]
    congr 1
    funext σ
    rw [character_charRep, character_charRep]
    show ((ψ σ : ℂˣ) : ℂ) = ψ (e.autCongr.symm (e.autCongr σ))
    rw [MulEquiv.symm_apply_apply]
  have h3 : (normUnits k M').range = (normUnits k M).range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨Units.map e.symm.toMonoidHom y, Units.ext ?_⟩
      simp only [coe_normUnits, Units.coe_map]
      rw [← Algebra.norm_eq_of_algEquiv e]
      simp
    · rintro ⟨y, rfl⟩
      refine ⟨Units.map e.toMonoidHom y, Units.ext ?_⟩
      simp only [coe_normUnits, Units.coe_map]
      exact Algebra.norm_eq_of_algEquiv e _
  rw [h2, h1, GroundTheory.LocalField.conductor, h3]

end LocalConductor

section Units

open ValuativeRel

variable {K : Type*} [Field K] [NumberField K]

theorem unitFiltrationUnits_eq_unitsLevel (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    unitFiltrationUnits (v.adicCompletion K) n = unitsLevel v n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact unitFiltrationUnits_zero_eq_unitsLevel_zero v
  ext x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  rw [mem_unitFiltrationUnits_iff hn hϖ, mem_unitsLevel_of_one_le hn, ← map_pow,
    (isEquiv_valuation_valued v).le_iff_le, map_pow, valued_irreducible_valuationInteger v hϖ,
    ← WithZero.exp_nsmul]
  simp

end Units

section OneDim

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

theorem charRep_eq_comp_restrictNormalHom :
    charRep χ = (charRep (charBar χ)).comp (AlgEquiv.restrictNormalHom (charField χ)) := by
  ext g
  simp [charRep_apply, charBar_restrictNormalHom]

theorem artinExponent_charRep (v : HeightOneSpectrum (𝓞 K)) :
    artinExponent v (charRep χ) = localConductorExponent (charField χ) v := by
  rw [charRep_eq_comp_restrictNormalHom, artinExponent_comp_restrictNormalHom]
  let u := placeAbove (L := charField χ) v
  have hinj : Function.Injective ((charBar χ).comp (localToGlobal v u)) :=
    (charBar_injective χ).comp (Subtype.val_injective.comp (decompositionMulEquiv v u).symm.injective)
  have h := artinExponent_eq v (charRep (charBar χ)) u
  rw [localArtinConductor] at h
  change _ = artinConductor (charRep ((charBar χ).comp (localToGlobal v u))) at h
  rw [artinConductor_charRep_eq_sInf _ hinj] at h
  have h' := Nat.cast_injective (R := ℚ) h
  rw [h', localConductorExponent, ker_localSymbol (charField χ) v ⟨u, inferInstance⟩]
  simp_rw [unitFiltrationUnits_eq_unitsLevel]

theorem conductorExponentAt_heckeCharacterOfChar (v : HeightOneSpectrum (𝓞 K)) :
    conductorExponentAt ((heckeCharacterOfChar χ).toIdele.comp ofFinite) v =
      localConductorExponent (charField χ) v := by
  have h : ((heckeCharacterOfChar χ).toIdele.comp ofFinite).comp (finiteUnitsSingle v) =
      ((heckeCharacterOfChar χ).localComponent v : (v.adicCompletion K)ˣ →* Circle) := by
    ext a
    simp only [MonoidHom.comp_apply, ofFinite_finiteUnitsSingle]
    rfl
  rw [conductorExponentAt, conductorExponent, h, ker_localComponent_heckeCharacterOfChar]
  rfl

theorem artinConductorIdeal_charRep_eq_conductor :
    artinConductorIdeal (charRep χ) = (heckeCharacterOfChar χ).conductor :=
  finprod_congr fun v ↦ by
    rw [artinExponent_charRep, ← conductorExponentAt_heckeCharacterOfChar]

end OneDim

end GroundTheory.Global
end
end

-- bundled from GroundTheory.GlobalFields.Artin.OneDimExistence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField

noncomputable section

section FiniteOrder

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

theorem isOfFinOrder_heckeCharacterOfChar : IsOfFinOrder (heckeCharacterOfChar χ) := by
  refine isOfFinOrder_iff_pow_eq_one.2
    ⟨Nat.card (charField χ ≃ₐ[K] charField χ), Nat.card_pos, ContinuousMonoidHom.ext fun c ↦ ?_⟩
  rw [ContinuousMonoidHom.pow_apply]
  change toCircleHom (charBar χ) (reciprocityMap K (charField χ) c) ^ _ = 1
  rw [← map_pow, pow_card_eq_one', map_one]

end FiniteOrder

section Existence

universe u

variable {K : Type u} [Field K] [NumberField K]

theorem exists_heckeCharacterOfChar_eq (ψ : HeckeCharacter K) (hψ : IsOfFinOrder ψ) :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L)
      (χ : Gal(L/K) →* ℂˣ), Function.Injective χ ∧ heckeCharacterOfChar χ = ψ := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hψ
  have hval : ∀ c, ψ c ^ n = 1 := fun c ↦ by
    rw [← ContinuousMonoidHom.pow_apply, hpow]
    rfl
  set f : IdeleClassGroup K →* Circle := ψ.toMonoidHom with hf

  have hS : {z : Circle | z ^ n = 1}.Finite := by
    refine Set.Finite.of_finite_image ?_ Circle.coe_injective.injOn
    refine (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset ?_
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ^ n = 1 := hz
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn, ← Circle.coe_pow, hz',
      Circle.coe_one]

  have hopen : IsOpen (f.ker : Set (IdeleClassGroup K)) := by
    have hU : IsOpen (({z : Circle | z ^ n = 1} \ {1})ᶜ) :=
      (hS.sdiff).isClosed.isOpen_compl
    have hker : (f.ker : Set (IdeleClassGroup K)) = ψ ⁻¹' ({z : Circle | z ^ n = 1} \ {1})ᶜ := by
      ext c
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and, not_not]
      exact ⟨fun h _ ↦ h, fun h ↦ h (hval c)⟩
    rw [hker]
    exact hU.preimage ψ.continuous

  have : Finite f.range :=
    (hS.subset (by rintro _ ⟨c, rfl⟩; exact hval c)).to_subtype
  obtain ⟨L, _, _, _, hab, hL⟩ :=
    exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex f.ker hopen

  let χ : Gal(L/K) →* ℂˣ := Circle.toUnits.comp
    ((QuotientGroup.lift _ f hL.le).comp (reciprocityMapEquiv K L).symm.toMonoidHom)
  have hχ : ∀ c, χ (reciprocityMap K L c) = Circle.toUnits (ψ c) := by
    intro c
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
    simp only [χ, MonoidHom.comp_apply, reciprocityMap_mk, MulEquiv.coe_toMonoidHom,
      ← reciprocityMapEquiv_mk, MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]
    rfl
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    obtain ⟨c, rfl⟩ := reciprocityMap_surjective (K := K) (L := L) σ
    rw [hχ, ← map_one Circle.toUnits] at hσ
    have hc : c ∈ f.ker := unitSphereToUnits_injective hσ
    rw [← hL, ← ker_reciprocityMap] at hc
    exact hc
  refine ⟨L, inferInstance, inferInstance, inferInstance, hab, χ, hinj,
    ContinuousMonoidHom.ext fun c ↦ Circle.ext ?_⟩
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [heckeCharacterOfChar_apply, reciprocityMap_mk,
    ← restrictNormal_ideleSymbol (charField χ) L x]
  change ((charBar χ (AlgEquiv.restrictNormalHom (charField χ) (ideleSymbol K L x)) : ℂˣ) : ℂ) = _
  rw [charBar_restrictNormalHom, ← reciprocityMap_mk, hχ]
  rfl

end Existence

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.Artin.OneDimL
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField

noncomputable section

section Average

variable {G : Type*} [Group G]

open Classical in

theorem cosetAverage_character (I : Subgroup G) [Finite I] (χ : G →* ℂˣ) (g : G) :
    cosetAverage I (fun x ↦ (χ x : ℂ)) g = if ∀ i ∈ I, χ i = 1 then (χ g : ℂ) else 0 := by
  have := Fintype.ofFinite I
  rw [cosetAverage_eq_sum]
  simp only [map_mul, Units.val_mul]
  rw [← Finset.mul_sum]
  split_ifs with h
  · have hs : ∑ i : I, ((χ i : ℂˣ) : ℂ) = Nat.card I := by
      rw [Finset.sum_congr rfl fun i _ ↦ by rw [h i i.2, Units.val_one], Finset.sum_const,
        Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]
    have hI : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [hs, mul_left_comm, inv_mul_cancel₀ hI, mul_one]
  · let ψ : I →* ℂ := (Units.coeHom ℂ).comp (χ.comp I.subtype)
    have hψ : ψ ≠ 1 := by
      intro h1
      apply h
      intro i hi
      have := DFunLike.congr_fun h1 ⟨i, hi⟩
      exact Units.val_eq_one.1 this
    have hs : ∑ i : I, ((χ i : ℂˣ) : ℂ) = 0 := sum_hom_units_eq_zero ψ hψ
    rw [hs, mul_zero, mul_zero]

end Average

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

open Classical in

theorem artinLocalLog_character (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    artinLocalLog K L (fun g ↦ (χ g : ℂ)) s v =
      if ∀ σ ∈ (placeAbove (L := L) v).asIdeal.inertia Gal(L/K), χ σ = 1 then
        -Complex.log (1 - χ (arithFrobAt (𝓞 K) Gal(L/K) (placeAbove (L := L) v).asIdeal) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
      else 0 := by
  have hterm : ∀ m, artinTerm K L (fun g ↦ (χ g : ℂ)) s v m =
      if ∀ σ ∈ (placeAbove (L := L) v).asIdeal.inertia Gal(L/K), χ σ = 1 then
        (χ (arithFrobAt (𝓞 K) Gal(L/K) (placeAbove (L := L) v).asIdeal) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ m / m
      else 0 := fun m ↦ by
    rw [artinTerm, localAverage, cosetAverage_character]
    split_ifs
    · rw [map_pow, Units.val_pow_eq_pow_val, mul_pow]
    · rw [zero_mul, zero_div]
  rw [artinLocalLog, tsum_congr hterm]
  split_ifs
  · refine (Complex.hasSum_taylorSeries_neg_log ?_).tsum_eq
    rw [norm_mul, norm_coe_apply_eq_one, one_mul]
    exact norm_absNorm_cpow_neg_lt_one v hs
  · exact tsum_zero

theorem artinL_eq_LFunction {s : ℂ} (hs : 1 < s.re) :
    artinL K L (fun g ↦ (χ g : ℂ)) s = (heckeCharacterOfChar χ).LFunction s := by
  have h1 : HasProd (Complex.exp ∘ fun v ↦ artinLocalLog K L (fun g ↦ (χ g : ℂ)) s v)
      (artinL K L (fun g ↦ (χ g : ℂ)) s) :=
    (hasSum_artinLocalLog_artinLogL _ hs).cexp
  refine h1.unique ?_
  convert (heckeCharacterOfChar χ).LFunction_hasProd_all hs using 1
  funext v
  rw [Function.comp_apply, artinLocalLog_character χ v hs]
  set w := placeAbove (L := L) v
  split_ifs with hχ
  · have hv := (not_dvd_conductor_heckeCharacterOfChar_iff χ v w).2 hχ
    obtain ⟨π, -, hπ⟩ := exists_ord_eq_one_valued v
    have hc : (heckeCharacterOfChar χ).coeff v.asIdeal =
        χ (arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal) := by
      rw [HeckeCharacter.coeff_asIdeal_of_not_dvd _ hv,
        HeckeCharacter.idealCharacter_primeIdealUnit _ hv hπ,
        localComponent_uniformizer χ v w hχ hπ (IsArithFrobAt.arithFrobAt _ _ _)]
    have hne : 1 - (χ (arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal) : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) ≠ 0 := by
      intro h
      have h2 : ‖(χ (arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal) : ℂ) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
        rw [norm_mul, norm_coe_apply_eq_one, one_mul]
        exact norm_absNorm_cpow_neg_lt_one v hs
      rw [← sub_eq_zero.1 h, norm_one] at h2
      exact lt_irrefl _ h2
    rw [hc, Complex.exp_neg, Complex.exp_log hne]
  · have hv : v.asIdeal ∣ (heckeCharacterOfChar χ).conductor :=
      not_not.1 fun h ↦ hχ ((not_dvd_conductor_heckeCharacterOfChar_iff χ v w).1 h)
    rw [HeckeCharacter.coeff_asIdeal_of_dvd _ hv, zero_mul, sub_zero, inv_one, Complex.exp_zero]

end

end GroundTheory.Global
end

