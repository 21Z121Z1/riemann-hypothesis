import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.SemistableReduction.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0006
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAC
section
namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HDiscVal

open IsDedekindDomain WithZero ValPl

variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]

variable (O F) in
include F in

theorem addv_eq_of_mem {w : AddValuation L (WithTop ℤ)} (hw : w ∈ PlacesOver O L) :
    ∃ v : HeightOneSpectrum (integralClosure O L), w = addv L v := by
  obtain ⟨e, he⟩ := placesOver_bij O F L
  refine ⟨e.symm ⟨w, hw⟩, ?_⟩
  rw [← he, Equiv.apply_symm_apply]

variable (O F) in
include F in
theorem addv_mem (v : HeightOneSpectrum (integralClosure O L)) : addv L v ∈ PlacesOver O L := by
  have hval : ∀ y : L, y ≠ 0 →
      addv L v y = ((-WithZero.log (v.valuation L y) : ℤ) : WithTop ℤ) := by
    intro y hy
    unfold addv
    rw [AddValuation.of_apply, if_neg hy]
  have hP : v.asIdeal.comap (algebraMap O (integralClosure O L)) = IsLocalRing.maximalIdeal O := by
    haveI := v.isMaximal
    apply IsLocalRing.eq_maximalIdeal
    first
      | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
      | exact Ideal.IsMaximal.under O v.asIdeal
      | infer_instance
  simp only [PlacesOver, IsNormDiscrete, Set.mem_setOf_eq]
  refine ⟨⟨fun a ha => ?_, ?_⟩, fun x => ?_⟩
  · rw [hval a ha]
    exact WithTop.coe_ne_top
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact absurd hπ.symm (by simp)
    refine ⟨π, ?_⟩
    rw [hval π hπ0, hπ]
    first
      | simp
      | rfl
  · have hx : algebraMap O L x =
        algebraMap (integralClosure O L) L (algebraMap O (integralClosure O L) x) :=
      IsScalarTower.algebraMap_apply O (integralClosure O L) L x
    by_cases hx0 : algebraMap O L x = 0
    · have hx00 : x = 0 := by
        have h1 : algebraMap O F x = 0 := by
          apply (algebraMap F L).injective
          rw [← IsScalarTower.algebraMap_apply, map_zero]
          exact hx0
        exact IsFractionRing.injective O F (by rw [h1, map_zero])
      subst hx00
      simp
    · rw [hval _ hx0]
      have hv : v.valuation L (algebraMap O L x) ≠ 0 := by simpa using hx0
      have hle := WithZero.log_le_log hv one_ne_zero
      have hge := WithZero.log_le_log one_ne_zero hv
      rw [WithZero.log_one] at hle hge
      have hmem : v.valuation L (algebraMap O L x) < 1 ↔
          algebraMap O (integralClosure O L) x ∈ v.asIdeal := by
        rw [hx]
        first
          | exact v.valuation_lt_one_iff_mem _
          | exact v.valuation_lt_one_iff_mem L _
      have hint : v.valuation L (algebraMap O L x) ≤ 1 := by
        rw [hx]
        first
          | exact v.valuation_le_one _
          | exact v.valuation_le_one L _
      rw [← hP, Ideal.mem_comap, ← hmem]
      constructor
      · have h3 := hle.2 hint
        exact_mod_cast (show (0 : ℤ) ≤ -WithZero.log (v.valuation L (algebraMap O L x)) by omega)
      · constructor
        · intro h
          have h' : (0 : ℤ) < -WithZero.log (v.valuation L (algebraMap O L x)) := by
            exact_mod_cast h
          refine lt_of_le_of_ne hint (fun he => ?_)
          rw [he, WithZero.log_one] at h'
          omega
        · intro h
          have h1 : ¬ (0 ≤ WithZero.log (v.valuation L (algebraMap O L x))) :=
            fun h0 => (not_le.2 h) (hge.1 h0)
          have h2 : (0 : ℤ) < -WithZero.log (v.valuation L (algebraMap O L x)) := by omega
          exact_mod_cast h2

omit [IsFractionRing O F] [FiniteDimensional F L] [Algebra.IsSeparable F L] [IsScalarTower O F L] in

theorem addv_nonneg_iff (v : HeightOneSpectrum (integralClosure O L)) {y : L} (hy : y ≠ 0) :
    0 ≤ addv L v y ↔ v.valuation L y ≤ 1 := by
  have hv : v.valuation L y ≠ 0 := by simpa using hy
  have hval : addv L v y = ((-WithZero.log (v.valuation L y) : ℤ) : WithTop ℤ) := by
    unfold addv
    rw [AddValuation.of_apply, if_neg hy]
  rw [hval]
  have h2 := WithZero.log_le_log hv one_ne_zero
  rw [WithZero.log_one] at h2
  constructor
  · intro h
    have h' : (0 : ℤ) ≤ -WithZero.log (v.valuation L y) := by exact_mod_cast h
    exact h2.1 (by omega)
  · intro h
    have h' := h2.2 h
    have h'' : (0 : ℤ) ≤ -WithZero.log (v.valuation L y) := by omega
    exact_mod_cast h''

variable (O F) in
include F in
theorem mem_integralClosure_iff (y : L) :
    y ∈ integralClosure O L ↔ ∀ w ∈ PlacesOver O L, 0 ≤ w y := by
  constructor
  · intro hy w hw
    obtain ⟨v, rfl⟩ := addv_eq_of_mem O F hw
    by_cases hy0 : y = 0
    · subst hy0
      rw [AddValuation.map_zero]
      exact le_top
    · rw [addv_nonneg_iff v hy0]
      first
        | exact v.valuation_le_one (⟨y, hy⟩ : integralClosure O L)
        | exact v.valuation_le_one L (⟨y, hy⟩ : integralClosure O L)
  · intro h
    by_cases hy0 : y = 0
    · subst hy0
      exact Subalgebra.zero_mem _
    · have hle : ∀ v : HeightOneSpectrum (integralClosure O L), v.valuation L y ≤ 1 :=
        fun v => (addv_nonneg_iff v hy0).1 (h _ (addv_mem O F v))
      have hr : y ∈ (algebraMap (integralClosure O L) L).range := by
        first
          | exact HeightOneSpectrum.mem_integers_of_valuation_le_one L y hle
          | exact HeightOneSpectrum.mem_integers_of_valuation_le_one y hle
      obtain ⟨b, hb⟩ := hr
      rw [← hb]
      exact b.2

variable (O F) in
include F in

theorem exists_val_eq (n : AddValuation L (WithTop ℤ) → ℤ) :
    ∃ g : L, g ≠ 0 ∧ ∀ w ∈ PlacesOver O L, w g = n w := by
  classical
  obtain ⟨_, _, _, _, hmax, _⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F L
  haveI : IsPrincipalIdealRing (integralClosure O L) := IsPrincipalIdealRing.of_finite_maximals hmax
  haveI := hmax.to_subtype
  haveI : Finite (HeightOneSpectrum (integralClosure O L)) := by
    refine Finite.of_injective (fun v => (⟨v.asIdeal, v.isMaximal⟩ :
      {I : Ideal (integralClosure O L) | I.IsMaximal})) ?_
    intro v v' h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)
  letI := Fintype.ofFinite (HeightOneSpectrum (integralClosure O L))
  let π : HeightOneSpectrum (integralClosure O L) → integralClosure O L := fun v =>
    Submodule.IsPrincipal.generator v.asIdeal
  have hπ : ∀ v, v.asIdeal = Ideal.span {π v} := fun v =>
    (Ideal.span_singleton_generator v.asIdeal).symm
  have hπ0 : ∀ v, π v ≠ 0 := fun v h => v.ne_bot (by rw [hπ v, Ideal.span_singleton_eq_bot.mpr h])
  have hπL : ∀ v, algebraMap (integralClosure O L) L (π v) ≠ 0 := fun v =>
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosure O L) L)).mpr (hπ0 v)
  have hval : ∀ v v' : HeightOneSpectrum (integralClosure O L),
      v'.valuation L (algebraMap _ L (π v)) = if v' = v then exp (-1 : ℤ) else 1 := by
    intro v v'
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    split_ifs with h
    · subst h
      exact HeightOneSpectrum.intValuation_singleton _ (hπ0 v') (hπ v')
    · apply le_antisymm (v'.intValuation_le_one _)
      rw [← not_lt, v'.intValuation_lt_one_iff_mem]
      intro hmem
      apply h
      have hle : v.asIdeal ≤ v'.asIdeal := by
        rw [hπ v, Ideal.span_singleton_le_iff_mem]
        exact hmem
      exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle).symm
  let g : L := ∏ v, (algebraMap _ L (π v)) ^ (n (addv L v))
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (hπL v)
  have hgv : ∀ v' : HeightOneSpectrum (integralClosure O L), v'.valuation L g = exp (-(n (addv L v'))) := by
    intro v'
    simp only [g, map_prod, map_zpow₀, hval]
    rw [Finset.prod_eq_single v']
    · rw [if_pos rfl, ← exp_zsmul, smul_eq_mul, mul_neg_one]
    · intro v _ hv
      rw [if_neg (Ne.symm hv), one_zpow]
    · simp
  refine ⟨g, hg0, fun w hw => ?_⟩
  obtain ⟨v, rfl⟩ := addv_eq_of_mem O F hw
  rw [addv_apply v hg0, hgv, log_exp, neg_neg]

end HDiscVal

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAD
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsDedekindDomain

section
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)

noncomputable abbrev algOTKT : Algebra (OT K D N) (KTf K D N) :=
  ((algebraMap (KTp K D N) (KTf K D N)).comp (OTtoKT K D N)).toAlgebra

noncomputable abbrev algOpKT (la : HeightOneSpectrum (𝓞 K)) : Algebra (Op D N la) (KTf K D N) :=
  (OpToKT D N la).toAlgebra

theorem isFractionRing_OT :
    letI := algOTKT (K := K) D N
    IsFractionRing (OT K D N) (KTf K D N) := by
  letI := algOTKT (K := K) D N
  have hinj : Function.Injective (algebraMap (OT K D N) (KTf K D N)) :=
    (IsFractionRing.injective (KTp K D N) (KTf K D N)).comp
      (MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K))
  haveI : FaithfulSMul (OT K D N) (KTf K D N) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (KTp K D N) z
  letI : Algebra (OT K D N) (KTp K D N) := MvPolynomial.algebraMvPolynomial
  haveI := MvPolynomial.isLocalization (σ := TVar D N) (nonZeroDivisors (𝓞 K)) K
  obtain ⟨⟨P, ⟨_, a, ha, rfl⟩⟩, hP⟩ :=
    IsLocalization.surj ((nonZeroDivisors (𝓞 K)).map (MvPolynomial.C (σ := TVar D N))) p
  obtain ⟨⟨Q, ⟨_, b, hb, rfl⟩⟩, hQ⟩ :=
    IsLocalization.surj ((nonZeroDivisors (𝓞 K)).map (MvPolynomial.C (σ := TVar D N))) q
  refine ⟨P * MvPolynomial.C b, Q * MvPolynomial.C a, ?_⟩
  have e : ∀ X : OT K D N, algebraMap (OT K D N) (KTf K D N) X =
      algebraMap (KTp K D N) (KTf K D N) (algebraMap (OT K D N) (KTp K D N) X) := fun X => rfl
  have hC : ∀ c ∈ nonZeroDivisors (𝓞 K),
      algebraMap (KTp K D N) (KTf K D N) (algebraMap (OT K D N) (KTp K D N) (MvPolynomial.C c)) ≠ 0 := by
    intro c hc
    rw [← e]
    exact (map_ne_zero_iff _ hinj).mpr (by
      rw [Ne, MvPolynomial.C_eq_zero]; exact nonZeroDivisors.ne_zero hc)
  have hq0 : algebraMap (KTp K D N) (KTf K D N) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K D N) (KTf K D N))).mpr
      (nonZeroDivisors.ne_zero hq)
  simp only at hP hQ
  rw [e, e, map_mul, map_mul, map_mul, map_mul, ← hP, ← hQ, map_mul, map_mul]
  have ha := hC a ha
  have hb := hC b hb
  field_simp

theorem isFractionRing_Op (la : HeightOneSpectrum (𝓞 K)) :
    letI := algOpKT (K := K) D N la
    IsFractionRing (Op D N la) (KTf K D N) := by
  letI := algOTKT (K := K) D N
  letI := algOpKT (K := K) D N la
  haveI := isFractionRing_OT (K := K) D N
  haveI : IsScalarTower (OT K D N) (Op D N la) (KTf K D N) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = OpToKT D N la (algebraMap _ _ x)
      rw [OpToKT, IsLocalization.lift_eq]
      rfl
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (laT D N la).primeCompl
    (Op D N la) (KTf K D N)

theorem OpToKT_injective (la : HeightOneSpectrum (𝓞 K)) : Function.Injective (OpToKT D N la) := by
  letI := algOpKT (K := K) D N la
  haveI := isFractionRing_Op (K := K) D N la
  exact IsFractionRing.injective (Op D N la) (KTf K D N)

omit [NumberField K] in
theorem unif_mem [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    (Data.unif la : 𝓞 K) ∈ la.asIdeal ∧ (Data.unif la : 𝓞 K) ∉ la.asIdeal ^ 2 := by
  have hex : ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 := by
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    refine ⟨π, ?_, ?_⟩
    · rw [← la.intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    · rw [← la.intValuation_le_pow_iff_mem, hπ, WithZero.exp_le_exp]
      norm_num
  rw [Data.unif, dif_pos hex]
  exact hex.choose_spec

noncomputable def unifOp (la : HeightOneSpectrum (𝓞 K)) : Op D N la :=
  algebraMap (OT K D N) (Op D N la) (MvPolynomial.C (Data.unif la))

theorem unifOp_irreducible (la : HeightOneSpectrum (𝓞 K)) : Irreducible (unifOp D N la) := by
  classical
  haveI := Op_isDVR (K := K) D N la
  obtain ⟨hmem, hnot⟩ := unif_mem la
  have hinj : Function.Injective (algebraMap (OT K D N) (Op D N la)) :=
    IsLocalization.injective (Op D N la) (laT D N la).primeCompl_le_nonZeroDivisors
  have hne : unifOp D N la ≠ 0 := by
    intro h
    have h0 : MvPolynomial.C (Data.unif la) = (0 : OT K D N) := hinj (h.trans (map_zero _).symm)
    rw [MvPolynomial.C_eq_zero] at h0
    exact hnot (h0 ▸ zero_mem _)
  have hmax : unifOp D N la ∈ IsLocalRing.maximalIdeal (Op D N la) := by
    rw [unifOp, IsLocalization.AtPrime.to_map_mem_maximal_iff (Op D N la) (laT D N la)]
    exact Ideal.mem_map_of_mem _ hmem
  have hnu : ¬ IsUnit (unifOp D N la) := (IsLocalRing.mem_maximalIdeal _).mp hmax
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Op D N la)
  obtain ⟨j, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (Op D N la) := (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  rcases j with _ | _ | j
  · exact absurd (by rw [hu, pow_zero, mul_one]; exact u.isUnit) hnu
  · rw [hu, pow_one]
    exact (irreducible_isUnit_mul u.isUnit).mpr hϖ
  · exfalso
    have h2 : unifOp D N la ∈ (IsLocalRing.maximalIdeal (Op D N la)) ^ 2 := by
      have hpow : (u : Op D N la) * ϖ ^ (j + 1 + 1) = (u * ϖ ^ j) * (ϖ * ϖ) := by ring
      rw [hu, hpow, pow_two]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hϖm hϖm)
    have hL2 : laT D N la ^ 2 = Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) (la.asIdeal ^ 2) := by
      unfold laT
      rw [Ideal.map_pow]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow, hL2,
      IsLocalization.mem_map_algebraMap_iff (laT D N la).primeCompl (Op D N la)] at h2
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hx⟩ := h2
    simp only [unifOp, ← map_mul] at hx
    have hx' := hinj hx
    rw [← hx', MvPolynomial.mem_map_C_iff] at ha
    have hs' : s ∉ Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) la.asIdeal := hs
    rw [MvPolynomial.mem_map_C_iff, not_forall] at hs'
    obtain ⟨mm, hmm⟩ := hs'
    have h3 := ha mm
    rw [MvPolynomial.coeff_C_mul] at h3
    have v1 : la.intValuation (Data.unif la) = la.intValuation (Data.unif la) * la.intValuation (MvPolynomial.coeff mm s) := by
      have : la.intValuation (MvPolynomial.coeff mm s) = 1 := by
        apply le_antisymm (la.intValuation_le_one _)
        rw [← not_lt, la.intValuation_lt_one_iff_mem]
        exact hmm
      rw [this, mul_one]
    have h4 : la.intValuation (Data.unif la) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
      rw [v1, ← map_mul]
      exact (la.intValuation_le_pow_iff_mem _ 2).mpr h3
    exact hnot ((la.intValuation_le_pow_iff_mem _ 2).mp h4)

theorem algK_unif (la : HeightOneSpectrum (𝓞 K)) :
    algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K) = OpToKT D N la (unifOp D N la) := by
  rw [unifOp, OpToKT, IsLocalization.lift_eq, RingHom.comp_apply, OTtoKT, MvPolynomial.map_C,
    IsScalarTower.algebraMap_apply K (KTp K D N) (KTf K D N), MvPolynomial.algebraMap_eq]

theorem exp_unique (la : HeightOneSpectrum (𝓞 K)) {m m' : ℤ} {u u' : Op D N la} (hu : IsUnit u)
    (hu' : IsUnit u')
    (h : (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m * OpToKT D N la u =
      (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m' * OpToKT D N la u') : m = m' := by
  have key : ∀ {m m' : ℤ} {u u' : Op D N la}, IsUnit u → IsUnit u' →
      (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m * OpToKT D N la u =
        (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m' * OpToKT D N la u' → m ≤ m' := by
    intro m m' u u' hu hu' h
    by_contra hlt
    push_neg at hlt
    have hϖ0 : algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K) ≠ 0 := by
      rw [algK_unif]
      exact (map_ne_zero_iff _ (OpToKT_injective D N la)).mpr (unifOp_irreducible D N la).ne_zero
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = m' + (k + 1 : ℕ) := ⟨(m - m' - 1).toNat, by omega⟩
    rw [hk, zpow_add₀ hϖ0, mul_assoc] at h
    have h' := mul_left_cancel₀ (zpow_ne_zero m' hϖ0) h
    rw [zpow_natCast, algK_unif, ← map_pow, ← map_mul] at h'
    have h'' := OpToKT_injective D N la h'
    have hunit : IsUnit (unifOp D N la ^ (k + 1) * u) := h'' ▸ hu'
    have := isUnit_of_mul_isUnit_left hunit
    exact (unifOp_irreducible D N la).not_isUnit ((isUnit_pow_iff (Nat.succ_ne_zero k)).mp this)
  exact le_antisymm (key hu hu' h) (key hu' hu h.symm)

end

namespace Data

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

theorem gOrd_eq (d : Data K ι Ω WT A) (la : HeightOneSpectrum (𝓞 K)) {q : KTf K d.D d.N} {m : ℤ}
    {u : Op d.D d.N la} (hu : IsUnit u)
    (hq : q = (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ m * OpToKT d.D d.N la u) :
    d.gOrd la q = m := by
  classical
  have hex : ∃ m : ℤ, ∃ u : Op d.D d.N la, IsUnit u ∧
      q = (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ m * OpToKT d.D d.N la u :=
    ⟨m, u, hu, hq⟩
  rw [gOrd, dif_pos hex]
  obtain ⟨u', hu', hq'⟩ := hex.choose_spec
  exact exp_unique d.D d.N la hu' hu (hq'.symm.trans hq)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def fDivE (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N :=
  ∏ c, ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p

noncomputable def omE (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N := d.De hd h * d.fDivE hd h ^ 2

def IsPres (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) : Prop :=
  b ≠ 0 ∧ algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a =
    d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ∧
  ∃ m : Fin (d.D + 1) → ℕ, m 0 = 0 ∧ ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m a ∧
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m b

noncomputable def mSgP (sg : K →+* ℂ) (a b : KTp K d.D d.N) : ℝ :=
  ∫ z, (Real.log ‖d.evT sg 0 (d.tOf z) a‖ - Real.log ‖d.evT sg 0 (d.tOf z) b‖)
    ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegHor
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem reg_horizontal {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    (P : Ideal A) [P.IsPrime] (hh : ¬ Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P)
    (hmeet : P ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) (e : A) (he : e ≠ 0)
    (f : FractionRing A)
    (hdvr : (¬ ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) →
      ∃ a s : A, a ∈ P ∧ s ∉ P ∧ f⁻¹ * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  exact reg_horizontal_pf P hh hmeet e he f hdvr hf

end ReciprocityTheory.ChartRestriction.G.T0
end

