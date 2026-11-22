import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0008
import ReciprocityTheory.SemistableReduction.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValPlRes

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional
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

theorem KTtoS_fieldRange (h : d.S1) (c : ι) :
    (d.KTtoS h c).fieldRange = (d.KT c).toSubfield := by
  have hval : ∀ p : (KTp K d.D d.N), d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p) =
      MvPolynomial.aeval (sImg (d.jc c) (d.x c)) p := by
    intro p
    simp only [KTtoS]
    rw [IsFractionRing.lift_algebraMap]
    rfl
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := (KTp K d.D d.N)) z
    have hmem : ∀ p : (KTp K d.D d.N), d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p) ∈ (d.KT c).toSubfield := by
      intro p
      rw [hval]
      show _ ∈ IntermediateField.adjoin K (Set.range (sImg (d.jc c) (d.x c)))
      apply IntermediateField.algebra_adjoin_le_adjoin
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨p, rfl⟩
    rw [map_div₀]
    exact (d.KT c).toSubfield.div_mem (hmem a) (hmem b)
  · intro y hy
    have hE : IntermediateField.adjoin K (Set.range (sImg (d.jc c) (d.x c))) ≤
        { (d.KTtoS h c).fieldRange with
          algebraMap_mem' := fun k => (d.KTtoS h c).mem_fieldRange.2
            ⟨algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C k), by rw [hval, MvPolynomial.aeval_C]⟩ } := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨v, rfl⟩
      exact (d.KTtoS h c).mem_fieldRange.2
        ⟨algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.X v), by rw [hval, MvPolynomial.aeval_X]⟩
    exact hE hy

theorem KT_finiteDimensional (hd : d.AxH 𝒜) (c : ι) :
    FiniteDimensional (d.KT c) (OmS (Ω c) d.D d.N) := by
  have hfs := ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K (Ω c) d.D d.N (d.x c) (hd.fg c) (hd.trdeg c) (hd.a1 c)
  let e : TVar d.D d.N ≃ TVar d.D d.N :=
    Equiv.prodCongr (Equiv.refl _) (Fin.cycleRange (d.jc c)).symm
  have key : (ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c)) = (sImg (D := d.D) (d.jc c) (d.x c)) ∘ e := by
    funext p
    obtain ⟨i, j⟩ := p
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_zero]
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_succ]
  have hrange : Set.range (ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c)) =
      Set.range (sImg (D := d.D) (d.jc c) (d.x c)) := by
    rw [key, EquivLike.range_comp]
  have h2 := hfs.2
  rw [hrange] at h2
  exact h2

theorem omS_finite (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      Module.finrank (KTf K d.D d.N) (OmS (Ω c) d.D d.N) = d.delc c := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI := d.KT_finiteDimensional hd c
  have hfr := d.KTtoS_fieldRange h c
  let e : (KTf K d.D d.N) ≃+* (d.KT c) :=
    ((d.KTtoS h c).rangeRestrictFieldEquiv).trans (RingEquiv.subfieldCongr hfr)
  have he : ∀ z, ((e z : d.KT c) : (OmS (Ω c) d.D d.N)) = d.KTtoS h c z := fun z => rfl
  have hc : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp e.symm.toRingHom =
      (RingEquiv.refl (OmS (Ω c) d.D d.N)).toRingHom.comp (algebraMap (d.KT c) (OmS (Ω c) d.D d.N)) := by
    refine RingHom.ext fun y => ?_
    show d.KTtoS h c (e.symm y) = (y : (OmS (Ω c) d.D d.N))
    rw [← he, RingEquiv.apply_symm_apply]
  refine ⟨Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl _) hc, ?_⟩
  rw [show d.delc c = Module.finrank (d.KT c) (OmS (Ω c) d.D d.N) from rfl]
  exact (Algebra.finrank_eq_of_equiv_equiv e.symm (RingEquiv.refl _) hc).symm

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValNorm
section
namespace ReciprocityTheory.ChartRestriction.G.T0

namespace ValPl

open IsDedekindDomain IsLocalRing

variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]

variable (O F L) in

noncomputable def hoEquiv : HeightOneSpectrum (integralClosure O L) ≃
    {Q : Ideal (integralClosure O L) // Q.IsMaximal} where
  toFun v := ⟨v.asIdeal, v.isMaximal⟩
  invFun Q := (exists_heightOne O F L Q.1 Q.2).choose
  left_inv v := by
    apply HeightOneSpectrum.ext
    exact (exists_heightOne O F L v.asIdeal v.isMaximal).choose_spec
  right_inv Q := Subtype.ext (exists_heightOne O F L Q.1 Q.2).choose_spec

include F in

theorem norm_integral (b : integralClosure O L) (hb : b ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F (algebraMap (integralClosure O L) L b) = algebraMap O F
        (ϖ ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O *
          Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})))
          * u) := by
  haveI : Module.Finite O (integralClosure O L) :=
    IsIntegralClosure.finite O F L (integralClosure O L)
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  have hinjB : Function.Injective (algebraMap O (integralClosure O L)) := by
    intro x y hxy
    apply hinj
    rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L x,
      IsScalarTower.algebraMap_apply O (integralClosure O L) L y, hxy]
  haveI : NoZeroSMulDivisors O (integralClosure O L) := by
    refine ⟨fun {c x} h => ?_⟩
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left (fun h' => hinjB (h'.trans (map_zero _).symm))
  have hN := ReciprocityTheory.MultiplicativeHeights.Closed.normOrd O (integralClosure O L) b hb
  have hne : Algebra.norm O b ≠ 0 := by
    intro h0
    rw [h0, IsDiscreteValuationRing.addVal_zero] at hN
    exact ENat.top_ne_coe _ hN
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hn := IsDiscreteValuationRing.addVal_def _ u hϖ n hu
  rw [hn] at hN
  have hnN : n = ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}, Q.1.inertiaDeg O *
      Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
    exact_mod_cast hN
  have hsum : (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O *
      Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) = n := by
    rw [hnN]
    exact finsum_comp_equiv (hoEquiv O F L)
      (f := fun Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal} => Q.1.inertiaDeg O *
        Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})))
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure O L) (nonZeroDivisors O)) L :=
    IsIntegralClosure.isLocalization O F L (integralClosure O L)
  refine ⟨u, u.isUnit, ?_⟩
  rw [Algebra.norm_localization O (nonZeroDivisors O) b, hu, hsum, mul_comm (u : O)]

theorem norm_eq_heightOne (y : L) (hy : y ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F y = (algebraMap O F ϖ) ^
        (∑ᶠ v : HeightOneSpectrum (integralClosure O L),
          (v.asIdeal.inertiaDeg O : ℤ) * WithTop.untopD 0 (addv L v y)) * algebraMap O F u := by
  haveI : Finite (HeightOneSpectrum (integralClosure O L)) := by
    have hinj : Function.Injective (algebraMap O L) := by
      rw [IsScalarTower.algebraMap_eq O F L]
      exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
    obtain ⟨b, hbdef⟩ : ∃ b : (integralClosure O L), b = algebraMap O (integralClosure O L) ϖ := ⟨_, rfl⟩
    have hbL : algebraMap (integralClosure O L) L b = algebraMap O L ϖ := by
      rw [hbdef]
      exact (IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ).symm
    have hb : b ≠ 0 := by
      intro h0
      have h00 : algebraMap O L ϖ = 0 := by rw [← hbL, h0, map_zero]
      exact hϖ.ne_zero (hinj (h00.trans (map_zero _).symm))
    have hmem : ϖ ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
    have hdvd : ∀ v : HeightOneSpectrum (integralClosure O L), v.asIdeal ∣ Ideal.span {b} := by
      intro v
      have h1 := ((addv_mem_placesOver (O := O) (L := L) v).2 ϖ).2.2 hmem
      rw [← hbL, addv_count v b hb] at h1
      have h2 : 0 < Multiset.count v.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
        rcases Nat.eq_zero_or_pos (Multiset.count v.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) with h | h
        · rw [h, Nat.cast_zero] at h1
          exact absurd h1 (lt_irrefl 0)
        · exact h
      exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.count_pos.1 h2)
    have hspan : Ideal.span {b} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hb
    have hfin := Ideal.finite_factors hspan
    have huniv : {v : HeightOneSpectrum (integralClosure O L) | v.asIdeal ∣ Ideal.span {b}} = Set.univ :=
      Set.eq_univ_of_forall hdvd
    rw [huniv] at hfin
    exact Set.finite_univ_iff.1 hfin
  haveI := Fintype.ofFinite (HeightOneSpectrum (integralClosure O L))
  obtain ⟨b1, b2, hb2m, hyb⟩ := IsFractionRing.div_surjective (A := (integralClosure O L)) y
  have hb2 : b2 ≠ 0 := nonZeroDivisors.ne_zero hb2m
  have hb1 : b1 ≠ 0 := by
    intro h
    apply hy
    rw [← hyb, h, map_zero, zero_div]
  have hb2L : algebraMap (integralClosure O L) L b2 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosure O L) L)).2 hb2
  have hyb2 : y * algebraMap (integralClosure O L) L b2 = algebraMap (integralClosure O L) L b1 := by
    rw [← hyb, div_mul_cancel₀ _ hb2L]
  have ha : algebraMap O F ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O F)).2 hϖ.ne_zero
  obtain ⟨u1, hu1, h1⟩ := norm_integral (F := F) b1 hb1 hϖ
  obtain ⟨u2, hu2, h2⟩ := norm_integral (F := F) b2 hb2 hϖ
  have hmul : Algebra.norm F y * Algebra.norm F (algebraMap (integralClosure O L) L b2) =
      Algebra.norm F (algebraMap (integralClosure O L) L b1) := by
    rw [← map_mul, hyb2]
  rw [h1, h2] at hmul
  simp only [map_mul, map_pow] at hmul
  have hk : ∀ v : HeightOneSpectrum (integralClosure O L),
      WithTop.untopD 0 (addv L v y) = ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1})) : ℕ) : ℤ) - ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2})) : ℕ) : ℤ) := by
    intro v
    have hm := (addv L v).map_mul y (algebraMap (integralClosure O L) L b2)
    rw [hyb2, addv_count v b1 hb1, addv_count v b2 hb2] at hm
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (mt (addv L v).top_iff.1 hy)
    rw [← hk] at hm ⊢
    have hm' : ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1})) : ℕ) : ℤ) = k + ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2})) : ℕ) : ℤ) := by
      exact_mod_cast hm
    rw [WithTop.untopD_coe]
    omega
  have hz : (∑ᶠ v : HeightOneSpectrum (integralClosure O L),
      (v.asIdeal.inertiaDeg O : ℤ) * WithTop.untopD 0 (addv L v y)) =
        (((∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1}))) : ℕ) : ℤ) - (((∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) : ℕ) : ℤ) := by
    simp only [hk]
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  refine ⟨u1 * ((hu2.unit⁻¹ : Oˣ) : O), hu1.mul (hu2.unit⁻¹).isUnit, ?_⟩
  have hU : algebraMap O F u2 * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, hu2.mul_val_inv, map_one]
  have haS : (algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) ≠ 0 := pow_ne_zero _ ha
  rw [hz, zpow_sub₀ ha, zpow_natCast, zpow_natCast, map_mul]
  calc Algebra.norm F y
      = Algebra.norm F y * ((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) * algebraMap O F u2) *
          (((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))))⁻¹ * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O)) := by
        rw [mul_assoc, mul_mul_mul_comm, mul_inv_cancel₀ haS, hU, one_mul, mul_one]
    _ = (algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1}))) * algebraMap O F u1 *
          (((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))))⁻¹ * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O)) := by
        rw [hmul]
    _ = _ := by
        rw [div_eq_mul_inv]
        ring

theorem norm_eq_places (y : L) (hy : y ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F y = (algebraMap O F ϖ) ^
        (∑ᶠ (w : AddValuation L (WithTop ℤ)) (_ : w ∈ PlacesOver O L),
          (letI := resAlg (F := F) w
           (Module.finrank (ResidueField ((vRing w).comap (algebraMap F L)))
             (ResidueField (vRing w)) : ℤ)) * WithTop.untopD 0 (w y)) * algebraMap O F u := by
  obtain ⟨u, hu, h⟩ := norm_eq_heightOne (F := F) y hy hϖ
  refine ⟨u, hu, ?_⟩
  rw [h]
  congr 2
  obtain ⟨e, he⟩ := placesOver_bij (O := O) (F := F) (L := L)
  rw [← finsum_set_coe_eq_finsum_mem, ← finsum_comp_equiv e]
  apply finsum_congr
  intro v
  rw [he v]
  congr 1
  exact congrArg (fun n : ℕ => (n : ℤ)) (resDeg_addv (F := F) v).symm

variable (O L) in
include F in

theorem placesOver_finite : (PlacesOver O L).Finite := by
  obtain ⟨e, -⟩ := placesOver_bij (O := O) (F := F) (L := L)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  obtain ⟨b, hbdef⟩ : ∃ b : integralClosure O L, b = algebraMap O (integralClosure O L) ϖ :=
    ⟨_, rfl⟩
  have hbL : algebraMap (integralClosure O L) L b = algebraMap O L ϖ := by
    rw [hbdef]
    exact (IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ).symm
  have hb : b ≠ 0 := by
    intro h0
    have h00 : algebraMap O L ϖ = 0 := by rw [← hbL, h0, map_zero]
    exact hϖ.ne_zero (hinj (h00.trans (map_zero _).symm))
  have hmem : ϖ ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  have hdvd : ∀ v : HeightOneSpectrum (integralClosure O L), v.asIdeal ∣ Ideal.span {b} := by
    intro v
    have h1 := ((addv_mem_placesOver (O := O) (L := L) v).2 ϖ).2.2 hmem
    rw [← hbL, addv_count v b hb] at h1
    have h2 : 0 < Multiset.count v.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
      rcases Nat.eq_zero_or_pos (Multiset.count v.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) with h | h
      · rw [h, Nat.cast_zero] at h1
        exact absurd h1 (lt_irrefl 0)
      · exact h
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.count_pos.1 h2)
  have hspan : Ideal.span {b} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hb
  have hfin := Ideal.finite_factors hspan
  have hfin' : Finite (HeightOneSpectrum (integralClosure O L)) := by
    have huniv : {v : HeightOneSpectrum (integralClosure O L) | v.asIdeal ∣ Ideal.span {b}} =
        Set.univ := Set.eq_univ_of_forall hdvd
    rw [huniv] at hfin
    exact Set.finite_univ_iff.1 hfin
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ e)

end ValPl

end ReciprocityTheory.ChartRestriction.G.T0
end

