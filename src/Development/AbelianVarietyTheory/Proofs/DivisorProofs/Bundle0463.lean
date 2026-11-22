import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0424
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0454
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0420
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarEtaleIntegralClosureRootUniformizerStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abhyankar_etale_integralClosure_root_uniformizer : ∀ (S S₁ K K₁ L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] [Algebra.IsSeparable K L],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L)) := by
  first | (exact @GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer) | (exact GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer) | (intros; apply GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicExtendScalarsZmodOfFlatBoundedBelowStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acyclic_extendScalars_zmod_of_flat_boundedBelow : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (K : Cx (ZMod Q)) (a : ℤ) [K.IsStrictlyGE a], (∀ n, FlatS (K.X n)) → K.Acyclic → (extCx (ZMod.castHom hq (ZMod q)) K).Acyclic := by
  first | exact @GlobalTheory.EtC.flatExtAcyc.main | exact GlobalTheory.EtC.flatExtAcyc.main | (intros; apply GlobalTheory.EtC.flatExtAcyc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfElementThetaCompatibleStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_element_theta_compatible : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ a : Ainf p O, a ≠ 0 → (inA a : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) := by
  first | exact @GlobalTheory.DetInv.inA_mem_nonZeroDivisors | exact GlobalTheory.DetInv.inA_mem_nonZeroDivisors | (intros; apply GlobalTheory.DetInv.inA_mem_nonZeroDivisors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraCoefficientsRestrictionBijectiveStatement
section
open CategoryTheory GlobalTheory.CxCoh GlobalTheory.CatCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebra_coefficients_restriction_bijective : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Bijective (CoefMap.restrict F G).pull1 → Function.Bijective (CoefMap.restrict F G).pull2 → ((Cx.single (Coef.ofAlg F)).resMap G).PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.CxCoh.single_algebra_restriction_bijective | exact GlobalTheory.CxCoh.single_algebra_restriction_bijective | (intros; apply GlobalTheory.CxCoh.single_algebra_restriction_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximationQuotientsAgree
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximation_quotients_agree : ∀ (q : ℕ) (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] (f : B) (I J : Ideal B) (n i : ℤ) (y : Ht q (sp B) n i), IsCoprime I J → (∀ a : A₁, ∃ b : B, a - algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f}) → (∀ b : B, algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f} ↔ b ∈ I) → (∀ a : A₂, ∃ b : B, a - algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f}) → (∀ b : B, algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f} ↔ b ∈ J) → pull _ (spMap (algebraMap B A₁)) _ _ y = 0 → pull _ (spMap (algebraMap B A₂)) _ _ y = 0 → (∀ a : A₁ × A₂, ∃ b : B, a - algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f}) ∧ (∀ b : B, algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f} ↔ b ∈ I ⊓ J) ∧ pull _ (spMap (algebraMap B (A₁ × A₂))) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.ProdStep.prodStep) | (exact GlobalTheory.EtC.ProdStep.prodStep) | (intros; apply GlobalTheory.EtC.ProdStep.prodStep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryChartHodgeMatrix
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem isLocalizationAway_of_le {k L : Type} [Field k] [Field L] [Algebra k L] {A B : Subalgebra k L}
    [Algebra A B] (hab : ∀ a : A, ((algebraMap A B a : B) : L) = a) (s : A) (hs : (s : L) ≠ 0)
    (hsi : (s : L)⁻¹ ∈ B) (hy : ∀ y ∈ B, ∃ N : ℕ, y * (s : L) ^ N ∈ A) : IsLocalization.Away s B := by
  have hu : IsUnit (algebraMap A B s) :=
    isUnit_iff_exists_inv.mpr ⟨⟨(s : L)⁻¹, hsi⟩, Subtype.ext (by simp [hab, hs])⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    simpa using hu.pow n
  · intro z
    obtain ⟨N, hN⟩ := hy z z.2
    exact ⟨(⟨_, hN⟩, ⟨s ^ N, N, rfl⟩), Subtype.ext (by simp [hab])⟩
  · intro a b h
    refine ⟨1, ?_⟩
    have := congrArg (fun z : B => (z : L)) h
    simp only [hab] at this
    simp [Subtype.ext this]

theorem smooth_of_le_away {k L : Type} [Field k] [Field L] [Algebra k L] {A B : Subalgebra k L} (hle : A ≤ B)
    (s : L) (hsA : s ∈ A) (hs : s ≠ 0) (hsi : s⁻¹ ∈ B) (hy : ∀ y ∈ B, ∃ N : ℕ, y * s ^ N ∈ A)
    [Algebra.Smooth k A] : Algebra.Smooth k B := by
  letI : Algebra A B := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization.Away (⟨s, hsA⟩ : A) B := isLocalizationAway_of_le (fun _ => rfl) _ hs hsi hy
  haveI : Algebra.Smooth A B := Algebra.Smooth.of_isLocalization_Away (⟨s, hsA⟩ : A)
  exact Algebra.Smooth.comp k A B

section Parts

variable {k : Type} [Field k] {F K : Type} [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K]
  [IsScalarTower k F K] {d : ℕ} {x : Fin (d + 1) → F}

theorem prod_ratio_ne_zero (h : IsPd k x) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) :
    ∏ j ∈ I, x j / x i ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (h.ne j) (h.ne i)

theorem prod_ratio_mem (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) : ∏ j ∈ I, x j / x i ∈ rA k x {i} :=
  Subalgebra.prod_mem _ fun j _ => Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩

theorem prod_ratio_inv_mem (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) : (∏ j ∈ I, x j / x i)⁻¹ ∈ rA k x I := by
  rw [← Finset.prod_inv_distrib]
  exact Subalgebra.prod_mem _ fun j hj => by
    rw [inv_div]; exact Algebra.subset_adjoin ⟨j, hj, i, rfl⟩

theorem rA_singleton_le {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) : rA k x {i} ≤ rA k x I :=
  Algebra.adjoin_mono fun _ ⟨i', hi', j, hy⟩ => ⟨i', by rw [Finset.mem_singleton.1 hi']; exact hi, j, hy⟩

theorem rA_isIntegrallyClosed (h : IsPd k x) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    IsIntegrallyClosed (rA k x I) := by
  obtain ⟨e, -⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x h i
  haveI : IsIntegrallyClosed (rA k x {i}) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  letI : Algebra (rA k x {i}) (rA k x I) := (Subalgebra.inclusion (rA_singleton_le hi)).toRingHom.toAlgebra
  haveI : IsLocalization.Away (⟨_, prod_ratio_mem I i⟩ : rA k x {i}) (rA k x I) :=
    isLocalizationAway_of_le (fun _ => rfl) _ (prod_ratio_ne_zero h I i) (prod_ratio_inv_mem I i)
      fun y hy => (GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x h I i hi y).1 hy
  exact isIntegrallyClosed_of_isLocalization (rA k x I) (Submonoid.powers (⟨_, prod_ratio_mem I i⟩ : rA k x {i}))
    (powers_le_nonZeroDivisors_of_noZeroDivisors fun h0 => prod_ratio_ne_zero h I i (congrArg Subtype.val h0))

theorem rA_finite (h : IsFinCover k K x) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    Module.Finite (rA k x I) (integralClosure (rA k x I) K) := by
  haveI := h.fin
  haveI := h.sep
  haveI : IsFractionRing (rA k x I) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x h.pd I ⟨i, hi⟩).1
  haveI : IsNoetherianRing (rA k x I) := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x h.pd I ⟨i, hi⟩).2
  haveI := rA_isIntegrallyClosed h.pd hi
  exact IsIntegralClosure.finite (rA k x I) F K (integralClosure (rA k x I) K)

theorem rB_frac (h : IsFinCover k K x) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    IsFractionRing (rB k K x I) K := by
  haveI := h.fin
  haveI : IsFractionRing (rA k x I) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x h.pd I ⟨i, hi⟩).1
  exact integralClosure.isFractionRing_of_finite_extension F K

theorem rB_smooth [CharZero k] (h : IsFinCover k K x) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    Algebra.Smooth k (rB k K x I) := by
  have hleB : rB k K x {i} ≤ rB k K x I :=
    (GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h {i} i (Finset.mem_singleton_self i)).1 I (Finset.singleton_subset_iff.2 hi)
  have hloc := (GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h I i hi).2
  have hsB : algebraMap F K (∏ j ∈ I, x j / x i) ∈ rB k K x {i} :=
    (integralClosure (rA k x {i}) K).algebraMap_mem ⟨_, prod_ratio_mem I i⟩
  have hsiB : (algebraMap F K (∏ j ∈ I, x j / x i))⁻¹ ∈ rB k K x I := by
    rw [← map_inv₀]; exact (integralClosure (rA k x I) K).algebraMap_mem ⟨_, prod_ratio_inv_mem I i⟩
  haveI := h.smooth i
  exact smooth_of_le_away hleB _ hsB ((map_ne_zero _).2 (prod_ratio_ne_zero h.pd I i)) hsiB fun y hy => (hloc y).1 hy

end Parts

theorem rB_finite_frac_smooth : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    ∀ I : Finset (Fin (d + 1)), I.Nonempty → Module.Finite (rA k x I) (integralClosure (rA k x I) K) ∧
      IsFractionRing (rB k K x I) K ∧ Algebra.Smooth k (rB k K x I) := by
  intro k _ _ F K _ _ _ _ _ _ d x h I hI
  obtain ⟨i, hi⟩ := hI
  exact ⟨rA_finite h hi, rB_frac h hi, rB_smooth h hi⟩

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧ Function.Injective (Sec.map (resι R F) (U := U)) ∧ (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k → Sec.map ((res R F).d n k) z = 0 → Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧ ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U) := by
  first | (exact @GlobalTheory.EtC.resSec) | (exact GlobalTheory.EtC.resSec) | (intros; apply GlobalTheory.EtC.resSec  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRingClassOrderUnitsEqMaxRealSubfieldUnits
section
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.OrderUnits

theorem prime_not_mem_sq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (w : HeightOneSpectrum (𝓞 E)) (hv : (p : 𝓞 E) ∈ w.asIdeal) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  obtain ⟨P, hP, hP0⟩ := w
  have he : P.ramificationIdx ℤ = 1 := by
    have h1 := (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) (Nat.prime_iff_prime_int.mp hp)).1 hd P hP (by simpa using hv)
    have := hP.isMaximal hP0
    have : (P.under ℤ).IsMaximal := inferInstance
    have hne : P.under ℤ ≠ ⊥ := by
      intro h0
      have h1 : (p : ℤ) ∈ P.under ℤ := by rw [Ideal.under_def, Ideal.mem_comap]; simpa using hv
      rw [h0] at h1
      exact hp.ne_zero (by simpa using h1)
    have : Finite (ℤ ⧸ P.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    have : Finite (P.under ℤ).ResidueField := inferInstance
    exact Ideal.ramificationIdx_eq_one_iff.2 h1
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hb] at he
  intro h2
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h2

theorem pow_first_order {R : Type} [CommRing R] (t : R) (i : ℕ) : ∃ r, (1 + t) ^ i = 1 + i * t + t ^ 2 * r := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨r + i + t * r, by rw [pow_succ, hr]; push_cast; ring⟩

theorem geom_first_order {R : Type} [CommRing R] (t : R) (n : ℕ) :
    ∃ r, ∑ i ∈ Finset.range n, (1 + t) ^ i = n + (n.choose 2 : ℕ) * t + t ^ 2 * r := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨s, hs⟩ := pow_first_order t n
    refine ⟨r + s, ?_⟩
    rw [Finset.sum_range_succ, hr, hs, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    push_cast; ring

theorem root_of_unity_eq_one {R : Type} [CommRing R] [IsDomain R] {P : Ideal R} (hP : P ≠ ⊤) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hlP : (l : R) ∈ P) (hlP2 : (l : R) ∉ P ^ 2) {ζ : R} (hζ : IsOfFinOrder ζ) (h1 : ζ - 1 ∈ P) : ζ = 1 := by
  by_contra hne
  have hn : orderOf ζ ≠ 1 := fun h => hne (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hp, m, hm⟩ := Nat.exists_prime_and_dvd hn
  have hpos := hζ.orderOf_pos
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp [hm] at hpos)
  have hη1 : ζ ^ m ≠ 1 := pow_ne_one_of_lt_orderOf hm0.ne' (by rw [hm]; nlinarith [hp.two_le])
  have hηp : (ζ ^ m) ^ p = 1 := by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  have ht : ζ ^ m - 1 ∈ P := by
    obtain ⟨s, hs⟩ := sub_one_dvd_pow_sub_one ζ m
    rw [hs]; exact P.mul_mem_right _ h1
  have hsum : ∑ i ∈ Finset.range p, (ζ ^ m) ^ i = 0 := by
    have := mul_geom_sum (ζ ^ m) p
    rw [hηp, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hη1)
  obtain ⟨r, hr⟩ := geom_first_order (ζ ^ m - 1) p
  rw [add_sub_cancel, hsum] at hr
  set t := ζ ^ m - 1
  have hpe : (p : R) = -((p.choose 2 : ℕ) * t) - t ^ 2 * r := by linear_combination -hr
  have hpP : (p : R) ∈ P := by
    rw [hpe]
    exact sub_mem (neg_mem (P.mul_mem_left _ ht)) (P.mul_mem_right _ (P.pow_mem_of_mem ht 2 two_pos))
  have hpl : p = l := by
    by_contra h
    have hc : IsCoprime (p : R) (l : R) := Nat.Coprime.cast ((Nat.coprime_primes hp hl).2 h)
    obtain ⟨a, b, hab⟩ := hc
    exact hP ((Ideal.eq_top_iff_one P).2 (hab ▸ add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hlP)))
  subst hpl
  obtain ⟨k, hk⟩ := hp.dvd_choose_self two_ne_zero (lt_of_le_of_ne hp.two_le (Ne.symm hl2))
  apply hlP2
  rw [hpe, hk]
  refine sub_mem (neg_mem ?_) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ht 2))
  rw [sq]
  push_cast
  exact Ideal.mul_mem_mul (P.mul_mem_right _ hlP) ht

theorem orderC_units (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (hc : 𝔣 ∣ c)
    (x : E) (hx0 : x ≠ 0) (hx : x ∈ orderC c) (hx' : x⁻¹ ∈ orderC c) : ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u := by
  obtain ⟨h0, h1, h⟩ := h𝔣
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal 𝔣 h1
  have hM0 : M ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hle))
  obtain ⟨⟨P, -, -, hP, -⟩, -, l, hl, hl2, hlv, hd, -⟩ := h ⟨M, hM.isPrime, hM0⟩ (Ideal.dvd_iff_le.2 hle)
  have hP' : P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) = M := hP
  have hlP : (l : 𝓞 E) ∈ P.asIdeal := by
    have : (l : OF E) ∈ P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) := by rw [hP']; exact hlv
    simpa using this
  have hcP : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.2 (hP' ▸ (Ideal.le_of_dvd hc).trans hle)
  obtain ⟨a, b, hb, hab⟩ := mem_orderC.1 hx
  obtain ⟨a', b', -, hab'⟩ := mem_orderC.1 hx'
  have e1 : x = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by rw [hab, map_add]; rfl
  have e2 : x⁻¹ = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a' + b') := by rw [hab', map_add]; rfl
  have hu : (algebraMap (OF E) (𝓞 E) a + b) * (algebraMap (OF E) (𝓞 E) a' + b') = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_mul, ← e1, ← e2, mul_inv_cancel₀ hx0, map_one]
  let u : (𝓞 E)ˣ := Units.mkOfMulEqOne _ _ hu
  have huv : (u : 𝓞 E) = algebraMap (OF E) (𝓞 E) a + b := rfl
  have hbc : IsCMField.ringOfIntegersComplexConj E b ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    have : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤
        (Ideal.map (algebraMap (OF E) (𝓞 E)) c).comap (IsCMField.ringOfIntegersComplexConj E) := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgEquiv.commutes]
      exact Ideal.mem_map_of_mem _ hy
    exact this hb
  have hcu : ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E) =
      algebraMap (OF E) (𝓞 E) a + IsCMField.ringOfIntegersComplexConj E b := by
    have : ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E) = IsCMField.ringOfIntegersComplexConj E u := rfl
    rw [this, huv, map_add, AlgEquiv.commutes]
  let ζ : (𝓞 E)ˣ := u * (IsCMField.unitsComplexConj E u)⁻¹
  have hfin : IsOfFinOrder ζ := (IsCMField.unitsMulComplexConjInv E u).2
  have hfin' : IsOfFinOrder (ζ : 𝓞 E) := (Units.coeHom (𝓞 E)).isOfFinOrder hfin
  have hζ : (ζ : 𝓞 E) - 1 ∈ P.asIdeal := by
    have : (ζ : 𝓞 E) - 1 = (b - IsCMField.ringOfIntegersComplexConj E b) * ↑(IsCMField.unitsComplexConj E u)⁻¹ := by
      have h3 := (IsCMField.unitsComplexConj E u).mul_inv
      rw [hcu] at h3
      simp only [ζ, Units.val_mul, huv]
      linear_combination h3
    rw [this]
    exact P.asIdeal.mul_mem_right _ (hcP (sub_mem hb hbc))
  have hone : ζ = 1 := Units.ext (root_of_unity_eq_one P.isPrime.ne_top hl hl2 hlP (prime_not_mem_sq hl hd P hlP) hfin' hζ)
  have hreal := (IsCMField.unitsComplexConj_eq_self_iff E u).1 (mul_inv_eq_one.1 hone).symm
  obtain ⟨v, hv⟩ := (IsCMField.mem_realUnits_iff E u).1 hreal
  refine ⟨v, ?_⟩
  rw [e1, ← huv, ← hv]
  rfl

end GlobalTheory.CMVal.OrderUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeTraceImaginaryPart
section
open NumberField GlobalTheory.CMVal
open scoped ComplexConjugate

namespace GlobalTheory

theorem cmType_trace_im_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (h : I → ℝ) (mu : E), (∀ z : E, ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) = ∑ i, h i * (φ i z).im) →
    ∀ i, 2 * Complex.I * φ i mu = (h i : ℂ) := by
  intro E _ _ _ I _ φ hφ h mu hmu i0
  classical
  let ψ : I ⊕ I → (E →+* ℂ) := fun k => Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)) k
  have hnr : ∀ i, φ i ≠ ComplexEmbedding.conjugate (φ i) := by
    intro i hi
    exact IsTotallyComplex.complexEmbedding_not_isReal (φ i) (ComplexEmbedding.isReal_iff.mpr hi.symm)
  have hinj : Function.Injective ψ := by
    rintro (i | i) (j | j) hij <;> simp only [ψ, Sum.elim_inl, Sum.elim_inr] at hij
    · obtain ⟨k, -, hk⟩ := hφ (φ i)
      rw [(hk i (Or.inl rfl)).trans (hk j (Or.inl hij)).symm]
    · obtain ⟨k, -, hk⟩ := hφ (φ i)
      have e := (hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm
      subst e; exact absurd hij (hnr i)
    · obtain ⟨k, -, hk⟩ := hφ (φ j)
      have e := (hk j (Or.inl rfl)).trans (hk i (Or.inr hij.symm)).symm
      subst e; exact absurd hij.symm (hnr j)
    · obtain ⟨k, -, hk⟩ := hφ (ComplexEmbedding.conjugate (φ i))
      rw [(hk i (Or.inr rfl)).trans (hk j (Or.inr hij)).symm]
  have hsurj : Function.Surjective ψ := by
    intro σ
    obtain ⟨k, hk, -⟩ := hφ σ
    rcases hk with hk | hk
    · exact ⟨Sum.inl k, hk.symm⟩
    · exact ⟨Sum.inr k, hk.symm⟩
  let e : I ⊕ I ≃ (E →+* ℂ) := Equiv.ofBijective ψ ⟨hinj, hsurj⟩
  have htr : ∀ x : E, ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ k, ψ k x := by
    intro x
    have h0 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
    rw [eq_ratCast] at h0
    rw [h0, ← Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ => σ x) (fun f => f x)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])]
    exact (Fintype.sum_equiv e (fun k => ψ k x) (fun σ => σ x) (fun _ => rfl)).symm
  let c : I ⊕ I → ℂ := Sum.elim (fun i => φ i mu - (h i : ℂ) / (2 * Complex.I))
    (fun i => conj (φ i mu) + (h i : ℂ) / (2 * Complex.I))
  have hz : ∀ z, ∑ k, c k * ψ k z = 0 := by
    intro z
    have h2 : ((Algebra.trace ℚ E (mu * z) : ℚ) : ℂ) =
        ∑ i, (h i : ℂ) * ((φ i z - conj (φ i z)) / (2 * Complex.I)) := by
      have h3 := congrArg (fun r : ℝ => (r : ℂ)) (hmu z)
      simp only [Complex.ofReal_ratCast, Complex.ofReal_sum, Complex.ofReal_mul] at h3
      rw [h3]
      simp_rw [Complex.im_eq_sub_conj]
    rw [htr (mu * z)] at h2
    simp only [Fintype.sum_sum_type, ψ, c, Sum.elim_inl, Sum.elim_inr, map_mul,
      ComplexEmbedding.conjugate_coe_eq] at h2 ⊢
    rw [← Finset.sum_add_distrib] at h2 ⊢
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hli : LinearIndependent ℂ (fun k => ((ψ k).toMonoidHom : E → ℂ)) := by
    refine (linearIndependent_monoidHom E ℂ).comp (fun k => (ψ k).toMonoidHom) ?_
    intro a b hab
    apply hinj
    ext x
    exact DFunLike.congr_fun hab x
  have hc := Fintype.linearIndependent_iff.mp hli c (by
    funext z
    simpa [Finset.sum_apply, smul_eq_mul] using hz z) (Sum.inl i0)
  simp only [c, Sum.elim_inl, sub_eq_zero] at hc
  have h2I : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  rw [hc, mul_div_cancel₀ _ h2I]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoalternatingExactOfFiniteTypeIsoFilteredColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

noncomputable def coAugNat {J : Type} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{0}) :
    (D ⋙ Arrow.leftFunc) ⋙ CosimplicialObject.const CommRingCat.{0} ⟶ D ⋙ CosimplicialObject.cechConerve where
  app j := coAug (D.obj j).hom
  naturality i j f := by
    have h := (CosimplicialObject.augmentedCechConerve.map (D.map f)).w
    exact h

theorem wExact_of_finiteType_iso (N M : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M)
    (hN : PreservesFilteredColimitsOfSize.{0, 0} N)
    (hε : ∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A))
    (hM : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact M (coAug g)) :
    ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact N (coAug g) := by
  intro A B g hg
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, hD⟩ := GlobalTheory.T.etaleFaithfullyFlat_filtered_colimit_finiteType A B g hg
  obtain ⟨⟨hU⟩, hX⟩ := GlobalTheory.EtC.isColimit_leftFunc_and_cechConerve_levels J D _ hc
  refine GlobalTheory.EtC.WExactColim.wExact_colimit CommRingCat.{0} N hN J (D ⋙ Arrow.leftFunc)
    (D ⋙ CosimplicialObject.cechConerve) (coAugNat D) (Arrow.leftFunc.mapCocone (Cocone.mk (Arrow.mk g) ι))
    (CosimplicialObject.cechConerve.mapCocone (Cocone.mk (Arrow.mk g) ι)) (coAug g) hU (fun k => hX k) ?_ ?_
  · intro j
    have h := (CosimplicialObject.augmentedCechConerve.map (ι.app j)).w
    exact h.symm
  · intro j
    obtain ⟨hj, hl, hr⟩ := hD j
    refine (GlobalTheory.EtC.wExact_congr CommRingCat.{0} _ _ (coAug (D.obj j).hom) N M ε (hε _ hl) (fun k => hε _ ?_)).2
      (hM _ _ _ hj)
    exact GlobalTheory.cechConerve_obj_finiteType_int _ _ (D.obj j).hom hr k

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleLocalSectionsRestrictCompatiblyStatement
section
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_local_sections_restrict_compatibly : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)), (∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a)) → ∀ (T : TT s) (p q : Pair (pt T)) (hpq : p ≤ q), Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) (hSec f g T q) = hSec f g T p := by
  first | exact @GlobalTheory.CechDR.AffLoc.hSec_res | exact GlobalTheory.CechDR.AffLoc.hSec_res | (intros; apply GlobalTheory.CechDR.AffLoc.hSec_res <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientsAcyclicOfTwoSectionsRetractionStatement
section
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction : ∀ (C : Type 1) [Category.{0} C] (M : Coef C) (S : C ⥤ C) (u v : 𝟭 C ⟶ S) (r : ∀ T, M.obj (S.obj T) →+ M.obj T), (∀ (T T' : C) (φ : T ⟶ T') x, r T' (M.map (S.map φ) x) = M.map φ (r T x)) → (∀ T x, r T (M.map (u.app T) x) = 0) → (∀ T x, r T (M.map (v.app T) x) = x) → M.Ac0 ∧ M.Ac1 ∧ M.Ac2 := by
  first | exact @GlobalTheory.coef_acyclic_of_two_sections | exact GlobalTheory.coef_acyclic_of_two_sections | (intros; apply GlobalTheory.coef_acyclic_of_two_sections <;> assumption)
end

