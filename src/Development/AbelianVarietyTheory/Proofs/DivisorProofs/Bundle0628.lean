import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0416
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVector
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

namespace GlobalTheory.FlatFibreRegular

theorem exists_minimal_generators {A : Type} [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime] (I : Ideal A)
    (hI : I.FG) :
    ∃ S : Finset A, (↑S ⊆ (I : Set A)) ∧ (∀ x ∈ I, ∃ s ∉ 𝔭, s * x ∈ Ideal.span (S : Set A)) ∧
      ∀ c : S → A, ∑ i, c i * (i : A) = 0 → ∀ i, c i ∈ 𝔭 := by
  classical
  let P : Finset A → Prop := fun S =>
    (↑S ⊆ (I : Set A)) ∧ ∀ x ∈ I, ∃ s ∉ 𝔭, s * x ∈ Ideal.span (S : Set A)
  have hex : ∃ n, ∃ S : Finset A, S.card = n ∧ P S := by
    obtain ⟨S, hS⟩ := hI
    refine ⟨S.card, S, rfl, fun a ha => ?_, fun x hx => ⟨1, ?_, ?_⟩⟩
    · rw [← hS]; exact Ideal.subset_span ha
    · exact fun h => (Ideal.IsPrime.ne_top' (I := 𝔭)) ((Ideal.eq_top_iff_one _).2 h)
    · rw [one_mul, hS]; exact hx
  obtain ⟨S, hcard, hSI, hSgen⟩ := Nat.find_spec hex
  refine ⟨S, hSI, hSgen, fun c hc k => ?_⟩
  by_contra hk
  have hlt : (S.erase k).card < Nat.find hex := by
    rw [← hcard]; exact Finset.card_erase_lt_of_mem k.2
  apply Nat.find_min hex hlt
  refine ⟨S.erase k, rfl, fun x hx => hSI (Finset.mem_of_mem_erase hx), fun x hx => ?_⟩
  obtain ⟨s, hs, hsx⟩ := hSgen x hx
  refine ⟨c k * s, fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hk hs), ?_⟩
  have key : Ideal.span (S : Set A) ≤
      Submodule.comap (LinearMap.mulLeft A (c k)) (Ideal.span ((S.erase k : Finset A) : Set A)) := by
    rw [Ideal.span_le]
    intro a ha
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    by_cases hak : a = k
    · rw [hak]
      have h1 := Finset.add_sum_erase Finset.univ (fun i : S => c i * (i : A)) (Finset.mem_univ k)
      rw [hc] at h1
      rw [eq_neg_of_add_eq_zero_left h1]
      refine neg_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      exact Finset.mem_erase.2 ⟨fun h => hik (Subtype.ext h), i.2⟩
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_erase.2 ⟨hak, ha⟩))
  have := key hsx
  simpa [mul_assoc] using this

theorem mem_map_mul_of_mul_mem {A L : Type} [CommRing A] [CommRing L] [Algebra A L] [Module.Flat A L]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s))
    (g : L) (hg : ∀ y, g * y ∈ 𝔭.map (algebraMap A L) → y ∈ 𝔭.map (algebraMap A L))
    (I : Ideal A) (hI : I.FG) (y : L) (hy : y ∈ I.map (algebraMap A L))
    (hgy : g * y ∈ (I * 𝔭).map (algebraMap A L)) : y ∈ (I * 𝔭).map (algebraMap A L) := by
  classical
  obtain ⟨S, hSI, hSgen, hrel⟩ := exists_minimal_generators 𝔭 I hI
  set J := 𝔭.map (algebraMap A L) with hJdef
  let v : S → L := fun i => algebraMap A L i
  have hspan : I.map (algebraMap A L) ≤ Ideal.span (Set.range v) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨s, hs, hsx⟩ := hSgen x hx
    have h1 : algebraMap A L (s * x) ∈ Ideal.span (Set.range v) := by
      have : Ideal.map (algebraMap A L) (Ideal.span (S : Set A)) ≤ Ideal.span (Set.range v) := by
        rw [Ideal.map_span]
        apply Ideal.span_mono
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
      exact this (Ideal.mem_map_of_mem _ hsx)
    rw [map_mul] at h1
    obtain ⟨t, ht⟩ := (hu s hs).exists_left_inv
    have := Ideal.mul_mem_left _ t h1
    rwa [← mul_assoc, ht, one_mul] at this
  have hvI : ∀ i, v i ∈ I.map (algebraMap A L) := fun i => Ideal.mem_map_of_mem _ (hSI i.2)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 (hspan hy)
  have hgy' : g * y ∈ J • Ideal.span (Set.range v) := by
    have h1 : (I * 𝔭).map (algebraMap A L) ≤ J • Ideal.span (Set.range v) := by
      rw [Ideal.smul_eq_mul, Ideal.map_mul, mul_comm]
      exact Ideal.mul_mono_right hspan
    exact h1 hgy
  obtain ⟨w, hwJ, hw⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum J v _).1 hgy'
  rw [Finsupp.sum_fintype _ _ (by simp)] at hw
  have hrel0 : ∑ i : S, (i : A) • (g * c i - w i) = 0 := by
    have e1 : ∑ i : S, (i : A) • (g * c i) = g * y := by
      rw [← hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [smul_eq_mul, v]; simp only [Algebra.smul_def]; ring
    have e2 : ∑ i : S, (i : A) • w i = g * y := by
      rw [← hw]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [smul_eq_mul, v]; simp only [Algebra.smul_def]; ring
    simp only [smul_sub, Finset.sum_sub_distrib, e1, e2, sub_self]
  obtain ⟨k, a, z, hx, hf⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := L)
    (f := fun i : S => (i : A)) (x := fun i => g * c i - w i) hrel0
  have ha : ∀ i j, a i j ∈ 𝔭 := fun i j =>
    hrel (fun i => a i j) (by rw [← hf j]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _) i
  have hcJ : ∀ i, c i ∈ J := by
    intro i
    apply hg
    have h1 : g * c i - w i ∈ J := by
      have hxi := hx i
      dsimp only at hxi
      rw [hxi]
      exact Ideal.sum_mem _ fun j _ => by
        rw [Algebra.smul_def]; exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ha i j))
    simpa using Ideal.add_mem _ h1 (hwJ i)
  rw [← hc, Ideal.map_mul]
  exact Ideal.sum_mem _ fun i _ => by
    rw [smul_eq_mul, mul_comm (c i)]; exact Ideal.mul_mem_mul (hvI i) (hcJ i)

theorem eq_zero_of_mul_eq_zero {A L : Type} [CommRing A] [IsNoetherianRing A] [CommRing L]
    [IsLocalRing L] [IsNoetherianRing L] [Algebra A L] [Module.Flat A L]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s))
    (hJ : 𝔭.map (algebraMap A L) ≠ ⊤)
    (g : L) (hg : ∀ y, g * y ∈ 𝔭.map (algebraMap A L) → y ∈ 𝔭.map (algebraMap A L))
    (y : L) (hgy : g * y = 0) : y = 0 := by
  have hn : ∀ n : ℕ, y ∈ (𝔭 ^ n).map (algebraMap A L) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; exact Submodule.mem_top
    | succ n ih =>
      rw [pow_succ]
      exact mem_map_mul_of_mul_mem 𝔭 hu g hg (𝔭 ^ n) (IsNoetherian.noetherian _) y ih
        (by rw [hgy]; exact zero_mem _)
  rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJ, Ideal.mem_iInf]
  intro n
  rw [← Ideal.map_pow]
  exact hn n

theorem isRadical_map_of_smooth {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (𝔭 : Ideal A) [𝔭.IsPrime] : (𝔭.map (algebraMap A B)).IsRadical := by
  haveI : _root_.IsReduced ((A ⧸ 𝔭) ⊗[A] B) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (A ⧸ 𝔭) _
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B 𝔭).toRingEquiv.trans
    (Algebra.TensorProduct.comm A B (A ⧸ 𝔭)).toRingEquiv
  haveI : _root_.IsReduced (B ⧸ 𝔭.map (algebraMap A B)) :=
    isReduced_of_injective e.toRingHom e.injective
  exact (Ideal.isRadical_iff_quotient_reduced _).2 this

theorem mem_of_mul_mem {B : Type} [CommRing B] (u : Ideal B) [u.IsPrime] (I₀ : Ideal B)
    (hrad : I₀.IsRadical) (g : B) (hg : ∀ Q ∈ I₀.minimalPrimes, Q ≤ u → g ∉ Q)
    (y : Localization.AtPrime u)
    (hy : algebraMap B _ g * y ∈ I₀.map (algebraMap B (Localization.AtPrime u))) :
    y ∈ I₀.map (algebraMap B (Localization.AtPrime u)) := by
  set L := Localization.AtPrime u
  set J := I₀.map (algebraMap B L) with hJdef
  have hJrad : J.IsRadical := by
    rintro x ⟨n, hn⟩
    obtain ⟨⟨b, s⟩, hx⟩ := IsLocalization.mk'_surjective u.primeCompl x
    dsimp only at hx
    subst hx
    have h1 : algebraMap B L (b ^ n) ∈ J := by
      have := Ideal.mul_mem_right (algebraMap B L ((s ^ n : u.primeCompl) : B)) J hn
      rwa [← IsLocalization.mk'_pow, IsLocalization.mk'_spec] at this
    obtain ⟨t, ht, htb⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff u.primeCompl L _ _).1 h1
    have h2 : t * b ∈ I₀ := hrad ⟨n + 1, by
      rw [show (t * b) ^ (n + 1) = (t ^ n * b) * (t * b ^ n) by ring]
      exact Ideal.mul_mem_left _ _ htb⟩
    have h3 : algebraMap B L b ∈ J := by
      have h4 := Ideal.mem_map_of_mem (algebraMap B L) h2
      rw [map_mul] at h4
      obtain ⟨t', ht'⟩ := (IsLocalization.map_units L (⟨t, ht⟩ : u.primeCompl)).exists_left_inv
      have := Ideal.mul_mem_left _ t' h4
      rwa [← mul_assoc, ht', one_mul] at this
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ h3
  by_contra hyJ
  rw [← hJrad.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf] at hyJ
  push_neg at hyJ
  obtain ⟨P, hP, hyP⟩ := hyJ
  haveI : P.IsPrime := hP.1.1
  have hgP : algebraMap B L g ∈ P := ((Ideal.IsPrime.mem_or_mem inferInstance (hP.1.2 hy)).resolve_right hyP)
  set Q := P.comap (algebraMap B L)
  have hQu : Q ≤ u := by
    intro x hx
    by_contra hxu
    exact (Ideal.IsPrime.ne_top inferInstance : P ≠ ⊤)
      (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.map_units L (⟨x, hxu⟩ : u.primeCompl)))
  have hQmin : Q ∈ I₀.minimalPrimes := by
    refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.1 hP.1.2⟩, fun Q' hQ' hle => ?_⟩
    haveI : Q'.IsPrime := hQ'.1
    have hd : Disjoint (u.primeCompl : Set B) (Q' : Set B) :=
      Set.disjoint_left.2 fun x hxM hxI => hxM (hQu (hle hxI))
    haveI := IsLocalization.isPrime_of_isPrime_disjoint u.primeCompl L Q' hQ'.1 hd
    have hc := IsLocalization.comap_map_of_isPrime_disjoint u.primeCompl L hQ'.1 hd
    have hPP : P ≤ Q'.map (algebraMap B L) :=
      hP.2 ⟨inferInstance, Ideal.map_mono hQ'.2⟩ (Ideal.map_le_iff_le_comap.2 hle)
    intro x hx
    rw [← hc]
    exact hPP hx
  exact hg Q hQmin hQu hgP

theorem localization_eq_zero_of_mul_eq_zero : ∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  intro A B _ _ _ _ _ b g u hgb hg
  set 𝔭 := u.asIdeal.comap (algebraMap A B)
  set L := Localization.AtPrime u.asIdeal
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  haveI : Module.Flat A L := Module.Flat.trans A B L
  have hmapeq : 𝔭.map (algebraMap A L) = (𝔭.map (algebraMap A B)).map (algebraMap B L) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s) := by
    intro s hs
    rw [IsScalarTower.algebraMap_apply A B L]
    exact IsLocalization.map_units L (⟨algebraMap A B s, hs⟩ : u.asIdeal.primeCompl)
  have hJ : 𝔭.map (algebraMap A L) ≠ ⊤ := by
    rw [hmapeq]
    refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal L).ne_top ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.2 le_rfl)
  have hg' : ∀ y : L, algebraMap B L g * y ∈ 𝔭.map (algebraMap A L) →
      y ∈ 𝔭.map (algebraMap A L) := by
    intro y hy
    rw [hmapeq] at hy ⊢
    exact mem_of_mul_mem u.asIdeal _ (isRadical_map_of_smooth 𝔭) g hg y hy
  apply eq_zero_of_mul_eq_zero 𝔭 hu hJ (algebraMap B L g) hg'
  rw [← map_mul, hgb, map_zero]

end GlobalTheory.FlatFibreRegular
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapAlgHomAlgebraMap
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbCoh.CohBaseChange

theorem exists_equiv_of_ker {S M A B : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup A]
    [Module S A] [AddCommGroup B] [Module S B] (f : M →ₗ[S] A) (g : M →ₗ[S] B) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : ∀ z, f z = 0 ↔ g z = 0) : ∃ e : A ≃ₗ[S] B, ∀ z, e (f z) = g z := by
  have hk : LinearMap.ker f = LinearMap.ker g := by
    ext z; exact h z
  refine ⟨(f.quotKerEquivOfSurjective hf).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    g.quotKerEquivOfSurjective hg, fun z ↦ ?_⟩
  have : (f.quotKerEquivOfSurjective hf).symm (f z) = Submodule.Quotient.mk z := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearEquiv.trans_apply, this]
  rfl

variable {R : Type} [CommRing R]

theorem dB_ext (K : CochainComplex (ModuleCat.{0} R) ℕ) {R' R'' : Type} [CommRing R'] [Algebra R R']
    [CommRing R''] [Algebra R R''] (α : R' →ₐ[R] R'') (i j : ℕ) (y : R' ⊗[R] K.X i) :
    dB K R'' i j (ext α _ y) = ext α _ (dB K R' i j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp
  | add a b ha hb => simp only [map_add, ha, hb]

theorem spMap_algHom_algebraMap {R' R'' : Type} [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R'']
    (α : R' →ₐ[R] R'') : spMap (α : R' →+* R'') ≫ spMap (algebraMap R R') = spMap (algebraMap R R'') := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, α.comp_algebraMap]

theorem isPullback_self {X : Scheme.{0}} (s : X ⟶ Sp R) : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
  have : spMap (algebraMap R R) = 𝟙 (Sp R) := Spec.map_id _
  rw [this]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

theorem liftsAt_of (K : CochainComplex (ModuleCat.{0} R) ℕ) {R' k : Type} [CommRing R'] [Algebra R R']
    [CommRing k] [Algebra R k] (α : R' →ₐ[R] k) (i : ℕ) {H H₀ : Type} [AddCommGroup H] [Module R' H]
    [AddCommGroup H₀] [Module k H₀] (θ : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] H)
    (θ₀ : LinearMap.ker (dB K k i (i + 1)) →ₗ[k] H₀) (p : H → H₀) (hθ : Function.Surjective θ)
    (hθ₀ : ∀ z, θ₀ z = 0 ↔ z.1 ∈ LinearMap.range (dB K k (i - 1) i))
    (nat : ∀ z z', z'.1 = ext α _ z.1 → θ₀ z' = p (θ z)) (hp : Function.Surjective p) : LiftsAt K α i := by
  intro z hz
  obtain ⟨x, hx⟩ := hp (θ₀ ⟨z, hz⟩)
  obtain ⟨y, rfl⟩ := hθ x
  have hy' : ext α _ y.1 ∈ LinearMap.ker (dB K k i (i + 1)) := by
    rw [LinearMap.mem_ker, dB_ext, LinearMap.mem_ker.1 y.2, map_zero]
  have h1 := nat y ⟨_, hy'⟩ rfl
  obtain ⟨b, hb⟩ := (hθ₀ (⟨z, hz⟩ - ⟨_, hy'⟩)).1 (by rw [map_sub, h1, hx, sub_self])
  refine ⟨y.1, b, y.2, ?_⟩
  rw [hb]
  simp

theorem bc_of {R' : Type} [CommRing R'] [Algebra R R'] {Z Z' P H H' : Type} [AddCommGroup Z] [Module R Z]
    [AddCommGroup Z'] [Module R' Z'] [AddCommGroup P] [Module R P] [AddCommGroup H] [Module R H]
    [AddCommGroup H'] [Module R' H'] (u : Z →ₗ[R] P) (v : Z' →ₗ[R'] R' ⊗[R] P) (θ : Z →ₗ[R] H)
    (θ' : Z' →ₗ[R'] H') (p : H → H') (hu : Function.Surjective u) (hv : Function.Surjective v)
    (hθ : Function.Surjective θ) (hθ' : Function.Surjective θ') (h : ∀ z, θ z = 0 ↔ u z = 0)
    (h' : ∀ z, v z = 0 ↔ θ' z = 0) (nat : ∀ z, ∃ z', v z' = 1 ⊗ₜ u z ∧ θ' z' = p (θ z)) :
    ∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ c, e (1 ⊗ₜ c) = p c := by
  obtain ⟨e, he⟩ := exists_equiv_of_ker θ u hθ hu h
  obtain ⟨e', he'⟩ := exists_equiv_of_ker v θ' hv hθ' h'
  refine ⟨e.baseChange R R' _ _ ≪≫ₗ e', fun c ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hθ c
  obtain ⟨z', h1, h2⟩ := nat z
  rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, he, ← h1, he', h2]

variable {X : Scheme.{0}} {s : X ⟶ Sp R} {K : CochainComplex (ModuleCat.{0} R) ℕ}

theorem liftsAt_zero (M : Model s K) (hU : UConst s) {R' k : Type} [CommRing R'] [Algebra R R']
    [CommRing k] [Algebra R k] (α : R' →ₐ[R] k) (hα : Function.Surjective α) : LiftsAt K α 0 := by
  intro z hz
  have h' := IsPullback.of_hasPullback s (spMap (algebraMap R R'))
  have h₀ := IsPullback.of_hasPullback s (spMap (algebraMap R k))
  obtain ⟨e', -⟩ := M.θ0_one h'
  obtain ⟨e₀, he₀⟩ := M.θ0_one h₀
  obtain ⟨r, hr, -⟩ := hU k _ _ _ h₀ (M.θ0 h₀ ⟨z, hz⟩).1 (M.θ0 h₀ ⟨z, hz⟩).2
  have hz' : (⟨z, hz⟩ : LinearMap.ker (dB K k 0 1)) = r • ⟨_, e₀⟩ := by
    apply (M.θ0 h₀).injective
    rw [map_smul]
    refine Subtype.ext (funext fun T ↦ ?_)
    rw [hr T, Algebra.algebraMap_eq_smul_one, ← he₀ T]
    rfl
  obtain ⟨r', rfl⟩ := hα r
  refine ⟨r' • ((1 : R') ⊗ₜ[R] M.one), 0, ?_, ?_⟩
  · rw [map_smul]
    exact (congrArg (r' • ·) (LinearMap.mem_ker.1 e')).trans (smul_zero _)
  · have := congrArg Subtype.val hz'
    simp only [Submodule.coe_smul] at this
    rw [this, map_zero, add_zero, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp

theorem of_parts (hex : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ (∃ n, ∀ p, n < p → IsZero (K.X p)) ∧ Nonempty (Model s K))
    (halg : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∃ n, ∀ p, n < p → IsZero (K.X p)) → (∀ i, i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → LiftsAt K α i) → ∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom))
    (hsplit : ∀ (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom)) → ∀ i, 1 ≤ i → i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'], ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Finite R P) (_ : Module.Projective R P) (u : LinearMap.ker (dB K R i (i + 1)) →ₗ[R] P) (v : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] R' ⊗[R] P), Function.Surjective u ∧ Function.Surjective v ∧ (∀ z, u z = 0 ↔ z.1 ∈ LinearMap.range (dB K R (i - 1) i)) ∧ (∀ z, v z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' (i - 1) i)) ∧ ∀ z z', z'.1 = ext (Algebra.ofId R R') _ z.1 → v z' = 1 ⊗ₜ u z) :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s := by
  intro R _ _ X s hp hf hU hl
  obtain ⟨K, hK, hb, ⟨M⟩⟩ := hex R X s hp hf
  have hproj := halg R K hK hb (by
    intro i hi R' _ _ _ _ k _ _ α hα
    have h' := IsPullback.of_hasPullback s (spMap (algebraMap R R'))
    have w := IsPullback.of_hasPullback (pullback.snd s (spMap (algebraMap R R'))) (spMap (α : R' →+* k))
    have h₀ := w.paste_horiz h'
    rw [spMap_algHom_algebraMap] at h₀
    obtain ⟨s1, s2⟩ := hl R' k α hα _ _ _ _ _ _ h' w
    obtain ⟨n1, n2⟩ := M.nat h' h₀ α _ w.w rfl
    obtain ⟨a1, -, a2, -⟩ := M.exact h'
    obtain ⟨-, b1, -, b2⟩ := M.exact h₀
    interval_cases i
    · exact liftsAt_zero M hU α hα
    · exact liftsAt_of K α 1 (M.θ1 h') (M.θ1 h₀) _ a1 b1 n1 s1
    · exact liftsAt_of K α 2 (M.θ2 h') (M.θ2 h₀) _ a2 b2 n2 s2)
  have hid := isPullback_self s
  obtain ⟨a1, b1, a2, b2⟩ := M.exact hid
  have hz : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (i : ℕ) (z : LinearMap.ker (dB K R i (i + 1))),
      ext (Algebra.ofId R R') _ z.1 ∈ LinearMap.ker (dB K R' i (i + 1)) := fun R' _ _ i z ↦ by
    rw [LinearMap.mem_ker, dB_ext, LinearMap.mem_ker.1 z.2, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨P, _, _, _, _, u, v, hu, -, ku, -⟩ := hsplit R K hK hproj 1 le_rfl (by norm_num) R
    obtain ⟨e, -⟩ := exists_equiv_of_ker u (M.θ1 hid) hu a1 fun z ↦ (ku z).trans (b1 z).symm
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  · obtain ⟨P, _, _, _, _, u, v, hu, -, ku, -⟩ := hsplit R K hK hproj 2 (by norm_num) le_rfl R
    obtain ⟨e, -⟩ := exists_equiv_of_ker u (M.θ2 hid) hu a2 fun z ↦ (ku z).trans (b2 z).symm
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  · intro R' _ _ X' s' φ h
    obtain ⟨P, _, _, _, _, u, v, hu, hv, ku, kv, hn⟩ := hsplit R K hK hproj 1 le_rfl (by norm_num) R'
    obtain ⟨c1, d1, -, -⟩ := M.exact h
    obtain ⟨n1, -⟩ := M.nat hid h (Algebra.ofId R R') φ h.w (Category.comp_id _)
    exact bc_of u v (M.θ1 hid) (M.θ1 h) _ hu hv a1 c1 (fun z ↦ (b1 z).trans (ku z).symm)
      (fun z ↦ (kv z).trans (d1 z).symm) fun z ↦ ⟨⟨_, hz R' 1 z⟩, hn _ _ rfl, n1 _ _ rfl⟩
  · intro R' _ _ X' s' φ h
    obtain ⟨P, _, _, _, _, u, v, hu, hv, ku, kv, hn⟩ := hsplit R K hK hproj 2 (by norm_num) le_rfl R'
    obtain ⟨-, -, c2, d2⟩ := M.exact h
    obtain ⟨-, n2⟩ := M.nat hid h (Algebra.ofId R R') φ h.w (Category.comp_id _)
    exact bc_of u v (M.θ2 hid) (M.θ2 h) _ hu hv a2 c2 (fun z ↦ (b2 z).trans (ku z).symm)
      (fun z ↦ (kv z).trans (d2 z).symm) fun z ↦ ⟨⟨_, hz R' 2 z⟩, hn _ _ rfl, n2 _ _ rfl⟩

end GlobalTheory.AbCoh.CohBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableUnderGeneralizationSectionComponents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem stableUnderGeneralization_sectionComponents :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ →
      StableUnderGeneralization {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  intro X S f e hf hef x x' hxx' hx
  obtain ⟨V, _, _, _, g, hgc, hgb⟩ := GlobalTheory.T.exists_valuationRing_dominating_specialization X x' x hxx'
  set p : Spec (CommRingCat.of V) ⟶ S := g ≫ f with hp
  have hpb : IsPullback (pullback.fst f p) (pullback.snd f p) f p := IsPullback.of_hasPullback f p
  let σ : Spec (CommRingCat.of V) ⟶ pullback f p := pullback.lift g (𝟙 _) (by simp [hp])
  let e' : Spec (CommRingCat.of V) ⟶ pullback f p :=
    pullback.lift (p ≫ e) (𝟙 _) (by simp [Category.assoc, hef])
  have hσf : σ ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have hσq : σ ≫ pullback.fst f p = g := pullback.lift_fst _ _ _
  have he'f : e' ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have he'q : e' ≫ pullback.fst f p = p ≫ e := pullback.lift_fst _ _ _
  haveI : Smooth f := hf
  have hf' : Smooth (pullback.snd f p) := inferInstance
  have key := GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback X S (pullback f p) (Spec (CommRingCat.of V)) f (pullback.snd f p) p
    (pullback.fst f p) e e' hf hpb hef he'f he'q
  have hc : σ (IsLocalRing.closedPoint V) ∈ {y : ↥(pullback f p) | y ∈ connectedComponentIn
      (pullback.snd f p ⁻¹' {pullback.snd f p y}) (e' (pullback.snd f p y))} := by
    rw [← key]
    rw [Set.mem_preimage]
    have h1 : (pullback.fst f p) (σ (IsLocalRing.closedPoint V)) = x := by
      rw [← hgc, ← hσq]
      rfl
    rw [h1]
    exact hx
  have hb := GlobalTheory.T.section_mem_component_generic_of_closed_valuation V (pullback f p) (pullback.snd f p) e' σ hf' he'f hσf hc
  rw [← key] at hb
  have : (pullback.fst f p) (σ (⊥ : PrimeSpectrum V)) = x' := by
    rw [← hgb, ← hσq]
    rfl
  rw [← this]
  exact hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheaf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem heightFunctionalStatement_of_pairingProperties (hA5 : A5)
    (hsect : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)),
      Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _) : B2 := by
  intro R _ A _ hA F n hn
  have key : ∀ x : H R (sp A) F n, x = 0 := by
    intro x
    obtain ⟨Y, f, hf, hs, hx⟩ := hA5 R (Spec (CommRingCat.of A)) F n hn x
    obtain ⟨s, hsf⟩ := hsect A hA Y f hf hs
    calc x = pull R (𝟙 (sp A)) F n x := (pull_id R _ F n x).symm
      _ = pull R (sch.map (s ≫ f)) F n x := by rw [hsf, CategoryTheory.Functor.map_id]
      _ = pull R (sch.map s) F n (pull R (sch.map f) F n x) := by
          rw [CategoryTheory.Functor.map_comp, pull_comp]
      _ = 0 := by rw [hx, map_zero]
  exact ⟨fun x y => by rw [key x, key y]⟩

theorem b2 : B2 := heightFunctionalStatement_of_pairingProperties GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover GlobalTheory.T.exists_section_of_etale_surjective_of_SH

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssocStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCupProduct_assoc : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l), cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring) := by
  first
  | exact @GlobalTheory.EtC.CupAssoc.main
  | exact GlobalTheory.EtC.CupAssoc.main
  | (intros; apply GlobalTheory.EtC.CupAssoc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCupProduct_graded_comm : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring) := by
  first
  | exact @GlobalTheory.EtC.cup_comm
  | exact GlobalTheory.EtC.cup_comm
  | (intros; apply GlobalTheory.EtC.cup_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)) ∧ (∀ (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (i j : ℤ), cup q (rootClass i ζ) (rootClass j ζ) = (rootClass (i + j) ζ).cast (by ring) rfl ∧ rootClass 0 ζ = one q (sch.obj X)) := by
  first
  | exact @GlobalTheory.EtC.CupGen.main
  | exact GlobalTheory.EtC.CupGen.main
  | (intros; apply GlobalTheory.EtC.CupGen.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLocalizationEtaleNbhdEqUnitMulPowStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_localization_etaleNbhd_eq_unit_mul_pow : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  first | (exact @GlobalTheory.EtC.kummer_divisor_step) | (exact GlobalTheory.EtC.kummer_divisor_step) | (intros; apply GlobalTheory.EtC.kummer_divisor_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVectorStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightDegree_le_of_homogeneous_fockWeightVector : ∀ (p q r s : ℕ), (∀ (d : ℕ) (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 → P ∈ wtSub (fockAct1 p q r s) μ → degW (cPair r s) μ ≤ d) ∧ (∀ (d : ℕ) (μ : Ix r s → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 → P ∈ wtSub (fockAct2 p q r s) μ → degW (cPair p q) μ ≤ d) := by
  first | exact @GlobalTheory.FockAlg.degW_le_of_homog_wtSub | exact GlobalTheory.FockAlg.degW_le_of_homog_wtSub | (intros; apply GlobalTheory.FockAlg.degW_le_of_homog_wtSub <;> assumption)
end

