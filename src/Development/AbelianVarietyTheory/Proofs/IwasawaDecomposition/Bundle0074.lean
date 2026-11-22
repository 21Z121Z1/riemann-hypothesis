import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0063
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris

theorem crisP_ker_dvd (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j)
    (x : Per.Acris l) (hx : j x = 0) : ∃ y : Per.Acris l, j y = 0 ∧ x = (l : Per.Acris l) * y := by
  obtain ⟨-, -, hd, hdv⟩ := acris_basic l
  obtain ⟨s, z, hs⟩ := hd x 1
  have h1 : (l : Per.Acris0 l) ∣ s := by
    refine GlobalTheory.T.acris_divisible_of_kernel_powers l s fun n => ?_
    obtain ⟨u, z', hu, e⟩ := GlobalTheory.T.acris_filtration_approx_by_envelope_kernel_power l j hj n x (by rw [hx]; exact zero_mem _)
    obtain ⟨w, hw⟩ := (hdv (s - u) 1).1 ⟨z' - z, by rw [map_sub]; linear_combination e - hs⟩
    exact ⟨u, w, by linear_combination hw, hu⟩
  obtain ⟨w, hw⟩ := h1
  have e : x = (l : Per.Acris l) * (algebraMap (Per.Acris0 l) (Per.Acris l) w + z) := by
    rw [hs, hw, map_mul, map_natCast]
    ring
  refine ⟨_, ?_, e⟩
  have hu : IsUnit (l : Per.BdRp l) := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map (algebraMap (Per.AinfP l) (Per.BdRp l))
    rwa [map_natCast] at this
  rw [e, map_mul, map_natCast] at hx
  exact hu.mul_right_eq_zero.1 hx

theorem crisP_injective : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → Function.Injective j := by
  intro l _ j hj
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h : ∀ n : ℕ, ∃ y : Per.Acris l, j y = 0 ∧ x = (l : Per.Acris l) ^ n * y := by
    intro n
    induction n with
    | zero => exact ⟨x, hx, by rw [pow_zero, one_mul]⟩
    | succ n ih =>
      obtain ⟨y, hy, e⟩ := ih
      obtain ⟨y', hy', e'⟩ := crisP_ker_dvd l j hj y hy
      exact ⟨y', hy', by rw [e, e', pow_succ, mul_assoc]⟩
  have hc := (acris_basic l).1
  refine hc.toIsHausdorff.haus x fun n => ?_
  obtain ⟨y, -, e⟩ := h n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨y, e⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.BdRField

theorem eq_pow_mul_unit {R : Type} [CommRing R] (π : R) (hsep : ∀ y : R, (∀ n : ℕ, π ^ n ∣ y) → y = 0)
    (hu : ∀ y : R, ¬ π ∣ y → IsUnit y) (y : R) (hy : y ≠ 0) : ∃ (n : ℕ) (u : R), IsUnit u ∧ y = π ^ n * u := by
  classical
  have h : ∃ n : ℕ, ¬ π ^ n ∣ y := by
    by_contra h
    push Not at h
    exact hy (hsep y h)
  have h0 : Nat.find h ≠ 0 := by
    intro e
    have := Nat.find_spec h
    rw [e] at this
    exact this (by simp)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have h1 : π ^ n ∣ y := by
    by_contra hc
    have := Nat.find_min' h hc
    omega
  obtain ⟨u, rfl⟩ := h1
  refine ⟨n, u, hu u ?_, rfl⟩
  intro hd
  have := Nat.find_spec h
  rw [hn] at this
  exact this (by rw [pow_succ]; exact mul_dvd_mul_left _ hd)

theorem general {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Nontrivial R] (M : Submonoid R)
    [IsLocalization M S] (π : R) (hreg : ∀ y : R, π * y = 0 → y = 0)
    (hsep : ∀ y : R, (∀ n : ℕ, π ^ n ∣ y) → y = 0)
    (hu : ∀ y : R, ¬ π ∣ y → IsUnit y) (hπ : π ∈ M) (hM : ∀ m ∈ M, ∃ n : ℕ, m ∣ π ^ n) :
    IsDomain R ∧ Function.Injective (algebraMap R S) ∧ IsField S ∧
      ∀ x : S, ∃ (n : ℕ) (y : R), x * algebraMap R S π ^ n = algebraMap R S y := by
  have hregn : ∀ (n : ℕ) (y : R), π ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y h; simpa using h
    | succ n ih => intro y h; exact ih y (hreg _ (by rw [← h]; ring))
  have : NoZeroDivisors R := ⟨fun {a b} h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    obtain ⟨n, u, hu', rfl⟩ := eq_pow_mul_unit π hsep hu a ha
    right
    rw [mul_assoc] at h
    exact (hu'.mul_right_eq_zero).1 (hregn n _ h)⟩
  have hD : IsDomain R := NoZeroDivisors.to_isDomain R
  have hle : M ≤ nonZeroDivisors R := by
    intro m hm
    obtain ⟨n, c, hc⟩ := hM m hm
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rintro rfl
    have := hregn n 1 (by rw [hc]; ring)
    exact one_ne_zero this
  have hinj : Function.Injective (algebraMap R S) := IsLocalization.injective S hle
  have : Nontrivial S := hinj.nontrivial
  refine ⟨hD, hinj, ⟨exists_pair_ne S, mul_comm, ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨⟨y, m⟩, hy⟩ := IsLocalization.surj M a
    have hm : IsUnit (algebraMap R S m) := IsLocalization.map_units S m
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp only [map_zero] at hy
      exact ha (hm.mul_left_eq_zero.1 hy)
    obtain ⟨n, u, hu', rfl⟩ := eq_pow_mul_unit π hsep hu y hy0
    have hyu : IsUnit (algebraMap R S (π ^ n * u)) := by
      rw [map_mul, map_pow]
      exact ((IsLocalization.map_units S (⟨π, hπ⟩ : M)).pow n).mul (hu'.map _)
    simp only at hy
    rw [← hy] at hyu
    exact (isUnit_of_mul_isUnit_left hyu).exists_right_inv
  · intro x
    obtain ⟨⟨y, m⟩, hy⟩ := IsLocalization.surj M x
    obtain ⟨n, c, hc⟩ := hM m m.2
    refine ⟨n, y * c, ?_⟩
    simp only at hy
    rw [← map_pow, hc, map_mul, map_mul, ← mul_assoc, hy]

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨ε, ?_, ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro e
    have := h 1
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val e

theorem of_isEps (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : IsEps e) :
    IsDomain (Per.BdRp l) ∧ Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ IsField (Per.BdR l) ∧
      ∀ x : Per.BdR l, ∃ (n : ℕ) (y : Per.BdRp l), x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n =
        algebraMap (Per.BdRp l) (Per.BdR l) y := by
  obtain ⟨hF, hreg, hc, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  obtain ⟨-, hθ, hu, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have : Nontrivial (Per.BdRp l) := (Per.θD l).domain_nontrivial
  haveI : IsLocalization.Away (aDp l (xi e)) (Per.BdR l) := GlobalTheory.CrisLoc.bdR_away l _ hk
  refine general (Submonoid.powers (aDp l (xi e))) (aDp l (xi e)) hreg ?_ ?_ ?_ ?_
  · intro y hy
    refine hc.toIsHausdorff.haus y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hy n
  · intro y hy
    refine hu y fun h => hy ?_
    have := (hF 1 y).1 ((hθ y).1 h)
    rwa [pow_one] at this
  · exact Submonoid.mem_powers _
  · rintro _ ⟨k, rfl⟩
    exact ⟨k, dvd_rfl⟩

theorem bdR_isField : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.BdRp l) ∧ Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ IsField (Per.BdR l) ∧ ∀ e : Per.Fl l, IsEps e → ∀ x : Per.BdR l, ∃ (n : ℕ) (y : Per.BdRp l), x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n = algebraMap (Per.BdRp l) (Per.BdR l) y := by
  intro l _
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨h1, h2, h3, -⟩ := of_isEps l e he
  exact ⟨h1, h2, h3, fun e' he' => (of_isEps l e' he').2.2.2⟩

end GlobalTheory.MemLoc.BdRField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CLTateInvariantsFiniteExtensionMemStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cLTate_invariants_finiteExtension_mem : ∀ (l : ℕ) [Fact l.Prime], ∀ (K : FinExt l) (x : ℂ_[l]), (∀ g ∈ GK K, Per.σC g x = x) → ∃ y ∈ K.1, ((y : Om l) : ℂ_[l]) = x := by
  first | exact @GlobalTheory.MemLoc.invariants_finExt | exact GlobalTheory.MemLoc.invariants_finExt | (intros; apply GlobalTheory.MemLoc.invariants_finExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApproxStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → (∀ j' : Per.Acris l →+* Per.BdRp l, IsCrisP j' → j' = j) ∧ (∀ (g : Per.Gq l) (x : Per.Acris l), j (sigA g x) = Per.σDp g (j x)) ∧ ∀ (n : ℕ) (x : Per.Acris l) (y : Per.BdRp l), (∀ r : ℕ, ∃ (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l), x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z ∧ Per.ev l n (y - algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) = Per.ev l n ((l : Per.BdRp l) ^ r * aDp l a)) → Per.ev l n (j x) = Per.ev l n y := by
  first | exact @GlobalTheory.MemLoc.crisP_unique_equivariant | exact GlobalTheory.MemLoc.crisP_unique_equivariant | (intros; apply GlobalTheory.MemLoc.crisP_unique_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_acris_to_bdRPlus : ∀ (l : ℕ) [Fact l.Prime], ∃ j : Per.Acris l →+* Per.BdRp l, IsCrisP j := by
  first | exact @GlobalTheory.MemLoc.exists_isCrisP | exact GlobalTheory.MemLoc.exists_isCrisP | (intros; apply GlobalTheory.MemLoc.exists_isCrisP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMaxUnramifiedEmbeddingIntoBcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maxUnramified_embedding_into_Bcris : ∀ (l : ℕ) [Fact l.Prime], ∀ (o : Om l →+* Per.BdRp l) (ι : Per.Bcris l →+* Per.BdR l), IsSec o → Function.Injective ι → (∀ a : Per.Ainf l, ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a)) → IsUnit (l : Per.Bcris l) → ∃ u : ↥(MaximalUnramifiedExtension l) →+* Per.Bcris l, ∀ c : ↥(MaximalUnramifiedExtension l), ι (u c) = algebraMap (Per.BdRp l) (Per.BdR l) (o (c : Om l)) := by
  first | exact @GlobalTheory.MemLoc.exists_unram_to_cris | exact GlobalTheory.MemLoc.exists_unram_to_cris | (intros; apply GlobalTheory.MemLoc.exists_unram_to_cris <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomainStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D], Module.Finite D (integralClosure D (FractionRing D)) := by
  first | exact @GlobalTheory.finite_integralClosure_of_essFiniteType_int | exact GlobalTheory.finite_integralClosure_of_essFiniteType_int | (intros; apply GlobalTheory.finite_integralClosure_of_essFiniteType_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeRhamFiltrationIffXiPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem mem_FilD_iff_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ ∃ y : Per.BdRp l, x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ (-a).toNat = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e) ^ a.toNat * y) := by
  intro l _ e he a x
  have h := (GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he).1
  have hg : ∀ (n : ℕ) (x : Per.BdR l), x ∈ Per.FilD l (-(n : ℤ)) ↔ ∃ y : Per.BdRp l,
      x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n = algebraMap (Per.BdRp l) (Per.BdR l) y :=
    GlobalTheory.CrisLoc.mem_fil_neg l _ (GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he)
  generalize aDp l (xi e) = ξ at h hg ⊢
  have hn : ∀ (n : ℕ) (w : Per.BdR l), w ∈ Per.FilD l (n : ℤ) ↔
      ∃ y : Per.BdRp l, w = algebraMap (Per.BdRp l) (Per.BdR l) (ξ ^ n * y) := by
    intro n w
    constructor
    · intro hw
      obtain ⟨z, hz, ez⟩ := GlobalTheory.RingIface.exists_of_mem_FilD_nat l hw
      obtain ⟨y, rfl⟩ := (h _ _).1 hz
      exact ⟨y, ez.symm⟩
    · rintro ⟨y, rfl⟩
      exact GlobalTheory.RingIface.alg_mem_FilD_nat l ((h _ _).2 (dvd_mul_right _ _))
  rcases le_total 0 a with ha | ha
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    rw [hn, Int.toNat_neg_natCast, Int.toNat_natCast, pow_zero, mul_one]
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat ha
    rw [hg, neg_neg, Int.toNat_neg_natCast, Int.toNat_natCast]
    simp only [pow_zero, one_mul]

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLatticeStabilizerDetRoot
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.DIV

namespace GlobalTheory.Mem.StabDet

theorem isIntegral_det {E : Type} [Field E] [NumberField E] {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det :=
  _root_.UpperTheory.Reformulated.B.Ybf4.isIntegral_det L hfg hsp γ hγ

theorem eq_pm_one_of_unitary {R : Ranks} (H : Formalism.BasicNotions.Host R) :
    letI := H.cmStar; ∀ z : H.E, z ∈ unitary H.E → IsIntegral ℤ z → ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  letI := H.cmStar
  intro z hu hz
  have := H.isCMField_hostE
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one H.E ℂ hz (fun φ => by
    have h1 : star z * z = 1 := hu.1
    have h2 : φ (star z) = starRingEnd ℂ (φ z) := IsCMField.complexEmbedding_complexConj H.E φ z
    have h3 := congrArg φ h1
    rw [map_mul, h2, map_one, Complex.conj_mul'] at h3
    have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4)
  exact ⟨n, hn, hp⟩

end GlobalTheory.Mem.StabDet
end

