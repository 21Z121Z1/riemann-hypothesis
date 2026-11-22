import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0204
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibilityOfVanishingPowers
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem DetInv.dvd_pow_of_local_dvd_pow (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C)) (ξ : R)
    (hξ : ξ ∈ nonZeroDivisors R) (hf : ∀ i, f i ξ = 0) (hker : ∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) :
    ∀ (n : ℕ) (r : R), (∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r) → ξ ^ n ∣ r := by
  intro n
  induction n with
  | zero => intro r _; simp
  | succ n ih =>
    intro r h
    have hr0 : ∀ i, f i r = 0 := by
      intro i
      obtain ⟨s, hs, t, ht⟩ := h i
      have h1 : f i (s * r) = 0 := by
        rw [ht, map_mul, map_pow, hf i, zero_pow (Nat.succ_ne_zero n), zero_mul]
      rw [map_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left hs
    obtain ⟨r1, rfl⟩ := hker r hr0
    have h2 : ∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r1 := by
      intro i
      obtain ⟨s, hs, t, ht⟩ := h i
      refine ⟨s, hs, t, ?_⟩
      have : ξ * (s * r1) = ξ * (ξ ^ n * t) := by
        rw [← mul_assoc, mul_comm ξ s, mul_assoc, ht]; ring
      exact (mul_cancel_left_mem_nonZeroDivisors hξ).mp this
    obtain ⟨u, hu⟩ := ih r1 h2
    exact ⟨u, by rw [hu]; ring⟩

example : ∀ (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C)) (ξ : R), ξ ∈ nonZeroDivisors R → (∀ i, f i ξ = 0) → (∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) → ∀ (n : ℕ) (r : R), (∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r) → ξ ^ n ∣ r :=
  @DetInv.dvd_pow_of_local_dvd_pow

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorDescentFlatNormalDomains
section
open IsLocalRing Polynomial

namespace GlobalTheory.DivDescent

theorem colonStep : ∀ (A' B' : Type) [CommRing A'] [IsNoetherianRing A'] [CommRing B'] [Algebra A' B']
    [Module.Flat A' B'] (b c : B') (s : A'), b * c = algebraMap A' B' s →
    (∀ x : A', (∀ j : A', c ∣ algebraMap A' B' j → ∃ a : A', x * j = s * a) →
      b ∣ algebraMap A' B' x) →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  intro A' B' _ _ _ _ _ b c s hbc h
  have hφ : (algebraMap A' B').Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hle : (Ideal.span {s}).colon (((Ideal.span {c}).comap (algebraMap A' B') : Ideal A') : Set A') ≤
      (Ideal.span {b}).comap (algebraMap A' B') := by
    intro x hx
    rw [Submodule.mem_colon] at hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    apply h x
    intro j hj
    have := hx j (by rw [SetLike.mem_coe, Ideal.mem_comap, Ideal.mem_span_singleton]; exact hj)
    rw [smul_eq_mul, Ideal.mem_span_singleton] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, by rw [ha]⟩
  refine Ideal.map_mono hle ?_
  rw [GlobalTheory.ideal_map_colon_eq_of_flat (algebraMap A' B') hφ, Submodule.mem_colon]
  intro y hy
  have hy' : y ∈ Ideal.span {c} := Ideal.map_comap_le hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.1 hy'
  rw [Ideal.map_span, Set.image_singleton, smul_eq_mul, Ideal.mem_span_singleton]
  exact ⟨z, by rw [← hbc, mul_assoc]⟩

theorem primeDescent : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [CommRing B']
    [IsDomain B'] [IsNoetherianRing B'] [Algebra A' B'] [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ Q : Ideal B', Q.IsPrime → Q.height = 1 → algebraMap A' B' s ∈ Q →
    (Q.comap (algebraMap A' B')).height = 1 ∧
      (Q.comap (algebraMap A' B')).map (algebraMap A' B') = Q := by
  intro A' B' _ _ _ _ _ _ _ _ s hs hpr Q hQ hQ1 hsQ
  haveI : Algebra.HasGoingDown A' B' := Algebra.HasGoingDown.of_flat
  haveI hPp : (Q.comap (algebraMap A' B')).IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver (Q.comap (algebraMap A' B')) := ⟨rfl⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (Q.comap (algebraMap A' B')) Q
  have hle1 : (Q.comap (algebraMap A' B')).height ≤ 1 := by rw [← hQ1, h]; exact le_self_add
  have h1 : (Q.comap (algebraMap A' B')).height = 1 := by
    refine le_antisymm hle1 ?_
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro hb
    have : s ∈ Q.comap (algebraMap A' B') := hsQ
    rw [hb, Ideal.mem_bot] at this
    exact hs this
  refine ⟨h1, ?_⟩
  haveI hP : ((Q.comap (algebraMap A' B')).map (algebraMap A' B')).IsPrime := hpr _ hPp h1 hsQ
  have hle : (Q.comap (algebraMap A' B')).map (algebraMap A' B') ≤ Q := Ideal.map_comap_le
  by_contra hne
  have hlt := Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hQ1] at hlt
  have h0 : ((Q.comap (algebraMap A' B')).map (algebraMap A' B')).height = 0 :=
    ENat.lt_one_iff_eq_zero.mp hlt
  rw [Ideal.height_eq_zero_iff_eq_bot] at h0
  have hm : algebraMap A' B' s ∈ (Q.comap (algebraMap A' B')).map (algebraMap A' B') :=
    Ideal.mem_map_of_mem _ hsQ
  rw [h0, Ideal.mem_bot] at hm
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B')
    (mem_nonZeroDivisors_of_ne_zero hs)
  have h2 : s • (1 : B') = s • (0 : B') := by
    rw [Algebra.smul_def, mul_one, smul_zero]; exact hm
  exact one_ne_zero (hreg h2)

theorem divisor_descent : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A']
    [IsIntegrallyClosed A'] [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B']
    [Algebra A' B'] [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ b c : B', b * c = algebraMap A' B' s →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  intro A' B' _ _ _ _ _ _ _ _ _ _ s hs hpr b c hbc
  have hinj : ∀ a : A', a ≠ 0 → algebraMap A' B' a ≠ 0 := by
    intro a ha h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B')
      (mem_nonZeroDivisors_of_ne_zero ha)
    have h1 : a • (1 : B') = a • (0 : B') := by
      rw [Algebra.smul_def, mul_one, smul_zero]; exact h0
    exact one_ne_zero (hreg h1)
  have hb0 : b ≠ 0 := by rintro rfl; exact hinj s hs (by rw [← hbc, zero_mul])
  have hc0 : c ≠ 0 := by rintro rfl; exact hinj s hs (by rw [← hbc, mul_zero])
  have hloc : ∀ Q : Ideal B', Q.IsPrime → Q.height = 1 → b ∈ Q →
      ∃ j : A', c ∣ algebraMap A' B' j ∧ ∃ t ∉ Q, algebraMap A' B' j ∣ t * c := by
    intro Q hQ hQ1 hbQ
    have hsQ : algebraMap A' B' s ∈ Q := by rw [← hbc]; exact Q.mul_mem_right c hbQ
    obtain ⟨h𝔭1, h𝔭Q⟩ := primeDescent A' B' s hs hpr Q hQ hQ1 hsQ
    obtain ⟨j₀, ⟨t₁, ht₁, hj₁⟩, ⟨t₂, ht₂, hj₂⟩⟩ :=
      GlobalTheory.T.height_one_prime_associate A' B' (Q.comap (algebraMap A' B')) (by rw [h𝔭Q]; exact hQ) (by rw [h𝔭Q]; exact hQ1) c hc0
    rw [h𝔭Q] at ht₁ ht₂
    have hS0 : (0 : B') ∉ (Q.comap (algebraMap A' B')).primeCompl.map (algebraMap A' B') := by
      intro h0
      obtain ⟨u', hu', h⟩ := Submonoid.mem_map.1 h0
      by_cases hu0 : u' = 0
      · exact hu' (hu0 ▸ (Q.comap (algebraMap A' B')).zero_mem)
      · exact hinj u' hu0 h
    obtain ⟨u, huS, hu⟩ := GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one B' ((Q.comap (algebraMap A' B')).primeCompl.map (algebraMap A' B'))
      hS0 (algebraMap A' B' j₀) c hc0 (by
        intro Q' hQ' hQ'1 hcQ' hdisj
        have hsQ' : algebraMap A' B' s ∈ Q' := by rw [← hbc]; exact Q'.mul_mem_left b hcQ'
        obtain ⟨h𝔭'1, h𝔭'Q'⟩ := primeDescent A' B' s hs hpr Q' hQ' hQ'1 hsQ'
        have hle : Q'.comap (algebraMap A' B') ≤ Q.comap (algebraMap A' B') := by
          intro x hx
          by_contra hx𝔭
          exact Set.disjoint_left.1 hdisj (Submonoid.mem_map_of_mem (algebraMap A' B') hx𝔭) hx
        have heq : Q'.comap (algebraMap A' B') = Q.comap (algebraMap A' B') := by
          by_contra hne
          have := Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hle hne)
          rw [h𝔭'1, h𝔭1] at this
          exact lt_irrefl _ this
        have hQQ : Q' = Q := by rw [← h𝔭'Q', heq, h𝔭Q]
        subst hQQ
        exact ⟨t₁, ht₁, hj₁⟩)
    obtain ⟨u', hu', rfl⟩ := Submonoid.mem_map.1 huS
    refine ⟨u' * j₀, by rw [map_mul]; exact hu, algebraMap A' B' u' * t₂, ?_, ?_⟩
    · intro hm
      rcases hQ.mem_or_mem hm with h | h
      · exact hu' h
      · exact ht₂ h
    · rw [map_mul, mul_assoc]; exact mul_dvd_mul_left _ hj₂
  apply colonStep A' B' b c s hbc
  intro x hx
  obtain ⟨u, hu, hdiv⟩ := GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one B' ⊥ (by simp) (algebraMap A' B' x) b hb0 (by
    intro Q hQ hQ1 hbQ _
    obtain ⟨j, hcj, t, htQ, z, hz⟩ := hloc Q hQ hQ1 hbQ
    obtain ⟨a, ha⟩ := hx j hcj
    refine ⟨t, htQ, ?_⟩
    have hj0 : algebraMap A' B' j ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hz
      rcases mul_eq_zero.1 hz with h | h
      · exact htQ (h ▸ Q.zero_mem)
      · exact hc0 h
    have hx' : algebraMap A' B' x * algebraMap A' B' j = b * c * algebraMap A' B' a := by
      rw [← map_mul, ha, map_mul, hbc]
    refine ⟨algebraMap A' B' a * z, mul_left_cancel₀ hj0 ?_⟩
    linear_combination t * hx' + b * algebraMap A' B' a * hz)
  rw [Submonoid.mem_bot] at hu
  subst hu
  simpa using hdiv

end GlobalTheory.DivDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsAllPrimesOfClosedFibre
section
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

open GlobalTheory.LocAcyc in
open CategoryTheory in

theorem divConstAll_of_divConstLocal : DivConstLocal → DivConstAll := by
  intro hL T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH
  set p : Ideal T := P.comap (C : T →+* T[X]) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let T' := Localization.AtPrime p
  have hle : p.primeCompl ≤ nonZeroDivisors T := p.primeCompl_le_nonZeroDivisors
  have hAIC' : AbsIntClosed T' :=
    ((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl
      (fun h => h (zero_mem p))).2
  have hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a) := fun a => by
    rw [IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s) := by
    intro s
    have hs : C (s : T) ∈ P.primeCompl := s.2
    have hu := (IsLocalization.map_units (Localization.AtPrime P)
      (⟨C (s : T), hs⟩ : P.primeCompl)).map φ
    rw [← RingHom.comp_apply, hφ] at hu
    rwa [hTO]
  letI : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra
  haveI : IsScalarTower T T' O :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  letI : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra
  haveI : IsScalarTower T' T'[X] O :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)
      rw [Polynomial.algebraMap_eq, eval₂_C])
  letI : Algebra T[X] T'[X] := Polynomial.algebra T T'
  haveI : IsLocalization (Submonoid.map C p.primeCompl) T'[X] :=
    Polynomial.isLocalization p.primeCompl T'
  have hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'
  haveI hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj
  have hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P :=
    IsLocalization.comap_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj
  have hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a) := fun a => by
    change _ = (C a).map (algebraMap T T')
    rw [Polynomial.map_C]
  have hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T' := by
    rw [← IsLocalization.map_comap p.primeCompl T' (P'.comap C),
      ← IsLocalization.map_comap p.primeCompl T' (maximalIdeal T'),
      IsLocalization.AtPrime.comap_maximalIdeal T' p]
    congr 1
    ext a
    change C (algebraMap T T' a) ∈ P' ↔ C a ∈ P
    rw [hCcomm, ← Ideal.mem_comap, hcomapP']
  haveI : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'
    have hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomapP']
    unfold IsLocalization.AtPrime at this ⊢
    rw [hc] at this
    exact this
  let e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  let φ' : Localization.AtPrime P' →+* O := φ.comp e.symm.toRingEquiv.toRingHom
  have hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _
      rw [Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _
      rw [Polynomial.map_X, eval₂_X]
  have hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O := by
    refine IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]
    refine RingHom.ext fun f => ?_
    change φ (e.symm (algebraMap T[X] _ f)) = _
    rw [AlgEquiv.commutes, ← RingHom.comp_apply, hφ]
  have hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hSH
    refine ⟨h1, h2, ?_, ?_⟩
    · refine ⟨fun a ha => ?_⟩
      change IsUnit (φ (e.symm a)) at ha
      have h5 : IsUnit (e.symm a) := h3.map_nonunit _ ha
      simpa using h5.map e
    · haveI : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢
      rw [CommRingCat.ofHom_comp]
      haveI : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) :=
        inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)
      exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4
  have key : DivConst T' O := hL T' O hAIC' P' φ' hφ' hSH' hmax trivial

  have hinj : Function.Injective (algebraMap T T') := IsLocalization.injective T' hle
  intro b c s hs hbc
  have hs' : algebraMap T T' s ≠ 0 := fun h => hs (hinj (by rw [h, map_zero]))
  rw [IsScalarTower.algebraMap_apply T T' O] at hbc
  obtain ⟨a', w, hb⟩ := key b c _ hs' hbc
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a'
  obtain ⟨v, hv⟩ := hunit u
  refine ⟨a, v⁻¹ * w, ?_⟩
  rw [hb, Units.val_mul, ← mul_assoc]
  congr 1
  rw [Units.eq_mul_inv_iff_mul_eq, hv, IsScalarTower.algebraMap_apply T T' O a,
    IsScalarTower.algebraMap_apply T T' O u, ← map_mul, IsLocalization.mk'_spec]

end GlobalTheory.VertUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsClosedPointsOfOrigin
section
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem divConstClosedPts_of_divConstOrigin :
    GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  intro hKO
  unfold GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith at hKO
  unfold GlobalTheory.VertUnits.DivConstClosedPts GlobalTheory.VertUnits.DivConstWith
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne
  have hne' : P ≠ (maximalIdeal T).map (C : T →+* T[X]) := hne
  haveI hac : IsAlgClosed (ResidueField T) :=
    (GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩).2.1
  obtain ⟨c, hc⟩ := GlobalTheory.LocAcyc.Translate.exists_X_sub_C_mem T P hPm hne'
  let τ : T[X] ≃ₐ[T] T[X] := algEquivAevalXAddC (-c)
  have hτX : τ X = X - C c := by simp [τ, sub_eq_add_neg]
  have hτC : ∀ a : T, τ (C a) = C a := fun a => τ.commutes a
  let P' : Ideal T[X] := P.comap (τ : T[X] →+* T[X])
  haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
  have hP'C : P'.comap (C : T →+* T[X]) = maximalIdeal T := by
    rw [← hPm]; ext a
    simp only [Ideal.mem_comap, P']
    rw [show ((τ : T[X] →+* T[X]) (C a)) = C a from hτC a]
  have hXP' : (X : T[X]) ∈ P' := by
    simp only [P', Ideal.mem_comap]
    rw [show ((τ : T[X] →+* T[X]) X) = X - C c from hτX]; exact hc
  have hP' : P' = (maximalIdeal T).map (C : T →+* T[X]) ⊔ Ideal.span {X} := by
    apply le_antisymm
    · intro p hp
      have hd : p - C (p.coeff 0) ∈ Ideal.span {(X : T[X])} := Ideal.mem_span_singleton.2 X_dvd_sub_C
      have hc0 : C (p.coeff 0) ∈ P' := by
        have h1 : p - C (p.coeff 0) ∈ P' := by
          obtain ⟨u, hu⟩ := (X_dvd_sub_C : X ∣ p - C (p.coeff 0))
          rw [hu]; exact P'.mul_mem_right _ hXP'
        have := P'.sub_mem hp h1
        simpa using this
      have hc0' : p.coeff 0 ∈ maximalIdeal T := by rw [← hP'C]; exact hc0
      have : p = C (p.coeff 0) + (p - C (p.coeff 0)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc0')) (Ideal.mem_sup_right hd)
    · refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, hP'C]
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hXP'

  let f' : T[X] →+* O := (algebraMap T[X] O).comp (τ : T[X] →+* T[X])
  let alg' : Algebra T[X] O := f'.toAlgebra
  have tower' : @IsScalarTower T T[X] O _ alg'.toSMul _ := by
    refine @IsScalarTower.of_algebraMap_eq T T[X] O _ _ _ _ alg' _ ?_
    intro x
    change algebraMap T O x = f' (algebraMap T T[X] x)
    simp only [f', RingHom.comp_apply]
    rw [show (τ : T[X] →+* T[X]) (algebraMap T T[X] x) = algebraMap T T[X] x from τ.commutes x,
      ← IsScalarTower.algebraMap_apply]

  have hmap : P'.primeCompl.map (τ : T[X] ≃+* T[X]).toMonoidHom = P.primeCompl := by
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨(τ : T[X] ≃+* T[X]).symm x, ?_, by simp⟩
      change (τ : T[X] →+* T[X]) ((τ : T[X] ≃+* T[X]).symm x) ∉ P
      have hx' : x ∉ P := hx
      convert hx' using 2
      exact (τ : T[X] ≃+* T[X]).apply_symm_apply x
  let Lq : Localization.AtPrime P' ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv _ _ (τ : T[X] ≃+* T[X]) hmap
  let φ' : Localization.AtPrime P' →+* O := φ.comp (Lq : Localization.AtPrime P' →+* Localization.AtPrime P)
  have hφ' : φ'.comp (algebraMap T[X] (Localization.AtPrime P')) = f' := by
    refine RingHom.ext fun x => ?_
    simp only [φ', f', RingHom.comp_apply]
    rw [show (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) (algebraMap T[X] _ x)
        = algebraMap T[X] (Localization.AtPrime P) ((τ : T[X] ≃+* T[X]) x) from
      IsLocalization.ringEquivOfRingEquiv_eq _ x]
    rw [← RingHom.comp_apply φ, hφ]
    rfl
  have hsh' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hsh
    refine ⟨h1, h2, ?_, ?_⟩
    · haveI := h3
      haveI : IsLocalHom (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) :=
        ⟨fun a ha => by simpa using ha.map (Lq.symm : Localization.AtPrime P →+* Localization.AtPrime P')⟩
      exact RingHom.isLocalHom_comp _ _
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      have h5 := CategoryTheory.MorphismProperty.RespectsIso.precomp
        (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
        Lq.toCommRingCatIso.hom (CommRingCat.ofHom φ) h4
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
      convert h5 using 1
      rfl
  exact @hKO T O _ _ _ _ _ _ alg' tower' hT P' hP'p φ' hφ' hsh' hP'C hP'

end GlobalTheory.VertUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfTwistedEq
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem dvd_of_twisted_eq :
    ∀ (R : Type) [CommRing R] (ψ : R →+* R) (m Δ Δs Δ' g b : R), m ∈ nonZeroDivisors R →
      Δ * Δs = m → Δ = g * ψ Δ → Δ' = g * b * ψ Δ' →
      (∀ z w : R, z * ψ m = m * w * ψ z → m ∣ z) → Δ ∣ Δ' := by
  intro R _ ψ m Δ Δs Δ' g b hm hmul hΔ hΔ' key
  have hz : (Δ' * Δs) * ψ m = m * b * ψ (Δ' * Δs) := by
    have h1 : Δ' * ψ Δ = b * ψ Δ' * Δ := by
      calc Δ' * ψ Δ = (g * b * ψ Δ') * ψ Δ := by rw [← hΔ']
        _ = b * ψ Δ' * (g * ψ Δ) := by ring
        _ = b * ψ Δ' * Δ := by rw [← hΔ]
    rw [← hmul, map_mul, map_mul]
    calc Δ' * Δs * (ψ Δ * ψ Δs) = (Δ' * ψ Δ) * (Δs * ψ Δs) := by ring
      _ = (b * ψ Δ' * Δ) * (Δs * ψ Δs) := by rw [h1]
      _ = Δ * Δs * b * (ψ Δ' * ψ Δs) := by ring
  obtain ⟨c, hc⟩ := key _ _ hz
  refine ⟨c, ?_⟩
  have hzero : (Δ' - Δ * c) * m = 0 := by
    have : (Δ' - Δ * c) * Δs = 0 := by
      rw [sub_mul, hc, ← hmul]; ring
    calc (Δ' - Δ * c) * m = ((Δ' - Δ * c) * Δs) * Δ := by rw [← hmul]; ring
      _ = 0 := by rw [this, zero_mul]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp hm) _ hzero)

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenSublatticeFreeLatticeIffEvalStatement
section
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenSublattice_freeLattice_iff_eval : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (τ : S), Function.Injective a → Function.Injective (evalVec (liftA hv a) N) → (∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) → ∀ y : Fin N → C, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔ ∃ z ∈ eigSub (liftA hv a) τ (Fin N → RS (liftA hv a)), (fun i => ((comp (liftA hv a) N τ z i : Int0 v) : C)) = y := by
  first | exact @GlobalTheory.EigenSubEval.eigenSub_iff_eval | exact GlobalTheory.EigenSubEval.eigenSub_iff_eval | (intros; apply GlobalTheory.EigenSubEval.eigenSub_iff_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspacesOfRingHomsIndependentStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspaces_of_ring_homs_independent : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), Function.Injective (algebraMap O C) → iSupIndep (fun σ : Λ →+* O => eig C (⇑ρ) σ) := by
  first | exact @GlobalTheory.iSupIndep_eig | exact GlobalTheory.iSupIndep_eig | (intros; apply GlobalTheory.iSupIndep_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSumIntegralCubeDerivativesStatement
section
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_sum_integral_cube_derivatives_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (s : ℝ), 0 < s → ∀ (N : ℕ) (c : Fin N → ℝ → G), (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ (J : Type) (_ : Fintype J) (κ : J → (Fin N → ℝ) → ℂ) (l : J → List (Fin N)), (∀ j, Continuous (κ j)) ∧ ∀ (d : Fin N → K → K) (S : Set K), (∀ v ∈ S, ∀ i, d i v ∈ S ∧ HasDerivAt (fun t : ℝ => ρ (c i t) v) (d i v) 0) → ∀ v ∈ S, v = ∑ j, ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), κ j t • ρ (List.ofFn fun i => c i (t i)).prod ((l j).foldr d v) := by
  first | exact @GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives | exact GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives | (intros; apply GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRelStatement
section
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivalence_generated_torus_rel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t}), Relation.EqvGen (fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G L M a.1 b.1) a b → TEquiv (IsCMField.complexConj E) G L M a.1 b.1 := by
  first | exact @GlobalTheory.UCls.torus_eqvGen_main | exact GlobalTheory.UCls.torus_eqvGen_main | (intros; apply GlobalTheory.UCls.torus_eqvGen_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayQuotientEqLocalizationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.away_quotient_span_eq_localization : ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D] (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → f ∈ P → ∀ (Q : Ideal D), Q.IsPrime → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∃ g : D, (∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Ideal.span {algebraMap B (Localization.Away g) f}) ∧ ∀ b : B, algebraMap B (Localization.Away g) b ∈ Ideal.span {algebraMap B (Localization.Away g) f} ↔ ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.etale_away_quotient_eq_localization) | (exact GlobalTheory.etale_away_quotient_eq_localization) | (intros; apply GlobalTheory.etale_away_quotient_eq_localization  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeTensorOfLowHeightStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_localizationAtPrime_tensor_of_low_height : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] (Q : Ideal O) [Q.IsPrime],
    GlobalTheory.GoodEtale.EtaleLow A R C → ((Q.comap (algebraMap R O)).comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) := by
  first | (exact @GlobalTheory.GoodEtale.etale_localization_of_etaleLow) | (exact GlobalTheory.GoodEtale.etale_localization_of_etaleLow) | (intros; apply GlobalTheory.GoodEtale.etale_localization_of_etaleLow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationOfInjectiveCokernelKilledStatement
section
open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_localization_of_injective_cokernel_killed : ∀ (S : Type) [CommRing S] (A B : Type) [CommRing A] [CommRing B] [Algebra S A] [Algebra S B] (ι : A →ₐ[S] B), Function.Injective ι → ∀ (p : Ideal S) [p.IsPrime] (s : S), s ∉ p → (∀ y : B, s • y ∈ ι.range) → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A) → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) B) := by
  first | exact @GlobalTheory.etale_localization_of_cokernel_killed | exact GlobalTheory.etale_localization_of_cokernel_killed | (intros; apply GlobalTheory.etale_localization_of_cokernel_killed <;> assumption)
end

