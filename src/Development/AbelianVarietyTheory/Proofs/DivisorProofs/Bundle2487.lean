import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenPreimageEqBaseChangeSqZeroAugmentation
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroBC

theorem preimage_surj : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U := by
  intro R₀ R₁ _ _ _ q hq X₀ X₁ s₀ s₁ pr hp U
  have hqs : Function.Surjective (q : R₁ →+* R₀) := fun x ↦ ⟨algebraMap R₀ R₁ x, q.commutes x⟩
  have hid : spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁) = 𝟙 (Sp R₀) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (q : R₁ →+* R₀).comp (algebraMap R₀ R₁) = RingHom.id R₀ := RingHom.ext fun x ↦ q.commutes x
    rw [this]
    exact Spec.map_id _
  let σ : X₀ ⟶ X₁ := hp.lift (𝟙 X₀) (s₀ ≫ spMap (q : R₁ →+* R₀)) (by rw [Category.id_comp, Category.assoc, hid, Category.comp_id])
  have hσ : σ ≫ pr = 𝟙 X₀ := hp.lift_fst _ _ _
  have hσ2 : σ ≫ s₁ = s₀ ≫ spMap (q : R₁ →+* R₀) := hp.lift_snd _ _ _
  have hout : IsPullback (σ ≫ pr) s₀ s₀ (spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁)) := by
    rw [hσ, hid]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hleft : IsPullback σ s₀ s₁ (spMap (q : R₁ →+* R₀)) := IsPullback.of_right hout hσ2 hp
  have hk2 : RingHom.ker (q : R₁ →+* R₀) ^ 2 = 0 := by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    rw [Ideal.mem_bot]
    exact hq a b (RingHom.mem_ker.1 ha) (RingHom.mem_ker.1 hb)
  have hsurj : Surjective σ := surjective_of_isPullback_sqZero hk2 hqs rfl hleft
  refine ⟨σ ⁻¹ᵁ U, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hsurj.surj x
  have e : pr (σ y) = y := by
    have := congrArg (fun f : X₀ ⟶ X₀ ↦ f y) hσ
    simpa only [Scheme.Hom.comp_apply] using this.trans (by simp)
  change σ (pr (σ y)) ∈ U ↔ σ y ∈ U
  rw [e]

end GlobalTheory.SqZeroBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensPreimageEqOfSqZeroAugmentation
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_opens_preimage_eq_of_sqZero_aug (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
    (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀)
    (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (W : X₁.Opens) :
    ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W := by
  have hcomp : (q : R₁ →+* R₀).comp (algebraMap R₀ R₁) = RingHom.id R₀ := RingHom.ext fun r ↦ q.commutes r
  have hsp : spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁) = 𝟙 (Sp R₀) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    exact Spec.map_id _
  let i : X₀ ⟶ X₁ := hp.lift (𝟙 X₀) (s₀ ≫ spMap (q : R₁ →+* R₀))
    (by rw [Category.id_comp, Category.assoc, hsp, Category.comp_id])
  have hi1 : i ≫ pr = 𝟙 X₀ := hp.lift_fst _ _ _
  have hi2 : i ≫ s₁ = s₀ ≫ spMap (q : R₁ →+* R₀) := hp.lift_snd _ _ _
  have hout : IsPullback (i ≫ pr) s₀ s₀ (spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁)) := by
    rw [hi1, hsp]; exact IsPullback.id_horiz s₀
  have hsq : IsPullback i s₀ s₁ (spMap (q : R₁ →+* R₀)) := IsPullback.of_right hout hi2 hp
  have hsurj : Function.Surjective (q : R₁ →+* R₀) := fun r ↦ ⟨algebraMap R₀ R₁ r, q.commutes r⟩
  have hI : (RingHom.ker (q : R₁ →+* R₀)) ^ 2 = 0 := by
    rw [sq, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro y hy y' hy'
    exact (Ideal.mem_bot).2 (hq y y' (RingHom.mem_ker.1 hy) (RingHom.mem_ker.1 hy'))
  have hisurj : Surjective i := surjective_of_isPullback_sqZero hI hsurj rfl hsq
  have key : ∀ x : X₁, i.base (pr.base x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := hisurj.surj x
    have h : pr.base (i.base y) = y := by rw [← Scheme.Hom.comp_apply, hi1]; rfl
    rw [h]
  refine ⟨i ⁻¹ᵁ W, ?_⟩
  ext x
  change i.base (pr.base x) ∈ W ↔ x ∈ W
  rw [key]

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrdQEqOrdDivOfRationalCombination
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem exists_ordQ_eq_ord_div : ∀ {k K : Type} [Field k] [Field K] (c : k →+* K) (φ : K →₀ ℚ),
    φ 0 = 0 → ∃ (m : ℕ) (g : Kˣ), 0 < m ∧ ∀ E : Place c, E.ordQ φ = (E.ord (g : K) : ℚ) / m := by
  intro k K _ _ c φ
  induction φ using Finsupp.induction with
  | zero => intro _; exact ⟨1, 1, one_pos, fun E => by simp⟩
  | single_add a b f ha hb ih =>
    intro h0
    have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero] at h0
      exact hb h0
    have hf0 : f 0 = 0 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm ha0), zero_add] at h0
      exact h0
    obtain ⟨m, g, hm, hg⟩ := ih hf0
    refine ⟨m * b.den, g ^ b.den * (Units.mk0 a ha0) ^ (b.num * m), ?_, fun E => ?_⟩
    · exact Nat.mul_pos hm b.pos
    · have hd : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.pos.ne'
      have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      rw [map_add, Place.ordQ_single, hg E, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_zpow_eq_zpow_val, E.ord_mul (pow_ne_zero _ g.ne_zero)
          (zpow_ne_zero _ (Units.mk0 a ha0).ne_zero), E.ord_pow, E.ord_zpow, Units.val_mk0]
      push_cast
      rw [← Rat.mul_den_eq_num b]
      field_simp
      ring

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermutationLeadingMinors
section
namespace GlobalTheory

open Matrix

theorem exists_isUnit_of_isUnit_sum_localRing {R : Type} [CommRing R] [IsLocalRing R]
    {ι : Type} (s : Finset ι) (f : ι → R) (h : IsUnit (∑ i ∈ s, f i)) :
    ∃ i ∈ s, IsUnit (f i) := by
  by_contra hne
  push_neg at hne
  apply (IsLocalRing.mem_maximalIdeal _).mp _ h
  exact Ideal.sum_mem _ fun i hi => (IsLocalRing.mem_maximalIdeal _).mpr (hne i hi)

theorem exists_perm_isUnit_leading_minors_localRing :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R),
      IsUnit M.det → ∃ w : Equiv.Perm (Fin m), ∀ (k : ℕ) (hk : k ≤ m),
        IsUnit ((M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
  intro R _ _ m
  induction m with
  | zero =>
    intro M _
    refine ⟨1, fun k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    simp
  | succ n ih =>
    intro M hM
    rw [Matrix.det_succ_row M (Fin.last n)] at hM
    obtain ⟨j, -, hj⟩ := exists_isUnit_of_isUnit_sum_localRing _ _ hM
    have hN := isUnit_of_mul_isUnit_right hj
    rw [Fin.succAbove_last] at hN
    obtain ⟨v, hv⟩ := ih _ hN
    let f : Fin (n + 1) → Fin (n + 1) := fun i =>
      if h : i = Fin.last n then j else j.succAbove (v (i.castPred h))
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      by_cases ha : a = Fin.last n <;> by_cases hb : b = Fin.last n
      · rw [ha, hb]
      · simp only [ha, hb, dite_true, dite_false] at hab
        exact absurd hab.symm (Fin.succAbove_ne _ _)
      · simp only [ha, hb, dite_true, dite_false] at hab
        exact absurd hab (Fin.succAbove_ne _ _)
      · simp only [ha, hb, dite_false] at hab
        have := v.injective (Fin.succAbove_right_injective hab)
        exact Fin.castPred_inj.mp this
    let w : Equiv.Perm (Fin (n + 1)) :=
      Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
    refine ⟨w, fun k hk => ?_⟩
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hk' : k ≤ n := Nat.lt_succ_iff.mp hlt
      have heq : (M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk) =
          ((M.submatrix Fin.castSucc j.succAbove).submatrix id v).submatrix
            (Fin.castLE hk') (Fin.castLE hk') := by
        ext a b
        have hb : Fin.castLE hk b ≠ Fin.last n := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp only [submatrix_apply, id, w, Equiv.ofBijective_apply, f, hb, dite_false]
        congr 2
        all_goals (ext; simp)
      rw [heq]
      exact hv k hk'
    · obtain rfl : k = n + 1 := le_antisymm hk hge
      have : Fin.castLE hk = id := Fin.castLE_rfl _
      rw [this, Matrix.submatrix_id_id, Matrix.det_permute']
      refine IsUnit.mul ?_ ?_
      · rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [h]
      · rw [Matrix.det_succ_row M (Fin.last n)]
        exact hM

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceDominatingLocalDomainComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.DvrDom

theorem exists_fractions_of_essFiniteType : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (O : Subring κ) (hc : ∀ a : ℂ, algebraMap ℂ κ a ∈ O), ((algebraMap ℂ κ).codRestrict O hc).EssFiniteType → ∃ G : Finset κ, (∀ x ∈ G, x ∈ O) ∧ ∀ o ∈ O, ∃ b ∈ Algebra.adjoin ℂ (G : Set κ), ∃ d ∈ Algebra.adjoin ℂ (G : Set κ), d ≠ 0 ∧ d⁻¹ ∈ O ∧ o = b / d := by
  classical
  intro κ _ _ O hc h
  letI : Algebra ℂ O := ((algebraMap ℂ κ).codRestrict O hc).toAlgebra
  have h' : Algebra.EssFiniteType ℂ O := h
  obtain ⟨s, hs⟩ := h'.cond
  refine ⟨s.image (fun x : O => (x : κ)), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have key : ∀ x ∈ Algebra.adjoin ℂ (s : Set O),
      ((x : O) : κ) ∈ Algebra.adjoin ℂ ((s.image (fun x : O => (x : κ)) : Finset κ) : Set κ) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Algebra.subset_adjoin
      rw [Finset.coe_image]
      exact ⟨x, hx, rfl⟩
    | algebraMap r => exact Subalgebra.algebraMap_mem _ r
    | add x y _ _ hx hy => simpa using Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => simpa using Subalgebra.mul_mem _ hx hy
  intro v hv
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj
    (Submonoid.comap (algebraMap (↥(Algebra.adjoin ℂ (s : Set O))) O) (IsUnit.submonoid O)) (⟨v, hv⟩ : O)
  have hu : IsUnit ((m : Algebra.adjoin ℂ (s : Set O)) : O) := m.2
  obtain ⟨u, hu'⟩ := hu
  have hinv : (((m : Algebra.adjoin ℂ (s : Set O)) : O) : κ) * (((u⁻¹ : Oˣ) : O) : κ) = 1 := by
    rw [← hu']
    change (((u : O) * ((u⁻¹ : Oˣ) : O) : O) : κ) = ((1 : O) : κ)
    rw [u.mul_inv]
  have hd0 : (((m : Algebra.adjoin ℂ (s : Set O)) : O) : κ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have hmL := congrArg (fun z : O => (z : κ)) hm
  simp only at hmL
  refine ⟨((a : O) : κ), key _ a.2, (((m : Algebra.adjoin ℂ (s : Set O)) : O) : κ),
    key _ (m : Algebra.adjoin ℂ (s : Set O)).2, hd0, ?_, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((u⁻¹ : Oˣ) : O).2
  · rw [eq_div_iff hd0]
    simpa using hmL

theorem exists_minimal_prime_le : ∀ {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (a : R), a ≠ 0 → a ∈ P → ∃ Q : Ideal R, Q.IsPrime ∧ a ∈ Q ∧ Q ≤ P ∧ Q ≠ ⊥ ∧ ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ Q → p = Q := by
  intro R _ _ _ P _ a ha haP
  have hle : Ideal.span {a} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 haP
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hle
  have hQp : Q.IsPrime := hQ.1.1
  have haQ : a ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self a)
  have hQ0 : Q ≠ ⊥ := fun h => ha (by rw [h] at haQ; exact (Ideal.mem_bot).1 haQ)
  have hht : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
  refine ⟨Q, hQp, haQ, hQP, hQ0, fun p hp hp0 hpQ => ?_⟩
  by_contra hne
  have hlt : p < Q := lt_of_le_of_ne hpQ hne
  haveI := hp
  haveI := hQp
  have h1 : p.height + 1 ≤ Q.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hp1 : 1 ≤ p.height :=
    Order.one_le_iff_ne_zero.mpr (fun h => hp0 (Ideal.height_eq_zero_iff_eq_bot.1 h))
  have h2 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left hp1 1).trans (h1.trans hht)
  exact absurd h2 (by decide)

theorem exists_place_dominating : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (O : Subring κ) (hO : IsLocModel (algebraMap ℂ κ) O), letI := hO.isLocalRing;
  ¬ IsField O → ∃ F : Place (algebraMap ℂ κ), F.Contains O ∧ ∀ f : O, f ∈ IsLocalRing.maximalIdeal O → (f : κ) ≠ 0 → 0 < F.ord f := by
  intro κ _ _ O hO
  letI := hO.isLocalRing
  intro hnf
  classical
  obtain ⟨G, hGO, hGfrac⟩ := exists_fractions_of_essFiniteType O hO.const_mem hO.essFiniteType
  letI : Algebra ℂ O := ((algebraMap ℂ κ).codRestrict O hO.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ O := hO.essFiniteType
  haveI : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℂ O
  obtain ⟨Y, hY⟩ := (IsNoetherian.noetherian (IsLocalRing.maximalIdeal O) :
    (IsLocalRing.maximalIdeal O).FG)

  obtain ⟨V, hOV⟩ := (LocalSubring.mk O).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := (LocalSubring.le_def).1 hOV
  have hOV' : ∀ x ∈ O, x ∈ V := fun x hx => hle hx
  have hVnu : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O → ∀ hx : (x : κ) ∈ V,
      (⟨x, hx⟩ : V) ∈ IsLocalRing.maximalIdeal V := by
    intro x hxm hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hxm
    exact hxm (hloc.map_nonunit x hu)

  have hm0 : IsLocalRing.maximalIdeal O ≠ ⊥ := fun h =>
    hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
  let Y' : Finset O := Y.filter (fun y : O => (y : κ) ≠ 0)
  have hY'ne : Y'.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply hm0
    rw [← hY, Submodule.span_eq_bot]
    intro y hy
    by_contra hy0
    have : y ∈ Y' := Finset.mem_filter.2 ⟨hy, fun h => hy0 (Subtype.ext h)⟩
    rw [hne] at this
    exact absurd this (Finset.notMem_empty _)
  obtain ⟨a, haY', hamax⟩ := Y'.exists_max_image (fun y : O => V.valuation (y : κ)) hY'ne
  obtain ⟨haY, ha0⟩ := Finset.mem_filter.1 haY'
  have hdivV : ∀ y ∈ Y, (y : κ) / a ∈ V := by
    intro y hy
    by_cases hy0 : (y : κ) = 0
    · rw [hy0, zero_div]; exact V.zero_mem
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
    have h1 := hamax y (Finset.mem_filter.2 ⟨hy, hy0⟩)
    have h2 : V.valuation (a : κ) ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
    exact (div_le_one₀ (zero_lt_iff.2 h2)).2 h1

  let T : Finset κ := G ∪ Y.image (fun y : O => (y : κ)) ∪ Y.image (fun y : O => (y : κ) / a)
  have hTV : ∀ x ∈ T, x ∈ V := by
    intro x hx
    simp only [T, Finset.mem_union, Finset.mem_image] at hx
    rcases hx with (hx | ⟨y, -, rfl⟩) | ⟨y, hy, rfl⟩
    · exact hOV' x (hGO x hx)
    · exact hOV' _ y.2
    · exact hdivV y hy
  have hGT : Algebra.adjoin ℂ (G : Set κ) ≤ Algebra.adjoin ℂ (T : Set κ) :=
    Algebra.adjoin_mono (by intro x hx; simp [T, Finset.mem_coe.1 hx])
  have hfracT : ∀ f : κ, ∃ u ∈ Algebra.adjoin ℂ (T : Set κ), ∃ v ∈ Algebra.adjoin ℂ (T : Set κ),
      v ≠ 0 ∧ f * v = u := by
    intro f
    obtain ⟨x, hx, z, hz, hz0, hfz⟩ := hO.frac f
    obtain ⟨b, hb, d, hd, hd0, -, rfl⟩ := hGfrac x hx
    obtain ⟨b', hb', d', hd', hd0', -, rfl⟩ := hGfrac z hz
    have hb0' : b' ≠ 0 := by rintro rfl; exact hz0 (zero_div _)
    refine ⟨b * d', Subalgebra.mul_mem _ (hGT hb) (hGT hd'), b' * d,
      Subalgebra.mul_mem _ (hGT hb') (hGT hd), mul_ne_zero hb0' hd0, ?_⟩
    field_simp at hfz
    linear_combination hfz
  have hcV : ∀ z : ℂ, algebraMap ℂ κ z ∈ V := fun z => hOV' _ (hO.const_mem z)
  obtain ⟨R, hcR, hft, hTR, hRV, hRn, hRi, hRf⟩ := GlobalTheory.T.exists_normal_finiteType_subring_le_valuationSubring' V T hcV hTV hfracT
  haveI := hRn
  haveI := hRi
  haveI := hRf
  have hadjR : ∀ x ∈ Algebra.adjoin ℂ (T : Set κ), x ∈ R := by
    let R' : Subalgebra ℂ κ := { R with algebraMap_mem' := hcR }
    have : Algebra.adjoin ℂ (T : Set κ) ≤ R' := Algebra.adjoin_le (fun x hx => hTR x hx)
    exact fun x hx => this hx

  let ι : R →+* V :=
    { toFun := fun r => ⟨r, hRV r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let P : Ideal R := (IsLocalRing.maximalIdeal V).comap ι
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have haT : (a : κ) ∈ T := by simp [T, haY]
  let a' : R := ⟨a, hTR _ haT⟩
  have ha'0 : a' ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
  have ha'P : a' ∈ P := hVnu a (hY ▸ Submodule.subset_span haY) _
  obtain ⟨Q, hQp, haQ, hQP, hQ0, hmin⟩ := exists_minimal_prime_le P a' ha'0 ha'P
  haveI := hQp
  obtain ⟨W, hWd, hRW, hinvW, hninvW, hWfrac⟩ := GlobalTheory.T.exists_dvr_localization_of_minimal_prime' R Q hQ0 hmin

  have hcW : ∀ z : ℂ, algebraMap ℂ κ z ∈ W := fun z => hRW ⟨_, hcR z⟩
  have hWft : ((algebraMap ℂ κ).codRestrict W hcW).EssFiniteType :=
    GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div κ (algebraMap ℂ κ) R hcR W hcW
      (fun x hx => hRW ⟨x, hx⟩) hft (fun e he => by
        obtain ⟨b, s, hs, rfl⟩ := hWfrac e he
        exact ⟨b, b.2, s, s.2, hinvW s hs, rfl⟩)
  let F : Place (algebraMap ℂ κ) := ⟨W, hcW, hWd, hWft⟩
  have hOW : ∀ o ∈ O, o ∈ W := by
    intro o ho
    obtain ⟨b, hb, d, hd, hd0, hdi, rfl⟩ := hGfrac o ho
    let d' : R := ⟨d, hadjR _ (hGT hd)⟩
    have hd'Q : d' ∉ Q := by
      intro hdQ
      have hm : ι d' ∈ IsLocalRing.maximalIdeal V := hQP hdQ
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
      apply hm
      exact IsUnit.of_mul_eq_one (⟨d⁻¹, hOV' _ hdi⟩ : V) (Subtype.ext (mul_inv_cancel₀ hd0))
    rw [div_eq_mul_inv]
    exact mul_mem (hRW ⟨b, hadjR _ (hGT hb)⟩) (hinvW d' hd'Q)
  refine ⟨F, hOW, ?_⟩
  intro f hf hf0
  have hspan : ∀ x ∈ Submodule.span O (Y : Set O), ∃ w ∈ W, ((x : O) : κ) = a * w := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      refine ⟨(y : κ) / a, hRW ⟨_, hTR _ ?_⟩, ?_⟩
      · simp only [T, Finset.mem_union, Finset.mem_image]
        exact Or.inr ⟨y, hy, rfl⟩
      · field_simp
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw, ex⟩ := hx
      obtain ⟨w', hw', ey⟩ := hy
      exact ⟨w + w', add_mem hw hw', by push_cast; rw [ex, ey]; ring⟩
    | smul c x _ hx =>
      obtain ⟨w, hw, ex⟩ := hx
      refine ⟨c * w, mul_mem (hOW _ c.2) hw, ?_⟩
      rw [smul_eq_mul, Subring.coe_mul, ex]; ring
  rw [← hY] at hf
  obtain ⟨w, hw, efw⟩ := hspan f hf
  have hw0 : w ≠ 0 := by rintro rfl; exact hf0 (by rw [efw, mul_zero])
  have haW : (a : κ) ∈ W := hRW a'
  have hainv : (a : κ)⁻¹ ∉ W := hninvW a' haQ ha'0
  have h1 : 0 ≤ F.ord (a : κ) := (F.ord_nonneg_iff ha0).2 haW
  have h2 : ¬ 0 ≤ F.ord ((a : κ)⁻¹) := fun h => hainv ((F.ord_nonneg_iff (inv_ne_zero ha0)).1 h)
  have h3 : 0 ≤ F.ord w := (F.ord_nonneg_iff hw0).2 hw
  rw [F.ord_inv] at h2
  rw [efw, F.ord_mul ha0 hw0]
  omega

end GlobalTheory.DvrDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatePrimitiveOfAmpleKTrivialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_translate_primitive_of_ample_K_trivial : ∀ (A : Type) [Field A] [IsAlgClosed A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  first | exact @GlobalTheory.PrimitiveNonSym.exists_point_translate_of_ample | exact GlobalTheory.PrimitiveNonSym.exists_point_translate_of_ample | (intros; apply GlobalTheory.PrimitiveNonSym.exists_point_translate_of_ample <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatesInOpenSemiAbelianLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_translates_in_open_semiAbelian_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ V : G.left.Opens, (∃ y₀ ∈ V, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ z : (G ⊗ G).left, (fst G G).left z = y ∧ (fst G G * snd G G).left z ∈ V ∧ (fst G G * (snd G G)⁻¹).left z ∈ V := by
  first | exact @GlobalTheory.ShearMeet.exists_fst_mul_mem | exact GlobalTheory.ShearMeet.exists_fst_mul_mem | (intros; apply GlobalTheory.ShearMeet.exists_fst_mul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDEqZeroSmoothAffineOpen
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq

theorem sec_exists_pow_of_D_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (U : X.affineOpens) (u : GlobalTheory.CechDR.Sec s U.1), KaehlerDifferential.D k (GlobalTheory.CechDR.Sec s U.1) u = 0 → ∃ h : GlobalTheory.CechDR.Sec s U.1, h ^ p = u := by
  intro p _ k _ _ hk X _ s _ U u hu
  haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s U.1) := by
    haveI : IsOpenImmersion (GlobalTheory.CechDR.affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
    have h : Smooth (GlobalTheory.CechDR.affPt s U ≫ s) := inferInstance
    rw [GlobalTheory.CechDR.affPt_w] at h
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h)
  by_cases hU : Nonempty U.1
  · haveI : IsDomain (GlobalTheory.CechDR.Sec s U.1) := IsIntegral.component_integral (X := X) U.1
    exact GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero_of_smooth_domain p k hk _ u hu
  · have e : U.1 = ⊥ := by
      ext x
      exact ⟨fun hx ↦ hU ⟨⟨x, hx⟩⟩, fun hx ↦ hx.elim⟩
    have hs : Subsingleton Γ(X, U.1) := by rw [e]; infer_instance
    haveI : Subsingleton (GlobalTheory.CechDR.Sec s U.1) := hs
    exact ⟨u, Subsingleton.elim _ _⟩

end GlobalTheory.ConjSeq
end

