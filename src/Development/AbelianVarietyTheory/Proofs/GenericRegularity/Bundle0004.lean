import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringLeDominatingOfFractionFiel
section
open IsLocalRing

namespace GlobalTheory

def compositeValuationSubring {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) : ValuationSubring L where
  toSubring := (V.toSubring.comap (residue W)).map W.subtype
  mem_or_inv_mem' := by
    intro x
    by_cases hx : x ∈ W
    · by_cases hx' : x⁻¹ ∈ W
      · rcases eq_or_ne x 0 with rfl | hx0
        · exact Or.inl (Subring.zero_mem _)
        have hmul : residue W ⟨x, hx⟩ * residue W ⟨x⁻¹, hx'⟩ = 1 := by
          rw [← map_mul, ← map_one (residue W)]
          congr 1
          exact Subtype.ext (mul_inv_cancel₀ hx0)
        rcases V.mem_or_inv_mem (residue W ⟨x, hx⟩) with h | h
        · exact Or.inl ⟨⟨x, hx⟩, h, rfl⟩
        · refine Or.inr ⟨⟨x⁻¹, hx'⟩, ?_, rfl⟩
          rw [← eq_inv_of_mul_eq_one_right hmul] at h
          exact h
      · refine Or.inl ⟨⟨x, hx⟩, ?_, rfl⟩
        have hm : (⟨x, hx⟩ : W) ∈ maximalIdeal W := by
          rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
          exact Or.inr hx'
        have h0 : residue W ⟨x, hx⟩ = 0 := (residue_eq_zero_iff _).2 hm
        change residue W ⟨x, hx⟩ ∈ V
        rw [h0]
        exact V.zero_mem
    · have hx' : x⁻¹ ∈ W := (W.mem_or_inv_mem x).resolve_left hx
      refine Or.inr ⟨⟨x⁻¹, hx'⟩, ?_, rfl⟩
      have hm : (⟨x⁻¹, hx'⟩ : W) ∈ maximalIdeal W := by
        rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
        exact Or.inr (by simpa using hx)
      have h0 : residue W ⟨x⁻¹, hx'⟩ = 0 := (residue_eq_zero_iff _).2 hm
      change residue W ⟨x⁻¹, hx'⟩ ∈ V
      rw [h0]
      exact V.zero_mem

theorem mem_compositeValuationSubring {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) (x : L) :
    x ∈ compositeValuationSubring W V ↔ ∃ h : x ∈ W, residue W ⟨x, h⟩ ∈ V := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hV⟩
    exact ⟨⟨x, h⟩, hV, rfl⟩

theorem compositeValuationSubring_le {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) : compositeValuationSubring W V ≤ W :=
  fun x hx => ((mem_compositeValuationSubring W V x).1 hx).1

theorem exists_valuationSubring_le_dominating {O L : Type*} [CommRing O] [IsLocalRing O]
    [Field L] (g : O →+* L) (W : ValuationSubring L) (hg : ∀ x, g x ∈ W) :
    ∃ W' : ValuationSubring L, W' ≤ W ∧ (∀ x : O, g x ∈ W') ∧
      ∀ x ∈ maximalIdeal O, g x ∈ W'.nonunits := by
  let g' : O →+* W := g.codRestrict W.toSubring hg
  let f : O →+* ResidueField W := (residue W).comp g'
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨compositeValuationSubring W V, compositeValuationSubring_le W V, fun x =>
    (mem_compositeValuationSubring W V _).2 ⟨hg x, hV x⟩, fun x hx => ?_⟩
  rw [ValuationSubring.mem_nonunits_iff_or]
  rcases eq_or_ne (g x) 0 with h0 | h0
  · exact Or.inl h0
  refine Or.inr fun hinv => ?_
  obtain ⟨h, hres⟩ := (mem_compositeValuationSubring W V _).1 hinv
  have hmul : f x * residue W ⟨(g x)⁻¹, h⟩ = 1 := by
    change residue W (g' x) * _ = 1
    rw [← map_mul, ← map_one (residue W)]
    congr 1
    exact Subtype.ext (mul_inv_cancel₀ h0)
  have hu : IsUnit (f.codRestrict V.toSubring hV x) :=
    isUnit_iff_exists_inv.2 ⟨⟨_, hres⟩, Subtype.ext hmul⟩
  exact (mem_maximalIdeal x).1 hx (hloc.1 x hu)

theorem exists_valuationSubring_le_dominating_of_fractionField :
    ∀ (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
      [Algebra O F] [IsFractionRing O F] [Field L] (ι : F →+* L) (W : ValuationSubring L),
      (∀ x, ι x ∈ W) → ∃ W' : ValuationSubring L, W' ≤ W ∧
        (∀ x : O, ι (algebraMap O F x) ∈ W') ∧
        ∀ x ∈ IsLocalRing.maximalIdeal O, ι (algebraMap O F x) ∈ W'.nonunits := by
  intro O F L _ _ _ _ _ _ _ ι W hW
  exact exists_valuationSubring_le_dominating (ι.comp (algebraMap O F)) W fun x => hW _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegralCoeffZeroMulOfAevalInv
section
namespace GlobalTheory

open Polynomial

open Polynomial in

theorem _root_.GlobalTheory.isIntegral_mul_of_bounded_at_points :
    ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [CharZero O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → (∀ (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B], Function.Injective (algebraMap O B) → ∀ I : Ideal B, I ≠ ⊤ → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O' V) (_ : Module.Finite O' V) (φ : B →+* V), φ.comp (algebraMap O B) = (algebraMap O' V).comp (algebraMap O O') ∧ φ e ≠ 0 ∧ ∀ x ∈ I, φ x ∈ IsLocalRing.maximalIdeal V) → ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω], Function.Injective (algebraMap O A) → ∀ (e : A), e ≠ 0 → ∀ f : Ω, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O' V] [Module.Finite O' V] (φ : A →+* V), φ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') → φ e ≠ 0 → ∀ a b : A, f * algebraMap A Ω b = algebraMap A Ω a → φ b ≠ 0 → φ b ∣ φ a) → ∃ s : A, s - 1 ∈ Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) ∧ IsIntegral A (algebraMap A Ω s * f) := by
  intro O O' _ _ _ _ _ _ _ _ _ _ _ hpts A Ω _ _ _ _ _ _ _ hOA e he f hf
  by_cases hf0 : f = 0
  · exact ⟨1, by simp, by simp [hf0, isIntegral_zero]⟩
  obtain ⟨d, c, hc, hdc⟩ := IsFractionRing.div_surjective (A := A) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  have hcΩ : algebraMap A Ω c ≠ 0 := (map_ne_zero_iff _ hinj).2 hc0
  have hfc : f * algebraMap A Ω c = algebraMap A Ω d := by rw [← hdc, div_mul_cancel₀ _ hcΩ]
  set g : Ω := f⁻¹ with hg
  have hgf : g * f = 1 := inv_mul_cancel₀ hf0
  have hgd : g * algebraMap A Ω d = algebraMap A Ω c := by
    rw [← hfc, ← mul_assoc, hgf, one_mul]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπm : π ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit
  let B := Algebra.adjoin A ({g} : Set Ω)
  letI : Algebra O B := ((algebraMap A B).comp (algebraMap O A)).toAlgebra
  haveI : IsScalarTower O A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType A B :=
    ⟨(Subalgebra.fg_top B).2 (by simpa using Subalgebra.fg_adjoin_finset (R := A) {g})⟩
  haveI : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have hOB : Function.Injective (algebraMap O B) := by
    intro x y hxy
    exact hOA (hinj (congrArg Subtype.val hxy))
  let gB : B := ⟨g, Algebra.self_mem_adjoin_singleton A g⟩
  let I : Ideal B := Ideal.span ({gB, algebraMap O B π} : Set B)
  have hI : I = ⊤ := by
    by_contra hI
    have hmI : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I := by
      rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le,
        Set.singleton_subset_iff]
      exact Ideal.subset_span (by simp)
    have hec : algebraMap A B (e * c) ≠ 0 := by
      intro h
      exact mul_ne_zero he hc0 (hinj (by simpa using congrArg Subtype.val h))
    obtain ⟨V, _, _, _, _, _, φ, hφ, hφe, hφI⟩ := hpts B hOB I hI hmI _ hec
    let ψ : A →+* V := φ.comp (algebraMap A B)
    have hψ : ψ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') := hφ
    have hψec : ψ e * ψ c ≠ 0 := by
      simpa [ψ, map_mul] using hφe
    have hψc : ψ c ≠ 0 := right_ne_zero_of_mul hψec
    obtain ⟨t, ht⟩ := hf V ψ hψ (left_ne_zero_of_mul hψec) d c hfc hψc
    have hmem : φ gB ∈ IsLocalRing.maximalIdeal V := hφI gB (Ideal.subset_span (by simp))
    have h1 : φ gB * ψ d = ψ c := by
      simp only [ψ, RingHom.comp_apply, ← map_mul]
      congr 1
      exact Subtype.ext hgd
    have hu : IsUnit (φ gB) := by
      refine IsUnit.of_mul_eq_one t ?_
      have h2 : ψ c * (φ gB * t) = ψ c * 1 := by linear_combination (-φ gB) * ht + h1
      exact mul_left_cancel₀ hψc h2
    exact ((IsLocalRing.mem_maximalIdeal _).1 hmem) hu
  have hone : (1 : B) ∈ I := hI ▸ Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hone
  have hpoly : ∀ x : B, ∃ p : A[X], aeval g p = (x : Ω) := by
    intro x
    have hx : (x : Ω) ∈ Algebra.adjoin A ({g} : Set Ω) := x.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    exact (AlgHom.mem_range _).1 hx
  obtain ⟨p, hp⟩ := hpoly a
  obtain ⟨r, hr⟩ := hpoly b
  have hΩ : (a : Ω) * g + (b : Ω) * algebraMap A Ω (algebraMap O A π) = 1 :=
    congrArg Subtype.val hab
  let H : A[X] := 1 - X * p - C (algebraMap O A π) * r
  have hH : aeval g H = 0 := by
    simp only [H, map_sub, map_one, map_mul, aeval_X, aeval_C, hp, hr]
    linear_combination -hΩ
  letI : Invertible g := invertibleOfNonzero (inv_ne_zero hf0)
  have hrev : aeval f (reverse H) = 0 := by
    have key := eval₂_reverse_mul_pow (algebraMap A Ω) g H
    have hinv : ⅟g = f := by rw [invOf_eq_inv, hg, inv_inv]
    rw [hinv, ← aeval_def, ← aeval_def, hH] at key
    exact (mul_eq_zero.1 key).resolve_right (pow_ne_zero _ (inv_ne_zero hf0))
  have hint := isIntegral_leadingCoeff_smul (reverse H) f hrev
  have hcoeff : H.coeff 0 = 1 - algebraMap O A π * r.coeff 0 := by simp [H]
  refine ⟨H.coeff 0, ?_, ?_⟩
  · rw [hcoeff, sub_sub_cancel_left]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπm))
  · by_cases h0 : H.coeff 0 = 0
    · rw [h0, map_zero, zero_mul]
      exact isIntegral_zero
    · have hlead : (reverse H).leadingCoeff = H.coeff 0 := by
        rw [reverse_leadingCoeff, trailingCoeff, natTrailingDegree_eq_zero.2 (Or.inr h0)]
      rw [← hlead, ← Algebra.smul_def]
      exact hint

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PolyChartSmoothFractionLift
section
namespace GlobalTheory

open MvPolynomial

section PolyChart

variable {K F₀ : Type} (V : Type) [Field K] [Field F₀] [Algebra K F₀] (R₀ : Subalgebra K F₀)

noncomputable def polyChartHom :
    MvPolynomial V R₀ →ₐ[K] FractionRing (MvPolynomial V F₀) :=
  (IsScalarTower.toAlgHom K (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))).comp
    (MvPolynomial.mapAlgHom R₀.val)

theorem polyChartHom_apply (p : MvPolynomial V R₀) :
    polyChartHom V R₀ p = algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
      (MvPolynomial.map (R₀.val : R₀ →+* F₀) p) := rfl

theorem polyChartHom_injective : Function.Injective (polyChartHom V R₀) := by
  intro p q h
  rw [polyChartHom_apply, polyChartHom_apply] at h
  exact MvPolynomial.map_injective _ Subtype.val_injective
    (IsFractionRing.injective (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) h)

theorem polyChartHom_C (a : R₀) :
    polyChartHom V R₀ (C a) = algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a := by
  rw [polyChartHom_apply, MvPolynomial.map_C,
    IsScalarTower.algebraMap_apply F₀ (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))]
  rfl

theorem polyChartHom_X (v : V) :
    polyChartHom V R₀ (X v) =
      algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (X v) := by
  rw [polyChartHom_apply, MvPolynomial.map_X]

theorem polyChartHom_range :
    (polyChartHom V R₀).range = Algebra.adjoin K
      ((algebraMap F₀ (FractionRing (MvPolynomial V F₀))) '' (R₀ : Set F₀) ∪
        Set.range fun v : V =>
          algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (X v)) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    change polyChartHom V R₀ p ∈ _
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [polyChartHom_C]
      exact Algebra.subset_adjoin (Or.inl ⟨a, a.2, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul, polyChartHom_X]
      exact mul_mem hp (Algebra.subset_adjoin (Or.inr ⟨v, rfl⟩))
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨a, ha, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨C ⟨a, ha⟩, polyChartHom_C V R₀ ⟨a, ha⟩⟩
    · exact ⟨X v, polyChartHom_X V R₀ v⟩

theorem polyChart_clear (h : ∀ x : F₀, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a)
    (p : MvPolynomial V F₀) :
    ∃ b : R₀, (b : F₀) ≠ 0 ∧ ∃ q : MvPolynomial V R₀,
      p * C (b : F₀) = MvPolynomial.map (R₀.val : R₀ →+* F₀) q := by
  induction p using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h x
    refine ⟨⟨b, hb⟩, hb0, C ⟨a, ha⟩, ?_⟩
    rw [MvPolynomial.map_C, ← map_mul]
    exact congrArg C e
  | add p q hp hq =>
    obtain ⟨b, hb, p', e⟩ := hp
    obtain ⟨c, hc, q', f⟩ := hq
    refine ⟨b * c, mul_ne_zero hb hc, p' * C c + q' * C b, ?_⟩
    rw [map_add, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, ← e, ← f]
    change (p + q) * C ((b : F₀) * c) = p * C (b : F₀) * C (c : F₀) + q * C (c : F₀) * C (b : F₀)
    rw [map_mul]
    ring
  | mul_X p v hp =>
    obtain ⟨b, hb, p', e⟩ := hp
    refine ⟨b, hb, p' * X v, ?_⟩
    rw [map_mul, MvPolynomial.map_X, ← e]
    ring

end PolyChart

theorem polyChart_smooth_fraction_lift : ∀ (K F₀ V : Type) [Field K] [Field F₀] [Algebra K F₀] [Finite V] (R₀ : Subalgebra K F₀) (R : Subalgebra K (FractionRing (MvPolynomial V F₀))), R = Algebra.adjoin K ((algebraMap F₀ (FractionRing (MvPolynomial V F₀))) '' (R₀ : Set F₀) ∪ Set.range fun v : V => algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (MvPolynomial.X v)) → (Algebra.Smooth K R₀ → Algebra.Smooth K R) ∧ ((∀ x : F₀, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a) → ∀ x : FractionRing (MvPolynomial V F₀), ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) ∧ ∀ (S : Type) [CommRing S] [Algebra K S] (ψ : R₀ →ₐ[K] S) (t : V → S), ∃! ψ' : R →ₐ[K] S, (∀ (a : R₀) (h : algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a ∈ R), ψ' ⟨_, h⟩ = ψ a) ∧ ∀ (v : V) (h : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (MvPolynomial.X v) ∈ R), ψ' ⟨_, h⟩ = t v := by
  intro K F₀ V _ _ _ _ R₀ R hR
  rw [← polyChartHom_range] at hR
  subst hR
  let e : MvPolynomial V R₀ ≃ₐ[K] (polyChartHom V R₀).range :=
    AlgEquiv.ofInjective _ (polyChartHom_injective V R₀)
  have he : ∀ p, ((e p : (polyChartHom V R₀).range) : FractionRing (MvPolynomial V F₀))
      = polyChartHom V R₀ p := fun p => rfl
  have heC : ∀ (a : R₀) (h : algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a ∈
      (polyChartHom V R₀).range), (⟨_, h⟩ : (polyChartHom V R₀).range) = e (C a) :=
    fun a h => Subtype.ext (polyChartHom_C V R₀ a).symm
  have heX : ∀ (v : V) (h : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
      (X v) ∈ (polyChartHom V R₀).range), (⟨_, h⟩ : (polyChartHom V R₀).range) = e (X v) :=
    fun v h => Subtype.ext (polyChartHom_X V R₀ v).symm
  refine ⟨fun hs => ?_, fun h x => ?_, fun S _ _ ψ t => ?_⟩
  · have : Algebra.Smooth R₀ (MvPolynomial V R₀) := ⟨inferInstance, inferInstance⟩
    have : Algebra.Smooth K (MvPolynomial V R₀) := Algebra.Smooth.comp K R₀ _
    exact Algebra.Smooth.of_equiv e
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial V F₀) x
    obtain ⟨b, hb, p', e1⟩ := polyChart_clear V R₀ h p
    obtain ⟨c, hc, q', e2⟩ := polyChart_clear V R₀ h q
    have hq0 : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    have hne : ∀ d : F₀, d ≠ 0 →
        algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (C d) ≠ 0 := by
      intro d hd h0
      rw [IsFractionRing.to_map_eq_zero_iff, MvPolynomial.C_eq_zero] at h0
      exact hd h0
    have h1 : polyChartHom V R₀ (p' * C c) =
        algebraMap (MvPolynomial V F₀) _ (p * C (b : F₀) * C (c : F₀)) := by
      rw [polyChartHom_apply, map_mul, MvPolynomial.map_C, e1]; rfl
    have h2 : polyChartHom V R₀ (q' * C b) =
        algebraMap (MvPolynomial V F₀) _ (q * C (c : F₀) * C (b : F₀)) := by
      rw [polyChartHom_apply, map_mul, MvPolynomial.map_C, e2]; rfl
    refine ⟨_, ⟨_, h1⟩, _, ⟨_, h2⟩, ?_, ?_⟩
    · rw [map_mul, map_mul]
      exact mul_ne_zero (mul_ne_zero hq0 (hne _ hc)) (hne _ hb)
    · simp only [map_mul]
      field_simp
  · let φ : MvPolynomial V R₀ →ₐ[K] S := MvPolynomial.aevalTower ψ t
    refine ⟨φ.comp e.symm.toAlgHom, ⟨fun a h => ?_, fun v h => ?_⟩, ?_⟩
    · rw [heC]
      simp [φ]
    · rw [heX]
      simp [φ]
    · rintro χ ⟨hC, hX⟩
      have : χ.comp e.toAlgHom = φ := by
        apply MvPolynomial.algHom_ext'
        · ext a
          have hm : algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a ∈
            (polyChartHom V R₀).range := ⟨C a, polyChartHom_C V R₀ a⟩
          have := (congrArg χ (heC a hm)).symm.trans (hC a hm)
          simpa [φ] using this
        · intro v
          have hm : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
            (X v) ∈ (polyChartHom V R₀).range := ⟨X v, polyChartHom_X V R₀ v⟩
          have := (congrArg χ (heX v hm)).symm.trans (hX v hm)
          simpa [φ] using this
      rw [← this]
      ext x
      simp

end GlobalTheory
end

