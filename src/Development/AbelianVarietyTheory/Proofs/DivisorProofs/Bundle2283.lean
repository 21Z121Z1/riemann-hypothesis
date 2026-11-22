import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0304
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialLatticeEndomorphismLift
section
open scoped TensorProduct NumberField

namespace GlobalTheory.TorusTateFree

open scoped nonZeroDivisors in

private theorem finrank_int_tower (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (𝓞 E) M] : Module.finrank ℤ M = Module.finrank ℚ E * Module.finrank (𝓞 E) M := by
  let f : M →ₗ[𝓞 E] E ⊗[𝓞 E] M := TensorProduct.mk (𝓞 E) E M 1
  have hb : IsBaseChange E f := TensorProduct.isBaseChange _ _ _
  haveI h1 : IsLocalizedModule (𝓞 E)⁰ f := (isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E f).2 hb
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  haveI h2 : IsLocalizedModule (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) f :=
    (isLocalizedModule_iff_isBaseChange _ E f).2 hb
  haveI h3 : IsLocalizedModule ℤ⁰ (f.restrictScalars ℤ) := IsLocalizedModule.restrictScalars _ f
  rw [← IsLocalizedModule.finrank_eq ℤ⁰ (f.restrictScalars ℤ) le_rfl,
    ← IsLocalizedModule.finrank_eq (𝓞 E)⁰ f le_rfl,
    ← IsLocalization.finrank_eq ℚ ℤ⁰ le_rfl, ← IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl,
    Module.finrank_mul_finrank]

private theorem exists_span_mod {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (m : R) [Finite (R ⧸ Ideal.span {m})] :
    ∃ v : Fin (Module.finrank R N) → N, ∀ x : N, ∃ (c : Fin (Module.finrank R N) → R) (z : N),
      x = ∑ k, c k • v k + m • z := by
  set I : Ideal R := Ideal.span {m} with hI
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  have h1 : Submodule.span R (Set.range b) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq,
      Submodule.restrictScalars_top]
  let q := TensorProduct.quotTensorEquivQuotSMul N I
  choose v hv using fun k => Submodule.Quotient.mk_surjective _ (q (b k))
  refine ⟨v, fun x => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
    (h1 ▸ Submodule.mem_top : q.symm (Submodule.Quotient.mk x) ∈ Submodule.span R (Set.range b))
  have h2 : x - ∑ k, c k • v k ∈ (I • ⊤ : Submodule R N) := by
    rw [← Submodule.Quotient.eq, ← q.apply_symm_apply (Submodule.Quotient.mk x), ← hc, map_sum,
      ← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, Submodule.mkQ_apply, hv]
  rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨z, -, hz⟩ := h2
  exact ⟨c, z, by rw [hz]; abel⟩

theorem exists_gens_mod : ∀ (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (L : Submodule ℤ W), (∀ a z, z ∈ L → ρ a z ∈ L) → Module.Finite ℤ L →
    ∀ (κ : Type) [Fintype κ], Module.finrank ℤ L = Fintype.card κ * Module.finrank ℚ E →
    ∃ y : κ → W, (∀ k, y k ∈ L) ∧ ∀ x ∈ L, ∃ (c : κ → 𝓞 E) (z : W), z ∈ L ∧ x = ∑ k, ρ (c k) (y k) + (ℓ : ℂ) • z := by
  intro E _ _ ℓ hℓ W _ _ ρ L hstab hfin κ _ hrk
  letI : Module (𝓞 E) W := Module.compHom W ρ
  have hs : ∀ (a : 𝓞 E) (z : W), a • z = ρ a z := fun _ _ => rfl
  let N : Submodule (𝓞 E) W :=
    { carrier := L
      add_mem' := fun ha hb => L.add_mem ha hb
      zero_mem' := L.zero_mem
      smul_mem' := fun a z hz => hstab a z hz }
  let e : L ≃ₗ[ℤ] N := AddEquiv.toIntLinearEquiv
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have : Module.Finite ℤ N := Module.Finite.equiv e
  have : Module.Finite (𝓞 E) N := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.IsTorsionFree (𝓞 E) W := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a z h => or_iff_not_imp_left.2 fun ha => ?_
    obtain ⟨b, n, hn, h1⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul ℤ (1 : 𝓞 E) ha
    have h2 : (n : 𝓞 E) = b * a := by rw [mul_comm, ← h1]; simp
    have h3 : (n : ℂ) • z = 0 := by
      rw [Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul (𝓞 E), h2, mul_smul, h, smul_zero]
    exact (smul_eq_zero.1 h3).resolve_left (Int.cast_ne_zero.2 hn)
  have : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 E) N := inferInstance
  have : Module.Projective (𝓞 E) N := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ Ideal.span {(ℓ : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hℓ.out.ne_zero)
  have hr : Fintype.card κ = Module.finrank (𝓞 E) N := by
    rw [e.finrank_eq, finrank_int_tower E N, mul_comm] at hrk
    exact (Nat.eq_of_mul_eq_mul_right Module.finrank_pos hrk).symm
  let σ : κ ≃ Fin (Module.finrank (𝓞 E) N) := Fintype.equivFinOfCardEq hr
  obtain ⟨v, hv⟩ := exists_span_mod (N := N) (ℓ : 𝓞 E)
  refine ⟨fun k => v (σ k), fun k => (v (σ k)).2, fun x hx => ?_⟩
  obtain ⟨c, z, h⟩ := hv ⟨x, hx⟩
  refine ⟨fun k => c (σ k), z, z.2, ?_⟩
  have h1 := congrArg N.subtype h
  rw [map_add, map_sum, map_smul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul ℂ,
    ← σ.sum_comp] at h1
  exact h1

theorem exists_tate_gens : ∀ (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (M : Type) [CommGroup M] (ex : W → M), (∀ z w, ex (z + w) = ex z * ex w) →
    Function.Surjective ex → ∀ (L : Submodule ℤ W), (∀ z, ex z = 1 ↔ z ∈ L) →
    ∀ (β : 𝓞 E → (M →* M)), (∀ a z, ex (ρ a z) = β a (ex z)) →
    ∀ (α : 𝓞 E →+* Module.End ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M)), (∀ a t n, (α a t).lev n = β a (t.lev n)) →
    ∀ (κ : Type) [Fintype κ] (y : κ → W), (∀ k, y k ∈ L) →
    (∀ x ∈ L, ∃ (c : κ → 𝓞 E) (z : W), z ∈ L ∧ x = ∑ k, ρ (c k) (y k) + (ℓ : ℂ) • z) →
    ∃ T : κ → GlobalTheory.HTLat.Tate ℓ M, ∀ t : GlobalTheory.HTLat.Tate ℓ M, ∃ (c : κ → 𝓞 E) (s : GlobalTheory.HTLat.Tate ℓ M),
      t = ∑ k, α (c k) (T k) + (ℓ : ℤ_[ℓ]) • s := by
  intro E _ _ ℓ hℓ W _ _ ρ M _ ex hadd hsurj L hL β hβ α hα κ _ y hyL hy
  have h0 : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hℓ.out.ne_zero
  let φ : W →+ Additive M := AddMonoidHom.mk' (fun z => Additive.ofMul (ex z)) hadd
  have hpow : ∀ (z : W) (n : ℕ), ex z ^ n = ex ((n : ℂ) • z) := fun z n => by
    rw [Nat.cast_smul_eq_nsmul]
    exact (map_nsmul φ n z).symm
  let lv : GlobalTheory.HTLat.Tate ℓ M →+ Additive M := AddMonoidHom.mk' (fun t => Additive.ofMul (t.lev 1))
    fun _ _ => rfl
  let T : κ → GlobalTheory.HTLat.Tate ℓ M := fun k =>
    GlobalTheory.HTLat.Tate.mk (fun n => ex (((ℓ : ℂ) ^ n)⁻¹ • y k)) fun n =>
      ⟨by rw [hpow, smul_smul, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero _ h0), one_smul, hL]; exact hyL k,
        by rw [hpow, smul_smul, pow_succ', mul_inv, mul_inv_cancel_left₀ h0]⟩
  refine ⟨T, fun t => ?_⟩
  obtain ⟨w, hw⟩ := hsurj (t.lev 1)
  have hwL : (ℓ : ℂ) • w ∈ L := by
    rw [← hL, ← hpow, hw]
    simpa using t.lev_pow 1
  obtain ⟨c, z, hz, h⟩ := hy _ hwL
  have h1 : w = ∑ k, ρ (c k) (((ℓ : ℂ) ^ 1)⁻¹ • y k) + z := by
    rw [← inv_smul_smul₀ h0 w, h, smul_add, inv_smul_smul₀ h0, Finset.smul_sum, pow_one]
    simp only [map_smul]
  have h2 : lv (t - ∑ k, α (c k) (T k)) = 0 := by
    have h3 : lv t = φ w := congrArg Additive.ofMul hw.symm
    have h4 : φ z = 0 := congrArg Additive.ofMul ((hL z).2 hz)
    rw [map_sub, sub_eq_zero, h3, h1, map_add, h4, add_zero, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => congrArg Additive.ofMul ?_
    exact (hβ _ _).trans (hα _ (T k) 1).symm
  obtain ⟨s, hs⟩ := GlobalTheory.TateSpan.exists_eq_p_smul_of_lev_one (t - ∑ k, α (c k) (T k)) h2
  exact ⟨c, s, by rw [← hs]; abel⟩

theorem tate_free_of_lattice : ∀ (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (M : Type) [CommGroup M] (ex : W → M), (∀ z w, ex (z + w) = ex z * ex w) →
    Function.Surjective ex → ∀ (L : Submodule ℤ W), (∀ z, ex z = 1 ↔ z ∈ L) → Module.Finite ℤ L →
    ∀ (β : 𝓞 E → (M →* M)), (∀ a z, ex (ρ a z) = β a (ex z)) →
    ∀ (α : 𝓞 E →+* Module.End ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M)), (∀ a t n, (α a t).lev n = β a (t.lev n)) →
    Module.Free ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) → Module.Finite ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) →
    ∀ (κ : Type) [Fintype κ], Module.finrank ℤ L = Fintype.card κ * Module.finrank ℚ E →
    Module.finrank ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) = Fintype.card κ * Module.finrank ℚ E →
    ∃ f : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] GlobalTheory.HTLat.Tate ℓ M,
      ∀ (a : 𝓞 E) (r : κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E), f (((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a) • r) = α a (f r) := by
  intro E _ _ ℓ _ W _ _ ρ M _ ex hadd hsurj L hL hfin β hβ α hα hfree hfinT κ _ hrkL hrkT
  have hstab : ∀ a z, z ∈ L → ρ a z ∈ L := fun a z hz => by
    rw [← hL] at hz ⊢
    rw [hβ, hz, map_one]
  obtain ⟨y, hyL, hy⟩ := exists_gens_mod E ℓ W ρ L hstab hfin κ hrkL
  obtain ⟨T, hT⟩ := exists_tate_gens E ℓ W ρ M ex hadd hsurj L hL β hβ α hα κ y hyL hy
  let act : ℤ_[ℓ] ⊗[ℤ] 𝓞 E →ₐ[ℤ_[ℓ]] Module.End ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) α.toIntAlgHom
      (fun x a => Algebra.commute_algebraMap_left x _)
  have hact : ∀ a, act ((1 : ℤ_[ℓ]) ⊗ₜ a) = α a := fun a => by
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    rw [map_one, one_mul]
    rfl
  let F : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) →ₗ[ℤ_[ℓ]] GlobalTheory.HTLat.Tate ℓ M :=
    { toFun := fun r => ∑ k, act (r k) (T k)
      map_add' := fun r s => by
        simp only [Pi.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
      map_smul' := fun c r => by
        simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum, RingHom.id_apply] }
  have hF : ∀ r, F r = ∑ k, act (r k) (T k) := fun r => rfl
  have hmem : ∀ c : κ → 𝓞 E, ∑ k, α (c k) (T k) ∈ LinearMap.range F := fun c =>
    ⟨fun k => (1 : ℤ_[ℓ]) ⊗ₜ c k, by simp only [hF, hact]⟩
  have hI : IsLocalRing.maximalIdeal ℤ_[ℓ] ≤ (⊥ : Ideal ℤ_[ℓ]).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hle : (⊤ : Submodule ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M)) ≤
      LinearMap.range F ⊔ IsLocalRing.maximalIdeal ℤ_[ℓ] • ⊤ := by
    intro t _
    obtain ⟨c, s, rfl⟩ := hT t
    refine Submodule.add_mem_sup (hmem c) (Submodule.smul_mem_smul ?_ trivial)
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  have hsurjF : Function.Surjective F := LinearMap.range_eq_top.1
    (top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI hle))
  have hrkR : Module.finrank ℤ_[ℓ] (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) = Fintype.card κ * Module.finrank ℚ E := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Module.finrank_baseChange, NumberField.RingOfIntegers.rank]
  let e := LinearEquiv.ofFinrankEq (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) (GlobalTheory.HTLat.Tate ℓ M) (hrkR.trans hrkT.symm)
  have hinj : Function.Injective F := by
    have h := OrzechProperty.injective_of_surjective_endomorphism (e.symm.toLinearMap ∘ₗ F)
      (e.symm.surjective.comp hsurjF)
    rw [LinearMap.coe_comp] at h
    exact h.of_comp
  refine ⟨LinearEquiv.ofBijective F ⟨hinj, hsurjF⟩, fun a r => ?_⟩
  change F _ = α a (F r)
  rw [hF, hF, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, hact]
  rfl

end GlobalTheory.TorusTateFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductSpecFieldPointFactors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SpecFibreProduct

theorem point_factors (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀)
    (g₂ : R₂ ⟶ R₀) (hP : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁)
    (hg₂ : Function.Surjective g₂) (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec P) :
    (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₁, y ≫ Spec.map f₁ = x) ∨
      (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₂, y ≫ Spec.map f₂ = x) := by
  have H := (Types.isPullback_iff _ _ _ _).1 (hP.map (forget CommRingCat))
  have hinj : ∀ a b : P, f₁.hom a = f₁.hom b → f₂.hom a = f₂.hom b → a = b :=
    fun a b h₁ h₂ ↦ H.2.1 a b ⟨h₁, h₂⟩
  have hex : ∀ (b : R₁) (c : R₂), g₁.hom b = g₂.hom c → ∃ a : P, f₁.hom a = b ∧ f₂.hom a = c :=
    fun b c h ↦ H.2.2 b c h
  have hs₁ : Function.Surjective f₁.hom := by
    intro b
    obtain ⟨c, hc⟩ := hg₂ (g₁.hom b)
    obtain ⟨a, ha, -⟩ := hex b c hc.symm
    exact ⟨a, ha⟩
  have hs₂ : Function.Surjective f₂.hom := by
    intro c
    obtain ⟨b, hb⟩ := hg₁ (g₂.hom c)
    obtain ⟨a, -, ha⟩ := hex b c hb
    exact ⟨a, ha⟩
  set χ : P ⟶ CommRingCat.of k := Spec.preimage x with hχ
  have hx : Spec.map χ = x := Spec.map_preimage x
  by_cases h : RingHom.ker f₁.hom ≤ RingHom.ker χ.hom
  · left
    let ψ : R₁ →+* k := f₁.hom.liftOfRightInverse (Function.surjInv hs₁)
      (Function.rightInverse_surjInv hs₁) ⟨χ.hom, h⟩
    have hψ : ∀ a, ψ (f₁.hom a) = χ.hom a := fun a ↦
      f₁.hom.liftOfRightInverse_comp_apply _ _ ⟨χ.hom, h⟩ a
    have he : f₁ ≫ CommRingCat.ofHom ψ = χ := CommRingCat.hom_ext (RingHom.ext hψ)
    exact ⟨Spec.map (CommRingCat.ofHom ψ), by rw [← Spec.map_comp, he, hx]⟩
  · right
    have h₂ : RingHom.ker f₂.hom ≤ RingHom.ker χ.hom := by
      intro b hb
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 h
      rw [RingHom.mem_ker] at ha hb ⊢
      rw [RingHom.mem_ker] at ha'
      have hab : a * b = 0 := hinj _ _ (by rw [map_mul, ha, zero_mul, map_zero])
        (by rw [map_mul, hb, mul_zero, map_zero])
      have : χ.hom a * χ.hom b = 0 := by rw [← map_mul, hab, map_zero]
      exact (mul_eq_zero.1 this).resolve_left ha'
    let ψ : R₂ →+* k := f₂.hom.liftOfRightInverse (Function.surjInv hs₂)
      (Function.rightInverse_surjInv hs₂) ⟨χ.hom, h₂⟩
    have hψ : ∀ a, ψ (f₂.hom a) = χ.hom a := fun a ↦
      f₂.hom.liftOfRightInverse_comp_apply _ _ ⟨χ.hom, h₂⟩ a
    have he : f₂ ≫ CommRingCat.ofHom ψ = χ := CommRingCat.hom_ext (RingHom.ext hψ)
    exact ⟨Spec.map (CommRingCat.ofHom ψ), by rw [← Spec.map_comp, he, hx]⟩

end GlobalTheory.SpecFibreProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFunctionFieldOfEtaleOnOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FunctionFieldEtale

theorem finiteDimensional_fractionRing_of_etale {R S K L : Type} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] (φ : R →+* S) (hφ : φ.Etale) (ψ : K →+* L)
    (h : ∀ r, ψ (algebraMap R K r) = algebraMap S L (φ r)) :
    letI := ψ.toAlgebra; FiniteDimensional K L := by
  letI : Algebra K L := ψ.toAlgebra
  letI : Algebra R S := φ.toAlgebra
  haveI : Algebra.Etale R S := hφ
  letI : Algebra R L := (ψ.comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq (fun r => h r)
  haveI : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  let g : K ⊗[R] S →ₐ[K] L := Algebra.TensorProduct.lift (Algebra.ofId K L)
    (IsScalarTower.toAlgHom R S L) (fun _ _ => Commute.all _ _)
  haveI : Module.Finite K g.range :=
    Module.Finite.of_surjective g.rangeRestrict.toLinearMap g.rangeRestrict_surjective
  have hS : ∀ s : S, algebraMap S L s ∈ g.range := fun s => ⟨1 ⊗ₜ s, by simp [g]⟩
  have hinv : ∀ x ∈ g.range, x⁻¹ ∈ g.range := fun x hx =>
    Subalgebra.inv_mem_of_algebraic (A := g.range) (x := ⟨x, hx⟩)
      ((Algebra.IsAlgebraic.isAlgebraic (R := K) (⟨x, hx⟩ : g.range)).algHom g.range.val)
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) y
    rw [div_eq_mul_inv]
    exact Subalgebra.mul_mem _ (hS a) (hinv _ (hS b))
  exact Module.Finite.of_surjective g.toLinearMap hsurj

theorem finiteDimensional_functionField_of_etale_on_open : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty →
    letI := (functionFieldMap f).toAlgebra; FiniteDimensional W.functionField M.functionField := by
  intro M W _ _ f _ U hf hU
  have hξU : genericPoint M ∈ U :=
    ((genericPoint_spec M).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  obtain ⟨V, hV, hfξV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f (genericPoint M))
    (U := ⊤) trivial
  let x : U := ⟨genericPoint M, hξU⟩
  have hx : x ∈ (U.ι ≫ f) ⁻¹ᵁ V := hfξV
  obtain ⟨V', hV', hxV', hV'sub⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : V' ≤ (U.ι ≫ f) ⁻¹ᵁ V := fun _ h => hV'sub h
  let U' : M.Opens := U.ι ''ᵁ V'
  have hU' : IsAffineOpen U' := hV'.image_of_isOpenImmersion U.ι
  have hξU' : genericPoint M ∈ U' := ⟨x, hxV', rfl⟩
  have e' : U' ≤ f ⁻¹ᵁ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact hV'sub hy
  haveI : Nonempty V := ⟨⟨_, hfξV⟩⟩
  haveI : Nonempty U' := ⟨⟨_, hξU'⟩⟩
  have het0 := HasRingHomProperty.appLE (P := @Etale) (f := U.ι ≫ f) hf ⟨V, hV⟩ ⟨V', hV'⟩ hle
  have key : (U.ι ≫ f).appLE V V' hle = f.appLE V U' e' := by
    rw [Scheme.Hom.comp_appLE]
    erw [Scheme.Opens.ι_appLE]
    rfl
  have het : (f.appLE V U' e').hom.Etale := by
    rw [← key]; exact het0
  haveI := functionField_isFractionRing_of_isAffineOpen W V hV
  haveI := functionField_isFractionRing_of_isAffineOpen M U' hU'
  refine finiteDimensional_fractionRing_of_etale (f.appLE V U' e').hom het (functionFieldMap f) ?_
  intro r
  have := functionFieldMap_algebraMap f (genericPoint M) (W.presheaf.germ V _ hfξV r)
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at this
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
  refine this.trans ?_
  rw [Scheme.Hom.germ_stalkMap_apply]
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨_, hfξV⟩⟩
  erw [Scheme.algebraMap_germ_eq_germToFunctionField]
  show M.presheaf.germ _ _ _ (f.app V r) =
    M.presheaf.germ U' _ hξU' (M.presheaf.map (homOfLE e').op (f.app V r))
  rw [TopCat.Presheaf.germ_res_apply]

end GlobalTheory.FunctionFieldEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLattice
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.FullLevel

theorem finE_mem_lev_of_isKM : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Links.IsSDFrame V β Λ 1 → V.rank ≤ L.r → L.P.H = ⊤ → ∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L := by
  intro D V β Λ L hΛ hr hP h hK
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hΛ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hk : GlobalTheory.Member.FinCong V 1 h := by
    intro z hz
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1] at hz ⊢
    exact hK.2.1 z hz
  have hc : ∀ a : GA D V, GlobalTheory.Member.FinCong V 1 a → ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (1 : ℕ) • y := by
    intro a ha
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap Λ 1 _ ha
  have hc' := hc _ (GlobalTheory.Member.PrincLevel.finCong_inv hk)
  rw [map_inv] at hc'
  obtain ⟨y, hy, -⟩ := GlobalTheory.PrincInLevel.exists_int (Formalism.L2.Herm.intAf D.host.F D.host.E) β (Formalism.IndefR.Lev.finE V h)
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ) 1 hfr (hc h hk) hc'
  have hS : Formalism.IndefR.Lev.finE V h ∈ Formalism.L2.DIV.St β := ⟨y, hy⟩
  have hU : Formalism.IndefR.Lev.finE V h ∈ Formalism.L2.DIV.UA D.sp.cm V.gram := GlobalTheory.LevSplit.finE_mem_UA V h
  have hb : ∀ a : Fin V.rank, a.val < L.r := fun a => lt_of_lt_of_le a.2 hr
  refine Formalism.L2.DIV.mem_lev.2 ⟨Formalism.L2.DIV.mem_parLev.2 ⟨hU, hS, fun PP _ => ?_, fun PP _ => ?_⟩, ?_⟩
  · intro i j hij
    exfalso
    simp only [Formalism.L2.DIV.blkOf, if_pos (hb i), if_pos (hb j)] at hij
    exact lt_irrefl _ hij
  · intro i j hij
    exfalso
    simp only [Formalism.L2.DIV.blk2, if_pos (hb i), if_pos (hb j)] at hij
    exact lt_irrefl _ hij
  · rw [hP]; exact Subgroup.mem_top _

end GlobalTheory.CovTop.VolUp.FullLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodules
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

theorem exists_mulVec_submatrix_mul_iff {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (U : Matrix m n R) (e : Equiv.Perm n) (C : Matrix n n R) (hC : IsUnit C.det) (cv : m → R) :
    (∃ a, (U.submatrix id e * C).mulVec a = cv) ↔ ∃ a, U.mulVec a = cv := by
  have hs : ∀ b, (U.submatrix id e).mulVec b = U.mulVec (b ∘ e.symm) := fun b => by
    have := Matrix.submatrix_mulVec_equiv U b (Equiv.refl m) e
    simpa using this
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(C.mulVec a) ∘ e.symm, by rw [← Matrix.mulVec_mulVec, hs]⟩
  · rintro ⟨a, rfl⟩
    have hC' : ∀ x, C.mulVec (C⁻¹.mulVec x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hC, Matrix.one_mulVec]
    refine ⟨C⁻¹.mulVec (a ∘ e), ?_⟩
    rw [← Matrix.mulVec_mulVec, hC', hs]
    congr 1
    funext i
    simp

end GlobalTheory.FlagMod.FieldFlag

namespace GlobalTheory.FlagMod.FieldFlag

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem cellFrames_topEigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ), (cellFrames hZ ht).TopEigen := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht
  intro S _ _ y hy z hx k hz σ
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (ev z _ hz).comp (cellθ κ k).toRingHom := ⟨_, rfl⟩
  have hzφ : spMap φ ≫ κ k.1 k.2 = z := hφ ▸ eq_spMap_ev k z hz
  have hxφ : y ≫ Y.j = spMap (φ.comp (cC A k.1)) ≫ tau (A.V k.1).2 := by
    rw [← hx, ← hzφ, Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp']
    rfl
  have hV : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ (A.k k.1).V := hxφ ▸ le_preimage_comp _ (tau_le (A.V k.1).2 le_rfl)
  have hev : ev (y ≫ Y.j) (A.k k.1).V hV = φ.comp (cC A k.1) := by
    rw [ev_congr hxφ _ hV (hxφ ▸ hV)]
    exact ev_spMap_tau (A.V k.1).2 _ _
  have hM : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ (A.k k.1).M.U := (cellFrames hZ ht).inM hz hx
  have huAt : (cellFrames hZ ht).uAt k z hz σ = ((((A.k k.1).u σ).map (ev (y ≫ Y.j) _ hV)).submatrix id (k.2 σ)) *
      (cellMat (A.V k.1) σ).map φ := by
    refine Matrix.ext fun i j => ?_
    show (ev z _ hz) ((cellθ κ k) (uC A k.1 k.2 σ i j)) = _
    have e2 : ∀ x, (ev z _ hz) ((cellθ κ k) x) = φ x := fun x => by rw [hφ]; rfl
    rw [hev, e2, uC]
    exact RingHom.map_matrix_mul _ _ i j φ
  have hdet : IsUnit ((cellMat (A.V k.1) σ).map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_cellMat, map_one]
    exact isUnit_one
  refine SetLike.ext fun v => ?_
  obtain ⟨cv, rfl⟩ := (vec (A.k k.1).M.toMChart _ hM).surjective v
  refine Iff.trans ?_ ((vec_mem_eigLie _ _ hM σ cv).trans (((LowRank.pm_gen p (A.k k.1).M.toMChart σ hy hM).1 cv).trans
    ((A.k k.1).fix_iff σ _ hV hM cv))).symm
  rw [mem_initSpan, ← exists_mulVec_submatrix_mul_iff _ (k.2 σ) _ hdet, ← huAt]
  exact ⟨fun ⟨a, _, e⟩ => ⟨a, (vec (A.k k.1).M.toMChart _ hM).injective
      (((cellFrames hZ ht).sum_vecAt k _ hz hx σ a).symm.trans e)⟩,
    fun ⟨a, e⟩ => ⟨a, fun j hj => absurd j.2 (not_lt.2 hj),
      ((cellFrames hZ ht).sum_vecAt k _ hz hx σ a).trans (congrArg (vec (A.k k.1).M.toMChart _ hM) e)⟩⟩

end GlobalTheory.FlagMod.FieldFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFibrePowerAndExternalTensorSectionNonzeroCloStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_fibrePower_and_externalTensorSection_nonzero_closedFibre : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) [Flat G.hom] (L : LB G.left) (θ : L.Sec), NonzeroClosed (X := G) θ → ∀ N : ℕ, Flat (pow G N).hom ∧ NonzeroClosed (X := pow G N) (boxSec G θ N) := by
  first | exact @GlobalTheory.BoxNonzeroClosed.main | exact GlobalTheory.BoxNonzeroClosed.main | (intros; apply GlobalTheory.BoxNonzeroClosed.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBoundStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_line_c1_log_bound : FlatDeg → Covers fun Fm x _ ι p i Y _ _ => GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict ∧ (∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q) ∧ GlobalTheory.FlatLine.FlatExists Y.U (xiR (Fm.D x ι)) ∧ (∀ τ, |GlobalTheory.FlatLine.c1 Y.U (xiR (Fm.D x ι)) τ + (((dat p i).p : ℝ) - (dat p i).q) / 2 * (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 3 * (dat p i).q * (Fm.L x ι).sc.L) ∧ GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes p.T.Q.H Y.d.l₂) ≤ 40 * (Fm.L x ι).sc.L := by
  first | exact @GlobalTheory.CovTop.FlatVal.flat_val | exact GlobalTheory.CovTop.FlatVal.flat_val | (intros; apply GlobalTheory.CovTop.FlatVal.flat_val <;> assumption)
end

