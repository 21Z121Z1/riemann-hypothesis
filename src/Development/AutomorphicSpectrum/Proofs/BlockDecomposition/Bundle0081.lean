import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0068
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0066
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0061
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0035
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0050

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicAlgebraHilbertNinety
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FirstApprox

private theorem tensorProduct_congr_refl_pow_tmul_lemma {O O' κ : Type} [CommRing O] [CommRing O']
    [Algebra O O'] [CommRing κ] [Algebra O κ] (τ : O' ≃ₐ[O] O') (j : ℕ) (k : κ) (x : O') :
    (Algebra.TensorProduct.congr (AlgEquiv.refl : κ ≃ₐ[κ] κ) τ ^ j) (k ⊗ₜ[O] x) =
      k ⊗ₜ[O] (τ ^ j) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, pow_succ', AlgEquiv.mul_apply,
      Algebra.TensorProduct.congr_apply]
    exact Algebra.TensorProduct.map_tmul ..

theorem res_fixed (O O' κ : Type) [CommRing O] [CommRing O'] [Algebra O O'] [CommRing κ] [Algebra O κ] (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hs : Function.Surjective (algebraMap O κ)) (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1) (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) (htr : ∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1) (z : κ ⊗[O] O') (hz : Algebra.TensorProduct.congr (AlgEquiv.refl : κ ≃ₐ[κ] κ) τ z = z) : z ∈ Set.range (algebraMap κ (κ ⊗[O] O')) := by
  obtain ⟨a, ha⟩ := htr
  obtain ⟨σ, hσ⟩ : ∃ σ : κ ⊗[O] O' ≃ₐ[κ] κ ⊗[O] O',
      σ = Algebra.TensorProduct.congr (AlgEquiv.refl : κ ≃ₐ[κ] κ) τ := ⟨_, rfl⟩
  rw [← hσ] at hz
  have hpow : ∀ (j : ℕ) (k : κ) (x : O'), (σ ^ j) (k ⊗ₜ[O] x) = k ⊗ₜ[O] (τ ^ j) x := by
    intro j k x
    rw [hσ]
    exact tensorProduct_congr_refl_pow_tmul_lemma τ j k x
  have hzfix : ∀ j : ℕ, (σ ^ j) z = z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hz]
  have htrace : ∀ t : κ ⊗[O] O',
      ∑ j ∈ Finset.range ℓ, (σ ^ j) t ∈ Set.range (algebraMap κ (κ ⊗[O] O')) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul k x =>
      have hfx : τ (∑ j ∈ Finset.range ℓ, (τ ^ j) x) = ∑ j ∈ Finset.range ℓ, (τ ^ j) x := by
        rw [map_sum]
        have e := (Finset.sum_range_succ' (fun j => (τ ^ j) x) ℓ).symm.trans
          (Finset.sum_range_succ (fun j => (τ ^ j) x) ℓ)
        rw [hτ, pow_zero] at e
        rw [← add_right_cancel e]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ', AlgEquiv.mul_apply]
      obtain ⟨c, hc⟩ := hfix _ hfx
      refine ⟨c • k, ?_⟩
      simp only [hpow]
      rw [← TensorProduct.tmul_sum, ← hc, Algebra.algebraMap_eq_smul_one (A := O') c,
        ← TensorProduct.smul_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨u₁, hu₁⟩ := h₁
      obtain ⟨u₂, hu₂⟩ := h₂
      exact ⟨u₁ + u₂, by simp only [map_add, Finset.sum_add_distrib, hu₁, hu₂]⟩
  have key : ∑ j ∈ Finset.range ℓ, (σ ^ j) ((1 ⊗ₜ[O] a) * z) = z := by
    simp only [map_mul, hpow, hzfix]
    rw [← Finset.sum_mul, ← TensorProduct.tmul_sum, ha, ← Algebra.TensorProduct.one_def, one_mul]
  rw [← key]
  exact htrace _

theorem res_compare (O O' R κ A : Type) [CommRing O] [CommRing O'] [Algebra O O'] [CommRing R] [Algebra O R] [CommRing κ] [Algebra O κ] [CommRing A] [Algebra O A] [Algebra κ A] [IsScalarTower O κ A] (π : R →ₐ[O] A) (hπ : Function.Surjective π) : ∃ ψ : O' ⊗[O] R →+* (κ ⊗[O] O') ⊗[κ] A, Function.Surjective ψ ∧ RingHom.ker ψ ≤ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (RingHom.ker π) ∧ (∀ x : R, ψ ((Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) x) = Algebra.TensorProduct.includeRight (π x)) ∧ ∀ (f : O' →ₐ[O] O') (s : O' ⊗[O] R), ψ (Algebra.TensorProduct.map f (AlgHom.id O R) s) = Algebra.TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id κ κ) f) (AlgHom.id κ A) (ψ s) := by
  let ψ : O' ⊗[O] R →+* (κ ⊗[O] O') ⊗[κ] A :=
    (((Algebra.TensorProduct.comm κ A (κ ⊗[O] O') :
        A ⊗[κ] (κ ⊗[O] O') →+* (κ ⊗[O] O') ⊗[κ] A).comp
      ((Algebra.TensorProduct.cancelBaseChange O κ κ A O').symm :
        A ⊗[O] O' →+* A ⊗[κ] (κ ⊗[O] O'))).comp
      (Algebra.TensorProduct.comm O O' A : O' ⊗[O] A →+* A ⊗[O] O')).comp
      (Algebra.TensorProduct.map (AlgHom.id O O') π : O' ⊗[O] R →+* O' ⊗[O] A)
  have hψ : ∀ t, ψ t = Algebra.TensorProduct.comm κ A (κ ⊗[O] O')
      ((Algebra.TensorProduct.cancelBaseChange O κ κ A O').symm
        (Algebra.TensorProduct.comm O O' A (Algebra.TensorProduct.map (AlgHom.id O O') π t))) :=
    fun t => rfl
  have hψt : ∀ (x : O') (r : R), ψ (x ⊗ₜ[O] r) = (1 ⊗ₜ[O] x) ⊗ₜ[κ] π r := by
    intro x r
    rw [hψ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.comm_tmul]
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨t, ht⟩ := Algebra.TensorProduct.map_surjective (AlgHom.id O O') π Function.surjective_id hπ
      ((Algebra.TensorProduct.comm O O' A).symm ((Algebra.TensorProduct.cancelBaseChange O κ κ A O')
        ((Algebra.TensorProduct.comm κ A (κ ⊗[O] O')).symm w)))
    refine ⟨t, ?_⟩
    rw [hψ, ht]
    simp only [AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply]
  · intro t ht
    have hm : Algebra.TensorProduct.map (AlgHom.id O O') π t = 0 := by
      rw [RingHom.mem_ker, hψ] at ht
      simpa using ht
    have hker : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id O O') π) =
        Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (RingHom.ker π) := by
      rw [Algebra.TensorProduct.map_ker _ _ Function.surjective_id hπ,
        (RingHom.injective_iff_ker_eq_bot (AlgHom.id O O')).mp Function.injective_id, Ideal.map_bot,
        bot_sup_eq]
    rw [← hker]
    exact hm
  · intro x
    simp only [Algebra.TensorProduct.includeRight_apply, hψt, ← Algebra.TensorProduct.one_def]
  · intro f s
    induction s using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hψt]
    | add x y hx hy => simp only [map_add, hx, hy]

theorem main : PositivityTheory.Rg.Tf.Loc.N1 → ∀ (O O' R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] [CommRing R] [Algebra O R] [Module.Finite O R] (ℓ : ℕ) (τ : O' ≃ₐ[O] O'), 0 < ℓ → τ ^ ℓ = 1 → (∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) → (∃ x y : Fin ℓ → O', ∀ j < ℓ, ∑ i, x i * (τ ^ j) (y i) = if j = 0 then 1 else 0) → (∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1) → ∀ r : Rˣ, ∃ s : (O' ⊗[O] R)ˣ, (∏ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) (s : O' ⊗[O] R)) - (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (r : R) ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson := by
  intro hNI O O' R _ _ _ _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hdual htr r
  obtain ⟨J, hJ⟩ : ∃ J : Ideal R, J = (⊥ : Ideal R).jacobson := ⟨_, rfl⟩
  have hmJ : Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) ≤ J :=
    hJ ▸ (GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le O R).1
  letI : Algebra (IsLocalRing.ResidueField O) (R ⧸ J) :=
    (Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) (algebraMap O (R ⧸ J)) fun c hc => by
      first
        | exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmJ (Ideal.mem_map_of_mem _ hc))
        | (rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
           exact hmJ (Ideal.mem_map_of_mem _ hc))).toAlgebra
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) (R ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun c => rfl
  haveI : Module.Finite O (R ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O J).toLinearMap (Ideal.Quotient.mkₐ_surjective O J)
  haveI : Module.Finite (IsLocalRing.ResidueField O) (R ⧸ J) :=
    Module.Finite.of_restrictScalars_finite O _ _
  have hrad : J.IsRadical := by
    rw [hJ]
    exact Ideal.radical_le_jacobson.trans Ideal.jacobson_idem.le
  haveI : IsReduced (R ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).mp hrad
  haveI : Module.Finite (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] O') :=
    Module.Finite.base_change O _ O'
  have hres : Function.Surjective (algebraMap O (IsLocalRing.ResidueField O)) :=
    IsLocalRing.residue_surjective
  obtain ⟨x, y, hxy⟩ := hdual
  have hτ' : Algebra.TensorProduct.congr
      (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O)
      τ ^ ℓ = 1 := by
    refine AlgEquiv.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul k w => rw [tensorProduct_congr_refl_pow_tmul_lemma, hτ]; rfl
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  have hfix' : ∀ z : IsLocalRing.ResidueField O ⊗[O] O',
      Algebra.TensorProduct.congr
        (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O)
        τ z = z →
      z ∈ Set.range (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] O')) :=
    fun z hz => GlobalTheory.CompanionTheory.FirstApprox.res_fixed O O'
      (IsLocalRing.ResidueField O) ℓ τ hres hℓ hτ hfix htr z hz
  have hdual' : ∃ x' y' : Fin ℓ → IsLocalRing.ResidueField O ⊗[O] O', ∀ j < ℓ,
      ∑ i, x' i * (Algebra.TensorProduct.congr
        (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O)
        τ ^ j) (y' i) = if j = 0 then 1 else 0 := by
    refine ⟨fun i => 1 ⊗ₜ[O] x i, fun i => 1 ⊗ₜ[O] y i, fun j hj => ?_⟩
    simp only [tensorProduct_congr_refl_pow_tmul_lemma, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [← TensorProduct.tmul_sum, hxy j hj]
    split_ifs
    · exact (Algebra.TensorProduct.one_def).symm
    · exact TensorProduct.tmul_zero _ _
  obtain ⟨sb, hsb⟩ := hNI (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] O') (R ⧸ J) ℓ
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O) τ)
    hℓ hτ' hfix' hdual' (Units.map (Ideal.Quotient.mk J).toMonoidHom r)
  obtain ⟨ψ, hψs, hψk, hψi, hψe⟩ := GlobalTheory.CompanionTheory.FirstApprox.res_compare O O' R
    (IsLocalRing.ResidueField O) (R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hkerπ : RingHom.ker (Ideal.Quotient.mkₐ O J) = J := by
    ext w
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hkerπ] at hψk
  obtain ⟨s0, hs0⟩ := hψs ↑sb
  obtain ⟨t0, ht0⟩ := hψs ↑(sb⁻¹)
  have hunit : IsUnit s0 := by
    have h1 : s0 * t0 - 1 ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) J :=
      hψk (by rw [RingHom.mem_ker, map_sub, map_mul, hs0, ht0, Units.mul_inv, map_one, sub_self])
    have h2 : IsUnit (1 + (s0 * t0 - 1)) :=
      GlobalTheory.CompanionTheory.JacUnit.main O O' R _ (by rw [← hJ]; exact h1)
    rw [show (1 : O' ⊗[O] R) + (s0 * t0 - 1) = s0 * t0 by ring] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hmap : ∀ j : ℕ, Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O))
      ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) =
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O)
        τ ^ j).toAlgHom := by
    intro j
    refine AlgHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul k w =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_eq_coe,
        AlgEquiv.coe_algHom, tensorProduct_congr_refl_pow_tmul_lemma]
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, ← hJ]
  refine hψk ?_
  rw [RingHom.mem_ker, map_sub, map_prod]
  simp_rw [hψe]
  rw [hψi, hs0, sub_eq_zero]
  refine Eq.trans ?_ (hsb.trans ?_)
  · refine Finset.prod_congr rfl fun j _ => ?_
    exact congrArg (fun g : (IsLocalRing.ResidueField O ⊗[O] O') →ₐ[IsLocalRing.ResidueField O]
        (IsLocalRing.ResidueField O ⊗[O] O') =>
      Algebra.TensorProduct.map g (AlgHom.id (IsLocalRing.ResidueField O) (R ⧸ J)) (sb : _)) (hmap j)
  · first
      | rfl
      | simp [Units.coe_map]

end GlobalTheory.CompanionTheory.FirstApprox
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimeDvdNotUnit
section
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.TraceJac

theorem exists_prime_dvd_not_unit {P A : Type*} [CommRing P] [IsDomain P]
    [UniqueFactorizationMonoid P] [CommRing A] (φ : P →+* A) (g : P) (hg : g ≠ 0)
    (h : ¬ IsUnit (φ g)) : ∃ π, Prime π ∧ π ∣ g ∧ ¬ IsUnit (φ π) := by
  revert hg h
  refine UniqueFactorizationMonoid.induction_on_prime g ?_ ?_ ?_
  · intro h0
    exact absurd rfl h0
  · intro x hx _ hxu
    exact absurd (hx.map φ) hxu
  · intro a p ha hp ih _ hpa
    by_cases hpu : IsUnit (φ p)
    · have hau : ¬ IsUnit (φ a) := fun hau => hpa (by rw [map_mul]; exact hpu.mul hau)
      obtain ⟨π, hπ, hπa, hπu⟩ := ih ha hau
      exact ⟨π, hπ, dvd_mul_of_dvd_right hπa p, hπu⟩
    · exact ⟨p, hp, dvd_mul_right p a, hpu⟩

section
variable {P A F L n : Type*} [CommRing P] [IsDomain P] [UniqueFactorizationMonoid P]
  [IsNoetherianRing P] [CommRing A] [IsDomain A] [Algebra P A] [Field F] [Algebra A F]
  [IsFractionRing A F] [Algebra P F] [IsScalarTower P A F] [Field L] [Algebra F L] [Algebra A L]
  [IsScalarTower A F L] [Algebra P L] [IsScalarTower P F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Fintype n] [DecidableEq n]

theorem main_abs (hinj : Function.Injective (algebraMap P A))
    (hloc : ∀ a : A, ∃ f g : P, IsUnit (algebraMap P A g) ∧ a * algebraMap P A g = algebraMap P A f)
    (E : n → Derivation ℤ L L) (hE : ∀ k f, ∃ f', E k (algebraMap P L f) = algebraMap P L f')
    (hjac : ∀ π : P, Prime π → ∃ j fj, E j (algebraMap P L π) = algebraMap P L fj ∧ ¬ π ∣ fj)
    (hnat : ∀ m : ℕ, m ≠ 0 → IsUnit (m : P))
    (c : L) (hc : IsIntegral A c) (b : n → L) (hb : ∀ l, IsIntegral A (b l)) :
    ∃ a : A, algebraMap A F a = Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) := by
  classical
  have hPF_inj : Function.Injective (algebraMap P F) := by
    rw [IsScalarTower.algebraMap_eq P A F]
    exact (IsFractionRing.injective A F).comp hinj
  have hne : ∀ g : P, IsUnit (algebraMap P A g) → algebraMap P F g ≠ 0 := by
    intro g hg h0
    have hg0 : g ≠ 0 := by
      rintro rfl
      simp at hg
    exact hg0 (hPF_inj (h0.trans (map_zero _).symm))
  have hloc' : ∀ a : A, ∃ f g : P, algebraMap P F g ≠ 0 ∧
      algebraMap A F a * algebraMap P F g = algebraMap P F f := by
    intro a
    obtain ⟨f, g, hg, hfg⟩ := hloc a
    refine ⟨f, g, hne g hg, ?_⟩
    rw [IsScalarTower.algebraMap_apply P A F g, IsScalarTower.algebraMap_apply P A F f, ← map_mul, hfg]
  haveI : IsFractionRing P F := by
    haveI : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective P F).2 hPF_inj
    refine IsFractionRing.of_field P F (fun z => ?_)
    obtain ⟨a, a', -, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    obtain ⟨f, g, hg, e1⟩ := hloc' a
    obtain ⟨f', g', hg', e2⟩ := hloc' a'
    refine ⟨f * g', g * f', ?_⟩
    rw [map_mul, map_mul, ← e1, ← e2]
    rw [show algebraMap A F a * algebraMap P F g * algebraMap P F g' /
        (algebraMap P F g * (algebraMap A F a' * algebraMap P F g')) =
        algebraMap A F a * (algebraMap P F g * algebraMap P F g') /
        (algebraMap A F a' * (algebraMap P F g * algebraMap P F g')) by ring]
    rw [mul_div_mul_right _ _ (mul_ne_zero hg hg')]
  have key : ∀ π : P, Prime π → ¬ IsUnit (algebraMap P A π) →
      ∃ f s : P, ¬ π ∣ s ∧ algebraMap P F s *
        Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) = algebraMap P F f := by
    intro π hπ hπu
    obtain ⟨j, fj, hfj, hj⟩ := hjac π hπ
    set p : Ideal P := Ideal.span {π} with hp
    haveI hpp : p.IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
    let R : Subalgebra P F :=
      Localization.subalgebra.ofField F p.primeCompl p.primeCompl_le_nonZeroDivisors
    haveI : IsScalarTower R F L := inferInstance
    haveI : IsScalarTower P R L := inferInstance
    haveI : IsLocalization.AtPrime R p := inferInstance
    have hr : ∀ a : A, algebraMap A L a ∈ (algebraMap R L).range := by
      intro a
      obtain ⟨f, g, hg, hfg⟩ := hloc a
      have hgp : g ∈ p.primeCompl := by
        intro hgmem
        apply hπu
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hgmem
        rw [map_mul] at hg
        exact isUnit_of_mul_isUnit_right hg
      refine ⟨IsLocalization.mk' R f ⟨g, hgp⟩, ?_⟩
      have h1 : algebraMap R F (IsLocalization.mk' R f ⟨g, hgp⟩) * algebraMap P F g = algebraMap P F f := by
        rw [IsScalarTower.algebraMap_apply P R F g, IsScalarTower.algebraMap_apply P R F f, ← map_mul,
          IsLocalization.mk'_spec]
      have h2 : algebraMap A F a * algebraMap P F g = algebraMap P F f := by
        rw [IsScalarTower.algebraMap_apply P A F g, IsScalarTower.algebraMap_apply P A F f, ← map_mul, hfg]
      have h3 : algebraMap R F (IsLocalization.mk' R f ⟨g, hgp⟩) = algebraMap A F a :=
        mul_right_cancel₀ (hne g hg) (h1.trans h2.symm)
      show algebraMap F L (algebraMap R F _) = _
      rw [h3, ← IsScalarTower.algebraMap_apply A F L]
    have hcR := integral_of_range hr c hc
    have hbR : ∀ l, IsIntegral R (b l) := fun l => integral_of_range hr (b l) (hb l)
    have hnatR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R) := fun m hm => by
      simpa using (hnat m hm).map (algebraMap P R)
    exact at_prime_abs (R := R) π hπ p hp E hE j fj hfj hj hnatR c hcR b hbR
  obtain ⟨n0, d0, hrel, hx0⟩ := IsFractionRing.exists_reduced_fraction (A := P)
    (Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det))
  have hd0 : (d0 : P) ≠ 0 := nonZeroDivisors.coe_ne_zero d0
  have hxd : Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) * algebraMap P F d0 =
      algebraMap P F n0 := by
    rw [← hx0]
    exact IsLocalization.mk'_spec F n0 d0
  by_cases hu : IsUnit (algebraMap P A d0)
  · obtain ⟨u, hu'⟩ := hu
    refine ⟨algebraMap P A n0 * ((u⁻¹ : Aˣ) : A), ?_⟩
    have hdF : algebraMap A F (algebraMap P A d0) = algebraMap P F d0 :=
      (IsScalarTower.algebraMap_apply P A F d0).symm
    have hnF : algebraMap A F (algebraMap P A n0) = algebraMap P F n0 :=
      (IsScalarTower.algebraMap_apply P A F n0).symm
    have hinv : algebraMap A F ((u⁻¹ : Aˣ) : A) * algebraMap P F d0 = 1 := by
      rw [← hdF, ← hu', ← map_mul, Units.inv_mul, map_one]
    rw [map_mul, hnF, ← hxd, mul_assoc, mul_comm (algebraMap P F _), hinv, mul_one]
  · obtain ⟨π, hπ, hπd, hπu⟩ := exists_prime_dvd_not_unit (algebraMap P A) (d0 : P) hd0 hu
    obtain ⟨f, s, hs, hfs⟩ := key π hπ hπu
    exfalso
    have h1 : algebraMap P F (s * n0) = algebraMap P F (f * d0) := by
      rw [map_mul, map_mul, ← hxd, ← hfs]
      ring
    have h2 := hPF_inj h1
    have hπn : π ∣ n0 := by
      have : π ∣ s * n0 := by
        rw [h2]
        exact dvd_mul_of_dvd_right hπd f
      exact (hπ.dvd_or_dvd this).resolve_left hs
    exact hπ.not_isUnit (hrel hπn hπd)
end

end GlobalTheory.CompanionTheory.TraceJac

namespace GlobalTheory.CompanionTheory.TraceJac

theorem deriv_aeval_mv {K L : Type*} [Field K] [Field L] [Algebra K L] {d : ℕ} (τ : Fin d → L)
    (D : Derivation K L L) (k : Fin d) (hD : ∀ j, D (τ j) = if k = j then 1 else 0)
    (f : MvPolynomial (Fin d) K) :
    D (MvPolynomial.aeval τ f) = MvPolynomial.aeval τ (MvPolynomial.pderiv k f) := by
  induction f using MvPolynomial.induction_on
  next a =>
    simp [MvPolynomial.aeval_C, MvPolynomial.pderiv_C]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p i hp =>
    simp only [map_mul, Derivation.leibniz, hp, MvPolynomial.aeval_X, hD, smul_eq_mul,
      MvPolynomial.pderiv_X, map_add]
    by_cases hki : k = i
    · subst hki
      simp
    · simp [hki, Pi.single_apply, Ne.symm hki]

theorem trace_jacobian_mem : ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (A : Type) [CommRing A] [IsDomain A] [Algebra K A] (t : Fin d → A), Function.Injective (MvPolynomial.aeval t : MvPolynomial (Fin d) K →ₐ[K] A) → (∀ a : A, ∃ f g : MvPolynomial (Fin d) K, IsUnit (MvPolynomial.aeval t g) ∧ a * MvPolynomial.aeval t g = MvPolynomial.aeval t f) → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ∀ (F L : Type) [Field F] [Field L] [Algebra A F] [IsFractionRing A F] [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower K B L] (D : Fin d → Derivation K L L), (∀ k j, D k (algebraMap A L (t j)) = if k = j then 1 else 0) → ∀ (c : B) (b : Fin d → B), ∃ a : A, algebraMap A F a = Algebra.trace F L (algebraMap B L c * (Matrix.of fun k l => D k (algebraMap B L (b l))).det) := by
  intro K _ _ d A _ _ _ t ht hloc B _ _ _ _ _ _ hAB F L _ _ _ _ _ _ _ _ _ _ _ _ D hD c b
  classical
  letI : Algebra (MvPolynomial (Fin d) K) A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin d) K) F :=
    ((algebraMap A F).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  letI : Algebra (MvPolynomial (Fin d) K) L :=
    ((algebraMap A L).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin d) K) A F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (MvPolynomial (Fin d) K) F L := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap A L _ = algebraMap F L (algebraMap A F _)
    exact IsScalarTower.algebraMap_apply A F L _)
  haveI : IsScalarTower K A L := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply K B L, IsScalarTower.algebraMap_apply K A B,
      ← IsScalarTower.algebraMap_apply A B L])
  haveI : FiniteDimensional F L := finite_frac (A := A) (B := B)
  haveI : CharZero A := (RingHom.charZero_iff (algebraMap K A).injective).1 inferInstance
  haveI : CharZero F := (RingHom.charZero_iff (IsFractionRing.injective A F)).1 inferInstance
  haveI : Algebra.IsSeparable F L := inferInstance
  have hτ : ∀ f : MvPolynomial (Fin d) K, algebraMap (MvPolynomial (Fin d) K) L f =
      MvPolynomial.aeval (fun i => algebraMap A L (t i)) f := by
    intro f
    show algebraMap A L (MvPolynomial.aeval t f) = _
    rw [← MvPolynomial.aeval_algebraMap_apply]
    rfl
  have hE : ∀ (k : Fin d) (f : MvPolynomial (Fin d) K), ∃ f',
      ((D k).restrictScalars ℤ) (algebraMap (MvPolynomial (Fin d) K) L f) =
        algebraMap (MvPolynomial (Fin d) K) L f' := by
    intro k f
    refine ⟨MvPolynomial.pderiv k f, ?_⟩
    rw [hτ, hτ]
    exact deriv_aeval_mv _ (D k) k (fun j => hD k j) f
  have hjac : ∀ π : MvPolynomial (Fin d) K, Prime π → ∃ j fj,
      ((D j).restrictScalars ℤ) (algebraMap (MvPolynomial (Fin d) K) L π) =
        algebraMap (MvPolynomial (Fin d) K) L fj ∧ ¬ π ∣ fj := by
    intro π hπ
    obtain ⟨j, hj⟩ := exists_pderiv_not_dvd π hπ
    refine ⟨j, MvPolynomial.pderiv j π, ?_, hj⟩
    rw [hτ, hτ]
    exact deriv_aeval_mv _ (D j) j (fun i => hD j i) π
  have hnat : ∀ m : ℕ, m ≠ 0 → IsUnit (m : MvPolynomial (Fin d) K) := by
    intro m hm
    have hmK : IsUnit (m : K) := (Nat.cast_ne_zero.2 hm).isUnit
    simpa using hmK.map (MvPolynomial.C : K →+* MvPolynomial (Fin d) K)
  have hc : IsIntegral A (algebraMap B L c) :=
    (Algebra.IsIntegral.isIntegral (R := A) c).map (IsScalarTower.toAlgHom A B L)
  have hb : ∀ l, IsIntegral A (algebraMap B L (b l)) := fun l =>
    (Algebra.IsIntegral.isIntegral (R := A) (b l)).map (IsScalarTower.toAlgHom A B L)
  obtain ⟨a, ha⟩ := main_abs (P := MvPolynomial (Fin d) K) (A := A) (F := F) (L := L) (n := Fin d)
    ht hloc (fun k => (D k).restrictScalars ℤ) hE hjac hnat (algebraMap B L c) hc
    (fun l => algebraMap B L (b l)) hb
  exact ⟨a, ha⟩

end GlobalTheory.CompanionTheory.TraceJac
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentialDecayByMidpointsStatement
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_decay_by_midpoints : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X) (S : Set (ℝ × ℝ)), (∀ a ∈ S, ∀ g : T, ∃ r : ℝ, 0 < r ∧ ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ x : ℝ × ℝ, |x.1 - a.1| ≤ r → |x.2 - a.2| ≤ r → ∀ g' ∈ U, ∀ t : ℝ × ℝ, ‖φ t g'‖ ≤ M * Real.exp (-rdot x t)) → (∀ x : ℝ × ℝ, ∃ a ∈ S, ∃ b ∈ S, x = midpoint ℝ a b) → ExpDecay φ := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.expDecay_of_midpoint | exact GlobalTheory.CompanionTheory.TubeFourier.expDecay_of_midpoint | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.expDecay_of_midpoint <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentialFourierIntegralBoundStatement
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_fourier_integral_bound : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (φ : ℝ × ℝ → X) (l : ℂ × ℂ) (ε M : ℝ), 0 < ε → Continuous φ → (∀ t : ℝ × ℝ, ‖φ t‖ ≤ M * Real.exp (-rdot (l.1.re, l.2.re) t) * Real.exp (-ε * (|t.1| + |t.2|))) → Integrable (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) ∧ ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖ ≤ M * (2 / ε) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.integrable_and_norm_integral_le | exact GlobalTheory.CompanionTheory.TubeFourier.integrable_and_norm_integral_le | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.integrable_and_norm_integral_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionLaw
section
noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisExt

variable {G : Type} [Group G]

theorem ext_mul {K P : Subgroup G} {f : G → ℝ} (hadd : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q)
    (hfK : ∀ p ∈ P, p ∈ K → f p = 0) {p k : G} (hp : p ∈ P) (hk : k ∈ K) :
    PositivityTheory.RgEis.ext K P f (p * k) = f p := by
  have hex : ∃ c : K, p * k * (c : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [PositivityTheory.RgEis.ext, dif_pos hex]
  have hcP : p * k * (hex.choose : G)⁻¹ ∈ P := hex.choose_spec
  have hq : p⁻¹ * (p * k * (hex.choose : G)⁻¹) ∈ P := P.mul_mem (P.inv_mem hp) hcP
  have hqK : p⁻¹ * (p * k * (hex.choose : G)⁻¹) ∈ K := by
    have he : p⁻¹ * (p * k * (hex.choose : G)⁻¹) = k * (hex.choose : G)⁻¹ := by group
    rw [he]
    exact K.mul_mem hk (K.inv_mem hex.choose.2)
  have h0 := hfK _ hq hqK
  have hsplit := hadd p hp _ hq
  rw [mul_inv_cancel_left] at hsplit
  rw [hsplit, h0, add_zero]

theorem extLaw : ExtLaw := by
  intro G _ _ _ _ Γ K P f hK hP hIwa hadd hfc hfK hfΓ
  have hval : ∀ p ∈ P, ∀ k ∈ K, PositivityTheory.RgEis.ext K P f (p * k) = f p :=
    fun p hp k hk => ext_mul hadd hfK hp hk
  have hone : ∀ p ∈ P, PositivityTheory.RgEis.ext K P f p = f p := by
    intro p hp
    simpa using hval p hp 1 K.one_mem
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hval⟩
  · intro p hp g
    obtain ⟨q, hq, k, hk, rfl⟩ := hIwa g
    rw [← mul_assoc, hval _ (P.mul_mem hp hq) k hk, hval q hq k hk, hone p hp, hadd p hp q hq]
  · intro g k hk
    obtain ⟨q, hq, k', hk', rfl⟩ := hIwa g
    rw [mul_assoc, hval q hq _ (K.mul_mem hk' hk), hval q hq k' hk']
  · intro γ hγ hγP
    rw [hone γ hγP]
    exact hfΓ γ hγP hγ
  · open Pointwise in
    · rw [continuous_iff_isClosed]
      intro C hC
      have hset : PositivityTheory.RgEis.ext K P f ⁻¹' C = ((P : Set G) ∩ f ⁻¹' C) * (K : Set G) := by
        ext g
        constructor
        · intro hg
          obtain ⟨q, hq, k, hk, rfl⟩ := hIwa g
          have hC' : PositivityTheory.RgEis.ext K P f (q * k) ∈ C := hg
          rw [hval q hq k hk] at hC'
          exact Set.mem_mul.mpr ⟨q, ⟨hq, hC'⟩, k, hk, rfl⟩
        · intro hg
          obtain ⟨q, ⟨hq, hqC⟩, k, hk, rfl⟩ := Set.mem_mul.mp hg
          show PositivityTheory.RgEis.ext K P f (q * k) ∈ C
          rw [hval q hq k hk]
          exact hqC
      rw [hset]
      exact (hfc.preimage_isClosed_of_isClosed hP hC).mul_right_of_isCompact hK

end GlobalTheory.CompanionTheory.RgEisExt
end
end

