import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightInvariantMulEqFinprodComponents
section
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem finprod_components_of_rightInvariant_mul :
    ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ) (a : Γ → ℂ),
      (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) →
      (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) →
      (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 →
      (∀ v g h, c v g = 1 → c v h = h → a (g * h) = a g * a h) →
      ∀ g, a g = ∏ᶠ v, a (c v g) := by
  intro Γ _ K ι c a hK hfin hidem horth hinv ha1 hmul
  classical

  have haK : ∀ k, k ∈ K → a k = 1 := by
    intro k hk
    have := hinv 1 k hk
    rw [one_mul] at this
    rw [this, ha1]
  have key : ∀ (s : Finset ι) (g : Γ), {v | c v g ∉ K} ⊆ (s : Set ι) →
      a g = ∏ v ∈ s, a (c v g) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have hgK : g ∈ K := (hK g).2 (fun v => by
        by_contra h
        simpa using hg h)
      simp [haK g hgK]
    | @insert v s hv ih =>
      intro g hg
      set g' := g * (c v g)⁻¹ with hg'
      have hcv : c v g' = 1 := by
        rw [hg', map_mul, map_inv, hidem, mul_inv_cancel]
      have hcw : ∀ w, w ≠ v → c w g' = c w g := by
        intro w hw
        rw [hg', map_mul, map_inv, horth v w g (Ne.symm hw), inv_one, mul_one]
      have hsupp : {w | c w g' ∉ K} ⊆ (s : Set ι) := by
        intro w hw
        simp only [Set.mem_setOf_eq] at hw
        by_cases hwv : w = v
        · subst hwv
          exact absurd (hcv ▸ K.one_mem) hw
        · rw [hcw w hwv] at hw
          have := hg hw
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at this
          exact this.resolve_left hwv
      have ih' := ih g' hsupp
      have hprod : ∏ w ∈ s, a (c w g') = ∏ w ∈ s, a (c w g) := by
        apply Finset.prod_congr rfl
        intro w hw
        rw [hcw w (fun h => hv (h ▸ hw))]
      have hsplit : g = g' * c v g := by
        rw [hg', inv_mul_cancel_right]
      have hag : a g = a g' * a (c v g) := by
        conv_lhs => rw [hsplit]
        exact hmul v g' (c v g) hcv (hidem v g)
      rw [hag, ih', hprod, Finset.prod_insert hv, mul_comm]
  intro g
  have hsub : Function.mulSupport (fun v => a (c v g)) ⊆ ((hfin g).toFinset : Set ι) := by
    intro w hw
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro hwK
    exact hw (haK _ hwK)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact key _ g (by simp)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomApplyEqPow
section
namespace GlobalTheory.FixedOfPower
open Polynomial

theorem fix_of_pow {k : Type} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (τ : k →+* k) (c : k) (hc : c ^ p = c) : τ c = c := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  let f : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  have hc' : ∃ a, f a = c := by
    by_contra hcon
    have hP0 : (X ^ p - X : k[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hp1
    have hsub : insert c (Finset.univ.image f) ⊆ (X ^ p - X : k[X]).roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hP0]
      show eval x (X ^ p - X) = 0
      rw [eval_sub, eval_pow, eval_X, sub_eq_zero]
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hc
      · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
        rw [← map_pow, ZMod.pow_card]
    have hcard : (insert c (Finset.univ.image f)).card = p + 1 := by
      rw [Finset.card_insert_of_notMem (by simpa using hcon),
        Finset.card_image_of_injective _ f.injective, Finset.card_univ, ZMod.card]
    have hle := (Finset.card_le_card hsub).trans
      ((Multiset.toFinset_card_le _).trans (card_roots' (X ^ p - X : k[X])))
    rw [hcard, FiniteField.X_pow_card_sub_X_natDegree_eq k hp1] at hle
    omega
  obtain ⟨a, rfl⟩ := hc'
  exact DFunLike.congr_fun (RingHom.ext_zmod (τ.comp f) f) a

theorem ringHom_apply_eq_pow {k : Type} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (τ : k →+* k) (N : ℕ) (hN : 0 < N) (z : k) (hz : z ^ p ^ N = z) :
    ∃ e : ℕ, τ z = z ^ p ^ e := by
  have : ExpChar k p := ExpChar.prime Fact.out
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  let g : k[X] := ∏ e ∈ Finset.range (M + 1), (X - C (z ^ p ^ e))
  have hg : g.map (frobenius k p) = g := by
    have e1 : ∀ e : ℕ, (z ^ p ^ e) ^ p = z ^ p ^ (e + 1) := fun e => by rw [← pow_mul, pow_succ]
    simp only [g, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      frobenius_def, e1]
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun e => X - C (z ^ p ^ e)), hz, pow_zero,
      pow_one]
  have hcoef : ∀ i, (g.coeff i) ^ p = g.coeff i := by
    intro i
    have h := congrArg (fun q : k[X] => q.coeff i) hg
    simpa [Polynomial.coeff_map, frobenius_def] using h
  have hτ : g.map τ = g := by
    ext i
    rw [Polynomial.coeff_map]
    exact fix_of_pow p τ _ (hcoef i)
  have hz0 : g.eval z = 0 := by
    simp only [g, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos M)) (by simp)
  have hτz : g.eval (τ z) = 0 := by
    rw [← hτ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hz0, map_zero]
  simp only [g, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hτz
  obtain ⟨e, -, he⟩ := Finset.prod_eq_zero_iff.mp hτz
  exact ⟨e, sub_eq_zero.mp he⟩

end GlobalTheory.FixedOfPower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfPerfectOfDvdSubAdicSeparated
section
open scoped NNReal

namespace GlobalTheory

theorem ringHom_eq_of_perfect_of_dvd_sub :
    ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by
  intro l _ R O _ _ _ _ _ x e he hH ψ ψ' h
  ext y
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  obtain ⟨z, rfl⟩ : ∃ z : R, z ^ l ^ n = y :=
    ⟨(iterateFrobeniusEquiv R l n).symm y, by
      have hs := (iterateFrobeniusEquiv R l n).apply_symm_apply y
      rwa [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at hs⟩
  rw [map_pow, map_pow, ← sub_pow_char_pow]
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hn : n ≤ e * l ^ n :=
    (Nat.lt_pow_self (by omega)).le.trans (Nat.le_mul_of_pos_left _ he)
  exact (pow_dvd_pow x hn).trans (by rw [pow_mul]; exact pow_dvd_pow_of_dvd (h z) _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomIsPushoutOfPiComponents
section
open TensorProduct

namespace GlobalTheory

theorem isPushout_of_pi_components_alg {A P A' P' : Type} [CommRing A] [CommRing P] [CommRing A']
    [CommRing P'] {n : ℕ} {Q Q' : Fin n → Type} [∀ i, CommRing (Q i)] [∀ i, CommRing (Q' i)]
    [Algebra A P] [Algebra A A'] [Algebra P P'] [Algebra A' P'] [Algebra A P']
    [IsScalarTower A P P'] [IsScalarTower A A' P']
    [∀ i, Algebra A (Q i)] [∀ i, Algebra (Q i) (Q' i)] [∀ i, Algebra A' (Q' i)]
    [∀ i, Algebra A (Q' i)] [∀ i, IsScalarTower A (Q i) (Q' i)] [∀ i, IsScalarTower A A' (Q' i)]
    (g : ∀ i, P →ₐ[A] Q i) (g' : ∀ i, P' →ₐ[A'] Q' i)
    (hg : Function.Bijective (fun (x : P) (i : Fin n) => g i x))
    (hg' : Function.Bijective (fun (x : P') (i : Fin n) => g' i x))
    (hk : ∀ i x, g' i (algebraMap P P' x) = algebraMap (Q i) (Q' i) (g i x))
    (H : ∀ i, Algebra.IsPushout A A' (Q i) (Q' i)) : Algebra.IsPushout A A' P P' := by
  have hpi := IsBaseChange.pi (S := A') (fun i => (IsScalarTower.toAlgHom A (Q i) (Q' i)).toLinearMap)
    (fun i => (H i).out)
  let e : P ≃ₗ[A] (∀ i, Q i) :=
    LinearEquiv.ofBijective (LinearMap.pi fun i => (g i).toLinearMap) hg
  let e' : P' ≃ₗ[A'] (∀ i, Q' i) :=
    LinearEquiv.ofBijective (LinearMap.pi fun i => (g' i).toLinearMap) hg'
  refine ⟨IsBaseChange.of_equiv
    (LinearEquiv.baseChange A A' _ _ e ≪≫ₗ hpi.equiv ≪≫ₗ e'.symm) fun x => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq,
    LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, one_smul]
  funext i
  exact (hk i x).symm

theorem isPushout_of_pi_components : ∀ {A P A' P' : Type} [CommRing A] [CommRing P] [CommRing A'] [CommRing P'] {n : ℕ}
    {Pi P'i : Fin n → Type} [∀ i, CommRing (Pi i)] [∀ i, CommRing (P'i i)]
    (f : A →+* P) (k : A →+* A') (k' : P →+* P') (h' : A' →+* P')
    (g : ∀ i, P →+* Pi i) (g' : ∀ i, P' →+* P'i i) (kk : ∀ i, Pi i →+* P'i i) (hh : ∀ i, A' →+* P'i i),
    Function.Bijective (fun (x : P) (i : Fin n) => g i x) →
    Function.Bijective (fun (x : P') (i : Fin n) => g' i x) →
    (∀ i, (g' i).comp k' = (kk i).comp (g i)) → (∀ i, (g' i).comp h' = hh i) →
    (∀ i, CategoryTheory.IsPushout (CommRingCat.ofHom ((g i).comp f)) (CommRingCat.ofHom k)
      (CommRingCat.ofHom (kk i)) (CommRingCat.ofHom (hh i))) →
    CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom k) (CommRingCat.ofHom k')
      (CommRingCat.ofHom h') := by
  intro A P A' P' _ _ _ _ n Q Q' _ _ f k k' h' g g' kk hh hg hg' hk hh' H
  have hw : ∀ i a, kk i (g i (f a)) = hh i (k a) := fun i a =>
    congrArg (fun φ : CommRingCat.of A ⟶ CommRingCat.of (Q' i) => φ.hom a) (H i).w
  have hk1 : ∀ i x, g' i (k' x) = kk i (g i x) := fun i x => RingHom.congr_fun (hk i) x
  have hh1 : ∀ i x, g' i (h' x) = hh i x := fun i x => RingHom.congr_fun (hh' i) x
  have hc : ∀ a, k' (f a) = h' (k a) := fun a => hg'.1 (funext fun i => by
    show g' i (k' (f a)) = g' i (h' (k a))
    rw [hk1, hh1, hw])
  letI : Algebra A P := f.toAlgebra
  letI : Algebra A A' := k.toAlgebra
  letI : Algebra P P' := k'.toAlgebra
  letI : Algebra A' P' := h'.toAlgebra
  letI : Algebra A P' := (k'.comp f).toAlgebra
  haveI : IsScalarTower A P P' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A A' P' := IsScalarTower.of_algebraMap_eq fun a => hc a
  letI : ∀ i, Algebra A (Q i) := fun i => ((g i).comp f).toAlgebra
  letI : ∀ i, Algebra (Q i) (Q' i) := fun i => (kk i).toAlgebra
  letI : ∀ i, Algebra A' (Q' i) := fun i => (hh i).toAlgebra
  letI : ∀ i, Algebra A (Q' i) := fun i => ((kk i).comp ((g i).comp f)).toAlgebra
  haveI : ∀ i, IsScalarTower A (Q i) (Q' i) := fun i => IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : ∀ i, IsScalarTower A A' (Q' i) := fun i => IsScalarTower.of_algebraMap_eq fun a => hw i a
  have H' : ∀ i, Algebra.IsPushout A A' (Q i) (Q' i) := fun i =>
    (CommRingCat.isPushout_iff_isPushout.mp (H i)).symm
  have := isPushout_of_pi_components_alg (A := A) (P := P) (A' := A') (P' := P') (Q := Q) (Q' := Q')
    (fun i => { g i with commutes' := fun _ => rfl })
    (fun i => { g' i with commutes' := fun a => hh1 i a }) hg hg' hk1 H'
  exact CommRingCat.isPushout_iff_isPushout.mpr this.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootsOfUnityInj
section
namespace GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues

theorem rootsOfUnity_inj {O k : Type} [CommRing O] [IsDomain O] [Field k] (f : O →+* k) {M : ℕ}
    (hM : (M : k) ≠ 0) {x y : O} (hx : x ^ M = 1) (hy : y ^ M = 1) (hf : f x = f y) : x = y := by
  have key : ∀ z : O, z ^ M = 1 → f z = 1 → z = 1 := by
    intro z hz hfz
    have h := geom_sum_mul z M
    rw [hz, sub_self] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exfalso
      apply hM
      have h2 := congrArg f h1
      simpa [map_sum, map_pow, hfz] using h2
    · exact sub_eq_zero.mp h1
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at hM
  have hsub : M - 1 + 1 = M := Nat.sub_add_cancel (Nat.pos_of_ne_zero hM0)
  have hyM : y ^ (M - 1) * y = 1 := by rw [← pow_succ, hsub, hy]
  have hz : (x * y ^ (M - 1)) ^ M = 1 := by
    rw [mul_pow, hx, ← pow_mul, mul_comm (M - 1) M, pow_mul, hy, one_pow, one_mul]
  have hfz : f (x * y ^ (M - 1)) = 1 := by
    rw [map_mul, map_pow, hf, ← pow_succ', hsub, ← map_pow, hy, map_one]
  have h1 := key _ hz hfz
  calc x = x * (y ^ (M - 1) * y) := by rw [hyM, mul_one]
    _ = (x * y ^ (M - 1)) * y := by ring
    _ = y := by rw [h1, one_mul]

theorem main : ∀ {O k : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field k] (f : O →+* k) {M : ℕ},
    (↑M : k) ≠ (0 : k) → ∀ {x y : O}, x ^ M = (1 : O) → y ^ M = (1 : O) →
      (f : O → k) x = (f : O → k) y → x = y :=
  fun f _ hM _ _ hx hy hf => rootsOfUnity_inj f hM hx hy hf

end GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScalarWeightSum
section
namespace GlobalTheory.WeightSum

theorem scalar_weight_sum {ι : Type} (S : Finset ι) (w : ι → ℤ) (a : ι → ℂ)
    (h : ∀ z : ℂ, ‖z‖ = 1 → ∑ s ∈ S, z ^ w s * a s = 0) :
    ∑ s ∈ S, (w s : ℂ) * a s = 0 := by
  have hG : HasDerivAt (fun u : ℂ => ∑ s ∈ S, Complex.exp ((w s : ℂ) * (u * Complex.I)) * a s)
      (∑ s ∈ S, ((w s : ℂ) * Complex.I) * a s) ((0 : ℝ) : ℂ) := by
    apply HasDerivAt.fun_sum
    intro s _
    have h1 : HasDerivAt (fun u : ℂ => (w s : ℂ) * (u * Complex.I)) ((w s : ℂ) * Complex.I)
        ((0 : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const Complex.I).const_mul (w s : ℂ)
    have h2 := h1.cexp.mul_const (a s)
    simpa using h2
  have hg := hG.comp_ofReal
  have hz : (fun t : ℝ => ∑ s ∈ S, Complex.exp ((w s : ℂ) * ((t : ℂ) * Complex.I)) * a s)
      = fun _ => (0 : ℂ) := by
    funext t
    have := h (Complex.exp (t * Complex.I)) (Complex.norm_exp_ofReal_mul_I t)
    simpa only [← Complex.exp_int_mul] using this
  rw [hz] at hg
  have h0 := hg.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  have h3 : (∑ s ∈ S, (w s : ℂ) * a s) * Complex.I = 0 := by
    rw [← h0, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  exact (mul_eq_zero.mp h3).resolve_right Complex.I_ne_zero

theorem weight_sum_mem {E : Type} [AddCommGroup E] [Module ℂ E] (V : Submodule ℂ E) {ι : Type}
    (S : Finset ι) (w : ι → ℤ) (f : ι → E)
    (h : ∀ z : ℂ, ‖z‖ = (1 : ℝ) → ∑ s ∈ S, z ^ w s • f s ∈ V) :
    ∑ s ∈ S, ((w s : ℤ) : ℂ) • f s ∈ V := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  have := scalar_weight_sum S w (fun s => φ (f s)) fun z hz => by
    simpa [map_sum] using hφ _ (h z hz)
  simpa [map_sum] using this

end GlobalTheory.WeightSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEquivariantMapsProportional
section
namespace GlobalTheory

theorem schur_proportional_of_range_le
    (H W X : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    [AddCommGroup X] [Module ℂ X] (ρ : H → Module.End ℂ W) (a : H → Module.End ℂ X)
    (φ ξ : W →ₗ[ℂ] X)
    (hirr : ∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤)
    (hξ : Function.Injective ξ) (hr : LinearMap.range φ ≤ LinearMap.range ξ)
    (hφe : ∀ h w, φ (ρ h w) = a h (φ w)) (hξe : ∀ h w, ξ (ρ h w) = a h (ξ w)) :
    ∃ c : ℂ, φ = c • ξ := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ξ (LinearMap.ker_eq_bot.mpr hξ)
  have hgx : ∀ v, g (ξ v) = v := fun v => by
    simpa using LinearMap.congr_fun hg v
  set A : Module.End ℂ W := g ∘ₗ φ with hA
  have hxA : ∀ w, ξ (A w) = φ w := by
    intro w
    obtain ⟨v, hv⟩ := hr (LinearMap.mem_range_self φ w)
    simp only [hA, LinearMap.comp_apply, ← hv, hgx]
  have hcomm : ∀ h w, A (ρ h w) = ρ h (A w) := by
    intro h w
    apply hξ
    rw [hxA, hφe, hξe, hxA]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hAv : A v = c • v := hv.apply_eq_smul
  let U : Submodule ℂ W := LinearMap.ker (A - c • LinearMap.id)
  have hmemU : ∀ u, u ∈ U ↔ A u = c • u := by
    intro u
    simp [U, sub_eq_zero]
  have hstab : ∀ h, U.map (ρ h) ≤ U := by
    intro h x hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    rw [hmemU] at hu ⊢
    rw [hcomm, hu, map_smul]
  have hne : U ≠ ⊥ := by
    intro hU
    have : v ∈ U := (hmemU v).mpr hAv
    rw [hU, Submodule.mem_bot] at this
    exact hv.2 this
  have htop : U = ⊤ := (hirr U hstab).resolve_left hne
  refine ⟨c, ?_⟩
  ext w
  have hw : w ∈ U := htop ▸ Submodule.mem_top
  rw [hmemU] at hw
  rw [LinearMap.smul_apply, ← hxA, hw, map_smul]

theorem schur_proportional :
    ∀ (H W X : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] [AddCommGroup X] [Module ℂ X] (ρ : H → Module.End ℂ W) (a : H → Module.End ℂ X) (φ ξ : W →ₗ[ℂ] X), (∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤) → Function.Injective ξ → LinearMap.range φ ≤ LinearMap.range ξ → (∀ h w, φ (ρ h w) = a h (φ w)) → (∀ h w, ξ (ρ h w) = a h (ξ w)) → ∃ c : ℂ, φ = c • ξ :=
  fun H W X _ _ _ _ _ _ _ ρ a φ ξ hirr hξ hr hφe hξe =>
    schur_proportional_of_range_le H W X ρ a φ ξ hirr hξ hr hφe hξe

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurIsotypicSplittingInnerProduct
section
namespace GlobalTheory

open Submodule

section SchurIsotypic
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma schur_act_inv (act : G →* Module.End ℂ H) (g : G) (y : H) : act g (act g⁻¹ y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

lemma schur_orth_stable (act : G →* Module.End ℂ H)
    (hact : ∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0)
    (P : Submodule ℂ H) (hP : ∀ g, ∀ p ∈ P, act g p ∈ P) :
    ∀ g, ∀ e ∈ Pᗮ, act g e ∈ Pᗮ := by
  intro g e he
  rw [Submodule.mem_orthogonal] at he ⊢
  intro u hu
  have := hact g _ _ (he _ (hP g⁻¹ u hu))
  rwa [schur_act_inv] at this

lemma schur_decomp [FiniteDimensional ℂ H] (P : Submodule ℂ H) (x : H) :
    ∃ p ∈ P, x - p ∈ Pᗮ := by
  exact ⟨P.starProjection x, P.starProjection_apply_mem x, P.sub_starProjection_mem_orthogonal x⟩

lemma schur_vanish {W : Type} [AddCommGroup W] [Module ℂ W] [Nontrivial W] [FiniteDimensional ℂ H]
    (act : G →* Module.End ℂ H)
    (hact : ∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0)
    (ρ : G →* Module.End ℂ W)
    (hirr : ∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤)
    (E : Submodule ℂ H) (hE : ∀ g, ∀ e ∈ E, act g e ∈ E)
    (hEorth : ∀ χ : W →ₗ[ℂ] H, (∀ g w, χ (ρ g w) = act g (χ w)) →
      ∀ w, ∀ e ∈ E, inner ℂ (χ w) e = 0)
    (φ : H →ₗ[ℂ] W) (hφ : ∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) : ∀ e ∈ E, φ e = 0 := by
  by_contra hne
  push_neg at hne
  obtain ⟨e₀, he₀E, he₀⟩ := hne
  let K : Submodule ℂ H := LinearMap.ker φ ⊓ E
  have hK : ∀ g, ∀ k ∈ K, act g k ∈ K := by
    intro g k hk
    obtain ⟨hk1, hk2⟩ := Submodule.mem_inf.1 hk
    refine Submodule.mem_inf.2 ⟨?_, hE g k hk2⟩
    rw [LinearMap.mem_ker] at hk1 ⊢
    rw [hφ g k hk2, hk1, map_zero]
  let C : Submodule ℂ H := Kᗮ ⊓ E
  have hC : ∀ g, ∀ c ∈ C, act g c ∈ C := fun g c hc =>
    Submodule.mem_inf.2 ⟨schur_orth_stable act hact K hK g c (Submodule.mem_inf.1 hc).1,
      hE g c (Submodule.mem_inf.1 hc).2⟩
  have hCE : ∀ c ∈ C, c ∈ E := fun c hc => (Submodule.mem_inf.1 hc).2
  have hinj : ∀ c ∈ C, φ c = 0 → c = 0 := by
    intro c hc h0
    have hcK : c ∈ K := Submodule.mem_inf.2 ⟨h0, hCE c hc⟩
    have := (Submodule.mem_orthogonal _ _).1 (Submodule.mem_inf.1 hc).1 c hcK
    exact inner_self_eq_zero.1 this
  have hU : C.map φ = ⊤ := by
    rcases hirr (C.map φ) (by
      intro g
      rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨act g c, hC g c hc, hφ g c (hCE c hc)⟩) with h | h
    · exfalso
      obtain ⟨p, hp, hr⟩ := schur_decomp K e₀
      have hrE : e₀ - p ∈ E := E.sub_mem he₀E (Submodule.mem_inf.1 hp).2
      have hrC : e₀ - p ∈ C := Submodule.mem_inf.2 ⟨hr, hrE⟩
      have hm : φ (e₀ - p) ∈ C.map φ := Submodule.mem_map_of_mem hrC
      rw [h, Submodule.mem_bot, map_sub, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hp).1,
        sub_zero] at hm
      exact he₀ hm
    · exact h
  let ψ : C →ₗ[ℂ] W := φ.comp C.subtype
  have hψi : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    exact Subtype.ext (hinj c c.2 (LinearMap.mem_ker.1 hc))
  have hψs : Function.Surjective ψ := by
    intro w
    have hw : w ∈ C.map φ := hU ▸ Submodule.mem_top
    obtain ⟨c, hc, hcw⟩ := hw
    exact ⟨⟨c, hc⟩, hcw⟩
  let e := LinearEquiv.ofBijective ψ ⟨hψi, hψs⟩
  let χ : W →ₗ[ℂ] H := C.subtype.comp e.symm.toLinearMap
  have hχC : ∀ w, χ w ∈ C := fun w => (e.symm w).2
  have hφχ : ∀ w, φ (χ w) = w := fun w => by
    show ψ (e.symm w) = w
    exact e.apply_symm_apply w
  have hχ : ∀ g w, χ (ρ g w) = act g (χ w) := by
    intro g w
    have hd : χ (ρ g w) - act g (χ w) ∈ C := C.sub_mem (hχC _) (hC g _ (hχC w))
    have := hinj _ hd (by rw [map_sub, hφχ, hφ g _ (hCE _ (hχC w)), hφχ, sub_self])
    exact sub_eq_zero.1 this
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have h0 : χ w = 0 := inner_self_eq_zero.1 (hEorth χ hχ w (χ w) (hCE _ (hχC w)))
  exact hw (by rw [← hφχ w, h0, map_zero])

end SchurIsotypic

theorem schur_isotypic_splitting : ∀ {G W H : Type} [Group G] [AddCommGroup W] [Module ℂ W] [Nontrivial W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (act : G →* Module.End ℂ H), (∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0) → ∀ (ρ : G →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ x : H, ∃ q ∈ Submodule.span ℂ {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}, ∃ E : Submodule ℂ H, (∀ g, ∀ e ∈ E, act g e ∈ E) ∧ (∀ φ : H →ₗ[ℂ] W, (∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) → ∀ e ∈ E, φ e = 0) ∧ x - q ∈ E := by
  intro G W H _ _ _ _ _ _ _ act hact ρ hirr x
  let S : Set H := {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}
  let I : Submodule ℂ H := Submodule.span ℂ S
  have hI : ∀ g, ∀ y ∈ I, act g y ∈ I := by
    intro g y hy
    have hle : I.map (act g) ≤ I := by
      rw [Submodule.map_span]
      apply Submodule.span_le.2
      rintro _ ⟨_, ⟨φ, w, hφ, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨φ, ρ g w, hφ, (hφ g w).symm⟩
    exact hle (Submodule.mem_map_of_mem hy)
  obtain ⟨q, hq, hxq⟩ := schur_decomp I x
  refine ⟨q, hq, Iᗮ, schur_orth_stable act hact I hI, ?_, hxq⟩
  intro φ hφ
  refine schur_vanish act hact ρ hirr Iᗮ (schur_orth_stable act hact I hI) ?_ φ hφ
  intro χ hχ w e he
  exact (Submodule.mem_orthogonal _ _).1 he _ (Submodule.subset_span ⟨χ, w, hχ, rfl⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumEqSumCompEmbedding
section
namespace GlobalTheory.EmbeddingSum

theorem sum_eq_sum_comp_embedding :
    ∀ {N j : ℕ} (e : Fin j ↪ Fin N) (f : Fin N → ℂ),
      (∀ c ∉ Set.range (⇑e : Fin j → Fin N), f c = (0 : ℂ)) →
      ∑ c : Fin N, f c = ∑ a : Fin j, f ((e : Fin j → Fin N) a) := by
  intro N j e f h
  rw [← Finset.sum_map Finset.univ e f]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro c _ hc
  refine h c ?_
  rintro ⟨a, rfl⟩
  exact hc (Finset.mem_map_of_mem e (Finset.mem_univ a))

end GlobalTheory.EmbeddingSum
end

