import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DirectedSystemEtaleBaseChangePolynomial
section
open IsLocalRing Polynomial TensorProduct

namespace GlobalTheory

theorem tensor_directedSystem_of_flat (R : Type) [CommRing R] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] (k₀ : ι) (P : ι → Type) [∀ k, CommRing (P k)]
    [instP : ∀ k, Algebra R (P k)] (Q : Type) [CommRing Q] [Algebra R Q]
    (E₀ : Type) [CommRing E₀] [Algebra R E₀] [Module.Flat R E₀]
    (inc : ∀ k l, k ≤ l → P k →ₐ[R] P l) (sub : ∀ k, P k →ₐ[R] Q)
    (hinc_id : ∀ k (hkk : k ≤ k) (p : P k), inc k k hkk p = p)
    (hinc_comp : ∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (p : P k),
      inc k m hkm p = inc l m hlm (inc k l hkl p))
    (hsub_comp : ∀ k l (hkl : k ≤ l) (p : P k), sub l (inc k l hkl p) = sub k p)
    (hsub_inj : ∀ k, Function.Injective (sub k))
    (hcov : ∀ q : Q, ∃ k p, sub k p = q) :
    ∃ (h : ∀ k l, k ≤ l → P k ⊗[R] E₀ →+* P l ⊗[R] E₀) (e : ∀ k, P k ⊗[R] E₀ →+* Q ⊗[R] E₀),
      (∀ k l (hkl : k ≤ l) (p : P k) (y : E₀), h k l hkl (p ⊗ₜ y) = inc k l hkl p ⊗ₜ y) ∧
      (∀ k (p : P k) (y : E₀), e k (p ⊗ₜ y) = sub k p ⊗ₜ y) ∧
      (∀ k l (hkl : k ≤ l) (y : P k ⊗[R] E₀), e l (h k l hkl y) = e k y) ∧
      (∀ k (hkk : k ≤ k) (y : P k ⊗[R] E₀), h k k hkk y = y) ∧
      (∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (y : P k ⊗[R] E₀),
          h k m hkm y = h l m hlm (h k l hkl y)) ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ z : Q ⊗[R] E₀, ∃ k y, e k y = z) := by
  let h : ∀ k l, k ≤ l → P k ⊗[R] E₀ →+* P l ⊗[R] E₀ := fun k l hkl =>
    (Algebra.TensorProduct.map (inc k l hkl) (AlgHom.id R E₀)).toRingHom
  let e : ∀ k, P k ⊗[R] E₀ →+* Q ⊗[R] E₀ := fun k =>
    (Algebra.TensorProduct.map (sub k) (AlgHom.id R E₀)).toRingHom
  have hh : ∀ k l (hkl : k ≤ l) (p : P k) (y : E₀), h k l hkl (p ⊗ₜ y) = inc k l hkl p ⊗ₜ y :=
    fun k l hkl p y => by simp [h]
  have he : ∀ k (p : P k) (y : E₀), e k (p ⊗ₜ y) = sub k p ⊗ₜ y :=
    fun k p y => by simp [e]
  have hcompat : ∀ k l (hkl : k ≤ l) (y : P k ⊗[R] E₀), e l (h k l hkl y) = e k y := by
    intro k l hkl y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p z => rw [hh, he, he, hsub_comp]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  refine ⟨h, e, hh, he, hcompat, ?_, ?_, ?_, ?_⟩
  · intro k hkk y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p z => rw [hh, hinc_id]
    | add a b ha hb => rw [map_add, ha, hb]
  · intro k l m hkl hlm hkm y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p z => rw [hh, hh, hh, hinc_comp k l m hkl hlm hkm]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  · intro k
    have hfun : ⇑(e k) = ⇑(LinearMap.rTensor E₀ (sub k).toLinearMap) := by
      funext z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul p y => rw [he, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      | add a b ha hb => rw [map_add, map_add, ha, hb]
    rw [hfun]
    exact Module.Flat.rTensor_preserves_injective_linearMap _ (hsub_inj k)
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨k₀, 0, map_zero _⟩
    | tmul q y =>
      obtain ⟨k, p, rfl⟩ := hcov q
      exact ⟨k, p ⊗ₜ y, he k p y⟩
    | add a b ha hb =>
      obtain ⟨k₁, y₁, rfl⟩ := ha
      obtain ⟨k₂, y₂, rfl⟩ := hb
      obtain ⟨m, h₁, h₂⟩ := directed_of (· ≤ ·) k₁ k₂
      exact ⟨m, h k₁ m h₁ y₁ + h k₂ m h₂ y₂, by rw [map_add, hcompat, hcompat]⟩

theorem directedSystem_etaleBaseChange : ∀ (T : Type) [CommRing T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (i₀ : ι), (∀ k, i₀ ≤ k) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E]
      (E₀ : Type) [CommRing E₀] [Algebra (Polynomial (𝒜 i₀)) E₀] [Algebra.Etale (Polynomial (𝒜 i₀)) E₀],
      (letI : Algebra (Polynomial (𝒜 i₀)) (Polynomial T) :=
          (Polynomial.mapRingHom (𝒜 i₀).subtype).toAlgebra
       Nonempty (TensorProduct (Polynomial (𝒜 i₀)) (Polynomial T) E₀ ≃ₐ[Polynomial T] E)) →
    ∃ (Ek : ι → Type) (_ : ∀ k, CommRing (Ek k)) (_ : ∀ k, Algebra (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra (𝒜 k) (Ek k)) (_ : ∀ k, IsScalarTower (𝒜 k) (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra.Etale (Polynomial (𝒜 k)) (Ek k))
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k, (e k).comp (algebraMap (Polynomial (𝒜 k)) (Ek k)) =
          (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 k).subtype)) ∧
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) ∧
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) ∧
      (∀ k (hkk : k ≤ k) (y : Ek k), h k k hkk y = y) ∧
      (∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (y : Ek k),
          h k m hkm y = h l m hlm (h k l hkl y)) ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ x : E, ∃ k y, e k y = x) := by
  intro T _ ι _ _ 𝒜 hA hcov i₀ h₀ E _ _ E₀ _ _ _ hφ
  obtain ⟨φ⟩ := hφ
  letI instA : ∀ k, Algebra (𝒜 i₀)[X] (𝒜 k)[X] := fun k =>
    (mapRingHom (Subring.inclusion (hA (h₀ k)))).toAlgebra
  letI instT : Algebra (𝒜 i₀)[X] T[X] := (mapRingHom (𝒜 i₀).subtype).toAlgebra
  have hincl : ∀ {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c),
      (Subring.inclusion (hA hbc)).comp (Subring.inclusion (hA hab)) =
        Subring.inclusion (hA (hab.trans hbc)) := by
    intro a b c hab hbc; ext x; rfl
  have hsub : ∀ {a b : ι} (hab : a ≤ b),
      (𝒜 b).subtype.comp (Subring.inclusion (hA hab)) = (𝒜 a).subtype := by
    intro a b hab; ext x; rfl
  let inc : ∀ k l, k ≤ l → (𝒜 k)[X] →ₐ[(𝒜 i₀)[X]] (𝒜 l)[X] := fun k l hkl =>
    { toRingHom := mapRingHom (Subring.inclusion (hA hkl))
      commutes' := fun p => by
        change Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
        rw [Polynomial.map_map, hincl (h₀ k) hkl] }
  let sub : ∀ k, (𝒜 k)[X] →ₐ[(𝒜 i₀)[X]] T[X] := fun k =>
    { toRingHom := mapRingHom (𝒜 k).subtype
      commutes' := fun p => by
        change Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
        rw [Polynomial.map_map, hsub (h₀ k)] }
  haveI : Module.Flat (𝒜 i₀)[X] E₀ := inferInstance
  have hcovT : ∀ q : T[X], ∃ k p, sub k p = q := by
    intro q
    have hq : ∃ k, ∀ n, q.coeff n ∈ 𝒜 k := by
      induction q using Polynomial.induction_on' with
      | add p q hp hq =>
        obtain ⟨k₁, h₁⟩ := hp
        obtain ⟨k₂, h₂⟩ := hq
        obtain ⟨m, hm₁, hm₂⟩ := directed_of (· ≤ ·) k₁ k₂
        exact ⟨m, fun n => by
          rw [coeff_add]; exact add_mem (hA hm₁ (h₁ n)) (hA hm₂ (h₂ n))⟩
      | monomial n c =>
        obtain ⟨j, hj⟩ := hcov c
        refine ⟨j, fun m => ?_⟩
        rw [coeff_monomial]
        split_ifs
        · exact hj
        · exact zero_mem _
    obtain ⟨k, hk⟩ := hq
    have hsubset : (↑q.coeffs : Set T) ⊆ 𝒜 k := by
      intro c hc
      obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
      exact hk n
    refine ⟨k, q.toSubring (𝒜 k) hsubset, ?_⟩
    show Polynomial.map (𝒜 k).subtype _ = q
    exact Polynomial.map_toSubring _ _ _
  obtain ⟨h, e', hh, he, hcompat, hid, hcomp, hinj, hcov'⟩ :=
    tensor_directedSystem_of_flat (𝒜 i₀)[X] i₀ (fun k => (𝒜 k)[X]) (instP := instA) T[X] E₀ inc sub
      (fun k hkk p => by
        have hid : Subring.inclusion (hA hkk) = RingHom.id _ := by ext; rfl
        show Polynomial.map _ p = p
        rw [hid, Polynomial.map_id])
      (fun k l m hkl hlm hkm p => by
        show Polynomial.map _ p = Polynomial.map _ (Polynomial.map _ p)
        rw [Polynomial.map_map, hincl hkl hlm])
      (fun k l hkl p => by
        show Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
        rw [Polynomial.map_map, hsub hkl])
      (fun k p q hpq => Polynomial.map_injective _ Subtype.val_injective hpq)
      hcovT
  let instC : ∀ k, Algebra (𝒜 k) (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀) := fun k =>
    ((algebraMap (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀)).comp (Polynomial.C)).toAlgebra
  have instS : ∀ k, @IsScalarTower (𝒜 k) (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀) _ _
      (instC k).toSMul := fun k =>
    letI := instC k
    IsScalarTower.of_algebraMap_eq (fun a => by
        change (algebraMap (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀)) (Polynomial.C a) =
          (algebraMap (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀)) (algebraMap (𝒜 k) (𝒜 k)[X] a)
        rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply])
  refine ⟨fun k => TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀, fun k => inferInstance,
    fun k => inferInstance, instC, instS, fun k => inferInstance,
    fun k => φ.toRingHom.comp (e' k), h, ?_, ?_, ?_, hid, hcomp, ?_, ?_⟩
  · intro k
    refine RingHom.ext fun p => ?_
    show φ (e' k (p ⊗ₜ 1)) = algebraMap T[X] E (Polynomial.map (𝒜 k).subtype p)
    rw [he, ← φ.commutes]
    rfl
  · intro k l hkl a
    show h k l hkl (C a ⊗ₜ 1) = C (Subring.inclusion (hA hkl) a) ⊗ₜ 1
    rw [hh]
    show Polynomial.map _ (C a) ⊗ₜ 1 = _
    rw [Polynomial.map_C]
  · intro k l hkl y
    exact congrArg φ (hcompat k l hkl y)
  · intro k
    exact φ.injective.comp (hinj k)
  · intro x
    obtain ⟨k, y, hy⟩ := hcov' (φ.symm x)
    refine ⟨k, y, ?_⟩
    show φ (e' k y) = x
    rw [hy, AlgEquiv.apply_symm_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierSchurOfRankLeAleph0
section
open Polynomial

namespace GlobalTheory

theorem isUnit_aeval_of_forall_isUnit_sub {A : Type*} [Ring A] [Algebra ℂ A] (T : A)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ A c)) (q : ℂ[X]) (hq : q ≠ 0) :
    IsUnit (aeval T q) := by
  have hs : spectrum ℂ T = ∅ := by
    ext c
    simp only [Set.mem_empty_iff_false, iff_false, spectrum.notMem_iff]
    simpa using (h c).neg
  by_cases hd : 0 < q.degree
  · have h1 := spectrum.map_polynomial_aeval_of_degree_pos T q hd
    rw [hs, Set.image_empty] at h1
    have h0 : (0 : ℂ) ∉ spectrum ℂ (aeval T q) := by rw [h1]; simp
    exact (spectrum.zero_notMem_iff ℂ).1 h0
  · have h2 : q = C (q.coeff 0) := eq_C_of_degree_le_zero (not_lt.1 hd)
    have h3 : q.coeff 0 ≠ 0 := fun h => hq (by rw [h2, h, C_0])
    rw [h2, aeval_C]
    exact (IsUnit.mk0 _ h3).map _

theorem linearIndependent_of_sub_apply_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c))
    (v : V) (hv : v ≠ 0) (w : ℂ → V)
    (hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v) :
    LinearIndependent ℂ w := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  set q : ℂ[X] := ∑ k ∈ s, C (g k) * ∏ j ∈ s.erase k, (X - C j) with hqdef
  have hq0 : aeval T q v = 0 := by
    have h1 : ∀ k ∈ s, aeval T (C (g k) * ∏ j ∈ s.erase k, (X - C j)) v
        = aeval T (∏ j ∈ s, (X - C j : ℂ[X])) (g k • w k) := by
      intro k hk
      rw [← Finset.prod_erase_mul s _ hk, ← hw k, map_mul, map_mul, aeval_C, map_sub, aeval_X,
        aeval_C, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
        map_smul, map_smul]
    rw [hqdef, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl h1, ← map_sum, hg, map_zero]
  have hq : q = 0 := by
    by_contra hne
    have hu := isUnit_aeval_of_forall_isUnit_sub T h q hne
    have hinj := ((Module.End.isUnit_iff _).1 hu).1
    exact hv (hinj (by rw [hq0, map_zero]))
  have h2 : eval i q = g i * ∏ j ∈ s.erase i, (i - j) := by
    rw [hqdef, eval_finset_sum, Finset.sum_eq_single i]
    · simp [eval_prod]
    · intro k _ hki
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨hki.symm, hi⟩)
        (by simp), mul_zero]
    · intro h; exact absurd hi h
  rw [hq, eval_zero] at h2
  refine (mul_eq_zero.1 h2.symm).resolve_right ?_
  exact Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (Finset.mem_erase.1 hj).1.symm

theorem dixmier_schur_of_rank_le_aleph0 :
    ∀ (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V) (T : Module.End ℂ V),
      Nontrivial V → Module.rank ℂ V ≤ Cardinal.aleph0 →
      (∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1 := by
  intro V ι _ _ ρ T hV hrank hirr hcomm
  by_contra hne
  push_neg at hne
  have hunit : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c) := by
    intro c
    set S := T - algebraMap ℂ (Module.End ℂ V) c with hS
    have hS0 : S ≠ 0 := by
      intro h0
      apply hne c
      rw [← Algebra.algebraMap_eq_smul_one]
      exact sub_eq_zero.1 h0
    have hSc : ∀ i x, S (ρ i x) = ρ i (S x) := by
      intro i x
      have := LinearMap.congr_fun (hcomm i) x
      simp only [Module.End.mul_apply] at this
      simp [hS, this, Module.algebraMap_end_apply]
    rw [Module.End.isUnit_iff]
    constructor
    · rw [← LinearMap.ker_eq_bot]
      refine (hirr _ ?_).resolve_right ?_
      · intro i x hx
        rw [LinearMap.mem_ker] at hx ⊢
        rw [hSc, hx, map_zero]
      · rw [LinearMap.ker_eq_top]; exact hS0
    · rw [← LinearMap.range_eq_top]
      refine (hirr _ ?_).resolve_left ?_
      · rintro i _ ⟨x, rfl⟩
        exact ⟨ρ i x, hSc i x⟩
      · rw [LinearMap.range_eq_bot]; exact hS0
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  choose w hw using fun c => ((Module.End.isUnit_iff _).1 (hunit c)).2 v
  have hli := linearIndependent_of_sub_apply_eq T hunit v hv w hw
  have h1 := hli.cardinal_le_rank.trans hrank
  rw [Cardinal.mk_complex] at h1
  exact absurd h1 (not_le.2 Cardinal.aleph0_lt_continuum)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetCardDivCardInfCommutativeSubgroup
section
open scoped Pointwise

namespace GlobalTheory.DCIndex

variable {A : Type} [Group A]

theorem normal_of_comm (hc : ∀ a b : A, a * b = b * a) (V : Subgroup A) : V.Normal :=
  ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩

theorem mem_sup_iff (hc : ∀ a b : A, a * b = b * a) (P Q : Subgroup A) {x : A} :
    x ∈ P ⊔ Q ↔ ∃ p ∈ P, ∃ q ∈ Q, p * q = x := by
  haveI : Q.Normal := normal_of_comm hc Q
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem card_quot_eq_index (hc : ∀ a b : A, a * b = b * a) (P V : Subgroup A) :
    Nat.card (DoubleCoset.Quotient (P : Set A) (V : Set A)) = (P ⊔ V).index := by
  rw [Subgroup.index]
  apply Nat.card_congr
  refine Quotient.congr (Equiv.refl A) ?_
  intro x y
  simp only [Equiv.refl_apply]
  rw [DoubleCoset.rel_iff, QuotientGroup.leftRel_apply, mem_sup_iff hc]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [hc a x, mul_assoc, inv_mul_cancel_left]
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [hc a x, mul_assoc, h, mul_inv_cancel_left]

theorem relIndex_split (hc : ∀ a b : A, a * b = b * a) (h u c : Subgroup A) (huc : u ≤ c) :
    u.relIndex c = (h ⊓ u).relIndex (h ⊓ c) * (h ⊔ u).relIndex (h ⊔ c) := by
  haveI : u.Normal := normal_of_comm hc u
  haveI : (h ⊔ u).Normal := normal_of_comm hc (h ⊔ u)
  have hM : (h ⊔ u) ⊓ c = (h ⊓ c) ⊔ u := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff hc h u).1 hx1
      have hpc : p ∈ c := by
        have := c.mul_mem hx2 (c.inv_mem (huc hq))
        rwa [mul_inv_cancel_right] at this
      exact (mem_sup_iff hc _ _).2 ⟨p, Subgroup.mem_inf.2 ⟨hp, hpc⟩, q, hq, rfl⟩
    · exact sup_le (inf_le_inf_right c le_sup_left) (le_inf le_sup_right huc)
  have e1 := Subgroup.relIndex_mul_relIndex (H := u) (K := (h ⊔ u) ⊓ c) (L := c)
    (le_inf le_sup_right huc) inf_le_right
  have e2 : ((h ⊔ u) ⊓ c).relIndex c = (h ⊔ u).relIndex (h ⊔ c) := by
    rw [Subgroup.inf_relIndex_right, ← Subgroup.relIndex_sup_right (H := c) (K := h ⊔ u)]
    congr 1
    apply le_antisymm
    · exact sup_le le_sup_right (sup_le le_sup_left (huc.trans le_sup_right))
    · exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
  have e3 : u.relIndex ((h ⊔ u) ⊓ c) = (h ⊓ u).relIndex (h ⊓ c) := by
    rw [hM, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right (H := u) (K := h ⊓ c)]
    congr 1
    apply le_antisymm
    · exact le_inf (inf_le_right.trans inf_le_left) inf_le_left
    · exact le_inf inf_le_right (inf_le_inf_left h huc)
  rw [← e1, e2, e3]

theorem card_split (h u c : Subgroup A) (huc : u ≤ c) :
    (h ⊓ u).relIndex (h ⊓ c) * Nat.card (h ⊓ u : Subgroup A) = Nat.card (h ⊓ c : Subgroup A) := by
  have hle : h ⊓ u ≤ h ⊓ c := inf_le_inf_left h huc
  have := Subgroup.card_mul_index ((h ⊓ u).subgroupOf (h ⊓ c))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at this
  rw [Subgroup.relIndex, mul_comm, this]

end GlobalTheory.DCIndex

namespace GlobalTheory.DCIndex

theorem card_inf_subgroupOf {G : Type} [Group G] (T H U : Subgroup G) (hUT : U ≤ T) :
    Nat.card (H.subgroupOf T ⊓ U.subgroupOf T : Subgroup T) = Nat.card (H ⊓ U : Subgroup G) := by
  have he : H.subgroupOf T ⊓ U.subgroupOf T = (H ⊓ U).subgroupOf T := by
    ext x; simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [he]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hUT)).toEquiv

theorem index_identity : ∀ {G : Type} [Group G] (T H U C : Subgroup G), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → U ≤ C → C ≤ T → U.relIndex C ≠ 0 → (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((U.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ U : Subgroup G) : ℂ) = (U.relIndex C : ℂ) * (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ C : Subgroup G) : ℂ) := by
  intro G _ T H U C hcomm hUC hCT hne
  have hc : ∀ a b : T, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
  have hu'c' : U.subgroupOf T ≤ C.subgroupOf T := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hUC hx
  have hrel : (U.subgroupOf T).relIndex (C.subgroupOf T) = U.relIndex C :=
    Subgroup.relIndex_subgroupOf hCT
  rw [card_quot_eq_index hc, card_quot_eq_index hc, ← card_inf_subgroupOf T H U (hUC.trans hCT),
    ← card_inf_subgroupOf T H C hCT, ← hrel]
  rw [← hrel] at hne
  have hU := (Subgroup.relIndex_mul_index
    (sup_le_sup_left hu'c' (H.subgroupOf T))).symm
  have hsplit := relIndex_split hc (H.subgroupOf T) _ _ hu'c'
  have hcard := card_split (H.subgroupOf T) _ _ hu'c'
  rw [hU, hsplit, ← hcard]
  rw [hsplit] at hne
  have hs : (((H.subgroupOf T ⊓ U.subgroupOf T).relIndex (H.subgroupOf T ⊓ C.subgroupOf T) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (left_ne_zero_of_mul hne)
  push_cast
  rw [mul_assoc, mul_div_mul_left _ _ hs]

end GlobalTheory.DCIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOperatorsCommOfAntiInvolution
section
open scoped BigOperators

namespace GlobalTheory

namespace GelfandTrick

variable {G : Type} [Group G]

def InDoubleCoset (J : Subgroup G) (a y : G) : Prop := ∃ k₁ ∈ J, ∃ k₂ ∈ J, y = k₁ * a * k₂

theorem InDoubleCoset.mul {J : Subgroup G} {a y z j₁ j₂ : G} (h : InDoubleCoset J a y)
    (h₁ : j₁ ∈ J) (h₂ : j₂ ∈ J) (hz : z = j₁ * y * j₂) : InDoubleCoset J a z := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h
  exact ⟨j₁ * k₁, J.mul_mem h₁ hk₁, k₂ * j₂, J.mul_mem hk₂ h₂, by rw [hz]; group⟩

open Classical in

theorem card_pairs_le (J : Subgroup G) (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a)
    (hinv : ∀ a, τ (τ a) = a) (hdc : ∀ g : G, ∃ k₁ ∈ J, ∃ k₂ ∈ J, τ g = k₁ * g * k₂)
    (hJ : ∀ k ∈ J, τ k ∈ J) (α β : G) (R S : Finset G)
    (hR : ∀ γ ∈ R, InDoubleCoset J α γ)
    (hR' : ∀ x : G, InDoubleCoset J α x → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J)
    (hS : ∀ γ ∈ S, InDoubleCoset J β γ)
    (hS' : ∀ x : G, InDoubleCoset J β x → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ J) (c : G ⧸ J) :
    ((R ×ˢ S).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card ≤
      ((S ×ˢ R).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have hone : τ 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hτinv : ∀ a, τ a⁻¹ = (τ a)⁻¹ := fun a => by
    have := hmul a a⁻¹
    rw [mul_inv_cancel, hone] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  have hτdc : ∀ a y, InDoubleCoset J a y → InDoubleCoset J a (τ y) := fun a y h => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hdc y
    exact h.mul hk₁ hk₂ e
  obtain ⟨k₁, hk₁, k₂, hk₂, hx⟩ := hdc x
  refine Finset.card_le_card_of_forall_subsingleton
    (fun p q => q.1⁻¹ * (x * k₂ * (τ p.1)⁻¹) ∈ J) ?_ ?_
  · rintro ⟨γ, δ⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp
    obtain ⟨⟨hγ, hδ⟩, hj⟩ := hp
    have h1 : τ x = τ ((γ * δ)⁻¹ * x) * τ δ * τ γ := by
      rw [← hmul, ← hmul]; congr 1; group
    have h2 : InDoubleCoset J β (x * k₂ * (τ γ)⁻¹) := by
      refine (hτdc _ _ (hS δ hδ)).mul (J.mul_mem (J.inv_mem hk₁) (hJ _ hj)) J.one_mem ?_
      have : x * k₂ = k₁⁻¹ * τ x := by rw [hx]; group
      rw [this, h1]; group
    obtain ⟨δ', ⟨hδ', hj'⟩, -⟩ := hS' _ h2
    have h3 : InDoubleCoset J α (δ'⁻¹ * x) :=
      (hτdc _ _ (hR γ hγ)).mul hj' (J.inv_mem hk₂) (by group)
    obtain ⟨γ', ⟨hγ', hj''⟩, -⟩ := hR' _ h3
    refine ⟨(δ', γ'), ?_, hj'⟩
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq]
    refine ⟨⟨hδ', hγ'⟩, ?_⟩
    rwa [mul_inv_rev, mul_assoc]
  · rintro ⟨δ', γ'⟩ - ⟨γ₁, δ₁⟩ h₁ ⟨γ₂, δ₂⟩ h₂
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_product,
      QuotientGroup.eq, Finset.mem_coe] at h₁ h₂
    obtain ⟨⟨⟨hγ₁, hδ₁⟩, hj₁⟩, hr₁⟩ := h₁
    obtain ⟨⟨⟨hγ₂, hδ₂⟩, hj₂⟩, hr₂⟩ := h₂
    have h4 : γ₂⁻¹ * γ₁ ∈ J := by
      have := hJ _ (J.mul_mem (J.inv_mem hr₁) hr₂)
      have e : (δ'⁻¹ * (x * k₂ * (τ γ₁)⁻¹))⁻¹ * (δ'⁻¹ * (x * k₂ * (τ γ₂)⁻¹))
          = τ (γ₂⁻¹ * γ₁) := by rw [hmul, hτinv]; group
      rwa [e, hinv] at this
    have hγ : γ₁ = γ₂ :=
      (hR' γ₁ (hR γ₁ hγ₁)).unique ⟨hγ₁, by simpa using J.one_mem⟩ ⟨hγ₂, h4⟩
    subst hγ
    have h5 : InDoubleCoset J β (γ₁⁻¹ * x) := (hS δ₁ hδ₁).mul J.one_mem hj₁ (by group)
    have hδ : δ₁ = δ₂ :=
      (hS' _ h5).unique ⟨hδ₁, by rwa [mul_inv_rev, mul_assoc] at hj₁⟩
        ⟨hδ₂, by rwa [mul_inv_rev, mul_assoc] at hj₂⟩
    rw [hδ]

end GelfandTrick

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualProdLogDerivModSq
section
open MvPolynomial

namespace GlobalTheory

theorem dualProd_logDeriv_modSq : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (δ : Derivation K R R) {N : ℕ} (e f : Fin N → R) (I : Ideal R), (∀ i, δ (e i) = 0) → (∀ i, e i ^ 2 ∈ I) → δ (∏ i, (1 + e i * f i)) - (∏ i, (1 + e i * f i)) * ∑ i, e i * δ (f i) ∈ I := by
  intro K R _ _ _ δ N
  induction N with
  | zero => intro e f I _ _; simp
  | succ n ih =>
    intro e f I he he2
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    have h := ih (fun i => e i.succ) (fun i => f i.succ) I (fun i => he _) (fun i => he2 _)
    set P := ∏ i : Fin n, (1 + e i.succ * f i.succ)
    set S := ∑ i : Fin n, e i.succ * δ (f i.succ)
    have key : δ ((1 + e 0 * f 0) * P) - (1 + e 0 * f 0) * P * (e 0 * δ (f 0) + S)
        = (1 + e 0 * f 0) * (δ P - P * S) - e 0 ^ 2 * (f 0 * P * δ (f 0)) := by
      simp only [Derivation.leibniz, map_add, Derivation.map_one_eq_zero, he 0, smul_eq_mul]
      ring
    rw [key]
    exact I.sub_mem (I.mul_mem_left _ h) (I.mul_mem_right _ (he2 0))

end GlobalTheory
end

