import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedMonomialsLinearIndependentOverConstants
section
open scoped TensorProduct

namespace GlobalTheory

open MvPolynomial

theorem truncMono_deriv_aeval {k A : Type} [Field k] [CommRing A] [Algebra k A] {d : ℕ}
    (x : Fin d → A) (E : Fin d → Derivation k A A)
    (hE : ∀ i j, E i (x j) = if i = j then 1 else 0) (B : Subalgebra k A)
    (hB : ∀ i, ∀ b ∈ B, E i b = 0) (i : Fin d) (F : MvPolynomial (Fin d) B) :
    E i (aeval x F) = aeval x (pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C b =>
    rw [aeval_C, pderiv_C, map_zero]
    exact hB i _ b.2
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p j hp =>
    have h1 : E i (aeval x p * x j) = aeval x p * E i (x j) + x j * E i (aeval x p) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [map_mul, aeval_X, h1, hp, pderiv_mul, pderiv_X, map_add, map_mul, map_mul, aeval_X, hE]
    by_cases h : i = j
    · subst h; simp; ring
    · simp [h, Pi.single_apply, Ne.symm h]; ring

theorem truncMono_eq_zero {p : ℕ} [Fact p.Prime] {k A : Type} [Field k] [CommRing A]
    [Algebra k A] [CharP k p] {d : ℕ}
    (x : Fin d → A) (E : Fin d → Derivation k A A)
    (hE : ∀ i j, E i (x j) = if i = j then 1 else 0) (B : Subalgebra k A)
    (hB : ∀ i, ∀ b ∈ B, E i b = 0) :
    ∀ n : ℕ, ∀ F : MvPolynomial (Fin d) B,
      (∀ m ∈ F.support, (∀ i, m i < p) ∧ ∑ i, m i ≤ n) → aeval x F = 0 → F = 0 := by
  have hconst : ∀ F : MvPolynomial (Fin d) B, (∀ m, m ≠ 0 → coeff m F = 0) →
      aeval x F = 0 → F = 0 := by
    intro F hc hF
    have hFC : F = C (coeff 0 F) := by
      refine MvPolynomial.ext _ _ (fun m => ?_)
      rw [coeff_C]
      by_cases hm : m = 0
      · subst hm; simp
      · rw [if_neg (Ne.symm hm)]; exact hc m hm
    rw [hFC, aeval_C] at hF
    have h0 : coeff 0 F = 0 := Subtype.ext (by simpa using hF)
    rw [hFC, h0, C_0]
  intro n
  induction n with
  | zero =>
    intro F hs hF
    apply hconst F _ hF
    intro m hm
    by_contra hc
    have := (hs m (mem_support_iff.mpr hc)).2
    apply hm
    ext i
    have := (Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp this)) i (Finset.mem_univ _)
    simpa using this
  | succ n ih =>
    intro F hs hF
    have hpd : ∀ i, pderiv i F = 0 := by
      intro i
      apply ih
      · intro m hm
        rw [mem_support_iff, coeff_pderiv] at hm
        have hm' := hs _ (mem_support_iff.mpr (left_ne_zero_of_mul hm))
        refine ⟨fun j => lt_of_le_of_lt ?_ (hm'.1 j), ?_⟩
        · simp
        · have h2 := hm'.2
          simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib] at h2
          have h3 : ∑ j, (Finsupp.single i 1 : Fin d →₀ ℕ) j = 1 := by
            simp [Finsupp.single_apply]
          omega
      · rw [← truncMono_deriv_aeval x E hE B hB, hF, map_zero]
    apply hconst F _ hF
    intro m hm
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hm (Finsupp.ext h)
    by_contra hc
    have hlt := (hs m (mem_support_iff.mpr hc)).1 i
    have hcoef := coeff_pderiv (i := i) F (m - Finsupp.single i 1)
    rw [Finsupp.sub_add_single_one_cancel hi, hpd i, coeff_zero] at hcoef
    have hmi : (m - Finsupp.single i 1 : Fin d →₀ ℕ) i + 1 = m i := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
    have hunit : IsUnit (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) := by
      have e : (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) = algebraMap k B ((m i : ℕ) : k) := by
        rw [map_natCast, ← hmi]; push_cast; rfl
      rw [e]
      apply IsUnit.map
      apply Ne.isUnit
      rw [Ne, CharP.cast_eq_zero_iff k p]
      intro hdvd
      exact hi (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
    exact hc ((hunit.mul_left_eq_zero).mp hcoef.symm)

end GlobalTheory

namespace GlobalTheory
open MvPolynomial

theorem truncMono_linearIndependent : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] (d : ℕ) (x : Fin d → A) (E : Fin d → Derivation k A A), (∀ i j, E i (x j) = if i = j then 1 else 0) → ∀ B : Subalgebra k A, (∀ i, ∀ b ∈ B, E i b = 0) → LinearIndependent B (fun a : Fin d → Fin p => ∏ i, x i ^ (a i : ℕ)) := by
  intro p _ k A _ _ _ _ d x E hE B hB
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let toF : (Fin d → Fin p) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))
  have hinj : Function.Injective toF := by
    intro a b hab
    funext i
    apply Fin.ext
    have := congrArg (fun f : Fin d →₀ ℕ => f i) hab
    simpa [toF] using this
  let F : MvPolynomial (Fin d) B := ∑ a, monomial (toF a) (g a)
  have hcoeff : ∀ m, coeff m F = ∑ a, if toF a = m then g a else 0 := by
    intro m
    simp only [F, coeff_sum, coeff_monomial]
  have hF : aeval x F = 0 := by
    rw [← hg]
    simp only [F, map_sum, aeval_monomial]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Subalgebra.smul_def]
    rfl
  have hF0 : F = 0 := by
    refine truncMono_eq_zero x E hE B hB (∑ _i : Fin d, p) F ?_ hF
    intro m hm
    rw [mem_support_iff, hcoeff] at hm
    obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    have hm' : toF a = m := by
      by_contra h
      exact ha (if_neg h)
    subst hm'
    refine ⟨fun i => by simp [toF], ?_⟩
    apply Finset.sum_le_sum
    intro i _
    simp [toF, (a i).isLt.le]
  intro a
  have := hcoeff (toF a)
  rw [hF0, coeff_zero] at this
  simp_rw [hinj.eq_iff] at this
  simpa using this.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFixedCosetDecomposition
section
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwLangAb

theorem finite_nsmul_preimage {A : Type*} [AddCommGroup A] [Module.Finite ℤ A] (r : ℕ) (hr : 0 < r)
    (T : Set A) (hT : T.Finite) : {a : A | r • a ∈ T}.Finite := by
  let K : AddSubgroup A := (nsmulAddMonoidHom r : A →+ A).ker
  have h0 : Module.Finite ℤ (AddSubgroup.toIntSubmodule K) := inferInstance
  have h1 : Module.Finite ℤ K := h0
  have h2 : AddGroup.FG K := Module.Finite.iff_addGroup_fg.mp h1
  have hKf : Finite K := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun x => ?_
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨r, hr, ?_⟩
    apply Subtype.ext
    have hx : (nsmulAddMonoidHom r : A →+ A) (x : A) = 0 := AddMonoidHom.mem_ker.mp x.2
    simpa using hx
  have hKs : (K : Set A).Finite := Set.finite_coe_iff.mp hKf
  change ((fun a : A => r • a) ⁻¹' T).Finite
  refine hT.preimage' fun b _ => ?_
  by_cases hb : ∃ a0 : A, r • a0 = b
  · obtain ⟨a0, rfl⟩ := hb
    refine (hKs.image (fun k => a0 + k)).subset ?_
    intro a ha
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha
    refine ⟨a - a0, ?_, by simp⟩
    show a - a0 ∈ K
    simp [K, smul_sub, ha]
  · have : (fun a : A => r • a) ⁻¹' {b} = ∅ := by
      ext a; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun h => hb ⟨a, h⟩
    rw [this]; exact Set.finite_empty

theorem finite_pow_preimage {Q : Type*} [CommGroup Q] [Group.FG Q] (r : ℕ) (hr : 0 < r)
    (T : Set Q) (hT : T.Finite) : {x : Q | x ^ r ∈ T}.Finite := by
  haveI : AddGroup.FG (Additive Q) := inferInstance
  haveI : Module.Finite ℤ (Additive Q) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have h := finite_nsmul_preimage (A := Additive Q) r hr (Additive.toMul ⁻¹' T)
    (hT.preimage Additive.toMul.injective.injOn)
  refine (h.preimage (f := Additive.ofMul) Additive.ofMul.injective.injOn).subset ?_
  intro x hx
  simpa using hx

def fixedSubgroup {M : Type*} [Group M] (τ : M →* M) : Subgroup M where
  carrier := {x | τ x = x}
  one_mem' := map_one τ
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem iterate_eq_mul_prod {M : Type*} [CommGroup M] (τ : M →* M) (t : M) (i : ℕ) :
    (⇑τ)^[i] t = t * ∏ j ∈ Finset.range i, (⇑τ)^[j] (t⁻¹ * τ t) := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc (⇑τ)^[i + 1] t = (⇑τ)^[i] (τ t) := Function.iterate_succ_apply _ _ _
      _ = (⇑τ)^[i] (t * (t⁻¹ * τ t)) := by rw [mul_inv_cancel_left]
      _ = _ := by rw [iterate_map_mul, ih, Finset.prod_range_succ, mul_assoc]

theorem core {M : Type*} [CommGroup M] (τ : M →* M) (r : ℕ) (hr : 0 < r) (hτr : ∀ z, (⇑τ)^[r] z = z)
    (U : Subgroup M) (hU : ∀ u ∈ U, τ u ∈ U) (G : Set M) (hG : G.Finite)
    (hgen : ∀ z : M, z ∈ Subgroup.closure (G ∪ (U : Set M))) (F : Set M) (hF : F.Finite) :
    ∃ S : Finset M, ∀ t : M, (∃ f ∈ F, ∃ u ∈ U, t⁻¹ * τ t = f * u) →
      ∃ b, τ b = b ∧ ∃ s ∈ S, ∃ u ∈ U, t = b * s * u := by
  let B := fixedSubgroup τ
  let K : Subgroup M := U ⊔ B
  let π : M →* M ⧸ K := QuotientGroup.mk' K
  have hUK : U ≤ K := le_sup_left
  have hBK : B ≤ K := le_sup_right
  haveI : Group.FG (M ⧸ K) := by
    refine Group.fg_iff.2 ⟨π '' G, ?_, hG.image _⟩
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective K q
    refine Subgroup.closure_induction (p := fun x _ => π x ∈ Subgroup.closure (π '' G)) ?_ ?_ ?_ ?_ (hgen z)
    · intro x hx
      rcases hx with hx | hx
      · exact Subgroup.subset_closure ⟨x, hx, rfl⟩
      · have : π x = 1 := (QuotientGroup.eq_one_iff x).2 (hUK hx)
        rw [this]; exact one_mem _
    · rw [map_one]; exact one_mem _
    · intro x y _ _ hx hy
      rw [map_mul]; exact mul_mem hx hy
    · intro x _ hx
      rw [map_inv]; exact inv_mem hx
  let P : M → M := fun c => ∏ i ∈ Finset.range r, ∏ j ∈ Finset.range i, (⇑τ)^[j] c
  have hPmul : ∀ a b, P (a * b) = P a * P b := by
    intro a b
    simp only [P, iterate_map_mul, Finset.prod_mul_distrib]
  have hit : ∀ j : ℕ, ∀ u ∈ U, (⇑τ)^[j] u ∈ U := by
    intro j
    induction j with
    | zero => intro u hu; exact hu
    | succ j ih => intro u hu; rw [Function.iterate_succ_apply']; exact hU _ (ih u hu)
  have hPU : ∀ u ∈ U, P u ∈ U := by
    intro u hu
    exact Subgroup.prod_mem _ fun i _ => Subgroup.prod_mem _ fun j _ => hit j u hu
  have key : ∀ t : M, π t ^ r = (π (P (t⁻¹ * τ t)))⁻¹ := by
    intro t
    let N := ∏ i ∈ Finset.range r, (⇑τ)^[i] t
    have hN : τ N = N := by
      have e1 : τ N = ∏ i ∈ Finset.range r, (⇑τ)^[i + 1] t := by
        simp only [N, map_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Function.iterate_succ_apply']
      have e2 := Finset.prod_range_succ (fun i => (⇑τ)^[i] t) r
      have e3 := Finset.prod_range_succ' (fun i => (⇑τ)^[i] t) r
      rw [hτr t] at e2
      rw [Function.iterate_zero_apply] at e3
      rw [e1]
      have := e3.symm.trans e2
      exact mul_right_cancel this
    have hNe : N = t ^ r * P (t⁻¹ * τ t) := by
      simp only [N, P]
      rw [Finset.prod_congr rfl fun i _ => iterate_eq_mul_prod τ t i, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_range]
    have hNK : π N = 1 := (QuotientGroup.eq_one_iff N).2 (hBK hN)
    rw [hNe, map_mul, map_pow] at hNK
    exact eq_inv_of_mul_eq_one_left hNK
  let T : Set (M ⧸ K) := (fun f => (π (P f))⁻¹) '' F
  have hX : {x : M ⧸ K | x ^ r ∈ T}.Finite := finite_pow_preimage r hr T (hF.image _)
  let σ := Function.surjInv (QuotientGroup.mk'_surjective K)
  refine ⟨hX.toFinset.image σ, ?_⟩
  rintro t ⟨f, hf, u, hu, hc⟩
  have hxT : π t ∈ {x : M ⧸ K | x ^ r ∈ T} := by
    show π t ^ r ∈ T
    refine ⟨f, hf, ?_⟩
    have h1 : π (P u) = 1 := (QuotientGroup.eq_one_iff _).2 (hUK (hPU u hu))
    show (π (P f))⁻¹ = π t ^ r
    rw [key t, hc, hPmul, map_mul, h1, mul_one]
  have hs : π (σ (π t)) = π t := Function.surjInv_eq _ _
  have hmem : (σ (π t))⁻¹ * t ∈ K := QuotientGroup.eq.mp hs
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hmem
  refine ⟨z, hz, σ (π t), Finset.mem_image.2 ⟨π t, hX.mem_toFinset.2 hxT, rfl⟩, y, hy, ?_⟩
  have e : σ (π t) * (y * z) = t := by rw [hyz, mul_inv_cancel_left]
  calc t = σ (π t) * (y * z) := e.symm
    _ = z * σ (π t) * y := by ac_rfl

theorem exists_finite_reps_of_twisted_lang : ∀ {H : Type} [Group H] (Z U : Subgroup H) (τ : H →* H) (r : ℕ),
    0 < r → (∀ z ∈ Z, τ z ∈ Z) →
    (∀ z ∈ Z, (⇑τ)^[r] z = z) → (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) → U ≤ Z → (∀ u ∈ U, τ u ∈ U) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ (U : Set H))) →
    ∀ F : Finset H, ∃ S : Finset H, ∀ t ∈ Z, (∃ f ∈ F, ∃ u ∈ U, t⁻¹ * τ t = f * u) →
      ∃ b ∈ Z, τ b = b ∧ ∃ s ∈ S, ∃ u ∈ U, t = b * s * u := by
  intro H _ Z U τ r hr hτZ hτr hcomm hUZ hU hGex F
  obtain ⟨G, hGZ, hcl⟩ := hGex
  letI : CommGroup Z := { (inferInstance : Group Z) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let τ' : Z →* Z :=
    { toFun := fun z => ⟨τ z, hτZ z z.2⟩
      map_one' := Subtype.ext (map_one τ)
      map_mul' := fun a b => Subtype.ext (map_mul τ (a : H) (b : H)) }
  have hiter : ∀ (n : ℕ) (z : Z), (((⇑τ')^[n] z : Z) : H) = (⇑τ)^[n] (z : H) := by
    intro n
    induction n with
    | zero => intro z; rfl
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  let U' : Subgroup Z := U.subgroupOf Z
  let G' : Set Z := Subtype.val ⁻¹' (G : Set H)
  have hG' : G'.Finite := G.finite_toSet.preimage Subtype.val_injective.injOn
  have hle : Subgroup.closure ((G : Set H) ∪ (U : Set H)) ≤ Z :=
    (Subgroup.closure_le _).2 (Set.union_subset (fun g hg => hGZ g hg) hUZ)
  have hgen : ∀ z : Z, z ∈ Subgroup.closure (G' ∪ (U' : Set Z)) := by
    intro z
    have := Subgroup.closure_induction
      (p := fun x hx => (⟨x, hle hx⟩ : Z) ∈ Subgroup.closure (G' ∪ (U' : Set Z)))
      (fun x hx => by
        apply Subgroup.subset_closure
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (Subgroup.mem_subgroupOf.2 hx))
      (one_mem _)
      (fun x y _ _ hx hy => mul_mem hx hy)
      (fun x _ hx => inv_mem hx) (hcl z.2)
    simpa using this
  let F' : Set Z := Subtype.val ⁻¹' (F : Set H)
  have hF' : F'.Finite := F.finite_toSet.preimage Subtype.val_injective.injOn
  obtain ⟨S', hS'⟩ := core τ' r hr (fun z => Subtype.ext (by rw [hiter]; exact hτr (z : H) z.2)) U'
    (fun u hu => Subgroup.mem_subgroupOf.2 (hU _ (Subgroup.mem_subgroupOf.1 hu))) G' hG' hgen F' hF'
  refine ⟨S'.image Subtype.val, ?_⟩
  rintro t ht ⟨f, hf, u, hu, hc⟩
  have hfe : f = t⁻¹ * τ t * u⁻¹ := by rw [hc, mul_inv_cancel_right]
  have hfZ : f ∈ Z := by
    rw [hfe]
    exact mul_mem (mul_mem (inv_mem ht) (hτZ t ht)) (inv_mem (hUZ hu))
  obtain ⟨b, hb, s, hs, u', hu', he⟩ := hS' ⟨t, ht⟩
    ⟨⟨f, hfZ⟩, hf, ⟨u, hUZ hu⟩, Subgroup.mem_subgroupOf.2 hu, Subtype.ext hc⟩
  exact ⟨b, b.2, congrArg Subtype.val hb, s, Finset.mem_image_of_mem _ hs, u',
    Subgroup.mem_subgroupOf.1 hu', congrArg Subtype.val he⟩

end GlobalTheory.TwLangAb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceEquivariantAndInjectiveOfGroupDet
section
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem mulVec_eq_zero_of_det_nonZeroDivisor {n R : Type} [Fintype n] [DecidableEq n]
    [CommRing R] (A : Matrix n n R) (hA : A.det ∈ nonZeroDivisors R) (v : n → R)
    (hv : A *ᵥ v = 0) : v = 0 := by
  have h : A.det • v = 0 := by
    have := congrArg (fun w => A.adjugate *ᵥ w) hv
    simpa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec] using this
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hA).1 hi

theorem twistedTrace_equivariant_and_injective_of_groupDet :
    ∀ (H K R : Type) [Group H] [Fintype H] [DecidableEq H] [Field K] [CommRing R] [Algebra K R] (st : H → R →ₐ[K] R), (∀ x, st 1 x = x) → (∀ h h' x, st (h * h') x = st h' (st h x)) → ∀ (χ : H →* Kˣ) (u : R), (Matrix.of fun h g : H => st (h * g) u).det ∈ nonZeroDivisors R → (∀ (F : R) (g : H), st g (∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F) = ((χ g : Kˣ) : K) • ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F) ∧ (∀ f : R, (∀ h, ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g (f * st h u) = 0) → f = 0) ∧ (∀ F : H → R, (∀ h g, st g (F h) = ((χ g : Kˣ) : K) • F h) → ∑ h, F h * st h u = 0 → F = 0) := by
  intro H K R _ _ _ _ _ _ st h1 hmul χ u hdet
  refine ⟨?_, ?_, ?_⟩
  · intro F g
    rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
    rw [map_smul, ← hmul, Equiv.coe_mulRight, smul_smul, ← Units.val_mul]
    congr 2
    rw [map_mul, mul_inv_rev, mul_inv_cancel_left]
  · intro f hf
    have h := mulVec_eq_zero_of_det_nonZeroDivisor _ hdet
      (fun g => (((χ g)⁻¹ : Kˣ) : K) • st g f) (by
        funext h
        rw [Pi.zero_apply, ← hf h]
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul, ← hmul, mul_smul_comm, mul_comm])
    simpa [h1] using congrFun h 1
  · intro F hF h0
    refine mulVec_eq_zero_of_det_nonZeroDivisor (Matrix.of fun h g : H => st (h * g) u)ᵀ
      (by rwa [Matrix.det_transpose]) F ?_
    funext g
    have h2 := congrArg (st g) h0
    rw [map_sum, map_zero] at h2
    have h3 : ((χ g : Kˣ) : K) • ∑ h, st (h * g) u * F h = 0 := by
      rw [← h2, Finset.smul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [map_mul, hF, ← hmul, smul_mul_assoc, mul_comm]
    have h4 := congrArg (fun x => (((χ g)⁻¹ : Kˣ) : K) • x) h3
    simp only [smul_smul, Units.inv_mul, one_smul, smul_zero] at h4
    simpa [Matrix.mulVec, dotProduct] using h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldSumInvariantLeviConj
section
namespace GlobalTheory

theorem unfold_sum_conj_invariant : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → ∀ k ∈ KM, ∀ y : P, (∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * ((s k)⁻¹ * y * s k) * u (Quotient.out x))) = ∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * y * u (Quotient.out x)) := by
  intro P M N _ _ _ s π u hπs hu hker KP KM L hsK hπK hL F hF k hk y
  set c := s k with hc_def
  have hc : c ∈ KP := hsK k hk
  have hπu : ∀ X, π (u X) = 1 := fun X => (hker _).2 ⟨X, rfl⟩
  have hex : ∀ (d : P), ∀ X, ∃ Y, u Y = d * u X * d⁻¹ := by
    intro d X
    exact (hker _).1 (by simp [map_mul, map_inv, hπu])
  choose φ hφ using hex c
  choose ψ hψ using hex c⁻¹
  have h1 : ∀ X, φ (ψ X) = X := fun X => hu (by rw [hφ, hψ]; group)
  have h2 : ∀ X, ψ (φ X) = X := fun X => hu (by rw [hψ, hφ]; group)
  have hconj : ∀ z, c * z * c⁻¹ ∈ KP ↔ z ∈ KP := by
    intro z
    constructor
    · intro h
      have := KP.mul_mem (KP.mul_mem (KP.inv_mem hc) h) hc
      simpa [mul_assoc] using this
    · intro h
      exact KP.mul_mem (KP.mul_mem hc h) (KP.inv_mem hc)
  let eN : N ≃ N := ⟨φ, ψ, h2, h1⟩
  let e : N ⧸ L ≃ N ⧸ L := Quotient.congr eN (by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← hL, ← hL]
    simp only [eN, Equiv.coe_fn_mk, map_mul, map_inv, hφ]
    rw [← hconj]
    constructor <;> intro h <;> convert h using 1 <;> group)
  conv_rhs => rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro x
  set X := Quotient.out x with hX
  have hex' : e x = (QuotientGroup.mk (φ X) : N ⧸ L) := by
    conv_lhs => rw [← Quotient.out_eq x]
    rfl
  set Z := Quotient.out (e x) with hZ
  have hZL : Z⁻¹ * φ X ∈ L := by
    apply QuotientGroup.eq.mp
    rw [← hex']
    exact Quotient.out_eq _
  have hw : u (Z⁻¹ * φ X) ∈ KP := (hL _).2 hZL
  calc F ((u X)⁻¹ * (c⁻¹ * y * c) * u X) = F (c⁻¹ * ((u (φ X))⁻¹ * y * u (φ X)) * c) := by
        congr 1; rw [hφ]; group
    _ = F ((u (φ X))⁻¹ * y * u (φ X)) := hF c hc _
    _ = F ((u Z * u (Z⁻¹ * φ X))⁻¹ * y * (u Z * u (Z⁻¹ * φ X))) := by
        rw [← map_mul, mul_inv_cancel_left]
    _ = F ((u (Z⁻¹ * φ X))⁻¹ * ((u Z)⁻¹ * y * u Z) * u (Z⁻¹ * φ X)) := by
        congr 1; group
    _ = F ((u Z)⁻¹ * y * u Z) := hF _ hw _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularOfIsFundamentalDomainFinite
section
open scoped NNReal ENNReal
open MeasureTheory

theorem GlobalTheory.unimodular_of_isFundamentalDomain_finite : ∀ (S : Type) [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [T2Space S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S] (Γ : Subgroup S) [Countable Γ] (μS : Measure S) (𝓢 : Set S), μS.IsHaarMeasure → IsFundamentalDomain Γ 𝓢 μS → μS 𝓢 ≠ ⊤ → μS.IsMulRightInvariant := by
  intro S _ _ _ _ _ _ _ _ Γ _ μS 𝓢 hH hF hfin
  haveI : SMulInvariantMeasure Γ S μS :=
    ⟨fun c s _ => by
      show μS ((fun x => (c : S) * x) ⁻¹' s) = μS s
      exact measure_preimage_mul μS (c : S) s⟩
  have hpos : μS 𝓢 ≠ 0 := hF.measure_ne_zero (NeZero.ne μS)
  refine ⟨fun g => ?_⟩
  have hmap := Measure.map_right_mul_eq_modularCharacterFun_smul μS g

  have hF' : IsFundamentalDomain Γ ((fun x => x * g) ⁻¹' 𝓢) μS := by
    refine hF.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · exact quasiMeasurePreserving_mul_right μS g
    · intro γ x
      show (γ : S) * x * g = (γ : S) * (x * g)
      exact mul_assoc _ _ _
  have heq : μS ((fun x => x * g) ⁻¹' 𝓢) = μS 𝓢 := hF'.measure_eq hF
  have h2 : (Measure.map (fun x => x * g) μS) 𝓢 = μS 𝓢 := by
    rw [show (fun x : S => x * g) = ⇑(MeasurableEquiv.mulRight g) from rfl, MeasurableEquiv.map_apply]
    exact heq
  rw [hmap] at h2
  rw [Measure.smul_apply] at h2
  have hc : (Measure.modularCharacterFun g : ℝ≥0∞) = 1 := by
    have h3 : (Measure.modularCharacterFun g : ℝ≥0∞) * μS 𝓢 = 1 * μS 𝓢 := by
      rw [one_mul]; simpa [ENNReal.smul_def] using h2
    exact (ENNReal.mul_left_inj hpos hfin).mp h3
  rw [show (fun x : S => x * g) = fun x => x * g from rfl] at hmap
  rw [hmap]
  have : Measure.modularCharacterFun g = 1 := by exact_mod_cast hc
  rw [this, one_smul]
end

