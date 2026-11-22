import ReciprocityTheory.DualLattices.Bundle0001
import ReciprocityTheory.DualLattices.Bundle0003
import Mathlib
import ReciprocityTheory.DualLattices.SqZeroOfSpan

-- bundled from ReciprocityTheory.DualLattices.FischerSmulRight
section
noncomputable section

open MvPolynomial Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

def fw (A : Fin ν × ι →₀ ℕ) : ℂ := ((A.prod fun _ e => e.factorial : ℕ) : ℂ)

private theorem finsupp_prod_factorial_add_single_one (B : Fin ν × ι →₀ ℕ) (v : Fin ν × ι) :
    (B + Finsupp.single v 1).prod (fun _ e => e.factorial)
      = B.prod (fun _ e => e.factorial) * (B v + 1) := by
  have hv : v ∈ insert v B.support := Finset.mem_insert_self v B.support
  have h1 : (B + Finsupp.single v 1).support ⊆ insert v B.support := by
    intro x hx
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply] at hx
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases hxv : x = v
    · exact Or.inl hxv
    · right
      rwa [if_neg (Ne.symm hxv), add_zero] at hx
  have h2 : B.support ⊆ insert v B.support := Finset.subset_insert v B.support
  have hrest : ∏ x ∈ (insert v B.support).erase v, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial
      = ∏ x ∈ (insert v B.support).erase v, (B x).factorial := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hx).symm, add_zero]
  calc (B + Finsupp.single v 1).prod (fun _ e => e.factorial)
      = ∏ x ∈ insert v B.support, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial :=
        Finsupp.prod_of_support_subset _ h1 _ (fun _ _ => Nat.factorial_zero)
    _ = ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) v).factorial
          * ∏ x ∈ (insert v B.support).erase v, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial :=
        (Finset.mul_prod_erase _ (fun x => ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial) hv).symm
    _ = (B v).factorial * (∏ x ∈ (insert v B.support).erase v, (B x).factorial) * (B v + 1) := by
        rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]; ring
    _ = (∏ x ∈ insert v B.support, (B x).factorial) * (B v + 1) := by
        rw [← Finset.mul_prod_erase _ _ hv]
    _ = B.prod (fun _ e => e.factorial) * (B v + 1) := by
        rw [Finsupp.prod_of_support_subset _ h2 _ (fun _ _ => Nat.factorial_zero)]

theorem fw_add_single (B : Fin ν × ι →₀ ℕ) (v : Fin ν × ι) :
    fw (B + Finsupp.single v 1) = fw B * ((B v : ℂ) + 1) := by
  unfold fw
  rw [finsupp_prod_factorial_add_single_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

theorem fischer_eq_sum (P Q : MvPolynomial (Fin ν × ι) ℂ) (S : Finset (Fin ν × ι →₀ ℕ))
    (hS : P.support ⊆ S) :
    fischer P Q = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
  have key : ∀ T : Finset (Fin ν × ι →₀ ℕ), P.support ⊆ T →
      ∑ A ∈ T, coeff A P * starRingEnd ℂ (coeff A Q) * fw A
        = ∑ A ∈ P.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
    intro T hT
    symm
    apply Finset.sum_subset hT
    intro A _ hA
    have h0 : coeff A P = 0 := by simpa [MvPolynomial.mem_support_iff] using hA
    simp [h0]
  calc fischer P Q
      = ∑ A ∈ P.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
        unfold fischer
        exact key _ (fun x hx => Finset.mem_union_left _ hx)
    _ = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := (key S hS).symm

theorem fischer_add_left (P P' Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (P + P') Q = fischer P Q + fischer P' Q := by
  have hsub : (P + P').support ⊆ P.support ∪ P'.support := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add] at hA
    rw [Finset.mem_union, MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    rw [h.1, h.2, add_zero] at hA
    exact hA rfl
  rw [fischer_eq_sum (P + P') Q (P.support ∪ P'.support) hsub,
    fischer_eq_sum P Q (P.support ∪ P'.support) (fun x hx => Finset.mem_union_left _ hx),
    fischer_eq_sum P' Q (P.support ∪ P'.support) (fun x hx => Finset.mem_union_right _ hx),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fischer_smul_left (c : ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (c • P) Q = c * fischer P Q := by
  have hsub : (c • P).support ⊆ P.support := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul] at hA
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hA
    rw [h, smul_zero]
  rw [fischer_eq_sum (c • P) Q P.support hsub,
    fischer_eq_sum P Q P.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fischer_add_right (P Q Q' : MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (Q + Q') = fischer P Q + fischer P Q' := by
  rw [fischer_eq_sum P (Q + Q') P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q' P.support (Finset.Subset.refl _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_add, map_add]
  ring

theorem fischer_smul_right (c : ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (c • Q) = starRingEnd ℂ c * fischer P Q := by
  rw [fischer_eq_sum P (c • Q) P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q P.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul]
  ring

theorem fischer_sum_right {α : Type*} (s : Finset α) (P : MvPolynomial (Fin ν × ι) ℂ)
    (f : α → MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (∑ i ∈ s, f i) = ∑ i ∈ s, fischer P (f i) := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rw [fischer_eq_sum P 0 P.support (Finset.Subset.refl _)]
    simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_right, ih]

theorem fischer_sum_left {α : Type*} (s : Finset α) (f : α → MvPolynomial (Fin ν × ι) ℂ)
    (Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (∑ i ∈ s, f i) Q = ∑ i ∈ s, fischer (f i) Q := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rw [fischer_eq_sum 0 Q ∅ (by simp)]
    simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_left, ih]

theorem fischer_C_left (c : ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (C c) Q = c * starRingEnd ℂ (coeff 0 Q) := by
  have hsub : (C c : MvPolynomial (Fin ν × ι) ℂ).support ⊆ {0} := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hA
    rw [Finset.mem_singleton]
    by_contra h
    exact hA (if_neg (fun e => h e.symm))
  rw [fischer_eq_sum (C c) Q {0} hsub, Finset.sum_singleton, MvPolynomial.coeff_C, if_pos rfl]
  simp [fw]

private theorem fischer_eq_sum_of_support_subset (P Q : MvPolynomial (Fin ν × ι) ℂ)
    (S : Finset (Fin ν × ι →₀ ℕ)) (hS : Q.support ⊆ S) :
    fischer P Q = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
  have key : ∀ T : Finset (Fin ν × ι →₀ ℕ), Q.support ⊆ T →
      ∑ A ∈ T, coeff A P * starRingEnd ℂ (coeff A Q) * fw A
        = ∑ A ∈ Q.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
    intro T hT
    symm
    apply Finset.sum_subset hT
    intro A _ hA
    have h0 : coeff A Q = 0 := by simpa [MvPolynomial.mem_support_iff] using hA
    simp [h0]
  calc fischer P Q
      = ∑ A ∈ Q.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
        unfold fischer
        exact key _ (fun x hx => Finset.mem_union_right _ hx)
    _ = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := (key S hS).symm

private theorem fischer_monomial_right (P : MvPolynomial (Fin ν × ι) ℂ)
    (m : Fin ν × ι →₀ ℕ) (b : ℂ) :
    fischer P (monomial m b) = coeff m P * starRingEnd ℂ b * fw m := by
  rw [fischer_eq_sum_of_support_subset P (monomial m b) {m} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

theorem fischer_mul_X (P Q : MvPolynomial (Fin ν × ι) ℂ) (v : Fin ν × ι) :
    fischer (P * X v) Q = fischer P (pderiv v Q) := by
  induction Q using MvPolynomial.induction_on'
  next m b =>
    rw [MvPolynomial.pderiv_monomial, fischer_monomial_right, fischer_monomial_right,
      MvPolynomial.coeff_mul_X']
    split_ifs with h
    · have hv : m v ≠ 0 := Finsupp.mem_support_iff.1 h
      have hm : m - Finsupp.single v 1 + Finsupp.single v 1 = m := by
        ext x
        rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with hx
        · subst hx
          omega
        · omega
      have hw : fw m = fw (m - Finsupp.single v 1) * (m v : ℂ) := by
        have h1 := fw_add_single (m - Finsupp.single v 1) v
        rw [hm, Finsupp.tsub_apply, Finsupp.single_eq_same,
          Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hv), Nat.cast_one, sub_add_cancel] at h1
        exact h1
      rw [hw, map_mul, map_natCast]
      ring
    · have hv : m v = 0 := by simpa [Finsupp.mem_support_iff] using h
      rw [hv]
      simp
  next Q₁ Q₂ h₁ h₂ =>
    rw [fischer_add_right, map_add, fischer_add_right, h₁, h₂]

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.MapTensorSpan
section
noncomputable section

namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem map_tensorSpan {X Y : Type} (σ : Y → X) (M : Submodule R (X → C)) :
    (tensorSpan R M).map (LinearMap.funLeft R C (Prod.map σ σ)) =
      tensorSpan R (M.map (LinearMap.funLeft R C σ)) := by
  rw [tensorSpan, tensorSpan, Submodule.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨_, ⟨g, hg, h, hh, rfl⟩, rfl⟩
    exact ⟨_, Submodule.mem_map_of_mem hg, _, Submodule.mem_map_of_mem hh, by
      funext p; simp [LinearMap.funLeft_apply]⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, _, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, h, hh, rfl⟩, by funext p; simp [LinearMap.funLeft_apply]⟩

def slice2 {X : Type} (E : (X → C) →ₗ[C] (X → C)) : (X × X → C) →ₗ[C] (X × X → C) where
  toFun F p := E (fun a => E (fun b => F (a, b)) p.2) p.1
  map_add' F G := by
    funext p
    have h2 : (fun a => E (fun b => (F + G) (a, b)) p.2) =
        (fun a => E (fun b => F (a, b)) p.2) + (fun a => E (fun b => G (a, b)) p.2) := by
      funext a
      rw [show (fun b => (F + G) (a, b)) = (fun b => F (a, b)) + (fun b => G (a, b)) from rfl,
        map_add]
      rfl
    show E (fun a => E (fun b => (F + G) (a, b)) p.2) p.1 =
      E (fun a => E (fun b => F (a, b)) p.2) p.1 + E (fun a => E (fun b => G (a, b)) p.2) p.1
    rw [h2, map_add]
    rfl
  map_smul' c F := by
    funext p
    have h2 : (fun a => E (fun b => (c • F) (a, b)) p.2) =
        c • (fun a => E (fun b => F (a, b)) p.2) := by
      funext a
      rw [show (fun b => (c • F) (a, b)) = c • (fun b => F (a, b)) from rfl, map_smul]
      rfl
    show E (fun a => E (fun b => (c • F) (a, b)) p.2) p.1 =
      c • E (fun a => E (fun b => F (a, b)) p.2) p.1
    rw [h2, map_smul]
    rfl

theorem slice2_tmul {X : Type} (E : (X → C) →ₗ[C] (X → C)) (g h : X → C) :
    slice2 E (fun p => g p.1 * h p.2) = fun p => E g p.1 * E h p.2 := by
  funext p
  show E (fun a => E (fun b => g a * h b) p.2) p.1 = E g p.1 * E h p.2
  have h1 : (fun a => E (fun b => g a * h b) p.2) = E h p.2 • g := by
    funext a
    rw [show (fun b => g a * h b) = g a • h from rfl, map_smul]
    simp [mul_comm]
  rw [h1, map_smul]
  simp [mul_comm]

theorem slice2_eq_self {X : Type} (E : (X → C) →ₗ[C] (X → C)) (W : Submodule C (X → C))
    (hE : ∀ f ∈ W, E f = f) (F : X × X → C) (h1 : ∀ a, (fun b => F (a, b)) ∈ W)
    (h2 : ∀ y, (fun a => F (a, y)) ∈ W) : slice2 E F = F := by
  funext p
  show E (fun a => E (fun b => F (a, b)) p.2) p.1 = F p
  have h3 : (fun a => E (fun b => F (a, b)) p.2) = fun a => F (a, p.2) := by
    funext a
    rw [hE _ (h1 a)]
  rw [h3, hE _ (h2 p.2)]

theorem slice2_mem {X : Type} (E : (X → C) →ₗ[C] (X → C)) (M M' : Submodule R (X → C))
    (hM : ∀ f ∈ M, E f ∈ M') {F : X × X → C} (hF : F ∈ tensorSpan R M) :
    slice2 E F ∈ tensorSpan R M' := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨g, hg, h, hh, rfl⟩ := hF
    rw [slice2_tmul]
    exact Submodule.subset_span ⟨E g, hM g hg, E h, hM h hh, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add F G _ _ hF hG => rw [map_add]; exact Submodule.add_mem _ hF hG
  | smul r F _ hF =>
    rw [← algebraMap_smul C r F, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ r hF

theorem apply_eq_sum {X : Type} [Fintype X] [DecidableEq X] (E : (X → C) →ₗ[C] (X → C))
    (f : X → C) (y : X) :
    E f y = ∑ a, f a * E (fun j => if a = j then 1 else 0) y := by
  have hf : f = ∑ a, f a • (fun j => if a = j then (1 : C) else 0) := by
    funext j
    simp [Finset.sum_apply]
  conv_lhs => rw [hf]
  rw [map_sum, Finset.sum_apply]
  simp [map_smul]

end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
end
end

-- bundled from ReciprocityTheory.DualLattices.MulIterateRootEqZero
section
noncomputable section

open WittVector Ideal TensorProduct

namespace ReciprocityTheory.PGsh

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

private lemma frob_bij : Function.Bijective (WittVector.frobenius : WittVector p R → WittVector p R) := by
  constructor
  · intro x y h
    ext n
    have h' := congrArg (fun z => WittVector.coeff z n) h
    simp only [WittVector.coeff_frobenius_charP] at h'
    apply (frobeniusEquiv R p).injective
    rw [_root_.frobeniusEquiv_apply, _root_.frobeniusEquiv_apply, frobenius_def, frobenius_def]
    exact h'
  · intro x
    refine ⟨WittVector.mk p (fun n => (frobeniusEquiv R p).symm (x.coeff n)), ?_⟩
    ext n
    rw [WittVector.coeff_frobenius_charP, WittVector.coeff_mk]
    have h := (frobeniusEquiv R p).apply_symm_apply (x.coeff n)
    rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h

lemma mem_span_p_iff (x : WittVector p R) : x ∈ span {(p : WittVector p R)} ↔ x.coeff 0 = 0 := by
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [← WittVector.verschiebung_frobenius, WittVector.verschiebung_coeff_zero]
  · intro hx
    obtain ⟨y, hy⟩ := (frob_bij (p := p) (R := R)).2 (WittVector.mk p (fun n => x.coeff (n + 1)))
    refine Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩
    rw [← WittVector.verschiebung_frobenius, hy]
    ext n
    cases n with
    | zero => rw [WittVector.verschiebung_coeff_zero, hx]
    | succ n => exact WittVector.verschiebung_coeff_succ _ n

lemma p_mul_eq_zero (x : WittVector p R) (h : x * p = 0) : x = 0 := by
  rw [← WittVector.verschiebung_frobenius] at h
  have h2 : WittVector.frobenius x = 0 := by
    ext n
    have h3 := congrArg (fun z => WittVector.coeff z n.succ) h
    simpa only [WittVector.verschiebung_coeff_succ, WittVector.zero_coeff] using h3
  apply (frob_bij (p := p) (R := R)).1
  rw [h2, map_zero]

lemma p_mem_nonZeroDivisors : (p : WittVector p R) ∈ nonZeroDivisors (WittVector p R) := mem_nonZeroDivisors_iff.mpr
  ⟨fun x hx => p_mul_eq_zero x (by rwa [mul_comm] at hx), fun x hx => p_mul_eq_zero x hx⟩

private lemma mul_root_eq_zero (w y : R) (h : w * y = 0) :
    w * (frobeniusEquiv R p).symm y = 0 := by
  have hr : ((frobeniusEquiv R p).symm y) ^ p = y := by
    have h1 := (frobeniusEquiv R p).apply_symm_apply y
    rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h1
  have hz : (w * (frobeniusEquiv R p).symm y) ^ p = 0 := by
    rw [mul_pow, hr]
    calc w ^ p * y = w ^ (p - 1) * (w * y) := by
          rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.out.pos]
      _ = 0 := by rw [h, mul_zero]
  apply (frobeniusEquiv R p).injective
  rw [map_zero, _root_.frobeniusEquiv_apply, frobenius_def, hz]

private lemma mul_iterate_root_eq_zero (w y : R) (h : w * y = 0) (n : ℕ) :
    w * ((frobeniusEquiv R p).symm^[n]) y = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact mul_root_eq_zero w _ ih

end Witt

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type*} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

lemma pflat_mul_eq_zero (hO : ∀ x : O, (p : O) * x = 0 → x = 0) (pflat : PreTilt O p)
    (hpf : pflat.untilt = (p : O)) (x : PreTilt O p) (hx : pflat * x = 0) : x = 0 := by
  have hu0 : (0 : PreTilt O p).untilt = 0 := by
    have h1 : (0 : PreTilt O p).untilt = (p : O) * (0 : PreTilt O p).untilt := by
      rw [← hpf, ← map_mul, mul_zero]
    have hJ := IsAdicComplete.le_jacobson_bot (span {(p : O)}) (Ideal.mem_span_singleton_self (p : O))
    rw [Ideal.mem_jacobson_bot] at hJ
    have h2 : ((p : O) * -1 + 1) * (0 : PreTilt O p).untilt = 0 := by
      linear_combination h1
    exact ((hJ (-1)).mul_right_eq_zero).mp h2
  have hzero : ∀ y : PreTilt O p, pflat * y = 0 → PreTilt.coeff 0 y = 0 := by
    intro y hy
    have h1 : (p : O) * y.untilt = 0 := by rw [← hpf, ← map_mul, hy, hu0]
    rw [← PreTilt.mk_untilt_eq_coeff_zero, hO _ h1, map_zero]
  have hred : ∀ n : ℕ, pflat * ((frobeniusEquiv (PreTilt O p) p).symm^[n]) x = 0 :=
    mul_iterate_root_eq_zero pflat x hx
  have hli : Function.LeftInverse (frobenius (PreTilt O p) p) (frobeniusEquiv (PreTilt O p) p).symm :=
    fun z => by rw [← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  apply Perfection.ext
  intro n
  have key := Perfection.coeff_iterate_frobenius (R := ModP O p) (p := p)
    ((frobeniusEquiv (PreTilt O p) p).symm^[n] x) 0 n
  rw [zero_add] at key
  erw [hli.iterate n x] at key
  exact key.trans ((hzero _ (hred n)).trans (map_zero (Perfection.coeff (ModP O p) p n)).symm)

end Tilt

section Main

variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem regular (hO : ∀ x : O, (p : O) * x = 0 → x = 0) : RegularStatement p O := by
  intro pflat hpf
  refine ⟨p_mem_nonZeroDivisors, ?_, ?_⟩
  · intro x hx
    rw [mem_span_p_iff] at hx ⊢
    rw [WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero] at hx
    exact pflat_mul_eq_zero hO pflat hpf _ hx
  · intro htop
    have h1 : (1 : WittVector p (PreTilt O p)) ∈
        span {(p : WittVector p (PreTilt O p)), teichmuller p pflat} := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨c, e, hce⟩ := Ideal.mem_span_pair.mp h1
    have h2 := congrArg (fun z => WittVector.coeff z 0) hce
    simp only [WittVector.add_coeff_zero, WittVector.mul_coeff_zero,
      WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h2
    have hp0 : (p : WittVector p (PreTilt O p)).coeff 0 = 0 := by
      rw [← mem_span_p_iff]; exact Ideal.mem_span_singleton_self _
    rw [hp0, mul_zero, zero_add, mul_comm] at h2
    have hu : IsUnit pflat := ⟨⟨pflat, _, h2, by rw [mul_comm]; exact h2⟩, rfl⟩
    have h3 := hu.map (PreTilt.untilt (O := O) (p := p))
    rw [hpf] at h3
    exact (Fact.out : ¬IsUnit (p : O)) h3

end Main

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.SeriesState
section
namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

def PairingPropertiesStatement (B : BX R₀) : Prop :=
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R), N • x = 0 → N • y = 0 → ∃ z, B.IsPairing N x y z) ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z z' : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x y z' → z = z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x x' y : B.G R) (z z' w : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x' y z' → B.IsPairing N (x + x') y w → w = z * z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y y' : B.G R) (z z' w : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x y' z' → B.IsPairing N x (y + y') w → w = z * z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z z' : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N y x z' → z * z' = 1) ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ), B.IsPairing N x y z → z ^ N = 1) ∧
  (∀ (R S : LAlg R₀) (f : LHom R S) (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N (B.map f x) (B.map f y) (Units.map (f.1 : R →* S) z)) ∧
  (∀ (R : LAlg R₀) (N p : ℕ) (x y : B.G R) (z : (R : Type u)ˣ), N • x = 0 → (N * p) • y = 0 →
    B.IsPairing (N * p) x y z → B.IsPairing N x (p • y) z)

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.SubgroupFreenessStatement
section
noncomputable section

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def SubgroupFreenessStatement : Prop :=
  IsAlgClosed C → CharZero C →
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
    (AA : HopfOrder (C := C) R N),
    let B := AA.carrier.comap (pullQ (R := R) K)
    let AK := AA.carrier.map (resK (R := R) K)
    let IK := (augIdeal B).map (pullQ K)
    (∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ g ∈ AA.carrier,
      ∃! b : K → N → C, (∀ j, b j ∈ B.map (pullQ K)) ∧ g = ∑ j, b j * f j) ∧
    (∀ g ∈ AA.carrier, resK (R := R) K g = 0 → g ∈ IK * AA.carrier) ∧
    (∀ c cB cK, HasColen R v AA.carrier c → HasColen R v B cB → HasColen R v AK cK →
      c = cB ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K)) ∧
    (∀ g ∈ augIdeal AA.carrier, resK (R := R) K g ∈ augIdeal AK * augIdeal AK →
      g ∈ IK ⊔ augIdeal AA.carrier * augIdeal AA.carrier)

end ReciprocityTheory.PGsh.L2
end
end

