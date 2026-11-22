import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0002

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatchStep
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private lemma coeff_lin_form {A ι : Type} [CommRing A] [Fintype ι] (a : ι → A) (k₀ : ι) :
    MvPolynomial.coeff (Finsupp.single k₀ 1) (∑ k, MvPolynomial.C (a k) * MvPolynomial.X k : MvPolynomial ι A) = a k₀ := by
  classical
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  rw [Finset.sum_eq_single k₀]
  · simp
  · intro k _ hk
    rw [MvPolynomial.coeff_X', if_neg, mul_zero]
    intro h
    exact hk (Finsupp.single_left_injective one_ne_zero h)
  · simp

theorem UpperTheory.Gal.crystallineComparison.matchStep_of :
    GaussLin → SameNormBasic → LinFactor → MatchStep := by
  intro hG hS hL B _ ϖ hϖ hnu ι _ N m hm u u' hcard hsame x hx hchain hdich
  by_contra hcon
  push_neg at hcon
  have hex : ∀ y : ι → B, ∃ c : B, ∃ e : ι → B,
      y ∈ u' → c ∣ ϖ ^ m ∧ (∃ k₀, e k₀ = 1) ∧ ∀ k, x k - y k = c * e k := by
    intro y
    by_cases hy : y ∈ u'
    · obtain ⟨k, hk⟩ := hcon y hy
      have hdk : x k - y k ∣ ϖ ^ m := (hdich y hy k).resolve_right hk
      obtain ⟨c, e, k₀, hc, he, hd⟩ := hL B ι (ϖ ^ m) (fun k => x k - y k) ⟨k, hdk⟩ (hchain y hy)
      exact ⟨c, e, fun _ => ⟨hc, ⟨k₀, he⟩, hd⟩⟩
    · exact ⟨0, 0, fun h => absurd h hy⟩
  choose c e hce using hex
  set M := ϖ ^ (m * (N + 1)) with hM
  have h4 := (hS (B ⧸ Ideal.span {M}) ι).2.2.2 (fun k => Ideal.Quotient.mk (Ideal.span {M}) (x k))
    (redMod M u) (redMod M u') hsame (Multiset.mem_map_of_mem _ hx)
  let L : (ι → B) → MvPolynomial ι (B ⧸ Ideal.span {M}) :=
    fun y => ∑ k, MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {M}) (e y k)) * MvPolynomial.X k
  have h4' : (u'.map (fun y => MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {M}) (c y)) * L y)).prod = 0 := by
    rw [← h4]
    congr 1
    unfold redMod
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun y hy => ?_
    simp only [Function.comp, L, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_sub, (hce y hy).2.2 k, map_mul, map_mul, mul_assoc]
  rw [Multiset.prod_map_mul] at h4'
  have hC : (u'.map fun y => (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {M}) (c y)) :
        MvPolynomial ι (B ⧸ Ideal.span {M}))).prod =
      (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {M}) (u'.map c).prod) :
        MvPolynomial ι (B ⧸ Ideal.span {M})) := by
    rw [map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
    rfl
  rw [hC] at h4'
  have hz : Ideal.Quotient.mk (Ideal.span {M}) (u'.map c).prod = 0 := by
    refine hG _ ι _ (u'.map L) ?_ h4'
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨k₀, hk₀⟩ := (hce y hy).2.1
    exact ⟨Finsupp.single k₀ 1, by simp only [L]; rw [coeff_lin_form, hk₀, map_one]⟩
  have hdvd : M ∣ (u'.map c).prod :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hdvd2 : (u'.map c).prod ∣ (ϖ ^ m) ^ Multiset.card u' := by
    have hh := Multiset.prod_dvd_prod_of_dvd (S := u') c (fun _ => ϖ ^ m) (fun y hy => (hce y hy).1)
    simpa [Multiset.map_const', Multiset.prod_replicate] using hh
  obtain ⟨t, ht⟩ := hdvd.trans hdvd2
  have hr : M = (ϖ ^ m) ^ Multiset.card u' * ϖ ^ (m * (N + 1 - Multiset.card u')) := by
    rw [hM, ← pow_mul, ← pow_add, ← Nat.mul_add]
    congr 2
    omega
  rw [hr, mul_assoc] at ht
  have hpa : (ϖ ^ m) ^ Multiset.card u' ∈ nonZeroDivisors B := pow_mem (pow_mem hϖ m) _
  have h0 : (ϖ ^ (m * (N + 1 - Multiset.card u')) * t - 1) * (ϖ ^ m) ^ Multiset.card u' = 0 := by
    linear_combination -ht
  have h1 : ϖ ^ (m * (N + 1 - Multiset.card u')) * t = 1 :=
    sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hpa).2 _ h0)
  have hu : IsUnit (ϖ ^ (m * (N + 1 - Multiset.card u'))) := isUnit_iff_exists_inv.mpr ⟨t, h1⟩
  exact hnu ((isUnit_pow_iff (Nat.mul_ne_zero (by omega) (by omega))).mp hu)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatching
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem descend (hS : SameNormBasic) {B ι : Type} [CommRing B] [Fintype ι] {a b : B} (hab : a ∣ b)
    {u u' : Multiset (ι → B)} (h : SameNorm (redMod b u) (redMod b u')) :
    SameNorm (redMod a u) (redMod a u') := by
  have hle : Ideal.span {b} ≤ Ideal.span {a} := Ideal.span_singleton_le_span_singleton.2 hab
  have := (hS (B ⧸ Ideal.span {b}) ι).1 (B ⧸ Ideal.span {a}) (Ideal.Quotient.factor hle) _ _ h
  simpa only [redMod, Multiset.map_map, Function.comp_def, Ideal.Quotient.factor_mk] using this

private theorem red_cons {B ι : Type} [CommRing B] (a : B) (x : ι → B) (u : Multiset (ι → B)) :
    redMod a (x ::ₘ u) = (fun k => Ideal.Quotient.mk (Ideal.span {a}) (x k)) ::ₘ redMod a u := by
  simp [redMod]

private theorem red_eq {B ι : Type} [CommRing B] {a : B} {x y : ι → B} (h : ∀ k, a ∣ x k - y k) :
    (fun k => Ideal.Quotient.mk (Ideal.span {a}) (x k)) = fun k => Ideal.Quotient.mk (Ideal.span {a}) (y k) := by
  funext k
  exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (h k))

private theorem main (hS : SameNormBasic) (hM : MatchStep) {B : Type} [CommRing B] (ϖ : B)
    (h0 : ϖ ∈ nonZeroDivisors B) (h1 : ¬ IsUnit ϖ) {ι : Type} [Fintype ι] (N : ℕ) :
    ∀ c, c ≤ N → ∀ (u u' : Multiset (ι → B)), u.card = c → u'.card ≤ N →
    (∀ x ∈ u, ∀ y ∈ u', ∀ k k', x k - y k ∣ ϖ ^ (N + 1) ^ N → x k - y k ∣ x k' - y k' ∨ x k' - y k' ∣ x k - y k) →
    (∀ x ∈ u, ∀ y ∈ u', ∀ k, ∀ j ≤ N, x k - y k ∣ ϖ ^ (N + 1) ^ j ∨ ϖ ^ (N + 1) ^ j ∣ x k - y k) →
    SameNorm (redMod (ϖ ^ (N + 1) ^ c) u) (redMod (ϖ ^ (N + 1) ^ c) u') →
    redMod ϖ u = redMod ϖ u' := by
  have hnu : ∀ j : ℕ, j ≠ 0 → ¬ IsUnit (ϖ ^ j) := fun j hj h => h1 ((isUnit_pow_iff hj).mp h)
  intro c
  induction c with
  | zero =>
    intro _ u u' hu _ _ _ hsn
    have hu0 : u = 0 := Multiset.card_eq_zero.mp hu
    subst hu0
    haveI : Nontrivial (B ⧸ Ideal.span {ϖ ^ (N + 1) ^ 0}) := by
      refine nontrivial_of_ne 1 0 ?_
      intro h
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {ϖ ^ (N + 1) ^ 0})),
        Ideal.Quotient.eq_zero_iff_mem, ← Ideal.eq_top_iff_one, Ideal.span_singleton_eq_top] at h
      exact hnu _ (by positivity) h
    have hc := (hS _ ι).2.2.1 inferInstance _ _ hsn
    have hu'0 : u' = 0 := by
      simp only [redMod, Multiset.card_map, Multiset.card_zero, Multiset.map_zero] at hc
      exact Multiset.card_eq_zero.mp hc.symm
    subst hu'0
    rfl
  | succ c ih =>
    intro hc u u' hu hu' hdiv hcmp hsn
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp (by rw [hu]; exact Nat.succ_pos c)
    obtain ⟨u0, rfl⟩ := Multiset.exists_cons_of_mem hx
    have hxm : x ∈ x ::ₘ u0 := Multiset.mem_cons.mpr (Or.inl rfl)
    have hm : 0 < (N + 1) ^ c := by positivity
    have hle : (N + 1) ^ c ≤ (N + 1) ^ N := Nat.pow_le_pow_right (Nat.succ_pos N) (by omega)
    have hsn' : SameNorm (redMod (ϖ ^ ((N + 1) ^ c * (N + 1))) (x ::ₘ u0))
        (redMod (ϖ ^ ((N + 1) ^ c * (N + 1))) u') := by
      rw [← pow_succ]; exact hsn
    obtain ⟨y, hy, hxy⟩ := hM B ϖ h0 h1 ι N ((N + 1) ^ c) hm (x ::ₘ u0) u' hu' hsn' x hxm
      (fun y hy k k' h => hdiv x hxm y hy k k' (h.trans (pow_dvd_pow ϖ hle)))
      (fun y hy k => hcmp x hxm y hy k c (by omega))
    obtain ⟨u0', rfl⟩ := Multiset.exists_cons_of_mem hy
    have hsn2 : SameNorm (redMod (ϖ ^ (N + 1) ^ c) (x ::ₘ u0)) (redMod (ϖ ^ (N + 1) ^ c) (y ::ₘ u0')) :=
      descend hS (pow_dvd_pow ϖ (Nat.pow_le_pow_right (Nat.succ_pos N) (Nat.le_succ c))) hsn
    rw [red_cons, red_cons, red_eq hxy] at hsn2
    have hsn3 := (hS _ ι).2.1 _ _ _ hsn2
    have ih' := ih (by omega) u0 u0' (by simpa using hu) (by simp at hu'; omega)
      (fun a ha b hb => hdiv a (Multiset.mem_cons_of_mem ha) b (Multiset.mem_cons_of_mem hb))
      (fun a ha b hb => hcmp a (Multiset.mem_cons_of_mem ha) b (Multiset.mem_cons_of_mem hb)) hsn3
    rw [red_cons, red_cons, ih', red_eq (fun k => (dvd_pow_self ϖ hm.ne').trans (hxy k))]

theorem UpperTheory.Gal.crystallineComparison.matching_of :
    SameNormBasic → MatchStep → Matching := by
  intro hS hM B _ ϖ h0 h1 ι _ N u u' hu hu' hsn hdiv hcmp
  apply main hS hM ϖ h0 h1 N u.card hu u u' rfl hu' hdiv hcmp
  exact descend hS (pow_dvd_pow _ (Nat.pow_le_pow_right (Nat.succ_pos N) hu)) hsn
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilAnn
section
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section
variable {F B : Type} [Field F] [AddCommGroup B] [Module F B]
  {L : Type} [Field L] [Algebra F L] {V : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]

private abbrev Phi (a : End L V) (b : End F B) : End L (V ⊗[F] B) := AlgebraTensorModule.map a b

end

private theorem commute_tensorMap_of_commute {F B L V : Type} [Field F] [AddCommGroup B] [Module F B] [Field L]
    [Algebra F L] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {f₁ f₂ : Module.End L V} {g₁ g₂ : Module.End F B} (hf : Commute f₁ f₂) (hg : Commute g₁ g₂) :
    Commute (AlgebraTensorModule.map f₁ g₁ : Module.End L (V ⊗[F] B)) (AlgebraTensorModule.map f₂ g₂) := by
  unfold Commute SemiconjBy
  rw [← AlgebraTensorModule.map_mul, ← AlgebraTensorModule.map_mul, hf.eq, hg.eq]

private theorem tensorMap_pow {F B L V : Type} [Field F] [AddCommGroup B] [Module F B] [Field L]
    [Algebra F L] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    (f : Module.End L V) (g : Module.End F B) (k : ℕ) :
    (AlgebraTensorModule.map f g : Module.End L (V ⊗[F] B)) ^ k = AlgebraTensorModule.map (f ^ k) (g ^ k) := by
  induction k with
  | zero => simp only [pow_zero, AlgebraTensorModule.map_one]
  | succ k ih =>
    rw [pow_succ, ih, ← AlgebraTensorModule.map_mul, ← pow_succ, ← pow_succ]

private theorem isNilpotent_tensorMap_of_isNilpotent {F B L V : Type} [Field F] [AddCommGroup B] [Module F B] [Field L]
    [Algebra F L] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {f : Module.End L V} (g : Module.End F B) (hf : IsNilpotent f) :
    IsNilpotent (AlgebraTensorModule.map f g : Module.End L (V ⊗[F] B)) := by
  have h : (AlgebraTensorModule.map f g : Module.End L (V ⊗[F] B)) =
      AlgebraTensorModule.map f 1 * AlgebraTensorModule.map 1 g := by
    rw [← AlgebraTensorModule.map_mul, mul_one, one_mul]
  rw [h]
  apply Commute.isNilpotent_mul_right (commute_tensorMap_of_commute (Commute.one_right f) (Commute.one_left g))
  obtain ⟨k, hk⟩ := hf
  refine ⟨k, ?_⟩
  rw [tensorMap_pow, hk, one_pow]
  apply TensorProduct.AlgebraTensorModule.ext
  intro v b
  simp

theorem UpperTheory.Gal.crystallineComparison.nilAnn_of :
    NilOfAnn := by
  intro F G B _ _ _ _ σ ψ hσψ L _ _ V _ _ _ _ ρ q n T θ hTρ hTT hnil hann
  let c : ℕ → ℤ := fun j => (-1) ^ j * (q : ℤ) ^ j.choose 2
  let P : Module.End L (V ⊗[F] B) :=
    ∑ j ∈ Finset.range (n + 1), c j • AlgebraTensorModule.map (T j) (ψ ^ (n - j))
  let E : Module.End L (V ⊗[F] B) :=
    ∑ j ∈ Finset.range (n + 1), c j • AlgebraTensorModule.map (T j - θ j • 1) (ψ ^ (n - j))
  have hQ : Polynomial.aeval (onPer ψ L V) (heckePol q n θ) = P - E := by
    rw [← Finset.sum_sub_distrib]
    simp only [heckePol, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    apply TensorProduct.AlgebraTensorModule.ext
    intro v b
    simp only [onPer, tensorMap_pow, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      Module.End.mul_apply, Module.algebraMap_end_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      AlgebraTensorModule.map_tmul, ← smul_sub, ← sub_tmul]
    simp [c, smul_tmul', sub_sub_cancel, smul_smul]
    rw [← Int.cast_smul_eq_zsmul L, smul_smul]
    congr 2
    push_cast
    ring
  have hP : ∀ x ∈ Dinv σ ρ, P x = 0 := by
    intro x hx
    simp only [P, LinearMap.sum_apply, LinearMap.smul_apply]
    exact hann x hx
  have hM : ∀ i j : ℕ, ∀ f : Module.End L V, Commute (T i) f →
      Commute (c i • AlgebraTensorModule.map (T i) (ψ ^ (n - i)) : Module.End L (V ⊗[F] B))
        (c j • AlgebraTensorModule.map f (ψ ^ (n - j))) := by
    intro i j f hf
    have h0 : Commute (AlgebraTensorModule.map (T i) (ψ ^ (n - i)) : Module.End L (V ⊗[F] B))
        (AlgebraTensorModule.map f (ψ ^ (n - j))) :=
      commute_tensorMap_of_commute hf (Commute.pow_pow_self ψ _ _)
    exact (h0.smul_left (c i)).smul_right (c j)
  have hPE : Commute P E := by
    refine Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
    exact hM i j _ ((hTT i j).sub_right ((Commute.one_right (T i)).smul_right (θ j)))
  have hE : IsNilpotent E := by
    refine Commute.isNilpotent_sum (fun j hj => (isNilpotent_tensorMap_of_isNilpotent _ (hnil j ?_)).smul (c j)) ?_
    · exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    · intro i j _ _
      have hf : Commute (T i - θ i • 1) (T j - θ j • 1) := by
        refine ((hTT i j).sub_right ((Commute.one_right (T i)).smul_right (θ j))).sub_left ?_
        exact ((Commute.one_left (T j)).smul_left (θ i)).sub_right
          (((Commute.one_right _).smul_left (θ i)).smul_right (θ j))
      have h0 : Commute (AlgebraTensorModule.map (T i - θ i • 1) (ψ ^ (n - i)) : Module.End L (V ⊗[F] B))
          (AlgebraTensorModule.map (T j - θ j • 1) (ψ ^ (n - j))) :=
        commute_tensorMap_of_commute hf (Commute.pow_pow_self ψ _ _)
      exact (h0.smul_left (c i)).smul_right (c j)
  obtain ⟨N, hN⟩ := hE
  refine ⟨N, fun x hx => ?_⟩
  have key : ∀ (k : ℕ) (y : V ⊗[F] B), P y = 0 → ((P - E) ^ k) y = ((-E) ^ k) y := by
    intro k
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      have h1 : (P - E) y = (-E) y := by simp [hy]
      rw [h1]
      apply ih
      rw [← Module.End.mul_apply, hPE.neg_right.eq, Module.End.mul_apply, hy, map_zero]
  rw [hQ, key N x (hP x hx), neg_pow, hN]
  simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilEmb
section
noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

section Comm
variable {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]

private theorem pow_comm (φ : M →ₗ[L] N) (A : End L M) (A' : End L N) (h : ∀ y, φ (A y) = A' (φ y)) (n : ℕ) (y : M) :
    φ ((A ^ n) y) = (A' ^ n) (φ y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem aeval_comm (φ : M →ₗ[L] N) (A : End L M) (A' : End L N) (h : ∀ y, φ (A y) = A' (φ y)) (Q : Polynomial L) (y : M) :
    φ (Polynomial.aeval A Q y) = Polynomial.aeval A' Q (φ y) :=
  _root_.UpperTheory.Reformulated.B.Qk66.aeval_comm φ A A' h Q y

end Comm

section
variable {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B)
  {L : Type} [Field L] [Algebra F L] {V W : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
  [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W]

private def ext1 (B : Type) [AddCommGroup B] [Module F B] (f : V →ₗ[L] W) : V ⊗[F] B →ₗ[L] W ⊗[F] B :=
  AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B)

private theorem scalar_extension_tmul (f : V →ₗ[L] W) (v : V) (b : B) : ext1 (F := F) B f (v ⊗ₜ b) = f v ⊗ₜ b := by
  simp [ext1]

private theorem typeCharacterExtension_mem_range_coefficientRing {ρ : Representation L G V} {ρ' : Representation L G W} {f : V →ₗ[L] W} (h : Inter ρ ρ' f)
    {x : V ⊗[F] B} (hx : x ∈ Dinv σ ρ) : ext1 B f x ∈ Dinv σ ρ' := by
  rw [mem_Dinv] at hx ⊢
  intro g
  have key : ∀ y : V ⊗[F] B, AlgebraTensorModule.map (ρ' g) (σ g) (ext1 B f y) =
      ext1 B f (AlgebraTensorModule.map (ρ g) (σ g) y) := by
    intro y
    induction y with
    | zero => simp
    | tmul v b => simp [scalar_extension_tmul, h g v]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [key, hx]

private theorem scalar_extension_period_action (f : V →ₗ[L] W) (y : V ⊗[F] B) :
    ext1 B f (onPer ψ L V y) = onPer ψ L W (ext1 B f y) := by
  induction y with
  | zero => simp
  | tmul v b => simp [scalar_extension_tmul, onPer]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem scalar_extension_basis_coord {κ : Type} [DecidableEq κ] (b : Basis κ F B) (f : V →ₗ[L] W) (y : V ⊗[F] B) (k : κ) :
    TensorProduct.equivFinsuppOfBasisRight b (ext1 B f y) k = f (TensorProduct.equivFinsuppOfBasisRight b y k) := by
  induction y with
  | zero => simp
  | tmul v c =>
    rw [scalar_extension_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, LinearMap.map_smul_of_tower]
  | add a c ha hc => simp only [map_add, Finsupp.add_apply, ha, hc]

end

theorem nilEmb_of : NilEmb := by
  intro F G B _ _ _ _ σ ψ L _ _ V _ _ _ _ ρ I _ W _ _ _ _ ρ' f hI hinj Q hQ
  classical
  cases nonempty_fintype I
  choose N hN using hQ
  refine ⟨∑ i, N i, fun x hx => ?_⟩
  set A := Polynomial.aeval (onPer ψ L V) Q with hA
  have hzero : ∀ i, ext1 B (f i) ((A ^ ∑ i, N i) x) = 0 := by
    intro i
    have hle : N i ≤ ∑ i, N i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [pow_comm (ext1 B (f i)) A (Polynomial.aeval (onPer ψ L (W i)) Q)
      (aeval_comm _ _ _ (scalar_extension_period_action ψ (f i)) Q), ← Nat.sub_add_cancel hle, pow_add, Module.End.mul_apply,
      hN i _ (typeCharacterExtension_mem_range_coefficientRing σ (hI i) hx), map_zero]
  apply (TensorProduct.equivFinsuppOfBasisRight (Basis.ofVectorSpace F B)).injective
  ext k
  rw [map_zero, Finsupp.zero_apply]
  refine hinj _ fun i => ?_
  rw [← scalar_extension_basis_coord, hzero i, map_zero, Finsupp.zero_apply]

end UpperTheory.Gal.crystallineComparison
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilSubq
section
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem pow_inter {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    (c : M →ₗ[L] N) (f : End L M) (g : End L N) (h : ∀ x, c (f x) = g (c x)) (n : ℕ) (x : M) :
    c ((f ^ n) x) = (g ^ n) (c x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem aeval_inter {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    (c : M →ₗ[L] N) (f : End L M) (g : End L N) (h : ∀ x, c (f x) = g (c x)) (Q : Polynomial L) (x : M) :
    c (Polynomial.aeval f Q x) = Polynomial.aeval g Q (c x) :=
  _root_.UpperTheory.Reformulated.B.Qi58.aeval_inter c f g h Q x

theorem UpperTheory.Gal.crystallineComparison.nilSubq_of :
    AdmExact → NilEmb → NilSubq := by
  intro hA hE F G B _ _ _ _ σ ψ L _ _ e hB V W _ _ _ _ _ _ _ _ _ ρ ρ' hS hAdm
  obtain ⟨U, _, _, ρU, i, p, hi, hinj, hp, hsurj⟩ := hS
  letI : Module F U := Module.compHom U (algebraMap F L)
  haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite L U := Module.Finite.of_injective i hinj
  haveI : Module.Finite L W := Module.Finite.of_surjective p hsurj
  have hU : admitted σ e ρU := (hA F G B σ L e hB U V ρU ρ i hi).1 hinj hAdm
  obtain ⟨hW, hmap⟩ := (hA F G B σ L e hB U W ρU ρ' p hp).2 hsurj hU
  refine ⟨hW, fun Q hQ => ?_⟩
  obtain ⟨N, hN⟩ : NilD σ ψ ρU Q :=
    hE F G B σ ψ L U ρU Unit (fun _ => V) (fun _ => ρ) (fun _ => i) (fun _ => hi)
      (fun v h => hinj (by simpa using h ())) Q (fun _ => hQ)
  refine ⟨N, fun y hy => ?_⟩
  rw [← hmap] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have h1 : ∀ z : U ⊗[F] B, AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) (onPer ψ L U z) =
      onPer ψ L W (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul u b => simp [onPer]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [← pow_inter _ _ _ (fun z => aeval_inter _ _ _ h1 Q z) N x, hN x hx, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNormEx
section
noncomputable section

namespace UpperTheory.Gal.crystallineComparison

theorem normEx_of : MatRep → DetSplit → NormEx := by
  intro hMR hDS R S _ _ _ _ _ ι _ s
  obtain ⟨m, M, hM⟩ := hMR R S
  let φ : R →+* Polynomial (MvPolynomial ι R) := Polynomial.C.comp MvPolynomial.C
  refine ⟨(1 - (M 1).map φ + (Polynomial.X : Polynomial (MvPolynomial ι R)) • (M 1).map φ
    - ∑ k, (Polynomial.C (MvPolynomial.X (R := R) k) : Polynomial (MvPolynomial ι R)) • (M (s k)).map φ).det, ?_⟩
  intro B _ _ I _ z hz
  classical
  obtain ⟨P, Q, hPQ, hQ⟩ := hM B I z hz
  let ψ : B →+* Polynomial (MvPolynomial ι B) := Polynomial.C.comp MvPolynomial.C
  let F : Polynomial (MvPolynomial ι R) →+* Polynomial (MvPolynomial ι B) :=
    Polynomial.mapRingHom (MvPolynomial.map (algebraMap R B))
  have hPQ' : P.map ψ * Q.map ψ = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one ψ (map_zero _) (map_one _)]
  have key := hDS (Polynomial (MvPolynomial ι B)) m I (P.map ψ) (Q.map ψ) hPQ'
    (fun i => form fun k => z i (s k))
  rw [← key]
  have hmap : ∀ t : S, ((M t).map φ).map F = Q.map ψ * (Matrix.diagonal fun i => z i t).map ψ * P.map ψ := by
    intro t
    have : ((M t).map φ).map F = ((M t).map (algebraMap R B)).map ψ := by
      rw [Matrix.map_map, Matrix.map_map]
      congr 1
      funext r
      simp [φ, ψ, F]
    rw [this, hQ t, Matrix.map_mul, Matrix.map_mul]
  have hd : Matrix.diagonal (fun i => form fun k => z i (s k))
      = (Polynomial.X : Polynomial (MvPolynomial ι B)) • (1 : Matrix I I _)
        - ∑ k, (Polynomial.C (MvPolynomial.X (R := B) k) : Polynomial (MvPolynomial ι B))
          • (Matrix.diagonal fun i => z i (s k)).map ψ := by
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · subst h
      simp [form, ψ, map_sum, mul_comm]
    · simp
  have hs : ∀ (c : Polynomial (MvPolynomial ι R)) (A : Matrix (Fin m) (Fin m) (Polynomial (MvPolynomial ι R))),
      F.mapMatrix (c • A) = F c • F.mapMatrix A := by
    intro c A
    ext i j
    simp
  have h1 : (Matrix.diagonal fun i => z i 1).map ψ = 1 := by
    simp
  change F _ = _
  rw [RingHom.map_det]
  congr 1
  rw [map_sub, map_add, map_sub, map_one, map_sum]
  simp only [hs, RingHom.mapMatrix_apply, hmap, h1, Matrix.mul_one]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_sum,
    Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  simp [F]
  abel

end UpperTheory.Gal.crystallineComparison
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPermMap
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.permMap_of :
    PermOfMap := by
  classical
  intro I I' P _ _ f g h
  have hc : ∀ p : P, Fintype.card {i // f i = p} = Fintype.card {j // g j = p} := by
    intro p
    have hp := congrArg (Multiset.count p) h
    simp only [Multiset.count_map] at hp
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card_def, Finset.filter_val, eq_comm] using hp
  let e : ∀ p, {i // f i = p} ≃ {j // g j = p} := fun p => Fintype.equivOfCardEq (hc p)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  intro i
  show f i = g ((e (f i)) ⟨i, rfl⟩).1
  exact ((e (f i)) ⟨i, rfl⟩).2.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtOrd
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ptOrd_of :
    OrdCount → PtIdOfOrd := by
  intro hC l q n Y π T hO V _ _ _ _ hl y hy φ hφ I _ z hz
  apply hC
  obtain ⟨k, H, x, hk, x2, x3, hf, C, A, e, h1, h2, h3, h4⟩ := hO V hl y hy φ hφ
  exact ⟨k, H, x, hk, x2, x3, hf, C, A, fun j => (Equiv.ofBijective (z j) (hz j)).trans (e j),
    h1, h2, h3, fun j i => h4 j (z j i)⟩
end

