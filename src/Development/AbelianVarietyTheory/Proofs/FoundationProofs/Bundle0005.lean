import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormForm
section
open Polynomial

namespace GlobalTheory.NormFormBound

theorem prod_pow_bound {k σ : Type} [Field k] (s : Finset σ) (m : σ → ℕ) (p : σ → k[X]) (d : ℕ)
    (hp : ∀ i, (p i).natDegree ≤ d) :
    (∏ i ∈ s, p i ^ m i).natDegree ≤ (∑ i ∈ s, m i) * d ∧
      (∏ i ∈ s, p i ^ m i).coeff ((∑ i ∈ s, m i) * d) = ∏ i ∈ s, (p i).coeff d ^ m i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, add_mul]
    have hpa : (p a ^ m a).natDegree ≤ m a * d :=
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hp a))
    refine ⟨natDegree_mul_le.trans (add_le_add hpa ih1), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hpa ih1, coeff_pow_of_natDegree_le (hp a), ih2, Finset.prod_insert ha]

theorem form_bound {k σ : Type} [Field k] [Infinite k] [Fintype σ] (n : ℕ)
    (F : MvPolynomial σ k[X]) (hF : F.IsHomogeneous n) (h0 : F ≠ 0) :
    ∃ (c : ℕ) (lam : σ → k),
      (∀ (d : ℕ) (p : σ → k[X]), (∀ i, (p i).natDegree ≤ d) →
        (MvPolynomial.eval p F).natDegree ≤ n * d + c) ∧
      ∀ (d : ℕ) (p : σ → k[X]), (∀ i, (p i).natDegree ≤ d) → (∀ i, (p i).coeff d = lam i) →
        (MvPolynomial.eval p F).coeff (n * d + c) ≠ 0 := by
  classical
  set c := F.support.sup (fun m => (F.coeff m).natDegree) with hc
  set G : MvPolynomial σ k := ∑ m ∈ F.support, MvPolynomial.monomial m ((F.coeff m).coeff c) with hG
  have hsumdeg : ∀ m ∈ F.support, ∑ i ∈ m.support, m i = n := by
    intro m hm
    have h := hF (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  have hcle : ∀ m ∈ F.support, (F.coeff m).natDegree ≤ c := fun m hm =>
    Finset.le_sup (f := fun m => (F.coeff m).natDegree) hm
  have hG0 : G ≠ 0 := by
    have hne : F.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
    obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image F.support (fun m => (F.coeff m).natDegree) hne
    have hcm : c = (F.coeff m0).natDegree :=
      le_antisymm (Finset.sup_le fun m hm => hmax m hm) (hcle m0 hm0)
    intro hG'
    have h1 := congrArg (MvPolynomial.coeff m0) hG'
    rw [hG, MvPolynomial.coeff_sum, Finset.sum_eq_single m0] at h1
    · rw [MvPolynomial.coeff_monomial, if_pos rfl, hcm, MvPolynomial.coeff_zero] at h1
      exact (MvPolynomial.mem_support_iff.mp hm0) (Polynomial.leadingCoeff_eq_zero.mp h1)
    · intro m _ hm
      rw [MvPolynomial.coeff_monomial, if_neg hm]
    · intro h
      exact absurd hm0 h
  obtain ⟨lam, hlam⟩ : ∃ lam : σ → k, MvPolynomial.eval lam G ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hG0 (MvPolynomial.funext fun x => by simpa using hall x)
  refine ⟨c, lam, ?_, ?_⟩
  · intro d p hp
    rw [MvPolynomial.eval_eq]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    have hdeg := (prod_pow_bound m.support m p d hp).1
    rw [hsumdeg m hm] at hdeg
    refine natDegree_mul_le.trans ?_
    have := hcle m hm
    omega
  · intro d p hp hpl
    rw [MvPolynomial.eval_eq, Polynomial.finset_sum_coeff]
    have hterm : ∀ m ∈ F.support, (F.coeff m * ∏ i ∈ m.support, p i ^ m i).coeff (n * d + c) =
        (F.coeff m).coeff c * ∏ i ∈ m.support, lam i ^ m i := by
      intro m hm
      have hb := prod_pow_bound m.support m p d hp
      rw [hsumdeg m hm] at hb
      rw [add_comm (n * d) c, coeff_mul_add_eq_of_natDegree_le (hcle m hm) hb.1, hb.2]
      simp [hpl]
    rw [Finset.sum_congr rfl hterm]
    have hev : MvPolynomial.eval lam G =
        ∑ m ∈ F.support, (F.coeff m).coeff c * ∏ i ∈ m.support, lam i ^ m i := by
      rw [hG, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.eval_monomial, Finsupp.prod]
    rw [← hev]
    exact hlam

theorem exists_norm_form {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
    (b : Module.Basis (Fin n) R A) :
    ∃ F : MvPolynomial (Fin n) R, F.IsHomogeneous n ∧
      ∀ p : Fin n → R, MvPolynomial.eval p F = Algebra.norm R (∑ i, p i • b i) := by
  classical
  refine ⟨(Matrix.of fun a c => ∑ i, MvPolynomial.C (Algebra.leftMulMatrix b (b i) a c) *
      MvPolynomial.X i).det, ?_, ?_⟩
  · rw [Matrix.det_apply]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    have hC : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n) R) =
        MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
    rw [hC]
    have hent : ∀ a ∈ (Finset.univ : Finset (Fin n)), ((Matrix.of fun a c => ∑ i,
        MvPolynomial.C (Algebra.leftMulMatrix b (b i) a c) * MvPolynomial.X i) (σ a) a).IsHomogeneous 1 := by
      intro a _
      rw [Matrix.of_apply]
      refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) (Algebra.leftMulMatrix b (b i) (σ a) a)).mul
        (MvPolynomial.isHomogeneous_X R i)
    have hmul := (MvPolynomial.isHomogeneous_C (Fin n) ((Equiv.Perm.sign σ : ℤ) : R)).mul
      (MvPolynomial.IsHomogeneous.prod _ _ (fun _ => 1) hent)
    simpa using hmul
  · intro p
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext a c
    simp [map_sum, Matrix.sum_apply, mul_comm]

theorem norm_degree (k A : Type) [Field k] [Infinite k] [CommRing A] [IsDomain A]
    [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) :
    ∃ (c : ℕ) (lam : Fin n → k),
      (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).natDegree ≤ d) →
        (Algebra.norm k[X] (∑ i, p i • b i)).natDegree ≤ n * d + c) ∧
      ∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).degree < (d : WithBot ℕ)) →
        ∑ i, (C (lam i) * X ^ d + p i) • b i ≠ 0 ∧
          (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).natDegree = n * d + c := by
  classical
  haveI : Module.Free k[X] A := Module.Free.of_basis b
  haveI : Module.Finite k[X] A := Module.Finite.of_basis b
  obtain ⟨F, hFh, hFev⟩ := exists_norm_form n b
  have hF0 : F ≠ 0 := by
    intro hF
    have h1 := hFev (fun i => b.repr 1 i)
    rw [hF, map_zero, b.sum_repr 1, map_one] at h1
    exact one_ne_zero h1.symm
  obtain ⟨c, lam, hb1, hb2⟩ := form_bound n F hFh hF0
  refine ⟨c, lam, fun d p hp => ?_, fun d p hp => ?_⟩
  · rw [← hFev]
    exact hb1 d p hp
  · have hq1 : ∀ i, (C (lam i) * X ^ d + p i).natDegree ≤ d := fun i =>
      (natDegree_add_le _ _).trans
        (max_le (natDegree_C_mul_X_pow_le _ _) (natDegree_le_of_degree_le (hp i).le))
    have hq2 : ∀ i, (C (lam i) * X ^ d + p i).coeff d = lam i := fun i => by
      rw [coeff_add, coeff_C_mul_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt (hp i), add_zero]
    have hN : (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).coeff (n * d + c) ≠ 0 := by
      rw [← hFev]
      exact hb2 d (fun i => C (lam i) * X ^ d + p i) hq1 hq2
    refine ⟨fun h0 => hN (by rw [h0, Algebra.norm_zero, coeff_zero]), ?_⟩
    apply le_antisymm
    · rw [← hFev]
      exact hb1 d (fun i => C (lam i) * X ^ d + p i) hq1
    · exact le_natDegree_of_ne_zero hN

end GlobalTheory.NormFormBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
section
noncomputable section

namespace GlobalTheory

open TensorProduct

theorem isPrecomplete_of_finite {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t with
  | zero => exact ⟨0, by simp⟩
  | tmul a m =>
    obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective I R a
    refine ⟨r • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, show AdicCompletion.of I R r =
      algebraMap R (AdicCompletion I R) r by simp [AdicCompletion.algebraMap_apply],
      algebraMap_smul, map_smul]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simp [hu, hv]⟩

theorem isAdicComplete_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M where
  toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  toIsPrecomplete := isPrecomplete_of_finite I M

theorem isAdicComplete_map_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (I.map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff]
  exact isAdicComplete_of_finite I S

section Tower

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem existsUnique_of_compatible_tower {M : Type*} [AddCommGroup M] [Module R M]
    [IsAdicComplete I M] {C : ℕ → Type*} (π : ∀ n, M → C n)
    (hπ : ∀ n, Function.Surjective (π n))
    (hker : ∀ n x y, π n x = π n y ↔ x - y ∈ (I ^ n • ⊤ : Submodule R M))
    (t : ∀ n, C (n + 1) → C n) (ht : ∀ n x, t n (π (n + 1) x) = π n x)
    (c : ∀ n, C n) (hc : ∀ n, t n (c (n + 1)) = c n) : ∃! x : M, ∀ n, π n x = c n := by
  choose x hx using fun n ↦ hπ n (c n)
  have hcauchy : ∀ {m n}, m ≤ n → x m ≡ x n [SMOD (I ^ m • ⊤ : Submodule R M)] := by
    refine (AdicCompletion.isAdicCauchy_iff I M x).2 fun n ↦ ?_
    rw [SModEq.sub_mem, ← hker, hx, ← ht, hx, hc]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) x hcauchy
  have hLc : ∀ n, π n L = c n := fun n ↦ by
    rw [← hx, hker, ← SModEq.sub_mem]
    exact (hL n).symm
  refine ⟨L, hLc, fun y hy ↦ sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n ↦ ?_)⟩
  rw [SModEq.zero, ← hker, hy, hLc]

theorem existsUnique_algHom_of_compatible_tower {A B : Type*} [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] [IsAdicComplete I B] {C : ℕ → Type*} [∀ n, Ring (C n)] [∀ n, Algebra R (C n)]
    (π : ∀ n, B →ₐ[R] C n) (hπ : ∀ n, Function.Surjective (π n))
    (hker : ∀ n x, π n x = 0 ↔ x ∈ (I ^ n • ⊤ : Submodule R B))
    (t : ∀ n, C (n + 1) → C n) (ht : ∀ n x, t n (π (n + 1) x) = π n x)
    (f : ∀ n, A →ₐ[R] C n) (hf : ∀ n a, t n (f (n + 1) a) = f n a) :
    ∃! g : A →ₐ[R] B, ∀ n a, π n (g a) = f n a := by
  have H := fun a ↦ existsUnique_of_compatible_tower I (fun n ↦ π n) hπ
    (fun n x y ↦ by rw [← hker, map_sub, sub_eq_zero]) t ht (fun n ↦ f n a) (fun n ↦ hf n a)
  choose g hg hu using H
  refine ⟨{ toFun := g
            map_one' := (hu _ _ fun n ↦ by simp).symm
            map_mul' a b := (hu _ _ fun n ↦ by simp [hg]).symm
            map_zero' := (hu _ _ fun n ↦ by simp).symm
            map_add' a b := (hu _ _ fun n ↦ by simp [hg]).symm
            commutes' r := (hu _ _ fun n ↦ by simp).symm }, fun n a ↦ hg a n,
    fun g' hg' ↦ AlgHom.ext fun a ↦ hu a _ fun n ↦ hg' n a⟩

end Tower

section Quotient

variable {R : Type*} [CommRing R] (I : Ideal R)

abbrev adicQuotTransition (A : Type*) [CommRing A] [Algebra R A] (n : ℕ) :
    (A ⧸ (I ^ (n + 1)).map (algebraMap R A)) →ₐ[R] A ⧸ (I ^ n).map (algebraMap R A) :=
  Ideal.Quotient.factorₐ R (Ideal.map_mono (Ideal.pow_le_pow_right n.le_succ))

variable [IsNoetherianRing R] [IsAdicComplete I R] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

theorem existsUnique_algHom_of_compatible_quotient [Module.Finite R B]
    (f : ∀ n : ℕ, (A ⧸ (I ^ n).map (algebraMap R A)) →ₐ[R] B ⧸ (I ^ n).map (algebraMap R B))
    (hf : ∀ n x, adicQuotTransition I B n (f (n + 1) x) = f n (adicQuotTransition I A n x)) :
    ∃! g : A →ₐ[R] B, ∀ n a, Ideal.Quotient.mk _ (g a) = f n (Ideal.Quotient.mk _ a) := by
  have := isAdicComplete_of_finite I B
  exact existsUnique_algHom_of_compatible_tower I
    (C := fun n ↦ B ⧸ (I ^ n).map (algebraMap R B)) (fun _ ↦ Ideal.Quotient.mkₐ R _)
    (fun _ ↦ Ideal.Quotient.mk_surjective)
    (fun n x ↦ by
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.smul_top_eq_map,
        Submodule.restrictScalars_mem])
    (fun n ↦ adicQuotTransition I B n) (fun _ _ ↦ rfl)
    (fun n ↦ (f n).comp (Ideal.Quotient.mkₐ R _))
    (fun n a ↦ hf n (Ideal.Quotient.mk _ a))

theorem existsUnique_algEquiv_of_compatible_quotient [Module.Finite R A] [Module.Finite R B]
    (f : ∀ n : ℕ, (A ⧸ (I ^ n).map (algebraMap R A)) ≃ₐ[R] B ⧸ (I ^ n).map (algebraMap R B))
    (hf : ∀ n x, adicQuotTransition I B n (f (n + 1) x) = f n (adicQuotTransition I A n x)) :
    ∃! g : A ≃ₐ[R] B, ∀ n a, Ideal.Quotient.mk _ (g a) = f n (Ideal.Quotient.mk _ a) := by
  obtain ⟨g, hg, hu⟩ := existsUnique_algHom_of_compatible_quotient I (fun n ↦ (f n).toAlgHom) hf
  obtain ⟨g', hg', -⟩ := existsUnique_algHom_of_compatible_quotient I
    (fun n ↦ (f n).symm.toAlgHom) fun n x ↦ by
      apply (f n).injective
      simpa using (hf n ((f (n + 1)).symm x)).symm
  have hA := (existsUnique_algHom_of_compatible_quotient I (A := A) (B := A)
    (fun n ↦ .id _ _) fun _ _ ↦ rfl).unique (y₁ := g'.comp g) (y₂ := .id _ _)
    (fun n a ↦ by simp [hg, hg']) fun _ _ ↦ rfl
  have hB := (existsUnique_algHom_of_compatible_quotient I (A := B) (B := B)
    (fun n ↦ .id _ _) fun _ _ ↦ rfl).unique (y₁ := g.comp g') (y₂ := .id _ _)
    (fun n a ↦ by simp [hg, hg']) fun _ _ ↦ rfl
  exact ⟨.ofAlgHom g g' hB hA, hg,
    fun e he ↦ AlgEquiv.coe_algHom_injective (hu e.toAlgHom he)⟩

end Quotient

section Tensor

variable {R : Type*} [CommRing R] (I : Ideal R)

abbrev adicTensorTransition (A : Type*) [Ring A] [Algebra R A] (n : ℕ) :
    (R ⧸ I ^ (n + 1)) ⊗[R] A →ₐ[R] (R ⧸ I ^ n) ⊗[R] A :=
  Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ))
    (AlgHom.id R A)

theorem one_tmul_quotient_eq_zero_iff (J : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    (x : M) : (1 : R ⧸ J) ⊗ₜ[R] x = 0 ↔ x ∈ (J • ⊤ : Submodule R M) := by
  rw [← (quotTensorEquivQuotSMul M J).map_eq_zero_iff, quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.Quotient.mk_eq_zero]

variable [IsNoetherianRing R] [IsAdicComplete I R]

theorem eq_of_forall_one_tmul_quotient_eq {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {x y : M}
    (h : ∀ n, (1 : R ⧸ I ^ n) ⊗ₜ[R] x = (1 : R ⧸ I ^ n) ⊗ₜ[R] y) : x = y := by
  have := isAdicComplete_of_finite I M
  refine sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n ↦ ?_)
  rw [SModEq.zero, ← one_tmul_quotient_eq_zero_iff, tmul_sub, h, sub_self]

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

theorem existsUnique_algHom_of_compatible_tensor [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A →ₐ[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A →ₐ[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) :=
  have := isAdicComplete_of_finite I B
  existsUnique_algHom_of_compatible_tower I (fun _ ↦ Algebra.TensorProduct.includeRight)
    (fun n x ↦ by
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul B (I ^ n) x)
      exact ⟨y, by rw [← (quotTensorEquivQuotSMul B (I ^ n)).symm_apply_apply x, ← hy]; rfl⟩)
    (fun n x ↦ one_tmul_quotient_eq_zero_iff _ x)
    (fun n ↦ adicTensorTransition I B n) (fun _ _ ↦ by simp)
    (fun n ↦ ((f n).restrictScalars R).comp Algebra.TensorProduct.includeRight)
    (fun n _ ↦ (hf n _).trans (by simp))

theorem existsUnique_algEquiv_of_compatible_tensor [Module.Finite R A] [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A ≃ₐ[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A ≃ₐ[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := by
  obtain ⟨g, hg, hu⟩ := existsUnique_algHom_of_compatible_tensor I (fun n ↦ (f n).toAlgHom) hf
  obtain ⟨g', hg', -⟩ := existsUnique_algHom_of_compatible_tensor I
    (fun n ↦ (f n).symm.toAlgHom) fun n x ↦ by
      apply (f n).injective
      simp [← hf]
  have hA : g'.comp g = .id _ _ := AlgHom.ext fun a ↦
    eq_of_forall_one_tmul_quotient_eq I fun n ↦ by simp [hg, hg']
  have hB : g.comp g' = .id _ _ := AlgHom.ext fun a ↦
    eq_of_forall_one_tmul_quotient_eq I fun n ↦ by simp [hg, hg']
  exact ⟨.ofAlgHom g g' hB hA, hg,
    fun e he ↦ AlgEquiv.coe_algHom_injective (hu e.toAlgHom he)⟩

end

omit [IsNoetherianRing R] [IsAdicComplete I R] in

theorem comul_one_tmul_eq_distribBaseChange (S : Type*) [CommRing S] [Algebra R S] {A : Type*}
    [AddCommGroup A] [Module R A] [Coalgebra R A] (a : A) :
    Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] a) =
      AlgebraTensorModule.distribBaseChange R S A A (1 ⊗ₜ Coalgebra.comul a) := by
  rw [TensorProduct.comul_tmul]
  induction (Coalgebra.comul a : A ⊗[R] A) with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

section

variable {A B : Type*} [Ring A] [Ring B] [Bialgebra R A] [Bialgebra R B]

theorem existsUnique_bialgHom_of_compatible_tensor [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A →ₐc[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A →ₐc[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := by
  obtain ⟨g, hg, hu⟩ := existsUnique_algHom_of_compatible_tensor I (A := A) (B := B)
    (fun n ↦ (f n : (R ⧸ I ^ n) ⊗[R] A →ₐ[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)) hf
  replace hg : ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := hg
  refine ⟨.ofAlgHom g ?_ ?_, hg, fun g' hg' ↦ BialgHom.ext fun a ↦ congr($(hu g' hg') a)⟩
  · refine AlgHom.ext fun a ↦ eq_of_forall_one_tmul_quotient_eq I fun n ↦ ?_
    have := CoalgHomClass.counit_comp_apply (f n) (1 ⊗ₜ a)
    rw [← hg, TensorProduct.counit_tmul, TensorProduct.counit_tmul] at this
    apply (TensorProduct.rid R _).injective
    simpa using this
  · refine AlgHom.ext fun a ↦ eq_of_forall_one_tmul_quotient_eq I fun n ↦ ?_
    have := CoalgHomClass.map_comp_comul_apply (f n) (1 ⊗ₜ a)
    rw [← hg, comul_one_tmul_eq_distribBaseChange, comul_one_tmul_eq_distribBaseChange] at this
    apply (AlgebraTensorModule.distribBaseChange R (R ⧸ I ^ n) B B).injective
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
    rw [← this]
    induction (Coalgebra.comul a : A ⊗[R] A) with
    | zero => simp
    | tmul x y => simp [hg]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

theorem existsUnique_bialgEquiv_of_compatible_tensor [Module.Finite R A] [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A ≃ₐc[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A ≃ₐc[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := by
  obtain ⟨g, hg, hu⟩ := existsUnique_bialgHom_of_compatible_tensor I (A := A) (B := B)
    (fun n ↦ (f n).toBialgHom) hf
  obtain ⟨e, he, -⟩ := existsUnique_algEquiv_of_compatible_tensor I (A := A) (B := B)
    (fun n ↦ (f n).toAlgEquiv) hf
  have hge : ⇑g = e := funext fun a ↦
    eq_of_forall_one_tmul_quotient_eq I fun n ↦ (hg n a).trans (he n a).symm
  exact ⟨.ofBijective g (hge ▸ e.bijective), hg,
    fun g' hg' ↦ BialgEquiv.ext fun a ↦ congr($(hu g' hg') a)⟩

end

end Tensor

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteQuotientComap
section
open NumberField

namespace GlobalTheory.FiniteQuotientComap

theorem exists_int_mul_mem {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ b : 𝓞 E, (b : E) = (m : E) * a := by

  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (R := ℤ) (Rₘ := ℚ)
    (M := nonZeroDivisors ℤ) a (Algebra.IsIntegral.isIntegral a)
  refine ⟨(m : ℤ), nonZeroDivisors.coe_ne_zero m, (⟨m • a, hm⟩ : 𝓞 E), ?_⟩
  show m • a = _
  rw [Submonoid.smul_def, zsmul_eq_mul]

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm0, hm⟩ := hy
    obtain ⟨k, hk0, hk⟩ := hz
    refine ⟨m * k, mul_ne_zero hm0 hk0, ?_⟩
    have e1 : (m * k) • y = k • (m • y) := by rw [mul_comm, mul_smul]
    have e2 : (m * k) • z = m • (k • z) := mul_smul m k z
    rw [smul_add, e1, e2]
    exact add_mem (zsmul_mem hm k) (zsmul_mem hk m)
  | smul c y _ hy =>

    obtain ⟨m, hm0, hm⟩ := hy
    obtain ⟨k, hk0, b, hb⟩ := exists_int_mul_mem c
    refine ⟨k * m, mul_ne_zero hk0 hm0, ?_⟩
    have e : (k * m) • (c • y) = b • (m • y) := by
      ext i
      simp [Algebra.smul_def, hb]
      ring
    rw [e]
    exact L.smul_mem b hm

theorem finite_quotient_comap {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L₀ L : Submodule (𝓞 E) (Fin n → E)) (h₀ : L₀.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := by

  have : Module.Finite (𝓞 E) L₀ := Module.Finite.iff_fg.mpr h₀
  have : Module.Finite ℤ L₀ := Module.Finite.trans (𝓞 E) L₀
  apply Module.finite_of_fg_torsion
  intro q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.comap L₀.subtype L) q
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem L (y : Fin n → E) (by rw [hL]; exact Submodule.mem_top)
  refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm0⟩, ?_⟩
  change (m : ℤ) • (Submodule.Quotient.mk y : L₀ ⧸ Submodule.comap L₀.subtype L) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  simpa using hm

end GlobalTheory.FiniteQuotientComap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtDetOfOne
section
namespace GlobalTheory.DetDerivativeAtOne

open Equiv Finset

theorem hasDerivAt_det_of_one {n : Type} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A (0 : ℝ) = (1 : Matrix n n ℂ))
    (hd : ∀ (i j : n), HasDerivAt (fun (t : ℝ) ↦ A t i j) (A' i j) (0 : ℝ)) :
    HasDerivAt (fun (t : ℝ) ↦ Matrix.det (A t)) (Matrix.trace A') (0 : ℝ) := by
  have hfun : (fun t : ℝ ↦ Matrix.det (A t)) =
      fun t ↦ ∑ σ : Perm n, ((Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i :=
    funext fun t ↦ Matrix.det_apply' _
  rw [hfun]
  have hσ : ∀ σ : Perm n, HasDerivAt (fun t : ℝ ↦ ∏ i, A t (σ i) i)
      (∑ i, (∏ j ∈ univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0 :=
    fun σ ↦ HasDerivAt.fun_finsetProd (fun i _ ↦ hd (σ i) i)
  have hsum := HasDerivAt.fun_sum (u := (univ : Finset (Perm n)))
    (fun σ _ ↦ (hσ σ).const_mul ((Perm.sign σ : ℤ) : ℂ))
  refine hsum.congr_deriv (Eq.symm ?_)
  rw [h0]
  rw [Finset.sum_eq_single (1 : Perm n)]
  · simp [Matrix.trace, Perm.one_apply, Matrix.one_apply]
  · intro σ _ hσ1
    have hz : ∀ i, (∏ j ∈ univ.erase i, (1 : Matrix n n ℂ) (σ j) j) = 0 := by
      intro i
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hc
        push Not at hc
        exact hσ1 (Equiv.ext hc)
      by_cases hki : k = i
      · subst hki
        apply Finset.prod_eq_zero (i := σ k)
        · simp [hk]
        · have : σ (σ k) ≠ σ k := fun h ↦ hk (σ.injective h)
          simp [Matrix.one_apply_ne this]
      · apply Finset.prod_eq_zero (i := k)
        · simp [hki]
        · simp [Matrix.one_apply_ne hk]
    simp [hz]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.DetDerivativeAtOne
end

