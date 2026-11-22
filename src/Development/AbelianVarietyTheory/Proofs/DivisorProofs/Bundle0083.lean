import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanHeisenbergTranslatesOfVacuum
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.HeisVacuum

theorem mem_span_translates_vacuum (X M : Type) [AddCommGroup X] [AddCommGroup M] [Module ℂ M]
    (β : X → X → ℂ) (ρ : X → M →ₗ[ℂ] M) (Λ : AddSubgroup X) (e : M)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1) (h0 : ∀ v, ρ 0 v = v)
    (hρ : ∀ x y v, ρ x (ρ y v) = β x y • ρ (x + y) v)
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ a ∈ Λ, β x a ^ 2 = 1)
    (hdiv : ∀ N : ℕ, 0 < N → ∀ x : X, ∃ y : X, N • y = x)
    (hfin : ∀ N : ℕ, 0 < N → ∃ R : Set X, R.Finite ∧ ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + N • u)
    (he : e ≠ 0) (hε : ∀ u ∈ Λ, ∃ ε : ℂ, ρ u e = ε • e) (h2 : ∀ u ∈ Λ, ρ (2 • u) e = e)
    (hvac : ∀ v : M, (∀ u ∈ Λ, ∀ ε : ℂ, ρ u e = ε • e → ρ u v = ε • v) → ∃ c : ℂ, v = c • e)
    (v : M) (hv : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ Λ, ρ (N • u) v = v) :
    v ∈ Submodule.span ℂ (Set.range fun x => ρ x e) := by
  classical
  obtain ⟨N, hN, hv⟩ := hv
  have hsym : ∀ x y, β x y * β y x = 1 := by
    intro x y
    have := hd (x + y)
    rw [hl, hr, hr, hd, hd] at this
    simpa using this
  have hne : ∀ x y, β x y ≠ 0 := fun x y => left_ne_zero_of_mul_eq_one (hsym x y)
  have hz1 : ∀ y, β 0 y = 1 := by
    intro y
    have := hl 0 0 y
    rw [add_zero] at this
    exact (mul_eq_left₀ (hne 0 y)).1 this.symm
  have hz2 : ∀ y, β y 0 = 1 := by
    intro y
    have := hsym y 0
    rwa [hz1, mul_one] at this
  have hp1 : ∀ (n : ℕ) x y, β (n • x) y = β x y ^ n := by
    intro n x y
    induction n with
    | zero => simp [hz1]
    | succ n ih => rw [succ_nsmul, hl, ih, pow_succ]
  have hp2 : ∀ (n : ℕ) x y, β x (n • y) = β x y ^ n := by
    intro n x y
    induction n with
    | zero => simp [hz2]
    | succ n ih => rw [succ_nsmul, hr, ih, pow_succ]
  have hcomm : ∀ x y w, ρ x (ρ y w) = β x y ^ 2 • ρ y (ρ x w) := by
    intro x y w
    rw [hρ, hρ, smul_smul, add_comm y x, pow_two, mul_assoc, hsym, mul_one]
  have hinv : ∀ t w, ρ t (ρ (-t) w) = w := by
    intro t w
    have := hr t t (-t)
    rw [add_neg_cancel, hz2, hd, one_mul] at this
    rw [hρ, add_neg_cancel, h0, ← this, one_smul]
  choose! ε hε using hε
  have huniq : ∀ u ∈ Λ, ∀ c : ℂ, ρ u e = c • e → c = ε u := by
    intro u hu c hc
    rw [hε u hu] at hc
    exact (smul_left_injective ℂ he hc).symm
  have hεne : ∀ u ∈ Λ, ε u ≠ 0 := by
    intro u hu h
    have := hinv (-u) e
    rw [neg_neg, hε u hu, h, zero_smul, map_zero] at this
    exact he this.symm
  have hεmul : ∀ u ∈ Λ, ∀ u' ∈ Λ, ε u * ε u' = β u u' * ε (u + u') := by
    intro u hu u' hu'
    have := hρ u u' e
    rw [hε u' hu', map_smul, hε u hu, hε _ (Λ.add_mem hu hu'), smul_smul, smul_smul, mul_comm] at this
    exact smul_left_injective ℂ he this
  let A : Λ → M → M := fun u w => (ε u)⁻¹ • ρ u w
  have hA : ∀ (u u' : Λ) w, A u (A u' w) = A (u + u') w := by
    intro u u' w
    simp only [A, map_smul, hρ, smul_smul, AddSubgroup.coe_add]
    congr 1
    have h1 := hεmul u u.2 u' u'.2
    have h3 := hεne u u.2
    have h4 := hεne u' u'.2
    have h5 := hεne _ (Λ.add_mem u.2 u'.2)
    field_simp
    rw [h1, mul_comm]
  have hA0 : ∀ w, A 0 w = w := by
    intro w
    have : (1 : ℂ) = ε 0 := huniq 0 Λ.zero_mem 1 (by rw [h0, one_smul])
    simp [A, h0, ← this]
  set K : ℕ := 2 * N with hK
  have hKpos : 0 < K := by omega
  have hεK : ∀ u ∈ Λ, ε (K • u) = 1 := by
    intro u hu
    refine (huniq _ (Λ.nsmul_mem hu K) 1 ?_).symm
    rw [one_smul, hK, mul_comm, mul_nsmul]
    exact h2 _ (Λ.nsmul_mem hu N)
  have hvK : ∀ u ∈ Λ, ρ (K • u) v = v := by
    intro u hu
    rw [hK, mul_nsmul]
    exact hv _ (Λ.nsmul_mem hu 2)
  let H : AddSubgroup Λ := (nsmulAddMonoidHom K : Λ →+ Λ).range
  have hQ : Finite (Λ ⧸ H) := by
    obtain ⟨R, hR, hR'⟩ := hfin K hKpos
    have : Finite {x : Λ // (x : X) ∈ R} := by
      have : Finite R := hR
      exact Finite.of_injective (fun x : {x : Λ // (x : X) ∈ R} => (⟨x.1, x.2⟩ : R))
        (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : R => (z : X)) h)))
    refine Finite.of_surjective (fun x : {x : Λ // (x : X) ∈ R} => (QuotientAddGroup.mk x.1 : Λ ⧸ H)) ?_
    intro q
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, u, hu, htu⟩ := hR' t t.2
    have hrΛ : r ∈ Λ := by
      have : r = t - K • u := by rw [htu]; abel
      rw [this]
      exact Λ.sub_mem t.2 (Λ.nsmul_mem hu K)
    refine ⟨⟨⟨r, hrΛ⟩, hr⟩, ?_⟩
    refine QuotientAddGroup.eq.2 ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    simp [htu]
  have := Fintype.ofFinite (Λ ⧸ H)
  have hwell : ∀ w, (∀ u ∈ Λ, ρ (K • u) w = w) → ∀ x y : Λ,
      (QuotientAddGroup.mk x : Λ ⧸ H) = QuotientAddGroup.mk y → A x w = A y w := by
    intro w hw x y hxy
    obtain ⟨u, hu⟩ := QuotientAddGroup.eq.1 hxy
    have h1 : y = x + K • u := by
      have : K • u = -x + y := hu
      rw [this]; abel
    have h3 : A (K • u) w = w := by
      simp only [A, AddSubgroup.coe_nsmul, hεK u u.2, hw u u.2, inv_one, one_smul]
    rw [h1, ← hA, h3]
  have hAsum : ∀ (u : Λ) (f : Λ ⧸ H → M), A u (∑ q, f q) = ∑ q, A u (f q) := by
    intro u f
    simp only [A, map_sum, Finset.smul_sum]
  have hP : ∀ w, (∀ u ∈ Λ, ρ (K • u) w = w) → ∃ c : ℂ, (∑ q : Λ ⧸ H, A q.out w) = c • e := by
    intro w hw
    apply hvac
    intro u hu c hc
    rw [huniq u hu c hc]
    have h1 : A ⟨u, hu⟩ (∑ q : Λ ⧸ H, A q.out w) = ∑ q : Λ ⧸ H, A q.out w := by
      rw [hAsum]
      refine Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk ⟨u, hu⟩ : Λ ⧸ H)) _ _ ?_
      intro q
      rw [hA]
      apply hwell w hw
      simp
    conv_rhs => rw [← h1]
    simp only [A, smul_smul, mul_inv_cancel₀ (hεne u hu), one_smul]
  let Tg : AddSubgroup X := Λ.comap (nsmulAddMonoidHom K : X →+ X)
  have hTg : ∀ t, t ∈ Tg ↔ K • t ∈ Λ := fun t => Iff.rfl
  let S := Submodule.span ℂ (Set.range fun x => ρ x e)
  have hmem : ∀ t ∈ Tg, (∑ q : Λ ⧸ H, β t (q.out : Λ) ^ 2 • A q.out v) ∈ S := by
    intro t ht
    obtain ⟨c, hc⟩ := hP (ρ (-t) v) (by
      intro u hu
      rw [hcomm, hvK u hu, hp1, ← hp2, (hΛ u).1 hu _ ((hTg _).1 (Tg.neg_mem ht)), one_smul])
    have h1 := congrArg (ρ t) hc
    rw [map_sum, map_smul] at h1
    have h3 : c • ρ t e ∈ S := S.smul_mem c (Submodule.subset_span ⟨t, rfl⟩)
    rw [← h1] at h3
    convert h3 using 2 with q
    simp only [A, map_smul]
    rw [hcomm t, hinv, smul_comm]
  let χ : Λ ⧸ H → (Multiplicative Tg →* ℂ) := fun q =>
    { toFun := fun t => β (t.toAdd : Tg) (q.out : Λ) ^ 2
      map_one' := by simp [hz1]
      map_mul' := by intro a b; simp [hl, mul_pow] }
  have hχ : Function.Injective χ := by
    intro q q' h
    have h1 : ∀ t ∈ Tg, β t (q.out : Λ) ^ 2 = β t (q'.out : Λ) ^ 2 := fun t ht =>
      DFunLike.congr_fun h (Multiplicative.ofAdd ⟨t, ht⟩)
    obtain ⟨y, hy⟩ := hdiv K hKpos (-((q.out : Λ) : X) + (q'.out : Λ))
    have hyΛ : y ∈ Λ := by
      rw [hΛ]
      intro a ha
      obtain ⟨t, rfl⟩ := hdiv K hKpos a
      have h3 := h1 t ha
      have h4 : ((q'.out : Λ) : X) = (q.out : Λ) + K • y := by rw [hy]; abel
      rw [h4, hr, mul_pow, hp2, ← hp1 K] at h3
      have h5 : β (K • t) y ^ 2 = 1 :=
        (mul_eq_left₀ (pow_ne_zero 2 (hne _ _))).1 h3.symm
      have h6 := congrArg (· ^ 2) (hsym y (K • t))
      simpa [mul_pow, h5] using h6
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
    exact QuotientAddGroup.eq.2 ⟨⟨y, hyΛ⟩, Subtype.ext (by simpa using hy)⟩
  have hli : LinearIndependent ℂ (fun q => (χ q : Multiplicative Tg → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative Tg) ℂ).comp χ hχ
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have h1 := Fintype.linearIndependent_iff.1 hli (fun q => φ (S.mkQ (A q.out v))) (by
    funext t
    have h3 := (Submodule.Quotient.mk_eq_zero S).2 (hmem _ (t.toAdd).2)
    have h4 := congrArg φ h3
    rw [← Submodule.mkQ_apply, map_sum, map_sum, map_zero] at h4
    simp only [map_smul, smul_eq_mul] at h4
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h4]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _) 0
  have h3 : A (0 : Λ ⧸ H).out v = v := by
    rw [hwell v hvK _ 0 (by simp), hA0]
  simpa [h3] using h1

end GlobalTheory.HeisVacuum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportQuotientIff
section
open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory.QuotientSupportBaseChange

theorem mem_support_baseChange {R A M : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (p : PrimeSpectrum A) :
    p ∈ Module.support A (A ⊗[R] M) ↔
      PrimeSpectrum.comap (algebraMap R A) p ∈ Module.support R M := by

  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  let Kp := p.asIdeal.ResidueField
  let Kq := (PrimeSpectrum.comap (algebraMap R A) p).asIdeal.ResidueField
  have hq : (PrimeSpectrum.comap (algebraMap R A) p).asIdeal = p.asIdeal.comap (algebraMap R A) := rfl
  let _ : Algebra Kq Kp :=
    (Ideal.ResidueField.map (PrimeSpectrum.comap (algebraMap R A) p).asIdeal p.asIdeal (algebraMap R A) hq).toAlgebra
  have : IsScalarTower R Kq Kp := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R Kp r = Ideal.ResidueField.map (PrimeSpectrum.comap (algebraMap R A) p).asIdeal
      p.asIdeal (algebraMap R A) hq (algebraMap R Kq r)
    rw [Ideal.ResidueField.map_algebraMap]
    exact IsScalarTower.algebraMap_apply R A Kp r
  rw [(AlgebraTensorModule.cancelBaseChange R A Kp Kp M).nontrivial_congr,
    ← (AlgebraTensorModule.cancelBaseChange R Kq Kp Kp M).nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right Kq Kp

theorem nonempty_quotient_equiv {R A M N ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) (hf : IsBaseChange A f) (s : ι → M) :
    Nonempty ((A ⊗[R] (M ⧸ Submodule.span R (Set.range s))) ≃ₗ[A]
      N ⧸ Submodule.span A (Set.range fun i => f (s i))) := by

  let n := Submodule.span R (Set.range s)
  let e₀ := AlgebraTensorModule.tensorQuotientEquiv (R := R) A R A n
  have hmap : (LinearMap.range (AlgebraTensorModule.lTensor A A (n.subtype.restrictScalars R))).map
      (hf.equiv : A ⊗[R] M →ₗ[A] N) = Submodule.span A (Set.range fun i => f (s i)) := by
    change (n.baseChange A).map (hf.equiv : A ⊗[R] M →ₗ[A] N) = _
    rw [Submodule.baseChange_span, Submodule.map_span]
    congr 1
    ext x
    simp [IsBaseChange.equiv_tmul]
  exact ⟨e₀.trans (Submodule.Quotient.equiv _ _ hf.equiv hmap)⟩

theorem mem_support_quotient_iff (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R')
    (ga : S ⟶ S') (qa' : R' ⟶ S') (h : IsPushout qa ba ga qa') (hfin : qa.hom.Finite)
    {ι : Type} (s : ι → S) (p : PrimeSpectrum R') :
    ((letI := qa'.hom.toAlgebra; p ∈ Module.support R'
        (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔
      (letI := qa.hom.toAlgebra; PrimeSpectrum.comap ba.hom p ∈ Module.support R
        (S ⧸ Submodule.span R (Set.range s)))) := by
  let _ : Algebra R R' := ba.hom.toAlgebra
  let _ : Algebra R S := qa.hom.toAlgebra
  let _ : Algebra R' S' := qa'.hom.toAlgebra
  let _ : Algebra S S' := ga.hom.toAlgebra
  let _ : Algebra R S' := (qa ≫ ga).hom.toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => by
    change (qa ≫ ga).hom r = qa'.hom (ba.hom r)
    rw [h.w]
    rfl
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun r => rfl
  have hpo : Algebra.IsPushout R R' S S' := CommRingCat.isPushout_iff_isPushout.mp h.flip
  have : Module.Finite R S := hfin

  obtain ⟨e⟩ : Nonempty ((R' ⊗[R] (S ⧸ Submodule.span R (Set.range s))) ≃ₗ[R']
      S' ⧸ Submodule.span R' (Set.range fun i => ga.hom (s i))) :=
    nonempty_quotient_equiv _ hpo.out s
  have key : p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range fun i => ga.hom (s i))) ↔
      PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)) := by
    rw [← e.support_eq]
    exact mem_support_baseChange p
  exact key

end GlobalTheory.QuotientSupportBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicCoeffNatDegreeSubEqMulCmConj
section
open NumberField Polynomial

namespace GlobalTheory

theorem coeff_natDegree_sub_eq_of_roots_norm_one (Q : ℂ[X]) (hQ : Q.Monic)
    (hroots : ∀ z ∈ Q.roots, ‖z‖ = 1) :
    ∀ i ≤ Q.natDegree, Q.coeff (Q.natDegree - i) = Q.coeff 0 * starRingEnd ℂ (Q.coeff i) := by
  intro i hi
  set s := Q.roots with hs
  have hprod : (s.map fun z => X - C z).prod = Q := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := Q) IsAlgClosed.card_roots_eq_natDegree
    rwa [hQ.leadingCoeff, C_1, one_mul] at h
  have hrevX : ∀ z ∈ s, (X - C z : ℂ[X]).reverse = C (-z) * (X - C (starRingEnd ℂ z)) := by
    intro z hz
    have hz1 : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hroots z hz]; simp
    rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, ← one_mul (X : ℂ[X]), reverse_mul_X, ← C_1, reverse_C]
    rw [mul_sub, ← C_mul, neg_mul, hz1]
    simp only [C_1, C_neg, one_mul, pow_one]
    ring
  have hrev : Q.reverse = C (Q.coeff 0) * Q.map (starRingEnd ℂ) := by
    have key : ∀ t : Multiset ℂ, (∀ z ∈ t, (X - C z : ℂ[X]).reverse = C (-z) * (X - C (starRingEnd ℂ z))) →
        (t.map fun z => X - C z).prod.reverse
          = (t.map fun z => C (-z) * (X - C (starRingEnd ℂ z))).prod := by
      intro t
      induction t using Multiset.induction_on with
      | empty => intro _; simpa using reverse_C (1 : ℂ)
      | cons a t ih =>
        intro h
        rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
          reverse_mul_of_domain, ih (fun z hz => h z (Multiset.mem_cons_of_mem hz)),
          h a (Multiset.mem_cons_self a t)]
    conv_lhs => rw [← hprod]
    rw [key s hrevX, Multiset.prod_map_mul]
    conv_rhs => rw [← hprod]
    congr 1
    · rw [coeff_zero_multiset_prod, Multiset.map_map, map_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro z _
      simp
    · rw [Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro z _
      simp
  have h1 := congrArg (fun p => p.coeff i) hrev
  simp only [coeff_reverse, coeff_C_mul, coeff_map] at h1
  rwa [revAt_le hi] at h1

theorem monic_coeff_natDegree_sub_eq_mul_complexConj :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Polynomial E),
    P.Monic → P.natDegree = n → (∀ (τ : E →+* ℂ), ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) →
    ∀ i ≤ n, P.coeff (n - i) = P.coeff 0 * IsCMField.complexConj E (P.coeff i) := by
  intro E _ _ _ n P hP hn hroots i hi
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  have hQ : (P.map τ).Monic := hP.map τ
  have hdeg : (P.map τ).natDegree = n := by rw [hP.natDegree_map, hn]
  have h := coeff_natDegree_sub_eq_of_roots_norm_one (P.map τ) hQ (hroots τ) i (hdeg ▸ hi)
  rw [hdeg, coeff_map, coeff_map, coeff_map, ← IsCMField.complexEmbedding_complexConj E τ,
    ← map_mul] at h
  exact τ.injective h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicSplitsValuationSubringOfSeparableReduction
section
open Polynomial IsLocalRing

namespace GlobalTheory

theorem monic_splits_of_separable_residue (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (V : ValuationSubring Ω) (q : Polynomial V) (hq : q.Monic)
    (hs : (q.map (IsLocalRing.residue V)).Separable) :
    ∃ s : Multiset V, q = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  have hinj : Function.Injective (algebraMap V Ω) := IsFractionRing.injective V Ω

  have hQ : (q.map (algebraMap V Ω)).Splits := by
    rw [splits_iff_splits]
    right
    intro g hg hgd
    obtain ⟨g₀, hg₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd Ω hq hgd
    have hg0 : g ≠ 0 := hg.ne_zero
    have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
    have hmap : g₀.map (algebraMap V Ω) = g * C g.leadingCoeff⁻¹ := by
      set c := g.leadingCoeff with hc
      rw [← hg₀, mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, mul_one]
    have hmapm : (g₀.map (algebraMap V Ω)).Monic := by
      rw [hmap]; exact monic_mul_leadingCoeff_inv hg0
    have hg₀m : g₀.Monic := monic_of_injective hinj hmapm
    have hdvd : g₀ ∣ q := by
      rw [← map_dvd_map (algebraMap V Ω) hinj hg₀m, hmap]
      refine dvd_trans (Dvd.intro (C g.leadingCoeff) ?_) hgd
      rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
    have hsep₀ : (g₀.map (residue V)).Separable :=
      hs.of_dvd (Polynomial.map_dvd _ hdvd)
    have hdeg : (g₀.map (residue V)).natDegree = g.natDegree := by
      rw [hg₀m.natDegree_map, ← natDegree_map_eq_of_injective hinj, hmap,
        natDegree_mul_C (inv_ne_zero hlc)]
    have hgdeg : g.natDegree ≠ 0 := fun h =>
      hg.not_isUnit (isUnit_iff_degree_eq_zero.mpr ((degree_eq_iff_natDegree_eq hg0).mpr h))
    have hder₀ : derivative (g₀.map (residue V)) ≠ 0 := by
      intro h0
      have hu : IsUnit (g₀.map (residue V)) := by
        have := hsep₀
        rw [Polynomial.Separable, h0, isCoprime_zero_right] at this
        exact this
      exact hgdeg (hdeg ▸ natDegree_eq_zero_of_isUnit hu)
    have hder : derivative g ≠ 0 := by
      intro h0
      apply hder₀
      have h1 : derivative (g₀.map (algebraMap V Ω)) = 0 := by
        rw [hmap, derivative_mul, derivative_C, h0]; simp
      rw [derivative_map] at h1 ⊢
      have h2 : derivative g₀ = 0 := by
        apply Polynomial.map_injective _ hinj
        rw [h1, Polynomial.map_zero]
      rw [h2, Polynomial.map_zero]
    exact IsSepClosed.degree_eq_one_of_irreducible Ω hg
      ((separable_iff_derivative_ne_zero hg).mpr hder)
  have hroots : ∀ a ∈ (q.map (algebraMap V Ω)).roots, a ∈ (algebraMap V Ω).range := by
    intro a ha
    have hne : q.map (algebraMap V Ω) ≠ 0 := (hq.map _).ne_zero
    have hr : aeval a q = 0 := by
      rw [mem_roots hne, IsRoot, eval_map_algebraMap] at ha
      exact ha
    have hint : IsIntegral V a := ⟨q, hq, by rwa [← aeval_def]⟩
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := Ω)).mp hint
    exact ⟨y, hy⟩
  have hqs : q.Splits := Splits.of_splits_map_of_injective hinj hQ hroots
  exact ⟨q.roots, hqs.eq_prod_roots_of_monic hq⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorseInequalityArith
section
namespace GlobalTheory

theorem morse_inequality_arith (d : ℕ) (a b : ℤ) (h g : ℕ → ℕ) (C C' m₀ m₁ : ℕ)
    (H1 : ∀ m : ℕ, m₀ ≤ m → |((d + 1).factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ (d + 1)| ≤
      C * (((d + 1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ (d + 1 - 1)))
    (H2 : ∀ m : ℕ, m₁ ≤ m → |(d.factorial : ℤ) * (g m : ℤ) - b * (m : ℤ) ^ d| ≤
      C' * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)))
    (hab : ((d : ℤ) + 1) * b < a) : ∃ m : ℕ, 1 ≤ m ∧ m * g m < h m := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = C * (d + 1) + (d + 1) * C' * d := ⟨_, rfl⟩
  obtain ⟨m, hm0, hm1, hmK⟩ : ∃ m : ℕ, m₀ ≤ m ∧ m₁ ≤ m ∧ K * 2 ^ d + 1 ≤ m :=
    ⟨m₀ + m₁ + (K * 2 ^ d + 1), by omega, by omega, by omega⟩
  have hm : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hmK
  refine ⟨m, hm, ?_⟩
  by_contra hcon
  have hcon' : (h m : ℤ) ≤ (m : ℤ) * g m := by exact_mod_cast not_lt.mp hcon
  have h1 := (abs_le.mp (H1 m hm0)).1
  have h2 := (abs_le.mp (H2 m hm1)).2
  rw [Nat.add_sub_cancel, Nat.factorial_succ] at h1
  push_cast at h1
  have hM : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hMK : (K : ℤ) * 2 ^ d + 1 ≤ m := by exact_mod_cast hmK
  have hKz : (K : ℤ) = C * ((d : ℤ) + 1) + (d + 1) * C' * d := by rw [hK]; push_cast; ring
  generalize (m : ℤ) = M at *
  have hF : (0 : ℤ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hd : (0 : ℤ) ≤ d := by positivity
  have hA : M * ((d : ℤ) * (M + 1) ^ (d - 1)) ≤ d * (M + 1) ^ d := by
    rcases d with _ | e
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      have : (0 : ℤ) ≤ ((e + 1 : ℕ) : ℤ) * (M + 1) ^ e := by positivity
      nlinarith
  have hP : (M + 1) ^ d ≤ 2 ^ d * M ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) d
  have hQ : 0 < M ^ d := by positivity
  have e1 : ((d : ℤ) + 1) * d.factorial * h m ≤ ((d : ℤ) + 1) * d.factorial * (M * g m) :=
    mul_le_mul_of_nonneg_left hcon' (by positivity)
  have e2 : ((d : ℤ) + 1) * M * ((d.factorial : ℤ) * g m - b * M ^ d) ≤
      ((d : ℤ) + 1) * M * (C' * ((d : ℤ) * (M + 1) ^ (d - 1))) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e3 : ((d : ℤ) + 1) * C' * (M * ((d : ℤ) * (M + 1) ^ (d - 1))) ≤
      ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have e4 : (K : ℤ) * (M + 1) ^ d ≤ K * (2 ^ d * M ^ d) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have e5 : ((K : ℤ) * 2 ^ d + 1) * M ^ d ≤ M * M ^ d :=
    mul_le_mul_of_nonneg_right hMK hQ.le
  have e6 : (((d : ℤ) + 1) * b + 1) * (M * M ^ d) ≤ a * (M * M ^ d) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e7 : (K : ℤ) * (M + 1) ^ d =
      C * ((d + 1) * (M + 1) ^ d) + ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d) := by
    rw [hKz]; ring
  rw [pow_succ' M d] at h1
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemIdentityComponentOfRational
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem GlobalTheory.mul_mem_identityComponent_of_rational : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), x.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → (x * y).left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) := by
  intro k _ G _ x y hx hy
  set T : G ⟶ G := (toUnit G ≫ x) * 𝟙 G with hT
  have hyT : y ≫ T = x * y := by
    rw [hT, comp_mul, ← Category.assoc, toUnit_unique (y ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id]
  have hηT : η[G] ≫ T = x := by
    rw [hT, comp_mul, ← Category.assoc, toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id]
    have : (η[G] : 𝟙_ _ ⟶ G) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [this, _root_.mul_one]
  have hsub := T.left.continuous.image_connectedComponent_subset ((η[G]).left (IsLocalRing.closedPoint k))
  have h1 : (x * y).left (IsLocalRing.closedPoint k) = T.left (y.left (IsLocalRing.closedPoint k)) := by
    rw [← hyT, Over.comp_left]
    exact Scheme.Hom.comp_apply y.left T.left _
  have h2 : T.left ((η[G]).left (IsLocalRing.closedPoint k)) = x.left (IsLocalRing.closedPoint k) := by
    rw [← hηT, Over.comp_left]
    exact (Scheme.Hom.comp_apply (η[G]).left T.left _).symm
  rw [h1, connectedComponent_eq hx]
  have := hsub ⟨_, hy, rfl⟩
  rwa [h2] at this
end

