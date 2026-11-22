import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreGoingDownTensor
section
open TensorProduct

namespace GlobalTheory

theorem fibre_going_down_tensor : ∀ (S A C : Type) [CommRing S] [CommRing A] [CommRing C] [Algebra S A] [Algebra S C]
    (u : Ideal (TensorProduct S A C)) [u.IsPrime] (Q₁ : Ideal C) [Q₁.IsPrime],
    Q₁ ≤ u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) →
    Q₁.comap (algebraMap S C) = u.comap (algebraMap S (TensorProduct S A C)) →
    ∃ Q : Ideal (TensorProduct S A C), Q.IsPrime ∧ Q ≤ u ∧
      Q.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) = Q₁ ∧
      Q.comap (algebraMap A (TensorProduct S A C)) = u.comap (algebraMap A (TensorProduct S A C)) := by
  intro S A C _ _ _ _ _ u _ Q₁ _ hle h2
  let p := u.comap (algebraMap A (A ⊗[S] C))
  let p₁ := u.comap (algebraMap S (A ⊗[S] C))
  have hp : p₁ = p.comap (algebraMap S A) := by
    simp only [p, p₁, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  let K₁ := p₁.ResidueField
  let K := p.ResidueField
  letI : Algebra K₁ K := (Ideal.ResidueField.mapₐ p₁ p (Algebra.ofId S A) hp).toAlgebra
  haveI : IsScalarTower S K₁ K := IsScalarTower.of_algebraMap_eq
    (fun s => ((Ideal.ResidueField.mapₐ p₁ p (Algebra.ofId S A) hp).commutes s).symm)
  let F₁ := p₁.Fiber C
  let E := F₁ ⊗[K₁] K
  let e1 : p.Fiber (A ⊗[S] C) ≃ₐ[K] K ⊗[S] C := Algebra.TensorProduct.cancelBaseChange S A K K C
  let e2 : K ⊗[K₁] F₁ ≃ₐ[K] K ⊗[S] C := Algebra.TensorProduct.cancelBaseChange S K₁ K K C
  let e3 : K ⊗[K₁] F₁ ≃ₐ[K₁] E := Algebra.TensorProduct.comm K₁ K F₁
  haveI : Module.Flat F₁ E := inferInstance
  haveI : Algebra.HasGoingDown F₁ E := inferInstance
  let Φ : p.Fiber (A ⊗[S] C) ≃+* E :=
    (e1.toRingEquiv.trans e2.symm.toRingEquiv).trans e3.toRingEquiv
  have hΦ : ∀ c : C, Φ (Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeRight c : A ⊗[S] C))
      = algebraMap F₁ E (Algebra.TensorProduct.includeRight c) := by
    intro c
    simp only [Φ, e1, e2, e3, Algebra.TensorProduct.includeRight_apply, RingEquiv.trans_apply,
      AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    erw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    rfl

  haveI : u.LiesOver p := ⟨rfl⟩
  let isoA := PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗[S] C) p
  let ub := isoA ⟨u, inferInstance, inferInstance⟩
  have hub : ub.asIdeal.comap (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) = u := by
    have := congrArg Subtype.val (isoA.symm_apply_apply ⟨u, inferInstance, inferInstance⟩)
    exact this
  have hmem : ∀ y : A ⊗[S] C, (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) y
      ∈ ub.asIdeal ↔ y ∈ u := fun y => Iff.of_eq (congrArg (y ∈ ·) hub)

  haveI : Q₁.LiesOver p₁ := ⟨h2.symm⟩
  let iso₁ := PrimeSpectrum.primesOverOrderIsoFiber S C p₁
  let Qb := iso₁ ⟨Q₁, inferInstance, inferInstance⟩
  have hQb : Qb.asIdeal.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] F₁) = Q₁ := by
    have := congrArg Subtype.val (iso₁.symm_apply_apply ⟨Q₁, inferInstance, inferInstance⟩)
    exact this

  let ue : Ideal E := ub.asIdeal.comap (Φ.symm : E →+* p.Fiber (A ⊗[S] C))
  haveI : ue.IsPrime := Ideal.comap_isPrime _ _
  let w : Ideal F₁ := ue.comap (algebraMap F₁ E)
  haveI : w.IsPrime := Ideal.comap_isPrime _ _
  haveI : ue.LiesOver w := ⟨rfl⟩
  have hw : w.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] F₁) =
      u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] A ⊗[S] C) := by
    ext c
    change Φ.symm (algebraMap F₁ E (Algebra.TensorProduct.includeRight c)) ∈ ub.asIdeal ↔ _
    rw [← hΦ, RingEquiv.symm_apply_apply]
    exact hmem _
  have hwle : Qb.asIdeal ≤ w := by
    let u₁ := u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] A ⊗[S] C)
    haveI : u₁.IsPrime := Ideal.comap_isPrime _ _
    haveI : u₁.LiesOver p₁ := ⟨by
      show p₁ = u₁.comap (algebraMap S C)
      ext s
      simp [u₁, p₁]⟩
    let wP : PrimeSpectrum F₁ := ⟨w, inferInstance⟩
    have hsym : (iso₁.symm wP).1 = u₁ := hw
    have key : iso₁.symm Qb ≤ iso₁.symm wP := by
      show (iso₁.symm Qb).1 ≤ (iso₁.symm wP).1
      rw [hsym, iso₁.symm_apply_apply]
      exact hle
    exact (iso₁.symm.le_iff_le.mp key : Qb ≤ wP)
  obtain ⟨P, hPle, hPprime, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := Qb.asIdeal) (q := w) ue hwle
  refine ⟨(P.comap (Φ : p.Fiber (A ⊗[S] C) →+* E)).comap
    (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)), inferInstance, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hmem]
    have := hPle hx
    simpa [ue] using this
  · ext c
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap]
    erw [hΦ c]
    rw [← hQb, Ideal.mem_comap, ← Ideal.mem_comap, ← Ideal.under_def, ← hPover.over]
  · ext a
    let J : Ideal K := (P.comap (Φ : p.Fiber (A ⊗[S] C) →+* E)).comap (algebraMap K (p.Fiber (A ⊗[S] C)))
    haveI : J.IsPrime := Ideal.comap_isPrime _ _
    have hJ : J = ⊥ := Ideal.eq_bot_of_prime J
    have hx : (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C))
        (algebraMap A (A ⊗[S] C) a) = algebraMap K (p.Fiber (A ⊗[S] C)) (algebraMap A K a) := by
      rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    rw [Ideal.mem_comap, Ideal.mem_comap, hx]
    change algebraMap A K a ∈ J ↔ _
    rw [hJ, Ideal.mem_bot, Ideal.algebraMap_residueField_eq_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldCase
section
namespace GlobalTheory.FieldCaseReduction

open Polynomial

theorem field_case (F : Type) [Field F] [Finite F] (t m f : F) (hD : t ^ 2 - 4 * m ≠ 0) :
    ∃ a b : F, a ^ 2 + t * a * b + m * b ^ 2 = f := by
  classical
  by_cases h2 : ringChar F = 2
  · obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two h2 f
    exact ⟨a, 0, by rw [ha]; ring⟩
  · haveI := Fintype.ofFinite F
    have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two h2
    have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero h2
    have hp : (X ^ 2 : F[X]).degree = 2 := by simp
    have hq : (C (-(t ^ 2 - 4 * m)) * X ^ 2 + C 0 * X + C (-(4 * f)) : F[X]).degree = 2 :=
      degree_quadratic (neg_ne_zero.mpr hD)
    obtain ⟨x, b, hxb⟩ := FiniteField.exists_root_sum_quadratic hp hq hodd
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hxb
    refine ⟨(x - t * b) / 2, b, ?_⟩
    field_simp
    linear_combination hxb

theorem main (S : Type) [inst : CommRing S] [Finite S] [IsReduced S] (t m f : S)
    (hD : IsUnit (t ^ (2 : ℕ) - (4 : S) * m)) (_hf : IsUnit f) :
    ∃ (a : S) (b : S), a ^ (2 : ℕ) + t * a * b + m * b ^ (2 : ℕ) = f := by
  classical
  haveI : IsArtinianRing S := isArtinian_of_finite
  let e := (IsArtinianRing.equivPi S).toRingEquiv
  have key : ∀ I : MaximalSpectrum S, ∃ a b : S ⧸ I.asIdeal,
      a ^ 2 + e t I * a * b + e m I * b ^ 2 = e f I := by
    intro I
    haveI := I.isMaximal
    letI : Field (S ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Finite (S ⧸ I.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    apply field_case
    have h := (hD.map ((Pi.evalRingHom (fun J : MaximalSpectrum S => S ⧸ J.asIdeal) I).comp
      e.toRingHom)).ne_zero
    simp only [map_sub, map_mul, map_pow, map_ofNat] at h
    exact h
  choose a b hab using key
  refine ⟨e.symm a, e.symm b, e.injective ?_⟩
  simp only [map_add, map_mul, map_pow, RingEquiv.apply_symm_apply]
  funext I
  exact hab I

end GlobalTheory.FieldCaseReduction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAwayOfIsAlgebraicOfFiniteType
section
namespace GlobalTheory

theorem finite_away_of_isAlgebraic_of_finiteType : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Module.Finite A' B' := by
  intro A B _ _ _ _ hft halg
  obtain ⟨s, hs⟩ := hft.out
  choose y hy hint using fun b : B =>
    (Algebra.IsAlgebraic.isAlgebraic (R := A) b).exists_integral_multiple
  refine ⟨∏ b ∈ s, y b, Finset.prod_ne_zero_iff.mpr fun b _ => hy b, ?_⟩
  intro c A' B' _ _ _ _ _ _ _ _ hA' hB'
  set a := ∏ b ∈ s, y b with ha
  haveI hBB : Algebra.FiniteType B B' :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (algebraMap A B (a * c))) B'
  haveI : Algebra.FiniteType A B' := Algebra.FiniteType.trans hft hBB
  haveI : Algebra.FiniteType A' B' := .of_restrictScalars_finiteType A A' B'
  have hu : IsUnit (algebraMap A A' (a * c)) := IsLocalization.Away.algebraMap_isUnit (a * c)
  have hunit : ∀ (r : A) (m : ℕ), r ∣ (a * c) ^ m → ∃ r' : A', algebraMap A' B' r' * algebraMap A B' r = 1 := by
    intro r m hr
    obtain ⟨u, hu'⟩ := isUnit_of_dvd_unit (map_dvd (algebraMap A A') hr) (by rw [map_pow]; exact hu.pow m)
    refine ⟨↑u⁻¹, ?_⟩
    rw [IsScalarTower.algebraMap_apply A A' B', ← hu', ← map_mul, Units.inv_mul, map_one]
  haveI : Algebra.IsIntegral A' B' := by
    let S : Subalgebra A B :=
      ((integralClosure A' B').restrictScalars A).comap (IsScalarTower.toAlgHom A B B')
    have hS : Algebra.adjoin A (s : Set B) ≤ S := by
      rw [Algebra.adjoin_le_iff]
      intro b hb
      have h1 : IsIntegral A' (algebraMap B B' (y b • b)) :=
        ((hint b).map (IsScalarTower.toAlgHom A B B')).tower_top
      obtain ⟨r', hr'⟩ := hunit (y b) 1 (by rw [pow_one]; exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hb) c)
      show IsIntegral A' (algebraMap B B' b)
      have : algebraMap B B' b = algebraMap A' B' r' * algebraMap B B' (y b • b) := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← mul_assoc, hr', one_mul]
      rw [this]
      exact isIntegral_algebraMap.mul h1
    rw [hs] at hS
    constructor
    intro x
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hx⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap A B (a * c))) x
    have hb : IsIntegral A' (algebraMap B B' b) := hS (Algebra.mem_top (x := b))
    obtain ⟨r', hr'⟩ := hunit ((a * c) ^ n) n dvd_rfl
    refine IsIntegral.of_mul_unit (y := algebraMap B B' (algebraMap A B (a * c) ^ n)) (r := r') ?_ ?_
    · rw [← map_pow, ← IsScalarTower.algebraMap_apply]; exact hr'
    · have hx' : x * algebraMap B B' (algebraMap A B (a * c) ^ n) = algebraMap B B' b := hx
      rw [hx']; exact hb
  exact Algebra.IsIntegral.finite

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCardTorsionQuotSmulTopLePowFinrank
section
open scoped TensorProduct

namespace GlobalTheory.TorsionCount

variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem exists_colon_gen (I J : Ideal R) (hI : I.IsMaximal) (hJ : J ≠ ⊥) :
    ∃ c : R, (∀ a ∈ I, c * a ∈ J) ∧ ∀ x : R, (∀ a ∈ I, a * x ∈ J) → ∃ r : R, x - r * c ∈ J := by
  by_cases hle : J ≤ I
  · obtain ⟨J', rfl⟩ := Ideal.dvd_iff_le.2 hle
    have hJ' : J' ≠ ⊥ := by rintro rfl; simp at hJ
    have hI0 : I ≠ ⊥ := by rintro rfl; simp at hJ
    have hne : ¬ J' ≤ I * J' := by
      intro h
      have h1 : I * J' ∣ 1 * J' := by rw [one_mul]; exact Ideal.dvd_iff_le.2 h
      rw [mul_dvd_mul_iff_right hJ', Ideal.one_eq_top] at h1
      exact hI.ne_top (eq_top_iff.2 (Ideal.dvd_iff_le.1 h1))
    obtain ⟨c, hc, hcn⟩ := Set.not_subset.1 hne
    refine ⟨c, fun a ha => ?_, fun x hx => ?_⟩
    · rw [mul_comm c a]; exact Ideal.mul_mem_mul ha hc
    · have hLJ' : Ideal.span {c} ⊔ I * J' ≤ J' :=
        sup_le (by rw [Ideal.span_le]; simpa using hc) (Ideal.mul_le_inf.trans inf_le_right)
      obtain ⟨L', hL'⟩ := Ideal.dvd_iff_le.2 hLJ'
      have hIL' : I ≤ L' := by
        have h2 : J' * L' ∣ J' * I := by
          rw [← hL', mul_comm J' I]; exact Ideal.dvd_iff_le.2 le_sup_right
        exact Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left hJ').1 h2)
      by_cases htop : L' = ⊤
      · rw [htop, Ideal.mul_top] at hL'
        have hxJ' : x ∈ J' := by
          have h3 : Ideal.span {x} * I ≤ J' * I := by
            rw [Ideal.span_singleton_mul_le_iff]
            intro z hz
            rw [mul_comm x z, mul_comm J' I]; exact hx z hz
          have := (mul_dvd_mul_iff_right hI0).1 (Ideal.dvd_iff_le.2 h3)
          exact Ideal.dvd_iff_le.1 this (Ideal.mem_span_singleton_self x)
        rw [← hL', Ideal.mem_span_singleton_sup] at hxJ'
        obtain ⟨r, b, hb, hrb⟩ := hxJ'
        exact ⟨r, by rw [← hrb]; simpa using hb⟩
      · have hEq : L' = I := (hI.eq_of_le htop hIL').symm
        rw [hEq, mul_comm] at hL'
        exact (hcn (by rw [mul_comm I J', ← hL']; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self c))).elim
  · have hsup : I ⊔ J = ⊤ :=
      hI.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hle (h ▸ le_sup_right))
    refine ⟨0, fun a _ => by simp, fun x hx => ⟨0, ?_⟩⟩
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : R) ∈ I ⊔ J)
    have : x = u * x + x * v := by rw [mul_comm u, ← mul_add, huv, mul_one]
    rw [zero_mul, sub_zero, this]
    exact J.add_mem (hx u hu) (J.mul_mem_left x hv)

variable {M : Type} [AddCommGroup M] [Module R M]

omit [IsDedekindDomain R] in
theorem map_mem_of_mem_smul_top {S : Type} [CommRing S] {N : Type} [AddCommGroup N] [Module S N]
    (J : Ideal S) (φ : N →ₗ[S] S) {z : N} (hz : z ∈ J • (⊤ : Submodule S N)) : φ z ∈ J := by
  exact Submodule.smul_induction_on hz (fun a ha n _ => by
      rw [map_smul, smul_eq_mul]; exact J.mul_mem_right _ ha)
    (fun x y hx hy => by rw [map_add]; exact J.add_mem hx hy)

omit [IsDedekindDomain R] in
theorem mem_range_of_torsion [Module.Finite R M] [Module.Projective R M] (I J : Ideal R) (c : R)
    (hc : ∀ x : R, (∀ a ∈ I, a * x ∈ J) → ∃ r : R, x - r * c ∈ J)
    (y : M ⧸ J • (⊤ : Submodule R M)) (hy : ∀ a ∈ I, a • y = 0) :
    ∃ m : M, Submodule.Quotient.mk (c • m) = y := by
  obtain ⟨m0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨n, g, f, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hcoord : ∀ j, ∃ r : R, f m0 j - r * c ∈ J := by
    intro j
    refine hc _ fun a ha => ?_
    have h1 : a • m0 ∈ J • (⊤ : Submodule R M) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]; exact hy a ha
    have h2 := map_mem_of_mem_smul_top J ((LinearMap.proj j) ∘ₗ f) h1
    simpa using h2
  choose r hr using hcoord
  refine ⟨g r, (Submodule.Quotient.eq _).2 ?_⟩
  have hm0 : m0 = g (f m0) := by
    have := congrArg (fun φ => φ m0) hfg; simpa using this.symm
  have hdec : f m0 - c • r = ∑ j, (f m0 j - r j * c) • Pi.single j (1 : R) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  have : c • g r - m0 = -(g (f m0 - c • r)) := by
    rw [map_sub, map_smul, ← hm0]; abel
  rw [this]
  refine Submodule.neg_mem _ ?_
  rw [hdec, map_sum]
  exact Submodule.sum_mem _ fun j _ => by
    rw [map_smul]; exact Submodule.smul_mem_smul (hr j) trivial

theorem card_quot_smul_top [Module.Finite R M] [Module.Projective R M] (I : Ideal R) [I.IsMaximal]
    [Finite (R ⧸ I)] : Finite (M ⧸ I • (⊤ : Submodule R M)) ∧
      Nat.card (M ⧸ I • (⊤ : Submodule R M)) = Nat.card (R ⧸ I) ^ Module.finrank R M := by
  let ek : (R ⧸ I) ≃ₐ[R] I.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ I) I.ResidueField)
      I.bijective_algebraMap_quotient_residueField
  let e : (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] I.ResidueField ⊗[R] M :=
    (TensorProduct.quotTensorEquivQuotSMul M I).symm ≪≫ₗ
      TensorProduct.congr ek.toLinearEquiv (LinearEquiv.refl R M)
  haveI : Finite I.ResidueField := Finite.of_equiv _ ek.toEquiv
  haveI : Finite (I.ResidueField ⊗[R] M) := Module.finite_of_finite I.ResidueField
  have hr : Module.finrank I.ResidueField (I.ResidueField ⊗[R] M) = Module.finrank R M :=
    Ideal.finrank_fiber_eq_finrank I
  refine ⟨Finite.of_equiv _ e.toEquiv.symm, ?_⟩
  rw [Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := I.ResidueField), hr,
    Nat.card_congr ek.toEquiv]

theorem torsion_card : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] (I J : Ideal R), I.IsMaximal →
    Finite (R ⧸ I) → J ≠ ⊥ → Finite {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} ∧
      Nat.card {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} ≤
        Nat.card (R ⧸ I) ^ Module.finrank R M := by
  intro R _ _ M _ _ _ _ I J hI hfin hJ
  obtain ⟨c, hcI, hc⟩ := exists_colon_gen I J hI hJ
  let f : M →ₗ[R] M ⧸ J • (⊤ : Submodule R M) :=
    (J • (⊤ : Submodule R M)).mkQ ∘ₗ (LinearMap.lsmul R M c)
  have hfI : I • (⊤ : Submodule R M) ≤ LinearMap.ker f := by
    rw [Submodule.smul_le]
    intro a ha m _
    rw [LinearMap.mem_ker]
    simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearMap.lsmul_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_smul]
    exact Submodule.smul_mem_smul (hcI a ha) trivial
  let g := (I • (⊤ : Submodule R M)).liftQ f hfI
  have hgT : ∀ z, ∀ a ∈ I, a • g z = 0 := by
    intro z a ha
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    simp only [g, Submodule.liftQ_apply, f, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lsmul_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, smul_smul]
    rw [mul_comm]
    exact Submodule.smul_mem_smul (hcI a ha) trivial
  let h : (M ⧸ I • (⊤ : Submodule R M)) →
      {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} := fun z => ⟨g z, hgT z⟩
  have hsurj : Function.Surjective h := by
    rintro ⟨y, hy⟩
    obtain ⟨m, hm⟩ := mem_range_of_torsion I J c hc y hy
    exact ⟨Submodule.Quotient.mk m, Subtype.ext (by simpa [h, g, f] using hm)⟩
  obtain ⟨hQ, hcard⟩ := card_quot_smul_top (M := M) I
  exact ⟨Finite.of_surjective h hsurj, (Nat.card_le_card_of_surjective h hsurj).trans hcard.le⟩

end GlobalTheory.TorsionCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatSurjectiveClosedSubschemeOfOpenCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isPullback_of_factor_iff {C : Type*} [Category C] {X X' A B : C} (m : X' ⟶ X)
    (b : B ⟶ X) (a : A ⟶ X') [Mono a] [Mono b]
    (h : ∀ (Y : C) (g : Y ⟶ X'), (∃ z : Y ⟶ B, z ≫ b = g ≫ m) ↔ (∃ z : Y ⟶ A, z ≫ a = g)) :
    ∃ k : A ⟶ B, IsPullback k a b m := by
  obtain ⟨k, hk⟩ := (h A a).2 ⟨𝟙 A, Category.id_comp a⟩
  refine ⟨k, ⟨hk⟩, ⟨PullbackCone.IsLimit.mk hk
    (fun s => ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose) ?_ ?_ ?_⟩⟩
  · intro s
    have hs := ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
    rw [← cancel_mono b, Category.assoc, hk, ← Category.assoc, hs, s.condition]
  · intro s
    exact ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
  · intro s l _ hl
    have hs := ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
    rw [← cancel_mono a, hl, hs]

theorem of_isPullback_openCover (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    {B T : Scheme.{0}} (f : B ⟶ T) {ι : Type} (V : ι → T.Opens) (hV : iSup V = ⊤)
    (A : ι → Scheme.{0}) (k : ∀ i, A i ⟶ B) (g : ∀ i, A i ⟶ (V i).toScheme)
    (h : ∀ i, IsPullback (k i) (g i) f (V i).ι) (hg : ∀ i, P (g i)) : P f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) V hV]
  intro i
  have h' := (isPullback_morphismRestrict f (V i)).flip
  have e : (h'.isoIsPullback _ _ (h i)).hom ≫ g i = f ∣_ V i := by simp
  rw [← e]
  exact (P.cancel_left_of_respectsIso _ _).2 (hg i)

set_option backward.isDefEq.respectTransparency.types false in

theorem finite_flat_surjective_of_openCover : ∀ (X T₀ : Scheme.{0}) (p : X ⟶ T₀) (ι : Type) (V : ι → T₀.Opens), iSup V = ⊤ → ∀ (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X) (q : ∀ i, Xi i ⟶ (V i).toScheme), (∀ i, IsPullback (m i) (q i) p (V i).ι) → ∀ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), (∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) → (∀ i, IsFinite (a i ≫ q i) ∧ Flat (a i ≫ q i) ∧ Surjective (a i ≫ q i)) → IsFinite (b ≫ p) ∧ Flat (b ≫ p) ∧ Surjective (b ≫ p) := by
  intro X T₀ p ι V hV Xi m q hpb B b hb A a ha hrep hP
  have H : ∀ i, ∃ k : A i ⟶ B, IsPullback k (a i ≫ q i) (b ≫ p) (V i).ι := by
    intro i
    have := ha i
    obtain ⟨k, hk⟩ := exists_isPullback_of_factor_iff (m i) b (a i) (hrep i)
    exact ⟨k, hk.paste_vert (hpb i)⟩
  choose k hk using H
  have hfin : IsZariskiLocalAtTarget @IsFinite.{0} :=
    inferInstance
  have hflat : IsZariskiLocalAtTarget @Flat.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  exact ⟨of_isPullback_openCover @IsFinite _ V hV A k _ hk (fun i => (hP i).1),
    of_isPullback_openCover @Flat _ V hV A k _ hk (fun i => (hP i).2.1),
    of_isPullback_openCover @Surjective _ V hV A k _ hk (fun i => (hP i).2.2)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteJointEigensystems
section
open Matrix

namespace GlobalTheory

theorem finite_joint_eigensystems : ∀ (K : Type) [Field K] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K), (∀ i j, Commute (A i) (A j)) → Set.Finite {χ : ι → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, A i *ᵥ c = χ i • c} := by
  intro K _ n ι A hc
  let f : ι → Module.End K (Fin n → K) := fun i => Matrix.toLin' (A i)
  have hcf : ∀ i j, Commute (f i) (f j) := by
    intro i j
    exact (hc i j).map Matrix.toLinAlgEquiv'
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcf j i) φ)
  refine (WellFoundedGT.finite_ne_bot_of_iSupIndep hind).subset ?_
  rintro χ ⟨c, hc0, hχ⟩
  show (⨅ i, (f i).maxGenEigenspace (χ i)) ≠ ⊥
  intro hbot
  apply hc0
  have hmem : c ∈ ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [Submodule.mem_iInf]
    intro i
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    simpa [f] using hχ i
  rw [hbot] at hmem
  exact (Submodule.mem_bot K).mp hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLeftOfFiniteTensorProductComplex
section
open scoped TensorProduct

namespace GlobalTheory

open scoped TensorProduct in
private lemma trace_eq_zero_of_not_finite' {V : Type} [AddCommGroup V] [Module ℂ V]
    (h : ¬ Module.Finite ℂ V) (f : V →ₗ[ℂ] V) : LinearMap.trace ℂ V f = 0 := by
  have hb : ¬ ∃ s : Finset V, Nonempty (Module.Basis s ℂ V) := by
    rintro ⟨s, ⟨b⟩⟩
    exact h (Module.Finite.of_basis b)
  simp [LinearMap.trace, hb]

open scoped TensorProduct in
private lemma finite_left_of_finite_tensor_of_nontrivial {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial W] [Module.Finite ℂ (V ⊗[ℂ] W)] :
    Module.Finite ℂ V := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
    by_contra! h
    exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).mp h)
  let p : V ⊗[ℂ] W →ₗ[ℂ] V :=
    (TensorProduct.rid ℂ V).toLinearMap ∘ₗ TensorProduct.map LinearMap.id φ
  refine Module.Finite.of_surjective p fun v => ⟨v ⊗ₜ ((φ w)⁻¹ • w), ?_⟩
  simp [p, hφ]

open scoped TensorProduct in
private lemma finite_right_of_finite_tensor_of_nontrivial {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial V] [Module.Finite ℂ (V ⊗[ℂ] W)] :
    Module.Finite ℂ W := by
  have : Module.Finite ℂ (W ⊗[ℂ] V) :=
    Module.Finite.equiv (TensorProduct.comm ℂ V W)
  exact finite_left_of_finite_tensor_of_nontrivial (W := V)

open scoped TensorProduct in

theorem _root_.GlobalTheory.trace_tensorProduct_map_complex {U U' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] (T : U →ₗ[ℂ] U) (T' : U' →ₗ[ℂ] U') :
    LinearMap.trace ℂ (U ⊗[ℂ] U') (TensorProduct.map T T') =
      LinearMap.trace ℂ U T * LinearMap.trace ℂ U' T' := by
  by_cases hU : Module.Finite ℂ U
  · by_cases hU' : Module.Finite ℂ U'
    · exact LinearMap.trace_tensorProduct' T T'
    · rw [trace_eq_zero_of_not_finite' hU' T', mul_zero]
      by_cases hUU : Module.Finite ℂ (U ⊗[ℂ] U')
      · rcases subsingleton_or_nontrivial U with hs | hs
        · rw [Subsingleton.elim T 0, TensorProduct.map_zero_left, map_zero]
        · exact absurd (finite_right_of_finite_tensor_of_nontrivial (V := U)) hU'
      · exact trace_eq_zero_of_not_finite' hUU _
  · rw [trace_eq_zero_of_not_finite' hU T, zero_mul]
    by_cases hUU : Module.Finite ℂ (U ⊗[ℂ] U')
    · rcases subsingleton_or_nontrivial U' with hs | hs
      · rw [Subsingleton.elim T' 0, TensorProduct.map_zero_right, map_zero]
      · exact absurd (finite_left_of_finite_tensor_of_nontrivial (W := U')) hU
    · exact trace_eq_zero_of_not_finite' hUU _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdjoinRootOfSeparable
section
namespace GlobalTheory.ReducedAdjoinRootSeparable

theorem isReduced_adjoinRoot_of_separable {k : Type} [Field k] {f : Polynomial k}
    (hf : f.Separable) : IsReduced (AdjoinRoot f) := by
  have h1 : IsRadical f := isRadical_iff_squarefree_or_zero.2 (Or.inl hf.squarefree)
  have h2 : (Ideal.span {f}).IsRadical := isRadical_iff_span_singleton.1 h1
  exact (Ideal.isRadical_iff_quotient_reduced _).1 h2

end GlobalTheory.ReducedAdjoinRootSeparable
end

