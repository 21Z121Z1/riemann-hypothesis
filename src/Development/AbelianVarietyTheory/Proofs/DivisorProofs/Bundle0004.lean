import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorLiftOfMulEqP
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem annihilator_lift_of_mul_eq_p : ∀ (p : ℕ) (O : Type) [CommRing O] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), (p : k) = 0 → (p : Λ) ^ 2 = 0 → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], (∀ m : M, (p : Λ) • m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ ϖ z : O, ϖ * z - (p : O) ∈ Ideal.span {(p : O) ^ 2} → ∀ n : N, ((1 : k) ⊗ₜ[ℤ] ϖ) • n = 0 → n ∈ Ideal.span {a : k ⊗[ℤ] O | ((1 : k) ⊗ₜ[ℤ] ϖ) * a = 0} • (⊤ : Submodule (k ⊗[ℤ] O) N) := by
  intro p O _ Λ _ k _ π hpk hp2 M _ _ _ _ htor N _ _ f hf hker ϖ z hϖz n hn
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hϖz

  have hL : ∀ (c : Λ) (m : M), c • m = (c ⊗ₜ[ℤ] (1 : O)) • m := by
    intro c m
    rw [← smul_one_smul (Λ ⊗[ℤ] O) c m]
    congr 1
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

  have hp2M : ∀ m : M, ((p : Λ) ^ 2) • m = 0 := by intro m; rw [hp2, zero_smul]

  have hpz : ∀ m : M, (p : Λ) • m = ((1 : Λ) ⊗ₜ[ℤ] z) • ((1 : Λ) ⊗ₜ[ℤ] ϖ) • m := by
    intro m
    rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm z ϖ]
    have : ϖ * z = (p : O) + y * (p : O) ^ 2 := by linear_combination -hy
    rw [this, TensorProduct.tmul_add, add_smul]
    have h1 : ((1 : Λ) ⊗ₜ[ℤ] (p : O)) = ((p : Λ) ⊗ₜ[ℤ] (1 : O)) := by
      have e1 : (p : O) = p • (1 : O) := by simp
      have e2 : (p : Λ) = p • (1 : Λ) := by simp
      rw [e1, e2, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have h2 : ((1 : Λ) ⊗ₜ[ℤ] (y * (p : O) ^ 2)) = ((p : Λ) ^ 2) • ((1 : Λ) ⊗ₜ[ℤ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [show (y * (p : O) ^ 2) = ((p ^ 2 : ℕ) : ℤ) • y by push_cast; simp [zsmul_eq_mul]; ring]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      congr 1
      push_cast; simp [zsmul_eq_mul]
    rw [h1, h2, ← hL, smul_assoc, hp2M, add_zero]

  have hσp : ∀ m : M, f ((p : Λ) • m) = 0 := by
    intro m
    rw [hL, f.map_smulₛₗ]
    have : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((p : Λ) ⊗ₜ[ℤ] (1 : O)) = 0 := by
      simp [Algebra.TensorProduct.map_tmul, hpk]
    rw [this, zero_smul]
  have hf0 : ∀ m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M), f m = 0 := by
    intro m hm
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hm
    obtain ⟨b, -, rfl⟩ := hm
    exact hσp b
  have hσϖ : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((1 : Λ) ⊗ₜ[ℤ] ϖ) = (1 : k) ⊗ₜ[ℤ] ϖ := by
    simp [Algebra.TensorProduct.map_tmul]
  have hσz : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((1 : Λ) ⊗ₜ[ℤ] z) = (1 : k) ⊗ₜ[ℤ] z := by
    simp [Algebra.TensorProduct.map_tmul]
  obtain ⟨m, rfl⟩ := hf n
  have h1 : f (((1 : Λ) ⊗ₜ[ℤ] ϖ) • m) = 0 := by rw [f.map_smulₛₗ, hσϖ]; exact hn
  have h2 := hker _ h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨m', -, hm'⟩ := h2
  have h3 : ((1 : Λ) ⊗ₜ[ℤ] ϖ) • (m - ((1 : Λ) ⊗ₜ[ℤ] z) • m') = 0 := by
    rw [smul_sub, ← hm', smul_smul, mul_comm ((1 : Λ) ⊗ₜ[ℤ] ϖ), ← smul_smul, ← hpz, sub_self]
  have h4 : (p : Λ) • (m - ((1 : Λ) ⊗ₜ[ℤ] z) • m') = 0 := by
    rw [hpz, h3, smul_zero]
  have h5 := hf0 _ (htor _ h4)
  have hn' : f m = ((1 : k) ⊗ₜ[ℤ] z) • f m' := by
    rw [map_sub, f.map_smulₛₗ, hσz, sub_eq_zero] at h5; exact h5
  rw [hn']
  apply Submodule.smul_mem_smul _ Submodule.mem_top
  apply Ideal.subset_span
  show ((1 : k) ⊗ₜ[ℤ] ϖ) * ((1 : k) ⊗ₜ[ℤ] z) = 0
  have hw : ϖ * z = ((p : ℤ) • (1 + (p : O) * y)) := by rw [zsmul_eq_mul]; push_cast; linear_combination -hy
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hw, ← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
  push_cast
  rw [hpk, TensorProduct.zero_tmul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLEInjectiveOfGenericPointMap
section
open CategoryTheory AlgebraicGeometry
namespace GlobalTheory

theorem appLE_injective_of_genericPoint_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (π : Y ⟶ X) (hπ : π (genericPoint Y) = genericPoint X) {U : X.Opens} {V : Y.Opens}
    (hV : (V : Set Y).Nonempty) (h : V ≤ π ⁻¹ᵁ U) :
    Function.Injective (π.appLE U V h).hom := by
  have hy : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have hxU : π (genericPoint Y) ∈ U := h hy
  have hF : IsField (X.presheaf.stalk (π (genericPoint Y))) :=
    isField_stalk_of_closure_mem_irreducibleComponents X _
      (by rw [hπ]; simp [irreducibleComponents_eq_singleton])
  letI := hF.toField
  have key : ∀ s, (π.stalkMap (genericPoint Y)).hom (X.presheaf.germ U _ hxU s) =
      Y.presheaf.germ V (genericPoint Y) hy ((π.appLE U V h).hom s) := by
    intro s
    rw [Scheme.Hom.germ_stalkMap_apply]
    simp [Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]
  intro s t hst
  apply germ_injective_of_isIntegral X _ hxU
  apply (π.stalkMap (genericPoint Y)).hom.injective
  rw [key, key, hst]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxStep
section
namespace GlobalTheory.FixedPointApproximation

noncomputable def approx {B : Type} [CommRing B] (q : B) (σ : B →+* B) (w : B) : ℕ → B
  | 0 => 0
  | n + 1 => -w + q * σ (approx q σ w n)

theorem approx_step {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B) (n : ℕ) :
    q ^ n ∣ approx q σ w (n + 1) - approx q σ w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨σ t, ?_⟩
    have e : approx q σ w (n + 1 + 1) - approx q σ w (n + 1) =
        q * σ (approx q σ w (n + 1) - approx q σ w n) := by
      rw [map_sub]
      show -w + q * σ (approx q σ w (n + 1)) - (-w + q * σ (approx q σ w n)) = _
      ring
    rw [e, ht, map_mul, map_pow, hq]
    ring

theorem approx_dvd {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B)
    (m n : ℕ) (h : m ≤ n) : q ^ m ∣ approx q σ w m - approx q σ w n := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have h2 : q ^ m ∣ approx q σ w (n + 1) - approx q σ w n :=
      (pow_dvd_pow q hmn).trans (approx_step q σ hq w n)
    have e : approx q σ w m - approx q σ w (n + 1) =
        (approx q σ w m - approx q σ w n) - (approx q σ w (n + 1) - approx q σ w n) := by ring
    rw [e]
    exact dvd_sub ih h2

theorem smodEq_iff {B : Type} [CommRing B] (q : B) (n : ℕ) (x y : B) :
    x ≡ y [SMOD ((Ideal.span {q}) ^ n • ⊤ : Submodule B B)] ↔ q ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem exists_fixed {B : Type} [inst : CommRing B] (q : B)
    [h : IsAdicComplete (Ideal.span {q}) B] (σ : B →+* B) (hq : σ q = q) (w : B) :
    ∃ c : B, c = -w + q * σ c := by
  obtain ⟨c, hc⟩ := h.toIsPrecomplete.prec (f := approx q σ w) fun {m n} hmn =>
    (smodEq_iff q m _ _).mpr (approx_dvd q σ hq w m n hmn)
  refine ⟨c, ?_⟩
  have hd : ∀ n, q ^ n ∣ c - (-w + q * σ c) := by
    intro n
    have h1 : q ^ n ∣ approx q σ w n - c := (smodEq_iff q n _ _).mp (hc n)
    have h2 : q ^ (n + 1) ∣ approx q σ w (n + 1) - c := (smodEq_iff q (n + 1) _ _).mp (hc (n + 1))
    obtain ⟨t, ht⟩ := h1
    have e : c - (-w + q * σ c) = -(approx q σ w (n + 1) - c) + q * σ (approx q σ w n - c) := by
      rw [map_sub]
      show _ = -((-w + q * σ (approx q σ w n)) - c) + q * (σ (approx q σ w n) - σ c)
      ring
    rw [e, ht, map_mul, map_pow, hq]
    exact dvd_add (dvd_neg.mpr ((pow_dvd_pow q (Nat.le_succ n)).trans h2)) ⟨q * σ t, by ring⟩
  have h0 := h.toIsHausdorff.haus (c - (-w + q * σ c)) fun n =>
    (smodEq_iff q n _ _).mpr (by simpa using hd n)
  exact sub_eq_zero.mp h0

end GlobalTheory.FixedPointApproximation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPrimeTensorIsDomainIsIntegrallyClosedFaithfulS
section
open IsLocalRing

namespace GlobalTheory

theorem atPrime_tensor_isDomain_isIntegrallyClosed_faithfulSMul : ∀ (R A : Type) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [FaithfulSMul R A] (p : Ideal R) [p.IsPrime], IsDomain (TensorProduct R (Localization.AtPrime p) A) ∧ IsIntegrallyClosed (TensorProduct R (Localization.AtPrime p) A) ∧ FaithfulSMul (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A) := by
  intro R A _ _ _ _ _ _ _ p _
  set Rp := Localization.AtPrime p
  set B := TensorProduct R Rp A
  letI : Algebra A B := Algebra.TensorProduct.rightAlgebra
  have hpush : Algebra.IsPushout R A Rp B := TensorProduct.isPushout'
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) B :=
    (Algebra.isLocalization_iff_isPushout p.primeCompl Rp).mpr hpush
  have hinj : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  have hle : Algebra.algebraMapSubmonoid A p.primeCompl ≤ nonZeroDivisors A := by
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    apply hr
    have : r = 0 := hinj (by simpa using h0)
    rw [this]; exact p.zero_mem
  haveI hdom : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hle
  refine ⟨hdom, isIntegrallyClosed_of_isLocalization B _ hle, ?_⟩
  have hAB : Function.Injective (algebraMap A B) := IsLocalization.injective B hle
  refine (faithfulSMul_iff_algebraMap_injective Rp B).mpr ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  have hcomp : ∀ r : R, algebraMap Rp B (algebraMap R Rp r) = algebraMap A B (algebraMap R A r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have h1 : algebraMap Rp B (algebraMap R Rp r) = 0 := by
    have := congrArg (algebraMap Rp B) (IsLocalization.mk'_spec Rp r s)
    rw [map_mul, hx, zero_mul] at this
    exact this.symm
  rw [hcomp] at h1
  have hr : r = 0 := hinj ((hAB (h1.trans (map_zero _).symm)).trans (map_zero _).symm)
  simp [hr]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayCongrModOfIsCoprime
section
theorem GlobalTheory.away_congr_of_isCoprime : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → (∀ c : C, ∃ a : A, c - algebraMap A C a ∈ Ideal.span {algebraMap A C g}) → ∀ c' : Localization.Away (algebraMap A C f), ∃ b : Localization.Away f, c' - Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} := by
  intro A C _ _ _ f g hfg hC c'
  obtain ⟨u, v, huv⟩ := hfg
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A C f)) c'
  obtain ⟨k, hk⟩ := s.2
  obtain ⟨a, ha⟩ := hC c
  refine ⟨algebraMap A (Localization.Away f) (a * u ^ k), ?_⟩
  have hmap : ∀ x : A, Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) x)
      = algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C x) :=
    fun x => IsLocalization.map_eq _ _
  rw [hmap, hmap]
  rw [Ideal.mem_span_singleton] at ha ⊢
  have hunit : IsUnit (algebraMap C (Localization.Away (algebraMap A C f)) (s : C)) :=
    IsLocalization.map_units _ s
  rw [← hunit.dvd_mul_right]
  have key : (IsLocalization.mk' (Localization.Away (algebraMap A C f)) c s
      - algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C (a * u ^ k)))
      * algebraMap C (Localization.Away (algebraMap A C f)) (s : C)
      = algebraMap C (Localization.Away (algebraMap A C f)) (c - algebraMap A C (a * (u * f) ^ k)) := by
    rw [sub_mul, IsLocalization.mk'_spec, ← hk]
    simp only [map_sub, map_mul, map_pow]
    ring
  rw [key]
  apply map_dvd
  have h1 : g ∣ a * (1 - (u * f) ^ k) := by
    have h2 : g ∣ 1 - u * f := ⟨v, by rw [← huv]; ring⟩
    have h3 : 1 - u * f ∣ 1 ^ k - (u * f) ^ k := sub_dvd_pow_sub_pow 1 (u * f) k
    rw [one_pow] at h3
    exact Dvd.dvd.mul_left (h2.trans h3) a
  have h4 := map_dvd (algebraMap A C) h1
  have : c - algebraMap A C (a * (u * f) ^ k) = (c - algebraMap A C a) + algebraMap A C (a * (1 - (u * f) ^ k)) := by
    simp only [map_sub, map_mul, map_pow, map_one]; ring
  rw [this]
  exact dvd_add ha h4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
section
noncomputable section

namespace GlobalTheory.AffineCurveNbhd

def IsNbhd (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) : Prop :=
  (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) ∧
  (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f})

theorem awayHom_isUnit {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A A'']
    (φ : A' →ₐ[A] A'') (f : A) :
    IsUnit (((algebraMap A'' (Localization.Away (algebraMap A A'' f))).comp φ.toRingHom) (algebraMap A A' f)) := by
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  exact IsLocalization.Away.algebraMap_isUnit _

def awayHom {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A A'']
    (φ : A' →ₐ[A] A'') (f : A) : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A'' f) :=
  Localization.awayLift ((algebraMap A'' _).comp φ.toRingHom) _ (awayHom_isUnit φ f)

theorem awayHom_comp_algebraMap {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) :
    (awayHom φ f).comp (algebraMap A' _) = (algebraMap A'' _).comp φ.toRingHom :=
  IsLocalization.Away.lift_comp _ (awayHom_isUnit φ f)

end GlobalTheory.AffineCurveNbhd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapBijectiveOfRangeEqSubalgebra
section
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

namespace GlobalTheory

theorem awayMap_bijective_of_range_eq_subalgebra :
    ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R B] (C : Subalgebra R B) (φ : A →+* B), Function.Injective φ → ∀ (_ : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B), φ a = b → (∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) → Function.Bijective (Localization.awayMap φ a) := by
  intro R A B _ _ _ _ C φ hφ hC a b hab hloc
  subst hab
  have hmem : ∀ y, φ y ∈ C := fun y => (hC _).2 ⟨y, rfl⟩
  let f : A →+* C := φ.codRestrict C.toSubsemiring hmem
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => hφ (congrArg Subtype.val h), fun c => ?_⟩
    obtain ⟨y, hy⟩ := (hC c.1).1 c.2
    exact ⟨y, Subtype.ext hy⟩
  let e : A ≃+* C := RingEquiv.ofBijective f hf
  have H : Submonoid.map e.toMonoidHom (Submonoid.powers a) = Submonoid.powers (f a) :=
    Submonoid.map_powers e.toMonoidHom a
  have h1 : Function.Bijective (Localization.awayMap f a) := by
    have hb := (IsLocalization.ringEquivOfRingEquiv (Localization.Away a)
      (Localization.Away (f a)) e H).bijective
    have key : ∀ z, Localization.awayMap f a z =
        IsLocalization.ringEquivOfRingEquiv (Localization.Away a) (Localization.Away (f a)) e H z := by
      intro z
      rw [IsLocalization.ringEquivOfRingEquiv_apply]
      rfl
    rw [show (Localization.awayMap f a : Localization.Away a → Localization.Away (f a)) = _ from funext key]
    exact hb
  have h2 : Localization.awayMap φ a =
      (Localization.awayMap C.val.toRingHom (f a)).comp (Localization.awayMap f a) := by
    simp only [Localization.awayMap, IsLocalization.Away.map]
    rw [IsLocalization.map_comp_map]
    rfl
  rw [h2]
  exact (hloc (hmem a)).comp h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapSpanSingletonDivisibilityDescends
section
namespace GlobalTheory

theorem awayMap_descends_divisibility : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), (∀ a : A, algebraMap A C a ∈ Ideal.span {algebraMap A C g} → a ∈ Ideal.span {g}) → ∀ b : Localization.Away f, Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} → b ∈ Ideal.span {algebraMap A (Localization.Away f) g} := by
  intro A C _ _ _ f g H b hb
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) b
  rw [Ideal.mem_span_singleton'] at hb
  obtain ⟨d, hd⟩ := hb
  obtain ⟨⟨c, ⟨_, m, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A C f)) d
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.map_eq] at hd
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq,
    IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap A C f))] at hd
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hd
  simp only [map_pow] at hn
  have key : algebraMap A C (f ^ (n + m) * a) ∈ Ideal.span {algebraMap A C g} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨algebraMap A C f ^ (n + k) * c, ?_⟩
    rw [map_mul, map_pow, pow_add, pow_add]
    linear_combination hn
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp (H _ key)
  rw [Ideal.mem_span_singleton']
  refine ⟨IsLocalization.mk' (Localization.Away f) e
    (⟨f ^ (n + m + k), n + m + k, rfl⟩ : Submonoid.powers f), ?_⟩
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq]
  congr 1
  simp only
  rw [pow_add, mul_comm g e, he]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaAlgEquivMatrixOfIdempotent
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

section Corner

variable {A : Type} [CommRing A] {Λ : Type} [Ring Λ] [Algebra A Λ]

noncomputable def leftIdealMulAlgHom (A : Type) [CommRing A] {Λ : Type} [Ring Λ] [Algebra A Λ]
    (e : Λ) : Λ →ₐ[A] Module.End A (LinearMap.range (LinearMap.mulRight A e)) where
  toFun l := (LinearMap.mulLeft A l).restrict (by
    rintro _ ⟨y, rfl⟩
    exact ⟨l * y, by simp [mul_assoc]⟩)
  map_one' := by ext p; simp [LinearMap.restrict_apply]
  map_mul' x y := by ext p; simp [LinearMap.restrict_apply, mul_assoc]
  map_zero' := by ext p; simp [LinearMap.restrict_apply]
  map_add' x y := by ext p; simp [LinearMap.restrict_apply, add_mul]
  commutes' c := by ext p; simp [LinearMap.restrict_apply, Algebra.smul_def]

theorem leftIdealMulAlgHom_apply_coe (e l : Λ) (p : LinearMap.range (LinearMap.mulRight A e)) :
    ((leftIdealMulAlgHom A e l p : LinearMap.range (LinearMap.mulRight A e)) : Λ) = l * p := rfl

theorem leftIdealMulAlgHom_injective (e : Λ)
    (h : ∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * e * b i = 1) :
    Function.Injective (leftIdealMulAlgHom A e) := by
  obtain ⟨N, a, b, hab⟩ := h
  rw [injective_iff_map_eq_zero]
  intro l hl
  have h0 : ∀ y : Λ, l * (y * e) = 0 := by
    intro y
    have := leftIdealMulAlgHom_apply_coe (A := A) e l ⟨y * e, y, rfl⟩
    rw [hl] at this
    simpa using this.symm
  calc l = l * ∑ i, a i * e * b i := by rw [hab, mul_one]
    _ = ∑ i, l * (a i * e) * b i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [mul_assoc]
    _ = 0 := by simp [h0]

theorem exists_mul_eq_mulLeftRight_of_corner (e : Λ)
    (hc : ∀ y : Λ, ∃ c : A, e * y * e = c • e) (t : Λ ⊗[A] Λᵐᵒᵖ) :
    ∃ l : Λ, ∀ y : Λ, AlgHom.mulLeftRight A Λ t (y * e) * e = l * (y * e) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, fun y => by simp⟩
  | tmul a b =>
    obtain ⟨c, hc⟩ := hc b.unop
    refine ⟨c • a, fun y => ?_⟩
    rw [AlgHom.mulLeftRight_apply]
    calc a * (y * e) * b.unop * e = a * y * (e * b.unop * e) := by simp only [mul_assoc]
      _ = c • a * (y * e) := by rw [hc]; simp [mul_assoc]
  | add s t hs ht =>
    obtain ⟨l, hl⟩ := hs
    obtain ⟨m, hm⟩ := ht
    exact ⟨l + m, fun y => by rw [map_add, LinearMap.add_apply, add_mul, hl, hm, add_mul]⟩

theorem leftIdealMulAlgHom_surjective [IsAzumaya A Λ] (e : Λ) (he : IsIdempotentElem e)
    (hc : ∀ y : Λ, ∃ c : A, e * y * e = c • e) :
    Function.Surjective (leftIdealMulAlgHom A e) := by
  intro f
  obtain ⟨t, ht⟩ := (IsAzumaya.bij (R := A) (A := Λ)).2
    ((LinearMap.range (LinearMap.mulRight A e)).subtype ∘ₗ f ∘ₗ
      (LinearMap.mulRight A e).rangeRestrict)
  obtain ⟨l, hl⟩ := exists_mul_eq_mulLeftRight_of_corner e hc t
  refine ⟨l, ?_⟩
  ext ⟨_, y, rfl⟩
  rw [leftIdealMulAlgHom_apply_coe]
  change l * (y * e) = _
  rw [← hl y, ht]
  have h1 : (LinearMap.mulRight A e).rangeRestrict (y * e)
      = ⟨LinearMap.mulRight A e y, y, rfl⟩ := by
    ext; simp [mul_assoc, he.eq]
  simp only [LinearMap.comp_apply, h1, Submodule.subtype_apply]
  obtain ⟨z, hz⟩ := (f ⟨LinearMap.mulRight A e y, y, rfl⟩).2
  rw [← hz]
  simp [mul_assoc, he.eq]

end Corner

theorem azumaya_algEquiv_matrix_of_idempotent :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ]
      [Module.Free A Λ] (n : ℕ), Module.finrank A Λ = n ^ 2 → ∀ e : Λ, IsIdempotentElem e →
      (∀ y : Λ, ∃ c : A, e * y * e = c • e) →
      (∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * e * b i = 1) →
      Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro A _ _ Λ _ _ _ _ n hn e he hc hs
  let P := LinearMap.range (LinearMap.mulRight A e)
  let φ : Λ ≃ₐ[A] Module.End A P := AlgEquiv.ofBijective (leftIdealMulAlgHom A e)
    ⟨leftIdealMulAlgHom_injective e hs, leftIdealMulAlgHom_surjective e he hc⟩
  haveI : Module.Projective A P :=
    Module.Projective.of_split P.subtype (LinearMap.mulRight A e).rangeRestrict (by
      ext ⟨_, y, rfl⟩
      simp [mul_assoc, he.eq])
  haveI : Module.Finite A P := Module.Finite.range _
  haveI : Module.Free A P := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank A P = n := by
    have h1 := φ.toLinearEquiv.finrank_eq
    rw [hn, Module.finrank_linearMap, ← sq] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  exact ⟨φ.trans (LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq A P hr))⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BandMono
section
universe u_1 u_2

namespace GlobalTheory.BandMonotonicity

theorem band_mono :
    (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop :=
      @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦
        ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k));
    ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ}
      {i j : ℕ} {X : Matrix ι ι k}, d1 ℓ j X → i ≤ j → d1 ℓ i X) := by
  intro d1 k _ ι _ _ ℓ i j X h hij r s hrs
  exact h r s (by omega)

end GlobalTheory.BandMonotonicity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEntriesIsCompact
section
namespace GlobalTheory.BoundedUnitsCompact

theorem boundedEntries_isCompact {F : Type} [NontriviallyNormedField F] [ProperSpace F] {n : ℕ}
    (M : ℝ) : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} := by
  have h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => Metric.closedBall (0 : F) M)) := by
    ext A
    constructor
    · intro hA i _ j _
      simpa using hA i j
    · intro hA i j
      simpa using hA i trivial j trivial
  rw [h]
  exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))

theorem isCompact_bounded_units {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] {n : ℕ} [ProperSpace F] (M : ℝ) :
    IsCompact {g : GL (Fin n) F | (∀ (i j : Fin n), ‖(↑g : Matrix (Fin n) (Fin n) F) i j‖ ≤ M) ∧
      ∀ (i j : Fin n), ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) F) i j‖ ≤ M} := by
  have hK1 := boundedEntries_isCompact (F := F) (n := n) M
  have hK : IsCompact ({A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} ×ˢ
      (MulOpposite.op '' {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M})) :=
    hK1.prod (hK1.image MulOpposite.continuous_op)
  have hce := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)
  convert hce.isCompact_preimage hK using 1
  ext g
  simp [Units.embedProduct, -MulOpposite.op_inv]

end GlobalTheory.BoundedUnitsCompact
end

