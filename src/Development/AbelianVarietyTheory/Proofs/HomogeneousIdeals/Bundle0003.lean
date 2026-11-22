import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
section
open TensorProduct

universe u

namespace GlobalTheory

theorem isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization {B : Type*} [CommRing B]
    (M : Submonoid B) (T : Type*) [CommRing T] [Algebra B T] [IsLocalization M T]
    (p : Ideal B) [hp : p.IsPrime] (hM : Disjoint (M : Set B) (p : Set B))
    (h : ∀ (q : Ideal T) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  have hq : (p.map (algebraMap B T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M T p hp hM
  have hc : (p.map (algebraMap B T)).comap (algebraMap B T) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint M T hp hM
  have h1 := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime (p.map (algebraMap B T))) (p.map (algebraMap B T))
  have h2 : IsLocalization p.primeCompl (Localization.AtPrime (p.map (algebraMap B T))) := by
    convert h1 using 1
    ext x
    simp [Ideal.primeCompl, hc]
  obtain ⟨h3, h4⟩ := h (p.map (algebraMap B T))
  let e : Localization.AtPrime (p.map (algebraMap B T)) ≃ₐ[B] Bp :=
    IsLocalization.algEquiv p.primeCompl _ _
  exact ⟨e.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

theorem isDomain_and_isIntegrallyClosed_atPrime_of_isDomain {B : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp :=
  ⟨IsLocalization.isDomain_of_le_nonZeroDivisors Bp p.primeCompl_le_nonZeroDivisors,
    isIntegrallyClosed_of_isLocalization Bp p.primeCompl p.primeCompl_le_nonZeroDivisors⟩

theorem isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi {B : Type*} [CommRing B]
    {ι : Type*} [Finite ι] (K : ι → Type*) [∀ i, Field (K i)] [Algebra B (Π i, K i)]
    [hB : IsIntegrallyClosedIn B (Π i, K i)] (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  classical
  have := Fintype.ofFinite ι
  have hinj : Function.Injective (algebraMap B (Π i, K i)) := (isIntegrallyClosedIn_iff.mp hB).1
  let φ (i : ι) : B →+* K i := (Pi.evalRingHom K i).comp (algebraMap B (Π i, K i))
  have key (i : ι) (x : K i) (hx : (φ i).IsIntegralElem x) :
      ∃ b : B, algebraMap B (Π i, K i) b = Pi.single i x := by
    apply IsIntegrallyClosedIn.algebraMap_eq_of_integral
    obtain ⟨f, hf, hfx⟩ := hx
    refine ⟨Polynomial.X * f, Polynomial.monic_X.mul hf, ?_⟩
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_X]
    funext j
    by_cases hj : j = i
    · subst hj
      have : (Polynomial.eval₂ (algebraMap B (Π i, K i)) (Pi.single j x) f) j = 0 := by
        have := Polynomial.hom_eval₂ f (algebraMap B (Π i, K i)) (Pi.evalRingHom K j)
          (Pi.single j x)
        simpa [φ] using this.trans (by simpa [φ] using hfx)
      simp [this]
    · simp [hj]
  choose e he using fun i ↦ key i 1 (RingHom.isIntegralElem_one _)
  have hsum : ∑ i, e i = 1 := by
    apply hinj
    simp [he, Finset.univ_sum_single, ← Pi.one_def]
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ p := by
    by_contra! H
    exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr (hsum ▸ p.sum_mem fun i _ ↦ H i))
  let D := (φ i).range
  letI : Algebra B D := (φ i).rangeRestrict.toAlgebra
  have hsurj : Function.Surjective (algebraMap B D) := (φ i).rangeRestrict_surjective
  have hidem : IsIdempotentElem (e i) := by
    apply hinj
    simp [he, ← Pi.single_mul]
  have : IsLocalization.Away (e i) D := by
    refine IsLocalization.away_of_isIdempotentElem_of_mul hidem (fun x y ↦ ?_) hsurj
    rw [Subtype.ext_iff, ← hinj.eq_iff, map_mul, map_mul, he]
    change algebraMap B (Π i, K i) x i = algebraMap B (Π i, K i) y i ↔ _
    refine ⟨fun h ↦ funext fun j ↦ ?_, fun h ↦ by simpa using congrFun h i⟩
    by_cases hj : j = i
    · subst hj
      simp [h]
    · simp [hj]
  have : IsIntegrallyClosedIn D (K i) := by
    rw [Subring.isIntegrallyClosedIn_iff]
    intro x hx
    letI : Algebra B (K i) := (φ i).toAlgebra
    have : IsScalarTower B D (K i) := .of_algebraMap_eq fun _ ↦ rfl
    have : Algebra.IsIntegral B D := Algebra.isIntegral_of_surjective hsurj
    obtain ⟨b, hb⟩ := key i x (isIntegral_trans x hx)
    exact ⟨b, by simp [φ, hb]⟩
  have : IsIntegrallyClosed D := IsIntegrallyClosed.of_isIntegrallyClosedIn D (K i)
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers (e i)) D p ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_isDomain q _) Bp
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

theorem isIntegrallyClosedIn_tensor_of_smooth {A B L : Type*} [CommRing A] [CommRing B]
    [CommRing L] [Algebra A B] [Algebra A L] [Algebra.Smooth A B] [hL : IsIntegrallyClosedIn A L] :
    IsIntegrallyClosedIn B (B ⊗[A] L) := by
  obtain ⟨hinj, hcl⟩ := isIntegrallyClosedIn_iff.mp hL
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, fun {x} hx ↦ ?_⟩
  · exact Algebra.TensorProduct.includeLeft_injective (S := A) hinj
  · obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := A) (S := B) (B := L)).2 ⟨x, hx⟩
    have hy' : Algebra.TensorProduct.map (.id B B) (integralClosure A L).val y = x :=
      congrArg Subtype.val hy
    subst hy'
    clear hx hy
    induction y with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
    | tmul b y =>
      obtain ⟨a, ha⟩ := hcl y.2
      refine ⟨a • b, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.algebraMap_apply,
        Subalgebra.coe_val, ← ha, Algebra.algebraMap_eq_smul_one a, ← TensorProduct.smul_tmul]
      rfl

theorem isIntegrallyClosed_mvPolynomial_fin (A : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) A) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv A (Fin 0)).symm
  | succ n ih => exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv A n).symm.toRingEquiv

theorem isDomain_and_isIntegrallyClosed_atPrime_of_etale (A : Type*) {B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Etale A B]
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  let L := FractionRing A
  have h1 : IsIntegrallyClosedIn B (B ⊗[A] L) := isIntegrallyClosedIn_tensor_of_smooth
  have := Algebra.FormallyUnramified.finite_of_free L (L ⊗[A] B)
  have := Algebra.FormallyUnramified.isReduced_of_field L (L ⊗[A] B)
  have : IsArtinianRing (L ⊗[A] B) := isArtinian_of_tower L inferInstance
  let e := (Algebra.TensorProduct.comm A B L).toRingEquiv
  have : IsArtinianRing (B ⊗[A] L) := e.symm.isArtinianRing
  have : IsReduced (B ⊗[A] L) := isReduced_of_injective e e.injective
  letI (m : MaximalSpectrum (B ⊗[A] L)) : Field ((B ⊗[A] L) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  have := (((IsArtinianRing.equivPi (B ⊗[A] L)).restrictScalars B).isIntegrallyClosedIn).mp h1
  exact isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi
    (fun m : MaximalSpectrum (B ⊗[A] L) ↦ (B ⊗[A] L) ⧸ m.asIdeal) p Bp

theorem isDomain_and_isIntegrallyClosed_atPrime_of_smooth (A : Type*) {B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B]
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  obtain ⟨f, hfm, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := p)
  have := isIntegrallyClosed_mvPolynomial_fin A n
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers f)
    (Localization.Away f) p ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_etale (MvPolynomial (Fin n) A) q _) Bp
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

theorem isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.Smooth A B] (p : Ideal B) [hp : p.IsPrime]
    (Ap : Type*) [CommRing Ap] [Algebra A Ap]
    [IsLocalization.AtPrime Ap (p.comap (algebraMap A B))] [IsDomain Ap] [IsIntegrallyClosed Ap]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  let M := (p.comap (algebraMap A B)).primeCompl
  letI : Algebra B (Ap ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B M) (Ap ⊗[A] B) :=
    IsLocalization.tensorRight _ _
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization
    (Algebra.algebraMapSubmonoid B M) (Ap ⊗[A] B) p ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_smooth Ap q _) Bp
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ h
  exact ha h

theorem isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_forall (A : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (hA : ∀ (q : Ideal A) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  obtain ⟨_, _⟩ := hA (p.comap (algebraMap A B))
  exact isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap (A := A) p
    (Localization.AtPrime (p.comap (algebraMap A B))) Bp

theorem isIntegrallyClosed_of_smooth (A B : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B] [IsDomain B] :
    IsIntegrallyClosed B :=
  IsIntegrallyClosed.of_localization_maximal fun p _ _ ↦
    (isDomain_and_isIntegrallyClosed_atPrime_of_smooth A p _).2

theorem isReduced_of_smooth_of_isIntegrallyClosed (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B] : IsReduced B :=
  isReduced_ofLocalizationMaximal B fun p _ ↦
    have := (isDomain_and_isIntegrallyClosed_atPrime_of_smooth A p (Localization.AtPrime p)).1
    inferInstance

open AlgebraicGeometry in

theorem isDomain_and_isIntegrallyClosed_stalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) [IsDomain (Y.presheaf.stalk (f x))] [IsIntegrallyClosed (Y.presheaf.stalk (f x))] :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hx, e, -⟩ := Smooth.exists_isStandardSmooth f x
  have hs := f.smooth_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  letI := Y.presheaf.algebra_section_stalk (⟨f x, e hx⟩ : U)
  have h1 := hV.isLocalization_stalk ⟨x, hx⟩
  have h2 := hU.isLocalization_stalk ⟨f x, e hx⟩
  have h3 : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V)) =
      (hU.primeIdealOf ⟨f x, e hx⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e hx)
  have h4 : IsLocalization.AtPrime (Y.presheaf.stalk (f x))
      ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V))) := by
    convert h2
  exact isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap (A := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

open AlgebraicGeometry in

theorem forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (x : X) : IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
  have := (hY (f x)).1
  have := (hY (f x)).2
  isDomain_and_isIntegrallyClosed_stalk_of_smooth f x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.PowLeComapMapPow
section
universe u_1 u_2

namespace GlobalTheory.PowerExtensionEvaluation

theorem pow_le_comap_map_pow {A : Type u_1} {B : Type u_2} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) (n : ℕ) : I ^ n ≤ ((I.map f) ^ n).comap f :=
  Ideal.map_le_iff_le_comap.mp (le_of_eq (Ideal.map_pow f I n))

theorem factorPow_evalₐ {A : Type u_1} [CommRing A] (I : Ideal A) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (I ^ m) (s.val n) = Ideal.Quotient.mk (I ^ m) (s.val m)
  rw [Ideal.Quotient.eq]
  have h := s.property hle
  rw [SModEq.sub_mem] at h
  have h2 : s.val m - s.val n ∈ I ^ m := by simpa [smul_eq_mul, Ideal.mul_top] using h
  have h3 := (I ^ m).neg_mem h2
  rwa [neg_sub] at h3

theorem exists_extension {A : Type u_1} {B : Type u_2} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) [IsAdicComplete (Ideal.map f I) B] :
    ∃ g : AdicCompletion I A →+* B, g.comp (algebraMap A (AdicCompletion I A)) = f := by
  let F : (n : ℕ) → AdicCompletion I A →+* B ⧸ (Ideal.map f I) ^ n := fun n =>
    (Ideal.quotientMap ((Ideal.map f I) ^ n) f (pow_le_comap_map_pow I f n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (Ideal.map f I) hle).comp (F n) = F m := by
    intro m n hle
    ext x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    have hm : AdicCompletion.evalₐ I m x = Ideal.Quotient.mk (I ^ m) a := by
      rw [← factorPow_evalₐ I hle x, ← ha]
      rfl
    change Ideal.Quotient.factorPow (Ideal.map f I) hle
        (Ideal.quotientMap _ f (pow_le_comap_map_pow I f n) (AdicCompletion.evalₐ I n x)) =
      Ideal.quotientMap _ f (pow_le_comap_map_pow I f m) (AdicCompletion.evalₐ I m x)
    rw [← ha, hm, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
    rfl
  refine ⟨IsAdicComplete.liftRingHom (Ideal.map f I) F hF, ?_⟩
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (Ideal.map f I)
  intro n a
  rw [RingHom.coe_comp, Function.comp_apply, IsAdicComplete.mk_liftRingHom]
  change Ideal.quotientMap _ f (pow_le_comap_map_pow I f n) (AdicCompletion.evalₐ I n (AdicCompletion.of I A a)) = _
  rw [AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

end GlobalTheory.PowerExtensionEvaluation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.RestrictScalarsMapEqSpan
section
universe u_1 u_2 u_3 u_4

namespace GlobalTheory.RestrictScalarsSpan

theorem mul_mem_span {K : Type u_1} {L : Type u_2} {A : Type u_3} {B : Type u_4} [Field K] [Field L]
    [Algebra K L] [Ring A] [Ring B] [Algebra K A] [Algebra K B] [Algebra L B]
    [IsScalarTower K L B] {j : A →ₐ[K] B} (h : IsBaseChange L (AlgHom.toLinearMap j))
    (I : Ideal A) (b x : B) (hx : x ∈ Submodule.span L ((j : A → B) '' (I : Set A))) :
    b * x ∈ Submodule.span L ((j : A → B) '' (I : Set A)) := by
  have key : ∀ a : A, j a * x ∈ Submodule.span L ((j : A → B) '' (I : Set A)) := by
    intro a
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact Submodule.subset_span ⟨a * i, I.mul_mem_left a hi, map_mul j a i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul l y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ l hy
  refine h.inductionOn b
    (motive := fun b => b * x ∈ Submodule.span L ((j : A → B) '' (I : Set A))) ?_ ?_ ?_ ?_
  · simp
  · exact key
  · intro l b hb
    rw [smul_mul_assoc]; exact Submodule.smul_mem _ l hb
  · intro b c hb hc
    rw [add_mul]; exact add_mem hb hc

theorem restrictScalars_map_eq_span {K : Type u_1} {L : Type u_2} {A : Type u_3} {B : Type u_4}
    [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A] [Algebra K B] [Algebra L B]
    [IsScalarTower K L B] {j : A →ₐ[K] B} (h : IsBaseChange L (AlgHom.toLinearMap j))
    (I : Ideal A) :
    Submodule.restrictScalars L (Ideal.map j I) =
      Submodule.span L ((⇑(AlgHom.toLinearMap j) : A → B) ''
        (↑(Submodule.restrictScalars K I) : Set A)) := by
  change _ = Submodule.span L ((j : A → B) '' (I : Set A))
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ Submodule.span B ((j : A → B) '' (I : Set A)) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul b y _ hy => exact mul_mem_span h I b y hy
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact Ideal.mem_map_of_mem j hi

end GlobalTheory.RestrictScalarsSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.StalkGenericPointSpecializesOfSpecializes
section
open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace GlobalTheory

section Generisation

variable {Z : Scheme.{u}} (η : Z) [IsDomain (Z.presheaf.stalk η)]

noncomputable def stalkGenericPoint : Z :=
  Z.fromSpecStalk η (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Z.presheaf.stalk η))

variable [IsDiscreteValuationRing (Z.presheaf.stalk η)]

end Generisation

section ResidueCharacteristic

end ResidueCharacteristic

section LocalSource

variable {Z : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]

variable {η ξ : Z} [IsDomain (Z.presheaf.stalk η)] [IsDiscreteValuationRing (Z.presheaf.stalk η)]

end LocalSource

section ThetaShiftProofs

open PowerSeries

theorem exists_algHom_powerSeries_apply_X_of_isAdicComplete {O : Type*} [CommRing O] (I : Ideal O)
    [h : IsAdicComplete I O] {π : O} (hπ : π ∈ I) : ∃ ev : O⟦X⟧ →ₐ[O] O, ev X = π := by
  let : WithIdeal O := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval π := WithIdeal.isTopologicallyNilpotent_of_mem hπ
  refine ⟨PowerSeries.aeval ha, ?_⟩
  rw [← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]

noncomputable def powerSeriesPrimeX (O : Type u) [CommRing O] [IsDomain O] :
    Spec (CommRingCat.of O⟦X⟧) :=
  (⟨Ideal.span {X}, span_X_isPrime⟩ : PrimeSpectrum O⟦X⟧)

@[simp]
theorem powerSeriesPrimeX_asIdeal (O : Type u) [CommRing O] [IsDomain O] :
    (powerSeriesPrimeX O).asIdeal = Ideal.span {(X : O⟦X⟧)} := rfl

variable {Z : Scheme.{u}} {η ξ : Z} [IsDomain (Z.presheaf.stalk η)]
  [IsDiscreteValuationRing (Z.presheaf.stalk η)]
  {O : Type u} [CommRing O] [IsDomain O] [IsLocalRing O]

end ThetaShiftProofs

section Model

open PowerSeries

end Model

end GlobalTheory
end

