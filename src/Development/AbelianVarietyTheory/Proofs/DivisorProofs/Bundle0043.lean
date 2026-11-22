import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquarePresentationOfTower
section
open scoped TensorProduct

namespace GlobalTheory.SquareTower

open MvPolynomial

noncomputable def presOf {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {s : ℕ}
    (φ : MvPolynomial (Fin s) R →ₐ[R] S) (g : Fin s → MvPolynomial (Fin s) R)
    (hs : Function.Surjective φ) (hk : RingHom.ker φ = Ideal.span (Set.range g)) :
    Algebra.Presentation R S (Fin s) (Fin s) :=
  have he : MvPolynomial.aeval (fun i => φ (X i)) = φ := MvPolynomial.algHom_ext (fun i => aeval_X _ _)
  { toGenerators := Algebra.Generators.ofSurjective (fun i => φ (X i)) (by rw [he]; exact hs)
    relation := g
    span_range_relation_eq_ker := by
      rw [Algebra.Generators.ker_eq_ker_aeval_val, ← hk]
      change RingHom.ker φ = RingHom.ker (MvPolynomial.aeval (fun i => φ (X i)))
      rw [he] }

theorem square_of_pres {R T ι σ : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (P : Algebra.Presentation R T ι σ) (e : Fin n ≃ ι) (f : Fin n ≃ σ) :
    ∃ (s : ℕ) (φ : MvPolynomial (Fin s) R →ₐ[R] T) (g : Fin s → MvPolynomial (Fin s) R),
      Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g) := by
  let E : MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial ι R := renameEquiv R e
  refine ⟨n, (aeval P.val).comp E.toAlgHom, fun i => E.symm (P.relation (f i)), ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := P.toGenerators.algebraMap_surjective y
    refine ⟨E.symm x, ?_⟩
    show aeval P.val (E (E.symm x)) = y
    rw [E.apply_symm_apply, ← hx, Algebra.Generators.algebraMap_eq]
    rfl
  · have h1 : Set.range (fun i => E.symm (P.relation (f i))) = E.symm '' Set.range P.relation := by
      rw [← Set.range_comp]
      exact f.surjective.range_comp (⇑E.symm ∘ P.relation)
    rw [h1, ← Ideal.map_span, P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val]
    ext x
    rw [RingHom.mem_ker, Ideal.mem_map_of_equiv]
    constructor
    · intro hx
      refine ⟨E x, ?_, by simp⟩
      rw [RingHom.mem_ker]; simpa using hx
    · rintro ⟨y, hy, rfl⟩
      rw [RingHom.mem_ker] at hy
      simpa using hy

theorem tower : ∀ (k B A : Type) [CommRing k] [CommRing B] [CommRing A] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A], (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] B) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) B →ₐ[B] A) (g : Fin s → MvPolynomial (Fin s) B), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  intro k B A _ _ _ _ _ _ _
  rintro ⟨t, φ, g, hφ, hg⟩ ⟨d, ψ, h, hψ, hh⟩
  let P := presOf φ g hφ hg
  let Q := presOf ψ h hψ hh
  exact square_of_pres (Q.comp P) finSumFinEquiv.symm finSumFinEquiv.symm

end GlobalTheory.SquareTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkRetractionOfSmallLifting
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.SmallLift

theorem map_closedPoint {X : Scheme.{0}} {x : X} {R : CommRingCat.{0}} [IsLocalRing R]
    (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (closedPoint R) = x := by
  refine (Scheme.Hom.comp_apply (Spec.map φ) (X.fromSpecStalk x) (closedPoint R)).trans ?_
  exact (congrArg (X.fromSpecStalk x) (Spec_closedPoint (f := φ))).trans
    Scheme.fromSpecStalk_closedPoint

theorem step {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) (C : Type) [CommRing C] [IsLocalRing C]
    (I : Ideal C) [IsLocalRing (C ⧸ I)]
    (H : ∀ (a : Spec (CommRingCat.of (C ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of C) ⟶ Y),
      a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b →
      ∃ l : Spec (CommRingCat.of C) ⟶ X,
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b)
    (π : Y.presheaf.stalk (f x) ⟶ CommRingCat.of C)
    (ψ : X.presheaf.stalk x ⟶ CommRingCat.of (C ⧸ I)) [IsLocalHom ψ.hom]
    (hψ : ψ.hom.comp (f.stalkMap x).hom = (Ideal.Quotient.mk I).comp π.hom) :
    ∃ g : X.presheaf.stalk x →+* C, IsLocalHom g ∧ g.comp (f.stalkMap x).hom = π.hom := by
  have e : f.stalkMap x ≫ ψ =
      π ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    ext1
    exact hψ
  obtain ⟨l, hl, hs⟩ := H (Spec.map ψ ≫ X.fromSpecStalk x)
    (Spec.map π ≫ Y.fromSpecStalk (f x)) (by
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc,
        ← Spec.map_comp_assoc, e])
  obtain ⟨⟨x', φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of C)).symm.surjective l
  rw [SpecToEquivOfLocalRing_symm_apply] at hs hl
  dsimp only at hs hl
  have hmk : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk I)).hom :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hx : x' = x := by
    rw [← Spec.map_comp_assoc] at hl
    have : IsLocalHom (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)).hom :=
      @RingHom.isLocalHom_comp _ _ _ _ _ _ _ φ.hom hmk hφ
    have h1 := map_closedPoint (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I))
    rw [hl] at h1
    exact h1.symm.trans (map_closedPoint ψ)
  subst hx
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc] at hs
  have : Mono (Y.fromSpecStalk (f x')) :=
    SurjectiveOnStalks.mono_of_injective (Y.fromSpecStalk (f x')).isEmbedding.injective
  have key := Spec.map_injective ((cancel_mono _).1 hs)
  exact ⟨φ.hom, hφ, congrArg CommRingCat.Hom.hom key⟩

theorem pow_ne_top {A : Type} [CommRing A] [IsLocalRing A] (n : ℕ) :
    maximalIdeal A ^ (n + 1) ≠ ⊤ := fun h =>
  (maximalIdeal.isMaximal A).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self n.succ_ne_zero))

theorem isLocalRing_quot {A : Type} [CommRing A] [IsLocalRing A] (n : ℕ) :
    IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
  haveI := Ideal.Quotient.nontrivial_iff.2 (pow_ne_top (A := A) n)
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

theorem map_maximalIdeal_quot {A : Type} [CommRing A] [IsLocalRing A] (J : Ideal A)
    [IsLocalRing (A ⧸ J)] :
    (maximalIdeal A).map (Ideal.Quotient.mk J) = maximalIdeal (A ⧸ J) :=
  IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective

theorem isArtinianRing_quot {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    IsArtinianRing (A ⧸ maximalIdeal A ^ (n + 1)) := by
  haveI := isLocalRing_quot (A := A) n
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨n + 1, ?_⟩
  rw [← map_maximalIdeal_quot, ← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

theorem exists_retraction : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → ∀ (x : X) [IsNoetherianRing (Y.presheaf.stalk (f x))], Function.Surjective (f.residueFieldMap x).hom → ∀ n : ℕ, ∃ ψ : X.presheaf.stalk x →+* Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (n + 1), ψ.comp (f.stalkMap x).hom = Ideal.Quotient.mk _ := by
  intro X Y f H x _ hs n
  suffices h : ∃ ψ : X.presheaf.stalk x →+*
      Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (n + 1),
      IsLocalHom ψ ∧ ψ.comp (f.stalkMap x).hom = Ideal.Quotient.mk _ from
    let ⟨ψ, _, h⟩ := h; ⟨ψ, h⟩
  induction n with
  | zero =>
    let e : ResidueField (Y.presheaf.stalk (f x)) ≃+* ResidueField (X.presheaf.stalk x) :=
      RingEquiv.ofBijective (f.residueFieldMap x).hom ⟨(f.residueFieldMap x).hom.injective, hs⟩
    let q : (Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (0 + 1)) ≃+*
        ResidueField (Y.presheaf.stalk (f x)) :=
      Ideal.quotEquivOfEq (by rw [zero_add, pow_one])
    let r := (q.trans e).symm
    haveI := isLocalRing_quot (A := Y.presheaf.stalk (f x)) 0
    refine ⟨r.toRingHom.comp (residue _), ?_, ?_⟩
    · have : IsLocalHom r.toRingHom := IsLocalHom.of_surjective _ r.surjective
      infer_instance
    · ext a
      change r (residue _ ((f.stalkMap x).hom a)) = _
      rw [RingEquiv.symm_apply_eq]
      rfl
  | succ n ih =>
    obtain ⟨ψ, hψ, h⟩ := ih
    set A := Y.presheaf.stalk (f x) with hA
    haveI := isLocalRing_quot (A := A) n
    haveI := isLocalRing_quot (A := A) (n + 1)
    haveI := isArtinianRing_quot (A := A) (n + 1)
    have hle : maximalIdeal A ^ (n + 1 + 1) ≤ maximalIdeal A ^ (n + 1) :=
      Ideal.pow_le_pow_right (Nat.le_succ _)
    let I : Ideal (A ⧸ maximalIdeal A ^ (n + 1 + 1)) :=
      (maximalIdeal A ^ (n + 1)).map (Ideal.Quotient.mk _)
    let r : (A ⧸ maximalIdeal A ^ (n + 1)) ≃+* ((A ⧸ maximalIdeal A ^ (n + 1 + 1)) ⧸ I) :=
      (DoubleQuot.quotQuotEquivQuotOfLE hle).symm
    haveI : IsLocalRing ((A ⧸ maximalIdeal A ^ (n + 1 + 1)) ⧸ I) := r.isLocalRing
    have h1 : I ≤ maximalIdeal _ := by
      rw [← map_maximalIdeal_quot]
      exact Ideal.map_mono (Ideal.pow_le_self n.succ_ne_zero)
    have h2 : maximalIdeal _ * I = ⊥ := by
      rw [← map_maximalIdeal_quot, ← Ideal.map_mul, ← pow_succ', Ideal.map_quotient_self]
    have : IsLocalHom r.toRingHom := IsLocalHom.of_surjective _ r.surjective
    have hl : IsLocalHom (r.toRingHom.comp ψ) := inferInstance
    let π : A →+* A ⧸ maximalIdeal A ^ (n + 1 + 1) := Ideal.Quotient.mk _
    refine @step X Y f x _ _ _ I _ (H _ I h1 h2) (CommRingCat.ofHom π)
      (CommRingCat.ofHom (r.toRingHom.comp ψ)) hl ?_
    change (r.toRingHom.comp ψ).comp _ = _
    rw [RingHom.comp_assoc, h]
    ext a
    rfl

end GlobalTheory.SmallLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardBasisExtensionDetNeZero
section
open Module Submodule

namespace GlobalTheory

theorem extend_linearIndependent_rows_by_standard_basis
    {K : Type} [Field K] {J : Type} [Fintype J] {n : ℕ} (v : J → Fin n → K) :
    LinearIndependent K v → ∃ e : J → Fin n, Function.Injective e ∧
      (Matrix.of (Function.extend e v (fun i => Pi.single i (1 : K)))).det ≠ 0 := by
  intro hv
  set std : Fin n → (Fin n → K) := fun i => Pi.single i (1 : K) with hstd
  set W : Submodule K (Fin n → K) := span K (Set.range v) with hWdef
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (W.mkQ ∘ std)
  classical
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hW : finrank K W = Fintype.card J := finrank_span_eq_card hv
  have hQ := Submodule.finrank_quotient_add_finrank W
  have hfin : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hκ : Fintype.card κ ≤ finrank K ((Fin n → K) ⧸ W) := hli.fintype_card_le_finrank

  let C := {i : Fin n // i ∉ Set.range a}
  have hC : Fintype.card C = n - Fintype.card κ := by
    have h1 : Fintype.card C = Fintype.card (Fin n) - Fintype.card (Set.range a) := by
      simp only [C]
      rw [Fintype.card_subtype_compl]
    rw [h1, Fintype.card_fin, Set.card_range_of_injective ha]
  have hJC : Fintype.card J ≤ Fintype.card C := by omega
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hJC
  let e : J → Fin n := fun j => (φ j).1
  have he : Function.Injective e := fun x y h => φ.injective (Subtype.ext h)
  have heC : ∀ j, e j ∉ Set.range a := fun j => (φ j).2
  refine ⟨e, he, ?_⟩
  set f := Function.extend e v std with hf
  have hfe : ∀ j, f (e j) = v j := fun j => he.extend_apply v std j
  have hfa : ∀ k, f (a k) = std (a k) := by
    intro k
    apply Function.extend_apply'
    rintro ⟨j, hj⟩
    exact heC j ⟨k, hj.symm⟩

  have hstdspan : span K (Set.range std) = ⊤ := by
    have := (Pi.basisFun K (Fin n)).span_eq
    convert this using 2
    ext i
    simp [std, Pi.basisFun_apply]
  have hspanf : span K (Set.range f) = ⊤ := by
    have hWle : W ≤ span K (Set.range f) := by
      apply span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact subset_span ⟨e j, hfe j⟩
    have hAle : span K (Set.range (std ∘ a)) ≤ span K (Set.range f) := by
      apply span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact subset_span ⟨a k, hfa k⟩
    have htop : W ⊔ span K (Set.range (std ∘ a)) = ⊤ := by
      rw [← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
      have : (W.mkQ ∘ std ∘ a) = (W.mkQ ∘ std) ∘ a := rfl
      rw [← Function.comp_assoc] at *
      rw [hspan, Set.range_comp, ← Submodule.map_span, hstdspan, Submodule.map_top, LinearMap.range_eq_top]
      exact W.mkQ_surjective
    exact eq_top_iff.mpr (htop ▸ sup_le hWle hAle)
  have hlin : LinearIndependent K f := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanf, finrank_top, hfin,
      Fintype.card_fin]
  have hunit : IsUnit (Matrix.of f) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hlin
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStripFinitelyManyPrimeFactors
section
namespace GlobalTheory

theorem strip_prime_factors (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ}
    (π : Fin n → R) (J : Finset (Fin n)) (x : R) (hx : x ≠ 0) :
    ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧
      ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y := by
  induction J using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, x, by simp, by simp⟩
  | @insert j J hj ih =>
    obtain ⟨m, y, hxy, hy⟩ := ih
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hxy)
    by_cases hp : Prime (π j)
    · obtain ⟨y', hy', hnd⟩ :=
        (FiniteMultiplicity.of_not_isUnit hp.not_unit hy0).exists_eq_pow_mul_and_not_dvd
      refine ⟨Function.update m j (multiplicity (π j) y), y', ?_, ?_⟩
      · rw [Finset.prod_insert hj, Function.update_self]
        have hJ : ∏ i ∈ J, π i ^ Function.update m j (multiplicity (π j) y) i
            = ∏ i ∈ J, π i ^ m i := by
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
        rw [hJ, hxy]
        conv_lhs => rw [hy']
        ring
      · intro i hi hpi hdvd
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hnd hdvd
        · exact hy i hi hpi (hdvd.trans (Dvd.intro_left _ hy'.symm))
    · refine ⟨Function.update m j 0, y, ?_, ?_⟩
      · rw [Finset.prod_insert hj, Function.update_self, pow_zero, one_mul]
        rw [hxy]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
      · intro i hi hpi hdvd
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hp hpi
        · exact hy i hi hpi hdvd

theorem strip_prime_factors_target : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (x : R), x ≠ 0 → ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧ ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y :=
  fun R _ _ _ _ π J x hx => strip_prime_factors R π J x hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjLocalizationMvPolynomialOfEssFiniteTyp
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_surj_localization_mvPolynomial_of_essFiniteType :
    ∀ (Λ R : Type) [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R]
      [Algebra.EssFiniteType Λ R], ∃ (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) (_ : P.IsPrime)
      (φ : Localization.AtPrime P →ₐ[Λ] R), Function.Surjective φ := by
  intro Λ R _ _ _ _ h
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff Λ R).mp h
  let y : Fin σ.card → R := fun i => (σ.equivFin.symm i : R)
  let φ₀ : MvPolynomial (Fin σ.card) Λ →ₐ[Λ] R := MvPolynomial.aeval y
  have hrange : Algebra.adjoin Λ (σ : Set R) = φ₀.range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨σ.equivFin ⟨x, hx⟩, by simp [y]⟩
    · rintro ⟨i, rfl⟩
      exact (σ.equivFin.symm i).2
  let P : Ideal (MvPolynomial (Fin σ.card) Λ) := (maximalIdeal R).comap φ₀
  have hunit : ∀ b : P.primeCompl, IsUnit (φ₀ b) := by
    intro b
    by_contra hb
    exact b.2 ((mem_maximalIdeal _).mpr hb)
  refine ⟨σ.card, P, inferInstance, IsLocalization.liftAlgHom (M := P.primeCompl) (f := φ₀) hunit, ?_⟩
  intro r
  obtain ⟨t, ht, htu, hrt⟩ := hσ r
  rw [hrange] at ht hrt
  obtain ⟨b, rfl⟩ := ht
  obtain ⟨a, ha⟩ := hrt
  have hb : b ∈ P.primeCompl := fun hbP => (mem_maximalIdeal _).mp hbP htu
  refine ⟨IsLocalization.mk' (Localization.AtPrime P) a ⟨b, hb⟩, ?_⟩
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec]
  change φ₀ a = φ₀ b * r
  exact ha.trans (mul_comm _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjPiQuotPowKerEq
section
open scoped TensorProduct
open TensorProduct

namespace GlobalTheory

theorem exists_surj_pi_quot_pow_ker_eq {A M : Type} [CommRing A] [IsDedekindDomain A] [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Projective A M] (P : Ideal A) :
    P.IsMaximal → ∀ (r d : ℕ), Module.finrank A M = d →
      ∃ g : M →ₗ[A] (Fin d → A ⧸ P ^ r), Function.Surjective g ∧
        ∀ x, g x = 0 ↔ x ∈ (P ^ r) • (⊤ : Submodule A M) := by
  intro hP r d hd
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨0, ?_, ?_⟩
    · intro y
      refine ⟨0, ?_⟩
      funext i
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y i)
      rw [← ha]
      exact (Ideal.Quotient.eq_zero_iff_mem.2 (by simp)).symm
    · intro x
      simp
  haveI : P.IsPrime := hP.isPrime
  have hPr : P ^ r ≠ ⊤ := by
    intro h
    exact hP.ne_top (eq_top_iff.mpr (h ▸ Ideal.pow_le_self hr.ne'))
  haveI : Nontrivial (A ⧸ P ^ r) := Ideal.Quotient.nontrivial_iff.2 hPr
  let Ap := Localization.AtPrime P
  let φ : Ap →ₐ[A] A ⧸ P ^ r := IsLocalization.liftAlgHom (M := P.primeCompl)
    (f := Ideal.Quotient.mkₐ A (P ^ r)) fun u ↦
      Ideal.Quotient.isUnit_mk_pow_of_notMem _ (Ideal.mem_primeCompl_iff.mp u.prop)
  letI : Algebra Ap (A ⧸ P ^ r) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A Ap (A ⧸ P ^ r) := IsScalarTower.of_algebraMap_eq fun a ↦ (φ.commutes a).symm

  haveI : Module.Free Ap (Ap ⊗[A] M) := Module.free_of_flat_of_isLocalRing
  have hle := Ideal.primeCompl_le_nonZeroDivisors P
  have hAp : Module.finrank Ap (Ap ⊗[A] M) = d := by
    rw [IsLocalization.finrank_eq Ap P.primeCompl hle,
      IsLocalizedModule.finrank_eq P.primeCompl (TensorProduct.mk A Ap M 1) hle, hd]
  let e0 := TensorProduct.AlgebraTensorModule.cancelBaseChange A Ap (A ⧸ P ^ r) (A ⧸ P ^ r) M
  haveI : Module.Free (A ⧸ P ^ r) ((A ⧸ P ^ r) ⊗[A] M) := Module.Free.of_equiv e0
  haveI : Module.Finite (A ⧸ P ^ r) ((A ⧸ P ^ r) ⊗[A] M) := inferInstance
  have hB : Module.finrank (A ⧸ P ^ r) ((A ⧸ P ^ r) ⊗[A] M) = d := by
    rw [← e0.finrank_eq, Module.finrank_baseChange, hAp]
  let e : (A ⧸ P ^ r) ⊗[A] M ≃ₗ[A ⧸ P ^ r] (Fin d → A ⧸ P ^ r) :=
    (Module.finBasisOfFinrankEq _ _ hB).equivFun
  let g : M →ₗ[A] (Fin d → A ⧸ P ^ r) :=
    (e.restrictScalars A).toLinearMap ∘ₗ TensorProduct.mk A (A ⧸ P ^ r) M 1
  refine ⟨g, ?_, ?_⟩
  · exact e.surjective.comp (TensorProduct.mk_surjective A M (A ⧸ P ^ r) Ideal.Quotient.mk_surjective)
  · intro x
    have h1 : g x = 0 ↔ (1 : A ⧸ P ^ r) ⊗ₜ[A] x = 0 := by
      simp [g, e.map_eq_zero_iff]
    rw [h1, ← (quotTensorEquivQuotSMul M (P ^ r)).map_eq_zero_iff]
    have h2 : (1 : A ⧸ P ^ r) = Ideal.Quotient.mk (P ^ r) 1 := rfl
    rw [h2, quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectivePiAdjoinRootKerEqRange
section
open Polynomial

namespace GlobalTheory

theorem exists_equiv_pi_adjoinRoot_of_aeval_eq_zero (F : Type) [Field F] (Q : Type) [AddCommGroup Q]
    [Module F Q] [FiniteDimensional F Q] (g : Module.End F Q) (f : F[X]) [Fact (Irreducible f)]
    (h : aeval g f = 0) :
    ∃ (t : ℕ) (e : Q ≃ₗ[F] (Fin t → AdjoinRoot f)),
      (∀ v, e (g v) = AdjoinRoot.root f • e v) ∧ Module.finrank F Q = f.natDegree * t := by
  have hf : f ≠ 0 := (Fact.out : Irreducible f).ne_zero
  let φ : AdjoinRoot f →+* Module.End F Q :=
    Ideal.Quotient.lift (Ideal.span {f}) (aeval g : F[X] →ₐ[F] Module.End F Q).toRingHom (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp [h])
  have hφ : ∀ p : F[X], φ (AdjoinRoot.mk f p) = aeval g p := fun p => rfl
  letI : Module (AdjoinRoot f) Q := Module.compHom Q φ
  have hs : ∀ (a : AdjoinRoot f) (v : Q), a • v = φ a v := fun _ _ => rfl
  haveI : IsScalarTower F (AdjoinRoot f) Q := ⟨fun c a v => by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hs, hs, AdjoinRoot.smul_mk, hφ, hφ]
    simp⟩
  haveI : Module.Finite (AdjoinRoot f) Q := Module.Finite.of_restrictScalars_finite F _ _
  refine ⟨Module.finrank (AdjoinRoot f) Q,
    (Module.finBasis (AdjoinRoot f) Q).equivFun.restrictScalars F, fun v => ?_, ?_⟩
  · have : g v = AdjoinRoot.root f • v := by
      rw [hs, ← AdjoinRoot.mk_X, hφ]; simp
    rw [this]
    exact map_smul (Module.finBasis (AdjoinRoot f) Q).equivFun _ _
  · rw [← Module.finrank_mul_finrank F (AdjoinRoot f) Q, (AdjoinRoot.powerBasis hf).finrank,
      AdjoinRoot.powerBasis_dim]

theorem exists_surjective_pi_adjoinRoot_ker_eq_range (F : Type) [Field F] (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X])
    [Fact (Irreducible f)] :
    ∃ (t : ℕ) (π : V →ₗ[F] (Fin t → AdjoinRoot f)), Function.Surjective π ∧
      (∀ v, π (g v) = AdjoinRoot.root f • π v) ∧
      LinearMap.ker π = LinearMap.range (aeval g f) ∧
      Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t := by
  set N : Submodule F V := LinearMap.range (aeval g f) with hN
  have hg : N ≤ N.comap g := by
    rintro _ ⟨v, rfl⟩
    refine ⟨g v, ?_⟩
    have h1 : aeval g f * g = g * aeval g f := by
      have : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
      simpa using this
    exact congrArg (fun u : Module.End F V => u v) h1
  let gq : Module.End F (V ⧸ N) := N.mapQ N g hg
  have hq : ∀ v, gq (N.mkQ v) = N.mkQ (g v) := fun v => rfl
  have hp : ∀ (p : F[X]) (v : V), aeval gq p (N.mkQ v) = N.mkQ (aeval g p v) := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => intro v; simp [Module.algebraMap_end_apply]
    | add p q hp hq => intro v; simp only [map_add, LinearMap.add_apply, hp, hq]
    | monomial n a ih =>
      intro v
      rw [pow_succ, ← mul_assoc, map_mul, map_mul (aeval g), aeval_X, aeval_X,
        Module.End.mul_apply, Module.End.mul_apply, hq, ih]
  have h0 : aeval gq f = 0 := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := N.mkQ_surjective x
    rw [hp]
    exact (Submodule.Quotient.mk_eq_zero N).2 ⟨v, rfl⟩
  obtain ⟨t, e, he, hd⟩ := exists_equiv_pi_adjoinRoot_of_aeval_eq_zero F (V ⧸ N) gq f h0
  refine ⟨t, e.toLinearMap ∘ₗ N.mkQ, e.surjective.comp N.mkQ_surjective, fun v => ?_, ?_, ?_⟩
  · have := he (N.mkQ v)
    rw [hq] at this
    exact this
  · rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]
  · have h1 := LinearMap.finrank_range_add_finrank_ker (aeval g f)
    have h2 := Submodule.finrank_quotient_add_finrank N
    rw [← hN] at h1
    omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreAndEqOfSpecializesOfIsFinite
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem finite_fibre_and_eq_of_specializes_of_isFinite :
    ∀ (Y Y' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ y : Y,
      {a : Y' | k a = y}.Finite ∧ ∀ a b : Y', k a = y → k b = y → a ⤳ b → a = b := by
  intro Y Y' k hk y
  refine ⟨k.finite_preimage_singleton y, ?_⟩
  intro a b ha hb h
  have hd := (k.isDiscrete_preimage_singleton y).to_subtype
  have h' : (⟨a, ha⟩ : k ⁻¹' {y}) ⤳ ⟨b, hb⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val h'.eq

end GlobalTheory
end

