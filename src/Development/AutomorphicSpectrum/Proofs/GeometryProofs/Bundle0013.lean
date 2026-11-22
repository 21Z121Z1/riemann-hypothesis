import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0006

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiChangeOfBasisDetStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iota_multi_change_of_basis_det : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V) (P : Matrix (Fin n) (Fin n) Ω), exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j) = P.det • exteriorPower.ιMulti Ω n e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family | exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiNeZeroOfLinIndepStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iota_multi_ne_zero_of_lin_indep : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V), LinearIndependent Ω e → exteriorPower.ιMulti Ω n e ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent | exact GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsClopenSpecializationsGenPt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_isOpen_common_generization {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] (p : Y) :
    ∃ V : Set Y, IsOpen V ∧ p ∈ V ∧ ∀ q ∈ V, ∃ z : Y, z ⤳ p ∧ z ⤳ q := by
  have hF : (irreducibleComponents Y).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine ⟨⋂ Z ∈ {Z ∈ irreducibleComponents Y | p ∉ Z}, Zᶜ, ?_, ?_, ?_⟩
  · refine (hF.subset (Set.sep_subset _ _)).isOpen_biInter fun Z hZ => ?_
    exact (isClosed_of_mem_irreducibleComponents Z hZ.1).isOpen_compl
  · simp only [Set.mem_iInter]
    exact fun Z hZ => hZ.2
  · intro q hq
    have hmem := irreducibleComponent_mem_irreducibleComponents q
    have hpZ : p ∈ irreducibleComponent q := by
      by_contra hp
      exact (Set.mem_iInter₂.1 hq _ ⟨hmem, hp⟩) mem_irreducibleComponent
    obtain ⟨z, hz⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := q))
      isClosed_irreducibleComponent
    exact ⟨z, hz.specializes hpZ, hz.specializes mem_irreducibleComponent⟩

theorem genPt_specializes_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) {p z : X}
    (hp : genPt ξ ⤳ p) (hz : z ⤳ p) : genPt ξ ⤳ z := by
  obtain ⟨y, rfl⟩ : z ∈ Set.range (X.fromSpecStalk p) := by
    rw [Scheme.range_fromSpecStalk]; exact hz
  have hinj := h.inj ⟨p, hp⟩
  haveI : IsDomain (X.presheaf.stalk p) := hinj.isDomain (genMap ξ ⟨p, hp⟩)
  have hp' : ξ (IsLocalRing.closedPoint (CommRingCat.of Ω)) ⤳ p := hp
  let φ := X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ
  have hφ : Spec.map φ ≫ X.fromSpecStalk p = ξ := by
    change Spec.map (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ≫ _ = ξ
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hbot : (Spec.map φ) (IsLocalRing.closedPoint Ω) =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p)) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (genMap ξ ⟨p, hp⟩) (IsLocalRing.maximalIdeal Ω) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ hinj
  have hη : genPt ξ = X.fromSpecStalk p ⟨⊥, Ideal.isPrime_bot⟩ := by
    rw [← hbot]
    conv_lhs => rw [genPt, ← hφ]
    rfl
  rw [hη]
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le).map (X.fromSpecStalk p).continuous

theorem isClopen_setOf_genPt_specializes (X : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (h : IsCptGen ξ) :
    IsClopen {q : X | genPt ξ ⤳ q} := by
  refine ⟨?_, ?_⟩
  · have : {q : X | genPt ξ ⤳ q} = closure {genPt ξ} := by
      ext q; exact specializes_iff_mem_closure
    rw [this]; exact isClosed_closure
  · rw [isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    obtain ⟨V, hV, hpV, hVq⟩ := @exists_isOpen_common_generization U _
      (noetherianSpace_of_isAffineOpen U hU) U.isOpen.isOpenEmbedding_subtypeVal.quasiSober
      ⟨p, hpU⟩
    have hopen : IsOpen (Subtype.val '' V : Set X) := U.isOpen.isOpenMap_subtype_val V hV
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨_, hpV, rfl⟩) ?_
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨z, hzp, hzq⟩ := hVq q hq
    exact (genPt_specializes_of_specializes ξ h (p := p) hp
      (hzp.map continuous_subtype_val)).trans (hzq.map continuous_subtype_val)

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGeneric
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem injective_of_maximal_point {X : Scheme.{0}} {Ω : Type} [Field Ω] (p : X)
    [IsDomain (X.presheaf.stalk p)] (φ : X.presheaf.stalk p ⟶ CommRingCat.of Ω)
    (h : ∀ y : X, y ⤳ (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω) →
      y = (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω)) :
    Function.Injective φ.hom := by
  let z : PrimeSpectrum (X.presheaf.stalk p) := ⟨⊥, Ideal.isPrime_bot⟩
  let q : PrimeSpectrum (X.presheaf.stalk p) := PrimeSpectrum.comap φ.hom (IsLocalRing.closedPoint Ω)
  have hs : z ⤳ q := (PrimeSpectrum.le_iff_specializes z q).1 bot_le
  have hq : (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω) = X.fromSpecStalk p q := rfl
  rw [hq] at h
  have h1 : X.fromSpecStalk p z = X.fromSpecStalk p q :=
    h _ (hs.map (X.fromSpecStalk p).continuous)
  have h2 : z = q := (X.fromSpecStalk p).isEmbedding.injective h1
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  have h3 : a ∈ q.asIdeal := by
    change φ.hom a ∈ (IsLocalRing.closedPoint Ω).asIdeal
    rw [ha]
    exact Ideal.zero_mem _
  rw [← h2] at h3
  exact h3

theorem isCptGen_of_maximal_of_surjective {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : ∀ y : X, y ⤳ genPt ξ → y = genPt ξ)
    (hs : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) : IsCptGen ξ := by
  refine ⟨⟨?_, hs⟩, fun p => ?_⟩
  · have := hX (ξ (IsLocalRing.closedPoint Ω))
    refine injective_of_maximal_point _ (Scheme.stalkClosedPointTo ξ) ?_
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    exact h
  · obtain ⟨p, hp⟩ := p
    have := hX p
    have hp' : ξ (IsLocalRing.closedPoint Ω) ⤳ p := hp
    refine injective_of_maximal_point p
      (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ?_
    have e : Spec.map (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ≫
        X.fromSpecStalk p = ξ := by
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    rw [e]
    exact h

theorem isCptGen_of_maximal : ∀ (X : Scheme.{0}), (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ x : X,
    (∀ y : X, y ⤳ x → y = x) → IsCptGen (Ω := X.residueField x) (X.fromSpecResidueField x) := by
  intro X hX x h
  have e : genPt (Ω := X.residueField x) (X.fromSpecResidueField x) = x :=
    X.fromSpecResidueField_apply x _
  refine isCptGen_of_maximal_of_surjective hX _ (by rw [e]; exact h) ?_
  unfold Scheme.stalkClosedPointTo
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso _).hom).2.comp
    ((X.fromSpecResidueField x).stalkMap_surjective _)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisTowerStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_basis_tower_alt : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Algebra.FormallySmooth S T] (e m : ℕ) (z : Fin e → S) (w : Fin m → T),
    LinearIndependent S (fun i => KaehlerDifferential.D R S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D R S (z i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)) →
    Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) ∧
    Submodule.span T (Set.range fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower | exact GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower | (intros; apply GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerDifferentialsSpanLocalStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_differentials_span_local : ∀ (S B : Type) [CommRing S] [Algebra ℚ S] [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [Algebra ℂ B] (ψ : S →+* B) (φ : S →+* ℂ),
    (∀ s, ψ s - algebraMap ℂ B (φ s) ∈ IsLocalRing.maximalIdeal B) →
    ∀ (T : Set S), IsLocalRing.maximalIdeal B = Ideal.span ((fun s => ψ s - algebraMap ℂ B (φ s)) '' T) →
    ∀ (n : ℕ) (z : Fin n → S),
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    IsLocalRing.maximalIdeal B = Ideal.span (Set.range fun i => ψ (z i) - algebraMap ℂ B (φ (z i))) := by
  first | exact @GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D | exact GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D | (intros; apply GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerFinrankFractionFieldStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_finrank_fraction_field : ∀ (S T K L : Type) [CommRing S] [CommRing T] [Field K] [Field L] [Algebra S T] [Algebra S K]
    [Algebra S L] [Algebra T L] [Algebra K L] [IsScalarTower S T L] [IsScalarTower S K L]
    [IsFractionRing S K] [IsFractionRing T L] (m : ℕ) (w : Fin m → T),
    LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)) →
    Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤ →
    Module.finrank L (KaehlerDifferential K L) = m := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis | exact GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis | (intros; apply GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_existsUnique_equiv :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (M' : LieModel G x E'), ∃! f : E ≃ₗ[R] E', ∀ e, M'.pt (f e) = M.pt e := by
  intro S G _ R _ x E E' _ _ _ _ M M'

  choose f hf using fun e => M'.onto (M.pt e) (M.tan e)
  choose g hg using fun e' => M.onto (M'.pt e') (M'.tan e')
  let φ : E ≃ₗ[R] E' :=
    { toFun := f
      invFun := g
      map_add' := fun e e' => M'.inj (by rw [M'.add, hf, hf, hf, M.add])
      map_smul' := fun c e => by
        show f (c • e) = c • f e
        apply M'.inj
        apply Over.OverMorphism.ext
        rw [M'.smul, hf, hf, M.smul]
      left_inv := fun e => M.inj (by rw [hg, hf])
      right_inv := fun e' => M'.inj (by rw [hf, hg]) }
  refine ⟨φ, fun e => hf e, fun ψ hψ => ?_⟩
  exact LinearEquiv.ext fun e => M'.inj ((hψ e).trans (hf e).symm)

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem IsTanAt.comp_monHom {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {v : epsAt x ⟶ G} (hv : IsTanAt G x v) (f : G ⟶ G') [IsMonHom f] :
    IsTanAt G' x (v ≫ f) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

theorem lieModel_exists_unique_diff :
    ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (R : Type) [CommRing R]
      (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E']
      [Module R E'] (M : LieModel G x E) (M' : LieModel G' x E') (f : G ⟶ G') [IsMonHom f],
      ∃! A : E →ₗ[R] E', ∀ e, M'.pt (A e) = M.pt e ≫ f := by
  intro S G G' _ _ R _ x E E' _ _ _ _ M M' f _
  have hex : ∀ e, ∃ e', M'.pt e' = M.pt e ≫ f := fun e => M'.onto _ ((M.tan e).comp_monHom f)
  choose A hA using hex
  have hadd : ∀ e₁ e₂, A (e₁ + e₂) = A e₁ + A e₂ := fun e₁ e₂ => M'.inj (by
    rw [hA, M'.add, hA, hA, M.add, MonObj.mul_comp])
  have hsmul : ∀ (c : R) e, A (c • e) = c • A e := fun c e => M'.inj (by
    rw [hA]
    apply Over.OverMorphism.ext
    rw [M'.smul, hA, Over.comp_left, Over.comp_left, M.smul, Category.assoc])
  refine ⟨⟨⟨A, hadd⟩, hsmul⟩, fun e => hA e, ?_⟩
  intro B hB
  ext e
  exact M'.inj ((hB e).trans (hA e).symm)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalHomCharZeroUnitsStatement
section
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hom_char_zero_units : ∀ (O F L K : Type) [CommRing O] [Field F] [NumberField F] [CommRing L] [Field K] [CharZero K] (β : O →+* F) (θ : O →+* L) (ρ : L →+* K), IsLocalHom ρ → (∀ a, β a = 0 → θ a = 0) → ∀ b, β b ≠ 0 → IsUnit (θ b) := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf | exact GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf | (intros; apply GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringIntegralClosureMaxStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_subring_integral_closure_max : ∀ {K : Type} [Field K] (R D B : Subring K) [IsLocalRing R] [IsLocalRing D], R ≤ D → (∀ r ∈ R, r ≠ 0 → r⁻¹ ∈ D → r⁻¹ ∈ R) → (integralClosure R K).toSubring ≤ D → B ≤ (integralClosure R K).toSubring → (∀ a ∈ D, ∃ u ∈ B, ∃ v ∈ B, v ≠ 0 ∧ v⁻¹ ∈ D ∧ a = u / v) → ∃ (P : Ideal (integralClosure R K).toSubring) (_ : P.IsMaximal), D = (LocalSubring.ofPrime _ P).toSubring ∧ ∀ t : (integralClosure R K).toSubring, t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ D) := by
  first | exact @GlobalTheory.CompanionTheory.Domination.eq_localisation_integralClosure | exact GlobalTheory.CompanionTheory.Domination.eq_localisation_integralClosure | (intros; apply GlobalTheory.CompanionTheory.Domination.eq_localisation_integralClosure <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationKaehlerPrimeIdealStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_kaehler_prime_ideal : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type)
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (bd : Ideal (MvPolynomial σ ℤ)) (S : Subalgebra ℚ Ω₀) (S' : Subalgebra ℚ Ω) (θ : S →+* S'),
    (∀ s, ((θ s : S') : Ω) = algebraMap Ω₀ Ω s) → (∀ p, r₀ p ∈ S) → (∀ p, r₁ p ∈ S') →
    ∀ q : Ideal S',
    ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
      (∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q.comap θ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff | exact GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff <;> assumption)
end

