import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimension
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbMonoIsoAny

open GlobalTheory.NearFibreIso GlobalTheory.DenseFibreIso

theorem exists_away_bijective_of_fg {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (R K : Type) [CommRing R] [CommRing K]
    [Algebra R K] [Algebra R A] [Algebra R B] [IsScalarTower R A B] [Module.Flat R B]
    (hs : Function.Surjective (algebraMap A B))
    (hfg : (RingHom.ker (algebraMap A B)).FG)
    (h : Function.Injective
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))
    (m : PrimeSpectrum (A ⊗[R] K)) :
    ∃ a : A, algebraMap A (A ⊗[R] K) a ∉ m.asIdeal ∧ Function.Bijective
      (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away a →+* Localization.Away a ⊗[A] B) := by
  let I : Submodule A A := LinearMap.ker (Algebra.linearMap A B)
  have : Module.Finite A I := Module.Finite.iff_fg.2 hfg
  have hex : Function.Exact I.subtype (Algebra.linearMap A B) := LinearMap.exact_subtype_ker_map _
  have hinj : Function.Injective ((I.subtype.restrictScalars R).rTensor K) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj K _).1
      (LinearMap.lTensor_injective_of_exact_of_flat ((Algebra.linearMap A B).restrictScalars R) hs
        (I.subtype.restrictScalars R) Subtype.val_injective hex K)
  have h1 : Subsingleton (I ⊗[R] K) := by
    refine subsingleton_of_forall_eq 0 fun z => hinj (h ?_)
    rw [map_zero, map_zero]
    induction z with
    | zero => rw [map_zero, map_zero]
    | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]
    | tmul x c =>
      have e : (x : A) ⊗ₜ[R] c = (x : A) • ((1 : A) ⊗ₜ[R] c) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      have hx : (x : A) • (1 : B) = 0 := by
        rw [← Algebra.algebraMap_eq_smul_one]; exact x.2
      change ((x : A) ⊗ₜ[R] c) ⊗ₜ[A] (1 : B) = 0
      rw [e, TensorProduct.smul_tmul, hx, TensorProduct.tmul_zero]
  have h2 : Subsingleton ((A ⊗[R] K) ⊗[A] I) :=
    ((TensorProduct.comm A _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A I K)).toEquiv.subsingleton
  obtain ⟨a, ha, ha'⟩ := exists_smul_eq_zero (A := A) (N := I) (A ⊗[R] K) m
  refine ⟨a, ha, ?_⟩
  have h3 := subsingleton_of_isUnit ha' (Localization.Away a)
    (IsLocalization.Away.algebraMap_isUnit a)
  rw [includeLeft_eq, EquivLike.bijective_comp]
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, LinearMap.lTensor_surjective _ hs⟩
  obtain ⟨y, rfl⟩ := (lTensor_exact (Localization.Away a) hex hs z).1 hz
  rw [Subsingleton.elim y 0, map_zero]

set_option backward.isDefEq.respectTransparency.types false in

theorem near_isIso_of_finitePresentation {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R)
    (f : Y ⟶ X) (K : Type) [Field K] [Algebra R K] [hcl : IsClosedImmersion f]
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation (f ≫ s)] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  refine local_of_ring (K := K) s f _ (fun A B _ _ _ _ _ _ j j' _ H hj hb m => ?_) x hx
  have h1 : IsClosedImmersion (spMap (algebraMap A B)) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) H.flip hcl
  have hs : Function.Surjective (algebraMap A B) := by
    have h2 := (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap (algebraMap A B))).2
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
    have h3 := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom).2.comp h2
    rw [← ConcreteCategory.coe_comp, e, ConcreteCategory.coe_comp] at h3
    exact h3.of_comp
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H ‹_›
  have e : spMap (algebraMap R B) = j' ≫ f ≫ s := by
    rw [← H.w_assoc, hj, ← Spec.map_comp, IsScalarTower.algebraMap_eq R A B]; rfl
  have h2 : Flat (spMap (algebraMap R B)) := by
    rw [e]; infer_instance
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h2)
  have h3 : LocallyOfFinitePresentation (spMap (algebraMap R B)) := by
    rw [e]; infer_instance
  have h4 : LocallyOfFinitePresentation (spMap (algebraMap R A)) := by
    rw [← hj]; infer_instance
  have : Algebra.FinitePresentation R B := RingHom.finitePresentation_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h3)
  have : Algebra.FinitePresentation R A := RingHom.finitePresentation_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h4)
  have hfg : (RingHom.ker (algebraMap A B)).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (IsScalarTower.toAlgHom R A B) hs
  obtain ⟨a, ha, ha'⟩ := exists_away_bijective_of_fg R K hs hfg hb.1 m
  exact ⟨a, ha, isIso_SpecMap_iff.2 ha'⟩

theorem isIso_of_isClosedImmersion {S X Y : Scheme.{0}} (p : X ⟶ S)
    (f : Y ⟶ X) [IsClosedImmersion f] [GeometricallyConnected p] [Surjective (f ≫ p)]
    {g g' : ℕ} (hg' : SmoothOfRelativeDimension g' p)
    (hg : SmoothOfRelativeDimension g (f ≫ p)) (hle : g' ≤ g) : IsIso f := by
  have hn : ∀ y : X, Near f (MorphismProperty.isomorphisms _) y := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p y)) isOpen_univ
    replace hU : IsAffineOpen U := hU
    let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
    obtain ⟨z, hz⟩ : p y ∈ Set.range j := by rw [hU.range_fromSpec]; exact hyU
    let gX := pullback.fst p j
    let s := pullback.snd p j
    let f' := pullback.snd f gX
    have HX := IsPullback.of_hasPullback p j
    have HY := IsPullback.of_hasPullback f gX
    have HYS := HY.paste_vert HX
    obtain ⟨y', hy', hy's⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z hz.symm
    have : Surjective (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have h₁ : SmoothOfRelativeDimension g' s :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback HX hg'
    have h₂ : SmoothOfRelativeDimension g (f' ≫ s) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback HYS hg
    have : Smooth s := h₁.smooth
    have : Smooth (f' ≫ s) := h₂.smooth
    have : (s y').asIdeal.IsPrime := (s y').isPrime
    have := GlobalTheory.AbMonoIso.fibre_isIso s f' h₁ h₂ hle (s y').asIdeal.ResidueField
    have h := near_isIso_of_finitePresentation s f' (s y').asIdeal.ResidueField y'
      (Ideal.ker_algebraMap_residueField (s y').asIdeal)
    have h' := Near.of_pullback f HY.flip h
    rwa [hy'] at h'
  have h := isIso_of_near f (𝟙 _) (fun y => by simpa using hn y)
  have e : f = inv (pullback.fst f (𝟙 X)) ≫ pullback.snd f (𝟙 X) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

theorem isIso_of_mono : ∀ (S : Scheme.{0}) (B B' : Over S) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension g B'.hom → ∀ x : B ⟶ B', IsMonHom x → Mono x → IsIso x := by
  intro S B B' _ _ hB hB' g hg hg' x _ _
  have := hB.proper
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : IsIso x.left :=
    isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) le_rfl
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

end GlobalTheory.AbMonoIsoAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineMilnorSquareOfCartesianRingSquareStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineMilnorSquare_of_cartesian_ring_square : ∀ (P C₁ C₂ C₀ : Type) [CommRing P] [CommRing C₁] [CommRing C₂] [CommRing C₀] (p₁ : P →+* C₁) (p₂ : P →+* C₂) (q₁ : C₁ →+* C₀) (q₂ : C₂ →+* C₀), q₁.comp p₁ = q₂.comp p₂ → (∀ x, p₁ x = 0 → p₂ x = 0 → x = 0) → (∀ a b, q₁ a = q₂ b → ∃ x, p₁ x = a ∧ p₂ x = b) → Function.Surjective q₂ → Milnor (spMap p₁) (spMap p₂) (spMap q₁) (spMap q₂) := by
  first | exact @GlobalTheory.DualOpen.milnor_of_ring_square | exact GlobalTheory.DualOpen.milnor_of_ring_square | (intros; apply GlobalTheory.DualOpen.milnor_of_ring_square <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenMeetingFibresPullbackSpecRingHomStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineOpen_meeting_fibres_pullback_specRingHom : ∀ {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R') (A : Over (Sp R)) (W : A.left.Opens), IsAffineOpen W → (∀ t ∈ Set.range (spMap a), ∃ x ∈ W, A.hom x = t) → ∃ V : ((Over.pullback (spMap a)).obj A).left.Opens, IsAffineOpen V ∧ ∀ s : Sp R', ∃ x ∈ V, ((Over.pullback (spMap a)).obj A).hom x = s := by
  first | exact @GlobalTheory.affine_preimage_pullback_meets_fibres | exact GlobalTheory.affine_preimage_pullback_meets_fibres | (intros; apply GlobalTheory.affine_preimage_pullback_meets_fibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingInjectsToRingMappingToDense
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AffineDense

theorem sInf_minimalPrimes_eq_bot (R : Type) [CommRing R] [IsReduced R] :
    sInf (minimalPrimes R) = ⊥ := by
  rw [minimalPrimes, Ideal.sInf_minimalPrimes]
  exact nilradical_eq_zero R

theorem exists_minimal_ge_of_disjoint {R : Type} [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (P : Ideal R) (hP : Disjoint (P : Set R) (nonZeroDivisors R)) :
    ∃ q ∈ minimalPrimes R, P ≤ q := by
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  have hsub : (P : Set R) ⊆ ⋃ i ∈ (↑t : Set (Ideal R)), ((fun I : Ideal R => I) i : Set R) := by
    intro a ha
    have hnz : a ∉ nonZeroDivisors R := fun h => Set.disjoint_left.1 hP ha h
    rw [mem_nonZeroDivisors_iff] at hnz
    push_neg at hnz
    obtain ⟨b, hba, hb⟩ : ∃ b, b * a = 0 ∧ b ≠ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨x, hx, hx0⟩ := hnz (fun x hx => h x (by rw [mul_comm]; exact hx))
      exact hx0 (h x hx)
    have hb' : b ∉ sInf (minimalPrimes R) := by
      rw [sInf_minimalPrimes_eq_bot]; exact hb
    rw [Ideal.mem_sInf] at hb'
    push_neg at hb'
    obtain ⟨q, hq, hbq⟩ := hb'
    have hqp : q.IsPrime := Ideal.minimalPrimes_isPrime hq
    have haq : a ∈ q := (hqp.mem_or_mem (hba ▸ q.zero_mem)).resolve_left hbq
    simp only [Set.mem_iUnion]
    exact ⟨q, by rw [ht]; exact hq, haq⟩
  obtain ⟨q, hqt, hPq⟩ := (Ideal.subset_union_prime ⊥ ⊥ (fun i hi _ _ => by
    have : i ∈ minimalPrimes R := by rw [← ht]; exact hi
    exact Ideal.minimalPrimes_isPrime this)).1 hsub
  exact ⟨q, by rw [← ht]; exact hqt, hPq⟩

theorem exists_annihilator_of_minimal {R : Type} [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (q : Ideal R) (hq : q ∈ minimalPrimes R) : ∃ s ∉ q, ∀ a ∈ q, s * a = 0 := by
  classical
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  have hqp : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  have hnle : ¬ (t.erase q).inf (fun I : Ideal R => I) ≤ q := by
    rw [hqp.inf_le']
    rintro ⟨i, hi, hiq⟩
    have him : i ∈ minimalPrimes R := by rw [← ht]; exact Finset.mem_of_mem_erase hi
    have : q ≤ i := hq.2 ⟨Ideal.minimalPrimes_isPrime him, bot_le⟩ hiq
    exact Finset.ne_of_mem_erase hi (le_antisymm hiq this)
  obtain ⟨s, hs, hsq⟩ := Set.not_subset.1 hnle
  refine ⟨s, hsq, fun a ha => ?_⟩
  have : s * a ∈ sInf (minimalPrimes R) := by
    rw [Ideal.mem_sInf]
    intro I hI
    by_cases hIq : I = q
    · subst hIq; exact I.mul_mem_left s ha
    · have hIt : I ∈ t.erase q := Finset.mem_erase.2 ⟨hIq, by rw [← Finset.mem_coe, ht]; exact hI⟩
      exact I.mul_mem_right a (Finset.inf_le (f := fun I : Ideal R => I) hIt hs)
  rw [sInf_minimalPrimes_eq_bot] at this
  exact this

theorem mem_of_dense_of_disjoint {R : Type} [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (D : Set (PrimeSpectrum R)) (hDo : IsOpen D) (hD : Dense D) (P : PrimeSpectrum R)
    (hP : Disjoint (P.asIdeal : Set R) (nonZeroDivisors R)) : P ∈ D := by
  obtain ⟨q, hq, hPq⟩ := exists_minimal_ge_of_disjoint P.asIdeal hP
  obtain ⟨s, hsq, hs⟩ := exists_annihilator_of_minimal q hq
  let Q : PrimeSpectrum R := ⟨q, Ideal.minimalPrimes_isPrime hq⟩
  obtain ⟨Q', hQ', hQ'D⟩ := hD.inter_open_nonempty (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum R))
    (PrimeSpectrum.basicOpen s).isOpen ⟨Q, hsq⟩
  have hle : Q ≤ Q' := by
    intro a ha
    have h0 : s * a ∈ Q'.asIdeal := by rw [hs a ha]; exact Q'.asIdeal.zero_mem
    exact (Q'.isPrime.mem_or_mem h0).resolve_left hQ'
  have hQD : Q ∈ D := ((PrimeSpectrum.le_iff_specializes Q Q').1 hle).mem_open hDo hQ'D
  exact ((PrimeSpectrum.le_iff_specializes P Q).1 hPq).mem_open hDo hQD

end GlobalTheory.AffineDense

open GlobalTheory.AffineDense in

theorem GlobalTheory.affineOpen_injects_to_dense : ∀ (X : Scheme.{0}) [IsReduced X] [IsLocallyNoetherian X] (U : X.Opens), Dense (U : Set X) → ∀ (W : X.Opens) (hW : IsAffineOpen W), ∃ (K : Type) (_ : CommRing K) (ρ : Γ(X, W) →+* K), Function.Injective ρ ∧ ⊤ ≤ (spMap ρ ≫ (show Sp Γ(X, W) ⟶ X from hW.fromSpec)) ⁻¹ᵁ U := by
  intro X _ _ U hU W hW
  haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  refine ⟨Localization (nonZeroDivisors Γ(X, W)), inferInstance, algebraMap _ _,
    IsLocalization.injective _ le_rfl, ?_⟩
  intro x _
  have hD : Dense ((hW.fromSpec ⁻¹ᵁ U : (Spec Γ(X, W)).Opens) : Set (Spec Γ(X, W))) :=
    hU.preimage hW.fromSpec.isOpenEmbedding.isOpenMap
  have key := mem_of_dense_of_disjoint (R := Γ(X, W)) _ (hW.fromSpec ⁻¹ᵁ U).isOpen hD
    ((spMap (algebraMap Γ(X, W) (Localization (nonZeroDivisors Γ(X, W))))).base x) ?_
  · exact key
  · rw [Set.disjoint_left]
    intro a ha hnzd
    have hu : IsUnit (algebraMap Γ(X, W) (Localization (nonZeroDivisors Γ(X, W))) a) :=
      IsLocalization.map_units _ (⟨a, hnzd⟩ : nonZeroDivisors Γ(X, W))
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenToFunctionFieldInjectiveAndFractionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineOpen_to_functionField_injective_and_fraction : ∀ (X : Scheme.{0}) (V : X.Opens) [IsIntegral V.toScheme] (W : X.affineOpens), W.1 ≤ V → ∀ (ρW : Γ(X, W.1) →+* V.toScheme.functionField), spMap ρW ≫ GlobalTheory.LogKS.chart W = V.toScheme.fromSpecStalk (genericPoint V.toScheme) ≫ V.ι → Function.Injective ρW ∧ ∀ x : V.toScheme.functionField, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a := by
  first | exact @GlobalTheory.GenFrac.injective_and_frac | exact GlobalTheory.GenFrac.injective_and_frac | (intros; apply GlobalTheory.GenFrac.injective_and_frac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseSystemInAlgebraisingClosedSubscheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem alg_of_closedSubscheme : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (a : W.IdealSheafData), Alg (a.subschemeι ≫ f) I →
    ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → (∀ e, IsProper ((t e).subschemeι ≫ f)) →
    ∃ T : W.IdealSheafData, IsProper (T.subschemeι ≫ f) ∧ Reduces f I T (fun e => t e ⊔ a) := by
  intro R _ I W f a hA t ht hp
  set ι := a.subschemeι with hι
  have hbase : ∀ J : Ideal R, (baseIdeal f J).comap ι = baseIdeal (ι ≫ f) J :=
    fun J => GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1 R W a.subscheme f ι J
  have hms := GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion a.subscheme W ι inferInstance
  let s : ℕ → a.subscheme.IdealSheafData := fun e => (t e).comap ι
  have hs : IsSystem (ι ≫ f) I s := fun e => by
    simp only [s]
    rw [ht e, Scheme.IdealSheafData.comap_sup, hbase]
  have hsp : ∀ e, IsProper ((s e).subschemeι ≫ ι ≫ f) := fun e => by
    have H : t e ≤ (s e).map ι := Scheme.IdealSheafData.le_map_comap _ _
    rw [← Category.assoc, ← Scheme.IdealSheafData.subschemeMap_subschemeι (s e) (t e) ι H,
      Category.assoc]
    haveI := hp e
    haveI : IsClosedImmersion (Scheme.IdealSheafData.subschemeMap (s e) (t e) ι H) := by
      haveI : IsClosedImmersion (Scheme.IdealSheafData.subschemeMap (s e) (t e) ι H ≫
          (t e).subschemeι) := by
        rw [Scheme.IdealSheafData.subschemeMap_subschemeι]; infer_instance
      exact IsClosedImmersion.of_comp_isClosedImmersion _ (t e).subschemeι
    infer_instance
  obtain ⟨T₀, hT₀p, hT₀r⟩ := hA s hs hsp
  refine ⟨T₀.map ι, ?_, fun e => ?_⟩
  · let g := T₀.subschemeι ≫ ι
    have hk : (T₀.map ι).subschemeι.ker = g.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; rfl
    haveI := IsClosedImmersion.isIso_lift _ _ hk
    have hfac : (T₀.map ι).subschemeι =
        inv (IsClosedImmersion.lift (T₀.map ι).subschemeι g hk.le) ≫ g := by
      rw [IsIso.eq_inv_comp, IsClosedImmersion.lift_fac]
    rw [hfac, Category.assoc]
    haveI : IsProper (g ≫ f) := by simpa [g, Category.assoc] using hT₀p
    infer_instance
  · calc T₀.map ι ⊔ baseIdeal f (I ^ (e + 1))
        = (T₀ ⊔ (baseIdeal f (I ^ (e + 1))).comap ι).map ι := (hms T₀ _).1.symm
      _ = (s e).map ι := by rw [hbase, hT₀r e]
      _ = ((⊥ : a.subscheme.IdealSheafData) ⊔ (t e).comap ι).map ι := by rw [bot_sup_eq]
      _ = t e ⊔ a := by
        rw [(hms ⊥ (t e)).1, Scheme.IdealSheafData.map_bot, hι,
          Scheme.IdealSheafData.ker_subschemeι, sup_comm]

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleDivIffIsAmpleLB
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem presents_lbPow_toLB' {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ) :
    Presents (k • D) (lbPow (toLB D) k) fun j => (j PUnit.unit).1.2 ^ k := by
  refine ⟨isLB_lbPow (isLB_toLB D) k, fun i j h => ?_, fun i x hx => ?_⟩
  · simp only [show (lbPow (toLB D) k).g i j = _ from lbPow_g _ k i j, Units.val_pow_eq_pow_val,
      LB.val_res, map_pow, fnOf_resG, fnOf_toLB_g]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Units.ne_zero _))]
  · exact ((i PUnit.unit).2.2 x ((lbPow_U _ k i).le hx)).nsmul k

theorem locus_rat {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ)
    (s : (lbPow (toLB D) k).Sec) :
    locus D k ((presents_lbPow_toLB' D k).rat s) = (nonzeroLocus s : Set X) :=
  Set.ext fun _ => (presents_lbPow_toLB' D k).generatesAt_rat_iff s

theorem rat_mem_sec {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ)
    (s : (lbPow (toLB D) k).Sec) : (presents_lbPow_toLB' D k).rat s ∈ Sec D k :=
  CartierDiv.mem_sections.1 ((presents_lbPow_toLB' D k).rat_mem s)

theorem ampleDiv_iff_isAmpleLB : ∀ (X : Scheme.{0}) [IsIntegral X] [CompactSpace X] (D : CartierDiv X),
    AmpleDiv D ↔ IsAmpleLB (toLB D) := by
  intro X _ hc D
  constructor
  · intro h
    refine ⟨isLB_toLB D, hc, fun x => ?_⟩
    obtain ⟨k, hk, u, hu, U, hUa, hU, hx⟩ := h x
    obtain ⟨s, hs⟩ := (presents_lbPow_toLB' D k).exists_rat_eq (CartierDiv.mem_sections.2 hu)
    have e : nonzeroLocus s = U := SetLike.coe_injective (by rw [hU, ← locus_rat D k s, hs])
    exact ⟨k, hk, s, e ▸ hx, e ▸ hUa⟩
  · intro h x
    obtain ⟨k, hk, s, hx, ha⟩ := h.exists_affine x
    exact ⟨k, hk, _, rat_mem_sec D k s, nonzeroLocus s, ha, (locus_rat D k s).symm, hx⟩

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTwistNormalisedBlowupNoetherianDomain
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.SiegelTor GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.BlowAmpleNoeth
open GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.ProjBlowup

theorem ample_twist_of_blowup : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X X' N : Scheme.{0})
    (s : X ⟶ Sp R) (J : X.IdealSheafData) (b : X' ⟶ X) (ν : N ⟶ X') (EX : EffCartierData N), IsProjOver s →
    FinalTheorems.Blowup b J → IsFinite ν → EX.idealSheaf = J.comap (ν ≫ b) → ∀ L : LB X, IsAmpleLB L → ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      IsAmpleLB (CechPic.tens (lbPow (L.pull (ν ≫ b)) T) (CechPic.dual EX.lb)) := by
  intro R _ _ _ X X' N s J b ν EX hs hb hν hEX L hL
  obtain ⟨L₀, m, σ, hL₀, hσ⟩ := GlobalTheory.T.exists_lineBundle_sections_generate_idealSheaf R X s J hs
  obtain ⟨c, hc, hprop, hci⟩ := GlobalTheory.T.exists_closedImmersion_blowup_generatingSections R X X' s J b L₀ m σ hs hb hσ
  have hψ : Proportional σ (ν ≫ b) (ν ≫ c) := hprop.comp ν
  have hiso := GlobalTheory.T.pullback_O1_iso_blowup_twist_dual R X N J L₀ m σ (ν ≫ b) (ν ≫ c) EX hL₀ hσ hψ hEX
  have : IsProper s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str R n
    infer_instance
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (GlobalTheory.AmpleDominates.eventually_isAmpleLB s hL hL₀)
  refine ⟨T₀, fun T hT => ?_⟩
  have hA := hT₀ T hT
  have hO := isAmple_projective_O_one R m
  set A := LB.div (lbPow L T) L₀ with hAdef
  set p := pullback.fst s (PSpace.str R m)
  set q := pullback.snd s (PSpace.str R m)
  set B := tens (A.pull p) ((O1 R m).pull q)
  have hBL : B.IsLB := isLB_tens (LB.isLB_pull hA.isLB _) (LB.isLB_pull hO.isLB _)
  have hB : IsAmpleLB B := by
    refine hA.box hO hBL (IsPullback.of_hasPullback s (PSpace.str R m)) ?_
    have h1 := LB.isLB_div hBL (LB.isLB_pull hA.isLB p)
    refine (cls_eq_zero_iff (LB.isLB_div h1 (LB.isLB_pull hO.isLB q))).1 ?_
    rw [cls_div h1 (LB.isLB_pull hO.isLB q), cls_div hBL (LB.isLB_pull hA.isLB p),
      cls_tens (LB.isLB_pull hA.isLB p) (LB.isLB_pull hO.isLB q)]
    abel
  let h : N ⟶ pullback s (PSpace.str R m) := ν ≫ pullback.lift b c hc
  have hp : h ≫ p = ν ≫ b := by
    simp only [h, p, Category.assoc]; rw [pullback.lift_fst]
  have hq : h ≫ q = ν ≫ c := by
    simp only [h, q, Category.assoc]; rw [pullback.lift_snd]
  have h2 := hB.pull_of_isAffineHom h
  have hT : (CechPic.tens (lbPow (L.pull (ν ≫ b)) T) (CechPic.dual EX.lb)).IsLB :=
    isLB_tens (isLB_lbPow (LB.isLB_pull hL.isLB _) T) (isLB_dual EX.isLB_lb)
  refine h2.of_lbIso hT ((cls_eq_iff hT (LB.isLB_pull hBL h)).1 ?_)
  have hG := (cls_eq_iff (LB.isLB_pull hO.isLB _) (isLB_tens (LB.isLB_pull hL₀ _) (isLB_dual EX.isLB_lb))).2 hiso
  rw [cls_tens (LB.isLB_pull hL₀ _) (isLB_dual EX.isLB_lb), cls_dual EX.isLB_lb, cls_pull hO.isLB, cls_pull hL₀] at hG
  rw [cls_pull hBL, cls_tens (LB.isLB_pull hA.isLB p) (LB.isLB_pull hO.isLB q), cls_pull hA.isLB, cls_pull hO.isLB,
    cls_div (isLB_lbPow hL.isLB T) hL₀, cls_lbPow hL.isLB,
    cls_tens (isLB_lbPow (LB.isLB_pull hL.isLB _) T) (isLB_dual EX.isLB_lb), cls_dual EX.isLB_lb,
    cls_lbPow (LB.isLB_pull hL.isLB _), cls_pull hL.isLB, map_add, ← pull_comp, ← pull_comp, hp, hq, hG]
  simp only [map_sub, map_nsmul]
  abel

end GlobalTheory.BlowAmpleNoeth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rep_ev_of_isPullback : ∀ (S : Scheme.{0}) (A B S' S'' B'' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (h : S'' ⟶ S') (k : B'' ⟶ B) (b'' : B'' ⟶ S''), Rep A b P → IsPullback k b'' b h → Rep A b'' (ev P (fst A B'') (snd A B'' ≫ k)) := by
  first | exact @GlobalTheory.DualCon.Rep.baseChange | exact GlobalTheory.DualCon.Rep.baseChange | (intros; apply GlobalTheory.DualCon.Rep.baseChange <;> assumption)
end

