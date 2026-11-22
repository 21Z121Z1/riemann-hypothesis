import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingGroupMorphismDeRhamLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTraitScalarGenericFibreNonfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unit_nonfield : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ¬ IsField R → ∀ b : W, b ≠ 0 → ∀ z : Z, IsUnit (gs p z ⊤ (scal T.G.hom b)) := by
  intro R _ _ _ D C W _ _ _ T Z p p' hpp hR b hb z

  have hw : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ jK R := by
    rw [← T.ξ_π, ← C.gp_π, ← Category.assoc T.G.hom, ← T.cart.1.w, ← Category.assoc C.A.A.hom, ← C.α_cart.1.w]
    simp only [← Category.assoc]; rw [hpp]
  have hpt := congrArg (fun g => (g z).asIdeal) hw
  simp only [Scheme.Hom.comp_apply] at hpt
  set P := ((p ≫ T.G.hom) z) with hP
  have hc : P.asIdeal.comap T.φ = ⊥ := by
    have e1 : (spMap T.φ ((T.G.hom) (p z))).asIdeal = P.asIdeal.comap T.φ := by
      rw [hP, Scheme.Hom.comp_apply]; rfl
    rw [← e1, hpt]
    have e2 : ((jK R) ((C.A.A.hom) (p' z))).asIdeal = ((C.A.A.hom) (p' z)).asIdeal.comap (algebraMap R (FractionRing R)) := rfl
    rw [e2]
    have hbot : ((C.A.A.hom) (p' z)).asIdeal = ⊥ := by
      have := ((C.A.A.hom) (p' z)).isPrime
      exact Ideal.eq_bot_of_prime _
    rw [hbot]
    exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R)))
  have hdvr : IsDiscreteValuationRing W := T.cdvr.1
  have hPbot : P.asIdeal = ⊥ := by
    by_contra hne
    have hmax : P.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal P.isPrime hne
    have hm : P.asIdeal = maximalIdeal W := IsLocalRing.eq_maximalIdeal hmax
    have hRm : maximalIdeal R ≠ ⊥ := fun h => hR ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRm
    have hl := T.loc
    have hφr : T.φ r ∈ P.asIdeal := by
      rw [hm]
      exact (IsLocalRing.mem_maximalIdeal _).2 fun hu => (IsLocalRing.mem_maximalIdeal _).1 hr (isUnit_of_map_unit T.φ r hu)
    have : r ∈ P.asIdeal.comap T.φ := hφr
    rw [hc] at this
    exact hr0 ((Submodule.mem_bot R).1 this)
  have hmem : (p ≫ T.G.hom) z ∈ (Sp W).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b) := by
    rw [basicOpen_eq_of_affine]
    show b ∉ ((p ≫ T.G.hom) z).asIdeal
    rw [← hP, hPbot]; exact fun h => hb ((Submodule.mem_bot W).1 h)
  have hpull : gs p z ⊤ (scal T.G.hom b) = gs (p ≫ T.G.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b) :=
    gs_pull p T.G.hom z ⊤ trivial _
  rw [hpull, gs_eq _ z ⊤ trivial]
  have hz : z ∈ Z.basicOpen (((p ≫ T.G.hom).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b)) := by
    rw [← Scheme.preimage_basicOpen]; exact hmem
  exact (Scheme.mem_basicOpen Z _ z (by trivial)).1 hz

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsomorphismMonHomDescendsFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ

namespace GlobalTheory.IsoFinExt

theorem isPullback_compare {X S L S' T : Scheme.{0}} (a : X ⟶ S) (b : L ⟶ S) (i : S' ⟶ S) (j : T ⟶ L)
    (l : T ⟶ S') (hc : l ≫ i = j ≫ b) :
    ∃ q : pullback (pullback.snd a b) j ⟶ pullback a i,
      q ≫ pullback.fst a i = pullback.fst _ _ ≫ pullback.fst a b ∧
      IsPullback q (pullback.snd _ _) (pullback.snd a i) l := by
  have hw : (pullback.fst (pullback.snd a b) j ≫ pullback.fst a b) ≫ a = (pullback.snd _ _ ≫ l) ≫ i := by
    rw [Category.assoc, pullback.condition, pullback.condition_assoc, Category.assoc, hc]
  refine ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback a i)
  rw [pullback.lift_fst, hc]
  exact (IsPullback.of_hasPullback (pullback.snd a b) j).paste_horiz (IsPullback.of_hasPullback a b)

theorem isIso_of_compare {X₁ X₂ S L S' T : Scheme.{0}} (a₁ : X₁ ⟶ S) (a₂ : X₂ ⟶ S) (b : L ⟶ S) (i : S' ⟶ S)
    (j : T ⟶ L) (l : T ⟶ S') [Surjective l] [Flat l] [QuasiCompact l] (hc : l ≫ i = j ≫ b)
    (f : pullback a₁ b ⟶ pullback a₂ b) [IsIso f] (hf : f ≫ pullback.snd _ _ = pullback.snd _ _)
    (f' : pullback a₁ i ⟶ pullback a₂ i) (hf' : f' ≫ pullback.snd _ _ = pullback.snd _ _)
    (h : ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback a₁ b) (p' : Z ⟶ pullback a₁ i) (t : Z ⟶ T),
      p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ j →
      p' ≫ pullback.snd _ _ = t ≫ l → p ≫ f ≫ pullback.fst _ _ = p' ≫ f' ≫ pullback.fst _ _) :
    IsIso f' := by
  obtain ⟨q₁, e₁, H₁⟩ := isPullback_compare a₁ b i j l hc
  obtain ⟨q₂, e₂, H₂⟩ := isPullback_compare a₂ b i j l hc
  let F : pullback (pullback.snd a₁ b) j ⟶ pullback (pullback.snd a₂ b) j :=
    pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hf]) (by simp)
  have hF₁ : F ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f := pullback.lift_fst _ _ _
  have hF₂ : F ≫ pullback.snd _ _ = pullback.snd _ _ := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hw : q₁ ≫ f' = F ≫ q₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, e₂, ← Category.assoc F, hF₁, Category.assoc]
      exact (h _ _ q₁ _ e₁.symm pullback.condition H₁.w).symm
    · rw [Category.assoc, Category.assoc, hf', H₂.w, ← Category.assoc, hF₂, H₁.w]
  have H : IsPullback q₁ F f' q₂ := by
    refine IsPullback.of_bot ?_ hw H₂
    rw [hF₂, hf']
    exact H₁
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) q₂ :=
    ⟨⟨MorphismProperty.of_isPullback H₂.flip ‹Surjective l›,
      MorphismProperty.of_isPullback H₂.flip ‹Flat l›⟩,
      MorphismProperty.of_isPullback H₂.flip ‹QuasiCompact l›⟩
  have hF : IsIso F := inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
    H.flip hq hF

theorem exists_finite_iso : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (A₁ A₂ : Over (Sp K)) [GrpObj A₁] [GrpObj A₂], IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ (f : (Over.pullback (spMap β)).obj A₁ ≅ (Over.pullback (spMap β)).obj A₂), IsMonHom f.hom → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω : Type) (_ : Field Ω) (j : L →+* Ω) (l : K' →+* Ω) (φ : (Over.pullback (spMap io)).obj A₁ ≅ (Over.pullback (spMap io)).obj A₂), io.Finite ∧ l.comp io = j.comp β ∧ IsMonHom φ.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A₁.hom (spMap β)) (p' : Z ⟶ pullback A₁.hom (spMap io)) (t : Z ⟶ Sp Ω), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.hom.left ≫ pullback.fst _ _ = p' ≫ φ.hom.left ≫ pullback.fst _ _ := by
  intro K L _ _ _ β A₁ A₂ _ _ h₁ h₂ f hf
  obtain ⟨K', _, io, Ω, _, j, l, f', hfin, hc, hm, h⟩ := GlobalTheory.T.exists_finiteExt_abelianVarietyHom_descent K L β A₁ A₂ h₁ h₂ f.hom hf
  have hc' : spMap l ≫ spMap io = spMap j ≫ spMap β := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hc]
  have : Flat (spMap l) := by
    rw [Flat.SpecMap_iff]
    letI := l.toAlgebra
    exact (inferInstance : Module.Flat K' Ω)
  have : Surjective (spMap l) := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hl : IsIso f.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f.hom))
  have : IsIso f'.left :=
    @isIso_of_compare _ _ _ _ _ _ A₁.hom A₂.hom (spMap β) (spMap io) (spMap j) (spMap l) _ _ _ hc'
      f.hom.left hl (Over.w f.hom) f'.left (Over.w f') h
  have : IsIso ((Over.forget _).map f') := this
  have : IsIso f' := isIso_of_reflects_iso f' (Over.forget _)
  exact ⟨K', inferInstance, io, Ω, inferInstance, j, l, asIso f', hfin, hc, hm, h⟩

end GlobalTheory.IsoFinExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedMultiplicationSubmoduleStable
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem norm_ratCast_padicComplex_le_one (l : ℕ) [Fact l.Prime] (q : ℚ) (hq : 0 ≤ padicValRat l q) :
    ‖(q : ℂ_[l])‖ ≤ 1 := by
  have e : ((q : ℚ_[l]) : ℂ_[l]) = (q : ℂ_[l]) := by
    exact map_ratCast (algebraMap ℚ_[l] ℂ_[l]) q
  rw [← e, PadicComplex.norm_extends', Padic.eq_padicNorm]
  by_cases h0 : q = 0
  · subst h0; simp
  · rw [padicNorm.eq_zpow_of_nonzero h0]
    have hl : (1 : ℚ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
    exact_mod_cast zpow_le_one_of_nonpos₀ hl (by omega)

theorem eventually_isPlaceRing (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) : Eventually l lam (IsPlaceRing E l lam) := by
  classical
  let t : (E →+* ℂ) → IntermediateField ℚ ℂ := fun σ ↦ σ.toRatAlgHom.fieldRange
  haveI : ∀ σ, FiniteDimensional ℚ (t σ) := fun σ ↦
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField σ.toRatAlgHom).toLinearEquiv
  refine ⟨⨆ σ, t σ, IntermediateField.finiteDimensional_iSup_of_finite, fun R hR ↦ ?_⟩
  obtain ⟨hdvr, hsz, hmem⟩ := hR
  refine ⟨hdvr, hsz, fun q hq ↦ ?_, fun σ x ↦ ?_⟩
  · have hk : (q : ℂ) ∈ ⨆ σ, t σ := by
      simpa using IntermediateField.algebraMap_mem (⨆ σ, t σ) q
    have hqa : (q : ℂ) ∈ algebraicClosure ℚ ℂ := by
      simpa using (algebraicClosure ℚ ℂ).algebraMap_mem q
    refine hmem _ hk ⟨hqa, ?_⟩
    have e : (⟨(q : ℂ), hqa⟩ : algebraicClosure ℚ ℂ) = (q : algebraicClosure ℚ ℂ) := by
      ext; simp
    rw [e, map_ratCast, Real.rpow_zero]
    exact norm_ratCast_padicComplex_le_one l q hq
  · have hk : σ x ∈ ⨆ σ, t σ :=
      (le_iSup t σ) (AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)
    have ha : σ x ∈ algebraicClosure ℚ ℂ :=
      mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
    by_cases hn : ‖lam ⟨σ x, ha⟩‖ ≤ 1
    · refine ⟨σ x, hmem _ hk ⟨ha, by rwa [Real.rpow_zero]⟩, 1, R.one_mem, one_ne_zero, mul_one _⟩
    · push_neg at hn
      have h0 : σ x ≠ 0 := by
        intro h
        have : (⟨σ x, ha⟩ : algebraicClosure ℚ ℂ) = 0 := Subtype.ext h
        rw [this, map_zero, norm_zero] at hn
        linarith
      have hia : (σ x)⁻¹ ∈ algebraicClosure ℚ ℂ := inv_mem ha
      have hik : (σ x)⁻¹ ∈ ⨆ σ, t σ := inv_mem hk
      have e : (⟨(σ x)⁻¹, hia⟩ : algebraicClosure ℚ ℂ) = (⟨σ x, ha⟩ : algebraicClosure ℚ ℂ)⁻¹ := by
        ext; simp
      have hs : Sz l lam 0 (σ x)⁻¹ := by
        refine ⟨hia, ?_⟩
        rw [e, map_inv₀, norm_inv, Real.rpow_zero]
        exact inv_le_one_of_one_le₀ hn.le
      exact ⟨1, R.one_mem, (σ x)⁻¹, hmem _ hik hs, inv_ne_zero h0, mul_inv_cancel₀ h0⟩

end GlobalTheory.LatModel

example : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]),
    GlobalTheory.LatModel.Eventually l lam (GlobalTheory.LatModel.IsPlaceRing E l lam) := GlobalTheory.LatModel.eventually_isPlaceRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JInvariantIntegral
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isIntegral_j_of_isIntLattice : ∀ (d : ℕ) (Λ : PeriodPair), d.Prime → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    IsIntegral ℤ (1728 * Λ.g₂ ^ 3 / latDisc Λ) := by
  intro d Λ hd hΛ
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau Λ
  have hj := g₂_cube_div_eq_modularJ ha h
  have hL : latDisc Λ = Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 := rfl
  rw [hL, hj]
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hsq : w ^ 2 = -(d : ℂ) := by
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  have hwint : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    · simp [Polynomial.eval₂_add, hsq]
  refine isIntegral_modularJ_of_mul_mem (α := w) (fun m hm => ?_) fun x hx ↦ ?_
  · have := congrArg Complex.im hm
    simp [hw] at this
    exact hd.ne_zero this
  · have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ Λ.lattice := fun y ↦ by
      rw [h, Submodule.mem_span_pair]
      simp [mul_right_inj' ha]
    rw [key] at hx ⊢
    obtain ⟨hi, p, q, hpq⟩ := (hΛ _).1 hx
    rw [mul_left_comm]
    refine (hΛ _).2 ⟨hwint.mul hi, -(d : ℚ) * q, p, ?_⟩
    rw [hpq]
    push_cast
    linear_combination (q : ℂ) * hsq

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCalculusStatement
section
set_option autoImplicit false
noncomputable section
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical

namespace GlobalTheory.JetCalcPf

theorem prod_t_list {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I)
    (hc : ∑ i, l.count i ≤ n + 1) :
    (l.map J.t).prod = ((∏ i, (l.count i).factorial : ℕ) : R) • J.b ⟨fun i => l.count i, hc⟩ :=
  GlobalTheory.T.jet_ring_prod_eq_factorial_smul J l hc

theorem prod_t_list_eq_zero {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I)
    (hl : n + 1 < l.length) : (l.map J.t).prod = 0 :=
  GlobalTheory.T.jet_ring_prod_eq_zero_of_long J l hl

theorem card_count_mul {I : Type} [Fintype I] (k : ℕ) (ν : I → ℕ) (hν : ∑ i, ν i = k) :
    (Finset.univ.filter (fun s : Fin k → I => ∀ i, (List.ofFn s).count i = ν i)).card * ∏ i, (ν i).factorial
      = k.factorial :=
  GlobalTheory.T.card_multiset_words_mul_factorial k ν hν

theorem repr_mul_of_coeff {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (F G : MvPowerSeries I ℂ) (x y : J.B)
    (hx : ∀ ν : Idx I n, J.b.repr x ν =
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F)
    (hy : ∀ ν : Idx I n, J.b.repr y ν =
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) G)
    (ν : Idx I n) : J.b.repr (x * y) ν =
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) (F * G) :=
  GlobalTheory.T.jet_ring_repr_mul_power_series J F G x y hx hy ν

theorem iterD_eq {I : Type} [Fintype I] (l : List I) (g : (I → ℂ) → ℂ) :
    iterD l g = GlobalTheory.lineDerivList ℂ (l.map fun i => (Pi.single i 1 : I → ℂ)) g := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [iterD, List.foldr_cons, List.map_cons, GlobalTheory.lineDerivList_cons] at ih ⊢; rw [← ih]; rfl

end GlobalTheory.JetCalcPf

namespace GlobalTheory.JetCalcPf

variable {I : Type} [Fintype I] {n : ℕ}

theorem sum_count (l : List I) : ∑ i, l.count i = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, ih, List.length_cons, beq_iff_eq]
    simp

theorem repr_prod_t_eq_ite_factorial (J : JetRing ℂ I n) (ν : Idx I n) {k : ℕ} (s : Fin k → I) :
    J.b.repr (∏ a, J.t (s a)) ν =
      if (∀ i, (List.ofFn s).count i = ν.1 i) then ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) else 0 := by
  have e : ∏ a, J.t (s a) = ((List.ofFn s).map J.t).prod := by
    rw [List.map_ofFn, List.prod_ofFn]; rfl
  rw [e]
  by_cases hk : k ≤ n + 1
  · have hc : ∑ i, (List.ofFn s).count i ≤ n + 1 := by rw [sum_count, List.length_ofFn]; exact hk
    rw [prod_t_list J _ hc, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hP : ∀ i, (List.ofFn s).count i = ν.1 i
    · have hν : (⟨fun i => (List.ofFn s).count i, hc⟩ : Idx I n) = ν := Subtype.ext (funext hP)
      rw [if_pos hν, if_pos hP, smul_eq_mul, mul_one]
      simp only [hP]
    · rw [if_neg hP, if_neg]
      · simp
      · intro h; exact hP fun i => congrFun (congrArg Subtype.val h) i
  · rw [prod_t_list_eq_zero J _ (by rw [List.length_ofFn]; omega), map_zero, Finsupp.zero_apply, if_neg]
    intro hP
    have h1 := ν.2
    have h2 : ∑ i, ν.1 i = k := by simp only [← hP]; rw [sum_count, List.length_ofFn]
    omega

theorem iFD_eq_iterD {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) {k : ℕ} (s : Fin k → I) (u : List I)
    (h : ∀ i, (List.ofFn s).count i = u.count i) :
    iteratedFDeriv ℂ k f 0 (fun a => (Pi.single (s a) 1 : I → ℂ)) = iterD u f 0 := by
  rw [iterD_eq, ← GlobalTheory.lineDerivList_ofFn hf]
  have hp : (List.ofFn s).Perm u := List.perm_iff_count.2 fun i => h i
  have e : List.ofFn (fun a => (Pi.single (s a) 1 : I → ℂ)) = (List.ofFn s).map fun i => (Pi.single i 1 : I → ℂ) := by
    rw [List.map_ofFn]; rfl
  rw [e]
  exact GlobalTheory.lineDerivList_perm hf (hp.map _)

theorem coeff_jet (J : JetRing ℂ I n) {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (ν : Idx I n) (u : List I)
    (hu : ∀ i, u.count i = ν.1 i) : J.b.repr (jet J f) ν = iterD u f 0 := by
  set K := ∑ i, ν.1 i with hK
  have hKn : K ≤ n + 1 := ν.2
  simp only [jet, GlobalTheory.PeriodFamily.taylor, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, repr_prod_t_eq_ite_factorial]
  rw [Finset.sum_eq_single_of_mem K (Finset.mem_range.2 (by omega))]
  · have step : ∀ s : Fin K → I, ((K.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ K f 0 (fun a => (Pi.single (s a) 1 : I → ℂ))) *
        (if (∀ i, (List.ofFn s).count i = ν.1 i) then ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) else 0) =
        if (∀ i, (List.ofFn s).count i = ν.1 i) then
          (K.factorial : ℂ)⁻¹ * iterD u f 0 * ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) else 0 := by
      intro s
      split_ifs with hP
      · rw [iFD_eq_iterD hf s u fun i => (hP i).trans (hu i).symm]
      · rw [mul_zero]
    simp only [step]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hc := card_count_mul K ν.1 rfl
    have hc' : ((Finset.univ.filter (fun s : Fin K → I => ∀ i, (List.ofFn s).count i = ν.1 i)).card : ℂ) *
        ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) = (K.factorial : ℂ) := by exact_mod_cast hc
    have hK0 : (K.factorial : ℂ) ≠ 0 := by exact_mod_cast K.factorial_ne_zero
    calc _ = ((Finset.univ.filter (fun s : Fin K → I => ∀ i, (List.ofFn s).count i = ν.1 i)).card : ℂ) *
        ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * (K.factorial : ℂ)⁻¹ * iterD u f 0 := by ring
      _ = _ := by rw [hc', mul_inv_cancel₀ hK0, one_mul]
  · intro k _ hk
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [if_neg, mul_zero]
    intro hP
    apply hk
    have := sum_count (List.ofFn s)
    rw [List.length_ofFn] at this
    rw [← this, hK]; simp only [hP]

theorem repr_jet_eq_coeff (J : JetRing ℂ I n) {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (ν : Idx I n) :
    J.b.repr (jet J f) ν =
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) (GlobalTheory.taylor f) := by
  set m : I →₀ ℕ := Finsupp.equivFunOnFinite.symm ν.1 with hm
  have hmi : ∀ i, m i = ν.1 i := fun i => by simp [hm]
  set l := (Finsupp.toMultiset m).toList
  have hl : (l : Multiset I) = Finsupp.toMultiset m := Multiset.coe_toList _
  have hcount : ∀ i, l.count i = ν.1 i := fun i => by
    rw [← hmi, ← Finsupp.count_toMultiset, ← hl, Multiset.coe_count]
  rw [GlobalTheory.taylor_eq_taylorDir, GlobalTheory.coeff_taylorDir_eq_lineDerivList _ hf hl, ← iterD_eq, ← coeff_jet J hf ν l hcount]
  have h0 : ((∏ i, (m i).factorial : ℕ) : ℂ) ≠ 0 := GlobalTheory.cast_prod_factorial_ne_zero m
  simp only [hmi] at h0 ⊢
  rw [mul_inv_cancel_left₀ h0]

theorem jetCalc : JetCalc := by
  intro I _ n J
  refine ⟨fun f hf ν u hu => coeff_jet J hf ν u hu, fun f g hf hg => ⟨?_, ?_⟩, fun f g h => ?_, fun a => ?_,
    fun i => ?_, fun i => ?_, fun s => ?_⟩
  · refine J.b.ext_elem fun ν => ?_
    rw [repr_mul_of_coeff J _ _ _ _ (repr_jet_eq_coeff J hf) (repr_jet_eq_coeff J hg) ν,
      repr_jet_eq_coeff J (hf.mul hg), GlobalTheory.taylor_mul hf hg]
  · refine J.b.ext_elem fun ν => ?_
    rw [map_add, Finsupp.add_apply, repr_jet_eq_coeff J hf, repr_jet_eq_coeff J hg,
      repr_jet_eq_coeff J (hf.add hg), GlobalTheory.taylor_add hf hg, map_add, mul_add]
  · have e : ∀ k, iteratedFDeriv ℂ k f 0 = iteratedFDeriv ℂ k g 0 := fun k => (h.iteratedFDeriv ℂ k).eq_of_nhds
    simp only [jet, GlobalTheory.PeriodFamily.taylor, e]
  · refine J.b.ext_elem fun ν => ?_
    rw [repr_jet_eq_coeff J analyticAt_const, GlobalTheory.taylor_const, MvPowerSeries.coeff_C,
      Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hν : ν = ⟨0, by simp⟩
    · subst hν
      have h0 : Finsupp.equivFunOnFinite.symm (0 : I → ℕ) = 0 := by ext; simp
      simp [h0]
    · rw [if_neg (Ne.symm hν), if_neg, mul_zero, smul_zero]
      intro h; apply hν; apply Subtype.ext; funext i
      have := congrArg (fun m : I →₀ ℕ => m i) h
      simpa using this
  · have ha : AnalyticAt ℂ (fun z : I → ℂ => z i) 0 :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).analyticAt 0
    refine J.b.ext_elem fun ν => ?_
    rw [repr_jet_eq_coeff J ha, GlobalTheory.taylor_coord, MvPowerSeries.coeff_X, JetRing.t, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases hν : ν.1 = Pi.single i 1
    · have h1 : (⟨Pi.single i 1, by simp⟩ : Idx I n) = ν := Subtype.ext hν.symm
      have h2 : Finsupp.equivFunOnFinite.symm ν.1 = Finsupp.single i 1 := by
        ext j; simp [hν, Pi.single_apply, Finsupp.single_apply, eq_comm]
      rw [if_pos h1, if_pos h2, hν, mul_one]
      have : ∀ j, (Pi.single i 1 : I → ℕ) j = 0 ∨ (Pi.single i 1 : I → ℕ) j = 1 := fun j => by
        by_cases hj : j = i <;> simp [hj]
      simp only [Nat.cast_eq_one]
      exact Finset.prod_eq_one fun j _ => by rcases this j with h | h <;> rw [h] <;> rfl
    · have h1 : (⟨Pi.single i 1, by simp⟩ : Idx I n) ≠ ν := fun h => hν (congrArg Subtype.val h).symm
      have h2 : Finsupp.equivFunOnFinite.symm ν.1 ≠ Finsupp.single i 1 := fun h => hν (by
        funext j; have := congrArg (fun m : I →₀ ℕ => m j) h; simpa [Pi.single_apply, Finsupp.single_apply, eq_comm] using this)
      rw [if_neg h1, if_neg h2, mul_zero]
  · rw [J.π_eq, JetRing.t, Module.Basis.repr_self, Finsupp.single_apply, if_neg]
    intro h
    have := congrFun (congrArg Subtype.val h) i
    simp at this
  · have e : ∏ a, J.t (s a) = ((List.ofFn s).map J.t).prod := by
      rw [List.map_ofFn, List.prod_ofFn]; rfl
    rw [e, prod_t_list_eq_zero J _ (by rw [List.length_ofFn]; omega)]

end GlobalTheory.JetCalcPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingGroupMorphismDeRhamLiftStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_group_morphism_de_rham_lift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      (∃ N' : Submodule J.B (Crys J.κ (spMap J.π) X.A), IsCompl (Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}) N') ∧
      ∀ y : HdR X.A, y ∈ Fil X.A ↔ ∃ d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, (GlobalTheory.Published.GrothendieckMessing.crysRedMor J.κ rfl X.A).Corr d y := by
  first | exact @GlobalTheory.LatJet.jetFil_summand_reduces | exact GlobalTheory.LatJet.jetFil_summand_reduces | (intros; apply GlobalTheory.LatJet.jetFil_summand_reduces <;> assumption)
end

