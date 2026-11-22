import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0758
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeMapStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_change_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (hle : c.F ≤ c'.F),
    1 ≤ Dw.p + Dw.q → l.Dvd l' →
    ∃ (r : Xo'.XF c' ⟶ Xo.XF c)
      (h : r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
        pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ spMap (IntermediateField.inclusion hle).toRingHom)
      (r₀ : Xo'.X ⟶ Xo.X) (_ : SABMap Xo'.univ.t Xo.univ.t r₀),
      r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r₀ ∧ IsFinite (pullback.lift r _ h) ∧ Etale (pullback.lift r _ h) ∧
        Surjective (pullback.lift r _ h) := by
  first | exact @GlobalTheory.LevelMapBase.levelMap_coeff_le | exact GlobalTheory.LevelMapBase.levelMap_coeff_le | (intros; apply GlobalTheory.LevelMapBase.levelMap_coeff_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftShearMapSquareZeroAbelianSchemes
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShearLift

variable {S : Scheme.{0}}

theorem isMonHom_mul {H G : Over S} [GrpObj H] [GrpObj G] [IsCommMonObj G] (f g : H ⟶ G) [IsMonHom f]
    [IsMonHom g] : IsMonHom (f * g) :=
  inferInstanceAs (IsMonHom (lift f g ≫ μ[G]))

theorem isCommMonObj_of_isGrpPullback {S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    [IsCommMonObj G] {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G b φ) : IsCommMonObj G' := by
  have key : ∀ {T : Over S'} (x y : T ⟶ G'), x * y = y * x := by
    intro T x y
    let x₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    let y₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (y.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    have e₁ := h.2 T x y x₀ y₀ rfl rfl
    have e₂ := h.2 T y x y₀ x₀ rfl rfl
    have c : x₀ * y₀ = y₀ * x₀ := mul_comm _ _
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← e₁, ← e₂, c]
    · rw [Over.w, Over.w]
  refine ⟨?_⟩
  rw [mul_eq_mul, comp_mul, key]
  simp

theorem isGrpPullback_tensor {S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B]
    [GrpObj A'] [GrpObj B'] {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsGrpPullback A' A b f) (n : IsGrpPullback B' B b g) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsGrpPullback (A' ⊗ B') (A ⊗ B) b h := by
  refine ⟨GlobalTheory.AbDual.isPullback_prod m.1 n.1 h₁ h₂, ?_⟩
  intro T x y x₀ y₀ hx hy
  have e₁ : ((x₀ * y₀) ≫ fst A B).left = ((x * y) ≫ fst A' B').left ≫ f := by
    rw [mul_comp, mul_comp]
    refine m.2 T _ _ _ _ ?_ ?_
    · simp only [Over.comp_left, hx, Category.assoc, h₁]
    · simp only [Over.comp_left, hy, Category.assoc, h₁]
  have e₂ : ((x₀ * y₀) ≫ snd A B).left = ((x * y) ≫ snd A' B').left ≫ g := by
    rw [mul_comp, mul_comp]
    refine n.2 T _ _ _ _ ?_ ?_
    · simp only [Over.comp_left, hx, Category.assoc, h₂]
    · simp only [Over.comp_left, hy, Category.assoc, h₂]
  have p : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [← Over.comp_left, e₁]
    simp only [Over.comp_left, Category.assoc, h₁]
  · rw [← Over.comp_left, e₂]
    simp only [Over.comp_left, Category.assoc, h₂]

theorem exists_lift_shear : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π →
    ∀ (g g' : ℕ) (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (i' : A₀.left ⟶ A'.left) (j' : B₀.left ⟶ B'.left),
    IsGrpPullback A₀ A' (spMap π) i' → IsGrpPullback B₀ B' (spMap π) j' → IsAbelianScheme A' → IsAbelianScheme B' →
    SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g' B'.hom →
    ∀ (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : B₀.left ⟶ Y.left) (h : IsPullback i A₀.hom X.hom (spMap π))
      (k : IsPullback j B₀.hom Y.hom (spMap π)), Smooth X.hom → Smooth Y.hom →
    ∀ (e : Sp R ⟶ X.left) (e' : Sp R ⟶ Y.left), e ≫ X.hom = 𝟙 _ → e' ≫ Y.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ B₀).left ≫ j = spMap π ≫ e' →
    ∀ (l : (A₀ ⊗ B₀).left ⟶ (X ⊗ Y).left), l ≫ (fst X Y).left = (fst A₀ B₀).left ≫ i → l ≫ (snd X Y).left = (snd A₀ B₀).left ≫ j →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀],
    (∀ d ∈ schemeFil (divided₂ hI) A₀ X i h.w, push (divided₂ hI) (spMap π) f₀ d ∈ schemeFil (divided₂ hI) B₀ Y j k.w) →
    ∃ φ : X ⊗ Y ⟶ Y, l ≫ φ.left = ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀).left ≫ j := by
  intro R R₀ _ _ I hI π hπ hker hL g g' A₀ B₀ _ _ A' B' _ _ i' j' hA hB hAab hBab hAg hBg X Y i j h k hX hY
    e e' he he' hie hje l hl₁ hl₂ f₀ _ hf
  haveI : IsCommMonObj B' := hBab.comm
  haveI : IsCommMonObj B₀ := isCommMonObj_of_isGrpPullback hB
  haveI hm : IsMonHom ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀) := isMonHom_mul _ _
  obtain ⟨σ, hσ⟩ : ∃ σ : A₀ ⊗ B₀ ⟶ A₀ ⊗ B₀, σ = lift (fst A₀ B₀) ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀) := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : A₀ ⊗ B₀ ⟶ A₀ ⊗ B₀, τ = lift (fst A₀ B₀) ((fst A₀ B₀ ≫ f₀)⁻¹ * snd A₀ B₀) := ⟨_, rfl⟩
  haveI : IsMonHom σ := by rw [hσ]; infer_instance
  have σ₁ : σ ≫ fst A₀ B₀ = fst A₀ B₀ := by rw [hσ, lift_fst]
  have σ₂ : σ ≫ snd A₀ B₀ = (fst A₀ B₀ ≫ f₀) * snd A₀ B₀ := by rw [hσ, lift_snd]
  have τ₁ : τ ≫ fst A₀ B₀ = fst A₀ B₀ := by rw [hτ, lift_fst]
  have τ₂ : τ ≫ snd A₀ B₀ = (fst A₀ B₀ ≫ f₀)⁻¹ * snd A₀ B₀ := by rw [hτ, lift_snd]
  have hστ : σ ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, τ₁, σ₁, Category.id_comp]
    · rw [Category.assoc, τ₂, comp_mul, GrpObj.comp_inv, ← Category.assoc, σ₁, σ₂, inv_mul_cancel_left,
        Category.id_comp]
  have hτσ : τ ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, σ₁, τ₁, Category.id_comp]
    · rw [Category.assoc, σ₂, comp_mul, ← Category.assoc, τ₁, τ₂, mul_inv_cancel_left, Category.id_comp]
  haveI : IsIso σ := ⟨τ, hστ, hτσ⟩
  haveI : IsIso σ.left :=
    ⟨τ.left, by rw [← Over.comp_left, hστ, Over.id_left], by rw [← Over.comp_left, hτσ, Over.id_left]⟩
  obtain ⟨h₀, h₀₁, h₀₂⟩ := GlobalTheory.AbDual.exists_prod_pullback hA hB
  have hAB : IsGrpPullback (A₀ ⊗ B₀) (A' ⊗ B') (spMap π) h₀ := isGrpPullback_tensor hA hB h₀₁ h₀₂
  have hABab := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A' B' hAab hBab
  have hABg := GlobalTheory.AbDual.smooth_prod hAg hBg
  have hl : IsPullback l (A₀ ⊗ B₀).hom (X ⊗ Y).hom (spMap π) := GlobalTheory.AbDual.isPullback_prod h k hl₁ hl₂
  have hσl : IsPullback (σ.left ≫ l) (A₀ ⊗ B₀).hom (X ⊗ Y).hom (spMap π) := by
    have q := (IsPullback.of_horiz_isIso (fst := σ.left) (snd := (A₀ ⊗ B₀).hom) (f := (A₀ ⊗ B₀).hom)
      (g := 𝟙 _) ⟨by rw [Over.w, Category.comp_id]⟩).paste_horiz hl
    rwa [Category.id_comp] at q
  have hsm : Smooth (X ⊗ Y).hom := by
    haveI := hX
    haveI := hY
    rw [Over.tensorObj_hom, Limits.pullback.condition]
    infer_instance
  have hfil : schemeFil (divided₂ hI) (A₀ ⊗ B₀) (X ⊗ Y) l hl.w =
      schemeFil (divided₂ hI) (A₀ ⊗ B₀) (X ⊗ Y) (σ.left ≫ l) hσl.w := by
    ext d
    rw [GlobalTheory.T.hodgeFiltration_comp_iso_lift_iff R R₀ I (divided₂ hI) π (A₀ ⊗ B₀) (A₀ ⊗ B₀) σ (X ⊗ Y) l hl.w hσl.w d]
    have P := fun d' ↦ GlobalTheory.T.hodgeFiltration_tensor_lifts_iff_projections R R₀ I (divided₂ hI) π A₀ B₀ X Y i j h.w k.w e e' he he' hie hje l hl₁ hl₂ hl.w d'
    rw [P d, P (push (divided₂ hI) (spMap π) σ d)]
    have c₁ : push (divided₂ hI) (spMap π) (fst A₀ B₀) (push (divided₂ hI) (spMap π) σ d) =
        push (divided₂ hI) (spMap π) (fst A₀ B₀) d := by
      rw [← LinearMap.comp_apply, ← push_comp, push_congr _ _ σ₁]
    have c₂ : push (divided₂ hI) (spMap π) (snd A₀ B₀) (push (divided₂ hI) (spMap π) σ d) =
        push (divided₂ hI) (spMap π) f₀ (push (divided₂ hI) (spMap π) (fst A₀ B₀) d) +
          push (divided₂ hI) (spMap π) (snd A₀ B₀) d := by
      rw [← LinearMap.comp_apply, ← push_comp, push_congr _ _ σ₂, push_mul, LinearMap.add_apply, push_comp,
        LinearMap.comp_apply]
    rw [c₁, c₂]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨ha, add_mem (hf _ ha) hb⟩
    · rintro ⟨ha, hb⟩
      refine ⟨ha, ?_⟩
      have := sub_mem hb (hf _ ha)
      rwa [add_sub_cancel_left] at this
  obtain ⟨E, hE⟩ := hL.exists_iso hAB hABab hABg hl hσl hsm hsm hfil
  refine ⟨E.hom ≫ snd X Y, ?_⟩
  rw [Over.comp_left, ← Category.assoc, hE, Category.assoc, hl₂, ← Category.assoc, ← Over.comp_left, σ₂]

end GlobalTheory.ShearLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineSectionsExternalTensorPowerFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_line_sections_externalTensorPower_fibre : ∀ (V K : Type) [CommRing V] [Field K] (f : V →+* K) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR V ⟶ G)) (x : KeyIn K), L.IsLB → IsFibreOf x G L rig θ w f → ∀ N : ℕ, ∃ (X' : Scheme.{0}) (p' : X' ⟶ Sp K) (φ : X' ⟶ (pow G N).left) (L' : LB X') (b : L'.Sec), IsPullback φ p' (pow G N).hom (spMap f) ∧ L'.IsLB ∧ LBIso L' ((boxLB G L N).pull φ) ∧ ∀ s : L'.Sec, ∃ a : K, ∀ i, s.f i = constFn p' _ a * b.f i := by
  first | exact @GlobalTheory.BoxLine.sections_line | exact GlobalTheory.BoxLine.sections_line | (intros; apply GlobalTheory.BoxLine.sections_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldExtendFunctionFieldDerivatio
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

theorem exists_derivation_extend {k A K : Type} [CommRing k] [CommRing A] [CommRing K] [Algebra k A] [Algebra k K]
    [Algebra A K] [IsScalarTower k A K] [Algebra.FormallyEtale A K] (D : Derivation k A A) :
    ∃ D' : Derivation k K K, ∀ a, D' (algebraMap A K a) = algebraMap A K (D a) := by
  let d : Derivation k A K := (Algebra.linearMap A K).compDer D
  let f : Ω[A⁄k] →ₗ[A] K := d.liftKaehlerDifferential
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale k A K
  let g : Ω[K⁄k] →ₗ[K] K := hb.lift f
  refine ⟨g.compDer (KaehlerDifferential.D k K), fun a => ?_⟩
  change g (KaehlerDifferential.D k K (algebraMap A K a)) = _
  rw [← KaehlerDifferential.map_D k k A K]
  erw [hb.lift_eq]
  simp [f, d]

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

theorem germ_appLE_apply {X Y : Scheme.{0}} (f : X ⟶ Y) (V : Y.Opens) (U' : X.Opens) (e : U' ≤ f ⁻¹ᵁ V) (x : X)
    (hx : x ∈ U') (hfx : f x ∈ V) (y : Γ(Y, V)) :
    X.presheaf.germ U' x hx (f.appLE V U' e y) = f.stalkMap x (Y.presheaf.germ V (f x) hfx y) := by
  rw [Scheme.Hom.germ_stalkMap_apply f V x hfx y, Scheme.Hom.appLE]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.germ_res_apply]

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

def derivOfConst {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (D : Derivation ℤ A A)
    (hD : ∀ a, D (φ a) = 0) : (letI := φ.toAlgebra; Derivation k A A) :=
  letI := φ.toAlgebra
  { toFun := D
    map_add' := D.map_add
    map_smul' := fun a x => by
      rw [Algebra.smul_def, D.leibniz, RingHom.algebraMap_toAlgebra, hD, smul_zero, add_zero]
      rfl
    map_one_eq_zero' := D.map_one_eq_zero
    leibniz' := D.leibniz }

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

theorem exists_genDer_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ {N : ℕ} (Dl : Fin N → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), ∃ D : Fin N → GlobalTheory.LogKSDiv.GenDer TF Z, letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ U hU ρ hρ N Dl
  set W := barComp TF.Y Z with hW
  set η₀ := genericPoint (X₀ TF.Y Z) with hη₀
  have hη : W.ι η₀ ∈ U.1 := by
    have e := congrArg (fun f : Sp (X₀ TF.Y Z).functionField ⟶ TF.Y.X => f (IsLocalRing.closedPoint _)) hρ
    simp only [Scheme.Hom.comp_apply] at e
    show W.ι η₀ ∈ (U.1 : Set TF.Y.X)
    rw [← U.2.range_fromSpec]
    refine ⟨_, e.trans ?_⟩
    exact congrArg W.ι Scheme.fromSpecStalk_closedPoint
  have hmono : Mono (LogKS.chart U) := by
    haveI := U.2.isOpenImmersion_fromSpec
    unfold LogKS.chart; infer_instance
  have hρ' : ρ = (TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀).hom := by
    have e : CommRingCat.ofHom ρ = TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀ := by
      apply Spec.map_injective
      rw [← cancel_mono (LogKS.chart U)]
      refine hρ.trans ?_
      have e1 := U.2.fromSpecStalk_eq_fromSpecStalk hη
      rw [Spec.map_comp, Category.assoc, LogKS.chart]
      show (X₀ TF.Y Z).fromSpecStalk η₀ ≫ W.ι = _
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← e1]
      rfl
    exact congrArg CommRingCat.Hom.hom e
  subst hρ'
  have hiso : IsIso (W.ι.stalkMap η₀) := inferInstance
  letI iA : Algebra c.F Γ(TF.Y.X, U.1) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1).toAlgebra
  letI iK : Algebra c.F (X₀ TF.Y Z).functionField := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  letI iAK : Algebra Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField :=
    (TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀).hom.toAlgebra
  have htow : IsScalarTower c.F Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, GlobalTheory.Cartier.constFn, GlobalTheory.Cartier.fnOf,
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, CommRingCat.hom_comp]
    refine (germ_appLE_apply (s₀ TF.Y Z) ⊤ ⊤ _ (genericPoint (X₀ TF.Y Z)) trivial trivial _).trans ?_
    refine Eq.trans ?_ (congrArg (W.ι.stalkMap η₀).hom
      (germ_appLE_apply TF.Y.s ⊤ U.1 _ (W.ι η₀) hη trivial _)).symm
    rw [show s₀ TF.Y Z = W.ι ≫ TF.Y.s from rfl, Scheme.Hom.stalkMap_comp]
    rfl
  letI iS : Algebra Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk (W.ι η₀)) :=
    TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf (U := U.1) ⟨W.ι η₀, hη⟩
  have hloc := U.2.isLocalization_stalk ⟨W.ι η₀, hη⟩
  let eK : TF.Y.X.presheaf.stalk (W.ι η₀) ≃ₐ[Γ(TF.Y.X, U.1)] (X₀ TF.Y Z).functionField :=
    AlgEquiv.ofRingEquiv (f := (asIso (W.ι.stalkMap η₀)).commRingCatIsoToRingEquiv) fun _ => rfl
  haveI := IsLocalization.isLocalization_of_algEquiv (U.2.primeIdealOf ⟨W.ι η₀, hη⟩).asIdeal.primeCompl eK
  haveI : Algebra.FormallyEtale Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField :=
    Algebra.FormallyEtale.of_isLocalization (U.2.primeIdealOf ⟨W.ι η₀, hη⟩).asIdeal.primeCompl
  choose D hD using fun j => exists_derivation_extend (k := c.F) (K := (X₀ TF.Y Z).functionField)
    (derivOfConst (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1) (Dl j).1 (Dl j).2.1)
  exact ⟨D, fun j r => hD j r⟩

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFiberIsAlgebraicResidueFieldOfLftStatement
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
open GlobalTheory.QCoh

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_fiber_isAlgebraic_residueField_of_lft : ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) [LocallyOfFiniteType π] (y₀ : Y), ∃ y : Y, π y = π y₀ ∧ (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) := by
  first | exact @GlobalTheory.exists_mem_fiber_isAlgebraic_residueField | exact GlobalTheory.exists_mem_fiber_isAlgebraic_residueField | (intros; apply GlobalTheory.exists_mem_fiber_isAlgebraic_residueField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelTangentOfPullbackTangentStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_modelTangent_of_pullback_tangent : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x) (w : epsOver V V ⟶ G.G), IsTan w → ∃ v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ := by
  first | exact @GlobalTheory.TanPull.exists_tanM_of_isTan | exact GlobalTheory.TanPull.exists_tanM_of_isTan | (intros; apply GlobalTheory.TanPull.exists_tanM_of_isTan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoHom
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ConeMono

noncomputable section

namespace GlobalTheory.MonoHom

variable {X : Type} [AddCommGroup X] {K : Type} [Field K]

def pform {ι : Type} (e : Module.Basis ι ℤ X) (i j : ι) : LinearMap.BilinForm ℤ X :=
  (e.coord i).smulRight (e.coord j)

@[simp] theorem pform_apply {ι : Type} (e : Module.Basis ι ℤ X) (i j : ι) (x y : X) :
    pform e i j x y = e.coord i x * e.coord j y := by
  simp [pform]

end GlobalTheory.MonoHom

namespace GlobalTheory.MonoHom

end GlobalTheory.MonoHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeatPrimeLevelAutSubgroupUnipotentStatement
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
theorem _root_.GlobalTheory.T.exists_neatPrime_levelAutSubgroup_unipotent : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H), D.host.g 0 * D.host.g 1 ∣ l.M → (∀ k, Dw.p + Dw.q + 1 < D.host.g k) → ∀ (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ (I : Ideal (𝓞 D.host.E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) ∧ l.Mb ≤ I ∧ ∀ γ ∈ S, UnipAt I γ := by
  first | exact @GlobalTheory.OrbitSep.exists_neatPrime_unipAt | exact GlobalTheory.OrbitSep.exists_neatPrime_unipAt | (intros; apply GlobalTheory.OrbitSep.exists_neatPrime_unipAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianLocalOfOrderFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_noetherianLocal_of_orderFunction : ∀ (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (t : B) (i : A →+* Ω), Function.Injective f → Function.Injective i → t ≠ 0 → (∀ b, ev b = 0 ↔ t ∣ b) → (∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C), Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  first | exact @GlobalTheory.MBLow.exists_localRing_of_order | exact GlobalTheory.MBLow.exists_localRing_of_order | (intros; apply GlobalTheory.MBLow.exists_localRing_of_order <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroTraceElementStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_trace_element : ∀ (E : Type) [Field E] [NumberField E], ∃ (d : ℕ) (c θ : Fin d → 𝓞 E),
    (∀ o : 𝓞 E, ∑ j, c j ⊗ₜ[ℤ] (o * θ j) = ∑ j, (o * c j) ⊗ₜ[ℤ] θ j) ∧ ∑ j, c j * θ j ≠ 0 := by
  first | exact @GlobalTheory.intCasimir_exists | exact GlobalTheory.intCasimir_exists | (intros; apply GlobalTheory.intCasimir_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringInValuationSubringStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_finiteType_subring_in_valuationSubring : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := by
  first | exact @GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring | exact GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring | (intros; apply GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldFrameValueNeZeroOfComplexStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberFieldFrame_value_ne_zero_of_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K]
    (y : FrPt Xo c K) (e : Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ (σ : c.F →+* ℂ) (σ₁ : K →ₐ[c.F] CAt σ)
    (w : FrPt Xo c (CAt σ)), spMap σ₁.toRingHom ≫ y.x = w.x → evR Xo c F w ≠ 0 →
    ∃ y' : FrPt Xo c K, y'.x = y.x ∧ evR Xo c F y' ≠ 0 := by
  first | exact @GlobalTheory.FrameDenseZ.exists_frame_evR_ne_zero_of_complex | exact GlobalTheory.FrameDenseZ.exists_frame_evR_ne_zero_of_complex | (intros; apply GlobalTheory.FrameDenseZ.exists_frame_evR_ne_zero_of_complex <;> assumption)
end

