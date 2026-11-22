import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximateSeriesLeadingTermFourierSystem
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulIncl
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellSectionOverBasicOpenInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2701

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUniformization
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem exists_isAH_diag : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → ∀ u : HolUnif X.A (X.diag c) (Module.finrank ℚ F),
    ∃ (u' : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (Hm : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ)
      (χ : u'.Λ → ℂ), u'.ex = u.ex ∧ u'.IsAH Hm χ := by
  intro F _ _ _ 𝔠 X c hc u
  obtain ⟨u', Hm, χ, hex, hH, hχ, hfr⟩ := GlobalTheory.T.exists_hermitian_theta_factor X.A X.ab (X.diag c) (pull_isLB (X.isLB c) _) _ u
  exact ⟨u', Hm, χ, hex, hH,
    GlobalTheory.T.appell_humbert_factor_of_hermitian X.A X.ab (X.diag c) (pull_isLB (X.isLB c) _) (X.pos c hc) _ u' Hm χ hH hχ hfr, hχ, hfr⟩

end GlobalTheory.RealMult.Obj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximateSeriesLeadingTermFourierSystemStatement
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approximate_series_leading_term_fourierSystem : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (bar : O → O), BddAct bar → ∀ (q : ℕ) (φ : InvFun O), IsPolFan bar q φ → ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∀ (N₁ : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y₀ : Φ.Y) (γ : Fin (Φ.m y₀) → LinearMap.BilinForm ℤ (Φ.X y₀)) (M : ℕ), 1 ≤ M → (∀ i, Φ.δ y₀ i = (M : ℤ) • γ i) → ∀ (d l : ℕ) (a : Fin l × Fin s → Φ.X y₀), Dominant bar φ d N₁ W γ a → ∀ (c : Fin l → Φ.Q) (e : ℕ), ∃ f : A, Φ.OrdGe φ d e f ∧ Φ.Leads y₀ a c e f := by
  first | exact @GlobalTheory.Poinc.approx_of_vsys | exact GlobalTheory.Poinc.approx_of_vsys | (intros; apply GlobalTheory.Poinc.approx_of_vsys <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAwaySpreadPointLocalizationAtPrime
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SpreadPoint

set_option backward.isDefEq.respectTransparency false

theorem isStalkMap_atPrime (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    GlobalTheory.UPoinc.LocSpread.IsStalkMap (algebraMap R (Localization.AtPrime 𝔭)) := by
  let x : PrimeSpectrum R := ⟨𝔭, inferInstance⟩
  let T := (Spec.structureSheaf R).presheaf.stalk x
  haveI : IsLocalization x.asIdeal.primeCompl T := StructureSheaf.IsLocalization.to_stalk R x
  let e : T ≃ₐ[R] Localization.AtPrime 𝔭 := IsLocalization.algEquiv x.asIdeal.primeCompl T _
  refine ⟨x, asIso (Spec.map (e.toRingEquiv.toCommRingCatIso).hom), ?_, fun a ha =>
    IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨a, ha⟩ : 𝔭.primeCompl)⟩
  rw [Spec.fromSpecStalk_eq', asIso_hom, ← Spec.map_comp]
  congr 1
  ext a
  exact e.commutes a

end GlobalTheory.SpreadPoint

theorem GlobalTheory.SpreadPoint.exists_away : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (q : X ⟶ Sp B) [LocallyOfFinitePresentation q] (R : Type) [CommRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (f₀ : Sp (Localization.AtPrime 𝔭) ⟶ X), f₀ ≫ q = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) → ∃ r ∉ 𝔭, ∃ (j : Localization.Away r →+* Localization.AtPrime 𝔭) (f : Sp (Localization.Away r) ⟶ X), j.comp (algebraMap R (Localization.Away r)) = algebraMap R (Localization.AtPrime 𝔭) ∧ f ≫ q = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ spMap j ≫ f = f₀ := by
  intro B _ X q _ R _ β 𝔭 _ f₀ hf₀
  set σ := algebraMap R (Localization.AtPrime 𝔭)
  have hσ := GlobalTheory.SpreadPoint.isStalkMap_atPrime R 𝔭
  let q' : pullback q (spMap β) ⟶ Sp R := pullback.snd q (spMap β)
  have hP : IsPullback (spMap σ) (𝟙 _) (𝟙 (Sp R)) (spMap σ) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hcomp : ∀ {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (f : A →+* C) (g : C →+* D),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm
  let u₀ : Sp (Localization.AtPrime 𝔭) ⟶ pullback q (spMap β) :=
    pullback.lift f₀ (spMap σ) (by rw [hf₀, hcomp])
  obtain ⟨a, ha, H⟩ := GlobalTheory.UPoinc.LocSpread.exists_hom hσ (𝟙 (Sp R)) q' hP u₀ (by rw [Category.comp_id]; exact pullback.lift_snd _ _ _)
  have ha' : a ∉ 𝔭 := by
    intro h
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 a).1 ha h
  let g := algebraMap R (Localization.Away a)
  obtain ⟨u, hu, hu₀⟩ := H (Localization.Away a) g (IsLocalization.Away.algebraMap_isUnit a) (Sp (Localization.Away a))
    (spMap g) (𝟙 _) (by simp)
  let j : Localization.Away a →+* Localization.AtPrime 𝔭 := IsLocalization.Away.lift a ha
  have hj : j.comp g = σ := IsLocalization.Away.lift_comp _ _
  refine ⟨a, ha', j, u ≫ pullback.fst q (spMap β), hj, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (u ≫ q') ≫ _ = _
    rw [hu, Category.comp_id, hcomp]
  · rw [← Category.assoc, hu₀ (spMap j) (by rw [hcomp, hj])]
    exact pullback.lift_fst _ _ _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedBimultiplicativeGeneratorLambdaInvStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_balanced_bimultiplicative_generator_lambda_inv : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (M : RigLB B) (cub : CubicalStr B M) (O : Type) [CommRing O] [StarRing O] (act : RingAct B O),
    (∀ a : O, RosatiAdj B M.L (act.act a) (act.act (star a))) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Projective O X] [Module.Finite O X] [Module.Free ℤ X]
      (c : X → (𝟙_ (Over (Sp R)) ⟶ B)), (∀ y y', c (y + y') = c y * c y') → (∀ (a : O) (y : X), c (a • y) = c y ≫ act.act a) →
    ∃ τ : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ := by
  first | exact @GlobalTheory.UBalA.exists_balTau | exact GlobalTheory.UBalA.exists_balTau | (intros; apply GlobalTheory.UBalA.exists_balTau <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeSemiAbelianCubicalPolarisedDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_semiAbelian_cubical_polarised_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R' → FinExt ρ → ∃ (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), IsSemiAbelian G₁ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) := by
  first | exact @GlobalTheory.Mum.exists_baseChange_semiAbelian_data | exact GlobalTheory.Mum.exists_baseChange_semiAbelian_data | (intros; apply GlobalTheory.Mum.exists_baseChange_semiAbelian_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseGlobalUnitAbelianSchemeBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TwoTors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_globalUnit_abelianScheme_baseChange : ∀ {S X : Scheme.{0}} (A Z : Over S) [GrpObj A], IsAbelianScheme A → ∀ (p : X ⟶ A.left) (q : X ⟶ Z.left), IsPullback p q A.hom Z.hom → ∀ D : Γ(X, ⊤)ˣ, ∃ c : Γ(Z.left, ⊤)ˣ, GlobalTheory.CharKer.pullTop q c = D := by
  first | exact @GlobalTheory.CharKer.exists_pullTop_of_isPullback | exact GlobalTheory.CharKer.exists_pullTop_of_isPullback | (intros; apply GlobalTheory.CharKer.exists_pullTop_of_isPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeneratingSectionAllFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_basicOpen_genSec_fibres : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB →
    ∀ (g : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), PolFib G L g x →
    ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧
      ∃ θ : SecAt G L (spMap (algebraMap R (Localization.Away r)) ≫ x),
        ∀ (K : Type) [Field K] (i : Localization.Away r →+* K), IsGenSec G L _ (SecAt.pull G L θ i) := by
  intro S G _ L hL g R _ _ x hx p
  obtain ⟨P, α, -, hp, w, hw⟩ := hx
  have hS : SecBaseChangeAnySt := GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny
  obtain ⟨V, hpV, hV⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near hS P p
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := ((V : Set (Sp R)) : Set (PrimeSpectrum R))) hpV V.isOpen
  let j := algebraMap R (Localization.Away r)
  have hrange : Set.range (spMap j) ⊆ (V : Set (Sp R)) := by
    intro y hy
    apply hrV
    obtain ⟨z, rfl⟩ := hy
    have hz : PrimeSpectrum.comap j z ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨z, rfl⟩
    exact hz
  obtain ⟨th, hth⟩ := hV (Localization.Away r) (spMap j) hrange
  have hτ : (𝟙 (Sp (Localization.Away r)) : (Over.mk (spMap j)).left ⟶ (Over.mk (spMap j ≫ x)).left) ≫
      (Over.mk (spMap j ≫ x)).hom = (Over.mk (spMap j)).hom ≫ x := Category.id_comp _
  obtain ⟨θ, hθ⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp (T := Over.mk (spMap j)) (T₀ := Over.mk (spMap j ≫ x))
    (𝟙 _) hτ hw hL P.isLB (a := ((1 : ℕ) : ℤ)) th
  refine ⟨r, hpr, θ, fun K _ i => ?_⟩
  have hτ' : (𝟙 (Sp K) : (Over.mk (spMap i ≫ spMap j)).left ⟶ (Over.mk (spMap i ≫ spMap j ≫ x)).left) ≫
      (Over.mk (spMap i ≫ spMap j ≫ x)).hom = (Over.mk (spMap i ≫ spMap j)).hom ≫ x := by
    simp [Category.assoc]
  let ξ : Over.mk (spMap i ≫ spMap j) ⟶ Over.mk (spMap j) := Over.homMk (spMap i) rfl
  let ξ₀ : Over.mk (spMap i ≫ spMap j ≫ x) ⟶ Over.mk (spMap j ≫ x) := Over.homMk (spMap i) rfl
  have hξ : (𝟙 (Sp K) : (Over.mk (spMap i ≫ spMap j)).left ⟶ (Over.mk (spMap i ≫ spMap j ≫ x)).left) ≫ ξ₀.left =
      ξ.left ≫ (𝟙 (Sp (Localization.Away r)) : (Over.mk (spMap j)).left ⟶ (Over.mk (spMap j ≫ x)).left) :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hrel : GlobalTheory.ThetaPtMove.SecRel hp _ hτ' w (VVRank.pullS P.A ((1 : ℕ) : ℤ) ξ th)
      (VVRank.pullS G ((1 : ℕ) : ℤ) ξ₀ θ) :=
    GlobalTheory.Ex.OneGen.SecRel.pullS hp _ hτ hθ (T' := Over.mk (spMap i ≫ spMap j))
      (T₀' := Over.mk (spMap i ≫ spMap j ≫ x)) _ hτ' ξ ξ₀ hξ
  have : IsAffine (Over.mk (spMap j)).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap i ≫ spMap j)).left := inferInstanceAs (IsAffine (Spec _))
  have hg : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 ξ th) :=
    GlobalTheory.EmbPull.isGenSec_pullS P hS ξ hth
  have hg' : IsGenSec P.A P.L ((1 : ℕ) : ℤ) (VVRank.pullS P.A ((1 : ℕ) : ℤ) ξ th) := hg
  have : IsIso (C := Scheme.{0}) (X := (Over.mk (spMap i ≫ spMap j)).left)
      (Y := (Over.mk (spMap i ≫ spMap j ≫ x)).left) (𝟙 (Sp K)) := IsIso.id _
  have h2 : IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G ((1 : ℕ) : ℤ) ξ₀ θ) :=
    GlobalTheory.ThetaPtUp.isGenSec_up hp _ hτ' hw hL P.isLB hrel hg'
  exact h2

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenIntegralOfIntegralAtPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem chart_res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem chart_res_app {X Y : Scheme.{0}} (α : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (Y.presheaf.map (homOfLE (α.preimage_mono h)).op).hom ((α.app U).hom x) =
      (α.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]; rfl

theorem isIntegralElem_of_square {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : C →+* D) (a : A →+* C) (b : B →+* D) (h : g.comp a = b.comp f) {x : B}
    (hx : f.IsIntegralElem x) : g.IsIntegralElem (b x) := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map a, hp.map a, ?_⟩
  rw [Polynomial.eval₂_map, h, ← Polynomial.hom_eval₂, hpx, map_zero]

theorem intAt_chart {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (ζ : X) :
    IntAt L α s ζ → ∀ (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ζ ∈ W →
      ∃ c : Γ(X, W), ζ ∈ X.basicOpen c ∧ (α.app (X.basicOpen c)).hom.IsIntegralElem
        ((Y.presheaf.map (homOfLE (α.preimage_mono (X.basicOpen_le c))).op).hom (chartVal L α s j W hW)) := by
  intro hint j W hW hWa hζW
  obtain ⟨j', W', hW', hζW', hW'a, hint'⟩ := hint
  obtain ⟨c, hcle, hζc⟩ := hWa.exists_basicOpen_le (V := W ⊓ W') ⟨ζ, hζW, hζW'⟩ hζW
  refine ⟨c, hζc, ?_⟩
  have hBW : X.basicOpen c ≤ W := hcle.trans inf_le_left
  have hBW' : X.basicOpen c ≤ W' := hcle.trans inf_le_right
  have hBV : α ⁻¹ᵁ X.basicOpen c ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) ⊓
      LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j') :=
    le_inf ((α.preimage_mono hBW).trans (locInt_le_chart L α j W hW))
      ((α.preimage_mono hBW').trans (locInt_le_chart L α j' W' hW'))
  have hBjj : X.basicOpen c ≤ L.U j ⊓ L.U j' := le_inf (hBW.trans hW) (hBW'.trans hW')
  have key := congrArg (Y.presheaf.map (homOfLE hBV).op).hom (s.compat (fun _ => j) (fun _ => j'))
  erw [chart_res_res, map_mul, chart_res_res] at key
  have ht : (Y.presheaf.map (homOfLE hBV).op).hom
      ((LB.LinComb L (K := Fin 1) (fun _ => α) (fun _ => (k : ℤ))).g (fun _ => j) (fun _ => j')).val =
      (α.app (X.basicOpen c)).hom (((X.presheaf.map (homOfLE hBjj).op).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) ^ k) := by
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, res, pullU, Units.coe_map, map_pow]
    congr 1
    erw [Units.coe_map, Units.coe_map]
    erw [chart_res_res, ← chart_res_app α hBjj]
    rfl
  have hj' : (α.app (X.basicOpen c)).hom.IsIntegralElem
      ((Y.presheaf.map (homOfLE (α.preimage_mono hBW')).op).hom (chartVal L α s j' W' hW')) :=
    isIntegralElem_of_square (α.app W').hom (α.app (X.basicOpen c)).hom (X.presheaf.map (homOfLE hBW').op).hom
      (Y.presheaf.map (homOfLE (α.preimage_mono hBW')).op).hom (RingHom.ext fun x => (chart_res_app α hBW' x).symm) hint'
  rw [chartVal] at hj' ⊢
  erw [chart_res_res] at hj' ⊢
  erw [key, ht]
  exact RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) hj'

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellChartFrameEigenbasis
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.LogPole.CellNear

theorem vecAt_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (k : TF.X.F.J) {S : Type}
    [CommRing S] {z₁ z₂ : Sp S ⟶ TF.X.YY} (h : z₁ = z₂) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ TF.X.F.U k) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ TF.X.F.U k)
    {x : Sp S ⟶ TF.Y.X} (hx₁ : z₁ ≫ TF.X.π = x) (hx₂ : z₂ ≫ TF.X.π = x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    TF.X.F.vecAt k z₁ h₁ hx₁ σ i = TF.X.F.vecAt k z₂ h₂ hx₂ σ i := by
  subst h; rfl

theorem exists_frameMat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c)
    (U : TF.Y.X.affineOpens) {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (hv : IsEigBasis TF U e v) (k : TF.X.F.J)
    {W₀ : (Y₀ TF.X Z).Opens} (hW₀ : IsAffineOpen W₀) (hW₀U : W₀ ≤ toBase TF Z ⁻¹ᵁ U.1)
    (hW₀k : W₀ ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k) :
    ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W₀),
      (∀ σ, IsUnit (C σ).det) ∧ IsFrameMat TF Z U e v W₀ k C := by
  have hU0 : ⊤ ≤ (FlagMod.tau hW₀ ≫ toBase TF Z) ⁻¹ᵁ U.1 := fun q hq => FlagMod.tau_le hW₀ hW₀U hq
  have hk0 : ⊤ ≤ (FlagMod.tau hW₀ ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun q hq => FlagMod.tau_le hW₀ hW₀k hq
  have hx0 : (FlagMod.tau hW₀ ≫ inc₀ TF.X Z) ≫ TF.X.π = FlagMod.tau hW₀ ≫ toBase TF Z := Category.assoc _ _ _
  obtain ⟨C, hC⟩ := GlobalTheory.T.frameVector_isCombination_eigenbasis_flagSpace_point E H Dw l Xo c TF Z U n e v hv k _ (FlagMod.tau hW₀) hU0 hk0 hx0
  refine ⟨C, fun σ => GlobalTheory.T.isUnit_det_frame_eigenbasis_block_at_point E H Dw l Xo c TF Z U n e v hv k _ (FlagMod.tau hW₀) hU0 hk0 hx0 σ (C σ)
    (hC σ), ?_⟩
  intro S _ z hz hU hk hx σ i
  have hzφ : spMap (ev z W₀ hz) ≫ FlagMod.tau hW₀ = z := FlagMod.spMap_ev z hW₀ hz
  have eb : spMap (ev z W₀ hz) ≫ FlagMod.tau hW₀ ≫ toBase TF Z = z ≫ toBase TF Z := by
    rw [← Category.assoc, hzφ]
  have hb := (GlobalTheory.TanBaseChange.tan_comb_baseChange E H TF.Y.X TF.Y.t _ S (ev z W₀ hz)
    (FlagMod.tau hW₀ ≫ toBase TF Z) (z ≫ toBase TF Z) eb).2 _
    (fun j => spMap (dualMap (ev (FlagMod.tau hW₀ ≫ toBase TF Z) U.1 hU0)) ≫ v (e ⟨σ, j⟩)) (C σ i) _ (hC σ i)
  have e1 : ∀ j, spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v j =
      spMap (dualMap (ev z W₀ hz)) ≫ spMap (dualMap (ev (FlagMod.tau hW₀ ≫ toBase TF Z) U.1 hU0)) ≫ v j := by
    intro j
    rw [← Category.assoc (spMap (dualMap (ev z W₀ hz))), TanBaseChange.spMap_comp_spMap', ← FlagMod.dualMap_comp,
      ← FlagMod.ev_spMap (ev z W₀ hz) (FlagMod.tau hW₀ ≫ toBase TF Z) U.1 hU0 (FlagMod.le_preimage_comp _ hU0),
      FlagMod.ev_congr eb U.1 (FlagMod.le_preimage_comp _ hU0) hU]
  have hz' : ⊤ ≤ (spMap (ev z W₀ hz) ≫ FlagMod.tau hW₀ ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k :=
    FlagMod.le_preimage_comp _ hk0
  have hx' : (spMap (ev z W₀ hz) ≫ FlagMod.tau hW₀ ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z := by
    rw [← eb]; simp only [toBase, Category.assoc]
  have e2 : (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left =
      spMap (dualMap (ev z W₀ hz)) ≫ (tv (TF.X.F.vecAt k (FlagMod.tau hW₀ ≫ inc₀ TF.X Z) hk0 hx0 σ i)).left := by
    rw [← FlagMod.tanPull_left (ev z W₀ hz) eb, FlagMod.Frames.tanPull_vecAt TF.X.F k (ev z W₀ hz) _ hk0 hz' hx0 hx' eb,
      vecAt_congr TF k (by rw [← Category.assoc, hzφ]) hz' hk hx' hx]
  rw [funext fun j => e1 (e ⟨σ, j⟩), e2]
  exact hb

theorem isUnit_prod_univ {R ι : Type} [CommRing R] [Fintype ι] (f : ι → R) (h : ∀ i, IsUnit (f i)) :
    IsUnit (∏ i, f i) :=
  Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => h i

theorem isUnit_of_isUnit_prod_univ {R ι : Type} [CommRing R] [Fintype ι] (f : ι → R) (h : IsUnit (∏ i, f i))
    (i : ι) : IsUnit (f i) :=
  isUnit_of_dvd_unit (Finset.dvd_prod_of_mem f (Finset.mem_univ i)) h

end GlobalTheory.LogPole.CellNear

open GlobalTheory.LogPole.CellNear in

theorem GlobalTheory.LogPole.exists_isCell_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (y : Y₀ TF.X Z), toBase TF Z y ∈ U.1 → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∃ (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsEigBasis TF U e' v ∧ y ∈ W ∧ W ≤ V ∧ IsCell TF Z U e' v W k L N := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv y hyU V hyV
  obtain ⟨k, hk⟩ : ∃ k, inc₀ TF.X Z y ∈ TF.X.F.U k := by
    have : inc₀ TF.X Z y ∈ ⨆ k, TF.X.F.U k := by rw [TF.X.F.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hyW₀, hW₀le⟩ := (Y₀ TF.X Z).isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((V ⊓ toBase TF Z ⁻¹ᵁ U.1 ⊓ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k : (Y₀ TF.X Z).Opens) : Set (Y₀ TF.X Z)) from
      ⟨⟨hyV, hyU⟩, hk⟩) (V ⊓ toBase TF Z ⁻¹ᵁ U.1 ⊓ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k).isOpen
  have hW₀V : W₀ ≤ V := fun q hq => (hW₀le hq).1.1
  have hW₀U : W₀ ≤ toBase TF Z ⁻¹ᵁ U.1 := fun q hq => (hW₀le hq).1.2
  have hW₀k : W₀ ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k := fun q hq => (hW₀le hq).2
  obtain ⟨C, hCu, hC⟩ := exists_frameMat TF Z U e v hv k hW₀ hW₀U hW₀k
  let g := ((Y₀ TF.X Z).presheaf.germ W₀ y hyW₀).hom
  have hperm : ∀ σ : E →+* ℂ, ∃ w : Equiv.Perm (Fin (Dw.mult σ)), ∀ (m : ℕ) (hm : m ≤ Dw.mult σ),
      IsUnit ((((C σ).map g).submatrix id w).submatrix (Fin.castLE hm) (Fin.castLE hm)).det := fun σ =>
    GlobalTheory.exists_perm_isUnit_leading_minors_localRing _ (by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (hCu σ).map g)
  choose p hp using hperm
  let mn : (σ : E →+* ℂ) → Fin (Dw.mult σ + 1) → Γ(Y₀ TF.X Z, W₀) := fun σ m =>
    (((C σ).submatrix id (p σ)).submatrix (Fin.castLE (Nat.lt_succ_iff.mp m.2))
      (Fin.castLE (Nat.lt_succ_iff.mp m.2))).det
  have hmap : ∀ {R' : Type} [CommRing R'] (φ : Γ(Y₀ TF.X Z, W₀) →+* R') (σ : E →+* ℂ) (m : Fin (Dw.mult σ + 1)),
      φ (mn σ m) = ((((C σ).map φ).submatrix id (p σ)).submatrix (Fin.castLE (Nat.lt_succ_iff.mp m.2))
        (Fin.castLE (Nat.lt_succ_iff.mp m.2))).det := by
    intro R' _ φ σ m
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, ← Matrix.submatrix_map]
  let f := ∏ σ, ∏ m, mn σ m
  have hyf : y ∈ (Y₀ TF.X Z).basicOpen f := by
    rw [Scheme.mem_basicOpen _ f y hyW₀]
    show IsUnit (g f)
    rw [map_prod]
    refine isUnit_prod_univ _ fun σ => ?_
    rw [map_prod]
    refine isUnit_prod_univ _ fun m => ?_
    rw [hmap]
    exact hp σ m (Nat.lt_succ_iff.mp m.2)
  have hWW₀ : (Y₀ TF.X Z).basicOpen f ≤ W₀ := (Y₀ TF.X Z).basicOpen_le f
  have hWa : IsAffineOpen ((Y₀ TF.X Z).basicOpen f) := hW₀.basicOpen f
  have hrf : IsUnit (resG (Y₀ TF.X Z) hWW₀ f) := (Y₀ TF.X Z).toRingedSpace.isUnit_res_basicOpen f
  have hrm : ∀ σ m, IsUnit (resG (Y₀ TF.X Z) hWW₀ (mn σ m)) := by
    intro σ m
    rw [map_prod] at hrf
    have h1 := isUnit_of_isUnit_prod_univ _ hrf σ
    rw [map_prod] at h1
    exact isUnit_of_isUnit_prod_univ _ h1 m
  have hLU : ∀ σ : E →+* ℂ, ∃ L N : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, (Y₀ TF.X Z).basicOpen f),
      GlobalTheory.ShFam.Cell.IsLowInv L ∧ (∀ i j, j < i → N i j = 0) ∧ (∀ i, N i i = 1) ∧
        ((C σ).map (resG (Y₀ TF.X Z) hWW₀)).submatrix id (p σ) = L * N := fun σ =>
    GlobalTheory.ShFam.Cell.exists_lowInv_mul_upperUni_of_leadingMinors _ _ fun m hm => by
      have := hrm σ ⟨m, Nat.lt_succ_of_le hm⟩
      rw [hmap] at this
      exact this
  choose L N hL hN hNd hLN using hLU
  refine ⟨permE e p, (Y₀ TF.X Z).basicOpen f, k, L, N, isEigBasis_permE p hv, hyf, hWW₀.trans hW₀V,
    isCell_of_isFrameMat hWa (hWW₀.trans hW₀U) (hWW₀.trans hW₀k) (fun σ => (hL σ).1) (fun σ => (hL σ).2) hN hNd ?_⟩
  have h1 := isFrameMat_mono hWW₀ (isFrameMat_permE p hC)
  have e1 : (fun σ => ((C σ).submatrix id (p σ)).map (resG (Y₀ TF.X Z) hWW₀)) = fun σ => L σ * N σ :=
    funext fun σ => (Matrix.submatrix_map _ _ _ _).symm.trans (hLN σ)
  rw [e1] at h1
  exact h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellSectionOverBasicOpenInteriorStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bigCellSection_over_basicOpen_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (a : Γ(TF.Y.X, U.1)), TF.Y.X.basicOpen a ≤ LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U → (∃ w : Y₀ TF.X Z, w ∈ W ∧ w ∈ U₀ TF.X Z ∧ toBase TF Z w ∈ TF.Y.X.basicOpen a) → ∃ z₁ : Sp (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) ⟶ Y₀ TF.X Z, ⊤ ≤ z₁ ⁻¹ᵁ U₀ TF.X Z ∧ (∃ hU : ⊤ ≤ (z₁ ≫ toBase TF Z) ⁻¹ᵁ U.1, ∀ r, ev (z₁ ≫ toBase TF Z) U.1 hU r = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) (MvPolynomial.C r)) ∧ ((z₁ ⁻¹ᵁ W : TopologicalSpace.Opens _) : Set (Sp (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))))).Nonempty ∧ ∀ (S : Type) [CommRing S] (ψ : Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) →+* S) (hW : ⊤ ≤ (spMap ψ ≫ z₁) ⁻¹ᵁ W) (σ : E →+* ℂ), ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ i j, i < j → b i j = 0) ∧ ∀ i j, ψ (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) _ (if h : i < j then MvPolynomial.X ⟨σ, ⟨(i, j), h⟩⟩ else if i = j then 1 else 0)) = ∑ m, b i m * ev (spMap ψ ≫ z₁) W hW ((L σ * N σ) m j) := by
  first | exact @GlobalTheory.LogPole.exists_cell_section_away | exact GlobalTheory.LogPole.exists_cell_section_away | (intros; apply GlobalTheory.LogPole.exists_cell_section_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleExtensionTranslateOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundle_extension_translate_open : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L.IsLB → ExtLam G L PP → ∀ (O : G.left.Opens) (N : LB O.toScheme), N.IsLB → LBIso (N.pull (pullback.fst O.ι (pullback.fst G.hom (jK R)))) (L.pull (pullback.snd O.ι (pullback.fst G.hom (jK R)))) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, ∃ N' : LB ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).toScheme, N'.IsLB ∧ LBIso (N'.pull (pullback.fst ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R)))) (L.pull (pullback.snd ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R)))) := by
  first | exact @GlobalTheory.Mum.exists_ext_translate | exact GlobalTheory.Mum.exists_ext_translate | (intros; apply GlobalTheory.Mum.exists_ext_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCDvrOfIsDiscreteValuationRing
section
namespace GlobalTheory.DvrCompletion

theorem exists_cDvr_of_isDiscreteValuationRing : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A], ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V), GlobalTheory.LN.CDvr V ∧ ∃ ι : A →+* V, Function.Injective ι ∧ IsLocalHom ι := by
  intro A _ _ _ _
  obtain ⟨V, _, _, _, ι, h, h1, h2⟩ := GlobalTheory.Mum.exists_cDvr_injective_isLocalHom A
  exact ⟨V, inferInstance, inferInstance, inferInstance, h, ι, h1, h2⟩

end GlobalTheory.DvrCompletion
end

