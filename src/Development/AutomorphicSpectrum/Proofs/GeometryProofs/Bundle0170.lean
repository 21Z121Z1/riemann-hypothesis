import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0166
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0160
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0165
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.WeilBound.CoreStatements.AmpleLineBundles.TangentVectorExtendsOverIntegers
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionalSpecializesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_functional_specializes : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (f : Module.Dual Ω Li) (p q : Cpt ξ),
    IsCptGen ξ → q.1 ⤳ p.1 → (∀ e ∈ M.lat p, f e ∈ regAt ξ p) → ∀ e ∈ M.lat q, f e ∈ regAt ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.lat_form_regular_generizes | exact GlobalTheory.CompanionTheory.Ar.RootHt.lat_form_regular_generizes | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.lat_form_regular_generizes <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesFlagDegreeStatement
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_lines_flag_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (r : CMType H × Fin (D.p + D.q)) (q : Cpt 𝔐.ξ) (cc : (k : K) → J k) (b : Fin (labelRk D (HodgeCpt.rootIdx D r).1) → 𝔐.Li) (t : Ω), Fl.RootLines xdeg e → InChart 𝔐.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) cc q → (∀ j, flagStep Ω b j = flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) j) → (𝔐.V (HodgeCpt.rootIdx D r).1).IsFrameAt b q → b (HodgeCpt.rootIdx D r).2 - t • Fl.b (HodgeCpt.rootIdx D r).1 (HodgeCpt.rootIdx D r).2 ∈ flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2 → unitAt 𝔐.ξ q ((∏ k, y ⟨k, cc k⟩ ^ xdeg r k) * e r / t ^ HodgeCpt.rootSgn D r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.rootLine_unitAt | exact GlobalTheory.CompanionTheory.Ar.OrVert.rootLine_unitAt | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.rootLine_unitAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorExtendsDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_lifts_of_local : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (S : Scheme.{0}) (x : Sp O ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (E : Type) [AddCommGroup E] [Module O E] (M : LieModel G x E) (v : epsAt (spMap (algebraMap O K) ≫ x) ⟶ G), IsTanAt G _ v → (∀ (P : Ideal O) [P.IsMaximal] (c : Localization.AtPrime P →+* K), c.comp (algebraMap O _) = algebraMap O K → ∃ w : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ x) ⟶ G, IsTanAt G _ w ∧ v.left = spMap (dualMap c) ≫ w.left) → ∃ e, M.Lifts (algebraMap O K) (𝟙 G.left) e v :=
  @CoverDenseAlt.tangent_vector_extends_over_integers

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoPullbackEquivStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_iso_pullback_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (k : Type) [Field k] (x' : Sp k ⟶ X') (x : Sp k ⟶ X), x = x' ≫ f → (∀ I : TateIsoAt D t x, ∃ I' : TateIsoAt D t' x', I'.ζ = I.ζ ∧ ∀ n a, (I'.ev n a).left ≫ m.φ = (I.ev n a).left) ∧ ∀ I' : TateIsoAt D t' x', ∃ I : TateIsoAt D t x, I'.ζ = I.ζ ∧ ∀ n a, (I'.ev n a).left ≫ m.φ = (I.ev n a).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.tateIsoAt_move | exact GlobalTheory.CompanionTheory.Ar.XR.tateIsoAt_move | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.tateIsoAt_move <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingBaseChangeUnit
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

private theorem gm_unitRes' {S : Scheme} {T : Over S} (V : T.left.Opens) {Z : Scheme}
    (r : Z ⟶ (Out.overRes V).left) (z : Z) (a : (↑(T.left.presheaf.obj (Opposite.op ⊤)))ˣ) :
    gm r z ⊤ (Out.unitRes V a) = gm (r ≫ V.ι) z ⊤ a :=
  gm_pull r V.ι z ⊤ trivial a

private theorem unitOn_units_map {k M : Type} [Field k] [Field M] (j : k →+* M) (c : kˣ) :
    unitOn (Units.map j.toMonoidHom c) = Units.map (spMap j).appTop.hom (unitOn c) := by
  ext
  show (Scheme.ΓSpecIso (CommRingCat.of M)).inv.hom (j c) =
    (Spec.map (CommRingCat.ofHom j)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
  exact congrArg (fun g => g.hom (c : k)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))

theorem weilIs_fieldExt : ∀ {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → ∀ (k M : Type) [Field k] [Field M] (j : k →+* M) (q : Sp k ⟶ X) (q' : Sp M ⟶ X), q' = spMap j ≫ q → ∀ (n : ℤ) (x y : Over.mk q ⟶ G) (x' y' : Over.mk q' ⟶ G), x'.left = spMap j ≫ x.left → y'.left = spMap j ≫ y.left → ∀ (c : kˣ) (c' : Mˣ), Out.WeilIs G L n x y (unitOn c) → Out.WeilIs G L n x' y' (unitOn c') → c' = Units.map j.toMonoidHom c := by
  intro X G _ _ L hL k M _ _ j q q' hq n x y x' y' hx hy c c' h1 h2
  let p' : (Over.mk q').left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum M)
  obtain ⟨V', hpV', -, H2⟩ := h2 p'
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hθx₀, hθy₀⟩, H1'⟩ := h1 ((spMap j).base p')
  have H1 := H1' θx₀ θy₀ hθx₀ hθy₀
  have key : ∀ I : Ideal k, I.IsPrime → I = ⊥ := fun I _ => Ideal.eq_bot_of_prime I
  have hall : ∀ z : (Over.mk q).left, z ∈ V := by
    intro z
    have hz : z = (spMap j).base p' := by
      apply PrimeSpectrum.ext
      exact (key z.asIdeal z.isPrime).trans (key _ ((spMap j).base p').isPrime).symm
    rw [hz]; exact hpV
  let τ : (Out.overRes V').left ⟶ (Out.overRes V).left :=
    IsOpenImmersion.lift V.ι (V'.ι ≫ spMap j) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact hall _)
  have hτι : τ ≫ V.ι = V'.ι ≫ spMap j := IsOpenImmersion.lift_fac _ _ _
  have hτ : τ ≫ (Out.overRes V).hom = (Out.overRes V').hom ≫ 𝟙 X := by
    change τ ≫ (V.ι ≫ q) = (V'.ι ≫ q') ≫ 𝟙 X
    rw [← Category.assoc, hτι, hq]
    simp
  haveI : IsMonHom (Iso.refl G).hom := by
    show IsMonHom (𝟙 G)
    infer_instance
  have hp : IsGrpPullback G G (𝟙 X) (𝟙 G.left) :=
    (isGrpPullback_of_iso (Iso.refl G)).congr rfl (by simp)
  obtain ⟨w, hw⟩ : LBIso L (L.pull (𝟙 G.left)) :=
    LBIso.chartPull (chartPullId L) (chartPullPull L (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)
  have hxpt : τ ≫ θx₀.pt.left = (Out.overResι V' ≫ x').left ≫ 𝟙 G.left := by
    rw [hθx₀]
    change τ ≫ (V.ι ≫ x.left) = (V'.ι ≫ x'.left) ≫ 𝟙 G.left
    rw [hx, Category.comp_id, ← Category.assoc τ, hτι, Category.assoc]
  have hypt : τ ≫ θy₀.pt.left = (Out.overResι V' ≫ y').left ≫ 𝟙 G.left := by
    rw [hθy₀]
    change τ ≫ (V.ι ≫ y.left) = (V'.ι ≫ y'.left) ≫ 𝟙 G.left
    rw [hy, Category.comp_id, ← Category.assoc τ, hτι, Category.assoc]
  obtain ⟨θx, hθx, hPx⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_theta_move hp τ hτ hL hL w hw n (Out.overResι V' ≫ x') θx₀ hxpt
  obtain ⟨θy, hθy, hPy⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_theta_move hp τ hτ hL hL w hw n (Out.overResι V' ≫ y') θy₀ hypt
  have hgm : ∀ (Z : Scheme) (r : Z ⟶ (Out.overRes V').left) (z : Z),
      gm (r ≫ τ) z ⊤ (Out.unitRes V (unitOn c)) =
        gm r z ⊤ (Out.unitRes V' (unitOn (Units.map j.toMonoidHom c))) := by
    intro Z r z
    rw [gm_unitRes', gm_unitRes', unitOn_units_map]
    erw [gm_pull (r ≫ V'.ι) (spMap j) z ⊤ trivial (unitOn c)]
    rw [Category.assoc, hτι, Category.assoc]
  have HC := ReciprocityTheory.ChartRestriction.G.H1.commIsOf_move hp τ hτ hL hL w n θx₀ θy₀ θx θy
    (by rw [hθx]; exact hxpt) (by rw [hθy]; exact hypt) hPx hPy _ _ hgm H1
  have HC2 := H2 θx θy hθx hθy
  have heq := ReciprocityTheory.ChartRestriction.G.H1.commIsOf_unique hL θx θy _ _ HC2 HC
  let pt : (Out.overRes V').left := ⟨p', hpV'⟩
  have e := (gm_unitRes' V' (𝟙 (Out.overRes V').left) pt (unitOn c')).symm.trans
    ((congrArg (gm (𝟙 (Out.overRes V').left) pt ⊤) heq).trans
      (gm_unitRes' V' (𝟙 (Out.overRes V').left) pt _))
  have e' := (gm_val (𝟙 (Out.overRes V').left ≫ V'.ι) pt ⊤ trivial (unitOn c')).symm.trans
    ((congrArg Units.val e).trans
      (gm_val (𝟙 (Out.overRes V').left ≫ V'.ι) pt ⊤ trivial _))
  apply Units.ext
  refine (RingHom.injective
    (((Out.overRes V').left.presheaf.germ ((TopologicalSpace.Opens.map (𝟙 (Out.overRes V').left ≫ V'.ι).base).obj ⊤)
      pt trivial).hom.comp
      (((𝟙 (Out.overRes V').left ≫ V'.ι).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of M)).inv.hom))) ?_
  have e'' := by simpa [unitOn] using e'
  exact e''

end GlobalTheory.CompanionTheory.Ar
end
end

