import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0179
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OmegaLatticeDominantCompat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0054
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0177
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0088
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.WeilBound.CoreStatements.HodgeTatePoints.Weilreg

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliTwistAutomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem moduli_twist_phi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (g : HostAut H) (a : TwIso D g) (h : TwOK Xo.univ g a),
    ∃ Φ : Xo.X ⟶ Xo.X, Φ ≫ Xo.s = Xo.s ∧ Nonempty (ObjMap (twistObj Xo.univ g a h) Xo.univ Φ) := by
  intro E _ _ _ H D l Xo g a h
  obtain ⟨f, ⟨hf, ho⟩, -⟩ :=
    Xo.rep Xo.X Xo.s (moduli_isReduced E H D l Xo) (twistObj Xo.univ g a h)
  exact ⟨f, hf, ho⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OmegaLatticeDominantCompatStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_lattice_dominant_compat : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → Smooth G.hom → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → ∀ (jd : Module.Dual Ω V →+ Module.Dual Ω' V'), (∀ w e, jd w (j e) = i (w e)) → ∀ (N : ℕ), 0 < N → ∀ (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), IsIntegrallyClosed (X.presheaf.stalk (f p'.1)) → IsNoetherianRing (X.presheaf.stalk (f p'.1)) → (∃ ζ : Ω, IsPrimitiveRoot ζ N) → M.IsHTFormAt N ⟨f p'.1, h⟩ 0 → M'.htLat N p' = (M.htLat N).pull ξ' f jd p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HTPull.main | exact GlobalTheory.CompanionTheory.Ar.HTPull.main | (intros; apply GlobalTheory.CompanionTheory.Ar.HTPull.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowFnsOfAbelianGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.PowFn

theorem powFns_of_generic_abelian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), IsReduced X0 → IsLocallyNoetherian X0 → (∀ z : X0, (∀ z' : X0, z' ⤳ z → z' = z) → z ∈ abLocus t.G) → PowFns t :=
  @PositivityTheory.HtPt.Cf.pow_fns

end GlobalTheory.CompanionTheory.Ar.PowFn
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelOverBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ProjModel

open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem sec_ext (hg : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) {W : X.Opens} {s t : Γ(X, W)}
    (h : ∀ hW : genPt ξ ∈ W, CoordBase.val (ξ := ξ) W hW s = CoordBase.val (ξ := ξ) W hW t) : s = t := by
  refine TopCat.Presheaf.section_ext X.sheaf W s t fun p hp => ?_
  have hW : genPt ξ ∈ W := (hall p).mem_open W.isOpen hp
  refine hg.inj ⟨p, hall p⟩ ?_
  exact (CoordBase.genMap_germ_val W hW ⟨p, hall p⟩ hp s).trans
    ((h hW).trans (CoordBase.genMap_germ_val W hW ⟨p, hall p⟩ hp t).symm)

theorem val_resG {U V : X.Opens} (h : V ≤ U) (hV : genPt ξ ∈ V) (s : Γ(X, U)) :
    CoordBase.val (ξ := ξ) V hV (resG X h s) = CoordBase.val (ξ := ξ) U (h hV) s := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_res_apply (homOfLE h).op.unop _ hV s)

theorem exists_charts {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x) (hall : ∀ q : X, genPt ξ ⤳ q) :
    ∃ U : κ → X.Opens, (∀ c, IsAffineOpen (U c)) ∧ ∀ c q, q ∈ U c ↔ InChart ξ x c ⟨q, hall q⟩ := by
  have : ∀ c, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ q, q ∈ U ↔ InChart ξ x c ⟨q, hall q⟩ := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨⊥, isAffineOpen_bot X, fun q => ⟨fun h => h.elim, fun h => (h.1 hc).elim⟩⟩
    · obtain ⟨U, hU, hm⟩ := hT.affine c hc
      exact ⟨U, hU, fun q => (hm q).trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨hall q, h⟩⟩⟩
  choose U hU using this
  exact ⟨U, fun c => (hU c).1, fun c => (hU c).2⟩

theorem eval₂Hom_surjective {A J : Type} [CommRing A] (b : ℤ →+* A) (ρ : J → A) (v : A →+* Ω)
    (hv : Function.Injective v) (y : J → Ω) (hρ : ∀ j, v (ρ j) = y j)
    (hA : ∀ a, v a ∈ Algebra.adjoin ℤ (Set.range y)) :
    Function.Surjective (MvPolynomial.eval₂Hom b ρ) := by
  intro g
  have hg := hA g
  rw [Algebra.adjoin_range_eq_range_aeval] at hg
  obtain ⟨P, hP⟩ := hg
  refine ⟨P, hv ?_⟩
  have key : v.comp (MvPolynomial.eval₂Hom b ρ) =
      (MvPolynomial.aeval y : MvPolynomial J ℤ →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp
    · simp [hρ]
  exact (congrArg (fun φ : MvPolynomial J ℤ →+* Ω => φ P) key).trans hP

theorem isProjOver_of_coordTie {N : ℕ} {x : Fin (N + 1) → Ω} (hT : CoordTie ℤ ξ x)
    (hall : ∀ q : X, genPt ξ ⤳ q) (s : X ⟶ Sp ℤ) : IsProjOver s := by
  classical
  obtain ⟨U, hU, hm⟩ := exists_charts hT hall
  have hmem : ∀ c q, q ∈ U c ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩ := fun c q =>
    (hm c q).trans ⟨fun h => ⟨hall q, h⟩, fun ⟨_, h⟩ => h⟩
  have hgen : ∀ c, genPt ξ ∈ U c → x c ≠ 0 := fun c h => ((hm c _).1 h).1
  have hr : ∀ c j, ∃ b : Γ(X, U c), ∀ hW : genPt ξ ∈ U c,
      CoordBase.val (ξ := ξ) (U c) hW b = x j / x c := by
    intro c j
    by_cases hW : genPt ξ ∈ U c
    · obtain ⟨b, hb⟩ := (CoordBase.mem_adjoin_iff hT (hgen c hW) (hU c) (hmem c) hW (x j / x c)).1
        (Algebra.subset_adjoin ⟨j, rfl⟩)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => (hW h).elim⟩
  choose r hr using hr
  have H : IsCoordFamily U r :=
    { cover := by
        rw [eq_top_iff]
        intro q _
        obtain ⟨c, hc⟩ := hT.cover ⟨q, hall q⟩
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, (hm c q).2 hc⟩
      self := fun i => sec_ext hT.gen hall fun hW => by
        rw [hr, map_one, div_self (hgen i hW)]
      mul := fun i j k => sec_ext hT.gen hall fun hW => by
        have hi := hgen i hW.1
        have hj := hgen j hW.2
        rw [map_mul, val_resG, val_resG, val_resG, hr, hr, hr]
        field_simp
      basicOpen_le := fun i j p hp => by
        have hpi : p ∈ U i := X.basicOpen_le _ hp
        obtain ⟨u, hu⟩ : IsUnit (X.presheaf.germ (U i) p hpi (r i j)) :=
          (X.mem_basicOpen _ p hpi).1 hp
        have hW : genPt ξ ∈ U i := (hall p).mem_open (U i).isOpen hpi
        have hxi := hgen i hW
        have hv : genMap ξ ⟨p, hall p⟩ (u : X.presheaf.stalk p) = x j / x i := by
          rw [hu]
          exact (CoordBase.genMap_germ_val (U i) hW ⟨p, hall p⟩ hpi _).trans (hr _ _ _)
        have hinv : (x j / x i) * genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) = 1 := by
          rw [← hv, ← map_mul, Units.mul_inv, map_one]
        have hxj : x j ≠ 0 := by
          intro h
          rw [h, zero_div, zero_mul] at hinv
          exact zero_ne_one hinv
        have hi := (hm i p).1 hpi
        refine (hm j p).2 ⟨hxj, fun c' => ?_⟩
        have e : x c' / x j = (x c' / x i) *
            genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) := by
          have e' : genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) = x i / x j := by
            field_simp at hinv ⊢
            linear_combination hinv
          rw [e']
          field_simp
        rw [e]
        exact (regAt ξ _).mul_mem (hi.2 c') ⟨_, rfl⟩ }
  refine ⟨N, H.toHom s, ?_, H.toHom_str s⟩
  refine (isClosedImmersion_iff_pullRatio (H.toHom s) (H.toHom_preimage s)).2 fun i => ⟨hU i, ?_⟩
  have hρ : pullRatio (H.toHom s) (U i) i (H.toHom_preimage s i).ge = r i :=
    funext (H.pullRatio_toHom s i)
  rw [hρ]
  by_cases hW : genPt ξ ∈ U i
  · refine eval₂Hom_surjective _ _ (CoordBase.val (ξ := ξ) (U i) hW) ?_ (fun j => x j / x i) (hr i · hW) ?_
    · intro a a' e
      exact sec_ext hT.gen hall fun _ => e
    · intro a
      exact (CoordBase.mem_adjoin_iff hT (hgen i hW) (hU i) (hmem i) hW _).2 ⟨a, rfl⟩
  · exact fun g => ⟨0, sec_ext hT.gen hall fun h => (hW h).elim⟩

theorem isProjOver_pModel {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel ℤ x) : IsProjOver M.s := by
  obtain ⟨N, x', h⟩ := coordTie_int_of_finite M.X Ω M.ξ ℤ κ x M.tie
  exact isProjOver_of_coordTie h M.all M.s

theorem isProjOver_of_map {O : Type} [CommRing O] {Z : Scheme.{0}} {s : Z ⟶ Sp ℤ} (h : IsProjOver s)
    (g : Z ⟶ Sp O) : IsProjOver g := by
  have hp := isProjOver_pullback_snd (Int.castRingHom O) h
  let σ : Z ⟶ pullback s (spMap (Int.castRingHom O)) :=
    pullback.lift (𝟙 Z) g (specZIsTerminal.hom_ext _ _)
  have hσ : IsClosedImmersion σ := by
    have : IsClosedImmersion (σ ≫ pullback.fst s (spMap (Int.castRingHom O))) := by
      rw [pullback.lift_fst]
      infer_instance
    exact .of_comp σ (pullback.fst s (spMap (Int.castRingHom O)))
  have := isProjOver_comp_of_isClosedImmersion σ hp
  rwa [pullback.lift_snd] at this

theorem isProjOver_comp_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω]
    (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X), IsProjOver (f ≫ Y.s) :=
  fun _ _ _ _ _ _ _ _ _ Y _ _ _ _ _ M f => isProjOver_of_map (isProjOver_pModel M) (f ≫ Y.s)

end GlobalTheory.CompanionTheory.Ar.ProjModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperDvrModelLatticeValuation
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.PlaceOrd

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

def tr {A B : Subring Ω} (h : A = B) (N : Submodule B Ω) : Submodule A Ω where
  carrier := N
  add_mem' := N.add_mem
  zero_mem' := N.zero_mem
  smul_mem' := fun c _ hx => N.smul_mem ⟨c.1, h ▸ c.2⟩ hx

theorem tr_eq_span_iff {A B : Subring Ω} (h : A = B) (N : Submodule B Ω) (S : Set Ω) :
    tr h N = Submodule.span A S ↔ N = Submodule.span B S := by
  subst h
  have : tr rfl N = N := by ext; rfl
  rw [this]

theorem genMap_stalkMap₀ (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

def push (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (p : Cpt ξ') : Cpt (ξ' ≫ g) :=
  ⟨g p.1, p.2.map g.continuous⟩

variable {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {g : X' ⟶ X}

def pullL (hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p)) (L : Lat (ξ' ≫ g) Ω) : Lat ξ' Ω :=
  fun p => tr (hr p) (L (push ξ' g p))

section

variable (hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p)) {L : Lat (ξ' ≫ g) Ω}
include hr

theorem unit_iff (p : Cpt ξ') (a : Ω) : unitAt ξ' p a ↔ unitAt (ξ' ≫ g) (push ξ' g p) a := by
  unfold unitAt
  rw [hr p]

theorem pull_span_iff (p : Cpt ξ') (S : Set Ω) :
    pullL hr L p = Submodule.span (regAt ξ' p) S ↔
      L (push ξ' g p) = Submodule.span (regAt (ξ' ≫ g) (push ξ' g p)) S :=
  tr_eq_span_iff _ _ _

theorem isVB_pull (hL : L.IsVB 1 ⊤) : (pullL hr L).IsVB 1 ⊤ := by
  intro p _
  obtain ⟨U, hU, b, hb, h⟩ := hL (push ξ' g p) trivial
  refine ⟨g ⁻¹ᵁ U, hU, b, hb, fun q _ hq => ?_⟩
  obtain ⟨h1, h2⟩ := h (push ξ' g q) trivial hq
  exact ⟨h1, (pull_span_iff hr q _).2 h2⟩

omit hr in
theorem isIntegral_congr {A B : Subring Ω} (h : A = B) {a : Ω} (ha : IsIntegral A a) : IsIntegral B a := by
  subst h
  exact ha

theorem normal_pull (hN : NormalCpt (ξ' ≫ g)) : NormalCpt ξ' := fun p a ha => by
  rw [hr p]
  exact hN _ a (isIntegral_congr (hr p) ha)

theorem isGenAt_pull {p : Cpt ξ'} {t : Ω} (h : L.IsGenAt (push ξ' g p) t) : (pullL hr L).IsGenAt p t :=
  ⟨h.1, (pull_span_iff hr p _).2 h.2⟩

theorem order_back {σ ϖ : Ω} {M : ℕ} {a : ℤ} {p : Cpt ξ'} (h : OrderAt (pullL hr L) σ ϖ M a p) :
    OrderAt L σ ϖ M a (push ξ' g p) := by
  obtain ⟨e, c, he, h1, h2, h3⟩ := h
  exact ⟨e, c, he, (pull_span_iff hr p _).1 h1, h2, (unit_iff hr p _).1 h3⟩

theorem trivMod_pull {ϖ l u : Ω} (e : l = ϖ * u) (hϖ : ∀ p, ϖ ∈ regAt ξ' p) (hu : ∀ p, u ∈ regAt ξ' p)
    (hT : TrivMod L l) : TrivMod (pullL hr L) ϖ := by
  obtain ⟨t, ht⟩ := hT
  have key : ∀ p, ¬ unitAt ξ' p ϖ → ¬ unitAt (ξ' ≫ g) (push ξ' g p) l := fun p hp hl =>
    hp (ZUnit.of_mul (hϖ p) (hu p) ((unit_iff hr p _).2 (e ▸ hl)))
  refine ⟨fun p => t (push ξ' g p), fun p hp => ?_⟩
  obtain ⟨U, hU, H⟩ := ht _ (key p hp)
  refine ⟨g ⁻¹ᵁ U, hU, fun q hq hq' => ?_⟩
  obtain ⟨h0, h1, y, hy, hty⟩ := H (push ξ' g q) hq (key q hq')
  refine ⟨h0, (pull_span_iff hr q _).2 h1, u • y, ?_, ?_⟩
  · exact (L (push ξ' g q)).smul_mem ⟨u, hr q ▸ hu q⟩ hy
  · change t (push ξ' g p) - t (push ξ' g q) = ϖ • u • y
    rw [hty, e, mul_smul]

end

theorem valAt_zero_down {R : Type} [CommRing R] [IsLocalRing R] (hc : IsCptGen ξ')
    (z : Spec (CommRingCat.of R) ⟶ X') {ϖ u l : Ω} (e : l = ϖ * u) (h : genPt ξ' ⤳ centre z)
    (hv : ValAt ξ' z ϖ 0) (hu : u ∈ regAt ξ' ⟨centre z, h⟩)
    (hl : l ∈ regAt (ξ' ≫ g) (push ξ' g ⟨centre z, h⟩)) : ValAt (ξ' ≫ g) (z ≫ g) l 0 := by
  obtain ⟨h', s, hs, h0⟩ := hv
  obtain ⟨t, ht⟩ : ∃ t : X'.presheaf.stalk (centre z), genMap ξ' ⟨centre z, h⟩ t = u := hu
  obtain ⟨w, hw⟩ := hl
  have e1 : (g.stalkMap (centre z)).hom w = s * t := by
    apply hc.inj ⟨centre z, h⟩
    rw [genMap_stalkMap₀ ξ' g ⟨centre z, h⟩ (push ξ' g ⟨centre z, h⟩).2 w, map_mul, ht]
    refine hw.trans ?_
    rw [e, ← hs]
  have e2 : (Scheme.stalkClosedPointTo (z ≫ g)).hom w =
      (Scheme.stalkClosedPointTo z).hom ((g.stalkMap (centre z)).hom w) :=
    congrArg (fun t => t.hom w) (Scheme.stalkClosedPointTo_comp z g)
  refine ⟨(push ξ' g ⟨centre z, h⟩).2, w, hw, e2.trans ?_⟩
  rw [e1]
  exact (map_mul (Scheme.stalkClosedPointTo z).hom s t).trans
    ((congrArg (fun x : R => x * (Scheme.stalkClosedPointTo z).hom t) h0).trans (zero_mul _))

theorem valAt_up {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X')
    (h : genPt ξ' ⤳ centre z) {a : Ω} {r : R} (hv : ValAt (ξ' ≫ g) (z ≫ g) a r) : ValAt ξ' z a r := by
  obtain ⟨h', s, hs, rfl⟩ := hv
  exact ⟨h, (g.stalkMap (centre z)).hom s, (genMap_stalkMap₀ ξ' g ⟨centre z, h⟩ h' s).trans hs,
    (congrArg (fun t => t.hom s) (Scheme.stalkClosedPointTo_comp z g)).symm⟩

def curvePush {ϖ l : Ω} (Γ : FibreCurve ξ' ϖ) (hz : ValAt (ξ' ≫ g) (Γ.η ≫ g) l 0) : FibreCurve (ξ' ≫ g) l where
  k := Γ.k
  κ := Γ.κ
  fg := Γ.fg
  trdeg := Γ.trdeg
  C := Γ.C
  w_pos := Γ.w_pos
  triv := Γ.triv
  all := Γ.all
  η := Γ.η ≫ g
  η_spec := hz.1
  η_zero := hz
  z := fun i => Γ.z i ≫ g
  z_gen := fun i => by rw [← Category.assoc, Γ.z_gen]

theorem hasDeg_back (hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p)) {L : Lat (ξ' ≫ g) Ω} {ϖ l : Ω}
    (Γ : FibreCurve ξ' ϖ) (hz : ValAt (ξ' ≫ g) (Γ.η ≫ g) l 0) (h : (curvePush Γ hz).HasDeg L 0) :
    Γ.HasDeg (pullL hr L) 0 := by
  obtain ⟨e, f, r, he, hf, hv, hfin, hd⟩ := h
  refine ⟨e, f, r, isGenAt_pull hr he, fun i => ⟨Γ.z_spec i, ?_⟩, fun i => ⟨(hv i).1, ?_⟩, hfin, hd⟩
  · obtain ⟨_, h2⟩ := hf i
    exact isGenAt_pull hr h2
  · exact valAt_up _ Γ.η_spec (hv i).2

theorem numTrivMod_pull (hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p)) (hc : IsCptGen ξ')
    {L : Lat (ξ' ≫ g) Ω} {ϖ l u : Ω} (e : l = ϖ * u) (hϖ : ∀ p, ϖ ∈ regAt ξ' p) (hu : ∀ p, u ∈ regAt ξ' p)
    (hT : NumTrivMod L l) : NumTrivMod (pullL hr L) ϖ := fun Γ => by
  let p : Cpt ξ' := ⟨centre Γ.η, Γ.η_spec⟩
  have hl : l ∈ regAt (ξ' ≫ g) (push ξ' g p) := by
    have h1 := mul_mem (hϖ p) (hu p)
    rwa [← e, hr p] at h1
  have hz := valAt_zero_down (g := g) hc Γ.η e Γ.η_spec Γ.η_zero (hu p) hl
  exact hasDeg_back hr Γ hz (hT (curvePush Γ hz))

theorem order_at_place : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X' ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O) (L : Lat ξ Ω) (σ : Ω) (ℓ : ℕ) (u : O), PropZ → Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ' ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ξ' ≫ g = ξ → IsCptGen ξ → IsCptGen ξ' → (∀ q' : X', genPt ξ' ⤳ q') → NormalCpt ξ → ConstClosed O Ω → (∀ (p' : Cpt ξ') (p : Cpt ξ), p.1 = g p'.1 → ∀ a : Ω, a ∈ regAt ξ' p' ↔ a ∈ regAt ξ p) → L.IsVB 1 ⊤ → (∀ p ∈ genFibre ℤ ξ, L.IsGenAt p σ) → (ℓ : Ω) = algebraMap O Ω (ϖ * u) → (TrivMod L (ℓ : Ω) ∨ NumTrivMod L (ℓ : Ω)) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, (∃ p' : Cpt ξ', g p'.1 = p.1) → OrderAt L σ (algebraMap O Ω ϖ) M a p := by
  intro X X' Ω _ _ ξ ξ' g O _ _ _ _ s _ ϖ L σ ℓ u hZ hirr hinj hs hcomp hc hc' hall hN hcc hreg hVB hgen hℓ hT
  subst hcomp
  have hr : ∀ p, regAt ξ' p = regAt (ξ' ≫ g) (push ξ' g p) := fun p =>
    SetLike.ext (hreg p (push ξ' g p) rfl)
  have hconst : ∀ (o : O) (p : Cpt ξ'), algebraMap O Ω o ∈ regAt ξ' p := fun o p =>
    (ConstReg.regular_const X' Ω ξ' O s hs p o).1
  have hconn := GlobalTheory.T.isConnected_zeroSet_uniformizer X' Ω ξ' O s ϖ hirr hinj hs hc' hcc
  have hgen' : ∀ p ∈ genFibre O ξ', (pullL hr L).IsGenAt p σ := fun p hp => by
    refine isGenAt_pull hr (hgen _ fun o ho => ?_)
    have e : algebraMap ℤ Ω o = algebraMap O Ω (o : O) := by simp
    rw [e, ← unit_iff hr]
    refine hp _ fun h0 => ho ?_
    have := congrArg (algebraMap O Ω) h0
    simpa using this
  have e : (ℓ : Ω) = algebraMap O Ω ϖ * algebraMap O Ω u := by rw [hℓ, map_mul]
  have main : ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ', OrderAt (pullL hr L) σ (algebraMap O Ω ϖ) M a p := by
    rcases hT with hT | hT
    · exact hZ X' Ω ξ' O s ϖ hirr hinj hs hc' (normal_pull hr hN) hconn (pullL hr L) σ (isVB_pull hr hVB)
        (trivMod_pull hr e (hconst ϖ) (hconst u) hT) hgen'
    · exact GlobalTheory.T.line_degree_special_fibre X' Ω ξ' O s ϖ hirr hinj hs hc' (normal_pull hr hN) hconn (pullL hr L) σ
        (isVB_pull hr hVB) (numTrivMod_pull hr hc' e (hconst ϖ) (hconst u) hT) hgen'
  obtain ⟨M, a, hM, H⟩ := main
  refine ⟨M, a, hM, ?_⟩
  rintro p ⟨p', hp⟩
  have : p = push ξ' g p' := Subtype.ext hp.symm
  rw [this]
  exact order_back hr (H p')

end GlobalTheory.CompanionTheory.Ar.Flat.PlaceOrd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleDivisibleAtPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_module_divisible_at_prime : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Sp R) [Smooth p] (M : LB X) (b : Sp R), b.asIdeal.IsMaximal → ∀ u : SecMod p M, (∀ y : X, p y = b → y ∉ Out.nonzeroLocus (M := M) u) → ∀ c e : R, e ≠ 0 → (∀ π ∈ b.asIdeal, e ∣ c * π) → ∃ u' : SecMod p M, e • u' = c • u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv.exists_smul_eq_smul | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv.exists_smul_eq_smul | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv.exists_smul_eq_smul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianOfPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semi_abelian_of_pullback : ∀ (X X' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsSemiAbelian G → IsSemiAbelian G' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isSemiAbelian_of_isGrpPullback | exact GlobalTheory.CompanionTheory.Ar.isSemiAbelian_of_isGrpPullback | (intros; apply GlobalTheory.CompanionTheory.Ar.isSemiAbelian_of_isGrpPullback <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorsBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vectors_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (τ : 𝓞 E →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), x' = spMap f ≫ x → (∃ v' : Fin n → (epsAt x' ⟶ t.G), ∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) ∧ ∀ v' : Fin n → (epsAt x' ⟶ t.G), (∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) → (IsEigFrame t.act x τ v ↔ IsEigFrame t.act x' (f.comp τ) v') := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change | exact GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change | (intros; apply GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionTowerWeilPairing
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem weil_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsAlgClosed (FractionRing O)] (y : Sp O ⟶ S) (La : Type) [AddCommGroup La] (X : TorsTower p t.G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), IsProper (Limits.pullback.snd t.G.hom ((BT.genPt O).hom ≫ y)) → (∀ n (a b : La) (ga gb : Over.mk ((BT.genPt O).hom ≫ y) ⟶ t.G), ga.left = ((X.Γ n).pt (lev p n a)).left ≫ X.i n → gb.left = ((X.Γ n).pt (lev p n b)).left ≫ X.i n → Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) ga gb (unitOn (Units.map (algebraMap O (FractionRing O) : O →* FractionRing O) (ζ n ^ B a b)))) → X.PairingRegular B ζ :=
  PositivityTheory.HtPt.Weilreg.weil_regular_of_fun weil_pairing_cubical

end GlobalTheory.CompanionTheory.Ar.HT
end

