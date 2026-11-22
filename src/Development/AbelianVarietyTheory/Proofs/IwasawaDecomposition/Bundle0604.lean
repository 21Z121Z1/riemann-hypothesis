import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharBundlePrimitive
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RankOneBaseWeightEqCmTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtFJQOver
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ShFam.Horiz

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def frameCast {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x x' : Sp R ⟶ Z.X} (h : x = x')
    (g : EigFrame Z φ x) : EigFrame Z φ x' := h ▸ g

theorem ptF_jQ_over (Z : Model Xo c β) {σ : c.F →+* ℂ} (P : FrPt Xo c (CAt σ)) :
    (GlobalTheory.AllWt.ptF (S := CAt σ) P ≫ Z.jQ) ≫ genStr Z = spMap σ := by
  rw [Category.assoc, Z.jQ_over]
  exact pullback.lift_snd _ _ _

def cxOf (Z : Model Xo c β) {σ : c.F →+* ℂ} (P : FrPt Xo c (CAt σ)) : CxFr Z σ :=
  ⟨⟨GlobalTheory.AllWt.ptF (S := CAt σ) P ≫ Z.jQ, ptF_jQ_over Z P⟩,
    frameCast (φ := σ) (Category.assoc _ _ _).symm (frameOf (R := CAt σ) Z P)⟩

end GlobalTheory.ShFam.Horiz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowthStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_extension_of_log_growth : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (U : Set V) (φ u : V → ℂ), IsOpen U → DifferentiableOn ℂ φ U → DifferentiableOn ℂ u {b ∈ U | φ b ≠ 0} → U ⊆ closure {b ∈ U | φ b ≠ 0} → (∀ b₀ ∈ U, ∃ (C : ℝ) (k : ℕ), ∀ᶠ b in 𝓝 b₀, φ b ≠ 0 → ‖u b‖ ≤ C * (1 + |Real.log ‖φ b‖|) ^ k) → ∃ u' : V → ℂ, DifferentiableOn ℂ u' U ∧ Set.EqOn u' u {b ∈ U | φ b ≠ 0} := by
  first | exact @GlobalTheory.LogExt.riemann_extension_log | exact GlobalTheory.LogExt.riemann_extension_log | (intros; apply GlobalTheory.LogExt.riemann_extension_log <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRochNeBotOfHolomorphicSectionNeBot
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

theorem riemannRoch_ne_bot_of_holomorphicSection_ne_bot : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ)
    (R : AnRead Y.str σ Y.dim) (D : Y.Dv), R.holSec (Y.lb D) ≠ ⊥ → Y.H0 D ≠ ⊥ := by
  intro F _ Y σ R D hR hH
  refine hR ?_
  have P := GlobalTheory.Cartier.presents_toLB D
  have hs : ∀ s : (Y.lb D).Sec, s = 0 := fun s => by
    have hm : P.rat s ∈ Y.H0 D := P.rat_mem s
    rw [hH, Submodule.mem_bot] at hm
    exact P.rat_injective (hm.trans (map_zero P.rat).symm)
  have hx : ∀ x : SecC Y.str σ (Y.lb D), x = 0 := fun x => by
    have hle : Submodule.span ℂ (Set.range (SecC.of Y.str σ : (Y.lb D).Sec → _)) ≤ ⊥ :=
      Submodule.span_le.2 (by
        rintro _ ⟨s, rfl⟩
        rw [hs s, map_zero]
        exact zero_mem _)
    exact (Submodule.mem_bot ℂ).1 (hle (SecC.span_range_of.ge Submodule.mem_top))
  have hb := GlobalTheory.AnRead.bijective_valC Y.isProjOver R (GlobalTheory.Cartier.isLB_toLB D)
  refine (Submodule.eq_bot_iff _).2 fun f hf => ?_
  obtain ⟨x, hxf⟩ := hb.2 ⟨f, hf⟩
  rw [hx x, map_zero] at hxf
  exact (congrArg Subtype.val hxf).symm

end GlobalTheory.ShFam.Hor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceNoChainPlaceOrTypePrimeOverStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.served_place_no_chain_place_or_type_prime_over : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      Formalism.L2.Forms.okQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)) v ∧
        (∀ w' ∈ Formalism.L2.Forms.badQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)), (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal) ∧
        ¬ (w.D Z).what₂.places.resChar v ∣ ((w.D Z).mem u).A.T := by
  first | exact @GlobalTheory.ServedPlace.places_prime | exact GlobalTheory.ServedPlace.places_prime | (intros; apply GlobalTheory.ServedPlace.places_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem smooth_gtCoord_q {H : Over (Spec (CommRingCat.of R))} [GrpObj H] [IsCommMonObj H]
    (c : GtCoord (⊥ : Ideal R) D 0 H) : Smooth c.q.left := by
  have := c.q_hom
  have := c.i_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  obtain ⟨-, -, -, -, h1, -⟩ := (GlobalTheory.splitTorus_properties (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1))))).1 D.X
  have : Smooth (splitTorus (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) D.X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ D.X) _
  have H' := (GlobalTheory.UnitRigidity.isPullback_act c.i c.q c.isKernel).map (Over.forget _)
  have a1 : Smooth (snd (splitTorus (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) D.X)
      (thickObj R ⊥ 0 H)).left :=
    inferInstanceAs (Smooth (pullback.snd (splitTorus _ D.X).hom (thickObj R ⊥ 0 H).hom))
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H'.flip ⟨⟨‹_›, ‹_›⟩, (inferInstance : QuasiCompact c.q.left)⟩ a1

theorem Ray.smooth_q {oa : D.OAct O} (Y : Ray oa) : Smooth Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have hc := smooth_gtCoord_q c
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F

  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ

  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]

  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]

  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

end GlobalTheory.RayEv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesAvoidAuxiliary
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.LevelPlaceSep

theorem not_mem_two {D : D7} (P : PlE D.host) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h1 : P ∈ placesOver D.host.E p) (h2 : P ∈ placesOver D.host.E q) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)
  have e := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
  push_cast at e
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  have h1' : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := h2
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h1') (P.asIdeal.mul_mem_left _ h2')

theorem mem_placesOver_of_comap {D : D7} {P P' : PlE D.host}
    (h : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))) {p : ℕ}
    (hP : P ∈ placesOver D.host.E p) : P' ∈ placesOver D.host.E p := by
  have e : ((p : ℕ) : 𝓞 D.host.E) = (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) (p : 𝓞 (maximalRealSubfield D.host.E)) := (map_natCast _ p).symm
  show ((p : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal
  have hP' : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hP
  rw [e, ← Ideal.mem_comap, ← h, Ideal.mem_comap, ← e]
  exact hP'

theorem isConjPl_conjPlE {D : D7} (P : PlE D.host) : Formalism.BasicNotions.IsConjPl D.host P (GlobalTheory.SplitConjPlace.conjPlE P) := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
  have : IsCMField.ringOfIntegersComplexConj D.host.E y = x := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy, GlobalTheory.LocM.complexConj_eq_conj,
      GlobalTheory.FixedPlaceSplit.host_conj_conj]
  rw [this]

theorem eq_of_qpOf {D : D7} (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
    (hPq : ∀ v, NG.OverPl (Pq v) v) (S : Finset (PlE D.host)) {P P' : PlE D.host}
    (hP : P ∈ qpOf D Pq S) (hP' : P' ∈ qpOf D Pq S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hv : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal) (hv' : P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal) : P = P' := by
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE P P' (hv'.trans hv.symm) with e | e
  · exact e.symm
  have hw : (Pq v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal := hPq v
  have hS : Pq v ∈ S := by
    rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE P (Pq v) (hw.trans hv.symm) with e' | e'
    · rw [e']; exact qpOf_sub D Pq S hP
    · rw [e', ← e]; exact qpOf_sub D Pq S hP'
  exact (qpOf_eq D Pq S hP hv hS).trans (qpOf_eq D Pq S hP' hv' hS).symm

theorem g_ne_g {D : D7} {k k' : Fin 2} (h : k ≠ k') : D.host.g k ≠ D.host.g k' := by
  have h0 := D.host.g_ne
  fin_cases k <;> fin_cases k' <;> simp_all [eq_comm]

theorem levelPlaces_sep : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (Q : Finset (PlE D.host))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (sp : PlE D.host → SplitPlace D.host.E),
    (∀ v, NG.OverPl (Pq v) v) → (∀ P ∈ Q, IsSplitPl D.host P) →
    (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) → (∀ P ∈ T.pD i, IsSplitPl D.host P) →
    (∀ P, (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P) →
    (∀ P P', (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) →
      (P' ∈ qpOf D Pq Q ∨ P' ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P' = NX.pG D kv) → (sp P).v = (sp P').v → P = P') ∧
    (∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i)) ∧ (∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i)) ∧
    ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
  intro D T i Q Pq sp hPq hQs hQ hpDs hsp
  obtain ⟨pp, hpp, hne, hpD⟩ : ∃ pp : ℕ, pp.Prime ∧ (∀ k, pp ≠ D.host.g k) ∧
      ∀ P, P ∈ T.pD i ↔ P ∈ placesOver D.host.E pp := by
    refine ⟨if T.l i = D.host.pde then D.host.pde' else D.host.pde, ?_, ?_,
      fun P => by rw [← Finset.mem_coe, T.pD_eq i]⟩
    · split_ifs
      · exact D.host.pde'_prime
      · exact D.host.pde_prime
    · intro k
      split_ifs
      · exact (D.host.pde_ne_g k).2
      · exact (D.host.pde_ne_g k).1
  have hG : ∀ kv, NX.pG D kv ∈ placesOver D.host.E (D.host.g kv.1) := fun kv => D.naut.plGw_over kv.1 kv.2
  have c2 : ∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i) := fun P hP hP' =>
    (hQ P (qpOf_sub D Pq Q hP)).1 (qpOf_sub D Pq _ hP')
  have c3 : ∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i) := fun kv =>
    ⟨fun h => (hQ _ (qpOf_sub D Pq Q h)).2 kv.1 (hG kv),
     fun h => not_mem_two _ hpp (D.host.g_prime kv.1) (hne kv.1) ((hpD _).1 (qpOf_sub D Pq _ h)) (hG kv)⟩
  have c4 : ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
    rintro ⟨k, v⟩ ⟨k', v'⟩ h
    by_cases hk : k = k'
    · subst hk
      have : v = v' := D.naut.plGw_inj k h
      rw [this]
    · exact (not_mem_two _ (D.host.g_prime k) (D.host.g_prime k') (g_ne_g hk) (hG ⟨k, v⟩)
        (by rw [h]; exact hG ⟨k', v'⟩)).elim
  refine ⟨?_, c2, c3, c4⟩
  intro P P' hP hP' hv
  have hcP : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = (sp P).v.asIdeal := by
    have := (sp P).w_under; rw [hsp P hP] at this; exact this
  have hcP' : P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = (sp P).v.asIdeal := by
    have := (sp P').w_under; rw [hsp P' hP'] at this; rw [this, hv]
  have hc : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := hcP.trans hcP'.symm
  have same : ∀ {p : ℕ}, P' ∈ placesOver D.host.E p → P ∈ placesOver D.host.E p :=
    fun h => mem_placesOver_of_comap hc.symm h
  have same' : ∀ {p : ℕ}, P ∈ placesOver D.host.E p → P' ∈ placesOver D.host.E p :=
    fun h => mem_placesOver_of_comap hc h
  rcases hP with hP | hP | ⟨kv, rfl⟩ <;> rcases hP' with hP' | hP' | ⟨kv', rfl⟩
  · exact eq_of_qpOf Pq hPq Q hP hP' _ hcP hcP'
  · exact ((hQ P (qpOf_sub D Pq Q hP)).1 ((hpD P).2 (same ((hpD P').1 (qpOf_sub D Pq _ hP'))))).elim
  · exact ((hQ P (qpOf_sub D Pq Q hP)).2 kv'.1 (same (hG kv'))).elim
  · exact ((hQ P' (qpOf_sub D Pq Q hP')).1 ((hpD P').2 (same' ((hpD P).1 (qpOf_sub D Pq _ hP))))).elim
  · exact eq_of_qpOf Pq hPq _ hP hP' _ hcP hcP'
  · exact (not_mem_two P hpp (D.host.g_prime kv'.1) (hne kv'.1) ((hpD P).1 (qpOf_sub D Pq _ hP))
      (same (hG kv'))).elim
  · exact ((hQ P' (qpOf_sub D Pq Q hP')).2 kv.1 (same' (hG kv))).elim
  · exact (not_mem_two P' hpp (D.host.g_prime kv.1) (hne kv.1) ((hpD P').1 (qpOf_sub D Pq _ hP'))
      (same' (hG kv))).elim
  · obtain ⟨k, v⟩ := kv
    obtain ⟨k', v'⟩ := kv'
    by_cases hk : k = k'
    · subst hk
      rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE (NX.pG D ⟨k, v⟩) (NX.pG D ⟨k, v'⟩) hc.symm with e | e
      · exact e.symm
      · have hc2 := isConjPl_conjPlE (NX.pG D ⟨k, v⟩)
        rw [← e] at hc2
        exact (D.naut.plGw_nconj k v v' hc2).elim
    · exact (not_mem_two _ (D.host.g_prime k) (D.host.g_prime k') (g_ne_g hk) (hG ⟨k, v⟩)
        (same (hG ⟨k', v'⟩))).elim

end GlobalTheory.LevelPlaceSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRootsStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_poly_chern_roots : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (S : MvPolynomial (Root m) ℝ), (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) → ∃ R : MvPolynomial (ι × ℕ) ℝ, chernRoots m R = S := by
  first | exact @GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric | exact GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric | (intros; apply GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.TorRef

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

def IsTwInv (φ : InvFun (𝓞 E)) : Prop :=
  ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 → ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ),
    φ.toFun n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) = φ.toFun n B

def IsPosFn (φ : InvFun (𝓞 E)) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Nontrivial X], ∀ be ∈ levelForms H 1 X,
    (∀ y, y ≠ 0 → 0 < be y y) → 0 < φ.evalZ be

variable {H} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsPhiDiv (φ : InvFun (𝓞 E)) (Z : Model Xo c β) (BD : EffCartierData Z.X) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t),
      Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
      ∃ n : ℕ, (n : ℝ) = φ.evalZ be ∧ idlAlong BD.idealSheaf χ = Ideal.span {ϖ ^ n}

def polOf (Z : Model Xo c β) (m : ℕ) (BD : EffCartierData Z.X) : LB Z.X :=
  GlobalTheory.CechPic.tens (lbPow (GlobalTheory.FlagMod.detOm Z) m) (GlobalTheory.CechPic.dual BD.lb)

def IsPol (φ : InvFun (𝓞 E)) (m : ℕ) (Z : Model Xo c β) (BD : EffCartierData Z.X) : Prop :=
  IsPhiDiv φ Z BD ∧ GlobalTheory.IsAmpleLB (polOf Z m BD)

def selfTor (Z : Model Xo c β) (h₁ : SmoothOfRelativeDimension D.dim (genStr Z)) (h₂ : FinalTheorems.Snc (genBdIdeal Z))
    (h₃ : ∀ x ∈ genBd Z, HasToricChart Z x) (BD : EffCartierData Z.X)
    (h₄ : ∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Z.t.G) (h₅ : ∀ x ∈ genBd Z, genι Z x ∈ BD.idealSheaf.support)
    (m : ℕ) (hm : 0 < m) : TorModel Z where
  Z := Z
  b := 𝟙 _
  b_s := Category.id_comp _
  j_b := Category.comp_id _
  pull := ObjComp.sabMapId Z.t
  pull_univ T g₁ g₂ h₁ h₂ := by
    obtain rfl : g₁ = g₂ := Z.m0.cart.1.hom_ext h₁ h₂
    exact congrArg (g₁ ≫ ·) (Category.comp_id _)
  smooth := h₁
  snc := h₂
  toric := h₃
  lifts _ _ _ _ _ _ _ χ _ _ := ⟨χ, Category.comp_id _⟩
  BD := BD
  BD_supp := h₄
  BD_pos := h₅
  m0 := m
  torModel_multiplicity_pos := hm

def DomAll {Xo : ∀ l : Level H, Moduli D l} (s : Sys Xo) {l : Level H} {c : Coeff l} (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (Z : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) : Prop :=
  ∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W),
    (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → Dominates Z (s.Y p W hp hW ⟨l, c, hg p hp⟩) b

end Defs

def PolMapSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X)
    (φ : InvFun (𝓞 E)) (m : ℕ) (b : O →+* O') (σ : 𝓞 E ≃+* 𝓞 E) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : TwMap σ Z'.oF.t Z.oF.t r), IsDedFrac β → IsDedFrac β' → Algebra.FiniteType ℤ O' → IsTwInv H φ → σ H.w0 = H.w0 →
    IsPol φ m Z BD → IsPol φ m Z' BD' → r ≫ Z.j ≫ Z.s = Z'.j ≫ Z'.s ≫ spMap b →
    ∃ (π : Z'.X ⟶ Z.X) (hπ : π ≫ Z.s = Z'.s ≫ spMap b) (mu : TwMap σ Z'.t Z.t π), IsFinite (pullback.lift π Z'.s hπ) ∧
      Z'.j ≫ π = r ≫ Z.j ∧ Z'.m.φ ≫ mu.cm.F = ν.cm.F ≫ Z.m.φ ∧ BD'.idealSheaf = BD.idealSheaf.comap π

def PolStableSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : TorModel Y) (φ : InvFun (𝓞 E)), IsTwInv H φ →
    IsPol φ T.m0 T.Z T.BD → IsStable T

def PolTransSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l)
    (Xo₂ : Moduli D l₂) (c : Coeff l) (c₂ : Coeff l₂) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (Y₂ : Model Xo₂ c₂ (algebraMap (𝓞 c₂.F) c₂.F)) (T : TorModel Y) (T₂ : TorModel Y₂) (φ : InvFun (𝓞 E))
    (b : 𝓞 c.F →+* 𝓞 c₂.F), 1 ≤ D.p + D.q → IsTwInv H φ → T₂.m0 = T.m0 → IsPol φ T.m0 T.Z T.BD →
    IsPol φ T.m0 T₂.Z T₂.BD → l.Dvd l₂ → (∀ x, (((b x : 𝓞 c₂.F) : c₂.F) : ℂ) = ((x : c.F) : ℂ)) → IsTorTrans T T₂ b

def PolSuppSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (BD : EffCartierData Z.X)
    (φ : InvFun (𝓞 E)), IsDedFrac β → IsPosFn H φ → IsPhiDiv φ Z BD →
    ∀ x, x ∈ BD.idealSheaf.support ↔ x ∉ abLocus Z.t.G

def PolArcSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (s : Sys Xo) (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (Z : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (BD : EffCartierData Z.X) (φ : InvFun (𝓞 E)) (m : ℕ),
    (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
    DomAll s hg Z → IsPol φ m Z BD → Z.N4

def HorizSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)), Z.N4 →
    ∀ x, x ∉ abLocus Z.t.G → x ∈ closure (genι Z '' (genBd Z : Set (gen Z)))

def PolDescSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (s : Sys Xo) (l : Level H) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (Z : ∀ c : Coeff l, Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (BD : ∀ c, EffCartierData (Z c).X)
    (φ : InvFun (𝓞 E)) (m : ℕ), l.A = 1 → IsTwInv H φ → (∀ c, DomAll s hg (Z c) ∧ IsPol φ m (Z c) (BD c)) →
    ∀ c, (Z c).Descends

def PolExSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ Xo : ∀ l : Level H, Moduli D l, ∃ (s : Sys Xo) (φ : InvFun (𝓞 E)) (m : ℕ), 0 < m ∧ IsTwInv H φ ∧ IsPosFn H φ ∧
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) ∧
      ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p),
        ∃ (Z : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (BD : EffCartierData Z.X), DomAll s hg Z ∧ IsPol φ m Z BD ∧
          SmoothOfRelativeDimension D.dim (genStr Z) ∧ FinalTheorems.Snc (genBdIdeal Z) ∧ ∀ x ∈ genBd Z, HasToricChart Z x

theorem sysEx_of_pol (hD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l),
      IsDedFrac (algebraMap (𝓞 c.F) c.F))
    (hSt : PolStableSt) (hTr : PolTransSt) (hSu : PolSuppSt) (hArc : PolArcSt) (hHo : HorizSt) (hDe : PolDescSt)
    (hEx : PolExSt) : SysExSt := by
  intro E _ _ _ H D h1 Xo
  obtain ⟨s, φ, m, hm, htw, hpos, hhom, h⟩ := hEx E H D h1 Xo
  choose Z BD hdom hpol hsm hsnc htor using h
  have hsupp := fun l c hg => hSu E H D l (Xo l) c _ _ (Z l c hg) (BD l c hg) φ (hD E H l c) hpos (hpol l c hg).1
  have hN4 := fun l c hg => hArc E H D Xo s l c hg (Z l c hg) (BD l c hg) φ m hhom (hdom l c hg) (hpol l c hg)
  let T : ∀ l c hg, TorModel (Z l c hg) := fun l c hg =>
    selfTor (Z l c hg) (hsm l c hg) (hsnc l c hg) (htor l c hg) (BD l c hg) (fun x hx => (hsupp l c hg x).1 hx)
      (fun x hx => (hsupp l c hg _).2 (mem_genBd_iff.1 hx)) m hm
  refine ⟨s, ⟨⟨Z, fun l c hg => ⟨fun hA => ?_, hdom l c hg, hN4 l c hg⟩, T, fun l c hg => ⟨(hpol l c hg).2, ?_, ?_⟩,
    fun l c hg l₂ c₂ hg₂ b hl hb => ?_⟩⟩⟩
  · exact hDe E H D Xo s l hg (fun c => Z l c hg) (fun c => BD l c hg) φ m hA htw
      (fun c => ⟨hdom l c hg, hpol l c hg⟩) c
  · exact fun x hx => hHo E H D l (Xo l) c (Z l c hg) (hN4 l c hg) x ((hsupp l c hg x).1 hx)
  · exact hSt E H D l (Xo l) c _ (T l c hg) φ htw (hpol l c hg)
  · exact hTr E H D l l₂ _ _ c c₂ _ _ (T l c hg) (T l₂ c₂ hg₂) φ b h1 htw rfl (hpol l c hg) (hpol l₂ c₂ hg₂) hl hb

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleTriangularFrameChangeFourthPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : Type) [Field K] [CharZero K] [Algebra c.F K] (t : Ix Dw → Kˣ) (y y' : FrPt Xo c K) (Φ : FibKey Xo K y.x) (Φ' : FibKey Xo K y'.x), FrBor t y y' → Tied e y.s y.u Φ → Tied e y'.s y'.u Φ' → κ K Φ'.key = kch t ^ 4 * κ K Φ.key := by
  first | exact @GlobalTheory.KeyFourth.rule_frBor | exact GlobalTheory.KeyFourth.rule_frBor | (intros; apply GlobalTheory.KeyFourth.rule_frBor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleValueAtThetaPointStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_key_rule_value_at_theta_point : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (a : ℂ) (y : FrPt Xo c (CAt σ)) (Φ : FibKey Xo ℂ y.x), a ≠ 0 → IsThetaPt T b a y → Tied (S := ℂ) e y.s y.u Φ → a ^ 8 * (κ ℂ Φ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g * (T.h b).det) ^ 4 := by
  first | exact @GlobalTheory.KeyFourth.value_at_thetaPt | exact GlobalTheory.KeyFourth.value_at_thetaPt | (intros; apply GlobalTheory.KeyFourth.value_at_thetaPt <;> assumption)
end

