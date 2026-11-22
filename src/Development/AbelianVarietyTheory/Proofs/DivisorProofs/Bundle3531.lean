import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3511
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3479
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3501
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledLowerObjectGroupIdentificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledLowerObject_group_identification : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] (ev : V →+* K), ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ev) π₁ → ∃ θ : o'.t.G.left ⟶ B'.left, IsGrpPullback o'.t.G B' (𝟙 _) θ ∧ LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) ∧ (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) := by
  first | exact @GlobalTheory.UCanon.pulled_lowObj_grp_ident | exact GlobalTheory.UCanon.pulled_lowObj_grp_ident | (intros; apply GlobalTheory.UCanon.pulled_lowObj_grp_ident <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteTautologicalChartClosedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiFinite_tautologicalChart_closedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p = ξ (closedPoint _) → p = closedPoint _) ∧ ((residue (ChartRing k m e)).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  first | exact @GlobalTheory.UCanon.quasiFinite_of_tautB | exact GlobalTheory.UCanon.quasiFinite_of_tautB | (intros; apply GlobalTheory.UCanon.quasiFinite_of_tautB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDecompositionOfTangentDivisibleByPStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_decomposition_of_tangent_divisible_by_p : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f ((p : O) • l) → ∃ (s : MvPowerSeries (Fin d) O) (g : MvPowerSeries (Fin d) E), cob1 (up E c.μ) g = 0 ∧ QL c.μ (Ideal.span {(p : O)}) (f - map (algebraMap O E) s - g) := by
  first | exact @GlobalTheory.QLogInj.main | exact GlobalTheory.QLogInj.main | (intros; apply GlobalTheory.QLogInj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyAmpleClosedImmersion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relatively_ample_closed_immersion : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∀ V₀ : S'.Opens, IsAffineOpen V₀ → Out.RelAmple ((Over.pullback V₀.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)).pull (lift (𝟙 ((Over.pullback V₀.ι).obj G)) (𝟙 ((Over.pullback V₀.ι).obj G))).left) → ∀ (Z : Over S') (i : Z ⟶ G), IsClosedImmersion i.left → (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) (z ≫ i)) → IsFinite (Z.hom ∣_ V₀) := by
  first | (exact @GlobalTheory.KernelRepFinite.isFinite_restrict) | (exact GlobalTheory.KernelRepFinite.isFinite_restrict) | (intros; apply GlobalTheory.KernelRepFinite.isFinite_restrict  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaledDegenerationDataDifferByScalarStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rescaled_degenerationData_differ_by_scalar : ∀ {O : Type} [CommRing O] [StarRing O] {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module O Q.X] (oQ : Q.OAct O) (g : Q.X → (FractionRing V)ˣ) (o' : letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; (GlobalTheory.PolDeg.rescale Q g).OAct O), (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; o'.onB = oQ.onB) → Q.TauBimult → (GlobalTheory.PolDeg.rescale Q g).TauBimult → ∀ w0 : O, TraceFormTwistIso Q oQ w0 → (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; TraceFormTwistIso (GlobalTheory.PolDeg.rescale Q g) o' w0) → ∃ q : Q.X → Q.X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : O) a b, q (x • a) b = q a (star x • b)) ∧ ∀ y, (g y)⁻¹ = q y (w0 • y) := by
  first | exact @GlobalTheory.RatioScalar.scalar | exact GlobalTheory.RatioScalar.scalar | (intros; apply GlobalTheory.RatioScalar.scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidCubicalExtensionPullbackOfToricChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCubExt

theorem cube_pull_of_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] {m n : ℕ} (tC : SAB H (Sp (ChartRing k m n))) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp (ChartRing k m n) ⟶ S) (πC : tC.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tC.G G ξ πC → ∀ (PP : RigLB G) (cub : CubicalStr G PP) {X' : Scheme.{0}} (tF : SAB H X') (j : X' ⟶ S) (e : tF.G.left ⟶ G.left) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ (y : Sp (FractionRing (ChartRing k m n)) ⟶ X'), y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK tC (jK _)) (b : SABMap tK tF y), a.φ ≫ πC = b.φ ≫ e → ∃ cm' : CubeMap tC.G G, cm'.F = πC ∧ cm'.e = ξ ∧ cm'.IsPullCubical tC.cub cub := by
  intro E _ _ _ H k _ m n tC S G _ _ ξ πC hG hπ PP cub X' tF j e cm hcF hce hcm y hy tK a b hab
  refine ⟨cubeMapOf hπ, rfl, rfl, ?_⟩
  let c2 : CubeMap tK.G G :=
    { F := b.cm.F ≫ cm.F, F3 := b.cm.F3 ≫ cm.F3, e := b.cm.e ≫ cm.e
      e_comm := by rw [← Category.assoc, b.cm.e_comm, Category.assoc, cm.e_comm, Category.assoc]
      psum_comm := fun I => by
        rw [← Category.assoc, b.cm.psum_comm, Category.assoc, cm.psum_comm, Category.assoc] }
  let c3 : CubeMap tK.G G :=
    { F := a.cm.F ≫ (cubeMapOf hπ).F, F3 := a.cm.F3 ≫ (cubeMapOf hπ).F3, e := a.cm.e ≫ (cubeMapOf hπ).e
      e_comm := by rw [← Category.assoc, a.cm.e_comm, Category.assoc, (cubeMapOf hπ).e_comm, Category.assoc]
      psum_comm := fun I => by
        rw [← Category.assoc, a.cm.psum_comm, Category.assoc, (cubeMapOf hπ).psum_comm, Category.assoc] }
  have H2 : c2.IsPullCubical tK.cub cub :=
    pullCubComp _ _ _ _ _ _ cm b.cm c2 _ _ _ _ _ _ rfl rfl rfl hcm b.lin
  have h₁ : c2.F = a.cm.F ≫ (cubeMapOf hπ).F := by
    show b.cm.F ≫ cm.F = a.cm.F ≫ πC
    rw [hcF]; exact hab.symm
  have h₂ : c2.F3 = a.cm.F3 ≫ (cubeMapOf hπ).F3 := by
    show c2.F3 = c3.F3
    refine hom_ext_triple _ fun i => ?_
    rw [cubeMap_comp_proj_three c2 i, cubeMap_comp_proj_three c3 i]
    exact congrArg (fun z => (x3 tK.G i).left ≫ z) h₁
  have h₃ : c2.e = a.cm.e ≫ (cubeMapOf hπ).e := by
    show b.cm.e ≫ cm.e = a.cm.e ≫ ξ
    rw [b.base, hce, a.base, hy]
  exact GlobalTheory.ChartCubExt.isPullCubical_of_generic_of_ext (GlobalTheory.T.extendsGenericRigidifiedGenerator_toricChartPowerSeriesRing k m n) tC.semi cub tC.cub tK.cub
    (cubeMapOf hπ) a.cm c2 a.cart.1 a.base h₁ h₂ h₃ a.lin H2

end GlobalTheory.ChartCubExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimAddTrdegCompletionPolynomialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_add_trdeg_completion_polynomial : ∀ (F W R : Type) [Field F] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R] [IsLocalRing R] (b : F →+* W), b.EssFiniteType → ∀ (I : Type) [Fintype I] (ψ : MvPolynomial I W →+* R), GlobalTheory.TChart.IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) → ∀ bR : F →+* R, (ψ.comp MvPolynomial.C).comp b = bR → ((residue R).comp bR).EssFiniteType ∧ ∀ a t : ℕ, ringKrullDim W = a → (letI := ((residue W).comp b).toAlgebra; Algebra.trdeg F (ResidueField W) = t) → ∃ a' t' : ℕ, ringKrullDim R = a' ∧ (letI := ((residue R).comp bR).toAlgebra; Algebra.trdeg F (ResidueField R) = t') ∧ a' + t' = a + t + Fintype.card I := by
  first | exact @GlobalTheory.CDimAlg.ringKrullDim_add_trdeg_of_isComplAt | exact GlobalTheory.CDimAlg.ringKrullDim_add_trdeg_of_isComplAt | (intros; apply GlobalTheory.CDimAlg.ringKrullDim_add_trdeg_of_isComplAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SabMapKeepsLevelEta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem toUnit_left_eq' {X : Scheme.{0}} (T : Over X) : (toUnit T).left = T.hom := by
  have := Over.w (toUnit T)
  simpa using this

theorem grpPullback_pow_succ {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G')
    (x₀ : Over.mk (T.hom ≫ f) ⟶ G) (hx : x₀.left = x.left ≫ φ) (n : ℕ) :
    (x₀ ^ (n + 1)).left = (x ^ (n + 1)).left ≫ φ := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ x₀, pow_succ x]
    exact hφ.2 T _ _ _ _ ih hx

theorem eta_eq_etaA_pow {D : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {bb : Base (LowDat.lowLevel l) B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D (LowDat.lowLevel l) bb s) (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) (β : B →+* k) (hx : x ≫ s = spMap β) (a : D.La)
    (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    toUnit (Over.mk x) ≫ o.eta a = (toUnit (Over.mk x) ≫ o.etaA a) ^ (l.M' / l.M) := by
  obtain ⟨-, I, -, hA, hM⟩ := o.geom k x β hx
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hdvd : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
  have hM'0 : 0 < l.M' := Nat.lcm_pos hM0 l.A_pos
  have hq : 0 < l.M' / l.M := Nat.div_pos (Nat.le_of_dvd hM'0 hdvd) hM0
  have hmul : l.M * (l.M' / l.M) = (LowDat.lowLevel l).A := Nat.mul_div_cancel' hdvd
  rw [hM a ha, hA a, ← hmul]
  exact (I.tower l.M (l.M' / l.M) hM0 hq a).symm

end GlobalTheory.UCanon

namespace GlobalTheory.UCanon

theorem sabMap_keeps_eta : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (A W : Type) [CommRing A] [IsDomain A] [CommRing W] (bA : c.F →+* A) (b : c.F →+* W) (o' : LowObj D c bA) (o : LowObj D c b) (f : W →+* A), f.comp b = bA → ∀ m : SABMap o'.t o.t (spMap f), (∀ a, (o'.etaA a).left ≫ m.φ = spMap f ≫ (o.etaA a).left) → ∀ a, (o'.eta a).left ≫ m.φ = spMap f ≫ (o.eta a).left := by
  intro E _ _ _ H D l c A W _ _ _ bA b o' o f hf m hA a
  subst hf

  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  have ha : u • a + v • a = a := by rw [← add_smul, huv, one_smul]
  have hu' : u • a ∈ (LowDat.lowLevel l).Mb • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hu Submodule.mem_top
  have hv' : v • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hv Submodule.mem_top
  have e1 : o'.eta a = o'.eta (v • a) := by
    conv_lhs => rw [← ha]
    rw [o'.eta_add, o'.eta_ker _ hu', _root_.one_mul]
  have e2 : o.eta a = o.eta (v • a) := by
    conv_lhs => rw [← ha]
    rw [o.eta_add, o.eta_ker _ hu', _root_.one_mul]
  rw [e1, e2]
  generalize v • a = a' at hv' ⊢

  let K := AlgebraicClosure (FractionRing A)
  let κ : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hκ : Function.Injective κ :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  haveI : IsDominant (spMap κ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical κ).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hκ]; exact bot_le)⟩
  haveI := o.proper
  haveI : IsReduced (𝟙_ (Over (Sp A))).left := (inferInstance : IsReduced (Sp A))
  refine ext_of_isDominant_of_isSeparated o.t.G.hom ?_ (spMap κ) ?_
  · have w1 := Over.w (o'.eta a')
    have w2 := Over.w (o.eta a')
    have w3 := m.cart.1.w
    simp only [Category.assoc]
    rw [w3, ← Category.assoc, w1, w2]
    simp
  · let β : KA (LowDat.lowLevel l) →+* K := κ.comp ((f.comp b).comp (IntermediateField.inclusion (LowDat.ka_le l c)).toRingHom)
    have hx' : spMap κ ≫ lowMap c (f.comp b) = spMap β := by
      unfold lowMap; rw [← Spec.map_comp]; rfl
    have hx : (spMap κ ≫ spMap f) ≫ lowMap c b = spMap β := by
      unfold lowMap; rw [← Spec.map_comp, ← Spec.map_comp]; rfl
    have p' := eta_eq_etaA_pow o' K (spMap κ) β hx' a' hv'
    have p := eta_eq_etaA_pow o K (spMap κ ≫ spMap f) β hx a' hv'
    have hM0 : 0 < l.M := by have := l.three_le; omega
    have hdvd : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
    have hq : 0 < l.M' / l.M := Nat.div_pos (Nat.le_of_dvd (Nat.lcm_pos hM0 l.A_pos) hdvd) hM0
    obtain ⟨n, hn⟩ : ∃ n, l.M' / l.M = n + 1 := ⟨l.M' / l.M - 1, by omega⟩
    rw [hn] at p p'
    have key := grpPullback_pow_succ m.cart (T := Over.mk (spMap κ)) (toUnit _ ≫ o'.etaA a')
      (toUnit (Over.mk (spMap κ ≫ spMap f)) ≫ o.etaA a') (by
        rw [Over.comp_left, Over.comp_left, toUnit_left_eq', toUnit_left_eq']
        simp only [Over.mk_hom, Category.assoc]
        rw [hA a']) n
    have q' := congrArg Over.Hom.left p'
    have q := congrArg Over.Hom.left p
    rw [Over.comp_left, toUnit_left_eq'] at q q'
    simp only [Over.mk_hom] at q q'
    rw [← Category.assoc, q', ← key, ← q, Category.assoc]

end GlobalTheory.UCanon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionCountGrowthMetricNearGeneratorMax
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem lc_exp_bounds : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ κ t : ℝ, 0 < κ → κ ≤ 1 → 0 < t → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), P.nu e 0 σ y (x l) ≤ 1) → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, gdeg P.L D / D.factorial * t - ε ≤ P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) ∧ P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) ≤ gdeg P.L D / D.factorial * (t - Real.log κ / e) + ε := by
  intro hA k _ X _ p D hp P hL e x hx κ t hκ hκ1 ht h1 h2 ε hε
  have hdeg := GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree hA k X p D hp P hL e x hx
  have hup := GlobalTheory.T.arithHilbertSamuel_upperBound_count_rank_ample k X p D hp P hL e x hx
  have hlo := GlobalTheory.T.arithHilbertSamuel_lowerBound_count_rank_ample k X p D hp P hL e x hx
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hfin : ∀ (m : ℕ) (R : ℝ), 0 ≤ R → (P.Bl m 1 R).Finite := by
    intro m R hR
    obtain ⟨c, C, _, h⟩ := hup m 1
    have := ((h 0).2.2 R κ hR hκ h2).1
    simpa using this
  have key := GlobalTheory.T.count_growth_exponential_radii D e (Module.finrank (ratF x) X.functionField) (fun m R => (P.Bl m 1 R).ncard) κ t
    hx.pos hκ hκ1 ht
    (fun m R R' hR hRR' => Set.ncard_le_ncard
      (fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans hRR'⟩) (hfin m R' (hR.trans hRR')))
    (fun s _ => by
      obtain ⟨c, C, hC, h⟩ := hlo s 1
      obtain ⟨c', C', hC', h'⟩ := hup s 1
      refine ⟨c, c', C, C', hC, hC', fun q R hR => ⟨?_, ?_⟩⟩
      · have h3 := (h q).2 R hR h1
        have hf := hfin (e * (q + c) + s) (C * (q + D).choose D * R) (by positivity)
        have e1 : ((e * (q + c) + s : ℕ) : ℤ) = e * (q + c : ℕ) + s := by push_cast; ring
        rw [← e1, ← hf.cast_ncard_eq] at h3
        exact_mod_cast h3
      · have h3 := ((h' q).2.2 R κ hR hκ h2).2
        have e1 : ((e * q + s : ℕ) : ℤ) = e * q + s := by push_cast; ring
        rw [← e1] at h3
        exact h3) ε hε
  have e2 : (Module.finrank (ratF x) X.functionField : ℝ) / ((e : ℝ) ^ D * D.factorial) =
      gdeg P.L D / D.factorial := by
    rw [hdeg, mul_div_mul_left _ _ (pow_pos he D).ne']
  rw [e2] at key
  exact key

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionCanonicalWeightsTendstoZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem selfInter_canWeight_le : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField),
    Gens P D e x → ∃ C : ℝ, ∀ (n : ℕ) (u : SmFn p) (a : ℝ), 1 ≤ n → IsCan P e n x u →
      (up P.L u).IsSelfInter a → |a| ≤ C / n := by
  intro hC k _ X _ p D hX P hA e x hG
  haveI := hX.isDomain
  haveI := hX.finite
  haveI := hX.charZero_base
  have hf : 0 < Module.finrank ℤ k := Module.finrank_pos
  have he : 0 < e := hG.pos
  obtain ⟨hPI, -, -, -, -, -, -⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hA e x hG
  obtain ⟨hPV, -, -⟩ := GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D

  obtain ⟨Φ₀, hΦ₀⟩ := ((hC.arExists k (PSpace k D) (PSpace.str k D) D hPV).2 Unit
    fun _ => ProjSpace.hermitianTwistingSheaf k D).1
  have hH := ((hC.arIso k (PSpace k D) (PSpace.str k D) D hPV).2 Unit _ Φ₀ hΦ₀).1 ()
  set H := Φ₀ (MvPolynomial.X () ^ (D + 1)) with hHdef
  set g := gdeg P.L D
  refine ⟨|g * H| / ((Module.finrank ℤ k : ℝ) * e), fun n u a hn hu ha => ?_⟩
  obtain ⟨-, -, -, hG', hu'⟩ := GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy k X p D hX P e x hG n u hn hu
  obtain ⟨hPI', π, hπ, hgen, hd, hdf, hiso⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hA (e * n) _ hG'
  have hdeg := GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree hC k X p D hX P hA (e * n) _ hG'
  have hpow := (GlobalTheory.T.geometricDegree_projectionFormula_selfInter_pow hC k X p D hX).2 (up P.L u) (e * n) a ha
  have hpull := ((hC.arProj k (PSpace k D) X (PSpace.str k D) p D hPV hX π hπ hgen hd).1 _ H hH)

  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => (up P.L u).pow (e * n)).1
  have hI := hC.arIso k X p D hX
  have h₁ := (hI.2 Unit _ Φ hΦ).1 ()
  have hΦ' := (hI.2 Unit _ Φ hΦ).2.1 (fun _ => (ProjSpace.hermitianTwistingSheaf k D).pull π hπ) fun _ => hiso u hu'
  have h₂ := (hI.2 Unit _ Φ hΦ').1 ()
  have e₁ := HermLB.IsSelfInter.unique hX hpow h₁
  have e₂ := HermLB.IsSelfInter.unique hX hpull h₂

  set d : ℝ := ((π.residueDegree (genericPoint X) : ℕ) : ℝ)
  set f : ℝ := ((Module.finrank ℤ k : ℕ) : ℝ)
  set E : ℝ := ((e * n : ℕ) : ℝ)
  have hE : 0 < E := by positivity
  have hfpos : (0 : ℝ) < f := Nat.cast_pos.mpr hf
  have key1 : E ^ (D + 1) * a = d * H := e₁.trans e₂.symm
  have key2 : d * f = E ^ D * g := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hdf
    simp only [Nat.cast_mul] at this
    rw [← hdeg]; exact this
  have ha' : a = g * H / (f * E) := by
    field_simp
    have : E ^ (D + 1) * a * f = E ^ D * g * H := by rw [key1, ← key2]; ring
    have hED : E ^ D ≠ 0 := pow_ne_zero _ hE.ne'
    apply mul_left_cancel₀ hED
    linear_combination this
  rw [ha', abs_div, abs_of_pos (by positivity : (0:ℝ) < f * E)]
  have : f * E = (f * e) * n := by simp [E, f]; ring
  rw [this, div_div]

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShimuraObjectPullbackCompCancelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shimuraObject_pullback_comp_cancel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}, (∀ {S S' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s) (f : S' ⟶ S) (s' : S' ⟶ Sp (KA l)), s' = f ≫ s → ∃ o' : Obj D l (baseKA l) s', Nonempty (ObjMap o' o f)) ∧ (∀ {S S' S'' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (s'' : S'' ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s) (o' : Obj D l (baseKA l) s') (o'' : Obj D l (baseKA l) s'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : ObjMap o' o f), (∀ n : ObjMap o'' o' g, ∃ k : ObjMap o'' o (g ≫ f), k.toSABMap.φ = n.toSABMap.φ ≫ m.toSABMap.φ) ∧ ∀ k : ObjMap o'' o (g ≫ f), ∃ n : ObjMap o'' o' g, k.toSABMap.φ = n.toSABMap.φ ≫ m.toSABMap.φ) := by
  first | exact @GlobalTheory.UCanon.obj_pull_comp_cancel | exact GlobalTheory.UCanon.obj_pull_comp_cancel | (intros; apply GlobalTheory.UCanon.obj_pull_comp_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortOfInputsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_of_inputs : Hypotheses2 → DeepGood → Size → FlatDeg → Short := by
  first | exact @GlobalTheory.CovHt.ShortPf.short | exact GlobalTheory.CovHt.ShortPf.short | (intros; apply GlobalTheory.CovHt.ShortPf.short <;> assumption)
end

