import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3484
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3475
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2542
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiZeroMulRigidificationKEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.Poinc.Sep.PsiZero

theorem psi_zero_mul_rigK : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1 := by
  intro V _ _ D hB Z r z J hJ

  let T : Over (Spec (CommRingCat.of V)) := Over.mk (r ≫ (TK V).hom)
  let ρ : T ⟶ TK V := Over.homMk r rfl
  have hcub : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 0 0 0)) r z J = 1 := by
    have e := val_cub D.cub ρ hJ (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0)
    refine e.trans ?_
    rw [GlobalTheory.Poinc.ThetaOne.c_zero, MonObj.comp_one, MonObj.comp_one]
    exact (isCub_cubV D.cub hJ).face 1 1
  have hc := (val_mul hJ _ _ r).symm.trans ((val_corr hJ (hB 0 0 0) r).trans (val_mul hJ _ _ r))
  rw [hcub, _root_.mul_one,
    congrArg (fun w => val (D.tau w 0) r z J) (add_zero (0 : D.X))] at hc
  have ht : val (D.tau 0 0) r z J = 1 := (mul_eq_left.1 hc.symm)
  unfold DegPre.tau at ht
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
    congrArg (fun w => val (D.psi w) r z J) (add_zero (0 : D.X)), mul_inv_cancel, _root_.one_mul] at ht
  rw [← mul_inv, inv_eq_one] at ht
  exact ht

end GlobalTheory.Poinc.Sep.PsiZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullDegKeepsBimultActionPolarisationElement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tauBimult_and_exists_oAct_of_pullDeg : ∀ {O : Type} [CommRing O] [StarRing O] {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] {θ₀ : W →+* V} {D₀ : DegPre W} [Module O D₀.X] (o₀ : D₀.OAct O) {D : DegPre V} [Module O D.X] (hD : IsPullDeg θ₀ D₀ D) (ob : D.P.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) → (∀ (a : O) y, D.c (a • y) = D.c y ≫ ob.act a) → (∀ a : O, (ob.act a).left ≫ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀)) ≫ (o₀.onB.act a).left) → D₀.TauBimult → ∀ w0 : O, TraceFormTwistIso D₀ o₀ w0 → D.TauBimult ∧ ∃ o : D.OAct O, o.onB = ob ∧ TraceFormTwistIso D o w0 := by
  intro O _ _ W V _ _ _ _ θ₀ D₀ _ o₀ D _ hD ob hx hcl hact hB w0 hP
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hc : ∀ a : O, ob.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ₀)).map (o₀.onB.act a) := by
    intro a
    have a₂ : ((Over.pullback (specOf θ₀)).map (o₀.onB.act a)).left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) =
        pullback.fst _ _ ≫ (o₀.onB.act a).left := pullback.lift_fst _ _ _
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · have h := hact a
      simp only [Over.comp_left, Category.assoc] at h ⊢
      exact h.trans (congrArg (fun q => hD.e.hom.left ≫ q) a₂.symm)
    · exact (Over.w (ob.act a ≫ hD.e.hom)).trans
        (Over.w (hD.e.hom ≫ (Over.pullback (specOf θ₀)).map (o₀.onB.act a))).symm
  let o : D.OAct O := ⟨ob, hcl, fun a =>
    GlobalTheory.tauBal_of_isPullDeg hG _ _ θ₀ D₀ D hD (o₀.onB.act a) (o₀.onB.act (star a)) (ob.act a) (ob.act (star a))
      (o₀.onB.hom _) (o₀.onB.hom _) (o₀.onB.rosati a) (hc a) (hc (star a)) (fun y => a • y) (fun y => star a • y)
      (fun y => a • y) (fun y => star a • y) (hx a) (hx (star a)) (o₀.c_lin a) (o₀.c_lin (star a)) (o₀.tau_bal a)⟩
  exact ⟨GlobalTheory.TauPull.tauBimult_pull hG hD hB, o, rfl,
    GlobalTheory.traceFormTwistIso_of_overPullback _ _ θ₀ D₀ D hD O o₀ o hx hc w0 hP⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledLowerObjectGroupIdentification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.pulled_lowObj_grp_ident : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] (ev : V →+* K), ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ev) π₁ → ∃ θ : o'.t.G.left ⟶ B'.left, IsGrpPullback o'.t.G B' (𝟙 _) θ ∧ LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) ∧ (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hDiv K _ ev o' m₁ B' _ π₁ hπ
  obtain ⟨g, hD, -, hxe, -⟩ := hDiv
  have hsp : spMap ev ≫ specOf iw = spMap (ev.comp iw) := by
    simp [spMap, specOf, ← Spec.map_comp]
  have hii : IsGrpPullback Q.P.A L.D.P.A (specOf iw) (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    GlobalTheory.UnifPullCompare.isGrpPullback_of_bc hD.e hD.e_hom
  have h₂ : IsGrpPullback B' L.D.P.A (spMap (ev.comp iw))
      (π₁ ≫ hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    (IsGrpPullback.comp hπ hii).congr hsp rfl
  have h₁ : IsGrpPullback o'.t.G L.D.P.A (spMap (ev.comp iw)) (m₁.toSABMap.φ ≫ L.φB) :=
    (IsGrpPullback.comp m₁.cart L.ab.1).congr (Category.comp_id _) rfl
  obtain ⟨θe, hθm, hθ⟩ := grpPullback_iso h₁ h₂
  refine ⟨θe.hom.left, ?_, ?_, ?_⟩
  · haveI := hθm
    exact isGrpPullback_of_iso θe
  · have A : LBIso o'.t.PP.L (L.o.t.PP.L.pull m₁.toSABMap.φ) := GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m₁.toSABMap
    have B : LBIso (L.o.t.PP.L.pull m₁.toSABMap.φ) (L.D.P.L.pull (m₁.toSABMap.φ ≫ L.φB)) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull L.ab.2.2 _ rfl
    have C : LBIso Q.P.L (L.D.P.L.pull (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw))) :=
      ⟨hD.w, hD.w_gen⟩
    have C' : LBIso (Q.P.L.pull (θe.hom.left ≫ π₁)) (L.D.P.L.pull (m₁.toSABMap.φ ≫ L.φB)) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull C _ (by rw [← hθ]; simp only [Category.assoc])
    exact LBIso.trans o'.t.PP.isLB (pull_isLB L.D.P.isLB _) (pull_isLB Q.P.isLB _)
      (LBIso.trans o'.t.PP.isLB (pull_isLB L.o.t.PP.isLB _) (pull_isLB L.D.P.isLB _) A B) C'.symm
  · intro x a hx hc
    apply hii.1.hom_ext
    · have hcp : (Q.c a).left ≫ hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
          specOf iw ≫ (L.D.c (l.M' • e a)).left := by
        have := hD.c_pr a
        rw [hxe a] at this
        exact this
      simp only [Category.assoc]
      rw [hθ, hc, hcp, ← Category.assoc, hsp]
    · have hq : (Q.c a).left ≫ Q.P.A.hom = 𝟙 _ := Over.w (Q.c a)
      have hB : θe.hom.left ≫ B'.hom = o'.t.G.hom := Over.w θe.hom
      simp only [Category.assoc]
      rw [hπ.1.w, ← Category.assoc θe.hom.left, hB, ← Category.assoc x, hx, hq]
      simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteTautologicalChartClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem quasiFinite_of_tautB : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p = ξ (closedPoint _) → p = closedPoint _) ∧ ((residue (ChartRing k m e)).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU hS k _ m e C hC ξ hξ
  obtain ⟨⟨_, _, _, _, ⟨_, _, hft⟩, _⟩, ⟨n, s, ε, τ₀, h1, h2, h3, h4, hP⟩⟩ := hC
  have hb : ξ ≫ π ≫ zs = spMap C.b := by
    refine GlobalTheory.ChartQF.eq_spMap_of_injective (algebraMap _ (FractionRing (ChartRing k m e)))
      (IsFractionRing.injective _ _) _ _ ?_
    have e1 : i ≫ zs = pullback.snd _ _ := hU.1.2.2.2.2.1
    have e2 : j ≫ π = i := hU.2.2.2.2.1.2.2.2.2.1
    show jK _ ≫ _ = jK _ ≫ _
    rw [← Category.assoc, ← hξ, Category.assoc, reassoc_of% e2, e1, C.y_over]
  exact GlobalTheory.ChartQF.quasiFinite_of_pointRigid ξ (π ≫ zs) C.b hb hft fun K _ _ ev k₀ hk hemb hq hd =>
    hP K ev k₀ hk hemb (hS _ C (GlobalTheory.ChartQF.base_chartRing C.toFam) ξ hξ n s ε τ₀ h1 h2 h3 h4 K ev k₀ hk hq hd)

end GlobalTheory.UCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDecompositionOfTangentDivisibleByP
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLogInj

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f ((p : O) • l) → ∃ (s : MvPowerSeries (Fin d) O) (g : MvPowerSeries (Fin d) E), cob1 (up E c.μ) g = 0 ∧ QL c.μ (Ideal.span {(p : O)}) (f - map (algebraMap O E) s - g) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c E _ _ hE f l hf hL
  exact GlobalTheory.QLog.exists_int_log_of_isLie_p_smul p O E hE G d c f l hf hL

end GlobalTheory.QLogInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudSectionIdentityOfGenericFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaud_section_identity_of_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (ρ τ : SecM Y.q.left Q.P.L k) (a b : R), (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (r : Z ⟶ Y.H.left), r ≫ Y.H.hom = g ≫ jK R → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J := by
  first | exact @GlobalTheory.RayFlatDesc.main | exact GlobalTheory.RayFlatDesc.main | (intros; apply GlobalTheory.RayFlatDesc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidifiedBundlePullbackUniversalTripleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_rigidifiedBundle_pullback_universalTriple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → RelAmple tF.G tF.PP.L := by
  first | exact @GlobalTheory.PullAmpleXF.relAmple_XF | exact GlobalTheory.PullAmpleXF.relAmple_XF | (intros; apply GlobalTheory.PullAmpleXF.relAmple_XF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaledDegenerationDataDifferByScalar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RatioScalar

theorem scalar : ∀ {O : Type} [CommRing O] [StarRing O] {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module O Q.X] (oQ : Q.OAct O) (g : Q.X → (FractionRing V)ˣ) (o' : letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; (GlobalTheory.PolDeg.rescale Q g).OAct O), (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; o'.onB = oQ.onB) → Q.TauBimult → (GlobalTheory.PolDeg.rescale Q g).TauBimult → ∀ w0 : O, TraceFormTwistIso Q oQ w0 → (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; TraceFormTwistIso (GlobalTheory.PolDeg.rescale Q g) o' w0) → ∃ q : Q.X → Q.X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : O) a b, q (x • a) b = q a (star x • b)) ∧ ∀ y, (g y)⁻¹ = q y (w0 • y) := by
  intro O _ _ V _ _ Q _ oQ g o' ho hB hB' w0 hW hW'
  obtain ⟨hs, hd⟩ := GlobalTheory.RescaleForm.main Q oQ w0 g hB hW hB' o' ho hW'
  exact ⟨fun a b => (g (a + b) * (g a)⁻¹ * (g b)⁻¹)⁻¹, hs.inv.symm, hs.inv.add_left, hs.inv.bal,
    fun y => congrArg (·⁻¹) (hd y)⟩

end GlobalTheory.RatioScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimAddTrdegCompletionPolynomial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CDimAlg

theorem trdeg_lt_aleph0_of_essFiniteType (F W : Type) [Field F] [CommRing W] [IsDomain W] [Algebra F W]
    [Algebra.EssFiniteType F W] : Algebra.trdeg F W < Cardinal.aleph0 := by
  set W₀ := Algebra.EssFiniteType.subalgebra F W
  haveI : FaithfulSMul W₀ W := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic W₀ W := IsLocalization.isAlgebraic W (Algebra.EssFiniteType.submonoid F W)
  have h := trdeg_add_eq F W₀ (A := W)
  rw [trdeg_eq_zero (R := W₀) (A := W), add_zero] at h
  rw [← h]
  exact trdeg_lt_aleph0_of_finiteType

theorem exists_nat_of_add_eq {d : WithBot ℕ∞} {n m : ℕ} (h : d + n = m) : ∃ k : ℕ, d = k ∧ k + n = m := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ + n : ℕ∞) : WithBot ℕ∞) = ((m : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_inj, top_add] at h'
      exact ENat.top_ne_natCast m h'
    | coe k =>
      refine ⟨k, rfl, ?_⟩
      exact_mod_cast h

end GlobalTheory.CDimAlg

namespace GlobalTheory.CDimAlg

theorem ringKrullDim_add_trdeg_of_isComplAt : ∀ (F W R : Type) [Field F] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R] [IsLocalRing R] (b : F →+* W), b.EssFiniteType → ∀ (I : Type) [Fintype I] (ψ : MvPolynomial I W →+* R), GlobalTheory.TChart.IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) → ∀ bR : F →+* R, (ψ.comp MvPolynomial.C).comp b = bR → ((residue R).comp bR).EssFiniteType ∧ ∀ a t : ℕ, ringKrullDim W = a → (letI := ((residue W).comp b).toAlgebra; Algebra.trdeg F (ResidueField W) = t) → ∃ a' t' : ℕ, ringKrullDim R = a' ∧ (letI := ((residue R).comp bR).toAlgebra; Algebra.trdeg F (ResidueField R) = t') ∧ a' + t' = a + t + Fintype.card I := by
  intro F W R _ _ _ _ _ _ b hb I _ ψ hψ hloc bR hbR
  obtain ⟨hRn, -, hfl, hmap, hres⟩ := hψ
  letI : Algebra F W := b.toAlgebra
  haveI : Algebra.EssFiniteType F W := hb
  haveI : IsNoetherianRing W := Algebra.EssFiniteType.isNoetherianRing F W
  set q : Ideal (MvPolynomial I W) := (maximalIdeal R).comap ψ with hq
  haveI : q.IsPrime := Ideal.comap_isPrime ψ _
  have hmemq : ∀ x, x ∈ q ↔ ¬ IsUnit (ψ x) := fun x => by
    rw [hq, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  have hu : ∀ s : q.primeCompl, IsUnit (ψ s) := fun s => by
    have h := s.2
    rw [Ideal.mem_primeCompl_iff, hmemq, not_not] at h
    exact h
  let ψA : Localization.AtPrime q →+* R := IsLocalization.lift hu
  have hψA' : ∀ x, ψA (algebraMap _ (Localization.AtPrime q) x) = ψ x := fun x => IsLocalization.lift_eq hu x
  have hψA : ψA.comp (algebraMap _ (Localization.AtPrime q)) = ψ := RingHom.ext hψA'
  haveI hlocA : IsLocalHom ψA := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    have e1 := IsLocalization.mk'_spec (Localization.AtPrime q) p s
    have hp : IsUnit (ψ p) := by
      rw [← hψA', ← e1, map_mul, hψA']
      exact hx.mul (hu s)
    have hpq : p ∈ q.primeCompl := by
      rw [Ideal.mem_primeCompl_iff, hmemq, not_not]; exact hp
    have h2 : IsUnit (algebraMap _ (Localization.AtPrime q) p) := IsLocalization.map_units _ ⟨p, hpq⟩
    rw [← e1] at h2
    exact isUnit_of_mul_isUnit_left h2
  letI : Algebra (MvPolynomial I W) R := ψ.toAlgebra
  letI : Algebra (Localization.AtPrime q) R := ψA.toAlgebra
  haveI : IsScalarTower (MvPolynomial I W) (Localization.AtPrime q) R :=
    IsScalarTower.of_algebraMap_eq (fun x => (hψA' x).symm)
  haveI : Module.Flat (MvPolynomial I W) R := hfl
  haveI : Module.Flat (Localization.AtPrime q) R :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime q) q.primeCompl R).2 inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  haveI : IsNoetherianRing R := hRn
  haveI : IsLocalHom (algebraMap (Localization.AtPrime q) R) := hlocA
  have hmA : (maximalIdeal (Localization.AtPrime q)).map (algebraMap (Localization.AtPrime q) R) = maximalIdeal R := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    change q.map (ψA.comp (algebraMap _ (Localization.AtPrime q))) = _
    rw [hψA]; exact hmap
  have hdim : ringKrullDim (Localization.AtPrime q) = ringKrullDim R :=
    GlobalTheory.RegSmooth.ringKrullDim_eq_of_flat_of_map_maximalIdeal hmA

  let κ : ResidueField (Localization.AtPrime q) →+* ResidueField R := ResidueField.map ψA
  have hκs : Function.Surjective κ := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    obtain ⟨a, c, hc, hr⟩ := hres r
    have hcq : c ∈ q.primeCompl := by rw [Ideal.mem_primeCompl_iff, hmemq, not_not]; exact hc
    refine ⟨residue _ (IsLocalization.mk' (Localization.AtPrime q) a ⟨c, hcq⟩), ?_⟩
    have e1 : ψA (IsLocalization.mk' (Localization.AtPrime q) a ⟨c, hcq⟩) * ψ c = ψ a := by
      rw [← hψA' c, ← map_mul, IsLocalization.mk'_spec, hψA']
    have e2 : residue R (r * ψ c) = residue R (ψ a) := Ideal.Quotient.eq.2 hr
    have hne : residue R (ψ c) ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hc
    change residue R (ψA _) = residue R r
    refine mul_right_cancel₀ hne ?_
    rw [← map_mul, e1, ← e2, map_mul]
  let e : ResidueField (Localization.AtPrime q) ≃+* ResidueField R := RingEquiv.ofBijective κ ⟨κ.injective, hκs⟩
  have hcomp : ∀ x : F, e (residue _ (algebraMap F (Localization.AtPrime q) x)) = residue R (bR x) := by
    intro x
    change residue R (ψA _) = _
    rw [IsScalarTower.algebraMap_apply F (MvPolynomial I W) (Localization.AtPrime q), hψA', ← hbR]
    rfl
  haveI : Algebra.EssFiniteType F (MvPolynomial I W) := Algebra.EssFiniteType.comp F W _
  haveI : Algebra.EssFiniteType (MvPolynomial I W) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_isLocalization _ q.primeCompl
  haveI hAft : Algebra.EssFiniteType F (Localization.AtPrime q) :=
    Algebra.EssFiniteType.comp F (MvPolynomial I W) _
  have hresA : ((residue (Localization.AtPrime q)).comp (algebraMap F (Localization.AtPrime q))).EssFiniteType :=
    RingHom.EssFiniteType.comp (RingHom.essFiniteType_algebraMap.2 hAft)
      (RingHom.FiniteType.of_surjective _ residue_surjective).essFiniteType
  have hRe : (residue R).comp bR =
      e.toRingHom.comp ((residue (Localization.AtPrime q)).comp (algebraMap F (Localization.AtPrime q))) :=
    RingHom.ext fun x => (hcomp x).symm
  refine ⟨?_, ?_⟩
  · rw [hRe]
    exact RingHom.EssFiniteType.comp hresA (RingHom.FiniteType.of_surjective _ e.surjective).essFiniteType
  intro a t ha ht

  obtain ⟨mW, hmW⟩ : ∃ m : ℕ, Algebra.trdeg F W = m :=
    Cardinal.lt_aleph0.1 (trdeg_lt_aleph0_of_essFiniteType F W)
  have hW : ringKrullDim W + t = mW := by
    letI : Algebra F (ResidueField W) := ((residue W).comp b).toAlgebra
    haveI : IsScalarTower F W (ResidueField W) := IsScalarTower.of_algebraMap_eq' rfl
    exact GlobalTheory.LocModelDim.ringKrullDim_add_trdeg (k := F) (R := W) (Ω := ResidueField W) residue_surjective ht hmW

  haveI : FaithfulSMul F W := (faithfulSMul_iff_algebraMap_injective _ _).2 b.injective
  haveI : FaithfulSMul W (MvPolynomial I W) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective I W)
  have hP : Algebra.trdeg F (MvPolynomial I W) = ((mW + Fintype.card I : ℕ) : Cardinal) := by
    rw [← trdeg_add_eq F W (A := MvPolynomial I W), MvPolynomial.trdeg_of_isDomain, hmW, Cardinal.lift_id,
      Cardinal.mk_fintype]
    push_cast; rfl
  haveI : FaithfulSMul (MvPolynomial I W) (Localization.AtPrime q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors)
  haveI : Algebra.IsAlgebraic (MvPolynomial I W) (Localization.AtPrime q) :=
    IsLocalization.isAlgebraic _ q.primeCompl
  have hA : Algebra.trdeg F (Localization.AtPrime q) = ((mW + Fintype.card I : ℕ) : Cardinal) := by
    rw [← trdeg_add_eq F (MvPolynomial I W) (A := Localization.AtPrime q),
      trdeg_eq_zero (R := MvPolynomial I W) (A := Localization.AtPrime q), add_zero, hP]

  letI alA : Algebra F (ResidueField (Localization.AtPrime q)) :=
    ((residue (Localization.AtPrime q)).comp (algebraMap F (Localization.AtPrime q))).toAlgebra
  haveI : IsScalarTower F (Localization.AtPrime q) (ResidueField (Localization.AtPrime q)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType F (ResidueField (Localization.AtPrime q)) := hresA
  obtain ⟨tA, htA⟩ : ∃ m : ℕ, Algebra.trdeg F (ResidueField (Localization.AtPrime q)) = m :=
    Cardinal.lt_aleph0.1 (trdeg_lt_aleph0 F (ResidueField (Localization.AtPrime q)))
  have hAf := GlobalTheory.LocModelDim.ringKrullDim_add_trdeg (k := F) (R := Localization.AtPrime q)
    (Ω := ResidueField (Localization.AtPrime q)) residue_surjective htA hA
  obtain ⟨k, hk, hkt⟩ := exists_nat_of_add_eq hAf
  letI alR : Algebra F (ResidueField R) := ((residue R).comp bR).toAlgebra
  let eA : ResidueField (Localization.AtPrime q) ≃ₐ[F] ResidueField R := { e with commutes' := fun x => hcomp x }
  refine ⟨k, tA, by rw [← hdim, hk], by rw [← eA.trdeg_eq, htA], ?_⟩
  obtain ⟨a0, ha0, ha0t⟩ := exists_nat_of_add_eq hW
  rw [ha] at ha0
  have : a = a0 := by exact_mod_cast ha0
  omega

end GlobalTheory.CDimAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecBEqEverywhereOfGenericAgreeConstStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secB_eq_everywhere_of_generic_agree_const : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (β : Q.X) (s s' : Q.SecB k β) (c : R), c ≠ 0 → (∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s' (DegPre.prB Q (FractionRing R)).left z J) → ∀ (Z : Scheme.{0}) (x : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval s x z J = sval s' x z J := by
  first | exact @GlobalTheory.SecBGenericAgree.main | exact GlobalTheory.SecBGenericAgree.main | (intros; apply GlobalTheory.SecBGenericAgree.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShimuraObjectPullbackCompCancel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem obj_pull_comp_cancel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}, (∀ {S S' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s) (f : S' ⟶ S) (s' : S' ⟶ Sp (KA l)), s' = f ≫ s → ∃ o' : Obj D l (baseKA l) s', Nonempty (ObjMap o' o f)) ∧ (∀ {S S' S'' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (s'' : S'' ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s) (o' : Obj D l (baseKA l) s') (o'' : Obj D l (baseKA l) s'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : ObjMap o' o f), (∀ n : ObjMap o'' o' g, ∃ k : ObjMap o'' o (g ≫ f), k.toSABMap.φ = n.toSABMap.φ ≫ m.toSABMap.φ) ∧ ∀ k : ObjMap o'' o (g ≫ f), ∃ n : ObjMap o'' o' g, k.toSABMap.φ = n.toSABMap.φ ≫ m.toSABMap.φ) := by
  intro E _ _ _ H D l
  refine ⟨fun {S S'} s o f s' hs => ?_, fun {S S' S''} s s' s'' o o' o'' f g m =>
    ⟨fun n => ObjComp.objMap_comp m n, fun k => ObjComp.objMap_cancel m k⟩⟩
  exact obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ S' _ s' f rfl rfl
    (hs.symm.trans ((Category.comp_id _).symm.trans (congrArg (s' ≫ ·) (Spec.map_id _).symm))) o

end GlobalTheory.UCanon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionShimuraObjectAbelianSch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UObjDim

theorem smoothOfRelativeDimension_obj : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Geo.Tor.Level H) {S : Scheme.{0}} (s : S ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s), SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom :=
  fun _ _ _ _ o => GlobalTheory.ObjDim.smoothOfRelativeDimension o

end GlobalTheory.UObjDim
end

