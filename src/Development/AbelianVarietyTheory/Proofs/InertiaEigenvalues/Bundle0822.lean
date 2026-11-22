import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0811
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0039
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0041
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0795
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0812
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0022
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0499
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0141
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ConjTwist
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefActIo

variable {D : D7}

section Gen

variable {S T : HSp D}

theorem om_fock_of_vac {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hB : B.Good) (hψ : ψ.Good)
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S)
    (P : PolF D T.rank S.rank) : ω (u, 1) (B.F.fock f P) = B.F.fock f (B.act u P) := by
  have hθ := hB.frame.vac.2.inf
  have hBS := fun τ => GlobalTheory.RealFockAction.onb_posDef (hB.frame.onbS τ)
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have eu : ∀ τ, (inBasis B.F.BS (realGL B.F.θ S u) τ).val =
      (B.F.BS τ).val⁻¹ * compAt B.F.θ τ (Formalism.L2.Theta.mt S u) * (B.F.BS τ).val := fun τ => by
    rw [← Matrix.coe_units_inv]
    rfl
  have hle : ∀ τ, B.w.p τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  unfold Frame.fock
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hθ (fun _ => 1) (fun _ => 1) (fun τ => (B.F.BS τ).val)
    (fun τ => (B.F.BS τ).val * (inBasis B.F.BS (realGL B.F.θ S u) τ).val) B.F.sT B.F.sT B.F.BT B.F.BT u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.coe_units_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, GlobalTheory.RealFockAction.om_vac hB hψ hω hf hv hu,
    GlobalTheory.FiniteFock.pureTensorO_smul,
    GlobalTheory.RealFockAction.pureTensorO_subst (p := B.w.p) hB.frame.vac.1 hθ
      (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)) hB.frame.cartT
      (fun τ => (GlobalTheory.RealFockAction.onb_laws (by have := hB.frame.onbT τ; rwa [← hB.sig τ] at this) (hle τ)).1) _ _
      (fun τ => by rw [eu]; exact GlobalTheory.RealFockAction.conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S u τ)) hf,
    Base.act, MonoidHom.comp_apply, fockGL_apply, LinearMap.map_smul]

theorem act_of_mem_GfC (B : Base S T) {k : GA D S} (hk : k ∈ GfC S) : B.act k = 1 := by
  have e : realGL B.F.θ S k = 1 := by
    funext τ
    change (Formalism.UG.bc (B.F.θ τ)) (infHom S k) = 1
    rw [show infHom S k = 1 from hk, map_one]
  rw [Base.act, MonoidHom.comp_apply, e, map_one]

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}

theorem thetaVector_laws (hC : GlobalTheory.Hk3.Core R F) (t : T0) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) ∧
      (∀ ρ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ ρ (cplxO 1 (cart (R.MW i (sg0 D A)) ρ)) (R.vP i t)) ∧
      Function.Injective (R.ptP i t) := by
  have hP := hC.thP
  have hM := hC.models
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have h := hP.pt_theta i t 1
    have e : R.ptP i t 1 = R.vP i t := by
      unfold RealDat.ptP pureTensorO pureTensorL
      rw [show (1 : PolF D (Wc D i).rank (Vc D i).rank) = MvPolynomial.basisMonomials _ ℂ 0 from rfl,
        Module.Basis.constr_basis]
      simp [opPow]
    rwa [e] at h
  have hv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hP.vP i t) hf
  have hne : R.vP i t ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i))
      ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hP.vP i t)
  exact ⟨hf, hv, GlobalTheory.FockIndep.pureTensorO_injective D R.ψ R.θ _ _ _ (R.MW i (sg0 D A)) (R.BV i) _
    (hP.ωP i t).std hM.inf (fun τ => GlobalTheory.OneMapRef.VecP.isCartanInv_one_of_onb (hM.BV i τ)) (hM.BV i) hf hne hv⟩

theorem act_ioP_inf (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good) (h : BaseOf R i B)
    {ψ : Twist D Circle} (hψ : ψ.Good) {t : T0} (ht : IsTupOf R B ψ t) :
    ∀ u ∈ GinfC (Vc D i), ∀ x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w) := by
  intro u hu x w
  obtain ⟨hf, hv, hinj⟩ := thetaVector_laws (i := i) hC t
  have hω := h.isWeil hC.thP.ωP ht
  have hpt : ∀ P, R.ptP i t P = B.F.fock (R.vP i t) P := fun P => by rw [h.fock_eq]; rfl
  have hf' : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (R.vP i t) := by rw [h.ψ]; exact hf
  have hv' : ∀ τ, IsFockVacAt (heisO B.F.ψ (Vc D i) (Wc D i)) B.F.θ τ (cplxO 1 (B.F.sT τ)) (R.vP i t) := by
    rw [h.ψ, h.θ, h.sT]; exact hv
  apply hinj
  rw [hpt, hpt, ← om_fock_of_vac hB hψ hω hf' hv' hu, ← hpt, ← hpt]
  exact (hC.thP.ioP i t).1 u hu x w

theorem act_ioP (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good) (h : BaseOf R i B)
    {ψ : Twist D Circle} (hψ : ψ.Good) {t : T0} (ht : IsTupOf R B ψ t) :
    (∀ u ∈ GinfC (Vc D i), ∀ x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w)) ∧
      ∀ (u : GA D (Vc D i)) x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w) := by
  refine ⟨act_ioP_inf hC hB h hψ ht, fun u x w => ?_⟩
  have e := GlobalTheory.AutMult.toInf_mul_toFin u
  set a := GlobalTheory.AutMult.toInf (Vc D i) u
  set k := GlobalTheory.AutMult.toFin (Vc D i) u
  rw [← e, map_mul, map_mul, act_of_mem_GfC B k.2, (hC.models.cV i).1 _ k.2, mul_one, mul_one]
  exact act_ioP_inf hC hB h hψ ht _ a.2 x w

end GlobalTheory.CoefActIo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AveragedSeriesFullRankOfComplexSpanGoodStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.averaged_series_full_rank_of_complex_span_good : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), Comparison₂ hρ rd → (∀ i j b, Faithful (rd i j b)) → ∀ (E : IntegralHeckeForms.XD D) (i : D.ntw.Tw), (∀ j b, RatBase (rd i j b)) → (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b) → SpanGood rd i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  first | exact @GlobalTheory.RankDescent.fullRk_of_spanGood | exact GlobalTheory.RankDescent.fullRk_of_spanGood | (intros; apply GlobalTheory.RankDescent.fullRk_of_spanGood <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseDataTypeCharacterEqLocalComponentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_data_type_character_eq_local_component : ∀ (D : D7) (S T : HSp D) (B : GlobalTheory.ExportSeries.Base S T), B.Good → ∀ χ : HChar D.host.E, ChrEq B.mu0 χ → ∀ PP ∈ B.G.Pg, ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0) (z : (kP PP)ˣ), (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((B.G.muC PP z : ℂˣ) : ℂ) = ((χ.locK PP (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TypeCharUnits.muC_eq_locK | exact GlobalTheory.TypeCharUnits.muC_eq_locK | (intros; apply GlobalTheory.TypeCharUnits.muC_eq_locK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormValuesBoundedOnHolomorphicArc
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ArcBdd

theorem norm_prod_pow_le {ι : Type} [Fintype ι] (f : ι → ℂ) (e : ι → ℕ) (B : ℝ) (hf : ∀ i, ‖f i‖ ≤ B) :
    ‖∏ i, f i ^ e i‖ ≤ B ^ (∑ i, e i) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hf i) _

theorem pnorm_unitFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (hx : GlobalTheory.FrameNorm.IsUnitFr X x) :
    X.pnorm la P x = ‖P x‖ := by
  unfold Data.pnorm
  have h1 : ∀ τ (i : Fin r), ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ = 1 := by
    intro τ i
    rw [norm_div, hx τ i.succ, hx τ i.castSucc, div_one]
  simp only [h1, Real.one_rpow, Finset.prod_const_one, mul_one]

theorem holSub_bdd {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : (k : Comp) → Wt (X k).Ψ r) (P : Formalism.L2.PjFree.FDSec X)
    (hP : P ∈ Formalism.L2.PjFree.holSub X la) (k : Comp) :
    ∃ C : ℝ, ∀ x ∈ (X k).dom, (X k).pnorm (la k) (P k) x ≤ C := by
  unfold Formalism.L2.PjFree.holSub at hP
  induction hP using Submodule.span_induction with
  | mem P hP => exact (hP k).1.2
  | zero => exact ⟨0, fun x _ => by
      have := Formalism.L2.Pj.pnorm_zero (X k) (la k) x
      simpa using this.le⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨C1, h1⟩ := hP
    obtain ⟨C2, h2⟩ := hQ
    exact ⟨C1 + C2, fun x hx => (Formalism.L2.Pj.pnorm_add_le (X k) (la k) (P k) (Q k) x).trans (add_le_add (h1 x hx) (h2 x hx))⟩
  | smul s P _ hP =>
    obtain ⟨C1, h1⟩ := hP
    exact ⟨‖s‖ * C1, fun x hx => by
      have := Formalism.L2.Pj.pnorm_smul (X k) (la k) s (P k) x
      simp only [Pi.smul_apply] at this ⊢
      rw [this]
      exact mul_le_mul_of_nonneg_left (h1 x hx) (norm_nonneg _)⟩

theorem cusp_bounded_at_unitFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Formalism.L2.PjFree.GoodEmb c σ → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ M : ℝ, ∀ (k : (U σ).Comp) (x : ((U σ).X k).dom), GlobalTheory.FrameNorm.IsUnitFr ((U σ).X k) x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x))‖ ≤ M := by
  intro E _ _ _ H Dw l Xo c r U σ a' n F hG hF
  haveI := (U σ).fin
  have hF' : Formalism.L2.PjFree.rdU (U σ) F ∈ Formalism.L2.PjFree.holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a' n) := by
    unfold Formalism.L2.PjFree.cusp at hF
    rw [Submodule.mem_inf, Submodule.mem_iInf] at hF
    have := hF.2 σ
    rw [Submodule.mem_iInf] at this
    exact Submodule.mem_comap.mp (this hG)
  choose C hC using holSub_bdd (U σ).X (Formalism.L2.PjFree.laU (U σ) a' n) _ hF'
  refine ⟨∑ k, max (C k) 0, fun k x hx => ?_⟩
  have h1 := hC k x.1 x.2
  rw [pnorm_unitFr _ _ _ _ hx] at h1
  have h2 : Formalism.L2.PjFree.rdU (U σ) F k x.1 = Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x)) := by
    simp [Formalism.L2.PjFree.rdU, x.2]
  rw [← h2]
  refine h1.trans ((le_max_left (C k) 0).trans ?_)
  exact Finset.single_le_sum (f := fun k => max (C k) 0) (fun k _ => le_max_right _ _) (Finset.mem_univ k)

theorem cusp_values_bounded_on_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (Uw : UnfWit (U σ)) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), (∀ σ', Formalism.L2.PjFree.GoodEmb c σ' → Formalism.L2.PjFree.IsUnf (U σ')) → Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Dom a' n → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ T C : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ‖Formalism.L2.PjFree.toC (evR Xo c F yw)‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c r U σ Uw _ _ O _ β Y a χ W Ha th Θ z hU hG hz a' n F hD hF
  obtain ⟨T1, B1, h1⟩ := GlobalTheory.T.norm_diag_tangent_unitFrame_holomorphicArc_le E H Dw l Xo c r σ (U σ) Uw O β Y a χ W Ha th Θ z hG (hU σ hG) hz
  obtain ⟨T2, B2, h2⟩ := GlobalTheory.T.arc_generator_ratio_bounded_unit_frame E H Dw l Xo c r σ (U σ) Uw O β Y a χ W Ha th Θ z hG (hU σ hG) hz
  obtain ⟨M, hM⟩ := cusp_bounded_at_unitFr E H Dw l Xo c r U σ a' n F hG hF
  have hev := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  set B := max 1 (max B1 B2)
  refine ⟨max T1 T2, max M 0 * B ^ (∑ i, ex Dw a' n i), ?_⟩
  intro w hw yw hyw
  obtain ⟨k, x, t, hux, hb⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hG (hU σ hG)).2 yw
  have hsc := ((GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a' n F (Formalism.L2.PjFree.cusp_le_sec Xo c U a' n hF) (CAt σ)).2 inferInstance).1 t _ _ hb
  have ht : ∀ i, ‖Formalism.L2.PjFree.toC (t i : CAt σ)‖ ≤ B := by
    intro i
    rcases i with _ | j
    · exact (h2 w (lt_of_le_of_lt (le_max_right _ _) hw) yw hyw k x t hux hb).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (h1 w (lt_of_le_of_lt (le_max_left _ _) hw) yw hyw k x t hux hb j).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hw' : ‖Formalism.L2.PjFree.toC (wchar (ex Dw a' n) t)‖ ≤ B ^ (∑ i, ex Dw a' n i) :=
    norm_prod_pow_le (fun i => Formalism.L2.PjFree.toC (t i : CAt σ)) (ex Dw a' n) B ht
  rw [hsc]
  change ‖(Formalism.L2.PjFree.toC (wchar (ex Dw a' n) t) * Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x)) : ℂ)‖ ≤ _
  rw [norm_mul, mul_comm]
  exact mul_le_mul ((hM k x hux).trans (le_max_left _ _)) hw' (norm_nonneg _) (le_max_right _ _)

end GlobalTheory.ArcBdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryFundamentalDomainVolumePosFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryFundamentalDomain_volume_pos_finite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), 0 < R.νV i t (R.fdV i t) ∧ R.νV i t (R.fdV i t) < ⊤ := by
  first | exact @GlobalTheory.DefVol.fdV_measure_pos_lt_top | exact GlobalTheory.DefVol.fdV_measure_pos_lt_top | (intros; apply GlobalTheory.DefVol.fdV_measure_pos_lt_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroInertiaOfLanglandsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_zero_inertia_of_langlands : GlobalTheory.Published.DepthZeroTypeInertia → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.Published.DepthZeroInertia := by
  first | exact @GlobalTheory.DepthZeroBridge.depthZeroInertia_of_depthZeroTypeInertia | exact GlobalTheory.DepthZeroBridge.depthZeroInertia_of_depthZeroTypeInertia | (intros; apply GlobalTheory.DepthZeroBridge.depthZeroInertia_of_depthZeroTypeInertia <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAveragedSeriesOfClassSumsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_averaged_series_of_class_sums : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.admT4 D.nexp E → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∃ S, BasisOf D.nexp i j b (SgJ D.nexp E i j b) S := by
  first | exact @GlobalTheory.TwInputs.exists_basisOf_of_classSum | exact GlobalTheory.TwInputs.exists_basisOf_of_classSum | (intros; apply GlobalTheory.TwInputs.exists_basisOf_of_classSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentMapNonzeroOfSmallFieldFormStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.NX
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_map_nonzero_of_small_field_form : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), (S.A j).IsKsForm → ∀ (i : D.ntw.Tw) (b : Bool) (x : S.WL j), x ≠ 0 →
    ∃ Φ : S.WL j →+ Fm S i j b, Φ x ≠ 0 ∧
      (∀ (c : ↥D.LL0) (w : S.WL j), Φ (((c : ↥D.LL0) : D.what₂.LL) • w) = readLL0 S i b c • Φ w) ∧
      ∀ (T : Module.End D.what₂.LL (S.WL j)) (hT : ∀ w ∈ (S.A j).WK, T w ∈ (S.A j).WK) (w : S.WL j),
        Φ (T w) = Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)
          ((T.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hT) (Φ w) := by
  first | exact @GlobalTheory.exists_desc_of_isKsForm | exact GlobalTheory.exists_desc_of_isKsForm | (intros; apply GlobalTheory.exists_desc_of_isKsForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbeddingProdIrrSupport
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel GlobalTheory.BCen

namespace GlobalTheory.BCen.SuppEmbed

theorem exists_embedding_prodIrr_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∃ (t : ℕ) (x : Fin t → IrrGL k) (hx : ∑ a, (x a).1 = n) (φ : π.IntertwiningMap (prodIrr x hx)),
      (∀ a, (x a).IsCusp) ∧ Function.Injective φ ∧ ∀ s, HasSupport π s ↔ Finset.univ.val.map x = s := by
  intro k _ _ _ _ n V _ _ π hs hi
  obtain ⟨t, x, hx, hc, φ, hφ⟩ :=
    GlobalTheory.CompanionTheory.SubEmb.subEmbedding_of_stage GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k n V π hs hi
  have hsupp : HasSupport π (Finset.univ.val.map x) :=
    hasSupport_of_isSubquotient hi hc (.of_injective φ hφ)
  refine ⟨t, x, hx, φ, hc, hφ, fun s => ⟨fun h => ?_, fun h => h ▸ hsupp⟩⟩
  exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.bernsteinZelevinskyFiniteness_holds hsupp h

end GlobalTheory.BCen.SuppEmbed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteUnramifiedApproximationPadicStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_unramified_approximation_padic : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (n : ℕ) (y : Fin n → ℂ_[p]), (∀ s, y s ∈ kurC φ) → ∀ ε : ℝ, 0 < ε → ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra F F') (φ' : F' →+* ℂ_[p]), (∀ a, φ' (algebraMap F F' a) = φ a) ∧ (∀ a : F, vLa (placeAt φ') (algebraMap F F' a) = vLa (placeAt φ) a) ∧ ∃ a' : Fin n → F', ∀ s, ‖y s - φ' (a' s)‖ < ε := by
  first | exact @GlobalTheory.KurApprox.kur_approx | exact GlobalTheory.KurApprox.kur_approx | (intros; apply GlobalTheory.KurApprox.kur_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRightInverseCentralProjectorUnitElementStatement
section
open GlobalTheory.MeetsGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_right_inverse_centralProjectorUnitElement : ∀ {G : Type} [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (ψ : U →* ℂˣ) (e : MonoidAlgebra ℂ G), e * e = e → (∀ a, e * a = a * e) → (∀ χ : G → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, e.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0) → ∃ v : MonoidAlgebra ℂ G, uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) e * v = 1 := by
  first | exact @GlobalTheory.MeetsUnit.exists_rightInv_uElt | exact GlobalTheory.MeetsUnit.exists_rightInv_uElt | (intros; apply GlobalTheory.MeetsUnit.exists_rightInv_uElt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitSupportedRepFiniteUnitaryClassStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_supported_rep_finite_unitary_class : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ h ∈ GfC (Vc D j), ∃ (γ : GQ (Vc D j)) (s : Finset (Pl D.host.E)) (h' : GA D (Vc D j)) (k : (ρ.B i j b).levJ (ρ.tw i b 0 ∅ 1)), SplitSet s ∧ (∀ v ∈ s, ((ρ.bad i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) ∧ h' ∈ GfC (Vc D j) ∧ SuppAt (idem s) (Vc D j) h' ∧ finPt (Vc D j) h = Bridge.ratF (Vc D j) γ * finPt (Vc D j) h' * (k : Bridge.Gf (Vc D j)) := by
  first | exact @GlobalTheory.RankReps.exists_rep_split_levJ | exact GlobalTheory.RankReps.exists_rep_split_levJ | (intros; apply GlobalTheory.RankReps.exists_rep_split_levJ <;> assumption)
end

