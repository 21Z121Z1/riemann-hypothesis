import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0985
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0982
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0977
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0981
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0947
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodRationalEigenformHittingCarriedPart
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0962
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0970
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0973
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointConcreteThetaInjectiveReferenceTuple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem.R3

namespace GlobalTheory.AdjInjLevel

set_option maxHeartbeats 2000000 in

theorem adjoint_eW_inj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → ∀ (i : Fin D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y) = 0 → y = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i σ y _ h0
  have hnP : 0 < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
  have hinj : Function.Injective (Y.mj.eW i) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    have h1 : RealDat.nP F.lv2 false * ‖d‖ ^ 2 = 0 := by rw [← Y.mj.eW_norm i d, hd]; simp
    have h2 : ‖d‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hnP.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
  have hWS : Y.mj.eW i y ∈ R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [hH.aux.levelW false i (sg0 D A3.A), ← Y.mj.eW_range i]
    exact LinearMap.mem_range_self _ _
  have hle : R.toRealDat.WS F.lv2 false i (sg0 D A3.A) ≤
      Submodule.comap (Tw.mkL (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H)
        (LinearMap.range ((R.toCx3 F).w0C false i)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact GlobalTheory.TwParts.mk_bC_mem_range R F i k
  have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i y) ∈ LinearMap.range ((R.toCx3 F).w0C false i) := hle hWS
  rw [← (hH.prim.sumW i).2] at h1
  have hsum : Y.mj.eW i y ∈ ⨆ p, R.Wp3 i p := by
    have key : ∀ w : (R.toCx3 F).W i, w ∈ (⨆ p, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)) →
        Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) w ∈ ⨆ p, R.Wp3 i p := by
      intro w hw
      refine Submodule.iSup_induction (motive := fun w => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) w ∈ ⨆ p, R.Wp3 i p) _ hw
        (fun p w hw => Submodule.mem_iSup_of_mem p hw.1) (Submodule.zero_mem _) ?_
      intro a b ha hb
      rw [Tw.out_add (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) a b]
      exact Submodule.add_mem _ ha hb
    exact key _ h1
  have hz := GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.thG i A3.A.μ0) (R.Wp3 i)
    (fun p => ((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ))
    (fun p => Complex.ofReal_ne_zero.2 (hH.prim.posScal.2 i A3.A.μ0 p A3.A.v0).ne')
    (fun p x hx => hH.prim.thmA i A3.A.μ0 p x hx) hsum h0
  exact hinj (hz.trans (map_zero _).symm)

end GlobalTheory.AdjInjLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointFrameMatrix_integral_of_conjugate_half : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ u : WO S T, u ∈ latO S T ΛS ΛT (fun _ => True) → IsHalf (cA D e) u → IsIntM (frMapAdj S T βS βT u) := by
  first | exact @GlobalTheory.HalfAdjInt.frMapAdj_int_of_half | exact GlobalTheory.HalfAdjInt.frMapAdj_int_of_half | (intros; apply GlobalTheory.HalfAdjInt.frMapAdj_int_of_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointThetaKillsReferenceTuple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev

noncomputable section
open scoped TensorProduct InnerProductSpace
open Formalism.L2.Rows GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.ThetaRead3

set_option maxHeartbeats 4000000 in

theorem thetaP_read_plain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) x, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i t x
  have hE : R.toRealDat.IsThP := RealDat.thP_of_weak hP.char.base.thP hH.aux.ex
  have hM := hP.char.base.models
  have hμ : Used0 D (Y.tup t) := by
    rcases hP.char.tup.mu_used t with h | ⟨w, hw⟩
    · left
      rw [h, Y.tup0]
    · right
      refine ⟨D.plEq.symm w, ?_⟩
      rw [Y.muAt, Equiv.apply_symm_apply, hw]
  set xM := D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x) with hxM
  set zt := R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x) with hzt
  obtain ⟨w, hwM, hwK, hwW⟩ := GlobalTheory.T.thetaAdjoint_at_lift_eq_lowestKType_restriction R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hP.char.base.lev
    hP.char.base.grp hM hE R.hv0 Y.IL (Y.tup t) hμ i xM
  have hth := Y.tied.lift.theta (Y.tup t) hμ i xM w
    (GlobalTheory.ThetaPRead.isThetaP_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hE.thF (Y.tup t) i) hwM hwK hwW
  set u := Y.tupT (Y.tup t) with hu
  set a := Y.IL.jMt (Y.tup t) hμ i xM with ha
  set z' : (R.HV i u).H := (LinearEquiv.ofInjective (R.extV i u) (Y.hinj i u)).symm
    (Submodule.inclusion inf_le_left a) with hz'
  have hz'1 : R.extV i u z' = R.extV i t zt := by
    rw [hz', ofInjective_symm_eq]
    exact Y.mtRead i t hμ x
  have hzz : R.thF i u z' = R.thF i t zt := thF_congr R.toRealDat Y.hinj i t u (Y.tupT_tup t) zt z' hz'1
  let w' : (⨂[ℂ] τ, (R.MW i (sg0 D A3.A)).sm τ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) := w
  let U : MMap (R.MW i (sg0 D A3.A)) := PiTensorProduct.lift.symm w'
  have hU : U ∈ R.Wall i (sg0 D A3.A) :=
    GlobalTheory.HeckeParts.mult_le_triv _ ((Mult.mem_multT _ _ _ _ w').1 hwM)
  have hlow : ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A3.A)) ρ, U (fun ρ => v ρ) = R.thF i u z' (fun ρ => v ρ) := by
    intro v
    have e := LinearMap.congr_fun hwK (PiTensorProduct.tprod ℂ v)
    have e2 : w' (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) =
        PiTensorProduct.lift (R.thF i u z')
          (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) := e
    rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod] at e2
    exact e2
  have hw0 : U - R.thF i t zt = 0 :=
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A3.A)) R.θ hM.inf
      (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ _ (Submodule.sub_mem _ hU (hE.thF_mem i t zt)) (fun v => by
        show U (fun ρ => v ρ) - R.thF i t zt (fun ρ => v ρ) = 0
        rw [hlow v, hzz, sub_self])
  have hUw : PiTensorProduct.lift U = w' := LinearEquiv.apply_symm_apply _ w'
  have h1 := (Y.mjRead i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) xM)).symm.trans hth
  change PiTensorProduct.lift _ = R.eWf i (sg0 D A3.A) ∘ₗ w' at h1
  rw [← hUw, sub_eq_zero.1 hw0, ← lift_postOn, ← hE.thG i t zt] at h1
  exact (hM.HW i (sg0 D A3.A)).1 (PiTensorProduct.lift.injective h1)

end GlobalTheory.Mem.ThetaRead3

namespace GlobalTheory.Mem.AdjLevel

set_option maxHeartbeats 4000000 in

theorem adjoint_eW_eq_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → ∀ (i : Fin D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y = 0 → LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y) = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i σ y _hy hT
  have hread := GlobalTheory.Mem.ThetaRead3.thetaP_read_plain D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH i A3.A.μ0
  have hT' : D.what₂.thetaT (Y.tup A3.A.μ0) ((i : ℕ) + 1) y = 0 := by rw [Y.tup0]; exact hT
  have hw : (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) ∈
      R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := by
    have h0 : Y.mj.eW i y ∈ LinearMap.range (Y.mj.eW i) := ⟨y, rfl⟩
    rw [Y.mj.eW_range] at h0
    exact h0
  have ha := GlobalTheory.CarriedPart.adjoint_mem_span R F hH.ok hP.char hH.prim.unif hH.prim.gUnit hH.prim.gEquiv hH.prim.levW i _ hw
  have horth : ∀ f ∈ BlockGood.goodR (A3.A.fam.L i A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0),
      ⟪Y.mj.eW i y, R.thG i A3.A.μ0 (R.jV i A3.A.μ0 f)⟫_ℂ = 0 := by
    intro f hf
    rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq] at hf
    have hfl : f ∈ lvlForms (A3.A.fam.L i A3.A.μ0).S (A3.A.fam.L i A3.A.μ0).r (A3.A.fam.lvlA F.P0 F.ψ0).P
        (A3.A.fam.lvlA F.P0 F.ψ0).ψ := fun h =>
      Formalism.IndefR.CxPass.LevelOperators.opF_goodAt_type _ _ hH.ok.ok2.irr _ _ h f hf
    rw [← GlobalTheory.Mem.LiftForms.range_lvlForm] at hfl
    obtain ⟨x, rfl⟩ := hfl
    have hx : GlobalTheory.Mem.LiftForms.lvlForm (A3.A.fam.L i A3.A.μ0).S (A3.A.fam.L i A3.A.μ0).r (A3.A.fam.lvlA F.P0 F.ψ0).P
        (A3.A.fam.lvlA F.P0 F.ψ0).ψ x = liftForm A3.A F.P0 F.ψ0 i A3.A.μ0 x := rfl
    rw [hx, ← hread x, GlobalTheory.Mem.LiftForms.inner_of_norm_sq (Y.mj.eW i) (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i),
      ← LinearMap.adjoint_inner_left]
    show _ * ⟪D.what₂.thetaT (Y.tup A3.A.μ0) ((i : ℕ) + 1) y, _⟫_ℂ = 0
    rw [hT', inner_zero_left, mul_zero]
  have hall : ∀ v ∈ Submodule.span ℂ (R.jV i A3.A.μ0 '' (BlockGood.goodR (A3.A.fam.L i A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) :
      Set (A3.A.fam.L i A3.A.μ0).S.Forms)), ⟪Y.mj.eW i y, R.thG i A3.A.μ0 v⟫_ℂ = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨f, hf, rfl⟩ := hz
      exact horth f hf
    | zero => rw [map_zero, inner_zero_right]
    | add a b _ _ ha hb => rw [map_add, inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, inner_smul_right, ha, mul_zero]
  have h0 : ⟪LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y), LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y)⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left]
    exact hall _ ha
  exact inner_self_eq_zero.1 h0

end GlobalTheory.Mem.AdjLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipVacuumEqMultipleOfTranslateMean
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

set_option maxHeartbeats 1600000 in
open MeasureTheory GlobalTheory.VacUnique GlobalTheory.FockCompare in

theorem eq_smul_vacuum {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f f' : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) (hth : IsThetaFunO ψ S T f')
    (hlat' : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) f')
    (hfock : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') : ∃ a : ℂ, f' = a • f := by
  classical
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hΛS hΛT
  have hden := GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT hΛS.1 hΛT.1
  have hlat := hf.2.lat
  have hinf := fun u => latO_inf (u := u) S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at h1 h2 h3 hden hlat hlat' hinf
  choose ε hε1 hε2 using h3 f hlat
  have det : ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      IsLatVac (heisO ψ S T) Λ g → IsLatVac (heisO ψ S T) Λ g' →
      (∀ z, g' (iotaW σ T S z) = c * g (iotaW σ T S z)) → g' = c • g := by
    intro g g' c hg hg' hl hl' hz
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := exists_decomp h h2 w
    rw [Pi.smul_apply, smul_eq_mul, hg.quasi, hg'.quasi, apply_real_add h hψ (hinf u hu) (hε2 u hu g hl),
      apply_real_add h hψ (hinf u hu) (hε2 u hu g' hl'), hz]
    ring
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 f = 1 := hn p hp
  have hne : (fun z : RW T S => f (iotaW σ T S z)) ≠ 0 := by
    intro h0
    have e := det f f 0 hf.2.theta hf.2.theta hlat hlat fun z => by rw [zero_mul]; exact congrFun h0 z
    rw [e] at n1
    simp [nrm2] at n1
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := span_piW_ratW_eq_top D θ σ h T S
    simpa only [piW_ratW hθ] using this
  have a1 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f hf.2.theta hf.2.fock
  have a2 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f' hth hfock
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε _ hv else 1
  have hc : ∀ v, ‖c v‖ = 1 := fun v => by
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψ.1.2.1]
      rcases hε1 _ hv with e | e <;> rw [e] <;> simp
    · exact norm_one
  have law : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) Λ g →
      ∀ v ∈ Λ.comap (finRat S T), ∀ z, g (iotaW σ T S (z + infRat S T v)) =
        c v * Complex.exp (-(Real.pi * Complex.I) * (omO S T z (infRat S T v) : ℂ)) * g (iotaW σ T S z) := by
    intro g hg hl v hv z
    have hv' : finRat S T (-v) ∈ Λ := (Λ.comap (finRat S T)).neg_mem hv
    rw [apply_add_infRat h hψ hg v (hε2 _ hv' g hl) z, ← j2]
    simp only [c, dif_pos hv']
  have hli := GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) j1 j2 j3 j4 (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (infRat S T) (infRat_injective S T) hsp (Λ.comap (finRat S T))
    (fun x => by
      obtain ⟨N, hN, hx⟩ := hden x
      exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, AddMonoidHom.map_nsmul]⟩)
    (GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf h1 h2 hden) c hc
    ![fun z => f (iotaW σ T S z), fun z => f' (iotaW σ T S z)]
    (fun k => by fin_cases k; exacts [a1.1, a2.1]) (fun k => by fin_cases k; exacts [a1.2, a2.2])
    (fun k => by fin_cases k; exacts [law f hf.2.theta hlat, law f' hth hlat'])
  rw [LinearIndependent.pair_iff' hne] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  exact ⟨a, det f f' a hf.2.theta hth hlat hlat' fun z => (congrFun ha z).symm⟩

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem moved_vacuum_eq_mean : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → z ∈ GfC V → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → ∃ (lam : ℂ) (Y : Finset (WO V W)), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) ∧ (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') ∧ Y.card = flipIdx V W T m ∧ om (z⁻¹, 1) f₀ = lam • ∑ y ∈ Y, heisO ψ V W y f₀ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT z hT hm hcop hmT hz hmt
  obtain ⟨Y, hY1, hY2, hY3, hYc⟩ := GlobalTheory.T.exists_levelPoint_reps_conjugate_half_mod_lattice D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT
  set G := ∑ y ∈ Y, heisO ψ V W y f₀ with hG
  obtain ⟨hGth, hGf⟩ := GlobalTheory.T.conjugateHalf_vacuum_translate_sum_isThetaFockVacuum D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT Y fun y hy => (hY1 y hy).1
  obtain ⟨hfix2, hfixh⟩ := GlobalTheory.T.vacuum_translate_sum_fixed_by_flipped_lattice D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT Y hY1 hY2 hY3
  have hne := GlobalTheory.T.vacuum_translate_sum_conjugateHalf_ne_zero D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT Y hY1 hY2 hY3
  have hW := hP.1.weil

  have hmove : ∀ u : WO V W, actO V W z 1 (flipElt eT m • u) = u := by
    intro u
    have e := GlobalTheory.AdelicLatMove.actO_actO_inv V W z 1 u
    have e2 : actO V W z⁻¹ 1⁻¹ u = flipElt eT m • u := by
      simp only [actO, inv_inv, hmt]
      have h1 : Formalism.L2.Theta.mt W (1 : GA D W)⁻¹ = 1 := by
        rw [inv_one]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
      rw [h1, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    rw [← e2]; exact e
  set H := om (z, 1) G with hH
  have hHth : IsThetaFunO ψ V W H := hW.om_pres _ _ hGth
  have hHh : ∀ u, heisO ψ V W u H = om (z, 1) (heisO ψ V W (flipElt eT m • u) G) := by
    intro u
    rw [hW.om_heis z 1 _ G hGth, hmove]
  have hzf : z ∈ GfC V := hz
  have hHf : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ)) H := by
    intro τ z'
    have c1 : compAt θ τ (Formalism.L2.Theta.mt W (1 : GA D W)) = 1 :=
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ W (one_mem _) τ
    have c2 : compAt θ τ (Formalism.L2.Theta.mt V z⁻¹) = 1 :=
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ V (inv_mem hzf) τ
    have e1 := GlobalTheory.OrientedHeis.om_dRho hW hP.1.inf z 1 τ z' hGth
    have e2 := GlobalTheory.OrientedHeis.om_dRho hW hP.1.inf z 1 τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ) z') hGth
    rw [c1, c2, Matrix.one_mul, Matrix.mul_one] at e1 e2
    have h0 := hGf τ z'
    unfold annih at h0 ⊢
    rw [hH, ← e1, ← e2, ← map_smul, ← map_add, h0, map_zero]
  have hHl : IsLatVac (heisO ψ V W) (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) H := by
    refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
    · rw [hHh, hfix2 u hu]
    · rw [hHh, hfixh e he u hu hh]
  obtain ⟨c, hc⟩ := eq_smul_vacuum hP.2.2.2.2.2.2.2.2.1 hP.1.inf (fun τ => GlobalTheory.SmoothVac.isCartanInv_one V hP.1.std τ)
    hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2 hHth hHl hHf
  have hback : om (z⁻¹, 1) H = G := by
    rw [hH, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, one_mul, ← Prod.one_eq_mk, map_one,
      Module.End.one_apply]
  have hGc : G = c • om (z⁻¹, 1) f₀ := by rw [← hback, hc, map_smul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by rw [← hG, hGc, zero_smul])
  refine ⟨c⁻¹, Y, hY1, hY2, hYc, ?_⟩
  rw [← hG, hGc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
end GlobalTheory.LevelSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacteristicFunctionIntegralApply
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefTheta

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame GlobalTheory.ThetaTri
open scoped TensorProduct

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem reference_tuple_used (D : D7) : Used0 D D.what₂.mu0 := Or.inl rfl

abbrev t0 (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : T := Y.tupT D.what₂.mu0

def repY (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : D.what₂.FT → NG.FinTyp D.host.E D.R.r :=
  fun σ => rowRepR R.θ (Y.eFT σ)

def IsCanonR (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (i : Fin D.R.m) {j : ℕ} (hj : i.1 + 1 = j) (X : GlobalTheory.NPin.RowMod D rep j) : Prop :=
  ∃ (e : X.A →ₗ[ℂ] Mult.MMap (R.MW i (sg0 D A3.A))) (c : ℝ), Function.Injective e ∧ 0 < c ∧
    X.C.map e = Minf R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) ∧
    (∀ h x, e (X.ρ h x) = actM (Y.PW i) (R.MW i (sg0 D A3.A)) h (e x)) ∧
    (∀ x ∈ X.C, ∀ y ∈ X.C, X.B x y = (c : ℂ) * Mult.ipM (R.MW i (sg0 D A3.A)) (R.νW i) (R.fdW i) (e x) (e y)) ∧
    ∀ y : D.what₂.Mj (i.1 + 1), PiTensorProduct.lift (e (X.φ (hj ▸ y))) = (Y.IL.jMj i y).1

variable {Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

def eC {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) : X.A →ₗ[ℂ] Mult.MMap (R.MW i (sg0 D A3.A)) :=
  Classical.choose hc

def cC {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) : ℝ :=
  Classical.choose (Classical.choose_spec hc)

def yv {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    ↥X.C →ₗ[ℂ] (Formalism.L2.Theta.GA D (Wc D i) → ℂ) :=
  LinearMap.applyₗ (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype)
      (kUnit (R.MW i (sg0 D A3.A)))) ∘ₗ
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ eC hc ∘ₗ X.C.subtype

variable {M : MtFam D}

def fV (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) :
    ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ) →ₗ[ℂ]
      (Formalism.L2.Theta.GA D (Vc D i) → (R.cV i).W) :=
  (R.cV i).ext ∘ₗ
    { toFun := fun F k => Ad.eW D.what₂.mu0 (reference_tuple_used D) i
        ((F : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))
      map_add' := fun F F' => by funext k; simp
      map_smul' := fun c F => by funext k; simp }

def omStd (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (t : T) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
  (R.ωP i t).comp ((Ad.PV i).ψ.prodMap (Y.PW i).ψ)

def Om (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    Submodule ℂ ((R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) :=
  OmSub (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) R.ψ (omStd Ad i (t0 Y))

def om (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ ↥(Om Ad i hc) :=
  omSub (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) R.ψ (omStd Ad i (t0 Y))

def lamV (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) (φ : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ))
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) (y : ↥X.C) : ℂ :=
  GlobalTheory.ThetaTri.lamV (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) (cC hc : ℂ) φ Fm y

def lamL (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    ↥(Om Ad i hc) →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ :=
  lam (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) (cC hc : ℂ) R.ψ
    (omStd Ad i (t0 Y))

variable (Y) in

def phi0 (i : Fin D.R.m) : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A3.A))) (R.BV i)
    (onb (R.MW i (sg0 D A3.A))) (R.vP i (t0 Y)) ∘ₗ R.ioP i (kUnit (R.MW i (sg0 D A3.A)))

end GlobalTheory.RefTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlockVectorNotKilledStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_block_vector_not_killed : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), GlobalTheory.HeightCounting.Up.CenLoc D P.M → ∀ S : Reading P.T, IsTrue P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) ρ f, InSeries D k ρ f → PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ) → ∃ x, IsBlockVec (S i _ hw).mu ((S i _ hw).rep PI).π x ∧ NotKilled ((S i _ hw).rep PI).π (idemOf D k ρ) x := by
  first | exact @GlobalTheory.DzVecLoc.main | exact GlobalTheory.DzVecLoc.main | (intros; apply GlobalTheory.DzVecLoc.main <;> assumption)
end

