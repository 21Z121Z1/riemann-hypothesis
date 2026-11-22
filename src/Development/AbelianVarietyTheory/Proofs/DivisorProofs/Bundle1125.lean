import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftIsOpenImmersionRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowersLinearIndependentOverLocalTensorCenterStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powers_linearIndependent_over_localTensorCenter : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n → ∀ (v : AwayP p) (c : Fin G.n → Qv v ⊗[ℚ] G.F), ∑ i, iotaF G v (c i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = 0 → c = 0 := by
  first | (exact @GlobalTheory.OrbFinAf.pow_indep_tensor) | (exact GlobalTheory.OrbFinAf.pow_indep_tensor) | (intros; apply GlobalTheory.OrbFinAf.pow_indep_tensor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsEqTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.PrincipalRows

theorem theta_adjoint_mem {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (cv : CrdV A) (hKR : X.KFormR) (hJR : X.JIsoR cv) (hRT : Formalism.IndefR.Rat.RowTest X) (t : Bs.Tup) (S : Submodule ℂ X.EE)
    (hZ : ∀ z ∈ X.Z t, X.Θ t (X.jR t z) ∈ S) (e : X.EE) : X.Θ t (LinearMap.adjoint (X.Θ t) e) ∈ S := by
  obtain ⟨N, ψ, hψ, hr⟩ := hRT
  have hspan : Submodule.span ℂ ((X.jR t) '' (X.Z t : Set (A.FR t))) = LinearMap.range (LinearMap.adjoint (X.Θ t)) :=
    Formalism.IndefR.Rat.range_adjoint_rat Bs.v0.embedding (X.jR t) (cv.hR t) (CxData.bR t) (hKR t).1 (hKR t).2 (hJR t) (X.Θ t) ψ hψ
      (fun i x => hr t i x)
  have hsub : LinearMap.range (LinearMap.adjoint (X.Θ t)) ≤ S.comap (X.Θ t) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact hZ z hz
  exact hsub ⟨e, rfl⟩

end GlobalTheory.PrincipalRows

namespace GlobalTheory.PrincipalRows

theorem mem_range_toF_full {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (Xc : Finset (G → K)) (Z : Submodule K B.S.Forms) (z : B.S.Forms) (hz : z ∈ Z)
    (hg : z ∈ B.goodF Xc) : z ∈ LinearMap.range (B.toF ⟨Xc, ⊥, 1⟩ Z) := by
  rw [GlobalTheory.OneForm.range_toF]
  refine ⟨hz, ?_⟩
  obtain ⟨w, hw⟩ := hg
  refine ⟨w, ?_⟩
  rw [← hw, Formalism.L2.DIV.CSD.gaOp, GlobalTheory.OneForm.asAlg_eq_sum, LinearMap.sum_apply]
  rfl

theorem theta_base_forms_mem_principal_good_part {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type}
    {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
    {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} (hIB : X.zs.InBlock) :
    ∀ z ∈ X.Z A3.A.fam.μ0, X.Θ A3.A.fam.μ0 (X.jR A3.A.fam.μ0 z) ∈
      EEg3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) := by
  intro z hz
  have h1 : z ∈ (A3.A.fam.R A3.A.fam.μ0).ZHg A3.A.fam.X := hIB.1 A3.A.fam.μ0 hz
  obtain ⟨x, hx⟩ := mem_range_toF_full (A3.A.fam.R A3.A.fam.μ0) A3.A.fam.X (X.zs.Z A3.A.fam.μ0) z hz h1.2
  refine ⟨cpt A3.A.v0.embedding x, ?_⟩
  have h3 := GlobalTheory.OneForm.iC_cpt X (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0 x
  refine h3.trans ?_
  exact congrArg (fun y => X.Θ A3.A.fam.μ0 (X.jR A3.A.fam.μ0 y)) hx

end GlobalTheory.PrincipalRows

namespace GlobalTheory.PrincipalRows

set_option maxHeartbeats 1000000 in

theorem principal_level_rows_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (⨆ p, R.EEp3 p) = ⊤ → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) = ⊤ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC hTop hPos hB hRT hIB
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hC.base.models
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hC.base.models
  have hmem := theta_adjoint_mem (R.toCx3 F) F.cv hKR hJR hRT A3.A.fam.μ0
    (EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc))
    (theta_base_forms_mem_principal_good_part A3 (R.toCx3 F) hIB)

  have hpart : ∀ p, ∀ y ∈ R.EEp3 p, (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) := by
    intro p y hy
    have hc : (0 : ℝ) < R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p := by
      refine mul_pos hPos.1 (Finset.prod_pos fun j _ => ?_)
      unfold RealDat3.lamN
      split_ifs
      · exact hPos.2 _ _ _
      · exact one_pos
    have hne : ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hce : ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y ∈ R.EEp3 p :=
      (R.EEp3 p).smul_mem _ hy
    have key : R.Th A3.A.fam.μ0 (LinearMap.adjoint (R.Th A3.A.fam.μ0)
        (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y)) = y := by
      refine (hB A3.A.fam.μ0 p _ hce).trans ?_
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    have h3 := hmem (Tw.mk (twAt D.what₂.embLL A3.A.v0) (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y))
    have h4 : (R.toCx3 F).Θ A3.A.fam.μ0 (LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0)
        (Tw.mk (twAt D.what₂.embLL A3.A.v0) (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y))) = Tw.mk (twAt D.what₂.embLL A3.A.v0) y := by
      show Tw.map _ (R.Th A3.A.fam.μ0) (LinearMap.adjoint (Tw.map _ (R.Th A3.A.fam.μ0)) _) = _
      rw [Tw.adjoint_map]
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) key
    rw [h4] at h3
    exact h3
  rw [eq_top_iff]
  intro e0 _
  have hx : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) e0 ∈ ⨆ p, R.EEp3 p := by rw [hTop]; exact Submodule.mem_top
  have hall : ∀ y ∈ ⨆ p, R.EEp3 p, (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) := by
    intro y hy
    exact Submodule.iSup_induction R.EEp3 (motive := fun y => (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc)) hy hpart
      (Submodule.zero_mem _) (fun a b ha hb => Submodule.add_mem _ ha hb)
  exact hall _ hx

end GlobalTheory.PrincipalRows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLiftFormsEqGoodForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.WgLift

open Formalism.IndefR.CxPass.LevelOperators

set_option maxHeartbeats 1000000 in

theorem principal_lift_forms_eq_good_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (⨆ p, R.Wp3 i p) = LinearMap.range (eH R.toRealDat i)) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmA → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ i, principalFormsSubspace A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) i = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hW hpos hA hLT hB i
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak hch hex
  have hM := hc.models
  have hCore : Core R.toRealDat F.lv2 := ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩
  have hL := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hok.ok2.irr i
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hM
  have hJ : (R.toCx3 F).JIsoL F.cv := Formalism.IndefR.Links.RealDat3.jIsoL_of (F := F) hM
  have hθ : ∀ t (u : (R.toCx3 F).FLC i t), Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) =
      cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u) := by
    intro t u
    rfl

  have hsub : ∀ t, ∀ y ∈ LinearMap.range ((R.toCx3 F).θ' i t), y ∈ Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) := by
    rintro t _ ⟨u, rfl⟩
    change Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) ∈ LinearMap.range (eH R.toRealDat i)
    rw [hθ]
    exact ⟨cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u), by rw [map_smul, hL.2.2.2]⟩

  have hrng : ∀ t, LinearMap.range ((R.toCx3 F).θ' i t) ≤
      LinearMap.range ((R.toCx3 F).tC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t) := by
    intro t
    obtain ⟨N, ψ, hψ, hr⟩ := hLT i
    have hRZ := Formalism.IndefR.Rat.range_adjoint_rat A3.fam3.base3.v0.embedding ((R.toCx3 F).jL i t) (F.cv.hL i t)
      (Formalism.IndefR.Cx.CxData.bL (A := A3.fam3.amb3) i t)
      (hK i t).1 (hK i t).2 (hJ i t) ((R.toCx3 F).θ' i t) ψ hψ (fun k x => hr t k x)
    have hgood : (LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) ≤
        LinearMap.range (opF (A3.A.fam.L i t).r (idemOf A3.A.X)) := by
      intro z hz
      have h1 : z ∈ (A3.A.fam.L i t).goodF A3.A.X := (hB.2 i t hz).2
      have h2 : (A3.A.fam.L i t).goodF A3.A.X = LinearMap.range (opF (A3.A.fam.L i t).r (idemOf A3.A.X)) := by
        unfold BlockDat.goodF
        rw [Formalism.IndefR.CxPass.LevelOperators.goodAt_bot]
        rfl
      rwa [h2] at h1
    rintro _ ⟨v, rfl⟩
    obtain ⟨u, hu, k, hk, hak⟩ := (LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).exists_add_mem_mem_orthogonal v
    have hk0 : (R.toCx3 F).θ' i t k = 0 := by
      have h0 : ⟪LinearMap.adjoint ((R.toCx3 F).θ' i t) ((R.toCx3 F).θ' i t k), k⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hk _ ⟨_, rfl⟩
      rw [LinearMap.adjoint_inner_left] at h0
      exact inner_self_eq_zero.1 h0
    rw [hak, map_add, hk0, add_zero]
    have hZeq : (((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t)) ⊓
        LinearMap.range (opF (A3.A.fam.L i t).r (idemOf A3.A.X)) : Submodule _ _) =
        LinearMap.range ((A3.A.fam.L i t).toF (A3.A.fam.lvlA ⊥ 1) ((R.toCx3 F).Zl i t)) := by
      refine Eq.trans ?_ (Formalism.IndefR.CxPass.LevelOperators.range_toF (A3.A.fam.L i t) (A3.A.fam.lvlA ⊥ 1) _).symm
      rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq,
        show goodAt (A3.A.fam.lvlA ⊥ 1).X (A3.A.fam.lvlA ⊥ 1).P (A3.A.fam.lvlA ⊥ 1).ψ = idemOf A3.A.X from
          Formalism.IndefR.CxPass.LevelOperators.goodAt_bot _ _]
      rfl
    have hZ2 : (LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) =
        LinearMap.range ((A3.A.fam.L i t).toF (A3.A.fam.lvlA ⊥ 1) ((R.toCx3 F).Zl i t)) := (inf_eq_left.2 hgood).symm.trans hZeq
    rw [← hRZ, hZ2] at hu
    obtain ⟨c, hc⟩ : u ∈ LinearMap.range (lin ((R.toCx3 F).uL (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t)) := by
      refine (Submodule.span_le.2 ?_) hu
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨cpt A3.fam3.base3.v0.embedding x,
        ((R.toCx3 F).jL_toL (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t x).symm⟩
    exact ⟨c, by rw [(R.toCx3 F).tC_eq, hc]⟩

  have hsup : Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) ≤ LinearMap.range ((R.toCx3 F).θ' i A3.A.μ0) := by
    intro w hw
    have hw' : Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) w ∈ ⨆ p, R.Wp3 i p := by rw [hW i]; exact hw
    have hcc : starRingEnd ℂ (R.phs i) * R.phs i = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, (hch.phase i).1]; norm_num
    refine Submodule.iSup_induction (fun p => R.Wp3 i p) (motive := fun (x : (R.HW i (sg0 D A3.A)).H) => (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : (R.toCx3 F).W i) ∈
      LinearMap.range ((R.toCx3 F).θ' i A3.A.μ0)) hw' ?_ ?_ ?_
    · intro p x hx
      have hlam := hpos.2 i A3.A.μ0 p
      have ha : LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x) =
          Tw.map (twAt D.what₂.embLL A3.A.v0) (LinearMap.adjoint (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x) :=
        congrArg (fun f => f (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)) (Formalism.IndefR.Links.Tw.adjoint_map (s := (twAt D.what₂.embLL A3.A.v0)) (R.thG i A3.A.μ0))
      have key : Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0) (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)) =
          ((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ) • Tw.mk (twAt D.what₂.embLL A3.A.v0) x := by
        refine (congrArg (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) ha).trans ?_
        show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0 (LinearMap.adjoint (R.thG i A3.A.μ0) x)) = _
        rw [hA i A3.A.μ0 p _ hx, Tw.mk_smul, cj_ofReal]
      have h3 := (Formalism.IndefR.Links.RealDat3.phase_cancel hcc (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)).trans key
      refine ⟨((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ)⁻¹ •
        LinearMap.adjoint (R.phs i • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x), ?_⟩
      change (R.phs i • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ)⁻¹ •
        LinearMap.adjoint (R.phs i • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)) = Tw.mk (twAt D.what₂.embLL A3.A.v0) x
      refine (map_smul _ _ _).trans ((congrArg (fun z => ((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ)⁻¹ • z) h3).trans ?_)
      rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hlam.ne'), one_smul]
    · exact Submodule.zero_mem _
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  unfold principalFormsSubspace
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rintro _ ⟨c, rfl⟩
    rw [(R.toCx3 F).tC_eq]
    exact hsub t _ ⟨_, rfl⟩
  · exact (hsup.trans (hrng A3.A.μ0)).trans
      (le_iSup (fun t => LinearMap.range ((R.toCx3 F).tC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t)) A3.A.μ0)

end GlobalTheory.WgLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalOfPrincipalMod
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PrincipalModRadical

open GlobalTheory.CechPic GlobalTheory.LamOfDouble

theorem surjective_of_finite {R A : Type} [CommRing R] [CommRing A] (J : Ideal R) (hJ : J ≤ Ideal.jacobson ⊥)
    (φ : R →+* A) (hφ : φ.Finite) (h : ∀ a, ∃ r, a - φ r ∈ J.map φ) : Function.Surjective φ := by
  algebraize [φ]
  have key : (⊤ : Submodule R A) ≤ LinearMap.range (Algebra.linearMap R A) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ fun a _ => ?_
    obtain ⟨r, hr⟩ := h a
    rw [← add_sub_cancel (φ r) a]
    refine Submodule.add_mem_sup ⟨r, rfl⟩ ?_
    rw [Ideal.smul_top_eq_map]
    exact hr
  exact fun a => key (Submodule.mem_top (x := a))

theorem mono_of_section {R : Type} [CommRing R] (J : Ideal R) (hJ : J ≤ Ideal.jacobson ⊥) {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of R)) [IsFinite f] (e : Spec (CommRingCat.of R) ⟶ H)
    (h : ∀ (T : Scheme.{0}) (d : T ⟶ H) (t : T ⟶ Spec (CommRingCat.of (R ⧸ J))),
      d ≫ f = t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) → d = d ≫ f ≫ e) : Mono f := by
  have : IsAffine H := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (H.isoSpec.inv ≫ f)
  obtain ⟨ε, hε⟩ := Spec.map_surjective (e ≫ H.isoSpec.hom)
  have fin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  let q : Γ(H, ⊤) ⟶ CommRingCat.of (Γ(H, ⊤) ⧸ J.map φ.hom) := CommRingCat.ofHom (Ideal.Quotient.mk _)
  let τ : CommRingCat.of (R ⧸ J) ⟶ CommRingCat.of (Γ(H, ⊤) ⧸ J.map φ.hom) :=
    CommRingCat.ofHom (Ideal.quotientMap _ φ.hom Ideal.le_comap_map)
  have h₁ := h _ (Spec.map q ≫ H.isoSpec.inv) (Spec.map τ) (by
    rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_comp]
    rfl)
  have h₂ : q = ε ≫ φ ≫ q := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hφ, hε, ← cancel_mono H.isoSpec.inv, h₁]
    simp
  have sur : Function.Surjective φ.hom := surjective_of_finite J hJ φ.hom fin fun a =>
    ⟨ε.hom a, Ideal.Quotient.eq.1 (congrArg (fun g => g.hom a) h₂)⟩
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ sur
  have e' : f = H.isoSpec.hom ≫ Spec.map φ := by rw [hφ, Iso.hom_inv_id_assoc]
  rw [e']
  infer_instance

end GlobalTheory.PrincipalModRadical
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullLiftOneEqZero
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem AddCls.pull_lift_one_eq_zero {T : Over S} {c : Pic (A ⊗ T).left} (h : AddCls A c) {Y : Over S} (t : Y ⟶ T) :
    CechPic.pull (lift (1 : Y ⟶ A) t).left c = 0 := by
  have h1 := h Y 1 1 t
  rw [_root_.mul_one] at h1
  exact left_eq_add.1 h1

theorem AddCls.pull_eq_zero_of_unit {T Z : Over S} (z : Z ⟶ T) {c : Pic (A ⊗ Z).left} (h : AddCls A c)
    {T' : Scheme.{0}} (t : T' ⟶ (A ⊗ Z).left) (s : T' ⟶ T.left)
    (hts : t ≫ (A ◁ z).left = s ≫ (lift (1 : T ⟶ A) (𝟙 T)).left) : CechPic.pull t c = 0 := by
  let Y : Over S := Over.mk (t ≫ (A ⊗ Z).hom)
  let t' : Y ⟶ A ⊗ Z := Over.homMk t rfl
  have hs : s ≫ T.hom = t ≫ (A ⊗ Z).hom := by
    rw [← Over.w (A ◁ z), ← Category.assoc, hts, Category.assoc, Over.w]
  let s' : Y ⟶ T := Over.homMk s hs
  have h1 : t' ≫ A ◁ z = s' ≫ lift (1 : T ⟶ A) (𝟙 T) := Over.OverMorphism.ext hts
  have h2 : t' ≫ fst A Z = 1 := by
    have h3 := congrArg (· ≫ fst A T) h1
    simpa only [Category.assoc, whiskerLeft_fst, lift_fst, MonObj.comp_one] using h3
  have h4 : t' = lift (1 : Y ⟶ A) (t' ≫ snd A Z) := by
    rw [← h2, lift_comp_fst_snd]
  have h5 := h.pull_lift_one_eq_zero (t' ≫ snd A Z)
  rw [← h4] at h5
  exact h5

theorem pull_eq_of_compat {T Z Z' : Over S} (z : Z ⟶ T) (z' : Z' ⟶ T) (y : (addF A).obj (op Z))
    (y' : (addF A).obj (op Z'))
    (h : ∀ (Y : Over S) (a : Y ⟶ Z) (b : Y ⟶ Z'), a ≫ z = b ≫ z' → (addF A).map a.op y = (addF A).map b.op y')
    {T' : Scheme.{0}} (a : T' ⟶ (A ⊗ Z).left) (b : T' ⟶ (A ⊗ Z').left)
    (hab : a ≫ (A ◁ z).left = b ≫ (A ◁ z').left) : CechPic.pull a y.1 = CechPic.pull b y'.1 := by
  let Y : Over S := Over.mk (a ≫ (A ⊗ Z).hom)
  let a' : Y ⟶ A ⊗ Z := Over.homMk a rfl
  have hb : b ≫ (A ⊗ Z').hom = a ≫ (A ⊗ Z).hom := by
    rw [← Over.w (A ◁ z), ← Over.w (A ◁ z'), ← Category.assoc, ← hab, Category.assoc]
  let b' : Y ⟶ A ⊗ Z' := Over.homMk b hb
  have h1 : a' ≫ A ◁ z = b' ≫ A ◁ z' := Over.OverMorphism.ext hab
  have h2 : a' ≫ fst A Z = b' ≫ fst A Z' := by
    have h3 := congrArg (· ≫ fst A T) h1
    simpa only [Category.assoc, whiskerLeft_fst] using h3
  have h3 : (a' ≫ snd A Z) ≫ z = (b' ≫ snd A Z') ≫ z' := by
    have h3 := congrArg (· ≫ snd A T) h1
    simpa only [Category.assoc, whiskerLeft_snd] using h3
  have h4 := congrArg Subtype.val (h Y _ _ h3)
  rw [addF_map_val, addF_map_val] at h4
  have ha' : a' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (a' ≫ snd A Z) := by
    rw [lift_whiskerLeft, Category.id_comp, lift_comp_fst_snd]
  have hb' : b' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (b' ≫ snd A Z') := by
    rw [lift_whiskerLeft, Category.id_comp, h2, lift_comp_fst_snd]
  have h5 := congrArg (CechPic.pull (lift (a' ≫ fst A Z) (𝟙 Y)).left) h4
  rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, ← ha', ← hb'] at h5
  exact h5

theorem addF_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → (∀ (T : Over S) (J : Type) (Z : J → Over S) (z : ∀ i, Z i ⟶ T) (y : ∀ i, (addF A).obj (op (Z i))), (∀ i, IsOpenImmersion (z i).left) → (∀ p : T.left, ∃ i, p ∈ Set.range (z i).left) → (∀ (i k : J) (Y : Over S) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → (addF A).map a.op (y i) = (addF A).map b.op (y k)) → ∃ y₀ : (addF A).obj (op T), ∀ i, (addF A).map (z i).op y₀ = y i) := by
  intro S A _ hA T J Z z y hz hcov hc
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  obtain ⟨c₀, h0, hc₀⟩ := GlobalTheory.T.exists_glue_rigidified_line_bundle_classes (A ⊗ T).left T.left (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left he
    (GlobalTheory.T.isPreimageSectionsBijective_abelianScheme_snd S A T hA) J (fun i ↦ (A ⊗ Z i).left) (fun i ↦ (A ◁ z i).left)
    (fun i ↦ haveI := hz i; (z i).left.opensRange) (fun i ↦ (y i).1)
    (fun i ↦ (GlobalTheory.whiskerLeft_isOpenImmersion_range S A T (Z i) (z i) (hz i)).1)
    (fun i x ↦ (GlobalTheory.whiskerLeft_isOpenImmersion_range S A T (Z i) (z i) (hz i)).2 x)
    (fun p ↦ hcov p)
    (fun i T' t s hts ↦ AddCls.pull_eq_zero_of_unit (z i) (y i).2 t s hts)
    (fun i k T' a b hab ↦ pull_eq_of_compat (z i) (z k) (y i) (y k) (hc i k) a b hab)
  refine ⟨⟨c₀, GlobalTheory.T.additive_picClass_of_locally_additive S A T hA c₀ h0 fun p ↦ ?_⟩, fun i ↦ Subtype.ext (hc₀ i)⟩
  obtain ⟨i, hi⟩ := hcov p
  refine ⟨Z i, z i, hz i, hi, ?_⟩
  rw [hc₀ i]
  exact (y i).2

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticOperatorEigenvectorDiagonalBlockIdentit
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem qop_quadratic_on_eigenvector : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (α β x : ℂ) (y : ι → M), (∀ a b, qop F α β a b = 0) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ j, s j = false → ∑ b, F j b (y b) = 0) → ∀ a, (x ^ 2 - α * x - β) • y a = 0 := by
  intro ι M _ _ _ _ s F α β x y hq hs ht hf a
  have hall : ∀ c, ∑ b, F c b (y b) = x • y c := by
    intro c
    cases hc : s c
    · rw [hf c hc, hs c hc, smul_zero]
    · exact ht c hc
  cases ha : s a
  · rw [hs a ha, smul_zero]
  · have key : ∑ b, qop F α β a b (y b) = 0 := by simp [hq]
    have pt : ∀ b, qop F α β a b (y b)
        = ∑ c, F a c (F c b (y b)) - α • F a b (y b) - (if a = b then β • y b else 0) := by
      intro b
      simp only [qop, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
      split_ifs <;> simp
    have expand : ∑ b, qop F α β a b (y b)
        = ∑ c, F a c (∑ b, F c b (y b)) - α • ∑ b, F a b (y b) - β • y a := by
      rw [Finset.sum_congr rfl (fun b _ => pt b), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_comm, Finset.sum_ite_eq, ← Finset.smul_sum]
      simp [map_sum]
    rw [expand, ht a ha] at key
    simp only [hall, map_smul] at key
    rw [← Finset.smul_sum, ht a ha] at key
    rw [sub_smul, sub_smul, pow_two, mul_smul, mul_smul]
    exact key

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientBundleFrameExistsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_bundle_frame_exists : ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (P : VB.Sub F) (c : Fin N → Γ(F, U)), VB.IsFrame c → ∀ (l : ℕ), l ≤ N → (∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)), (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) → ∃ e : Fin (N - l) → Γ(cokernel P.incl, U), VB.IsFrame e := by
  first | exact @GlobalTheory.VB.exists_isFrame_cokernel_of_frame | exact GlobalTheory.VB.exists_isFrame_cokernel_of_frame | (intros; apply GlobalTheory.VB.exists_isFrame_cokernel_of_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaisingSpanEqSpanWordsStatement
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raisingSpan_eq_map_span_words_of_isKMod : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E → ∀ S : Submodule ℂ H, S ≤ D → raisingSpan ε σ S = (Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}).map D.subtype := by
  first | exact @GlobalTheory.HolDS.raisingSpan_eq_span_words | exact GlobalTheory.HolDS.raisingSpan_eq_span_words | (intros; apply GlobalTheory.HolDS.raisingSpan_eq_span_words <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComplexPointsLevelFormsEqGoodForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.LevelRange

theorem range_w0C_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.LUnif → ∀ b i, LinearMap.range ((R.toCx3 F).w0C b i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) ((R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 b (sg0 D A3.A))).comap (R.HW i (sg0 D A3.A)).e) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hU b i
  have hL := GlobalTheory.LevelForms.levelW_of_irr R.toRealDat F.lv2 hOk.ok2.irr hU hC.base.models.HW
  rw [← hL b i (sg0 D A3.A)]
  have h3 : Submodule.span ℂ (Set.range fun k => (⟨R.toRealDat.bC F.lv2 b i (sg0 D A3.A) k, Submodule.subset_span ⟨k, rfl⟩⟩ :
      R.toRealDat.WS F.lv2 b i (sg0 D A3.A))) = ⊤ := Submodule.span_range_subtype_eq_top_iff _ _ |>.2 rfl
  have h4 : LinearMap.range ((R.toCx3 F).wC b i A3.A.v0) = ⊤ :=
    (Fintype.range_linearCombination _ _).trans (Tw.span_top (E := R.toRealDat.WS F.lv2 b i (sg0 D A3.A)) _ h3)
  have hc : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) b)).ne'
  refine (LinearMap.range_comp_of_range_eq_top _ h4).trans (le_antisymm ?_ fun x hx => ?_)
  · rintro _ ⟨y, rfl⟩
    exact (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).smul_mem _ (Tw.out y : R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).2
  · let y : (R.HW i (sg0 D A3.A)).H := x
    exact ⟨(⟨((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ)⁻¹ • y, (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).smul_mem _ hx⟩ :
      R.toRealDat.WS F.lv2 b i (sg0 D A3.A)), smul_inv_smul₀ hc y⟩

end GlobalTheory.LevelRange
end
end

