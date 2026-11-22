import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCuspIsThClsDOfPre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0145
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0502
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0093
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NontrivialReferenceForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsDivStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0391
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0531
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcIsEquivAtSerOfTie
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealGeo.PhaseOne

open GlobalTheory.PhaseRationalDegenerate GlobalTheory.AdTh GlobalTheory.PtId GlobalTheory.OneMapTuples

theorem lieFac_eq_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) {x : ℝ}
    (hx : 0 < x) (a : (E →+* ℂ) × ℕ → ℕ) : lieFac Dw x a = (Real.sqrt (2 * Real.pi * x))⁻¹ ^ GlobalTheory.PtId.degW Dw a := by
  have h : 0 < 2 * Real.pi * x := by positivity
  have e : (Real.sqrt (2 * Real.pi * x))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * x)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h, ← Real.exp_neg]
    congr 1
    ring
  rw [e, ← Real.exp_nat_mul, lieFac, GlobalTheory.PtId.degW]
  congr 1
  push_cast
  ring

theorem shape {c s l k m r : ℂ} (hc : c ≠ 0) : s * l * k * (m * r) = c * (c⁻¹ * s * k * l * m * r) := by
  field_simp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Rat

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
  (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

end Rat

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem wt_n (hT : TieIn T R κ v₀) (i : Fin D.R.m) : (κ i).n = (Vc D i).rank :=
  (hT.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm

theorem fieldRange_le (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) :
    D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F := by
  rintro _ ⟨a, rfl⟩
  have h : ((O.jL a : O.c'.F) : ℂ) = D.what₂.embLL a := RingHom.congr_fun hP.lift.field a
  show D.what₂.embLL a ∈ O.c'.F
  exact h ▸ (O.jL a).2

set_option maxHeartbeats 1000000 in

theorem tieC_of_serOf (hR : PreChar R) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hs : SerOf O (κ i) (v₀ i (sg0 D A)) cc 1) :
    OneMapTieC O.hle D.what₂.embLL.toRatAlgHom.fieldRange (T.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu (xiR D) (wtA (κ i))
      (actLev T.Q.c O.lev2) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc cc 1 :=
  ⟨fieldRange_le O hP, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hP.act.1).2,
    oneMapRow_of_serOf_ofPre D G Pl0 T0 A T R κ v₀ hR hT i Tp tup O hP cc hs
      (GlobalTheory.ClassSumRule.exists_cusp_isThClsD_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hR hT i Tp tup O hP)⟩

end GlobalTheory.RealGeo.PhaseOne

namespace GlobalTheory.RealGeo

open GlobalTheory.AdTh GlobalTheory.PtId GlobalTheory.OneMapTuples PhaseOne

set_option maxHeartbeats 2000000 in

theorem exists_scalar_serOf {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (hC : PreChar R) (hT : TieIn T R κ v₀) (hio : IoExt R)
    (i : Fin D.R.m) (c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) :
    ∃ s : ℂ, ‖s‖ = 1 ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0' →
      ∀ c0 : ℂ, ‖c0‖ = 1 → XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 →
      ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
        (R.ωP i A.μ0) (R.vacP i) cc → SerOf O (κ i) (v₀ i (sg0 D A)) ((c0⁻¹ * s) • cc) 1 := by
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
    O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)
  swap
  · exact ⟨1, norm_one, fun Tp tup O hP => absurd ⟨Tp, tup, O, hP⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀⟩ := hex
  obtain ⟨ka, hka1, hka⟩ := OneScalar.exists_scalar_ofPre D G Pl0 T0 A T R κ v₀ hC hT hio i c0L
  have hs₀ : O₀.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨hemb, hiso, -⟩ := dict_cast T hT.laws _ (inR i) O₀.s0 (hs₀ ▸ T.toCore.good_σ₀) (Wc D i) O₀.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := ShortSeries.thetaKO_eq_short_series_ofPre D G Pl0 T0 A _ R hC i hP₀.lift.std _ _ (iotaW T i) hemb hiso
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = ka * (((δ : ℤ) : ℂ) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) *
    (-1) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) := ⟨_, rfl⟩
  have hs1 : ‖s‖ = 1 := by
    rcases Int.units_eq_one_or δ with h | h <;> simp [hs, h, hka1]
  have hx : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hcm : cmpConst D ka δ (GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) =
      s * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) := by
    rw [lieFac_eq_pow _ hx, hs, cmpConst]
    simp only [Complex.ofReal_pow, Complex.ofReal_inv]
    ring
  refine ⟨s, hs1, fun Tp tup O hP hbc c0 h0 hxi cc hcc => ?_⟩
  have hne : c0 ≠ 0 := norm_ne_zero_iff.1 (h0 ▸ one_ne_zero)
  refine ⟨fun k => ?_, norm_one, fun t h J' hR y x hx f _ hf g => ?_⟩
  · show ‖c0⁻¹ * s * cc k‖ = 1
    rw [norm_mul, norm_mul, norm_inv, h0, hs1, hcc.1 k]
    norm_num
  · have h2 := exact_identity_ofPre hC hT O hP (hka Tp tup O hP hbc) hδ
      (covAt_of_xiConst_ofPre D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP c0 hxi) hcc t h J' hR y x hx f hf g
    rw [hcm] at h2
    refine mul_left_cancel₀ hne ((congrArg _ (one_mul _)).trans (h2.trans ?_))
    exact shape hne

set_option maxHeartbeats 1000000 in

theorem exists_serOf_of_ccIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), PreChar R → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∃ u : ℂ, ‖u‖ = 1 ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hC hT hio i Tp tup O hP cc hcc
  obtain ⟨_, _, c0L, -, hbc⟩ := hP.lift.c0
  obtain ⟨c0, ⟨m, hm, hr⟩, hxi⟩ := hP.cxi
  have h0 : ‖c0‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hr hm.ne'
  obtain ⟨s, hs1, hs⟩ := exists_scalar_serOf hC hT hio i (c0L i)
  refine ⟨c0⁻¹ * s, ?_, hs Tp tup O hP hbc c0 h0 hxi cc hcc⟩
  rw [norm_mul, norm_inv, h0, hs1]
  norm_num

set_option maxHeartbeats 1000000 in

theorem exists_ccIs_equivAt_serOf_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), PreChar R → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ O.EquivAt (κ i) (u • cc) ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 ∧ OneMapTieC O.hle D.what₂.embLL.toRatAlgHom.fieldRange (T.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu (xiR D) (wtA (κ i)) (actLev T.Q.c O.lev2) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc (u • cc) 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hC hT hio i Tp tup O hP
  obtain ⟨cc, hcc⟩ := CcEx.exists_ccIs_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP
  obtain ⟨u, hu, hS⟩ := exists_serOf_of_ccIs D G Pl0 T0 A T R κ v₀ hC hT hio i Tp tup O hP cc hcc
  exact ⟨cc, hcc, u, hu,
    GlobalTheory.FrameConstMove.equivAt_of_ccIs_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP cc hcc u, hS,
    tieC_of_serOf hC hT O hP hS⟩

end GlobalTheory.RealGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.TorRef TensorProduct

namespace GlobalTheory.NormalBaseChange

theorem exists_etale_of_isEtaleCompletion (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] [IsNoetherianRing A] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (het : IsEtaleCompletion (algebraMap A R)) (hfu : ((residue R).comp (algebraMap A R)).FormallyUnramified) :
    ∃ g : AdicCompletion (maximalIdeal A) A →+* R, g.comp (algebraMap A _) = algebraMap A R ∧
      @Algebra.Etale _ R _ _ g.toAlgebra := by
  obtain ⟨hflat, hmap, hfin⟩ := het
  set h := algebraMap A R with hh
  let D := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing D := AdicNoeth.isNoetherianRing_adicCompletion A _
  haveI : IsAdicComplete ((maximalIdeal A).map h) R := by rw [hmap]; infer_instance
  obtain ⟨g, hg⟩ := exists_adicCompletion_ringHom_extend (maximalIdeal A) h
  letI : Algebra D R := g.toAlgebra
  have hgA : ∀ a, g (algebraMap A D a) = h a := fun a => RingHom.congr_fun hg a
  have hmA : (maximalIdeal D).map (algebraMap D R) = maximalIdeal R := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
    change (maximalIdeal A).map (g.comp _) = _
    rw [hg, hmap]
  haveI : IsLocalHom (algebraMap D R) := ((local_hom_TFAE _).out 0 2).mpr hmA.le
  have hres : ((residue R).comp g).Finite :=
    RingHom.Finite.of_comp_finite (f := algebraMap A D) (by rw [RingHom.comp_assoc, hg]; exact hfin)
  haveI : Module.Finite D (R ⧸ (maximalIdeal D).map (algebraMap D R)) := by
    rw [← RingHom.finite_algebraMap]
    show ((Ideal.Quotient.mk _).comp (algebraMap D R)).Finite
    rw [hmA]
    exact hres
  haveI : IsHausdorff ((maximalIdeal D).map (algebraMap D R)) R := by rw [hmA]; infer_instance
  haveI : Module.Finite D R := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal D)
  haveI : Module.Flat D R := by
    refine LocalFlat.flat_of_relationsLift R (I := maximalIdeal D)
      (hmA.le.trans (maximalIdeal_le_jacobson _)) fun n => ?_
    haveI : Module.Flat A R := RingHom.flat_algebraMap_iff.mp hflat
    have fg := (maximalIdeal A).fg_of_isNoetherianRing
    have hkerA : ∀ x : D, AdicCompletion.evalₐ (maximalIdeal A) n x = 0 ↔ x ∈ maximalIdeal D ^ n := by
      intro x
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem A,
        ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
      constructor
      · intro h0
        rw [← AdicCompletion.factor_evalₐ_eq_eval _ x (by simp), h0, map_zero]
      · intro h0
        rw [← AdicCompletion.factor_eval_eq_evalₐ _ x (by simp), h0, map_zero]
    have hmapn : (maximalIdeal D ^ n).map (algebraMap D R) = (maximalIdeal A ^ n).map (algebraMap A R) := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_map]
      change (maximalIdeal A ^ n).map (g.comp _) = _
      rw [hg]
    refine LocalFlat.relationsLift_of_square
      (AdicCompletion.evalₐ (maximalIdeal A) n).toRingHom
      (Ideal.Quotient.mk ((maximalIdeal A ^ n).map (algebraMap A R)))
      (algebraMap _ _) (AdicCompletion.surjective_evalₐ _ n) Ideal.Quotient.mk_surjective ?_ ?_ ?_ ?_
    · ext x
      exact (hkerA x)
    · rw [Ideal.mk_ker, hmapn]
    · ext x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal A) n x)
      have hx : x - algebraMap A D a ∈ maximalIdeal D ^ n := by
        rw [← hkerA, map_sub, ← ha, AlgHom.commutes, sub_eq_zero]
        rfl
      have hx' : algebraMap D R x - h a ∈ (maximalIdeal A ^ n).map (algebraMap A R) := by
        rw [← hmapn, ← hgA]
        rw [show algebraMap D R x - g (algebraMap A D a) = algebraMap D R (x - algebraMap A D a) from
          (map_sub g _ _).symm]
        exact Ideal.mem_map_of_mem _ hx
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← ha]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, eq_comm, Ideal.Quotient.eq]
      exact hx'
    · rw [RingHom.flat_algebraMap_iff]
      exact Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R (maximalIdeal A ^ n)).toLinearEquiv
  haveI : Algebra.FormallyUnramified D (ResidueField R) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    have e : (algebraMap D (ResidueField R)).comp (algebraMap A D) = (residue R).comp h := by
      rw [← hg]; rfl
    exact RingHom.FormallyUnramified.of_comp (f := algebraMap A D) (by rw [e]; exact hfu)
  haveI : Algebra.FormallyUnramified D R :=
    GlobalTheory.EtaleCompletionNormal.formallyUnramified_of_map_maximalIdeal hmA
  haveI : Algebra.FinitePresentation D R :=
    (Algebra.FinitePresentation.of_finiteType (R := D) (A := R)).1 inferInstance
  exact ⟨g, hg, Algebra.Etale.of_formallyUnramified_of_flat⟩

theorem normal_transfer {S S' : Type} [CommRing S] [CommRing S'] (e : S ≃+* S')
    (h : ∀ (Q : Ideal S) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q))
    (Q' : Ideal S') [Q'.IsPrime] : IsDomain (Localization.AtPrime Q') ∧ IsIntegrallyClosed (Localization.AtPrime Q') := by
  haveI : (Q'.comap e).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨h1, h2⟩ := h (Q'.comap e)
  have hM : (Q'.comap e).primeCompl.map e.toMonoidHom = Q'.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      show e.symm x ∉ Q'.comap e
      rw [Ideal.mem_comap, RingEquiv.apply_symm_apply]
      exact hx
  let f : Localization.AtPrime (Q'.comap e) ≃+* Localization.AtPrime Q' :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (Q'.comap e)) (Localization.AtPrime Q') e hM
  exact ⟨f.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv f⟩

theorem normal_noetherian_tensor : ∀ (A C R : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing C] [Algebra A C] [Algebra.EssFiniteType A C] [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra A R], (∀ (P : Ideal C) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) ∧ CharZero (Localization.AtPrime P)) → IsCN R → IsEtaleCompletion (algebraMap A R) → ((residue R).comp (algebraMap A R)).FormallyUnramified → ∀ (Q : Ideal (TensorProduct A C R)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) ∧ IsNoetherianRing (Localization.AtPrime Q) := by
  intro A C R _ _ _ _ _ _ _ _ _ _ hC hCN het hfu
  haveI := hCN.1
  exact GlobalTheory.TensorNormal.localization_tensor_normal_of_charZero A C R hC het hfu

end GlobalTheory.NormalBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtTwistedPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Second

theorem exists_lt_of_stage (hG : GlobalTheory.Published.GreenCuspidal) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)
    (hO : K.Over B.toPre) (hX : B.fields.Ok) (G : GJStage B w.C) :
    ∃ Z : w.Lt, Z.G = G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) := by
  obtain ⟨R⟩ := GlobalTheory.Mem.Df.rowsDef_nonempty w.I w.ok w.pins w.l hX
  obtain ⟨kb, ks, hk⟩ := GlobalTheory.Mem.Df.Model.exists_ka B
  let W' : RowsRest B w.C :=
    { R.W with
      eOp := fun _ => 0
      eOp_idem := fun _ => LinearMap.comp_zero _
      eOp_sa := fun _ => LinearMap.IsSymmetric.zero
      kaBig := kb
      kaSmall := ks }
  obtain ⟨V, -⟩ := GlobalTheory.Mem.DivModel.exists_divStage B w.C W'
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C W' G.cd hO (GlobalTheory.Mem.Df.cols_pos w.I w.ok w.pins w.l hX)
    (show R.W.Drows ≤ R.W.Dall by rw [R.std.drows, R.std.dall])
  have hMt : ∀ (μ : w.C.Tup) (j : ℕ), W'.eMt μ j = 0 := fun μ j => by
    haveI := R.std.mt μ j
    exact LinearMap.ext fun _ => Subsingleton.elim _ _
  obtain ⟨N, -, -, hN, -⟩ := GlobalTheory.Mem.Top.exists_nStage_grpTrue hG B w.C W' R.std.sha (fun j v _ _ => R.std.eta j v)
    (fun _ => rfl) hMt f
  exact ⟨⟨W', V, S, N, G⟩, rfl, hN, GlobalTheory.Mem.R3.Model.grpAt_of_grpTrue (w.st ⟨W', V, S, N, G⟩) w.I w.ok
    (by show GrpTrue N w.I.C; rw [w.C_eq]; exact hN), hk w.C W' rfl rfl V S N G⟩

theorem exists_below_of_range (D D' : D7) (h : Set.range D.what₂.embLL ⊆ Set.range D'.what₂.embLL) (v' : D'.what₂.places.Pl) :
    ∃ v : D.what₂.places.Pl, Below D D' v v' := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.PrimeBelow.exists_below
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.PrimeBelow.exists_below
  | exact @_root_.GlobalTheory.PrimeBelow.exists_below
  | exact _root_.GlobalTheory.PrimeBelow.exists_below
  | (apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeBelow.exists_below <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeBelow.exists_below ..)

theorem resChar_of_below {D D' : D7} {v : D.what₂.places.Pl} {v' : D'.what₂.places.Pl} (hB : Below D D' v v') :
    D'.what₂.places.resChar v' = D.what₂.places.resChar v := by
  refine GlobalTheory.LvT.Inh.resChar_eq_of_mem_plEq D' v' (D.what₂.places.resChar_prime v) ((hB _ _ ?_).1 (GlobalTheory.LvT.Inh.resChar_mem_plEq D v))
  simp only [map_natCast]

theorem not_mem_W1F_zero (D : D7) (v : D.what₂.places.Pl) : v ∉ placesWithNonzeroContentOrConj D (fun _ _ => 0) := by
  rintro ⟨_, _, _, h⟩
  exact h rfl

end GlobalTheory.Mem.R3.Rw.Second

namespace GlobalTheory.Mem.R3.Rw.Second

theorem exists_ext_twisted_places : GlobalTheory.Published.GreenCuspidal → DatExt → StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Pinned K B f T w → HEq w'.px w.px → T'.pl = T.pl → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → Fine z → HoldsL z.R z.F → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) → (∀ (Z' : w'.Lt) v', (∀ v, Below (w.D Z) (w'.D Z') v v' → v ∉ Wt) → T'.psi v' = 1) → ∃ (Z' : w'.Lt) (hX' : B'.fields.Ok) (z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}), GIs2 K w' Z'.G ∧ GrpTrue Z'.N f' ∧ GrpAt (w'.st Z') w'.I ∧ DV.KapDef (w'.D Z') ∧ Fine z' ∧ (∀ v ∈ z'.W1 (F0K K.s (w'.D Z')), B'.places.resChar v ∈ T'.pl) ∧ (∀ v, v ∉ z'.W1 (F0K K.s (w'.D Z')) → T'.psi v = 1) ∧ Ext z z' ∧ ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ Wt ↔ v' ∈ z'.W1 (F0K K.s (w'.D Z'))) := by
  intro hG hDE
  have hP : StepW Pinned Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine ((hP.and hDE).and GlobalTheory.T.exists_GJStage_GIs2_pinned).trans (StepW.of_all fun K B' f' T' w' hO' _ H => ?_)
  obtain ⟨⟨⟨pin'⟩, hDE'⟩, G, hG2⟩ := H
  intro B f T w hE hf hPin hpx hpl Z hX Wt z hGT hGA hKap hFine hHL hWt hsub hpsi
  obtain ⟨Z', rfl, hGT', hGA', hKap'⟩ := exists_lt_of_stage hG w' hO' pin'.hX G
  obtain ⟨z', hFine', hExt⟩ := hDE' B f T w hE hf hPin hpx Z hX Wt z hGT hGA hFine hHL Z' pin'.hX hGT' hGA'
    (hG2 Z'.W Z'.V Z'.S Z'.N).1
  have key : ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ Wt ↔ v' ∈ z'.W1 (F0K K.s (w'.D Z'))) := by
    intro v v' hB
    have h0 := hExt.W1 v v' hB
    have a := Dat.mem_auxiliaryPlaces_iff_three_parts z (fun _ _ => 0) v
    have b := Dat.mem_auxiliaryPlaces_iff_three_parts z' (fun _ _ => 0) v'
    have i0 : (v ∈ z.IwasawaPlaceIndex ∨ v ∈ z.W1jw) ↔ (v' ∈ z'.IwasawaPlaceIndex ∨ v' ∈ z'.W1jw) :=
      ⟨fun h => (b.1 (h0.1 (a.2 (Or.inl h)))).resolve_right (not_mem_W1F_zero _ _),
        fun h => (a.1 (h0.2 (b.2 (Or.inl h)))).resolve_right (not_mem_W1F_zero _ _)⟩
    have c := Dat.mem_auxiliaryPlaces_iff_three_parts z (F0K K.s (w.D Z)) v
    have d := Dat.mem_auxiliaryPlaces_iff_three_parts z' (F0K K.s (w'.D Z')) v'
    have e := nonzeroForcedContentPlaces_agree_over_enlargement K B f T w B' f' T' w' hE Z Z' hKap hKap' v v' hB
    rw [hWt]
    exact c.trans ((or_congr i0 e).trans d.symm)
  refine ⟨Z', pin'.hX, z', hG2, hGT', hGA', hKap', hFine', ?_, ?_, hExt, key⟩
  · intro v' hv'
    obtain ⟨v, hB⟩ := exists_below_of_range (w.D Z) (w'.D Z') hE.2.2.2 v'
    have hv := (key v v' hB).2 hv'
    have hr := resChar_of_below hB
    rw [hpl]
    exact hr ▸ hsub v hv
  · intro v' hv'
    exact hpsi Z' v' fun v hB hv => hv' ((key v v' hB).1 hv)

end GlobalTheory.Mem.R3.Rw.Second
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaFixesAbelianPartOfTorsionPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InertiaFix

open GlobalTheory.TorusExt GlobalTheory.UnramTorsion ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] gtGroup

theorem sigma_fixes_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ), IsUnit (k : O) → ∀ (σ : F →ₐ[FractionRing R] F), (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    ∀ p : QkPt D F k, spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left := by
  intro R _ _ D hB F _ _ O φ hφ k hk σ hσ p
  have memO : ∀ x : O, σ (x : F) ∈ O := fun x => by
    have h1 : σ (x : F) - x ∈ O := (O.valuation_le_one_iff _).1 (hσ x x.2).le
    have := O.add_mem _ _ h1 x.2
    simpa using this
  let σO : O →+* O := (σ.toRingHom.comp O.subtype).codRestrict O.toSubring memO
  have hσO : ∀ x : O, ((σO x : O) : F) = σ x := fun _ => rfl
  have hσφ : σO.comp φ = φ := RingHom.ext fun r => Subtype.ext (by
    show σ ((φ r : O) : F) = (φ r : F)
    rw [hφ]; exact σ.commutes _)
  have hres : (IsLocalRing.residue O).comp σO = IsLocalRing.residue O := RingHom.ext fun x => by
    show IsLocalRing.residue O (σO x) = IsLocalRing.residue O x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply (ValuationSubring.valuation_lt_one_iff O _).2
    have : ((σO x - x : O) : F) = σ (x : F) - x := by push_cast; rfl
    rw [this]; exact hσ x x.2
  have hsub : σ.toRingHom.comp O.subtype = O.subtype.comp σO := rfl
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ) := Over.homMk (spMap O.subtype) (by
    show spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  obtain ⟨b', hb'⟩ := exists_extend O φ ρ rfl p.g.b
  let σ' : Over.mk (spMap φ) ⟶ Over.mk (spMap φ) := Over.homMk (spMap σO) (by
    show spMap σO ≫ spMap φ = spMap φ
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσφ])
  have := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
  haveI := D.P.isAb.comm
  have hd : IsDominant (spMap O.subtype) := by
    constructor
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical O.subtype).2
      (by rw [(RingHom.injective_iff_ker_eq_bot O.subtype).1 Subtype.val_injective]; exact bot_le)
  have hpk : p.g.b ^ k = cP D _ p.y := by
    rw [← nsmul_b, qk_nsmul hB, iota_b]
  have hpow : b' ^ k = cP D _ p.y := by
    have e : ρ ≫ b' ^ k = ρ ≫ cP D _ p.y := by
      rw [comp_cP, ← hpk, ← hb']; exact map_pow (preHom ρ) _ _
    apply Over.OverMorphism.ext
    haveI : IsReduced (Over.mk (spMap φ)).left := (inferInstance : IsReduced (Sp O))
    exact ext_of_isDominant (spMap O.subtype) (congrArg CommaMorphism.left e)
  have hpow' : b' ^ k = (σ' ≫ b') ^ k := by
    have e2 : σ' ≫ b' ^ k = (σ' ≫ b') ^ k := map_pow (preHom σ') b' k
    rw [← e2, hpow, comp_cP]
  have hcl : spMap (IsLocalRing.residue O) ≫ b'.left = spMap (IsLocalRing.residue O) ≫ (σ' ≫ b').left := by
    rw [Over.comp_left, ← Category.assoc]
    congr 1
    show _ = spMap (IsLocalRing.residue O) ≫ spMap σO
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hres]
  have heq : b' = σ' ≫ b' := GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint (Sp R) D.P.A D.P.isAb.smooth O (spMap φ) k hk b' (σ' ≫ b') hpow'
    (IsLocalRing.ResidueField O) (IsLocalRing.residue O) inferInstance hcl
  rw [← hb', Over.comp_left]
  show spMap σ.toRingHom ≫ spMap O.subtype ≫ b'.left = spMap O.subtype ≫ b'.left
  conv_rhs => rw [heq]
  rw [← Category.assoc, Over.comp_left, ← Category.assoc]
  congr 1
  show spMap σ.toRingHom ≫ spMap O.subtype = spMap O.subtype ≫ spMap σO
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory.InertiaFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatDRSubsetLatHT
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

theorem latDR_subset_latHT :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (x : Sp C ⟶ X), latDR t x ⊆ latHT t p x := by
  intro E _ _ _ H X t C _ _ p x v hv
  obtain ⟨xO, hx, vO, htan, hvO⟩ := hv
  have h1 : epsMul (1 : C) = RingHom.id (DualNumber C) := by
    ext a <;> simp [epsMul]
  have h2 : spMap (RingHom.id (DualNumber C)) = 𝟙 _ := by
    simp [spMap]
  refine ⟨xO, hx, 0, vO, htan, ?_, ?_⟩
  · rw [pow_zero, h1, h2, Category.id_comp, hvO]
  · intro n c g _
    rw [pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top

end GlobalTheory.ShFam.Pad
end

