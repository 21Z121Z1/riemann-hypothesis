import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0330
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsColumnArrows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsLastRowArrows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsRemoveBlockArrow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0333
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUMeasurableEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

open Topology

theorem conjU_measurableEmbedding {D : D7} (S : HSp D) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    (c : D.host.E) (hJ : J = c • S.gram) : MeasurableEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ) := by
  haveI : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  let κ : GL (Fin S.rank) (AE D) → GL (Fin S.rank) (AE D) := fun g => GeneralLinearGroup.map (cA D) g
  have hκc : Continuous κ := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
    · exact Units.continuous_coe_inv.matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
  have hκκ : Function.LeftInverse κ κ := fun g => by
    ext i j
    exact Formalism.L2.Theta.cA_cA _
  have hκe : IsEmbedding κ := hκκ.isEmbedding hκc hκc
  have hmat : IsEmbedding (matHom S) := IsEmbedding.subtypeVal
  have hcomp : (Subtype.val : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J → GL (Fin S.rank) (AE D)) ∘ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ =
      κ ∘ matHom S := rfl
  have hemb : IsEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ) := by
    refine ⟨IsInducing.of_comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU S c hJ) continuous_subtype_val ?_, ?_⟩
    · rw [hcomp]; exact (hκe.comp hmat).isInducing
    · intro a b hab
      apply (hκe.comp hmat).injective
      rw [← hcomp]
      exact congrArg Subtype.val hab
  refine hemb.measurableEmbedding ?_
  have hrange : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ) =
      (κ ∘ Subtype.val) ⁻¹' (HR (AF D.host.F) D.sp.cm.sig S.gram : Set (GL (Fin S.rank) (AE D))) := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      show κ (κ (matHom S g)) ∈ (HR (AF D.host.F) D.sp.cm.sig S.gram : Set (GL (Fin S.rank) (AE D)))
      rw [hκκ]
      exact g.2
    · intro hy
      refine ⟨(⟨κ y.1, hy⟩ : HR (AF D.host.F) D.sp.cm.sig S.gram), Subtype.ext ?_⟩
      exact hκκ y.1
  rw [hrange]
  exact ((PI.AdicCompletionValuation.isClosed_HR _ _ _).preimage (hκc.comp continuous_subtype_val)).measurableSet

theorem thetaInt_eq_modelI : ∀ (D : D7) (S X : HSp D) (d : ℕ) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Wd) (c : D.host.E)
    (hJ : Y.J = c • S.gram)
    (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (ω : WRep S X) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Y Wd)
    (κ : GA D X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ),
    M.μ = ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ) → M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ '' 𝓕 →
    (∀ g h, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ g) (κ h) = thetaKO ω g h f) →
    ∀ h, thetaInt ω ν 𝓕 f h = M.I om Φ (κ h) := by
  intro D S X d Y Wd M c hJ ν 𝓕 ω om κ Φ f hμ hdom hθ h
  have he := conjU_measurableEmbedding S c hJ
  rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.I, hμ, hdom, he.restrict_map, Set.preimage_image_eq _ he.injective, he.integral_map]
  simp only [hθ]
  rfl

end GlobalTheory.SquareAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftScalarOfInnerProductFormula
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalarProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem inner_gW (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : G) (x y : (R.HW i σ).H) :
    ⟪R.gW i σ g x, R.gW i σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  LinearIsometry.inner_map_map ⟨R.gW i σ g, GlobalTheory.gW_norm_eq R hC.models.HW hC.models.gW hC.models.νW i σ g⟩ x y

theorem adjoint_projH (hC : GlobalTheory.Hk3.Core R F) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    LinearMap.adjoint (GlobalTheory.LiftLower.projH R i σ) = GlobalTheory.LiftLower.projH R i σ := by
  have hc : ∀ g, starRingEnd ℂ (RealDat.eC (A := A) σ g) = RealDat.eC (A := A) σ g⁻¹ := by
    intro g
    unfold RealDat.eC
    rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have h1 := (hX χ hχ).map_inv σ 1
    have h2 := (hX χ hχ).map_inv σ g⁻¹
    rw [inv_one] at h1
    simp only [map_mul, map_div₀, map_natCast]
    rw [h2, ← h1]
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  unfold GlobalTheory.LiftLower.projH
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hc]
  refine Finset.sum_nbij' (fun g => g⁻¹) (fun g => g⁻¹) (by simp) (by simp) (by simp) (by simp) fun g _ => ?_
  rw [← inner_gW hC i σ g⁻¹, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem projH_projH (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    GlobalTheory.LiftLower.projH R i σ (GlobalTheory.LiftLower.projH R i σ x) = GlobalTheory.LiftLower.projH R i σ x := by
  classical
  have h1 : ∀ g, ∑ a, RealDat.eC (A := A) σ a * RealDat.eC (A := A) σ (a⁻¹ * g) = RealDat.eC (A := A) σ g := by
    intro g
    unfold RealDat.eC
    conv_rhs => rw [← idemOf_mul_self A.X hX]
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp), map_sum]
    simp only [map_mul]
  unfold GlobalTheory.LiftLower.projH
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_congr rfl fun g _ => by rw [← h1 g, Finset.sum_smul]]
  rw [Finset.sum_comm (f := fun g a => (RealDat.eC (A := A) σ a * RealDat.eC (A := A) σ (a⁻¹ * g)) • R.gW i σ g x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_nbij' (fun g => a * g) (fun g => a⁻¹ * g) (by simp) (by simp) (by simp) (by simp) fun g _ => ?_
  rw [inv_mul_cancel_left, map_mul, Module.End.mul_apply, mul_comm]

theorem eq_of_ext {V : HSp D} {c : CoefA V} (hc : c.Is) {H : HMod (Bridge.Gf V → c.W)} (hinj : Function.Injective H.e) {z z' : H.H}
    (h : ∀ x w, inner ℂ (c.ext (H.e z) x) w = inner ℂ (c.ext (H.e z') x) w) : z = z' := by
  refine hinj (funext fun u => ?_)
  have e : c.ext (H.e z) (GlobalTheory.AdelicScalar.finLift V u) = c.ext (H.e z') (GlobalTheory.AdelicScalar.finLift V u) :=
    ext_inner_right ℂ fun w => h _ w
  exact (GlobalTheory.AdelicScalar.ext_finLift c hc (H.e z) u).symm.trans (e.trans (GlobalTheory.AdelicScalar.ext_finLift c hc (H.e z') u))

end GlobalTheory.ConjScalarProof

namespace GlobalTheory.ConjScalarProof
set_option maxHeartbeats 1000000 in
open GlobalTheory.LiftLower in

theorem conjScalarAt_of_sourceLevelLaw_fock_zeta : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R → GlobalTheory.ConjScalar.ConjScalarAt R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hCore hX hSL hIPF hFC hFZ hRC
  intro gramR c0R c0L hT i σ hσ μ' η' c c₁ H j th hD ev
  have hμ := hD.1
  have hη := hD.2.1
  have hf := hD.2.2.1
  have hL := hD.2.2.2
  have hL2 := (GlobalTheory.GalLift.isConjLift_iff R i σ μ' η' c H th).1 hL
  obtain ⟨ω, hL3⟩ := hL2
  obtain ⟨f₀, f, B, io, thP, hL4⟩ := hL3
  have hLD := hL4.1
  have hP := hL4.2
  have h38 := GlobalTheory.T.adelicLiftDatum_of_conjugate_liftDatum R F hCore gramR c0R c0L hT i σ c c₁ H j hσ hf μ' η' hμ hη ω f₀ f B io thP hLD
  obtain ⟨s, m, h39⟩ := h38
  have hC := h39.1
  have hν := h39.2.1
  have hy := h39.2.2.1
  have hH := h39.2.2.2
  have hth := hLD.2.2.2
  have hio := hC.2.2.2.2.2.2.2.2.2.2
  have hc : c.Is := hC.2.2.2.2.2.2.2.2.2.1
  have hv0 := hio.2.2
  let v := hv0.choose
  have hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 := hv0.choose_spec.choose_spec.1
  let K : ℂ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)
  have hKdef : K = ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ) := rfl
  have hK0 : K ≠ 0 := by
    rw [hKdef, Finset.prod_ne_zero_iff]
    intro ρ _
    have h1 := GlobalTheory.AdelicScalar.one_le_dimK i σ ρ
    exact_mod_cast (show (dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) ≠ 0 by positivity)
  have hKc : starRingEnd ℂ K = K := by
    rw [hKdef, map_prod]
    exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _
  have hadj : ∀ (y : (R.HW i σ).H) (h : GA D (Vc D i)) (w : c.W), inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w = K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) fun ρ => v ρ) h :=
    GlobalTheory.T.adjoint_conjugateThetaLift_eq_vectorValuedLift R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv thP th hth hP
  have hpp : ∀ y, projH R i σ (projH R i σ y) = projH R i σ y := projH_projH hX i σ
  have hsa : LinearMap.adjoint (projH R i σ) = projH R i σ := adjoint_projH hCore hX i σ
  have hinj : Function.Injective H.e := hH.1
  have hadjP : ∀ y, LinearMap.adjoint th (projH R i σ y) = LinearMap.adjoint th y := fun y =>
    eq_of_ext (V := Vc D i) (c := c) (H := H) hc hinj fun x w =>
      (hadj (projH R i σ y) x w).trans ((congrArg (fun z => K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e z fun ρ => v ρ) x) (hpp y)).trans (hadj y x w).symm)
  have hfix : ∀ u, projH R i σ (th u) = th u := fun u => ext_inner_right ℂ fun y =>
    (LinearMap.adjoint_inner_right (projH R i σ) (th u) y).symm.trans
      ((congrArg (fun A => inner ℂ (th u) (A y)) hsa).trans ((LinearMap.adjoint_inner_right th u (projH R i σ y)).symm.trans
        ((congrArg (inner ℂ u) (hadjP y)).trans (LinearMap.adjoint_inner_right th u y))))
  have hW : ∀ y, (R.HW i σ).e y ∈ R.Wall i σ := fun y => GlobalTheory.AdelicScalar.HMod_mem (hCore.models.HW i σ) y
  have hz : ∀ y h w, inner ℂ (c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h := by
    intro y h w
    have e1 : c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) = K⁻¹ • c.ext (H.e (LinearMap.adjoint th y)) :=
      (congrArg c.ext (H.e.map_smul K⁻¹ _)).trans (c.ext.map_smul K⁻¹ _)
    have e2 : starRingEnd ℂ K⁻¹ = K⁻¹ := by simp only [map_inv₀, hKc]
    calc inner ℂ (c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) h) w
        = inner ℂ (K⁻¹ • c.ext (H.e (LinearMap.adjoint th y)) h) w := congrArg (fun Fn => inner ℂ (Fn h) w) e1
      _ = starRingEnd ℂ K⁻¹ * inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w := inner_smul_left _ _ _
      _ = K⁻¹ * (K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h) := by simp only [e2, hadj y h w]
      _ = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h := inv_mul_cancel_left₀ hK0 _
  have hG := GlobalTheory.T.exists_scalar_innerProductFormula_unitCoefficient R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv ev
  let C := hG.choose
  have hC2 := hG.choose_spec
  let b := stdOrthonormalBasis ℂ c.W
  have key : ∀ u, th u ∈ partH R i σ ev → ∀ y₂,
      inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y₂) = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y₂ := by
    intro u hu y₂
    have e1 := GlobalTheory.T.classSum_inner_eq_sum_vectorThetaLifts R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv
      _ (hW (projH R i σ (th u))) _ (hW (projH R i σ y₂)) _ _ (hz (th u)) (hz y₂) b
    have hu' : projH R i σ (th u) ∈ partH R i σ ev := (hfix u).symm ▸ hu
    have e2 : inner ℂ (projH R i σ (th u)) (projH R i σ y₂) = inner ℂ (th u) y₂ :=
      (congrArg (fun z => inner ℂ z (projH R i σ y₂)) (hfix u)).trans
        ((congrArg (fun A => inner ℂ (th u) (A y₂)) hsa.symm).trans
          ((LinearMap.adjoint_inner_right (projH R i σ) (th u) y₂).trans (congrArg (fun z => inner ℂ z y₂) (hfix u))))
    have e4 : inner ℂ (K⁻¹ • LinearMap.adjoint th (th u)) (K⁻¹ • LinearMap.adjoint th y₂) =
        (Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂) := by
      refine e1.trans ?_
      rw [Finset.sum_congr rfl fun k _ => hC2 _ hu' (projH R i σ y₂) (b k) (b.orthonormal.1 k), e2, Finset.sum_const,
        Finset.card_fin, nsmul_eq_mul]
    have e3 : ∀ y, LinearMap.adjoint th y = K • (K⁻¹ • LinearMap.adjoint th y) := fun y =>
      (smul_inv_smul₀ hK0 _).symm
    calc inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y₂)
        = inner ℂ (K • (K⁻¹ • LinearMap.adjoint th (th u))) (K • (K⁻¹ • LinearMap.adjoint th y₂)) :=
          congrArg₂ (inner ℂ) (e3 _) (e3 _)
      _ = starRingEnd ℂ K * (K * inner ℂ (K⁻¹ • LinearMap.adjoint th (th u)) (K⁻¹ • LinearMap.adjoint th y₂)) :=
          (inner_smul_left _ _ _).trans (congrArg (fun z => starRingEnd ℂ K * z) (inner_smul_right _ _ _))
      _ = K * (K * ((Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂))) :=
          (congrArg (fun z => starRingEnd ℂ K * (K * z)) e4).trans
            (congrArg (fun k => k * (K * ((Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂)))) hKc)
      _ = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y₂ := by ring
  refine ⟨(K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re, fun u hu => ?_⟩
  by_cases h0 : th u = 0
  · simp only [h0, map_zero, smul_zero]
  have hre : (((K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re : ℝ) : ℂ) = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) := by
    have e0 : ((‖LinearMap.adjoint th (th u)‖ : ℝ) : ℂ) ^ 2 = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * ((‖th u‖ : ℝ) : ℂ) ^ 2 :=
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (LinearMap.adjoint th (th u))).symm.trans
        ((key u hu (th u)).trans (congrArg (fun z => (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * z) (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (th u))))
    have hn : ((‖th u‖ : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.2 h0)
    have e' : (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) = ((‖LinearMap.adjoint th (th u)‖ ^ 2 / ‖th u‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [eq_div_iff hn]
      exact e0.symm
    exact (congrArg (fun z : ℂ => ((z.re : ℝ) : ℂ)) e').trans ((congrArg (fun r : ℝ => (r : ℂ)) (Complex.ofReal_re _)).trans e'.symm)
  refine ext_inner_right ℂ fun y => ?_
  calc inner ℂ (th (LinearMap.adjoint th (th u))) y = inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y) :=
        (LinearMap.adjoint_inner_right th _ y).symm
    _ = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y := key u hu y
    _ = inner ℂ ((((K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re : ℝ) : ℂ) • th u) y :=
      (congrArg (fun z => z * inner ℂ (th u) y) ((Complex.conj_ofReal _).trans hre)).symm.trans (inner_smul_left _ _ _).symm

end GlobalTheory.ConjScalarProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLocallyIntegrableStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_locally_integrable : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule D.host.E V.V) (hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W) (F : DividedPowerChartLift V μ), LocallyIntegrable (constTerm (.single hW) (lift (GQ V) F)) μ ∧ (∀ u ∈ NA (.single hW), (fun g => constTerm (.single hW) (lift (GQ V) F) (u * g)) =ᵐ[μ] constTerm (.single hW) (lift (GQ V) F)) ∧ ∀ f : GA D V → ℂ, Continuous f → HasCompactSupport f → ∀ x, constTerm (.single hW) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) x = ∫ y, f (x⁻¹ * y) * constTerm (.single hW) (lift (GQ V) F) y ∂μ := by
  first | exact @GlobalTheory.ConstantTermL2.main | exact GlobalTheory.ConstantTermL2.main | (intros; apply GlobalTheory.ConstantTermL2.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousArchimedeanWeilOperatorLinePairW
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
open GlobalTheory.WeilM

namespace GlobalTheory.ArchLineContPair

theorem continuous_apply : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∀ (f : SInf F (Fin n × Fin d)) (x : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), Continuous fun t => T t f x := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hW γ hγ T hAct f x
  classical
  let κ := Fin n × Fin d
  let g₀ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1
  have hg₀ : g₀ ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  let r₀ : (κ → AF F) → ℂ := fun y => g₀ (fun i => (y i).2)
  have htens : ∀ h : SInf F κ, tens (evI F) (⇑h) r₀ = pureA F (⇑h) g₀ := fun h => rfl
  have hRest : ∀ h : SInf F κ, Rest (evI F) (⇑h) r₀ := by
    intro h
    refine ⟨fun y z hz => ?_, ?_⟩
    · have h2 : ∀ i, (z i).2 = 0 := by
        intro i
        have hu := hz ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) (by
          show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
          exact map_zero _)
        have h1 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd (congrFun hu i)
        rwa [one_mul] at h1
      show g₀ (fun i => (y i + z i).2) = g₀ (fun i => (y i).2)
      congr 1
      funext i
      show (y i).2 + (z i).2 = (y i).2
      rw [h2 i, add_zero]
    · rw [htens]
      exact Submodule.subset_span ⟨h, g₀, hg₀, rfl⟩
  let xh : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), (0 : FiniteAdeleRing (𝓞 F) F))
  let l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj xh
  have hxh : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (xh i).1) = x := by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x i)
  have hg0 : g₀ (fun i => (xh i).2) = 1 := by
    have hm : (fun i => (xh i).2) ∈ GlobalTheory.SchANonzero.intPts F κ := fun i _ v => by
      show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
      exact zero_mem (v.adicCompletionIntegers F)
    simp only [g₀, Set.indicator_of_mem hm, Pi.one_apply]
  have hl : l ∈ (adeleClass F).adm κ := by
    intro g _
    refine ⟨g (fun i => (xh i).2) • ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun h => ?_⟩
    show pureA F (⇑h) g xh = _
    simp only [pureA, hxh, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul]
    exact mul_comm _ _
  have hφ : pureA F (⇑f) g₀ ∈ (adeleClass F).sp κ := Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩
  have hc := hW.2.2 l hl _ hφ
  have key : (fun t : ℝ => T t f x) =
      (fun p => l (om p (pureA F (⇑f) g₀))) ∘ (fun t : ℝ => ((1 : UA σ X.J), γ (Multiplicative.ofAdd t))) := by
    funext t
    have e := hAct t f r₀ (hRest f)
    rw [htens, htens] at e
    simp only [Function.comp_apply]
    rw [e]
    show _ = pureA F _ g₀ xh
    simp only [pureA, hxh, hg0, mul_one]
  rw [key]
  exact hc.comp (continuous_const.prodMk (hγ.1.comp continuous_ofAdd))

end GlobalTheory.ArchLineContPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousArchimedeanWeilOperatorLinePairX
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
open GlobalTheory.WeilM

namespace GlobalTheory.ArchLineContPairLeft

theorem continuous_apply : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (f : SInf F (Fin n × Fin d)) (x : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), Continuous fun t => T t f x := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hW γ hγ T hAct f x
  classical
  let κ := Fin n × Fin d
  let g₀ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1
  have hg₀ : g₀ ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  let r₀ : (κ → AF F) → ℂ := fun y => g₀ (fun i => (y i).2)
  have htens : ∀ h : SInf F κ, tens (evI F) (⇑h) r₀ = pureA F (⇑h) g₀ := fun h => rfl
  have hRest : ∀ h : SInf F κ, Rest (evI F) (⇑h) r₀ := by
    intro h
    refine ⟨fun y z hz => ?_, ?_⟩
    · have h2 : ∀ i, (z i).2 = 0 := by
        intro i
        have hu := hz ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) (by
          show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
          exact map_zero _)
        have h1 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd (congrFun hu i)
        rwa [one_mul] at h1
      show g₀ (fun i => (y i + z i).2) = g₀ (fun i => (y i).2)
      congr 1
      funext i
      show (y i).2 + (z i).2 = (y i).2
      rw [h2 i, add_zero]
    · rw [htens]
      exact Submodule.subset_span ⟨h, g₀, hg₀, rfl⟩
  let xh : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), (0 : FiniteAdeleRing (𝓞 F) F))
  let l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj xh
  have hxh : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (xh i).1) = x := by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x i)
  have hg0 : g₀ (fun i => (xh i).2) = 1 := by
    have hm : (fun i => (xh i).2) ∈ GlobalTheory.SchANonzero.intPts F κ := fun i _ v => by
      show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
      exact zero_mem (v.adicCompletionIntegers F)
    simp only [g₀, Set.indicator_of_mem hm, Pi.one_apply]
  have hl : l ∈ (adeleClass F).adm κ := by
    intro g _
    refine ⟨g (fun i => (xh i).2) • ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun h => ?_⟩
    show pureA F (⇑h) g xh = _
    simp only [pureA, hxh, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul]
    exact mul_comm _ _
  have hφ : pureA F (⇑f) g₀ ∈ (adeleClass F).sp κ := Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩
  have hc := hW.2.2 l hl _ hφ
  have key : (fun t : ℝ => T t f x) =
      (fun p => l (om p (pureA F (⇑f) g₀))) ∘ (fun t : ℝ => (γ (Multiplicative.ofAdd t), (1 : UA σ W.J))) := by
    funext t
    have e := hAct t f r₀ (hRest f)
    rw [htens, htens] at e
    simp only [Function.comp_apply]
    rw [e]
    show _ = pureA F _ g₀ xh
    simp only [pureA, hxh, hg0, mul_one]
  rw [key]
  exact hc.comp ((hγ.1.comp continuous_ofAdd).prodMk continuous_const)

end GlobalTheory.ArchLineContPairLeft
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsAddBlockArrowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredientThetaParams_addBlockArrow : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i j : ℕ) (τ : D.what₂.Tau), i < D.R.m → j ≤ D.R.m → PairPar (GlobalTheory.SignedHC.flip (parV D (i + 1) j τ)) (parV D i j τ) (att (cen D τ (D.R.m - i)) (rkV D (i + 1) j)) (att (cen D τ (D.R.m - i)) (rkV D i j)) := by
  first | exact @GlobalTheory.GridParD.pairPar_X | exact GlobalTheory.GridParD.pairPar_X | (intros; apply GlobalTheory.GridParD.pairPar_X <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsColumnArrowsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredientThetaParams_columnArrows : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i : ℕ) (τ : D.what₂.Tau), i < D.R.m → PairPar (dualPar (GlobalTheory.SignedHC.flip (parP D (i + 1) τ))) (dualPar (parP D i τ)) (cen D τ (D.R.m - i)) (cen D τ (D.R.m - i)) ∧ PairPar (dualPar (parP D i τ)) (dualPar (GlobalTheory.SignedHC.flip (parP D (i + 1) τ))) (cen D τ (D.R.m - i)) (cen D τ (D.R.m - i)) := by
  first | exact @GlobalTheory.ParPairArrows.parPi_pairPar | exact GlobalTheory.ParPairArrows.parPi_pairPar | (intros; apply GlobalTheory.ParPairArrows.parPi_pairPar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsLastRowArrowsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredientThetaParams_lastRowArrows : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (j : ℕ) (τ : D.what₂.Tau) (hj : j < D.R.m), PairPar (dualPar (parXp D (j + 1) τ)) (dualPar (parXp D j τ)) (-(D.hc τ).e ⟨j, hj⟩) (-(D.hc τ).e ⟨j, hj⟩) := by
  first | exact @GlobalTheory.TopPair.pairPar_top | exact GlobalTheory.TopPair.pairPar_top | (intros; apply GlobalTheory.TopPair.pairPar_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsRemoveBlockArrowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredientThetaParams_removeBlockArrow : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i j : ℕ) (τ : D.what₂.Tau), i ≤ D.R.m → ∀ hj : j < D.R.m, PairPar (parV D i j τ) (parV D i (j + 1) τ) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j)) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1))) := by
  first | exact @GlobalTheory.RemoveBlock.removeBlock_pairPar | exact GlobalTheory.RemoveBlock.removeBlock_pairPar | (intros; apply GlobalTheory.RemoveBlock.removeBlock_pairPar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestDataLargeGapsIntegrableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_testData_large_gaps_integrable : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D), HostHyp D → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  first | exact @GlobalTheory.DSGapData.dsData_gap_integrable | exact GlobalTheory.DSGapData.dsData_gap_integrable | (intros; apply GlobalTheory.DSGapData.dsData_gap_integrable <;> assumption)
end

