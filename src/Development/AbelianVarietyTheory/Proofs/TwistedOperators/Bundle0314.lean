import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0300
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0284
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientDecayKFiniteSecondVector
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicPointRationalLatticeUnitaryModelIsoEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPointRationalLattice_unitaryModelIso_eq : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (x : (Formalism.IndefR.Eqv.UI.instV fr).GA), latAt fr.Λ (Formalism.IndefR.Eqv.UI.brg fr x) = GlobalTheory.Count.lamX (Formalism.IndefR.Eqv.UI.instV fr) x := by
  first | exact @GlobalTheory.LatDict.latAt_brg | exact GlobalTheory.LatDict.latAt_brg | (intros; apply GlobalTheory.LatDict.latAt_brg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointConjugateThetaLiftEqVectorValuedLift
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjAdjoint

theorem inner_eq_integral {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hH : R.models_HW)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : ∀ ρ, lowT (R.MW i σ) ρ)
    (hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) (a b : (R.HW i σ).H) :
    inner ℂ a b = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) *
      ∫ g in R.fdW i, star ((R.HW i σ).e a (fun ρ => v ρ) g) * (R.HW i σ).e b (fun ρ => v ρ) g ∂(R.νW i) := by
  obtain ⟨-, -, hip⟩ := hH i σ
  have hc := ipM_spec (R.MW i σ) (R.νW i) (R.fdW i) _ _
    (GlobalTheory.LiftLower.IsMultIP₂ (R.HW i σ) (N := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) hip a b)
  rw [hip, ipAt, (hc (fun ρ => v ρ) (fun ρ => v ρ)).2]
  congr 1
  rw [Finset.prod_eq_one, mul_one]
  intro ρ _
  rw [inner_self_eq_norm_sq_to_K, hv ρ]
  simp

end GlobalTheory.ConjAdjoint

namespace GlobalTheory.ConjAdjoint

theorem integrableOn_theta {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hI : GlobalTheory.LiftRows.InnerProductFormulaC R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (hL : GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io)
    (hM : IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0))
    (U : MMap (R.MW i σ)) (hU : U ∈ R.Wall i σ) (v : ∀ ρ, lowT (R.MW i σ) ρ) (h : GA D (Vc D i))
    (Q : PolF D (Wc D i).rank (Vc D i).rank) :
    IntegrableOn (fun g => Datum.thetaKO ω h g (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f Q) * starRingEnd ℂ (U (fun ρ => v ρ) g))
      (R.fdW i) (R.νW i) := by
  obtain ⟨μ, 𝓧, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
  obtain ⟨⟨Fr, hFr⟩, h2⟩ := (hL.1.models.νW i).1.2.2 R.θ hL.1.models.inf
  obtain ⟨mR, hmR⟩ := (h2 Fr hFr).1
  exact (hI i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hL _ _ hM μ 𝓧 hμ Fr hFr mR hmR U hU U hU v v Q Q).1 h

end GlobalTheory.ConjAdjoint

namespace GlobalTheory.ConjAdjoint
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

set_option maxHeartbeats 400000 in

theorem adjoint_eq_upLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (th : H.H →ₗ[ℂ] (R.HW i σ).H),
  Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ H.e)) thP →
  GlobalTheory.GalLift.IsProjOf R i σ thP th →
  ∀ (y : (R.HW i σ).H) (h : GA D (Vc D i)) (w : c.W),
    inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w =
      (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) fun ρ => v ρ) h := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hX hS hI hF hZ hR i σ s m μ' η' ω B f₀ f c io H hL hM hy hH v hv thP th hT hP y h w

  have hC : GlobalTheory.Hk3.Core R F := hL.1
  have hω := hL.2.2.2.2.2.1
  have hpt := hL.2.2.2.2.2.2.2.2.1
  have hc : c.Is := hL.2.2.2.2.2.2.2.2.2.1
  have hio := hL.2.2.2.2.2.2.2.2.2.2
  have hKc : starRingEnd ℂ (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _
  let φ : c.W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) := GlobalTheory.AdelicScalar.ptL R i σ B f (io (PiTensorProduct.tprod ℂ v))
  have hφ : ∀ w, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) (φ w) := fun w => hpt _
  have hinf : ∀ u ∈ GinfC (Vc D i), ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w) := fun u hu w => hio.1 u hu _ w
  have hlev : ∀ κ ∈ Lev.levA (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)), ∀ w,
      ω (κ, 1) (φ w) = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) κ)⁻¹ • φ w :=
    fun κ hκ w => hS i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hL κ hκ _
  have hWall : ∀ y' : (R.HW i σ).H, (R.HW i σ).e y' ∈ R.Wall i σ := fun y' =>
    GlobalTheory.AdelicScalar.HMod_mem (hC.models.HW i σ) y'
  have hth : ∀ y' : (R.HW i σ).H, ∀ w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) *
      starRingEnd ℂ ((R.HW i σ).e y' (fun ρ => v ρ) g)) (R.fdW i) (R.νW i) := fun y' w h =>
    integrableOn_theta R F hI i σ s m μ' η' ω B f₀ f c io hL hM _ (hWall y') v h (io (PiTensorProduct.tprod ℂ v) w)
  have hth' : ∀ y' : (R.HW i σ).H, ∀ w h, IntegrableOn (fun g => star (Datum.thetaKO ω h g (φ w)) *
      (R.HW i σ).e y' (fun ρ => v ρ) g) (R.fdW i) (R.νW i) := fun y' w h => by
    have h1 := hth y' w h
    have h2 : IntegrableOn (fun g => starRingEnd ℂ (Datum.thetaKO ω h g (φ w) *
        starRingEnd ℂ ((R.HW i σ).e y' (fun ρ => v ρ) g))) (R.fdW i) (R.νW i) :=
      h1.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable h1.1) (Filter.Eventually.of_forall fun x => by simp)
    refine Integrable.congr h2 (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.star_def]
  have hcls : ∀ u g, thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g =
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹ *
        Datum.thetaKO ω (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j)) g
          (φ (H.e u ((R.B.L i A.μ0).pres.y j))) := by
    intro u g
    refine (hT.eq _ _ _).trans ?_
    exact GlobalTheory.AdelicScalar.theta_classSum hω c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) φ hφ hinf hlev hM hy (GlobalTheory.AdelicScalar.HMod_mem hH u) g
  have hφw : ∀ w, φ w = ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w) := fun w => rfl
  clear_value φ
  have hex := GlobalTheory.AdelicScalar.exists_upVec hω c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) φ hφ hinf hlev (R.νW i) (R.fdW i)
    ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ)) (hth _)
  have hΨ := hex.choose_spec.1
  have hlaw := hex.choose_spec.2
  have hzex := GlobalTheory.AdelicScalar.HMod_onto hH (GlobalTheory.AdelicScalar.upVec_mem c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) hex.choose hlaw)
  have hz := hzex.choose_spec
  have hinv : ∀ u, ∀ γ ∈ GQ (Wc D i), ∀ g, thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) (γ * g) =
      thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g := by
    intro u γ hγ g
    refine (hcls u (γ * g)).trans (Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (hcls u g).symm)
    exact congrArg _ (GlobalTheory.T.thetaKO_mul_left_invariant_of_mem_GQ R i _ _ ω hω _ (hφ _) _ γ hγ g)
  have eF : ∀ u (y' : (R.HW i σ).H), (fun g => star (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g) *
      (R.HW i σ).e y' (fun ρ => v ρ) g) = fun g =>
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹ *
        (star (Datum.thetaKO ω (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j)) g
          (φ (H.e u ((R.B.L i A.μ0).pres.y j)))) * (R.HW i σ).e y' (fun ρ => v ρ) g) := by
    intro u y'
    funext g
    refine (congrArg (fun t => star t * (R.HW i σ).e y' (fun ρ => v ρ) g) (hcls u g)).trans ?_
    simp only [star_sum, Finset.sum_mul, star_mul', star_inv₀, star_natCast]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hintF : ∀ u (y' : (R.HW i σ).H), IntegrableOn (fun g => star (thP ((c.ext ∘ₗ H.e).rangeRestrict u)
      (PiTensorProduct.tprod ℂ v) g) * (R.HW i σ).e y' (fun ρ => v ρ) g) (R.fdW i) (R.νW i) := by
    intro u y'
    have hsum := integrable_finset_sum (μ := (R.νW i).restrict (R.fdW i)) Finset.univ fun j _ =>
      (hth' y' (H.e u ((R.B.L i A.μ0).pres.y j)) (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j))).const_mul
        ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹
    exact hsum.congr (Filter.Eventually.of_forall fun g => (congrFun (eF u y') g).symm)
  have hpair : ∀ u, ∫ g in R.fdW i, star (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g) *
      (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) g ∂(R.νW i) = inner ℂ u hzex.choose := by
    intro u
    refine (congrArg (fun F => ∫ g in R.fdW i, F g ∂(R.νW i)) (eF u (GlobalTheory.LiftLower.projH R i σ y))).trans ?_
    refine (integral_finset_sum _ fun j _ => (hth' _ _ _).const_mul _).trans ?_
    refine Eq.trans ?_ (hH.2.2 u hzex.choose).symm
    refine Eq.trans ?_ (congrArg (Bridge.adInner _ _ _ (H.e u)) hz).symm
    unfold Bridge.adInner
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (integral_const_mul _ _).trans (congrArg _ ?_)
    refine Eq.trans ?_ (inner_conj_symm _ _)
    refine Eq.trans ?_ (congrArg (starRingEnd ℂ) (hΨ _ _)).symm
    unfold GlobalTheory.AdelicScalar.l2 Lift.pet
    refine Eq.trans ?_ integral_conj
    refine congrArg (fun F : GA D (Wc D i) → ℂ => ∫ g in R.fdW i, F g ∂(R.νW i)) (funext fun g => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.star_def]
  have hadj : LinearMap.adjoint th y = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) • hzex.choose := by
    refine ext_inner_left ℂ fun u => ?_
    have e1 : (fun g => star ((R.HW i σ).e (th u) (fun ρ => v ρ) g) * (R.HW i σ).e y (fun ρ => v ρ) g) =
        fun g => star (R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v)) g) *
          (R.HW i σ).e y (fun ρ => v ρ) g :=
      funext fun g => congrArg (fun t : GA D (Wc D i) → ℂ => star (t g) * (R.HW i σ).e y (fun ρ => v ρ) g) (hP u v)
    refine (LinearMap.adjoint_inner_right th u y).trans ?_
    refine (inner_eq_integral R hC.models.HW i σ v hv (th u) y).trans ?_
    refine Eq.trans ?_ (inner_smul_right _ _ _).symm
    refine congrArg _ (Eq.trans ?_ (hpair u))
    refine (congrArg (fun F : GA D (Wc D i) → ℂ => ∫ g in R.fdW i, F g ∂(R.νW i)) e1).trans ?_
    exact GlobalTheory.T.integral_goodProjector_move_petersson R F hC hX i σ v _ (hinv u) (hintF u) y
  have e3 : c.ext (H.e (LinearMap.adjoint th y)) h = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) • hex.choose h := by
    refine (congrArg (fun x => c.ext (H.e x) h) hadj).trans ?_
    simp only [map_smul, Pi.smul_apply]
    exact congrArg _ ((congrArg (fun x => c.ext x h) hz).trans
      (GlobalTheory.T.extend_restriction_finitePoints_eq c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) hex.choose hlaw h))
  refine (congrArg (fun a => inner ℂ a w) e3).trans ?_
  refine (inner_smul_left _ _ _).trans ?_
  refine congrArg₂ (· * ·) hKc ?_
  exact (hΨ h w).trans (congrArg (fun p => GlobalTheory.AdelicScalar.l2 (R.νW i) (R.fdW i) (fun g => Datum.thetaKO ω h g p)
    ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ))) (hφw w))

end GlobalTheory.ConjAdjoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFiniteStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_unitary_K_finite : (GlobalTheory.Published.IrreducibleUnitaryAdmissible → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsAdmRep ε σ) ∧ (GlobalTheory.Published.KFiniteCoefficientsAnalytic → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε π → ∀ v w : H, IsKFin ε π v → AnalyticOnUJ ε fun g => ⟪w, π g v⟫_ℂ) := by
  first | exact @GlobalTheory.HCUnitary.admissible_and_analytic | exact GlobalTheory.HCUnitary.admissible_and_analytic | (intros; apply GlobalTheory.HCUnitary.admissible_and_analytic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDiagonalCoordinatesMemComplementIdealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStep_diagonalCoordinates_mem_complementIdeal : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : Frames G}, Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (u : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))), u ∈ latO _ _ (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) → ∀ p : Fin ρ, ((F.dJ ρ h).pY ⬝ u ⬝ (F.dB ρ h).jY) p p ∈ complId (D.host.AA * G.pl.stAbar sc) := by
  first | exact @GlobalTheory.XCharBF.DiagCoord.diag_mem_complId | exact GlobalTheory.XCharBF.DiagCoord.diag_mem_complId | (intros; apply GlobalTheory.XCharBF.DiagCoord.diag_mem_complId <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardNegativeSignsDiagonalFrameEqSignatureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_negativeSigns_diagonalFrame_eq_signature : ∀ {D : D7} (V : HSp D), V.SigOK → ∀ (A : Fr V) (τ : D.what₂.Tau), (Finset.univ.filter fun a => A.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  first | exact @GlobalTheory.FrameSylvester.neg_card_eq_sig | exact GlobalTheory.FrameSylvester.neg_card_eq_sig | (intros; apply GlobalTheory.FrameSylvester.neg_card_eq_sig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChamberCoefficientContinuousStatement
section
open MeasureTheory GlobalTheory.Chamber
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chamber_coefficient_continuous : FamilySmooth → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ Q ∈ parF 𝔞 ∅, ∀ (Z : Type) [TopologicalSpace Z] (X : Z → Finset (SV k) → A0 k), (∀ z, IsOrth 𝔞 (X z)) → (∀ P ∈ parP 𝔞 Q, Continuous fun z => X z P) → Continuous fun z => cM 𝔞 Q (expFam (X z)) 0 := by
  first | exact @GlobalTheory.FamCont.continuous_cM_expFam_zero | exact GlobalTheory.FamCont.continuous_cM_expFam_zero | (intros; apply GlobalTheory.FamCont.continuous_cM_expFam_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChamberCoefficientProductFormulaStatement
section
open MeasureTheory GlobalTheory.Chamber
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chamber_coefficient_product_formula : ExpFamilyIntegral → FamilyProduct → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ X Y W : Finset (SV k) → A0 k, IsOrth 𝔞 X → IsOrth 𝔞 Y → (∀ P ∈ parF 𝔞 ∅, W P = X P + Y P) → ((∫ H : aMQ 𝔞 ∅, gamM 𝔞 ∅ W H : ℝ) : ℂ) = cM 𝔞 ∅ (expFam W) 0 ∧ cM 𝔞 ∅ (expFam W) 0 = ∑ Q ∈ parF 𝔞 ∅, cM 𝔞 Q (expFam X) 0 * cP Q ∅ (expFam Y) 0 ∧ cP ∅ ∅ (expFam Y) 0 = 1 := by
  first | exact @GlobalTheory.Chamber.SumSplit.volume_sum_split | exact GlobalTheory.Chamber.SumSplit.volume_sum_split | (intros; apply GlobalTheory.Chamber.SumSplit.volume_sum_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChamberCoefficientTranslationStatement
section
open MeasureTheory GlobalTheory.Chamber
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chamber_coefficient_translation : FamilySmooth → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ Q ∈ parF 𝔞 ∅, ∀ X Y : Finset (SV k) → A0 k, IsOrth 𝔞 X → ∀ h : A0 k, (∀ P ∈ parP 𝔞 Q, Y P = X P + pr P h) → cM 𝔞 Q (expFam Y) 0 = cM 𝔞 Q (expFam X) 0 := by
  first | exact @GlobalTheory.Chamber.cM_expFam_shift_zero | exact GlobalTheory.Chamber.cM_expFam_shift_zero | (intros; apply GlobalTheory.Chamber.cM_expFam_shift_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiGridNumericalDataRealPlaceGapSizeBoundsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chiGridNumericalData_realPlace_gap_size_bounds : ∀ (D : D7) (large₂ : SizeData₂ D), SizeRows large₂ → ∀ τ : D.what₂.Tau, (∀ i, 2 ≤ i → i < (GlobalTheory.ChiGrid.num D 1 τ).k → (GlobalTheory.ChiGrid.num D 1 τ).v (i + 1) + 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v i) ∧ 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k + (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (∀ l, 1 ≤ l → l < (GlobalTheory.ChiGrid.num D 1 τ).m → ((GlobalTheory.ChiGrid.num D 1 τ).b l : ℝ) + 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).b (l + 1)) ∧ 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).ga ∧ 0 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k ∧ 0 < (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (((GlobalTheory.ChiGrid.num D 1 τ).a 0 : ℚ) : ℝ) ≤ large₂.sc.b ^ 2 ∧ ((GlobalTheory.ChiGrid.num D 1 τ).b (GlobalTheory.ChiGrid.num D 1 τ).m : ℝ) ≤ large₂.sc.b ^ 2 ∧ 1 ≤ large₂.sc.b ∧ 8 * ((D.R.r : ℝ) + 1) ≤ large₂.sc.b ^ 4 := by
  first | exact @GlobalTheory.GridReal.num_real_bounds | exact GlobalTheory.GridReal.num_real_bounds | (intros; apply GlobalTheory.GridReal.num_real_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientDecayKFiniteSecondVectorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientDecay_kFinite_second_vector : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (v : M.H τ) (N : ℕ), v ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → DecayAt M τ v v N → ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, DecayAt M τ v a N := by
  first | exact @GlobalTheory.KFinDecay.decayAt_of_kFin | exact GlobalTheory.KFinDecay.decayAt_of_kFin | (intros; apply GlobalTheory.KFinDecay.decayAt_of_kFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjSmoothVectorConjugateModelMemSmooth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjSmooth

open GlobalTheory.ConjDS

theorem conj_list_prod {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    A * l.prod * A⁻¹ = (l.map fun x => A * x * A⁻¹).prod := by
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  induction l with
  | nil => simp [h1]
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    calc A * (x * l.prod) * A⁻¹ = A * x * (A⁻¹ * A) * l.prod * A⁻¹ := by rw [h2]; noncomm_ring
      _ = A * x * A⁻¹ * (A * l.prod * A⁻¹) := by noncomm_ring

theorem cj_mem_sm : ∀ (D : D7) (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau)
  (w : (GlobalTheory.ConjDS.conjModel M).H τ),
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ))) ((GlobalTheory.ConjDS.conjModel M).σ τ) w →
  GlobalTheory.ConjDS.cj (M.H τ) w ∈ M.sm τ := by
  intro D Y S M τ w hw
  apply Submodule.subset_span
  intro k Xs hXs
  set A := (conjModel M).fr τ with hAdef
  have hA : IsUnit A := (conjModel M).fr_unit τ
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet

  have hrep : ∀ g, M.rep τ g (cj (M.H τ) w) = cj (M.H τ) ((conjModel M).σ τ (A * g * A⁻¹) w) := by
    intro g
    have e : rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
        ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹) = M.fr τ * g * (M.fr τ)⁻¹ := by
      rw [inv_submatrix_equiv]
      have : (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * (M.fr τ)⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
          rv (M.fr τ * g * (M.fr τ)⁻¹) := by
        ext i j
        simp [rv, Matrix.mul_apply]
      rw [this, rv_rv]
    show M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (cj (M.H τ) w) = M.σ τ (rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
        ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹)) (cj (M.H τ) w)
    rw [e]

  have hX' : ∀ i, A * Xs i * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((conjModel M).ε τ)) := by
    intro i
    have hg : Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A = gramAt D Y τ := (conjModel M).fr_gram τ
    have hi : (Xs i)ᴴ * gramAt D Y τ + gramAt D Y τ * Xs i = 0 := hXs i
    have h3 : (A⁻¹)ᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    show (A * Xs i * A⁻¹)ᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) = 0
    rw [← hg] at hi
    have : (A * Xs i * A⁻¹)ᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) =
        (A⁻¹)ᴴ * ((Xs i)ᴴ * (Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A) + (Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A) * Xs i) * A⁻¹ := by
      simp only [Matrix.conjTranspose_mul]
      calc _ = (A⁻¹)ᴴ * (Xs i)ᴴ * Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + 1 * Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) := by
              rw [Matrix.one_mul]; noncomm_ring
        _ = _ := by rw [← h3]; simp only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul]
    rw [this, hi, Matrix.mul_zero, Matrix.zero_mul]
  have hprod : ∀ t : Fin k → ℝ, A * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * A⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • (A * Xs i * A⁻¹))).prod := by
    intro t
    rw [conj_list_prod hA, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun i => ?_)
    simp only [Function.comp]
    rw [← Matrix.exp_conj A _ hA, Matrix.mul_smul, Matrix.smul_mul]
  have hc := hw k (fun i => A * Xs i * A⁻¹) hX'
  let L : Cj (M.H τ) →L[ℝ] M.H τ :=
    { toFun := cj (M.H τ)
      map_add' := map_add (cj (M.H τ))
      map_smul' := fun r x => by
        rw [← Complex.coe_smul, ← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal]
        rfl
      cont := (cj (M.H τ)).continuous }
  have hL := L.contDiff.comp hc
  convert hL using 1
  funext t
  simp only [Function.comp]
  rw [hrep, hprod]
  rfl

end GlobalTheory.ConjSmooth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelFrameMatrixFactsAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLocFacts

variable {n : ℕ}

theorem conj_mem_lie {F J G X : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F) (hG : Fᴴ * J * F = G)
    (hX : Xᴴ * G + G * X = 0) : (F * X * F⁻¹)ᴴ * J + J * (F * X * F⁻¹) = 0 := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hF
  have h1 : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hd
  have h2 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have e : (F * X * F⁻¹)ᴴ * J + J * (F * X * F⁻¹) = (F⁻¹)ᴴ * (Xᴴ * G + G * X) * F⁻¹ := by
    rw [← hG]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    congr 1
    · rw [h1, Matrix.mul_one]
    · rw [← Matrix.mul_assoc (F⁻¹)ᴴ Fᴴ, h2, Matrix.one_mul]
  rw [e, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem ofFr_mem_UH {F J G g : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F) (hG : Fᴴ * J * F = G)
    (hg : gᴴ * J * g = J) : F⁻¹ * g * F ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hF
  have h1 : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hd
  have h2 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq]
  rw [← hG]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (F⁻¹)ᴴ Fᴴ, h2, Matrix.one_mul, ← Matrix.mul_assoc F F⁻¹, h1, Matrix.one_mul,
    ← Matrix.mul_assoc J g F, ← Matrix.mul_assoc gᴴ (J * g) F, ← Matrix.mul_assoc gᴴ J g, hg]

theorem rev_conj (F g : Matrix (Fin n) (Fin n) ℂ) :
    F.submatrix Fin.revPerm (Equiv.refl _) * g * (F.submatrix Fin.revPerm (Equiv.refl _))⁻¹ =
      GlobalTheory.ConjDS.rv (F * g * F⁻¹) := by
  rw [Matrix.inv_submatrix_equiv]
  ext i j
  simp [GlobalTheory.ConjDS.rv, Matrix.mul_apply]

theorem frame_facts : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau),
  (∀ u : Formalism.REAL.UJ (M.ε τ), GlobalTheory.PackLoc.ptY M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
    (GlobalTheory.ConjDS.conjModel M).fr τ * GlobalTheory.PackLoc.ptY M τ u * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u) ∧
    M.rep τ (GlobalTheory.PackLoc.ptY M τ u) = M.σ τ (Formalism.MainNotions.S.umat u)) ∧
  ∀ X ∈ lieAt Y τ,
    (GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ ∈
      GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ)) ∧
    ∀ s : ℝ, cmp θ τ (oneP θ Y τ X s) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
      (GlobalTheory.ConjDS.conjModel M).fr τ * cmp θ τ (oneP θ Y τ X s) * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
        NormedSpace.exp (s • ((GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹)) := by
  intro D θ hθ Y S M τ
  have hF : IsUnit (M.fr τ) := M.fr_unit τ
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hF
  have hA : ∀ g, (GlobalTheory.ConjDS.conjModel M).fr τ * g * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (M.fr τ * g * (M.fr τ)⁻¹) := fun g => rev_conj (M.fr τ) g
  have hcan : ∀ U : Matrix (Fin Y.rank) (Fin Y.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * U * M.fr τ) * (M.fr τ)⁻¹ = U := by
    intro U
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  refine ⟨fun u => ⟨?_, ?_, ?_⟩, fun X hX => ⟨?_, fun s => ?_⟩⟩
  · exact ofFr_mem_UH hF (M.fr_gram τ) u.2
  · show _ * ((M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ) * _ = _
    rw [hA, hcan]
  · show M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ) * (M.fr τ)⁻¹) = _
    rw [hcan]
  · exact conj_mem_lie ((GlobalTheory.ConjDS.conjModel M).fr_unit τ) ((GlobalTheory.ConjDS.conjModel M).fr_gram τ) hX
  · have hmem : NormedSpace.exp (s • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) :=
      GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit Y τ) hX s
    have hc : cmp θ τ (oneP θ Y τ X s) = NormedSpace.exp (s • X) :=
      (GlobalTheory.PointAtPlaceHom.atTau_spec hθ Y τ hmem).2.1
    rw [hc]
    refine ⟨hmem, ?_⟩
    rw [← Matrix.exp_conj _ _ ((GlobalTheory.ConjDS.conjModel M).fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.PackLocFacts

end
end

