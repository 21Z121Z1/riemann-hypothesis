import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MvZOneEqMapUnivSubst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedDiagonalCoordinateMemCompletionConjAA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0284
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryHaarEqMapProdRealFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HaarSplit
open scoped ENNReal NNReal

theorem haar_eq_map_prod : ∀ (D : D7) (Y : HSp D) (ν : Measure (GA D Y)), ν.IsHaarMeasure → ∃ (m : Measure (GinfC Y)) (μ : Measure (GfC Y)), m.IsHaarMeasure ∧ μ.IsHaarMeasure ∧ SigmaFinite m ∧ SigmaFinite μ ∧ MeasurableEmbedding (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2) ∧ ν = (m.prod μ).map (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2) := by
  intro D Y ν hν
  haveI : LocallyCompactSpace (GinfC Y) := (GlobalTheory.AdelicSplit.isClosed_GinfC' Y).locallyCompactSpace
  haveI : LocallyCompactSpace (GfC Y) := (GlobalTheory.AdelicSplit.isClosed_GfC' Y).locallyCompactSpace
  set e := GlobalTheory.AdelicSplit.splitEquiv Y with he_def
  have he : (⇑e : GinfC Y × GfC Y → GA D Y) = fun q => (q.1 : GA D Y) * q.2 := rfl
  let m₀ : Measure (GinfC Y) := Measure.haar
  let μ : Measure (GfC Y) := Measure.haar
  haveI hρ : ((m₀.prod μ).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ e
  set c := Measure.haarScalarFactor ν ((m₀.prod μ).map e) with hc_def
  have hc : ν = c • (m₀.prod μ).map e := Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  haveI hm : ((c : ℝ≥0∞) • m₀).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul _ (by simpa using hc0) ENNReal.coe_ne_top
  refine ⟨(c : ℝ≥0∞) • m₀, μ, hm, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [← he]; exact e.toHomeomorph.measurableEmbedding
  · rw [← he, Measure.prod_smul_left, Measure.map_smul, hc, ENNReal.smul_def]

end GlobalTheory.HaarSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedSectionTendstoConstantTermImaginaryFlowStatement
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedSection_tendsto_constantTerm_imaginary_flow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsBddSec la P → ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, (∀ t : ℝ, 0 ≤ t → X.flow ξ (fun _ => Complex.I * t) x ∈ X.dom) ∧ Filter.Tendsto (fun t : ℝ => P (X.flow ξ (fun _ => Complex.I * t) x)) Filter.atTop (nhds (X.fj la ξ 0 P x)) := by
  first | exact @GlobalTheory.HeckeEx.bddSec_tendsto_constTerm | exact GlobalTheory.HeckeEx.bddSec_tendsto_constTerm | (intros; apply GlobalTheory.HeckeEx.bddSec_tendsto_constTerm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryAverageFockPolynomialJetFunctional
section
open Formalism.BasicNotions Formalism.L2.DIV MeasureTheory
open scoped Matrix

noncomputable section
open MvPolynomial GlobalTheory.KJInf

namespace GlobalTheory.AvgJet

variable {ι : Type} [Fintype ι]

def evalL {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) : PY ι a →ₗ[ℂ] ℂ where
  toFun := evalAt y
  map_add' F G := by simp [evalAt]
  map_smul' c F := by simp [evalAt, smul_eval]

theorem evalL_apply {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) : evalL y F = evalAt y F := rfl

theorem dual_eq_sum_evalAt {a : ℕ} (V : Submodule ℂ (PY ι a)) [FiniteDimensional ℂ V]
    (hsep : ∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0) (Λ : Module.Dual ℂ V) :
    ∃ (S : Finset {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y}) (c : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} → ℂ),
      ∀ v : V, Λ v = ∑ y ∈ S, c y * evalAt y.1 (v : PY ι a) := by
  set E : Submodule ℂ (Module.Dual ℂ V) := Submodule.span ℂ
    (Set.range fun y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} => (evalL y.1).comp V.subtype) with hE
  have hco : E.dualCoannihilator = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    rw [Submodule.mem_dualCoannihilator] at hv
    have h0 : (v : PY ι a) = 0 := hsep _ fun y hy => hv _ (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)
    exact Subtype.ext h0
  have htop : E = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := E), hco, Submodule.dualAnnihilator_bot]
  have hΛ : Λ ∈ E := htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hΛ
  refine ⟨c.support, c, fun v => ?_⟩
  rw [← hc, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, evalL_apply, smul_eq_mul]

theorem evalAt_rhoK {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (G : VV ℂ lam)
    (Y : ι → Matrix (Fin n) (Fin n) ℂ) :
    evalAt Y ((rhoK lam (invTrK g⁻¹) G : VV ℂ lam) : PY ι n) =
      (∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift) *
        evalAt (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Y τ) (G : PY ι n) := by
  have htr : trAct (invTrK g⁻¹) = lft (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
    unfold trAct lft Formalism.GradedWeylDivisibility.blockAct
    congr 1
  have hdet : detTwK lam (invTrK g⁻¹) =
      ∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift := by
    unfold detTwK
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [detPow, invTrK, inside₂, Units.val_zpow_eq_zpow_val]
  show evalAt Y (actP lam (invTrK g⁻¹) G) = _
  rw [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, htr, hdet]
  rw [evalAt, smul_eval, ← evalAt, evalAt_lft]

theorem integrable_term {a b : ℕ} {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K]
    [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν] {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r)
    (Λ : FP ι a b →ₗ[ℂ] ℂ) (Q : FP ι a b) (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Integrable (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) Q) * evalAt (fun τ => r k τ * y τ) F) ν := by
  set U := GlobalTheory.KJAvg.univSubst Q with hU
  set p : PY ι a := ∑ m ∈ U.support, C (Λ (monomial m 1)) * coeff m U with hp'
  have hp : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, Λ (mvZ g (fun _ => 1) Q) = eval (fun w => g w.1 w.2.1 w.2.2) p := by
    intro g
    rw [GlobalTheory.KJAvg.mvZ_one_eq_map_univSubst, GlobalTheory.KJAvg.linear_eq_sum_coeff Λ U.support _ (support_map_subset _ _)]
    simp only [hp', map_sum, map_mul, eval_C, coeff_map]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have e : (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) Q) * evalAt (fun τ => r k τ * y τ) F) =
      fun k => eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) p * evalAt (fun τ => r k τ * y τ) F := by
    funext k
    rw [hp]
    simp only [GlobalTheory.KJAvg.ontoUni_inv hr]
  rw [e]
  exact GlobalTheory.KJAvg.integrable_avg_term ν hr p y F

end GlobalTheory.AvgJet

open GlobalTheory.AvgJet in

theorem GlobalTheory.AvgJet.avg_jet : ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b → 0 < a → ∀ (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (nn : ι → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' nn → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (r : K →* (ι → GL (Fin a) ℂ)), GlobalTheory.KJInf.OntoUni (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) →
    ∀ (Q : MvPolynomial (ι × Fin b × Fin a) ℂ) (Λ : Module.Dual ℂ (VV ℂ lam)), ∃ Λ' : Module.Dual ℂ (VV ℂ lam'),
    ∀ (ℓ : MvPolynomial (ι × Fin b × Fin a) ℂ →ₗ[ℂ] ℂ) (h : ι → GL (Fin b) ℂ) (v : VV ℂ lam),
      ∫ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) ∂ν =
        Λ' (rhoK lam' (invTrK h⁻¹) (Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v)) := by
  intro ι _ a b hab ha lam lam' nn hJ K _ _ _ _ _ ν _ _ r hr Q Λ
  classical
  obtain ⟨-, hcomp, -, -, -, -, hsep, -⟩ := GlobalTheory.T.fockSubstitution_identities ι a b hab
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  obtain ⟨S, c, hΛ⟩ := dual_eq_sum_evalAt (VV ℂ lam) hsep Λ
  have hav := fun y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} =>
    GlobalTheory.KJAvg.avg_span ι a b hab ha lam nn K ν (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) hr y.1 Q
  choose m y' s hinv hspan using hav
  let d : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} → ℂ := fun y => (∏ τ, (y.1 τ).det ^ nn τ)⁻¹
  refine ⟨∑ y ∈ S, (c y * d y) • ∑ j, s y j • (evalL (y' y j)).comp (VV ℂ lam').subtype, fun ℓ h v => ?_⟩
  let hh : ι → Matrix (Fin b) (Fin b) ℂ := fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ)
  let Hh : ℂ := ∏ τ, (hh τ).det ^ (lam' τ).detShift
  let ℓ₀ : FP ι a b →ₗ[ℂ] ℂ := ℓ ∘ₗ (mvZ (fun _ => 1) hh).toLinearMap
  let F : PY ι a := (v : PY ι a) * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ nn τ
  have hFV : F ∈ Vn lam nn := ⟨v, (GlobalTheory.KJInf.ClsVal.cSpan_eq_VV' lam).symm ▸ v.2, rfl⟩

  have hpt : ∀ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) =
        Hh * ∑ y ∈ S, c y * d y * (ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F) := by
    intro k
    have hsub : GlobalTheory.CompactHowe.substF hh (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q =
        mvZ (fun _ => 1) hh (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) := by
      rw [hcomp]
      simp only [mul_one, one_mul, Matrix.coe_units_inv]
      rfl
    rw [map_inv r k, hΛ]
    simp only [evalAt_rhoK]
    rw [hsub]
    set L := ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) with hL
    have hL' : ℓ (mvZ (fun _ => 1) hh (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q)) = L := rfl
    have hH : (∏ τ, ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) = Hh := rfl
    rw [hL', Finset.prod_mul_distrib, hH, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hdet : ∀ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := fun τ => (Matrix.isUnits_det_units _).ne_zero
    have key : (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift)) *
        (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ (lam τ).detShift) =
        ∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [← zpow_add₀ (hdet τ), sub_add_cancel, zpow_natCast]
    have hdy : d y * ∏ τ, (y.1 τ).det ^ nn τ = 1 :=
      inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (y.2 τ).ne_zero)
    have hF : evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F =
        evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a) *
          ((∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ) * ∏ τ, (y.1 τ).det ^ nn τ) := by
      rw [GlobalTheory.KJInf.ValPol.evalAt_mul_prod, ← Finset.prod_mul_distrib]
      simp only [Matrix.det_mul, mul_pow]
    rw [hF]
    linear_combination (Hh * L * c y * evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a)) * key -
      (Hh * L * c y * evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a) *
        ∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ) * hdy
  have hint : ∀ y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y}, Integrable (fun k => c y * d y *
      (ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F)) ν :=
    fun y => (integrable_term ν hr ℓ₀ Q y.1 F).const_mul _
  have hjet : ((Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v : VV ℂ lam') : PY ι b) =
      Formalism.L2.Ker.jetMap (fun m => ℓ (MvPolynomial.monomial m 1)) nn (v : PY ι a) := by
    have hx : Formalism.L2.Ker.jetMap (fun m => ℓ (MvPolynomial.monomial m 1)) nn (v : PY ι a) =
        ((⟨_, hJ _ _ v.2⟩ : VV ℂ lam') : PY ι b) := rfl
    simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.retrVV, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hx, Submodule.projectionOnto_apply_left]
  have hav' : ∀ y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y},
      ∫ k, ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F ∂ν =
        ∑ j, s y j * ℓ (subY hab (fun τ => hh τ * y' y j τ) F) := by
    intro y
    rw [hspan y F hFV ℓ₀]
    refine Finset.sum_congr rfl fun j _ => ?_
    show s y j * ℓ (mvZ (fun _ => 1) hh (subY hab (y' y j) F)) = _
    rw [mvZ_subY]
  have hH : (∏ τ, ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) = Hh := rfl
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ fun y _ => hint y]
  simp only [integral_const_mul, hav']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, evalL_apply,
    smul_eq_mul, evalAt_rhoK, hjet, GlobalTheory.KJInf.ClsVal.evalAt_jetMap hab, hH]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedDiagonalCoordinateMemCompletionConjAAStatement
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
theorem _root_.GlobalTheory.T.completed_diagonal_coordinate_mem_completion_conj_AA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : Frames G}, Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (x : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))), x ∈ hatMx (G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) → ∀ p : Fin ρ, ((F.dJ ρ h).pY ⬝ x ⬝ (F.dB ρ h).jY) p p ∈ complId D.host.AAbar := by
  first | exact @GlobalTheory.XCharBF.HatCoord.hatMx_coord_mem | exact GlobalTheory.XCharBF.HatCoord.hatMx_coord_mem | (intros; apply GlobalTheory.XCharBF.HatCoord.hatMx_coord_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanVanishingOnStripsAtOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.StripVanish

set_option maxHeartbeats 1000000 in

theorem mean_eq_zero_of_strips : ∀ (D : D7) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (R K : Subgroup (GA D W)), IsClosed (R : Set (GA D W)) → (∀ a ∈ GinfC W, ∀ b ∈ GfC W, a * b ∈ R → a ∈ R ∧ b ∈ R) → K ≤ GfC W → IsCompact (K : Set (GA D W)) → IsOpen ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W)) → ∀ (μR : Measure R), μR.IsHaarMeasure → μR.IsInvInvariant → ∀ (𝓡 : Set R) (𝓑 : Set (GA D W)), IsFundamentalDomain ((GQ W ⊓ R).subgroupOf R) 𝓡 μR → IsFundamentalDomain (GQ W ⊓ R : Subgroup (GA D W)) 𝓑 vW.μ → ∀ f : GA D W → ℂ, Measurable f → (∀ γ ∈ GQ W ⊓ R, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 vW.μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → (Continuous fun h => ∫ r in 𝓡, f ((r : GA D W) * h) ∂μR) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ h, f h ≠ 0 → ∃ r ∈ R, ∃ a ∈ GinfC W, ∃ k ∈ K, h = r * a * k) → (∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → MeasurableSet (strip W R C) ∧ ∫ h in 𝓑 ∩ strip W R C, f h ∂vW.μ = 0) → ∫ r in 𝓡, f r ∂μR = 0 := by
  intro D W vW R K hRc hsplit hKf hKc hKo μR hμR hμRinv 𝓡 𝓑 h𝓡 h𝓑 f hfm hfl hfi hfiR hTc hfK hsupp hstrip
  haveI := vW.haar
  haveI : LocallyCompactSpace R := hRc.locallyCompactSpace
  haveI : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  obtain ⟨hinfC, -, hcomm, ⟨e, he⟩, -⟩ := GlobalTheory.AdelicSplit.adelic_split D W
  obtain ⟨hΓc, hΓd, -⟩ :=
    GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D W (GQ W ⊓ R) inf_le_left
  set T : GA D W → ℂ := fun h => ∫ r in 𝓡, f ((r : GA D W) * h) ∂μR with hTdef
  have hQ := GlobalTheory.quot_fubini_mean (GA D W) vW.μ R (GQ W ⊓ R) inf_le_right hRc hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑 f hfm
    hfl hfi hfiR
  have hTl : ∀ s ∈ R, ∀ x, T (s * x) = T x := fun s hs x => hQ.left hs x
  have hTr : ∀ k ∈ K, ∀ x, T (x * k) = T x := by
    intro k hk x
    simp only [hTdef]
    congr 1
    funext r
    rw [← mul_assoc, hfK k hk]
  have h1 : T 1 = ∫ r in 𝓡, f (r : GA D W) ∂μR := by simp [hTdef]
  rw [← h1]
  by_contra hT1

  have hsupT : ∀ x, T x ≠ 0 → ∃ q ∈ R, ∃ a ∈ GinfC W, ∃ k ∈ K, x = q * a * k := by
    intro x hx
    by_contra hno
    apply hx
    have hz : ∀ r : R, f ((r : GA D W) * x) = 0 := by
      intro r
      by_contra hr
      obtain ⟨r₁, hr₁, a, ha, k, hk, hrx⟩ := hsupp _ hr
      refine hno ⟨(r : GA D W)⁻¹ * r₁, R.mul_mem (R.inv_mem r.2) hr₁, a, ha, k, hk, ?_⟩
      rw [show x = (r : GA D W)⁻¹ * ((r : GA D W) * x) by group, hrx]
      group
    simp [hTdef, hz]

  have hP : ∀ C : Set (GA D W), C ⊆ GinfC W → ∀ x ∈ strip W R C, T x ≠ 0 → ∃ c ∈ C, T x = T c := by
    rintro C hC x ⟨r, hr, c, hc, b, hb, rfl⟩ hx
    obtain ⟨q, hq, a, ha, k, hk, hx'⟩ := hsupT _ hx
    have hkb : k * b⁻¹ ∈ GfC W := (GfC W).mul_mem (hKf hk) ((GfC W).inv_mem hb)
    have hc' : c⁻¹ ∈ GinfC W := (GinfC W).inv_mem (hC hc)
    have hac : a * c⁻¹ ∈ GinfC W := (GinfC W).mul_mem ha hc'
    have e1 : c⁻¹ * (k * b⁻¹) = (k * b⁻¹) * c⁻¹ := hcomm _ hc' _ hkb
    have hmem : (a * c⁻¹) * (k * b⁻¹) ∈ R := by
      have : (a * c⁻¹) * (k * b⁻¹) = q⁻¹ * r := by
        calc (a * c⁻¹) * (k * b⁻¹) = a * (k * b⁻¹) * c⁻¹ := by rw [mul_assoc, e1, ← mul_assoc]
          _ = q⁻¹ * (q * a * k) * b⁻¹ * c⁻¹ := by group
          _ = q⁻¹ * (r * c * b) * b⁻¹ * c⁻¹ := by rw [hx']
          _ = q⁻¹ * r := by group
      rw [this]
      exact R.mul_mem (R.inv_mem hq) hr
    obtain ⟨hacR, -⟩ := hsplit _ hac _ hkb hmem
    refine ⟨c, hc, ?_⟩
    calc T (r * c * b) = T (q * (a * k)) := by rw [hx', mul_assoc]
      _ = T a := by rw [hTl q hq, hTr k hk]
      _ = T ((a * c⁻¹) * c) := by group
      _ = T c := hTl _ hacR c

  set U : Set (GA D W) := {h | (1 : ℝ) / 2 < (T h / T 1).re} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp (hTc.div_const (T 1)))
  have h1U : (1 : GA D W) ∈ U := by
    show (1 : ℝ) / 2 < (T 1 / T 1).re
    rw [div_self hT1]; norm_num
  haveI : LocallyCompactSpace (GinfC W) := hinfC.locallyCompactSpace
  have hU'o : IsOpen ((Subtype.val : GinfC W → GA D W) ⁻¹' U) := hUo.preimage continuous_subtype_val
  obtain ⟨C', hC'n, hC'U, hC'c⟩ :=
    local_compact_nhds (hU'o.mem_nhds (show ((1 : GinfC W) : GA D W) ∈ U from h1U))
  set C : Set (GA D W) := Subtype.val '' C' with hCdef
  have hCinf : C ⊆ GinfC W := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hCU : C ⊆ U := by rintro _ ⟨y, hy, rfl⟩; exact hC'U hy
  obtain ⟨hSm, hS0⟩ := hstrip C (hC'c.image continuous_subtype_val) hCinf
  set S := strip W R C with hSdef
  have hSinv : ∀ s ∈ R, ∀ x, s * x ∈ S ↔ x ∈ S := by
    intro s hs x
    constructor
    · rintro ⟨r, hr, c, hc, b, hb, hx⟩
      refine ⟨s⁻¹ * r, R.mul_mem (R.inv_mem hs) hr, c, hc, b, hb, ?_⟩
      rw [show x = s⁻¹ * (s * x) by group, hx]; group
    · rintro ⟨r, hr, c, hc, b, hb, rfl⟩
      exact ⟨s * r, R.mul_mem hs hr, c, hc, b, hb, by group⟩

  have hfSl : ∀ γ ∈ GQ W ⊓ R, ∀ g, S.indicator f (γ * g) = S.indicator f g := by
    intro γ hγ g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hSinv γ hγ.2 g).2 hg), hfl γ hγ g]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (hSinv γ hγ.2 g).1 hg)]
  have hfSi : ∀ h, IntegrableOn (fun r : R => S.indicator f ((r : GA D W) * h)) 𝓡 μR := by
      intro h
      by_cases hh : h ∈ S
      · have : (fun r : R => S.indicator f ((r : GA D W) * h)) = fun r : R => f ((r : GA D W) * h) :=
          funext fun r => Set.indicator_of_mem ((hSinv _ r.2 h).2 hh) _
        rw [this]; exact hfiR h
      · have : (fun r : R => S.indicator f ((r : GA D W) * h)) = fun _ => 0 :=
          funext fun r => by simp [Set.indicator_apply, hSinv _ r.2 h, hh]
        rw [this]; exact integrableOn_zero
  have hQS := GlobalTheory.quot_fubini_mean (GA D W) vW.μ R (GQ W ⊓ R) inf_le_right hRc hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑
    (S.indicator f) (hfm.indicator hSm) hfSl (hfi.indicator hSm) hfSi
  have hQS' : IsQuotIntL1 μR vW.μ (S.indicator T) 0 := by
    have e1 : (fun h => ∫ r in 𝓡, S.indicator f ((r : GA D W) * h) ∂μR) = S.indicator T := by
      funext h
      by_cases hh : h ∈ S
      · rw [Set.indicator_of_mem hh]
        simp only [hTdef]
        congr 1; funext r
        exact Set.indicator_of_mem ((hSinv _ r.2 h).2 hh) _
      · simp [Set.indicator_apply, hSinv _ (Subtype.property _) h, hh]
    have e2 : ∫ g in 𝓑, S.indicator f g ∂vW.μ = 0 := by rw [setIntegral_indicator hSm, hS0]
    rw [e1, e2] at hQS
    exact hQS
  obtain ⟨β, -, hβ⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := μR) hRc
  obtain ⟨hβi, hβ0⟩ := hQS'.cutoff hβ

  have hre : ∀ x, 0 ≤ (S.indicator T x / T 1).re ∧ (x ∈ S → T x ≠ 0 → (1 : ℝ) / 2 < (S.indicator T x / T 1).re) := by
    intro x
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
      by_cases hx : T x = 0
      · simp [hx]
      · obtain ⟨c, hc, hTc'⟩ := hP C hCinf x hxS hx
        have h2 : (1 : ℝ) / 2 < (T x / T 1).re := by rw [hTc']; exact hCU hc
        exact ⟨by linarith, fun _ _ => h2⟩
    · simp [Set.indicator_of_notMem hxS, hxS]
  set φ : GA D W → ℝ := fun x => ((β x : ℝ) • S.indicator T x / T 1).re with hφdef
  have hφ : ∀ x, φ x = (β x : ℝ) * (S.indicator T x / T 1).re := by
    intro x
    simp only [hφdef, Complex.real_smul, mul_div_assoc, Complex.re_ofReal_mul]
  have hφnn : 0 ≤ φ := fun x => by rw [hφ]; exact mul_nonneg (NNReal.coe_nonneg _) (hre x).1
  have hφi : Integrable φ vW.μ := (hβi.div_const (T 1)).re
  have hφ0 : ∫ x, φ x ∂vW.μ = 0 := by
    have h := integral_re (hβi.div_const (T 1))
    simp only [RCLike.re_to_complex] at h
    simp only [hφdef]
    rw [h, integral_div, ← hβ0, zero_div, Complex.zero_re]
  have hφae := (integral_eq_zero_iff_of_nonneg hφnn hφi).1 hφ0
  set A : Set (GA D W) := S ∩ {x | T x ≠ 0} with hAdef
  have hAm : MeasurableSet A := hSm.inter (hTc.measurable (measurableSet_singleton (0 : ℂ)).compl)
  have hAinv : ∀ s ∈ R, ∀ x, s * x ∈ A ↔ x ∈ A := by
    intro s hs x
    simp only [hAdef, Set.mem_inter_iff, Set.mem_setOf_eq, hSinv s hs x, hTl s hs x]
  set g : GA D W → ENNReal := A.indicator fun x => (β x : ENNReal) with hgdef
  have hgm : Measurable g := hβ.1.coe_nnreal_ennreal.indicator hAm
  have hg0 : ∫⁻ x, g x ∂vW.μ = 0 := by
    rw [lintegral_eq_zero_iff hgm]
    filter_upwards [hφae] with x hx
    by_cases hxA : x ∈ A
    · have h2 := (hre x).2 hxA.1 hxA.2
      rw [Pi.zero_apply, hφ] at hx
      have : (β x : ℝ) = 0 := by
        rcases mul_eq_zero.1 hx with h | h
        · exact h
        · linarith
      simp [hgdef, Set.indicator_of_mem hxA, Pi.zero_apply, NNReal.coe_eq_zero.1 this]
    · simp [hgdef, Set.indicator_of_notMem hxA]

  have hA0 : vW.μ A = 0 := by
    have hmul : Measurable fun p : GA D W × R => (p.2 : GA D W) * p.1 :=
      (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
    have e1 : vW.μ A = ∫⁻ x, ∫⁻ t : R, g ((t : GA D W) * x) ∂μR ∂vW.μ := by
      rw [← lintegral_indicator_one hAm]
      refine lintegral_congr fun x => ?_
      by_cases hxA : x ∈ A
      · have : ∀ t : R, g ((t : GA D W) * x) = β ((t : GA D W) * x) := fun t => by
          simp [hgdef, Set.indicator_of_mem ((hAinv _ t.2 x).2 hxA)]
        simp only [this, hβ.2 x, Set.indicator_of_mem hxA, Pi.one_apply]
      · have : ∀ t : R, g ((t : GA D W) * x) = 0 := fun t => by
          simp [hgdef, Set.indicator_of_notMem (mt (hAinv _ t.2 x).1 hxA)]
        simp [this, Set.indicator_of_notMem hxA]
    rw [e1, lintegral_lintegral_swap (f := fun x (t : R) => g ((t : GA D W) * x)) (hgm.comp hmul).aemeasurable]
    have e2 : ∀ t : R, ∫⁻ x, g ((t : GA D W) * x) ∂vW.μ = 0 := fun t => by
      rw [lintegral_mul_left_eq_self, hg0]
    simp [e2]

  set O : Set (GA D W) := e '' (interior C' ×ˢ ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W))) with hOdef
  have hOo : IsOpen O := e.isOpenMap _ (isOpen_interior.prod hKo)
  have h1O : (1 : GA D W) ∈ O :=
    ⟨(1, 1), ⟨mem_interior_iff_mem_nhds.2 hC'n, (K.subgroupOf (GfC W)).one_mem⟩, by rw [he]; simp⟩
  have hOA : O ⊆ A := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    rw [he]
    have hk : (p.2 : GA D W) ∈ K := Subgroup.mem_subgroupOf.1 hp2
    refine ⟨⟨1, R.one_mem, p.1, ⟨p.1, interior_subset hp1, rfl⟩, p.2, p.2.2, by simp⟩, ?_⟩
    show T (p.1 * p.2) ≠ 0
    rw [hTr _ hk]
    intro h0
    have := hC'U (interior_subset hp1)
    simp only [Set.mem_preimage, hUdef, Set.mem_setOf_eq, h0, zero_div, Complex.zero_re] at this
    linarith
  have hpos := hOo.measure_pos vW.μ ⟨1, h1O⟩
  exact hpos.ne' (measure_mono_null hOA hA0)

end GlobalTheory.StripVanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EllipticPartStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_part : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.EllipticPart := by
  first | exact @GlobalTheory.TrEllSum.ellipticPart | exact GlobalTheory.TrEllSum.ellipticPart | (intros; apply GlobalTheory.TrEllSum.ellipticPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleLinearHomFramedPointEigenbasesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_linear_hom_framed_point_eigenbases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T] (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (p : ℕ), p ≠ 0 → IsLinHom Ψ → Etale Ψ → ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left), (∀ τ j, IsLieImg p Ψ (y.u τ j) (u τ j)) ∧ (∀ τ j, IsEigAt c τ (u τ j)) ∧ ∀ τ w, IsTanAt x' w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T, IsCombAt x' (u τ) a w := by
  first | exact @GlobalTheory.HeckePointLawRing.exists_frame_image | exact GlobalTheory.HeckePointLawRing.exists_frame_image | (intros; apply GlobalTheory.HeckePointLawRing.exists_frame_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleUnipotentSplitPlaceHermitianStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_unipotent_at_split_place : (∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ V v,
      ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt V v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt V v) ∧
        Yᵀ * incM F V.J + incM F V.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt V v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt V v := by
  first | exact @GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian | exact GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian | (intros; apply GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian <;> assumption)
end

