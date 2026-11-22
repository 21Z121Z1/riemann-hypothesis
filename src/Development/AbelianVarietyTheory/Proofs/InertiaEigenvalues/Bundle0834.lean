import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0740
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0825
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharInfinityEqCoeffMulHalfNormPow
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

theorem phase_zpow_eq (z : ℂ) (hz : z ≠ 0) (b : ℤ) (r : ℕ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * b + (r : ℤ)) =
      z ^ (b + (r : ℤ)) * ((starRingEnd ℂ z) ^ b)⁻¹ * (((‖z‖ : ℝ) : ℂ) ^ r)⁻¹ := by
  have hN : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hc : starRingEnd ℂ z ≠ 0 := (map_ne_zero _).2 hz
  have hsq : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have h2b : ((‖z‖ : ℝ) : ℂ) ^ (2 * b) = z ^ b * (starRingEnd ℂ z) ^ b := by
    rw [_root_.zpow_mul, show ((‖z‖ : ℝ) : ℂ) ^ (2 : ℤ) = ((‖z‖ : ℝ) : ℂ) ^ (2 : ℕ) from zpow_ofNat _ 2, hsq, mul_zpow]
  have hzn : z ^ (2 * b + (r : ℤ)) = z ^ b * z ^ (b + (r : ℤ)) := by
    rw [← zpow_add₀ hz]; congr 1; ring
  rw [div_zpow, zpow_add₀ hN, h2b, hzn, zpow_natCast]
  have h1 : z ^ b ≠ 0 := zpow_ne_zero _ hz
  have h2 : (starRingEnd ℂ z) ^ b ≠ 0 := zpow_ne_zero _ hc
  have h3 : ((‖z‖ : ℝ) : ℂ) ^ r ≠ 0 := pow_ne_zero _ hN
  field_simp

theorem prod_norm_inv_pow {ι : Type} [Fintype ι] (z : ι → ℂ) (r : ℕ) :
    ∏ i, (((‖z i‖ : ℝ) : ℂ) ^ r)⁻¹ = (((∏ i, ‖z i‖ ^ 2) ^ (-(r : ℝ) / 2) : ℝ) : ℂ) := by
  rw [← Real.finset_prod_rpow _ _ (fun i _ => by positivity)]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_natCast_mul (norm_nonneg _)]
  rw [show ((2 : ℕ) : ℝ) * (-(r : ℝ) / 2) = -(r : ℝ) by push_cast; ring, Real.rpow_neg (norm_nonneg _),
    Real.rpow_natCast]
  push_cast
  rfl

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem conjugate_tauE_ne_tauE (D : D7) (τ τ' : D.what₂.Tau) :
    NumberField.ComplexEmbedding.conjugate (tauE D τ) ≠ tauE D τ' := by
  intro h
  have e := DFunLike.congr_fun h D.host.sqrtMinusD
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, Formalism.L2.Theta.tauE_sqrtMinusD,
    Formalism.L2.Theta.tauE_sqrtMinusD] at e
  have e2 := congrArg Complex.im e
  simp at e2
  have : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  linarith

theorem mk_tauE_bij (D : D7) : Function.Bijective (fun τ : D.what₂.Tau => InfinitePlace.mk (tauE D τ)) := by
  refine ⟨fun τ τ' h => ?_, fun w => GlobalTheory.CharInfPlace.exists_mk_tauE D w⟩
  rcases InfinitePlace.mk_eq_iff.1 h with e | e
  · exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  · exact absurd e (conjugate_tauE_ne_tauE D τ τ')

theorem mk_tauE_complex (D : D7) (τ : D.what₂.Tau) : ¬ (InfinitePlace.mk (tauE D τ)).IsReal := by
  rw [InfinitePlace.isReal_mk_iff, NumberField.ComplexEmbedding.isReal_iff]
  exact conjugate_tauE_ne_tauE D τ τ

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem inf_eq_mul_normPow : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (χ : Formalism.L2.Host.HChar D.host.E), ChrEq χW χ → ∀ (k : Type) [Field k] (σ : k →+* ℂ), ConjIn D σ → ∀ a : D.host.Eˣ, ∃ y : k, ((χ.inf a : ℂˣ) : ℂ) = σ y * ((|((Algebra.norm ℚ (a : D.host.E) : ℚ) : ℝ)| ^ (-(W.rank : ℝ) / 2) : ℝ) : ℂ) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hvp χ hc k _ σ hσ a
  choose b hb using hvp.1.expW
  obtain ⟨n, hn, hinf⟩ := GlobalTheory.HeckeInfExp.hasInfQ_of_hasInfExp D χW χ _ hc hb
  have hn' : ∀ τ, n τ = 2 * b τ + (W.rank : ℤ) := fun τ => by
    have : (n τ : ℚ) = ((2 * b τ + (W.rank : ℤ) : ℤ) : ℚ) := by rw [hn]; push_cast; ring
    exact_mod_cast this
  have hnorm : ∏ τ, ‖tauE D τ (a : D.host.E)‖ ^ 2 = |((Algebra.norm ℚ (a : D.host.E) : ℚ) : ℝ)| := by
    rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm]
    refine (Fintype.prod_bijective _ (mk_tauE_bij D) _ _ (fun τ => ?_))
    rw [NumberField.InfinitePlace.mult, if_neg (mk_tauE_complex D τ)]
    rfl
  have hA : ∏ τ, (tauE D τ (a : D.host.E) ^ ((b τ : ℤ) + (W.rank : ℤ)) *
      ((starRingEnd ℂ (tauE D τ (a : D.host.E))) ^ (b τ : ℤ))⁻¹) ∈ σ.fieldRange := by
    refine prod_mem fun τ _ => mul_mem (zpow_mem ?_ _) (inv_mem (zpow_mem ?_ _))
    · obtain ⟨y, hy⟩ := hσ (tauE D τ) a
      exact ⟨y, hy⟩
    · obtain ⟨y, hy⟩ := hσ ((starRingEnd ℂ).comp (tauE D τ)) a
      exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hA
  refine ⟨y, ?_⟩
  rw [hinf a, hy, ← hnorm, ← prod_norm_inv_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hn' τ]
  exact phase_zpow_eq _ ((map_ne_zero _).2 a.ne_zero) _ W.rank

end GlobalTheory.LevelSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientFrameChangeOfTriangularFrameChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori GlobalTheory.HeckeFrCompare GlobalTheory.HeckePointLaw

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeBorelChange

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem isLieImg_comb {Ω : Type} [Field Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'} (hψ : IsLinHom ψ) {p m : ℕ}
    {v v' : Fin m → (Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsLieImg p ψ (v j) (v' j))
    (cf : Fin m → Ω) {w w' : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left} (htw : IsTanAt x w) (htw' : IsTanAt x' w')
    (hw : IsCombAt x v cf w) (hw' : IsCombAt x' v' cf w') : IsLieImg p ψ w w' := by
  let A : Fin m → (tEps x ⟶ Xo.univ.t.G) := fun j => Over.homMk (v j) (hv j).1.1
  let B : Fin m → (tEps x' ⟶ Xo.univ.t.G) := fun j => Over.homMk (v' j) (hv j).2.1.1
  let W : tEps x ⟶ Xo.univ.t.G := Over.homMk w htw.1
  let W' : tEps x' ⟶ Xo.univ.t.G := Over.homMk w' htw'.1
  have hAB : ∀ j, scaleAt x' (p : Ω) ≫ B j = tanMap hψ (A j) := fun j => by
    obtain ⟨-, -, a, ha, e⟩ := hv j
    have : a = A j := Over.OverMorphism.ext ha
    subst this
    exact Over.OverMorphism.ext e
  have hW : (List.ofFn fun i => scaleAt x (cf i) ≫ A i).prod = W := (isCombAt_iff A cf W).1 hw
  have hW' : (List.ofFn fun i => scaleAt x' (cf i) ≫ B i).prod = W' := (isCombAt_iff B cf W').1 hw'
  let Lc : (tEps x' ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
    MonoidHom.mk' (fun b => scaleAt x' (p : Ω) ≫ b) fun b b' => MonObj.comp_mul _ _ _
  have key : scaleAt x' (p : Ω) ≫ W' = tanMap hψ W := by
    have e1 : scaleAt x' (p : Ω) ≫ W' = Lc W' := rfl
    rw [e1, ← hW, ← hW', map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    refine congrArg (fun f => (List.ofFn f).prod) (funext fun i => ?_)
    simp only [Function.comp_apply, Lc, MonoidHom.mk'_apply]
    rw [tanMap_scale, ← hAB, ← Category.assoc, ← Category.assoc, scaleAt_comm]
  exact ⟨htw, htw', W, rfl, congrArg (·.left) key⟩

theorem scal_mul'' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one'' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x (1 : S) i = 1 := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem secBC_self {Ω : Type} [CommRing Ω] {x : Sp Ω ⟶ Xo.X} {a : Ω} {s s' : LB.Sec (PPx x)}
    (h : GlobalTheory.Frames.SecBC (RingHom.id Ω) a x x s s') : ∀ i, s'.f i = scal x a i * s.f i := by
  obtain ⟨pm, h₁, h₂, h₃⟩ := h
  have e0 : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by simp [spMap]
  obtain rfl : pm = 𝟙 _ := gx_ext (h₂.trans (by rw [e0]; simp))
    (h₁.trans (Category.id_comp _).symm)
  intro i
  have e : Scheme.Hom.appLE (𝟙 (Gx x)) ((PPx x).U i) ((PPx x).U i) le_rfl = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)
  have := h₃ i le_rfl
  rw [e] at this
  exact this.symm

end SlopeTestRemainingChoices

theorem hkRelFr_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (w z : FrPt Xo c Ω), FrBor t w z → ∀ (C : hkKer (Xo := Xo) P p i Ω z) (z' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω z C z' → ∃ (C₀ : hkKer (Xo := Xo) P p i Ω w) (w' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω w C₀ w' ∧ FrBor t w' z' := by
  intro E _ _ _ H Dw l Xo c P p i hP Ω _ _ _ t w z hb C z' hz
  have hsp : IsSplitOff l P p := hP
  obtain ⟨g, hg0, hgd, hgc⟩ := (GlobalTheory.Frames.frBor_iff_frChg w z t).1 hb
  have hdet : ∀ τ, IsUnit (g τ).det := fun τ =>
    GlobalTheory.Frames.lowerTri_isUnit_det _ (hg0 τ) fun j => by rw [hgd]; exact Units.isUnit _
  have hdet' : ∀ τ, IsUnit ((g τ)⁻¹).det := fun τ => by
    rw [Matrix.det_nonsing_inv]; exact (hdet τ).ringInverse
  obtain ⟨w', hw', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c Ω z' (fun τ => (g τ)⁻¹) (t none)⁻¹ hdet'
  have hdiag : ∀ τ j, (g τ)⁻¹ j j = ((t⁻¹ (some ⟨τ, j⟩) : Ωˣ) : Ω) := fun τ j => by
    have e := GlobalTheory.Frames.lowerTri_mul_diag ((g τ)⁻¹) (g τ) (GlobalTheory.Frames.lowerTri_inv _ (hg0 τ) (hdet τ)) (hg0 τ) j
    rw [Matrix.nonsing_inv_mul _ (hdet τ), Matrix.one_apply_eq, hgd] at e
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_left e.symm
  have hb' : FrBor t⁻¹ z' w' := (GlobalTheory.Frames.frBor_iff_frChg z' w' t⁻¹).2
    ⟨fun τ => (g τ)⁻¹, fun τ => GlobalTheory.Frames.lowerTri_inv _ (hg0 τ) (hdet τ), hdiag, hw'⟩
  have hbw : FrBor t w' z' := by
    simpa using (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c Ω z' w' w').2.2.2 t⁻¹ hb'
  obtain ⟨ψ, hiso, hlie, hth⟩ := (hkPt_iff hsp _ z C.1 z').1 hz
  obtain ⟨hx, hc, hs⟩ := hgc
  obtain ⟨hx', hc', hs'⟩ := hw'
  obtain ⟨zx, zo, zu, ztan, zeig, zbas, zs, zgen⟩ := z
  dsimp only at hx
  subst hx
  obtain ⟨zx', zo', zu', ztan', zeig', zbas', zs', zgen'⟩ := z'
  dsimp only at hx'
  subst hx'
  refine ⟨C, w', (hkPt_iff hsp _ w C.1 w').2 ⟨ψ, hiso, fun τ j => ?_, ?_⟩, hbw⟩
  · have hcomb : IsCombAt w.x (zu τ) ((g τ)⁻¹ j) (w.u τ j) := by
      obtain ⟨a, ha, -⟩ := zbas τ (w.u τ j) (w.tan τ j) (w.eig τ j)
      have h1 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo Ω w.x (w.u τ) (w.tan τ) (zu τ) (g τ).transpose a
        (w.u τ j) (fun k => hc τ k) ha
      have h2 := Formalism.L2.PjFree.isCombAt_single (w.tan τ) j
      have e : (g τ).transpose.mulVec a = Pi.single j 1 :=
        (w.basis τ (w.u τ j) (w.tan τ j) (w.eig τ j)).unique h1 h2
      have ea : a = (g τ)⁻¹ j := by
        have e2 := congrArg ((g τ).transpose⁻¹.mulVec) e
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact hdet τ),
          Matrix.one_mulVec, Matrix.mulVec_single_one] at e2
        rw [e2, ← Matrix.transpose_nonsing_inv]
        ext k
        rfl
      exact ea ▸ ha
    exact isLieImg_comb hiso.2.1 (fun k => hlie τ k) ((g τ)⁻¹ j) (w.tan τ j) (w'.tan τ j) hcomb (hc' τ j)
  · have hth' : GlobalTheory.ThetaTrace.IsThetaTrace Xo.univ.t.G Xo.univ.t.PP ψ p zs zs' := by
      have := hth
      simp only [GlobalTheory.ThetaTrace.hkTr, Equiv.apply_symm_apply] at this
      exact this
    show GlobalTheory.ThetaTrace.IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj w.x w'.x ((conj w.x w'.x).symm ψ)) p w.s w'.s
    rw [Equiv.apply_symm_apply]
    have hs₁ := secBC_self hs
    have hs₂ := secBC_self hs'
    refine GlobalTheory.ThetaTrace.IsThetaTrace.smul hth' (toΓ Ω (((t none)⁻¹ : Ωˣ) : Ω)) (fun k => ?_) (fun k => hs₂ k)
    show w.s.f k = scal w.x (((t none)⁻¹ : Ωˣ) : Ω) k * zs.f k
    rw [hs₁ k, ← _root_.mul_assoc, ← scal_mul'', Units.inv_mul, scal_one'', _root_.one_mul]

end GlobalTheory.HeckeBorelChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJointHighestWeightHarmonicSliceOuterVariables
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.Slice

open MvPolynomial GlobalTheory.Capelli

variable {σ σ₀ : Type} (ι : σ₀ → σ)

abbrev Outer := {v : σ // v ∉ Set.range ι}

noncomputable def sliceVar (v : σ) : MvPolynomial (Outer ι) (MvPolynomial σ₀ ℂ) := by
  classical
  exact if h : v ∈ Set.range ι then C (X h.choose) else X ⟨v, h⟩

noncomputable def slice : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (Outer ι) (MvPolynomial σ₀ ℂ) :=
  aeval (sliceVar ι)

variable {ι}

theorem slice_X_inner (hι : Function.Injective ι) (u : σ₀) : slice ι (X (ι u)) = C (X u) := by
  have h : ι u ∈ Set.range ι := ⟨u, rfl⟩
  simp only [slice, aeval_X, sliceVar, dif_pos h]
  rw [hι h.choose_spec]

theorem slice_X_outer {v : σ} (hv : v ∉ Set.range ι) : slice ι (X v) = X ⟨v, hv⟩ := by
  simp only [slice, aeval_X, sliceVar, dif_neg hv]

theorem slice_C (a : ℂ) : slice ι (C a) = C (C a) := by
  simp [slice, aeval_C, MvPolynomial.algebraMap_apply]

variable (ι)

noncomputable def coefAt (t : Outer ι →₀ ℕ) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ₀ ℂ where
  toFun Q := coeff t (slice ι Q)
  map_add' _ _ := by simp
  map_smul' c Q := by simp [coeff_smul]

variable {ι}

theorem coefAt_X_mul (hι : Function.Injective ι) (t : Outer ι →₀ ℕ) (u : σ₀)
    (Q : MvPolynomial σ ℂ) : coefAt ι t (X (ι u) * Q) = X u * coefAt ι t Q := by
  simp [coefAt, map_mul, slice_X_inner hι, coeff_C_mul]

theorem coefAt_pderiv (hι : Function.Injective ι) (u : σ₀) (Q : MvPolynomial σ ℂ) :
    ∀ t, coefAt ι t (pderiv (ι u) Q) = pderiv u (coefAt ι t Q) := by
  classical
  simp only [coefAt, LinearMap.coe_mk, AddHom.coe_mk]
  induction Q using MvPolynomial.induction_on with
  | C a => intro t; simp only [pderiv_C, map_zero, coeff_zero, slice_C, coeff_C]; split_ifs <;> simp
  | add p q hp hq => intro t; simp [hp, hq]
  | mul_X p v hp =>
    intro t
    by_cases hv : v ∈ Set.range ι
    · obtain ⟨w, rfl⟩ := hv
      by_cases huw : w = u
      · subst huw
        simp [Derivation.leibniz, map_mul, slice_X_inner hι, hp, pderiv_X, coeff_C_mul,
          mul_comm (slice ι p) (C (X w))]
        ring
      · have h1 : ι u ≠ ι w := fun h => huw (hι h).symm
        have h2 : u ≠ w := fun h => huw h.symm
        simp [Derivation.leibniz, map_mul, slice_X_inner hι, hp, pderiv_X,
          Pi.single_apply, h1, h2, coeff_C_mul, mul_comm (slice ι p) (C (X w))]
    · have h1 : ι u ≠ v := fun h => hv ⟨u, h⟩
      simp only [Derivation.leibniz, map_add, map_mul, smul_eq_mul, pderiv_X, Pi.single_apply,
        if_neg h1.symm, mul_zero, zero_add, slice_X_outer hv]
      rw [coeff_X_mul', coeff_mul_X']
      split_ifs
      · rw [hp]
      · simp

theorem coefAt_jointTop (hι : Function.Injective ι) (t : Outer ι →₀ ℕ) {k l N : ℕ}
    (z : Fin k × Fin N → σ₀) (y : Fin l × Fin N → σ₀) (κ : Fin N → ℂ) (α : Fin k → ℂ)
    (β : Fin l → ℂ) (P : MvPolynomial σ ℂ)
    (h : GlobalTheory.CompactHarm.JointTop (ι ∘ z) (ι ∘ y) κ α β P) :
    GlobalTheory.CompactHarm.JointTop z y κ α β (coefAt ι t P) := by
  have hm : ∀ i j, coefAt ι t (mixedOp ℂ (ι ∘ z) (ι ∘ y) i j P) =
      mixedOp ℂ z y i j (coefAt ι t P) := fun i j => by
    simp only [mixedOp_apply, map_sub, map_sum, Function.comp_apply, coefAt_X_mul hι,
      coefAt_pderiv hι]
  have hr : ∀ {K : ℕ} (w : Fin K × Fin N → σ₀) (a b : Fin K),
      coefAt ι t (rowOp ℂ (ι ∘ w) a b P) = rowOp ℂ w a b (coefAt ι t P) := fun w a b => by
    simp only [rowOp_apply, map_sum, Function.comp_apply, coefAt_X_mul hι, coefAt_pderiv hι]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun i j hij => ?_, fun i => ?_, fun c c' hc => ?_, fun c => ?_, fun d d' hd => ?_,
    fun d => ?_, fun c d => ?_⟩
  · rw [← hm, h1 i j hij, map_zero]
  · rw [← hm, h2 i, map_smul]
  · rw [← hr, h3 c c' hc, map_zero]
  · rw [← hr, h4 c, map_smul]
  · rw [← hr, h5 d d' hd, map_zero]
  · rw [← hr, h6 d, map_smul]
  · have := congrArg (coefAt ι t) (h7 c d)
    simpa only [map_sum, Function.comp_apply, coefAt_pderiv hι, map_zero] using this

variable (ι)

noncomputable def unslice : MvPolynomial (Outer ι) (MvPolynomial σ₀ ℂ) →+* MvPolynomial σ ℂ :=
  eval₂Hom (rename ι).toRingHom (fun r => X r.1)

variable {ι}

theorem unslice_slice_X (hι : Function.Injective ι) (v : σ) : unslice ι (slice ι (X v)) = X v := by
  by_cases hv : v ∈ Set.range ι
  · obtain ⟨w, rfl⟩ := hv
    rw [slice_X_inner hι]
    simp only [unslice, coe_eval₂Hom, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
  · rw [slice_X_outer hv]
    simp only [unslice, coe_eval₂Hom, eval₂_X]

theorem unslice_slice (hι : Function.Injective ι) (Q : MvPolynomial σ ℂ) :
    unslice ι (slice ι Q) = Q := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [slice_C]
    simp only [unslice, coe_eval₂Hom, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, hp, unslice_slice_X hι]

theorem slice_decomp (hι : Function.Injective ι) (P : MvPolynomial σ ℂ) :
    P = ∑ t ∈ (slice ι P).support,
      rename ι (coefAt ι t P) * t.prod (fun r e => (X r.1 : MvPolynomial σ ℂ) ^ e) := by
  conv_lhs => rw [← unslice_slice hι P, (slice ι P).as_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [unslice, eval₂_monomial, coefAt]

theorem vars_outer_prod (t : Outer ι →₀ ℕ) :
    ∀ v ∈ (t.prod (fun r e => (X r.1 : MvPolynomial σ ℂ) ^ e)).vars, v ∉ Set.range ι := by
  classical
  intro v hv
  obtain ⟨r, -, hr⟩ := Finset.mem_biUnion.1 (vars_prod _ hv)
  have := vars_pow _ _ hr
  rw [vars_X, Finset.mem_singleton] at this
  exact this ▸ r.2

noncomputable def outerEmb : (Outer ι →₀ ℕ) ↪ (σ →₀ ℕ) :=
  ⟨Finsupp.mapDomain Subtype.val, Finsupp.mapDomain_injective Subtype.val_injective⟩

noncomputable def outerBack (i : σ →₀ ℕ) : Outer ι →₀ ℕ :=
  Finsupp.comapDomain Subtype.val i Subtype.val_injective.injOn

theorem outerBack_emb (t : Outer ι →₀ ℕ) : outerBack (outerEmb t) = t :=
  Finsupp.comapDomain_mapDomain _ Subtype.val_injective t

end GlobalTheory.Slice

open GlobalTheory.Slice in
theorem GlobalTheory.jointTop_slice : ∀ {σ σ₀ : Type} [DecidableEq σ] (ι : σ₀ → σ), Function.Injective ι →
    ∀ {k l N : ℕ} (z : Fin k × Fin N → σ₀) (y : Fin l × Fin N → σ₀) (κ : Fin N → ℂ)
    (α : Fin k → ℂ) (β : Fin l → ℂ) (P : MvPolynomial σ ℂ),
    GlobalTheory.CompactHarm.JointTop (ι ∘ z) (ι ∘ y) κ α β P →
    ∃ (s : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → MvPolynomial σ₀ ℂ) (g : (σ →₀ ℕ) → MvPolynomial σ ℂ),
      P = ∑ i ∈ s, MvPolynomial.rename ι (f i) * g i ∧
      (∀ i ∈ s, GlobalTheory.CompactHarm.JointTop z y κ α β (f i)) ∧
      ∀ i ∈ s, ∀ v ∈ (g i).vars, v ∉ Set.range ι := by
  intro σ σ₀ _ ι hι k l N z y κ α β P hP
  refine ⟨(slice ι P).support.map (outerEmb (ι := ι)), fun i => coefAt ι (outerBack (ι := ι) i) P,
    fun i => (outerBack (ι := ι) i).prod (fun r n => (MvPolynomial.X r.1 : MvPolynomial σ ℂ) ^ n), ?_, ?_, ?_⟩
  · rw [Finset.sum_map]
    simp only [outerBack_emb]
    exact slice_decomp hι P
  · intro i _
    exact coefAt_jointTop hι _ z y κ α β P hP
  · intro i _
    exact vars_outer_prod _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LawsOfSerSide
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs

theorem laws_of_serSide : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → Laws Y.Z.good Y.Z.rd := by
  intro D X E Y hR
  refine ⟨fun i j b => ?_, fun i j b => ?_, fun i j b => ?_, fun i hi j b => Y.Z.rat (hR i hi j b)⟩
  · exact GlobalTheory.SeriesTie.realRd_faithful D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
      (Y.Z.scalar i j b).ne X.unif X.char.models.HW (Y.Z.vec j)
      ((GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)
  · exact GlobalTheory.SeriesTie.actRead_realRd D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
      Y.Z.pin X.unif X.char.models.HW
  · exact Y.Z.heckeRead (GlobalTheory.SeriesTie.HkRat.ratHecke_realRd D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
      Y.Z.pin (X.char.lev.mu0 j) (GlobalTheory.SplitOffS0.main Y.Z.good i _ (Y.Sb i)) Y.H.hL
      (Y.H.hs _ (Nat.le_add_left _ _) j.2) Y.reads)

end GlobalTheory.TwInputs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharactersTypePlacesEqLocalComponentsStatement
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
theorem _root_.GlobalTheory.T.levelCharacters_typePlaces_eq_local_components : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf → ∀ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ, (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) → ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k) (x : (ZMod (D.host.g kv.1))ˣ) (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - u) ∈ (NX.pG D kv).asIdeal → embLL0 D ((τ (j.1 + 1) kv x : (↥D.LL0)ˣ) : ↥D.LL0) = (((cf.mu0 j).locK (NX.pG D kv) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TwInputs.tau_eq_locK | exact GlobalTheory.TwInputs.tau_eq_locK | (intros; apply GlobalTheory.TwInputs.tau_eq_locK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfPublishedStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_of_published : LocalLanglandsExists → LocalConverseGL → DepthZeroCuspidalLL → DepthZeroInduction → BrauerDegreeZero → ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → LocalLanglandsGL := by
  first | exact @GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein | exact GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein | (intros; apply GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein <;> assumption)
end

