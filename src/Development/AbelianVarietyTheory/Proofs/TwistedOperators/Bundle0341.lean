import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIntegralFourierBesselBasePointEqPairin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0102
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0314
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0326
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0322
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0342
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceCompactTorusClassesCompactWeylCosets
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelIsometryHalfLatticeVolumeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelBasePointMulMemRationalMatrices
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.HeisL

variable {D : D7}

theorem mixedModelBasePointWithLast_mul {σ : ℕ} (B : BesL D σ) (S : HSp D) (b : Mx D (σ + 1) S.rank) :
    xLast B.d (vecB B.o B.ζ) ⬝ b = B.d.incX S (Matrix.of fun i j => b (Fin.castSucc i) j) +
      B.d.inc0 S ((B.o.resT S).symm (0, zEll B.L (σ + 1) B.ζ ⬝ b)) := by
  rw [HypDec.incX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, GlobalTheory.Unf.FB.zEll_mul_eq,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, OrthDec.jB, ← ratV_mulVec]
  ext k j
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, xLast, vecMulVec_apply, vecB]

theorem symplOH_x0L {σ : ℕ} (B : BesL D σ) (S : HSp D) (b b' : Mx D (σ + 1) S.rank) :
    symplOH S B.V (xLast B.d (vecB B.o B.ζ) ⬝ b) (xLast B.d (vecB B.o B.ζ) ⬝ b') =
      symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ b) (zEll B.L (σ + 1) B.ζ ⬝ b') := by
  rw [mixedModelBasePointWithLast_mul, mixedModelBasePointWithLast_mul]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.symplOH_incX_incX,
    HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, HypDec.wittDecomp_sympl_inclAnisotropic_inclAnisotropic, zero_add]
  rw [symplOH_skew S B.V (B.d.incX S _) (B.d.inc0 S _), HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, neg_zero, zero_add,
    OrthDec.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

theorem zlL_mem_ratMx {σ : ℕ} (B : BesL D σ) : zEll B.L (σ + 1) B.ζ ∈ ratMx D B.L.rank (σ + 1) := by
  refine ⟨vecMulVec B.ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩
  refine Matrix.ext fun k i => ?_
  change incA D (B.ζ k * (if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0)) =
    incA D (B.ζ k) * (if i.1 + 1 = σ + 1 then (1 : AE D) else 0)
  split_ifs
  · rw [mul_one, mul_one]
  · rw [mul_zero, mul_zero, map_zero]

theorem mixedModelBasePoint_mul_mem_rationalMatrices {σ : ℕ} (B : BesL D σ) (S : HSp D) {γ : Mx D (σ + 1) S.rank} (hγ : γ ∈ ratMx D (σ + 1) S.rank) :
    xLast B.d (vecB B.o B.ζ) ⬝ γ ∈ ratMx D B.V.rank S.rank := by
  rw [mixedModelBasePointWithLast_mul]
  obtain ⟨g, rfl⟩ := hγ
  refine add_mem (ratMx_mul (rat_mem _) ⟨Matrix.of fun i j => g (Fin.castSucc i) j, rfl⟩)
    (ratMx_mul (rat_mem _) ?_)
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  exact ratMx_mul (rat_mem _) (ratMx_mul (zlL_mem_ratMx B) (rat_mem _))

end GlobalTheory.Asc.HeisL

namespace GlobalTheory.Asc

open GlobalTheory.Asc.HeisL GlobalTheory.Unf.FB

set_option maxHeartbeats 2000000 in

theorem heis_baseL : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : HSp D) (B : BesL D σ) (vB : VolM D (σ + 1) S.rank) (vT : VolM D σ S.rank) (vL : VolM D B.L.rank S.rank) (f : WO S B.V → ℂ) (y : WO S B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ S B.V f → GlobalTheory.Unf.FB.Quasi ψ S B.L y → (∫ b in vB.𝓕, f (xLast B.d (vecB B.o B.ζ) ⬝ b) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) ∂vB.μ = contractT B.o S vL.μ vL.𝓕 (B.d.mixT S ψ vT.μ vT.𝓕 f 0) y 0) ∧ ∫⁻ v in vL.𝓕, ‖B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v))‖ₑ ∂vL.μ ≤ ∫⁻ b in vB.𝓕, ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vB.μ := by
  intro D ψ hψ σ S B vB vT vL f y hf hy
  have hψn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have hL1 : B.L.rank = 1 := B.line.1
  let i₀ : Fin B.L.rank := ⟨0, by omega⟩
  have h1 : ∀ i : Fin B.L.rank, i = i₀ := fun i => Fin.ext (by have := i.2; simp only [i₀]; omega)
  have h0 : B.ζ i₀ ≠ 0 := by
    intro h
    apply B.line.2
    have : B.ζ = 0 := funext fun i => by rw [h1 i, h]; rfl
    rw [this]; simp
  set e := splitLine (σ := σ) (n := S.rank) B.L B.ζ i₀ h1 h0 with he_def
  obtain ⟨he, hes⟩ := continuous_splitLine (σ := σ) (n := S.rank) B.L B.ζ i₀ h1 h0
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D (σ + 1) S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D σ S.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D B.L.rank S.rank
  haveI : BorelSpace (Mx D (σ + 1) S.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D σ S.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D B.L.rank S.rank) := ⟨rfl⟩
  haveI : Countable (ratMx D (σ + 1) S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := vT.covol.1
  haveI := vL.covol.1
  haveI := vB.covol.1

  have hx : ∀ b : Mx D (σ + 1) S.rank, xLast B.d (vecB B.o B.ζ) ⬝ b = B.d.incX S (e b).1 + B.d.inc0 S ((B.o.resT S).symm (0, (e b).2)) := fun b => mixedModelBasePointWithLast_mul B S b

  set P := vT.μ.prod vL.μ with hP
  let me : Mx D (σ + 1) S.rank ≃ᵐ Mx D σ S.rank × Mx D B.L.rank S.rank :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving me (P.map e.symm) P := MeasurePreserving.symm me.symm ⟨me.symm.measurable, rfl⟩
  have hmp' : MeasurePreserving e (P.map e.symm) P := hmp
  have hν : (P.map e.symm).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map P e.symm hes (by simpa using he)
  have hPF : IsAddFundamentalDomain ((ratMx D σ S.rank).prod (ratMx D B.L.rank S.rank)) (vT.𝓕 ×ˢ vL.𝓕) P :=
    GlobalTheory.CoordUnfold.isAddFundamentalDomain_prod vT.covol.2.1 vL.covol.2.1
  have hF' : IsAddFundamentalDomain (ratMx D (σ + 1) S.rank) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) (P.map e.symm) := by
    let g : (ratMx D σ S.rank).prod (ratMx D B.L.rank S.rank) → ratMx D (σ + 1) S.rank :=
      fun p => ⟨e.symm p, splitLine_symm_mem B.L B.ζ i₀ h1 h0 p.2⟩
    have hg : Function.Bijective g := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, splitLine_mem B.L B.ζ i₀ h1 h0 x.2⟩, Subtype.ext (by simp [g])⟩
    refine hPF.preimage_of_equiv hmp'.quasiMeasurePreserving hg ?_
    intro p x
    simp [g, AddSubgroup.vadd_def]
  have hv : (P.map e.symm) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) = 1 := by
    refine (hmp.measure_preimage_equiv _).trans ?_
    rw [Measure.prod_prod, vT.covol.2.2, vL.covol.2.2, one_mul]
  have hcov : IsCovolOne (ratMx D (σ + 1) S.rank) (P.map e.symm) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) := ⟨hν, hF', hv⟩
  have hμeq : P.map e.symm = vB.μ := covolOne_measure_eq vB.covol hcov

  have hfx : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b,
      f (xLast B.d (vecB B.o B.ζ) ⬝ (γ + b)) = ψ (-(symplOH S B.V (xLast B.d (vecB B.o B.ζ) ⬝ γ) (xLast B.d (vecB B.o B.ζ) ⬝ b))) * f (xLast B.d (vecB B.o B.ζ) ⬝ b) := by
    intro γ hγ b
    obtain ⟨δ, hδ⟩ := mixedModelBasePoint_mul_mem_rationalMatrices B S hγ
    have e1 := hf.1 δ (xLast B.d (vecB B.o B.ζ) ⬝ b)
    rw [show ratW B.V S δ = xLast B.d (vecB B.o B.ζ) ⬝ γ from hδ] at e1
    rw [Matrix.mul_add, e1]
  have hyz : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b,
      y (zEll B.L (σ + 1) B.ζ ⬝ (γ + b)) = ψ (-(symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b))) * y (zEll B.L (σ + 1) B.ζ ⬝ b) := by
    intro γ hγ b
    obtain ⟨δ, hδ⟩ := ratMx_mul (zlL_mem_ratMx B) hγ
    have e1 := hy.1 δ (zEll B.L (σ + 1) B.ζ ⬝ b)
    rw [show ratW B.L S δ = zEll B.L (σ + 1) B.ζ ⬝ γ from hδ] at e1
    rw [Matrix.mul_add, e1]
  have hunit : ∀ a, ψ a * star (ψ a) = 1 := fun a => by
    rw [← starRingEnd_apply, RCLike.mul_conj, hψn]; simp
  set s := vT.𝓕 ×ˢ vL.𝓕 with hs
  set G : Mx D (σ + 1) S.rank → ℂ := fun b => f (xLast B.d (vecB B.o B.ζ) ⬝ b) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) with hG
  have hGper : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b, G (γ + b) = G b := by
    intro γ hγ b
    simp only [hG]
    rw [hfx γ hγ b, hyz γ hγ b, symplOH_x0L, star_mul]
    calc ψ (-symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b)) * f (xLast B.d (vecB B.o B.ζ) ⬝ b) *
          (star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) * star (ψ (-symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b))))
        = (ψ (-symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b)) * star (ψ (-symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b)))) *
          (f (xLast B.d (vecB B.o B.ζ) ⬝ b) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b))) := by ring
      _ = _ := by rw [hunit, one_mul]
  have hx0c : Continuous fun b : Mx D (σ + 1) S.rank => xLast B.d (vecB B.o B.ζ) ⬝ b := continuous_const.matrix_mul continuous_id
  have hzlc : Continuous fun b : Mx D (σ + 1) S.rank => zEll B.L (σ + 1) B.ζ ⬝ b := continuous_const.matrix_mul continuous_id
  have hGc : Continuous G := (hf.2.comp hx0c).mul (continuous_star.comp (hy.2.comp hzlc))
  set H : Mx D σ S.rank × Mx D B.L.rank S.rank → ℂ :=
    fun p => f (B.d.incX S p.1 + B.d.inc0 S ((B.o.resT S).symm (0, p.2))) * star (y p.2) with hH
  have hGH : ∀ p, G (e.symm p) = H p := by
    intro p
    simp only [hG, hH]
    rw [hx (e.symm p), AddEquiv.apply_symm_apply]
    congr 3
    exact congrArg Prod.snd (e.apply_symm_apply p)
  have hmix : ∀ w₀, B.d.mixT S ψ vT.μ vT.𝓕 f 0 w₀ = ∫ ξ in vT.𝓕, f (B.d.incX S ξ + B.d.inc0 S w₀) ∂vT.μ := by
    intro w₀
    change ∫ ξ in vT.𝓕, heisO ψ S B.V (B.d.incX S ξ) (heisO ψ S B.V (B.d.incAdj S 0)
      (heisO ψ S B.V (B.d.inc0 S w₀) f)) 0 ∂vT.μ = _
    congr 1
    funext ξ
    rw [HypDec.integrandT_eq, map_zero, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  have hGi : IntegrableOn G (e ⁻¹' s) (P.map e.symm) := covolOne_integrableOn hcov G hGc hGper
  have hHi : Integrable H ((vT.μ.restrict vT.𝓕).prod (vL.μ.restrict vL.𝓕)) := by
    rw [Measure.prod_restrict]
    have h2 := (hmp.integrableOn_comp_preimage me.measurableEmbedding (f := H) (s := s)).1 (by
      have : H ∘ me = G := funext fun b => by
        rw [Function.comp_apply, ← hGH]
        exact congrArg G (e.symm_apply_apply b)
      rw [this]; exact hGi)
    exact h2
  refine ⟨?_, ?_⟩
  · calc ∫ b in vB.𝓕, f (xLast B.d (vecB B.o B.ζ) ⬝ b) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) ∂vB.μ = ∫ b in vB.𝓕, G b ∂vB.μ := rfl
      _ = ∫ b in e ⁻¹' s, G b ∂(P.map e.symm) := (covolOne_integral_eq vB.covol hcov G hGper).symm
      _ = ∫ p in s, H p ∂P := by
        have h3 := hmp.setIntegral_preimage_emb me.measurableEmbedding H s
        rw [← h3]
        refine congrArg (fun F : Mx D (σ + 1) S.rank → ℂ => ∫ b in e ⁻¹' s, F b ∂(P.map e.symm)) (funext fun b => ?_)
        rw [← hGH]
        exact (congrArg G (e.symm_apply_apply b)).symm
      _ = ∫ v in vL.𝓕, ∫ ξ in vT.𝓕, H (ξ, v) ∂vT.μ ∂vL.μ := by
        rw [hP, ← Measure.prod_restrict]
        exact integral_prod_symm H hHi
      _ = _ := by
        change _ = ∫ v in vL.𝓕, B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v)) * star (y v) ∂vL.μ
        congr 1
        funext v
        rw [hmix, ← integral_mul_const]
  · have hψe : ∀ a, ‖ψ a‖ₑ = 1 := fun a => by rw [← ofReal_norm_eq_enorm, hψn, ENNReal.ofReal_one]
    set K : Mx D σ S.rank × Mx D B.L.rank S.rank → ENNReal :=
      fun p => ‖f (B.d.incX S p.1 + B.d.inc0 S ((B.o.resT S).symm (0, p.2)))‖ₑ with hK
    have hKc : Continuous K := by
      refine (hf.2.comp ?_).enorm
      simp only [HypDec.incX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, OrthDec.resT_symm_apply]
      exact (continuous_const.matrix_mul continuous_fst).add (continuous_const.matrix_mul
        (continuous_const.add (continuous_const.matrix_mul continuous_snd)))
    have hKe : ∀ b, K (e b) = ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ := fun b => by rw [hK, hx b]
    have hper' : ∀ (γ : ratMx D (σ + 1) S.rank) (b : Mx D (σ + 1) S.rank),
        ‖f (xLast B.d (vecB B.o B.ζ) ⬝ (γ +ᵥ b))‖ₑ = ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ := by
      intro γ b
      rw [AddSubgroup.vadd_def, vadd_eq_add, hfx γ γ.2 b, enorm_mul, hψe, one_mul]
    have hF'' : IsAddFundamentalDomain (ratMx D (σ + 1) S.rank) (e ⁻¹' s) vB.μ := hμeq ▸ hF'
    calc ∫⁻ v in vL.𝓕, ‖B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v))‖ₑ ∂vL.μ
        ≤ ∫⁻ v in vL.𝓕, ∫⁻ ξ in vT.𝓕, K (ξ, v) ∂vT.μ ∂vL.μ := by
          refine lintegral_mono fun v => ?_
          rw [hmix]
          exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p in s, K p ∂P := by
        rw [hP, ← Measure.prod_restrict, lintegral_prod_symm _ hKc.measurable.aemeasurable]
      _ = ∫⁻ b in e ⁻¹' s, K (e b) ∂(P.map e.symm) :=
        (hmp'.setLIntegral_comp_preimage_emb me.measurableEmbedding K s).symm
      _ = ∫⁻ b in e ⁻¹' s, ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vB.μ := by
        rw [hμeq]; congr 1; funext b; exact hKe b
      _ = ∫⁻ b in vB.𝓕, ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vB.μ := hF''.setLIntegral_eq vB.covol.2.1 _ hper'

end GlobalTheory.Asc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormCuspFormLeOfShortLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ShortLineCusp

theorem sum_sqrt_le (ι : Type) [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, Real.sqrt (a i) ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, a i) := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => Real.sqrt (a i))
  simp only [one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_mul,
    Real.sq_sqrt (ha _)] at h1
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  simpa [Real.sq_sqrt (ha _)] using h1

theorem sum_sqrt_add_le : ∀ (ι : Type) [Fintype ι] (a b : ι → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) → ∑ i, (Real.sqrt (a i) + Real.sqrt (b i)) ≤ Real.sqrt (Fintype.card ι) * (Real.sqrt (∑ i, a i) + Real.sqrt (∑ i, b i)) := by
  intro ι _ a b ha hb
  rw [Finset.sum_add_distrib, mul_add]
  exact add_le_add (sum_sqrt_le ι a ha) (sum_sqrt_le ι b hb)

theorem finrank_eq_card_and_rd : ∀ D : D7, Module.finrank ℚ D.host.F = Fintype.card D.what₂.Tau ∧ |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (2 * (Module.finrank ℚ D.host.F : ℝ))) = rdisc D := by
  intro D
  haveI := D.sp.cm.totReal
  refine ⟨?_, ?_⟩
  · rw [Fintype.card_congr (Formalism.L2.Host.tauPl D), ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  · unfold rdisc
    rw [← Module.finrank_mul_finrank ℚ D.host.F D.host.E, D.sp.cm.deg2]
    congr 1
    push_cast
    ring

theorem least_nonneg : ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), 0 ≤ GlobalTheory.Count.least I x := by
  intro I x
  unfold GlobalTheory.Count.least Formalism.HN.leastSize
  apply Real.sInf_nonneg
  rintro t ⟨R, -, -, rfl⟩
  unfold Formalism.HN.size Formalism.HN.ht Formalism.F.covol
  apply Real.rpow_nonneg
  apply mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _))
  split_ifs <;> positivity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem norm_le_of_not_long : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∀ (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ V.rank → (∀ τ, min (Finset.univ.filter fun a => A.ε τ a = true).card (Finset.univ.filter fun a => A.ε τ a = false).card ≤ q) → ∀ φ : GA D V → ℂ, IsAutFun V φ → IsCuspFun V φ → (∀ k ∈ Lev.levA V (congLev D.sp.cm V.gram Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})), ∀ x, φ (x * k) = φ x) → ∀ c : ℝ, 0 ≤ c → Lip θ A φ c → ∀ (x : GA D V) (s : ℝ), 0 < s → s ≤ 1 / 2 → ¬ Long θ A Λ x s → ‖φ x‖ ≤ c * ((V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D * (2 * s) ^ ((1 : ℝ) / q)) := by
  intro D θ hθ V A Λ hΛ g q hg hq hn hrk φ hφ hcusp hlev c hc hlip x s hs hs2 hlong
  obtain ⟨fr, hfrΛ, hfr⟩ := GlobalTheory.T.exists_instanceFrames_of_diagonalFrame_selfDual D V A Λ hΛ
  subst hfrΛ
  obtain ⟨hfF, hrdE⟩ := finrank_eq_card_and_rd D
  have hfI : (Formalism.IndefR.Eqv.UI.instV fr).f = Fintype.card D.what₂.Tau := hfF
  have hrdI : (Formalism.IndefR.Eqv.UI.instV fr).rd = rdisc D := hrdE
  set x0 := (Formalism.IndefR.Eqv.UI.brg fr).symm x with hx0
  have hbx : Formalism.IndefR.Eqv.UI.brg fr x0 = x := by simp [hx0]
  have hl0 : 0 ≤ GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0 := least_nonneg _ x0
  have hlt : GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0 < s := by
    by_contra hge
    push_neg at hge
    apply hlong
    intro 𝔪 h𝔪 w hw hw0
    have hL := GlobalTheory.T.adelicPointRationalLattice_unitaryModelIso_eq D V fr x0
    rw [hbx] at hL
    rw [hL] at hw
    have h1 := GlobalTheory.T.leastSize_pow_mul_sqrt_absNorm_le_prod_norms (Formalism.IndefR.Eqv.UI.instV fr) x0 𝔪 h𝔪 w hw hw0
    rw [GlobalTheory.T.rationalVectorNorm_adelicPoint_twoModels_eq D θ hθ V A fr (fun τ => (hfr τ).2) x0 w, hbx, hfI] at h1
    exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.le hge _) (Real.sqrt_nonneg _)) h1
  have hrkI : ∀ v, GlobalTheory.Count.rkR ((Formalism.IndefR.Eqv.UI.instV fr).ε v) ≤ q := by
    intro (v : InfinitePlace D.host.F)
    have h := (hfr ((Formalism.L2.Host.tauPl D).symm v)).1
    have e : (Formalism.L2.Host.tauPl D) ((Formalism.L2.Host.tauPl D).symm v) = v := Equiv.apply_symm_apply _ _
    rw [e] at h
    show GlobalTheory.Count.rkR (fr.ε v) ≤ q
    rw [h]
    exact hrk _
  obtain ⟨W, hW, hmv⟩ := GlobalTheory.T.automorphicPoint_exists_isotropic_reduction_of_small_size (Formalism.IndefR.Eqv.UI.instV fr) x0 g q hg hq hn hrkI (hlt.trans_le hs2)
  obtain ⟨hGQ, -, hN⟩ := GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr
  obtain ⟨r, C₀, hC₀, hNI⟩ := hN W hW
  apply GlobalTheory.CuspGeo.norm_le_of_unipRad_variation D V φ hφ hcusp r C₀ hC₀ x
  intro m hm
  have hm' : (Formalism.IndefR.Eqv.UI.brg fr).symm m ∈ (Formalism.IndefR.Eqv.UI.instV fr).NA W :=
    hNI _ (by simpa using hm)
  obtain ⟨γ, hγ, k, hk, u, Av, Z, hAZ, hu, heq, hbd⟩ := hmv _ hm'
  have hmx : m * x = Formalism.IndefR.Eqv.UI.brg fr γ * (x * Formalism.IndefR.Eqv.UI.brg fr (u, 1)) * Formalism.IndefR.Eqv.UI.brg fr (1, k) := by
    have h2 := congrArg (Formalism.IndefR.Eqv.UI.brg fr) heq
    have h3 : ((u, k) : (Formalism.IndefR.Eqv.UI.instV fr).GA) = (u, 1) * (1, k) := by simp
    rw [h3] at h2
    simp only [map_mul, hbx, ContinuousMulEquiv.apply_symm_apply] at h2
    rw [h2]; group
  rw [hmx, hlev _ (GlobalTheory.T.principalCongruence_mem_latticeCongruenceLevel D V fr g hg k hk), hφ.left _ ((hGQ γ).2 hγ)]
  have h6 := GlobalTheory.T.lipschitz_bound_real_unipotent_action D θ hθ V A fr (fun τ => (hfr τ).2) φ c hc hlip u Av Z hAZ hu x
  have h7 := sum_sqrt_add_le (InfinitePlace D.host.F) (fun v => Formalism.REAL.hs (Av v)) (fun v => Formalism.REAL.hs (Z v))
    (fun v => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (fun v => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hcard : Fintype.card (InfinitePlace D.host.F) = Fintype.card D.what₂.Tau :=
    Fintype.card_congr (Formalism.L2.Host.tauPl D).symm
  rw [hcard] at h7
  rw [hfI, hrdI] at hbd
  have hL : (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) ≤ (2 * s) ^ ((1 : ℝ) / q) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hL0 : 0 ≤ (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) := by positivity
  have hrd0 : 0 ≤ rdisc D := by unfold rdisc; positivity
  have hN : Real.sqrt (Fintype.card D.what₂.Tau) * Real.sqrt (Fintype.card D.what₂.Tau) = Fintype.card D.what₂.Tau :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hP : 0 ≤ (V.rank : ℝ) ^ 2 * (Fintype.card D.what₂.Tau : ℝ) * (g : ℝ) * rdisc D := by positivity
  have hbd' : Real.sqrt (Fintype.card D.what₂.Tau) *
      (Real.sqrt (∑ v, Formalism.REAL.hs (Av v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v))) ≤
      (V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D * (2 * s) ^ ((1 : ℝ) / q) := by
    calc _ ≤ Real.sqrt (Fintype.card D.what₂.Tau) * ((V.rank : ℝ) ^ 2 * Real.sqrt (Fintype.card D.what₂.Tau) * g * rdisc D *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) / 4) :=
          mul_le_mul_of_nonneg_left hbd (Real.sqrt_nonneg _)
      _ = (Real.sqrt (Fintype.card D.what₂.Tau) * Real.sqrt (Fintype.card D.what₂.Tau)) * ((V.rank : ℝ) ^ 2 * g * rdisc D *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q)) / 4 := by ring
      _ = ((V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D) *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) / 4 := by rw [hN]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hL hP, mul_nonneg hP hL0]
  calc _ ≤ _ := h6
    _ ≤ c * (Real.sqrt (Fintype.card D.what₂.Tau) *
      (Real.sqrt (∑ v, Formalism.REAL.hs (Av v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v)))) := mul_le_mul_of_nonneg_left h7 hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hbd' hc

end GlobalTheory.ShortLineCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormDerivCharacterSymplecticPairingRealLineStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_deriv_character_symplecticPairing_realLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : WO S T), ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ = 2 * Real.pi * |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ z (compAt θ τ w)| := by
  first | exact @GlobalTheory.LatSum.norm_deriv_psi_symplO_lineAt | exact GlobalTheory.LatSum.norm_deriv_psi_symplO_lineAt | (intros; apply GlobalTheory.LatSum.norm_deriv_psi_symplO_lineAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormRightConvolutionLeAdelicHeightPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_rightConvolution_le_adelic_height_pow : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Ω : Set (GA D V)}, IsCompact Ω → (∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A)) → ∃ (A : ℕ) (C : ℝ), ∀ f' : GA D V → ℂ, Continuous f' → tsupport f' ⊆ Ω → ∀ M : ℝ, (∀ y, ‖f' y‖ ≤ M) → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (g : GA D V), ‖GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g‖ ≤ C * M * ‖F‖ * GlobalTheory.Grow.height V g ^ A := by
  first | exact @GlobalTheory.ConvGrowth.norm_convR_le_height | exact GlobalTheory.ConvGrowth.norm_convR_le_height | (intros; apply GlobalTheory.ConvGrowth.norm_convR_le_height <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicMatrixCoordinatesTriangular
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

open scoped TensorProduct

namespace GlobalTheory.IwasawaTri

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (coordR extSub act)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {V : HSpace E} {R : Type} [CommRing R] [Algebra F R]

theorem act_mem_of_mem_span {S : Set V.V} {A : Submodule E V.V} {g : HA R hc.sig V.gram}
    (h : ∀ x ∈ S, act hc V g (coordR V R x) ∈ extSub (F := F) V R A) {x : V.V}
    (hx : x ∈ Submodule.span E S) : act hc V g (coordR V R x) ∈ extSub (F := F) V R A := by
  let f : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] Fin V.rank → R ⊗[F] E :=
    (HA.mat R hc.sig V.gram g).1.mulVecLin
  change f (coordR V R x) ∈ _
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [show coordR V R 0 = 0 from funext fun _ => by simp [coordR], map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 =>
    rw [show coordR V R (x + y) = coordR V R x + coordR V R y from funext fun _ => by simp [coordR], map_add]
    exact add_mem h1 h2
  | smul a x _ h1 =>
    rw [show coordR V R (a • x) = inclR (F := F) R a • coordR V R x from funext fun _ => by simp [coordR], map_smul]
    exact Submodule.smul_mem _ _ h1

end Gen

theorem mem_pLoc_flag0_of_mul_eq_upper : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (v : HeightOneSpectrum (𝓞 D.host.F)) (p : GLoc D.sp.cm.sig V.gram v) (b : Matrix (Fin (wittIndex V)) (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), b.BlockTriangular id → (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram p).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * b → p ∈ PLoc Φ.flag0 v := by
  intro D V Φ v p b hb h
  refine IsoFlag.mem_par.2 fun i => GlobalTheory.Cusp.mem_parab.2 fun x hx => ?_
  have hgen : ∀ j : Fin (wittIndex V), j.val < i.val →
      act D.sp.cm V p (coordR V (Fv D.host.F v) (Φ.e j)) ∈ extSub (F := D.host.F) V (Fv D.host.F v) (Φ.flag0.X i) := by
    intro j hj
    have hcol : act D.sp.cm V p (coordR V (Fv D.host.F v) (Φ.e j)) =
        ∑ k, b k j • coordR V (Fv D.host.F v) (Φ.e k) := by
      funext a
      have := congrFun (congrFun h a) j
      simp only [Matrix.mul_apply, Matrix.of_apply] at this
      simp only [act, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hcol]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : j < k
    · rw [hb hk, zero_smul]; exact zero_mem _
    · exact Submodule.smul_mem _ _ (GlobalTheory.Cusp.coordR_mem V _
        (Submodule.subset_span ⟨k, show k.val < i.val from Nat.lt_of_le_of_lt (Fin.le_def.1 (not_lt.1 hk)) hj, rfl⟩))
  exact act_mem_of_mem_span (S := Φ.e '' {j | j.val < i.val}) (fun _ ⟨j, hj, e⟩ => e ▸ hgen j hj) hx

end GlobalTheory.IwasawaTri
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceCompactTorusClassesCompactWeylCosetsStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_place_compact_torus_classes_compactWeyl_cosets : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau), CompactSpace (Tor P (placeOf D ρ).Completion) → ∀ WK : Subgroup (Equiv.Perm (Fin V.rank)), (∀ w, w ∈ WK ↔ w ∈ GlobalTheory.HCChar.compactWeyl (M.ε ρ)) → ∃ (T : Finset (Equiv.Perm (Fin V.rank))) (b : XSet P (placeOf D ρ).Completion V.gram ≃ T), Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin V.rank)))⁻¹ * (p.1 : Equiv.Perm (Fin V.rank))) ∧ ∀ (q : XSet P (placeOf D ρ).Completion V.gram) (γ : GArch D.sp.cm.sig V.gram (placeOf D ρ)), HasCls P (placeOf D ρ).Completion V.gram γ q.1 → ∃ g, frameMat M ρ (g * γ * g⁻¹) = Matrix.diagonal fun i => cxRoots (embOverOf D ρ).1 P ((b q : Equiv.Perm (Fin V.rank))⁻¹ i) := by
  first | exact @GlobalTheory.TrEll.RealClasses.real_classes | exact GlobalTheory.TrEll.RealClasses.real_classes | (intros; apply GlobalTheory.TrEll.RealClasses.real_classes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelIsometryHalfLatticeVolumeOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerModel_halfLatticeVolume_mul_inner_eq_inner : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (a : AE D), IsSplitIdem D a → ∀ (m n : ℕ) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a (latO S T ΛS ΛT fun _ => True) κ → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n) (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t}) ≠ 0 ∧ GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n) (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t}) ≠ ⊤ ∧ ∀ Φ₁ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), ∀ Φ₂ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), ((GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n) (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t})).toReal : ℂ) * ipO μ 𝓕 (Tm (pull a κ Φ₁)) (Tm (pull a κ Φ₂)) = GlobalTheory.SplitWeil.ip ν Φ₁ Φ₂ := by
  first | exact @GlobalTheory.PlaceIsometry.placeModel_isometry | exact GlobalTheory.PlaceIsometry.placeModel_isometry | (intros; apply GlobalTheory.PlaceIsometry.placeModel_isometry <;> assumption)
end

