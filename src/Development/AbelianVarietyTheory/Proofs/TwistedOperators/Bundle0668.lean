import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0449
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0569
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0661
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0660
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0468
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0662
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0369
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0666
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiLevelOneCosetAtGoodPlace

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPairedKernelFlatMapWeilTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.KerContFB

set_option maxHeartbeats 400000 in

theorem kerFB_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → Continuous fun q : GA D B.V × GA D J.W₀ × GA D B.A => contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ))) (omz (q.2.1, 1) Φ₀) 0 := by
  intro D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.JacMean.xLast_lin B.d B.o B.line
  have hn : ∀ t, ψ t * star (ψ t) = 1 := fun t => by
    have h1 : ‖ψ t‖ = 1 := s.weil₀.std.1.2.1 t
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  have hpsi : psiBes ψ B.d 1 (vecB B.o B.ζ) 1 = 1 :=
    (GlobalTheory.T.flag_unipotent_bessel_character_laws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1).2.1 _ 1 (one_mem _)
  have hfl : ∀ Ψ, flFB s Ψ = flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x) 0 Ψ := fun Ψ => by
    simp only [flFB, flatS, hxe]
  have heq : ∀ h h₀ h₁, s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ)) =
      flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x) 0 (s.om (J.d.emb0 h₀, embA B.d B.o h₁ * h) Φ) := by
    intro h h₀ h₁
    have e := GlobalTheory.T.jacobiToBesselFlatMap_equivariant D ψ σ J B s (s.om (1, h) Φ) (s.weil.om_pres _ Φ hΦ) h₀ 1 (one_mem _) h₁
    rw [hpsi, star_one, one_smul, one_mul] at e
    rw [← e, hfl]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hth : ∀ h, IsThetaFunO ψ J.W₀ B.V₀ (flFB s (s.om (1, h) Φ)) := fun h => by
    rw [hfl]
    exact (GlobalTheory.Unf.Flat.flatLaw D ψ s.weil.std J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU x hx 0 _
      (s.weil.om_pres _ Φ hΦ)).2
  set K : Mx D B.L.rank J.W₀.rank → GA D B.V × GA D J.W₀ × GA D B.A → ℂ := fun w q =>
    s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ)) (B.o.jB ⬝ w) * star (omz (q.2.1, 1) Φ₀ w) with hK
  have hP : ∀ q : GA D B.V × GA D J.W₀ × GA D B.A, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (q.2.1, B.o.emb (q.2.2, 1))
      (flFB s (s.om (1, q.1) Φ))) (omz (q.2.1, 1) Φ₀) 0 = ∫ w in vL.𝓕, K w q ∂vL.μ := fun q => by
    simp only [contractT, thPair, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, hK]
  have hc : Continuous (Function.uncurry K) := by
    have h1 := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x hx Φ hΦ
    have hJ := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ _ _ χ χz omz homz Φ₀ hΦ₀
    have hK' : Function.uncurry K = fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x) 0
          (s.om (J.d.emb0 p.2.2.1, embA B.d B.o p.2.2.2 * p.2.1) Φ) (B.o.jB ⬝ p.1) * star (omz (p.2.2.1, 1) Φ₀ p.1) := by
      funext p
      simp only [Function.uncurry, hK, heq]
    rw [hK']
    have ha : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) => p.2.2.1 :=
      continuous_fst.comp (continuous_snd.comp continuous_snd)
    have hb : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) => p.2.2.2 :=
      continuous_snd.comp (continuous_snd.comp continuous_snd)
    have hh : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) => p.2.1 :=
      continuous_fst.comp continuous_snd
    have hA : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) => embA B.d B.o p.2.2.2 := by
      simp only [embA_apply]
      exact B.d.continuous_embed.comp (B.o.continuous_emb.comp (hb.prodMk continuous_const))
    have h2 : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        (((J.d.emb0 p.2.2.1, embA B.d B.o p.2.2.2 * p.2.1) : GA D J.W × GA D B.V), ((0 : Mx D J.W₀.rank σ),
          (B.o.jB ⬝ p.1 : WO J.W₀ B.V₀))) :=
      ((J.d.continuous_embed.comp ha).prodMk (hA.mul hh)).prodMk
        (continuous_const.prodMk (continuous_const.matrix_mul continuous_fst))
    have h3 : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x) 0
          (s.om (J.d.emb0 p.2.2.1, embA B.d B.o p.2.2.2 * p.2.1) Φ) (B.o.jB ⬝ p.1) := by
      convert h1.comp h2 using 2
      simp only [Function.comp_apply]
    have h4 : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        omz (p.2.2.1, 1) Φ₀ p.1 :=
      hJ.comp (f := fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        (((p.2.2.1, 1) : GA D J.W₀ × GA D B.L), (p.1 : WO J.W₀ B.L))) ((ha.prodMk continuous_const).prodMk continuous_fst)
    exact h3.mul h4.star
  have hper : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ w q, K (γ + w) q = K w q := by
    rintro _ ⟨γ, rfl⟩ w q
    have e1 := (s.weil₀.om_pres (q.2.1, B.o.emb (q.2.2, 1)) _ (hth q.1)).quasi (B.o.iB * γ) (B.o.jB ⬝ w)
    have e2 := (homz.om_pres (q.2.1, 1) Φ₀ hΦ₀).quasi γ w
    rw [ratW_eq, rat_mul] at e1
    rw [ratW_eq] at e2
    have e3 : symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ w) = symplOH J.W₀ B.L (rat γ) w := by
      rw [B.o.symplOH_resT]
      simp only [OrthDec.resT_apply, cancel₂ B.o.pA_jB, cancel₂ B.o.pB_jB, Matrix.zero_mul, Matrix.one_mul,
        symplOH_zero_left, zero_add]
    change s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ)) (B.o.jB ⬝ (rat γ + w)) *
        star (omz (q.2.1, 1) Φ₀ (rat γ + w)) =
      s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ)) (B.o.jB ⬝ w) * star (omz (q.2.1, 1) Φ₀ w)
    rw [Matrix.mul_add, e2]
    refine (congrArg (· * _) e1).trans ?_
    change ψ (-symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ w)) * _ * _ = _
    rw [e3, star_mul', mul_mul_mul_comm, hn, one_mul]
  obtain ⟨-, hcont, -, -⟩ := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D _ _ vL _ K hc hper
  have : (fun q : GA D B.V × GA D J.W₀ × GA D B.A => contractT B.o J.W₀ vL.μ vL.𝓕
      (s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ))) (omz (q.2.1, 1) Φ₀) 0) =
      fun q => ∫ w in vL.𝓕, K w q ∂vL.μ := funext hP
  rw [this]; exact hcont

end GlobalTheory.KerContFB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteApprox
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section
namespace GlobalTheory.CuspKFinDecomp

theorem avg_lev : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ) (U : Subgroup (GA D N.V)), (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), ∀ k ∈ U, k ∈ GfC N.V → ∀ g, GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ (g * k) = GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ g := by
  intro D θ hθ N ψ U hψ τ e k hk hkf g
  unfold GlobalTheory.SeriesToClosure.avg
  congr 1
  funext k'
  rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc,
    hψ k hk hkf]

theorem cuspAvg_kfin_decomp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, φ (g * k) = φ g) → ∀ (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ), (∀ τ, GlobalTheory.TypeSum.KFinFun (N.M.ε τ) (e τ)) → ∀ (l : List D.what₂.Tau), (∀ τ, τ ∈ l) → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → SmT N.M), (∀ j, F j ∈ N.Cusp θ) ∧ (∀ j, ∀ k ∈ U, k ∈ GfC N.V → ∀ g, F j (v j) (g * k) = F j (v j) g) ∧ GlobalTheory.CuspApproxAll.avgList θ N e l φ = ∑ j, F j (v j) := by
  intro D θ hθ hP N φ hφ U hU hlev e he l hl
  have key : ∀ l' : List D.what₂.Tau, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N (GlobalTheory.CuspApproxAll.avgList θ N e l' φ) ∧
      (∀ k ∈ U, k ∈ GfC N.V → ∀ g, GlobalTheory.CuspApproxAll.avgList θ N e l' φ (g * k) = GlobalTheory.CuspApproxAll.avgList θ N e l' φ g) ∧
      ∀ τ ∈ l', GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.CuspApproxAll.avgList θ N e l' φ) := by
    intro l'
    induction l' with
    | nil => exact ⟨hφ, hlev, fun τ h => absurd h List.not_mem_nil⟩
    | cons τ l' ih =>
      rw [GlobalTheory.CuspApproxAll.avgList_cons]
      refine ⟨GlobalTheory.T.cusp_form_avg_series_closure D θ hθ hP N _ ih.1 τ (e τ) (he τ), avg_lev D θ hθ N _ U ih.2.1 τ (e τ), fun τ' hτ' => ?_⟩
      rcases List.mem_cons.1 hτ' with rfl | h
      · exact GlobalTheory.T.averaged_automorphic_function_K_finite D θ hθ N _ ih.1.1 τ' (e τ') (he τ')
      · exact GlobalTheory.T.average_preserves_K_finiteness D θ hθ N _ ih.1.1 τ' τ (e τ) (he τ) (ih.2.2 τ' h)
  obtain ⟨hc, hlv, hk⟩ := key l
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D N.V
    (Measure.haar : Measure (GA D N.V)) inferInstance
  obtain ⟨n, T₀, u, hT₀, hsum⟩ := GlobalTheory.T.cusp_form_K_finite_decomposition D θ hθ hP N _ hc U hU hlv (fun τ => hk τ (hl τ))
    (Measure.haar : Measure (GA D N.V)) 𝓕 inferInstance h𝓕
  have hext := fun j => (GlobalTheory.GKExt.extExists hP.harishChandraModules hP.casselmanWallach D θ hθ N.V N.S N.M
    {k | k ∈ U ∧ k ∈ GfC N.V} 1 (Measure.haar : Measure (GA D N.V)) 𝓕 inferInstance h𝓕 (T₀ j) (hT₀ j)).exists
  choose T hT using hext
  have hsm : ∀ τ (w : N.M.H τ), w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → w ∈ N.M.sm τ := fun τ w hw =>
    (GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff N.M τ w).2 ((GlobalTheory.TypeSum.std_of_isDS hP.harishChandraModules (N.M.ds τ)).2.2.1 w hw)
  refine ⟨n, fun j => PiTensorProduct.lift (T j),
    fun j => PiTensorProduct.tprod ℂ (fun τ => (⟨(u j τ : N.M.H τ), hsm τ _ (u j τ).2⟩ : N.M.sm τ)),
    fun j => ?_, fun j k hk hkf g => ?_, ?_⟩
  · exact N.multT_le_cusp θ {k | k ∈ U ∧ k ∈ GfC N.V} 1
      (Submodule.mem_map_of_mem (Submodule.subset_span (hT j).1))
  · rw [PiTensorProduct.lift.tprod]
    have := (hT j).1.lev (fun τ => (⟨(u j τ : N.M.H τ), hsm τ _ (u j τ).2⟩ : N.M.sm τ)) k ⟨hk, hkf⟩ g
    simpa using this
  · rw [hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PiTensorProduct.lift.tprod]
    exact ((hT j).2 _ (u j) fun τ => rfl).symm

end GlobalTheory.CuspKFinDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConstSetIntegralHaarFundamentalDomainsUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.HaarFundDom

theorem setIntegral_eq_const_mul : ∀ {D : D7} {V : HSp D} (ν₁ ν₂ : Measure (GA D V)) (fd₁ fd₂ : Set (GA D V)), ν₁.IsHaarMeasure → ν₂.IsHaarMeasure → IsFundamentalDomain (GQ V) fd₁ ν₁ → IsFundamentalDomain (GQ V) fd₂ ν₂ → ∃ c : ℂ, ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → (IntegrableOn f fd₁ ν₁ ↔ IntegrableOn f fd₂ ν₂) ∧ ∫ g in fd₁, f g ∂ν₁ = c * ∫ g in fd₂, f g ∂ν₂ := by
  intro D V ν₁ ν₂ fd₁ fd₂ h₁ h₂ hfd₁ hfd₂
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hc := Measure.isMulLeftInvariant_eq_smul ν₁ ν₂
  set c₀ : NNReal := Measure.haarScalarFactor ν₁ ν₂ with hc₀
  have hpos : 0 < c₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure ν₁ ν₂
  have hc0 : (c₀ : ENNReal) ≠ 0 := by exact_mod_cast hpos.ne'
  have hctop : (c₀ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsm : (c₀ • ν₂ : Measure (GA D V)) = (c₀ : ENNReal) • ν₂ := rfl
  have hfd₂' : IsFundamentalDomain (GQ V) fd₂ ν₁ := hfd₂.mono (by rw [hc, hsm]; exact Measure.smul_absolutelyContinuous)
  refine ⟨(c₀ : ℂ), fun f hf => ?_⟩
  have hf' : ∀ (g : GQ V) (x : GA D V), f (g • x) = f x := fun g x => hf g g.2 x
  constructor
  · rw [hfd₁.integrableOn_iff hfd₂' hf', hc, hsm, IntegrableOn, Measure.restrict_smul, integrable_smul_measure hc0 hctop]
    rfl
  · rw [hfd₁.setIntegral_eq hfd₂' hf', hc, hsm, Measure.restrict_smul, integral_smul_measure]
    simp [Complex.real_smul]

end GlobalTheory.HaarFundDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteElementConjRowLevelCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.SeeConj.exists_conj_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) ∧ IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp _hMod
  obtain ⟨ψ0, hψ0, -, π, -, hmem, hchi⟩ := hGrp.levels
  obtain ⟨β₃, hfr₃, hD1⟩ := GlobalTheory.T.exists_frame_conjugate_level_symmetricLevel R F X h hIs hGrp ψ0 hψ0
  obtain ⟨β₂, hfr₂, hD2⟩ := GlobalTheory.T.exists_frame_reordering_levelData R.toLevCh (R.levR F true) (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0) π hmem hchi β₃ hfr₃
  obtain ⟨t₀, ht₀, hfr₀⟩ := GlobalTheory.T.exists_finiteUnitary_selfDualFrame_to_baseLatticeFrame (Yc D 0) (R.βY 0) (R.ΛY 0) _ (hIs.βY 0 (by have := D.R.two_le_m; omega))
  obtain ⟨u, hu, hfru, hred⟩ := GlobalTheory.T.exists_unitary_matching_frames_at_nonconjugate_places (Yc D 0) R.Pg (GlobalTheory.T.levelPlaces_not_isConjPlace_realDat R F hIs hGrp) _ β₂ hfr₀ hfr₂
  have hfe : finE (Yc D 0) (u * t₀) * R.βY 0 = finE (Yc D 0) u * (finE (Yc D 0) t₀ * R.βY 0) := by
    rw [map_mul, mul_assoc]
  refine ⟨u * t₀, mul_mem hu ht₀, ?_, by rw [hfe]; exact hfru⟩
  intro (k : GA D (Yc D 0))
  have hA := GlobalTheory.T.levelSubgroup_conj_finite_moves_frame (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) (u * t₀) (mul_mem hu ht₀) k
  rw [hfe] at hA
  have hC := GlobalTheory.T.levS_iff_and_levChi_eq_of_redFn_eq (Yc D 0) (finE (Yc D 0) u * (finE (Yc D 0) t₀ * R.βY 0)) β₂ _ (R.dat0 (R.levR F true)) hfru hfr₂
    (fun PP hPP x => hred PP hPP x) (fun PP hPP => absurd hPP (Finset.notMem_empty _)) ((u * t₀) * k * (u * t₀)⁻¹)
  have h2 := hD2 ((u * t₀) * k * (u * t₀)⁻¹)
  have h1 := hD1 ((u * t₀) * k * (u * t₀)⁻¹)
  have hm : ∀ hk : k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)), (u * t₀) * k * (u * t₀)⁻¹ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) :=
    fun hk => h2.1.1 (hC.1.1 (hA.1.1 hk))
  have key : (k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) ↔ (u * t₀) * k * (u * t₀)⁻¹ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) ∧
      (k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) → star (X.chi2 ((iotaX X h).toMulEquiv ((u * t₀) * k * (u * t₀)⁻¹)).2) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k) :=
    ⟨hA.1.trans (hC.1.trans (h2.1.trans h1.1.symm)), fun hk => by rw [h1.2 (hm hk), ← h2.2, ← hC.2, hA.2]⟩
  have e : ((u * t₀)⁻¹⁻¹ : GA D (D.sp.Y 0)) = u * t₀ := inv_inv (G := GA D (D.sp.Y 0)) _
  rw [e]
  exact key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsFinOf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def locAt (B : Frames G) (t : T) (w : Pl D.host.E) (j : ℕ) (hj : j ≤ D.R.m) :
    GA D (G.V (.grid D.R.m j)) →* GL (Fin ((locGrid G t w).rank (D.R.m, j))) (Kw w) :=
  (inBasis (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (B.β D.R.m j) w).comp (Lev.finE _)

theorem locAt_inf (B : Frames G) (t : T) (w : Pl D.host.E) (j : ℕ) (hj : j ≤ D.R.m) {a : GA D (G.V (.grid D.R.m j))}
    (ha : a ∈ GinfC _) : locAt B t w j hj a = 1 := by
  have h : Lev.finE (G.V (.grid D.R.m j)) a = 1 := by
    simp only [Lev.finE, GinfC, MonoidHom.mem_ker] at ha ⊢
    rw [MonoidHom.comp_apply, ha, map_one]
  simp only [locAt, MonoidHom.comp_apply, h, map_one]

theorem exists_isFinOf (V : HSp D) (g : GA D V) : ∃ b, GlobalTheory.RowVal.IsFinOf g b := by
  obtain ⟨-, -, -, ⟨e, he⟩, -⟩ := GlobalTheory.AdelicSplit.adelic_split D V
  obtain ⟨p, rfl⟩ := e.surjective g
  exact ⟨p.2, p.2.2, p.1, p.1.2, (he p).symm⟩

theorem elt_succ (t : T) (w : Pl D.host.E) (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w))
    (i : Fin ((locGrid G t w).m - 2)) :
    (repsAt G t w).elt β ((locGrid G t w).m, i.1 + 1) = (repsAt G t w).rep i (β i) := by
  simp only [Reps.elt]
  rw [onColumn_apply]
  simp only [dif_pos i.2]

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem loc_rep (B : Frames G) (t : T) (s : ℤˣ) (β : CosFam G t) (w : locPl G t) (i : Fin ((locGrid G t w.1).m - 2))
    (hj : i.1 + 1 ≤ D.R.m) (r : GA D (G.V (.grid D.R.m (i.1 + 1))))
    (ρ : GL (Fin ((locGrid G t w.1).rank (D.R.m, i.1 + 1))) (Kw w.1)) (hρ : ρ = (repsAt G t w.1).rep i (β w i))
    (hr : (inBasis (rank_vertex G t w.1 (X := (D.R.m, i.1 + 1)) ⟨le_rfl, hj⟩) (B.β D.R.m (i.1 + 1)) w.1)
      (Lev.finE (G.V (.grid D.R.m (i.1 + 1))) r) =
      GlobalTheory.RowVal.sgnAt G t s w.1 (i.1 + 1) * (repsAt G t w.1).elt (β w) (D.R.m, i.1 + 1)) :
    locAt B t w.1 (i.1 + 1) hj r = GlobalTheory.RowVal.sgnAt G t s w.1 (i.1 + 1) * ρ := by
  rw [hρ, ← elt_succ]
  exact hr

theorem mk_eq_of {Gp : Type} [Group Gp] (H K : Subgroup Gp) {A A' S X Y ρ ρ' : Gp}
    (e : A' * (S * ρ') = X * (A * (S * ρ)) * Y) (hN : (A' * S)⁻¹ * X * (A * S) ∈ H) (hY : Y ∈ K) :
    DoubleCoset.mk H K ρ = DoubleCoset.mk H K ρ' := by
  rw [DoubleCoset.eq]
  refine ⟨_, hN, Y, hY, ?_⟩
  rw [show (A' * S)⁻¹ * X * (A * S) * ρ * Y = (A' * S)⁻¹ * (X * (A * (S * ρ)) * Y) by group, ← e]
  group

theorem idx_le {j : ℕ} (h : j ∈ GlobalTheory.RowVal.idx D) : 1 ≤ j ∧ j + 2 ≤ D.R.m := by
  simp only [GlobalTheory.RowVal.idx, List.mem_range'_1] at h
  omega

end GlobalTheory.RowRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeForMatchedFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_for_matched_frames : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁,
  ∃ (L : GlobalTheory.FinPl.Lat (G.V (.grid i j))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    L.FG ∧ Submodule.span D.host.E (L : Set (Fin (G.V (.grid i j)).rank → D.host.E)) = ⊤ ∧
    ∀ κ, GlobalTheory.FinPl.InK (G.V (.grid i j)) L (fun v => v ∉ S) κ → ∀ u, kerSmall W Θ' g g₁ (u * κ) = kerSmall W Θ' g g₁ u := by
  first | exact @GlobalTheory.SmallKerInv.kerSmall_inv | exact GlobalTheory.SmallKerInv.kerSmall_inv | (intros; apply GlobalTheory.SmallKerInv.kerSmall_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLineOperatorPolynomial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DerPol

theorem pairDer (hP : GlobalTheory.FunPr.Hypotheses₂) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (F := F) E w) (χX χW : Chr F E) (om : Rep σ X W) (hcm : IsCMExt F E σ) (hψ : IsStd ψ)
    (hW : M.IsWeil ψ χX χW om) :
    ∀ γ ∈ Lines σ W, ∃ δ : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f ∈ M.Pol ψ τ,
      δ f ∈ M.Pol ψ τ ∧ ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro γ hγ
  obtain ⟨m, u, v, c, c₀, hat, hQ⟩ := GlobalTheory.T.weil_line_action_sum hP M ψ χX χW om hcm hψ hW γ hγ
  choose Du hDu using fun i => GlobalTheory.T.exists_archSchwartz_derivative_heisenbergLine M ψ hψ (u i) (hat i).1
  choose Dv hDv using fun i => GlobalTheory.T.exists_archSchwartz_derivative_heisenbergLine M ψ hψ (v i) (hat i).2
  have closed : ∀ w, At (evI F) w → ∀ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ w) f (D f)) → ∀ f ∈ M.Pol ψ τ, D f ∈ M.Pol ψ τ := by
    intro w hw D hD f hf
    rw [Model.Pol, Submodule.mem_sInf] at hf ⊢
    intro N hN
    exact hN.2 w hw f (hf N hN) (D f) (hD f)
  refine ⟨∑ i, c i • (Du i ∘ₗ Dv i) + c₀ • LinearMap.id, fun f hf => ⟨?_, ?_⟩⟩
  · simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.id_apply]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ hf)
    exact closed _ (hat i).1 _ (hDu i) _ (closed _ (hat i).2 _ (hDv i) _ hf)
  · intro r hr x
    choose F₁ hF₁ using fun t : ℝ => GlobalTheory.T.weil_action_unitary_compact hP M ψ χX χW om hcm hψ hW (γ (Multiplicative.ofAdd t)) (hγ.2 _) f
    have hd := hQ f (fun i => Dv i f) (fun i => Du i (Dv i f)) (fun i => hDv i f) (fun i => hDu i _) F₁ hF₁
      (fun i => evI F (x i))
    have e : (fun t => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) x) =
        fun t => F₁ t (fun i => evI F (x i)) * r x := by
      funext t; rw [hF₁ t r hr]; rfl
    rw [e]
    refine (hd.mul_const (r x)).congr_deriv ?_
    show _ = ((∑ i, c i • (Du i ∘ₗ Dv i) + c₀ • LinearMap.id : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) f) (fun i => evI F (x i)) * r x
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
      SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul]
    congr 2
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, SchwartzMap.add_apply, ih]; simp

theorem exists_lieDer_model' : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')), ∀ f ∈ G.M'.Pol B.ψ B.emb,
      δ f ∈ G.M'.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ
  exact pairDer hP G.M' B.ψ B.emb X.α (X.α / X.β) om' hT.base.cm hT.base.std hT.weil' γ hγ

end GlobalTheory.DerPol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalOperatorThetaQuotientFinitePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localOperator_thetaQuotient_finitePlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a a' : ℕ)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ hv ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.W (GlobalTheory.AdelicU.evFin F v),
    ∃ T : Module.End ℂ (Rf.Pi v),
      (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, hv)) φ φ₁ → Rf.p v φ₁ = T (Rf.p v φ)) ∧
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, hv)) φ φ₁ → Rf.p' v φ₁ = T (Rf.p' v φ) := by
  first | exact @GlobalTheory.LocalDescent.exists_localOp | exact GlobalTheory.LocalDescent.exists_localOp | (intros; apply GlobalTheory.LocalDescent.exists_localOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiLevelOneCosetAtGoodPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiLevel_oneCoset_at_goodPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ A L : HSp D) (σ : ℕ) (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ) (o : OrthDec W₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (p : Pieces V₀ W W₀ (σ + 1) σ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (LA : Lat A) (LL : Lat L) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xLast dW (vecB o ζ)) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → IsSelfDualC A LA → IsSelfDualC L LL → OrthAt o LW₀ LA LL v → ∀ h ∈ grpAt W (· = v), Cond dW p (xLast dW (vecB o ζ)) 0 ψ (· = v) h → CosetAt W (Rgrp W (xLast dW (vecB o ζ))) LW v h := by
  first | exact @GlobalTheory.AscFin.OneCosetFJ.oneCoset_good | exact GlobalTheory.AscFin.OneCosetFJ.oneCoset_good | (intros; apply GlobalTheory.AscFin.OneCosetFJ.oneCoset_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselPairedKernelHeightBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiToBessel_pairedKernel_heightBound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∃ (C : ℝ) (a : ℕ), ∀ h h₀ h₁, ‖contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0‖ ≤ C * (height J.W₀ h₀ * height B.A h₁ * height B.V h) ^ a := by
  first | exact @GlobalTheory.PairKerBound.kernel_bound | exact GlobalTheory.PairKerBound.kernel_bound | (intros; apply GlobalTheory.PairKerBound.kernel_bound <;> assumption)
end

