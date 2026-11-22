import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0269
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MajorantExistsAndWittDecomposition
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section

namespace GlobalTheory.Core.Rk.WittDec

variable {D : D7}

theorem isoFrame_le {W : HSp D} {r : ℕ} {C : Matrix (Fin W.rank) (Fin r) D.host.E} (h : IsIsoFrame W C) :
    r ≤ W.rank := by
  have := h.2.1.fintype_card_le_finrank
  simpa using this

theorem isoFrame_extend {W W₀ : HSp D} {r s : ℕ} (d : HypDec W W₀ r)
    {C₀ : Matrix (Fin W₀.rank) (Fin s) D.host.E} (hC₀ : IsIsoFrame W₀ C₀) :
    ∃ C : Matrix (Fin W.rank) (Fin (r + s)) D.host.E, IsIsoFrame W C := by
  classical
  set M : Matrix (Fin W.rank) (Fin r ⊕ Fin s) D.host.E := Matrix.fromCols d.e (d.i₀ * C₀) with hM
  have hG : (HSpace.gram W)ᴴ = HSpace.gram W := GlobalTheory.MixModel.gram_conjTranspose W
  have hi₀e : d.eᴴ * HSpace.gram W * d.i₀ = 0 := by
    have h := congrArg Matrix.conjTranspose d.i₀e
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  have he'i₀ : d.e'ᴴ * HSpace.gram W * d.i₀ = 0 := by
    have h := congrArg Matrix.conjTranspose d.i₀e'
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  have hC₀iso : C₀ᴴ * HSpace.gram W₀ * C₀ = 0 := hC₀.2.2
  have hiso : Mᴴ * HSpace.gram W * M = 0 := by
    rw [hM, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols]
    have h1 : d.eᴴ * HSpace.gram W * d.e = 0 := d.ee
    have h2 : d.eᴴ * HSpace.gram W * (d.i₀ * C₀) = 0 := by rw [← Matrix.mul_assoc, hi₀e, Matrix.zero_mul]
    have h3 : (d.i₀ * C₀)ᴴ * HSpace.gram W * d.e = 0 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.i₀e,
        Matrix.mul_zero]
    have h4 : (d.i₀ * C₀)ᴴ * HSpace.gram W * (d.i₀ * C₀) = 0 := by
      rw [Matrix.conjTranspose_mul, show C₀ᴴ * d.i₀ᴴ * HSpace.gram W * (d.i₀ * C₀) =
        C₀ᴴ * (d.i₀ᴴ * HSpace.gram W * d.i₀) * C₀ by simp only [Matrix.mul_assoc], d.iso, hC₀iso]
    rw [h1, h2, h3, h4, Matrix.fromBlocks_zero]
  have hker : ∀ v, M *ᵥ v = 0 → v = 0 := by
    intro v hv
    rw [hM, Matrix.fromCols_mulVec] at hv
    have ha : v ∘ Sum.inl = 0 := by
      have h := congrArg (fun x => (d.e'ᴴ * HSpace.gram W) *ᵥ x) hv
      simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h
      rwa [d.e'e, ← Matrix.mul_assoc, he'i₀, Matrix.zero_mul, Matrix.zero_mulVec, add_zero,
        Matrix.one_mulVec] at h
    have hb' : d.i₀ *ᵥ (C₀ *ᵥ (v ∘ Sum.inr)) = 0 := by
      rw [ha, Matrix.mulVec_zero, zero_add] at hv
      rw [Matrix.mulVec_mulVec]; exact hv
    have hb'' : HSpace.gram W₀ *ᵥ (C₀ *ᵥ (v ∘ Sum.inr)) = 0 := by
      rw [← d.iso, ← Matrix.mulVec_mulVec, hb', Matrix.mulVec_zero]
    have hc : C₀ *ᵥ (v ∘ Sum.inr) = 0 := Matrix.eq_zero_of_mulVec_eq_zero (gram_det_ne W₀) hb''
    have hinj₀ : Function.Injective C₀.mulVec := Matrix.mulVec_injective_iff.2 hC₀.2.1
    have hb : v ∘ Sum.inr = 0 := hinj₀ (by rw [hc, Matrix.mulVec_zero])
    funext x
    cases x with
    | inl i => exact congrFun ha i
    | inr j => exact congrFun hb j
  refine ⟨M.submatrix id finSumFinEquiv.symm, ?_, ?_, ?_⟩
  · have := hC₀.1; omega
  · apply Matrix.mulVec_injective_iff.1
    intro v w h
    have hsub : M.submatrix id finSumFinEquiv.symm *ᵥ (v - w) = 0 := by
      rw [Matrix.mulVec_sub, h, sub_self]
    rw [Matrix.submatrix_mulVec_equiv] at hsub
    have h0 := hker _ (by simpa using hsub)
    have h1 : v - w = 0 := by
      funext i
      have := congrFun h0 (finSumFinEquiv.symm i)
      simpa using this
    exact sub_eq_zero.1 h1
  · show (M.submatrix id finSumFinEquiv.symm)ᴴ * HSpace.gram W * M.submatrix id finSumFinEquiv.symm = 0
    refine Matrix.ext fun i j => ?_
    exact congrFun (congrFun hiso (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)

theorem aniso_or_hypDec (W : HSp D) :
    IsAniso W ∨ ∃ (W₀ : HSp D) (r' : ℕ) (_ : HypDec W W₀ r'), IsAniso W₀ ∧ 0 < r' := by
  classical
  by_cases hA : IsAniso W
  · exact Or.inl hA
  right
  have hex : ∃ r, ∃ C : Matrix (Fin W.rank) (Fin r) D.host.E, IsIsoFrame W C := by
    by_contra h
    push_neg at h
    exact hA fun r C => h r C
  obtain ⟨r₁, C₁, hC₁⟩ := hex
  let P : ℕ → Prop := fun r => ∃ C : Matrix (Fin W.rank) (Fin r) D.host.E, IsIsoFrame W C
  have hPr : P (Nat.findGreatest P W.rank) := Nat.findGreatest_spec (isoFrame_le hC₁) ⟨C₁, hC₁⟩
  have hmax : ∀ s, P s → s ≤ Nat.findGreatest P W.rank := fun s hs =>
    Nat.le_findGreatest (isoFrame_le hs.choose_spec) hs
  obtain ⟨C, hC⟩ := hPr
  obtain ⟨W₀, ⟨hrk, ι, hι, C', hC', horth⟩, -⟩ :=
    GlobalTheory.WittLow.wittLowEx D W (Nat.findGreatest P W.rank) ⟨C, hC.2.1, hC.2.2⟩
  have hpos : 0 < Nat.findGreatest P W.rank := hC.1
  have hG : (HSpace.gram W)ᴴ = HSpace.gram W := GlobalTheory.MixModel.gram_conjTranspose W
  have hsplit : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W₀ C' (frameMat W W₀ ι) := by
    refine ⟨⟨hpos, hC'.1, hC'.2⟩, GlobalTheory.AutFunCounterexample.gram_pull W W₀ ι hι, ?_, by omega⟩
    show C'ᴴ * HSpace.gram W * frameMat W W₀ ι = 0
    have h : (frameMat W W₀ ι)ᴴ * HSpace.gram W * C' = 0 := horth
    have h2 := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h2
  obtain ⟨d, -, -, -⟩ := GlobalTheory.WittSect.exists_hypDec_mem_NI D W W₀ _ C' _ hsplit
  refine ⟨W₀, _, d, fun s C₀ hC₀ => ?_, hpos⟩
  obtain ⟨C₂, hC₂⟩ := isoFrame_extend d hC₀
  have h1 := hmax _ ⟨C₂, hC₂⟩
  have h2 := hC₀.1
  omega

theorem maj_and_witt : ∀ (D : D7) (W : HSp D), HSpace.SigOK W →
    (∃ b : GL (Fin W.rank) (AE D), IsMaj W b) ∧
      (IsAniso W ∨ ∃ (W₀ : HSp D) (r' : ℕ) (_ : HypDec W W₀ r'), IsAniso W₀ ∧ 0 < r') :=
  fun _ W _ => ⟨GlobalTheory.Doubling.exists_isMaj W, aniso_or_hypDec W⟩

end GlobalTheory.Core.Rk.WittDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MaximalCompactSortedFrameActsThroughModelCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RealData

theorem isKC_comm_Jpq {p q : ℕ} {b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hb : IsKC b) :
    b * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * b := by
  ext a c
  rcases a with i | i <;> rcases c with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
  · rw [hb (Sum.inl i) (Sum.inr j) (by simp [sameBlock]), neg_zero]
  · rw [hb (Sum.inr i) (Sum.inl j) (by simp [sameBlock]), neg_zero]

theorem conj_mem_Kset {n p q : ℕ} (ε : Fin n → Bool) (e : Fin n ≃ Fin p ⊕ Fin q)
    (hJ : (Formalism.UG.Jpq p q).submatrix e e = Formalism.REAL.Jm ε) (fr g : Matrix (Fin n) (Fin n) ℂ) (hfr : IsUnit fr)
    (hg : gᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * g = frᴴ * Formalism.REAL.Jm ε * fr)
    (b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hb : IsKC b)
    (hbA : b * fr.submatrix e.symm id = fr.submatrix e.symm id * g) :
    fr * g * fr⁻¹ ∈ Formalism.REAL.Kset ε := by
  have hdet : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det _).1 hfr
  have hinv : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet

  set X := b.submatrix e e with hX
  have hXfr : X * fr = fr * g := by
    have h1 := congrArg (fun N => N.submatrix e id) hbA
    rw [Matrix.submatrix_mul _ _ _ _ _ e.bijective, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id] at h1
    simpa [Matrix.submatrix_submatrix] using h1
  have hXe : fr * g * fr⁻¹ = X := by
    rw [← hXfr, Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [hXe]
  have hcomm : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X := by
    rw [← hJ, hX, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective,
      isKC_comm_Jpq hb]

  have hiso : Xᴴ * Formalism.REAL.Jm ε * X = Formalism.REAL.Jm ε := by
    have hgX : g = fr⁻¹ * X * fr := by
      rw [Matrix.mul_assoc, hXfr, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    have hinvH : (fr⁻¹)ᴴ * frᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
    have key : X = fr * g * fr⁻¹ := hXe.symm
    calc Xᴴ * Formalism.REAL.Jm ε * X
        = (fr⁻¹)ᴴ * (gᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * g) * fr⁻¹ := by
          rw [key]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (fr⁻¹)ᴴ * frᴴ * Formalism.REAL.Jm ε * (fr * fr⁻¹) := by
          rw [hg]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hinvH, hinv, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, hcomm⟩
  rw [Matrix.mem_unitaryGroup_iff']
  change Xᴴ * X = 1
  calc Xᴴ * X = Xᴴ * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * X := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    _ = Xᴴ * Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε := by
        rw [Matrix.mul_assoc (Xᴴ * Formalism.REAL.Jm ε) X, hcomm]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hiso, Formalism.REAL.Jm_mul_self]

theorem conj_mem_Kset_of_mem_Kinf : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (hV : V.SigOK) (k : GA D V), IsInfFam θ → k ∈ GlobalTheory.Cusp.Kinf θ V (GlobalTheory.ChainOnto.RealData.sortedFrame M hV) → ∀ τ, M.fr τ * infMat D.sp.cm.sig V.gram (θ τ) k * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) := by
  intro D θ V S M hV k hθ hk τ
  obtain ⟨-, hkτ⟩ := GlobalTheory.Cusp.mem_Kinf.1 hk
  obtain ⟨b, hb, hbA⟩ := hkτ τ
  have hU := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ
  have hU' : (infMat D.sp.cm.sig V.gram (θ τ) k)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) *
      infMat D.sp.cm.sig V.gram (θ τ) k = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by
    rw [M.fr_gram τ]; exact hU
  exact conj_mem_Kset (M.ε τ) (signEquiv (M.ε τ) (card_true M hV τ) (card_false M hV τ))
    (Jpq_submatrix _ _) (M.fr τ) _ (M.fr_unit τ) hU' b hb hbA

end GlobalTheory.ChainOnto.RealData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHyperspecialSubgroupAtPlaceIffLocalStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

noncomputable section

namespace GlobalTheory.HypDict

theorem mem_hyp_iff_embV : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ (V : HSp D) (g : GA D V), g ∈ hyp V w ↔ ∃ k ∈ Kv V v, g = embV V v k := by
  intro D v w hw V g
  obtain ⟨e, f, hP⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 w
  rw [GlobalTheory.LevOp.mem_hyp hP, GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem V hP hw g, GlobalTheory.AdelicU.KsphC_eq]
  constructor
  · rintro ⟨hk, k, rfl⟩
    refine ⟨k, ?_, rfl⟩
    have := (GlobalTheory.AdelicU.mem_levelOff.1 hk).2.2 v (Finset.notMem_empty v)
    simpa using this
  · rintro ⟨k, hk, rfl⟩
    exact ⟨GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk, k, rfl⟩

end GlobalTheory.HypDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMultiplicitySpaceLevelOfKFiniteTensorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), (∀ κ ∈ J, κ ∈ GfC V) → ∀ F ∈ MultT θ M ∅ 1, (∀ w ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), ∀ κ ∈ J, ∀ g, F w (g * κ) = χ κ * F w g) → F ∈ MultT θ M J χ := by
  first | exact @GlobalTheory.KFiniteLevel.mem_multT_of_kfin | exact GlobalTheory.KFiniteLevel.mem_multT_of_kfin | (intros; apply GlobalTheory.KFiniteLevel.mem_multT_of_kfin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemWittStabilizerOfKeepsIsotropicRealPlaces
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

noncomputable section

namespace GlobalTheory.Core.Rk.IwGlob

open GlobalTheory.MixModel
open scoped TensorProduct

theorem tens_prod_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] {z z' : (A × B) ⊗[F] E}
    (a : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z')
    (b : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z') : z = z' := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz z, hz z', a, b]

theorem adTens_ext {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {z z' : AF F ⊗[F] E}
    (h1 : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.compInf F E w z = GlobalTheory.AdelicU.compInf F E w z')
    (h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z') : z = z' := by
  refine tens_prod_ext (A := Ainf F) (B := Af F) (GlobalTheory.AutFunCompare.infTens_ext fun w => ?_) h2
  have e : ∀ y : AF F ⊗[F] E, Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) y) =
      GlobalTheory.AdelicU.compInf F E w y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => erw [map_zero]
    | tmul a x => rfl
    | add x y hx hy => erw [map_add, map_add, map_add, hx, hy]
  rw [e, e]
  exact h1 w

theorem map_mul_eq_of_keeps {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (X : Matrix (Fin n) (Fin r) A) (P : Matrix (Fin r) (Fin n) A)
    (hPX : P * X = 1) (β : Matrix (Fin r) (Fin r) R) (h : M.map φ * X.map φ = X.map φ * β) :
    (M * X).map φ = (X * (P * M * X)).map φ := by
  have hPX' : P.map φ * X.map φ = 1 := by
    rw [← Matrix.map_mul, hPX, Matrix.map_one _ (map_zero φ) (map_one φ)]
  simp only [Matrix.map_mul]
  rw [h, Matrix.mul_assoc (P.map φ), h, ← Matrix.mul_assoc (P.map φ), hPX', Matrix.one_mul]

theorem mat_projArch {D : D7} {T : HSp D} (q : GA D T) (w : InfinitePlace D.host.F) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (GlobalTheory.AdelicU.projArch D.sp.cm.sig T.gram w q)).1 =
                 (Formalism.L2.Theta.mt T q).map (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) :=
  Matrix.ext fun _ _ => rfl

theorem mt_inv_mul_self {D : D7} {T : HSp D} (q : GA D T) :
    Formalism.L2.Theta.mt T q⁻¹ * Formalism.L2.Theta.mt T q = 1 := by
  show (Formalism.L2.Theta.matHom T q⁻¹).1 * (Formalism.L2.Theta.matHom T q).1 = 1
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem keeps_map {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (w : InfinitePlace D.host.F)
    (β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E))
    (h : (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    (Formalism.L2.Theta.mt T q).map (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) * Matrix.map d.jX (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) =
      Matrix.map d.jX (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) * β := by
  rw [← mat_projArch q w]
  exact h

theorem arch_comp {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (w : InfinitePlace D.host.F)
    (β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E))
    (h : (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β)
    (i : Fin T.rank) (j : Fin r) :
    GlobalTheory.AdelicU.compInf D.host.F D.host.E w ((Formalism.L2.Theta.mt T q ⬝ d.jX) i j) =
      GlobalTheory.AdelicU.compInf D.host.F D.host.E w ((d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)) i j) := by
  have h2 := keeps_map d q w β h
  have h3 := map_mul_eq_of_keeps (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (Formalism.L2.Theta.mt T q) d.jX d.pX
    d.pX_jX β h2
  rw [← Matrix.map_apply (f := GlobalTheory.AdelicU.compInf D.host.F D.host.E w), h3]
  rfl

theorem mul_jX_eq {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (hq : q ∈ GinfC T)
    (hw : ∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    Formalism.L2.Theta.mt T q ⬝ d.jX = d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX) := by
  let φf : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hf : (Formalism.L2.Theta.mt T q).map φf = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hq)
  have hfin := map_mul_eq_of_keeps φf (Formalism.L2.Theta.mt T q) d.jX d.pX d.pX_jX 1
    (by rw [hf, Matrix.one_mul, Matrix.mul_one])
  funext i j
  exact adTens_ext (F := D.host.F) (E := D.host.E) (fun w => Exists.elim (hw w) fun β hβ => arch_comp d q w β hβ i j)
    (congrFun (congrFun hfin i) j)

theorem mem_stab_of_keeps : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T), q ∈ GinfC T → (∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) → q ∈ stab d := by
  intro D T T₀ r d q hq hw
  have hPX : d.pX ⬝ d.jX = 1 := d.pX_jX
  have key := mul_jX_eq d q hq hw
  have hinv : Formalism.L2.Theta.mt T q⁻¹ ⬝ Formalism.L2.Theta.mt T q = 1 := mt_inv_mul_self q
  have h1 : (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX) = 1 := by
    calc (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)
        = (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹) ⬝ (d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)) := by
          rw [Matrix.mul_assoc]
      _ = (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹) ⬝ (Formalism.L2.Theta.mt T q ⬝ d.jX) := by rw [← key]
      _ = d.pX ⬝ ((Formalism.L2.Theta.mt T q⁻¹ ⬝ Formalism.L2.Theta.mt T q) ⬝ d.jX) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hinv, Matrix.one_mul, hPX]
  exact ⟨⟨_, _, mul_eq_one_comm.mp h1, h1⟩, key⟩

end GlobalTheory.Core.Rk.IwGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D := by
  first | exact @GlobalTheory.MixValues.mixed_values | exact GlobalTheory.MixValues.mixed_values | (intros; apply GlobalTheory.MixValues.mixed_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelIdentification_respects_real_and_finite : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D), IsInfFam θ → IdE X → RealSplit X h θ := by
  first | exact @GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE | exact GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE | (intros; apply GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapRightTranslateRealPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealPointMove

theorem translate_eq_move : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ k ∈ GinfC V, ∀ v : M.Vec, ∃ v' : M.Vec, (∀ τ, (v' τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) k) (v τ)) ∧ ∀ x, T v (x * k) = T v' x := by
  intro D θ hθ V S M J χ T hT k hk v
  refine ⟨fun τ => ⟨M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) k) (v τ),
    GlobalTheory.UnifEvery.rep_mem_sm M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ) (v τ).2⟩,
    fun τ => rfl, fun x => ?_⟩
  have key := GlobalTheory.RealEquiv.mult_realElt D V S θ M J χ T (Submodule.subset_span hT)
    (fun τ => infMat D.sp.cm.sig V.gram (θ τ) k) (fun τ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ) v
    (fun τ => ⟨M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) k) (v τ),
      GlobalTheory.UnifEvery.rep_mem_sm M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ) (v τ).2⟩) (fun τ => rfl)
  rw [← GlobalTheory.RealTransSm.eq_realElt hθ hk] at key
  rw [key]
  rfl

end GlobalTheory.RealPointMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZeroStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero : ∀ (D : D7) (S : Set (FinPl D)) (a b : ℕ), AnalyticOnNhd ℂ (GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b) (rightOf 0) ∧ ∀ s : ℂ, 0 < s.re → GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b s ≠ 0 ∧ (∀ v : FinPl D, GlobalTheory.LFun.dv D.host.E a b v s ≠ 0) ∧ HasProd (fun v : {v : FinPl D // v ∉ S} => GlobalTheory.LFun.dv D.host.E a b v.1 s) (GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b s) := by
  first | exact @GlobalTheory.Core.Rk.IP.dSfun_analytic_ne_zero | exact GlobalTheory.Core.Rk.IP.dSfun_analytic_ne_zero | (intros; apply GlobalTheory.Core.Rk.IP.dSfun_analytic_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramifiedStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_coefficient_bounded_spherical_unramified : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A) (L : Lat A), IsInfFam θ → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)), ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram L (Sf : Set (FinPl D)) u₁ par → SphFun A L Sf u₂ → ∀ v ∉ Sf, ∀ x : GA D A, proj D.sp.cm.sig A.gram v x = 1 → IsSphCoef A L v par fun y => rcoef m u₁ u₂ (x * emb D.sp.cm.sig A.gram v y) := by
  first | exact @GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef | exact GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef | (intros; apply GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef <;> assumption)
end

