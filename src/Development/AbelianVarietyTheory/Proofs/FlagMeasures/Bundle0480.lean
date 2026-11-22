import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0020
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0479
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0195
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0469
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0193
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0468
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsFD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0105
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0192
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0460
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0473
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0470
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0465
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0287
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0416
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0036
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0014
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeConstantEqProdCovolumes
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AmplitudeConst

theorem normSq_inv_mul_sqrt (l d l' d' : ℝ) (hl : 0 < l) (hl' : 0 < l') (hd : 0 ≤ d) (hd' : 0 ≤ d') :
    Complex.normSq ((((l / d : ℝ) : ℂ))⁻¹ * ((Real.sqrt (l / d * d' / l') : ℝ) : ℂ)) = d / l * (d' / l') := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.normSq_ofReal]
  have hs : 0 ≤ l / d * d' / l' := by positivity
  have e : (l / d)⁻¹ * Real.sqrt (l / d * d' / l') * ((l / d)⁻¹ * Real.sqrt (l / d * d' / l')) =
      (l / d)⁻¹ * (l / d)⁻¹ * (Real.sqrt (l / d * d' / l') * Real.sqrt (l / d * d' / l')) := by ring
  rw [e, Real.mul_self_sqrt hs]
  rcases hd.eq_or_lt with h | h
  · subst h; simp
  · field_simp

theorem const_eq (P P' L L' K M H M' H' V V' : ℝ) (hK : 0 < K) (hM : 0 < M) (hH : 0 < H) (hM' : 0 < M')
    (hH' : 0 < H') (hL : 0 < L) (hL' : 0 < L') (hV : L * V = M * H) (hV' : L' * V' = M' * H')
    (hP : 0 ≤ P) (hP' : 0 ≤ P') :
    P / L * (P' / L') = ((Real.sqrt (K * M * H / P * (K * M' * H' / P')))⁻¹ * K) ^ 2 * (V * V') := by
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), mul_inv, inv_div, inv_div]
  have eV : V = M * H / L := by field_simp; linarith
  have eV' : V' = M' * H' / L' := by field_simp; linarith
  subst eV eV'
  field_simp

theorem prod_finrank_loc {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    ∏ τ : D.what₂.Tau, (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) = (Module.finrank ℂ (X.Vpi u) : ℝ) := by
  rw [Formalism.L2.SG.Pf.finrank_Vpi, Nat.cast_prod]
  exact Fintype.prod_equiv X.pl.symm _ _ fun τ => rfl

theorem prod_normSq_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∏ τ, Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * ((Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u')).toReal) := by
  intro D X Y hF θ C hB u u' hθ hG
  have hK0 : 0 ≤ X.volK2 := ENNReal.toReal_nonneg
  have hv := hF.volPos u
  have hv' := hF.volPos u'
  have hN : 0 < X.volK2 * (X.muN u (Y.FN u)).toReal := hv.1
  have hN' : 0 < X.volK2 * (X.muN u' (Y.FN u')).toReal := hv'.1
  have hK : 0 < X.volK2 := pos_of_mul_pos_left hN ENNReal.toReal_nonneg
  have hNu : 0 < (X.muN u (Y.FN u)).toReal := pos_of_mul_pos_right hN hK0
  have hNu' : 0 < (X.muN u' (Y.FN u')).toReal := pos_of_mul_pos_right hN' hK0
  have hHu : 0 < (X.muH u Set.univ).toReal := hv.2
  have hHu' : 0 < (X.muH u' Set.univ).toReal := hv'.2
  obtain ⟨hl, hp⟩ := GlobalTheory.T.product_l2_positive D X Y θ C hB u hθ hG hNu hHu
  obtain ⟨hl', hp'⟩ := GlobalTheory.T.product_l2_positive D X Y θ C hB u' hθ hG hNu' hHu'
  have hτ : ∀ τ, Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) =
      (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) / (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal *
        ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℝ) / (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal) := by
    intro τ
    unfold sclOf cOf
    exact normSq_inv_mul_sqrt _ _ _ _ (hl τ) (hl' τ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [Finset.prod_congr rfl fun τ _ => hτ τ, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_div_distrib, prod_finrank_loc, prod_finrank_loc]
  unfold Formalism.L2.SG.TermOp.scl Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X
  exact const_eq _ _ _ _ _ _ _ _ _ _ _ hK hNu hHu hNu' hHu' (Finset.prod_pos fun τ _ => hl τ)
    (Finset.prod_pos fun τ _ => hl' τ) hp hp' (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end GlobalTheory.AmplitudeConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGaps
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory

theorem bp_forms_of_gapIn_thmBpDS : GlobalTheory.GapIn.Hyp → ThmBpDS → ∀ Ch : ℝ, ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → (∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ) ∧ (∀ D : D7, Formalism.MainNotions.OnePlaceEstimates.TheoremBPrimePointwise D Ch Cg Cb) ∧ ∀ (D : D7) (Cu Cg' : ℝ), 200 * Cu ≤ Cg' → Formalism.MainNotions.OnePlaceEstimates.UniformityTheoremBPrime D Ch Cu Cg Cg' Cb := by
  intro hH hT Ch
  obtain ⟨C₄, G₀, hC₄, hloc⟩ := GlobalTheory.pointwiseBound_at_place_of_locBessel hT Ch
  obtain ⟨c₃, hdict⟩ := GlobalTheory.ThA.BpDict.bpIneq_of_thmBpAt
  refine ⟨max (C₄ + 1) 10, max G₀ (240 + 2 * |c₃|), fun Cg hCg => ?_⟩
  have hG₀ : G₀ ≤ Cg := (le_max_left _ _).trans hCg
  have hG₁ : 240 + 2 * |c₃| ≤ Cg := (le_max_right _ _).trans hCg
  have main : ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D (max (C₄ + 1) 10) L f μsec b γ := by
    intro D L lam0 f μsec ka b hL hg hf hsec
    obtain ⟨U, U', p, n₀, hstd, hn₀, hB⟩ := hloc Cg hG₀ D L lam0 f μsec ka b hL hg hf hsec
    obtain ⟨hk, -, hc, hκ0, hκ, hS, -⟩ := hL
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb, -, -, hall, hgap, -⟩ := hS
    obtain ⟨hOK, hA⟩ := bpNear_gapOK D.R.k D.R.rS hk c₃ Cg hG₁
    obtain ⟨v1, v2, -⟩ := GlobalTheory.upqRep_vocabulary_agree D.R.k D.R.rS L.Hs L.σ L.ε L.lam
    have hone : (1 : B.Mat D.R.k D.R.rS) ∈ UH (Hpk D.R.k D.R.rS) := by simp [UH]
    have hE := GlobalTheory.T.discreteSeriesCoefficient_smooth_decay_capelliEigen_largeGap hH D.R.k D.R.rS L.ε L.lam _ ⟨L.Hs, L.σ⟩ L.Wp L.Wq f ⟨L.hlam, v1.1 L.hσ⟩
      (bpNear_gapAtLeast _ _ _ _ hgap hg) hOK (by
        obtain ⟨P, Q, hQ, hP, he⟩ := hf
        exact ⟨1, hone, 1, hone, P, Q, fun w => (v2 _).1 (hQ w), fun x => (v2 _).1 (hP x), fun g => by
          simpa using he g⟩)
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have hm : ((2 * D.R.rS + 2 : ℕ) : ℝ) = 2 * ((D.R.rS : ℝ) + 1) := by push_cast; ring
    have hb3 : 3 ≤ b := by
      have h1 := hall ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
      have h2 := abs_sub (lam0 ⟨0, by omega⟩) (lam0 ⟨1, by omega⟩)
      have h3 : (1 : ℝ) ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by rw [hm]; linarith)
      have h4 : 240 * 1 ≤ Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 :=
        mul_le_mul (by linarith [abs_nonneg c₃]) h3 (by norm_num) (by linarith [abs_nonneg c₃])
      linarith [hb ⟨0, by omega⟩, hb ⟨1, by omega⟩]
    refine hdict D L μsec U U' p f _ b C₄ _ n₀ _ hstd (hc.trans Formalism.MainNotions.OnePlaceEstimates.cOfDpsi_one) hκ0.ne' hκ hA (hE.2.1 1)
      hb3 (le_max_left _ _) ?_ hB
    have h1 : (n₀ : ℝ) ≤ 30 * ((D.R.rS : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn₀
    have h2 : 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ≤ max (C₄ + 1) 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    refine le_trans ?_ h2
    rw [hm]; push_cast; nlinarith
  refine ⟨main, ?_, ?_⟩
  · intro D L f μsec ka b hL hf hsec
    exact main D L L.lam f μsec ka b hL (fun s s' _ => by simp [l1]) hf hsec
  · intro D Cu Cg' hCu L lam0 f μsec ka b hL hR hf hsec _
    refine main D L lam0 f μsec ka b hL (fun s s' hs => le_trans ?_ (hR.1 s s' hs)) hf hsec
    have h1 := hR.2
    have h2 : 200 * Cu * ((D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) ≤
        Cg' * ((D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) := mul_le_mul_of_nonneg_right hCu (by positivity)
    nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProofStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyGenericMassPositiveBounded_proof : PI.VolStabS.MassDataS.SWXS → GlobalTheory.SnFam.WeightsFam := by
  first | exact @GlobalTheory.WeightsFamPf.weightsFam_of | exact GlobalTheory.WeightsFamPf.weightsFam_of | (intros; apply GlobalTheory.WeightsFamPf.weightsFam_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyRowWeightSumUnfoldingIdentityProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyRowWeightSumUnfoldingIdentity : GlobalTheory.SnFam.FamilyWeightSumUnfoldingIdentity := by
  first | exact @GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof | exact GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof | (intros; apply GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
section
namespace GlobalTheory.GapIn

theorem hyp_of_uniqGap : GlobalTheory.GapIn.UniqGap → GlobalTheory.GapIn.Hyp :=
  fun h => ⟨CompanionTheory.PieriExpansion.hypsG_of_zuck CompanionTheory.Zuck.zuckerman_gap, h, Formalism.L2.SG.OwnFacts.factMultOne.out,
    Formalism.L2.SG.OwnFacts.FD.factDsigHC.out⟩

end GlobalTheory.GapIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowDoubleCosetSumNormSqBound
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.RowCoset

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem isLattice_of_lrel {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) {Γ Γ' : G.Lt}
    (hΓ : Submodule.IsLattice E Γ) (h : G.LRel Γ Γ') : Submodule.IsLattice E Γ' := by
  obtain ⟨g, -, rfl⟩ := h
  refine ⟨hΓ.fg.map _, ?_⟩
  rw [Submodule.map_coe]
  have : (((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E)) : G.V → G.V) = ((g : G.V →ₗ[E] G.V) : G.V → G.V) := rfl
  rw [this, Submodule.span_image, hΓ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem term_of_lrel {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (hk : 4 * r + 7 ≤ k) {d : G.Dat}
    (hex : ∃ Λ₀, G.IsTerm d Λ₀) {Γ Γ' : G.Lt} (hΓ : G.IsTerm d Γ) (h : G.LRel Γ Γ') : G.IsTerm d Γ' := by
  have hl := isLattice_of_lrel G hΓ.1 h
  have e := ((GlobalTheory.T.globalHermitianFrames_terms_orbits_local A r k G hk d hex).2.1 Γ Γ' hΓ hl).1 h
  refine ⟨hl, fun p => ?_⟩
  obtain ⟨s, hs, hsp⟩ := e p
  rw [hsp]
  have := (A.loc p).lf
  have := (A.loc p).char0
  exact (GlobalTheory.FrameAct.stabiliser_acts_on_terms (A.L p) r k (G.S p) (d p) _ (hΓ.2 p) s hs).1

end GlobalTheory.HL.RowCoset

namespace GlobalTheory.HL.RowCoset

theorem row_coset_sum_norm_sq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → Formalism.L2.SG.PairVal.ptOf t₀.toTerm = w → ∀ Q : Prop → Prop, ‖∑' t : TauC Y u u', {t : TauC Y u u' | (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ∧ nmlOf Y u u' t = nmlOf Y u u' t₀ ∧ Q (¬ t.generic)}.indicator (Y.tO u u').vec t‖ ^ 2 = Formalism.L2.SG.TermOp.wt t₀ ^ 2 * ‖G.amp (G.datOf (c.lat ρ t₀.lam)) (fun Γ => Q (¬ G.Gen (G.datOf (c.lat ρ t₀.lam)) Γ))‖ ^ 2 * ((((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) ^ 2 * ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w)‖ ^ 2) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c ν hν t₀ ρ U U' hMv hrelv hpt Q
  set d₀ := G.datOf (c.lat ρ t₀.lam) with hd₀
  have hrow : ∀ t : TauC Y u u', (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → t.lam = t₀.lam ∧ t.lam' = t₀.lam' :=
    fun t h => ⟨congrArg (fun x => x.1.1) h, congrArg (fun x => x.2.1.1) h⟩
  have hmv : ∀ (t : TauC Y u u') n m, (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧
      t.lin = n⁻¹ * t₀.lin * m) → ∃ A A' : Formalism.L2.SG.PairVal.MatR D,
      MovesTo F00 F'0 (lf D (X.Fu u)) t.frame (ρ * n) (U * A) (U' * A') := by
    intro t n m h
    obtain ⟨A, A', -, -, -, -, hM⟩ :=
      (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv).2.2.2.2.2 t n m h
    exact ⟨A, A', hM⟩
  have hdat : ∀ (t : TauC Y u u') n m, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ →
      (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m) →
      G.datOf (c.lat (ρ * n) t.lam) = d₀ := by
    intro t n m hr h
    obtain ⟨h1, h2⟩ := hrow t hr
    exact (GlobalTheory.T.termRow_eq_iff_movedLatticeInnerData_eq D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv t n m h1 h2 h).1 hr
  have hterm : ∀ (t : TauC Y u u') n m, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ →
      (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m) →
      G.IsTerm d₀ (c.lat (ρ * n) t.lam) := by
    intro t n m hr h
    obtain ⟨A, A', hM⟩ := hmv t n m h
    have := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t (ρ * n) (U * A) (U' * A') hM).1
    rwa [hdat t n m hr h] at this
  have hgen : ∀ (t : TauC Y u u') n m, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ →
      (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m) →
      (t.generic ↔ G.Gen d₀ (c.lat (ρ * n) t.lam)) := by
    intro t n m hr h
    obtain ⟨A, A', hM⟩ := hmv t n m h
    have := GlobalTheory.T.generic_iff_zero_defectGroup_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t (ρ * n) (U * A) (U' * A') hM
    rwa [hdat t n m hr h] at this
  have hinj : ∀ (t t' : TauC Y u u') n m n' m', (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ →
      (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t₀ →
      (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m) →
      (n' ∈ NRat (lf D (X.Fu u)) ∧ m' ∈ NRat (lf D (X.Fu u')) ∧ t'.lin = n'⁻¹ * t₀.lin * m') →
      (t = t' ↔ G.LRel (c.lat (ρ * n) t.lam) (c.lat (ρ * n') t'.lam)) := by
    intro t t' n m n' m' hr hr' h h'
    obtain ⟨a1, a2⟩ := hrow t hr
    obtain ⟨b1, b2⟩ := hrow t' hr'
    exact GlobalTheory.T.doubleCoset_term_eq_iff_stabiliserOrbit D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv t t' n m n' m' a1 a2 b1 b2 h h'
  have hex : ∃ Λ₀, G.IsTerm d₀ Λ₀ :=
    ⟨_, (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv).1⟩
  have hfin : {o : Quot G.LRel | G.IsTerm d₀ o.out}.Finite :=
    (GlobalTheory.T.hermitian_amplitude_mass_product_structure _ _ _ G hk d₀ hex (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)
      (Set.finite_empty.subset fun _ ⟨_, _, h⟩ => absurd trivial h)).2.2.2
  have heqv : Equivalence G.LRel := (GlobalTheory.T.globalHermitianFrames_terms_orbits_local _ _ _ G hk d₀ hex).2.2.1
  have hsurj := fun Γ hΓ => GlobalTheory.T.exists_term_of_globalTerm_strongApprox D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv Γ hΓ
  let τ : Quot G.LRel → TauC Y u u' := fun o =>
    if h : G.IsTerm d₀ o.out then (hsurj o.out h).choose else t₀
  have hτ : ∀ o, G.IsTerm d₀ o.out → ∃ n m, (Y.tO u u').rowOf (τ o) = (Y.tO u u').rowOf t₀ ∧
      (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ (τ o).lin = n⁻¹ * t₀.lin * m) ∧
      o.out = c.lat (ρ * n) (τ o).lam := by
    intro o h
    have e : τ o = (hsurj o.out h).choose := dif_pos h
    rw [e]
    exact (hsurj o.out h).choose_spec
  let Cf : Finset (Quot G.LRel) := hfin.toFinset.filter (fun o => Q (¬ G.Gen d₀ o.out))
  have hmemC : ∀ o, o ∈ Cf ↔ G.IsTerm d₀ o.out ∧ Q (¬ G.Gen d₀ o.out) := by
    intro o
    simp [Cf]
  set S : Set (TauC Y u u') := {t : TauC Y u u' | (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ∧
    nmlOf Y u u' t = nmlOf Y u u' t₀ ∧ Q (¬ t.generic)} with hS
  have hτS : ∀ o ∈ Cf, τ o ∈ S := by
    intro o ho
    obtain ⟨hT, hPo⟩ := (hmemC o).1 ho
    obtain ⟨n, m, hr, h, he⟩ := hτ o hT
    refine ⟨hr, (GlobalTheory.T.doubleCoset_eq_iff_isometry_unipotent_translate D X Y u u' hSt t₀ (τ o)).2 ⟨n, m, h⟩, ?_⟩
    have hg := hgen (τ o) n m hr h
    rw [← he] at hg
    have : (¬ (τ o).generic) = (¬ G.Gen d₀ o.out) := propext (not_congr hg)
    rw [this]
    exact hPo
  have hτinj : Set.InjOn τ Cf := by
    intro o ho o' ho' e
    obtain ⟨hT, -⟩ := (hmemC o).1 ho
    obtain ⟨hT', -⟩ := (hmemC o').1 ho'
    obtain ⟨n, m, hr, h, he⟩ := hτ o hT
    obtain ⟨n', m', hr', h', he'⟩ := hτ o' hT'
    have hl := (hinj (τ o) (τ o') n m n' m' hr hr' h h').1 e
    rw [← he, ← he'] at hl
    calc o = Quot.mk G.LRel o.out := (Quot.out_eq o).symm
      _ = Quot.mk G.LRel o'.out := Quot.sound hl
      _ = o' := Quot.out_eq o'
  have hτsurj : ∀ t ∈ S, ∃ o ∈ Cf, τ o = t := by
    rintro t ⟨hr, hn, hq⟩
    obtain ⟨n, m, h⟩ := (GlobalTheory.T.doubleCoset_eq_iff_isometry_unipotent_translate D X Y u u' hSt t₀ t).1 hn
    have hΓ := hterm t n m hr h
    obtain ⟨o, ho⟩ : ∃ o : Quot G.LRel, o = Quot.mk G.LRel (c.lat (ρ * n) t.lam) := ⟨_, rfl⟩
    have hrel1 : G.LRel (c.lat (ρ * n) t.lam) o.out := by
      have e : Quot.mk G.LRel o.out = Quot.mk G.LRel (c.lat (ρ * n) t.lam) := by rw [Quot.out_eq o, ho]
      exact heqv.symm ((Equivalence.eqvGen_iff heqv).1 (Quot.eqvGen_exact e))
    have hT : G.IsTerm d₀ o.out := term_of_lrel G hk hex hΓ hrel1
    obtain ⟨n', m', hr', h', he'⟩ := hτ o hT
    have heq : τ o = t := (hinj (τ o) t n' m' n m hr' hr h' h).2 (by rw [← he']; exact heqv.symm hrel1)
    refine ⟨o, (hmemC o).2 ⟨hT, ?_⟩, heq⟩
    have hg := hgen (τ o) n' m' hr' h'
    rw [← he', heq] at hg
    have : (¬ G.Gen d₀ o.out) = (¬ t.generic) := propext (not_congr hg.symm)
    rw [this]
    exact hq
  obtain ⟨T, hTn, hamp⟩ :=
    GlobalTheory.T.rowTerm_amplitude_eq_mass_mul_phase D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c ν hν t₀ ρ U U' hMv hrelv hpt
  set K : ℝ := ((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹ with hK
  let q₀ : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u'} := (⟨t₀.lam, t₀.mem⟩, ⟨t₀.lam', t₀.mem'⟩)
  let V : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) → H1 X u u' (Y.what₂ u) (Y.what₂ u') :=
    fun x => WithLp.toLp 2 (fun q => if q = q₀ then x else 0)
  have hVadd : ∀ x y, V x + V y = V (x + y) := by
    intro x y
    show WithLp.toLp 2 _ + WithLp.toLp 2 _ = WithLp.toLp 2 _
    rw [← WithLp.toLp_add]
    congr 1
    funext q
    by_cases h : q = q₀ <;> simp [h]
  have hV0 : V 0 = 0 := by
    show WithLp.toLp 2 _ = 0
    have : (fun q => if q = q₀ then (0 : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u)) else 0) = 0 := by
      funext q; simp
    rw [this]
    rfl
  have hVsum : ∀ (s : Finset (Quot G.LRel)) (x : Quot G.LRel → Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u)),
      ∑ o ∈ s, V (x o) = V (∑ o ∈ s, x o) := by
    intro s x
    induction s using Finset.induction_on with
    | empty => simp [hV0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, hVadd]
  have hVn : ∀ x, ‖V x‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    show ‖(WithLp.toLp 2 (fun q => if q = q₀ then x else 0) : H1 X u u' (Y.what₂ u) (Y.what₂ u'))‖ ^ 2 = _
    rw [PiLp.norm_sq_eq_of_L2]
    have : ∀ q, ‖(if q = q₀ then x else 0 : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u))‖ ^ 2 =
        if q = q₀ then ‖x‖ ^ 2 else 0 := fun q => by by_cases h : q = q₀ <;> simp [h]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hvec : ∀ o ∈ Cf, (Y.tO u u').vec (τ o) = V (((Formalism.L2.SG.TermOp.wt t₀ : ℝ) : ℂ) •
      Formalism.L2.SG.PackageTie.hsEmb ((((K * G.mu o.out : ℝ) : ℂ) * G.om d₀ o.out) • T)) := by
    intro o ho
    obtain ⟨hT, -⟩ := (hmemC o).1 ho
    obtain ⟨n, m, hr, h, he⟩ := hτ o hT
    obtain ⟨h1, h2⟩ := hrow (τ o) hr
    have ha := hamp (τ o) n m hr h
    rw [← he] at ha
    show WithLp.toLp 2 _ = WithLp.toLp 2 _
    congr 1
    funext q
    have hq : ((⟨(τ o).lam, (τ o).mem⟩, ⟨(τ o).lam', (τ o).mem'⟩) :
        {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u'}) = q₀ := Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    have hw : Formalism.L2.SG.TermOp.wt (τ o) = Formalism.L2.SG.TermOp.wt t₀ := by
      unfold Formalism.L2.SG.TermOp.wt
      rw [h1, h2]
    rw [hq, hw, ha]
  have hzero : ∀ t ∉ Cf.image τ, S.indicator (Y.tO u u').vec t = 0 := by
    intro t ht
    apply Set.indicator_of_notMem
    intro hSt'
    obtain ⟨o, ho, e⟩ := hτsurj t hSt'
    exact ht (Finset.mem_image.2 ⟨o, ho, e⟩)
  have hampeq : G.amp d₀ (fun Γ => Q (¬ G.Gen d₀ Γ)) = ∑ o ∈ Cf, (G.mu o.out : ℂ) * G.om d₀ o.out := by
    unfold GFrames.amp
    rw [tsum_eq_sum (s := Cf)]
    · exact Finset.sum_congr rfl fun o ho => if_pos ((hmemC o).1 ho)
    · intro o ho
      exact if_neg fun h => ho ((hmemC o).2 h)
  rw [tsum_eq_sum hzero, Finset.sum_image hτinj]
  rw [Finset.sum_congr rfl fun o ho => by rw [Set.indicator_of_mem (hτS o ho), hvec o ho], hVsum, hVn]
  have hsum : ∑ o ∈ Cf, ((Formalism.L2.SG.TermOp.wt t₀ : ℝ) : ℂ) •
      Formalism.L2.SG.PackageTie.hsEmb ((((K * G.mu o.out : ℝ) : ℂ) * G.om d₀ o.out) • T) =
      ((Formalism.L2.SG.TermOp.wt t₀ : ℝ) : ℂ) • (((K : ℂ) * G.amp d₀ (fun Γ => Q (¬ G.Gen d₀ Γ))) •
        Formalism.L2.SG.PackageTie.hsEmb T) := by
    rw [hampeq, Finset.mul_sum, Finset.sum_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [map_smul]
    congr 2
    push_cast
    ring
  rw [hsum, norm_smul, norm_smul, norm_mul, hTn, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  simp only [mul_pow, sq_abs]
  ring

end GlobalTheory.HL.RowCoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAmplitudeLeCovolumeLocalAmplitudes
section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem factC_of (hP : PullC) (hTn : TensC) (hC : ConstC) : FactC := by
  intro D X Y u C hB hG hcov t hrel μ ν K hμν hK
  obtain ⟨μR, νl, hνl, hH, hQ, hμR, hmap⟩ := hP D X Y u C t μ ν hμν
  have hFA := Formalism.L2.SG.Pf.formAllC_holds D X Y u u t μR (Measure.pi νl) K
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u t hrel) hH hQ hK.1 hK.2
  have hT := hTn D X u t.pt.1 νl hνl
  obtain ⟨hc, hconst⟩ := hC D X Y u C hB hG hcov
  have hloc : ∀ τ, Real.sqrt (hsNormSq ((locS hB u u τ).J (ν τ) (gamT C t τ))) =
      (cOf hB u τ)⁻¹ * Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ))
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u (vOf X τ)) (t.pt.1 (vOf X τ)))) := by
    intro τ
    rw [← hmap τ]
    unfold gamT
    rw [Formalism.L2.SG.Pf.LocJEq.locJ_map_eq' C hB u u τ]
    refine (congrArg Real.sqrt (Formalism.L2.SG.Pf.LTL.hsNormSq_smul _ _)).trans ?_
    rw [(hc τ).2, mul_one, map_inv₀, Complex.normSq_ofReal, Real.sqrt_mul', Real.sqrt_inv,
      Real.sqrt_mul_self (hc τ).1.le]
    · rfl
    · exact Formalism.L2.SG.Pf.LTL.hsNormSq_nonneg _
  have hv : ‖(Y.tO u u).vec t‖ = wt t * ‖Formalism.L2.SG.PackageTie.hsEmb
      (ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t)‖ := by
    show ‖Formalism.L2.SG.TermOp.vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t‖ = _
    unfold Formalism.L2.SG.TermOp.vec
    rw [← norm_smul_of_nonneg (show 0 ≤ wt t from Real.sqrt_nonneg _) (Formalism.L2.SG.PackageTie.hsEmb
      (ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t)), ← Complex.coe_smul]
    refine Eq.trans ?_ (PiLp.norm_toLp_single 2
      (fun _ : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u} => Formalism.L2.SG.PackageTie.HS (X.Vpi u) (X.Vpi u))
      ((⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩) : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u}) _)
    congr 2
    funext q
    simp only [Pi.single_apply]
  have hs0 : 0 ≤ scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2 := by
    unfold scl HidaSetting.volK2
    positivity
  have hamp : ‖Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t)‖ =
      (scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2) * ((μR K).toReal *
        ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) t.pt.1)‖) := by
    unfold ampN
    rw [map_smul, map_smul, norm_smul, norm_smul, Formalism.L2.SG.Pf.FibreCounting.norm_chiN, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs0, hFA, ← Complex.coe_smul, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hprod : ∏ τ, Real.sqrt (hsNormSq ((locS hB u u τ).J (ν τ) (gamT C t τ))) =
      (∏ τ, cOf hB u τ)⁻¹ * ∏ v, Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (t.pt.1 v))) := by
    rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    congr 1
    exact Fintype.prod_equiv X.pl.symm _ _ (fun τ => rfl)
  have hPc : 0 < ∏ τ, cOf hB u τ := Finset.prod_pos fun τ _ => (hc τ).1
  rw [hv, hamp, ← hμR K hK.1, hprod]
  set N := ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) t.pt.1)‖ with hN
  set Pv := ∏ v, Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (t.pt.1 v))) with hPv
  set Pc := ∏ τ, cOf hB u τ with hPcd
  set s := scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2 with hsd
  set a := wt t with had
  set m := (μR K).toReal with hmd
  set cv := (covN C Y u).toReal with hcv
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hcv0 : 0 ≤ cv := ENNReal.toReal_nonneg
  have hPv0 : 0 ≤ Pv := Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _
  have hNP : N ≤ Pv := hT
  have hSJ : 0 ≤ Pc⁻¹ * Pv := mul_nonneg (inv_nonneg.2 hPc.le) hPv0
  calc a * (s * (m * N)) * cv = (a * m * cv * s) * N := by ring
    _ ≤ (a * m * cv * s) * (Pc * (Pc⁻¹ * Pv)) := by
        rw [mul_inv_cancel_left₀ hPc.ne']
        exact mul_le_mul_of_nonneg_left hNP (by positivity)
    _ = (a * (m * (Pc⁻¹ * Pv))) * (s * Pc * cv) := by ring
    _ ≤ (a * (m * (Pc⁻¹ * Pv))) * 1 := mul_le_mul_of_nonneg_left hconst (by positivity)
    _ = a * (m * (Pc⁻¹ * Pv)) := mul_one _

theorem factC_holds : FactC := factC_of GlobalTheory.T.localHaarMeasures_pullback_realGroup GlobalTheory.T.orbitalIntegralTensorBoundHyp_proof GlobalTheory.T.normalisingConstantsProductHyp_proof

end GlobalTheory.TypeAsm
end
end

