import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0292
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinitePartDenominatorLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0294
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionals
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactFiniteComponentsOfAnnihilatorOpenSu
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.MixModel GlobalTheory.Unf
noncomputable section

namespace GlobalTheory.AnnihMat

variable {D : D7}

theorem hO_single (S T : HSp D) (w : WO S T) (i : Fin T.rank) (j : Fin S.rank) (e : AE D) :
    hO S T w (Matrix.single i j (cA D e)) = e * (gA T ⬝ w ⬝ giA S) i j := by
  have ha : adj (Matrix.single i j (cA D e)) = Matrix.single j i e := by
    ext a b
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
    by_cases h1 : i = b <;> by_cases h2 : j = a <;> simp [h1, h2, GlobalTheory.DualPairCheck.cA_cA]
  rw [hO_eq_trace, ha, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_single_mul, smul_eq_mul]

end GlobalTheory.AnnihMat

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.AnnihMat GlobalTheory.AnnihBox in

theorem GlobalTheory.AnnihMat.annihilator_inBox_full : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∃ Q : Set (WO S T), IsCompact Q ∧ ∀ w : WO S T, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1) → GlobalTheory.Unf.InBox Q w := by
  intro D ψ hψ S T U hU
  let g : Fin T.rank → Fin S.rank → (AE D →+ WO S T) := fun i j =>
    { toFun := fun c => Matrix.single i j (cA D c)
      map_zero' := by simp
      map_add' := fun a b => by simp [Matrix.single_add] }
  have hg : ∀ i j, Continuous (g i j) := fun i j => by
    show Continuous fun c => Matrix.single i j (cA D c)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.single_apply]
    split_ifs
    · exact continuous_cA'
    · exact continuous_const
  have hK := fun i j => GlobalTheory.CondBound.annihilator_finPart_compact D ψ hψ (U.comap (g i j)) (hU.preimage (hg i j))
  choose K hKc hK using hK
  let R : WO S T → WO S T := fun k => giA T ⬝ k.map (fun z => incA D D.host.xi0⁻¹ * z) ⬝ gA S
  have hR : Continuous R :=
    (continuous_const.matrix_mul (continuous_id.matrix_map (continuous_const.mul continuous_id))).matrix_mul
      continuous_const
  refine ⟨R '' (Set.univ.pi fun i => Set.univ.pi fun j => K i j : Set (WO S T)),
    (isCompact_univ_pi fun i => isCompact_univ_pi fun j => hKc i j).image hR, ?_⟩
  intro w hw
  have hy : ∀ i j, ∃ k ∈ K i j, finPart D (incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j - k) = 0 := fun i j =>
    hK i j _ fun c hc hc0 => by
      have h1 : (Matrix.single i j (cA D c)).map (infPart D) = 0 := by
        ext a b
        simp only [Matrix.map_apply, Matrix.single_apply, Matrix.zero_apply]
        split_ifs
        · exact infPart_cA' c hc0
        · exact map_zero _
      have h2 := hw (Matrix.single i j (cA D c)) hc h1
      have e3 : incA D D.host.xi0 * hO S T w (Matrix.single i j (cA D c)) =
          incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j * c := by rw [hO_single]; ring
      unfold symplO at h2
      rwa [e3] at h2
  choose k hk hk0 using hy
  refine ⟨R (Matrix.of k), ⟨Matrix.of k, fun i _ j _ => hk i j, rfl⟩, ?_⟩
  have hsub : ∀ a b : WO S T, R (a - b) = R a - R b := fun a b => by
    simp only [R]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j
    simp [mul_sub]
  have hx' : R (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j) = w := by
    simp only [R]
    have e : (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j).map
        (fun z => incA D D.host.xi0⁻¹ * z) = gA T ⬝ w ⬝ giA S := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one, one_mul]
    rw [e]
    simp only [Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, giA_gA_cancel]
  have e : w - R (Matrix.of k) = R (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j - k i j) := by
    have hm : (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j - k i j) =
        (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j) - Matrix.of k := Matrix.ext fun _ _ => rfl
    rw [hm, hsub, hx']
  have h0 := map_finPart_mul_map (giA T) (incA D D.host.xi0⁻¹)
    (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j - k i j) fun i j => hk0 i j
  rw [e]
  simp only [R]
  rw [Matrix.map_mul, h0, Matrix.zero_mul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConstSqNormTwoHaarFundamentalDomainsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_sqNorm_two_haar_fundamentalDomains : ∀ (D : D7) (V' W : HSp D) (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (μ'' : Measure (WO V' W)) (𝓕'' : Set (WO V' W)), IsCovolOne (ratL W V') μ'' 𝓕'' → ∃ c : ENNReal, ∀ g : WO V' W → ℂ, Continuous g → (∀ γ ∈ ratL W V', ∀ w, ‖g (γ + w)‖ = ‖g w‖) → ∫⁻ x in 𝓕', ‖g x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x in 𝓕'', ‖g x‖ₑ ^ 2 ∂μ'' := by
  first | exact @GlobalTheory.Twist.NormRed.sq_norm_two_haar | exact GlobalTheory.Twist.NormRed.sq_norm_two_haar | (intros; apply GlobalTheory.Twist.NormRed.sq_norm_two_haar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinitePartDenominatorLeHeightPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePart_denominator_le_height_pow : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * height V g ^ A ∧ ∀ i j, (d : Lev.EAf D) * (Lev.finE V g).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.PointDenom.exists_denom_le_height_pow | exact GlobalTheory.PointDenom.exists_denom_le_height_pow | (intros; apply GlobalTheory.PointDenom.exists_denom_le_height_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedDenominatorFiniteCoordsIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_denominator_finiteCoords_integral : ∀ (D : D7), ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x → ∀ k, (d : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  first | exact @GlobalTheory.DenInt.exists_den | exact GlobalTheory.DenInt.exists_den | (intros; apply GlobalTheory.DenInt.exists_den <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphWittFlagCoordinatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homeomorph_wittFlagCoordinates : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ e : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) ≃ₜ flagN d, ∀ p, (e p : GA D S) = d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2) := by
  first | exact @GlobalTheory.MixPer.flagCoord_homeo | exact GlobalTheory.MixPer.flagCoord_homeo | (intros; apply GlobalTheory.MixPer.flagCoord_homeo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInstanceFramesOfDiagonalFrameSelfDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_instanceFrames_of_diagonalFrame_selfDual : ∀ (D : D7) (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∃ fr : Formalism.IndefR.Eqv.UI.Frames D V, fr.Λ = Λ ∧ ∀ τ, fr.ε (Formalism.L2.Host.tauPl D τ) = A.ε τ ∧ fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := by
  first | exact @GlobalTheory.frames_of_diagonalising_frame | exact GlobalTheory.frames_of_diagonalising_frame | (intros; apply GlobalTheory.frames_of_diagonalising_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralMatricesSeparatingRationalPairingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_matrices_separating_rationalPairing : ∀ (D : D7) (W : HSp D) (r : ℕ), ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E), (∀ j a b, IsIntegral ℤ (X j a b)) ∧ ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := by
  first | exact @GlobalTheory.RatPairSep.main | exact GlobalTheory.RatPairSep.main | (intros; apply GlobalTheory.RatPairSep.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLeftInverseIsotropicFrameKillingEmbeddingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leftInverse_isotropicFrame_killing_embedding : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∃ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 ∧ K * B = 0 := by
  first | exact @GlobalTheory.HalfAverage.exists_leftInv_frame_kill_emb | exact GlobalTheory.HalfAverage.exists_leftInv_frame_kill_emb | (intros; apply GlobalTheory.HalfAverage.exists_leftInv_frame_kill_emb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNatMulIntegralMatricesSubsetOpenAddSubgrouStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_natMul_integralMatrices_subset_openAddSubgroup : ∀ (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)), IsOpen (U : Set (WO V W)) → ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ a : Fin W.rank → Fin V.rank → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F, (∀ i j k, a i j k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : WO V W) ∈ U := by
  first | exact @GlobalTheory.OpenSubAdele.exists_nat_mul_mem_openAddSubgroup | exact GlobalTheory.OpenSubAdele.exists_nat_mul_mem_openAddSubgroup | (intros; apply GlobalTheory.OpenSubAdele.exists_nat_mul_mem_openAddSubgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroVacuumBesselLineLatticeRankZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_vacuum_besselLineLattice_rankZero : OnStd fun {D} _ _ _ {G} W F => ∃ Φ₀, VacG W.ψ _ _ (lineLat F 0) Φ₀ ∧ Φ₀ ≠ 0 := by
  first | exact @GlobalTheory.AscFin.LineZero.exists_vacG_lineLat_zero | exact GlobalTheory.AscFin.LineZero.exists_vacG_lineLat_zero | (intros; apply GlobalTheory.AscFin.LineZero.exists_vacG_lineLat_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupHalfCharactersSeparate
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfSeparate

open GlobalTheory.IdemModTwo

theorem sum_incA_inv_mul {D : D7} (W : HSp D) (p i : Fin W.rank) :
    ∑ k, incA D (W.gram⁻¹ p k) * incA D (W.gram k i) = if p = i then 1 else 0 := by
  have h1 : (∑ k, incA D (W.gram⁻¹ p k) * incA D (W.gram k i)) = incA D ((W.gram⁻¹ * W.gram) p i) := by
    rw [Matrix.mul_apply, map_sum (incA D)]
    exact Finset.sum_congr rfl fun k _ => ((incA D).map_mul _ _).symm
  rw [h1, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit W), Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

set_option maxHeartbeats 1000000 in

theorem exists_pair_entry {D : D7} {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)}
    {e : AE D} (he : SplitAt D v e) (W : HSp D) {r : ℕ} (p : Fin W.rank) (q : Fin r) (c : Fv D.host.F v) :
    ∃ a : Mx D W.rank r, IsHalf e a ∧ ∀ t : Mx D W.rank r,
      halfPair W a t = incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * t p q := by
  let a : Mx D W.rank r := Matrix.of fun k j => if j = q then
    incA D (star (W.gram⁻¹ p k)) * incA D (star D.host.xi0⁻¹) * fj D (singleV D.host.F v c) * e else 0
  have hca : ∀ k, cA D (a k q) = incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * incA D (W.gram⁻¹ p k) := by
    intro k
    show cA D (if q = q then _ else 0) = _
    rw [if_pos rfl, map_mul, map_mul, map_mul, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.cA_incA, star_star, star_star,
      cA_fj]
    ring
  refine ⟨a, fun k j => ?_, fun t => ?_⟩
  · show e * a k j = a k j
    simp only [a, Matrix.of_apply]
    split_ifs
    · rw [mul_left_comm, he.1]
    · rw [mul_zero]
  have hG := sum_incA_inv_mul W p
  unfold halfPair
  calc ∑ i, ∑ j, ∑ k, cA D (a k j) * incA D (W.gram k i) * t i j
      = ∑ i, incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * (if p = i then 1 else 0) * t i q :=
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_eq_single q (fun j _ hj => Finset.sum_eq_zero fun k _ => by
            rw [show a k j = 0 from if_neg hj, map_zero, zero_mul, zero_mul]) (fun h => absurd (Finset.mem_univ q) h)]
          rw [← hG i, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by rw [hca]; ring
    _ = incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * t p q := by
      rw [Finset.sum_eq_single p (fun i _ hi => by rw [if_neg (Ne.symm hi), mul_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ p) h), if_pos rfl, mul_one]

end GlobalTheory.HalfSeparate

namespace GlobalTheory.HalfSeparate

open GlobalTheory.IdemModTwo

set_option maxHeartbeats 1000000 in

theorem exists_open_separated : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (e : AE D), IsSplitIdem D e → ∀ U : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (U : Set (halfMx (cA D e) W.rank r)) → ∃ L : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ L ≤ U ∧ ∀ x, x ∉ L → ∃ a : halfMx e W.rank r, (∀ l ∈ L, ψ (halfSympl W (a : Mx D W.rank r) (l : Mx D W.rank r)) = 1) ∧ ψ (halfSympl W (a : Mx D W.rank r) (x : Mx D W.rank r)) ≠ 1 := by
  intro D ψ hψ W r e hε U hU
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hε
  have he' := he.conj
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : ProperSpace (Fv D.host.F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  let sg : Fv D.host.F v →+ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F := AddMonoidHom.ofMapSub (singleV D.host.F v) (singleV_sub D v)
  let ι : Fv D.host.F v →+ AF D.host.F := AddMonoidHom.mk' (fun y => pairA D.host.F 0 (sg y)) fun a b => by
    rw [map_add]; exact Prod.ext (add_zero _).symm rfl
  have hι : Continuous ι := Continuous.prodMk continuous_const (GlobalTheory.SplitAnnihilator.continuous_singleV D.host.F v)
  have hψc : Continuous fun x => ψ (ι x) := hψ.1.1.comp hι

  obtain ⟨ε0, hε0, hψε⟩ : ∃ ε > 0, ∀ x : Fv D.host.F v, ‖x‖ < ε → ψ (ι x) = 1 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hψc.continuousAt (x := 0)) (1 / 2) (by norm_num)
    refine ⟨δ, hδ, fun x hx => GlobalTheory.ThetaStalk.eq_one_of_pow_near fun n => ?_⟩
    have := h (x := n • x) (by
      rw [dist_zero_right]; exact (IsUltrametricDist.norm_nsmul_le x n).trans_lt hx)
    rwa [map_zero, AddChar.map_zero_eq_one, dist_eq_norm, map_nsmul, AddChar.map_nsmul_eq_pow] at this
  obtain ⟨y1, hy1⟩ : ∃ y, ψ (ι y) ≠ 1 := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v

  let G := Fin W.rank × Fin r → Fv D.host.F v
  let J : G →+ Mx D W.rank r := AddMonoidHom.mk' (fun y => Matrix.of fun i k => fj D (sg (y (i, k))) * cA D e)
    fun a b => by
      ext i k
      simp only [G, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add, add_mul]
  have hJ : Continuous J := continuous_matrix fun i k =>
    ((IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))).comp
      (hι.comp (continuous_apply (i, k)))).mul continuous_const
  have hJh : ∀ y, J y ∈ halfMx (cA D e) W.rank r := fun y i k => by
    show cA D e * (_ * cA D e) = _ * cA D e
    rw [mul_left_comm, he'.1]
  let J' : G →+ halfMx (cA D e) W.rank r := J.codRestrict (halfMx (cA D e) W.rank r) hJh
  have hJ' : Continuous J' := hJ.subtype_mk _
  have hJs : Function.Surjective J' := fun u => by
    choose y hy using fun p : Fin W.rank × Fin r => he'.exists_scalar ((u : Mx D W.rank r) p.1 p.2)
    exact ⟨y, Subtype.ext (Matrix.ext fun i k => (hy (i, k)).symm.trans (u.2 i k))⟩
  have : T2Space (halfMx (cA D e) W.rank r) := t2Space_halfAdelicMatrixAddSubgroup (cA D e) W.rank r
  have : LocallyCompactSpace (halfMx (cA D e) W.rank r) := lcHalf (cA D e) W.rank r
  have : R1Space (halfMx (cA D e) W.rank r) := T2Space.r1Space
  have : BaireSpace (halfMx (cA D e) W.rank r) := BaireSpace.of_t2Space_locallyCompactSpace
  have hopen : IsOpenMap J' := AddMonoidHom.isOpenMap_of_sigmaCompact J' hJs hJ'
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hJ') 0 (by
    show J' 0 ∈ U
    rw [map_zero]; exact U.zero_mem)

  have hR : 0 ≤ ‖y1‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  let LG : AddSubgroup G :=
    { carrier := {y | ∀ p, ∀ c : Fv D.host.F v, ‖c‖ ≤ ‖y1‖ / ρ → ψ (ι (c * y p)) = 1}
      add_mem' := fun {a b} ha hb p c hc => by
        rw [Pi.add_apply, mul_add, map_add, AddChar.map_add_eq_mul, ha p c hc, hb p c hc, one_mul]
      zero_mem' := fun p c _ => by rw [Pi.zero_apply, mul_zero, map_zero, AddChar.map_zero_eq_one]
      neg_mem' := fun {a} ha p c hc => by
        have h := ψ.map_add_eq_mul (ι (c * (-a) p)) (ι (c * a p))
        rw [← map_add, Pi.neg_apply, mul_neg, neg_add_cancel, map_zero, AddChar.map_zero_eq_one, ha p c hc,
          mul_one] at h
        rw [Pi.neg_apply, mul_neg]
        exact h.symm }
  have hLGopen : IsOpen (LG : Set G) := by
    refine AddSubgroup.isOpen_of_mem_nhds LG (g := 0) (Metric.mem_nhds_iff.2 ⟨ε0 / (‖y1‖ / ρ + 1), by positivity,
      fun y hy p c hc => hψε _ ?_⟩)
    have hy' : ‖y‖ < ε0 / (‖y1‖ / ρ + 1) := mem_ball_zero_iff.1 hy
    rw [lt_div_iff₀ (by positivity)] at hy'
    calc ‖c * y p‖ = ‖c‖ * ‖y p‖ := norm_mul _ _
      _ ≤ ‖y1‖ / ρ * ‖y‖ := mul_le_mul hc (norm_le_pi_norm y p) (norm_nonneg _) hR
      _ ≤ ‖y‖ * (‖y1‖ / ρ + 1) := by nlinarith [norm_nonneg y]
      _ < ε0 := hy'
  have hLGsmall : ∀ y ∈ LG, ‖y‖ < ρ := fun y hy => (pi_norm_lt_iff hρ).2 fun p => by
    by_contra hn
    push_neg at hn
    have hp : 0 < ‖y p‖ := hρ.trans_le hn
    have h := hy p (y1 / y p) (by rw [norm_div]; exact div_le_div_of_nonneg_left (norm_nonneg _) hρ hn)
    rw [div_mul_cancel₀ _ (norm_pos_iff.1 hp)] at h
    exact hy1 h
  refine ⟨LG.map J', by rw [AddSubgroup.coe_map]; exact hopen _ hLGopen, ?_, fun x hx => ?_⟩
  · rw [AddSubgroup.map_le_iff_le_comap]
    intro y hy
    exact hball (mem_ball_zero_iff.2 (hLGsmall y hy))
  obtain ⟨y, rfl⟩ := hJs x
  have hy : ¬ ∀ p, ∀ c : Fv D.host.F v, ‖c‖ ≤ ‖y1‖ / ρ → ψ (ι (c * y p)) = 1 :=
    fun h => hx (AddSubgroup.mem_map_of_mem _ h)
  push_neg at hy
  obtain ⟨p, c, hc, hne⟩ := hy
  obtain ⟨a, ha, hpair⟩ := exists_pair_entry he W p.1 p.2 c
  have key : ∀ y', ψ (halfSympl W a (J y')) = ψ (ι (c * y' p)) := fun y' => by
    congr 1
    have h1 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one]
    have h2 : incA D D.host.xi0 * halfPair W a (J y') =
        fj D (singleV D.host.F v c) * cA D e * (fj D (singleV D.host.F v (y' p)) * cA D e) := by
      rw [hpair]
      show incA D D.host.xi0 * (incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e *
        (fj D (singleV D.host.F v (y' p)) * cA D e)) = _
      linear_combination (fj D (singleV D.host.F v c) * cA D e * (fj D (singleV D.host.F v (y' p)) * cA D e)) * h1
    rw [halfSympl, h2]
    exact GlobalTheory.SplitAnnihilator.trace_split he' c (y' p)
  refine ⟨⟨a, ha⟩, fun l hl => ?_, (key y).trans_ne hne⟩
  obtain ⟨y', hy', rfl⟩ := AddSubgroup.mem_map.1 hl
  exact (key y').trans (hy' p c hc)

end GlobalTheory.HalfSeparate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsNeProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 1000000 in

theorem exists_part (R : RealDat D A Ks) (F : Face D A) {s : ℕ} (hs : A.fam.Ok s) (hC : GlobalTheory.Hk3.Core R F)
    (hS : GlobalTheory.Hk3.SchurAll R) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hSF : GlobalTheory.Hk3.IsSF R SF) (b : Bool)
    (i : Fin D.R.m) (hi : R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥) :
    ∃ c, ∃ z ∈ GlobalTheory.Hk3.Wcc R SF i c, z ≠ 0 ∧ (R.HW i (sg0 D A)).e z ∈ R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) := by
  classical
  have irr : ∀ χ ∈ A.X, IsAbsIrrChar χ := hs.irr
  obtain ⟨y, hy, hy0⟩ := Submodule.ne_bot_iff _ |>.1 hi
  have hWall : R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≤ R.Wall i (sg0 D A) :=
    (GlobalTheory.PartDims.goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _).trans inf_le_left
  have hR : LinearMap.range (R.HW i (sg0 D A)).e = R.Wall i (sg0 D A) := (hC.models.HW i (sg0 D A)).2.1
  obtain ⟨x, rfl⟩ : y ∈ LinearMap.range (R.HW i (sg0 D A)).e := hR ▸ hWall hy
  have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (map_zero _)
  obtain ⟨hxe, hxt⟩ := (GlobalTheory.WatType.wat_iff_type R F hs hC b i x).1 hy
  obtain ⟨h, -, -, -, hsup, hstab, -, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS irr SF hSF i
  obtain ⟨hidem, -, -, -⟩ := GlobalTheory.Hk3.eH_laws R F hC irr i
  obtain ⟨lam, hlam⟩ : ∃ lam : (F.lvl b).P → ℂ, ∀ p, lam p = sg0 D A ((((F.lvl b).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) :=
    ⟨_, fun _ => rfl⟩
  have lam_mul : ∀ p q, lam (p * q) = lam p * lam q := fun p q => by
    simp only [hlam, map_mul, Units.val_mul]
  have lam_ne : ∀ p, lam p ≠ 0 := fun p => by rw [hlam]; exact (map_ne_zero _).2 (Units.ne_zero _)
  have hxt' : ∀ p : (F.lvl b).P, R.gW i (sg0 D A) (p : G) x = lam p • x := fun p => by rw [hlam]; exact hxt p
  obtain ⟨π, hπ⟩ : ∃ π : Module.End ℂ (R.HW i (sg0 D A)).H,
      ∀ w, π w = ∑ p : (F.lvl b).P, (lam p)⁻¹ • R.gW i (sg0 D A) (p : G) w :=
    ⟨∑ p : (F.lvl b).P, (lam p)⁻¹ • R.gW i (sg0 D A) (p : G), fun w => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]⟩
  have htype : ∀ w (q : (F.lvl b).P), R.gW i (sg0 D A) (q : G) (π w) = lam q • π w := by
    intro w q
    rw [hπ, map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft q) _ _ fun p => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, smul_smul, Equiv.coe_mulLeft]
    show (lam p)⁻¹ • R.gW i (sg0 D A) ((q : G) * p) w =
      (lam q * (lam (q * p))⁻¹) • R.gW i (sg0 D A) ((q * p : (F.lvl b).P) : G) w
    rw [lam_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (lam_ne q), one_mul]
    exact congrArg (fun g => (lam p)⁻¹ • R.gW i (sg0 D A) g w) (Subgroup.coe_mul _ q p).symm
  have hπmem : ∀ c w, w ∈ GlobalTheory.Hk3.Wcc R SF i c → π w ∈ GlobalTheory.Hk3.Wcc R SF i c := by
    intro c w hw
    rw [hπ]
    refine Submodule.sum_mem _ fun p _ => ?_
    refine Submodule.smul_mem _ _ ?_
    have h2 : R.gW i (sg0 D A) (p : G) w ∈ (GlobalTheory.Hk3.Wcc R SF i c).map (R.gW i (sg0 D A) (p : G)) :=
      Submodule.mem_map_of_mem hw
    exact hstab c (p : G) h2
  have hfix : π x = (Fintype.card (F.lvl b).P : ℂ) • x := by
    have h1 : ∀ p : (F.lvl b).P, (lam p)⁻¹ • R.gW i (sg0 D A) (p : G) x = x := fun p => by
      rw [hxt' p, smul_smul, inv_mul_cancel₀ (lam_ne p), one_smul]
    rw [hπ, Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hπx : π x ≠ 0 := by
    intro h0
    apply hx0
    have hc : (Fintype.card (F.lvl b).P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have h3 := congrArg (fun z => (Fintype.card (F.lvl b).P : ℂ)⁻¹ • z) (hfix.symm.trans h0)
    rwa [smul_zero, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
  have hxR := hsup.ge (LinearMap.mem_range.2 ⟨x, hxe⟩)
  have hmem := (Submodule.map_iSup π (fun c => GlobalTheory.Hk3.Wcc R SF i c)).le (Submodule.mem_map_of_mem (f := π) hxR)
  by_contra hall
  push_neg at hall
  have hbot : ∀ c, (GlobalTheory.Hk3.Wcc R SF i c).map π = ⊥ := by
    intro c
    rw [eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    have hz : π w ∈ GlobalTheory.Hk3.Wcc R SF i c := hπmem c w hw
    have he : GlobalTheory.Hk3.eH R i (π w) = π w := by
      obtain ⟨u, hu⟩ := LinearMap.mem_range.1 (hsup.le (Submodule.mem_iSup_of_mem c hz))
      rw [← hu, ← Module.End.mul_apply, hidem]
    by_contra h0
    exact hall c (π w) hz h0
      ((GlobalTheory.WatType.wat_iff_type R F hs hC b i _).2 ⟨he, fun p => by rw [htype w p, hlam]⟩)
  simp only [hbot, iSup_bot, Submodule.mem_bot] at hmem
  exact hπx hmem

theorem rowsNe : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF → (∀ b, ∃ i, R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥) → RowsNe R F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hs hC hS SF hSF hTR hW b
  obtain ⟨i, hi⟩ := hW b
  obtain ⟨c, z, hzc, hz0, hzW⟩ := exists_part R F hs hC hS SF hSF b i hi
  have hinj := (hC.models.HW i (sg0 D A)).1
  have hez : (R.HW i (sg0 D A)).e z ≠ 0 := fun h => hz0 (hinj (h.trans (map_zero _).symm))
  have hzc' := (Submodule.mem_inf.1 (Submodule.mem_comap.1 hzc)).2
  have hpart : (R.HW i (sg0 D A)).e z ∈ GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A))
      (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A))))
      (R.eWf i (sg0 D A)) SF c := by
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hzW).1, ?_⟩, hzW⟩
    have h1 := (Submodule.mem_inf.1 hzc').2
    simp only [Submodule.mem_iInf] at h1 ⊢
    exact fun P d B hB => h1 P d B (GlobalTheory.T.heckeOperator_faceLevel_eq_principalLevel R F hC SF hSF b i P d B hB)
  have hne : GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A))
      (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A))))
      (R.eWf i (sg0 D A)) SF c ≠ ⊥ := fun h => hez ((Submodule.mem_bot ℂ).1 (h ▸ hpart))
  have hr := (hTR i).2 b c
  intro hE
  apply hne
  rw [← Submodule.rank_eq_zero, ← hr, Submodule.rank_eq_zero]
  exact eq_bot_iff.2 (inf_le_right.trans hE.le)

end GlobalTheory.RowsNeProof

end
end

