import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0076
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0102
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0101
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0095
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EqOfOrbitNormal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFourth
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0098
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0024
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPermOfRange
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0099
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothConjInvariantMetricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_conj_invariant_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (a : K → ℤ), ∃ A : HermLine J, A.a = a ∧ IsSmoothHerm A ∧ IsConjInvariantH A := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric | exact GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsLogResolution
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (cst : ℝ), IsNormFn M τ a k₀ ca cb RW (fun x => logNormSec L' v x + cst) → ∀ (U : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) → (∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)) → ∃ α : ℕ → Ψ × Fin N → (Fin d → ℂ) → ℝ, (∀ m, ∀ w ∈ U m, (G m w).PosDef) ∧ (∀ m r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G m w r s) (U m)) ∧ (∀ m p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (α m p) (U m)) ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = xiPot (G m (Fin.tail z')) (z' 0) + (Hh z').re) ∧ (∀ m p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = α m p (Fin.tail z') + (Hh z').re) ∧ ∀ m (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U m → z 0 ≠ z 1 → logNormSec L' v (ΦW m z) + cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦW m z)) + (FA.S.comap some).ph p (q 1 (ΦW m z))) = logSin (G m (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hcase hblk hca hcb RW q hq h0 h1 L' v cst hnorm U G ΦY ΦW hU hC
  have hC' := fun m => (isFibreChart_iff FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)).1 (hC m)
  choose l H bp hD using hC'
  refine ⟨fun m => alphaOf BM (l m) (H m) (bp m), fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · exact GlobalTheory.T.two_point_fibre_chart_second K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_third K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_fourth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_sixth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_seventh K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_twisted_resolution K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb k₀ hblk RW q h0 h1 _ hnorm (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionAltBis
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_alt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e) (F : FrameData ι Ψ N M.Ω M.blk) (H : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), x ∈ ψ.source → IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H → ∃ (V : Set RW.X) (z₀ z₁ : RW.X → (Σ k, ι k) → ℂ) (c : Option K → RW.X → ℂ), IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ V ⊆ RW.U x ∧ (∀ q, RW.A.HoloOn V fun w => z₀ w q) ∧ (∀ o, RW.A.HoloOn V (c o)) ∧ (∀ o, ∀ w ∈ V, c o w ≠ 0) ∧ ∀ w ∈ V, SameOrbit (z₀ w) (fstPt k₀ (RW.lift w w)) ∧ SameOrbit (z₁ w) (sndPt k₀ (RW.lift w w)) ∧ (∀ τ' i, M.ExactAt F (τ', i) (z₀ w) (H τ' (ψ w)) ∧ M.ExactAt F (τ', i) (z₁ w) (if τ' = τ then H τ (ψ w) * (1 + Matrix.single cb ca (ψ w i₀)) else H τ' (ψ w))) ∧ (∀ q : Σ k, ι k, q.1 ≠ k₀ → z₁ w q = z₀ w q) ∧ (∀ q : Σ k, ι k, RW.lift x w ⟨some q.1, q.2⟩ = c (some q.1) w * z₀ w q) ∧ ∀ m : ι k₀, RW.lift x w ⟨none, m⟩ = c none w * z₁ w ⟨k₀, m⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFourthStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_arithmetic_fourth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∃ (D : MRing (baseIdx ι M.blk)) (a : NonPluckerBlocks M.blk → ℕ), IsMultiHomog D a ∧ D ∉ mCoordIdeal M.x ∧ ∀ zb ∈ mcPts (mCoordIdeal M.x), eval zb (map (Int.castRingHom ℂ) D) ≠ 0 → (GroundTheory.Heights₂.Heights.Inter.ptsOverPt (mCoordIdeal M'.x) Cv.v zb).ncard = Cv.deg := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BaseCount.base_count | exact GlobalTheory.CompanionTheory.Ar.PB.BaseCount.base_count | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BaseCount.base_count <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBaseBlockValueStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_base_block_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (kb : NonPluckerBlocks M.blk), z₁ ∈ mcPts (mCoordIdeal y') → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → ∃ (e : Φ') (s : ι kb.1 → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i, transPt Cv ⟨kb.1, i⟩ = e * s i ∧ IsValueAt y' (s i) z₁ (t * z₀ ⟨kb.1, i⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.transPt_block_base | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.transPt_block_base | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.transPt_block_base <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtBasePointStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_frames_at_base_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal zb) → M.GoodAt F (mCoordIdeal (zb ∘ Cv.v)) → ∀ (p : Ψ × Fin N) (q : Σ k, ι k) (r : Σ k, ι' k), RegAt M'.x (mCoordIdeal zb) (coE Cv F' F p q r) ∧ valAt M'.x (coE Cv F' F p q r) zb = ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2), valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' * valAt M'.x (F'.u' I' r) zb := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.coE_regAt_valAt | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.coE_regAt_valAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.coE_regAt_valAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtPointStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_frames_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), z ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), M'.GoodAt F' (mCoordIdeal (basePart M'.blk z')) ∧ M.GoodAt F (mCoordIdeal (basePart M'.blk z' ∘ Cv.v)) ∧ f z' = CovMap.LocImg.img Cv F' F z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An.main | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesPullbackStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_frames_pullback : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), M'.IsFrame F' → M.IsFrame F → (∀ k, M'.x ⟨k, F'.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K) (k' : K'), M.blk p = some k → M'.blk p = some k' → ∃ c : Φ', c ≠ 0 ∧ ∀ m : ι k, transPt Cv ⟨k, m⟩ = c * ∑ m' : ι' k', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * y' ⟨k', m'⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr.transPt_eq_smul_sum | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr.transPt_eq_smul_sum | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr.transPt_eq_smul_sum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDomainCellCoordinates
section
open MeasureTheory Filter Topology Matrix NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.OrthBridge

def headEquiv {r k : ℕ} (hk : k ≤ r) : Fin k ≃ {a : Fin r // (a : ℕ) < k} where
  toFun a := ⟨Fin.castLE hk a, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem submatrix_neg_transpose {r k : ℕ} (hk : k ≤ r) (s : Fin r → ℝ) (n : Matrix (Fin r) (Fin r) ℂ) :
    (-(gramOf s n)ᵀ).submatrix (Fin.castLE hk) (Fin.castLE hk) =
      ((-gramHead s k n).submatrix (headEquiv hk) (headEquiv hk))ᵀ := by
  ext a b; rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem Gw_eq (X : Data E r) {j : ℕ} (hp : X.p0 = r - j) (w : ReciprocityTheory.L2DbarEstimates.V (nd X)) (τ : X.Ψ) :
    PoinPf.Gw X w τ = -(gramOf (sigForm r j) (mat (nmat X w) τ))ᵀ := by
  have hs : PoinPf.Jd X = -diagonal (fun i => ((sigForm r j i : ℝ) : ℂ)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [PoinPf.Jd, sgn, sigForm, hp]
      split_ifs <;> simp
    · simp [PoinPf.Jd, hab]
  have hc : ((mat (nmat X w) τ)ᴴ)ᵀ = (mat (nmat X w) τ).map (starRingEnd ℂ) := by
    ext a b; rfl
  rw [PoinPf.Gw, hs, gramOf, Matrix.transpose_mul, Matrix.transpose_mul, diagonal_transpose, hc]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem gram_cpt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : ReciprocityTheory.L2DbarEstimates.V (nd X)) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (cpt X x w) τ) = PoinPf.Gw X w τ := by
  show gram τ.1 X.Gm (mat x τ * mat (nmat X w) τ) = _
  rw [FrameDegreeData.gram_mul, hx τ]
  rfl

theorem norm_dmin_eq (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {j : ℕ} (hp : X.p0 = r - j)
    (w : ReciprocityTheory.L2DbarEstimates.V (nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm (cpt X x w) τ i‖ = ‖(gramHead (sigForm r j) i (mat (nmat X w) τ)).det‖ := by
  have hi : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  rw [PoinPf.dmin_cpt_orth X hx, lminor, Gw_eq X hp, submatrix_neg_transpose hi, det_transpose,
    det_submatrix_equiv_self, Matrix.det_neg]
  simp

theorem gramPos_iff (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {j : ℕ} (hp : X.p0 = r - j)
    (w : ReciprocityTheory.L2DbarEstimates.V (nd X)) (τ : X.Ψ) :
    (X.gramPos (cpt X x w) τ).PosDef ↔ (-gramHead (sigForm r j) X.p0 (mat (nmat X w) τ)).PosDef := by
  have h : X.gramPos (cpt X x w) τ =
      ((-gramHead (sigForm r j) X.p0 (mat (nmat X w) τ)).submatrix (headEquiv X.p0_le) (headEquiv X.p0_le))ᵀ := by
    rw [← submatrix_neg_transpose, ← Gw_eq X hp, ← gram_cpt X hx]
    rfl
  rw [h]
  constructor
  · intro hP
    have h1 := hP.transpose
    rw [transpose_transpose] at h1
    have h2 := h1.submatrix (e := (headEquiv X.p0_le).symm) (headEquiv X.p0_le).symm.injective
    simpa using h2
  · intro hP
    exact (hP.submatrix (e := headEquiv X.p0_le) (headEquiv X.p0_le).injective).transpose

section Coord

variable {Ψ : Type} [Fintype Ψ] {e : ℕ}

def sig (X : Data E r) (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) : Fin (nd X) ≃ Fin e :=
  ((Fintype.equivFin (Ent X)).symm.trans (Equiv.prodCongr lab (Equiv.refl _)).symm).trans q

def toChart (X : Data E r) (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) :
    (Fin e → ℂ) ≃ᵐ ReciprocityTheory.L2DbarEstimates.V (nd X) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (nd X) => ℂ) (sig X lab q).symm).trans
    (MeasurableEquiv.toLp 2 (Fin (nd X) → ℂ))

theorem toChart_apply (X : Data E r) (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) (z : Fin e → ℂ) :
    toChart X lab q z = (WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr lab (Equiv.refl _)).symm
      ((Fintype.equivFin (Ent X)).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd X)) := by
  ext i
  simp [toChart, sig, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

theorem toChart_preserving (X : Data E r) (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) :
    MeasurePreserving (toChart X lab q) volume volume := by
  have hl : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (nd X) → ℂ)).symm :=
    GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))
  exact hl.symm.comp (volume_measurePreserving_piCongrLeft (fun _ : Fin (nd X) => ℂ) (sig X lab q).symm)

theorem mat_nmat_toChart (X : Data E r) (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) (z : Fin e → ℂ) (t : Ψ) :
    mat (nmat X (toChart X lab q z)) (lab t) = lowMat q z t := by
  ext a b
  rw [toChart_apply]
  simp only [mat, nmat, lowMat, Matrix.of_apply]
  split_ifs with h
  · simp [PiLp.toLp_apply]
  · rfl
  · rfl

theorem mem_iff (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {j : ℕ} (hp : X.p0 = r - j)
    (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) (z : Fin e → ℂ) :
    z ∈ cellDom j q ↔ toChart X lab q z ∈ OmF X x0 := by
  constructor
  · intro hz
    show cpt X x0 _ ∈ X.dom
    refine ExF.mem_dom_of_gramPos X fun τ => ?_
    obtain ⟨t, rfl⟩ := lab.surjective τ
    have h := hz t
    rw [InFlagDomain, ← mat_nmat_toChart X lab q z t, ← hp] at h
    refine ⟨?_, (gramPos_iff X ho hp _ _).2 h.2⟩
    show (mat x0 _ * mat (nmat X _) _).det ≠ 0
    rw [det_mul]
    exact mul_ne_zero (KU.orth_dom X ho _).1 h.1.ne_zero
  · intro hz t
    have hz' : cpt X x0 (toChart X lab q z) ∈ X.dom := hz
    have hd : (mat x0 (lab t) * mat (nmat X (toChart X lab q z)) (lab t)).det ≠ 0 := (hz' (lab t)).1
    have hP := (gramPos_iff X ho hp _ _).1 (X.gramPos_posDef hz' (lab t))
    rw [det_mul] at hd
    rw [mat_nmat_toChart] at hP hd
    rw [InFlagDomain, ← hp]
    exact ⟨isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hd), hP⟩

theorem dens_eq (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {j : ℕ} (hp : X.p0 = r - j)
    (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) {z : Fin e → ℂ} (hz : toChart X lab q z ∈ OmF X x0) :
    densF X x0 (toChart X lab q z) = cellDens j q z := by
  unfold densF cellDens
  rw [← Equiv.prod_comp lab]
  refine Finset.prod_congr rfl fun t _ => Finset.prod_congr rfl fun i _ => ?_
  have hz' : cpt X x0 (toChart X lab q z) ∈ X.dom := hz
  have hne : dmin X.Gm (cpt X x0 (toChart X lab q z)) (lab t) i.castSucc ≠ 0 := by
    intro h0
    have h1 := (hz' (lab t)).2 i.castSucc
    rw [h0] at h1
    simp at h1
  have hn := norm_dmin_eq X ho hp (toChart X lab q z) (lab t) i.castSucc
  rw [mat_nmat_toChart, Fin.val_castSucc] at hn
  have hd : 0 < ‖(gramHead (sigForm r j) i (lowMat q z t)).det‖ := by
    rw [← hn]; exact norm_pos_iff.2 hne
  rw [hn, gramLog, show (-4 : ℝ) * (1 / 2 * Real.log ‖(gramHead (sigForm r j) i (lowMat q z t)).det‖) =
      Real.log ‖(gramHead (sigForm r j) i (lowMat q z t)).det‖ * ((-2 : ℤ) : ℝ) by push_cast; ring,
    ← Real.rpow_def_of_pos hd, Real.rpow_intCast]

theorem muF_eq (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {j : ℕ} (hp : X.p0 = r - j)
    (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) {FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X))}
    (hFF : MeasurableSet FF) (hsub : FF ⊆ OmF X x0) :
    muF X x0 FF = cellVol j q (toChart X lab q ⁻¹' FF) := by
  have hM := toChart_preserving X lab q
  rw [muF, withDensity_apply _ hFF, Measure.restrict_restrict hFF, Set.inter_eq_left.2 hsub, cellVol,
    ← hM.setLIntegral_comp_preimage_emb (toChart X lab q).measurableEmbedding]
  refine setLIntegral_congr_fun ((toChart X lab q).measurable hFF) fun z hz => ?_
  simp only [dens_eq X ho hp lab q (hsub hz)]

end Coord

end GlobalTheory.CompanionTheory.Ar.Cmp.OrthBridge

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem muF_orth_eq_cellVol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j e : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (Ψ : Type) [Fintype Ψ] (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e), IsOrth X x0 → j ≤ r → X.p0 = r - j → (∀ z : Fin e → ℂ, z ∈ cellDom j q ↔ (WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr lab (Equiv.refl _)).symm ((Fintype.equivFin (Ent X)).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd X)) ∈ OmF X x0) ∧ ∀ FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X)), MeasurableSet FF → FF ⊆ OmF X x0 → muF X x0 FF = cellVol j q {z | (WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr lab (Equiv.refl _)).symm ((Fintype.equivFin (Ent X)).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd X)) ∈ FF} := by
  intro E _ _ _ r j e X x0 Ψ _ lab q ho _ hp
  refine ⟨fun z => ?_, fun FF hFF hsub => ?_⟩
  · rw [← OrthBridge.toChart_apply]
    exact OrthBridge.mem_iff X ho hp lab q z
  · have h : {z : Fin e → ℂ | (WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr lab (Equiv.refl _)).symm ((Fintype.equivFin (Ent X)).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd X)) ∈ FF} = OrthBridge.toChart X lab q ⁻¹' FF := by
      ext z
      rw [Set.mem_preimage, OrthBridge.toChart_apply]
      rfl
    rw [h]
    exact OrthBridge.muF_eq X ho hp lab q hFF hsub

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapSameBaseOrbit
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem stepGap_eq_of_base_block : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (x₀ : BM.Rb.X) (z z' : (Σ k, ι k) → ℂ), x₀ ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z' ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → basePart M.blk z = basePart M.blk z' → (∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = z' ⟨k, m⟩) → stepGap M BM p z = stepGap M BM p z' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p x₀ z z' hx₀ hz hz' horb hbase hblk
  obtain ⟨l, hl⟩ := BM.O_cover x₀
  have hx : x₀ ∈ BM.O l \ ReciprocityTheory.AnForm.P.bdry BM.s := ⟨hl, hx₀⟩
  have horb' : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (GlobalTheory.CompanionTheory.Ar.PB.basePart M.blk z') (BM.Rb.lift x₀ x₀) := by
    rw [← hbase]
    exact horb
  have hbm : GlobalTheory.CompanionTheory.Ar.PB.StepW.baseMono M (BM.F l) p z = GlobalTheory.CompanionTheory.Ar.PB.StepW.baseMono M (BM.F l) p z' := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.StepW.baseMono
    rw [hbase]
  have hfs : (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm ι (M.dy p)).h z =
      (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm ι (M.dy p)).h z' := by
    show GroundTheory.Heights₂.Heights.LowerBoundFree.refNorm (M.dy p) z =
      GroundTheory.Heights₂.Heights.LowerBoundFree.refNorm (M.dy p) z'
    unfold GroundTheory.Heights₂.Heights.LowerBoundFree.refNorm
    refine Finset.prod_congr rfl (fun k _ => ?_)
    by_cases h0 : M.dy p k = 0
    · simp [h0]
    · have hcoord : ∀ i, z ⟨k, i⟩ = z' ⟨k, i⟩ := by
        intro i
        by_cases hk : M.blk p = some k
        · exact hblk k hk i
        · by_cases hb : ∀ p' : Ψ × Fin N, M.blk p' ≠ some k
          · exact congrFun hbase ⟨⟨k, hb⟩, i⟩
          · exfalso
            apply h0
            unfold GlobalTheory.CompanionTheory.Ar.PB.FlagModel.dy
            rw [dif_neg hb, if_neg hk]
      simp only [hcoord]
  have hh : Real.log ((BM.hom p).h z) = Real.log ((BM.hom p).h z') := by
    cases hp : M.blk p with
    | none =>
      rw [GlobalTheory.T.log_block_metric_off_boundary K ι Φ y Ψ N j M n BM p l x₀ z hp hx hz horb,
        GlobalTheory.T.log_block_metric_off_boundary K ι Φ y Ψ N j M n BM p l x₀ z' hp hx hz' horb', hbm, hbase]
    | some k₀ =>
      obtain ⟨I₀, hI₀, hne⟩ := GlobalTheory.T.block_metric_row_echelon_local K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hl hz horb
      obtain ⟨C, B, hCB⟩ := GlobalTheory.CompanionTheory.Ar.PB.StepW.GrChart.exists_isGrChart N j p.2 I₀ M.j_le hI₀
      have hfun : GlobalTheory.CompanionTheory.Ar.PB.StepW.plk M (BM.F l) k₀ z = GlobalTheory.CompanionTheory.Ar.PB.StepW.plk M (BM.F l) k₀ z' := by
        funext I
        unfold GlobalTheory.CompanionTheory.Ar.PB.StepW.plk
        rw [hbase]
        simp only [hblk k₀ hp]
      have hne' : GlobalTheory.CompanionTheory.Ar.PB.StepW.plk M (BM.F l) k₀ z' I₀ ≠ 0 := by
        rw [← hfun]
        exact hne
      rw [GlobalTheory.T.block_metric_explicit_matrix_form K ι Φ y Ψ N j M n BM p k₀ l x₀ z I₀ C B hp hCB hx hz horb hne,
        GlobalTheory.T.block_metric_explicit_matrix_form K ι Φ y Ψ N j M n BM p k₀ l x₀ z' I₀ C B hp hCB hx hz' horb' hne', hfun, hbm]
  unfold GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap
  rw [hh, hfs]

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMapStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_change_under_field_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₂ : Type) [Field Ω₂] (x₂ : (Σ k, ι₂ k) → Ω₂) (φ : M.Ω →+* Ω₂) (zb : (Σ k, ι₂ k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal x₂) → M.IsFrame F₁ → M.IsFrame F₂ → (∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F₂.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → (∀ (m : ι k) (I : Finset (Fin N)), RegAt x₂ (mCoordIdeal zb) (φ (F₁.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₁.u' I ⟨k, m⟩)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u' I ⟨k, m⟩))) → (∀ a b, RegAt x₂ (mCoordIdeal zb) ((((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) a b) ∧ RegAt x₂ (mCoordIdeal zb) ((((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) a b)) → ∃ c : ℂ, c ≠ 0 ∧ ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → ∀ m : ι k, ∑ I, valAt x₂ (φ (F₁.u ⟨k, m⟩ I)) zb * minorIJ (CovMap.LocImg.valMat x₂ zb (((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) * h) I (stepCols N j p.2) = c * ∑ I, valAt x₂ (φ (F₂.u ⟨k, m⟩ I)) zb * minorIJ h I (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.main | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfProjectionAndFibreDimStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | exact GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | (intros; apply GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim <;> assumption)
end

