import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0007
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0015
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFamilyExistsOnEigenspace
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V), 2 * Fintype.card Ψ = Module.finrank ℚ E → (∃ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v) ∧ ∀ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v → ∀ s, ∃ (k : ℕ) (q : Fin k → A.Λ), (∀ c, (q c : V) ∈ A.eig s) ∧ A.IsAdapted s v q ∧ r + k = Module.finrank L (eigSp A.ρ (A.σ s)) ∧ A.Bq.rank (A.img s) = k ∧ ∀ ι, 0 < A.gramDet ι q := by
  first | exact @LevelTowerAlt.orthogonal_family_adapted_basis | exact LevelTowerAlt.orthogonal_family_adapted_basis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticVarietyGenericFibreProjective
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem varieties_over_rat_arith_contract : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (n : ℕ), (∀ V : Ideal (MRingOver ℚ ι), Nonempty K → IsProjVarF V n → IsArithVar (V.comap (MvPolynomial.map (Int.castRingHom ℚ))) (n + 1) ∧ (V.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = V) ∧ ∀ P : Ideal (MRing ι), IsArithVar P (n + 1) → IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) n ∧ (P.map (MvPolynomial.map (Int.castRingHom ℚ))).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P :=
  @PositivityTheory.Xgp.t_contract

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseFunctionValueAtPointStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_function_value_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (z : (Σ k, ι k) → ℂ) (s : M.Ω), z ∈ mcPts (mCoordIdeal y) → basePart M.blk z ∈ mcPts (mCoordIdeal M.x) → RegAt M.x (mCoordIdeal (basePart M.blk z)) s → IsValueAt y (algebraMap M.Ω Φ s) z (valAt M.x s (basePart M.blk z)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_of_base | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_of_base | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_of_base <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricVectorLogResolutionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_metric_vector_log_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P' J' : Ideal (MRing ι')) (e : ℕ) (R' : AnLogRes P' J' e), J' = ⊤ → ∀ (l : Fin BM.q) (vec : BM.Rb.X → (Ψ → Matrix (Fin N) (Fin N) ℂ) → (Σ k, ι' k) → ℂ) (T : Ψ → Matrix (Fin N) (Fin N) ℂ), (∀ τ', IsLowerUni (T τ')) → (∀ (m : ℕ) (V : Set (Fin m → ℂ)) (bp : (Fin m → ℂ) → BM.Rb.X) (hh : Ψ → (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ), IsOpen V → ContinuousOn bp V → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ u ∈ V, bp u ∈ BM.O l) → (∀ τ' r s, AnalyticOnNhd ℂ (fun u => hh τ' u r s) V) → (∀ u ∈ V, ∀ τ', IsBlockDiag j (hh τ' u) ∧ (hh τ' u).det ≠ 0) → ∀ q, AnalyticOnNhd ℂ (fun u => vec (bp u) (fun τ' => hh τ' u) q) V) → (∀ b ∈ BM.O l, ∀ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → vec b h ∈ mcPts P') → ∀ (x : R'.X), ∀ b ∈ BM.O l, ∀ h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h₀ τ') ∧ (h₀ τ').det ≠ 0) → SameOrbit (R'.lift x x) (vec b h₀) → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, ∃ b' ∈ BM.O l \ bdry BM.s, ∃ h' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h' τ') ∧ (h' τ').det ≠ 0) ∧ SameOrbit (R'.lift x' x') (vec b' h') ∧ ∀ (τ' : Ψ) (i : Fin N), IsProperStep N j i → minorIJ (h' τ') (stepCols N j i) (stepCols N j i) ≠ 0 ∧ minorIJ (h' τ' * T τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Dens.dens_core | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Dens.dens_core | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Dens.dens_core <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BdryIsAnalyticSubsetInteriorEmpty
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem bdry_isAnalyticSubset_interior_empty : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsSection A L s → IsSNC A L s m W → A.IsAnalyticSubset (bdry s) ∧ interior (bdry s) = ∅ := by
  intro e X _ A L s n m W hS hSNC
  refine ⟨?_, LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC⟩
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hzU⟩
    exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
  · rintro ⟨hzU, hz⟩
    exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagFrameAtGoodPointStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_diag_frame_at_good_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (w : (Σ k, ι k) → ℂ) (H : Ψ → Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → basePart M.blk w ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk w)) → (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) → (∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, w ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk w) p.2 ⟨k, m⟩ (H p.1)) → w ∈ mcPts (mCoordIdeal y) ∧ ∃ z₀, SameOrbit z₀ w ∧ SameOrbit (basePart M.blk z₀) (basePart M.blk w) ∧ M.IsFlagOf F z₀ H := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FlagPt.main | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FlagPt.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FlagPt.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricExplicitMatrixForm
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep

theorem prod_base_split {K : Type} [Fintype K] {σ : Type} (blk : σ → Option K) (p : σ) (k₀ : K)
    (hp : blk p = some k₀) (f : K → ℝ)
    (hf : ∀ k, (¬ ∀ p', blk p' ≠ some k) → k ≠ k₀ → f k = 1) :
    ∏ k, f k = (∏ k : NonPluckerBlocks blk, f k.1) * f k₀ := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ fun k => ∀ p', blk p' ≠ some k]
  congr 1
  · exact Finset.prod_subtype _ (by simp) f
  · refine Finset.prod_eq_single_of_mem k₀ ?_ ?_
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun e => e p hp⟩
    · intro k hk e
      exact hf k (Finset.mem_filter.1 hk).2 e

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ) (I₀ : Finset (Fin N)) (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ), M.blk p = some k₀ → IsGrChart N j p.2 I₀ C B → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → plk M (BM.F l) k₀ z I₀ ≠ 0 → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) (grMat C B I₀ (plk M (BM.F l) k₀ z)) + Real.log ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z I₀ C B hp hC hx hz hor hw
  obtain ⟨h, a, hb, hd, ha, hstep, hzk⟩ := GlobalTheory.T.block_metric_grassmann_chart_local K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hx.1 hz hor
  obtain ⟨hHb, hHd, hHm⟩ := hC h a _ hb hd ha hstep hw
  have hL : BM.Rb.lift x₀ x₀ ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem x₀ x₀ (BM.Rb.mem_U x₀)
  have hor' := hor
  obtain ⟨c0, hc0, e0⟩ := hor'
  have hbz : basePart M.blk z ∈ mcPts (mCoordIdeal M.x) := by
    rw [e0]
    exact ((TorusAct.main _ _ _ M.x _ c0 hc0).2 hL).1
  have hne : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := by
    intro k h0
    have hl : BM.Rb.lift x₀ x₀ ⟨k, (BM.F l).c k⟩ = 0 := by
      have e1 := congrFun e0 ⟨k, (BM.F l).c k⟩
      rw [h0] at e1
      exact (mul_eq_zero.1 e1.symm).resolve_left (hc0 k)
    refine (BM.good l x₀ hx.1).1 k ?_
    show mConeMap (BM.Rb.lift x₀ x₀) (X ⟨k, (BM.F l).c k⟩) = 0
    rw [mConeMap, aeval_X, hl, map_zero, zero_mul]
  let c : K → ℂ := fun k => if hk : ∀ p', M.blk p' ≠ some k then
    (basePart M.blk z ⟨⟨k, hk⟩, (BM.F l).c ⟨k, hk⟩⟩)⁻¹ else if k = k₀ then (plk M (BM.F l) k₀ z I₀)⁻¹ else 1
  have hcb : ∀ k : NonPluckerBlocks M.blk, c k.1 = (basePart M.blk z ⟨k, (BM.F l).c k⟩)⁻¹ := fun k => dif_pos k.2
  have hk₀ : ¬ ∀ p', M.blk p' ≠ some k₀ := fun e => e p hp
  have hck : c k₀ = (plk M (BM.F l) k₀ z I₀)⁻¹ := (dif_neg hk₀).trans (if_pos rfl)
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : ∀ p', M.blk p' ≠ some k
    · rw [hcb ⟨k, hk⟩]
      exact inv_ne_zero (hne ⟨k, hk⟩)
    · by_cases e : k = k₀
      · rw [e, hck]
        exact inv_ne_zero hw
      · rw [show c k = 1 from (dif_neg hk).trans (if_neg e)]
        exact one_ne_zero
  have hz₂ := ((TorusAct.main K ι Φ y z c hc).2 hz).1
  have hval := ((TorusAct.main _ _ _ M.x _ (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc _)).2 hbz).2
  have hbp : basePart M.blk (fun q : Σ k, ι k => c q.1 * z q) =
      fun q : Σ k, baseIdx ι M.blk k => c q.1.1 * basePart M.blk z q := rfl
  have hso : SameOrbit (basePart M.blk (fun q : Σ k, ι k => c q.1 * z q)) (BM.Rb.lift x₀ x₀) := by
    refine ⟨fun k => c k.1 * c0 k, fun k => mul_ne_zero (hc _) (hc0 k), ?_⟩
    rw [hbp, e0]
    funext q
    exact (mul_assoc _ _ _).symm
  have hnorm : ∀ k, basePart M.blk (fun q : Σ k, ι k => c q.1 * z q) ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hbp]
    show c k.1 * basePart M.blk z ⟨k, (BM.F l).c k⟩ = 1
    rw [hcb k, inv_mul_cancel₀ (hne k)]
  have hlog := (BM.induced l x₀ hx p _ hz₂ hso hnorm _ hHb hHd).1 k₀ hp (fun m => by
    rw [hbp, hzk m, hck]
    simp only [hval]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [mul_left_comm a, ← hHm I, mul_left_comm, ← mul_assoc _ _ (plk M (BM.F l) k₀ z I₀), mul_comm _ (plk M (BM.F l) k₀ z I₀),
      mul_inv_cancel_left₀ hw])
  have hs := (BM.hom p).smul c z hc
  rw [BM.hom_deg p] at hs
  have hdy : M.dy p k₀ = 1 := (dif_neg hk₀).trans (if_pos hp)
  have hdy0 : ∀ k, (¬ ∀ p', M.blk p' ≠ some k) → k ≠ k₀ → M.dy p k = 0 := fun k hk e =>
    (dif_neg hk).trans (if_neg fun e' => e (Option.some_injective _ (hp.symm.trans e')).symm)
  have hsplit := prod_base_split M.blk p k₀ hp (fun k => ‖c k‖ ^ M.dy p k)
    (fun k hk e => by simp only [hdy0 k hk e, zpow_zero])
  have hPQ : (∏ k, ‖c k‖ ^ M.dy p k) * ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ = 1 := by
    rw [hsplit, hdy, zpow_one, hck, norm_mul, baseMono, norm_prod, norm_inv]
    simp only [norm_zpow]
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw), mul_one]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [hcb k, norm_inv, _root_.inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ (norm_ne_zero_iff.2 (hne k)))]
  have hpos := (BM.hom p).pos (fun q => c q.1 * z q) hz₂.1
  have hQ : ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ ≠ 0 := fun e => by
    rw [e, mul_zero] at hPQ
    exact zero_ne_one hPQ
  have hh : (BM.hom p).h z =
      ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ * (BM.hom p).h fun q => c q.1 * z q := by
    rw [hs, ← mul_assoc, mul_comm ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖, hPQ, one_mul]
  rw [hh, Real.log_mul hQ hpos.ne', hlog, add_comm]

end GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricRowEchelonLocal
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem stepCols_ne_empty_of_le {N j : ℕ} (hj : j ≤ N) (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro e
  have hN := i.2
  by_cases hi : (i : ℕ) + 1 ≤ j
  · have hlt : N - j < N := by omega
    have hm : (⟨N - j, hlt⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
      omega
    rw [e] at hm
    simp at hm
  · have hlt : 0 < N := by omega
    have hm : (⟨0, hlt⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
      omega
    rw [e] at hm
    simp at hm

theorem exists_plk_ne_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = some k₀ → x₀ ∈ BM.O l → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → ∃ I₀, IsStepRows N j p.2 I₀ ∧ plk M (BM.F l) k₀ z I₀ ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z hp hx hz hO
  obtain ⟨h, a, hb, -, ha, hpl, hzk⟩ := GlobalTheory.T.block_metric_grassmann_chart_local K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hx hz hO
  by_contra hcon
  push_neg at hcon
  have hmin : ∀ I, minorIJ h I (stepCols N j p.2) = 0 := fun I => by
    by_cases hI : IsStepRows N j p.2 I
    · have e := hpl I hI
      rw [hcon I hI] at e
      exact (mul_eq_zero.1 e.symm).resolve_left ha
    · exact ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).2.1 h I hb hI).resolve_right
        (stepCols_ne_empty_of_le M.j_le p.2)
  obtain ⟨m, hm⟩ := hz.1 k₀
  exact hm (by rw [hzk m]; simp [hmin])

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMinorSumFrameIdentityStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_minor_sum_frame_identity : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (S : Type) [CommRing S] (ρ : M.Ω →+* S) (F : FrameData ι Ψ N M.Ω M.blk), M.IsFrame F → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∀ (m : ι k) (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → detFac j p.2 ((F.T p.1).map ρ) * ∑ I, ρ (M.coef ⟨k, m⟩ I) * minorIJ ((F.T p.1).map ρ * h) I (stepCols N j p.2) = ρ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, ρ (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt.frame_identity_map | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt.frame_identity_map | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt.frame_identity_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockTriangularOfProportionalMinorsStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_triangular_of_proportional_minors : ∀ (N j : ℕ) (h g : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j h → IsBlockDiag j g → h.det ≠ 0 → g.det ≠ 0 → (∀ i : Fin N, IsProperStep N j i → ∃ μ : ℂ, ∀ I, minorIJ g I (stepCols N j i) = μ * minorIJ h I (stepCols N j i)) → (h⁻¹ * g).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep.triangular_of_minors_proportional | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep.triangular_of_minors_proportional | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep.triangular_of_minors_proportional <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CauchyBinetSumPositionedMinors
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

theorem bExt_posOf (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (s : Ψ ⊕ Ψ)
    (l : Fin (rk Ψ p q s)) (j : Fin (n s)) : bExt B s (posOf p q s l) j = B s l j := by
  have hinj := (BlockEmbeddings.posOf_strictMono (Ψ := Ψ) (p := p) (q := q) s).injective
  unfold bExt
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun h => hb (hinj h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aExt_posOf (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ)
    (j : Fin (n s)) (l : Fin (rk Ψ p q s)) : aExt C s j (posOf p q s l) = C s j l := by
  have hinj := (BlockEmbeddings.posOf_strictMono (Ψ := Ψ) (p := p) (q := q) s).injective
  unfold aExt
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun h => hb (hinj h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aExt_of_forall_ne (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ)
    (j : Fin (n s)) {b : Fin (p + q)} (h : ∀ l, posOf p q s l ≠ b) : aExt C s j b = 0 :=
  Finset.sum_eq_zero fun l _ => if_neg (h l)

theorem bExt_mul_aExt_row (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (hBC : ∀ s, B s * C s = 1) (s : Ψ ⊕ Ψ)
    (l : Fin (rk Ψ p q s)) (b : Fin (p + q)) :
    (bExt B s * aExt C s) (posOf p q s l) b = (1 : Matrix (Fin (p + q)) (Fin (p + q)) Ω) (posOf p q s l) b := by
  have hinj := (BlockEmbeddings.posOf_strictMono (Ψ := Ψ) (p := p) (q := q) s).injective
  rw [Matrix.mul_apply]
  simp only [bExt_posOf]
  by_cases hb : ∃ l', posOf p q s l' = b
  · obtain ⟨l', rfl⟩ := hb
    simp only [aExt_posOf]
    have h := congrFun (congrFun (hBC s) l) l'
    rw [Matrix.mul_apply] at h
    rw [h]
    by_cases e : l = l'
    · subst e
      simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne fun h' => e (hinj h')]
  · have hb' : ∀ l', posOf p q s l' ≠ b := fun l' h' => hb ⟨l', h'⟩
    simp only [aExt_of_forall_ne C s _ hb', mul_zero, Finset.sum_const_zero]
    rw [Matrix.one_apply_ne (hb' l)]

theorem sum_strictMono_eq {M : Type} [AddCommMonoid M] {d m : ℕ} (f : (Fin d → Fin m) → M)
    (hf : ∀ J, ¬ StrictMono J → f J = 0) :
    ∑ J, f J = ∑ s : GroundTheory.PAdicHodge.KSubset m d, f s.emb := by
  classical
  symm
  refine Fintype.sum_of_injective (fun s : GroundTheory.PAdicHodge.KSubset m d => (s.emb : Fin d → Fin m))
    ?_ _ _ ?_ fun _ => rfl
  · intro s s' h
    have h' : Set.range s.emb = Set.range s'.emb := congrArg Set.range h
    rw [GroundTheory.PAdicHodge.KSubset.range_emb, GroundTheory.PAdicHodge.KSubset.range_emb] at h'
    exact Subtype.ext (Finset.coe_injective h')
  · intro J hJ
    refine hf J fun hm => hJ ?_
    have hc : (Finset.univ.image J).card = d := by
      rw [Finset.card_image_of_injective _ hm.injective]
      simp
    refine ⟨⟨Finset.univ.image J, hc⟩, ?_⟩
    exact (Finset.orderEmbOfFin_unique hc (fun x => by simp) hm).symm

theorem sum_sMin_mul_cMin : ∀ {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω)
    (hBC : ∀ s, B s * C s = 1) (t : StepIx Ψ p q) (I I' : Finset (Fin (p + q)))
    (hI : I.card = (t.2 : ℕ) + 1) (hI' : I'.card = (t.2 : ℕ) + 1)
    (hp : ∀ a ∈ I, ∃ l, posOf p q t.1 l = a) (hp' : ∀ a ∈ I', ∃ l, posOf p q t.1 l = a),
    ∑ J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1), sMin B t I J * cMin C t J I' = if I = I' then 1 else 0 := by
  intro Ψ p q Ω _ n C B hBC t I I' hI hI' hp _
  classical
  rw [sum_strictMono_eq (fun J => sMin B t I J * cMin C t J I') (fun J hJ => by
    simp only [sMin, if_neg hJ, zero_mul])]
  have hterm : ∀ s : GroundTheory.PAdicHodge.KSubset (n t.1) ((t.2 : ℕ) + 1),
      sMin B t I s.emb * cMin C t s.emb I' =
        (((bExt B t.1).submatrix (I.orderEmbOfFin hI) id).submatrix id s.emb).det *
          (((aExt C t.1).submatrix id (I'.orderEmbOfFin hI')).submatrix s.emb id).det := by
    intro s
    simp only [sMin, if_pos s.emb.strictMono, bMin, cMin, dif_pos hI, dif_pos hI']
    rfl
  simp only [hterm]
  rw [← GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  have hmat : (bExt B t.1).submatrix (I.orderEmbOfFin hI) id * (aExt C t.1).submatrix id (I'.orderEmbOfFin hI') =
      (1 : Matrix (Fin (p + q)) (Fin (p + q)) Ω).submatrix (I.orderEmbOfFin hI) (I'.orderEmbOfFin hI') := by
    ext x y
    obtain ⟨l, hl⟩ := hp _ (Finset.orderEmbOfFin_mem I hI x)
    have h := bExt_mul_aExt_row C B hBC t.1 l (I'.orderEmbOfFin hI' y)
    rw [hl] at h
    simpa [Matrix.mul_apply] using h
  rw [hmat]
  by_cases e : I = I'
  · subst e
    rw [if_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin hI).injective, Matrix.det_one]
  · rw [if_neg e]
    have hns : ¬ I ⊆ I' := fun hs => e (Finset.eq_of_subset_of_card_le hs (by omega))
    obtain ⟨a, ha, ha'⟩ := Finset.not_subset.1 hns
    have hr : a ∈ Set.range (I.orderEmbOfFin hI) := by
      rw [Finset.range_orderEmbOfFin]
      exact ha
    obtain ⟨x, rfl⟩ := hr
    refine Matrix.det_eq_zero_of_row_eq_zero x fun y => ?_
    rw [Matrix.submatrix_apply]
    refine Matrix.one_apply_ne fun h => ha' ?_
    rw [h]
    exact Finset.orderEmbOfFin_mem _ _ _

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjectionTwistedStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_chart_product_projection_twisted : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ (∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i) ∧ ∀ y ∈ ψ'.source, ∀ i, (∀ l, σ l ≠ i) → ψ' y i = ψ y i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap_keep | exact GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap_keep | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap_keep <;> assumption)
end

