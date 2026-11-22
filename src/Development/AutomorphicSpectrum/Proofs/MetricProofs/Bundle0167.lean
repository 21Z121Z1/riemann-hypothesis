import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0166
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0163
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0130
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0142
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0165
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0113
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFlAn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothContinuous
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.OfMoriwakiFibreNormPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0115
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0147
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegrableChartAbsDensity
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCompatiblePullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareSystemPolarVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapSquareSystem
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem ansq_exists : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∃ (Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a)) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (e : RW.X → Q.SW.X), HoloMap RW.A Q.SW.A e ∧ IsDegreeOff Q.SW.A RW.A e 1 ∅ ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) fun p => RW.lift x x ⟨some p.1, p.2⟩) ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 1 (e x) → ∃ z₁, SameOrbit (FA.Re.R.lift x₀ x₀) z₁ ∧ (∀ p : (Σ k, ι k), p.1 ≠ k₀ → z₁ p = RW.lift x x ⟨some p.1, p.2⟩) ∧ ∀ m : ι k₀, z₁ ⟨k₀, m⟩ = RW.lift x x ⟨none, m⟩) ∧ (Function.Injective fun w => (Q.q 0 w, Q.q 1 w)) ∧ ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) F (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → (∀ x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₀) → (∀ x₀, FA.Re.π x₀ = Q.q 1 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₁) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 → (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → logNormSec Q.L' Q.v (e x) + Q.cst = Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1) else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) := by
  intro hin K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb har
  have hdim := GlobalTheory.T.flag_analytic_dimension_count K ι Φ y Ψ N j M n d BM FA
  obtain ⟨RW, pr, hpr, hbase, hch⟩ := GlobalTheory.T.flag_adjacent_rows_resolution K ι Φ y Ψ N j M n d BM.Rb τ a b k₀ ca cb hb hs hk hca hcb har hdim
  obtain ⟨q, hq, hpq, hl0, hl1, hinj, hbp⟩ :=
    GlobalTheory.T.flag_adjacent_rows_analytic K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb har RW pr hpr hbase
  have hch' : ∀ x, ∃ (ψ : OpenPartialHomeomorph RW.X (Fin (d + 2) → ℂ)) (kb : Fin BM.Rb.A.n) (σ : Fin n ↪ Fin (d + 2)),
      IsCompatChart RW.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (BM.Rb.A.chart kb).source ∧
        ∀ i, BM.Rb.A.chart kb (pr x') i = ψ x' (σ i)) := fun x => by
    obtain ⟨ψ, kb, σ, i₀, F, H, hx, h1, -, -, h4, -⟩ := hch x
    exact ⟨ψ, kb, σ, h1, hx, h4⟩
  obtain ⟨pL, sL, nL, -⟩ := GlobalTheory.T.snc_adapted_atlas_projection (d + 2) n RW.X BM.Rb.X RW.A BM.Rb.A BM.Bat pr hpr BM.L BM.s BM.nb BM.m BM.W
    BM.potL BM.sec BM.snc BM.norm_le hch'
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.T.log_resolution_fubini_study_positive (Option K) (fun o => ι (o.getD k₀)) _ (d + 2) RW
  have hL : ∀ i, (FA.S.comap some).L.pullback (q i) (hq i).1 = BM.L.pullback pr hpr.1 := fun i => by
    show FA.S.L.pullback (q i) (hq i).1 = _
    have e := FA.L_eq
    revert e
    generalize FA.S.L = LL
    intro e
    subst e
    exact pullback_pullback _ _ _ _ _ _ _ (hpq i)
  have hs' : ∀ i, (fun x y => (FA.S.comap some).s (q i x) (q i y)) = fun x y => BM.s (pr x) (pr y) := fun i => by
    funext x y
    show FA.S.s (q i x) (q i y) = _
    rw [FA.s_eq]
    show BM.s ((FA.pr ∘ q i) x) ((FA.pr ∘ q i) y) = _
    rw [hpq i]
  obtain ⟨C₅, C, t₀, ht₀, hmem⟩ := GlobalTheory.T.two_map_pullback_energy (d + 1) (d + 2) (Ψ × Fin N) (FA.S.comap some) RW.X RW.A
    (potOf RW (fsHerm _ fun _ => 1)) (BM.L.pullback pr hpr.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) q hq hin.pullback (hA _ hfs) hΘ pL sL nL (fun x => BM.norm_le (pr x)) hL hs'
  obtain ⟨L', v, Dg, cst, potL', secv, sncv, sncsv, normv, hN⟩ :=
    GlobalTheory.T.flag_adjacent_rows_base_metric K ι Φ y Ψ N j M n d BM τ a b k₀ ca cb hb hs hk hca hcb har RW pr hpr.1 ⟨hpr, hbase, hch⟩
  obtain ⟨U, B, G, ΦY, ΦW, U_open, B_meas, coverY, coverW, ΦY_open, hfc⟩ :=
    GlobalTheory.T.flag_adjacent_rows_dimension K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb hdim RW q hq hl0 hl1 hinj
  obtain ⟨α, G_pos, G_smooth, α_smooth, xi_pot, base_pot, norm_hom⟩ :=
    GlobalTheory.T.flag_adjacent_rows_log_resolution K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW q hq hl0 hl1 L' v cst hN U G ΦY ΦW U_open hfc
  let SW : AnSys (d + 2) (Option (Ψ × Fin N)) :=
    { X := RW.X
      A := RW.A
      Θ := potOf RW (fsHerm _ fun _ => 1)
      L := BM.L.pullback pr hpr.1
      s := fun x y => BM.s (pr x) (pr y)
      nb := BM.nb
      m := BM.m
      W := fun k => pr ⁻¹' BM.W k
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := pL
      sec := sL
      snc := nL
      norm_le := fun x => BM.norm_le (pr x)
      th := fun o => o.elim (((FA.S.comap some).th (τ, a)).pullback (q 1) (hq 1).1)
        fun p => ((FA.S.comap some).th p).pullback (q 0) (hq 0).1
      ph := fun o => o.elim ((FA.S.comap some).ph (τ, a) ∘ q 1) fun p => (FA.S.comap some).ph p ∘ q 0
      phT := fun o => o.elim (fun t => (FA.S.comap some).phT (τ, a) t ∘ q 1)
        fun p t => (FA.S.comap some).phT p t ∘ q 0
      C₅ := C₅
      C := C
      t₀ := t₀
      sing := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).1
        | some p => exact (hmem 0 p).1
      reg := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).2.1
        | some p => exact (hmem 0 p).2.1
      c2 := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).2.2
        | some p => exact (hmem 0 p).2.2 }
  have hsame : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X), SamePot A Set.univ P P :=
    fun A P x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ _ _ => analyticAt_const, fun y _ => by simp⟩
  let Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a) :=
    { eps_a₀ := by simp [xiCoef]
      SW := SW
      q := q
      holo := hq
      bdry_eq := fun i => by
        ext x
        show BM.s (pr x) (pr x) ≠ 0 ↔ FA.S.s (q i x) (q i x) ≠ 0
        rw [FA.s_eq]
        show _ ↔ BM.s ((FA.pr ∘ q i) x) ((FA.pr ∘ q i) x) ≠ 0
        rw [hpq i]
      t₀_le := ht₀
      th0 := fun p => hsame _ _
      th1 := hsame _ _
      ph0 := fun _ => rfl
      ph1 := rfl
      phase_some_eq_comp_first_projection := fun _ _ => rfl
      phase_none_eq_comp_second_projection := fun _ => rfl
      base_ph := fun p hp => (hbp p hp).1
      base_phT := fun p hp t => (hbp p hp).2 t
      L' := L'
      v := v
      Dg := Dg
      cst := cst
      potL' := potL'
      secv := secv
      sncv := sncv
      sncsv := sncsv
      normv := normv
      U := U
      B := B
      G := G
      α := α
      ΦY := ΦY
      ΦW := ΦW
      U_open := U_open
      B_meas := B_meas
      G_pos := G_pos
      G_smooth := G_smooth
      α_smooth := fun m p => α_smooth m p
      coverY := coverY
      coverW := coverW
      ΦY_open := ΦY_open
      first_projection_chart_compat := fun m z hz => by
        obtain ⟨l, H, bp, -, -, -, -, -, -, h⟩ := hfc m
        exact (h z hz).1
      second_projection_chart_compat := fun m z hz => by
        obtain ⟨l, H, bp, -, -, -, -, -, -, h⟩ := hfc m
        exact (h z hz).2
      xi_pot := xi_pot
      base_pot := base_pot
      norm_hom := norm_hom }
  have hsurj : ∀ w, ∃ x₀, FA.Re.π x₀ = w := fun w => by
    have hd := FA.Re.degree
    rw [FA.deg_one, FA.br_empty] at hd
    obtain ⟨x₀, hx₀⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 w (Set.notMem_empty w))
    exact ⟨x₀, (hx₀ ▸ Set.mem_singleton x₀ : x₀ ∈ FA.Re.π ⁻¹' {w})⟩
  refine ⟨Q, RW, id, ⟨continuous_id, fun j k => RW.A.holo j k⟩, isDegreeOff_id RW.A, hl0, ?_, hinj, ?_⟩
  · intro x x₀ hx
    refine ⟨sndPt k₀ (RW.lift x x), hl1 x x₀ hx, fun p hp => ?_, fun m => ?_⟩
    · show RW.lift x x (v₁ k₀ p) = _
      rw [v₁_ne hp]
    · show RW.lift x x (v₁ k₀ ⟨k₀, m⟩) = _
      rw [v₁_self]
  · intro x z₀ z₁ F h t hF hG h0 h1 hh hd ht hE0 hE1
    obtain ⟨x₀, hx₀⟩ := hsurj (q 0 x)
    obtain ⟨x₁, hx₁⟩ := hsurj (q 1 x)
    exact hN x z₀ z₁ F h t hF hG (orbit_trans (orbit_symm (h0 x₀ hx₀)) (hl0 x x₀ hx₀)) (orbit_trans (orbit_symm (h1 x₁ hx₁)) (hl1 x x₁ hx₁))
      hh hd ht hE0 hE1

end GlobalTheory.CompanionTheory.Ar.PB.WSq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDataFubiniStudy
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_analytic_data_fubini_study : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → bdry BM.s = ∅ → (∀ p, BM.hom p = fsHerm ι (M.dy p)) → ∃ FA : FlagAn BM d, ∀ p t, FA.Re.line (some p) t = fsHerm ι (M.dy p) := by
  first | exact @PositivityTheory.Xgp.t_c_fl_an | exact PositivityTheory.Xgp.t_c_fl_an
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelArithDimensionBoundary
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.ConjOf

theorem flagAn_exists_conj : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → (∀ x x', SameOrbit (BM.Rb.lift x' x') (fun q => starRingEnd ℂ (BM.Rb.lift x x q)) → (x' ∈ bdry BM.s ↔ x ∈ bdry BM.s) ∧ rW BM.L BM.s x' = rW BM.L BM.s x) → (∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry BM.s → SameOrbit (basePart M.blk z) (BM.Rb.lift x x) → (BM.hom p).h (fun q => starRingEnd ℂ (z q)) = (BM.hom p).h z) → ∃ FA : FlagAn BM d, ∀ a t, IsConjInvariantH (FA.Re.line a t) :=
  fun hI K _ ι _ Φ _ y Ψ _ _ N j M n d BM hA hd h1 h2 =>
    flagAn_conj K ι Φ y Ψ N j M n d BM (GlobalTheory.T.flag_model_analytic_data_exists hI K ι Φ y Ψ N j M n d BM hA hd) h1 h2

end GlobalTheory.CompanionTheory.Ar.PB.ConjOf
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeIndexImpliesHeightBound
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem smallCountUpper_of_moriwaki : MoriwakiHSStatement → ArithmeticHilbertSamuelUpperBound := fun hM =>
  GroundTheory.Heights₂.Heights.ForSecondHalf.NefBundleMoriwaki.of_moriwaki hM GlobalTheory.T.packing'

end GlobalTheory.CompanionTheory.Ar.Small
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicAdaptedFrameOnBallStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_adapted_frame_on_ball : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (A₀ : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), C.IsAdapted (F.R 0) A₀ → ∃ (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom F.q) ∧ DifferentiableOn ℂ G (ballDom F.q) ∧ (∀ t ∈ ballDom F.q, ∀ A, C.IsAdapted (F.R t) A → Z t = moebBall F.q (fun τ => C.cinv (A₀ τ) τ * A τ) 0) ∧ ∀ t ∈ ballDom F.q, ballPot F.q (Z t) = ballPot F.q t + (G t).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.chart_exists | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.chart_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.chart_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegrableChartAbsDensityStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_chartAbsDensity : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : MvPolynomial (Fin n) ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ) (R C : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A → f ∉ J →
    (∀ i, GroundTheory.Heights₂.Heights.SmoothNear (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) (φ i)) →
    Integrable (chartAbsDens J A
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x f‖| + C) φ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog.integrable_chartAbsDens_log | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog.integrable_chartAbsDens_log | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog.integrable_chartAbsDens_log <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCompatiblePullbackStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_compatible_pullback : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P J : Ideal (MRing ι)) (P' J' : Ideal (MRing ι')) (D : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (R : AnLogRes P J D) (π : R.X → X) (R' : AnLogRes P' J' D) (h : R'.X → X) (Rel : ((Σ k, ι' k) → ℂ) → ((Σ k, ι k) → ℂ) → Prop) (G : MRing ι) (G₂ : MRing ι') (aG : K → ℕ) (aG₂ : K' → ℕ) (e : ℕ), J = ⊤ → IsArithVar P (D + 1) → IsArithVar P' (D + 1) → HoloMap R.A A π → IsDegreeOff A R.A π 1 ∅ → HoloMap R'.A A h → IsMultiHomog G aG → G ∉ P → IsMultiHomog G₂ aG₂ → G₂ ∉ P' → (∀ z z₁ w w₁, Rel z w → SameOrbit z₁ z → SameOrbit w₁ w → Rel z₁ w₁) → (∀ x x₀, π x₀ = h x → Rel (R'.lift x x) (R.lift x₀ x₀)) → (∀ x x₀, Rel (R'.lift x x) (R.lift x₀ x₀) → π x₀ = h x) → (∀ w ∈ mcPts P, eval w (map (Int.castRingHom ℂ) G) ≠ 0 → {O | ∃ z ∈ mcPts P', O = {z'' | SameOrbit z'' z} ∧ Rel z w}.ncard = e) → (∀ z ∈ mcPts P', z ∈ mcPts J' → ∀ w ∈ mcPts P, Rel z w → eval w (map (Int.castRingHom ℂ) G) = 0) → (∀ z ∈ mcPts P', ∀ w ∈ mcPts P, Rel z w → eval w (map (Int.castRingHom ℂ) G) = 0 → eval z (map (Int.castRingHom ℂ) G₂) = 0) → (∀ z ∈ mcPts P', ∀ w₀ ∈ mcPts P, Rel z w₀ → eval w₀ (map (Int.castRingHom ℂ) G) ≠ 0 → ∃ (V : Set ((Σ k, ι k) → ℂ)) (V' : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι k) → ℂ) → (Σ k, ι' k) → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen V' ∧ z ∈ V' ∧ AnalyticOnNhd ℂ f V ∧ ∀ z'' ∈ V' ∩ mcPts P', ∀ w ∈ V ∩ mcPts P, Rel z'' w → SameOrbit (f w) z'') → IsDegreeOff A R'.A h e (π '' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.Deg.isDegreeOff_of_correspondence | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.Deg.isDegreeOff_of_correspondence | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.Deg.isDegreeOff_of_correspondence <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareSystemPolarVanishingStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_system_polar_vanishing : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ) (Q : SqSys Re a₀ ε) (n : σ → ℤ), n a₀ = 0 → ∀ t, 0 < t → t ≤ Q.an.SW.t₀ → polar (d + 2) (Re.num II t) (fun _ a => (n a : ℝ)) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → polar (d + 2) (Re.num II t) (mix (2 * k) (fun a => (ε a : ℝ)) fun a => (n a : ℝ)) = -∑ i ∈ Finset.range k, polar (d + 2) (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potT (w r) t) (Q.an.gT t)) (Q.an.wcoef (fun a => (n a : ℝ)) k i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.first_half_at_scale | exact GlobalTheory.CompanionTheory.Ar.PB.first_half_at_scale | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.first_half_at_scale <;> assumption)
end

