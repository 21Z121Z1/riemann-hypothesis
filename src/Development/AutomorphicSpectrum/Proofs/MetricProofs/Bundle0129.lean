import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RegWeightLimits
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0123
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0124
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0115
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0120
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0117
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0125
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightDominatesEventually
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section Metric

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W} {w : ((Σ k, J k) → ℂ) → ℝ}

theorem MUc_h_of_mem (Hd : HodgeData D) {M : XModel D} (S : BoundedRegularisationSetting M D.Xo Hd.aMu w) (B p q : ℕ) (t : ℝ)
    {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    (MUc Hd S B p q t).h z = (S.ref.h z * Real.exp (S.bregWeight t (M.proj z))) ^ q *
      (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p := by
  set P := mCoordIdeal D.y with hPdef
  set a : K → ℤ := (q : ℤ) • muTwDeg Hd B + (p : ℤ) • D.a' with ha
  set F : ((Σ k, J k) → ℂ) → ℝ := fun z => (S.ref.h z * Real.exp (S.bregWeight t (M.proj z))) ^ q *
    (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p with hFdef
  have hVS : VertFactorSmooth.Statement := VertFactorSmooth.proof VertFactorPos.proof
  have hSB : ∀ p' ∈ D.SB B, p' ∈ D.S := fun p' hp' => (Finset.mem_filter.1 hp').1
  have hMH : IsMultiHomogIdeal P := D.arith.2.1.2.1
  have hpos : ∀ z ∈ mcPts P, 0 < F z := by
    intro z hz
    have h2 : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' z := Finset.prod_pos fun p' hp' =>
      VertFactorPos.proof II Ψ K J Ω W D p' (hSB p' hp') z hz
    exact mul_pos (mul_pos (pow_pos (mul_pos (S.ref.pos z hz.1) (Real.exp_pos _)) q) (pow_pos h2 q))
      (pow_pos (D.A'.pos z hz.1) p)
  have hhom : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts P := mcPts_smul hMH c hc hz
    have hproj : M.proj (torusSmul c z) = M.proj z := ((M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ Hd.aMu k) * S.ref.h z := by
      have := S.ref.smul c z hc
      rw [S.ref_deg] at this
      exact this
    have hA : D.A'.h (torusSmul c z) = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h z := by
      have := D.A'.smul c z hc
      rw [D.A'_deg] at this
      exact this
    have hV : ∀ p' ∈ D.SB B, D.vertFactor p' (torusSmul c z) =
        (∏ k, ‖c k‖ ^ D.vdeg p' k) * D.vertFactor p' z :=
      fun p' hp' => (hVS II Ψ K J Ω W D p' (hSB p' hp')).1 z hz c hc
    have hk : ∀ k, ‖c k‖ ^ a k = (‖c k‖ ^ (muTwDeg Hd B) k) ^ q * (‖c k‖ ^ D.a' k) ^ p := by
      intro k
      have hx : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      have hak : a k = (q : ℤ) * (muTwDeg Hd B) k + (p : ℤ) * D.a' k := by
        simp only [ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hak, zpow_add₀ hx, _root_.zpow_mul', zpow_natCast, _root_.zpow_mul', zpow_natCast]
    have hprod : (∏ k, ‖c k‖ ^ a k) = ((∏ k, ‖c k‖ ^ Hd.aMu k) *
        ∏ p' ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p' k) ^ q * (∏ k, ‖c k‖ ^ D.a' k) ^ p := by
      rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
        muTwDeg, MuRegSmooth.prod_norm_zpow_add_sum hc]
    simp only [hFdef]
    rw [hproj, href, hA, Finset.prod_congr rfl hV, Finset.prod_mul_distrib, hprod]
    ring
  show (smoothRepConj P (hermOfFun J a F)).h z = F z
  rw [smoothRepConj_h _ hz]
  exact NbarSmooth.hermOfFun_h_of_mem hMH hhom hz (hpos z hz)

theorem log_MUc_h_of_mem (Hd : HodgeData D) {M : XModel D} (S : BoundedRegularisationSetting M D.Xo Hd.aMu w) (B p q : ℕ) (t : ℝ)
    {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    Real.log ((MUc Hd S B p q t).h z) = q * (Real.log (S.ref.h z) + S.bregWeight t (M.proj z) +
      ∑ r ∈ D.SB B, Real.log (D.vertFactor r z)) + p * Real.log (D.A'.h z) := by
  have hSB : ∀ p' ∈ D.SB B, 0 < D.vertFactor p' z := fun p' hp' =>
    VertFactorPos.proof II Ψ K J Ω W D p' (Finset.mem_filter.1 hp').1 z hz
  have h1 : S.ref.h z ≠ 0 := (S.ref.pos z hz.1).ne'
  have h2 : D.A'.h z ≠ 0 := (D.A'.pos z hz.1).ne'
  have h3 : ∏ p' ∈ D.SB B, D.vertFactor p' z ≠ 0 := (Finset.prod_pos hSB).ne'
  have h4 : S.ref.h z * Real.exp (S.bregWeight t (M.proj z)) ≠ 0 := mul_ne_zero h1 (Real.exp_pos _).ne'
  rw [MUc_h_of_mem Hd S B p q t hz, Real.log_mul (mul_ne_zero (pow_ne_zero _ h4) (pow_ne_zero _ h3)) (pow_ne_zero _ h2),
    Real.log_mul (pow_ne_zero _ h4) (pow_ne_zero _ h3), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul h1 (Real.exp_pos _).ne', Real.log_exp, Real.log_prod fun r hr => (hSB r hr).ne']
  ring

end Metric

theorem bregWeight_ge_and_MUc_smooth : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), S'.IsTied → ∀ᶠ t' in 𝓝[>] (0 : ℝ), (∀ x, S'.B.ph x ≤ S'.bregWeight t' x) ∧ M.atlas.Smooth (S'.bregWeight t') ∧ ∀ B p q : ℕ, IsSmoothHerm (MUc Hd S' B p q t') ∧ (MUc Hd S' B p q t').a = (q : ℤ) • muTwDeg Hd B + (p : ℤ) • D.a' ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((MUc Hd S' B p q t').h z) = q * (Real.log (S'.ref.h z) + S'.bregWeight t' (M.proj z) + ∑ r ∈ D.SB B, Real.log (D.vertFactor r z)) + p * Real.log (D.A'.h z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M w S' hS
  obtain ⟨δ, hδ, hmarg⟩ := S'.B.toPotentialCharts.exists_margin
  have hδ' : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < δ :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun t ht => ht.2
  have hMU := GroundTheory.Heights₂.Heights.NineStatements.MUcSmooth.proof HermExtend.proof
    (ProjSmoothAlong.proof HoloInjDerivInj.proof GlobalTheory.T.local_orbit_chart_statement_holds)
  filter_upwards [self_mem_nhdsWithin, hδ', S'.eventually_chartLevi hS] with t ht htδ hlev
  have ht' : 0 < t := ht
  have hε : 0 < S'.e1 t := lt_of_lt_of_le ht' (S'.e1_ge t ht')
  refine ⟨fun x => boundedPsh_le_regularised S'.B S'.ρ S'.cutoff hmarg ht' htδ.le hε x, hlev.1,
    fun B p q => ⟨hMU II Ψ K J Ω W D Hd M w S' B p q t hlev.1, smoothRepConj_a _ _,
      fun z hz => log_MUc_h_of_mem Hd S' B p q t hz⟩⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimChartComponents
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)

theorem chartComponents_dim : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsCxVar Q e → ∀ J ∈ chartComponents (conePts Q) σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  intro K _ _ ι _ Q e m σ i hQ J hJ
  have hmin : J ∈ (setSegChartIdeal (conePts Q) σ i).minimalPrimes :=
    mem_chartComponents.mp hJ
  have hhom : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ.2.1.2.1
  exact segChart_dim hQ.2.1.1 hhom hQ.2.2 σ i hmin

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothLocalPotentialLift
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push.DCont

section General

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def ReHolAt (A : FinHolAtlas e X) (f : X → ℝ) (y₀ : X) : Prop :=
  ∃ W : Set X, IsOpen W ∧ y₀ ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧ ∀ z ∈ W, f z = (G z).re

theorem holoOn_continuousOn {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} (h : A.HoloOn W f) :
    ContinuousOn f W := by
  intro z hz
  obtain ⟨j, hj⟩ := A.cover z
  have h1 : (A.chart j).symm (A.chart j z) = z := (A.chart j).left_inv hj
  have hu : A.chart j z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by rw [Set.mem_preimage, h1]; exact hz⟩
  have hc : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j z) := (h j _ hu).continuousAt
  have hc2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) z :=
    ContinuousAt.comp hc ((A.chart j).continuousAt hj)
  have hev : ((f ∘ (A.chart j).symm) ∘ (A.chart j)) =ᶠ[𝓝 z] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  exact (hc2.congr hev).continuousWithinAt

theorem ReHolAt.congr {A : FinHolAtlas e X} {f g : X → ℝ} {y₀ : X} (hg : ReHolAt A g y₀)
    (h : f =ᶠ[𝓝 y₀] g) : ReHolAt A f y₀ := by
  obtain ⟨W, hW, hy, G, hG, hWG⟩ := hg
  obtain ⟨T, hT, hTo, hyT⟩ := mem_nhds_iff.1 h
  exact ⟨W ∩ T, hW.inter hTo, ⟨hy, hyT⟩, G, fun j u hu => hG j u ⟨hu.1, hu.2.1⟩,
    fun z hz => (hT hz.2).trans (hWG z hz.1)⟩

theorem ReHolAt.add {A : FinHolAtlas e X} {f g : X → ℝ} {y₀ : X} (hf : ReHolAt A f y₀)
    (hg : ReHolAt A g y₀) : ReHolAt A (fun y => f y + g y) y₀ := by
  obtain ⟨W, hW, hy, G, hG, hWG⟩ := hf
  obtain ⟨W', hW', hy', G', hG', hWG'⟩ := hg
  refine ⟨W ∩ W', hW.inter hW', ⟨hy, hy'⟩, fun z => G z + G' z, fun j u hu => ?_, fun z hz => ?_⟩
  · exact (hG j u ⟨hu.1, hu.2.1⟩).add (hG' j u ⟨hu.1, hu.2.2⟩)
  · show f z + g z = (G z + G' z).re
    rw [hWG z hz.1, hWG' z hz.2, Complex.add_re]

theorem ReHolAt.const_mul {A : FinHolAtlas e X} {f : X → ℝ} {y₀ : X} (c : ℝ) (hf : ReHolAt A f y₀) :
    ReHolAt A (fun y => c * f y) y₀ := by
  obtain ⟨W, hW, hy, G, hG, hWG⟩ := hf
  refine ⟨W, hW, hy, fun z => (c : ℂ) * G z, fun j u hu => ?_, fun z hz => ?_⟩
  · exact analyticAt_const.mul (hG j u hu)
  · show c * f z = ((c : ℂ) * G z).re
    rw [hWG z hz, Complex.re_ofReal_mul]

theorem ReHolAt.sub {A : FinHolAtlas e X} {f g : X → ℝ} {y₀ : X} (hf : ReHolAt A f y₀)
    (hg : ReHolAt A g y₀) : ReHolAt A (fun y => f y - g y) y₀ := by
  refine (hf.add (hg.const_mul (-1))).congr (Eventually.of_forall fun y => ?_)
  show f y - g y = f y + -1 * g y
  ring

theorem ReHolAt.sum {A : FinHolAtlas e X} {J : Type} (s : Finset J) {f : J → X → ℝ} {y₀ : X}
    (hf : ∀ i ∈ s, ReHolAt A (f i) y₀) : ReHolAt A (fun y => ∑ i ∈ s, f i y) y₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, fun j u _ => analyticAt_const, ?_⟩
    intro z _
    simp
  | insert a s ha ih =>
    refine ((hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))).congr (Eventually.of_forall fun y => ?_)
    show ∑ i ∈ insert a s, f i y = f a y + ∑ i ∈ s, f i y
    rw [Finset.sum_insert ha]

theorem reHolAt_log_norm {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} {y₀ : X} (hW : IsOpen W)
    (hf : A.HoloOn W f) (hy : y₀ ∈ W) (h0 : f y₀ ≠ 0) :
    ReHolAt A (fun y => Real.log ‖f y‖) y₀ := by
  have hS : IsOpen {w : ℂ | w / f y₀ ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (continuous_id.div_const _)
  have hW' := (holoOn_continuousOn hf).isOpen_inter_preimage hW hS
  refine ⟨_, hW', ⟨hy, ?_⟩, fun z => Complex.log (f z / f y₀) + (Real.log ‖f y₀‖ : ℂ),
    fun j u hu => ?_, fun z hz => ?_⟩
  · show f y₀ / f y₀ ∈ Complex.slitPlane
    rw [div_self h0]
    exact Complex.one_mem_slitPlane
  · have h1 : AnalyticAt ℂ (f ∘ (A.chart j).symm) u := hf j u ⟨hu.1, hu.2.1⟩
    exact ((h1.div_const (c := f y₀)).clog hu.2.2).add analyticAt_const
  · have hz0 : f z ≠ 0 := fun h => by
      have := Complex.slitPlane_ne_zero hz.2
      simp [h] at this
    rw [Complex.add_re, Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0),
      Complex.ofReal_re]
    ring

end General

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ}

def IsSecOn (M : CxModel P d) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ) : Prop :=
  (∀ y ∈ U, s y ∈ mcPts P ∧ M.proj (s y) = y) ∧ ∀ p, M.atlas.HoloOn U fun y => s y p

theorem reHolAt_log_sections {M : CxModel P d} {U U' : Set M.Xc} {s s' : M.Xc → (Σ k, ι k) → ℂ}
    {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} (hU : IsOpen U) (hU' : IsOpen U') (hs : IsSecOn M U s)
    (hs' : IsSecOn M U' s')
    (hF : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    (hpos : ∀ z ∈ mcPts P, 0 < F z) {y₀ : M.Xc} (hy : y₀ ∈ U) (hy' : y₀ ∈ U') :
    ReHolAt M.atlas (fun y => Real.log (F (s' y)) - Real.log (F (s y))) y₀ := by
  classical
  have hz := (hs.1 y₀ hy).1
  have hz' := (hs'.1 y₀ hy').1
  choose i hi using hz.1
  obtain ⟨c₀, hc₀, hcz⟩ := (M.fibre _ hz _ hz').1 (by rw [(hs.1 y₀ hy).2, (hs'.1 y₀ hy').2])
  have hi' : ∀ k, s' y₀ ⟨k, i k⟩ ≠ 0 := by
    intro k
    rw [hcz]
    exact mul_ne_zero (hc₀ k) (hi k)
  have hR : ∀ k ∈ (Finset.univ : Finset K), ReHolAt M.atlas
      (fun y => (a k : ℝ) * (Real.log ‖s' y ⟨k, i k⟩‖ - Real.log ‖s y ⟨k, i k⟩‖)) y₀ := fun k _ =>
    ((reHolAt_log_norm hU' (hs'.2 _) hy' (hi' k)).sub
      (reHolAt_log_norm hU (hs.2 _) hy (hi k))).const_mul _
  refine (ReHolAt.sum Finset.univ hR).congr ?_
  have hev : ∀ᶠ y in 𝓝 y₀, ∀ k, s y ⟨k, i k⟩ ≠ 0 := eventually_all.2 fun k =>
    ((holoOn_continuousOn (hs.2 ⟨k, i k⟩)).continuousAt (hU.mem_nhds hy)).eventually_ne (hi k)
  filter_upwards [hU.mem_nhds hy, hU'.mem_nhds hy', hev] with y h1 h2 h3
  have hm := (hs.1 y h1).1
  have hm' := (hs'.1 y h2).1
  obtain ⟨c, hc, hcy⟩ := (M.fibre _ hm _ hm').1 (by rw [(hs.1 y h1).2, (hs'.1 y h2).2])
  have hnc : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hc k)
  rw [hcy, hF _ hm c hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hnc k))
    (hpos _ hm).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hnc k)), add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h4 : torusSmul c (s y) ⟨k, i k⟩ = c k * s y ⟨k, i k⟩ := rfl
  rw [h4, Real.log_zpow, norm_mul, Real.log_mul (hnc k) (norm_ne_zero_iff.2 (h3 k)), add_sub_cancel_right]

theorem hessC_base_eq {M : CxModel P d} {Y : Set M.Xc} (c : ℝ) (B : HermLine ι) (Q : LocPot M.Xc)
    (j : Fin M.atlas.n)
    (hsm : ∀ x, M.atlas.SmoothOn (Q.U x ∩ Y) (Q.φ x)) (hY : IsOpen Y)
    (hsec : ∀ x, ∀ y₀ ∈ Q.U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ Q.U x ∩ Y ∧
      ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧
        (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧
          ∀ y' ∈ U, Q.φ x y' - (fun z => c * Real.log (B.h z)) (s y') = (G y').re)
    {y : Fin d → ℂ} (hy : y ∈ (M.atlas.chart j).target) (hyY : (M.atlas.chart j).symm y ∈ Y)
    {x₀ : M.Xc} (hx₀ : (M.atlas.chart j).symm y ∈ Q.U x₀) :
    hessC (fun y' => Q.φ ((M.atlas.chart j).symm y) ((M.atlas.chart j).symm y')) y =
      hessC (fun y' => Q.φ x₀ ((M.atlas.chart j).symm y')) y := by
  set x := (M.atlas.chart j).symm y with hx
  obtain ⟨U₁, hU₁, hx₁, -, s₁, hs₁, hh₁, G₁, hG₁, he₁⟩ := hsec x x ⟨Q.mem_U x, hyY⟩
  obtain ⟨U₂, hU₂, hx₂, -, s₂, hs₂, hh₂, G₂, hG₂, he₂⟩ := hsec x₀ x ⟨hx₀, hyY⟩
  obtain ⟨W, hW, hxW, G₃, hG₃, he₃⟩ :=
    (reHolAt_log_sections (M := M) (F := B.h) (a := B.a) hU₂ hU₁ ⟨hs₂, hh₂⟩ ⟨hs₁, hh₁⟩
      (fun z _ c hc => B.smul c z hc) (fun z hz => B.pos z hz.1) hx₂ hx₁).const_mul c
  have hOo : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (U₁ ∩ U₂ ∩ W)) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm ((hU₁.inter hU₂).inter hW)
  have hyO : y ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (U₁ ∩ U₂ ∩ W) :=
    ⟨hy, ⟨⟨hx₁, hx₂⟩, hxW⟩⟩
  have h1 : (fun y' => Q.φ x ((M.atlas.chart j).symm y')) =ᶠ[nhds y]
      (fun w => (fun y' => Q.φ x₀ ((M.atlas.chart j).symm y')) w +
        ((fun w' => G₁ ((M.atlas.chart j).symm w') - G₂ ((M.atlas.chart j).symm w') +
          G₃ ((M.atlas.chart j).symm w')) w).re) := by
    filter_upwards [hOo.mem_nhds hyO] with w hw
    have e1 := he₁ _ hw.2.1.1
    have e2 := he₂ _ hw.2.1.2
    have e3 := he₃ _ hw.2.2
    simp only [Complex.add_re, Complex.sub_re] at *
    linarith
  rw [hessCGerm _ _ _ h1]
  have hopen : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Q.U x₀ ∩ Y)) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm ((Q.isOpen_U x₀).inter hY)
  have hsmooth : ContDiffAt ℝ 2 (fun y' => Q.φ x₀ ((M.atlas.chart j).symm y')) y :=
    ((hsm x₀ j).contDiffAt (hopen.mem_nhds ⟨hy, ⟨hx₀, hyY⟩⟩)).of_le (WithTop.coe_le_coe.2 le_top)
  exact ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _ hsmooth
    (((hG₁ j y ⟨hy, hx₁⟩).sub (hG₂ j y ⟨hy, hx₂⟩)).add (hG₃ j y ⟨hy, hxW⟩))

end Model

theorem locDens_continuousOn_of_sections : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Y : Set M.Xc) (c : Fin n → ℝ) (B : Fin n → HermLine ι) (Φ : Fin n → LocPot M.Xc) (j : Fin M.atlas.n), IsOpen Y → (∀ i x, M.atlas.SmoothOn ((Φ i).U x ∩ Y) ((Φ i).φ x)) → (∀ i, ∀ x, ∀ y₀ ∈ (Φ i).U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ i).U x ∩ Y ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ i).φ x y' - (fun z => c i * Real.log ((B i).h z)) (s y') = (G y').re) → ContinuousOn (locDens M.atlas Φ j) ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' Y) := by
  intro K _ ι _ P n M Y c B Φ j hY hΦs hsec y₀ hy₀
  apply ContinuousAt.continuousWithinAt
  set x₀ := (M.atlas.chart j).symm y₀ with hx₀
  have hVo : IsOpen ((M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' (Y ∩ ⋂ i, (Φ i).U x₀)) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm
      (hY.inter (isOpen_iInter_of_finite fun i => (Φ i).isOpen_U _))
  have hy0V : y₀ ∈ (M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' (Y ∩ ⋂ i, (Φ i).U x₀) :=
    ⟨hy₀.1, hy₀.2, Set.mem_iInter.2 fun i => (Φ i).mem_U _⟩
  have heq : maDens (fun i y' => (Φ i).φ x₀ ((M.atlas.chart j).symm y')) =ᶠ[nhds y₀]
      locDens M.atlas Φ j := by
    filter_upwards [hVo.mem_nhds hy0V] with y hy
    unfold locDens
    refine maDens_congr_hessC _ _ _ fun i => ?_
    exact (hessC_base_eq (c i) (B i) (Φ i) j (hΦs i) hY (hsec i) hy.1 hy.2.1
      (Set.mem_iInter.1 hy.2.2 i)).symm
  refine ContinuousAt.congr ?_ heq
  refine (maDens_continuousOn _ _ hVo fun i => ?_).continuousAt (hVo.mem_nhds hy0V)
  exact ((hΦs i x₀ j).of_le (WithTop.coe_le_coe.2 le_top)).mono
    fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2.2 i, hy.2.1⟩

end GlobalTheory.CompanionTheory.Ar.Giv.Push.DCont
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionBoundaryNormalCrossing
section
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_sncData_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, ∃ d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)), (∃ O : Set (SncRes.Pts (pC (mCoordIdeal y))), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src (pC (mCoordIdeal y)) p ∧ ∀ k, SncRes.comp (pC (mCoordIdeal y)) (pC J) k ∩ O = {x' ∈ O | ∃ l, d.σ l = some k ∧ eval (SncRes.coord (pC (mCoordIdeal y)) p x') (d.r l) = 0}) ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), ReciprocityTheory.AnForm.R.IsMultiHomog f a → f ∉ pC (mCoordIdeal y) → (∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal y)), eval z f = 0 → z ∈ ReciprocityTheory.AnForm.R.conePts (pC J)) → ∃ u : ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x), IsUnit u ∧ algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (bind₁ (SncRes.lift p) f) = u * ∏ l ∈ d.J, algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (d.r l) ^ (d.σ l).elim 0 (fun k => SncRes.ordAlong (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k) (pC (mCoordIdeal y)) f) := by
  intro K _ ι _ Ω _ _ y e J hA hJ hJn hS p x hx
  have hPm : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hA.2.1.2.1
  have hDm : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC J) := isMultiHomogIdeal_pC hJ
  have hz : ∀ k, SncRes.rep x ⟨k, p k⟩ ≠ 0 := hx
  have hzc := SncRes.rep_mem x
  obtain ⟨r, Jf, hIt, hreg, hdim, hspan, hpr⟩ := GlobalTheory.T.snc_chart_parameters_at_cone_point K ι Ω y e J hA hS p (SncRes.rep x) hzc hz
  have hID : SncRes.ideal (pC (mCoordIdeal y)) p ≤ SncRes.ideal (pC (mCoordIdeal y) ⊔ pC J) p :=
    Ideal.map_mono (sup_le_sup_right le_sup_left _)
  obtain ⟨h, hh, hmem, hle⟩ := GlobalTheory.T.exists_radical_locally_eq_span_prod _ e _ _ _ r Jf hID hIt hreg hdim hspan hpr
  obtain ⟨σ, hinj, hnone, hσ, hcov⟩ := GlobalTheory.T.snc_chart_regular_at_cone_point K ι _ (pC J) e p (SncRes.rep x) r Jf hPm hDm hzc hz hIt hreg hdim hspan hpr
  let d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)) :=
    { r := r, J := Jf, h := h, σ := σ, σ_injOn := hinj, σ_eq_none := hnone, span_eq := hspan, eval_h := hh,
      mem_bd := hmem, le_span := hle }
  refine ⟨d, GlobalTheory.T.snc_chart_regular_with_boundary_choice K ι _ (pC J) e p x r Jf σ hPm hDm hx hIt hreg hdim hspan hnone (fun l k hl => (hσ l k hl).1) hcov, ?_⟩
  intro f a hf hfP hfz
  obtain ⟨u, mm, hm0, hfac⟩ := GlobalTheory.T.snc_chart_multihomog_order_at_point K ι _ (pC J) e p (SncRes.rep x) r Jf f a hPm hDm hzc hz hIt hreg hdim hspan hpr hf hfz
  refine ⟨u.val, u.isUnit, ?_⟩
  refine hfac.trans (congrArg (fun w => u.val * w) (Finset.prod_congr rfl fun l hl => ?_))
  have hlJ : l ∈ Jf := hl
  obtain ⟨k, hk⟩ : ∃ k, σ l = some k := by
    cases hσl : σ l with
    | none => exact absurd hlJ ((hnone l).1 hσl)
    | some k => exact ⟨k, rfl⟩
  have hdσ : d.σ l = some k := hk
  rw [hdσ]
  obtain ⟨hQc, hX⟩ := hσ l k hk
  have hQmin := SncRes.compIdeal_mem (P := pC (mCoordIdeal y)) (pC J) k
  have hQm := GlobalTheory.T.minimal_primes_of_multihomog_sup K ι _ _ hPm hDm _ hQmin
  have hQp : (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k).IsPrime := hQmin.1.1
  have hord := GlobalTheory.T.unit_times_parameter_monomial _ e _ _ r Jf _ u mm hIt hreg hdim hspan hfac l hlJ
  have key : ∀ n : ℕ, (∃ s ∉ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k,
      s * f ∈ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k ^ n ⊔ pC (mCoordIdeal y)) ↔ n ≤ mm l := by
    intro n
    rw [← hord n, ← hQc]
    constructor
    · rintro ⟨s, hs, hsf⟩
      exact GlobalTheory.T.symbolic_power_from_affine_chart K ι _ _ p f s a n hPm hQm hQp hX hf hs hsf
    · rintro ⟨s', hs, hsf⟩
      exact GlobalTheory.T.symbolic_power_in_affine_chart K ι _ _ p f a n s' hPm hQm hQp hX hf hs hsf
  have hset : {n : ℕ | ∃ s ∉ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k,
      s * f ∈ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k ^ n ⊔ pC (mCoordIdeal y)} = Set.Iic (mm l) := by
    ext n
    exact key n
  show _ ^ mm l = _ ^ (SncRes.ordAlong _ _ f)
  rw [SncRes.ordAlong, hset, csSup_Iic]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ZeroSetChartIdealEqChartSetStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeroSet_chartIdeal_eq_chartSet : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal Q →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.zeroSet_chartIdeal_conePts | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.zeroSet_chartIdeal_conePts | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.zeroSet_chartIdeal_conePts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ZeroWeightRegularFamilyStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zero_weight_regular_family : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (C₅ C t₁ : ℝ), IsPotential A Θ → IsPosPot A Θ → (∀ y, logNormSec L s y ≤ 0) → 0 ≤ C₅ → 0 ≤ C → 0 < t₁ → t₁ ≤ Real.exp (-Real.exp 1) → IsSingWeight A L s (LocPot.ofFun 0) 0 C₅ ∧ IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) C t₁ ∧ IsRegFamilyC2 A s 0 (fun _ => 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.zeroMember_isRegFamily | exact GlobalTheory.CompanionTheory.Ar.Giv.zeroMember_isRegFamily | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.zeroMember_isRegFamily <;> assumption)
end

