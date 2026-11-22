import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelOfRiemann
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SymplecticPolydiscPeriodBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TendstoLocallyUniformlyOnOfNhds
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0005

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeLeRankMulSlope
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.DegSlope

private lemma degreeWith_bot {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    {r : ℕ} (f : Fin r → ↥(⊥ : Submodule (𝓞 K) E.carrier)) : E.degreeWith ⊥ f = 0 := by
  unfold HermitianBundle.degreeWith
  have h0 : ∀ i, ((f i : E.carrier)) = 0 := fun i => (Submodule.mem_bot _).1 (f i).2
  have hcard : Nat.card (↥(⊥ : Submodule (𝓞 K) E.carrier) ⧸ Submodule.span (𝓞 K) (Set.range f)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Quotient.inductionOn₂' a b (fun x y => congrArg _ (Subsingleton.elim x y))⟩, ⟨0⟩⟩
  have hdet : ∀ σ : K →+* ℂ, Real.log ‖E.gramDet σ (fun i => ((f i : E.carrier)))‖ = 0 := by
    intro σ
    unfold HermitianBundle.gramDet
    simp only [h0, TensorProduct.tmul_zero, inner_zero_left]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
      have hc : (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier)) = 0 := by
        have h : @inner ℂ _ (E.metric.form σ).toInner ((0 : Fibre σ E.carrier) + 0) 0 =
            @inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) 0 +
              @inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) 0 :=
          (E.metric.form σ).add_left 0 0 0
        rw [add_zero] at h
        linear_combination -h
      have hdet0 : (Matrix.of fun (_ : Fin r) (_ : Fin r) =>
          (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))).det = 0 := by
        rw [show (Matrix.of fun (_ : Fin r) (_ : Fin r) =>
            (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))) = 0 from
          Matrix.ext fun _ _ => hc]
        exact Matrix.det_zero
      have hgoal : Real.log ‖(Matrix.of fun (_ : Fin r) (_ : Fin r) =>
          (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))).det‖ = 0 := by
        rw [hdet0, norm_zero, Real.log_zero]
      exact hgoal
  rw [hcard]
  simp [hdet]

theorem normDegree_le_rank_mul_of_slopeMax_le : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (μ : ℝ), E.slopeMax ≤ (μ : EReal) → ∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E.rank F * μ := by
  intro K _ _ E μ hμ F
  by_cases hF : F = ⊥
  · subst hF
    have hr : E.rank ⊥ = 0 := by
      simp [HermitianBundle.rank]
    rw [hr, Nat.cast_zero, zero_mul]
    unfold HermitianBundle.normDegree HermitianBundle.degree
    rw [degreeWith_bot, zero_div]
  · have hpos : 0 < E.rank F := by
      unfold HermitianBundle.rank
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF
      exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, hx⟩, by simpa using hx0⟩
    have h1 : (E.slope F : EReal) ≤ E.slopeMax :=
      le_iSup₂ (f := fun G (_ : G ≠ ⊥) => (E.slope G : EReal)) F hF
    have h2 : E.slope F ≤ μ := EReal.coe_le_coe_iff.1 (h1.trans hμ)
    unfold HermitianBundle.slope at h2
    rw [div_le_iff₀ (by exact_mod_cast hpos)] at h2
    linarith

end GlobalTheory.CompanionTheory.Ar.DegSlope
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodMatrixLocalTrivialization
section
open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_periodPolydisc_frame : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ), ∃ (Q : PeriodPolydisc n a g) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (ball 0 1)) ∧ (A 0).det ≠ 0 ∧ ∀ w ∈ logCover L.a_le, A (expCover a w) * L.H (expCover a w) * (A (expCover a w))ᴴ = (((Q.τ w).map Complex.im)⁻¹).map Complex.ofReal := by
  intro n a g Λ _ L
  obtain ⟨bas, Q, A, T0, hsym, hAd, hdet, -, -, hAP, hQP⟩ := exists_markedPeriods_frame n a g Λ L
  refine ⟨Q, A, hAd, hdet, fun w hw => ?_⟩
  let Am : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i => L.P w (bas (.inl i))
  let Bm : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i => L.P w (bas (.inr i))
  have hAm : Am = A (expCover a w) := by
    ext i k
    exact hAP w hw i k
  obtain ⟨h1, -, -, h4⟩ := siegel_of_riemann g Am Bm (L.H (expCover a w)) (L.herm w hw)
    (L.pos w hw) (fun i j => ⟨(L.im w hw (bas (.inl i)) (bas (.inl j))).trans (by simp [(hsym i j).1]),
      (L.im w hw (bas (.inr i)) (bas (.inr j))).trans (by simp [(hsym i j).2.1]),
      (L.im w hw (bas (.inl i)) (bas (.inr j))).trans (by
        rw [(hsym i j).2.2]; split_ifs <;> simp)⟩)
  have hB : Bm = Q.τ w * Am := by
    ext j k
    have h := congrFun (hQP w hw j) k
    rw [Finset.sum_apply] at h
    simpa [Am, Bm, Matrix.mul_apply] using h
  have hτ : Bm * Am⁻¹ = Q.τ w := by
    rw [hB, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h1), Matrix.mul_one]
  rw [← hAm, h4, hτ]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPullbackCompatible
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem pb_indep_cover : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k', ι' k') → Ω) (S' : AnSys D σ) (Re' : Realis S' (mCoordIdeal y)) (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')), IsBlockMap κ v → imageZ v (mCoordIdeal y) = P → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a, IsPullHerm κ v (Re.line a t) (Re'.line a t)) → Re'.deg = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * Re.deg → Re'.PB II = Re.PB II := by
  intro II hII K _ ι _ D σ _ S P Re K' _ ι' _ Ω _ _ y S' Re' κ v hbl hP hpull hdeg
  have hr0 : IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 := by
    intro h
    have hd := Re'.deg_pos
    rw [hdeg, h, zero_mul] at hd
    exact lt_irrefl 0 hd
  have hr : ((IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hr0
  have harith : IsArithVar (imageZ v (mCoordIdeal y)) (D + 1) := by
    rw [hP]
    exact Re.arith
  have key : ∀ w : Fin (D + 1) → σ, Re'.limNum II w = Re.limNum II w := by
    intro w
    have ht0 : 0 < S.t₀ := (S.reg (w 0)).1
    have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ S.t₀ := by
      filter_upwards [Ioo_mem_nhdsGT ht0] with t ht using ht.2.le
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    have heq : (fun t => Re'.num II t w) =ᶠ[𝓝[>] (0 : ℝ)] (fun t => Re.num II t w) := by
      filter_upwards [hpull, hle, hpos] with t hpt hle' hpos'
      have hPF := hII.2.2.1 K ι K' ι' κ v Ω y (D + 1) (fun j => Re.line (w j) t)
        (fun j => Re'.line (w j) t) hbl Re'.arith harith
        (fun j => Re.line_smooth (w j) t hpos' hle') (fun j => hpt (w j))
      rw [hP] at hPF
      show (II K' ι' (mCoordIdeal y) (D + 1) fun j => Re'.line (w j) t) / (Re'.deg : ℝ)
        = (II K ι P (D + 1) fun j => Re.line (w j) t) / (Re.deg : ℝ)
      rw [hPF, hdeg]
      push_cast
      exact mul_div_mul_left _ _ hr
    unfold Realis.limNum Filter.limUnder
    rw [Filter.map_congr heq]
  unfold Realis.PB
  rw [show Re'.limNum II = Re.limNum II from funext key]

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFamilyC2PullbackOfSection
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

theorem isOpen_compl_bdry {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : s x x ≠ 0 := hx
  obtain ⟨j, hj⟩ := A.cover x
  have hleft : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ L.U x
      rw [hleft]; exact L.mem_U x⟩
  have hg : ContinuousAt (s x ∘ (A.chart j).symm) (A.chart j x) :=
    (hs.1 x j _ hmem).continuousAt
  have hne : (s x ∘ (A.chart j).symm) (A.chart j x) ≠ 0 := by
    simpa [Function.comp_apply, hleft] using hx0
  have h1 : ∀ᶠ y in 𝓝 x, (s x ∘ (A.chart j).symm) (A.chart j y) ≠ 0 :=
    ((A.chart j).continuousAt hj).eventually (hg.eventually_ne hne)
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ (A.chart j).source := (A.chart j).open_source.mem_nhds hj
  have h3 : ∀ᶠ y in 𝓝 x, y ∈ L.U x := (L.isOpen_U x).mem_nhds (L.mem_U x)
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  have hsy : s x y ≠ 0 := by
    simpa [Function.comp_apply, (A.chart j).left_inv hy2] using hy1
  intro hb
  have hb0 : s y y = 0 := hb
  have heq := hs.2 x y y ⟨hy3, L.mem_U y⟩
  rw [hb0, norm_zero, zero_mul] at heq
  exact (mul_ne_zero (norm_ne_zero_iff.2 hsy) (Real.exp_ne_zero _)) heq

theorem regular_family_C2_pullback_of_open {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (A : FinHolAtlas e X) (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h)
    (s : X → X → ℂ) (ph : X → ℝ) (phT : ℝ → X → ℝ) (hO : IsOpen (bdry s)ᶜ)
    (hph : A.SmoothOn (bdry s)ᶜ ph)
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), A.Smooth (phT t))
    (hC : IsRegFamilyC2 A s ph phT) :
    IsRegFamilyC2 A' (fun x y => s (h x) (h y)) (ph ∘ h) (fun t => phT t ∘ h) := by
  have key := GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.proof A' A h hh (bdry s)ᶜ hO phT ph
    (ph ∘ h) hph (fun _ _ => rfl) hT (fun k K hK hKs => hC k K hKs hK)
  intro j K hKs hK
  exact key j K hK hKs

theorem regular_family_C2_pullback_of_section {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (A : FinHolAtlas e X) (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h)
    (L : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (phT : ℝ → X → ℝ) (hs : IsSection A L s)
    (hph : A.SmoothOn (bdry s)ᶜ ph)
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), A.Smooth (phT t))
    (hC : IsRegFamilyC2 A s ph phT) :
    IsRegFamilyC2 A' (fun x y => s (h x) (h y)) (ph ∘ h) (fun t => phT t ∘ h) :=
  regular_family_C2_pullback_of_open A A' h hh s ph phT (isOpen_compl_bdry hs) hph hT hC

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TailLogBoundLocalIntegrable
section
open MeasureTheory Filter Topology ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.Metric.LocTail

theorem tailLog_on_compact_of_chart {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : FinHolAtlas e X) (Yo : Set X) (r : X → ℝ) (Φ : Fin e → LocPot X) (CE : ℝ)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hr : ∀ x ∈ Yo, 1 ≤ r x)
    (hdens : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo → 0 ≤ locDens A Φ j y)
    (hT : GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A Yo r Φ CE)
    (j : Fin A.n) (S : Set (Fin e → ℂ)) (hSt : S ⊆ (A.chart j).target) (hSc : IsCompact S)
    (R₀ : ℝ) (hR₀ : Real.exp 1 ≤ R₀) :
    IntegrableOn (fun y => (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator
      (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y) S ∧
    ∫ y in S, (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator
      (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y ≤
      CE * Real.log R₀ ^ (e + 1) / R₀ := by
  classical
  obtain ⟨hI, hB⟩ := hT R₀ hR₀
  set h : X → ℝ := (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator
    (fun x => Real.log (r x)) with hdef
  have hIS := hI j S hSt hSc
  refine ⟨hIS, ?_⟩
  have hh0 : ∀ x, 0 ≤ h x := by
    intro x
    refine Set.indicator_nonneg (fun x hx => ?_) x
    exact Real.log_nonneg (hr x hx.1)
  have hhYo : ∀ x, x ∉ Yo → h x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem (fun hm => hx hm.1) _
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  set ch := A.chart j with hch
  set Z : Set X := ch.symm '' S with hZ
  set g : X → ℝ := Z.indicator h with hgdef
  have hg0 : ∀ x, x ∉ ch.source → g x = 0 := by
    intro x hx
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨y, hy, rfl⟩
    exact hx (ch.map_target (hSt hy))
  set F : (Fin e → ℂ) → ℝ := fun y => h (ch.symm y) * locDens A Φ j y with hF
  have hgF : ∀ z ∈ ch.target, g (ch.symm z) * locDens A Φ j z = S.indicator F z := by
    intro z hz
    by_cases hzS : z ∈ S
    · rw [Set.indicator_of_mem hzS, hgdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hzS)]
    · have hnZ : ch.symm z ∉ Z := by
        rintro ⟨y, hy, hyz⟩
        exact hzS ((ch.symm.injOn (by simpa using hSt hy) (by simpa using hz) hyz) ▸ hy)
      rw [Set.indicator_of_notMem hzS, hgdef, Set.indicator_of_notMem hnZ, zero_mul]
  have hFint : IntegrableOn (S.indicator F) ch.target :=
    ((integrable_indicator_iff hSm).2 hIS).integrableOn
  have hint : IntegrableOn (fun z => g (ch.symm z) * locDens A Φ j z) ch.target :=
    hFint.congr_fun (fun z hz => (hgF z hz).symm) ch.open_target.measurableSet
  have hne : Nonempty (ChartPartition A) := existsPartition A
  obtain ⟨hgt, hgI⟩ := integralWith_localize_support A hne.some Φ hΦ j g hg0 hint
  have hSint : ∫ z in ch.target, g (ch.symm z) * locDens A Φ j z = ∫ y in S, F y := by
    rw [setIntegral_congr_fun ch.open_target.measurableSet hgF,
      setIntegral_indicator hSm, Set.inter_eq_right.2 hSt]
  have hle : integralWith A hne.some Φ g ≤ integralWith A hne.some Φ h := by
    unfold integralWith
    refine Finset.sum_le_sum fun k _ => ?_
    refine setIntegral_mono_on (hgt k) (integrableOn_weight A hne.some Φ h hI k)
      (A.chart k).open_target.measurableSet fun y hy => ?_
    by_cases hx : (A.chart k).symm y ∈ Yo
    · have hd := hdens k y hy hx
      have hχ := hne.some.nonneg k ((A.chart k).symm y)
      have hgh : g ((A.chart k).symm y) ≤ h ((A.chart k).symm y) :=
        Set.indicator_le_self' (fun x _ => hh0 x) _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgh hχ) hd
    · have h1 : h ((A.chart k).symm y) = 0 := hhYo _ hx
      have h2 : g ((A.chart k).symm y) = 0 := by
        rw [hgdef]
        by_cases hz : (A.chart k).symm y ∈ Z
        · rw [Set.indicator_of_mem hz, h1]
        · rw [Set.indicator_of_notMem hz]
      rw [h1, h2]
  calc ∫ y in S, F y = integralWith A hne.some Φ g := by rw [hgI, hSint]
    _ ≤ integralWith A hne.some Φ h := hle
    _ = mInt A Φ h := (mInt_eq_integralWith A Φ hne h).symm
    _ ≤ _ := hB

end GlobalTheory.CompanionTheory.Metric.LocTail
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformisedPotentialIntegralFormula
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem proportional_on_uniformised : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (U : Set X) (th : Ψ × Fin N → LocPot X) (ph : Ψ × Fin N → X → ℝ), j ≤ N → e = antisymDegree Ψ N → IsOpen U → IsNull A Uᶜ → (∀ p, IsPotential A (th p)) → (∀ p, A.SmoothOn U (ph p)) → IsUniformised A U j (fun p => th p + LocPot.ofFun (ph p)) → (∀ w : Fin e → Ψ × Fin N, MIntegrable A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) → ∃ v : ℝ, 0 < v ∧ toWt (formPoly e fun w => mInt A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) = C v * antisymDelta Ψ N :=
  @PositivityTheory.Xgp.t_per_int

end GlobalTheory.CompanionTheory.Ar.PB
end

