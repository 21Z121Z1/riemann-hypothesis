import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0131
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0122
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0085
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0095
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0099
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0130
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0104
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0132
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0123
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0133

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartTenth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto

section Scale

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

def normScale (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) : Option K → ℂ
  | some k => if h : ∀ p, M.blk p ≠ some k then c ⟨k, h⟩ else 1
  | none => 1

theorem normScale_ne (M : FlagModel y Ψ N j) {c : NonPluckerBlocks M.blk → ℂ} (hc : ∀ k, c k ≠ 0) (o : Option K) :
    normScale M c o ≠ 0 := by
  cases o with
  | none => exact one_ne_zero
  | some k =>
    by_cases h : ∀ p, M.blk p ≠ some k
    · show dite _ _ _ ≠ 0
      rw [dif_pos h]
      exact hc ⟨k, h⟩
    · show dite _ _ _ ≠ 0
      rw [dif_neg h]
      exact one_ne_zero

theorem normScale_base (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) (k : NonPluckerBlocks M.blk) :
    normScale M c (some k.1) = c k := by
  simp [normScale, k.2]

theorem normScale_step (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) : normScale M c (some k) = 1 := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
  show dite _ _ _ = 1
  rw [dif_neg h]

end Scale

theorem norm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) ∧ SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) ∧ ∃ (h' : Ψ → Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), (∀ τ', IsBlockDiag j (h' τ') ∧ (h' τ').det ≠ 0) ∧ (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (h' p.1) I (stepCols N j p.2)) ∧ ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (h' τ * (1 + Matrix.single cb ca t')) I (stepCols N j a) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hctx z hzO
  obtain ⟨hb, hba, hk₀, hca, hcb, hAV, hF, hBC, hr, -, -⟩ := hctx
  obtain ⟨hz, hsrc, hV₀, -, -⟩ := hzO
  have z₀ : fstPt k₀ z ∈ mcPts (mCoordIdeal y) :=
    CPts.comp_mem_mcPts (Pts.isBlockMap_v₀ k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz
  have hbm : baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) := CPts.base_mem M z₀
  obtain ⟨hblm, hbl1, hblG, horb⟩ := hBC.2.2.2.2 _ hV₀
  rw [(Rb.A.chart kb).left_inv hsrc] at horb
  have horbit : SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) :=
    orbit_trans (orbit_symm horb) (hr _ hbm)
  have hG : M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) := by
    rwa [← CovMap.mCoordIdeal_eq_of_sameOrbit horbit]
  refine ⟨hbm, hG, horbit, ?_⟩
  obtain ⟨c, hc, hce⟩ := id horbit
  let z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun q => normScale M c q.1 * z q
  have hz' : z' ∈ mcPts (wP M τ a k₀ ca cb) :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal _) _ (normScale_ne M hc) hz
  have hbase : basePart M.blk (fstPt k₀ z') = bl (Rb.A.chart kb (r (baseOf M k₀ z))) := by
    rw [hce]
    funext q
    show normScale M c (some q.1.1) * z _ = c q.1 * z _
    rw [normScale_base]
  have hval : ∀ s : M.Ω, valAt M.x s (basePart M.blk (fstPt k₀ z')) = valAt M.x s (baseOf M k₀ z) := fun s => by
    rw [hbase]
    exact CovMap.LocImg.valAt_orbit horbit hbm s
  obtain ⟨h', t', H, H'⟩ := (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hk₀ hca hcb hAV F z' hF
    (by rw [hbase]; exact hblm) (by rw [hbase]; exact hblG) (by rw [hbase]; exact hbl1)).1 hz'
  refine ⟨h', t', H.2.1, fun p k hp => ?_, ?_⟩
  · obtain ⟨α, hα, e⟩ := H.2.2 p k hp
    refine ⟨α, hα, fun m => ?_⟩
    have e' := e m
    simp only [hval] at e'
    rw [← e']
    show z _ = normScale M c (some k) * z _
    rw [normScale_step M c hp, one_mul]
  · obtain ⟨α, hα, e⟩ := H'.2.2 (τ, a) k₀ hk₀
    refine ⟨α, hα, fun m => ?_⟩
    have e' := e m
    rw [Pts.basePart_snd M hk₀] at e'
    simp only [hval, Function.update_self] at e'
    rw [← e', Pts.snd_self, Pts.snd_self]
    show z _ = 1 * z _
    rw [one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedMeasure
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem holoOn_mul_prod_zpow {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X} {κ : Type}
    [Fintype κ] {f : X → ℂ} {c : κ → X → ℂ} (d : κ → ℤ) (hf : A.HoloOn U f) (hc : ∀ k, A.HoloOn U (c k))
    (h0 : ∀ k, ∀ y ∈ U, c k y ≠ 0) : A.HoloOn U fun y => f y * ∏ k, c k y ^ d k := by
  intro j z hz
  have h1 : AnalyticAt ℂ (fun v => ∏ k, ((c k ∘ (A.chart j).symm) v) ^ d k) z :=
    Finset.analyticAt_fun_prod _ fun k _ => (hc k j z hz).zpow (h0 k _ hz.2)
  exact (hf j z hz).mul h1

theorem holoOn_comp_chart {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) {g : (Fin e → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g ψ.target) {V : Set X} (hV : V ⊆ ψ.source) : A.HoloOn V fun w => g (ψ w) := by
  intro j z hz
  have hs : (A.chart j).symm z ∈ ψ.source := hV hz.2
  have h1 : AnalyticAt ℂ (g ∘ (ψ ∘ (A.chart j).symm)) z :=
    AnalyticAt.comp (g := g) (f := ψ ∘ (A.chart j).symm) (hg _ (ψ.map_source hs)) ((hψ j).1 z ⟨hz.1, hs⟩)
  exact h1

def mixPt (k₀ : K) (z₀ z₁ : (Σ k, ι k) → ℂ) : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p =>
  match p with
  | ⟨some k, m⟩ => z₀ ⟨k, m⟩
  | ⟨none, m⟩ => z₁ ⟨k₀, m⟩

theorem fstPt_mixPt (k₀ : K) (z₀ z₁ : (Σ k, ι k) → ℂ) : fstPt k₀ (mixPt k₀ z₀ z₁) = z₀ := by
  funext q
  obtain ⟨k, m⟩ := q
  rfl

theorem sndPt_mixPt {k₀ : K} {z₀ z₁ : (Σ k, ι k) → ℂ} (h : ∀ q : Σ k, ι k, q.1 ≠ k₀ → z₁ q = z₀ q) :
    sndPt k₀ (mixPt k₀ z₀ z₁) = z₁ := by
  funext q
  obtain ⟨k, m⟩ := q
  by_cases e : k = k₀
  · subst e
    change mixPt k z₀ z₁ (v₁ k ⟨k, m⟩) = _
    rw [v₁_self]
    rfl
  · change mixPt k₀ z₀ z₁ (v₁ k₀ ⟨k, m⟩) = _
    rw [v₁_ne (p := ⟨k, m⟩) e]
    exact (h ⟨k, m⟩ e).symm

theorem mixPt_blocks {k₀ : K} {z₀ z₁ : (Σ k, ι k) → ℂ} (h₀ : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0)
    (h₁ : ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) : ∀ o, ∃ i, mixPt k₀ z₀ z₁ ⟨o, i⟩ ≠ 0 := by
  intro o
  cases o with
  | none => exact h₁ k₀
  | some k => exact h₀ k

theorem log_norm_sub {k₀ : K} (A : HermLine fun o : Option K => ι (o.getD k₀)) {c : Option K → ℂ}
    (hc : ∀ o, c o ≠ 0) {z zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z = fun p => c p.1 * zz p)
    (hzz : ∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) {f t : ℂ} (hf : f ≠ 0) (ht : t ≠ 0) :
    Real.log ‖f * (∏ o, c o ^ A.a o) * t‖ - Real.log (A.h z) = Real.log ‖t * f‖ - Real.log (A.h zz) := by
  have hC : (∏ o, ‖c o‖ ^ A.a o) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun o _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc o))
  have hP : ‖∏ o, c o ^ A.a o‖ = ∏ o, ‖c o‖ ^ A.a o := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun o _ => norm_zpow _ _
  have hN : ‖f * (∏ o, c o ^ A.a o) * t‖ = (∏ o, ‖c o‖ ^ A.a o) * ‖t * f‖ := by
    rw [norm_mul, norm_mul, norm_mul, hP]
    ring
  have hA : A.h z = (∏ o, ‖c o‖ ^ A.a o) * A.h zz := by
    rw [hz]
    exact A.smul c zz hc
  have hp : A.h zz ≠ 0 := (A.pos zz hzz).ne'
  have hn : ‖t * f‖ ≠ 0 := norm_ne_zero_iff.2 (mul_ne_zero ht hf)
  rw [hN, hA, Real.log_mul hC hn, Real.log_mul hC hp]
  ring

theorem goodAt_of_orbit {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)
    {F : FrameData ι Ψ N M.Ω M.blk} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z'))) : M.GoodAt F (mCoordIdeal (basePart M.blk z)) := by
  obtain ⟨c, hc0, hzc⟩ := h
  have e₀ : basePart M.blk z = fun q : Σ k, baseIdx ι M.blk k =>
      (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk z' q := by
    rw [hzc]; rfl
  rw [e₀, GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.mCoordIdeal_torus (K := NonPluckerBlocks M.blk) (ι := baseIdx ι M.blk)
    (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc0 k.1) (basePart M.blk z')]
  exact hG

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ x, ∃ ψ kb σ i₀ V u, IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW x
  obtain ⟨ψ, kb, σ, i₀, F, H, hx, hC⟩ := hW.2.2 x
  obtain ⟨V, z₀, z₁, c, hVo, hxV, hVs, hVU, hz₀h, hch, hc0, hL⟩ :=
    GlobalTheory.T.flag_adjacent_twisted_resolution_alt K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW x ψ kb σ i₀ F H hx hC
  have hFr : M.IsFrame F := hC.2.1
  have hsrc := hC.2.2.2.2.2
  have hfacts : ∀ w ∈ V, basePart M.blk (z₀ w) ∈ mcPts (mCoordIdeal M.x) ∧ (∀ k, ∃ i, z₀ w ⟨k, i⟩ ≠ 0) ∧
      (∀ k, ∃ i, z₁ w ⟨k, i⟩ ≠ 0) ∧ basePart M.blk (z₁ w) = basePart M.blk (z₀ w) ∧
      M.GoodAt F (mCoordIdeal (basePart M.blk (z₀ w))) := by
    intro w hw
    obtain ⟨ho₀, ho₁, -, hoff, -, -⟩ := hL w hw
    obtain ⟨h1, -, h3, h4⟩ := PtBase.main K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hW w (z₀ w) (z₁ w) ho₀ ho₁
    refine ⟨h1, h3, h4, ?_, goodAt_of_orbit M ho₀ (hsrc w (hVs hw)).2.1⟩
    funext q
    exact hoff ⟨q.1.1, q.2⟩ fun e' => q.1.2 (τ, a) (hk.trans (congrArg some (Eq.symm e')))
  have hdata : ∀ w ∈ V, ψ w i₀ ≠ 0 → IsPtData M τ a k₀ ca cb RW w (z₀ w) (z₁ w) F (H τ (ψ w)) (ψ w i₀) := by
    intro w hw h0
    obtain ⟨ho₀, ho₁, hex, -⟩ := hL w hw
    have hH := (hsrc w (hVs hw)).1 τ
    exact ⟨hFr, (hfacts w hw).2.2.2.2, ho₀, ho₁, hH.1, hH.2, h0, fun i => (hex τ i).1, fun i => by
      simpa using (hex τ i).2⟩
  obtain ⟨V', hV'o, hxV', hV'V, hfh, hf0⟩ := GlobalTheory.T.holomorphic_frame_metric_near_point K ι Φ y Ψ N j M e RW.X RW.A V x
    (fun w => basePart M.blk (z₀ w)) (fun w => H τ (ψ w)) F τ a hVo hxV (fun q => hz₀h ⟨q.1.1, q.2⟩)
    (fun w hw => (hfacts w hw).1) (fun w hw => (hfacts w hw).2.2.2.2)
    (fun r s => holoOn_comp_chart RW.A hC.1 (hC.2.2.2.2.1 τ r s) hVs) (fun w hw => (hsrc w (hVs hw)).1 τ)
  obtain ⟨f, hfh, hf0, hfd⟩ : ∃ f : RW.X → ℂ, RW.A.HoloOn V' f ∧ (∀ w ∈ V', f w ≠ 0) ∧ ∀ w, f w =
      ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk (z₀ w)) *
        (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (H τ (ψ w)) (wIdx N j) (wIdx N j) else 1)
          else minorIJ (H τ (ψ w)) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i) :=
    ⟨_, hfh, hf0, fun _ => rfl⟩
  refine ⟨ψ, kb, σ, i₀, V', fun w => f w * ∏ o, c o w ^ aDeg M τ a k₀ o, ⟨F, H, hC⟩, hV'o, hxV',
    hV'V.trans hVs, hV'V.trans hVU, ?_, ?_, ?_, ?_⟩
  · exact holoOn_mul_prod_zpow RW.A _ hfh (fun o j' => (hch o j').mono
      (Set.inter_subset_inter_right _ (Set.preimage_mono hV'V))) fun o w hw => hc0 o w (hV'V hw)
  · intro w hw
    exact mul_ne_zero (hf0 w hw) (Finset.prod_ne_zero_iff.2 fun o _ => zpow_ne_zero _ (hc0 o w (hV'V hw)))
  · intro w hw
    have hwV := hV'V hw
    constructor
    · intro h0
      obtain ⟨ho₀, ho₁, hex, hoff, -, -⟩ := hL w hwV
      have hbase := (hfacts w hwV).2.2.2.1
      have hz : z₁ w = z₀ w := by
        funext q
        obtain ⟨k, m⟩ := q
        by_cases e' : k = k₀
        · subst e'
          have h1 := (hex τ a).1.2 k hk m
          have h2 := (hex τ a).2.2 k hk m
          rw [if_pos rfl, h0, Matrix.single_zero, add_zero, mul_one, hbase] at h2
          exact h2.trans h1.symm
        · exact hoff ⟨k, m⟩ e'
      rw [hz] at ho₁
      exact orbit_trans (orbit_symm ho₀) ho₁
    · intro hs
      by_contra h0
      exact GlobalTheory.T.flag_adjacent_twisted_resolution K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW w _ _ _ _ _
        (hdata w hwV h0) hs
  · intro w hw h0 z₀' z₁' F' h' t' hD
    have hwV := hV'V hw
    obtain ⟨ho₀, ho₁, -, hoff, hl0, hl1⟩ := hL w hwV
    obtain ⟨hmc, hn₀, hn₁, hbase, hG⟩ := hfacts w hwV
    obtain ⟨hF', hG', hp₀, hp₁, hB', hd', ht', he₀', he₁'⟩ := hD
    have hd := hdata w hwV h0
    have hind := GlobalTheory.T.flag_adjacent_two_frames_orbit K ι Φ y Ψ N j M τ a b k₀ ca cb hb hj hk hca hcb F F' (z₀ w) (z₁ w) z₀' z₁'
      (H τ (ψ w)) h' (ψ w i₀) t' hmc hn₀ hn₁ hbase hFr hF' hG hG' (orbit_trans ho₀ (orbit_symm hp₀))
      (orbit_trans ho₁ (orbit_symm hp₁)) hd.2.2.2.2.1 hd.2.2.2.2.2.1 hB' hd' h0 ht' hd.2.2.2.2.2.2.2.1
      hd.2.2.2.2.2.2.2.2 he₀' he₁'
    rw [← hind]
    have hlift : RW.lift x w = fun p => c p.1 w * mixPt k₀ (z₀ w) (z₁ w) p := by
      funext p
      obtain ⟨o, m⟩ := p
      cases o with
      | none => exact hl1 m
      | some k => exact hl0 ⟨k, m⟩
    have hzz := mixPt_blocks (k₀ := k₀) hn₀ hn₁
    have hnorm := log_norm_sub (potA M τ a k₀) (c := fun o => c o w) (fun o => hc0 o w hwV) hlift hzz
      (hf0 w hw) h0
    have hcombo := GlobalTheory.T.twisted_metric_log_formula K ι Φ y Ψ N j M τ a k₀ hk _ hzz
    rw [fstPt_mixPt, sndPt_mixPt hoff] at hcombo
    have e₁ : Real.log ‖(f w * ∏ o, c o w ^ aDeg M τ a k₀ o) * ψ w i₀‖ -
        Real.log ((potA M τ a k₀).h (RW.lift x w)) = _ := hnorm
    refine e₁.trans ?_
    rw [hcombo, normRhs, ← hfd w]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointTriangularChangeOrbit
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

private theorem sum_eq_sum_orderEmbOfFin_of_zero_off {N : ℕ} (S : Finset (Fin N)) (F : Fin N → ℂ)
    (hz : ∀ a, a ∉ S → F a = 0) :
    ∑ a, F a = ∑ z : Fin S.card, F (S.orderEmbOfFin rfl z) := by
  calc ∑ a, F a = ∑ a ∈ S, F a :=
        (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hz a ha)).symm
    _ = ∑ i : S, F i := (Finset.sum_coe_sort S F).symm
    _ = ∑ z : Fin S.card, F (S.orderEmbOfFin rfl z) :=
        (Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _
          (fun z => by simp [Finset.coe_orderIsoOfFin_apply])).symm

private theorem minorIJ_mul_of_block {N : ℕ} (h B : Matrix (Fin N) (Fin N) ℂ) (S I : Finset (Fin N))
    (hB : ∀ a c, c ∈ S → a ∉ S → B a c = 0) :
    minorIJ (h * B) I S = minorIJ h I S * minorIJ B S S := by
  unfold minorIJ
  by_cases e : I.card = S.card
  · rw [dif_pos e, dif_pos e, dif_pos rfl, ← Matrix.det_mul]
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    exact sum_eq_sum_orderEmbOfFin_of_zero_off S (fun a => h (I.orderEmbOfFin e x) a * B a (S.orderEmbOfFin rfl y))
      (fun a ha => by rw [hB a _ (Finset.orderEmbOfFin_mem S rfl y) ha, mul_zero])
  · rw [dif_neg e, dif_neg e, zero_mul]

private theorem apply_eq_zero_of_mem_stepCols_not_mem {N j : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (hd : IsBlockDiag j B) (ht : B.BlockTriangular id) :
    ∀ a c, c ∈ stepCols N j i → a ∉ stepCols N j i → B a c = 0 := by
  intro a c hc ha
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc ha
  have hi := i.isLt
  by_cases hblk : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)
  · apply ht
    show c < a
    rw [Fin.lt_def]
    split_ifs at hc ha <;> omega
  · exact hd a c hblk

private theorem minorIJ_ne_zero_of_blockTriangular {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (ht : B.BlockTriangular id) (hdet : B.det ≠ 0) : minorIJ B S S ≠ 0 := by
  unfold minorIJ
  rw [dif_pos rfl]
  have hdiag : ∀ a, B a a ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular ht] at hdet
    exact fun a => (Finset.prod_ne_zero_iff.mp hdet) a (Finset.mem_univ a)
  have htS : (B.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)).BlockTriangular id :=
    fun x y hxy => ht ((S.orderEmbOfFin rfl).strictMono hxy)
  rw [Matrix.det_of_isUpperTriangular htS]
  exact Finset.prod_ne_zero_iff.mpr (fun z _ => hdiag _)

theorem sameOrbit_flagPt_mul : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h B : Ψ → Matrix (Fin N) (Fin N) ℂ), (∀ τ', IsBlockDiag j (B τ') ∧ (B τ').BlockTriangular id ∧ (B τ').det ≠ 0) → SameOrbit (FC.flagPt M F b fun τ' => h τ' * B τ') (FC.flagPt M F b h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b h B hB
  refine Exists.intro (fun k => if hk : ∀ p, M.blk p ≠ some k then (1 : ℂ) else
    minorIJ (B (not_forall.1 hk).choose.1) (stepCols N j (not_forall.1 hk).choose.2)
      (stepCols N j (not_forall.1 hk).choose.2)) ⟨fun k => ?_, ?_⟩
  · dsimp only
    split_ifs with hk
    · exact one_ne_zero
    · generalize (not_forall.1 hk).choose = p
      exact minorIJ_ne_zero_of_blockTriangular (B p.1) (stepCols N j p.2) (hB p.1).2.1 (hB p.1).2.2
  · funext q
    simp only [flagPt]
    split_ifs with hk
    · rw [one_mul]
    · generalize (not_forall.1 hk).choose = p
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun I _ => ?_)
      rw [minorIJ_mul_of_block (h p.1) (B p.1) (stepCols N j p.2) I
        (apply_eq_zero_of_mem_stepCols_not_mem (B p.1) p.2 (hB p.1).1 (hB p.1).2.1)]
      ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameMinorValueFormulaStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_minor_value_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (p : Ψ × Fin N) (k : K) (A g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (α : ℂ) (J : Finset (Fin N)), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → M.blk p = some k → IsBlockDiag j A → (∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2)) → twMinor M F zb p.2 k g z J = α * minorIJ (g * A) J (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LUTwistRefactorizationStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.LU_twist_refactorization : ∀ (N j : ℕ) (a ca cb : Fin N) (L U : Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), j ≤ N → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → minorIJ (L * U * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 → ∃ (t : ℂ) (V : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c ∈ stepCols N j a, V c c ≠ 0) ∧ U * (1 + Matrix.single cb ca t') = (1 + Matrix.single cb ca t) * V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionOfPotentialOnModelStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_of_potential_on_model : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D) (Φ : LocPot M.Xc), IsPotential M.atlas Φ → (∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (D.A'.h z)) (s y') = (G y').re) → IsPosPot M.atlas Φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.potential_pos_of_section | exact GlobalTheory.CompanionTheory.Ar.Giv.potential_pos_of_section | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.potential_pos_of_section <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentMinorFormulaStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_unipotent_minor_formula : ∀ (N j : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (a' b' : Fin N), j ≤ N → IsBlockDiag j X → IsLowerUni X → b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) → minorIJ X (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b')) = 1 ∧ minorIJ X (insert a' ((stepCols N j (stepOf N j b')).erase b')) (stepCols N j (stepOf N j b')) = X a' b' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralModelFormula
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem push_chart_integrals : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (Y Z : Set M.Xc) (N : Set ((Σ k, ι k) → ℂ)) (c : Fin n → ℝ) (B : Fin n → HermLine ι) (Φ : Fin n → LocPot M.Xc) (g : ((Σ k, ι k) → ℂ) → ℝ) (G₀ : M.Xc → ℝ), IsArithVar P (n + 1) → IsGoodProj P Q → IsOpen Y → (∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Yᶜ ∪ Z)) = 0) → IsPtsNull P n N → (∀ i x, M.atlas.SmoothOn ((Φ i).U x ∩ Y) ((Φ i).φ x)) → (∀ i, ∀ x, ∀ y₀ ∈ (Φ i).U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ i).U x ∩ Y ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ i).φ x y' - (fun z => c i * Real.log ((B i).h z)) (s y') = (G y').re) → (∀ z ∈ mcPts P, z ∉ N → M.proj z ∈ Y → M.proj z ∉ Z → g z = G₀ (M.proj z)) → (∀ j, AEStronglyMeasurable (G₀ ∘ (M.atlas.chart j).symm) (volume.restrict (M.atlas.chart j).target)) → AEStronglyMeasurable (fun y => ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w) volume ∧ (∀ Pt : ChartPartition M.atlas, ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ fibre P Q y, |sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w|) = ∑ j, ∫⁻ u in (M.atlas.chart j).target, ENNReal.ofReal |Pt.χ j ((M.atlas.chart j).symm u) * G₀ ((M.atlas.chart j).symm u) * locDens M.atlas (Φ) j u|) ∧ (MIntegrable M.atlas Φ G₀ → Integrable (fun y => ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w) ∧ ptsIntegralAt P Q (fun i z => c i * Real.log ((B i).h z)) g = mInt M.atlas Φ G₀) := by
  intro K _ ι _ P n M Q Y Z N c B Φ g G₀ hP hQ hY hnull hN hΦs hΦt hg hG
  have hS : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelBad M Q (Yᶜ ∪ Z)) = 0 := by
    intro j
    rw [modelBad, Set.preimage_union, Set.inter_union_distrib_left]
    exact measure_union_null (hnull j) (GlobalTheory.T.volume_modelCrit_chart_eq_zero K ι P n M Q j hP hQ)
  have hq := modelQ_good_of_notMem M Q (Yᶜ ∪ Z)
  have hfin : ∀ y, (modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z)).Finite := fun y =>
    (ModelFibreFinite.proof K ι P n M Q hP hQ y).subset (Set.sdiff_subset_sdiff_right Set.subset_union_right)
  have hYof : ∀ x ∉ modelBad M Q (Yᶜ ∪ Z), x ∈ Y := fun x hx => by
    by_contra h
    exact hx (Or.inl (Or.inl h))
  have hsm : ∀ x ∉ modelBad M Q (Yᶜ ∪ Z), ∀ i k, x ∈ (M.atlas.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (M.atlas.chart k).symm) (M.atlas.chart k x) := by
    intro x hx i k hk
    have hxk : (M.atlas.chart k).symm (M.atlas.chart k x) = x := (M.atlas.chart k).left_inv hk
    have hmem : M.atlas.chart k x ∈ (M.atlas.chart k).target ∩ (M.atlas.chart k).symm ⁻¹' ((Φ i).U x ∩ Y) :=
      ⟨(M.atlas.chart k).map_source hk, by
        rw [Set.mem_preimage, hxk]; exact ⟨(Φ i).mem_U x, hYof x hx⟩⟩
    have hop := (M.atlas.chart k).isOpen_inter_preimage_symm (((Φ i).isOpen_U x).inter hY)
    exact ((hΦs i x k).contDiffAt (hop.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)
  have hYnull : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' Yᶜ) = 0 := fun j =>
    measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.subset_union_left)) (hnull j)
  have hm : ∀ j, AEStronglyMeasurable (fun u => G₀ ((M.atlas.chart j).symm u) * locDens M.atlas Φ j u)
      (volume.restrict (M.atlas.chart j).target) := by
    intro j
    let _ : MeasurableSpace M.Xc := borel M.Xc
    have : BorelSpace M.Xc := ⟨rfl⟩
    refine AEStronglyMeasurable.mul (hG j) ?_
    rw [MeasOff.restrict_target_eq M.atlas hYnull j]
    exact ((GlobalTheory.T.smooth_local_potential_lift K ι P n M Y c B Φ j hY hΦs hΦt).aestronglyMeasurable
      (MeasOff.isOpen_ov M.atlas hY j).measurableSet)
  have hae := GlobalTheory.T.chart_integral_potential_locally_finite K ι P n M Q Y Z N c B Φ g G₀ hP hQ hY hnull hN hΦs hΦt hg
  have e1 : ∀ᵐ y, ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w =
      ∑ᶠ x ∈ modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z), G₀ x * pushDens M.atlas Φ (modelQ M Q) x := by
    filter_upwards [hae] with y ⟨W, hW, hf, ht⟩
    rw [hf, finsum_mem_image hW]
    exact finsum_mem_congr rfl ht
  have e2 : ∀ᵐ y, ∑ᶠ w ∈ fibre P Q y, |sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w| =
      ∑ᶠ x ∈ modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z), |G₀ x * pushDens M.atlas Φ (modelQ M Q) x| := by
    filter_upwards [hae] with y ⟨W, hW, hf, ht⟩
    rw [hf, finsum_mem_image hW]
    exact finsum_mem_congr rfl fun x hx => by rw [ht x hx]
  refine ⟨(GlobalTheory.T.measurable_fibre_count_of_local_diffeo M.atlas Φ (modelQ M Q) _ G₀ hS hq hfin hsm hm).congr (e1.mono fun y hy => hy.symm),
    fun Pt => ?_, fun hI => ?_⟩
  · rw [lintegral_congr_ae (e2.mono fun y hy => congrArg ENNReal.ofReal hy)]
    exact GlobalTheory.T.finite_fibres_of_analytic_local_diffeo M.atlas Φ (modelQ M Q) _ G₀ hS hq hfin hsm hm Pt
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.integral_fibre_sum_change_of_variables M.atlas Φ (modelQ M Q) _ G₀ hS hq hfin hsm hI
    refine ⟨h1.congr (e1.mono fun y hy => hy.symm), ?_⟩
    rw [h2]
    exact integral_congr_ae (e1.mono fun y hy => hy)

end GlobalTheory.CompanionTheory.Ar.Giv
end

