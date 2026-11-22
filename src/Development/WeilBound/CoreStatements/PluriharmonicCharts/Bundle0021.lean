import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0132
import Development.WeilBound.CoreStatements.PluriharmonicCharts.PullDegSome
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0018
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0019
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorSingle
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0122
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.ContinuousOnLogNormSec
section
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB

namespace PositivityTheory.Xgp.sq_limit

open GlobalTheory.CompanionTheory.Ar.Giv GlobalTheory.CompanionTheory.Ar.Giv.SignedConv ReciprocityTheory.AnForm.M.FinHolAtlas

theorem continuousOn_logNormSec {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (v : X → X → ℂ) (hL : IsPotential A L) (hv : IsSection A L v) :
    ContinuousOn (logNormSec L v) (bdry v)ᶜ := by
  intro y hy
  refine ContinuousAt.continuousWithinAt ?_
  have hy' : v y y ≠ 0 := hy
  have h1 : ContinuousAt (v y) y := LeviFormBoundaryTopology.continuousAt_of_holoOn A (hv.1 y) (L.mem_U y)
  have h2 : ContinuousAt (L.φ y) y :=
    LeviFormBoundaryTopology.continuousAt_of_smoothOn A (L.isOpen_U y) (hL.1 y) (L.mem_U y)
  have h3 : ContinuousAt (fun z => Real.log (‖v y z‖ * Real.exp (-L.φ y z))) y := by
    refine ContinuousAt.log (h1.norm.mul (Real.continuous_exp.continuousAt.comp h2.neg)) ?_
    exact mul_ne_zero (norm_ne_zero_iff.2 hy') (Real.exp_pos _).ne'
  refine h3.congr ?_
  filter_upwards [(L.isOpen_U y).mem_nhds (L.mem_U y)] with z hz
  unfold logNormSec
  rw [hv.2 y z z ⟨hz, L.mem_U z⟩]

theorem smoothOn_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U V : Set X} {f : X → ℝ} (hUV : U ⊆ V) (h : A.SmoothOn V f) : A.SmoothOn U f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hUV))

theorem isPshOn_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U V : Set X} {P : LocPot X} (hUV : U ⊆ V) (h : IsPshOn A V P) : IsPshOn A U P :=
  fun x j y hy w => h x j y ⟨hy.1, hy.2.1, hUV hy.2.2⟩ w

theorem unifIntSigned (hU : UnifIntStatement) {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ)
    (hL : IsPotential A L) (hS : IsSection A L s) (hSNC : IsSNC A L s m W)
    (hs : ∀ y, logNormSec L s y ≤ 0) (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X)
    (hL' : IsPotential A L') (hv : IsSection A L' v) (hvS : IsSNC A L' v ![1] ![Dg])
    (hsv : IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg))
    (hvn : ∀ y, logNormSec L' v y ≤ 0)
    (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ)
    (hSW : ∀ i, IsSingWeight A L s (th i) (ph i) C₅)
    (hRF : ∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀)
    (hC2 : ∀ i, IsRegFamilyC2 A s (ph i) (phT i)) :
    MIntegrable A (fun i => th i + LocPot.ofFun (ph i)) (logNormSec L' v) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable A (fun i => th i + LocPot.ofFun (phT i t)) (logNormSec L' v)) ∧
      Tendsto (fun t => mInt A (fun i => th i + LocPot.ofFun (phT i t)) (logNormSec L' v)) (𝓝[>] 0)
        (𝓝 (mInt A (fun i => th i + LocPot.ofFun (ph i)) (logNormSec L' v))) := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  set g := logNormSec L' v with hg
  have hΘpsh : IsPsh A Θ := isPsh_of_isPosPot A Θ hΘp
  set U : Set X := (bdry s)ᶜ ∩ (bdry v)ᶜ with hUdef
  have hUo : IsOpen U := (LeviFormBoundaryTopology.isClosed_bdry hS).isOpen_compl.inter
    (LeviFormBoundaryTopology.isClosed_bdry hv).isOpen_compl
  have hUs : U ⊆ (bdry s)ᶜ := Set.inter_subset_left
  have hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0 := by
    intro j
    rw [hUdef, Set.compl_inter, Set.preimage_union, Set.inter_union_distrib_left]
    exact measure_union_null (chart_null A L s m W hS hSNC j) (chart_null A L' v _ _ hv hvS j)
  have hgc : ContinuousOn g U := (continuousOn_logNormSec A L' v hL' hv).mono Set.inter_subset_right
  have hmem : ∀ T : Finset (Fin e),
      (∀ i, IsSingWeight A L s (if i ∈ T then th i else LocPot.ofFun 0)
        (if i ∈ T then ph i else 0) |C₅|) ∧
      (∀ i, IsRegFamily A Θ L s (if i ∈ T then th i else LocPot.ofFun 0)
        (if i ∈ T then ph i else 0) (fun t => if i ∈ T then phT i t else 0) |C|
        (min t₀ (Real.exp (-Real.exp 1)))) ∧
      (∀ i, IsRegFamilyC2 A s (if i ∈ T then ph i else 0) (fun t => if i ∈ T then phT i t else 0)) := by
    intro T
    have hz : ∀ i : Fin e, IsSingWeight A L s (LocPot.ofFun 0) 0 |C₅| ∧
        IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) |C| (min t₀ (Real.exp (-Real.exp 1))) ∧
        IsRegFamilyC2 A s 0 (fun _ => 0) := fun i =>
      zero_member A Θ L s |C₅| |C| _ hΘ hΘp hs (abs_nonneg _) (abs_nonneg _)
        (lt_min (hRF i).1 (Real.exp_pos _)) (min_le_right _ _)
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;> by_cases hi : i ∈ T <;>
      simp only [hi, ↓reduceIte]
    · exact isSingWeight_abs A L s _ _ _ hs (hSW i)
    · exact (hz i).1
    · exact isRegFamily_mono A Θ L s (th i) (ph i) (phT i) C t₀ |C| _ hΘ hΘpsh (hSW i).1 hs (hRF i)
        le_rfl (lt_min (hRF i).1 (Real.exp_pos _)) (min_le_left _ _) (min_le_right _ _)
    · exact (hz i).2.1
    · exact hC2 i
    · exact (hz i).2.2
  have hconv : ∀ T : Finset (Fin e),
      Integrable g (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then ph i else 0) + Θ)) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), Integrable g (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ))) ∧
      Tendsto (fun t => ∫ y, g y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) (𝓝[>] 0)
        (𝓝 (∫ y, g y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then ph i else 0) + Θ))) := by
    intro T
    obtain ⟨h1, h2, h3⟩ := hU A Θ L s m W hΘ hΘp hL hS hSNC hs L' v Dg hL' hv hvS hsv hvn
      (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0)
      (fun i t => if i ∈ T then phT i t else 0) |C₅| |C| _ (hmem T).1 (hmem T).2.1 (hmem T).2.2
    refine ⟨integrable_neg_iff.1 h1, h2.mono fun t ht => integrable_neg_iff.1 ht, ?_⟩
    simp only [integral_neg] at h3
    simpa only [neg_neg] using h3.neg
  have hlimT := fun T : Finset (Fin e) => GlobalTheory.T.mInt_eq_integral_maMeasure A U
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0) Θ hUo hnull
    (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => smoothOn_mono A hUs ((hmem T).1 i).2.1)
    (fun i => isPshOn_add_psh A _ _ _ Θ hUo ((hmem T).1 i).1 hΘ (smoothOn_mono A hUs ((hmem T).1 i).2.1)
      (isPshOn_mono A hUs ((hmem T).1 i).2.2.1) hΘpsh) g hgc (hconv T).1
  have hexpL := expand_mInt A U th ph Θ g hUo hnull (fun i => (hSW i).1) hΘ
    (fun i => smoothOn_mono A hUs (hSW i).2.1) (fun T => (hlimT T).1)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ i, A.Smooth (phT i t)) ∧
      ∀ T : Finset (Fin e), (∀ i, A.Smooth (if i ∈ T then phT i t else 0) ∧
        IsPsh A ((if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) ∧
        Integrable g (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) := by
    refine (eventually_all.2 fun i => ?_).and (eventually_all.2 fun T => ?_)
    · exact (eventually_isPsh A Θ L s (th i) (ph i) (phT i) C t₀ hΘ hΘp (hSW i).1 (hRF i)).mono
        fun t ht => ht.1
    · refine (eventually_all.2 fun i => ?_).and (hconv T).2.1
      exact eventually_isPsh A Θ L s _ _ _ _ _ hΘ hΘp ((hmem T).1 i).1 ((hmem T).2.1 i)
  have hreg : ∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable A (fun i => th i + LocPot.ofFun (phT i t)) g ∧
      ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        ∫ y, g y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ) =
        mInt A (fun i => th i + LocPot.ofFun (phT i t)) g := by
    filter_upwards [hev] with t ht
    have hmt := fun T : Finset (Fin e) => GlobalTheory.T.mInt_eq_integral_maMeasure A U
      (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then phT i t else 0) Θ hUo hnull
      (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => smoothOn_of_smooth A _ _ ((ht.2 T).1 i).1)
      (fun i => isPshOn_of_isPsh A _ _ ((ht.2 T).1 i).2) g hgc (ht.2 T).2
    have hx := expand_mInt A U th (fun i => phT i t) Θ g hUo hnull (fun i => (hSW i).1) hΘ
      (fun i => smoothOn_of_smooth A _ _ (ht.1 i)) (fun T => (hmt T).1)
    refine ⟨hx.1, ?_⟩
    rw [hx.2]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [(hmt T).2]
  refine ⟨hexpL.1, hreg.mono fun t ht => ht.1, ?_⟩
  rw [hexpL.2]
  refine Tendsto.congr' (hreg.mono fun t ht => ht.2) ?_
  refine tendsto_finsetSum _ fun T _ => ?_
  rw [(hlimT T).2]
  exact ((hconv T).2.2).const_mul _

theorem singular_part (hI : Inputs) {d : ℕ} {σ : Type} [Fintype σ] {SY : AnSys (d + 1) σ} {a₀ : σ}
    {ε : σ → ℤ} (Q : AnSq SY a₀ ε) (w : Fin (d + 2) → Option σ) :
    MIntegrable Q.SW.A (fun r => Q.SW.potH (w r)) (logNormSec Q.L' Q.v) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v)) ∧
      Tendsto (fun t => mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v)) (𝓝[>] 0)
        (𝓝 (mInt Q.SW.A (fun r => Q.SW.potH (w r)) (logNormSec Q.L' Q.v))) :=
  unifIntSigned hI.unifInt Q.SW.A Q.SW.Θ Q.SW.L Q.SW.s Q.SW.m Q.SW.W Q.SW.potΘ Q.SW.posΘ Q.SW.potL
    Q.SW.sec Q.SW.snc Q.SW.norm_le Q.L' Q.v Q.Dg Q.potL' Q.secv Q.sncv Q.sncsv Q.normv
    (fun r => Q.SW.th (w r)) (fun r => Q.SW.ph (w r)) (fun r => Q.SW.phT (w r)) Q.SW.C₅ Q.SW.C Q.SW.t₀
    (fun r => Q.SW.sing (w r)) (fun r => Q.SW.reg (w r)) (fun r => Q.SW.c2 (w r))

end PositivityTheory.Xgp.sq_limit
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.WCoZero
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section
namespace PositivityTheory.Xgp.c_algsq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem wCo_zero (M : FlagModel y Ψ N j) {p : Ψ × Fin N} {k₀ : K} (hk : M.blk p = some k₀) (ca cb : Fin N)
    (m : ι k₀) : M.wCo p k₀ ca cb 0 ⟨none, m⟩ = M.wCo p k₀ ca cb 0 ⟨some k₀, m⟩ := by
  simp only [FlagModel.wCo, Matrix.single_zero, add_zero, mul_one]
  rw [M.y_step p k₀ hk m, map_sum]
  exact Finset.sum_congr rfl fun I _ => by rw [map_mul, CPts.minorIJ_map]

def mkAlg (M : FlagModel y Ψ N j) {d : ℕ} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N} (hb : (b : ℕ) = a + 1)
    (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀) (hca : (ca : ℕ) = lastCol N j a)
    (hcb : (cb : ℕ) = ca + 1) (hy : IsArithVar (mCoordIdeal y) (d + 2)) (xi2 : K → ℤ) (hxi : xi2 k₀ = -2)
    (g h : MRing fun o : Option K => ι (o.getD k₀)) (dg dh : Option K → ℕ) (hg : IsMultiHomog g dg)
    (hh : IsMultiHomog h dh) (hgn : g ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))
    (hhn : h ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))
    (hdeg : ∀ o : Option K, (dg o : ℤ) - dh o = o.elim 1 fun k => -xi2 k - (if M.blk (τ, a) = some k then 1 else 0))
    (hdiv : divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) g =
      divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) h +
        Finsupp.single (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) 1) :
    AlgSq (mCoordIdeal y) d k₀ xi2 where
  arithY := hy
  xi_two_base_eq_neg_two := hxi
  KW := Option K
  ιW := fun o => ι (o.getD k₀)
  PW := mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)
  arithW := (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).1
  κ := ![some, κ₁ k₀]
  v := ![v₀ k₀, v₁ k₀]
  block := Fin.forall_fin_two.2 ⟨Pts.isBlockMap_v₀ k₀, isBlockMap_v₁ k₀⟩
  image := Fin.forall_fin_two.2 ⟨(t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.2.1,
    (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.2.2 (v₁ k₀) (fun _ h => v₁_ne h)
      (v₁_self k₀)⟩
  same p hp := (v₁_ne hp).symm
  new := by
    rintro ⟨k, hk'⟩
    have : some k = κ₁ k₀ k₀ := hk'
    rw [κ₁_self] at this
    cases this
  all k' := by
    cases k' with
    | none => exact Or.inr (κ₁_self k₀).symm
    | some k => exact Or.inl ⟨k, rfl⟩
  fibre_line := t_c_w_line K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hk hca hcb
  Δ := mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)
  arithΔ := (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.1
  PW_le := (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.1
  diag i i' := by
    show mConeMap _ (X (v₀ k₀ ⟨k₀, i⟩) * X (v₁ k₀ ⟨k₀, i'⟩) - X (v₀ k₀ ⟨k₀, i'⟩) * X (v₁ k₀ ⟨k₀, i⟩)) = 0
    rw [v₁_self, v₁_self]
    simp only [mConeMap, map_sub, map_mul, aeval_X, v₀, wCo_zero M hk]
    ring
  g := g
  h := h
  dg := dg
  dh := dh
  g_deg := hg
  h_deg := hh
  g_nmem := hgn
  h_nmem := hhn
  deg_eq o := by
    show _ = -(pullDeg some xi2 o + pullDeg (κ₁ k₀) xi2 o)
    rw [hdeg, pullDeg_some, pullDeg_κ₁]
    cases o with
    | none => simp [hxi]
    | some k =>
      simp only [Option.elim, hk, Option.some.injEq]
      by_cases e : k = k₀
      · subst e; simp [hxi]
      · rw [if_neg e, if_neg (Ne.symm e)]; ring
  div_eq := hdiv

end PositivityTheory.Xgp.c_algsq
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCCovSelf
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace PositivityTheory.Xgp.c_cov_self

open GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

def idCover (M : FlagModel y Ψ N j) : FlagCover M M where
  κ := id
  v := id
  block := ⟨Function.injective_id, Function.injective_id, fun _ => rfl, fun q _ => ⟨q, rfl⟩⟩
  φ := RingHom.id _
  x_eq _ := rfl
  deg_pos := by
    show 0 < IntermediateField.relfinrank (blockFnField M.x) (blockFnField M.x)
    rw [IntermediateField.relfinrank_self]; exact one_pos
  agree z hz F' F h' h g' g τ a b := ⟨all_mem hz h h' g g' τ a b, all_mem hz h' h g' g τ a b⟩

theorem trans_eq (M : FlagModel y Ψ N j) (F' F : FrameData ι Ψ N M.Ω M.blk) (zb) (τ : Ψ) :
    (idCover M).trans F' F zb τ = valMat M.x zb ((F.T τ)⁻¹ * F'.T τ) := rfl

theorem log_refNorm_congr {a : K → ℤ} {z z' : (Σ k, ι k) → ℂ}
    (h : ∀ k, a k ≠ 0 → ∀ m, z ⟨k, m⟩ = z' ⟨k, m⟩) : refNorm a z = refNorm a z' := by
  unfold refNorm
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : a k = 0
  · simp [hk]
  · simp only [h k hk]

theorem metric_self [Fintype Ψ] [DecidableEq Ψ] (M : FlagModel y Ψ N j) (z : (Σ k, ι k) → ℂ)
    (hz : z ∈ mcPts (mCoordIdeal y)) (z₀ : (Σ k, ι k) → ℂ) (F' F : FrameData ι Ψ N M.Ω M.blk)
    (h' : M.IsFrame F') (h : M.IsFrame F) (g' : M.GoodAt F' (mCoordIdeal (basePart M.blk z)))
    (g : M.GoodAt F (mCoordIdeal (basePart M.blk z))) (ho : SameOrbit (basePart M.blk z₀) (basePart M.blk z))
    (p : Ψ × Fin N) (H : Matrix (Fin N) (Fin N) ℂ) (hH : IsBlockDiag j H) (e' : M.ExactAt F' p z H)
    (e : M.ExactAt F p z₀ ((idCover M).trans F' F (basePart M.blk z) p.1 * H)) :
    Real.log ((fsHerm ι (M.dy p)).h z) + M.upsLog F' p z =
      Real.log ((fsHerm ι (M.dy p)).h z₀) + M.upsLog F p z₀ +
        Real.log ‖detFac j p.2 ((idCover M).trans F' F (basePart M.blk z) p.1)‖ := by
  have hzb := CPts.base_mem M hz
  have hT := FibreCount.trans_unit (idCover M) hzb h' h g' g p.1
  have hd := CPts.detFac_ne_zero M.j_le p.2 hT.1 hT.2
  have hρ := rhoC_ne g g' p
  have hval : ∀ s, valAt M.x s (basePart M.blk z₀) = valAt M.x s (basePart M.blk z) := valAt_orbit ho hzb
  rw [trans_eq] at hd e ⊢
  set dd := detFac j p.2 (valMat M.x (basePart M.blk z) ((F.T p.1)⁻¹ * F'.T p.1)) with hdd
  set ρ := rhoC M F F' p (basePart M.blk z) with hρd
  obtain ⟨c, hc, hco⟩ := ho
  have hρc : ρ = ∏ k, c k ^ M.b p k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    have h1 := e.1 k
    rw [hco] at h1
    rw [e'.1 k, one_div, ← eq_inv_of_mul_eq_one_left h1]
  let t : K → ℂ := fun k => if hk : ∀ p', M.blk p' ≠ some k then c ⟨k, hk⟩ else
    if M.blk p = some k then ρ / dd else 1
  have ht : ∀ k, t k ≠ 0 := fun k => by
    simp only [t]
    split_ifs
    · exact hc _
    · exact div_ne_zero hρ hd
    · exact one_ne_zero
  have e1 : refNorm (M.dy p) z₀ = refNorm (M.dy p) fun q => t q.1 * z q := by
    refine log_refNorm_congr fun k hk m => ?_
    by_cases hb : ∀ p', M.blk p' ≠ some k
    · simp only [t, dif_pos hb]
      exact congrFun hco ⟨⟨k, hb⟩, m⟩
    · have hp : M.blk p = some k := by
        by_contra hp
        exact hk (by simp only [FlagModel.dy, dif_neg hb, if_neg hp])
      simp only [t, dif_neg hb, if_pos hp]
      have r := relC hzb h h' g g' hp H hH m
      rw [e.2 k hp m, e'.2 k hp m]
      simp only [hval]
      rw [← hdd, ← hρd] at r
      field_simp
      linear_combination r
  have e2 : (∏ k, ‖t k‖ ^ M.dy p k) = ‖ρ‖⁻¹ * (M.blk p).elim 1 fun _ => ‖ρ‖ / ‖dd‖ := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun k => ∀ p', M.blk p' ≠ some k)]
    congr 1
    · rw [hρc, norm_prod, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr (by congr; exact Subsingleton.elim _ _) fun k _ => ?_
      simp only [t, FlagModel.dy, dif_pos k.2, _root_.zpow_neg, norm_zpow]
    · cases hp : M.blk p with
      | none =>
        refine Finset.prod_eq_one fun k _ => ?_
        have : M.blk p ≠ some k.1 := by rw [hp]; simp
        simp only [FlagModel.dy, dif_neg k.2, if_neg this, _root_.zpow_zero]
      | some k₀ =>
        have hk₀ : ¬ ∀ p', M.blk p' ≠ some k₀ := fun e => e p hp
        rw [Finset.prod_eq_single ⟨k₀, hk₀⟩]
        · simp only [t, FlagModel.dy, dif_neg hk₀, if_pos hp, _root_.zpow_one, norm_div, Option.elim_some]
        · intro k _ hk
          have : M.blk p ≠ some k.1 := fun e => hk (Subtype.ext (Option.some.inj (e.symm.trans hp)))
          simp only [FlagModel.dy, dif_neg k.2, if_neg this, _root_.zpow_zero]
        · simp
  have e3 := (fsHerm ι (M.dy p)).smul t z ht
  have hpos := (fsHerm ι (M.dy p)).pos z hz.1
  have hρn : 0 < ‖ρ‖ := norm_pos_iff.2 hρ
  have hdn : 0 < ‖dd‖ := norm_pos_iff.2 hd
  have e4 : (fsHerm ι (M.dy p)).h z₀ =
      (‖ρ‖⁻¹ * (M.blk p).elim 1 fun _ => ‖ρ‖ / ‖dd‖) * (fsHerm ι (M.dy p)).h z := by
    rw [← e2]; exact e1.trans e3
  rw [e4]
  unfold FlagModel.upsLog
  cases hp : M.blk p with
  | none =>
    have r := congrArg (fun w => Real.log ‖w‖) (rel0C hzb h h' g g' hp)
    have u1 := norm_pos_iff.2 (ups_ne hzb g hp)
    have u2 := norm_pos_iff.2 (ups_ne hzb g' hp)
    simp only [← hdd, ← hρd, norm_mul] at r
    rw [Real.log_mul hdn.ne' u1.ne', Real.log_mul hρn.ne' u2.ne'] at r
    simp only [Option.elim_none, mul_one, hval]
    rw [Real.log_mul (inv_pos.2 hρn).ne' hpos.ne', Real.log_inv]
    linarith
  | some k =>
    simp only [Option.elim_some]
    rw [← mul_div_assoc, inv_mul_cancel₀ hρn.ne', Real.log_mul (one_div_pos.2 hdn).ne' hpos.ne', one_div,
      Real.log_inv]
    ring

theorem isImg_self [Fintype Ψ] [DecidableEq Ψ] (M : FlagModel y Ψ N j) (z : (Σ k, ι k) → ℂ)
    (hz : z ∈ mcPts (mCoordIdeal y)) (F' F : FrameData ι Ψ N M.Ω M.blk)
    (h' : M.IsFrame F') (h : M.IsFrame F) (g' : M.GoodAt F' (mCoordIdeal (basePart M.blk z)))
    (g : M.GoodAt F (mCoordIdeal (basePart M.blk z))) (H : Ψ → Matrix (Fin N) (Fin N) ℂ) (hH : M.IsFlagOf F' z H) :
    ∃ z₀, SameOrbit z₀ z ∧ SameOrbit (basePart M.blk z₀) (basePart M.blk z) ∧
      M.IsFlagOf F z₀ fun τ => (idCover M).trans F' F (basePart M.blk z) τ * H τ := by
  have hzb := CPts.base_mem M hz
  have hT := FibreCount.trans_unit (idCover M) hzb h' h g' g
  refine (GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F z _ h hzb g (fun τ => ⟨(hT τ).1.mul (hH.2.1 τ).1, by
    rw [det_mul]; exact mul_ne_zero (hT τ).2 (hH.2.1 τ).2⟩) fun p k hp => ?_).2
  obtain ⟨a, ha, hz'⟩ := hH.2.2 p k hp
  have hd := CPts.detFac_ne_zero M.j_le p.2 (hT p.1).1 (hT p.1).2
  have hρ := rhoC_ne g g' p
  refine ⟨a * detFac j p.2 ((idCover M).trans F' F (basePart M.blk z) p.1) / rhoC M F F' p (basePart M.blk z),
    div_ne_zero (mul_ne_zero ha hd) hρ, fun m => ?_⟩
  have r := relC hzb h h' g g' hp (H p.1) (hH.2.1 p.1).1 m
  rw [hz' m, plk, trans_eq, div_mul_eq_mul_div, mul_assoc, r]
  field_simp

end PositivityTheory.Xgp.c_cov_self
end

theorem PositivityTheory.Xgp.t_c_cov_self : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), ∃ (Cv : FlagCover M M) (CR : CovReal FA Cv), Cv.deg = 1 ∧ (∀ p, CR.Re.ref p = FA.Re.ref (some p)) ∧ ∀ p t, CR.Re.line p t = FA.Re.line (some p) t := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hJ : ∀ z, z ∉ mcPts FA.Re.J := fun z h => by
    rw [FA.J_top] at h
    simpa using h.2 1 trivial
  have hne : Nonempty FA.S.X := FA.Re.nonempty_base
  let ϖ : ((Σ k, ι k) → ℂ) → FA.S.X := fun z =>
    if h : ∃ x, SameOrbit (FA.Re.R.lift x x) z then FA.Re.π h.choose else hne.some
  have hϖ : ∀ z x, SameOrbit (FA.Re.R.lift x x) z → ϖ z = FA.Re.π x := by
    intro z x hx
    have h : ∃ x, SameOrbit (FA.Re.R.lift x x) z := ⟨x, hx⟩
    simp only [ϖ, dif_pos h]
    rw [FA.Re.R.inj _ x (hJ _) (Cj.sameOrbit_trans h.choose_spec (Cj.sameOrbit_symm hx))]
  have hinj : Function.Injective FA.Re.π := by
    intro x x' hx
    have h1 := FA.Re.degree.2.2.2.2.1 (FA.Re.π x') (by rw [FA.br_empty]; exact Set.notMem_empty _)
    rw [FA.deg_one, Set.ncard_eq_one] at h1
    obtain ⟨a, ha⟩ := h1
    have m1 : x ∈ FA.Re.π ⁻¹' {FA.Re.π x'} := hx
    have m2 : x' ∈ FA.Re.π ⁻¹' {FA.Re.π x'} := rfl
    rw [ha] at m1 m2
    exact m1.trans m2.symm
  have hdeg : (PositivityTheory.Xgp.c_cov_self.idCover M).deg = 1 := IntermediateField.relfinrank_self _
  refine ⟨PositivityTheory.Xgp.c_cov_self.idCover M,
    { Re := FA.Re.comap some
      deg_eq := FA.deg_one.trans hdeg.symm
      ref_deg := fun p => congrArg HermLine.a (FA.ref_some p)
      step := FA.step
      ϖ := ϖ
      ϖ_torus := ?_
      π_eq := fun x => (hϖ _ x (Cj.sameOrbit_refl _)).symm
      line_pt := ?_
      flags := ?_
      metric := ?_ }, hdeg, fun _ => rfl, fun _ _ => rfl⟩
  · intro z z' hz ho
    obtain ⟨x, hx⟩ := FA.Re.R.surj z hz (hJ z)
    rw [hϖ z x hx, hϖ z' x (Cj.sameOrbit_trans hx (Cj.sameOrbit_symm ho))]
  · intro p t h0 h1 z hz
    obtain ⟨x, hx⟩ := FA.Re.R.surj z hz (hJ z)
    have e1 := FA.Re.line_eq (some p) t h0 h1 x
    have e2 := Cj.log_sub_orbit _ _ (FA.Re.line_deg (some p) t) hz.1 hx
    rw [hϖ z x hx]
    show Real.log ((FA.Re.line (some p) t).h z) = Real.log ((FA.Re.ref (some p)).h z) + _
    linarith
  · intro z hz F' F h' h g' g H hH x₀ hx₀
    obtain ⟨x, hx⟩ := FA.Re.R.surj z hz (hJ z)
    rw [hϖ z x hx] at hx₀
    obtain rfl := hinj hx₀
    obtain ⟨z₀, o1, o2, fl⟩ := PositivityTheory.Xgp.c_cov_self.isImg_self M z hz F' F h' h g' g H hH
    exact ⟨z₀, Cj.sameOrbit_trans o1 (Cj.sameOrbit_symm hx), o2, fl⟩
  · intro z hz z₀ _ F' F h' h g' g ho p H hH _ e' e
    have := PositivityTheory.Xgp.c_cov_self.metric_self M z hz z₀ F' F h' h g' g ho p H hH e' e
    rw [← FA.ref_some p] at this
    rw [← FA.ref_some p]
    exact this
end

