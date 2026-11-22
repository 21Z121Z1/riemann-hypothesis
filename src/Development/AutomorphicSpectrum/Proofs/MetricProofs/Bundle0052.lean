import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijective
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem re_pi_bijective : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), Function.Bijective FA.Re.π := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hdeg0 := FA.Re.degree
  unfold ReciprocityTheory.AnForm.M.IsDegreeOff at hdeg0
  have hdeg := hdeg0.2.2.2.2.1
  rw [FA.br_empty, FA.deg_one] at hdeg
  have h1 : ∀ x, ∃ a, FA.Re.π ⁻¹' {x} = {a} := fun x => Set.ncard_eq_one.1 (hdeg x (by simp))
  constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := h1 (FA.Re.π a)
    have ha : a ∈ FA.Re.π ⁻¹' {FA.Re.π a} := Set.mem_preimage.2 (Set.mem_singleton _)
    have hb : b ∈ FA.Re.π ⁻¹' {FA.Re.π a} := Set.mem_preimage.2 (Set.mem_singleton_iff.2 hab.symm)
    rw [hc] at ha hb
    exact (Set.mem_singleton_iff.1 ha).trans (Set.mem_singleton_iff.1 hb).symm
  · intro x
    obtain ⟨c, hc⟩ := h1 x
    have hcx : c ∈ FA.Re.π ⁻¹' {x} := by
      rw [hc]
      exact Set.mem_singleton c
    exact ⟨c, Set.mem_singleton_iff.1 (Set.mem_preimage.1 hcx)⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionIndexEquiv
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount

theorem sum_range_eq_choose (m : ℕ) : ∑ i ∈ Finset.range m, i = m.choose 2 := by
  rw [Finset.sum_range_id, Nat.choose_two_right]

theorem card_row (N j : ℕ) (hj : j ≤ N) (a : Fin N) :
    Fintype.card {b : Fin N // b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} =
      if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j) := by
  rw [Fintype.card_subtype]
  have key : (Finset.univ.filter fun b : Fin N => b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)).map
      Fin.valEmbedding = Finset.Ico (if (a : ℕ) < N - j then 0 else N - j) (a : ℕ) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨b, ⟨hba, hiff⟩, rfl⟩
      have hba' : (b : ℕ) < a := hba
      split_ifs with h
      · exact ⟨Nat.zero_le _, hba'⟩
      · exact ⟨Nat.le_of_not_lt (fun hb => h (hiff.mpr hb)), hba'⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, lt_trans h2 a.isLt⟩, ⟨h2, ?_⟩, rfl⟩
      show (a : ℕ) < N - j ↔ x < N - j
      split_ifs at h1 with h
      · exact ⟨fun _ => lt_trans h2 h, fun _ => h⟩
      · exact ⟨fun h' => absurd h' h, fun h' => absurd h1 (Nat.not_le.mpr h')⟩
  rw [← Finset.card_map Fin.valEmbedding, key, Nat.card_Ico]
  split_ifs <;> simp

theorem card_pairs (N j : ℕ) (hj : j ≤ N) :
    Fintype.card {p : Fin N × Fin N // p.2 < p.1 ∧ ((p.1 : ℕ) < N - j ↔ (p.2 : ℕ) < N - j)} =
      j.choose 2 + (N - j).choose 2 := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (a b : Fin N) => b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j))), Fintype.card_sigma]
  have h1 : ∀ a : Fin N, Fintype.card {b : Fin N // b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} =
      if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j) := card_row N j hj
  simp only [h1]
  have hs : ∑ a : Fin N, (if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j)) =
      ∑ i ∈ Finset.range N, (if i < N - j then i else i - (N - j)) :=
    Fin.sum_univ_eq_sum_range (fun i => if i < N - j then i else i - (N - j)) N
  rw [hs]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + j := ⟨N - j, by omega⟩
  have hM : M + j - j = M := by omega
  rw [hM, Finset.sum_range_add]
  have e1 : ∑ x ∈ Finset.range M, (if x < M then x else x - M) = ∑ x ∈ Finset.range M, x :=
    Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx))
  have e2 : ∑ x ∈ Finset.range j, (if M + x < M then M + x else M + x - M) =
      ∑ x ∈ Finset.range j, x :=
    Finset.sum_congr rfl (fun x _ => by rw [if_neg (by omega)]; omega)
  rw [e1, e2, sum_range_eq_choose, sum_range_eq_choose, add_comm]

theorem card_lowIdx (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : j ≤ N) :
    Fintype.card (LowIdx Ψ N j) = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  rw [← card_pairs N j hj, ← Fintype.card_prod]
  exact Fintype.card_congr
    { toFun := fun q => (q.1.1, ⟨q.1.2, q.2⟩)
      invFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem nonempty_paramEquiv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ), j ≤ N →
    d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) →
    Nonempty (Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)) := by
  intro Ψ _ _ N j n d hj hd
  apply Fintype.card_eq.mp
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, card_lowIdx Ψ N j hj,
    Fintype.card_unit, Fintype.card_fin]
  generalize Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) = t at hd ⊢
  omega

end GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFirst
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CWeight

section Calc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}

def SmMat (M : E → Matrix (Fin N) (Fin N) ℂ) (w : E) : Prop :=
  ∀ a b, ContDiffAt ℝ ∞ (fun u => M u a b) w

theorem SmMat.mul {M M' : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) (h' : SmMat M' w) :
    SmMat (fun u => M u * M' u) w := by
  intro a b
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun c _ => (h a c).mul (h' c b)

theorem SmMat.conjTranspose {M : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) :
    SmMat (fun u => (M u)ᴴ) w := by
  intro a b
  simp only [Matrix.conjTranspose_apply]
  exact (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt.comp w (h b a)

theorem SmMat.minor {M : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) (I J : Finset (Fin N)) :
    ContDiffAt ℝ ∞ (fun u => minorIJ (M u) I J) w := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply']
    refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul ?_
    exact contDiffAt_prod fun i _ => h _ _
  · simp only [dif_neg e]
    exact contDiffAt_const

theorem contDiffAt_blockPot (j : ℕ) (i : Fin N) {G h : E → Matrix (Fin N) (Fin N) ℂ} {w : E}
    (hG : SmMat G w) (hh : SmMat h w) (hpos : (G w).PosDef) (hdet : (h w).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun u => blockPot j i (G u) (h u)) w := by
  have hre : ∀ {f : E → ℂ}, ContDiffAt ℝ ∞ f w → 0 < f w →
      ContDiffAt ℝ ∞ (fun u => Real.log (f u).re) w := fun hf h0 =>
    (Complex.reCLM.contDiff.contDiffAt.comp w hf).log (Complex.lt_def.1 h0).1.ne'
  have hfac : ContDiffAt ℝ ∞ (fun u => detFac j i (G u)) w := by
    unfold detFac
    refine ContDiffAt.mul ?_ ?_
    · by_cases c : j ≤ (i : ℕ) + 1
      · simpa only [if_pos c] using hG.minor _ _
      · simpa only [if_neg c] using contDiffAt_const
    · by_cases c : (i : ℕ) + 1 = N
      · simpa only [if_pos c] using hG.minor _ _
      · simpa only [if_neg c] using contDiffAt_const
  have hfac0 : 0 < detFac j i (G w) := by
    unfold detFac
    refine mul_pos ?_ ?_
    · split_ifs
      · exact GramPot.minor_pos hpos _
      · exact zero_lt_one
    · split_ifs
      · exact GramPot.minor_pos hpos _
      · exact zero_lt_one
  unfold blockPot
  refine (contDiffAt_const.mul (hre hfac hfac0)).add ?_
  by_cases c : IsProperStep N j i
  · simp only [if_pos c]
    refine contDiffAt_const.mul (hre ((hh.conjTranspose.mul hG).mul hh |>.minor _ _) ?_)
    have hu : IsUnit (h w) := (Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit
    exact GramPot.minor_pos
      (hpos.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)) _
  · simp only [if_neg c]
    exact contDiffAt_const

end Calc

section Chart

variable {e n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem contDiffAt_comp_holoMap {A : FinHolAtlas e X} {B : FinHolAtlas n Y} {pr : X → Y}
    (hp : HoloMap A B pr) {U : Set Y} (hU : IsOpen U) {f : Y → ℝ} (hf : B.SmoothOn U f)
    (c : Fin A.n) {w : Fin e → ℂ} (hw : w ∈ (A.chart c).target)
    (hwU : pr ((A.chart c).symm w) ∈ U) :
    ContDiffAt ℝ ∞ (fun u => f (pr ((A.chart c).symm u))) w := by
  obtain ⟨k, hk⟩ := B.cover (pr ((A.chart c).symm w))
  have h1 : ContDiffAt ℝ ∞ (f ∘ (B.chart k).symm) (B.chart k (pr ((A.chart c).symm w))) := by
    refine (hf k).contDiffAt
      (((B.chart k).isOpen_inter_preimage_symm hU).mem_nhds ⟨(B.chart k).map_source hk, ?_⟩)
    simpa [(B.chart k).left_inv hk] using hwU
  have h2 : ContDiffAt ℝ ∞ (B.chart k ∘ pr ∘ (A.chart c).symm) w :=
    (hp.2 c k w ⟨hw, hk⟩).contDiffAt.restrict_scalars ℝ
  refine (ContDiffAt.comp w h1 h2).congr_of_eventuallyEq ?_
  filter_upwards [((A.chart c).isOpen_inter_preimage_symm
    ((B.chart k).open_source.preimage hp.1)).mem_nhds ⟨hw, hk⟩] with u hu
  simp only [Function.comp_apply, (B.chart k).left_inv hu.2]

theorem contDiffAt_of_re_im {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℂ} {w : E}
    (h1 : ContDiffAt ℝ ∞ (fun u => (g u).re) w) (h2 : ContDiffAt ℝ ∞ (fun u => (g u).im) w) :
    ContDiffAt ℝ ∞ g w := by
  have e : g = fun u => (((g u).re : ℝ) : ℂ) + (((g u).im : ℝ) : ℂ) * Complex.I := by
    funext u
    exact (Complex.re_add_im _).symm
  rw [e]
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp w h1).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp w h2).mul contDiffAt_const)

end Chart

theorem smoothOn_stepPh : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → R.A.SmoothOn (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (stepPh M BM p v R pr) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hS hP c w hw
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨hwt, hwb⟩ := hw
  have hb : pr ((R.A.chart c).symm w) ∉ bdry BM.s := hwb
  obtain ⟨W, l, H, D, hWo, hyW, hWU, hWO, hH, hHd, hD, hD0, heq⟩ :=
    hS ((R.A.chart c).symm w) ((R.A.chart c).symm w) (R.mem_U _)
  have hcl : IsClosed (bdry BM.s) := isClosed_bdry_of_isSection _ _ _ _ _ BM.sec
  have hOo : IsOpen (W ∩ pr ⁻¹' (bdry BM.s)ᶜ) := hWo.inter (hcl.isOpen_compl.preimage hp.1)
  have hnhd : (R.A.chart c).target ∩ (R.A.chart c).symm ⁻¹' (W ∩ pr ⁻¹' (bdry BM.s)ᶜ) ∈ 𝓝 w :=
    ((R.A.chart c).isOpen_inter_preimage_symm hOo).mem_nhds ⟨hwt, hyW, hb⟩
  have hOb : IsOpen (BM.O l \ bdry BM.s) := (BM.O_open l).sdiff hcl
  have hmemO : pr ((R.A.chart c).symm w) ∈ BM.O l \ bdry BM.s := ⟨hWO _ hyW, hb⟩
  have hG : SmMat (fun u => BM.G l p.1 (pr ((R.A.chart c).symm u))) w := fun a b =>
    contDiffAt_of_re_im
      (contDiffAt_comp_holoMap hp hOb (BM.G_smooth l p.1 a b).1 c hwt hmemO)
      (contDiffAt_comp_holoMap hp hOb (BM.G_smooth l p.1 a b).2 c hwt hmemO)
  have hHm : SmMat (fun u => H ((R.A.chart c).symm u)) w := fun a b =>
    (hH a b c w ⟨hwt, hyW⟩).contDiffAt.restrict_scalars ℝ
  have hDm : ContDiffAt ℝ ∞ (fun u => D ((R.A.chart c).symm u)) w :=
    (hD c w ⟨hwt, hyW⟩).contDiffAt.restrict_scalars ℝ
  have hD1 : D ((R.A.chart c).symm w) ≠ 0 := hD0 _ hyW
  have hbp := contDiffAt_blockPot j p.2 hG hHm (BM.G_pos l p.1 _ hmemO).2 (hHd _ hyW).2
  have hlog : ContDiffAt ℝ ∞ (fun u => Real.log ‖D ((R.A.chart c).symm u)‖) w :=
    (hDm.norm ℝ hD1).log (norm_ne_zero_iff.2 hD1)
  have hpot : ContDiffAt ℝ ∞ (fun u => Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h
      (R.lift ((R.A.chart c).symm w) ((R.A.chart c).symm u)))) w :=
    (hP.1 ((R.A.chart c).symm w) c).contDiffAt
      (((R.A.chart c).isOpen_inter_preimage_symm (R.isOpen_U _)).mem_nhds ⟨hwt, R.mem_U _⟩)
  refine ((hbp.add hlog).sub hpot).congr_of_eventuallyEq ?_
  filter_upwards [hnhd] with u hu
  have := heq _ hu.2.1 hu.2.2
  simp only [Function.comp_apply]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.CWeight
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackThird
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize

theorem continuousAt_of_chart {X E F : Type*} [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace F]
    (c : OpenPartialHomeomorph X E) {f : X → F} {x : X} (hx : x ∈ c.source)
    (h : ContinuousAt (f ∘ c.symm) (c x)) : ContinuousAt f x := by
  have h1 : ContinuousAt ((f ∘ c.symm) ∘ c) x := ContinuousAt.comp h (c.continuousAt hx)
  refine h1.congr ?_
  filter_upwards [c.open_source.mem_nhds hx] with z hz
  simp [c.left_inv hz]

theorem holoOn_continuousAt {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) {W : Set X}
    {g : X → ℂ} (h : A.HoloOn W g) {x : X} (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  refine continuousAt_of_chart (A.chart j) hj ?_
  have hm : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  exact (h j _ hm).continuousAt

theorem smoothOn_continuousAt {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) {W : Set X}
    (hW : IsOpen W) {g : X → ℝ} (h : A.SmoothOn W g) {x : X} (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  refine continuousAt_of_chart (A.chart j) hj ?_
  have hm : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hW
  exact ((h j).continuousOn).continuousAt (ho.mem_nhds hm)

variable {N : ℕ}

theorem gram_cmp {k : ℕ} (hk : k ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (V : Matrix (Fin N) (Fin k) ℂ) {m : ℝ}
    (hm : 1 ≤ m) (hG : G.PosDef) (h1 : ((m : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef)
    (h2 : ((m : ℂ) • G - 1).PosSemidef) (hV : LinearIndependent ℂ Vᵀ) :
    |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * (1 : Matrix (Fin N) (Fin N) ℂ) * V).det.re| ≤ N * Real.log m := by
  refine (GlobalTheory.T.log_det_comparable_gram_bound N k G 1 V m hm Matrix.PosDef.one hG h1 h2 hV).trans ?_
  have : (k : ℝ) ≤ N := by exact_mod_cast hk
  exact mul_le_mul_of_nonneg_right this (Real.log_nonneg hm)

theorem card_le (S : Finset (Fin N)) : S.card ≤ N := by
  simpa using S.card_le_univ

theorem blockPot_sub_le (j : ℕ) (i : Fin N) {G h : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (hd : h.det ≠ 0)
    {m : ℝ} (hm : 1 ≤ m) (h1 : ((m : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef)
    (h2 : ((m : ℂ) • G - 1).PosSemidef) :
    |blockPot j i G h - blockPot j i 1 h| ≤ (3 / 2) * N * Real.log m := by
  obtain ⟨hS, hHS, hP⟩ := GramPot.blockPot_eq_gram N j i G h
  obtain ⟨-, -, hP1⟩ := GramPot.blockPot_eq_gram N j i 1 h
  have e1 := hP hG
  have e2 := hP1 Matrix.PosDef.one
  have tW := abs_le.1 (gram_cmp (card_le (wIdx N j)) (selM (wIdx N j)) hm hG h1 h2 (hS _))
  have tO := abs_le.1 (gram_cmp (card_le (omIdx N j)) (selM (omIdx N j)) hm hG h1 h2 (hS _))
  have tH := abs_le.1 (gram_cmp (card_le (stepCols N j i)) (h * selM (stepCols N j i)) hm hG h1 h2 (hHS hd _))
  have hl : 0 ≤ (N : ℝ) * Real.log m := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hm)
  rw [e1, e2, abs_le]
  split_ifs <;> constructor <;> linarith [tW.1, tW.2, tO.1, tO.2, tH.1, tH.2]

theorem size_abs {G : Matrix (Fin N) (Fin N) ℂ} {r c : ℝ} (hr : 1 ≤ r) (hG : G.PosDef)
    (h : (((r ^ c : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef ∧
      (((r ^ c : ℝ) : ℂ) • G - 1).PosSemidef) :
    (((r ^ |c| : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef ∧
      (((r ^ |c| : ℝ) : ℂ) • G - 1).PosSemidef := by
  have hd : (0 : ℝ) ≤ r ^ |c| - r ^ c := sub_nonneg.2 (Real.rpow_le_rpow_of_exponent_le hr (le_abs_self c))
  have hd' : (0 : ℂ) ≤ ((r ^ |c| - r ^ c : ℝ) : ℂ) := by exact_mod_cast hd
  constructor
  · have := h.1.add (Matrix.PosSemidef.one.smul hd')
    convert this using 1
    push_cast
    module
  · have := h.2.add (hG.posSemidef.smul hd')
    convert this using 1
    push_cast
    module

theorem gram_one_pos {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) (S : Finset (Fin N)) :
    0 < (minorIJ (hᴴ * 1 * h) S S).re := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 hd.isUnit
  have hp : (hᴴ * 1 * h).PosDef :=
    Matrix.PosDef.one.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
  exact (Complex.lt_def.1 (GramPot.minor_pos hp S)).1

theorem continuous_gram (S : Finset (Fin N)) :
    Continuous fun h : Matrix (Fin N) (Fin N) ℂ => (minorIJ (hᴴ * 1 * h) S S).re := by
  simp only [minorIJ, dif_pos]
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine Continuous.matrix_submatrix ?_ _ _
  fun_prop

theorem continuousAt_blockPot_one {X : Type*} [TopologicalSpace X] (j : ℕ) (i : Fin N)
    {H : X → Matrix (Fin N) (Fin N) ℂ} {x : X} (hH : ∀ a b, ContinuousAt (fun y => H y a b) x)
    (hd : (H x).det ≠ 0) : ContinuousAt (fun y => blockPot j i 1 (H y)) x := by
  have hc : ContinuousAt H x :=
    continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => hH a b
  unfold blockPot
  refine continuousAt_const.add ?_
  split_ifs
  · refine continuousAt_const.mul (ContinuousAt.log ((continuous_gram _).continuousAt.comp hc) ?_)
    exact (gram_one_pos hd _).ne'
  · exact continuousAt_const

theorem stepPh_le_log : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → ∃ C₁ : ℝ, ∀ x ∉ bdry (fun x y => BM.s (pr x) (pr y)), |stepPh M BM p v R pr x| ≤ C₁ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hch hpot
  have hr : ∀ x, Real.exp 1 ≤ rW BM.L BM.s x := fun x => by
    have := BM.norm_le x
    simp only [rW]
    linarith
  have hrpos : ∀ x, 0 < rW BM.L BM.s x := fun x => (Real.exp_pos 1).trans_le (hr x)
  have hr1 : ∀ x, 1 ≤ rW BM.L BM.s x := fun x =>
    (by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) ≤ Real.exp 1).trans (hr x)
  have hlog : ∀ x, 1 ≤ Real.log (rW BM.L BM.s x) := fun x =>
    (Real.le_log_iff_exp_le (hrpos x)).2 (hr x)
  have key : ∀ y₀ : R.X, ∃ t ∈ 𝓝 y₀, ∃ C : ℝ, ∀ x ∈ t, x ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      |stepPh M BM p v R pr x| ≤ C * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
    intro y₀
    obtain ⟨W, l, H, D, hW, hy₀, -, hO, hH, hHd, hD, hDne, heq⟩ := hch y₀ y₀ (R.mem_U y₀)
    let u : R.X → ℝ := fun y' => blockPot j p.2 1 (H y') + Real.log ‖D y'‖ -
      Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift y₀ y'))
    have hu : ContinuousAt u y₀ := by
      refine ((continuousAt_blockPot_one j p.2 (fun a b => holoOn_continuousAt R.A (hH a b) hy₀)
        (hHd y₀ hy₀).2).add ?_).sub ?_
      · exact ContinuousAt.log (holoOn_continuousAt R.A hD hy₀).norm (norm_ne_zero_iff.2 (hDne y₀ hy₀))
      · exact smoothOn_continuousAt R.A (R.isOpen_U y₀) (hpot.1 y₀) (R.mem_U y₀)
    refine ⟨W ∩ {y' | |u y'| < |u y₀| + 1}, inter_mem (hW.mem_nhds hy₀)
      (hu.abs.eventually_lt continuousAt_const (lt_add_one _)), (3 / 2) * N * |BM.Cst| + (|u y₀| + 1), ?_⟩
    rintro y' ⟨hy'W, hy'u⟩ hb
    have hb' : pr y' ∉ bdry BM.s := hb
    have hmem : pr y' ∈ BM.O l \ bdry BM.s := ⟨hO y' hy'W, hb'⟩
    obtain ⟨-, hpd⟩ := BM.G_pos l p.1 _ hmem
    have hs := size_abs (hr1 (pr y')) hpd (BM.size l p.1 _ hmem)
    have hm1 : 1 ≤ rW BM.L BM.s (pr y') ^ |BM.Cst| := Real.one_le_rpow (hr1 _) (abs_nonneg _)
    have hdiff := blockPot_sub_le j p.2 hpd (hHd y' hy'W).2 hm1 hs.1 hs.2
    rw [Real.log_rpow (hrpos _)] at hdiff
    have e' := heq y' hy'W hb'
    have hL := hlog (pr y')
    have hsum : stepPh M BM p v R pr y' = (blockPot j p.2 (BM.G l p.1 (pr y')) (H y') - blockPot j p.2 1 (H y')) + u y' := by
      simp only [u]
      linarith
    change |stepPh M BM p v R pr y'| ≤ _ * Real.log (rW BM.L BM.s (pr y'))
    rw [hsum]
    have hu' : |u y'| < |u y₀| + 1 := hy'u
    have hc : |u y₀| + 1 ≤ (|u y₀| + 1) * Real.log (rW BM.L BM.s (pr y')) :=
      le_mul_of_one_le_right (by positivity) hL
    calc _ ≤ |blockPot j p.2 (BM.G l p.1 (pr y')) (H y') - blockPot j p.2 1 (H y')| + |u y'| := abs_add_le _ _
      _ ≤ (3 / 2) * N * (|BM.Cst| * Real.log (rW BM.L BM.s (pr y'))) + (|u y₀| + 1) * Real.log (rW BM.L BM.s (pr y')) := by
        linarith
      _ = _ := by ring
  have hlogr : ∀ x, 0 ≤ Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := fun x =>
    zero_le_one.trans (hlog (pr x))
  obtain ⟨C, hC⟩ := (isCompact_univ (X := R.X)).induction_on
    (p := fun S => ∃ C : ℝ, ∀ x ∈ S, x ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      |stepPh M BM p v R pr x| ≤ C * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x))
    ⟨0, fun x hx => absurd hx (Set.notMem_empty x)⟩
    (fun s t hst ⟨C, hC⟩ => ⟨C, fun x hx => hC x (hst hx)⟩)
    (fun s t ⟨C, hC⟩ ⟨C', hC'⟩ => ⟨max C C', fun x hx hb => hx.elim
      (fun h => (hC x h hb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlogr x)))
      (fun h => (hC' x h hb).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hlogr x)))⟩)
    (fun y₀ _ => by
      obtain ⟨t, ht, C, hC⟩ := key y₀
      exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, C, hC⟩)
  exact ⟨C, fun x hb => hC x (Set.mem_univ x) hb⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmoothStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubini_study_metric_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℤ), IsSmoothHerm (fsHerm ι a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramMatrixSubScalarPosSemidefStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_sub_scalar_posSemidef : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a P Q : ℝ), 0 < a → 0 < P → P ≤ Q → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ Q) → (∀ p q, ‖V x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ Q) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * P ^ 2 * Q / a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.gram_grad_scaled | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.gram_grad_scaled | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.gram_grad_scaled <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianRestrictionOrthonormalCoordsStatement
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_restriction_orthonormal_coords : ∀ (g m : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ W : Submodule ℂ (Fin g → ℂ), Module.finrank ℂ W = m → ∃ c : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ z ∈ W, ∀ z' ∈ W, z' ⬝ᵥ Hm *ᵥ star z = ∑ i, starRingEnd ℂ (c z i) * c z' i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords | exact GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicConjugatePullbackStatement
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_conjugate_pullback : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} (c : X → X), Continuous c → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → ∀ {V : Set X} {g : X → ℂ}, A.HoloOn V g → A.HoloOn (c ⁻¹' V) (fun y => starRingEnd ℂ (g (c y))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_conj_comp | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_conj_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_conj_comp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicDegreeOneBiholomorphismStatement
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_degree_one_biholomorphism : ∀ {e : ℕ} {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X), HoloMap B A h → IsDegreeOff A B h 1 ∅ → ∃ g : X → Y, (∀ y, g (h y) = y) ∧ (∀ x, h (g x) = x) ∧ HoloMap A B g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundaryStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_section_boundary : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsSection A L s → IsClosed (bdry s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection | exact GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeCommensurableBoundStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labelled_degree_commensurable_bound : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ) (F : Submodule (𝓞 L) V) (𝔞 : Ideal (𝓞 L)), A.IsAdapted s v q → 𝔞 ≠ ⊥ → 𝔞 • F ≤ A.eig s → 𝔞 • A.eig s ≤ F → |A.labDeg s F v q - A.labDeg s (A.eig s) v q| ≤ (r + k) * Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L := by
  first | exact @GlobalTheory.CompanionTheory.Relay.labelled_degree_commensurable_bound | exact GlobalTheory.CompanionTheory.Relay.labelled_degree_commensurable_bound | (intros; apply GlobalTheory.CompanionTheory.Relay.labelled_degree_commensurable_bound <;> assumption)
end

