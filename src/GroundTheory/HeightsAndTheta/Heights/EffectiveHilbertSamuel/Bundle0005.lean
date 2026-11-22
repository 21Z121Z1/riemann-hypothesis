import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.SymbolExtensionProperty
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Inhabitants
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.AnalyticAtOfHoloOn
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M

noncomputable section

namespace EffectiveHilbertSamuelJetLemmas

variable {D : ℕ} {U : Type} [TopologicalSpace U]

theorem chart_sum_eq (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (a : ℕ)
    (h : (Fin D → ℕ) → Fin A.n → U → ℂ) (c : Fin A.n) :
    (∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s α * h α) c ∘ (A.chart c).symm =
      fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        (∏ i, (s i c ∘ (A.chart c).symm) z ^ α i) * (h α c ∘ (A.chart c).symm) z := by
  funext z
  simp [sPow, Finset.sum_apply, Finset.prod_apply]

theorem analyticAt_of_holoOn (A : FinHolAtlas D U) {f : U → ℂ} {c : Fin A.n}
    (hf : A.HoloOn (A.chart c).source f) {x : U} (hx : x ∈ (A.chart c).source) :
    AnalyticAt ℂ (f ∘ (A.chart c).symm) (A.chart c x) :=
  hf c _ ⟨(A.chart c).map_source hx, by rw [Set.mem_preimage, (A.chart c).left_inv hx]; exact hx⟩

theorem exists_unit {N : ℕ} (A : FinHolAtlas D U) (e : Fin N → Fin A.n → U → ℂ)
    (he : NoCommonZero A e) {S : Set U} (hS : S.Finite) :
    ∃ c : Fin N → ℂ, ∀ x ∈ S, lin e c (chartIdx A x) x ≠ 0 := by
  classical
  let φ : U → (Fin N → ℂ) →ₗ[ℂ] ℂ := fun x =>
    ∑ k, e k (chartIdx A x) x • (LinearMap.proj k : (Fin N → ℂ) →ₗ[ℂ] ℂ)
  have hφ : ∀ x c, φ x c = lin e c (chartIdx A x) x := by
    intro x c
    simp [φ, lin, Finset.sum_apply, mul_comm]
  have hne : ∀ x, LinearMap.ker (φ x) ≠ ⊤ := by
    intro x htop
    obtain ⟨k, hk⟩ := he x
    have h0 : Pi.single k 1 ∈ LinearMap.ker (φ x) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hφ] at h0
    have hl : lin e (Pi.single k 1) = e k := by simp [lin, Pi.single_apply]
    rw [hl] at h0
    exact hk h0
  have hss := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt hS.toFinset
    (fun x => LinearMap.ker (φ x)) hne (by rw [ENat.card_eq_top_of_infinite]; exact ENat.natCast_lt_top _)
  obtain ⟨c, -, hc⟩ := Set.exists_of_ssubset hss
  refine ⟨c, fun x hx h0 => hc ?_⟩
  rw [Set.mem_iUnion₂]
  exact ⟨x, hS.mem_toFinset.2 hx, by rw [SetLike.mem_coe, LinearMap.mem_ker, hφ]; exact h0⟩

theorem _root_.GroundTheory.Heights₂.Heights.EffectiveHS.SymOnto.proof
    (hJ : JetOfMonomialSum.Statement) : SymOnto.Statement := by
  classical
  intro D T X Z Y hD hT hRes a ha g
  obtain ⟨c₀, hc₀⟩ := exists_unit X.A X.e X.gen Z.finite
  set w : Fin X.A.n → X.U → ℂ := lin X.e c₀ with hw
  set j := T - a with hj
  have hsum : ∀ α ∈ Finset.Nat.antidiagonalTuple D a, ∑ i, α i = a := fun α hα =>
    Finset.Nat.mem_antidiagonalTuple.1 hα
  choose m hmV hm using fun α : Fin D → ℕ =>
    hRes (fun y => g α y / w (chartIdx X.A y) y ^ j)
  have hwj : w ^ j = ∑ ι : Fin j → Fin X.N, (∏ l, c₀ (ι l)) • ∏ l, X.e (ι l) := by
    rw [← Fin.prod_const j w, hw, lin, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    funext k x
    simp [Finset.prod_apply, Finset.prod_mul_distrib]
  have pt : ∀ x ∈ zeroSet X.A Z.s,
      (∀ k < a, iteratedFDeriv ℂ k ((∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        sPow Z.s α * (w ^ j * m α)) (chartIdx X.A x) ∘ (X.A.chart (chartIdx X.A x)).symm)
        (X.A.chart (chartIdx X.A x) x) = 0) ∧
      ∀ v : Fin D → ℂ, iteratedFDeriv ℂ a ((∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        sPow Z.s α * (w ^ j * m α)) (chartIdx X.A x) ∘ (X.A.chart (chartIdx X.A x)).symm)
          (X.A.chart (chartIdx X.A x) x) (fun _ => v) / (a.factorial : ℂ) =
        sJac X.A Z.s (chartIdx X.A x) x * ∑ α ∈ Finset.Nat.antidiagonalTuple D a,
          (∏ i, (sJacMap X.A Z.s (chartIdx X.A x) x v i) ^ α i) * g α x := by
    intro x hx
    set c := chartIdx X.A x with hc
    have hxc : x ∈ (X.A.chart c).source := Classical.choose_spec (X.A.cover x)
    have hlin : ∀ c' : Fin X.N → ℂ, lin X.e c' ∈ X.L.sections 1 := fun c' =>
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (X.e_mem k)
    have au : ∀ i, AnalyticAt ℂ (Z.s i c ∘ (X.A.chart c).symm) (X.A.chart c x) := fun i =>
      analyticAt_of_holoOn X.A ((hlin (Z.c i)).1 c) hxc
    have aw : AnalyticAt ℂ (w c ∘ (X.A.chart c).symm) (X.A.chart c x) :=
      analyticAt_of_holoOn X.A ((hlin c₀).1 c) hxc
    have ah : ∀ α, AnalyticAt ℂ ((w ^ j * m α) c ∘ (X.A.chart c).symm) (X.A.chart c x) :=
      fun α => (aw.pow j).mul (analyticAt_of_holoOn X.A ((Y.V_le 0 (hmV α)).1 c) hxc)
    have hz : ∀ i, (Z.s i c ∘ (X.A.chart c).symm) (X.A.chart c x) = 0 := fun i => by
      simp only [Function.comp_apply, (X.A.chart c).left_inv hxc]; exact hx i
    obtain ⟨h1, -, h3⟩ := hJ D D (fun i => Z.s i c ∘ (X.A.chart c).symm)
      (fun α => (w ^ j * m α) c ∘ (X.A.chart c).symm) _ a au hz ah
    have hF := chart_sum_eq X.A Z.s a (fun α => w ^ j * m α) c
    rw [hF]
    refine ⟨h1, fun v => ?_⟩
    rw [h3 v]
    have hJ0 : sJac X.A Z.s c x ≠ 0 := Z.nondeg x hx
    have hcoef : ∀ α, ((w ^ j * m α) c ∘ (X.A.chart c).symm) (X.A.chart c x) =
        g α x * sJac X.A Z.s c x := by
      intro α
      have hr := hm α x hx
      have hw0 : w c x ≠ 0 := hc₀ x hx
      simp only [res] at hr
      rw [div_eq_div_iff hJ0 (pow_ne_zero _ hw0)] at hr
      simp only [Function.comp_apply, (X.A.chart c).left_inv hxc, Pi.mul_apply, Pi.pow_apply]
      linear_combination hr
    have hder : ∀ i, sJacMap X.A Z.s c x v i =
        fderiv ℂ (Z.s i c ∘ (X.A.chart c).symm) (X.A.chart c x) v := by
      intro i
      show (fderiv ℂ (fun z i => (Z.s i c ∘ (X.A.chart c).symm) z) (X.A.chart c x)) v i = _
      rw [fderiv_pi (fun i => (au i).differentiableAt)]
      rfl
    rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero a)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hcoef α]
    simp only [hder]
    ring
  refine ⟨∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow Z.s α * (w ^ j * m α), ?_,
    fun x hx => (pt x hx).1, fun x hx => (pt x hx).2⟩
  refine Submodule.sum_mem _ fun α hα => ?_
  have hexp : sPow Z.s α * (w ^ j * m α) =
      ∑ ι : Fin j → Fin X.N, (∏ l, c₀ (ι l)) • (sPow Z.s α * (∏ l, X.e (ι l)) * m α) := by
    rw [hwj, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [hexp]
  exact Submodule.sum_mem _ fun ι _ => Submodule.smul_mem _ _ (Submodule.mem_sup_left
    (Submodule.subset_span ⟨α, j, ι, m α, hmV α, by rw [hsum α hα]; omega,
      by rw [hsum α hα]; exact ha, rfl⟩))

theorem _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS.EffectiveHilbertSamuelJetSecond.proof
    (hJ : JetOfMonomialSum.Statement) : IndefiniteRowSideFullHecke.EffectiveHS.EffectiveHilbertSamuelJetSecond.Statement := by
  classical
  intro D hD X Y _ _ _ _ _ _ A d s hGood hRes hUnit a ha g
  obtain ⟨c₀, hc₀⟩ := hUnit
  set j := d.T - a with hj
  choose m hmV hm using fun α : Fin D → ℕ =>
    hRes (fun y => g α y / d.W.sec c₀ (chartIdx A y) y ^ j)
  let s' : Fin D → Fin A.n → X → ℂ := fun i => d.W.sec (s i)
  let hh : (Fin D → ℕ) → Fin A.n → X → ℂ := fun α =>
    IndefiniteRowSideFullHecke.EffectiveHS.secMul (d.wProd fun _ : Fin j => c₀) (m α)
  have hF : (∑ α ∈ IndefiniteRowSideFullHecke.EffectiveHS.tuples D a,
      IndefiniteRowSideFullHecke.EffectiveHS.secMul (d.monoSec s α) (hh α)) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s' α * hh α := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [TranslateEq.sPow_eq_monoSec]
    rfl
  refine ⟨∑ α ∈ IndefiniteRowSideFullHecke.EffectiveHS.tuples D a, IndefiniteRowSideFullHecke.EffectiveHS.secMul (d.monoSec s α) (hh α),
    Submodule.sum_mem _ fun α hα => Submodule.mem_sup_left (Submodule.subset_span
      ⟨j, α, fun _ => c₀, m α, hmV α, ?_, ?_, rfl⟩), ?_⟩
  · rw [Finset.Nat.mem_antidiagonalTuple.1 hα]; omega
  · rw [Finset.Nat.mem_antidiagonalTuple.1 hα]; exact ha
  have hsec : ∀ c' : Fin d.W.n → ℂ,
      d.W.sec c' ∈ IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.sectionSpace d.L 1 := fun c' =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (d.W.mem k)
  have pt : ∀ x ∈ d.zeroU s,
      (∀ k < a, iteratedFDeriv ℂ k ((∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s' α * hh α)
        (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) = 0) ∧
      iteratedFDeriv ℂ a ((∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s' α * hh α)
        (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) =
        ∑ α ∈ IndefiniteRowSideFullHecke.EffectiveHS.tuples D a, (g α x * d.sJac s (chartIdx A x) x) •
          iteratedFDeriv ℂ a (fun z => ∏ i, d.sLoc s (chartIdx A x) z i ^ α i)
            (A.chart (chartIdx A x) x) := by
    intro x hx
    set c := chartIdx A x with hc
    have hxc : x ∈ (A.chart c).source := Classical.choose_spec (A.cover x)
    have au : ∀ i, AnalyticAt ℂ (s' i c ∘ (A.chart c).symm) (A.chart c x) := fun i =>
      analyticAt_of_holoOn A ((hsec (s i)).1 c) hxc
    have aw : AnalyticAt ℂ (d.W.sec c₀ c ∘ (A.chart c).symm) (A.chart c x) :=
      analyticAt_of_holoOn A ((hsec c₀).1 c) hxc
    have hhc : ∀ α, hh α c ∘ (A.chart c).symm = fun z =>
        (d.W.sec c₀ c ∘ (A.chart c).symm) z ^ j * (m α c ∘ (A.chart c).symm) z := by
      intro α
      funext z
      simp [hh, IndefiniteRowSideFullHecke.EffectiveHS.secMul, IndefiniteRowSideFullHecke.EffectiveHS.FSData.wProd]
    have ah : ∀ α, AnalyticAt ℂ (hh α c ∘ (A.chart c).symm) (A.chart c x) := by
      intro α
      rw [hhc α]
      exact (aw.pow j).mul
        (analyticAt_of_holoOn A ((TranslateEq.space_le_topForms d 0 (hmV α)).1 c) hxc)
    have hz : ∀ i, (s' i c ∘ (A.chart c).symm) (A.chart c x) = 0 := fun i => by
      simp only [Function.comp_apply, (A.chart c).left_inv hxc]; exact hx i
    obtain ⟨h1, h2, -⟩ := hJ D D (fun i => s' i c ∘ (A.chart c).symm)
      (fun α => hh α c ∘ (A.chart c).symm) _ a au hz ah
    rw [chart_sum_eq A s' a hh c]
    refine ⟨h1, ?_⟩
    rw [h2]
    have hJ0 : d.sJac s c x ≠ 0 := hGood.etale x hx
    refine Finset.sum_congr rfl fun α _ => ?_
    have hr := hm α x hx
    have hw0 : d.W.sec c₀ c x ≠ 0 := hc₀ x hx
    simp only [IndefiniteRowSideFullHecke.EffectiveHS.FSData.res] at hr
    rw [div_eq_div_iff hJ0 (pow_ne_zero _ hw0)] at hr
    have hcoef : (hh α c ∘ (A.chart c).symm) (A.chart c x) = g α x * d.sJac s c x := by
      rw [hhc α]
      simp only [Function.comp_apply, (A.chart c).left_inv hxc]
      linear_combination hr
    rw [hcoef]
    rfl
  rw [hF]
  exact ⟨fun x hx => (pt x hx).1, fun x hx => (pt x hx).2⟩

end EffectiveHilbertSamuelJetLemmas

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.InhabitantsExt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace ExtInhabitants

def c0 : Fin (flatAtlas 1).n := ⟨0, Nat.one_pos⟩

theorem piece_flat : piece (flatAtlas 1) c0 = univ := by
  ext y
  simp only [piece, mem_ofPred_eq, mem_univ, iff_true]
  exact ⟨by simp, fun k hk => absurd hk (by simp [c0, Fin.lt_def])⟩

theorem chartIntegral_flat (f : Fin (flatAtlas 1).n → (Fin 1 → ℂ) → ℝ≥0∞) :
    chartIntegral (flatAtlas 1) f = ∫⁻ y, f c0 y := by
  unfold chartIntegral
  rw [Fintype.sum_subsingleton _ c0, piece_flat, Measure.restrict_univ]
  simp

theorem exp_neg_wt (m : ℕ) (y : Fin 1 → ℂ) :
    Real.exp (-exEmb.wt m c0 y) = ((1 + ‖y 0‖ ^ 2) ^ m)⁻¹ := by
  have he : ∑ k : Fin 2, ‖exE k c0 y‖ ^ 2 = 1 + ‖y 0‖ ^ 2 := by
    simp [exE, Fin.sum_univ_two]
  have he₂ : ∑ k : Fin 1, ‖exE₂ k c0 y‖ ^ 2 = 1 := by simp [exE₂]
  simp only [EmbDatum.wt, fsWeight]
  change Real.exp (-(Real.log (∑ k : Fin 1, ‖exE₂ k c0 y‖ ^ 2) +
    (m : ℝ) * Real.log (∑ k : Fin 2, ‖exE k c0 y‖ ^ 2))) = _
  rw [he, he₂, Real.log_one, zero_add, Real.exp_neg, Real.exp_nat_mul,
    Real.exp_log (by positivity)]

theorem one_add_pow_three_le (t : ℝ) (ht : 0 ≤ t) : (1 + t) ^ 3 ≤ 4 * (1 + t ^ 2) ^ 2 := by
  nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (t ^ 2 - t), sq_nonneg t, mul_nonneg ht (sq_nonneg t),
    mul_nonneg ht (sq_nonneg (t - 1))]

theorem lintegral_inv_one_add_sq_sq_lt_top (c : ℝ) :
    ∫⁻ y : Fin 1 → ℂ, ENNReal.ofReal (c * ((1 + ‖y 0‖ ^ 2) ^ 2)⁻¹) < ⊤ := by
  have hfin : (Module.finrank ℝ (Fin 1 → ℂ) : ℝ) < 3 := by
    rw [Module.finrank_pi_fintype]; simp; norm_num
  have hI := finite_integral_one_add_norm (E := Fin 1 → ℂ) (μ := volume) hfin
  have hpt : ∀ y : Fin 1 → ℂ, ENNReal.ofReal (c * ((1 + ‖y 0‖ ^ 2) ^ 2)⁻¹) ≤
      ENNReal.ofReal (4 * |c|) * ENNReal.ofReal ((1 + ‖y‖) ^ (-(3 : ℝ))) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hy : ‖y‖ ≤ ‖y 0‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
      rw [Subsingleton.elim i 0]
    have hr : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖) ^ 3)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      norm_cast
    rw [hr]
    have he : ((1 + ‖y 0‖ ^ 2) ^ 2)⁻¹ ≤ 4 * ((1 + ‖y 0‖) ^ 3)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      rw [inv_mul_le_iff₀ (by positivity)]
      linarith [one_add_pow_three_le ‖y 0‖ (norm_nonneg _)]
    have hmono : ((1 + ‖y 0‖) ^ 3)⁻¹ ≤ ((1 + ‖y‖) ^ 3)⁻¹ := by
      apply inv_anti₀ (by positivity)
      gcongr
    calc c * ((1 + ‖y 0‖ ^ 2) ^ 2)⁻¹ ≤ |c| * ((1 + ‖y 0‖ ^ 2) ^ 2)⁻¹ := by
          gcongr; exact le_abs_self c
      _ ≤ |c| * (4 * ((1 + ‖y 0‖) ^ 3)⁻¹) := by gcongr
      _ ≤ |c| * (4 * ((1 + ‖y‖) ^ 3)⁻¹) := by gcongr
      _ = 4 * |c| * ((1 + ‖y‖) ^ 3)⁻¹ := by ring
  calc ∫⁻ y : Fin 1 → ℂ, ENNReal.ofReal (c * ((1 + ‖y 0‖ ^ 2) ^ 2)⁻¹)
      ≤ ∫⁻ y : Fin 1 → ℂ, ENNReal.ofReal (4 * |c|) * ENNReal.ofReal ((1 + ‖y‖) ^ (-(3 : ℝ))) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (4 * |c|) * ∫⁻ y : Fin 1 → ℂ, ENNReal.ofReal ((1 + ‖y‖) ^ (-(3 : ℝ))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

def exZdz : Fin (flatAtlas 1).n → (Fin 1 → ℂ) → ℂ := fun _ y => y 0

end ExtInhabitants

open ExtInhabitants

theorem extDelta_hyp : ∃ (X : EmbDatum 1) (Z : ZeroDatum X), 1 ≤ 1 ∧ 2 ≤ 2 ∧ Z.S.Nonempty :=
  ⟨exEmb, exZ, le_rfl, le_rfl, ⟨0, by
    change (0 : Fin 1 → ℂ) ∈ zeroSet (flatAtlas 1) (fun i => lin exE (exC i))
    rw [exZero]; rfl⟩⟩

theorem topSecCompact_hyp : ∃ (F : ℕ → Fin exEmb.A.n → exEmb.U → ℂ) (C : ℝ),
    (∀ n, F n ∈ topSections exEmb.A exEmb.L₂ exEmb.L 2) ∧
    (∀ n, topNormSq exEmb.A (exEmb.wt 2) (F n) ≤ ENNReal.ofReal C) ∧ F 0 ≠ 0 := by
  have hfin : topNormSq exEmb.A (exEmb.wt 2) exOne < ⊤ := by
    change chartIntegral (flatAtlas 1) _ < ⊤
    rw [chartIntegral_flat]
    simp only [exOne, norm_one, one_pow, mul_one]
    simp only [exp_neg_wt]
    simpa using lintegral_inv_one_add_sq_sq_lt_top 2
  refine ⟨fun _ => exOne, (topNormSq exEmb.A (exEmb.wt 2) exOne).toReal,
    fun _ => mem_topSections_flat 2 (fun _ => 1) analyticOnNhd_const,
    fun _ => (ENNReal.ofReal_toReal hfin.ne).ge, fun h => ?_⟩
  have := congr_fun (congr_fun h c0) 0
  simp [exOne] at this

theorem extNonInt_hyp :
    (∀ k, ContinuousOn (exZdz k ∘ (exEmb.A.chart k).symm) (exEmb.A.chart k).target) ∧
    (∀ k l, ∀ x ∈ (exEmb.A.chart k).source ∩ (exEmb.A.chart l).source,
      exZdz k x = jac exEmb.A k l x * exEmb.L₂.g k l x * exEmb.L.g k l x ^ 3 * exZdz l x) ∧
    chartIntegral exEmb.A (fun k y => ENNReal.ofReal (2 ^ 1 * ‖exZdz k y‖ ^ 2 *
      Real.exp (-exEmb.wt 3 k y) * extFactor 1 1 0 (extEv exZ k y))) < ⊤ ∧ exZdz ≠ 0 := by
  refine ⟨fun k => ?_, fun k l x _ => by simp [exZdz, jac_flat, trivLB], ?_, fun h => ?_⟩
  · exact (continuous_apply 0).continuousOn
  · change chartIntegral (flatAtlas 1) _ < ⊤
    rw [chartIntegral_flat]
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) (lintegral_inv_one_add_sq_sq_lt_top 2)
    apply ENNReal.ofReal_le_ofReal
    have hev : extEv exZ c0 y = ‖y 0‖ ^ 2 * (1 + ‖y 0‖ ^ 2)⁻¹ := by
      have hs : ∑ i : Fin 1, ‖exZ.s i c0 y‖ ^ 2 = ‖y 0‖ ^ 2 := by
        simp [ZeroDatum.s, exS_apply]
      have he : fsWeight exE c0 y = Real.log (1 + ‖y 0‖ ^ 2) := by
        simp [fsWeight, exE, Fin.sum_univ_two]
      have hr : rSq exZ.c = 1 := by
        simp [rSq, exC, Fin.sum_univ_two]
      unfold extEv
      rw [hs, he, hr, Real.exp_neg, Real.exp_log (by positivity), div_one]
    have hw : Real.exp (-exEmb.wt 3 c0 y) = ((1 + ‖y 0‖ ^ 2) ^ 3)⁻¹ := exp_neg_wt 3 y
    have ha0 : 0 ≤ ‖y 0‖ ^ 2 := by positivity
    simp only [exZdz, hw, hev]
    unfold extFactor
    rw [zero_pow two_ne_zero, add_zero, pow_one]
    generalize ‖y 0‖ ^ 2 = a at ha0 ⊢
    rcases ha0.lt_or_eq with hapos | ha0'
    · have hden : 1 ≤ extDen 1 (a * (1 + a)⁻¹) := by
        have ht1 : a * (1 + a)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one (by positivity)]; linarith
        have hx : 1 ≤ extX 1 (a * (1 + a)⁻¹) := by
          unfold extX
          have : Real.log (a * (1 + a)⁻¹ + 1 ^ 2) ≤ Real.log (1 + 1 ^ 2) :=
            Real.log_le_log (by positivity) (by linarith)
          linarith
        unfold extDen curvEta
        have := Real.log_nonneg hx
        nlinarith
      have hne : (1 + a) ≠ 0 := by positivity
      calc _ = 2 * ((1 + a) ^ 2)⁻¹ / extDen 1 (a * (1 + a)⁻¹) := by field_simp
        _ ≤ _ := div_le_self (by positivity) hden
    · rw [← ha0']
      simp
  · have := congr_fun (congr_fun h c0) (fun _ => 1)
    simp [exZdz] at this

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtBergman
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def BergmanProj.Statement : Prop :=
  ∀ (D : ℕ) (U : Type) [TopologicalSpace U] [T2Space U] (A : FinHolAtlas D U)
    (L₂ L : HolLineBundle A) (m : ℕ) (ψ : Fin A.n → U → ℝ) (F₀ : Fin A.n → U → ℂ),
    (∀ k, ContinuousOn (ψ k ∘ (A.chart k).symm) (A.chart k).target) →
    (∀ k l, ∀ x ∈ (A.chart k).source ∩ (A.chart l).source,
      ψ k x = ψ l x + Real.log (‖L₂.g k l x * L.g k l x ^ m‖ ^ 2)) →
    (∀ k, ContinuousOn (F₀ k ∘ (A.chart k).symm) (A.chart k).target) →
    (∀ k l, ∀ x ∈ (A.chart k).source ∩ (A.chart l).source,
      F₀ k x = jac A k l x * L₂.g k l x * L.g k l x ^ m * F₀ l x) →
    topNormSq A ψ F₀ < ⊤ →
    ∃ F ∈ topSections A L₂ L m, topNormSq A ψ F < ⊤ ∧
      ∀ G ∈ topSections A L₂ L m, topNormSq A ψ G < ⊤ → chartInner A ψ (F₀ - F) G = 0

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtCutoff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def ExtCutoff.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (j : ℕ), 1 ≤ D → 2 ≤ j →
    ∀ (g : X.U → ℂ) (θ : ℝ), 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ (F₀ : Fin X.A.n → X.U → ℂ) (G : Fin X.A.n → X.U → ℝ),
        (∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F₀ k ∘ (X.A.chart k).symm)
          (X.A.chart k).target) ∧
        (∀ k l, ∀ x ∈ (X.A.chart k).source ∩ (X.A.chart l).source,
          F₀ k x = jac X.A k l x * X.L₂.g k l x * X.L.g k l x ^ (D + j) * F₀ l x) ∧
        (∀ k, ∀ x ∉ (X.A.chart k).source, F₀ k x = 0) ∧
        (∀ x ∈ Z.S, res X.A Z.s F₀ x = g x) ∧
        topNormSq X.A (X.wt (D + j)) F₀ ≤ ENNReal.ofReal θ ∧
        (∀ k, ContinuousOn (G k ∘ (X.A.chart k).symm) (X.A.chart k).target) ∧
        (∀ k y, 0 ≤ G k y) ∧
        (∀ k, ∀ y ∈ (X.A.chart k).target, ∀ ξ : Fin D → ℂ,
          ‖dbarPair (F₀ k ∘ (X.A.chart k).symm) y ξ‖ ^ 2 ≤
            9 * extShell ε (extEv Z k ((X.A.chart k).symm y)) * G k ((X.A.chart k).symm y) *
              ‖dbarPair (fun z => (extEv Z k ((X.A.chart k).symm z) : ℂ)) y ξ‖ ^ 2 / ε ^ 4) ∧
        72 * chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D * G k y *
            Real.exp (-X.wt (D + j) k y) * (extEv Z k y ^ D)⁻¹ * extShell ε (extEv Z k y))) ≤
          ENNReal.ofReal (36 * Real.log 2 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g + θ)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtShell
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def ExtShell.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (m : ℕ), 1 ≤ D →
    ∀ (g : X.U → ℂ) (W : Set X.U) (gt : Fin X.A.n → X.U → ℂ), IsOpen W → Z.S ⊆ W →
      (∀ k, ContinuousOn (gt k ∘ (X.A.chart k).symm)
        ((X.A.chart k).target ∩ (X.A.chart k).symm ⁻¹' W)) →
      (∀ k l, ∀ x ∈ (X.A.chart k).source ∩ (X.A.chart l).source ∩ W,
        gt k x = jac X.A k l x * X.L₂.g k l x * X.L.g k l x ^ (D + m) * gt l x) →
      (∀ x ∈ Z.S, gt (chartIdx X.A x) x = g x * sJac X.A Z.s (chartIdx X.A x) x) →
      Tendsto (fun ε : ℝ => chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D * ‖gt k y‖ ^ 2 *
          Real.exp (-X.wt (D + m) k y) * (extEv Z k y ^ D)⁻¹ * extShell ε (extEv Z k y))))
        (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (Real.log 2 / 2 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt m) g)))

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtTwist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def ExtTwist.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (j : ℕ), 1 ≤ D → 2 ≤ j →
    ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      (∀ k, X.A.SmoothOn (X.A.chart k).source (fun y => extPsi Z j δ k y + extPhi Z ε k y)) ∧
      (∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extPhi Z ε k ∘ (X.A.chart k).symm)
        (X.A.chart k).target) ∧
      (∀ k l, ∀ x ∈ (X.A.chart k).source ∩ (X.A.chart l).source,
        extPsi Z j δ k x = extPsi Z j δ l x + Real.log (‖X.L₂.g k l x * X.L.g k l x ^ (D + j)‖ ^ 2) ∧
          extPhi Z ε k x = extPhi Z ε l x) ∧
      (∀ k, ∀ y ∈ (X.A.chart k).target, ∀ ξ : Fin D → ℂ,
        extTheta ε (extEv Z k ((X.A.chart k).symm y)) * extOmega Z ε k y ξ ≤
          levi ((fun x => extPsi Z j δ k x + extPhi Z ε k x) ∘ (X.A.chart k).symm) y ξ) ∧
      (∀ k, ∀ y ∈ (X.A.chart k).target, ∀ ξ : Fin D → ℂ,
        ‖dbarPair (fun z => (extPhi Z ε k ((X.A.chart k).symm z) : ℂ)) y ξ‖ ^ 2 =
          (curvK (extX ε (extEv Z k ((X.A.chart k).symm y))) /
            curvEta (extX ε (extEv Z k ((X.A.chart k).symm y)))) ^ 2 * extOmega Z ε k y ξ)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

