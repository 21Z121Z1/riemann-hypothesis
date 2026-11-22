import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncTransfer
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Monotone
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Metric Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier polyMax molli mollify_thm polyMax_le' polyMax_mono' le_polyMax
  limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.Regular

noncomputable section

def regularisedAt {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
    (R : RegChartData A) (ρ : Mollifier D) (η : Fin R.N → X → ℝ) (κ E t : ℝ) : X → ℝ :=
  R.regularised ρ (κ * Real.log (Real.log t⁻¹)) t
    (E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹ + t)) η

def RegularisedMonotone.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D) (η : Fin R.N → X → ℝ) (Cη κ E : ℝ),
    R.IsCutoffFamily η Cη → 0 ≤ κ → 0 ≤ E →
    ∃ C ℓ₀ : ℝ, ∀ t t₀ : ℝ, 0 < t → t ≤ t₀ → ℓ₀ ≤ Real.log t₀⁻¹ → ∀ x : X,
      regularisedAt R ρ η κ E t x ≤
        regularisedAt R ρ η κ E t₀ x + C * (Real.log (Real.log t₀⁻¹) / Real.log t₀⁻¹)

theorem regularisedMonotone_hyp : CompactSpace Unit ∧ T2Space Unit ∧ Nonempty (Mollifier 0) ∧
    pointReg.IsCutoffFamily (fun _ _ => 0) 1 :=
  ⟨inferInstance, inferInstance, ReciprocityTheory.AnForm.A.mollifierInhabit_thm 0, pointCutoff⟩

theorem le_logLog_div {t ℓ : ℝ} (ht : 0 < t) (hℓdef : ℓ = Real.log t⁻¹) (hℓe : Real.exp 1 ≤ ℓ) :
    t ≤ Real.log ℓ / ℓ := by
  have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le hℓe
  have hlog1 : 1 ≤ Real.log ℓ := by rw [Real.le_log_iff_exp_le hℓ0]; exact hℓe
  have hlogt : Real.log t = -ℓ := by rw [hℓdef, Real.log_inv, neg_neg]
  have htexp : t = Real.exp (-ℓ) := by rw [← hlogt, Real.exp_log ht]
  rw [htexp, Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos ℓ)]
  have h5 : ℓ + 1 ≤ Real.exp ℓ := Real.add_one_le_exp ℓ
  have h6 : 1 ≤ Real.exp ℓ * (Real.log ℓ / ℓ) := by
    rw [mul_div_assoc', le_div_iff₀ hℓ0, one_mul]
    have := le_mul_of_one_le_right (Real.exp_pos ℓ).le hlog1
    linarith
  rw [mul_comm]; exact h6

theorem RegularisedMonotone.proof : RegularisedMonotone.Statement := by
  intro X _ _ _ D A R ρ η Cη κ E hη hκ hE
  obtain ⟨δ, B₀, hδ, hV⟩ := TruncPsh.proof X D A R
  choose V hVo hVt hVball hVpsh using hV
  obtain ⟨C₂, t₂, ht₂, hlow⟩ := PolyMaxLowerBound.proof X D A R
  obtain ⟨b, hb⟩ := mollifier_exists_bound ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  obtain ⟨B', hB'⟩ : ∃ c : ℝ, c = max B₀ 0 := ⟨_, rfl⟩
  obtain ⟨C₂', hC₂'⟩ : ∃ c : ℝ, c = max C₂ 0 := ⟨_, rfl⟩
  have hB'0 : 0 ≤ B' := hB' ▸ le_max_right _ _
  have hB₀B' : B₀ ≤ B' := hB' ▸ le_max_left _ _
  have hC₂'0 : 0 ≤ C₂' := hC₂' ▸ le_max_right _ _
  have hC₂C₂' : C₂ ≤ C₂' := hC₂' ▸ le_max_left _ _
  obtain ⟨a, ha⟩ : ∃ c : ℝ, c = |Real.log (δ / 2)| := ⟨_, rfl⟩
  have hL16 : 0 ≤ Real.log (4 * 2 ^ 2 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨E₁, hE₁⟩ : ∃ c : ℝ, c = 2 * Real.log (4 * 2 ^ 2 : ℝ) * (B' + C₂') := ⟨_, rfl⟩
  have hE₁0 : 0 ≤ E₁ := by rw [hE₁]; positivity
  refine ⟨10 * E + c₀ * E₁,
    max (max (Real.exp 1) (2 * a)) (max (-Real.log t₂) (-Real.log (δ / 2))) + 1,
    fun t t₀ ht htt₀ hℓ x => ?_⟩
  have ht₀ : 0 < t₀ := ht.trans_le htt₀
  obtain ⟨ℓ, hℓdef⟩ : ∃ s : ℝ, s = Real.log t₀⁻¹ := ⟨_, rfl⟩
  obtain ⟨ℓt, hℓtdef⟩ : ∃ s : ℝ, s = Real.log t⁻¹ := ⟨_, rfl⟩
  rw [← hℓdef] at hℓ
  have h1 := le_max_left (Real.exp 1) (2 * a)
  have h2 := le_max_right (Real.exp 1) (2 * a)
  have h3 := le_max_left (-Real.log t₂) (-Real.log (δ / 2))
  have h4 := le_max_right (-Real.log t₂) (-Real.log (δ / 2))
  have h5 := le_max_left (max (Real.exp 1) (2 * a)) (max (-Real.log t₂) (-Real.log (δ / 2)))
  have h6 := le_max_right (max (Real.exp 1) (2 * a)) (max (-Real.log t₂) (-Real.log (δ / 2)))
  have hℓe : Real.exp 1 ≤ ℓ := by linarith
  have hℓa : 2 * a ≤ ℓ := by linarith
  have hlogt₀ : Real.log t₀ = -ℓ := by rw [hℓdef, Real.log_inv, neg_neg]
  have htt₂ : t₀ < t₂ := (Real.log_lt_log_iff ht₀ ht₂).1 (by linarith)
  have htδ : t₀ < δ / 2 := (Real.log_lt_log_iff ht₀ (by linarith)).1 (by linarith)
  have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le hℓe
  have hlog1 : 1 ≤ Real.log ℓ := by rw [Real.le_log_iff_exp_le hℓ0]; exact hℓe
  obtain ⟨q, hqdef⟩ : ∃ s : ℝ, s = Real.log ℓ / ℓ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hqdef]; exact div_nonneg (by linarith) hℓ0.le
  have htq : t₀ ≤ q := hqdef ▸ le_logLog_div ht₀ hℓdef hℓe
  have hqℓ : q * ℓ = Real.log ℓ := by rw [hqdef]; field_simp

  have hℓℓt : ℓ ≤ ℓt := by
    rw [hℓdef, hℓtdef]; exact Real.log_le_log (inv_pos.2 ht₀) (inv_anti₀ ht htt₀)
  have hqt : Real.log ℓt / ℓt ≤ q := by
    have h := Real.log_div_self_antitoneOn (Set.mem_Ici.2 hℓe) (Set.mem_Ici.2 (hℓe.trans hℓℓt))
      hℓℓt
    simp only at h
    rw [hqdef]; exact h
  have hlogℓt : Real.log ℓ ≤ Real.log ℓt := Real.log_le_log hℓ0 hℓℓt
  have hKK : κ * Real.log ℓ ≤ κ * Real.log ℓt := mul_le_mul_of_nonneg_left hlogℓt hκ
  have hK0 : 0 ≤ κ * Real.log ℓ := mul_nonneg hκ (by linarith)
  have hqt0 : 0 ≤ Real.log ℓt / ℓt := div_nonneg (by linarith) (by linarith)
  have hεt0 : 0 ≤ E * (Real.log ℓt / ℓt + t) := mul_nonneg hE (by linarith)
  have hε0 : 0 ≤ E * (q + t₀) := mul_nonneg hE (by linarith)
  have hεle : E * (Real.log ℓt / ℓt + t) ≤ E * (q + t₀) :=
    mul_le_mul_of_nonneg_left (by linarith) hE
  have hε2 : E * (q + t₀) ≤ 2 * E * q := by
    have := mul_le_mul_of_nonneg_left htq hE
    linarith

  have key : ∀ j, x ∈ R.mid j → R.phReg ρ (κ * Real.log ℓt) t j x ≤
      R.phReg ρ (κ * Real.log ℓ) t₀ j x + c₀ * E₁ * q := by
    intro j hx
    obtain ⟨hp₀, hbd₀⟩ := hVpsh j (κ * Real.log ℓ)
    have hball : ∀ s, s ≤ δ → closedBall (R.chart j x) s ⊆ V j := fun s hs =>
      (closedBall_subset_closedBall hs).trans (hVball j x hx)
    have h2t : 2 * t₀ ≤ δ := by linarith

    have hpt := (hVpsh j (κ * Real.log ℓt)).1
    have hi : molli ρ t (R.trunc (κ * Real.log ℓt) j) (R.chart j x) ≤
        polyMax (R.trunc (κ * Real.log ℓt) j) (R.chart j x) t :=
      (((mollify_thm D ρ (V j) _ (hVo j) hpt).1 t ht).2.2.2 (R.chart j x)
        (hball t (by linarith))).2
    have hii : polyMax (R.trunc (κ * Real.log ℓt) j) (R.chart j x) t ≤
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀) := by
      refine polyMax_le' ht.le fun y hy => ?_
      have hyV : y ∈ V j := hball t (by linarith) hy
      exact TruncTransfer.limsupExt_max_le (R.chart j).open_target (R.S j) (R.u j) _ _ t₀
        (hVt j hyV) ht₀ fun y' hy' _ hy'S => by
          have hy'b : y' ∈ closedBall (R.chart j x) (2 * t₀) := by
            rw [mem_closedBall]; rw [mem_ball] at hy'; rw [mem_closedBall] at hy
            linarith [dist_triangle y' y (R.chart j x)]
          have e : R.trunc (κ * Real.log ℓ) j y' = max (R.u j y') (-(κ * Real.log ℓ)) := by
            simp only [RegChartData.trunc, limsupExt, if_neg hy'S]
          calc max (R.u j y') (-(κ * Real.log ℓt)) ≤ max (R.u j y') (-(κ * Real.log ℓ)) :=
                max_le_max le_rfl (neg_le_neg hKK)
            _ = R.trunc (κ * Real.log ℓ) j y' := e.symm
            _ ≤ _ := le_polyMax hp₀.1 (hball _ h2t) hy'b

    have hiv := MollifiedLowerBound.full D ρ b (V j) (R.trunc (κ * Real.log ℓ) j) (R.chart j x) t₀
      (hVo j) hp₀ ht₀ (hball _ h2t) hb
    rw [← hc₀] at hiv
    have hv := PolyMaxOscillation.full D (V j) (R.trunc (κ * Real.log ℓ) j) (R.chart j x) δ t₀ 2
      (hVo j) hp₀ (hball δ le_rfl) ht₀ (by norm_num) (by linarith)
    have mono : ∀ s s', 0 ≤ s → s ≤ s' → s' ≤ δ →
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) s ≤
          polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) s' :=
      fun s s' hs hss' hs' => polyMax_mono' hp₀.1 hs hss' (hball _ hs')
    have e1 := mono (t₀ / (4 * 2)) (t₀ / 4) (by linarith) (by linarith) (by linarith)
    have e2 := mono t₀ (2 * t₀) ht₀.le (by linarith) h2t
    have hlowj := hlow t₀ ht₀ htt₂ (κ * Real.log ℓ) j x hx
    rw [← hℓdef] at hlowj
    have hMδ : polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) δ ≤ B' :=
      polyMax_le' hδ.le fun y hy => (hbd₀ y (hVball j x hx hy)).trans
        (max_le hB₀B' (by linarith))
    have hN : polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) δ -
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀) ≤ (B' + C₂') * Real.log ℓ := by
      have h1' : C₂ * Real.log ℓ ≤ C₂' * Real.log ℓ :=
        mul_le_mul_of_nonneg_right hC₂C₂' (by linarith)
      have h2' : B' ≤ B' * Real.log ℓ := le_mul_of_one_le_right hB'0 hlog1
      linarith
    have hden : ℓ / 2 ≤ Real.log (δ / (2 * t₀)) := by
      rw [show δ / (2 * t₀) = (δ / 2) * t₀⁻¹ by field_simp,
        Real.log_mul (by linarith : (0 : ℝ) < δ / 2).ne' (inv_pos.2 ht₀).ne']
      have := neg_abs_le (Real.log (δ / 2))
      rw [← ha] at this
      linarith
    have hden0 : 0 < Real.log (δ / (2 * t₀)) := by linarith
    have hO : polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀) -
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (t₀ / (4 * 2)) ≤ E₁ * q := by
      refine hv.trans ?_
      rw [div_le_iff₀ hden0]
      calc Real.log (4 * 2 ^ 2) * (polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) δ -
              polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀))
          ≤ Real.log (4 * 2 ^ 2) * ((B' + C₂') * Real.log ℓ) :=
            mul_le_mul_of_nonneg_left hN hL16
        _ = E₁ * q * (ℓ / 2) := by rw [hE₁, ← hqℓ]; ring
        _ ≤ E₁ * q * Real.log (δ / (2 * t₀)) :=
            mul_le_mul_of_nonneg_left hden (mul_nonneg hE₁0 hq0)
    have hc : c₀ * (polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀) -
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (t₀ / 4)) ≤ c₀ * (E₁ * q) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₀0
    simp only [RegChartData.phReg, RegChartData.smoothed]
    linarith

  have hg := LogLogRegularisation.glue_le R.toPotentialCharts
    (fun j x => R.phReg ρ (κ * Real.log ℓt) t j x + 4 * (E * (Real.log ℓt / ℓt + t)) * η j x)
    hεt0 (c := regularisedAt R ρ η κ E t₀ x + 4 * (E * (q + t₀)) + c₀ * E₁ * q) (x := x)
    fun j hx => by
      have hb' := hη.bounds j x hx
      have hlo := LogLogRegularisation.le_glue R.toPotentialCharts
        (fun j x => R.phReg ρ (κ * Real.log ℓ) t₀ j x + 4 * (E * (q + t₀)) * η j x) hε0 hx
      have e : R.toPotentialCharts.glue
          (fun j x => R.phReg ρ (κ * Real.log ℓ) t₀ j x + 4 * (E * (q + t₀)) * η j x)
          (E * (q + t₀)) x = regularisedAt R ρ η κ E t₀ x := by
        simp only [regularisedAt, ← hℓdef, ← hqdef]; rfl
      rw [e] at hlo
      have hk := key j hx
      have m1 : 4 * (E * (Real.log ℓt / ℓt + t)) * η j x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hb'.2
      have m2 : 0 ≤ 4 * (E * (q + t₀)) * (η j x + 1) := mul_nonneg (by linarith) (by linarith)
      linarith
  have e : R.toPotentialCharts.glue
      (fun j x => R.phReg ρ (κ * Real.log ℓt) t j x + 4 * (E * (Real.log ℓt / ℓt + t)) * η j x)
      (E * (Real.log ℓt / ℓt + t)) x = regularisedAt R ρ η κ E t x := by
    simp only [regularisedAt, ← hℓtdef]; rfl
  rw [e] at hg
  rw [← hℓdef, ← hqdef]
  linarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdCocycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem BdCocycle.proof (hDense : RegYoDense.Statement) (hHolo : BdEqHolo.Statement) :
    BdCocycle.Statement := by
  intro X _ D A R g hg hEq j k l
  have hOopen : IsOpen (bdDom R j ∩ bdDom R k ∩ bdDom R l) :=
    ((isOpen_bdDom R j).inter (isOpen_bdDom R k)).inter (isOpen_bdDom R l)
  have hOjl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R l := fun _ hy => ⟨hy.1.1, hy.2⟩
  have hOjk : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R k := fun _ hy => hy.1
  have hOkl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R k ∩ bdDom R l := fun _ hy => ⟨hy.1.2, hy.2⟩
  have hYo : Set.EqOn (g j l) (fun y => g j k y * g k l y)
      ((bdDom R j ∩ bdDom R k ∩ bdDom R l) ∩ R.Yo) := by
    rintro y ⟨hyO, hyY⟩
    have hne : bdEq R l y ≠ 0 := fun h0 => ((hHolo D A R l).2 y hyO.2).1 h0 hyY
    have h1 := hEq j l y (hOjl hyO)
    have h2 := hEq j k y (hOjk hyO)
    have h3 := hEq k l y (hOkl hyO)
    apply mul_right_cancel₀ hne
    show g j l y * bdEq R l y = g j k y * g k l y * bdEq R l y
    rw [← h1, h2, h3, mul_assoc]
  have hall := hYo.of_subset_closure ((hg j l).mono hOjl)
    (((hg j k).mono hOjk).mul ((hg k l).mono hOkl)) Set.inter_subset_left
    ((hDense D A R).open_subset_closure_inter hOopen)
  intro y hy
  exact hall hy

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdComparison
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot logNormSec)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem BdComparison.proof (hCC : ChartCont.Statement) (hBI : BddOnInner.Statement) :
    BdComparison.Statement := by
  intro X _ D A R φ hφ c
  have hp : ∀ j, ∃ B : ℝ, ∀ y ∈ R.V'' j, |φ j y| ≤ B := fun j =>
    hBI D A R j (φ j) ((hCC D A (bdDom R j) (isOpen_bdDom R j)).1 _ (hφ.1 j))
  choose Bf hBf using R.f_bdd
  choose Bp hBp using hp
  refine ⟨∑ j, (|Bf j| + 2 * |Bp j|) + 2 * |c|, fun y hy => ?_⟩
  have hV := mem_V''_bdIdx R y
  have hdom := V''_subset_bdDom R _ hV
  set j := bdIdx R y with hj
  have hW : R.ψ j y ∈ R.W j := hdom.2
  have hsymm : (R.ψ j).symm (R.ψ j y) = y := (R.ψ j).left_inv hV.1
  have hnd : R.ψ j y ∉ coordDiv (R.S j) := by
    rw [← R.mem_Yo_iff j _ hW, hsymm]; exact hy
  have hz : ∀ i ∈ R.S j, R.ψ j y i ≠ 0 := fun i hi h => hnd ⟨i, hi, h⟩
  have hr := R.r_chart j (R.ψ j y) ⟨hW, hnd⟩
  rw [hsymm] at hr
  have hs : rSec (bdPot R φ c) (bdSec R) y =
      Real.exp 1 - ∑ i ∈ R.S j, Real.log (‖R.ψ j y i‖ ^ 2) + 2 * (φ j y + c) := by
    have hprod : ‖∏ i ∈ R.S j, R.ψ j y i‖ ≠ 0 :=
      norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 hz)
    simp only [rSec, logNormSec, bdPot, bdSec, bdEq, ← hj]
    rw [Real.log_mul hprod (Real.exp_pos _).ne', Real.log_exp, norm_prod,
      Real.log_prod (fun i hi => norm_ne_zero_iff.2 (hz i hi))]
    simp only [Real.log_pow, Nat.cast_ofNat, ← Finset.mul_sum]
    ring
  rw [hr, hs]
  have e : Real.exp 1 + R.f j (R.ψ j y) - ∑ i ∈ R.S j, Real.log (‖R.ψ j y i‖ ^ 2) -
      (Real.exp 1 - ∑ i ∈ R.S j, Real.log (‖R.ψ j y i‖ ^ 2) + 2 * (φ j y + c)) =
      R.f j (R.ψ j y) + (-2) * φ j y + (-2) * c := by ring
  rw [e]
  have h1 : |R.f j (R.ψ j y)| ≤ |Bf j| := (hBf j _ hW).trans (le_abs_self _)
  have h2 : |φ j y| ≤ |Bp j| := (hBp j y hV).trans (le_abs_self _)
  have h3 : |Bf j| + 2 * |Bp j| ≤ ∑ k, (|Bf k| + 2 * |Bp k|) :=
    Finset.single_le_sum (f := fun k => |Bf k| + 2 * |Bp k|)
      (fun k _ => by positivity) (Finset.mem_univ j)
  calc |R.f j (R.ψ j y) + (-2) * φ j y + (-2) * c|
      ≤ |R.f j (R.ψ j y)| + |(-2) * φ j y| + |(-2) * c| := abs_add_three _ _ _
    _ = |R.f j (R.ψ j y)| + 2 * |φ j y| + 2 * |c| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ ∑ k, (|Bf k| + 2 * |Bp k|) + 2 * |c| := by linarith

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdDivides
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts)

theorem BdDivides.proof (hdiv : CoordDivDivisible.Statement) : BdDivides.Statement := by
  intro X _ D A R j k
  set Ω : Set (Fin D → ℂ) := (R.ψ j).target ∩ (R.ψ j).symm ⁻¹' (bdDom R j ∩ bdDom R k) with hΩdef
  have hΩ : IsOpen Ω :=
    (R.ψ j).isOpen_inter_preimage_symm ((isOpen_bdDom R j).inter (isOpen_bdDom R k))
  set F : (Fin D → ℂ) → ℂ := fun z => ∏ i ∈ R.S k, R.ψ k ((R.ψ j).symm z) i with hFdef
  have hF : AnalyticOnNhd ℂ F Ω := by
    intro z hz
    have ht : AnalyticAt ℂ (R.ψ k ∘ (R.ψ j).symm) z :=
      ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.compat_trans A (R.compat j) (R.compat k) hz.1 hz.2.2.1
    exact Finset.analyticAt_fun_prod (f := fun i z => R.ψ k ((R.ψ j).symm z) i) _
      fun i _ => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt _ |>.comp ht
  have hvan : ∀ z ∈ Ω, z ∈ coordDiv (R.S j) → F z = 0 := by
    intro z hz hzS
    obtain ⟨hzt, ⟨_, hzW⟩, ⟨hyk, hykW⟩⟩ := hz
    have hjz : R.ψ j ((R.ψ j).symm z) = z := (R.ψ j).right_inv hzt
    rw [Set.mem_preimage, hjz] at hzW
    have hnot : (R.ψ j).symm z ∉ R.Yo := fun h => ((R.mem_Yo_iff j z hzW).1 h) hzS
    have hk : R.ψ k ((R.ψ j).symm z) ∈ coordDiv (R.S k) := by
      by_contra hc
      apply hnot
      have := (R.mem_Yo_iff k _ hykW).2 hc
      rwa [(R.ψ k).left_inv hyk] at this
    obtain ⟨i, hi, h0⟩ := hk
    exact Finset.prod_eq_zero hi h0
  obtain ⟨G, hG, hFG⟩ := hdiv D Ω F (R.S j) hΩ hF hvan
  have hmem : ∀ y ∈ bdDom R j ∩ bdDom R k, R.ψ j y ∈ Ω := fun y hy =>
    ⟨(R.ψ j).map_source hy.1.1, by
      show (R.ψ j).symm (R.ψ j y) ∈ bdDom R j ∩ bdDom R k
      rw [(R.ψ j).left_inv hy.1.1]; exact hy⟩
  refine ⟨fun y => G (R.ψ j y), ?_, ?_, ?_⟩
  · intro m w hw
    have hx : (A.chart m).symm w ∈ bdDom R j ∩ bdDom R k := hw.2
    have hc : AnalyticAt ℂ (R.ψ j ∘ (A.chart m).symm) w := ((R.compat j) m).1 w ⟨hw.1, hx.1.1⟩
    exact (hG _ (hmem _ hx)).comp (f := R.ψ j ∘ (A.chart m).symm) hc
  · exact hG.continuousOn.comp ((R.ψ j).continuousOn.mono fun y hy => hy.1.1) hmem
  · intro y hy
    have h := hFG _ (hmem y hy)
    simp only [hFdef, (R.ψ j).left_inv hy.1.1] at h
    simp only [bdEq]
    rw [h, mul_comm]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdEqHolo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem BdEqHolo.proof : BdEqHolo.Statement := by
  intro X _ D A R j
  refine ⟨fun m v hv => ?_, fun y hy => ?_⟩
  · have h : AnalyticAt ℂ (R.ψ j ∘ (A.chart m).symm) v := (R.compat j m).1 v ⟨hv.1, hv.2.1⟩
    have hi : ∀ i, AnalyticAt ℂ (fun w => (R.ψ j ∘ (A.chart m).symm) w i) v :=
      (analyticAt_pi_iff (f := fun i w => (R.ψ j ∘ (A.chart m).symm) w i)).1 h
    show AnalyticAt ℂ (fun w => ∏ i ∈ R.S j, (R.ψ j ∘ (A.chart m).symm) w i) v
    exact Finset.analyticAt_fun_prod _ fun i _ => hi i
  · have hmem := R.mem_Yo_iff j (R.ψ j y) hy.2
    rw [(R.ψ j).left_inv hy.1] at hmem
    rw [hmem, not_not]
    simp only [bdEq, Finset.prod_eq_zero_iff, coordDiv, Set.mem_ofPred_eq]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdMetric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

noncomputable section

theorem BdMetric.proof (hCC : ChartCont.Statement) (hT : BdTransition.Statement)
    (hC : BdCocycle.Statement) (hL : LogNormHolo.Statement) (hW : BdWeight.Statement) :
    BdMetric.Statement := by
  intro X _ _ _ D A R
  choose g hgH hg using fun j k => hT D A R j k
  have hO : ∀ j k, IsOpen (bdDom R j ∩ bdDom R k) := fun j k =>
    (isOpen_bdDom R j).inter (isOpen_bdDom R k)
  have hgC : ∀ j k, ContinuousOn (g j k) (bdDom R j ∩ bdDom R k) := fun j k =>
    (hCC D A _ (hO j k)).2 _ (hgH j k)
  have hcoc := hC D A R g hgC fun j k y hy => (hg j k y hy).2
  obtain ⟨w, hwS, hwP, hwE⟩ := hW D A R g hgH (fun j k y hy => (hg j k y hy).1) hcoc

  have hd : ∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k,
      Real.log (w j y) / 2 = Real.log ‖g j k y‖ + Real.log (w k y) / 2 := by
    intro j k y hy
    have hg0 : ‖g j k y‖ ≠ 0 := norm_ne_zero_iff.mpr (hg j k y hy).1
    rw [hwE j k y hy, Real.log_mul (pow_ne_zero 2 hg0) (hwP k y hy.2).ne', Real.log_pow]
    push_cast
    ring
  refine ⟨fun j y => Real.log (w j y) / 2, fun j i => ?_, fun j k y hy => ?_, fun j k y hy => ?_⟩
  · exact ((hwS j i).log fun z hz => (hwP j _ hz.2).ne').div_const 2
  · obtain ⟨V, hV, hyV, hVW, G, hG, hGe⟩ :=
      hL D A _ (g j k) (hO j k) (hgH j k) (fun z hz => (hg j k z hz).1) y hy
    refine ⟨V, hV, hyV, G, hG, fun z hz => ?_⟩
    show Real.log (w j z) / 2 - Real.log (w k z) / 2 = (G z).re
    rw [hd j k z hz.2, ← hGe z hz.1]
    ring
  · have hgp : 0 < ‖g j k y‖ := norm_pos_iff.mpr (hg j k y hy).1
    simp only
    rw [hd j k y hy, (hg j k y hy).2, norm_mul, neg_add, Real.exp_add, Real.exp_neg (Real.log _),
      Real.exp_log hgp]
    field_simp

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdNormCont
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem BdNormCont.proof (hCC : ChartCont.Statement) (hEq : BdEqHolo.Statement) :
    BdNormCont.Statement := by
  intro X _ D A R φ hφ c
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  set j := bdIdx R y₀
  have hU : IsOpen (bdDom R j) := isOpen_bdDom R j
  have hy₀ : y₀ ∈ bdDom R j := mem_bdDom_bdIdx R y₀
  have hEqc : ContinuousOn (bdEq R j) (bdDom R j) := (hCC D A _ hU).2 _ (hEq D A R j).1
  have hφc : ContinuousOn (φ j) (bdDom R j) := (hCC D A _ hU).1 _ (hφ.1 j)
  have hg : ContinuousOn (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) (bdDom R j) :=
    hEqc.norm.mul ((hφc.add continuousOn_const).neg.rexp)
  have hgy : ContinuousAt (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) y₀ :=
    hg.continuousAt (hU.mem_nhds hy₀)
  refine hgy.congr ?_
  filter_upwards [hU.mem_nhds hy₀] with y hy
  have hk : y ∈ bdDom R (bdIdx R y) ∩ bdDom R j := ⟨mem_bdDom_bdIdx R y, hy⟩
  have h3 := hφ.2.2 (bdIdx R y) j y hk
  show ‖bdEq R j y‖ * Real.exp (-(φ j y + c)) = ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y)
  simp only [bdSec, bdPot]
  simp only [neg_add, Real.exp_add, ← mul_assoc, h3]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdSectionProps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)

theorem BdSectionProps.proof (hB : BdEqHolo.Statement) : BdSectionProps.Statement := by
  intro X _ D A R φ hφ c
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨⟨fun x j => ?_, fun x x' y hy => ?_⟩, ⟨fun x => (hB D A R _).1, fun x x' y hy => ?_⟩, ?_⟩
  · exact (h1 (bdIdx R x) j).add contDiffOn_const
  · obtain ⟨W, hW, hyW, G, hG, hGe⟩ := h2 (bdIdx R x) (bdIdx R x') y hy
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    have h := hGe z ⟨hz.1.1, hz.1.2, hz.2⟩
    show (φ (bdIdx R x) z + c) - (φ (bdIdx R x') z + c) = (G z).re
    linarith
  · show ‖bdEq R (bdIdx R x) y‖ * Real.exp (-(φ (bdIdx R x) y + c)) =
      ‖bdEq R (bdIdx R x') y‖ * Real.exp (-(φ (bdIdx R x') y + c))
    simp only [neg_add, Real.exp_add, ← mul_assoc]
    rw [h3 _ _ y hy]
  · ext y
    have h := (hB D A R (bdIdx R y)).2 y (mem_bdDom_bdIdx R y)
    show bdEq R (bdIdx R y) y ≠ 0 ↔ y ∈ R.Yo
    rw [Ne, h, not_not]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

