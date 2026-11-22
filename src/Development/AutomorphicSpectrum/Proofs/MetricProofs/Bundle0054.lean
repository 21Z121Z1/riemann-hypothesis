import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0044
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0045
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBlockMetricOffBoundary
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem valAt_inv {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (h0 : s ≠ 0)
    (hs : RegAt x (mCoordIdeal z) s) (hs' : RegAt x (mCoordIdeal z) s⁻¹) :
    valAt x s⁻¹ z = (valAt x s z)⁻¹ ∧ valAt x s z ≠ 0 := by
  obtain ⟨-, -, -, h1, hm⟩ := ValRing.regAt_valAt_ring K ι Ω x z hz
  have h := (hm s s⁻¹ hs hs').2.2.1
  rw [mul_inv_cancel₀ h0, h1] at h
  have hne : valAt x s z ≠ 0 := left_ne_zero_of_mul_eq_one h.symm
  exact ⟨eq_inv_of_mul_eq_one_right h.symm, hne⟩

theorem coord_ne_zero {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 :=
  fun h0 => h (by
    show mConeMap z (X q) = 0
    rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

end Values

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = none → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) 1 + Real.log ‖baseMono M (BM.F l) p z * valAt M.x ((BM.F l).υ p)⁻¹ (basePart M.blk z)‖ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p l x₀ z hp hx hz hso
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (BM.Rb.lift x₀ x₀)) := BM.good l x₀ hx.1
  have hxb : BM.Rb.lift x₀ x₀ ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem x₀ x₀ (BM.Rb.mem_U x₀)
  obtain ⟨c, hc, hzc⟩ := id hso

  have hI : mCoordIdeal (basePart M.blk z) = mCoordIdeal (BM.Rb.lift x₀ x₀) := by
    rw [hzc]; exact TorusAct.mCoordIdeal_torus c hc _
  have hzb : basePart M.blk z ∈ mcPts (mCoordIdeal M.x) := by
    rw [hzc]
    exact ((TorusAct.main _ _ _ M.x _ c hc).2 hxb).1
  have hgood' : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z)) := by rw [hI]; exact hgood
  have hne : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := fun k => coord_ne_zero (hgood'.1 k)

  let t : K → ℂ := fun k => if h : ∀ p', M.blk p' ≠ some k then (basePart M.blk z ⟨⟨k, h⟩, (BM.F l).c ⟨k, h⟩⟩)⁻¹ else 1
  have htb : ∀ k : NonPluckerBlocks M.blk, t k.1 = (basePart M.blk z ⟨k, (BM.F l).c k⟩)⁻¹ := fun k => dif_pos k.2
  have ht1 : ∀ k, ¬ (∀ p', M.blk p' ≠ some k) → t k = 1 := fun k h => dif_neg h
  have ht : ∀ k, t k ≠ 0 := fun k => by
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [htb ⟨k, h⟩]; exact inv_ne_zero (hne _)
    · rw [ht1 k h]; exact one_ne_zero
  let z₁ : (Σ k, ι k) → ℂ := fun q => t q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := ((TorusAct.main _ _ _ y z t ht).2 hz).1
  have hb₁ : basePart M.blk z₁ = fun q : Σ k, baseIdx ι M.blk k => t q.1.1 * basePart M.blk z q := rfl
  have hval : valAt M.x ((BM.F l).υ p) (basePart M.blk z₁) = valAt M.x ((BM.F l).υ p) (basePart M.blk z) := by
    rw [hb₁]
    exact ((TorusAct.main _ _ _ M.x _ (fun k : NonPluckerBlocks M.blk => t k.1) fun k => ht _).2 hzb).2 _
  have hso₁ : SameOrbit (basePart M.blk z₁) (BM.Rb.lift x₀ x₀) :=
    ⟨fun k => t k.1 * c k, fun k => mul_ne_zero (ht _) (hc k), by
      rw [hb₁, hzc]; funext q; exact (mul_assoc _ _ _).symm⟩
  have hnorm : ∀ k, basePart M.blk z₁ ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hb₁]
    show t k.1 * _ = 1
    rw [htb k]
    exact inv_mul_cancel₀ (hne k)
  have hind := (BM.induced l x₀ hx p z₁ hz₁ hso₁ hnorm 1 isBlockDiag_one (by simp)).2 hp
  rw [hval] at hind

  have hscale : (BM.hom p).h z₁ = (∏ k, ‖t k‖ ^ M.dy p k) * (BM.hom p).h z := by
    have := (BM.hom p).smul t z ht
    rw [BM.hom_deg] at this
    exact this
  have hprod : (∏ k, ‖t k‖ ^ M.dy p k) = ‖baseMono M (BM.F l) p z‖⁻¹ := by
    have e := Fintype.prod_subtype_mul_prod_subtype (fun k : K => ∀ p', M.blk p' ≠ some k)
      (fun k : K => (‖t k‖ ^ M.dy p k : ℝ))
    rw [← e, Fintype.prod_eq_one (f := fun k : {k // ¬ ∀ p', M.blk p' ≠ some k} => ‖t k.1‖ ^ M.dy p k.1)
      (fun k => by rw [ht1 _ k.2]; simp), mul_one, baseMono, norm_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr (by ext; simp) fun k _ => ?_
    show ‖t k.1‖ ^ M.dy p k.1 = (‖basePart M.blk z ⟨k, (BM.F l).c k⟩ ^ M.dy p k.1‖)⁻¹
    rw [htb k, norm_inv, norm_zpow, _root_.inv_zpow]

  obtain ⟨hu0, hu1, hu2⟩ := hgood'.2.2 p hp
  obtain ⟨hinv, hv0⟩ := valAt_inv hzb hu0 hu1 hu2
  have hmono : baseMono M (BM.F l) p z ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)
  have hpos : 0 < (BM.hom p).h z := (BM.hom p).pos z hz.1
  rw [hscale, hprod, Real.log_mul (inv_ne_zero (norm_ne_zero_iff.2 hmono)) hpos.ne', Real.log_inv] at hind
  rw [hinv, norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 hmono) (inv_ne_zero (norm_ne_zero_iff.2 hv0)),
    Real.log_inv]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineFormula
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin

theorem hermitian_pair_one_coordinates (G : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) :
    herm2 G ![1, a] ![1, b] =
      G 0 0 + G 0 1 * b + (starRingEnd ℂ) a * G 1 0 + (starRingEnd ℂ) a * G 1 1 * b := by
  simp [herm2, dotProduct, mulVec, Fin.sum_univ_two]
  ring

theorem gram_identity (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.IsHermitian) (a₀ a₁ : ℂ) :
    (herm2 G ![1, a₀] ![1, a₀]).re * (herm2 G ![1, a₁] ![1, a₁]).re - ‖herm2 G ![1, a₀] ![1, a₁]‖ ^ 2 =
      G.det.re * ‖a₁ - a₀‖ ^ 2 := by
  have h10 : G 1 0 = (starRingEnd ℂ) (G 0 1) := (hG.apply 1 0).symm
  have h00 : (G 0 0).im = 0 := Complex.conj_eq_iff_im.mp (hG.apply 0 0)
  have h11 : (G 1 1).im = 0 := Complex.conj_eq_iff_im.mp (hG.apply 1 1)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, Matrix.det_fin_two,
    hermitian_pair_one_coordinates, hermitian_pair_one_coordinates, hermitian_pair_one_coordinates, h10]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, h00, h11]
  ring

theorem hermitian_pair_one_re_pos (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (a : ℂ) :
    0 < (herm2 G ![1, a] ![1, a]).re := by
  have hne : (![1, a] : Fin 2 → ℂ) ≠ 0 := fun h => by simpa using congrFun h 0
  have h := hG.dotProduct_mulVec_pos hne
  exact (Complex.lt_def.mp h).1

theorem det_re_pos (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) : 0 < G.det.re :=
  (Complex.lt_def.mp hG.det_pos).1

theorem logSin_eq_log_add_xiPot (G : Matrix (Fin 2) (Fin 2) ℂ) (a₀ a₁ : ℂ) (hG : G.PosDef) (hne : a₀ ≠ a₁) :
    logSin G a₀ a₁ = Real.log ‖a₁ - a₀‖ + (1 / 2) * (xiPot G a₀ + xiPot G a₁) := by
  have hA := hermitian_pair_one_re_pos G hG a₀
  have hB := hermitian_pair_one_re_pos G hG a₁
  have hD := det_re_pos G hG
  have hn : 0 < ‖a₁ - a₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hid := gram_identity G hG.1 a₀ a₁
  unfold logSin xiPot
  set A := (herm2 G ![1, a₀] ![1, a₀]).re
  set B := (herm2 G ![1, a₁] ![1, a₁]).re
  set C := ‖herm2 G ![1, a₀] ![1, a₁]‖
  set D := G.det.re
  set n := ‖a₁ - a₀‖
  have harg : 1 - C ^ 2 / (A * B) = D * n ^ 2 / (A * B) := by
    rw [← hid]
    field_simp
  rw [harg, Real.log_div (by positivity) (by positivity), Real.log_mul hD.ne' (by positivity),
    Real.log_mul hA.ne' hB.ne', Real.log_pow]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentFamilyAnalytic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem mul_elem_apply (A : Matrix (Fin N) (Fin N) ℂ) (ca cb r s : Fin N) (t : ℂ) :
    (A * (1 + Matrix.single cb ca t)) r s = A r s + if s = ca then A r cb * t else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  rw [Matrix.mul_apply]
  by_cases h : s = ca
  · subst h
    simp [Matrix.single_apply]
  · simp [Matrix.single_apply, h, Ne.symm h]

theorem elem_mul_elem {ca cb : Fin N} (hne : ca ≠ cb) (t u : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) * (1 + Matrix.single cb ca u) =
      1 + Matrix.single cb ca (t + u) := by
  ext r s
  rw [mul_elem_apply]
  by_cases h : s = ca
  · subst h
    by_cases hr : cb = r
    · subst hr
      simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hne, Ne.symm hne]
      try ring
    · simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hne, Ne.symm hne, hr, Ne.symm hr]
  · simp [Matrix.add_apply, Matrix.single_apply, h, Ne.symm h]

theorem mul_elem_cancel {ca cb : Fin N} (hne : ca ≠ cb) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) :
    A * (1 + Matrix.single cb ca t) * (1 + Matrix.single cb ca (-t)) = A := by
  rw [Matrix.mul_assoc, elem_mul_elem hne, add_neg_cancel, Matrix.single_zero, add_zero, Matrix.mul_one]

theorem isBlockDiag_elem {ca cb : Fin N} (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  intro r s hrs
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
  have h2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hrs hs
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem isLowerUni_mul_elem {ca cb : Fin N} (hlt : ca < cb) {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsLowerUni A)
    (t : ℂ) : IsLowerUni (A * (1 + Matrix.single cb ca t)) := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · rw [mul_elem_apply, hA.1]
    split_ifs with h
    · subst h
      rw [hA.2 r cb hlt, zero_mul, add_zero]
    · rw [add_zero]
  · rw [mul_elem_apply, hA.2 r s hrs]
    split_ifs with h
    · subst h
      rw [hA.2 r cb (hrs.trans hlt), zero_mul, add_zero]
    · rw [add_zero]

theorem isBlockDiag_Lc (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) :
    IsBlockDiag j (FC.Lc τ ca cb c τ') := by
  intro r s hrs
  have hne : r ≠ s := fun e => hrs (by rw [e])
  unfold FC.Lc
  rw [dif_neg (fun h => hrs h.1.2), if_neg hne]

theorem isLowerUni_Lc (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) :
    IsLowerUni (FC.Lc τ ca cb c τ') := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · unfold FC.Lc
    rw [dif_neg (fun h => lt_irrefl _ h.1.1), if_pos rfl]
  · unfold FC.Lc
    rw [dif_neg (fun h => lt_asymm hrs h.1.1), if_neg hrs.ne]

theorem Lc_apply_idx (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (q : FC.CIdx Ψ N j τ ca cb) :
    FC.Lc τ ca cb c q.1.1.1 q.1.1.2.1 q.1.1.2.2 = c q := by
  unfold FC.Lc
  rw [dif_pos (⟨q.1.2, q.2⟩ : _ ∧ _)]

theorem Lc_self_apply (τ : Ψ) {ca cb : Fin N} (hne : ca ≠ cb) (c : FC.CIdx Ψ N j τ ca cb → ℂ) :
    FC.Lc τ ca cb c τ cb ca = 0 := by
  unfold FC.Lc
  rw [dif_neg (fun h => h.2 rfl), if_neg (Ne.symm hne)]

theorem Lc_of_entries (τ : Ψ) {ca cb : Fin N} (hne : ca ≠ cb) (L : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hL : ∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) (h0 : L τ cb ca = 0) :
    FC.Lc τ ca cb (fun q : FC.CIdx Ψ N j τ ca cb => L q.1.1.1 q.1.1.2.1 q.1.1.2.2) = L := by
  funext τ'
  ext r s
  unfold FC.Lc
  split_ifs with h hrs
  · rfl
  · subst hrs
    exact ((hL τ').2.1 r).symm
  · by_cases e : (τ', r, s) = (τ, cb, ca)
    · obtain ⟨rfl, rfl, rfl⟩ : τ' = τ ∧ r = cb ∧ s = ca := by simpa using e
      exact h0.symm
    · have hn : ¬ (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) := fun h' => h ⟨h', e⟩
      by_cases hsr : s < r
      · exact ((hL τ').1 r s fun hb => hn ⟨hsr, hb⟩).symm
      · exact ((hL τ').2.2 r s (lt_of_le_of_ne (not_lt.1 hsr) hrs)).symm

theorem Lc_analytic (τ : Ψ) (ca cb : Fin N) (τ' : Ψ) (r s : Fin N) :
    AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ := by
  unfold FC.Lc
  by_cases h : (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) ∧ (τ', r, s) ≠ (τ, cb, ca)
  · simp only [dif_pos h]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : FC.CIdx Ψ N j τ ca cb => ℂ)
      ⟨⟨(τ', r, s), h.1⟩, h.2⟩).analyticOnNhd _
  · simp only [dif_neg h]
    exact analyticOnNhd_const

theorem exists_Lca (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j)
    (L : Ψ → Matrix (Fin N) (Fin N) ℂ) (hL : ∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) :
    ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L := by
  have hne : ca ≠ cb := hlt.ne
  let a : ℂ := L τ cb ca
  let L' : Ψ → Matrix (Fin N) (Fin N) ℂ := Function.update L τ (L τ * (1 + Matrix.single cb ca (-a)))
  have hτ : L' τ = L τ * (1 + Matrix.single cb ca (-a)) := Function.update_self _ _ _
  have hL' : ∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ') := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [hτ]
      exact ⟨(hL _).1.mul (isBlockDiag_elem hs _), isLowerUni_mul_elem hlt (hL _).2 _⟩
    · have : L' τ' = L τ' := Function.update_of_ne e _ _
      rw [this]
      exact hL τ'
  have h0 : L' τ cb ca = 0 := by
    rw [hτ, mul_elem_apply, if_pos rfl, (hL τ).2.1 cb, one_mul]
    exact add_neg_cancel _
  refine ⟨fun q => L' q.1.1.1 q.1.1.2.1 q.1.1.2.2, a, ?_⟩
  have hback : L τ * (1 + Matrix.single cb ca (-a)) * (1 + Matrix.single cb ca a) = L τ := by
    have := mul_elem_cancel hne (L τ) (-a)
    rwa [neg_neg] at this
  unfold FC.Lca
  rw [Lc_of_entries τ hne L' hL' h0, hτ, hback]
  funext τ'
  by_cases e : τ' = τ
  · subst e
    exact Function.update_self _ _ _
  · rw [Function.update_of_ne e]
    exact Function.update_of_ne e _ _

theorem Lca_prop (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j)
    (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) (τ' : Ψ) :
    IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ') := by
  unfold FC.Lca
  by_cases e : τ' = τ
  · subst e
    rw [Function.update_self]
    exact ⟨(isBlockDiag_Lc _ _ _ _ _).mul (isBlockDiag_elem hs _), isLowerUni_mul_elem hlt (isLowerUni_Lc _ _ _ _ _) _⟩
  · rw [Function.update_of_ne e]
    exact ⟨isBlockDiag_Lc _ _ _ _ _, isLowerUni_Lc _ _ _ _ _⟩

theorem Lca_injective (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ)
    (h : FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a') : c = c' ∧ a = a' := by
  have hne : ca ≠ cb := hlt.ne
  have hτ : FC.Lc τ ca cb c τ * (1 + Matrix.single cb ca a) = FC.Lc τ ca cb c' τ * (1 + Matrix.single cb ca a') := by
    have := congrFun h τ
    unfold FC.Lca at this
    rwa [Function.update_self, Function.update_self] at this
  have entry : ∀ (d : FC.CIdx Ψ N j τ ca cb → ℂ) (t : ℂ),
      (FC.Lc τ ca cb d τ * (1 + Matrix.single cb ca t)) cb ca = t := fun d t => by
    rw [mul_elem_apply, if_pos rfl, Lc_self_apply τ hne, (isLowerUni_Lc τ ca cb d τ).1 cb, zero_add, one_mul]
  have ha : a = a' := by
    rw [← entry c a, hτ, entry]
  subst ha
  have hc : FC.Lc τ ca cb c = FC.Lc τ ca cb c' := by
    funext τ'
    by_cases e : τ' = τ
    · subst e
      rw [← mul_elem_cancel hne (FC.Lc τ' ca cb c τ') a, hτ, mul_elem_cancel hne]
    · have := congrFun h τ'
      unfold FC.Lca at this
      rwa [Function.update_of_ne e, Function.update_of_ne e] at this
  refine ⟨funext fun q => ?_, rfl⟩
  rw [← Lc_apply_idx τ ca cb c q, hc, Lc_apply_idx]

theorem lc_main : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) τ', IsBlockDiag j (FC.Lc τ ca cb c τ') ∧ (FC.Lc τ ca cb c τ').det ≠ 0) ∧ (∀ τ' r s, AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ) ∧ (∀ L : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L) ∧ (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) τ', IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ')) ∧ ∀ (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ), FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a' → c = c' ∧ a = a' := by
  intro Ψ _ _ N j τ ca cb hlt hs
  refine ⟨fun c τ' => ⟨isBlockDiag_Lc τ ca cb c τ', ?_⟩, fun τ' r s => Lc_analytic τ ca cb τ' r s,
    fun L hL => exists_Lca τ hlt hs L hL, fun c a τ' => Lca_prop τ hlt hs c a τ',
    fun c c' a a' h => Lca_injective τ hlt c c' a a' h⟩
  rw [(isLowerUni_Lc τ ca cb c τ').det]
  exact one_ne_zero

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemSpanOfRealCombinationPeriodsStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_of_real_combination_periods : ∀ (g k n : ℕ) (Λ : Type) [AddCommGroup Λ] (P : Λ →+ (Fin g → ℂ)) (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n), LinearIndependent ℝ (fun j => P (b j)) → Function.Injective f → ∀ (x : Λ) (c : Fin k → ℝ), P x = ∑ i, (c i : ℂ) • P (b (f i)) → x ∈ Submodule.span ℤ (Set.range fun i => b (f i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.mem_span_part_of_period_real_comb | exact GlobalTheory.CompanionTheory.Ar.Cusp.mem_span_part_of_period_real_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.mem_span_part_of_period_real_comb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricQuotientOfMultihomogPairStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_quotient_of_multihomog_pair : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → (∀ y : R.X, aeval (R.lift y y) G ≠ (0 : ℂ) → aeval (R.lift y y) Hf ≠ (0 : ℂ) → π y ∈ S.open') → ∀ x₀ : R.X, aeval (R.lift x₀ x₀) Hf ≠ (0 : ℂ) → ∃ (V : Set R.X) (N : ℕ) (C : ℝ), IsOpen V ∧ x₀ ∈ V ∧ 0 < N ∧ ∀ y ∈ V, aeval (R.lift y y) Hf ≠ (0 : ℂ) ∧ (π y ∈ S.open' → aeval (R.lift y y) G ≠ (0 : ℂ) → Real.log ‖(aeval (R.lift y y) G : ℂ) / aeval (R.lift y y) Hf‖ - Real.log (Eh.h (R.lift y y)) ≤ -(1 / (2 * (N : ℝ))) * rW S.L S.s (π y) + C) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay | exact GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantLinearFunctionalStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_discriminant_linear_functional : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
    ∃ L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ, ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantOneRowExpansionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_discriminant_one_row_expansion : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (c : Fin (d + 1) → ℝ) (v : Fin (d + 1) → ℝ) (n : Fin 3 → ℝ) (e : ℂ),
      ((d + 1).factorial : ℂ) * mdisc (fun r => blk ((c r : ℂ) * e)
        ((∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H)) =
      e * L (evalW n n (pderiv (some 0) (∏ r, rowW ![c r, 0] (v r)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.extract_one | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.extract_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.extract_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantTwoRowExpansionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_discriminant_two_row_expansion : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (u : Fin (d + 2) → Fin 2 → ℝ) (v : Fin (d + 2) → ℝ) (n₀ n₁ : Fin 3 → ℝ) (e₀ e₁ : ℂ),
      ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁)
        ((∑ i, ((u r 0 * n₀ i + u r 1 * n₁ i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))) =
      e₀ * e₁ * L (evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r, rowW (u r) (v r))))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NearTriangularOfStepConditionsStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.near_triangular_of_step_conditions : ∀ (N j : ℕ) (a b ca cb : Fin N) (C : Matrix (Fin N) (Fin N) ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j C → (∀ i, IsProperStep N j i → i ≠ a → ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → C r c = 0) → ∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C r c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepShape.upper_of_steps | exact GlobalTheory.CompanionTheory.Ar.PB.StepShape.upper_of_steps | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepShape.upper_of_steps <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeFullRankSublatticeStatement
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_degree_full_rank_sublattice : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier), E.rank F = Module.finrank (𝓞 K) E.carrier → E.normDegree F ≤ E.normDegree ⊤ ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ F) → E.normDegree ⊤ ≤ E.normDegree F + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds | exact GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds | (intros; apply GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PluckerNonvanishingOrbitInvariant
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem plk_ne_zero_iff_of_sameOrbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (z z' : (Σ k, ι k) → ℂ) (p : Ψ × Fin N), SameOrbit z z' → (FC.plk M F b z p ≠ 0 ↔ FC.plk M F b z' p ≠ 0) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b z z' p h
  obtain ⟨c, hc, rfl⟩ := h
  unfold FC.plk
  cases hb : M.blk p with
  | none => simp
  | some k =>
    simp only [Option.elim, mul_left_comm _ (c k), ← Finset.mul_sum, ne_eq, mul_eq_zero, hc k, false_or]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

