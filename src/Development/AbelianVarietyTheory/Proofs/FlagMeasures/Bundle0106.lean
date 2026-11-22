import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormCongruenceLiftSmallGroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0102
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0094
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameComplementChangeOfBasis
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem frameForm_symm_zero {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ} (hH : Hᴴ = H)
    (x y : Fin N → ℂ) : star x ⬝ᵥ (H *ᵥ y) = star (star y ⬝ᵥ (H *ᵥ x)) := by
  rw [star_dotProduct, star_mulVec, hH, ← dotProduct_mulVec]

private theorem dotProduct_mulVec_sum_smul {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ} {ι : Type}
    [Fintype ι] (x : Fin N → ℂ) (g : ι → ℂ) (v : ι → Fin N → ℂ) :
    star x ⬝ᵥ (H *ᵥ ∑ i, g i • v i) = ∑ i, g i * (star x ⬝ᵥ (H *ᵥ v i)) := by
  simp [mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul]

theorem frame_orthogonal_eq_zero {N r k : ℕ} {H : Matrix (Fin N) (Fin N) ℂ}
    {e f : Fin r → Fin N → ℂ} {z : Fin N → ℂ} {w : Fin k → Fin N → ℂ}
    (hN : N = 2 * r + k + 1) (hH : Hᴴ = H)
    (hee : ∀ a b, star (e a) ⬝ᵥ (H *ᵥ e b) = 0) (hff : ∀ a b, star (f a) ⬝ᵥ (H *ᵥ f b) = 0)
    (hef : ∀ a b, star (e a) ⬝ᵥ (H *ᵥ f b) = if a = b then 1 else 0)
    (hz : ∀ a, star (e a) ⬝ᵥ (H *ᵥ z) = 0 ∧ star (f a) ⬝ᵥ (H *ᵥ z) = 0)
    (hzz : star z ⬝ᵥ (H *ᵥ z) ≠ 0)
    (hww : ∀ a b, star (w a) ⬝ᵥ (H *ᵥ w b) = if a = b then 1 else 0)
    (hw : ∀ a, (∀ c, star (e c) ⬝ᵥ (H *ᵥ w a) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ w a) = 0) ∧
      star z ⬝ᵥ (H *ᵥ w a) = 0)
    (u : Fin N → ℂ) (hu : (∀ c, star (e c) ⬝ᵥ (H *ᵥ u) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ u) = 0) ∧
      star z ⬝ᵥ (H *ᵥ u) = 0) (huw : ∀ a, star (w a) ⬝ᵥ (H *ᵥ u) = 0) : u = 0 := by
  have sym := fun x y => frameForm_symm_zero hH x y
  have hfe : ∀ a b, star (f a) ⬝ᵥ (H *ᵥ e b) = if a = b then 1 else 0 := by
    intro a b
    rw [sym, hef b a]
    rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [hab, hab.symm]
  have hze : ∀ a, star z ⬝ᵥ (H *ᵥ e a) = 0 := fun a => by rw [sym, (hz a).1, star_zero]
  have hzf : ∀ a, star z ⬝ᵥ (H *ᵥ f a) = 0 := fun a => by rw [sym, (hz a).2, star_zero]
  have hwe : ∀ a c, star (w a) ⬝ᵥ (H *ᵥ e c) = 0 := fun a c => by rw [sym, ((hw a).1 c).1, star_zero]
  have hwf : ∀ a c, star (w a) ⬝ᵥ (H *ᵥ f c) = 0 := fun a c => by rw [sym, ((hw a).1 c).2, star_zero]
  have hwz : ∀ a, star (w a) ⬝ᵥ (H *ᵥ z) = 0 := fun a => by rw [sym, (hw a).2, star_zero]
  have hew : ∀ c a, star (e c) ⬝ᵥ (H *ᵥ w a) = 0 := fun c a => ((hw a).1 c).1
  have hfw : ∀ c a, star (f c) ⬝ᵥ (H *ᵥ w a) = 0 := fun c a => ((hw a).1 c).2
  have hzw : ∀ a, star z ⬝ᵥ (H *ᵥ w a) = 0 := fun a => (hw a).2
  have hez : ∀ a, star (e a) ⬝ᵥ (H *ᵥ z) = 0 := fun a => (hz a).1
  have hfz : ∀ a, star (f a) ⬝ᵥ (H *ᵥ z) = 0 := fun a => (hz a).2
  set v : (Fin r ⊕ Fin r) ⊕ (Fin k ⊕ Unit) → Fin N → ℂ :=
    Sum.elim (Sum.elim e f) (Sum.elim w fun _ => z) with hv
  have key : ∀ g : (Fin r ⊕ Fin r) ⊕ (Fin k ⊕ Unit) → ℂ,
      (∀ j, star (v j) ⬝ᵥ (H *ᵥ ∑ i, g i • v i) = 0) → g = 0 := by
    intro g hg
    simp only [dotProduct_mulVec_sum_smul] at hg
    simp only [Fintype.sum_sum_type] at hg
    funext i
    rcases i with ((a | a) | (a | u))
    · have := hg (.inl (.inr a))
      simpa [hv, hfe, hff, hwe, hfw, hfz, mul_ite] using this
    · have := hg (.inl (.inl a))
      simpa [hv, hee, hef, hew, hez, mul_ite] using this
    · have := hg (.inr (.inl a))
      simpa [hv, hwe, hwf, hww, hwz, mul_ite] using this
    · have := hg (.inr (.inr u))
      simpa [hv, hze, hzf, hzw, hzz] using this
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := key g (fun j => by rw [hg, mulVec_zero, dotProduct_zero])
    exact congrFun this i
  have hcard : Fintype.card ((Fin r ⊕ Fin r) ⊕ (Fin k ⊕ Unit)) = Module.finrank ℂ (Fin N → ℂ) := by
    simp [hN]
    ring
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hu' : u ∈ Submodule.span ℂ (Set.range v) := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu'
  have hg0 := key g (fun j => by
    rw [hg]
    rcases j with ((a | a) | (a | _))
    · simpa [hv] using (hu.1 a).1
    · simpa [hv] using (hu.1 a).2
    · simpa [hv] using huw a
    · simpa [hv] using hu.2)
  rw [← hg, hg0]
  simp

theorem frame_complement_change_of_basis : ∀ (N r k n : ℕ) (h : k = n) (H : Matrix (Fin N) (Fin N) ℂ) (e f : Fin r → Fin N → ℂ) (z : Fin N → ℂ) (w : Fin k → Fin N → ℂ) (q : Fin n → Fin N → ℂ), N = 2 * r + k + 1 → Hᴴ = H → IsUnit H.det → (∀ a b, star (e a) ⬝ᵥ (H *ᵥ e b) = 0) → (∀ a b, star (f a) ⬝ᵥ (H *ᵥ f b) = 0) → (∀ a b, star (e a) ⬝ᵥ (H *ᵥ f b) = if a = b then 1 else 0) → (∀ a, star (e a) ⬝ᵥ (H *ᵥ z) = 0 ∧ star (f a) ⬝ᵥ (H *ᵥ z) = 0) → star z ⬝ᵥ (H *ᵥ z) ≠ 0 → (∀ a b, star (w a) ⬝ᵥ (H *ᵥ w b) = if a = b then 1 else 0) → (∀ a, (∀ c, star (e c) ⬝ᵥ (H *ᵥ w a) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ w a) = 0) ∧ star z ⬝ᵥ (H *ᵥ w a) = 0) → (∀ a, (∀ c, star (e c) ⬝ᵥ (H *ᵥ q a) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ q a) = 0) ∧ star z ⬝ᵥ (H *ᵥ q a) = 0) → ∀ G : Matrix (Fin n) (Fin n) ℂ, (∀ a b, G a b = star (q a) ⬝ᵥ (H *ᵥ q b)) → IsUnit G.det → ∃ o : Matrix (Fin n) (Fin n) ℂ, IsUnit o.det ∧ oᴴ * G * o = 1 ∧ ∀ s : Matrix (Fin N) (Fin N) ℂ, sᴴ * H * s = H → (∀ a, s *ᵥ e a = e a ∧ s *ᵥ f a = f a) → s *ᵥ z = z → ∃ m ∈ Matrix.unitaryGroup (Fin n) ℂ, m.submatrix (Fin.cast h) (Fin.cast h) = (Matrix.of fun a b => star (w a) ⬝ᵥ (H *ᵥ (s *ᵥ w b))) ∧ G⁻¹ * (Matrix.of fun a b => star (q a) ⬝ᵥ (H *ᵥ (s *ᵥ q b))) = o * m * o⁻¹ := by
  intro N r k n h H e f z w q hN hH _hdet hee hff hef hz hzz hww hw hq G hG hGdet
  subst h
  have sym := fun x y => frameForm_symm_zero hH x y
  have expand : ∀ x : Fin N → ℂ, ((∀ c, star (e c) ⬝ᵥ (H *ᵥ x) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ x) = 0) ∧
      star z ⬝ᵥ (H *ᵥ x) = 0) → x = ∑ a, (star (w a) ⬝ᵥ (H *ᵥ x)) • w a := by
    intro x hx
    have h0 := frame_orthogonal_eq_zero hN hH hee hff hef hz hzz hww hw
      (x - ∑ a, (star (w a) ⬝ᵥ (H *ᵥ x)) • w a) ?_ ?_
    · exact sub_eq_zero.mp h0
    · refine ⟨fun c => ⟨?_, ?_⟩, ?_⟩
      · simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, (hx.1 c).1, fun a => ((hw a).1 c).1]
      · simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, (hx.1 c).2, fun a => ((hw a).1 c).2]
      · simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, hx.2, fun a => (hw a).2]
    · intro a
      simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, hww, mul_ite]
  have parseval : ∀ x y : Fin N → ℂ,
      ((∀ c, star (e c) ⬝ᵥ (H *ᵥ y) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ y) = 0) ∧ star z ⬝ᵥ (H *ᵥ y) = 0) →
      star x ⬝ᵥ (H *ᵥ y) = ∑ c, star (star (w c) ⬝ᵥ (H *ᵥ x)) * (star (w c) ⬝ᵥ (H *ᵥ y)) := by
    intro x y hy
    conv_lhs => rw [expand y hy]
    rw [dotProduct_mulVec_sum_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sym x (w c), mul_comm]
  set P := Matrix.of fun c b => star (w c) ⬝ᵥ (H *ᵥ q b) with hPdef
  have hGP : G = Pᴴ * P := by
    ext a b
    rw [hG, parseval (q a) (q b) (hq b), Matrix.mul_apply]
    simp [hPdef, Matrix.conjTranspose_apply]
  have hP : IsUnit P.det := by
    rw [hGP, Matrix.det_mul, Matrix.det_conjTranspose] at hGdet
    exact isUnit_of_mul_isUnit_right hGdet
  have hPh : IsUnit Pᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hP.star
  refine ⟨P⁻¹, Matrix.isUnit_nonsing_inv_det _ hP, ?_, ?_⟩
  · rw [hGP, Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_assoc (Pᴴ)⁻¹,
      Matrix.nonsing_inv_mul _ hPh, Matrix.one_mul, Matrix.mul_nonsing_inv _ hP]
  intro s hs hfix hzfix
  have pres : ∀ x y : Fin N → ℂ, star (s *ᵥ x) ⬝ᵥ (H *ᵥ (s *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y) := by
    intro x y
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hs]
  have sperp : ∀ x : Fin N → ℂ,
      ((∀ c, star (e c) ⬝ᵥ (H *ᵥ x) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ x) = 0) ∧ star z ⬝ᵥ (H *ᵥ x) = 0) →
      ((∀ c, star (e c) ⬝ᵥ (H *ᵥ (s *ᵥ x)) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ (s *ᵥ x)) = 0) ∧
        star z ⬝ᵥ (H *ᵥ (s *ᵥ x)) = 0) := by
    intro x hx
    refine ⟨fun c => ⟨?_, ?_⟩, ?_⟩
    · rw [← (hfix c).1, pres]; exact (hx.1 c).1
    · rw [← (hfix c).2, pres]; exact (hx.1 c).2
    · rw [← hzfix, pres]; exact hx.2
  set M := Matrix.of fun a b => star (w a) ⬝ᵥ (H *ᵥ (s *ᵥ w b)) with hMdef
  refine ⟨M, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply, ← hww a b, ← pres (w a) (w b),
      parseval _ _ (sperp _ (hw b))]
    simp [hMdef, Matrix.conjTranspose_apply]
  · ext a b
    simp [hMdef]
  · have hQ : (Matrix.of fun a b => star (q a) ⬝ᵥ (H *ᵥ (s *ᵥ q b))) = Pᴴ * (M * P) := by
      ext a b
      have hsq : s *ᵥ q b = ∑ d, P d b • (s *ᵥ w d) := by
        conv_lhs => rw [expand (q b) (hq b)]
        rw [mulVec_sum]
        simp [mulVec_smul, hPdef]
      rw [Matrix.of_apply, parseval _ _ (sperp _ (hq b)), Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hsq, dotProduct_mulVec_sum_smul, Matrix.mul_apply]
      simp [hPdef, hMdef, Matrix.conjTranspose_apply, mul_comm]
    rw [hQ, hGP, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Pᴴ)⁻¹, Matrix.nonsing_inv_mul _ hPh, Matrix.one_mul, Matrix.mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsGapsExceed
section
open GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem gaps_exceed :
    ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x →
      ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → ∀ r : ℝ, k ≤ r → r ≤ 2 * k →
      C * k * m ^ 4 + r * m ^ 10 < 4 * Del ∧ C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) ∧
      C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps ∧
      C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
  intro eps CD heps _heps' hCD C hC
  refine ⟨max (max 1 (C + 2)) (max (C ^ (100 / eps)) ((16 : ℝ) ^ (2 / eps))), ?_⟩
  intro x hx m f k lrd Del h r hkr hrk
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxC : C + 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxC' : C ^ (100 / eps) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx16 : (16 : ℝ) ^ (2 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 ≤ x := by linarith
  have hm1 : 1 ≤ m := le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo
  have hm4 : x ≤ m ^ 4 := by
    have h1 : (x ^ ((1 : ℝ) / 4)) ^ 4 ≤ m ^ 4 := by
      gcongr
      exact h.m_lo
    have h2 : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
    linarith
  have hf : x ≤ f := le_trans hm4 h.mf
  have hk : x ≤ k := le_trans hf h.fk
  have hr : x ≤ r := le_trans hk hkr
  have hf1 : 1 ≤ f := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hL : 1 ≤ x ^ eps := Real.one_le_rpow hx1 heps.le
  have hL' : 1 ≤ x ^ (eps / 100) := Real.one_le_rpow hx1 (by positivity)
  have hm10 : m ^ 10 ≤ f ^ 3 := by
    have h1 : m ^ 10 ≤ m ^ 12 := pow_le_pow_right₀ hm1 (by norm_num)
    have h2 : m ^ 12 = (m ^ 4) ^ 3 := by ring
    have h3 : (m ^ 4) ^ 3 ≤ f ^ 3 := by gcongr; exact h.mf
    linarith
  have hf3 : f ≤ f ^ 3 := by
    have := pow_le_pow_right₀ hf1 (show 1 ≤ 3 by norm_num); simpa using this
  have hS : C * k * m ^ 4 + r * m ^ 10 ≤ (C + 2) * k * f ^ 3 := by
    have h1 : C * k * m ^ 4 ≤ C * k * f ^ 3 := by
      have : m ^ 4 ≤ f ^ 3 := le_trans h.mf hf3
      gcongr
    have h2 : r * m ^ 10 ≤ (2 * k) * f ^ 3 := by
      gcongr
    nlinarith
  have hSpos : 0 < C * k * m ^ 4 + r * m ^ 10 := by positivity

  have hy1 : 1 ≤ k * f * x ^ eps := by
    have : 1 ≤ k * f := one_le_mul_of_one_le_of_one_le hk1 hf1
    exact one_le_mul_of_one_le_of_one_le this hL
  have hDel3 : (k * f * x ^ eps) ^ (3 : ℕ) ≤ Del := by
    have := Real.rpow_le_rpow_of_exponent_le hy1 hCD
    rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    linarith [h.Del_lo]
  have hDelpos : 0 < Del := by
    have : 0 < (k * f * x ^ eps) ^ (3 : ℕ) := by positivity
    linarith
  have hc1 : C * k * m ^ 4 + r * m ^ 10 < 4 * Del := by
    have hkf3 : 0 < k * f ^ 3 := by positivity
    have hk2 : C + 2 < 4 * k ^ 2 := by nlinarith
    have e1 : (C + 2) * k * f ^ 3 < 4 * k ^ 2 * (k * f ^ 3) := by nlinarith
    have e2 : 4 * k ^ 2 * (k * f ^ 3) ≤ 4 * (k * f * x ^ eps) ^ (3 : ℕ) := by
      have hkf : k * f ≤ k * f * x ^ eps := le_mul_of_one_le_right (by positivity) hL
      have : (k * f) ^ 3 ≤ (k * f * x ^ eps) ^ 3 := by gcongr
      nlinarith
    linarith

  set t := x ^ (eps / 2) with ht
  have ht16 : 16 ≤ t := by
    have h1 : ((16 : ℝ) ^ (2 / eps)) ^ (eps / 2) ≤ x ^ (eps / 2) :=
      Real.rpow_le_rpow (by positivity) hx16 (by positivity)
    have h2 : ((16 : ℝ) ^ (2 / eps)) ^ (eps / 2) = 16 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 2 / eps * (eps / 2) = 1 := by field_simp
      rw [this, Real.rpow_one]
    linarith
  have hxe : x ^ eps = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; congr 1; push_cast; ring
  have hDelE : Del ≤ Real.exp t := by
    have := h.Del_hi
    rw [Real.log_le_iff_le_exp hDelpos] at this
    exact this
  have hc2 : C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) := by
    rw [Real.lt_sqrt hSpos.le]
    have e1 : (C * k * m ^ 4 + r * m ^ 10) ^ 2 < (4 * Real.exp t) ^ 2 := by
      have : C * k * m ^ 4 + r * m ^ 10 < 4 * Real.exp t := by linarith
      gcongr
    have e2 : (4 * Real.exp t) ^ 2 = Real.exp (Real.log 16 + 2 * t) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
      rw [show 2 * t = t + t by ring, Real.exp_add]; ring
    have e3 : Real.log 16 + 2 * t ≤ x ^ eps := by
      have : Real.log 16 ≤ 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      rw [hxe]; nlinarith
    have e4 : Real.exp (Real.log 16 + 2 * t) ≤ bx x eps := by
      unfold bx; exact Real.exp_le_exp.mpr e3
    linarith

  have hc3 : C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
    have hf35 : f ^ 3 ≤ f ^ 5 := pow_le_pow_right₀ hf1 (by norm_num)
    have e1 : C * k * m ^ 4 + r * m ^ 10 ≤ (C + 2) * r * f ^ 5 := by
      have : (C + 2) * k * f ^ 3 ≤ (C + 2) * r * f ^ 5 := by gcongr
      linarith
    have hx18 : x ≤ x ^ 18 := by
      have := pow_le_pow_right₀ hx1 (show 1 ≤ 18 by norm_num); simpa using this
    have hr18 : x ^ 18 ≤ r ^ 18 := by gcongr
    have e2 : (C + 2) * r * f ^ 5 < r ^ 18 * (r * f ^ 5) := by
      have hp : 0 < r * f ^ 5 := by positivity
      have hC18 : C + 2 < r ^ 18 := by
        have hx2 : x ^ 2 ≤ x ^ 18 := pow_le_pow_right₀ hx1 (by norm_num)
        have : x < x ^ 2 := by nlinarith
        linarith
      have := mul_lt_mul_of_pos_right hC18 hp
      calc (C + 2) * r * f ^ 5 = (C + 2) * (r * f ^ 5) := by ring
        _ < r ^ 18 * (r * f ^ 5) := this
    have e3 : r ^ 18 * (r * f ^ 5) = r ^ 19 * f ^ 5 := by ring
    have e4 : r ^ 19 * f ^ 5 ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
      have hp : 0 ≤ r ^ 19 * f ^ 5 := by positivity
      have h1 : 1 ≤ x ^ (eps / 100) * x ^ eps := one_le_mul_of_one_le_of_one_le hL' hL
      have := mul_le_mul_of_nonneg_right h1 hp
      calc r ^ 19 * f ^ 5 = 1 * (r ^ 19 * f ^ 5) := by ring
        _ ≤ (x ^ (eps / 100) * x ^ eps) * (r ^ 19 * f ^ 5) := this
        _ = x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by ring
    linarith

  have hc4 : C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
    have hCx : C ≤ x ^ (eps / 100) := by
      have h1 : (C ^ (100 / eps)) ^ (eps / 100) ≤ x ^ (eps / 100) :=
        Real.rpow_le_rpow (by positivity) hxC' (by positivity)
      have h2 : (C ^ (100 / eps)) ^ (eps / 100) = C := by
        rw [← Real.rpow_mul hC.le]
        have : 100 / eps * (eps / 100) = 1 := by field_simp
        rw [this, Real.rpow_one]
      linarith
    have hp : 0 ≤ r ^ 19 * f ^ 5 * x ^ eps := by positivity
    have := mul_le_mul_of_nonneg_right hCx hp
    calc C * r ^ 19 * f ^ 5 * x ^ eps = C * (r ^ 19 * f ^ 5 * x ^ eps) := by ring
      _ ≤ x ^ (eps / 100) * (r ^ 19 * f ^ 5 * x ^ eps) := this
      _ = x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by ring
  exact ⟨hc1, hc2, hc3, hc4⟩

end GlobalTheory.Diag.PG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsRankClausesFirstHalf
section
namespace GlobalTheory.Diag.PG

theorem rankNums_first_half : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x →
    ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → C * m ^ 5 * f * x ^ eps ≤ k ∧
      Real.log f ≤ Real.sqrt (m / 2 - 1) ∧ C * x ^ eps ≤ f * Real.log k ∧ C * (m ^ 2 * x ^ eps) ≤ k ∧ C ≤ m ∧
      C * x ^ eps ≤ m - 1 ∧ C ≤ k ∧ 1 < x ^ eps := by
  intro eps CD heps heps' _ C
  set C1 : ℝ := max C 2 with hC1
  have hCC1 : C ≤ C1 := le_max_left _ _
  have hC12 : 2 ≤ C1 := le_max_right _ _
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, C1 ≤ x ^ (eps / 2) :=
    (tendsto_rpow_atTop (by linarith)).eventually_ge_atTop C1
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, C1 + 1 ≤ x ^ ((1 : ℝ) / 52) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop (C1 + 1)
  have e3 : ∀ᶠ x : ℝ in Filter.atTop, (200 : ℝ) ≤ x ^ ((1 : ℝ) / 16) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 200
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x := Filter.eventually_ge_atTop 2
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (e1.and (e2.and (e3.and e4)))
  refine ⟨x0, fun x hx m f k lrd Del h => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hx0 x hx
  have hx0' : (0 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  set A := x ^ eps with hA
  have hA1 : 1 < A := Real.one_lt_rpow hx1 heps
  set y := x ^ ((1 : ℝ) / 52) with hy
  have hAy : A ≤ y := Real.rpow_le_rpow_of_exponent_le hx1.le heps'.le
  set q := x ^ ((1 : ℝ) / 4) with hq
  have hqy : q = y ^ (13 : ℕ) := by
    rw [hq, hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0']; norm_num
  have hy1 : 1 ≤ y := by linarith
  have hy13 : y ^ 2 ≤ y ^ (13 : ℕ) := pow_le_pow_right₀ hy1 (by norm_num)
  have hq_big : C1 * A + 1 ≤ q := by
    rw [hqy]; nlinarith
  have hm : C1 * A + 1 ≤ m := le_trans hq_big h.m_lo
  have hm1 : 1 ≤ m := by nlinarith
  have hm3 : 3 ≤ m := by nlinarith
  have hm4 : m ≤ m ^ 4 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hf : m ≤ f := le_trans hm4 h.mf
  have hf1 : 1 ≤ f := by linarith
  have hk : m ≤ k := le_trans hf h.fk
  have hCA : C * A ≤ C1 * A := mul_le_mul_of_nonneg_right hCC1 (by linarith)
  have hB0 : 0 ≤ m ^ 5 * f * A := by positivity
  have hk1 : C1 * (m ^ 5 * f * A) ≤ k :=
    le_trans (mul_le_mul_of_nonneg_right h1 hB0) h.k_lo
  have hm25 : m ^ 2 ≤ m ^ 5 * f := by
    have : m ^ 2 ≤ m ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
    nlinarith
  have hlogk : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hC1A : C1 ≤ C1 * A := by
    have := mul_le_mul_of_nonneg_left hA1.le (by linarith : (0:ℝ) ≤ C1)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hA1⟩
  · have : C * (m ^ 5 * f * A) ≤ C1 * (m ^ 5 * f * A) := mul_le_mul_of_nonneg_right hCC1 hB0
    calc C * m ^ 5 * f * A = C * (m ^ 5 * f * A) := by ring
      _ ≤ k := le_trans this hk1
  ·
    set t := x ^ ((1 : ℝ) / 16) with ht
    have hqt : q = t ^ (4 : ℕ) := by
      rw [hq, ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0']; norm_num
    have hf0 : 0 < f := by linarith
    have hlf : Real.log f ≤ 5 * Real.log x := by
      have : Real.log f ≤ Real.log (x ^ (5 : ℝ)) :=
        Real.log_le_log hf0 (le_trans h.fk h.k_hi)
      rw [Real.log_rpow (by linarith)] at this
      exact this
    have hlx : Real.log x ≤ t / (1 / 16) := Real.log_le_rpow_div hx0' (by norm_num)
    have h80 : 80 * t ≤ Real.sqrt (m / 2 - 1) := by
      rw [Real.le_sqrt (by linarith)]
      have hmq : t ^ (4 : ℕ) ≤ m := hqt ▸ h.m_lo
      have ht2 : 40000 ≤ t ^ 2 := by nlinarith
      have ht4 : t ^ (4 : ℕ) = t ^ 2 * t ^ 2 := by ring
      have : (80 * t) ^ 2 = 6400 * t ^ 2 := by ring
      nlinarith
      all_goals linarith
    have : 5 * Real.log x ≤ 80 * t := by
      have : t / (1 / 16) = 16 * t := by ring
      linarith
    linarith
  · calc C * A ≤ C1 * A := hCA
      _ ≤ m := by linarith
      _ ≤ f := hf
      _ = f * 1 := (mul_one f).symm
      _ ≤ f * Real.log k := mul_le_mul_of_nonneg_left hlogk (by linarith)
  · have hB2 : 0 ≤ m ^ 2 * A := by positivity
    calc C * (m ^ 2 * A) ≤ C1 * (m ^ 2 * A) := mul_le_mul_of_nonneg_right hCC1 hB2
      _ ≤ C1 * (m ^ 5 * f * A) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_right hm25 (by linarith)
      _ ≤ k := hk1
  · linarith
  · linarith
  · linarith

end GlobalTheory.Diag.PG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormCongruenceLiftSmallGroupStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairNormalForm_congruence_lift_smallGroup : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔫 : Ideal (𝓞 K), (∀ x ∈ 𝔫, ∃ y ∈ 𝔫, (y : K) = star (x : K)) → ∀ s ∈ N.R, (∀ x ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'), s x - x ∈ (Ideal.span {(N.T : 𝓞 K)} * 𝔫) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'))) → ∃ s' ∈ N.Rs, (∀ y ∈ V0 N.F N.F', s' y = s y) ∧ ∀ x ∈ N.P0, s' x - x ∈ 𝔫 • N.P0 := by
  first | exact @GlobalTheory.DegCnt.LiftS.lift_congruence | exact GlobalTheory.DegCnt.LiftS.lift_congruence | (intros; apply GlobalTheory.DegCnt.LiftS.lift_congruence <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormUniqueUpToUnipotentStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairNormalForm_unique_up_to_unipotent : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (N₀ N₁ : NF H r), SameGr F N₀.F → SameGr F N₁.F → N₀.j = N₁.j → N₀.c = N₁.c → N₀.T = N₁.T → pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j → ∃ s : V ≃ₗ[K] V, F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by
  first | exact @GlobalTheory.DegAsm.nf_unique | exact GlobalTheory.DegAsm.nf_unique | (intros; apply GlobalTheory.DegAsm.nf_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolPos
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegAsm.WeightInf

theorem invVol_nn {G : Type} [Group G] (A B : Subgroup G) : 0 ≤ GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  positivity

theorem invVol_pos' {G : Type} [Group G] (A B : Subgroup G) (h1 : A.relIndex B ≠ 0) (h2 : B.relIndex A ≠ 0) :
    0 < GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  have h1' := Nat.pos_of_ne_zero h1
  have h2' := Nat.pos_of_ne_zero h2
  positivity

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), (∀ (N : NF H r) (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → 0 < N.om Λ ∧ ∀ s ∈ N.R, N.om (s • Λ) = N.om Λ) ∧ ∀ (F F' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V), 0 ≤ omI F F' 𝔡 Λ ∧ (∀ N : NF H r, Adapt F F' 𝔡 N → omI F F' 𝔡 Λ ≤ N.om Λ) ∧ ∀ a c : ℝ, 0 ≤ c → (∃ N : NF H r, Adapt F F' 𝔡 N) → (∀ N : NF H r, Adapt F F' 𝔡 N → a ≤ c * N.om Λ) → a ≤ c * omI F F' 𝔡 Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r
  refine ⟨?_, ?_⟩
  · intro N g Λ hg hT
    have hnil := (GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N).2.2.2.2
    have href := (GlobalTheory.DegCnt.InnerLat.main K V H hK r N g Λ hg hT).2.2.2.2.1
    have hΛ : Submodule.IsLattice K Λ := ((isUnimod_iff H Λ).1 hT.1.1).1
    have h1 := GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil Λ _ hΛ href
    have h2 := GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ Λ href hΛ
    refine ⟨invVol_pos' _ _ h2.1 h1.1, fun s hs => ?_⟩
    have h3 := (GlobalTheory.DegCnt.StabInv.main K V H hK r N g Λ hg hT s hs).2.1.1
    unfold NF.om
    rw [h3]
    exact h1.2 s hs
  · intro F F' 𝔡 Λ
    have hnn : ∀ x ∈ ((fun N : NF H r => N.om Λ) '' {N | Adapt F F' 𝔡 N}), (0 : ℝ) ≤ x := by
      rintro _ ⟨N, -, rfl⟩
      exact invVol_nn _ _
    refine ⟨Real.sInf_nonneg hnn, fun N hN => csInf_le ⟨0, hnn⟩ ⟨N, hN, rfl⟩, ?_⟩
    rintro a c hc ⟨N₀, hN₀⟩ h
    rcases hc.eq_or_lt with rfl | hc
    · simpa using h N₀ hN₀
    · rw [← div_le_iff₀' hc]
      refine le_csInf ⟨_, N₀, hN₀, rfl⟩ ?_
      rintro _ ⟨N, hN, rfl⟩
      rw [div_le_iff₀' hc]
      exact h N hN

end GlobalTheory.DegAsm.WeightInf
end

