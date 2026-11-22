import Mathlib
import Formalism.HermitianCurvature.StatementTB
import Formalism.HermitianCurvature.LowerBlockNormalisedBoundFromComponents

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveSemidefinitePullback
section
namespace Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback

open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data

open scoped ComplexOrder

noncomputable section

open Classical

theorem sqrt_form_sum_le {n ι : Type} [Fintype n] (M : Matrix n n ℂ) (hM : M.PosSemidef)
    (I : Finset ι) (x : ι → n → ℂ) :
    √(((M *ᵥ (∑ s ∈ I, x s)) ⬝ᵥ star (∑ s ∈ I, x s)).re) ≤
      ∑ s ∈ I, √(((M *ᵥ x s) ⬝ᵥ star (x s)).re) :=
  @norm_sum_le _ _ (M.toSeminormedAddCommGroup hM) I x

def ind {α : Type} (Y A : Finset α) : Y → ℂ := fun p => if (p : α) ∈ A then 1 else 0

theorem sum_mul_ind {α : Type} (Y A : Finset α) (hA : A ⊆ Y) (g : α → ℂ) :
    ∑ q : Y, g q * ind Y A q = ∑ q ∈ A, g q := by
  have h := Finset.sum_coe_sort Y (fun q => g q * (if q ∈ A then (1 : ℂ) else 0))
  simp only [ind]
  rw [h]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hA]

theorem star_ind {α : Type} (Y A : Finset α) : star (ind Y A) = ind Y A := by
  funext p
  simp only [Pi.star_apply, ind]
  split_ifs <;> simp

theorem form_ind {α : Type} (Y A : Finset α) (hA : A ⊆ Y) (k : α → α → ℂ) :
    ((Matrix.of fun x y : Y => k x y) *ᵥ ind Y A) ⬝ᵥ star (ind Y A) = ∑ p ∈ A, ∑ q ∈ A, k p q := by
  rw [star_ind]
  simp only [dotProduct, mulVec, of_apply]
  have h1 : ∀ p : Y, ∑ q : Y, k p q * ind Y A q = ∑ q ∈ A, k p q :=
    fun p => sum_mul_ind Y A hA (fun q => k p q)
  simp only [h1]
  exact sum_mul_ind Y A hA (fun p => ∑ q ∈ A, k p q)

theorem psd_mul {α : Type} {Y : Finset α} {k₁ k₂ : α → α → ℂ} (h₁ : PSDOn Y k₁) (h₂ : PSDOn Y k₂) :
    PSDOn Y (fun p q => k₁ p q * k₂ p q) :=
  Matrix.PosSemidef.hadamard h₁ h₂

theorem psd_pull {α β : Type} {Y : Finset α} (g : α → β) {k : β → β → ℂ}
    (h : PSDOn (Y.image g) k) : PSDOn Y (fun p q => k (g p) (g q)) :=
  Matrix.PosSemidef.submatrix h (fun p : Y => (⟨g p, Finset.mem_image_of_mem g p.2⟩ : Y.image g))

theorem psd_sum_nonneg {α : Type} {Y : Finset α} {k : α → α → ℂ} (h : PSDOn Y k) :
    0 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q).re := by
  rw [← form_ind Y Y (Finset.Subset.refl Y) k, dotProduct_comm]
  exact Matrix.PosSemidef.re_dotProduct_nonneg h _

variable {E W : Type} [Field E]

theorem last_size (T : Tower E) {i : ℕ} (hi : 1 ≤ i) {p : Pt E} (hp : p ∈ T.X i) :
    ∃ s ∈ Icc 1 i, p.getLast?.map Prod.fst = some s := by
  obtain ⟨hl, hb⟩ := (T.isTower i p).1 hp
  rcases List.eq_nil_or_concat p with rfl | ⟨h, b, rfl⟩
  · simp [level] at hl; omega
  · refine ⟨b.1, ?_, by simp⟩
    have h1 : 1 ≤ b.1 := by simpa using (hb h.length (by simp)).1
    have h2 : level (h.concat b) = level h + b.1 := by simp [level]
    rw [Finset.mem_Icc]
    exact ⟨h1, by omega⟩

theorem sum_ind_Xs (T : Tower E) {i : ℕ} (hi : 1 ≤ i) :
    ∑ s ∈ Icc 1 i, ind (T.X i) (Xs T i s) = ind (T.X i) (T.X i) := by
  funext p
  obtain ⟨s, hs, hps⟩ := last_size T hi p.2
  rw [Finset.sum_apply, Finset.sum_eq_single s]
  · have hm : (p : Pt E) ∈ Xs T i s := by
      simp only [Xs, Finset.mem_filter]
      exact ⟨p.2, hps⟩
    simp [ind, hm]
  · intro s' _ hne
    have : (p : Pt E) ∉ Xs T i s' := by
      simp only [Xs, Finset.mem_filter, not_and]
      intro _ h
      rw [hps] at h
      exact hne (Option.some.inj h).symm
    simp [ind, this]
  · intro h; exact absurd hs h

theorem Nst_re (D : Data E W) (ε : ℝ) (i s : ℕ) (w : W) (Y : Finset (Pt E))
    (κ : Pt E → Pt E → ℂ) (t t' : E) :
    (D.Nst ε i s w Y κ t t').re =
      (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * D.gram ε i w (join h s t) (join h' s t')).re / D.wt w := by
  simp only [Data.Nst, Complex.div_ofReal_re]

theorem Nst_nonneg (D : Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε)
    (i s : ℕ) (w : W) (Y : Finset (Pt E)) {κ : Pt E → Pt E → ℂ} (hκ : PSDOn Y κ) (t : E) :
    0 ≤ (D.Nst ε i s w Y κ t t).re := by
  rw [Nst_re]
  refine div_nonneg ?_ (hW w).le
  exact psd_sum_nonneg (psd_mul hκ (psd_pull (fun h => join h s t) (hG ε hε i w _)))

theorem Nst_mono (D : Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε)
    (i s : ℕ) (w : W) (Y : Finset (Pt E)) {κ₁ κ₂ : Pt E → Pt E → ℂ}
    (hκ : PSDOn Y (fun h h' => κ₂ h h' - κ₁ h h')) (t : E) :
    (D.Nst ε i s w Y κ₁ t t).re ≤ (D.Nst ε i s w Y κ₂ t t).re := by
  have h := Nst_nonneg D hG hW hε i s w Y hκ t
  have e : D.Nst ε i s w Y (fun h h' => κ₂ h h' - κ₁ h h') t t =
      D.Nst ε i s w Y κ₂ t t - D.Nst ε i s w Y κ₁ t t := by
    simp only [Data.Nst, sub_mul, Finset.sum_sub_distrib, sub_div]
  rw [e, Complex.sub_re] at h
  linarith

end

end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback

namespace Formalism.FourierDecayAlt.P

open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback

open Classical in
theorem splitByLastSize : Formalism.FourierDecayAlt.TB.SplitBySize := by
  intro E W _ D hG hK T ε hε i hi w
  have hM : PSDOn (T.X i) (fun p q => D.Kr i p q * D.gram ε i w p q) :=
    psd_mul (hK.1 i _) (hG ε hε i w _)
  have h := sqrt_form_sum_le _ hM (Icc 1 i) (fun s => ind (T.X i) (Xs T i s))
  have h2 : ∀ s, Xs T i s ⊆ T.X i := fun s => Finset.filter_subset _ _
  rw [sum_ind_Xs T hi, form_ind (T.X i) (T.X i) (Finset.Subset.refl _)
    (fun p q => D.Kr i p q * D.gram ε i w p q)] at h
  simp only [fun s => form_ind (T.X i) (Xs T i s) (h2 s)
    (fun p q => D.Kr i p q * D.gram ε i w p q)] at h
  exact h

open Classical in
theorem diagStep : Formalism.FourierDecayAlt.TB.DiagStep := by
  intro E W _ D hG hK hW hA T ε hε i s hs hsi hir w R hR
  obtain ⟨_, hdom, hper, _⟩ := hA i s hs hsi hir
  have hY : ∀ h ∈ T.X (i - s), level h = i - s := fun h hh => ((T.isTower _ h).1 hh).1
  have hnn : ∀ t₀ t : E, 0 ≤ (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re :=
    fun t₀ t => Nst_nonneg D hG hW hε i s w _ (hK.2 i s t₀ _) t
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold Data.Dg
  refine Finset.sum_le_sum fun t ht => ?_
  have ht0 : t ≠ 0 := fun h => T.zero_not_mem _ _ (h ▸ ht)
  obtain ⟨t₀, ht₀, hmem⟩ := hR t ht
  have h1 := Nst_mono D hG hW hε i s w (T.X (i - s)) (hdom t ht0 _ hY) t
  rw [hper t t₀ hmem] at h1
  refine h1.trans ?_
  have h2 := Finset.single_le_sum (f := fun t₀ => if t - t₀ ∈ D.La (i - s + 1) s then
      (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re else 0)
    (fun x _ => by
      split_ifs
      · exact hnn x t
      · exact le_refl 0) ht₀
  simpa only [if_pos hmem] using h2

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ScaleThresholdCharacters
section
open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P.ScaleThresholdCharacters

open Formalism.FourierDecayAlt.PairingProductCorollary

theorem corAProduct_ok : CorAProduct := by
  intro n TT IL y q x P QQ hTT hIL hn hq hqpos hx hP hPr
  have hb : 0 < |P (y + 1)| := abs_pos.mpr hP
  have ha : 0 ≤ |P y| := abs_nonneg _
  have hQ0 : 0 ≤ |QQ (y + 1 / 2)| := abs_nonneg _
  have hexp : Real.exp (4 * n / IL) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by rw [div_le_one hIL]; exact hn)
  have hab : |P y| ≤ Real.exp 1 * |P (y + 1)| := by
    have h1 : |P y| / |P (y + 1)| ≤ Real.exp 1 := by rw [← abs_div]; exact hPr.trans hexp
    rwa [div_le_iff₀ hb] at h1
  have hxa : 0 ≤ |x (y + 1)| := abs_nonneg _
  have hxa2 : |x (y + 1)| ^ 2 ≤ |QQ (y + 1 / 2)| := by
    have := pow_le_pow_left₀ hxa hx 2
    rwa [Real.sq_sqrt hQ0] at this
  have hs0 : 0 ≤ TT ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hTT.le _
  have hs2 : (TT ^ (-(1 / 2 : ℝ))) ^ 2 = TT⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTT.le]
    norm_num
    exact Real.rpow_neg_one TT
  have hu2 : Real.sqrt (|P y * P (y + 1)| / q y) ^ 2 = |P y| * |P (y + 1)| / q y := by
    rw [Real.sq_sqrt (by positivity), abs_mul]
  have he2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  rw [abs_mul]
  have hLn : 0 ≤ |x (y + 1)| * |P y| / q y := by positivity
  have hRn : 0 ≤ Real.exp (1 / 2) * Real.sqrt (|P y * P (y + 1)| / q y) * TT ^ (-(1 / 2 : ℝ)) := by
    positivity
  have hQv : |QQ (y + 1 / 2)| = q y / TT := by rw [hq]; field_simp
  have hsq : (|x (y + 1)| * |P y| / q y) ^ 2 ≤
      (Real.exp (1 / 2) * Real.sqrt (|P y * P (y + 1)| / q y) * TT ^ (-(1 / 2 : ℝ))) ^ 2 := by
    have e1 : (|x (y + 1)| * |P y| / q y) ^ 2 = |x (y + 1)| ^ 2 * |P y| ^ 2 / q y ^ 2 := by ring
    have e2 : (Real.exp (1 / 2) * Real.sqrt (|P y * P (y + 1)| / q y) * TT ^ (-(1 / 2 : ℝ))) ^ 2 =
        Real.exp (1 / 2) ^ 2 * Real.sqrt (|P y * P (y + 1)| / q y) ^ 2 * (TT ^ (-(1 / 2 : ℝ))) ^ 2 := by
      ring
    rw [e1, e2, hu2, hs2, he2]
    calc |x (y + 1)| ^ 2 * |P y| ^ 2 / q y ^ 2 ≤ |QQ (y + 1 / 2)| * |P y| ^ 2 / q y ^ 2 := by gcongr
      _ = |P y| ^ 2 / (TT * q y) := by rw [hQv]; field_simp
      _ ≤ Real.exp 1 * |P (y + 1)| * |P y| / (TT * q y) := by gcongr; nlinarith
      _ = Real.exp 1 * (|P y| * |P (y + 1)| / q y) * TT⁻¹ := by field_simp
  nlinarith

theorem corAConstTop_ok : CorAConstTop := by
  have hRZ : ∀ (Rw ZZ BB TT : ℝ), 0 < TT → 0 ≤ Rw → Rw ≤ Real.exp (1 / 2) → 0 ≤ ZZ →
      ZZ ≤ Real.exp (1 / 2) * BB * TT ^ (-(1 / 2 : ℝ)) →
      Rw * ZZ ≤ Real.exp (3 / 2) * (BB * TT ^ (-(1 / 2 : ℝ))) := by
    intro Rw ZZ BB TT hTT hR hR' hZ hZ'
    have hp := Real.exp_pos (1 / 2)
    have hBs : 0 ≤ BB * TT ^ (-(1 / 2 : ℝ)) := by
      have h0 : 0 ≤ Real.exp (1 / 2) * (BB * TT ^ (-(1 / 2 : ℝ))) := by
        rw [← mul_assoc]; exact hZ.trans hZ'
      exact (mul_nonneg_iff_of_pos_left hp).mp h0
    calc Rw * ZZ ≤ Real.exp (1 / 2) * (Real.exp (1 / 2) * (BB * TT ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul hR' (by rw [← mul_assoc]; exact hZ') hZ hp.le
      _ = Real.exp 1 * (BB * TT ^ (-(1 / 2 : ℝ))) := by rw [← mul_assoc, ← Real.exp_add]; norm_num
      _ ≤ Real.exp (3 / 2) * (BB * TT ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by norm_num)) hBs
  refine ⟨?_, ?_⟩
  · intro n ell Rw ZZ BB TT hell hn hTT hR hR' hZ hZ'
    have h := hRZ Rw ZZ BB TT hTT hR hR' hZ hZ'
    calc ((1 / 2) * (4 / ell) ^ n) ^ 2 * Rw * ZZ = (1 / 4) * ((4 / ell) ^ n) ^ 2 * (Rw * ZZ) := by ring
      _ ≤ (1 / 4) * ((4 / ell) ^ n) ^ 2 * (Real.exp (3 / 2) * (BB * TT ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Real.exp (3 / 2) * (1 / 4) * (4 / ell) ^ (2 * n) * BB * TT ^ (-(1 / 2 : ℝ)) := by
          rw [show 2 * n = n * 2 by ring, pow_mul]; ring
  · intro Rw ZZ BB TT hTT hR hR' hZ hZ'
    have h := hRZ Rw ZZ BB TT hTT hR hR' hZ hZ'
    linarith [h, show Real.exp (3 / 2) * (BB * TT ^ (-(1 / 2 : ℝ))) =
      Real.exp (3 / 2) * BB * TT ^ (-(1 / 2 : ℝ)) by ring]

theorem scaleThresholds_ok : ScaleThresholds := by
  intro ka ell sb TT i s r hka hell hTT hi
  have e : ∀ m : ℕ, (4 * ka / ell) ^ m = (4 / ell) ^ m * ka ^ m := fun m => by rw [← mul_pow]; ring
  have key1 : ka ^ ((2 * i : ℤ) - 3) * ka = ka ^ (2 * i - 2) := by
    rw [← zpow_add_one₀ hka.ne', ← zpow_natCast]; congr 1; omega
  have key2 : ka ^ ((2 * i + s : ℤ) - 3) * ka = ka ^ (2 * (i - 1) + s) := by
    rw [← zpow_add_one₀ hka.ne', ← zpow_natCast]; congr 1; omega
  have k3 : (ka ^ (4 * r)) ^ (-(1 / 2 : ℝ)) = (ka ^ (2 * r))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, show 4 * r = 2 * r * 2 by ring, pow_mul,
      Real.sqrt_sq (by positivity)]
  have key3 : ka ^ (2 * (i + r - 1)) * ka = ka ^ (2 * i - 1) * ka ^ (2 * r) := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  have hk2 : ka ^ (2 * r) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    linear_combination (Real.exp (1 / 4) * (1 / 2) * (4 / ell) ^ (2 * i - 2) * sb) * key1
  · rw [e]
    linear_combination (Real.exp (1 / 4) * (1 / 2) * (4 / ell) ^ (2 * (i - 1) + s) * sb) * key2
  · rw [Real.mul_rpow (by positivity) hTT.le, k3]
    have hinv := mul_inv_cancel₀ hk2
    linear_combination (Real.exp (3 / 2) * (1 / 4) * (4 / ell) ^ (2 * (i - 1)) * sb *
      TT ^ (-(1 / 2 : ℝ)) * (ka ^ (2 * r))⁻¹) * key3 +
      (Real.exp (3 / 2) * (1 / 4) * (4 / ell) ^ (2 * (i - 1)) * sb * TT ^ (-(1 / 2 : ℝ)) *
        ka ^ (2 * i - 1)) * hinv

theorem scaleThresholdsOne_ok : ScaleThresholdsOne := by
  intro ka sb TT r hka hTT
  have k3 : (ka ^ (4 * r)) ^ (-(1 / 2 : ℝ)) = (ka ^ (2 * r))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, show 4 * r = 2 * r * 2 by ring, pow_mul,
      Real.sqrt_sq (by positivity)]
  have hk2 : ka ^ (2 * r) ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · rw [zpow_neg_one]
    field_simp
  · rw [Real.mul_rpow (by positivity) hTT.le, k3]
    field_simp

theorem scaleThresholdsBelow_ok : ScaleThresholdsBelow := by
  intro ka ell sb TT N IL m i hka hell hN hIL hsb hTT hle
  have h4 : 4 / ell ≤ 28 * N / IL := by
    rw [div_le_div_iff₀ hell hIL]
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 7 * N)).mp hle
    nlinarith
  have hE1 : Real.exp (1 / 4) / 2 ≤ 1 := by
    have h4e : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    have hlt := Real.exp_one_lt_d9
    have hpos := Real.exp_pos (1 / 4)
    by_contra hc
    have hc' : 2 < Real.exp (1 / 4) := by linarith [not_le.mp hc]
    have h16 : (2:ℝ) ^ 4 < Real.exp (1 / 4) ^ 4 := pow_lt_pow_left₀ hc' (by norm_num) (by norm_num)
    norm_num at h16
    linarith
  have hE2 : Real.exp (3 / 2) / 4 ≤ 2 := by
    have h2e : Real.exp (3 / 2) ^ 2 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have hlt := Real.exp_one_lt_d9
    have hpos := Real.exp_pos 1
    have hpos' := Real.exp_pos (3 / 2)
    by_contra hc
    have hc' : 8 < Real.exp (3 / 2) := by linarith [not_le.mp hc]
    have h64 : (8:ℝ) ^ 2 < Real.exp (3 / 2) ^ 2 := pow_lt_pow_left₀ hc' (by norm_num) (by norm_num)
    have h3 : Real.exp 1 ^ 3 < 3 ^ 3 := pow_lt_pow_left₀ (by linarith) hpos.le (by norm_num)
    rw [h2e] at h64
    norm_num at h64 h3
    linarith
  refine ⟨?_, ?_⟩
  · have hX : (4 * ka / ell) ^ m ≤ (28 * ka * N / IL) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      rw [show 4 * ka / ell = ka * (4 / ell) by ring, show 28 * ka * N / IL = ka * (28 * N / IL) by ring]
      exact mul_le_mul_of_nonneg_left h4 hka.le
    calc Real.exp (1 / 4) / 2 * sb * (4 * ka / ell) ^ m ≤ Real.exp (1 / 4) / 2 * sb * (28 * ka * N / IL) ^ m :=
          mul_le_mul_of_nonneg_left hX (mul_nonneg (by positivity) hsb)
      _ ≤ 1 * sb * (28 * ka * N / IL) ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE1 hsb) (by positivity)
      _ = sb * (28 * ka * N / IL) ^ m := by ring
  · have hA : (4 / ell) ^ (2 * (i - 1)) ≤ (28 * N / IL) ^ (2 * (i - 1)) :=
      pow_le_pow_left₀ (by positivity) h4 _
    have hC : 0 ≤ sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg hsb (by positivity)) (Real.rpow_nonneg hTT.le _)
    calc Real.exp (3 / 2) / 4 * sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ)) * (4 / ell) ^ (2 * (i - 1))
        = (Real.exp (3 / 2) / 4) * (sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ))) *
            (4 / ell) ^ (2 * (i - 1)) := by ring
      _ ≤ 2 * (sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ))) * (28 * N / IL) ^ (2 * (i - 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hE2 hC) hA (by positivity) (mul_nonneg (by norm_num) hC)
      _ = 2 * sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ)) * (28 * N / IL) ^ (2 * (i - 1)) := by ring

theorem scaleCharacter_ok : ScaleCharacter := by
  intro ka i l c hka hi
  have hk : (ka : ℂ) ≠ 0 := by exact_mod_cast hka.ne'
  have he : (3 - 2 * (i : ℤ)) + ((2 * i - 2 : ℕ) : ℤ) = 1 := by omega
  have h1 : (ka : ℂ) ^ (3 - 2 * (i : ℤ)) * (ka : ℂ) ^ (2 * i - 2) = ka := by
    rw [← zpow_natCast, ← zpow_add₀ hk, he, zpow_one]
  have h2 : (ka : ℂ) ^ (3 - 2 * (i : ℤ)) * l * ((ka : ℂ) ^ (2 * i - 2) * c) = (ka : ℂ) * (l * c) := by
    calc (ka : ℂ) ^ (3 - 2 * (i : ℤ)) * l * ((ka : ℂ) ^ (2 * i - 2) * c)
        = ((ka : ℂ) ^ (3 - 2 * (i : ℤ)) * (ka : ℂ) ^ (2 * i - 2)) * (l * c) := by ring
      _ = (ka : ℂ) * (l * c) := by rw [h1]
  rw [h2]
  congr 1
  simp only [map_mul, Complex.conj_ofReal]
  ring

end Formalism.FourierDecayAlt.P.ScaleThresholdCharacters

theorem Formalism.FourierDecayAlt.P.constant_product_corollary : Formalism.FourierDecayAlt.PairingProductCorollary.CorAProduct := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.corAProduct_ok
theorem Formalism.FourierDecayAlt.P.constant_top_corollary : Formalism.FourierDecayAlt.PairingProductCorollary.CorAConstTop := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.corAConstTop_ok
theorem Formalism.FourierDecayAlt.P.scale_thresholds_estimate : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleThresholds := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholds_ok
theorem Formalism.FourierDecayAlt.P.scale_thresholds_at_one : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleThresholdsOne := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholdsOne_ok
theorem Formalism.FourierDecayAlt.P.pairing_product_scale_bounds_below : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleThresholdsBelow := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholdsBelow_ok
theorem Formalism.FourierDecayAlt.P.scale_character_identity : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleCharacter := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleCharacter_ok

end
end

