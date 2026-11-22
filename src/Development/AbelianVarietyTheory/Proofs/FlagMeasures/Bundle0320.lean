import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0209
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaProductGaugeSandwichNearOne
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwSand

theorem exists_le_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] (f g : V → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hfs : ∀ s : ℝ, 0 ≤ s → ∀ v, f (s • v) = s * f v)
    (hgs : ∀ s : ℝ, 0 ≤ s → ∀ v, g (s • v) = s * g v) (hg0 : ∀ v, 0 ≤ g v) (hd : ∀ v, g v = 0 → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v, f v ≤ C * g v := by
  have hf0 : f 0 = 0 := by simpa using hfs 0 le_rfl 0
  have hg0' : g 0 = 0 := by simpa using hgs 0 le_rfl 0
  rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := by
      by_contra hv
      have hmem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
        simp [norm_smul, hv]
      rw [hS] at hmem
      exact hmem
    subst hv
    simp [hf0, hg0']
  · have hK := isCompact_sphere (0 : V) 1
    obtain ⟨u0, hu0, hmin⟩ := hK.exists_isMinOn hS hg.continuousOn
    obtain ⟨u1, -, hmax⟩ := hK.exists_isMaxOn hS hf.continuousOn
    have hm : 0 < g u0 := by
      rcases (hg0 u0).lt_or_eq with h | h
      · exact h
      · exfalso
        have h0 := hd u0 h.symm
        subst h0
        simp at hu0
    refine ⟨max (f u1) 0 / g u0 + 1, by positivity, fun v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp [hf0, hg0']
    have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
      simp [norm_smul, hr.ne']
    have hvw : v = ‖v‖ • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hfv : f v = ‖v‖ * f (‖v‖⁻¹ • v) := by
      conv_lhs => rw [hvw]
      exact hfs _ hr.le _
    have hgv : g v = ‖v‖ * g (‖v‖⁻¹ • v) := by
      conv_lhs => rw [hvw]
      exact hgs _ hr.le _
    have h1 : f (‖v‖⁻¹ • v) ≤ f u1 := isMaxOn_iff.mp hmax _ hw
    have h2 : g u0 ≤ g (‖v‖⁻¹ • v) := isMinOn_iff.mp hmin _ hw
    have hgw : 0 ≤ g (‖v‖⁻¹ • v) := hg0 _
    rw [hfv, hgv]
    calc ‖v‖ * f (‖v‖⁻¹ • v) ≤ ‖v‖ * max (f u1) 0 :=
          mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) hr.le
      _ = max (f u1) 0 / g u0 * (‖v‖ * g u0) := by field_simp
      _ ≤ max (f u1) 0 / g u0 * (‖v‖ * g (‖v‖⁻¹ • v)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hr.le) (by positivity)
      _ ≤ (max (f u1) 0 / g u0 + 1) * (‖v‖ * g (‖v‖⁻¹ • v)) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hr.le hgw)

variable {n : ℕ}

theorem nrm_le_add_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : nrm X ≤ nrm Y + nrm (X - Y) := by
  have h := nrm_add_le Y (X - Y)
  rwa [add_sub_cancel] at h

theorem abs_nrm_sub_le (X Y : Matrix (Fin n) (Fin n) ℂ) : |nrm X - nrm Y| ≤ nrm (X - Y) := by
  have h1 := nrm_le_add_sub X Y
  have h2 := nrm_le_add_sub Y X
  have h3 : nrm (Y - X) = nrm (X - Y) := by rw [← neg_sub, nrm_neg]
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem abs_len_sub_le {d : ℕ} (x y : Fin d → ℝ) : |len x - len y| ≤ len (x - y) := by
  have h1 : len x ≤ len y + len (x - y) := by
    have h := len_add_le y (x - y)
    rwa [add_sub_cancel] at h
  have h2 : len y ≤ len x + len (y - x) := by
    have h := len_add_le x (y - x)
    rwa [add_sub_cancel] at h
  have h3 : len (y - x) = len (x - y) := by rw [← neg_sub, len_neg]
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem nrm_prod_sub_le (a b c X Y Z : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (hs1 : s ≤ 1) (ha : nrm (a - 1) ≤ s)
    (hb : nrm (b - 1) ≤ s) (hc : nrm (c - 1) ≤ s) (hX : nrm (a - 1 - X) ≤ s ^ 2) (hY : nrm (b - 1 - Y) ≤ s ^ 2)
    (hZ : nrm (c - 1 - Z) ≤ s ^ 2) : nrm (a * b * c - 1 - (X + Y + Z)) ≤ 7 * s ^ 2 := by
  have hs0 : 0 ≤ s := (nrm_nonneg _).trans ha
  have key : a * b * c - 1 - (X + Y + Z) =
      ((a - 1 - X) + (b - 1 - Y) + (c - 1 - Z)) +
        ((a - 1) * (b - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1)) + (a - 1) * (b - 1) * (c - 1) := by
    noncomm_ring
  have pr2 : ∀ P Q : Matrix (Fin n) (Fin n) ℂ, nrm P ≤ s → nrm Q ≤ s → nrm (P * Q) ≤ s ^ 2 := by
    intro P Q hP hQ
    calc nrm (P * Q) ≤ nrm P * nrm Q := nrm_mul_le _ _
      _ ≤ s * s := mul_le_mul hP hQ (nrm_nonneg _) hs0
      _ = s ^ 2 := (sq s).symm
  have e1 : nrm ((a - 1 - X) + (b - 1 - Y) + (c - 1 - Z)) ≤ 3 * s ^ 2 := by
    have := nrm_add_le ((a - 1 - X) + (b - 1 - Y)) (c - 1 - Z)
    have := nrm_add_le (a - 1 - X) (b - 1 - Y)
    linarith
  have e2 : nrm ((a - 1) * (b - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1)) ≤ 3 * s ^ 2 := by
    have := nrm_add_le ((a - 1) * (b - 1) + (a - 1) * (c - 1)) ((b - 1) * (c - 1))
    have := nrm_add_le ((a - 1) * (b - 1)) ((a - 1) * (c - 1))
    have := pr2 _ _ ha hb
    have := pr2 _ _ ha hc
    have := pr2 _ _ hb hc
    linarith
  have e3 : nrm ((a - 1) * (b - 1) * (c - 1)) ≤ s ^ 2 := by
    calc nrm ((a - 1) * (b - 1) * (c - 1)) ≤ nrm ((a - 1) * (b - 1)) * nrm (c - 1) := nrm_mul_le _ _
      _ ≤ s ^ 2 * s := mul_le_mul (pr2 _ _ ha hb) hc (nrm_nonneg _) (sq_nonneg _)
      _ ≤ s ^ 2 * 1 := mul_le_mul_of_nonneg_left hs1 (sq_nonneg _)
      _ = s ^ 2 := mul_one _
  rw [key]
  have := nrm_add_le (((a - 1 - X) + (b - 1 - Y) + (c - 1 - Z)) +
        ((a - 1) * (b - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1))) ((a - 1) * (b - 1) * (c - 1))
  have := nrm_add_le ((a - 1 - X) + (b - 1 - Y) + (c - 1 - Z))
        ((a - 1) * (b - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1))
  linarith

theorem real_sandwich {C η s σ γ : ℝ} (hC : 0 < C) (hη : 0 < η) (hγ : 0 ≤ γ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2)
    (hs' : s ≤ η / (1 + η) / (14 * C)) (h1 : s ≤ C * γ + s ^ 2) (h2 : |σ - γ| ≤ 7 * s ^ 2) :
    γ ≤ (1 + η) * σ ∧ σ ≤ (1 + η) * γ ∧ s ≤ 2 * C * γ := by
  have hδη : η / (1 + η) ≤ η := div_le_self hη.le (by linarith)
  have hδ : η / (1 + η) * (1 + η) = η := div_mul_cancel₀ η (by positivity)
  have h3 : s ≤ 2 * C * γ := by nlinarith [mul_nonneg hs0 (sub_nonneg.2 hs)]
  have h4 : s * (14 * C) ≤ η / (1 + η) := by
    rwa [le_div_iff₀ (by positivity)] at hs'
  have h5 : 7 * s ^ 2 ≤ η / (1 + η) * γ := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hs0, mul_le_mul_of_nonneg_right h4 hγ]
  obtain ⟨hl, hr⟩ := abs_le.mp h2
  refine ⟨?_, ?_, h3⟩
  · have hpos : 0 ≤ (1 + η) * (σ - γ + η / (1 + η) * γ) :=
      mul_nonneg (by linarith) (by linarith)
    have hδγ : η / (1 + η) * (1 + η) * γ = η * γ := by rw [hδ]
    nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right hδη hγ]

theorem gau_sandwich : ∀ (n : ℕ) (ε : Fin n → Bool) (SN SM MainNotions : Set (Formalism.REAL.UJ ε)), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε SN EN → IsCut ε SM EM → IsCut ε MainNotions EK → IsON EL → (∀ v, gau EN EM EK EL v = 0 → v = 0) → ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ u ∈ SN, ∀ m ∈ SM, ∀ k ∈ MainNotions, nrm (uMat u - 1) < t → nrm (uMat m - 1) < t → nrm (uMat k - 1) < t → ∀ σ γ : ℝ, σ = max (nrm (uMat (u * m * k) - 1)) (len (crd EL (uMat k - 1))) → γ = gau EN EM EK EL (crd EN (uMat u - 1), crd EM (uMat m - 1), crd EK (uMat k - 1)) → γ ≤ (1 + η) * σ ∧ σ ≤ (1 + η) * γ ∧ nrm (uMat u - 1) ≤ C * γ ∧ nrm (uMat m - 1) ≤ C * γ ∧ nrm (uMat k - 1) ≤ C * γ := by
  intro n ε SN SM MainNotions dN dM dK dL EN EM EK EL hN hM hK hL hdef
  obtain ⟨C0, hC0, hC0le⟩ := exists_le_mul
    (fun v : (Fin dN → ℝ) × (Fin dM → ℝ) × (Fin dK → ℝ) => max (len v.1) (max (len v.2.1) (len v.2.2)))
    (gau EN EM EK EL)
    ((continuous_len.comp continuous_fst).max ((continuous_len.comp (continuous_fst.comp continuous_snd)).max
      (continuous_len.comp (continuous_snd.comp continuous_snd))))
    (continuous_gau EN EM EK EL)
    (by
      intro s hs v
      simp only [Prod.smul_fst, Prod.smul_snd, len_smul, abs_of_nonneg hs]
      rw [mul_max_of_nonneg _ _ hs, mul_max_of_nonneg _ _ hs])
    (fun s hs v => gau_smul EN EM EK EL s hs v) (gau_nonneg EN EM EK EL) hdef
  refine ⟨2 * C0, by positivity, fun η hη => ?_⟩
  refine ⟨min (1 / 2) (η / (1 + η) / (14 * C0)), lt_min (by norm_num) (by positivity), ?_⟩
  intro u hu m hm k hk hut hmt hkt σ γ hσ hγ
  set s := max (nrm (uMat u - 1)) (max (nrm (uMat m - 1)) (nrm (uMat k - 1))) with hs_def
  have hst : s < min (1 / 2) (η / (1 + η) / (14 * C0)) := max_lt hut (max_lt hmt hkt)
  have hs12 : s ≤ 1 / 2 := (hst.trans_le (min_le_left _ _)).le
  have hsη : s ≤ η / (1 + η) / (14 * C0) := (hst.trans_le (min_le_right _ _)).le
  have hsu : nrm (uMat u - 1) ≤ s := le_max_left _ _
  have hsm : nrm (uMat m - 1) ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hsk : nrm (uMat k - 1) ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  have hs0 : 0 ≤ s := (nrm_nonneg _).trans hsu
  have hs2 : ∀ x : ℝ, 0 ≤ x → x ≤ s → x ^ 2 ≤ s ^ 2 := fun x hx hxs => pow_le_pow_left₀ hx hxs 2

  have aN := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε SN dN EN hN u hu
  have aM := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε SM dM EM hM m hm
  have aK := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε MainNotions dK EK hK k hk
  set X := cmb EN (crd EN (uMat u - 1))
  set Y := cmb EM (crd EM (uMat m - 1))
  set Z := cmb EK (crd EK (uMat k - 1))
  have aN' : nrm (uMat u - 1 - X) ≤ s ^ 2 := aN.trans (hs2 _ (nrm_nonneg _) hsu)
  have aM' : nrm (uMat m - 1 - Y) ≤ s ^ 2 := aM.trans (hs2 _ (nrm_nonneg _) hsm)
  have aK' : nrm (uMat k - 1 - Z) ≤ s ^ 2 := aK.trans (hs2 _ (nrm_nonneg _) hsk)
  have hmul : uMat (u * m * k) = uMat u * uMat m * uMat k := by
    simp [uMat]
  have hprod : nrm (uMat (u * m * k) - 1 - (X + Y + Z)) ≤ 7 * s ^ 2 := by
    rw [hmul]
    exact nrm_prod_sub_le _ _ _ X Y Z s (by linarith) hsu hsm hsk aN' aM' aK'
  have hγ' : γ = max (nrm (X + Y + Z)) (len (crd EL Z)) := by
    rw [hγ]; rfl
  have d1 : |nrm (uMat (u * m * k) - 1) - nrm (X + Y + Z)| ≤ 7 * s ^ 2 :=
    (abs_nrm_sub_le _ _).trans hprod
  have d2 : |len (crd EL (uMat k - 1)) - len (crd EL Z)| ≤ 7 * s ^ 2 := by
    refine (abs_len_sub_le _ _).trans ?_
    rw [← crd_sub]
    refine (len_crd_le hL _).trans ?_
    nlinarith [sq_nonneg s]
  have hσγ : |σ - γ| ≤ 7 * s ^ 2 := by
    rw [hσ, hγ']
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le d1 d2)

  have hγ0 : 0 ≤ γ := by rw [hγ]; exact gau_nonneg _ _ _ _ _
  have hbound := hC0le (crd EN (uMat u - 1), crd EM (uMat m - 1), crd EK (uMat k - 1))
  rw [← hγ] at hbound
  have lN : len (crd EN (uMat u - 1)) ≤ C0 * γ := (le_max_left _ _).trans hbound
  have lM : len (crd EM (uMat m - 1)) ≤ C0 * γ := ((le_max_left _ _).trans (le_max_right _ _)).trans hbound
  have lK : len (crd EK (uMat k - 1)) ≤ C0 * γ := ((le_max_right _ _).trans (le_max_right _ _)).trans hbound
  have near : ∀ {d : ℕ} (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin n) ℂ), IsON E →
      len (crd E W) ≤ C0 * γ → nrm (W - cmb E (crd E W)) ≤ s ^ 2 → nrm W ≤ C0 * γ + s ^ 2 := by
    intro d E W hE h1 h2
    have h3 := nrm_le_add_sub W (cmb E (crd E W))
    rw [nrm_cmb hE] at h3
    linarith
  have bN := near EN _ hN.isON lN aN'
  have bM := near EM _ hM.isON lM aM'
  have bK := near EK _ hK.isON lK aK'
  have h1 : s ≤ C0 * γ + s ^ 2 := max_le bN (max_le bM bK)
  obtain ⟨r1, r2, r3⟩ := real_sandwich hC0 hη hγ0 hs0 hs12 hsη h1 hσγ
  refine ⟨r1, r2, ?_, ?_, ?_⟩ <;> linarith

end GlobalTheory.IwSand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaSlabSqueezedBetweenBalls
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem slab_arith_lower {a s r t η u v : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hst : s < t) (hrt : r < t)
    (ht : t ≤ 1 / 24) (hη : 0 < η) (htη : 3 * t * (1 + η) ≤ η) (h1 : a < 1 / 8 + s + a * s)
    (h2 : a ≤ u + a ^ 2) (h3 : u ≤ v + a * s) (h4 : v ≤ r) : a ≤ (1 + η) * r := by

  have hs24 : s < 1 / 24 := lt_of_lt_of_le hst ht
  have hA : a < 4 / 23 := by nlinarith [mul_nonneg ha (sub_nonneg.2 hs24.le)]
  have hkey : a * (1 - s - a) ≤ r := by nlinarith
  have hgap : 433 / 552 ≤ 1 - s - a := by linarith
  have hat : a * (433 / 552) < t := by nlinarith [mul_le_mul_of_nonneg_left hgap ha]
  have hsum : (1 + η) * (s + a) ≤ η := by
    nlinarith [mul_le_mul_of_nonneg_left (show s + a ≤ 3 * t by linarith) (show (0 : ℝ) ≤ 1 + η by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ 1 + η by linarith),
    mul_le_mul_of_nonneg_left hsum ha]

theorem slab_squeeze : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η →
    ∃ t : ℝ, 0 < t ∧ ∀ r : ℝ, 0 < r → r < t → ∀ k : Formalism.REAL.UJ ε, nrm (uMat k - 1) < t →
      crd E (uMat k - 1) = 0 → ∀ l ∈ S, (l ∈ hsBall ε (r / (1 + η)) → l * k ∈ slab ε E ρ r) ∧
        (l * k ∈ slab ε E ρ r → l ∈ hsBall ε ((1 + η) * r)) := by
  intro n ε S d E hS ρ η hρ hρ8 hη
  have hON := hS.isON
  obtain ⟨t, ht0, ht24, htη, htρ⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 24 ∧ 3 * t * (1 + η) ≤ η ∧ 3 * t ≤ ρ := by
    refine ⟨min (1 / 24) (min (η / (3 * (1 + η))) (ρ / 3)),
      lt_min (by norm_num) (lt_min (by positivity) (by positivity)), min_le_left _ _, ?_, ?_⟩
    · have h : min (1 / 24) (min (η / (3 * (1 + η))) (ρ / 3)) * (3 * (1 + η)) ≤ η :=
        (le_div_iff₀ (by positivity)).1 (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    · have h := le_trans (min_le_right (1 / 24 : ℝ) _) (min_le_right (η / (3 * (1 + η))) (ρ / 3))
      linarith
  refine ⟨t, ht0, ?_⟩
  intro r hr hrt k hk hk0 l hl

  have hmul : uMat (l * k) - 1 = (uMat l - 1) + (uMat k - 1) + (uMat l - 1) * (uMat k - 1) := by
    have e : uMat (l * k) = uMat l * uMat k := rfl
    rw [e]; noncomm_ring
  have hXY : nrm ((uMat l - 1) * (uMat k - 1)) ≤ nrm (uMat l - 1) * nrm (uMat k - 1) := nrm_mul_le _ _
  have ha0 := nrm_nonneg (uMat l - 1)
  have hs0 := nrm_nonneg (uMat k - 1)
  have htle : t ≤ η := by nlinarith
  constructor
  · intro hlB
    have ha : nrm (uMat l - 1) ≤ r / (1 + η) := hlB
    have ha' : nrm (uMat l - 1) * (1 + η) ≤ r := (le_div_iff₀ (by positivity)).1 ha
    refine ⟨?_, ?_⟩
    ·
      have h1 : nrm (uMat (l * k) - 1) ≤ nrm (uMat l - 1) + nrm (uMat k - 1) + nrm ((uMat l - 1) * (uMat k - 1)) := by
        rw [hmul]
        exact le_trans (nrm_add_le _ _) (by linarith [nrm_add_le (uMat l - 1) (uMat k - 1)])
      have hat : nrm (uMat l - 1) < t := by nlinarith
      have hprod : nrm (uMat l - 1) * nrm (uMat k - 1) ≤ t * t := by
        exact mul_le_mul hat.le hk.le hs0 ht0.le
      nlinarith
    ·
      have hc : crd E (uMat (l * k) - 1) = crd E (uMat l - 1) + crd E ((uMat l - 1) * (uMat k - 1)) := by
        rw [hmul, crd_add, crd_add, hk0, add_zero]
      have hlen : len (crd E (uMat (l * k) - 1)) ≤ nrm (uMat l - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
        rw [hc]
        exact le_trans (len_add_le _ _)
          (add_le_add (len_crd_le hON _) (le_trans (len_crd_le hON _) hXY))
      have hsη : nrm (uMat l - 1) * nrm (uMat k - 1) ≤ nrm (uMat l - 1) * η :=
        mul_le_mul_of_nonneg_left (by linarith) ha0
      show len (crd E (uMat (l * k) - 1)) ≤ r
      nlinarith
  · intro hslab
    obtain ⟨hZ, hv⟩ := hslab
    show nrm (uMat l - 1) ≤ (1 + η) * r
    have hX : uMat l - 1 = (uMat (l * k) - 1) - (uMat k - 1) - (uMat l - 1) * (uMat k - 1) := by
      rw [hmul]; abel

    have h1 : nrm (uMat l - 1) < 1 / 8 + nrm (uMat k - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
      have e := nrm_sub_le ((uMat (l * k) - 1) - (uMat k - 1)) ((uMat l - 1) * (uMat k - 1))
      have e' := nrm_sub_le (uMat (l * k) - 1) (uMat k - 1)
      rw [← hX] at e
      linarith

    have h2 : nrm (uMat l - 1) ≤ len (crd E (uMat l - 1)) + nrm (uMat l - 1) ^ 2 := by
      have hp := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε S d E hS l hl
      have e := nrm_add_le (cmb E (crd E (uMat l - 1))) (uMat l - 1 - cmb E (crd E (uMat l - 1)))
      rw [add_sub_cancel, nrm_cmb hON] at e
      linarith

    have h3 : len (crd E (uMat l - 1)) ≤ len (crd E (uMat (l * k) - 1)) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
      have hc : crd E (uMat l - 1) = crd E (uMat (l * k) - 1) + -crd E ((uMat l - 1) * (uMat k - 1)) := by
        conv_lhs => rw [hX]
        rw [crd_sub, crd_sub, hk0, sub_zero, sub_eq_add_neg]
      rw [hc]
      refine le_trans (len_add_le _ _) (add_le_add le_rfl ?_)
      rw [len_neg]
      exact le_trans (len_crd_le hON _) hXY
    exact slab_arith_lower ha0 hs0 hk hrt ht24 hη htη (by linarith) h2 h3 hv

end GlobalTheory.IwConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeSpanEInfToO
section
open NumberField

namespace GlobalTheory.SpanInfDenominators

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (Λ : Submodule (𝓞 E) V) (x : V)
    (hx : x ∈ Submodule.span E (Λ : Set V)) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • x ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, hcy⟩ := hy
    obtain ⟨c', hc', hcz⟩ := hz
    refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
    have e1 : (c * c') • y = c' • (c • y) := by rw [mul_comm, mul_smul]
    have e2 : (c * c') • z = c • (c' • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact Λ.add_mem (Λ.smul_mem _ hcy) (Λ.smul_mem _ hcz)
  | smul a y _ hy =>
    obtain ⟨c, hc, hcy⟩ := hy
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) a
    have hd : (d : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero d.2
    refine ⟨(d : 𝓞 E) * c, mul_ne_zero hd hc, ?_⟩
    have key : ((d : 𝓞 E) * c) • (a • y) = n • (c • y) := by
      rw [← algebraMap_smul E ((d : 𝓞 E) * c) (a • y), ← algebraMap_smul E n (c • y),
        ← algebraMap_smul E c y, smul_smul, smul_smul, map_mul]
      congr 1
      rw [← hnd]
      ring
    rw [key]
    exact Λ.smul_mem n hcy

theorem le_spanE_inf_toO {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (U : Submodule E S.V) :
    U ≤ Formalism.MainNotions.S.Lat.spanE S (Λ ⊓ Formalism.MainNotions.S.Lat.toO S U) := by
  intro x hx
  have hxs : x ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hΛ.span_eq_top]
    trivial
  obtain ⟨c, hc, hcx⟩ := exists_smul_mem Λ x hxs
  have hcU : c • x ∈ U := by
    rw [← algebraMap_smul E c x]
    exact U.smul_mem _ hx
  have hmem : c • x ∈ Λ ⊓ Formalism.MainNotions.S.Lat.toO S U := Submodule.mem_inf.2 ⟨hcx, hcU⟩
  have hc' : algebraMap (𝓞 E) E c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
  have hx' : x = (algebraMap (𝓞 E) E c)⁻¹ • (c • x) := by
    rw [← algebraMap_smul E c x, smul_smul, inv_mul_cancel₀ hc', one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.SpanInfDenominators
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralLeSumTypes
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.TypeDecomp

theorem lintegral_biUnion_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (A : ι → Set α) (f : α → ENNReal) :
    ∫⁻ x in ⋃ i ∈ s, A i, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in A i, f x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hb]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

theorem hasType_cast (I : AutInst) (x : I.GA) {a a' : ℕ} (h : a' = a) (j : Fin a → ℕ) (τ : Fin a → ℝ)
    (H : HasType I x j τ) : ∃ τ', HasType I x (fun i : Fin a' => j (Fin.cast h i)) τ' := by
  subst h
  exact ⟨τ, H⟩

theorem sum_diff (a : ℕ) (r : Fin (a + 1) → ℕ) (j : Fin a → ℕ)
    (h : ∀ i, r i.succ = r i.castSucc + j i) : r (Fin.last a) = r 0 + ∑ i, j i := by
  induction a with
  | zero => simp
  | succ a ih =>
    have key := ih (fun i => r i.castSucc) (fun i => j i.castSucc) (fun i => by
      have := h i.castSucc
      rwa [Fin.succ_castSucc] at this)
    have hl := h (Fin.last a)
    rw [Fin.succ_last] at hl
    simp only [Fin.castSucc_zero] at key
    rw [Fin.sum_univ_castSucc, hl, key]
    ring

theorem exists_type (B : RowsAut) (p q : ℕ) (hs : SigIs B p q) (hn : 1 ≤ B.I.n) (x : B.I.GA)
    (hx : least B.I x < 1 / 2) :
    ∃ J ∈ Finset.Icc 1 q, ∃ c : Composition J, ∃ τ, HasType B.I x c.blocksFun τ := by
  obtain ⟨⟨a, S, τ, hF⟩, -, hprop⟩ := GlobalTheory.PointFlag.flag_spec B.I x
  obtain ⟨hsteps, hlast⟩ := hprop a S τ hF
  have hlt : ∀ i : Fin a, Formalism.HN.rkK (S i.castSucc) < Formalism.HN.rkK (S i.succ) := fun i => (hsteps i).2.1
  set j : Fin a → ℕ := fun i => Formalism.HN.rkK (S i.succ) - Formalism.HN.rkK (S i.castSucc) with hj
  have hstep : ∀ i, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i := fun i => by
    have := hlt i
    simp only [hj]
    omega
  have hjpos : ∀ i, 0 < j i := fun i => by
    have := hlt i
    simp only [hj]
    omega
  have hT : HasType B.I x j τ := ⟨S, hF, hstep⟩
  have hsum : Formalism.HN.rkK (S (Fin.last a)) = Formalism.HN.rkK (S 0) + ∑ i, j i :=
    GlobalTheory.TypeDecomp.sum_diff a (fun i => Formalism.HN.rkK (S i)) j hstep
  have ha : a ≠ 0 := by
    intro h0
    have := (hlast hn).1.mp h0
    linarith
  obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
  have hiso : Formalism.HN.rkK (stepLt B.I x (1 / 2)) ≤ rkR (B.I.ε v) := (GlobalTheory.FlagIso.flag_isotropic B.I x).2.1 v
  have hq : rkR (B.I.ε v) ≤ q := (min_le_right _ _).trans (hs v).2.le
  have hSl : S (Fin.last a) = stepLt B.I x (1 / 2) := hF.2.2.1
  have h1 : 1 ≤ ∑ i, j i := by
    have := Finset.single_le_sum (f := j) (fun i _ => Nat.zero_le _) (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero ha⟩)
    have := hjpos ⟨0, Nat.pos_of_ne_zero ha⟩
    omega
  have h2 : ∑ i, j i ≤ q := by
    rw [hSl] at hsum
    omega
  let c : Composition (∑ i, j i) :=
    ⟨List.ofFn j, fun {b} hb => by
      simp only [List.mem_ofFn, Set.mem_range] at hb
      obtain ⟨k, rfl⟩ := hb
      exact hjpos k, by simp [List.sum_ofFn]⟩
  have hlen : c.length = a := by simp [c, Composition.length]
  have hc : c.blocksFun = fun i => j (Fin.cast hlen i) := by
    funext i
    show (List.ofFn j).get i = j (Fin.cast hlen i)
    first
      | rw [List.get_ofFn]
      | simp [List.get_eq_getElem, Fin.cast]
  obtain ⟨τ', h'⟩ := GlobalTheory.TypeDecomp.hasType_cast B.I x hlen j τ hT
  refine ⟨∑ i, j i, Finset.mem_Icc.mpr ⟨h1, h2⟩, c, τ', ?_⟩
  rw [hc]
  exact h'

theorem lintegral_le_sum_types : ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → 1 ≤ B.I.n → ∀ Φ : B.I.GA → ENNReal, (∀ x, 1 / 2 ≤ least B.I x → Φ x = 0) → ∫⁻ x in B.fund, Φ x ∂(B.I.muA B.μf) ≤ ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J, ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) := by
  intro B p q hs hn Φ hΦ
  have hT : ∀ (J : ℕ) (c : Composition J),
      MeasurableSet {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} := fun J c => by
    obtain ⟨s, -, h, -⟩ := GlobalTheory.FlagMeas.type_measurable B.I c.length c.blocksFun
    exact h
  set P : Set B.I.GA := ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
    {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} with hP
  set U : Set B.I.GA := ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
    {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund with hU
  have hPm : MeasurableSet P :=
    Finset.measurableSet_biUnion _ fun J _ => Finset.measurableSet_biUnion _ fun c _ => hT J c
  have hcover : B.fund ⊆ U ∪ Pᶜ := by
    intro x hx
    by_cases hxP : x ∈ P
    · left
      simp only [hP, hU, Set.mem_iUnion, Set.mem_inter_iff] at hxP ⊢
      obtain ⟨J, hJ, c, hc, hxc⟩ := hxP
      exact ⟨J, hJ, c, hc, hxc, hx⟩
    · exact Or.inr hxP
  have hzero : ∫⁻ x in Pᶜ, Φ x ∂(B.I.muA B.μf) = 0 := by
    have hae : ∀ᵐ x ∂((B.I.muA B.μf).restrict Pᶜ), Φ x = 0 := by
      rw [ae_restrict_iff' hPm.compl]
      refine ae_of_all _ fun x hx => hΦ x ?_
      by_contra hlt
      push_neg at hlt
      obtain ⟨J, hJ, c, τ, hτ⟩ := GlobalTheory.TypeDecomp.exists_type B p q hs hn x hlt
      apply hx
      simp only [hP, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨J, hJ, c, Finset.mem_univ c, τ, hτ⟩
    rw [lintegral_congr_ae hae, lintegral_zero]
  calc ∫⁻ x in B.fund, Φ x ∂(B.I.muA B.μf)
      ≤ ∫⁻ x in U ∪ Pᶜ, Φ x ∂(B.I.muA B.μf) := lintegral_mono_set hcover
    _ ≤ ∫⁻ x in U, Φ x ∂(B.I.muA B.μf) + ∫⁻ x in Pᶜ, Φ x ∂(B.I.muA B.μf) := lintegral_union_le _ _ _
    _ = ∫⁻ x in U, Φ x ∂(B.I.muA B.μf) := by rw [hzero, add_zero]
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∫⁻ x in ⋃ c ∈ (Finset.univ : Finset (Composition J)),
          {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) :=
        GlobalTheory.TypeDecomp.lintegral_biUnion_le _ _ _ _
    _ ≤ _ := Finset.sum_le_sum fun J _ => GlobalTheory.TypeDecomp.lintegral_biUnion_le _ _ _ _

end GlobalTheory.TypeDecomp
end

