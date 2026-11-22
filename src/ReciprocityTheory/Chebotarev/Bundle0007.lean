import ReciprocityTheory.Chebotarev.Bundle0006
import ReciprocityTheory.Chebotarev.DiscreteTopologyLatOf
import ReciprocityTheory.Chebotarev.Bundle0003
import ReciprocityTheory.Chebotarev.Bundle0005
import ReciprocityTheory.Chebotarev.SplitEA

-- bundled from ReciprocityTheory.Chebotarev.NormGsEmbZLe
section
open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

theorem gs_eq_ofReal {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    Gs χ s x = χ (rsgn x : ZMod l) * ((uphi x * (mixedEmbedding.norm x) ^ (-s) : ℝ) : ℂ) := by
  unfold Gs
  rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (mixedEmbedding.norm_nonneg x)]
  push_cast; ring

theorem norm_gs_le {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    ‖Gs χ s x‖ ≤ uphi x * (mixedEmbedding.norm x) ^ (-s) := by
  rw [gs_eq_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (uphi_nonneg x) (Real.rpow_nonneg (mixedEmbedding.norm_nonneg x) _))]
  exact mul_le_of_le_one_left (mul_nonneg (uphi_nonneg x) (Real.rpow_nonneg (mixedEmbedding.norm_nonneg x) _))
    (DirichletCharacter.norm_le_one χ _)

theorem norm_gs_embZ_le {l : ℕ} (χ : DirichletCharacter ℂ l) {s : ℝ} (hs : 1 ≤ s) (α : 𝓞 E) :
    ‖Gs χ s (embZ α)‖ ≤ 1 := by
  refine (norm_gs_le χ s _).trans ?_
  have h1 : (mixedEmbedding.norm (embZ α)) ^ (-s) ≤ 1 := by
    rw [norm_embZ]
    by_cases h0 : Algebra.norm ℤ α = 0
    · rw [h0]; simp only [Int.cast_zero, abs_zero]
      rw [Real.zero_rpow (by linarith)]; norm_num
    · apply Real.rpow_le_one_of_one_le_of_nonpos _ (by linarith)
      have : (1 : ℤ) ≤ |Algebra.norm ℤ α| := Int.one_le_abs h0
      exact_mod_cast this
  calc uphi (embZ α) * (mixedEmbedding.norm (embZ α)) ^ (-s) ≤ 1 * 1 :=
        mul_le_mul (uphi_le_one _) h1 (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _) zero_le_one
    _ = 1 := one_mul 1

theorem continuous_gs {l : ℕ} (χ : DirichletCharacter ℂ l) (x : mixedSpace E) :
    Continuous fun s : ℝ => Gs χ s x := by
  simp_rw [gs_eq_ofReal]
  by_cases h : mixedEmbedding.norm x = 0
  · simp only [uphi_of_norm_eq_zero h, zero_mul, Complex.ofReal_zero, mul_zero]
    exact continuous_const
  · refine continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul ?_))
    exact (Real.continuous_const_rpow h).comp continuous_neg

theorem summable_gs {l : ℕ} (χ : DirichletCharacter ℂ l) (Λ : Submodule ℤ (mixedSpace E)) [DiscreteTopology Λ]
    (hΛ : Module.finrank ℤ Λ = Module.finrank ℚ E) {s : ℝ} (hs : 1 < s) :
    Summable fun x : Λ => Gs χ s (x : mixedSpace E) := by
  obtain ⟨c₀, hc₀, -, hb⟩ := exists_support_bound (E := E)
  set d := Module.finrank ℚ E
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Module.finrank_pos
  set r : ℝ := -((d : ℝ) * s)
  have hr : r < -(Module.finrank ℤ Λ : ℝ) := by
    rw [hΛ]; simp only [r, neg_lt_neg_iff]; nlinarith
  refine Summable.of_norm_bounded ((ZLattice.summable_norm_rpow Λ r hr).mul_left (c₀ ^ r)) fun x => ?_
  refine (norm_gs_le χ s _).trans ?_
  have hpos : 0 ≤ c₀ ^ r * ‖x‖ ^ r := mul_nonneg (Real.rpow_nonneg hc₀.le _) (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hu : uphi (x : mixedSpace E) = 0
  · rw [hu, zero_mul]; exact hpos
  obtain ⟨-, hN⟩ := hb _ hu
  have hN0 : mixedEmbedding.norm (x : mixedSpace E) ≠ 0 := by
    intro h; exact hu (uphi_of_norm_eq_zero h)
  have hx0 : (x : mixedSpace E) ≠ 0 := by
    rintro h; apply hN0; rw [h]
    exact mixedEmbedding.norm_eq_zero_iff.mpr ⟨Classical.arbitrary _, by simp⟩
  have hxn : 0 < ‖(x : mixedSpace E)‖ := norm_pos_iff.mpr hx0
  have hcx : 0 < c₀ * ‖(x : mixedSpace E)‖ := mul_pos hc₀ hxn
  have key : (mixedEmbedding.norm (x : mixedSpace E)) ^ (-s) ≤ (c₀ * ‖(x : mixedSpace E)‖) ^ r := by
    have : (c₀ * ‖(x : mixedSpace E)‖) ^ r = ((c₀ * ‖(x : mixedSpace E)‖) ^ d) ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hcx.le]; simp [r]
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos (pow_pos hcx _) (by rw [mul_pow]; exact hN) (by linarith)
  calc uphi (x : mixedSpace E) * (mixedEmbedding.norm (x : mixedSpace E)) ^ (-s)
      ≤ 1 * (c₀ * ‖(x : mixedSpace E)‖) ^ r :=
        mul_le_mul (uphi_le_one _) key (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _) zero_le_one
    _ = c₀ ^ r * ‖x‖ ^ r := by rw [one_mul, Real.mul_rpow hc₀.le (norm_nonneg _)]; rfl

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.PrimeAsymp
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem pa_cpow_eq (n : ℕ) (s : ℝ) :
    ((n : ℂ) ^ (-(s : ℂ))) = (((n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

theorem pa_one_le_absNorm {E : Type} [Field E] [NumberField E] (a : NZIdeal E) :
    (1 : ℝ) ≤ ((Ideal.absNorm a.1 : ℕ) : ℝ) := by
  have h : Ideal.absNorm a.1 ≠ 0 := by
    intro h0
    exact a.2 (Ideal.absNorm_eq_zero_iff.mp h0)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

theorem pa_rpow_lt_one {E : Type} [Field E] [NumberField E] (q : Prm E) {s : ℝ} (hs : 0 < s) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) < 1 := by
  have h := two_le_Nrm q
  have h1 : (1 : ℝ) < ((Nrm q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < Nrm q)
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

theorem real_euler (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Real.exp (∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) =
      ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by
  have hs0 : (0 : ℝ) < s := by linarith
  set f : Ideal (𝓞 E) → ℂ := fun a => ((Ideal.absNorm a : ℕ) : ℂ) ^ (-(s : ℂ)) with hfdef
  have hf1 : f 1 = 1 := by simp [hfdef]
  have hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b := by
    intro a b
    simp only [hfdef, map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _
  have hnorm : ∀ a : Ideal (𝓞 E), ‖f a‖ = ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s) := by
    intro a
    simp only [hfdef]
    rw [pa_cpow_eq, Complex.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hsum : Summable (fun a : NZIdeal E => ‖f a.1‖) := by
    simp only [hnorm]
    exact summable_absNorm_rpow E hs
  have hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1 := by
    intro q
    rw [hnorm]
    exact pa_rpow_lt_one q hs0
  have h := euler_exp_log f hf1 hmul hsum hlt
  apply Complex.ofReal_injective
  rw [Complex.ofReal_exp, Complex.ofReal_tsum, Complex.ofReal_tsum]
  have e1 : (∑' q : Prm E, (((-Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) : ℝ) : ℂ)) =
      ∑' q : Prm E, -Complex.log (1 - f q.asIdeal) := by
    refine tsum_congr fun q => ?_
    have hx := pa_rpow_lt_one q hs0
    rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub, Complex.ofReal_one,
      ← pa_cpow_eq]
    rfl
  have e2 : (∑' a : NZIdeal E, ((((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) = ∑' a : NZIdeal E, f a.1 := by
    refine tsum_congr fun a => ?_
    rw [← pa_cpow_eq]
  rw [e1, e2]
  exact h

theorem pa_log_bdd {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |-Real.log (1 - x) - x| ≤ 2 * x ^ 2 := by
  have hx1 : |x| < 1 := by
    rw [abs_of_nonneg hx0]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  norm_num at h
  rw [abs_of_nonneg hx0] at h
  rw [show -Real.log (1 - x) - x = -(x + Real.log (1 - x)) by ring, abs_neg]
  calc |x + Real.log (1 - x)| ≤ x ^ 2 / (1 - x) := h
    _ ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]

theorem pa_A_sub_PE (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    |(∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) - PE E s| ≤
      2 * ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hP := summable_prm_rpow E hs
  have h2 := summable_prm_rpow E (by norm_num : (1 : ℝ) < 2)
  have hb : ∀ q : Prm E, ‖-Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s)) - ((Nrm q : ℕ) : ℝ) ^ (-s)‖ ≤
      2 * ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    intro q
    have hN2 : (2 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
    have hN0 : (0 : ℝ) < ((Nrm q : ℕ) : ℝ) := by linarith
    have hx0 : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg hN0.le _
    have hxh : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := by
      calc ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = (((Nrm q : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hN2
    rw [Real.norm_eq_abs]
    refine (pa_log_bdd hx0 hxh).trans ?_
    have : (((Nrm q : ℕ) : ℝ) ^ (-s)) ^ 2 ≤ ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
      rw [sq, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    linarith
  have hg : Summable (fun q : Prm E => -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s)) - ((Nrm q : ℕ) : ℝ) ^ (-s)) :=
    Summable.of_norm_bounded (h2.mul_left 2) hb
  have hA : Summable (fun q : Prm E => -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) :=
    (hg.add hP).congr (fun q => by ring)
  unfold PE
  rw [← hA.tsum_sub hP, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded ((h2.hasSum).mul_left 2) hb

theorem pa_Z_ge_one (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    1 ≤ ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by
  have h := (summable_absNorm_rpow E hs).le_tsum (⟨⊤, top_ne_bot⟩ : NZIdeal E)
    (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  simpa [Ideal.absNorm_top] using h

theorem pa_Z_anti (E : Type) [Field E] [NumberField E] {s t : ℝ} (ht : 1 < t) (hts : t ≤ s) :
    ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ≤
      ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-t) :=
  Summable.tsum_le_tsum (fun a => Real.rpow_le_rpow_of_exponent_le (pa_one_le_absNorm a) (by linarith))
    (summable_absNorm_rpow E (lt_of_lt_of_le ht hts)) (summable_absNorm_rpow E ht)

theorem pa_Z_lim (E : Type) [Field E] [NumberField E] :
    Tendsto (fun s : ℝ => (s - 1) * ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s))
      (𝓝[>] 1) (𝓝 (dedekindZeta_residue E)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT E)
  simp only [Complex.ofReal_re] at h
  refine h.congr' ?_
  refine eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => ?_
  simp only [Function.comp_apply]
  rw [dedekindZeta_eq_tsum E hs]
  have e : (∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) =
      ((∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun a => pa_cpow_eq _ _
  rw [e, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem pa_g_bdd (E : Type) [Field E] [NumberField E] :
    ∃ m M : ℝ, 0 < m ∧ ∀ s ∈ Set.Ioc (1 : ℝ) 2,
      m ≤ (s - 1) * ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ∧
      (s - 1) * ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ≤ M := by
  set r := dedekindZeta_residue E
  have hr : 0 < r := dedekindZeta_residue_pos E
  have hmem := pa_Z_lim E (Icc_mem_nhds (by linarith : r / 2 < r) (by linarith : r < 2 * r))
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (by norm_num : (1 : ℝ) < 2)).mp hmem
  have hu1 : 1 < u := hu
  set t := min ((1 + u) / 2) 2 with htdef
  have ht1 : 1 < t := lt_min (by linarith) (by norm_num)
  have htu : t < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht2 : t ≤ 2 := min_le_right _ _
  set Zt := ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-t)
  refine ⟨min (r / 2) (t - 1), max (2 * r) Zt, lt_min (by linarith) (by linarith), fun s hs => ?_⟩
  obtain ⟨hs1, hs2⟩ := hs
  have hZ1 := pa_Z_ge_one E hs1
  rcases le_total s t with hst | hst
  · have hin := hsub ⟨hs1, lt_of_le_of_lt hst htu⟩
    obtain ⟨h1, h2⟩ := hin
    exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_left _ _)⟩
  · have hZ := pa_Z_anti E ht1 hst
    constructor
    · refine (min_le_right _ _).trans ?_
      nlinarith
    · refine le_trans ?_ (le_max_right _ _)
      have hZ0 : 0 ≤ ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by linarith
      nlinarith

theorem pe_log_bdd : faceMap_castSucc_comp_eq_succ := by
  intro E _ _
  obtain ⟨m, M, hm, hbd⟩ := pa_g_bdd E
  refine ⟨2 * ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) + (|Real.log m| + |Real.log M|), fun s hs => ?_⟩
  obtain ⟨h1, h2⟩ := hbd s hs
  have hs1 : 1 < s := hs.1
  have hAP := pa_A_sub_PE E hs1
  have hZ := pa_Z_ge_one E hs1
  have he := real_euler E hs1
  set A := ∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))
  set Z := ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s)
  have hAZ : A = Real.log Z := by rw [← he, Real.log_exp]
  have hg0 : 0 < (s - 1) * Z := lt_of_lt_of_le hm h1
  have hlog : A - Real.log (1 / (s - 1)) = Real.log ((s - 1) * Z) := by
    rw [hAZ, one_div, Real.log_inv, Real.log_mul (by linarith) (by linarith)]
    ring
  have hl1 : Real.log m ≤ Real.log ((s - 1) * Z) := Real.log_le_log hm h1
  have hl2 : Real.log ((s - 1) * Z) ≤ Real.log M := Real.log_le_log hg0 h2
  have hb : |Real.log ((s - 1) * Z)| ≤ |Real.log m| + |Real.log M| :=
    abs_le.mpr ⟨by linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log M)],
      by linarith [le_abs_self (Real.log M), abs_nonneg (Real.log m)]⟩
  have e : PE E s - Real.log (1 / (s - 1)) = -(A - PE E s) + (A - Real.log (1 / (s - 1))) := by ring
  rw [e, hlog]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  linarith

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.SplitE
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem splitE_split_ext (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) (hχ : χ ≠ 1) :
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : Algebra E E') (k : ℕ), 2 ≤ k ∧
      ∀ q : Prm E, ¬ l ∣ Nrm q → χ ((Nrm q : ℕ) : ZMod l) = 1 →
        k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard := by
  refine ⟨IntermediateField.fixedField (splitEH hirr χ), inferInstance, inferInstance, inferInstance,
    Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)), splitE_two_le hirr χ hχ, ?_⟩
  intro q hl hq
  exact splitE_count hirr χ q hl hq _
    (fun x σ hσ => (IntermediateField.mem_fixedField_iff _ _).1 x.2 σ hσ)

end ReciprocityTheory.Cheb
end

