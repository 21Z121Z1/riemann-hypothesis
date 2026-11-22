import Formalism.GaussValuationBounds.Statement
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.WachModuleLifts.WachModuleProofs.Bundle0001

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.GaussValueContractionProofFactBis
section
noncomputable section

namespace Formalism.NOK

open Polynomial

theorem padicInt_dvd_pow_valuation (ℓ : ℕ) [Fact ℓ.Prime] {x : ℤ_[ℓ]} (hx : x ≠ 0) :
    x ∣ (ℓ : ℤ_[ℓ]) ^ x.valuation := by
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[ℓ]ˣ, x = (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ x.valuation :=
    ⟨_, PadicInt.unitCoeff_spec hx⟩
  refine ⟨((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]), ?_⟩
  calc (ℓ : ℤ_[ℓ]) ^ x.valuation
      = ((u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ x.valuation) * ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
        rw [mul_comm (u : ℤ_[ℓ]), mul_assoc, Units.mul_inv, mul_one]
    _ = x * ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by rw [← hu]

theorem padicInt_valuation_unit (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) :
    (u : ℤ_[ℓ]).valuation = 0 := by
  have h := PadicInt.valuation_mul (Units.ne_zero u) (Units.ne_zero u⁻¹)
  rw [Units.mul_inv, PadicInt.valuation_one] at h
  omega

theorem cjExist_proof : CjExist := by
  intro ℓ _ hℓ χ hχ
  have hZ := Formalism.WindowSums.arc_ZpowVal ℓ χ 1 le_rfl (fun h => absurd h hℓ) hχ
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hdvd : ∀ j : ℤ, (ℓ : ℤ_[ℓ]) ∣ ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp
    · obtain ⟨hne, hv⟩ := hZ (-j) (neg_ne_zero.2 hj)
      rw [PadicInt.unitCoeff_spec hne]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (by rw [hv]; omega)) _
  choose d hd using hdvd
  have hc1 : ∀ j, -(ℓ : ℤ_[ℓ]) * (-d j) = ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro j
    rw [hd j]
    ring
  have key : ∀ j j' : ℤ, j ≠ j' → -d j' - -d j ≠ 0 ∧
      PadicInt.valuation (-d j' - -d j) = padicValInt ℓ (j' - j) := by
    intro j j' hjj
    have hid : χ ^ (-j) = χ ^ (-j') * χ ^ (j' - j) := by
      rw [← zpow_add]
      congr 1
      ring
    have hkey : (ℓ : ℤ_[ℓ]) ^ 1 * (-d j' - -d j) =
        ((χ ^ (-j') : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (((χ ^ (j' - j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) := by
      have e1 := hd j
      have e2 := hd j'
      rw [hid, Units.val_mul] at e1
      linear_combination e2 - e1
    obtain ⟨hne, hv⟩ := hZ (j' - j) (sub_ne_zero.2 (Ne.symm hjj))
    have hw : -d j' - -d j ≠ 0 := by
      intro h
      rw [h, mul_zero] at hkey
      exact mul_ne_zero (Units.ne_zero _) hne hkey.symm
    refine ⟨hw, ?_⟩
    have h1 := PadicInt.valuation_p_pow_mul 1 (-d j' - -d j) hw
    rw [hkey, PadicInt.valuation_mul (Units.ne_zero _) hne, padicInt_valuation_unit, hv] at h1
    omega
  refine ⟨fun j => -d j, hc1, ?_, fun j j' h => key j' j (Ne.symm h)⟩
  have h0 : (ℓ : ℤ_[ℓ]) * d 0 = 0 := by
    rw [← hd 0]
    simp
  show -d 0 = 0
  rw [neg_eq_zero]
  exact (mul_eq_zero.1 h0).resolve_left hℓ0

theorem gapLagrange (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V]
    (T : Module.End ℤ_[ℓ] V) (c : ℤ → ℤ_[ℓ])
    (hc : ∀ j j', j ≠ j' → c j - c j' ≠ 0 ∧
      PadicInt.valuation (c j - c j') = padicValInt ℓ (j - j'))
    (R₁ R₂ : Finset ℤ) (x : V) (J : ℕ) (a : Fin J → ℤ) (L : Fin J → ℕ) (D E : ℕ)
    (hdisj : Disjoint R₁ R₂)
    (h1 : aeval T (∏ r ∈ R₁, (X - C (c r))) x = 0)
    (h2 : aeval T (∏ r ∈ R₂, (X - C (c r))) x = 0)
    (hwin : ∀ r ∈ R₁ ∪ R₂, ∃ j, a j ≤ r ∧ r < a j + L j)
    (hD : ∀ r ∈ R₁ ∪ R₂, ∀ r' ∈ R₁ ∪ R₂, |r - r'| ≤ D)
    (hE : (∑ j, ((L j : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D)) ≤ E) :
    ((ℓ : ℤ_[ℓ]) ^ E) • x = 0 := by
  have hsub : R₁ ⊆ R₁ ∪ R₂ := Finset.subset_union_left
  have hinj : Set.InjOn c ((R₁ ∪ R₂ : Finset ℤ) : Set ℤ) := by
    intro m _ m' _ h
    by_contra hne
    exact (hc m m' hne).1 (sub_eq_zero.2 h)
  refine Formalism.WindowSums.arc_Lagrange ℤ_[ℓ] V T (R₁ ∪ R₂) R₁ c ((ℓ : ℤ_[ℓ]) ^ E) x hsub hinj h1 ?_ ?_
  · rw [Finset.union_sdiff_cancel_left hdisj]
    exact h2
  · intro k hk
    have hstep : (∏ m ∈ (R₁ ∪ R₂).erase k, (c k - c m)) ∣
        (ℓ : ℤ_[ℓ]) ^ (∑ m ∈ (R₁ ∪ R₂).erase k, padicValInt ℓ (k - m)) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_dvd_prod_of_dvd
      intro m hm
      have hne : k ≠ m := (Finset.ne_of_mem_erase hm).symm
      obtain ⟨h0, hv⟩ := hc k m hne
      rw [← hv]
      exact padicInt_dvd_pow_valuation ℓ h0
    refine hstep.trans (pow_dvd_pow _ ?_)
    obtain ⟨j₀, -⟩ := hwin k hk
    let g : ℤ → Fin J := fun m =>
      if h : m ∈ R₁ ∪ R₂ then Classical.choose (hwin m h) else j₀
    have hg : ∀ m ∈ R₁ ∪ R₂, a (g m) ≤ m ∧ m < a (g m) + L (g m) := by
      intro m hm
      simp only [g, dif_pos hm]
      exact Classical.choose_spec (hwin m hm)
    rw [← Finset.sum_fiberwise ((R₁ ∪ R₂).erase k) g]
    have hj : ∀ j : Fin J,
        ((∑ m ∈ ((R₁ ∪ R₂).erase k).filter (fun m => g m = j), padicValInt ℓ (k - m) : ℕ) : ℝ)
          ≤ (L j : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
      intro j
      have himg := Finset.sum_image (s := ((R₁ ∪ R₂).erase k).filter (fun m => g m = j))
        (g := fun m : ℤ => k - m) (f := fun i => padicValInt ℓ i)
        (by intro x _ y _ h; simpa using h)
      rw [← himg]
      apply Formalism.WindowSums.arc_WindowSum ℓ (k - a j - L j + 1) (L j) D
      · intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨m, hm, rfl⟩ := hi
        rw [Finset.mem_filter] at hm
        obtain ⟨hm1, hm2⟩ := hm
        have hw := hg m (Finset.mem_of_mem_erase hm1)
        rw [hm2] at hw
        rw [Finset.mem_Ico]
        omega
      · intro h0
        rw [Finset.mem_image] at h0
        obtain ⟨m, hm, hm0⟩ := h0
        have := Finset.ne_of_mem_erase (Finset.mem_filter.1 hm).1
        omega
      · intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨m, hm, rfl⟩ := hi
        exact hD k hk m (Finset.mem_of_mem_erase (Finset.mem_filter.1 hm).1)
    have hsum : ((∑ j, ∑ m ∈ ((R₁ ∪ R₂).erase k).filter (fun m => g m = j),
        padicValInt ℓ (k - m) : ℕ) : ℝ) ≤ E := by
      rw [Nat.cast_sum]
      exact (Finset.sum_le_sum fun j _ => hj j).trans hE
    exact_mod_cast hsum

theorem gaussValueContraction_proof_fact_bis : GapPure1 := by
  intro ℓ _ V _ _ T c hc a S η b E R₁ R₂ x hb hR₁ hR₂ h1 h2 hE
  have m1 : ∀ r ∈ R₁, (b : ℤ) - S - a + 1 ≤ r ∧ r ≤ b := fun r hr => Finset.mem_Icc.1 (hR₁ hr)
  have m2 : ∀ r ∈ R₂, ((b : ℤ) + 1 ≤ r ∧ r ≤ b + S + a) ∨ (1 - (η : ℤ) ≤ r ∧ r ≤ η + a) := by
    intro r hr
    simpa only [Finset.mem_union, Finset.mem_Icc] using hR₂ hr
  have hall : ∀ r ∈ R₁ ∪ R₂, 1 - (η : ℤ) ≤ r ∧ r ≤ b + S + a := by
    intro r hr
    rcases Finset.mem_union.1 hr with hr | hr
    · have := m1 r hr
      omega
    · have := m2 r hr
      omega
  refine gapLagrange ℓ V T c hc R₁ R₂ x 2 ![(b : ℤ) - S - a + 1, 1 - η] ![2 * S + 2 * a, 2 * η + a]
    (b + S + a + η) E ?_ h1 h2 ?_ ?_ ?_
  · rw [Finset.disjoint_left]
    intro r hr1 hr2
    have := m1 r hr1
    have := m2 r hr2
    omega
  · intro r hr
    rcases Finset.mem_union.1 hr with hr | hr
    · have := m1 r hr
      refine ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero]
      push_cast
      omega
    · rcases m2 r hr with h | h
      · refine ⟨0, ?_⟩
        simp only [Matrix.cons_val_zero]
        push_cast
        omega
      · refine ⟨1, ?_⟩
        simp only [Matrix.cons_val_one]
        push_cast
        omega
  · intro r hr r' hr'
    have := hall r hr
    have := hall r' hr'
    rw [abs_le]
    push_cast
    constructor <;> omega
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    convert hE using 1
    push_cast
    ring

theorem gaussValueContraction_proof_fact_alt : GapPure2 := by
  intro ℓ _ V _ _ T c hc a S b E R₁ x hab hR₁ h1 h2 hE
  have m1 : ∀ r ∈ R₁, (1 ≤ r ∧ r ≤ (a : ℤ)) ∨ (-(b : ℤ) - S + 1 ≤ r ∧ r ≤ -(b : ℤ) + a) := by
    intro r hr
    simpa only [Finset.mem_union, Finset.mem_Icc] using hR₁ hr
  have h1' : aeval T (∏ j ∈ ({0} : Finset ℤ), (X - C (c j))) x = 0 := by
    rw [Finset.prod_singleton]
    exact h1
  have hall : ∀ r ∈ ({0} : Finset ℤ) ∪ R₁, -(b : ℤ) - S + 1 ≤ r ∧ r ≤ a := by
    intro r hr
    rcases Finset.mem_union.1 hr with hr | hr
    · rw [Finset.mem_singleton] at hr
      omega
    · have := m1 r hr
      omega
  refine gapLagrange ℓ V T c hc {0} R₁ x 2 ![0, -(b : ℤ) - S + 1] ![a + 1, S + a]
    (b + S + a) E ?_ h1' h2 ?_ ?_ ?_
  · rw [Finset.disjoint_singleton_left]
    intro h0
    have := m1 0 h0
    omega
  · intro r hr
    rcases Finset.mem_union.1 hr with hr | hr
    · rw [Finset.mem_singleton] at hr
      refine ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero]
      push_cast
      omega
    · rcases m1 r hr with h | h
      · refine ⟨0, ?_⟩
        simp only [Matrix.cons_val_zero]
        push_cast
        omega
      · refine ⟨1, ?_⟩
        simp only [Matrix.cons_val_one]
        push_cast
        omega
  · intro r hr r' hr'
    have := hall r hr
    have := hall r' hr'
    rw [abs_le]
    push_cast
    constructor <;> omega
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    convert hE using 1
    push_cast
    ring

end Formalism.NOK
end
end

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.GaussValueContractionProofFactVariant
section
noncomputable section

namespace Formalism.NOK

theorem pow_mem_span_pair_pow {R : Type} [CommRing R] (a b p : R) (z c m : ℕ)
    (hp : p ∈ Ideal.span {a, b}) (h : c + m ≤ z + 1) :
    p ^ z ∈ Ideal.span {a ^ c, b ^ m} := by
  obtain ⟨s, t, rfl⟩ := Ideal.mem_span_pair.mp hp
  rw [add_pow]
  refine Ideal.sum_mem _ (fun i hi => ?_)
  have hiz : i ≤ z := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hci : c ≤ i
  · have e : (s * a) ^ i * (t * b) ^ (z - i) * (z.choose i : R)
        = (s ^ i * a ^ (i - c) * (t * b) ^ (z - i) * (z.choose i : R)) * a ^ c := by
      rw [mul_pow]
      conv_lhs => rw [show a ^ i = a ^ (i - c) * a ^ c by rw [← pow_add, Nat.sub_add_cancel hci]]
      ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · have hm : m ≤ z - i := by omega
    have e : (s * a) ^ i * (t * b) ^ (z - i) * (z.choose i : R)
        = ((s * a) ^ i * t ^ (z - i) * b ^ (z - i - m) * (z.choose i : R)) * b ^ m := by
      rw [mul_pow t b]
      conv_lhs => rw [show b ^ (z - i) = b ^ (z - i - m) * b ^ m by
        rw [← pow_add, Nat.sub_add_cancel hm]]
      ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem gaussValueContraction_proof_fact_form : Rel1 := by
  intro A _ ℓ hℓ h3 X u B r
  have hLeg := Formalism.CL.legendreBound ℓ r
  have h3R : (3 : ℝ) ≤ ℓ := by exact_mod_cast h3
  have hd : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  set v := r + padicValNat ℓ r.factorial with hv
  set σ := ⌊(B : ℝ) / ((ℓ : ℝ) - 1)⌋₊ + 1 with hσ
  have hσB : (B : ℝ) / ((ℓ : ℝ) - 1) < σ := by
    rw [hσ]; push_cast; exact Nat.lt_floor_add_one _
  have hvR : (v : ℝ) * ((ℓ : ℝ) - 1) ≤ r * ℓ := by
    rw [hv]; push_cast; rwa [le_div_iff₀ hd] at hLeg
  have hσR : (B : ℝ) < σ * ((ℓ : ℝ) - 1) := by rwa [div_lt_iff₀ hd] at hσB
  have hmul : (ℓ - 1) * r + r = ℓ * r := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ ℓ)]
  by_cases h1 : v ≤ σ
  · apply Ideal.mul_mem_right
    rw [show (ℓ : A) ^ σ = (ℓ : A) ^ (σ - v) * (ℓ : A) ^ v by
      rw [← pow_add, Nat.sub_add_cancel h1]]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso; apply h1; rw [hv, h0]; simp
    · exact h0
  by_cases h2 : B ≤ (ℓ - 1) * r
  · apply Ideal.mul_mem_left
    have e : (u * X * (X + (ℓ : A)) ^ (ℓ - 1)) ^ r
        = (u ^ r * X ^ (r - 1) * (X + (ℓ : A)) ^ ((ℓ - 1) * r - B)) * (X * (X + (ℓ : A)) ^ B) := by
      rw [mul_pow, mul_pow, ← pow_mul]
      conv_lhs => rw [show X ^ r = X ^ (r - 1) * X by rw [← pow_succ, Nat.sub_add_cancel hr],
        show (X + (ℓ : A)) ^ ((ℓ - 1) * r) = (X + (ℓ : A)) ^ ((ℓ - 1) * r - B) * (X + (ℓ : A)) ^ B by
          rw [← pow_add, Nat.sub_add_cancel h2]]
      ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  push Not at h1 h2
  have hlB : B < ℓ * r := by
    by_contra hh
    push Not at hh
    have hh' : (ℓ : ℝ) * r ≤ B := by exact_mod_cast hh
    have hlt : (v : ℝ) * ((ℓ : ℝ) - 1) < σ * ((ℓ : ℝ) - 1) := by nlinarith
    have : (v : ℝ) < σ := lt_of_mul_lt_mul_right hlt hd.le
    have : v < σ := by exact_mod_cast this
    omega
  have hkey : v ≤ σ + (ℓ * r - B) := by
    have hlr : (B : ℝ) < ℓ * r := by exact_mod_cast hlB
    have hlt : (v : ℝ) * ((ℓ : ℝ) - 1) < (σ + ((ℓ : ℝ) * r - B)) * ((ℓ : ℝ) - 1) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hlr.le) (by linarith : (0 : ℝ) ≤ ℓ - 2)]
    have hcast : ((σ + (ℓ * r - B) : ℕ) : ℝ) = (σ : ℝ) + ((ℓ : ℝ) * r - B) := by
      push_cast [Nat.cast_sub hlB.le]; ring
    have h' : (v : ℝ) < ((σ + (ℓ * r - B) : ℕ) : ℝ) := by
      rw [hcast]; exact lt_of_mul_lt_mul_right hlt hd.le
    exact_mod_cast h'.le
  have hXmem : X ∈ Ideal.span {(ℓ : A), X + (ℓ : A)} :=
    Ideal.mem_span_pair.mpr ⟨-1, 1, by ring⟩
  have hpow := pow_mem_span_pair_pow (ℓ : A) (X + (ℓ : A)) X (r - 1) (ℓ * r - B)
    (B - (ℓ - 1) * r) hXmem (by omega)
  obtain ⟨s, t, hst⟩ := Ideal.mem_span_pair.mp hpow
  have hx : (u * X * (X + (ℓ : A)) ^ (ℓ - 1)) ^ r
      = u ^ r * X * (X + (ℓ : A)) ^ ((ℓ - 1) * r) * X ^ (r - 1) := by
    rw [mul_pow, mul_pow, ← pow_mul]
    conv_lhs => rw [show X ^ r = X ^ (r - 1) * X by rw [← pow_succ, Nat.sub_add_cancel hr]]
    ring
  rw [hx, ← hst]
  have e1 : (ℓ : A) ^ σ * (ℓ : A) ^ (ℓ * r - B) = (ℓ : A) ^ (σ + (ℓ * r - B) - v) * (ℓ : A) ^ v := by
    rw [← pow_add, ← pow_add, Nat.sub_add_cancel hkey]
  have e2 : (X + (ℓ : A)) ^ ((ℓ - 1) * r) * (X + (ℓ : A)) ^ (B - (ℓ - 1) * r) = (X + (ℓ : A)) ^ B := by
    rw [← pow_add, Nat.add_sub_cancel' h2.le]
  have e : (ℓ : A) ^ σ * (u ^ r * X * (X + (ℓ : A)) ^ ((ℓ - 1) * r) *
      (s * (ℓ : A) ^ (ℓ * r - B) + t * (X + (ℓ : A)) ^ (B - (ℓ - 1) * r)))
      = (u ^ r * X * s * (X + (ℓ : A)) ^ ((ℓ - 1) * r) * (ℓ : A) ^ (σ + (ℓ * r - B) - v)) *
          (ℓ : A) ^ v + ((ℓ : A) ^ σ * u ^ r * t) * (X * (X + (ℓ : A)) ^ B) := by
    linear_combination (u ^ r * X * s * (X + (ℓ : A)) ^ ((ℓ - 1) * r)) * e1 +
      ((ℓ : A) ^ σ * u ^ r * t * X) * e2
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

theorem gaussValueContraction_proof_fact_variant : Rel2 := by
  intro O _ ℓ hℓ h3 ε u' w b r
  have hLeg := Formalism.CL.legendreBound ℓ r
  have h3R : (3 : ℝ) ≤ ℓ := by exact_mod_cast h3
  have hd : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hL : (0 : ℝ) < ℓ := by linarith
  set v := r + padicValNat ℓ r.factorial with hv
  set σ := ⌊(b : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌋₊ + 1 with hσ
  have hσb : (b : ℝ) / ((ℓ : ℝ) - 1) ^ 2 < σ := by
    rw [hσ]; push_cast; exact Nat.lt_floor_add_one _
  have hvR : (v : ℝ) * ((ℓ : ℝ) - 1) ≤ r * ℓ := by
    rw [hv]; push_cast; rwa [le_div_iff₀ hd] at hLeg
  have hσR : (b : ℝ) < σ * ((ℓ : ℝ) - 1) ^ 2 := by rwa [div_lt_iff₀ (by positivity)] at hσb
  have hx : (w * (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ (ℓ - 1) *
      (Formalism.WindowSums.p1 ℓ ε u') ^ (ℓ - 1)) ^ r
      = (w * (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ (ℓ - 1)) ^ r *
        (Formalism.WindowSums.p1 ℓ ε u') ^ ((ℓ - 1) * r) := by
    rw [mul_pow, ← pow_mul]
  unfold Formalism.WindowSums.IdLQ
  by_cases h1 : v ≤ σ
  · apply Ideal.mul_mem_right
    rw [show (ℓ : O) ^ σ = (ℓ : O) ^ (σ - v) * (ℓ : O) ^ v by
      rw [← pow_add, Nat.sub_add_cancel h1], map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  push Not at h1
  have hnum : ((v - σ : ℕ) : ℝ) ≤ (((ℓ - 1) * r : ℕ) : ℝ) + 1 - (b : ℝ) / (ℓ : ℝ) := by
    rw [Nat.cast_sub h1.le, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
    set β := (b : ℝ) / (ℓ : ℝ) with hβdef
    have hβ : β * ℓ = b := by rw [hβdef]; field_simp
    have h1R : (σ : ℝ) < v := by exact_mod_cast h1
    have hv2 : (v : ℝ) * ((ℓ : ℝ) - 1) ^ 2 ≤ r * ℓ * ((ℓ : ℝ) - 1) := by
      have := mul_le_mul_of_nonneg_right hvR hd.le
      nlinarith
    by_cases hc : ((ℓ : ℝ) - 1) * r * ℓ < b
    · exfalso
      have hlt : (v : ℝ) * ((ℓ : ℝ) - 1) ^ 2 < σ * ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
      have := lt_of_mul_lt_mul_right hlt (by positivity)
      linarith
    · push Not at hc
      have hβr : β ≤ ((ℓ : ℝ) - 1) * r := by
        by_contra hh; push Not at hh
        have := mul_lt_mul_of_pos_right hh hL
        linarith
      have hA : ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) * (((ℓ : ℝ) - 1) * r - β) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)
      have hlt : (v : ℝ) * ((ℓ : ℝ) - 1) ^ 2 <
          (σ + ((ℓ : ℝ) - 1) * r - β) * ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
      have := lt_of_mul_lt_mul_right hlt (by positivity)
      linarith
  have hC2 := Formalism.WindowSums.arc_C2Lower O ℓ ε u' ((ℓ - 1) * r) b (v - σ) hnum
  unfold Formalism.WindowSums.IdLQ at hC2
  obtain ⟨s, t, hst⟩ := Ideal.mem_span_pair.mp hC2
  rw [hx, ← hst]
  have e1 : PowerSeries.C ((ℓ : O) ^ σ) * PowerSeries.C ((ℓ : O) ^ (v - σ)) =
      PowerSeries.C ((ℓ : O) ^ v) := by
    rw [← map_mul, ← pow_add, Nat.add_sub_cancel' h1.le]
  set W := (w * (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ (ℓ - 1)) ^ r
  have e : PowerSeries.C ((ℓ : O) ^ σ) * (W * (s * PowerSeries.C ((ℓ : O) ^ (v - σ)) +
      t * PowerSeries.X ^ b)) = (W * s) * PowerSeries.C ((ℓ : O) ^ v) +
      (PowerSeries.C ((ℓ : O) ^ σ) * W * t) * PowerSeries.X ^ b := by
    linear_combination (W * s) * e1
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

end Formalism.NOK
end
end

