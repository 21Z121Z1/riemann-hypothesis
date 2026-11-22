import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0005
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnDensNonneg
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Finset
open scoped ENNReal

theorem cn_lint_prod {a : ℕ} (h : Fin a → ℝ → ℝ) (hi : ∀ i, Integrable (h i)) (h0 : ∀ i t, 0 ≤ h i t) :
    ∫⁻ t : Fin a → ℝ, ENNReal.ofReal (∏ i, h i (t i)) = ENNReal.ofReal (∏ i, ∫ s, h i s) := by
  rw [← integral_fintype_prod_volume_eq_prod]
  refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
  · exact Integrable.fintype_prod hi
  · exact Filter.Eventually.of_forall fun t => Finset.prod_nonneg fun i _ => h0 i (t i)

theorem cn_int_log (f j : ℕ) (ts : ℝ) (h0 : 0 < ts) (h1 : ts ≤ 1 / 2) :
    Integrable ((Set.Ico ts (1 / 2)).indicator fun t : ℝ => 2 * (f : ℝ) * j / t) ∧
      ∫ t, (Set.Ico ts (1 / 2)).indicator (fun t : ℝ => 2 * (f : ℝ) * j / t) t =
        2 * (f : ℝ) * j * Real.log (1 / (2 * ts)) := by
  have hc : ContinuousOn (fun t : ℝ => 2 * (f : ℝ) * j / t) (Set.Icc ts (1 / 2)) :=
    continuousOn_const.div continuousOn_id fun t ht => (lt_of_lt_of_le h0 ht.1).ne'
  have hI : IntegrableOn (fun t : ℝ => 2 * (f : ℝ) * j / t) (Set.Icc ts (1 / 2)) := hc.integrableOn_Icc
  refine ⟨(integrable_indicator_iff measurableSet_Ico).2 (hI.mono_set Set.Ico_subset_Icc_self), ?_⟩
  rw [integral_indicator measurableSet_Ico, ← Formalism.HermitianLatticeCounting.Final.S7.logVolume f j ts h0 h1,
    intervalIntegral.integral_of_le h1, integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

theorem cn_int_tau (f j n0 : ℕ) (hf : 1 ≤ f) (hj : 1 ≤ j) (hn : 1 ≤ n0) :
    Integrable ((Set.Ioo (0 : ℝ) (1 / 2)).indicator fun t : ℝ => t ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / t)) ∧
      ∫ t, (Set.Ioo (0 : ℝ) (1 / 2)).indicator (fun t : ℝ => t ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / t)) t =
        (1 / 2) ^ (2 * j * n0 * f) / (n0 : ℝ) := by
  have hT := Formalism.HermitianLatticeCounting.Final.S7.tauIntegral f j n0 hf hj hn
  have hpos : (0 : ℝ) < (1 / 2) ^ (2 * j * n0 * f) / (n0 : ℝ) := by positivity
  have hII : IntervalIntegrable (fun t : ℝ => t ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / t)) volume 0 (1 / 2) := by
    by_contra hcon
    rw [intervalIntegral.integral_undef hcon] at hT
    exact hpos.ne hT
  have hI : IntegrableOn (fun t : ℝ => t ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / t)) (Set.Ioc 0 (1 / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hII
  refine ⟨(integrable_indicator_iff measurableSet_Ioo).2 (hI.mono_set Set.Ioo_subset_Ioc_self), ?_⟩
  rw [integral_indicator measurableSet_Ioo, ← hT, intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo]

abbrev cn_Root (a : ℕ) : Type :=
  ({p : Fin a × Fin a // p.1 < p.2} ⊕ {p : Fin a × Fin a // p.1 < p.2}) ⊕ (Fin a ⊕ Fin a)

def cn_la {a : ℕ} (t : Fin a → ℝ) : cn_Root a → ℝ
  | .inl (.inl p) => t p.1.1 / t p.1.2
  | .inl (.inr p) => t p.1.1 * t p.1.2
  | .inr (.inl x) => t x ^ 2
  | .inr (.inr x) => t x

def cn_dim {a : ℕ} (j : Fin a → ℕ) (n0 : ℕ) : cn_Root a → ℕ
  | .inl (.inl p) => 2 * j p.1.1 * j p.1.2
  | .inl (.inr p) => 2 * j p.1.1 * j p.1.2
  | .inr (.inl x) => j x ^ 2
  | .inr (.inr x) => 2 * j x * n0

def cn_Reg (a : ℕ) : Set (Fin a → ℝ) := {t | StrictMono t ∧ ∀ x, 0 < t x ∧ t x < 1 / 2}

def cn_dens {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (t : Fin a → ℝ) : ℝ := ∏ r, cn_la t r ^ (cn_dim j n0 r * f)

def cn_cnt {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (de : ℝ) (t : Fin a → ℝ) : ℝ :=
  ∏ r, (1 + 12 * de / cn_la t r) ^ (cn_dim j n0 r * f)

theorem cn_sum_pairs {a : ℕ} (F : Fin a → Fin a → ℕ) :
    ∑ p : {p : Fin a × Fin a // p.1 < p.2}, F p.1.1 p.1.2 = ∑ x, ∑ y with x < y, F x y := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin a × Fin a => p.1 < p.2) (by simp)
    (fun p => F p.1 p.2), Finset.sum_filter, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ => (Finset.sum_filter _ _).symm

theorem cn_sum_dim {a : ℕ} (j : Fin a → ℕ) (n0 : ℕ) : ∑ r, cn_dim j n0 r = Formalism.HermitianLatticeCounting.S7.dimN j n0 := by
  simp only [Fintype.sum_sum_type, cn_dim, Formalism.HermitianLatticeCounting.S7.dimN]
  rw [cn_sum_pairs fun x y => 2 * j x * j y]
  ring

theorem cn_la_mem {a : ℕ} {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) (r : cn_Root a) : 0 < cn_la t r ∧ cn_la t r < 1 := by
  obtain ⟨hm, hb⟩ := ht
  rcases r with (p | p) | (x | x)
  · have h1 := hb p.1.1
    have h2 := hb p.1.2
    exact ⟨div_pos h1.1 h2.1, (div_lt_one h2.1).2 (hm p.2)⟩
  · have h1 := hb p.1.1
    have h2 := hb p.1.2
    refine ⟨mul_pos h1.1 h2.1, ?_⟩
    show t p.1.1 * t p.1.2 < 1
    nlinarith
  · have h1 := hb x
    refine ⟨pow_pos h1.1 2, ?_⟩
    show t x ^ 2 < 1
    nlinarith
  · have h1 := hb x
    exact ⟨h1.1, by show t x < 1; linarith⟩

theorem cn_cnt_dens_le {a : ℕ} (j : Fin a → ℕ) (n0 f n q : ℕ) (de : ℝ) (hn : n0 + 2 * ∑ x, j x = n) (hq : ∑ x, j x ≤ q)
    (hde : 0 ≤ de) (hsm : de * q * n * f ≤ 1 / 100) {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) :
    cn_cnt j n0 f de t * cn_dens j n0 f t ≤ 2 := by
  refine Formalism.HermitianLatticeCounting.Final.S7.nearProduct (cn_Root a) (cn_la t) (cn_dim j n0) n q (∑ x, j x) f de 12 (cn_la_mem ht) hde
    (by norm_num) (by norm_num) ?_ hq hsm
  rw [cn_sum_dim, ← hn]
  exact (Formalism.HermitianLatticeCounting.Final.S7.dimIdentity a j n0).2.1

theorem cn_dens_le {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) :
    cn_dens j n0 f t ≤ ∏ x, t x ^ (2 * j x * n0 * f) := by
  have h1 : ∀ r, 0 ≤ cn_la t r ^ (cn_dim j n0 r * f) ∧ cn_la t r ^ (cn_dim j n0 r * f) ≤ 1 := fun r =>
    ⟨pow_nonneg (cn_la_mem ht r).1.le _, pow_le_one₀ (cn_la_mem ht r).1.le (cn_la_mem ht r).2.le⟩
  unfold cn_dens
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type (f := fun r : Fin a ⊕ Fin a => _)]
  have hA : ∏ r : {p : Fin a × Fin a // p.1 < p.2} ⊕ {p : Fin a × Fin a // p.1 < p.2},
      cn_la t (Sum.inl r) ^ (cn_dim j n0 (Sum.inl r) * f) ≤ 1 :=
    Finset.prod_le_one (fun r _ => (h1 _).1) fun r _ => (h1 _).2
  have hB : ∏ x : Fin a, cn_la t (Sum.inr (Sum.inl x)) ^ (cn_dim j n0 (Sum.inr (Sum.inl x)) * f) ≤ 1 :=
    Finset.prod_le_one (fun r _ => (h1 _).1) fun r _ => (h1 _).2
  have hA0 : 0 ≤ ∏ r : {p : Fin a × Fin a // p.1 < p.2} ⊕ {p : Fin a × Fin a // p.1 < p.2},
      cn_la t (Sum.inl r) ^ (cn_dim j n0 (Sum.inl r) * f) := Finset.prod_nonneg fun r _ => (h1 _).1
  have hB0 : 0 ≤ ∏ x : Fin a, cn_la t (Sum.inr (Sum.inl x)) ^ (cn_dim j n0 (Sum.inr (Sum.inl x)) * f) :=
    Finset.prod_nonneg fun r _ => (h1 _).1
  have hC0 : 0 ≤ ∏ x : Fin a, cn_la t (Sum.inr (Sum.inr x)) ^ (cn_dim j n0 (Sum.inr (Sum.inr x)) * f) :=
    Finset.prod_nonneg fun r _ => (h1 _).1
  have hC : ∏ x : Fin a, cn_la t (Sum.inr (Sum.inr x)) ^ (cn_dim j n0 (Sum.inr (Sum.inr x)) * f) =
      ∏ x, t x ^ (2 * j x * n0 * f) := rfl
  rw [← hC]
  calc _ ≤ 1 * (1 * ∏ x : Fin a, cn_la t (Sum.inr (Sum.inr x)) ^ (cn_dim j n0 (Sum.inr (Sum.inr x)) * f)) := by
        gcongr
    _ = _ := by ring

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnKappaBoundAbs
section
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder

namespace Formalism.MainNotions.LeviCoordinates

theorem cn_kappaBoundAbs : ∀ C : ℝ, 1 ≤ C → ∃ n₀ : ℕ, ∀ (n p q J a f dN : ℕ) (v res ℓ : ℝ), n₀ ≤ n → p + q = n → q ^ 2 ≤ n →
    1 ≤ a → a ≤ J → J ≤ q → 1 ≤ f → dN ≤ 2 * J * n → 1 / 2 ≤ v → 0 < ℓ → Real.log ℓ ≤ n → 0 ≤ res →
    res ≤ (C * ℓ) ^ (2 * f) →
    v ^ (-((f : ℝ) * dN / 2)) * C ^ (J * n * f) * res ^ a * ((C / p) ^ (J * (p - J)) * (J : ℝ) ^ ((J : ℝ) ^ 2 / 2)) ^ f ≤
      Real.exp (-(1 / 8 * J * n * f * Real.log n)) := by
  intro C hC
  have hLc : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨max 16 ⌈Real.exp (14 * (1 + Real.log C))⌉₊, ?_⟩
  intro n p q J a f dN v res ℓ hn hpq hq ha haJ hJq hf hdN hv hℓ hlℓ hres0 hres
  have hn16 : (16:ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hn1 : Real.exp (14 * (1 + Real.log C)) ≤ n := Nat.ceil_le.mp ((le_max_right _ _).trans hn)
  have hn0 : (0:ℝ) < n := by linarith
  have hlog : 14 * (1 + Real.log C) ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hn1
  have hC0 : 0 < C := by linarith
  have hss : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = n := Real.mul_self_sqrt hn0.le
  have hs4 : 4 ≤ Real.sqrt (n:ℝ) := Real.le_sqrt_of_sq_le (by
    have : (4:ℝ) ^ 2 = 16 := by norm_num
    linarith)
  have hqs : (q:ℝ) ≤ Real.sqrt (n:ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hq)
  generalize Real.sqrt (n:ℝ) = s at *
  have hsn : s ≤ n / 4 := by nlinarith
  have hpr : (p:ℝ) = n - q := by
    have : ((p + q : ℕ):ℝ) = n := by exact_mod_cast hpq
    push_cast at this; linarith
  have hJq' : (J:ℝ) ≤ q := by exact_mod_cast hJq
  have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast ha.trans haJ
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg _
  have hJp : J ≤ p := by
    have : (J:ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hpJ : ((p - J : ℕ):ℝ) = p - J := Nat.cast_sub hJp
  have hp0 : (0:ℝ) < p := by linarith
  have t1 : v ^ (-((f:ℝ) * dN / 2)) ≤ Real.exp ((J:ℝ) * n * f) := by
    have hv0 : 0 < v := by linarith
    rw [Real.rpow_def_of_pos hv0]
    apply Real.exp_le_exp.mpr
    have hlv : 0 ≤ Real.log v + 1 := by
      have h1 : Real.log (1/2) ≤ Real.log v := Real.log_le_log (by norm_num) hv
      have h2 : Real.log (1/2) = - Real.log 2 := by rw [one_div, Real.log_inv]
      have := Real.log_two_lt_d9
      linarith
    have hd : (dN:ℝ) ≤ 2 * J * n := by exact_mod_cast hdN
    have h3 : 0 ≤ (f:ℝ) * dN / 2 := by positivity
    have h4 : (f:ℝ) * dN / 2 ≤ J * n * f := by
      calc (f:ℝ) * dN / 2 ≤ f * (2 * J * n) / 2 := by gcongr
        _ = _ := by ring
    nlinarith [mul_nonneg hlv h3]
  have t2 : C ^ (J * n * f) = Real.exp ((J:ℝ) * n * f * Real.log C) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hC0]; congr 1; push_cast; ring
  have t3 : res ^ a ≤ Real.exp (2 * f * J * (Real.log C + n)) := by
    have hCl : 0 < C * ℓ := by positivity
    calc res ^ a ≤ ((C * ℓ) ^ (2 * f)) ^ a := by gcongr
      _ = Real.exp (((2 * f * a : ℕ):ℝ) * Real.log (C * ℓ)) := by
          rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hCl, mul_comm]
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          rw [Real.log_mul hC0.ne' hℓ.ne']
          push_cast
          have ha' : (a:ℝ) ≤ J := by exact_mod_cast haJ
          have h0 : 0 ≤ Real.log C + n := by linarith
          calc 2 * (f:ℝ) * a * (Real.log C + Real.log ℓ) ≤ 2 * (f:ℝ) * a * (Real.log C + n) := by
                gcongr
            _ ≤ _ := by gcongr
  have t4 : (C / (p:ℝ)) ^ (J * (p - J))
      ≤ Real.exp (-((J:ℝ) * n / 2 * (Real.log n - 1 - Real.log C))) := by
    have hCp : 0 < C / (p:ℝ) := by positivity
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hCp]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div hC0.ne' hp0.ne', Nat.cast_mul, hpJ]
    have hlp : Real.log n - 1 ≤ Real.log p := by
      have h1 : Real.log (n / 2) ≤ Real.log p := Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_div hn0.ne' (by norm_num)] at h1
      have := Real.log_two_lt_d9; linarith
    have hl : 0 ≤ Real.log n - 1 - Real.log C := by linarith
    have hk : (J:ℝ) * n / 2 ≤ J * (p - J) := by
      have : (n:ℝ) / 2 ≤ p - J := by linarith
      nlinarith
    have hk0 : 0 ≤ (J:ℝ) * (p - J) := le_trans (by positivity) hk
    have a1 : (Real.log C - Real.log p) * ((J:ℝ) * (p - J))
        ≤ (-(Real.log n - 1 - Real.log C)) * ((J:ℝ) * (p - J)) :=
      mul_le_mul_of_nonneg_right (by linarith) hk0
    have a2 := mul_le_mul_of_nonneg_left hk hl
    linarith
  have t5 : (J:ℝ) ^ ((J:ℝ) ^ 2 / 2) ≤ Real.exp ((J:ℝ) * n / 8 * Real.log n) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    have hlJ : Real.log J ≤ Real.log n := Real.log_le_log (by linarith) (by linarith)
    have hlJ0 : 0 ≤ Real.log J := Real.log_nonneg hJ1
    have hJ2 : (J:ℝ) ^ 2 / 2 ≤ J * n / 8 := by nlinarith
    calc Real.log J * ((J:ℝ) ^ 2 / 2) ≤ Real.log n * ((J:ℝ) * n / 8) := by gcongr
      _ = _ := by ring
  have hv0 : 0 < v := by linarith
  calc v ^ (-((f:ℝ) * dN / 2)) * C ^ (J * n * f) * res ^ a
        * ((C / (p:ℝ)) ^ (J * (p - J)) * (J:ℝ) ^ ((J:ℝ) ^ 2 / 2)) ^ f
      ≤ Real.exp ((J:ℝ) * n * f) * Real.exp ((J:ℝ) * n * f * Real.log C)
        * Real.exp (2 * f * J * (Real.log C + n))
        * (Real.exp (-((J:ℝ) * n / 2 * (Real.log n - 1 - Real.log C)))
            * Real.exp ((J:ℝ) * n / 8 * Real.log n)) ^ f := by
        rw [t2]; gcongr
    _ = Real.exp ((J:ℝ) * n * f + (J:ℝ) * n * f * Real.log C + 2 * f * J * (Real.log C + n)
          + f * (-((J:ℝ) * n / 2 * (Real.log n - 1 - Real.log C)) + (J:ℝ) * n / 8 * Real.log n)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hw : 0 ≤ (J:ℝ) * n * f := by positivity
        have h2 : (f:ℝ) * J * Real.log C * 1 ≤ (f:ℝ) * J * Real.log C * n := by
          gcongr; linarith
        have h3 : (J:ℝ) * n * f * (14 * (1 + Real.log C)) ≤ (J:ℝ) * n * f * Real.log n := by gcongr
        linarith

end Formalism.MainNotions.LeviCoordinates
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.FramedTwoCoboundaries
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

section Tr

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

def conjHomeomorphOfUnitDet (P : Mat k r) (hu : IsUnit P.det) : Mat k r ≃ₜ Mat k r where
  toFun x := P⁻¹ * x * P
  invFun y := P * y * P⁻¹
  left_inv x := by
    have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    calc P * (P⁻¹ * x * P) * P⁻¹ = (P * P⁻¹) * x * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [h2]; simp
  right_inv y := by
    have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
    calc P⁻¹ * (P * y * P⁻¹) * P = (P⁻¹ * P) * y * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [h1]; simp
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def cayleyEmbedding (P : Mat k r) (g : Formalism.REAL.UJ ε) : Formalism.QuantumDeterminants.Mt k r := P⁻¹ * umat g * P

theorem cayleyEmbedding_measurable {P : Mat k r} (hP : IsCayleyU k r ε P) : MeasurableEmbedding (cayleyEmbedding (ε := ε) P) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => (conjHomeomorphOfUnitDet P hu) (umat g)) :=
    (conjHomeomorphOfUnitDet P hu).isClosedEmbedding.comp (Formalism.REAL.isClosedEmbeddingMatrix _ ε).1
  have h2 : Topology.IsClosedEmbedding (cayleyEmbedding (ε := ε) P) := h1
  exact h2.measurableEmbedding

theorem cayleyEmbedding_mem_unitary {P : Mat k r} (hP : IsCayleyU k r ε P) (g : Formalism.REAL.UJ ε) :
    Matrix.of (cayleyEmbedding P g) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have hg : (umat g)ᴴ * Formalism.REAL.Jm ε * umat g = Formalism.REAL.Jm ε := g.2
  show (P⁻¹ * umat g * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * umat g * P) = Formalism.QuantumDeterminants.Hpk k r
  rw [← hH]
  calc (P⁻¹ * umat g * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (P⁻¹ * umat g * P)
      = Pᴴ * ((umat g)ᴴ * ((P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹)) * umat g) * P := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * ((umat g)ᴴ * Formalism.REAL.Jm ε * umat g) * P := by rw [h2]; simp
    _ = Pᴴ * Formalism.REAL.Jm ε * P := by rw [hg]

theorem cayleyEmbedding_map_haar {P : Mat k r} (hP : IsCayleyU k r ε P) :
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ((Formalism.REAL.muG ε).map (cayleyEmbedding P)) := by
  have hemb := cayleyEmbedding_measurable hP
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  refine ⟨hemb.sigmaFinite_map, ?_, ?_, ?_⟩
  · intro h0
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h0
    exact (NeZero.ne (Formalism.REAL.muG ε)) h0
  · rw [hemb.map_apply]
    have : cayleyEmbedding P ⁻¹' {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = (∅ : Set (Formalism.REAL.UJ ε)) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact cayleyEmbedding_mem_unitary hP g
    rw [this, measure_empty]
  · intro s hs
    have hm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s) := by
      unfold Formalism.QuantumDeterminants.lmulM
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply]
      refine Finset.measurable_sum _ fun l _ => ?_
      have h0 : Measurable fun x : Formalism.QuantumDeterminants.Mt k r => x l j := by fun_prop
      exact h0.const_mul _
    rw [Measure.map_map hm hemb.measurable]
    set s' : Formalism.REAL.UJ ε := Formalism.REAL.indefiniteUnitaryMk ε (P * s * P⁻¹) (cayley_conj_mem_diagonal_model hP hs).1 with hs'
    have hcomp : Formalism.QuantumDeterminants.lmulM s ∘ cayleyEmbedding (ε := ε) P = cayleyEmbedding P ∘ fun g => s' * g := by
      funext g
      show s * (P⁻¹ * umat g * P) = P⁻¹ * (P * s * P⁻¹ * umat g) * P
      calc s * (P⁻¹ * umat g * P) = (P⁻¹ * P) * s * (P⁻¹ * umat g * P) := by rw [h1]; simp
        _ = P⁻¹ * (P * s * P⁻¹ * umat g) * P := by simp only [Matrix.mul_assoc]
    rw [hcomp, ← Measure.map_map hemb.measurable (measurable_const_mul s'), map_mul_left_eq_self]

theorem haar_eq_smul_cayley_image {P : Mat k r} (hP : IsCayleyU k r ε P) {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • (Formalism.REAL.muG ε).map (cayleyEmbedding P) := by
  obtain ⟨ν, hν⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨c1, a1, a2, e1⟩ := left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) hν hμ
  obtain ⟨c2, b1, b2, e2⟩ := left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) hν (cayleyEmbedding_map_haar hP)
  refine ⟨c1 / c2, ENNReal.div_ne_zero.2 ⟨a1, b2⟩, ENNReal.div_ne_top a2 b1, ?_⟩
  rw [e1, e2, smul_smul, ENNReal.div_mul_cancel b1 b2]

end Tr

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjFdegAllPos
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def SepF (X : CData) : Prop := SecondCountableTopology X.I.Gf

def TensRep (X : CData) : Prop :=
  (∀ g h, X.σs (g * h) = X.σs g ∘L X.σs h) ∧ X.σs 1 = 1 ∧ (∀ g (x : X.Hs), ‖X.σs g x‖ = ‖x‖) ∧
    ∀ x : X.Hs, Continuous fun g => X.σs g x

abbrev muInf (X : CData) : Measure X.I.Ginf := Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)

def SchurS (X : CData) : Prop :=
  ∀ x y : X.Hs, Integrable (fun g => ‖⟪y, X.σs g x⟫_ℂ‖ ^ 2) (muInf X) ∧
    ∫ g, ‖⟪y, X.σs g x⟫_ℂ‖ ^ 2 ∂(muInf X) = ‖x‖ ^ 2 * ‖y‖ ^ 2 / fdegAll X.I X.σ X.w

theorem pj_fdegAll_pos (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) :
    0 < fdegAll X.I X.σ X.w := by
  unfold fdegAll
  refine Finset.prod_pos fun v _ => ?_
  obtain ⟨d, hd⟩ := h1 X.I.n (X.I.ε v) (X.lam v) (hX.1.2.2.2.2.1 v) (X.H v) (X.σ v) (hX.2.1.1 v)
  rw [fdegOf_eq hd (hX.2.1.2.1 v).1]
  exact hd.1

theorem pj_norm_tens (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) : ‖X.tens X.w‖ = 1 := by
  have h := hX.2.1.2.2.1.1 X.w X.w
  have h2 : ∀ v, ⟪X.w v, X.w v⟫_ℂ = 1 := fun v => by
    rw [inner_self_eq_norm_sq_to_K, (hX.2.1.2.1 v).1]; simp
  simp only [h2, Finset.prod_const_one] at h
  have h3 : ‖X.tens X.w‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h]; simp
  have h4 : (‖X.tens X.w‖ - 1) * (‖X.tens X.w‖ + 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.1 h4 with h5 | h5
  · linarith
  · have := norm_nonneg (X.tens X.w); linarith

theorem pj_coef_tens (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (g : X.I.Ginf) :
    ⟪X.tens X.w, X.σs g (X.tens X.w)⟫_ℂ = ∏ v, coefOn (X.σ v) (X.w v) (X.w v) (g v) := by
  rw [hX.2.1.2.2.1.2.1 g X.w, hX.2.1.2.2.1.1]
  rfl

theorem pj_Re_proj (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (hR : RepA X) (hUm : UnimodF X) (hSep : SepF X) :
    IsStarProjection X.Re := by
  have : SecondCountableTopology X.I.Gf := hSep
  have : X.μf.IsMulRightInvariant := hUm
  have : X.μf.IsHaarMeasure := hX.2.1.2.2.2.1
  obtain ⟨hlc, hconv, hinv, hpos, -⟩ := hX.1.2.2.2.2.2.2.1
  obtain ⟨hei, heq⟩ := hX.2.1.2.2.2.2.2.2
  have hbd : ∀ y, ‖X.e y‖ ≤ (X.e 1).re := Formalism.HermitianLatticeCounting.Final.S7.posTypeBound X.I.Gf X.e (positive_type_notation_eq X.I hpos)
  by_cases h0 : (X.e 1).re = 0
  · have he0 : ∀ y, X.e y = 0 := fun y => norm_le_zero_iff.1 (h0 ▸ hbd y)
    have : X.Re = 0 := by
      ext1 y
      refine ext_inner_left ℂ fun x => ?_
      rw [heq]
      simp [he0]
    rw [this]
    exact ⟨IsIdempotentElem.zero, IsSelfAdjoint.zero _⟩
  · have h1 : 0 < ‖X.e 1‖ := by
      rw [norm_pos_iff]
      intro h
      exact h0 (by rw [h]; rfl)
    have hc : Continuous X.e := hlc.continuous
    have : X.μf.IsInvInvariant := inv_invariant_of_bi_invariant X.μf (fun y => ‖X.e y‖) hc.norm hei.norm h1
    let πf : X.I.Gf →* (X.L2 →L[ℂ] X.L2) :=
      { toFun := fun k => X.R (1, k)
        map_one' := hR.2.1
        map_mul' := fun a b => by
          rw [ContinuousLinearMap.mul_def, ← hR.1]
          simp }
    refine pj_starProj X.μf X.e hc hei (fun g => by rw [hinv, star_star]) (fun y => congrFun hconv y) πf
      (fun g x => hR.2.2.1 _ x) (fun x => (hR.2.2.2 x).comp (by fun_prop)) X.Re ⟨hei, heq⟩

theorem pj_main (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (hph : Integrable (phOf X.I X.σ X.w) (muInf X))
    (hR : RepA X) (hUm : UnimodF X) (hSep : SepF X) (hTR : TensRep X) (hS : SchurS X) :
    X.ProjStep ∧ X.CountedStep := by
  have : SecondCountableTopology X.I.Gf := hSep
  have : ∀ v, (Formalism.REAL.muG (X.I.ε v)).IsMulRightInvariant :=
    fun v => ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular X.I.n (X.I.ε v) g⟩
  have hd := pj_fdegAll_pos D h1 X hX
  set d := fdegAll X.I X.σ X.w with hddef
  have hw := pj_norm_tens X hX
  let σH : X.I.Ginf →* (X.Hs →L[ℂ] X.Hs) :=
    { toFun := X.σs, map_one' := hTR.2.1, map_mul' := fun a b => hTR.1 a b }
  let π1 : X.I.Ginf →* (X.L2 →L[ℂ] X.L2) :=
    { toFun := fun g => X.R (g, 1)
      map_one' := hR.2.1
      map_mul' := fun a b => by
        rw [ContinuousLinearMap.mul_def, ← hR.1]
        simp }
  have hphA : phOf X.I X.σ X.w = phA d σH (X.tens X.w) := by
    funext g
    unfold phOf phA
    rw [← pj_coef_tens X hX g]
    rfl
  have hcoef : Integrable (fun g => ⟪X.tens X.w, σH g (X.tens X.w)⟫_ℂ) (muInf X) := by
    have h2 : Integrable (fun g => ((d : ℂ)⁻¹) * phOf X.I X.σ X.w g) (muInf X) := hph.const_mul _
    have h3 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h2
    refine h3.congr (Filter.Eventually.of_forall fun g => ?_)
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [hphA]
    simp only [phA]
    rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
    simp
  obtain ⟨-, -, c3⟩ := abstract_projector_statements_hold D X.I.Ginf (muInf X) X.Hs σH hTR.2.2.1 hTR.2.2.2 d hd hS (X.tens X.w) hw hcoef
  obtain ⟨⟨P1, hP1⟩, c4⟩ := c3 X.L2 π1 (fun g x => hR.2.2.1 _ x) (fun x => (hR.2.2.2 x).comp (by fun_prop))
  obtain ⟨hP1s, -, -, hrange⟩ := c4 P1 hP1
  have hRe := pj_Re_proj X hX hR hUm hSep
  have hcyc := cyclic_of_schur_relation (muInf X) d hd σH hS (X.tens X.w) hw
  have hcomm : ∀ g : X.I.Ginf, X.Re ∘L X.R (g, 1) = X.R (g, 1) ∘L X.Re :=
    pj_comm X.μf X.R hR.1 X.e X.Re hX.2.1.2.2.2.2.2.2.2
  have key : ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → T = P1 ∘L X.Re ∧ T = X.Re ∘L P1 := by
    intro T hT
    refine pj_fubini (muInf X) X.μf X.R hR.1 hR.2.2.1
      (fun x y => (continuous_const.inner (hR.2.2.2 y)).aestronglyMeasurable)
      (phOf X.I X.σ X.w) X.e hT.1 P1 X.Re T ?_ hX.2.1.2.2.2.2.2.2.2 hT.2
    intro x y
    rw [hP1.2 x y, hphA]
    rfl
  have fin : ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → _ := fun T hT =>
    pj_counted X.σs (fun g => X.R (g, 1)) (X.tens X.w) P1 X.Re T hP1s hRe (key T hT).1 (key T hT).2 hrange hcomm hcyc
      (X.I.HomS X.σs X.μf X.fund X.R) (fun Ψ => Iff.rfl)
  exact ⟨fun T hT => (fin T hT).1, fun T hT _ => (fin T hT).2⟩

end Formalism.MainNotions.LeviCoordinates

end
end

