import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PBoundedHomogeneousZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

theorem BoundedHomogeneousZero.proof : BoundedHomogeneousZero.Statement.{u} := by
  intro X D g ⟨C, hC⟩ hD

  have iter : ∀ (k : ℕ) (x : X), g (D^[k] x) = 4 ^ k * g x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', hD, ih, pow_succ]
      ring
  funext x
  simp only [Pi.zero_apply]
  by_contra hx
  have hpos : 0 < |g x| := abs_pos.mpr hx
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C / |g x|) (by norm_num : (1 : ℝ) < 4)
  have hle : (4 : ℝ) ^ k * |g x| ≤ C := by
    have := hC (D^[k] x)
    rwa [iter, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ k)] at this
  have : C < (4 : ℝ) ^ k * |g x| := (div_lt_iff₀ hpos).mp hk
  linarith

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PMonomialNormLowerBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Finset

theorem MonomialNormLowerBound.factorial_le_prod_mul_pow (i : ℕ) (a : Fin i → ℕ) :
    (∑ j, a j).factorial ≤ (∏ j, (a j).factorial) * i ^ (∑ j, a j) := by
  have hsum := Finset.sum_pow_eq_sum_piAntidiag (univ : Finset (Fin i)) (fun _ => (1 : ℕ))
    (∑ j, a j)
  simp only [one_pow, prod_const_one, mul_one, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  have hmem : a ∈ piAntidiag (univ : Finset (Fin i)) (∑ j, a j) := by
    rw [mem_piAntidiag]; exact ⟨rfl, fun j _ => mem_univ j⟩
  have hle : Nat.multinomial univ a ≤ i ^ (∑ j, a j) := by
    rw [hsum]
    exact Finset.single_le_sum (f := fun k => Nat.multinomial univ k) (fun _ _ => Nat.zero_le _)
      hmem
  rw [← Nat.multinomial_spec]
  exact Nat.mul_le_mul_left _ hle

theorem MonomialNormLowerBound.factorial_le_pow_mul (i n : ℕ) (hi : 1 ≤ i) :
    (n + i - 1).factorial ≤ (n + i) ^ i * n.factorial * (i - 1).factorial := by
  have hk : n ≤ n + i - 1 := by omega
  have hsub : n + i - 1 - n = i - 1 := by omega
  have hspec := Nat.choose_mul_factorial_mul_factorial hk
  rw [hsub] at hspec
  have hch : (n + i - 1).choose n ≤ (n + i) ^ i := by
    rw [← Nat.choose_symm hk, hsub]
    calc (n + i - 1).choose (i - 1) ≤ (n + i - 1) ^ (i - 1) := Nat.choose_le_pow _ _
      _ ≤ (n + i) ^ (i - 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (n + i) ^ i := Nat.pow_le_pow_right (by omega) (by omega)
  calc (n + i - 1).factorial = (n + i - 1).choose n * n.factorial * (i - 1).factorial := hspec.symm
    _ ≤ (n + i) ^ i * n.factorial * (i - 1).factorial := by gcongr

theorem MonomialNormLowerBound.proof : MonomialNormLowerBound.Statement := by
  intro i hi n a ha

  have hnat : (n + i - 1).factorial ≤
      (∏ j, (a j).factorial) * (i - 1).factorial * (i ^ n * (n + i) ^ i) := by
    have h1 := MonomialNormLowerBound.factorial_le_prod_mul_pow i a
    rw [ha] at h1
    calc (n + i - 1).factorial ≤ (n + i) ^ i * n.factorial * (i - 1).factorial :=
          MonomialNormLowerBound.factorial_le_pow_mul i n hi
      _ ≤ (n + i) ^ i * ((∏ j, (a j).factorial) * i ^ n) * (i - 1).factorial := by gcongr
      _ = (∏ j, (a j).factorial) * (i - 1).factorial * (i ^ n * (n + i) ^ i) := by ring
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hA : (0 : ℝ) < (i : ℝ) ^ n * ((n : ℝ) + i) ^ i := by positivity
  have hF : (0 : ℝ) < ((n + i - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hreal : ((n + i - 1).factorial : ℝ) ≤
      (∏ j, ((a j).factorial : ℝ)) * ((i - 1).factorial : ℝ) * ((i : ℝ) ^ n * ((n : ℝ) + i) ^ i) := by
    exact_mod_cast hnat
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← mul_inv, inv_eq_one_div,
    div_le_div_iff₀ hA hF, one_mul]
  exact hreal

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PSlopeParameterChoice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

theorem SlopeParameterChoice.proof : SlopeParameterChoice.Statement := by
  intro C₀ C₂ hC₀ hC₂
  refine ⟨9 + C₀ + C₂, ?_⟩
  intro g h μ s hg hh hμ hs
  set K : ℝ := (⌈2 + (g : ℝ) ^ 2 + h⌉₊ : ℝ) with hKdef
  set G : ℝ := (g : ℝ) with hGdef
  set X : ℝ := 2 + G + h with hXdef
  set L : ℝ := Real.log X with hLdef
  have hG1 : (1 : ℝ) ≤ G := by rw [hGdef]; exact_mod_cast hg
  have hKlow : 2 + G ^ 2 + h ≤ K := Nat.le_ceil _
  have hKup : K < 2 + G ^ 2 + h + 1 := Nat.ceil_lt_add_one (by positivity)
  have hGG : G ≤ G ^ 2 := by nlinarith
  have hK3 : (3 : ℝ) ≤ K := by nlinarith
  have hGK : G ≤ K := by nlinarith
  have hhK : h ≤ K := by nlinarith
  have hX3 : (3 : ℝ) ≤ X := by rw [hXdef]; linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hKX : K ≤ X ^ 2 := by rw [hXdef]; nlinarith
  have hlev : (SlopeParameterChoice.level g h : ℝ) = 3 * K := by
    simp only [SlopeParameterChoice.level, hKdef]; push_cast; ring
  have hthird : SlopeParameterChoice.third g h = 3 * K ^ 2 := by
    simp only [SlopeParameterChoice.third, hlev]; ring
  rw [hthird, hlev] at hs

  have hL1 : (1 : ℝ) ≤ L := by
    have he : Real.exp 1 ≤ X := by
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at this

  have hLK : L ≤ K := by
    have : L ≤ X - 1 := Real.log_le_sub_one_of_pos hXpos
    linarith

  have hfirst : 1 / 2 * Real.log (3 * Real.exp 1 * (3 * K ^ 2) ^ 2) ≤ 6 * L := by
    have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have hKpos : (0 : ℝ) < K := by linarith
    have hpos : (0 : ℝ) < 3 * Real.exp 1 * (3 * K ^ 2) ^ 2 := by positivity
    have hK4 : K ^ 4 ≤ X ^ 8 := by
      calc K ^ 4 ≤ (X ^ 2) ^ 4 := pow_le_pow_left₀ hKpos.le hKX 4
        _ = X ^ 8 := by ring
    have hX4 : (81 : ℝ) ≤ X ^ 4 := by
      calc (81 : ℝ) = 3 ^ 4 := by norm_num
        _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX3 4
    have hle : 3 * Real.exp 1 * (3 * K ^ 2) ^ 2 ≤ X ^ 12 := by
      have h1 : 3 * Real.exp 1 * (3 * K ^ 2) ^ 2 ≤ 81 * K ^ 4 := by
        have : 3 * Real.exp 1 * (3 * K ^ 2) ^ 2 = 27 * Real.exp 1 * K ^ 4 := by ring
        rw [this]
        have : (0 : ℝ) ≤ K ^ 4 := by positivity
        nlinarith
      have h2 : 81 * K ^ 4 ≤ X ^ 4 * X ^ 8 :=
        mul_le_mul hX4 hK4 (by positivity) (by positivity)
      calc _ ≤ 81 * K ^ 4 := h1
        _ ≤ X ^ 4 * X ^ 8 := h2
        _ = X ^ 12 := by ring
    have := Real.log_le_log hpos hle
    rw [Real.log_pow] at this
    push_cast at this
    linarith

  have hsecond : 2 / (3 * K ^ 2) * (G * Real.log (3 * K) - μ) ≤ (3 + C₀ + C₂) * L := by
    have hKpos : (0 : ℝ) < K := by linarith
    have hlogm : Real.log (3 * K) ≤ 3 * K := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 3 * K); linarith
    have hKK : K ≤ K ^ 2 := by nlinarith
    have hY : G * Real.log (3 * K) - μ ≤ (7 / 2 + C₀ + C₂) * K ^ 2 := by
      have a1 : G * Real.log (3 * K) ≤ K * (3 * K) :=
        mul_le_mul hGK hlogm (Real.log_nonneg (by linarith)) hKpos.le
      have a3 : C₀ * G ≤ C₀ * K ^ 2 := mul_le_mul_of_nonneg_left (by linarith) hC₀
      have hGL : G * L ≤ K * K := mul_le_mul hGK hLK (by linarith) hKpos.le
      have a4 := mul_le_mul_of_nonneg_left hGL hC₂
      have a5 : C₂ * G * L = C₂ * (G * L) := by ring
      have a6 : K * (3 * K) = 3 * K ^ 2 := by ring
      have a7 : C₂ * (K * K) = C₂ * K ^ 2 := by ring
      have a8 : (7 / 2 + C₀ + C₂) * K ^ 2 = 3 * K ^ 2 + K ^ 2 / 2 + C₀ * K ^ 2 + C₂ * K ^ 2 := by ring
      rw [a8]
      linarith
    have hpos : (0 : ℝ) < 2 / (3 * K ^ 2) := by positivity
    calc 2 / (3 * K ^ 2) * (G * Real.log (3 * K) - μ)
        ≤ 2 / (3 * K ^ 2) * ((7 / 2 + C₀ + C₂) * K ^ 2) :=
          mul_le_mul_of_nonneg_left hY hpos.le
      _ = 2 / 3 * (7 / 2 + C₀ + C₂) := by field_simp
      _ ≤ 3 + C₀ + C₂ := by linarith
      _ ≤ (3 + C₀ + C₂) * L := le_mul_of_one_le_right (by linarith) hL1
  calc s ≤ _ := hs
    _ ≤ 6 * L + (3 + C₀ + C₂) * L := add_le_add hfirst hsecond
    _ = (9 + C₀ + C₂) * L := by ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PSupOfOrthonormalSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Finset

theorem SupOfOrthonormalSum.proof : SupOfOrthonormalSum.Statement := by
  intro V _ _ ι _ b p hb c

  have h1 : p (∑ i, c i • b i) ≤ ∑ i, ‖c i‖ := by
    refine (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_smul_eq_mul]
    calc ‖c i‖ * p (b i) ≤ ‖c i‖ * 1 := mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)
      _ = ‖c i‖ := mul_one _

  have h2 : (∑ i, ‖c i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ι) (fun _ => (1 : ℝ))
      (fun i => ‖c i‖)
    simpa [Finset.card_univ] using hcs
  have h3 : ∑ i, ‖c i‖ ≤ √(Fintype.card ι : ℝ) * √(∑ i, ‖c i‖ ^ 2) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.le_sqrt_of_sq_le h2
  exact h1.trans h3

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PThirdDifferenceConstant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ThirdDifferenceConstant.step_zero_of_bounded (u v K : ℝ)
    (h : ∀ n : ℕ, |u + n * v| ≤ K) : v = 0 := by
  by_contra hv
  have hv' : 0 < |v| := abs_pos.mpr hv
  obtain ⟨n, hn⟩ := exists_nat_gt ((K + |u|) / |v|)
  have h1 : |(n : ℝ) * v| ≤ K + |u| := by
    have : (n : ℝ) * v = (u + n * v) - u := by ring
    rw [this]
    linarith [abs_sub (u + n * v) u, h n]
  rw [abs_mul, Nat.abs_cast] at h1
  rw [div_lt_iff₀ hv'] at hn
  linarith

theorem ThirdDifferenceConstant.proof : ThirdDifferenceConstant.Statement := by
  intro A _ f ⟨C, hC⟩ hf
  have key : ∀ z : A, f z = f 0 := by
    intro z
    have hrec : ∀ n : ℕ, f ((n + 1 + 1) • z) - f ((n + 1) • z) =
        (f ((n + 1) • z) - f (n • z)) + (f (z + z) - 2 * f z + f 0) := by
      intro n
      have h := hf (n • z) z z
      have e1 : (n + 1) • z = n • z + z := succ_nsmul z n
      have e2 : (n + 1 + 1) • z = n • z + z + z := by rw [succ_nsmul, succ_nsmul]
      rw [e2, e1]
      linarith
    have hd : ∀ n : ℕ, f ((n + 1) • z) - f (n • z) =
        (f z - f 0) + n * (f (z + z) - 2 * f z + f 0) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih => rw [hrec k, ih]; push_cast; ring
    have hc0 : f (z + z) - 2 * f z + f 0 = 0 := by
      refine ThirdDifferenceConstant.step_zero_of_bounded (f z - f 0) _ (C + C) (fun n => ?_)
      rw [← hd n]
      linarith [abs_sub (f ((n + 1) • z)) (f (n • z)), hC ((n + 1) • z), hC (n • z)]
    have ha : ∀ n : ℕ, f (n • z) = f 0 + n * (f z - f 0) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have := hd k
        rw [hc0, mul_zero, add_zero] at this
        push_cast
        linarith
    have h0 : f z - f 0 = 0 :=
      ThirdDifferenceConstant.step_zero_of_bounded (f 0) _ C (fun n => by rw [← ha n]; exact hC _)
    linarith
  intro x y
  rw [key x, key y]

end GroundTheory.Heights₂.Heights
end

