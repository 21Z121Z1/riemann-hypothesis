import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLStar
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem lstar_ineqs_of_le (m b b' Λ S η t P : ℝ) (hm : 1 ≤ m) (hΛ0 : 0 < Λ) (hΛ : Λ ≤ P) (hS : S ≤ P)
    (hη : η ≤ P) (ht : t ≤ P) (hP : 100 ≤ P) (h1 : P ^ 2 ≤ b') (h2 : b' * P ^ 2 ≤ b) :
    b' + S + η + b / (m * b / Λ) < m * b / Λ ∧ 2 * η + t + 8 * b / (m * b / Λ) + 7 < m * b / Λ := by
  have hPb : P ≤ b' := by nlinarith
  have hb'0 : 0 < b' := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) h2
  have hm0 : 0 < m := by linarith
  have e1 : b / (m * b / Λ) = Λ / m := by field_simp
  have e2 : 8 * b / (m * b / Λ) = 8 * (Λ / m) := by field_simp
  have h3 : Λ / m ≤ P := (div_le_self hΛ0.le hm).trans hΛ
  have h4 : 100 * b' ≤ m * b / Λ := by
    rw [le_div_iff₀ hΛ0]
    have a1 : 100 * Λ ≤ P ^ 2 := by nlinarith
    have a2 : b' * (100 * Λ) ≤ b' * P ^ 2 := mul_le_mul_of_nonneg_left a1 hb'0.le
    have a3 : b ≤ m * b := le_mul_of_one_le_left hb0.le hm
    nlinarith
  rw [e1, e2]
  constructor <;> linarith

theorem lstar_den_le (n t N l k m Δ h Q : ℝ) (hQ : 100 ≤ Q) (n0 : 0 ≤ n) (t0 : 0 ≤ t) (N0 : 0 ≤ N) (l0 : 0 ≤ l)
    (k0 : 0 ≤ k) (m0 : 0 ≤ m) (Δ0 : 0 ≤ Δ) (h0 : 0 ≤ h) (hn : n ≤ Q) (ht : t ≤ Q) (hN : N ≤ Q) (hl : l ≤ Q)
    (hk : k ≤ Q) (hm : m ≤ Q) (hΔ : Δ ≤ 2 * Q) (hh : h ≤ 4 * Q) :
    n * t ^ 2 * (N + t) * l ^ 2 + k * n ^ 2 * (k * (4 * Δ) + t + l) ≤ Q ^ 7 ∧ k * (4 * Δ) ≤ Q ^ 7 ∧
      m * h ≤ Q ^ 7 ∧ t ≤ Q ^ 7 ∧ 100 ≤ Q ^ 7 := by
  have Q1 : 1 ≤ Q := by linarith
  have Q0 : 0 ≤ Q := by linarith
  have p1 : Q ≤ Q ^ 6 := le_self_pow₀ Q1 (by norm_num)
  have p2 : Q ^ 2 ≤ Q ^ 6 := pow_le_pow_right₀ Q1 (by norm_num)
  have p4 : Q ^ 4 ≤ Q ^ 6 := pow_le_pow_right₀ Q1 (by norm_num)
  have p5 : Q ^ 5 ≤ Q ^ 6 := pow_le_pow_right₀ Q1 (by norm_num)
  have p7 : 100 * Q ^ 6 ≤ Q ^ 7 := by
    rw [show Q ^ 7 = Q * Q ^ 6 by ring]; gcongr
  have a1 : n * t ^ 2 * (N + t) * l ^ 2 ≤ Q * Q ^ 2 * (Q + Q) * Q ^ 2 := by gcongr
  have a2 : k * n ^ 2 * (k * (4 * Δ) + t + l) ≤ Q * Q ^ 2 * (Q * (4 * (2 * Q)) + Q + Q) := by gcongr
  have a3 : k * (4 * Δ) ≤ Q * (4 * (2 * Q)) := by gcongr
  have a4 : m * h ≤ Q * (4 * Q) := by gcongr
  have e1 : Q * Q ^ 2 * (Q + Q) * Q ^ 2 = 2 * Q ^ 6 := by ring
  have e2 : Q * Q ^ 2 * (Q * (4 * (2 * Q)) + Q + Q) = 8 * Q ^ 5 + 2 * Q ^ 4 := by ring
  have e3 : Q * (4 * (2 * Q)) = 8 * Q ^ 2 := by ring
  have e4 : Q * (4 * Q) = 4 * Q ^ 2 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem szRow_lStar : SzRow (fun _ D L => (L.sc.b' + L.Sc + L.etaSz + L.sc.b / lStar L < lStar L) ∧
    (2 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 7 < lStar L)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD hcD => ⟨0, fun ch hch => ?_⟩⟩
  have hcD' : 0 ≤ cD := hcD
  have hch' : 0 ≤ ch := hch
  obtain ⟨x1, h1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  obtain ⟨x2, h2⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps ((cD + ch + 402) * 14) 1 he0 one_pos
  refine ⟨max 100 (max x1 x2), fun D L hL hx hV => ?_⟩
  have hx0 : 100 ≤ L.sc.x := (le_max_left _ _).trans hx
  have hx1 : x1 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx2 : x2 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  obtain ⟨hf, hm, hr, hkr, -, hl, hl1, -, -, -, -, -, -, ht, hN, -, -⟩ := h1 L.sc D.R hL hx1 hV.ranks
  obtain ⟨-, -, -, hb1, hb2, -, -⟩ := h2 L.sc hL hx2
  have x1le : 1 ≤ L.sc.x := by linarith
  set Q : ℝ := L.sc.x ^ (cD + ch + 402) with hQ
  have hpow : ∀ c : ℝ, c ≤ cD + ch + 402 → L.sc.x ^ c ≤ Q := fun c hc =>
    Real.rpow_le_rpow_of_exponent_le x1le hc
  have hxQ : L.sc.x ≤ Q := by
    have := hpow 1 (by linarith); rwa [Real.rpow_one] at this
  have hQ14 : L.sc.x ^ ((cD + ch + 402) * 14) = (Q ^ 7) ^ 2 := by
    rw [Real.rpow_mul (by linarith), ← pow_mul, ← hQ]
    exact_mod_cast Real.rpow_natCast Q 14
  rw [hQ14] at hb1 hb2
  rw [sub_self, Real.rpow_zero, one_mul] at hb2
  have hQ100 : 100 ≤ Q := hx0.trans hxQ
  have hnQ : (D.R.n : ℝ) ≤ Q := by
    have a : (D.R.n : ℝ) ≤ D.R.f := by
      have : D.R.n ≤ D.R.f := by unfold Ranks.f; omega
      exact_mod_cast this
    exact a.trans (hf.trans (hpow 3 (by linarith)))
  have hkQ : (D.R.k : ℝ) ≤ Q := by
    have a : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact a.trans (hr.trans (hpow 5 (by linarith)))
  have htQ : (D.R.t : ℝ) ≤ Q := ht.trans (hpow 401 (by linarith))
  have hNQ : (D.R.N D.R.m : ℝ) ≤ Q := hN.trans (hpow 402 (by linarith))
  have hΔ : (Delv L.sc cD : ℝ) ≤ 2 * Q := by
    have a := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by positivity)
    have b := hpow cD (by linarith)
    unfold Delv; linarith
  have hh : (h0v L.sc ch : ℝ) ≤ 4 * Q := by
    have a := Nat.ceil_lt_add_one (a := L.sc.x ^ ch) (by positivity)
    have b := hpow ch (by linarith)
    unfold h0v; push_cast; linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * (Delv L.sc cD : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; push_cast; rfl
  obtain ⟨c1, c2, c3, c4, c5⟩ := lstar_den_le (D.R.n : ℝ) D.R.t (D.R.N D.R.m) L.sc.L D.R.k D.R.m
    (Delv L.sc cD) (h0v L.sc ch) Q hQ100 (by positivity) (by positivity) (by positivity) (by linarith)
    (by positivity) (by positivity) (by positivity) (by positivity) hnQ htQ hNQ (hl.trans hxQ) hkQ
    (hm.trans hxQ) hΔ hh
  rw [← hSc] at c1 c2
  rw [← hV.eta_eq] at c3
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hn0 : (0 : ℝ) < D.R.n := by unfold Ranks.n; positivity
  have ht0 : (0 : ℝ) < D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (by omega : 0 < D.R.t)
  have hl0 : 0 < L.sc.L := by linarith
  have hSc0 : 0 ≤ L.Sc := by rw [hSc]; positivity
  unfold lStar
  exact lstar_ineqs_of_le _ _ _ _ _ _ _ (Q ^ 7) hm1 (by positivity) c1 c2 c3 c4 c5 hb2 hb1

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNodeGap
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem nodeGap_poly {x Y n f m k r t N M L S c₁ c₂ H : ℝ} (hx : 200 ≤ x) (hY : 1 ≤ Y)
    (hn0 : 0 ≤ n) (hf0 : 0 ≤ f) (hm1 : 1 ≤ m) (hk0 : 0 ≤ k) (hr0 : 0 ≤ r) (ht0 : 0 ≤ t) (hN0 : 0 ≤ N) (hM0 : 0 ≤ M)
    (hL0 : 0 ≤ L) (hS0 : 0 ≤ S)
    (hn : n ≤ x ^ 3) (hf : f ≤ x ^ 3) (hm : m ≤ x) (hk : k ≤ x ^ 5) (hr : r ≤ x ^ 5) (ht : t ≤ x ^ 401)
    (hN : N ≤ x ^ 402) (hM : M ≤ x ^ 402) (hL : L ≤ x) (hS : S ≤ x ^ 6 * Y) (h₁ : c₁ ≤ x) (h₂ : c₂ ≤ x)
    (hH : x ^ 1300 * Y ≤ H) :
    12 * ((n * t ^ 2 * (N + t) * L ^ 2 + k * n ^ 2 * (S + t + L)) / m) + 2 * t + 8 ≤ H ∧ k * t * L ≤ H ∧
      c₁ * r ^ 19 * f ^ 5 * L ≤ H ∧ 4 * N ^ 3 + 2 * t + 6 ≤ H ∧ c₂ * k * m ^ ((9 : ℝ) / 2) ≤ H ∧
      2 * M ^ 3 + t + 3 ≤ H ∧ 120 * r * m ^ ((3 : ℝ) / 2) ≤ H ∧ N * m ^ 10 ≤ H ∧ 16 * m * N ≤ H := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have mono : ∀ a b : ℕ, a ≤ b → x ^ a ≤ x ^ b := fun a b h => pow_le_pow_right₀ hx1 h
  have hP : 0 ≤ x ^ 1299 := by positivity
  have hQ : x ^ 1299 ≤ x ^ 1299 * Y := le_mul_of_one_le_right hP hY
  have hH' : 200 * (x ^ 1299 * Y) ≤ H := by
    refine le_trans ?_ hH
    have : x ^ 1300 * Y = x * (x ^ 1299 * Y) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hx (by positivity)
  have h1 : 1 ≤ x ^ 1299 := one_le_pow₀ hx1
  have ht' : t ≤ x ^ 1299 := ht.trans (mono _ _ (by norm_num))
  have hm92 : m ^ ((9 : ℝ) / 2) ≤ x ^ 5 := by
    calc m ^ ((9 : ℝ) / 2) ≤ m ^ ((5 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = m ^ 5 := Real.rpow_natCast _ _
      _ ≤ x ^ 5 := by gcongr
  have hm32 : m ^ ((3 : ℝ) / 2) ≤ x ^ 2 := by
    calc m ^ ((3 : ℝ) / 2) ≤ m ^ ((2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = m ^ 2 := Real.rpow_natCast _ _
      _ ≤ x ^ 2 := by gcongr
  have hm0 : 0 ≤ m := by linarith
  have hN3 : N ^ 3 ≤ x ^ 1299 := by
    calc N ^ 3 ≤ (x ^ 402) ^ 3 := by gcongr
      _ = x ^ 1206 := by ring
      _ ≤ _ := mono _ _ (by norm_num)
  have hM3 : M ^ 3 ≤ x ^ 1299 := by
    calc M ^ 3 ≤ (x ^ 402) ^ 3 := by gcongr
      _ = x ^ 1206 := by ring
      _ ≤ _ := mono _ _ (by norm_num)
  refine ⟨?_, ?_, ?_, by linarith, ?_, by linarith, ?_, ?_, ?_⟩
  · have hA : n * t ^ 2 * (N + t) * L ^ 2 ≤ 2 * x ^ 1299 := by
      have ht2 : t ≤ x ^ 402 := ht.trans (mono _ _ (by norm_num))
      calc n * t ^ 2 * (N + t) * L ^ 2 ≤ x ^ 3 * (x ^ 401) ^ 2 * (x ^ 402 + x ^ 402) * x ^ 2 := by gcongr
        _ = 2 * x ^ 1209 := by ring
        _ ≤ _ := by have := mono 1209 1299 (by norm_num); linarith
    have hB : k * n ^ 2 * (S + t + L) ≤ 3 * (x ^ 1299 * Y) := by
      have hY0 : 0 ≤ Y := by linarith
      have hW : x ^ 401 ≤ x ^ 401 * Y := le_mul_of_one_le_right (by positivity) hY
      have hS' : S ≤ x ^ 401 * Y := hS.trans (mul_le_mul_of_nonneg_right (mono _ _ (by norm_num)) hY0)
      have ht2 : t ≤ x ^ 401 * Y := ht.trans hW
      have hL2 : L ≤ x ^ 401 * Y := by
        have := mono 1 401 (by norm_num)
        rw [pow_one] at this
        exact hL.trans (this.trans hW)
      calc k * n ^ 2 * (S + t + L) ≤ x ^ 5 * (x ^ 3) ^ 2 * (x ^ 401 * Y + x ^ 401 * Y + x ^ 401 * Y) := by gcongr
        _ = 3 * (x ^ 412 * Y) := by ring
        _ ≤ _ := by
          have := mul_le_mul_of_nonneg_right (mono 412 1299 (by norm_num)) hY0
          linarith
    have hD : (n * t ^ 2 * (N + t) * L ^ 2 + k * n ^ 2 * (S + t + L)) / m ≤
        n * t ^ 2 * (N + t) * L ^ 2 + k * n ^ 2 * (S + t + L) := div_le_self (by positivity) hm1
    linarith
  · have : k * t * L ≤ x ^ 1299 := by
      calc k * t * L ≤ x ^ 5 * x ^ 401 * x := by gcongr
        _ = x ^ 407 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : c₁ * r ^ 19 * f ^ 5 * L ≤ x ^ 1299 := by
      calc c₁ * r ^ 19 * f ^ 5 * L ≤ x * (x ^ 5) ^ 19 * (x ^ 3) ^ 5 * x := by gcongr
        _ = x ^ 112 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : c₂ * k * m ^ ((9 : ℝ) / 2) ≤ x ^ 1299 := by
      calc c₂ * k * m ^ ((9 : ℝ) / 2) ≤ x * x ^ 5 * x ^ 5 := by gcongr
        _ = x ^ 11 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : r * m ^ ((3 : ℝ) / 2) ≤ x ^ 1299 := by
      calc r * m ^ ((3 : ℝ) / 2) ≤ x ^ 5 * x ^ 2 := by gcongr
        _ = x ^ 7 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : N * m ^ 10 ≤ x ^ 1299 := by
      calc N * m ^ 10 ≤ x ^ 402 * x ^ 10 := by gcongr
        _ = x ^ 412 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : m * N ≤ x ^ 1299 := by
      calc m * N ≤ x * x ^ 402 := by gcongr
        _ = x ^ 403 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith

theorem szRow_nodeGap : SzRow (fun C D L => (12 * L.sc.b / lStar L + 2 * D.R.t + 8 ≤ h0 L ∧ (D.R.k : ℝ) * D.R.t * L.sc.L ≤ h0 L ∧ C.P.Ch0r * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L ≤ h0 L ∧ ((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ h0 L ∧ 4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 ≤ h0 L ∧ C.P.Ch0k * D.R.k * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) ≤ h0 L ∧ 2 * (Mrt D : ℝ) ^ 3 + D.R.t + 3 ≤ h0 L ∧ 120 * (D.R.r : ℝ) * (qSig D : ℝ) ^ ((3 : ℝ) / 2) ≤ h0 L ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ h0 L ∧ 16 * (qSig D : ℝ) * D.R.N D.R.m ≤ h0 L)) := by
  intro eps he0 he1 C _
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨0, fun cD hcD => ⟨max (1300 + cD) (406 * |C.P.CCount|), fun ch hch =>
    ⟨max (max x1 200) (max C.P.Ch0r C.P.Ch0k), fun D L hε hx hV => ?_⟩⟩⟩
  simp only [max_le_iff, ge_iff_le] at hx hch
  obtain ⟨⟨hxa, hxb⟩, hxc, hxd⟩ := hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, ht, hN, -, -⟩ := hx1 L.sc D.R hε hxa hV.ranks
  have hxone : 1 ≤ L.sc.x := by linarith
  have hxpos : 0 < L.sc.x := by linarith
  have cast : ∀ a : ℕ, L.sc.x ^ (a : ℝ) = L.sc.x ^ a := fun a => Real.rpow_natCast _ _
  have hf' : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by rw [← cast]; exact_mod_cast hf
  have hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5 := by rw [← cast]; exact_mod_cast hr
  have ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by rw [← cast]; exact_mod_cast ht
  have hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ 402 := by rw [← cast]; exact_mod_cast hN
  have hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := le_trans (by exact_mod_cast hkr) hr'
  have hnf : (D.R.n : ℝ) ≤ D.R.f := by
    have : D.R.n ≤ D.R.f := by unfold Ranks.f; omega
    exact_mod_cast this
  have hm2 := D.R.two_le_m
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hMN : (Mrt D : ℝ) ≤ D.R.N D.R.m := by
    have : Mrt D ≤ D.R.N D.R.m := by
      unfold Mrt Ranks.N Ranks.r
      rw [Nat.mul_add, Nat.mul_one]; omega
    exact_mod_cast this
  have hY : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hxone hcD
  have hDel : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD := by
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    unfold Delv; linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; push_cast; ring
  have hS0 : 0 ≤ L.Sc := by rw [hSc]; positivity
  have hS : L.Sc ≤ L.sc.x ^ 6 * L.sc.x ^ cD := by
    rw [hSc]
    calc (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) ≤ L.sc.x ^ 5 * (4 * (2 * L.sc.x ^ cD)) := by gcongr
      _ = L.sc.x ^ 5 * 8 * L.sc.x ^ cD := by ring
      _ ≤ L.sc.x ^ 5 * L.sc.x * L.sc.x ^ cD := by gcongr; linarith
      _ = _ := by ring
  have hh0 : L.sc.x ^ ch ≤ h0 L := by
    have e : h0 L = (h0v L.sc ch : ℝ) := by
      unfold h0; rw [hV.eta_eq]; field_simp
    have := Nat.le_ceil (L.sc.x ^ ch)
    have h0' : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℕ) := Nat.cast_nonneg _
    rw [e]; unfold h0v; push_cast; linarith
  have hH : L.sc.x ^ 1300 * L.sc.x ^ cD ≤ h0 L := by
    refine le_trans ?_ hh0
    rw [← cast, ← Real.rpow_add hxpos]
    exact Real.rpow_le_rpow_of_exponent_le hxone (by exact_mod_cast hch.1)
  obtain ⟨a1, a2, a3, a5, a6, a7, a8, a9, a10⟩ := nodeGap_poly (c₁ := C.P.Ch0r) (c₂ := C.P.Ch0k) hxb hY
    (Nat.cast_nonneg D.R.n) (Nat.cast_nonneg D.R.f) hm1 (Nat.cast_nonneg D.R.k) (Nat.cast_nonneg D.R.r)
    (Nat.cast_nonneg D.R.t) (Nat.cast_nonneg (D.R.N D.R.m)) (Nat.cast_nonneg (Mrt D)) (by linarith : 0 ≤ L.sc.L) hS0
    (hnf.trans hf') hf' hm hk' hr' ht' hN' (hMN.trans hN') hL hS hxc hxd hH
  refine ⟨?_, a2, a3, ?_, a5, a6, a7, a8, a9, a10⟩
  · have hb : 0 < L.sc.b := by unfold Scale.b; positivity
    refine le_trans (le_of_eq ?_) a1
    unfold lStar
    rw [div_div_eq_mul_div]
    field_simp
  · have hf1 : (1 : ℝ) ≤ D.R.f := by
      have : 1 ≤ D.R.f := le_trans (by omega) D.R.m_le_f
      exact_mod_cast this
    have hN1 : (1 : ℝ) ≤ D.R.N D.R.m := by
      have := D.R.m_add_three_le_k
      have : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; omega
      exact_mod_cast this
    have hB1 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) * D.R.f * L.sc.L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN1 hf1) hL1
    have hB : (D.R.N D.R.m : ℝ) * D.R.f * L.sc.L ≤ L.sc.x ^ (406 : ℝ) := by
      calc (D.R.N D.R.m : ℝ) * D.R.f * L.sc.L ≤ L.sc.x ^ 402 * L.sc.x ^ 3 * L.sc.x := by gcongr
        _ = L.sc.x ^ 406 := by ring
        _ = _ := by rw [← cast]; norm_num
    calc _ ≤ ((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ |C.P.CCount| :=
          Real.rpow_le_rpow_of_exponent_le hB1 (le_abs_self _)
      _ ≤ (L.sc.x ^ (406 : ℝ)) ^ |C.P.CCount| := Real.rpow_le_rpow (by linarith) hB (abs_nonneg _)
      _ = L.sc.x ^ (406 * |C.P.CCount|) := (Real.rpow_mul hxpos.le _ _).symm
      _ ≤ L.sc.x ^ ch := Real.rpow_le_rpow_of_exponent_le hxone hch.2
      _ ≤ _ := hh0

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTOLower
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem factor_products_le_rpow_three_hundred_seventy_seven (x c W Dy k f m d : ℝ) (hx : 1 ≤ x) (hc0 : 0 ≤ c) (hc : c ^ 4 ≤ x)
    (hW0 : 0 ≤ W) (hW : W ^ 4 ≤ x ^ 330) (hD0 : 0 ≤ Dy) (hD : Dy ≤ x ^ 12)
    (hk0 : 0 ≤ k) (hk : k ≤ x ^ 5) (hf0 : 0 ≤ f) (hm : 1 ≤ m) (hkf : k * f / m ≤ x ^ 7)
    (hd : 1 / x ≤ d) :
    (c * W) ^ 4 * Dy ^ 3 * k * f * x / (m * d) ≤ x ^ 377 ∧ Dy * k / m ≤ x ^ 377 := by
  have hx0 : 0 < x := by linarith
  have hm0 : 0 < m := by linarith
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hd' : 1 / d ≤ x := by
    rw [div_le_iff₀ hd0]
    rw [div_le_iff₀ hx0] at hd
    linarith
  refine ⟨?_, ?_⟩
  · calc (c * W) ^ 4 * Dy ^ 3 * k * f * x / (m * d)
        = c ^ 4 * W ^ 4 * Dy ^ 3 * (k * f / m) * x * (1 / d) := by field_simp
      _ ≤ x * x ^ 330 * (x ^ 12) ^ 3 * x ^ 7 * x * x := by gcongr
      _ = x ^ 376 := by ring
      _ ≤ x ^ 377 := pow_le_pow_right₀ hx (by norm_num)
  · calc Dy * k / m ≤ Dy * k := div_le_self (by positivity) hm
      _ ≤ x ^ 12 * x ^ 5 := by gcongr
      _ = x ^ 17 := by ring
      _ ≤ x ^ 377 := pow_le_pow_right₀ hx (by norm_num)

theorem szRow_TO_lower : SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ^ 4 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ C.T.Cp / ((D.R.m : ℝ) * L.de2) ≤ ((TOv L.sc : ℕ) : ℝ)) ∧ (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) * D.R.k / D.R.m ≤ ((TOv L.sc : ℕ) : ℝ))) := by
  intro eps he he' C hC
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  have hCp : C.T.Cp = 1 := hC.2.2.2.2.2.2.2.1
  have heP : C.T.eP = 12 := hC.2.2.2.2.2.2.2.2.1
  have hCP : 1000 ≤ C.T.CP := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 (C.T.CP ^ 4), ?_⟩⟩⟩
  intro D L hLe hx V
  simp only [max_le_iff] at hx
  obtain ⟨hxa, hxP⟩ := hx
  obtain ⟨-, -, hr, hkr, -, -, hL1, -, hZ, hD, hkf, -⟩ := hx1 L.sc D.R hLe hxa V.ranks
  have hxx := L.sc.one_lt_alt
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := by unfold Ranks.n; positivity
    exact_mod_cast this
  have hd : L.sc.x ^ (-L.sc.eps) ≤ L.de2 := by
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn]
    exact V.host.2.2.1
  have hT : L.sc.x ^ (377 : ℝ) ≤ ((TOv L.sc : ℕ) : ℝ) := Nat.le_ceil _
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hZ0 : 0 ≤ zBase L := by
    unfold zBase
    have : (0:ℝ) ≤ L.sc.L := by linarith
    positivity
  have hZ' : zBase L ≤ L.sc.x ^ ((687 : ℝ) / 100) := hZ
  set x := L.sc.x with hxdef
  have hx1' : 1 ≤ x := hxx.le
  have hx0 : 0 < x := by linarith
  have cast : ∀ n : ℕ, x ^ ((n : ℕ) : ℝ) = x ^ n := fun n => Real.rpow_natCast x n
  have hPe : zBase L ^ C.T.eP = zBase L ^ (12 : ℕ) := by
    rw [heP]; first | rfl | exact_mod_cast Real.rpow_natCast _ 12
  have hd' : 1 / x ≤ L.de2 := by
    refine le_trans ?_ hd
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx1' (by rw [hLe]; linarith)
  have hW : (zBase L ^ (12 : ℕ)) ^ 4 ≤ x ^ 330 := by
    calc (zBase L ^ (12 : ℕ)) ^ 4 = zBase L ^ 48 := by ring
      _ ≤ (x ^ ((687 : ℝ) / 100)) ^ 48 := by gcongr
      _ = x ^ ((687 : ℝ) / 100 * ((48 : ℕ) : ℝ)) := (Real.rpow_mul_natCast hx0.le _ _).symm
      _ ≤ x ^ ((330 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num)
      _ = x ^ 330 := cast 330
  have hk : (D.R.k : ℝ) ≤ x ^ 5 := by
    have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact this.trans (by exact_mod_cast hr)
  have hT' : x ^ 377 ≤ ((TOv L.sc : ℕ) : ℝ) := by exact_mod_cast hT
  obtain ⟨a, b⟩ := factor_products_le_rpow_three_hundred_seventy_seven x C.T.CP (zBase L ^ (12 : ℕ)) ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ)
    D.R.k D.R.f D.R.m L.de2 hx1' (by linarith) hxP (by positivity) hW (Nat.cast_nonneg _)
    (by exact_mod_cast hD) (Nat.cast_nonneg _) hk (Nat.cast_nonneg _) (by linarith)
    (by exact_mod_cast hkf) hd'
  refine ⟨?_, b.trans hT'⟩
  rw [hPe, hCp]
  first
    | (rw [Real.rpow_one]; exact a.trans hT')
    | (rw [pow_one]; exact a.trans hT')

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTypePrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_typePrimes : SzRow (fun C D L => (∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧ (D.R.N D.R.m : ℝ) ^ 4 * (condE D : ℝ) ^ C.P.CY ≤ Y ^ ((1 : ℝ) / 4) ∧ Real.log Y ≤ C.P.CYL * L.sc.L ∧ ∀ i, Y ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ 2 * Y)) := by
  intro eps he he' C hC
  obtain ⟨-, -, -, -, -, hYL, -, -, -, -, -, -, hpde, -⟩ := hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x1, h1⟩ := GlobalTheory.EX.hostBounds eps C.P.Cpde he he' hpde
  obtain ⟨x2, h2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  obtain ⟨x3, h3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 0 eps 1608 1 he
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (eps / 5) eps (2 * |C.P.CY|) 2 (by linarith)
  refine ⟨max (max x1 x2) (max x3 x4), fun D L hL hx V => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  obtain ⟨-, -, -, -, hc, -⟩ := h1 L.sc D.R D.host hL hx1 V.ranks V.host
  obtain ⟨-, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, hN, -⟩ := h2 L.sc D.R hL hx2 V.ranks
  have h3' := h3 _ hx3
  have h4' := h4 _ hx4
  rw [Real.rpow_zero, mul_one, pow_one] at h3'
  rw [← hL] at h3' h4'
  have hLdef : L.sc.L = L.sc.x ^ L.sc.eps := rfl
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  rw [← hLdef] at h3' h4'
  have hx1' : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlog : 0 < Real.log L.sc.x := Real.log_pos hx1'
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have h := V.ranks.2.2.1.1
    have : 1 ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps) := Real.one_le_rpow hx1'.le (by rw [hL]; linarith)
    linarith
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hbpos : 0 < L.sc.b := by rw [hb]; exact Real.exp_pos _
  have hkb : 0 < (D.R.k : ℝ) * L.sc.b := by positivity
  refine ⟨((D.R.k : ℝ) * L.sc.b) ^ 8, le_rfl, ?_, ?_, V.host.2.2.2.2.1⟩
  · have hY : (((D.R.k : ℝ) * L.sc.b) ^ 8) ^ ((1 : ℝ) / 4) = ((D.R.k : ℝ) * L.sc.b) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hkb.le, ← Real.rpow_natCast]
      norm_num
    rw [hY]
    have hcE : ((condE D : ℕ) : ℝ) = (D.host.QS : ℝ) * D.host.q * D.host.d := by
      unfold condE; push_cast; ring
    have hc1 : (1 : ℝ) ≤ (condE D : ℝ) := by
      have : condE D ≠ 0 := by
        have hQS := D.host.QS_pos
        have hq0 := D.host.hyp.1.pos
        have hd0 := D.host.hyp.2.1.pos
        unfold condE; positivity
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    rw [← hcE] at hc
    have hlc : 0 ≤ Real.log (condE D : ℝ) := Real.log_nonneg hc1
    have hA : (condE D : ℝ) ^ C.P.CY ≤ L.sc.b := by
      rw [Real.rpow_def_of_pos (by linarith), hb]
      apply Real.exp_le_exp.mpr
      calc Real.log (condE D : ℝ) * C.P.CY ≤ Real.log (condE D : ℝ) * |C.P.CY| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hlc
        _ ≤ (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) * |C.P.CY| :=
            mul_le_mul_of_nonneg_right hc (abs_nonneg _)
        _ = 2 * |C.P.CY| * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 := by ring
        _ ≤ _ := h4'
    have hB : (D.R.N D.R.m : ℝ) ^ 4 ≤ L.sc.b := by
      calc (D.R.N D.R.m : ℝ) ^ 4 ≤ (L.sc.x ^ (402 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 4
        _ = Real.exp (1608 * Real.log L.sc.x) := by
            rw [Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul]; congr 1; push_cast; ring
        _ ≤ L.sc.b := by rw [hb]; exact Real.exp_le_exp.mpr h3'
    calc (D.R.N D.R.m : ℝ) ^ 4 * (condE D : ℝ) ^ C.P.CY ≤ L.sc.b * L.sc.b :=
          mul_le_mul hB hA (Real.rpow_nonneg (by linarith) _) hbpos.le
      _ = L.sc.b ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ hbpos.le (le_mul_of_one_le_left hbpos.le hk1) 2
  · rw [hYL, Real.log_pow, Real.log_mul (by positivity) hbpos.ne', hb, Real.log_exp]
    have : Real.log (D.R.k : ℝ) ≤ 5 * Real.log L.sc.x := by
      rw [← Real.log_rpow hx0]; exact Real.log_le_log (by linarith) hk5
    push_cast
    linarith

end GlobalTheory.EX
end

