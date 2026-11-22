import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsND
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsOneN
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0001

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNDn
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_exp_nd {m f s r c mx cf C : ℝ} (hm : m = 2 * r + 2) (hr : 0 ≤ r) (hf : 1 ≤ f) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hmx : 0 ≤ mx) (hcf : cf ≤ m) (hC : 4 + (c ^ 2 + 2 * mx) * (6 * c + 2) ≤ C ^ 2) :
    1 + 12 * f * (r + 1) ^ 2 + (c ^ 2 * m ^ 3 * f + 4 * (mx * m ^ 2 * f * (r + 1))) *
        (2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2) ≤
      C * m ^ 2 * f * (C * (s + m) * m ^ 2) := by
  have hm2 : 2 ≤ m := by linarith
  set Mx : ℝ := (s + m) * m with hMx
  have hMx1 : m ^ 2 ≤ Mx := by rw [hMx]; nlinarith
  have hMx2 : m ≤ Mx := by nlinarith
  have hMx0 : 0 ≤ Mx := by nlinarith
  have hr1 : r + 1 = m / 2 := by linarith
  have hrm : r ^ 2 ≤ Mx := by nlinarith
  have e1 : c ^ 2 * m ^ 3 * f + 4 * (mx * m ^ 2 * f * (r + 1)) = (c ^ 2 + 2 * mx) * (m ^ 3 * f) := by rw [hr1]; ring
  have b1 : c * cf ≤ c * Mx := mul_le_mul_of_nonneg_left (hcf.trans hMx2) hc
  have b2 : c * r ^ 2 ≤ c * Mx := mul_le_mul_of_nonneg_left hrm hc
  have b3 : 6 * (r + 1) ^ 2 ≤ 2 * Mx := by rw [hr1]; nlinarith
  have br : 2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2 ≤ (6 * c + 2) * Mx := by
    have : c * (s + m) * m = c * Mx := by rw [hMx]; ring
    rw [this]; nlinarith
  have hK0 : 0 ≤ m ^ 3 * f := by positivity
  have hp0 : 0 ≤ (c ^ 2 + 2 * mx) * (m ^ 3 * f) := by positivity
  have t1 : (c ^ 2 + 2 * mx) * (m ^ 3 * f) * (2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2) ≤
      (c ^ 2 + 2 * mx) * (m ^ 3 * f) * ((6 * c + 2) * Mx) := mul_le_mul_of_nonneg_left br hp0
  have hKM : 0 ≤ m ^ 3 * f * Mx := by positivity
  have t2 : 1 + 12 * f * (r + 1) ^ 2 ≤ 4 * (m ^ 3 * f * Mx) := by
    rw [hr1]
    have a1 : f * m ^ 2 ≤ m ^ 3 * f * Mx := by
      have : (1 : ℝ) ≤ m * Mx := by nlinarith
      calc f * m ^ 2 = f * m ^ 2 * 1 := by ring
        _ ≤ f * m ^ 2 * (m * Mx) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = m ^ 3 * f * Mx := by ring
    have a2 : (1 : ℝ) ≤ f * m ^ 2 := by nlinarith
    nlinarith
  have t3 : (4 + (c ^ 2 + 2 * mx) * (6 * c + 2)) * (m ^ 3 * f * Mx) ≤ C ^ 2 * (m ^ 3 * f * Mx) :=
    mul_le_mul_of_nonneg_right hC hKM
  rw [e1]
  calc 1 + 12 * f * (r + 1) ^ 2 + (c ^ 2 + 2 * mx) * (m ^ 3 * f) *
        (2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2)
      ≤ 4 * (m ^ 3 * f * Mx) + (c ^ 2 + 2 * mx) * (m ^ 3 * f) * ((6 * c + 2) * Mx) := add_le_add t2 t1
    _ = (4 + (c ^ 2 + 2 * mx) * (6 * c + 2)) * (m ^ 3 * f * Mx) := by ring
    _ ≤ C ^ 2 * (m ^ 3 * f * Mx) := t3
    _ = C * m ^ 2 * f * (C * (s + m) * m ^ 2) := by rw [hMx]; ring

section Rec

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_m_cast (D : D7) : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by
  have := d_m_eq D; exact_mod_cast this

theorem rows_cF_le {C' Cl Cg cb Cu cT CT C0 A : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A) :
    cF D.R.f ≤ D.R.m := by
  obtain ⟨_, _, _, _, h5, _⟩ := hH.1.1
  have h5' : Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.rS : ℝ) := h5
  have hr : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hH.2.1.1
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hsq : Real.sqrt (D.R.rS : ℝ) ≤ D.R.rS := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hl2 := Real.log_two_gt_d9
  have hl0 : 0 ≤ Real.log (D.R.f : ℝ) := Real.log_nonneg hf
  have e : cF D.R.f = 2 + Real.log (D.R.f : ℝ) / Real.log 2 := by
    unfold cF lg2f Real.logb
    rw [Real.log_mul (by norm_num) (by linarith)]
    field_simp
    ring
  have h2 : Real.log (D.R.f : ℝ) / Real.log 2 ≤ 2 * Real.log (D.R.f : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  rw [e, rows_m_cast]
  linarith

theorem rows_one_le_NT (D : D7) (w : D.what₂.Word) : 1 ≤ NT D w := by
  unfold NT
  exact one_le_pow₀ (by exact_mod_cast (D.mem w).A.T_prime.pos)

theorem rows_XiP_le (D : D7) (large₂ : SizeData₂ D) (w : D.what₂.Word) {c Ch C : ℝ} (hc : 0 ≤ c) (hcC : c ≤ C)
    (hC : 2 * pairCountExponentShift D c Ch ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) (s : ℕ) :
    XiS D w (rows_P D large₂ c Ch ^ 2) c s ≤ XiB D large₂ w C s := by
  have hb := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hP1 := rows_P_one_le D large₂ c Ch
  have hN := rows_one_le_NT D w
  have hPH : rows_P D large₂ c Ch ^ 2 ≤ Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) := by
    unfold rows_P Hb
    rw [rows_rpow_pow hb0, ← Real.rpow_mul hb0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  unfold XiB XiS Xi
  split_ifs
  · exact le_rfl
  · have h1 : (1 : ℝ) ≤ rows_P D large₂ c Ch ^ 2 * NT D w := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hP1) hN
    have h2 : rows_P D large₂ c Ch ^ 2 * NT D w ≤ Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) * NT D w :=
      mul_le_mul_of_nonneg_right hPH (by linarith)
    have h3 : (rows_P D large₂ c Ch ^ 2 * NT D w) ^ (c * (D.R.k : ℝ)) ≤
        (Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) * NT D w) ^ (C * (D.R.k : ℝ)) :=
      calc (rows_P D large₂ c Ch ^ 2 * NT D w) ^ (c * (D.R.k : ℝ))
          ≤ (Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) * NT D w) ^ (c * (D.R.k : ℝ)) :=
            Real.rpow_le_rpow (by linarith) h2 (by positivity)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (h1.trans h2) (by gcongr)
    have h4 : (c * (D.R.k : ℝ)) ^ (D.R.k * D.R.f) ≤ (C * (D.R.k : ℝ)) ^ (D.R.k * D.R.f) :=
      pow_le_pow_left₀ (by positivity) (by gcongr) _
    exact mul_le_mul h4 h3 (Real.rpow_nonneg (by linarith) _) (by
      have : 0 ≤ C := hc.trans hcC
      positivity)
  · exact le_rfl

theorem rows_ndB_le {C' Cl Cg cb Cu cT CT C0 A c Ch δ C : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hc : 0 ≤ c) (hcC : c ≤ C) (hC1 : 1 ≤ C) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2) (s : ℕ) :
    rows_ndB D large₂ u u' c Ch δ s ≤
      LatticeSumBounds.ndRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C) * rDD D u' := by
  have hg2 := two_le_gg_of_count_hypotheses hH.1
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := hH.1.1
    exact h19
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hGam0 : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hP1 := rows_P_one_le D large₂ c Ch
  have hmx : 0 ≤ max (Ch - c) 0 := le_max_right _ _
  have hexp := rows_exp_nd (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (c := c) (mx := max (Ch - c) 0)
    (cf := cF D.R.f) (C := C) (rows_m_cast D) (by positivity) hf (by positivity) hc hmx (rows_cF_le hH) hC
  have hpe2 : 2 * pairCountExponentShift D c Ch ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have e1 : pairCountExponentShift D c Ch = (c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by
      unfold pairCountExponentShift
      have : (D.R.rS : ℝ) + 1 = (D.R.m : ℝ) / 2 := by rw [rows_m_cast]; ring
      rw [this]; ring
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 3 * D.R.f := by positivity
    have h1 : 2 * (c ^ 2 + 2 * max (Ch - c) 0) ≤ C ^ 2 := by
      have : 0 ≤ (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c) := by positivity
      nlinarith
    rw [e1]
    calc 2 * ((c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f))
        = (2 * (c ^ 2 + 2 * max (Ch - c) 0)) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by ring
      _ ≤ C ^ 2 * ((D.R.m : ℝ) ^ 3 * D.R.f) := mul_le_mul_of_nonneg_right h1 h0
      _ = _ := by ring
  have := rows_num_nd (k := D.R.k) (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (b := large₂.sc.b) (g := gg D)
    (v := D.host.v) (Γ := GamS D large₂) (c := c) (C := C) (pe := pairCountExponentShift D c Ch) (E1 := pairCountExponent D c s)
    (cr := c * (D.R.rS : ℝ) ^ 2) (δ := δ) (rD := rDD D u') (XiP := XiS D u (rows_P D large₂ c Ch ^ 2) c s)
    (Xi := XiB D large₂ u C) (d_two_le_b D large₂) (by linarith) (by linarith) hGam0.le hc hcC hC1 hδ0 hδ
    (rows_rDD_nonneg D u') (rows_XiS_nonneg D u (by positivity) hc s) (rows_XiP_le D large₂ u hc hcC hpe2 s)
    (by unfold pairCountExponentShift pairCountExponent; exact hexp)
  unfold rows_ndB rows_R rows_Phi
  exact this

theorem rows_RowBound_mono {Q : D.s.Pair u u' → Prop} {B B' : ℝ} (h : RowBound X Y Q B) (hB : B ≤ B')
    (hdim : 0 ≤ dimPi (hc := D.hcW) u) : RowBound X Y Q B' := fun S hS =>
  (h S hS).trans (mul_le_mul_of_nonneg_left hB (mul_nonneg (rows_massRows_nonneg Y) hdim))

theorem rows_RowsND_record {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm C : ℝ} {q : ℕ}
    (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (hδ : δ ≤ 1) (hcC : c ≤ C) (hC1 : 1 ≤ C)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c D.R.k + 4 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1)) : RowsND X Y C := by
  intro s hs hsk
  refine rows_RowBound_mono Y (rows_ND_record Y h s hs hsk ?_) (rows_ndB_le h.hH h.hc hcC hC1 h.hδ hδ hC s) h.hdim.le
  have : pairCountExponent D c s ≤ pairCountExponent D c D.R.k := by
    unfold pairCountExponent
    have hsk' : (s : ℝ) ≤ D.R.k := by exact_mod_cast hsk
    have := h.hc
    gcongr
  linarith

end Rec

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsOneC
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem weighted_sum_le_of_fibre_counts {Pr κ : Type} (S : Finset Pr) (w a₁ a₂ : Pr → ℝ) (c₁ c₂ : Pr → κ) (M R Φ : ℝ) (N : κ → κ → ℝ)
    (α₁ α₂ φ : κ → ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) (hw : ∀ p ∈ S, 0 ≤ w p) (ha₂ : ∀ p ∈ S, 0 ≤ a₂ p)
    (hα₁ : ∀ p ∈ S, a₁ p ≤ α₁ (c₁ p)) (hα₂ : ∀ p ∈ S, a₂ p ≤ α₂ (c₂ p))
    (hcount : ∀ x y, (∃ p ∈ S, c₁ p = x) → (∃ p ∈ S, c₂ p = y) → ∀ S' : Finset Pr, S' ⊆ S →
      (∀ p ∈ S', c₁ p = x ∧ c₂ p = y) → ∑ p ∈ S', w p ≤ M * N x y)
    (hN : ∀ x y, (∃ p ∈ S, c₁ p = x) → (∃ p ∈ S, c₂ p = y) → N x y * (α₁ x * α₂ y) ≤ R * (φ x * φ y))
    (hα0₁ : ∀ x, 0 ≤ α₁ x) (hα0₂ : ∀ x, 0 ≤ α₂ x) (hφ0 : ∀ x, 0 ≤ φ x)
    (hΦ₁ : ∀ 𝒵 : Finset κ, (∀ x ∈ 𝒵, ∃ p ∈ S, c₁ p = x) → ∑ x ∈ 𝒵, φ x ≤ Φ)
    (hΦ₂ : ∀ 𝒵 : Finset κ, (∀ x ∈ 𝒵, ∃ p ∈ S, c₂ p = x) → ∑ x ∈ 𝒵, φ x ≤ Φ) :
    ∑ p ∈ S, w p * (a₁ p * a₂ p) ≤ M * (R * Φ ^ 2) := by
  classical
  rw [rows_fibres S c₁ c₂]
  have h1 := hΦ₁ (S.image c₁) fun x hx => Finset.mem_image.1 hx
  have h2 := hΦ₂ (S.image c₂) fun x hx => Finset.mem_image.1 hx
  have hΦ0 : 0 ≤ Φ := le_trans (Finset.sum_nonneg fun x _ => hφ0 x) h1
  calc ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (a₁ p * a₂ p)
      ≤ ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, M * (R * (φ x * φ y)) := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
        calc ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (a₁ p * a₂ p)
            ≤ ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (α₁ x * α₂ y) := by
              refine Finset.sum_le_sum fun p hp => ?_
              obtain ⟨hpS, e1, e2⟩ := Finset.mem_filter.1 hp
              refine mul_le_mul_of_nonneg_left ?_ (hw p hpS)
              exact mul_le_mul (e1 ▸ hα₁ p hpS) (e2 ▸ hα₂ p hpS) (ha₂ p hpS) (hα0₁ x)
          _ = (∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p) * (α₁ x * α₂ y) := by rw [Finset.sum_mul]
          _ ≤ (M * N x y) * (α₁ x * α₂ y) :=
              mul_le_mul_of_nonneg_right (hcount x y (Finset.mem_image.1 hx) (Finset.mem_image.1 hy) _
                (Finset.filter_subset _ _) fun p hp => (Finset.mem_filter.1 hp).2) (mul_nonneg (hα0₁ x) (hα0₂ y))
          _ = M * (N x y * (α₁ x * α₂ y)) := by ring
          _ ≤ M * (R * (φ x * φ y)) :=
              mul_le_mul_of_nonneg_left (hN x y (Finset.mem_image.1 hx) (Finset.mem_image.1 hy)) hM
    _ = M * (R * ((∑ x ∈ S.image c₁, φ x) * ∑ y ∈ S.image c₂, φ y)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ M * (R * Φ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hR) hM
        rw [sq]
        exact mul_le_mul h1 h2 (Finset.sum_nonneg fun x _ => hφ0 x) hΦ0

section One

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def wordPairWeightRatio (D : D7) (u u' : D.what₂.Word) : ℝ :=
  4 * Real.sqrt (Tr D u' / Tr D u) * (gS D : ℝ) * gg D ^ (-(D.R.m : ℝ)) * ((D.R.k : ℝ) ^ D.R.rS)⁻¹

def smallTermBound (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C0 : ℝ) : ℝ :=
  2 * C0 * GamS D large₂ ^ 2 * (wordPairWeightRatio D u u' ^ D.R.f) ^ D.R.k

def logHeightExp (D : D7) (large₂ : SizeData₂ D) (C2 : ℝ) : ℝ := Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b)

def smallTermLoss (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c C2 Ch δ C0 : ℝ) (q : ℕ) (Z : GramM D) : ℝ :=
  (HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
    (GamS D large₂ * sizeZ D large₂.sc.b Ch Z ^ (C2 * (D.R.m : ℝ) ^ 2)) *
    (logHeightExp D large₂ C2 * sizeZ D large₂.sc.b Ch Z ^ (C2 * (D.R.m : ℝ) ^ 4)) ^ 2 * ((1 + δ) * rDD D u') * smallTermBound D large₂ u u' C0 *
    sizeZ D large₂.sc.b Ch Z ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1)))

def smallTermAmplitude (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c C2 Ch δ C0 : ℝ) (q : ℕ) (Z : GramM D) : ℝ :=
  Real.sqrt (smallTermLoss D large₂ u u' c C2 Ch δ C0 q Z / wordPairGramNorm D u u' Z)

def twoLabelCount (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c : ℝ) (x y : GramM D) : ℝ :=
  min (wordPairSwapBound D large₂ u u' c x * gramPairQuadrupleBound D large₂ c x y) (wordPairSwapBound D large₂ u u' c y * gramPairQuadrupleBound D large₂ c y x)

def labelPairConstant (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c C2 Ch δ C0 : ℝ) : ℝ :=
  c ^ D.R.f * ((rows_P D large₂ c Ch ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 * (rows_P D large₂ c Ch ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
    (rows_P D large₂ c Ch ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2) * GamS D large₂ * logHeightExp D large₂ C2 * ((1 + δ) * rDD D u') *
    Real.sqrt (smallTermBound D large₂ u u' C0)

def corankOneBound (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c C2 Ch δ C0 : ℝ) : ℝ :=
  2 * (labelPairConstant D large₂ u u' c C2 Ch δ C0 * rows_Phi D large₂ c Ch ^ 2)

def IsSmallTerm (t : D.s.Term u u') : Prop :=
  Dr (X.fl t) (X.fl' t) ≠ 0 ∧ ∏ τ, min (nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t τ)) (Tr D u') ≤
    (4 * Real.sqrt (Tr D u' / Tr D u) * (gS D : ℝ)) ^ D.R.f

variable {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm : ℝ} {q : ℕ}

theorem one_le_rank_k (D : D7) : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega

theorem term_weight_pos (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0)
    (τ : D.what₂.Tau) : 0 < tvPr D τ u' := by
  have hl := h7 hH0 u' τ
  have hg : 0 < gg D := by linarith [two_le_gg_of_count_hypotheses hH0]
  have hgm : 0 < gg D ^ (-(D.R.m : ℝ)) := Real.rpow_pos_of_pos hg _
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast one_le_rank_k D
  have hk : 0 < (D.R.k : ℝ) ^ (3 * D.R.rS) := by positivity
  have hT : 0 < Tcrit D u' τ := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos hgm.le (not_lt.1 hn)
    linarith
  unfold tvPr
  exact div_pos hT (rows_Tr_pos D u')

theorem prod_term_weight_pow_le (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (h6 : VanishingOnXAndXPlus.adm6 D large₂ C' Cl Cg cb Cu cT CT C0 δ)
    (hδ2 : δ ≤ 1 / 2) : ∏ τ, tvPr D τ u' ^ D.R.k ≤ 2 * C0 * GamS D large₂ ^ 2 := by
  have h := abs_le.1 (h6 hH0 u')
  have hD := d_Dstar_pos D
  obtain ⟨_, _, _, _, _, _, _, _, _, h10, _⟩ := hH0.2.1
  have hC0 : 0 < C0 := lt_of_lt_of_le one_pos hH0.2.2
  have hΓ : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hw := (h10 u').1
  rw [d_GamP_eq D large₂ u'] at hw
  have e2 : GamS D large₂ ^ (-2 : ℤ) = (GamS D large₂ ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
  rw [e2] at hw
  have hd : 0 < (D.duS u' : ℝ) := lt_of_lt_of_le (by positivity) hw
  set P : ℝ := ∏ τ, (Tcrit D u' τ / Tr D u') ^ D.R.k with hP
  have e : ∏ τ, tvPr D τ u' ^ D.R.k = P := rfl
  rw [e]
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun τ _ => D.R.k_even.pow_nonneg _
  have h1 : P / 2 ≤ D.what₂.Dstar / (D.duS u' : ℝ) := by nlinarith [h.1]
  have h2 : D.what₂.Dstar / (D.duS u' : ℝ) ≤ C0 * GamS D large₂ ^ 2 := by
    rw [div_le_iff₀ hd]
    have a1 : (GamS D large₂ ^ 2)⁻¹ * D.what₂.Dstar ≤ (D.duS u' : ℝ) * C0 := (div_le_iff₀ hC0).1 hw
    have a2 : D.what₂.Dstar ≤ GamS D large₂ ^ 2 * ((D.duS u' : ℝ) * C0) := (inv_mul_le_iff₀ (by positivity)).1 a1
    linarith
  linarith

theorem weightRatio_nonneg (D : D7) (hg : 0 ≤ gg D) (u u' : D.what₂.Word) : 0 ≤ wordPairWeightRatio D u u' := by
  unfold wordPairWeightRatio; positivity

theorem smallTermBound_nonneg (D : D7) (large₂ : SizeData₂ D) (hg : 0 ≤ gg D) (u u' : D.what₂.Word) (hC0 : 0 ≤ C0) :
    0 ≤ smallTermBound D large₂ u u' C0 := by
  have := weightRatio_nonneg D hg u u'
  unfold smallTermBound; positivity

theorem ampMin_mono_constant (D : D7) {C C'' δ' : ℝ} (h0 : 0 ≤ C) (hCC : C ≤ C'') (hδ1 : δ' ≤ 1) (τ : D.what₂.Tau) (w w' : D.what₂.Word)
    (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (γ : MatKR D.R.k D.R.rS)
    (hx : 0 ≤ nuV (Tr D w) z z' γ * tvPr D τ w' * gg D ^ (-(D.R.m : ℝ))) :
    ampMinF D C δ' τ w w' z z' γ ≤ ampMinF D C'' δ' τ w w' z z' γ := by
  unfold ampMinF
  split_ifs
  · exact le_rfl
  · refine min_le_min le_rfl (mul_le_mul_of_nonneg_left ?_ hx)
    have ha : 0 ≤ 2 * (D.R.rS : ℝ) * (1 - δ') := by
      have : 0 ≤ 1 - δ' := by linarith
      positivity
    exact Real.rpow_le_rpow (by positivity) (by gcongr) ha

theorem small_term_pow_le (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0) (hδ2 : δ ≤ 1 / 2) (hδm0 : 0 ≤ δm) (hδm : δm ≤ 1 / 4) (hCa : 0 ≤ Ca)
    (hCak : (max Ca 1) ^ 3 ≤ D.R.k) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) (hsm : IsSmallTerm Y t) :
    rows_Mt Y Ca δm t ^ D.R.k ≤ smallTermBound D large₂ u u' C0 := by
  have hrd := d_rdE_pos h.hH.1
  have hg : 0 < gg D := by linarith [two_le_gg_of_count_hypotheses h.hH.1]
  have hk := one_le_rank_k D
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast hk
  have htv := fun τ => term_weight_pos (u' := u') h.hH.1 h7 τ
  have hC1 : (1 : ℝ) ≤ max Ca 1 := le_max_right _ _
  have m1 := rowsT_Mt_small Y hrd t hG hrel hsm.1 hC1 hδm0 (by linarith) hg hk (fun τ => h7 h.hH.1 u' τ) hsm.2 le_rfl
  have hgS : (0 : ℝ) ≤ (gS D : ℝ) := by positivity
  have m2 : (4 * Real.sqrt (Tr D u' / Tr D u) * (gS D : ℝ) * gg D ^ (-(D.R.m : ℝ)) *
      (max Ca 1 / D.R.k) ^ (2 * (D.R.rS : ℝ) * (1 - δm))) ^ D.R.f ≤ wordPairWeightRatio D u u' ^ D.R.f := by
    apply pow_le_pow_left₀ (by positivity)
    unfold wordPairWeightRatio
    exact mul_le_mul_of_nonneg_left (div_rpow_le_inv_pow hk hC1 hδm hCak) (by positivity)
  have hP0 : 0 ≤ ∏ τ, tvPr D τ u' := Finset.prod_nonneg fun τ _ => (htv τ).le
  have hx : ∀ τ, 0 ≤ nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t τ) * tvPr D τ u' * gg D ^ (-(D.R.m : ℝ)) := by
    intro τ
    have hν : 0 ≤ nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t τ) := by
      unfold nuV
      rw [d_Gf_eq Y hrd t τ]
      exact div_nonneg (rows_Gz_pos Y h.hT hrd t hG hrel τ).le (mul_nonneg (rows_Tr_pos D u).le (sq_nonneg _))
    have := (htv τ).le
    positivity
  have a0 : ∀ τ, 0 ≤ ampMinF D Ca δm τ u u' (Y.W τ).z (Y.W τ).z' (Y.γ t τ) := by
    intro τ
    unfold ampMinF
    split_ifs
    · exact zero_le_one
    · exact le_min zero_le_one (mul_nonneg (hx τ) (Real.rpow_nonneg (by positivity) _))
  have m0 : 0 ≤ rows_Mt Y Ca δm t := by
    unfold rows_Mt; exact Finset.prod_nonneg fun τ _ => a0 τ
  have mm : rows_Mt Y Ca δm t ≤ rows_Mt Y (max Ca 1) δm t := by
    unfold rows_Mt
    exact Finset.prod_le_prod (fun τ _ => a0 τ) fun τ _ =>
      ampMin_mono_constant D hCa (le_max_left _ _) (by linarith) τ u u' _ _ _ (hx τ)
  have m3 : rows_Mt Y Ca δm t ≤ (∏ τ, tvPr D τ u') * wordPairWeightRatio D u u' ^ D.R.f :=
    mm.trans (m1.trans (mul_le_mul_of_nonneg_left m2 hP0))
  calc rows_Mt Y Ca δm t ^ D.R.k ≤ ((∏ τ, tvPr D τ u') * wordPairWeightRatio D u u' ^ D.R.f) ^ D.R.k := pow_le_pow_left₀ m0 m3 _
    _ = (∏ τ, tvPr D τ u' ^ D.R.k) * (wordPairWeightRatio D u u' ^ D.R.f) ^ D.R.k := by rw [mul_pow, Finset.prod_pow]
    _ ≤ 2 * C0 * GamS D large₂ ^ 2 * (wordPairWeightRatio D u u' ^ D.R.f) ^ D.R.k :=
        mul_le_mul_of_nonneg_right (prod_term_weight_pow_le h.hH.1 h.h6 hδ2) (by have := weightRatio_nonneg D hg.le u u'; positivity)

theorem small_term_amplitude_le (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0) (hδ2 : δ ≤ 1 / 2) (hδm0 : 0 ≤ δm) (hδm : δm ≤ 1 / 4) (hCa : 0 ≤ Ca)
    (hCak : (max Ca 1) ^ 3 ≤ D.R.k) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) (hsm : IsSmallTerm Y t) :
    aT X t / Real.sqrt (dimPi (hc := D.hcW) u) ≤ smallTermAmplitude D large₂ u u' c C2 Ch δ C0 q (termReducedGramMatrix Y h.hH h.hHH t) := by
  obtain ⟨hEq, hGood⟩ := rows_Zr_spec Y h.hH h.hHH t hG hrel
  have h1 := rows_term_MINIdec Y h.hH h.hDEC h.ha h.hb h.hp h.hpp h.h6 h.hδ h.hV h.hT h.hCh t hG hrel q h.hq
  have hM := small_term_pow_le Y h h7 hδ2 hδm0 hδm hCa hCak t hG hrel hsm
  rw [← rows_nZ_inv hEq, ← rows_HHZ_inv hEq, ← rows_sizeZ_inv hEq] at h1
  have hσ := rows_one_le_sizeZ (D := D) large₂.sc.b Ch (termReducedGramMatrix Y h.hH h.hHH t)
  have hHH1 := rows_one_le_HHZ D large₂ h.hc (termReducedGramMatrix Y h.hH h.hHH t)
  have hΓ : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hτ0 : 0 ≤ (1 + δ) * rDD D u' := mul_nonneg (by linarith [h.hδ]) (rows_rDD_nonneg D u')
  have h1' : wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) * aT X t ^ 2 / dimPi (hc := D.hcW) u ≤
      smallTermLoss D large₂ u u' c C2 Ch δ C0 q (termReducedGramMatrix Y h.hH h.hHH t) := by
    refine h1.trans ?_
    unfold smallTermLoss logHeightExp
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM ?_) (by positivity)
    positivity
  have h2 : aT X t ^ 2 / dimPi (hc := D.hcW) u ≤ smallTermLoss D large₂ u u' c C2 Ch δ C0 q (termReducedGramMatrix Y h.hH h.hHH t) /
      wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) := by
    rw [le_div_iff₀ (rows_nZ_pos Y h hGood)]
    calc aT X t ^ 2 / dimPi (hc := D.hcW) u * wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t)
        = wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) * aT X t ^ 2 / dimPi (hc := D.hcW) u := by ring
      _ ≤ _ := h1'
  have h3 : aT X t / Real.sqrt (dimPi (hc := D.hcW) u) = Real.sqrt (aT X t ^ 2 / dimPi (hc := D.hcW) u) := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (aT_nonneg X t)]
  rw [h3]
  exact Real.sqrt_le_sqrt h2

end One

end Formalism.MainNotions.BridgeLemma₂

end
end

