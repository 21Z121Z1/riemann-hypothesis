import Mathlib
import GroundTheory.PAdicHodge.ExistsWeightLeOfConvergesAt
import GroundTheory.PAdicHodge.Bundle0005
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.RobbaBounded
import GroundTheory.PAdicHodge.RobbaNewton
import GroundTheory.PAdicHodge.RobbaClosed
import GroundTheory.PAdicHodge.RobbaLazard

-- bundled from GroundTheory.PAdicHodge.DMTeichPow
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

def id (T : TeichLift p L Γ) : T.TeichFrob where
  φ := RingEquiv.refl Γ
  a := 0
  red_φ x := by simp
  u := 1
  φ_π := by simp
  u_mem_int := one_mem _
  norm_red_u := by simp
  map_int _ hx := hx
  symm_map_int _ hx := hx

def comp (F G : T.TeichFrob) : T.TeichFrob where
  φ := G.φ.trans F.φ
  a := F.a + G.a
  red_φ x := by
    simp only [RingEquiv.trans_apply, F.red_φ, G.red_φ, ← pow_mul, pow_add, mul_comm]
  u := F.u * F.φ G.u
  φ_π := by
    simp only [RingEquiv.trans_apply, G.φ_π, map_mul, F.φ_π]
    ring
  u_mem_int := mul_mem F.u_mem_int (F.map_int _ G.u_mem_int)
  norm_red_u := by
    rw [map_mul, norm_mul, F.norm_red_u, F.red_φ, norm_pow, G.norm_red_u, one_pow, one_mul]
  map_int x hx := F.map_int _ (G.map_int _ hx)
  symm_map_int x hx := G.symm_map_int _ (F.symm_map_int _ hx)

variable (F G : T.TeichFrob)

theorem comp_φ_apply (x : Γ) : (F.comp G).φ x = F.φ (G.φ x) := rfl

theorem comp_a : (F.comp G).a = F.a + G.a := rfl

def pow : ℕ → T.TeichFrob
  | 0 => id T
  | d + 1 => F.comp (pow d)

theorem pow_zero : F.pow 0 = id T := rfl

theorem pow_succ (d : ℕ) : F.pow (d + 1) = F.comp (F.pow d) := rfl

theorem pow_φ_apply (d : ℕ) (x : Γ) : (F.pow d).φ x = F.φ^[d] x := by
  induction d with
  | zero => rfl
  | succ d ih => rw [pow_succ, comp_φ_apply, ih, Function.iterate_succ_apply']

theorem pow_a (d : ℕ) : (F.pow d).a = F.a * d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [pow_succ, comp_a, ih]; ring

theorem pow_a_pos {d : ℕ} (ha : 0 < F.a) (hd : 0 < d) : 0 < (F.pow d).a := by
  rw [pow_a]; exact Nat.mul_pos ha hd

theorem exists_iterate_φ_eq_mul_of_mem_Gcon [IsAlgClosed L] (ha : 0 < F.a) {d : ℕ} (hd : 0 < d)
    {w : Γ} (hw : w ∈ T.Gcon) (hw0 : T.red w ≠ 0) :
    ∃ y ∈ T.Gcon, T.red y ≠ 0 ∧ F.φ^[d] y = w * y := by
  obtain ⟨y, hy, hy0, hyw⟩ := (F.pow d).exists_φ_eq_mul_of_mem_Gcon (F.pow_a_pos ha hd) hw hw0
  exact ⟨y, hy, hy0, by rw [← pow_φ_apply]; exact hyw⟩

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.RobbaAmice
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Robba

variable (K) in

def amiceSet : Set (ℤ → K) :=
  {a | BddAbove (Set.range fun n => ‖a n‖) ∧ Tendsto (fun n : ℕ => a (-(n : ℤ))) atTop (𝓝 0)}

def norm1 (f : Robba K) : ℝ := ⨆ n, ‖f.coeff n‖

theorem gaussNorm_nonneg_alt (f : Robba K) : 0 ≤ norm1 f := Real.iSup_nonneg fun _ => norm_nonneg _

theorem norm_coeff_le_norm1 {f : Robba K} (hf : f ∈ bounded K) (n : ℤ) : ‖f.coeff n‖ ≤ norm1 f :=
  le_ciSup hf n

theorem tendsto_gaussNorm_norm1 {f : Robba K} (hf : f ∈ bounded K) :
    Tendsto (fun ρ => gaussNorm f.coeff ρ) (𝓝[<] 1) (𝓝 (norm1 f)) := by
  obtain ⟨r, hr0, hr1, hc⟩ := exists_common f f
  have hI : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ ∈ Set.Ioo r 1 := Ioo_mem_nhdsLT hr1
  refine tendsto_order.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
  ·
    obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hx
    have hlim : Tendsto (fun ρ : ℝ => ‖f.coeff n‖ * ρ ^ n) (𝓝[<] 1) (𝓝 (‖f.coeff n‖ * 1 ^ n)) :=
      ((continuousAt_zpow₀ (1 : ℝ) n (Or.inl one_ne_zero)).tendsto.const_mul _).mono_left
        nhdsWithin_le_nhds
    rw [one_zpow, mul_one] at hlim
    filter_upwards [hI, hlim.eventually (lt_mem_nhds hn)] with ρ hρ h1
    exact h1.trans_le ((hc ρ hρ.1.le hρ.2).1.le_gaussNorm n)
  ·
    have hM : norm1 f < x := hx
    set ε := (x - norm1 f) / 2 with hε_def
    have hε : 0 < ε := by rw [hε_def]; linarith
    have hF := (hc r le_rfl hr1).1.finite_le hε
    have hev : ∀ n ∈ hF.toFinset, ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ‖f.coeff n‖ * ρ ^ n < norm1 f + ε := by
      intro n _
      have hlim : Tendsto (fun ρ : ℝ => ‖f.coeff n‖ * ρ ^ n) (𝓝[<] 1)
          (𝓝 (‖f.coeff n‖ * 1 ^ n)) :=
        ((continuousAt_zpow₀ (1 : ℝ) n (Or.inl one_ne_zero)).tendsto.const_mul _).mono_left
          nhdsWithin_le_nhds
      rw [one_zpow, mul_one] at hlim
      exact hlim.eventually (gt_mem_nhds (lt_of_le_of_lt (norm_coeff_le_norm1 hf n)
        (by linarith)))
    have hall := (Finset.eventually_all hF.toFinset).2 hev
    filter_upwards [hI, hall] with ρ hρ hfin
    have hρ0 : 0 < ρ := hr0.trans hρ.1
    refine lt_of_le_of_lt (gaussNorm_le fun n => ?_) (by linarith : norm1 f + ε < x)
    by_cases hn : n ∈ hF.toFinset
    · exact (hfin n hn).le
    · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hn
      rcases le_or_gt 0 n with h0 | h0
      · calc ‖f.coeff n‖ * ρ ^ n ≤ ‖f.coeff n‖ * 1 :=
              mul_le_mul_of_nonneg_left (zpow_le_one₀ hρ0 hρ.2.le h0) (norm_nonneg _)
          _ ≤ norm1 f + ε := by rw [mul_one]; linarith [norm_coeff_le_norm1 hf n]
      · have : ρ ^ n ≤ r ^ n := by
          rw [show ρ ^ n = (ρ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv],
            show r ^ n = (r ^ (-n))⁻¹ by rw [zpow_neg, inv_inv]]
          exact inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (by omega) hr0.le hρ.1.le)
        calc ‖f.coeff n‖ * ρ ^ n ≤ ‖f.coeff n‖ * r ^ n :=
              mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ ≤ ε := hn.le
          _ ≤ norm1 f + ε := by linarith [gaussNorm_nonneg_alt f]

theorem gaussNorm_mul_alt {f g : Robba K} (hf : f ∈ bounded K) (hg : g ∈ bounded K) :
    norm1 (f * g) = norm1 f * norm1 g := by
  by_cases hf0 : f.coeff = 0
  · have : f = 0 := Robba.ext hf0
    subst this; simp [norm1]
  by_cases hg0 : g.coeff = 0
  · have : g = 0 := Robba.ext hg0
    subst this; simp [norm1]
  obtain ⟨r, hr0, hr1, hc⟩ := exists_common f g
  have hI : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ ∈ Set.Ioo r 1 := Ioo_mem_nhdsLT hr1
  have h1 := tendsto_gaussNorm_norm1 ((bounded K).mul_mem hf hg)
  have h2 := (tendsto_gaussNorm_norm1 hf).mul (tendsto_gaussNorm_norm1 hg)
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [hI] with ρ hρ
  exact (gaussNorm_cmul (hr0.trans hρ.1) (hc ρ hρ.1.le hρ.2).1 (hc ρ hρ.1.le hρ.2).2 hf0 hg0).symm

theorem gaussNorm_add_le_max_alt {f g : Robba K} (hf : f ∈ bounded K) (hg : g ∈ bounded K) :
    norm1 (f + g) ≤ max (norm1 f) (norm1 g) :=
  ciSup_le fun n => (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (norm_coeff_le_norm1 hf n) (norm_coeff_le_norm1 hg n))

theorem gaussNorm_eq_zero_iff_alt {f : Robba K} (hf : f ∈ bounded K) : norm1 f = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext n
    have := norm_coeff_le_norm1 hf n
    rw [h] at this
    simpa using le_antisymm this (norm_nonneg _)
  · rintro rfl; simp [norm1]

theorem exists_norm1_eq [IsDiscreteValuationRing (normInteger K)] {f : Robba K}
    (hf : f ∈ bounded K) : ∃ n, norm1 f = ‖f.coeff n‖ := by
  obtain ⟨q, hq0, hq1, hq⟩ := exists_norm_le_mul_of_lt (K := K)
  by_cases h0 : norm1 f = 0
  · exact ⟨0, by rw [h0, ((gaussNorm_eq_zero_iff_alt hf).1 h0)]; simp⟩
  have hpos : 0 < norm1 f := lt_of_le_of_ne (gaussNorm_nonneg_alt f) (Ne.symm h0)
  have hlt : q * norm1 f < norm1 f := by nlinarith
  obtain ⟨n₁, hn₁⟩ := exists_lt_of_lt_ciSup hlt
  refine ⟨n₁, le_antisymm (ciSup_le fun n => not_lt.1 fun hn => ?_) (norm_coeff_le_norm1 hf n₁)⟩
  have := hq _ _ hn
  have := norm_coeff_le_norm1 hf n
  nlinarith [norm_nonneg (f.coeff n₁)]

end Robba

end GroundTheory.PAdicHodge
end
end

