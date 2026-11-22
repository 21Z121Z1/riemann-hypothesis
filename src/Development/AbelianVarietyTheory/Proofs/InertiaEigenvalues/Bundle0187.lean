import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0176
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0177
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAnalyticFiltrationIffLatticeFiltrationAdd
section
noncomputable section

open PowerSeries Matrix

namespace GlobalTheory.BK.FilAn

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι)

theorem E_pow_smul_mem_extRpi {β : ℕ} (hβ : ∀ v ∈ P.M, E K l e ^ β • v ∈ P.L) {m : Vec K a ι}
    (hm : m ∈ P.Mext (Rpi O K l e)) : E K l e ^ β • m ∈ P.ext (Rpi O K l e) :=
  P.smul_mem_ext_of_basis (fun i => hβ _ (P.bas_mem_M i)) (A_le_Rpi l e) hm

theorem mem_extInvL_of_Ezpow_smul {i : ℤ} {y : Vec K a ι} (hy : y ∈ P.ext (Rpi O K l e))
    (hg : Ezpow K l e i • y ∈ P.Mext (invL l (A O K))) : y ∈ P.ext (invL l (A O K)) := by
  refine mem_tot.2 fun τ => P.mem_extc_iff.2 fun j => ?_
  have hc : (P.mxInv τ *ᵥ y τ) j ∈ Rpi O K l e := P.mem_extc_iff.1 (mem_tot.1 hy τ) j
  have hB : invE l e (A O K) ≤ invE l e (invL l (A O K)) := away_mono (le_away _ _) rfl
  have h1 : (P.mxInv τ *ᵥ (Ezpow K l e i • y) τ) j ∈ invE l e (invL l (A O K)) := by
    simp only [Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun k _ => mul_mem (hB (P.mxInv_mem τ j k))
      (le_away _ _ (mem_tot.1 hg τ k))
  obtain ⟨n, hn⟩ := h1
  have h2 : Ezpow K l e (n + i) * (P.mxInv τ *ᵥ y τ) j ∈ invL l (A O K) := by
    rw [Ezpow_add, Ezpow_natCast, mul_assoc]
    simpa [Matrix.mulVec_smul] using hn
  have h3 := mul_mem ((Ezpow_mem_invL_A_iff (O := O) (K := K) (l := l) (e := e)
    (i := ((-(n + i)).toNat : ℤ))).2 (by omega)) h2
  rw [← mul_assoc, ← Ezpow_add,
    show (((-(n + i)).toNat : ℕ) : ℤ) + (n + i) = ((n + i).toNat : ℕ) by omega, Ezpow_natCast] at h3
  exact mem_invL_A_of_E_pow_mul l e _ hc h3

omit [IsUltrametricDist K] [CompleteSpace K] [IsUnitBall O K] [Fintype ι] [DecidableEq ι] in
theorem Ezpow_zero' : Ezpow K l e 0 = 1 := by
  simpa using Ezpow_natCast (K := K) l e 0

omit [CompleteSpace K] in
theorem mem_extRpi_of_mem_shiftE_one {z : Vec K a ι} (hz : z ∈ shiftE l e 1 (P.ext (Rpi O K l e))) :
    z ∈ P.ext (Rpi O K l e) := by
  have h := P.smul_tot_mem_ext (f := fun _ => E K l e) (fun _ => E_mem l e _) (mem_shiftE.1 hz)
  have h1 : E K l e * Ezpow K l e (-1) = 1 := by
    simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
  have h2 : ((fun _ : ZMod a => E K l e) • Ezpow K l e (-1) • z) = z := by
    ext τ j
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, h1, one_mul]
  rwa [h2] at h

theorem exists_mem_filL_of_mem_inf [NeZero a] (i : ℤ) {x : Vec K a ι}
    (hx : x ∈ P.ext (Rpi O K l e) ⊓ shiftE l e i (P.Mext (Rpi O K l e))) :
    ∃ y ∈ P.filL i, x - y ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
  obtain ⟨hxL, hxM⟩ := Submodule.mem_inf.1 hx
  obtain ⟨-, β, -, hβ⟩ := P.exists_exponents
  set N : ℕ := (β + 1 - i).toNat with hN
  choose g hg h hh hgh using fun τ k => exists_div_E_pow l e N (mem_tot.1 (mem_shiftE.1 hxM) τ k)
  have hgM : g ∈ P.Mext (invL l (A O K)) := mem_tot.2 fun τ k => hg τ k
  have hhM : h ∈ P.Mext (Rpi O K l e) := mem_tot.2 fun τ k => hh τ k
  have hx' : Ezpow K l e (-i) • x = g + E K l e ^ N • h := by
    funext τ k
    exact hgh τ k
  have hxe : x = Ezpow K l e i • g + Ezpow K l e i • E K l e ^ N • h := by
    rw [← smul_add, ← hx', smul_smul, ← Ezpow_add, add_neg_cancel, Ezpow_zero', one_smul]
  have hsub : x - Ezpow K l e i • g ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
    rw [mem_shiftE]
    have h1 := E_pow_smul_mem_extRpi P hβ (P.smul_tot_mem_Mext (f := fun _ => E K l e ^ (i - 1 + N - β).toNat)
      (fun _ => pow_mem (E_mem l e _) _) hhM)
    convert h1 using 1
    have hs : Ezpow K l e (-1) * (Ezpow K l e i * E K l e ^ N) =
        E K l e ^ β * E K l e ^ (i - 1 + N - β).toNat := by
      simp only [← Ezpow_natCast, ← Ezpow_add]
      congr 1
      omega
    rw [hxe, add_sub_cancel_left]
    funext τ k
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul]
    linear_combination (h τ k) * hs
  refine ⟨Ezpow K l e i • g, Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨?_, ?_⟩), hsub⟩
  · refine mem_extInvL_of_Ezpow_smul P (i := -i) ?_ ?_
    · have := sub_mem hxL (mem_extRpi_of_mem_shiftE_one P hsub)
      rwa [sub_sub_cancel] at this
    · rwa [smul_smul, ← Ezpow_add, neg_add_cancel, Ezpow_zero', one_smul]
  · rwa [mem_shiftE, smul_smul, ← Ezpow_add, neg_add_cancel, Ezpow_zero', one_smul]

end GlobalTheory.BK.FilAn

open GlobalTheory.BK in

theorem GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (i : ℤ) (x : Vec K a ι), x ∈ (P.ext (Rpi O K l e) ⊓ shiftE l e i (P.Mext (Rpi O K l e))) ⊔ shiftE l e 1 (P.ext (Rpi O K l e)) ↔ ∃ y ∈ P.filL i, x - y ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P i x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y, hy, hxy⟩ := FilAn.exists_mem_filL_of_mem_inf P i hx₁
    refine ⟨y, hy, ?_⟩
    rw [add_sub_right_comm]
    exact add_mem hxy hx₂
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨hy₁L, hy₁M⟩ := Submodule.mem_inf.1 hy₁
    refine Submodule.mem_sup.2 ⟨y₁, Submodule.mem_inf.2 ⟨P.ext_mono (invL_A_le_Rpi l e) hy₁L,
      mem_shiftE.2 (P.Mext_mono (invL_A_le_Rpi l e) (mem_shiftE.1 hy₁M))⟩, y₂ + (x - (y₁ + y₂)),
      add_mem (mem_shiftE.2 (P.ext_mono (invL_A_le_Rpi l e) (mem_shiftE.1 hy₂))) hxy, by abel⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemEisensteinFiltrationEqEisensteinPowMulDisc
section
noncomputable section

namespace GlobalTheory.FilDiv

open PowerSeries Filter Topology GlobalTheory.BK

section
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

theorem FilPre_le_E_pow (j : ℕ) {g : S O K e} (hg : g ∈ FilPre O K l e j) :
    ∃ q ∈ Rpi O K l e, (g : K⟦X⟧) = E K l e ^ j * q := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, hx⟩ := hx
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
    refine ⟨C (((m + j).factorial : K)⁻¹) * E K l e ^ m,
      mul_mem (HasK.C_mem _) (pow_mem (E_mem l e _) m), ?_⟩
    rw [hx, Ediv]; ring
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨q, hq, h⟩ := hx
    obtain ⟨q', hq', h'⟩ := hy
    exact ⟨q + q', add_mem hq hq', by rw [Subalgebra.coe_add, h, h', mul_add]⟩
  | smul c x _ hx =>
    obtain ⟨q, hq, h⟩ := hx
    exact ⟨c * q, mul_mem (S_le_R l e c.2) hq, by
      rw [smul_eq_mul, Subalgebra.coe_mul, h]; ring⟩

theorem norm_coeff_pow_mul_le (n : ℕ) {h : K⟦X⟧} (hh : h ∈ S O K e) (k : ℕ) :
    ‖coeff k ((l : K⟦X⟧) ^ n * h)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n := by
  rw [← map_natCast (C : K →+* K⟦X⟧), ← map_pow, coeff_C_mul, norm_mul, norm_pow, mul_assoc]
  refine mul_le_of_le_one_right (by positivity) ?_
  refine le_trans ?_ (hh.1 k)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans ?_ (norm_pow_le_norm_factorial l (k / e))
  rw [← rad_pow l e, ← pow_mul]
  exact pow_le_pow_of_le_one (rad_nonneg _ _) (rad_le_one l (by positivity)) (Nat.mul_div_le k e)

theorem norm_coeff_E_le (k : ℕ) : ‖coeff k (E K l e)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ := by
  have he := NeZero.ne e
  rw [E, map_add, coeff_X_pow, ← map_natCast (C : K →+* K⟦X⟧), coeff_C]
  by_cases hk : k = e
  · rw [if_pos hk, if_neg (by omega), add_zero, norm_one, one_mul, hk, rad_pow (K := K) l e]
  · by_cases h0 : k = 0
    · rw [if_neg hk, if_pos h0, zero_add, h0, pow_zero, mul_one]
    · rw [if_neg hk, if_neg h0, add_zero, norm_zero, zero_mul]
      exact norm_nonneg _

variable [CompleteSpace K]

theorem norm_coeff_quotE_le {r : K⟦X⟧} {n : ℕ}
    (hr : ∀ k, ‖coeff k r‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1)) (k : ℕ) :
    ‖coeff k (quotE l e r)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n := by
  have hρ := rad_pos l (1 / (e : ℝ))
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
  rw [quotE, coeff_mk]
  have h1 : ‖tail l e r (k + e)‖ ≤ ‖(l : K)‖ ^ (n + 1) / rad l (1 / e) ^ (k + e) := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun j => ?_
    rw [le_div_iff₀ (pow_pos hρ _), norm_term_eq]
    exact hr _
  calc ‖tail l e r (k + e)‖ * rad l (1 / e) ^ k
      ≤ ‖(l : K)‖ ^ (n + 1) / rad l (1 / e) ^ (k + e) * rad l (1 / e) ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖(l : K)‖ ^ n := by
        rw [pow_add (rad l (1 / (e : ℝ))) k e, rad_pow (K := K) l e, pow_succ]
        field_simp

theorem norm_coeff_rem_le {r : K⟦X⟧} {n : ℕ}
    (hr : ∀ k, ‖coeff k r‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1)) (k : ℕ) :
    ‖coeff k (r - E K l e * quotE l e r)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1) := by
  have hw : ∀ i, 0 ≤ rad l (1 / (e : ℝ)) ^ i := fun i => pow_nonneg (rad_nonneg _ _) i
  rw [sub_eq_add_neg]
  refine (norm_coeff_add_le hw _ _ k).trans (max_le (hr k) ?_)
  rw [map_neg, norm_neg, pow_succ']
  exact norm_coeff_mul_le (w := fun i => rad l (1 / (e : ℝ)) ^ i) hw (fun i j => (pow_add _ i j).le)
    (norm_nonneg _) (by positivity) (norm_coeff_E_le l e) (norm_coeff_quotE_le l e hr) k

theorem exists_eq_E_pow_mul (j : ℕ) {ψ : K⟦X⟧} (hψ : ψ ∈ Rpi O K l e)
    (H : ∀ n : ℕ, ∃ q ∈ Rpi O K l e,
      ∀ k, ‖coeff k (ψ - E K l e ^ j * q)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n) :
    ∃ q ∈ Rpi O K l e, ψ = E K l e ^ j * q := by
  induction j generalizing ψ with
  | zero => exact ⟨ψ, hψ, by simp⟩
  | succ j ih =>
    have hQ := quotE_mem_Rpi l e hψ
    have key : ∀ n, ∃ q ∈ Rpi O K l e,
        (∀ k, ‖coeff k (quotE l e ψ - E K l e ^ j * q)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n) ∧
        ∀ k, ‖coeff k (ψ - E K l e * quotE l e ψ)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1) := by
      intro n
      obtain ⟨q, hq, hr⟩ := H (n + 1)
      have hrR : ψ - E K l e ^ (j + 1) * q ∈ Rpi O K l e :=
        sub_mem hψ (mul_mem (pow_mem (E_mem l e _) _) hq)
      generalize hr_def : ψ - E K l e ^ (j + 1) * q = r at hr hrR
      have hg : quotE l e ψ - E K l e ^ j * q - quotE l e r = 0 := by
        refine eq_zero_of_E_mul l e (sub_mem (sub_mem hQ (mul_mem (pow_mem (E_mem l e _) _) hq))
          (quotE_mem_Rpi l e hrR)) fun m => ?_
        have h1 := coeff_sub_E_mul_quotE l e hψ m
        have h2 := coeff_sub_E_mul_quotE l e hrR m
        have : E K l e * (quotE l e ψ - E K l e ^ j * q - quotE l e r) =
            (r - E K l e * quotE l e r) - (ψ - E K l e * quotE l e ψ) := by
          rw [← hr_def]; ring
        rw [this, map_sub, h1, h2, sub_zero]
      have hg' : quotE l e ψ - E K l e ^ j * q = quotE l e r := sub_eq_zero.1 hg
      have hrem : ψ - E K l e * quotE l e ψ = r - E K l e * quotE l e r := by
        rw [← hg', ← hr_def]; ring
      exact ⟨q, hq, fun k => by rw [hg']; exact norm_coeff_quotE_le l e hr k,
        fun k => by rw [hrem]; exact norm_coeff_rem_le l e hr k⟩
    choose qs hqs hsmall hrem using key
    obtain ⟨q, hq, hQ'⟩ := ih hQ fun n => ⟨qs n, hqs n, hsmall n⟩
    have hR0 : ψ - E K l e * quotE l e ψ = 0 := by
      ext k
      rw [map_zero]
      have hρ := pow_pos (rad_pos l (1 / (e : ℝ))) k
      have ht : Tendsto (fun n : ℕ => ‖(l : K)‖ ^ (n + 1)) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one l)).comp
          (tendsto_add_atTop_nat 1)
      have h0 : ‖coeff k (ψ - E K l e * quotE l e ψ)‖ * rad l (1 / e) ^ k ≤ 0 :=
        ge_of_tendsto' ht fun n => hrem n k
      exact norm_le_zero_iff.1 (le_of_mul_le_mul_right (by simpa using h0) hρ)
    refine ⟨q, hq, ?_⟩
    rw [sub_eq_zero] at hR0
    rw [hR0, hQ', pow_succ']; ring

end

theorem mem_Fil_eq_E_pow_mul : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [NeZero e] (j : ℕ), ∀ φ : S O K e, φ ∈ Fil O K l e j →
      ∃ q ∈ Rpi O K l e, (φ : K⟦X⟧) = E K l e ^ j * q := by
  intro O K _ _ _ _ _ _ l e _ _ _ j φ hφ
  have hψ : (φ : K⟦X⟧) ∈ Rpi O K l e := S_le_R l e φ.2
  refine exists_eq_E_pow_mul l e j hψ fun n => ?_
  obtain ⟨g, hg, h, H⟩ := (mem_Fil l).1 hφ n
  obtain ⟨q, hq, hgq⟩ := FilPre_le_E_pow l e j hg
  refine ⟨q, hq, fun k => ?_⟩
  have : (φ : K⟦X⟧) - E K l e ^ j * q = (l : K⟦X⟧) ^ n * h := by
    rw [H]; push_cast; rw [hgq]; ring
  rw [this]
  exact norm_coeff_pow_mul_le l e n h.2 k

example : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (j : ℕ), ∀ φ : S O K e, φ ∈ Fil O K l e j → ∃ q ∈ Rpi O K l e, (φ : K⟦X⟧) = E K l e ^ j * q := mem_Fil_eq_E_pow_mul

end GlobalTheory.FilDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPhiModuleLatticeOfAdicSeriesPrimePowTerms
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Matrix

theorem PhiMod.mem_MM_of_series (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι) :
    ∀ (w : Vec K a ι) (t : ℕ → Vec K a ι), (∀ n, ∃ v ∈ P.MM, t n = (l : K) ^ n • v) →
      (∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m) → w ∈ P.MM := by
  intro w t ht hw
  choose v hv htv using ht
  have h2 (k : ℕ) : ∃ s ∈ P.MM, ∀ m, ∃ g ∈ P.MM,
      w - (s + (l : K) ^ k • g) ∈ uPow K a ι m := by
    refine ⟨∑ n ∈ Finset.range k, t n,
      sum_mem fun n _ => (htv n) ▸ P.l_pow_smul_mem_MM n (hv n), fun m => ?_⟩
    refine ⟨∑ n ∈ Finset.range m, (l : K) ^ n • v (k + n),
      sum_mem fun n _ => P.l_pow_smul_mem_MM n (hv _), uPow_anti (Nat.le_add_left m k) ?_⟩
    have := hw (k + m)
    rw [Finset.sum_range_add] at this
    simpa only [Finset.smul_sum, smul_smul, ← pow_add, ← htv] using this
  refine mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => mem_S_of_approx (l := l) fun k => ?_
  obtain ⟨s, hs, H⟩ := h2 k
  refine ⟨_, P.mem_extc_iff.1 (mem_tot.1 hs τ) i, fun m => ?_⟩
  obtain ⟨g, hg, H'⟩ := H m
  refine ⟨_, P.mem_extc_iff.1 (mem_tot.1 hg τ) i, ?_⟩
  have := dvd_mulVec (P.mxInv τ) (H' τ) i
  simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_smul] using this

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRigidFunctionsClosedDiscOfAdicLimitStatement
section
open PowerSeries GlobalTheory.BK Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rigidFunctionsClosedDisc_of_adic_limit : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) (k : ℝ) (f : K⟦X⟧) (s : ℕ → K⟦X⟧), (∀ n, s n ∈ R O K l k) → (∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ f - s n) → Tendsto (fun n => normR l k (s (n + 1) - s n)) atTop (𝓝 0) → f ∈ R O K l k := by
  first | exact @GlobalTheory.mem_R_of_adic_limit | exact GlobalTheory.mem_R_of_adic_limit | (intros; apply GlobalTheory.mem_R_of_adic_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedLengthLatticeQuotientBaseChangeEqStatement
section
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedLength_latticeQuotient_baseChange_eq : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V), LinearIndependent (FractionRing O) (fun a => iV (b a)) → (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → (l : 𝓞 K) ∈ w.asIdeal → (∀ a : 𝓞 K, ∀ z : O, algebraMap O (FractionRing O) z = e (a : K) → (a ∈ w.asIdeal ↔ ¬ IsUnit z)) → ∀ (A B : Submodule (𝓞 K) V), A.FG → B ≤ A → lenUnit (O := O) l (↥(Submodule.span O (iV '' (A : Set V))) ⧸ (Submodule.span O (iV '' (B : Set V))).comap (Submodule.span O (iV '' (A : Set V))).subtype) = Formalism.L2.Col.lenUW w A B := by
  first | exact @GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW | exact GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW | (intros; apply GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiMemInvertedLattice
section
open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.BK

namespace PhiMod

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NeZero a]

theorem exists_lpow_smul_mem_MM (P : PhiMod O K l e a ι) {v : Vec K a ι} (hv : v ∈ P.MMl) :
    ∃ N : ℕ, (l : K) ^ N • v ∈ P.MM := by
  have hc : ∀ p : ZMod a × ι, ∃ n : ℕ,
      (l : K⟦X⟧) ^ n * (P.mxInv p.1 *ᵥ v p.1) p.2 ∈ S O K e := by
    intro p
    obtain ⟨n, hn⟩ := mem_away.1 (mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 hv p.1)) p.2)
    exact ⟨n, by simpa using hn⟩
  choose n hn using hc
  refine ⟨Finset.univ.sup n, mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun i => ?_)⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, hc, smul_eq_C_mul, map_pow, map_natCast,
    pow_add, mul_assoc]
  exact mul_mem (pow_mem (natCast_mem _ l) c) (hn (τ, i))

theorem mem_MMl_of_lpow_smul_mem_MM (P : PhiMod O K l e a ι) {w : Vec K a ι} (N : ℕ)
    (h : (l : K) ^ N • w ∈ P.MM) : w ∈ P.MMl := by
  refine mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun i => mem_away.2 ⟨N, ?_⟩)
  have h1 := mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 h τ)) i
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_C_mul, map_pow, map_natCast] at h1
  simpa using h1

end PhiMod

theorem BKDat.phi_mem_MMl : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ v ∈ D.MMl, D.phi v ∈ D.MMl := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D v hv
  obtain ⟨N, hN⟩ := D.toPhiMod.exists_lpow_smul_mem_MM hv
  have h := PhiMod.pow_smul_phi_mem_MM O K l e a ι D.toPhiMod η D.upper _ hN
  rw [map_smul, smul_smul, ← pow_add] at h
  exact D.toPhiMod.mem_MMl_of_lpow_smul_mem_MM _ h

end GlobalTheory.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiMemInvertedPrimeLatticeOfMemEisensteinInvaria
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

theorem phi_mem_MMl_of_mem_Y : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, D.phi y ∈ D.MMl := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy
  have hl : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero (algebraMap ℚ_[l] K)).2
      (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)
  have hE : E K l e ^ η • y ∈ D.M := hy.1
  have h0 : (l : K) ^ η • D.phi y ∈ D.MM := D.l_pow_smul_phi_mem_MM (D.Mext_mono (A_le_S l e) hE)
  have h1 : (l : K) ^ η • D.phi y ∈ D.MMl := D.ext_mono (le_away _ _) h0
  have hc : (C ((l : K)⁻¹ ^ η) : K⟦X⟧) ∈ invL l (S O K e) := by
    refine ⟨η, ?_⟩
    have : ((l : S O K e) : K⟦X⟧) ^ η * C ((l : K)⁻¹ ^ η) = 1 := by
      rw [show ((l : S O K e) : K⟦X⟧) = C (l : K) by simp, ← map_pow, ← map_mul, ← mul_pow,
        mul_inv_cancel₀ hl, one_pow, map_one]
    rw [this]; exact one_mem _
  have h2 := D.MMl.smul_mem ⟨_, hc⟩ h1
  convert h2 using 1
  rw [Subalgebra.smul_def]
  funext τ i
  simp only [Pi.smul_apply, smul_eq_mul, Subtype.coe_mk]
  rw [PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, ← mul_pow, inv_mul_cancel₀ hl, one_pow,
    map_one, one_mul]

end GlobalTheory.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDivisibilityOfDescentDatum
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.NgalDivisible

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem l_pow_eq (n : ℕ) : ((l : K⟦X⟧)) ^ n =
    E K l e ^ n - (X : K⟦X⟧) ^ e * ∑ i ∈ Finset.range n, (l : K⟦X⟧) ^ i * E K l e ^ (n - 1 - i) := by
  have h := (Commute.all ((l : K⟦X⟧)) (E K l e)).geom_sum₂_mul n
  have hE : (l : K⟦X⟧) - E K l e = -((X : K⟦X⟧) ^ e) := by simp [E]
  rw [hE] at h
  linear_combination -h

theorem l_pow_smul (n : ℕ) (y : Vec K a ι) : (l : K) ^ n • y =
    E K l e ^ n • y - (X : K⟦X⟧) ^ e • ∑ i ∈ Finset.range n, ((l ^ i : ℕ)) • (E K l e ^ (n - 1 - i) • y : Vec K a ι) := by
  have h1 : (l : K) ^ n • y = ((l : K⟦X⟧)) ^ n • y := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h1, l_pow_eq (e := e), sub_smul, mul_smul, Finset.sum_smul]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

variable (D : BKDat O K l e a ι η H)

theorem E_pow_smul_mem_M (j : ℕ) {m : Vec K a ι} (hm : m ∈ D.M) : E K l e ^ j • m ∈ D.M := by
  have := D.M.smul_mem (EIn l e (A O K) ^ j) hm
  simpa [Subalgebra.smul_def] using this

theorem E_pow_smul_mem_EM (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.EM η) : E K l e ^ j • y ∈ D.EM η := by
  rw [mem_divE] at hy ⊢
  rw [smul_comm]
  exact E_pow_smul_mem_M D j hy

theorem E_pow_smul_mem_Y (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.Y) : E K l e ^ j • y ∈ D.Y := by
  rw [BKDat.Y, Descent.mem_invOf] at hy ⊢
  exact ⟨E_pow_smul_mem_EM D j hy.1, fun g => by rw [Descent.act_E_pow_smul, hy.2 g]⟩

theorem cls_E_pow_smul_mem_Z (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.EM η)
    (h : ∀ g, D.desc.actPol g (D.cls y) = D.cls y) : D.cls (E K l e ^ j • y) ∈ D.Z := by
  refine ⟨⟨_, E_pow_smul_mem_EM D j hy, rfl⟩, fun g => ?_⟩
  have h' := congrArg (D.mulPol ⟨_, pow_mem (E_mem l e (Rpi O K l e)) j⟩) (h g)
  rw [Descent.actPol_cls] at h'
  change D.desc.actPol g (D.cls (E K l e ^ j • y)) = D.cls (E K l e ^ j • y)
  rw [Descent.actPol_cls, Descent.act_E_pow_smul]
  exact h'

end GlobalTheory.NgalDivisible

namespace GlobalTheory.NgalDivisible

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}
  (D : BKDat O K l e a ι η H)

theorem l_pow_smul_Z {w : D.Pol} (hw : w ∈ D.Z) : ∃ z ∈ D.Z, (l : K) ^ η • w = D.vPol z := by
  obtain ⟨⟨y, hy, rfl⟩, h⟩ := D.desc.mem_Z.1 hw
  set s : Vec K a ι := ∑ i ∈ Finset.range η, (l ^ i : ℕ) • (E K l e ^ (η - 1 - i) • y : Vec K a ι) with hs
  have hsZ : D.cls s ∈ D.Z := by
    rw [hs, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_nsmul]
      exact Submodule.smul_of_tower_mem _ _ (cls_E_pow_smul_mem_Z D _ hy h)
  refine ⟨-D.cls s, neg_mem hsZ, ?_⟩
  have h0 : D.cls (E K l e ^ η • y) = 0 := D.cls_eq_zero_iff.2 (D.M_le_Man hy)
  rw [← map_smul, l_pow_smul (e := e) η y, ← hs, map_sub, h0, zero_sub, map_neg, PhiMod.vPol_cls]

theorem l_pow_smul_Y {y : Vec K a ι} (hy : y ∈ D.Y) : (l : K) ^ η • y ∈ D.Y' ⊔ D.Minv := by
  have hy' := hy
  rw [BKDat.Y, Descent.mem_invOf] at hy'
  set s : Vec K a ι := ∑ i ∈ Finset.range η, (l ^ i : ℕ) • (E K l e ^ (η - 1 - i) • y : Vec K a ι) with hs
  have hsY : s ∈ D.Y := Submodule.sum_mem _ fun i _ =>
    Submodule.smul_of_tower_mem _ _ (E_pow_smul_mem_Y D _ hy)
  have h1 : -((X : K⟦X⟧) ^ e • s) ∈ D.Y' :=
    D.desc.mem_Y'.2 ⟨-s, neg_mem hsY, smul_neg _ _⟩
  have h2 : E K l e ^ η • y ∈ D.Minv := by
    rw [BKDat.Minv, Descent.mem_invOf]
    exact ⟨hy'.1, fun g => by rw [Descent.act_E_pow_smul, hy'.2 g]⟩
  rw [l_pow_smul (e := e) η y, ← hs, sub_eq_neg_add]
  exact Submodule.add_mem_sup h1 h2

end GlobalTheory.NgalDivisible

theorem GlobalTheory.divisible_of_BKDat : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ)
    (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Divisible D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D
  exact ⟨fun _ hw => NgalDivisible.l_pow_smul_Z D hw, fun _ hy => NgalDivisible.l_pow_smul_Y D hy⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PseudoCharacterApplyIdempotentNatLeStatement
section
open Formalism.MainNotions.N GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ e : R, IsIdempotentElem e → (∃ m : ℕ, m ≤ d ∧ T e = m) ∧ (T e = 0 → ∀ y : R, T (e * y) = 0) := by
  first | exact @GlobalTheory.PsChar.isPsChar_idempotent | exact GlobalTheory.PsChar.isPsChar_idempotent | (intros; apply GlobalTheory.PsChar.isPsChar_idempotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PseudoCharacterEqZeroOfIsNilpotentStatement
section
open Formalism.MainNotions.N GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudoCharacter_eq_zero_of_isNilpotent : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ x : R, IsNilpotent x → T x = 0 := by
  first | exact @GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent | exact GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent | (intros; apply GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent <;> assumption)
end

