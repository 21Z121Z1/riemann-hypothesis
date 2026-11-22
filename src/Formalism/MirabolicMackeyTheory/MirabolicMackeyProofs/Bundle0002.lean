import Mathlib
import Formalism.MirabolicMackeyTheory.Bundle0001
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxPsiGood
section
open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem mem_sc {K : Type} [Field K] {Z : Type} [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] (a : K) (A : Submodule (𝓞 K) Z) (x : Z) :
    x ∈ sc a A ↔ ∃ y ∈ A, a • y = x := by
  unfold sc
  rw [Submodule.mem_map]
  rfl

theorem idxPsiGood_of (hMono : IdxMono) (hSc : IdxScaleIn) (hCut : IdxCutLe) (hInt : LatInter) :
    IdxPsiGood := by
  unfold IdxPsiGood
  intro K _ _ _ Z _ _ _ _ _ w Zψ V₀ M Th ThK Th0 hM hTh hThK hThM hTh0fg hTh0Z σ hσ hThσ u hu
    hucut a E r ha hE hr δ hδ hδi
  have hVB := valuation_basic_properties K w

  have hcc : ∀ (W W' : Submodule K Z) (A : Submodule (𝓞 K) Z), W' ≤ W →
      cut W' (cut W A) = cut W' A := by
    intro W W' A hWW
    ext x
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, hWW h3⟩, h3⟩
  set L : Submodule K Z := Zψ ⊓ V₀ with hL
  have hLZ : L ≤ Zψ := inf_le_left
  set N : Submodule (𝓞 K) Z := M ⊓ sc a⁻¹ Th with hN
  have hNl : IsLatIn ⊤ N := hInt K Z M Th hM hTh a⁻¹ (inv_ne_zero ha)
  have hNM : N ≤ M := inf_le_left
  have hX : IsLatIn L (cut L M) := (hCut K Z w ⊤ L M M hM hM le_rfl le_top).1
  have hB0 : IsLatIn L (cut L N) := (hCut K Z w ⊤ L N N hNl hNl le_rfl le_top).1
  have hMψ : IsLatIn Zψ (cut Zψ M) := (hCut K Z w ⊤ Zψ M M hM hM le_rfl le_top).1
  have hNψ : IsLatIn Zψ (cut Zψ N) := (hCut K Z w ⊤ Zψ N N hNl hNl le_rfl le_top).1
  have hThKψ : IsLatIn Zψ (cut Zψ ThK) := (hCut K Z w ⊤ Zψ ThK ThK hThK hThK le_rfl le_top).1
  have hu' : (u : K) ≠ 0 := by exact_mod_cast hu
  have hc : a * σ⁻¹ ≠ 0 := mul_ne_zero ha (inv_ne_zero hσ)

  have hTh0 : IsLatIn Zψ Th0 := by
    show Th0.FG ∧ Submodule.span K (Th0 : Set Z) = Zψ
    refine ⟨hTh0fg, le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.mpr (fun x hx => hTh0Z hx)
    · have h1 := (hSc K Z w Zψ (cut Zψ ThK) (cut Zψ ThK) hThKψ hThKψ (u : K) hu').1
      have h2 : Submodule.span K ((sc (u : K) (cut Zψ ThK) : Submodule (𝓞 K) Z) : Set Z) = Zψ :=
        h1.2
      rw [← h2]
      exact Submodule.span_mono (SetLike.coe_subset_coe.mpr hucut)
  have hcutTh0 : cut V₀ Th0 = cut L Th0 := by
    ext x
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem, hL]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hTh0Z h1, h2⟩
    · rintro ⟨h1, _, h2⟩
      exact ⟨h1, h2⟩
  have hT : IsLatIn L (cut V₀ Th0) := by
    rw [hcutTh0]
    exact (hCut K Z w Zψ L Th0 Th0 hTh0 hTh0 le_rfl hLZ).1
  refine ⟨hT, ?_⟩
  have hB1 := hSc K Z w L (cut L M) (cut L N) hX hB0 (a * σ⁻¹) hc
  have hB2 := hSc K Z w L (cut L M) (sc (a * σ⁻¹) (cut L N)) hX hB1.1 (u : K) hu'

  have hle2 : sc (u : K) (sc (a * σ⁻¹) (cut L N)) ≤ cut V₀ Th0 := by
    intro x hx
    rw [mem_sc] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_sc] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem, hN, hL] at hz ⊢
    obtain ⟨⟨_, hz2⟩, hzψ, hzV⟩ := hz
    rw [mem_sc] at hz2
    obtain ⟨t, ht, rfl⟩ := hz2
    obtain ⟨k, hk, rfl⟩ := (mem_sc σ ThK t).1 (hThσ ht)
    have hkey : (a * σ⁻¹) • a⁻¹ • σ • k = k := by
      rw [smul_smul, smul_smul]
      have h1 : a * σ⁻¹ * a⁻¹ * σ = 1 := by field_simp
      rw [h1, one_smul]
    have hkψ : k ∈ Zψ := by
      have h1 := Zψ.smul_mem (a * σ⁻¹) hzψ
      rwa [hkey] at h1
    have hkV : k ∈ V₀ := by
      have h1 := V₀.smul_mem (a * σ⁻¹) hzV
      rwa [hkey] at h1
    rw [hkey]
    have hkc : k ∈ cut Zψ ThK := by
      simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem]
      exact ⟨hk, hkψ⟩
    exact ⟨hucut ((mem_sc _ _ _).2 ⟨k, hkc, rfl⟩), V₀.smul_mem _ hkV⟩
  have hmono := hMono K Z w L (cut L M) (sc (u : K) (sc (a * σ⁻¹) (cut L N))) (cut V₀ Th0)
    hX hB2.1 hT hle2
  have hNMψ : cut Zψ N ≤ cut Zψ M := by
    unfold cut
    exact inf_le_inf_right _ hNM
  have hcut2 := (hCut K Z w Zψ L (cut Zψ M) (cut Zψ N) hMψ hNψ hNMψ hLZ).2.2
  rw [hcc Zψ L M hLZ, hcc Zψ L N hLZ] at hcut2
  have hv : vw w (a * σ⁻¹) = (E : ℤ) - vw w σ := by
    rw [hVB.1 a σ⁻¹ ha (inv_ne_zero hσ), hVB.2.2.2.2.2.1 σ, hE]
    ring
  rw [hB2.2, hB1.2, hv] at hmono
  have h1 : (δ : ℝ) * (lix w (cut Zψ M) (cut Zψ N) : ℝ) ≤
      (lix w M N : ℝ) + (finrank K Z : ℝ) * (vw w (u : K) : ℝ) := by
    exact_mod_cast hδi
  have hJ : (lix w (cut Zψ M) (cut Zψ N) : ℝ) ≤
      (r + (finrank K Z : ℝ) * (vw w (u : K) : ℝ)) / (δ : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hδ)]
    linarith
  have hm : (lix w (cut L M) (cut V₀ Th0) : ℝ) ≤ (lix w (cut L M) (cut L N) : ℝ) +
      (finrank K L : ℝ) * ((E : ℝ) - (vw w σ : ℝ)) + (finrank K L : ℝ) * (vw w (u : K) : ℝ) := by
    exact_mod_cast hmono
  have hc2 : (lix w (cut L M) (cut L N) : ℝ) ≤ lix w (cut Zψ M) (cut Zψ N) := by
    exact_mod_cast hcut2
  nlinarith

end Formalism.EigenvalueLevelCeiling
end

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OnExport
section
open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem onExport_of (hR : RamBasic) : OnExport := by
  classical
  intro K _ _ _ D hD Tup μ J _ d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 hsh hv
    hdep htw hEA hRb hEJ hE3
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hp, hr1, hpc, hrc, hell⟩ := hR K w
    have hρ : (1 : ℝ) ≤ (ramw w : ℝ) := by exact_mod_cast hr1
    obtain ⟨hv0, hvc, hvg⟩ := hv w hw
    have hl : (0 : ℝ) < (plc w : ℝ) ^ 2 := by
      have : (0 : ℝ) < (plc w : ℝ) := by exact_mod_cast hp.pos
      positivity
    have key : ∀ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
          (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
        (2 * ((ramw w : ℝ) * F0 w j) +
            (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)))) * D +
          (ramw w : ℝ) * (ε0 w j + ε0 (conjPl w) j) := by
      intro j
      have a1 := h1 w hw j
      have a2 := h2 w hw j
      rw [hrc, hvc] at a2
      have hdj : (d j : ℝ) = D := by exact_mod_cast hd j
      rw [hdj] at a1 a2
      have a3 := hdep w hw j
      have a4 := hsh j
      have e1 : (r0 w j + dK j * vU0 w) / δq = r0 w j / δq + dK j / δq * vU0 w := by
        field_simp
      have e2 : (r0 (conjPl w) j + dK j * vU0 w) / δq = r0 (conjPl w) j / δq + dK j / δq * vU0 w := by
        field_simp
      have e3 : (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)) * D = r0 w j / δq + r0 (conjPl w) j / δq := by
        field_simp
      rw [e1] at a1
      rw [e2] at a2
      have b1 : dK j / δq * vU0 w ≤ 3 * (D : ℝ) * vU0 w := mul_le_mul_of_nonneg_right a4 hv0
      have b2 : (e0 w j + e0 (conjPl w) j + 8 * vU0 w) * (D : ℝ) ≤ (2 * F0 w j + errl w j) * D :=
        mul_le_mul_of_nonneg_right (by linarith) hDr.le
      have b3 : ((e0 w j + vU0 w) * (D : ℝ) + (r0 w j / δq + dK j / δq * vU0 w) + ε0 w j) +
          ((e0 (conjPl w) j + vU0 w) * (D : ℝ) + (r0 (conjPl w) j / δq + dK j / δq * vU0 w) +
            ε0 (conjPl w) j) ≤
          (2 * F0 w j + errl w j) * D + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)) * D +
            (ε0 w j + ε0 (conjPl w) j) := by
        rw [e3]; nlinarith
      have b4 := mul_le_mul_of_nonneg_left b3 (by linarith : (0 : ℝ) ≤ (ramw w : ℝ))
      calc _ ≤ _ := add_le_add a1 a2
        _ = (ramw w : ℝ) * (((e0 w j + vU0 w) * (D : ℝ) + (r0 w j / δq + dK j / δq * vU0 w) + ε0 w j) +
          ((e0 (conjPl w) j + vU0 w) * (D : ℝ) + (r0 (conjPl w) j / δq + dK j / δq * vU0 w) +
            ε0 (conjPl w) j)) := by ring
        _ ≤ _ := b4
        _ = _ := by ring
    calc _ ≤ _ := Finset.sum_le_sum (fun j _ => key j)
      _ = (∑ j, (2 * ((ramw w : ℝ) * F0 w j) +
            (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))))) * D +
          (ramw w : ℝ) * ∑ j, (ε0 w j + ε0 (conjPl w) j) := by
            rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      _ ≤ _ := by
        rw [hell, add_mul]
        have c1 := mul_le_mul_of_nonneg_left (htw w hw) (by linarith : (0 : ℝ) ≤ (ramw w : ℝ))
        have c2 : (ramw w : ℝ) * (1 / (plc w : ℝ) ^ 2) ≤ (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2) * D := by
          have c3 : (0 : ℝ) ≤ (ramw w : ℝ) * (1 / (plc w : ℝ) ^ 2) := by positivity
          have c4 : (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2) = 2 * ((ramw w : ℝ) * (1 / (plc w : ℝ) ^ 2)) := by
            ring
          rw [c4]; nlinarith
        linarith
  · intro j
    have hc : ∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 (conjPl w) j) ≤ Rb j := by
      have hinj : Set.InjOn (conjPl (K := K)) S := by
        intro a _ b _ hab
        have := congrArg conjPl hab
        rwa [(valuation_basic_properties K a).2.2.2.1, (valuation_basic_properties K b).2.2.2.1] at this
      have := hRb j (S.image conjPl)
      rw [Finset.sum_image hinj] at this
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [(valuation_basic_properties K w).2.2.1, (hR K w).2.2.2.1]
    have hpos : (0 : ℝ) < δq * D := mul_pos hδ hDr
    have e : ∑ w ∈ S, lw w * ((ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))) +
          Jx w j) =
        ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w j) +
          (∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 w j) + ∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 (conjPl w) j)) /
            (δq * (D : ℝ)) + ∑ w ∈ S, lw w * Jx w j := by
      rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      ring
    rw [e]
    have f1 : (∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 w j) +
        ∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 (conjPl w) j)) / (δq * (D : ℝ)) ≤ 2 * Rb j / (δq * (D : ℝ)) :=
      div_le_div_of_nonneg_right (by linarith [hRb j S]) hpos.le
    linarith [hEA j, hEJ j]
  · refine le_trans (le_of_eq ?_) hE3
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [(hR K w).2.2.2.2]

end Formalism.EigenvalueLevelCeiling
end

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.UnipotentNumeric
section
namespace Formalism.EigenvalueLevelCeiling

theorem depth_cases : DepthCases := by
  unfold DepthCases
  intro e ec F
  refine ⟨fun a h1 h2 => by linarith, fun h1 h2 h3 => by linarith,
    fun s T β h1 h2 h3 h4 => by linarith, fun s T h1 h2 h3 => by linarith,
    fun T nn nnc g2 h1 h2 h3 => by linarith⟩

theorem unipotent_numeric : UnipNum := by
  unfold UnipNum
  intro f r d dK δq hf hr hd hq
  have hr0 : 0 ≤ r - 1 := by linarith
  have hA : 0 ≤ f * r * (r - 1) / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hf (by linarith)) hr0) (by norm_num)
  have h1 : f * r * (r - 1) / 2 * (d + dK / δq) ≤ f * r * (r - 1) / 2 * (4 * d) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  have h2 : 0 ≤ f * r * d := mul_nonneg (mul_nonneg hf (by linarith)) hd
  have h3 : f * r * (r - 1) / 2 * (4 * d) = 2 * f * r ^ 2 * d - 2 * (f * r * d) := by ring
  linarith

theorem budget_numeric : BudgetNum := by
  unfold BudgetNum
  intro dK δq D B hδ hD hB hq
  rw [div_le_iff₀ (mul_pos hδ hD)]
  have h1 : dK ≤ 3 * D * δq := (div_le_iff₀ hδ).mp hq
  have h2 : dK * B ≤ 3 * D * δq * B := mul_le_mul_of_nonneg_right h1 hB
  linarith

theorem share_numeric : ShareNum := by
  unfold ShareNum
  intro dK d0 d U δq ep y del hU hδ hdK hd0 hep hey hy hdel hdel' h1 h2 h3
  rw [div_le_iff₀ hδ]
  have k1 : 7 / 8 * dK ≤ U * d0 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 8 - ep) hdK]
  have k2 : 7 / 8 * U ≤ δq := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 8 - y) hU.le]
  have k3 : 3 / 4 * d0 ≤ d := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 4 - del) hd0]
  have hd : 0 ≤ d := by linarith
  have k4 : d * (7 / 8 * U) ≤ d * δq := mul_le_mul_of_nonneg_left k2 hd
  have k5 : 3 / 4 * d0 * U ≤ d * U := mul_le_mul_of_nonneg_right k3 hU.le
  nlinarith

theorem level_pair : LevelPair := by
  unfold LevelPair
  intro en enc T vs vsc nn nnc frn Dp Dm F h1 h2 hT hf hvs hvsc hn hF
  subst hvs hvsc hF
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem normaliser_pair : NormaliserPair := by
  unfold NormaliserPair
  intro K _ _ _ w π hπ Dp Dm
  have hV := Formalism.DivisionValues.valuation_basic_properties K w
  have hsπ : star π ≠ 0 := star_ne_zero.mpr hπ
  have hpow : ∀ x : K, x ≠ 0 → ∀ n : ℕ, Formalism.DivisionValues.vw w (x ^ n) = (n : ℤ) * Formalism.DivisionValues.vw w x := by
    intro x hx n
    induction n with
    | zero => simp [hV.2.2.2.2.1]
    | succ n ih =>
      rw [pow_succ, hV.1 _ _ (pow_ne_zero _ hx) hx, ih]
      push_cast
      ring
  rw [← hV.2.1, star_mul, star_pow, star_pow, star_star,
    hV.1 (star π ^ Dp) (π ^ Dm) (pow_ne_zero _ hsπ) (pow_ne_zero _ hπ),
    hV.1 (star π ^ Dm) (π ^ Dp) (pow_ne_zero _ hsπ) (pow_ne_zero _ hπ),
    hV.1 π (star π) hπ hsπ, hpow _ hsπ Dp, hpow _ hπ Dm, hpow _ hsπ Dm, hpow _ hπ Dp]
  ring

theorem unit_change' : UnitChange := by
  unfold UnitChange
  intro ρ x y d r k δ ε hρ hδ
  have hρ' : ρ ≠ 0 := hρ.ne'
  have hδ' : δ ≠ 0 := hδ.ne'
  first
    | (field_simp; ring)
    | field_simp

end Formalism.EigenvalueLevelCeiling
end

