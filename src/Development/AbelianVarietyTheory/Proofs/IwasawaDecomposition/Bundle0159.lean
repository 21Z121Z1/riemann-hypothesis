import Mathlib
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0152
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiChiSqrtLogBound
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.GoodLarge

theorem inv_eq_self {q : ℕ} (χ : DirichletCharacter ℂ q) (h : GlobalTheoryTheory.IsRealChar χ) : χ⁻¹ = χ := by
  rw [← MulChar.star_eq_inv]
  ext a
  rw [MulChar.star_apply]
  exact Complex.conj_eq_iff_im.2 (h _)

theorem inv_norm_le {Q : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hQ : 1 ≤ Q)
    (hg : GlobalTheoryTheory.GoodFor Q χ) {ρ : ℂ} (hρ : ρ ∈ zerosIn χ 0 1) : 1 / ‖ρ‖ ≤ 400 := by
  obtain ⟨h0, h1, hT, hL⟩ := hρ
  have h2 := ((zeros_symm_one_sub q χ hg.1 ρ h0 h1).1).1 hL
  rw [inv_eq_self χ hg.2.1] at h2
  have h3 : 1 / 400 ≤ ρ.re := by
    by_contra hc
    refine hg.2.2.2 (1 - ρ) ?_ ?_ h2
    · simp only [Complex.sub_re, Complex.one_re]; linarith
    · simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      rw [sub_zero] at hT; linarith
  have h4 : 1 / 400 ≤ ‖ρ‖ := h3.trans (Complex.re_le_norm ρ)
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem zsumR_inv_norm_one_le {Q : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hQ : 1 ≤ Q)
    (hg : GlobalTheoryTheory.GoodFor Q χ) :
    zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ 400 * zsumR χ 0 1 (fun _ => 1) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  rw [zsumR_eq_sum_toFinset χ 0 1 _ hf, zsumR_eq_sum_toFinset χ 0 1 _ hf, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have := mul_le_mul_of_nonneg_left (inv_norm_le hQ hg (by simpa using hρ))
    (Nat.cast_nonneg (α := ℝ) (zmult χ ρ))
  linarith

theorem zsumR_inv_norm_le {Q : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hQ : 1 ≤ Q)
    (hg : GlobalTheoryTheory.GoodFor Q χ) (T : ℝ) :
    zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) ≤ 400 * zsumR χ 0 1 (fun _ => 1) +
      zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) := by
  classical
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  have hf1 := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have h1 := sum_indicator_le_zsumR χ 0 1 hf.toFinset hf1
  rw [zsumR_eq_sum_toFinset χ 0 T _ hf, zsumR_eq_sum_toFinset χ 0 T _ hf]
  refine le_trans ?_ (add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) le_rfl)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hρ' : ρ ∈ zerosIn χ 0 T := by simpa using hρ
  have hm : (0 : ℝ) ≤ zmult χ ρ := Nat.cast_nonneg _
  by_cases h : 1 < |ρ.im|
  · rw [if_pos h]
    split_ifs <;> linarith
  · have h2 : ρ ∈ zerosIn χ 0 1 := ⟨hρ'.1, hρ'.2.1, by rw [sub_zero]; linarith, hρ'.2.2.2⟩
    rw [if_neg h, if_pos h2]
    have := mul_le_mul_of_nonneg_left (inv_norm_le hQ hg h2) hm
    linarith

theorem norm_zsum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u T M : ℝ)
    (h : ∀ ρ ∈ zerosIn χ 0 T, ‖(u : ℂ) ^ ρ‖ ≤ M) :
    ‖zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ M * zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  rw [zsumR_eq_sum_toFinset χ 0 T _ hf, zsum, finsum_mem_eq_finite_toFinset_sum _ hf, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  rw [norm_mul, norm_div, Complex.norm_natCast, mul_left_comm, mul_one_div]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (h ρ (by simpa using hρ)) (norm_nonneg _)) (Nat.cast_nonneg _)

theorem re_le (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
    ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 0 < Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ →
      ∀ s : ℝ, 1 ≤ s → Real.log q ≤ s → ∀ ρ ∈ zerosIn χ 0 (Real.exp s), ρ.re ≤ 1 - c / s := by
  obtain ⟨c, hc, H⟩ := hZ
  refine ⟨min (c / 4) (1 / 400), by positivity, (min_le_right _ _).trans (by norm_num), ?_⟩
  intro Q q _ χ hQ hχ hg s hs hqs ρ ⟨h0, h1, hT, hL⟩
  rw [sub_zero] at hT
  have hs0 : 0 < s := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  by_cases hR : Formalism.ZeroFreeDirichlet.InRegion c q ρ
  · have him := (H q χ ρ hR ⟨Or.inl hχ, hL⟩).2.2.1
    have h2 : ρ.re ≤ 1 - 1 / 400 := by
      by_contra hn
      exact hg.2.2.2 ρ (not_le.1 hn) (by rw [him, abs_zero]; exact hQ.le) hL
    have h3 : min (c / 4) (1 / 400) / s ≤ 1 / 400 :=
      (div_le_self (by positivity) hs).trans (min_le_right _ _)
    linarith
  · unfold Formalism.ZeroFreeDirichlet.InRegion at hR
    have ha : 0 ≤ |ρ.im| := abs_nonneg _
    have hLpos : 0 < Real.log (q * (|ρ.im| + 2)) := Real.log_pos (by nlinarith)
    have hL4 : Real.log (q * (|ρ.im| + 2)) ≤ 4 * s := by
      rw [Real.log_mul (by positivity) (by positivity)]
      have h1 : Real.log (|ρ.im| + 2) ≤ s + 2 := by
        rw [Real.log_le_iff_le_exp (by positivity), Real.exp_add]
        have e1 : 1 ≤ Real.exp s := Real.one_le_exp hs0.le
        have e2 : 3 ≤ Real.exp 2 := by
          have := Real.add_one_le_exp 2
          linarith
        nlinarith
      linarith
    have h2 : c / (4 * s) ≤ c / Real.log (q * (|ρ.im| + 2)) :=
      div_le_div_of_nonneg_left hc.le hLpos hL4
    have h3 : min (c / 4) (1 / 400) / s ≤ c / (4 * s) := by
      rw [← div_div]
      exact div_le_div_of_nonneg_right (min_le_left _ _) hs0.le
    linarith [not_le.1 hR]

theorem psi_le_of_large : GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.ExplZeta → ∃ C₁ c₁ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u → ‖psiChi χ u‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u)) := by
  intro h1 h2 h3 h4 h5
  obtain ⟨A₀, hA₀⟩ := GlobalTheory.T.norm_psi0_add_zsum_le_of_isPrimitive h5 h1 h2
  obtain ⟨B₀, hB₀⟩ := zsumR_recip_le h3
  obtain ⟨c, hc, hc1, hre⟩ := re_le h4
  set A := max A₀ 0 with hA
  set B := max B₀ 0 with hB
  have hA0 : 0 ≤ A := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  refine ⟨(1 + 1204 * B + A * (11 + 1200 * B)) * (24 / (c / 2) ^ 4), c / 2, by positivity, by positivity, ?_⟩
  intro Q q _ χ hQ hχ hg u hu
  have hQ0 : 0 < Q := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlQ : 1 ≤ Real.log Q := by
    rw [Real.le_log_iff_exp_le hQ0]
    have := Real.exp_one_lt_d9
    linarith
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu
  have hlu : Real.log Q ^ 2 ≤ Real.log u := (Real.le_log_iff_exp_le hu0).2 hu
  have hlu0 : 0 ≤ Real.log u := le_trans (sq_nonneg _) hlu
  set s := Real.sqrt (Real.log u) with hs
  have hss : s ^ 2 = Real.log u := Real.sq_sqrt hlu0
  have hQs : Real.log Q ≤ s := Real.le_sqrt_of_sq_le hlu
  have hs1 : 1 ≤ s := hlQ.trans hQs
  have hs0 : 0 < s := by linarith
  have hqs : Real.log q ≤ s := (Real.log_le_log (by linarith) hg.2.2.1).trans hQs
  have hq0 : 0 ≤ Real.log q := Real.log_nonneg hq
  have hT2 : 2 ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have hs2 : s ≤ s ^ 2 := by nlinarith
  have hs4 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by norm_num)
  have hTu : Real.exp s ≤ u := by
    rw [← Real.le_log_iff_exp_le hu0, ← hss]; exact hs2
  set M := u * Real.exp (-c * s) with hM
  have hM' : u / Real.exp s ≤ M := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hu0.le
  have hM1 : 1 ≤ M := le_trans ((one_le_div (Real.exp_pos _)).2 hTu) hM'
  have hMz : ∀ ρ ∈ zerosIn χ 0 (Real.exp s), ‖(u : ℂ) ^ ρ‖ ≤ M := by
    intro ρ hρ
    have hre' := hre Q q χ hQ0 hχ hg s hs1 hqs ρ hρ
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, Real.rpow_def_of_pos hu0]
    have e : M = Real.exp (Real.log u * (1 - c / s)) := by
      rw [hM]
      conv_lhs => rw [← Real.exp_log hu0]
      rw [← Real.exp_add, ← hss]
      congr 1
      field_simp
      ring
    rw [e]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hre' hlu0)
  obtain ⟨hb1, hb2⟩ := hB₀ q χ hg.1 (Real.exp s) hT2
  have hl1 : Real.log (q * Real.exp s) ^ 2 ≤ 4 * s ^ 4 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
    nlinarith
  have hl2 : Real.log (3 * q) ≤ 3 * s ^ 4 := by
    rw [Real.log_mul (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num)
    linarith
  have hl2' : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
  have hc1' : zsumR χ 0 (Real.exp s) (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) ≤ B * (4 * s ^ 4) :=
    hb1.trans (mul_le_mul (le_max_left _ _) hl1 (sq_nonneg _) hB0)
  have hc2 : zsumR χ 0 1 (fun _ => 1) ≤ B * (3 * s ^ 4) :=
    hb2.trans (mul_le_mul (le_max_left _ _) hl2 hl2' hB0)
  have hS1 : zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ 1200 * B * s ^ 4 := by
    have := zsumR_inv_norm_one_le (by linarith) hg
    linarith
  have hS0 : 0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
    rw [zsumR_eq_sum_toFinset χ 0 1 _ (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1]
    exact Finset.sum_nonneg fun ρ _ => by positivity
  have hST : zsumR χ 0 (Real.exp s) (fun ρ => 1 / ‖ρ‖) ≤ 1204 * B * s ^ 4 := by
    have := zsumR_inv_norm_le (by linarith) hg (Real.exp s)
    linarith
  have hZ : ‖zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ M * (1204 * B * s ^ 4) :=
    (norm_zsum_le χ u _ M hMz).trans (mul_le_mul_of_nonneg_left hST (by linarith))
  have hE := hA₀ q χ hg.1 u (Real.exp s) hT2 hTu
  have hp : GlobalTheoryTheory.psi0 χ u = psiChi χ u := by
    rw [GlobalTheoryTheory.psi0, if_neg hχ, sub_zero, psiChi]
  rw [hp] at hE
  have hl3 : Real.log (q * u * Real.exp s) ^ 2 ≤ 9 * s ^ 4 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, ← hss]
    calc _ ≤ (3 * s ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = _ := by ring
  have hl4 : Real.log (q * u) ≤ 2 * s ^ 4 := by
    rw [Real.log_mul (by positivity) (by positivity), ← hss]
    linarith
  have hl4' : 0 ≤ Real.log (q * u) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    linarith
  have he1 : u * Real.log (q * u * Real.exp s) ^ 2 / Real.exp s ≤ M * (9 * s ^ 4) := by
    rw [mul_div_right_comm]
    exact mul_le_mul hM' hl3 (sq_nonneg _) (by linarith)
  have he2 : 2 * s ^ 4 + 1200 * B * s ^ 4 ≤ M * (2 * s ^ 4 + 1200 * B * s ^ 4) :=
    le_mul_of_one_le_left (by positivity) hM1
  have hE' : ‖psiChi χ u + zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤
      A * (M * (9 * s ^ 4) + M * (2 * s ^ 4 + 1200 * B * s ^ 4)) :=
    hE.trans (mul_le_mul (le_max_left _ _) (by linarith)
      (add_nonneg (add_nonneg (by positivity) hl4') hS0) hA0)
  have hfin : ‖psiChi χ u‖ ≤ (1 + 1204 * B + A * (11 + 1200 * B)) * (M * s ^ 4) := by
    have h := norm_sub_le (psiChi χ u + zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ))
      (zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ))
    rw [add_sub_cancel_right] at h
    have : 0 ≤ M * s ^ 4 := by positivity
    linarith
  have hsq : s ^ 4 ≤ 24 / (c / 2) ^ 4 * Real.exp (c / 2 * s) := by
    have h := Real.pow_div_factorial_le_exp (c / 2 * s) (by positivity) 4
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rw [mul_pow] at h
    norm_num [Nat.factorial] at h
    linarith
  refine hfin.trans ?_
  have e : Real.exp (-(c / 2) * s) = Real.exp (-c * s) * Real.exp (c / 2 * s) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ ≤ (1 + 1204 * B + A * (11 + 1200 * B)) * (M * (24 / (c / 2) ^ 4 * Real.exp (c / 2 * s))) := by
        gcongr
    _ = _ := by rw [e, hM]; ring

end GlobalTheory.Mem.An.GoodLarge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldFinrankPowPrincipalStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassField_finrank_pow_principal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)), IsRayField K L 𝔮 → ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 → ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I ^ Module.finrank K L * Ideal.span {β} = Ideal.span {α} := by
  first | exact @GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal | exact GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal | (intros; apply GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueCompFormalCompletionStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_comp_formal_completion : ∀ (A B R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing R] [IsDomain R] [IsLocalRing R] (f : A →+* B) (g : A →+* R), IsNoetherianRing A → IsNoetherianRing R → Algebra.EssFiniteType ℤ B → IsLocalHom f → Function.Injective f → (∀ b : B, ∃ a s : A, f s ≠ 0 ∧ f s * b = f a) → IsLocalHom g → GlobalTheory.Toroidal.IsEtaleCompletion g → ((IsLocalRing.residue R).comp g).FormallyUnramified → ∃ (C : Type) (_ : CommRing C) (_ : IsDomain C) (_ : IsLocalRing C) (φ : R →+* C) (ψ : B →+* C), IsNoetherianRing C ∧ IsLocalHom φ ∧ Function.Injective φ ∧ IsLocalHom ψ ∧ Function.Injective ψ ∧ ψ.Flat ∧ (IsLocalRing.maximalIdeal B).map ψ = IsLocalRing.maximalIdeal C ∧ ((IsLocalRing.residue C).comp ψ).Finite ∧ ((IsLocalRing.residue C).comp ψ).FormallyUnramified ∧ ψ.comp f = φ.comp g := by
  first | exact @GlobalTheory.LocalChart.exists_localised_base_change | exact GlobalTheory.LocalChart.exists_localised_base_change | (intros; apply GlobalTheory.LocalChart.exists_localised_base_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterValueViaPowerGeneratorStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameHeckeCharacter_value_via_power_generator : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ w, w ∉ S → χ.UnrAt w) → (∀ w ∈ S, χ.TameAt w) → ∀ (v : HeightOneSpectrum (𝓞 L)), v ∉ S → ∀ (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → (∀ w ∈ S, w.valuation L ((k : L) - 1) < 1) → χ.inf k * χ.val v ^ h = 1 := by
  first | exact @GlobalTheory.Mem.ValPow.inf_mul_val_pow | exact GlobalTheory.Mem.ValPow.inf_mul_val_pow | (intros; apply GlobalTheory.Mem.ValPow.inf_mul_val_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorLocalizationNoetherianStatement
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_localization_noetherian : ∀ (A D R : Type) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D] [Algebra A D] [IsLocalHom (algebraMap A D)] [Algebra.EssFiniteType A D] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R], IsEtaleCompletion (algebraMap A R) → ((residue R).comp (algebraMap A R)).FormallyUnramified → ∀ (q : Ideal (D ⊗[A] R)) [q.IsPrime], (∀ d ∈ maximalIdeal D, d ⊗ₜ[A] (1 : R) ∈ q) → IsNoetherianRing (Localization.AtPrime q) ∧ IsLocalHom ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))) ∧ ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))).Flat ∧ (maximalIdeal D).map ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))) = maximalIdeal (Localization.AtPrime q) ∧ ((residue (Localization.AtPrime q)).comp ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R)))).Finite ∧ ((residue (Localization.AtPrime q)).comp ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R)))).FormallyUnramified := by
  first | exact @GlobalTheory.LocalChart.localised_base_change_at_prime | exact GlobalTheory.LocalChart.localised_base_change_at_prime | (intros; apply GlobalTheory.LocalChart.localised_base_change_at_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorLocalizationNormalDomainStatement
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_localization_normal_domain : ∀ (A B D R : Type) [CommRing A] [CommRing B] [CommRing D] [CommRing R] [Algebra A B] [Algebra A D] [Algebra A R] (ι : D →ₐ[A] B), Function.Injective ι → (∀ b, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a) → ∀ (Q : Ideal (B ⊗[A] R)) [Q.IsPrime] (q : Ideal (D ⊗[A] R)) [q.IsPrime], Q.comap (Algebra.TensorProduct.map ι (AlgHom.id A R)) ≤ q → IsDomain (Localization.AtPrime q) → IsIntegrallyClosed (Localization.AtPrime q) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.normal_atPrime_tensor_of_chart_localization | exact GlobalTheory.normal_atPrime_tensor_of_chart_localization | (intros; apply GlobalTheory.normal_atPrime_tensor_of_chart_localization <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorPrimeContractionMaximalStatement
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_prime_contraction_maximal : ∀ (A C R : Type) [CommRing A] [CommRing C] [CommRing R] [Algebra A C] [Algebra A R] (Q : Ideal (C ⊗[A] R)) [Q.IsPrime], ∃ (Q' : Ideal (Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R)) ⊗[A] R)) (_ : Q'.IsPrime), Q'.comap (Algebra.TensorProduct.includeLeft : Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R)) →ₐ[A] _ ⊗[A] R) = maximalIdeal _ ∧ (IsDomain (Localization.AtPrime Q') → IsIntegrallyClosed (Localization.AtPrime Q') → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) := by
  first | exact @GlobalTheory.BaseChangeLoc.localization_atPrime_tensor | exact GlobalTheory.BaseChangeLoc.localization_atPrime_tensor | (intros; apply GlobalTheory.BaseChangeLoc.localization_atPrime_tensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueDtPackRelDet
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.Chr

def trueDtPack {R : Ranks} {H : Formalism.BasicNotions.Host R} {e : Fin R.m → R.Psi → ℚ} (C : HFrame H e) : DtPack H :=
  letI := H.cmStar
  { Dt := DtT H
    instDt := inferInstance
    muTil := muTilT H C.mu0
    chiD := tildeD H C.chiPsi
    UO := UOT H
    chiD_UO := (GlobalTheory.T.tilde_character_on_unitary R H C.chiPsi C.isChi).1
    e1Dt := e1T H
    rest_detCharacter_on_unitary_eq := (GlobalTheory.T.tilde_character_on_unitary R H C.chiPsi C.isChi).2
    relDet := fun N L L' => relDetT H N L.1 L'.1
    relDet_self := fun N => (GlobalTheory.T.relativeLatticeDeterminantClass_laws R H N).1
    relDet_mul := fun N => (GlobalTheory.T.relativeLatticeDeterminantClass_laws R H N).2.1
    relDet_smul := fun N => (GlobalTheory.T.relativeLatticeDeterminantClass_laws R H N).2.2 }

end GlobalTheory.Mem.Chr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedHeckeCharIdeleValueUniformiserStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedHeckeChar_idele_value_uniformiser : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (h : Formalism.L2.NC.HC E), h.χ = (χ : Ideles E →* ℂˣ) → ∀ (v : HeightOneSpectrum (𝓞 E)), (χ.UnrAt v → h.At v (χ.val v)) ∧ (χ.UnrAt v ↔ h.Unr v) := by
  first | exact @GlobalTheory.HeckeUnifVal.at_val_and_unr_iff | exact GlobalTheory.HeckeUnifVal.at_val_and_unr_iff | (intros; apply GlobalTheory.HeckeUnifVal.at_val_and_unr_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPowClassNumber
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.ChiVal

theorem val_pow_classNumber {L : Type} [Field L] [NumberField L] (ξ : HChar L) (hu : ∀ v, ξ.UnrAt v) (hi : ∀ k, ξ.inf k = 1)
    (v : HeightOneSpectrum (𝓞 L)) : ξ.val v ^ classNumber L = 1 := by
  obtain ⟨γ, h0, hγ⟩ := GlobalTheory.Mem.FieldsEx.exists_gen v.asIdeal v.ne_bot
  have h1 : (γ : L) ≠ 0 := by exact_mod_cast h0
  have h2 := GlobalTheory.Mem.ValPow.inf_mul_val_pow L ξ ∅ (fun w _ => hu w) (fun w hw => absurd hw (Finset.notMem_empty w)) v
    (Finset.notMem_empty v) (classNumber L) (Units.mk0 _ h1)
    (by rw [← FractionalIdeal.coeIdeal_pow, hγ, FractionalIdeal.coeIdeal_span_singleton]; rfl)
    (fun w hw => absurd hw (Finset.notMem_empty w))
  rwa [hi, one_mul] at h2

theorem mem_of_pow_eq_one (M : Subfield ℂ) {n : ℕ} (hn : n ≠ 0)
    (hM : Complex.exp (2 * Real.pi * Complex.I / (n : ℕ)) ∈ M) {x : ℂ} (hx : x ^ n = 1) : x ∈ M := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, -, rfl⟩ := (Complex.isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one hx
  exact pow_mem hM i

theorem val_sq_eq {L : Type} [Field L] [NumberField L] (η : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    ((η.val v : ℂˣ) : ℂ) * ((η.val v : ℂˣ) : ℂ) = η.valTw (1 / 2) v ^ 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := by
  have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(((1 / 2 : ℝ)) : ℂ))) ^ 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = 1 := by
    rw [sq, ← Complex.cpow_add _ _ h0, show -(((1 / 2 : ℝ)) : ℂ) + -(((1 / 2 : ℝ)) : ℂ) = -1 by push_cast; ring,
      Complex.cpow_neg_one, inv_mul_cancel₀ h0]
  unfold HChar.valTw
  rw [mul_pow, mul_assoc, h1, mul_one, sq]

theorem chiId_mem {L : Type} [Field L] [NumberField L] (χ : HChar L) (M : Subfield ℂ)
    (h : ∀ w, ((χ.val w : ℂˣ) : ℂ) ∈ M) (𝔞 : Submodule (𝓞 L) L) : chiId χ 𝔞 ∈ M := by
  unfold chiId
  refine finprod_induction (fun u : ℂˣ => (u : ℂ) ∈ M) (one_mem M) (fun a b ha hb => mul_mem ha hb) fun w => ?_
  rw [Units.val_pow_eq_pow_val]
  exact pow_mem (h w) _

theorem chi_values : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok →
    (∀ w, ∃ k : B.LL, B.embLL k = ((I.C.chiPsi.val w : ℂˣ) : ℂ)) ∧ ∀ 𝔞, ∃ k : B.LL, B.embLL k = I.chi 𝔞 := by
  intro B X I h
  have key : ∀ w, ((I.C.chiPsi.val w : ℂˣ) : ℂ) ∈ B.embLL.fieldRange := by
    intro w
    have hc := I.C.isEta.sq_chiPsi.div_cls I.C.isChi
    have h1 := val_pow_classNumber _ hc.unr hc.inf w
    obtain ⟨z, -, hz⟩ := B.roots_Ks' (classNumber B.host.E) (by simp)
    have h2 : (((I.C.chiPsi * (I.C.eta * I.C.eta)⁻¹).val w : ℂˣ) : ℂ) ∈ B.embLL.fieldRange :=
      mem_of_pow_eq_one B.embLL.fieldRange (classNumber_ne_zero B.host.E) ⟨z, hz⟩
        (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
    have h3 : I.C.eta.valTw (1 / 2) w ∈ B.embLL.fieldRange := ⟨_, h.ch_tied.etaVal w⟩
    have h4 : I.C.chiPsi.val w = (I.C.chiPsi * (I.C.eta * I.C.eta)⁻¹).val w * (I.C.eta.val w * I.C.eta.val w) := by
      rw [HChar.val_mul, HChar.val_inv, HChar.val_mul, inv_mul_cancel_right]
    rw [h4, Units.val_mul, Units.val_mul (I.C.eta.val w), val_sq_eq]
    exact mul_mem h2 (mul_mem (pow_mem h3 2) (natCast_mem _ _))
  exact ⟨key, fun 𝔞 => chiId_mem _ _ key 𝔞⟩

end GlobalTheory.Mem.ChiVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedCompAtDetIdl
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin unif ordF)
open GlobalTheory.CharValCompare (IsFr)

namespace GlobalTheory.Mem.Col2.DetProj

section General

variable {E : Type} [Field E] [NumberField E]

theorem valuation_eq_exp (w : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    w.valuation E (k : E) = WithZero.exp (-ordF w k) := by
  unfold ordF
  rw [neg_neg, WithZero.exp_log (by simp)]

variable [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem ordSub_conjP (p : DecoF E n ST SG Q) (w : HeightOneSpectrum (𝓞 E)) :
    ordSub (conjPrime₂ w) (detSub p.deco.1.N) = -ordSub w (detSub p.deco.1.N) := by
  have h := CharValCompare.val_dual (P := w) ⟨p.deco.2.lat, p.deco.2.uni⟩ (isFr_ptFr p w) (isFr_ptFr p (conjPrime₂ w))
  rw [map_mul, valuation_star, CharValCompare.conjP_conjP] at h
  rw [ordSub_detSub_eq p.deco.2.lat (isFr_ptFr p w), ordSub_detSub_eq p.deco.2.lat (isFr_ptFr p (conjPrime₂ w))]
  have h' : w.valuation E ((LinearEquiv.det (ptFr p w) : Eˣ) : E) *
      (conjPrime₂ w).valuation E ((LinearEquiv.det (ptFr p (conjPrime₂ w)) : Eˣ) : E) = 1 := h
  rw [valuation_eq_exp, valuation_eq_exp, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at h'
  omega

open Classical in

theorem valued_compAt_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) (p : DecoF E n ST SG Q)
    (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (compAt w (detIdl SB p.deco.1.N (ptFr p))) = WithZero.exp (-(if w ∈ SB then ordSub w (detSub p.deco.1.N)
      else if conjPrime₂ w ∈ SB then 0 else ((ordSub w (detSub p.deco.1.N)).toNat : ℤ))) := by
  rw [compAt_detIdl SB p.deco.2.lat]
  split_ifs
  · rw [valued_algebraMap, valuation_eq_exp, ordSub_detSub_eq p.deco.2.lat (isFr_ptFr p w)]
  · simp
  · rw [map_pow, valued_algebraMap, valuation_eq_exp, ordF_unif_self, ← WithZero.exp_nsmul]
    simp

theorem valued_compAt_conjP {SB : Finset (HeightOneSpectrum (𝓞 E))} (hs : ∀ P ∈ SB, conjPrime₂ P ∉ SB)
    (p : DecoF E n ST SG Q) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (compAt w (detIdl SB p.deco.1.N (ptFr p))) =
      Valued.v (compAt (conjPrime₂ w) (detIdl SB p.deco.1.N (ptFr p))) * WithZero.exp (-ordSub w (detSub p.deco.1.N)) := by
  rw [valued_compAt_detIdl, valued_compAt_detIdl, ← WithZero.exp_add, WithZero.exp_inj, CharValCompare.conjP_conjP,
    ordSub_conjP]
  by_cases h : w ∈ SB
  · rw [if_pos h, if_neg (hs w h), if_pos h]
    omega
  · rw [if_neg h, if_neg h]
    split_ifs <;> omega

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toDtQ_detPt : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E)))
    (h : Q ⊆ SQ) (p : DecoF H.E n ST SG Q), LevOk H SG SQ → toDtQ H h (detPt H SQ p) = detPt H Q p := by
  intro R H n ST SG Q SQ h p hL
  classical
  have hL' := hL.mono h
  have hsub : uSG SG Q ⊆ uSG SG SQ := by
    intro P
    simp only [Finset.mem_union]
    exact Or.imp_right fun h' => h h'
  unfold detPt
  rw [toDtQ_mk]
  symm
  rw [QuotientGroup.eq, inv_mul_eq_div]
  have h0 : ∀ w (a : Ideles H.E), compAt w a ≠ 0 := fun w a => ((Group.isUnit a).map (compAt w)).ne_zero
  refine mem_KDq_of_conj hL' _ (fun w => ?_) fun P hP => ?_
  · rw [map_div, map_div, map_div₀, map_div₀]
    unfold ptIdl
    rw [valued_compAt_conjP hL.split p w, valued_compAt_conjP hL'.split p w, mul_div_mul_right _ _ WithZero.exp_ne_zero]
  · have e1 : compAt P (ptIdl H SQ p / ptIdl H Q p) = 1 := by
      rw [map_div, div_eq_one_iff_eq (h0 _ _)]
      unfold ptIdl
      rw [compAt_detIdl _ p.deco.2.lat, compAt_detIdl _ p.deco.2.lat, if_pos hP, if_pos (hsub hP)]
    have e2 : compAt (conjPrime₂ P) (ptIdl H SQ p / ptIdl H Q p) = 1 := by
      rw [map_div, div_eq_one_iff_eq (h0 _ _)]
      unfold ptIdl
      rw [compAt_detIdl _ p.deco.2.lat, compAt_detIdl _ p.deco.2.lat, if_neg (hL.split P (hsub hP)),
        if_neg (hL'.split P hP), CharValCompare.conjP_conjP, if_pos hP, if_pos (hsub hP)]
    have e3 := valued_sigR (host_cmData R H) P ((finAf H.F H.E (ptIdl H SQ p / ptIdl H Q p) : AfE H.F H.E) - 1)
    rw [map_sub (adAt _ _), adAt_finAf, e2, map_one (adAt _ _), sub_self, map_zero, Valuation.zero_iff,
      map_sub (Formalism.UG.sigR _ _), map_one (Formalism.UG.sigR _ _), map_sub (adAt _ _), map_one (adAt _ _), sub_eq_zero] at e3
    rw [e1, e3, div_one, sub_self, map_zero]
    exact zero_lt_one

end GlobalTheory.Mem.Col2.DetProj
end
end

