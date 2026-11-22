import Mathlib
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0139
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0014
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0137
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLastRowDivisibleStabilizesLattices
import Formalism.LocalToGlobal.Columns.RecLevelLocK

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiChiPowerSavingBound
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.GoodBound

theorem inv_eq_self_of_real {q : ℕ} (χ : DirichletCharacter ℂ q) [NeZero q] (h : GlobalTheoryTheory.IsRealChar χ) :
    χ⁻¹ = χ := by
  rw [← MulChar.star_eq_inv]
  ext a
  rw [MulChar.star_apply]
  exact Complex.conj_eq_iff_im.2 (h _)

theorem re_bounds {Q T : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hg : GlobalTheoryTheory.GoodFor Q χ)
    (hT : T ≤ Q) {ρ : ℂ} (hρ : ρ ∈ zerosIn χ 0 T) : 1 / 400 ≤ ρ.re ∧ ρ.re ≤ 1 - 1 / 400 := by
  obtain ⟨hp, hr, -, hz⟩ := hg
  obtain ⟨h0, h1, h2, h3⟩ := hρ
  rw [sub_zero] at h2
  refine ⟨?_, not_lt.1 fun h => hz ρ h (h2.trans hT) h3⟩
  by_contra hlt
  have h4 := (zeros_symm_one_sub q χ hp ρ h0 h1).1.1 h3
  rw [inv_eq_self_of_real χ hr] at h4
  refine hz (1 - ρ) ?_ ?_ h4
  · simp only [Complex.sub_re, Complex.one_re]
    linarith [not_le.1 hlt]
  · simpa using h2.trans hT

theorem recip_le {Q T : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hg : GlobalTheoryTheory.GoodFor Q χ)
    (hT : T ≤ Q) {ρ : ℂ} (hρ : ρ ∈ zerosIn χ 0 T) : 1 / ‖ρ‖ ≤ 400 := by
  have h1 := (re_bounds hg hT hρ).1
  have h2 : ρ.re ≤ ‖ρ‖ := Complex.re_le_norm ρ
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem low_le {Q : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hg : GlobalTheoryTheory.GoodFor Q χ)
    (hQ : 1 ≤ Q) : zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ 400 * zsumR χ 0 1 (fun _ => 1) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  rw [zsumR_eq_sum_toFinset χ _ _ _ hf, zsumR_eq_sum_toFinset χ _ _ _ hf, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have := recip_le hg hQ (by simpa using hρ : ρ ∈ zerosIn χ 0 1)
  have h0 : (0 : ℝ) ≤ zmult χ ρ := Nat.cast_nonneg _
  nlinarith

theorem low_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  rw [zsumR_eq_sum_toFinset χ _ _ _ hf]
  exact Finset.sum_nonneg fun ρ _ => by positivity

theorem norm_zsum_le {Q T u : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hg : GlobalTheoryTheory.GoodFor Q χ)
    (hT : T ≤ Q) (hu : 1 ≤ u) :
    ‖zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ u ^ (1 - (1 : ℝ) / 400) *
      (zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) + 400 * zsumR χ 0 1 (fun _ => 1)) := by
  classical
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  have hf1 := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have hA : 0 ≤ u ^ (1 - (1 : ℝ) / 400) := by positivity
  have hI := sum_indicator_le_zsumR χ 0 1 hf.toFinset hf1
  refine le_trans ?_ (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hI (by norm_num))) hA)
  rw [zsumR_eq_sum_toFinset χ _ _ _ hf, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  unfold zsum
  rw [finsum_mem_eq_finite_toFinset_sum _ hf]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  have hρ' : ρ ∈ zerosIn χ 0 T := by simpa using hρ
  have h2 : ‖(u : ℂ) ^ ρ / ρ‖ ≤ u ^ (1 - (1 : ℝ) / 400) * (1 / ‖ρ‖) := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hu (re_bounds hg hT hρ').2) (by positivity)
  have h3 : 1 / ‖ρ‖ ≤ (if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) +
      400 * (if ρ ∈ zerosIn χ 0 1 then (1 : ℝ) else 0) := by
    by_cases h : 1 < |ρ.im|
    · rw [if_pos h]
      split_ifs <;> simp
    · have : ρ ∈ zerosIn χ 0 1 := ⟨hρ'.1, hρ'.2.1, by simpa using h, hρ'.2.2.2⟩
      rw [if_neg h, if_pos this]
      linarith [recip_le hg hT hρ']
  have h0 : (0 : ℝ) ≤ zmult χ ρ := Nat.cast_nonneg _
  rw [norm_mul, Complex.norm_natCast]
  calc _ ≤ (zmult χ ρ : ℝ) * (u ^ (1 - (1 : ℝ) / 400) * ((if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) +
      400 * (if ρ ∈ zerosIn χ 0 1 then (1 : ℝ) else 0))) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hA)) h0
    _ = _ := by ring

set_option maxHeartbeats 1000000 in

theorem psiChi_bound_of_goodFor : GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.ExplZeta → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ∀ u : ℝ, 2 ≤ u → ‖psiChi χ u‖ ≤ C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2) := by
  intro hE hL hZ _ hE0
  obtain ⟨C, hC⟩ := ExplUsed.explicit_formula_used hE0 hE hL
  obtain ⟨D, hD⟩ := zsumR_recip_le hZ
  refine ⟨|C| * (5 + 800 * |D|) + 801 * |D| + 1, by positivity, ?_⟩
  intro Q q _ χ hQ hχ hg u hu
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqQ : (q : ℝ) ≤ Q := hg.2.2.1
  obtain ⟨T, hT2, hTu, hTQ, huT⟩ : ∃ T : ℝ, 2 ≤ T ∧ T ≤ u ∧ T ≤ Q ∧ u / T ≤ 1 + u / Q := by
    have : 0 ≤ u / Q := by positivity
    rcases le_total u Q with h | h
    · exact ⟨u, hu, le_rfl, h, by rw [div_self (by linarith)]; linarith⟩
    · exact ⟨Q, by linarith, h, le_rfl, by linarith⟩
  have h1 := hC q χ hg.1 u T hT2 hTu
  obtain ⟨h2, h3⟩ := hD q χ hg.1 T hT2
  have h4 := norm_zsum_le hg hTQ (by linarith : (1 : ℝ) ≤ u)
  have h5 := low_le hg (by linarith : (1 : ℝ) ≤ Q)
  have h6 := low_nonneg χ
  have hpsi : GlobalTheoryTheory.psi0 χ u = psiChi χ u := by
    simp [GlobalTheoryTheory.psi0, psiChi, hχ]
  rw [hpsi] at h1
  set S := zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)
  set A := u ^ (1 - (1 : ℝ) / 400)
  set L := Real.log (u * Q) with hLdef
  set N := zsumR χ 0 1 (fun _ => (1 : ℝ))
  set R := zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)
  set H := zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0)
  have hA1 : 1 ≤ A := Real.one_le_rpow (by linarith) (by norm_num)
  have hP : 6 ≤ u * Q := by nlinarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hLL : L ≤ L ^ 2 := by nlinarith
  have h2L : Real.log ((u * Q) ^ 2) = 2 * L := by rw [Real.log_pow, hLdef]; norm_num
  have l1 : Real.log (q * T) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg (by nlinarith))
      (Real.log_le_log (by nlinarith) (by nlinarith)) 2
  have hqu : (q : ℝ) * u ≤ u * Q := by nlinarith
  have hqu1 : (1 : ℝ) ≤ q * u := by nlinarith
  have l2 : Real.log (3 * q) ≤ 2 * L := by
    rw [← h2L]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have l2' : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
  have l3 : Real.log (q * u) ≤ L := Real.log_le_log (by linarith) hqu
  have l3' : 0 ≤ Real.log (q * u) := Real.log_nonneg hqu1
  have l4 : Real.log (q * u * T) ^ 2 ≤ (2 * L) ^ 2 := by
    refine pow_le_pow_left₀ (Real.log_nonneg (by nlinarith)) ?_ 2
    rw [← h2L, sq]
    exact Real.log_le_log (by positivity)
      (mul_le_mul hqu (by nlinarith) (by linarith) (by linarith))
  have hB : 0 ≤ u / Q := by positivity
  set B := u / Q
  have hD0 := abs_nonneg D
  have hC0 := abs_nonneg C
  have hM : 0 ≤ L ^ 2 := sq_nonneg _
  have hN : N ≤ 2 * (|D| * L ^ 2) := by
    have := h3.trans ((mul_le_mul_of_nonneg_right (le_abs_self D) l2').trans
      (mul_le_mul_of_nonneg_left (l2.trans (by linarith : 2 * L ≤ 2 * L ^ 2)) hD0))
    linarith
  have hH : H ≤ |D| * L ^ 2 :=
    h2.trans ((mul_le_mul_of_nonneg_right (le_abs_self D) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left l1 hD0))
  have hS : ‖S‖ ≤ A * (801 * (|D| * L ^ 2)) :=
    h4.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have e1 : u * Real.log (q * u * T) ^ 2 / T ≤ (1 + B) * (2 * L) ^ 2 := by
    rw [mul_div_right_comm]
    exact mul_le_mul huT l4 (sq_nonneg _) (by linarith)
  have e0 : 0 ≤ u * Real.log (q * u * T) ^ 2 / T := by positivity
  set M := L ^ 2
  have hAM : M ≤ A * M := le_mul_of_one_le_left hM hA1
  have hBM : 0 ≤ B * M := mul_nonneg hB hM
  have hDM : |D| * M ≤ |D| * (A * M + B * M) := mul_le_mul_of_nonneg_left (by linarith) hD0
  have hDM' : |D| * (A * M) ≤ |D| * (A * M + B * M) := mul_le_mul_of_nonneg_left (by linarith) hD0
  have e2 : u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + R ≤
      (5 + 800 * |D|) * (A * M + B * M) := by
    have : (1 + B) * (2 * L) ^ 2 = 4 * M + 4 * (B * M) := by simp only [M]; ring
    have h7 : (5 + 800 * |D|) * (A * M + B * M) = 5 * (A * M) + 5 * (B * M) + 800 * (|D| * (A * M + B * M)) := by
      ring
    linarith
  have e3 := h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)).trans
    (mul_le_mul_of_nonneg_left e2 hC0))
  have htri : ‖psiChi χ u‖ ≤ ‖psiChi χ u + S‖ + ‖S‖ := by
    simpa using norm_sub_le (psiChi χ u + S) S
  have h8 : A * (801 * (|D| * M)) = 801 * (|D| * (A * M)) := by ring
  have h9 : (|C| * (5 + 800 * |D|) + 801 * |D| + 1) * (A * M + B * M) =
      |C| * ((5 + 800 * |D|) * (A * M + B * M)) + 801 * (|D| * (A * M + B * M)) + (A * M + B * M) := by ring
  linarith

end GlobalTheory.Mem.An.GoodBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueCompFormalCompletion
section
open IsLocalRing TensorProduct

namespace GlobalTheory.LocalChart
theorem exists_localised_base_change : ∀ (A B R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing R] [IsDomain R] [IsLocalRing R] (f : A →+* B) (g : A →+* R), IsNoetherianRing A → IsNoetherianRing R → Algebra.EssFiniteType ℤ B → IsLocalHom f → Function.Injective f → (∀ b : B, ∃ a s : A, f s ≠ 0 ∧ f s * b = f a) → IsLocalHom g → GlobalTheory.Toroidal.IsEtaleCompletion g → ((IsLocalRing.residue R).comp g).FormallyUnramified → ∃ (C : Type) (_ : CommRing C) (_ : IsDomain C) (_ : IsLocalRing C) (φ : R →+* C) (ψ : B →+* C), IsNoetherianRing C ∧ IsLocalHom φ ∧ Function.Injective φ ∧ IsLocalHom ψ ∧ Function.Injective ψ ∧ ψ.Flat ∧ (IsLocalRing.maximalIdeal B).map ψ = IsLocalRing.maximalIdeal C ∧ ((IsLocalRing.residue C).comp ψ).Finite ∧ ((IsLocalRing.residue C).comp ψ).FormallyUnramified ∧ ψ.comp f = φ.comp g := by
  intro A B R _ _ _ _ _ _ _ _ _ f g hA hR hB hfl hfi hbir hgl hEt hFU
  obtain ⟨hflat, hmax, hfin⟩ := hEt
  letI := f.toAlgebra
  letI := g.toAlgebra
  haveI : Module.Flat A R := hflat
  haveI : IsLocalHom (algebraMap A R) := hgl
  haveI : IsLocalHom (algebraMap A B) := hfl
  haveI : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨hdom, hinjR⟩ := GlobalTheory.T.tensor_domain_birational A B R hfi hbir
  haveI := hdom
  haveI : Algebra.EssFiniteType A B := Algebra.EssFiniteType.of_comp ℤ A B
  haveI : IsNoetherianRing (B ⊗[A] R) :=
    haveI := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[A] B)
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R B).toRingEquiv
  have hne : (maximalIdeal B).map (algebraMap B (B ⊗[A] R)) ≠ ⊤ := by
    intro h
    have := Ideal.comap_map_eq_self_of_faithfullyFlat (B := B ⊗[A] R) (maximalIdeal B)
    rw [h, Ideal.comap_top] at this
    exact (maximalIdeal.isMaximal B).ne_top this.symm
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
  set C := Localization.AtPrime q
  have hJ : (maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R) ≤ (maximalIdeal B).map (algebraMap B (B ⊗[A] R)) := by
    rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    have e : (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R) (g a) = algebraMap B (B ⊗[A] R) (f a) :=
      ((Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).commutes a).trans
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R).commutes a).symm
    simp only [Ideal.mem_comap]
    rw [e]
    exact Ideal.mem_map_of_mem _ (map_nonunit f a ha)
  obtain ⟨hFU1, hFin1⟩ := GlobalTheory.T.tensor_residue_unramified_finite A B R hfin hFU
  have e1 := GlobalTheory.T.localization_maximal_ideal_map B (B ⊗[A] R) _ q hJ hle hFU1 hFin1
  obtain ⟨e2, e3⟩ := GlobalTheory.T.localization_residue_finite_unram B (B ⊗[A] R) _ q (hJ.trans hle) hFU1 hFin1
  refine ⟨C, inferInstance, inferInstance, inferInstance, (algebraMap (B ⊗[A] R) C).comp (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).toRingHom, (algebraMap (B ⊗[A] R) C).comp (algebraMap B (B ⊗[A] R)), inferInstance, ?_, ?_, ?_, ?_, ?_, e1, e2, e3, ?_⟩
  · refine ((local_hom_TFAE _).out 0 2).2 ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_map]
    exact Ideal.map_mono (le_trans (hmax ▸ hJ) hle)
  · exact (IsLocalization.injective C q.primeCompl_le_nonZeroDivisors).comp hinjR
  · refine ((local_hom_TFAE _).out 0 2).2 ?_
    rw [e1]
  · refine (IsLocalization.injective C q.primeCompl_le_nonZeroDivisors).comp ?_
    show Function.Injective (algebraMap B (B ⊗[A] R))
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker, ← Ideal.map_bot (f := algebraMap B (B ⊗[A] R))]
    exact Ideal.comap_map_eq_self_of_faithfullyFlat _
  · exact RingHom.Flat.comp ((RingHom.flat_algebraMap_iff).2 (Module.Flat.baseChange A B R)) ((RingHom.flat_algebraMap_iff).2 (IsLocalization.flat C q.primeCompl))
  · ext a
    simp only [RingHom.comp_apply]
    congr 1
    exact ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R).commutes a).trans
        ((Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).commutes a).symm

end GlobalTheory.LocalChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetAutSelfNaut
section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne

def CGK.of {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N) : CGK A :=
  CGK.ofSide A

def RowWD.unram (D : D7) (m : D.what₂.FT → PlE D.host → Multiset ℂ) (h0 : ∀ σ w, (0:ℂ) ∉ m σ w)
    (hc : ∀ σ w, Multiset.card (m σ w) = D.R.r) : RowWD D where
  par σ w := WD.lpUnr _ (m σ w)
  sat := m
  dim σ w := (WD.lpUnr_spec (m σ w) (h0 σ w)).2.2.trans (hc σ w)
  tame σ _ _ := WD.tame_of_unr (WD.lpUnr_spec (m σ _) (h0 σ _)).1

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterValueViaPowerGenerator
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.ValPow

variable {L : Type} [Field L] [NumberField L]

theorem count_span_int (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) (ha : a ≠ 0) :
    FractionalIdeal.count L w (FractionalIdeal.spanSingleton (𝓞 L)⁰ (algebraMap (𝓞 L) L a)) =
      -WithZero.log (w.valuation L (algebraMap (𝓞 L) L a)) := by
  classical
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe L w (by simpa using ha),
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha]
  simp

theorem ordF_eq_count (w : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    ordF w k = FractionalIdeal.count L w (FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L)) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (k : L)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact k.ne_zero (by rw [← hab]; simp)
  have ha' : algebraMap (𝓞 L) L a ≠ 0 := by simpa using ha0
  have hb' : algebraMap (𝓞 L) L b ≠ 0 := by simpa using hb0
  unfold ordF
  rw [← hab, div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul L w (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha')
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hb')),
    FractionalIdeal.count_inv, count_span_int w a ha0, count_span_int w b hb0, map_mul, map_inv₀,
    WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha') (inv_ne_zero ((Valuation.ne_zero_iff _).2 hb')), WithZero.log_inv]
  ring

theorem locK_eq_one {χ : HChar L} {w : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt w) (k : Lˣ)
    (hk : w.valuation L ((k : L) - 1) < 1) : χ.locK w k = 1 := by
  refine h _ ?_ ?_
  · unfold IsUnitAt
    have h1 : Valued.v ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) = w.valuation L (k : L) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : L)
    rw [h1]
    have := (w.valuation L).map_one_add_of_lt hk
    rwa [add_sub_cancel] at this
  · have h1 : ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
        algebraMap L (w.adicCompletion L) ((k : L) - 1) := by
      rw [map_sub, map_one]
      rfl
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) ((k : L) - 1)) =
        w.valuation L ((k : L) - 1) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h1, h2]
    rcases eq_or_ne (w.valuation L ((k : L) - 1)) 0 with h0 | h0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hk
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      push_cast
      omega

theorem inf_mul_val_pow : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ w, w ∉ S → χ.UnrAt w) → (∀ w ∈ S, χ.TameAt w) → ∀ (v : HeightOneSpectrum (𝓞 L)), v ∉ S → ∀ (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → (∀ w ∈ S, w.valuation L ((k : L) - 1) < 1) → χ.inf k * χ.val v ^ h = 1 := by
  classical
  intro L _ _ χ S hS hT v hv h k hk h1
  rw [← GlobalTheory.HeckeProduct.hchar_productRule L χ S hS k,
    Finset.prod_eq_one (fun w hw => locK_eq_one (hT w hw) k (h1 w hw)), mul_one]
  congr 1
  rw [finprod_eq_single _ v]
  · rw [finprod_eq_if, if_pos hv, ordF_eq_count, hk, FractionalIdeal.count_pow, FractionalIdeal.count_self, mul_one,
      zpow_natCast]
  · intro w hw
    rw [ordF_eq_count, hk, FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime L w (Ne.symm hw), mul_zero,
      zpow_zero, finprod_one]

end GlobalTheory.Mem.ValPow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorLocalizationNoetherian
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory.LocalChart

theorem localised_base_change_at_prime : ∀ (A D R : Type) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D] [Algebra A D] [IsLocalHom (algebraMap A D)] [Algebra.EssFiniteType A D] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R], IsEtaleCompletion (algebraMap A R) → ((residue R).comp (algebraMap A R)).FormallyUnramified → ∀ (q : Ideal (D ⊗[A] R)) [q.IsPrime], (∀ d ∈ maximalIdeal D, d ⊗ₜ[A] (1 : R) ∈ q) → IsNoetherianRing (Localization.AtPrime q) ∧ IsLocalHom ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))) ∧ ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))).Flat ∧ (maximalIdeal D).map ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))) = maximalIdeal (Localization.AtPrime q) ∧ ((residue (Localization.AtPrime q)).comp ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R)))).Finite ∧ ((residue (Localization.AtPrime q)).comp ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R)))).FormallyUnramified := by
  intro A D R _ _ _ _ _ _ _ _ _ _ _ hEt hFU q _ hq
  obtain ⟨hflat, hmax, hfin⟩ := hEt
  haveI : Module.Flat A R := RingHom.flat_algebraMap_iff.1 hflat
  haveI : IsNoetherianRing (D ⊗[A] R) :=
    haveI := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[A] D)
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R D).toRingEquiv
  set J := (maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] D ⊗[A] R)
  have hJ : J ≤ (maximalIdeal D).map (algebraMap D (D ⊗[A] R)) := by
    show (maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] D ⊗[A] R) ≤ _
    rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    have e : (Algebra.TensorProduct.includeRight : R →ₐ[A] D ⊗[A] R) (algebraMap A R a) = algebraMap D (D ⊗[A] R) (algebraMap A D a) :=
      ((Algebra.TensorProduct.includeRight : R →ₐ[A] D ⊗[A] R).commutes a).trans
        ((Algebra.TensorProduct.includeLeft : D →ₐ[A] D ⊗[A] R).commutes a).symm
    simp only [Ideal.mem_comap]
    rw [e]
    exact Ideal.mem_map_of_mem _ (map_nonunit (algebraMap A D) a ha)
  have hle : (maximalIdeal D).map (algebraMap D (D ⊗[A] R)) ≤ q := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    rw [Ideal.mem_comap, Algebra.TensorProduct.algebraMap_apply]
    simpa using hq d hd
  obtain ⟨hFU1, hFin1⟩ := GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified A D R hfin hFU
  haveI hqm : q.IsMaximal := by
    have hJq : J ≤ q := hJ.trans hle
    haveI : Module.Finite D ((D ⊗[A] R) ⧸ J) := hFin1
    haveI : Module.Finite D ((D ⊗[A] R) ⧸ q) :=
      Module.Finite.of_surjective (Ideal.Quotient.factorₐ D hJq).toLinearMap (Ideal.Quotient.factor_surjective hJq)
    haveI : Algebra.IsIntegral D ((D ⊗[A] R) ⧸ q) := Algebra.IsIntegral.of_finite D _
    have hcomap : (⊥ : Ideal ((D ⊗[A] R) ⧸ q)).comap (algebraMap D ((D ⊗[A] R) ⧸ q)) = maximalIdeal D := by
      refine ((maximalIdeal.isMaximal D).eq_of_le ?_ ?_).symm
      · intro h
        have h1 : (1 : D) ∈ (⊥ : Ideal ((D ⊗[A] R) ⧸ q)).comap (algebraMap D ((D ⊗[A] R) ⧸ q)) := h ▸ Submodule.mem_top
        rw [Ideal.mem_comap, map_one, Ideal.mem_bot] at h1
        exact one_ne_zero h1
      · intro d hd
        rw [Ideal.mem_comap, Ideal.mem_bot, IsScalarTower.algebraMap_apply D (D ⊗[A] R) ((D ⊗[A] R) ⧸ q), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
        exact hle (Ideal.mem_map_of_mem _ hd)
    haveI : (⊥ : Ideal ((D ⊗[A] R) ⧸ q)).IsPrime := Ideal.bot_prime
    have hbot : (⊥ : Ideal ((D ⊗[A] R) ⧸ q)).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := D) _ (hcomap ▸ maximalIdeal.isMaximal D)
    exact Ideal.Quotient.maximal_of_isField q (Ring.isField_iff_maximal_bot.mpr hbot)
  have e1 := GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient D (D ⊗[A] R) J q hJ hle hFU1 hFin1
  obtain ⟨e2, e3⟩ := GlobalTheory.residue_atMaximal_finite_formallyUnramified D (D ⊗[A] R) J q (hJ.trans hle) hFU1 hFin1
  refine ⟨IsLocalization.isNoetherianRing q.primeCompl _ inferInstance, ?_, ?_, e1, e2, e3⟩
  · refine ((local_hom_TFAE _).out 0 2).2 ?_
    rw [e1]
  · exact RingHom.Flat.comp ((RingHom.flat_algebraMap_iff).2 (Module.Flat.baseChange A D R)) ((RingHom.flat_algebraMap_iff).2 (IsLocalization.flat (Localization.AtPrime q) q.primeCompl))

end GlobalTheory.LocalChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorLocalizationNormalDomain
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem normal_atPrime_tensor_of_chart_localization : ∀ (A B D R : Type) [CommRing A] [CommRing B] [CommRing D] [CommRing R] [Algebra A B] [Algebra A D] [Algebra A R] (ι : D →ₐ[A] B), Function.Injective ι → (∀ b, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a) → ∀ (Q : Ideal (B ⊗[A] R)) [Q.IsPrime] (q : Ideal (D ⊗[A] R)) [q.IsPrime], Q.comap (Algebra.TensorProduct.map ι (AlgHom.id A R)) ≤ q → IsDomain (Localization.AtPrime q) → IsIntegrallyClosed (Localization.AtPrime q) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  intro A B D R _ _ _ _ _ _ _ ι hinj hsurj Q _ q _ hle hdom hic
  letI : Algebra D B := ι.toRingHom.toAlgebra
  haveI : IsScalarTower A D B := .of_algebraMap_eq fun a ↦ (ι.commutes a).symm
  let M : Submonoid D := (IsUnit.submonoid B).comap ι.toRingHom
  haveI : IsLocalization M B :=
    { map_units := fun y ↦ y.2
      surj := fun b ↦ by
        obtain ⟨a, s, hs, h⟩ := hsurj b
        exact ⟨(a, ⟨s, hs⟩), by rw [mul_comm]; exact h⟩
      exists_of_eq := fun {x y} h ↦ ⟨1, by rw [hinj h]⟩ }
  let φ := Algebra.TensorProduct.map ι (AlgHom.id A R)
  letI : Algebra (D ⊗[A] R) (B ⊗[A] R) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower D (D ⊗[A] R) (B ⊗[A] R) := .of_algebraMap_eq fun x ↦ by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply, φ]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (D ⊗[A] R) M) (B ⊗[A] R) :=
    IsLocalization.tensorProduct_tensorProduct A R M B (by
      ext x; simp [RingHom.algebraMap_toAlgebra, φ])
  set QD := Q.comap (algebraMap (D ⊗[A] R) (B ⊗[A] R)) with hQD
  haveI : QD.IsPrime := Ideal.comap_isPrime _ _
  haveI hL : IsLocalization QD.primeCompl (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (D ⊗[A] R) M) (Localization.AtPrime Q) Q
  have hle' : q.primeCompl ≤ QD.primeCompl := fun x hx hx' ↦ hx (hle hx')
  letI : Algebra (Localization.AtPrime q) (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ q.primeCompl QD.primeCompl hle'
  haveI : IsScalarTower (D ⊗[A] R) (Localization.AtPrime q) (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ q.primeCompl QD.primeCompl hle'
  haveI : IsLocalization (QD.primeCompl.map (algebraMap (D ⊗[A] R) (Localization.AtPrime q)))
      (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ q.primeCompl QD.primeCompl hle'
  have hN : QD.primeCompl.map (algebraMap (D ⊗[A] R) (Localization.AtPrime q)) ≤
      nonZeroDivisors (Localization.AtPrime q) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    have hu : IsUnit (algebraMap (D ⊗[A] R) (Localization.AtPrime Q) c) :=
      IsLocalization.map_units (Localization.AtPrime Q) (⟨c, hc⟩ : QD.primeCompl)
    rw [IsScalarTower.algebraMap_apply (D ⊗[A] R) (Localization.AtPrime q)
      (Localization.AtPrime Q), h0, map_zero] at hu
    exact not_isUnit_zero hu
  exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors _ hN,
    isIntegrallyClosed_of_isLocalization _ _ hN⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TildeCharacterOnUnitaryStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilde_character_on_unitary : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsChiPsi H χ → (∀ x ∈ UOT H, tildeD H χ x = 1) ∧ (letI := H.cmStar; ∀ z : unitary H.E, ((tildeD H χ (e1T H z) : ℂˣ) : ℂ) = ∏ τ : R.Psi, (H.emb (τ : R.GG) (z : H.E))⁻¹) := by
  first | exact @GlobalTheory.Mem.ChiLaws.chi_laws | exact GlobalTheory.Mem.ChiLaws.chi_laws | (intros; apply GlobalTheory.Mem.ChiLaws.chi_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScaleStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cdScaleIs_trueScale' : ∀ cd : CDHaar, CdScaleIs cd (trueScale cd) := by
  first | exact @GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale | exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale | (intros; apply GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLastRowDivisibleStabilizesLatticesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lastRowDivisible_stabilizes_lattices : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) → ((∀ i j, (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧ ∀ j, j ≠ lastIdx n → ∃ s ∈ intV E v, (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (lastIdx n) j = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s) → ((∀ i j, ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧ ∀ j, j ≠ lastIdx n → ∃ s ∈ intV E v, ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (lastIdx n) j = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s) → g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) ∧ g ∈ stabGL (baseDualV hc n ST v) ∧ g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) := by
  first | exact @GlobalTheory.unitary_offRow_stab_three | exact GlobalTheory.unitary_offRow_stab_three | (intros; apply GlobalTheory.unitary_offRow_stab_three <;> assumption)
end

