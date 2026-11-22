import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0217
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0190
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0061
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqualGaussNormTeichmullerCancel
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GaussCancel

variable {l : ℕ} [Fact l.Prime]

theorem untilt_zero' : (0 : Formalism.Per.Fl l).untilt = 0 := by
  rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]

theorem isGauss_gC {ρ : ℝ} (h1 : (l : ℝ)⁻¹ ≤ ρ) (h2 : ρ < 1) : IsGauss l ρ (gC l ρ) := by
  have h : ∃ N, IsGauss l ρ N := by
    obtain ⟨N, hN⟩ := GlobalTheory.GaussExt.exists_gauss_acris l ρ h1 h2
    exact ⟨N, hN⟩
  have hfun : gC l ρ = Classical.choose h := by
    funext x
    unfold gC
    rw [dif_pos h]
  rw [hfun]
  exact Classical.choose_spec h

theorem gC_sub_le {ρ : ℝ} (hG : IsGauss l ρ (gC l ρ)) (x y : Formalism.Per.Acris l) :
    gC l ρ (x - y) ≤ max (gC l ρ x) (gC l ρ y) := by
  rw [sub_eq_add_neg]
  calc _ ≤ max (gC l ρ x) (gC l ρ (-y)) := hG.2.1 _ _
    _ = _ := by rw [hG.2.2.1]

theorem gC_pow {ρ : ℝ} (hG : IsGauss l ρ (gC l ρ)) (h1 : gC l ρ 1 = 1) (x : Formalism.Per.Acris l) (n : ℕ) :
    gC l ρ (x ^ n) = gC l ρ x ^ n := by
  induction n with
  | zero => simp [h1]
  | succ n ih => rw [pow_succ, hG.2.2.2.1, ih, pow_succ]

theorem gA_le_of_coeff_zero {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a : Formalism.Per.Ainf l)
    (ha : a.coeff 0 = 0) : gA l ρ a ≤ ρ := by
  unfold gA
  apply ciSup_le
  intro n
  rcases n with _ | n
  · simpa [ha, untilt_zero'] using h0
  · have hn : ‖(((a.coeff (n + 1)).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ (n + 1)) ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) (GlobalTheory.TiltAbs.norm_le_one _) (by positivity)
    calc _ ≤ 1 * ρ ^ (n + 1) := mul_le_mul_of_nonneg_right hn (pow_nonneg h0 _)
      _ ≤ ρ := by rw [one_mul]; exact pow_le_of_le_one h0 h1 (Nat.succ_ne_zero n)

theorem tc_mul (a b : Formalism.Per.Fl l) : tc l (a * b) = tc l a * tc l b := by
  unfold tc
  rw [Formalism.Per.tm, map_mul, map_mul]

end GlobalTheory.GaussCancel

namespace GlobalTheory.GaussCancel

variable {l : ℕ} [Fact l.Prime]

theorem equal_gauss_cancel : ∀ (l : ℕ) [Fact l.Prime] (w w' : Formalism.Per.Acris l), w' ≠ 0 →
    (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') →
    ∃ (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ (l : ℝ)⁻¹ < ρ₀ ∧ ρ₀ < 1 ∧
      gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' := by
  intro l _ w w' hw' heq
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  obtain ⟨⟨c, k, ρ₂, hc, hρ₂, hρ₂1, hm'⟩, -⟩ := GlobalTheory.T.gaussNormAcris_locally_monomial l w' hw' (l : ℝ)⁻¹ le_rfl hlinv
  have hm : ∀ ρ ∈ Set.Icc (l : ℝ)⁻¹ ρ₂, gC l ρ w = c * ρ ^ k := fun ρ hρ => by
    rw [heq ρ hρ.1 (lt_of_le_of_lt hρ.2 hρ₂1)]; exact hm' ρ hρ
  obtain ⟨y', j', hkj', hy', hL'⟩ := GlobalTheory.T.exists_teichmuller_lower_gaussNorm_of_locally_monomial l w' c (l : ℝ)⁻¹ ρ₂ k le_rfl hρ₂ hρ₂1 hc hm'
  obtain ⟨y, j, hkj, hy, hL⟩ := GlobalTheory.T.exists_teichmuller_lower_gaussNorm_of_locally_monomial l w c (l : ℝ)⁻¹ ρ₂ k le_rfl hρ₂ hρ₂1 hc hm

  have hy'0 : ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hy'
    linarith
  have hdvd : y' ∣ y := by
    apply GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd
    have hq : ((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
      rw [GlobalTheory.RingBasics.mem_OC, norm_div, hy, hy', div_self hc.ne']
    refine ⟨⟨_, hq⟩, Subtype.ext ?_⟩
    change ((y.untilt : Formalism.Per.OC l) : ℂ_[l]) = ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) *
      (((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]))
    field_simp
  obtain ⟨u, hu⟩ := hdvd
  have hu1 : ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((1 : Formalism.Per.Fl l).untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
    have h := hy
    rw [hu, map_mul] at h
    push_cast at h
    rw [norm_mul, hy'] at h
    rw [map_one]
    simp only [OneMemClass.coe_one, norm_one]
    have : c * ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c * 1 := by rw [h, mul_one]
    exact mul_left_cancel₀ hc.ne' this
  obtain ⟨ζ, o, ho, hζ, hζ0, hlt⟩ := GlobalTheory.T.exists_tilt_root_of_unity_approx_ratio l u 1 one_ne_zero hu1
  rw [mul_one, map_one] at hlt
  simp only [OneMemClass.coe_one, norm_one] at hlt

  set ρ₀ : ℝ := ((l : ℝ)⁻¹ + ρ₂) / 2 with hρ₀def
  have hρ₀a : (l : ℝ)⁻¹ < ρ₀ := by rw [hρ₀def]; linarith
  have hρ₀b : ρ₀ < ρ₂ := by rw [hρ₀def]; linarith
  have hρ₀1 : ρ₀ < 1 := lt_trans hρ₀b hρ₂1
  have hρ₀pos : 0 < ρ₀ := lt_trans hlpos hρ₀a
  have hIoo : ρ₀ ∈ Set.Ioo (l : ℝ)⁻¹ ρ₂ := ⟨hρ₀a, hρ₀b⟩
  have hIcc : ρ₀ ∈ Set.Icc (l : ℝ)⁻¹ ρ₂ := ⟨hρ₀a.le, hρ₀b.le⟩
  refine ⟨ζ, o, ρ₀, ho, hζ, hζ0, hρ₀a, hρ₀1, ?_⟩
  have hG := isGauss_gC (l := l) hρ₀a.le hρ₀1
  obtain ⟨hb1, hbl, -, hbt, -⟩ := GlobalTheory.T.gaussNormAcris_basic_values l ρ₀ hρ₀a.le hρ₀1
  have hlpow : ∀ n : ℕ, gC l ρ₀ ((l : Formalism.Per.Acris l) ^ n) = ρ₀ ^ n := fun n => by
    rw [gC_pow hG hb1, hbl]
  have hGw' : gC l ρ₀ w' = c * ρ₀ ^ k := hm' ρ₀ hIcc
  have hGw : gC l ρ₀ w = c * ρ₀ ^ k := hm ρ₀ hIcc
  set T : ℝ := ρ₀ ^ (max j j') * (c * ρ₀ ^ k) with hTdef
  set J : ℕ := max j j' with hJ
  set m : ℕ := (k + J).toNat with hmdef

  have hA : ∀ (x : Formalism.Per.Acris l) (z : Formalism.Per.Fl l) (i : ℕ), 0 ≤ k + i → i ≤ J → gC l ρ₀ x = c * ρ₀ ^ k →
      gC l ρ₀ ((l : Formalism.Per.Acris l) ^ i * x - (l : Formalism.Per.Acris l) ^ (k + i).toNat * tc l z) < ρ₀ ^ i * gC l ρ₀ x →
      gC l ρ₀ ((l : Formalism.Per.Acris l) ^ J * x - (l : Formalism.Per.Acris l) ^ m * tc l z) < T := by
    intro x z i hki hiJ hx hlt'
    have hmi : m = (J - i) + (k + i).toNat := by rw [hmdef]; omega
    have heqA : (l : Formalism.Per.Acris l) ^ J * x - (l : Formalism.Per.Acris l) ^ m * tc l z =
        (l : Formalism.Per.Acris l) ^ (J - i) * ((l : Formalism.Per.Acris l) ^ i * x -
          (l : Formalism.Per.Acris l) ^ (k + i).toNat * tc l z) := by
      have e : (l : Formalism.Per.Acris l) ^ J = (l : Formalism.Per.Acris l) ^ (J - i) * (l : Formalism.Per.Acris l) ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hiJ]
      rw [hmi, e, pow_add]
      ring
    rw [heqA, hG.2.2.2.1, hlpow, hTdef, ← hx]
    calc ρ₀ ^ (J - i) * gC l ρ₀ _ < ρ₀ ^ (J - i) * (ρ₀ ^ i * gC l ρ₀ x) :=
          mul_lt_mul_of_pos_left hlt' (pow_pos hρ₀pos _)
      _ = ρ₀ ^ J * gC l ρ₀ x := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hiJ]
  have hAw := hA w y j hkj (le_max_left _ _) hGw (hL ρ₀ hIoo)
  have hAw' := hA w' y' j' hkj' (le_max_right _ _) hGw' (hL' ρ₀ hIoo)

  have hζ1 : gC l ρ₀ (tc l ζ) ≤ 1 := (hG.1 _).2
  have hdiff : gC l ρ₀ (tc l u - tc l ζ) < 1 := by
    have hsplit : tc l u - tc l ζ = tc l (u - ζ) + algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)
        (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)) := by
      unfold tc
      rw [map_sub, map_sub]
      ring
    have hc0 : (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)).coeff 0 = 0 := by
      change WittVector.constantCoeff (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)) = 0
      rw [map_sub, map_sub]
      change (Formalism.Per.tm u).coeff 0 - (Formalism.Per.tm ζ).coeff 0 - (Formalism.Per.tm (u - ζ)).coeff 0 = 0
      simp [Formalism.Per.tm, WittVector.teichmuller_coeff_zero]
    rw [hsplit]
    refine lt_of_le_of_lt (hG.2.1 _ _) (max_lt ?_ ?_)
    · rw [hbt]; exact hlt
    · rw [hG.2.2.2.2]
      exact lt_of_le_of_lt (gA_le_of_coeff_zero hρ₀pos.le hρ₀1.le _ hc0) hρ₀1
  have hmz : ((m : ℕ) : ℤ) = k + J := by rw [hmdef]; exact Int.toNat_of_nonneg (by omega)
  have hD : gC l ρ₀ ((l : Formalism.Per.Acris l) ^ m * (tc l y - tc l ζ * tc l y')) < T := by
    have : tc l y - tc l ζ * tc l y' = tc l y' * (tc l u - tc l ζ) := by
      rw [hu, tc_mul]; ring
    rw [this, hG.2.2.2.1, hG.2.2.2.1, hlpow, hbt, hy']
    have hT : ρ₀ ^ m * c = T := by
      rw [hTdef, ← zpow_natCast, hmz, zpow_add₀ hρ₀pos.ne', zpow_natCast]
      ring
    rw [← hT, ← mul_assoc]
    exact mul_lt_of_lt_one_right (mul_pos (pow_pos hρ₀pos _) hc) hdiff
  have hB : gC l ρ₀ (tc l ζ * ((l : Formalism.Per.Acris l) ^ J * w' - (l : Formalism.Per.Acris l) ^ m * tc l y')) < T := by
    rw [hG.2.2.2.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (hG.1 _).1 hζ1) hAw'
  have hid : (l : Formalism.Per.Acris l) ^ J * (w - tc l ζ * w') =
      ((l : Formalism.Per.Acris l) ^ J * w - (l : Formalism.Per.Acris l) ^ m * tc l y) -
        tc l ζ * ((l : Formalism.Per.Acris l) ^ J * w' - (l : Formalism.Per.Acris l) ^ m * tc l y') +
        (l : Formalism.Per.Acris l) ^ m * (tc l y - tc l ζ * tc l y') := by ring
  have hbig : gC l ρ₀ ((l : Formalism.Per.Acris l) ^ J * (w - tc l ζ * w')) < T := by
    rw [hid]
    refine lt_of_le_of_lt (hG.2.1 _ _) (max_lt (lt_of_le_of_lt (gC_sub_le hG _ _) (max_lt hAw hB)) ?_)
    exact hD
  rw [hG.2.2.2.1, hlpow, hTdef, ← hGw'] at hbig
  exact lt_of_mul_lt_mul_left hbig (pow_nonneg hρ₀pos.le _)

end GlobalTheory.GaussCancel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsApproxRootEisensteinAwayPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem eval_derivative_scaleRoots_mul {R : Type*} [CommRing R] (P : Polynomial R) (s x : R) :
    (Polynomial.derivative (P.scaleRoots s)).eval (s * x) =
      s ^ (P.natDegree - 1) * (Polynomial.derivative P).eval x := by
  have h1 : (Polynomial.derivative (P.scaleRoots s)).natDegree < P.natDegree - 1 + 1 := by
    have := Polynomial.natDegree_derivative_le (P.scaleRoots s)
    rw [Polynomial.natDegree_scaleRoots] at this
    omega
  have h2 : (Polynomial.derivative P).natDegree < P.natDegree - 1 + 1 := by
    have := Polynomial.natDegree_derivative_le P
    omega
  rw [Polynomial.eval_eq_sum_range' h1, Polynomial.eval_eq_sum_range' h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ P.natDegree - 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative, Polynomial.coeff_scaleRoots]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi'
  have h3 : P.natDegree - (i + 1) = k := by omega
  rw [h3, hk]
  ring

theorem exists_approx_root_scaleRoots {R : Type*} [CommRing R] (P : Polynomial R) (hP : 0 < P.natDegree)
    (t x b : R) (c : ℕ) (hb : P.eval x ∣ b * (Polynomial.derivative P).eval x - t ^ c) (n : ℕ) :
    ∃ (m : ℕ) (q : R), P.eval x ∣ q - t ^ m * x ∧ P.eval x ^ (n + 1) ∣ (P.scaleRoots (t ^ m)).eval q := by
  induction n with
  | zero => exact ⟨0, x, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨m, q, ⟨z, hz⟩, ⟨w, hw⟩⟩ := ih
    obtain ⟨e, he⟩ : ∃ e, P.natDegree = e + 1 := ⟨P.natDegree - 1, by omega⟩
    obtain ⟨v, hv⟩ := hb
    set E := P.eval x with hE
    set s := t ^ m with hs
    set r := t ^ c * s ^ e with hr
    have hsr : t ^ (m + (c + m * e)) = s * r := by rw [hr, hs]; ring
    set h := -(b * (P.scaleRoots s).eval q) with hh
    refine ⟨m + (c + m * e), r * q + h, ?_, ?_⟩
    · rw [hsr]
      refine ⟨r * z - b * E ^ n * w, ?_⟩
      rw [hh, hw]
      linear_combination r * hz
    · rw [hsr]
      obtain ⟨k, hk⟩ := Polynomial.binomExpansion (P.scaleRoots (s * r)) (r * q) h
      have h0 : (P.scaleRoots (s * r)).eval (r * q) = r ^ (e + 1) * (P.scaleRoots s).eval q := by
        rw [Polynomial.scaleRoots_mul, Polynomial.scaleRoots_eval_mul, Polynomial.natDegree_scaleRoots, he]
      have h1 := eval_derivative_scaleRoots_mul P (s * r) x
      rw [he, Nat.add_sub_cancel] at h1
      obtain ⟨y, hy⟩ := Polynomial.sub_dvd_eval_sub (r * q) (s * r * x)
        (Polynomial.derivative (P.scaleRoots (s * r)))
      have h2 : (Polynomial.derivative (P.scaleRoots (s * r))).eval (r * q) =
          (s * r) ^ e * (Polynomial.derivative P).eval x + E * (r * z * y) := by
        rw [← h1]
        linear_combination hy + r * y * hz
      rw [hk, h0, h2, hh, hw]
      refine ⟨-((s * r) ^ e * v * w) - b * w * (r * z * y) + k * b ^ 2 * w ^ 2 * E ^ n, ?_⟩
      have h3 : r ^ (e + 1) = (s * r) ^ e * t ^ c := by
        rw [pow_succ, mul_pow]; nth_rewrite 2 [hr]; ring
      rw [h3]
      linear_combination (-((s * r) ^ e * E ^ (n + 1) * w)) * hv

theorem BK.exists_approx_root : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n : ℕ),
    ∃ (m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X ∧
      bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) := by
  intro l _ K bk n
  obtain ⟨c, a, b, hab⟩ := GlobalTheory.T.bezout_eisenstein_derivative_prime_pow l K bk
  have hcoe : ∀ p : Polynomial (Wq l bk.a),
      (p.map (PowerSeries.C : Wq l bk.a →+* bk.S)).eval (X : bk.S) = (p : bk.S) := fun p => by
    rw [Polynomial.eval_map, Polynomial.eval₂_C_X_eq_coe]
  have hdeg : (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S)).natDegree = bk.Ep.natDegree :=
    bk.monic.natDegree_map _
  have hb : (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S)).eval (X : bk.S) ∣
      (b : bk.S) * (Polynomial.derivative (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S))).eval X -
        (l : bk.S) ^ c := by
    rw [Polynomial.derivative_map, hcoe, hcoe]
    have h := congrArg (fun p : Polynomial (Wq l bk.a) => (p : bk.S)) hab
    beta_reduce at h
    rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C, map_pow, map_natCast] at h
    exact ⟨-(a : bk.S), by linear_combination h⟩
  obtain ⟨m, q, h1, h2⟩ := exists_approx_root_scaleRoots _ (hdeg ▸ bk.deg_pos) (l : bk.S) X b c hb n
  rw [hcoe] at h1 h2
  refine ⟨m, q, h1, (pow_dvd_pow _ n.le_succ).trans ?_⟩
  rw [← Polynomial.eval_map, Polynomial.map_scaleRoots _ _ _ (by rw [bk.monic.leadingCoeff, map_one]; exact one_ne_zero),
    map_pow, map_natCast]
  exact h2

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlockAction
section
noncomputable section

namespace GlobalTheory.SpanBlockAction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

section

variable {O : Type} [CommRing O] {n r t : ℕ}

def ActsAs (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (M : Matrix (Fin n) (Fin n) O) (P : Matrix (Fin r) (Fin r) O) (d : Fin t → O) : Prop :=
  ∀ u, e ((M.map (toFr O)).mulVec u) =
    ((P.map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (d c) * (e u).2 c)

theorem map_smul_toFr {k : ℕ} (c : O) (M : Matrix (Fin k) (Fin k) O) :
    (c • M).map (toFr O) = toFr O c • M.map (toFr O) := by
  ext i j
  simp [smul_eq_mul]

theorem map_sum_toFr {k m : ℕ} (M : Fin m → Matrix (Fin k) (Fin k) O) :
    (∑ i, M i).map (toFr O) = ∑ i, (M i).map (toFr O) := by
  ext i j
  simp [Matrix.sum_apply]

private theorem sum_mulVec_eq {K : Type} [CommRing K] {k m : ℕ} (A : Fin m → Matrix (Fin k) (Fin k) K)
    (v : Fin k → K) : (∑ i, A i).mulVec v = ∑ i, (A i).mulVec v := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

private theorem smul_mulVec_eq' {K : Type} [CommRing K] {k : ℕ} (a : K) (A : Matrix (Fin k) (Fin k) K)
    (v : Fin k → K) : (a • A).mulVec v = a • A.mulVec v := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem actsAs_sum
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    {m : ℕ} (c : Fin m → O) (M : Fin m → Matrix (Fin n) (Fin n) O) (P : Fin m → Matrix (Fin r) (Fin r) O)
    (d : Fin m → Fin t → O) (h : ∀ k, ActsAs e (M k) (P k) (d k)) :
    ActsAs e (∑ k, c k • M k) (∑ k, c k • P k) (fun j => ∑ k, c k * d k j) := by
  unfold ActsAs at h ⊢
  intro u
  rw [map_sum_toFr, map_sum_toFr]
  simp only [map_smul_toFr, sum_mulVec_eq, smul_mulVec_eq', map_sum, map_smul, h]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · funext j
    simp [Prod.snd_sum, Finset.sum_apply, Finset.sum_mul, mul_assoc]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Algebra.smul_def]

theorem ActsAs.unique
    {e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))}
    {M : Matrix (Fin n) (Fin n) O} {P P' : Matrix (Fin r) (Fin r) O} {d d' : Fin t → O}
    (h : ActsAs e M P d) (h' : ActsAs e M P' d') : P = P' := by
  have hv : ∀ v : Fin r → FractionRing O, (P.map (toFr O)).mulVec v = (P'.map (toFr O)).mulVec v := by
    intro v
    have h1 := h (e.symm (v, 0))
    have h2 := h' (e.symm (v, 0))
    rw [h1] at h2
    simpa using congrArg Prod.fst h2
  have hm : P.map (toFr O) = P'.map (toFr O) := by
    apply Matrix.toLin'.injective
    exact LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using hv v
  ext i j
  apply IsFractionRing.injective O (FractionRing O)
  have := congrFun (congrFun hm i) j
  simpa [toFr] using this

end

theorem actsAs_mat {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ}
    {σ : Γ →* GL (Fin n) O} {ρ : Γ →* GL (Fin r) O} {χ : ℕ → (Γ →* Oˣ)}
    {e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))}
    (h : IsDecomp (t := t) σ ρ χ e) (g : Γ) :
    ActsAs e (mat σ g) (mat ρ g) (fun c => ((χ ((c : ℕ) + 1) g : Oˣ) : O)) := by
  unfold ActsAs
  intro u
  simpa [overK, matRep, mapM, mat] using h g u

theorem exists_block_action {Γ X O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ}
    (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ))
    (π : X)
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (hspan : Submodule.span O (Set.range (mat ρ)) = ⊤) (hdec : IsDecomp (t := t) (rep π) ρ χ e) :
    ∃ (ψρ : (X → Matrix (Fin n) (Fin n) O) → Matrix (Fin r) (Fin r) O)
      (ψχ : Fin t → (X → Matrix (Fin n) (Fin n) O) → O),
      (∀ a, InRing T rep a → ∀ u, e (((a π).map (toFr O)).mulVec u) =
        (((ψρ a).map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (ψχ c a) * (e u).2 c)) ∧
      ∀ P : Matrix (Fin r) (Fin r) O, ∃ a, InRing T rep a ∧ ψρ a = P := by
  classical
  have hact : ∀ M ∈ Submodule.span O (Set.range (mat (rep π))),
      ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e M p.1 p.2 := by
    intro M hM
    obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.mp hM
    have hg : ∀ k, ∃ γ, mat (rep π) γ = (g k : Matrix (Fin n) (Fin n) O) := fun k => (g k).2
    choose γ hγ using hg
    refine ⟨(∑ k, c k • mat ρ (γ k), fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)), ?_⟩
    have := actsAs_sum e c (fun k => mat (rep π) (γ k)) (fun k => mat ρ (γ k))
      (fun k j => ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) (fun k => actsAs_mat hdec (γ k))
    simpa only [hγ] using this
  refine ⟨fun a => if h : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e (a π) p.1 p.2
      then h.choose.1 else 0,
    fun j a => if h : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e (a π) p.1 p.2
      then h.choose.2 j else 0, ?_, ?_⟩
  · intro a ha u
    have hex := hact (a π) (eval_mem_span ha π)
    simp only [dif_pos hex]
    exact hex.choose_spec u
  · intro P
    have hP : P ∈ Submodule.span O (Set.range (mat ρ)) := hspan ▸ Submodule.mem_top
    obtain ⟨m, c, g, hsum⟩ := Submodule.mem_span_set'.mp hP
    have hg : ∀ k, ∃ γ, mat ρ γ = (g k : Matrix (Fin r) (Fin r) O) := fun k => (g k).2
    choose γ hγ using hg
    refine ⟨∑ k, c k • (fun x => mat (rep x) (γ k)), ?_, ?_⟩
    · exact inRing_sum _ fun k _ => inRing_smul (c k) (inRing_mat (γ k))
    · have hev : (∑ k, c k • (fun x => mat (rep x) (γ k))) π = ∑ k, c k • mat (rep π) (γ k) := by
        simp [Finset.sum_apply]
      have hA : ActsAs e ((∑ k, c k • (fun x => mat (rep x) (γ k))) π) (∑ k, c k • mat ρ (γ k))
          (fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) := by
        rw [hev]
        exact actsAs_sum e c (fun k => mat (rep π) (γ k)) (fun k => mat ρ (γ k))
          (fun k j => ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) (fun k => actsAs_mat hdec (γ k))
      have hex : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O),
          ActsAs e ((∑ k, c k • (fun x => mat (rep x) (γ k))) π) p.1 p.2 :=
        ⟨(∑ k, c k • mat ρ (γ k), fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)), hA⟩
      simp only [dif_pos hex]
      rw [ActsAs.unique hex.choose_spec hA, ← hsum]
      simp only [hγ]

end GlobalTheory.SpanBlockAction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinEvalTeichmullerTiltStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisin_eval_teichmuller_tilt : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (π : OC l), ¬ IsUnit π → ∃ (fl : OCb l) (ev : (Wq l a)⟦X⟧ →+* Ainf l), Per.θ l (WittVector.teichmuller l fl) = π ∧ ev X = WittVector.teichmuller l fl ∧ (∀ w, ev (C w) = wA l a w) ∧ ∀ x, ev (frobS l a x) = WittVector.frobenius (ev x) := by
  first | exact @GlobalTheory.BKReal.exists_ev_of_root | exact GlobalTheory.BKReal.exists_ev_of_root | (intros; apply GlobalTheory.BKReal.exists_ev_of_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrobeniusPeriod
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ τ : Ainf l, bk.IsPer τ := by
  intro l hl K bk
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  set x : Ainf l := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) with hx
  have hxl : x ^ l = Per.tm e := by
    rw [hx, ← map_pow, frobeniusEquiv_symm_pow_p]
  have hφx : WittVector.frobenius x = Per.tm e := by
    rw [hx, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
      frobeniusEquiv_symm_pow_p]
  have hξ : GlobalTheory.MemLoc.xi e * (x - 1) = Per.tm e - 1 := by
    rw [GlobalTheory.MemLoc.xi, ← hx, geom_sum_mul, hxl]
  have hsp : Ideal.span {bk.ev bk.E} = Ideal.span {GlobalTheory.MemLoc.xi e} :=
    bk.span_ev.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  obtain ⟨ω, hω⟩ := Ideal.span_singleton_eq_span_singleton.1 hsp.symm
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_ainf_unit_frobenius_eq_mul l ω
  refine ⟨(x - 1) * η, ?_, e, ω * η, hE, ?_⟩
  · rw [map_mul, map_sub, map_one, hφx, hη, ← hω, ← hξ]
    ring
  · rw [map_mul, map_sub, map_one, hφx, hη, Units.val_mul]
    rw [mul_comm]
end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureLocalizationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deltaRingStructure_localization : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (M : Submonoid A), (∀ x ∈ M, D.φ x ∈ M) → ∃ D' : Delta l (Localization M), IsδMap D D' (algebraMap A (Localization M)) := by
  first | exact @GlobalTheory.BSP.delta_localization | exact GlobalTheory.BSP.delta_localization | (intros; apply GlobalTheory.BSP.delta_localization <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureQuotientSpanStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deltaRingStructure_quotient_span : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (s : Set A), (∀ x ∈ s, D.δ x ∈ Ideal.span s) → ∃ D' : Delta l (A ⧸ Ideal.span s), IsδMap D D' (Ideal.Quotient.mk (Ideal.span s)) := by
  first | exact @GlobalTheory.BSP.delta_quot_span | exact GlobalTheory.BSP.delta_quot_span | (intros; apply GlobalTheory.BSP.delta_quot_span <;> assumption)
end

