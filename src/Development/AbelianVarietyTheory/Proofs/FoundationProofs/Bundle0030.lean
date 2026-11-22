import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitSlashInvariantGamma1InterGamma0
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_transform {N l : ℕ} {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ lev N l, f ∣[k] γ = f) (A B C D : ℤ) (hdet : A * D - B * C = 1)
    (hA : (A : ZMod N) = 1) (hD : (D : ZMod N) = 1) (hCN : (C : ZMod N) = 0)
    (hCl : (C : ZMod l) = 0) (z : ℂ) (hz : 0 < z.im) :
    f (ofComplex ((A * z + B) / (C * z + D))) = (C * z + D) ^ k * f (ofComplex z) := by
  let g : SL(2, ℤ) := ⟨!![A, B; C, D], by simp [Matrix.det_fin_two_of]; linarith⟩
  have hg : g ∈ lev N l := by
    refine Subgroup.mem_inf.2 ⟨(Gamma1_mem N g).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩ <;> simpa [g]
  let w : ℍ := ⟨z, hz⟩
  have h1 := congrFun (hf g hg) w
  rw [SL_slash_apply] at h1
  have hden : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ) = C * z + D := by
    have e1 : g 1 0 = C := rfl
    have e2 : g 1 1 = D := rfl
    have := (show denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ) = ((g 1 0 : ℤ) : ℂ) * z + (g 1 1 : ℤ) by
      simp [denom, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, w])
    rw [this, e1, e2]
  have hsm : ((g • w : ℍ) : ℂ) = (A * z + B) / (C * z + D) := by
    rw [specialLinearGroup_apply]; simp [g, w]
  have hne : (C * z + D : ℂ) ≠ 0 := by rw [← hden]; exact denom_ne_zero _ _
  rw [hden] at h1
  have hw : ofComplex z = w := ofComplex_apply_of_im_pos hz
  rw [← hsm, ofComplex_apply, hw, ← h1, zpow_neg]
  field_simp

theorem lev_periodic {N l : ℕ} {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ lev N l, f ∣[k] γ = f) (z : ℂ) (hz : 0 < z.im) :
    f (ofComplex (z + 1)) = f (ofComplex z) := by
  have h := lev_transform hf 1 1 0 1 (by norm_num) (by simp) (by simp) (by simp) (by simp) z hz
  simpa using h

theorem sum_range_affine {q : ℕ} (hq : 0 < q) (F : ℤ → ℂ) (hF : Function.Periodic F q)
    (u v : ℤ) (hu : ∃ w : ZMod q, w * u = 1) :
    ∑ j ∈ Finset.range q, F (v + u * j) = ∑ j ∈ Finset.range q, F j := by
  haveI : NeZero q := ⟨hq.ne'⟩
  let G : ZMod q → ℂ := fun x => F (x.val : ℤ)
  have hFG : ∀ m : ℤ, F m = G m := by
    intro m
    simp only [G, ZMod.val_intCast]
    have := (hF.int_mul (m / q)) (m % q)
    rw [← this]; congr 1
    rw [Int.cast_id]; linear_combination (Int.mul_ediv_add_emod m q).symm
  have hsum : ∀ H : ZMod q → ℂ, ∑ j ∈ Finset.range q, H (j : ZMod q) = ∑ x, H x := by
    intro H
    symm
    refine Finset.sum_bij' (fun x _ => x.val) (fun j _ => (j : ZMod q)) ?_ ?_ ?_ ?_ ?_
    · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
    · intro j _; exact Finset.mem_univ _
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro j hj; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hj)
    · intro x _; rw [ZMod.natCast_zmod_val]
  obtain ⟨w, hw⟩ := hu
  have hbij : Function.Bijective (fun x : ZMod q => (v : ZMod q) + u * x) := by
    refine Finite.injective_iff_bijective.1 ?_
    intro x y hxy
    have : (u : ZMod q) * x = u * y := add_left_cancel hxy
    calc x = w * (u * x) := by rw [← mul_assoc, hw, one_mul]
      _ = y := by rw [this, ← mul_assoc, hw, one_mul]
  calc ∑ j ∈ Finset.range q, F (v + u * j)
      = ∑ j ∈ Finset.range q, G ((v : ZMod q) + u * (j : ZMod q)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hFG]; push_cast; rfl
    _ = ∑ x, G ((v : ZMod q) + u * x) := hsum (fun x => G ((v : ZMod q) + u * x))
    _ = ∑ x, G x := hbij.sum_comp G
    _ = ∑ j ∈ Finset.range q, G (j : ZMod q) := (hsum G).symm
    _ = ∑ j ∈ Finset.range q, F j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hFG]; push_cast; rfl

theorem uOp_slash_lev : ∀ (N l q : ℕ) (k : ℤ) (f : ℍ → ℂ), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    (∀ γ ∈ lev N l, f ∣[k] γ = f) → ∀ γ ∈ lev N l, uOp q f ∣[k] γ = uOp q f := by
  intro N l q k f _ _ hq hqNl hf γ hγ
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.1 hγ
  rw [Gamma1_mem] at h1
  rw [Gamma0_mem] at h0
  obtain ⟨ha, hd, hcN⟩ := h1
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hqc : (q : ℤ) ∣ γ 1 0 := by
    rcases hq.dvd_mul.1 hqNl with h | h
    · exact (Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 hcN)
    · exact (Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 h0)
  obtain ⟨t, ht⟩ := hqc
  funext τ
  rw [SL_slash_apply]
  have hden : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ) = (γ 1 0 : ℂ) * τ + γ 1 1 := by
    simp [denom, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hsm : ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1) := by
    rw [specialLinearGroup_apply]; simp
  have hcd : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := by rw [← hden]; exact denom_ne_zero _ _
  set a := γ 0 0 with ha_def
  set b := γ 0 1 with hb_def
  set c := γ 1 0 with hc_def
  set d := γ 1 1 with hd_def
  let F : ℤ → ℂ := fun m => f (ofComplex (((τ : ℂ) + m) / q))
  have hzim : ∀ m : ℤ, 0 < (((τ : ℂ) + m) / q).im := by
    intro m
    have : (((τ : ℂ) + m) / q).im = τ.im / q := by simp [Complex.div_natCast_im]
    rw [this]; exact div_pos τ.im_pos hqpos
  have hper : Function.Periodic F (q : ℤ) := by
    intro m
    have e : ((τ : ℂ) + ((m + q : ℤ) : ℂ)) / q = ((τ : ℂ) + m) / q + 1 := by
      push_cast; field_simp; ring
    show f (ofComplex (((τ : ℂ) + ((m + q : ℤ) : ℂ)) / q)) = f (ofComplex (((τ : ℂ) + m) / q))
    rw [e]; exact lev_periodic hf _ (hzim m)
  have hterm : ∀ j : ℕ, f (ofComplex (((a * τ + b) / (c * τ + d) + j) / q)) =
      (c * τ + d) ^ k * F (d * b + d * d * j) := by
    intro j
    set j' : ℤ := d * b + d * d * j with hj'
    set e : ℤ := t * (-(b * b) - 2 * j * b * d - j * j * d * d) with he_def
    have he : e * q = b + j * d - (a + j * c) * j' := by
      rw [he_def, hj']
      linear_combination (b + j * d) * hdet + (b * b + 2 * j * b * d + j * j * d * d) * ht
    have heC : (e : ℂ) * q = b + j * d - (a + j * c) * j' := by exact_mod_cast he
    have h := lev_transform hf (a + j * c) e (q * c) (d - c * j')
      (by linear_combination hdet - c * he)
      (by push_cast; simp [ha, hcN]) (by push_cast; simp [hd, hcN]) (by push_cast; simp [hcN])
      (by push_cast; simp [h0]) _ (hzim j')
    have hCD : ((q * c : ℤ) : ℂ) * (((τ : ℂ) + j') / q) + ((d - c * j' : ℤ) : ℂ) = c * τ + d := by
      push_cast; field_simp; ring
    rw [hCD] at h
    have harg : (((a + j * c : ℤ) : ℂ) * (((τ : ℂ) + j') / q) + (e : ℂ)) / (c * τ + d) =
        ((a * τ + b) / (c * τ + d) + j) / q := by
      push_cast
      field_simp
      linear_combination heC
    rw [harg] at h
    exact h
  have hunit : ∃ w : ZMod q, w * ((d * d : ℤ) : ZMod q) = 1 := by
    refine ⟨(a : ZMod q) * a, ?_⟩
    have h := congrArg (Int.cast : ℤ → ZMod q) hdet
    rw [ht] at h
    push_cast at h
    rw [ZMod.natCast_self] at h
    push_cast
    linear_combination ((a : ZMod q) * d + 1) * h
  unfold uOp
  rw [hsm, hden]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_range_affine hq.pos F hper _ _ hunit]
  have hF : ∑ j ∈ Finset.range q, F j =
      ∑ j ∈ Finset.range q, f (ofComplex (((τ : ℂ) + j) / q)) := by simp [F]
  rw [hF, zpow_neg]
  field_simp

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlRepresentativesRightMulPerm
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem ulFam_perm : ∀ (N l : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin l),
    ∀ i, ∃ γ' : Lev N l, ulFam l i * mat γ = mat γ' * ulFam l (π i) := by
  intro N l _ hl _ γ
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.mp γ.2
  rw [CongruenceSubgroup.Gamma1_mem] at hγ1
  rw [CongruenceSubgroup.Gamma0_mem] at hγ0
  obtain ⟨ha1, hd1, hcN⟩ := hγ1
  set a : ℤ := mat γ 0 0 with ha
  set b : ℤ := mat γ 0 1 with hb
  set c : ℤ := mat γ 1 0 with hc
  set d : ℤ := mat γ 1 1 with hd
  have hdet : a * d - b * c = 1 := by
    have h := (γ : SL(2, ℤ)).2
    rw [Matrix.det_fin_two] at h
    exact h
  have hmat : mat γ = !![a, b; c, d] := Matrix.eta_fin_two _
  have hcl : (c : ZMod l) = 0 := hγ0
  have hcN' : (c : ZMod N) = 0 := hcN
  have ha1' : (a : ZMod N) = 1 := ha1
  have hd1' : (d : ZMod N) = 1 := hd1
  have had : (d : ZMod l) * a = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at h
    rw [hcl] at h
    linear_combination h
  let f : Fin l → Fin l := fun i => ⟨(((b + (i : ℕ) * d) * d : ℤ) : ZMod l).val, ZMod.val_lt _⟩
  have hf : ∀ i, (((f i : ℕ) : ℤ) : ZMod l) = (((b + (i : ℕ) * d) * d : ℤ) : ZMod l) := by
    intro i
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val _
  have hinj : Function.Injective f := by
    intro i i' h
    have h2 := congrArg (fun x : Fin l => (((x : ℕ) : ℤ) : ZMod l)) h
    simp only [hf] at h2
    push_cast at h2
    have h3 : ((i : ℕ) : ZMod l) = ((i' : ℕ) : ZMod l) := by
      linear_combination (a * a) * h2 - ((i : ℕ) - (i' : ℕ) : ZMod l) * (d * a + 1) * had
    have h4 := congrArg ZMod.val h3
    rw [ZMod.val_natCast_of_lt i.2, ZMod.val_natCast_of_lt i'.2] at h4
    exact Fin.ext h4
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => ?_⟩
  simp only [Equiv.ofBijective_apply]
  set j : ℤ := ((f i : ℕ) : ℤ) with hj
  set x : ℤ := ((i : ℕ) : ℤ) with hx
  have hdvd : (l : ℤ) ∣ b + x * d - j * (a + x * c) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp
    have hj' := hf i
    rw [← hj] at hj'
    have hxc : (x : ZMod l) = ((i : ℕ) : ZMod l) := by rw [hx, Int.cast_natCast]
    push_cast
    rw [hj', hcl, hxc]
    push_cast
    linear_combination (-(b : ZMod l) - x * d) * had + (d : ZMod l) * (d * a - 1) * hxc
  obtain ⟨e, he⟩ := hdvd
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![a + x * c, e; l * c, d - j * c]
  have hMdet : M.det = 1 := by
    simp only [M, Matrix.det_fin_two_of]
    linear_combination hdet + c * he
  let g : SL(2, ℤ) := ⟨M, hMdet⟩
  have hg : g ∈ Lev N l := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      refine ⟨?_, ?_, ?_⟩
      · show ((a + x * c : ℤ) : ZMod N) = 1
        push_cast; rw [ha1', hcN']; ring
      · show ((d - j * c : ℤ) : ZMod N) = 1
        push_cast; rw [hd1', hcN']; ring
      · show (((l : ℤ) * c : ℤ) : ZMod N) = 0
        push_cast; rw [hcN']; ring
    · rw [CongruenceSubgroup.Gamma0_mem]
      show (((l : ℤ) * c : ℤ) : ZMod l) = 0
      push_cast; simp
  refine ⟨⟨g, hg⟩, ?_⟩
  show ulFam l i * mat γ = M * ulFam l (f i)
  rw [hmat]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [ulFam, M, Matrix.mul_apply, Fin.sum_univ_two, ← hj, ← hx] <;>
    first | ring1 | linear_combination he

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjMulExpEqConjQExpansionCoeff
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Qc

lemma exp_eq_conj_qParam (T : ℝ) (n : ℕ) (x y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T) =
      (starRingEnd ℂ) (1 / Function.Periodic.qParam T ((x : ℂ) + (y : ℂ) * Complex.I) ^ n) *
        (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, one_div, ← Complex.exp_neg, ← Complex.exp_conj,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, map_div₀, map_add, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  push_cast
  linear_combination (4 * (Real.pi : ℂ) * n * y / T) * Complex.I_sq

theorem conj_integral (h : ℍ → ℂ) (T : ℝ) (n : ℕ) (y : ℝ) (hT : 0 < T) (hy : 0 < y)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (hper : Function.Periodic (h ∘ ofComplex) T)
    (hbdd : IsBoundedAtImInfty h) :
    (∫ x in (0 : ℝ)..T, (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) *
        Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) =
      T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  have hc : ∀ f : ℝ → ℂ, (starRingEnd ℂ) (∫ u in (0 : ℝ)..T, f u) = ∫ u in (0 : ℝ)..T, (starRingEnd ℂ) (f u) := by
    intro f
    rw [intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le, integral_conj]
  rw [qExpansion_coeff_eq_intervalIntegral hT hper hhol hbdd n hy, map_mul, hc]
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [show (starRingEnd ℂ) (1 / (T : ℂ)) = 1 / (T : ℂ) by simp [Complex.conj_ofReal],
    ← mul_assoc, mul_one_div_cancel hT', one_mul, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun x _ => ?_
  have him : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  simp only [ofComplex_apply_of_im_pos him]
  rw [exp_eq_conj_qParam, map_mul, ← mul_assoc, mul_comm ((starRingEnd ℂ) (h _))]
  rfl

end GlobalTheory.HeckeFamilyMatrices.Qc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixConjMemGamma1InterGamma0Level
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isDia_conj_mem_lev : ∀ (N l : ℕ) (d : ℤ) (σ γ : SL(2, ℤ)), IsDia N l d σ → γ ∈ lev N l →
    σ * γ * σ⁻¹ ∈ lev N l := by
  intro N l d σ γ hσ hγ
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hσ.1
  have hσN : σ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      (dvd_trans (Int.natCast_dvd_natCast.2 (dvd_mul_right N l)) hc)
  have hσl : σ ∈ Gamma0 l := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      (dvd_trans (Int.natCast_dvd_natCast.2 (dvd_mul_left l N)) hc)
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.1 hγ
  refine Subgroup.mem_inf.2
    ⟨?_, (Gamma0 l).mul_mem ((Gamma0 l).mul_mem hσl hγ0) ((Gamma0 l).inv_mem hσl)⟩
  have hγN : γ ∈ Gamma0 N := ((Gamma1_mem N γ).1 hγ1).2.2
  set S : Gamma0 N := ⟨σ, hσN⟩
  set G : Gamma0 N := ⟨γ, hγN⟩
  have hG : G ∈ Gamma1' N := (Gamma1_to_Gamma0_mem G).2 ((Gamma1_mem N γ).1 hγ1)
  have hX : S * G * S⁻¹ ∈ Gamma1' N := by
    rw [Gamma1_mem'] at hG ⊢
    rw [map_mul, map_mul, hG, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have h := (Gamma1_to_Gamma0_mem _).1 hX
  exact (Gamma1_mem N _).2 h

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfForallMemDiscreteValuationSubring
section
open IsLocalRing

namespace GlobalTheory

theorem isIntegral_of_forall_mem_discreteValuationSubring : ∀ (S K : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K] [Algebra S K] [IsFractionRing S K] (t : K), (∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ s : S, algebraMap S K s ∈ V) → t ∈ V) → IsIntegral S t := by
  intro S K _ _ _ _ _ _ t ht
  by_contra hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn isIntegral_zero
  have : Algebra.EssFiniteType S K := .of_isLocalization K (nonZeroDivisors S)
  have hic : IsIntegrallyClosedIn (integralClosure S K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure S K) K)
  obtain ⟨W, hW, htW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure S K).toSubring) (x := t) hn
  have hinv : t⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr htW)
  obtain ⟨V, h1, h2, -, h3⟩ := exists_discreteValuationSubring_of_valuationSubring (R := S) W
    (fun r => hW ((integralClosure S K).algebraMap_mem r))
    Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv)
    ⟨_, rfl, inv_ne_zero ht0⟩
  exact (V.inv_mem_nonunits_iff.mp (h3 _ rfl)).resolve_left ht0 (ht V h1 h2)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsMemSubalgebraOfFiniteTypeAlgebraStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jets_mem_subalgebra_of_finiteType_algebra : ∀ (k A R : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [Algebra k R] (N : ℕ) (Δ : ℕ → A →ₗ[k] R), Δ 0 1 = 1 → (∀ l, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ p u * Δ (l - p) w)) →
 ∃ T : Finset R, ∀ S : Subalgebra k R, (∀ t ∈ T, t ∈ S) → ∀ l < N, ∀ u, Δ l u ∈ S := by
  first | exact @GlobalTheory.jets_mem_subalgebra_of_finiteType | exact GlobalTheory.jets_mem_subalgebra_of_finiteType | (intros; apply GlobalTheory.jets_mem_subalgebra_of_finiteType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainCupProductCongruence
section
open GlobalTheory.K5

namespace GlobalTheory.CuspCup

theorem cup_identity {R : Type*} [CommRing R]
    (N P A B A' B' i m ag bg bh bgh qg qh qgh zg zh zgh x gx gy ghy e₁ e₂ tb tq tz : R)
    (h₁ : P * ag - A * qg - B * zg - (gx - x) = N * e₁)
    (h₂ : P * bh - A' * qh - B' * zh - (ghy - gy) = N * e₂)
    (hb : bgh = bg + bh - N * tb) (hq : qgh = qg + qh - N * tq) (hz : zgh = zg + zh - N * tz)
    (hi : 2 * i = 1 + N * m) :
    (P * ag) * (P * bh) + (A * B' - B * A') * (zg * qh) -
      ((gx * (P * bh) - (A * qh + B * zh) * ghy - i * (A * A') * qh ^ 2 - A * B' * (qh * zh)
          - i * (B * B') * zh ^ 2)
        - (x * (P * bgh) - (A * qgh + B * zgh) * ghy - i * (A * A') * qgh ^ 2
          - A * B' * (qgh * zgh) - i * (B * B') * zgh ^ 2)
        + (x * (P * bg) - (A * qg + B * zg) * gy - i * (A * A') * qg ^ 2 - A * B' * (qg * zg)
          - i * (B * B') * zg ^ 2)) =
    N * (e₁ * (P * bh) + (A * qg + B * zg) * e₂ - P * x * tb + (A * tq + B * tz) * ghy
      - m * (A * A') * (qg * qh) - m * (B * B') * (zg * zh)
      + i * (A * A') * (2 * tq * (qg + qh) - N * tq ^ 2)
      + A * B' * (tq * (zg + zh) + tz * (qg + qh) - N * (tq * tz))
      + i * (B * B') * (2 * tz * (zg + zh) - N * tz ^ 2)) := by
  subst hb hq hz
  linear_combination (P * bh) * h₁ + (A * qg + B * zg) * h₂
    - (A * A' * (qg * qh) + B * B' * (zg * zh)) * hi

theorem exists_val_add {R : Type*} [CommRing R] (p n : ℕ) (hp : p ≠ 0) (u v : ZMod (p ^ n)) :
    ∃ t : ℕ, (((u + v).val : ℕ) : R) = (u.val : R) + (v.val : R) - (p : R) ^ n * (t : R) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp⟩
  refine ⟨(u.val + v.val) / p ^ n, ?_⟩
  have h := Nat.mod_add_div (u.val + v.val) (p ^ n)
  rw [← ZMod.val_add] at h
  have h' := congrArg (Nat.cast : ℕ → R) h
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_add] at h'
  linear_combination h'

theorem exists_half (p n : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ∃ i m : ℤ, 2 * i = 1 + (p : ℤ) ^ n * m := by
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two h2).pow (n := n)
  refine ⟨k + 1, 1, ?_⟩
  have := congrArg (Nat.cast : ℕ → ℤ) hk
  push_cast at this
  rw [this]; ring

theorem cup_congruence : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (H : Subgroup (Gal p Ω)) (n c : ℕ)
  (a b lz lq : Gal p Ω → ZMod (p ^ n)) (A B A' B' : Ω),
  (∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g + a h) → (∀ g ∈ H, ∀ h ∈ H, b (g * h) = b g + b h) →
  (∀ g ∈ H, ∀ h ∈ H, lz (g * h) = lz g + lz h) → (∀ g ∈ H, ∀ h ∈ H, lq (g * h) = lq g + lq h) →
  (∀ g ∈ H, g A = A ∧ g B = B ∧ g A' = A' ∧ g B' = B') →
  IsInt p ((p : Ω) ^ c * A) → IsInt p ((p : Ω) ^ c * B) → IsInt p ((p : Ω) ^ c * A') → IsInt p ((p : Ω) ^ c * B') →
  (∀ g, ∃ S : Finset Ω, ∀ h : Gal p Ω, (∀ x ∈ S, h x = g x) → a h = a g ∧ b h = b g ∧ lz h = lz g ∧ lq h = lq g) →
  Cob1 n H (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * A * ((lq g).val : Ω) - (p : Ω) ^ c * B * ((lz g).val : Ω)) →
  Cob1 n H (fun g => (p : Ω) ^ c * ((b g).val : Ω) - (p : Ω) ^ c * A' * ((lq g).val : Ω) - (p : Ω) ^ c * B' * ((lz g).val : Ω)) →
  Cob2 n H (fun g h => (p : Ω) ^ (4 * c) * (((a g).val : Ω) * ((b h).val : Ω)) +
      (p : Ω) ^ (4 * c) * (A * B' - B * A') * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  intro p hp h2 Ω _ _ H n c a b lz lq A B A' B' _ hb hz hq hfix iA iB iA' iB' hlc ⟨x, ix, hx⟩
    ⟨y, iy, hy⟩
  classical
  obtain ⟨i, m, him⟩ := exists_half p n hp.out h2
  have him' : 2 * (i : Ω) = 1 + (p : Ω) ^ n * (m : Ω) := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) him
  let R := integralClosure (O0 p) Ω
  have key : ∀ v : Ω, IsInt p v ↔ v ∈ R := fun v => Iff.rfl
  have hmap : ∀ (g : Gal p Ω) (v : Ω), v ∈ R → g v ∈ R := fun g v hv =>
    IsIntegral.map g.toAlgHom hv
  rw [key] at iA iB iA' iB' ix iy
  have iP : (p : Ω) ^ c ∈ R := pow_mem (natCast_mem R p) c
  have iN : (p : Ω) ^ n ∈ R := pow_mem (natCast_mem R p) n
  have i2 : (2 : Ω) ∈ R := ofNat_mem R 2
  refine ⟨fun k => ((p : Ω) ^ c) ^ 2 * (x * ((p : Ω) ^ c * ((b k).val : Ω))
    - ((p : Ω) ^ c * A * ((lq k).val : Ω) + (p : Ω) ^ c * B * ((lz k).val : Ω)) * k y
    - (i : Ω) * (((p : Ω) ^ c * A) * ((p : Ω) ^ c * A')) * ((lq k).val : Ω) ^ 2
    - ((p : Ω) ^ c * A) * ((p : Ω) ^ c * B') * (((lq k).val : Ω) * ((lz k).val : Ω))
    - (i : Ω) * (((p : Ω) ^ c * B) * ((p : Ω) ^ c * B')) * ((lz k).val : Ω) ^ 2), ⟨?_, ?_⟩, ?_⟩
  · intro k
    rw [key]
    have h1 := hmap k y iy
    generalize (p : Ω) ^ c * A = A₁ at *
    generalize (p : Ω) ^ c * B = B₁ at *
    generalize (p : Ω) ^ c * A' = A₂ at *
    generalize (p : Ω) ^ c * B' = B₂ at *
    generalize (p : Ω) ^ c = P at *
    repeat' first
      | assumption
      | exact natCast_mem R _
      | exact intCast_mem R _
      | apply mul_mem
      | apply sub_mem
      | apply add_mem
      | apply pow_mem
  · intro k
    obtain ⟨S, hS⟩ := hlc k
    refine ⟨insert y S, fun h hh => ⟨0, (key _).2 (zero_mem R), ?_⟩⟩
    obtain ⟨-, e1, e2, e3⟩ := hS h (fun x hx => hh x (Finset.mem_insert_of_mem hx))
    have e4 := hh y (Finset.mem_insert_self _ _)
    simp only [e1, e2, e3, e4, sub_self, mul_zero]
  · intro g hg h hh
    obtain ⟨e₁, ie₁, h₁⟩ := hx g hg
    obtain ⟨e₂, ie₂, h₂⟩ := hy h hh
    obtain ⟨fA, fB, fA', fB'⟩ := hfix g hg
    have h₂' := congrArg g h₂
    simp only [map_sub, map_mul, map_pow, map_natCast, fA', fB'] at h₂'
    obtain ⟨tb, htb⟩ := exists_val_add (R := Ω) p n hp.out.ne_zero (b g) (b h)
    obtain ⟨tq, htq⟩ := exists_val_add (R := Ω) p n hp.out.ne_zero (lq g) (lq h)
    obtain ⟨tz, htz⟩ := exists_val_add (R := Ω) p n hp.out.ne_zero (lz g) (lz h)
    rw [← hb g hg h hh] at htb
    rw [← hq g hg h hh] at htq
    rw [← hz g hg h hh] at htz
    have main := cup_identity _ _ _ _ _ _ _ _ _ ((b g).val : Ω) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      h₁ h₂' htb htq htz him'
    refine ⟨_, ?_, Eq.trans ?_
      ((congrArg (fun t => ((p : Ω) ^ c) ^ 2 * t) main).trans (mul_left_comm _ _ _))⟩
    swap
    · simp only [map_sub, map_add, map_mul, map_pow, map_natCast, map_intCast, fA, fB, fA', fB',
        AlgEquiv.mul_apply]
      ring
    · rw [key] at ie₁ ie₂ ⊢
      have h1 := hmap g _ (hmap h y iy)
      have h3 := hmap g _ ie₂
      clear main h₁ h₂ h₂' hx hy htb htq htz him'
      generalize (p : Ω) ^ c * A = A₁ at *
      generalize (p : Ω) ^ c * B = B₁ at *
      generalize (p : Ω) ^ c * A' = A₂ at *
      generalize (p : Ω) ^ c * B' = B₂ at *
      generalize (p : Ω) ^ c = P at *
      generalize (p : Ω) ^ n = N at *
      repeat' first
        | assumption
        | exact natCast_mem R _
        | exact intCast_mem R _
        | apply mul_mem
        | apply sub_mem
        | apply add_mem
        | apply pow_mem

end GlobalTheory.CuspCup
end

