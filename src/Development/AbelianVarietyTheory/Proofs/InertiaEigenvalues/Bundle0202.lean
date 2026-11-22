import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0196
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0197
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0183

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommutantValuationDecomposition
section
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.ValDecomp

section Abstract
variable {R : Type*} [CommRing R]

end Abstract
end GlobalTheory.ValDecomp

namespace GlobalTheory.ValDecomp
section Abstract2
variable {R : Type*} [CommRing R]

end Abstract2
end GlobalTheory.ValDecomp

namespace GlobalTheory.ValDecomp
section Mat
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

end Mat
end GlobalTheory.ValDecomp

namespace GlobalTheory.ValDecomp

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
private theorem exists_pow_smul_entries_norm_le_one {ϖ : E} (h1 : ‖ϖ‖ < 1)
    (c : Matrix (Fin n) (Fin n) E) : ∃ k : ℕ, ∀ i j, ‖(ϖ ^ k • c) i j‖ ≤ 1 := by
  set B : ℝ := 1 + ∑ i, ∑ j, ‖c i j‖
  have hB : 0 < B := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hB) h1
  refine ⟨k, fun i j => ?_⟩
  have hij : ‖c i j‖ ≤ B := by
    have h := (Finset.single_le_sum (f := fun j => ‖c i j‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖c i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    linarith
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  calc ‖ϖ‖ ^ k * ‖c i j‖ ≤ B⁻¹ * B := mul_le_mul hk.le hij (norm_nonneg _) (inv_pos.2 hB).le
    _ = 1 := inv_mul_cancel₀ hB.ne'

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
private theorem inv_mul_comm_of_mul_comm' {x N : Matrix (Fin n) (Fin n) E} (hx : IsUnit x.det)
    (h : x * N = N * x) : x⁻¹ * N = N * x⁻¹ := by
  calc x⁻¹ * N = x⁻¹ * (N * x) * x⁻¹ := by
        rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv x hx, mul_one]
    _ = x⁻¹ * (x * N) * x⁻¹ := by rw [h]
    _ = N * x⁻¹ := by rw [← mul_assoc, Matrix.nonsing_inv_mul x hx, one_mul]

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
private theorem norm_det_le_one_of_entries_norm_le_one' {x : Matrix (Fin n) (Fin n) E}
    (hx : ∀ i j, ‖x i j‖ ≤ 1) : ‖x.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp only [h, one_smul, Units.neg_smul, norm_neg, norm_prod] <;>
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hx _ _

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
private theorem inv_entries_norm_le_one_of_norm_det_one {x : Matrix (Fin n) (Fin n) E}
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (hd : ‖x.det‖ = 1) : ∀ i j, ‖x⁻¹ i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, norm_mul, Ring.inverse_eq_inv', norm_inv,
    hd, inv_one, one_mul, Matrix.adjugate_apply]
  apply norm_det_le_one_of_entries_norm_le_one'
  intro k l
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs <;> simp
  · exact hx _ _

theorem _root_.GlobalTheory.ValDecomp.valuation_decomp : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → (∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ e a : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a * N = N * a ∧ (∀ i j, ‖e i j‖ ≤ 1 ∧ ‖a i j‖ ≤ 1) ∧ e * e = e ∧ ‖(y * e + (1 - e)).det‖ = 1 ∧ y * (1 - e) = ϖ • a) → ∀ c : Matrix (Fin n) (Fin n) E, IsUnit c → c * N = N * c → ∃ e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E, (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ ‖u.det‖ = 1 ∧ e₁ * e₁ = e₁ ∧ e₂ * e₂ = e₂ ∧ e₃ * e₃ = e₃ ∧ e₁ * e₂ = 0 ∧ e₁ * e₃ = 0 ∧ e₂ * e₃ = 0 ∧ e₁ + e₂ + e₃ = 1 ∧ c * e₁ = u * e₁ ∧ c * e₂ = ϖ • (a₂ * e₂) ∧ c⁻¹ * e₃ = ϖ • (a₃ * e₃) := by
  intro E _ _ n N ϖ h0 h1 hcomm hdec c hc hcN
  have hϖ : ϖ ≠ 0 := norm_pos_iff.1 h0
  have hpow : ∀ k : ℕ, ‖ϖ ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h1.le
  have hone : ∀ i j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 :=
    fun i j => _root_.GlobalTheory.UnitDiscAlg.integ_one i j
  let S := Subalgebra.centralizer E ({N} : Set (Matrix (Fin n) (Fin n) E))
  have memS : ∀ {x : Matrix (Fin n) (Fin n) E}, x * N = N * x → x ∈ S := fun hx => by
    rw [Subalgebra.mem_centralizer_iff]; rintro g rfl; exact hx.symm
  have ofS : ∀ {x : Matrix (Fin n) (Fin n) E}, x ∈ S → x * N = N * x := fun hx =>
    ((Subalgebra.mem_centralizer_iff E).1 hx N rfl).symm
  letI : CommRing S := { (inferInstance : Ring S) with
    mul_comm := fun x y => Subtype.ext (hcomm x y (ofS x.2) (ofS y.2)) }
  have toM : ∀ {X Y : S}, X = Y → (X : Matrix (Fin n) (Fin n) E) = Y := fun h => congrArg _ h
  have hscal : ∀ r : E, (r • (1 : Matrix (Fin n) (Fin n) E)) * N = N * (r • 1) := fun r => by
    rw [smul_one_mul, Matrix.mul_smul, mul_one]
  let Pp : S := ⟨ϖ • 1, memS (hscal ϖ)⟩
  obtain ⟨k, hk⟩ := exists_pow_smul_entries_norm_le_one h1 c
  induction k generalizing c with
  | zero =>
    have hc0 : ∀ i j, ‖c i j‖ ≤ 1 := by simpa using hk
    obtain ⟨e, a, heN, haN, hea, hee, hdet, hca⟩ := hdec c hcN hc0
    have he : ∀ i j, ‖e i j‖ ≤ 1 := fun i j => (hea i j).1
    let C : S := ⟨c, memS hcN⟩
    let Ee : S := ⟨e, memS heN⟩
    let A : S := ⟨a, memS haN⟩
    have re : Ee * Ee = Ee := Subtype.ext hee
    have rca : C * (1 - Ee) = Pp * A :=
      Subtype.ext (show c * (1 - e) = (ϖ • 1) * a by rw [smul_one_mul]; exact hca)
    refine ⟨e, 1 - e, 0, c * e + (1 - e), a, 0, ⟨heN, ofS (1 - Ee).2, by simp,
      ofS (C * Ee + (1 - Ee)).2, haN, by simp⟩, fun i j => ⟨he i j,
      _root_.GlobalTheory.UnitDiscAlg.integ_sub hone he i j, by simp,
      _root_.GlobalTheory.UnitDiscAlg.integ_add (_root_.GlobalTheory.UnitDiscAlg.integ_mul hc0 he)
        (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he) i j, (hea i j).2, by simp⟩, hdet, hee,
      toM (by linear_combination re : (1 - Ee) * (1 - Ee) = 1 - Ee), by simp,
      toM (by linear_combination (-1 : S) * re : Ee * (1 - Ee) = 0), by simp, by simp,
      by abel, toM (by linear_combination (1 - C) * re : C * Ee = (C * Ee + (1 - Ee)) * Ee),
      ?_, by simp⟩
    have h := toM (by linear_combination (1 - Ee) * rca - C * re :
      C * (1 - Ee) = Pp * (A * (1 - Ee)))
    rw [← smul_one_mul]; exact h
  | succ k ih =>
    have hyN : (ϖ ^ (k + 1) • c) * N = N * (ϖ ^ (k + 1) • c) :=
      (show Commute c N from hcN).smul_left _
    obtain ⟨e, a, heN, haN, hea, hee, hdet, hya⟩ := hdec _ hyN hk
    have he : ∀ i j, ‖e i j‖ ≤ 1 := fun i j => (hea i j).1
    have ha : ∀ i j, ‖a i j‖ ≤ 1 := fun i j => (hea i j).2
    have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    have hciN : c⁻¹ * N = N * c⁻¹ := inv_mul_comm_of_mul_comm' hcd hcN
    let C : S := ⟨c, memS hcN⟩
    let Ci : S := ⟨c⁻¹, memS hciN⟩
    let Ee : S := ⟨e, memS heN⟩
    let Pk : S := ⟨ϖ ^ k • 1, memS (hscal _)⟩
    have re : Ee * Ee = Ee := Subtype.ext hee
    have r1 : C * Ci = 1 := Subtype.ext (Matrix.mul_nonsing_inv c hcd)
    have hsplit : ϖ ^ (k + 1) • c = (ϖ • 1) * (ϖ ^ k • 1) * c := by
      rw [smul_one_mul, smul_mul_assoc, smul_one_mul, smul_smul, ← pow_succ']
    have hzN : (ϖ ^ (k + 1) • c * e + (1 - e)) * N = N * (ϖ ^ (k + 1) • c * e + (1 - e)) := by
      rw [hsplit]; exact ofS (Pp * Pk * C * Ee + (1 - Ee)).2
    have hzint : ∀ i j, ‖(ϖ ^ (k + 1) • c * e + (1 - e)) i j‖ ≤ 1 :=
      _root_.GlobalTheory.UnitDiscAlg.integ_add (_root_.GlobalTheory.UnitDiscAlg.integ_mul hk he)
        (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he)
    have hzd : IsUnit (ϖ ^ (k + 1) • c * e + (1 - e)).det :=
      isUnit_iff_ne_zero.2 fun h => by rw [h, norm_zero] at hdet; exact zero_ne_one hdet
    have hw := inv_entries_norm_le_one_of_norm_det_one hzint hdet
    have hwN := inv_mul_comm_of_mul_comm' hzd hzN
    let W : S := ⟨_, memS hwN⟩
    have rwz : (Pp * Pk * C * Ee + (1 - Ee)) * W = 1 := Subtype.ext (show
      ((ϖ • 1) * (ϖ ^ k • 1) * c * e + (1 - e)) * (ϖ ^ (k + 1) • c * e + (1 - e))⁻¹ = 1 by
        rw [← hsplit]; exact Matrix.mul_nonsing_inv _ hzd)
    have hA : Ci * Ee = Pp * Pk * (Ee * W) := by
      linear_combination (-(Ci * Ee)) * rwz + (Pp * Pk * W - Ci * W) * re
        + (Pp * Pk * Ee ^ 2 * W) * r1
    have ha' : ϖ ^ k • (c * (1 - e)) = a := smul_right_injective _ hϖ
      (show ϖ • (ϖ ^ k • (c * (1 - e))) = ϖ • a by
        rw [← hya, smul_smul, ← pow_succ', smul_mul_assoc])
    have hc'int : ∀ i j, ‖(ϖ ^ k • (c * (1 - e) + e)) i j‖ ≤ 1 := by
      rw [smul_add, ha']
      exact _root_.GlobalTheory.UnitDiscAlg.integ_add ha (_root_.GlobalTheory.UnitDiscAlg.integ_smul (hpow k) he)
    have rcd : (C * (1 - Ee) + Ee) * (Ci * (1 - Ee) + Ee) = 1 := by
      linear_combination (1 - Ee) * r1 + (C * Ci - C - Ci + 1) * re
    have hmat : (c * (1 - e) + e) * (c⁻¹ * (1 - e) + e) = 1 := toM rcd
    have hunit : IsUnit (c * (1 - e) + e) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hmat)
    have hinv : (c * (1 - e) + e)⁻¹ = c⁻¹ * (1 - e) + e := Matrix.inv_eq_right_inv hmat
    obtain ⟨f₁, f₂, f₃, u, b₂, b₃, ⟨h1N, h2N, h3N, huN, hb2N, hb3N⟩, hint, hu, h11, h22, h33,
      h12, h13, h23, hsum, hc1, hc2, hc3⟩ := ih _ hunit (ofS (C * (1 - Ee) + Ee).2) hc'int
    rw [hinv] at hc3
    have hF1 : ∀ i j, ‖f₁ i j‖ ≤ 1 := fun i j => (hint i j).1
    have hF2 : ∀ i j, ‖f₂ i j‖ ≤ 1 := fun i j => (hint i j).2.1
    have hF3 : ∀ i j, ‖f₃ i j‖ ≤ 1 := fun i j => (hint i j).2.2.1
    have hB3 : ∀ i j, ‖b₃ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.2.2
    let F1 : S := ⟨f₁, memS h1N⟩
    let F2 : S := ⟨f₂, memS h2N⟩
    let F3 : S := ⟨f₃, memS h3N⟩
    let U : S := ⟨u, memS huN⟩
    let B2 : S := ⟨b₂, memS hb2N⟩
    let B3 : S := ⟨b₃, memS hb3N⟩
    have s11 : F1 * F1 = F1 := Subtype.ext h11
    have s22 : F2 * F2 = F2 := Subtype.ext h22
    have s33 : F3 * F3 = F3 := Subtype.ext h33
    have s12 : F1 * F2 = 0 := Subtype.ext h12
    have s13 : F1 * F3 = 0 := Subtype.ext h13
    have s23 : F2 * F3 = 0 := Subtype.ext h23
    have ssum : F1 + F2 + F3 = 1 := Subtype.ext hsum
    have sc1 : (C * (1 - Ee) + Ee) * F1 = U * F1 := Subtype.ext hc1
    have sc2 : (C * (1 - Ee) + Ee) * F2 = Pp * (B2 * F2) := Subtype.ext
      (show (c * (1 - e) + e) * f₂ = (ϖ • 1) * (b₂ * f₂) by rw [smul_one_mul]; exact hc2)
    have sc3 : (Ci * (1 - Ee) + Ee) * F3 = Pp * (B3 * F3) := Subtype.ext
      (show (c⁻¹ * (1 - e) + e) * f₃ = (ϖ • 1) * (b₃ * f₃) by rw [smul_one_mul]; exact hc3)
    refine ⟨f₁ * (1 - e), f₂ * (1 - e), f₃ * (1 - e) + e, u, b₂,
      b₃ * (1 - e) + (ϖ ^ k • 1) * (e * (ϖ ^ (k + 1) • c * e + (1 - e))⁻¹),
      ⟨ofS (F1 * (1 - Ee)).2, ofS (F2 * (1 - Ee)).2, ofS (F3 * (1 - Ee) + Ee).2, huN, hb2N,
        ofS (B3 * (1 - Ee) + Pk * (Ee * W)).2⟩,
      fun i j => ⟨_root_.GlobalTheory.UnitDiscAlg.integ_mul hF1 (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he) i j,
        _root_.GlobalTheory.UnitDiscAlg.integ_mul hF2 (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he) i j,
        _root_.GlobalTheory.UnitDiscAlg.integ_add
          (_root_.GlobalTheory.UnitDiscAlg.integ_mul hF3 (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he)) he i j,
        (hint i j).2.2.2.1, (hint i j).2.2.2.2.1,
        _root_.GlobalTheory.UnitDiscAlg.integ_add
          (_root_.GlobalTheory.UnitDiscAlg.integ_mul hB3 (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he))
          (_root_.GlobalTheory.UnitDiscAlg.integ_mul (_root_.GlobalTheory.UnitDiscAlg.integ_smul (hpow k) hone)
            (_root_.GlobalTheory.UnitDiscAlg.integ_mul he hw)) i j⟩, hu,
      toM (by linear_combination (1 - Ee) ^ 2 * s11 + F1 * re :
        F1 * (1 - Ee) * (F1 * (1 - Ee)) = F1 * (1 - Ee)),
      toM (by linear_combination (1 - Ee) ^ 2 * s22 + F2 * re :
        F2 * (1 - Ee) * (F2 * (1 - Ee)) = F2 * (1 - Ee)),
      toM (by linear_combination (1 - Ee) ^ 2 * s33 + (1 - F3) * re :
        (F3 * (1 - Ee) + Ee) * (F3 * (1 - Ee) + Ee) = F3 * (1 - Ee) + Ee),
      toM (by linear_combination (1 - Ee) ^ 2 * s12 : F1 * (1 - Ee) * (F2 * (1 - Ee)) = 0),
      toM (by linear_combination (1 - Ee) ^ 2 * s13 - F1 * re :
        F1 * (1 - Ee) * (F3 * (1 - Ee) + Ee) = 0),
      toM (by linear_combination (1 - Ee) ^ 2 * s23 - F2 * re :
        F2 * (1 - Ee) * (F3 * (1 - Ee) + Ee) = 0),
      toM (by linear_combination (1 - Ee) * ssum :
        F1 * (1 - Ee) + F2 * (1 - Ee) + (F3 * (1 - Ee) + Ee) = 1),
      toM (by linear_combination (1 - Ee) * sc1 - (C * F1 - F1) * re :
        C * (F1 * (1 - Ee)) = U * (F1 * (1 - Ee))), ?_, ?_⟩
    · have h := toM (by linear_combination (1 - Ee) * sc2 - (C * F2 - F2) * re :
        C * (F2 * (1 - Ee)) = Pp * (B2 * (F2 * (1 - Ee))))
      rw [← smul_one_mul]; exact h
    · have h := toM (by
        linear_combination (1 - Ee) * sc3 + hA
          + (F3 - Ci * F3 - Pp * B3 * F3 + Pp * B3 + Pp * Pk * W * F3 - Pp * Pk * W) * re :
        Ci * (F3 * (1 - Ee) + Ee) = Pp * ((B3 * (1 - Ee) + Pk * (Ee * W)) * (F3 * (1 - Ee) + Ee)))
      rw [← smul_one_mul]; exact h

end GlobalTheory.ValDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPrimePowLatticeOfXPowSmulMemStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_prime_pow_lattice_of_X_pow_smul_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (n b : ℕ) (w z : Vec K a ι), w ∈ P.L → z ∈ P.L → ((X : K⟦X⟧) ^ e) ^ n • w = (l : K) ^ b • z → ∃ z' ∈ P.L, w = (l : K) ^ b • z' := by
  first | exact @GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul | exact GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul | (intros; apply GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbc
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem model_obj_and_abc : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → F.Obj A ∧ ABC (F.D A) Dt.w Dt.wst N := by
  intro k G _ _ l n _ _ _ R F r Dt M A N h
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := h
  have oB : F.Obj B := M.base_obj B Nb hB
  have o1 : F.Obj A₁ := F.obj_sub A₁ B j hj hji oB
  have oA : F.Obj A := F.obj_quot A₁ A p hp hps o1
  obtain ⟨h1, h2, h3⟩ := M.base_abc B Nb hB
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.phiGammaModule_saturation_theorem R (F.D B) (F.D A₁) (F.map A₁ B j)
    (F.map_inj A₁ B j o1 oB hj hji) (F.map_φ A₁ B j o1 oB hj) (F.map_γ A₁ B j o1 oB hj)
    Dt.w Dt.wst Nb h1 h2 h3
  exact ⟨oA, GlobalTheory.T.phiGammaLatticeFamily_image_of_surjective R (F.D A₁) (F.D A) (F.map A₁ A p)
    (F.map_surj A₁ A p o1 oA hp hps) (F.map_φ A₁ A p o1 oA hp) (F.map_γ A₁ A p o1 oA hp)
    Dt.w Dt.wst (F.pre A₁ B j Nb) s1 s2 s3⟩

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPushOfSurjective
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem ModTh.model_push_of_surjective {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l]
    [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G)
    (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n A.m) (hp : IsHom A B p)
    (hs : Function.Surjective p) (hN : M.Model A N) : M.Model B (F.push A B p N) := by
  obtain ⟨C, Nb, A₁, j, q, hb, hj, hji, hq, hqs, rfl⟩ := hN
  have hC : F.Obj C := M.base_obj C Nb hb
  have h1 : F.Obj A₁ := F.obj_sub A₁ C j hj hji hC
  have hA : F.Obj A := F.obj_quot A₁ A q hq hqs h1
  have hB : F.Obj B := F.obj_quot A B p hp hs hA
  refine ⟨C, Nb, A₁, j, p ∘ₗ q, hb, hj, hji, fun g x => ?_, hs.comp hqs, ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hq g x, hp g]
  · funext i
    simp only [DFun.push]
    rw [F.map_comp A₁ A B q p h1 hA hB hq hp i, ← Submodule.map_comp]
    rfl

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelSup
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.SupModel

variable {k G : Type} [Field k] [Group G]

theorem isHom_comp {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hf : IsHom A B f) (hg : IsHom B C g) : IsHom A C (g ∘ₗ f) :=
  fun s x => by simp only [LinearMap.comp_apply]; rw [hf, hg]

theorem isHom_add {A B : Ob k G} {f g : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    (hf : IsHom A B f) (hg : IsHom A B g) : IsHom A B (f + g) :=
  fun s x => by simp only [LinearMap.add_apply, map_add]; rw [hf, hg]

theorem exists_sum (A B : Ob k G) : ∃ (C : Ob k G) (i : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (j : (Fin B.m → k) →ₗ[k] (Fin C.m → k)), IsHom A C i ∧ IsHom B C j ∧ Function.Bijective (i.coprod j) := by
  obtain ⟨C, e, he⟩ := exists_ob (A.ρ.prod B.ρ)
  refine ⟨C, e.toLinearMap ∘ₗ LinearMap.inl k _ _, e.toLinearMap ∘ₗ LinearMap.inr k _ _, ?_, ?_, ?_⟩
  · intro g x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]; congr 1; simp [Representation.prod]
  · intro g x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]; congr 1; simp [Representation.prod]
  · have : (e.toLinearMap ∘ₗ LinearMap.inl k _ _).coprod (e.toLinearMap ∘ₗ LinearMap.inr k _ _)
        = e.toLinearMap := by
      rw [← LinearMap.comp_coprod, LinearMap.coprod_inl_inr, LinearMap.comp_id]
    rw [this]; exact e.bijective

theorem exists_proj {A B C : Ob k G} {i : (Fin A.m → k) →ₗ[k] (Fin C.m → k)}
    {j : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hi : IsHom A C i) (hj : IsHom B C j)
    (hb : Function.Bijective (i.coprod j)) :
    ∃ (π : (Fin C.m → k) →ₗ[k] (Fin A.m → k)) (π' : (Fin C.m → k) →ₗ[k] (Fin B.m → k)),
      IsHom C A π ∧ IsHom C B π' ∧ (∀ x, π (i x) = x) ∧ (∀ x, π (j x) = 0) ∧ (∀ x, π' (i x) = 0) ∧
      (∀ x, π' (j x) = x) ∧ ∀ x, i (π x) + j (π' x) = x := by
  let e := LinearEquiv.ofBijective _ hb
  have h1 : ∀ x y, e.symm (i x + j y) = (x, y) := fun x y => by
    rw [LinearEquiv.symm_apply_eq]; simp [e]
  have h2 : ∀ x, i (e.symm x).1 + j (e.symm x).2 = x := fun x => by
    exact e.apply_symm_apply x
  have h3 : ∀ g x, e.symm (C.ρ g x) = (A.ρ g (e.symm x).1, B.ρ g (e.symm x).2) := fun g x => by
    rw [← h1, hi, hj, ← map_add, h2]
  refine ⟨LinearMap.fst k _ _ ∘ₗ e.symm.toLinearMap, LinearMap.snd k _ _ ∘ₗ e.symm.toLinearMap,
    fun g x => ?_, fun g x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => h2 x⟩
  · simp [h3]
  · simp [h3]
  · have := h1 x 0; simp at this; simp [this]
  · have := h1 0 x; simp at this; simp [this]
  · have := h1 x 0; simp at this; simp [this]
  · have := h1 0 x; simp at this; simp [this]

variable {l n : ℕ} {R : RingPG k l}

theorem map_comp_apply (F : DFun R n G) {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} {h : (Fin A.m → k) →ₗ[k] (Fin C.m → k)}
    (hA : F.Obj A) (hB : F.Obj B) (hC : F.Obj C) (hf : IsHom A B f) (hg : IsHom B C g)
    (hh : ∀ x, g (f x) = h x) (i : ZMod n) (x : Vc k A.m) :
    F.map B C g i (F.map A B f i x) = F.map A C h i x := by
  have : h = g ∘ₗ f := LinearMap.ext fun x => (hh x).symm
  rw [this, F.map_comp A B C f g hA hB hC hf hg]; rfl

theorem map_zero' (F : DFun R n G) {A B : Ob k G} (hA : F.Obj A) (hB : F.Obj B) (i : ZMod n) (x : Vc k A.m) :
    F.map A B 0 i x = 0 := by
  have := F.map_smul A B 0 0 hA hB (fun g x => by simp) i x
  simpa using this

theorem model_sup : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N N' : Lats k n A.m), M.Model A N → M.Model A N' → M.Model A (fun i => N i ⊔ N' i) := by
  intro k G _ _ l n _ _ _ R F r Dt M A N N' hN hN'
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  obtain ⟨B', Nb', A₂, j', p', hB', hj', hji', hp', hps', rfl⟩ := hN'
  obtain ⟨C, i, i', hi, hi', hb, hC⟩ := M.base_sum B Nb B' Nb' hB hB'
  obtain ⟨π, π', hπ, hπ', e1, e2, e3, e4, -⟩ := exists_proj hi hi' hb
  obtain ⟨S, a, a', ha, ha', hab⟩ := exists_sum A₁ A₂
  obtain ⟨q, q', hq, hq', d1, d2, d3, d4, d5⟩ := exists_proj ha ha' hab
  have oB := M.base_obj _ _ hB
  have oB' := M.base_obj _ _ hB'
  have oC := M.base_obj _ _ hC
  have o1 := F.obj_sub _ _ _ hj hji oB
  have o2 := F.obj_sub _ _ _ hj' hji' oB'
  have oS := F.obj_sum _ _ _ _ _ ha ha' hab.2 o1 o2
  have oA := F.obj_quot _ _ _ hp hps o1
  have hJ : IsHom S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') :=
    isHom_add (isHom_comp (isHom_comp hq hj) hi) (isHom_comp (isHom_comp hq' hj') hi')
  have hP : IsHom S A (p ∘ₗ q + p' ∘ₗ q') := isHom_add (isHom_comp hq hp) (isHom_comp hq' hp')
  refine ⟨C, _, S, _, _, hC, hJ, ?_, hP, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 := congrArg π hx
    have h2 := congrArg π' hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, e1, e2, e3, e4, map_zero, add_zero,
      zero_add] at h1 h2
    have h1' : q x = 0 := hji (by simpa using h1)
    have h2' : q' x = 0 := hji' (by simpa using h2)
    rw [← d5 x, h1', h2']; simp
  · intro y
    obtain ⟨x, rfl⟩ := hps y
    exact ⟨a x, by simp [d1, d3]⟩
  · funext t
    apply le_antisymm
    · apply sup_le
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨F.map A₁ S a t y, ?_, ?_⟩
        · change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t (F.map A₁ S a t y) ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t
          rw [map_comp_apply F (h := i ∘ₗ j) o1 oS oC ha hJ (fun x => by simp [d1, d3]),
            ← map_comp_apply F o1 oB oC hj hi (fun _ => rfl)]
          exact Submodule.mem_sup_left ⟨_, hy, rfl⟩
        · exact map_comp_apply F o1 oS oA ha hP (fun x => by simp [d1, d3]) t y
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨F.map A₂ S a' t y, ?_, ?_⟩
        · change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t (F.map A₂ S a' t y) ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t
          rw [map_comp_apply F (h := i' ∘ₗ j') o2 oS oC ha' hJ (fun x => by simp [d2, d4]),
            ← map_comp_apply F o2 oB' oC hj' hi' (fun _ => rfl)]
          exact Submodule.mem_sup_right ⟨_, hy, rfl⟩
        · exact map_comp_apply F o2 oS oA ha' hP (fun x => by simp [d2, d4]) t y
    · rintro _ ⟨s, hs, rfl⟩
      change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t s ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t at hs
      obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨u', hu', rfl⟩, h⟩ := Submodule.mem_sup.1 hs
      change F.map B C i t u + F.map B' C i' t u' = _ at h
      have h1 := congrArg (F.map C B π t) h
      have h2 := congrArg (F.map C B' π' t) h
      rw [map_add, map_comp_apply F (h := LinearMap.id) oB oC oB hi hπ e1,
        map_comp_apply F (h := 0) oB' oC oB hi' hπ e2, F.map_id B oB, map_zero' F oB' oB,
        map_comp_apply F (h := j ∘ₗ q) oS oC oB hJ hπ (fun x => by simp [e1, e2]),
        ← map_comp_apply F oS o1 oB hq hj (fun _ => rfl), add_zero, LinearMap.id_apply] at h1
      rw [map_add, map_comp_apply F (h := LinearMap.id) oB' oC oB' hi' hπ' e4,
        map_comp_apply F (h := 0) oB oC oB' hi hπ' e3, F.map_id B' oB', map_zero' F oB oB',
        map_comp_apply F (h := j' ∘ₗ q') oS oC oB' hJ hπ' (fun x => by simp [e3, e4]),
        ← map_comp_apply F oS o2 oB' hq' hj' (fun _ => rfl), zero_add, LinearMap.id_apply] at h2
      change F.map S A _ t s ∈ _
      rw [F.map_add S A _ _ oS oA (isHom_comp hq hp) (isHom_comp hq' hp'),
        ← map_comp_apply F oS o1 oA hq hp (fun _ => rfl), ← map_comp_apply F oS o2 oA hq' hp' (fun _ => rfl)]
      refine Submodule.add_mem_sup ⟨_, ?_, rfl⟩ ⟨_, ?_, rfl⟩
      · change F.map A₁ B j t _ ∈ Nb t
        rw [← h1]; exact hu
      · change F.map A₂ B' j' t _ ∈ Nb' t
        rw [← h2]; exact hu'

end GlobalTheory.Models.SupModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDetLeOneOfEntriesNormLeOne
section
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory

theorem norm_det_le_one_of_entries_le_one :
    ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
      (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ ≤ 1 := by
  intro E _ _ n x hx
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hp : ‖∏ i, x (σ i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hx _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul, norm_neg]; exact hp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTiltUntiltLeOfFrobeniusSeriesSizeLe
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem norm_sh_le_of_lam_le : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (ρ : ℝ) (x : Fl l), 2 ≤ h → 0 ≤ ρ → ρ < 1 → ‖sh x‖ < 1 → (∀ j : ℕ, j < 2 → ‖lam h j x‖ ≤ gam l h j ρ) → ‖sh x‖ ≤ ρ := by
  intro l _ h ρ x h2 hρ0 hρ1 hs1 hlam
  by_contra hlt
  push_neg at hlt
  set s := ‖sh x‖ with hs
  have hs0 : 0 < s := lt_of_le_of_lt hρ0 hlt
  have h1 : 1 ≤ h := le_trans (by norm_num) h2
  obtain ⟨j, hj, n₀, hn₀⟩ := GlobalTheory.T.exists_unique_max_term_untiltFrobeniusSeries l h s h2 hs0 hs1
  obtain ⟨hsum, -, -, -⟩ := GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j s x h1 hs1 le_rfl
  have hpw := (GlobalTheory.T.tiltFrobeniusIntegerPower_laws l).2.2.2.2.2.2
  have hterm : ∀ n : ℤ, ‖(l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)‖
      = ‖(l : ℂ_[l])‖ ^ (-n) * s ^ ((l : ℝ) ^ (n * h + j : ℤ)) := by
    intro n
    rw [norm_mul, norm_zpow, hpw]
  have hnorm : ‖lam h j x‖ = ‖(l : ℂ_[l])‖ ^ (-n₀) * s ^ ((l : ℝ) ^ (n₀ * h + j : ℤ)) := by
    rw [GlobalTheory.T.norm_eq_of_hasSum_of_dominant_term ℂ_[l] ℤ _ _ n₀ hsum (by
      intro n hn
      rw [hterm, hterm]
      exact hn₀ n hn), hterm]
  obtain ⟨-, ⟨m, hm⟩, -, -, -, hmono⟩ := GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j s h1 hs0.le hs1
  have hgs : gam l h j s ≤ ‖lam h j x‖ := by
    rw [hm, hnorm]
    by_cases hmn : m = n₀
    · rw [hmn]
    · exact (hn₀ m hmn).le
  have hgρ : gam l h j ρ < gam l h j s := ((GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j ρ h1 hρ0 hρ1).2.2.2.2.2) s hlt hs1
  have := hlam j hj
  linarith

end GlobalTheory.PSer
end

