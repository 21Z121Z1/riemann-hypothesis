import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsoluteHermitianVolumeBoundArithStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolute_hermitian_volume_bound_arith : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (n : ℕ) (X : ℝ), 8 ≤ n → 2 ≤ X → 2 * Formalism.HermitianLatticesTheory.vInv E ≤ X → 2 * Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ≤ X ^ 2 → volU 2 ^ Formalism.HermitianLatticesTheory.fDeg E * (4 ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E) * (1 + Formalism.HermitianLatticesTheory.fDeg E * Real.log (2 * Formalism.HermitianLatticesTheory.vInv E)) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E)) * ∏ M ∈ Finset.Ioc 2 n, rankFac E M ≤ X ^ (n ^ 2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  first | exact @GlobalTheory.VolArith.volume_bound_arith | exact GlobalTheory.VolArith.volume_bound_arith | (intros; apply GlobalTheory.VolArith.volume_bound_arith <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeCarryIffForallPlace
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.Carry

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in

theorem prVec_mulVec (v : HeightOneSpectrum (𝓞 F)) (y : GL (Fin n) (E ⊗[F] Ad F)) (x : Fin n → E ⊗[F] Ad F) :
    prVec v (y.1 *ᵥ x) = (bc (prV (E := E) v) y).1 *ᵥ prVec v x := by
  funext i
  exact RingHom.map_mulVec (prV (E := E) v) y.1 x i

omit [NumberField E] in
theorem prVec_single_self (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] v.adicCompletion F) :
    prVec v (fun i => Formalism.UG.P.afsplitIE v (x i)) = x := by
  funext i
  exact Formalism.UG.P.afsplit_prV_IE v (x i)

omit [NumberField E] in
theorem prVec_single_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : Fin n → E ⊗[F] v.adicCompletion F) :
    prVec w (fun i => Formalism.UG.P.afsplitIE v (x i)) = 0 := by
  funext i
  exact Formalism.UG.P.afsplit_prV_IE_ne v w h (x i)

theorem carry_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → ∀ y : GL (Fin n) (E ⊗[F] Ad F), (∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F M) ↔ ∀ v : HeightOneSpectrum (𝓞 F), ∀ x, x ∈ loc v L ↔ (bc (prV (E := E) v) y).1 *ᵥ x ∈ loc v M := by
  intro F E _ _ _ _ _ n L M hL hM y
  have lgL := GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n L hL
  have lgM := GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n M hM
  constructor
  · intro h v x
    have h1 := h (fun i => Formalism.UG.P.afsplitIE v (x i))
    rw [lgL, lgM] at h1
    constructor
    · intro hx
      have h2 := h1.1 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [prVec_single_self]; exact hx
        · rw [prVec_single_ne v w hw]; exact Submodule.zero_mem _) v
      rwa [prVec_mulVec, prVec_single_self] at h2
    · intro hx
      have h2 := h1.2 (fun w => by
        rw [prVec_mulVec]
        by_cases hw : w = v
        · subst hw; rw [prVec_single_self]; exact hx
        · rw [prVec_single_ne v w hw, Matrix.mulVec_zero]; exact Submodule.zero_mem _) v
      rwa [prVec_single_self] at h2
  · intro h x
    rw [lgL, lgM]
    refine forall_congr' fun v => ?_
    rw [prVec_mulVec]
    exact h v _

end GlobalTheory.St.G.Carry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitianStatement
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLattice_selfDual_hermitian : ∀ (I : AutInst) (y : Fin I.n → (I.E ⊗[I.F] Af I.F)), y ∈ I.Lf ↔ ∀ y' ∈ I.Lf, hAf I y' y ∈ IntAf I.F I.E := by
  first | exact @GlobalTheory.AdelicLattice.adelicLattice_selfDual | exact GlobalTheory.AdelicLattice.adelicLattice_selfDual | (intros; apply GlobalTheory.AdelicLattice.adelicLattice_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeArithmetic
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.AmpArith

theorem v_part (k r f j : ℕ) (v : ℝ) (hr : 1 ≤ r) (hv : 1 ≤ v) :
    v ^ (k * (r - j) * f) *
        ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f
      ≤ 2 ^ (r ^ 2 * f) := by
  have hv0 : v ≠ 0 := by positivity
  have h2v : 0 ≤ 2 * v := by positivity
  have hexp : r * (k + 1) + r * (r - 1) = r * k + r ^ 2 := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel]; ring
  have hneg : (2 * v) ^ (-((r : ℝ) * k)) = ((2 * v) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg h2v, show ((r : ℝ) * k) = ((r * k : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have key : ((2 * v) ^ (r * k))⁻¹ * 1 * (2 : ℝ) ^ (r * k + r ^ 2) = 2 ^ (r ^ 2) / v ^ (r * k) := by
    rw [mul_pow, pow_add]
    field_simp
  have hle : v ^ (k * (r - j) * f) ≤ v ^ (r * k * f) := by
    apply pow_le_pow_right₀ hv
    have : r - j ≤ r := Nat.sub_le r j
    calc k * (r - j) * f ≤ k * r * f := by gcongr
    _ = r * k * f := by ring
  rw [hneg, hexp, key, div_pow, ← pow_mul, ← pow_mul, mul_div_assoc', div_le_iff₀ (by positivity)]
  calc v ^ (k * (r - j) * f) * 2 ^ (r ^ 2 * f) ≤ v ^ (r * k * f) * 2 ^ (r ^ 2 * f) := by gcongr
  _ = 2 ^ (r ^ 2 * f) * v ^ (r * k * f) := by ring

theorem exponent_bound (CH C R F : ℝ) (hCH : 0 ≤ CH) (hC : 100 * (CH + 10) ≤ C) (hR : 1 ≤ R)
    (hF : 0 ≤ F) :
    R ^ 2 * F + 3 * (2 * (R + 1) ^ 2 * F) + 3 * (2 * (R + 1) ^ 2 * F)
        + ((2 * R + 2) + 3 + CH * (2 * R + 2)) * (80 * R ^ 4 * F)
      ≤ C * (2 * R + 2) ^ 2 * F * (C * R ^ 4) := by
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR4 : R ^ 2 ≤ R ^ 4 := by nlinarith
  have hR41 : 1 ≤ R ^ 4 := le_trans hR2 hR4
  have hS : 1 ≤ (R + 1) ^ 2 := by nlinarith
  have hP0 : 0 ≤ R ^ 4 * (R + 1) ^ 2 := by positivity
  have e1 : R ^ 2 ≤ R ^ 4 * (R + 1) ^ 2 := by
    calc R ^ 2 ≤ R ^ 4 := hR4
    _ = R ^ 4 * 1 := by ring
    _ ≤ R ^ 4 * (R + 1) ^ 2 := by gcongr
  have e2 : (R + 1) ^ 2 ≤ R ^ 4 * (R + 1) ^ 2 := by
    calc (R + 1) ^ 2 = 1 * (R + 1) ^ 2 := by ring
    _ ≤ R ^ 4 * (R + 1) ^ 2 := by gcongr
  have e3 : R ^ 4 * (2 * R + 5) ≤ 5 * (R ^ 4 * (R + 1) ^ 2) := by
    have : 2 * R + 5 ≤ 5 * (R + 1) ^ 2 := by nlinarith
    calc R ^ 4 * (2 * R + 5) ≤ R ^ 4 * (5 * (R + 1) ^ 2) := by gcongr
    _ = 5 * (R ^ 4 * (R + 1) ^ 2) := by ring
  have e4 : R ^ 4 * (2 * R + 2) ≤ 2 * (R ^ 4 * (R + 1) ^ 2) := by
    have : 2 * R + 2 ≤ 2 * (R + 1) ^ 2 := by nlinarith
    calc R ^ 4 * (2 * R + 2) ≤ R ^ 4 * (2 * (R + 1) ^ 2) := by gcongr
    _ = 2 * (R ^ 4 * (R + 1) ^ 2) := by ring
  have hC1 : 1000 ≤ C := by linarith
  have hCC : 413 + 160 * CH ≤ 4 * C ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left e1 hF, mul_le_mul_of_nonneg_left e2 hF,
    mul_le_mul_of_nonneg_left e3 hF, mul_le_mul_of_nonneg_left e4 (mul_nonneg hF hCH),
    mul_le_mul_of_nonneg_left hCC (mul_nonneg hF hP0)]

theorem b_part (CH C : ℝ) (hCH : 0 ≤ CH) (hC : 100 * (CH + 10) ≤ C) (r m f : ℕ) (b v : ℝ)
    (hm : m = 2 * r + 2) (hr : 1 ≤ r) (hb : 2 ≤ b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b) :
    2 ^ (r ^ 2 * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)
        * (8 * r * b ^ (CH * m)) ^ (80 * r ^ 4 * f)
      ≤ (b ^ (C * (m : ℝ) ^ 2 * f)) ^ (C * (r : ℝ) ^ 4) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hmR : (m : ℝ) = 2 * r + 2 := by rw [hm]; push_cast; ring
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have f1 : (2 : ℝ) ^ (r ^ 2 * f) ≤ b ^ ((r : ℝ) ^ 2 * f) := by
    rw [show ((r : ℝ) ^ 2 * f) = ((r ^ 2 * f : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hb _
  have h8v : 8 * v ≤ b ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h4 : 4 ≤ b ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hb0.le]
  have f2 : (8 * v) ^ (2 * (r + 1) ^ 2 * f) ≤ b ^ (3 * (2 * ((r : ℝ) + 1) ^ 2 * f)) := by
    rw [show (3 * (2 * ((r : ℝ) + 1) ^ 2 * f)) = 3 * ((2 * (r + 1) ^ 2 * f : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_mul_natCast hb0.le]
    exact pow_le_pow_left₀ (by linarith) h8v _
  have hn : 8 * r ≤ 2 ^ (m + 3) := by
    have h1 : r < 2 ^ r := Nat.lt_two_pow_self
    have h2 : 2 ^ r ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add]
    omega
  have h8r : 8 * (r : ℝ) ≤ b ^ ((m : ℝ) + 3) := by
    rw [show ((m : ℝ) + 3) = ((m + 3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    calc 8 * (r : ℝ) = ((8 * r : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ (m + 3) : ℕ) : ℝ) := by exact_mod_cast hn
    _ = (2 : ℝ) ^ (m + 3) := by push_cast; ring
    _ ≤ b ^ (m + 3) := pow_le_pow_left₀ (by norm_num) hb _
  have h3 : 8 * (r : ℝ) * b ^ (CH * m) ≤ b ^ ((m : ℝ) + 3 + CH * m) := by
    rw [Real.rpow_add hb0]
    exact mul_le_mul_of_nonneg_right h8r (Real.rpow_nonneg hb0.le _)
  have f3 : (8 * (r : ℝ) * b ^ (CH * m)) ^ (80 * r ^ 4 * f)
      ≤ b ^ (((m : ℝ) + 3 + CH * m) * ((80 * r ^ 4 * f : ℕ) : ℝ)) := by
    rw [Real.rpow_mul_natCast hb0.le ((m : ℝ) + 3 + CH * m) (80 * r ^ 4 * f)]
    exact pow_le_pow_left₀ (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _)) h3 _
  have p2 : 0 ≤ (8 * v) ^ (2 * (r + 1) ^ 2 * f) := pow_nonneg (by linarith) _
  have hE := exponent_bound CH C (r : ℝ) (f : ℝ) hCH hC hr1 (Nat.cast_nonneg f)
  calc
    _ ≤ b ^ ((r : ℝ) ^ 2 * f) * b ^ (3 * (2 * ((r : ℝ) + 1) ^ 2 * f))
        * b ^ (3 * (2 * ((r : ℝ) + 1) ^ 2 * f))
        * b ^ (((m : ℝ) + 3 + CH * m) * ((80 * r ^ 4 * f : ℕ) : ℝ)) := by
      apply mul_le_mul _ f3 (pow_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _)) _)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg hb0.le _))
          (Real.rpow_nonneg hb0.le _))
      apply mul_le_mul _ f2 p2 (mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg hb0.le _))
      exact mul_le_mul f1 f2 p2 (Real.rpow_nonneg hb0.le _)
  _ = b ^ ((r : ℝ) ^ 2 * f + 3 * (2 * ((r : ℝ) + 1) ^ 2 * f) + 3 * (2 * ((r : ℝ) + 1) ^ 2 * f)
        + ((m : ℝ) + 3 + CH * m) * ((80 * r ^ 4 * f : ℕ) : ℝ)) := by
      rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0]
  _ ≤ b ^ (C * (m : ℝ) ^ 2 * f * (C * (r : ℝ) ^ 4)) := by
      apply Real.rpow_le_rpow_of_exponent_le hb1
      rw [hmR]; push_cast; linarith [hE]
  _ = _ := Real.rpow_mul hb0.le _ _

theorem regroup {A B D G Pi H T G' Y U : ℝ} (hA : 0 ≤ A * D) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hG0 : 0 ≤ G) (hPi : 0 ≤ Pi) (hT : 0 ≤ T) (hU : A * D ≤ U) (hY : U * B * B * H ≤ Y)
    (hG : G ≤ G') : A * B * B * D * (G * Pi * H * T) ≤ G' * Pi * Y * T := by
  have hU0 : 0 ≤ U := le_trans hA hU
  have hBBH : 0 ≤ B * B * H := mul_nonneg (mul_nonneg hB hB) hH
  have hGPT : 0 ≤ G * Pi * T := mul_nonneg (mul_nonneg hG0 hPi) hT
  have hY0 : 0 ≤ Y := le_trans (mul_nonneg (mul_nonneg (mul_nonneg hU0 hB) hB) hH) hY
  calc A * B * B * D * (G * Pi * H * T) = (A * D) * (B * B * H) * (G * Pi * T) := by ring
  _ ≤ U * (B * B * H) * (G * Pi * T) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hU hBBH) hGPT
  _ = (U * B * B * H) * (G * Pi * T) := by ring
  _ ≤ Y * (G * Pi * T) := mul_le_mul_of_nonneg_right hY hGPT
  _ ≤ Y * (G' * Pi * T) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hG hPi) hT) hY0
  _ = G' * Pi * Y * T := by ring

end GlobalTheory.AmpArith

open GlobalTheory.AmpArith in

theorem GlobalTheory.amplitude_arithmetic : ∀ CH : ℝ, 0 ≤ CH → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ (k r m f j : ℕ) (b v Del S Cs P : ℝ), m = 2 * r + 2 → 1 ≤ j → j ≤ r → r + 2 ≤ k → 1 ≤ f → 2 ≤ b → 1 ≤ v → 2 * v ≤ b → 0 < P → Del = P ^ 2 → 1 ≤ S → (v ^ (k * (r - j) * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)) * (8 * v) ^ (2 * (r + 1) ^ 2 * f) * ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f * ((16 * Real.pi * Real.exp 1 / k) ^ (j * (k - 1 - j) * f) * (P ^ (k - 1 - j))⁻¹ * (8 * r * b ^ (CH * m)) ^ (80 * r ^ 4 * f) * S ^ (-(Cs * k))) ≤ (C / k) ^ ((j : ℝ) * ((k : ℝ) - 1 - j) * f) * Del ^ (-(((k : ℝ) - 1 - j) / 2)) * (b ^ (C * (m : ℝ) ^ 2 * f)) ^ (C * (r : ℝ) ^ 4) * S ^ (-(Cs * k)) := by
  intro CH hCH
  refine ⟨100 * (CH + 10), ?_⟩
  intro C hC k r m f j b v Del S Cs P hm hj1 hjr hrk hf hb hv hvb hP hDel hS
  have hv0 : 0 ≤ v := by linarith
  have hb0 : 0 < b := by linarith
  have hr : 1 ≤ r := le_trans hj1 hjr
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hcast : ((k - 1 - j : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
    rw [Nat.cast_sub (by omega : j ≤ k - 1), Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hPi : Del ^ (-(((k : ℝ) - 1 - j) / 2)) = (P ^ (k - 1 - j))⁻¹ := by
    rw [hDel, ← Real.rpow_natCast P 2, ← Real.rpow_mul hP.le,
      show ((2 : ℕ) : ℝ) * (-(((k : ℝ) - 1 - j) / 2)) = -(((k - 1 - j : ℕ) : ℝ)) by
        rw [hcast]; push_cast; ring,
      Real.rpow_neg hP.le, Real.rpow_natCast]
  have hG : (16 * Real.pi * Real.exp 1 / k) ^ (j * (k - 1 - j) * f)
      ≤ (C / k) ^ ((j : ℝ) * ((k : ℝ) - 1 - j) * f) := by
    rw [show ((j : ℝ) * ((k : ℝ) - 1 - j) * f) = ((j * (k - 1 - j) * f : ℕ) : ℝ) by
      rw [Nat.cast_mul, Nat.cast_mul, hcast], Real.rpow_natCast]
    apply pow_le_pow_left₀ (by positivity)
    gcongr
    have h1 := Real.pi_lt_d2
    have h2 := Real.exp_one_lt_d9
    have hpe : Real.pi * Real.exp 1 < 3.15 * 2.7182818286 :=
      mul_lt_mul'' h1 h2 Real.pi_pos.le (Real.exp_pos 1).le
    nlinarith
  rw [hPi]
  exact GlobalTheory.AmpArith.regroup
    (mul_nonneg (pow_nonneg hv0 _) (pow_nonneg (mul_nonneg (mul_nonneg
      (Real.rpow_nonneg (by positivity) _) zero_le_one) (by positivity)) _))
    (pow_nonneg (by linarith) _)
    (pow_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _)) _)
    (pow_nonneg (by positivity) _)
    (inv_nonneg.mpr (pow_nonneg hP.le _))
    (Real.rpow_nonneg (by linarith) _)
    (GlobalTheory.AmpArith.v_part k r f j v hr hv)
    (GlobalTheory.AmpArith.b_part CH C hCH hC r m f b v hm hr hb hv hvb)
    hG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOperatorNormFinalArithmeticLeStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeOperatorNorm_finalArithmetic_le : ∀ (k r : ℕ) (H₁ De D : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 1 ≤ H₁ → 1 ≤ De → 0 < D → ((4 * r : ℝ) ^ (11 * r ^ 2) * De ^ (12 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * 4 ^ (k - 2 - r) * ((r + 1) * 4 ^ (24 * r ^ 3 + 1))) * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ (k - 2 - r) ≤ absBd k r H₁ De D := by
  first | exact @GlobalTheory.Amp.absArith | exact GlobalTheory.Amp.absArith | (intros; apply GlobalTheory.Amp.absArith <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeSizeConsequencesOfWordIndependentHyps
section
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.SizesProof

theorem vand_pos {n : ℕ} {x : Fin n → ℝ} (h : StrictAnti x) : 0 < Formalism.MainNotions.S.vand x :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hb => sub_pos.2 (h (Finset.mem_filter.1 hb).2)

theorem sizes_of_hyp : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), D.host.rdE ≤ large₂.sc.b →
    HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → Sizes D large₂ Cl Cg CT := by
  intro D large₂ C' Cl Cg cb Cu cT CT C0 hb h
  obtain ⟨⟨-, -, hmf, hfk, -, -, -, -, -, -, -, hg1, hg1', hg2, hg2', -, -, -, hv, -, -, hgap, hT, hCl, hCl0⟩, -, -⟩ := h
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hbe : Real.exp 1 < large₂.sc.b := Real.exp_lt_exp.2 hL
  have hb1 : 1 < large₂.sc.b := lt_trans (by simpa using Real.exp_lt_exp.2 (zero_lt_one (α := ℝ))) hbe
  have hm : D.R.m = 2 * D.R.rS + 2 := by
    have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; unfold Ranks.rS; omega
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hk : (1 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkb : (1 : ℝ) ≤ D.R.k * large₂.sc.b := by nlinarith
  have h8 : (1 : ℝ) ≤ (D.R.k * large₂.sc.b) ^ 8 := one_le_pow₀ hkb
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hgg : 1 ≤ gg D := by unfold gg; nlinarith
  have hu : ∀ w τ, StrictAnti (uS D w τ) := fun w τ => by
    have hk0 : D.R.k = (D.R.k - 1) + 1 := by have := D.R.m_add_three_le_k; omega
    have key : ∀ (i : ℕ) (hi : i + 1 < D.R.k), uS D w τ ⟨i + 1, hi⟩ < uS D w τ ⟨i, by omega⟩ := fun i hi => by
      have a := (D.hcW w τ).u_gt_v ⟨i, by omega⟩
      have b := (D.hcW w τ).v_gt_u ⟨i, by omega⟩
      unfold uS; exact_mod_cast b.trans a
    rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    have hac' : a < c := hac
    induction c, hac' using Nat.le_induction with
    | base => exact key a hc
    | succ c hc' ih => exact (key c hc).trans (ih (by omega) hc')
  refine ⟨hL, Real.log_exp _, hbe, hm, hr, D.what₂.card_Tau, hCl, hmf.trans hfk, hv, hrd, rfl, hrd ▸ hb, hgg, ?_, ?_, ?_,
    fun w => (hT w).2, fun w τ => ⟨vand_pos (hu w τ), ?_⟩, ?_⟩
  · rw [two_mul, Real.rpow_add (by linarith)]
    exact mul_le_mul hg1' hg2' (by linarith) (by linarith)
  · have : large₂.sc.b ^ (8 : ℝ) ≤ large₂.sc.b ^ Cg := by
      refine le_trans ?_ (hg1.trans hg1')
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by linarith) (by nlinarith) 8
    exact (Real.rpow_le_rpow_left_iff hb1).1 this
  · refine le_trans ?_ (hg1.trans hg1')
    exact le_trans (by nlinarith) (le_self_pow₀ hkb (by norm_num))
  · have h1 : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
    have h2 : 0 < D.host.rdE := by linarith
    have h3 : 0 < gg D := by linarith
    have h4 : 0 < VV D τ := mul_pos (D.dsig_pos τ) (Finset.prod_pos fun i _ => by positivity)
    have h5 := vand_pos (hu w τ)
    unfold Tcrit; positivity
  · intro τ
    have hp : 0 ≤ Cl * D.R.k * (D.R.m : ℝ) ^ 4 := by positivity
    have key : ∀ (i : ℕ) (hi : i + 1 < 2 * D.R.rS + D.R.k + 1),
        Cl * D.R.k * (D.R.m : ℝ) ^ 4 < lamD D τ ⟨i, by omega⟩ - lamD D τ ⟨i + 1, hi⟩ := fun i hi => by
      have := hgap τ ⟨i, by omega⟩ (by simpa [hr] using hi)
      have h0 : (0 : ℝ) ≤ D.R.r * (D.R.m : ℝ) ^ 10 := by positivity
      exact lt_of_le_of_lt (le_add_of_nonneg_right h0) this
    rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    have hac' : a < c := hac
    induction c, hac' using Nat.le_induction with
    | base => exact key a hc
    | succ c hc' ih =>
      have := key c hc
      have := ih (by omega) hc'
      linarith

end GlobalTheory.Amp.SizesProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRankStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autInst_degree_rootDiscriminant_rank : ∀ I : AutInst, Formalism.HermitianLatticesTheory.fDeg I.E = I.f ∧ 2 * Formalism.HermitianLatticesTheory.vInv I.E = I.rd ∧ 1 ≤ I.rd ∧ 1 ≤ I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ ∀ p q, HasSig I p q → p + q = I.n := by
  first | exact @GlobalTheory.FlagMeas.instance_numbers | exact GlobalTheory.FlagMeas.instance_numbers | (intros; apply GlobalTheory.FlagMeas.instance_numbers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnitaryHaarTransportDiagonalStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselUnitary_haar_transport_diagonal : ∀ (k r : ℕ) (μG : Measure (Mt k r)) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r), IsHaarOn (GG k r) μG → IsUnit P.det → Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r → ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ y, φ (Matrix.of.symm (P⁻¹ * umat y * P)) ∂(Formalism.REAL.muG ε) = c * ∫⁻ x, φ x ∂μG := by
  first | exact @GlobalTheory.HaarTransport.haar_transport | exact GlobalTheory.HaarTransport.haar_transport | (intros; apply GlobalTheory.HaarTransport.haar_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerivedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_operator_on_unitary_coefficient_eq_derived : PI.UnitaryGroupMassFormula.CapelliEig.FunAct := by
  first | exact @GlobalTheory.CapelliCoef.capelli_coef | exact GlobalTheory.CapelliCoef.capelli_coef | (intros; apply GlobalTheory.CapelliCoef.capelli_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRankOneHermitianLatticeClassesLeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_rankOne_hermitian_lattice_classes_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ N : Submodule (𝓞 E) E, ENat.card (Quot (fun X Y : {X : E × Submodule (𝓞 E) E // star X.1 = X.1 ∧ (∀ φ : E →+* ℂ, 0 < (φ X.1).re) ∧ Submodule.IsLattice E X.2 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ X.2, ∃ y ∈ X.2, t = star x * X.1 * y} = N} => ∃ c : E, c ≠ 0 ∧ star c * Y.1.1 * c = X.1.1 ∧ ∀ y, c * y ∈ Y.1.2 ↔ y ∈ X.1.2)) ≤ ((classNumber E * 2 ^ Formalism.HermitianLatticesTheory.fDeg E : ℕ) : ENat) := by
  first | exact @GlobalTheory.RankOneClasses.card_classes_le | exact GlobalTheory.RankOneClasses.card_classes_le | (intros; apply GlobalTheory.RankOneClasses.card_classes_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheoremStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_matrix_subgroup_theorem : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)), PI.IsMatGroup S → (∀ X : lieE S, unrealify (X : EuclideanSpace ℝ _) ∈ lieOf S) ∧ ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ S, (∀ i j, ‖(g - 1) i j‖ < δ) → Matrix.of.symm g ∈ expSet S (Metric.ball 0 ρ) := by
  first | exact @GlobalTheory.ClosedMatGroup.closed_subgroup | exact GlobalTheory.ClosedMatGroup.closed_subgroup | (intros; apply GlobalTheory.ClosedMatGroup.closed_subgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpenStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn S μ → (∀ C : Set (Mt k r), IsCompact C → μ C < ⊤) ∧ (∀ U : Set (Mt k r), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ S) → 0 < μ U) := by
  first | exact @GlobalTheory.SgInf.haarOn_locFinite_openPos | exact GlobalTheory.SgInf.haarOn_locFinite_openPos | (intros; apply GlobalTheory.SgInf.haarOn_locFinite_openPos <;> assumption)
end

