import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.Bundle0001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegion
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.LFCoords

open Ad3

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem modulus_add_le_max (x y : F) :
    (modulus (x + y) : ℝ) ≤ max (modulus x : ℝ) (modulus y : ℝ) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rcases le_total (ord x) (ord y) with h | h
  · have hmem : x + y ∈ valBall F (ord x) :=
      add_mem mem_valBall_ord (valBall_antitone h mem_valBall_ord)
    have h1 := modulus_le_of_mem_valBall hmem
    rw [← modulus_of_ne_zero hx] at h1
    have h1' : (modulus (x + y) : ℝ) ≤ modulus x := by exact_mod_cast h1
    exact h1'.trans (le_max_left _ _)
  · have hmem : x + y ∈ valBall F (ord y) :=
      add_mem (valBall_antitone h mem_valBall_ord) mem_valBall_ord
    have h1 := modulus_le_of_mem_valBall hmem
    rw [← modulus_of_ne_zero hy] at h1
    have h1' : (modulus (x + y) : ℝ) ≤ modulus y := by exact_mod_cast h1
    exact h1'.trans (le_max_right _ _)

theorem modulus_neg_self (x : F) : modulus (-x) = modulus x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [modulus_of_ne_zero hx, modulus_of_ne_zero (neg_ne_zero.mpr hx)]
  simp [ord, Valuation.map_neg]

theorem modulus_le_one_real {x : F} (hx : x ∈ 𝒪[F]) : (modulus x : ℝ) ≤ 1 := by
  exact_mod_cast modulus_le_one_iff.2 hx

theorem modulus_mul_entry_le {κ k : Matrix (Fin 2) (Fin 2) F} (hκ : ∀ i j, κ i j ∈ 𝒪[F]) {B : ℝ}
    (hk : ∀ i j, (modulus (k i j) : ℝ) ≤ B) (i l : Fin 2) : (modulus ((κ * k) i l) : ℝ) ≤ B := by
  have term : ∀ j, (modulus (κ i j * k j l) : ℝ) ≤ B := fun j => by
    rw [modulus_mul, NNReal.coe_mul]
    calc (modulus (κ i j) : ℝ) * modulus (k j l) ≤ 1 * modulus (k j l) :=
          mul_le_mul_of_nonneg_right (modulus_le_one_real (hκ i j)) (NNReal.coe_nonneg _)
      _ ≤ B := by simpa using hk j l
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact (modulus_add_le_max _ _).trans (max_le (term 0) (term 1))

theorem exists_one_le_modulus {κ : GL (Fin 2) F} (hκ : κ ∈ GLnLocal.integralGL F 2) :
    ∃ j, 1 ≤ (modulus ((κ : Matrix (Fin 2) (Fin 2) F) 1 j) : ℝ) := by
  have hinv := ((GLnLocal.mem_integralGL_iff F 2).1 hκ).2
  have e : (κ : Matrix (Fin 2) (Fin 2) F) * ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e11 := congrFun (congrFun e 1) 1
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e11
  by_contra hcon
  push_neg at hcon
  have term : ∀ j, (modulus ((κ : Matrix (Fin 2) (Fin 2) F) 1 j *
      ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) j 1) : ℝ) < 1 := fun j => by
    rw [modulus_mul, NNReal.coe_mul]
    calc (modulus ((κ : Matrix (Fin 2) (Fin 2) F) 1 j) : ℝ) *
          modulus (((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) j 1)
        ≤ (modulus ((κ : Matrix (Fin 2) (Fin 2) F) 1 j) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (modulus_le_one_real (hinv j 1)) (NNReal.coe_nonneg _)
      _ < 1 := by simpa using hcon j
  have h := modulus_add_le_max ((κ : Matrix (Fin 2) (Fin 2) F) 1 0 *
      ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1)
    ((κ : Matrix (Fin 2) (Fin 2) F) 1 1 * ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1)
  rw [e11, modulus_one, NNReal.coe_one] at h
  exact absurd h (not_le.2 (max_lt (term 0) (term 1)))

theorem modulus_unif_zpow (m : ℤ) :
    (modulus ((unifUnit F ^ m : Fˣ) : F) : ℝ) = (residueCard F : ℝ) ^ (-m) := by
  rw [modulus_of_ne_zero (Units.ne_zero _), ord_unifUnit_zpow, NNReal.coe_zpow, NNReal.coe_natCast]

theorem modulus_unif_zpow_inv (m : ℤ) :
    (modulus (((unifUnit F ^ m)⁻¹ : Fˣ) : F) : ℝ) = (residueCard F : ℝ) ^ m := by
  rw [Units.val_inv_eq_inv_val, modulus_inv, NNReal.coe_inv, modulus_unif_zpow, _root_.zpow_neg, inv_inv]

theorem val_inv_uni_dg (x : F) (a b : Fˣ) :
    (((uni2 x * dg2 a b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((a⁻¹ : Fˣ) : F), ((a⁻¹ : Fˣ) : F) * -x; 0, ((b⁻¹ : Fˣ) : F)] := by
  have h : (((uni2 x * dg2 a b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((a⁻¹ : Fˣ) : F), 0; 0, ((b⁻¹ : Fˣ) : F)] * !![1, -x; 0, 1] := by
    rw [_root_.mul_inv_rev, Units.val_mul]
    rfl
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem val_uni_dg_mul_last (x : F) (a b : Fˣ) (κ : GL (Fin 2) F) (j : Fin 2) :
    ((uni2 x * dg2 a b * κ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j =
      (b : F) * (κ : Matrix (Fin 2) (Fin 2) F) 1 j := by
  have h : ((uni2 x * dg2 a b * κ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (!![1, x; 0, 1] * !![(a : F), 0; 0, (b : F)]) * (κ : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, Units.val_mul]
    rfl
  rw [h]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

end

theorem coords : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (x : F) (m n L : ℤ) (κ : GL (Fin 2) F) (R : ℝ) (t : Fˣ), κ ∈ GLnLocal.integralGL F 2 → R ≤ (residueCard F : ℝ) ^ L → (Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ)⁻¹ ∈ Ad3.LFS.om R t → m ≤ L ∧ n ≤ L ∧ (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ (modulus (t : F) : ℝ) * (residueCard F : ℝ) ^ (-n) ≤ (residueCard F : ℝ) ^ L := by
  intro F _ _ _ _ x m n L κ R t hκ hR hk
  obtain ⟨h1, h2⟩ := hk
  have hq : (1 : ℝ) < residueCard F := by exact_mod_cast one_lt_residueCard (K := F)
  have hq0 : (0 : ℝ) < residueCard F := zero_lt_one.trans hq
  set a : GL (Fin 2) F := uni2 x * dg2 (unifUnit F ^ m) (unifUnit F ^ n) with ha
  have hent := ((GLnLocal.mem_integralGL_iff F 2).1 hκ).1

  have hmul : (κ : Matrix (Fin 2) (Fin 2) F) * (((a * κ)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, _root_.mul_inv_rev, mul_inv_cancel_left]
  have hb : ∀ i l, (modulus (((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i l) : ℝ) ≤
      (residueCard F : ℝ) ^ L := fun i l => by
    rw [← hmul]
    exact modulus_mul_entry_le hent (fun i j => (h1 i j).trans hR) i l
  have hval : ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _ := val_inv_uni_dg x _ _
  have b00 := hb 0 0
  have b01 := hb 0 1
  have b11 := hb 1 1
  rw [hval] at b00 b01 b11
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at b00 b01 b11
  rw [modulus_unif_zpow_inv] at b00 b11
  rw [modulus_mul, NNReal.coe_mul, modulus_unif_zpow_inv, modulus_neg_self] at b01
  refine ⟨(zpow_le_zpow_iff_right₀ hq).1 b00, (zpow_le_zpow_iff_right₀ hq).1 b11, ?_, ?_⟩
  · rw [zpow_sub₀ hq0.ne', le_div_iff₀ (zpow_pos hq0 m), mul_comm]
    exact b01
  · obtain ⟨j, hj⟩ := exists_one_le_modulus hκ
    have h3 := h2 j
    rw [inv_inv, ha, val_uni_dg_mul_last, modulus_mul, modulus_mul, NNReal.coe_mul, NNReal.coe_mul,
      modulus_unif_zpow] at h3
    have hnn : 0 ≤ (modulus (t : F) : ℝ) * (residueCard F : ℝ) ^ (-n) :=
      mul_nonneg (NNReal.coe_nonneg _) (zpow_pos hq0 _).le
    calc (modulus (t : F) : ℝ) * (residueCard F : ℝ) ^ (-n)
        ≤ (modulus (t : F) : ℝ) * (residueCard F : ℝ) ^ (-n) * modulus ((κ : Matrix (Fin 2) (Fin 2) F) 1 j) :=
          le_mul_of_one_le_right hnn hj
      _ = (modulus (t : F) : ℝ) * ((residueCard F : ℝ) ^ (-n) * modulus ((κ : Matrix (Fin 2) (Fin 2) F) 1 j)) := by ring
      _ ≤ R := h3
      _ ≤ _ := hR

end GlobalTheory.CompanionTheory.LFCoords
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaSumMeasureEstimate
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.ShellSum

lemma shell_exponent_identity (q A : ℝ) (L m n : ℤ) (hq : 1 < q) :
    A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2) * q ^ (L - n)
      = A * q ^ L * q ^ ((m : ℝ) / 4) * q ^ (-(n : ℝ) / 4) := by
  have hq0 : 0 < q := by linarith
  have e1 : q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2) * q ^ (((L - n : ℤ)) : ℝ)
      = q ^ (L : ℝ) * q ^ ((m : ℝ) / 4) * q ^ (-(n : ℝ) / 4) := by
    rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
    congr 1
    push_cast
    ring
  rw [Real.rpow_intCast, Real.rpow_intCast] at e1
  linear_combination A * e1

theorem lintegral_le_of_shells :
    ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (q A τ : ℝ) (L : ℤ) (c T₁ T₂ : ℝ≥0∞)
      (S : ℤ → ℤ → Set X) (Φ : X → ℝ≥0∞), 1 < q → 0 ≤ A → 0 < τ →
      (∀ m n, MeasurableSet (S m n)) →
      (∀ m n, n ≤ L → μ (S m n) ≤ ENNReal.ofReal (q ^ (L - n)) * c) →
      (∑' m : ℤ, (if m ≤ L then ENNReal.ofReal (q ^ ((m : ℝ) / 4)) else 0)) ≤ T₁ →
      (∑' n : ℤ, (if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) else 0)) ≤ T₂ →
      (∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L ∧ y ∈ S m n ∧
        Φ y ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2))) →
      ∫⁻ y, Φ y ∂μ ≤ ENNReal.ofReal (A * q ^ L) * T₁ * T₂ * c := by
  intro X _ μ q A τ L c T₁ T₂ S Φ hq hA hτ hS hμ hT1 hT2 hΦ
  have hq0 : 0 < q := by linarith
  let a : ℤ → ℝ≥0∞ := fun m => if m ≤ L then ENNReal.ofReal (q ^ ((m : ℝ) / 4)) else 0
  let b : ℤ → ℝ≥0∞ := fun n =>
    if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) else 0
  let w : ℤ × ℤ → ℝ≥0∞ := fun p =>
    if p.1 ≤ L ∧ p.2 ≤ L ∧ τ * q ^ (-p.2) ≤ q ^ L then
      ENNReal.ofReal (A * q ^ (((p.2 : ℝ) - p.1) / 4) * q ^ (((p.1 : ℝ) + p.2) / 2))
    else 0
  have hpt : ∀ y, Φ y ≤ ∑' p : ℤ × ℤ, (S p.1 p.2).indicator (fun _ => w p) y := by
    intro y
    by_cases h0 : Φ y = 0
    · simp [h0]
    obtain ⟨m, n, h1, h2, h3, h4, h5⟩ := hΦ y h0
    refine le_trans ?_ (ENNReal.le_tsum (m, n))
    have hw : w (m, n) = ENNReal.ofReal
        (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) := by
      simp only [w]
      rw [if_pos ⟨h1, h2, h3⟩]
    rw [Set.indicator_of_mem (show y ∈ S (m, n).1 (m, n).2 from h4), hw]
    exact h5
  have hterm : ∀ p : ℤ × ℤ,
      w p * μ (S p.1 p.2) ≤ ENNReal.ofReal (A * q ^ L) * (a p.1 * b p.2 * c) := by
    rintro ⟨m, n⟩
    by_cases hc : m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L
    · obtain ⟨h1, h2, h3⟩ := hc
      have hw : w (m, n) = ENNReal.ofReal
          (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) := by
        simp only [w]
        rw [if_pos ⟨h1, h2, h3⟩]
      have ha : a m = ENNReal.ofReal (q ^ ((m : ℝ) / 4)) := by
        simp only [a]
        rw [if_pos h1]
      have hb : b n = ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) := by
        simp only [b]
        rw [if_pos h3]
      have hnn1 : 0 ≤ A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2) := by positivity
      have hnn2 : 0 ≤ A * q ^ L := by positivity
      have hnn3 : 0 ≤ q ^ ((m : ℝ) / 4) := by positivity
      show w (m, n) * μ (S m n) ≤ ENNReal.ofReal (A * q ^ L) * (a m * b n * c)
      rw [hw, ha, hb]
      calc ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) * μ (S m n)
          ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) *
              (ENNReal.ofReal (q ^ (L - n)) * c) := by
            gcongr
            exact hμ m n h2
        _ = ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2) * q ^ (L - n))
              * c := by
            rw [ENNReal.ofReal_mul hnn1]
            ring
        _ = ENNReal.ofReal (A * q ^ L * q ^ ((m : ℝ) / 4) * q ^ (-(n : ℝ) / 4)) * c := by
            rw [shell_exponent_identity q A L m n hq]
        _ = ENNReal.ofReal (A * q ^ L) *
              (ENNReal.ofReal (q ^ ((m : ℝ) / 4)) * ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) * c) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hnn2]
            ring
    · have hw : w (m, n) = 0 := by
        simp only [w]
        rw [if_neg hc]
      show w (m, n) * μ (S m n) ≤ _
      rw [hw, zero_mul]
      exact zero_le
  have hfac : ∑' p : ℤ × ℤ, a p.1 * b p.2 * c = (∑' m, a m) * (∑' n, b n) * c := by
    rw [ENNReal.tsum_prod (f := fun m n => a m * b n * c)]
    simp only [mul_assoc]
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  calc ∫⁻ y, Φ y ∂μ
      ≤ ∫⁻ y, ∑' p : ℤ × ℤ, (S p.1 p.2).indicator (fun _ => w p) y ∂μ := lintegral_mono hpt
    _ = ∑' p : ℤ × ℤ, ∫⁻ y, (S p.1 p.2).indicator (fun _ => w p) y ∂μ :=
        lintegral_tsum fun p => (measurable_const.indicator (hS p.1 p.2)).aemeasurable
    _ = ∑' p : ℤ × ℤ, w p * μ (S p.1 p.2) := by
        refine tsum_congr fun p => ?_
        exact lintegral_indicator_const (hS p.1 p.2) (w p)
    _ ≤ ∑' p : ℤ × ℤ, ENNReal.ofReal (A * q ^ L) * (a p.1 * b p.2 * c) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (A * q ^ L) * ((∑' m, a m) * (∑' n, b n) * c) := by
        rw [ENNReal.tsum_mul_left, hfac]
    _ ≤ ENNReal.ofReal (A * q ^ L) * (T₁ * T₂ * c) := by
        gcongr
    _ = ENNReal.ofReal (A * q ^ L) * T₁ * T₂ * c := by ring

end GlobalTheory.CompanionTheory.ShellSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
section
noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.JacExp

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem exists_atom_le {ρ : Representation ℂ G V} (h : HasFiniteLength ρ) {E : Subrepresentation ρ}
    (hE : E ≠ ⊥) : ∃ S : Subrepresentation ρ, IsAtom S ∧ S ≤ E := by
  obtain ⟨-, hw⟩ := (hasFiniteLength_iff_wellFounded ρ).1 h
  haveI : IsAtomic (Subrepresentation ρ) := isAtomic_of_orderBot_wellFounded_lt hw.wf
  obtain h' | ⟨S, hS, hle⟩ := eq_bot_or_exists_atom_le E
  · exact absurd h' hE
  · exact ⟨S, hS, hle⟩

def eigenSub (ρ : Representation ℂ G V) (z : G) (hz : ∀ g, z * g = g * z) (ν : ℂ) : Subrepresentation ρ :=
  ⟨Module.End.eigenspace (ρ z) ν, fun g v hv => by
    have hv' : ρ z v = ν • v := Module.End.mem_eigenspace_iff.1 hv
    refine Module.End.mem_eigenspace_iff.2 ?_
    have : ρ z (ρ g v) = ρ g (ρ z v) := by
      rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply]
    rw [this, hv', map_smul]⟩

theorem mem_eigenSub {ρ : Representation ℂ G V} {z : G} {hz : ∀ g, z * g = g * z} {ν : ℂ} {v : V} :
    v ∈ (eigenSub ρ z hz ν).toSubmodule ↔ ρ z v = ν • v :=
  Module.End.mem_eigenspace_iff

theorem isSmooth_sub [TopologicalSpace G] {ρ : Representation ℂ G V} (h : IsSmooth ρ)
    (S : Subrepresentation ρ) : IsSmooth S.toRepresentation := fun v => by
  have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g v.1 = v.1} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact h v.1

end General

section Tensor

variable {Γ X Y : Fin 2 → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]

theorem piTensor_apply_of_scalar (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : ℂ)
    (h0 : ∀ v, ρ 0 (g 0) v = c • v) (h1 : ∀ v, ρ 1 (g 1) v = v) (z : PiTensorProduct ℂ X) :
    piTensor ρ g z = c • z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    have : (fun a => ρ a (g a) (f a)) = Function.update f 0 (c • f 0) := by
      funext a
      fin_cases a
      · simp [h0]
      · simp [h1]
    rw [this, MultilinearMap.map_update_smul, Function.update_eq_self]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

def piTensorCongr {ρ : ∀ a, Representation ℂ (Γ a) (X a)} {σ : ∀ a, Representation ℂ (Γ a) (Y a)}
    (φ : ∀ a, (ρ a).Equiv (σ a)) : (piTensor ρ).Equiv (piTensor σ) :=
  .mk (PiTensorProduct.congr fun a => (φ a).toLinearEquiv) fun g => by
    apply PiTensorProduct.ext
    ext f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      piTensor_tprod, PiTensorProduct.congr_tprod]
    exact congrArg _ (funext fun a => (φ a).toIntertwiningMap.isIntertwining _ _ (g a) (f a))

end Tensor

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def omegaLevi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) : Levi k (fun a => Fin (d a)) :=
  fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) (if a = 0 then Zls.unifU k else 1)

theorem omegaLevi_comm (d : Fin 2 → ℕ) (h : Levi k (fun a => Fin (d a))) :
    omegaLevi k d * h = h * omegaLevi k d := by
  funext a
  apply Units.ext
  simp only [omegaLevi, Matrix.GeneralLinearGroup.scalar, Pi.mul_apply, Units.val_mul, Units.coe_map,
    MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact Matrix.scalar_commute _ (fun r => Commute.all _ _) _

theorem diagPow_val (N : ℕ) (lam : Fin N → ℤ) :
    (Zls.diagPow k N lam : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((Zls.unifU k ^ lam i : kˣ) : k) := rfl

theorem leviEmb_omegaLevi {N : ℕ} (d : Fin 2 → ℕ) (hd : ∑ a, d a = N) :
    leviEmb k (stdBlocks d hd) (omegaLevi k d) = Zls.diagPow k N (Zls.omegaVec N (d 0)) := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [diagPow_val]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      have hv := stdBlocks_val d hd a i
      have : (((stdBlocks d hd ⟨a, i⟩ : Fin N) : ℕ) < d 0) ↔ a = 0 := by
        rw [hv]
        fin_cases a
        · simp
        · simp
      simp [omegaLevi, Zls.omegaVec, this, Matrix.GeneralLinearGroup.scalar]
    · have : (stdBlocks d hd ⟨a, i⟩) ≠ (stdBlocks d hd ⟨a, j⟩) := by simpa using hij
      simp [omegaLevi, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply_ne _ this, hij]
  · have : (stdBlocks d hd ⟨a, i⟩) ≠ (stdBlocks d hd ⟨b, j⟩) := fun h =>
      hab (congrArg Sigma.fst ((stdBlocks d hd).injective h))
    rw [leviEmb_apply_ne k _ _ hab, Matrix.diagonal_apply_ne _ this]

theorem deltaHalf_omegaLevi (d : Fin 2 → ℕ) :
    (((deltaHalf k (fun a => Fin (d a)) (omegaLevi k d))⁻¹ : ℂˣ) : ℂ) =
      (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2) := by
  have h0 : modExp (fun a : Fin 2 => Fin (d a)) 0 = d 1 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have hd0 : Matrix.GeneralLinearGroup.det (omegaLevi k d 0) = Zls.unifU k ^ d 0 := by
    apply Units.ext
    simp [omegaLevi, Matrix.GeneralLinearGroup.scalar]
  have hd1 : Matrix.GeneralLinearGroup.det (omegaLevi k d 1) = 1 := by
    apply Units.ext
    simp [omegaLevi, Matrix.GeneralLinearGroup.scalar]
  have hn : nabs k (Zls.unifU k) = (resCard k : ℝ)⁻¹ :=
    nabs_uniformiser Zls.irreducible_unif rfl
  rw [deltaHalf_apply, Fin.prod_univ_two, hd0, hd1, map_one, mul_one, map_pow, h0]
  have hq : ((((resCard k : ℝ)⁻¹ : ℝ)) : ℂ) = ((Nat.card 𝓀[k] : ℂ))⁻¹ := by simp [resCard]
  have harg : Complex.arg (Nat.card 𝓀[k] : ℂ) ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_pos.ne
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, val_absPow, hn, hq, Complex.inv_cpow _ _ harg,
    inv_pow, inv_inv, ← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

theorem exists_scalarBy (x : IrrGL k) (t : kˣ) : ∃ c : ℂ, Zl.ScalarBy x t c := by
  obtain ⟨ω, -, hω⟩ := ((schur_and_segments k).1 (Fin x.1) _ x.rep x.2.rep.smooth x.2.rep.irr).2
  exact ⟨ω t, fun v => hω t v⟩

theorem jm_ne_zero_of_equiv {h N : ℕ} (x : Fin h → IrrGL k) (hx : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (S : Subrepresentation (jac (stdBlocks (fun a => (x a).1) hx) π))
    (Φ : S.toRepresentation.Equiv (piTensor fun a => (x a).rep)) : Zc.jm x hx π ≠ 0 :=
  jhMult_ne_zero_iff.2 ⟨S, Φ.toIntertwiningMap, Φ.surjective⟩

theorem exists_constituent (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) (d : Fin 2 → ℕ)
    (hd : ∑ a, d a = N) (μ : ℂ) (w : V)
    (hw : (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0)
    (hμ : (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) w) :
        Jacquet π (unipRad k (stdBlocks d hd))) =
      μ • (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd)))) :
    ∃ (x : Fin 2 → IrrGL k) (hx : ∑ a, (x a).1 = N), (∀ a, (x a).1 = d a) ∧ Zc.jm x hx π ≠ 0 ∧
      Zl.ScalarBy (x 0) (Zls.unifU k) (μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2)) ∧
      ∃ c1 : ℂ, Zl.ScalarBy (x 1) (Zls.unifU k) c1 := by
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hfl : HasFiniteLength (jac (stdBlocks d hd) π) :=
    (hBZ k).2.1 (Fin 2) (Fin N) (fun a => Fin (d a)) (stdBlocks d hd) V π hs
      (hasFiniteLength_of_isIrreducible hi)
  set ν : ℂ := μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2) with hν
  set w' : Jacquet π (unipRad k (stdBlocks d hd)) := Submodule.Quotient.mk w with hw'
  have heig : jac (stdBlocks d hd) π (omegaLevi k d) w' = ν • w' := by
    rw [hw', jac_mk, leviEmb_omegaLevi, hμ, deltaHalf_omegaLevi, smul_smul, hν, mul_comm]
  set E := eigenSub (jac (stdBlocks d hd) π) (omegaLevi k d) (omegaLevi_comm d) ν with hE
  have hEne : E ≠ ⊥ := by
    intro h
    have : w' ∈ E.toSubmodule := mem_eigenSub.2 heig
    rw [h] at this
    exact hw ((Submodule.mem_bot ℂ).1 this)
  obtain ⟨S, hS, hSE⟩ := exists_atom_le hfl hEne
  have hSirr : S.toRepresentation.IsIrreducible := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨S.toSubmodule, S.toRepresentation, isSmooth_sub (isSmooth_jac _ hs) S, hSirr⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hBZ k (Fin 2) (fun a => Fin (d a)) τ
  let x : Fin 2 → IrrGL k := fun a => IrrGL.of (N := d a) (s a).ρ (s a).smooth (s a).irr
  let Ψ : S.toRepresentation.Equiv (piTensor fun a => (x a).rep) :=
    Φ.trans (piTensorCongr fun a => IrrGL.equivOf (N := d a) (s a).ρ (s a).smooth (s a).irr)
  obtain ⟨c₀, hc₀⟩ := exists_scalarBy (x 0) (Zls.unifU k)
  obtain ⟨c₁, hc₁⟩ := exists_scalarBy (x 1) (Zls.unifU k)
  refine ⟨x, hd, fun a => rfl, jm_ne_zero_of_equiv x hd π S Ψ, ?_, c₁, hc₁⟩
  have hSne : S.toSubmodule ≠ ⊥ := fun h => hS.1 (Subrepresentation.ext h)
  obtain ⟨v₀, hv₀, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSne
  let v : S.toSubmodule := ⟨v₀, hv₀⟩
  have hv : v ≠ 0 := fun h => hv₀ne (congrArg Subtype.val h)
  have h1 : S.toRepresentation (omegaLevi k d) v = ν • v := Subtype.ext (mem_eigenSub.1 (hSE hv₀))
  have h2 : piTensor (fun a => (x a).rep) (omegaLevi k d) (Ψ v) = c₀ • Ψ v := by
    refine piTensor_apply_of_scalar _ _ c₀ (fun u => ?_) (fun u => ?_) _
    · have : omegaLevi k d 0 = Matrix.GeneralLinearGroup.scalar (Fin (x 0).1) (Zls.unifU k) := by
        simp [omegaLevi]
        rfl
      rw [this]
      exact hc₀ u
    · have : omegaLevi k d 1 = 1 := by simp [omegaLevi]
      rw [this]
      exact LinearMap.congr_fun (map_one (x 1).rep) u
  have h3 : Ψ (S.toRepresentation (omegaLevi k d) v) =
      piTensor (fun a => (x a).rep) (omegaLevi k d) (Ψ v) :=
    Ψ.toIntertwiningMap.isIntertwining _ _ _ v
  have h4 : Ψ v ≠ 0 := fun h => hv (Ψ.toLinearEquiv.injective (by simpa using h))
  have h5 : ν • Ψ v = c₀ • Ψ v := by
    rw [← h2, ← h3, h1, map_smul]
  have h6 : c₀ = ν := (smul_left_injective ℂ h4 h5).symm
  rw [← h6]
  exact hc₀

theorem exists_constituent_of_eigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ (μ : ℂ) (w : V), (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 → (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) w) : Jacquet π (unipRad k (stdBlocks d hd))) = μ • (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) → ∃ (x : Fin 2 → IrrGL k) (hx : ∑ a, (x a).1 = N), (∀ a, (x a).1 = d a) ∧ Zc.jm x hx π ≠ 0 ∧ Zl.ScalarBy (x 0) (Zls.unifU k) (μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2)) ∧ ∃ c1 : ℂ, Zl.ScalarBy (x 1) (Zls.unifU k) c1 :=
  fun _ _ _ _ _ N _ _ _ π hs hi _ _ d hd _ _ μ w hw hμ => exists_constituent N π hs hi d hd μ w hw hμ

end Local

end GlobalTheory.CompanionTheory.JacExp

end
end

