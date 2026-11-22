import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0183
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0448
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0192
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0140
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceNormGe

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmeticStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleLetterData_window_arithmetic : ∀ {k : Type} [Field k] {l n r : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] (Dt : TopData n r), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ i, ((Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i) ∧ (∀ u ∈ Dt.U i, ∀ y : ℤ, Dt.w i - Dt.sg l i - 2 ≤ y → y ≤ Dt.w i + Dt.t + 1 + Dt.sg l i → (u : k) ≠ (y : k)) ∧ (Dt.ty i = LType.G → (∀ u ∈ Dt.U i, ∀ y : ℤ, -(Dt.sg l i : ℤ) ≤ y → y ≤ 0 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, 0 ≤ y → y ≤ Dt.η i → (u : k) ≠ (y : k)) ∧ 1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i) ∧ (Dt.ty i = LType.Bd → (∀ u ∈ Dt.U i, ∀ y : ℤ, (Dt.h i : ℤ) ≤ y → y ≤ Dt.h i + Dt.sg l i + 1 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, (Dt.h i : ℤ) - Dt.η i ≤ y → y ≤ Dt.h i → (u : k) ≠ (y : k)) ∧ (Dt.t : ℤ) ≤ Dt.wst i ∧ Dt.wst i ≤ Dt.η i) := by
  first | exact @GlobalTheory.WindowArith.windows | exact GlobalTheory.WindowArith.windows | (intros; apply GlobalTheory.WindowArith.windows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproximatedTraceSystemLocallyCauchyStatement
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximatedTraceSystem_locally_cauchy : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ) (θ : J → PadicAlgCl l) (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∀ ε : ℝ, 0 < ε → ∀ g : Γ, ∃ V ∈ nhds g, ∀ i j, x i ∈ V → x j ∈ V → ‖θ i - θ j‖ ≤ ε := by
  first | exact @GlobalTheory.polyApprox_trc_locally_cauchy | exact GlobalTheory.polyApprox_trc_locally_cauchy | (intros; apply GlobalTheory.polyApprox_trc_locally_cauchy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExactTripleJumpsCharactersLift
section
noncomputable section

open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.ExactTripleBK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem smul_eq_of_retr {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : GlobalTheory.BK.Hom P Q) {n : ℕ}
    {τ : ZMod a} {Λ : Matrix ι κ K⟦X⟧} (h : Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧))
    (v : Vec K a ι) : (l : K) ^ n • v τ = Λ *ᵥ F.app v τ := by
  rw [Hom.app_apply, Matrix.mulVec_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem onPol_injective {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : GlobalTheory.BK.Hom P Q) (n : ℕ)
    (hΛ : ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧
      Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧)) :
    Function.Injective F.onPol := by
  refine (injective_iff_map_eq_zero F.onPol).2 fun w hw => ?_
  obtain ⟨v, rfl⟩ := P.Man.mkQ_surjective w
  have hv : F.app v ∈ Q.Man := Q.cls_eq_zero_iff.1 hw
  change P.cls v = 0
  rw [PhiMod.cls_eq_zero_iff]
  have h1 : (l : K) ^ n • v ∈ P.Man := by
    refine P.mem_Man.2 (mem_tot.2 fun τ i => ?_)
    obtain ⟨Λ, hΛA, hΛF⟩ := hΛ τ
    have hFv := mem_tot.1 (Q.mem_Man.1 hv) τ
    have h2 : ((l : K) ^ n • v) τ = Λ *ᵥ F.app v τ := by
      rw [Pi.smul_apply]
      exact smul_eq_of_retr F hΛF v
    rw [h2]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (A_le_Rpi l e (hΛA i k)) (hFv k)
  have h3 := P.Man.smul_mem ((l : K) ^ n)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (l_ne_zero l)), one_smul] at h3

omit [CompleteSpace K] in

theorem onD_actD {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P} {Δ₂ : Descent Q}
    (F : Descent.Hom Δ₁ Δ₂) (g : TameGal K l e a) (d : P.D) :
    F.onD (Δ₁.actD g d) = Δ₂.actD g (F.onD d) := by
  have h1 : Δ₁.actD g d = red (Δ₁.act g (cst d)) := rfl
  rw [h1, ← Hom.red_app, F.app_act, Δ₂.red_act, Hom.red_app, red_cst]

theorem map_constantCoeff_smul_one (c : K) :
    (c • (1 : Matrix ι ι K⟦X⟧)).map constantCoeff = c • (1 : Matrix ι ι K) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_smul]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem chars_subset {η H : ℕ} {D₀ : BKDat O K l e a ι η H} {D₁ : BKDat O K l e a κ η H}
    (F : BKHom D₀ D₁) (n : ℕ)
    (hΛ : ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧
      Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧)) (τ : ZMod a) :
    D₀.desc.chars τ ⊆ D₁.desc.chars τ := by
  rintro c ⟨d, hd, hc⟩
  refine ⟨F.onD d, fun h0 => hd ?_, fun ζ => ?_⟩
  · obtain ⟨Λ, -, hΛF⟩ := hΛ τ
    have h1 : Λ.map constantCoeff *ᵥ F.onD d τ = (l : K) ^ n • d τ := by
      rw [show F.onD d τ = (F.mat τ).map constantCoeff *ᵥ d τ from rfl, Matrix.mulVec_mulVec,
        ← Matrix.map_mul, hΛF, map_constantCoeff_smul_one, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (l_ne_zero l))
  · rw [← onD_actD]
    change (F.mat τ).map constantCoeff *ᵥ _ = _ • ((F.mat τ).map constantCoeff *ᵥ d τ)
    rw [hc ζ, Matrix.mulVec_smul]

theorem exists_Z_of_onPol_eq_zero {μ : Type} [Fintype μ] [DecidableEq μ] {η H : ℕ}
    {D₀ : BKDat O K l e a ι η H} {D₁ : BKDat O K l e a κ η H} {D₂ : BKDat O K l e a μ η H}
    (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (hex : IsExactTriple F.toHom G.toHom)
    (hinj : Function.Injective F.onPol) (n : ℕ)
    (hn : ∀ y ∈ D₂.M, ∃ x ∈ D₁.M, G.app x = (l : K) ^ n • y) {w : D₁.Pol} (hw : w ∈ D₁.Z)
    (hG : G.onPol w = 0) : ∃ w₀ ∈ D₀.Z, F.onPol w₀ = (l : K) ^ n • w := by
  obtain ⟨⟨y, hy, rfl⟩, hinv⟩ := D₁.desc.mem_Z.1 hw
  have hGy : G.app y ∈ D₂.M :=
    D₂.mem_M_of_mem_Man (G.app_mem_EM hy) (D₂.cls_eq_zero_iff.1 hG)
  obtain ⟨x, hx, hxy⟩ := hn _ hGy
  have hGz : G.app ((l : K) ^ n • y - x) = 0 := by
    rw [map_sub, LinearMap.map_smul_of_tower, hxy, sub_self]
  have hlM : ∀ {m : Vec K a κ}, m ∈ D₁.M → (l : K) ^ n • m ∈ D₁.M := fun hm => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hm _
  have hEz : E K l e ^ η • ((l : K) ^ n • y - x) ∈ D₁.M := by
    rw [smul_sub, smul_comm]
    refine sub_mem (hlM hy) ?_
    exact D₁.M.smul_mem (⟨E K l e ^ η, pow_mem (E_mem l e _) η⟩ : A O K) hx
  have hker : G.app (E K l e ^ η • ((l : K) ^ n • y - x)) = 0 := by rw [map_smul, hGz, smul_zero]
  obtain ⟨m₀, hm₀, hFm⟩ := Submodule.mem_map.1 ((hex.exact _ hEz).1 hker)
  have hFm' : F.app m₀ = E K l e ^ η • ((l : K) ^ n • y - x) := hFm
  have hFy : F.app (Ezpow K l e (-η) • m₀) = (l : K) ^ n • y - x := by
    rw [map_smul, hFm', smul_smul, mul_comm, E_pow_mul_Ezpow_neg, one_smul]
  have hy₀M : Ezpow K l e (-η) • m₀ ∈ D₀.EM η := by
    show E K l e ^ η • (Ezpow K l e (-η) • m₀) ∈ D₀.M
    rw [smul_smul, E_pow_mul_Ezpow_neg, one_smul]
    exact hm₀
  have hF : F.onPol (D₀.cls (Ezpow K l e (-η) • m₀)) = (l : K) ^ n • D₁.cls y := by
    rw [BK.Hom.onPol_cls, hFy, map_sub, map_smul, D₁.cls_eq_zero_iff.2 (D₁.M_le_Man hx), sub_zero]
  refine ⟨D₀.cls (Ezpow K l e (-η) • m₀), D₀.desc.mem_Z.2 ⟨⟨_, hy₀M, rfl⟩, fun g => hinj ?_⟩, hF⟩
  rw [F.onPol_act, hF, map_smul, hinv g]

end GlobalTheory.ExactTripleBK

open GlobalTheory.ExactTripleBK in

theorem GlobalTheory.exactTriple_jumps_chars_lift : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (D₂ : BKDat O K l e a μ η H) (F : BKHom D₀ D₁) (G : BKHom D₁ D₂), IsExactTriple F.toHom G.toHom → D₀.jumps ⊆ D₁.jumps ∧ (∀ τ, D₀.desc.chars τ ⊆ D₁.desc.chars τ) ∧ Function.Injective F.onPol ∧ (∀ n : ℕ, (∀ y ∈ D₂.M, ∃ x ∈ D₁.M, G.app x = (l : K) ^ n • y) → ∀ w ∈ D₁.Z, G.onPol w = 0 → ∃ w₀ ∈ D₀.Z, F.onPol w₀ = (l : K) ^ n • w) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ μ _ _ _ _ η H D₀ D₁ D₂ F G hex
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_prime_pow_smul_mem_range_of_finiteLength_coker O K l e a κ μ D₁.toPhiMod D₂.toPhiMod G.toHom hex.finiteLength
  have hΛ := GlobalTheory.T.exists_integral_leftInverse_of_phiModule_exactTriple O K l e a ι κ μ D₀.toPhiMod D₁.toPhiMod D₂.toPhiMod F.toHom G.toHom hex n hn
  have hinj := onPol_injective F.toHom n hΛ
  exact ⟨GlobalTheory.T.breuilKisin_jumps_subset_of_split_mono O K l e a ι κ η H D₀ D₁ F.toHom n hΛ, fun τ => chars_subset F n hΛ τ, hinj,
    fun m hm w hw hG => exists_Z_of_onPol_eq_zero F G hex hinj m hm hw hG⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIntegralityComputationStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_integrality_computation : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), η < H → 10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.IntegralityComputation D := by
  first | exact @GlobalTheory.IntegralityComp.integralityComputation | exact GlobalTheory.IntegralityComp.integralityComputation | (intros; apply GlobalTheory.IntegralityComp.integralityComputation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensor
section
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK

theorem norm_natCast_eq_rpow_padicValNat (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K]
    [NormedAlgebra ℚ_[l] K] (N : ℕ) (hN : N ≠ 0) :
    ‖(N : K)‖ = (l : ℝ) ^ (-(padicValNat l N : ℝ)) := by
  rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap',
    Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hN), Padic.valuation_natCast,
    ← Real.rpow_intCast]
  congr 1
  push_cast
  simp [padicValRat.of_nat]

theorem wS_le_rpow (K : Type) [NormedField K] [IsUltrametricDist K] (l e : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) :
    wS K e n ≤ (l : ℝ) ^ (1 / ((l : ℝ) - 1)) * ((n : ℝ) + 1) *
      (l : ℝ) ^ (-(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hq : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  set m := n / e with hmdef
  have hv := GlobalTheory.DetPowContent.padicValNat_factorial_ge l (Fact.out : l.Prime) m
  have hm : (n : ℝ) / e - 1 ≤ m := by
    have h1 : n < (m + 1) * e := by
      have := Nat.lt_div_mul_add (a := n) (Nat.pos_of_ne_zero (NeZero.ne e))
      rw [hmdef]; linarith
    have h2 : (n : ℝ) < ((m : ℝ) + 1) * e := by exact_mod_cast h1
    rw [div_sub_one he.ne', div_le_iff₀ he]; linarith
  have hm1 : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    have : m ≤ n := Nat.div_le_self n e
    exact_mod_cast Nat.add_le_add_right this 1
  unfold wS
  rw [← hmdef, norm_natCast_eq_rpow_padicValNat l K _ (Nat.factorial_ne_zero m)]
  have hexp : -(padicValNat l m.factorial : ℝ) ≤ Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) +
      -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) := by
    have h3 : (n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) = ((n : ℝ) / e) / ((l : ℝ) - 1) := by
      field_simp
    have h4 : ((n : ℝ) / e) / ((l : ℝ) - 1) ≤ (m : ℝ) / ((l : ℝ) - 1) + 1 / ((l : ℝ) - 1) := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hq.le
    nlinarith
  calc (l : ℝ) ^ (-(padicValNat l m.factorial : ℝ))
      ≤ (l : ℝ) ^ (Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) +
          -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := Real.rpow_le_rpow_of_exponent_le hl.le hexp
    _ = ((m : ℝ) + 1) * (l : ℝ) ^ (1 / ((l : ℝ) - 1)) *
          (l : ℝ) ^ (-(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := by
      rw [Real.rpow_add hl0, Real.rpow_add hl0, Real.rpow_logb hl0 hl.ne' (by positivity)]
    _ ≤ _ := by
      rw [mul_comm ((m : ℝ) + 1)]
      gcongr

end GlobalTheory.BK

open Matrix

namespace GlobalTheory.BK

theorem R_le_invL_S (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    (k : ℝ) (hk : k < 1 / ((e : ℝ) * (l - 1))) : R O K l k ≤ invL l (S O K e) := by
  intro f hf
  rw [mem_invL_S_iff_tendsto O K l e f]
  have hR := mem_R.1 hf
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  set k0 := 1 / ((e : ℝ) * (l - 1)) with hk0
  set q := (l : ℝ) ^ (k - k0) with hqdef
  have hq0 : 0 ≤ q := Real.rpow_nonneg hl0.le _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)
  set C := (l : ℝ) ^ (1 / ((l : ℝ) - 1)) with hC
  have hg : Tendsto (fun n : ℕ => C * (((n : ℝ) + 1) * q ^ n)) atTop (𝓝 0) := by
    have h1 := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    rw [add_zero] at h1
    have h2 := h1.const_mul C
    rw [mul_zero] at h2
    exact h2.congr fun n => by ring
  have hprod := hR.mul hg
  rw [zero_mul] at hprod
  refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) (fun n => ?_) hprod
  have hw := wS_le_rpow K l e n
  have hrad : rad l k ^ n * q ^ n = (l : ℝ) ^ (-(n : ℝ) * k0) := by
    rw [rad, hqdef, ← Real.rpow_mul_natCast hl0.le, ← Real.rpow_mul_natCast hl0.le,
      ← Real.rpow_add hl0]
    congr 1; ring
  calc ‖coeff n f‖ * wS K e n ≤ ‖coeff n f‖ * (C * ((n : ℝ) + 1) * (l : ℝ) ^ (-(n : ℝ) * k0)) :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = ‖coeff n f‖ * rad l k ^ n * (C * (((n : ℝ) + 1) * q ^ n)) := by
        rw [← hrad]; ring

theorem mulVec_mem_vecs {ι : Type} [Fintype ι] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    {B : Subalgebra O K⟦X⟧} {M : Matrix ι ι K⟦X⟧} (hM : ∀ i j, M i j ∈ B) {v : ι → K⟦X⟧}
    (hv : v ∈ vecs ι B) : M *ᵥ v ∈ vecs ι B := fun i =>
  Subalgebra.sum_mem _ fun j _ => B.mul_mem (hM i j) (hv j)

end GlobalTheory.BK

open GlobalTheory.BK in
theorem GlobalTheory.BK.xi_trivialises_invL_S : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι), (∀ k : ℝ, k < 1 / ((e : ℝ) * (l - 1)) → R O K l k ≤ invL l (S O K e)) ∧ ∀ w : Vec K a ι, P.xiExt w ∈ P.MMl ↔ w ∈ P.Mext (invL l (S O K e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P
  refine ⟨fun k hk => R_le_invL_S O K l e k hk, fun w => ?_⟩
  have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  set k : ℝ := (1 / ((e : ℝ) * l) + 1 / ((e : ℝ) * (l - 1))) / 2 with hkdef
  have hlt : 1 / ((e : ℝ) * l) < 1 / ((e : ℝ) * (l - 1)) :=
    one_div_lt_one_div_of_lt (by nlinarith) (by nlinarith)
  have hk1 : 1 / ((e : ℝ) * l) < k := by rw [hkdef]; linarith
  have hk2 : k < 1 / ((e : ℝ) * (l - 1)) := by rw [hkdef]; linarith
  have hRB := R_le_invL_S O K l e k hk2
  have hT := GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι P k hk1
  set Y : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => P.mxInv τ * P.xiMat τ with hY
  have hext : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι),
      P.xiExt v ∈ P.ext B ↔ ∀ τ, Y τ *ᵥ v τ ∈ vecs ι B := by
    intro B v
    simp only [PhiMod.ext, mem_tot, PhiMod.mem_extc_iff, PhiMod.xiExt_apply, Matrix.mulVec_mulVec, hY]
  have hM : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι), v ∈ P.Mext B ↔ ∀ τ, v τ ∈ vecs ι B := by
    intro B v
    simp only [PhiMod.Mext, mem_tot]
  have hYu : ∀ τ, IsUnit (Y τ).det := by
    intro τ
    rw [hY, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (P.mx_mul_mxInv τ)).mul (P.isUnit_det_xiMat τ)

  have hYR : ∀ τ i j, Y τ i j ∈ R O K l k := by
    intro τ i j
    have h0 : (fun _ : ZMod a => (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Mext (R O K l k) := by
      rw [hM]; intro τ' i'
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    have h1 := (hext _ _).1 ((hT _).2 h0) τ i
    simpa [Matrix.mulVec_single_one] using h1

  have hZR : ∀ τ i j, (Y τ)⁻¹ i j ∈ R O K l k := by
    intro τ i j
    have h0 : P.xiExt (fun τ' => (Y τ')⁻¹ *ᵥ (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Lk k := by
      rw [PhiMod.Lk, hext]; intro τ' i'
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hYu τ'), Matrix.one_mulVec, Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    have h1 := (hM _ _).1 ((hT _).1 h0) τ i
    simpa [Matrix.mulVec_single_one] using h1
  rw [PhiMod.MMl, hext, hM]
  constructor
  · intro h τ
    have := mulVec_mem_vecs (fun i j => hRB (hZR τ i j)) (h τ)
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hYu τ), Matrix.one_mulVec] at this
  · intro h τ
    exact mulVec_mem_vecs (fun i j => hRB (hYR τ i j)) (h τ)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqOfApply
section
noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen

namespace GlobalTheory.SenLines.Coords

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def zc (c : F⟦X⟧) (n : ℤ) : F := if 0 ≤ n then coeff n.toNat c else 0

theorem zc_nat (c : F⟦X⟧) (n : ℕ) : zc c n = coeff n c := by
  simp [zc]

theorem zc_neg (c : F⟦X⟧) {n : ℤ} (h : n < 0) : zc c n = 0 := by
  unfold zc
  rw [if_neg (not_le.mpr h)]

theorem zc_add (c c' : F⟦X⟧) (n : ℤ) : zc (c + c') n = zc c n + zc c' n := by
  unfold zc
  split_ifs <;> simp [map_add]

theorem zc_mul (f c : F⟦X⟧) (n : ℤ) (N : ℕ) (h : n < N) :
    zc (f * c) n = ∑ j ∈ Finset.range N, coeff j f * zc c (n - j) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [zc_neg _ hn]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [zc_neg _ (by omega), mul_zero]
  · lift n to ℕ using hn
    have hN : n < N := by exact_mod_cast h
    rw [zc_nat, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j c),
      ← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ N by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (n + 1) N) ?_, add_zero]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show ((n : ℤ) - (j : ℤ)) = ((n - j : ℕ) : ℤ) by omega, zc_nat]
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [zc_neg _ (by omega), mul_zero]

def lines {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c : Fin r → F⟦X⟧) : ℤ → M :=
  ∑ k, serLine (u k) (d k) (c k)

theorem lines_apply {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c : Fin r → F⟦X⟧) (m : ℤ) :
    lines u d c m = ∑ k, zc (c k) (m + u k) • d k := by
  unfold lines
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [serLine, zc]
  split_ifs <;> simp

theorem lines_add {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c c' : Fin r → F⟦X⟧) :
    lines u d (c + c') = lines u d c + lines u d c' := by
  funext m
  simp only [lines_apply, Pi.add_apply, zc_add, add_smul, Finset.sum_add_distrib]

theorem lines_zero {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) :
    lines u d (0 : Fin r → F⟦X⟧) = 0 := by
  funext m
  rw [lines_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : zc (0 : F⟦X⟧) (m + u k) = 0 := by
    unfold zc
    split_ifs <;> simp
  rw [Pi.zero_apply, this, zero_smul]

theorem lines_sum {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) {ι : Type} (s : Finset ι)
    (c : ι → Fin r → F⟦X⟧) : lines u d (∑ j ∈ s, c j) = ∑ j ∈ s, lines u d (c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, lines_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lines_add, ih]

theorem coeff_eq_of_apply {r : ℕ} (u : Fin r → ℤ) {d : Fin r → M} (hd : LinearIndependent F d)
    (c c' : Fin r → F⟦X⟧) (a : F) (m : ℤ) (h : lines u d c m = a • lines u d c' m) (k : Fin r) :
    zc (c k) (m + u k) = a * zc (c' k) (m + u k) := by
  rw [lines_apply, lines_apply, Finset.smul_sum] at h
  have h2 : ∑ k, (zc (c k) (m + u k) - a * zc (c' k) (m + u k)) • d k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
    rw [h, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hd _ h2 k)

theorem lines_injective {r : ℕ} (u : Fin r → ℤ) {d : Fin r → M} (hd : LinearIndependent F d) :
    Function.Injective (lines (F := F) u d) := by
  intro c c' h
  funext k
  ext n
  have := coeff_eq_of_apply u hd c c' 1 ((n : ℤ) - u k) (by rw [h, one_smul]) k
  rwa [sub_add_cancel, one_mul, zc_nat, zc_nat] at this

theorem serAct_lines {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (f : F⟦X⟧) (c : Fin r → F⟦X⟧) :
    serAct f (lines u d c) = lines u d (f • c) := by
  funext m
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k, m + u k < N := by
    refine ⟨(Finset.univ.sup fun k => (m + u k).toNat) + 1, fun k => ?_⟩
    have h1 : (m + u k).toNat ≤ Finset.univ.sup fun k => (m + u k).toNat :=
      Finset.le_sup (f := fun k => (m + u k).toNat) (Finset.mem_univ k)
    have h2 := Int.self_le_toNat (m + u k)
    push_cast
    omega
  have hsupp : (Function.support fun j : ℕ => coeff j f • lines u d c (m - j)) ⊆ ↑(Finset.range N) := by
    intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hjN
    apply hj
    rw [lines_apply, Finset.sum_eq_zero, smul_zero]
    intro k _
    rw [zc_neg _ (by have := hN k; omega), zero_smul]
  unfold serAct
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  simp_rw [lines_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [zc_mul f (c k) (m + u k) N (hN k), Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show m - (j : ℤ) + u k = m + u k - j by ring]

theorem exists_coords : ∀ {F M A N : Type} [Field F] [AddCommGroup M] [Module F M] [CommRing A] [AddCommGroup N] [Module A N] (lev : A → F⟦X⟧) (L : N →+ (ℤ → M)) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M), LinearIndependent F d → (∀ a x, L (a • x) = serAct (lev a) (L x)) → SpanIsLines L u d F → ∃ e : N →+ (Fin r → F⟦X⟧), (∀ a x, e (a • x) = lev a • e x) ∧ Submodule.span F⟦X⟧ (Set.range e) = ⊤ ∧ ∀ (χ : F) (x y : N), χ ≠ 0 → (∀ k : ℤ, L y k = χ ^ k • L x k) → ∀ k, e y k = C (χ ^ (-u k)) * rescale χ (e x k) := by
  intro F M A N _ _ _ _ _ _ lev L r u d hd hL hS
  have hex : ∀ x, ∃ c : Fin r → F⟦X⟧, L x = lines u d c := by
    intro x
    obtain ⟨c, hc⟩ := (hS (L x)).mp ⟨1, fun _ => x, fun _ => 1, by simp only [Fin.sum_univ_one, serAct_one]⟩
    exact ⟨c, hc⟩
  choose e he using hex
  have hinj := lines_injective (F := F) u hd
  have eadd : ∀ x y, e (x + y) = e x + e y := fun x y =>
    hinj (by rw [← he, lines_add, ← he, ← he, map_add])
  refine ⟨AddMonoidHom.mk' e eadd, ?_, ?_, ?_⟩
  · intro a x
    show e (a • x) = lev a • e x
    apply hinj
    rw [← he, hL, he x, serAct_lines]
  · rw [eq_top_iff]
    intro c _
    obtain ⟨s, x, f, hy⟩ := (hS (lines u d c)).mpr ⟨c, rfl⟩
    have hc : c = ∑ j, f j • e (x j) := by
      apply hinj
      rw [hy, lines_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [he, serAct_lines]
    rw [hc]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x j, rfl⟩)
  · intro χ x y hχ hxy k
    show e y k = C (χ ^ (-u k)) * rescale χ (e x k)
    ext n
    have h1 : lines u d (e y) ((n : ℤ) - u k) = χ ^ ((n : ℤ) - u k) • lines u d (e x) ((n : ℤ) - u k) := by
      rw [← he, ← he]
      exact hxy _
    have h2 := coeff_eq_of_apply u hd (e y) (e x) _ _ h1 k
    rw [sub_add_cancel, zc_nat, zc_nat] at h2
    rw [h2, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, zpow_sub₀ hχ, zpow_neg, zpow_natCast]
    ring

end GlobalTheory.SenLines.Coords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerTraceAlmostSurjective
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem trace_almost_onto (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)) (hKL : Kinf K ≤ L)
    (_hL : ∀ h ∈ Hinf K, ∀ x ∈ L, h x ∈ L) (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup)
    (a : Om l) (ha : a ∈ Kinf K) (ha1 : ‖a‖ < 1) :
    ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a :=
  AlmostTrace.trace_almost_onto_of_levels (GlobalTheory.Cyc.exists_trace_norm_ge l) K L S hKL hS hrep a ha ha1

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRepStatement
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep : ∀ (k Γ : Type) [Field k] [CharZero k] [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) k), IsSSRep r → ∀ M ∈ Submodule.span k (Set.range fun g => ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)), (∀ g, (M * ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).trace = 0) → M = 0 := by
  first | exact @GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero | exact GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero | (intros; apply GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero <;> assumption)
end

