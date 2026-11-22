import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaLift
import GroundTheory.PAdicHodge.ExtRobbaUnits
import GroundTheory.PAdicHodge.ExtRobbaNewton
import GroundTheory.PAdicHodge.ExtRobbaDMForward
import GroundTheory.PAdicHodge.SlopePhiModule

-- bundled from GroundTheory.PAdicHodge.ExtRobba
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ExtRobba

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (IsLocalRing.ResidueField (normInteger K)) p]
  [PerfectRing (IsLocalRing.ResidueField (normInteger K)) p]
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p]
variable (ι : IsLocalRing.ResidueField (normInteger K) →+* L) {ϖ : normInteger K}
  (hϖ : Irreducible ϖ) (hι : ∀ a, ‖ι a‖ ≤ 1)

abbrev EDagger : Subring (gammaTeichLift p ι hϖ hι).B := (gammaTeichLift p ι hϖ hι).Edag

abbrev RobbaR (ρ0 : Set.Ioo (0 : ℝ) 1) := (gammaTeichLift p ι hϖ hι).RobbaExt ρ0

abbrev RobbaTildeL := (gammaTeichLift p ι hϖ hι).RobbaTilde

example : IsDomain (RobbaTildeL p ι hϖ hι) := inferInstance

example (ρ0 : Set.Ioo (0 : ℝ) 1) : IsDomain (RobbaR p ι hϖ hι ρ0) := inferInstance

def frobenius (σ : K →+* K) (hσn : ∀ x, ‖σ x‖ = ‖x‖) (a : ℕ)
    (hσr : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ p ^ a‖ < 1) :
    RobbaTildeL p ι hϖ hι ≃+* RobbaTildeL p ι hϖ hι :=
  (gammaTeichFrob p σ hσn a hσr hϖ ι hι).tildeEquiv

end ExtRobba

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.ExtRobbaDMApprox
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

section Seq

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem convergesAt_of_weight_le {a : ℤ → K} {ρ σ Y : ℝ} (hσ0 : 0 < σ) (hσρ : σ < ρ)
    (hneg : ∃ N, ∀ n < N, a n = 0) (h : ∀ n, ‖a n‖ * ρ ^ n ≤ Y) : ConvergesAt a σ := by
  have hρ0 : 0 < ρ := hσ0.trans hσρ
  have hY : 0 ≤ Y := (mul_nonneg (norm_nonneg _) (zpow_pos hρ0 0).le).trans (h 0)
  have hsr0 : 0 ≤ σ / ρ := by positivity
  have hsr1 : σ / ρ < 1 := by rwa [div_lt_one hρ0]
  refine convergesAt_of_eventually hσ0 hneg fun ε hε => ?_
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (Y + 1) by positivity) hsr1
  refine ⟨M, fun n hn => ?_⟩
  lift n to ℕ using (by omega)
  have hn' : M ≤ n := by exact_mod_cast hn
  rw [zpow_natCast]
  calc ‖a n‖ * σ ^ n = (‖a n‖ * ρ ^ (n : ℤ)) * (σ / ρ) ^ n := by
        rw [div_pow, zpow_natCast]; field_simp
    _ ≤ Y * (σ / ρ) ^ M :=
        mul_le_mul (h n) (pow_le_pow_of_le_one hsr0 hsr1.le hn') (by positivity) hY
    _ ≤ (Y + 1) * (ε / (Y + 1)) := mul_le_mul (by linarith) hM.le (by positivity) (by linarith)
    _ = ε := by field_simp

end Seq

def fwdConst (q c : ℕ) (ρ : ℝ) : ℝ := ⨆ k : ℕ, ρ ^ (-((c * k : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ (q ^ k - 1)

theorem tendsto_fwdConst_terms {q : ℕ} (hq : 2 ≤ q) (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) :
    Tendsto (fun k : ℕ => ρ ^ (-((c * k : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ (q ^ k - 1)) atTop (𝓝 0) := by
  have := tendsto_mul_pow_pow_sub_one (A := (ρ ^ c)⁻¹) (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num) hq
  refine this.congr fun k => ?_
  rw [inv_pow, ← pow_mul, ← zpow_natCast, ← zpow_neg]

theorem le_fwdConst {q : ℕ} (hq : 2 ≤ q) (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (k : ℕ) :
    ρ ^ (-((c * k : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ (q ^ k - 1) ≤ fwdConst q c ρ :=
  le_ciSup (tendsto_fwdConst_terms hq c hρ0).bddAbove_range k

theorem fwdConst_nonneg {q : ℕ} (hq : 2 ≤ q) (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) :
    0 ≤ fwdConst q c ρ :=
  (by positivity : (0 : ℝ) ≤ ρ ^ (-((c * 0 : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ (q ^ 0 - 1)).trans
    (le_fwdConst hq c hρ0 0)

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem coeffB_invSelf_pow_mul (c : ℕ) (b : T.B) (n : ℤ) :
    T.coeffB (IsLocalization.Away.invSelf T.π ^ c * b) n = T.coeffB b (n + c) := by
  have h : (IsLocalization.Away.invSelf T.π ^ c * b) * algebraMap Γ T.B T.π ^ (T.den b + c) =
      algebraMap Γ T.B (T.num b) := by
    rw [pow_add, ← T.num_spec b]
    calc IsLocalization.Away.invSelf T.π ^ c * b *
          (algebraMap Γ T.B T.π ^ T.den b * algebraMap Γ T.B T.π ^ c)
        = b * algebraMap Γ T.B T.π ^ T.den b *
          (IsLocalization.Away.invSelf T.π ^ c * algebraMap Γ T.B T.π ^ c) := by ring
      _ = _ := by rw [T.invSelf_pow_mul_pow, mul_one]
  rw [T.coeffB_eq h, T.coeffB_eq (T.num_spec b)]
  simp only
  congr 1; push_cast; ring

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem gaussNorm_π_pow (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) :
    ConvergesAt (T.coeffB (algebraMap Γ T.B T.π ^ c)) ρ ∧
      gaussNorm (T.coeffB (algebraMap Γ T.B T.π ^ c)) ρ = ρ ^ c := by
  rw [← map_pow, T.coeffB_algebraMap, zcoeff_π_pow, gaussNorm_pi_single _ _ hρ0]
  exact ⟨convergesAt_pi_single _ _ _, by simp⟩

namespace TeichFrob

variable (F : T.TeichFrob)

theorem exists_approx_sol [IsAlgClosed L] (ha : 0 < F.a) (c : ℕ) {d : T.B}
    (hd : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB d) ρ) (K : ℕ) :
    ∃ t R : T.B, F.toB t - algebraMap Γ T.B T.π ^ c * t = d - R ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB t) ρ ∧
        gaussNorm (T.coeffB t) ρ ≤
          max 2 (fwdConst (p ^ F.a) c ρ * ρ ^ (-(c : ℤ))) * gaussNorm (T.coeffB d) ρ) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB R) ρ ∧
        gaussNorm (T.coeffB R) ρ ≤
          ρ ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) *
            gaussNorm (T.coeffB d) ρ) := by
  have hq := F.two_le_q ha
  have hθ0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hsd : T.smallPart (1 / 2) d + T.bigPart (1 / 2) d = d := T.smallPart_add_bigPart _ d
  obtain ⟨w, hwdef⟩ : ∃ w, IsLocalization.Away.invSelf T.π ^ c * T.smallPart (1 / 2) d = w :=
    ⟨_, rfl⟩
  have hw : ∀ n, ‖T.coeffB w n‖ ≤ 1 / 2 := fun n => by
    rw [← hwdef, T.coeffB_invSelf_pow_mul]; exact (T.norm_coeffB_smallPart_lt hθ0 d _).le
  have hπw : algebraMap Γ T.B T.π ^ c * w = T.smallPart (1 / 2) d := by
    rw [← hwdef, ← mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, one_mul]
  obtain ⟨z, hz, hzb⟩ := F.exists_sol_big ha c hθ0 (by norm_num)
    (T.coeffB_bigPart_eq_zero_or (1 / 2) d)
  refine ⟨z + F.fwdSum c w K, algebraMap Γ T.B T.π ^ c * (F.fwd c)^[K] w, ?_, ?_, ?_⟩
  · have h1 := F.toB_fwdSum_sub c w K
    rw [hπw] at h1
    rw [map_add, ← hsd]
    linear_combination hz + h1
  · intro ρ hρ0 hρ1
    have hdρ := hd ρ hρ0 hρ1
    obtain ⟨hbρ, hbρn⟩ := convergesAt_of_norm_le hρ0 (T.norm_coeffB_bigPart_le (1 / 2) d) hdρ
    obtain ⟨hsρ, hsρn⟩ := convergesAt_of_norm_le hρ0 (T.norm_coeffB_smallPart_le hθ0 d) hdρ

    obtain ⟨ρ', hρ'0, hρ'1, hρρ'⟩ : ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' < 1 ∧ ρ < ρ' :=
      ⟨(ρ + 1) / 2, by positivity, by linarith, by linarith⟩
    obtain ⟨hbρ', -⟩ := convergesAt_of_norm_le hρ'0 (T.norm_coeffB_bigPart_le (1 / 2) d)
      (hd ρ' hρ'0 hρ'1)
    have hzc : ConvergesAt (T.coeffB z) ρ :=
      convergesAt_of_weight_le hρ0 hρρ' (T.coeffB_neg_exists z) (hzb ρ' hρ'0 hρ'1 hbρ')
    have hzn : gaussNorm (T.coeffB z) ρ ≤ 2 * gaussNorm (T.coeffB d) ρ := by
      refine gaussNorm_le fun n => (hzb ρ hρ0 hρ1 hbρ n).trans ?_
      rw [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num]
      exact mul_le_mul_of_nonneg_left hbρn (by norm_num)

    obtain ⟨hi1, hi2⟩ := T.gaussNorm_invSelf_pow c hρ0
    obtain ⟨hwc, hwn⟩ := T.convergesAt_coeffB_mul hρ0 hρ1 hi1 hsρ
    rw [hwdef] at hwc hwn
    have hwd : gaussNorm (T.coeffB w) ρ ≤ ρ ^ (-(c : ℤ)) * gaussNorm (T.coeffB d) ρ := by
      rw [hwn, hi2]; exact mul_le_mul_of_nonneg_left hsρn (zpow_pos hρ0 _).le
    have hM : 0 ≤ fwdConst (p ^ F.a) c ρ * ρ ^ (-(c : ℤ)) * gaussNorm (T.coeffB d) ρ :=
      mul_nonneg (mul_nonneg (fwdConst_nonneg hq c hρ0) (zpow_pos hρ0 _).le) (gaussNorm_nonneg hρ0)
    obtain ⟨hSc, hSn⟩ := F.gaussNorm_fwdSum_sub_le c hθ0.le hw (Nat.zero_le K) hρ0 hρ1 hM
      fun k _ => by
        rw [mul_assoc (fwdConst _ _ _)]
        exact mul_le_mul (le_fwdConst hq c hρ0 k) hwd (gaussNorm_nonneg hρ0)
          (fwdConst_nonneg hq c hρ0)
    have e0 : F.fwdSum c w 0 = 0 := by simp [fwdSum]
    rw [e0, sub_zero] at hSc hSn
    obtain ⟨htc, htn⟩ := T.convergesAt_coeffB_add hρ0 hρ1 hzc hSc
    refine ⟨htc, htn.trans ?_⟩
    rw [max_mul_of_nonneg _ _ (gaussNorm_nonneg hρ0)]
    exact max_le_max hzn (by rw [mul_assoc] at hSn ⊢; exact hSn)
  · intro ρ hρ0 hρ1
    have hdρ := hd ρ hρ0 hρ1
    obtain ⟨hsρ, hsρn⟩ := convergesAt_of_norm_le hρ0 (T.norm_coeffB_smallPart_le hθ0 d) hdρ
    obtain ⟨hi1, hi2⟩ := T.gaussNorm_invSelf_pow c hρ0
    obtain ⟨-, hwn⟩ := T.convergesAt_coeffB_mul hρ0 hρ1 hi1 hsρ
    rw [hwdef] at hwn
    obtain ⟨hKc, hKn⟩ := F.gaussNorm_fwd_iterate_le c hθ0.le hw K hρ0 hρ1
    obtain ⟨hp1, hp2⟩ := gaussNorm_π_pow (T := T) c hρ0
    obtain ⟨hRc, hRn⟩ := T.convergesAt_coeffB_mul hρ0 hρ1 hp1 hKc
    refine ⟨hRc, ?_⟩
    rw [hRn, hp2]
    calc ρ ^ c * gaussNorm (T.coeffB ((F.fwd c)^[K] w)) ρ
        ≤ ρ ^ c * (ρ ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) *
            (ρ ^ (-(c : ℤ)) * gaussNorm (T.coeffB d) ρ)) := by
          refine mul_le_mul_of_nonneg_left (hKn.trans ?_) (pow_pos hρ0 c).le
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hwn, hi2]; exact mul_le_mul_of_nonneg_left hsρn (zpow_pos hρ0 _).le
      _ = ρ ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) *
            gaussNorm (T.coeffB d) ρ := by
          rw [← zpow_natCast ρ c]
          have : ρ ^ (c : ℤ) * ρ ^ (-(c : ℤ)) = 1 := by
            rw [← zpow_add₀ hρ0.ne', add_neg_cancel, zpow_zero]
          linear_combination (ρ ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) *
            gaussNorm (T.coeffB d) ρ) * this

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.ExtRobbaOrd
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def piB : T.Bˣ := (IsLocalization.Away.algebraMap_isUnit T.π).unit

theorem piB_val : (T.piB : T.B) = algebraMap Γ T.B T.π := IsUnit.unit_spec _

theorem exists_pi_pow_mul_red_ne {x : Γ} (hx : x ≠ 0) :
    ∃ (j : ℕ) (y : Γ), x = T.π ^ j * y ∧ T.red y ≠ 0 := by
  classical
  have hex : ∃ n, T.coeff x n ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx (T.eq_of_coeff_eq (funext fun n => by rw [h n, coeff_zero_elem]))
  set j := Nat.find hex
  have hj : T.coeff x j ≠ 0 := Nat.find_spec hex
  have hlt : ∀ i < j, T.coeff x i = 0 := fun i hi => by
    by_contra h; exact Nat.find_min hex hi h
  have hps : T.partialSum x j = 0 := by
    rw [partialSum, T.finSum_congr (b := 0) hlt]; simp [finSum]
  refine ⟨j, T.tail^[j] x, ?_, ?_⟩
  · have := T.sub_partialSum x j
    rwa [hps, sub_zero] at this
  · rw [← coeff_zero, coeff_tail_iterate, zero_add]; exact hj

theorem coeffB_piB_zpow_mul (k : ℤ) (y : Γ) (n : ℤ) :
    T.coeffB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) n = T.zcoeff y (n - k) := by
  rcases k with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, piB_val, ← map_pow,
      ← map_mul, coeffB_algebraMap]
    have := T.zcoeff_π_pow_mul m y (n - m)
    rwa [sub_add_cancel] at this
  · have hb : ((T.piB ^ Int.negSucc m : T.Bˣ) : T.B) * algebraMap Γ T.B y *
        algebraMap Γ T.B T.π ^ (m + 1) = algebraMap Γ T.B y := by
      rw [zpow_negSucc, ← piB_val, ← Units.val_pow_eq_pow_val, mul_comm, ← mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [T.coeffB_eq hb]
    congr 1

def ordB (b : T.B) : ℤ := sInf {n | T.coeffB b n ≠ 0}

theorem ordB_piB_zpow_mul (k : ℤ) {y : Γ} (hy : T.red y ≠ 0) :
    T.ordB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) = k := by
  have hS : ∀ n, n ∈ {n | T.coeffB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) n ≠ 0} ↔
      T.zcoeff y (n - k) ≠ 0 := fun n => by
    rw [Set.mem_ofPred_eq, coeffB_piB_zpow_mul]
  have hk : k ∈ {n | T.coeffB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) n ≠ 0} := by
    rw [hS, sub_self]
    rwa [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, zcoeff_natCast, coeff_zero]
  have hlow : ∀ n ∈ {n | T.coeffB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) n ≠ 0}, k ≤ n := by
    intro n hn
    rw [hS] at hn
    by_contra h
    exact hn (T.zcoeff_of_neg y (by omega))
  exact le_antisymm (csInf_le ⟨k, hlow⟩ hk) (le_csInf ⟨k, hk⟩ hlow)

theorem exists_piB_zpow_mul {b : T.B} (hb : b ≠ 0) :
    ∃ (k : ℤ) (y : Γ), b = (T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y ∧ T.red y ≠ 0 := by
  obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π b
  have hx0 : x ≠ 0 := by rintro rfl; exact hb (T.eq_zero_of_mul_pow (by rw [hx, map_zero]))
  obtain ⟨j, y, rfl, hy⟩ := T.exists_pi_pow_mul_red_ne hx0
  refine ⟨(j : ℤ) - N, y, ?_, hy⟩
  have hN : ((T.piB ^ (N : ℤ) : T.Bˣ) : T.B) = algebraMap Γ T.B T.π ^ N := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, piB_val]
  have hj : ((T.piB ^ (j : ℤ) : T.Bˣ) : T.B) = algebraMap Γ T.B T.π ^ j := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, piB_val]
  calc b = b * ((T.piB ^ (N : ℤ) : T.Bˣ) * (T.piB ^ (-(N : ℤ)) : T.Bˣ) : T.Bˣ) := by
        rw [← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, mul_one]
    _ = (b * algebraMap Γ T.B T.π ^ N) * (T.piB ^ (-(N : ℤ)) : T.Bˣ) := by
        rw [Units.val_mul, hN]; ring
    _ = _ := by
        rw [hx, map_mul, map_pow, ← hj, mul_comm, ← mul_assoc, ← Units.val_mul, ← zpow_add,
          neg_add_eq_sub]

theorem ordB_mul {b c : T.B} (hb : b ≠ 0) (hc : c ≠ 0) : T.ordB (b * c) = T.ordB b + T.ordB c := by
  obtain ⟨k, y, rfl, hy⟩ := T.exists_piB_zpow_mul hb
  obtain ⟨l, z, rfl, hz⟩ := T.exists_piB_zpow_mul hc
  have e : ((T.piB ^ k : T.Bˣ) : T.B) * algebraMap Γ T.B y * (((T.piB ^ l : T.Bˣ) : T.B) *
      algebraMap Γ T.B z) = ((T.piB ^ (k + l) : T.Bˣ) : T.B) * algebraMap Γ T.B (y * z) := by
    rw [zpow_add, Units.val_mul, map_mul]; ring
  rw [e, T.ordB_piB_zpow_mul _ hy, T.ordB_piB_zpow_mul _ hz,
    T.ordB_piB_zpow_mul _ (by rw [map_mul]; exact mul_ne_zero hy hz)]

namespace TeichFrob

variable {T} (F : T.TeichFrob)

theorem ordB_toB {b : T.B} (hb : b ≠ 0) : T.ordB (F.toB b) = T.ordB b := by
  obtain ⟨k, y, rfl, hy⟩ := T.exists_piB_zpow_mul hb
  obtain ⟨v, -, huv, -⟩ := F.exists_inv_u
  set uU : Γˣ := ⟨F.u, v, huv, by rw [mul_comm]; exact huv⟩
  have hpi : Units.map (F.toB : T.B →* T.B) T.piB =
      T.piB * Units.map (algebraMap Γ T.B : Γ →* T.B) uU := by
    ext
    simp only [Units.coe_map, Units.val_mul, MonoidHom.coe_coe]
    rw [piB_val]
    show F.toB (algebraMap Γ T.B T.π) = _
    rw [F.toB_algebraMap, F.φ_π, map_mul]
  have e : F.toB (((T.piB ^ k : T.Bˣ) : T.B) * algebraMap Γ T.B y) =
      ((T.piB ^ k : T.Bˣ) : T.B) * algebraMap Γ T.B (((uU ^ k : Γˣ) : Γ) * F.φ y) := by
    have h1 : F.toB (((T.piB ^ k : T.Bˣ) : T.B)) = ((T.piB ^ k : T.Bˣ) : T.B) *
        algebraMap Γ T.B ((uU ^ k : Γˣ) : Γ) := by
      have := congrArg Units.val (congrArg (· ^ k) hpi)
      simp only [← map_zpow, Units.coe_map, mul_zpow, Units.val_mul, MonoidHom.coe_coe] at this
      exact this
    rw [map_mul, h1, F.toB_algebraMap, map_mul]; ring
  have hu : T.red ((uU ^ k : Γˣ) : Γ) ≠ 0 := by
    have := (Units.map (T.red : Γ →* L) (uU ^ k)).ne_zero
    rwa [Units.coe_map, MonoidHom.coe_coe] at this
  rw [e, T.ordB_piB_zpow_mul _ hy, T.ordB_piB_zpow_mul _ (by
    rw [map_mul, F.red_φ]; exact mul_ne_zero hu (pow_ne_zero _ hy))]

end TeichFrob

variable [CompleteSpace L]

def unitPre (x : T.RobbaTildeˣ) : T.Edag := (T.mem_range_of_isUnit x.isUnit).choose

theorem unitPre_spec (x : T.RobbaTildeˣ) : T.edagToTilde (T.unitPre x) = x :=
  (T.mem_range_of_isUnit x.isUnit).choose_spec

theorem unitPre_ne_zero (x : T.RobbaTildeˣ) : ((T.unitPre x : T.Edag) : T.B) ≠ 0 := by
  intro h
  have h0 : T.unitPre x = 0 := Subtype.ext h
  have := T.unitPre_spec x
  rw [h0, map_zero] at this
  exact x.ne_zero this.symm

def tildeOrd (x : T.RobbaTildeˣ) : ℤ := T.ordB (T.unitPre x : T.Edag)

theorem tildeOrd_eq {x : T.RobbaTildeˣ} {b : T.Edag} (h : T.edagToTilde b = x) :
    T.tildeOrd x = T.ordB (b : T.B) := by
  have : T.unitPre x = b := T.edagToTilde_injective ((T.unitPre_spec x).trans h.symm)
  rw [tildeOrd, this]

theorem tildeOrd_mul (x y : T.RobbaTildeˣ) : T.tildeOrd (x * y) = T.tildeOrd x + T.tildeOrd y := by
  rw [T.tildeOrd_eq (b := T.unitPre x * T.unitPre y) (by
    rw [map_mul, T.unitPre_spec, T.unitPre_spec, Units.val_mul]), Subring.coe_mul]
  exact T.ordB_mul (T.unitPre_ne_zero x) (T.unitPre_ne_zero y)

namespace TeichFrob

variable {T} (F : T.TeichFrob)

theorem tildeOrd_map (x : T.RobbaTildeˣ) :
    T.tildeOrd (Units.map (F.tildeFrob : T.RobbaTilde →* T.RobbaTilde) x) = T.tildeOrd x := by
  rw [T.tildeOrd_eq (b := F.edagEquiv (T.unitPre x)) (by
    rw [← F.tildeFrob_edagToTilde, T.unitPre_spec]; rfl), F.edagEquiv_apply,
    F.ordB_toB (T.unitPre_ne_zero x)]
  rfl

def tildeUnitOrd : PhiModule.UnitOrd T.RobbaTilde F.tildeFrob where
  ord := T.tildeOrd
  map_mul := T.tildeOrd_mul
  map_phi := F.tildeOrd_map

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

