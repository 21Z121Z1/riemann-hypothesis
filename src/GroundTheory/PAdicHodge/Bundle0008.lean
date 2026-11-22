import Mathlib
import GroundTheory.PAdicHodge.DMTeichBasic
import GroundTheory.PAdicHodge.Bundle0007
import GroundTheory.PAdicHodge.ExtRobbaEigenGlue
import GroundTheory.PAdicHodge.ExtRobbaLimit

-- bundled from GroundTheory.PAdicHodge.ExtRobbaFixedTerm
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

abbrev πB : T.B := algebraMap Γ T.B T.π

theorem πB_ne_zero : T.πB ≠ 0 := by
  have := T.nontrivial_B
  exact (IsLocalization.Away.algebraMap_isUnit T.π).ne_zero

def DigLe (x : Γ) (Θ : ℝ) : Prop := ∀ n, ‖T.coeff x n‖ ≤ Θ

def IsUnitTerm (P : T.B) (i : ℤ) : Prop :=
  ∃ U ∈ T.int, ‖T.red U‖ = 1 ∧ P = T.πB ^ i * algebraMap Γ T.B U

variable {T}

theorem digLe_iff_prefixLe {x : Γ} {Θ : ℝ} : T.DigLe x Θ ↔ ∀ n, T.PrefixLe x n Θ :=
  ⟨fun h _ m _ => h m, fun h n => h n n le_rfl⟩

theorem DigLe.mono {x : Γ} {Θ Θ' : ℝ} (h : T.DigLe x Θ) (hΘ : Θ ≤ Θ') : T.DigLe x Θ' :=
  fun n => (h n).trans hΘ

theorem DigLe.add {x y : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) (hy : T.DigLe y Θ) : T.DigLe (x + y) Θ :=
  digLe_iff_prefixLe.2 fun n =>
    T.prefixLe_add (digLe_iff_prefixLe.1 hx n) (digLe_iff_prefixLe.1 hy n)

theorem digLe_teich {a : L} {Θ : ℝ} (h : ‖a‖ ≤ Θ) : T.DigLe (T.teich a) Θ := fun n => by
  rw [T.coeff_teich]
  split_ifs
  · exact h
  · simpa using (norm_nonneg a).trans h

theorem digLe_π_mul_iff {x : Γ} {Θ : ℝ} (hΘ : 0 ≤ Θ) : T.DigLe (T.π * x) Θ ↔ T.DigLe x Θ := by
  constructor
  · intro h n; rw [← T.coeff_π_mul_succ]; exact h (n + 1)
  · intro h n
    cases n with
    | zero => rw [T.coeff_zero, map_mul, T.red_π, zero_mul, norm_zero]; exact hΘ
    | succ n => rw [T.coeff_π_mul_succ]; exact h n

theorem digLe_one_of_mem_int {x : Γ} (hx : x ∈ T.int) : T.DigLe x 1 := T.mem_int_iff.1 hx

theorem DigLe.convergesAt {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ConvergesAt (T.zcoeff x) r :=
  T.convergesAt_of_forall_weight_le (ρ := 1) (Y := Θ) hr0 hr1 fun n => by
    rw [one_pow, mul_one]; exact hx n

theorem DigLe.gaussNorm_le {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) (hΘ : 0 ≤ Θ) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) : gaussNorm (T.zcoeff x) r ≤ Θ :=
  ciSup_le fun j => T.zcoeff_weight_le hΘ (fun n =>
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hr0.le hr1.le)).trans (hx n)) j

theorem DigLe.convAll {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) : T.ConvAll (algebraMap Γ T.B x) :=
  fun _ hr0 hr1 => by rw [T.coeffB_algebraMap]; exact hx.convergesAt hr0 hr1

theorem convAll_πB_zpow (i : ℤ) : T.ConvAll (T.πB ^ i) := by
  have hinv : (T.πB)⁻¹ = IsLocalization.Away.invSelf T.π :=
    inv_eq_of_mul_eq_one_right (IsLocalization.Away.mul_invSelf T.π)
  have hc : T.ConvAll (IsLocalization.Away.invSelf T.π) := fun ρ _ _ => by
    rw [T.coeffB_invSelf]; exact convergesAt_pi_single _ _ _
  have hpow : ∀ n : ℕ, T.ConvAll ((IsLocalization.Away.invSelf T.π) ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero]
      simpa using (convAll_π_pow (T := T) 0)
    | succ n ih => rw [pow_succ]; exact ih.mul hc
  rcases i with n | n
  · simpa [zpow_natCast] using (convAll_π_pow (T := T) n)
  · rw [zpow_negSucc, ← inv_pow, hinv]; exact hpow _

theorem convAll_algebraMap_of_mem_int {U : Γ} (hU : U ∈ T.int) :
    T.ConvAll (algebraMap Γ T.B U) := (digLe_one_of_mem_int hU).convAll

theorem coeffB_πB_zpow_mul (i : ℤ) (x : Γ) :
    T.coeffB (T.πB ^ i * algebraMap Γ T.B x) = fun k => T.zcoeff x (k - i) := by
  set N := (-i).toNat
  set M := i.toNat
  have hNM : i + (N : ℤ) = M := by have := Int.toNat_sub_toNat_neg i; omega
  have h : T.πB ^ i * algebraMap Γ T.B x * algebraMap Γ T.B T.π ^ N =
      algebraMap Γ T.B (T.π ^ M * x) := by
    rw [map_mul, map_pow, mul_right_comm, ← zpow_natCast, ← zpow_add₀ T.πB_ne_zero, hNM,
      zpow_natCast]
  rw [T.coeffB_eq h]
  funext k
  have := T.zcoeff_π_pow_mul M x (k - i)
  rw [show k - i + (M : ℤ) = k + (N : ℤ) by omega] at this
  exact this

theorem isUnitTerm_one : T.IsUnitTerm 1 0 :=
  ⟨1, T.int.one_mem, by simp, by simp⟩

theorem isUnitTerm_πB_zpow (i : ℤ) : T.IsUnitTerm (T.πB ^ i) i :=
  ⟨1, T.int.one_mem, by simp, by simp⟩

theorem isUnitTerm_algebraMap {U : Γ} (hU : U ∈ T.int) (h1 : ‖T.red U‖ = 1) :
    T.IsUnitTerm (algebraMap Γ T.B U) 0 :=
  ⟨U, hU, h1, by simp⟩

theorem IsUnitTerm.congr_idx {P : T.B} {i j : ℤ} (h : T.IsUnitTerm P i) (hij : i = j) :
    T.IsUnitTerm P j := hij ▸ h

theorem IsUnitTerm.mul {P P' : T.B} {i i' : ℤ} (h : T.IsUnitTerm P i) (h' : T.IsUnitTerm P' i') :
    T.IsUnitTerm (P * P') (i + i') := by
  obtain ⟨U, hU, hU1, rfl⟩ := h
  obtain ⟨U', hU', hU1', rfl⟩ := h'
  refine ⟨U * U', T.int.mul_mem hU hU', by rw [map_mul, norm_mul, hU1, hU1', one_mul], ?_⟩
  rw [zpow_add₀ T.πB_ne_zero, map_mul]; ring

theorem IsUnitTerm.inv {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) : T.IsUnitTerm P⁻¹ (-i) := by
  obtain ⟨U, hU, hU1, rfl⟩ := h
  obtain ⟨V, hV, hUV⟩ := T.exists_inv_mem_int hU hU1
  have hV1 : ‖T.red V‖ = 1 := by
    have := congrArg (fun y => ‖T.red y‖) hUV
    simpa [map_mul, norm_mul, hU1] using this
  refine ⟨V, hV, hV1, ?_⟩
  have hUVB : algebraMap Γ T.B U * algebraMap Γ T.B V = 1 := by rw [← map_mul, hUV, map_one]
  rw [mul_inv, zpow_neg, inv_eq_of_mul_eq_one_right hUVB]

theorem IsUnitTerm.ne_zero {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) : P ≠ 0 := by
  intro h0
  obtain ⟨U, hU, hU1, hP⟩ := h.inv
  rw [h0, inv_zero] at hP
  have hU0 : algebraMap Γ T.B U = 0 := by
    rcases mul_eq_zero.1 hP.symm with h1 | h1
    · exact absurd h1 (zpow_ne_zero _ T.πB_ne_zero)
    · exact h1
  have : U = 0 := T.algebraMap_injective (by rw [hU0, map_zero])
  rw [this, map_zero, norm_zero] at hU1
  exact zero_ne_one hU1

theorem IsUnitTerm.zpow {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) (k : ℤ) :
    T.IsUnitTerm (P ^ k) (k * i) := by
  induction k using Int.induction_on with
  | zero => rw [zpow_zero]; exact isUnitTerm_one.congr_idx (by ring)
  | succ k ih => rw [zpow_add_one₀ h.ne_zero]; exact (ih.mul h).congr_idx (by ring)
  | pred k ih =>
    rw [zpow_sub_one₀ h.ne_zero]; exact (ih.mul h.inv).congr_idx (by ring)

theorem IsUnitTerm.convAll {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) : T.ConvAll P := by
  obtain ⟨U, hU, -, rfl⟩ := h
  exact (convAll_πB_zpow i).mul (convAll_algebraMap_of_mem_int hU)

theorem gaussNorm_single_zero (c : L) (r : ℝ) :
    gaussNorm (Pi.single 0 c) r = ‖c‖ := by
  refine le_antisymm (ciSup_le fun n => ?_) ?_
  · by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  · calc ‖c‖ = ‖(Pi.single (0 : ℤ) c : ℤ → L) 0‖ * r ^ (0 : ℤ) := by simp
      _ ≤ gaussNorm (Pi.single 0 c) r :=
        le_ciSup (f := fun n : ℤ => ‖(Pi.single (0 : ℤ) c : ℤ → L) n‖ * r ^ n)
          (convergesAt_pi_single (0 : ℤ) c r).bddAbove 0

theorem IsUnitTerm.gaussNorm_mul_teich {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) (a : L) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    gaussNorm (T.coeffB (P * algebraMap Γ T.B (T.teich a))) r = r ^ i * ‖a‖ := by
  obtain ⟨U, hU, hU1, rfl⟩ := h
  rw [mul_assoc, ← map_mul, coeffB_πB_zpow_mul]
  have e : (fun k => T.zcoeff (U * T.teich a) (k - i)) =
      fun k => T.zcoeff (U * T.teich a) (k + -i) := by funext k; rw [sub_eq_add_neg]
  rw [e, gaussNorm_shift hr0, neg_neg,
    T.gaussNorm_zcoeff_mul hr0 hr1 (T.convergesAt_of_mem_int hU hr0 hr1)
      ((digLe_teich (T := T) (le_refl ‖a‖)).convergesAt hr0 hr1),
    T.gaussNorm_eq_one_of_mem_int hU hU1 hr0 hr1, T.zcoeff_teich, gaussNorm_single_zero a r]
  ring

namespace TeichFrob

variable (F : T.TeichFrob)

def frobPow (k : ℤ) (a : L) : L := ((iterateFrobeniusEquiv L p F.a : RingAut L) ^ k) a

theorem IsUnitTerm.toB {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) : T.IsUnitTerm (F.toB P) i := by
  obtain ⟨U, hU, hU1, rfl⟩ := h
  have hπt : T.IsUnitTerm (F.toB T.πB) 1 := by
    have h1 := (isUnitTerm_πB_zpow (T := T) 1).mul (isUnitTerm_algebraMap F.u_mem_int F.norm_red_u)
    rw [zpow_one, add_zero] at h1
    rw [F.toB_algebraMap, F.φ_π, map_mul]
    exact h1
  have hUt : T.IsUnitTerm (F.toB (algebraMap Γ T.B U)) 0 := by
    rw [F.toB_algebraMap]
    refine isUnitTerm_algebraMap (F.map_int U hU) ?_
    rw [F.red_φ, norm_pow, hU1, one_pow]
  rw [map_mul, map_zpow₀]
  exact ((hπt.zpow i).mul hUt).congr_idx (by ring)

def twist (t : T.B) (ht : t ≠ 0) : AddAut T.B where
  toFun b := t * F.toB b
  invFun b := F.toB.symm (t⁻¹ * b)
  left_inv b := by simp [ht]
  right_inv b := by simp [ht]
  map_add' b c := by simp [mul_add]

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.SlopeDescentBounded
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem upperPart_eq_algebraMap (b : T.B) : ∃ w : Γ, T.upperPart b = algebraMap Γ T.B w := by
  obtain ⟨w, hw⟩ := T.mem_span_pow.1 (T.sub_partialSum_mem (T.num b) (T.den b))
  refine ⟨w, ?_⟩
  rw [upperPart, hw, map_mul, map_pow]
  calc algebraMap Γ T.B T.π ^ T.den b * algebraMap Γ T.B w * IsLocalization.Away.invSelf T.π ^ T.den b
      = algebraMap Γ T.B w * (algebraMap Γ T.B T.π * IsLocalization.Away.invSelf T.π) ^ T.den b := by
        ring
    _ = algebraMap Γ T.B w := by rw [IsLocalization.Away.mul_invSelf, one_pow, mul_one]

variable {T}

theorem gaussNorm_lowerPart_le_mul {b : T.B} (hb : T.ConvAll b) {r r' : ℝ} (h0 : 0 < r')
    (hle : r' ≤ r) (h1 : r' < 1) :
    gaussNorm (T.coeffB (T.lowerPart b)) r ≤ (r' / r) * gaussNorm (T.coeffB b) r' := by
  have hr0 : 0 < r := h0.trans_le hle
  refine gaussNorm_le fun n => ?_
  rw [coeffB_lowerPart]
  split_ifs with hn
  · have hq : 1 ≤ r / r' := (one_le_div h0).2 hle
    have hpow : (r / r') ^ n ≤ (r / r') ^ (-1 : ℤ) := zpow_le_zpow_right₀ hq (by omega)
    rw [zpow_neg_one, inv_div] at hpow
    have h3 : r ^ n ≤ (r' / r) * r' ^ n := by
      calc r ^ n = (r / r') ^ n * r' ^ n := by
            rw [div_zpow, div_mul_cancel₀ _ (zpow_pos h0 n).ne']
        _ ≤ (r' / r) * r' ^ n := mul_le_mul_of_nonneg_right hpow (zpow_pos h0 n).le
    calc ‖T.coeffB b n‖ * r ^ n ≤ ‖T.coeffB b n‖ * ((r' / r) * r' ^ n) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = (r' / r) * (‖T.coeffB b n‖ * r' ^ n) := by ring
      _ ≤ (r' / r) * gaussNorm (T.coeffB b) r' :=
          mul_le_mul_of_nonneg_left ((hb r' h0 h1).le_gaussNorm n) (by positivity)
  · rw [norm_zero, zero_mul]; exact mul_nonneg (by positivity) (gaussNorm_nonneg h0)

theorem exists_rpow_small {σ γ C η : ℝ} (hσ : 0 < σ) (hγ : 0 < γ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ t, 0 < t ∧ t ≤ σ ∧ C * t ^ γ ≤ η := by
  set a : ℝ := η / (C + 1) with ha
  have ha0 : 0 < a := by positivity
  refine ⟨min σ (a ^ γ⁻¹), lt_min hσ (Real.rpow_pos_of_pos ha0 _), min_le_left _ _, ?_⟩
  have ht0 : 0 ≤ min σ (a ^ γ⁻¹) := (lt_min hσ (Real.rpow_pos_of_pos ha0 _)).le
  have h1 : (min σ (a ^ γ⁻¹)) ^ γ ≤ a := by
    calc (min σ (a ^ γ⁻¹)) ^ γ ≤ (a ^ γ⁻¹) ^ γ :=
          Real.rpow_le_rpow ht0 (min_le_right _ _) hγ.le
      _ = a := Real.rpow_inv_rpow ha0.le hγ.ne'
  calc C * (min σ (a ^ γ⁻¹)) ^ γ ≤ C * a := mul_le_mul_of_nonneg_left h1 hC
    _ ≤ (C + 1) * a := by nlinarith
    _ = η := by rw [ha]; field_simp

theorem exists_gamma_of_extNorm_le [CompleteSpace L] {σ : Set.Ioo (0 : ℝ) 1} (x : T.RobbaExt σ) {C β : ℝ} (b : ℕ)
    (hb : β - 1 < b) (hx : ∀ s : Set.Ioc (0 : ℝ) σ, T.extNorm σ s x ≤ C * (s : ℝ) ^ (-β)) :
    ∃ w : Γ, ∃ hw : algebraMap Γ T.B w ∈ T.Econ σ,
      T.ofAll _ (convAll_π_pow b) σ * x = ((⟨algebraMap Γ T.B w, hw⟩ : T.Econ σ) : T.RobbaExt σ) := by
  have hσ0 : (0 : ℝ) < σ := σ.2.1
  have hσ1 : (σ : ℝ) < 1 := σ.2.2
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set y := T.ofAll _ (convAll_π_pow b) σ * x with hydef

  have hy : ∀ s : Set.Ioc (0 : ℝ) σ, T.extNorm σ s y ≤ C' * (s : ℝ) ^ ((b : ℝ) - β) := by
    intro s
    have hs0 : (0 : ℝ) < s := s.2.1
    rw [hydef, extNorm_mul, extNorm_ofAll, (gaussNorm_π_pow b hs0).2]
    have hxs : T.extNorm σ s x ≤ C' * (s : ℝ) ^ (-β) :=
      (hx s).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hs0.le _))
    calc (s : ℝ) ^ b * T.extNorm σ s x ≤ (s : ℝ) ^ b * (C' * (s : ℝ) ^ (-β)) :=
          mul_le_mul_of_nonneg_left hxs (pow_nonneg hs0.le _)
      _ = C' * ((s : ℝ) ^ (b : ℝ) * (s : ℝ) ^ (-β)) := by rw [Real.rpow_natCast]; ring
      _ = C' * (s : ℝ) ^ ((b : ℝ) - β) := by rw [← Real.rpow_add hs0, sub_eq_add_neg]

  let r : ℕ → Set.Ioc (0 : ℝ) σ := fun j =>
    ⟨σ / (j + 1), by positivity, div_le_self hσ0.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])⟩
  let ε : ℕ → ℝ := fun j => 1 / (j + 1)
  have hε0 : ∀ j, 0 < ε j := fun j => by positivity
  choose d hd hdx using fun j : ℕ => exists_approx_convAll y (r j) (hε0 j)
  choose w hw using fun j => T.upperPart_eq_algebraMap (d j)
  have hr_anti : ∀ {j k : ℕ}, j ≤ k → ((r k : ℝ)) ≤ r j := fun {j k} hjk => by
    show σ / ((k : ℝ) + 1) ≤ σ / ((j : ℝ) + 1)
    exact div_le_div_of_nonneg_left hσ0.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hε_anti : ∀ {j k : ℕ}, j ≤ k → ε k ≤ ε j := fun {j k} hjk => by
    show 1 / ((k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1)
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hsmall : ∀ η > (0 : ℝ), ∀ t > (0 : ℝ), ∃ J, ∀ j ≥ J, (r j : ℝ) ≤ t ∧ ε j ≤ η := by
    intro η hη t ht
    obtain ⟨J, hJ⟩ := exists_nat_gt (max (σ / t) (1 / η))
    refine ⟨J, fun j hj => ⟨?_, ?_⟩⟩
    · refine (hr_anti hj).trans ?_
      show σ / ((J : ℝ) + 1) ≤ t
      rw [div_le_iff₀ (by positivity)]
      have : σ / t < J := lt_of_le_of_lt (le_max_left _ _) hJ
      rw [div_lt_iff₀ ht] at this
      nlinarith
    · refine (hε_anti hj).trans ?_
      show 1 / ((J : ℝ) + 1) ≤ η
      rw [div_le_iff₀ (by positivity)]
      have : 1 / η < J := lt_of_le_of_lt (le_max_right _ _) hJ
      rw [div_lt_iff₀ hη] at this
      nlinarith

  have hdt : ∀ j (t : Set.Ioc (0 : ℝ) σ), (r j : ℝ) ≤ t →
      gaussNorm (T.coeffB (d j)) t ≤ max (C' * (t : ℝ) ^ ((b : ℝ) - β)) (ε j) := by
    intro j t ht
    rw [← extNorm_ofAll (hd j) t]
    have e : T.ofAll (d j) (hd j) σ = y + -(y - T.ofAll (d j) (hd j) σ) := by ring
    rw [e]
    refine (T.extNorm_add_le t _ _).trans (max_le_max (hy t) ?_)
    rw [extNorm_neg]; exact hdx j t ht

  have hA : ∀ η > (0 : ℝ), ∃ J, ∀ j ≥ J, gaussNorm (T.coeffB (T.lowerPart (d j))) σ ≤ η := by
    intro η hη
    have hγ : 0 < (b : ℝ) - β + 1 := by linarith
    obtain ⟨t, ht0, htσ, htC⟩ := exists_rpow_small hσ0 hγ (div_nonneg hC'0 hσ0.le) hη
    obtain ⟨J, hJ⟩ := hsmall η hη t ht0
    refine ⟨J, fun j hj => ?_⟩
    obtain ⟨hrj, hεj⟩ := hJ j hj
    have h1 := gaussNorm_lowerPart_le_mul (hd j) ht0 htσ (htσ.trans_lt hσ1)
    have h2 := hdt j ⟨t, ht0, htσ⟩ hrj
    refine h1.trans ?_
    have htσ' : t / σ ≤ 1 := (div_le_one hσ0).2 htσ
    calc t / σ * gaussNorm (T.coeffB (d j)) t
        ≤ t / σ * max (C' * t ^ ((b : ℝ) - β)) (ε j) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ max (C' / σ * t ^ ((b : ℝ) - β + 1)) (ε j) := by
          rw [mul_max_of_nonneg _ _ (by positivity)]
          refine max_le_max (le_of_eq ?_) ?_
          · rw [Real.rpow_add ht0, Real.rpow_one]; field_simp
          · calc t / σ * ε j ≤ 1 * ε j := mul_le_mul_of_nonneg_right htσ' (hε0 j).le
              _ = ε j := one_mul _
      _ ≤ η := max_le htC hεj

  have hup : ∀ j, T.ConvAll (algebraMap Γ T.B (w j)) := fun j => by
    rw [← hw j]; exact (hd j).upperPart
  have hconv : ∀ j, ConvergesAt (T.zcoeff (w j)) σ := fun j => by
    have := hup j σ hσ0 hσ1
    rwa [coeffB_algebraMap] at this
  have hsplit : ∀ j, T.ofAll (d j) (hd j) σ =
      T.ofAll _ (hd j).lowerPart σ + T.ofAll _ (hup j) σ := by
    intro j
    rw [← ofAll_add]
    exact ofAll_congr _ _ (by rw [← hw j, lowerPart_add_upperPart]) σ
  have hwsub : ∀ j k, gaussNorm (T.zcoeff (w j - w k)) σ =
      T.extNorm σ (topRad σ) (T.ofAll _ (hup j) σ - T.ofAll _ (hup k) σ) := by
    intro j k
    rw [← gaussNorm_ofAll_sub (hup j) (hup k), ← map_sub, coeffB_algebraMap]
    rfl

  have hB : ∀ η > (0 : ℝ), ∃ N, ∀ j ≥ N, ∀ k ≥ N, gaussNorm (T.zcoeff (w j - w k)) σ ≤ η := by
    intro η hη
    obtain ⟨J1, hJ1⟩ := hA η hη
    obtain ⟨J2, hJ2⟩ := hsmall η hη σ hσ0
    refine ⟨max J1 J2, fun j hj k hk => ?_⟩
    rw [hwsub]
    have e : T.ofAll _ (hup j) σ - T.ofAll _ (hup k) σ =
        -(y - T.ofAll (d j) (hd j) σ) + (y - T.ofAll (d k) (hd k) σ) +
          (T.ofAll _ (hd k).lowerPart σ - T.ofAll _ (hd j).lowerPart σ) := by
      rw [hsplit j, hsplit k]; ring
    rw [e]
    have hlow : ∀ i ≥ J1, T.extNorm σ (topRad σ) (T.ofAll _ (hd i).lowerPart σ) ≤ η := fun i hi => by
      rw [extNorm_ofAll]; exact hJ1 i hi
    have happ : ∀ i ≥ J2, T.extNorm σ (topRad σ) (y - T.ofAll (d i) (hd i) σ) ≤ η := fun i hi =>
      (hdx i (topRad σ) (hJ2 i hi).1).trans (hJ2 i hi).2
    refine (extNorm_add_add_le_max _ _ _ _).trans (max_le ?_ (max_le ?_ ?_))
    · rw [extNorm_neg]; exact happ j (le_of_max_le_right hj)
    · exact happ k (le_of_max_le_right hk)
    · rw [sub_eq_add_neg]
      refine (T.extNorm_add_le _ _ _).trans (max_le (hlow k (le_of_max_le_left hk)) ?_)
      rw [extNorm_neg]; exact hlow j (le_of_max_le_left hj)

  obtain ⟨-, hWc, hWlim⟩ := T.exists_limit_gaussNorm hσ0 hσ1 hconv hB
  set W := T.coeffLim w with hWdef
  have hWE : algebraMap Γ T.B W ∈ T.Econ σ := by
    rw [mem_Econ, coeffB_algebraMap]; exact hWc
  refine ⟨W, hWE, ?_⟩

  rw [← sub_eq_zero, ← T.extNorm_eq_zero_iff (topRad σ)]
  refine le_antisymm (le_of_forall_pos_le_add fun η hη => ?_) (T.extNorm_nonneg _ _)
  rw [zero_add]
  obtain ⟨J1, hJ1⟩ := hA η hη
  obtain ⟨J2, hJ2⟩ := hsmall η hη σ hσ0
  obtain ⟨J3, hJ3⟩ := hWlim η hη
  set j := max J1 (max J2 J3)
  have e : y - ((⟨algebraMap Γ T.B W, hWE⟩ : T.Econ σ) : T.RobbaExt σ) =
      (y - T.ofAll (d j) (hd j) σ) + T.ofAll _ (hd j).lowerPart σ +
        (T.ofAll _ (hup j) σ - ((⟨algebraMap Γ T.B W, hWE⟩ : T.Econ σ) : T.RobbaExt σ)) := by
    rw [hsplit j]; ring
  rw [e]
  refine (extNorm_add_add_le_max _ _ _ _).trans (max_le ?_ (max_le ?_ ?_))
  · exact (hdx j (topRad σ) (hJ2 j (le_max_of_le_right (le_max_left _ _))).1).trans
      (hJ2 j (le_max_of_le_right (le_max_left _ _))).2
  · rw [extNorm_ofAll]; exact hJ1 j (le_max_left _ _)
  · rw [ofAll, ← Completion.coe_sub, extNorm_coe]
    have := hJ3 j (le_max_of_le_right (le_max_right _ _))
    rw [← coeffB_algebraMap, map_sub] at this
    exact this

end TeichLift

end GroundTheory.PAdicHodge
end
end

