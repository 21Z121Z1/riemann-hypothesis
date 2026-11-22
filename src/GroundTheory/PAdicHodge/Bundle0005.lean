import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMRankOne
import GroundTheory.PAdicHodge.NormalizedTraceTower
import GroundTheory.PAdicHodge.NormalizedTraceClosure
import GroundTheory.PAdicHodge.CyclotomicTower

-- bundled from GroundTheory.PAdicHodge.ExtRobbaDMLinear
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob)

theorem linStep_mem {α γ y x : Γ} {n : ℕ}
    (hx : α * F.φ x - γ * x - y ∈ Ideal.span {T.π ^ n}) {t : L}
    (ht : T.red α * T.red F.u ^ n * t ^ p ^ F.a - T.red γ * t +
      T.coeff (α * F.φ x - γ * x - y) n = 0) :
    α * F.φ (x + T.π ^ n * T.teich t) - γ * (x + T.π ^ n * T.teich t) - y ∈
      Ideal.span {T.π ^ (n + 1)} := by
  obtain ⟨z, hz⟩ := T.mem_span_pow.1 hx
  have he : T.coeff (α * F.φ x - γ * x - y) n = T.red z := by
    rw [hz]; simpa using T.coeff_π_pow_mul_add n z 0
  have hred : T.red (z + α * (F.u ^ n * T.teich (t ^ p ^ F.a)) - γ * T.teich t) = 0 := by
    rw [map_sub, map_add, map_mul, map_mul, map_mul, map_pow, T.red_teich, T.red_teich, ← he]
    linear_combination ht
  obtain ⟨z', hz'⟩ := T.red_eq_zero_iff.1 hred
  have : α * F.φ (x + T.π ^ n * T.teich t) - γ * (x + T.π ^ n * T.teich t) - y =
      T.π ^ (n + 1) * z' := by
    rw [map_add, F.φ_π_pow_mul_teich, pow_succ, mul_assoc, ← hz']
    linear_combination hz
  rw [this]; exact T.π_pow_mul_mem le_rfl _

def linApprox (α γ y : Γ) (r : ℕ → L → L) : ℕ → Γ
  | 0 => 0
  | n + 1 => linApprox α γ y r n + T.π ^ n * T.teich (r n
      (T.coeff (α * F.φ (linApprox α γ y r n) - γ * linApprox α γ y r n - y) n))

def linCoeff (α γ y : Γ) (r : ℕ → L → L) (n : ℕ) : L :=
  r n (T.coeff (α * F.φ (F.linApprox α γ y r n) - γ * F.linApprox α γ y r n - y) n)

theorem linApprox_eq_finSum (α γ y : Γ) (r : ℕ → L → L) (n : ℕ) :
    F.linApprox α γ y r n = T.finSum (F.linCoeff α γ y r) n := by
  induction n with
  | zero => simp [linApprox]
  | succ n ih => rw [T.finSum_succ, ← ih]; rfl

variable {F}

theorem linApprox_mem {α γ y : Γ} {r : ℕ → L → L}
    (hr : ∀ n e, T.red α * T.red F.u ^ n * r n e ^ p ^ F.a - T.red γ * r n e + e = 0) (n : ℕ) :
    α * F.φ (F.linApprox α γ y r n) - γ * F.linApprox α γ y r n - y ∈ Ideal.span {T.π ^ n} := by
  induction n with
  | zero => simp [linApprox]
  | succ n ih => exact F.linStep_mem ih (hr n _)

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable {F : T.TeichFrob}

theorem linCoeff_weight_le (ha : 0 < F.a) {α γ y : Γ} (hα : α ∈ T.int) {r : ℕ → L → L}
    (hr : ∀ n e, T.red α * T.red F.u ^ n * r n e ^ p ^ F.a - T.red γ * r n e + e = 0)
    (hα1 : ‖T.red α‖ = 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hγ : ConvergesAt (T.zcoeff γ) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) {Y : ℝ} (hY : 0 ≤ Y)
    (hγY : gaussNorm (T.zcoeff γ) ρ ≤ Y ^ (p ^ F.a - 1))
    (hyY : gaussNorm (T.zcoeff y) ρ ≤ Y ^ p ^ F.a) (n : ℕ) :
    ‖F.linCoeff α γ y r n‖ * ρ ^ n ≤ Y := by
  have hq := F.two_le_q ha
  set q := p ^ F.a with hqdef
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨hs, hsY⟩ := T.finSum_gaussNorm_le hρ0 hρ1 (F.linCoeff α γ y r) hY n ih
  rw [← F.linApprox_eq_finSum] at hs hsY
  set s := F.linApprox α γ y r n
  set σ := ρ ^ q
  have hσ0 : 0 < σ := pow_pos hρ0 _
  have hσ1 : σ < 1 := pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hσρ : σ ≤ ρ := pow_le_of_le_one hρ0.le hρ1.le (by omega)
  obtain ⟨hφ, hφn⟩ := F.gaussNorm_zcoeff_map hρ0 hρ1 hs
  have hασ := T.convergesAt_of_mem_int hα hσ0 hσ1
  have hαφ := T.convergesAt_zcoeff_mul hσ0 hσ1 hασ hφ
  have hαφn : gaussNorm (T.zcoeff (α * F.φ s)) σ ≤ Y ^ q := by
    calc gaussNorm (T.zcoeff (α * F.φ s)) σ
        ≤ gaussNorm (T.zcoeff α) σ * gaussNorm (T.zcoeff (F.φ s)) σ :=
          T.gaussNorm_zcoeff_mul_le hσ0 hσ1.le hασ hφ
      _ ≤ 1 * Y ^ q := by
          refine mul_le_mul (T.gaussNorm_le_one_of_mem_int hα hσ0 hσ1.le) ?_
            (gaussNorm_nonneg hσ0) zero_le_one
          rw [hφn]; exact pow_le_pow_left₀ (gaussNorm_nonneg hρ0) hsY _
      _ = Y ^ q := one_mul _
  have hγσ : ConvergesAt (T.zcoeff γ) σ := convergesAt_of_le (T.zcoeff_neg_exists γ) hγ hσ0 hσρ
  have hsσ : ConvergesAt (T.zcoeff s) σ := convergesAt_of_le (T.zcoeff_neg_exists s) hs hσ0 hσρ
  have hyσ : ConvergesAt (T.zcoeff y) σ := convergesAt_of_le (T.zcoeff_neg_exists y) hy hσ0 hσρ
  have hγs := T.convergesAt_zcoeff_mul hσ0 hσ1 hγσ hsσ
  have hγsn : gaussNorm (T.zcoeff (γ * s)) σ ≤ Y ^ q := by
    calc gaussNorm (T.zcoeff (γ * s)) σ
        ≤ gaussNorm (T.zcoeff γ) σ * gaussNorm (T.zcoeff s) σ :=
          T.gaussNorm_zcoeff_mul_le hσ0 hσ1.le hγσ hsσ
      _ ≤ Y ^ (q - 1) * Y :=
          mul_le_mul ((T.gaussNorm_zcoeff_mono hσ0 hσρ hγ).trans hγY)
            ((T.gaussNorm_zcoeff_mono hσ0 hσρ hs).trans hsY) (gaussNorm_nonneg hσ0)
            (pow_nonneg hY _)
      _ = Y ^ q := by rw [← pow_succ]; congr 1; omega
  have hyn : gaussNorm (T.zcoeff y) σ ≤ Y ^ q := (T.gaussNorm_zcoeff_mono hσ0 hσρ hy).trans hyY
  have hn1 := T.convergesAt_zcoeff_neg hσ0 hσ1 hγs
  have hn2 := T.convergesAt_zcoeff_neg hσ0 hσ1 hyσ
  have hc1 := T.convergesAt_zcoeff_add hσ0 hσ1 hαφ hn1
  have hE : α * F.φ s - γ * s - y = (α * F.φ s + -(γ * s)) + -y := by ring
  have hG : gaussNorm (T.zcoeff (α * F.φ s - γ * s - y)) σ ≤ Y ^ q := by
    rw [hE]
    refine (T.gaussNorm_zcoeff_add_le hσ0 hσ1.le hc1 hn2).trans (max_le ?_ ?_)
    · refine (T.gaussNorm_zcoeff_add_le hσ0 hσ1.le hαφ hn1).trans (max_le hαφn ?_)
      exact (T.gaussNorm_zcoeff_neg_le hσ0 hσ1.le hγs).trans hγsn
    · exact (T.gaussNorm_zcoeff_neg_le hσ0 hσ1.le hyσ).trans hyn
  have hconv : ConvergesAt (T.zcoeff (α * F.φ s - γ * s - y)) σ := by
    rw [hE]; exact T.convergesAt_zcoeff_add hσ0 hσ1 hc1 hn2
  set e := T.coeff (α * F.φ s - γ * s - y) n
  have hen : ‖e‖ * σ ^ n ≤ Y ^ q := by
    have := T.weight_natCast_le hconv n; rw [zpow_natCast] at this; exact this.trans hG
  have hρn0 : 0 < ρ ^ n := pow_pos hρ0 n
  have hρn1 : ρ ^ n ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
  set Y' := Y / ρ ^ n
  have hYY' : Y ≤ Y' := (le_div_iff₀ hρn0).2 (mul_le_of_le_one_right hY hρn1)
  have hY' : 0 ≤ Y' := hY.trans hYY'
  have he' : ‖e‖ ≤ Y' ^ q := by
    rw [div_pow, le_div_iff₀ (pow_pos hρn0 _), ← pow_mul, mul_comm n q, pow_mul]
    exact hen
  have hb : ‖T.red γ‖ ≤ Y' ^ (q - 1) := by
    have h0 := T.weight_natCast_le hγ 0
    simp only [Nat.cast_zero, zpow_zero, mul_one, coeff_zero] at h0
    exact h0.trans (hγY.trans (pow_le_pow_left₀ hY hYY' _))
  have hc : ‖T.red α * T.red F.u ^ n‖ = 1 := by rw [norm_mul, norm_pow, F.norm_red_u, one_pow, hα1, one_mul]
  have ht := norm_le_of_root hq hc (hr n e) hY' he' hb
  calc ‖F.linCoeff α γ y r n‖ * ρ ^ n ≤ Y' * ρ ^ n := mul_le_mul_of_nonneg_right ht hρn0.le
    _ = Y := div_mul_cancel₀ Y hρn0.ne'

variable (F)

theorem exists_linear_sol [IsAlgClosed L] (ha : 0 < F.a) {α : Γ} (hα : α ∈ T.int)
    (hα1 : ‖T.red α‖ = 1) (γ y : Γ) :
    ∃ x : Γ, α * F.φ x - γ * x = y ∧ ∀ ρ Y : ℝ, 0 < ρ → ρ < 1 →
      ConvergesAt (T.zcoeff γ) ρ → ConvergesAt (T.zcoeff y) ρ → 0 ≤ Y →
      gaussNorm (T.zcoeff γ) ρ ≤ Y ^ (p ^ F.a - 1) → gaussNorm (T.zcoeff y) ρ ≤ Y ^ p ^ F.a →
      ∀ n : ℕ, ‖T.coeff x n‖ * ρ ^ n ≤ Y := by
  have hq := F.two_le_q ha
  have hc0 : ∀ n : ℕ, T.red α * T.red F.u ^ n ≠ 0 := fun n => by
    refine mul_ne_zero (norm_ne_zero_iff.1 (by rw [hα1]; exact one_ne_zero))
      (pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [F.norm_red_u]; exact one_ne_zero)))
  choose r hr _ using fun (n : ℕ) (e : L) => exists_root_of_isAlgClosed hq (hc0 n) (T.red γ) e
  refine ⟨T.ofCoeff (F.linCoeff α γ y r), ?_, fun ρ Y hρ0 hρ1 hγ hy hY hγY hyY n => ?_⟩
  · set x := T.ofCoeff (F.linCoeff α γ y r)
    have hall : ∀ n, α * F.φ x - γ * x - y ∈ Ideal.span {T.π ^ n} := fun n => by
      have h1 : x - F.linApprox α γ y r n ∈ Ideal.span {T.π ^ n} := by
        rw [F.linApprox_eq_finSum]; exact T.mk_sub_finSum_mem _ n
      have : α * F.φ x - γ * x - y = (α * F.φ (F.linApprox α γ y r n) - γ * F.linApprox α γ y r n - y) +
          (α * F.φ (x - F.linApprox α γ y r n) - γ * (x - F.linApprox α γ y r n)) := by
        rw [map_sub]; ring
      rw [this]
      exact add_mem (linApprox_mem hr n)
        (sub_mem (Ideal.mul_mem_left _ _ (F.φ_mem_span_pow h1)) (Ideal.mul_mem_left _ _ h1))
    have h0 : α * F.φ x - γ * x - y = 0 := T.eq_of_coeff_eq (funext fun n => by
      rw [T.coeff_zero_elem]; exact T.coeff_of_mem_span (hall (n + 1)) n le_rfl)
    exact sub_eq_zero.1 h0
  · rw [T.coeff_ofCoeff]
    exact linCoeff_weight_le ha hα hr hα1 hρ0 hρ1 hγ hy hY hγY hyY n

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.ExtRobbaFixedUnif
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem norm_le_one_of_forall_weight_le {a : L} {n : ℕ}
    (h : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ‖a‖ * ρ ^ n ≤ 1) : ‖a‖ ≤ 1 := by
  have ht : Tendsto (fun ρ : ℝ => ‖a‖ * ρ ^ n) (𝓝[<] 1) (𝓝 (‖a‖ * 1 ^ n)) :=
    ((continuous_const.mul (continuous_pow n)).tendsto 1).mono_left nhdsWithin_le_nhds
  rw [one_pow, mul_one] at ht
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
  exact h ρ hρ.1 hρ.2

namespace TeichFrob

variable {T} (F : T.TeichFrob)

theorem exists_int_φ_eq_u_mul [IsAlgClosed L] (ha : 0 < F.a) :
    ∃ y ∈ T.int, ‖T.red y‖ = 1 ∧ F.φ y = F.u * y := by
  have hq := F.two_le_q ha
  have hu0 : ∀ n : ℕ, T.red F.u ^ n ≠ 0 := fun n =>
    pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [F.norm_red_u]; exact one_ne_zero))
  have hw0 : T.red F.u ≠ 0 := by simpa using hu0 1
  choose r hr hr0 using fun (n : ℕ) (e : L) => exists_root_of_isAlgClosed hq (hu0 n) (T.red F.u) e
  set y := T.ofCoeff (F.approxCoeff F.u r) with hydef

  have hdig : ∀ n, ‖T.coeff y n‖ ≤ 1 := by
    intro n
    rw [hydef, T.coeff_ofCoeff]
    refine norm_le_one_of_forall_weight_le (n := n) fun ρ hρ0 hρ1 => ?_
    have hw := T.convergesAt_of_mem_int F.u_mem_int hρ0 hρ1
    have hW : gaussNorm (T.zcoeff F.u) ρ ≤ (1 : ℝ) ^ (p ^ F.a - 1) := by
      rw [T.gaussNorm_eq_one_of_mem_int F.u_mem_int F.norm_red_u hρ0 hρ1, one_pow]
    exact approxCoeff_weight_le ha hr hρ0 hρ1 hw zero_le_one hW n
  have hyint : y ∈ T.int := T.mem_int_iff.2 hdig

  have hy0 : T.red y = r 0 0 := by
    rw [← T.coeff_zero, hydef, T.coeff_ofCoeff]
    simp [approxCoeff, approx]
  have hr00 : r 0 0 ≠ 0 := hr0 0 0 rfl hw0
  have hroot := hr 0 0
  simp only [pow_zero, one_mul, add_zero] at hroot
  have hnorm : ‖r 0 0‖ = 1 := by
    have hle : ‖r 0 0‖ ≤ 1 := by rw [← hy0, ← T.coeff_zero]; exact hdig 0
    have hq1 : r 0 0 ^ (p ^ F.a - 1) = T.red F.u := by
      have : r 0 0 ^ p ^ F.a = r 0 0 ^ (p ^ F.a - 1) * r 0 0 := by
        rw [← pow_succ]; congr 1; omega
      rw [this] at hroot
      exact mul_right_cancel₀ hr00 (by linear_combination hroot)
    have h1 : ‖r 0 0‖ ^ (p ^ F.a - 1) = 1 := by rw [← norm_pow, hq1, F.norm_red_u]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1
  refine ⟨y, hyint, by rw [hy0, hnorm], ?_⟩

  have hall : ∀ n, F.φ y - F.u * y ∈ Ideal.span {T.π ^ n} := fun n => by
    have h1 : y - F.approx F.u r n ∈ Ideal.span {T.π ^ n} := by
      rw [F.approx_eq_finSum]; exact T.mk_sub_finSum_mem _ n
    have : F.φ y - F.u * y = (F.φ (F.approx F.u r n) - F.u * F.approx F.u r n) +
        (F.φ (y - F.approx F.u r n) - F.u * (y - F.approx F.u r n)) := by
      rw [map_sub]; ring
    rw [this]
    exact add_mem (approx_mem hr n) (sub_mem (F.φ_mem_span_pow h1) (Ideal.mul_mem_left _ _ h1))
  have h0 : F.φ y - F.u * y = 0 := T.eq_of_coeff_eq (funext fun n => by
    rw [T.coeff_zero_elem]; exact T.coeff_of_mem_span (hall (n + 1)) n le_rfl)
  exact sub_eq_zero.1 h0

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.TateNormalizedTrace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField Module Set

noncomputable section

variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]

def tateTrace (n : ℕ) : PadicAlgCl p → PadicAlgCl p := normTrace (cyclotomicLayer K n)

theorem tateTrace_add (n : ℕ) (y z : PadicAlgCl p) :
    tateTrace K n (y + z) = tateTrace K n y + tateTrace K n z :=
  normTrace_add _ y z

theorem tateTrace_mem (n : ℕ) (y : PadicAlgCl p) : tateTrace K n y ∈ cyclotomicLayer K n :=
  normTrace_mem _ y

theorem tateTrace_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTrace K n a = a :=
  normTrace_of_mem _ ha

theorem tateTrace_mul_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n)
    (y : PadicAlgCl p) : tateTrace K n (a * y) = a * tateTrace K n y :=
  normTrace_mul_of_mem _ ha y

theorem tateTrace_gal (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    tateTrace K n (σ y) = σ (tateTrace K n y) :=
  normTrace_cyclotomicLayer_gal K σ n y

theorem tateTrace_tateTrace_of_le {n n' : ℕ} (h : n ≤ n') (y : PadicAlgCl p) :
    tateTrace K n (tateTrace K n' y) = tateTrace K n y :=
  normTrace_normTrace_of_le (cyclotomicLayer_mono K h) y

theorem exists_norm_tateTrace_le_of_stableIndex_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n, stableIndex K ≤ n → ∀ x ∈ cyclotomicLimit K,
      ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  refine ⟨p * ∑ i, ‖towerVec K i‖ * ‖towerDualVec K i‖,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => by positivity), ?_⟩
  intro n hn x hx
  obtain ⟨m, hm⟩ := (mem_cyclotomicLimit K).1 hx
  have hm' : x ∈ cyclotomicLayer K (max m n) := cyclotomicLayer_mono K (le_max_left m n) hm
  refine norm_normTrace_cyclotomicLayer_le K (Nat.cast_nonneg p) ?_ hn (le_max_right m n) hm'
  intro n' m' hn' hnm' y hy
  exact norm_normTrace_cycl_le
    (le_trans (by norm_num) ((two_le_stableIndex K).trans hn')) hnm' hy

theorem exists_norm_tateTrace_le_on_layer (n N : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ cyclotomicLayer K N, ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  let S : Submodule ℚ_[p] (PadicAlgCl p) := (cyclotomicLayer K N).toSubalgebra.toSubmodule
  haveI : FiniteDimensional ℚ_[p] S :=
    inferInstanceAs (FiniteDimensional ℚ_[p] (cyclotomicLayer K N))
  let f : S →ₗ[ℚ_[p]] PadicAlgCl p :=
    ((normTraceₗ (cyclotomicLayer K n)).restrictScalars ℚ_[p]).comp S.subtype
  let f' := LinearMap.toContinuousLinearMap f
  refine ⟨‖f'‖, ContinuousLinearMap.opNorm_nonneg f', fun x hx => ?_⟩
  have := f'.le_opNorm ⟨x, hx⟩
  exact this

theorem exists_norm_tateTrace_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n, ∀ x ∈ cyclotomicLimit K, ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_tateTrace_le_of_stableIndex_le K
  choose c' hc'0 hc' using fun n => exists_norm_tateTrace_le_on_layer K n (stableIndex K)
  refine ⟨c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n), by
    have : 0 ≤ ∑ n ∈ Finset.range (stableIndex K), c' n := Finset.sum_nonneg fun n _ => hc'0 n
    positivity, ?_⟩
  intro n x hx
  have hs : 0 ≤ ∑ n ∈ Finset.range (stableIndex K), c' n := Finset.sum_nonneg fun n _ => hc'0 n
  by_cases hn : stableIndex K ≤ n
  · calc ‖tateTrace K n x‖ ≤ c * ‖x‖ := hc n hn x hx
      _ ≤ c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n) * ‖x‖ := by
        nlinarith [mul_nonneg (mul_nonneg hc0 hs) (norm_nonneg x)]
  · push_neg at hn
    have hle : c' n ≤ ∑ n ∈ Finset.range (stableIndex K), c' n :=
      Finset.single_le_sum (fun n _ => hc'0 n) (Finset.mem_range.2 hn)
    rw [← tateTrace_tateTrace_of_le K hn.le x]
    calc ‖tateTrace K n (tateTrace K (stableIndex K) x)‖
        ≤ c' n * ‖tateTrace K (stableIndex K) x‖ := hc' n _ (tateTrace_mem K _ x)
      _ ≤ c' n * (c * ‖x‖) := mul_le_mul_of_nonneg_left (hc _ le_rfl x hx) (hc'0 n)
      _ ≤ c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n) * ‖x‖ := by
        have := norm_nonneg x
        nlinarith [mul_nonneg hc0 this]

def tateBound : ℝ := Classical.choose (exists_norm_tateTrace_le K)

theorem tateBound_nonneg : 0 ≤ tateBound K := (Classical.choose_spec (exists_norm_tateTrace_le K)).1

theorem norm_tateTrace_le (n : ℕ) {x : PadicAlgCl p} (hx : x ∈ cyclotomicLimit K) :
    ‖tateTrace K n x‖ ≤ tateBound K * ‖x‖ :=
  (Classical.choose_spec (exists_norm_tateTrace_le K)).2 n x hx

section Completion

def cyclotomicCompletion : Set ℂ_[p] := closureInCp (cyclotomicLimit K)

def tateTraceHat (n : ℕ) : ℂ_[p] → ℂ_[p] := extendToClosure (cyclotomicLimit K) (tateTrace K n)

def tateKernel (n : ℕ) : Set ℂ_[p] := kernelInCp (cyclotomicLimit K) (tateTrace K n)

variable {K}

theorem tateTrace_add_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K, ∀ z ∈ cyclotomicLimit K,
    tateTrace K n (y + z) = tateTrace K n y + tateTrace K n z :=
  fun y _ z _ => tateTrace_add K n y z

theorem norm_tateTrace_le_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K,
    ‖tateTrace K n y‖ ≤ tateBound K * ‖y‖ :=
  fun _ hy => norm_tateTrace_le K n hy

theorem norm_tateTraceHat_le (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    ‖tateTraceHat K n x‖ ≤ tateBound K * ‖x‖ :=
  norm_extendToClosure_le (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) hx

theorem tateTraceHat_add (n : ℕ) {x x' : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K)
    (hx' : x' ∈ cyclotomicCompletion K) :
    tateTraceHat K n (x + x') = tateTraceHat K n x + tateTraceHat K n x' :=
  (extendToClosure_add (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) hx hx').2

theorem tateTraceHat_mem (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n x ∈
      ((↑) : PadicAlgCl p → ℂ_[p]) '' (cyclotomicLayer K n : Set (PadicAlgCl p)) :=
  extendToClosure_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (fun y _ => tateTrace_mem K n y) hx

theorem tateTraceHat_coe_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTraceHat K n (a : ℂ_[p]) = a :=
  extendToClosure_coe_of_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha => tateTrace_of_mem K ha) ha

theorem tateTraceHat_mul {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n ((a : ℂ_[p]) * x) = (a : ℂ_[p]) * tateTraceHat K n x :=
  extendToClosure_mul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha y _ => tateTrace_mul_of_mem K ha y) ha hx

theorem gal_mem_cyclotomicLimit (σ : Gal(PadicAlgCl p/K)) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLimit K) : σ y ∈ cyclotomicLimit K :=
  map_mem_cyclotomicLimit K (σ.restrictScalars ℚ_[p]) (fun x hx => σ.commutes ⟨x, hx⟩) hy

theorem smul_mem_cyclotomicCompletion (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : σ • x ∈ cyclotomicCompletion K :=
  smul_mem_closureInCp σ (fun _ hy => gal_mem_cyclotomicLimit σ hy) hx

theorem tateTraceHat_smul (n : ℕ) (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : tateTraceHat K n (σ • x) = σ • tateTraceHat K n x :=
  extendToClosure_smul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) σ
    (fun _ hy => gal_mem_cyclotomicLimit σ hy) (fun y _ => tateTrace_gal K σ n y) hx

end Completion

section Gamma

variable {K}

def tateGammaBound (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] : ℝ :=
  (p : ℝ) ^ 3 * ∑ i, ‖towerVec K i‖ * ‖towerDualVec K i‖

end Gamma

end

end GroundTheory.PAdicHodge
end

