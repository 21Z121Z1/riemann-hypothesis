import Formalism.EllipticTorsion.Bundle0002
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.ConstantCoeffLogOnePlus
section
noncomputable section

namespace Formalism.ELL.EulerSeries

open Formalism.G Formalism.ELL

variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]

def eulFun (F : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun d => (d.degree : K) * MvPowerSeries.coeff d F

theorem coeff_eulFun (F : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (eulFun F) = (d.degree : K) * MvPowerSeries.coeff d F := rfl

def eulLin : MvPowerSeries σ K →ₗ[K] MvPowerSeries σ K where
  toFun := eulFun
  map_add' F G := by
    ext d
    simp only [coeff_eulFun, map_add, mul_add]
  map_smul' c F := by
    ext d
    simp only [coeff_eulFun, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

theorem eulFun_mul (F G : MvPowerSeries σ K) :
    eulFun (F * G) = F • eulFun G + G • eulFun F := by
  ext d
  rw [smul_eq_mul, smul_eq_mul, mul_comm G, map_add, coeff_eulFun, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [coeff_eulFun, coeff_eulFun, ← hp, map_add, Nat.cast_add]
  ring

def eul : Derivation K (MvPowerSeries σ K) (MvPowerSeries σ K) :=
  Derivation.mk' eulLin fun a b => eulFun_mul a b

theorem eul_apply (F : MvPowerSeries σ K) : eul F = eulFun F := rfl

theorem eq_zero_of_eulFun (F : MvPowerSeries σ K) (h0 : MvPowerSeries.constantCoeff F = 0)
    (h : eulFun F = 0) : F = 0 := by
  ext d
  rw [map_zero]
  by_cases hd : d = 0
  · subst hd
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0
  · have h1 := congrArg (MvPowerSeries.coeff d) h
    rw [coeff_eulFun, map_zero] at h1
    have hdeg : ((d.degree : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact fun h' => hd ((Finsupp.degree_eq_zero_iff d).mp h')
    exact (mul_eq_zero.mp h1).resolve_left hdeg

def Agree (N : ℕ) (F G : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < N → MvPowerSeries.coeff d F = MvPowerSeries.coeff d G

theorem Agree.mul_right {N : ℕ} {F G : MvPowerSeries σ K} (h : Agree N F G)
    (H : MvPowerSeries σ K) : Agree N (F * H) (G * H) := by
  intro d hd
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg := congrArg Finsupp.degree hp
  rw [map_add] at hdeg
  rw [h p.1 (by omega)]

theorem Agree.eulFun {N : ℕ} {F G : MvPowerSeries σ K} (h : Agree N F G) :
    Agree N (eulFun F) (eulFun G) := by
  intro d hd
  rw [coeff_eulFun, coeff_eulFun, h d hd]

theorem coeff_pow_eq_zero {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    ∀ (n : ℕ) (d : σ →₀ ℕ), d.degree < n → MvPowerSeries.coeff d (f ^ n) = 0
  | 0, d, hd => absurd hd (Nat.not_lt_zero _)
  | n + 1, d, hd => by
    rw [pow_succ', MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg := congrArg Finsupp.degree hp
    rw [map_add] at hdeg
    by_cases h1 : p.1 = 0
    · rw [h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
    · have : 0 < p.1.degree :=
        Nat.pos_of_ne_zero (fun h => h1 ((Finsupp.degree_eq_zero_iff _).mp h))
      rw [coeff_pow_eq_zero hf n p.2 (by omega), mul_zero]

def truncLog (N : ℕ) (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  ∑ n ∈ Finset.range N, PowerSeries.coeff n (PowerSeries.log K) • f ^ n

theorem agree_truncLog {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (N : ℕ) : Agree N (logOnePlus f) (truncLog N f) := by
  intro d hd
  rw [logOnePlus, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    truncLog, map_sum]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N) ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul]
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hn
    rw [coeff_pow_eq_zero hf n d (by omega), smul_zero]

theorem coeff_log_succ_mul (k : ℕ) :
    PowerSeries.coeff (k + 1) (PowerSeries.log K) * ((k + 1 : ℕ) : K) = (-1) ^ k := by
  rw [PowerSeries.coeff_log, if_neg (Nat.succ_ne_zero k)]
  simp only [map_div₀, map_pow, map_neg, map_one, map_natCast]
  have : ((k + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  field_simp
  ring

theorem eul_truncLog (f : MvPowerSeries σ K) (M : ℕ) :
    eulFun (truncLog (M + 1) f) = (∑ k ∈ Finset.range M, (-f) ^ k) * eulFun f := by
  have h0 : PowerSeries.coeff 0 (PowerSeries.log K) = 0 := by simp
  rw [← eul_apply, truncLog, map_sum, Finset.sum_range_succ', h0, zero_smul, map_zero,
    add_zero, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.map_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, Algebra.smul_def,
    nsmul_eq_mul, smul_eq_mul, eul_apply, neg_pow]
  have h1 : algebraMap K (MvPowerSeries σ K) (PowerSeries.coeff (k + 1) (PowerSeries.log K)) *
      ((k + 1 : ℕ) : MvPowerSeries σ K) = (-1) ^ k := by
    rw [← map_natCast (algebraMap K (MvPowerSeries σ K)), ← map_mul, coeff_log_succ_mul,
      map_pow, map_neg, map_one]
  linear_combination (f ^ k * eulFun f) * h1

theorem eul_log_mul {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    eulFun (logOnePlus f) * (1 + f) = eulFun f := by
  ext d
  have hA := ((agree_truncLog hf (d.degree + 2)).eulFun).mul_right (1 + f) d (by omega)
  rw [hA, show d.degree + 2 = (d.degree + 1) + 1 from rfl, eul_truncLog]
  have hg := geom_sum_mul (-f) (d.degree + 1)
  have hE : (∑ k ∈ Finset.range (d.degree + 1), (-f) ^ k) * eulFun f * (1 + f) =
      eulFun f - (-f) ^ (d.degree + 1) * eulFun f := by
    linear_combination (-(eulFun f)) * hg
  rw [hE, map_sub]
  have hz : Agree (d.degree + 1) ((-f) ^ (d.degree + 1)) 0 := by
    intro e he
    rw [map_zero]
    exact coeff_pow_eq_zero (by rw [map_neg, hf, neg_zero]) _ e he
  have := hz.mul_right (eulFun f) d (by omega)
  rw [this, zero_mul, map_zero, sub_zero]

theorem constantCoeff_logOnePlus {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (logOnePlus f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hf _ PowerSeries.constantCoeff_log

theorem log_zero : logOnePlus (0 : MvPowerSeries σ K) = 0 := by
  apply eq_zero_of_eulFun _ (constantCoeff_logOnePlus (map_zero _))
  have := eul_log_mul (map_zero (MvPowerSeries.constantCoeff (σ := σ) (R := K)))
  rwa [add_zero, mul_one, ← eul_apply 0, map_zero] at this

theorem log_add {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    logOnePlus f + logOnePlus g = logOnePlus (f + g + f * g) := by
  have hh : MvPowerSeries.constantCoeff (f + g + f * g) = 0 := by
    simp only [map_add, map_mul, hf, hg, add_zero, mul_zero]
  have hu : IsUnit (1 + (f + g + f * g)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_add, hh, map_one, add_zero]
    exact isUnit_one
  have e1 := eul_log_mul hf
  have e2 := eul_log_mul hg
  have e3 := eul_log_mul hh
  have hD : eulFun (f + g + f * g) = eulFun f + eulFun g + (f * eulFun g + g * eulFun f) := by
    show eul (f + g + f * g) = eul f + eul g + (f * eul g + g * eul f)
    rw [map_add, map_add, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have key : eulFun (logOnePlus f + logOnePlus g - logOnePlus (f + g + f * g)) = 0 := by
    rw [← hu.mul_left_inj, zero_mul]
    show eul (logOnePlus f + logOnePlus g - logOnePlus (f + g + f * g)) * _ = 0
    rw [map_sub, map_add, eul_apply, eul_apply, eul_apply]
    linear_combination (1 + g) * e1 + (1 + f) * e2 - e3 - hD
  have := eq_zero_of_eulFun _ (by
    rw [map_sub, map_add, constantCoeff_logOnePlus hf, constantCoeff_logOnePlus hg,
      constantCoeff_logOnePlus hh, add_zero, sub_zero]) key
  exact sub_eq_zero.mp this

variable [IsUltrametricDist K]

theorem integral_map (F : MvPowerSeries σ (unitBall K)) :
    IntegralMv (MvPowerSeries.map (unitBall K).subtype F) := fun d => by
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff d F).2

theorem integral_add_mul {f g : MvPowerSeries σ K} (hf : IntegralMv f) (hg : IntegralMv g) :
    IntegralMv (f + g + f * g) := by
  have hf' : ∀ n, MvPowerSeries.coeff n f ∈ unitBall K := fun n => hf n
  have hg' : ∀ n, MvPowerSeries.coeff n g ∈ unitBall K := fun n => hg n
  have := integral_map (f.toSubring _ hf' + g.toSubring _ hg' +
    f.toSubring _ hf' * g.toSubring _ hg')
  simpa only [map_add, map_mul, MvPowerSeries.map_toSubring] using this

theorem exists_inv {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0)
    (hf : IntegralMv f) :
    ∃ h : MvPowerSeries σ K, MvPowerSeries.constantCoeff h = 0 ∧ IntegralMv h ∧
      f + h + f * h = 0 := by
  have hf' : ∀ n, MvPowerSeries.coeff n f ∈ unitBall K := fun n => hf n
  set f' := f.toSubring _ hf' with hf'def
  have hc : MvPowerSeries.constantCoeff f' = 0 := by
    apply Subtype.ext
    rw [hf'def, MvPowerSeries.constantCoeff_toSubring, hf0]
    rfl
  have hu : IsUnit (1 + f') := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_add, hc, map_one, add_zero]
    exact isUnit_one
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨MvPowerSeries.map (unitBall K).subtype (v - 1), ?_, integral_map _, ?_⟩
  · have hprod := congrArg (MvPowerSeries.map (unitBall K).subtype) hv
    rw [map_mul, map_add, map_one, MvPowerSeries.map_toSubring] at hprod
    have h2 := congrArg MvPowerSeries.constantCoeff hprod
    simp only [map_mul, map_add, map_one, hf0, add_zero, one_mul] at h2
    simp only [map_sub, h2, map_one, sub_self]
  · have hprod := congrArg (MvPowerSeries.map (unitBall K).subtype) hv
    rw [map_mul, map_add, map_one, MvPowerSeries.map_toSubring] at hprod
    rw [map_sub, map_one]
    linear_combination hprod

end Formalism.ELL.EulerSeries

namespace Formalism.ELL

theorem N_additive_subgroup : Formalism.ELL.NAddSubgroup := by
  intro K _ _ _ σ
  classical
  refine ⟨⟨0, map_zero _, fun d => by simp, EulerSeries.log_zero.symm⟩, ?_, ?_⟩
  · rintro G H ⟨f, hf0, hfi, rfl⟩ ⟨g, hg0, hgi, rfl⟩
    exact ⟨f + g + f * g, by simp only [map_add, map_mul, hf0, hg0, add_zero, mul_zero],
      EulerSeries.integral_add_mul hfi hgi, EulerSeries.log_add hf0 hg0⟩
  · rintro G ⟨f, hf0, hfi, rfl⟩
    obtain ⟨h, hh0, hhi, hfh⟩ := EulerSeries.exists_inv hf0 hfi
    refine ⟨h, hh0, hhi, ?_⟩
    have := EulerSeries.log_add hf0 hh0
    rw [hfh, EulerSeries.log_zero] at this
    linear_combination -this

end Formalism.ELL
end
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.IntVal
section
noncomputable section

namespace Formalism.ELL.IntegerValuedContinuity

theorem continuous_eval {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] (P : Polynomial K) :
    Continuous fun b : ℤ_[p] => P.eval (algebraMap ℚ_[p] K (b : ℚ_[p])) := by
  have h1 : Continuous (algebraMap ℚ_[p] K) := by
    have : (⇑(algebraMap ℚ_[p] K)) = fun c => c • (1 : K) := by
      funext c; exact Algebra.algebraMap_eq_smul_one c
    rw [this]; exact continuous_id.smul continuous_const
  have h2 : Continuous (fun b : ℤ_[p] => (b : ℚ_[p])) := continuous_subtype_val
  exact (P.continuous).comp (h1.comp h2)

end Formalism.ELL.IntegerValuedContinuity

namespace Formalism.ELL

theorem integer_valued_padic_integers : IntValuedZp := by
  intro p _ K _ _ P hP b
  have hc := Formalism.ELL.IntegerValuedContinuity.continuous_eval (p := p) (K := K) P
  have hclosed : IsClosed {b : ℤ_[p] | ‖P.eval (algebraMap ℚ_[p] K (b : ℚ_[p]))‖ ≤ 1} :=
    isClosed_le (continuous_norm.comp hc) continuous_const
  refine PadicInt.denseRange_natCast.induction_on b hclosed ?_
  intro n
  show ‖P.eval (algebraMap ℚ_[p] K (((n : ℤ_[p])) : ℚ_[p]))‖ ≤ 1
  have : algebraMap ℚ_[p] K (((n : ℤ_[p])) : ℚ_[p]) = (n : K) := by
    simp
  rw [this]; exact hP n

end Formalism.ELL
end
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.LegendreInvariant
section
namespace Formalism.ELL

theorem legendre_invariant : LegendreInv := by
  intro K _ l
  refine ⟨?_, ?_⟩ <;>
  simp only [legendre, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring

theorem deuring_invariant : DeuringInv := by
  intro K _ a
  refine ⟨?_, ?_⟩ <;>
  simp only [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring

end Formalism.ELL
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.ModelUnitOf
section
universe u

namespace Formalism.ELL.unitAtAlt

open Formalism.ELL

lemma two_or_three {K : Type u} [NormedField K] [IsUltrametricDist K] :
    ‖(2 : K)‖ = 1 ∨ ‖(3 : K)‖ = 1 := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 2
  have h3 : ‖(3 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 3
  have h1 : ‖(1 : K)‖ ≤ max ‖(3 : K)‖ ‖(2 : K)‖ := by
    have : (1 : K) = 3 + -2 := by norm_num
    rw [this]
    simpa [norm_neg] using IsUltrametricDist.norm_add_le_max (3 : K) (-2)
  rw [norm_one] at h1
  by_cases h : ‖(2 : K)‖ = 1
  · exact Or.inl h
  · right
    have hlt : ‖(2 : K)‖ < 1 := lt_of_le_of_ne h2 h
    rcases le_max_iff.mp h1 with h' | h'
    · exact le_antisymm h3 h'
    · exact absurd h' (not_le.mpr hlt)

lemma of_model {K : Type u} [NormedField K] (W : WeierstrassCurve K) (j : K)
    (hI : IntegralModel W) (hc : W.c₄ ^ 3 = j * W.Δ) (hΔ : ‖W.Δ‖ = 1) :
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic),
      IntegralModel W ∧ ‖W.Δ‖ = 1 ∧ W.j = j := by
  have hne : W.Δ ≠ 0 := by
    intro h; rw [h, norm_zero] at hΔ; exact zero_ne_one hΔ
  have : W.IsElliptic := ⟨hne.isUnit⟩
  refine ⟨W, inferInstance, hI, hΔ, ?_⟩
  rw [WeierstrassCurve.j, hc, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  field_simp

end Formalism.ELL.unitAtAlt

namespace Formalism.ELL

open Formalism.ELL.unitAtAlt

theorem modelUnit_of (hL : Formalism.ELL.ModelLegendre.{u}) (hD : Formalism.ELL.ModelDeuring.{u}) :
    Formalism.ELL.ModelUnit.{u} := by
  intro K _ _ _ j hj
  rcases two_or_three (K := K) with h2 | h3
  · obtain ⟨l, hl, _hl1, hc, hΔ⟩ := hL K h2 j hj
    refine of_model (legendre l) j ?_ hc hΔ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [legendre]
    · simp
    · rw [norm_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      simp [hl]
    · simp
    · exact hl.le
    · simp
  · obtain ⟨a, ha, hc, hΔ⟩ := hD K h3 j hj
    refine of_model (deuring a) j ?_ hc hΔ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [deuring]
    · exact ha
    all_goals simp

end Formalism.ELL
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.PadicMult
section
noncomputable section

open PowerSeries

universe u

namespace Formalism.ELL.PadicMultiplication

open Formalism.G Formalism.G.LogP

section Ring

variable {R : Type*} [CommRing R]

def mulN (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | m + 1 => MvPowerSeries.subst (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries

theorem mulN_zero (F : FormalGroup R) : mulN F 0 = 0 := rfl

theorem mulN_succ (F : FormalGroup R) (m : ℕ) :
    mulN F (m + 1) = MvPowerSeries.subst
      (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries := rfl

theorem constantCoeff_mulN (F : FormalGroup R) (m : ℕ) :
    MvPowerSeries.constantCoeff (mulN F m) = 0 := by
  induction m with
  | zero => simp [mulN_zero]
  | succ m ih =>
    rw [mulN_succ]
    have := constantCoeff_subst_of_zero (R := R) F.toPowerSeries
      (b := (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R))
      (fun i => by fin_cases i; exacts [ih, PowerSeries.constantCoeff_X])
    rw [F.zero_constantCoeff] at this
    exact this

end Ring

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem map_mulN (F : FormalGroup (unitBall K)) (m : ℕ) :
    (mulN F (m + 1)).map (unitBall K).subtype =
      MvPowerSeries.subst
        (![(mulN F m).map (unitBall K).subtype, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K)
        (F.map (unitBall K).subtype).toPowerSeries := by
  rw [mulN_succ]
  have hs := hs2 (R := unitBall K) (constantCoeff_mulN F m)
    (u := mulN F m) (v := (PowerSeries.X : PowerSeries (unitBall K))) PowerSeries.constantCoeff_X
  rw [PowerSeries.map, MvPowerSeries.map_subst hs]
  simp only [FormalGroup.map_toPowerSeries]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact PowerSeries.map_X _

theorem log_mulN (F : FormalGroup (unitBall K)) (l : PowerSeries K)
    (hl : IsLog (F.map (unitBall K).subtype) l) (m : ℕ) :
    l.subst ((mulN F m).map (unitBall K).subtype) = (m : K) • l := by
  obtain ⟨hl0, -, hlF⟩ := hl
  induction m with
  | zero => simp [mulN_zero, hl0]
  | succ m ih =>
    have hM : MvPowerSeries.constantCoeff ((mulN F m).map (unitBall K).subtype) = 0 := by
      show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (mulN F m)) = 0
      rw [MvPowerSeries.constantCoeff_map, constantCoeff_mulN]; simp
    have hs := hs2 (R := K) hM (v := (PowerSeries.X : PowerSeries K)) PowerSeries.constantCoeff_X
    rw [map_mulN, ← psubst_subst l (F.map (unitBall K).subtype).zero_constantCoeff hs, hlF,
      MvPowerSeries.subst_add hs, atX, atY,
      psubst_subst l (by simp) hs, psubst_subst l (by simp) hs,
      MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [ih, PowerSeries.X_subst]
    push_cast
    rw [add_smul, one_smul]

end Formalism.ELL.PadicMultiplication

namespace Formalism.ELL.PadicMultiplication

open Formalism.G Formalism.G.LogP

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem e_natMul (F : FormalGroup (unitBall K)) (l e : PowerSeries K)
    (hl : IsLog (F.map (unitBall K).subtype) l) (hel : e.subst l = X) (m : ℕ) :
    e.subst ((m : K) • l) = (mulN F m).map (unitBall K).subtype := by
  have hM : MvPowerSeries.constantCoeff ((mulN F m).map (unitBall K).subtype) = 0 := by
    show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (mulN F m)) = 0
    rw [MvPowerSeries.constantCoeff_map, constantCoeff_mulN]; simp
  rw [← log_mulN F l hl m, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hl.1)
    (PowerSeries.HasSubst.of_constantCoeff_zero hM), hel,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hM)]

theorem integral_natMul (F : FormalGroup (unitBall K)) (m n : ℕ) :
    ‖coeff n ((mulN F m).map (unitBall K).subtype)‖ ≤ 1 := by
  rw [PowerSeries.coeff_map]
  exact (coeff n (mulN F m)).2

def coeffPoly (l e : PowerSeries K) (n : ℕ) : Polynomial K :=
  ∑ d ∈ Finset.range (n + 1),
    Polynomial.C (coeff d e * coeff n (l ^ d)) * Polynomial.X ^ d

theorem coeff_subst_smul (l e : PowerSeries K) (hl0 : constantCoeff l = 0) (c : K) (n : ℕ) :
    coeff n (e.subst (c • l)) = (coeffPoly l e n).eval c := by
  have hcl : constantCoeff (c • l) = 0 := by simp [hl0]
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr hl0
  have hz : ∀ d, n < d → coeff n (l ^ d) = 0 := by
    intro d hd
    rw [hg, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hcl),
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · simp only [coeffPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, smul_pow, PowerSeries.coeff_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun d _ => by ring
  · intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hd
    rw [smul_pow, PowerSeries.coeff_smul, hz d (by omega), smul_zero, smul_zero]

end Formalism.ELL.PadicMultiplication

namespace Formalism.ELL

open Formalism.G Formalism.ELL.PadicMultiplication

theorem padicMult_of (h : IntValuedZp.{u}) : PadicMult.{u} := by
  intro p _ K _ _ _ F l e hl he0 hel hle b n
  rw [coeff_subst_smul l e hl.1]
  refine h p K (coeffPoly l e n) (fun m => ?_) b
  rw [← coeff_subst_smul l e hl.1, e_natMul F l e hl hel m]
  exact integral_natMul F m n

end Formalism.ELL
end
end

