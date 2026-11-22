import Formalism.PeriodIntegrals.Bundle0006
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.CoeffSubstOfDegreeEqOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0039
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0035

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.CoeffPowEqZeroOfDegreeLt
section
noncomputable section

open PI.JetsPhW

namespace PI.JetsPhW.Ch

section Chain

variable {R : Type*} [CommRing R] {σ : Type*}

private theorem coeff_dX (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (PI.JetsPhW.dX f) = ((n : R) + 1) * PowerSeries.coeff (n + 1) f := by
  simp only [PI.JetsPhW.dX, PowerSeries.coeff_mk]

theorem dX_eq (f : PowerSeries R) : dX f = PowerSeries.derivative R f := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_dX]
  ring

theorem degree_le_of_le {y e : σ →₀ ℕ} (h : y ≤ e) : y.degree ≤ e.degree := by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  rw [map_add]
  exact Nat.le_add_right _ _

theorem coeff_pow_eq_zero_of_degree_lt {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    {e : σ →₀ ℕ} {d : ℕ} (h : e.degree < d) : MvPowerSeries.coeff e (a ^ d) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero d ha)

theorem coeff_subst_congr {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    {f g : PowerSeries R} {N : ℕ} (hfg : ∀ k < N, PowerSeries.coeff k f = PowerSeries.coeff k g)
    {e : σ →₀ ℕ} (he : e.degree < N) :
    MvPowerSeries.coeff e (PowerSeries.subst a f) = MvPowerSeries.coeff e (PowerSeries.subst a g) := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs]
  refine finsum_congr fun k => ?_
  by_cases hk : k < N
  · rw [hfg k hk]
  · rw [coeff_pow_eq_zero_of_degree_lt ha (lt_of_lt_of_le he (not_lt.mp hk)), smul_zero, smul_zero]

theorem coeff_mul_congr (u : MvPowerSeries σ R) {f g : MvPowerSeries σ R} {e : σ →₀ ℕ}
    (hfg : ∀ y ≤ e, MvPowerSeries.coeff y f = MvPowerSeries.coeff y g) :
    MvPowerSeries.coeff e (u * f) = MvPowerSeries.coeff e (u * g) := by
  classical
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [hfg p.2 (by rw [← hp]; exact le_add_self)]

theorem pderiv_subst_coe (i : σ) {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    (q : Polynomial R) :
    MvPowerSeries.pderiv R i (PowerSeries.subst a (q : PowerSeries R)) =
      MvPowerSeries.pderiv R i a * PowerSeries.subst a (dX (q : PowerSeries R)) := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [dX_eq, PowerSeries.derivative_coe, PowerSeries.subst_coe hs,
    PowerSeries.subst_coe hs, Derivation.map_aeval, smul_eq_mul]
  ring

theorem pderiv_subst (i : σ) {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    (g : PowerSeries R) :
    MvPowerSeries.pderiv R i (PowerSeries.subst a g) =
      MvPowerSeries.pderiv R i a * PowerSeries.subst a (dX g) := by
  ext e
  have h1 : MvPowerSeries.coeff e (MvPowerSeries.pderiv R i (PowerSeries.subst a g)) =
      MvPowerSeries.coeff e (MvPowerSeries.pderiv R i
        (PowerSeries.subst a (PowerSeries.trunc (e.degree + 2) g : PowerSeries R))) := by
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv]
    congr 1
    refine coeff_subst_congr ha (N := e.degree + 2) (fun k hk => ?_) ?_
    · exact (PowerSeries.coeff_coe_trunc_of_lt hk).symm
    · rw [map_add, Finsupp.degree_single]
      omega
  have h2 : MvPowerSeries.coeff e (MvPowerSeries.pderiv R i a * PowerSeries.subst a (PI.JetsPhW.dX g)) =
      MvPowerSeries.coeff e (MvPowerSeries.pderiv R i a *
        PowerSeries.subst a (PI.JetsPhW.dX (PowerSeries.trunc (e.degree + 2) g : PowerSeries R))) := by
    refine coeff_mul_congr _ fun y hy => ?_
    refine coeff_subst_congr ha (N := e.degree + 1) (fun k hk => ?_) ?_
    · rw [coeff_dX, coeff_dX, PowerSeries.coeff_coe_trunc_of_lt (n := k + 1) (m := e.degree + 2) (by omega)]
    · exact Nat.lt_succ_of_le (degree_le_of_le hy)
  rw [h1, pderiv_subst_coe i ha, h2]

theorem pderiv_subst_X_self (i : σ) (g : PowerSeries R) :
    MvPowerSeries.pderiv R i (PowerSeries.subst (MvPowerSeries.X i) g) =
      PowerSeries.subst (MvPowerSeries.X i) (dX g) := by
  rw [pderiv_subst i (a := MvPowerSeries.X i) (MvPowerSeries.constantCoeff_X i) g,
    MvPowerSeries.pderiv_X_self, one_mul]

theorem pderiv_subst_X_ne {i j : σ} (h : j ≠ i) (g : PowerSeries R) :
    MvPowerSeries.pderiv R i (PowerSeries.subst (MvPowerSeries.X j) g) = 0 := by
  rw [pderiv_subst i (a := MvPowerSeries.X j) (MvPowerSeries.constantCoeff_X j) g,
    MvPowerSeries.pderiv_X_of_ne h, zero_mul]

def sumL (l : PowerSeries R) (c : σ → R) (s : Finset σ) : MvPowerSeries σ R :=
  ∑ j ∈ s, MvPowerSeries.C (c j) * PowerSeries.subst (MvPowerSeries.X j) l

def DvR (v : PowerSeries R) (i : σ) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  PowerSeries.subst (MvPowerSeries.X i) v * MvPowerSeries.pderiv R i f

theorem subst_one' (a : MvPowerSeries σ R) : PowerSeries.subst a (1 : PowerSeries R) = 1 := by
  simpa using PowerSeries.subst_C (a := a) (1 : R)

private theorem powerSeries_hasSubst_mvPowerSeries_X (i : σ) : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ R) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)

theorem subst_v_mul {l v : PowerSeries R} (hv : v * dX l = 1) (i : σ) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ R) v *
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ R) (dX l) = 1 := by
  rw [← PowerSeries.subst_mul (powerSeries_hasSubst_mvPowerSeries_X i), hv, subst_one']

end Chain

end PI.JetsPhW.Ch
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.ExpLow
section
noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

variable {p : ℕ} [Fact p.Prime]

theorem coeff_truncatedExp_of_degree_eq_one {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) {e : σ →₀ ℕ}
    (hd : Finsupp.degree e = 1) :
    MvPowerSeries.coeff e (expMv F) = MvPowerSeries.coeff e F := by
  classical
  have he : e ≠ 0 := by
    rintro rfl
    simp at hd
  have h1 : (e.sum fun _ k => k) = 1 := by
    rw [← hd]
    rfl
  change (∑ n ∈ Finset.range ((e.sum fun _ k => k) + 1),
    MvPowerSeries.coeff e (F ^ n) / (n.factorial : ℂ_[p])) = _
  rw [h1, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, MvPowerSeries.coeff_one, if_neg he]
  simp

theorem norm_two (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp)
  have e : (2 : ℂ_[p]) = ((algebraMap ℚ_[p] (PadicAlgCl p) ((2 : ℕ) : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    rw [map_natCast, PadicComplex.coe_natCast]
    norm_num
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends, h]

end PI.JetsPhW.Low
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.InvOmega
section
noncomputable section

open Classical

namespace PI.JetsPhW.Inv

variable {p : ℕ} [Fact p.Prime]

noncomputable def intS (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  _root_.UpperTheory.Reformulated.B.PadicComplexValuationRing.intS p

theorem coeff_mul_memS {S : Subring ℂ_[p]} {f g : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (hg : ∀ i ≤ m, PowerSeries.coeff i g ∈ S) :
    PowerSeries.coeff m (f * g) ∈ S := by
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun x hx => S.mul_mem (hf _ ?_) (hg _ ?_)
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega

theorem coeff_pow_memS {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (k : ℕ) : ∀ i ≤ m, PowerSeries.coeff i (f ^ k) ∈ S := by
  induction k with
  | zero =>
    intro i _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  | succ k ih =>
    intro i hi
    rw [pow_succ]
    exact coeff_mul_memS (fun j hj => ih j (hj.trans hi)) (fun j hj => hf j (hj.trans hi))

theorem coeff_termS (a : ℂ_[p]) (k n : ℕ) (f : PowerSeries ℂ_[p]) :
    PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ k * f) =
      if k ≤ n then a * PowerSeries.coeff (n - k) f else 0 := by
  rw [PowerSeries.algebraMap_apply, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs <;> simp

theorem wq_mem {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    ∀ n, PowerSeries.coeff n wq ∈ S := by
  simp only [IsWq] at h
  have h' : wq = 1 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X ^ 1 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * PowerSeries.X ^ 2 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := by
    rw [pow_one]; exact h
  have key : ∀ n, (∀ i < n, PowerSeries.coeff i wq ∈ S) → PowerSeries.coeff n wq ∈ S := by
    intro n ih
    rw [h']
    simp only [map_add, coeff_termS, PowerSeries.coeff_one]
    refine S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem ?_ ?_) ?_) ?_) ?_) ?_
    · split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h1 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h2 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h3 (coeff_pow_memS (m := n - 3) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h4 (coeff_pow_memS (m := n - 4) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h6 (coeff_pow_memS (m := n - 6) (fun i hi => ih i (by omega)) 3 _ le_rfl)
      · exact S.zero_mem
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn => exact key n ihn

theorem wq_const {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.constantCoeff wq = 1 := by
  simp only [IsWq] at h
  have := congrArg PowerSeries.constantCoeff h
  simpa using this

def serS (S : Subring ℂ_[p]) : Subring (PowerSeries ℂ_[p]) where
  carrier := {f | ∀ n, PowerSeries.coeff n f ∈ S}
  mul_mem' {f g} hf hg n := coeff_mul_memS (fun i _ => hf i) (fun i _ => hg i)
  one_mem' n := by
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  add_mem' {f g} hf hg n := by
    rw [map_add]; exact S.add_mem (hf n) (hg n)
  zero_mem' n := by simp
  neg_mem' {f} hf n := by
    rw [map_neg]; exact S.neg_mem (hf n)

theorem X_mem_serS (S : Subring ℂ_[p]) : (PowerSeries.X : PowerSeries ℂ_[p]) ∈ serS S := by
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

theorem C_mem_serS {S : Subring ℂ_[p]} {a : ℂ_[p]} (ha : a ∈ S) :
    algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a ∈ serS S := by
  intro n
  rw [PowerSeries.algebraMap_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, PowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact S.zero_mem

theorem dX_eq_derivative (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative ℂ_[p] f := by
  ext n
  simp only [dX, PowerSeries.coeff_mk, PowerSeries.coeff_derivative]
  ring

theorem dX_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    dX (flog W wq) = omegaW W wq := by
  ext n
  simp only [dX, PowerSeries.coeff_mk, flog, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
  have h : ((n : ℂ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

def vInv (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  1 - (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
    algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * PowerSeries.X ^ 2 +
    2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X ^ 3 * wq) +
    2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * PowerSeries.X * (PowerSeries.X ^ 3 * wq) +
    3 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * (PowerSeries.X ^ 3 * wq) ^ 2)

theorem vInv_mul_omega {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    vInv W wq * omegaW W wq = 1 := by
  have hc := wq_const h
  simp only [IsWq] at h
  have hd : PowerSeries.derivative ℂ_[p] wq =
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (wq + PowerSeries.X * PowerSeries.derivative ℂ_[p] wq) +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ *
        (2 * PowerSeries.X * wq + PowerSeries.X ^ 2 * PowerSeries.derivative ℂ_[p] wq) +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ *
        (3 * PowerSeries.X ^ 2 * wq ^ 2 + 2 * PowerSeries.X ^ 3 * wq * PowerSeries.derivative ℂ_[p] wq) +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ *
        (4 * PowerSeries.X ^ 3 * wq ^ 2 + 2 * PowerSeries.X ^ 4 * wq * PowerSeries.derivative ℂ_[p] wq) +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ *
        (6 * PowerSeries.X ^ 5 * wq ^ 3 + 3 * PowerSeries.X ^ 6 * wq ^ 2 * PowerSeries.derivative ℂ_[p] wq) := by
    conv_lhs => rw [h]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
      PowerSeries.derivative_X, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul]
    norm_num
    ring
  have hden : PowerSeries.constantCoeff (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2)) ≠ 0 := by
    simp [hc]
    rw [map_ofNat]
    norm_num
  have key : vInv W wq * (-(2 : PowerSeries ℂ_[p]) * wq - PowerSeries.X * dX wq) =
      wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2) := by
    rw [dX_eq_derivative]
    simp only [vInv]
    linear_combination (-(PowerSeries.X : PowerSeries ℂ_[p])) * hd
  simp only [omegaW]
  rw [← mul_assoc, key, PowerSeries.mul_inv_cancel _ hden]

theorem vInv_mem {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : IsIntP W.a₁) (h2 : IsIntP W.a₂) (h3 : IsIntP W.a₃) (h4 : IsIntP W.a₄) (h6 : IsIntP W.a₆)
    (h : IsWq W wq) : vInv W wq ∈ serS (intS p) := by
  have hw : wq ∈ serS (intS p) := wq_mem (S := intS p) h1 h2 h3 h4 h6 h
  have hX := X_mem_serS (intS p)
  have c1 := C_mem_serS (S := intS p) h1
  have c2 := C_mem_serS (S := intS p) h2
  have c3 := C_mem_serS (S := intS p) h3
  have c4 := C_mem_serS (S := intS p) h4
  have c6 := C_mem_serS (S := intS p) h6
  have t2 : (2 : PowerSeries ℂ_[p]) ∈ serS (intS p) := by
    exact_mod_cast natCast_mem (serS (intS p)) 2
  have t3 : (3 : PowerSeries ℂ_[p]) ∈ serS (intS p) := by
    exact_mod_cast natCast_mem (serS (intS p)) 3
  have hw3 : PowerSeries.X ^ 3 * wq ∈ serS (intS p) := Subring.mul_mem _ (Subring.pow_mem _ hX 3) hw
  simp only [vInv]
  refine Subring.sub_mem _ (Subring.one_mem _) ?_
  refine Subring.add_mem _ (Subring.add_mem _ (Subring.add_mem _ (Subring.add_mem _ ?_ ?_) ?_) ?_) ?_
  · exact Subring.mul_mem _ c1 hX
  · exact Subring.mul_mem _ c2 (Subring.pow_mem _ hX 2)
  · exact Subring.mul_mem _ (Subring.mul_mem _ t2 c3) hw3
  · exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ t2 c4) hX) hw3
  · exact Subring.mul_mem _ (Subring.mul_mem _ t3 c6) (Subring.pow_mem _ hw3 2)

theorem inverse_omega_holds : InvOmega :=
  _root_.UpperTheory.Reformulated.B.Gwa1.inverse_omega_holds

end PI.JetsPhW.Inv
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.TwoUnit
section
noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

def Dv {p : ℕ} [Fact p.Prime] {σ : Type*} (v : PowerSeries ℂ_[p]) (i : σ)
    (f : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) v * MvPowerSeries.pderiv ℂ_[p] i f

def psi {p : ℕ} [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  PowerSeries.subst ex ph

def IntP {p : ℕ} [Fact p.Prime] (g : PowerSeries ℂ_[p]) : Prop :=
  ∀ n, IsIntP (PowerSeries.coeff n g)

def Chain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (s : MvPowerSeries σ ℂ_[p]) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.pderiv ℂ_[p] i (PowerSeries.subst s g) =
      MvPowerSeries.pderiv ℂ_[p] i s * PowerSeries.subst s (dX g)

def DChain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (l v g : PowerSeries ℂ_[p]) (s : MvPowerSeries σ ℂ_[p])
    (c : ℂ_[p]), v * dX l = 1 → MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.pderiv ℂ_[p] i s =
      MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (dX l) →
    Dv v i (PowerSeries.subst s g) = MvPowerSeries.C c * PowerSeries.subst s (dX g)

def PdSelf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.pderiv ℂ_[p] i (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (dX g)

def PdNe : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i j : σ) (g : PowerSeries ℂ_[p]), j ≠ i →
    MvPowerSeries.pderiv ℂ_[p] i (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ ℂ_[p]) g) = 0

def DSelf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v g : PowerSeries ℂ_[p]),
    Dv v i (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (v * dX g)

def Ev0 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (s : MvPowerSeries σ ℂ_[p]) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.constantCoeff (PowerSeries.subst s g) = PowerSeries.constantCoeff g

def Coef1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a g : PowerSeries ℂ_[p]), PowerSeries.constantCoeff a = 0 →
    PowerSeries.coeff 1 (PowerSeries.subst a g : PowerSeries ℂ_[p]) =
      PowerSeries.coeff 1 g * PowerSeries.coeff 1 a

def JetD : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) (n : ℕ),
    jet ex ph n = PowerSeries.constantCoeff ((dX (A := ℂ_[p]))^[n] (psi ex ph))

def LogDer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v : PowerSeries ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    IntP v → MvPowerSeries.constantCoeff f = 0 → IntegralMv (expMv f) → IntegralMv (Dv v i f)

def Dint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v : PowerSeries ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    IntP v → IntegralMv f → IntegralMv (Dv v i f)

def RwAdd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (l ex ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
    phAt ph (add l ex a b) = PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) (psi ex ph)

def RwMul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (l ex ph : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    MvPowerSeries.constantCoeff a = 0 →
    phAt ph (mulBy l ex c a) = PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) (psi ex ph)

abbrev lX {p : ℕ} [Fact p.Prime] {σ : Type*} (l : PowerSeries ℂ_[p]) (j : σ) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ ℂ_[p]) l

def Rw3 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex →
    cubeE l ex ph =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) +
        phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2)

def Rw1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex →
    (phAt ph (mulBy l ex (-1) (Xv ())) - phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.subst (MvPowerSeries.C (-1) * lX l () : MvPowerSeries Unit ℂ_[p]) (psi ex ph) -
        phAt ph (Xv ())

def Rw2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (a b : ℂ_[p]), LogOk l ex →
    (be l ex ph (mulBy l ex a (Xv 0)) (Xv 1) - be l ex ph (Xv 0) (mulBy l ex b (Xv 1)) :
      MvPowerSeries (Fin 2) ℂ_[p]) =
      PowerSeries.subst (MvPowerSeries.C a * lX l 0 + lX l 1 : MvPowerSeries (Fin 2) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (MvPowerSeries.C a * lX l 0 : MvPowerSeries (Fin 2) ℂ_[p]) (psi ex ph) -
        phAt ph (Xv 1) -
        PowerSeries.subst (lX l 0 + MvPowerSeries.C b * lX l 1 : MvPowerSeries (Fin 2) ℂ_[p]) (psi ex ph) +
        phAt ph (Xv 0) +
        PowerSeries.subst (MvPowerSeries.C b * lX l 1 : MvPowerSeries (Fin 2) ℂ_[p]) (psi ex ph)

def TwoUnit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ‖(2 : ℂ_[p])‖ = 1

end PI.JetsPhW.W
end
end

