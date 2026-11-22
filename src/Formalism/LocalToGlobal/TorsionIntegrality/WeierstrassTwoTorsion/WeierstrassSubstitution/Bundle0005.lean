import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0005
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0004

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ChainRuleFormalGroupVar
section
open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace More

section Tools

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem map_derivative (φ : R →+* S) (f : R⟦X⟧) :
    PowerSeries.map φ (derivative R f) = derivative S (PowerSeries.map φ f) := by
  ext n
  simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map]

theorem map_subst' (φ : R →+* S) {s : R⟦X⟧} (hs : HasSubst s) (f : R⟦X⟧) :
    PowerSeries.map φ (f.subst s) = (PowerSeries.map φ f).subst (PowerSeries.map φ s) := by
  first
    | exact PowerSeries.map_subst hs φ f
    | exact PowerSeries.map_subst hs f
    | exact PowerSeries.map_subst φ hs f
    | exact (PowerSeries.subst_map hs φ f).symm

variable (W : WeierstrassCurve R)

end Tools

end More

open More

namespace More

end More

namespace More

end More

namespace More

theorem iterate_derivative_subst {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
    (n : ℕ) (f : K⟦X⟧) :
    (derivative K)^[n] (f.subst (expSer W)) = ((D W)^[n] f).subst (expSer W) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    first
    | exact chainZ_of integration_spec composition_inverse_spec invariant_differential_units K W _
    | exact chainZ_of integration_spec.{u} composition_inverse_spec.{u} invariant_differential_units.{u} K W _

end More

private theorem constantCoeff_powerSeries_subst_eq_zero {R : Type u} [CommRing R] {a : R⟦X⟧} (ha : HasSubst a)
    (ha0 : constantCoeff a = 0) (g : R⟦X⟧) :
    constantCoeff (g.subst a) = constantCoeff g := by
  obtain ⟨h, hh⟩ := (PowerSeries.X_dvd_iff).mpr
    (show constantCoeff (g - C (constantCoeff g)) = 0 by simp)
  have hg : g = X * h + (constantCoeff g) • (1 : R⟦X⟧) := by
    rw [PowerSeries.smul_eq_C_mul, mul_one, ← hh]; ring
  rw [hg, ← PowerSeries.coe_substAlgHom ha, map_add, map_mul, map_smul, map_one,
    PowerSeries.coe_substAlgHom ha, PowerSeries.subst_X ha]
  simp [ha0, PowerSeries.smul_eq_C_mul]

private theorem factorial_mul_coeff_eq_coeff_zero_iterate_derivative {R : Type u} [CommRing R] (n : ℕ) (g : R⟦X⟧) :
    (n.factorial : R) * coeff n g = coeff 0 ((derivative R)^[n] g) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ← ih, PowerSeries.coeff_derivative, Nat.factorial_succ]
    push_cast
    ring

theorem jet_integral : JetZ.{u} := by
  intro K _ _ W f n
  have hE0 : constantCoeff (expSer W) = 0 := by
    first
    | exact (expSpec_of integration_spec composition_inverse_spec invariant_differential_units K W).1
    | exact (formal_exponential_spec K W).1
  have hs : HasSubst (expSer W) := by
    first
    | exact HasSubst.of_constantCoeff_zero' hE0
    | exact HasSubst.of_constantCoeff_zero hE0
  rw [factorial_mul_coeff_eq_coeff_zero_iterate_derivative, More.iterate_derivative_subst, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_powerSeries_subst_eq_zero hs hE0]

namespace More

variable {K : Type u} [Field K] (W : WeierstrassCurve K) (S : Subring K)

theorem fw_mem (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S)
    (n : ℕ) : coeff n (fw W) ∈ S := by
  have e : (⟨⟨W.a₁, h1⟩, ⟨W.a₂, h2⟩, ⟨W.a₃, h3⟩, ⟨W.a₄, h4⟩, ⟨W.a₆, h6⟩⟩ :
      WeierstrassCurve S).map S.subtype = W := by
    ext <;> rfl
  rw [← e, ← CurveSer.map_fw, coeff_map]
  exact SetLike.coe_mem _

theorem D_mem (hw : ∀ n, coeff n (fw W) ∈ S) (f : K⟦X⟧) (hf : ∀ n, coeff n f ∈ S) (n : ℕ) :
    coeff n (D W f) ∈ S := by
  have e1 : D W f = fw W * derivative K f := by
    simp only [D, Derivation.smul_apply, smul_eq_mul]
  rw [e1, PowerSeries.coeff_mul]
  refine Subring.sum_mem S fun p _ => Subring.mul_mem S (hw _) ?_
  rw [PowerSeries.coeff_derivative]
  exact Subring.mul_mem S (hf _) (Subring.add_mem S (natCast_mem S _) (Subring.one_mem S))

theorem iterate_D_mem (hw : ∀ n, coeff n (fw W) ∈ S) (k : ℕ) (f : K⟦X⟧)
    (hf : ∀ n, coeff n f ∈ S) (n : ℕ) : coeff n ((D W)^[k] f) ∈ S := by
  induction k generalizing f n with
  | zero => exact hf n
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact D_mem W S hw _ (fun m => ih f hf m) n

end More

theorem jet_mem' : JetMem.{u} := by
  intro K _ _ W S h1 h2 h3 h4 h6
  have hw := fw_mem W S h1 h2 h3 h4 h6
  have hsec : ∀ f : K⟦X⟧, (∀ n, coeff n f ∈ S) → ∀ n : ℕ,
      (n.factorial : K) * coeff n (f.subst (expSer W)) ∈ S := by
    intro f hf n
    rw [jet_integral K W f n, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact iterate_D_mem W S hw n f hf 0
  refine ⟨fun f hf n => D_mem W S hw f hf n, hsec, fun n => ?_⟩
  have hE0 : constantCoeff (expSer W) = 0 := by
    first
    | exact (expSpec_of integration_spec composition_inverse_spec invariant_differential_units K W).1
    | exact (formal_exponential_spec K W).1
  have hs : HasSubst (expSer W) := by
    first
    | exact HasSubst.of_constantCoeff_zero' hE0
    | exact HasSubst.of_constantCoeff_zero hE0
  have hX : ∀ m, coeff m (X : K⟦X⟧) ∈ S := fun m => by
    rw [PowerSeries.coeff_X]
    split_ifs
    · exact one_mem S
    · exact zero_mem S
  have h := hsec X hX n
  rwa [PowerSeries.subst_X hs] at h

theorem weierstrass_p_prime_shape : WpPrimeShape.{u} := by
  intro K _ _ W
  obtain ⟨e0, e1, -⟩ := expSpec K W
  have he : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' e0
  have hne : toL (expSer W) ≠ 0 := by
    intro h
    have h0 : expSer W = 0 := toL_injective (by rw [h, map_zero])
    rw [h0] at e1
    simp at e1
  constructor
  · rw [(wpShape K W).1, map_add, dL_uPow, dL_toL, WpSh.C_neg_two]
    norm_num
  · have h2 : (toL (expSer W))⁻¹ * toL (expSer W) = 1 := inv_mul_cancel₀ hne
    have h3 : Wp.sig he (wU W) * Wp.sig he (xS W) = 1 := by
      rw [← map_mul, CurveSer.wU_mul_xS, map_one]
    rw [yZ, ← Wp.sig_apply he, ← Wp.sig_apply he, CurveSer.wSer_eq, yS, map_mul, map_pow, map_neg,
      Wp.sig_X]
    linear_combination (-(Wp.sig he (wU W) * Wp.sig he (xS W)) *
      (((toL (expSer W))⁻¹ * toL (expSer W)) ^ 2 + (toL (expSer W))⁻¹ * toL (expSer W) + 1)) * h2
      - h3

namespace More

variable {K : Type u} {L : Type v} [Field K] [Field L] (φ : K →+* L)

theorem map_integ (f : K⟦X⟧) : PowerSeries.map φ (integ f) = integ (PowerSeries.map φ f) := by
  ext n
  simp only [integ, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp [map_div₀]

theorem map_logSer (W : WeierstrassCurve K) :
    PowerSeries.map φ (logSer W) = logSer (W.map φ) := by
  rw [logSer, map_integ, CurveSer.map_om, logSer]

theorem map_g₂ (W : WeierstrassCurve K) : φ (g₂ W) = g₂ (W.map φ) := by
  simp [g₂, map_div₀, WeierstrassCurve.map_c₄, map_ofNat]

theorem map_g₃ (W : WeierstrassCurve K) : φ (g₃ W) = g₃ (W.map φ) := by
  simp [g₃, map_div₀, WeierstrassCurve.map_c₆, map_ofNat]

theorem map_cleared {g2 g3 : K} {r : K⟦X⟧} (h : WpSh.Cleared g2 g3 r) :
    WpSh.Cleared (φ g2) (φ g3) (PowerSeries.map φ r) := by
  unfold WpSh.Cleared at h ⊢
  have h' := congrArg (PowerSeries.map φ) h
  simpa [map_derivative, PowerSeries.map_X, PowerSeries.map_C, map_ofNat] using h'

end More

theorem z_series_map_spec : ZMap.{u, v} := by
  intro K L _ _ _ _ φ W
  obtain ⟨l0, l1, -⟩ := logSpec K W
  refine ⟨map_logSer φ W, ?_, ?_, map_g₂ φ W, map_g₃ φ W⟩
  · rw [expSer, compInvMap K L φ (logSer W) l0 (by rw [l1]; exact isUnit_one), map_logSer, expSer]
  · have h1 := map_cleared φ (WpSh.wpL_shape expSpec wpODE W).2
    rw [map_g₂, map_g₃] at h1
    exact WpSh.cleared_unique h1 (WpSh.wpL_shape expSpec wpODE (W.map φ)).2

end Formalism.L2.Th1.A
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.DivisionLogarithm
section
open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

theorem division_spec : DivSpec.{u, v} := by
  intro R _ W n hn
  obtain ⟨hcc, hc1⟩ := (zSerSpec R W).1 n
  have hu : IsUnit (coeff 1 (zSer W n)) := by rw [hc1]; exact hn
  obtain ⟨h0, hr, hl, h1, -, -⟩ := compInvSpec R (zSer W n) hcc hu
  refine ⟨h0, ?_, hr, hl, ?_, ?_⟩
  · rw [hc1] at h1
    rw [mul_comm]; exact h1
  · intro S _ φ
    have key := compInvMap R S φ (zSer W n) hcc hu
    rw [zSerMap R S φ W n] at key
    exact key
  · intro h2
    subst h2
    rfl

section Double

variable {A : Type u} [CommRing A]

end Double

end Formalism.L2.Th1.A
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.XPowSuccDvdOfDerivative
section
open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace Nn

section Unique

variable {R : Type u} [CommRing R]

theorem X_pow_succ_dvd_of_derivative
    (hR : ∀ (n : ℕ) (r : R), n ≠ 0 → (n : R) * r = 0 → r = 0) {f : R⟦X⟧} {n : ℕ}
    (h0 : constantCoeff f = 0) (h : X ^ n ∣ derivative R f) : X ^ (n + 1) ∣ f := by
  rw [PowerSeries.X_pow_dvd_iff] at h ⊢
  intro m hm
  rcases m with _ | k
  · simpa using h0
  · have hk := h k (by omega)
    rw [PowerSeries.coeff_derivative] at hk
    apply hR (k + 1) _ (Nat.succ_ne_zero k)
    rw [mul_comm]
    exact_mod_cast hk

theorem eq_zero_of_forall_X_pow_dvd {f : R⟦X⟧} (h : ∀ n : ℕ, X ^ n ∣ f) : f = 0 := by
  ext n
  have h1 := (PowerSeries.X_pow_dvd_iff).mp (h (n + 1)) n (Nat.lt_succ_self n)
  simpa using h1

end Unique

end Nn

open Nn

theorem flow_unique : FlowUnique.{u} := by
  rintro R _ W x y x' y' hR ⟨-, hx, hy⟩ ⟨-, hx', hy'⟩ h0x h0y
  have hfo : fw W * om W = 1 := (invariant_differential_units R W).2.1
  have eD : ∀ g : R⟦X⟧, derivative R g = om W * D W g := fun g => by
    simp only [D, Derivation.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm (om W), hfo, one_mul]
  have key : ∀ n : ℕ, X ^ n ∣ x - x' ∧ X ^ n ∣ y - y' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
      constructor
      · apply X_pow_succ_dvd_of_derivative hR (by rw [map_sub, h0x, sub_self])
        refine ⟨om W * (2 * b + (curveS W).a₁ * a), ?_⟩
        rw [map_sub, eD x, eD x', hx, hx']
        linear_combination (2 * om W) * hb + ((curveS W).a₁ * om W) * ha
      · apply X_pow_succ_dvd_of_derivative hR (by rw [map_sub, h0y, sub_self])
        refine ⟨om W * (3 * (x + x') * a + 2 * (curveS W).a₂ * a - (curveS W).a₁ * b), ?_⟩
        rw [map_sub, eD y, eD y', hy, hy']
        linear_combination (om W * (3 * (x + x') + 2 * (curveS W).a₂)) * ha
          - ((curveS W).a₁ * om W) * hb
  constructor
  · exact sub_eq_zero.mp (eq_zero_of_forall_X_pow_dvd fun n => (key n).1)
  · exact sub_eq_zero.mp (eq_zero_of_forall_X_pow_dvd fun n => (key n).2)

theorem chord_equation : ChordEquation.{u} := by
  intro R _ W xP yP xQ yQ t hP hQ ht
  rw [WeierstrassCurve.Affine.equation_iff] at hP hQ
  have hL : (yP - yQ) * t * (xP - xQ) = yP - yQ := by linear_combination (yP - yQ) * ht
  obtain ⟨hc1, hc0⟩ := chord_rel hP hQ ht hL
  generalize (yP - yQ) * t = L at hL hc1 hc0 ⊢
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX]
  linear_combination -(L ^ 2 + W.a₁ * L - W.a₂ - xP - xQ) * hc1 - hc0

theorem addition_addition : PlusPlus.{u} := by
  intro R _ W xP yP xQ yQ t hR hP hQ ht s hs
  obtain ⟨hDer, hConst, -, -, -, -⟩ := flowU R W
  obtain ⟨hFP, hxP0, hyP0⟩ := plusFlow R W xP yP hP
  have hPQ := chord_equation R W xP yP xQ yQ t hP hQ ht
  obtain ⟨hFS, hxS0, hyS0⟩ := plusFlow R W _ _ hPQ
  have hDC : ∀ r : R, D W (C r) = 0 := fun r => by
    rw [CurveSer.D_apply, derivative_C, mul_zero]
  have hQC : (curveS W).toAffine.Equation (C xQ) (C yQ) :=
    WeierstrassCurve.Affine.Equation.map (C : R →+* R⟦X⟧) hQ
  have hFT := flowTranslate _ (curveS W) (D W) (xPlus W xP yP) (yPlus W xP yP) (C xQ) (C yQ) s
    hDer hConst hFP hQC (hDC xQ) (hDC yQ) hs
  have hs0 : constantCoeff s = t := by
    have h := congrArg (constantCoeff (R := R)) hs
    rw [map_mul, map_sub, hxP0, constantCoeff_C, map_one] at h
    linear_combination t * h - constantCoeff s * ht
  refine flow_unique R W _ _ _ _ hR hFS hFT ?_ ?_
  · rw [hxS0]
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      map_add, map_sub, map_mul, map_pow, constantCoeff_C, hxP0, hyP0, hs0]
  · rw [hyS0]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      map_add, map_sub, map_neg, map_mul, map_pow, constantCoeff_C, hxP0, hyP0, hs0]

theorem addition_neg_y : PlusNegY.{u} := by
  intro R _ W xP yP _
  have hI : ISerSpec.{u} := iSerSpec
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hi0, -, -, -, -, hy, -, -⟩ := hI R W
    have hv := Plus.inv_subst W xP hI
    have hn := Plus.nS_subst W xP yP hI
    have hxp := Plus.xPlus_subst W xP yP hI
    have hqr := CurveSer.iDen_mul_inv W
    have htv := Plus.tDen_mul_inv W xP
    rw [← Plus.subHom_apply _ hi0] at hv hn hxp hy ⊢
    have φX : Plus.subHom (iSer W) hi0 X = X * invOfUnit (iDen W) (-1) := Plus.subHom_X _ _
    rw [yPlus, map_sub, map_sub, map_sub, map_neg, map_mul, map_mul, map_mul, map_sub, map_mul,
      map_pow, map_pow, Plus.subHom_C, Plus.subHom_C, Plus.subHom_C, φX, hv, hn, hxp, hy]
    simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    rw [yPlus]
    have hx' : xPlus W xP (W.toAffine.negY xP yP) = C xP
        + X * nS W xP (W.toAffine.negY xP yP) * invOfUnit (tDen W xP) 1 ^ 2 := rfl
    simp only [WeierstrassCurve.Affine.negY] at hx' ⊢
    rw [hx']
    simp only [map_sub, map_neg, map_mul]
    generalize nS W xP (-yP - W.a₁ * xP - W.a₃) = n'
    generalize invOfUnit (iDen W) (-1) = r at hqr
    generalize invOfUnit (tDen W xP) 1 = v at htv
    generalize iDen W = q at hqr
    rw [tDen] at htv
    linear_combination (yS W + C W.a₁ * X * xS W + C W.a₃ * X ^ 3 + C yP * X ^ 3) * n' * v ^ 3
        * ((q * r) ^ 5 + (q * r) ^ 4 + (q * r) ^ 3 + (q * r) ^ 2 + q * r + 1) * hqr
      + C W.a₁ * X * n' * v ^ 2 * htv
  · simp only [xPlus, tS, nS, WeierstrassCurve.Affine.negY, map_add, map_sub, map_neg, map_mul,
      map_pow, map_ofNat]
    ring
  · rw [xPlus, map_add, coeff_C, if_neg one_ne_zero, zero_add, mul_assoc, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, Plus.nS_cc, Plus.inv_cc]
    ring

theorem expSeriesAdd : ExpAdd.{u} := by
  intro K _ _ W
  obtain ⟨l0, -, -, -⟩ := logSpec K W
  obtain ⟨e0, -, hle, -, -⟩ := expSpec K W
  have c0 : MvPowerSeries.constantCoeff (U₁ : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (U₂ : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hU0 : HasSubst (U₁ : MvPowerSeries (Fin 2) K) := HasSubst.of_constantCoeff_zero c0
  have hU1 : HasSubst (U₂ : MvPowerSeries (Fin 2) K) := HasSubst.of_constantCoeff_zero c1
  have he : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' e0
  have ce0 : MvPowerSeries.constantCoeff ((expSer W).subst (U₁ : MvPowerSeries (Fin 2) K)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero c0 _ e0
  have ce1 : MvPowerSeries.constantCoeff ((expSer W).subst (U₂ : MvPowerSeries (Fin 2) K)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero c1 _ e0
  have hb : MvPowerSeries.HasSubst (![(expSer W).subst (U₁ : MvPowerSeries (Fin 2) K),
      (expSer W).subst (U₂ : MvPowerSeries (Fin 2) K)] : Fin 2 → MvPowerSeries (Fin 2) K) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
      fin_cases s
      · exact ce0
      · exact ce1)
  have cl : MvPowerSeries.constantCoeff ((logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K)) = 0 := by
    rw [map_add, PowerSeries.constantCoeff_subst_eq_zero c0 _ l0,
      PowerSeries.constantCoeff_subst_eq_zero c1 _ l0, add_zero]
  have k0 : (logSer W).subst ((expSer W).subst (U₁ : MvPowerSeries (Fin 2) K)) = U₁ := by
    have key := subst_comp_subst_apply he hU0 (logSer W)
    rw [hle, subst_X hU0] at key
    exact key.symm
  have k1 : (logSer W).subst ((expSer W).subst (U₂ : MvPowerSeries (Fin 2) K)) = U₂ := by
    have key := subst_comp_subst_apply he hU1 (logSer W)
    rw [hle, subst_X hU1] at key
    exact key.symm
  conv_rhs => rw [(fglLog K W).2]
  rw [Fgl2.mvsubst_psubst (HasSubst.of_constantCoeff_zero cl) hb, MvPowerSeries.subst_add hb,
    Fgl2.mvsubst_psubst hU0 hb, Fgl2.mvsubst_psubst hU1 hb, MvPowerSeries.subst_X hb,
    MvPowerSeries.subst_X hb]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [k0, k1]

theorem plusZCleared_of (hZ : PlusZ.{u}) (hT : TInZ.{u}) : PlusZCleared.{u} := by
  intro K _ _ W xP yP hP
  obtain ⟨-, -, hlog⟩ := hZ K W xP yP hP
  have hT' := hT K W xP
  have hsh := (wpShape K W).1
  set P := wpReg W with hPdef
  set c : K := xP + W.b₂ / 12 with hc
  set T := (tS W xP).subst (expSer W) with hTdef
  set xp := (xPlus W xP yP).subst (expSer W) with hxp
  set xm := (xPlus W xP (W.toAffine.negY xP yP)).subst (expSer W) with hxm
  set f : K⟦X⟧ := 1 + X ^ 2 * (P - C c) with hf
  have hf0 : constantCoeff f = 1 := by simp [hf]
  set g : K⟦X⟧ := invOfUnit f 1 with hg
  have hfg : f * g = 1 := mul_invOfUnit _ _ (by rw [hf0, Units.val_one])
  have hTf : T * f = X ^ 2 := by rw [← hT', hf]; ring
  have hTg : T = X ^ 2 * g := by linear_combination g * hTf - T * hfg
  have hdf : X * derivative K f = 2 * (f - 1) + X ^ 3 * derivative K P := by
    rw [hf]
    simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
      derivative_C, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hdg : derivative K g = -g ^ 2 * derivative K f := by
    have h := congrArg (derivative K) hfg
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h
    linear_combination g * h - derivative K g * hfg
  have hz : (toL X : LaurentSeries K) * uPow (-1) = 1 := Plus.toL_X_mul
  have hxZ : xZ W = uPow (-2) + toL P - HahnSeries.C (W.b₂ / 12) := by
    rw [← hsh, wpL]; ring

  have hdwp : dL (wpL W) = uPow (-1) ^ 3 * (toL X * toL (derivative K f) - 2 * toL f) := by
    have h1 : toL X * toL (derivative K f) = 2 * (toL f - 1) + toL X ^ 3 * toL (derivative K P) := by
      rw [← map_mul, hdf]
      simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
    rw [hsh, map_add, dL_uPow, dL_toL, h1]
    have e3 : (uPow (-2 - 1) : LaurentSeries K) = uPow (-1) ^ 3 := by
      rw [← Plus.uPow_neg_three]; norm_num
    rw [e3]
    have e2 : (HahnSeries.C (((-2 : ℤ) : K)) : LaurentSeries K) = -2 := by
      push_cast
      rw [map_neg, map_ofNat]
    rw [e2]
    linear_combination (-toL (derivative K P)
      * ((toL X * uPow (-1)) ^ 2 + toL X * uPow (-1) + 1)) * hz
  have hprod : toL T * dL (wpL W) = toL (g * derivative K f) - 2 * uPow (-1) := by
    have hfg' : toL f * toL g = 1 := by rw [← map_mul, hfg, map_one]
    rw [hdwp, hTg, map_mul, map_mul, map_pow]
    linear_combination (toL g * toL (derivative K f) * ((toL X * uPow (-1)) ^ 2
        + toL X * uPow (-1) + 1) - 2 * toL g * toL f * uPow (-1) * (toL X * uPow (-1) + 1)) * hz
      - 2 * uPow (-1) * hfg'
  rw [hprod, map_sub, dL_toL, dL_mul, dL_uPow, hxZ] at hlog
  have e2' : (uPow (-1 - 1) : LaurentSeries K) = uPow (-2) := by norm_num
  have e1 : (HahnSeries.C (((-1 : ℤ) : K)) : LaurentSeries K) = -1 := by
    push_cast
    rw [map_neg, map_one]
  have d2 : dL (2 : LaurentSeries K) = 0 := by
    rw [← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 2, dL_C]
  rw [e2', e1, d2] at hlog
  have hmain : derivative K (g * derivative K f) = 2 * P - (xp + C (W.b₂ / 12))
      - (xm + C (W.b₂ / 12)) := by
    apply toL_injective
    simp only [map_add, map_sub, map_mul, map_ofNat, toL_C]
    linear_combination hlog
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hdg] at hmain
  rw [← hmain]
  linear_combination (-(derivative K (derivative K f)) * f
    + derivative K f ^ 2 * (f * g + 1)) * hfg

end Formalism.L2.Th1.A
end
end

