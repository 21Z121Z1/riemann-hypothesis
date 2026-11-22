import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.WeierstrassReducedEquations
import Formalism.GL3MeanSquares.HookFormulaTorsion.ExpSeries

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BaseChangeCompatible
section
noncomputable section

namespace Formalism.L2.Th1.B.Map

open Formalism.InvariantFactorPaths.G7 (at1 cob)

variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')

theorem map_psubst {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries K) :
    MvPowerSeries.map j (PowerSeries.subst a f) =
      PowerSeries.subst (MvPowerSeries.map j a) (PowerSeries.map j f) := by
  have ha' : MvPowerSeries.constantCoeff (MvPowerSeries.map j a) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, ha, map_zero]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have hs' := PowerSeries.HasSubst.of_constantCoeff_zero ha'
  ext e
  rw [MvPowerSeries.coeff_map, PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs',
    map_finsum j (PowerSeries.coeff_subst_finite hs f e)]
  refine finsum_congr fun d => ?_
  rw [smul_eq_mul, smul_eq_mul, map_mul, PowerSeries.coeff_map, ← map_pow (MvPowerSeries.map j),
    MvPowerSeries.coeff_map]

theorem map_psubst' {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0)
    (f : PowerSeries K) :
    PowerSeries.map j (PowerSeries.subst a f) =
      PowerSeries.subst (PowerSeries.map j a) (PowerSeries.map j f) :=
  map_psubst j (ι := Unit) ha f

theorem map_fExp {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.map j (fExp a) = fExp (MvPowerSeries.map j a) := by
  unfold Formalism.L2.Th1.B.fExp
  rw [map_psubst j ha, PowerSeries.map_exp]

theorem map_fExp' {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.map j (fExp a) = fExp (PowerSeries.map j a) :=
  map_fExp j (ι := Unit) ha

theorem map_fLog {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 1) :
    MvPowerSeries.map j (fLog a) = fLog (MvPowerSeries.map j a) := by
  have h' : MvPowerSeries.constantCoeff (a - 1) = 0 := by rw [map_sub, ha, map_one, sub_self]
  unfold Formalism.L2.Th1.B.fLog
  rw [map_psubst j h', map_sub, map_one, PowerSeries.map_log]

theorem map_fLog' {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 1) :
    PowerSeries.map j (fLog a) = fLog (PowerSeries.map j a) :=
  map_fLog j (ι := Unit) ha

theorem map_prim (f : PowerSeries K) :
    PowerSeries.map j (prim f) = prim (PowerSeries.map j f) := by
  ext n
  simp only [Formalism.L2.Th1.B.prim, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp [map_div₀, map_natCast]

theorem map_lU (l : PowerSeries K) :
    PowerSeries.map j (lU l) = lU (PowerSeries.map j l) := by
  ext n
  simp only [Formalism.L2.Th1.B.lU, PowerSeries.coeff_map, PowerSeries.coeff_mk]

private theorem powerSeries_constantCoeff_map' (f : PowerSeries K) :
    PowerSeries.constantCoeff (PowerSeries.map j f) = j (PowerSeries.constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map]

theorem map_inv' {f : PowerSeries K} (hf : PowerSeries.constantCoeff f ≠ 0) :
    PowerSeries.map j f⁻¹ = (PowerSeries.map j f)⁻¹ := by
  have h' : PowerSeries.constantCoeff (PowerSeries.map j f) ≠ 0 := by
    rw [powerSeries_constantCoeff_map']; exact (map_ne_zero j).mpr hf
  rw [PowerSeries.eq_inv_iff_mul_eq_one h', ← map_mul, PowerSeries.inv_mul_cancel _ hf, map_one]

theorem map_sigS (P : PowerSeries K) :
    PowerSeries.map j (sigS P) = sigS (PowerSeries.map j P) := by
  unfold Formalism.L2.Th1.B.sigS
  rw [map_neg, map_prim, map_prim]

theorem cc_sigS (P : PowerSeries K) : PowerSeries.constantCoeff (sigS P) = 0 := by
  unfold Formalism.L2.Th1.B.sigS
  rw [map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]

theorem map_sig1S (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.map j (sigmaOneSeries e1 kap w) = sigmaOneSeries (j e1) (j kap) (PowerSeries.map j w) := by
  unfold Formalism.L2.Th1.B.sigmaOneSeries
  rw [map_neg, map_prim, map_prim, map_add, map_mul, PowerSeries.map_C,
    PowerSeries.map_C]

theorem cc_sig1S (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.constantCoeff (sigmaOneSeries e1 kap w) = 0 := by
  unfold Formalism.L2.Th1.B.sigmaOneSeries
  rw [map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]

theorem map_sigma (P : PowerSeries K) :
    PowerSeries.map j (sigma P) = sigma (PowerSeries.map j P) := by
  unfold Formalism.L2.Th1.B.sigma
  rw [map_mul, PowerSeries.map_X, map_fExp' j (cc_sigS P),
    map_sigS]

theorem map_sgStar (s2 : K) (P : PowerSeries K) :
    PowerSeries.map j (sgStar s2 P) = sgStar (j s2) (PowerSeries.map j P) := by
  have hc : PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2)) = 0 := by
    simp
  unfold Formalism.L2.Th1.B.sgStar
  rw [map_mul, map_sigma, map_fExp' j hc, map_neg, map_mul, PowerSeries.map_C,
    map_pow, PowerSeries.map_X, map_div₀, map_ofNat]

theorem map_sigma1 (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.map j (sigma1 e1 kap w) = sigma1 (j e1) (j kap) (PowerSeries.map j w) := by
  unfold Formalism.L2.Th1.B.sigma1
  rw [map_fExp' j (cc_sig1S e1 kap w), map_sig1S]

theorem map_wOf (e1 : K) (P : PowerSeries K) :
    PowerSeries.map j (wOf e1 P) = wOf (j e1) (PowerSeries.map j P) := by
  have hc : PowerSeries.constantCoeff
      (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) ≠ 0 := by
    simp
  unfold Formalism.L2.Th1.B.wOf
  rw [map_mul, map_inv' j hc]
  simp only [map_pow, map_sub, map_add, map_one, map_mul, PowerSeries.map_X, PowerSeries.map_C]

theorem map_phO (s2 : K) (P : PowerSeries K) {l : PowerSeries K}
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    PowerSeries.map j (phO s2 P l) = phO (j s2) (PowerSeries.map j P) (PowerSeries.map j l) := by
  have hd : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU l) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.L2.Th1.B.lU, PowerSeries.coeff_mk, zero_add, h1]
  unfold Formalism.L2.Th1.B.phO
  rw [map_sub, map_add, map_neg, map_psubst' j h0, map_sigS, map_mul,
    PowerSeries.map_C, map_div₀, map_ofNat, map_pow, map_fLog' j hd, map_lU]

theorem map_phE (s2 e1 kap : K) (w : PowerSeries K) {l : PowerSeries K}
    (h0 : PowerSeries.constantCoeff l = 0) :
    PowerSeries.map j (phE s2 e1 kap w l) =
      phE (j s2) (j e1) (j kap) (PowerSeries.map j w) (PowerSeries.map j l) := by
  unfold Formalism.L2.Th1.B.phE
  rw [map_add, map_neg, map_psubst' j h0, map_sig1S, map_mul,
    PowerSeries.map_C, map_div₀, map_ofNat, map_pow]

theorem map_inVar {ι : Type} (x : ι) (f : PowerSeries K) :
    MvPowerSeries.map j (at1 x f) = at1 x (PowerSeries.map j f) := by
  unfold Formalism.InvariantFactorPaths.G7.at1
  rw [map_psubst j (MvPowerSeries.constantCoeff_X x), MvPowerSeries.map_X]

theorem map_cob {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) :
    MvPowerSeries.map j (cob F f) = cob (MvPowerSeries.map j F) (PowerSeries.map j f) := by
  unfold Formalism.InvariantFactorPaths.G7.cob
  rw [map_sub, map_sub, map_psubst j hF, map_inVar, map_inVar]

theorem baseChangeCompatible : BaseChange := by
  intro K K' _ _ _ _ j s2 e1 kap P w l F h0 h1 hF
  exact ⟨map_sigma j P, map_sgStar j s2 P, map_sigma1 j e1 kap w,
    map_wOf j e1 P, map_phO j s2 P h0 h1,
    map_phE j s2 e1 kap w h0, fun f => map_cob j hF f⟩

end Formalism.L2.Th1.B.Map
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSig1S
section
noncomputable section

namespace Formalism.L2.Th1.B.Sq

open PowerSeries

variable {K : Type} [Field K] [CharZero K]

theorem even_iff_rescale (f : PowerSeries K) :
    (∀ n, Odd n → coeff n f = 0) ↔ rescale (-1 : K) f = f := by
  constructor
  · intro h
    ext n
    rw [PowerSeries.coeff_rescale]
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow, one_mul]
    · rw [h n ho, mul_zero]
  · intro h n hn
    have h1 := congrArg (coeff n) h
    rw [PowerSeries.coeff_rescale, hn.neg_one_pow] at h1
    have h2 : (2 : K) * coeff n f = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

theorem rescale_fExp (a : K) {f : PowerSeries K} (hf : constantCoeff f = 0) :
    rescale a (fExp f) = fExp (rescale a f) := by
  rw [PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst]
  have hφ : ∀ _ : Unit, MvPowerSeries.constantCoeff (a • (PowerSeries.X : PowerSeries K)) = 0 := by
    intro _
    show PowerSeries.constantCoeff (a • (PowerSeries.X : PowerSeries K)) = 0
    rw [PowerSeries.smul_eq_C_mul]
    simp
  exact subst_fExp (φ := fun _ => (a • PowerSeries.X : PowerSeries K)) hφ hf

theorem fExp_even {f : PowerSeries K} (hf : constantCoeff f = 0)
    (h : ∀ n, Odd n → coeff n f = 0) : ∀ n, Odd n → coeff n (fExp f) = 0 := by
  rw [even_iff_rescale] at h ⊢
  rw [rescale_fExp _ hf, h]

theorem coeff_prim_succ (f : PowerSeries K) (n : ℕ) :
    coeff (n + 1) (prim f) = coeff n f / ((n + 1 : ℕ) : K) := by
  simp [prim, PowerSeries.coeff_mk]

theorem coeff_zero_prim (f : PowerSeries K) : coeff 0 (prim f) = 0 := by
  simp [prim, PowerSeries.coeff_mk]

theorem prim_prim_even {f : PowerSeries K} (h : ∀ n, Odd n → coeff n f = 0) :
    ∀ n, Odd n → coeff n (prim (prim f)) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ := hn
  rw [coeff_prim_succ]
  rcases k with _ | k
  · simp [coeff_zero_prim]
  · have e : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [e, coeff_prim_succ, h (2 * k + 1) ⟨k, rfl⟩]
    simp

theorem constantCoeff_sigS (P : PowerSeries K) : constantCoeff (sigS P) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, sigS, map_neg, coeff_zero_prim, neg_zero]

theorem constantCoeff_sig1S (e1 kap : K) (w : PowerSeries K) :
    constantCoeff (sigmaOneSeries e1 kap w) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, sigmaOneSeries, map_neg, coeff_zero_prim, neg_zero]

theorem sigmaSeriesOdd : SigmaOdd := by
  intro K _ _ P hP
  have hs : ∀ n, Odd n → coeff n (sigS P) = 0 := by
    intro n hn
    rw [sigS, map_neg, prim_prim_even hP n hn, neg_zero]
  have he := fExp_even (constantCoeff_sigS P) hs
  have h0 : PowerSeries.constantCoeff (fExp (sigS P) : PowerSeries K) = 1 :=
    constantCoeff_fExp (constantCoeff_sigS P)
  constructor
  · have h1 := PowerSeries.coeff_succ_X_mul 0 (fExp (sigS P) : PowerSeries K)
    simp only [zero_add] at h1
    rw [sigma, h1, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0
  · intro n hn
    rcases n with _ | m
    · simp [sigma]
    · rw [sigma, PowerSeries.coeff_succ_X_mul]
      exact he m (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hn))

theorem sigmaOneEven : Sigma1Even := by
  intro K _ _ e1 kap w hw
  have hf : ∀ n, Odd n → coeff n (PowerSeries.C e1 + PowerSeries.C kap * w) = 0 := by
    intro n hn
    have hn0 : n ≠ 0 := hn.pos.ne'
    simp [PowerSeries.coeff_C, hn0, PowerSeries.coeff_C_mul, hw n hn]
  have hs : ∀ n, Odd n → coeff n (sigmaOneSeries e1 kap w) = 0 := by
    intro n hn
    rw [sigmaOneSeries, map_neg, prim_prim_even hf n hn, neg_zero]
  exact ⟨constantCoeff_fExp (constantCoeff_sig1S e1 kap w), fExp_even (constantCoeff_sig1S e1 kap w) hs⟩

private theorem pd_unit_eq_dz (f : PowerSeries K) : pd () f = dz f := by
  ext n
  rw [PowerSeries.coeff_derivative,
    PowerSeries.coeff_def (s := Finsupp.single () n) (by simp), MvPowerSeries.coeff_pderiv,
    PowerSeries.coeff_def (s := Finsupp.single () (n + 1)) (by simp), ← Finsupp.single_add,
    Finsupp.single_eq_same]

theorem mul_dz_fLog {g : PowerSeries K} (hg : constantCoeff g = 1) : g * dz (fLog g) = dz g := by
  have h := mul_pd_fLog (ι := Unit) () (g := g) hg
  rwa [pd_unit_eq_dz, pd_unit_eq_dz] at h

private theorem dz_prim_eq_self (f : PowerSeries K) : dz (prim f) = f := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_prim_succ]
  push_cast
  exact div_mul_cancel₀ _ (Nat.cast_add_one_ne_zero n)

private theorem eq_of_constantCoeff_eq_of_dz_eq {F G : PowerSeries K} (h0 : constantCoeff F = constantCoeff G)
    (hd : dz F = dz G) : F = G := by
  ext n
  rcases n with _ | m
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0
  · have h := congrArg (coeff m) hd
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at h
    exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero m) h

theorem sigmaOneSquare : Sigma1Sq := by
  intro K _ _ g2 g3 e1 P hP hc
  obtain ⟨q, rfl⟩ : ∃ q, g2 = 4 * q := ⟨g2 / 4, by ring⟩
  have hk : (3 * e1 ^ 2 - 4 * q / 4 : K) = 3 * e1 ^ 2 - q := by ring
  rw [hk]
  obtain ⟨hR1, hR2⟩ := weierstrassReducedEquations K (4 * q) g3 P hP
  have h42 : (4 * q / 2 : K) = 2 * q := by ring
  rw [h42] at hR2
  have hcC : PowerSeries.C (4 * e1 ^ 3 - 4 * q * e1 - g3) = 0 := by rw [hc, map_zero]
  simp only [map_sub, map_mul, map_pow, map_ofNat] at hR1 hR2 hcC
  set w := wOf e1 P with hwdef
  set u : PowerSeries K := 1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2 with hudef
  have hu0 : constantCoeff u = 1 := by simp [hudef]
  have hwu : w * u = PowerSeries.X ^ 2 := by
    have e : w = PowerSeries.X ^ 2 * u⁻¹ := rfl
    rw [e, mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [hu0]; exact one_ne_zero), mul_one]
  set L : PowerSeries K := fLog u with hLdef
  have hL0 : constantCoeff L = 0 := constantCoeff_fLog hu0
  have huL : u * dz L = dz u := mul_dz_fLog hu0
  have hdu : dz u = 2 * PowerSeries.X * P + PowerSeries.X ^ 2 * dz P - 2 * PowerSeries.C e1 * PowerSeries.X := by
    simp [hudef, Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_X,
      PowerSeries.derivative_C]
    ring
  have hddu : dz (dz u) = 2 * P + 4 * PowerSeries.X * dz P + PowerSeries.X ^ 2 * dz (dz P) -
      2 * PowerSeries.C e1 := by
    have hd2 : PowerSeries.derivative K (2 : PowerSeries K) = 0 := by
      rw [show (2 : PowerSeries K) = PowerSeries.C 2 from (map_ofNat _ 2).symm]
      exact PowerSeries.derivative_C
    rw [hdu]
    simp [Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_X,
      PowerSeries.derivative_C, hd2]
    ring
  have hT : u * dz (dz u) - dz u ^ 2 =
      u ^ 2 * (2 * P - 2 * PowerSeries.C e1) -
        2 * (3 * PowerSeries.C e1 ^ 2 - PowerSeries.C q) * PowerSeries.X ^ 2 * u := by
    rw [hddu, hdu, hudef]
    linear_combination (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) * hR2 - hR1 -
      PowerSeries.X ^ 4 * hcC
  have hB : u * dz (dz L) + dz L * dz u = dz (dz u) := by
    have h := congrArg (PowerSeries.derivative K) huL
    rwa [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 (fun h => by rw [h] at hu0; simp at hu0)
  have hLdd : dz (dz L) = 2 * P - 2 * PowerSeries.C e1 - 2 * PowerSeries.C (3 * e1 ^ 2 - q) * w := by
    apply mul_left_cancel₀ hu2
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    linear_combination u * hB - dz u * huL + hT + 2 * (3 * PowerSeries.C e1 ^ 2 - PowerSeries.C q) * u * hwu
  have hp0 : ∀ f : PowerSeries K, constantCoeff (prim f) = 0 := fun f => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact coeff_zero_prim f
  have hL1 : constantCoeff (dz L) = 0 := by
    have h := congrArg PowerSeries.constantCoeff huL
    rw [map_mul, hu0, one_mul, hdu] at h
    simpa using h
  have hs0 := constantCoeff_sigS P
  have hs10 := constantCoeff_sig1S e1 (3 * e1 ^ 2 - q) w
  have hkey : sigmaOneSeries e1 (3 * e1 ^ 2 - q) w + sigmaOneSeries e1 (3 * e1 ^ 2 - q) w = sigS P + sigS P + L := by
    apply eq_of_constantCoeff_eq_of_dz_eq
    · rw [map_add, map_add, map_add, hs0, hs10, hL0]; ring
    · apply eq_of_constantCoeff_eq_of_dz_eq
      · simp only [map_add, sigmaOneSeries, sigS, map_neg, dz_prim_eq_self, hp0, hL1]
        ring
      · simp only [map_add, sigmaOneSeries, sigS, map_neg, dz_prim_eq_self, hLdd]
        ring
  have hsq : fExp (sigmaOneSeries e1 (3 * e1 ^ 2 - q) w) ^ 2 = fExp (sigS P + sigS P) * u := by
    have hss : MvPowerSeries.constantCoeff (sigS P + sigS P) = 0 := by
      rw [map_add]
      exact (show PowerSeries.constantCoeff (sigS P) + PowerSeries.constantCoeff (sigS P) = 0 by
        rw [hs0, add_zero])
    rw [sq, ← fExp_add hs10 hs10, hkey, fExp_add hss hL0, hLdef, fExp_fLog hu0]
  show PowerSeries.X ^ 2 * fExp (sigmaOneSeries e1 (3 * e1 ^ 2 - q) w) ^ 2 =
    (PowerSeries.X * fExp (sigS P)) ^ 2 * u
  rw [hsq, fExp_add hs0 hs0]
  ring

end Formalism.L2.Th1.B.Sq
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.SimeqPadicIntegers
section
noncomputable section

namespace Formalism.L2.Th1.B.Sim

open Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.HermitianLattices.ExpSeriesBivariate (InLam)
open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_zero inLam_add inLam_neg inLam_nsmul integral_of_mul_eq_one)

variable {K ι : Type} [NormedField K] [CharZero K]

theorem simeq_iff (f g : MvPowerSeries ι K) : Simeq f g ↔ InLam (f - g) := Iff.rfl

theorem inLam_zsmul [IsUltrametricDist K] {f : MvPowerSeries ι K} (hf : InLam f) (n : ℤ) :
    InLam (n • f) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [natCast_zsmul]; exact inLam_nsmul hf m
  · rw [neg_zsmul, natCast_zsmul]; exact inLam_neg (inLam_nsmul hf m)

theorem integral_of_sq [IsUltrametricDist K] {y : MvPowerSeries ι K} (h2 : ‖(2 : K)‖ = 1)
    (hy0 : MvPowerSeries.constantCoeff y = 1) (hy : Integral (y * y)) : Integral y := by
  classical
  have main : ∀ (m : ℕ) (d : ι →₀ ℕ), d.degree = m → ‖MvPowerSeries.coeff d y‖ ≤ 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro d hd
      by_cases hd0 : d = 0
      · subst hd0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hy0, norm_one]
      have hmem : ((d, 0) : (ι →₀ ℕ) × (ι →₀ ℕ)) ∈ (antidiagonal d).erase ((0 : ι →₀ ℕ), d) := by
        refine Finset.mem_erase.mpr ⟨fun h => hd0 (congrArg Prod.fst h), by simp⟩
      have h1 : MvPowerSeries.coeff d (y * y) = _ := MvPowerSeries.coeff_mul d y y
      rw [← Finset.add_sum_erase _ _ (show ((0 : ι →₀ ℕ), d) ∈ antidiagonal d by simp),
        ← Finset.add_sum_erase _ _ hmem] at h1
      simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hy0, one_mul, mul_one] at h1
      have h3 : 2 * MvPowerSeries.coeff d y = MvPowerSeries.coeff d (y * y) +
          - ∑ p ∈ ((antidiagonal d).erase ((0 : ι →₀ ℕ), d)).erase (d, 0),
            MvPowerSeries.coeff p.1 y * MvPowerSeries.coeff p.2 y := by
        rw [h1]; ring
      have h4 : ‖MvPowerSeries.coeff d y‖ = ‖2 * MvPowerSeries.coeff d y‖ := by
        rw [norm_mul, h2, one_mul]
      rw [h4, h3]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy d) ?_)
      rw [norm_neg]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p hp => ?_
      rw [norm_mul]
      have hpa := Finset.mem_erase.mp hp
      have hpb := Finset.mem_erase.mp hpa.2
      have hp1 : p.1 + p.2 = d := by simpa using hpb.2
      have hdeg : p.1.degree + p.2.degree = d.degree := by rw [← map_add, hp1]
      have hne1 : p.1 ≠ 0 := by
        intro h0
        apply hpb.1
        ext1
        · exact h0
        · simpa [h0] using hp1
      have hne2 : p.2 ≠ 0 := by
        intro h0
        apply hpa.1
        ext1
        · simpa [h0] using hp1
        · exact h0
      have hpos1 : p.1.degree ≠ 0 := fun h => hne1 ((Finsupp.degree_eq_zero_iff _).mp h)
      have hpos2 : p.2.degree ≠ 0 := fun h => hne2 ((Finsupp.degree_eq_zero_iff _).mp h)
      exact mul_le_one₀ (ih p.1.degree (by omega) p.1 rfl) (norm_nonneg _)
        (ih p.2.degree (by omega) p.2 rfl)
  exact fun d => main _ d rfl

theorem inLam_of_two_mul [IsUltrametricDist K] {f : MvPowerSeries ι K} (h2 : ‖(2 : K)‖ = 1)
    (hf : InLam (2 * f)) : InLam f := by
  have h0 : MvPowerSeries.constantCoeff f = 0 := by
    have h := hf.1
    rw [map_mul, map_ofNat] at h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  refine ⟨h0, integral_of_sq h2 (constantCoeff_fExp h0) ?_⟩
  have h := hf.2
  rw [two_mul] at h
  have e : fExp (f + f) = fExp f * fExp f := fExp_add h0 h0
  exact e ▸ h

theorem inLam_fLog {g : MvPowerSeries ι K} (hg0 : MvPowerSeries.constantCoeff g = 1)
    (hg : Integral g) : InLam (fLog g) := by
  refine ⟨constantCoeff_fLog hg0, ?_⟩
  have e : fExp (fLog g) = g := fExp_fLog hg0
  have h : Integral (fExp (fLog g)) := by rw [e]; exact hg
  exact h

end Formalism.L2.Th1.B.Sim

namespace Formalism.L2.Th1.B.Sim

open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_add inLam_neg)

theorem simeq_integral_series : SimeqInt := by
  intro K ι _ _ _ f g f' g' h h'
  rw [simeq_iff] at h h'
  refine ⟨?_, ?_, fun n => ?_⟩
  · rw [simeq_iff]
    have e : f - f' - (g - g') = (f - g) + -(f' - g') := by ring
    rw [e]; exact inLam_add h (inLam_neg h')
  · rw [simeq_iff]
    have e : -f - -g = -(f - g) := by ring
    rw [e]; exact inLam_neg h
  · rw [simeq_iff]
    have e : (n : MvPowerSeries ι K) * f - n * g = n • (f - g) := by
      rw [zsmul_eq_mul]; ring
    rw [e]; exact inLam_zsmul h n

theorem simeq_halving : SimeqHalf := by
  intro K ι _ _ _ f g h2 h
  rw [simeq_iff] at h ⊢
  rw [← mul_sub] at h
  exact inLam_of_two_mul h2 h

theorem simeq_formal_log : SimeqLog := by
  intro K ι _ _ _ g hg0 hg
  have h := inLam_fLog hg0 hg
  refine ⟨?_, ?_⟩
  · rw [simeq_iff, sub_zero]; exact h
  · rw [simeq_iff, sub_zero]; exact inLam_neg h

end Formalism.L2.Th1.B.Sim
end
end

