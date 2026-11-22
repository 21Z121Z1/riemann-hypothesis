import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsRelevantSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimate
section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

namespace GlobalTheory.BigTop.Fun.PolBound

theorem log_le_posLog' (y : ℝ) : Real.log y ≤ Real.posLog y := by
  unfold Real.posLog; exact le_max_right _ _

theorem posLog_le_of_log_le {y B : ℝ} (hy : Real.log y ≤ B) (hB : 0 ≤ B) : Real.posLog y ≤ B := by
  unfold Real.posLog; exact max_le hB hy

theorem pol_core {C Q f m k t lb Lb : ℝ} (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hf0 : 0 ≤ f) (hf : f ≤ Q) (hm0 : 0 ≤ m)
    (hm : m ≤ Q) (hk0 : 0 ≤ k) (hk : k ≤ Q) (ht0 : 0 ≤ t) (ht : t ≤ Q) (hlb0 : 0 ≤ lb) (hlb : lb ≤ Q)
    (hLb : Lb ≤ 20 * Q) :
    100000 * C ^ 3 * f * m ^ 2 * (k + m * (t + (k + m + 5) + 1)) ^ 2 *
      ((k + m - 1) * (k + m * (t + (k + m + 5) + 1)) * lb + C * f ^ 2 * (k + m) ^ 6 * Lb) ≤
      13000000000 * C ^ 4 * Q ^ 16 := by
  set N := k + m * (t + (k + m + 5) + 1) with hNdef
  have hQ0 : 0 ≤ Q := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hN0 : 0 ≤ N := by positivity
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  have hN : N ≤ 10 * Q ^ 2 := by
    have h1 : t + (k + m + 5) + 1 ≤ 9 * Q := by linarith
    have h2 : m * (t + (k + m + 5) + 1) ≤ Q * (9 * Q) := mul_le_mul hm h1 (by positivity) hQ0
    nlinarith
  have hr : k + m - 1 ≤ 2 * Q := by linarith
  have hnr0 : 0 ≤ k + m := by linarith
  have hnr : k + m ≤ 2 * Q := by linarith
  have i1 : (k + m - 1) * N * lb ≤ (2 * Q) * (10 * Q ^ 2) * Q := by
    have a : (k + m - 1) * (N * lb) ≤ (2 * Q) * (N * lb) := mul_le_mul_of_nonneg_right hr (by positivity)
    have b : N * lb ≤ (10 * Q ^ 2) * Q := mul_le_mul hN hlb hlb0 (by positivity)
    have c : (2 * Q) * (N * lb) ≤ (2 * Q) * ((10 * Q ^ 2) * Q) := mul_le_mul_of_nonneg_left b (by positivity)
    calc (k + m - 1) * N * lb = (k + m - 1) * (N * lb) := by ring
      _ ≤ _ := a.trans c
      _ = _ := by ring
  have i2 : C * f ^ 2 * (k + m) ^ 6 * Lb ≤ C * Q ^ 2 * (2 * Q) ^ 6 * (20 * Q) := by
    have a : C * f ^ 2 * (k + m) ^ 6 * Lb ≤ C * f ^ 2 * (k + m) ^ 6 * (20 * Q) :=
      mul_le_mul_of_nonneg_left hLb (by positivity)
    have b : C * f ^ 2 * (k + m) ^ 6 ≤ C * Q ^ 2 * (2 * Q) ^ 6 := by gcongr
    exact a.trans (mul_le_mul_of_nonneg_right b (by positivity))
  have hQ4 : Q ^ 4 ≤ Q ^ 9 := pow_le_pow_right₀ hQ (by norm_num)
  have hinner : (k + m - 1) * N * lb + C * f ^ 2 * (k + m) ^ 6 * Lb ≤ 1300 * C * Q ^ 9 := by
    have e1 : (2 * Q) * (10 * Q ^ 2) * Q = 20 * Q ^ 4 := by ring
    have e2 : C * Q ^ 2 * (2 * Q) ^ 6 * (20 * Q) = 1280 * C * Q ^ 9 := by ring
    have e3 : 20 * Q ^ 4 ≤ 20 * C * Q ^ 9 := by
      have : Q ^ 4 ≤ C * Q ^ 9 := hQ4.trans (le_mul_of_one_le_left (by positivity) hC)
      linarith
    linarith
  have hpre0 : 0 ≤ 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 := by positivity
  have hpre : 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 ≤ 100000 * C ^ 3 * Q * Q ^ 2 * (10 * Q ^ 2) ^ 2 := by gcongr
  calc 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 * ((k + m - 1) * N * lb + C * f ^ 2 * (k + m) ^ 6 * Lb)
      ≤ 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 * (1300 * C * Q ^ 9) := mul_le_mul_of_nonneg_left hinner hpre0
    _ ≤ 100000 * C ^ 3 * Q * Q ^ 2 * (10 * Q ^ 2) ^ 2 * (1300 * C * Q ^ 9) :=
        mul_le_mul_of_nonneg_right hpre (by positivity)
    _ = 13000000000 * C ^ 4 * Q ^ 16 := by ring

end GlobalTheory.BigTop.Fun.PolBound

namespace GlobalTheory.BigTop.Fun.PolBound

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem rpow_mono {x a b : ℝ} (hx : 1 ≤ x) (h : a ≤ b) : x ^ a ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx h

theorem factors_le {D : D7} (L : SizeData₂ D) (hS : SizesAt L) (T : ℕ) (hT : L.Ct + 1 ≤ T) :
    (D.R.f : ℝ) ≤ L.sc.x ^ (T + 9) ∧ (D.R.m : ℝ) ≤ L.sc.x ^ (T + 9) ∧ (D.R.k : ℝ) ≤ L.sc.x ^ (T + 9) ∧
      (D.R.t : ℝ) ≤ L.sc.x ^ (T + 9) ∧ Real.log L.sc.b ≤ L.sc.x ^ (T + 9) ∧ 0 ≤ Real.log L.sc.b ∧
      Real.log (L.sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
        (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|) ≤ 20 * L.sc.x ^ (T + 9) := by
  obtain ⟨hN, hM, hK, hKR, hTt, -, hQD, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, hPde, -⟩ := hS
  set x := L.sc.x with hxdef
  have hx1 : 1 ≤ x := L.sc.one_lt_alt.le
  have hx0 : 0 ≤ x := by linarith
  have he0 : 0 < L.sc.eps := L.sc.eps_pos
  have he1 : L.sc.eps < 1 / 52 := L.sc.eps_lt
  have hth : szTh L = L.sc.eps / 100 := rfl
  have hpow : ∀ j : ℕ, j ≤ T + 9 → x ^ j ≤ x ^ (T + 9) := fun j hj => pow_le_pow_right₀ hx1 hj
  have hrp : ∀ (a : ℝ) (j : ℕ), a ≤ j → x ^ a ≤ x ^ j := fun a j h => by
    rw [← Real.rpow_natCast]; exact rpow_mono hx1 h

  have hLd : L.sc.L = x ^ L.sc.eps := by rw [hxdef]; rfl
  have hlb : Real.log L.sc.b = x ^ L.sc.eps := by
    show Real.log (Real.exp L.sc.L) = _
    rw [Real.log_exp]; exact hLd
  have hLx : x ^ L.sc.eps ≤ x := by
    have := hrp L.sc.eps 1 (by norm_num; linarith); simpa using this

  have hm : (D.R.m : ℝ) ≤ x := by
    have hd1 : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0 _
    have h1 : Real.sqrt (x * L.sc.delta1) ≤ x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt (by nlinarith)
    have h2 : x ^ szTh L * Real.sqrt (x * L.sc.delta1) ≤ x ^ szTh L * x ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx0 _)
    rw [← Real.rpow_add (by linarith)] at h2
    have h3 : x ^ (szTh L + 1 / 2) ≤ x ^ (1 : ℕ) := hrp _ 1 (by rw [hth]; push_cast; linarith)
    linarith [hM.2, pow_one x]
  have hk : (D.R.k : ℝ) ≤ x ^ 5 := hK.2.trans (hrp _ 5 (by rw [hth]; push_cast; linarith))
  have hn : (D.R.n : ℝ) ≤ x ^ 3 := hN.2.trans (hrp _ 3 (by rw [hth]; push_cast; linarith))
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hf : (D.R.f : ℝ) ≤ x ^ 5 := by
    have h := hKR.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h2 : (D.R.m : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hm0 hm 2
    have h3 : (D.R.m : ℝ) ^ 2 * D.R.n ≤ x ^ 2 * x ^ 3 := mul_le_mul h2 hn (Nat.cast_nonneg _) (by positivity)
    calc (D.R.f : ℝ) ≤ _ := h
      _ ≤ _ := h3
      _ = x ^ 5 := by ring
  have ht : (D.R.t : ℝ) ≤ x ^ T := by
    refine hTt.2.trans (hrp _ T ?_)
    have : L.Ct + szTh L ≤ L.Ct + 1 := by rw [hth]; linarith
    linarith
  have hQ5 : x ^ 5 ≤ x ^ (T + 9) := hpow 5 (by omega)
  have hQ8 : x ^ 8 ≤ x ^ (T + 9) := hpow 8 (by omega)
  have hQ1 : x ≤ x ^ (T + 9) := by simpa using hpow 1 (by omega)
  refine ⟨hf.trans hQ5, hm.trans hQ1, hk.trans hQ5, ht.trans (hpow T (by omega)), by rw [hlb]; linarith,
    by rw [hlb]; positivity, ?_⟩

  have hb : Real.posLog L.sc.b ≤ x := posLog_le_of_log_le (by rw [hlb]; exact hLx) hx0
  have hnr : Real.posLog ((D.R.k + D.R.m : ℕ) : ℝ) ≤ 2 * x ^ 5 := by
    refine posLog_le_of_log_le ((Real.log_le_self (Nat.cast_nonneg _)).trans ?_) (by positivity)
    push_cast
    have : (D.R.m : ℝ) ≤ x ^ 5 := hm.trans (by simpa using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 5))
    linarith
  have hg : ∀ i : Fin 2, Real.posLog (D.host.g i : ℝ) ≤ x := fun i => by
    refine posLog_le_of_log_le ((hG i i).2.2.trans ?_) hx0
    rw [hLd, ← Real.rpow_add (by linarith)]
    have := hrp (szTh L + L.sc.eps) 1 (by rw [hth]; push_cast; linarith)
    simpa using this
  have hp1 : Real.posLog (D.host.pde : ℝ) ≤ x := posLog_le_of_log_le (hPde.1.trans (hLd ▸ hLx)) hx0
  have hp2 : Real.posLog (D.host.pde' : ℝ) ≤ x := posLog_le_of_log_le (hPde.2.trans (hLd ▸ hLx)) hx0
  have hdE : Real.posLog |((discr D.host.E : ℤ) : ℝ)| ≤ 6 * x ^ 8 := by
    refine posLog_le_of_log_le ?_ (by positivity)
    have e := logdE_eq_rd D
    unfold logdE at e
    rw [e]
    have hlr : Real.log D.host.rdE ≤ 2 * x ^ 3 + x := by
      have h1 := UpperTheory.Ram.Rd.log_rdE_le D.host
      have h2 : Real.log (D.R.n : ℝ) ≤ x ^ 3 := (Real.log_le_self (Nat.cast_nonneg _)).trans hn
      have hq : Real.log D.host.q ≤ x := hQD.2.2.1.trans (by
        have := hrp (L.sc.eps / 5 + szTh L) 1 (by rw [hth]; push_cast; linarith); simpa using this)
      have hd : Real.log D.host.d ≤ x := hQD.2.2.2.2.1.trans (by
        have := hrp (L.sc.eps / 5 + szTh L) 1 (by rw [hth]; push_cast; linarith); simpa using this)
      linarith
    have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    calc 2 * (D.R.f : ℝ) * Real.log D.host.rdE ≤ 2 * (D.R.f : ℝ) * (2 * x ^ 3 + x) :=
          mul_le_mul_of_nonneg_left hlr (by positivity)
      _ ≤ 2 * x ^ 5 * (2 * x ^ 3 + x) := by gcongr
      _ ≤ 6 * x ^ 8 := by
          have : x ^ 6 ≤ x ^ 8 := pow_le_pow_right₀ hx1 (by norm_num)
          nlinarith
  have hprod : Real.log (L.sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
        (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|) ≤ Real.posLog L.sc.b + Real.posLog ((D.R.k + D.R.m : ℕ) : ℝ) +
      Real.posLog (D.host.g 0 : ℝ) + Real.posLog (D.host.g 1 : ℝ) + Real.posLog (D.host.pde : ℝ) +
      Real.posLog (D.host.pde' : ℝ) + Real.posLog |((discr D.host.E : ℤ) : ℝ)| := by
    refine (log_le_posLog' _).trans ?_
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    exact Real.posLog_mul
  have h8 : x ^ 5 ≤ x ^ 8 := pow_le_pow_right₀ hx1 (by norm_num)
  have h18 : x ≤ x ^ 8 := by simpa using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 8)
  have := hg 0
  have := hg 1
  refine hprod.trans ?_
  linarith

end GlobalTheory.BigTop.Fun.PolBound

namespace GlobalTheory.BigTop.Fun

open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.BigTop.Fun.PolBound

theorem desPol : DesPol := by
  refine ⟨0, fun CF _ => ?_⟩
  refine ⟨1 / 52, by norm_num, fun eps _ _ =>
    ⟨⟨0, fun _ => 0, fun l => 16 * ((⌈|l.getD 0 0|⌉₊ : ℝ) + 1 + 9) + 1, fun _ => 0⟩, fun Fm CH _ hL => ?_⟩⟩
  intro _
  have hCH : 16 * ((⌈|Fm.Ct|⌉₊ : ℝ) + 1 + 9) + 1 ≤ CH := hL.2.2.1 CH (by simp [FamP.cMid])
  refine ⟨1, fun C hC => ?_⟩
  refine ⟨max (13000000000 * C ^ 4) 1, fun x hx hxle i p _ d _ => ?_⟩
  set T : ℕ := ⌈|Fm.Ct|⌉₊ + 1 with hTdef
  have hT : (Fm.L x i).Ct + 1 ≤ T := by
    rw [Fm.Ct_eq, hTdef]; push_cast; linarith [le_abs_self Fm.Ct, Nat.le_ceil |Fm.Ct|]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := factors_le (Fm.L x i) (Fm.sizes x hx i) T hT
  set X := (Fm.L x i).sc.x with hXdef
  have hX1 : 1 ≤ X := (Fm.L x i).sc.one_lt_alt.le
  have hXA : 13000000000 * C ^ 4 ≤ X := by
    rw [hXdef, Fm.L_x x i hx]; exact (le_max_left _ _).trans hxle
  set D := Fm.D x i
  have eN : ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) =
      (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) := by push_cast; ring
  have enr : ((D.R.k + D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + D.R.m := by push_cast; ring
  have e : d.O.pol C p.Z.b = 100000 * C ^ 3 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 *
      ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) ^ 2 *
      (((D.R.k : ℝ) + D.R.m - 1) * ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) *
        Real.log (Fm.L x i).sc.b + C * (D.R.f : ℝ) ^ 2 * ((D.R.k + D.R.m : ℕ) : ℝ) ^ 6 *
        Real.log ((Fm.L x i).sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) *
          (D.host.pde : ℝ) * (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|)) := rfl
  show d.O.pol C p.Z.b ≤ X ^ CH
  rw [e, eN, enr]
  rw [enr] at h7
  have key := pol_core hC (one_le_pow₀ hX1) (Nat.cast_nonneg _) h1 (Nat.cast_nonneg _) h2 (Nat.cast_nonneg _) h3
    (Nat.cast_nonneg _) h4 h6 h5 h7
  refine key.trans ?_
  have hp : (X ^ (T + 9)) ^ 16 = X ^ (16 * (T + 9)) := by rw [← pow_mul, mul_comm]
  have hC4 : 0 ≤ 13000000000 * C ^ 4 := by positivity
  calc 13000000000 * C ^ 4 * (X ^ (T + 9)) ^ 16 ≤ X * X ^ (16 * (T + 9)) := by
        rw [hp]; exact mul_le_mul_of_nonneg_right hXA (by positivity)
    _ = X ^ ((16 * (T + 9) + 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast, pow_succ, mul_comm]
    _ ≤ X ^ CH := by
        refine rpow_mono hX1 ?_
        rw [hTdef] at *
        push_cast
        linarith

end GlobalTheory.BigTop.Fun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsSeventhEstimate
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun.RamSum

section Norms

variable {F : Type} [Field F] [NumberField F]

theorem isPrimePow_absNorm (v : HeightOneSpectrum (𝓞 F)) : IsPrimePow (Ideal.absNorm v.asIdeal) := by
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact FiniteField.isPrimePow_card _

theorem sum_log_absNorm_le (S : Finset (HeightOneSpectrum (𝓞 F))) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ v ∈ S, (n : 𝓞 F) ∈ v.asIdeal) :
    ∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal) ≤ Module.finrank ℚ F * Real.log n := by
  have h1 : ∏ v ∈ S, v.asIdeal ∣ Ideal.span {(n : 𝓞 F)} :=
    Finset.prod_dvd_of_coprime (fun v _ w _ hvw => (HeightOneSpectrum.isCoprime_of_ne v w hvw))
      fun v hv => Ideal.dvd_span_singleton.2 (h v hv)
  have h2 := map_dvd Ideal.absNorm h1
  rw [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h2
  have h3 := Nat.le_of_dvd (by positivity) h2
  have h4 : ∀ v ∈ S, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := fun v _ => by
    exact_mod_cast (isPrimePow_absNorm v).ne_zero
  rw [← Real.log_prod h4, ← Real.log_pow]
  refine Real.log_le_log (Finset.prod_pos fun v hv => lt_of_le_of_ne (Nat.cast_nonneg _) (h4 v hv).symm) ?_
  exact_mod_cast h3

end Norms

theorem leaves_of_sum {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (O : FunData K Df) (C b : ℝ) (hL : 0 ≤ Real.log b) (h0 : O.sv0 ∈ O.S0) (hq : ∀ q ∈ O.S0, IsPrimePow (O.qq q))
    (hS : ∑ q ∈ O.S0, Real.log (O.qq q) ≤ 21 * (O.f * Real.log b)) (hc : ∀ q ∈ O.S0, O.cc q ≤ 2)
    (hP : 42 * (O.f * Real.log b) ≤ O.PPF C b) : PrimePowerModuliSumBound O C b ∧ LeafCS O b := by
  classical
  have hfL : 0 ≤ O.f * Real.log b := by positivity
  have hlq : 0 < Real.log (O.qq O.sv0) := Real.log_pos (by exact_mod_cast (hq _ h0).one_lt)
  have hP0 : 0 ≤ O.PPF C b := by linarith
  refine ⟨⟨hq, ?_⟩, ?_⟩
  · unfold FunData.Sig0
    rw [← Finset.add_sum_erase _ _ h0] at hS ⊢
    have e1 : ∑ q ∈ O.S0.erase O.sv0, (O.ee C b q : ℝ) * Real.log (O.qq q) =
        2 * ∑ q ∈ O.S0.erase O.sv0, Real.log (O.qq q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq' => ?_
      simp [FunData.ee, Finset.ne_of_mem_erase hq']
    have e2 : (O.ee C b O.sv0 : ℝ) * Real.log (O.qq O.sv0) ≤ O.PPF C b + Real.log (O.qq O.sv0) := by
      have h := Nat.floor_le (div_nonneg hP0 hlq.le)
      rw [le_div_iff₀ hlq] at h
      simp only [FunData.ee, if_true]
      push_cast
      linarith
    rw [e1]
    linarith
  · unfold LeafCS FunData.cS
    have e1 : ∑ q ∈ O.S0, (O.cc q : ℝ) * Real.log (O.qq q) ≤ 2 * ∑ q ∈ O.S0, Real.log (O.qq q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq' => mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg _)
      exact_mod_cast hc q hq'
    linarith

theorem ramifiedPlaces_sum_log_absNorm_le {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} (P : GlobalTheory.ChiGrid.Places Lc) (s : Formalism.BasicNotions.Scale)
    (hg : ∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * s.L)) (h1 : (D.host.pde : ℝ) < s.X')
    (h2 : (D.host.pde' : ℝ) < s.X') (h3 : ((GlobalTheory.ChiGrid.q0 D : ℕ) : ℝ) < s.X') :
    ∑ v ∈ P.S0, Real.log (Ideal.absNorm v.asIdeal) ≤ 21 * (D.R.f * Real.log s.b) := by
  have p0 := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
  have p1 := (D.host.g_prime 0).pos
  have p2 := (D.host.g_prime 1).pos
  have p3 := D.host.pde_prime.pos
  have p4 := D.host.pde'_prime.pos
  have hF : Module.finrank ℚ D.host.F = D.R.f := by
    rw [D.host.finrank_hostF, Ranks.f, Ranks.n]
  have key := sum_log_absNorm_le P.S0
    (n := GlobalTheory.ChiGrid.q0 D * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde')) (by positivity) fun v hv => by
      rw [Nat.cast_mul]
      rcases P.mem_S0_of_sum_eq.1 hv with rfl | hv
      · exact Ideal.mul_mem_right _ _ P.basePlace_over_qZero
      · exact Ideal.mul_mem_left _ _ (Formalism.L2.DIV.mem_primesOf.1 hv).2
  rw [hF] at key
  refine key.trans ?_
  have hb : Real.log s.b = s.L := Real.log_exp _
  have hX : s.X' ≤ Real.exp s.L :=
    Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith [s.eps_pos]))
  have hl : ∀ {n : ℕ} {y : ℝ}, 0 < n → (n : ℝ) ≤ Real.exp y → Real.log n ≤ y := fun hn h =>
    (Real.log_le_iff_le_exp (by exact_mod_cast hn)).2 h
  have a0 := hl p0 (h3.le.trans hX)
  have a1 := hl p1 (hg 0)
  have a2 := hl p2 (hg 1)
  have a3 := hl p3 (h1.le.trans hX)
  have a4 := hl p4 (h2.le.trans hX)
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), hb, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

theorem le_PPF {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (O : FunData K Df) {C b : ℝ} (hC : 42 ≤ C) (hb : 1 ≤ b) (hf : 1 ≤ O.f) (hn : 1 ≤ O.nr) (h1 : 1 ≤ O.g1) (h2 : 1 ≤ O.g2)
    (h3 : 1 ≤ O.pd) (h4 : 1 ≤ O.pd') (h5 : O.dE ≠ 0) : 42 * (O.f * Real.log b) ≤ O.PPF C b := by
  have hf' : (1 : ℝ) ≤ O.f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ O.nr := by exact_mod_cast hn
  have h1' : (1 : ℝ) ≤ O.g1 := by exact_mod_cast h1
  have h2' : (1 : ℝ) ≤ O.g2 := by exact_mod_cast h2
  have h3' : (1 : ℝ) ≤ O.pd := by exact_mod_cast h3
  have h4' : (1 : ℝ) ≤ O.pd' := by exact_mod_cast h4
  have h5' : (1 : ℝ) ≤ |(O.dE : ℝ)| := by exact_mod_cast Int.one_le_abs h5
  have hl : 0 ≤ Real.log b := Real.log_nonneg hb
  have e1 : Real.log b ≤ Real.log (b * O.nr * O.g1 * O.g2 * O.pd * O.pd' * |(O.dE : ℝ)|) := by
    refine Real.log_le_log (by linarith) ?_
    calc b = b * 1 * 1 * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have e2 : (O.f : ℝ) ≤ (O.f : ℝ) ^ 2 := le_self_pow₀ hf' two_ne_zero
  have e3 : (1 : ℝ) ≤ (O.nr : ℝ) ^ 6 := one_le_pow₀ hn'
  unfold FunData.PPF
  calc 42 * (O.f * Real.log b) = 42 * O.f * 1 * Real.log b := by ring
    _ ≤ _ := by gcongr

end GlobalTheory.BigTop.Fun.RamSum

namespace GlobalTheory.BigTop.Fun

open RamSum

theorem ramified_sums_seventh_bound : RamifiedSumBound := by
  refine ⟨0, fun CF _ => ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ _ => ?_⟩⟩⟩
  refine ⟨42, fun C hC => EvPt.of_forall fun x hx i p _ d _ => ?_⟩
  obtain ⟨-, -, hg, h1, h2, -⟩ := hF.1.2.2.2.2.2.2.2.2 x hx i
  have h3 := hF.2.2.1 x hx i
  have hb : 1 ≤ (Fm.L x i).sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  refine leaves_of_sum d.O C p.Z.b (Real.log_nonneg hb) (d.G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)) (fun v _ => isPrimePow_absNorm v)
    (ramifiedPlaces_sum_log_absNorm_le d.G.pl (Fm.L x i).sc hg h1 h2 h3) (fun v _ => ?_)
    (le_PPF d.O hC hb ?_ ?_ ((Fm.D x i).host.g_prime 0).pos ((Fm.D x i).host.g_prime 1).pos (Fm.D x i).host.pde_prime.pos
      (Fm.D x i).host.pde'_prime.pos (discr_ne_zero _))
  · unfold FunIn.O FunIn.data
    dsimp only
    split_ifs <;> omega
  · have := (Fm.D x i).R.m_le_f
    have := (Fm.D x i).R.two_le_m
    show 1 ≤ (Fm.D x i).R.f
    unfold Ranks.f Ranks.n
    omega
  · have := (Fm.D x i).R.two_le_m
    show 1 ≤ (Fm.D x i).R.k + (Fm.D x i).R.m
    omega

end GlobalTheory.BigTop.Fun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsRelevantSpaceStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_maps_relevant_space : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (R₂ : RealMaps F a a'),
    IsTriple B (reG G V V' W) X om om' → IsRealMaps B (reG G V V' W) om om' R₂ →
    ∀ g ∈ UAt σ G.V (evI F), ∀ g' ∈ UAt σ G.V' (evI F), ∀ h ∈ UAt σ G.W (evI F),
    (∀ w, (mat g).map (piInf (B.emb w)) * G.V.θ w = V.θ w * (mat g).map (piInf (B.emb w))) →
    (∀ w, (mat g').map (piInf (B.emb w)) * G.V'.θ w = V'.θ w * (mat g').map (piInf (B.emb w))) →
    (∀ w, (mat h).map (piInf (B.emb w)) * G.W.θ w = W.θ w * (mat h).map (piInf (B.emb w))) →
    ∃ R₃ : RealMaps F a a', IsRealMaps B G om om' R₃ ∧ ∀ (Rf : FinMaps F a a') Φ Φ', PolMatch B G X R₃ Rf Φ Φ' →
        PolMatch B (reG G V V' W) X R₂ Rf (om (g, h) Φ) (om' (g', h) Φ') := by
  first | exact @GlobalTheory.MajTransport.transport | exact GlobalTheory.MajTransport.transport | (intros; apply GlobalTheory.MajTransport.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCharacterTimesInverseUnitary
section
open NumberField

noncomputable section

namespace GlobalTheory.CovTop

open Formalism.L2.DIV

theorem prod_hom_pow_eq_one {H M ι : Type} [Group H] [CommMonoid M] (s : Finset ι) (f : ι → H →* M) (N : ℕ)
    (h : ∀ i x, f i x ^ N = 1) (x : H) : (∏ i ∈ s, f i) x ^ N = 1 := by
  rw [MonoidHom.finset_prod_apply, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => h i x

theorem ofLocal_chi_pow {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    (Hl : (PP : Pg) → Subgroup (GL (Fin r) (kP PP.1))) (cl : (PP : Pg) → Hl PP →* LLˣ) (N : ℕ)
    (h : ∀ PP x, cl PP x ^ N = 1) (g : (LevelP.ofLocal Hl cl).H) : (LevelP.ofLocal Hl cl).chi g ^ N = 1 :=
  prod_hom_pow_eq_one (H := Subgroup.pi Set.univ Hl) Finset.univ _ N (fun PP x => h PP _) g

theorem unipotentTypeLevel_char_pow_eq_one {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : (PP : Pl E) → AddChar (kP PP) LL) (N : ℕ) (hN : ∀ PP : Pg, (N : kP PP.1) = 0)
    (g : (P0 Pg r ψ).H) : (P0 Pg r ψ).chi g ^ N = 1 := by
  refine ofLocal_chi_pow _ _ N (fun PP x => ?_) g
  apply Units.ext
  simp only [addCharHom, Units.val_pow_eq_pow_val, MonoidHom.coe_toHomUnits, Units.val_one, MonoidHom.comp_apply,
    AddChar.toMonoidHom_apply]
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hN PP, zero_mul, AddChar.map_zero_eq_one]

theorem det_of_mem_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    Matrix.det_of_upperTriangular (fun i j hij => hg.1 hij)]
  exact Finset.prod_eq_one fun i _ => hg.2 i

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem chi_mul_psi_inv_mem_core (p : GlobalTheory.BigTop.PtAt ex Csz) (i : Fin D.R.m) : p.Rows → RecTied D L →
    ∀ u : (p.F.lv2.lvl false).P, (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ∈
      Set.range (algebraMap p.T.Q.c.F D.what₂.LL) := by
  intro _ _ u
  have hB := p.charW.base
  obtain ⟨ψ0, -, hlev, -⟩ := hB.grp.levels
  have hL := hB.lev
  have hN0 : p.T.Q.l.M' ≠ 0 := Nat.lcm_ne_zero (by have := p.T.Q.l.three_le; omega) p.T.Q.l.A_pos.ne'
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  have hN : ∀ PP : p.R.Pg, (p.T.Q.l.M' : kP PP.1) = 0 := by
    intro PP
    obtain ⟨k, hk⟩ := (hL.Pg PP.1).1 PP.2
    have h2 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.1.under (𝓞 D.host.K)).asIdeal := by
      rw [hk]; exact p.R.C.P.pb_over k
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal := by
      change _ ∈ Ideal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) PP.1.asIdeal at h2
      rwa [Ideal.mem_comap, map_natCast] at h2
    have h3 : ((D.host.g k : ℕ) : kP PP.1) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk PP.1.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 h1
    have hk' : D.host.g k ∣ p.T.Q.l.M' := by
      refine dvd_trans ?_ (Nat.dvd_lcm_left p.T.Q.l.M p.T.Q.l.A)
      rw [hM]
      fin_cases k
      exacts [dvd_mul_right _ _, dvd_mul_left _ _]
    obtain ⟨c, hc⟩ := hk'
    rw [hc, Nat.cast_mul, h3, zero_mul]
  have hu : p.R.eG u ∈ (p.R.levR p.F.lv2 false).H := by
    show p.R.eG.symm.toMonoidHom (p.R.eG u) ∈ (p.F.lv2.lvl false).P
    simp
  have key : ∀ X : LevelP p.R.Pg D.R.r ℂ, X = P0 p.R.Pg D.R.r ψ0 → ∀ g (hg : g ∈ X.H),
      (∀ PP, g PP ∈ unip (kP PP.1) D.R.r) ∧ X.chi ⟨g, hg⟩ ^ p.T.Q.l.M' = 1 := by
    rintro X rfl g hg
    exact ⟨fun PP => (Subgroup.mem_pi _).1 hg PP (Set.mem_univ _), unipotentTypeLevel_char_pow_eq_one _ _ ψ0 _ hN _⟩
  obtain ⟨hun, hpow⟩ := key _ hlev _ hu
  have e1 : (p.R.levR p.F.lv2 false).chi ⟨p.R.eG u, hu⟩ =
      Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((p.F.lv2.lvl false).ψ u) := by
    show Units.map _ ((p.F.lv2.lvl false).ψ _) = _
    congr 2
    exact Subtype.ext (by show p.R.eG.symm (p.R.eG u) = u; exact p.R.eG.symm_apply_apply _)
  have h5 : (((p.F.lv2.lvl false).ψ u : D.what₂.LLˣ) : D.what₂.LL) ^ p.T.Q.l.M' = 1 := by
    apply D.what₂.embLL.injective
    have := congrArg (fun z : ℂˣ => (z : ℂ)) (e1 ▸ hpow)
    simpa using this
  have hchi : (p.R.toRealDat.FW i).chi u = 1 := by
    apply Units.ext
    apply D.what₂.embLL.injective
    rw [hB.grp.chiW i u, Finset.prod_eq_one (fun PP _ => by rw [det_of_mem_unip (hun PP), map_one, Units.val_one]),
      Units.val_one, map_one]
  rw [hchi, one_mul]
  have hy : (((p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ^ p.T.Q.l.M' = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_pow, h5, inv_one]
  have hz : IsPrimitiveRoot (⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta p.T.Q.l.M', p.T.Q.c.zeta_mem⟩ : p.T.Q.c.F) p.T.Q.l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := p.T.Q.c.F.val) (Complex.isPrimitiveRoot_exp _ hN0) Subtype.val_injective
  have hz' := hz.map_of_injective (f := algebraMap p.T.Q.c.F D.what₂.LL) (algebraMap p.T.Q.c.F D.what₂.LL).injective
  haveI : NeZero p.T.Q.l.M' := ⟨hN0⟩
  obtain ⟨k, -, hk⟩ := hz'.eq_pow_of_pow_eq_one hy
  exact ⟨_ ^ k, by rw [map_pow, hk]⟩

end GlobalTheory.CovTop
end
end

