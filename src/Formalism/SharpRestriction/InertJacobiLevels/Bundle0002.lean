import Formalism.SharpRestriction.InertJacobiLevels.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExtraVal
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain IsLocalRing

theorem val_le_one_iff {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (w : HeightOneSpectrum R) {B FB : Type*} [CommRing B] [IsLocalRing B] [Field FB] [Algebra B FB]
    (hinj : Function.Injective (algebraMap B FB)) (f : K →+* FB)
    (h1 : ∀ x : R, x ∈ w.asIdeal → ∃ y ∈ maximalIdeal B, algebraMap B FB y = f (algebraMap R K x))
    (h3 : ∀ x : R, x ∉ w.asIdeal → ∃ y : Bˣ, algebraMap B FB y = f (algebraMap R K x)) (x : K) :
    w.valuation K x ≤ 1 ↔ f x ∈ (algebraMap B FB).range := by
  have key : ∀ y : K, w.valuation K y ≤ 1 →
      ∃ a s : R, s ∉ w.asIdeal ∧ y * algebraMap R K s = algebraMap R K a := by
    intro y hy
    have hmem : y ∈ Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors := by
      have h1 : y ∈ (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w).toSubring := by
        show y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w
        rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
        exact (Valuation.mem_valuationSubring_iff _ _).2 hy
      rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring] at h1
      exact h1
    haveI := Localization.subalgebra.isLocalization_ofField K w.asIdeal.primeCompl
      w.asIdeal.primeCompl_le_nonZeroDivisors
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl
      (⟨y, hmem⟩ : Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors)
    refine ⟨a, s, s.2, ?_⟩
    have h2 := congrArg (fun z : Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors => (z : K))
      (IsLocalization.mk'_spec (Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors) a s)
    have hs' : IsLocalization.mk' (Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors) a s = ⟨y, hmem⟩ := hs
    rw [hs'] at h2
    simpa using h2
  have hone : ∀ s : R, s ∉ w.asIdeal → w.intValuation s = 1 := fun s hs =>
    le_antisymm (w.intValuation_le_one s)
      (not_lt.1 fun h => hs ((IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem w s).1 h))
  constructor
  · intro hx
    obtain ⟨a, s, hs, has⟩ := key x hx
    obtain ⟨u, hu⟩ := h3 s hs
    have hfa : f (algebraMap R K a) ∈ (algebraMap B FB).range := by
      by_cases ha : a ∈ w.asIdeal
      · obtain ⟨y, _, hy⟩ := h1 a ha
        exact ⟨y, hy⟩
      · obtain ⟨y, hy⟩ := h3 a ha
        exact ⟨y, hy⟩
    obtain ⟨b, hb⟩ := hfa
    refine ⟨b * ↑u⁻¹, ?_⟩
    have hfx : f x * f (algebraMap R K s) = f (algebraMap R K a) := by rw [← map_mul, has]
    rw [map_mul, hb, ← hfx, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  · rintro ⟨b, hb⟩
    by_contra hx
    push_neg at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hinv : w.valuation K x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hx
    obtain ⟨a, s, hs, has⟩ := key x⁻¹ hinv.le
    have hva : w.intValuation a < 1 := by
      have es : w.valuation K (algebraMap R K s) = 1 := by
        have e0 : w.valuation K (algebraMap R K s) = w.intValuation s :=
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap w s
        rw [e0, hone s hs]
      have ev : w.valuation K (algebraMap R K a) = w.valuation K x⁻¹ := by
        rw [← has, map_mul, es, mul_one]
      have ea : w.valuation K (algebraMap R K a) = w.intValuation a :=
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap w a
      rw [← ea, ev]
      exact hinv
    have ha : a ∈ w.asIdeal := (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem w a).1 hva
    obtain ⟨y, hy, hya⟩ := h1 a ha
    obtain ⟨u, hu⟩ := h3 s hs
    have e1 : f x⁻¹ * algebraMap B FB u = algebraMap B FB y := by
      rw [hu, hya, ← map_mul, has]
    have e2 : algebraMap B FB (b * y) = algebraMap B FB u := by
      rw [map_mul, ← e1, hb, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0, map_one, one_mul]
    have e3 := hinj e2
    have hmax : (u : B) ∈ maximalIdeal B := e3 ▸ Ideal.mul_mem_left _ b hy
    exact ((IsLocalRing.mem_maximalIdeal _).1 hmax) u.isUnit

theorem map_mem_maximalIdeal {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B]
    [IsLocalRing B] (g : A →+* B) (l : ℕ) (hl0 : (l : A) ≠ 0) (hl : (l : B) ∈ maximalIdeal B) (y : A)
    (hy : y ∈ maximalIdeal A) : g y ∈ maximalIdeal B := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hne : Ideal.span {(l : A)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hyn : y ^ n ∈ Ideal.span {(l : A)} := by
    rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
    exact Ideal.pow_mem_pow hy n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hyn
  have hpow : g y ^ n ∈ maximalIdeal B := by
    rw [← map_pow, ← hc, map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ hl
  exact (maximalIdeal.isMaximal B).isPrime.mem_of_pow_mem n hpow

section Rec

variable (D : D7)

theorem val_nonneg_iff (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val w x ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [D.val_eq w x hx, Formalism.BasicNotions.vAdd]
    have hv0 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (D.plEq w).valuation D.what₂.LL x = WithZero.exp n :=
      ⟨_, (WithZero.exp_log hv0).symm⟩
    rw [hn, WithZero.log_exp, ← WithZero.exp_zero, WithZero.exp_le_exp]
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
    omega

theorem resChar_mem (w : D.what₂.places.Pl) : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have h1 := D.what₂.places.val_resChar w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  rw [D.val_eq w _ hne, Formalism.BasicNotions.vAdd] at h1
  have h2 := WithTop.coe_injective h1
  have hv0 : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hne
  obtain ⟨n, hn⟩ : ∃ n : ℤ,
      (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = WithZero.exp n :=
    ⟨_, (WithZero.exp_log hv0).symm⟩
  rw [hn, WithZero.log_exp] at h2
  have hpos := D.what₂.places.ramIdx_pos w
  have hlt : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) < 1 := by
    rw [hn, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
  have e : (D.plEq w).valuation D.what₂.LL
      (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) =
      (D.plEq w).intValuation ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) :=
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _
  rw [← e, map_natCast]
  exact hlt

end Rec

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.GenSplit
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField

theorem jacobi_neg_of_one_mod {a g : ℕ} (ha : Odd a) (h4 : g % 4 = 1) (hg : g ≡ 1 [MOD a]) :
    jacobiSym (-(a : ℤ)) g = 1 := by
  have hodd : Odd g := Nat.odd_iff.2 (by omega)
  have h1 : jacobiSym (g : ℤ) a = 1 := by
    have : (g : ℤ) % a = 1 % a := by
      have h2 : g % a = 1 % a := hg
      have h3 : ((g % a : ℕ) : ℤ) = ((1 % a : ℕ) : ℤ) := by rw [h2]
      push_cast at h3
      exact h3
    rw [jacobiSym.mod_left' this, jacobiSym.one_left]
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_one_mod_four h4, one_mul,
    ← jacobiSym.quadratic_reciprocity_one_mod_four h4 ha, h1]

theorem typePrime_facts {q d g : ℕ} (hq : q.Prime) (hd : d.Prime) (hq2 : Odd q) (hd2 : Odd d) (h1 : 1 < g)
    (hg : g ≡ 1 [MOD 16 * q * d]) :
    g ≠ 2 ∧ g ≠ q ∧ g ≠ d ∧ jacobiSym (-(q : ℤ)) g = 1 ∧ jacobiSym (-(d : ℤ)) g = 1 ∧
      (g : ZMod (2 ^ (2 + 2))) = 1 := by
  have h16 : g ≡ 1 [MOD 16] := hg.of_mul_right _ |>.of_mul_right _
  have hmq : g ≡ 1 [MOD q] := by
    have : 16 * q * d = q * (16 * d) := by ring
    rw [this] at hg; exact hg.of_mul_right _
  have hmd : g ≡ 1 [MOD d] := by
    have : 16 * q * d = d * (16 * q) := by ring
    rw [this] at hg; exact hg.of_mul_right _
  have h16' : g % 16 = 1 := h16
  have hne : ∀ p : ℕ, p.Prime → g ≡ 1 [MOD p] → g ≠ p := by
    rintro p hp h rfl
    have : g % g = 1 % g := h
    rw [Nat.mod_self, Nat.mod_eq_of_lt h1] at this
    omega
  refine ⟨by omega, hne q hq hmq, hne d hd hmd, jacobi_neg_of_one_mod hq2 (by omega) hmq,
    jacobi_neg_of_one_mod hd2 (by omega) hmd, ?_⟩
  have := (ZMod.natCast_eq_natCast_iff g 1 (2 ^ (2 + 2))).2 h16
  simpa using this

variable {s B : ℕ} (A : Arith B (4 * (2 * s + 15) * 9 + 1))

theorem hostOf_g_split (u0 : _) (T Lw : ℕ) :
    ∀ k, (placesOver (hostOf A u0 T Lw).E ((hostOf A u0 T Lw).g k)).ncard =
      Module.finrank ℚ (hostOf A u0 T Lw).E := by
  have hM : 1 < 16 * A.q * A.d := by
    nlinarith [Nat.mul_pos A.hyp.1.pos A.hyp.2.1.pos]
  have hc : ∀ g : ℕ, g ≡ 1 [MOD 16 * A.q * A.d] → g % (16 * A.q * A.d) = 1 := by
    intro g hg
    have h1 : g % (16 * A.q * A.d) = 1 % (16 * A.q * A.d) := hg
    rw [Nat.mod_eq_of_lt hM] at h1
    exact h1
  refine g_split_of (hostOf A u0 T Lw) (fun k => ?_)
  fin_cases k
  · exact hc _ A.first_prime_modEq_one
  · exact hc _ A.second_prime_modEq_one

theorem hostOf_tHyp (u0 : _) (T Lw : ℕ) : THyp (hostOf A u0 T Lw) := by
  have hq2 : Odd A.q := Nat.odd_iff.2 (by have := A.hyp.2.2.1; omega)
  have hd2 : Odd A.d := Nat.odd_iff.2 (by have := A.hyp.2.2.2.1; omega)
  have hg0 := A.sixty_one_lt_first_prime
  have hg1 := A.first_prime_lt_second
  have hM : 1 < 16 * A.q * A.d := by
    have := A.hyp.1.pos
    have := A.hyp.2.1.pos
    nlinarith [Nat.mul_pos A.hyp.1.pos A.hyp.2.1.pos]
  have hc : ∀ g : ℕ, g ≡ 1 [MOD 16 * A.q * A.d] → g % (4 * 4 * A.q * A.d) = 1 := by
    intro g hg
    have h1 : g % (16 * A.q * A.d) = 1 % (16 * A.q * A.d) := hg
    rw [Nat.mod_eq_of_lt hM] at h1
    exact h1
  obtain ⟨a0, -, -, -, e0, -⟩ := typePrime_facts A.hyp.1 A.hyp.2.1 hq2 hd2 (by omega) A.first_prime_modEq_one
  obtain ⟨a1, -, -, -, e1, -⟩ := typePrime_facts A.hyp.1 A.hyp.2.1 hq2 hd2 (by omega) A.second_prime_modEq_one
  refine ⟨fun k => ?_, A.bb, fun k => ?_⟩
  · fin_cases k
    · exact hc _ A.first_prime_modEq_one
    · exact hc _ A.second_prime_modEq_one
  · fin_cases k
    · exact ⟨a0, e0⟩
    · exact ⟨a1, e1⟩

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.TiesCore
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.Inhab.GC

structure GHost (R : Ranks) where
  TT : Finset (R.A)
  T2 : Finset ℕ
  u0 : R.A
  cls : ℕ → PrimeClass

structure GD where
  R : Ranks
  host : GHost R
  hPf : ℕ → R.A

structure GParameters (D : GD) where
  sc : Scale
  Sc : ℝ
  etaSz : ℝ

def GParameters.lifts (D : GD) : Finset ℕ := Finset.Icc 1 D.R.m

abbrev HH (D : GD) : Type := D.R.A

def cG {D : GD} (L : GParameters D) : ℝ := 4 * L.Sc

def Nm (D : GD) : ℝ := (D.R.N D.R.m : ℝ)

def L1 (D : GD) (s : Scale) (p : ℕ) : ℕ := ⌈Real.logb p (((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4)⌉₊

def L2 (D : GD) (s : Scale) : ℕ :=
  2 * sSup {l | ∃ p : ℕ, p.Prime ∧ D.host.cls p = PrimeClass.inertClass ∧ l = L1 D s p}

def Nstar (D : GD) (s : Scale) : ℝ := 2 * (D.R.n : ℝ) * s.delta1

def rho (D : GD) (K : Consts) (s : Scale) : ℝ :=
  4 * Nstar D s * s.x ^ s.eps * La K s / D.R.k + K.rho * (N1 s : ℝ) * La K s / D.R.k

def rhoB (D : GD) (K : Consts) (s : Scale) : ℝ :=
  4 * Nstar D s * s.x ^ s.eps * La K s / D.R.k + K.rho * K.CN * Real.log s.x * La K s / D.R.k

def InBand0 (D : GD) (K : Consts) (s : Scale) (p : ℕ) : Prop :=
  s.p0 D.R.k ≤ (p : ℝ) ∧ (p : ℝ) < s.X' ∧ ∃ d : ℕ, 1 ≤ d ∧
    s.X' * (1 - rho D K s) ≤ (p : ℝ) ^ d ∧ (p : ℝ) ^ d ≤ s.X' * (1 + rho D K s)

def InBand (D : GD) (K : Consts) (s : Scale) (p : ℕ) : Prop :=
  s.p0 D.R.k ≤ (p : ℝ) ∧ (p : ℝ) < s.X' ∧ ∃ d : ℕ, 1 ≤ d ∧
    s.X' * (1 - rhoB D K s) ≤ (p : ℝ) ^ d ∧ (p : ℝ) ^ d ≤ s.X' * (1 + rhoB D K s)

def c0num {D : GD} (L : GParameters D) : ℝ := 2 * L.sc.b' + 2 * cG L

def hP (D : GD) (p : ℕ) : HH D := D.hPf p

abbrev IsResidueClassZero (D : GD) (p : ℕ) : Prop := D.host.cls p = PrimeClass.inertClass

abbrev IsSg (D : GD) (p : ℕ) : Prop := D.host.cls p = PrimeClass.signal

def partner (D : GD) (p : ℕ) (t : HH D) (e : ℕ) : Bool × HH D :=
  (decide (IsSg D p ∧ Odd e), t + e • hP D p)

def IsTopPl (D : GD) (z : Bool × HH D) : Prop := z.1 = false ∧ z.2 ∈ D.host.TT

def IsThickPl (D : GD) (z : Bool × HH D) : Prop :=
  z.1 = true ∧ z.2 ∈ D.host.T2.image (fun s : ℕ => D.R.dig s + D.host.u0)

def IsThinPl (D : GD) (z : Bool × HH D) : Prop := ¬ IsTopPl D z ∧ ¬ IsThickPl D z

structure Inst (D : GD) (L : GParameters D) where
  bs : HH D → HH D → HH D
  bs_orb : ∀ h t, ∃ i : ℕ, bs h t + i • h = t
  bs_step : ∀ h t, bs h (t + h) = bs h t
  off : ℕ → Bool × HH D → ℝ
  off_top : ∀ j z, IsTopPl D z → L.sc.b' / L.sc.x ≤ off j z ∧ off j z ≤ L.sc.b' / L.sc.x + L.etaSz
  off_thin : ∀ j z, IsThinPl D z → L.sc.w'' D.R.n ≤ off j z ∧ off j z ≤ L.sc.w'' D.R.n + L.etaSz
  off_thick : ∀ j z, IsThickPl D z → L.sc.b ≤ off j z ∧ off j z ≤ L.sc.b + L.etaSz + 1
  kapI : ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ
  ep : ℕ → ℕ

variable {D : GD} {L : GParameters D}

def fill (X : Inst D L) (b : HH D → ℤ) (j : ℕ) (z : Bool × HH D) : ℝ :=
  (if z.1 = false ∧ z.2 ∈ D.host.TT then (b z.2 : ℝ) else 0) + X.off j z

def kaJ (D : GD) (j : ℕ) : ℝ := ((D.R.k : ℝ) + (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1)) / 2

def fillG (X : Inst D L) (b : HH D → ℤ) (j : ℕ) (z : Bool × HH D) : ℝ := fill X b j z - kaJ D j

def stepP (D : GD) (p : ℕ) : HH D := if IsSg D p then 2 • hP D p else hP D p

def nP (D : GD) (p : ℕ) : ℕ :=
  if IsSg D p then 2 * addOrderOf (2 • hP D p) else addOrderOf (hP D p)

def reps (X : Inst D L) (p : ℕ) : Finset (HH D) := Finset.univ.image (X.bs (stepP D p))

def topsOn (X : Inst D L) (p : ℕ) (t0 : HH D) : Finset (HH D) :=
  D.host.TT.filter (fun t => X.bs (stepP D p) t = t0)

def Nv (X : Inst D L) (p : ℕ) (t0 : HH D) : ℕ := (topsOn X p t0).card

def topsPos (D : GD) (p : ℕ) (t0 : HH D) : Finset (Fin (addOrderOf (hP D p))) :=
  Finset.univ.filter (fun i => t0 + (i : ℕ) • hP D p ∈ D.host.TT)

def wPos (D : GD) (p : ℕ) (t0 : HH D) (a : HH D → ℤ) : Fin (addOrderOf (hP D p)) → ℤ :=
  fun i => a (t0 + (i : ℕ) • hP D p)

def IsV (X : Inst D L) (p : ℕ) (t : HH D) : Prop :=
  ∃ i : ℕ, i < nP D p ∧ Even i ∧ X.bs (stepP D p) t + i • hP D p = t

def Good (_X : Inst D L) (p : ℕ) (t0 : HH D) : Prop :=
  IsGoodOrbit (addOrderOf (hP D p)) (topsPos D p t0) (L2 D L.sc) (KG L.sc) (rG L.sc) L.sc.delta1
    (hG L.sc) L.sc.x

def DIIf (K : Consts) (L : GParameters D) (p n' : ℕ) : ℕ :=
  ⌈K.DII * NplusF L.sc n' * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) *
      Real.logb p L.sc.a + 2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L +
      (rG L.sc : ℝ) * NplusF L.sc n' * c0num L⌉₊

def DIf (K : Consts) (L : GParameters D) (p n' : ℕ) : ℕ :=
  ⌈K.DI * NplusF L.sc n' * (L.sc.x ^ (Scale.A / 2)) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) *
      Real.logb p L.sc.a⌉₊

def tIIf (K : Consts) (L : GParameters D) (p n' N : ℕ) : ℝ :=
  K.tII * (rG L.sc : ℝ) * (N : ℝ) * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) +
    L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) + c0num L + (D.R.k : ℝ) * Qp L.sc p) +
    2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L

def kapIIf (K : Consts) (L : GParameters D) (N : ℕ) : ℝ :=
  min 1 (K.kII * (N : ℝ) * (rG L.sc : ℝ) ^ 2 * (D.R.k : ℝ) * L.sc.x ^ (-Scale.A))

def c6f (K : Consts) (L : GParameters D) (p n' : ℕ) : ℝ :=
  8 * ((DIf K L p n' : ℝ) + 1) + K.kappaThresholdTwo * NplusF L.sc n' * (D.R.k : ℝ) * Real.logb p L.sc.a +
    4 * NplusF L.sc n' * cG L + 2 * (n' : ℝ) * cG L

open Classical in
def tIf (K : Consts) (L : GParameters D) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : ℝ :=
  (∑ y ∈ TT.filter (fun y => ¬ IsTypeV y),
      (if dMinus TT y = 0 then 0 else
        min (b y : ℝ) ((a (posAdd y (n' - dMinus TT y)) : ℝ) / (p : ℝ) ^ dMinus TT y))) +
    K.kappaThresholdOne * (TT.card : ℝ) * (N1 L.sc : ℝ) *
      (L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) +
    K.kappaThresholdTwo * (TT.card : ℝ) * (Qp L.sc p * c6f K L p n' +
      (D.R.k : ℝ) * Qp L.sc p +
      (D.R.k : ℝ) * Real.logb p L.sc.a + cG L) + 2 * (n' : ℝ) * cG L

def kapLoc (X : Inst D L) (K : Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : ℝ :=
  if (p : ℝ) < L.sc.p0 D.R.k then kapIIf K L TT.card else X.kapI p n' TT a b

def al (L : GParameters D) (a : HH D → ℤ) (s : HH D) : ℝ := (a s : ℝ) - 2 * cG L

def capU (X : Inst D L) (b : HH D → ℤ) (p j : ℕ) (s : HH D) (e : ℕ) : ℝ :=
  fillG X b j (partner D p s e) + cG L

def IsDist (D : GD) (p : ℕ) (s s' : HH D) (e : ℕ) : Prop :=
  0 < e ∧ partner D p s e = (false, s') ∧ ∀ e', 0 < e' → e' < e → partner D p s e' ≠ (false, s')

def Excl (D : GD) (p : ℕ) (s : HH D) (e : ℕ) : Prop :=
  Odd e ∧ ∃ s' ∈ D.host.TT, s' ≠ s ∧ IsDist D p s s' e

def dl (X : Inst D L) (K : Consts) (p : ℕ) (t0 : HH D) : ℝ :=
  K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
    K.dl2 * (Nv X p t0 : ℝ) * Real.logb p (2 * L.sc.a) ^ 2

open Classical in
def g0 (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  (∑ s ∈ topsOn X p t0, ∑' e : ℕ,
    if Odd e ∧ ¬ Excl D p s e then max 0 (al L a s / (p : ℝ) ^ e - capU X b p j s e) else 0) -
    dl X K p t0

open Classical in
def gU (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  gam p * (∑ s ∈ topsOn X p t0, al L a s) -
    (∑ s ∈ (topsOn X p t0).filter (fun s => ¬ IsV X p s), ∑' e : ℕ,
      if Odd e then min (al L a s / (p : ℝ) ^ e) (capU X b p j s e) else 0) -
    dl X K p t0

open Classical in
def Pr (X : Inst D L) (K : Consts) (b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  if L.sc.p0 D.R.k ≤ (p : ℝ) then
    (∑ s ∈ (topsOn X p t0).filter (fun s => ¬ IsV X p s), (fillG X b j (false, s) - (b s : ℝ))) +
      K.Pr1 * (nP D p : ℝ) * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D)
  else (rG L.sc : ℝ) * ((Nv X p t0 : ℝ) * (2 * L.sc.b' + cG L) +
      (nP D p : ℝ) * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D))

def Dp (K : Consts) (L : GParameters D) (p : ℕ) : ℕ :=
  if (p : ℝ) < L.sc.p0 D.R.k then DIIf K L p (nP D p) else DIf K L p (nP D p)

def tv (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (t0 : HH D) : ℝ :=
  if (p : ℝ) < L.sc.p0 D.R.k then tIIf K L p (nP D p) (Nv X p t0)
  else tIf K L p (addOrderOf (hP D p)) (topsPos D p t0) (wPos D p t0 a) (wPos D p t0 b)

def kapv (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (t0 : HH D) : ℝ :=
  kapLoc X K p (addOrderOf (hP D p)) (topsPos D p t0) (wPos D p t0 a) (wPos D p t0 b)

def Cand (D : GD) (L : GParameters D) (K : Consts) (p : ℕ) : Prop :=
  p.Prime ∧ (p : ℝ) < L.sc.X' ∧ IsResidueClassZero D p ∧ L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ) ∧
    (L.sc.p0 D.R.k ≤ (p : ℝ) → ¬ InBand D K L.sc p)

open Classical in
def goodReps (X : Inst D L) (p : ℕ) : Finset (HH D) := (reps X p).filter (fun t0 => Good X p t0)

def Sig (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  (D.R.m : ℝ) * ∑ t0 ∈ goodReps X p, kapv X K a b p t0

open Classical in
def VV (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : Finset (HH D) :=
  if Cand D L K p ∧ Sig X K a b p ≤ L.sc.x ^ (-L.sc.eps) then goodReps X p else ∅

def Sv (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (t0 : HH D) : ℝ :=
  (⌈∑ j ∈ GParameters.lifts D, max 0 (gU X K a b p j t0 - Pr X K b p j t0 - max (g0 X K a b p j t0) 0)⌉ : ℤ)

open Classical in
def tauP (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  if VV X K a b p = ∅ then 0 else
    (X.ep p : ℝ) + ∑ t0 ∈ VV X K a b p,
      (D.R.m : ℝ) * ((⌈tv X K a b p t0⌉₊ : ℝ) + (Dp K L p : ℝ) + 1)

open Classical in
def ioP (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  if h : (VV X K a b p).Nonempty then
    2 * Sig X K a b p * (VV X K a b p).sup' h (fun t0 => Sv X K a b p t0)
  else 0

open Classical in
def gainP (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) : ℝ :=
  if (IsResidueClassZero D p ∧ hP D p = 0) ∨ L.sc.X'' D.R.n < (p : ℝ) then 0 else
    (∑ t0 ∈ VV X K a b p, max (gU X K a b p j t0 - Pr X K b p j t0) (max (g0 X K a b p j t0) 0)) +
    ∑ t0 ∈ reps X p \ VV X K a b p, max (g0 X K a b p j t0) 0

open Classical in
def TTP (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : Finset (HH D) :=
  if IsSg D p ∨ L.sc.X' ≤ (p : ℝ) then D.host.TT
  else D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ VV X K a b p)

end Formalism.MainNotions.Inhab.GC

end
end

