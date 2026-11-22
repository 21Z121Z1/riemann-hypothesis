import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChBalance
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.MeanSquareBounds.Bundle0001

-- bundled from Development.AutomorphicArithmetic.ConductorsKronecker.ChCond
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

section
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]

private theorem UpperTheory.GL.primVal_of_periodic {N c : ℕ} [NeZero N] (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (E0 × A)) (ψ : AddChar (E0 × A) ℂ) (F : ℕ →* ℤ) (hc : c ∣ N)
    (hF : ∀ x y, x ≡ y [MOD c] → F x = F y)
    (hψ : ∀ u : (ZMod N)ˣ, ψ (Multiplicative.toAdd (r u)) = ((F (u : ZMod N).val : ℤ) : ℂ))
    (hram : ∀ p, p.Prime → p ∣ c → F p = 0 ∧
      ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[p] N] ∧ F (u : ZMod N).val = -1)
    (n : ℕ) (hn : n ≠ 0) : primVal (cftData q d r) ψ n = ((F n : ℤ) : ℂ) := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors, map_prod, Int.cast_prod]
  unfold primVal
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hi : n.factorization p ≠ 0 := by
    have := (Nat.support_factorization n ▸ hp : p ∈ n.factorization.support)
    exact Finsupp.mem_support_iff.1 this
  rw [map_pow, Int.cast_pow]
  by_cases hpc : p ∣ c
  · obtain ⟨h0, u, hu, hu1⟩ := hram p hpp hpc
    rw [cosetMean_of_nontrivial, h0, Int.cast_zero, zero_pow hi]
    intro h
    have := h _ ((mem_inertia_iff q d r p _).2 ⟨u, (mem_localUnits_iff p u).2 hu, rfl⟩)
    rw [hψ, hu1] at this
    norm_num at this
  · have hcd : c ∣ ordCompl[p] N := Nat.dvd_ordCompl_of_dvd_not_dvd hc hpc
    rw [cosetMean_of_trivial, AddChar.map_nsmul_eq_pow]
    · congr 1
      change ψ (Multiplicative.toAdd (r (frobUnit N p))) = _
      rw [hψ, hF _ _ ((frobUnit_modEq hpp).1.of_dvd hcd)]
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff q d r p _).1 hx
      rw [hψ, hF _ _ (((mem_localUnits_iff p u).1 hu).of_dvd hcd), map_one, Int.cast_one]

private theorem UpperTheory.GL.conductor_of_periodic {N c : ℕ} [NeZero N]
    (r : (ZMod N)ˣ →* Multiplicative (E0 × A)) (ψ : AddChar (E0 × A) ℂ) (F : ℕ →* ℤ) (hc : c ∣ N) (hp : c.Prime)
    (hF : ∀ x y, x ≡ y [MOD c] → F x = F y)
    (hψ : ∀ u : (ZMod N)ˣ, ψ (Multiplicative.toAdd (r u)) = ((F (u : ZMod N).val : ℤ) : ℂ))
    (hram : ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[c] N] ∧ F (u : ZMod N).val = -1) :
    (dirChar r ψ).conductor = c := by
  apply Nat.dvd_antisymm
  · rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ hc,
      DirichletCharacter.mem_conductorSet_iff,
      DirichletCharacter.factorsThrough_iff_ker_unitsMap hc]
    intro u hu
    rw [MonoidHom.mem_ker, unitsMap_eq_one_iff] at hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, dirChar_unit, Units.val_one, hψ, hF _ _ hu,
      map_one, Int.cast_one]
  · by_contra hh
    obtain ⟨u, hu, hu1⟩ := hram
    have := (inertia_conductor (H := A) N 0 0 r ψ c (NeZero.ne N) hp).2 hh _
      ((mem_inertia_iff 0 0 r c _).2 ⟨u, (mem_localUnits_iff c u).2 hu, rfl⟩)
    rw [hψ, hu1] at this
    norm_num at this

end

private def UpperTheory.GL.jac (l : ℕ) : ℕ →* ℤ where
  toFun a := jacobiSym (a : ℤ) l
  map_one' := by simp
  map_mul' a b := by rw [Nat.cast_mul, jacobiSym.mul_left]

private theorem UpperTheory.GL.exists_nonres {N l : ℕ} [NeZero N] (hl : l.Prime) (h2 : l ≠ 2) (hN : l ∣ N) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[l] N] ∧ jacobiSym ((u : ZMod N).val : ℤ) l = -1 := by
  have : Fact l.Prime := ⟨hl⟩
  have hN0 := NeZero.ne N
  have hcop : (ordProj[l] N).Coprime (ordCompl[l] N) := (Nat.coprime_ordCompl hl hN0).pow_left _
  have hlP : l ∣ ordProj[l] N := Nat.dvd_ordProj_of_dvd hN0 hl hN
  have : NeZero (ordProj[l] N) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨x, hx⟩ := quadraticChar_exists_neg_one' (F := ZMod l) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨y, hy⟩ := ZMod.unitsMap_surjective hlP x
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (Nat.ordProj_mul_ordCompl_eq_self N l).symm hcop
      (Nat.ordProj_dvd N l) (Nat.ordCompl_dvd N l) y 1
  refine ⟨u, (unitsMap_eq_one_iff _ u).1 hu2, ?_⟩
  have h3 : ZMod.unitsMap hN u = x := by
    rw [← hy, ← hu1, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, ← hx, ← h3, ZMod.unitsMap_val,
    ZMod.natCast_val]

private theorem UpperTheory.GL.sgn_val (s : ℤˣ) :
    (if Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 s) = 0 then (1 : ℂ) else -1) = (((s : ℤˣ) : ℤ) : ℂ) := by
  rw [sgn2_toAdd_eq_ite]
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp

theorem UpperTheory.GL.ch_cond :
    ∀ {φ : Frame} (H : HostAx φ), (dirChar (recH H.toHostRaw) chC).conductor = H.d ∧
      (∀ n : ℕ, n ≠ 0 → primVal (arith H.toHostRaw) chC n = ((jacobiSym (n : ℤ) H.d : ℤ) : ℂ)) ∧
      (H.PsQ → (dirChar (recH H.toHostRaw) psC).conductor = H.q ∧
        (∀ n : ℕ, n ≠ 0 → primVal (arith H.toHostRaw) psC n = ((jacobiSym (n : ℤ) H.q : ℤ) : ℂ)) ∧
        ∀ n : ℕ, n ≠ 0 → primVal (arith H.toHostRaw) chpsC n = ((jacobiSym (n : ℤ) H.d * jacobiSym (n : ℤ) H.q : ℤ) : ℂ)) := by
  intro φ H
  have hd := H.d_prime
  have hq := H.q_prime
  have ed := exists_nonres hd H.d_ne_two H.d_dvd_condN
  have eq := exists_nonres hq H.q_ne_two H.q_dvd_condN
  have hch : ∀ u : (ZMod H.condN)ˣ, (chC : AddChar (E0 × φ.A) ℂ) (Multiplicative.toAdd (recH H.toHostRaw u))
      = ((jac H.d (u : ZMod H.condN).val : ℤ) : ℂ) := by
    intro u
    change _ = ((jacobiSym _ _ : ℤ) : ℂ)
    rw [← H.der.art_ch u]
    exact sgn_val _
  have one : ∀ l : ℕ, l.Prime → (∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧
      jacobiSym ((u : ZMod H.condN).val : ℤ) l = -1) → ∀ p, p.Prime → p ∣ l → jac l p = 0 ∧
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[p] H.condN] ∧
        jac l (u : ZMod H.condN).val = -1 := by
    intro l hl e p hp hpl
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hl).1 hpl
    exact ⟨jac_self p hp.one_lt, e⟩
  refine ⟨conductor_of_periodic _ _ (jac H.d) H.d_dvd_condN hd (fun _ _ h => jacobi_congr h) hch ed,
    primVal_of_periodic _ _ _ _ (jac H.d) H.d_dvd_condN (fun _ _ h => jacobi_congr h) hch (one _ hd ed), fun hP => ?_⟩
  have hps : ∀ u : (ZMod H.condN)ˣ, (psC : AddChar (E0 × φ.A) ℂ) (Multiplicative.toAdd (recH H.toHostRaw u))
      = ((jac H.q (u : ZMod H.condN).val : ℤ) : ℂ) := by
    intro u
    change _ = ((jacobiSym _ _ : ℤ) : ℂ)
    rw [← hP u]
    exact sgn_val _
  refine ⟨conductor_of_periodic _ _ (jac H.q) H.q_dvd_condN hq (fun _ _ h => jacobi_congr h) hps eq,
    primVal_of_periodic _ _ _ _ (jac H.q) H.q_dvd_condN (fun _ _ h => jacobi_congr h) hps (one _ hq eq), ?_⟩
  refine primVal_of_periodic (c := H.d * H.q) _ _ _ _ (jac H.d * jac H.q)
    (H.coprime_q_d.symm.mul_dvd_of_dvd_of_dvd H.d_dvd_condN H.q_dvd_condN) (fun x y h => ?_) (fun u => ?_) ?_
  · change jacobiSym _ _ * jacobiSym _ _ = jacobiSym _ _ * jacobiSym _ _
    rw [jacobi_congr (h.of_dvd (dvd_mul_right _ _)), jacobi_congr (h.of_dvd (dvd_mul_left _ _))]
  · unfold chpsC
    rw [AddChar.mul_apply, hch, hps, MonoidHom.mul_apply, Int.cast_mul]
  · intro p hp hpl
    rcases hp.dvd_mul.1 hpl with h | h
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hd).1 h
      obtain ⟨u, hu, hu1⟩ := ed
      have hqd : H.q ∣ ordCompl[H.d] H.condN := Nat.dvd_ordCompl_of_dvd_not_dvd H.q_dvd_condN
        (fun hh => H.q_ne_d ((Nat.prime_dvd_prime_iff_eq hd hq).1 hh).symm)
      refine ⟨?_, u, hu, ?_⟩
      · change jacobiSym _ _ * jacobiSym _ _ = 0
        rw [jac_self _ hd.one_lt, zero_mul]
      · change jacobiSym _ _ * jacobiSym _ _ = -1
        rw [hu1, jacobi_congr (hu.of_dvd hqd)]
        simp
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hq).1 h
      obtain ⟨u, hu, hu1⟩ := eq
      have hqd : H.d ∣ ordCompl[H.q] H.condN := Nat.dvd_ordCompl_of_dvd_not_dvd H.d_dvd_condN
        (fun hh => H.q_ne_d ((Nat.prime_dvd_prime_iff_eq hq hd).1 hh))
      refine ⟨?_, u, hu, ?_⟩
      · change jacobiSym _ _ * jacobiSym _ _ = 0
        rw [jac_self _ hq.one_lt, mul_zero]
      · change jacobiSym _ _ * jacobiSym _ _ = -1
        rw [hu1, jacobi_congr (hu.of_dvd hqd)]
        simp
end

-- bundled from Development.AutomorphicArithmetic.ConductorsKronecker.CostPropositionBasicBound
section
open Finset ArithmeticFunction

noncomputable section

namespace UpperTheory.GL

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Deduction.CH

theorem cost_proposition_basic_bound {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (S : Finset ℕ)
    (hD : HostFactsS D S) (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (x ε b b' η X' θ Cd CL Err : ℝ)
    (hH : GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err) :
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL)
      ≤ Err + (TT.card : ℝ) * m * (2 * fPl H * (x + 1) * b * θ)
        + (TT.card : ℝ) * m * (6 * fPl H * (x + 1) * (η + 1)) := by
  obtain ⟨hx, hb, hη, hX', hb', hbX, hθ, hCd, ha, ⟨hwpos, hwthick, hwthin⟩, hN, hTop, hThin, hLip, hDer, hVal⟩ := hH
  have haB : ∀ t ∈ TT, (x - 1) * b ≤ a t ∧ a t ≤ (x + 1) * b := by
    intro t ht
    obtain ⟨h1, h2⟩ := abs_le.1 (ha t ht)
    constructor
    · have : x - 1 ≤ a t / b := by linarith
      rwa [le_div_iff₀ hb] at this
    · have : a t / b ≤ x + 1 := by linarith
      rwa [div_le_iff₀ hb] at this
  have hapos : ∀ t ∈ TT, 0 < a t := fun t ht => lt_of_lt_of_le (by nlinarith) (haB t ht).1
  have hf := CR.fPl_pos (H := H)

  have hA : topExcess D N ell TT a w = (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
      balTop (CR.host D ell) (a t) t (w u0 j) := by
    unfold topExcess
    refine congrArg _ (Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun t ht =>
      Finset.sum_congr rfl fun j _ => ?_)
    have h1 := Deduction.ch_balance D S hD ell (a t) t (w u0 j) (hapos t ht) (hwpos u0 j) N (fun ρ hρ => hN u0 j t ρ ht hρ)
    have h2 := congrArg Complex.re h1
    rw [Complex.sub_re, Complex.ofReal_re, CR.De_re] at h2
    exact h2

  have hB : ∀ u0 : H, ∀ t ∈ TT, ∀ j : Fin m,
      balTop (CR.host D ell) (CR.aR TT a t) t (CR.wR T2 b w u0 j)
        ≤ balTop (CR.host D ell) (a t) t (w u0 j) + 2 * fPl H * (3 * (x + 1) * (η + 1)) := by
    intro u0 t ht j
    rw [CR.aR_mem TT a ht]
    have hd := CR.balTop_diff (CR.host D ell) (a t) t (w u0 j) (CR.wR T2 b w u0 j) (3 * (x + 1) * (η + 1))
      (by positivity) (by
        intro g hg ψ
        have hρ := CR.partner_inPhi t hg
        by_cases hth : IsThickAt T2 u0 (cconj + g + topPl t)
        · rw [CR.wR_thick T2 b w u0 j _ hth]
          obtain ⟨h1, h2⟩ := hwthick u0 j _ hth
          have hl := hLip ψ (a t) (w u0 j (cconj + g + topPl t)) b (hapos t ht) (hwpos u0 j _ hρ) hb
          rw [min_eq_right h1, abs_of_nonneg (by linarith)] at hl
          refine le_trans hl ?_
          have e1 : 3 * a t / b ≤ 3 * (x + 1) := by
            rw [div_le_iff₀ hb]; nlinarith [(haB t ht).2]
          have e0 : 0 ≤ 3 * a t / b := by have := hapos t ht; positivity
          exact mul_le_mul e1 (by linarith) (by linarith) (by positivity)
        · rw [CR.wR_thin T2 b w u0 j _ hth hρ, sub_self, norm_zero]; positivity)
    have := (abs_le.1 hd).1
    linarith
  have hB' := CR.mean_le TT (fun u0 t j => balTop (CR.host D ell) (CR.aR TT a t) t (CR.wR T2 b w u0 j))
    (fun u0 t j => balTop (CR.host D ell) (a t) t (w u0 j)) _ hB

  have hTA := thick_average_formula (H := H) (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos)

  have hC : ∀ u0 : H, ∀ t ∈ TT, ∀ j : Fin m, (0 : ℝ) ≤
      ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt T2 u0 (cconj + g + topPl t)),
      ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((CR.wR T2 b w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC (CR.host D ell) ψ (CR.aR TT a t / CR.wR T2 b w u0 j (cconj + g + topPl t))).re
        + 2 * fPl H * ((x + 1) * b * θ) := by
    intro u0 t ht j
    rw [CR.aR_mem TT a ht]
    have hn := CR.norm_avg_le (univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt T2 u0 (cconj + g + topPl t)))
      (CR.card_S_le t _ (by
        intro g hg
        rw [Finset.mem_filter] at hg ⊢
        exact ⟨hg.1, hg.2.1⟩))
      (fun g ψ => ((CR.wR T2 b w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC (CR.host D ell) ψ (a t / CR.wR T2 b w u0 j (cconj + g + topPl t)))
      ((x + 1) * b * θ) (by positivity) (by
        intro g hg ψ
        obtain ⟨hg1, hg2⟩ := (Finset.mem_filter.1 hg).2
        have hρ := CR.partner_inPhi t hg1
        rw [CR.wR_thin T2 b w u0 j _ hg2 hρ]
        have hw0 := hwpos u0 j _ hρ
        have hw2 := hwthin u0 j _ hρ hg2
        have hy : X' / 3 ≤ a t / w u0 j (cconj + g + topPl t) := by
          rw [le_div_iff₀ hw0]
          have h1 : X' / 3 * w u0 j (cconj + g + topPl t) ≤ X' / 3 * (2 * b') :=
            mul_le_mul_of_nonneg_left hw2 (by positivity)
          have h2 := (haB t ht).1
          nlinarith
        have ht' := hThin ψ _ hy
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
        calc w u0 j (cconj + g + topPl t) * ‖GC (CR.host D ell) ψ (a t / w u0 j (cconj + g + topPl t))‖
            ≤ w u0 j (cconj + g + topPl t) * (a t / w u0 j (cconj + g + topPl t) * θ) :=
              mul_le_mul_of_nonneg_left ht' hw0.le
          _ = a t * θ := by field_simp
          _ ≤ (x + 1) * b * θ := mul_le_mul_of_nonneg_right (haB t ht).2 hθ)
    have hre := (abs_le.1 (le_trans (Complex.abs_re_le_norm _) hn)).1
    simp only [mul_assoc] at hre ⊢
    linarith
  have hC' := CR.mean_le TT (fun _ _ _ => (0 : ℝ)) _ _ hC
  have hrest : -((TT.card : ℝ) * m * (2 * fPl H * ((x + 1) * b * θ)))
      ≤ restAvg (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos) := by
    simp only [Finset.sum_const_zero, mul_zero] at hC'
    have : restAvg (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos) = _ := rfl
    unfold restAvg
    show -((TT.card : ℝ) * m * (2 * fPl H * ((x + 1) * b * θ))) ≤ (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
      ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt T2 u0 (cconj + g + topPl t)),
      ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((CR.wR T2 b w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC (CR.host D ell) ψ (CR.aR TT a t / CR.wR T2 b w u0 j (cconj + g + topPl t))).re
    linarith

  have hD' : (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL)
      ≤ signal (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos) := by
    show _ ≤ ((T2.card : ℝ) / Fintype.card H) / 2 * ∑ t ∈ TT, ∑ j : Fin m, b *
      (GC (CR.host D ell) 0 (CR.aR TT a t / b) + GC (CR.host D ell) psC (CR.aR TT a t / b)
        - GC (CR.host D ell) chC (CR.aR TT a t / b) - GC (CR.host D ell) chpsC (CR.aR TT a t / b)).re
    have hs : ∑ t ∈ TT, ∑ _j : Fin m, b * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL)
        ≤ ∑ t ∈ TT, ∑ j : Fin m, b *
      (GC (CR.host D ell) 0 (CR.aR TT a t / b) + GC (CR.host D ell) psC (CR.aR TT a t / b)
        - GC (CR.host D ell) chC (CR.aR TT a t / b) - GC (CR.host D ell) chpsC (CR.aR TT a t / b)).re := by
      refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun j _ => ?_
      rw [CR.aR_mem TT a ht]
      exact mul_le_mul_of_nonneg_left (CR.signal_term D ell hx hCd (ha t ht) hDer hVal) hb.le
    have hδ : 0 ≤ ((T2.card : ℝ) / Fintype.card H) / 2 := by positivity
    have := mul_le_mul_of_nonneg_left hs hδ
    refine le_trans (le_of_eq ?_) this
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    unfold delta2; ring

  have hTA' : (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
      balTop (CR.host D ell) (CR.aR TT a t) t (CR.wR T2 b w u0 j)
      = signal (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos)
        + restAvg (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos) := hTA
  rw [← hA, hTA'] at hB'
  have e1 : (TT.card : ℝ) * m * (2 * fPl H * (3 * (x + 1) * (η + 1)))
      = (TT.card : ℝ) * m * (6 * fPl H * (x + 1) * (η + 1)) := by ring
  have e2 : (TT.card : ℝ) * m * (2 * fPl H * ((x + 1) * b * θ))
      = (TT.card : ℝ) * m * (2 * fPl H * (x + 1) * b * θ) := by ring
  rw [e1] at hB'
  rw [e2] at hrest
  linarith

theorem card_mul_delta_le_err {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (S : Finset ℕ)
    (hD : HostFactsS D S) (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (x ε b b' η X' θ Cd CL Err : ℝ)
    (hH : GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err) (hS : SmallCosts x ε (fPl H) b η θ Cd CL) :
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 4 * x ^ ((1 : ℝ) / 2 + ε))
      ≤ Err + 2 * (TT.card : ℝ) * m * b / x := by
  have hc := cost_proposition_basic_bound D S hD ell N m TT T2 a w x ε b b' η X' θ Cd CL Err hH
  obtain ⟨hMv, hth, hlip⟩ := hS
  have hx : 3 ≤ x := hH.1
  have hb : 0 < b := hH.2.1
  have hK : 0 ≤ (TT.card : ℝ) * m := by positivity
  have hδ : 0 ≤ delta2 T2 / 2 := by unfold delta2; positivity
  have h1 : (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 4 * x ^ ((1 : ℝ) / 2 + ε))
      ≤ (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : (TT.card : ℝ) * m * (2 * fPl H * (x + 1) * b * θ) ≤ (TT.card : ℝ) * m * (b * (1 / x)) := by
    apply mul_le_mul_of_nonneg_left _ hK
    calc 2 * fPl H * (x + 1) * b * θ = b * (2 * fPl H * (x + 1) * θ) := by ring
      _ ≤ b * (1 / x) := mul_le_mul_of_nonneg_left hth hb.le
  have h3 : (TT.card : ℝ) * m * (6 * fPl H * (x + 1) * (η + 1)) ≤ (TT.card : ℝ) * m * (b / x) :=
    mul_le_mul_of_nonneg_left hlip hK
  have e : 2 * (TT.card : ℝ) * m * b / x = (TT.card : ℝ) * m * (b * (1 / x)) + (TT.card : ℝ) * m * (b / x) := by
    ring
  rw [e]; linarith

theorem cost_proposition_at_scale {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (S : Finset ℕ)
    (hD : HostFactsS D S) (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (C x ε b b' η X' θ Cd CL Err k aE : ℝ)
    (hH : GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err) (hS : SmallCosts x ε (fPl H) b η θ Cd CL)
    (hW : SizeWindows C ε x (Fintype.card H) TT.card T2.card m b k aE Err) :
    Gz x ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) :=
  proposition_size_bound C ε x (Fintype.card H) TT.card T2.card m b k aE Err (Gz x) hW
    (card_mul_delta_le_err D S hD ell N m TT T2 a w x ε b b' η X' θ Cd CL Err hH hS)

end UpperTheory.GL

end
end

-- bundled from Development.AutomorphicArithmetic.ConductorsKronecker.IsInertIff
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

private lemma notInPhi_iff {φ : Frame} (H : HostAx φ) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hd : p ≠ H.d) :
    ¬ Formalism.D5.InPhi ((arith H.toHostRaw).frob p) ↔ jacobiSym (-(H.d : ℤ)) p = -1 := by
  have hdp := H.toHostRaw.d_prime
  have hN0 : H.condN ≠ 0 := by
    simp only [HostRaw.condN]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero) hdp.ne_zero
  haveI : NeZero H.condN := ⟨hN0⟩
  set u := frobUnit H.condN p with hu
  obtain ⟨h1, -⟩ := frobUnit_modEq (N := H.condN) hp
  have hcop : Nat.Coprime (p ^ H.condN.factorization p) H.d :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hdp).mpr hd)
  have hdm : H.d ∣ H.condN / p ^ H.condN.factorization p := by
    have hsplit := Nat.ordProj_mul_ordCompl_eq_self H.condN p
    have : H.d ∣ p ^ H.condN.factorization p * (H.condN / p ^ H.condN.factorization p) := by
      rw [hsplit]; exact H.d_dvd_condN
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
  have hmod : (u : ZMod H.condN).val ≡ p [MOD H.d] := Nat.ModEq.of_dvd hdm h1
  have hJ : jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d = jacobiSym (-(H.d : ℤ)) p := by
    rw [jacobi_congr hmod]
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
    exact (jacobi_neg_recip H.d_mod_four hodd).symm
  have hart := H.der.art_ch u
  rw [hJ] at hart
  show ¬ (Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 (H.art u).1.2) = 0) ↔ _
  rw [sgn2_toAdd_eq_zero_iff, ← hart]
  rcases Int.units_eq_one_or (H.art u).1.2 with hs | hs
  · rw [hs]; simp
  · rw [hs]; simp

theorem UpperTheory.GL.isInert_iff :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), IsInert (arith H.toHostRaw) p ↔ p.Prime ∧ ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = -1 := by
  intro φ H p
  constructor
  · rintro ⟨hp, h2, -, hd, h⟩
    have hj := (notInPhi_iff H hp h2 hd).1 h
    exact ⟨hp, H.not_dvd_condN_of_inert hp h2 hj, hj⟩
  · rintro ⟨hp, hN, hj⟩
    exact ⟨hp, HostRaw.ne_two_of_not_dvd hN, HostRaw.ne_q_of_not_dvd hN, HostRaw.ne_d_of_not_dvd hN,
      (notInPhi_iff H hp (HostRaw.ne_two_of_not_dvd hN) (HostRaw.ne_d_of_not_dvd hN)).2 hj⟩
end

-- bundled from Development.AutomorphicArithmetic.ConductorsKronecker.OddQSLe
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

theorem UpperTheory.GL.oddQS_le :
    ∀ {φ : Frame} (H : HostRaw φ) (C : ℝ), (φ.o : ℝ) ≤ C → (H.QS : ℝ) ≤ C * φ.ord → ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ C ^ 2 := by
  intro φ H C ho hQ
  have h0 : H.QS ≠ 0 := H.QS_pos.ne'
  have hC : (0 : ℝ) ≤ C := (Nat.cast_nonneg _).trans ho
  have h1 : φ.e + 2 ≤ H.QS.factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization h0).1 H.tower_dvd
  have h2 : 2 ^ φ.e * ordCompl[2] H.QS ≤ H.QS := by
    conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self H.QS 2]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (by omega))
  have h3 : (φ.ord : ℝ) ≤ φ.o * 2 ^ φ.e := by exact_mod_cast φ.ord_le_o_mul_two_pow
  have h4 : (2 : ℝ) ^ φ.e * ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ H.QS := by exact_mod_cast h2
  have hp : (0 : ℝ) < 2 ^ φ.e := by positivity
  have h5 : (φ.ord : ℝ) ≤ C * 2 ^ φ.e := h3.trans (mul_le_mul_of_nonneg_right ho hp.le)
  refine le_of_mul_le_mul_left ?_ hp
  calc (2 : ℝ) ^ φ.e * ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ C * φ.ord := h4.trans hQ
    _ ≤ C * (C * 2 ^ φ.e) := mul_le_mul_of_nonneg_left h5 hC
    _ = 2 ^ φ.e * C ^ 2 := by ring
end

-- bundled from Development.AutomorphicArithmetic.ConductorsKronecker.realClass
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

private theorem realClass_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hreal : ∀ a : ZMod N, (χ a).im = 0) : χ ^ 2 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply u.isUnit]
  have hn : ‖χ (u : ZMod N)‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
  have him : (χ (u : ZMod N)).im = 0 := hreal _
  set z := χ (u : ZMod N) with hz
  have h1 : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  have h2 : z.re ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hn, Complex.normSq_apply, him] at this
    nlinarith
  rw [h1]; exact_mod_cast h2

private theorem realClass_level_dvd {φ : Frame} (H : HostRaw φ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : H.IsCharE χ) : N ∣ H.condN := by
  obtain ⟨θ, hθ⟩ := h
  have e := (H.isPrimOf_iff θ ⟨N, χ, hθ.1⟩).1 hθ
  have e2 : N = (H.dir θ).conductor := congrArg Formalism.HC.PChar.N e
  rw [e2]
  exact DirichletCharacter.conductor_dvd_level _

theorem UpperTheory.GL.realClass :
    ∀ {φ : Frame} (H : HostRaw φ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsCharE χ →
      N ∣ H.condN ∧ ((∀ a : ZMod N, (χ a).im = 0) → N ∣ 8 * ordCompl[2] H.QS ∨ H.q ∣ N ∨ H.d ∣ N) := by
  intro φ H N _ χ hχ
  have hdvd := realClass_level_dvd H χ hχ
  refine ⟨hdvd, fun hreal => ?_⟩
  have hp : χ.IsPrimitive := by
    obtain ⟨θ, hθ⟩ := hχ
    exact hθ.1
  have h2 := realClass_sq χ hreal
  by_cases hqd : H.q ∣ N ∨ H.d ∣ N
  · exact Or.inr hqd
  · left
    have hq : H.q.Prime := H.hyp.1
    have hd : H.d.Prime := H.hyp.2.1
    rw [not_or] at hqd
    have hN : N ∣ 8 * ordCompl[2] H.QS * H.q * H.d := by
      refine QH.real_cond _ H.q H.d N χ hp h2 (dvd_mul_right _ _) hq hd fun p hpp hpN => ?_
      have h3 : p ∣ H.QS * H.q * H.d := hpN.trans hdvd
      rcases hpp.dvd_mul.1 h3 with h4 | h4
      · rcases hpp.dvd_mul.1 h4 with h5 | h5
        · left
          rw [← Nat.ordProj_mul_ordCompl_eq_self H.QS 2] at h5
          rcases hpp.dvd_mul.1 h5 with h6 | h6
          · exact ((hpp.dvd_of_dvd_pow h6).trans (by norm_num)).mul_right _
          · exact h6.mul_left _
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp hq).1 h5))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hpp hd).1 h4))
    have cq : N.Coprime H.q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hqd.1).symm
    have cd : N.Coprime H.d := ((Nat.Prime.coprime_iff_not_dvd hd).2 hqd.2).symm
    exact cq.dvd_of_dvd_mul_right (cd.dvd_of_dvd_mul_right hN)
end

