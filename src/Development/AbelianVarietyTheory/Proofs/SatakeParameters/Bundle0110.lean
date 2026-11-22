import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnfoldingIsGoodCyclotomicInvariantReferenceLatti
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator GlobalTheory.LastSteps

noncomputable section

namespace GlobalTheory.ColPeriod

section Unfold

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem good_om_two {N' N : ℕ} {e' e : ℕ → ℤ} {Φ : HomE E N' N → K}
    (h : Good P (homS (LocE.sclLat P (qOf P) N' e') (LocE.sclLat P (qOf P) N e)) Φ) (cq sq : K)
    (χ₀ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {g : Sp E N' ≃ₗ[E] Sp E N'} (hg : g ∈ stabL E N' (LocE.sclLat P (qOf P) N' e'))
    {k : Sp E N ≃ₗ[E] Sp E N} (hk : k ∈ stabL E N (LocE.sclLat P (qOf P) N e)) :
    Good P (homS (LocE.sclLat P (qOf P) N' e') (LocE.sclLat P (qOf P) N e))
      (Loc.om (LocE.locChar (qOf P) cq χ₀) (LocE.vP P (qOf P)) sq g k Φ) := by
  have hu := isUnit_det_of_stab hg
  have h1 := isUnit_det_of_stab hk
  unfold Loc.om
  rw [locChar_unit _ _ hu, locChar_unit _ _ h1, vP_unit hu, vP_unit h1]
  refine Good.const_mul (h.comp (H' := homS (LocE.sclLat P (qOf P) N' e') (LocE.sclLat P (qOf P) N e))
    (fun x => k.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap)
    (fun x z => ?_) fun w => ⟨fun hw y hy => (inv_mem hk _).2 (hw _ ((hg y).2 hy)), fun hw y hy => ?_⟩) ?_
  · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul]
  · have := hw (g.symm y) ((hg _).1 (by simpa using hy))
    rw [← g.apply_symm_apply y]
    exact (inv_mem hk _).1 this
  · simp only [neg_zero, zero_mul, zpow_zero, mul_one]
    exact mul_mem (unitV_mem _ _) (unitV_inv_mem _ _)

omit [NumberField E] [StarRing E] in
theorem freeCoordinateExtension_apply_single {n' c' n c : ℕ} (xj : HomE E n' n) (t : Loc.FC n' c' n c → E) (l : Fin (n + c)) (s : Fin (n' + c')) :
    Loc.xx1 xj t (Pi.single s 1) l =
      if hf : Loc.IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
      else if hs : s.1 < n' then (if hl : l.1 < n then xj (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0)
      else if l.1 = n + (s.1 - n') then 1 else 0 := by
  unfold Loc.xx1
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  simp only [Matrix.col_apply, Matrix.of_apply, LinearMap.toMatrix'_apply]

theorem intAt_zpow {z : ℤ} (hz : 0 ≤ z) : IntAt P ((qOf P : E) ^ z) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  rw [zpow_natCast]
  exact intAt_pow (intAt_nat _) _

theorem mem_homS_std {a b : ℕ} {x : HomE E a b} :
    x ∈ homS (stdAt E a P) (stdAt E b P) ↔ ∀ l s, IntAt P (x (Pi.single s 1) l) := by
  refine ⟨fun h l s => mem_stdAt.1 (h _ (single_mem_stdAt s)) l, fun h y hy => mem_stdAt.2 fun l => ?_⟩
  rw [apply_eq_sum]
  exact intAt_sum _ fun j _ => (mem_stdAt.1 hy j).mul (h l j)

theorem standardLattice_restriction_of_freeExtension_mem {n' c' n c : ℕ} {ex' ex : ℕ → ℕ} {xj : HomE E n' n} {t : Loc.FC n' c' n c → E}
    (h : Loc.xx1 xj t ∈ homS (LocE.lamY P (qOf P) n' c' ex') (LocE.lamY P (qOf P) n c ex)) :
    xj ∈ homS (stdAt E n' P) (stdAt E n P) := by
  refine mem_homS_std.2 fun l s => ?_
  have h1 := mem_homS_sclLat.1 h (Fin.castAdd c l) (Fin.castAdd c' s)
  have hs : (Fin.castAdd c' s).1 < n' := s.2
  have hl : (Fin.castAdd c l).1 < n := l.2
  rw [freeCoordinateExtension_apply_single, dif_neg (fun hf => absurd hf.1 (by omega)), dif_pos hs, dif_pos hl] at h1
  simpa [LocE.scE] using h1

theorem chArg_int {n' c' n c : ℕ} {x : HomE E (n' + c') (n + c)}
    (h : x ∈ homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) :
    IntAt P ((qOf P : E) * (-Loc.chArg x)) := by
  rw [mul_neg]
  refine intAt_neg ?_
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with h1
  · by_cases h2 : n' + i + 1 < n' + c'
    · rw [eN_eq h2]
      have h3 := mem_homS_sclLat.1 h ⟨_, h1⟩ ⟨_, h2⟩
      have e : LocE.scE n' (fun i => i + 1) (n' + i + 1) - LocE.scE n (fun i => i + 1) (n + i) = 1 := by
        unfold LocE.scE
        rw [if_neg (by omega), if_neg (by omega)]
        dsimp only
        omega
      rw [e, zpow_one, mul_comm] at h3
      exact h3
    · rw [eN_of_not h2]
      simpa using intAt_zero
  · simpa using intAt_zero

omit [StarRing E] in
theorem chArg_sub_int {n' c' n c : ℕ} {x x' : HomE E (n' + c') (n + c)}
    (h : ∀ l s, IntAt P (x' (Pi.single s 1) l - x (Pi.single s 1) l)) : IntAt P (Loc.chArg x - Loc.chArg x') := by
  rw [← neg_sub]
  refine intAt_neg ?_
  unfold Loc.chArg
  rw [← Finset.sum_sub_distrib]
  refine intAt_sum _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with h1
  · by_cases h2 : n' + i + 1 < n' + c'
    · rw [eN_eq h2]
      exact h _ _
    · rw [eN_of_not h2]
      simpa using intAt_zero
  · simpa using intAt_zero

theorem integrand_congr {n' c' n c : ℕ} {Φ : HomE E (n' + c') (n + c) → K}
    (h : Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) Φ)
    {psi : E → K} (hpsi : ∀ a b, IntAt P ((qOf P : E) * a) → IntAt P b → psi (a + b) = psi a)
    {xj xj' : HomE E n' n} {t t' : Loc.FC n' c' n c → E}
    (hx : ∀ l s, IntAt P ((qOf P : E)⁻¹ * (xj' (Pi.single s 1) l - xj (Pi.single s 1) l))) (ht : ∀ p, IntAt P (t' p - t p)) :
    Φ (Loc.xx1 xj' t') * psi (-Loc.chArg (Loc.xx1 xj' t')) = Φ (Loc.xx1 xj t) * psi (-Loc.chArg (Loc.xx1 xj t)) := by
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  have h1 : (qOf P : E)⁻¹ • (Loc.xx1 xj' t' - Loc.xx1 xj t) ∈
      homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1) := by
    refine mem_homS_sclLat.2 fun l s => ?_
    rw [LinearMap.smul_apply, LinearMap.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, freeCoordinateExtension_apply_single, freeCoordinateExtension_apply_single]
    split_ifs with hf hs hl h4
    · have hl := l.2
      have e : 0 ≤ LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1 - 1 := by
        unfold LocE.scE
        unfold Loc.IsFree at hf
        dsimp only
        split_ifs <;> omega
      convert (ht ⟨(l, s), hf⟩).mul (intAt_zpow e) using 1
      rw [zpow_sub_one₀ hq]
      ring
    · simpa [LocE.scE, hs, hl] using hx _ _
    all_goals simpa using intAt_zero
  have h2 : ∀ l s, IntAt P (Loc.xx1 xj' t' (Pi.single s 1) l - Loc.xx1 xj t (Pi.single s 1) l) := fun l s => by
    rw [freeCoordinateExtension_apply_single, freeCoordinateExtension_apply_single]
    split_ifs with hf hs hl h4
    · exact ht _
    · have := (intAt_nat (qOf P)).mul (hx ⟨l.1, hl⟩ ⟨s.1, hs⟩)
      rwa [mul_inv_cancel_left₀ hq] at this
    all_goals simpa using intAt_zero
  have h3 := h.2.1 (Loc.xx1 xj t) _ h1
  rw [smul_inv_smul₀ hq, add_sub_cancel] at h3
  rw [h3]
  by_cases h0 : Φ (Loc.xx1 xj t) = 0
  · rw [h0, zero_mul, zero_mul]
  · rw [← hpsi _ _ (chArg_int (h.1 _ h0)) (chArg_sub_int h2)]
    congr 2
    ring

theorem unfolding_isGoodCyclotomicInvariant_referenceLattices [CharZero K] {n' c' n c : ℕ} {Φ : HomE E (n' + c') (n + c) → K}
    (h : Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) Φ)
    {psi : E → K} (hpsi : ∀ a b, IntAt P ((qOf P : E) * a) → IntAt P b → psi (a + b) = psi a)
    (hmem : ∀ a, IntAt P ((qOf P : E) * a) → psi a ∈ Zmu K (qOf P)) (A B : ℕ) :
    Good P (homS (stdAt E n' P) (stdAt E n P)) (Loc.E1 psi (LocE.valsQ E (qOf P) A B) (((qOf P : K) ^ B)⁻¹) Φ) := by
  classical
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  have hqK : (qOf P : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.cast_ne_zero.1 hq)
  refine ⟨fun x hx => ?_, fun x z hz => ?_, fun x => ?_⟩
  · obtain ⟨t, -, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hx)
    exact standardLattice_restriction_of_freeExtension_mem (h.1 _ (left_ne_zero_of_mul h0))
  · unfold Loc.E1
    congr 1
    refine Finset.sum_congr rfl fun t _ => integrand_congr h hpsi (fun l s => ?_) fun p => ?_
    · simpa [inv_mul_cancel_left₀ hq] using mem_homS_std.1 hz l s
    · simpa using intAt_zero
  · unfold Loc.E1
    rw [weighted_sum_piFinset (Loc.FC n' c' n c) E K (fun g => ∀ a u, IntAt P u → g (a + (qOf P : E) ^ 0 * u) = g a)
      (LocE.valsQ E (qOf P) A B) (LocE.valsQ E (qOf P) A 0) (((qOf P : K) ^ B)⁻¹) 1 (fun g hg => ?_)
      (fun t => Φ (Loc.xx1 x t) * psi (-Loc.chArg (Loc.xx1 x t))) fun t p a u hu => ?_]
    · rw [one_pow, one_mul]
      refine sum_mem fun t _ => ?_
      by_cases h0 : Φ (Loc.xx1 x t) = 0
      · rw [h0, zero_mul]
        exact zero_mem _
      · exact mul_mem (h.2.2 _) (hmem _ (chArg_int (h.1 _ h0)))
    · rw [sum_valsQ_of_invariant E P K g 0 hg A B (Nat.zero_le B), Nat.sub_zero, inv_mul_cancel_left₀ (pow_ne_zero _ hqK), one_mul]
    · refine integrand_congr h hpsi (fun l s => by simpa using intAt_zero) fun p' => ?_
      by_cases hp : p' = p
      · subst hp
        simpa using hu
      · simpa [hp] using intAt_zero

omit [StarRing E] in

theorem volN_inv_nat {n c : ℕ} {Λ : Submodule (𝓞 E) (Sp E (n + c))} {J : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c))}
    (hJ : J ≤ stabL E _ Λ) {k : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hk : k ∈ stabL E _ Λ) :
    ∃ m : ℕ, (Loc.volN K (Loc.Cbe J k) (Loc.N1 E n c ⊓ stabL E _ Λ))⁻¹ = m := by
  have h : Loc.Cbe J k ⊓ Loc.N1 E n c ≤ Loc.N1 E n c ⊓ stabL E _ Λ := fun r hr => ⟨hr.2, by
    have h1 : k⁻¹ * r * k⁻¹⁻¹ ∈ stabL E _ Λ := hJ hr.1.2
    have h2 := mul_mem (mul_mem hk h1) (inv_mem hk)
    rwa [show k * (k⁻¹ * r * k⁻¹⁻¹) * k⁻¹ = r by group] at h2⟩
  unfold Loc.volN
  rw [Subgroup.relIndex_eq_one.2 h, Nat.cast_one, one_div, inv_inv]
  exact ⟨_, rfl⟩

end Unfold

theorem entryAtG : EntryAtG := by
  intro X Pr R Ch sel S mu cst L G m2 hL i hi al be P hP _
  have hm := hL.hm
  have hal := hL.stabG i al P hP
  have hbe := hL.stabG (i + 1) be P hP
  have hJ : Jat (Pr := Pr) cst.sharp (i + 1) P.1 ≤ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1) := by
    unfold Jat lamYat
    rw [if_pos hP, if_pos hP]
    split_ifs
    · exact inf_le_left
    · exact inf_le_left
  obtain ⟨v, hv⟩ := volN_inv_nat (K := X.K) hJ hbe
  have h1 : R.k ≤ R.N i := Nat.le_add_right _ _
  have h2 : R.k ≤ R.N (i + 1) := Nat.le_add_right _ _
  have h3 : R.r + (i + 1 - 1) * R.t = R.N i + cOf R i := by
    unfold Ranks.r Ranks.N cOf
    rw [hm, Nat.add_sub_cancel, mul_add i]
    omega
  have h4 : R.N i + cOf R i ≤ R.N (i + 1) + cOf R (i + 1) := by
    unfold Ranks.N cOf
    rw [hm, add_mul i]
    omega
  have hom : Good P.1 (homS (LocE.lamY P.1 (qOf P.1) (R.N i) (cOf R i) fun i => i + 1)
      (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1))
      (omPhi Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P)) := by
    unfold lamYat at hal hbe
    rw [if_pos hP] at hal hbe
    refine good_om_two ?_ _ _ _ hal hbe
    unfold PhiAt
    rw [if_pos hP]
    split_ifs
    · exact good_PhiGS _ _ h1 h2 h3 h4
    · exact good_PhiG _ _ h1 h2 h3 h4
  refine (fnModAt_iff _ _ _).2 (Good.const_mul (unfolding_isGoodCyclotomicInvariant_referenceLattices hom (fun a b => psi_add_int hL.cst_ok P)
    (fun a => psi_mem hL.cst_ok P) cst.A cst.B) ?_)
  rw [hv]
  exact natCast_mem _ v

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfPow
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator GlobalTheory.LastSteps

noncomputable section

namespace GlobalTheory.ColPeriod.TopTwist

theorem valuation_le_one_of_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {k : ℕ}
    (hk : k ≠ 0) (h : x ^ k = 1) : w.valuation K x ≤ 1 := by
  by_contra hn
  have h1 := one_lt_pow₀ (not_le.1 hn) hk
  rw [← map_pow, h, map_one] at h1
  exact lt_irrefl _ h1

section Phi

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
theorem qOf_nat_ne_zero : qOf P ≠ 0 := fun h => (qOf_ne_zero (P := P)) (by rw [h, Nat.cast_zero])

omit [StarRing E] in
theorem qOf_pred_ne_zero : qOf P - 1 ≠ 0 := by
  intro h
  have h0 := qOf_nat_ne_zero (P := P)
  have h1 : qOf P = 1 := by omega
  have h2 := qOf_mem (P := P)
  rw [h1, Nat.cast_one] at h2
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

omit [StarRing E] in
theorem valuation_PhiQ [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (q k₀ r c' n' c n : ℕ)
    (x : HomE E (n' + c') (n + c)) : w.valuation K (LocE.PhiQ q ξ k₀ r c' n' c n x) ≤ 1 := by
  unfold LocE.PhiQ LocE.unitV
  split_ifs
  · exact valuation_le_one_of_pow w qOf_pred_ne_zero (char_pow ξ _)
  · simp
  · simp

theorem PhiQ_add (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r c' n' c n : ℕ} (h1 : r ≤ n' + c') (h2 : r ≤ n + c)
    (x z : HomE E (n' + c') (n + c)) (hz : z ∈ homS (LocE.lamY P (qOf P) n' c' 0) (LocE.lamY P (qOf P) n c 0)) :
    LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • z) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  have hZ := entB_int k₀ hz
  unfold LocE.PhiQ
  rw [entB_add_smul]
  generalize LocE.entB (qOf P) k₀ c' n' c n 0 0 z = Z at hZ
  generalize LocE.entB (qOf P) k₀ c' n' c n 0 0 x = M
  have e1 := fun a p p' => intAt_add_q (a := a) (hZ p p')
  have e2 := fun a p p' => intAt_add_q_div (a := a) (hZ p p')
  refine ite_eq_ite_zero (by simp only [e1, e2]) fun h => ?_
  exact unitV_congr _ (redP_det_add_q (fun s s' => h.1 _ _ (by have := s.2; omega) (by have := s'.2; omega)) fun _ _ => hZ _ _)

end Phi

section Psi

variable {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB}

theorem psi_add_int' (hc : c.Ok) (P : SB) {a b : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * a)) (hb : IntAt P.1 b) :
    c.psi P (a + b) = c.psi P a := by
  rw [hc.psi_add P a b ha ((intAt_pow (intAt_nat _) _).mul hb), hc.psi_int P b hb, mul_one]

theorem psi_pow (hc : c.Ok) (P : SB) {a : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * a)) :
    c.psi P a ^ (qOf P.1 ^ c.D P) = 1 := by
  have h : ∀ k : ℕ, c.psi P a ^ k = c.psi P ((k : X.E) * a) := fun k => by
    induction k with
    | zero => rw [pow_zero, Nat.cast_zero, zero_mul, hc.psi_int P 0 intAt_zero]
    | succ k ih =>
      rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, hc.psi_add P _ _ _ ha]
      rw [mul_left_comm]
      exact (intAt_nat _).mul ha
  rw [h, Nat.cast_pow, hc.psi_int P _ ha]

end Psi

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem intAt_arg (P : rowSG Pr sel mu) (hD : 2 * cst.M ≤ cst.D P) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E)
    (h : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single i 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η y)) := by
  have he : IntAt P.1 (epsSg : X.E) := by simpa [epsSg] using intAt_neg intAt_one
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hD
  have h1 := (inDual_iff (((qOf P.1 : X.E) ^ cst.M) • η)).2 h _ hy
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  convert (he.mul (intAt_pow (intAt_nat (qOf P.1)) k)).mul h1 using 1
  rw [hk]
  ring

theorem valuation_ftY (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P)
    (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E) :
    w.valuation X.K (ftY sel mu cst P η y) ≤ 1 := by
  unfold ftY
  rw [if_neg hP]
  split_ifs with h
  · have h2 : w.valuation X.K (algebraMap (𝓞 X.K) X.K (qOf P.1 : 𝓞 X.K)) = 1 :=
      (w.valuation_eq_one_iff_notMem (K := X.K)).2 hw
    rw [map_natCast] at h2
    rw [map_mul, map_inv₀, map_pow, h2, one_pow, inv_one, one_mul]
    exact valuation_le_one_of_pow w (pow_ne_zero _ qOf_nat_ne_zero) (psi_pow hc P (intAt_arg sel mu cst P hD hy η h))
  · simp

theorem ftY_add (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η z : Sp X.E n →ₗ[X.E] X.E) (hz : InDual P.1 z) :
    ftY sel mu cst P (η + ((qOf P.1 : X.E) ^ cst.B) • z) y = ftY sel mu cst P η y := by
  have he : IntAt P.1 (epsSg : X.E) := by simpa [epsSg] using intAt_neg intAt_one
  have hz' := (inDual_iff z).1 hz
  unfold ftY
  simp only [if_neg hP]
  refine ite_eq_ite_zero (forall_congr' fun i => ?_) fun h => ?_
  · rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add]
    exact intAt_add_iff ((intAt_pow (intAt_nat _) _).mul ((intAt_pow (intAt_nat _) _).mul (hz' i)))
  · rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add,
      psi_add_int' hc P (intAt_arg sel mu cst P hD hy η h)]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hc.M_le_B
    have h1 := hz _ hy
    rw [map_smul, smul_eq_mul] at h1
    convert (he.mul (intAt_pow (intAt_nat (qOf P.1)) k)).mul h1 using 1
    rw [hk]
    ring

theorem frsF_mem' {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (x : Sp X.E (R.N j)) : frsF sel mu p P x ∈ localization₂ P.1.asIdeal p.deco.1.N ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  classical
  unfold frsF
  rw [dif_neg hP]
  have h : ∀ Q : QE sel (mu : Chr X.F X.E X.K), p.fr Q x ∈ localization₂ Q.1.asIdeal p.deco.1.N ↔ x ∈ stdAt X.E (R.N j) Q.1 :=
    fun Q => p.2 Q x
  exact h ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩

theorem pow_smul_repY {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N)
    (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) : ((qOf P.1 : X.E) ^ cst.M) • repY Y ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, hY⟩ := hY
  have h0 : repY Y ∈ Y := Classical.epsilon_spec (p := fun y => y ∈ Y) ⟨y, by rw [hY]; simp⟩
  generalize repY Y = y' at h0
  rw [hY] at h0
  have h1 := (mem_locLat _ _ _ _).1 hy P
  have h2 := (mem_locLat _ _ _ _).1 h0 P
  rw [if_neg hP] at h1 h2
  simp only [zpow_neg, inv_inv, zpow_natCast] at h1 h2
  have hq : ((qOf P.1 : X.E) ^ cst.M) ≠ 0 := pow_ne_zero _ qOf_ne_zero
  have hi : IntAt P.1 ((qOf P.1 : X.E) ^ cst.M) := intAt_pow (intAt_nat _) _
  have h3 := smul_mem_locP hi (smul_mem_locP hi h2)
  rw [smul_inv_smul₀ hq] at h3
  have h4 := add_mem h3 h1
  rwa [← smul_add, sub_add_cancel] at h4

end Chain

theorem topAtQ : GlobalTheory.ColPeriod.TopAtQ := by
  intro X Pr R Ch sel S mu cst L G m2 u hPr hsel hS hL P w hP _ hw p d Y hY
  have hc := hL.cst_ok
  have hm := hL.hm
  have hD := hL.depthQ P hP
  have hu := piT_notMem_rowSG sel mu hPr hsel u hS
  have hy : ((qOf P.1 : X.E) ^ cst.M) • (frsF sel mu p P).symm (repY Y) ∈ stdAt X.E _ P.1 := by
    rw [← map_smul, ← frsF_mem' sel mu p P hP, LinearEquiv.apply_symm_apply]
    exact pow_smul_repY sel mu cst hY P hP
  refine ⟨fun x => ?_, fun x z hz => ?_⟩
  · unfold facTop PhiTop
    rw [if_neg hP, map_mul]
    exact mul_le_one' (valuation_PhiQ w _ _ _ _ _ _ _ _ _) (valuation_ftY sel mu cst hc P hP hD w hw hy _)
  · have key : ∀ y ∈ stdAt X.E (R.N (m2 + 1)) P.1,
        (d.1.liftFr P).symm (prXp X.E R (z (frsF sel mu p P y))) ∈ stdAt X.E (R.N R.m - 1) P.1 ∧
          IntAt P.1 (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) (z (frsF sel mu p P y))) := fun y hy => by
      have h := (mem_tilH (N_m_succ R) d (conj_piT_notMem hPr u) hu P.1 _).1
        (hz P.1 (Finset.mem_singleton_self _) _ ((frsF_mem' sel mu p P hP y).2 hy))
      rw [atNL_last, ← (liftFr_spec d.2 P).1, LinearEquiv.apply_symm_apply, inv_mul_eq_div]
      exact ⟨h.1, h.2.div_of_notMem (hu P)⟩
    have h1 : R.r ≤ R.N (m2 + 1) + cOf R (m2 + 1) := by
      unfold Ranks.r Ranks.N cOf
      rw [hm, mul_add (m2 + 1)]
      omega
    have h4 : R.N (m2 + 1) + cOf R (m2 + 1) ≤ R.N R.m - 1 + 0 := by
      unfold Ranks.N cOf
      rw [hm, show m2 + 2 = m2 + 1 + 1 from rfl, add_mul (m2 + 1)]
      omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hc.B_pos
    unfold facTop PhiTop
    rw [if_neg hP]
    congr 1
    · have e : (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ (x + ((qOf P.1 : X.E) ^ cst.B) • z) ∘ₗ
            (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) =
          (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ
            (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) +
          (qOf P.1 : X.E) • ((((qOf P.1 : X.E) ^ k) • ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ z ∘ₗ
            (frsF sel mu p P).toLinearMap)) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
        rw [hk, pow_succ', mul_smul]
        simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc]
      rw [e]
      refine PhiQ_add _ h1 (h1.trans h4) _ _ ?_
      rw [comp_funLeft_mem (cOf_top hm), lamY_zero]
      exact fun y hy => smul_mem_locP (intAt_pow (intAt_nat _) _) (key y hy).1
    · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp ((qOf P.1 : X.E) ^ cst.B), LinearMap.comp_smul]
      exact ftY_add sel mu cst hc P hP hD hy _ _ fun y hy => (key y hy).2

end GlobalTheory.ColPeriod.TopTwist
end
end

