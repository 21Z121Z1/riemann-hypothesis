import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.ConstantCoeffVecConsPairEqZero
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementT
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0083
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInVarEqZero
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.E

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq cob IsLawOfLog lgF UnrOK)
open Formalism.L2.Th1.C (IntMv IntPS IsPt)

namespace CompatibleChartOperations

section Ring

variable {K : Type} [Field K] {σ : Type} {R : Subring K}

theorem intMv_C {a : K} (ha : a ∈ R) : IntMv R (MvPowerSeries.C a : MvPowerSeries σ K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact R.zero_mem

theorem intMv_sum {κ : Type} (s : Finset κ) {F : κ → MvPowerSeries σ K}
    (hF : ∀ k ∈ s, IntMv R (F k)) : IntMv R (∑ k ∈ s, F k) := by
  intro n
  rw [map_sum]
  exact R.sum_mem fun k hk => hF k hk n

theorem isPt_X (s : σ) : IsPt R (MvPowerSeries.X s : MvPowerSeries σ K) :=
  ⟨MvPowerSeries.constantCoeff_X s, Formalism.L2.Th1.C.Pts.intMv_X s⟩

theorem series_at_variable_mul (i : σ) (f g : PowerSeries K) : at1 i (f * g) = at1 i f * at1 i g :=
  PowerSeries.subst_mul (PowerSeries.HasSubst.X i) f g

theorem series_at_variable_neg (i : σ) (f : PowerSeries K) : at1 i (-f) = -at1 i f := by
  unfold at1
  rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X i), map_neg]

theorem constantCoeff_inVar_eq_zero (i : σ) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (at1 i f) = 0 :=
  Formalism.L2.Th1.C.Pts.constantCoeff_subst (MvPowerSeries.constantCoeff_X i) hf

theorem cc_phSum [Fintype σ] {ph : PowerSeries K} (hf : PowerSeries.constantCoeff ph = 0) :
    MvPowerSeries.constantCoeff (phSum ph : MvPowerSeries σ K) = 0 := by
  unfold phSum
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => constantCoeff_inVar_eq_zero i hf

theorem intMv_thetaProd {κ : Type} [Fintype κ] [Fintype σ] {r : κ → K} {V : κ → σ → PowerSeries K}
    (hr : ∀ k, r k ∈ R) (hV : ∀ k i, IntPS R (V k i)) : IntMv R (thetaProd r V) :=
  intMv_sum _ fun k _ => Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_mul (intMv_C (hr k))
    (Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_prod _ fun i _ => Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_subst (hV k i) (isPt_X i))

theorem subst_phSum {τ : Type} [Fintype σ] (ph : PowerSeries K) {φ : σ → MvPowerSeries τ K}
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    MvPowerSeries.subst φ (phSum ph) = ∑ i, PowerSeries.subst (φ i) ph := by
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ
  unfold phSum
  rw [← MvPowerSeries.coe_substAlgHom h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPowerSeries.coe_substAlgHom h]
  unfold at1
  rw [Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X i) hφ, MvPowerSeries.subst_X h]

end Ring

section Normed

variable {K : Type} [NormedField K] {σ : Type}

theorem integral_iff {R : Subring K} (hR : ∀ a, a ∈ R ↔ ‖a‖ ≤ 1) (f : MvPowerSeries σ K) :
    Integral f ↔ IntMv R f := forall_congr' fun _ => (hR _).symm

theorem intS_iff {R : Subring K} (hR : ∀ a, a ∈ R ↔ ‖a‖ ≤ 1) (f : PowerSeries K) :
    IntS f ↔ IntPS R f := forall_congr' fun _ => (hR _).symm

theorem mem_ball [IsUltrametricDist K] (a : K) : a ∈ Formalism.G.unitBall K ↔ ‖a‖ ≤ 1 := Iff.rfl

theorem mvExp_eq [CharZero K] (f : MvPowerSeries σ K) : mvExp f = Formalism.L2.Th1.C.mvExp f := rfl

end Normed

end CompatibleChartOperations

open CompatibleChartOperations

theorem product_integral : ProdInt := by
  intro K _ _ _ κ n _ _ ph r V hph hr hV
  refine ⟨?_, (integral_iff mem_ball _).2 (intMv_thetaProd (fun k => (mem_ball _).2 (hr k))
    fun k i => (intS_iff mem_ball _).1 (hV k i))⟩
  have hnph : PowerSeries.constantCoeff (-ph) = 0 := by rw [map_neg, hph, neg_zero]
  have hE : ∀ i : n, at1 i (mvExp (-ph) : PowerSeries K) = mvExp (-(at1 i ph)) := by
    intro i
    rw [← series_at_variable_neg]
    exact Formalism.L2.Th1.C.subst_mvExp hnph (MvPowerSeries.constantCoeff_X i)
  have hS : mvExp (-(phSum ph : MvPowerSeries n K)) = ∏ i : n, mvExp (-(at1 i ph)) := by
    unfold phSum
    rw [← Finset.sum_neg_distrib]
    exact Formalism.L2.Th1.C.mvExp_sum _ _ fun i _ => by rw [map_neg, constantCoeff_inVar_eq_zero i hph, neg_zero]
  unfold thetaProd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hS, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [series_at_variable_mul, hE]

theorem subst_exp_integral : SubstExpInt := by
  intro K _ _ _ n m _ φ hφ0 hφ Φ U hΦ hU
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have hnΦ : MvPowerSeries.constantCoeff (-Φ) = 0 := by rw [map_neg, hΦ, neg_zero]
  refine ⟨?_, ?_, MvPowerSeries.constantCoeff_subst_eq_zero h hφ0 hΦ⟩
  · have hneg : MvPowerSeries.subst φ (-Φ) = -MvPowerSeries.subst φ Φ := by
      rw [← MvPowerSeries.coe_substAlgHom h, map_neg]
    rw [MvPowerSeries.subst_mul h, ← hneg]
    congr 1
    exact Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp hnΦ hφ0
  · exact (integral_iff mem_ball _).2 (Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_substMv ((integral_iff mem_ball _).1 hU)
      fun i => ⟨hφ0 i, (integral_iff mem_ball _).1 (hφ i)⟩)

theorem congruence_iff_simeq : CongIffSimeq := by
  intro K _ _ _ R hR σ f g
  exact and_congr Iff.rfl (integral_iff hR _).symm

theorem IntHyp_of (hP : ProdInt) (hS : SubstExpInt) (hC : CongIffSimeq)
    (hH : Formalism.L2.Th1.C.HyperbolicSum) (_hPt : Formalism.L2.Th1.C.PtClosure) : IntHyp := by
  intro K _ _ _ R hR l linv ph hFr O _ _ τ hEnd hBin hF1 hN hA n ι _ _ _ f f' hff hff' hd κ _ r V hr hV
  obtain ⟨hlp, hFG, hph⟩ := hFr
  have hpt : ∀ i, IsPt R (hypCoord l linv τ f f' i) := fun i =>
    Formalism.L2.Th1.C.Pts.isPt_flin hlp hFG (by rintro (e | e) <;> exact hEnd _)
      (by rintro (e | e) <;> exact isPt_X _)
  obtain ⟨h1, h2⟩ := hP K κ n ph r V hph hr hV
  obtain ⟨h3, h4, h5⟩ := hS K n (Bool × ι) (hypCoord l linv τ f f') (fun i => (hpt i).1)
    (fun i => (integral_iff hR _).2 (hpt i).2) (phSum ph) (thetaProd r V) (cc_phSum hph) h2
  refine ⟨_, _, h4, h5, (hC K R hR _ _ _).1 ?_, by rw [h1, h3]⟩
  rw [subst_phSum ph fun i => (hpt i).1]
  exact hH K R l linv ph ⟨hlp, hFG, hph⟩ O τ hEnd hBin hF1 hN hA n ι f f' hff hff' hd (Bool × ι)
    (fun e => MvPowerSeries.X (false, e)) (fun e => MvPowerSeries.X (true, e))
    (fun e => isPt_X _) (fun e => isPt_X _)

theorem sum_series_analytic : SumEBridge := by
  intro K _ _ l linv hlp F hF hc ph ι _ N0 N1
  rw [Formalism.L2.Th1.C.Dict.law_eq hlp hF hc]
  unfold Formalism.L2.Th1.D.sumE beSum
  refine Finset.sum_congr rfl fun e => fun _ => ?_
  rw [← Formalism.L2.Th1.C.Dict.subst_cob hlp ph (MvPowerSeries.constantCoeff_X (false, e))
    (MvPowerSeries.constantCoeff_X (true, e))]
  congr 1
  funext a
  fin_cases a <;> rfl

theorem map_coboundary : MapCob := by
  intro K0 K _ _ j F f hF
  exact Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_cob j F hF f

theorem IntThetaZ_of (hB0 : Formalism.L2.Th1.D.B0) (hI : IntHyp) (hS : SumEBridge) (hM : MapCob) :
    IntThetaZ := by
  intro K0 K _ _ _ _ _ _ l d N0 N1 _ σ j hU hj hd2 hev F hF ph0 hph0 hF1 hF2 ι _ _ om oms hOw hTr ζ hζ
    R hR hFr O _ _ τ hEnd hBin hCF1 hN hA n _ f f' hff hff' hdual κ _ r V hr hV
  obtain ⟨U0, Φ, hU0, hΦ0, hΦ, hEq⟩ := hI K R hR (lgF K l) (Formalism.L2.Th1.D.expF K l)
    (PowerSeries.map j ph0) hFr O τ hEnd hBin hCF1 hN hA n (ι × Fin N0 × Fin N1) f f' hff hff' hdual
    κ r V hr hV
  have hFj0 : MvPowerSeries.constantCoeff (MvPowerSeries.map j F) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hF.1, map_zero]
  have hcob : cob (MvPowerSeries.map j F) (lgF K l) = 0 := by
    rw [← Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF j l, ← hM K0 K j F (lgF K0 l) hF.1, hF.2.2, map_zero]
  have hb : beSum (lgF K l) (Formalism.L2.Th1.D.expF K l) (PowerSeries.map j ph0) =
      (Formalism.L2.Th1.D.sumE (MvPowerSeries.map j (cob F ph0)) :
        MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K) := by
    rw [hM K0 K j F ph0 hF.1]
    exact (hS K (lgF K l) (Formalism.L2.Th1.D.expF K l) hFr.1 (MvPowerSeries.map j F) hFj0 hcob
      (PowerSeries.map j ph0) ι N0 N1).symm
  rw [hb] at hΦ
  obtain ⟨U, hUi, hg⟩ := hB0 K0 K l d N0 N1 σ j hU hj hd2 hev F hF (cob F ph0) hF1 hF2 ι om oms hOw hTr
    ζ hζ U0 Φ hU0 hΦ0 hΦ
  exact ⟨U, hUi, fun g h1 h2 => by rw [hEq]; exact hg g h1 h2⟩

end Formalism.L2.Th1.E
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInvTDen
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace Shape

def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {a | ‖a‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    change ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem mem_ball {K : Type} [NormedField K] [IsUltrametricDist K] {a : K} :
    a ∈ ball K ↔ ‖a‖ ≤ 1 := Iff.rfl

section Alg

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)

end Alg

section Pts

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

theorem px_neg (Q : W.toAffine.Point) : px W (-Q) = px W Q := by
  cases Q <;> rfl

end Pts

section Nrm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

end Nrm

end Shape

open Shape

theorem XTShape_holds : XTShape := UpperTheory.Reformulated.B.SeriesSubgroup.XTShape_holds

theorem FacShape_of (hR : IntRules) (hA : UnitAtRules) (hK : UnitKap) (hP : UnitPsi2)
    (hD : UnitDiff) (hX : XTShape) : FacShape := by
  intro K _ _ _ W hW P Q hP0 hQ0 hPx hPy hQx hQy hs hd
  obtain ⟨hI, hc0, hc1, hc2⟩ := hX K W hW P hP0 hPx hPy
  obtain ⟨rC, -, rAdd, rNeg, -⟩ := hR K
  obtain ⟨-, -, rU, -⟩ := hA K
  have hf : IntS (C (px W Q) - xT W P) := by
    rw [sub_eq_add_neg]; exact rAdd _ _ (rC _ hQx) (rNeg _ hI)
  have e0 : coeff 0 (C (px W Q) - xT W P) = px W Q - px W P := by
    rw [map_sub, hc0, coeff_zero_C]
  have e1 : coeff 1 (C (px W Q) - xT W P) = -psi2 W P := by
    rw [map_sub, hc1, coeff_C]; simp
  have hxeq : (P + Q = 0 ∨ P - Q = 0) → px W Q = px W P := by
    rintro (h | h)
    · rw [eq_neg_of_add_eq_zero_left h, px_neg]
    · rw [sub_eq_zero.mp h]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · refine rU 0 _ hf (fun i hi => absurd hi (Nat.not_lt_zero i)) ?_
    rw [e0, norm_sub_rev]
    exact hD K W hW P Q hP0 hQ0 h1 h2 hPx hPy hQx hQy (hs h1) (hd h2)
  · refine rU 1 _ hf (fun i hi => ?_) ?_
    · obtain rfl : i = 0 := by omega
      rw [e0, hxeq h1, sub_self]
    · rw [e1, norm_neg]
      rcases h1 with h | h
      · have hPQ : P = -Q := eq_neg_of_add_eq_zero_left h
        have hPP : P + P = P - Q := by rw [hPQ, sub_eq_add_neg]
        have hne : P + P ≠ 0 := by
          rw [hPQ, ← neg_add]; exact neg_ne_zero.mpr h2
        refine hP K W hW P hP0 hne hPx hPy ?_
        rw [hPP]; exact hd (hPP ▸ hne)
      · have hPQ : P = Q := sub_eq_zero.mp h
        have hne : P + Q ≠ 0 := by rw [hPQ]; exact h2
        have hne' : P + P ≠ 0 := by rw [hPQ]; exact h2
        refine hP K W hW P hP0 hne' hPx hPy ?_
        have := hs hne
        rwa [← hPQ] at this
  · have hPQ : P = Q := sub_eq_zero.mp h1
    obtain ⟨k0, k1⟩ := hK K W hW P hP0 (by rw [hPQ]; exact h2) hPx hPy
    refine rU 2 _ hf (fun i hi => ?_) ?_
    · have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl
      · rw [e0, hPQ, sub_self]
      · rw [e1, k0, neg_zero]
    · rw [map_sub, hc2 k0, coeff_C]
      simpa using k1

end Formalism.L2.Th1.E
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.OpUTh0RootOf
section
open scoped ComplexConjugate

namespace Formalism.L2.Th1.E

namespace OperatorUThetaLemmas

open Formalism.L2.Th1.F

theorem opU_const_mul (L : PeriodPair) (x a : ℂ) (f : ℂ → ℂ) :
    opU L x (fun z => a * f z) = fun z => a * opU L x f z := by
  funext z
  simp only [opU]
  ring

theorem altE_nat_mul (L : PeriodPair) (N : ℕ) (x y : ℂ) :
    altE L ((N : ℂ) * x) ((N : ℂ) * y) = (N : ℝ) ^ 2 * altE L x y := by
  have h : herm L ((N : ℂ) * x) ((N : ℂ) * y) = (((N : ℝ) ^ 2 : ℝ) : ℂ) * herm L x y := by
    simp only [herm, map_mul, Complex.conj_natCast]
    push_cast
    ring
  simp only [altE, h, Complex.im_ofReal_mul]

theorem exp_altE_pow (L : PeriodPair) (N : ℕ) (x y : ℂ)
    (hx : (N : ℂ) * x ∈ L.lattice) (hy : (N : ℂ) * y ∈ L.lattice) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L x y : ℂ)) ^ (2 * N ^ 2) = 1 := by
  obtain ⟨k, hk⟩ := altEInt L _ _ hx hy
  rw [altE_nat_mul] at hk
  have hk' : ((N : ℂ)) ^ 2 * (altE L x y : ℂ) = (k : ℂ) := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hk
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨-k, ?_⟩
  push_cast
  rw [← hk']
  ring

end OperatorUThetaLemmas

open Formalism.L2.Th1.F in
theorem OpUTh0Root_of : OpUTh0Root := by
  intro L t t₀ N hN ht ht₀ _
  refine ⟨Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L t t₀ : ℂ)), 2 * N ^ 2, by positivity,
    OperatorUThetaLemmas.exp_altE_pow L N t t₀ ht ht₀, ?_⟩
  have h0 : th0 L t₀ = fun z => (opU L t₀ (sgStar L) 0)⁻¹ * opU L t₀ (sgStar L) z := by
    funext z
    simp only [th0]
    rw [div_eq_mul_inv, mul_comm]
  rw [h0, OperatorUThetaLemmas.opU_const_mul]
  funext z
  rw [opUMul L t t₀ (sgStar L) z]
  ring

end Formalism.L2.Th1.E
end

