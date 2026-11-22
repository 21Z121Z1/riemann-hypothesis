import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaUnitFunctionShortModelIntegral
section
noncomputable section

namespace GlobalTheory.ShortModelTheta

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso epOf)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.L2.KerInert.BeCob (eLT vLT ThetaTie ShortIso)
open GlobalTheory.CurveDictionary (cc_lgF' lgF_eq_logF)

section IntPS

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem integral_ps' {K : Type} [NormedField K] {f : PowerSeries K}
    (h : ∀ k, ‖PowerSeries.coeff k f‖ ≤ 1) : Integral (f : MvPowerSeries Unit K) := by
  intro n
  have e : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by rcases u with ⟨⟩; simp
  rw [e]
  exact h (n ())

theorem ips' {f : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K)) (k : ℕ) :
    ‖PowerSeries.coeff k f‖ ≤ 1 := hf _

theorem ips_add' {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f + g : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ips' hf k) (ips' hg k))

theorem ips_sub' {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f - g : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [map_sub, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ips' hf k) (by rw [norm_neg]; exact ips' hg k))

theorem ips_Cmul' {c : K} (hc : ‖c‖ ≤ 1) {f : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K)) :
    Integral ((PowerSeries.C c * f : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [PowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (ips' hf k)

theorem ips_X' : Integral ((PowerSeries.X : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [PowerSeries.coeff_X]
  split_ifs <;> simp

theorem ips_mul' {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f * g : PowerSeries K) : MvPowerSeries Unit K) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hf hg

end IntPS

theorem shortIso_holds : ShortIso := by
  intro K _ _ _ h2 h3 W hW
  obtain ⟨hxI, hx1, hA, -⟩ := Formalism.L2.Th1.A.bridgeCurve K W hW
  obtain ⟨hB, -⟩ := Formalism.L2.Th1.A.bridgeCurve3 K W hW
  obtain ⟨hnum, hden⟩ := Formalism.L2.Th1.A.wpNumEq K W
  rw [← Formalism.L2.Th1.A.uSerEq K _ _]
  obtain ⟨hl0, hl1, -, -⟩ := Formalism.L2.Th1.A.logSpec K W
  have hlS : PowerSeries.HasSubst (Formalism.L2.Th1.A.logSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have hl_ne : Formalism.L2.Th1.A.logSer W ≠ 0 := by
    intro h; rw [h, map_zero] at hl1; exact zero_ne_one hl1
  set lW := Formalism.L2.Th1.A.logSer W with hlW
  set P := Formalism.L2.Th1.A.wpReg W with hP
  set xs := Formalism.L2.Th1.A.xS W with hxs
  set N : PowerSeries K := xs + PowerSeries.C (W.b₂ / 12) * PowerSeries.X ^ 2 with hN
  set D : PowerSeries K := xs - PowerSeries.C (W.a₁ / 2) * PowerSeries.X * xs -
    PowerSeries.C (W.a₃ / 2) * PowerSeries.X ^ 3 with hD
  have hD1 : PowerSeries.constantCoeff D = 1 := by
    rw [hD]; simp [hx1]
  have hden1 : PowerSeries.constantCoeff (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) ≠ 0 := by
    rw [hden]; simp
  have hsn : PowerSeries.subst lW (Formalism.L2.Th1.CM.wpNum (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      1 + lW ^ 2 * PowerSeries.subst lW P := by
    rw [hnum, PowerSeries.subst_add hlS, PowerSeries.subst_mul hlS, PowerSeries.subst_pow hlS,
      PowerSeries.subst_X hlS, ← PowerSeries.coe_substAlgHom hlS, map_one]
  have hsd : PowerSeries.subst lW (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      1 - PowerSeries.C (1 / 2 : K) * lW ^ 3 * PowerSeries.subst lW (PowerSeries.derivative K P) := by
    rw [hden, PowerSeries.subst_sub hlS, PowerSeries.subst_mul hlS, PowerSeries.subst_mul hlS,
      PowerSeries.subst_pow hlS, PowerSeries.subst_X hlS, PowerSeries.subst_C, ← PowerSeries.coe_substAlgHom hlS,
      map_one]
    rfl
  set I := PowerSeries.subst lW (Formalism.L2.Th1.CM.uSer (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) with hI
  have hIB : I * PowerSeries.subst lW (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      lW * PowerSeries.subst lW (Formalism.L2.Th1.CM.wpNum (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) := by
    rw [hI, ← PowerSeries.subst_mul hlS]
    unfold Formalism.L2.Th1.CM.uSer
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hden1, mul_one, PowerSeries.subst_mul hlS, PowerSeries.subst_X hlS]
  rw [hsn, hsd] at hIB
  have hID : I * D = PowerSeries.X * N := by
    have h3ne : lW ^ 3 ≠ 0 := pow_ne_zero 3 hl_ne
    apply mul_left_cancel₀ h3ne
    have e2 : (2 : K) ≠ 0 := two_ne_zero
    have hB' : PowerSeries.X ^ 3 * (1 - PowerSeries.C (1 / 2 : K) * lW ^ 3 * PowerSeries.subst lW (PowerSeries.derivative K P)) =
        lW ^ 3 * D := by
      have hh : (PowerSeries.C (1 / 2 : K) : PowerSeries K) * (2 : PowerSeries K) = 1 := by
        rw [show (2 : PowerSeries K) = PowerSeries.C (2 : K) from (map_ofNat _ 2).symm, ← map_mul]; norm_num
      rw [hD]
      have ha1 : (PowerSeries.C (W.a₁ / 2) : PowerSeries K) = PowerSeries.C (1 / 2 : K) * PowerSeries.C W.a₁ := by
        rw [← map_mul]; ring_nf
      have ha3 : (PowerSeries.C (W.a₃ / 2) : PowerSeries K) = PowerSeries.C (1 / 2 : K) * PowerSeries.C W.a₃ := by
        rw [← map_mul]; ring_nf
      rw [ha1, ha3]
      linear_combination (-(PowerSeries.C (1 / 2 : K) : PowerSeries K)) * hB -
        (PowerSeries.X ^ 3 - lW ^ 3 * xs) * hh
    linear_combination PowerSeries.X ^ 3 * hIB - I * hB' + lW * PowerSeries.X * hA
  have hDinv : D⁻¹ * D = 1 := PowerSeries.inv_mul_cancel _ (by rw [hD1]; exact one_ne_zero)
  have hIe : I = PowerSeries.X * N * D⁻¹ := by
    calc I = I * D * D⁻¹ := by rw [mul_assoc, mul_comm D, hDinv, mul_one]
      _ = _ := by rw [hID]
  rw [hIe]
  have h12 : ‖(12 : K)‖ = 1 := by
    rw [show (12 : K) = 2 * 2 * 3 by norm_num, norm_mul, norm_mul, h2, h3]; norm_num
  have hi1 : ‖W.a₁‖ ≤ 1 := hW.1
  have hi2 : ‖W.a₂‖ ≤ 1 := hW.2.1
  have hi3 : ‖W.a₃‖ ≤ 1 := hW.2.2.1
  have hb2 : ‖W.b₂ / 12‖ ≤ 1 := by
    rw [norm_div, h12, div_one, WeierstrassCurve.b₂]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hi1
    · rw [norm_mul]
      refine mul_le_one₀ ?_ (norm_nonneg _) hi2
      rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]; norm_num
  have ha12 : ‖W.a₁ / 2‖ ≤ 1 := by rw [norm_div, h2, div_one]; exact hi1
  have ha32 : ‖W.a₃ / 2‖ ≤ 1 := by rw [norm_div, h2, div_one]; exact hi3
  have hX2 : Integral (((PowerSeries.X : PowerSeries K) ^ 2 : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [pow_two]; exact ips_mul' ips_X' ips_X'
  have hX3 : Integral (((PowerSeries.X : PowerSeries K) ^ 3 : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [pow_succ]; exact ips_mul' hX2 ips_X'
  have hNI : Integral ((N : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [hN]; exact ips_add' hxI (ips_Cmul' hb2 hX2)
  have hDI : Integral ((D : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [hD]
    exact ips_sub' (ips_sub' hxI (ips_mul' (ips_Cmul' ha12 ips_X') hxI)) (ips_Cmul' ha32 hX3)
  have hDiI : Integral ((D⁻¹ : PowerSeries K) : MvPowerSeries Unit K) :=
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_of_mul_eq_one hDI hD1 hDinv
  exact ips_mul' (ips_mul' ips_X' hNI) hDiI

theorem exists_witt_series_inverse_formalGroup_iso_short {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

theorem v_integral' {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) (n : ℕ) :
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso_short hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

theorem norm_nat_one' {l : ℕ} [Fact l.Prime] (h5 : 5 ≤ l) (m : ℕ) (hm1 : 0 < m) (hm : m < 5) :
    ‖(m : ℂ_[l])‖ = 1 := by
  have hp : l.Prime := Fact.out
  refine Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one l) ?_
  intro h
  have := Nat.le_of_dvd hm1 h
  omega

theorem thetaTie_holds : ThetaTie := by
  intro l _ h5 g hLT hOk n
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hvcc : PowerSeries.constantCoeff (vLT hLT) = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hvS : PowerSeries.HasSubst (vLT hLT) := PowerSeries.HasSubst.of_constantCoeff_zero' hvcc
  have hgl : g.l = Formalism.L2.Th1.A.logSer g.W := Formalism.L2.KerInert.Dict.formal_logarithm_agree l g.W g.wq hOk.2.1
  have hlW0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer g.W) = 0 := by rw [← hgl]; exact Formalism.MainNotions.J.cc_l g
  have hvl : PowerSeries.subst (vLT hLT) (Formalism.L2.Th1.A.logSer g.W) = PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l := by
    rw [← hgl]; exact Formalism.L2.G.Pend.lg_pt g hex hinv hv0
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_nat_one' h5 2 (by norm_num) (by norm_num)
  have h3 : ‖(3 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_nat_one' h5 3 (by norm_num) (by norm_num)
  have hiso := shortIso_holds ℂ_[l] h2 h3 g.W (Formalism.L2.KerInert.Dict.intModel_of_ok hOk)
  have hθ : thetaS l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) (eLT hLT)⁻¹ =
      MvPowerSeries.subst (fun _ => vLT hLT) (PowerSeries.subst (Formalism.L2.Th1.A.logSer g.W)
        (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W)))) := by
    unfold thetaS
    rw [Formalism.L2.Th1.A.uSerEq ℂ_[l] _ _, ← PowerSeries.subst_def,
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlW0) hvS, hvl]
  rw [hθ]
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun _ => hvcc) (fun _ => integral_ps' (v_integral' hOk hLT)) hiso
    (Finsupp.single () n)

end GlobalTheory.ShortModelTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.SplitMatch

open Formalism.L2.NTheta

variable {D : D7}

theorem exists_isIdemAt {P : Pl D.host.E} (hP : conjPl P ≠ P) : ∃ e : AE D, IsIdemAt e P := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  rcases h with ⟨h, -⟩ | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exact ⟨e, h⟩
  · refine absurd (GlobalTheory.IdemSupport.eq_of_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)) hP
    have h2 := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at h2
    by_cases h0 : x = 0
    · rw [h0]; exact zero_mem _
    · exact (h2 x h0).2 ((ht x h0).1 hx)

theorem idem_unique {P : Pl D.host.E} {e e' f' : AE D} (he : IsIdemAt e P) (h : IsPrimeIdem P e' f') :
    e' = e ∧ f' = e + cA D e := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨hd, ε, hε, h1⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ (f := e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨hd', ε', hε', h1'⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  exact ⟨GlobalTheory.IdemSupport.delta_unique hΦ hd' hd, by rw [h1, h1', GlobalTheory.IdemSupport.placeIdem_unique hε' hε]⟩

theorem mem_hyp {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {V : HSp D} {k : GA D V} (hk : k ∈ hyp V P) :
    k ∈ locPart V (KsphC V ∅) e := by
  obtain ⟨h1, e', f', h2, h3⟩ := hk
  rw [(idem_unique he h2).2] at h3
  exact ⟨h1, h3⟩

theorem one_mem_hyp {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) (V : HSp D) : (1 : GA D V) ∈ hyp V P := by
  refine ⟨⟨one_mem _, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, e + cA D e,
    Or.inl ⟨he, rfl⟩, GlobalTheory.SplitHecke.suppAt_one V⟩
  rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]

theorem unr {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {χ : (AE D)ˣ →* Circle} (hχ : UnrPl P χ)
    (y : (AE D)ˣ) (h : (1 - e) * (y : AE D) = 1 - e) (h1 : finPart D (e * (y : AE D)) ∈ intAE D)
    (h2 : finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D) : χ y = 1 := by
  have h' : (1 - e) * ((y⁻¹ : (AE D)ˣ) : AE D) = 1 - e := by
    conv_lhs => rw [← h, mul_assoc, Units.mul_inv, mul_one]
  have e0 : finPart D e ∈ intAE D := by
    by_contra hc
    have := (he.2 1 one_ne_zero).2 (by
      rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one])
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have key : ∀ z : AE D, (1 - e) * z = 1 - e → finPart D (e * z) ∈ intAE D → finPart D z ∈ intAE D := fun z a b => by
    have : z = e * z + 1 - e := by linear_combination a
    rw [this, RingHom.map_sub, RingHom.map_add, RingHom.map_one]
    exact sub_mem (add_mem b (GlobalTheory.SplitDivisors.one_mem_int D)) e0
  refine hχ e _ (Or.inl ⟨he, rfl⟩) y ?_ (key _ h h1) (key _ h' h2)
  linear_combination (cA D e - 1) * h + ((y : AE D) - 1) * he.1.2.1

theorem sphOp_of {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal)
    (h2 : ϖ ∉ P.asIdeal ^ 2) {V : HSp D} {d : List ℤ} (hd : d.Pairwise fun a b => b ≤ a) {α : GA D V}
    (hα : SuppAt e V α) (hD : DivAt V e (ϖ : D.host.E) d α) {R : Finset (GA D V)} (hR : ∀ γ ∈ R, SuppAt e V γ)
    (hc : IsCosetRep V (locPart V (KsphC V ∅) e) α R) : SphOp V P d R :=
  ⟨e, e + cA D e, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), Or.inl ⟨he, rfl⟩, h1, h2, hd,
    fun _ _ => Iff.rfl, fun _ _ _ => rfl, hα, hD, hR, hc⟩

theorem splitLab_pairwise (n k : ℕ) : (splitLab n k).Pairwise fun a b => b ≤ a := by
  simp [splitLab, List.pairwise_append, List.pairwise_replicate]

theorem dual_splitLab_pairwise (n k : ℕ) : (dualLab (splitLab n k)).Pairwise fun a b => b ≤ a := by
  simp [dualLab, splitLab, List.pairwise_append, List.pairwise_replicate]

theorem exists_data {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal)
    (h2 : ϖ ∉ P.asIdeal ^ 2) (V : HSp D) : ∃ (α : ℕ → GA D V) (R R' : ℕ → Finset (GA D V)),
      (∀ j, j ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) j (α j) ∧ (∀ γ ∈ R j, SuppAt e V γ) ∧
        IsCosetRep V (locPart V (KsphC V ∅) e) (α j) (R j)) ∧
      (∀ j, j ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) j (α j) ∧ (∀ γ ∈ R' j, SuppAt e V γ) ∧
        IsCosetRep V (locPart V (KsphC V ∅) e) (α j)⁻¹ (R' j)) ∧
      (∀ j, j ≤ V.rank → SphOp V P (dualLab (splitLab V.rank j)) (R j)) ∧
      ∀ j, j ≤ V.rank → SphOp V P (splitLab V.rank j) (R' j) := by
  obtain ⟨-, hrep, hH⟩ := GlobalTheory.SplitPlace.split_local V P e he
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]; exact zero_mem _)
  choose! α hα using (hH ϖ h1 h2).1
  choose! ρ hρ using hrep
  have hD := fun j hj => GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt V P e ϖ j (α j) he h1 h2 hj (hα j hj)
  have s := fun j hj => (hα j hj).2.1
  have s' := fun j hj => GlobalTheory.SplitHecke.suppAt_inv (s j hj)
  refine ⟨α, fun j => ρ (α j), fun j => ρ (α j)⁻¹, fun j hj => ⟨hα j hj, hρ _ (s j hj)⟩,
    fun j hj => ⟨hα j hj, hρ _ (s' j hj)⟩, fun j hj => ?_, fun j hj => ?_⟩
  · refine sphOp_of he h1 h2 (dual_splitLab_pairwise _ _) (s j hj) ?_ (hρ _ (s j hj)).1 (hρ _ (s j hj)).2
    have := (GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul V e _ _ _ he.1.1 h0 (hD j hj)).1
    rwa [inv_inv] at this
  · exact sphOp_of he h1 h2 (splitLab_pairwise _ _) (s' j hj) (hD j hj) (hρ _ (s' j hj)).1 (hρ _ (s' j hj)).2

section

variable {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)

theorem opOf_single (d : List ℤ) (z : ℂ) : opOf π P (Finsupp.single d z) = z • ∑ γ ∈ rep V P d, π γ := by
  unfold opOf
  exact Finsupp.sum_single_index (zero_smul _ _)

theorem opOf_sum (s : Finset ℕ) (d : ℕ → List ℤ) (z : ℕ → ℂ) :
    opOf π P (∑ j ∈ s, Finsupp.single (d j) (z j)) = ∑ j ∈ s, z j • opOf π P (Finsupp.single (d j) 1) := by
  simp only [opOf_single, one_smul]
  unfold opOf
  rw [← Finsupp.sum_finsetSum_index (by simp) (by simp [add_smul])]
  exact Finset.sum_congr rfl fun j _ => Finsupp.sum_single_index (zero_smul _ _)

theorem opOf_trunc (n k : ℕ) (d : ℕ → List ℤ) (z : ℕ → ℂ) (u : M) :
    opOf π P (∑ j ∈ Finset.range (n + 1), Finsupp.single (d j) (if j ≤ k then z j else 0)) u =
      ∑ j ∈ Finset.range (min k n + 1), z j • opOf π P (Finsupp.single (d j) 1) u := by
  rw [opOf_sum, LinearMap.sum_apply]
  symm
  refine (Finset.sum_congr rfl fun j hj => ?_).trans
    (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j hj hj' => ?_)
  · rw [Finset.mem_range] at hj
    rw [if_pos (by omega), LinearMap.smul_apply]
  · rw [Finset.mem_range] at hj hj'
    rw [if_neg (by omega), zero_smul, LinearMap.zero_apply]

end

theorem dualC_splitC (n : ℕ) (z : ℕ → ℂ) :
    dualC (splitC n z) = ∑ j ∈ Finset.range (n + 1), Finsupp.single (dualLab (splitLab n j)) (z j) := by
  unfold dualC splitC
  rw [Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]

set_option maxHeartbeats 1000000 in

theorem match_split : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → conjPl P ≠ P → UnrPl P χS → UnrPl P χT → VacFix ψ om P ∧ ∀ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ) (t : ℕ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → (T.rank = S.rank + t → ∀ k, k ≤ T.rank → Match ψ om P (dualC (splitC S.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank)⁻¹ ^ k * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank) ^ j else 0)) (Finsupp.single (splitLab T.rank k) 1)) ∧ (S.rank = T.rank + t → ∀ k, k ≤ S.rank → Match ψ om P (dualC (Finsupp.single (splitLab S.rank k) 1)) (splitC T.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((T.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank)⁻¹ ^ k * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank) ^ j else 0)) := by
  intro D ψ S T χS χT om P hW hP hS hT
  have main : ∀ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ) (t : ℕ) (he : IsIdemAt e P) (h1 : ϖ ∈ P.asIdeal)
      (h2 : ϖ ∉ P.asIdeal ^ 2) (hx : (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e)) f (hf : IsVacAt ψ S T P f)
      αS αT RS RT a b, _ := fun e ϖ x t he h1 h2 hx f hf αS αT RS RT a b =>
    GlobalTheory.SplitHecke.hecke_identity_split ψ S T χS χT om P e ϖ x f αS αT RS RT t hW he h1 h2 hx
      (fun y a b c => ⟨unr he hS y a b c, unr he hT y a b c⟩) hf.1 (hf.2 e _ (Or.inl ⟨he, rfl⟩)) a b
  have fix : VacFix ψ om P := by
    intro f hf k hk k' hk'
    obtain ⟨e, he⟩ := exists_isIdemAt hP
    obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt
      (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
    have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
      rw [show ϖ = 0 from Subtype.ext h]; exact zero_mem _)
    have hi : incA D (ϖ : D.host.E) * incA D (ϖ : D.host.E)⁻¹ = 1 := by
      rw [← RingHom.map_mul, mul_inv_cancel₀ h0, RingHom.map_one]
    obtain ⟨αS, RS, -, a, -, -, -⟩ := exists_data he h1 h2 S
    obtain ⟨αT, -, RT, -, b, -, -⟩ := exists_data he h1 h2 T
    exact (main e ϖ (Units.mkOfMulEqOne _ _ (GlobalTheory.SplitHecke.idem_mul_inv he.1.1 hi)) 0 he h1 h2 rfl f hf
      αS αT RS RT a b).1 k (mem_hyp he hk) k' (mem_hyp he hk')
  refine ⟨fix, fun e ϖ x t he h1 h2 hx => ?_⟩
  obtain ⟨αS, RS, -, a, -, a', -⟩ := exists_data he h1 h2 S
  obtain ⟨αT, -, RT, -, b, -, b'⟩ := exists_data he h1 h2 T
  have eS : ∀ f, IsVacAt ψ S T P f → ∀ j, j ≤ S.rank → ∑ γ ∈ RS j, om (γ, 1) f =
      opOf (om.comp (MonoidHom.inl _ _)) P (Finsupp.single (dualLab (splitLab S.rank j)) 1) f := fun f hf j hj =>
    ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors S P).1 _ _ (a' j hj)).2 _ (om.comp (MonoidHom.inl _ _)) f
      fun k hk => fix f hf k hk 1 (one_mem_hyp he T)
  have eT : ∀ f, IsVacAt ψ S T P f → ∀ j, j ≤ T.rank → ∑ γ ∈ RT j, om (1, γ) f =
      opOf (om.comp (MonoidHom.inr _ _)) P (Finsupp.single (splitLab T.rank j) 1) f := fun f hf j hj =>
    ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors T P).1 _ _ (b' j hj)).2 _ (om.comp (MonoidHom.inr _ _)) f
      fun k hk => fix f hf 1 (one_mem_hyp he S) k hk
  refine ⟨fun hr k hk f hf => ?_, fun hr k hk f hf => ?_⟩
  · rw [dualC_splitC, opOf_trunc, ← eT f hf k hk, (main e ϖ x t he h1 h2 hx f hf αS αT RS RT a b).2.1 hr k hk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [eS f hf j (by rw [Finset.mem_range] at hj; omega)]
  · rw [splitC, opOf_trunc, dualC, Finsupp.mapDomain_single, ← eS f hf k hk,
      (main e ϖ x t he h1 h2 hx f hf αS αT RS RT a b).2.2 hr k hk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [eT f hf j (by rw [Finset.mem_range] at hj; omega)]

end GlobalTheory.Hk3.SplitMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneRankOneLocalParam
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.CuspRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.AwayLGC

theorem weil_deligne_rank_one_eq_local : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ), Continuous μ → IsLAdicOf art ι χ n μ → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal), GlobalTheory.WeilDeligne.wdOf h hl ι (rk1 μ) = ParLaws.locPar hL (CG.ofChar χ) h := by
  intro hL E Ω _ _ _ _ _ _ l _ ι art hart χ n μ hμ hlad A w h hl
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL h
  rw [ParLaws.locPar_ofChar, H.one]
  refine GlobalTheory.WeilDeligne.wdOf_eq_mk hl _ rfl fun g => ?_
  have e := hlad.loc_away (Or.inl hl) (a g) (g : G E Ω) (ha.glob art hart g)
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [Subsingleton.elim i 0]
  simp [GlobalTheory.WeilDeligne.toEndC_apply, GlobalTheory.TripleGal.rk1, Matrix.mulVec, dotProduct, e]

end GlobalTheory.AwayLGC

end
end

