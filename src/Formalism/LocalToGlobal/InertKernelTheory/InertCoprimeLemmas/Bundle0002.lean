import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0004
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0006
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0001
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0009
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GenusOneWittExistsOf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0005
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0004
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0005
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GenusOneDatumExistence
section
noncomputable section

namespace Formalism.L2.KerInert.GenusOneDatumExistence

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend PowerSeries

section Gen

variable {p : ℕ} [Fact p.Prime]

theorem mem_Wp_of_kur {x : ℂ_[p]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h1 : ‖x‖ ≤ 1) : x ∈ Wp p := by
  have hp : p.Prime := Fact.out
  have hB := ((Formalism.L2.Th1.D.kurIntegers p).1 x).2 ⟨hx, h1⟩
  have hS : Formalism.L2.Th1.D.muPrime p = {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} := by
    ext ζ
    simp only [Formalism.L2.Th1.D.muPrime, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn), h⟩
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hn), h⟩
  unfold Formalism.L2.Th1.D.ringB Formalism.L2.Th1.D.ringA at hB
  rw [hS] at hB
  exact hB

theorem logF_eq : logF p = Formalism.L2.Th1.CM.ltLog ℂ_[p] p := by
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (fun j : ℕ => p ^ (2 * j)) := by
    intro a b h
    have := Nat.pow_right_injective hp.two_le h
    simpa using this
  ext n
  simp only [logF, Formalism.L2.Th1.CM.ltLog, coeff_mk]
  split_ifs with h
  · have hj := Nat.find_spec h
    set j0 := Nat.find h
    have hn : n = p ^ (2 * j0) := by rw [hj, ← pow_mul]
    rw [Finset.sum_eq_single j0]
    · rw [if_pos hn]
    · intro j _ hne
      rw [if_neg]
      intro h'
      exact hne (hinj (h'.symm.trans hn))
    · intro hj0
      exfalso
      apply hj0
      rw [Finset.mem_range, hn]
      have : j0 < p ^ j0 := Nat.lt_pow_self hp.one_lt
      have h2 : p ^ j0 ≤ p ^ (2 * j0) := Nat.pow_le_pow_right hp.pos (by omega)
      omega
  · apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro h'
    exact h ⟨j, by rw [h', pow_mul]⟩

theorem isWq_wU (W : WeierstrassCurve ℂ_[p]) : Formalism.MainNotions.TaylorLogMetric.IsWq W (Formalism.L2.Th1.A.wU W) := by
  have hF := (Formalism.L2.Th1.A.CurveSer.wSer_fixed W).2
  rw [Formalism.L2.Th1.A.CurveSer.wSer_eq] at hF
  unfold Formalism.MainNotions.TaylorLogMetric.IsWq
  simp only [PowerSeries.algebraMap_eq]
  apply mul_left_cancel₀ (pow_ne_zero 3 (X_ne_zero (R := ℂ_[p])))
  linear_combination hF

theorem norm_four (h5 : 5 ≤ p) : ‖(4 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have h := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) (m := 4) hp
    (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p) (by
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega)
  exact_mod_cast h

theorem datum_of_short (h5 : 5 ≤ p) (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (g2 g3 : ℂ_[p])
    (hW : C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ = Formalism.L2.Th1.A.shortW g2 g3)
    (k2 : g2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (k3 : g3 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (n2 : ‖g2‖ ≤ 1) (n3 : ‖g3‖ ≤ 1)
    (nd : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) (ε : ℂ_[p]) (hε1 : ‖ε‖ = 1)
    (hint : ∀ n : ℕ,
      PowerSeries.coeff n ((Formalism.L2.Th1.CM.uSer g2 g3).subst (PowerSeries.C ε * Formalism.L2.Th1.CM.ltLog ℂ_[p] p)) ∈
          Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧
        ‖PowerSeries.coeff n ((Formalism.L2.Th1.CM.uSer g2 g3).subst
          (PowerSeries.C ε * Formalism.L2.Th1.CM.ltLog ℂ_[p] p))‖ ≤ 1) :
    ∃ g : G1 p, g.lam = lam ∧ g.abelian₂ = Λ ∧ g.C = C ∧ g.Ok ∧ ModelOverW g.lam g.abelian₂ g.C ∧ LTIso g := by
  set S := Formalism.L2.Th1.A.shortW g2 g3 with hS
  let g : G1 p := ⟨lam, Λ, C, Formalism.L2.Th1.A.wU S, Formalism.L2.Th1.A.expSer S⟩
  have hgW : g.W = S := hW
  have h4 := norm_four (p := p) h5
  have hWq : Formalism.MainNotions.TaylorLogMetric.IsWq g.W g.wq := by
    rw [hgW]; exact isWq_wU S
  obtain ⟨hx0, -, hLE, hEL, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] S
  have hfl : Formalism.MainNotions.TaylorLogMetric.flog S (Formalism.L2.Th1.A.wU S) = Formalism.L2.Th1.A.logSer S :=
    Formalism.L2.KerInert.Dict.formal_logarithm_agree p S _ (isWq_wU S)
  have hΔ : S.Δ = g2 ^ 3 - 27 * g3 ^ 2 := (Formalism.L2.Th1.A.shortInv ℂ_[p] g2 g3).2.2.2
  have na4 : ‖S.a₄‖ ≤ 1 := by
    simp only [hS, Formalism.L2.Th1.A.shortW, norm_div, norm_neg, h4, div_one]; exact n2
  have na6 : ‖S.a₆‖ ≤ 1 := by
    simp only [hS, Formalism.L2.Th1.A.shortW, norm_div, norm_neg, h4, div_one]; exact n3
  have hU : IsModelU lam Λ C := by
    show Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₁ ∧ Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₂ ∧
      Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₃ ∧ Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₄ ∧
      Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₆ ∧ ‖(C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).Δ‖ = 1
    rw [hW]
    refine ⟨?_, ?_, ?_, na4, na6, by rw [hΔ]; exact nd⟩ <;> simp [Formalism.MainNotions.TaylorLogMetric.IsIntP, hS, Formalism.L2.Th1.A.shortW]
  have hOk : g.Ok := by
    refine ⟨hU, hWq, hx0, ?_⟩
    show PowerSeries.subst (Formalism.L2.Th1.A.expSer S) (Formalism.MainNotions.TaylorLogMetric.flog g.W (Formalism.L2.Th1.A.wU S)) = PowerSeries.X
    rw [hgW, hfl]
    exact hLE
  have hM : ModelOverW lam Λ C := by
    show (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₁ ∈ Wp p ∧ (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₂ ∈ Wp p ∧
      (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₃ ∈ Wp p ∧ (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₄ ∈ Wp p ∧
      (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₆ ∈ Wp p
    rw [hW]
    refine ⟨by simp [hS, Formalism.L2.Th1.A.shortW], by simp [hS, Formalism.L2.Th1.A.shortW],
      by simp [hS, Formalism.L2.Th1.A.shortW], mem_Wp_of_kur ?_ na4, mem_Wp_of_kur ?_ na6⟩
    · simp only [hS, Formalism.L2.Th1.A.shortW]
      exact div_mem (neg_mem k2) (ofNat_mem _ 4)
    · simp only [hS, Formalism.L2.Th1.A.shortW]
      exact div_mem (neg_mem k3) (ofNat_mem _ 4)
  have hpt : (g.pt (MvPowerSeries.C ε * logF p) : MvPowerSeries Unit ℂ_[p]) =
      (Formalism.L2.Th1.CM.uSer g2 g3).subst (PowerSeries.C ε * Formalism.L2.Th1.CM.ltLog ℂ_[p] p) := by
    show PowerSeries.subst (MvPowerSeries.C ε * logF p) (Formalism.L2.Th1.A.expSer S) = _
    rw [hS, ← Formalism.L2.Th1.A.uSerEq, logF_eq]
    rfl
  have hΘ : IntegralW (g.pt (MvPowerSeries.C ε * logF p) : MvPowerSeries Unit ℂ_[p]) := by
    intro n
    rw [hpt, Finsupp.unique_single n]
    exact mem_Wp_of_kur (hint (n ())).1 (hint (n ())).2
  exact ⟨g, rfl, rfl, rfl, hOk, hM, ltIso_of' g hOk hε1 hΘ⟩

end Gen

open NumberField Formalism.BasicNotions

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem genus_one_datum_exists (hInv : Formalism.L2.KerInert.Sigma.InvAlg) : Formalism.L2.KerInert.GenusOneModelExists := by
  intro D cc δ hcurve hδ12 p _ hcop h5 hIn lam
  have hp : p.Prime := Fact.out
  have hcc : cc ≠ ⊥ := hcurve.1

  have hδ : δ ≠ 0 := by
    intro h0
    obtain ⟨⟨L1, hL1⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc 1 hcc one_ne_zero
    obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L1 (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL1)
    have hd := Formalism.L2.Th1.F.discNeZero L1
    apply hd
    have h12 := hδ12
    unfold Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice Formalism.MainNotions.TaylorLogMetric.discr at h12
    rw [h0, e2, e3] at h12
    rw [← h12]; norm_num

  obtain ⟨⟨L, hL⟩, hCM⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ
  obtain ⟨hg2, hg3⟩ := hInv D cc δ hcurve hδ12 L hL
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL)
  set a2 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₃, hg3⟩ with ha3
  obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt p lam

  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hns : ¬ IsSquare ((-(D.host.d : ℤ) : ℤ) : ZMod p) := ZMod.nonsquare_of_jacobiSym_eq_neg_one hIn
  have hsq' : ¬ ∃ a : ZMod p, a ^ 2 = -(D.host.d : ZMod p) := by
    rintro ⟨a, ha⟩; apply hns; exact ⟨a, by push_cast; rw [← ha]; ring⟩
  have hpd : ¬ p ∣ D.host.d := by
    intro h; apply hsq'; refine ⟨0, ?_⟩
    rw [(ZMod.natCast_eq_zero_iff _ _).2 h]; ring
  have hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
    intro ω hω
    have h1 := hCM ω (by rw [← hL]; exact hω)
    rw [← hL] at h1
    have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
      unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
    rw [e]; exact h1

  obtain ⟨g2', g3', hGood⟩ := Formalism.L2.Th1.CM.cm2 D.host.d L hdp.squarefree hd4 hcmby p h5 hpd ι
  obtain ⟨ε, -, hε1, hεint⟩ :=
    Formalism.L2.Th1.CM.cm3 D.host.d L hdp.squarefree hd4 hcmby p h5 hpd hsq' ι g2' g3' hGood
  obtain ⟨k2, k3, n2, n3, nd, μ, hμ, hg2', hg3'⟩ := hGood

  let C : WeierstrassCurve.VariableChange ℂ_[p] := ⟨(Units.mk0 μ hμ)⁻¹, 0, 0, 0⟩
  have ea4 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g2 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4) = -(ι L.g₂) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g2 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4 = ((-a2 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by
      rw [e2]; push_cast; rfl
    rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat, ← hι a2]
  have ea6 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g3 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4) = -(ι L.g₃) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g3 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4 = ((-a3 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by
      rw [e3]; push_cast; rfl
    rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat, ← hι a3]
  have hW : C • Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.A.shortW g2' g3' := by
    have hw : Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = ⟨0, 0, 0, -(ι L.g₂) / 4, -(ι L.g₃) / 4⟩ := by
      simp only [Formalism.MainNotions.TaylorLogMetric.wModel, ea4, ea6]
    rw [hw]
    ext <;> simp [C, Formalism.L2.Th1.A.shortW, hg2', hg3', WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆] <;> ring
  obtain ⟨g, hgl, hgL, -, hOk, hM, hLT⟩ :=
    datum_of_short h5 lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) C g2' g3' hW k2 k3 n2 n3 nd ε hε1 hεint
  exact ⟨g, hgl, ⟨hcurve, hcop, hδ12, hgL, hOk⟩, hM, hLT⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem genus_one_datum_exists_lattice (hInv : Formalism.L2.KerInert.Sigma.InvAlg) : Formalism.L2.KerInert.GenusOneModelExistsLattice := by
  intro D cc δ hcurve hδ12 p _ h5 hIn lam
  obtain ⟨cc', δ', hc', hd', hcop, hlat⟩ := Formalism.L2.KerInert.curve_ideal_prime D cc δ hcurve hδ12 p hIn
  obtain ⟨g, hgl, hAt, hM, hLT⟩ := genus_one_datum_exists hInv D cc' δ' hc' hd' p hcop h5 hIn lam
  exact ⟨cc', δ', g, hc', hd', hlat.symm, hgl, hAt, hM, hLT⟩

end Formalism.L2.KerInert.GenusOneDatumExistence
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMModel
section
noncomputable section

namespace Formalism.L2.KerInert.MModel

open PowerSeries
open Formalism.L2.Th1.A (shortW logSer expSer wpReg)
open Formalism.L2.KerInert.MC (phi)

variable {p : ℕ} [Fact p.Prime]

def scaleVC (e : ℂ_[p]ˣ) : WeierstrassCurve.VariableChange ℂ_[p] := ⟨e⁻¹, 0, 0, 0⟩

theorem scaleVC_smul (e : ℂ_[p]ˣ) (g2 g3 : ℂ_[p]) :
    scaleVC e • shortW g2 g3 = shortW ((e : ℂ_[p]) ^ 4 * g2) ((e : ℂ_[p]) ^ 6 * g3) := by
  ext <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, scaleVC, shortW, inv_inv] <;> ring

theorem norm_four (h5 : 5 ≤ p) : ‖(4 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  rw [show (4 : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((4 : ℕ) : ℚ_[p]) by rw [map_natCast]; norm_num,
    norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
  have := Nat.le_of_dvd (by norm_num) hd
  omega

theorem coeffIn_short (h5 : 5 ≤ p) {g2 g3 : ℂ_[p]} (n2 : ‖g2‖ ≤ 1) (n3 : ‖g3‖ ≤ 1) :
    Formalism.L2.Th1.C.CoeffIn (Formalism.L2.KerInert.ModelP.RB p) (shortW g2 g3) := by
  have h4 := norm_four h5
  simp only [Formalism.L2.Th1.C.CoeffIn, Formalism.L2.Th1.C.mem_unitBall_iff, shortW, norm_zero, zero_le_one,
    norm_div, norm_neg, h4, div_one, true_and]
  exact ⟨n2, n3⟩

theorem param (h5 : 5 ≤ p) (g2 g3 ε : ℂ_[p]) (hε : ‖ε‖ = 1) (n2 : ‖g2‖ ≤ 1) (n3 : ‖g3‖ ≤ 1)
    (nd : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) (hth : ∀ n, ‖coeff n (Formalism.L2.Th1.D.thetaS p g2 g3 ε)‖ ≤ 1)
    (C : WeierstrassCurve.VariableChange ℂ_[p])
    (i1 : ‖(C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3)).a₁‖ ≤ 1) (i2 : ‖(C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3)).a₂‖ ≤ 1)
    (i3 : ‖(C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3)).a₃‖ ≤ 1) (hΔ : ‖(C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3)).Δ‖ = 1) :
    ∃ h : PowerSeries ℂ_[p], constantCoeff h = 0 ∧ (∀ n, ‖coeff n h‖ ≤ 1) ∧ ‖coeff 1 h‖ = 1 ∧
      PowerSeries.C (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * (logSer (C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3))).subst h =
        Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p := by
  have hp2 : 2 ≤ p := by omega
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h, norm_zero] at hε
    exact zero_ne_one hε
  set e : ℂ_[p]ˣ := Units.mk0 ε hε0 with he
  have hee : (e : ℂ_[p]) = ε := rfl
  have hW' : shortW (ε ^ 4 * g2) (ε ^ 6 * g3) = scaleVC e • shortW g2 g3 := by
    rw [scaleVC_smul, hee]
  set D := C * scaleVC e with hD
  have hCD : C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3) = D • shortW g2 g3 := by
    rw [hW', hD, mul_smul]
  have hΔ0 : (shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
    simp only [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have hW0int : Formalism.L2.Th1.C.CoeffIn (Formalism.L2.KerInert.ModelP.RB p) (shortW g2 g3) :=
    coeffIn_short h5 n2 n3
  obtain ⟨hu, hui, hr, hs, ht⟩ := Formalism.L2.KerInert.ModelP.vc_gen h5 (shortW g2 g3)
    (by simp [shortW]) (by simp [shortW]) (by simp [shortW]) (by rw [hΔ0, nd]) D
    (by rw [← hCD]; exact i1) (by rw [← hCD]; exact i2) (by rw [← hCD]; exact i3)
    (by rw [← hCD]; exact hΔ)
  have hsu : ((scaleVC e).u : ℂ_[p]) = ε⁻¹ := by
    show ((e⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ε⁻¹
    rw [Units.val_inv_eq_inv_val, hee]
  have hDu : (D.u : ℂ_[p]) = C.u * ε⁻¹ := by
    rw [← hsu]
    rfl
  have hCu : ‖(C.u : ℂ_[p])‖ = 1 := by
    rw [hDu, norm_mul, norm_inv, hε, inv_one, mul_one] at hu
    exact hu
  have hphiInt : Formalism.L2.Th1.C.IntPS (Formalism.L2.KerInert.ModelP.RB p) (phi (shortW g2 g3) D) :=
    Formalism.L2.KerInert.MC.intPS_phi (shortW g2 g3) hW0int D
      ((Formalism.L2.Th1.C.mem_unitBall_iff _).mpr hu.le) ((Formalism.L2.Th1.C.mem_unitBall_iff _).mpr hr)
      ((Formalism.L2.Th1.C.mem_unitBall_iff _).mpr hs) ((Formalism.L2.Th1.C.mem_unitBall_iff _).mpr ht)
  have hthInt : Formalism.L2.Th1.C.IntPS (Formalism.L2.KerInert.ModelP.RB p) (Formalism.L2.Th1.D.thetaS p g2 g3 ε) :=
    fun n => (Formalism.L2.Th1.C.mem_unitBall_iff _).mpr (hth n)
  have hlg0 : constantCoeff (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) = 0 :=
    Formalism.InvariantFactorPaths.G7.FormalGroupLaws.constantCoeff_lgF p hp2
  have hth0 : constantCoeff (Formalism.L2.Th1.D.thetaS p g2 g3 ε) = 0 := by
    simp only [Formalism.L2.Th1.D.thetaS]
    refine PowerSeries.constantCoeff_subst_eq_zero
      (by rw [map_mul]; exact mul_eq_zero_of_right _ hlg0) _ ?_
    simp [Formalism.L2.Th1.CM.uSer]
  set b : PowerSeries ℂ_[p] := PowerSeries.C (C.u : ℂ_[p]) * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p with hbdef
  have hb0 : constantCoeff b = 0 := by simp [hbdef, hlg0]
  have hb : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero' hb0
  obtain ⟨hE0, hE1, hEL, -, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] (D • shortW g2 g3)
  have hE : PowerSeries.HasSubst (expSer (D • shortW g2 g3)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hE0
  have hh : PowerSeries.subst b (expSer (D • shortW g2 g3)) =
      PowerSeries.subst (Formalism.L2.Th1.D.thetaS p g2 g3 ε) (phi (shortW g2 g3) D) := by
    have hCX0 : constantCoeff (PowerSeries.C ((D.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X : PowerSeries ℂ_[p]) = 0 := by
      simp
    have hCX : PowerSeries.HasSubst (PowerSeries.C ((D.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X : PowerSeries ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hCX0
    obtain ⟨hE00, -, -, -, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] (shortW g2 g3)
    have hA : PowerSeries.HasSubst (PowerSeries.subst (PowerSeries.C ((D.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X)
        (expSer (shortW g2 g3))) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (PowerSeries.constantCoeff_subst_eq_zero hCX0 _ hE00)
    rw [Formalism.L2.KerInert.MC.exp_eq, PowerSeries.subst_comp_subst_apply hA hb,
      PowerSeries.subst_comp_subst_apply hCX hb]
    congr 1
    have hsb : PowerSeries.subst b (PowerSeries.C ((D.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X : PowerSeries ℂ_[p]) =
        PowerSeries.C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p := by
      rw [PowerSeries.subst_mul hb, PowerSeries.subst_X hb, PowerSeries.subst_C]
      show PowerSeries.C _ * b = _
      rw [hbdef, ← mul_assoc, ← map_mul, Units.val_inv_eq_inv_val, hDu]
      congr 2
      field_simp
    rw [hsb, Formalism.L2.Th1.D.thetaS, Formalism.L2.Th1.A.uSerEq]
  refine ⟨PowerSeries.subst b (expSer (D • shortW g2 g3)), ?_, ?_, ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hb0 _ hE0
  · intro n
    rw [hh]
    exact (Formalism.L2.Th1.C.mem_unitBall_iff _).mp
      (Formalism.L2.KerInert.MC.intPS_subst' _ hphiInt hthInt hth0 n)
  · rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hb0, hE1, one_mul, hbdef, PowerSeries.coeff_C_mul,
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF p hp2, mul_one, hCu]
  · rw [hCD, ← PowerSeries.subst_comp_subst_apply hE hb, hEL, PowerSeries.subst_X hb, hbdef,
      ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

section Exp

open Formalism.L2.Th1.B (fExp fLog sigS sigma lU fExp_add constantCoeff_fExp fExp_fLog constantCoeff_fLog)

theorem X_mul_shift (f : PowerSeries ℂ_[p]) (hf : constantCoeff f = 0) :
    f = X * PowerSeries.mk (fun n => coeff (n + 1) f) := by
  have h := PowerSeries.sub_const_eq_X_mul_shift f
  rwa [hf, map_zero, sub_zero] at h

theorem subst_fExp {a f : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (hf : constantCoeff f = 0) :
    PowerSeries.subst a (fExp (ι := Unit) f) = fExp (ι := Unit) (PowerSeries.subst a f) := by
  simp only [fExp]
  exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hf)
    (PowerSeries.HasSubst.of_constantCoeff_zero' ha) _

theorem sig_at (h5 : 5 ≤ p) (g2 g3 s2 ε : ℂ_[p]) :
    (Formalism.L2.Th1.B.sgStar s2 (wpReg (shortW g2 g3))).subst (PowerSeries.C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) =
      PowerSeries.C ε * X * fExp (-Formalism.L2.Th1.D.phFF p g2 g3 s2 ε) := by
  have hp2 : 2 ≤ p := by omega
  set L : PowerSeries ℂ_[p] := PowerSeries.C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p with hLdef
  set P := wpReg (shortW g2 g3)
  have hlg0 : constantCoeff (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) = 0 :=
    Formalism.InvariantFactorPaths.G7.FormalGroupLaws.constantCoeff_lgF p hp2
  have hL0 : constantCoeff L = 0 := by simp [hLdef, hlg0]
  have hL : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero' hL0
  have hS0 : constantCoeff (sigS P) = 0 := by
    simp [sigS, Formalism.L2.Th1.B.constantCoeff_prim]
  have hQ0 : constantCoeff (-(PowerSeries.C (s2 / 2) * X ^ 2 : PowerSeries ℂ_[p])) = 0 := by simp
  have hA0 : constantCoeff (PowerSeries.subst L (sigS P)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hL0 _ hS0
  have hB0 : constantCoeff (-(PowerSeries.C (s2 / 2) * L ^ 2)) = 0 := by simp [hL0]
  have hAB : constantCoeff (PowerSeries.subst L (sigS P) + -(PowerSeries.C (s2 / 2) * L ^ 2)) = 0 := by
    rw [map_add, hA0, hB0, add_zero]
  have hU1 : constantCoeff (lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p)) = 1 := by
    have h := Formalism.InvariantFactorPaths.G7.coeff_lgF_pow ℂ_[p] hp2 0
    simp only [pow_zero, inv_one] at h
    simpa [lU] using h
  have hF0 : constantCoeff (fLog (lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p))) = 0 :=
    constantCoeff_fLog hU1
  have hXU : X * lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) = Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p :=
    (X_mul_shift _ hlg0).symm
  have hL' : L = PowerSeries.C ε * X * lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) := by
    rw [mul_assoc, hXU]
  have hsubQ : PowerSeries.subst L (-(PowerSeries.C (s2 / 2) * X ^ 2 : PowerSeries ℂ_[p])) =
      -(PowerSeries.C (s2 / 2) * L ^ 2) := by
    rw [← PowerSeries.coe_substAlgHom hL, map_neg, map_mul, map_pow, PowerSeries.coe_substAlgHom hL,
      PowerSeries.subst_X hL, PowerSeries.subst_C]
    rfl
  have hphi : -Formalism.L2.Th1.D.phFF p g2 g3 s2 ε =
      PowerSeries.subst L (sigS P) + -(PowerSeries.C (s2 / 2) * L ^ 2) +
        fLog (lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p)) := by
    simp only [Formalism.L2.Th1.D.phFF]
    ring
  rw [hphi, fExp_add hAB hF0, fExp_add hA0 hB0, fExp_fLog hU1]
  simp only [Formalism.L2.Th1.B.sgStar, sigma]
  rw [PowerSeries.subst_mul hL, PowerSeries.subst_mul hL, PowerSeries.subst_X hL,
    subst_fExp hL0 hS0, subst_fExp hL0 hQ0, hsubQ]
  generalize fExp (PowerSeries.subst L (sigS P)) = a
  generalize fExp (-(PowerSeries.C (s2 / 2) * L ^ 2)) = b
  rw [hL']
  ring

end Exp

section EPart

open Formalism.L2.Th1.B (fExp fExp_add constantCoeff_fExp)

end EPart

section Comparison₂

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

end Comparison₂

end Formalism.L2.KerInert.MModel
end
end

