import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0001

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.FirstLevelOfThreeVarParallelogram
section
noncomputable section

namespace Formalism.L2.Th1.B.E3

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)

theorem parallelogram_three_sub_pairs {K : Type} [NormedField K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (hF : MvPowerSeries.constantCoeff F = 0) (i f : PowerSeries K)
    (hi : PowerSeries.constantCoeff i = 0) :
    par3 F i f -
        MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1]
          (par F i f) -
        MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]
          (par F i f) -
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]
          (par F i f) =
      d1 F (cob F f) := by
  have h0 : ∀ j : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  rw [parallelogram_coboundary_three_vars F hF f, cube_par_subst F hF i f hi _ _ (h0 0) (h0 1),
    cube_par_subst F hF i f hi _ _ (h0 0) (h0 2), cube_par_subst F hF i f hi _ _ (h0 1) (h0 2)]
  unfold par3 F3 lawDifferenceThree in3 at1
  ring

theorem cube_relation_from_parallelograms : CubeFromPars := by
  intro K _ _ _ F l i f hF hi hp h3
  obtain ⟨_, hsymm, _, hadd, _⟩ := equivalence_rules K (Fin 3)
  have hsubS : ∀ a b : MvPowerSeries (Fin 3) K, Simeq a 0 → Simeq b 0 → Simeq (a - b) 0 := by
    intro a b ha hb
    have h := hadd a 0 0 b ha (hsymm _ _ hb)
    rw [add_zero, zero_add] at h
    unfold Simeq at h ⊢
    simpa using h
  have hpar : ∀ j k : Fin 3,
      Simeq (MvPowerSeries.subst ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k]
        (par F i f)) 0 := by
    intro j k
    have hc : ∀ m : Fin 2, MvPowerSeries.constantCoeff
        (![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] m) = 0 := by
      intro m; fin_cases m <;> simp
    have hI : ∀ m : Fin 2, Integral
        (![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] m) := by
      intro m; fin_cases m <;> simp [integral_mvPowerSeries_X]
    have h := (equivalence_rules K (Fin 2)).2.2.2.2 (Fin 3) (par F i f) 0 _ hc hI hp
    have hz : MvPowerSeries.subst ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k]
        (0 : MvPowerSeries (Fin 2) K) = 0 := by
      rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hc), map_zero]
    rwa [hz] at h
  rw [← parallelogram_three_sub_pairs F hF.1 i f hi.1]
  exact hsubS _ _ (hsubS _ _ (hsubS _ _ h3 (hpar 0 1)) (hpar 0 2)) (hpar 1 2)

theorem log_sigma_pullback_cocycle_jets_of_parallelogram_and_cube (hP : ParThree) (hC : CubeFromPars) : LogSigmaPullbackCocycleJets := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 P l i ep F hW hF hi hc hc3
  have hpar := parO K g2 g3 s2 c0 P l i ep F hW hF hi hc
  have hp3 := hP K g2 g3 s2 c0 a1 a3 P l i ep F hW hF hi hc hc3
  have hd := hC K F l i (phO s2 P l) hF hi hpar hp3
  have hf0 := constantCoeff_eq_zero_of_parallelogram hF hi hpar
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phO s2 P l) hF hf0
  refine ⟨hdiv, hsw, hd, ?_, fun n hn => jetsThree K F l _ hF hd n hn⟩
  rw [hsw]
  exact hd

end Formalism.L2.Th1.B.E3
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.SigmaOneCocycleShifted
section
noncomputable section

namespace Formalism.L2.Th1.B.Cor

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)

theorem even_phi_simeq_odd_phi : PhESimPhO := by
  intro K _ _ _ g2 g3 s2 c0 e1 P l i ep F hP he hF hC hc h2
  exact simeqHalf K Unit _ _ h2 ((diffPh K g2 g3 s2 c0 e1 P l i ep F hP he hF hC).2 hc)

theorem sigma_one_cocycle_shifted : SigmaOneCocycleShifted := by
  intro K _ _ _ g2 g3 s2 c0 e1 P l i ep F hP he hF hi hC hc hk h2
  have hW := wOfWp K g2 g3 e1 P hP he
  have hw := (wIntegral K c0 e1 P l i ep F hF hC hc).2
  obtain ⟨a, -, b, c⟩ := f1E K (3 * e1) (3 * e1 ^ 2 - g2 / 4) e1 s2 (wOf e1 P) l i F hW hF hi hk hw h2
  exact ⟨a, b, c⟩

theorem cc_Dinv {K : Type} [Field K] [CharZero K] (l f : PowerSeries K)
    (h1 : PowerSeries.coeff 1 l = 1) :
    PowerSeries.constantCoeff (Dinv l f) = PowerSeries.coeff 1 f := by
  have key : ∀ g : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.derivative K g) =
      PowerSeries.coeff 1 g := by
    intro g
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  unfold Dinv
  rw [map_mul, PowerSeries.constantCoeff_inv, key, key, h1, inv_one, one_mul]

theorem first_jet_of_formal_law : JetOne := by
  intro K _ _ _ l i f hl0 hl1 hi hS
  obtain ⟨hi0, -, hil⟩ := hi
  obtain ⟨hg0, hE⟩ := hS
  have hi1 : PowerSeries.coeff 1 i = -1 := by
    have e := law_coeff_one_subst l i hi0
    rw [hil, map_neg, hl1, one_mul] at e
    exact e.symm
  have hE1 : PowerSeries.coeff 1
      (PowerSeries.subst (PowerSeries.subst i f - f : PowerSeries K) (PowerSeries.exp K) :
        PowerSeries K) = PowerSeries.coeff 1 (PowerSeries.subst i f - f : PowerSeries K) := by
    rw [law_coeff_one_subst _ _ hg0, PowerSeries.coeff_exp]
    simp
  have hn : ‖PowerSeries.coeff 1 (PowerSeries.subst i f - f : PowerSeries K)‖ ≤ 1 := by
    rw [← hE1]
    exact hE (Finsupp.single () 1)
  rw [map_sub, law_coeff_one_subst f i hi0, hi1] at hn
  rw [cc_Dinv l f hl1, ← norm_neg]
  have : -(2 * PowerSeries.coeff 1 f) = PowerSeries.coeff 1 f * -1 - PowerSeries.coeff 1 f := by
    ring
  rw [this]
  exact hn

theorem jets_of_odd_parallelogram_phi : JetsPhO := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hC h2 n hn
  rcases hn with rfl | hn
  · have hS := phOEven K s2 P l i hP.2.1 hF.2.2.1 hF.2.2.2.1 hi
    have h := first_jet_of_formal_law K l i _ hF.2.2.1 hF.2.2.2.1 hi hS
    rw [norm_mul, h2, one_mul] at h
    exact h
  · exact jetsThree K F l _ hF (f1O K g2 g3 s2 c0 P l i ep F hP hF hi hC h2).2.2.1 n hn

end Formalism.L2.Th1.B.Cor
end
end

