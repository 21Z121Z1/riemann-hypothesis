import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussEveryOrth7
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.Bundle0003
import Formalism.GaussJetBounds.OneLetterGaussJets.GainDominatesOddLevelSum
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0004
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0015
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementA

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.EvenDegreeWeightBounds
section
namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (cm2 cm3 cm4)

theorem matrix_entries_all_disc_seven : ThmAEntryAll7 := by
  intro l _ _ g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN d N0 N1 _ hd2 hde hN0 ιr _ _ om oms hO hT hζ U0 Φ hU0
    hΦ0 hΦ TT colN p hp hp1 I nu1 nu2 size h1 h2 h3 hJ δ hδ
  obtain ⟨a1, a2, -⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨K1, ζ, be, g, U, hK1, hζ', hbe, hg0, hg, hUi, heq⟩ := CohomologyFunctoriality₂.thetaForm l (CM.MaximalUnramifiedExtension l) σ hσ
    (CM.MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2 d N0 N1 hd2 hde ιr om oms hO hT hζ U0 Φ hU0 hΦ0 hΦ
  rw [heq]
  exact Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAEntry7 l d N0 N1 hσ.2.1 hd2 hde hN0 K1 hK1 ζ hζ' be hbe g hg0 hg U hUi (-1)
    (Or.inr rfl) TT colN p hp hp1 I nu1 nu2 size h1 h2 h3 hJ δ hδ

theorem gauss_form_all_disc_seven : ThmAGaussAll7 := by
  intro l _ _ g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN d N0 N1 _ hd2 hde hN0 ιr _ _ om oms hO hT hζ U0 Φ hU0
    hΦ0 hΦ TT colN p hp hp1 I nu1 nu2 size h1 h2 h3 hJ n
  obtain ⟨a1, a2, -⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨K1, ζ, be, g, U, hK1, hζ', hbe, hg0, hg, hUi, heq⟩ := CohomologyFunctoriality₂.thetaForm l (CM.MaximalUnramifiedExtension l) σ hσ
    (CM.MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2 d N0 N1 hd2 hde ιr om oms hO hT hζ U0 Φ hU0 hΦ0 hΦ
  rw [heq]
  exact Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAGauss7 l d N0 N1 hσ.2.1 hd2 hde hN0 K1 hK1 ζ hζ' be hbe g hg0 hg U hUi (-1)
    (Or.inr rfl) TT colN p hp hp1 I nu1 nu2 size h1 h2 h3 hJ n

theorem one_letter_gauss_all_disc_seven : OneLetterGaussAll7 := by
  intro l _ _ g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN N0 N1 C U0 Φ hU0 hΦ0 hΦ p hp I n
  obtain ⟨a1, a2, a3⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨ζ, hζ⟩ := FAux.exists_root2 l
  obtain ⟨U, hUi, hUeq⟩ := single_letter_theta_factorization (CM.MaximalUnramifiedExtension l) ℂ_[l] l N0 N1 σ (CM.MaximalUnramifiedExtension l).subtype hσ (FAux.norm_coe l) F hF _
    a1 a2 ζ hζ _ a3 U0 Φ hU0 hΦ0 hΦ
  obtain ⟨g, hg0, hg, -⟩ := Formalism.DworkPowerSeriesWeights.generalized_log_inverse.{0, 0} ℂ_[l] l hσ.1
    (Fin N0 × Fin N1) id
  have hg' : ∀ y, MvPowerSeries.subst g (Formalism.DworkPowerSeriesWeights.oneLog (K := ℂ_[l]) l y) = MvPowerSeries.X y := by
    intro y
    rw [(Formalism.DworkPowerSeriesWeights.logarithm_weight_comparison.{0} ℂ_[l] l 2 N0 N1).2.2 y]
    exact hg y
  obtain ⟨hT1, hT2, -, -⟩ := Formalism.DworkPowerSeriesWeights.admissibleTransfer (CM.MaximalUnramifiedExtension l) ℂ_[l] (CM.MaximalUnramifiedExtension l).subtype
    (FAux.norm_coe l) l 2 N0 N1 ⊤ ζ
    (beMean (d := 2) l σ _ (fun _ : Unit => (1 : CM.MaximalUnramifiedExtension l)) (fun _ => 1) ζ)
  rw [hUeq g hg0 hg']
  exact Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.oneLetterGauss7 l N0 N1 C hσ.2.1 _ (hT1 (unramified_top (CM.MaximalUnramifiedExtension l) l σ hσ))
    ((CM.MaximalUnramifiedExtension l).subtype ζ) (hζ.map_of_injective (CM.MaximalUnramifiedExtension l).subtype.injective) _
    (hT2 (biextension_hypotheses_of_level_one (CM.MaximalUnramifiedExtension l) l 2 σ hσ le_rfl (by decide) F hF _ a1 Unit _ _ (SingleLetterLog.owOK_two σ) ζ hζ))
    1 (by simp) g hg0 hg' U hUi (-1) (Or.inr rfl) p hp I n

theorem matrix_entries_every_integral_disc_seven : ThmAEntryEveryInt7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨s2, hs2, hc2, fun σ hσ F hF => matrix_entries_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem matrix_entries_integral_disc_seven : ThmAEntryInt7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, hs2, hc2, tail⟩ := matrix_entries_every_integral_disc_seven dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, hg, hε, hth, hs2, hc2, tail⟩

theorem gauss_form_every_integral_disc_seven : ThmAGaussEveryInt7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨s2, hs2, hc2, fun σ hσ F hF => gauss_form_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem gauss_form_integral_disc_seven : ThmAGaussInt7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, hs2, hc2, tail⟩ := gauss_form_every_integral_disc_seven dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, hg, hε, hth, hs2, hc2, tail⟩

theorem one_letter_gauss_every_integral_disc_seven : OneLetterGaussEveryInt7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨s2, hs2, hc2, fun σ hσ F hF => one_letter_gauss_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem one_letter_gauss_integral_disc_seven : OneLetterGaussInt7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, hs2, hc2, tail⟩ := one_letter_gauss_every_integral_disc_seven dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, hg, hε, hth, hs2, hc2, tail⟩

theorem ThmAEntryEveryPh7_of (hS : HypShape) : ThmAEntryEveryPh7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev hN0' ιr _ _ om oms hO hT hζ n _ f f' hH Θ hInt
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact matrix_entries_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev hN0' ιr om oms hO hT hζ U0 Φ hU hΦ hsim

theorem matrix_entries_sharp_of_kappa_integral (hK : uniformGaussModelConditionReformulated) (hS : HypShape) : MatrixEntriesSharpCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev hN0' ιr _ _ om oms hO hT hζ n _ _ f f' hH Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact matrix_entries_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev hN0' ιr om oms hO hT hζ U0 Φ hU hΦ hsim

theorem ThmAEntryEveryOrth7_of (hS : OrthShape) : ThmAEntryEveryOrth7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev hN0' ιr _ _ om oms hO hT hζ n _ f f' hH ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 (Formalism.L2.Th1.F.scalePair L c hc) ι g2 g3 ε s2 e2 e3 es
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH ω₀ hω hω2 κ r s N
    hr hN0 hlN hs
  rw [hΘ]
  exact matrix_entries_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev hN0' ιr om oms hO hT hζ U0 Φ hU hΦ hsim

theorem ThmAGaussEveryPh7_of (hS : HypShape) : ThmAGaussEveryPh7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev hN0' ιr _ _ om oms hO hT hζ n _ f f' hH Θ hInt
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact gauss_form_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev hN0' ιr om oms hO hT hζ U0 Φ hU hΦ hsim

theorem gauss_form_sharp_of_kappa_integral (hK : uniformGaussModelConditionReformulated) (hS : HypShape) : GaussFormSharpCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev hN0' ιr _ _ om oms hO hT hζ n _ _ f f' hH Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact gauss_form_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev hN0' ιr om oms hO hT hζ U0 Φ hU hΦ hsim

theorem ThmAGaussEveryOrth7_of (hS : OrthShape) : ThmAGaussEveryOrth7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev hN0' ιr _ _ om oms hO hT hζ n _ f f' hH ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 (Formalism.L2.Th1.F.scalePair L c hc) ι g2 g3 ε s2 e2 e3 es
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH ω₀ hω hω2 κ r s N
    hr hN0 hlN hs
  rw [hΘ]
  exact gauss_form_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev hN0' ιr om oms hO hT hζ U0 Φ hU hΦ hsim

namespace DiscriminantSevenGaussModels

theorem cc_phSum {l : ℕ} [Fact l.Prime] (h5 : 5 ≤ l) (g2 g3 s2 ε : CM.MaximalUnramifiedExtension l) (n : Type) [Fintype n] :
    MvPowerSeries.constantCoeff
      (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) = 0 := by
  unfold Formalism.L2.Th1.E.phSum
  rw [map_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  refine Pair.constantCoeff_inVar_eq_zero x ?_
  unfold phL
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF (by omega), map_zero]

theorem split {l : ℕ} [Fact l.Prime] (h5 : 5 ≤ l) (g2 g3 s2 ε : CM.MaximalUnramifiedExtension l) (n : Type) [Fintype n]
    (Θ : MvPowerSeries n ℂ_[l]) :
    Θ = Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l])) *
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε)) * Θ) := by
  have h0 := cc_phSum h5 g2 g3 s2 ε n
  obtain ⟨e0, -, eadd, -⟩ := Formalism.L2.Th1.C.mvExpLaws ℂ_[l] n
  have h1 := eadd (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε))) (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε))
    (by rw [map_neg, h0, neg_zero]) h0
  rw [neg_add_cancel, e0] at h1
  rw [← mul_assoc]
  change Θ = (Formalism.L2.Th1.C.mvExp _ * Formalism.L2.Th1.C.mvExp _) * Θ
  rw [← h1, one_mul]

end DiscriminantSevenGaussModels

theorem one_letter_gauss_every_principal_seven : OneLetterGaussEveryPh7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF N0 N1 C Θ hInt
  rw [DiscriminantSevenGaussModels.split h5 g2 g3 s2 ε (Fin N0 × Fin N1) Θ]
  exact one_letter_gauss_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) N0 N1 C
    _ _ hInt (DiscriminantSevenGaussModels.cc_phSum h5 g2 g3 s2 ε _) (InverseCommuting.sim_refl _)

theorem one_letter_gauss_sharp_of_kappa_integral (hK : uniformGaussModelConditionReformulated) : OneLetterGaussSharpCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF N0 N1 C Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) (Fin N0 × Fin N1) Θ γ hγ hK1
  rw [DiscriminantSevenGaussModels.split h5 g2 g3 s2 ε (Fin N0 × Fin N1) Θ]
  exact one_letter_gauss_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) N0 N1 C
    _ _ hInt (DiscriminantSevenGaussModels.cc_phSum h5 g2 g3 s2 ε _) (InverseCommuting.sim_refl _)

theorem OneLetterGaussEveryOrth7_of (hS : OrthShapeOne) : OneLetterGaussEveryOrth7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF N0 N1 C ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  obtain ⟨U0, hU, hΘ⟩ := hS l h5 (Formalism.L2.Th1.F.scalePair L c hc) ι g2 g3 ε s2 e2 e3 es
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth (Fin N0 × Fin N1) ω₀ hω hω2 κ r s N hr hN0 hlN hs
  rw [hΘ]
  exact one_letter_gauss_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) N0 N1 C
    U0 _ hU (DiscriminantSevenGaussModels.cc_phSum h5 g2 g3 s2 ε _) (InverseCommuting.sim_refl _)

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem ThmAEntryOrth7_of (h : ThmAEntryEveryOrth7) : ThmAEntryOrth7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, c, hc, hs2, e2, e3, es, tail⟩ := h dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, c, hc, hg, hε, hth, hs2, e2, e3, es, tail⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem ThmAGaussOrth7_of (h : ThmAGaussEveryOrth7) : ThmAGaussOrth7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, c, hc, hs2, e2, e3, es, tail⟩ := h dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, c, hc, hg, hε, hth, hs2, e2, e3, es, tail⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem OneLetterGaussOrth7_of (h : OneLetterGaussEveryOrth7) : OneLetterGaussOrth7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, c, hc, hs2, e2, e3, es, tail⟩ := h dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, c, hc, hg, hε, hth, hs2, e2, e3, es, tail⟩

end Formalism.L2.Th1.Top
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.GaussFormCMOfUniformGaussModelsOfHypShape
section
namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (cm4)

theorem matrixEntriesCM_of_uniformGaussModels_of_hypShape (hK : uniformGaussModelConditionReformulated) (hS : HypShape) : MatrixEntriesCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev ιr _ _ om oms hO hT hζ n _ _ f f' hH Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ)
    N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact theorem_a_entry_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev ιr om oms hO hT hζ
    U0 Φ hU hΦ hsim

theorem gaussFormCM_of_uniformGaussModels_of_hypShape (hK : uniformGaussModelConditionReformulated) (hS : HypShape) : GaussFormCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev ιr _ _ om oms hO hT hζ n _ _ f f' hH Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ)
    N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact theorem_a_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev ιr om oms hO hT hζ
    U0 Φ hU hΦ hsim

theorem threeBoundsCM_of_uniformGaussModels_of_hypShape (hK : uniformGaussModelConditionReformulated) (hS : HypShape) : ThreeBoundsCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF ν r0 r1 _ om oms hO hT n _ _ f f' hH Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ)
    r0 r1 (Fin ν) n f f' hH Θ hInt
  rw [hΘ]
  exact kernel_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) ν r0 r1 om oms hO hT
    U0 Φ hU hΦ hsim

theorem oneLetterGaussCMReformulated_of_uniformGaussModels (hK : uniformGaussModelConditionReformulated) : OneLetterGaussCMReformulated := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF N0 N1 C Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) (Fin N0 × Fin N1) Θ γ hγ hK1
  have h0 : MvPowerSeries.constantCoeff
      (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l]) = 0 := by
    unfold Formalism.L2.Th1.E.phSum
    rw [map_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    refine Pair.constantCoeff_inVar_eq_zero x ?_
    unfold phL
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF (by omega), map_zero]
  have hΘ : Θ = Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) :
      MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])) *
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε)) * Θ) := by
    obtain ⟨e0, -, eadd, -⟩ := Formalism.L2.Th1.C.mvExpLaws ℂ_[l] (Fin N0 × Fin N1)
    have h1 := eadd (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε))) (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε))
      (by rw [map_neg, h0, neg_zero]) h0
    rw [neg_add_cancel, e0] at h1
    rw [← mul_assoc]
    change Θ = (Formalism.L2.Th1.C.mvExp _ * Formalism.L2.Th1.C.mvExp _) * Θ
    rw [← h1, one_mul]
  rw [hΘ]
  exact one_letter_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) N0 N1 C
    _ _ hInt h0 (InverseCommuting.sim_refl _)

end Formalism.L2.Th1.Top
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormTwelveCubedEqOneOfFiveLePrime
section
noncomputable section

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy jInv)
open Formalism.L2.Th1.E (IntCurve curveL)

namespace GM

variable (p : ℕ) [Fact p.Prime]

theorem norm_divisor_twelve_power_eq_one (h5 : 5 ≤ p) {N k : ℕ} (hN : N ∣ 12 ^ k) : ‖(N : ℂ_[p])‖ = 1 := by
  refine Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p fun h => ?_
  have hp : p.Prime := Fact.out
  have h12 : p ∣ 12 := hp.dvd_of_dvd_pow (h.trans hN)
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem norm_twelve_cubed_eq_one_of_five_le_prime (h5 : 5 ≤ p) : ‖(1728 : ℂ_[p])‖ = 1 := by
  have := norm_divisor_twelve_power_eq_one p h5 (N := 1728) (k := 3) (by norm_num)
  simpa using this

theorem norm_27 (h5 : 5 ≤ p) : ‖(27 : ℂ_[p])‖ = 1 := by
  have := norm_divisor_twelve_power_eq_one p h5 (N := 27) (k := 3) (by norm_num)
  simpa using this

end GM

theorem good_model_exists_all_primes : GoodModelAll := by
  intro dK L hsq hd4 hcm p _ h5 ι
  have hD0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := Formalism.L2.Th1.F.discNeZero L
  obtain ⟨c, hc12⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (show 0 < 12 by norm_num)
  have hc : c ≠ 0 := by
    intro h
    rw [h] at hc12
    exact hD0 (by rw [← hc12]; simp)
  refine ⟨c, hc, ?_⟩
  have hH := Formalism.L2.Th1.F.homogeneity L c hc
  have e2 : (Formalism.L2.Th1.F.scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := hH.2.2.2.2.2.2.2.2.2.1
  have e3 : (Formalism.L2.Th1.F.scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := hH.2.2.2.2.2.2.2.2.2.2
  set a : ℂ := (Formalism.L2.Th1.F.scalePair L c hc).g₂ with ha
  set b : ℂ := (Formalism.L2.Th1.F.scalePair L c hc).g₃ with hb

  have hΔ : a ^ 3 - 27 * b ^ 2 = 1 := by
    rw [e2, e3]
    have : ((c ^ 4)⁻¹ * L.g₂) ^ 3 - 27 * ((c ^ 6)⁻¹ * L.g₃) ^ 2 =
        (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
      field_simp
    rw [this, hc12, inv_mul_cancel₀ hD0]
  have hj : 1728 * a ^ 3 = jInv L := by
    unfold jInv
    rw [e2, ← hc12]
    field_simp
  have hJ : ‖ι (jInv L)‖ ≤ 1 :=
    ReciprocityTheory.ChartRestriction.L1.jInt dK L hsq hd4 hcm p ι
  have ha3 : ‖ι a‖ ^ 3 ≤ 1 := by
    have h := congrArg ι hj
    rw [map_mul, map_pow, map_ofNat] at h
    rw [← h, norm_mul, GM.norm_twelve_cubed_eq_one_of_five_le_prime p h5, one_mul, norm_pow] at hJ
    exact hJ
  have ha1 : ‖ι a‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 ha3
  have hb2 : ‖ι b‖ ^ 2 ≤ 1 := by
    have h : 27 * ι b ^ 2 = ι a ^ 3 - 1 := by
      have h := congrArg ι hΔ
      rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
      linear_combination -h
    have h' := congrArg norm h
    rw [norm_mul, GM.norm_27 p h5, one_mul, norm_pow] at h'
    rw [h', sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by simp))
    rw [norm_pow]; exact ha3
  have hb1 : ‖ι b‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hb2
  unfold curveL
  refine Formalism.L2.Th1.E.ScaledModelNorms.intCurve_short p h5 _ _ ha1 hb1 ?_
  have h := congrArg ι hΔ
  rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
  rw [h, norm_one]

end Formalism.L2.Th1.Top
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussEveryIntProof
section
namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (cm2 cm3 cm4)

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem ThmAEntryInt_proof : ThmAEntryInt := Formalism.L2.Th1.D.thmAEntryFinal cm2 cm3 cm4
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem ThmAGaussInt_proof : ThmAGaussInt := Formalism.L2.Th1.D.thmAGaussFinal cm2 cm3 cm4
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem OneLetterGaussInt_proof : OneLetterGaussInt := Formalism.L2.Th1.D.oneLetterGaussFinal cm2 cm3 cm4
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem KernelInt_proof : KernelInt := Formalism.L2.Th1.D.kernelFinal cm2 cm3 cm4

theorem ThmAEntryEveryInt_proof : ThmAEntryEveryInt := Formalism.L2.Th1.D.thmAEntryEvery cm4
theorem ThmAGaussEveryInt_proof : ThmAGaussEveryInt := Formalism.L2.Th1.D.thmAGaussEvery cm4
theorem OneLetterGaussEveryInt_proof : OneLetterGaussEveryInt := Formalism.L2.Th1.D.oneLetterGaussEvery cm4
theorem KernelEveryInt_proof : KernelEveryInt := Formalism.L2.Th1.D.kernelEvery cm4

end Formalism.L2.Th1.Top
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.StructureTheoremCMOfUniformGaussModelsOfHypShape
section
namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (cm4)

theorem ThmSEveryInt_proof : ThmSEveryInt := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF ν r0 r1 _
  obtain ⟨a1, a2, -⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)
  have : CompleteSpace (CM.MaximalUnramifiedExtension l) := kurComplete l
  exact thmSOfF (CM.MaximalUnramifiedExtension l) ℂ_[l] (CM.MaximalUnramifiedExtension l).subtype l ν r0 r1 σ (FAux.norm_coe l) hσ (FAux.exists_root2 l)
    F hF _ a1 a2

theorem ThmSEveryOrth_of (hS : OrthShape) : ThmSEveryOrth := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF ν r0 r1 _
  obtain ⟨a1, a2, -⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)
  have : CompleteSpace (CM.MaximalUnramifiedExtension l) := kurComplete l
  obtain ⟨cS, h1, h2, h3⟩ := thmSOfF (CM.MaximalUnramifiedExtension l) ℂ_[l] (CM.MaximalUnramifiedExtension l).subtype l ν r0 r1 σ (FAux.norm_coe l) hσ
    (FAux.exists_root2 l) F hF _ a1 a2
  refine ⟨cS, h1, h2, ?_⟩
  intro om oms ϖ μ hϖ hO hT hμ0 hμ n _ f f' hH ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 (Formalism.L2.Th1.F.scalePair L c hc) ι g2 g3 ε s2 e2 e3 es
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) r0 r1 (Fin ν) n f f' hH ω₀ hω hω2 κ r s N
    hr hN0 hlN hs
  rw [hΘ]
  exact h3 om oms ϖ μ U0 Φ hϖ hO hT hμ0 hμ hU hΦ hsim

theorem structureTheoremCM_of_uniformGaussModels_of_hypShape (hK : uniformGaussModelConditionReformulated) (hS : HypShape) : StructureTheoremCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF ν r0 r1 _
  obtain ⟨a1, a2, -⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)
  have : CompleteSpace (CM.MaximalUnramifiedExtension l) := kurComplete l
  obtain ⟨cS, h1, h2, h3⟩ := thmSOfF (CM.MaximalUnramifiedExtension l) ℂ_[l] (CM.MaximalUnramifiedExtension l).subtype l ν r0 r1 σ (FAux.norm_coe l) hσ
    (FAux.exists_root2 l) F hF _ a1 a2
  refine ⟨cS, h1, h2, ?_⟩
  intro om oms ϖ μ hϖ hO hT hμ0 hμ n _ _ f f' hH Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ)
    r0 r1 (Fin ν) n f f' hH Θ hInt
  rw [hΘ]
  exact h3 om oms ϖ μ U0 Φ hϖ hO hT hμ0 hμ hU hΦ hsim

end Formalism.L2.Th1.Top
end

