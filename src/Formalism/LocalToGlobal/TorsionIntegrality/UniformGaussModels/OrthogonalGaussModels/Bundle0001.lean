import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CurveIntegerMultiplicationSeries
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementJ
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0004
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussEveryOrth7
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0005

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KJoint
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)

namespace KJ

theorem phC_eq (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) :
    phC p L ι = Formalism.L2.Th1.E.phL p L ι := by
  unfold phC Formalism.L2.Th1.E.phL
  rw [Formalism.L2.Th1.E.wpBridge p L ι]

theorem phSum_one {K : Type} [Field K] {n : Type} [Fintype n] (ph : PowerSeries K) :
    Formalism.L2.Th1.G.phSum (fun _ : n => (1 : K)) ph = Formalism.L2.Th1.E.phSum ph := by
  unfold Formalism.L2.Th1.G.phSum Formalism.L2.Th1.E.phSum Formalism.InvariantFactorPaths.G7.at1
  exact Finset.sum_congr rfl fun i _ => one_smul _ _

theorem toZ_thetaProd {K : Type} [Field K] {κ n : Type} [Fintype κ] [Fintype n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (r : κ → K) (H : κ → n → PowerSeries K) :
    Formalism.L2.Th1.G.toZ linv (Formalism.L2.Th1.E.thetaProd r H) =
      Formalism.L2.Th1.E.thetaProd r (fun k i => PowerSeries.subst linv (H k i)) := by
  unfold Formalism.L2.Th1.E.thetaProd Formalism.InvariantFactorPaths.G7.at1
  rw [← Formalism.L2.Th1.G.toZHom_apply h0, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_prod]
  congr 1
  · rw [MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Formalism.L2.Th1.G.toZHom_apply, Formalism.L2.Th1.G.toZ_subst_X h0]

end KJ

theorem kernel_bounds_joint : KernelJoint := by
  intro p _ L ι hp2 hW n _ ω₀ hω hω2 κ _ r s N hr hN hpN hs
  have hlp := Formalism.L2.Th1.C.WeierstrassCurveSeries.logPair (curveL p L ι)
  obtain ⟨hl0, -, hv0, -, hlv⟩ := hlp
  have hph : PowerSeries.constantCoeff (Formalism.L2.Th1.E.phL p L ι) = 0 :=
    Formalism.L2.Th1.E.AnaSys.cc_phL p L ι
  have hT := (Formalism.L2.Th1.E.th0Analytic p L ι hp2 hW ω₀ hω hω2).2
  obtain ⟨e1, hInt⟩ := Formalism.L2.Th1.E.prodInt ℂ_[p] κ n (Formalism.L2.Th1.E.phL p L ι) r
    (fun k i => Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.E.phL p L ι) *
      Formalism.L2.Th1.E.inU p L ι (Formalism.L2.Th1.F.opU L (s k i) (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))
    hph hr (fun k i => (hT (s k i) N hN hpN (hs k i)).1)
  refine ⟨_, fun d => hInt d, ?_⟩
  rw [KJ.phC_eq, KJ.phSum_one]
  change _ = Formalism.L2.Th1.G.toZ _ (Formalism.DworkPowerSeriesWeights.mvExp _ * _)
  rw [← e1, KJ.toZ_thetaProd hv0]
  unfold thetaZ
  congr 1
  funext k i
  change _ = PowerSeries.subst _ (Formalism.L2.Th1.B.fExp (-(Formalism.L2.Th1.E.phL p L ι)) * _)
  rw [← mul_assoc, ← Formalism.L2.Th1.B.fExp_add (by rw [map_neg]; exact neg_eq_zero.2 hph) hph,
    neg_add_cancel, Formalism.L2.Th1.B.ParO.fExp_zero, one_mul]
  unfold Formalism.L2.Th1.E.inU
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hv0), hlv]
  exact (PowerSeries.X_subst _).symm

end Formalism.L2.Th1.Top
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussTranslateOfCmCase
section
namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.H (CmOK)

namespace HAux

theorem odd_b {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} (hOK : CmOK a₀ b₀ c₀ dK) : Odd b₀ := by
  obtain ⟨h1, -, h3, -⟩ := hOK
  rcases Int.even_or_odd b₀ with ⟨k, hk⟩ | h
  · exfalso
    subst hk
    have h4 : (dK : ℤ) = 4 * ((a₀ : ℤ) * c₀ - k * k) := by linear_combination -h1
    obtain ⟨m, hm⟩ : ∃ m : ℤ, (dK : ℤ) = 4 * m := ⟨_, h4⟩
    omega
  · exact h

theorem data {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} (ha : 0 < a₀) (hdK : 0 < dK) (hOK : CmOK a₀ b₀ c₀ dK) :
    Squarefree dK ∧ dK % 4 = 3 ∧ Formalism.L2.Th1.CM.HasCMBy dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) := by
  obtain ⟨j, hj⟩ := odd_b hOK
  have h1 := hOK.1
  refine ⟨hOK.2.2.2.squarefree, by have := hOK.2.2.1; omega, ?_⟩
  intro ω hω
  simp only [PeriodPair.lattice, Formalism.L2.Th1.F.cmPair] at hω ⊢
  rw [Submodule.mem_span_pair] at hω ⊢
  obtain ⟨m, n, rfl⟩ := hω
  refine ⟨-m * j - n * c₀, m * a₀ + n * (j + 1), ?_⟩
  have hs : ((Real.sqrt dK : ℝ) : ℂ) ^ 2 = (dK : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h1c : 4 * (a₀ : ℂ) * c₀ = (b₀ : ℂ) ^ 2 + dK := by exact_mod_cast h1
  have hb : (b₀ : ℂ) = 2 * j + 1 := by exact_mod_cast hj
  simp only [Formalism.L2.Th1.CM.omegaK, Formalism.L2.Th1.F.cmTheta, zsmul_eq_mul]
  push_cast
  linear_combination (↑m * ↑a₀ / 2) * hb - ↑n * ((((Real.sqrt dK : ℝ) : ℂ) ^ 2 / 4) * hI - (1 / 4) * hs +
    (1 / 4) * h1c + ((↑b₀ + Complex.I * ((Real.sqrt dK : ℝ) : ℂ)) / 4) * hb)

end HAux

theorem ThmAEntryEveryH_of (hX : MatrixEntriesCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) : ThmAEntryEveryH := by
  unfold ThmAEntryEveryH MatrixEntriesCM at *
  intro hLS hKE a₀ b₀ c₀ dK ha hdK hOK l _ h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨hsf, hd4, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, hg2, hg3, hs2e⟩, hrest⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsf hd4 hcm l h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨lam, hlam, hLT⟩ := hN l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 s2 ε c hc hε hg2 hg3 hs2e
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκalg, hκn, hθ⟩ := hK hLS hKE a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, hκ0, hκalg, hκn, fun θ hθmem heq => ?_⟩
  obtain ⟨g₁, hiso, hidx, hK1⟩ := hθ θ hθmem heq l h5 ι
  refine ⟨g₁, hiso, hidx, ?_⟩
  intro t N hN0 hlN hNt σ hσ γ B' hfr F hF d N0 N1 _ hd2 hde ιr _ _ om oms how htr hζ f f' hhyp
  have hcurve := hK1 g2 g3 ε s2 hLT hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2.1 hε hcoef t N hN0 hlN hNt σ γ B' hfr
  exact hrest σ hσ F hF d N0 N1 hd2 hde ιr om oms how htr hζ n f f' hhyp _ γ hfr.1 hcurve

theorem ThmAGaussEveryH_of (hX : GaussFormCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) : ThmAGaussEveryH := by
  unfold ThmAGaussEveryH GaussFormCM at *
  intro hLS hKE a₀ b₀ c₀ dK ha hdK hOK l _ h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨hsf, hd4, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, hg2, hg3, hs2e⟩, hrest⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsf hd4 hcm l h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨lam, hlam, hLT⟩ := hN l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 s2 ε c hc hε hg2 hg3 hs2e
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκalg, hκn, hθ⟩ := hK hLS hKE a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, hκ0, hκalg, hκn, fun θ hθmem heq => ?_⟩
  obtain ⟨g₁, hiso, hidx, hK1⟩ := hθ θ hθmem heq l h5 ι
  refine ⟨g₁, hiso, hidx, ?_⟩
  intro t N hN0 hlN hNt σ hσ γ B' hfr F hF d N0 N1 _ hd2 hde ιr _ _ om oms how htr hζ f f' hhyp
  have hcurve := hK1 g2 g3 ε s2 hLT hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2.1 hε hcoef t N hN0 hlN hNt σ γ B' hfr
  exact hrest σ hσ F hF d N0 N1 hd2 hde ιr om oms how htr hζ n f f' hhyp _ γ hfr.1 hcurve

theorem OneLetterGaussEveryH_of (hX : OneLetterGaussCMReformulated) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) :
    OneLetterGaussEveryH := by
  unfold OneLetterGaussEveryH OneLetterGaussCMReformulated at *
  intro hLS hKE a₀ b₀ c₀ dK ha hdK hOK l _ h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨hsf, hd4, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, hg2, hg3, hs2e⟩, hrest⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsf hd4 hcm l h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨lam, hlam, hLT⟩ := hN l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 s2 ε c hc hε hg2 hg3 hs2e
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro N0 N1 h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκalg, hκn, hθ⟩ := hK hLS hKE a₀ b₀ c₀ dK ha hdK lam hlam hOK (Fin N0 × Fin N1) h Λ g₀ hLat
  refine ⟨κ, hκ0, hκalg, hκn, fun θ hθmem heq => ?_⟩
  obtain ⟨g₁, hiso, hidx, hK1⟩ := hθ θ hθmem heq l h5 ι
  refine ⟨g₁, hiso, hidx, ?_⟩
  intro t N hN0 hlN hNt σ hσ γ B' hfr F hF C
  have hcurve := hK1 g2 g3 ε s2 hLT hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2.1 hε hcoef t N hN0 hlN hNt σ γ B' hfr
  exact hrest σ hσ F hF N0 N1 C _ γ hfr.1 hcurve

theorem KernelEveryH_of (hX : ThreeBoundsCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) : CMThetaKernelEveryInertPrime := by
  intro hL hκ a₀ b₀ c₀ dK ha hdK hOK l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨hsq, hmod, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, tail⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsq hmod hcm l h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨lam, hlam, hLT⟩ := hN l _ ι g2 g3 s2 ε c hc hε e2 e3 es
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, k1, k2, k3, hθ⟩ := hK hL hκ a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, k1, k2, k3, fun θ hθm hten => ?_⟩
  obtain ⟨g₁, i1, i2, hK1⟩ := hθ θ hθm hten l h5 ι
  refine ⟨g₁, i1, i2, ?_⟩
  intro t N hN0 hlN ht σ hσ γ B' hFr F hF ν r0 r1 _ om oms hO hT f f' hH
  exact tail σ hσ F hF ν r0 r1 om oms hO hT n f f' hH _ γ hFr.1
    (hK1 g2 g3 ε s2 hLT hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth t N hN0 hlN ht σ γ B' hFr)

theorem ThmSEveryH_of (hX : StructureTheoremCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) : ThmSEveryH := by
  intro hL hκ a₀ b₀ c₀ dK ha hdK hOK l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨hsq, hmod, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, c, hc, hs2, e2, e3, es, tail⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsq hmod hcm l h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨lam, hlam, hLT⟩ := hN l _ ι g2 g3 s2 ε c hc hε e2 e3 es
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, k1, k2, k3, hθ⟩ := hK hL hκ a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, k1, k2, k3, fun θ hθm hten => ?_⟩
  obtain ⟨g₁, i1, i2, hK1⟩ := hθ θ hθm hten l h5 ι
  refine ⟨g₁, i1, i2, ?_⟩
  intro t N hN0 hlN ht σ hσ γ B' hFr F hF ν r0 r1 _
  obtain ⟨cS, c1, c2, c3⟩ := tail σ hσ F hF ν r0 r1
  refine ⟨cS, c1, c2, ?_⟩
  intro om oms ϖ μ hϖ hO hT hμ0 hμ f f' hH
  exact c3 om oms ϖ μ hϖ hO hT hμ0 hμ n f f' hH _ γ hFr.1
    (hK1 g2 g3 ε s2 hLT hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth t N hN0 hlN ht σ γ B' hFr)

theorem matrix_entries_translate_of_cm_case (hX : MatrixEntriesSharpCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) : MatrixEntriesSharpTranslate := by
  unfold MatrixEntriesSharpTranslate MatrixEntriesSharpCM at *
  intro hLS hKE a₀ b₀ c₀ dK ha hdK hOK l _ h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨hsf, hd4, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, hg2, hg3, hs2e⟩, hrest⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsf hd4 hcm l h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨lam, hlam, hLT⟩ := hN l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 s2 ε c hc hε hg2 hg3 hs2e
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκalg, hκn, hθ⟩ := hK hLS hKE a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, hκ0, hκalg, hκn, fun θ hθmem heq => ?_⟩
  obtain ⟨g₁, hiso, hidx, hK1⟩ := hθ θ hθmem heq l h5 ι
  refine ⟨g₁, hiso, hidx, ?_⟩
  intro t N hN0 hlN hNt σ hσ γ B' hfr F hF d N0 N1 _ hd2 hde hx ιr _ _ om oms how htr hζ f f' hhyp
  have hcurve := hK1 g2 g3 ε s2 hLT hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2.1 hε hcoef t N hN0 hlN hNt σ γ B' hfr
  exact hrest σ hσ F hF d N0 N1 hd2 hde hx ιr om oms how htr hζ n f f' hhyp _ γ hfr.1 hcurve

theorem gauss_form_translate_of_cm_case (hX : GaussFormSharpCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) : GaussFormSharpTranslate := by
  unfold GaussFormSharpTranslate GaussFormSharpCM at *
  intro hLS hKE a₀ b₀ c₀ dK ha hdK hOK l _ h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨hsf, hd4, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, hg2, hg3, hs2e⟩, hrest⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsf hd4 hcm l h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨lam, hlam, hLT⟩ := hN l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 s2 ε c hc hε hg2 hg3 hs2e
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκalg, hκn, hθ⟩ := hK hLS hKE a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, hκ0, hκalg, hκn, fun θ hθmem heq => ?_⟩
  obtain ⟨g₁, hiso, hidx, hK1⟩ := hθ θ hθmem heq l h5 ι
  refine ⟨g₁, hiso, hidx, ?_⟩
  intro t N hN0 hlN hNt σ hσ γ B' hfr F hF d N0 N1 _ hd2 hde hx ιr _ _ om oms how htr hζ f f' hhyp
  have hcurve := hK1 g2 g3 ε s2 hLT hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2.1 hε hcoef t N hN0 hlN hNt σ γ B' hfr
  exact hrest σ hσ F hF d N0 N1 hd2 hde hx ιr om oms how htr hζ n f f' hhyp _ γ hfr.1 hcurve

theorem one_letter_gauss_translate_of_cm_case (hX : OneLetterGaussSharpCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) :
    OneLetterGaussSharpTranslate := by
  unfold OneLetterGaussSharpTranslate OneLetterGaussSharpCM at *
  intro hLS hKE a₀ b₀ c₀ dK ha hdK hOK l _ h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨hsf, hd4, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, hg2, hg3, hs2e⟩, hrest⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsf hd4 hcm l h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨lam, hlam, hLT⟩ := hN l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 s2 ε c hc hε hg2 hg3 hs2e
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro N0 N1 h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκalg, hκn, hθ⟩ := hK hLS hKE a₀ b₀ c₀ dK ha hdK lam hlam hOK (Fin N0 × Fin N1) h Λ g₀ hLat
  refine ⟨κ, hκ0, hκalg, hκn, fun θ hθmem heq => ?_⟩
  obtain ⟨g₁, hiso, hidx, hK1⟩ := hθ θ hθmem heq l h5 ι
  refine ⟨g₁, hiso, hidx, ?_⟩
  intro t N hN0 hlN hNt σ hσ γ B' hfr F hF C
  have hcurve := hK1 g2 g3 ε s2 hLT hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2.1 hε hcoef t N hN0 hlN hNt σ γ B' hfr
  exact hrest σ hσ F hF N0 N1 C _ γ hfr.1 hcurve

end Formalism.L2.Th1.Top
end

