import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0006
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0003
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0004
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0015
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0011
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0009
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CoefWfPhAt
section
namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

section

variable {p : ℕ} [Fact p.Prime]

theorem ptW_X {σ : Type} (i : σ) : PtW (Xv i : MvPowerSeries σ ℂ_[p]) := by
  classical
  unfold PtW
  constructor
  · intro n
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp

theorem coefWf_add {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) : CoefWf (f + g) := (coefWfRing_holds p σ f g hf hg).1

theorem coefWf_sub {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) : CoefWf (f - g) := (coefWfRing_holds p σ f g hf hg).2.1

theorem coefWf_phAt (g : G1 p) (hph : CoefWf g.ph) {σ : Type} {a : MvPowerSeries σ ℂ_[p]} (ha : PtW a) : CoefWf (g.phAt a) := by
  obtain ⟨ha1, ha2⟩ := ha
  exact substWf_holds p σ g.ph a hph ha1 ha2

theorem coefWf_be (HA : AddPtW) (g : G1 p) (hOk : g.Ok) (hF : IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hph : CoefWf g.ph) {σ : Type} {a b : MvPowerSeries σ ℂ_[p]} (ha : PtW a) (hb : PtW b) : CoefWf (g.be a b) := by
  have hab : PtW (g.add a b) := HA p g hOk hF σ a b ha hb
  show CoefWf (g.phAt (g.add a b) - g.phAt a - g.phAt b)
  exact coefWf_sub (coefWf_sub (coefWf_phAt g hph hab) (coefWf_phAt g hph ha)) (coefWf_phAt g hph hb)

theorem simeqW_of {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) (h : Simeq f g) : SimeqW f g := by

  obtain ⟨h0, hI⟩ := h
  have hr : SimeqW (f - g) 0 :=
    readW_holds p σ (f - g) (coefWf_sub hf hg) (And.intro (by simpa using h0) (by simpa using hI))
  obtain ⟨r0, rI⟩ := hr
  exact And.intro (by simpa using r0) (by simpa using rI)

end

theorem beW_of (HA : AddPtW) (HM : MulPtW) (D : D7)
    (hs : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (α : ℂ_[p] × ℂ_[p]), α ∈ OKp D lam → α.swap ∈ OKp D lam) :
    StatementBilinearWitt D := by
  intro hph _ hadd hend hbi hconj p _ cc δ g hAt hp5 hI hM
  have hOk : g.Ok := hAt.2.2.2.2
  have hF : IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := (hadd p cc δ g hAt).2 hM
  have hg : CoefWf g.ph := hph p cc δ g hAt hp5 hI hM
  have P : ∀ {σ : Type} (i : σ), PtW (Xv i : MvPowerSeries σ ℂ_[p]) := fun i => ptW_X i
  have B : ∀ {σ : Type} {a b : MvPowerSeries σ ℂ_[p]}, PtW a → PtW b → CoefWf (g.be a b) :=
    fun ha hb => coefWf_be HA g hOk hF hg ha hb
  have S : ∀ {σ : Type} {a b : MvPowerSeries σ ℂ_[p]}, PtW a → PtW b → PtW (g.add a b) :=
    fun {σ} {a} {b} ha hb => HA p g hOk hF σ a b ha hb
  refine ⟨B (P (0 : Fin 2)) (P (1 : Fin 2)), ?_, ?_, ?_⟩
  · exact simeqW_of (B (S (P (0 : Fin 3)) (P (1 : Fin 3))) (P (2 : Fin 3)))
      (coefWf_add (B (P (0 : Fin 3)) (P (2 : Fin 3))) (B (P (1 : Fin 3)) (P (2 : Fin 3))))
      (hbi p cc δ g hAt).1
  · exact simeqW_of (B (P (0 : Fin 3)) (S (P (1 : Fin 3)) (P (2 : Fin 3))))
      (coefWf_add (B (P (0 : Fin 3)) (P (1 : Fin 3))) (B (P (0 : Fin 3)) (P (2 : Fin 3))))
      (hbi p cc δ g hAt).2
  · intro α hα
    have h1 : PtW (g.mulBy α.1 (Xv 0) : MvPowerSeries (Fin 2) ℂ_[p]) :=
      HM p g hOk α.1 (hend p cc δ g hAt hp5 hI hM α hα) (Fin 2) _ (P 0)
    have h2 : PtW (g.mulBy α.2 (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) :=
      HM p g hOk α.2 (hend p cc δ g hAt hp5 hI hM α.swap (hs p g.lam α hα)) (Fin 2) _ (P 1)
    exact simeqW_of (B h1 (P (1 : Fin 2))) (B (P (0 : Fin 2)) h2) (hconj p cc δ g hAt (by omega) α hα)

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
section
namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

theorem dual_pair_isometry (D : D7) : IsometryOntoDualFrames D := fun N nu => isometry_dual_pair (Bool × HH D) N nu

theorem isoFun_holds (D : D7) : isoFun D := fun N N' nu s Θ => isometry_function_v (Bool × HH D) D.what₂.Tau (tauPl D) N N' nu s Θ

theorem isoScale_holds (D : D7) : isoScale D := fun N N' nu c s Θ φ => isometry_scaling (Bool × HH D) D.what₂.Tau (tauPl D) N N' nu c s Θ φ

theorem inverse_metric_isometry (D : D7) : InducedNormInvariantMetric D := fun N nu => isometry_invariant_metric (Bool × HH D) N nu

theorem scal_holds (D : D7) : scal D := fun N N' s s' Qp dg hH y' => scalar_degree D.what₂.Tau N N' s s' Qp dg hH y'

theorem isoB_holds (D : D7) : isoB D :=
  fun N N' nu s Θ φ Q hQ y' => isometry_derivative_bound (Bool × HH D) D.what₂.Tau (tauPl D) N N' nu s Θ φ Q hQ y'

theorem wwCB_holds (D : D7) : wwCB D := fun k _ N nu y => cauchy_binet_minors (Bool × HH D) k N nu y

theorem wwKt_holds (D : D7) : wwKt D := fun N0 N1 nu I => minor_expansion (Bool × HH D) N0 N1 nu I

theorem ww_holds (D : D7) : ww D :=
  fun l _ N0 N1 nu Th ph Q hQ y' => minor_identity (Bool × HH D) l N0 N1 nu Th ph Q hQ y'

theorem wwEv_holds (D : D7) : wwEv D := fun l _ N0 N1 nu Th x I => minor_evaluation (Bool × HH D) l N0 N1 nu Th x I

theorem wwInj_holds (D : D7) : wwInj D :=
  fun l _ N nu ph hy J => wwInjective_of cauchy_binet_minors (Bool × HH D) l N nu ph hy J

theorem theta_isometry_facts_hold (D : D7) : ConclusionW D :=
  ⟨wwCB_holds D, wwInj_holds D, wwKt_holds D, ww_holds D, wwEv_holds D, inverse_metric_isometry D, dual_pair_isometry D, isoB_holds D, isoFun_holds D,
    isoScale_holds D⟩

end Formalism.MainNotions.GL3Columns
end

