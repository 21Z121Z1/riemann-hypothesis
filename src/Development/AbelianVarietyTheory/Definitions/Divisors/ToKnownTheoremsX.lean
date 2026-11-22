import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesY
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LogResolutionProjectiveLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete

namespace GlobalTheory.CovTop

structure HypothesesXH : Prop where

  toClassicalTheoremsX : HypothesesX

  mb : GlobalTheory.Published.MoretBaillyModel

  arr : GlobalTheory.Published.ArithRiemannRoch

  cube : GlobalTheory.Published.CubeTheorem

  dual : GlobalTheory.Published.DualAbelianScheme

  logres : GlobalTheory.Published.AnalyticLogResolution

  andim : GlobalTheory.Published.AnalyticSetDimension

  conj : GlobalTheory.Published.ConjugateFiltration

  ray : GlobalTheory.Published.RaynaudExtension

  orth : GlobalTheory.Published.GrothendieckOrthogonality

  y : GlobalTheory.CovHt.HypothesesY

  btd : GlobalTheory.Published.BarsottiTateDieudonne

instance : Coe HypothesesXH HypothesesX := ⟨HypothesesXH.toClassicalTheoremsX⟩

theorem HypothesesXH.ks (h : HypothesesXH) : GlobalTheory.Published.ToroidalForFanKS := h.toClassicalTheoremsX.ks

theorem HypothesesXH.lie (h : HypothesesXH) : GlobalTheory.Published.SemiAbelianLieSeminegative := h.toClassicalTheoremsX.lie

theorem HypothesesXH.green (h : HypothesesXH) : GlobalTheory.Published.GreenCuspidal := h.toClassicalTheoremsX.green

theorem HypothesesXH.sep (h : HypothesesXH) : GlobalTheory.Published.PointSeparationPair := h.toClassicalTheoremsX.sep

end GlobalTheory.CovTop
