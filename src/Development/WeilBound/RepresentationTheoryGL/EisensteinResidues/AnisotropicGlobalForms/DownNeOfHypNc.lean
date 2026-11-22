import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.DmOfHyp
import Development.AutomorphicSpectrum.PublishedTheorems.SiegelWeil₂.RegularisedSiegelWeilFirstTermIdentity2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0491
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0510
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0324
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0531
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFSingleOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.ZetaEqIntegralIntegrandNc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0787
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0534
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0476
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0596
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0420
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Exh.Top

variable {D : D7}

theorem fockVec_of_vac_nc {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A H : HSp D} {sA : RealMat A} {sH : RealMat H}
    {f : WO A H → ℂ} (hf : IsThetaFunO ψ A H f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO (sA τ) (sH τ)) f) : IsFockVec ψ θ A H sA sH f := by
  refine ⟨hf, 1, fun l hl => ?_⟩
  match l, hl with
  | [p], _ => exact hv p.1 p.2

theorem sphFun_of_param_nc {V : HSp D} {Λ : Lat V} {Sf : Finset (FinPl D)} {f : GA D V → ℂ}
    {B : GlobalTheory.LFun.Fam D.host.E} (hf : GlobalTheory.LFun.IsParamFun D.sp.cm.sig V.gram Λ (Sf : Set (FinPl D)) f B) :
    SphFun V Λ Sf f := by
  intro v hv k hk g
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hx := (hf v (by simpa using hv) w hw).mem_fixed
  have := congrFun (hx ⟨k, hk⟩) g
  simpa [GlobalTheory.PRep.rightReg, LinearMap.funLeft] using this

end GlobalTheory.Core.Rk.Exh.Top

end
