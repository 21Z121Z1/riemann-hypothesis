import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0495
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0223
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0516
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0517
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0283
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0288
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0514
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPair
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem unrAt_inv_of_unrAt {D : D7} {χ : (AE D)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : GlobalTheory.LFun.UnrAt χ w) : GlobalTheory.LFun.UnrAt χ⁻¹ w := by
  intro x hx
  have := h x hx
  simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv] at this ⊢
  rw [this, inv_one]

theorem isHeckeChar_inv_sph {D : D7} {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ := by
  refine ⟨?_, fun x => ?_⟩
  · have : (χ⁻¹ : (AE D)ˣ →* Circle) = fun x => (χ x)⁻¹ := rfl
    rw [this]; exact h.1.inv
  · rw [MonoidHom.inv_apply, h.2 x, inv_one]

set_option maxHeartbeats 1000000 in

theorem sphFactor_of_weilRepresentationUnitaryPair (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) (D : D7) : SphFactor D := by
  intro ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU v hv s
  obtain ⟨omh, homh⟩ := GlobalTheory.T.exists_weilDatum_hermitianSpaceDoubled hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ A B χA χB om omh hP.weil homh
  have hCC := GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient D ψ A B χA χB om omh hP.weil hTC ν 𝓕 hP.covol
  have hδ := (hTC Φ₁ Φ₂ hΦ₁ hΦ₂).1
  have hco := (hCC Φ₁ Φ₂ hΦ₁ hΦ₂).2
  have hlaw := GlobalTheory.T.siegelWeilSection_degeneratePrincipalSeries_law hW D ψ A B χB omh homh ν 𝓕 hP.covol _ hδ
  have hvac := GlobalTheory.T.doubledTheta_vector_fixed_unramified_stabilizer D ψ A B χB omh homh LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU v hv
  haveI : Submodule.IsLattice D.host.E LA := hU.sdA.1
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (KAd D.sp.cm.sig (dblSp A).gram LA a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A LA a hU.sdA hP.maj
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hK : IsCompact (KAd D.sp.cm.sig (dblSp A).gram LA a : Set (GA D (dblSp A))) := isCompact_KAd (isCMExt_host D)
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : GA D (dblSp A) → ℂ, Ψ = fun g => swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) g *
      npow (hgtAd D.sp.cm.sig (dblSp A).gram LA a g) (s - sZero A B) := ⟨_, rfl⟩
  have hw : ∀ g : GA D A, wcoef om ν 𝓕 Φ₁ Φ₂ g * npow (hgtL A LA a g) (s - sZero A B) = Ψ (io A (g, 1)) := by
    intro g
    simp only [hΨdef, wcoef, hgtL, hco g]
  have hΨlaw : ∀ (p : siegelH _ D.sp.cm.sig (dblSp A).gram) (g : GA D (dblSp A)),
      Ψ ((p : GA D (dblSp A)) * g) = (χB⁻¹ (aH _ D.sp.cm.sig (dblSp A).gram p) : Circle) *
        npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) * Ψ g := by
    intro p g
    simp only [hΨdef]
    have hleft : hgtAd D.sp.cm.sig (dblSp A).gram LA a ((p : GA D (dblSp A)) * g) =
        absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p) * hgtAd D.sp.cm.sig (dblSp A).gram LA a g :=
      hI.hgtH_left continuous_absE hK p g
    have hr : npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) =
        npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (sZero A B + (A.rank : ℂ) / 2) *
          npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (s - sZero A B) := by
      rw [← npow_add (hom_pos (absE D.host.F D.host.E) (aH _ D.sp.cm.sig (dblSp A).gram p))]
      congr 1; ring
    rw [hlaw p g, hleft, npow_mul, hr]
    ring
  have hΨright : ∀ g, ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v,
      Ψ (g * emb D.sp.cm.sig (dblSp A).gram v k) = Ψ g := by
    intro g k hk
    simp only [hΨdef]
    have hright : hgtAd D.sp.cm.sig (dblSp A).gram LA a (g * emb D.sp.cm.sig (dblSp A).gram v k) =
        hgtAd D.sp.cm.sig (dblSp A).gram LA a g := hI.hgtH_right continuous_absE hK g (emb_mem_KAd hk)
    rw [hright]
    congr 1
    simp only [swSec]
    rw [show ((g * emb D.sp.cm.sig (dblSp A).gram v k, (1 : GA D B))) =
      (g, 1) * (emb D.sp.cm.sig (dblSp A).gram v k, 1) by simp, map_mul, Module.End.mul_apply, hvac k hk]
  have hunr : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χB⁻¹ w := by
    intro w hw'
    refine unrAt_inv_of_unrAt (hU.unr w ?_)
    intro hmem
    exact hv (by simpa [GlobalTheory.LFun.above, hw'] using hmem)
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_unique_spherical_doubling_section_unramified D A LA hU.sdA χB⁻¹ (isHeckeChar_inv_sph homh.hecT) v hunr s
  have huniq := hφ.2
  refine ⟨φ, hφ.1, fun x hx y => ?_⟩
  have hx' : proj D.sp.cm.sig (dblSp A).gram v (io A (x, 1)) = 1 := by
    rw [io, proj_ioH, hx, map_one, ioH_one]
  have hl : ∀ (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram) (g : Gv (dblSp A) v),
      Ψ (emb D.sp.cm.sig (dblSp A).gram v (p * g) * io A (x, 1)) =
        charAt χB⁻¹ v (aH _ D.sp.cm.sig (dblSp A).gram p) *
          npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) *
          Ψ (emb D.sp.cm.sig (dblSp A).gram v g * io A (x, 1)) := by
    intro p g
    rw [map_mul, mul_assoc, ← coe_embP, hΨlaw, aH_embP, absE_ideleAt]
    rfl
  have hr : ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v, ∀ g : Gv (dblSp A) v,
      Ψ (emb D.sp.cm.sig (dblSp A).gram v (g * k) * io A (x, 1)) =
        Ψ (emb D.sp.cm.sig (dblSp A).gram v g * io A (x, 1)) := by
    intro k hk g
    rw [map_mul, mul_assoc, (commute_emb D.sp.cm.sig (dblSp A).gram k hx').eq, ← mul_assoc, hΨright _ k hk]
  have key := huniq (fun g => Ψ (emb D.sp.cm.sig (dblSp A).gram v g * io A (x, 1))) hl hr (ioAt A v y)
  simp only [map_one, one_mul] at key
  rw [hw, hw, ← key, ioAt, emb_ioH, io, ← map_mul, Prod.mk_mul_mk, map_one, one_mul,
    (commute_emb D.sp.cm.sig A.gram y hx).eq]

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingWittTowerReduction
section
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
namespace GlobalTheory.Core.Rk.ResKill

theorem dblInt_smul_left {D : D7} {V : HSp D} {μ : (AE D)ˣ →* Circle} {m : Measure (GA D V)} (c : ℂ)
    (E : GA D (dblSp V) → ℂ) (f : GA D V → ℂ) :
    GlobalTheory.Eis.dblInt V μ m (c • E) f f = c * GlobalTheory.Eis.dblInt V μ m E f f := by
  have h := GlobalTheory.Eis.dblInt_smul (V := V) (μ := μ) (m := m) (E := E) (f₁ := f) (f₂ := f) c 1 1
  simpa using h

theorem res_killed : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → ∀ (B W : HSp D) (t : ℕ) (_ : HypDec B W t), HSpace.SigOK B → HSpace.SigOK W → 0 < W.rank → 0 < t → A.rank = W.rank + t → ∀ (χ : (AE D)ˣ →* Circle) (omB : WRep (dblSp A) B) (omW : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) B 1 χ omB → IsWeilDatumO ψ (dblSp A) W 1 χ omW → ∀ ν 𝓕, IsCovolOne (ratL B A) ν 𝓕 → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omW m u → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IsKFinVec omB (Khat A a) φ → GlobalTheory.Eis.EisPoleLE A (flat A a (swSec A B omB ν 𝓕 φ) (sZero A B)) (sZero A B) 1 ∧ ∃ E₁, GlobalTheory.Eis.EisCoeffAt A (flat A a (swSec A B omB ν 𝓕 φ) (sZero A B)) (sZero A B) (-1) E₁ ∧ GlobalTheory.Eis.dblInt A χ⁻¹ m E₁ (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  intro hPr D ψ θ A cA a hDef h2 B W t d hsB hsW hW ht hA χ omB omW hWB hWW ν 𝓕 hcov m hm u hu hinv hK φ hφ hKφ
  obtain ⟨b, hb⟩ := GlobalTheory.RegSW.Model.exists_isMaj B
  obtain ⟨νK, hνH, hνP⟩ := GlobalTheory.RegSW.Model.exists_haar_Kmax B b
  obtain ⟨μ₁, 𝓕₁, hμ₁⟩ := GlobalTheory.MixModel.exists_isCovolOne D t (dblSp A).rank
  have hrk := d.rank_add
  have hIwA : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a hDef.maj
  have hIwB : HasIw d (Kmax B b) := GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D B W t d b h2 hb
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hPr D ψ A B W t d (by omega) (by omega) hW χ omB omW hWB hWW a b hDef.maj hb hIwA hIwB
    ν 𝓕 hcov μ₁ 𝓕₁ hμ₁ νK hνH hνP Measure.haar inferInstance
  have hproj : ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IsThetaFunO ψ (dblSp A) B (projK omB νK φ) := fun φ h => (hP1 φ h).1
  have hφ' : IsThetaFunO ψ (dblSp A) W (ikeda ψ d μ₁ 𝓕₁ (projK omB νK φ)) := (hP1 _ (hproj φ hφ)).2
  have hKφ' : IsKFinVec omW (Khat A a) (ikeda ψ d μ₁ 𝓕₁ (projK omB νK φ)) :=
    (GlobalTheory.T.theta_majorant_average_identity D ψ (dblSp A) B W t d 1 χ omB omW hWB hWW b hb νK hνP μ₁ 𝓕₁ hμ₁ hproj).2 (Khat A a) φ hφ hKφ
  refine ⟨hP2 φ hφ hKφ, ?_⟩
  obtain ⟨-, hWitt⟩ := GlobalTheory.T.majorant_exists_and_witt_decomposition D W hsW
  rcases hWitt with hAn | ⟨W₀, r', d₀, hAn₀, hr'⟩
  · obtain ⟨hconv, κ, -, hE⟩ := hP3 hAn
    refine ⟨_, hE φ hφ hKφ, ?_⟩
    rw [dblInt_smul_left, GlobalTheory.T.theta_killing_implies_vanishing D ψ θ A cA a hDef W χ omW hWW m Measure.haar hm inferInstance u hu hinv hK hconv _ hφ'
      hKφ', mul_zero]
  · obtain ⟨b', hb'⟩ := GlobalTheory.RegSW.Model.exists_isMaj W
    have hIw₀ : HasIw d₀ (Kmax W b') := GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D W W₀ r' d₀ b' h2 hb'
    obtain ⟨hAux, hReg, κ, -, hE⟩ := hP4 W₀ r' d₀ hAn₀ hr' b' hb' hIw₀ θ hDef.inf
    obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
    obtain ⟨zG, zH, P, hzP⟩ := hReg τ
    obtain ⟨hRI, hE'⟩ := hE τ zG zH P hzP
    refine ⟨_, hE' φ hφ hKφ, ?_⟩
    rw [dblInt_smul_left, GlobalTheory.T.theta_kill_witt_decomposition D ψ θ A cA a hDef W W₀ r' d₀ b' χ omW hWW m Measure.haar hm inferInstance u hu hinv hK
      hAux τ zH P hzP.2.2.2 hRI _ hφ' hKφ', mul_zero]

end GlobalTheory.Core.Rk.ResKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralElementHomotheticGluedCores
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.CoreHomothety

variable {D : D7}

theorem mulVec_mem_idAt {P : GlobalTheory.FinPl.Pl D → Prop} {m l : ℕ} (X : Matrix (Fin m) (Fin l) (AE D))
    {y : Fin l → AE D} (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (X *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  have h1 := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  have h2 : mt S g *ᵥ (mt S g⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, show mt S g * mt S g⁻¹ = mt S (g * g⁻¹) from rfl, mul_inv_cancel, mt_one,
      Matrix.one_mulVec]
  rw [h2] at h1
  exact h1.symm

theorem moves_trans {S : HSp D} {g h : GA D S} {L M N : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h1 : Moves S g L M P)
    (h2 : Moves S h M N P) : Moves S (h * g) L N P := by
  intro y hy
  rw [h1 y hy, h2 _ (mulVec_mem_idAt _ hy), Matrix.mulVec_mulVec]
  rfl

theorem moves_conj {S : HSp D} {h : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (hM : Moves S h L M P)
    (a : GA D S) : Moves S (h * a * h⁻¹) M M P ↔ Moves S a L L P := by
  constructor
  · intro H
    have e : h⁻¹ * (h * a * h⁻¹ * h) = a := by group
    have := moves_trans (moves_trans hM H) (moves_inv hM)
    rwa [e] at this
  · intro H
    have := moves_trans (moves_trans (moves_inv hM) H) hM
    rwa [← mul_assoc] at this

theorem sMoves_trans {S : HSp D} {c : AE D} {g h : GA D S} {L M N : Lat S} {v : GlobalTheory.FinPl.Pl D}
    (hS : SMoves S c g L M v) (hM : Moves S h M N (· = v)) : SMoves S c (h * g) L N v := by
  intro y hy
  rw [hS y hy, hM (c • (mt S g *ᵥ y)) (fun i => Ideal.mul_mem_left _ c (mulVec_mem_idAt _ hy i)),
    Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rfl

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem mem_gluedS_smul (q : GlobalTheory.LatPair.Unif k) {P P' : GlobalTheory.LatPair.Pair k n} {g : GL n k} {s : k} (hs : s ≠ 0)
    (hg : g.val = s • (1 : Matrix n n k)) (hP : P' = g • P) (u : n → k) (t : Fin 1 → k) :
    Sum.elim u t ∈ GlobalTheory.LatPair.gluedS q 1 P.ker P.vec ↔ Sum.elim (s • u) t ∈ GlobalTheory.LatPair.gluedS q 1 P'.ker P'.vec := by
  have hgx : ∀ x : n → k, g • x = s • x := fun x => by
    show g.val *ᵥ x = s • x
    rw [hg, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hgi : ∀ x : n → k, g⁻¹ • x = s⁻¹ • x := fun x => by
    have : x = g • (s⁻¹ • x) := by rw [hgx, smul_smul, mul_inv_cancel₀ hs, one_smul]
    conv_lhs => rw [this]
    rw [inv_smul_smul]
  have hker : ∀ x : n → k, x ∈ P'.ker ↔ s⁻¹ • x ∈ P.ker := fun x => by
    rw [hP, GlobalTheory.LatPair.Pair.smul_ker, GlobalTheory.LatPair.mem_smul_iff, hgi]
  have hvec : P'.vec - s • P.vec ∈ P'.ker := by
    have h1 := P.hasVal_vec.gl_smul g
    rw [← hP, hgx] at h1
    have := GlobalTheory.LatPair.Pair.sub_vec_mem h1
    rw [← neg_sub]
    exact neg_mem this
  rw [GlobalTheory.LevelUnfold.mem_gluedS, GlobalTheory.LevelUnfold.mem_gluedS]
  refine exists_congr fun σ => and_congr_left' ?_
  have e1 : (Sum.elim u t : n ⊕ Fin 1 → k) ∘ Sum.inl = u := rfl
  have e2 : (Sum.elim (s • u) t : n ⊕ Fin 1 → k) ∘ Sum.inl = s • u := rfl
  rw [e1, e2]
  have e3 : s • u - σ • P'.vec = s • (u - σ • P.vec) - σ • (P'.vec - s • P.vec) := by
    simp only [smul_sub]
    rw [smul_comm σ s P.vec]
    abel
  rw [e3, Submodule.sub_mem_iff_left _ (Submodule.smul_mem _ σ hvec), hker, smul_smul, inv_mul_cancel₀ hs, one_smul]

theorem emb_central_frame {p : SplitPt D k} {S A L : HSp D} {o : OrthDec S A L} {ζ : Fin L.rank → D.host.E}
    {β : GlobalTheory.FinPl.Frame p A n} {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} (hsum : IsSumFrame o ζ β β₀) {a : GA D A}
    {c' : AE D} (ha : mt A a = c' • (1 : Matrix (Fin A.rank) (Fin A.rank) (AE D))) (y : n ⊕ Fin 1 → k) :
    (mt S (o.emb (a, 1))).map p.pr *ᵥ (β₀.b *ᵥ y) =
      β₀.b *ᵥ Sum.elim (fun i => p.pr c' * y (Sum.inl i)) (fun j => y (Sum.inr j)) := by
  have h3 : (mt A a).map p.pr = β.b * (p.pr c' • (1 : Matrix n n k)) * β.b' := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, β.bb', ha]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have e := GlobalTheory.FinPl.Comm.block_calc p.pr _ _ _ _ _ _ _ (o.emb_jA a 1) (GlobalTheory.FinPl.Comm.emb_vecB o ζ a) h3 β.b'b
  rw [← hsum] at e
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  congr 1
  ext (i | j) <;> simp [Matrix.fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

end Split

theorem exists_central_sMoves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M M' : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k) (P : GlobalTheory.LatPair.Pair k n) (a₀ : GA D A), 3 ≤ Fintype.card n → IsSumFrame o ζ β β₀ → IsSelfDualC S M → IsSelfDualC S M' → β₀.IsLat M (GlobalTheory.LatPair.gluedS q 1 P.ker P.vec) → μ ≠ 0 → LineAt (vecB o ζ) μ M' p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → (∀ a ∈ grpAt A (· = p.v), Moves S (o.emb (a, 1)) M M (· = p.v) ↔ Moves S (o.emb (a₀ * a * a₀⁻¹, 1)) M' M' (· = p.v)) → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' p.v := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M M' μ T q P a₀ hn hsum hM hM' hlat hμ hline hnorm hval hconj
  obtain ⟨M'', hsd'', hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S M' hM').1 (o.emb (a₀, 1))⁻¹
  have hmv' : Moves S (o.emb (a₀, 1)) M'' M' (· = p.v) := by
    have := moves_inv (hmv (· = p.v))
    rwa [inv_inv] at this
  have hline'' : LineAt (vecB o ζ) μ M'' p.v := by
    intro b hb
    rw [← hline b hb, hmv' (b • ratV (vecB o ζ)) (fun i => Ideal.mul_mem_right _ _ hb), Matrix.mulVec_smul,
      GlobalTheory.FinPl.Comm.emb_vecB]
  obtain ⟨P', hP'⟩ := GlobalTheory.T.selfDualCore_component_gluedAlongPair D k p S A L o ζ n β β₀ M'' μ T q hsum hsd'' hμ hline'' hnorm hval
  have hm : p.pr (incA D μ) ≠ 0 := by
    intro h0
    have h1 : p.pr (incA D μ * incA D μ⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ hμ, map_one, map_one]
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hW : GluedW β₀ M q 1 P := fun x => by
    have e : (Sum.elim (fun a => x (Sum.inl a)) (fun j => 1 * x (Sum.inr j)) : n ⊕ Fin 1 → k) = x := by
      ext (i | i) <;> simp
    rw [e]
    exact (hlat x).symm
  have hstab : ∀ g : GL n k, g • P = P ↔ g • P' = P' := fun g => by
    rw [← GlobalTheory.T.orthogonalEmbedding_keeps_gluedCore_iff_fixes_pair D k p S A L o ζ n β β₀ M q 1 P hsum hM one_ne_zero hW g,
      ← GlobalTheory.T.orthogonalEmbedding_keeps_gluedCore_iff_fixes_pair D k p S A L o ζ n β β₀ M'' q _ P' hsum hsd'' hm hP' g,
      hconj _ (GlobalTheory.FinPl.FrameLat.gl_mem_grpAt β g)]
    have e : o.emb (a₀ * β.gl g * a₀⁻¹, 1) = o.emb (a₀, 1) * o.emb (β.gl g, 1) * (o.emb (a₀, 1))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, inv_one, mul_one, mul_one]
    rw [e, moves_conj hmv']
  obtain ⟨g, s, hs, hg, hPP⟩ := GlobalTheory.T.latticeResiduePair_eq_scalar_of_same_stabilizer k n P P' hn hstab
  obtain ⟨c, hc, hcpr⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p (p.pr (incA D μ))⁻¹ (inv_ne_zero hm)
  obtain ⟨c', hc', hc'pr⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p (s * p.pr (incA D μ)) (mul_ne_zero hs hm)
  obtain ⟨a, hcen, hamt⟩ := GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D A p.v c' hc'
  refine ⟨a, c, hcen, hc, ?_⟩
  have key : SMoves S c (o.emb (a, 1)) M M'' p.v := by
    refine GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D k p S M M'' c (o.emb (a, 1)) hM hsd'' hc fun x => ?_
    have hx : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]
    rw [hx, emb_central_frame hsum hamt, ← Matrix.mulVec_smul, hW, hP']
    refine (mem_gluedS_smul q hs hg hPP _ _).trans (iff_of_eq ?_)
    congr 1
    ext (i | j)
    · simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul, hcpr, hc'pr]
      field_simp
    · simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, hcpr]
      field_simp
  have e : o.emb (a₀ * a, 1) = o.emb (a₀, 1) * o.emb (a, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e]
  exact sMoves_trans key hmv'

end GlobalTheory.Core.Mi.LatMatch.CoreHomothety
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroJetScaleTrueColumnsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_jetScale_trueColumns : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∃ s, JetS I l Z ψ θ s := by
  first | exact @GlobalTheory.AdForm.JetScales.exists_jetS | exact GlobalTheory.AdForm.JetScales.exists_jetS | (intros; apply GlobalTheory.AdForm.JetScales.exists_jetS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceModelExtensionLineLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModelExtend

theorem isLattice_span {D : D7} {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) :
    Submodule.IsLattice D.host.E (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) := by
  refine ⟨Submodule.fg_span_singleton ζ, ?_⟩
  have h0 : ζ ≠ 0 := fun h0 => h.2 (by simp [h0])
  rw [Submodule.span_span_of_tower]
  have hr : Module.finrank D.host.E (Fin L.rank → D.host.E) = 1 := by simp [h.1]
  exact (finrank_eq_one_iff_of_nonzero ζ h0).1 hr

open GlobalTheory.LocMod in

theorem exists_placeModel_ext : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S L'' : HSp D) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : GlobalTheory.LocMod.Frame k S.rank n) (FL'' : GlobalTheory.LocMod.Frame k L''.rank Unit) (TL : SB (Matrix Unit n k) →ₗ[ℂ] (WO S L'' → ℂ)), (GlobalTheory.LocMod.Place.ofSplitPt p).IsModel ψ FS FL'' TL → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ ∀ Φ, T₃ (GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FS FL'' Φ) = TL Φ := by
  intro D k _ _ _ _ p ψ hψ hU S L'' ζ₀ hζ LS hLS n _ _ FS FL'' TL hTL
  classical
  set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP
  set Λ := latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v) with hΛ
  obtain ⟨hAo, hAc⟩ := GlobalTheory.T.splitPlace_homLattice_completion_openCompact D k p S L'' LS (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀}) hLS.1
    (isLattice_span hζ) Unit n FS FL''
  have hinj : Function.Injective (Witness.ext P FS FL'') := by
    intro Φ Ψ h
    apply Subtype.ext; funext x
    have := congrFun h (P.up FS FL'' x)
    rwa [Witness.ext_apply, Witness.ext_apply, if_pos (Witness.up_half P FS FL'' x),
      if_pos (Witness.up_half P FS FL'' x), Witness.down_up] at this
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Witness.ext P FS FL'') (LinearMap.ker_eq_bot.2 hinj)
  set T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ) := TL ∘ₗ G with hT₃d
  have hT₃ : ∀ Φ, T₃ (Witness.ext P FS FL'' Φ) = TL Φ := fun Φ => by
    change TL (G (Witness.ext P FS FL'' Φ)) = TL Φ
    rw [← LinearMap.comp_apply G, hG, LinearMap.id_apply]
  have hsb : ∀ Φ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Unit n k), Witness.ext P FS FL'' Φ' = Φ :=
    GlobalTheory.T.exists_schwartzBruhat_extByZero_of_splitPlaceHalf D k P S L'' Unit n FS FL'' Λ hAo hAc
  generalize hA : (Λ.comap (Witness.upH P FS FL'') : AddSubgroup (Matrix Unit n k)) = A at hAo hAc
  have hcl : IsClopen (A : Set (Matrix Unit n k)) := ⟨A.isClosed_of_isOpen hAo, hAo⟩
  let Φ₀ : SB (Matrix Unit n k) := ⟨(A : Set (Matrix Unit n k)).indicator 1,
    (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩
  have e1 : Witness.ext P FS FL'' Φ₀ = halfInd p.e Λ := by
    funext t
    rw [Witness.ext_apply, halfInd]
    change (if IsHalf p.e t then _ else _) = _
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      change (A : Set (Matrix Unit n k)).indicator 1 _ = _
      rw [Set.indicator_apply, ← hA]
      refine if_congr ?_ rfl rfl
      change P.up FS FL'' (P.down FS FL'' t) ∈ Λ ↔ _
      rw [Witness.up_down P FS FL'' ht, and_iff_left ht]
    · rw [if_neg ht, if_neg fun h => ht h.2]
  refine ⟨TL Φ₀, T₃, hTL.theta Φ₀, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, hT₃⟩
  · obtain ⟨Φ', rfl⟩ := hsb Φ hΦ
    let Φ'' : SB (Matrix Unit n k) := ⟨fun s => Φ'.1 (s + P.down FS FL'' x),
      Φ'.2.1.comp_continuous (continuous_add_right _), Φ'.2.2.comp_homeomorph (Homeomorph.addRight _)⟩
    have e2 : (fun t => Witness.ext P FS FL'' Φ' (t + x)) = Witness.ext P FS FL'' Φ'' := by
      funext t
      rw [Witness.ext_apply, Witness.ext_apply, Witness.down_add]
      exact if_congr (Witness.half_add hx) rfl rfl
    rw [e2, hT₃, hT₃, hTL.trans (P.down FS FL'' x) Φ' Φ'' (fun t => rfl), Witness.up_down P FS FL'' hx]
  · obtain ⟨Φ', rfl⟩ := hsb Φ hΦ
    let Φ'' : SB (Matrix Unit n k) := ⟨fun s => ψ (symplO S L'' (P.up FS FL'' s) y) * Φ'.1 s,
      GlobalTheory.T.schwartzBruhat_mul_conjugateHalf_character_splitPlace D k P ψ hψ S L'' Unit n FS FL'' y hy Φ'.1 Φ'.2⟩
    have e2 : (fun t => ψ (symplO S L'' t y) * Witness.ext P FS FL'' Φ' t) = Witness.ext P FS FL'' Φ'' := by
      funext t
      rw [Witness.ext_apply, Witness.ext_apply]
      split_ifs with ht
      · change _ = ψ (symplO S L'' (P.up FS FL'' (P.down FS FL'' t)) y) * _
        rw [Witness.up_down P FS FL'' ht]
      · rw [mul_zero]
    rw [e2, hT₃, hT₃, hTL.modul y hy Φ' Φ'' (fun t => rfl)]
  · rw [one_smul, ← e1, hT₃]

end GlobalTheory.ModelExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulasStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas : ∀ (D : D7) (A V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A V)) (𝓨 : Set (WO A V)), IsCovolOne (ratL V A) ν 𝓨 → ∀ ω : G D A.rank →* Module.End ℂ (schwartzA θ V.rank A.rank), IsWeilSch ψ χ θ V ν ω → ∃ (ψ₀ : AddChar (AF D.host.F) ℂ) (μ : D.host.E) (lam : D.host.F) (κ : GA D (dblSp A) ≃* G D A.rank) (omh : GA D (dblSp A) × GA D V →* Module.End ℂ (WO (dblSp A) V → ℂ)), IsStdChar D ψ₀ (-1) ∧ IsSkew μ ∧ algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ ∧ ψ = shift ψ₀ lam ∧ IsChart A μ κ ∧ IsWeilDatumO ψ₀ (dblSp A) V 1 χ⁻¹ omh ∧ IsTransport ψ₀ θ A V ν 𝓨 omh κ ω := by
  first | exact @GlobalTheory.StdUnn.SchDatum.exists_datum | exact GlobalTheory.StdUnn.SchDatum.exists_datum | (intros; apply GlobalTheory.StdUnn.SchDatum.exists_datum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZero
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory

theorem coord_first_isotropic_ne_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : 1 ≤ D.R.rS), (fun i : Fin (D.sp.Y 0).rank => X.ιE (X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) i))) ≠ 0 := by
  intro D X h hr hzero
  have hrepr : X.bas.repr (X.eX ⟨0, hr⟩) = 0 := by
    ext j
    have := congrFun hzero (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h).symm j)
    simpa [Formalism.L2.SG.HidaSetting.HidaSetting.eR, Formalism.L2.SG.HidaSetting.HidaSetting.crd,
      Formalism.L2.SG.HidaSetting.crdOf] using this
  have hx : X.eX ⟨0, hr⟩ = 0 := by
    simpa using hrepr
  have hef := X.ef ⟨0, hr⟩ ⟨0, hr⟩
  rw [hx] at hef
  simp at hef

end GlobalTheory
end

