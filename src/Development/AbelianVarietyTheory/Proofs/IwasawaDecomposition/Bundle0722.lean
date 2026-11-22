import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0709
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0391
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0233
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubspaceTrivialOutsideSplitPlac
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0454
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0401
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpTiedCopy
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.HeightCounting.ExpCopy

open GlobalTheory.Mem.R3.Tr

theorem sig_heq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') {T T' : Type} (hT : T = T')
    {f : T ≃ R.Psi} {f' : T' ≃ R'.Psi} (hf : HEq f f') {t : T} {t' : T'} (ht : HEq t t')
    {x : H.E} {x' : H'.E} (hx : HEq x x') :
    HEq (H.sigmaOf ((f t : R.Psi) : R.GG) x)
      (H'.sigmaOf ((f' t' : R'.Psi) : R'.GG) x') := by
  subst hR; cases hH; subst hT; cases hf; cases ht; cases hx; rfl

section
variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem kEmb_heq (h : CopyTw D D' ι e) {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (b : Bool) {t : D.what₂.Tau}
    {t' : D'.what₂.Tau} (ht : HEq t t') {x : D.host.E} {x' : D'.host.E} (hx : HEq x x') :
    HEq (Formalism.L2.NX.kEmb D i b t x) (Formalism.L2.NX.kEmb D' i' b t' x') := by
  have hσ := sig_heq h.gal.R h.gal.host h.Tau h.eTau ht hx
  have hy : e (Formalism.L2.NX.embEL0 D' (D'.host.sigmaOf ((D'.eTau t' : D'.R.Psi) : D'.R.GG) x')) =
      Formalism.L2.NX.embEL0 D (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x) :=
    Subtype.ext (ι.injective ((h.LL0 _).trans (h.map_embE hσ).symm))
  have := h.sideEmb_heq hi b (Formalism.L2.NX.embEL0 D' (D'.host.sigmaOf ((D'.eTau t' : D'.R.Psi) : D'.R.GG) x'))
  rw [hy] at this
  exact this

theorem side_heq (h : CopyTw D D' ι e) {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (b : Bool) (z : ↥D.LL0) :
    HEq (GlobalTheory.SeriesTie.sideEmb D.ntw i b z) (GlobalTheory.SeriesTie.sideEmb D'.ntw i' b (e.symm z)) := by
  have := h.sideEmb_heq hi b (e.symm z)
  rw [e.apply_symm_apply] at this
  exact this

end

theorem infG_eta {D : D7} {cf : CharFrame D} (hcs : CharSide D cf) (t : D.what₂.Tau) :
    D.naut.infG D.naut.etaT (Formalism.L2.Host.embPsi D.host (D.eTau t)) = {(((1 / 2 : ℚ)) : ℂ)} :=
  (hcs.infG D.naut.etaT (fun _ => 1 / 2) (by rw [hcs.etaT]; exact ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩) (D.eTau t)).1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem core (D : D7) (r : Rest D) (X : NExpTied D) (hpl : HEq D.naut.plGw (overD D r).naut.plGw)
    (hhw : ∀ i j b (t : D.what₂.Tau), 1 ≤ j → j ≤ D.R.m →
      ∃ lam : Fin D.R.nV → ℤ, Formalism.L2.NX.HWAtF (Formalism.L2.NX.cE D) (X.rhoW i j b).dual ((by exact NX.kEmb (overD D r) i b t)) lam)
    (hwt : ∀ i j b (t : D.what₂.Tau) (hj : 1 ≤ j) (hjm : j ≤ D.R.m) (sh : ℂ) (lam : Fin D.R.nV → ℤ),
      (overD D r).naut.infG (overD D r).naut.etaT ((by exact embPsi D.host (D.eTau t))) = {sh} →
      Formalism.L2.NX.HWAtF (Formalism.L2.NX.cE D) (X.rhoW i j b).dual ((by exact NX.kEmb (overD D r) i b t)) lam →
      NG.infOf lam = NG.paramV D.R (D.hc t) ⟨j - 1, by omega⟩ sh) :
    ∃ X' : NExpTied (overD D r), HEq X.tauG X'.tauG ∧ ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hA : NX.AdmTw D i k Q ψ),
      HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA))).QP ∧
      HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA))).DP ∧
      ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : D.nexp.MtV i j b k Q ψ → Formalism.AUTREP.GAf D.host.E D.R.nV → V),
        GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V ρ →
          GlobalTheory.HeightCounting.Reads X' ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA)) ((by exact ε)) V ((by exact ρ)) := by
  cases r
  rename NAut _ => n
  cases n
  dsimp only [overD] at hpl
  cases hpl
  refine ⟨@Formalism.L2.NExpTied.mk (_)
      (U_eq := (X.U_eq))
      (psiU_gen := (X.psiU_gen))
      (psiU_side := (X.psiU_side))
      (psiU_xi := (X.psiU_xi))
      (delU_cont := (X.delU_cont))
      (delU_ine := (X.delU_ine))
      (thU_empty := (X.thU_empty))
      (sgnT := (X.sgnT))
      (sgnT_one := (X.sgnT_one))
      (Wt := (X.Wt))
      (acgWt := (X.acgWt))
      (modWt := (X.modWt))
      (fdWt := (X.fdWt))
      (rhoW := (X.rhoW))
      (rhoW_irr := (X.rhoW_irr))
      (rhoW_alg := (X.rhoW_alg))
      (tauG := (X.tauG))
      (sgnG := (X.sgnG))
      (sgnG_one := (X.sgnG_one))
      (tau_galois_first_character := (X.tau_galois_first_character))
      (mtV := fun x1 x2 x3 x4 x5 x6 x7 x8 x9 => @Formalism.L2.NX.MtVReal.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
        (W := (@NX.MtVReal.W D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (acg := (@NX.MtVReal.acg D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (mod := (@NX.MtVReal.mod D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (fd := (@NX.MtVReal.fd D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (ρ := (@NX.MtVReal.ρ D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (irr := (@NX.MtVReal.irr D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (alg := (@NX.MtVReal.alg D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (bc := (@NX.MtVReal.bc D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (J := (@NX.MtVReal.J D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (χ := (@NX.MtVReal.χ D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (J_open := (@NX.MtVReal.J_open D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (hyp := (@NX.MtVReal.hyp D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP := (@NX.MtVReal.QP D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP_sub := (@NX.MtVReal.QP_sub D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP_cover := (@NX.MtVReal.QP_cover D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP_nconj := (@NX.MtVReal.QP_nconj D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP := (@NX.MtVReal.DP D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP_sub := (@NX.MtVReal.DP_sub D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP_cover := (@NX.MtVReal.DP_cover D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP_nconj := (@NX.MtVReal.DP_nconj D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (sp := (@NX.MtVReal.sp D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (sp_w := (@NX.MtVReal.sp_w D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (redG := (@NX.MtVReal.redG D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (J_mem := (@NX.MtVReal.J_mem D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (chi_eq := (@NX.MtVReal.chi_eq D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (real := (@NX.MtVReal.real D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9))))
      (rhoW_hw := (hhw))
      (rhoW_wt := (hwt)), (HEq.refl X.tauG), fun i j b k Q ψ h1 h2 hA => ⟨?_, ?_, fun ε V _ _ ρ hR => ?_⟩⟩
  · exact (HEq.refl (X.mtV i j b k Q ψ h1 h2 hA).QP)
  · exact (HEq.refl (X.mtV i j b k Q ψ h1 h2 hA).DP)
  · exact (hR)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem expTied_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → CharSide D cf → CharSide D' cf' → ∀ X : NExpTied D, ∃ X' : NExpTied D', (TauTrue X → TauTrue X') ∧ ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (Q' : Finset (PlE D'.host)), HEq Q Q' → ∀ (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), HEq ψ ψ' → ∀ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (h2' : j ≤ D'.R.m) (hA' : NX.AdmTw D' i' k Q' ψ'), ∃ hA : NX.AdmTw D i k Q ψ, HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV i' j b k Q' ψ' h1 h2' hA').QP ∧ HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV i' j b k Q' ψ' h1 h2' hA').DP ∧ ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (ε' : FractionRing (D'.ntw.Ok i' k) →+* ℂ), HEq ε ε' → ∀ (V V' : Type) [aV : AddCommGroup V] [mV : Module ℂ V] [aV' : AddCommGroup V'] [mV' : Module ℂ V'], V = V' → HEq aV aV' → HEq mV mV' → ∀ (r : D.nexp.MtV i j b k Q ψ → Formalism.AUTREP.GAf D.host.E D.R.nV → V) (r' : D'.nexp.MtV i' j b k Q' ψ' → Formalism.AUTREP.GAf D'.host.E D'.R.nV → V'), HEq r r' → GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V r → GlobalTheory.HeightCounting.Reads X' i' j b k Q' ψ' h1 h2' hA' ε' V' r' := by
  intro D D' ι e h cf cf' _ hcs hcs' X
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  have hk : ∀ i b t, Formalism.L2.NX.kEmb D i b t = (by with_unfolding_all exact ((Formalism.L2.NX.kEmb (overD D r) ((by with_unfolding_all exact (i :))) b ((by with_unfolding_all exact (t :)))) :)) := fun i b t =>
    RingHom.ext fun x => (by with_unfolding_all exact (eq_of_heq (α := FractionRing (D.ntw.O i)) (a := Formalism.L2.NX.kEmb D i b t x)
        (a' := (by with_unfolding_all exact ((Formalism.L2.NX.kEmb (overD D r) ((i)) b ((t)) ((x))) : _)))
        ((by with_unfolding_all exact ((kEmb_heq h.cp (i := i) (i' := (i)) (((HEq.refl i))) b (t := t) (t' := (t)) (((HEq.refl t)))
          (x := x) (x' := (x)) (((HEq.refl x)))) : _))) :))
  obtain ⟨X', hτ, hM⟩ := core D r X h.pl
    (fun i j b t h1 h2 => by
      have := X.rhoW_hw i j b t h1 h2
      rw [hk] at this
      exact this)
    (fun i j b t h1 h2 sh lam hsh hw => by
      refine X.rhoW_wt i j b t h1 h2 sh lam ?_ ?_
      · have h3 : ({(((1 / 2 : ℚ)) : ℂ)} : Multiset ℂ) = {sh} := (infG_eta hcs' ((by with_unfolding_all exact (t :)))).symm.trans (c := {sh}) ((by with_unfolding_all exact (hsh :)))
        exact (infG_eta hcs t).trans h3
      · rw [hk]
        exact hw)
  refine ⟨X', fun ⟨τ, hτ'⟩ => ?_, fun i i' hi j b k Q Q' hQ ψ ψ' hψ h1 h2 h2' hA' => ?_⟩
  · have hτ2 : X'.tauG = (by with_unfolding_all exact (X.tauG :)) := (by with_unfolding_all exact ((eq_of_heq (a := X'.tauG) (a' := (by with_unfolding_all exact (X.tauG :))) ((by with_unfolding_all exact (hτ.symm :)))) :))
    refine ⟨fun j kv => (Units.map e.symm.toRingHom.toMonoidHom).comp ((by with_unfolding_all exact ((τ j ((by with_unfolding_all exact (kv :)))) :))), fun i j b kv x h1 h2 => ?_⟩
    rw [hτ2]
    exact (by with_unfolding_all exact ((hτ' ((by with_unfolding_all exact (i :))) j b ((by with_unfolding_all exact (kv :))) ((by with_unfolding_all exact (x :))) h1 ((by with_unfolding_all exact (h2 :)))).trans (eq_of_heq (α := FractionRing (D.ntw.O ((by with_unfolding_all exact (i :)))))
      (a' := (by with_unfolding_all exact ((GlobalTheory.SeriesTie.sideEmb (overD D r).ntw i b (e.symm ((τ j ((kv)) ((x)) : (↥D.LL0)ˣ) : ↥D.LL0))) : _)))
      ((by with_unfolding_all exact ((side_heq h.cp (i := (i)) (i' := i) (((HEq.refl i))) b ((τ j ((kv)) ((x)) : (↥D.LL0)ˣ) : ↥D.LL0)) : _)))) :))
  · cases hi; cases hQ; cases hψ
    refine ⟨(by with_unfolding_all exact (hA' :)), (hM i j b k Q ψ h1 h2 ((by with_unfolding_all exact (hA' :)))).1, (hM i j b k Q ψ h1 h2 ((by with_unfolding_all exact (hA' :)))).2.1, ?_⟩
    intro ε ε' hε V V' aV mV aV' mV' hV haV hmV ρ ρ' hρ hR
    subst hV; cases haV; cases hmV; cases hε; cases hρ
    exact (by with_unfolding_all exact (((hM i j b k Q ψ h1 h2 ((by with_unfolding_all exact (hA' :)))).2.2 ε V ρ hR) :))

end GlobalTheory.HeightCounting.ExpCopy

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinTypRowsExistsIsLocSAlt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLocalRows2

open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult

set_option maxHeartbeats 1000000 in

theorem finTyp_rows_exists_isLocS : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → D.host.F = maximalRealSubfield D.host.E → ∀ (σ : D.what₂.FT) (s : SplitPlace D.host.E), ∃ τ, GlobalTheory.HeightCounting.IsLocS (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S s τ := by
  intro hH hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ _ _ σ s
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  set π := principalLevelFrame.rowRepR R.θ (Y.eFT σ) with hπ
  have hne : isotIn (D := D) (actM Y.PY (R.MY 0)) (Minf R.θ Y.PY (R.MY 0)) (FinTyp.conjT π) ≠ ⊥ := by
    intro h
    apply hb
    unfold isotE isotL
    rw [h, inf_bot_eq]
  have hM := hP.char.base.models
  have hθ : IsInfFam R.θ := hM.inf
  have hSig : (Yc D 0).SigOK := D.sp.Y_sig 0
  have hcc := GlobalTheory.T.unitary_congruence_conj_contains_congruence D.host.E D.R.r
  have hfd : ∀ j, j < D.R.m → (R.νY A3.A.μ0 j).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D j)) (R.fdY A3.A.μ0 j) (R.νY A3.A.μ0 j) := by
    intro j hj
    by_cases h : j + 1 < D.R.m
    · have := hM.νY A3.A.μ0 j h
      exact ⟨this.1.1, this.2⟩
    · obtain rfl : j = D.R.m - 1 := by omega
      have := hM.νY' A3.A.μ0
      exact ⟨this.1.1, this.2⟩
  obtain ⟨hHaar, hFD⟩ := hfd 0 Y.hm
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  have hHA : HCAll D := fun V _ S θ M J χ =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := R.MY 0) (θ := R.θ) (R.νY A3.A.μ0 0)
    (R.fdY A3.A.μ0 0) Y.PY hSA hSig hθ hHaar hFD
  obtain ⟨B', h1, h2, h3, h4⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r _ (actM Y.PY (R.MY 0))
    (Minf R.θ Y.PY (R.MY 0)) (ipM (R.MY 0) (R.νY A3.A.μ0 0) (R.fdY A3.A.μ0 0)) hlin hherm hpos
    (fun h x hx => GlobalTheory.FinTypesRows.minf_stable Y.PY hcc h hx)
    (fun h x hx y hy => GlobalTheory.T.schur_pairing_invariant_under_standard_group D (Yc D 0) _ R.θ (R.MY 0) D.R.r Y.PY (R.νY A3.A.μ0 0) (R.fdY A3.A.μ0 0) hSA hSig hθ
      hHaar hFD h x hx y hy) (FinTyp.conjT π) hne
  obtain ⟨B, k1, k2, k3, k4⟩ := GlobalTheory.RowLocalRows.form_of_conjT π B' h1 h2 h3 h4
  have hadm : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ Minf R.θ Y.PY (R.MY 0) ∧
      ∀ κ, NG.Cong D.host.E D.R.r N κ → actM Y.PY (R.MY 0) κ x = x}) := fun N hN =>
    GlobalTheory.FinTypesRows.minf_adm (M := R.MY 0) Y.PY hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open Y.PY Y.stdPsi.1) N hN
  have hfix : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ π.S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f}) := fun N hN =>
    GlobalTheory.RowLocalRows.fixed_fd_of_conjT π N (GlobalTheory.RowLocalRows.fixed_fd_of_isotIn _ _ hadm _ hne N hN)
  obtain ⟨W, hWS, hW0, hst, hirr⟩ := GlobalTheory.T.exists_irreducible_subspace_trivialOutside_splitPlace D.host.E D.R.r π B k1 k2 k3 k4 hfix s
  exact GlobalTheory.RowLocal.isLocS_of_irr π s W hWS hW0 hst hirr

end GlobalTheory.RowLocalRows2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteBilinFormAbsLe
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

theorem finite_bilinForm_abs_le (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (B : X → X → ℤ) :
    {x : LinearMap.BilinForm ℤ X | ∀ a b, |x a b| ≤ B a b}.Finite := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  let f : LinearMap.BilinForm ℤ X → (s × s → ℤ) := fun x p => x p.1 p.2
  have hf : Function.Injective f := fun x y h =>
    LinearMap.ext_on hs fun a ha => LinearMap.ext_on hs fun b hb => congrFun h (⟨a, ha⟩, ⟨b, hb⟩)
  have hfin : (Set.pi Set.univ fun p : s × s => Set.Icc (-B p.1 p.2) (B p.1 p.2)).Finite :=
    Set.Finite.pi' (fun p : s × s => Set.finite_Icc (-B p.1 p.2) (B p.1 p.2)) |>.subset fun g hg p => hg p trivial
  exact (hfin.preimage hf.injOn).subset fun x hx p _ => abs_le.1 (hx p.1 p.2)

theorem abs_le_of_indec {X : Type} [AddCommGroup X] {m : ℕ} (τ : Fin m → LinearMap.BilinForm ℤ X)
    {x : LinearMap.BilinForm ℤ X} (hx : InRCone τ x)
    (hind : ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x) (a b : X) :
    |x a b| ≤ ∑ j, |τ j a b| := by
  classical
  obtain ⟨c, hc, h⟩ := hx
  have hv : ∀ a b, ((x a b : ℤ) : ℝ) = ∑ i, c i * (τ i a b : ℝ) := fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simpa [toReal, LinearMap.sum_apply] using this
  by_cases hex : ∃ j, τ j ≠ 0 ∧ 1 ≤ c j
  · obtain ⟨j, hj, hcj⟩ := hex
    have hin : InRCone τ (x - τ j) := by
      refine ⟨c - Pi.single j 1, fun i => ?_, LinearMap.ext₂ fun a b => ?_⟩
      · by_cases hi : i = j
        · subst hi; simpa using hcj
        · simpa [Pi.single_apply, hi] using hc i
      · simp [toReal, LinearMap.sum_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, hv]
    have hx0 : x - τ j = 0 := by
      by_contra h0
      exact hind _ _ hin (inRCone_self τ j) h0 hj (by simp)
    rw [sub_eq_zero.1 hx0]
    exact Finset.single_le_sum (f := fun j => |τ j a b|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  · push Not at hex
    have : ((|x a b| : ℤ) : ℝ) ≤ ((∑ j, |τ j a b| : ℤ) : ℝ) := by
      push_cast
      rw [hv]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      by_cases hi : τ i = 0
      · simp [hi]
      · rw [abs_mul, abs_of_nonneg (hc i)]
        exact mul_le_of_le_one_left (abs_nonneg _) (hex i hi).le
    exact_mod_cast this

theorem finite_indec_inRCone (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m : ℕ)
    (τ : Fin m → LinearMap.BilinForm ℤ X) :
    {x : LinearMap.BilinForm ℤ X | InRCone τ x ∧ x ≠ 0 ∧
      ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x}.Finite :=
  (finite_bilinForm_abs_le X fun a b => ∑ j, |τ j a b|).subset fun _ hx => abs_le_of_indec τ hx.1 hx.2.2

end GlobalTheory.PolFan.Mark
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalSubfieldComplexFinitelyGenerate
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.finDimSubfield_finGen : ∀ (M : IntermediateField ℚ ℂ), FiniteDimensional ℚ M → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ Lf : IntermediateField ℚ ℂ, (↑S : Set ℂ) ⊆ Lf → M ≤ Lf := by
  intro M hM
  classical
  let b := Module.finBasis ℚ M
  refine ⟨Finset.univ.image (fun i => ((b i : M) : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    have : IsIntegral ℚ (b i) := Algebra.IsIntegral.isIntegral _
    exact (this.map M.val).isAlgebraic
  · intro Lf hS x hx
    have hb : ∀ i, ((b i : M) : ℂ) ∈ Lf := fun i =>
      hS (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    have hx' : (⟨x, hx⟩ : M) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
    have : x = ((∑ i, (b.repr ⟨x, hx⟩ i) • b i : M) : ℂ) := by rw [← hx']
    rw [this, IntermediateField.coe_sum]
    simp only [IntermediateField.coe_smul]
    exact Lf.sum_mem fun i _ => Lf.smul_mem (hb i)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVectorConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLevelSplitData

theorem levS_of_kOne_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → D.host.F = maximalRealSubfield D.host.E → ∀ (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → ∃ h : GL (Fin D.R.r) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ (b : Bool) (κ : Formalism.AUTREP.GAf D.host.E D.R.r), TrivOutside {s.v} κ → h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) → Y.PY.ψ κ ∈ levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) ∧ levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) (Y.PY.ψ κ) = 1 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHost hF k v s hs
  have hβ := hP.char.base.lev.βY 0 Y.hm
  obtain ⟨h, hh⟩ := GlobalTheory.RowLevelSplit.lemA_pf
    (GlobalTheory.RowLevelSplit.stdFrame_splitPlace_entries_off_place GlobalTheory.T.frameComponent_eq_one_off_splitPlace_of_trivOutside GlobalTheory.T.standard_frame_conjugate_close GlobalTheory.T.exists_conjugate_into_K1 GlobalTheory.T.placeOver_splitPlace_eq_chosen_or_conjugate) D (Yc D 0) D.R.r Y.hF Y.PY (R.βY 0) _ _
    Y.stdPsi.1 hβ s
  refine ⟨h, fun b κ hκ hk => ?_⟩
  classical
  exact GlobalTheory.RowLevelSplit.lemB_pf D (Yc D 0) (R.βY 0) _ (_ ∪ _) (Y.PY.ψ κ) Finset.subset_union_left Finset.subset_union_right
    (Y.PY.into κ) (hh κ hκ hk _)

theorem fixed_ne_bot_of_fixed_vector_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), GlobalTheory.HeightCounting.IsLocS π.S s τ → ∀ f ∈ π.S, f ≠ 0 → (∀ κ : Formalism.AUTREP.GAf L n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f) → GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n π s τ h hloc f hf hf0 hfix
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s h
  have hmul : ∀ (a b : Formalism.AUTREP.GAf L n) (g : Formalism.AUTREP.GAf L n → ℂ), NG.rt L n (a * b) g = NG.rt L n a (NG.rt L n b g) := by
    intro a b g
    funext c
    simp [NG.rt, mul_assoc]
  have hone : ∀ g : Formalism.AUTREP.GAf L n → ℂ, NG.rt L n 1 g = g := by
    intro g
    funext c
    simp [NG.rt]
  have hT : ∀ a b : Formalism.AUTREP.GAf L n, TrivOutside {s.v} a → TrivOutside {s.v} b → TrivOutside {s.v} (a * b) :=
    fun a b ha hb v hv => by
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha v hv, hb v hv, mul_one]
  refine GlobalTheory.FixedAtSplit.fixed_ne_bot_of_fixed_vector L n π s τ hloc (NG.rt L n x⁻¹ f) ?_ ?_ ?_
  · exact π.stable _ f hf
  · intro h0
    apply hf0
    rw [← hone f, ← mul_inv_cancel x, hmul, h0, map_zero]
  · intro κ hκ hk
    have h1 := hfix (x * κ * x⁻¹) (hT _ _ (hT _ _ hx hκ) (GlobalTheory.RowLevelSplit.trivOutside_inv hx)) (by
      rw [map_mul, map_mul, map_inv, e, show h⁻¹ * (h * s.loc n κ * h⁻¹) * h = s.loc n κ by group]
      exact hk)
    rw [← hmul, show κ * x⁻¹ = x⁻¹ * (x * κ * x⁻¹) by group, hmul, h1]

end GlobalTheory.RowLevelSplitData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseDimEqCmTypeCardMulPq
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

namespace GlobalTheory.BaseDim

theorem two_card_psi (E : Type) [Field E] [NumberField E] [IsCMField E] {r : ℕ} (D : ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    2 * D.Ψ.card = Module.finrank ℚ E := Formalism.L2.Pj.DatLin.two_card D.cmType

theorem eq_of_smooth_two {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    (m n : ℕ) (hm : SmoothOfRelativeDimension m f) (hn : SmoothOfRelativeDimension n f) : m = n := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := genericPoint X) trivial
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  obtain ⟨α, hα⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  algebraize [α.hom]
  have t₁ := trdeg_eq_of_smoothOfRelativeDimension K X f m hm Γ(X, U) hU.fromSpec inferInstance hα.symm
  have t₂ := trdeg_eq_of_smoothOfRelativeDimension K X f n hn Γ(X, U) hU.fromSpec inferInstance hα.symm
  exact_mod_cast t₁.symm.trans t₂

theorem card_eq_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ _ Φ k X j f f₀ Eb A₀ hj hL
  have hoi : IsOpenImmersion j := hL.1
  have hs : SmoothOfRelativeDimension Dw.dim (genStr T.Z) := T.smooth
  have hi : IsIso (spMap e.toRingHom) := inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have h0 : SmoothOfRelativeDimension 0 (spMap e.toRingHom) := inferInstance
  have h2 : SmoothOfRelativeDimension (Dw.dim + 0) (genStr T.Z ≫ spMap e.toRingHom) := inferInstance
  rw [Nat.add_zero] at h2
  have h1 : SmoothOfRelativeDimension (0 + Dw.dim) (j ≫ genStr T.Z ≫ spMap e.toRingHom) := inferInstance
  rw [hj, Nat.zero_add] at h1
  have hd : Dw.dim = X.dim := eq_of_smooth_two X.X X.str Dw.dim X.dim h1 X.smooth
  rw [← hd, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.dim, ← two_card_psi E (U.X k), Nat.mul_div_cancel_left _ two_pos]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Nat.add_sub_cancel_left, Nat.mul_assoc]

end GlobalTheory.BaseDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseMapOfFunctionFieldsStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpaceComponent_baseMap_of_functionFields : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∃ φ : X.Fn →ₐ[F] C.Y.Fn, (ratOf X).IsHom (ratOf C.Y) φ f := by
  first | exact @GlobalTheory.FlagBundle.exists_isHom_base_of_lifts | exact GlobalTheory.FlagBundle.exists_isHom_base_of_lifts | (intros; apply GlobalTheory.FlagBundle.exists_isHom_base_of_lifts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCAtState
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.RatSide

theorem formsC_of_full {D : D7} (S : RatDat D.ntw)
    (h : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm ∧ (S.A j).MKFull) : FormsC S := by
  intro j h1 h2
  obtain ⟨hK, hM⟩ := h j h1 h2
  refine ⟨hK, ?_, ?_⟩
  · obtain ⟨n, b, -, -, hsp, -, -⟩ := hK
    show FiniteDimensional S.Ks ↥(S.A j).WK
    rw [← hsp]
    exact FiniteDimensional.span_of_finite S.Ks (Set.finite_range b)
  · obtain ⟨T, hT⟩ := hM.1
    refine ⟨T, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [← hT]; exact Submodule.subset_span hx
    · exact ⟨hx.fst, by rw [hT]; exact hx⟩
    · rw [← hM.2] at hx
      refine Submodule.span_le.2 (fun y hy => ?_) hx
      have hy' : y ∈ Submodule.span (𝓞 S.Ks) (T : Set (S.WL j)) := by rw [hT]; exact hy
      exact Submodule.span_le_restrictScalars (𝓞 S.Ks) S.Ks _ hy'

end GlobalTheory.HeightCounting.RatSide

namespace GlobalTheory.HeightCounting.RatSide

theorem formsC_at_state : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w =>
    ∀ (P : Pre2 K w) (x : St P), LA hL x → FormsC (SOf x) := by
  intro hL
  refine StepW.of_all fun K _ _ _ w _ _ _ P x _ => formsC_of_full _ fun j _ _ =>
    ⟨x.m.z.geo.fw.ks (idxOf _ j), GlobalTheory.GoodLat.Obj.mkFull_of_tie x.m.z.geo.fw (idxOf _ j)⟩

end GlobalTheory.HeightCounting.RatSide
end

