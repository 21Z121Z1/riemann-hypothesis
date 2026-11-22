import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0281
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0548
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0549
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0550
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridStageLatticesPropertiesProof
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct nonZeroDivisors ComplexConjugate

namespace GlobalTheory.CoreOnto.StageProof

theorem under_mem_of_modul_le {D : D7} {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) (h : P.modul sc ≤ Q.asIdeal) : Q.under (𝓞 D.host.F) ∈ P.S0 := by
  unfold GlobalTheory.ChiGrid.Places.modul at h
  obtain ⟨v, hv, hle⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 h
  have hd : 0 < P.depth sc v ∨ P.depth sc v = 0 := by omega
  rcases hd with hd | hd
  · have h1 : (P.w v).asIdeal ≤ Q.asIdeal := Q.isPrime.le_of_pow_le hle
    have h2 : (P.w v).asIdeal = Q.asIdeal := (P.w v).isMaximal.eq_of_le Q.isPrime.ne_top h1
    have h3 : P.w v = Q := HeightOneSpectrum.ext h2
    rw [← h3, P.w_over v hv]
    exact hv
  · rw [hd, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact absurd hle Q.isPrime.ne_top

theorem stageOK : StageOK := by
  intro D hQ T L μ0 hL sc G W Mv hM i hi
  have hV := node_isV G hL (X := .core i) hi
  have hsd : IsSelfDualC (G.V (.core i)) (G.Λ (.core i)) := hV.sd
  obtain ⟨hsd', hstab, hcong⟩ := GlobalTheory.T.polarisationTwist_lattice_selfDual_same_stabilisers D (G.V (.core i)) (G.Λ (.core i)) hsd i
  have hRL := GlobalTheory.T.selfDualLattice_changeOfLattice_laws D
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := hRL.1 _ _ hsd'
    exact ⟨r, hr⟩
  · intro r hr v Mo
    have hsdS : IsSelfDualC (gridStage G v i r Mo).V (gridStage G v i r Mo).Λ := by
      show IsSelfDualC r.sp (GlobalTheory.AdelicU.frameLat r.sp)
      rw [hr]; exact hsd'
    have hJ : (gridStage G v i r Mo).J = Lev.levA (gridStage G v i r Mo).V
        (congLev D.sp.cm (gridStage G v i r Mo).V.gram (gridStage G v i r Mo).Λ G.modul) := by
      show lev G (.core i) = Lev.levA r.sp (congLev D.sp.cm r.sp.gram (GlobalTheory.AdelicU.frameLat r.sp) G.modul)
      rw [hr]
      exact (congrArg (Lev.levA (G.V (.core i))) (hcong G.modul)).symm
    obtain ⟨hfin, hopen, hst, hoff, hsph, hsplit⟩ := GlobalTheory.T.congruenceSubgroup_level_member_clauses D (gridCom W) (gridStage G v i r Mo) G.modul
      (GlobalTheory.ChiGrid.Places.modul_ne_bot _ _) (fun Q hQ' => under_mem_of_modul_le G.pl sc Q hQ') hsdS hJ
    have hw : GlobalTheory.Cusp.wittIndex r.sp = GlobalTheory.Cusp.wittIndex (G.V (.core i)) :=
      ((hRL.2.1 (G.V (.core i)) r W.θ _ Mo Set.univ).2.2.2).1
    have hwle : GlobalTheory.Cusp.wittIndex (G.V (.core i)) ≤ Node.neg D.R.m (.core i) := by
      haveI : IsCMField D.host.E := D.host.isCMField_hostE
      have hpar := GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel.parallelSig_of_sigOK hV.sigOK (fun τ => hV.sig τ)
      obtain ⟨U, hU, e⟩ := (GlobalTheory.Cusp.isGreatest_wittIndex ((G.V (.core i)) : HSpace D.host.E)).1
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      have h1 := GlobalTheory.ParallelWitt.finrank_le (E := D.host.E) (G.V (.core i)) τ (hpar τ) U (fun x hx y hy => by
        have := hU hy
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
        exact this x hx)
      omega
    exact {
      rank := hV.rank
      sigOK := hV.sigOK
      witt := by
        rw [show (gridStage G v i r Mo).V = r.sp from rfl, hw]
        refine lt_of_le_of_lt hwle ?_
        have h3 := D.R.three_m_lt_t
        have h4 := D.R.rank_add_five_le
        have h5 := D.R.m_add_three_le_k
        simp only [Node.neg, gridCom, sLen]
        unfold Ranks.r
        omega
      selfDual := hsdS
      fin := hfin
      isOpen := hopen
      stab := hst
      off := hoff
      sph := hsph
      split := hsplit
      haar := (v i).haar
      fund := (v i).fund }

end GlobalTheory.CoreOnto.StageProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridRouteKernelEqDetCharactersMulThetaKerne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict.ExactBig

variable {D : D7}

theorem exists_change {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χ χ₁ χ' : (AE D)ˣ →* Circle}
    {ω₁ : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (H₁ : IsWeilDatumO ψ S T χ₁ χ' ω₁)
    (hχ : IsHeckeChar D χ) (rχ : ResEta D χ S.rank) :
    ∃ ω, IsWeilDatumO ψ S T χ χ' ω ∧ ∀ u g y, IsDetRoot T g y → ω₁ (u, g) = (((χ₁ / χ) y : Circle) : ℂ) • ω (u, g) := by
  have r0 : ResEta D (χ * χ₁⁻¹) 0 :=
    Formalism.L2.Theta.resEta_parity (Formalism.L2.Theta.resEta_mul rχ (Formalism.L2.Theta.resEta_inv H₁.resS)) (by omega)
  have r1 : ResEta D 1 0 := ⟨r0.1, fun _ _ _ => by simp⟩
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  obtain ⟨ω, H, hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ H₁.std S T χ₁ χ' (χ * χ₁⁻¹) 1 ω₁ H₁
    (GlobalTheory.WeilChange.hecke_mul hχ (GlobalTheory.WeilChange.hecke_inv H₁.hecS)) h1 r0 r1
  have e : χ₁ * (χ * χ₁⁻¹) = χ := by rw [mul_comm χ, mul_inv_cancel_left]
  rw [e, mul_one] at H
  refine ⟨ω, H, fun u g y hy => ?_⟩
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D S u
  have e1 : (χ₁ / χ) y * (((1 : (AE D)ˣ →* Circle) x)⁻¹ * (χ * χ₁⁻¹) y) = 1 := by
    rw [MonoidHom.one_apply, inv_one, one_mul, ← MonoidHom.mul_apply, ← mul_assoc, div_mul_cancel, mul_inv_cancel,
      MonoidHom.one_apply]
  rw [hv u g x y hx hy, smul_smul, ← Circle.coe_mul, e1, Circle.coe_one, one_smul]

theorem seesaw_exact {ψ : AddChar (AF D.host.F) ℂ} {S A B : HSp D} {χ χ₁ χ₁' χ₂ χ₂' : (AE D)ˣ →* Circle}
    {ω₁ : GA D S × GA D A →* Module.End ℂ (WO S A → ℂ)} {ω₂ : GA D S × GA D B →* Module.End ℂ (WO S B → ℂ)}
    {ω : GA D S × GA D (GlobalTheory.Doubling.hsum A B) →* Module.End ℂ (WO S (GlobalTheory.Doubling.hsum A B) → ℂ)}
    (H₁ : IsWeilDatumO ψ S A χ₁ χ₁' ω₁) (H₂ : IsWeilDatumO ψ S B χ₂ χ₂' ω₂)
    (H : IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum A B) χ (χ₁' * χ₂') ω)
    {φ : WO S A → ℂ} {φ' : WO S B → ℂ} (hφ : IsThetaFunO ψ S A φ) (hφ' : IsThetaFunO ψ S B φ')
    (u : GA D S) (g : GA D A) (g₁ : GA D B) {x y : (AE D)ˣ} (hx : IsDetRoot A g x) (hy : IsDetRoot B g₁ y) :
    thetaKO ω₁ u g φ * thetaKO ω₂ u g₁ φ' = (((χ₁ / χ) x : Circle) : ℂ) * (((χ₂ / χ) y : Circle) : ℂ) *
      thetaKO ω u (GlobalTheory.SquareComm.blk A B (g, g₁)) (box2 φ φ') := by
  obtain ⟨o₁, K₁, e₁⟩ := exists_change H₁ H.hecS H.resS
  obtain ⟨o₂, K₂, e₂⟩ := exists_change H₂ H.hecS H.resS
  have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ H.std _ A B (GlobalTheory.BiTransfer.sumDec A B) S).om_box χ χ₁' χ₂' ω o₁
    o₂ H K₁ K₂ u g g₁ φ φ' hφ hφ'
  simp only [thetaKO]
  rw [← GlobalTheory.SeesawSumTarget.emb_sumDec, ← GlobalTheory.SeesawSumTarget.boxT_sumDec, key, GlobalTheory.MixModel.OrthDec.boxT_zero,
    e₁ u g x hx, e₂ u g₁ y hy]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem adjoint_exact {ψ : AddChar (AF D.host.F) ℂ} {S B : HSp D} {χB χS : (AE D)ˣ →* Circle}
    {ω₂ : GA D B × GA D S →* Module.End ℂ (WO B S → ℂ)} (H : IsWeilDatumO ψ B S χB χS ω₂) :
    ∃ ω : GA D (negSp S) × GA D B →* Module.End ℂ (WO (negSp S) B → ℂ),
      IsWeilDatumO ψ (negSp S) B χS⁻¹ χB⁻¹ ω ∧ ∀ f : WO B S → ℂ, IsThetaFunO ψ B S f →
        IsThetaFunO ψ (negSp S) B (fun y => f (adjM S B y)) ∧
        ∀ g₁ u, thetaKO ω (negGA S u) g₁ (fun y => f (adjM S B y)) = thetaKO ω₂ g₁ u f := by
  have hψ := H.std
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂),
    GlobalTheory.ConjWeil.weil_conjSource D ψ S B _ _ _ (GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ B S _ _ ω₂ H),
    fun f hf => ?_⟩
  have e : (fun y : WO (negSp S) B => f (adjM S B y)) =
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.AdjSwap.dagger_eq_adjM]
  rw [e]
  have h1 : IsThetaFunO ψ S B (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) :=
    ((GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ B S).2.2.1 f).2 hf
  refine ⟨((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S B).1 _).2.2 h1, fun g₁ u => ?_⟩
  show GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂) (negGA S u, g₁) _ 0 = ω₂ (g₁, u) f 0
  rw [GlobalTheory.ConjWeil.conjSource_apply]
  simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
  rw [GlobalTheory.TensorTargetRule.conjAdjoint_cj]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.AdjSwap.dagger_eq_adjM, adjM_zero]

theorem attChr_eq {C : Type} [CommGroup C] (χ η : C) (n : ℕ) :
    Formalism.IndefR.Lift.attChr χ η n = χ / η ^ (n % 2) := by
  unfold Formalism.IndefR.Lift.attChr
  rcases Nat.even_or_odd n with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]; simp
  · rw [if_pos h, Nat.odd_iff.1 h]; simp [div_eq_mul_inv]

theorem kerBig_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerBig W Θ g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωA u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumA W Θ) := by
  intro D T L sc G μ₀ hL W t i j ωA hA B ρ Θ Θ' hΘ g g₁ u
  have hd := isThetaFunO_of_isMatched hL W B ρ t i j Θ Θ' hΘ
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, hω₂, hadj⟩ := adjoint_exact h2
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hi := i.2
  have hj := j.2
  obtain ⟨s, hs⟩ := odd_sLen D
  obtain ⟨t', ht⟩ := D.R.t_odd
  have pW : (G.V (.grid (i + 1) (j + 1))).rank % 2 = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
    rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
    simp only [rankV, add_mul, one_mul]
    omega
  have pV : (G.V (.grid i (j + 1))).rank % 2 = (G.V (.grid (i + 1) j)).rank % 2 := by
    rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
    simp only [rankV, add_mul, one_mul]
    omega
  have cT : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j =
      G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹ := by
    simp only [GridData.chrT, GridData.chrS, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha]
    rw [pV, mul_div_mul_right_eq_div, ← div_eq_mul_inv, div_div_div_cancel_right]
  have cV : G.chrS (.chi i (j + 1)) / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = (L.eta ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j))⁻¹ := by
    simp only [GridData.chrS, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta]
    rw [pW, two_mul, pow_add, div_div, mul_left_comm, div_mul_cancel_left]
  have cV₁ : (G.chrT (.mu t (i + 1) j))⁻¹ / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j =
      (L.mu t (j + 1) * G.ch.chi (D.R.m - i))⁻¹ := by
    simp only [GridData.chrT, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta]
    rw [pW, inv_div, div_div, ← mul_assoc, div_mul_cancel_right]
  rw [cT] at hA
  let S := G.V (.grid (↑i + 1) (↑j + 1))
  let A := G.V (.grid (↑i) (↑j + 1))
  let Bs := G.V (.grid (↑i + 1) ↑j)
  have hA' : IsWeilDatumO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs) _ _ (ωA.toSgn true) := hA
  have e : ∀ d ∈ Θ.support, W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁ =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ * ωA (u, GlobalTheory.SquareComm.blk A Bs (g, g₁))
        (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) 0 := fun d hdm => by
    have k := seesaw_exact h1 hω₂ hA' (hd d hdm).1 (hadj _ (hd d hdm).2).1 (negGA S u) g g₁
      (GlobalTheory.RecDict.exists_isDetRoot D _ g).choose_spec (GlobalTheory.RecDict.exists_isDetRoot D _ g₁).choose_spec
    rw [(hadj _ (hd d hdm).2).2, cV, cV₁] at k
    exact k
  simp only [thetaKO, GlobalTheory.SquareDict.datumA, kerBig, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hdm => ?_
  rw [e d hdm]
  ring

end GlobalTheory.SquareDict.ExactBig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalFiniteSumsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_horizontal_finite_sums : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) → ∀ (n' : ℕ) (Fs : Fin n' → (G.V i (j + 1)).Maps) (vs : Fin n' → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) ∧ IsAutFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g) ∂(G.meas t i (j + 1)).ν) ∧ IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g) ∂(G.meas t i (j + 1)).ν) := by
  first | exact @GlobalTheory.FinLift.th_finLift | exact GlobalTheory.FinLift.th_finLift | (intros; apply GlobalTheory.FinLift.th_finLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftInjectiveGoodPartJointEigenspaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_injective_goodPart_jointEigenspace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (x y : (R.toCx3 F).FLC j A3.A.fam.μ0), x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c → (R.toCx3 F).θ' j A3.A.fam.μ0 x ≠ 0 → y ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c ⊓ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → (R.toCx3 F).θ' j A3.A.fam.μ0 y = 0 → y = 0 := by
  first | exact @GlobalTheory.InjEigen.inj_eig | exact GlobalTheory.InjEigen.inj_eig | (intros; apply GlobalTheory.InjEigen.inj_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftOpenLevelBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_open_level_bound : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → ∀ M : ℕ, ∃ (d : ℕ) (C : NNReal), ∀ ψ : GA D (G.P (i + 1)).V → ℂ, IsAutFun (G.P (i + 1)).V ψ → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, ψ (g * k) = ψ g) → ψ ∈ GlobalTheory.Mem.AutSpace.SmFun R.θ (G.P (i + 1)).V → (∀ k, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V k 0 ψ ≠ ⊤) → IsCuspFun (G.P (i + 1)).V ψ → GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M ψ ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 ψ := by
  first | exact @GlobalTheory.DownConv.decayInt_le_growthSob | exact GlobalTheory.DownConv.decayInt_le_growthSob | (intros; apply GlobalTheory.DownConv.decayInt_le_growthSob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUniformFiniteBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownGrowth

open GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.DownApprox
open scoped ENNReal

set_option maxHeartbeats 2000000 in

theorem growth_approx : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (J : Finset ℕ) (f : ℕ → WO (G.P (i + 1)).V (G.P i).V → ℂ) (p : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ j ∈ J, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j)) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  intro hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi
  classical
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (neg (G.P (i + 1)).V).rank (G.P i).V.rank
  refine ⟨Ae, fun K Fm v hF Φ hΦ ε hε => ?_⟩
  have hθ : IsInfFam R.θ := hRB.inf
  have hW := (hG.arrows.dn i hi).weil
  have hω : IsWeilDatumO R.ψ (neg (G.P (i + 1)).V) (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i))
      ((G.dn i).ω.toSgn true) := hW
  obtain ⟨hν, hfd⟩ : (G.mP (i + 1)).ν.IsHaarMeasure ∧
      IsFundamentalDomain (GQ (G.P (i + 1)).V) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    have h := hG.meas.P (i + 1) hi
    by_cases hd : i + 1 = D.R.m
    · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
    · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩
  have hFv : ∀ k ∈ K, GlobalTheory.Grow.RapidDec (G.P (i + 1)).V (Fm k (v k)) := fun k hk => by
    have h := GlobalTheory.LowVanishObj.multT_apply_cusp R.θ (G.P (i + 1)).M ∅ 1 (Fm k) (hF k hk) (v k)
    exact (GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ h.1 h.2).rapidDec
  have hB : ∀ k ∈ K, ∃ B : ℝ, ∀ g, ‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae ≤ B :=
    fun k hk => (hFv k hk).decay Ae
  choose! B hB using hB
  obtain ⟨μ, 𝓓, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (neg (G.P (i + 1)).V) (G.P i).V
  obtain ⟨U, hU, hΦU, happ⟩ := GlobalTheory.FockDensity.fockDense D _ _ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) R.θ R.ψ
    hω.std hθ μ 𝓓 hμ Φ hΦ
  haveI : BorelSpace (GA D (G.P (i + 1)).V) := ⟨rfl⟩
  haveI hfin : IsFiniteMeasure ((G.mP (i + 1)).ν.restrict (G.mP (i + 1)).fd) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.Chain.LiftReg.vol_ne_top hν hfd)

  have hker : ∀ U' : AddSubgroup (WO (neg (G.P (i + 1)).V) (G.P i).V), IsOpen (U' : Set (WO (neg (G.P (i + 1)).V) (G.P i).V)) →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (neg (G.P (i + 1)).V) (G.P i).V U', ∀ g h,
        ‖thetaKO (G.dn i).ω g h f‖ ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal *
          GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae * GlobalTheory.Grow.height (G.P i).V h ^ Ae := by
    intro U' hU'
    obtain ⟨C, hC0, hC⟩ := (H (neg (G.P (i + 1)).V) (G.P i).V rfl rfl).real R.ψ hθ hU'
    refine ⟨C * 2 ^ Ae, by positivity, fun f hf g h => ?_⟩
    have hb := (hC _ _ ((G.dn i).ω.toSgn true) hω μ 𝓓 hμ f hf).2
    have hinv : ∀ γ ∈ GQ (G.P (i + 1)).V, ∀ g, thetaKO (G.dn i).ω (γ * g) h f = thetaKO (G.dn i).ω g h f := fun γ hγ g => by
      have e1 : (((ofSgn true (G.P (i + 1)).V).symm (γ * g), h) : GA D (neg (G.P (i + 1)).V) × GA D (G.P i).V) =
          ((ofSgn true (G.P (i + 1)).V).symm γ, 1) * ((ofSgn true (G.P (i + 1)).V).symm g, h) := by simp
      show ((G.dn i).ω.toSgn true) ((ofSgn true (G.P (i + 1)).V).symm (γ * g), h) f 0 =
        ((G.dn i).ω.toSgn true) ((ofSgn true (G.P (i + 1)).V).symm g, h) f 0
      rw [e1, map_mul, Module.End.mul_apply]
      exact hω.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hω.om_pres _ _ hf.1)
    have hgr : ∀ g, ‖thetaKO (G.dn i).ω g h f‖ ≤ (C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal *
        GlobalTheory.Grow.height (G.P i).V h ^ Ae) * GlobalTheory.Grow.height (G.P (i + 1)).V g ^ Ae := fun g => by
      have := hb ((ofSgn true (G.P (i + 1)).V).symm g) h
      refine this.trans_eq ?_
      show C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal *
        (GlobalTheory.Grow.height (G.P (i + 1)).V g * GlobalTheory.Grow.height (G.P i).V h) ^ Ae = _
      ring
    refine (GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO (G.dn i).ω g h f) hinv hgr g).trans_eq ?_
    ring

  have hbound : ∀ U' : AddSubgroup (WO (neg (G.P (i + 1)).V) (G.P i).V), IsOpen (U' : Set (WO (neg (G.P (i + 1)).V) (G.P i).V)) →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (neg (G.P (i + 1)).V) (G.P i).V U', ∀ k ∈ K, ∀ h,
        IntegrableOn (fun g => thetaKO (G.dn i).ω g h f * Fm k (v k) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν ∧
        ‖∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h f * Fm k (v k) g ∂(G.mP (i + 1)).ν‖ ≤
          Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max (B k) 0 * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal *
            GlobalTheory.Grow.height (G.P i).V h ^ Ae := by
    intro U' hU'
    obtain ⟨Kc, hK0, hK⟩ := hker U' hU'
    refine ⟨Kc, hK0, fun f hf k hk h => ?_⟩
    have hs : 0 ≤ (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal := ENNReal.toReal_nonneg
    have hcont : Continuous fun g => thetaKO (G.dn i).ω g h f * Fm k (v k) g :=
      ((hω.om_cont f hf.1 0).comp ((continuous_ofSgn_symm true _).prodMk continuous_const)).mul (hFv k hk).continuous
    have h5 : 0 ≤ GlobalTheory.Grow.height (G.P i).V h ^ Ae := pow_nonneg (GlobalTheory.Grow.height_pos _ h).le Ae
    have hpt : ∀ g, ‖thetaKO (G.dn i).ω g h f * Fm k (v k) g‖ ≤
        Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max (B k) 0 * GlobalTheory.Grow.height (G.P i).V h ^ Ae := by
      intro g
      rw [norm_mul]
      have h1 := hK f hf g h
      have h3 : ‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae ≤ max (B k) 0 :=
        (hB k hk g).trans (le_max_left _ _)
      calc ‖thetaKO (G.dn i).ω g h f‖ * ‖Fm k (v k) g‖
          ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae *
              GlobalTheory.Grow.height (G.P i).V h ^ Ae * ‖Fm k (v k) g‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height (G.P i).V h ^ Ae *
              (‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae) := by ring
        _ ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height (G.P i).V h ^ Ae * max (B k) 0 := by
          gcongr
        _ = _ := by ring
    refine ⟨Integrable.of_bound hcont.aestronglyMeasurable _ (.of_forall hpt), ?_⟩
    refine (norm_integral_le_of_norm_le_const (.of_forall hpt)).trans (le_of_eq ?_)
    simp only [Measure.real, Measure.restrict_apply_univ]
    ring

  obtain ⟨Kc, hK0, hMb⟩ := hbound U hU
  have hvol : 0 ≤ ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal := ENNReal.toReal_nonneg
  have hBs : 0 ≤ ∑ k ∈ K, max (B k) 0 := Finset.sum_nonneg fun k _ => le_max_right _ _
  have hM0 : 0 ≤ Kc * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal * ∑ k ∈ K, max (B k) 0 := by positivity
  obtain ⟨r, -, hr0', hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr0'
  set M := Kc * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal * ∑ k ∈ K, max (B k) 0 with hMdef
  have hδ : (0 : ℝ≥0∞) < ENNReal.ofReal (r / (M + 1)) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨g₀, hgS, hgU, hlt⟩ := happ d _ hδ
  obtain ⟨n, f, p, hf, rfl⟩ := exists_sum_of_mem_fockSpan hgS
  let f' : ℕ → (WO (G.P (i + 1)).V (G.P i).V → ℂ) := fun j => if hj : j < n then f ⟨j, hj⟩ else 0
  let p' : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) := fun j => if hj : j < n then p ⟨j, hj⟩ else 0
  refine ⟨Finset.range n, f', p', fun j hj => ?_, ?_⟩
  · have hj' := Finset.mem_range.1 hj
    simp only [f', dif_pos hj']
    exact (isVacF_negFr _ _ _).1 (hf _)
  have hpt : ∀ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l) =
      fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l) := fun l => ptF_negFr _ _ (f l) (p l)
  have hint : ∀ l, ∀ k ∈ K, ∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h
      (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * Fm k (v k) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    intro l k hk h
    have ht : IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V
        (ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l)) :=
      GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hθ _ _ _ _ (hf l).1 (p l)
    obtain ⟨U', hU', hl'⟩ := GlobalTheory.Size.isTheta_iff_level.1 ht
    obtain ⟨_, _, hb⟩ := hbound U' hU'
    rw [← hpt l]
    exact (hb _ hl' k hk h).1
  have hΨU := sub_mem hΦU hgU
  have e : ∀ k ∈ K, ∀ h, (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * Fm k (v k) g ∂(G.mP (i + 1)).ν) -
      ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) *
        Fm k (v k) g ∂(G.mP (i + 1)).ν =
      ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l)) * Fm k (v k) g
          ∂(G.mP (i + 1)).ν := by
    intro k hk h
    rw [← integral_finset_sum _ fun l _ => hint l k hk h,
      ← integral_sub (hMb Φ hΦU k hk h).1 (integrable_finset_sum _ fun l _ => hint l k hk h)]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp only [thetaKO, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul, hpt]
  have hsw : ∀ h, ∑ j ∈ Finset.range n, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * Fm k (v k) g ∂(G.mP (i + 1)).ν =
      ∑ k ∈ K, ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * Fm k (v k) g ∂(G.mP (i + 1)).ν := by
    intro h
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * Fm k (v k) g ∂(G.mP (i + 1)).ν) n]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [f', p', dif_pos l.isLt, Fin.eta]
  set s := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d
    (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l))).toReal with hsdef
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hs := ENNReal.toReal_lt_of_lt_ofReal hlt
  have hle : GlobalTheory.Size.growthSize (G.P i).V Ae (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ *
      (Fm k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ Finset.range n, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * (Fm k (v k)) g ∂(G.mP (i + 1)).ν) ≤
      ENNReal.ofReal (M * s) := by
    refine (GlobalTheory.Size.growthSize_le_iff (mul_nonneg hM0 hs0)).2 fun h => ?_
    rw [hsw h, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun k hk => e k hk h]
    refine (norm_sum_le _ _).trans ?_
    rw [hMdef, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ((hMb _ hΨU k hk h).2).trans_eq ?_
    ring
  refine hle.trans_lt (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hrε)
  have hM1 : 0 < M + 1 := by linarith
  have h1 : (M + 1) * s < r := by
    have := mul_lt_mul_of_pos_left hs hM1
    rwa [mul_div_cancel₀ _ hM1.ne'] at this
  nlinarith

end GlobalTheory.DownGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopSeparationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_separation : GlobalTheory.FunPr.Hypotheses₂ → TopSep := by
  first | exact @GlobalTheory.SepRows.SepProof.topSep_of_classicalTheorems | exact GlobalTheory.SepRows.SepProof.topSep_of_classicalTheorems | (intros; apply GlobalTheory.SepRows.SepProof.topSep_of_classicalTheorems <;> assumption)
end

