import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0115
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0632
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0627
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0537
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupProductFiniteClassesCoboundary
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmFonOfPoints
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HubFon

theorem g_ne_q_d (D : D7) (k : Fin 2) : D.host.g k ≠ D.host.q ∧ D.host.g k ≠ D.host.d := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  constructor
  · intro h
    have h1 : D.host.g k % D.host.q = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.d, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega
  · intro h
    have h1 : D.host.g k % D.host.d = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.q, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), AdmissibleParameterJ.DeRhamFamilyAway D → AdmissibleParameterJ.ConclusionJa D → ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ := by
  intro hF D _L hG hJa r ρ hP i hi w hw C
  obtain ⟨ep, hJ⟩ := hJa
  have hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d := hi.1.1
  have h0 : D.nd.l i ≠ D.host.g 0 := by
    intro h; rcases hl with e | e <;> rw [e] at h
    · exact (g_ne_q_d D 0).1 h.symm
    · exact (g_ne_q_d D 0).2 h.symm
  have h1 : D.nd.l i ≠ D.host.g 1 := by
    intro h; rcases hl with e | e <;> rw [e] at h
    · exact (g_ne_q_d D 1).1 h.symm
    · exact (g_ne_q_d D 1).2 h.symm
  obtain ⟨π₀, hπ₀⟩ := hi.2
  have hg0 : π₀ ∈ D.nd.Zgood i := (D.Zgood_tie i π₀).2 hπ₀
  have hZ0 := LargeLevelLemmas.zgoodSubsetZ i hg0
  have hd0 : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (r i) (ρ i) π₀ := by
    obtain ⟨e, he⟩ := (hP.compl i π₀ hZ0).rho
    exact ⟨e, fun g u => he g u⟩
  have hc := (GlobalTheory.CrysFromGTwo.main hF D i (r i) (ρ i) π₀ (hP.good i) (hG i _ (hP.good i)) h0 h1 hd0 w hw C).2
  have K := GlobalTheory.TateDualCrys.crystalline_and_jumps D i w hw (D.locT (D.nd.l i)) C.LL C.le (r i) (ρ i)
    (fun x => (hc x).2)
  refine ⟨fun V1 _ _ _ _ _ ρ1 hs => K.1 V1 ρ1 hs, fun π hπ => ?_⟩
  have hZ := LargeLevelLemmas.zgoodSubsetZ i hπ
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r i π) (ρ i π) (D.nd.chi i) e := by
    obtain ⟨e, he⟩ := (hP.compl i π hZ).rho
    exact ⟨e, fun g u => he g u⟩
  refine K.2 π hdec (fun τ a => ?_)
  obtain ⟨g, ρ', -, hx, -⟩ := hJ i (r i) (hP.good i) w hw C τ
  have := (hx π a).2.1
  rw [this]
  split_ifs <;> norm_num

end GlobalTheory.HubFon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2OfDecomposition
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.GTwoTheta

open Formalism.MainNotions.AdmissibleParameterJ

variable {D : D7}

theorem zero_not_mem_JW {L : SizeData₂ D} (hc : jcCondition L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) : (0 : ℚ) ∉ JW D up j ρ := by
  obtain ⟨hlow, -, hcl, h0⟩ := hc j hj1 hjm ρ
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  cases up
  · simp only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union, reflS, Set.mem_setOf_eq, AdmissibleParameterJ.refl]
    rintro (h | h)
    · have := hcl _ h; linarith
    · rcases hlow _ h with ⟨-, h2⟩ | ⟨h2, -⟩ <;> linarith
  · simpa only [JW, cloudT, lowT, ↓reduceIte] using h0

theorem JW_sub_JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : JW D up j ρ ⊆ JJ D up j ρ := by
  intro q hq
  cases up
  · simp only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union] at hq
    simp only [JJ, Bool.false_eq_true, ↓reduceIte, Jm, Jp]
    rcases hq with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · simp only [JW, cloudT, lowT, ↓reduceIte, Set.mem_union] at hq
    simp only [JJ, ↓reduceIte, Jp, Set.mem_union]
    exact Or.inl hq

theorem neg_one_not_mem_JW {L : SizeData₂ D} (hc : jcCondition L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) : (-1 : ℚ) ∉ JW D up j ρ :=
  fun h => ((hc j hj1 hjm ρ).2.1 up).1 (JW_sub_JJ up j ρ h)

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem dR_WT (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)))) :
    IsDR (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧
      IsDR (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) := by
  have := D.nd.lPrime i
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e :=
    (GlobalTheory.DecompForms.main D i r ρ π).1 hD
  have hsum := (GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hdec).1 hc
  exact ⟨(GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) _ _ _ _ hsum.1).1,
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) _ _ _ _ hsum.2).1⟩

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem twistedRep_no_invariants_purity (D : D7) (L : SizeData₂ D) (ep : Bool) (hJ : hodgeTateJumpsAtModulesForSign D ep) (hJc : jcCondition L) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (hr : GoodR D.nd i r)
    (hπ : π ∈ D.nd.Z i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)))) :
    H0V (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) = ⊥ ∧ H0V (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) = ⊥ := by
  have := D.nd.lPrime i
  have hjr := D.nd.j_range i
  obtain ⟨hdrW, hdrT⟩ := dR_WT D i r ρ π w hw C hD hc
  obtain ⟨τ₀⟩ := GlobalTheory.PtCore.nonempty_embE D i w hw C.LL C.le
  obtain ⟨g, ρ', -, -, hW⟩ := hJ i r hr w hw C τ₀
  obtain ⟨-, hW0, -, hT0⟩ := hW ρ π hπ hD 0
  constructor
  · refine GlobalTheory.T.H0_vanish_of_zero_multiplicity _ _ _ (D.locT _) _ _ _ _ τ₀ hdrW ?_
    refine hW0.trans ?_
    rw [if_neg]
    push_cast
    exact zero_not_mem_JW hJc _ hjr.1 hjr.2 ρ' _
  · refine GlobalTheory.T.H0_vanish_of_zero_multiplicity _ _ _ (D.locT _) _ _ _ _ τ₀ hdrT ?_
    refine hT0.trans ?_
    rw [if_neg]
    rw [GlobalTheory.JumpSets.dualS_int]
    push_cast
    exact neg_one_not_mem_JW hJc _ hjr.1 hjr.2 ρ' _

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem chi_jump (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hamb : ∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∀ c ∈ Finset.Icc 1 D.R.t, ∀ a,
      multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a =
        if a = (c : ℤ) - 1 then 1 else 0)
    (c : ℕ) (hc1 : 1 ≤ c) (hct : c ≤ D.R.t) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (a : ℤ) :
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a ↔ a = (c : ℤ) - 1 := by
  have := D.nd.lPrime i
  have hm := hamb τ c (Finset.mem_Icc.2 ⟨hc1, hct⟩) a
  refine (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero _ _ _ (D.locT _) _ _ _
    (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a).2.2.trans ?_
  refine (Iff.of_eq (congrArg (· ≠ 0) hm)).trans ?_
  split_ifs with h <;> simp [h]

theorem tw_jumps (D : D7) (L : SizeData₂ D) (ep : Bool) (hJ : hodgeTateJumpsAtModulesForSign D ep) (hJc : jcCondition L) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) :
    (∀ (x y : D.nd.X i) (a : ℤ),
      multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a =
        multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r y)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a) ∧
    (∀ (x : D.nd.X i) (a : ℤ),
      multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a ≤ 1) ∧
    (∀ x : D.nd.X i,
      ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ (-1)) := by
  have hjr := D.nd.j_range i
  obtain ⟨g, ρ', -, hx, -⟩ := hJ i r hr w hw C τ
  refine ⟨fun x y a => ?_, fun x a => ?_, fun x => ?_⟩
  · rw [← locC_rTwO, ← locC_rTwO, (hx x a).2.1, (hx y a).2.1]
  · rw [← locC_rTwO, (hx x a).2.1]
    split_ifs <;> norm_num
  · rw [← locC_rTwO, (hx x (-1)).1]
    push_cast
    exact ((hJc _ hjr.1 hjr.2 ρ').2.1 _).1

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), AdmissibleParameterJ.DeRhamFamilyAway D → AdmissibleParameterJ.ConclusionJa D → AdmissibleParameterJ.jcCondition L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π := by
  intro hF D L hG2 hJa hJc i r ρ π hr h0 h1 hπ hD w hw C
  obtain ⟨ep, hJ⟩ := hJa
  have hcrys := GlobalTheory.CrysFromGTwo.main hF D i r ρ π hr (hG2 i r hr) h0 h1 hD w hw C
  have hamb := GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition D i r ρ π hD hπ h0 h1 w hw C
  have hH := twistedRep_no_invariants_purity D L ep hJ hJc i r ρ π hr hπ w hw C hD (hcrys.2 π).2
  refine ⟨⟨fun x => (hcrys.2 x).1, fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).1,
    fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).2.1,
    fun c hc1 hct τ a => chi_jump D i r ρ π w hw C (fun τ => (hamb τ).2) c hc1 hct τ a,
    fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).2.2, hH.1, hH.2⟩, fun x => ?_⟩
  rw [← locC_rTwO]
  exact (hcrys.2 x).2

end GlobalTheory.GTwoTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorIdentificationNaturalStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcrisTensorIdentification_natural : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Q : PhiMod O K l e a κ) (T' : LocLat (Gl l) ℚ_[l] K O) (I' : Ident t ϖ Q T') (jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T') (f : LatHom T.L T'.L) (F : GlobalTheory.BK.Hom P Q), IsCrisCmp I' jB' → IsMapOf I I' f F → (∀ (m : P.MMl) (m' : Q.MMl), m'.1 = F.app m.1 → jB' (toBcris t ϖ Q m') = TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB (toBcris t ϖ P m))) ∧ ∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ Q jB' (homW t ϖ F w) (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  first | exact @GlobalTheory.BKGal.cris_natural | exact GlobalTheory.BKGal.cris_natural | (intros; apply GlobalTheory.BKGal.cris_natural <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisImagesBasisBdRplusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_basis_images_basis_BdRplus : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∃ f : ι → T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ i, A ((ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) ^ β) (f i) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) ∧ (∀ v, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : ι → OD l ↥(OL LL), v = ∑ i, A (d i) (f i)) ∧ ∀ d : ι → OD l ↥(OL LL), ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0 := by
  first | exact @GlobalTheory.BKGal.JumpDR.basis_images | exact GlobalTheory.BKGal.JumpDR.basis_images | (intros; apply GlobalTheory.BKGal.JumpDR.basis_images <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinComparisonUnitCocycleEveryPrism
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.StratCocycle

variable {l : ℕ} {R : Type} [CommRing R]

theorem comp_assoc {P P' P'' P''' : Obj l R} (h : Hom P'' P''') (g : Hom P' P'') (f : Hom P P') :
    (h.comp g).comp f = h.comp (g.comp f) := Hom.ext' rfl

theorem comp_id {P P' : Obj l R} (f : Hom P P') : f.comp (Hom.id P) = f := Hom.ext' rfl

theorem map_comp {P P' P'' : Obj l R} {d : ℕ} (ε : Matrix (Fin d) (Fin d) P.A) (g : Hom P' P'') (f : Hom P P') :
    ε.map (g.comp f).f = (ε.map f.f).map g.f := by
  rw [Matrix.map_map]; rfl

theorem unit_of_codiag {P Q B : Obj l R} {d : ℕ} (inl inr : Hom P Q)
    (univ : ∀ (C : Obj l R) (f g : Hom P C), ∃! h : Hom Q C, h.comp inl = f ∧ h.comp inr = g)
    (ε : Matrix (Fin d) (Fin d) Q.A)
    (h1 : ∀ Δ : Hom Q P, Δ.comp inl = Δ.comp inr → ε.map Δ.f = 1)
    (k : Hom Q B) (hk : k.comp inl = k.comp inr) : ε.map k.f = 1 := by
  obtain ⟨Δ, ⟨hΔl, hΔr⟩, -⟩ := univ P (Hom.id _) (Hom.id _)
  have hk' : k = (k.comp inl).comp Δ := by
    refine (univ B (k.comp inl) (k.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp (k.comp inl)) hΔl).trans (comp_id _))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp (k.comp inl)) hΔr).trans ((comp_id _).trans hk))
  calc ε.map k.f = ε.map ((k.comp inl).comp Δ).f := congrArg (fun k : Hom Q B => ε.map k.f) hk'
    _ = (ε.map Δ.f).map (k.comp inl).f := map_comp ε _ Δ
    _ = (1 : Matrix (Fin d) (Fin d) P.A).map (k.comp inl).f :=
        congrArg (fun M : Matrix (Fin d) (Fin d) P.A => M.map (k.comp inl).f) (h1 Δ (hΔl.trans hΔr.symm))
    _ = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem cocycle_of_triple {P Q Q₂ B : Obj l R} {d : ℕ} (inl inr : Hom P Q)
    (univ : ∀ (C : Obj l R) (f g : Hom P C), ∃! h : Hom Q C, h.comp inl = f ∧ h.comp inr = g)
    (i₁ : Hom Q Q₂) (j : Hom P Q₂)
    (univ₂ : ∀ (C : Obj l R) (f : Hom Q C) (g : Hom P C), ∃! h : Hom Q₂ C, h.comp i₁ = f ∧ h.comp j = g)
    (ε : Matrix (Fin d) (Fin d) Q.A)
    (hc : ∀ k₂₃ k₁₃ : Hom Q Q₂, i₁.comp inr = k₂₃.comp inl → i₁.comp inl = k₁₃.comp inl →
      k₂₃.comp inr = k₁₃.comp inr → ε.map i₁.f * ε.map k₂₃.f = ε.map k₁₃.f)
    (k₁ k₂ k₃ : Hom Q B) (h12 : k₁.comp inr = k₂.comp inl) (h13 : k₁.comp inl = k₃.comp inl)
    (h23 : k₂.comp inr = k₃.comp inr) : ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  obtain ⟨k₂₃, ⟨h₂₃l, h₂₃r⟩, -⟩ := univ Q₂ (i₁.comp inr) j
  obtain ⟨k₁₃, ⟨h₁₃l, h₁₃r⟩, -⟩ := univ Q₂ (i₁.comp inl) j
  have hc' := hc k₂₃ k₁₃ h₂₃l.symm h₁₃l.symm (h₂₃r.trans h₁₃r.symm)
  obtain ⟨m, ⟨hml, hmr⟩, -⟩ := univ₂ B k₁ (k₂.comp inr)
  have e₂ : k₂ = m.comp k₂₃ := by
    refine (univ B (k₂.comp inl) (k₂.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₂₃l).trans
        ((comp_assoc _ _ _).symm.trans ((congrArg (fun q => Hom.comp q inr) hml).trans h12)))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₂₃r).trans hmr)
  have e₃ : k₃ = m.comp k₁₃ := by
    refine (univ B (k₃.comp inl) (k₃.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₁₃l).trans
        ((comp_assoc _ _ _).symm.trans ((congrArg (fun q => Hom.comp q inl) hml).trans h13)))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₁₃r).trans (hmr.trans h23))
  subst e₂ e₃ hml
  rw [map_comp ε m i₁, map_comp ε m k₂₃, map_comp ε m k₁₃, ← Matrix.map_mul, hc']

theorem unit_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A),
    ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) →
    ∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧
      ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl →
        k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  intro l _ K bk d ρ τ s ht En ε hrel B
  have cocB := GlobalTheory.T.breuilKisinCoproduct_unit_cocycle_identities l K bk d ρ τ s ht En ε hrel
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  refine ⟨unit_of_codiag En.inl En.inr En.univ ε
    (fun Δ h => (cocB bk.prism (Hom.id _) Unit (TopBasis.self bk.J)).1 Δ h), fun k₁ k₂ k₃ h12 h13 h23 => ?_⟩
  exact (GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk En.Q _ _ (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk En.Q En.inl)).elim fun En₂ =>
    (GlobalTheory.T.breuilKisinEnvelopes_adicTopologicalBasis l K bk En En₂).2.elim fun ι htb => htb.elim fun tb =>
      cocycle_of_triple En.inl En.inr En.univ En₂.inl En₂.inr En₂.univ ε
        (fun k₂₃ k₁₃ a b c => (cocB En₂.Q (En₂.inl.comp En.inl) ι tb).2 En₂.inl k₂₃ k₁₃ a b c)
        k₁ k₂ k₃ h12 h13 h23

end GlobalTheory.BSP.StratCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeFrobeniusSolutionsPowDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem envelope_dvd_lpow_aux₁ {R : Type} [CommRing R] {ι : Type} (s : Finset ι) (L a b : R) (u v : ι → R)
    (hL : L ∈ nonZeroDivisors R) (h : a * (L * b) = ∑ i ∈ s, L * u i * v i) : a * b = ∑ i ∈ s, u i * v i := by
  refine sub_eq_zero.1 ((mem_nonZeroDivisors_iff.mp hL).2 _ ?_)
  have e : ∑ i ∈ s, u i * v i * L = ∑ i ∈ s, L * u i * v i := Finset.sum_congr rfl fun i _ => by ring
  rw [sub_mul, Finset.sum_mul, e, ← h]
  ring

theorem envelope_dvd_lpow_aux₂ {R : Type} [CommRing R] (L w z : R) (k : ℕ)
    (hL : ∀ x : R, L * x = 0 → x = 0) (h : L * w = L ^ (k + 1) * z) : L ^ k ∣ w :=
  ⟨z, sub_eq_zero.1 (hL _ (by rw [mul_sub, h, pow_succ', mul_assoc, sub_self]))⟩

theorem envelope_dvd_lpow_aux₄ {R : Type} [CommRing R] (L x y : R) (k : ℕ) (hxy : x = L * y) (h : L ^ k ∣ y) :
    L ^ (k + 1) ∣ x := by
  rw [hxy, pow_succ']
  exact mul_dvd_mul_left _ h

theorem envelope_dvd_lpow_aux₃ {l : ℕ} [Fact l.Prime] {K : FinExt l} {B : Obj l ↥(OL K)} (σ : Hom B (ainfObj K))
    (x y : B.A) (k : ℕ) (hxy : x = (l : B.A) * y) (h : ((l : ℕ) : (ainfObj K).A) ^ (k + 1) ∣ σ.f x) :
    ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f y := by
  subst hxy
  obtain ⟨z, hz⟩ := h
  rw [map_mul, map_natCast] at hz
  exact envelope_dvd_lpow_aux₂ (R := Ainf l) (l : Ainf l) (σ.f y) z k ainf_torsionFree hz

theorem envelope_dvd_lpow_of_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (c : κ → κ → En.Q.A) (h k : ℕ) (x : κ → En.Q.A), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ^ k ∣ x j := by
  intro l _ K bk En κ _ c h k
  have hreg : ((l : ℕ) : En.Q.A) ∈ nonZeroDivisors En.Q.A :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk En.Q.A (BK.hf En.inl) (Digits l) En.tb).2.2.1
  induction k with
  | zero => intro x _ _ j; rw [pow_zero]; exact one_dvd _
  | succ k ih =>
    intro x hx hσ j
    have h1 := GlobalTheory.T.dvd_l_of_galoisSections_breuilKisinCoproduct l K bk En κ x c h hx
      (fun g σ e1 e2 i => dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) (hσ g σ e1 e2 i))
    choose y hy using h1
    have hyeq : ∀ j, BK.hf En.inl bk.E ^ h * y j = ∑ i, En.Q.D.φ (y i) * c i j := by
      intro j
      have hxj := hx j
      simp only [hy, map_mul, map_natCast] at hxj
      exact envelope_dvd_lpow_aux₁ Finset.univ _ _ _ (fun i => En.Q.D.φ (y i)) (fun i => c i j) hreg hxj
    have hσ' : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
        σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (y j) := by
      intro g σ e1 e2 i
      exact envelope_dvd_lpow_aux₃ σ (x i) (y i) k (hy i) (hσ g σ e1 e2 i)
    exact envelope_dvd_lpow_aux₄ _ _ _ k (hy j) (ih y hyeq hσ' j)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCuspidalMultisetsTotalDegreeLeStatement
section
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_cuspidal_multisets_total_degree_le : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → ∀ S : Finset (Multiset (Pc g)), (∀ M ∈ S, (M.map fun p => p.1).sum = n ∧ ∀ p ∈ M, IsCusp p.2) → S.card ≤ g ^ n - g ^ (n - 1) := by
  first | exact @GlobalTheory.GLq.CuspMultisetCount.card_le | exact GlobalTheory.GLq.CuspMultisetCount.card_le | (intros; apply GlobalTheory.GLq.CuspMultisetCount.card_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleMemLatticeOnKummerTowerGaloisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_mem_lattice_on_kummerTowerGalois : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ ϖ.GKinf → ∃ x : ↥T.L.T, actB (sQ l) T g b - b = (1 : OB l O) ⊗ₜ[O] x := by
  first | exact @GlobalTheory.CocycleKinf.cocycle_mem_lattice_of_mem_GKinf | exact GlobalTheory.CocycleKinf.cocycle_mem_lattice_of_mem_GKinf | (intros; apply GlobalTheory.CocycleKinf.cocycle_mem_lattice_of_mem_GKinf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousUnipotentColumnWhittakerTransform
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem continuous_colT_good : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → Continuous (colT ψ (m + 1) f) := by
  intro E _ _ a ψ hψ m f hf
  have hl : ∀ (c : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) g, f (ratGL E a (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g
  have key := GlobalTheory.T.continuous_quotientAverage_periodic_family (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) (GA E a)
    (fun p => ψ (-dot (eLast a (m + 1)) p.2) * f (blkU p.2 * p.1)) ?_ ?_
  · exact key
  · refine (hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul
      (hf.cont.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))
  · intro g γ hγ y
    exact (per_coef hψ (eLast a (m + 1)) hf.cont hl g).2 γ hγ y

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupProductFiniteClassesCoboundaryStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_product_finite_classes_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR (P.PD K) A.ρ → IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ a ∈ finiteCocycles (P.PD K) A.ρ, ∀ b ∈ finiteCocycles (P.PD K) A'.ρ, CobL (P.PD K) (cupL A'.ρ m a b) := by
  first | exact @GlobalTheory.BKOrth.bk_orth | exact GlobalTheory.BKOrth.bk_orth | (intros; apply GlobalTheory.BKOrth.bk_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbTypeUeIffLocalEmbeddingInCMHalfType
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TypeUeHalf

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), EmbeddingTypes.EmbTypeUe (i := i) (w := w) (hw := hw) ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ :=
  fun _ _ _ _ ep τ => GlobalTheory.SplitDecl.embTypeUe_iff ep τ

end GlobalTheory.TypeUeHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantLatticeMatrixOverBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_latticeMatrix_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T := by
  first | exact @GlobalTheory.BSP.equivariant_matrix_over_bk | exact GlobalTheory.BSP.equivariant_matrix_over_bk | (intros; apply GlobalTheory.BSP.equivariant_matrix_over_bk <;> assumption)
end

