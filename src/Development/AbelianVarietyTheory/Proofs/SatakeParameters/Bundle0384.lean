import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0014
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0121
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0222
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0039
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0353
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0366
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0355
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0374
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0382
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0369
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0376
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.X0OfStarCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplit
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CMFam

open IntermediateField

theorem exists_qcm_adjoin (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (p : ℕ) (hp : 0 < p) (δ : Ω) (hδ : δ ^ 2 = -(p : Ω))
    (hn : δ ∉ Set.range (algebraMap E Ω)) :
    ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} :=
  GlobalTheory.T.exists_cmQuadratic_adjoin_sqrt_neg_nat E Ω p hp δ hδ hn

theorem isSplitAt_of_dvd (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L) (hp : 0 < p)
    (hδ : δ ^ 2 = -(p : L)) (hq : ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1) (w : HeightOneSpectrum (𝓞 L))
    (hw : (q : 𝓞 L) ∈ w.asIdeal) : GlobalTheory.UnitaryBC.IsSplitAt w :=
  GlobalTheory.T.isSplitPlaceBelowCMField_of_sqrt_neg_prime L p q δ hp hδ hq w hw

theorem not_isUnramifiedAt (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (p : ℕ) (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (δ : K) (hδ : δ ^ 2 = -(p : K))
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal :=
  GlobalTheory.T.not_isUnramifiedAt_of_sq_eq_neg_prime E K p hp hd δ hδ w hw

theorem exists_unram (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra E K]
      (w : HeightOneSpectrum (𝓞 K)), (N : 𝓞 K) ∉ w.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) w.asIdeal :=
  GlobalTheory.T.exists_nat_unramified_over_maximalRealSubfield E

theorem even_finrank (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    (Q : GlobalTheory.RealGal.QCM E Ω) : Even (Module.finrank ℚ (maximalRealSubfield Q.K)) :=
  GlobalTheory.T.finrank_maximal_real_even E Ω Q

end GlobalTheory.CMFam

namespace GlobalTheory.CMFam

theorem dvd_of_mem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q n : ℕ} (hq : q.Prime)
    (hqw : (q : 𝓞 K) ∈ w.asIdeal) (hn : (n : 𝓞 K) ∈ w.asIdeal) : q ∣ n := by
  by_contra h
  have hc : Nat.gcd q n = 1 := (Nat.Prime.coprime_iff_not_dvd hq).2 h
  have hm : (((Nat.gcd q n : ℕ) : ℤ) : 𝓞 K) ∈ w.asIdeal := by
    rw [Nat.gcd_eq_gcd_ab q n]
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_right _ hqw) (w.asIdeal.mul_mem_right _ hn)
  rw [hc] at hm
  simp only [Nat.cast_one, Int.cast_one] at hm
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hm)

theorem natCast_mem_under {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : (n : 𝓞 E) ∈ (w.under (𝓞 E)).asIdeal ↔ (n : 𝓞 K) ∈ w.asIdeal := by
  change _ ∈ Ideal.comap _ _ ↔ _
  rw [Ideal.mem_comap, map_natCast]

end GlobalTheory.CMFam

open GlobalTheory.CMFam GlobalTheory.ExSplitCM in

theorem GlobalTheory.GalCut.infinite_qcm_split_good : AutomorphicFormsFiniteGL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)), {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, IsPlaceOver A w₀ → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P}.Infinite := by
  intro hAF E Ω _ _ _ _ _ _ l _ a π w₀
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have halg : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  obtain ⟨q₀, hq₀, hq₀w⟩ := exists_prime_mem w₀
  haveI : Fact q₀.Prime := ⟨hq₀⟩
  obtain ⟨N, hN0, hN⟩ := exists_unram E
  set S : Set (HeightOneSpectrum (𝓞 E)) := {v | ¬ ∃ B, (CG.mk π).HasSat v B} with hSdef
  have hS : S.Finite := Filter.eventually_cofinite.1 (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hAF E a π)
  set T : Finset ℕ := ({2, l, q₀} : Finset ℕ) ∪ N.primeFactors ∪ (discr E).natAbs.primeFactors ∪
    (finite_primes_of_finite hS).toFinset with hTdef
  set M : ℕ := 8 * ∏ q ∈ T, q with hM
  have hT2 : 2 ∈ T := by simp [hTdef]
  have hTl : l ∈ T := by simp [hTdef]
  have hTq₀ : q₀ ∈ T := by simp [hTdef]
  have hTN : ∀ r : ℕ, r.Prime → r ∣ N → r ∈ T := fun r hr hd => by
    simp [hTdef, Nat.mem_primeFactors, hr, hd, hN0]
  have hTd : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ T := fun r hr hd => by
    have : r ∈ (discr E).natAbs.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hr, Int.natCast_dvd.1 hd, Int.natAbs_ne_zero.2 (discr_ne_zero E)⟩
    simp [hTdef, this]
  have hTS : ∀ r : ℕ, r.Prime → ∀ v ∈ S, (r : 𝓞 E) ∈ v.asIdeal → r ∈ T := fun r hr v hv h => by
    have : r ∈ (finite_primes_of_finite hS).toFinset := by simpa using ⟨hr, v, hv, h⟩
    simp [hTdef, this]
  have hM0 : M ≠ 0 := by
    rw [hM]
    refine mul_ne_zero (by norm_num) ?_
    rw [Finset.prod_ne_zero_iff]
    intro q hq h0
    subst h0
    simp [hTdef] at hq
    rcases hq with h | h | h
    · exact (Fact.out : l.Prime).ne_zero h.symm
    · exact hq₀.ne_zero h.symm
    · exact Nat.not_prime_zero h.1
  haveI : NeZero M := ⟨hM0⟩
  have hsq : ∀ p : ℕ, ∃ δ : Ω, δ ^ 2 = -(p : Ω) := fun p =>
    IsAlgClosed.exists_pow_nat_eq (-(p : Ω)) two_pos
  choose δ hδ using hsq
  set Gd : Set ℕ := {p | p.Prime ∧ p ∉ T ∧ (M : ℤ) ∣ (p : ℤ) + 1} with hGd
  have hGood : Gd.Infinite := by
    refine ((Nat.infinite_setOfPred_prime_and_eq_mod (q := M) isUnit_one.neg).diff T.finite_toSet).mono ?_
    rintro p ⟨⟨hp, hpe⟩, hpT⟩
    refine ⟨hp, hpT, ?_⟩
    have : (((p : ℤ) + 1 : ℤ) : ZMod M) = 0 := by push_cast; rw [hpe]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have h8 : ∀ p ∈ Gd, ∀ q ∈ T, ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 := fun p hp q hq => by
    refine dvd_trans ?_ hp.2.2
    rw [Int.natCast_dvd_natCast, hM]
    exact Nat.mul_dvd_mul_left 8 (Finset.dvd_prod_of_mem _ hq)
  have hodd : ∀ p ∈ Gd, p ≠ 2 := fun p hp h => hp.2.1 (h ▸ hT2)
  have hdisc : ∀ p ∈ Gd, ¬ (p : ℤ) ∣ discr E := fun p hp h => hp.2.1 (hTd p hp.1 h)
  have hmove : ∀ p ∈ Gd, ∀ (u : HeightOneSpectrum (𝓞 E)) (A' : ValuationSubring Ω), ((p : ℕ) : 𝓞 E) ∈ u.asIdeal →
      IsPlaceOver A' u → ∃ s ∈ Ine (F := E) A', s (δ p) ≠ δ p := fun p hp u A' hu hA' =>
    GlobalTheory.SqrtNegRam.sqrt_neg_moved_by_inertia E Ω p hp.1 (hodd p hp) (hdisc p hp) (δ p) (hδ p) u A' hu hA'
  have hnot : ∀ p ∈ Gd, δ p ∉ Set.range (algebraMap E Ω) := by
    rintro p hp ⟨x, hx⟩
    obtain ⟨u, hu⟩ := exists_mem_of_prime (F := E) hp.1
    obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
    obtain ⟨s, -, hs⟩ := hmove p hp u A' hu hA'
    exact hs (by rw [← hx]; exact s.commutes x)
  have hQ : ∀ p ∈ Gd, ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ p} := fun p hp =>
    exists_qcm_adjoin E Ω p hp.1.pos (δ p) (hδ p) (hnot p hp)
  have hmem : ∀ p ∈ Gd, ∀ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ p} →
      Q ∈ {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, IsPlaceOver A w₀ → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P} := by
    intro p hp Q hQK
    have hδK : δ p ∈ Q.K := by rw [hQK]; exact IntermediateField.mem_adjoin_simple_self E (δ p)
    set y : ↥Q.K := ⟨δ p, hδK⟩ with hy
    have hy2 : y ^ 2 = -(p : ↥Q.K) := Subtype.ext (by simpa using hδ p)
    have hsplit : ∀ q ∈ T, ∀ w : HeightOneSpectrum (𝓞 ↥Q.K), (q : 𝓞 ↥Q.K) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w :=
      fun q hq w hw => isSplitAt_of_dvd _ p q y hp.1.pos hy2 (h8 p hp q hq) w hw
    refine ⟨fun A hA s hs => ?_, fun w hw => ?_, ?_, fun P hP => ?_⟩
    · rw [mem_range_res_iff, hQK]
      refine fix_adjoin (halg.isAlgebraic (δ p)).isIntegral s ?_
      exact GlobalTheory.SqFix.sqrt_fixed_of_isSquare_padic E Ω w₀ A hA q₀ hq₀w (-(p : ℤ)) (δ p)
        (by push_cast; exact hδ p)
        (by push_cast; exact GlobalTheory.RealGal.PrimesNegSquare.isSquare_neg_of_dvd q₀ p (h8 p hp q₀ hTq₀)) s hs
    · refine hsplit q₀ hTq₀ w ?_
      rw [← natCast_mem_under (E := E), hw]
      exact hq₀w
    · obtain ⟨w, hw⟩ := exists_mem_of_prime (F := ↥Q.K) hp.1
      refine ⟨w, not_isUnramifiedAt E ↥Q.K p hp.1 (hdisc p hp) y hy2 w hw, ?_⟩
      by_contra hB
      exact hp.2.1 (hTS p hp.1 _ hB ((natCast_mem_under w p).2 hw))
    · refine ⟨⟨y, p, hp.1.pos, by rw [hy2]⟩, even_finrank E Ω Q, fun w hw => ?_⟩
      obtain ⟨q, hq, hqw⟩ := exists_prime_mem w
      have hqT : q ∉ T := fun h => hw (hsplit q h w hqw)
      refine ⟨fun hl => hqT (prime_eq_of_mem w (Fact.out : l.Prime) hq hl hqw ▸ hTl), ?_, ?_⟩
      · refine hN ↥Q.K w fun h => hqT (hTN q hq (dvd_of_mem w hq hqw h))
      · have hB : ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B := by
          by_contra hB
          exact hqT (hTS q hq _ hB ((natCast_mem_under w q).2 hqw))
        obtain ⟨B, hB⟩ := hB
        exact ⟨_, hP.sat w _ B (GlobalTheory.RealGal.AttRes.normV_eq_pow w) hB⟩
  intro hfin
  apply hGood
  refine (hfin.biUnion (t := fun Q : GlobalTheory.RealGal.QCM E Ω => {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 E) |
      ¬ ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Ine (F := E) A' ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range},
      ((p : ℕ) : 𝓞 E) ∈ u.asIdeal})
    fun Q _ => finite_primes_of_finite (Filter.eventually_cofinite.1 (UpperTheory.cm_inertia_restriction_holds E ↥Q.K Ω))).subset ?_
  intro p hp
  obtain ⟨Q, hQK⟩ := hQ p hp
  refine Set.mem_biUnion (hmem p hp Q hQK) ⟨hp.1, ?_⟩
  obtain ⟨u, hu⟩ := exists_mem_of_prime (F := E) hp.1
  obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  refine ⟨u, fun hall => ?_, hu⟩
  obtain ⟨s, hs, hne⟩ := hmove p hp u A' hu hA'
  refine hne ((mem_range_res_iff Q.K s).1 (hall A' hA' hs) (δ p) ?_)
  rw [hQK]
  exact IntermediateField.mem_adjoin_simple_self E (δ p)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfContragredientConjugate
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.ContraPair.SphTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem conjFin_locGL_mem (w : HeightOneSpectrum (𝓞 E))
    (hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w) (k : GL (Fin a) (w.adicCompletion E))
    (hk : k ∈ GlobalTheory.LFun.KGL w a) : ∃ k' ∈ GlobalTheory.LFun.KGL w a,
      Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a w k) = locGL E a w k' := by
  have key : ∀ u (h : conjSrc (IsCMField.complexConj E).toRingEquiv w = u) (k : GL (Fin a) (u.adicCompletion E)),
      k ∈ GlobalTheory.LFun.KGL u a → ∃ k' ∈ GlobalTheory.LFun.KGL w a,
        Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a u k) = locGL E a w k' := by
    intro u h k hk
    subst h
    refine ⟨_, ?_, GlobalTheory.ConjPairLoc.conjFin_locGL _ w k⟩
    obtain ⟨k0, rfl⟩ := hk
    let r : Formalism.UG.Ov E (conjSrc (IsCMField.complexConj E).toRingEquiv w) →+* Formalism.UG.Ov E w :=
      (conjLoc (IsCMField.complexConj E).toRingEquiv w).restrict _ _ fun x hx => by
        change _ ∈ w.adicCompletionIntegers E
        change x ∈ (conjSrc (IsCMField.complexConj E).toRingEquiv w).adicCompletionIntegers E at hx
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
        rw [(conjLoc_spec _ w).2.2]
        exact hx
    refine ⟨Matrix.GeneralLinearGroup.map r k0, ?_⟩
    ext i j
    rfl
  exact key w hw k hk

end GlobalTheory.ContraPair.SphTwist

open GlobalTheory.ContraPair.SphTwist in

theorem GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy π ψ → ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ψ⁻¹).locRep w) (GlobalTheory.LFun.KGL w a) := by
  intro E _ _ _ a _ π ψ hP w hns hS
  obtain ⟨B0, hB0⟩ := hS
  obtain ⟨B, -, hB2, hfin, -, -⟩ := hP
  have hsat : GlobalTheory.LFun.HasSatGL w (π.locRep w) B0 := (CG.hasSat_mk π w B0).1 hB0
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
  obtain ⟨y, hy⟩ : ∃ y, B y x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (hB2 x h)
  have hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w := by
    by_contra h
    exact hns ⟨_, h, GlobalTheory.DefU.LocRet.under_conjSrc w⟩
  have hL : ∀ k ∈ GlobalTheory.LFun.KGL w a, B.flip x ((π.twist ψ⁻¹).locRep w k y) = B.flip x y := by
    intro k hk
    obtain ⟨k', hk', e⟩ := conjFin_locGL_mem w hw k hk
    have hx' : π.op (.fin (locGL E a w k')) x = x := GlobalTheory.LGrp.mem_fixed.1 hx k' hk'
    have h1 := hfin (locGL E a w k) y x
    change B ((π.twist ψ⁻¹).op (.fin (locGL E a w k)) y) x = B y x
    conv_lhs => rw [← hx']
    rw [← e]
    exact h1
  obtain ⟨v, hv, hve⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq ((π.twist ψ⁻¹).isSmooth_locRep w)
    GlobalTheory.BcSpehCompare.isCompact_KGL (B.flip x) y hL
  refine (Submodule.ne_bot_iff _).2 ⟨v, hv, fun h => hy ?_⟩
  have : B.flip x v = B y x := hve
  rw [← this, h, map_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedFormsOperatorDegreesAtKernelSource
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

set_option maxHeartbeats 4000000 in

theorem moved_forms_at_source : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std), ∀ j < D.R.m, Nonempty (Lv.comp (j + 1)) → ∀ (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) (gmS d) j ∧ TieOpS (Y := S.Y) t u μ (clsAt X H) (gmS d) (sO d ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j) ∧ KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPos ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  intro d j hjm hne hN
  have hj : j ≤ D.R.m := hjm.le
  have h : ((sysS H X std).Pj j).m + 1 = D.R.N j := rkS _ _ hN
  have hWt := GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j hjm hne
  have hPT := (posTie_at S hPos ι hι).1
  have hdg : ∀ τ, (t.O u μ).dgen τ ≠ 0 := by
    intro τ h0
    have h1 := GlobalTheory.T.norm_derivation_generators_eq_one_at_site S ι hι τ
    rw [h0, map_zero, norm_zero] at h1
    exact zero_ne_one h1
  have hV : ∀ (j : ℕ) (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j),
      ((sysS H X std).Pj j).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat j).V, ∃ V : XR ((sysS H X std).Pj j) ℂ,
        MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp j x La.1 La.2) =
          MvPolynomial.map ι V ∧ RealAt d j hj h La ((ex.tw.fm u μ).emb j x) V := by
    intro j
    cases j with
    | zero => intro hj h La hL x; exact GlobalTheory.T.comparedForm_levelZero_realises_complexPoly S hDict hPos ι hι d h La hL x
    | succ k => intro hj h La hL x; exact GlobalTheory.T.comparedForm_normalisedValues_latticeTuple S hDict hPos ι hι d k hj h La hL x
  have core : ∀ La ∈ S.Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) Q, K2.SharpQ t ex.tw u μ j x Q →
      GoodG (sysS H X std) ℂ_[D.what₂.places.resChar w] j (gmS d j La x) ∧ OddDeg (sysS H X std) j (gmS d j La x) ∧
      ∀ n, MvPolynomial.coeff n (polDel (sysS H X std) ℂ_[D.what₂.places.resChar w] j (gmS d j La x)) =
        ι (sPt d j hj La * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) •
          MvPolynomial.coeff n (trDY (sysS H X std) ℂ_[D.what₂.places.resChar w] j D (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)
            (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j) (polDY D (t.O u μ).dgen (Q (clsAt X H j La.1 La.2)) (N' := D.R.N (j + 1)))) := by
    intro La hLa x Q hQ
    have hL := S.Y.Rep_lat j La hLa
    obtain ⟨V, hVm, hVr⟩ := hV j hj h La hL x
    have hFr := GlobalTheory.T.changedFrame_rational_unitary S d j hj h La
    have hmap := gmOf_map_eq_actC (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) hPT d.fd2 j La h
      (mM d j hj La) hFr.1 hFr.2.1 _ V hVm
    have hφ : ∀ y, (ex.tw.fm u μ).emb j x (clsAt X H j La.1 La.2) y =
        (∏ τ, (D.chTw u μ).de j y τ ^ (D.chTw u μ).sSharp j τ)⁻¹ * frPoly (t.O u μ) j (Q (clsAt X H j La.1 La.2)) y := by
      intro y
      have h2 := congrFun (hQ.2 (clsAt X H j La.1 La.2)) y
      have hne : (∏ τ, (D.chTw u μ).de j y τ ^ (D.chTw u μ).sSharp j τ) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((D.chTw u μ).de_ne j y τ)
      rw [← h2]
      simp only [ColumnChain.sharp, mulFun, LinearMap.coe_mk, AddHom.coe_mk]
      field_simp
    have hR := (GlobalTheory.T.kernelSite_valuesAtPoint_iff_realisesInStdCoords S d j hj h La ((D.chTw u μ).sSharp j) ((ex.tw.fm u μ).emb j x) (Q (clsAt X H j La.1 La.2)) hφ V).1 hVr
    have hw : (fun τ => (D.chTw u μ).sSharp j τ - cTw D j) = wT (sysS H X std) D (hT.gat_pos u w hg) j :=
      funext fun τ => (hWt.sh τ).symm
    rw [hw] at hR
    exact GlobalTheory.T.operatorPolynomial_of_realising_value (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι j hN (nuT D u j) hWt.nu
      (Q (clsAt X H j La.1 La.2)) (hQ.1 _) (sPt d j hj La) _ (gmS d j La x) hR hmap (t.O u μ).dgen hdg
  refine ⟨fun La hLa x => ?_, fun La hLa x Q hQ n => ?_, fun La hLa x Q hQ α hα => ?_⟩
  · obtain ⟨Q, hQ⟩ := J.sharp j hjm x
    obtain ⟨h1, h2, -⟩ := core La hLa x Q hQ
    exact ⟨GlobalTheory.T.naturalAction_inverseFrame_undoes_move (sysS H X std) D (hT.gat_pos u w hg) d.fd2 j La _, h1, h2⟩
  · rw [(core La hLa x Q hQ).2.2 n]
    simp only [sO, dif_pos hj]
  · exact polDY_goodDeg (sysS H X std) D (hT.gat_pos u w hg) j hN (nuT D u j) hWt.nu _ (hQ.1 _) _ α hα

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalCodimOneStalkDvr
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut

namespace GlobalTheory.RoadW

theorem sphAt_of_repIso {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : CuspSub E a) {r r' : G E Ω →* GL (Fin a) (Qbar l)}
    (hr : Continuous r) (hiso : UpperTheory.V.Af.RepIso r r') (c : GlobalTheory.RoadU.Sph) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (hc : GlobalTheory.RoadU.SphAt c π ι r w B) : GlobalTheory.RoadU.SphAt c π ι r' w B := by
  cases c with
  | unr =>
    obtain ⟨p, hp⟩ := hiso
    intro hl A hA
    obtain ⟨h1, h2⟩ := hc hl A hA
    refine ⟨fun s hs => by rw [hp, h1 s hs]; group, fun σ hσ => ?_⟩
    rw [← h2 σ hσ, hp, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  | dR => exact clauseAt_of_repIso E Ω l ι a π r r' hr hiso .dR w hc
  | crys => exact clauseAt_of_repIso E Ω l ι a π r r' hr hiso .crys w hc
  | phi =>
    obtain ⟨p, hp⟩ := hiso
    have hcd : ∀ (A : ValuationSubring Ω) (g : ↥(Dec (F := E) A)), r'.comp (Dec (F := E) A).subtype g =
        p * r.comp (Dec (F := E) A).subtype g * p⁻¹ := fun A g => hp g
    intro P AI hT A h O _ _ _ Bw hj g
    have e := GlobalTheory.AboveL.RepConj.wdAt_conj P ι Bw h hj p (hcd A)
    exact (congrArg (fun x => WD.charPol x g) e).trans (hc P AI hT A h O Bw hj g)

theorem core_of_rowStarCore : GlobalTheory.RoadW.RowStarCore → GlobalTheory.RoadU.Core := by
  intro h
  refine ⟨fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hs => ?_, fun c E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w _ B hB => ?_⟩
  · obtain rfl : χ = quadChar E ^ a := hs.2.2.2
    obtain ⟨r, hr, -⟩ := h E Ω l ι a ha π hs
    exact ⟨r, hr⟩
  · obtain rfl : χ = quadChar E ^ a := hs.2.2.2
    obtain ⟨r₀, hr₀, hc⟩ := h E Ω l ι a ha π hs
    refine sphAt_of_repIso ι π hr₀.1 (weak_repIso E Ω l ι a π r₀ r hr₀ hr) c w B ?_
    obtain ⟨h1, h2, h3, h4⟩ := hc w B hB
    cases c
    exacts [h1, h2, h3, h4]

end GlobalTheory.RoadW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairSatakeParameterConjugatePlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.PolarizedSat

theorem hasSat_conjPlace : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), GlobalTheory.ContraPair.PolarizedPair π χ → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B → (CG.mk π).HasSat (UpperTheory.V.Af.Bc.cPl w) (B.map fun α => α⁻¹ * (compNorm E χ).val w) := by
  intro hF E _ _ _ a π χ hpol
  have hu : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, (compNorm E χ).UnrAt w :=
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified _)
  have hs : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk π).HasSat (UpperTheory.V.Af.Bc.cPl w) B :=
    (conjSrc_injective _).tendsto_cofinite.eventually (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π)
  filter_upwards [hu, hs] with w hw hB'e B hB
  obtain ⟨B', hB'⟩ := hB'e
  have e := UpperTheory.V.Br.satOfPol E a π _ hpol.dual w hw B B' hB hB'
  have e2 : B' = B.map fun α => α⁻¹ * (compNorm E χ).val w := by
    have e3 := congrArg (Multiset.map fun z : ℂˣ => z⁻¹) e
    rw [Multiset.map_map, Multiset.map_map] at e3
    simp only [Function.comp_def, inv_inv, Multiset.map_id'] at e3
    rw [e3]
    exact Multiset.map_congr rfl fun α _ => by rw [mul_inv_rev, inv_inv, mul_comm]
  rw [← e2]
  exact hB'

end GlobalTheory.PolarizedSat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticHeckeCharUnramifiedOfIsUnramifiedAt
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.QuadCharUnr

theorem quadChar_unrAt_of_isUnramifiedAt (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w : HeightOneSpectrum (𝓞 E)) (hw : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    (quadChar E).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E)))
    · exact GlobalTheory.LFun.isUnram_of_isSplit h2 hs
    · refine GlobalTheory.LFun.isUnram_iff.2 fun u hu => ?_
      obtain rfl := GlobalTheory.LFun.eq_of_not_isSplit hs hu rfl
      haveI := u.isPrime
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 hw
  intro x hx
  have hn := GlobalTheory.LFun.mem_normGroup_of_isUnram h2 hu hx
  change Units.map _ (GlobalTheory.IdeleNormChar.normSign E (localIdele _ _ x)) = 1
  rw [GlobalTheory.LFun.normSign_localIdele, GlobalTheory.QuadSymbol.eta_eq_one_iff.2 hn, map_one]

end GlobalTheory.QuadCharUnr
end

