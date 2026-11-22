import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0619
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0626
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0622

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedActionEqTwistedCoefficientsCocycleIffStatement
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff : ∀ {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X]
    (χ : G →* Oˣ),
    (∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m) ∧
    ∀ z : G → ↥L.T ⊗[O] X, tableLineDegreeTwo.IsCoc L X χ z ↔ z ∈ Z1 (twCoef (latRep L) χ X) ⊤ := by
  first | exact @GlobalTheory.actTw_eq_twCoef_and_isCoc_iff | exact GlobalTheory.actTw_eq_twCoef_and_isCoc_iff | (intros; apply GlobalTheory.actTw_eq_twCoef_and_isCoc_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedTorsionClassTheoremGoodCase
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.TheoremTB

theorem tb_assembled : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    admitted D HW F → Conclusion5 D → Conclusion4 D HW F := by
  intro D HW F hA h5 l _ K s LL h
  exact ⟨GlobalTheory.T.crystalline_extension_class_bound D HW F hA l K s LL h, GlobalTheory.T.weight_good_reduction_at_prime D HW F hA h5 l K s LL h⟩

end GlobalTheory.TheoremTB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeFamilyPotentiallyCrystallineCommonTameExtensStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeFamily_potentiallyCrystalline_common_tame_extension : StepPotDirect := by
  first | exact @GlobalTheory.PotDirect.main | exact GlobalTheory.PotDirect.main | (intros; apply GlobalTheory.PotDirect.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedHomsBoundedByClassNumberOfArtin
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.UnramifiedHomBound

noncomputable def homToH1 {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (U : Submodule O (G → M)) (hU : ∀ c ∈ U, ∀ g h, c (g * h) = c g + c h) :
    U →ₗ[O] NG.H1z (Representation.trivial O G M) :=
  (Submodule.mkQ _).comp (Submodule.inclusion
    (show U ≤ NG.coZ1s (Representation.trivial O G M) from fun c hc g h => by simpa using hU c hc g h))

theorem homToH1_injective {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (U : Submodule O (G → M)) (hU : ∀ c ∈ U, ∀ g h, c (g * h) = c g + c h) :
    Function.Injective (homToH1 U hU) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).1 hc
  apply Subtype.ext
  funext g
  have h := congrFun hv g
  have h2 : NG.coD0 (Representation.trivial O G M) v g = 0 := by simp [NG.coD0]
  exact h.symm.trans h2

theorem homToH1_mem_unrH1 {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (U : Submodule O (G → M)) (hU : ∀ c ∈ U, ∀ g h, c (g * h) = c g + c h) (I : Subgroup G)
    (c : U) (hc : ∀ g ∈ I, (c : G → M) g = 0) :
    homToH1 U hU c ∈ RepresentationBoundsCohomology.BR.unrH1 (Representation.trivial O G M) I := by
  change NG.resH1 (Representation.trivial O G M) I (Submodule.Quotient.mk _) = 0
  rw [NG.resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  have h : NG.restrictCocycles1 (Representation.trivial O G M) I (Submodule.inclusion
      (show U ≤ NG.coZ1s (Representation.trivial O G M) from fun c hc g h => by simpa using hU c hc g h) c)
      = 0 := Subtype.ext (funext fun g => hc g g.2)
  rw [h]
  exact Submodule.zero_mem _

theorem l_ne_zero (D : D7) (i : D.nd.Loc) : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 := by
  have : CharZero (FractionRing (D.nd.O i)) :=
    charZero_of_injective_ringHom (D.nd.embK i).injective
  intro h
  have h2 := congrArg (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) h
  rw [map_natCast, map_zero] at h2
  exact (Fact.out : (D.nd.l i).Prime).ne_zero (Nat.cast_eq_zero.1 h2)

theorem length_unrHom_le (h : ReciprocityTheory.ChartRestriction.T2.VhE) (D : D7) (i : D.nd.Loc) :
    Module.length (D.nd.O i) ↥(TruncatedSeriesCountingIdentities.unrHom i) ≤
      Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)}) *
        (padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ∞) := by
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  have hU : ∀ c ∈ TruncatedSeriesCountingIdentities.unrHom i, ∀ g h, c (g * h) = c g + c h := fun c hc => hc.2.1
  rw [(LinearEquiv.ofInjective _ (homToH1_injective _ hU)).length_eq]
  refine h D.host.E D.nd.Om D.nd.plOm.1 D.nd.plOm.2 (D.nd.l i) (D.nd.O i)
    (Or.inr (IsTotallyComplex.nrRealPlaces_eq_zero _)) (KmodO (D.nd.O i))
    ⟨Submodule.quotEquivOfEq _ _ (Submodule.one_eq_range).symm⟩ _ (fun _ _ => rfl) _ ?_ ?_
  · rintro _ ⟨c, rfl⟩
    exact ⟨_, rfl, c.2.1⟩
  · rintro v _ ⟨c, rfl⟩
    exact homToH1_mem_unrH1 _ hU _ c (c.2.2.2 v)

theorem unramified_homs_bounded_by_class_number_of_artin :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i := by
  intro hA D i
  have h := length_unrHom_le (GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity hA) D i
  have hfin : Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)}) ≠ ⊤ :=
    Module.length_ne_top_iff.2
      (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero (l_ne_zero D i)))
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 hfin
  have hlt : Module.length (D.nd.O i) ↥(TruncatedSeriesCountingIdentities.unrHom i) < ⊤ := by
    refine lt_of_le_of_lt h ?_
    rw [← he, ← Nat.cast_mul]
    exact ENat.natCast_lt_top _
  refine ⟨hlt, ?_⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hlt.ne
  rw [← he, ← hn, ← Nat.cast_mul, Nat.cast_le] at h
  unfold lenUnit
  rw [← he, ← hn, ENat.toNat_natCast, ENat.toNat_natCast]
  refine div_le_of_le_mul₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _) ?_
  rw [mul_comm]
  exact_mod_cast h

end GlobalTheory.UnramifiedHomBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumpsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattice_heights_from_hodgeJumps : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P5 D HW F := by
  first | exact @GlobalTheory.NL.Heights.heights_from_jumps | exact GlobalTheory.NL.Heights.heights_from_jumps | (intros; apply GlobalTheory.NL.Heights.heights_from_jumps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeUsedPropertiesOfAdmittedStatement
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattice_usedProperties_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), tableLineDegreeTwo.admitted D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), GlobalTheory.WachUse.QN ((HW l).W K 1 LL hA.2.2) := by
  first | exact @GlobalTheory.WachQN.qN_of_admitted | exact GlobalTheory.WachQN.qN_of_admitted | (intros; apply GlobalTheory.WachQN.qN_of_admitted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotient
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachModulePoleQuotient

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem wachModule_consequences_poleQuotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), gammaSemisimpleQuotientGlobal D HW F := by
  intro D HW F Cm
  unfold gammaSemisimpleQuotientGlobal gammaSemisimpleLocal GammaSemisimpleQuotient
  intro l _ K s LL h T hT y hy
  classical
  have hfr := GlobalTheory.T.wachModule_inverseQuotient_free_finite_crystalline D HW F l K s LL h T hT y
  have hJ := GlobalTheory.T.crystallineLattice_hodgeTateJumps_finite D HW l K s LL h T hT
  let Fs : Finset (↥(OL LL))ˣ := (hJ.toFinset ×ˢ Finset.Icc 1 y).image
    (fun p : ℤ × ℕ => uU ((HW l).W K s LL h) ^ (-(p.1 + (p.2 : ℤ))))
  have hmem : ∀ c, c ∈ Fs ↔ ∃ a ∈ Jumps (PD := (D.loc l).PD K) T, ∃ j : ℕ, 1 ≤ j ∧ j ≤ y ∧
      c = uU ((HW l).W K s LL h) ^ (-(a + j)) := by
    intro c
    simp only [Fs, Finset.mem_image, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_Icc,
      Prod.exists]
    constructor
    · rintro ⟨a, j, ⟨ha, h1, h2⟩, rfl⟩
      exact ⟨a, ha, j, h1, h2, rfl⟩
    · rintro ⟨a, ha, j, h1, h2, rfl⟩
      exact ⟨a, j, ⟨ha, h1, h2⟩, rfl⟩
  refine ⟨hfr.1, hfr.2, Fs, ?_, ?_, ?_⟩
  · ext c
    exact hmem c
  · intro x hx
    exact GlobalTheory.T.prod_gamma_sub_jump_units_annihilates_quotient D HW F Cm l K s LL h T hT y hy Fs
      (fun a ha j h1 h2 => (hmem _).2 ⟨a, ha, j, h1, h2, rfl⟩) x hx
  · intro c hc
    obtain ⟨a, ha, j, h1, h2, rfl⟩ := (hmem c).1 hc
    obtain ⟨x, hx, hxN, hγ⟩ := GlobalTheory.T.gamma_eigenvalue_on_wachLattice_qPower_quotient D HW F Cm l K s LL h T hT y hy a ha j h1 h2
    exact ⟨x, hx, hxN, hγ⟩

end GlobalTheory.NL.WachModulePoleQuotient
end

