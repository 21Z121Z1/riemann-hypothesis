import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0633
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0678
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormPlaceLeOfFrobenius
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory
namespace NormLeFrob

theorem valuation_algebraMap_le_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (x : 𝓞 E) :
    A.valuation (algebraMap E Ω (x : E)) ≤ 1 := by
  have h1 : IsIntegral ℤ (algebraMap E Ω (x : E)) := (x.2).map (IsScalarTower.toAlgHom ℤ E Ω)
  have h2 : IsIntegral A (algebraMap E Ω (x : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact A.valuation_le_one y

noncomputable def toResidue {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) : 𝓞 E →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp
    { toFun := fun x => ⟨algebraMap E Ω (x : E), (A.valuation_le_one_iff _).mp (valuation_algebraMap_le_one A x)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }

theorem toResidue_eq_zero_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hw : IsPlaceOver A w) (x : 𝓞 E) :
    toResidue A x = 0 ↔ x ∈ w.asIdeal := by
  rw [← hw x]
  simp only [toResidue, RingHom.coe_comp, Function.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]

theorem toResidue_isRoot {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (q : ℕ) (σ : G E Ω) (hσ : IsFrob A q σ) (x : 𝓞 E) :
    (X ^ q - X : (IsLocalRing.ResidueField A)[X]).IsRoot (toResidue A x) := by
  have hx := valuation_algebraMap_le_one A x
  have h := hσ.2 _ hx
  rw [AlgEquiv.commutes] at h
  have hmem : (⟨algebraMap E Ω (x : E), (A.valuation_le_one_iff _).mp hx⟩ : A) ^ q
      - ⟨algebraMap E Ω (x : E), (A.valuation_le_one_iff _).mp hx⟩ ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    rw [← Valuation.map_neg]
    convert h using 2
    simp
  rw [← IsLocalRing.residue_eq_zero_iff] at hmem
  simp only [IsRoot, eval_sub, eval_pow, eval_X]
  have e : toResidue A x = IsLocalRing.residue A
      ⟨algebraMap E Ω (x : E), (A.valuation_le_one_iff _).mp hx⟩ := rfl
  rw [e, ← map_pow, ← map_sub]
  exact hmem

theorem normV_le_of_isFrob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ q : ℕ, 1 < q → ∀ σ : G E Ω, IsFrob A q σ → normV w ≤ q := by
  intro E Ω _ _ _ _ A w hw q hq σ hσ
  classical
  set k := IsLocalRing.ResidueField A
  set P : k[X] := X ^ q - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hq
  let f : 𝓞 E ⧸ w.asIdeal →+* k :=
    Ideal.Quotient.lift w.asIdeal (toResidue A) (fun x hx => (toResidue_eq_zero_iff A w hw x).mpr hx)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (toResidue_eq_zero_iff A w hw x).mp ha
  let g : 𝓞 E ⧸ w.asIdeal → {y : k // y ∈ P.roots.toFinset} := fun a =>
    ⟨f a, by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Multiset.mem_toFinset, mem_roots hP0]
      exact toResidue_isRoot A q σ hσ x⟩
  have hg : Function.Injective g := fun a b h => hf (congrArg Subtype.val h)
  calc normV w = Nat.card (𝓞 E ⧸ w.asIdeal) := rfl
    _ ≤ Nat.card {y : k // y ∈ P.roots.toFinset} := Nat.card_le_card_of_injective g hg
    _ = P.roots.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ = q := FiniteField.X_pow_card_sub_X_natDegree_eq k hq

end NormLeFrob
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesAStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedTrivialH1f_of_decl : ∀ (D : D7) (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i), Formalism.MainNotions.EmbeddingTypes.UnramifiedTrivialH1f (D := D) i dc := by
  first | exact @GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces | exact GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces | (intros; apply GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoHypothesisGlobalStepAtQdStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoHypothesis_globalStep_at_qd : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := by
  first | exact @GlobalTheory.BKAtQD.admBK_embeddingTypeJumps | exact GlobalTheory.BKAtQD.admBK_embeddingTypeJumps | (intros; apply GlobalTheory.BKAtQD.admBK_embeddingTypeJumps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterEqProdSupercuspidalSupportStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralCharacter_eq_prod_supercuspidalSupport : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k) (s : Multiset (IrrGL k)) (ω : kˣ →* ℂˣ), HasSupport x.rep s → HasCentralChar x.rep ω → ∃ f : IrrGL k → kˣ →* ℂˣ, (∀ y ∈ s, HasCentralChar y.rep (f y)) ∧ ∀ z, ω z = (s.map fun y => f y z).prod := by
  first | exact @GlobalTheory.CentralSupport.centralChar_eq_prod_support | exact GlobalTheory.CentralSupport.centralChar_eq_prod_support | (intros; apply GlobalTheory.CentralSupport.centralChar_eq_prod_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryDeRhamOfCoboundarySemistableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_deRham_of_coboundary_semistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (c : ↥(GK K) → V) (z : V ⊗[ℚ_[l]] Bst P), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b := by
  first | exact @GlobalTheory.cocycle_dies_dR_of_dies_st | exact GlobalTheory.cocycle_dies_dR_of_dies_st | (intros; apply GlobalTheory.cocycle_dies_dR_of_dies_st <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionBaseChangePlacesStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_base_change_places : ∀ (E L E' L' : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [Field E'] [NumberField E'] [Field L'] [NumberField L'] [Algebra E' L'] (w : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 L)) (w' : HeightOneSpectrum (𝓞 E')) (v' : HeightOneSpectrum (𝓞 L')) (j : E →+* E') (jL : L →+* L') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) x ∈ v.asIdeal ↔ x ∈ w.asIdeal) → (∀ x : 𝓞 E', algebraMap (𝓞 E') (𝓞 L') x ∈ v'.asIdeal ↔ x ∈ w'.asIdeal) → (∀ x : 𝓞 L, RingOfIntegers.mapRingHom jL x ∈ v'.asIdeal ↔ x ∈ v.asIdeal) → (∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x)) → Algebra.adjoin E' (Set.range jL) = ⊤ → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∃ iL : v.adicCompletion L ≃+* v'.adicCompletion L', Continuous iL ∧ ∀ x, iL (algebraMap L _ x) = algebraMap L' _ (jL x) := by
  first | exact @GlobalTheory.CompositumCompletion.exists_ringEquiv_completion | exact GlobalTheory.CompositumCompletion.exists_ringEquiv_completion | (intros; apply GlobalTheory.CompositumCompletion.exists_ringEquiv_completion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalFieldIso

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem continuous_symm (i : k ≃+* k') (hi : Continuous i) : Continuous i.symm := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k')
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous

variable (k) in

theorem valuation_le_one_iff_ord (x : kˣ) : valuation k (x : k) ≤ 1 ↔ 0 ≤ GlobalTheory.SmGL.ord k x := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (x : k)) ≠ 0 := by simp
  rw [GlobalTheory.SmGL.ord, neg_nonneg, ← φ.strictMono.le_iff_le, map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  simp [φ]

variable (k) in

theorem valuation_le_one_iff_nabs (x : kˣ) : valuation k (x : k) ≤ 1 ↔ GlobalTheory.SplitWeil.nabs k x ≤ 1 := by
  rw [valuation_le_one_iff_ord, GlobalTheory.LGrp.nabs_eq_zpow,
    zpow_le_one_iff_right₀ (by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k)]
  omega

theorem nabs_map (i : k ≃+* k') (hi : Continuous i) (x : kˣ) :
    GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x :=
  GlobalTheory.SplitWeil.nabs_map_of_homeomorph i hi (continuous_symm i hi) x

theorem valuation_map_le_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := valuation_le_one_iff_nabs k' (Units.map i.toRingHom.toMonoidHom (Units.mk0 x hx))
  rw [nabs_map i hi, ← valuation_le_one_iff_nabs k] at h
  simpa using h

theorem map_integer (i : k ≃+* k') (hi : Continuous i) :
    (𝒪[k] : Subring k).map i.toRingHom = 𝒪[k'] := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Valuation.mem_integer_iff _ _).2 ((valuation_map_le_one_iff i hi x).2 ((Valuation.mem_integer_iff _ _).1 hx))
  · intro hy
    refine ⟨i.symm y, (Valuation.mem_integer_iff _ _).2 ?_, i.apply_symm_apply y⟩
    rw [← valuation_map_le_one_iff i hi, RingEquiv.apply_symm_apply]
    exact (Valuation.mem_integer_iff _ _).1 hy

theorem resCard_eq (i : k ≃+* k') (hi : Continuous i) : GlobalTheory.SplitWeil.resCard k' = GlobalTheory.SplitWeil.resCard k := by
  let e : 𝒪[k] ≃+* 𝒪[k'] := (i.subringMap (s := 𝒪[k])).trans (RingEquiv.subringCongr (map_integer i hi))
  exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv).symm

theorem ord_map (i : k ≃+* k') (hi : Continuous i) (x : kˣ) :
    GlobalTheory.SmGL.ord k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SmGL.ord k x := by
  have h := nabs_map i hi x
  rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, resCard_eq i hi] at h
  have hq : (1 : ℝ) < GlobalTheory.SplitWeil.resCard k := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k
  exact neg_inj.1 (zpow_right_injective₀ (by linarith) hq.ne' h)

theorem absPow_map (i : k ≃+* k') (hi : Continuous i) (s : ℂ) (x : kˣ) :
    GlobalTheory.SmGL.absPow k' s (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SmGL.absPow k s x := by
  ext
  rw [GlobalTheory.SmGL.val_absPow, GlobalTheory.SmGL.val_absPow, nabs_map i hi]

end GlobalTheory.LocalFieldIso

theorem GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → Continuous i.symm ∧ (∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) ∧ (∀ x : kˣ, ord k' (Units.map i.toRingHom.toMonoidHom x) = ord k x) ∧ resCard k' = resCard k ∧ ∀ (s : ℂ) (x : kˣ), absPow k' s (Units.map i.toRingHom.toMonoidHom x) = absPow k s x := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  exact ⟨GlobalTheory.LocalFieldIso.continuous_symm i hi, GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi,
    GlobalTheory.LocalFieldIso.ord_map i hi, GlobalTheory.LocalFieldIso.resCard_eq i hi, GlobalTheory.LocalFieldIso.absPow_map i hi⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConvolutionSingleFactorGoodProjectorEqZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_singleFactor_goodProjector_eq_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (eR : G ≃* G0g D.nd) (kv0 : Σ k : Fin 2, D.nd.PlG k),
    haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
    ∀ M : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv0.1))),
    (∀ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) →
      M * D.ntypes.eSer kv0.1 (Formalism.CyclotomicNorms.monicOf (a kv0)) = 0) → ∀ x : G,
    ∑ y : G, (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then M.coeff (eR y kv0) else 0) *
      D.ntypes.e0.coeff (eR (y⁻¹ * x)) = 0 := by
  first | exact @GlobalTheory.DownLift.conv_single_goodProj_eq_zero | exact GlobalTheory.DownLift.conv_single_goodProj_eq_zero | (intros; apply GlobalTheory.DownLift.conv_single_goodProj_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CountableDoubledHermitianLagrangiansStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.countable_doubled_hermitian_lagrangians : ∀ (D : D7) (W : HSp D), Countable (Lag W) := by
  first | exact @GlobalTheory.RawLift.lag_countable | exact GlobalTheory.RawLift.lag_countable | (intros; apply GlobalTheory.RawLift.lag_countable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharactersGivenJumpsUnramifiedTwists
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.CrysCharJumps

open Classical

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l)

def HasJumps (χ : ↥(GK K) →* (↥(OL LL))ˣ) (f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ) : Prop :=
  Continuous (fun g => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ g : (↥LL.1)ˣ) : ↥LL.1)) ∧
    IsCrys (P.PD K) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)) ∧
    ∀ τ b, multV (P.PD K) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)) τ b = if b = f τ then 1 else 0

variable {P K LL}

theorem charL_val (χ : ↥(GK K) →* (↥(OL LL))ˣ) (g : ↥(GK K)) :
    ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ g : (↥LL.1)ˣ) : ↥LL.1) =
      algebraMap ↥(OL LL) ↥LL.1 ((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) := rfl

theorem isJumpV_of_multV_ne {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ) (h : multV (P.PD K) ρ τ b ≠ 0) :
    IsJumpV (P.PD K) ρ τ b := by
  intro he
  apply h
  unfold multV
  rw [he]
  simp

theorem hasJumps_one (hT : LocTied l P AI) : HasJumps P K LL 1 0 := by
  have hc : Continuous (fun g => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (1 : ↥(GK K) →* (↥(OL LL))ˣ) g : (↥LL.1)ˣ) : ↥LL.1)) := by
    simp only [charL_val, MonoidHom.one_apply, Units.val_one, map_one]
    exact continuous_const
  obtain ⟨h1, h2⟩ := GlobalTheory.T.unramifiedChar_isCrystalline_hodgeTate_zero l P AI hT K LL (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) 1) hc
    (fun g _ => by ext; simp [charL_val])
  exact ⟨hc, h1, fun τ b => by rw [h2]; rfl⟩

theorem hasJumps_mul (hT : LocTied l P AI) {χ ψ : ↥(GK K) →* (↥(OL LL))ˣ}
    {f g : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ} (hχ : HasJumps P K LL χ f) (hψ : HasJumps P K LL ψ g) :
    HasJumps P K LL (χ * ψ) (f + g) := by
  have htw : IsTwistRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)
      (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) ψ)) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (χ * ψ))) := by
    refine ⟨LinearEquiv.refl _ _, fun x y => ?_⟩
    simp [charRep, charL_val, mul_smul]
  obtain ⟨hc, hm⟩ := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l P AI hT K LL ↥LL.1
    (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) ψ)) ↥LL.1
    (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (χ * ψ))) (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ) htw hχ.2.1 hψ.2.1
  refine ⟨?_, hc, fun τ b => ?_⟩
  · have : (fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (χ * ψ) x : (↥LL.1)ˣ) : ↥LL.1)) =
        fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ x : (↥LL.1)ˣ) : ↥LL.1) *
          ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) ψ x : (↥LL.1)ˣ) : ↥LL.1) := by
      funext x
      simp [charL_val]
    rw [this]
    exact hχ.1.mul hψ.1
  · have hj : IsJumpV (P.PD K) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)) τ (f τ) :=
      isJumpV_of_multV_ne _ τ (f τ) (by rw [hχ.2.2]; simp)
    have := hm τ (b - f τ) (f τ) hj
    rw [sub_add_cancel] at this
    rw [this, hψ.2.2]
    simp only [Pi.add_apply]
    split_ifs <;> omega

theorem hasJumps_inv (hT : LocTied l P AI) {χ : ↥(GK K) →* (↥(OL LL))ˣ}
    {f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ} (hχ : HasJumps P K LL χ f) :
    HasJumps P K LL χ⁻¹ (-f) := by
  have he : Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ⁻¹ = (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)⁻¹ := by
    refine MonoidHom.ext fun x => ?_
    simp only [Formalism.MainNotions.tableLineDegreeTwo.charL, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isCrys_inv_and_hodgeTate_jumps_neg l P AI hT K LL (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ) f hχ.2.1 hχ.2.2
  refine ⟨?_, he ▸ h1, fun τ b => by rw [he, h2]; rfl⟩
  have : (fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ⁻¹ x : (↥LL.1)ˣ) : ↥LL.1)) =
      (fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ x : (↥LL.1)ˣ) : ↥LL.1)) ∘ (fun x => x⁻¹) := by
    funext x
    simp only [Function.comp_apply, charL_val, MonoidHom.inv_apply, map_inv]
  rw [this]
  exact hχ.1.comp continuous_inv

theorem hasJumps_zpow (hT : LocTied l P AI) {χ : ↥(GK K) →* (↥(OL LL))ˣ}
    {f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ} (hχ : HasJumps P K LL χ f) (k : ℤ) :
    HasJumps P K LL (χ ^ k) (k • f) := by
  induction k using Int.induction_on with
  | zero =>
    rw [zpow_zero, zero_smul]
    exact hasJumps_one AI hT
  | succ k ih =>
    rw [zpow_add_one, add_smul, one_smul]
    exact hasJumps_mul AI hT ih hχ
  | pred k ih =>
    rw [zpow_sub_one, sub_smul, one_smul, sub_eq_add_neg]
    exact hasJumps_mul AI hT ih (hasJumps_inv AI hT hχ)

theorem hasJumps_prod (hT : LocTied l P AI)
    (ψ : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → (↥(GK K) →* (↥(OL LL))ˣ))
    (hψ : ∀ τ₀, HasJumps P K LL (ψ τ₀) (fun τ => if τ = τ₀ then 1 else 0))
    (c : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ) (s : Finset (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) :
    HasJumps P K LL (∏ τ ∈ s, ψ τ ^ c τ) (fun τ => if τ ∈ s then c τ else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    convert hasJumps_one AI hT using 1
    funext τ
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    convert hasJumps_mul AI hT (hasJumps_zpow AI hT (hψ a) (c a)) ih using 1
    funext τ
    by_cases h : τ = a
    · subst h
      simp [ha]
    · simp [h]

end GlobalTheory.CrysCharJumps

open GlobalTheory.CrysCharJumps Classical in

theorem GlobalTheory.CrysCharJumps.adm20_of_fonOf :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.tableLineDegreeTwo.adm20 D HW F := by
  intro D HW F l _ K LL hA
  refine ⟨fun a => ?_, ?_⟩
  · classical
    choose ψ hψ using fun τ₀ => GlobalTheory.T.exists_crystalline_char_jump_one_alt l (D.loc l) (D.locA l) (D.locT l) K LL hA τ₀
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    haveI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    let c : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ := fun τ =>
      if h : ∃ i, Formalism.MainNotions.tableLineDegreeTwo.Over ((HW l).W K 1 LL hA.2.2).emb i τ then a h.choose else 0
    have hp := hasJumps_prod (D.locA l) (D.locT l) ψ (fun τ₀ => hψ τ₀) c Finset.univ
    refine ⟨∏ τ, ψ τ ^ c τ, hp.1, hp.2.1, fun i τ hi b => ?_⟩
    rw [hp.2.2]
    have hex : ∃ i, Formalism.MainNotions.tableLineDegreeTwo.Over ((HW l).W K 1 LL hA.2.2).emb i τ := ⟨i, hi⟩
    have hc : c τ = a i := by
      simp only [c, dif_pos hex]
      congr 1
      apply ((HW l).W K 1 LL hA.2.2).emb_bij.1
      have h1 := hex.choose_spec
      unfold Formalism.MainNotions.tableLineDegreeTwo.Over at h1 hi
      exact h1.symm.trans hi
    simp [hc]
  · intro V _ _ _ _ _ _ _ ρ ρ' μ hρc hρ hμc hμI hρ'
    obtain ⟨hμcr, hμm⟩ := GlobalTheory.T.unramifiedChar_isCrystalline_hodgeTate_zero l (D.loc l) (D.locA l) (D.locT l) K LL μ hμc hμI
    have htw : IsTwistRep μ ρ ρ' := ⟨LinearEquiv.refl _ _, fun g x => by simp [hρ' g]⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) (D.locT l) K LL
      V ρ V ρ' μ htw hμcr hρ
    refine ⟨h1, fun τ x => ?_⟩
    have hj : IsJumpV ((D.loc l).PD K) (charRep μ) τ 0 :=
      isJumpV_of_multV_ne _ τ 0 (by rw [hμm]; simp)
    simpa using h2 τ x 0 hj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteSpaceFormsFunctionalPrincipalTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteSpace_forms_functional_principalType : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ),
      HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (fun h => l (R.extV i t y h)) := by
  first | exact @GlobalTheory.DefiniteType.hasType_extV | exact GlobalTheory.DefiniteType.hasType_extV | (intros; apply GlobalTheory.DefiniteType.hasType_extV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetHeckeSumPreservesPrincipalFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_levW_mul_heckeOn_mem_wall : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (γ : GA D (Wc D i)), γ ∈ GfC (Wc D i) → ∃ C : Finset (GA D (Wc D i)), C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ levW R i, δ = k * γ) ∧ ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  first | exact @GlobalTheory.TransSum.heckeOn_doubleCoset_mem_wall | exact GlobalTheory.TransSum.heckeOn_doubleCoset_mem_wall | (intros; apply GlobalTheory.TransSum.heckeOn_doubleCoset_mem_wall <;> assumption)
end

