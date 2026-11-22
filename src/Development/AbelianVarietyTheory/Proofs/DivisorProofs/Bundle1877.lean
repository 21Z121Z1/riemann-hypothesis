import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryBlockLevelUnitBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCutOperatorsMirabolicFinitePlaces
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin GlobalTheory.SmGL

theorem cuts_mir {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ)
    (hψ : IsLocallyConstant ψ) (hψ1 : ψ ≠ 1) (m : ℕ) (U : Subgroup (GL (Fin (m + 1)) F))
    (hUc : IsCompact (U : Set (GL (Fin (m + 1)) F))) (hUo : IsOpen (U : Set (GL (Fin (m + 1)) F)))
    (z : GL (Fin (m + 1)) F) : Cuts ψ (U : Set (GL (Fin (m + 1)) F)) (cell z (U : Set (GL (Fin (m + 1)) F)))
      {p | lr p = lr 1} := by
  induction m with
  | zero =>
    classical
    have h1 : ∀ q : GL (Fin (0 + 1)) F, lr q = lr 1 → q = 1 := fun q hq => by
      obtain ⟨h, x, rfl⟩ := exists_mir hq
      rw [Subsingleton.elim h 1, Subsingleton.elim x 0, mir_one]
    refine ⟨Finsupp.single 1 (if (1 : GL (Fin (0 + 1)) F) ∈ cell z (U : Set (GL (Fin (0 + 1)) F)) then 1 else 0),
      fun f _ _ g hg => ?_⟩
    rw [h1 g hg, act_single, mul_one]
    by_cases h : (1 : GL (Fin (0 + 1)) F) ∈ cell z (U : Set (GL (Fin (0 + 1)) F))
    · rw [if_pos h, one_mul, Set.indicator_of_mem h]
    · rw [if_neg h, zero_mul, Set.indicator_of_notMem h]
  | succ m ih =>
    refine GlobalTheory.T.mirabolic_cutoffs_of_restriction_cutoffs ψ hψ hψ1 m (GlobalTheory.T.exists_whittakerCut_inductionStep_of_open_subgroup ψ hψ hψ1 m (fun V hVc hVo z' => ?_)) U hUc hUo z
    refine GlobalTheory.T.whittakerIndicatorCut_mul_open_subgroup ψ V hVo _ _ (fun x hx u hu => ?_) (ih V hVc hVo z')
    obtain ⟨n, hn, k, hk, rfl⟩ := hx
    exact ⟨n, hn, k * u, V.mul_mem hk hu, by rw [mul_assoc]⟩

end GlobalTheory.JSW.Cut

open GlobalTheory.JSW.Cut in

theorem GlobalTheory.JSW.MirPatch.cut_operators : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (n : ℕ) (h : Fin n → GA E (m + 1)) (c : Fin n → ℂ), (∀ i, h i ∈ GlobalTheory.JSW.supS E (m + 1) S) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, ∑ i, c i * W (p * h i) = (GlobalTheory.JSW.MirPatch.cell K q).indicator W p := by
  intro E _ _ _ m S K hKo hKc q
  classical
  obtain ⟨U, N, z, hU, hdisj, hchar⟩ := GlobalTheory.T.mirabolic_cell_finite_union_local_double_cosets E m S K hKo hKc q
  choose ψ hψv hψl hψ1 using GlobalTheory.T.finitePlace_standardChar_locallyConstant_nontrivial E
  have hcut : ∀ i : Fin N, ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS E (m + 1) S ∧
      GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
      (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ GlobalTheory.JSW.mirS E S m,
      act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈
        GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
    intro i
    refine GlobalTheory.T.composite_cut_operators_product_local_cells_mirabolic E m S ψ hψv K U (z i) (fun w hw => (hU w hw).2.2) fun w hw => ?_
    haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
    haveI : IsUltrametricDist (w.adicCompletion E) :=
      inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
        (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)
    exact cuts_mir (ψ w) (hψl w) (hψ1 w) m (U w) (hU w hw).1 (hU w hw).2.1 (z i w)
  choose T hTs hT using hcut
  obtain ⟨n, h, c, hh, he⟩ := exists_fin (∑ i, T i)
  refine ⟨n, h, c, fun j => ?_, fun W hW hWK p hp => ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum (hh j))
    exact (hTs i _ hi).1
  · rw [← he, act_finset_sum]
    simp_rw [fun i => hT i W hW hWK p hp]
    by_cases hc : p ∈ GlobalTheory.JSW.MirPatch.cell K q
    · obtain ⟨i, hi⟩ := (hchar p hp).1 hc
      rw [Set.indicator_of_mem hc, Finset.sum_eq_single i]
      · exact Set.indicator_of_mem (s := {x : GA E (m + 1) | _}) hi _
      · intro j _ hj
        exact Set.indicator_of_notMem (s := {x : GA E (m + 1) | _}) (fun hj' => hj (hdisj p hp j i hj' hi)) _
      · simp
    · rw [Set.indicator_of_notMem hc]
      refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (s := {x : GA E (m + 1) | _}) (fun hi => hc ((hchar p hp).2 ⟨i, hi⟩)) _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualBasesIsotropicSubspacesDuality
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.IsoDuality

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_herm (V : Formalism.BasicNotions.HSpace E) (x y : V.V) : star (V.hT x y) = V.hT y x := by
  have := V.herm.eq x y
  rw [← starRingEnd_apply]; exact this

theorem iso_zero (V : Formalism.BasicNotions.HSpace E) {W : Submodule E V.V} (hW : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W)
    {w v : V.V} (hw : w ∈ W) (hv : v ∈ W) : V.hT w v = 0 := by
  have := hW hv
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
  exact this w hw

theorem finrank_le_of_sep (V : Formalism.BasicNotions.HSpace E) (A B : Submodule E V.V)
    (h : ∀ y ∈ B, (∀ x ∈ A, V.hT x y = 0) → y = 0) :
    Module.finrank E B ≤ Module.finrank E A := by
  classical
  let bA := Module.finBasis E A
  let Φ : B →ₗ[E] (Fin (Module.finrank E A) → E) :=
    LinearMap.pi (fun i => (V.hT (bA i : V.V)).comp B.subtype)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, V.hT (bA i : V.V) y = 0 := fun i => congrFun hy i
    apply Subtype.ext
    apply h y y.2
    intro x hx
    have hx' : (⟨x, hx⟩ : A) = ∑ i, (bA.repr ⟨x, hx⟩ i) • bA i := (bA.sum_repr _).symm
    have : x = ∑ i, (bA.repr ⟨x, hx⟩ i) • (bA i : V.V) := by
      calc x = ((∑ i, (bA.repr ⟨x, hx⟩ i) • bA i : A) : V.V) := by rw [← hx']
        _ = _ := by simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [this, map_sum]
    simp [map_smulₛₗ, hy']
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

end GlobalTheory.IsoDuality

namespace GlobalTheory.IsoDuality

theorem exists_dual_bases : ∀ {D : D7} {V : HSp D} (X X' : Submodule D.host.E V.V), X ≠ ⊥ → X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X → X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' → (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) → (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) → ∃ (a : ℕ) (x x' : Fin a → V.V), 0 < a ∧ a ≤ wittIndex V ∧ Submodule.span D.host.E (Set.range x) = X ∧ Submodule.span D.host.E (Set.range x') = X' ∧ LinearIndependent D.host.E (Sum.elim x x') ∧ (∀ i j, V.hD (x i) (x j) = 0) ∧ (∀ i j, V.hD (x' i) (x' j) = 0) ∧ (∀ i j, V.hD (x i) (x' j) = if i = j then 1 else 0) := by
  classical
  intro D V X X' hX0 hX hX' h1 h2
  have hTX := fun {w v : V.V} (hw : w ∈ X) (hv : v ∈ X) => iso_zero V hX hw hv
  have hTX' := fun {w v : V.V} (hw : w ∈ X') (hv : v ∈ X') => iso_zero V hX' hw hv

  have hle1 : Module.finrank D.host.E X ≤ Module.finrank D.host.E X' :=
    finrank_le_of_sep V X' X (fun y hy h => h1 y hy (fun z hz => h z hz))
  have hle2 : Module.finrank D.host.E X' ≤ Module.finrank D.host.E X :=
    finrank_le_of_sep V X X' (fun y hy h => h2 y hy (fun z hz => by
      show V.hT y z = 0
      rw [← hT_herm, h z hz, star_zero]))
  set a := Module.finrank D.host.E X with ha
  let bx := Module.finBasis D.host.E X
  let x : Fin a → V.V := fun i => (bx i : V.V)
  have hxX : ∀ i, x i ∈ X := fun i => (bx i).2
  let Φ : X' →ₗ[D.host.E] (Fin a → D.host.E) :=
    LinearMap.pi (fun i => (V.hT (x i)).comp X'.subtype)
  have hΦ : ∀ y i, Φ y i = V.hT (x i) y := fun y i => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, V.hT (x i) y = 0 := fun i => congrFun hy i
    apply Subtype.ext
    apply h2 y y.2
    intro z hz
    have hz' : (⟨z, hz⟩ : X) = ∑ i, (bx.repr ⟨z, hz⟩ i) • bx i := (bx.sum_repr _).symm
    have : z = ∑ i, (bx.repr ⟨z, hz⟩ i) • x i := by
      calc z = ((∑ i, (bx.repr ⟨z, hz⟩ i) • bx i : X) : V.V) := by rw [← hz']
        _ = _ := by simp only [Submodule.coe_sum, Submodule.coe_smul]; rfl
    show V.hT (y : V.V) z = 0
    rw [← hT_herm, this, map_sum]
    simp [map_smulₛₗ, hy']
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hinj
    · simp [a]; omega
  choose g hg using fun j : Fin a => hsurj (Pi.single j 1)
  let x' : Fin a → V.V := fun j => (g j : V.V)
  have hx'X : ∀ j, x' j ∈ X' := fun j => (g j).2
  have hxx' : ∀ i j, V.hT (x i) (x' j) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (hg j) i
    rw [hΦ] at this
    show V.hT (x i) (g j : V.V) = _
    rw [this, Pi.single_apply]
  have hxli : LinearIndependent D.host.E x :=
    bx.linearIndependent.map' X.subtype (Submodule.ker_subtype X)
  have hli : LinearIndependent D.host.E (Sum.elim x x') := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fintype.sum_sum_type] at hc
    simp only [Sum.elim_inl, Sum.elim_inr] at hc
    have hd : ∀ k, c (Sum.inr k) = 0 := by
      intro k
      have := congrArg (V.hT (x k)) hc
      rw [map_add, map_sum, map_sum, map_zero] at this
      simp only [map_smul, smul_eq_mul, hTX (hxX k) (hxX _), mul_zero, Finset.sum_const_zero,
        zero_add, hxx', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
      exact this
    have hc' : ∑ i, c (Sum.inl i) • x i = 0 := by
      simpa [hd] using hc
    have hcl := Fintype.linearIndependent_iff.1 hxli _ hc'
    rintro (i | j)
    · exact hcl i
    · exact hd j
  have hx'li : LinearIndependent D.host.E x' := hli.comp Sum.inr Sum.inr_injective
  refine ⟨a, x, x', ?_, ?_, ?_, ?_, hli, ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (fun h => hX0 (Submodule.finrank_eq_zero.1 h))
  · exact GlobalTheory.Cusp.finrank_le_wittIndex hX
  · have : Set.range x = X.subtype '' Set.range bx := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bx.span_eq, Submodule.map_top, Submodule.range_subtype]
  · apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; rintro _ ⟨j, rfl⟩; exact hx'X j
    · rw [finrank_span_eq_card hx'li]; simp [a]; omega
  · intro i j
    show V.hT (x j) (x i) = 0
    exact hTX (hxX j) (hxX i)
  · intro i j
    show V.hT (x' j) (x' i) = 0
    exact hTX' (hx'X j) (hx'X i)
  · intro i j
    show V.hT (x' j) (x i) = _
    rw [← hT_herm, hxx']
    split_ifs <;> simp

end GlobalTheory.IsoDuality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumOfHeisenbergLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

open Matrix

namespace GlobalTheory.HeisLatVac

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At Acts)

theorem exists_local_vac {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ) (hc : Continuous ψ₀) (hne : ψ₀ ≠ 1)
    (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (ho : IsOpen (Λ : Set ((κ → Fv F v) × (κ → Fv F v))))
    (hk : IsCompact (Λ : Set ((κ → Fv F v) × (κ → Fv F v))))
    (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (h0 : χ 0 = 1)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : Fv F v) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (h2 : ∀ u ∈ Λ, χ (u + u) = 1) :
    ∃ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ ≠ 0 ∧ ∀ u ∈ Λ, GlobalTheory.WeilM.schr ψ₀ u φ = χ u • φ := by
  have hsq : ∀ u ∈ Λ, χ u * χ u = 1 := fun u hu => by
    have e := hco u hu u hu
    rw [h2 u hu, sub_self, mul_zero, AddChar.map_zero_eq_one, mul_one] at e
    exact e.symm
  have hiso : ∀ u ∈ Λ, ∀ w ∈ Λ, ψ₀ (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) = 1 := by
    intro u hu w hw
    have e1 := hco u hu w hw
    have e2 := hco w hw u hu
    rw [add_comm w u, e1, mul_comm (χ w) (χ u)] at e2
    have hne0 : χ u * χ w ≠ 0 :=
      mul_ne_zero (left_ne_zero_of_mul_eq_one (hsq u hu)) (left_ne_zero_of_mul_eq_one (hsq w hw))
    set a := ⅟(2 : Fv F v) * (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) with ha_def
    have ha : ⅟(2 : Fv F v) * (w.1 ⬝ᵥ u.2 - u.1 ⬝ᵥ w.2) = -a := by rw [ha_def]; ring
    rw [ha] at e2
    have e3 : ψ₀ a = ψ₀ (-a) := mul_left_cancel₀ hne0 e2
    have e4 : u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2 = a + a := by
      rw [ha_def, ← two_mul, ← mul_assoc, mul_invOf_self, one_mul]
    rw [e4, AddChar.map_add_eq_mul]
    calc ψ₀ a * ψ₀ a = ψ₀ (-a) * ψ₀ a := congrArg (· * ψ₀ a) e3
      _ = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  let L : AddSubgroup (κ → Fv F v) := Λ.comap (AddMonoidHom.inr (κ → Fv F v) (κ → Fv F v))
  let L' : AddSubgroup (κ → Fv F v) := Λ.comap ((AddMonoidHom.inr (κ → Fv F v) (κ → Fv F v)).comp
    (DistribMulAction.toAddMonoidHom (κ → Fv F v) (⅟(2 : Fv F v))))
  have hL : IsCompact (L : Set (κ → Fv F v)) := by
    have e : (L : Set (κ → Fv F v)) = Prod.snd '' ((Λ : Set ((κ → Fv F v) × (κ → Fv F v))) ∩ {u | u.1 = 0}) := by
      ext y
      constructor
      · intro hy
        exact ⟨(0, y), ⟨hy, rfl⟩, rfl⟩
      · rintro ⟨u, ⟨hu, hu1⟩, rfl⟩
        have : u = (0, u.2) := Prod.ext hu1 rfl
        show (0, u.2) ∈ Λ
        rw [← this]; exact hu
    rw [e]
    exact (hk.inter_right (isClosed_eq continuous_fst continuous_const)).image continuous_snd
  have hL' : IsOpen (L' : Set (κ → Fv F v)) := by
    rw [AddSubgroup.coe_comap]
    exact ho.preimage (continuous_const.prodMk (continuous_const.smul continuous_id))
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.exists_dotProduct_representation_compact_character_local v ψ₀ hc hne L hL L' hL' (fun y => χ (0, y))
    (fun y hy y' hy' => by
      have e := hco _ hy _ hy'
      simp only [AddMonoidHom.inr_apply, Prod.mk_add_mk, add_zero, zero_dotProduct, sub_self, mul_zero,
        AddChar.map_zero_eq_one, mul_one] at e
      exact e)
    (fun y hy hy' => by
      have e := h2 _ hy'
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inr_apply,
        DistribMulAction.toAddMonoidHom_apply, Prod.mk_add_mk, add_zero] at e
      rwa [← add_smul, invOf_two_add_invOf_two, one_smul] at e)
  have hx : ∀ y : κ → Fv F v, ((0 : κ → Fv F v), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y) := fun y hy => hx₀ y hy
  refine ⟨vacFn ψ₀ Λ χ x₀, ⟨GlobalTheory.T.isLocallyConstant_heisenberg_lattice_vacuum_function v ψ₀ hc Λ ho χ x₀ hco hx h2, GlobalTheory.T.heisenbergLatticeVacuumFn_hasCompactSupport v ψ₀ Λ χ x₀ hk⟩, ?_,
    GlobalTheory.T.schroedingerOperator_heisenbergLatticeVacuum_eigen ψ₀ Λ χ x₀ hco hx hiso⟩
  intro h
  have e := GlobalTheory.T.heisenbergLatticeVacuumFn_apply_add ψ₀ Λ χ x₀ hco hx 0 (zero_mem _)
  simp only [Prod.fst_zero, Prod.snd_zero, add_zero, dotProduct_zero, neg_zero, mul_zero, sub_zero,
    AddChar.map_zero_eq_one, h0, mul_one, h, Pi.zero_apply] at e
  exact zero_ne_one e

end GlobalTheory.HeisLatVac

namespace GlobalTheory.HeisLatVac

theorem exists_vac_of_lattice : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), Continuous ψ → GlobalTheory.LatVac.psiAt ψ v ≠ 1 →
    ∀ Γ : AddSubgroup W, (∀ γ ∈ Γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ) →
    (∀ a ∈ v.adicCompletionIntegers F, ∀ γ ∈ Γ, GlobalTheory.LatVac.liftV v a • γ ∈ Γ) →
    IsOpen ((Γ.map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
    IsCompact ((Γ.map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ c : W → ℂ, c 0 = 1 → (∀ γ ∈ Γ, ∀ γ' ∈ Γ, c (γ + γ') = c γ * c γ' * ψ (⅟(2 : AF F) * B γ γ')) →
    (∀ γ ∈ Γ, c (GlobalTheory.LatVac.liftV v 2 • γ) = 1) →
    ∃ φ : (κ → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ ∧ φ ≠ 0 ∧
      ∀ γ ∈ Γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (co.rho ψ γ) φ (c γ • φ) := by
  intro F _ _ W _ _ B κ _ co ψ v hψc hψ1 Γ hAt _hO hopen hcomp c hc0 hcoc hc2
  have hsupp : ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a →
      a = GlobalTheory.LatVac.liftV v (GlobalTheory.AdelicU.evFin F v a) := by
    intro a ha
    have h1 := ha (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
    conv_lhs => rw [h1]
    exact GlobalTheory.EmbChart.atPlace_mul_right v 1 a |>.trans (by rw [one_mul]; rfl)
  have hψloc : ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a →
      ψ a = GlobalTheory.LatVac.psiAt ψ v (GlobalTheory.AdelicU.evFin F v a) := by
    intro a ha
    conv_lhs => rw [hsupp a ha]
    rfl
  have hAtE : ∀ γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ → ∀ k,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e γ).1 k) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e γ).2 k) := by
    intro γ hγ k
    have e : ∀ u : AF F, GlobalTheory.AdelicU.evFin F v u = 0 → u • co.e γ = 0 := fun u hu => by
      rw [← LinearEquiv.map_smul, hγ u hu, map_zero]
    exact ⟨fun u hu => by simpa using congrArg (fun p => p.1 k) (e u hu),
      fun u hu => by simpa using congrArg (fun p => p.2 k) (e u hu)⟩
  have hinj : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, GlobalTheory.LatVac.locCo co v γ = GlobalTheory.LatVac.locCo co v γ' → γ = γ' := by
    intro γ hγ γ' hγ' h
    have hδ := hAt _ (sub_mem hγ hγ')
    have h0 : GlobalTheory.LatVac.locCo co v (γ - γ') = 0 := by rw [map_sub, h, sub_self]
    have he : co.e (γ - γ') = 0 := by
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · rw [hsupp _ (hAtE _ hδ k).1]
        have := congrFun (congrArg Prod.fst h0) k
        change GlobalTheory.AdelicU.evFin F v ((co.e (γ - γ')).1 k) = 0 at this
        rw [this, map_zero]; rfl
      · rw [hsupp _ (hAtE _ hδ k).2]
        have := congrFun (congrArg Prod.snd h0) k
        change GlobalTheory.AdelicU.evFin F v ((co.e (γ - γ')).2 k) = 0 at this
        rw [this, map_zero]; rfl
    rw [LinearEquiv.map_eq_zero_iff, sub_eq_zero] at he
    exact he
  classical
  let χ : (κ → Fv F v) × (κ → Fv F v) → ℂ := fun u =>
    if h : ∃ γ ∈ Γ, GlobalTheory.LatVac.locCo co v γ = u then c h.choose else 0
  have hχ : ∀ γ ∈ Γ, χ (GlobalTheory.LatVac.locCo co v γ) = c γ := by
    intro γ hγ
    have h : ∃ γ' ∈ Γ, GlobalTheory.LatVac.locCo co v γ' = GlobalTheory.LatVac.locCo co v γ := ⟨γ, hγ, rfl⟩
    simp only [χ, dif_pos h]
    rw [hinj _ h.choose_spec.1 _ hγ h.choose_spec.2]
  have hcont : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hψc v
  obtain ⟨φ, hSB, hne, heig⟩ := exists_local_vac v (GlobalTheory.LatVac.psiAt ψ v) hcont hψ1
    (Γ.map (GlobalTheory.LatVac.locCo co v)) hopen hcomp χ
    (by rw [← map_zero (GlobalTheory.LatVac.locCo co v), hχ 0 (zero_mem _), hc0])
    (by
      rintro _ ⟨γ, hγ, rfl⟩ _ ⟨γ', hγ', rfl⟩
      rw [← map_add, hχ _ (add_mem hγ hγ'), hχ _ hγ, hχ _ hγ', hcoc γ hγ γ' hγ']
      congr 1
      have hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (⅟(2 : AF F) * B γ γ') := by
        rw [co.form]
        refine GlobalTheory.VacAny.at_mul_left _ (GlobalTheory.VacAny.at_sub ?_ ?_)
        · exact GlobalTheory.VacAny.at_sum _ fun i _ => GlobalTheory.VacAny.at_mul_left _ (hAtE _ (hAt _ hγ') i).2
        · exact GlobalTheory.VacAny.at_sum _ fun i _ => GlobalTheory.VacAny.at_mul_left _ (hAtE _ (hAt _ hγ) i).2
      rw [hψloc _ hA, co.form, map_mul, GlobalTheory.VacAny.evFin_invOf_two, map_sub]
      simp only [dotProduct, map_sum, map_mul]
      rfl)
    (by
      rintro _ ⟨γ, hγ, rfl⟩
      rw [← map_add, hχ _ (add_mem hγ hγ)]
      have e : γ + γ = GlobalTheory.LatVac.liftV v 2 • γ := by
        have h := hAt γ hγ (GlobalTheory.LatVac.liftV v 2 - 2)
          (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_ofNat, sub_self])
        rw [sub_smul, sub_eq_zero, two_smul] at h
        exact h.symm
      rw [e]
      exact hc2 γ hγ)
  refine ⟨φ, hSB, hne, fun γ hγ => ?_⟩
  have hb := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger co ψ v γ (hAt γ hγ) φ
  rwa [heig _ (AddSubgroup.mem_map_of_mem _ hγ), hχ γ hγ] at hb

end GlobalTheory.HeisLatVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomeomorphColumnFixatorCoreUnitaryGroupStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homeomorph_columnFixator_coreUnitaryGroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ e : GAd σ J₀ ≃ₜ* (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), ∀ g, g ∈ ratPts σ J₀ ↔ (e g : GAd σ J) ∈ ratPts σ J := by
  first | exact @GlobalTheory.SphEis.fixFrames_equiv_core | exact GlobalTheory.SphEis.fixFrames_equiv_core | (intros; apply GlobalTheory.SphEis.fixFrames_equiv_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPartnerSplittingSelfDualLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hyperbolicPartner_splitting_selfDualLattice : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x : S.V),
    IsSelfDualC S Λ → x ≠ 0 → S.hT x x = 0 →
    ∃ y : S.V, S.hT y y = 0 ∧ S.hT x y = 1 ∧
      ∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y) := by
  first | exact @GlobalTheory.HypPairSelfDual.exists_partner | exact GlobalTheory.HypPairSelfDual.exists_partner | (intros; apply GlobalTheory.HypPairSelfDual.exists_partner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryBlockLevelUnitBlockStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralUnitary_blockLevel_unitBlock : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ {a d : ℕ}, a ≤ d →
    ∀ h ∈ intG D d, (∀ i j : Fin d, j.1 < a → a ≤ i.1 →
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪) →
    ∃ k ∈ intG D a, ∀ i j, (((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * (unitBlock D 0 a d).map (inc D) -
      (unitBlock D 0 a d).map (inc D) * (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
        hatId D 𝔪 := by
  first | exact @GlobalTheory.FunObj.StdDatum.BlockPoint.exists_intG_unitBlock | exact GlobalTheory.FunObj.StdDatum.BlockPoint.exists_intG_unitBlock | (intros; apply GlobalTheory.FunObj.StdDatum.BlockPoint.exists_intG_unitBlock <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealTrivialPointFiniteAdelicHomEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq : ∀ {D : D7} (V : HSp D) (M : GL (Fin V.rank) (Lev.EAf D)), M ∈ UA D.sp.cm V.gram → ∃ g : GfC V, finG V g = M := by
  first | exact @GlobalTheory.FrameTransport.exists_finG_eq | exact GlobalTheory.FrameTransport.exists_finG_eq | (intros; apply GlobalTheory.FrameTransport.exists_finG_eq <;> assumption)
end

