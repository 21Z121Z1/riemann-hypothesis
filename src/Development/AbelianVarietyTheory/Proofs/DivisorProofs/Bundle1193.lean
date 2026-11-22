import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1153
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicCuspFormOfAdelicConstantTermsZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterPolyEqZeroOfIsHomogeneousNeDimStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interPoly_eq_zero_of_isHomogeneous_ne_dim : ∀ (F : Type) [Field F] (Y : Var F) (κ : Type) (gr : κ → Y.Dv) (k : ℕ) (P : MvPolynomial κ ℝ), P.IsHomogeneous k → k ≠ Y.dim → Y.interPoly gr P = 0 := by
  first | exact @GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous | exact GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous | (intros; apply GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionDivisorEqSelfIntersectionPresentedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_divisor_eq_selfIntersection_presented : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), L.IsLB → Presents Δ L r → Y.inter (fun _ => Δ) = topSelfIntersection ℂ L Y.dim := by
  first | exact @GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents | exact GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents | (intros; apply GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSheafEqSumLengthMulCycle
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SheafCycle

theorem dim_add_one_le {T : Type} [TopologicalSpace T] {A B : Set T} (hA : IsClosed A)
    (hAi : IsIrreducible A) (hBi : IsIrreducible B) (h : A ⊂ B) :
    topologicalKrullDim A + 1 ≤ topologicalKrullDim B :=
  GlobalTheory.T.topologicalKrullDim_add_one_le_of_irreducible_ssubset T A B hA hAi hBi h

theorem length_stalk_ne_top {X : Scheme.{0}} [IsLocallyNoetherian X] (F : X.Modules)
    [QCoh.IsFiniteQC F] (w : X) (h : ∀ y ∈ QCoh.support F, w ∈ closure {y} → y = w) :
    Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) ≠ ⊤ :=
  GlobalTheory.T.length_stalk_ne_infty_of_no_generization X F w h

theorem length_stalk_pushforward_generic {X : Scheme.{0}} (Z : Closeds X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
    (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [QCoh.IsFiniteQC G] :
    Module.length (X.presheaf.stalk (redι Z (genericPoint _)))
      (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk (redι Z (genericPoint _)) :) =
      (GlobalTheory.VB.genRank G : ℕ∞) :=
  GlobalTheory.T.length_stalk_reducedClosed_genericPoint_eq_rank X Z G

theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ n) : a < n := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) := rfl
      rw [e, top_add] at h
      have : ((⊤ : ℕ∞)) ≤ (n : ℕ∞) := by exact_mod_cast h
      exact ENat.natCast_ne_top n (top_le_iff.1 this)
    | coe m =>
      have : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ n := by exact_mod_cast h
      have : m + 1 ≤ n := by exact_mod_cast this
      exact_mod_cast (by omega : m < n)

open QCoh

variable {κ : Type} [Field κ] {X : Scheme.{0}} [Algebra κ Γ(X, ⊤)]

theorem length_stalk_eq_zero_of_notMem {F : X.Modules} {w : X} (h : w ∉ support F) :
    Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) = 0 := by
  haveI := notMem_support_iff.1 h
  exact Module.length_eq_zero

theorem dim_closure_le_suppDim {F : X.Modules} [IsFiniteQC F] {w : X} (h : w ∈ support F) :
    topologicalKrullDim (closure {w} : Set X) ≤ suppDim F := by
  rw [suppDim_eq_iSup_closure F]
  exact le_iSup₂ (f := fun x (_ : x ∈ support F) ↦ topologicalKrullDim (closure {x} : Set X)) w h

theorem eq_of_mem_closure {F : X.Modules} [IsFiniteQC F] {n : ℕ} (hd : suppDim F ≤ n) {w : X}
    (hw : topologicalKrullDim (closure {w} : Set X) = n) :
    ∀ y ∈ support F, w ∈ closure {y} → y = w := by
  intro y hy hwy
  have hsub : closure {w} ⊆ closure {y} :=
    isClosed_closure.closure_subset_iff.2 (Set.singleton_subset_iff.2 hwy)
  by_cases he : closure ({w} : Set X) = closure {y}
  · exact (inseparable_iff_closure_eq.2 he.symm).eq
  · have h1 := dim_add_one_le isClosed_closure isIrreducible_singleton.closure
      isIrreducible_singleton.closure (ssubset_of_subset_of_ne hsub he)
    have h2 := (dim_closure_le_suppDim hy).trans hd
    rw [hw] at h1
    have h3 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ n := by push_cast; exact h1.trans h2
    exact absurd (by exact_mod_cast h3 : n + 1 ≤ n) (by omega)

variable (κ) in

theorem interNumRed_eq_zero (hp : IsProjOver (strHom κ X)) {ι : Type} [Fintype ι]
    {P : ι → LB X} (hP : ∀ i, (P i).IsLB) (C : Closeds X)
    (hC : topologicalKrullDim (C : Set X) < (Fintype.card ι : ℕ)) : interNumRed κ C P = 0 := by
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  have : IsLocallyNoetherian X := (isNoetherian_of_isProjOver hp).toIsLocallyNoetherian
  have hAV : IsAmpleLB (A.pull (redι C)) := hA.pull_of_isClosedImmersion _
  haveI : IsFiniteQC ((Scheme.Modules.pushforward (redι C)).obj (structureModule _)) :=
    ProperFinite.isFiniteQC_pushforward (redι C) hAV _
  refine interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom κ X) _ hp ?_ hP
  refine lt_of_le_of_lt (topologicalKrullDim_mono ?_) hC
  exact (support_pushforward_subset_image_of_isClosedImmersion (redι C) _).trans
    ((Set.image_subset_range _ _).trans (range_redι C).le)

theorem interNum_eq_sum_length_mul_interNumRed : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ X) → ∀ (ι : Type) [Fintype ι] (P : ι → LB X), (∀ i, (P i).IsLB) → ∀ (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F], GlobalTheory.QCoh.suppDim F ≤ (Fintype.card ι : ℕ) → ∀ S : Finset X, (∀ w ∈ GlobalTheory.QCoh.support F, topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card ι : ℕ) → w ∈ S) → interNum κ F P = ∑ w ∈ S, ((Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :)).toNat : ℤ) * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  intro κ _ X _ hp ι _ P hP F hF
  have hf := algebraMap_eq_strHom κ X
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  set n := Fintype.card ι with hn
  let term : X.Modules → X → ℤ := fun E w ↦
    ((Module.length (X.presheaf.stalk w) (E.presheaf.stalk w :)).toNat : ℤ) *
      interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P

  have hsmall : ∀ (E : X.Modules) (w : X), topologicalKrullDim (closure ({w} : Set X)) < n →
      term E w = 0 := fun E w h ↦ by
    simp only [term, interNumRed_eq_zero κ hp hP ⟨closure {w}, isClosed_closure⟩ h, mul_zero]
  have hout : ∀ (E : X.Modules) (w : X), w ∉ support E → term E w = 0 := fun E w h ↦ by
    simp only [term, length_stalk_eq_zero_of_notMem h, ENat.toNat_zero, Nat.cast_zero, zero_mul]
  let Q : X.Modules → Prop := fun E ↦ suppDim E ≤ n → ∀ S : Finset X,
    (∀ w ∈ support E, topologicalKrullDim (closure ({w} : Set X)) = n → w ∈ S) →
      interNum κ E P = ∑ w ∈ S, term E w
  suffices H : Q F from H
  refine GlobalTheory.QCoh.devissage X Q ?_ ?_ ?_ F hF
  · intro E hE _ S _
    rw [interNum_eq_zero_of_isZero κ hE hP]
    refine (Finset.sum_eq_zero fun w _ ↦ hout E w ?_).symm
    rw [support_eq_empty_iff.2 hE]
    exact Set.notMem_empty w
  · intro C hC h₁ h₃ Q₁ Q₃ hd S hS
    haveI := h₁
    haveI := h₃
    haveI := hC.mono_f
    haveI := hC.epi_g
    have hd₁ : suppDim C.X₁ ≤ n := (suppDim_le_of_mono C.f).trans hd
    have hd₃ : suppDim C.X₃ ≤ n := (suppDim_le_of_epi C.g).trans hd
    rw [interNum_shortExact hC hP (finiteCohTwists_of_isProjOver hf _ hp)
        (finiteCohTwists_of_isProjOver hf _ hp),
      Q₁ hd₁ S (fun w hw ↦ hS w (support_subset_of_mono C.f hw)),
      Q₃ hd₃ S (fun w hw ↦ hS w (support_subset_of_epi C.g hw)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    by_cases hw : topologicalKrullDim (closure ({w} : Set X)) < n
    · rw [hsmall _ _ hw, hsmall _ _ hw, hsmall _ _ hw, add_zero]
    have hfin : ∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ n →
        Module.length (X.presheaf.stalk w) (E.presheaf.stalk w :) ≠ ⊤ := fun E _ hE ↦ by
      by_cases hm : w ∈ support E
      · have he : topologicalKrullDim (closure ({w} : Set X)) = n :=
          le_antisymm ((dim_closure_le_suppDim hm).trans hE) (not_lt.1 hw)
        exact length_stalk_ne_top E w (eq_of_mem_closure hE he)
      · rw [length_stalk_eq_zero_of_notMem hm]; exact ENat.zero_ne_top
    have hex := Module.length_eq_add_of_exact (stalkLinear C.f w) (stalkLinear C.g w)
      (stalkLinear_injective C.f w) (stalkLinear_surjective C.g w)
      ((exact_iff_stalkLinear C).1 hC.exact w)
    simp only [term]
    rw [hex, ENat.toNat_add (hfin C.X₁ hd₁) (hfin C.X₃ hd₃)]
    push_cast
    ring
  · intro Z hZ hsm G hG hd S hS
    haveI := hG
    haveI := isIntegral_red hZ
    have hAV : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
    haveI hFq : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj G) :=
      ProperFinite.isFiniteQC_pushforward (redι Z) hAV G
    have hsupp : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊆ (Z : Set X) :=
      (support_pushforward_subset_image_of_isClosedImmersion (redι Z) G).trans
        ((Set.image_subset_range _ _).trans (range_redι Z).le)
    by_cases hss : support ((Scheme.Modules.pushforward (redι Z)).obj G) = (Z : Set X)
    swap
    · exact hsm _ hFq (ssubset_of_subset_of_ne hsupp hss) hd S hS
    have hdZ : topologicalKrullDim (Z : Set X) ≤ n := by
      rw [← hss]; exact hd

    have hlt : ∀ w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G),
        closure ({w} : Set X) ≠ Z → topologicalKrullDim (closure ({w} : Set X)) < n := by
      intro w hw hne
      have hwZ : closure ({w} : Set X) ⊆ Z :=
        Z.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hsupp hw))
      have h1 := dim_add_one_le isClosed_closure isIrreducible_singleton.closure hZ
        (ssubset_of_subset_of_ne hwZ hne)
      exact lt_of_add_one_le_natCast (h1.trans hdZ)
    rcases lt_or_eq_of_le hdZ with hZlt | hZeq
    · rw [interNum_eq_zero_of_isProjOver hf _ hp (by rw [suppDim, hss]; exact hZlt) hP]
      refine (Finset.sum_eq_zero fun w _ ↦ ?_).symm
      by_cases hw : w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G)
      · refine hsmall _ _ (lt_of_le_of_lt (topologicalKrullDim_mono ?_) hZlt)
        exact Z.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hsupp hw))
      · exact hout _ _ hw
    set η := redι Z (genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) with hη
    have hcl : closure ({η} : Set X) = Z := by
      rw [hη, ← Set.image_singleton, (redι Z).isClosedEmbedding.closure_image_eq,
        (genericPoint_spec _).def, Set.image_univ, range_redι]
    have hηs : η ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G) := by
      rw [hss]; exact (range_redι Z).le ⟨_, rfl⟩
    rw [Finset.sum_eq_single_of_mem η (hS η hηs (by rw [hcl]; exact hZeq)) fun w _ hne ↦ ?_]
    swap
    · by_cases hw : w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G)
      · refine hsmall _ _ (hlt w hw fun e ↦ hne ?_)
        exact (inseparable_iff_closure_eq.2 (e.trans hcl.symm)).eq
      · exact hout _ _ hw
    simp only [term]
    rw [length_stalk_pushforward_generic Z G, ENat.toNat_natCast]
    have hC : (⟨closure {η}, isClosed_closure⟩ : Closeds X) = Z := Closeds.ext hcl
    rw [hC]
    letI : Algebra κ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
      algebraΓOfHom (redι Z ≫ strHom κ X)
    have hfZ : ∀ r : κ, (redι Z).appTop (algebraMap κ Γ(X, ⊤) r) =
        algebraMap κ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r ↦ by
      rw [hf r]; rfl
    have hstr : strHom κ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = redι Z ≫ strHom κ X :=
      strHom_eq fun _ ↦ rfl
    have hpZ : IsProjOver (strHom κ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
      rw [hstr]; exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
    have hdimZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤
        (Fintype.card ι : ℕ) := by
      rw [topologicalKrullDim_red]; exact hdZ
    rw [interNum_pushforward_of_isClosedImmersion hfZ G hP,
      GlobalTheory.T.lineBundleIntersectionNumber_eq_genericRank_mul κ _ hpZ ι hdimZ G _ (fun i ↦ pull_isLB (hP i) _), interNumRed_def, interNumSub_def,
      interNumOn_def, interNum_pushforward_of_isClosedImmersion hfZ _ hP]

end GlobalTheory.SheafCycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvIntegralSqDiscreteSeriesCoefficientCompactDuaStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_integral_sq_discreteSeries_coefficient_compactDual : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (cd : CDHaar) {D : D7} (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (Fr : Frames W), IsFrames W Fr → (∀ ρ, (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) → ∀ ρ, StrictAnti (M.lam ρ) → (∀ a, ∃ z : ℤ, M.lam ρ a - ((W.rank : ℝ) - 1) / 2 = (z : ℝ)) → ∀ w : M.H ρ, ‖w‖ = 1 → Integrable (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) (cd.cd _ _) ∧ (∫ b : Upq W ρ, ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2 ∂(cd.cd _ _))⁻¹ = (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) / ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq | exact GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq | (intros; apply GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicAppLE
section
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace GlobalTheory.GenDegAlg

theorem isAlgebraic_appLE : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (letI := (π.appLE U V h).hom.toAlgebra; Algebra.IsAlgebraic Γ(X, U) Γ(Y, V)) := by
  intro X Y _ _ π hgen hdeg U V hU hV h
  have hη : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hx : π (genericPoint Y) ∈ U := h hη
  letI : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V h).hom.toAlgebra
  letI : Algebra Γ(X, U) (X.residueField (π (genericPoint Y))) :=
    (X.evaluation U _ hx).hom.toAlgebra
  letI : Algebra (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    (π.residueFieldMap (genericPoint Y)).hom.toAlgebra
  letI : Algebra Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    (Y.evaluation V _ hη).hom.toAlgebra
  letI : Algebra Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (X.evaluation U _ hx ≫ π.residueFieldMap (genericPoint Y)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.residueField (π (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := IsScalarTower.of_algebraMap_eq' rfl
  have hnat : π.appLE U V h ≫ Y.evaluation V _ hη =
      X.evaluation U _ hx ≫ π.residueFieldMap (genericPoint Y) := by
    rw [Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp [Scheme.evaluation]
  haveI : IsScalarTower Γ(X, U) Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' congr($(hnat).hom).symm
  haveI := GlobalTheory.ProjFin.isFractionRing_evaluation X hU hgen hx
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  haveI : Module.Finite (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hdeg)
  haveI : Algebra.IsAlgebraic (X.residueField (π (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (IsFractionRing.comap_isAlgebraic_iff (K := X.residueField (π (genericPoint Y)))).2 inferInstance
  have hinj : Function.Injective (Y.evaluation V _ hη).hom := by
    have h1 := germ_injective_of_isIntegral Y (genericPoint Y) hη
    have h2 : Function.Injective (Y.residue (genericPoint Y)).hom :=
      RingHom.injective (show Y.functionField →+* Y.residueField (genericPoint Y) from
        (Y.residue (genericPoint Y)).hom)
    exact h2.comp h1
  exact Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom Γ(X, U) Γ(Y, V)
    (Y.residueField (genericPoint Y))) hinj

end GlobalTheory.GenDegAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOverMvPolynomialRangeEtaleTower
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem isAlgebraic_range_eval₂Hom_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T),
  IsEtTower cK R cL T ι ψ τ → Function.Injective (MvPolynomial.eval₂Hom ι τ) →
  ∀ z : L, IsAlgebraic (T.subtype.comp (MvPolynomial.eval₂Hom ι τ)).range z := by
  intro K L _ _ cK cL r R T ι ψ τ h hinj z
  classical
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  let φL : A →+* L := T.subtype.comp φ
  have hφL : Function.Injective φL := Subtype.val_injective.comp hinj

  letI : Algebra A T := φ.toAlgebra
  letI : Algebra A L := φL.toAlgebra
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FormallyEtale A T := h.etale

  haveI : IsFractionRing T L := IsFractionRing.of_field T L fun f => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.top.frac f
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change f = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  haveI : Algebra.FormallyUnramified T L :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors T)
  haveI : Algebra.FormallyUnramified A L := Algebra.FormallyUnramified.comp A T L

  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let cT : ℂ →+* T := cL.codRestrict T h.top.const_mem
  letI : Algebra ℂ R := c0.toAlgebra
  letI : Algebra ℂ T := cT.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  haveI : IsScalarTower ℂ T L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ A L := IsScalarTower.of_algebraMap_eq fun a => by
    change cL a = T.subtype (MvPolynomial.eval₂Hom ι τ (MvPolynomial.C (c0 a)))
    rw [MvPolynomial.eval₂Hom_C]
    exact (h.const a).symm
  haveI : Algebra.EssFiniteType ℂ T := RingHom.essFiniteType_algebraMap.1 h.top.essFiniteType
  haveI : Algebra.EssFiniteType T L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors T)
  haveI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ T L
  haveI : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_comp ℂ A L

  let F := FractionRing A
  letI : Algebra F L := (IsFractionRing.lift hφL : F →+* L).toAlgebra
  haveI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap hφL a).symm
  haveI : Algebra.FormallyUnramified F L := Algebra.FormallyUnramified.of_restrictScalars A F L
  haveI : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp A F L
  haveI : Algebra.IsSeparable F L := Algebra.FormallyUnramified.isSeparable F L
  have hA : IsAlgebraic A z :=
    (IsFractionRing.isAlgebraic_iff A F L).2 (Algebra.IsAlgebraic.isAlgebraic z)

  obtain ⟨p, hp, hpz⟩ := hA
  refine ⟨p.map φL.rangeRestrict, (Polynomial.map_ne_zero_iff
    (RingHom.injective_codRestrict.2 hφL)).2 hp, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  exact hpz

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlmostLowerTriangularOfShearParabolicStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlmostLowerTriangular_of_shear_parabolic : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (L K : Type) [Field L] [Field K] (j : L →+* K) (t : K), t ≠ 0 → ∀ C : Mat m L, Par m ⊤ (shear τ a b t * C.map j) → AlmostLow τ a b C := by
  first | exact @GlobalTheory.FlagPush.almostLow_of_shear | exact GlobalTheory.FlagPush.almostLow_of_shear | (intros; apply GlobalTheory.FlagPush.almostLow_of_shear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBGenericOfSpecial
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.AmpleGeneric

theorem isAmpleLB_generic_of_special : ∀ (O E κ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [Field κ] [Algebra O κ], Function.Surjective (algebraMap O κ) → ∀ (W C W₀ : Scheme.{0}) (f : W ⟶ Sp O) (q : C ⟶ Sp E) (φ : C ⟶ W) (f₀ : W₀ ⟶ Sp κ) (b : W₀ ⟶ W), IsProjOver f → Flat f → IsPullback φ q f (spMap (algebraMap O E)) → IsPullback b f₀ f (spMap (algebraMap O κ)) → ∀ M : LB W, M.IsLB → IsAmpleLB (M.pull b) → IsAmpleLB (M.pull φ) := by
  intro O E κ _ _ _ _ _ _ _ hs W C W₀ f q φ f₀ b hP hF H H₀ M hM hA₀
  have hP₀ : IsProjOver f₀ := GlobalTheory.ProjSpace.isProjOver_of_isPullback_spMap _ H₀ hP
  have hB₀ : GlobalTheory.AbLaw.IsProjBy f₀ := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver f₀).2 hP₀
  have hB : GlobalTheory.AbLaw.IsProjBy f := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver f).2 hP
  have : IsProper (Over.mk f₀).hom := GlobalTheory.AbLaw.isProper_of_isProjBy κ W₀ f₀ hB₀
  have hR₀ : ReciprocityTheory.ChartRestriction.G.Out.RelAmple (Over.mk f₀) (M.pull b) :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine (Over.mk f₀) (LB.isLB_pull hM b)).2 hA₀
  have hR : ReciprocityTheory.ChartRestriction.G.Out.RelAmple (Over.mk f) M :=
    GlobalTheory.AmpleLocalBase.relAmple_of_closed O (Over.mk f) M hF hB hM κ (algebraMap O κ) hs (Over.mk f₀) b H₀
      (M.pull b) (LB.isLB_pull hM b) (GlobalTheory.lbIso_refl (LB.isLB_pull hM b)) hR₀
  have hAmp : IsAmpleLB M := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine (Over.mk f) hM hR
  have : IsAffineHom φ := MorphismProperty.of_isPullback H.flip inferInstance
  exact hAmp.pull_of_isAffineHom φ

end GlobalTheory.AmpleGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefOfDimLeZero
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem isAmpleLB_tens_of_isNef_of_dim_le_zero : ∀ (k : Type) [Field k] [Infinite k], (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (0 : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) := by
  intro k _ _ Y _ hp hd A N hA hN
  have : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hp
  have hAN : (tens A N).IsLB := (IsNef.tens_of_isProjOver (IsAmpleLB.isNef (k := k) hA) hN hp).isLB
  have hlt : topologicalKrullDim Y < ((1 : ℕ) : WithBot ℕ∞) :=
    lt_of_le_of_lt hd (by exact_mod_cast Nat.zero_lt_one)
  refine isAmpleLB_of_subsingleton_coh_one Y (tens A N) hAN fun F _ => ⟨1, le_rfl, ?_⟩
  have : IsFiniteQC (twist F (lbPow (tens A N) 1)) := isFiniteQC_twist (isLB_lbPow hAN 1)
  exact hA.subsingleton_coh_of_dim_lt _ hlt

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelOfIsIsoOverNonemptyOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isModel_of_isIso_restrict : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (U : X.Opens),
    (U : Set X).Nonempty → IsIso (π ∣_ U) → ∃ φ : X.functionField →+* Y.functionField, IsModel π φ := by
  intro X Y _ _ π U hU hiso
  obtain ⟨h₁, h₂⟩ := GlobalTheory.Published.generic_of_isIso_restrict π U hU
  have e : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
  have hd : IsDominant π := ⟨dense_iff_closure_eq.mpr
    (Set.eq_univ_of_univ_subset (e ▸ closure_mono (Set.singleton_subset_iff.mpr ⟨_, h₁⟩)))⟩
  exact ⟨functionFieldMap π, h₁, h₂, fun y a => functionFieldMap_algebraMap π y a⟩

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFunOfTransvectionConstantTermsZeroStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFun_of_transvection_constantTerms_zero : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ φ : GA D V → ℂ, IsAutFun V φ → ZCusp V φ → IsCuspFun V φ := by
  first | exact @GlobalTheory.TransvCusp.isCuspFun_of_zCusp | exact GlobalTheory.TransvCusp.isCuspFun_of_zCusp | (intros; apply GlobalTheory.TransvCusp.isCuspFun_of_zCusp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicCuspFormOfAdelicConstantTermsZeroStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHolomorphicCuspForm_of_adelic_constantTerms_zero : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ P : FDSec X, (∀ k, (X k).IsBddSec (la k) (P k)) → ZCusp V (adel V dict (muPin V dict mu c) P) → IsHolCusp X la P := by
  first | exact @GlobalTheory.HolDict.IntoCusp.isHolCusp_of_zCusp | exact GlobalTheory.HolDict.IntoCusp.isHolCusp_of_zCusp | (intros; apply GlobalTheory.HolDict.IntoCusp.isHolCusp_of_zCusp <;> assumption)
end

