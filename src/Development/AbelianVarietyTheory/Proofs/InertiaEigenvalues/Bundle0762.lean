import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0753
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0361
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinPullbackIsGoodTwistOfAnticyclotomicTame
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtension

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGLStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLProjections_mul_infiniteAdelicGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)), prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_mul_infGL) | (exact GlobalTheory.SchurExt.prS_prO_mul_infGL) | (intros; apply GlobalTheory.SchurExt.prS_prO_mul_infGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlacesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLProjections_on_supportedAtPlaces : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ g ∈ GlobalTheory.JSW.supS E a S, prS S a g = g ∧ prO S a g = 1) ∧ ∀ g, prS S a g ∈ GlobalTheory.JSW.supS E a S := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_supS) | (exact GlobalTheory.SchurExt.prS_prO_supS) | (intros; apply GlobalTheory.SchurExt.prS_prO_supS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericCharStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLProjections_upperUnitriangular_genericChar : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ u ∈ GlobalTheory.JSW.NA E a, prS S a u ∈ GlobalTheory.JSW.NA E a ∧ prO S a u ∈ GlobalTheory.JSW.NA E a ∧ GlobalTheory.JSW.psiN (prS S a u) * GlobalTheory.JSW.psiN (prO S a u) = GlobalTheory.JSW.psiN u := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_NA_psiN) | (exact GlobalTheory.SchurExt.prS_prO_NA_psiN) | (intros; apply GlobalTheory.SchurExt.prS_prO_NA_psiN  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2PairOfAdmissible
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.PointRepAboveL

theorem place_unique {D : D7} {i : D.nd.Loc} {τ : D.host.E →+* Qbar (D.nd.l i)} {w w' : PlE D.host}
    (h : InducesW D.nd i τ w) (h' : InducesW D.nd i τ w') : w' = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [← h x, h' x]

theorem compat_above (D : D7) (h0 : SumRepresentations.tie0 D) (h2 : SumRepresentations.adm2 D) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) (x : D.nd.X i)
    (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)) (hP : D.naut.ptV i P = some x)
    (hB : IsBCV D.nd D.naut i P Pa) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
    D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w =
      D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧
    ∀ τ, InducesW D.nd i τ w →
      D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ := by
  obtain ⟨ρ, hc, hs, hwd, hl⟩ := GlobalTheory.GalIsoBC.galRep_isobaric D h0 h2 i P Pa hB
  obtain ⟨Pm, hPm⟩ := GlobalTheory.BaseChangeConj.rep_conj_of_baseChange D h5 i r hr x P Pa hP hB ρ hc hs
    (fun w _ => hwd w)
  obtain ⟨-, hconj, -, -⟩ := h0.2.2.2.2.2 i
  obtain ⟨hdR, hWD, hJ⟩ := hconj _ ρ _ hc Pm hPm
  refine ⟨(hdR w hw).2 (hl w hw).1, ?_, fun τ hτ => ?_⟩
  · rw [hWD w (Or.inr (hl w hw).1), hwd]
  · rw [hJ τ (fun w' h' => by rw [place_unique hτ h']; exact (hl w hw).1)]
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [(hl w hw).2 τ hτ, D.naut.locAut_hodgeTateWeightsLevelZero_def i τ]

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → AdmissibleParameterJ.DeRhamFamilyAway D ∧ AdmissibleParameterJ.DeRhamFamilyTypePrimes D := by
  intro D h0 h1 h2 h5
  have key : ∀ i x, ∃ P Pa, D.naut.ptV i P = some x ∧ IsBCV D.nd D.naut i P Pa := fun i x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := h1 i P
    exact ⟨P, Pa, hP, hPa⟩
  refine ⟨fun i r hr w hw => ?_, fun i r hr _ w hw x => ?_⟩
  · have hl : (D.nd.l i).Prime := Fact.out
    refine ⟨fun hl0 hl1 x => ?_, fun _ x hm => ?_⟩
    · obtain ⟨P, Pa, hP, hB⟩ := key i x
      have h := compat_above D h0 h2 h5 i r hr x P Pa hP hB w hw
      have hc : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x)) :=
        SumRepresentations.contQ_of_continuous D.nd D.naut i (r x) (hr x).1
      refine ⟨(D.naut.wdOf_unrL i _ w hw hc h.1).1 ?_, h.2.2⟩
      rw [h.2.1, D.naut.unr_tw]
      by_cases hs : IsSplitPl D.host w
      · rw [hB.2.2.2.1 w hs]
        refine D.naut.locV_unr i P w hs (fun hq => D.nd.SQ_l i w (Or.inr hq) hw) (fun k => ?_) ?_
        · have hk : D.nd.l i ≠ D.host.g k := by
            fin_cases k
            · exact hl0
            · exact hl1
          exact SumRepresentations.not_over_of_ne hl (D.host.g_prime k) hk hw
        · split_ifs with hpd
          · exact SumRepresentations.not_over_of_ne hl D.host.pde'_prime (hpd ▸ D.host.pde_ne) hw
          · exact SumRepresentations.not_over_of_ne hl D.host.pde_prime hpd hw
      · exact (hB.2.2.2.2.1 w hs).1
    · obtain ⟨P, Pa, hP, hB⟩ := key i x
      have h := compat_above D h0 h2 h5 i r hr x P Pa hP hB w hw
      have hc : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x)) :=
        SumRepresentations.contQ_of_continuous D.nd D.naut i (r x) (hr x).1
      refine (D.naut.wdOf_mono0L i _ w hw hc h.1).1 ?_
      rw [h.2.1, D.naut.monomial_twist_iff]
      exact hm P Pa hP hB
  · obtain ⟨P, Pa, hP, hB⟩ := key i x
    have h := compat_above D h0 h2 h5 i r hr x P Pa hP hB w hw
    exact ⟨h.1, h.2.2⟩

end GlobalTheory.PointRepAboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTransportCompMemSphericalHecke
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.SatInd

theorem guMap_comp_mem_hecke : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (n : ℕ) (h : Formalism.UG.GU σ' n → ℂ), h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ' n) → (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) := by
  intro K _ _ g σ σ' hg hint n h hh
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [hg]
    simp
  let e : Formalism.UG.GU σ n ≃* Formalism.UG.GU σ' n :=
    { toFun := guMap g hg n
      invFun := guMap g.symm hg' n
      left_inv := fun y => guMap_symm_comp g hg hg' y
      right_inv := fun y => by
        have := guMap_symm_comp g.symm hg' (by simpa using hg) y
        simpa using this
      map_mul' := map_mul _ }
  have hK : ∀ y, y ∈ Formalism.UG.KU σ' n ↔ e.symm y ∈ Formalism.UG.KU σ n := by
    intro y
    rw [mem_KU_iff_guMap g hg hint (e.symm y)]
    change y ∈ Formalism.UG.KU σ' n ↔ e (e.symm y) ∈ Formalism.UG.KU σ' n
    rw [MulEquiv.apply_symm_apply]
  have := GlobalTheory.LFun.EigLoc.comp_symm_mem_hecke e.symm hK hh
  exact this

end GlobalTheory.SatInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusionsStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.SaturationArcLifting D HW F ∧ UnusedSlot80.SaturationEtale D HW F ∧ ArcLiftingSetup.SaturationFrobeniusPullback D HW F ∧ UnusedSlot80.GammaPreservesUniformiser D HW F ∧ UnusedSlot80.KillerAtLevels D HW F ∧ UnusedSlot80.KillerBoundWithConstant D HW F 8 ∧ UnusedSlot80.KillerAtLevelsSecondForm D HW F ∧ UnusedSlot80.FirstFiltrationArcLifting D HW F ∧ UnusedSlot80.FirstFiltrationEtale D HW F ∧ UnusedSlot80.SecondFiltrationArcLifting D HW F ∧ UnusedSlot80.SecondFiltrationEtale D HW F ∧ UnusedSlot80.FiltrationPropertiesEtale D HW F Cm ∧ UnusedSlot80.H1fBaseChangeFree D := by
  first | exact @GlobalTheory.ArcTools.arc_tools_from_clauses | exact GlobalTheory.ArcTools.arc_tools_from_clauses | (intros; apply GlobalTheory.ArcTools.arc_tools_from_clauses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinPullbackIsGoodTwistOfAnticyclotomicTameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (a : Recip D N.Om), a.Good → ∀ (A : Type) [CommGroup A] (φ : G D.host.E N.Om →* A) (l : ℕ), l.Prime → (∀ σ, ∃ n : ℕ, φ σ ^ (l ^ n) = 1) → IsOpen (φ.ker : Set (G D.host.E N.Om)) → AntiHom X.cc φ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1) → (⟨Q, a.pull φ, resOf (a.pull φ)⟩ : Twist D A).Good := by
  first | exact @GlobalTheory.TwistPull.good_pull | exact GlobalTheory.TwistPull.good_pull | (intros; apply GlobalTheory.TwistPull.good_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangePartitionsPermStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_partitions_perm : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P0 PI : D.naut.AV i) (Pa0 Pa : List (Part D.naut.CG)), D.naut.ptV i P0 = some x → D.naut.ptV i PI = some x → IsBCV D.nd D.naut i P0 Pa0 → IsBCV D.nd D.naut i PI Pa → Pa0.Perm Pa := by
  first | exact @GlobalTheory.BCPerm.main | exact GlobalTheory.BCPerm.main | (intros; apply GlobalTheory.BCPerm.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoTopOfLocalTateDualityEulerCharStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoTop_of_localTateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), tableLineDegreeTwo.aux₃ D HW F := by
  first | exact @GlobalTheory.TopClosing.blochKatoTop_of_localTateDuality_eulerChar_alt | exact GlobalTheory.TopClosing.blochKatoTop_of_localTateDuality_eulerChar_alt | (intros; apply GlobalTheory.TopClosing.blochKatoTop_of_localTateDuality_eulerChar_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlacesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDiagGL_mem_adelicGLSupportedAtFinitePlaces : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS E (m + r + 1 + 1) S := by
  first | (exact @GlobalTheory.SchurExt.blockGL_mem_supS) | (exact GlobalTheory.SchurExt.blockGL_mem_supS) | (intros; apply GlobalTheory.SchurExt.blockGL_mem_supS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtensionStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_chart_schurComplementExtension : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) → (∀ g, ContDiffOn ℝ ∞ (chart b₁ g) (invSet E (r + 1))) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (r + 1), u⁻¹ * p ∈ C) → ContDiff ℝ ∞ χ → ∀ g, ContDiffOn ℝ ∞ (chart (schurF β b₁ χ) g) (invSet E (m + r + 1 + 1)) := by
  first | (exact @GlobalTheory.SchurExt.contDiffOn_chart_schurF) | (exact GlobalTheory.SchurExt.contDiffOn_chart_schurF) | (intros; apply GlobalTheory.SchurExt.contDiffOn_chart_schurF  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CosetSumTransferAlongSurjectionPreimage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem cosetSum_transfer_surj {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (U0 : Subgroup G) (K : Subgroup H) (T : Subgroup G) (ψ : T →* H)
    (hψ : Function.Surjective ψ) (hTU : ∀ t : T, ψ t ∈ K ↔ (t : G) ∈ U0)
    (a φ' : H → ℂ) (β : G → V) (lam : V →ₗ[ℂ] ℂ)
    (ha : ∀ x, ∀ k ∈ K, a (x * k) = a x)
    (hfin : (Function.support fun d : H ⧸ K => a d.out).Finite)
    (hβ : ∀ x, ∀ u ∈ U0, β (x * u) = β x)
    (hφ : ∀ t : T, φ' (ψ t) = lam (β t)) :
    ∑ᶠ d : H ⧸ K, a d.out * φ' d.out = lam (∑ᶠ c : G ⧸ U0,
      if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then
        a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0) := by
  classical
  set F : G ⧸ U0 → V := fun c => if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then
        a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0 with hF
  let t : H ⧸ K → T := fun d => (hψ d.out).choose
  have ht : ∀ d, ψ (t d) = d.out := fun d => (hψ d.out).choose_spec
  let f : H ⧸ K → G ⧸ U0 := fun d => ((t d : G) : G ⧸ U0)

  have key : ∀ x y : T, ((x : G) : G ⧸ U0) = ((y : G) : G ⧸ U0) →
      ((x : G)⁻¹ * y ∈ U0) ∧ ∃ k ∈ K, ψ y = ψ x * k := by
    intro x y hxy
    rw [QuotientGroup.eq] at hxy
    refine ⟨hxy, ψ (x⁻¹ * y), (hTU _).2 (by simpa using hxy), ?_⟩
    simp [map_mul, map_inv]

  have hinj : Function.Injective f := by
    intro d d' h
    obtain ⟨-, k, hk, hkk⟩ := key _ _ h
    rw [ht, ht] at hkk
    rw [← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d', QuotientGroup.eq, hkk]
    simpa using hk

  have hcover : ∀ x : T, f ((ψ x : H) : H ⧸ K) = ((x : G) : G ⧸ U0) ∧
      a (((ψ x : H) : H ⧸ K).out) = a (ψ x) := by
    intro x
    set d : H ⧸ K := ((ψ x : H) : H ⧸ K) with hd
    have h1 : d.out⁻¹ * ψ x ∈ K := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    refine ⟨?_, ?_⟩
    · show (((t d : T) : G) : G ⧸ U0) = ((x : G) : G ⧸ U0)
      rw [QuotientGroup.eq]
      have : ψ ((t d)⁻¹ * x) ∈ K := by simpa [map_mul, map_inv, ht] using h1
      simpa using (hTU _).1 this
    · have := ha d.out _ h1
      simpa using this.symm

  have hval : ∀ d, F (f d) = a d.out • β (t d) := by
    intro d
    have hc : ∃ x : G, (x : G ⧸ U0) = f d ∧ x ∈ T := ⟨t d, rfl, (t d).2⟩
    simp only [hF, dif_pos hc]
    obtain ⟨hU, k, hk, hkk⟩ := key (t d) ⟨hc.choose, hc.choose_spec.2⟩ hc.choose_spec.1.symm
    rw [hkk, ha _ k hk, ht]
    congr 1
    have := hβ (t d : G) _ hU
    simpa using this

  set S : Finset (H ⧸ K) := hfin.toFinset with hS
  have hsupp : Function.support F ⊆ ↑(S.image f) := by
    intro c hc
    rw [Function.mem_support] at hc
    have hc' : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T := by
      by_contra hn
      exact hc (by simp only [hF, dif_neg hn])
    obtain ⟨x, rfl, hx⟩ := hc'
    obtain ⟨h1, h2⟩ := hcover ⟨x, hx⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, ?_, h1⟩)
    rw [hS, Set.Finite.mem_toFinset, Function.mem_support, h2]
    intro h0
    apply hc
    have hF' := hval ((ψ ⟨x, hx⟩ : H) : H ⧸ K)
    rw [h1, h2, h0, zero_smul] at hF'
    exact hF'
  have hL : Function.support (fun d : H ⧸ K => a d.out * φ' d.out) ⊆ ↑S := by
    intro d hd
    rw [hS, Set.Finite.coe_toFinset]
    exact fun h0 => hd (by simp only [h0, zero_mul])
  rw [finsum_eq_sum_of_support_subset _ hL, finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun d _ d' _ h => hinj h), map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hval, map_smul, smul_eq_mul, ← hφ, ht]

end GlobalTheory
end

