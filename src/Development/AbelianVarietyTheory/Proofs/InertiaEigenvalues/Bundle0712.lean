import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0663
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0711
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0707
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0703
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0704

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeStableAndHodgeTateJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.NgalFil

theorem ENStable_and_jumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) ∧ ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  intro hB l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hS hC hH
  have h1 := GlobalTheory.T.monodromyOperator_maps_into_completion hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH
  exact ⟨h1, GlobalTheory.T.filtration_jumps_breuilKisin_subset_galoisJumps hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH h1⟩

end GlobalTheory.NgalFil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterRecCompatible
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.SuppLaw

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero h).charPol σ = 1 := by
  rw [WD.lpZero, WD.charPol_mk]
  exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree]; simp)

theorem charPol_sumList (l : List (WD h)) (σ : Weil h) :
    (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod := by
  induction l with
  | nil => simp [sumList, charPol_lpZero]
  | cons b l ih =>
    have : sumList (b :: l) = WD.lpSum b (sumList l) := rfl
    rw [this, WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]

theorem nu_eq {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc : IrrGL (w.adicCompletion E) → WD h}
    (H : LawsLit a ha e rc) (x : IrrGL (w.adicCompletion E)) (s : ℝ) : rc (x.nu s) = (rc x).lpTw s := by
  rw [IrrGL.nu, H.twist, H.one, lpChar_lpOfChar, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

theorem charPol_seg {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc : IrrGL (w.adicCompletion E) → WD h}
    (H : LawsLit a ha e rc) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).charPol σ
      = (Δ.ms.map fun y => (rc y).charPol σ).prod := by
  rw [(GlobalTheory.T.weilDeligne_charpoly_twist_special E Ω A w h (rc Δ.first)).2 Δ.len σ, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (rc (Δ.term j)).charPol σ = ((rc Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, nu_eq H]
  change _ = ∏ j : Fin Δ.len, (fun y => (rc y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((rc Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

end GlobalTheory.LocLanglands.SuppLaw

namespace GlobalTheory.LocLanglands

theorem charPol_eq_prod_support : LanglandsExhaustionGL → ZelevinskyPolynomialRing → GeometricLemma →
    BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ)
    (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ)
    (rc : IrrGL (w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (x : IrrGL (w.adicCompletion E)) s,
    HasSupport x.rep s → ∀ σ, (rc x).charPol σ = (s.map fun y => (rc y).charPol σ).prod := by
  intro hEx hZ hG hBZ E Ω _ _ _ _ _ A w h a ha e rc H x s hs σ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := hEx (w.adicCompletion E) x
  have h1 := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment hZ _ 𝔪 x hm
  obtain rfl : s = msupp 𝔪 := GlobalTheory.T.supercuspidalSupport_unique_GL hG hBZ hZ _ x s _ hs h1
  rw [H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, SuppLaw.charPol_sumList, List.map_map,
    msupp, Multiset.map_bind, Multiset.prod_bind]
  have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
      (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
  rw [hl, Multiset.coe_toList]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => SuppLaw.charPol_seg H Δ σ)

end GlobalTheory.LocLanglands
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCocycleOfSemistableCoboundaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousCocycle_of_semistable_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → c ∈ continuousCocycles ρ := by
  first | exact @GlobalTheory.cocycle_of_st_coboundary | exact GlobalTheory.cocycle_of_st_coboundary | (intros; apply GlobalTheory.cocycle_of_st_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalOfLocalLanglands
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspReadTrue

theorem cuspRead_recT : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut),
    CGTrue hL D T → CuspRead (recT T hL) := by
  intro hL D T C a P ha hP
  haveI := host_isCMField D.host
  have hu : (CG.mk P).IsUnitary := CsdUnitary.isUnitary_of_isCsd _ a (CG.mk P) hP
  have hπ : C.e a ((C.equiv a ha).symm ⟨CG.mk P, hu⟩) = ⟨CG.mk P, hu⟩ := (C.equiv a ha).apply_symm_apply _
  refine ⟨(C.equiv a ha).symm ⟨CG.mk P, hu⟩, (C.csd a _).2 (by rw [hπ]; exact hP), fun w σ hσ => ?_, fun τ m hm => ?_⟩
  · apply (T.e w).injective
    rw [C.loc, hπ]
    simp only [recT, Equiv.apply_symm_apply]
    exact ParLaws.locPar_mk hL hσ _
  · rw [C.inf, hπ]
    exact CG.HasInfChar.infChar_eq (π := CG.mk P) hm

end GlobalTheory.CuspReadTrue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupActsResiduesFrobeniusPowerStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decompositionGroup_acts_residues_frobeniusPower : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w),
    ∀ d ∈ Dec (F := E) A, ∀ y : Ω, ∃ K : IntermediateField E Ω, FiniteDimensional E K ∧ y ∈ K ∧
      ∃ j : ℕ, ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1 := by
  first | exact @GlobalTheory.DecFrobPow.exists_field_cong_pow | exact GlobalTheory.DecFrobPow.exists_field_cong_pow | (intros; apply GlobalTheory.DecFrobPow.exists_field_cong_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantRecCompatible
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc : IrrGL (w.adicCompletion E) → WD h}

theorem LawsLit.nu_eq_lpTw (H : LawsLit a ha e rc) (x : IrrGL (w.adicCompletion E)) (s : ℝ) :
    rc (x.nu s) = (rc x).lpTw s := by
  rw [IrrGL.nu, H.twist, H.one, lpChar_lpOfChar, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

end GlobalTheory.LocLanglands

namespace GlobalTheory

theorem lawsLit_det : StandardCosocleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) = sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j)) := by
  intro hSC E Ω _ _ _ _ _ A w h a ha e rc H t χ hχ
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have hL := GlobalTheory.T.isLanglandsClassification_detCharacter hSC (w.adicCompletion E) t χ hχ
  obtain ⟨φ⟩ := (IrrRep.det (Fin t) χ hχ).nonempty_equiv_rep
  have hL' := hL.of_equiv φ.symm
  rw [H.langlands _ (cls (IrrRep.det (Fin t) χ hχ)) hL', segSum, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  show ((rc ((IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ))).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar
      (WD.lpSp h 1) = _
  have h0 : ((((1 : ℕ) : ℝ) - 1) / 2) = 0 := by norm_num
  rw [h0, (GlobalTheory.T.weilDeligne_charpoly_twist_special E Ω A w h _).1, H.nu_eq_lpTw]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidualStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_spectrum_of_residual : GlobalTheory.Published.DiscreteSpectrumResidual → GlobalTheory.Published.DiscreteSpectrumGL := by
  first | exact @GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual | exact GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual | (intros; apply GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfCompRangeRestrict
section
noncomputable section

open GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.KTypeTest GlobalTheory.KTypeDatum

namespace GlobalTheory.KTypeDatum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsHeckeTypeDatum (π₀ : IrrGL k) (t : ℕ) {N : ℕ} (J : Subgroup (KO k (Fin N))) {W : Type} [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ J W) (q : ℕ) (T : ℕ → Module.End ℂ (indSpace J τ)) : Prop :=
  2 ≤ q ∧ FiniteDimensional ℂ (indSpace J τ) ∧
    (∃ K' : Subgroup (GL (Fin N) k), IsOpen (K' : Set (GL (Fin N) k)) ∧ K' ≤ KO k (Fin N) ∧
      (K'.subgroupOf (KO k (Fin N))).Normal ∧ (∀ κ : KO k (Fin N), (κ : GL (Fin N) k) ∈ K' → κ ∈ J) ∧
      ∀ j : J, ((j : KO k (Fin N)) : GL (Fin N) k) ∈ K' → τ j = 1) ∧
    (∀ (r : ℕ) (y : Fin r → IrrGL k) (hd : ∑ j, (y j).1 = N), IsSegFamily y → (∃ j, ¬ InComp π₀ (y j)) →
      ∀ f, IsJMap J τ (prodIrr y hd) f → f = 0) ∧
    (∀ i, i + 1 < t → ∀ κ : KO k (Fin N), T i * ind J τ κ = ind J τ κ * T i) ∧
    (∀ i, i + 1 < t → (T i - (q : ℂ) • 1) * (T i + 1) = 0) ∧
    (∀ i j, j + 1 < t → i + 2 ≤ j → T i * T j = T j * T i) ∧
    (∀ i, i + 2 < t → T i * T (i + 1) * T i = T (i + 1) * T i * T (i + 1)) ∧
    (∀ (r : ℕ) (y : Fin r → IrrGL k) (hd : ∑ j, (y j).1 = N), IsSegFamily y → (∀ j, InComp π₀ (y j)) →
      (∃ j, ¬ IrrGL.Inert π₀ (y j)) → ∀ F, IsKMap (KO k (Fin N)) (ind J τ) (prodIrr y hd) F →
      (∀ i, i + 1 < t → F ∘ₗ T i = (q : ℂ) • F) → F = 0) ∧
    ∃ (hN : ∑ _i : Fin t, π₀.1 = N) (F : indSpace J τ →ₗ[ℂ] _), F ≠ 0 ∧
      IsKMap (KO k (Fin N)) (ind J τ) (prodIrr (fun _ : Fin t => π₀) hN) F ∧
      ∀ i, i + 1 < t → F ∘ₗ T i = (q : ℂ) • F

end GlobalTheory.KTypeDatum

namespace GlobalTheory.KTypeDatum

section Generic

variable {G : Type} [Group G] {K : Subgroup G} {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V]
  [Module ℂ V] {σ : Representation ℂ K U} {ρ : Representation ℂ G V} {e : Module.End ℂ U}

theorem range_stable (hc : ∀ κ : K, σ κ * e = e * σ κ) :
    ∀ κ : K, ∀ f ∈ LinearMap.range e, σ κ f ∈ LinearMap.range e := by
  rintro κ _ ⟨x, rfl⟩
  refine ⟨σ κ x, ?_⟩
  have := congrArg (fun L : Module.End ℂ U => L x) (hc κ)
  simpa [Module.End.mul_apply] using this.symm

theorem isKMap_comp_rangeRestrict (hc : ∀ κ : K, σ κ * e = e * σ κ) {f : LinearMap.range e →ₗ[ℂ] V}
    (hf : IsKMap K (sub σ (LinearMap.range e) (range_stable hc)) ρ f) : IsKMap K σ ρ (f ∘ₗ e.rangeRestrict) := by
  intro κ
  ext x
  have := congrArg (fun L => L (e.rangeRestrict x)) (hf κ)
  simp only [LinearMap.comp_apply] at this ⊢
  rw [← this]
  congr 1
  apply Subtype.ext
  have := congrArg (fun L : Module.End ℂ U => L x) (hc κ)
  simpa [sub, Module.End.mul_apply] using this.symm

theorem isKMap_comp_subtype (hc : ∀ κ : K, σ κ * e = e * σ κ) {F : U →ₗ[ℂ] V} (hF : IsKMap K σ ρ F) :
    IsKMap K (sub σ (LinearMap.range e) (range_stable hc)) ρ (F ∘ₗ (LinearMap.range e).subtype) := by
  intro κ
  ext ⟨y, hy⟩
  have := congrArg (fun L => L y) (hF κ)
  simpa [sub] using this

theorem eq_zero_of_comp_rangeRestrict (he : e * e = e) {f : LinearMap.range e →ₗ[ℂ] V}
    (h0 : f ∘ₗ e.rangeRestrict = 0) : f = 0 := by
  ext ⟨_, x, rfl⟩
  have := congrArg (fun L => L x) h0
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
  exact this

theorem comp_subtype_ne_zero {F : U →ₗ[ℂ] V} (hF : F ≠ 0) (hfix : F ∘ₗ e = F) :
    F ∘ₗ (LinearMap.range e).subtype ≠ 0 := by
  intro h0
  apply hF
  rw [← hfix]
  ext x
  have := congrArg (fun L => L ⟨e x, x, rfl⟩) h0
  simpa using this

theorem comp_rangeRestrict_comp {f : LinearMap.range e →ₗ[ℂ] V} {T : Module.End ℂ U} {c : ℂ}
    (heT : e * T = c • e) : (f ∘ₗ e.rangeRestrict) ∘ₗ T = c • (f ∘ₗ e.rangeRestrict) := by
  ext x
  have h2 := congrArg (fun L : Module.End ℂ U => L x) heT
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h2
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  rw [← map_smul]
  congr 1
  exact Subtype.ext (by simpa using h2)

end Generic

end GlobalTheory.KTypeDatum

namespace GlobalTheory.KTypeDatum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isKTypeDatum_range {π₀ : IrrGL k} {t N : ℕ} {J : Subgroup (KO k (Fin N))} {W : Type} [AddCommGroup W]
    [Module ℂ W] {τ : Representation ℂ J W} {q : ℕ} {T : ℕ → Module.End ℂ (indSpace J τ)}
    (h : IsHeckeTypeDatum π₀ t J τ q T) (e : Module.End ℂ (indSpace J τ)) (he : e * e = e)
    (heT : ∀ i, i + 1 < t → e * T i = (q : ℂ) • e)
    (hc : ∀ κ : KO k (Fin N), ind J τ κ * e = e * ind J τ κ)
    (hfix : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (F : indSpace J τ →ₗ[ℂ] V),
      (∀ i, i + 1 < t → F ∘ₗ T i = (q : ℂ) • F) → F ∘ₗ e = F) :
    IsKTypeDatum π₀ t J τ (LinearMap.range e) (range_stable hc) := by
  obtain ⟨-, hfd, h1, h3, -, -, -, -, h4, hN, F5, hF5, hK5, hT5⟩ := h
  refine ⟨h1, ?_, h3, ?_, ?_⟩
  · haveI := hfd; infer_instance
  · intro r y hd hs hin hn f hf
    exact eq_zero_of_comp_rangeRestrict he (h4 r y hd hs hin hn _ (isKMap_comp_rangeRestrict hc hf)
      fun i hi => comp_rangeRestrict_comp (heT i hi))
  · exact ⟨hN, _, comp_subtype_ne_zero hF5 (hfix _ F5 hT5), isKMap_comp_subtype hc hK5⟩

end GlobalTheory.KTypeDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitar
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.DefU

theorem exists_hasWeightAt_of_isAutRepU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam :=
  fun E _ _ _ n _ π hπ τ => (GlobalTheory.T.existsUnique_weight_definiteUnitary_at E n (AU.mk ⟨π, hπ⟩) τ).exists

end GlobalTheory.DefU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinBasisOfSemistablePeriodsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisinBasis_of_semistablePeriods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (N : ℕ) (F : Pre bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T ∧ IsUnit Z ∧ ∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA := by
  first | exact @GlobalTheory.BKLim.exists_pre_of_wseed | exact GlobalTheory.BKLim.exists_pre_of_wseed | (intros; apply GlobalTheory.BKLim.exists_pre_of_wseed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFrameLimitLatticeBreuilKisinTowerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRhamFrame_limitLattice_breuilKisinTower : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val), (∀ n, (F n).IsDR) → ∃ F₀ : Frame bk N d (fun g => (ρ g).val), F₀.IsDR ∧ ((∀ n, (F n).IsCr) → F₀.IsCr) ∧ ∃ r, ∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r := by
  first | (exact @GlobalTheory.BKLim.limit_frame_exists) | (exact GlobalTheory.BKLim.limit_frame_exists) | (intros; apply GlobalTheory.BKLim.limit_frame_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElemStdLatticeSandwichSplitSupportStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_elem_stdLattice_sandwich_splitSupport : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (bad : ℕ), IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e V h → ∃ m : 𝓞 D.host.E, m ≠ 0 ∧ Ideal.span {m} • Bridge.hLat V (finPt V h) ≤ Formalism.L2.Pj.stdLat D.host.E V.rank ∧ Ideal.span {m} • Formalism.L2.Pj.stdLat D.host.E V.rank ≤ Bridge.hLat V (finPt V h) ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → m ∈ P → P.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ P ∧ ((bad : ℕ) : 𝓞 D.host.E) ∉ P := by
  first | exact @GlobalTheory.SuppLatStd.lat_std_of_suppAt | exact GlobalTheory.SuppLatStd.lat_std_of_suppAt | (intros; apply GlobalTheory.SuppLatStd.lat_std_of_suppAt <;> assumption)
end

