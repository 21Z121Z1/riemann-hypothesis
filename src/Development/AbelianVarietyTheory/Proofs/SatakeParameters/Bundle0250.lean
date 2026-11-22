import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0248
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0154
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0099
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
import Formalism.LocalToGlobal.KernelLattices.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import ReciprocityTheory.Hypotheses.GalCoh

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsHeckeModulesIsoAllPlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicModularForms_heckeModules_iso_all_places : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsIrrRep a.ρ S₂ → (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ (∃ f ∈ S₁, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ (∃ f ∈ S₂, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ ∀ U : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), (∀ f ∈ S₁, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f) ∧ (∀ f ∈ S₂, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f)) → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  first | exact @GlobalTheory.HeckeIso.main | exact GlobalTheory.HeckeIso.main | (intros; apply GlobalTheory.HeckeIso.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockTypeVectorIrreducibleSplitsAsProductStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockTypeVector_irreducible_splits_as_product : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], BlockSplit k := by
  first | exact @GlobalTheory.BlockSplitProof.main | exact GlobalTheory.BlockSplitProof.main | (intros; apply GlobalTheory.BlockSplitProof.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightTwistCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_weight_twist_character : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ i : D.nd.Loc, (∀ a (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w → (D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ↔ D.naut.IsdRW i ρ w)) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i χ w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = D.naut.lpChar (D.naut.wdOf i ρ w) (D.naut.wdOf i χ w)) ∧ (∀ τ (c : ℤ), (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i χ w) → D.naut.jumpsW i χ τ = {c} → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (D.naut.jumpsW i ρ τ).map (· + c))) := by
  first | exact @GlobalTheory.TwistGal.galois_twist | exact GlobalTheory.TwistGal.galois_twist | (intros; apply GlobalTheory.TwistGal.galois_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHeckeOperatorsRowsIntertwineThetaLifts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Hk3.HeckeRowsClose

section TwLemmas
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tw_sub_injective (s : Bool) {V W : Submodule ℂ E} (h : Tw.sub s V = Tw.sub s W) : V = W := by
  ext x
  exact SetLike.ext_iff.mp h (Tw.mk s x)

theorem tw_span_image (s : Bool) (S : Set E) :
    Submodule.span ℂ ((Tw.mk s : E → Tw s E) '' S) = Tw.sub s (Submodule.span ℂ S) := by
  have h1 : Tw.sub s (Submodule.span ℂ S) = (Submodule.span ℂ S).map (Tw.mkL s E) := by
    ext x
    constructor
    · intro hx; exact ⟨Tw.out x, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  rw [h1, Submodule.map_span]; rfl

theorem tw_commute (s : Bool) {a b : Module.End ℂ E} (h : Commute a b) : Commute (Tw.map s a) (Tw.map s b) := by
  show Tw.map s a * Tw.map s b = Tw.map s b * Tw.map s a
  ext x
  exact congrArg (Tw.mk s) (LinearMap.congr_fun h.eq (Tw.out x))

end TwLemmas

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem opC_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hK : (R.toCx3 F).KFormR) (t : T) (i : (A3.rowI t).OpIx)
    (g : Module.End ℂ (R.HX t).H) (hg : ∀ x, R.jX t ((A3.rowI t).opAll i x) = g (R.jX t x)) :
    (R.toCx3 F).opC t (Sum.inl i) = Tw.map (twAt D.what₂.embLL A3.A.v0) g := by
  apply (Module.Basis.mk (hK t).1 (hK t).2.ge).ext
  intro k
  rw [Module.Basis.mk_apply, ← CxData.jR_opR _ hK]
  exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (hg _)

set_option maxHeartbeats 1000000 in
theorem span_parts_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hK : (R.toCx3 F).KFormR)
    (op : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H)
    (hOpC : ∀ i, (R.toCx3 F).opC A3.A.μ0 (Sum.inl i) = Tw.map (twAt D.what₂.embLL A3.A.v0) (op i))
    (p : A3.fam3.base3.Ix) :
    Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) =
      Formalism.L2.Col.eigSum op (fun x => cxSys A3.fam3.base3.v0.embedding ((A3.rowI A3.A.μ0).HasRes3 p.1)
        (fun i => cj (twAt D.what₂.embLL A3.A.v0) (x i))) := by
  have hFD : FiniteDimensional D.what₂.LL (A3.fam3.amb3.FR A3.A.μ0) :=
    Module.Finite.of_basis (A3.A.fam.R A3.A.μ0).S.basis
  have hFin : Finite (Module.Basis.ofVectorSpaceIndex D.what₂.LL (A3.fam3.amb3.FR A3.A.μ0)) :=
    Module.Finite.finite_basis (CxData.bR (A := A3.fam3.amb3) A3.A.μ0)
  have hjR : ∀ i x, (R.toCx3 F).jR A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i x) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (op i) ((R.toCx3 F).jR A3.A.μ0 x) :=
    fun i x => (CxData.jR_opR _ hK _ (Sum.inl i) x).trans (LinearMap.congr_fun (hOpC i) _)
  have hspan := (GlobalTheory.span_image_eigAt_of_basis A3.fam3.base3.v0.embedding ((R.toCx3 F).jR A3.A.μ0)
    (CxData.bR (A := A3.fam3.amb3) A3.A.μ0) (A3.rowI A3.A.μ0).opAll
    (fun i => Tw.map (E := (R.HX A3.A.μ0).H) (F := (R.HX A3.A.μ0).H) (twAt D.what₂.embLL A3.A.v0) (op i))
    (hK _).1 (hK _).2 hjR).2.1 ((A3.rowI A3.A.μ0).HasRes3 p.1)
  have hTw := (GlobalTheory.TwEig.pairComm_eigSum_sub_iSup (twAt D.what₂.embLL A3.A.v0) op).2.1
    (cxSys A3.fam3.base3.v0.embedding ((A3.rowI A3.A.μ0).HasRes3 p.1))
  apply tw_sub_injective (twAt D.what₂.embLL A3.A.v0)
  rw [← tw_span_image, Set.image_image]
  exact hspan.trans hTw

set_option maxHeartbeats 1000000 in
theorem adj_ne_zero (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hB : R.PThmB)
    (hPos : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0)
    (hEEc : ∀ c, R.EEc c = EEc R.toRealDat R.SF c) (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ)
    (hc : EEc R.toRealDat R.SF c ≠ ⊥) :
    ∃ w ∈ EEc R.toRealDat R.SF c, LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hc
  have hc' : R.EEc c ≠ ⊥ := fun h0 => hc ((hEEc c).symm.trans h0)
  have hcar : R.Carries p c := by
    refine ⟨hc', ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [hall v ((SetLike.ext_iff.mp (hEEc c) v).mp hv)]
    exact Submodule.zero_mem _
  exact GlobalTheory.thetaUp_injective_on_carried R F hB hPos p c hcar w ((SetLike.ext_iff.mp (hEEc c) w).mpr hw) hw0 (hall w hw)

set_option maxHeartbeats 1000000 in
theorem eep_eq (R : RealDat3 D A3 Ks) (hEEc : ∀ c, R.EEc c = EEc R.toRealDat R.SF c) (p : A3.fam3.base3.Ix)
    (op : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H)
    (h' : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ R.HE.H) (Q : ((A3.rowI A3.A.μ0).OpIx → ℂ) → Prop)
    (hspanE : Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) =
      Formalism.L2.Col.eigSum op Q)
    (hLA : (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : EEc R.toRealDat R.SF c ≠ ⊥ ∧
      (EEc R.toRealDat R.SF c).map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤ Formalism.L2.Col.eigSum op Q),
        EEc R.toRealDat R.SF c) = Formalism.L2.Col.eigSum h' Q) :
    R.EEp3 p = Formalism.L2.Col.eigSum h' Q := by
  rw [← hLA]
  unfold RealDat3.EEp3 RealDat3.Carries
  simp only [hEEc, hspanE]

set_option maxHeartbeats 1000000 in
theorem exists_core (hH : HoweUnram) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hLI : GlobalTheory.Chain.LiftInteg D)
    (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hS : SchurAll R.toRealDat) (hJ : InertJunk A3) (hB : R.PThmB)
    (hPos : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) : ∃ hE, HeckeIntertwiningDefinite A3 (R.toCx3 F) hE := by
  obtain ⟨hCore', hSF, -, -, hEEc, -, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC
  have hCore := hCore' hEx
  obtain ⟨h, hOpsE, hNE, hTop, hEig, -⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 hCore hS R.SF hSF
  choose hX hXops hXnorm using (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models).1
  choose pl cX c0 hDict using GlobalTheory.T.every_rowOperator_is_labelOperator_with_partner hH R F hLI hC hEx hS hJ
  have hK : (R.toCx3 F).KFormR := RealDat3.kFormR_of hCore.models
  have hOpC : ∀ t i, (R.toCx3 F).opC t (Sum.inl i) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (hX t (pl t i) (cX t i)) :=
    fun t i => opC_eq R F hK t i _ ((hDict t).op _ (hXops t) i)
  have hSys := fun t i => GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 hCore hS R.SF hSF t (pl t i) ((hDict t).good i) (cX t i)
    (c0 t i) ((hDict t).mat i) (hX t) (hXops t)
  refine ⟨fun t i => Tw.map (E := R.HE.H) (F := R.HE.H) (twAt D.what₂.embLL A3.A.v0) (h (pl t i) (c0 t i)), ⟨?_, ?_, ?_⟩⟩
  · intro t i u
    rw [hOpC]
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) ((hSys t i).1 h hOpsE (Tw.out (s := twAt D.what₂.embLL A3.A.v0) u))
  · intro i j
    exact tw_commute _ (hNE.1 _ _ ((hDict _).good i) ((hDict _).good j) _ _)
  · intro p
    have hNX := hXnorm A3.A.μ0
    have hspanE := span_parts_eq R F hK (fun i => hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i)) (hOpC A3.A.μ0) p
    have hNop : ∀ i, Commute (hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i))
        (LinearMap.adjoint (hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i))) := fun i => by
      have hg := (hDict A3.A.μ0).good i
      have hc := hNX.1 _ _ hg hg (cX A3.A.μ0 i) (dualC (Finsupp.mapRange star (star_zero ℂ) (cX A3.A.μ0 i)))
      rw [← hNX.2 _ hg] at hc
      exact hc
    have hNh : ∀ i, Commute (h (pl A3.A.μ0 i) (c0 A3.A.μ0 i)) (LinearMap.adjoint (h (pl A3.A.μ0 i) (c0 A3.A.μ0 i))) :=
      fun i => by
        have hg := (hDict A3.A.μ0).good i
        have hc := hNE.1 _ _ hg hg (c0 A3.A.μ0 i) (dualC (Finsupp.mapRange star (star_zero ℂ) (c0 A3.A.μ0 i)))
        rw [← hNE.2 _ hg] at hc
        exact hc
    have hPC : Formalism.L2.Col.PairComm (fun i => hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i)) :=
      fun i j => hNX.1 _ _ ((hDict _).good i) ((hDict _).good j) _ _
    obtain ⟨-, hLA⟩ := GlobalTheory.T.parts_adjoint_intertwiner_eq_joint_eigenspaces (R.Th A3.A.μ0) (fun i => hX A3.A.μ0 (pl A3.A.μ0 i) (cX A3.A.μ0 i))
      (fun i => h (pl A3.A.μ0 i) (c0 A3.A.μ0 i)) (fun c => EEc R.toRealDat R.SF c)
      (fun c i => evC (Yc D 0) (pl A3.A.μ0 i) (fun d => c (pl A3.A.μ0 i) (dualLab d)) (c0 A3.A.μ0 i))
      (fun i u => (hSys A3.A.μ0 i).1 h hOpsE u) hNop hNh hPC hTop
      (fun c w hw i => hEig c _ ((hDict _).good i) _ w hw) (adj_ne_zero R F hB hPos hEEc p)
    have hEEp := eep_eq R hEEc p _ (fun i => h (pl A3.A.μ0 i) (c0 A3.A.μ0 i)) _ hspanE (hLA _).2
    exact (congrArg (Tw.sub (twAt D.what₂.embLL A3.A.v0)) hEEp).trans
      ((GlobalTheory.TwEig.pairComm_eigSum_sub_iSup (twAt D.what₂.embLL A3.A.v0)
        (fun i => h (pl A3.A.μ0 i) (c0 A3.A.μ0 i))).2.1 _).symm

theorem exists_heckeIntertwiningDefinite_of_liftInteg : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type}
    [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F →
    R.toRealDat.ExAt → InertJunk A3 → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) →
    ∃ hE, HeckeIntertwiningDefinite A3 (R.toCx3 F) hE :=
  fun hH _ hCD _ _ _ _ _ _ _ _ _ _ _ _ R F hLI hC hEx hJ hB hPos =>
    exists_core hH R F hLI hC hEx (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCD R.toRealDat) hJ hB hPos

end GlobalTheory.Hk3.HeckeRowsClose
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSeparatingInertEigenvaluePassage
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TrPass

theorem sep_extend {α κ K : Type} [Field K] [CharZero K] (S : Finset α) (C : α → Prop) (f : α → κ → K) (k0 : κ) :
    ∃ g : α → κ → K, (∀ a, C a → g a = f a) ∧
      ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → ¬ (C a ∧ C a') → g a k0 ≠ g a' k0 := by
  classical
  set Ex : Finset K := (S.filter C).image (fun a => f a k0)
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  have hinf : ((Ex : Set K)ᶜ).Infinite := Ex.finite_toSet.infinite_compl
  haveI := hinf.to_subtype
  let e : ℕ ↪ ((Ex : Set K)ᶜ : Set K) := Infinite.natEmbedding _
  set U := S.filter (fun a => ¬ C a)
  let idx : α → ℕ := fun a => if h : a ∈ U then ((U.equivFin ⟨a, h⟩ : Fin U.card) : ℕ) else 0
  refine ⟨fun a => if C a then f a else fun _ => (e (idx a) : K), fun a ha => by simp [ha], ?_⟩
  intro a ha a' ha' hne hC
  have hidx : ∀ b ∈ S, ¬ C b → ∀ b' ∈ S, ¬ C b' → idx b = idx b' → b = b' := by
    intro b hb hCb b' hb' hCb' h
    have hbU : b ∈ U := Finset.mem_filter.2 ⟨hb, hCb⟩
    have hbU' : b' ∈ U := Finset.mem_filter.2 ⟨hb', hCb'⟩
    simp only [idx, dif_pos hbU, dif_pos hbU'] at h
    have := U.equivFin.injective (Fin.ext h)
    exact congrArg Subtype.val this
  have hnot : ∀ n, (e n : K) ∉ Ex := fun n => (e n).2
  by_cases h1 : C a
  · have h2 : ¬ C a' := fun h2 => hC ⟨h1, h2⟩
    simp only [if_pos h1, if_neg h2]
    intro h
    have hm : f a k0 ∈ Ex := Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, h1⟩, rfl⟩
    rw [h] at hm
    exact hnot _ hm
  · by_cases h2 : C a'
    · simp only [if_neg h1, if_pos h2]
      intro h
      have hm : f a' k0 ∈ Ex := Finset.mem_image.2 ⟨a', Finset.mem_filter.2 ⟨ha', h2⟩, rfl⟩
      rw [← h] at hm
      exact hnot _ hm
    · simp only [if_neg h1, if_neg h2]
      intro h
      exact hne (hidx a ha h1 a' ha' h2 (e.injective (Subtype.ext h)))

end GlobalTheory.TrPass

namespace GlobalTheory.TrPass

theorem exists_inert_passage : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → (∀ χ ∈ A3.A.X, IsAbsIrrChar χ) → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hCW hEx hSch hJ hAbs hPB hPP
  classical
  have hlab : ∀ (j : Fin D.R.m) P d, IsLab (Yc D 0) P d ↔ IsLab (Wc D j) P d := by
    intro j P d
    rw [GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing, GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing]
    have h1 : (Yc D 0).rank = D.R.r := by
      rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]; simp [Ranks.rankY]
    have h2 : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
    rw [h1, h2]
  let Wit : ∀ j : Fin D.R.m, A3.fam3.base3.Ix → (Pl D.host.E → List ℤ → ℂ) →
      ((A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) → Prop :=
    fun j p c s => R.Carries p c ∧ ∃ x : (A3.A.fam.L j A3.A.μ0).S.Forms,
      x ∈ BlockGood.goodR (A3.A.fam.L j A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) ∧
      (∀ i, (A3.liftI j A3.A.μ0).opAll i x = s i • x) ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧
      R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0
  have key : ∀ j p c s p' c' s', Wit j p c s → Wit j p' c' s' → ∀ Q : A3.okI A3.A.μ0,
      ((∀ y, p.1.2 (Q.1, y) = p'.1.2 (Q.1, y)) ↔ ∀ y, s (Sum.inr (Q, y)) = s' (Sum.inr (Q, y))) := by
    intro j p c s p' c' s' hw hw' Q
    obtain ⟨hc, x, -, hx, hxW, hx0⟩ := hw
    obtain ⟨hc', x', -, hx', hxW', hx0'⟩ := hw'
    rw [GlobalTheory.T.inertTypeEigenvalues_iff_labelEigensystems_rows hHowe R F hLI hCW hEx hSch hJ hPB hPP p p' c c' hc hc' Q,
      GlobalTheory.T.liftInertEigenvalues_iff_thetaImageEigensystem hHowe R F hLI hCW hEx hSch hJ hAbs j c c' s s' x x' hx hxW hx0 hx' hxW' hx0' Q]
    exact forall_congr' fun d => imp_congr_left (hlab j _ d)
  let Cons : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → Prop := fun j a => ∃ p c s, Wit j p c s ∧ p.1.2 = a
  let f : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL := fun j a k =>
    if h : Cons j a then
      (if hk : k.1 ∈ A3.okI A3.A.μ0 then h.choose_spec.choose_spec.choose (Sum.inr (⟨k.1, hk⟩, k.2)) else 0)
    else 0
  have hf : ∀ j a (h : Cons j a) (Q : A3.okI A3.A.μ0) y,
      f j a (Q.1, y) = h.choose_spec.choose_spec.choose (Sum.inr (Q, y)) := by
    intro j a h Q y
    simp only [f, dif_pos h, dif_pos Q.2]
  have hspec : ∀ j a (h : Cons j a),
      Wit j h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose ∧ h.choose.1.2 = a :=
    fun j a h => h.choose_spec.choose_spec.choose_spec
  let S : Finset (I0 × List ℕ → D.what₂.LL) := ((A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X).image Prod.snd
  have hg : ∀ j, ∃ g : (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL, (∀ a, Cons j a → g a = f j a) ∧
      ∀ _q : A3.okI A3.A.μ0, ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → ¬ (Cons j a ∧ Cons j a') →
        ∃ k : A3.okI A3.A.μ0 × List ℕ, g a (k.1.1, k.2) ≠ g a' (k.1.1, k.2) := by
    intro j
    by_cases hne : Nonempty (A3.okI A3.A.μ0)
    · obtain ⟨q⟩ := hne
      obtain ⟨g, hg1, hg2⟩ := sep_extend S (Cons j) (f j) (q.1, ([] : List ℕ))
      exact ⟨g, hg1, fun _ a ha a' ha' hne hC => ⟨(q, []), hg2 a ha a' ha' hne hC⟩⟩
    · exact ⟨f j, fun _ _ => rfl, fun q => (hne ⟨q⟩).elim⟩
  choose g hg1 hg2 using hg
  refine ⟨g, ?_, ?_⟩
  · intro j p c hc s hx k
    have hC : Cons j p.1.2 := ⟨p, c, s, ⟨hc, hx⟩, rfl⟩
    rw [hg1 j _ hC]
    change s (Sum.inr k) = f j p.1.2 (k.1.1, k.2)
    rw [hf j _ hC k.1 k.2]
    obtain ⟨hw, ha⟩ := hspec j _ hC
    exact (((key j _ _ _ p c s hw ⟨hc, hx⟩ k.1).1 (fun y => by rw [ha])) k.2).symm
  · intro j p hp p' hp' hk
    obtain ⟨k0, hk0⟩ := hk
    by_cases hC : Cons j p.2 ∧ Cons j p'.2
    · by_contra hcon
      push_neg at hcon
      obtain ⟨hw, ha⟩ := hspec j _ hC.1
      obtain ⟨hw', ha'⟩ := hspec j _ hC.2
      have := (key j _ _ _ _ _ _ hw hw' k0.1).2 (fun y => by
        have h1 := hcon (k0.1, y)
        rw [hg1 j _ hC.1, hg1 j _ hC.2, hf j _ hC.1, hf j _ hC.2] at h1
        exact h1) k0.2
      rw [ha, ha'] at this
      exact hk0 this
    · have hne : p.2 ≠ p'.2 := fun h => hk0 (by rw [h])
      exact hg2 j k0.1 p.2 (Finset.mem_image_of_mem _ hp) p'.2 (Finset.mem_image_of_mem _ hp') hne hC

end GlobalTheory.TrPass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromD
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

namespace GlobalTheory.Ggeo.AdmEntInt

theorem mod_three_eq_two_of_jacobiSym_neg_eq_one (d : ℕ) (h : jacobiSym (-(d : ℤ)) 3 = 1) : d % 3 = 2 := by
  rw [jacobiSym.mod_left] at h
  simp only [Nat.cast_ofNat] at h
  have : (-(d : ℤ)) % 3 = 0 ∨ (-(d : ℤ)) % 3 = 1 ∨ (-(d : ℤ)) % 3 = 2 := by omega
  rcases this with h0 | h0 | h0 <;> rw [h0] at h
  · norm_num at h
  · omega
  · norm_num at h

end GlobalTheory.Ggeo.AdmEntInt

theorem GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hIn D L hT Gi Gl K Y cX ex t hHyp h3 ep be sg
  intro u μ w hlf hd i hi _heven c c'
  have hlf' : LevFree Y u μ w := hlf
  obtain ⟨hAdm, hComb⟩ := GlobalTheory.Ggeo.KerComb.comb_of_tied hIn.algT D L hT Gi Gl K Y cX ex t hHyp u μ w hlf' i hi c c'
  have hd3 : D.what₂.places.resChar w = 3 → D.host.d % 3 = 2 := fun _ =>
    GlobalTheory.Ggeo.AdmEntInt.mod_three_eq_two_of_jacobiSym_neg_eq_one _ (D.host.split_small 3 Nat.prime_three (by norm_num) h3)
  have hJ := GlobalTheory.T.integralJets_normalisedThetaCombinations_away_d hIn D t.cc t.δ t.cc_ok t.δ_ok t.B t.χ t.χ_ok t.X t.seam t.seam_ok _ _ _ _ hAdm
    (D.what₂.places.resChar w) (t.ent.lam w) hd hd3 _ hComb
  let T := t.kf u μ w hlf'
  have hB := T.B_bas i hi.le c
  have hB' := T.B_bas (i + 1) hi c'
  have hK := GlobalTheory.T.integral_jets_realPlace_local_bases D (t.O u μ).dgen (t.O u μ).dgen_gen _ _ _ _ hAdm (D.what₂.places.resChar w) (t.ent.lam w)
    (T.B i c) (T.B (i + 1) c') (fun τ => T.c0 i c c' τ * TaylorLogMetric.lamC (t.ent.lam w) ((t.O u μ).dgen τ)) hB hB'
    (fun τ => by rw [norm_mul, T.unitAbs_eq_one, one_mul]) _ hJ
  rw [← T.th i hi c c'] at hK
  exact GlobalTheory.T.kvalGe_zero_of_integral_jets _ _ _ _ _ _ hK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumThetaSeriesShapeAtDAdaptedBases
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

namespace GlobalTheory.Ggeo.KerShapeD

theorem thetaKernelShapeAtD_ofKer_of_hyp_adapted : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
    (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → t.Adapted →
    ∀ ep be sg, OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hIn D L hT Gi Gl K Y cX ex t hH hA ep be sg
  intro u μ w hlev hcls i hi c c'
  have hpd : D.what₂.places.resChar w = D.host.d := by
    have h := hcls
    simp only [Host.cls, primeClass] at h
    split_ifs at h with h1 h2 h3 <;> first | exact h3 | cases h
  have hAd : AdPl D w := Or.inr (Or.inr hcls)
  have hlev' : LevFree Y u μ w := hlev
  obtain ⟨Pm, hBas, -, hConj, hTh⟩ := hA w hAd u μ hlev'
  have hStd : ∀ j, j ≤ D.R.m → ∀ cl, GlobalTheory.KerStd.StdBases D (t.ent.lam w) ((t.O u μ).lat j cl).1 (Pm j cl) :=
    fun j hj cl => GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat j cl).2.1 (fun τ => hBas j hj cl τ)
      (fun τ τ' h => hConj j hj cl τ τ' h)
  have hcomb := GlobalTheory.Ggeo.KerComb.comb_of_tied hIn.algT D L hT Gi Gl K Y cX ex t hH u μ w hlev' i hi c c'
  have hdg : IsDgen D t.cD := by
    rw [← t.O_dgen u μ]
    exact (t.O u μ).dgen_gen
  have hnorm : ∀ τ, ‖(fun _ => (1 : ℂ_[D.what₂.places.resChar w])) τ‖ ≤ ‖TaylorLogMetric.lamC (t.ent.lam w) (t.cD τ)‖ := by
    intro τ
    rw [GlobalTheory.EigenGenerator.norm_dgen_eq_one D t.cD hdg _ (t.ent.lam w) hpd τ]
    simp
  show OrbitPlaces.ShapeD D _ (t.ent.Th u μ w i c c')
  rw [hTh i hi c c', GlobalTheory.atLin_adCoef_eq_stdSer]
  exact GlobalTheory.T.shape_normalisedThetaCombinations_dualBases_at_d hIn D t.cc t.δ t.cc_ok t.δ_ok t.B t.χ t.χ_ok t.X t.seam t.seam_ok _ _ _ _ hcomb.1 _ (t.ent.lam w) hpd
    t.cD hdg (Pm i c) (Pm (i + 1) c') _ (hStd i hi.le c) (hStd (i + 1) hi c') hnorm _ hcomb.2

end GlobalTheory.Ggeo.KerShapeD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointOfConditions
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowPointLoc

theorem continuous_of_adic {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A ≃+* B) :
    Continuous f := by
  have hm : Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu
    apply hx
    have := hu.map (f.symm : B →+* A)
    simpa using this
  refine continuous_of_continuousAt_zero (f : A →+ B) ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := ((isAdic_iff.1 hB).2 s hs)
  have hopen := (isAdic_iff.1 hA).1 n
  refine Filter.mem_map.2 (Filter.mem_of_superset (hopen.mem_nhds (Ideal.zero_mem _)) ?_)
  intro x hx
  apply hn
  have h1 : f x ∈ Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Formalism.MainNotions.SumRepresentations.Conclusion42 D → Formalism.MainNotions.SumRepresentations.Conclusion41 D → RowPoint D.nd D.naut := by
  intro hL D P h42 _ i σ hne
  obtain ⟨Q, hQ⟩ := ((h42 i) σ hne).1.2
  obtain ⟨i', hi', P', x', hth, hx⟩ :=
    GlobalTheory.T.theta_lift_has_point_at_localisation_same_place D P.M P.H.hecke P.H.av P.H.cover (GlobalTheory.T.hecke_standard_twist hL D P) i σ Q hQ
  obtain ⟨hj, hw⟩ := (D.nd.locs_mem _ _ i').1 hi'
  have hl : D.nd.l i' = D.nd.l i := by rw [← D.nd.w_l i', ← D.nd.w_l i, hw]
  obtain ⟨φ, hφ⟩ := P.H.hecke.sameO i' i hj hw
  refine ⟨i', hj, hl, fun w _ => P.locW_eq i' i σ w, ⟨φ, ?_, fun z => (hφ z).symm⟩, P', x', hth, hx⟩
  exact continuous_of_adic (D.nd.O_adic i') (D.nd.O_adic i) φ

end GlobalTheory.RowPointLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrvG5OfLocalDualityStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conclusionG5_of_local_duality : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ D : D7, SumRepresentations.admitted D → RbEx D → SumRepresentations.ConclusionG5 D := by
  first | exact @GlobalTheory.LevelPlaces.local_conditions_at_level | exact GlobalTheory.LevelPlaces.local_conditions_at_level | (intros; apply GlobalTheory.LevelPlaces.local_conditions_at_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_block_type_at_split_place : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ S : Reading P.T, IsTrue P S → ∀ i w hw, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → TypeBlock S i w hw := by
  first | exact @GlobalTheory.TypeBlockPf.main | exact GlobalTheory.TypeBlockPf.main | (intros; apply GlobalTheory.TypeBlockPf.main <;> assumption)
end

