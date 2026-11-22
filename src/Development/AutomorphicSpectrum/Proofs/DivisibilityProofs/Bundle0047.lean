import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PureEqPureA
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0046
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.EdgesRouteSmall
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0032
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0011
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SplitQuadraticAlgebraOrder
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0006

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CountableCompactOpen
section
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT.Inj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.RT.Inj.Rank

theorem countable_compactOpen (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {U : Set X | IsOpen U ∧ IsCompact U}.Countable := by
  have hb := TopologicalSpace.isBasis_countableBasis X
  have hc := TopologicalSpace.countable_countableBasis X
  have hfin : {t : Set (Set X) | t.Finite ∧ t ⊆ TopologicalSpace.countableBasis X}.Countable :=
    Set.countable_setOf_finite_subset hc
  refine (hfin.image fun t => ⋃₀ t).mono ?_
  rintro U ⟨hU, hK⟩
  obtain ⟨S, hS, rfl⟩ := hb.open_eq_sUnion hU
  obtain ⟨t, htS, htf, hcov⟩ := hK.elim_finite_subcover_image (b := S) (c := fun s => s)
    (fun s hs => hb.isOpen (hS hs)) Set.sUnion_eq_biUnion.subset
  refine ⟨t, ⟨htf, htS.trans hS⟩, Set.Subset.antisymm ?_ ?_⟩
  · exact Set.sUnion_subset_sUnion htS
  · simpa [Set.sUnion_eq_biUnion] using hcov

theorem mem_span_indicator {X : Type} [TopologicalSpace X] {f : X → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB X) :
    f ∈ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) := by
  classical
  obtain ⟨hl, hK⟩ := hf
  have hK' : IsCompact (tsupport f) := hK
  obtain ⟨t, ht⟩ := hK'.elim_finite_subcover (fun c : ℂ => f ⁻¹' {c})
    (fun c => hl.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hsum : f = ∑ c ∈ t, c • (f ⁻¹' {c}).indicator (1 : X → ℂ) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_preimage,
      Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      have hx : x ∈ tsupport f := subset_tsupport f (fun h0 => hne (by simpa using h0))
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (ht hx)
      have : f x = c := hxc
      exact h (this ▸ hc)
  rw [hsum]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : c = 0
  · simp [hc]
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨hl.isOpen_fiber c, ?_⟩, rfl⟩)
    refine hK'.of_isClosed_subset (hl.isClosed_fiber c) fun x hx => subset_tsupport f ?_
    have : f x = c := hx
    simpa [Function.mem_support, this] using hc

theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  have hle : GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) :=
    fun f hf => mem_span_indicator hf
  refine (Submodule.rank_mono hle).trans ((rank_span_le _).trans ?_)
  exact Cardinal.le_aleph0_iff_set_countable.2 ((countable_compactOpen X).image _)

end GlobalTheory.CompanionTheory.Ar.RT.Inj.Rank
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DSApply
section
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct SchwartzMap LineDeriv
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.Lie

section Real

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def schV (L : V →L[ℝ] V →L[ℝ] ℝ) (a b : V) (φ : V → ℂ) : V → ℂ :=
  fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((L x b + L a b / 2 : ℝ) : ℂ)) * φ (x + a)

def dS (L : V →L[ℝ] V →L[ℝ] ℝ) (a b : V) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{a} f + (-(2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (L.flip b) f

variable [MeasurableSpace V]

def IsSchL (L : V →L[ℝ] V →L[ℝ] ℝ) (μ : Measure V) (ρ₀ : V → V → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Prop :=
  ∀ a b (h : Lp ℂ 2 μ), ρ₀ a b h =ᵐ[μ] schV L a b h

end Real

section Arch

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def trL (κ : Type) [Fintype κ] : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousBilinearMap (LinearMap.mk₂ ℝ
    (fun x y : κ → mixedEmbedding.mixedSpace F => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by rw [← map_add, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, add_mul])
    (fun c x y => by rw [← map_smul, Finset.smul_sum]; simp only [Pi.smul_apply, smul_mul_assoc])
    (fun x y y' => by rw [← map_add, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, mul_add])
    (fun c x y => by rw [← map_smul, Finset.smul_sum]; simp only [Pi.smul_apply, mul_smul_comm]))

variable (F) in

abbrev Ix (n d : ℕ) : Type := InfinitePlace F × Fin n × Fin d

def piM (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (u : Matrix (Fin n) (Fin d) (AE F E)) : Ix F n d → ℂ :=
  fun p => piInf (τ p.1) (u p.2.1 p.2.2)

open Classical in

def HM (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) :
    Matrix (Ix F n d) (Ix F n d) ℂ :=
  fun p q => if p.1 = q.1 then 2 * Complex.I * (τ p.1).1 (JX q.2.1 p.2.1) * (τ p.1).1 (JW q.2.2 p.2.2) else 0

open Classical in

def mM (τ : ∀ w : InfinitePlace F, EmbOver E w) (n : ℕ) {d : ℕ} (g : Matrix (Fin d) (Fin d) (AE F E)) :
    Matrix (Ix F n d) (Ix F n d) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2.1 = q.2.1 then piInf (τ p.1) (g p.2.2 q.2.2) else 0

def coA {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i)

def coB {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).2 i)

end Arch

end GlobalTheory.CompanionTheory.Ar.RT.Lie

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsSplitPlaceOutsideStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_place_outside : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois ℚ E] (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)), ∃ v ∉ S, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v ∧ Nonempty (E →ₐ[F] Fv F v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RT.exists_splitsFully_notMem | exact GlobalTheory.CompanionTheory.Ar.RT.exists_splitsFully_notMem | (intros; apply GlobalTheory.CompanionTheory.Ar.RT.exists_splitsFully_notMem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsUnitDetOfCartan
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Ar.RT

theorem det_ne_zero_of_cartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan M θ) : M.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hx : star v ≠ 0 := fun e => hv (by simpa using congrArg star e)
  have := h.2.2 (star v) hx
  rw [star_star, hMv, dotProduct_zero] at this
  simp at this

open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

theorem isUnit_det_of_cartan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (s : ℂ) (θ : Matrix (Fin n) (Fin n) ℂ)
    (h : IsCartan (s • J.map τ) θ) : IsUnit J.det := by
  refine isUnit_iff_ne_zero.mpr fun h0 => det_ne_zero_of_cartan h ?_
  rw [Matrix.det_smul, show (J.map τ).det = τ J.det from (RingHom.map_det τ J).symm, h0, map_zero, mul_zero]

open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

theorem acts_congr {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {T T' : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ, T Φ = T' Φ) {R : Type} [Zero R] {ev : AF F → R} {φ φ₁ : (κ → R) → ℂ} :
    Acts ev T φ φ₁ ↔ Acts ev T' φ φ₁ :=
  ⟨fun a r hr => (h _ hr.2).symm.trans (a r hr), fun a r hr => (h _ hr.2).trans (a r hr)⟩

end GlobalTheory.CompanionTheory.Ar.RT

end
end

