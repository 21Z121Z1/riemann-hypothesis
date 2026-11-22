import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSemiStable
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsIntegralConj
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LocIntSpan

theorem exists_finset_algebraMap_mem (s : Finset ℚ) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ q ∈ s,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  let d : ℤ := ∏ q ∈ s, (q.den : ℤ)
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun q _ => by exact_mod_cast q.den_nz
  have hfin : {v : HeightOneSpectrum ℤ | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hd)
  refine ⟨hfin.toFinset, fun v hv q hq => ?_⟩
  have hden : (q.den : ℤ) ∉ v.asIdeal := by
    intro h
    apply hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hq) h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q
  rw [e]
  have hq' : q = ((q.num : ℤ) : ℚ) / ((q.den : ℤ) : ℚ) := by
    push_cast; exact (Rat.num_div_den q).symm
  rw [hq', map_div₀]
  have h1 : v.valuation ℚ ((q.num : ℤ) : ℚ) ≤ 1 := by
    rw [show ((q.num : ℤ) : ℚ) = algebraMap ℤ ℚ q.num from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_le_one _
  have h2 : v.valuation ℚ ((q.den : ℤ) : ℚ) = 1 := by
    rw [show ((q.den : ℤ) : ℚ) = algebraMap ℤ ℚ q.den from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (v.intValuation_le_one _)
      (not_lt.1 fun h => hden ((v.intValuation_lt_one_iff_mem _).1 h))
  rw [h2, div_one]
  exact h1

theorem isIntegral_of_isIntegral_conj {R A : Type} [CommRing R] [Ring A] [Algebra R A] (X : Aˣ) (y : A)
    (h : IsIntegral R (↑X * y * ↑X⁻¹)) : IsIntegral R y := by
  let f : A →ₐ[R] A :=
    { toFun := fun z => ↑X⁻¹ * z * ↑X
      map_one' := by simp
      map_mul' := fun a b => by simp [mul_assoc]
      map_zero' := by simp
      map_add' := fun a b => by simp [mul_add, add_mul]
      commutes' := fun r => by
        show _ * _ * _ = _
        rw [mul_assoc, Algebra.commutes, Units.inv_mul_cancel_left] }
  have := h.map f
  simpa [f, mul_assoc] using this

theorem map_id_injective (K : Type) [CommRing K] [Algebra ℚ K] {L C : Type} [Ring L] [Algebra ℚ L] [Ring C]
    [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (hι : Function.Injective ι) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ K) ι) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := K) ι.toLinearMap hι

theorem mem_of_isIntegral (v : HeightOneSpectrum ℤ) {x : v.adicCompletion ℚ}
    (hx : IsIntegral (v.adicCompletionIntegers ℚ) x) : x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
  exact y.2

theorem trace_one_tmul' {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

end GlobalTheory.LocIntSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeMapRationalFunctionsGenericLinearFormNotMStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrime_map_rationalFunctions_generic_linearForm_not_mem : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)).IsPrime ∧ ((∃ j, X j ∉ P) → (∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L) ∉ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) := by
  first | exact @GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem | exact GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem | (intros; apply GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmallB
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

def IsSmallB (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) (y : v.adicCompletion ℚ ⊗[ℚ] M) : Prop :=
  ∀ i, Valued.v ((Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i) < 1

end GlobalTheory.AdicSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped TensorProduct

namespace GlobalTheory.DefTransfer

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def KP [IsCMField D.host.E] (n : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) : Set (UA D.host.E n) :=
  {x | x ∈ locU n P ∧ cLoc P x ∈ GlobalTheory.LFun.KGL P n}

def cj [IsCMField D.host.E] {V : HSp D} (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V) :
    UA D.host.E V.rank ≃* GA D V :=
  j.toMulEquiv.trans (MulAut.conj h₀⁻¹)

theorem cj_apply [IsCMField D.host.E] {V : HSp D} (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (x : UA D.host.E V.rank) : cj j h₀ x = h₀⁻¹ * j x * h₀ := by
  simp [cj, MulAut.conj_apply]
  rfl

def IsTransfer [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V) : Prop :=
  h₀ ∈ GfC V ∧
  (∀ x, x ∈ ratU D.host.E V.rank ↔ j x ∈ GQ V) ∧
  (∀ x, x ∈ finU D.host.E V.rank ↔ j x ∈ GfC V) ∧
  (∀ x, x ∈ infU D.host.E V.rank ↔ j x ∈ GinfC V) ∧
  (∃ A : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsUnit (A τ)) ∧
    ∀ τ x, infMat D.sp.cm.sig V.gram (θ τ) (j x) =
      A τ * (cEmb (tauE D τ) x : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (A τ)⁻¹) ∧
  (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x,
    x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ ∃ e f, IsPrimeIdem P e f ∧ SuppF V f (cj j h₀ x)) ∧
  (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, cj j h₀ x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P) ∧
  ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) d R, GlobalTheory.Hk3.SphOp V P d R →
    (∀ γ ∈ R, (cj j h₀).symm γ ∈ locU V.rank P ∧ HasDiv (Ov D.host.E P) d (cLoc P ((cj j h₀).symm γ))) ∧
    ∀ x ∈ locU V.rank P, HasDiv (Ov D.host.E P) d (cLoc P x) →
      ∃! γ, γ ∈ R ∧ ((cj j h₀).symm γ)⁻¹ * x ∈ KP V.rank P

variable {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (M : DSModel V S)

def IsStableCompl (W' W W₀ : Submodule ℂ (MMap M)) : Prop :=
  GlobalTheory.SphGal.IsStableSub θ M W₀ ∧ W₀ ≤ W ∧ W' ⊓ W₀ = ⊥ ∧ W' ⊔ W₀ = W

variable {θ M}

def uOf [IsCMField D.host.E] (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V) (W₀ : Submodule ℂ (MMap M)) :
    Submodule ℂ (UA D.host.E V.rank → ℂ) :=
  Submodule.span ℂ {φ | ∃ T ∈ W₀, ∃ v : M.Vec, φ = fun x => T v (j x * h₀)}

end GlobalTheory.DefTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeightWordApplyWeightVectorStatement
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isWeight_word_apply_weightVector : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ (μ : Fin n → ℝ) (w : V), IsWeight E μ w → ∀ l : List (Fin n × Fin n), IsWeight E (μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum) ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) := by
  first | exact @GlobalTheory.wordWeight | exact GlobalTheory.wordWeight | (intros; apply GlobalTheory.wordWeight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStabIffIsKStableOnFiniteVectors
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.KFinStab

theorem kStab_iff_kStableOn : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ U : Submodule ℂ D, FiniteDimensional ℂ U → (KStab ε E U ↔ IsKStableOn ε σ (U.map D.subtype)) := by
  intro n ε H _ _ σ D E hc hσ hirr hK U hU
  obtain ⟨S, E', hS⟩ := CompanionTheory.D.DSIC.hSmMod n ε H σ hσ
  have hDS : D ≤ S := fun v hv =>
    (hS.mem v).2 (CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs n ε H σ hσ hirr v ((hK.mem v).1 hv))
  set ι := Submodule.inclusion hDS with hι
  have hιinj : Function.Injective ι := Submodule.inclusion_injective hDS
  have hE : ∀ a b (v : D), E' a b (ι v) = ι (E a b v) := by
    intro a b v
    have key := GlobalTheory.realForm_spans n ε H (fun a b => (E a b v : H) - (E' a b (ι v) : H)) ?_ a b
    · apply Subtype.ext
      exact (sub_eq_zero.1 key).symm
    intro X hX
    have h1 := hK.real X hX v
    have h2 := hS.real X hX (ι v)
    have h3 : ((ι v : S) : H) = (v : H) := rfl
    rw [h3] at h2
    have h4 := h1.unique h2
    simp only [smul_sub, Finset.sum_sub_distrib, h4, sub_self]
  have hmap : (U.map ι).map S.subtype = U.map D.subtype := by
    rw [← Submodule.map_comp]
    rfl
  have : FiniteDimensional ℂ (U.map ι) := inferInstance
  have hL := CompanionTheory.D.DSIC.hStabLink n ε H σ S E' hσ hS (U.map ι) inferInstance
  rw [hmap] at hL
  refine Iff.trans ?_ hL
  constructor
  · intro h a b hab w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    rw [hE]
    exact Submodule.mem_map_of_mem (h a b hab v hv)
  · intro h a b hab v hv
    have := h a b hab (ι v) (Submodule.mem_map_of_mem hv)
    rw [hE] at this
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 this
    rwa [← hιinj hxe]

end GlobalTheory.KFinStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumCompMulEquivStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzIsogenyClassPointSum_comp_mulEquiv : ∀ {Γ Γ' G₁ G₂ : Type} [Group Γ] [Group Γ'] [Group G₁] [Group G₂] (e : Γ' ≃* Γ) (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), pointSum (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) θ K₁ K₂ γ δ f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  first | (exact @GlobalTheory.pointSum_comp_mulEquiv) | (exact GlobalTheory.pointSum_comp_mulEquiv) | (intros; apply GlobalTheory.pointSum_comp_mulEquiv  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumConjDataStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzIsogenyClassPointSum_conj_data : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ g₁ : G₁) (δ g₂ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), (∀ k ∈ K₁, ∀ x, f (k⁻¹ * x * k) = f x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ y, ι₁ y * γ = γ * ι₁ y) → (∀ y, ι₂ y * δ = δ * θ (ι₂ y)) → pointSum ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) θ K₁ K₂ (g₁⁻¹ * γ * g₁) (g₂⁻¹ * δ * θ g₂) f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  first | (exact @GlobalTheory.PointSumConj.pointSum_conj_data) | (exact GlobalTheory.PointSumConj.pointSum_conj_data) | (intros; apply GlobalTheory.PointSumConj.pointSum_conj_data  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairScalarIsomorphicEquivalenceStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzPairScalarIsomorphic_equivalence : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Equivalence (Pair.Rel (G := G)) := by
  first | (exact @GlobalTheory.LKMid.Pair.rel_equivalence) | (exact GlobalTheory.LKMid.Pair.rel_equivalence) | (intros; apply GlobalTheory.LKMid.Pair.rel_equivalence  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastWeightPositive
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem lastPos_wtA_of_kapIs : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → KapIs κ → ∀ i : Fin D.R.m, LastPos (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) :=
  fun D T κ h hκ i =>
    GlobalTheory.lastPos_wtA_of_pins D T.Q h.pins _ (inR i) (κ i) (GlobalTheory.HolDict.lastPos_of_kapIs D κ hκ i)

end GlobalTheory.HolRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullCongr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj
open GlobalTheory.MBLit

noncomputable section

namespace GlobalTheory.MBDesc

theorem lbIso_pullComp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso (L.pull (g ≫ f)) ((L.pull f).pull g) :=
  LBIso.chartPull (RigidBundleGlue.chartPullComp L f g _ rfl) (chartPullId _)
    ⟨idIso _, idIso_isGen (pull_isLB (pull_isLB hL f) g)⟩

theorem lbIso_pull_congr {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {f g : Y ⟶ X} (h : f = g) :
    LBIso (L.pull f) (L.pull g) := h ▸ ⟨idIso _, idIso_isGen (pull_isLB hL f)⟩

end GlobalTheory.MBDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevAgreesOfIsLift
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftAgrees

open Formalism.IndefR Formalism.L2.DIV

theorem cong_mul {R : Type} [CommRing R] {n : ℕ} (K U : Matrix (Fin n) (Fin n) R) (M : ℕ) (x y w w' : Fin n → R)
    (e : y - K *ᵥ x = M • w) (e' : U *ᵥ x - x = M • w') : y - (K * U) *ᵥ x = M • (w - K *ᵥ w') := by
  rw [smul_sub, ← e, ← Matrix.mulVec_smul, ← e', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
  abel

variable {D : D7}

theorem isLift_inv_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {g : Formalism.L2.DIV.G0 L.Pg L.r} {κ k : GA D V} (hκ : Lev.IsLevelLift V β L g κ) (hk : Lev.IsLevelLift V β L g k) :
    Lev.IsLevelLift V β L 1 (κ⁻¹ * k) := by
  have h1 : Lev.finE V (κ⁻¹ * k) ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
    rw [map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ.2.1) hk.2.1
  refine ⟨(GfC V).mul_mem ((GfC V).inv_mem hκ.1) hk.1, h1, ?_⟩
  have h2 := Formalism.L2.DIV.rTup_mul hκ.2.1 h1
  rw [← map_mul, mul_inv_cancel_left, hκ.2.2, hk.2.2] at h2
  exact (mul_eq_left.1 h2.symm)

theorem finCong_one_of_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : Formalism.IndefR.Links.IsSDFrame V β Λ 1) {κ : GA D V}
    (hκ : Lev.finE V κ ∈ St β) : GlobalTheory.Member.FinCong V 1 κ := by
  have hβ : IsFrame β Λ := h.choose_spec.1
  intro z hz
  have h1 := ((GlobalTheory.LevSplit.mem_St_iff β Λ hβ _).1 hκ).1 _ ((GlobalTheory.LiftLevel.latHat_iff_frame h z).1 hz)
  refine ⟨(finHom V κ).1 *ᵥ z - z, sub_mem ?_ hz, (one_smul _ _).symm⟩
  refine (GlobalTheory.LiftLevel.latHat_iff_frame h _).2 ?_
  convert h1 using 1
  funext i
  exact RingHom.map_mulVec (Lev.swapAE D) _ z i

set_option maxHeartbeats 1000000 in

theorem finCong_of_red (P : Formalism.L2.Host.PiBar D.host) {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : Formalism.IndefR.Links.IsSDFrame V β Λ 1) {u : GA D V}
    (h1 : u ∈ GfC V) (h2 : Lev.finE V u ∈ St β)
    (h3 : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (∃ k, P.Div k PP) → redFn β PP (Lev.finE V u) = 1) :
    GlobalTheory.Member.FinCong V (D.host.g 0 * D.host.g 1) u := by
  obtain ⟨l, ⟨hM, -⟩, hMb⟩ := Formalism.L2.Pj.levelPb_exists D P.pb P.pb_over
  obtain ⟨Kf, hK⟩ := (GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds D V l.M).1
  have hH := (GlobalTheory.Member.finCong_iff_half_and_kfHalf D _ l V).2 Kf hK
  have hN : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ l.Mb := by
    rw [hMb]; exact GlobalTheory.LiftLevel.natCast_mem_prod _
  have hsq : Squarefree l.Mb := (GlobalTheory.CoverHalf.squarefree_span_g D).squarefree_of_dvd
    (Ideal.dvd_span_singleton.2 hN)
  have hu : u ∈ Kf := (GlobalTheory.LiftLevel.mem_level_iff h hK hH hsq l.prod (by rw [hM]; exact hN) u).1
    ⟨h1, h2, fun PP hP => h3 PP (by rw [hMb, GlobalTheory.LiftLevel.prod_le_iff] at hP; exact hP)⟩
  rw [← hM]
  exact ((hK u).1 hu).2

theorem levAgrees_mul {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} {Mh : Ideal (𝓞 D.host.E)}
    {κ u : GA D V} {lev : La →ₗ[𝓞 D.host.E] La} (hκ : GlobalTheory.Member.FinCong V 1 κ) (hu : GlobalTheory.Member.FinCong V M u)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees V ι M Mh κ lev) : GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees V ι M Mh (κ * u) lev := by
  intro a ha
  obtain ⟨w, hw, e⟩ := h a ha
  have hm : ι a ∈ (⊤ : Ideal (𝓞 D.host.E)) • latG V 1 := by
    rw [Submodule.top_smul, ← hι.2]
    exact ⟨a, rfl⟩
  obtain ⟨w', hw', e'⟩ := ((GlobalTheory.Member.AALev.congruences_agree D V u).2 M ⊤).1
    (fun b _ z hz => hu _ (GlobalTheory.Member.halfVec_mem_latHat V b z hz)) _ hm
  refine ⟨w - (finHom V κ).1 *ᵥ w', sub_mem hw ((GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 hκ w' hw'), ?_⟩
  rw [map_mul, Units.val_mul]
  exact cong_mul _ _ M _ _ _ _ e e'

end GlobalTheory.LiftAgrees

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LiftAgrees.levAgrees_of_isLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat D A Ks) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → ∀ (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Formalism.IndefR.Links.Wc D i).rank → D.host.E)) (Mh : Ideal (𝓞 D.host.E)) (lev : G → La →ₗ[𝓞 D.host.E] La), LatEmb (Formalism.IndefR.Links.Wc D i) ι → Formalism.IndefR.FWT.LevIs R i ι (D.host.g 0 * D.host.g 1) Mh lev → ∀ (g : G) (k : GA D (Formalism.IndefR.Links.Wc D i)), Formalism.IndefR.Lev.IsLevelLift (Formalism.IndefR.Links.Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees (Formalism.IndefR.Links.Wc D i) ι (D.host.g 0 * D.host.g 1) Mh k (lev g) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i hIs La _ _ ι Mh lev hι hlev g k hk
  obtain ⟨κ, hκ, hag⟩ := hlev g
  have h1 := (GlobalTheory.LiftLevel.isLift_one_iff (R.βW i) (R.datWp i R.triv)
    (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le rfl _).1 (GlobalTheory.LiftAgrees.isLift_inv_mul hκ hk)
  have h2 := GlobalTheory.LiftAgrees.finCong_of_red R.C.P (hIs.βW i) h1.1 h1.2.1 fun PP hP => h1.2.2 PP ((hIs.Pg PP).2 hP)
  have h3 := GlobalTheory.LiftAgrees.finCong_one_of_St (hIs.βW i) (Formalism.L2.DIV.parLev_St hκ.2.1)
  have h4 := GlobalTheory.LiftAgrees.levAgrees_mul hι h3 h2 hag
  rwa [mul_inv_cancel_left] at h4
end

