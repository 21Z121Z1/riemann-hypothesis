import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Mathlib
import GroundTheory.AutomorphicForms.Bundle0018
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0005
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0037
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralHuaBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0373
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterFormulaOfDiscreteSeriesDatum
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCentralLeviCongruence
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetCoeff

theorem exists_coeff_geometric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (m : ℕ), 1 ≤ m → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β, a * u * a⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β) → (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β, a⁻¹ * z * a ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β) → ∀ (y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π) (Λ : ℂ), y ≠ 0 → (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y → ∃ (w : V) (l : Module.Dual ℂ V), (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, π g w = w) ∧ (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, l ∘ₗ π g = l) ∧ ∀ j : ℕ, l (π (a ^ j) w) = Λ ^ j := by
  classical
  intro k _ _ _ _ N V _ _ π hπ h β _ m hm a ha hcomm _ hconj y Λ hy hyK hΛ
  have hKc := GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k N m
  have hKo := GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m
  have hyfix : y ∈ GroundTheory.Automorphic.fixedVectors (GroundTheory.Automorphic.Parabolic.jacquetAction k N β π)
      ((GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m).subgroupOf
        (GroundTheory.Automorphic.Parabolic.levi k N β)) :=
    fun g hg => hyK g (Subgroup.mem_subgroupOf.1 hg)
  obtain ⟨⟨w, hw⟩, hwy⟩ :=
    GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective_congruenceSubgroup β hπ hm ⟨y, hyfix⟩
  have hqw : Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) w = y :=
    congrArg Subtype.val hwy
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π),
      f y = 1 := by
    have h0 : ¬ ∀ f : Module.Dual ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π), f y = 0 :=
      fun h' => hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 h')
    push_neg at h0
    obtain ⟨f, hf⟩ := h0
    exact ⟨(f y)⁻¹ • f, by simp [hf]⟩

  have hpowc : ∀ j : ℕ, ∀ g ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a ^ j * g = g * a ^ j := by
    intro j g hg
    exact ((show Commute a g from hcomm g hg).pow_left j)
  have hpowz : ∀ j : ℕ, ∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓
      GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β,
      (a ^ j)⁻¹ * z * a ^ j ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓
        GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β := by
    intro j
    induction j with
    | zero => intro z hz; simpa using hz
    | succ j ih =>
      intro z hz
      have := hconj _ (ih z hz)
      have e : (a ^ (j + 1))⁻¹ * z * a ^ (j + 1) = a⁻¹ * ((a ^ j)⁻¹ * z * a ^ j) * a := by
        rw [pow_succ]; group
      rwa [e]
  have hq : ∀ j : ℕ, Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) (π (a ^ j) w) =
      Λ ^ j • y := by
    intro j
    induction j with
    | zero => simp [hqw]
    | succ j ih =>
      have e : π (a ^ (j + 1)) w = π a (π (a ^ j) w) := by
        rw [pow_succ', map_mul, Module.End.mul_apply]
      have e2 := GroundTheory.Automorphic.Parabolic.jacquetAction_mk (F := k) (n := N) (β := β) π ⟨a, ha⟩
        (π (a ^ j) w)
      rw [e]
      refine e2.symm.trans ?_
      rw [ih, map_smul, hΛ, smul_smul, pow_succ]
  have hkey : ∀ j : ℕ, Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype)
      (GroundTheory.Automorphic.fixedProj π hπ.1 hKc hKo (π (a ^ j) w) : V) =
      Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) (π (a ^ j) w) := by
    intro j
    refine GroundTheory.Automorphic.Parabolic.mk_fixedProj_eq hπ.1 hKc hKo
      (GroundTheory.Automorphic.Parabolic.congruenceSubgroup_iwahoriFactorization' β hm)
      (fun z hz => ?_) (fun g hg => ?_)
    · have hz' := (Subgroup.mem_inf.1 (hpowz j z hz)).1
      have hzeq : z = a ^ j * ((a ^ j)⁻¹ * z * a ^ j) * (a ^ j)⁻¹ := by group
      have : π z (π (a ^ j) w) = π (a ^ j) (π ((a ^ j)⁻¹ * z * a ^ j) w) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [this, hw _ hz']
    · have hc := hpowc j g (Subgroup.mem_inf.1 hg).2
      rw [← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply,
        hw g (Subgroup.mem_inf.1 hg).1]
  refine ⟨w, f ∘ₗ Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) ∘ₗ
      (GroundTheory.Automorphic.fixedVectors π
        (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m)).subtype ∘ₗ
      GroundTheory.Automorphic.fixedProj π hπ.1 hKc hKo, hw, ?_, ?_⟩
  · intro g hg
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [GroundTheory.Automorphic.fixedProj_apply_act hπ.1 hKc hKo hg]
  · intro j
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [hkey j, hq j, map_smul, hf, smul_eq_mul, mul_one]

end GlobalTheory.CompanionTheory.JacquetCoeff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCentralLeviFixedSubmodule
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetEigen

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic GroundTheory.Automorphic.GLnLocal in

theorem exists_eigenvector_fixed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → ∀ (W T : Submodule ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π)) (Λ : ℂ), Λ ≠ 0 → T ≤ W → (∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ w ∈ W) → (∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ w - Λ • w ∈ T) → (∃ w ∈ W, w ∉ T) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π, y ≠ 0 ∧ (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) ∧ GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y := by
  intro k _ _ _ _ N V _ _ π hπ h β _hβ a ha hcomm W T Λ hΛ hTW hWst hWT hex
  obtain ⟨w₀, hw₀W, hw₀T⟩ := hex
  let J := GroundTheory.Automorphic.Parabolic.jacquetAction k N β π
  let KM : ℕ → Subgroup (GroundTheory.Automorphic.Parabolic.levi k N β) := fun m =>
    (congruenceSubgroup k N m).subgroupOf (GroundTheory.Automorphic.Parabolic.levi k N β)
  have hA := isAdmissible_jacquetRep (β := β) hπ
  obtain ⟨m₁, hm₁⟩ := exists_subgroupOf_congruenceSubgroup_subset (F := k) (n := N) (β := β)
    ((hA.1 w₀).mem_nhds (one_mem (stabilizerOf _ w₀)))
  have hfix₁ : w₀ ∈ fixedVectors J (KM m₁) := by
    have : w₀ ∈ fixedVectors (jacquetRep k N β π) (KM m₁) := fun x hx => hm₁ hx
    rwa [fixedVectors_jacquetRep_congruenceSubgroup] at this
  refine ⟨m₁, fun m hm => ?_⟩
  have hle : KM m ≤ KM m₁ := fun x hx =>
    Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone k N hm (Subgroup.mem_subgroupOf.1 hx))
  have hfix : w₀ ∈ fixedVectors J (KM m) := fixedVectors_antitone _ hle hfix₁
  have hfin : FiniteDimensional ℂ (fixedVectors J (KM m)) := by
    have := hA.2 (KM m) (isCompact_subgroupOf_levi (isCompact_congruenceSubgroup k N m))
      (isOpen_subgroupOf_levi (isOpen_congruenceSubgroup k N m))
    rwa [fixedVectors_jacquetRep_congruenceSubgroup] at this
  let A : Module.End ℂ _ := J ⟨a, ha⟩
  let W' : Submodule ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π) :=
    W ⊓ fixedVectors J (KM m)
  have hW'fin : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le inf_le_right
  have hst : ∀ w ∈ W', A w ∈ W' := by
    intro w hw
    refine ⟨hWst w hw.1, fun g hg => ?_⟩
    have hw2 := hw.2 g hg
    have hc : g * ⟨a, ha⟩ = ⟨a, ha⟩ * g := Subtype.ext (hcomm g g.2).symm
    show J g (J ⟨a, ha⟩ w) = J ⟨a, ha⟩ w
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    exact congrArg _ hw2
  let B : W' →ₗ[ℂ] W' := A.restrict hst
  let Tc : Submodule ℂ W' := T.comap W'.subtype
  have hw₀' : w₀ ∈ W' := ⟨hw₀W, hfix⟩
  have hsq : Tc.mkQ ∘ₗ B = (Λ • (LinearMap.id : (W' ⧸ Tc) →ₗ[ℂ] (W' ⧸ Tc))) ∘ₗ Tc.mkQ := by
    ext w
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    exact hWT _ w.2.1
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts W' (W' ⧸ Tc) B
    (Λ • (LinearMap.id : (W' ⧸ Tc) →ₗ[ℂ] (W' ⧸ Tc))) Tc.mkQ (Submodule.mkQ_surjective _) hsq Λ
    (Tc.mkQ ⟨w₀, hw₀'⟩)
    (fun h0 => hw₀T (by simpa [Tc] using (Submodule.Quotient.mk_eq_zero Tc).1 h0))
    rfl hΛ
  refine ⟨y, fun h0 => hy0 (Subtype.ext h0), fun g hg => y.2.2 g (Subgroup.mem_subgroupOf.2 hg), ?_⟩
  exact congrArg Subtype.val hy

end GlobalTheory.CompanionTheory.JacquetEigen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleIrreducibleCentralScalar
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SchurCentre

theorem scalar_acts_by_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → ∀ t : kˣ, ∃ c : ℂ, ∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v := by
  intro k _ _ _ _ N V _ _ π hs hirr hadm t
  haveI := hirr

  have hz : ∀ g : GL (Fin N) k, g * Matrix.GeneralLinearGroup.scalar (Fin N) t =
      Matrix.GeneralLinearGroup.scalar (Fin N) t * g := by
    intro g
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]
  set z := Matrix.GeneralLinearGroup.scalar (Fin N) t with hzdef
  have hcomm : ∀ (g : GL (Fin N) k) (w : V), π g (π z w) = π z (π g w) := by
    intro g w
    rw [← Module.End.mul_apply, ← map_mul, hz g, map_mul, Module.End.mul_apply]

  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    change (⊥ : Submodule ℂ V) = ⊤
    ext u
    simp [h u]

  let S : Subgroup (GL (Fin N) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  let K : Subgroup (GL (Fin N) k) := GlobalTheory.SplitWeil.KO k (Fin N) ⊓ S
  have hKo : IsOpen (K : Set (GL (Fin N) k)) :=
    (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N)).inter (hs v)
  have hKc : IsCompact (K : Set (GL (Fin N) k)) :=
    (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin N)).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen K hKo) (fun _ h => h.1)
  haveI hfd : FiniteDimensional ℂ (fixed π K) := hadm.2 K hKo hKc
  have hmem : ∀ w : V, w ∈ fixed π K ↔ ∀ h : K, π (h : GL (Fin N) k) w = w := by
    intro w
    show (∀ h : K, _ = _) ↔ _
    simp
  have hvK : v ∈ fixed π K := (hmem v).2 fun h => h.2.2
  haveI : Nontrivial (fixed π K) :=
    ⟨⟨⟨v, hvK⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hst : ∀ w ∈ fixed π K, π z w ∈ fixed π K := by
    intro w hw
    refine (hmem _).2 fun h => ?_
    rw [hcomm, (hmem w).1 hw h]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((π z).restrict hst)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hwc : π z (w : V) = c • (w : V) := by
    have := congrArg Subtype.val hw.apply_eq_smul
    simpa using this

  let f : Representation.IntertwiningMap π π :=
    { toLinearMap := π z - c • LinearMap.id
      isIntertwining' := by
        intro g
        ext u
        simp [hcomm] }
  refine ⟨c, fun u => ?_⟩
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | h0
  · exfalso
    apply hw0
    apply hb.1
    show π z (w : V) - c • (w : V) = f 0
    rw [hwc, sub_self, map_zero]
  · have := congrArg (fun F : Representation.IntertwiningMap π π => F u) h0
    have h1 : π z u - c • u = 0 := this
    exact sub_eq_zero.1 h1

end GlobalTheory.CompanionTheory.SchurCentre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramIntegral
section
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section
namespace GlobalTheory.CompanionTheory.BinaryDil

theorem fibre_unit_dilation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 0 < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf 1 M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf 1) minf → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ s t : Ainf F, IsUnit t → minf (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ (t ^ 2 * s)) = ((∏ w, ‖e t w‖₊) ^ (2 * M - 2)) • (minf (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s)).map (fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b lam hlam m hm e he s t ht
  have hloc : GlobalTheory.CompanionTheory.SW.IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨i1, i2, i3, i4, i5, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  set N : ℝ≥0 := ∏ w, ‖e t w‖₊ with hN
  have hN0 : N ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    have : IsUnit (e t) := ht.map e
    exact nnnorm_ne_zero_iff.2 (Pi.isUnit_iff.1 this w).ne_zero
  have hN2 : ∏ w, ‖e (t ^ 2) w‖₊ = N ^ 2 := by
    rw [hN, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    simp [map_pow]
  have hs1 := GlobalTheory.T.archimedean_haar_scaling_norm F e he lam hlam t ht
  have hs2 := GlobalTheory.T.archimedean_haar_scaling_norm F e he lam hlam (t ^ 2) (ht.pow 2)
  rw [hN2] at hs2
  have hk := GlobalTheory.T.coordinate_measure_scaling_tensor F E σ hσ M 2 b lam hlam t ht _ hs1
  let g : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E) := Matrix.of fun _ _ => algebraMap (Ainf F) (Ainf F ⊗[F] E) t
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact ht.map (algebraMap (Ainf F) (Ainf F ⊗[F] E))
  have hrm : (fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X g) =
      fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i := by
    funext X p i
    simp only [GlobalTheory.CompanionTheory.SW.rmul, Fin.sum_univ_one, g, Matrix.of_apply]
    rw [Subsingleton.elim p 0, mul_comm]
  have hsig : sigR (Ainf F) σ (algebraMap (Ainf F) (Ainf F ⊗[F] E) t) = algebraMap (Ainf F) (Ainf F ⊗[F] E) t := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  let τ : HermR (Ainf F) σ 1 → HermR (Ainf F) σ 1 := fun S =>
    ⟨fun i j => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j, by
      intro i j
      have := S.2 i j
      show sigR (Ainf F) σ (_ * _) = _ * _
      rw [map_mul, this, map_pow, map_pow, hsig]⟩
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j =
      algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j := fun _ _ _ => rfl
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Ainf F) σ 1) := ⟨rfl⟩
    have : Continuous τ := by
      refine Continuous.subtype_mk ?_ _
      refine continuous_pi fun i => continuous_pi fun j => ?_
      exact continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))
    exact this.measurable
  have hc := GlobalTheory.T.hermitian_measure_scaling_transform F E σ hσ 2 b lam hlam (t ^ 2) (ht.pow 2) _ hs2 τ hτm hτe
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) g * S * g := by
    intro S
    ext i j
    rw [hτe, map_pow, GlobalTheory.CompanionTheory.SW.Dil.cT_scalar _ _ hsig]
  have key := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ (Ainf F) hloc 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M)
    (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1) m (hW 1 M) (hH 1) hm g hg τ hτ _ _
    (by rw [hrm]; exact hk) hc (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s)
  have hτs : τ (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s) = GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ (t ^ 2 * s) := by
    apply Subtype.ext
    funext i j
    change algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (s ⊗ₜ[F] (1 : E)) = (t ^ 2 * s) ⊗ₜ[F] (1 : E)
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hτs, hrm] at key
  have e1 : (N ^ (2 * M)) * (N⁻¹ ^ (2 * M)) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hN0, one_pow]
  have e2 : (N ^ (2 * M)) * (N ^ 2)⁻¹ = N ^ (2 * M - 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [this, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hN0), mul_one]
    simp
  have key2 := congrArg (fun μ' => (N ^ (2 * M)) • μ') key
  simp only [smul_smul] at key2
  rw [e1, e2, one_smul] at key2
  exact key2

theorem dilation_inf_binary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)), IsStdInf li →
  ∀ (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E)),
  IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
  ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ ε : ℝ, 0 < ε → ∀ (s : Ainf F) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ), Continuous φ →
  ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) * ∫⁻ X, ENNReal.ofReal (φ (PositivityTheory.Rg.Mass.dil θ ε X)) ∂(mi (hermScal (Ainf F) σ s)) =
    ENNReal.ofReal ((ε ^ 2) ^ Module.finrank ℚ F) * ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ (θ (ε ^ 2) * s))) := by
  intro F E _ _ _ _ _ σ hσ J hJ d b li hli mi hm θ hθ ε hε s φ hφ
  obtain ⟨-, e, -, he, -, habs, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hσ.1
  obtain ⟨i1, i2, i3, i4, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Fin 1 → Fin 2 → Ainf F ⊗[F] E) := hB 1 2
  set t : Ainf F := θ ε with ht_def
  have ht : IsUnit t := (isUnit_iff_ne_zero.2 hε.ne').map θ
  have key := fibre_unit_dilation F E σ hσ 2 J hJ (by norm_num) d b li hli.1 mi hm e he s t ht
  set n := Module.finrank ℚ F with hn
  have hw : ∀ w, ‖e t w‖₊ = ε.toNNReal := by
    intro w
    have h1 := (PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real F hσ.1).2 θ hθ ε w
    have h2 := habs t w
    apply NNReal.eq
    rw [coe_nnnorm, Real.norm_eq_abs, h2, Real.coe_toNNReal _ hε.le]
    rw [show ‖t w‖ = ‖θ ε w‖ from rfl, h1, abs_of_pos hε]
  have hN : ∏ w, ‖e t w‖₊ = ε.toNNReal ^ n := by
    have hc : Fintype.card (InfinitePlace F) = n := by
      have := hσ.1
      rw [hn, IsTotallyReal.finrank F, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ, hc]
  have hs : θ (ε ^ 2) * s = t ^ 2 * s := by rw [map_pow]
  have hD : Continuous (fun (X : Fin 1 → Fin 2 → Ainf F ⊗[F] E) p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) :=
    continuous_pi fun p => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply p))
  have hf : Measurable (fun X => ENNReal.ofReal (φ X)) := hφ.measurable.ennreal_ofReal
  rw [hs, key, lintegral_smul_measure, lintegral_map hf hD.measurable, hN]
  have hdil : ∀ X, PositivityTheory.Rg.Mass.dil θ ε X = fun p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i := by
    intro X
    funext p i
    simp [PositivityTheory.Rg.Mass.dil, Algebra.TensorProduct.algebraMap_apply, ht_def]
  simp only [hdil]
  rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_pow, Real.coe_toNNReal _ hε.le]
  ring

end GlobalTheory.CompanionTheory.BinaryDil

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralHuaBoundStatement
section
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_orbital_integral_hua_bound : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ), (∀ w, (J w).IsHermitian) → (∀ w, (J w).det ≠ 0) →
  ∀ (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  ∃ C : ℝ, ∀ b : W → hermC n, ‖coreC J μ (fun X => f (e X)) b‖ ≤
    C * ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockCentralElementCommutesLevi
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ZjCentral

theorem leviEmb_zj_eq_diagonal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ)
    (j : Fin h) :
    ((leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1 := by
  ext i l
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, l'⟩, rfl⟩ := (stdBlocks d hd).surjective l
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hil : i' = l'
    · subst hil
      by_cases haj : a ≤ j
      · simp [Zl.JC.zj, Zl.JC.blockIdx, haj, Matrix.GeneralLinearGroup.scalar]
      · simp [Zl.JC.zj, Zl.JC.blockIdx, haj]
    · have hne : (stdBlocks d hd) ⟨a, i'⟩ ≠ (stdBlocks d hd) ⟨a, l'⟩ := fun e => hil (by
        simpa using (stdBlocks d hd).injective e)
      rw [Matrix.diagonal_apply_ne _ hne]
      by_cases haj : a ≤ j
      · simp [Zl.JC.zj, haj, Matrix.GeneralLinearGroup.scalar, hil]
      · simp [Zl.JC.zj, haj, hil]
  · have hne : (stdBlocks d hd) ⟨a, i'⟩ ≠ (stdBlocks d hd) ⟨b, l'⟩ := fun e => hab (by
      simpa using congrArg Sigma.fst ((stdBlocks d hd).injective e))
    rw [leviEmb_apply_ne k _ _ hab, Matrix.diagonal_apply_ne _ hne]

theorem leviEmb_zj_comm : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ)
    (j : Fin h), ∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd),
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) * y =
      y * leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) := by
  intro k _ _ _ _ h N d hd t j y hy
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, leviEmb_zj_eq_diagonal]
  ext i l
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hil : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l
  · rw [hil]
    exact mul_comm _ _
  · have h0 : (y : Matrix (Fin N) (Fin N) k) i l = 0 :=
      GroundTheory.Automorphic.Parabolic.mem_levi.1 hy i l hil
    rw [h0, mul_zero, zero_mul]

end GlobalTheory.CompanionTheory.ZjCentral
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliConstantTermVanishingStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_constant_term_vanishing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (F : Sm E (r + s)), ((∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) → (∀ m : GA E r × GA E s, (capR r s τ u F).1 (lev (Ad E) r s m) = 0) ∧ ∀ m : GA E r × GA E s, (capS r s τ u F).1 (lev (Ad E) r s m) = 0) ∧ ((∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (cap (a := r + s) τ u F).1 (unip x * g) = (cap (a := r + s) τ u F).1 g) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.CapStable.capStable | exact GlobalTheory.CompanionTheory.CTFin.CapStable.capStable | (intros; apply GlobalTheory.CompanionTheory.CTFin.CapStable.capStable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliUnseenStatementStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_restrict_levi : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (q : Polynomial ℂ) (F : Sm E (r + s)), (∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ m, (Polynomial.aeval (cap (a := r) τ u) q G).1 m = (Polynomial.aeval (capR r s τ u) q F).1 (lev (Ad E) r s (m, 1))) ∧ (∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ m, (Polynomial.aeval (cap (a := s) τ u) q G).1 m = (Polynomial.aeval (capS r s τ u) q F).1 (lev (Ad E) r s (1, m))) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.capelli_restrict | exact GlobalTheory.CompanionTheory.CTFin.capelli_restrict | (intros; apply GlobalTheory.CompanionTheory.CTFin.capelli_restrict <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterExistsStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k) (t : kˣ), ∃ c : ℂ, Zl.ScalarBy x t c := by
  first | exact @GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy | exact GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy | (intros; apply GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterFormulaOfDiscreteSeriesDatumStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_formula_of_discrete_series_datum : PositivityTheory.RgDs.Hilb.StepDatum → PositivityTheory.RgDs.Hilb.StepFormulaF := by
  first | exact @GlobalTheory.CompanionTheory.Hilb.stepFormulaF | exact GlobalTheory.CompanionTheory.Hilb.stepFormulaF | (intros; apply GlobalTheory.CompanionTheory.Hilb.stepFormulaF <;> assumption)
end

