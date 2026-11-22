import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0800
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0799
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0038
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0802
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0386
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneFibreMeasureLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0796
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0048
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0111
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSymmetric
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem measurable_PintF (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)
    (D : HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n =>
      Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  obtain ⟨iTR, iLR, iSR, iTR2, -⟩ := D.hR
  haveI := iTR
  haveI := iLR
  haveI := iSR
  haveI := iTR2
  obtain ⟨iTK, iLK, iSK, iT2K, -, -, -, iBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := iTK
  haveI := iLK
  haveI := iSK
  haveI := iT2K
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, ⟨κ, hκs, hκm⟩, -, -⟩ :=
    GlobalTheory.T.local_fibre_measure_orthogonal_sum F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hloc₁, -⟩ :=
    GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨-, -, iSH, -, iBH, hH⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  haveI := iSH
  haveI := iBH
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := iBor n M
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := iBor (n + 1) (M + 1)
  haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := iBor 1 (M + 1)
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hact := (hH (n + 1)).1
  have hten : Measurable (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have hc : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ : R => (1 : R ⊗[F] E))
        continuous_id continuous_const
    have he : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [he]
    exact hc.measurable
  haveI : IsSFiniteKernel κ := hκs
  let κ' : Kernel ((R × (Fin n → R ⊗[F] E) × HermR R σ n) × (Fin 1 → Fin (M + 1) → R ⊗[F] E))
      (Fin n → Fin M → R ⊗[F] E) :=
    κ.comap (fun p => p.1.2.2) (measurable_snd.comp (measurable_snd.comp measurable_fst))
  haveI := hloc₁ (hermScal R σ (algebraMap F R t))
  have hvec : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2 : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
    measurable_vec_triple.comp ((hten.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      (((measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))).prodMk
        measurable_snd))
  have hΦ : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s q.1.2)
          (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2)) :=
    hact.measurable.comp ((D.hs.comp (measurable_snd.comp measurable_fst)).prodMk hvec)
  have hinner := Measurable.lintegral_kernel_prod_right' (κ := κ') (hφ.comp hΦ)
  have hfin := Measurable.lintegral_prod_right' (ν := m₁ (hermScal R σ (algebraMap F R t))) hinner
  have hm'κ : m' = fun S => κ S := funext fun S => (hκm S).symm
  rw [hm'κ]
  exact hfin

end GlobalTheory.CompanionTheory.SW.StageF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalPairTyped
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.FdPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSpace_eq_prodSpan (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ = prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro F ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩
  · refine Submodule.span_mono ?_
    rintro F ⟨_, ⟨φ₁, h₁, rfl⟩, _, ⟨φ₂, h₂, rfl⟩, rfl⟩
    exact ⟨φ₁, h₁, φ₂, h₂, rfl⟩

theorem map_typed {N : ℕ} (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E)))
    (W : Submodule ℂ (Kinf E N → ℂ)) :
    U.map (Sm E N).subtype ⊓ typeF K W = (typed U K W).map (Sm E N).subtype := by
  ext f
  constructor
  · rintro ⟨⟨φ, hφ, rfl⟩, hS⟩
    exact ⟨φ, ⟨hφ, hS⟩, rfl⟩
  · rintro ⟨φ, ⟨hφ, hS⟩, rfl⟩
    exact ⟨⟨φ, hφ, rfl⟩, hS⟩

theorem slice_left {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : TypeH K₁ K₂ W₁ W₂ F) (y : GA E b) : (fun x => F (x, y)) ∈ typeF K₁ W₁ := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have := hF.1 u hu 1 K₂.one_mem (g, y)
    simpa using this
  · let L : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
      { toFun := fun f k => f (k, 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hL : Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}
        ≤ W₁.comap L := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨w₁, h₁, w₂, h₂, rfl⟩
      have : L (fun k => w₁ k.1 * w₂ k.2) = w₂ 1 • w₁ := by
        funext k
        simp [L, mul_comm]
      show L _ ∈ W₁
      rw [this]
      exact W₁.smul_mem _ h₁
    have := hL (hF.2 (g, y))
    simpa [L] using this

theorem slice_right {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : TypeH K₁ K₂ W₁ W₂ F) (x : GA E a) : (fun y => F (x, y)) ∈ typeF K₂ W₂ := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have := hF.1 1 K₁.one_mem u hu (x, g)
    simpa using this
  · let L : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E b → ℂ) :=
      { toFun := fun f k => f (1, k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hL : Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}
        ≤ W₂.comap L := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨w₁, h₁, w₂, h₂, rfl⟩
      have : L (fun k => w₁ k.1 * w₂ k.2) = w₁ 1 • w₂ := by
        funext k
        simp [L]
      show L _ ∈ W₂
      rw [this]
      exact W₂.smul_mem _ h₂
    have := hL (hF.2 (x, g))
    simpa [L] using this

theorem finiteDimensional_pairSpace_inf_typeHF : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E)))
    (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)),
    FiniteDimensional ℂ (typed U₁ K₁ W₁) → FiniteDimensional ℂ (typed U₂ K₂ W₂) →
    FiniteDimensional ℂ ((pairSpace U₁ U₂ ⊓ typeHF K₁ K₂ W₁ W₂ : Submodule ℂ (H E a b → ℂ))) := by
  intro E _ _ _ a b U₁ U₂ K₁ K₂ W₁ W₂ h₁ h₂
  have f₁ : FiniteDimensional ℂ (U₁.map (Sm E a).subtype ⊓ typeF K₁ W₁ : Submodule ℂ (GA E a → ℂ)) := by
    rw [map_typed]; infer_instance
  have f₂ : FiniteDimensional ℂ (U₂.map (Sm E b).subtype ⊓ typeF K₂ W₂ : Submodule ℂ (GA E b → ℂ)) := by
    rw [map_typed]; infer_instance
  haveI hfd := GlobalTheory.T.finiteDimensional_prodSpan (U₁.map (Sm E a).subtype ⊓ typeF K₁ W₁) (U₂.map (Sm E b).subtype ⊓ typeF K₂ W₂) f₁ f₂
  refine Submodule.finiteDimensional_of_le (S₂ := prodSpan (U₁.map (Sm E a).subtype ⊓ typeF K₁ W₁)
    (U₂.map (Sm E b).subtype ⊓ typeF K₂ W₂)) ?_
  rintro F ⟨hU, hT⟩
  rw [SetLike.mem_coe, pairSpace_eq_prodSpan] at hU
  exact GlobalTheory.T.mem_prodSpan_inf _ _ _ _ F hU (fun y => slice_left hT y) (fun x => slice_right hT x)

end GlobalTheory.CompanionTheory.LimV.FdPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedExtension
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem typed_tw_finite {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    (U : Submodule ℂ (Sm E N)) (z : ℂ)
    (H : ∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)),
      IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U K W))
    (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (hW : FiniteDimensional ℂ W) :
    FiniteDimensional ℂ (typed (tw U z) K W) := by
  have hK₀ : IsOpen ((K ⊓ KO E N : Subgroup (GL (Fin N) (Af E))) : Set (GL (Fin N) (Af E))) := by
    rw [Subgroup.coe_inf]
    exact hK.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E N)
  have hfin := H (K ⊓ KO E N) W hK₀ hW
  have hflat : FlatFn (absFn (E := E) N (-z)) := GlobalTheory.T.flat_absolute_character N (-z)
  have hval : ∀ (φ : Sm E N) x, (mulChi N (GlobalTheory.CuspRep.Model.absC E (-z)) φ).1 x =
      absFn N (-z) x * φ.1 x := fun φ x => by
    simp only [mulChi_apply, absFn]
    exact mul_comm _ _
  have hfinv : ∀ (g : GA E N), ∀ u ∈ KO E N, absFn (E := E) N (-z) (g * finGL E N u) = absFn N (-z) g := by
    intro g u hu
    have := hflat.rinv g 1 u hu
    simpa [cf] using this
  have hkinv : ∀ (g : GA E N) (k : Kinf E N),
      absFn (E := E) N (-z) (g * infGL E N (Unitary.toUnits k)) = absFn N (-z) g := by
    intro g k
    have := hflat.rinv g k 1 (one_mem _)
    simpa [cf] using this
  let L : Sm E N ≃ₗ[ℂ] Sm E N := mulChi N (GlobalTheory.CuspRep.Model.absC E (-z))
  have hle : (typed (tw U z) K W).map (L : Sm E N →ₗ[ℂ] Sm E N) ≤ typed U (K ⊓ KO E N) W := by
    rintro _ ⟨φ, ⟨⟨ψ, hψ, rfl⟩, hlev, htype⟩, rfl⟩
    set φ : Sm E N := mulChi N (GlobalTheory.CuspRep.Model.absC E z) ψ with hφ
    have hL : ∀ x, (L φ).1 x = absFn N (-z) x * φ.1 x := hval φ
    refine ⟨?_, ?_, ?_⟩
    · have hback : L φ = ψ := by
        refine Subtype.ext (funext fun x => ?_)
        have e : ∀ s : ℂ, ((chiDet N (GlobalTheory.CuspRep.Model.absC E s) x : ℂˣ) : ℂ) =
            Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x)) := fun _ => rfl
        rw [hL, hφ, mulChi_apply, absFn, e, e, mul_left_comm, ← Complex.exp_add]
        simp
      show L φ ∈ U
      rw [hback]
      exact hψ
    · intro u hu g
      have h2 : φ.1 (g * finGL E N u) = φ.1 g := hlev u hu.1 g
      show (L φ).1 (g * finGL E N u) = (L φ).1 g
      rw [hL, hL, hfinv g u hu.2, h2]
    · intro g
      have h3 : (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W := htype g
      have h4 : (fun k : Kinf E N => (L φ).1 (g * infGL E N (Unitary.toUnits k))) =
          absFn N (-z) g • (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) := by
        funext k
        rw [hL, hkinv g k]
        rfl
      show (fun k : Kinf E N => (L φ).1 (g * infGL E N (Unitary.toUnits k))) ∈ W
      rw [h4]
      exact W.smul_mem _ h3
  have h1 : FiniteDimensional ℂ ((typed (tw U z) K W).map (L : Sm E N →ₗ[ℂ] Sm E N)) :=
    Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (L.submoduleMap (typed (tw U z) K W)).symm

end GlobalTheory.CompanionTheory.LimV
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedNode
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV.FdNode

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N r s : ℕ}

theorem memInd2_of_mem_indSpan {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ indSpan U₁ U₂) : MemInd2 U₁ U₂ φ := by
  unfold indSpan at h
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => (tens2 U₁ U₂).zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u g => ?_, fun k g => (tens2 U₁ U₂).add_mem (hx.2 k g) (hy.2 k g)⟩
    change x.1 _ + y.1 _ = x.1 _ + y.1 _
    rw [hx.1, hy.1]
  | smul c x _ hx =>
    refine ⟨fun u g => ?_, fun k g => (tens2 U₁ U₂).smul_mem c (hx.2 k g)⟩
    change c • x.1 _ = c • x.1 _
    rw [hx.1]

def sliceMap (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) :
    Sm E (r + s) →ₗ[ℂ] (GA E r × GA E s → ℂ) where
  toFun φ m := φ.1 (lev (Ad E) r s m * cf (r + s) k t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tensor_le_prodSpan (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) :
    tens2 U₁ U₂ ≤ prodSpan (U₁.map (Sm E r).subtype) (U₂.map (Sm E s).subtype) := by
  refine Submodule.span_le.2 ?_
  rintro F ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact Submodule.subset_span ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩

theorem fd_inf (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (h : FiniteDimensional ℂ (typed U K W)) :
    FiniteDimensional ℂ ↥(U.map (Sm E N).subtype ⊓ typeF K W) := by
  have hle : U.map (Sm E N).subtype ⊓ typeF K W ≤ (typed U K W).map (Sm E N).subtype := by
    rintro f ⟨⟨φ, hφ, rfl⟩, hf⟩
    exact ⟨φ, ⟨hφ, hf⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end SlopeTestRemainingChoices

theorem finiteDimensional_typed_indSpan : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)), (∀ (K : Subgroup (GL (Fin r) (Af E))) (W : Submodule ℂ (Kinf E r → ℂ)), IsOpen (K : Set (GL (Fin r) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₁ K W)) → (∀ (K : Subgroup (GL (Fin s) (Af E))) (W : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K : Set (GL (Fin s) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₂ K W)) → ∀ (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed (indSpan U₁ U₂) K W) := by
  intro E _ _ _ r s U₁ U₂ h₁ h₂ K W hK hW
  obtain ⟨T, hT⟩ := GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets E r s K hK
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finite_determining_set W hW
  choose K₁ W₁ oK₁ fW₁ sl₁ using
    fun i : Kinf E (r + s) × GL (Fin (r + s)) (Af E) => GlobalTheory.T.typed_first_block_restriction i.1 i.2 K W hK hW
  choose K₂ W₂ oK₂ fW₂ sl₂ using
    fun i : Kinf E (r + s) × GL (Fin (r + s)) (Af E) => GlobalTheory.T.typed_second_block_restriction i.1 i.2 K W hK hW
  let P : ↥S × ↥T → Submodule ℂ (GA E r × GA E s → ℂ) := fun i =>
    prodSpan (U₁.map (Sm E r).subtype ⊓ typeF (K₁ (i.1.1, i.2.1)) (W₁ (i.1.1, i.2.1)))
      (U₂.map (Sm E s).subtype ⊓ typeF (K₂ (i.1.1, i.2.1)) (W₂ (i.1.1, i.2.1)))
  haveI : ∀ i, FiniteDimensional ℂ (P i) := fun i =>
    GlobalTheory.T.finiteDimensional_prodSpan _ _ (fd_inf _ _ _ (h₁ _ _ (oK₁ _) (fW₁ _))) (fd_inf _ _ _ (h₂ _ _ (oK₂ _) (fW₂ _)))
  have hmem : ∀ (i : ↥S × ↥T) (φ : typed (indSpan U₁ U₂) K W), sliceMap i.1.1 i.2.1 φ.1 ∈ P i := by
    intro i φ
    have hmi := memInd2_of_mem_indSpan φ.2.1
    exact GlobalTheory.T.mem_prodSpan_inf _ _ _ _ _ (tensor_le_prodSpan U₁ U₂ (hmi.2 i.1.1 i.2.1))
      (fun y => sl₁ (i.1.1, i.2.1) _ φ.2.2 y) (fun x => sl₂ (i.1.1, i.2.1) _ φ.2.2 x)
  let Φ : typed (indSpan U₁ U₂) K W →ₗ[ℂ] ∀ i, P i := LinearMap.pi fun i =>
    ((sliceMap i.1.1 i.2.1).comp (Submodule.subtype _)).codRestrict (P i) (hmem i)
  refine FiniteDimensional.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun φ hφ => ?_)
  have hz : ∀ a ∈ S, ∀ t ∈ T, ∀ m, φ.1.1 (lev (Ad E) r s m * cf (r + s) a t) = 0 := by
    intro a ha t ht m
    have e := congrArg Subtype.val (congrFun hφ (⟨a, ha⟩, ⟨t, ht⟩))
    exact congrFun e m
  have hmi := memInd2_of_mem_indSpan φ.2.1
  have hty : φ.1.1 ∈ typeF K W := φ.2.2
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  obtain ⟨x, m, t, k, l, ht, hl, rfl⟩ := hT g
  have e : unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l =
      unip x * (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k)) * finGL E (r + s) l := by
    simp only [mul_assoc]
  rw [e, hty.1 l hl, hmi.1]
  have hw := hS _ (hty.2 (lev (Ad E) r s m * finGL E (r + s) t)) (fun a ha => by
    have h0 := hz a ha t ht m
    rw [cf, infGL_comm, ← mul_assoc] at h0
    exact h0)
  exact congrFun hw k

end GlobalTheory.CompanionTheory.LimV.FdNode

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeUnramifiedAlmostAll
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageGoodFree

theorem stage_good_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree (Fv F v) σ J n μ ν m → ∀ h : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m (hermOf (Fv F v) σ T hT) {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m (hermOf (Fv F v) σ T hT) (latV b v)) (actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT d b
  obtain ⟨hdet, hherm, -, -⟩ := BlockAlg.block_alg F E σ hCM M J t
  have hND : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hherm hJ.1, by
      rw [hdet]
      exact mul_ne_zero (by simpa using ht) hJ.2⟩
  filter_upwards [GoodTrans.good_trans F E σ hCM (M + 1) _ hND t ht d b,
    (LatRat.latV_rational F E σ hCM d b n M).2.2, (LatRat.latV_rational F E σ hCM d b 0 M).2.2]
    with v hv hv1 hv0
  intro μ ν m hμ hν hm h
  have hLoc := LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hLoc
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hBorel, -, -⟩ := TopK.topTens_props F E σ hCM (Fv F v)
  have := hBorel n M
  have hOpen := ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2
  obtain ⟨-, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) _ hND (Fv F v)
  obtain ⟨-, -, -, -, -, hactJ⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (Fv F v)
  obtain ⟨-, hone, hmul, hgram⟩ := hact 1
  by_cases he : actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) ∈ latV b v
  · rw [Set.indicator_of_mem he]
    have he0 : (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) ∈ latV b v := by
      have h0 := (hv0 (fun a : Fin 0 => a.elim0)).2 (fun a => a.elim0)
      have hc : consTup (fun a : Fin 0 => a.elim0) =
          (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) := by
        funext a
        exact Fin.cases rfl (fun j => j.elim0) a
      rwa [hc] at h0
    obtain ⟨k, hk, hkl⟩ := hv _ _ he0 he (StageGood.gram_first (Fv F v) σ J t) (hgram h _)
    obtain ⟨ι, -, -, hrange, -, hcons⟩ := StabFirst.stab_first F E σ hCM M J hJ t ht (Fv F v)
    have hg : actW (Fv F v) σ _ (k⁻¹ * h) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) =
        (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) := by
      rw [hmul, ← hk, ← hmul, inv_mul_cancel, hone]
    obtain ⟨u, hu⟩ := (hrange _).2 hg
    have hh : h = k * ι u := by rw [hu]; group
    have hset : {X : Fin n → Fin M → Fv F v ⊗[F] E | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} =
        actW (Fv F v) σ J u ⁻¹' latV b v := by
      ext X
      rw [Set.mem_ofPred_eq, Set.mem_preimage, hh]
      have := (hact (n + 1)).2.2.1 k (ι u) (consTup X)
      rw [this, hkl, hcons, hv1]
    have hcont : Continuous (actW (Fv F v) σ J u : (Fin n → Fin M → Fv F v ⊗[F] E) → _) :=
      (hactJ n).1.comp (Continuous.prodMk continuous_const continuous_id)
    rw [hset, ← Measure.map_apply hcont.measurable hOpen.measurableSet,
      GlobalTheory.T.local_gram_fibration_disintegration F E σ hCM M J hJ (Fv F v) hLoc n μ ν m hμ hν hm u]
  · rw [Set.indicator_of_notMem he]
    have hempty : {X : Fin n → Fin M → Fv F v ⊗[F] E | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = ∅ := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hX => he (StageGood.first_mem b v σ _ h X hX)
    rw [hempty, measure_empty]

end GlobalTheory.CompanionTheory.SW.StageGoodFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittIsotropicToE0
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypWitt

theorem e0_linearIndependent (K : Type) [CommRing K] (M : ℕ) : LinearIndependent K (e0 K M) := by
  refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
  rw [Subsingleton.elim i 0]
  have h := congrFun hg 0
  simpa [e0] using h

theorem gramR_e0 {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    gramR R σ (hypOne J) (e0 (R ⊗[F] E) M) = 0 := by
  ext a b
  simp [gramR, hR, hform, JR, e0, Fin.sum_univ_succ, hypOne_zero_zero]

theorem witt_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, LinearIndependent (R ⊗[F] E) x → gramR R σ (hypOne J) x = 0 → ∃ g : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) = x := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hL x hx gx
  exact FreeTrans.transitive_free_isotropic F E σ hσ (M + 2) (hypOne J) (isHermND_hypOne σ hJ) R hL
    (e0 _ M) x (e0_linearIndependent _ M) hx (gramR_e0 R σ J) gx

end GlobalTheory.CompanionTheory.WeilSiegel.HypWitt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalOfNonIsomorphicStatement
section
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_of_non_isomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
  ∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ¬ IsoV V V' →
    ∀ φ ∈ V, ∀ ψ ∈ V', ∫ x in F, φ.1 x * (starRingEnd ℂ) (ψ.1 x) ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV | exact GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV | (intros; apply GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairRestrictionStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_restriction : GlobalTheory.CompanionTheory.EGlue.PairRestrict := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds | exact GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneFibreMeasureLocalStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_fibre_measure_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ 1)) (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree R σ J 1 μ ν m → ∀ X : Fin 1 → Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → gramR R σ J X = 0 → ∀ S : HermR R σ 1, m S ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos.fibre_ne_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos.fibre_ne_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos.fibre_ne_zero <;> assumption)
end

