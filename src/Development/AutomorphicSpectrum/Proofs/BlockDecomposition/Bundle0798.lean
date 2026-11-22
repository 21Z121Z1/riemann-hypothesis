import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0792
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentationUnitaryAverage
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0791
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0793
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSpaceCarriesFlat
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

section PairCarry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem FlatFn.fin_inv {N : ℕ} {e : GA E N → ℂ} (he : FlatFn e) (x : GA E N) {u : GL (Fin N) (Af E)}
    (hu : u ∈ KO E N) : e (x * finGL E N u) = e x := by
  have h := he.rinv x 1 u hu
  simpa [cf] using h

theorem FlatFn.inf_inv {N : ℕ} {e : GA E N → ℂ} (he : FlatFn e) (x : GA E N) (k : Kinf E N) :
    e (x * infGL E N (Unitary.toUnits k)) = e x := by
  have h := he.rinv x k 1 (one_mem _)
  simpa [cf] using h

theorem mul_mem_pairSpace (e₁ : GA E a → ℂ) (e₂ : GA E b → ℂ) (U₁ U₁' : Submodule ℂ (Sm E a))
    (U₂ U₂' : Submodule ℂ (Sm E b)) (F : H E a b → ℂ) (c₁ : Carries e₁ U₁ U₁') (c₂ : Carries e₂ U₂ U₂')
    (hF : F ∈ pairSpace U₁ U₂) : (fun x => e₁ x.1 * e₂ x.2 * F x) ∈ pairSpace U₁' U₂' := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hG
    obtain ⟨ψ₁, k₁, i₁⟩ := c₁ φ₁ h₁
    obtain ⟨ψ₂, k₂, i₂⟩ := c₂ φ₂ h₂
    refine Submodule.subset_span ⟨ψ₁, k₁, ψ₂, k₂, funext fun x => ?_⟩
    simp only [i₁, i₂]
    ring
  | zero =>
    have : (fun x : H E a b => e₁ x.1 * e₂ x.2 * (0 : H E a b → ℂ) x) = 0 := by
      funext x; simp
    rw [this]
    exact Submodule.zero_mem _
  | add G G' _ _ h h' =>
    have : (fun x : H E a b => e₁ x.1 * e₂ x.2 * (G + G') x) =
        (fun x => e₁ x.1 * e₂ x.2 * G x) + fun x => e₁ x.1 * e₂ x.2 * G' x := by
      funext x; simp only [Pi.add_apply]; ring
    rw [this]
    exact Submodule.add_mem _ h h'
  | smul c G _ h =>
    have : (fun x : H E a b => e₁ x.1 * e₂ x.2 * (c • G) x) = c • fun x => e₁ x.1 * e₂ x.2 * G x := by
      funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    exact Submodule.smul_mem _ c h

theorem pair_carry (e₁ : GA E a → ℂ) (e₂ : GA E b → ℂ) (U₁ U₁' : Submodule ℂ (Sm E a))
    (U₂ U₂' : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (F : H E a b → ℂ)
    (f₁ : FlatFn e₁) (f₂ : FlatFn e₂) (c₁ : Carries e₁ U₁ U₁') (c₂ : Carries e₂ U₂ U₂')
    (hF : F ∈ pairSpace U₁ U₂) (hT : TypeH K₁ K₂ W₁ W₂ F) :
    (fun x => e₁ x.1 * e₂ x.2 * F x) ∈
      (pairSpace U₁' U₂' ⊓ typeHF (K₁ ⊓ KO E a) (K₂ ⊓ KO E b) W₁ W₂ : Submodule ℂ (H E a b → ℂ)) := by
  refine Submodule.mem_inf.2 ⟨mul_mem_pairSpace e₁ e₂ U₁ U₁' U₂ U₂' F c₁ c₂ hF, ?_, fun x => ?_⟩
  · intro u₁ hu₁ u₂ hu₂ x
    have h₁ : e₁ (x * (finGL E a u₁, finGL E b u₂)).1 = e₁ x.1 := f₁.fin_inv x.1 hu₁.2
    have h₂ : e₂ (x * (finGL E a u₁, finGL E b u₂)).2 = e₂ x.2 := f₂.fin_inv x.2 hu₂.2
    show e₁ (x * (finGL E a u₁, finGL E b u₂)).1 * e₂ (x * (finGL E a u₁, finGL E b u₂)).2 *
      F (x * (finGL E a u₁, finGL E b u₂)) = e₁ x.1 * e₂ x.2 * F x
    rw [h₁, h₂, hT.1 u₁ hu₁.1 u₂ hu₂.1 x]
  · have h : (fun k : Kinf E a × Kinf E b =>
        (fun y : H E a b => e₁ y.1 * e₂ y.2 * F y)
          (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2)))) =
        (e₁ x.1 * e₂ x.2) • fun k : Kinf E a × Kinf E b =>
          F (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) := by
      funext k
      have h₁ : e₁ (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))).1 = e₁ x.1 :=
        f₁.inf_inv x.1 k.1
      have h₂ : e₂ (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))).2 = e₂ x.2 :=
        f₂.inf_inv x.2 k.2
      simp only [Pi.smul_apply, smul_eq_mul, h₁, h₂]
    rw [h]
    exact Submodule.smul_mem _ _ (hT.2 x)

end PairCarry

end GlobalTheory.CompanionTheory.LimV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientHeisenbergExpansionStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_coefficient_heisenberg_expansion : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (h : G D n), pc M m ψ b₀ F (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h) = ∫ x in m.𝓕, conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ)) * zc M m ψ b₀ F (M.nzx 0 x * h) ∂m.μ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.PcShear.pc_sh | exact GlobalTheory.CompanionTheory.FJE.PcShear.pc_sh | (intros; apply GlobalTheory.CompanionTheory.FJE.PcShear.pc_sh <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentationUnitaryAverageStatement
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representation_unitary_average : ∀ {K M H X : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure] [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ K M) (ι : M →ₗ[ℂ] H) (U U' : Submodule ℂ M) (ev : X → M →ₗ[ℂ] ℂ),
  (∀ k, ∀ x ∈ U', ∀ y ∈ U, ⟪ι (ρ k x), ι (ρ k y)⟫_ℂ = ⟪ι x, ι y⟫_ℂ) →
  (∀ k, ∀ x ∈ U', ∀ y ∈ U', ⟪ι (ρ k x), ι (ρ k y)⟫_ℂ = ⟪ι x, ι y⟫_ℂ) →
  (∀ x ∈ U, ∃ A : Submodule ℂ M, FiniteDimensional ℂ A ∧ x ∈ A ∧ A ≤ U ∧ (∀ k, ∀ a ∈ A, ρ k a ∈ A) ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (ρ k a)) →
  (∀ x ∈ U', ∃ A : Submodule ℂ M, FiniteDimensional ℂ A ∧ x ∈ A ∧ A ≤ U' ∧ (∀ k, ∀ a ∈ A, ρ k a ∈ A) ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (ρ k a)) →
  (∀ W : Submodule ℂ (K → ℂ), FiniteDimensional ℂ W → FiniteDimensional ℂ (Submodule.span ℂ {x | x ∈ U' ∧ ∀ t, (fun k => ev t (ρ k x)) ∈ W})) →
  ∀ x ∈ U, ∃ y ∈ U', ∀ z ∈ U', ⟪ι z, ι x⟫_ℂ = ⟪ι z, ι y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscRepr.representing_vector | exact GlobalTheory.CompanionTheory.FinDiscRepr.representing_vector | (intros; apply GlobalTheory.CompanionTheory.FinDiscRepr.representing_vector <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateIsometryStatement
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_translate_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : GA E N) (x y : Sm E N), x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → rt E N g x ∈ squareIntegrableSmoothSubmoduleGL μ ∧ ⟪l2Map μ (rt E N g x), l2Map μ (rt E N g y)⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.rt_mem_l2Sub_and_inner_eq | exact GlobalTheory.CompanionTheory.FinDiscOrth.rt_mem_l2Sub_and_inner_eq | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.rt_mem_l2Sub_and_inner_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOfLocalIdentities
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt

open GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale

theorem exists_scale_cover {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fin n → Fin M → Fv F v ⊗[F] E)) (hC : IsCompact C) :
    ∃ (c : F) (hc : c ≠ 0), C ⊆ latV (scaleB b c hc) v := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set p : Fv F v := algebraMap F (Fv F v) π with hp
  have hval : Valued.v p = WithZero.exp (-1 : ℤ) := by
    have h0 : Valued.v (algebraMap F (Fv F v) π) = v.valuation F π :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π
    rw [hp, h0, hπ]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hlt : Valued.v p < 1 := by
    rw [hval]
    decide
  have hpO : p ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hlt.le
  have hnorm : ‖p‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 hlt
  have hlim : Filter.Tendsto (fun k : ℕ => p ^ k) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have hOopen : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  have hmem : ∀ (k : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E),
      X ∈ latV (scaleB b (π ^ k) (pow_ne_zero k hπ0)) v ↔
        ∀ a i l, p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          v.adicCompletionIntegers F := by
    intro k X
    simp only [latV, Set.mem_setOf_eq, repr_scaleB, map_pow, hp]
  let U : ℕ → Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun k => latV (scaleB b (π ^ k) (pow_ne_zero k hπ0)) v
  have hUo : ∀ k, IsOpen (U k) := fun k =>
    (((GlobalTheory.T.adelic_tuple_projections F E σ hcm d (scaleB b (π ^ k) (pow_ne_zero k hπ0)) n M).2.2.2.1 v).2)
  have hcov : C ⊆ ⋃ k, U k := by
    intro X _
    have h1 : ∀ a i l, ∀ᶠ k : ℕ in Filter.atTop,
        p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          (v.adicCompletionIntegers F : Set (Fv F v)) := by
      intro a i l
      have h2 : Filter.Tendsto
          (fun k : ℕ => p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l)
          Filter.atTop (𝓝 0) := by
        simpa using hlim.mul_const ((Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l)
      exact h2 (hOopen.mem_nhds (zero_mem _))
    have h3 : ∀ᶠ k : ℕ in Filter.atTop, ∀ a i l,
        p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          (v.adicCompletionIntegers F : Set (Fv F v)) :=
      Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i =>
        Filter.eventually_all.2 fun l => h1 a i l
    obtain ⟨k, hk⟩ := h3.exists
    exact Set.mem_iUnion.2 ⟨k, (hmem k X).2 hk⟩
  have hmono : Monotone U := monotone_nat_of_le_succ fun k X hX => by
    refine (hmem (k + 1) X).2 fun a i l => ?_
    have h := (hmem k X).1 hX a i l
    rw [pow_succ', mul_assoc]
    exact mul_mem hpO h
  obtain ⟨k, hk⟩ := hC.elim_directed_cover U hUo hcov hmono.directed_le
  exact ⟨π ^ k, pow_ne_zero k hπ0, hk⟩

theorem fibre_compact_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), SWFree σ J T hT → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (m : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) m → ∀ C : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact C → m (hermOf (Fv F v) σ T hT) C < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ n T hT hSW d b laminf lam hinf hv v m hm C hC
  classical
  obtain ⟨c, hc, hCc⟩ := exists_scale_cover σ hcm b n M v C hC
  set b' := scaleB b c hc with hb'
  have hrV : ∀ w, IsLocR (Fv F w) := GlobalTheory.T.completion_is_local_ring F
  haveI : ∀ w, BorelSpace (Fv F w) := fun _ => ⟨rfl⟩
  obtain ⟨k, hk0, hk⟩ := coord_rescale σ hcm J (Fv F v) (hrV v) b b' (lam v) (hv v).1 n m hm
  have hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hWi, hHi⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Ainf F) _ b' laminf hinf.1
  obtain ⟨minf, hminf⟩ := GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap F E σ hcm M n J hJ (coordW (Ainf F) b' laminf n M)
    (coordHerm (Ainf F) σ b' laminf n) (hWi n M) (hHi n)
  have hfV : ∀ w : HeightOneSpectrum (𝓞 F), ∃ fib : HermR (Fv F w) σ n → Measure (Fin n → Fin M → Fv F w ⊗[F] E),
      IsGramFibFree (Fv F w) σ J n (coordW (Fv F w) b' (lam w) n M) (coordHerm (Fv F w) σ b' (lam w) n) fib := fun w => by
    have := PI.VolStabS.secondCountable_Fv F w
    have := PI.VolStabS.locallyCompact_Fv F w
    obtain ⟨-, hWv, hHv⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F w) _ b' (lam w) (hv w).1
    exact PI.OmFibreUniq.W.gram_map_fibre_existence σ J w n hcm hJ _ _ (hWv n M) (hHv n)
  choose m₀ hm₀ using hfV
  let m₂ : ∀ w : HeightOneSpectrum (𝓞 F), HermR (Fv F w) σ n → Measure (Fin n → Fin M → Fv F w ⊗[F] E) :=
    Function.update m₀ v (fun S => k • m S)
  have hm₂v : m₂ v = fun S => k • m S := Function.update_self _ _ _
  have hm₂ : ∀ w, IsGramFibFree (Fv F w) σ J n (coordW (Fv F w) b' (lam w) n M)
      (coordHerm (Fv F w) σ b' (lam w) n) (m₂ w) := fun w => by
    by_cases h : w = v
    · subst h
      rw [hm₂v]
      exact hk
    · have : m₂ w = m₀ w := Function.update_of_ne h _ _
      rw [this]
      exact hm₀ w
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁
  have hE := hSW d b' laminf lam hinf hv μ₁ 𝓕₁ hμ₁ h𝓕₁ minf m₂ hminf hm₂
  have h1 : (k • m (hermOf (Fv F v) σ T hT)) (latV b' v) < ⊤ := by
    have h2 : m₂ v (hermOf (Fv F v) σ T hT) (latV b' v) < ⊤ := hE.1 v
    rwa [hm₂v] at h2
  have h3 : m (hermOf (Fv F v) σ T hT) (latV b' v) < ⊤ := by
    by_contra hx
    have hs : (k • m (hermOf (Fv F v) σ T hT)) (latV b' v) =
        (k : ℝ≥0∞) * m (hermOf (Fv F v) σ T hT) (latV b' v) := by
      rw [Measure.smul_apply]
      rfl
    rw [hs, not_lt_top_iff.1 hx, ENNReal.mul_top (by exact_mod_cast hk0)] at h1
    exact lt_irrefl _ h1
  exact (measure_mono hCc).trans_lt h3

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoAbsoluteCharacterOne
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem absFn_tendsto_one : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (x : GA E N) (w : ℕ → ℂ), Tendsto w atTop (𝓝 0) → Tendsto (fun k => absFn N (w k) x) atTop (𝓝 1) := by
  intro E _ _ _ N x w hw
  have hL : ∀ t : ℂ, absFn N t x =
      Complex.exp (t * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ)) := by
    intro t
    exact GlobalTheory.Mem.Chr.CharModel.absHom_val E t (GeneralLinearGroup.det x)
  have h0 : Tendsto (fun k => Complex.exp (w k *
      (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ))) atTop
      (𝓝 (Complex.exp (0 * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ)))) :=
    (Complex.continuous_exp.tendsto _).comp (hw.mul_const _)
  simpa [hL] using h0

end GlobalTheory.CompanionTheory.LimV
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusElementLeviEmbedding
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.LevAt

theorem aT_eq_lev (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (t : ℝ) :
    aT E (r + s) r t = GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s (aT E r r t, 1) := by
  apply Units.ext
  rw [PositivityTheory.Rg.Rs.JFinTr.aT_val, GlobalTheory.SmGL.val_emb₂]
  ext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr, PositivityTheory.Rg.Rs.JFinTr.aT_val, Matrix.diagonal_apply]
  have h1 : (fun _ : InfinitePlace E => (1 : ℂ)) = (1 : Cinf E) := rfl
  rw [h1, sub_add_cancel, Matrix.one_apply]

end GlobalTheory.CompanionTheory.Conc.LevAt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedFirstBlockRestriction
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.SliceL

theorem slice_typeF {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)) :
    IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W →
    ∃ (K₁ : Subgroup (GL (Fin r) (Af E))) (W₁ : Submodule ℂ (Kinf E r → ℂ)),
      IsOpen (K₁ : Set (GL (Fin r) (Af E))) ∧ FiniteDimensional ℂ W₁ ∧
      ∀ f ∈ typeF K W, ∀ y : GA E s,
        (fun x : GA E r => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₁ W₁ := by
  intro hK hW
  have hcf : cf (r + s) k t = finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) := by
    rw [cf, infGL_comm]
  refine ⟨Slice1.levelOne s K t,
    W.map (LinearMap.funLeft ℂ ℂ fun κ : Kinf E r => Slice1.levK E r s κ * k),
    Slice1.isOpen_levelOne hK t, inferInstance, ?_⟩
  intro f hf y
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have h := Slice1.lev_finGL_right g u y t (Unitary.toUnits k)
    have h' := hf.1 _ (Slice1.mem_levelOne.1 hu)
      (lev (Ad E) r s (g, y) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))
    rw [← h] at h'
    simpa only [hcf, mul_assoc] using h'
  · refine ⟨_, hf.2 (lev (Ad E) r s (g, y) * finGL E (r + s) t), ?_⟩
    funext κ
    have h := Slice1.lev_infGL_right g (Unitary.toUnits κ) y t (Unitary.toUnits k)
    have e : lev (Cinf E) r s (Unitary.toUnits κ, 1) * Unitary.toUnits k =
        Unitary.toUnits (Slice1.levK E r s κ * k) := by
      rw [map_mul, Slice1.toUnits_levK]
    rw [e] at h
    simp only [LinearMap.funLeft_apply, hcf]
    rw [← h]
    simp only [mul_assoc]

end GlobalTheory.CompanionTheory.LimV.SliceL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSecondBlockRestriction
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.SliceR

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

def levelTwo (K : Subgroup (GL (Fin (r + s)) (Af E))) (t : GL (Fin (r + s)) (Af E)) :
    Subgroup (GL (Fin s) (Af E)) :=
  K.comap ((MulAut.conj t⁻¹).toMonoidHom.comp (Slice2.lev2 (Af E) r s))

theorem mem_levelTwo {K : Subgroup (GL (Fin (r + s)) (Af E))} {t : GL (Fin (r + s)) (Af E)}
    {u : GL (Fin s) (Af E)} : u ∈ levelTwo K t ↔ t⁻¹ * lev (Af E) r s (1, u) * t ∈ K := by
  simp [levelTwo, MulAut.conj_apply, Slice2.lev2]

theorem isOpen_levelTwo {K : Subgroup (GL (Fin (r + s)) (Af E))}
    (hK : IsOpen (K : Set (GL (Fin (r + s)) (Af E)))) (t : GL (Fin (r + s)) (Af E)) :
    IsOpen (levelTwo K t : Set (GL (Fin s) (Af E))) := by
  have hc : Continuous fun u : GL (Fin s) (Af E) => t⁻¹ * Slice2.lev2 (Af E) r s u * t :=
    (continuous_const.mul Slice2.continuous_lev2).mul continuous_const
  convert hK.preimage hc using 1
  ext u
  exact mem_levelTwo

def sliceMap (k : Kinf E (r + s)) : (Kinf E (r + s) → ℂ) →ₗ[ℂ] (Kinf E s → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun κ => Slice2.levK E r s κ * k

theorem lev_finGL_right (x : GA E r) (g : GA E s) (u : GL (Fin s) (Af E)) (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) :
    lev (Ad E) r s (x, g * finGL E s u) * cf (r + s) k t =
      lev (Ad E) r s (x, g) * cf (r + s) k t * finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
  have hY : finGL E (r + s) (lev (Af E) r s (1, u)) * finGL E (r + s) t =
      finGL E (r + s) t * finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [Slice2.lev_mul_right, Slice2.lev_finGL_one, cf, mul_assoc (lev (Ad E) r s (x, g)),
    ← mul_assoc (finGL E (r + s) _), ← infGL_comm, mul_assoc (infGL E (r + s) _), hY]
  simp only [mul_assoc]

theorem lev_infGL_right (x : GA E r) (g : GA E s) (κ : Kinf E s) (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) :
    lev (Ad E) r s (x, g * infGL E s (Unitary.toUnits κ)) * cf (r + s) k t =
      (lev (Ad E) r s (x, g) * finGL E (r + s) t) *
        infGL E (r + s) (Unitary.toUnits (Slice2.levK E r s κ * k)) := by
  rw [Slice2.lev_mul_right, Slice2.lev_infGL_one, cf, map_mul Unitary.toUnits, Slice2.toUnits_levK,
    map_mul (infGL E (r + s)), mul_assoc (lev (Ad E) r s (x, g)) (finGL E (r + s) t), infGL_comm _ t]
  rw [mul_assoc (lev (Ad E) r s (x, g)) (infGL E (r + s) _), ← mul_assoc (infGL E (r + s) _) (finGL E (r + s) t),
    infGL_comm]
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.LimV.SliceR

theorem GlobalTheory.CompanionTheory.LimV.SliceR.slice_right : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → ∃ (K₂ : Subgroup (GL (Fin s) (Af E))) (W₂ : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K₂ : Set (GL (Fin s) (Af E))) ∧ FiniteDimensional ℂ W₂ ∧ ∀ f ∈ typeF K W, ∀ x : GA E r, (fun y : GA E s => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₂ W₂ := by
  intro E _ _ _ r s k t K W hK hW
  refine ⟨SliceR.levelTwo K t, W.map (SliceR.sliceMap k), SliceR.isOpen_levelTwo hK t, inferInstance,
    fun f hf x => ⟨fun u hu g => ?_, fun g => ?_⟩⟩
  · change f (lev (Ad E) r s (x, g * finGL E s u) * cf (r + s) k t) = f (lev (Ad E) r s (x, g) * cf (r + s) k t)
    rw [SliceR.lev_finGL_right]
    exact hf.1 _ (SliceR.mem_levelTwo.1 hu) _
  · refine ⟨_, hf.2 (lev (Ad E) r s (x, g) * finGL E (r + s) t), ?_⟩
    funext κ
    change f _ = f (lev (Ad E) r s (x, g * infGL E s (Unitary.toUnits κ)) * cf (r + s) k t)
    rw [SliceR.lev_infGL_right]

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingRankOneVolumeStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_scaling_rank_one_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' S) = ((‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ : ℝ≥0∞)) ^ M * coordW (Fv F v) b lam 1 M S := by
  first | exact @GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul | exact GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul | (intros; apply GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaCompactStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_adelic_iwasawa_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), K ≤ finPts σ J ∧ IsCompact (K : Set (GAd σ J)) ∧ (∀ g ∈ finPts σ J, ∃ p ∈ minPar σ J X, p ∈ finPts σ J ∧ ∃ k ∈ K, g = p * k) ∧ GoodPosition σ J X Y K := by
  first | exact @GlobalTheory.CompanionTheory.KFin.exists_compact_iwasawa_good | exact GlobalTheory.CompanionTheory.KFin.exists_compact_iwasawa_good | (intros; apply GlobalTheory.CompanionTheory.KFin.exists_compact_iwasawa_good <;> assumption)
end

