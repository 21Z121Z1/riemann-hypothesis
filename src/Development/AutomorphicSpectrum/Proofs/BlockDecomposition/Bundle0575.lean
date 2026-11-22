import Mathlib
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0066
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityUnitLattice
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBoundedAlmostAll
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0074
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0545
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SummableUnitBounds.SBoundOf

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTrace
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.ClozelLie

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem Eop_add_conjugate (τ : E →+* ℂ) (i : Fin a) :
    Eop τ i i + Eop (ComplexEmbedding.conjugate τ) i i = lieS E a i i (atEmb τ 1) := by
  have e1 : atEmb (ComplexEmbedding.conjugate τ) 1 = atEmb τ 1 := by rw [atEmb_conj, map_one]
  have e2 : atEmb (ComplexEmbedding.conjugate τ) Complex.I = -atEmb τ Complex.I := by
    rw [atEmb_conj, Complex.conj_I, atEmb_eq, atEmb_eq τ Complex.I]
    simp
  simp only [Eop, e1, e2, map_neg]
  module

theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (1 + 1 : Cinf E) := by
  classical
  have e : ∀ τ : E →+* ℂ, atEmb τ 1 = Pi.single (InfinitePlace.mk τ) (1 : ℂ) := fun τ => by
    unfold atEmb
    split_ifs <;> simp
  funext w
  simp only [e, Finset.sum_apply, Pi.single_apply, Pi.add_apply, Pi.one_apply]
  simp only [eq_comm (a := w)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    IsTotallyComplex.mult_eq]
  norm_num

theorem sum_Eop_diag (i : Fin a) : ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 := by
  have hs : ∑ τ : E →+* ℂ, Eop (ComplexEmbedding.conjugate τ) i i = ∑ τ : E →+* ℂ, Eop τ i i :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (fun τ : E →+* ℂ => star_star τ))
      (fun τ => Eop τ i i)
  have h : (∑ τ : E →+* ℂ, Eop τ i i) + ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 + lieS E a i i 1 := by
    nth_rw 2 [← hs]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => Eop_add_conjugate τ i, ← map_sum,
      sum_atEmb_one, map_add]
  have h2 : (2 : ℂ) • (∑ τ : E →+* ℂ, Eop τ i i) = (2 : ℂ) • lieS E a i i 1 := by
    rw [two_smul, two_smul, h]
  exact smul_right_injective _ (two_ne_zero (α := ℂ)) h2

theorem lie_oneL_eq_sum_Eop (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop_diag i]
  simp only [lieS_apply]
  rw [← map_sum]
  have hm : ∑ i : Fin a, Matrix.single i i (1 : Cinf E) = 1 := by
    refine Matrix.ext fun p q => ?_
    rw [Matrix.sum_apply, Matrix.one_apply]
    by_cases h : p = q
    · subst h
      simp [Matrix.single_apply]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact h rfl
  congr 1
  exact (congrArg Matrix.of.symm hm).symm

end GlobalTheory.CompanionTheory.ClozelLie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointL2
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.LieSkew

theorem continuous_infGL_map (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  refine Continuous.units_map _ ?_
  exact continuous_const.add (continuous_id.matrix_map hs)

theorem inner_R_R {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (g : G) (F F' : L2 Γ μ) :
    inner ℂ (R Γ μ g F) (R Γ μ g F') = inner ℂ F F' :=
  (LinearIsometry.mk (R Γ μ g).toLinearMap (norm_R g)).inner_map_map F F'

theorem lie_skew : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.CuspRep.Lie E a) (φ ψ : Sm E a) (hφ : MemL2Quotient (latticeGL E a) μ φ.1) (hψ : MemL2Quotient (latticeGL E a) μ ψ.1) (hXφ : MemL2Quotient (latticeGL E a) μ (lie E a X φ).1) (hXψ : MemL2Quotient (latticeGL E a) μ (lie E a X ψ).1), Continuous φ.1 → Continuous ψ.1 → Continuous (lie E a X φ).1 → Continuous (lie E a X ψ).1 → inner ℂ hXφ.toL2 hψ.toL2 = - inner ℂ hφ.toL2 hXψ.toL2 := by
  intro E _ _ _ a μ _ _ X φ ψ hφ hψ hXφ hXψ cφ cψ cXφ cXψ
  obtain ⟨c, hc, h0, hadd, hd, -⟩ := GlobalTheory.T.one_parameter_subgroup_exists E a X
  have hγ : Continuous fun t => infGL E a (c t) := (continuous_infGL_map E a).comp hc
  have hγ0 : infGL E a (c 0) = 1 := by rw [h0, map_one]
  have hγa : ∀ s t, infGL E a (c (s + t)) = infGL E a (c s) * infGL E a (c t) := fun s t => by
    rw [hadd, map_mul]
  have d1 := GlobalTheory.T.hasDerivAt_right_translate_toL2 (GA E a) (latticeGL E a) μ φ.1 (lie E a X φ).1 hφ hXφ
    (fun t => infGL E a (c t)) cφ cXφ hγ hγ0 hγa (fun g => hasDerivAt_curve φ g c X h0 hd) 0
  have d2 := GlobalTheory.T.hasDerivAt_right_translate_toL2 (GA E a) (latticeGL E a) μ ψ.1 (lie E a X ψ).1 hψ hXψ
    (fun t => infGL E a (c t)) cψ cXψ hγ hγ0 hγa (fun g => hasDerivAt_curve ψ g c X h0 hd) 0
  have d3 := d1.inner ℂ d2
  have hconst : (fun t : ℝ => inner ℂ (R (latticeGL E a) μ (infGL E a (c t)) hφ.toL2)
      (R (latticeGL E a) μ (infGL E a (c t)) hψ.toL2)) = fun _ => inner ℂ hφ.toL2 hψ.toL2 :=
    funext fun t => inner_R_R _ μ _ _ _
  rw [hconst] at d3
  have h := d3.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [hγ0, map_one, ContinuousLinearMap.one_apply] at h
  exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h)

end GlobalTheory.CompanionTheory.LieSkew
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCompactCoverByUnitScalings
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.SphereCover

section Abstract

variable {K : Type} [NormedField K] [IsUltrametricDist K] [ProperSpace K]

theorem exists_sphere {T : Type} [AddCommGroup T] [Module K T] [Module.Finite K T]
    [TopologicalSpace T] [IsModuleTopology K T] (π : K) (h0 : π ≠ 0) (h1 : ‖π‖ < 1)
    (hv : ∀ a : K, a ≠ 0 → ∃ j : ℤ, ‖a‖ = ‖π‖ ^ j) (A : Set T) (hA : IsCompact A) :
    ∃ (P : Set T) (k : ℕ), IsCompact P ∧ IsOpen P ∧ (0 : T) ∉ P ∧
      ∀ X ∈ A, X ≠ 0 → ∃ (i : ℕ), ∃ Y ∈ P, X = (π ^ ((i : ℤ) - k)) • Y := by
  haveI : ContinuousAdd T := IsModuleTopology.toContinuousAdd K T
  haveI : ContinuousSMul K T := IsModuleTopology.toContinuousSMul K T
  let c : T ≃ₗ[K] (Fin (Module.finrank K T) → K) := (Module.finBasis K T).equivFun
  have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
  have hc' : Continuous c.symm := IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap
  obtain ⟨C, hC⟩ : ∃ C, ∀ X ∈ A, ‖c X‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hA.image hc).isBounded.exists_norm_le
    exact ⟨C, fun X hX => hC _ ⟨X, hX, rfl⟩⟩
  have hπ : 0 < ‖π‖ := norm_pos_iff.2 h0
  obtain ⟨k, hk⟩ : ∃ k : ℕ, C < (‖π‖⁻¹) ^ k :=
    pow_unbounded_of_one_lt C ((one_lt_inv₀ hπ).2 h1)
  have himg : c.symm '' Metric.sphere 0 1 = c ⁻¹' Metric.sphere 0 1 := by
    ext X
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hX
      exact ⟨c X, hX, by simp⟩
  refine ⟨c.symm '' Metric.sphere 0 1, k, (isCompact_sphere _ _).image hc', ?_, ?_, ?_⟩
  · rw [himg]
    exact (IsUltrametricDist.isClopen_sphere 0 one_ne_zero).isOpen.preimage hc
  · rw [himg]
    simp
  · intro X hX hX0
    have hw : c X ≠ 0 := by simpa using hX0
    obtain ⟨l, hl⟩ : ∃ l, c X l ≠ 0 := Function.ne_iff.1 hw
    haveI : Nonempty (Fin (Module.finrank K T)) := ⟨l⟩
    obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup (Finset.univ) Finset.univ_nonempty
      (fun i => ‖c X i‖₊)
    have hnorm : ‖c X‖ = ‖c X m‖ := by
      rw [← coe_nnnorm, Pi.nnnorm_def, hm, coe_nnnorm]
    have hm0 : c X m ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      exact hw (norm_eq_zero.1 hnorm)
    obtain ⟨j, hj⟩ := hv _ hm0
    rw [← hnorm] at hj
    have hjk : -(k : ℤ) ≤ j := by
      have : ‖π‖ ^ j ≤ ‖π‖ ^ (-(k : ℤ)) := by
        rw [← hj, zpow_neg, zpow_natCast, ← inv_pow]
        exact ((hC X hX).trans hk.le)
      exact (zpow_le_zpow_iff_right_of_lt_one₀ hπ h1).1 this
    have hY : ‖c ((π ^ (-j)) • X)‖ = 1 := by
      rw [map_smul, norm_smul, norm_zpow, hj, ← zpow_add₀ hπ.ne']
      simp
    refine ⟨(j + k).toNat, (π ^ (-j)) • X, ?_, ?_⟩
    · rw [himg]
      simpa using hY
    · have : (((j + k).toNat : ℕ) : ℤ) - k = j := by
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      rw [this, smul_smul, ← zpow_add₀ h0]
      simp

end Abstract

section Cover

variable {K R : Type} [NormedField K] [IsUltrametricDist K] [ProperSpace K] [CommRing R]
  [Algebra K R] [Module.Finite K R] [TopologicalSpace R] [IsModuleTopology K R]

theorem linearIndependent_of_ne_zero (hR : IsField R) {M : ℕ} {X : Fin 1 → Fin M → R}
    (hX : X ≠ 0) : LinearIndependent R X := by
  haveI : IsDomain R := hR.isDomain
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h0 : X 0 ≠ 0 := fun h => hX (funext fun p => by
    obtain rfl : p = 0 := Subsingleton.elim _ _
    exact h)
  obtain ⟨l, hl⟩ : ∃ l, X 0 l ≠ 0 := Function.ne_iff.1 h0
  have h1 := congrFun hg l
  simp only [Fin.sum_univ_one, Fin.isValue, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_right hl

theorem exists_cover (hR : IsField R) (π : K) (h0 : π ≠ 0) (h1 : ‖π‖ < 1)
    (hv : ∀ a : K, a ≠ 0 → ∃ j : ℤ, ‖a‖ = ‖π‖ ^ j) {M : ℕ} (hM : 2 ≤ M)
    (A : Set (Fin 1 → Fin M → R)) (hA : IsCompact A) :
    ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → R)) (u : ι → Rˣ),
      IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → R | LinearIndependent R X} ∧
      Summable (fun i => ‖Algebra.norm K (u i : R)‖₊ ^ (M - 1)) ∧
      A ∩ {X : Fin 1 → Fin M → R | LinearIndependent R X} ⊆
        ⋃ i, (fun (X : Fin 1 → Fin M → R) (p : Fin 1) (k : Fin M) => (u i : R) * X p k) '' P := by
  haveI : Nontrivial R := ⟨hR.exists_pair_ne⟩
  obtain ⟨P, k, hPc, hPo, hP0, hcov⟩ := exists_sphere π h0 h1 hv A hA
  let w : Kˣ := Units.mk0 π h0
  let u : ℕ → Rˣ := fun i => Units.map (algebraMap K R).toMonoidHom (w ^ ((i : ℤ) - k))
  have hu : ∀ i : ℕ, (u i : R) = algebraMap K R (π ^ ((i : ℤ) - k)) := fun i => by
    change algebraMap K R ((w ^ ((i : ℤ) - k) : Kˣ) : K) = _
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  refine ⟨ℕ, inferInstance, P, u, hPc, hPo, ?_, ?_, ?_⟩
  · intro X hX
    exact linearIndependent_of_ne_zero hR fun h => hP0 (h ▸ hX)
  · have hd : 0 < Module.finrank K R := Module.finrank_pos
    have hπ : 0 < ‖π‖₊ := nnnorm_pos.2 h0
    have hlt : ‖π‖₊ < 1 := by exact_mod_cast h1
    set e : ℕ := Module.finrank K R * (M - 1) with he
    have he0 : e ≠ 0 := Nat.mul_ne_zero hd.ne' (by omega)
    have hq : ‖π‖₊ ^ e < 1 := pow_lt_one₀ hπ.le hlt he0
    have hs := (NNReal.summable_geometric hq).mul_left ((‖π‖₊ ^ (-(k : ℤ))) ^ e)
    refine hs.congr fun i => ?_
    rw [hu, Algebra.norm_algebraMap, nnnorm_pow, nnnorm_zpow, sub_eq_add_neg,
      zpow_add₀ hπ.ne', zpow_natCast, he]
    ring
  · rintro X ⟨hXA, hXf⟩
    have hX0 : X ≠ 0 := by
      intro h
      have h2 : LinearIndependent R X := hXf
      exact h2.ne_zero 0 (by rw [h]; rfl)
    obtain ⟨i, Y, hY, hXY⟩ := hcov X hXA hX0
    refine Set.mem_iUnion.2 ⟨i, Y, hY, ?_⟩
    rw [hXY]
    funext p l
    simp [hu, Algebra.smul_def]

end Cover

theorem exists_uniformizer {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ a : Fv F v, a ≠ 0 → ∃ j : ℤ, ‖a‖ = ‖π‖ ^ j := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  let ϖ : Fv F v := (π : Fv F v)
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have h1 : Valued.v ϖ < 1 := by
    rw [hϖ]
    decide
  refine ⟨ϖ, hϖ0, Valued.toNormedField.norm_lt_one_iff.2 h1, fun a ha => ?_⟩
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  set k : ℤ := WithZero.log (Valued.v a) with hk
  have hu : Valued.v (a * ϖ ^ k) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      ← hk, ← WithZero.exp_zero]
    congr 1
    simp
  have hn : ‖a * ϖ ^ k‖ = 1 := le_antisymm (Valued.toNormedField.norm_le_one_iff.2 hu.le)
    (not_lt.1 fun h => (Valued.toNormedField.norm_lt_one_iff.1 h).ne hu)
  have hϖn : ‖ϖ‖ ≠ 0 := norm_ne_zero_iff.2 hϖ0
  refine ⟨-k, ?_⟩
  rw [norm_mul, norm_zpow] at hn
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left hn

theorem coverF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 2 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)), IsField (Fv F v ⊗[F] E) → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ), IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧ A ∩ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u i : Fv F v ⊗[F] E) * X p k) '' P := by
  intro F E _ _ _ _ _ σ h M hM v hF A hA
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  haveI : ProperSpace (Fv F v) := GlobalTheory.CompanionTheory.DictLoc.properSpace_Fv v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨π, h0, h1, hv⟩ := exists_uniformizer v
  exact exists_cover hF π h0 h1 hv hM A hA

end GlobalTheory.CompanionTheory.WeilSiegel.SphereCover
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensitiesHermitianRepresentation
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodMassLt

open GlobalTheory.CompanionTheory.SW.GoodMass

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem key (hcm : IsCMExt F E σ) : ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    n < M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ,
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m,
      IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m →
      |(m (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| ≤
        C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro M J hJ _ T hT _ d b
    refine ⟨0, Filter.Eventually.of_forall ?_⟩
    intro v lam hl m hm
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have h0 := GlobalTheory.T.rank_zero_gram_fiber_measure F E σ hcm M J hJ (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) d b lam hl.1 m hm
      (hermOf (Fv F v) σ T hT)
    have hU : (latV b v : Set (Fin 0 → Fin M → Fv F v ⊗[F] E)) = Set.univ := by
      ext Y
      simp [latV]
    rw [h0, hU, measure_univ]
    simp
  | succ n ih =>
    intro M J hJ hn T hT hdet d b
    obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 1 := ⟨M - 1, by omega⟩
    obtain ⟨x, t, ht, hx⟩ := exists_aniso hcm T hT hdet
    obtain ⟨g, T₁, hT₁, hblock, -⟩ :=
      AlgSplit.split_anisotropic F E σ hcm n T ⟨hT, hdet⟩ t x ht hx
    have hbh : ∀ a b, σ (blockOne (algebraMap F E t) T₁ b a) = blockOne (algebraMap F E t) T₁ a b :=
      blockOne_herm _ (σ.commutes t) _ hT₁.1
    have hgdet : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) E).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    have hone : IsHermND σ (1 : Matrix (Fin M₁) (Fin M₁) E) := one_hermND M₁
    have hJ' : IsHermND σ (blockOne (algebraMap F E t) (1 : Matrix (Fin M₁) (Fin M₁) E)) :=
      blockOne_hermND t ht
    obtain ⟨C₁, hC₁⟩ := ih M₁ 1 hone (by omega) T₁ hT₁.1 hT₁.2 d b
    refine ⟨3 * |C₁| + 2, ?_⟩
    have e1 := GlobalTheory.T.local_densities_congruent_target_almost_all F E σ hcm (M₁ + 1) J hJ (n + 1) T hT hdet g hgdet _ hbh hblock d b
    have e2 := GlobalTheory.T.local_gram_fiber_measures_agree_almost_all F E σ hcm (M₁ + 1) J hJ _ hJ' d b (n + 1)
    have e3 := GlobalTheory.T.local_densities_block_one_almost_all F E σ hcm M₁ 1 hone t ht n T₁ hT₁.1 hT₁.2 hbh d b
    have e4 := GlobalTheory.CompanionTheory.SW.UnitVal.density_unit_lattice F E σ hcm (M₁ + 1) _ hJ' (by omega) d b
    have e5 := (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 t ht
    filter_upwards [e1, e2, e3, e4, e5, hC₁] with v h1 h2 h3 h4 h5 h6 lam hl m hm
    obtain ⟨m', hm'⟩ := exists_family hcm hJ' b v lam hl (n + 1)
    obtain ⟨m₁, hm₁⟩ := exists_family hcm hJ' b v lam hl 1
    obtain ⟨m₂, hm₂⟩ := exists_family hcm hone b v lam hl n
    have a1 := h1 lam hl m hm
    have a2 := h2 lam hl m m' hm hm' (hermOf (Fv F v) σ _ hbh)
    have a3 := h3 lam hl m' m₁ m₂ hm' hm₁ hm₂
    have a4 := h4 lam hl m₁ hm₁ _ h5
    have a6 := h6 lam hl m₂ hm₂
    have hq1 := absNorm_one_le (F := F) v
    have a4' : |(m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)) (latV b v)).toReal - 1| ≤
        2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M₁ + 1) :=
      a4.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))
    rw [← a1, a2, a3, ENNReal.toReal_mul]
    exact arith hq1 (by omega) a4' a6

end Main

end GlobalTheory.CompanionTheory.SW.GoodMassLt

namespace GlobalTheory.CompanionTheory.SW

end GlobalTheory.CompanionTheory.SW
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDependentSetNull
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree

theorem linearIndependent_of_isUnit_qR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (R : Type) [Field R] [Algebra F R] (X : Fin 1 → Fin M → R ⊗[F] E)
    (hu : IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0))) : LinearIndependent (R ⊗[F] E) X := by
  classical
  have hfix : HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (X 0)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (X 0) :=
    GlobalTheory.CompanionTheory.SW.FibreRatio.sigR_hR_self R hσ hJ (X 0)
  obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.SW.FibreRatio.fixed_tmul R hσ _ hfix
  have hq : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) = r := by
    unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR
    rw [hr]
    exact GlobalTheory.CompanionTheory.SW.FibreRatio.half_trace_tmul R hσ r
  have hr0 : r ≠ 0 := by
    rw [← hq]
    exact hu.ne_zero
  have hunit : IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (X 0)) := by
    rw [hr]
    exact GlobalTheory.CompanionTheory.SW.FibreRatio.isUnit_tmul R hr0
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  set a := g 0 with ha_def
  have ha' : a • X 0 = 0 := by simpa [Fin.sum_univ_one] using hg
  have hlin : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (a • X 0) =
      a * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (X 0) := by
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hzero : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (0 : Fin M → R ⊗[F] E) = 0 := by
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.UG.hform, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  rw [ha', hzero] at hlin
  exact (hunit.mul_left_eq_zero).1 hlin.symm

theorem null_nonfree : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → coordW (Fv F v) b lam 1 M {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}ᶜ = 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b v lam hlam
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hh := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lam hlam.1
  have h0 := (NullV.null_nonunits F E σ hσ M J hJ hM v (coordW (Fv F v) b lam 1 M) lam (hh.2.1 1 M) hlam.1).2
  refine measure_mono_null ?_ h0
  intro X hX hu
  exact hX (linearIndependent_of_isUnit_qR hσ hJ (Fv F v) X hu)

end GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureUnramifiedStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_gram_fibre_measure_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ c : HermR (Fv F v) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det → ∀ A : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : HermR (Fv F v) σ n) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets → (∀ k, MeasurableSet (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ∧ GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ≠ ⊤) ∧ Filter.Tendsto (fun k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k})).toReal / (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto | exact GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedCharacterEquivariance
section
open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LocalChar

theorem sPsi : Ad3.LU.SPsi := by
  intro F _ _ _ _ ψ hψ x hx
  obtain ⟨hc, h1, h0⟩ := hψ
  have hb : x ∈ valBall F (addCharConductor ψ) := by
    rw [h0]
    have : x ∈ (valBall F 0 : Set F) := by
      rw [coe_valBall_zero]; exact hx
    exact this
  have := isTrivialOn_addCharConductor hc h1 x hb
  simp [this]

end GlobalTheory.CompanionTheory.LocalChar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedGaugeEstimate
section
open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LUGauge

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mem_integers_of_ord_nonneg {x : F} (hx : x ≠ 0) (h : 0 ≤ ord x) : x ∈ 𝒪[F] := by
  have h1 : normalizedValuation F x ≤ normalizedValuation F 1 := by
    rw [map_one, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have h2 := normalizedValuation_le_iff.1 h1
  rw [map_one] at h2
  exact h2

theorem modulus_coe (a : Fˣ) :
    ((modulus (a : F) : NNReal) : ℝ) = (residueCard F : ℝ) ^ (-ord (a : F)) := by
  rw [modulus_of_ne_zero a.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast]

end

end GlobalTheory.CompanionTheory.LUGauge
end

