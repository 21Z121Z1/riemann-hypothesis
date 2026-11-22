import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.WeilBound.CoreStatements.AutomorphicKernels.ArchimedeanJacquetFirstTerm.ArchimedeanWhittakerTrace.ArchJacquet
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0005
import GroundTheory.ArithmeticGeometry.SchemeCohomology.AffineVanishing
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0458
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryProdCreationLeviChains
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0457
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsThetaIntLtTopOfEqZero
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelAssembly

theorem two_mul_finrank_isotropic_le {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E)
    (W : Submodule E B.V) (hW : ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0) : 2 * Module.finrank E W ≤ B.rank := by
  let b := Module.finBasis E W
  have hl : LinearIndependent E fun i => B.hT (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h1 : B.hT ((∑ i, star (c i) • b i : W) : B.V) = 0 := by
      rw [← hc]; simp [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]
    have h2 : (∑ i, star (c i) • b i : W) = 0 := Subtype.ext (B.nondeg.1 _ fun y => by rw [h1]; rfl)
    simpa using Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 i
  have h3 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range fun i => B.hT (b i)))
  rw [finrank_span_eq_card hl, Fintype.card_fin, B.rank_eq] at h3
  have h4 : W ≤ (Submodule.span E (Set.range fun i => B.hT (b i))).dualCoannihilator := fun y hy => by
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; exact hW _ (b i).2 _ hy
    | zero => rfl
    | add _ _ _ _ h h' => rw [LinearMap.add_apply, h, h', add_zero]
    | smul _ _ _ h => rw [LinearMap.smul_apply, h, smul_zero]
  have := Submodule.finrank_mono h4
  omega

theorem bddAbove_isotropic_dims {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    BddAbove {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0} :=
  ⟨B.rank, by rintro _ ⟨W, rfl, hW⟩; have := two_mul_finrank_isotropic_le B W hW; omega⟩

theorem two_mul_wittIdx_le_rank {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    2 * Formalism.MainNotions.SchurIrreducible.wittIdx B ≤ B.rank := by
  obtain ⟨W, h, hW⟩ := Nat.sSup_mem (s := {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧
    ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0}) ⟨_, ⊥, rfl, by simp⟩ (bddAbove_isotropic_dims B)
  rw [Formalism.MainNotions.SchurIrreducible.wittIdx, ← h]
  exact two_mul_finrank_isotropic_le B W hW

theorem exists_isRowBasis {D : D7} {n : ℕ} (U : Submodule D.host.E (Fin n → D.host.E)) :
    ∃ c, IsRowBasis U c := by
  refine ⟨fun i => ((Module.finBasis D.host.E U i : U) : Fin n → D.host.E), ?_, ?_⟩
  · exact (Module.finBasis D.host.E U).linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · have : Set.range (fun i => ((Module.finBasis D.host.E U i : U) : Fin n → D.host.E)) =
        U.subtype '' Set.range (Module.finBasis D.host.E U) := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, (Module.finBasis D.host.E U).span_eq, Submodule.map_subtype_top]

theorem absThetaInt_lt_top_of_eq_zero {D : D7} (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {r : ℕ}
    (hr : r = 0) (φ : Mx D V.rank r → ℂ) : GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ := by
  subst hr
  have hc : ∀ h, GlobalTheory.SiegelFormula.absTheta V φ h = ‖φ 0‖ₑ := by
    intro h
    unfold GlobalTheory.SiegelFormula.absTheta
    haveI : Unique (Matrix (Fin V.rank) (Fin 0) D.host.E) :=
      inferInstanceAs (Unique (Fin V.rank → Fin 0 → D.host.E))
    rw [tsum_eq_single default (fun b hb => absurd (Subsingleton.elim b default) hb)]
    have h0 : GlobalTheory.SiegelFormula.invPt V h (default : Matrix (Fin V.rank) (Fin 0) D.host.E) = 0 := by
      funext i j; exact j.elim0
    rw [h0]
  unfold GlobalTheory.SiegelFormula.absThetaInt
  have hq : ∀ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q = ‖φ 0‖ₑ := fun q => hc _
  simp_rw [hq, lintegral_const]
  exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)

end GlobalTheory.CompanionTheory.SiegelAssembly

namespace GlobalTheory.CompanionTheory.SiegelAssembly

end GlobalTheory.CompanionTheory.SiegelAssembly
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroup
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula PositivityTheory.FTA.FunctionalEquationHypotheses.B2

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelRadTop

theorem nA_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
    (∀ β : Matrix (Fin n) (Fin n) (AE F E), β ∈ nA σ Y b ↔ βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0) →
    IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) ∧ IsTopologicalAddGroup (nA σ Y b) ∧
    LocallyCompactSpace (nA σ Y b) ∧ SecondCountableTopology (nA σ Y b) ∧ T2Space (nA σ Y b) ∧ BorelSpace (nA σ Y b) := by
  intro F E _ _ _ _ _ σ n Y b ε h
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  have hc : Continuous (cA σ) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  have hS : (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) =
      {β | βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0} := Set.ext h
  have hC : IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) := by
    rw [hS]
    have h1 : Continuous fun β : Matrix (Fin n) (Fin n) (AE F E) => β.map (cA σ) := continuous_id.matrix_map hc
    have h2 : Continuous fun β : Matrix (Fin n) (Fin n) (AE F E) => ((ε : ℤ) : AE F E) • β.map (cA σ) :=
      (continuous_const_smul (((ε : ℤ) : AE F E))).comp h1
    exact isClosed_eq (continuous_id.matrix_transpose.add h2) continuous_const
  haveI : LocallyCompactSpace (nA σ Y b) := hC.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (nA σ Y b) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact ⟨hC, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.CompanionTheory.SiegelRadTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishesStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_cover_higher_cohomology_vanishes : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (str : ∀ W : X.Opens, O →+* Γ(X, W)) (W : X.Opens) (hW : IsAffineOpen W)
    {ι : Type} [Fintype ι] (U : ι → X.Opens) (hU : (⨆ α, U α) = W) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i))
    (K : Cos.{1} O) (V : VB str U K) (p : ℕ), Subsingleton (K.cx.H (p + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.VBAff.subsingleton_H | exact GlobalTheory.CompanionTheory.VBAff.subsingleton_H | (intros; apply GlobalTheory.CompanionTheory.VBAff.subsingleton_H <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMinorHeightBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.MinInf

theorem opNorm_le_one_of_unitary {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) :
    opNorm U ≤ 1 := by
  have h1 : Uᴴ * U = 1 := mul_eq_one_comm.1 hU
  set T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) U with hT
  have h2 : star T * T = 1 := by
    rw [hT, ← map_star, ← map_mul, Matrix.star_eq_conjTranspose, h1, map_one]
  have h3 : ‖T‖ * ‖T‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, h2]
    exact ContinuousLinearMap.norm_id_le
  have h4 : ‖T‖ ≤ 1 := by
    by_contra h
    have h' : 1 < ‖T‖ := not_le.1 h
    nlinarith
  exact_mod_cast h4

theorem nnnorm_entry_le {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (i j : ι) :
    ‖A i j‖₊ ≤ opNorm A := by
  unfold opNorm
  have h1 : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ d, A i d * (EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ ι) d = A i j
    simp
  have h2 := ContinuousLinearMap.le_opNNNorm (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (EuclideanSpace.single j 1)
  rw [PiLp.nnnorm_single, nnnorm_one, mul_one] at h2
  rw [← h1]
  exact (PiLp.nnnorm_apply_le _ i).trans h2

theorem nnnorm_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℝ≥0) (h : ∀ i j, ‖M i j‖₊ ≤ c) :
    ‖M.det‖₊ ≤ (n.factorial : ℝ≥0) * c ^ n := by
  have h1 := Matrix.det_le (A := M) (abv := NormedField.toAbsoluteValue ℂ) (x := (c : ℝ))
    (fun i j => NNReal.coe_le_coe.2 (h i j))
  simp only [Fintype.card_fin, nsmul_eq_mul] at h1
  exact_mod_cast h1

theorem minor_le {R : Type} [CommRing R] (φ : R →+* ℂ) {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (A κ : Matrix ι ι R) (c : ℝ≥0) (hA : opNorm (A.map φ) ≤ c) (hκ : κ.map φ * (κ.map φ)ᴴ = 1) (f e : Fin n → ι) :
    ‖φ ((A * κ).submatrix f e).det‖₊ ≤ (n.factorial : ℝ≥0) * c ^ n := by
  have hAU : opNorm (A.map φ * κ.map φ) ≤ c :=
    (opNorm_mul_le _ _).trans ((mul_le_of_le_one_right' (opNorm_le_one_of_unitary _ hκ)).trans hA)
  have hdet : φ ((A * κ).submatrix f e).det = ((A.map φ * κ.map φ).submatrix f e).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul]
  rw [hdet]
  exact nnnorm_det_le _ c fun i j => (nnnorm_entry_le (A.map φ * κ.map φ) (f i) (e j)).trans hAU

theorem opNorm_le_htInf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : Type) [Fintype ι] [DecidableEq ι] (w : InfinitePlace F) (τ : EmbOver E w) (X : GL ι (AE F E)) :
    opNorm (X.1.map (piInf τ)) ≤ htInf F w (Formalism.UG.bc (compInf F E w) X) := by
  have e : X.1.map (piInf τ) = ((Formalism.UG.bc (compInf F E w) X).1).map (infEmb τ) := by
    ext i j
    rfl
  rw [e]
  exact ((normInf_le_iff F w).1 le_rfl τ).trans (le_htOf (normInf F w) (Formalism.UG.bc (compInf F E w) X))

theorem minor_le_htInf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (w : InfinitePlace F) (τ : EmbOver E w) (X : GL ι (AE F E))
    (κ : Matrix ι ι (AE F E)) (hκ : κ.map (piInf τ) * (κ.map (piInf τ))ᴴ = 1) (f e : Fin n → ι) :
    ‖piInf τ ((X.1 * κ).submatrix f e).det‖₊ ≤
      (n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n :=
  minor_le (piInf τ) X.1 κ _ (opNorm_le_htInf F E ι w τ X) hκ f e

end GlobalTheory.CompanionTheory.GodementH.MinInf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanRationalEmbeddingMapStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_rational_embedding_map : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : GRat σ J) (w : InfinitePlace F) (τ : EmbOver E w), archMat σ J τ (projArch σ J w (ratEmb σ J γ)) = γ.1.1.map τ.1 := by
  first | exact @GlobalTheory.CompanionTheory.CFin.archMat_projArch_ratEmb | exact GlobalTheory.CompanionTheory.CFin.archMat_projArch_ratEmb | (intros; apply GlobalTheory.CompanionTheory.CFin.archMat_projArch_ratEmb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgEqLevel
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgLevel

theorem avg_eq_level : ∀ {H : Type} [Group H] (S : Subgroup H) (u : H → ℂ), S ≤ rStab u →
    S.index ≠ 0 → avg u = ((S.index : ℂ))⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ S u hS hfin
  have hmul := Subgroup.relIndex_mul_index hS
  have hm : S.relIndex (rStab u) ≠ 0 := fun h0 => hfin (by rw [← hmul, h0, zero_mul])
  have hmC : ((S.relIndex (rStab u) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [GlobalTheory.CompanionTheory.HintLevel.finsum_out_of_le u hS le_rfl hm, ← hmul, avg, Nat.cast_mul, mul_inv,
    mul_mul_mul_comm, inv_mul_cancel₀ hmC, one_mul]

end GlobalTheory.CompanionTheory.AvgLevel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolicLocalStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_triangular_mem_minimal_parabolic_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} (v : HeightOneSpectrum (𝓞 F)) (p : GLoc σ J v) (B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E)), B.BlockTriangular id → (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B → emb σ J v p ∈ minPar σ J X := by
  first | exact @GlobalTheory.CompanionTheory.KFin.emb_mem_minPar | exact GlobalTheory.CompanionTheory.KFin.emb_mem_minPar | (intros; apply GlobalTheory.CompanionTheory.KFin.emb_mem_minPar <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolicStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_triangular_mem_minimal_parabolic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A] [TopologicalSpace A] (p : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E)), B.BlockTriangular id → (matHom A σ J p).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B → ∃ m : HA A σ J, (matHom A σ J m).1 = leviMat σ J A X Y (matHom A σ J p).1 ∧ (∃ d : Fin r → A ⊗[F] E, (matHom A σ J m).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * diagonal d) ∧ (∃ d' : Fin r → A ⊗[F] E, (matHom A σ J m).1 * Y.map (inclR (F := F) A) = Y.map (inclR (F := F) A) * diagonal d') ∧ (∃ B' : Matrix (Fin r) (Fin r) (A ⊗[F] E), B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧ (matHom A σ J (m⁻¹ * p)).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B') ∧ ∀ z : Fin n → A ⊗[F] E, ((cT (σ : E →+* E) X * J).map (inclR (F := F) A)) *ᵥ z = 0 → ∃ a : Fin r → A ⊗[F] E, ((matHom A σ J (m⁻¹ * p)).1 - 1) *ᵥ z = X.map (inclR (F := F) A) *ᵥ a := by
  first | exact @GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi | exact GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi | (intros; apply GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryProdCreationLeviChainsStatement
section
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_prod_creation_levi_chains : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (l : List (Pos n)) (x : Cq n V), (∀ e ∈ l, lev e.1.1 = lev e.1.2) →
    (∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
      CompanionTheory.RgExh.U.adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post) →
    SuppL (inUU lev) x → (∀ e ∈ l, Lv lev E1 E2 e.1.1 e.1.2 x = 0) →
    bdL (inRR lev) E1 E2 (((l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V)) x) =
      (-1 : ℂ) ^ l.length • ((l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V))
        (bdL (inRR lev) E1 E2 x) := by
  first | exact @GlobalTheory.CompanionTheory.LvChain.BdProdL.bd_prodL | exact GlobalTheory.CompanionTheory.LvChain.BdProdL.bd_prodL | (intros; apply GlobalTheory.CompanionTheory.LvChain.BdProdL.bd_prodL <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedIntegralMatricesFiniteStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_integral_matrices_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsTotallyReal F → ∀ {ι : Type} [Finite ι] (d : ℕ) (B : ℝ), 0 < d → {N : Matrix ι ι E | (∀ u v, IsIntegral ℤ ((d : E) * N u v)) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : ι), ‖τ.1 (N u v)‖ ≤ B}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite | exact GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite | (intros; apply GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpSectionValueLocalIntegralStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bump_section_value_local_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (s : kˣ)
    (hψ1 : ∀ y ∈ GlobalTheory.SplitWeil.cball s, ψ y = 1) (w : τ.V ⊗[ℂ] σ.V) (F : XS τ σ)
    (h1 : ∀ d : Fin (t + 1) → k, (∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) → evX F (dEmb k i t d) = w)
    (h0 : ∀ d : Fin (t + 1) → k, (¬ ∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) → evX F (dEmb k i t d) = 0),
  ∃ c : ℂ, c ≠ 0 ∧ intC ψ F 1 = c • w := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.intC_one_of_bump | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.intC_one_of_bump | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.intC_one_of_bump <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpTranslateMemSubmoduleStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bump_translate_mem_submodule : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (ρ : Representation ℂ H W) (K₁ K₂ : Subgroup G) (h₂₁ : K₂ ≤ K₁)
    (hK₁c : IsCompact (K₁ : Set G)) (hK₂o : IsOpen (K₂ : Set G)) (v : W)
    (hv : ∀ a : H, (a : G) ∈ K₁ → ρ a v = v) (S : Submodule ℂ (cIndSpace H ρ))
    (hS : ∀ g, ∀ b ∈ S, cInd H ρ g b ∈ S) (b : cIndSpace H ρ) (hb : IsBump H ρ K₂ 1 v b) (hbS : b ∈ S)
    (B : cIndSpace H ρ) (hB : IsBump H ρ K₁ 1 v B), B ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Avg.bump_mem_of_bump | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Avg.bump_mem_of_bump | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Avg.bump_mem_of_bump <;> assumption)
end

