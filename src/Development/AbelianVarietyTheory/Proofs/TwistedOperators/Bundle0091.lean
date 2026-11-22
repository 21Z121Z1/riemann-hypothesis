import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0086
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0087
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsDetOnStableSubspaceConjTransposeStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absDetOnStableSubspace_conjTranspose : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)), (∀ y ∈ V, g *ᵥ y ∈ V) → (∀ y ∈ V, gᴴ *ᵥ y ∈ V) → GlobalTheory.FlagMeas.detOn gᴴ V = GlobalTheory.FlagMeas.detOn g V := by
  first | exact @GlobalTheory.FlagMeas.DetAdj.detOn_conjTranspose | exact GlobalTheory.FlagMeas.DetAdj.detOn_conjTranspose | (intros; apply GlobalTheory.FlagMeas.DetAdj.detOn_conjTranspose <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdMatSqMulVecAdSqEigenvectorMatrixUnitPStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adMat_sq_mulVec_adSqEigenvectorMatrixUnitP : ∀ (p q : ℕ) (h : ℕ → ℝ) (ab : PIx p q), (adMat (aOf p q h) ^ 2) *ᵥ eigP ab.1 = (((rootP h ab.1 : ℝ) : ℂ) ^ 2) • eigP ab.1 := by
  first | exact @GlobalTheory.PolarU.adMat_sq_mulVec_eigP | exact GlobalTheory.PolarU.adMat_sq_mulVec_eigP | (intros; apply GlobalTheory.PolarU.adMat_sq_mulVec_eigP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardBlockUpperTriangularSubgroupOfTopBlock
section
noncomputable section

open Matrix Formalism.L2.DIV

namespace GlobalTheory.ParIndex

variable {κ : Type} [Field κ] {r t : ℕ}

abbrev blkForm (g : GL (Fin (r + t)) κ) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) κ :=
  (g : Matrix (Fin (r + t)) (Fin (r + t)) κ).submatrix finSumFinEquiv finSumFinEquiv

theorem blkForm_toBlocks₂₁ {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    (blkForm g).toBlocks₂₁ = 0 := by
  ext i j
  simp only [toBlocks₂₁, blkForm, submatrix_apply, of_apply, Matrix.zero_apply, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right]
  apply hg
  have hj : (Fin.castAdd t j).val < r := j.2
  have hi : ¬ (Fin.natAdd r i).val < r := by simp
  simp only [blk2, hj, hi, if_true, if_false]
  exact Nat.zero_lt_one

theorem blkForm_eq {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    blkForm g = fromBlocks (blkForm g).toBlocks₁₁ (blkForm g).toBlocks₁₂ 0 (blkForm g).toBlocks₂₂ := by
  rw [← blkForm_toBlocks₂₁ hg, fromBlocks_toBlocks]

theorem det_blkForm_toBlocks22_ne_zero_of_mem_blockTri {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    (blkForm g).toBlocks₂₂.det ≠ 0 := by
  have h1 : (g : Matrix (Fin (r + t)) (Fin (r + t)) κ).det ≠ 0 := g.isUnit.map Matrix.detMonoidHom |>.ne_zero
  have h2 : (blkForm g).det = (g : Matrix (Fin (r + t)) (Fin (r + t)) κ).det := det_submatrix_equiv_self _ _
  rw [blkForm_eq hg, det_fromBlocks_zero₂₁] at h2
  intro h; rw [h, mul_zero] at h2; exact h1 h2.symm

def blkMk (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) : GL (Fin (r + t)) κ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((fromBlocks (A : Matrix (Fin r) (Fin r) κ) B 0 (D : Matrix (Fin t) (Fin t) κ)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm) (by
    rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
    exact mul_ne_zero (A.isUnit.map Matrix.detMonoidHom).ne_zero (D.isUnit.map Matrix.detMonoidHom).ne_zero)

theorem blkForm_blkMk (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) :
    blkForm (blkMk A D B) = fromBlocks (A : Matrix (Fin r) (Fin r) κ) B 0 (D : Matrix (Fin t) (Fin t) κ) := by
  ext i j
  simp [blkForm, blkMk, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem blkMk_mem (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) :
    blkMk A D B ∈ blockTri (blk2 r) := by
  intro i j hij
  have key : r ≤ i.val ∧ j.val < r := by unfold blk2 at hij; split_ifs at hij <;> omega
  obtain ⟨i', rfl⟩ : ∃ i', i = Fin.natAdd r i' := ⟨⟨i.val - r, by omega⟩, by ext; simp; omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = Fin.castAdd t j' := ⟨⟨j.val, key.2⟩, by ext; simp⟩
  simp [blkMk, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem topBlock_upperTriangularBlockGL (hr : r ≤ r + t) (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) :
    upperLeftBlock hr (blkMk A D B) = A := by
  ext i j
  rw [upper_block_val_submatrix hr (blkMk_mem A D B)]
  have : Fin.castLE hr = Fin.castAdd t := rfl
  rw [this]
  simp [blkMk, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem upperLeftBlock_eq_blkForm_toBlocks11 (hr : r ≤ r + t) {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    ((upperLeftBlock hr g : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) = (blkForm g).toBlocks₁₁ := by
  rw [upper_block_val_submatrix hr hg]
  ext i j
  rfl

def parSubEquiv (hr : r ≤ r + t) (H : Subgroup (GL (Fin r) κ)) :
    parSub hr H ≃ H × GL (Fin t) κ × Matrix (Fin r) (Fin t) κ where
  toFun g := (⟨upperLeftBlock hr g, g.2.2⟩,
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_blkForm_toBlocks22_ne_zero_of_mem_blockTri g.2.1), (blkForm (g : GL (Fin (r + t)) κ)).toBlocks₁₂)
  invFun x := ⟨blkMk x.1 x.2.1 x.2.2, blkMk_mem _ _ _, by rw [topBlock_upperTriangularBlockGL]; exact x.1.2⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    have h1 := blkForm_blkMk (r := r) (t := t) (κ := κ) (upperLeftBlock hr g)
      (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_blkForm_toBlocks22_ne_zero_of_mem_blockTri g.2.1)) (blkForm (g : GL (Fin (r + t)) κ)).toBlocks₁₂
    have h2 := blkForm_eq g.2.1
    rw [upperLeftBlock_eq_blkForm_toBlocks11 hr g.2.1] at h1
    have h3 : blkForm (blkMk (upperLeftBlock hr g) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_blkForm_toBlocks22_ne_zero_of_mem_blockTri g.2.1))
        (blkForm (g : GL (Fin (r + t)) κ)).toBlocks₁₂) = blkForm (g : GL (Fin (r + t)) κ) := by
      exact h1.trans h2.symm
    ext i j
    have := congrFun (congrFun h3 (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
    simpa [blkForm] using this
  right_inv x := by
    obtain ⟨A, D, B⟩ := x
    refine Prod.ext (Subtype.ext (topBlock_upperTriangularBlockGL hr _ _ _)) (Prod.ext ?_ ?_)
    · apply Units.ext
      show (blkForm (blkMk A.1 D B)).toBlocks₂₂ = _
      rw [blkForm_blkMk]; rfl
    · show (blkForm (blkMk A.1 D B)).toBlocks₁₂ = _
      rw [blkForm_blkMk]; rfl

theorem card_parSub_eq (hr : r ≤ r + t) (H : Subgroup (GL (Fin r) κ)) [Finite κ] :
    Nat.card (parSub hr H) = Nat.card H * Nat.card (GL (Fin t) κ) * Nat.card κ ^ (r * t) := by
  rw [Nat.card_congr (parSubEquiv hr H), Nat.card_prod, Nat.card_prod, mul_assoc]
  congr 2
  show Nat.card (Fin r → Fin t → κ) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r), Nat.card_eq_fintype_card (α := Fin t),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]

theorem card_parSub : ∀ (κ : Type) [Field κ] [Finite κ] (n r t : ℕ) (hr : r ≤ n), n = r + t →
    ∀ H : Subgroup (GL (Fin r) κ),
      Nat.card (GlobalTheory.ParIndex.parSub hr H) = Nat.card H * Nat.card (GL (Fin t) κ) * Nat.card κ ^ (r * t) := by
  intro κ _ _ n r t hr hn H
  subst hn
  exact card_parSub_eq hr H

end GlobalTheory.ParIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPolarCoordinatesJacobianStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_polarCoordinatesJacobian : ∀ (p q : ℕ), Continuous (polJ : Mat p q → ℝ) := by
  first | exact @GlobalTheory.PolarU.continuous_polJ | exact GlobalTheory.PolarU.continuous_polJ | (intros; apply GlobalTheory.PolarU.continuous_polJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetAdSqEigenvectorMatrixUnitPNeZeroStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_adSqEigenvectorMatrix_ne_zero : ∀ (p q : ℕ), (Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1).det ≠ 0 := by
  first | exact @GlobalTheory.PolarU.det_eigenvectorMatrix_ne_zero | exact GlobalTheory.PolarU.det_eigenvectorMatrix_ne_zero | (intros; apply GlobalTheory.PolarU.det_eigenvectorMatrix_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetSinhcAdjointUpperRightCoordEqPolJStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_sinhcAdjointUpperRightCoord_eq_polJ : ∀ (p q : ℕ) (Y : Mat p q), (∀ C : Fin p → Fin q → ℂ, sAd Y (pY C) = pY (sP Y C)) → LinearMap.det (sP Y) = polJ Y := by
  first | exact @GlobalTheory.PolarU.det_sinhc_eq_polarJacobian | exact GlobalTheory.PolarU.det_sinhc_eq_polarJacobian | (intros; apply GlobalTheory.PolarU.det_sinhc_eq_polarJacobian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBasisOfIsQuadraticExtension
section
open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

theorem exists_basis_of_isQuadraticExtension (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] :
    ∃ (δ : K) (e : Module.Basis (Fin 2) K L), ¬ IsSquare δ ∧ e 0 = 1 ∧ e 1 * e 1 = algebraMap K L δ := by
  have hr : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  have : IsGalois K L := inferInstance
  have hc : Nat.card (L ≃ₐ[K] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, hr]
  have : Nontrivial (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : L ≃ₐ[K] L)
  have h2 : σ * σ = 1 := by
    have := pow_card_eq_one' (x := σ)
    rwa [hc, pow_two] at this
  obtain ⟨δ, b, hδ, h0, -, h1⟩ := GlobalTheory.QuadNormBase.exists_basis K L (σ : L →ₐ[K] L) hr
    (fun x => by simpa using congrArg (fun f : L ≃ₐ[K] L => f x) h2)
    (by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext fun x => h x))
  exact ⟨δ, b, hδ, h0, h1⟩

theorem exists_completion_hom_real {K : Type} [Field K] (σ : K →+* ℝ) :
    ∃ (w : InfinitePlace K) (f : w.Completion →+* ℝ), ∀ x : K, f (algebraMap K w.Completion x) = σ x := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := InfinitePlace.isReal_mk_iff.2 hφ
  refine ⟨_, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw, fun x => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv _).symm x)
  refine Eq.trans he ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp

theorem normTheorem : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L], NormTheorem K L := by
  intro K L _ _ _ _ _ _ t
  obtain ⟨δ, e, hδ, h0, h1⟩ := exists_basis_of_isQuadraticExtension K L
  have : FiniteDimensional K L := Module.Finite.of_basis e
  refine ⟨fun h => ⟨fun v => toUnits_mem_normGroup _ h, fun w => toUnits_mem_normGroup _ h⟩, ?_⟩
  rintro ⟨hf, hi⟩
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hδ ⟨0, by simp⟩
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt K δ t hδ0 t.ne_zero
    (fun σ => by
      obtain ⟨w, f, hw⟩ := exists_completion_hom_real σ
      obtain ⟨a, b, hab⟩ := (mem_normGroup_iff_form e h0 h1).1 (hi w)
      refine ⟨f a, f b, ?_⟩
      have h3 : algebraMap K w.Completion t = a ^ 2 - algebraMap K w.Completion δ * b ^ 2 := hab
      rw [← hw, ← hw, h3, map_sub, map_mul, map_pow, map_pow])
    (fun v => (mem_normGroup_iff_form e h0 h1).1 (hf v))
  refine mem_globalNorms_iff.2 ⟨a • e 0 + b • e 1, ?_⟩
  rw [hab]
  refine GlobalTheory.QuadNormBase.norm_of_basis e δ h0 ?_ a b
  rw [h1, h0, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.QuadSymbol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBiinvariantProbabilityOnCompactSubgroupStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_biinvariant_probability_on_compact_subgroup' : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (K : Subgroup G), IsCompact (K : Set G) → ∃ mK : Measure G, IsProbabilityMeasure mK ∧ mK (K : Set G)ᶜ = 0 ∧ (∀ k ∈ K, Measure.map (fun x => k * x) mK = mK) ∧ ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK := by
  first | exact @GlobalTheory.exists_biinvariant_probability_on_compact_subgroup | exact GlobalTheory.exists_biinvariant_probability_on_compact_subgroup | (intros; apply GlobalTheory.exists_biinvariant_probability_on_compact_subgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousOnPolarLogStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousOn_polar_log' : ∀ (p q : ℕ), ∃ L : Mat p q → (Fin p → Fin q → ℂ), ContinuousOn L {g | IsUnit g} ∧ ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B := by
  first | exact @GlobalTheory.PolarLogCont.exists_continuousOn_polar_log | exact GlobalTheory.PolarLogCont.exists_continuousOn_polar_log | (intros; apply GlobalTheory.PolarLogCont.exists_continuousOn_polar_log <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphicActionOfCoverOnPStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homeomorphic_action_of_cover_on_p : ∀ (p q : ℕ) (T : GrpData p q) (L : Mat p q → (Fin p → Fin q → ℂ)), ContinuousOn L {g | IsUnit g} → (∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B) → (∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y) → ∀ g : T.G, ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧ ∀ B, ∃ κ ∈ T.Kset, T.expt (pY B) * g = κ * T.expt (pY (ψ B)) := by
  first | exact @GlobalTheory.PolarU.exists_action_on_p | exact GlobalTheory.PolarU.exists_action_on_p | (intros; apply GlobalTheory.PolarU.exists_action_on_p <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIndefiniteUnitaryBoostHilbertSchmidtStatement
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_indefiniteUnitary_boost_hilbertSchmidt : ∀ (m : ℕ) (ε : Fin m → Bool) (a b : Fin m → ℂ), (∀ i, ε i = false → a i = 0) → (∀ i, ε i = true → b i = 0) → ∑ i, ‖a i‖ ^ 2 = 1 + ∑ i, ‖b i‖ ^ 2 → ∃ A ∈ UJset ε, (∀ i, ∑ j, A i j * a j = (Real.sqrt (∑ j, ‖a j‖ ^ 2) : ℂ) * (a i + b i)) ∧ hsn A ^ 2 ≤ (m : ℝ) + 2 * ∑ i, ‖a i + b i‖ ^ 2 := by
  first | exact @GlobalTheory.Boost.boost_exists | exact GlobalTheory.Boost.boost_exists | (intros; apply GlobalTheory.Boost.boost_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFockProjectionMaximalMinorsStatement
section
open Classical MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_fock_projection_maximal_minors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℚ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), ∀ T : GlobalTheory.MinorFrame.Tup ι a d n,
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.prodMinors T)
      (MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (U p)) = 0 := by
  first | exact @GlobalTheory.MinorFrame.RatProj.exists_rat_proj | exact GlobalTheory.MinorFrame.RatProj.exists_rat_proj | (intros; apply GlobalTheory.MinorFrame.RatProj.exists_rat_proj <;> assumption)
end

