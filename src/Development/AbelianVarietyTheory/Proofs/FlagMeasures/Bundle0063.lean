import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0056
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLatIffMemLocP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0057
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0059
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCompleteDense
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct

noncomputable section

namespace GlobalTheory.HilbTensorExists

theorem exists_pre_fin (n : ℕ) : ∀ (H : Fin n → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)],
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (t : (∀ v, H v) → K),
      ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ := by
  induction n with
  | zero =>
    intro H _ _
    refine ⟨ℂ, inferInstance, inferInstance, fun _ => 1, fun x y => ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    simp
  | succ n ih =>
    intro H _ _
    obtain ⟨K, iK, iK', t, ht⟩ := ih (fun i => H i.castSucc)
    refine ⟨K ⊗[ℂ] H (Fin.last n), inferInstance, inferInstance,
      fun x => t (fun i => x i.castSucc) ⊗ₜ[ℂ] x (Fin.last n), fun x y => ?_⟩
    rw [TensorProduct.inner_tmul, ht, Fin.prod_univ_castSucc]

theorem exists_pre {ι : Type} [Fintype ι] (H : ι → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (t : (∀ v, H v) → K),
      ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ := by
  let e := Fintype.equivFin ι
  obtain ⟨K, iK, iK', t, ht⟩ := exists_pre_fin (Fintype.card ι) (fun i => H (e.symm i))
  refine ⟨K, iK, iK', fun x => t (fun i => x (e.symm i)), fun x y => ?_⟩
  rw [ht]
  exact e.symm.prod_comp (fun v => ⟪x v, y v⟫_ℂ)

theorem exists_complete_dense {X K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (t : X → K) :
    ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L) (_ : CompleteSpace L) (s : X → L),
      (∀ x y, ⟪s x, s y⟫_ℂ = ⟪t x, t y⟫_ℂ) ∧ Dense (Submodule.span ℂ (Set.range s) : Set L) := by
  let V := Submodule.span ℂ (Set.range t)
  let u : X → V := fun x => ⟨t x, Submodule.subset_span ⟨x, rfl⟩⟩
  have hu : Submodule.span ℂ (Set.range u) = ⊤ := by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    rfl
  refine ⟨UniformSpace.Completion V, inferInstance, inferInstance, inferInstance,
    fun x => ((u x : V) : UniformSpace.Completion V), fun x y => ?_, ?_⟩
  · rw [UniformSpace.Completion.inner_coe]
    rfl
  · refine UniformSpace.Completion.denseRange_coe.mono ?_
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span ℂ (Set.range u) := hu ▸ Submodule.mem_top
    have hm := Submodule.mem_map_of_mem
      (f := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := V)).toLinearMap) hv
    rw [Submodule.map_span, ← Set.range_comp] at hm
    exact hm

theorem exists_extension {X L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (s : X → L) (hs : Dense (Submodule.span ℂ (Set.range s) : Set L)) (f : X → X)
    (hf : ∀ x y, ⟪s (f x), s (f y)⟫_ℂ = ⟪s x, s y⟫_ℂ) :
    ∃ T : L →L[ℂ] L, ∀ x, T (s x) = s (f x) := by
  let S := Finsupp.linearCombination ℂ s
  let A := Finsupp.linearCombination ℂ (s ∘ f)
  have key : ∀ c : X →₀ ℂ, ⟪A c, A c⟫_ℂ = ⟪S c, S c⟫_ℂ := by
    intro c
    simp only [A, S, Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
      inner_smul_left, inner_smul_right, Function.comp_apply, hf]
  have hn : ∀ c, ‖A c‖ ≤ 1 * ‖S c‖ := by
    intro c
    rw [one_mul, @norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, key]
  have hd : DenseRange S := by
    rw [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination]
    exact hs
  refine ⟨A.extendOfNorm S, fun x => ?_⟩
  have h := LinearMap.extendOfNorm_eq hd ⟨1, hn⟩ (Finsupp.single x (1 : ℂ))
  simp only [S, A, Finsupp.linearCombination_single, one_smul, Function.comp_apply] at h
  exact h

theorem exists_isHilbTensor (I : AutInst) (H : NumberField.InfinitePlace I.F → Type)
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (hσ : ∀ v (g : Formalism.REAL.UJ (I.ε v)) x y, ⟪σ v (uMat g) x, σ v (uMat g) y⟫_ℂ = ⟪x, y⟫_ℂ) :
    ∃ (Hs : Type) (_ : NormedAddCommGroup Hs) (_ : InnerProductSpace ℂ Hs) (_ : CompleteSpace Hs)
      (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs), I.IsHilbTensor σ σs tens := by
  obtain ⟨K, iK, iK', t, ht⟩ := exists_pre H
  obtain ⟨L, iL, iL', iL'', s, hs, hd⟩ := exists_complete_dense t
  have hext : ∀ g : I.Ginf, ∃ T : L →L[ℂ] L,
      ∀ x, T (s x) = s (fun v => σ v (uMat (g v)) (x v)) := by
    intro g
    refine exists_extension s hd (fun x v => σ v (uMat (g v)) (x v)) (fun x y => ?_)
    simp only [hs, ht]
    exact Finset.prod_congr rfl fun v _ => hσ v (g v) (x v) (y v)
  choose σs hσs using hext
  refine ⟨L, iL, iL', iL'', σs, s, ?_⟩
  unfold Formalism.MainNotions.S.AutInst.IsHilbTensor
  exact ⟨fun x y => by rw [hs, ht], hσs, hd⟩

end GlobalTheory.HilbTensorExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMultilinearMapOfInnerProd
section
open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

namespace GlobalTheory

theorem eq_of_inner_eq_on_dense_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {s : Set E} (hs : Dense (Submodule.span ℂ s : Set E)) {a b : E}
    (h : ∀ y ∈ s, ⟪y, a⟫_ℂ = ⟪y, b⟫_ℂ) : a = b := by
  have h1 : ∀ y ∈ Submodule.span ℂ s, ⟪y, a⟫_ℂ = ⟪y, b⟫_ℂ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, inner_add_left, hy, hz]
    | smul c y _ hy => rw [inner_smul_left, inner_smul_left, hy]
  have h2 : (fun y : E => ⟪y, a⟫_ℂ) = fun y => ⟪y, b⟫_ℂ :=
    Continuous.ext_on hs (by fun_prop) (by fun_prop) h1
  exact ext_inner_left ℂ fun y => congrFun h2 y

theorem exists_continuousMultilinearMap_of_inner_prod {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (t : (∀ v, H v) → E)
    (hin : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range t) : Set E)) :
    ∃ m : ContinuousMultilinearMap ℂ H E, (∀ x, m x = t x) ∧ ∀ x, ‖t x‖ = ∏ v, ‖x v‖ := by
  have hn : ∀ x, ‖t x‖ = ∏ v, ‖x v‖ := by
    intro x
    have h := hin x x
    simp only [inner_self_eq_norm_sq_to_K] at h
    have h' : ‖t x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by
      rw [← Finset.prod_pow]
      exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun v _ => norm_nonneg _)
      two_ne_zero).1 h'
  have hu : ∀ [DecidableEq ι] (y x : ∀ v, H v) (i : ι) (a : H i),
      ⟪t y, t (Function.update x i a)⟫_ℂ =
        ⟪y i, a⟫_ℂ * ∏ j ∈ Finset.univ.erase i, ⟪y j, x j⟫_ℂ := by
    intro _ y x i a
    rw [hin, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  let m : MultilinearMap ℂ H E :=
    { toFun := t
      map_update_add' := by
        intro _ x i a b
        refine eq_of_inner_eq_on_dense_span hd ?_
        rintro _ ⟨y, rfl⟩
        rw [inner_add_right, hu, hu, hu, inner_add_right, add_mul]
      map_update_smul' := by
        intro _ x i c a
        refine eq_of_inner_eq_on_dense_span hd ?_
        rintro _ ⟨y, rfl⟩
        rw [inner_smul_right, hu, hu, inner_smul_right, mul_assoc] }
  refine ⟨m.mkContinuous 1 fun x => ?_, fun x => rfl, hn⟩
  rw [one_mul]
  exact (hn x).le

theorem rowsAut_tens_continuousMultilinear :
    ∀ B : RowsAut, ∃ m : ContinuousMultilinearMap ℂ B.H B.Hs,
      (∀ x, m x = B.tens x) ∧ ∀ x, ‖B.tens x‖ = ∏ v, ‖x v‖ := fun B =>
  exists_continuousMultilinearMap_of_inner_prod B.tens B.tens_spec.1 B.tens_spec.2.2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalUnitriangularOfLocalCongruenceStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_unitriangular_of_local_congruence : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : GlobalTheory.HL.Places F E sig) (N r : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)), Λ.FG → ∀ (g : ℕ), 0 < g → ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (y x : Fin (r + 1) → Fin N → E) (ξp : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), (∀ a b, ξp a b ∈ (A.L p).O) → (∀ a b, b < a → ξp a b = 0) → (∀ a, ξp a a = 1) → (∀ a, A.bc p (y a) ∈ A.lat p Λ) → (∀ b, A.bc p (x b) - ∑ a, ξp a b • A.bc p (y a) ∈ A.lat p (Ideal.span {(g : 𝓞 E)} • Λ)) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → ∀ b, x b - ∑ a, ((ξ a b : 𝓞 E) : E) • y a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ)) := by
  first | exact @GlobalTheory.HL.LocCongApprox.loc_cong_approx | exact GlobalTheory.HL.LocCongApprox.loc_cong_approx | (intros; apply GlobalTheory.HL.LocCongApprox.loc_cong_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroupStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gluing_homomorphism_defect_group : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∀ w ∈ S.complementLatticeOfDatum d, ∃ y ∈ S.sat Λ, S.TauRel d Λ w y) ∧ (∀ w y y', S.TauRel d Λ w y → (S.TauRel d Λ w y' ↔ y - y' ∈ S.M d Λ)) ∧ (∀ c ∈ L.O, ∀ w₁ w₂ y₁ y₂, S.TauRel d Λ w₁ y₁ → S.TauRel d Λ w₂ y₂ → S.TauRel d Λ (c • w₁ + w₂) (c • y₁ + y₂)) ∧ (∀ w ∈ S.W0, w ∈ Λ ↔ (w ∈ S.complementLatticeOfDatum d ∧ S.TauRel d Λ w 0)) ∧ S.Ihat d Λ ≤ S.sat Λ ∧ ∃ b : Fin (k - 1) → S.V, LinearIndependent E b ∧ S.complementLatticeOfDatum d = (Submodule.span L.O (Set.range b) : Set S.V) := by
  first | exact @GlobalTheory.HL.Gluing.main | exact GlobalTheory.HL.Gluing.main | (intros; apply GlobalTheory.HL.Gluing.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnramStatement
section
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_add_star_eq_one_of_isCMUnram' : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∃ t : 𝓞 K, (t : K) + star (t : K) = 1 := by
  first | exact @GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram | exact GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram | (intros; apply GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryTupleMatrixRightMulNearIdentityStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_tupleMatrixRightMul_near_identity : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N e : ℕ, ∃ i0 : ℕ, ∀ i ≥ i0, ∀ x : Fin m → Fin n → E, (∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ) → gramT L Hm x = Γ → ∀ A ∈ congK L ϖ m i, cT L A * Γ * A = Γ → ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∀ a, g (x a) = rmul x A a := by
  first | exact @GlobalTheory.HL.RStab.exists_isometry_rmul | exact GlobalTheory.HL.RStab.exists_isometry_rmul | (intros; apply GlobalTheory.HL.RStab.exists_isometry_rmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormSqTensUpdate
section
open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace GlobalTheory

theorem exists_gram_factor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {k : ℕ}
    (x : Fin k → E) : ∃ C : Fin k → Fin k → ℂ, ∀ l l',
      ⟪x l, x l'⟫_ℂ = ∑ r, (starRingEnd ℂ) (C r l) * C r l' := by
  have h := (Matrix.posSemidef_gram ℂ x).nonneg
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h
  refine ⟨fun r l => C r l, fun l l' => ?_⟩
  have := congrFun (congrFun hC l) l'
  simpa [Matrix.gram_apply, Matrix.mul_apply, Matrix.star_apply] using this

theorem exists_normSq_tens_update {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (tens : (∀ v, H v) → Hs)
    (ht : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (v₀ : ι) {k : ℕ}
    (u : Fin k → ∀ v, H v) :
    ∃ C : ({v // v ≠ v₀} → Fin k) → Fin k → ℂ, ∀ a : Fin k → H v₀,
      ‖∑ l, tens (Function.update (u l) v₀ (a l))‖ ^ 2 = ∑ r, ‖∑ l, C r l • a l‖ ^ 2 := by
  choose D hD using fun v : {v // v ≠ v₀} => exists_gram_factor (fun l => u l v.1)
  refine ⟨fun r l => ∏ v, D v (r v) l, fun a => ?_⟩
  have key : ∀ l l', ⟪tens (Function.update (u l) v₀ (a l)),
      tens (Function.update (u l') v₀ (a l'))⟫_ℂ =
      ∑ r : {v // v ≠ v₀} → Fin k,
        ⟪(∏ v, D v (r v) l) • a l, (∏ v, D v (r v) l') • a l'⟫_ℂ := by
    intro l l'
    rw [ht, Fintype.prod_eq_mul_prod_subtype_ne _ v₀]
    simp only [Function.update_self]
    have h1 : ∏ v : {v // v ≠ v₀}, ⟪Function.update (u l) v₀ (a l) v.1,
        Function.update (u l') v₀ (a l') v.1⟫_ℂ =
        ∏ v : {v // v ≠ v₀}, ∑ r, (starRingEnd ℂ) (D v r l) * D v r l' := by
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Function.update_of_ne v.2, Function.update_of_ne v.2, hD]
    rw [h1, Fintype.prod_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [inner_smul_left, inner_smul_right, Finset.prod_mul_distrib, map_prod]
    ring
  have hc : ((‖∑ l, tens (Function.update (u l) v₀ (a l))‖ ^ 2 : ℝ) : ℂ) =
      ((∑ r : {v // v ≠ v₀} → Fin k, ‖∑ l, (∏ v, D v (r v) l) • a l‖ ^ 2 : ℝ) : ℂ) := by
    have hn : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (z : E),
        ((‖z‖ ^ 2 : ℝ) : ℂ) = ⟪z, z⟫_ℂ := by
      intro E _ _ z
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [Complex.ofReal_sum, hn]
    simp only [hn, sum_inner, inner_sum, key]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
  exact_mod_cast hc

theorem sum_normSq_tens_update_le :
    ∀ (B : RowsAut) (v₀ : InfinitePlace B.I.F) (S : ∀ v, Submodule ℂ (B.H v)) (m : ℕ) (L : Fin m → (S v₀ →ₗ[ℂ] B.H v₀)) (β : ℝ), (∀ y : S v₀, ∑ i, ‖L i y‖ ^ 2 ≤ β * ‖y‖ ^ 2) → ∀ (k : ℕ) (u : Fin k → ∀ v, S v), open Classical in ∑ i, ‖∑ l, B.tens (Function.update (fun v => (u l v : B.H v)) v₀ (L i (u l v₀)))‖ ^ 2 ≤ β * ‖∑ l, B.tens (fun v => (u l v : B.H v))‖ ^ 2 := by
  classical
  intro B v₀ S m L β hL k u
  obtain ⟨C, hC⟩ := exists_normSq_tens_update B.tens B.tens_spec.1 v₀
    (fun l v => (u l v : B.H v))
  have h0 := hC (fun l => (u l v₀ : B.H v₀))
  have hu : ∀ l, Function.update (fun v => (u l v : B.H v)) v₀ (u l v₀ : B.H v₀) =
      fun v => (u l v : B.H v) := fun l => Function.update_eq_self v₀ _
  simp only [hu] at h0
  rw [h0, Finset.mul_sum]
  have h1 : ∀ i, _ := fun i => hC (fun l => L i (u l v₀))
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun r _ => ?_
  have := hL (∑ l, C r l • u l v₀)
  simp only [map_sum, map_smul] at this
  refine this.trans_eq ?_
  rw [← Submodule.norm_coe]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalSameIntegralSpanUnimodular
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SelfDual

open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

theorem exists_orthonormal_same_span : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ b : Fin m → Fin n → E, (∀ i j, hf L Hm (b i) (b j) ∈ L.O) → (∃ P : Matrix (Fin m) (Fin m) E, IsIntM L P ∧ (Matrix.of fun i j => hf L Hm (b i) (b j)) * P = 1) → ∃ b' : Fin m → Fin n → E, (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) ∧ Submodule.span L.O (Set.range b') = Submodule.span L.O (Set.range b) := by
  intro F _ _ _ _ _ E _ _ _ L n m Hm hH b hint₀ hunim
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨htr, -, -, hpir, -, -, -, hnorm⟩ := order_facts L ϖ hϖ
  obtain ⟨P₀, hP₀, hGP₀⟩ := hunim
  have hmem : ∀ i, b i ∈ Submodule.span L.O (Set.range b) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  have hsm : ∀ (a : L.O) (v : Fin n → E), a • v = (a : E) • v := fun _ _ => rfl
  let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => cj_mem L hx
  have hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (L.cj_cj x)
  let G : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨hf L Hm (b i) (b j), hint₀ i j⟩
  have hGv : ∀ i j, (G i j : E) = hf L Hm (b i) (b j) := fun _ _ => rfl
  have hG : ∀ i j, c (G i j) = G j i := fun i j => Subtype.ext (hf_cj L hH.1 _ _)
  let Q : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨P₀ i j, hP₀ i j⟩
  have hGQ : G * Q = 1 := by
    ext i j
    have h := congrFun (congrFun hGP₀ i) j
    rw [Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero,
      Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum]
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  let : Algebra 𝒪[F] L.O := i.toAlgebra
  have hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range := fun x hx => by
    obtain ⟨a, ha⟩ := exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
    exact ⟨a, Subtype.ext ha.symm⟩
  have hinj : Function.Injective (algebraMap 𝒪[F] L.O) := fun a b h =>
    Subtype.ext (algebraMap_inj L (congrArg Subtype.val h))
  obtain ⟨P, hP, hGP⟩ := GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map (R₀ := 𝒪[F]) c hc hfix
    (by
      obtain ⟨w, hw, h⟩ := htr 1
      exact ⟨⟨w, hw⟩, Subtype.ext (by simpa [hcv] using h)⟩)
    (fun u hu hu' => by
      obtain ⟨v, hv⟩ := hu'.exists_right_inv
      have hv' := congrArg c hv
      rw [map_mul, hu, map_one] at hv'
      obtain ⟨s, rfl⟩ := hfix v (by linear_combination v * hv' - c v * hv)
      obtain ⟨r, rfl⟩ := hfix u hu
      have hr : IsUnit r := IsUnit.of_mul_eq_one s (hinj (by rw [map_mul, hv, map_one]))
      obtain ⟨x, hx, h⟩ := hnorm hr.unit
      exact ⟨⟨x, hx⟩, Subtype.ext h⟩)
    hG (Matrix.isUnit_det_of_right_inverse hGQ)
  have hQ : (P⁻¹)ᵀ * G * (P⁻¹).map c = 1 := by
    rw [hGP, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.transpose_one, Matrix.one_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.map_one _ (map_zero c) (map_one c)]
  refine ⟨fun i => ∑ k, P⁻¹ k i • b k, fun i j => ?_, le_antisymm ?_ ?_⟩
  · have h := congrArg Subtype.val (congrFun (congrFun hQ i) j)
    rw [Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero] at h
    rw [← h]
    simp only [hsm, hf_sum_l, hf_sum_r, Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum,
      Subring.coe_mul, Matrix.transpose_apply, Matrix.map_apply, hcv, hGv]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmem l)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine (Submodule.mem_span_range_iff_exists_fun L.O).2 ⟨fun i => P i k, ?_⟩
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h : ∀ l, ∑ i, P i k * P⁻¹ l i = if l = k then 1 else 0 := fun l => by
      rw [← Matrix.one_apply, ← Matrix.nonsing_inv_mul _ hP, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp [← Finset.sum_smul, h]

end GlobalTheory.HL.SelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueGlobalLatticeOfLocalLattices
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

theorem glue : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep)), (∀ p, IsLat (A.L p) (Λ p)) → {p | Λ p ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite → ∃! Γ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Γ ∧ ∀ p, A.lat p Γ = Λ p := by
  intro F E _ _ _ _ _ sig A n Λ hlat hfin
  refine existsUnique_of_exists_of_unique ?_ ?_
  · have happ1 := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A (fun _ => 1)
      (Set.finite_empty.subset fun p hp => hp ⟨1, by simp⟩)).2.1
    have h3 : ∀ p (y : (A.loc p).Ep), ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O :=
      GlobalTheory.T.exists_nat_mul_mem_integers_quadraticCompletion A (fun y hy => by
        obtain ⟨x, hx⟩ := happ1 y hy
        exact ⟨x, fun p => by simpa using hx p⟩)
    obtain ⟨N, hN, hb⟩ := GlobalTheory.T.exists_nat_bound_localLattices_standard_ae A n Λ hfin fun p => GlobalTheory.T.local_lattice_between_scaled_standard_lattices A p n (Λ p) (hlat p) (h3 p)
    let Γ : Submodule (𝓞 E) (Fin n → E) :=
      { carrier := {x | ∀ p, A.bc p x ∈ Λ p}
        add_mem' := by
          intro x y hx hy p
          have : A.bc p (x + y) = A.bc p x + A.bc p y := by funext i; simp [Places.bc]
          rw [this]; exact (Λ p).add_mem (hx p) (hy p)
        zero_mem' := by
          intro p
          have : A.bc p (0 : Fin n → E) = 0 := by funext i; simp [Places.bc]
          rw [this]; exact (Λ p).zero_mem
        smul_mem' := by
          intro a x hx p
          have ha : (A.loc p).ιE (a : E) ∈ (A.L p).O := ιE_mem A p _ a.isIntegral_coe
          have : A.bc p (a • x) = (⟨_, ha⟩ : (A.L p).O) • A.bc p x := by
            funext i; simp [Places.bc, Subring.smul_def, Algebra.smul_def]; rfl
          rw [this]; exact (Λ p).smul_mem _ (hx p) }
    have hΓ : ∀ x, x ∈ Γ ↔ ∀ p, A.bc p x ∈ Λ p := fun x => Iff.rfl
    have hL : Submodule.IsLattice E Γ := by
      refine GlobalTheory.T.isLattice_of_squeezed_between_nat_multiples n Γ N hN (fun x hx p => ?_) (fun x hx i => ?_)
      · have : A.bc p ((N : E) • x) = (N : (A.loc p).Ep) • A.bc p x := by
          funext i; simp [Places.bc]
        rw [this]
        exact (hb p).1 _ fun i => ιE_mem A p _ (hx i)
      · refine GlobalTheory.T.isIntegral_of_integral_all_quadraticCompletions A _ fun p => ?_
        have := (hb p).2 _ (hx p) i
        simpa [Places.bc] using this
    refine ⟨Γ, hL, fun p => le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hx p)
    · haveI := (A.loc p).char0
      refine GlobalTheory.T.localLattice_le_completion_glued_lattice A n Λ Γ N hΓ (fun q => (hb q).1) ?_ p
      have hc : ∀ q, (N : (A.loc q).Fp) ≠ 0 := fun q => by
        haveI := (A.loc q).char0; exact_mod_cast hN
      have happN := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A (fun q => Units.mk0 _ (hc q))
        (by simpa using GlobalTheory.T.natCast_isUnit_quadraticCompletion_almost_all A N hN)).2.1
      intro y hy
      obtain ⟨x, hx⟩ := happN y hy
      exact ⟨x, fun q => by simpa using hx q⟩
  · rintro Γ₁ Γ₂ ⟨h1, e1⟩ ⟨h2, e2⟩
    ext x
    rw [(GlobalTheory.T.numberField_lattice_determined_by_local_lattices A n Γ₁ h1).1 x, (GlobalTheory.T.numberField_lattice_determined_by_local_lattices A n Γ₂ h2).1 x]
    simp only [e1, e2]

end GlobalTheory.HL.Glue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductParamsIntegralStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianEichlerProduct_params_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : IsHerm L Hm) (hI : ∀ i j, Hm i j ∈ L.O) (X Y u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (hX : ∀ i j, X i j ∈ L.O) (hY : ∀ i j, Y i j ∈ L.O) (hXY : ∀ a b, hf L Hm (X a) (Y b) = if a = b then 1 else 0) (hXX : ∀ a b, hf L Hm (X a) (X b) = 0) (hu : ∀ i, ∀ j, j ≤ i → hf L Hm (u i) (X j) = 0 ∧ hf L Hm (u i) (Y j) = 0) (hs : ∀ i, s i + L.cj (s i) = hf L Hm (u i) (u i)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (hn : ∀ x : Fin N → E, (∀ j, (List.ofFn e).prod x j ∈ L.O) ↔ ∀ j, x j ∈ L.O), (∀ i j, u i j ∈ L.O) ∧ ∀ i, s i ∈ L.O := by
  first | exact @GlobalTheory.HL.SAN.IntParam.eich_prod_params_int | exact GlobalTheory.HL.SAN.IntParam.eich_prod_params_int | (intros; apply GlobalTheory.HL.SAN.IntParam.eich_prod_params_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameCoordinatesTransportInnerLatticesStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrameCoordinates_transport_innerLattices : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), Function.Injective (c.inn P.A.f) ∧ (∀ L, P.A.IsInner L ↔ S.IsInner S.f S.es (c.inn P.A.f L)) ∧ (∀ A, S.IsInner S.f S.es A → ∃ L, A = c.inn P.A.f L) ∧ ∀ L, c.lat (P.A.LamStd L) = S.stdLat S.f S.es (c.inn P.A.f L) := by
  first | exact @GlobalTheory.HL.CoordInnerFst.transport | exact GlobalTheory.HL.CoordInnerFst.transport | (intros; apply GlobalTheory.HL.CoordInnerFst.transport <;> assumption)
end

