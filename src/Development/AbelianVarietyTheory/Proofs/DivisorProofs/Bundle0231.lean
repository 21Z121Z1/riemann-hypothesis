import Mathlib
import GroundTheory.GlobalFields.TateThesis.LatticePoisson
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0170
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
import Formalism.SatakeDualWeyl.Statement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDualFourierExpansionSchwartz
section
open Module
open scoped RealInnerProductSpace FourierTransform SchwartzMap

namespace GlobalTheory

theorem schwartz_summable_norm_mul_one_add_pow {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (h : 𝓢(V, ℂ)) (N : ℕ) : Summable fun l : Λ => ‖h l‖ * (1 + ‖(l : V)‖) ^ N := by
  set k := finrank ℤ Λ + 1
  obtain ⟨C, hC, hg⟩ := GroundTheory.Global.exists_norm_le_inv_one_add_pow h (k + N)
  have hs : Summable fun l : Λ => C * ((1 + ‖l‖) ^ k)⁻¹ := by
    apply Summable.mul_left
    have hs := ZLattice.summable_norm_pow_inv (L := Λ) k (by omega)
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [(Set.finite_singleton (0 : Λ)).compl_mem_cofinite] with l hl
    have hpos : 0 < ‖l‖ := norm_pos_iff.mpr hl
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
    gcongr
    linarith
  refine hs.of_nonneg_of_le (fun _ => by positivity) fun l => ?_
  have hp : 0 < 1 + ‖(l : V)‖ := by positivity
  calc ‖h l‖ * (1 + ‖(l : V)‖) ^ N
      ≤ C * ((1 + ‖(l : V)‖) ^ (k + N))⁻¹ * (1 + ‖(l : V)‖) ^ N := by
        gcongr
        exact hg _
    _ = C * ((1 + ‖(l : V)‖) ^ k)⁻¹ := by
        rw [pow_add]
        field_simp
    _ = C * ((1 + ‖l‖) ^ k)⁻¹ := rfl

theorem periodisation_hasSum_fourier_bilinForm {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (hP : P.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : SchwartzMap V ℂ) :
    ∃ c : V → ℂ, (∀ N : ℕ, Summable (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        ‖c μ‖ * (1 + ‖(μ : V)‖) ^ N)) ∧
      ∀ x : V, HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) (∑' l : Λ, f (x + l)) := by
  let E := EuclideanSpace ℝ (Fin (finrank ℝ V))
  let T : E ≃L[ℝ] V := (toEuclidean (E := V)).symm
  let A₀ : V ≃ₗ[ℝ] E := (P.flip.toDual hP.flip) ≪≫ₗ T.toLinearEquiv.dualMap ≪≫ₗ
    (LinearMap.BilinForm.toDual (innerₗ E) GroundTheory.Global.innerₗ_nondegenerate).symm
  let A : V ≃L[ℝ] E := A₀.toContinuousLinearEquiv
  have hA : ∀ μ y, ⟪A μ, y⟫ = P (T y) μ := by
    intro μ y
    have h := LinearMap.BilinForm.toDual_def (B := innerₗ E) GroundTheory.Global.innerₗ_nondegenerate
      (m := A₀ μ) (n := y)
    have h2 : ⟪A μ, y⟫ = (innerₗ E) (A₀ μ) y := rfl
    rw [h2, ← h]
    simp only [A₀, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  let L : Submodule ℤ E := ZLattice.comap ℝ Λ T.toLinearMap
  haveI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ Λ T.toLinearMap))
  haveI : IsZLattice ℝ L := inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ Λ T.toLinearMap))
  have hL : ∀ y, y ∈ L ↔ T y ∈ Λ := fun y => Iff.rfl
  let g : 𝓢(E, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ T f
  have hg : ∀ y, g y = f (T y) := fun y => rfl
  let Λ' : Submodule ℤ V := ZLattice.comap ℝ (GroundTheory.Global.dualLattice L) A.toLinearMap
  haveI : DiscreteTopology Λ' :=
    inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (GroundTheory.Global.dualLattice L) A.toLinearMap))
  have hmem : ∀ μ : V, (∀ l ∈ Λ, ∃ k : ℤ, P l μ = k) ↔ A μ ∈ GroundTheory.Global.dualLattice L := by
    intro μ
    rw [GroundTheory.Global.mem_dualLattice]
    constructor
    · intro h y hy
      rw [hA]
      exact h _ ((hL y).mp hy)
    · intro h l hl
      have := h (T.symm l) ((hL _).mpr (by simpa using hl))
      rwa [hA, T.apply_symm_apply] at this
  let h : 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ A (𝓕 g)
  have hh : ∀ μ, h μ = 𝓕 (g : E → ℂ) (A μ) := fun μ => rfl
  refine ⟨fun μ => (ZLattice.covolume L)⁻¹ • h μ, fun N => ?_, fun x => ?_⟩
  · let e : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} ≃ Λ' := Equiv.subtypeEquivRight hmem
    have hs := (e.summable_iff.mpr
      (schwartz_summable_norm_mul_one_add_pow Λ' h N)).mul_left ‖(ZLattice.covolume L)⁻¹‖
    refine hs.congr fun μ => ?_
    rw [norm_smul, mul_assoc]
    rfl
  · let e : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} ≃ GroundTheory.Global.dualLattice L :=
      A.toEquiv.subtypeEquiv hmem
    let e' : L ≃ Λ := T.toEquiv.subtypeEquiv hL
    have hs := e.hasSum_iff.mpr
      (GroundTheory.Global.LatticePoisson.hasSum_smul_fourier (L := L) g (T.symm x))
    have hper : GroundTheory.Global.LatticePoisson.per L g (T.symm x) = ∑' l : Λ, f (x + l) := by
      rw [GroundTheory.Global.LatticePoisson.per, ← e'.tsum_eq]
      refine tsum_congr fun l => ?_
      rw [hg, map_add, T.apply_symm_apply]
      rfl
    rw [hper] at hs
    convert hs using 1
    funext μ
    have he : (e μ : E) = A μ := rfl
    simp only [Function.comp_apply, he, hA, T.apply_symm_apply, hh, Real.fourierChar_apply,
      smul_mul_assoc]
    congr 3
    push_cast
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRelativeLengthSmulEqRankMulValuation
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.ScalLen

theorem relLen_map_lsmul : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) →
    ∀ (X : Submodule (Int0 v) M), Module.Finite (Int0 v) X → ∀ (c : Int0 v) (r : ℝ),
      v (c : C) = r →
      RelLen v (X.map (LinearMap.lsmul (Int0 v) M c)) X ((finrank (Int0 v) X : ℝ) * r) := by
  intro C _ v M _ _ htf X hX c r hr
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hr
  haveI : Module.IsTorsionFree (Int0 v) X := ⟨fun s hs x y hxy => by
    have hs0 : s ≠ 0 := hs.ne_zero
    apply Subtype.ext
    have h1 : s • ((x : M) - (y : M)) = 0 := by
      rw [smul_sub]
      have := congrArg Subtype.val hxy
      simp only [Submodule.coe_smul] at this
      rw [this, sub_self]
    exact sub_eq_zero.1 (htf s _ hs0 h1)⟩
  haveI : Module.Free (Int0 v) X := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing _ _
  set n := finrank (Int0 v) X with hn
  let b : Basis (Fin n) (Int0 v) X := Module.finBasis _ _
  let g : X →ₗ[Int0 v] M := (LinearMap.lsmul (Int0 v) M c).comp X.subtype
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have h1 : c • ((x : M) - (y : M)) = 0 := by
      rw [smul_sub]
      simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.lsmul_apply] at hxy
      rw [hxy, sub_self]
    exact sub_eq_zero.1 (htf c _ hc h1)
  have hrange : LinearMap.range g = X.map (LinearMap.lsmul (Int0 v) M c) := by
    simp only [g, LinearMap.range_comp, Submodule.range_subtype]
  let e : X ≃ₗ[Int0 v] X.map (LinearMap.lsmul (Int0 v) M c) :=
    (LinearEquiv.ofInjective g hg).trans (LinearEquiv.ofEq _ _ hrange)
  refine ⟨n, b, b.map e, Matrix.diagonal (fun _ => c), fun k => ?_, ?_⟩
  · simp only [Basis.map_apply, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Subring.coe_pow, AddValuation.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]

end GlobalTheory.ScalLen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulEigenspaceFinrankOne
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory.RegEigen

theorem eig_leftMulMatrix_finrank : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ) (b : Module.Basis (Fin n) R Λ) (φ : R →+* O) (τ : Λ →+* O), τ.comp (algebraMap R Λ) = φ → Module.finrank C (eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ) = 1 := by
  intro C _ O _ _ R Λ _ _ _ n b φ τ hτ
  set ψ : R →+* C := (algebraMap O C).comp φ with hψ
  let f : (Fin n → C) → Λ → C := fun w x => ∑ i, ψ (b.repr x i) * w i
  have f_add : ∀ w x y, f w (x + y) = f w x + f w y := by
    intro w x y; simp [f, map_add, add_mul, Finset.sum_add_distrib]
  have f_smul : ∀ w (r : R) x, f w (r • x) = ψ r * f w x := by
    intro w r x; simp [f, map_mul, Finset.mul_sum, mul_assoc]
  have f_basis : ∀ w j, f w (b j) = w j := by
    intro w j; simp [f, Finsupp.single_apply]
  have f_sum : ∀ w (g : Fin n → Λ), f w (∑ i, g i) = ∑ i, f w (g i) := by
    intro w g
    exact map_sum (AddMonoidHom.mk' (f w) (f_add w)) g Finset.univ
  have mem : ∀ w, w ∈ eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ ↔
      ∀ a i, f w (a * b i) = algebraMap O C (τ a) * w i := by
    intro w
    simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, funext_iff]
    refine forall_congr' fun a => forall_congr' fun i => ?_
    simp [f, Matrix.mulVec, dotProduct, Algebra.leftMulMatrix_eq_repr_mul, hψ]
  have hτ' : ∀ r, τ (algebraMap R Λ r) = φ r := fun r => by rw [← hτ]; rfl
  set w0 : Fin n → C := fun i => algebraMap O C (τ (b i)) with hw0
  have f_w0 : ∀ x, f w0 x = algebraMap O C (τ x) := by
    intro x
    conv_rhs => rw [← b.sum_repr x]
    simp [f, hw0, map_sum, Algebra.smul_def, hτ', hψ]
  have f_mul : ∀ w, (∀ a i, f w (a * b i) = algebraMap O C (τ a) * w i) →
      ∀ a x, f w (a * x) = algebraMap O C (τ a) * f w x := by
    intro w h a x
    conv_lhs => rw [← b.sum_repr x, Finset.mul_sum]
    rw [f_sum]
    simp_rw [mul_smul_comm, f_smul, h a]
    simp only [f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have cmHalfIntegralGenerator_mem_algebraicClosure : w0 ∈ eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ := by
    rw [mem]; intro a i; rw [f_w0]; simp [hw0]
  have w0_ne : w0 ≠ 0 := by
    intro h0
    have := f_w0 1
    rw [h0] at this
    simp [f] at this
  have heq : eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ = Submodule.span C {w0} := by
    apply le_antisymm
    · intro w hw
      rw [Submodule.mem_span_singleton]
      refine ⟨f w 1, funext fun i => ?_⟩
      have h := f_mul w ((mem w).1 hw) (b i) 1
      rw [mul_one, f_basis] at h
      simp [hw0, h, mul_comm]
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact cmHalfIntegralGenerator_mem_algebraicClosure
  rw [heq, finrank_span_singleton w0_ne]

end GlobalTheory.RegEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulMatrixRingHomTrace
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem transposedRegularRep_ringHom_trace :
    ∀ (O : Type) [CommRing O] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ)
      (b : Module.Basis (Fin n) R Λ) (φ : R →+* O),
      (∃ ρ : Λ →+* Matrix (Fin n) (Fin n) O,
        ⇑ρ = fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) ∧
      ∀ a : Λ, (((Algebra.leftMulMatrix b a).transpose).map φ).trace
        = φ (Algebra.trace R Λ a) := by
  intro O _ R Λ _ _ _ n b φ
  refine ⟨⟨{ toFun := fun a => ((Algebra.leftMulMatrix b a).transpose).map φ
             map_one' := ?_
             map_mul' := ?_
             map_zero' := ?_
             map_add' := ?_ }, rfl⟩, ?_⟩
  · rw [map_one, Matrix.transpose_one]
    exact Matrix.map_one φ (map_zero φ) (map_one φ)
  · intro x y
    rw [mul_comm x y, map_mul, Matrix.transpose_mul, Matrix.map_mul]
  · ext i j
    simp
  · intro x y
    rw [map_add, Matrix.transpose_add]
    ext i j
    simp
  · intro a
    rw [Algebra.trace_eq_matrix_trace b a, ← Matrix.trace_transpose (Algebra.leftMulMatrix b a)]
    simp [Matrix.trace, map_sum]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthCokerLsmulEqLengthKerAddSumStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_coker_lsmul_eq_length_ker_add_sum' : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A)), (∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M], (∀ p ∈ Module.support A M, p ∈ P ∨ p.asIdeal = IsLocalRing.maximalIdeal A) → Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧ Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) + ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) := by
  first | exact @GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum | exact GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum | (intros; apply GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenSublatticeIffEvalFlat
section
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory

theorem lie_eigenSub_iff_flat : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → Function.Injective (evalVec (liftA hv a) N) → (∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) → (∀ x, x ∈ filPre (liftA hv a) F ↔ evalVec (liftA hv a) N x ∈ F) → (∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F) → ∀ z : (Fin N → C) ⧸ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) F) τ ↔ ∃ x : Fin N → RS (liftA hv a), proj (liftA hv a) (filPre (liftA hv a) F) x ∈ eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ filPre (liftA hv a) F) ∧ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.quotMap (w := w) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ) (fun i => ((comp (liftA hv a) N τ x i : Int0 v) : C)) = z := by
  intro C _ w v hv S _ _ a N F τ hinj _hfilt _hevinj hrange hmem hlast z
  have hev : ∀ x : Fin N → RS (liftA hv a), ∀ s i,
      evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s i
        = ((a s : C) - a τ) * evalVec (liftA hv a) N x s i := by
    intro x s i
    simp only [evalVec, Pi.smul_apply, smul_eq_mul, map_mul, ev_lin]
    rfl
  have hevs : ∀ x : Fin N → RS (liftA hv a), ∀ s,
      evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s
        = ((a s : C) - a τ) • evalVec (liftA hv a) N x s := by
    intro x s; funext i; rw [hev]; rfl
  have heig : ∀ x : Fin N → RS (liftA hv a),
      proj (liftA hv a) (filPre (liftA hv a) F) x ∈
          eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ filPre (liftA hv a) F) ↔
        evalVec (liftA hv a) N (lin (liftA hv a) τ • x) ∈ F := by
    intro x
    rw [← hmem]
    show lin (liftA hv a) τ • (filPre (liftA hv a) F).mkQ x = 0 ↔ _
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hlie : z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub
        (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) F) τ ↔
      ∃ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, ∀ s,
        (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s).mkQ (h s) =
          (Pi.single τ z : ∀ s, (Fin N → C) ⧸ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) s := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie, Submodule.mem_comap,
      Submodule.mem_map]
    constructor
    · rintro ⟨h, hh, he⟩
      exact ⟨h, hh, fun s => congrFun he s⟩
    · rintro ⟨h, hh, he⟩
      exact ⟨h, hh, funext he⟩
  rw [hlie]
  constructor
  · rintro ⟨h, hh, he⟩
    obtain ⟨x, rfl⟩ := (hrange h).1 hh
    refine ⟨x, (heig x).2 ?_, ?_⟩
    · apply hlast _ ((hrange _).2 ⟨_, rfl⟩)
      intro s
      rw [hevs]
      by_cases hs : s = τ
      · rw [hs, sub_self, zero_smul]; exact zero_mem _
      · have h1 : evalVec (liftA hv a) N x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s := by
          have := he s
          rw [Pi.single_eq_of_ne hs, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
          exact this
        exact Submodule.smul_mem _ _ h1
    · have := he τ
      rw [Pi.single_eq_same] at this
      exact this
  · rintro ⟨x, hx, rfl⟩
    refine ⟨evalVec (liftA hv a) N x, (hrange _).2 ⟨x, rfl⟩, fun s => ?_⟩
    by_cases hs : s = τ
    · subst hs
      rw [Pi.single_eq_same]
      rfl
    · rw [Pi.single_eq_of_ne hs, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      have hy := (heig x).1 hx
      have hys : evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s ∈
          GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s :=
        Submodule.subset_span ⟨_, hy, rfl⟩
      have hne : (a s : C) - a τ ≠ 0 := sub_ne_zero.2 fun e => hs (hinj (Subtype.ext e))
      have : evalVec (liftA hv a) N x s =
          ((a s : C) - a τ)⁻¹ • evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s := by
        rw [hevs, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hys

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsToLatticeOfFiniteInvertibleStabilisersStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_forms_to_lattice_of_finite_invertible_stabilisers : ∀ (O : Type) [CommRing O] (G : Type) [Group G] (Γ K : Subgroup G) (B Q : Type) [AddCommGroup B] [Module O B] [AddCommGroup Q] [Module O Q] (ρ : Representation O K B) (π : B →ₗ[O] Q), Function.Surjective π → (∀ κ x, π x = 0 → π (ρ κ x) = 0) → (∀ g : G, Finite {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} ∧ IsUnit ((Nat.card {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} : ℕ) : O)) → ∀ f : G → Q, (∀ (γ : Γ) (g : G) (κ : K) (y : B), f g = π y → f ((γ : G) * g * κ) = π (ρ κ⁻¹ y)) → ∃ F ∈ Formalism.UG.AMFK O Γ K ρ, ∀ g, π (F g) = f g := by
  first | exact @GlobalTheory.lift_forms_of_card_isUnit | exact GlobalTheory.lift_forms_of_card_isUnit | (intros; apply GlobalTheory.lift_forms_of_card_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRingHomAffineOpenOfArtinianSchemeLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_ringHom_affine_open_of_artinian_scheme_lift : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → ∀ (U : (Sp B).Opens), IsAffineOpen U → ∀ (V : X.Opens), IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : Γ(Sp B, U) →+* C) (φ₀ : Γ(X, V) →+* C₀), φ₀.comp ((s.appLE U V e).hom) = π.comp β → ∃ φ : Γ(X, V) →+* C, π.comp φ = φ₀ ∧ φ.comp ((s.appLE U V e).hom) = β) := by
  first | exact @GlobalTheory.lift_ringHom_of_scheme_lift | exact GlobalTheory.lift_ringHom_of_scheme_lift | (intros; apply GlobalTheory.lift_ringHom_of_scheme_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSquarePresentationOfFlat
section
open scoped TensorProduct

namespace GlobalTheory

theorem lift_square_presentation_of_flat : ∀ (O B A k H σ : Type) [CommRing O] [IsLocalRing O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Module.Flat B A] [Field k] [CommRing H] [Algebra k H] [Fintype σ] (ε : A →ₐ[O] O) (π : O →+* k) (ρ : A →+* H) (εH : H →ₐ[k] k) (x : σ → A), Function.Surjective π → RingHom.ker π = IsLocalRing.maximalIdeal O → (∀ c : O, ρ (algebraMap O A c) = algebraMap k H (π c)) → (∀ a, εH (ρ a) = π (ε a)) → RingHom.ker ρ = (RingHom.ker (π.comp ((ε : A →+* O).comp (algebraMap B A)))).map (algebraMap B A) → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A)).FG → ∀ g : σ → MvPolynomial σ k, (∀ i, MvPolynomial.aeval (fun j => ρ (x j)) (g i) = 0) → RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (εH.comp (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H)) * RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) → ∃ f : σ → MvPolynomial σ B, (∀ i, MvPolynomial.aeval x (f i) = 0) ∧ RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) := by
  intro O B A k H σ _ _ _ _ _ _ _ _ _ _ _ _ _ ε π ρ εH x hπ hker hρO hε hρ hx hfg g hg hJ
  classical
  set τ : B →+* k := π.comp ((ε : A →+* O).comp (algebraMap B A)) with hτ
  have hτb : ∀ b, τ b = π (ε (algebraMap B A b)) := fun b => rfl
  have hτO : ∀ c, τ (algebraMap O B c) = π c := by
    intro c
    rw [hτb, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
    rfl
  have hτs : Function.Surjective τ := by
    intro y
    obtain ⟨c, rfl⟩ := hπ y
    exact ⟨_, hτO c⟩
  have hρB : ∀ b, ρ (algebraMap B A b) = algebraMap k H (τ b) := by
    intro b
    have h1 : b - algebraMap O B (ε (algebraMap B A b)) ∈ RingHom.ker τ := by
      rw [RingHom.mem_ker, map_sub, hτO, hτb, sub_self]
    have h2 : algebraMap B A (b - algebraMap O B (ε (algebraMap B A b))) ∈ RingHom.ker ρ := by
      rw [hρ]
      exact Ideal.mem_map_of_mem _ h1
    rw [RingHom.mem_ker, map_sub, map_sub, ← IsScalarTower.algebraMap_apply, hρO,
      sub_eq_zero] at h2
    rw [h2, hτb]
  set Ψ : MvPolynomial σ B →ₐ[B] A := MvPolynomial.aeval x with hΨ
  set Φ : MvPolynomial σ k →ₐ[k] H := MvPolynomial.aeval (fun j => ρ (x j)) with hΦ
  set T : MvPolynomial σ B →+* MvPolynomial σ k := MvPolynomial.map τ with hT
  have hcomm : ∀ F, ρ (Ψ F) = Φ (T F) := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp [hΨ, hΦ, hT, hρB]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp]
      simp [hΨ, hΦ, hT]
  have hTs : Function.Surjective T := MvPolynomial.map_surjective τ hτs
  have hTk : RingHom.ker T = (RingHom.ker τ).map (algebraMap B (MvPolynomial σ B)) :=
    MvPolynomial.ker_map τ
  have hlift : ∀ G, Φ G = 0 → ∃ F, Ψ F = 0 ∧ T F = G := by
    intro G hG
    obtain ⟨F0, rfl⟩ := hTs G
    have h1 : Ψ F0 ∈ ((RingHom.ker τ).map (algebraMap B (MvPolynomial σ B))).map
        (Ψ : MvPolynomial σ B →+* A) := by
      rw [Ideal.map_map, AlgHom.comp_algebraMap, ← hρ, RingHom.mem_ker, hcomm, hG]
    rw [Ideal.mem_map_iff_of_surjective (Ψ : MvPolynomial σ B →+* A) hx] at h1
    obtain ⟨F1, hF1, hF⟩ := h1
    rw [← hTk, RingHom.mem_ker] at hF1
    refine ⟨F0 - F1, ?_, ?_⟩
    · rw [map_sub, sub_eq_zero]
      exact hF.symm
    · rw [map_sub, hF1, sub_zero]
  choose f hf hfT using fun i => hlift (g i) (hg i)
  refine ⟨f, hf, ?_⟩
  let η : MvPolynomial σ B →ₐ[O] O := ε.comp (Ψ.restrictScalars O)
  have hη : ∀ F, η F = ε (Ψ F) := fun F => rfl
  have hn : ∀ F, F ∈ (IsLocalRing.maximalIdeal O).comap η ↔ εH (Φ (T F)) = 0 := by
    intro F
    rw [Ideal.mem_comap, ← hker, RingHom.mem_ker, ← hcomm, hε, hη]
  have key : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔
      (IsLocalRing.maximalIdeal O).comap η * RingHom.ker Ψ := by
    have hle : Ideal.span (Set.range g) ⊔ RingHom.ker (εH.comp Φ) * RingHom.ker Φ ≤
        (Ideal.span (Set.range f) ⊔
          (IsLocalRing.maximalIdeal O).comap η * RingHom.ker Ψ).map T := by
      rw [Ideal.map_sup, Ideal.map_mul]
      refine sup_le_sup ?_ (Ideal.mul_mono ?_ ?_)
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        rw [← hfT i]
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
      · intro G hG
        obtain ⟨F, rfl⟩ := hTs G
        exact Ideal.mem_map_of_mem _ ((hn F).2 hG)
      · intro G hG
        obtain ⟨F, hF, rfl⟩ := hlift G hG
        exact Ideal.mem_map_of_mem _ hF
    have hS : Ideal.span (Set.range f) ⊔
        (IsLocalRing.maximalIdeal O).comap η * RingHom.ker Ψ ≤ RingHom.ker Ψ := by
      refine sup_le ?_ Ideal.mul_le_right
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hf i
    have hp : (RingHom.ker τ).map (algebraMap B (MvPolynomial σ B)) ≤
        (IsLocalRing.maximalIdeal O).comap η := by
      rw [← hTk]
      intro F hF
      rw [hn, (RingHom.mem_ker).1 hF, map_zero, map_zero]
    intro F hF
    have h1 : T F ∈ RingHom.ker Φ := by
      rw [RingHom.mem_ker, ← hcomm, (RingHom.mem_ker).1 hF, map_zero]
    obtain ⟨F1, hF1, hF'⟩ := (Ideal.mem_map_iff_of_surjective T hTs).1 (hle (hJ h1))
    have h2 : F - F1 ∈ RingHom.ker Ψ ⊓
        (RingHom.ker τ).map (algebraMap B (MvPolynomial σ B)) := by
      refine ⟨sub_mem hF (hS hF1), ?_⟩
      rw [← hTk]
      show T (F - F1) = 0
      rw [map_sub, hF', sub_self]
    have h3 := Ideal.mul_mono_left hp
      (GlobalTheory.T.ker_inf_map_le_map_mul_ker_of_flat_target B (MvPolynomial σ B) A Ψ hx (RingHom.ker τ) h2)
    have h4 : F = F1 + (F - F1) := by ring
    rw [h4]
    exact add_mem hF1 (Ideal.mem_sup_right h3)
  exact GlobalTheory.T.le_sup_ker_mul_of_le_sup_maximal_mul_section O (MvPolynomial σ B) η _ _ hfg key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalDomainUnfoldRefoldMeasureStatement
section
open MeasureTheory
open scoped ENNReal Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_fundamentalDomain_unfold_refold_measure : ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (Γ : Subgroup S) [Countable Γ] (D₁ D₂ : Set X), MeasurableSet D₁ → IsFundamentalDomain Γ D₂ μ → ∀ (E : Set S), MeasurableSet E → IsFundamentalDomain Γ E ν → ∀ (ψ : X → ℝ≥0∞), Measurable ψ → (∀ (s : S) (x : X), ψ (s • x) = ψ x) → ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) ∂μ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ := by
  first | exact @GlobalTheory.CovolIndep.lintegral_unfold_refold | exact GlobalTheory.CovolIndep.lintegral_unfold_refold | (intros; apply GlobalTheory.CovolIndep.lintegral_unfold_refold <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMulMeasureInterSmulPreimageOfInvariantStatement
section
open MeasureTheory
open scoped ENNReal Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_mul_measure_inter_smul_preimage_of_invariant : ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (D : Set X), MeasurableSet D → ∀ (E : Set S), MeasurableSet E → ∀ (ψ : X → ℝ≥0∞), Measurable ψ → (∀ (s : S) (x : X), ψ (s • x) = ψ x) → ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ := by
  first | exact @GlobalTheory.lintegral_mul_measure_inter_smul_preimage | exact GlobalTheory.lintegral_mul_measure_inter_smul_preimage | (intros; apply GlobalTheory.lintegral_mul_measure_inter_smul_preimage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationIsDomainIsIntegrallyClosedOfFinsetSuStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_isIntegrallyClosed_atPrime_of_finset_subrings : ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring | exact GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring | (intros; apply GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring <;> assumption)
end

