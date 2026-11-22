import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0042
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagTransitiveOfBase
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
section
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.AutLevel

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

theorem finEmb_eq_finGL (k : AdelicGLn.FiniteAdelicGL E a) :
    AutomorphicForm.finEmb E a k = finGL E a k := by
  apply (AdelicGLn.prodEquiv E a).injective
  rw [AutomorphicForm.prodEquiv_finEmb]
  have s1 : ∀ x, (sFin E x).1 = 0 := fun _ => rfl
  have s2 : ∀ x, (sFin E x).2 = x := fun _ => rfl
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · change (1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j =
      ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).1 -
        (sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)).1 + (sFin E (k i j)).1
    rw [s1, s1, sub_zero, add_zero]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
      rfl
  · change k.1 i j =
      ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).2 -
        (sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)).2 + (sFin E (k i j)).2
    rw [s2, s2]
    have h1 : ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).2 = (1 : Matrix (Fin a) (Fin a) (Af E)) i j := by
      by_cases h : i = j
      · subst h
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
        rfl
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
        rfl
    rw [h1, sub_self, zero_add]

theorem exists_open_level : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → (∃ U : Subgroup (AdelicGLn.integralFiniteGL E a), IsOpen (U : Set (AdelicGLn.integralFiniteGL E a)) ∧
    ∀ (g : AdelicGLn.AdelicGL E a) (u : U), φ.1 (g * AutomorphicForm.finEmb E a ((u : AdelicGLn.integralFiniteGL E a) : AdelicGLn.FiniteAdelicGL E a)) = φ.1 g) := by
  intro E _ _ _ a φ hφ
  let S : Subgroup (AdelicGLn.FiniteAdelicGL E a) :=
    { carrier := {k | finRep E a k φ = φ}
      mul_mem' := fun {x y} hx hy => by
        change finRep E a (x * y) φ = φ
        rw [map_mul, Module.End.mul_apply, hy, hx]
      one_mem' := by
        change finRep E a 1 φ = φ
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {x} hx => by
        change finRep E a x⁻¹ φ = φ
        have h : finRep E a x⁻¹ (finRep E a x φ) = φ := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [hx] at h }
  refine ⟨S.subgroupOf (AdelicGLn.integralFiniteGL E a), ?_, ?_⟩
  · exact hφ.level.preimage continuous_subtype_val
  · intro g u
    have hu : finRep E a ((u : AdelicGLn.integralFiniteGL E a) : AdelicGLn.FiniteAdelicGL E a) φ = φ :=
      Subgroup.mem_subgroupOf.1 u.2
    rw [finEmb_eq_finGL]
    exact congrArg (fun ψ : Sm E a => ψ.1 g) hu

end GlobalTheory.CompanionTheory.AutLevel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPositiveHermitianForm
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.TraceHerm

def toep {K : Type} [CommRing K] {n : ℕ} (M M' : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun j k => Matrix.trace (M ^ (k : ℕ) * M' ^ (j : ℕ))

theorem toep_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ} (f : K →+* L) (M M' : Matrix (Fin n) (Fin n) K) :
    (toep M M').map f = toep (M.map f) (M'.map f) := by
  ext j k
  simp only [toep, Matrix.map_apply, Matrix.of_apply]
  rw [← Matrix.map_pow, ← Matrix.map_pow, ← Matrix.map_mul]
  exact AddMonoidHom.map_trace f.toAddMonoidHom _

theorem pow_mul_eq {n : ℕ} {A T : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ} (h : A * T = T * diagonal z) (k : ℕ) :
    A ^ k * T = T * diagonal (fun i => z i ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h, Matrix.mul_assoc, diagonal_mul_diagonal]
    congr 2
    ext i
    rw [pow_succ']

theorem core {n : ℕ} (A A' T : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) (v : Fin n → ℂ) (hAA : A' * A = 1)
    (hT : A * T = T * diagonal z) (hv : v = T *ᵥ 1) (hz : ∀ i, ‖z i‖ = 1)
    (hB : (GlobalTheory.ClassParam.krylov A v).det ≠ 0) :
    (((GlobalTheory.ClassParam.krylov A v)⁻¹)ᴴ * toep A A' * (GlobalTheory.ClassParam.krylov A v)⁻¹).PosDef ∧
      Aᴴ * (((GlobalTheory.ClassParam.krylov A v)⁻¹)ᴴ * toep A A' * (GlobalTheory.ClassParam.krylov A v)⁻¹) * A =
        ((GlobalTheory.ClassParam.krylov A v)⁻¹)ᴴ * toep A A' * (GlobalTheory.ClassParam.krylov A v)⁻¹ := by
  set B := GlobalTheory.ClassParam.krylov A v with hBdef
  let V : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => z i ^ (k : ℕ)
  let zc : Fin n → ℂ := fun i => starRingEnd ℂ (z i)
  have hzz : ∀ i, z i * zc i = 1 := by
    intro i
    simp only [zc]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz i]
    simp
  have hDD : diagonal z * diagonal zc = 1 := by
    rw [diagonal_mul_diagonal]
    simp [hzz]
  have hBTV : B = T * V := by
    ext i k
    have h1 := pow_mul_eq hT (k : ℕ)
    have h2 : ((A ^ (k : ℕ)) *ᵥ v) = (T * diagonal (fun i => z i ^ (k : ℕ))) *ᵥ 1 := by
      rw [hv, Matrix.mulVec_mulVec, h1]
    simp only [hBdef, GlobalTheory.ClassParam.krylov, Matrix.of_apply]
    rw [h2]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, V, Matrix.diagonal_apply]
  have hdet : T.det * V.det ≠ 0 := by
    rw [← Matrix.det_mul, ← hBTV]; exact hB
  have hTd : IsUnit T.det := (isUnit_iff_ne_zero).2 (left_ne_zero_of_mul hdet)
  have hVd : IsUnit V.det := (isUnit_iff_ne_zero).2 (right_ne_zero_of_mul hdet)
  have hA' : A' * T = T * diagonal zc := by
    calc A' * T = A' * (T * (diagonal z * diagonal zc)) := by rw [hDD, Matrix.mul_one]
      _ = A' * A * T * diagonal zc := by
          rw [Matrix.mul_assoc A' A T, hT]; simp only [Matrix.mul_assoc]
      _ = T * diagonal zc := by rw [hAA, Matrix.one_mul]
  have hTT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hTd
  have hTT' : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ hTd
  have hG : toep A A' = Vᴴ * V := by
    ext j k
    have h1 : A ^ (k : ℕ) * A' ^ (j : ℕ) * T =
        T * diagonal (fun i => z i ^ (k : ℕ) * zc i ^ (j : ℕ)) := by
      rw [Matrix.mul_assoc, pow_mul_eq hA', ← Matrix.mul_assoc, pow_mul_eq hT, Matrix.mul_assoc,
        diagonal_mul_diagonal]
    have h2 : A ^ (k : ℕ) * A' ^ (j : ℕ) =
        T * (diagonal (fun i => z i ^ (k : ℕ) * zc i ^ (j : ℕ)) * T⁻¹) := by
      rw [← Matrix.mul_assoc, ← h1, Matrix.mul_assoc, hTT, Matrix.mul_one]
    simp only [toep, Matrix.of_apply]
    rw [h2, Matrix.trace_mul_comm, Matrix.mul_assoc, hTT', Matrix.mul_one, Matrix.trace_diagonal]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, Matrix.of_apply, zc]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have hQ : V * B⁻¹ = T⁻¹ := by
    rw [hBTV, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hVd, Matrix.one_mul]
  have hP : (B⁻¹)ᴴ * toep A A' * B⁻¹ = (T⁻¹)ᴴ * T⁻¹ := by
    rw [hG, ← hQ, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hP]
  have hQA : T⁻¹ * A = diagonal z * T⁻¹ := by
    calc T⁻¹ * A = T⁻¹ * A * (T * T⁻¹) := by rw [hTT, Matrix.mul_one]
      _ = T⁻¹ * (A * T) * T⁻¹ := by simp only [Matrix.mul_assoc]
      _ = diagonal z * T⁻¹ := by rw [hT, ← Matrix.mul_assoc, hTT', Matrix.one_mul]
  refine ⟨Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_), ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).2 (by rw [Matrix.det_nonsing_inv]; simpa using hTd)
  · have hDc : (diagonal z)ᴴ * diagonal z = 1 := by
      rw [Matrix.diagonal_conjTranspose, diagonal_mul_diagonal]
      have h1 : (fun i => (star z) i * z i) = fun _ => (1 : ℂ) :=
        funext fun i => by rw [Pi.star_apply, mul_comm]; exact hzz i
      rw [h1]
      exact diagonal_one
    calc Aᴴ * ((T⁻¹)ᴴ * T⁻¹) * A = (T⁻¹ * A)ᴴ * (T⁻¹ * A) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (T⁻¹)ᴴ * ((diagonal z)ᴴ * diagonal z) * T⁻¹ := by
          rw [hQA, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (T⁻¹)ᴴ * T⁻¹ := by rw [hDc, Matrix.mul_one]

theorem exists_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hs : A.charpoly.Separable) (v : Fin n → ℂ) :
    ∃ (T : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ),
      A * T = T * diagonal z ∧ v = T *ᵥ 1 ∧ ∀ i, z i ∈ A.charpoly.roots := by
  have hnd : A.charpoly.roots.Nodup := nodup_roots hs
  have hcard := splits_iff_card_roots.1 (IsAlgClosed.splits A.charpoly)
  have hdeg : A.charpoly.natDegree = n := by
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  set s := A.charpoly.roots.toFinset with hs_def
  have hsc : Fintype.card s = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnd, hcard, hdeg]
  let e := Fintype.equivFinOfCardEq hsc
  let z : Fin n → ℂ := fun a => ((e.symm a : s) : ℂ)
  have hprod : A.charpoly = ∏ a, (X - C (z a)) := by
    rw [Equiv.prod_comp e.symm (fun r : s => X - C (r : ℂ)), Finset.prod_coe_sort s (fun r => X - C r),
      Finset.prod_eq_multiset_prod, hs_def, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd,
      prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic _) hcard]
  have hch : (diagonal z).charpoly = A.charpoly := by rw [charpoly_diagonal, hprod]
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (M := diagonal z) (N := A)
    (by rw [GlobalTheory.Orb.IsRegSS, hch]; exact hs) hch.symm
  let w : Fin n → ℂ := ((x⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v
  refine ⟨(x : Matrix (Fin n) (Fin n) ℂ) * diagonal w, z, ?_, ?_, fun i => ?_⟩
  · rw [← Matrix.mul_assoc, hx, Matrix.mul_assoc, Matrix.mul_assoc, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 2
    ext i
    exact mul_comm _ _
  · have h1 : diagonal w *ᵥ (1 : Fin n → ℂ) = w := by
      ext i
      simp [Matrix.mulVec_diagonal]
    rw [← Matrix.mulVec_mulVec, h1]
    simp only [w]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
    simp
  · have : (e.symm i : ℂ) ∈ s := (e.symm i).2
    exact Multiset.mem_toFinset.1 this

theorem exists_posDef_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (N : GL (Fin n) E),
  N.val.charpoly.Separable → (∀ τ : E →+* ℂ, ∀ z ∈ (N.val.charpoly.map τ).roots, ‖z‖ = 1) →
  ∃ H : Matrix (Fin n) (Fin n) E, IsUnit H.det ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
    N ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H ∧ ∀ τ : E →+* ℂ, (H.map τ).PosDef := by
  intro E _ _ _ n N hs hr
  set c : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hc
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field N.val hs
  set B := GlobalTheory.ClassParam.krylov N.val v with hB
  set N' : Matrix (Fin n) (Fin n) E := ((N⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hN'
  have hN'N : N' * N.val = 1 := by
    rw [hN', ← Units.val_mul, inv_mul_cancel]; rfl
  have hcT : ∀ (τ : E →+* ℂ) (M : Matrix (Fin n) (Fin n) E), (cT c M).map τ = (M.map τ)ᴴ := by
    intro τ M
    ext i j
    simp only [cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    exact IsCMField.complexEmbedding_complexConj E τ (M j i)
  have hinv : ∀ τ : E →+* ℂ, (B⁻¹).map τ = (B.map τ)⁻¹ := by
    intro τ
    have h1 : (B⁻¹).map τ * B.map τ = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ ((isUnit_iff_ne_zero).2 hv)]
      simp
    exact (Matrix.inv_eq_left_inv h1).symm
  let H : Matrix (Fin n) (Fin n) E := cT c B⁻¹ * toep N.val N' * B⁻¹
  have hkey : ∀ τ : E →+* ℂ, (H.map τ).PosDef ∧ (N.val.map τ)ᴴ * H.map τ * N.val.map τ = H.map τ := by
    intro τ
    have hHτ : H.map τ = ((GlobalTheory.ClassParam.krylov (N.val.map τ) (τ ∘ v))⁻¹)ᴴ *
        toep (N.val.map τ) (N'.map τ) * (GlobalTheory.ClassParam.krylov (N.val.map τ) (τ ∘ v))⁻¹ := by
      simp only [H]
      rw [Matrix.map_mul, Matrix.map_mul, hcT, toep_map, hinv, hB, GlobalTheory.ClassParam.krylov_map]
    have hsτ : (N.val.map τ).charpoly.Separable := by
      rw [Matrix.charpoly_map]; exact hs.map
    obtain ⟨T, z, h1, h2, h3⟩ := exists_diag (N.val.map τ) hsτ (τ ∘ v)
    have hz : ∀ i, ‖z i‖ = 1 := fun i => hr τ (z i) (by rw [← Matrix.charpoly_map]; exact h3 i)
    have hdet : (GlobalTheory.ClassParam.krylov (N.val.map τ) (τ ∘ v)).det ≠ 0 := by
      rw [← GlobalTheory.ClassParam.krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero τ).2 hv
    rw [hHτ]
    exact core _ _ T z _ (by rw [← Matrix.map_mul, hN'N]; simp) h1 h2 hz hdet
  have hhermτ : ∀ τ : E →+* ℂ, (cT c H).map τ = H.map τ := fun τ => by
    rw [hcT]; exact (hkey τ).1.isHermitian.eq
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinj : Function.Injective (fun M : Matrix (Fin n) (Fin n) E => M.map τ₀) :=
    Matrix.map_injective τ₀.injective
  refine ⟨H, ?_, hinj (hhermτ τ₀), ?_, fun τ => (hkey τ).1⟩
  · have h := (hkey τ₀).1.det_pos.ne'
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
    exact (isUnit_iff_ne_zero).2 (fun h0 => h (by rw [h0, map_zero]))
  · change cT c N.val * H * N.val = H
    apply hinj
    simp only
    rw [Matrix.map_mul, Matrix.map_mul, hcT]
    exact (hkey τ₀).2

end GlobalTheory.CompanionTheory.TraceHerm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimOfAnnihilatingPolyEigenspaces
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.LinAlg

open Polynomial

theorem finiteDimensional_of_roots_of_eigenspaces {M : Type} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) (s : Multiset ℂ) :
    ∀ V : Submodule ℂ M, (∀ v ∈ V, T v ∈ V) →
      (∀ v ∈ V, aeval T ((s.map fun a => (X - C a : ℂ[X])).prod) v = 0) →
      (∀ c : ℂ, FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ V ∧ T v = c • v})) →
      FiniteDimensional ℂ V := by
  induction s using Multiset.induction_on with
  | empty =>
    intro V _ hker _
    have hbot : V = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      exact (Submodule.mem_bot ℂ).mpr (by simpa using hker v hv)
    subst hbot
    infer_instance
  | cons a s ih =>
    intro V hV hker hfin
    set f : Module.End ℂ M := aeval T (X - C a : ℂ[X]) with hf
    have hfv : ∀ v, f v = T v - a • v := by
      intro v
      simp [f]
    have hWV : ∀ w ∈ V.map f, w ∈ V := by
      rintro w ⟨v, hv, rfl⟩
      rw [hfv]
      exact V.sub_mem (hV v hv) (V.smul_mem a hv)
    have hW1 : ∀ w ∈ V.map f, T w ∈ V.map f := by
      rintro w ⟨v, hv, rfl⟩
      refine ⟨T v, hV v hv, ?_⟩
      simp [hfv, map_sub, map_smul]
    have hW2 : ∀ w ∈ V.map f,
        aeval T ((s.map fun b => (X - C b : ℂ[X])).prod) w = 0 := by
      rintro w ⟨v, hv, rfl⟩
      have h := hker v hv
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm, map_mul] at h
      exact h
    have hW3 : ∀ c : ℂ, FiniteDimensional ℂ
        (Submodule.span ℂ {v | v ∈ V.map f ∧ T v = c • v}) := by
      intro c
      haveI := hfin c
      have hsub : {v | v ∈ V.map f ∧ T v = c • v} ⊆ {v | v ∈ V ∧ T v = c • v} :=
        fun v hv => ⟨hWV v hv.1, hv.2⟩
      exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)
    have hWfin : FiniteDimensional ℂ (V.map f) := ih (V.map f) hW1 hW2 hW3
    apply Module.Finite.iff_fg.mpr
    apply Submodule.fg_of_fg_map_of_fg_inf_ker f
    · exact Module.Finite.iff_fg.mp hWfin
    · haveI := hfin a
      have hle : V ⊓ LinearMap.ker f ≤ Submodule.span ℂ {v | v ∈ V ∧ T v = a • v} := by
        rintro v ⟨hv, hk⟩
        apply Submodule.subset_span
        refine ⟨hv, ?_⟩
        have h0 : f v = 0 := hk
        rw [hfv, sub_eq_zero] at h0
        exact h0
      haveI := Submodule.finiteDimensional_of_le hle
      exact Module.Finite.iff_fg.mp inferInstance

theorem finiteDimensional_of_polynomial_of_eigenspaces :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (V : Submodule ℂ M),
      (∀ v ∈ V, T v ∈ V) → ∀ p : Polynomial ℂ, p ≠ 0 →
      (∀ v ∈ V, Polynomial.aeval T p v = 0) →
      (∀ c : ℂ, FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ V ∧ T v = c • v})) →
      FiniteDimensional ℂ V := by
  intro M _ _ T V hV p hp hker hfin
  have hsplit : p = C p.leadingCoeff * (p.roots.map fun a => (X - C a : ℂ[X])).prod := by
    first
      | exact Polynomial.eq_prod_roots_of_splits_id (IsAlgClosed.splits p)
      | exact (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
          (IsAlgClosed.card_roots_eq_natDegree (k := ℂ))).symm
  refine finiteDimensional_of_roots_of_eigenspaces T p.roots V hV ?_ hfin
  intro v hv
  have h := hker v hv
  rw [hsplit, map_mul, Polynomial.aeval_C] at h
  have h' : p.leadingCoeff • aeval T ((p.roots.map fun a => (X - C a : ℂ[X])).prod) v = 0 := by
    rw [← h, Algebra.algebraMap_eq_smul_one]
    rfl
  exact (smul_eq_zero.mp h').resolve_left (Polynomial.leadingCoeff_ne_zero.mpr hp)

end GlobalTheory.CompanionTheory.LinAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalKerSubId
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CompactFix

theorem finiteDimensional_ker_sub_id {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) (hT : IsCompactOperator T) :
    FiniteDimensional ℂ (LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id)) := by
  set K : Submodule ℂ X := LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id) with hK
  have hfix : ∀ x ∈ K, T x = x := by
    intro x hx
    have : (T : X →ₗ[ℂ] X) x - x = 0 := by simpa [hK] using hx
    simpa [sub_eq_zero] using this
  have hclosed : IsClosed (K : Set X) := by
    have : (K : Set X) = {x | T x = x} := by
      ext x
      constructor
      · exact hfix x
      · intro h
        have h' : T x = x := h
        simp [hK, h']
    rw [this]
    exact isClosed_eq T.continuous continuous_id
  obtain ⟨C, hC, hCsub⟩ := hT
  have hpre : (T ⁻¹' C) ∈ nhds (0 : X) := hCsub
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hpre
  have hcomp : IsCompact (Metric.closedBall (0 : K) r) := by
    have hemb : Topology.IsClosedEmbedding (Subtype.val : K → X) := hclosed.isClosedEmbedding_subtypeVal
    rw [hemb.isCompact_iff]
    refine hC.of_isClosed_subset ?_ ?_
    · have : (Subtype.val '' Metric.closedBall (0 : K) r) = (K : Set X) ∩ Metric.closedBall 0 r := by
        ext x
        simp [Metric.mem_closedBall, dist_eq_norm, and_comm]
      rw [this]
      exact hclosed.inter Metric.isClosed_closedBall
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : X) ∈ Metric.closedBall (0 : X) r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      have := hball hx'
      simpa [hfix x x.2] using this
  exact FiniteDimensional.of_isCompact_closedBall ℂ hr hcomp

end GlobalTheory.CompanionTheory.CompactFix
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFieldEmbeddingsDifferFrobenius
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem exists_frobenius_pow_of_ringHoms : ∀ {l : ℕ} [Fact l.Prime] {k D : Type} [Field k] [Finite k] [CommRing D] [IsDomain D] [CharP D l]
    (α β : k →+* D), ∃ i : ℕ, ∀ x, β x = α x ^ l ^ i := by
  intro l _ k D _ _ _ _ _ α β
  haveI : CharP k l := α.charP α.injective l
  exact GlobalTheory.ResidueChar.exists_pow_of_finite_field l α β

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceMinorHeightBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem absFin_minor_mul_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (v : Pl F) (X : GL ι (AE F E)) (κ : Matrix ι ι (AE F E))
    (hκ : ∀ i j, absFin F v (compFin F E v (κ i j)) ≤ 1) (f e : Fin n → ι) :
    absFin F v (compFin F E v ((X.1 * κ).submatrix f e).det) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
  have hent : ∀ i j, absFin F v (compFin F E v ((X.1 * κ) i j)) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) := by
    intro i j
    have h1 : compFin F E v ((X.1 * κ) i j) = ((X.1.map (compFin F E v)) * (κ.map (compFin F E v))) i j := by
      rw [← Matrix.map_mul]; rfl
    rw [h1]
    refine (absFin_le_normFin F v _ i j).trans ((normFin_mul_le F v _ _).trans ?_)
    have h2 : normFin F v (κ.map (compFin F E v)) ≤ 1 := (normFin_le_iff F v).2 fun a b => hκ a b
    exact (mul_le_of_le_one_right' h2).trans (le_htOf (normFin F v) (Formalism.UG.bc (compFin F E v) X))
  rw [RingHom.map_det, Matrix.det_apply]
  refine absFin_sum_le F v _ _ fun σ _ => ?_
  have hprod : absFin F v (∏ i : Fin n, ((compFin F E v).mapMatrix ((X.1 * κ).submatrix f e)) (σ i) i)
      ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
    calc _ ≤ ∏ i : Fin n, absFin F v (((compFin F E v).mapMatrix ((X.1 * κ).submatrix f e)) (σ i) i) :=
          Finset.le_prod_of_submultiplicative _ (absFin_one F v).le (absFin_mul_le F v) _ _
      _ ≤ ∏ _i : Fin n, htFin F v (Formalism.UG.bc (compFin F E v) X) :=
          Finset.prod_le_prod' fun i _ => hent _ _
      _ = _ := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hprod
  · rw [h, Units.neg_smul, one_smul, absFin_neg]; exact hprod

end GlobalTheory.CompanionTheory.GodementH
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagTransitiveOfBaseStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_transitive_of_base : ∀ {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R), IsHermRing c 𝔬 → HasBase c 𝔬 → FlagTransitive c 𝔬 := by
  first | exact @GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive | exact GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive | (intros; apply GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_section_growth_bound : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsCompact (K : Set (G2 σ Y)) → IsHgt K a → (∀ x, 0 < a x) → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ C : ℝ, ∀ (s : ℂ) (x : G2 σ Y), ‖flat a f s₁ s x‖ ≤ C * a x ^ (s.re + (n : ℝ) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow | exact GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow | (intros; apply GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameStabilizerFlagConverseStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_stabilizer_flag_converse : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (Qi * g * frm X Z Y).BlockTriangular (lev m S) → IsUnit (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) ∧ cT s (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) * J * (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) = J := by
  first | exact @GlobalTheory.CompanionTheory.CFin.BdU.bd_unitary | exact GlobalTheory.CompanionTheory.CFin.BdU.bd_unitary | (intros; apply GlobalTheory.CompanionTheory.CFin.BdU.bd_unitary <;> assumption)
end

