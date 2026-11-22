import Mathlib
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Topology

-- bundled from GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Anisotropic
section
set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology Metric

noncomputable section

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Form

variable (K) (H : Matrix ι ι E) (R : Type*) [CommRing R] [Algebra K R]

def hermValue (x : ι → R ⊗[K] E) : R ⊗[K] E :=
  (fun i => conjBase K E R (x i)) ⬝ᵥ (baseMatrix K H R *ᵥ x)

variable {K H R}

theorem hermValue_mulVec (g : unitaryPoints K E H R) (x : ι → R ⊗[K] E) :
    hermValue K H R (unitaryMat g *ᵥ x) = hermValue K H R x := by
  have hg : ((unitaryMat g).map (conjBase K E R))ᵀ * baseMatrix K H R * unitaryMat g =
      baseMatrix K H R := g.2
  have h1 : (fun i => conjBase K E R ((unitaryMat g *ᵥ x) i)) =
      (unitaryMat g).map (conjBase K E R) *ᵥ (fun i => conjBase K E R (x i)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  unfold hermValue
  rw [h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg, Matrix.dotProduct_mulVec]

theorem conjBase_smul (c : R) (z : R ⊗[K] E) :
    conjBase K E R (c • z) = c • conjBase K E R z :=
  map_smul (show R ⊗[K] E →ₐ[R] R ⊗[K] E from
    Algebra.TensorProduct.map (AlgHom.id R R) (conj K E).toAlgHom) c z

theorem hermValue_smul (c : R) (x : ι → R ⊗[K] E) :
    hermValue K H R (c • x) = (c * c) • hermValue K H R x := by
  unfold hermValue
  have : (fun i => conjBase K E R ((c • x) i)) = c • fun i => conjBase K E R (x i) := by
    funext i
    simp only [Pi.smul_apply, conjBase_smul]
  rw [this, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul]

end Form

section Compact

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable (H : Matrix ι ι E)
variable (R : Type*) [NontriviallyNormedField R] [ProperSpace R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

def anisoVecCoords (x : ι → R ⊗[K] E) : ι × κ → R :=
  fun p => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2

def anisoVecOfCoords (y : ι × κ → R) : ι → R ⊗[K] E :=
  fun i => (tensorCoordsHomeomorph R b).symm fun k => y (i, k)

variable {R b}

variable (R b)

def anisoForm (y : ι × κ → R) : κ → R :=
  tensorCoordsHomeomorph R b (hermValue K H R (anisoVecOfCoords R b y))

variable {H R b}

variable (H R)

end Compact

section RealPlace

open NumberField

variable (H : Matrix ι ι E)

abbrev completionNontriviallyNormedField (w : InfinitePlace K) :
    NontriviallyNormedField w.Completion :=
  { (inferInstance : NormedField w.Completion) with
    non_trivial := ⟨2, by
      have := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) 2
      rw [← this, map_ofNat]
      norm_num⟩ }

def IsHermDefiniteAt (w : InfinitePlace K) (hw : w.IsReal) : Prop :=
  (∀ x : ι → w.Completion ⊗[K] E, x ≠ 0 → ∃ t : w.Completion,
      hermValue K H w.Completion x = algebraMap w.Completion (w.Completion ⊗[K] E) t ∧
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw t) ∨
    ∀ x : ι → w.Completion ⊗[K] E, x ≠ 0 → ∃ t : w.Completion,
      hermValue K H w.Completion x = algebraMap w.Completion (w.Completion ⊗[K] E) t ∧
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hw t < 0

variable {H}

variable (H)

end RealPlace

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Lattice
section
set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

noncomputable section

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {R : Type*} [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

theorem repr_one_tmul (e : E) (m : κ) :
    (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ e) m = algebraMap K R (b.repr e m) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

theorem repr_mul (z w : R ⊗[K] E) (m : κ) :
    (Algebra.TensorProduct.basis R b).repr (z * w) m =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr z k *
        (Algebra.TensorProduct.basis R b).repr w l * algebraMap K R (b.repr (b k * b l) m) := by
  set B := Algebra.TensorProduct.basis R b
  conv_lhs => rw [← B.sum_repr z, ← B.sum_repr w]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, B,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_sum,
    map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    repr_one_tmul]
  exact Finset.sum_comm

variable (ι R) in

def stdLattice (O : Subring R) : Set (ι → R ⊗[K] E) :=
  {x | ∀ i k, (Algebra.TensorProduct.basis R b).repr (x i) k ∈ O}

variable (R) in

def latticeStabilizer (O : Subring R) : Subgroup (unitaryPoints K E H R) where
  carrier := {g | ∀ x ∈ stdLattice ι R b O, unitaryMat g *ᵥ x ∈ stdLattice ι R b O ∧
    unitaryMat g⁻¹ *ᵥ x ∈ stdLattice ι R b O}
  one_mem' x hx := by
    have h1 : unitaryMat (1 : unitaryPoints K E H R) = 1 := rfl
    simp only [inv_one, h1, Matrix.one_mulVec]
    exact ⟨hx, hx⟩
  mul_mem' {g h} hg hh x hx := by
    refine ⟨?_, ?_⟩
    · have : unitaryMat (g * h) = unitaryMat g * unitaryMat h := rfl
      rw [this, ← Matrix.mulVec_mulVec]
      exact (hg _ (hh x hx).1).1
    · have : unitaryMat (g * h)⁻¹ = unitaryMat h⁻¹ * unitaryMat g⁻¹ := by
        rw [_root_.mul_inv_rev]
        rfl
      rw [this, ← Matrix.mulVec_mulVec]
      exact (hh _ (hg x hx).2).2
  inv_mem' {g} hg x hx := by
    rw [inv_inv]
    exact ⟨(hg x hx).2, (hg x hx).1⟩

variable {H b}

variable (b) in

def IsAdapted (O : Subring R) : Prop :=
  (∀ k, algebraMap K R (b.repr 1 k) ∈ O) ∧ ∀ k l m, algebraMap K R (b.repr (b k * b l) m) ∈ O

theorem repr_mul_mem {O : Subring R} (hO : IsAdapted b O) {z w : R ⊗[K] E}
    (hz : ∀ k, (Algebra.TensorProduct.basis R b).repr z k ∈ O)
    (hw : ∀ k, (Algebra.TensorProduct.basis R b).repr w k ∈ O) (m : κ) :
    (Algebra.TensorProduct.basis R b).repr (z * w) m ∈ O := by
  rw [repr_mul]
  exact O.sum_mem fun k _ => O.sum_mem fun l _ =>
    O.mul_mem (O.mul_mem (hz k) (hw l)) (hO.2 k l m)

theorem single_one_mem_stdLattice {O : Subring R} (hO : IsAdapted b O) (j : ι) :
    (Pi.single j 1 : ι → R ⊗[K] E) ∈ stdLattice ι R b O := by
  intro i k
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, Algebra.TensorProduct.one_def, repr_one_tmul]
    exact hO.1 k
  · rw [Pi.single_eq_of_ne h, map_zero]
    exact O.zero_mem

theorem mulVec_mem_stdLattice {O : Subring R} (hO : IsAdapted b O) {M : Matrix ι ι (R ⊗[K] E)}
    (hM : ∀ i j k, (Algebra.TensorProduct.basis R b).repr (M i j) k ∈ O) {x : ι → R ⊗[K] E}
    (hx : x ∈ stdLattice ι R b O) : M *ᵥ x ∈ stdLattice ι R b O := by
  intro i k
  simp only [Matrix.mulVec, dotProduct, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact O.sum_mem fun j _ => repr_mul_mem hO (hM i j) (hx j) k

theorem mem_latticeStabilizer_iff {O : Subring R} (hO : IsAdapted b O)
    (g : unitaryPoints K E H R) :
    g ∈ latticeStabilizer H R b O ↔
      (∀ p, unitaryCoords H R b g p ∈ O) ∧ ∀ p, unitaryCoords H R b g⁻¹ p ∈ O := by
  constructor
  · intro hg
    refine ⟨fun ⟨i, j, k⟩ => ?_, fun ⟨i, j, k⟩ => ?_⟩
    · have := (hg _ (single_one_mem_stdLattice hO j)).1 i k
      rwa [Matrix.mulVec_single_one] at this
    · have := (hg _ (single_one_mem_stdLattice hO j)).2 i k
      rwa [Matrix.mulVec_single_one] at this
  · rintro ⟨h₁, h₂⟩ x hx
    exact ⟨mulVec_mem_stdLattice hO (fun i j k => h₁ (i, j, k)) hx,
      mulVec_mem_stdLattice hO (fun i j k => h₂ (i, j, k)) hx⟩

end

end GroundTheory.Automorphic
end

