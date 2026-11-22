import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0008
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0005
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0004

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.IntegralBlockMatrixIff
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {D : D7}

def IntM {D : D7} {m p : ℕ} (v : Pl D) (M : Mx D m p) : Prop := ∀ i j, cv D v (M i j) ∈ intLoc D.host.F D.host.E v

namespace IntM

variable {v : Pl D} {m p q : ℕ}

theorem add {M N : Mx D m p} (hM : IntM v M) (hN : IntM v N) : IntM v (M + N) := fun i j => by
  rw [Matrix.add_apply, map_add]; exact add_mem (hM i j) (hN i j)

theorem neg {M : Mx D m p} (hM : IntM v M) : IntM v (-M) := fun i j => by
  rw [Matrix.neg_apply, map_neg]; exact neg_mem (hM i j)

theorem zero : IntM v (0 : Mx D m p) := fun i j => by
  rw [Matrix.zero_apply, map_zero]; exact zero_mem _

theorem one : IntM v (1 : Mx D m m) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · rw [map_one]; exact one_mem _
  · rw [map_zero]; exact zero_mem _

theorem mul {M : Mx D m p} {N : Mx D p q} (hM : IntM v M) (hN : IntM v N) : IntM v (M * N) := fun i j => by
  rw [Matrix.mul_apply, map_sum]
  exact sum_mem fun k _ => by rw [map_mul]; exact mul_mem (hM i k) (hN k j)

theorem inv {M : Mx D m m} (hM : IntM v M) (hu : IsUnit M.det)
    (hdet : ∃ z ∈ intLoc D.host.F D.host.E v, cv D v M.det * z = 1) : IntM v M⁻¹ := by
  obtain ⟨z, hz, hdz⟩ := hdet
  obtain ⟨u, hu'⟩ := hu
  have hinv : cv D v (Ring.inverse M.det) = z := by
    rw [← hu', Ring.inverse_unit]
    have h1 : cv D v ((u⁻¹ : (AE D)ˣ) : AE D) * cv D v (u : AE D) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hu'] at h1
    calc cv D v ((u⁻¹ : (AE D)ˣ) : AE D) = cv D v ((u⁻¹ : (AE D)ˣ) : AE D) * (cv D v M.det * z) := by
          rw [hdz, mul_one]
      _ = z := by rw [← mul_assoc, h1, one_mul]

  let N : Matrix (Fin m) (Fin m) (intLoc D.host.F D.host.E v) := fun i j => ⟨cv D v (M i j), hM i j⟩
  have hN : N.map (intLoc D.host.F D.host.E v).subtype = M.map (cv D v) := rfl
  have hadj : ∀ i j, cv D v (M.adjugate i j) ∈ intLoc D.host.F D.host.E v := by
    intro i j
    have e1 : cv D v (M.adjugate i j) = (M.map (cv D v)).adjugate i j :=
      congrFun (congrFun (RingHom.map_adjugate (cv D v) M) i) j
    have e2 : (intLoc D.host.F D.host.E v).subtype (N.adjugate i j) =
        (N.map (intLoc D.host.F D.host.E v).subtype).adjugate i j :=
      congrFun (congrFun (RingHom.map_adjugate (intLoc D.host.F D.host.E v).subtype N) i) j
    rw [e1, ← hN, ← e2]
    exact (N.adjugate i j).2
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, hinv]
  exact mul_mem hz (hadj i j)

end IntM

theorem integral_block_matrix_iff {v : Pl D} {n : ℕ} {a b c d : Mx D n n} :
    IntM v (blk4 a b c d) ↔ IntM v a ∧ IntM v b ∧ IntM v c ∧ IntM v d := by
  have key : ∀ x y, blk4 a b c d (finSumFinEquiv x) (finSumFinEquiv y) = Matrix.fromBlocks a b c d x y := by
    intro x y; simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · have := h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
      rwa [key, Matrix.fromBlocks_apply₁₁] at this
    · have := h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))
      rwa [key, Matrix.fromBlocks_apply₁₂] at this
    · have := h (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j))
      rwa [key, Matrix.fromBlocks_apply₂₁] at this
    · have := h (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j))
      rwa [key, Matrix.fromBlocks_apply₂₂] at this
  · rintro ⟨ha, hb, hc, hd⟩ i j
    obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    show cv D v (blk4 a b c d _ _) ∈ _
    rw [key]
    rcases i' with i' | i' <;> rcases j' with j' | j'
    · rw [Matrix.fromBlocks_apply₁₁]; exact ha i' j'
    · rw [Matrix.fromBlocks_apply₁₂]; exact hb i' j'
    · rw [Matrix.fromBlocks_apply₂₁]; exact hc i' j'
    · rw [Matrix.fromBlocks_apply₂₂]; exact hd i' j'

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LBumpEx
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace PositivityTheory.Rg.Rsw.L.LBumpEx

variable {D : D7}

theorem theta_e (θ : InfFam D) (hθ : IsInfFam θ) {e : AE D} (he : ∀ w, compInf D.host.F D.host.E w e = 1)
    (τ : D.what₂.Tau) : θ τ (infPart D e) = 1 := by
  have h := ((GlobalTheory.StdUnn.RealComp.real_components D θ hθ).1 (e - 1)).1
    (fun w => by rw [map_sub, map_one, he w, sub_self])
  have h' := h τ
  rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h'
  exact h'

end PositivityTheory.Rg.Rsw.L.LBumpEx

open PositivityTheory.Rg.Rsw.L.LBumpEx Classical in
theorem PositivityTheory.Rg.Rsw.L.bumpEx : IdemEx → BumpEx := by
  intro hI D θ hθ a b S e he C hC hCi
  obtain ⟨hee, -⟩ := (hI D S).2 e he
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨hom⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have : T2Space (AE D) := hom.isEmbedding.t2Space
  set ef : AfE D := finPart D e with hef_def
  have hef : ef * ef = ef := by rw [hef_def, ← map_mul, hee]
  have hefI : ef ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D ef hef
  have hS : ∀ v : Pl D, PositivityTheory.Rg.Rsw.L.LBumpEx.cf v ef = if v ∈ S then 1 else 0 := fun v => by
    rw [← cv_eq]; exact he.2 v
  have hθe := theta_e θ hθ he.1
  obtain ⟨N, hN, hNC⟩ := exists_nat_mul_mem (D := D)
    (Q := ⋃ i, ⋃ j, (fun x : Mx D a b => ef * finPart D (x i j)) '' C)
    (isCompact_iUnion fun i => isCompact_iUnion fun j => hC.image
      (continuous_const.mul ((GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j))))
  let W := U S ef N 1 b
  have hWo : IsOpen (W : Set (Matrix (Fin 1) (Fin b) (AfE D))) := U_isOpen hefI N 1 b
  have hWc : IsCompact (W : Set (Matrix (Fin 1) (Fin b) (AfE D))) := U_isCompact hefI hS hN 1 b
  let g : Matrix (Fin 1) (Fin b) (AfE D) → ℂ := fun w =>
    if (QuotientAddGroup.mk w : _ ⧸ W) = 0 then 1 else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin b → AfE D) := GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  have hg1 : ∀ w, g w = if w ∈ W then 1 else 0 := fun w => by
    simp only [g, QuotientAddGroup.eq_zero_iff]
  let rc : Mx D 1 b → (D.what₂.Tau → Fin 1 → Fin b → ℂ) := fun y τ i j => compAt θ τ y i j
  have hrc : Continuous rc := continuous_pi fun τ => GlobalTheory.RealWeil.continuous_compAt hθ τ 1 b
  have hK : IsCompact (⋃ i, (fun x : Mx D a b => rc (x.submatrix (fun _ : Fin 1 => i) id)) '' C) :=
    isCompact_iUnion fun i => hC.image (hrc.comp (continuous_id.matrix_submatrix _ _))
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  let bump : ContDiffBump (0 : D.what₂.Tau → Fin 1 → Fin b → ℂ) :=
    ⟨max R 1, max R 1 + 1, lt_max_of_lt_right one_pos, by linarith⟩
  have hc : HasCompactSupport fun y => ((bump y : ℝ) : ℂ) :=
    bump.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  let f : SchwartzMap (D.what₂.Tau → Fin 1 → Fin b → ℂ) ℂ :=
    hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp bump.contDiff)
  have hf : ∀ y, f y = ((bump y : ℝ) : ℂ) := fun y => rfl
  let η₀ : Mx D 1 b → ℂ := fun y => f (fun τ i j => compAt θ τ y i j) * g (fun i j => finPart D (y i j))
  have hη : ∀ y, η₀ y = ((bump (rc y) : ℝ) : ℂ) *
      (if (Matrix.of fun i j => finPart D (y i j)) ∈ W then 1 else 0) := fun y => by
    show f _ * g _ = _
    rw [hf]
    congr 1
    exact hg1 _
  refine ⟨fun _ => η₀, fun i => ⟨Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    obtain ⟨Ka, hKa, hKaC⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (max R 1 + 1)
      (⋃ i, ⋃ j, (fun w : Matrix (Fin 1) (Fin b) (AfE D) => w i j) '' (W : Set _))
      (isCompact_iUnion fun i => isCompact_iUnion fun j =>
        (hWc.image ((continuous_apply j).comp (continuous_apply i)) :
          IsCompact ((fun w : Matrix (Fin 1) (Fin b) (AfE D) => w i j) '' (W : Set _))))
    have hKc : IsCompact {y : Mx D 1 b | ∀ i j, y i j ∈ Ka} :=
      isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hKa
    refine HasCompactSupport.intro' hKc hKc.isClosed fun y hy => ?_
    by_contra hne
    change ¬ η₀ y = 0 at hne
    apply hy
    intro i j
    rw [hη] at hne
    have h1 := left_ne_zero_of_mul hne
    have h2 := right_ne_zero_of_mul hne
    have hw : (Matrix.of fun i j => finPart D (y i j)) ∈ W := by
      by_contra h
      exact h2 (if_neg h)
    refine hKaC _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, _, hw, rfl⟩⟩) fun ρ => ?_
    have hb : bump (rc y) ≠ 0 := fun h => h1 (by rw [h, Complex.ofReal_zero])
    have hmem : rc y ∈ Metric.ball (0 : D.what₂.Tau → Fin 1 → Fin b → ℂ) (max R 1 + 1) := by
      rw [← bump.support_eq]; exact hb
    rw [mem_ball_zero_iff] at hmem
    have h3 : ‖rc y ρ i j‖ ≤ ‖rc y‖ :=
      ((norm_le_pi_norm (rc y ρ i) j).trans (norm_le_pi_norm (rc y ρ) i)).trans (norm_le_pi_norm (rc y) ρ)
    exact h3.trans hmem.le
  ·
    intro y
    show η₀ y = if IntOff S y then η₀ (e • y) else 0
    by_cases hy : IntOff S y
    · rw [if_pos hy, hη, hη]
      have hr : rc (e • y) = rc y := by
        funext τ i j
        show θ τ (infPart D ((e • y) i j)) = θ τ (infPart D (y i j))
        rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_mul, hθe τ, one_mul]
      have hw : (Matrix.of fun i j => finPart D ((e • y) i j)) = Matrix.of fun i j => ef * finPart D (y i j) := by
        funext i j
        rw [Matrix.of_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      have hiff := mem_U_iff (N := N) hef hS (w := Matrix.of fun i j => finPart D (y i j))
        (fun v hv i j => by rw [Matrix.of_apply, ← cv_eq]; exact hy v hv i j)
      rw [hr, hw]
      simp only [Matrix.of_apply] at hiff
      by_cases hm : (Matrix.of fun i j => finPart D (y i j)) ∈ W
      · rw [if_pos hm, if_pos (hiff.1 hm)]
      · rw [if_neg hm, if_neg (fun h => hm (hiff.2 h))]
    · rw [if_neg hy, hη, if_neg, mul_zero]
      intro hm
      exact hy fun v hv i j => by rw [cv_eq]; exact hm.1 v hv i j
  ·
    intro y
    show 0 ≤ (η₀ y).re ∧ (η₀ y).re ≤ 1 ∧ (η₀ y).im = 0
    rw [hη]
    split_ifs
    · rw [mul_one, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨bump.nonneg, bump.le_one, rfl⟩
    · simp
  ·
    intro x hx
    show η₀ (x.submatrix (fun _ => i) id) = 1
    rw [hη, if_pos, bump.one_of_mem_closedBall]
    · simp
    · exact Metric.closedBall_subset_closedBall (le_max_left _ _)
        (hR (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩))
    · refine ⟨fun v hv i' j => ?_, fun i' j => ?_⟩
      · rw [Matrix.of_apply, ← cv_eq]; exact hCi x hx v hv i j
      · exact hNC _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, x, hx, rfl⟩⟩)

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKE
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

section GlobalTheory

variable {R : Type} [CommRing R] {n : ℕ}

theorem submatrix_fromBlocks_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _, fromBlocks_multiply]

theorem block_matrix_one : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4; rw [fromBlocks_one, Matrix.submatrix_one_equiv]

theorem conj_block_matrix (s : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R) :
    cj s (blk4 a b c d) = blk4 (cj s a) (cj s c) (cj s b) (cj s d) := by
  unfold blk4; rw [← cj_fromBlocks]; rfl

theorem block_matrix_map {S : Type} [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4; rw [← fromBlocks_map]; rfl

theorem blockMatrixTwoByTwoFin_injective {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R} (h : blk4 a b c d = blk4 a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have : fromBlocks a b c d = fromBlocks a' b' c' d' := by
    have := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
    simpa [blk4, Matrix.submatrix_submatrix] using this
  exact Matrix.fromBlocks_inj.1 this

def bA (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
def bB (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂
def bC (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁
def bD (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

theorem block_matrix_of_blocks (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : blk4 (bA M) (bB M) (bC M) (bD M) = M := by
  unfold blk4 bA bB bC bD
  rw [fromBlocks_toBlocks, Matrix.submatrix_submatrix]
  simp

theorem unit_fromBlocks (s : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R)
    (h : cj s (blk4 a b c d) * blk4 0 1 (-1) 0 * blk4 a b c d = blk4 0 1 (-1) 0) :
    cj s (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d = fromBlocks 0 1 (-1) 0 := by
  rw [conj_block_matrix, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h
  obtain ⟨h1, h2, h3, h4⟩ := blockMatrixTwoByTwoFin_injective h
  rw [cj_fromBlocks, fromBlocks_multiply, fromBlocks_multiply, h1, h2, h3, h4]

theorem unit_col (s : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R)
    (h : cj s (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d = fromBlocks 0 1 (-1) 0) :
    cj s a * c = cj s c * a ∧ cj s a * d - cj s c * b = 1 ∧ cj s b * d = cj s d * b := by
  rw [cj_fromBlocks, fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
    zero_add, add_zero] at h
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← h1]; noncomm_ring
  · rw [← h2]; noncomm_ring
  · rw [← sub_eq_zero, ← h4]; noncomm_ring

end GlobalTheory

section G

variable {D : D7} {n : ℕ}

abbrev Jm (D : D7) (n : ℕ) : Mx D (n + n) (n + n) := blk4 0 1 (-1) 0

theorem Jst_map : (Jst D n).map (inclR (AF D.host.F)) = Jm D n := by
  rw [Jst, block_matrix_map]
  have e : ((-1 : Matrix (Fin n) (Fin n) D.host.E)).map (inclR (F := D.host.F) (AF D.host.F)) = -1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  simp [e]

theorem mat_unit (g : G D n) : cj (cA D) (mat g) * Jm D n * mat g = Jm D n := by
  rw [← Jst_map]; exact g.2

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp [mat]

theorem mat_one : mat (1 : G D n) = 1 := by
  simp [mat]

theorem mat_inv_mul (g : G D n) : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := by
  apply Subtype.ext; apply Units.ext; exact e

theorem mat_inv_eq {g : G D n} {N : Mx D (n + n) (n + n)} (h : mat g * N = 1) : mat g⁻¹ = N := by
  calc mat g⁻¹ = mat g⁻¹ * (mat g * N) := by rw [h, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]

theorem Jm_inv : blk4 (0 : Mx D n n) (-1) 1 0 * Jm D n = 1 := by
  rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]

theorem exists_G (M : Mx D (n + n) (n + n)) (hM : cj (cA D) M * Jm D n * M = Jm D n) : ∃ g : G D n, mat g = M := by
  have h1 : (blk4 (0 : Mx D n n) (-1) 1 0 * cj (cA D) M * Jm D n) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cj (cA D) M), hM, Jm_inv]
  have h2 := mul_eq_one_comm.1 h1
  let u : GL (Fin (n + n)) (AE D) := ⟨M, _, h2, h1⟩
  have hu : u ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n) := by
    change cj (cA D) M * (Jst D n).map (inclR (AF D.host.F)) * M = (Jst D n).map (inclR (AF D.host.F))
    rw [Jst_map]; exact hM
  exact ⟨⟨u, hu⟩, rfl⟩

end G

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEv
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

variable {D : D7}

theorem gen_good {θ : InfFam D} {a b : ℕ} (f : SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ)
    (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e →
      Good S e (fun x : Mx D a b => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) := by
  obtain ⟨S₀, hS₀⟩ := fin_good g hg
  refine ⟨S₀, fun S hS e he x => ?_⟩
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hi1, hi2⟩ := isIdem_eS S
  have heS : e = eS S := ae_ext e (eS S) (fun w => (he1 w).trans (hi1 w).symm)
    (fun v => (he2 v).trans (hi2 v).symm)
  subst heS
  have hinf : ∀ τ (i : Fin a) (j : Fin b), compAt θ τ (eS S • x) i j = compAt θ τ x i j := by
    intro τ i j
    show θ τ (infPart D ((eS S • x) i j)) = θ τ (infPart D (x i j))
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, infPart_eS, one_mul]
  have hfin : (fun (i : Fin a) (j : Fin b) => finPart D ((eS S • x) i j)) =
      sPart S (fun i j => finPart D (x i j)) := by
    funext i j
    show finPart D ((eS S • x) i j) = algebraMap _ _ (indS S) * finPart D (x i j)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, finPart_eS]
  simp only [hinf]
  rw [hfin, hS₀ S hS (fun i j => finPart D (x i j))]
  by_cases h : IntOff S x
  · have h' : ∀ v ∉ S, ∀ (i : Fin a) (j : Fin b),
        projV v (fun i j => finPart D (x i j)) i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
      fun v hv i j => by
        have := h v hv i j
        rw [cv_eq] at this
        exact this
    rw [if_pos h', if_pos h]
  · have h' : ¬ ∀ v ∉ S, ∀ (i : Fin a) (j : Fin b),
        projV v (fun i j => finPart D (x i j)) i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
      fun h'' => h (fun v hv i j => by
        have := h'' v hv i j
        rw [cv_eq]
        exact this)
    rw [if_neg h', if_neg h, mul_zero]

end PositivityTheory.Rg.Rsw.L.LGoodEv

namespace PositivityTheory.Rg.Rsw.L

theorem goodEv : IdemEx → GoodEv := by
  intro _ D θ _ a b Φ hΦ
  refine LGoodEv.ev_span _ rfl ?_ Φ hΦ
  rintro φ ⟨f, g, hg, rfl⟩
  exact LGoodEv.gen_good f g hg

end PositivityTheory.Rg.Rsw.L

end
end

