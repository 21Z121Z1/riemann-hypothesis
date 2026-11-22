import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0237

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilActionBlockMatrixComponents
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Parts

section Field

variable {K : Type} [Field K]

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem extB_castAdd {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) (i j : Fin r) :
    (extB b : Matrix (Fin (r + s)) (Fin (r + s)) K) (Fin.castAdd s i) (Fin.castAdd s j) = b i j := by
  simp [extB]

theorem extB_natAdd_left {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) (i : Fin s) (j : Fin (r + s)) :
    (extB b : Matrix (Fin (r + s)) (Fin (r + s)) K) (Fin.natAdd r i) j = 0 := by
  simp [extB]

theorem extB_natAdd_right {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) (i : Fin (r + s)) (j : Fin s) :
    (extB b : Matrix (Fin (r + s)) (Fin (r + s)) K) i (Fin.natAdd r j) = 0 := by
  simp [extB]

theorem eId_mul_extB {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) :
    eId K (r + s) r * extB b = extB b := by
  ext i j
  rw [eId, Matrix.diagonal_mul]
  by_cases h : (i : ℕ) < r
  · simp [h]
  · simp [h, extB]

theorem representation_matrix_block_form (σ : K →+* K) {r s : ℕ} (b : Matrix (Fin r) (Fin r) K)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) K) :
    repMat σ b a = blk4 ((1 - eId K (r + s) r) * a)
        (((1 - eId K (r + s) r) * extB b + eId K (r + s) r) * (cT σ a)⁻¹)
        (-(eId K (r + s) r * a))
        ((1 - eId K (r + s) r - extB b) * (cT σ a)⁻¹) := by
  simp only [repMat, wr, nB, mA]
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have h : -eId K (r + s) r * extB b + (1 - eId K (r + s) r) * 1 =
      1 - eId K (r + s) r - extB b := by
    rw [Matrix.neg_mul, eId_mul_extB, Matrix.mul_one]
    abel
  rw [h]
  simp

end Field

variable {D : D7}

theorem block_matrix_map {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) D.host.E) :
    (blk4 a b c d).map (incA D) = blk4 (a.map (incA D)) (b.map (incA D)) (c.map (incA D)) (d.map (incA D)) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem xPart_zy_mul {m n : ℕ} (y : Mx D m n) (A B C E' : Mx D n n) :
    xPart (HMul.hMul (zy y) (blk4 A B C E') : Mx D m (n + n)) = HMul.hMul y C := by
  ext i j
  simp only [xPart, zy, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [Fintype.sum_equiv finSumFinEquiv.symm _
    (fun t => Sum.elim (fun _ => (0 : AE D)) (y i) t * Matrix.fromBlocks A B C E' t (Sum.inl j))
    (fun _ => rfl), Fintype.sum_sum_type]
  simp

theorem yPart_zy_mul {m n : ℕ} (y : Mx D m n) (A B C E' : Mx D n n) :
    yPart (HMul.hMul (zy y) (blk4 A B C E') : Mx D m (n + n)) = HMul.hMul y E' := by
  ext i j
  simp only [yPart, zy, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [Fintype.sum_equiv finSumFinEquiv.symm _
    (fun t => Sum.elim (fun _ => (0 : AE D)) (y i) t * Matrix.fromBlocks A B C E' t (Sum.inr j))
    (fun _ => rfl), Fintype.sum_sum_type]
  simp

theorem colJoin_mul_eId {m r s : ℕ} (y₁ : Mx D m r) (y₂ : Mx D m s) :
    (HMul.hMul (colJoin y₁ y₂) ((eId D.host.E (r + s) r).map (incA D)) : Mx D m (r + s)) =
      colJoin y₁ (0 : Mx D m s) := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [eId, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply]
  · simp [eId, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply]

theorem colJoin_mul_extB {m r s : ℕ} (y₁ : Mx D m r) (y₂ : Mx D m s) (b : Matrix (Fin r) (Fin r) D.host.E) :
    (HMul.hMul (colJoin y₁ y₂) ((extB b : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E).map (incA D)) : Mx D m (r + s)) =
      colJoin (HMul.hMul y₁ (rat b) : Mx D m r) (0 : Mx D m s) := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [Matrix.mul_apply, Fin.sum_univ_add, extB_castAdd, extB_natAdd_left, rat]
  · simp [Matrix.mul_apply, Fin.sum_univ_add, extB_natAdd_right]

theorem parts : ∀ (D : D7) (m r s : ℕ) (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (y₁ : Mx D m r) (y₂ : Mx D m s),
    xPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        -HMul.hMul (colJoin y₁ (0 : Mx D m s)) (rat a) ∧
      yPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) := by
  intro D m r s b a y₁ y₂
  set e := eId D.host.E (r + s) r with he
  set y : Mx D m (r + s) := colJoin y₁ y₂ with hy
  have hmap : ∀ X : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E,
      X.map (incA D) = (incA D).mapMatrix X := fun _ => rfl
  rw [representation_matrix_block_form, block_matrix_map, xPart_zy_mul, yPart_zy_mul]
  constructor
  · have h1 : (-(e * a)).map (incA D) = -(e.map (incA D) * rat a) := by
      simp only [hmap, map_neg, map_mul]; rfl
    rw [h1, Matrix.mul_neg, ← Matrix.mul_assoc, colJoin_mul_eId]
  · have h2 : ((1 - e - extB b) * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹).map (incA D) =
        (1 - e.map (incA D) - (extB b : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E).map (incA D)) *
          rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹ := by
      simp only [hmap, map_sub, map_mul, map_one]; rfl
    rw [h2, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, hy, colJoin_mul_eId,
      colJoin_mul_extB, ← colJoin_sub, ← colJoin_sub]
    congr 2
    · simp
    · simp

end GlobalTheory.CompanionTheory.EisUnfold.Parts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNormDiagonalReduction
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.MajIwa

theorem eq_uni_mul_dg (β : G3) (hβ : β ∈ (Reduction.adelicBorel : Subgroup G3))
    (t1 t2 t3 : (𝔸[ℚ])ˣ) (h1 : (β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 0 0 = t1)
    (h2 : (β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 1 1 = t2)
    (h3 : (β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 2 2 = t3) :
    β = uni ((β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 0 1 * ((t2⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]))
          ((β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 0 2 * ((t3⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]))
          ((β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 1 2 * ((t3⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ])) * dg t1 t2 t3 := by
  have hb := Reduction.mem_adelicBorel.1 hβ
  have z10 : (β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 1 0 = 0 := hb (by decide : (0 : Fin 3) < 1)
  have z20 : (β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 2 0 = 0 := hb (by decide : (0 : Fin 3) < 2)
  have z21 : (β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 2 1 = 0 := hb (by decide : (1 : Fin 3) < 2)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, dg, Matrix.mul_apply, Fin.sum_univ_three, h1, h2, h3, z10, z20, z21, mul_assoc]

theorem dg_eq_scalar_mul (t1 t2 t3 : (𝔸[ℚ])ˣ) :
    (dg t1 t2 t3 : G3) = dg t3 t3 t3 * dg (t1 * t2⁻¹ * (t2 * t3⁻¹)) (t2 * t3⁻¹) 1 := by
  apply Units.ext
  have e0 : t1 * t2⁻¹ * (t2 * t3⁻¹) = t1 * t3⁻¹ := by group
  have e1 : ((t3 : 𝔸[ℚ])) * ((t1 * t3⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) = t1 := by
    rw [← Units.val_mul, mul_comm t1, mul_inv_cancel_left]
  have e2 : ((t3 : 𝔸[ℚ])) * ((t2 * t3⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) = t2 := by
    rw [← Units.val_mul, mul_comm t2, mul_inv_cancel_left]
  rw [e0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg, Matrix.mul_apply, Fin.sum_univ_three, -Units.val_mul, e1, e2]

theorem norm_W_borel_mul : ∀ (V : Submodule ℂ (G3 → ℂ)), WhA V → ∀ W ∈ V,
    ∀ β ∈ (Reduction.adelicBorel : Subgroup G3), ∀ t1 t2 t3 : (𝔸[ℚ])ˣ,
    (β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 0 0 = t1 → (β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 1 1 = t2 →
    (β : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) 2 2 = t3 → ∀ k : G3,
    ‖W (β * k)‖ = ‖W (dg (t1 * t2⁻¹ * (t2 * t3⁻¹)) (t2 * t3⁻¹) 1 * k)‖ := by
  intro V hV W hW β hβ t1 t2 t3 h1 h2 h3 k
  rw [eq_uni_mul_dg β hβ t1 t2 t3 h1 h2 h3, mul_assoc, hV.psi W hW, norm_mul, Circle.norm_coe,
    one_mul, dg_eq_scalar_mul t1 t2 t3, mul_assoc, hV.cen W hW]

end GlobalTheory.CompanionTheory.MajIwa
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursIrreducibleSubquotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.WordIrr

theorem exists_lift_twKer {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) {H : Subgroup G} {y : W} (hy : y ∈ twKer τ H 1) :
    ∃ x ∈ twKer σ H 1, f x = y := by
  have hint : ∀ (g : G) (u : V), f.toLinearMap (σ g u) = τ g (f.toLinearMap u) :=
    fun g u => LinearMap.congr_fun (f.isIntertwining' g) u
  have hfL : ∀ x, f x = f.toLinearMap x := fun _ => rfl
  have hy' : y ∈ Submodule.span ℂ {w | ∃ (n : H) (v : W), w = τ ↑n v - ↑((1 : H →* ℂˣ) n) • v} := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, v, rfl⟩ := hw
    obtain ⟨u, rfl⟩ := hf v
    refine ⟨σ ↑n u - ↑((1 : H →* ℂˣ) n) • u, Submodule.subset_span ⟨n, u, rfl⟩, ?_⟩
    simp only [hfL, map_sub, Units.smul_def, map_smul, hint]
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [hfL]
    exact map_zero _
  | add a b _ _ ha hb =>
    obtain ⟨x1, hx1, rfl⟩ := ha
    obtain ⟨x2, hx2, rfl⟩ := hb
    refine ⟨x1 + x2, add_mem hx1 hx2, ?_⟩
    simp only [hfL, map_add]
  | smul c a _ ha =>
    obtain ⟨x1, hx1, rfl⟩ := ha
    refine ⟨c • x1, Submodule.smul_mem _ c hx1, ?_⟩
    simp only [hfL, map_smul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N s : ℕ} {d : Fin s → ℕ} {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

theorem jhMult_jac_of_le (e : (Σ a, Fin (d a)) ≃ Fin N)
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) U} (hσ : σ.IsIrreducible)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) {S T : Subrepresentation π} (h : T ≤ S) :
    jhMult σ (jac e S.toRepresentation) =
      jhMult σ (jac e T.toRepresentation) + jhMult σ (jac e (subQuot S T)) := by
  let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hS : IsSmooth S.toRepresentation := (IsSubquotient.of_injective j Subtype.val_injective).isSmooth hπ
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion h, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  have hps : Function.Surjective p := Submodule.Quotient.mk_surjective _
  refine jhMult_exact (jacMap e ι) (jacMap e p) hσ
    (GlobalTheory.JacquetExact.jacMap_injective e hS ι (Submodule.inclusion_injective h))
    (GlobalTheory.JacquetExact.jacMap_surjective e p hps) (fun u => ?_) (fun v hv => ?_)
  · obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have h0 : p (ι t) = 0 := (hp _).2 t.2
    show Submodule.Quotient.mk (p (ι t)) = 0
    rw [h0]
    rfl
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    have h1 : p x ∈ twKer (subQuot S T) (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
    obtain ⟨y, hy, hxy⟩ := exists_lift_twKer p hps h1
    have h2 : (x - y).1 ∈ T.toSubmodule := (hp _).1 (by rw [map_sub, hxy, sub_self])
    refine ⟨Submodule.Quotient.mk ⟨(x - y).1, h2⟩, ?_⟩
    show Submodule.Quotient.mk (x - y) = Submodule.Quotient.mk x
    refine (Submodule.Quotient.eq _).2 ?_
    rw [sub_sub_cancel_left]
    exact neg_mem hy

theorem exists_irrRep_of_subrep (e : (Σ a, Fin (d a)) ≃ Fin N)
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) U} (hσ : σ.IsIrreducible)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) (hl : HasFiniteLength π)
    (S : Subrepresentation π) (hS : jhMult σ (jac e S.toRepresentation) ≠ 0) :
    ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ S.toRepresentation ∧ jhMult σ (jac e τ.ρ) ≠ 0 := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hl
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  induction S using WellFoundedLT.induction with
  | ind S ih =>
  rcases eq_or_ne S ⊥ with rfl | hne
  · exfalso
    apply hS
    have h0 : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
      inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
    have h1 : Subsingleton (Jacquet (⊥ : Subrepresentation π).toRepresentation (unipRad k e)) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    exact jhMult_of_subsingleton hσ _
  obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  rw [jhMult_jac_of_le e hσ hπ hT.le] at hS
  by_cases h0 : jhMult σ (jac e T.toRepresentation) = 0
  · rw [h0, zero_add] at hS
    have hq : IsSubquotient (subQuot S T) S.toRepresentation :=
      .of_surjective p (Submodule.Quotient.mk_surjective _)
    have hsm : IsSmooth (subQuot S T) :=
      (hq.trans (.of_injective j Subtype.val_injective)).isSmooth hπ
    exact ⟨⟨_, subQuot S T, hsm, isIrreducible_subQuot hT⟩, hq, hS⟩
  · obtain ⟨τ, h1, h2⟩ := ih T hT.lt h0
    exact ⟨τ, h1.trans (.of_injective ι (Submodule.inclusion_injective hT.le)), h2⟩

theorem exists_irrRep_wd : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ w : List (IrrGL k), Wd π w → ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ π ∧ Wd τ.ρ w := by
  intro k _ _ _ _ hA N V _ _ π hπ hl w ⟨hd, hw⟩
  have hσ : (piTensor fun a => (w.get a).rep).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (w.get a).2.rep.irr) fun a φ hφ =>
      GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin (w.get a).1)) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO _ _ (w.get a).2.rep.irr
        (hA k _ _ _ (w.get a).2.rep.smooth (w.get a).2.rep.irr) φ hφ
  have hT1 : IsSubquotient π (⊤ : Subrepresentation π).toRepresentation :=
    .of_surjective (topEquiv π).toIntertwiningMap (topEquiv π).surjective
  have hT2 : IsSubquotient (⊤ : Subrepresentation π).toRepresentation π :=
    .of_injective (topEquiv π).toIntertwiningMap (topEquiv π).injective
  have h1 : jhMult (piTensor fun a => (w.get a).rep)
      (jac (stdBlocks (fun a => (w.get a).1) hd) (⊤ : Subrepresentation π).toRepresentation) ≠ 0 :=
    jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 hw).trans
      (GlobalTheory.JacquetExact.isSubquotient_jac _ (hT2.isSmooth hπ) hT1))
  obtain ⟨τ, h2, h3⟩ := exists_irrRep_of_subrep _ hσ hπ hl ⊤ h1
  exact ⟨τ, h2.trans hT2, hd, h3⟩

end GlobalTheory.CompanionTheory.WordIrr

end
end

