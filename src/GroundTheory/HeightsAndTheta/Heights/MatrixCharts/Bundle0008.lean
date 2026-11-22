import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PSchurDetBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace SchurDetBound

theorem qf_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (G : Matrix ι ι ℝ)
    (w : κ → ℝ) : MCSchur.qf G (w ∘ e) = MCSchur.qf (reindex e e G) w := by
  simp only [MCSchur.qf, dotProduct, mulVec, reindex_apply, submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.sum_comp]
  simp

end SchurDetBound

theorem SchurDetBound.proof : SchurDetBound.Statement := by
  intro k G hsym hdet t ht
  set e : Fin (k + 1) ≃ Fin k ⊕ Fin 1 := finSumFinEquiv.symm with he
  set M := reindex e e G with hMdef
  set A := M.toBlocks₁₁ with hAdef
  set B := M.toBlocks₁₂ with hBdef
  set D := M.toBlocks₂₂ with hDdef
  have hA : A = G.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp [hAdef, hMdef, he, toBlocks₁₁, Fin.castSucc]
  have hAsymm : A.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [hAdef, hMdef, toBlocks₁₁, transpose_apply, of_apply, reindex_apply,
      submatrix_apply]
    exact congrFun (congrFun hsym _) _
  have hM : fromBlocks A B Bᴴ D = M := by
    rw [← fromBlocks_toBlocks M]
    congr 1
    rw [conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [hBdef, hMdef, toBlocks₁₂, toBlocks₂₁, transpose_apply, of_apply, reindex_apply,
      submatrix_apply]
    exact congrFun (congrFun hsym _) _
  have hdetA : 0 < A.det := by rw [hA]; exact hdet
  have : Invertible A := invertibleOfIsUnitDet A hdetA.ne'.isUnit
  set S := D - Bᴴ * A⁻¹ * B with hSdef
  have hdetG : G.det = A.det * S 0 0 := by
    rw [← det_reindex_self e G, ← hMdef, ← hM, det_fromBlocks₁₁, invOf_eq_nonsing_inv,
      Matrix.det_unique (D - Bᴴ * A⁻¹ * B)]
    rfl

  set y : Fin 1 → ℝ := fun _ => 1 with hy
  set x : Fin k → ℝ := -((A⁻¹ * B) *ᵥ y) with hx
  have hval : MCSchur.qf G ((Sum.elim x y) ∘ e) = S 0 0 := by
    rw [SchurDetBound.qf_reindex, ← hMdef, ← hM]
    have h := schur_complement_eq₁₁ B D x y hAsymm
    simp only [star_trivial] at h
    simp only [MCSchur.qf, dotProduct_mulVec]
    rw [show (Sum.elim x y) = x ⊕ᵥ y from rfl, h, hx, neg_add_cancel]
    simp [hy, dotProduct, vecMul, hSdef]
  have hlast : ((Sum.elim x y) ∘ e) (Fin.last k) = 1 := by
    simp [he, hy]
  have hts := ht _ hlast
  rw [hval] at hts
  rw [hdetG, ← hA, mul_comm t]
  exact mul_le_mul_of_nonneg_left hts hdetA.le

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PUnimodularLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace UnimodularLast

def dotForm {k : ℕ} (ρ : Fin (k + 1) → ℤ) : (Fin (k + 1) → ℤ) →ₗ[ℤ] ℤ where
  toFun x := ρ ⬝ᵥ x
  map_add' x y := dotProduct_add ρ x y
  map_smul' c x := by rw [dotProduct_smul]; rfl

theorem exists_basis (k : ℕ) (ρ : Fin (k + 1) → ℤ) (hρ : ρ ≠ 0) :
    ∃ b : Module.Basis (Fin (k + 1)) ℤ (Fin (k + 1) → ℤ),
      (∀ j : Fin k, ρ ⬝ᵥ b (Fin.castSucc j) = 0) ∧ ρ ⬝ᵥ b (Fin.last k) ≠ 0 := by
  set φ := dotForm ρ with hφ
  have hφx : ∀ x, φ x = ρ ⬝ᵥ x := fun _ => rfl
  set g := Submodule.IsPrincipal.generator (LinearMap.range φ) with hgdef
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp
    (Submodule.IsPrincipal.generator_mem (LinearMap.range φ))
  have hg : g ≠ 0 := by
    intro h0
    have hbot := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero
      (LinearMap.range φ)).mpr h0
    apply hρ
    funext i
    have hi : φ (Pi.single i 1) ∈ LinearMap.range φ := LinearMap.mem_range_self φ _
    rw [hbot, Submodule.mem_bot, hφx, dotProduct_single, mul_one] at hi
    simpa using hi
  have hli : ∀ (c : ℤ), ∀ x ∈ LinearMap.ker φ, c • y + x = 0 → c = 0 := by
    intro c x hx hc
    have h1 := congrArg φ hc
    rw [map_add, map_smul, LinearMap.mem_ker.mp hx, hy, map_zero, add_zero, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_right hg
  have hsp : ∀ z, ∃ c : ℤ, z + c • y ∈ LinearMap.ker φ := by
    intro z
    obtain ⟨c, hc⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator
      (LinearMap.range φ)).mp (LinearMap.mem_range_self φ z)
    refine ⟨-c, ?_⟩
    rw [LinearMap.mem_ker, map_add, map_smul, hy, hc, ← hgdef, smul_eq_mul, smul_eq_mul]
    ring
  obtain ⟨n, bk⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin (k + 1))) (LinearMap.ker φ)
  let b := Module.Basis.mkFinSnoc bk y hli hsp
  have hn : n = k := by
    have h := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_fin] at h
    omega
  subst hn
  refine ⟨b, fun j => ?_, ?_⟩
  · have hb : b (Fin.castSucc j) = (bk j : Fin (n + 1) → ℤ) := by
      simp only [b, Module.Basis.coe_mkFinSnoc, Fin.snoc_castSucc, Function.comp_apply]
    rw [hb, ← hφx]
    exact LinearMap.mem_ker.mp (bk j).2
  · have hb : b (Fin.last n) = y := by
      simp only [b, Module.Basis.coe_mkFinSnoc, Fin.snoc_last]
    rw [hb, ← hφx, hy]
    exact hg

end UnimodularLast

theorem UnimodularLast.proof : UnimodularLast.Statement := by
  intro k ρ hρ
  obtain ⟨b, hker, hlast⟩ := UnimodularLast.exists_basis k ρ hρ
  refine ⟨(Pi.basisFun ℤ (Fin (k + 1))).toMatrix b, ?_, ?_, ?_⟩
  · exact Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  · intro j
    have : (ρ ᵥ* (Pi.basisFun ℤ (Fin (k + 1))).toMatrix b) (Fin.castSucc j) =
        ρ ⬝ᵥ b (Fin.castSucc j) := by
      simp only [vecMul, dotProduct, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [this]
    exact hker j
  · have : (ρ ᵥ* (Pi.basisFun ℤ (Fin (k + 1))).toMatrix b) (Fin.last k) =
        ρ ⬝ᵥ b (Fin.last k) := by
      simp only [vecMul, dotProduct, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [this]
    exact hlast

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def InvEntryBound.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ), 0 < c →
    (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ∀ j l, |Y⁻¹ j l| ≤ c⁻¹

def InvEntryDeriv.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ)
    (Y : E → Matrix (Fin g) (Fin g) ℝ) (p : E) (c b : ℝ), 0 < c →
    (Y p - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef →
    (∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p ∧ ‖fderiv ℝ (fun q => Y q j l) p‖ ≤ b) →
    ∀ j l, DifferentiableAt ℝ (fun q => (Y q)⁻¹ j l) p ∧
      ‖fderiv ℝ (fun q => (Y q)⁻¹ j l) p‖ ≤ (g : ℝ) ^ 2 * c⁻¹ ^ 2 * b

def MatrixDetDeriv.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (H : E → Matrix (Fin k) (Fin k) ℂ) (p : E) (A B : ℝ),
    (∀ j l, DifferentiableAt ℝ (fun q => H q j l) p ∧ ‖H p j l‖ ≤ A ∧
      ‖fderiv ℝ (fun q => H q j l) p‖ ≤ B) →
    DifferentiableAt ℝ (fun q => (H q).det) p ∧
      ‖fderiv ℝ (fun q => (H q).det) p‖ ≤ (k.factorial : ℝ) * k * A ^ (k - 1) * B

def GramEntryDeriv.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g k : ℕ)
    (F : E → Matrix (Fin g) (Fin k) ℂ) (Z : E → Matrix (Fin g) (Fin g) ℝ) (p : E) (a e e' : ℝ),
    (∀ j l, DifferentiableAt ℝ (fun q => F q j l) p ∧ ‖F p j l‖ ≤ a ∧
      ‖fderiv ℝ (fun q => F q j l) p‖ ≤ a) →
    (∀ j l, DifferentiableAt ℝ (fun q => Z q j l) p ∧ |Z p j l| ≤ e ∧
      ‖fderiv ℝ (fun q => Z q j l) p‖ ≤ e') →
    ∀ j l, DifferentiableAt ℝ (fun q => ((F q)ᴴ * (Z q).map (fun x : ℝ => (x : ℂ)) * F q) j l) p ∧
      ‖((F p)ᴴ * (Z p).map (fun x : ℝ => (x : ℂ)) * F p) j l‖ ≤ (g : ℝ) ^ 2 * a ^ 2 * e ∧
      ‖fderiv ℝ (fun q => ((F q)ᴴ * (Z q).map (fun x : ℝ => (x : ℂ)) * F q) j l) p‖ ≤
        (g : ℝ) ^ 2 * (2 * a ^ 2 * e + a ^ 2 * e')

def LogDetGramDeriv.Statement : Prop :=
  ∀ g k : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → Matrix (Fin g) (Fin k) ℂ) (Y : E → Matrix (Fin g) (Fin g) ℝ) (p : E) (a b c μ : ℝ),
    0 < c → 0 < μ → 0 ≤ a → 0 ≤ b →
    (∀ j l, DifferentiableAt ℝ (fun q => F q j l) p ∧ ‖F p j l‖ ≤ a ∧
      ‖fderiv ℝ (fun q => F q j l) p‖ ≤ a) →
    (∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p ∧ ‖fderiv ℝ (fun q => Y q j l) p‖ ≤ b) →
    (Y p - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef →
    μ ≤ ((F p)ᴴ * (Y p)⁻¹.map (fun x : ℝ => (x : ℂ)) * F p).det.re →
    DifferentiableAt ℝ (fun q => logDetGram (Y q) (F q)) p ∧
      ‖fderiv ℝ (fun q => logDetGram (Y q) (F q)) p‖ ≤
        K * (1 + a) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * (1 + b) / μ

def AnalyticDerivBound.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℂ) (U K : Set E),
    IsOpen U → AnalyticOnNhd ℂ f U → IsCompact K → K ⊆ U →
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ K, DifferentiableAt ℝ f x ∧ ‖f x‖ ≤ A ∧ ‖fderiv ℝ f x‖ ≤ A

def ChartFrameDeriv.Statement : Prop :=
  ∀ D : PeriodChartData, ∃ A : ℝ, 0 < A ∧ ∀ p ∈ D.K, ∀ j l,
    DifferentiableAt ℝ (fun q => D.f q j l) p ∧ ‖D.f p j l‖ ≤ A ∧
      ‖fderiv ℝ (fun q => D.f q j l) p‖ ≤ A

def CuspTimeDeriv.Statement : Prop :=
  ∀ D : PeriodChartData, ∀ z ∈ D.Ustar, ∀ i : Fin D.a,
    DifferentiableAt ℝ (fun w => cuspTime D.a_le w i) z ∧
      ‖fderiv ℝ (fun w => cuspTime D.a_le w i) z‖ ≤ Real.exp (D.radius z / 2)

def ChartImagDeriv.Statement : Prop :=
  ∀ D : PeriodChartData, ∃ A : ℝ, 0 < A ∧ ∀ p ∈ D.K, p.1 ∈ D.Ustar → ∀ j l,
    DifferentiableAt ℝ (fun q : (Fin D.n → ℂ) × (Fin D.m → ℂ) => D.Y q.1 j l) p ∧
      ‖fderiv ℝ (fun q : (Fin D.n → ℂ) × (Fin D.m → ℂ) => D.Y q.1 j l) p‖ ≤
        A * Real.exp (D.radius p.1 / 2)

theorem InvEntryBound.hypotheses_met :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) - (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 ∧
      (0 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef :=
  ⟨by simp, PosSemidef.zero⟩

theorem InvEntryDeriv.hypotheses_met :
    ((fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 - (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef ∧
      ∀ j l : Fin 2, DifferentiableAt ℝ (fun q : ℝ => (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) q j l) 0 ∧
        ‖fderiv ℝ (fun q : ℝ => (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) q j l) 0‖ ≤ 0 := by
  refine ⟨by simpa using PosSemidef.zero, fun j l => ⟨differentiableAt_const _, ?_⟩⟩
  simp

theorem MatrixDetDeriv.hypotheses_met :
    ∀ j l : Fin 2, DifferentiableAt ℝ (fun q : ℝ => (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) q j l) 0 ∧
      ‖(fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 j l‖ ≤ 1 ∧
      ‖fderiv ℝ (fun q : ℝ => (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) q j l) 0‖ ≤ 0 := by
  intro j l
  refine ⟨differentiableAt_const _, ?_, by simp⟩
  by_cases h : j = l <;> simp [Matrix.one_apply, h]

theorem LogDetGramDeriv.hypotheses_met :
    (1 : ℝ) ≤ ((1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ * ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹).map
      (fun x : ℝ => (x : ℂ)) * (1 : Matrix (Fin 1) (Fin 1) ℂ)).det.re := by
  simp

theorem AnalyticDerivBound.hypotheses_met :
    IsOpen (Set.univ : Set ℂ) ∧ AnalyticOnNhd ℂ (fun x : ℂ => x) Set.univ ∧
      IsCompact (Metric.closedBall (0 : ℂ) 1) ∧ Metric.closedBall (0 : ℂ) 1 ⊆ Set.univ :=
  ⟨isOpen_univ, analyticOnNhd_id, isCompact_closedBall _ _, Set.subset_univ _⟩

end

end GroundTheory.Heights₂.Heights
end

