import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTensorTypesIntertwinerMatrixPolynomials
section
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompactHoweJoint

theorem exists_bilinear {G G' H H' P : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    [AddCommGroup P] [Module ℂ P] (S : Set G) (S' : Set G') (τ : G → H →ₗ[ℂ] H) (τ' : G' → H' →ₗ[ℂ] H')
    (a : G → P →ₗ[ℂ] P) (b : G' → P →ₗ[ℂ] P) (hab : ∀ g h x, a g (b h x) = b h (a g x))
    (hirr : ∀ U : Submodule ℂ H, (∀ g ∈ S, ∀ v ∈ U, τ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hirr' : ∀ U : Submodule ℂ H', (∀ g ∈ S', ∀ v ∈ U, τ' g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (L : H →ₗ[ℂ] P) (L' : H' →ₗ[ℂ] P) (hL : ∀ g ∈ S, ∀ u, L (τ g u) = a g (L u))
    (hL' : ∀ h ∈ S', ∀ u, L' (τ' h u) = b h (L' u)) (v₀ : H) (v₀' : H') (h0 : L v₀ = L' v₀')
    (hne : L v₀ ≠ 0) :
    ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] P, Ψ ≠ 0 ∧ ∀ h ∈ S', ∀ g ∈ S, ∀ v' v, Ψ (τ' h v') (τ g v) = b h (a g (Ψ v' v)) := by
  let 𝓗 : Submodule ℂ (H →ₗ[ℂ] P) :=
    { carrier := {A | ∀ g ∈ S, ∀ u, A (τ g u) = a g (A u)}
      add_mem' := fun {A B} hA hB g hg u => by
        simp only [LinearMap.add_apply, map_add, hA g hg u, hB g hg u]
      zero_mem' := fun g _ u => by simp
      smul_mem' := fun c A hA g hg u => by
        simp only [LinearMap.smul_apply, map_smul, hA g hg u] }
  have hv₀ : v₀ ≠ 0 := fun h => hne (by rw [h, map_zero])
  have hv₀' : v₀' ≠ 0 := fun h => hne (by rw [h0, h, map_zero])
  let ev : 𝓗 →ₗ[ℂ] P := (LinearMap.applyₗ v₀).comp 𝓗.subtype
  have hev : ∀ A : 𝓗, ev A = (A : H →ₗ[ℂ] P) v₀ := fun _ => rfl
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro A hA
    rcases hirr (LinearMap.ker (A : H →ₗ[ℂ] P)) (fun g hg v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [A.2 g hg v, hv, map_zero]) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h v₀ hA) hv₀
    · exact Subtype.ext (LinearMap.ker_eq_top.1 h)
  have hstab : ∀ h, ∀ A ∈ 𝓗, (b h).comp A ∈ 𝓗 := fun h A hA g hg u => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hA g hg u, hab]
  have hrange : ∀ v', L' v' ∈ LinearMap.range ev := by
    rcases hirr' ((LinearMap.range ev).comap L') (fun h hh v hv => by
      obtain ⟨A, hA⟩ := hv
      refine ⟨⟨(b h).comp A, hstab h _ A.2⟩, ?_⟩
      rw [hL' h hh, ← hA]
      rfl) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h v₀' ⟨⟨L, hL⟩, h0⟩) hv₀'
    · intro v'
      have : v' ∈ (LinearMap.range ev).comap L' := h ▸ Submodule.mem_top
      exact this
  let Φ : H' →ₗ[ℂ] 𝓗 :=
    (LinearEquiv.ofInjective ev hinj).symm.toLinearMap.comp (L'.codRestrict _ hrange)
  have hΦ : ∀ v', ev (Φ v') = L' v' := fun v' =>
    congrArg Subtype.val ((LinearEquiv.ofInjective ev hinj).apply_symm_apply (L'.codRestrict _ hrange v'))
  refine ⟨𝓗.subtype.comp Φ, fun h => hne ?_, fun h hh g hg v' v => ?_⟩
  · rw [h0, ← hΦ, hev]
    exact congrArg (fun f : H' →ₗ[ℂ] H →ₗ[ℂ] P => f v₀' v₀) h
  · have key : Φ (τ' h v') = ⟨(b h).comp (Φ v'), hstab h _ (Φ v').2⟩ := by
      apply hinj
      rw [hΦ, hL' h hh, ← hΦ v']
      rfl
    show (Φ (τ' h v') : H →ₗ[ℂ] P) (τ g v) = b h (a g ((Φ v' : H →ₗ[ℂ] P) v))
    rw [key]
    show b h ((Φ v' : H →ₗ[ℂ] P) (τ g v)) = _
    rw [(Φ v').2 g hg v]

theorem mem_K_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Formalism.REAL.Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by simp [Formalism.REAL.Jm, allPos]
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Formalism.REAL.Jm (allPos k) = Formalism.REAL.Jm (allPos k) * g) ↔
    gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k)
  rw [hJ, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

open MvPolynomial in
theorem subst2_one_right {N n : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    subst2 h 1 P = ReciprocityTheory.PGsh.rowSubst h P := by
  have key : subst2 h (1 : Matrix (Fin n) (Fin n) ℂ) = ReciprocityTheory.PGsh.rowSubst h := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, ReciprocityTheory.PGsh.rowSubst, aeval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
  rw [key]

open MvPolynomial in
theorem subst2_one_left {N n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin N) ℂ) :
    subst2 1 g (rename Prod.swap P) = rename Prod.swap (ReciprocityTheory.PGsh.rowSubst g P) := by
  have key : (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g).comp (rename Prod.swap) =
      (rename Prod.swap).comp (ReciprocityTheory.PGsh.rowSubst (ι := Fin N) g) := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, subst2_X, ReciprocityTheory.PGsh.rowSubst, aeval_X,
      Finset.sum_eq_single p.2]
    · have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) p.2 p.swap.1 = 1 := Matrix.one_apply_eq _
      simp [map_sum, h1]
    · intro l _ hl
      have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) l p.swap.1 = 0 := Matrix.one_apply_ne hl
      simp [h1]
    · simp
  exact congrArg (fun f => f P) key

theorem isUpperUnitri_one (k : ℕ) : ReciprocityTheory.PGsh.IsUpperUnitri (1 : Matrix (Fin k) (Fin k) ℂ) :=
  ⟨fun _ => Matrix.one_apply_eq _, fun _ _ h => Matrix.one_apply_ne h.ne'⟩

open MvPolynomial in

theorem exists_joint_intertwiner : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (τ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → IsURepOn (UJset (allPos n)) τ → IsKTypeOf (allPos n) τ (fun a => (ν (Fin.castLE hn a) : ℝ)) ⊤ → IsURepOn (UJset (allPos N)) τ' → IsKTypeOf (allPos N) τ' (fun b => (ν b : ℝ)) ⊤ → ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] MvPolynomial (Fin N × Fin n) ℂ, Ψ ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ v' v, Ψ (τ' h v') (τ g v) = subst2 h g (Ψ v' v) := by
  intro N n hn ν H _ _ _ τ H' _ _ _ τ' hν hz hτ hK hτ' hK'
  obtain ⟨Δ, hΔ, hU, hD⟩ := GlobalTheory.T.exists_jointHighestWeight_leadingMinorProduct N n hn ν hν hz
  have hsw : ∀ Q : MvPolynomial (Fin N × Fin n) ℂ,
      rename (Prod.swap : Fin n × Fin N → _) (rename Prod.swap Q) = Q := fun Q => by
    rw [rename_rename]; simp
  have hinj : Function.Injective
      (rename (Prod.swap : Fin n × Fin N → Fin N × Fin n) : MvPolynomial _ ℂ → MvPolynomial _ ℂ) :=
    rename_injective _ Prod.swap_injective
  obtain ⟨L', hL', v₀', hv'⟩ := GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial N (Fin n) ν H' τ' Δ hτ' hK' hΔ
    (fun g hg => by rw [← subst2_one_right, hU g 1 hg (isUpperUnitri_one n)])
    (fun d => by
      have := hD d (fun _ => 1)
      rw [Matrix.diagonal_one, subst2_one_right] at this
      simpa using this)
  obtain ⟨L, hL, v₀, hv⟩ := GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial n (Fin N) (fun a => ν (Fin.castLE hn a)) H τ
    (rename Prod.swap Δ) hτ hK
    (fun h => hΔ (by rw [← hsw Δ, h, map_zero]))
    (fun g hg => hinj (by rw [← subst2_one_left, hsw, hU 1 g (isUpperUnitri_one N) hg]))
    (fun e => hinj (by
      have := hD (fun _ => 1) e
      rw [Matrix.diagonal_one] at this
      rw [← subst2_one_left, map_smul, hsw, this]
      simp))
  have hLv : ((rename (Prod.swap : Fin n × Fin N → Fin N × Fin n)).toLinearMap.comp L) v₀ = Δ := by
    show rename Prod.swap (L v₀) = Δ
    rw [hv, hsw]
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_bilinear (UJset (allPos n)) (UJset (allPos N))
    (fun g => (τ g).toLinearMap) (fun h => (τ' h).toLinearMap)
    (fun g => (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g).toLinearMap)
    (fun h => (subst2 h (1 : Matrix (Fin n) (Fin n) ℂ)).toLinearMap)
    (fun g h x => by simp [subst2_mul])
    (fun U hS => hK.2.2.1 U le_top fun g hg => hS g ((mem_K_iff g).1 hg))
    (fun U hS => hK'.2.2.1 U le_top fun g hg => hS g ((mem_K_iff g).1 hg))
    ((rename (Prod.swap : Fin n × Fin N → Fin N × Fin n)).toLinearMap.comp L) L'
    (fun g hg u => by
      show rename Prod.swap (L (τ g u)) = subst2 1 g (rename Prod.swap (L u))
      rw [hL g hg u, subst2_one_left])
    (fun h hh u => by
      show L' (τ' h u) = subst2 h 1 (L' u)
      rw [hL' h hh u, subst2_one_right])
    v₀ v₀' (hLv.trans hv'.symm) (by rw [hLv]; exact hΔ)
  refine ⟨Ψ, hΨ, fun h hh g hg v' v => ?_⟩
  have := hΨe h hh g hg v' v
  simpa [subst2_mul] using this

end GlobalTheory.CompactHoweJoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueProjectiveBundleFlagRefinement
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle.StepLift

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

variable {ι : Type} {m k k' : ι → ℕ} {τ : ι} {K : Type} [Field K]

theorem mul_apply_rest {O : Subring K} (g : Mat m K) {h : Mat m K} (hh : Par k O h) (a : Fin (m τ))
    (j : Rest m k τ) : (g * h) τ a j.1 = ∑ l : Rest m k τ, g τ a l.1 * h τ l.1 j.1 := by
  have hz : ∀ l : {l : Fin (m τ) // ¬ k τ ≤ (l : ℕ)}, g τ a l.1 * h τ l.1 j.1 = 0 := by
    intro l
    have hl : ¬ k τ ≤ (l.1 : ℕ) := l.2
    have hj : k τ ≤ (j.1 : ℕ) := j.2
    rw [(hh τ).2.2.2 l.1 j.1 (by omega) (by rw [Fin.lt_def]; omega), mul_zero]
  rw [Pi.mul_apply, Matrix.mul_apply,
    ← Fintype.sum_subtype_add_sum_subtype (fun l : Fin (m τ) => k τ ≤ (l : ℕ)),
    Finset.sum_eq_zero (fun l _ => hz l), add_zero]

private theorem det_submatrix_rest_ne_zero {O : Subring K} {g : Mat m K} (hg : Par k O g) (σ : ι) :
    ((g σ).submatrix (Subtype.val : Rest m k σ → Fin (m σ)) (Subtype.val : Rest m k σ → Fin (m σ))).det ≠ 0 := by
  have hd := Matrix.twoBlockTriangular_det (g σ) (fun i : Fin (m σ) => k σ ≤ (i : ℕ)) (by
    intro i hi j hj
    have hi' : ¬ k σ ≤ (i : ℕ) := hi
    have hj' : k σ ≤ (j : ℕ) := hj
    exact (hg σ).2.2.2 i j (by omega) (by rw [Fin.lt_def]; omega))
  intro h0
  apply (hg σ).2.1
  rw [hd]
  exact mul_eq_zero_of_left h0 _

theorem row_ne_zero {h : Mat m K} (hh : Par k ⊤ h) (hk : k τ < m τ) :
    (fun j : Rest m k τ => h τ ⟨k τ, hk⟩ j.1) ≠ 0 := by
  intro h0
  exact det_submatrix_rest_ne_zero hh τ (Matrix.det_eq_zero_of_row_eq_zero ⟨⟨k τ, hk⟩, le_refl _⟩ fun j => congrFun h0 j)

theorem par_succ_iff {h G : Mat m K} (hh : Par k ⊤ h) (hG : Par k ⊤ G) (hk : k τ < m τ) (h1 : k' τ = k τ + 1)
    (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ') :
    Par k' ⊤ (h * G⁻¹) ↔ ∃ t : K, ∀ j : Rest m k τ, h τ ⟨k τ, hk⟩ j.1 = t * G τ ⟨k τ, hk⟩ j.1 := by
  have hX : Par k ⊤ (h * G⁻¹) := hh.mul hG.inv
  have hXG : h * G⁻¹ * G = h := by rw [mul_assoc, Mat.inv_mul hG.det_ne, mul_one]
  have hrow : ∀ j : Rest m k τ,
      h τ ⟨k τ, hk⟩ j.1 = ∑ l : Rest m k τ, (h * G⁻¹) τ ⟨k τ, hk⟩ l.1 * G τ l.1 j.1 := by
    intro j
    rw [← mul_apply_rest (h * G⁻¹) hG, hXG]
  constructor
  · intro hP
    refine ⟨(h * G⁻¹) τ ⟨k τ, hk⟩ ⟨k τ, hk⟩, fun j => ?_⟩
    rw [hrow j, Finset.sum_eq_single (⟨⟨k τ, hk⟩, le_refl _⟩ : Rest m k τ)]
    · intro l _ hl
      have hl2 : k τ ≤ (l.1 : ℕ) := l.2
      have hl3 : (l.1 : ℕ) ≠ k τ := fun e => hl (Subtype.ext (Fin.ext e))
      have hlt : (⟨k τ, hk⟩ : Fin (m τ)) < l.1 := by rw [Fin.lt_def]; show k τ < (l.1 : ℕ); omega
      rw [(hP τ).2.2.2 ⟨k τ, hk⟩ l.1 (by show k τ < k' τ; omega) hlt, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rintro ⟨t, ht⟩
    have hv : Matrix.vecMul (fun l : Rest m k τ => (h * G⁻¹) τ ⟨k τ, hk⟩ l.1 -
        if l = (⟨⟨k τ, hk⟩, le_refl _⟩ : Rest m k τ) then t else 0)
        ((G τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ))) = 0 := by
      funext j
      have e := hrow j
      rw [ht j] at e
      simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Pi.zero_apply, sub_mul,
        Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← e, sub_self]
    have hv0 := Matrix.eq_zero_of_vecMul_eq_zero (det_submatrix_rest_ne_zero hG τ) hv
    intro σ
    refine ⟨fun _ _ => Subring.mem_top _, hX.det_ne σ, Subring.mem_top _, ?_⟩
    intro i j hi hij
    by_cases hσ : σ = τ
    · subst hσ
      by_cases hik : (i : ℕ) < k σ
      · exact (hX σ).2.2.2 i j hik hij
      · have hi' : (i : ℕ) = k σ := by omega
        have hj : k σ ≤ (j : ℕ) := by rw [Fin.lt_def] at hij; omega
        have hne : (⟨j, hj⟩ : Rest m k σ) ≠ ⟨⟨k σ, hk⟩, le_refl _⟩ := by
          intro e
          have e' := congrArg (fun x : Rest m k σ => (x.1 : ℕ)) e
          simp only at e'
          rw [Fin.lt_def] at hij
          omega
        have e := congrFun hv0 ⟨j, hj⟩
        simp only [hne, if_false, sub_zero, Pi.zero_apply] at e
        have hieq : i = ⟨k σ, hk⟩ := Fin.ext hi'
        subst hieq
        exact e
    · exact (hX σ).2.2.2 i j (by rw [← h2 σ hσ]; exact hi) hij

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

theorem row_eq {φ : Ω →ₐ[F] Ω'} {O : Subring Ω} (hk : k τ < m τ) {A₀ A : Mat m Ω} (hA : ∀ τ, (A τ).det ≠ 0)
    (hP : Par k O (A * A₀⁻¹)) (hd : (dualBlock k τ A₀ A).det ≠ 0) {s : Rest m k τ → Ω'} {A' : Mat m Ω'} {a : Ω'}
    (ha : ∀ j : Rest m k τ, (A' * (A₀.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1 = a * s j) (j : Rest m k τ) :
    (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1 = a * ((dualBlock k τ A₀ A).map φ).mulVec s j := by
  have hPφ : Par k ⊤ ((A * A₀⁻¹).map φ) := hP.map (φ : Ω →+* Ω') fun _ _ => Subring.mem_top _
  have hAφ : ∀ σ, (A.map φ σ).det ≠ 0 := fun σ => by
    rw [show (A.map φ σ).det = φ (A σ).det from Mat.det_map A (φ : Ω →+* Ω') σ]
    exact (map_ne_zero φ).2 (hA σ)
  have hmap : (A * A₀⁻¹).map φ = A.map φ * (A₀.map φ)⁻¹ := by
    rw [show (A * A₀⁻¹).map φ = A.map φ * A₀⁻¹.map φ from Mat.map_mul A A₀⁻¹ (φ : Ω →+* Ω'),
      show A₀⁻¹.map φ = (A₀.map φ)⁻¹ from Mat.map_inv A₀ (φ : Ω →+* Ω')]
  have hZ : A' * (A.map φ)⁻¹ * (A * A₀⁻¹).map φ = A' * (A₀.map φ)⁻¹ := by
    rw [hmap, mul_assoc, ← mul_assoc (A.map φ)⁻¹, Mat.inv_mul hAφ, one_mul]
  have hNd := det_submatrix_rest_ne_zero hPφ τ
  have hrow : Matrix.vecMul (fun l : Rest m k τ => (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ l.1)
      ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ))) = a • s := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul, ← ha j, ← hZ, mul_apply_rest _ hPφ]
    rfl
  have hz : (fun l : Rest m k τ => (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ l.1) =
      a • Matrix.vecMul s ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹ := by
    rw [← Matrix.smul_vecMul, ← hrow, Matrix.vecMul_vecMul,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hNd), Matrix.vecMul_one]
  have hmul : (((A * A₀⁻¹) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ))).map φ * (((A * A₀⁻¹) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_submatrix_rest_ne_zero hP τ)),
      Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hinv : (((A * A₀⁻¹) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹.map φ = ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹ := (Matrix.inv_eq_right_inv hmul).symm
  have hfin : Matrix.vecMul s ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹ = Matrix.mulVec ((dualBlock k τ A₀ A).map φ) s := by
    rw [← Matrix.mulVec_transpose, ← hinv]
    try rfl
  rw [← hfin]
  exact congrFun hz j

theorem existsUnique_bears (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι]
    (m k k' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω)
    (EE : M.Lat (Rest m k τ)) (s : Rest m k τ → Ω') (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (hA₀ : A₀ ∈ S.S (genericPoint M.Z))
    (hE : ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)))
    (hP : ProjPoints M EE M' φ f s) (hS : ∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z')
    (K : Type) [Field K] (x : Sp K ⟶ M.Z) (A : Mat m Ω) (hA : A ∈ S.S (x (IsLocalRing.closedPoint K)))
    (h : Mat m K) (hh : Par k ⊤ h) : ∃! p : Sp K ⟶ M'.Z, p ≫ f = x ∧ Bears S' φ A h p := by
  have hB := hE _ A hA
  have hA0P : Par k (M.O (genericPoint M.Z)).toSubring (A * A₀⁻¹) :=
    (Fr.mem_iff hA₀).1 (Fr.mem_genericPoint hA)
  have hc : (fun j : Rest m k τ => h τ ⟨k τ, hk⟩ j.1) ≠ 0 := row_ne_zero hh hk
  obtain ⟨p, ⟨hpf, hp⟩, huniq⟩ := hP.lifts K x (dualBlock k τ A₀ A) hB.1 hB.2 _ hc
  have key : ∀ q : Sp K ⟶ M'.Z, q ≫ f = x → (Bears S' φ A h q ↔
      ∃ i, M'.Div (((dualBlock k τ A₀ A).map φ).mulVec s) i (q (IsLocalRing.closedPoint K)) ∧
        ∀ j, h τ ⟨k τ, hk⟩ j.1 = h τ ⟨k τ, hk⟩ i.1 * M'.val q
          (((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s i)) := by
    intro q hqf
    have hfq : f (q (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
      rw [← hqf]
      first | rfl | simp
    have hsp : ∀ w, q w ⤳ q (IsLocalRing.closedPoint K) :=
      RatModel.specializes_of_range_eq (RatModel.range_eq_singleton q _)
    have hunit : ∀ y : Ω', y ∈ M'.O (q (IsLocalRing.closedPoint K)) →
        (M'.val q y ≠ 0 ↔ y ≠ 0 ∧ y⁻¹ ∈ M'.O (q (IsLocalRing.closedPoint K))) := fun y hy =>
      (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton q _) ⟨y, hy⟩).trans
        (RatModel.isUnit_O_iff _)
    have hstep : ∀ A' ∈ S'.S (q (IsLocalRing.closedPoint K)),
        Par k (M'.O (q (IsLocalRing.closedPoint K))).toSubring (A' * (A.map φ)⁻¹) ∧
        ∃ a : Ω', ∀ j : Rest m k τ, (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1 =
          a * ((dualBlock k τ A₀ A).map φ).mulVec s j := by
      intro A' hA'
      rw [hS] at hA'
      obtain ⟨hpar, a, ha⟩ := hA'
      exact ⟨hpar A (by rw [hfq]; exact hA), a,
        fun j => row_eq hk (fun σ => Fr.det_ne hA σ) hA0P hB.1 ha j⟩
    have hW : ∀ A' ∈ S'.S (q (IsLocalRing.closedPoint K)),
        Par k ⊤ ((A' * (A.map φ)⁻¹).map (M'.val q)) := fun A' hA' =>
      (hstep A' hA').1.map_of (M'.val q)
        (RatModel.valHom q (q (IsLocalRing.closedPoint K)) (RatModel.range_eq_singleton q _))
        (fun y => (RatModel.valHom_apply _ _ _ y).symm)
    unfold Bears
    constructor
    · rintro ⟨A', hA', hpar⟩
      obtain ⟨hX, a, ha⟩ := hstep A' hA'
      have hmem : ∀ j : Rest m k τ, a * ((dualBlock k τ A₀ A).map φ).mulVec s j ∈
          M'.O (q (IsLocalRing.closedPoint K)) := fun j => by
        have hj := (hX τ).1 ⟨k τ, hk⟩ j.1
        rw [ha j] at hj
        exact hj
      obtain ⟨t, ht⟩ := (par_succ_iff hh (hW A' hA') hk h1 h2).1 hpar
      obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 (row_ne_zero (hW A' hA') hk)
      have hu : M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀) ≠ 0 := by
        rw [← ha j₀]
        exact hj₀
      obtain ⟨hne0, hinv0⟩ := (hunit _ (hmem j₀)).1 hu
      have ha0 : a ≠ 0 := left_ne_zero_of_mul hne0
      have hv0 : ((dualBlock k τ A₀ A).map φ).mulVec s j₀ ≠ 0 := right_ne_zero_of_mul hne0
      have hdiv : ∀ j, ((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s j₀ ∈
          M'.O (q (IsLocalRing.closedPoint K)) := fun j => by
        have e : ((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s j₀ =
            a * ((dualBlock k τ A₀ A).map φ).mulVec s j * (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀)⁻¹ := by
          field_simp
        rw [e]
        exact mul_mem (hmem j) hinv0
      refine ⟨j₀, ⟨hv0, hdiv⟩, fun j => ?_⟩
      have e2 : a * ((dualBlock k τ A₀ A).map φ).mulVec s j = a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀ *
          (((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s j₀) := by
        field_simp
      rw [ht j, ht j₀]
      show t * M'.val q ((A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1) =
        t * M'.val q ((A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j₀.1) * _
      rw [ha j, ha j₀, e2, RatModel.val_mul hsp (hmem j₀) (hdiv j), mul_assoc]
    · rintro ⟨i, ⟨hvi, hdivi⟩, hci⟩
      obtain ⟨A', hA'⟩ := S'.nonempty (q (IsLocalRing.closedPoint K))
      obtain ⟨hX, a, ha⟩ := hstep A' hA'
      have hmem : ∀ j : Rest m k τ, a * ((dualBlock k τ A₀ A).map φ).mulVec s j ∈
          M'.O (q (IsLocalRing.closedPoint K)) := fun j => by
        have hj := (hX τ).1 ⟨k τ, hk⟩ j.1
        rw [ha j] at hj
        exact hj
      obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 (row_ne_zero (hW A' hA') hk)
      have hu : M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀) ≠ 0 := by
        rw [← ha j₀]
        exact hj₀
      obtain ⟨hne0, hinv0⟩ := (hunit _ (hmem j₀)).1 hu
      have ha0 : a ≠ 0 := left_ne_zero_of_mul hne0
      have hv0 : ((dualBlock k τ A₀ A).map φ).mulVec s j₀ ≠ 0 := right_ne_zero_of_mul hne0
      have e3 : (a * ((dualBlock k τ A₀ A).map φ).mulVec s i)⁻¹ =
          ((dualBlock k τ A₀ A).map φ).mulVec s j₀ / ((dualBlock k τ A₀ A).map φ).mulVec s i *
            (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀)⁻¹ := by
        field_simp
      have hinvi : (a * ((dualBlock k τ A₀ A).map φ).mulVec s i)⁻¹ ∈ M'.O (q (IsLocalRing.closedPoint K)) := by
        rw [e3]
        exact mul_mem (hdivi j₀) hinv0
      have hui : M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s i) ≠ 0 :=
        (hunit _ (hmem i)).2 ⟨mul_ne_zero ha0 hvi, hinvi⟩
      refine ⟨A', hA', (par_succ_iff hh (hW A' hA') hk h1 h2).2
        ⟨h τ ⟨k τ, hk⟩ i.1 / M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s i), fun j => ?_⟩⟩
      show h τ ⟨k τ, hk⟩ j.1 = h τ ⟨k τ, hk⟩ i.1 / M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s i) *
        M'.val q ((A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1)
      have e2 : a * ((dualBlock k τ A₀ A).map φ).mulVec s j = a * ((dualBlock k τ A₀ A).map φ).mulVec s i *
          (((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s i) := by
        field_simp
      rw [ha j, e2, RatModel.val_mul hsp (hmem i) (hdivi j), hci j, ← mul_assoc, div_mul_cancel₀ _ hui]
  exact ⟨p, ⟨hpf, (key p hpf).2 hp⟩, fun q hq => huniq q ⟨hq.1, (key q hq.1).1 hq.2⟩⟩

end GlobalTheory.FlagBundle.StepLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinXSpectralRedivisionFullChoicesStatement
section
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finX_spectralRedivisionFullChoices : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X), FinX Y → FinX (reY Z Y) := by
  first | exact @GlobalTheory.Mem.SRe.finX_reY | exact GlobalTheory.Mem.SRe.finX_reY | (intros; apply GlobalTheory.Mem.SRe.finX_reY <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.CuspRep.CompUniq

theorem isotypic : ∀ (G H V W W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (s : H →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'), ρ.IsIrreducible → σ.IsIrreducible → σ'.IsIrreducible → (∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y)) → ∀ f : σ.IntertwiningMap (ρ.comp s), f ≠ 0 → (⨆ f : σ.IntertwiningMap (ρ.comp s), LinearMap.range f.toLinearMap) = ⊤ ∧ ∀ f' : σ'.IntertwiningMap (ρ.comp s), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
  intro G H V W W' _ _ _ _ _ _ _ _ ρ s σ σ' hρ hσ hσ' hc f hf
  have hP : GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s) = ⊤ := by
    rcases ((isIrreducible_iff ρ).1 hρ).2 (GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s)) (fun g v hv => by
      obtain ⟨u, hu⟩ := hc g
      have h1 := GlobalTheory.CuspRep.LocUniq.isoPart_comm σ (ρ.comp s) (ρ ((s u)⁻¹ * g)) (fun y x => by
        simp only [MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, (hu y).eq]) hv
      have h2 := GlobalTheory.CuspRep.LocUniq.isoPart_act σ (ρ.comp s) u h1
      rwa [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h2) with h | h
    · refine absurd ?_ hf
      apply Representation.IntertwiningMap.toLinearMap_injective
      refine LinearMap.ext fun v => ?_
      have h3 : f.toLinearMap v ∈ GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s) :=
        Submodule.mem_iSup_of_mem f ⟨v, rfl⟩
      rw [h] at h3
      rw [(Submodule.mem_bot ℂ).1 h3]
      rfl
    · exact h
  refine ⟨hP, fun f' hf' => ?_⟩
  haveI := hσ
  haveI := hσ'
  exact GlobalTheory.CuspRep.LocUniq.equiv_of_isoPart σ σ' (ρ.comp s) hP f' hf'

end GlobalTheory.CuspRep.CompUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAffineSpaceCoveredMorphism
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle

theorem ProjBundle.affCover (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J]
    (EE : M.Lat J) (s : J → Ω') (h : ProjBundle M EE M' φ f s) : AffCover M M' φ f (Fintype.card J - 1) := by
  refine ⟨h.hom, fun z' => ?_⟩
  obtain ⟨U₀, b, hz, hb, hE⟩ := EE.loc (f z')
  obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := U₀) hz
  obtain ⟨hc, hch⟩ := h.chart W b hW ⟨_, hzW⟩ fun z hzz => hE z (hle hzz)
  obtain ⟨i, hi⟩ := hc z' hzW
  obtain ⟨U, hU, hUe, hR⟩ := hch i hi.1
  have hcard : Fintype.card {j // j ≠ i} = Fintype.card J - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  let e : Fin (Fintype.card J - 1) ≃ {j // j ≠ i} := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ y, y ∈ U ↔ f y ∈ W ∧ M'.Div ((b.map φ).mulVec s) i y := fun y =>
    Set.ext_iff.1 hUe y
  refine ⟨U, W, fun k => (b.map φ).mulVec s (e k).1 / (b.map φ).mulVec s i, hU, hW, (hmem z').2 ⟨hzW, hi⟩,
    fun y hy => ((hmem y).1 hy).1, fun P hP => ?_, ?_⟩
  · apply MvPolynomial.rename_injective e e.injective
    rw [map_zero]
    refine (h.gen b hb i).2 _ ?_
    rw [MvPolynomial.eval₂_rename]
    exact hP
  · rw [hR]
    refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_mono (Set.union_subset_union_right _ ?_))
    · rintro x (hx | ⟨j, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inl hx)
      · by_cases hj : j = i
        · subst hj
          show _ / _ ∈ _
          rw [div_self hi.1]
          exact one_mem _
        · refine Algebra.subset_adjoin (Or.inr ⟨e.symm ⟨j, hj⟩, ?_⟩)
          simp only [Equiv.apply_symm_apply]
    · rintro _ ⟨k, rfl⟩
      exact ⟨(e k).1, rfl⟩

end GlobalTheory.FlagBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIffStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nefFib_pow_iff' : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (L : HermLB p) (m : ℕ), 0 < m → (ArInt.NefFib (L.pow m) ↔ ArInt.NefFib L) := by
  first | exact @GlobalTheory.ArInt.nefFib_pow_iff | exact GlobalTheory.ArInt.nefFib_pow_iff | (intros; apply GlobalTheory.ArInt.nefFib_pow_iff <;> assumption)
end

