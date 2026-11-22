import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.DefLift.BilFischer

variable {σ : Type} [Fintype σ]

def wt (α : σ →₀ ℕ) : ℂ := ∏ v, ((α v).factorial : ℂ)

theorem wt_ne_zero (α : σ →₀ ℕ) : wt α ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

theorem wt_zero : wt (0 : σ →₀ ℕ) = 1 := by simp [wt]

theorem wt_add_single (α : σ →₀ ℕ) (v : σ) : wt (α + Finsupp.single v 1) = wt α * ((α v : ℂ) + 1) := by
  classical
  unfold wt
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v),
    ← Finset.mul_prod_erase _ (fun x => ((α x).factorial : ℂ)) (Finset.mem_univ v)]
  have h3 : ∏ x ∈ Finset.univ.erase v, (((α + Finsupp.single v 1 : σ →₀ ℕ) x).factorial : ℂ) =
      ∏ x ∈ Finset.univ.erase v, ((α x).factorial : ℂ) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxv : x ≠ v := Finset.ne_of_mem_erase hx
    simp [Finsupp.single_apply, Ne.symm hxv]
  rw [h3]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

def pair : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  (basisMonomials σ ℂ).constr ℂ fun α => wt α • lcoeff ℂ α

theorem pair_monomial_one (α : σ →₀ ℕ) (Q : MvPolynomial σ ℂ) :
    pair (monomial α 1) Q = wt α * coeff α Q := by
  have := (basisMonomials σ ℂ).constr_basis ℂ (fun α => wt α • lcoeff ℂ α) α
  rw [coe_basisMonomials] at this
  unfold pair
  rw [this]
  simp

theorem pair_monomial (α : σ →₀ ℕ) (c : ℂ) (Q : MvPolynomial σ ℂ) :
    pair (monomial α c) Q = c * (wt α * coeff α Q) := by
  have : (monomial α c : MvPolynomial σ ℂ) = c • monomial α 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply, pair_monomial_one, smul_eq_mul]

theorem pair_mul_X (P Q : MvPolynomial σ ℂ) (v : σ) : pair (P * X v) Q = pair P (pderiv v Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [X, monomial_mul, mul_one, pair_monomial, pair_monomial, coeff_pderiv, wt_add_single]
    ring
  | add P P' h h' => simp only [add_mul, map_add, LinearMap.add_apply, h, h']

def lin (A : σ → σ → ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun v => ∑ w, A v w • X w

theorem lin_X (A : σ → σ → ℂ) (v : σ) : lin A (X v) = ∑ w, A v w • X w := by
  simp [lin]

theorem pderiv_lin_X (A : σ → σ → ℂ) (v u : σ) : pderiv v (lin A (X u)) = C (A u v) := by
  classical
  rw [lin_X, map_sum, Finset.sum_eq_single v]
  · simp [smul_eq_C_mul]
  · intro w _ hw
    simp [pderiv_X, Pi.single_apply, hw]
  · simp

theorem pderiv_lin (A : σ → σ → ℂ) (v : σ) (Q : MvPolynomial σ ℂ) :
    pderiv v (lin A Q) = ∑ w, A w v • lin A (pderiv w Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp [lin]
  | add P P' h h' => simp only [map_add, h, h', smul_add, Finset.sum_add_distrib]
  | mul_X P u h =>
    rw [map_mul, Derivation.leibniz, h, pderiv_lin_X]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, smul_add, Finset.sum_add_distrib,
      Finset.mul_sum, mul_smul_comm]
    congr 1
    rw [Finset.sum_eq_single u]
    · simp [smul_eq_C_mul, mul_comm]
    · intro w _ hw
      simp [pderiv_X, Pi.single_apply, hw, Ne.symm hw]
    · simp

theorem coeff_zero_lin (A : σ → σ → ℂ) (Q : MvPolynomial σ ℂ) : coeff 0 (lin A Q) = coeff 0 Q := by
  change constantCoeff (lin A Q) = constantCoeff Q
  induction Q using MvPolynomial.induction_on with
  | C c => simp [lin]
  | add P P' h h' => simp only [map_add, h, h']
  | mul_X P u h => simp [lin_X, map_sum, smul_eq_C_mul]

theorem pair_lin (A : σ → σ → ℂ) (P Q : MvPolynomial σ ℂ) :
    pair (lin A P) Q = pair P (lin (fun v w => A w v) Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    have : lin A (C c) = C c := by simp [lin]
    rw [this, C_apply, pair_monomial, pair_monomial, coeff_zero_lin]
  | add P P' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | mul_X P u h =>
    rw [pair_mul_X, pderiv_lin, map_mul, lin_X, Finset.mul_sum, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mul_smul_comm, map_smul, map_smul, LinearMap.smul_apply, pair_mul_X, h]

theorem pair_nondeg (Q : MvPolynomial σ ℂ) (h : ∀ P, pair P Q = 0) : Q = 0 := by
  ext α
  have := h (monomial α 1)
  rw [pair_monomial_one] at this
  simpa [wt_ne_zero] using this

theorem pair_rep (ℓ : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (d : ℕ)
    (h : ∀ α : σ →₀ ℕ, d < α.degree → ℓ (monomial α 1) = 0) : ∃ Q, ∀ P, pair P Q = ℓ P := by
  classical
  have hfin : {α : σ →₀ ℕ | α.degree ≤ d}.Finite := Finsupp.finite_of_degree_le d
  refine ⟨∑ α ∈ hfin.toFinset, monomial α (ℓ (monomial α 1) / wt α), fun P => ?_⟩
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    have : (monomial α c : MvPolynomial σ ℂ) = c • monomial α 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [pair_monomial, this, map_smul, smul_eq_mul, coeff_sum]
    congr 1
    simp only [coeff_monomial, Finset.sum_ite_eq', Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    split_ifs with hd
    · exact mul_div_cancel₀ _ (wt_ne_zero α)
    · rw [h α (not_le.1 hd), mul_zero]
  | add P P' h h' => simp only [map_add, LinearMap.add_apply, h, h']

open Classical in
theorem subst_eq_lin {ι : Type} [Fintype ι] {m n : ℕ} (a : ι → Matrix (Fin n) (Fin n) ℂ)
    (b : ι → Matrix (Fin m) (Fin m) ℂ) :
    subst a b = lin fun v w => if v.1 = w.1 then b v.1 w.2.1 v.2.1 * a v.1 v.2.2 w.2.2 else 0 := by
  unfold subst lin
  congr 1
  funext v
  rw [Fintype.sum_prod_type, Finset.sum_eq_single v.1, Fintype.sum_prod_type]
  · simp
  · intro τ _ hτ
    simp [Ne.symm hτ]
  · simp

theorem exists_pair (ι : Type) [Fintype ι] (m n : ℕ) :
    ∃ B : Pol ι m n →ₗ[ℂ] Pol ι m n →ₗ[ℂ] ℂ, (∀ Q, (∀ P, B P Q = 0) → Q = 0) ∧
      (∀ a b P Q, B (subst a b P) Q =
        B P (subst (fun τ => (a τ).transpose) (fun τ => (b τ).transpose) Q)) ∧
      ∀ (ℓ : Pol ι m n →ₗ[ℂ] ℂ) (d : ℕ),
        (∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → ℓ (MvPolynomial.monomial α 1) = 0) →
          ∃ Q, ∀ P, B P Q = ℓ P := by
  refine ⟨pair, pair_nondeg, fun a b P Q => ?_, pair_rep⟩
  rw [subst_eq_lin, subst_eq_lin, pair_lin]
  congr 3
  funext v w
  by_cases h : v.1 = w.1
  · simp [h]
  · simp [h, Ne.symm h]

end GlobalTheory.DefLift.BilFischer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColStableDisjoint
section
noncomputable section

open MvPolynomial GlobalTheory.MvPoly GlobalTheory.Harm Matrix

namespace GlobalTheory.DefLift

namespace Compl

theorem exists_sub_perp {E : Type*} [AddCommGroup E] [Module ℂ E] (B : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x, B x x = 0 → x = 0) (W : Submodule ℂ E) [FiniteDimensional ℂ W] (P : E) :
    ∃ Q ∈ W, ∀ w ∈ W, B (P - Q) w = 0 := by
  let b := Module.finBasis ℂ W
  let L : E →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := LinearMap.pi fun i => B.flip (b i)
  have hL (P) (h : L P = 0) (w) (hw : w ∈ W) : B P w = 0 := by
    have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)
    rw [map_sum, Submodule.subtype_apply] at this
    change _ = w at this
    rw [← this, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, map_smulₛₗ]
    exact smul_eq_zero_of_right _ (congrFun h i)
  have hinj : Function.Injective (L ∘ₗ W.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (hB _ (hL x hx x x.2))
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
    (L P)
  exact ⟨x, x.2, hL _ (by rw [map_sub, ← hx]; simp)⟩

theorem totalDegree_aeval_le {σ : Type*} (f : σ → MvPolynomial σ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (aeval f P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.AevalTotalDegreeBound.main
  | exact _root_.GlobalTheory.AevalTotalDegreeBound.main
  | (apply _root_.GlobalTheory.AevalTotalDegreeBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalTotalDegreeBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalTotalDegreeBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalTotalDegreeBound.main ..)

variable {ι : Type} {m n : ℕ}

theorem totalDegree_subst_le (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ) (P : Pol ι m n) :
    (subst a b P).totalDegree ≤ P.totalDegree := by
  refine totalDegree_aeval_le _ (fun v => ?_) P
  refine totalDegree_finsetSum_le fun i _ => totalDegree_finsetSum_le fun c _ => ?_
  exact (totalDegree_smul_le _ _).trans (totalDegree_X _).le

theorem totalDegree_colSub_le (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) (P : Pol ι m n) :
    (colSub m τ g P).totalDegree ≤ P.totalDegree := by
  unfold colSub
  rw [AlgHom.toLinearMap_apply]
  exact totalDegree_subst_le _ _ _

theorem fockInner_subst [Fintype ι] (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ)
    (P Q : Pol ι m n) :
    fockInner (subst a b P) Q = fockInner P (subst (fun τ => star (a τ)) (fun τ => star (b τ)) Q) := by
  classical
  refine fockInner_algHom_of_linear _ _
    (fun v w => if v.1 = w.1 then b v.1 w.2.1 v.2.1 * a v.1 v.2.2 w.2.2 else 0) ?_ ?_ P Q
  · rintro ⟨t, i, k⟩
    simp [subst, Fintype.sum_prod_type]
  · rintro ⟨t, i, k⟩
    simp [subst, Fintype.sum_prod_type, apply_ite star, mul_comm]

theorem fockInner_colSub [Fintype ι] (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) (P Q : Pol ι m n) :
    fockInner (colSub m τ g P) Q = fockInner P (colSub m τ g⁻¹ Q) := by
  unfold colSub
  simp only [AlgHom.toLinearMap_apply]
  rw [fockInner_subst]
  congr 3
  · funext ρ
    split_ifs
    · rfl
    · simp
  · funext ρ
    simp

end Compl

open Compl in

theorem exists_colStable_disjoint (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (U W : Submodule ℂ (X →ₗ[ℂ] Pol ι m n))
    (hU : ∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) (hW : ∀ Φ ∈ W, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ W) (hlt : U < W) :
    ∃ U' : Submodule ℂ (X →ₗ[ℂ] Pol ι m n), U' ≠ ⊥ ∧ U' ≤ W ∧ U ⊓ U' = ⊥ ∧
      ∀ Φ ∈ U', ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U' := by
  classical
  let b := Module.finBasis ℂ X
  let B : (X →ₗ[ℂ] Pol ι m n) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n) →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun Φ Ψ => ∑ i, fockInner (Φ (b i)) (Ψ (b i)))
      (fun _ _ _ => by simp [fockInner_add_left, Finset.sum_add_distrib])
      (fun _ _ _ => by simp [fockInner_smul_left, Finset.mul_sum])
      (fun _ _ _ => by simp [fockInner_add_right, Finset.sum_add_distrib])
      (fun _ _ _ => by simp [fockInner_smul_right, Finset.mul_sum])
  have hBa (Φ Ψ) : B Φ Ψ = ∑ i, fockInner (Φ (b i)) (Ψ (b i)) := rfl
  have hB (Φ) (h : B Φ Φ = 0) : Φ = 0 := by
    rw [hBa] at h
    simp only [fockInner_self] at h
    have h' : ∑ i, fockNormSq (Φ (b i)) = 0 := by
      rw [← RCLike.ofReal_sum] at h
      exact RCLike.ofReal_eq_zero.mp h
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => fockNormSq_nonneg _] at h'
    exact b.ext fun i => fockNormSq_eq_zero.mp (h' i (Finset.mem_univ i))
  have hadj (Φ Ψ τ g) : B (colSub m τ g ∘ₗ Φ) Ψ = B Φ (colSub m τ g⁻¹ ∘ₗ Ψ) := by
    simp only [hBa, LinearMap.comp_apply, fockInner_colSub]
  clear hBa
  clear_value B
  obtain ⟨β, hβW, hβU⟩ := SetLike.exists_of_lt hlt
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ∀ i, (β (b i)).totalDegree ≤ d :=
    ⟨_, fun i => Finset.le_sup (f := fun i => (β (b i)).totalDegree) (Finset.mem_univ i)⟩
  obtain ⟨R, hRf, hR⟩ : ∃ R : Submodule ℂ (Pol ι m n), FiniteDimensional ℂ R ∧ ∀ P, P ∈ R ↔ P.totalDegree ≤ d :=
    ⟨restrictTotalDegree (ι × Fin m × Fin n) ℂ d, inferInstance, fun P => mem_restrictTotalDegree _ _ _⟩
  let ψ : (X →ₗ[ℂ] R) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n) :=
    { toFun := fun Ψ => R.subtype ∘ₗ Ψ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let D : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := LinearMap.range ψ
  have hD (Φ) : Φ ∈ D ↔ ∀ x, Φ x ∈ R := by
    constructor
    · rintro ⟨Ψ, rfl⟩ x
      exact (Ψ x).2
    · intro h
      exact ⟨Φ.codRestrict R h, rfl⟩
  haveI : FiniteDimensional ℂ D := inferInstance
  clear_value D
  have hDs (Φ) (h : Φ ∈ D) (τ g) : colSub m τ g ∘ₗ Φ ∈ D := by
    rw [hD] at h ⊢
    intro x
    have := h x
    rw [hR] at this ⊢
    rw [LinearMap.comp_apply]
    exact (totalDegree_colSub_le τ g _).trans this
  have hβD : β ∈ D := by
    rw [hD]
    intro x
    rw [← b.sum_repr x, map_sum]
    refine R.sum_mem fun i _ => ?_
    rw [map_smul]
    exact R.smul_mem _ ((hR _).2 (hd i))
  haveI : FiniteDimensional ℂ (U ⊓ D : Submodule ℂ _) := Submodule.finiteDimensional_inf_right _ _
  let T : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := ⨅ w ∈ U ⊓ D, LinearMap.ker (B.flip w)
  have hT (Φ) : Φ ∈ T ↔ ∀ w ∈ U ⊓ D, B Φ w = 0 := by simp [T, Submodule.mem_iInf]
  obtain ⟨Q, hQ, hperp⟩ := exists_sub_perp B hB (U ⊓ D) β
  refine ⟨W ⊓ D ⊓ T, ?_, inf_le_left.trans inf_le_left, ?_, ?_⟩
  · intro h
    have hm : β - Q ∈ W ⊓ D ⊓ T :=
      ⟨⟨W.sub_mem hβW (hlt.le hQ.1), D.sub_mem hβD hQ.2⟩, (hT _).2 hperp⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at hm
    exact hβU (hm ▸ hQ.1)
  · rw [Submodule.eq_bot_iff]
    rintro Φ ⟨h1, ⟨-, h2⟩, h3⟩
    exact hB Φ ((hT Φ).1 h3 Φ ⟨h1, h2⟩)
  · rintro Φ ⟨⟨h1, h2⟩, h3⟩ τ g
    refine ⟨⟨hW Φ h1 τ g, hDs Φ h2 τ g⟩, (hT _).2 fun w hw => ?_⟩
    rw [hadj]
    exact (hT Φ).1 h3 _ ⟨hU w hw.1 τ _, hDs w hw.2 τ _⟩

end GlobalTheory.DefLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDegreeBoundOfRowUnitaryInvariantPairing
section
noncomputable section

open GlobalTheory.DefLift

namespace GlobalTheory.RowSupport

theorem exp_I_pow_injective : Function.Injective fun e : ℕ => Complex.exp Complex.I ^ e := by
  intro a b h
  simp only [← Complex.exp_nat_mul] at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have h2 : (a : ℝ) = b + k * (2 * Real.pi) := by
    have := congrArg Complex.im hk
    simpa using this
  by_cases h0 : k = 0
  · subst h0
    exact_mod_cast (by simpa using h2 : (a : ℝ) = b)
  · exfalso
    have h3 : (2 * k : ℤ) ≠ 0 := mul_ne_zero two_ne_zero h0
    refine (irrational_pi.intCast_mul h3).ne_int ((a : ℤ) - b) ?_
    push_cast
    linarith

def scal (m : ℕ) : Matrix.unitaryGroup (Fin m) ℂ :=
  ⟨Complex.exp Complex.I • 1, by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, mul_one]
    have : Complex.exp Complex.I * star (Complex.exp Complex.I) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp
    rw [this, one_smul]⟩

open Classical in
theorem rowSub_scal {ι : Type} [Fintype ι] {m n : ℕ} (τ : ι) (α : ι × Fin m × Fin n →₀ ℕ) :
    rowSub n τ (scal m) (MvPolynomial.monomial α 1) =
      Complex.exp Complex.I ^ (∑ v, if v.1 = τ then α v else 0) • MvPolynomial.monomial α 1 := by
  have hv : ∀ v : ι × Fin m × Fin n,
      (∑ i, ∑ c, ((if v.1 = τ then (scal m : Matrix (Fin m) (Fin m) ℂ) else 1) i v.2.1 *
        (1 : Matrix (Fin n) (Fin n) ℂ) v.2.2 c) • (MvPolynomial.X (v.1, i, c) : Pol ι m n)) =
      (if v.1 = τ then Complex.exp Complex.I else 1) • MvPolynomial.X v := by
    rintro ⟨ρ, j, d⟩
    by_cases h : ρ = τ
    · simp [h, scal, Matrix.one_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp [h, Matrix.one_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
  unfold rowSub subst
  rw [AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial, map_one, one_mul, MvPolynomial.monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp only [hv, smul_pow]
  rw [Finset.prod_smul, ← Finset.prod_pow_eq_pow_sum]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  split_ifs <;> simp

theorem exists_degree_bound (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X) (β : Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] ℂ)
    (h : ∀ τ u P x, β (rowSub n τ u P) (π τ u x) = β P x) :
    ∃ d : ℕ, ∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → β (MvPolynomial.monomial α 1) = 0 := by
  classical
  have hfin : ∀ τ, ∃ d : ℕ, ∀ e : ℕ,
      Module.End.HasEigenvalue (LinearMap.dualMap (π τ (scal m)) : Module.End ℂ (Module.Dual ℂ X))
        (Complex.exp Complex.I ^ e)⁻¹ → e ≤ d := by
    intro τ
    have h1 := Module.End.finite_hasEigenvalue (LinearMap.dualMap (π τ (scal m)) : Module.End ℂ (Module.Dual ℂ X))
    have h2 := h1.preimage (f := fun e : ℕ => (Complex.exp Complex.I ^ e)⁻¹)
      (inv_injective.comp exp_I_pow_injective).injOn
    obtain ⟨d, hd⟩ := h2.bddAbove
    exact ⟨d, fun e he => hd he⟩
  choose d hd using hfin
  refine ⟨∑ τ, d τ, fun α hα => ?_⟩
  by_contra hne
  have hdeg : α.degree = ∑ τ, ∑ v, if v.1 = τ then α v else 0 := by
    rw [Finset.sum_comm, Finsupp.degree_eq_sum]
    simp
  refine absurd hα (not_lt.2 ?_)
  rw [hdeg]
  refine Finset.sum_le_sum fun τ _ => hd τ _ ?_
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := β (MvPolynomial.monomial α 1)) ⟨?_, hne⟩
  rw [Module.End.mem_eigenspace_iff]
  ext x
  have := h τ (scal m) (MvPolynomial.monomial α 1) x
  rw [rowSub_scal, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  rw [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ (Complex.exp_ne_zero _))]
  convert this

end GlobalTheory.RowSupport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimePairBoxBounds
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem boundsAtX_mono_const {x eps C C' : ℝ} {f : ℕ → ℂ} {M : ℕ} (hx : 0 ≤ Real.log x) (hC : C ≤ C')
    (h : BoundsAtX x eps C f M) : BoundsAtX x eps C' f M := by
  intro N _ χ hχ
  obtain ⟨h1, h2⟩ := h N χ hχ
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right hC hx)⟩

theorem log_four_mul_nqd_le {x eps : ℝ} {n q d : ℕ} (he : 0 < eps) (he' : eps < 1 / 52)
    (hx : Real.exp 5 ≤ x) (hn1 : 1 ≤ n) (hq1 : 1 ≤ q) (hd1 : 1 ≤ d)
    (hn : (n : ℝ) ≤ 2 * x ^ (2 + 8 * eps)) (hq : (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps) (hd : (d : ℝ) ≤ GlobalTheoryTheory.X2 x eps) :
    Real.log (4 * n * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 := by
  have hx0 : 0 < x := (Real.exp_pos 5).trans_le hx
  have hL : 5 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have hy : 1 ≤ x ^ (eps / 5) := Real.one_le_rpow hx1 (by positivity)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hlq : Real.log q ≤ x ^ (eps / 5) := (Real.log_le_iff_le_exp hq0).2 hq
  have hld : Real.log d ≤ x ^ (eps / 5) * Real.log x ^ 2 := (Real.log_le_iff_le_exp hd0).2 hd
  have hln : Real.log n ≤ Real.log 2 + (2 + 8 * eps) * Real.log x := by
    have := Real.log_le_log hn0 hn
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0] at this
  have h4 : Real.log 4 ≤ 3 := by have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have h2 : Real.log 2 ≤ 1 := by have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  rw [Real.log_mul (by positivity) hd0.ne', Real.log_mul (by positivity) hq0.ne',
    Real.log_mul (by norm_num) hn0.ne']
  have h3 : (2 + 8 * eps) * Real.log x ≤ 3 * Real.log x :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h5 : 5 * Real.log x ≤ Real.log x ^ 2 := by nlinarith
  have h6 : Real.log x ^ 2 - 1 ≤ x ^ (eps / 5) * (Real.log x ^ 2 - 1) :=
    le_mul_of_one_le_left (by linarith) hy
  nlinarith

theorem exists_q_d_box_bounds_rows : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∃ q d : ℕ, Boxq x eps q d ∧ QDq x eps C q d ∧ ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * x ^ (2 + 8 * eps) → Rowq x eps n q d := by
  intro p1 p2 p3 p4 p5 p6 p7 p8 eps he he'
  obtain ⟨x1, C1, hC1, H1⟩ := GlobalTheory.T.exists_prime_three_mod_eight_good p1 p2 p3 p4 p5 p6 p7 p8 eps he he'
  obtain ⟨x2, C2, hC2, H2⟩ := GlobalTheory.T.exists_prime_seven_mod_sixteen_good p1 p2 p3 p4 p5 p6 p7 p8 eps he he'
  refine ⟨max (max x1 x2) (Real.exp 5), max C1 C2, lt_max_of_lt_left hC1, fun x hx => ?_⟩
  have hx1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx2 : x2 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx5 : Real.exp 5 ≤ x := (le_max_right _ _).trans hx
  have hL : 0 ≤ Real.log x := Real.log_nonneg (le_trans (Real.one_le_exp (by norm_num)) hx5)
  obtain ⟨q, hq, hq8, hql, hqu, Hq⟩ := H1 x hx1
  obtain ⟨d, hd, hd16, hdl, hdu, hk, hsp, hg, hb1, hb2⟩ := H2 x hx2 q hq hq8 hql hqu
  obtain ⟨g1, g2, b0⟩ := Hq d hd (by omega) (by rintro rfl; omega)
  refine ⟨q, d, ⟨g1, g2, ?_, ?_, ?_, ?_⟩,
    ⟨boundsAtX_mono_const hL (le_max_left _ _) b0, boundsAtX_mono_const hL (le_max_right _ _) hb1,
      boundsAtX_mono_const hL (le_max_right _ _) hb2⟩, fun n hn1 hn =>
    ⟨hq, hq8, hql, hqu, hd, hd16, hdl, hdu, hk, hsp,
      log_four_mul_nqd_le he he' hx5 hn1 hq.one_le hd.one_le hn hqu hdu⟩⟩
  · simpa using hg 0 0
  · simpa using hg 0 1
  · simpa using hg 1 0
  · simpa using hg 1 1

end GlobalTheory.Mem.An
end

