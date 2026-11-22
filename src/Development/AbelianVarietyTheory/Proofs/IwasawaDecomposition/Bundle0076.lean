import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetTwistedConjugateIsKTypeOfReversed
section
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ConjTwist

variable {k : ℕ}

theorem Jm_allPos (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  simp [Formalism.REAL.Jm, allPos]

theorem mem_U_iff (g : Matrix (Fin k) (Fin k) ℂ) : g ∈ UJset (allPos k) ↔ gᴴ * g = 1 := by
  show gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) ↔ _
  rw [Jm_allPos, Matrix.mul_one]

theorem mem_K_iff (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Formalism.REAL.Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  rw [mem_U_iff]
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Formalism.REAL.Jm (allPos k) = Formalism.REAL.Jm (allPos k) * g) ↔ _
  rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

theorem map_star_mul (g h : Matrix (Fin k) (Fin k) ℂ) :
    (g * h).map star = g.map star * h.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem map_star_one : (1 : Matrix (Fin k) (Fin k) ℂ).map star = 1 :=
  Matrix.map_one _ (star_zero _) (star_one _)

theorem map_star_star (g : Matrix (Fin k) (Fin k) ℂ) : (g.map star).map star = g := by
  ext a b
  simp

theorem map_star_mem {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    g.map star ∈ UJset (allPos k) := by
  rw [mem_U_iff] at hg ⊢
  have h : (g.map star)ᴴ = gᴴ.map star := by
    ext a b
    simp
  rw [h, ← map_star_mul, hg, map_star_one]

theorem norm_det {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) : ‖g.det‖ = 1 := by
  rw [mem_U_iff] at hg
  have h := congrArg (fun M => ‖Matrix.det M‖) hg
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, Matrix.det_one,
    norm_one] at h
  nlinarith [norm_nonneg g.det]

theorem det_ne_zero {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) : g.det ≠ 0 := by
  intro h
  have := norm_det hg
  rw [h, norm_zero] at this
  exact zero_ne_one this

abbrev tor (θ : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem tor_map_star (θ : Fin k → ℝ) : (tor θ).map star = tor (fun a => -θ a) := by
  rw [tor, Matrix.diagonal_map (star_zero _)]
  congr 1
  funext a
  show (starRingEnd ℂ) _ = _
  rw [← Complex.exp_conj]
  simp

theorem tor_mem (θ : Fin k → ℝ) : tor θ ∈ UJset (allPos k) := by
  rw [mem_U_iff, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  show (starRingEnd ℂ) _ * _ = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem tor_det_zpow (θ : Fin k → ℝ) (x : ℤ) :
    (tor θ).det ^ x = Complex.exp (((∑ a, (x : ℝ) * θ a : ℝ) : ℂ) * Complex.I) := by
  rw [Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

def revMat (k : ℕ) : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun a b => if Fin.rev a = b then 1 else 0

theorem revMat_mul_self : revMat k * revMat k = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev a)]
  · simp [revMat, Matrix.one_apply]
  · intro c _ hc
    simp [revMat, hc.symm]
  · simp

theorem revMat_conjTranspose : (revMat k)ᴴ = revMat k := by
  ext a b
  simp only [revMat, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : Fin.rev a = b
  · subst h
    simp
  · have h' : ¬ Fin.rev b = a := fun h' => h (by rw [← h', Fin.rev_rev])
    simp [h, h']

theorem revMat_mem : revMat k ∈ UJset (allPos k) := by
  rw [mem_U_iff, revMat_conjTranspose, revMat_mul_self]

theorem tor_mul_revMat (θ : Fin k → ℝ) :
    tor θ * revMat k = revMat k * tor (fun a => θ (Fin.rev a)) := by
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, revMat, Matrix.of_apply]
  by_cases h : Fin.rev a = b
  · subst h
    simp
  · simp [h]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)}

theorem isWtOn_rev (hσ : IsURepOn (UJset (allPos k)) σ) {μ : Fin k → ℝ} {v : H}
    (hv : IsWtOn (Formalism.REAL.Kset (allPos k)) σ μ v) :
    IsWtOn (Formalism.REAL.Kset (allPos k)) σ (fun a => μ (Fin.rev a)) (σ (revMat k) v) := by
  intro θ _
  have h1 : σ (tor θ) (σ (revMat k) v) = σ (revMat k) (σ (tor fun a => θ (Fin.rev a)) v) := by
    have h2 := hσ.1.2 _ (tor_mem θ) _ revMat_mem
    have h3 := hσ.1.2 _ revMat_mem _ (tor_mem fun a => θ (Fin.rev a))
    rw [tor_mul_revMat, h3] at h2
    exact (congrArg (fun f : H →L[ℂ] H => f v) h2).symm
  refine h1.trans ?_
  rw [hv _ ((mem_K_iff _).2 (tor_mem _)), map_smul]
  congr 4
  rw [← Equiv.sum_comp Fin.revPerm]
  simp

theorem rev_ne_zero (hσ : IsURepOn (UJset (allPos k)) σ) {v : H} (hv : v ≠ 0) :
    σ (revMat k) v ≠ 0 := by
  rw [← norm_ne_zero_iff, hσ.2.1 _ revMat_mem, norm_ne_zero_iff]
  exact hv

theorem exp_split (x : ℤ) (μ θ : Fin k → ℝ) :
    Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) =
      (tor θ).det ^ x * Complex.exp (((∑ a, ((x : ℝ) - μ a) * -θ a : ℝ) : ℂ) * Complex.I) := by
  rw [tor_det_zpow, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  congr 3
  exact Finset.sum_congr rfl fun a _ => by ring

theorem isWtOn_twist_iff (x : ℤ) (μ : Fin k → ℝ) (v : H) :
    IsWtOn (Formalism.REAL.Kset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) μ v ↔
      IsWtOn (Formalism.REAL.Kset (allPos k)) σ (fun a => (x : ℝ) - μ a) v := by
  constructor
  · intro h θ _
    have h1 : (tor fun a => -θ a).det ^ x • σ ((tor fun a => -θ a).map star) v = _ :=
      h (fun a => -θ a) ((mem_K_iff _).2 (tor_mem _))
    rw [exp_split x, ← smul_smul, tor_map_star] at h1
    simp only [neg_neg] at h1
    exact smul_right_injective H (zpow_ne_zero x (det_ne_zero (tor_mem _))) h1
  · intro h θ _
    show (tor θ).det ^ x • σ ((tor θ).map star) v = _
    rw [exp_split x, ← smul_smul, tor_map_star, h _ ((mem_K_iff _).2 (tor_mem _))]

theorem stable_twist_iff (x : ℤ) (S : Submodule ℂ H) :
    IsKStableOn (allPos k) (fun g => g.det ^ x • σ (g.map star)) S ↔ IsKStableOn (allPos k) σ S := by
  constructor
  · intro h g hg v hv
    have hg' := map_star_mem ((mem_K_iff g).1 hg)
    have h1 : (g.map star).det ^ x • σ ((g.map star).map star) v ∈ S :=
      h _ ((mem_K_iff _).2 hg') v hv
    rw [map_star_star] at h1
    exact (S.smul_mem_iff (zpow_ne_zero x (det_ne_zero hg'))).1 h1
  · intro h g hg v hv
    exact S.smul_mem _ (h _ ((mem_K_iff _).2 (map_star_mem ((mem_K_iff g).1 hg))) v hv)

theorem isURepOn_twist (hσ : IsURepOn (UJset (allPos k)) σ) (x : ℤ) :
    IsURepOn (UJset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · simp only [Matrix.det_one, _root_.one_zpow, one_smul, map_star_one, hσ.1.1]
  · simp only [Matrix.det_mul, mul_zpow, map_star_mul]
    rw [hσ.1.2 _ (map_star_mem ha) _ (map_star_mem hb)]
    ext v
    simp [smul_smul, mul_comm]
  · simp only [ContinuousLinearMap.smul_apply, norm_smul, norm_zpow, norm_det hg, _root_.one_zpow,
      one_mul, hσ.2.1 _ (map_star_mem hg)]
  · simp only [ContinuousLinearMap.smul_apply]
    refine ContinuousOn.smul ?_ ?_
    · exact (continuous_id.matrix_det.continuousOn).zpow₀ x fun g hg => Or.inl (det_ne_zero hg)
    · exact (hσ.2.2 v).comp (continuous_id.matrix_map continuous_star).continuousOn
        fun g hg => map_star_mem hg

theorem cdom_rev (x : ℤ) (Λ μ : Fin k → ℝ)
    (h : CDom (allPos k) (fun a => (x : ℝ) - μ (Fin.rev a)) Λ) :
    CDom (allPos k) μ (fun a => (x : ℝ) - Λ (Fin.rev a)) := by
  obtain ⟨c, hc, he⟩ := h
  refine ⟨fun a b => c (Fin.rev b) (Fin.rev a), fun a b hab => ⟨?_, rfl⟩, ?_⟩
  · exact Fin.rev_lt_rev.1 (hc _ _ hab).1
  · funext i
    have h1 := congrFun he (Fin.rev i)
    simp only [Pi.sub_apply, Fin.rev_rev, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    have h2 : ∑ a, ∑ b, (c (Fin.rev b) (Fin.rev a) : ℝ) * Formalism.REAL.root a b i =
        -∑ a, ∑ b, (c a b : ℝ) * Formalism.REAL.root a b (Fin.rev i) := by
      rw [Finset.sum_comm, ← Equiv.sum_comp Fin.revPerm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Equiv.sum_comp Fin.revPerm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev, Formalism.REAL.root, Pi.sub_apply, Pi.single_apply,
        Fin.rev_eq_iff]
      ring
    rw [h2, ← h1]
    ring

theorem conj_twist_isKTypeOf : ∀ (k : ℕ) (Λ : Fin k → ℝ) (x : ℤ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ Λ ⊤ → IsURepOn (UJset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) ∧ IsKTypeOf (allPos k) (fun g => g.det ^ x • σ (g.map star)) (fun a => (x : ℝ) - Λ (Fin.rev a)) ⊤ := by
  intro k Λ x H _ _ _ σ hσ hK
  obtain ⟨hfd, -, hirr, ⟨v, -, hv0, hv⟩, hdom⟩ := hK
  refine ⟨isURepOn_twist hσ x, hfd, fun _ _ _ _ => trivial,
    fun S hS hst => hirr S hS ((stable_twist_iff x S).1 hst),
    ⟨σ (revMat k) v, trivial, rev_ne_zero hσ hv0, ?_⟩, fun μ w _ hw0 hw => ?_⟩
  · rw [isWtOn_twist_iff]
    simpa only [sub_sub_cancel] using isWtOn_rev hσ hv
  · rw [isWtOn_twist_iff] at hw
    exact cdom_rev x Λ μ (hdom _ _ trivial (rev_ne_zero hσ hw0) (isWtOn_rev hσ hw))

end GlobalTheory.ConjTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantPiTensorPolynomialBilinear
section
noncomputable section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

namespace GlobalTheory.CompactHowe.PolyTensor

open MvPolynomial

variable {ι σ : Type} [Fintype ι]

def prodRename [DecidableEq ι] :
    MultilinearMap ℂ (fun _ : ι => MvPolynomial σ ℂ) (MvPolynomial (ι × σ) ℂ) :=
  (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
    fun i => (rename (Prod.mk i) : MvPolynomial σ ℂ →ₐ[ℂ] _).toLinearMap

theorem prodRename_apply [DecidableEq ι] (P : ι → MvPolynomial σ ℂ) :
    prodRename P = ∏ i, rename (Prod.mk i) (P i) := by
  simp [prodRename]

theorem sum_mapDomain_apply (a : ι → σ →₀ ℕ) (j : ι) (s : σ) :
    (∑ i, Finsupp.mapDomain (Prod.mk i) (a i)) (j, s) = a j s := by
  classical
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single j]
  · exact Finsupp.mapDomain_apply (Prod.mk_right_injective j) _ _
  · intro i _ hi
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨t, ht⟩
    exact hi (congrArg Prod.fst ht)
  · simp

theorem prod_rename_monomial (a : ι → σ →₀ ℕ) :
    (∏ i, rename (Prod.mk i) (monomial (a i) (1 : ℂ)) : MvPolynomial (ι × σ) ℂ)
      = monomial (∑ i, Finsupp.mapDomain (Prod.mk i) (a i)) 1 := by
  simp only [rename_monomial]
  rw [monomial_sum_one]

def res (α : ι × σ →₀ ℕ) (i : ι) : σ →₀ ℕ :=
  Finsupp.comapDomain (Prod.mk i) α (Prod.mk_right_injective i).injOn

theorem res_sum (a : ι → σ →₀ ℕ) : res (∑ i, Finsupp.mapDomain (Prod.mk i) (a i)) = a := by
  funext j
  ext s
  exact sum_mapDomain_apply a j s

theorem sum_res (α : ι × σ →₀ ℕ) : ∑ i, Finsupp.mapDomain (Prod.mk i) (res α i) = α := by
  ext ⟨j, s⟩
  exact sum_mapDomain_apply (res α) j s

variable {A B : ι → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]

def tens (I : ∀ i, MvPolynomial σ ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) :
    MvPolynomial (ι × σ) ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i :=
  (basisMonomials (ι × σ) ℂ).constr ℂ fun α => PiTensorProduct.map fun i => I i (monomial (res α i) 1)

theorem tens_prod (I : ∀ i, MvPolynomial σ ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) (P : ι → MvPolynomial σ ℂ) :
    tens I (∏ i, rename (Prod.mk i) (P i)) = PiTensorProduct.map fun i => I i (P i) := by
  classical
  have key : (tens I).compMultilinearMap prodRename
      = (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap I := by
    refine Module.Basis.ext_multilinear (fun _ => basisMonomials σ ℂ) fun a => ?_
    simp only [LinearMap.compMultilinearMap_apply, prodRename_apply, coe_basisMonomials,
      MultilinearMap.compLinearMap_apply, PiTensorProduct.mapMultilinear_apply]
    rw [prod_rename_monomial]
    have := (basisMonomials (ι × σ) ℂ).constr_basis ℂ
      (fun α => PiTensorProduct.map fun i => I i (monomial (res α i) 1))
      (∑ i, Finsupp.mapDomain (Prod.mk i) (a i))
    rw [res_sum, coe_basisMonomials] at this
    exact this
  have := congrArg (fun f => f P) key
  simpa [prodRename_apply] using this

omit [Fintype ι] in
theorem tprod_ne_zero [Finite ι] (v : ∀ i, B i) (hv : ∀ i, v i ≠ 0) :
    PiTensorProduct.tprod ℂ v ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h0
  simp [hl] at this

omit [Fintype ι] in
theorem substF_rename {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (i : ι) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    substF h g (rename (Prod.mk i) P) = rename (Prod.mk i) (subst2 (h i) (g i) P) := by
  have key : (substF h g).comp (rename (Prod.mk i)) = (rename (Prod.mk i)).comp (subst2 (h i) (g i)) := by
    refine algHom_ext fun p => ?_
    simp only [AlgHom.comp_apply, rename_X, substF_X, subst2_X, map_sum, map_mul, rename_C]
  exact congrArg (fun f => f P) key

theorem exists_tensor : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (A B : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (I : ∀ i, MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i), (∀ i, I i ≠ 0) → ∃ It : MvPolynomial (ι × Fin N × Fin n) ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i, It ≠ 0 ∧ ∀ (c : ι → ℂ) (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (a : ∀ i, A i →ₗ[ℂ] A i) (b : ∀ i, B i →ₗ[ℂ] B i), (∀ i P v, I i (c i • subst2 (h i) (g i) P) (a i v) = b i (I i P v)) → ∀ P x, It ((∏ i, c i) • substF h g P) (PiTensorProduct.map a x) = PiTensorProduct.map b (It P x) := by
  intro ι _ N n A B _ _ _ _ I hI
  classical
  refine ⟨tens I, ?_, ?_⟩
  · have hex : ∀ i, ∃ P v, I i P v ≠ 0 := by
      intro i
      by_contra hc
      push Not at hc
      exact hI i (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
    choose P v hPv using hex
    intro h0
    have h1 := tens_prod I P
    rw [h0] at h1
    have h2 := congrArg (fun f => f (PiTensorProduct.tprod ℂ v)) h1
    simp only [LinearMap.zero_apply, PiTensorProduct.map_tprod] at h2
    exact tprod_ne_zero _ hPv h2.symm
  · intro c h g a b hab
    have key : ∀ Q : ι → MvPolynomial (Fin N × Fin n) ℂ,
        (tens I ((∏ i, c i) • substF h g (∏ i, rename (Prod.mk i) (Q i)))) ∘ₗ PiTensorProduct.map a
          = PiTensorProduct.map b ∘ₗ tens I (∏ i, rename (Prod.mk i) (Q i)) := by
      intro Q
      have e : (∏ i, c i) • substF h g (∏ i, rename (Prod.mk i) (Q i))
          = ∏ i, rename (Prod.mk i) (c i • subst2 (h i) (g i) (Q i)) := by
        simp only [map_prod, substF_rename, map_smul, Finset.prod_smul]
      rw [e, tens_prod, tens_prod, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
      congr 1
      funext i
      exact LinearMap.ext fun v => hab i (Q i) v
    intro P x
    induction P using MvPolynomial.induction_on' with
    | monomial α r =>
      have e : (monomial α r : MvPolynomial (ι × Fin N × Fin n) ℂ)
          = r • ∏ i, rename (Prod.mk i) (monomial (res α i) (1 : ℂ)) := by
        rw [prod_rename_monomial, sum_res, smul_monomial, smul_eq_mul, mul_one]
      have := congrArg (fun f => f x) (key fun i => monomial (res α i) 1)
      simp only [LinearMap.comp_apply] at this
      rw [e, map_smul (substF h g), smul_comm, map_smul (tens I), LinearMap.smul_apply, this, map_smul (tens I),
        LinearMap.smul_apply, map_smul]
    | add p q hp hq =>
      rw [map_add, smul_add, map_add, LinearMap.add_apply, hp, hq, map_add (tens I),
        LinearMap.add_apply, map_add]

end GlobalTheory.CompactHowe.PolyTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsJointHighestWeightLeadingMinorProduct
section
noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.CompactHowe.Minors

variable {N n : ℕ}

def IsBorelVec (hn : n ≤ N) (ν : Fin N → ℕ) (Δ : MvPolynomial (Fin N × Fin n) ℂ) : Prop :=
  Δ ≠ 0 ∧ ∀ (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ),
    (∀ i j, j < i → h i j = 0) → (∀ i j, j < i → g i j = 0) →
      subst2 h g Δ = ((∏ b, h b b ^ ν b) * ∏ a, g a a ^ ν (Fin.castLE hn a)) • Δ

theorem isBorelVec_one (hn : n ≤ N) : IsBorelVec hn (fun _ => 0) 1 :=
  ⟨one_ne_zero, fun h g _ _ => by simp⟩

theorem IsBorelVec.mul {hn : n ≤ N} {ν μ : Fin N → ℕ} {Δ Γ : MvPolynomial (Fin N × Fin n) ℂ}
    (h1 : IsBorelVec hn ν Δ) (h2 : IsBorelVec hn μ Γ) : IsBorelVec hn (fun b => ν b + μ b) (Δ * Γ) := by
  refine ⟨mul_ne_zero h1.1 h2.1, fun h g hh hg => ?_⟩
  rw [map_mul, h1.2 h g hh hg, h2.2 h g hh hg, smul_mul_smul_comm]
  congr 1
  simp only [pow_add, Finset.prod_mul_distrib]
  ring

theorem not_range_castLE {k m : ℕ} (hk : k ≤ m) (i : Fin m) (hi : i ∉ Set.range (Fin.castLE hk)) : k ≤ (i : ℕ) := by
  by_contra hc
  exact hi ⟨⟨i, by omega⟩, Fin.ext rfl⟩

theorem sum_castLE {M : Type*} [AddCommMonoid M] {k m : ℕ} (hk : k ≤ m) (f : Fin m → M)
    (hf : ∀ i : Fin m, k ≤ (i : ℕ) → f i = 0) : ∑ i, f i = ∑ i : Fin k, f (Fin.castLE hk i) :=
  (Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ f
    (fun i hi => hf i (not_range_castLE hk i hi)) fun _ => rfl).symm

theorem prod_pow_ite {k m : ℕ} (hk : k ≤ m) (c : Fin m → ℂ) :
    ∏ i, c i ^ (if (i : ℕ) < k then 1 else 0) = ∏ i : Fin k, c (Fin.castLE hk i) :=
  (Fintype.prod_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _
    (fun i hi => by rw [if_neg (not_lt.2 (not_range_castLE hk i hi)), pow_zero])
    fun i => by simp).symm

def block (hn : n ≤ N) {k : ℕ} (hk : k ≤ n) : Matrix (Fin k) (Fin k) (MvPolynomial (Fin N × Fin n) ℂ) :=
  Matrix.of fun i j => X (Fin.castLE (hk.trans hn) i, Fin.castLE hk j)

theorem det_block_ne_zero (hn : n ≤ N) {k : ℕ} (hk : k ≤ n) : (block hn hk).det ≠ 0 := by
  intro h0
  have h1 := (eval (fun p : Fin N × Fin n => if (p.1 : ℕ) = (p.2 : ℕ) then (1 : ℂ) else 0)).map_det (block hn hk)
  have h2 : (eval (fun p : Fin N × Fin n => if (p.1 : ℕ) = (p.2 : ℕ) then (1 : ℂ) else 0)).mapMatrix (block hn hk) = 1 := by
    ext i j
    simp [block, Matrix.one_apply, Fin.ext_iff]
  rw [h2, h0] at h1
  simp at h1

theorem det_lead {k m : ℕ} (hk : k ≤ m) (g : Matrix (Fin m) (Fin m) ℂ) (hg : ∀ i j, j < i → g i j = 0) :
    (g.submatrix (Fin.castLE hk) (Fin.castLE hk)).det = ∏ i : Fin k, g (Fin.castLE hk i) (Fin.castLE hk i) := by
  rw [Matrix.det_of_upperTriangular]
  · rfl
  · intro i j hij
    exact hg _ _ hij

theorem isBorelVec_det (hn : n ≤ N) {k : ℕ} (hk : k ≤ n) :
    IsBorelVec hn (fun b => if (b : ℕ) < k then 1 else 0) (block hn hk).det := by
  refine ⟨det_block_ne_zero hn hk, fun h g hh hg => ?_⟩
  have key : (subst2 h g).mapMatrix (block hn hk) =
      ((C : ℂ →+* _).mapMatrix (h.submatrix (Fin.castLE (hk.trans hn)) (Fin.castLE (hk.trans hn))))ᵀ * block hn hk *
        (C : ℂ →+* _).mapMatrix (g.submatrix (Fin.castLE hk) (Fin.castLE hk)) := by
    ext1 i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, block, Matrix.of_apply, subst2_X, Matrix.mul_apply,
      Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.submatrix_apply, Finset.sum_mul]
    rw [sum_castLE (hk.trans hn), Finset.sum_comm]
    · rw [sum_castLE hk]
      · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul]; ring
      · intro l hl
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [hg l _ (by rw [Fin.lt_def]; have := j.2; simp only [Fin.val_castLE]; omega)]
        simp
    · intro l hl
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [hh l _ (by rw [Fin.lt_def]; have := i.2; simp only [Fin.val_castLE]; omega)]
      simp
  rw [AlgHom.map_det, key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, ← RingHom.map_det,
    det_lead _ _ hh, det_lead _ _ hg, prod_pow_ite (hk.trans hn) (fun b => h b b)]
  simp only [Fin.val_castLE]
  rw [prod_pow_ite hk (fun b => g b b), smul_eq_C_mul, map_mul]
  ring

theorem exists_isBorelVec (hn : n ≤ N) (M : ℕ) : ∀ ν : Fin N → ℕ, (∀ b, ν b ≤ M) → Antitone ν →
    (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → ∃ Δ, IsBorelVec hn ν Δ := by
  classical
  induction M with
  | zero =>
    intro ν hM _ _
    obtain rfl : ν = fun _ => 0 := funext fun b => Nat.le_zero.1 (hM b)
    exact ⟨1, isBorelVec_one hn⟩
  | succ M ih =>
    intro ν hM ha h0
    obtain ⟨Γ, hΓ⟩ := ih (fun b => ν b - 1) (fun b => by have := hM b; omega)
      (fun a b hab => Nat.sub_le_sub_right (ha hab) 1) (fun b hb => by simp [h0 b hb])
    have hex : ∃ k : ℕ, ∀ b : Fin N, k ≤ (b : ℕ) → ν b = 0 := ⟨n, h0⟩
    have hk : Nat.find hex ≤ n := Nat.find_min' hex h0
    refine ⟨(block hn hk).det * Γ, ?_⟩
    have := (isBorelVec_det hn hk).mul hΓ
    convert this using 2 with b
    split_ifs with hb
    · have h1 := Nat.find_min hex hb
      push Not at h1
      obtain ⟨c, hc, hc0⟩ := h1
      have : ν c ≤ ν b := ha (Fin.le_def.2 hc)
      omega
    · have := Nat.find_spec hex b (not_lt.1 hb)
      omega

theorem exists_highestWeight (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (ha : Antitone ν)
    (h0 : ∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) :
    ∃ Δ : MvPolynomial (Fin N × Fin n) ℂ, Δ ≠ 0 ∧
      (∀ h g, ReciprocityTheory.PGsh.IsUpperUnitri h → ReciprocityTheory.PGsh.IsUpperUnitri g → subst2 h g Δ = Δ) ∧
      ∀ (d : Fin N → ℂ) (e : Fin n → ℂ), subst2 (Matrix.diagonal d) (Matrix.diagonal e) Δ =
        ((∏ b, d b ^ ν b) * ∏ a, e a ^ ν (Fin.castLE hn a)) • Δ := by
  obtain ⟨Δ, h1, h2⟩ := exists_isBorelVec hn (∑ b, ν b) ν
    (fun b => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)) ha h0
  refine ⟨Δ, h1, fun h g hh hg => ?_, fun d e => ?_⟩
  · rw [h2 h g hh.2 hg.2]
    simp [hh.1, hg.1]
  · rw [h2 _ _ (fun i j hij => Matrix.diagonal_apply_ne _ hij.ne') (fun i j hij => Matrix.diagonal_apply_ne _ hij.ne')]
    simp

end GlobalTheory.CompactHowe.Minors

end
end

