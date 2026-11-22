import Mathlib
import GroundTheory.AutomorphicForms.RealGroupsLie
import GroundTheory.AutomorphicForms.SphericalLaurent

-- bundled from GroundTheory.AutomorphicForms.RealGroupsPolar
section
namespace GroundTheory.Automorphic

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem continuousOn_matrix_inv :
    ContinuousOn (fun A : Matrix n n 𝕜 => A⁻¹) {A | IsUnit A} := by
  rintro _ ⟨u, rfl⟩
  have h := NormedRing.inverse_continuousAt u
  have he : (fun A : Matrix n n 𝕜 => A⁻¹) = Ring.inverse := funext nonsing_inv_eq_ringInverse
  rw [he]
  exact h.continuousWithinAt

theorem posDef_conjTranspose_mul_self_GL (g : GL n 𝕜) : ((g : Matrix n n 𝕜)ᴴ * g).PosDef :=
  PosDef.conjTranspose_mul_self _ (mulVec_injective_of_isUnit g.isUnit)

noncomputable def polarPos (g : GL n 𝕜) : Matrix n n 𝕜 := CFC.sqrt ((g : Matrix n n 𝕜)ᴴ * g)

theorem polarPos_posDef (g : GL n 𝕜) : (polarPos g).PosDef := by
  have h := posDef_conjTranspose_mul_self_GL g
  rw [← isStrictlyPositive_iff_posDef] at h ⊢
  exact IsStrictlyPositive.sqrt _ h

theorem polarPos_mul_self (g : GL n 𝕜) : polarPos g * polarPos g = (g : Matrix n n 𝕜)ᴴ * g :=
  CFC.sqrt_mul_sqrt_self _ ((posDef_conjTranspose_mul_self_GL g).posSemidef.nonneg)

noncomputable def polarUnitary (g : GL n 𝕜) : Matrix n n 𝕜 := (g : Matrix n n 𝕜) * (polarPos g)⁻¹

theorem isUnit_det_of_posDef {p : Matrix n n 𝕜} (hp : p.PosDef) : IsUnit p.det :=
  (isUnit_iff_isUnit_det p).1 hp.isUnit

theorem polarUnitary_mem (g : GL n 𝕜) : polarUnitary g ∈ unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  have hP : (polarPos g)ᴴ = polarPos g := (polarPos_posDef g).isHermitian
  have hd := isUnit_det_of_posDef (polarPos_posDef g)
  rw [star_eq_conjTranspose, polarUnitary, conjTranspose_mul, conjTranspose_nonsing_inv, hP]
  calc (polarPos g)⁻¹ * (g : Matrix n n 𝕜)ᴴ * ((g : Matrix n n 𝕜) * (polarPos g)⁻¹)
      = (polarPos g)⁻¹ * ((g : Matrix n n 𝕜)ᴴ * g) * (polarPos g)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (polarPos g)⁻¹ * (polarPos g * polarPos g) * (polarPos g)⁻¹ := by rw [polarPos_mul_self]
    _ = 1 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul,
          Matrix.mul_nonsing_inv _ hd]

theorem polarUnitary_mul_polarPos (g : GL n 𝕜) : polarUnitary g * polarPos g = g := by
  rw [polarUnitary, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef (polarPos_posDef g)), Matrix.mul_one]

theorem polar_unique {g : GL n 𝕜} {k p : Matrix n n 𝕜} (hk : k ∈ unitaryGroup n 𝕜)
    (hp : p.PosDef) (h : k * p = g) : polarPos g = p ∧ polarUnitary g = k := by
  have hkk : kᴴ * k = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 hk
  have hP : pᴴ = p := hp.isHermitian
  have hpp : p * p = (g : Matrix n n 𝕜)ᴴ * g := by
    rw [← h, conjTranspose_mul, hP]
    calc p * p = p * (kᴴ * k) * p := by rw [hkk, Matrix.mul_one]
      _ = p * kᴴ * (k * p) := by simp only [Matrix.mul_assoc]
  have h1 : polarPos g = p := CFC.sqrt_unique hpp hp.posSemidef.nonneg
  refine ⟨h1, ?_⟩
  rw [polarUnitary, h1, ← h, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hp), Matrix.mul_one]

noncomputable def polarMul (kp : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef}) : GL n 𝕜 :=
    ⟨kp.1 * kp.2, kp.2.1⁻¹ * star (kp.1 : Matrix n n 𝕜), by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (kp.2 : Matrix n n 𝕜),
        Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef kp.2.2), Matrix.one_mul]
      exact mem_unitaryGroup_iff.1 kp.1.2, by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star (kp.1 : Matrix n n 𝕜)),
        mem_unitaryGroup_iff'.1 kp.1.2, Matrix.one_mul,
        Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef kp.2.2)]⟩

noncomputable def polarEquiv : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef} ≃ GL n 𝕜 where
  toFun := polarMul
  invFun g := (⟨polarUnitary g, polarUnitary_mem g⟩, ⟨polarPos g, polarPos_posDef g⟩)
  left_inv kp := by
    obtain ⟨⟨k, hk⟩, ⟨p, hp⟩⟩ := kp
    have := polar_unique (g := polarMul (⟨k, hk⟩, ⟨p, hp⟩)) hk hp rfl
    exact Prod.ext (Subtype.ext this.2) (Subtype.ext this.1)
  right_inv g := Units.ext (polarUnitary_mul_polarPos g)

@[simp] theorem coe_polarEquiv_apply (kp : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef}) :
    ((polarEquiv kp : GL n 𝕜) : Matrix n n 𝕜) = kp.1 * kp.2 := rfl

theorem continuous_polarPos
    (hsqrt : ContinuousOn (CFC.sqrt : Matrix n n 𝕜 → Matrix n n 𝕜) {a | 0 ≤ a}) :
    Continuous (polarPos : GL n 𝕜 → Matrix n n 𝕜) :=
  hsqrt.comp_continuous
    ((Units.continuous_val.matrix_conjTranspose).mul Units.continuous_val)
    (fun g => (posDef_conjTranspose_mul_self_GL g).posSemidef.nonneg)

noncomputable def polarHomeomorph
    (hsqrt : ContinuousOn (CFC.sqrt : Matrix n n 𝕜 → Matrix n n 𝕜) {a | 0 ≤ a}) :
    unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef} ≃ₜ GL n 𝕜 where
  toEquiv := polarEquiv
  continuous_toFun := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
    · exact (continuousOn_matrix_inv.comp_continuous (continuous_subtype_val.comp continuous_snd)
        (fun kp => kp.2.2.isUnit)).mul
        (continuous_star.comp (continuous_subtype_val.comp continuous_fst))
  continuous_invFun := by
    have hP := continuous_polarPos (n := n) (𝕜 := 𝕜) hsqrt
    refine Continuous.prodMk ?_ (hP.subtype_mk _)
    refine Continuous.subtype_mk ?_ _
    exact Units.continuous_val.mul
      (continuousOn_matrix_inv.comp_continuous hP (fun g => (polarPos_posDef g).isUnit))

noncomputable def polarHomeomorphReal :
    unitaryGroup n ℝ × {p : Matrix n n ℝ // p.PosDef} ≃ₜ GL n ℝ :=
  polarHomeomorph CFC.continuousOn_sqrt

noncomputable def polarHomeomorphComplex :
    unitaryGroup n ℂ × {p : Matrix n n ℂ // p.PosDef} ≃ₜ GL n ℂ :=
  polarHomeomorph CFC.continuousOn_sqrt

section ExpHermitianComplex

theorem posDef_exp_of_isHermitian_complex {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (NormedSpace.exp X).PosDef := by
  have h0 : 0 ≤ NormedSpace.exp X := IsSelfAdjoint.exp_nonneg (hX : IsSelfAdjoint X)
  exact (nonneg_iff_posSemidef.1 h0).posDef_iff_isUnit.2 (Matrix.isUnit_exp X)

noncomputable def expHermitianHomeomorphComplex :
    {X : Matrix n n ℂ // X.IsHermitian} ≃ₜ {p : Matrix n n ℂ // p.PosDef} where
  toFun X := ⟨NormedSpace.exp X.1, posDef_exp_of_isHermitian_complex X.2⟩
  invFun p := ⟨CFC.log p.1, IsSelfAdjoint.log⟩
  left_inv X := Subtype.ext (CFC.log_exp X.1 (X.2 : IsSelfAdjoint X.1))
  right_inv p := Subtype.ext (CFC.exp_log p.1 (isStrictlyPositive_iff_posDef.2 p.2))
  continuous_toFun :=
    ((contDiff_exp ℝ (Matrix n n ℂ) (n := 0)).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (CFC.continuousOn_log.comp_continuous continuous_subtype_val
      (fun p => ⟨(p.2.isHermitian : IsSelfAdjoint p.1), p.2.isUnit⟩)).subtype_mk _

noncomputable def polarExpHomeomorphComplex :
    unitaryGroup n ℂ × {X : Matrix n n ℂ // X.IsHermitian} ≃ₜ GL n ℂ :=
  ((Homeomorph.refl _).prodCongr expHermitianHomeomorphComplex).trans polarHomeomorphComplex

theorem coe_polarExpHomeomorphComplex_apply
    (kX : unitaryGroup n ℂ × {X : Matrix n n ℂ // X.IsHermitian}) :
    ((polarExpHomeomorphComplex kX : GL n ℂ) : Matrix n n ℂ) = kX.1 * NormedSpace.exp kX.2.1 :=
  rfl

end ExpHermitianComplex

section ExpHermitianReal

theorem posDef_exp_of_isHermitian_real {X : Matrix n n ℝ} (hX : X.IsHermitian) :
    (NormedSpace.exp X).PosDef := by
  have h0 : 0 ≤ NormedSpace.exp X := IsSelfAdjoint.exp_nonneg (hX : IsSelfAdjoint X)
  exact (nonneg_iff_posSemidef.1 h0).posDef_iff_isUnit.2 (Matrix.isUnit_exp X)

noncomputable def expHermitianHomeomorphReal :
    {X : Matrix n n ℝ // X.IsHermitian} ≃ₜ {p : Matrix n n ℝ // p.PosDef} where
  toFun X := ⟨NormedSpace.exp X.1, posDef_exp_of_isHermitian_real X.2⟩
  invFun p := ⟨CFC.log p.1, IsSelfAdjoint.log⟩
  left_inv X := Subtype.ext (CFC.log_exp X.1 (X.2 : IsSelfAdjoint X.1))
  right_inv p := Subtype.ext (CFC.exp_log p.1 (isStrictlyPositive_iff_posDef.2 p.2))
  continuous_toFun :=
    ((contDiff_exp ℝ (Matrix n n ℝ) (n := 0)).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (CFC.continuousOn_log.comp_continuous continuous_subtype_val
      (fun p => ⟨(p.2.isHermitian : IsSelfAdjoint p.1), p.2.isUnit⟩)).subtype_mk _

noncomputable def polarExpHomeomorphReal :
    unitaryGroup n ℝ × {X : Matrix n n ℝ // X.IsHermitian} ≃ₜ GL n ℝ :=
  ((Homeomorph.refl _).prodCongr expHermitianHomeomorphReal).trans polarHomeomorphReal

theorem coe_polarExpHomeomorphReal_apply
    (kX : unitaryGroup n ℝ × {X : Matrix n n ℝ // X.IsHermitian}) :
    ((polarExpHomeomorphReal kX : GL n ℝ) : Matrix n n ℝ) = kX.1 * NormedSpace.exp kX.2.1 :=
  rfl

end ExpHermitianReal

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.SatakeSymmetric
section
noncomputable section

namespace GroundTheory.Automorphic

open AddMonoidAlgebra MvPolynomial

namespace Spherical

variable {n : ℕ}

def permCoord (σ : Equiv.Perm (Fin n)) : (Fin n → ℤ) →+ (Fin n → ℤ) where
  toFun l := l ∘ σ.symm
  map_zero' := rfl
  map_add' _ _ := rfl

theorem permCoord_apply (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) : permCoord σ l = l ∘ σ.symm :=
  rfl

def permAct (σ : Equiv.Perm (Fin n)) : LaurentRing n →ₐ[ℂ] LaurentRing n :=
  mapDomainAlgHom ℂ ℂ (permCoord σ)

theorem permAct_single (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) (c : ℂ) :
    permAct σ (single l c) = single (l ∘ σ.symm) c := by
  simp [permAct, mapDomainAlgHom, mapDomain_single, permCoord_apply]

theorem permAct_mul (σ τ : Equiv.Perm (Fin n)) :
    permAct (σ * τ) = (permAct σ).comp (permAct τ) := by
  refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, permAct_single, permAct_single, permAct_single]
  congr 1

theorem permAct_one : permAct (1 : Equiv.Perm (Fin n)) = AlgHom.id ℂ (LaurentRing n) := by
  refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
  rw [permAct_single, AlgHom.id_apply]
  rfl

theorem evalAt_permAct (w : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) (p : LaurentRing n) :
    evalAt w (permAct σ p) = evalAt (w ∘ σ) p := by
  have : (evalAt w).comp (permAct σ) = evalAt (w ∘ σ) := by
    refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
    rw [AlgHom.comp_apply, permAct_single, evalAt_single, evalAt_single, monomialChar_apply,
      monomialChar_apply]
    congr 1
    exact Fintype.prod_equiv σ.symm _ _ fun i => by simp
  exact AlgHom.congr_fun this p

variable (n) in

def symmetricLaurent : Subalgebra ℂ (LaurentRing n) where
  carrier := {p | ∀ σ, permAct σ p = p}
  mul_mem' {a b} ha hb σ := by
    change permAct σ (a * b) = a * b
    rw [map_mul, ha σ, hb σ]
  add_mem' {a b} ha hb σ := by
    change permAct σ (a + b) = a + b
    rw [map_add, ha σ, hb σ]
  algebraMap_mem' c σ := AlgHom.commutes _ c

theorem mem_symmetricLaurent {p : LaurentRing n} :
    p ∈ symmetricLaurent n ↔ ∀ σ, permAct σ p = p :=
  Iff.rfl

theorem monomial_const_mem (c : ℤ) : monomial (fun _ : Fin n => c) ∈ symmetricLaurent n := by
  intro σ
  rw [permAct_single]
  rfl

def natToInt : (Fin n →₀ ℕ) →+ (Fin n → ℤ) where
  toFun s i := s i
  map_zero' := by
    funext i
    simp
  map_add' s t := by
    funext i
    simp

theorem natToInt_apply (s : Fin n →₀ ℕ) (i : Fin n) : natToInt s i = s i :=
  rfl

theorem natToInt_injective : Function.Injective (natToInt (n := n)) := fun s t h => by
  ext i
  exact Int.ofNat_inj.1 (congrFun h i)

variable (n) in

def polyEmb : MvPolynomial (Fin n) ℂ →ₐ[ℂ] LaurentRing n :=
  mapDomainAlgHom ℂ ℂ natToInt

theorem polyEmb_monomial (s : Fin n →₀ ℕ) (c : ℂ) :
    polyEmb n (MvPolynomial.monomial s c) = single (natToInt s) c := by
  simp [polyEmb, mapDomainAlgHom, MvPolynomial.monomial, mapDomain_single]

theorem polyEmb_X (i : Fin n) : polyEmb n (X i) = monomial (Pi.single i 1) := by
  rw [X, polyEmb_monomial]
  congr 1
  funext j
  rw [natToInt_apply, Finsupp.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem polyEmb_injective : Function.Injective (polyEmb n) :=
  mapDomain_injective natToInt_injective

theorem polyEmb_rename (σ : Equiv.Perm (Fin n)) (Q : MvPolynomial (Fin n) ℂ) :
    polyEmb n (rename σ Q) = permAct σ (polyEmb n Q) := by
  have : (polyEmb n).comp (rename σ) = (permAct σ).comp (polyEmb n) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, polyEmb_X, polyEmb_X, permAct_single]
    congr 1
    funext j
    simp only [Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]
  exact AlgHom.congr_fun this Q

theorem mem_range_polyEmb {q : LaurentRing n} (hq : ∀ l ∈ q.coeff.support, ∀ i, 0 ≤ l i) :
    q ∈ (polyEmb n).range := by
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single q]
  refine Subalgebra.sum_mem _ fun l hl => ?_
  refine ⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (l i).toNat) (q.coeff l), ?_⟩
  change polyEmb n _ = _
  rw [polyEmb_monomial]
  congr 1
  funext i
  simp [natToInt_apply, Int.toNat_of_nonneg (hq l hl i)]

theorem symmetricLaurent_le {A : Subalgebra ℂ (LaurentRing n)}
    (he : ∀ k, polyEmb n (esymm (Fin n) ℂ k) ∈ A) (hinv : monomial (fun _ => (-1 : ℤ)) ∈ A) :
    symmetricLaurent n ≤ A := by
  classical
  intro p hp
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ l ∈ p.coeff.support, ∀ i, -(N : ℤ) ≤ l i := by
    refine ⟨p.coeff.support.sup fun l => Finset.univ.sup fun i => (l i).natAbs, fun l hl i => ?_⟩
    have h1 : (l i).natAbs ≤ Finset.univ.sup fun i => (l i).natAbs :=
      Finset.le_sup (f := fun i => (l i).natAbs) (Finset.mem_univ i)
    have h2 := Finset.le_sup (f := fun l : Fin n → ℤ => Finset.univ.sup fun i => (l i).natAbs) hl
    have h3 : ((l i).natAbs : ℤ) ≤ _ := Nat.cast_le.2 (h1.trans h2)
    rw [Int.natCast_natAbs] at h3
    have h4 := neg_abs_le (l i)
    linarith
  set c : LaurentRing n := monomial (fun _ => (N : ℤ))
  set q := c * p
  have hq : q ∈ symmetricLaurent n := Subalgebra.mul_mem _ (monomial_const_mem _) hp
  have hqs : ∀ l ∈ q.coeff.support, ∀ i, 0 ≤ l i := by
    intro l hl i
    have hsub := AddMonoidAlgebra.support_coeff_mul_subset c p hl
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hsub
    have ha' : a = fun _ => (N : ℤ) := by
      have := Finsupp.support_single_subset ha
      simpa using this
    subst ha'
    have := hN b hb i
    simp only [Pi.add_apply]
    omega
  obtain ⟨Q, hQ⟩ := mem_range_polyEmb hqs
  change polyEmb n Q = q at hQ
  have hQsym : Q ∈ symmetricSubalgebra (Fin n) ℂ := by
    rw [mem_symmetricSubalgebra]
    intro σ
    apply polyEmb_injective
    rw [polyEmb_rename, hQ, hq σ]
  obtain ⟨P, hP⟩ := esymmAlgHom_surjective ℂ (σ := Fin n) (n := n) (Fintype.card_fin n).le ⟨Q, hQsym⟩
  have hQP : Q = aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) P := by
    rw [← esymmAlgHom_apply, hP]
  have hqA : q ∈ A := by
    rw [← hQ, hQP, ← AlgHom.comp_apply, comp_aeval]
    have : aeval (fun i : Fin n => polyEmb n (esymm (Fin n) ℂ (i + 1))) P ∈
        (aeval fun i : Fin n => polyEmb n (esymm (Fin n) ℂ (i + 1))).range :=
      AlgHom.mem_range_self _ _
    rw [aeval_range] at this
    exact Algebra.adjoin_le (Set.range_subset_iff.2 fun i => he _) this
  have hp' : p = monomial (fun _ => (-1 : ℤ)) ^ N * q := by
    rw [AddMonoidAlgebra.single_pow, one_pow, ← mul_assoc, AddMonoidAlgebra.single_mul_single,
      one_mul]
    have : (N • fun _ : Fin n => (-1 : ℤ)) + (fun _ => (N : ℤ)) = 0 := by
      funext i
      simp
    rw [this, ← AddMonoidAlgebra.one_def, one_mul]
  rw [hp']
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hinv _) hqA

def orbitSum (ν : Fin n → ℤ) : LaurentRing n :=
  ∑ σ : Equiv.Perm (Fin n), monomial (ν ∘ σ.symm)

theorem orbitSum_mem (ν : Fin n → ℤ) : orbitSum ν ∈ symmetricLaurent n := by
  intro τ
  rw [orbitSum, map_sum]
  simp only [permAct_single]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => by congr 1

theorem coeff_orbitSum (ν l : Fin n → ℤ) :
    (orbitSum ν).coeff l = ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      ν ∘ σ.symm = l).card : ℂ) := by
  classical
  rw [orbitSum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.card_filter,
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp

theorem exists_of_coeff_orbitSum_ne_zero {ν l : Fin n → ℤ} (h : (orbitSum ν).coeff l ≠ 0) :
    ∃ σ : Equiv.Perm (Fin n), ν ∘ σ.symm = l := by
  rw [coeff_orbitSum] at h
  obtain ⟨σ, hσ⟩ := Finset.card_ne_zero.1 (fun h' => h (by rw [h', Nat.cast_zero]))
  exact ⟨σ, (Finset.mem_filter.1 hσ).2⟩

theorem coeff_orbitSum_self_ne_zero (ν : Fin n → ℤ) : (orbitSum ν).coeff ν ≠ 0 := by
  rw [coeff_orbitSum, Nat.cast_ne_zero, Finset.card_ne_zero]
  exact ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩

theorem orbitSum_ne_zero (ν : Fin n → ℤ) : orbitSum ν ≠ 0 := fun h =>
  coeff_orbitSum_self_ne_zero ν (by rw [h]; rfl)

theorem comp_eq_of_antitone {ν : Fin n → ℤ} (hν : Antitone ν) (σ : Equiv.Perm (Fin n))
    (hσ : Antitone (ν ∘ σ)) : ν ∘ σ = ν := by
  set f : Fin n → ℤ := fun i => -ν i
  have hf : Monotone (f ∘ σ) := fun i j hij => neg_le_neg (hσ hij)
  have hf1 : Monotone (f ∘ (1 : Equiv.Perm (Fin n))) := fun i j hij => neg_le_neg (hν hij)
  have e1 := (Tuple.comp_sort_eq_comp_iff_monotone (f := f) (σ := σ)).2 hf
  have e2 := (Tuple.comp_sort_eq_comp_iff_monotone (f := f) (σ := 1)).2 hf1
  have : f ∘ σ = f := by
    rw [e1, ← e2]
    rfl
  funext i
  have := congrFun this i
  simpa [f] using this

end Spherical

end GroundTheory.Automorphic
end
end

