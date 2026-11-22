import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0022

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgFieldChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial
open scoped TensorProduct

noncomputable section

namespace SecAlgFieldChange

theorem normForm_eq_det {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) {n : ℕ} (x : Fin n → A) :
    normForm A x = Matrix.det (Matrix.of fun i k => ∑ j, X j * C (b.repr (x j * b k) i)) := by
  letI : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) :=
    MvPolynomial.algebraMvPolynomial
  let e₀ : MvPolynomial (Fin n) R ⊗[R] A ≃ₐ[R] MvPolynomial (Fin n) A :=
    (Algebra.TensorProduct.comm R _ A).trans
      ((MvPolynomial.algebraTensorAlgEquiv R A).restrictScalars R)
  have he₀ : ∀ a : A, e₀ (1 ⊗ₜ a) = C a := by
    intro a; simp [e₀, MvPolynomial.smul_eq_C_mul]
  have he₁ : ∀ p, e₀ (p ⊗ₜ 1) = MvPolynomial.map (algebraMap R A) p := by
    intro p; simp [e₀]
  let e : MvPolynomial (Fin n) R ⊗[R] A ≃ₐ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) A :=
    AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (fun p => by
      simp [Algebra.TensorProduct.algebraMap_apply, he₁])
  let B := (Algebra.TensorProduct.basis (MvPolynomial (Fin n) R) b).map e.toLinearEquiv
  have hB : ∀ i, B i = C (b i) := by
    intro i
    simp only [B, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    exact he₀ (b i)
  unfold normForm
  rw [Algebra.norm_eq_matrix_det B]
  congr 1
  ext i k
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.of_apply]
  have key : (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * B k =
      ∑ i, (∑ j, X j * C (b.repr (x j * b k) i)) • B i := by
    simp only [hB, Algebra.smul_def, MvPolynomial.algebraMap_def, map_sum, map_mul,
      MvPolynomial.map_X, MvPolynomial.map_C, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← C_mul]
    conv_lhs => rw [← b.sum_repr (x j * b k)]
    simp only [map_sum, Finset.mul_sum, Algebra.smul_def, C_mul, mul_assoc]
  rw [key, B.repr_sum_self]

theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (u : Fin n → R) : MvPolynomial.map φ (linForm u) = linForm (φ ∘ u) := by
  simp [linForm]

theorem secIdeal_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n e : ℕ}
    (Q₀ : Ideal (MvPolynomial (Fin n) R)) (y₀ : Par e n → R) :
    secIdeal (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀) =
      (secIdeal Q₀ y₀).map (MvPolynomial.map φ) := by
  have h1 : (MvPolynomial.map φ) ∘ secForm y₀ = secForm (φ ∘ y₀) := by
    funext i; simp [secForm, map_linForm]; rfl
  have h2 : MvPolynomial.map φ (chartForm y₀) = chartForm (φ ∘ y₀) := by
    simp [chartForm, map_linForm]; rfl
  simp only [secIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_sub, map_one, h2,
    ← Set.range_comp, h1]

end SecAlgFieldChange

theorem SecAlgFieldChange.proof : SecAlgFieldChange.Statement := by
  intro E₀ E _ _ φ n e Q₀ y₀ hfin
  classical
  letI : Algebra E₀ E := φ.toAlgebra
  have hI := SecAlgFieldChange.secIdeal_map φ Q₀ y₀
  set Q := Q₀.map (MvPolynomial.map φ)
  set y : Par e n → E := φ ∘ y₀

  let g : SecAlg Q₀ y₀ →ₐ[E₀] SecAlg Q y :=
    Ideal.quotientMapₐ (secIdeal Q y) (MvPolynomial.mapAlgHom (Algebra.ofId E₀ E))
      (by rw [hI]; exact Ideal.le_comap_map)
  have hg : ∀ p, g (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map φ p) := by
    intro p; rfl

  let ψ : SecAlg Q y →ₐ[E] E ⊗[E₀] SecAlg Q₀ y₀ :=
    Ideal.Quotient.liftₐ (secIdeal Q y)
      (aeval fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j) (by
        intro a ha
        rw [hI] at ha
        have hle : (secIdeal Q₀ y₀).map (MvPolynomial.map φ) ≤
            RingHom.ker
              (MvPolynomial.aeval (R := E) fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j).toRingHom := by
          rw [Ideal.map_le_iff_le_comap]
          intro p hp
          rw [Ideal.mem_comap, RingHom.mem_ker]
          change aeval (fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j)
            (MvPolynomial.map (algebraMap E₀ E) p) = 0
          rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_one_tmul]
          have h0 : aeval (secCoord Q₀ y₀) p = 0 := by
            rw [show secCoord Q₀ y₀ = (Ideal.Quotient.mkₐ E₀ (secIdeal Q₀ y₀)) ∘ X from rfl,
              ← MvPolynomial.aeval_unique, Ideal.Quotient.mkₐ_eq_mk]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
          rw [h0, TensorProduct.tmul_zero]
        exact RingHom.mem_ker.mp (hle ha))
  have hψ : ∀ p, ψ (Ideal.Quotient.mk _ p) = aeval (fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j) p :=
    fun p => rfl
  let θ : E ⊗[E₀] SecAlg Q₀ y₀ →ₐ[E] SecAlg Q y :=
    Algebra.TensorProduct.lift (Algebra.ofId E _) g (fun _ _ => Commute.all _ _)
  have hθ : ∀ a, θ (1 ⊗ₜ a) = g a := by
    intro a; simp [θ]
  let eqv : E ⊗[E₀] SecAlg Q₀ y₀ ≃ₐ[E] SecAlg Q y :=
    AlgEquiv.ofAlgHom θ ψ
      (by
        apply Ideal.Quotient.algHom_ext
        apply MvPolynomial.algHom_ext
        intro j
        show θ (ψ (Ideal.Quotient.mk _ (X j))) = Ideal.Quotient.mk _ (X j)
        rw [hψ, aeval_X, hθ, secCoord, hg, map_X])
      (by
        apply Algebra.TensorProduct.ext
        · exact Subsingleton.elim _ _
        · apply Ideal.Quotient.algHom_ext
          apply MvPolynomial.algHom_ext
          intro j
          show ψ (θ (1 ⊗ₜ Ideal.Quotient.mk _ (X j))) = 1 ⊗ₜ Ideal.Quotient.mk _ (X j)
          rw [hθ, hg, map_X, hψ, aeval_X]
          rfl)
  haveI := hfin
  let b := Module.Free.chooseBasis E₀ (SecAlg Q₀ y₀)
  let B := (Algebra.TensorProduct.basis E b).map eqv.toLinearEquiv
  have hB : ∀ a i, B.repr (g a) i = φ (b.repr a i) := by
    intro a i
    have : g a = eqv.toLinearEquiv (1 ⊗ₜ a) := (hθ a).symm
    simp [B, this]
    rfl
  have hBk : ∀ k, B k = g (b k) := by
    intro k; simp [B, eqv, hθ]
  have hx : ∀ j, secCoord Q y j = g (secCoord Q₀ y₀ j) := by
    intro j; simp [secCoord, hg]
  refine ⟨Module.Finite.of_basis B, ?_⟩
  rw [SecAlgFieldChange.normForm_eq_det b, SecAlgFieldChange.normForm_eq_det B, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i k => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    MvPolynomial.map_X, MvPolynomial.map_C, hx, hBk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_mul, hB]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace SecAlgFinite

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n e : ℕ}

def lineSub (y : Par e n → E) (m : Fin n) (ij : Fin (e + 1) × Fin n) : Polynomial E :=
  Fin.cases (motive := fun _ => Polynomial E)
    (Polynomial.C (y (.inr ij.2)) * Polynomial.X - if ij.2 = m then 1 else 0)
    (fun i => Polynomial.C (y (.inl (i, ij.2)))) ij.1

def transVar (m : Fin n) (ij : Fin (e + 1) × Fin n) : MvPolynomial (Par e n) k :=
  Fin.cases (motive := fun _ => MvPolynomial (Par e n) k)
    (X (.inr ij.2) - if ij.2 = m then 1 else 0) (fun i => X (.inl (i, ij.2))) ij.1

def transVarInv (m : Fin n) : Par e n → MvPolynomial (Fin (e + 1) × Fin n) k
  | .inl ij => X (ij.1.succ, ij.2)
  | .inr j => X (0, j) + if j = m then 1 else 0

theorem transVar_injective (m : Fin n) :
    Function.Injective (aeval (R := k) (transVar (k := k) (e := e) m)) := by
  have h : (aeval (R := k) (transVarInv (k := k) (e := e) m)).comp (aeval (R := k) (transVar m)) =
      AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    induction i using Fin.cases with
    | zero => by_cases hj : j = m <;> simp [transVar, transVarInv, hj]
    | succ i => simp [transVar, transVarInv]
  refine Function.LeftInverse.injective (g := aeval (R := k) (transVarInv m)) fun p => ?_
  simpa using DFunLike.congr_fun h p

theorem coord_integral (h1 : IncidenceNull.Statement) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → E) (hy : AlgebraicIndependent k y)
    (hg : IsChowForm Q (e + 1) g) (m : Fin n) :
    IsIntegral E (secCoord (Q.map (MvPolynomial.map (algebraMap k E))) y m) := by
  set Q' := Q.map (MvPolynomial.map (algebraMap k E))
  set x := secCoord Q' y with hx
  have hC : ∀ a : E, Ideal.Quotient.mk (secIdeal Q' y) (C a) = algebraMap E (SecAlg Q' y) a :=
    fun a => rfl

  have hmk : ∀ q : MvPolynomial (Fin n) k,
      aeval x q = Ideal.Quotient.mk (secIdeal Q' y) (MvPolynomial.map (algebraMap k E) q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => rw [aeval_C, map_C, hC, ← IsScalarTower.algebraMap_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, map_X]; rfl
  have hQ : ∀ q ∈ Q, aeval x q = 0 := fun q hq => by
    rw [hmk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))
  have ht : ∑ j, algebraMap E (SecAlg Q' y) (y (.inr j)) * x j = 1 := by
    have h : chartForm y - 1 ∈ secIdeal Q' y :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← Ideal.Quotient.eq] at h
    simpa [chartForm, linForm, map_sum, hC, hx, secCoord] using h
  have hl : ∀ i, ∑ j, algebraMap E (SecAlg Q' y) (y (.inl (i, j))) * x j = 0 := fun i => by
    have h : secForm y i ∈ secIdeal Q' y :=
      Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h
    simpa [secForm, linForm, map_sum, hC, hx, secCoord] using h

  set φ : MvPolynomial (Fin n ⊕ (Fin (e + 1) × Fin n)) k →ₐ[k] SecAlg Q' y :=
    aeval (Sum.elim x fun ij => Polynomial.aeval (x m) (lineSub y m ij)) with hφ
  have hker : ∀ p ∈ incIdeal Q (e + 1), φ p = 0 := by
    intro p hp
    suffices incIdeal Q (e + 1) ≤ RingHom.ker φ.toRingHom from this hp
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      simp [hφ, aeval_rename, hQ q hq]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      induction i using Fin.cases with
      | zero =>
        have h0 : ∀ j, Polynomial.aeval (x m) (lineSub y m (0, j)) =
            algebraMap E (SecAlg Q' y) (y (.inr j)) * x m - if j = m then 1 else 0 := by
          intro j
          split_ifs with hj <;> simp [lineSub, hj]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, hφ, aeval_X,
          Sum.elim_inr, Sum.elim_inl, h0, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
          zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [sub_eq_zero]
        conv_rhs => rw [← mul_one (x m), ← ht, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      | succ i =>
        simpa [hφ, lineSub] using hl i
  obtain ⟨M, hM⟩ := h1 k n (e + 1) Q g hg
  set P : Polynomial E := aeval (lineSub y m) g with hP
  have hG : φ (rename Sum.inr g) = Polynomial.aeval (x m) P := by
    rw [hφ, aeval_rename, Sum.elim_comp_inr, hP]
    have := DFunLike.congr_fun
      (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (x m)).restrictScalars k)) g
    simpa using this.symm
  have hnil : IsNilpotent (Polynomial.aeval (x m) P) := by
    rw [← hG, ← mul_one (φ _), ← ht, Finset.mul_sum]
    refine isNilpotent_sum fun j _ => ?_
    have hj : IsNilpotent (φ (rename Sum.inr g) * x j) := by
      refine ⟨M, ?_⟩
      have h0 := hker _ (hM j)
      rwa [map_pow, map_mul, show φ (X (Sum.inl j)) = x j by simp [hφ]] at h0
    rw [mul_left_comm]
    exact (Commute.all _ _).isNilpotent_mul_left hj
  have hP0 : P ≠ 0 := by
    intro h0
    have h1' : Polynomial.aeval (1 : E) P = aeval y (aeval (transVar (k := k) m) g) := by
      have ha := DFunLike.congr_fun
        (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (1 : E)).restrictScalars k)) g
      have hb := DFunLike.congr_fun
        (MvPolynomial.comp_aeval (R := k) (transVar (k := k) m) (aeval y)) g
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at ha hb
      have hfun : (fun ij => Polynomial.aeval (1 : E) (lineSub y m ij)) =
          fun ij => aeval y (transVar (k := k) m ij) := by
        funext ⟨i, j⟩
        induction i using Fin.cases with
        | zero => by_cases hj : j = m <;> simp [lineSub, transVar, hj]
        | succ i => simp [lineSub, transVar]
      rw [hP, ha, hb, hfun]
    rw [h0, map_zero] at h1'
    exact hg.1 (transVar_injective m ((hy.eq_zero_of_aeval_eq_zero _ h1'.symm).trans
      (map_zero (aeval (R := k) (transVar (k := k) (e := e) m))).symm))
  obtain ⟨N, hN⟩ := hnil
  exact isAlgebraic_iff_isIntegral.1 ⟨P ^ N, pow_ne_zero _ hP0, by rw [map_pow, hN]⟩

end SecAlgFinite

theorem SecAlgFinite.proof (h1 : IncidenceNull.Statement) : SecAlgFinite.Statement := by
  intro k E _ _ _ n e Q g y hy _ hg
  set Q' := Q.map (MvPolynomial.map (algebraMap k E))
  have htop : Algebra.adjoin E (Set.range (secCoord Q' y)) = ⊤ := by
    have h : Set.range (secCoord Q' y) = Ideal.Quotient.mkₐ E (secIdeal Q' y) '' Set.range X := by
      rw [← Set.range_comp]; rfl
    rw [h, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top _).2 (Ideal.Quotient.mkₐ_surjective E _)
  have hfg := fg_adjoin_of_finite (Set.finite_range (secCoord Q' y))
    (by rintro _ ⟨m, rfl⟩; exact SecAlgFinite.coord_integral h1 Q g y hy hg m)
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecFirstNeField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem exists_relComps_of_mem_incidence_field {F : Type*} [Field F] {n k : ℕ}
    {J : Ideal (MvPolynomial (Fin n) F)} {v : Fin k × Fin n → AlgebraicClosure F}
    (hv : v ∈ incidence J k) : ∃ W ∈ relComps J, v ∈ incidence W k := by
  obtain ⟨x, hx0, hxJ, hxv⟩ := hv
  have hP : (RingHom.ker (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F)).IsPrime :=
    RingHom.ker_isPrime _
  have hJP : J ≤ RingHom.ker (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F) :=
    fun g hg => RingHom.mem_ker.mpr (hxJ g hg)
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hJP
  refine ⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxv⟩
  by_contra hrel
  apply hx0
  funext j
  have hj : X j ∈ W := by
    by_contra hj
    exact hrel ⟨j, hj⟩
  simpa using RingHom.mem_ker.mp (hWP hj)

theorem SpecFirstNeField.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConeDimComponent.Statement)
    (h₃ : ChowFormExists.Statement) (h₄ : IncidenceZeroLocus.Statement) :
    SpecFirstNeField.Statement := by
  classical
  intro F _ n e I f u hI hf hu h0
  have hdim := h₁ F n (e + 1) I f hI hf

  have hG : ∀ W : Ideal (MvPolynomial (Fin n) F), ∃ g : MvPolynomial (Fin e × Fin n) F,
      g ≠ 0 ∧ (W ∈ relComps (I ⊔ Ideal.span {linForm u}) → IsChowForm W e g) := by
    intro W
    by_cases hW : W ∈ relComps (I ⊔ Ideal.span {linForm u})
    · obtain ⟨hWp, hWd⟩ := h₂ F n e I W u hI hdim hu hW
      obtain ⟨g, hg⟩ := h₃ F n e W hWp hWd
      exact ⟨g, hg.1, fun _ => hg⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hW⟩
  choose G hG0 hGc using hG
  let S := ((I ⊔ Ideal.span {linForm u}).finite_minimalPrimes_of_isNoetherianRing _).toFinset
  have hprod : ∀ v : Fin e × Fin n → AlgebraicClosure F, aeval v (∏ W ∈ S, G W) = 0 := by
    intro v
    let w : Fin (e + 1) × Fin n → AlgebraicClosure F := fun ij =>
      Fin.cases (motive := fun _ => AlgebraicClosure F) (algebraMap F _ (u ij.2))
        (fun i => v (i, ij.2)) ij.1
    have hw : aeval w f = 0 := by
      have hs : aeval v (specFirst f u) = aeval w f := by
        have hfun : (fun ij => aeval v (specFirstVar u ij)) = w := by
          funext ij
          obtain ⟨i, j⟩ := ij
          induction i using Fin.cases with
          | zero => simp [specFirstVar, w]
          | succ i => simp [specFirstVar, w]
        unfold specFirst
        rw [aeval_bind₁, hfun]
      rw [← hs, h0, map_zero]
    have hinc : ∀ g ∈ GroundTheory.Heights₂.Heights.incIdeal I (e + 1), aeval w g = 0 := by
      intro g hg
      simp only [GroundTheory.Heights₂.Heights.incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
      obtain ⟨h, rfl⟩ := (hf.2 g).1 hg
      rw [map_mul, hw, zero_mul]
    obtain ⟨y, hy0, hyI, hyw⟩ := h₄ F n (e + 1) I hI.isHomog (AlgebraicClosure F) w hinc
    have hvJ : v ∈ incidence (I ⊔ Ideal.span {linForm u}) e := by
      refine ⟨y, hy0, fun g hg => ?_, fun i => by simpa [w] using hyw i.succ⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hg
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      have hu0 : aeval y (linForm u) = 0 := by
        simpa [w, linForm] using hyw 0
      rw [map_add, map_mul, hu0, mul_zero, add_zero, hyI a ha]
    obtain ⟨W, hW, hvW⟩ := exists_relComps_of_mem_incidence_field hvJ
    rw [map_prod]
    exact Finset.prod_eq_zero ((Set.Finite.mem_toFinset _).mpr hW.1)
      (((hGc W hW).2 (G W)).2 dvd_rfl v hvW)
  have hne : (∏ W ∈ S, G W) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W _ => hG0 W
  apply hne
  apply MvPolynomial.map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F _).injective
  rw [map_zero]
  apply MvPolynomial.funext
  intro v
  rw [eval_map, ← aeval_def, hprod v, map_zero]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChartPointTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def ChartPointTrdeg.Statement : Prop :=
  ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      ∀ (x : Fin n → L) (j₀ : Fin n), (∀ f ∈ Q, aeval x f = 0) → x j₀ ≠ 0 →
        Algebra.trdeg k (Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹)) ≤ (e : Cardinal)

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsDerivSpanTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

def DerivSpanTrdeg.Statement : Prop :=
  ∀ (k L : Type) [Field k] [PerfectField k] [Field L] [Algebra k L] (ι : Type) [Fintype ι]
    (z : ι → L) (e : ℕ),
    Algebra.trdeg k (Algebra.adjoin k (Set.range z)) ≤ (e : Cardinal) →
    ∃ r ≤ e, ∃ b : Fin r → ι → IntermediateField.adjoin k (Set.range z),
      ∀ D : Derivation k L L, ∃ c : Fin r → L, ∀ j, D (z j) = ∑ m, c m * (b m j : L)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenSecKer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def GenSecKer.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      RingHom.ker ((Ideal.Quotient.mk
          (secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n))).comp
        (MvPolynomial.map (algebraMap k (GenParField k e n)))) = Q

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenericFormsKer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def GenericFormsKer.Statement : Prop :=
  ∀ (F L : Type) [Field F] [Field L] [Algebra F L] (ι : Type) [Fintype ι] (e r : ℕ), r ≤ e →
    ∀ (u : Fin e × ι → L), AlgebraicIndependent F u →
    ∀ (b : Fin r → ι → F) (c : Fin r → L),
      (∀ i : Fin e, ∑ j, u (i, j) * ∑ m, c m * algebraMap F L (b m j) = 0) →
      ∀ j, ∑ m, c m * algebraMap F L (b m j) = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
end

