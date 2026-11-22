import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0034
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerNesbittExistsEquivOfCharpolyEqHypotheses
section
noncomputable section

namespace GlobalTheory.CharpolyIso

open Module Polynomial GlobalTheory.TraceIso

variable {k A : Type} [Field k] [Ring A] [Algebra k A]

def cp (k : Type) [Field k] {A : Type} [Ring A] [Algebra k A] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Module A V] [IsScalarTower k A V] (a : A) : k[X] :=
  LinearMap.charpoly (Algebra.lsmul k k V a)

section

variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [FiniteDimensional k V] [FiniteDimensional k W]

theorem cp_congr (e : V ≃ₗ[A] W) (a : A) : cp k V a = cp k W a := by
  unfold cp
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k) (Algebra.lsmul k k V a)]
  congr 1
  ext w
  simp [LinearEquiv.conj_apply]

theorem cp_prod (a : A) : cp k (V × W) a = cp k V a * cp k W a := by
  unfold cp
  rw [← LinearMap.charpoly_prodMap]
  congr 1

theorem charpoly_one_eq (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    LinearMap.charpoly (1 : V →ₗ[k] V) = (X - 1 : k[X]) ^ finrank k V := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis k V), LinearMap.toMatrix_one,
    Matrix.charpoly_one]
  simp

theorem charpoly_zero_eq (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    LinearMap.charpoly (0 : V →ₗ[k] V) = (X : k[X]) ^ finrank k V := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis k V), map_zero, Matrix.charpoly_zero]
  simp

theorem finrank_eq_zero_of_hom
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (h : ∀ a : A, cp k V a = cp k W a)
    (h₁ : ∀ f : V →ₗ[A] W, f = 0) (h₂ : ∀ f : W →ₗ[A] V, f = 0) : finrank k V = 0 := by
  classical
  let p : End A (V × W) := (LinearMap.inl A V W).comp (LinearMap.fst A V W)
  let F : End (End A (V × W)) (V × W) :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := by
        rintro φ ⟨v, w⟩
        have e₁ := LinearMap.congr_fun
          (h₁ ((LinearMap.snd A V W).comp (φ.comp (LinearMap.inl A V W)))) v
        have e₂ := LinearMap.congr_fun
          (h₂ ((LinearMap.fst A V W).comp (φ.comp (LinearMap.inr A V W)))) w
        have e₃ : φ (v, w) = φ (v, 0) + φ (0, w) := by rw [← map_add]; simp
        simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.snd_apply,
          LinearMap.fst_apply, LinearMap.zero_apply] at e₁ e₂
        change ((φ (v, w)).1, (0 : W)) = φ (v, 0)
        rw [e₃]
        ext
        · simp [e₂]
        · exact e₁.symm }
  let b := Module.finBasis k (V × W)
  haveI : IsSemisimpleModule A (V × W) := by
    have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl A V W))
      (IsSemisimpleModule.range (LinearMap.inr A V W))
    rw [LinearMap.sup_range_inl_inr] at hs
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have hall : (p.restrictScalars k) = Algebra.lsmul k k (V × W) r :=
    b.ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hV : Algebra.lsmul k k V r = 1 := by
    ext v
    exact (congrArg Prod.fst (LinearMap.congr_fun hall (v, 0))).symm
  have hW : Algebra.lsmul k k W r = 0 := by
    ext w
    exact (congrArg Prod.snd (LinearMap.congr_fun hall (0, w))).symm
  have key := h r
  unfold cp at key
  rw [hV, hW, charpoly_one_eq, charpoly_zero_eq] at key
  have hdeg : finrank k V = finrank k W := by
    have := congrArg natDegree key
    have h1 : (X - 1 : k[X]).natDegree = 1 := by
      simpa using natDegree_X_sub_C (1 : k)
    simpa [natDegree_pow, h1] using this
  have h0 := congrArg (Polynomial.eval 0) key
  simp only [eval_pow, eval_sub, eval_X, eval_one, zero_sub] at h0
  by_contra hne
  have hW0 : finrank k W ≠ 0 := hdeg ▸ hne
  rw [zero_pow hW0] at h0
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h0

end

theorem nonempty_linear_equiv_of_charpoly_eq (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
    finrank k V + finrank k W ≤ n → (∀ a : A, cp k V a = cp k W a) → Nonempty (V ≃ₗ[A] W) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have step : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
      [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
      [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
      finrank k V + finrank k W ≤ n → (∀ a : A, cp k V a = cp k W a) → ∀ f : V →ₗ[A] W, f ≠ 0 →
      Nonempty (V ≃ₗ[A] W) := by
    intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h f hf
    obtain ⟨P, Q, S, ⟨e₁⟩, ⟨e₂⟩, hP, hQ⟩ := split_of_hom (k := k) f hf
    haveI := finiteDimensional_sub (k := k) P
    haveI := finiteDimensional_sub (k := k) Q
    haveI := finiteDimensional_sub (k := k) S
    obtain ⟨e⟩ := ih (finrank k P + finrank k Q) (by omega) P Q le_rfl fun a => by
      have := h a
      rw [cp_congr e₁, cp_congr e₂, cp_prod, cp_prod] at this
      have hS : cp k S a ≠ 0 := (LinearMap.charpoly_monic _).ne_zero
      exact mul_right_cancel₀ hS this
    exact ⟨e₁.trans ((e.prodCongr (LinearEquiv.refl A _)).trans e₂.symm)⟩
  intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h
  by_cases h₁ : ∀ f : V →ₗ[A] W, f = 0
  · by_cases h₂ : ∀ f : W →ₗ[A] V, f = 0
    · haveI : Subsingleton V := Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom h h₁ h₂)
      haveI : Subsingleton W :=
        Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom (fun a => (h a).symm) h₂ h₁)
      exact ⟨LinearEquiv.ofSubsingleton V W⟩
    · push_neg at h₂
      obtain ⟨f, hf⟩ := h₂
      obtain ⟨e⟩ := step W V (by omega) (fun a => (h a).symm) f hf
      exact ⟨e.symm⟩
  · push_neg at h₁
    obtain ⟨f, hf⟩ := h₁
    exact step V W hn h f hf

theorem cp_asModule {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k Γ V) (a : MonoidAlgebra k Γ) :
    haveI : FiniteDimensional k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
    cp k ρ.asModule a = LinearMap.charpoly (ρ.asAlgebraHom a) := by
  haveI : FiniteDimensional k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
  unfold cp
  rw [← LinearEquiv.charpoly_conj ρ.asModuleEquiv.symm (ρ.asAlgebraHom a)]
  congr 1

theorem exists_equiv_of_charpoly_eq {Γ V W : Type} [Monoid Γ] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) (hρ : ρ.IsSemisimpleRepresentation)
    (hσ : σ.IsSemisimpleRepresentation)
    (h : ∀ a : MonoidAlgebra k Γ,
      LinearMap.charpoly (ρ.asAlgebraHom a) = LinearMap.charpoly (σ.asAlgebraHom a)) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).1 hρ
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 hσ
  haveI : FiniteDimensional k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
  haveI : FiniteDimensional k σ.asModule := σ.asModuleEquiv.symm.finiteDimensional
  have key : ∀ a : MonoidAlgebra k Γ, cp k ρ.asModule a = cp k σ.asModule a := fun a => by
    rw [cp_asModule, cp_asModule, h]
  obtain ⟨e⟩ := nonempty_linear_equiv_of_charpoly_eq (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule σ.asModule le_rfl key
  refine ⟨ρ.asModuleEquiv.symm.trans ((e.restrictScalars k).trans σ.asModuleEquiv), fun g v => ?_⟩
  change σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v))) =
    σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul]
  simp

theorem exists_equiv_of_charpoly_eq' : ∀ {k Γ V W : Type} [Field k] [Monoid Γ] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] [FiniteDimensional k V] [FiniteDimensional k W] (ρ : Representation k Γ V)
    (σ : Representation k Γ W), ρ.IsSemisimpleRepresentation → σ.IsSemisimpleRepresentation →
    (∀ a : MonoidAlgebra k Γ, LinearMap.charpoly (ρ.asAlgebraHom a) =
      LinearMap.charpoly (σ.asAlgebraHom a)) →
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) :=
  fun ρ σ hρ hσ h => exists_equiv_of_charpoly_eq ρ σ hρ hσ h

end GlobalTheory.CharpolyIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CMemCoeffSub
section
open scoped BigOperators

namespace GlobalTheory.BlockDetPoly

def coeffSub {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ) :
    Subalgebra (MvPolynomial (Fin m) O) (X → MvPolynomial (Fin m) O) where
  carrier := {f | ∀ d, (fun x => MvPolynomial.coeff d (f x)) ∈ T}
  mul_mem' := by
    intro f g hf hg d
    have : (fun x => MvPolynomial.coeff d ((f * g) x)) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal d,
        (fun x => MvPolynomial.coeff p.1 (f x)) * (fun x => MvPolynomial.coeff p.2 (g x)) := by
      funext x
      simp [MvPolynomial.coeff_mul, Finset.sum_apply]
    rw [this]
    exact T.sum_mem fun p _ => T.mul_mem (hf _) (hg _)
  add_mem' := by
    intro f g hf hg d
    have : (fun x => MvPolynomial.coeff d ((f + g) x)) =
        (fun x => MvPolynomial.coeff d (f x)) + (fun x => MvPolynomial.coeff d (g x)) := by
      funext x
      simp
    rw [this]
    exact T.add_mem (hf _) (hg _)
  algebraMap_mem' := fun p d => T.algebraMap_mem (MvPolynomial.coeff d p)

theorem C_mem_coeffSub {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ)
    (t : X → O) (ht : t ∈ T) : (fun x => MvPolynomial.C (t x)) ∈ coeffSub T m := by
  show ∀ d : Fin m →₀ ℕ,
    (fun x => MvPolynomial.coeff d (MvPolynomial.C (t x) : MvPolynomial (Fin m) O)) ∈ T
  intro d
  rcases eq_or_ne d 0 with rfl | hd
  · simpa using ht
  · have h0 : (fun x => MvPolynomial.coeff d (MvPolynomial.C (t x) : MvPolynomial (Fin m) O)) = 0 := by
      funext x
      simp [MvPolynomial.coeff_C, Ne.symm hd]
    rw [h0]
    exact T.zero_mem

theorem det_comb_mem {O X Q : Type} [CommRing O] [CommRing Q] (T : Subalgebra O (X → O)) {n : ℕ}
    (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O))
    (hR : ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) →
      ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T)
    (φ : O →+* Q) (S : Subalgebra Q (X → Q)) (hS : ∀ t ∈ T, (fun x => φ (t x)) ∈ S)
    {J : Type} [Fintype J] (b : J → X → Matrix (Fin n) (Fin n) O) (hb : ∀ j, b j ∈ R)
    (c : J → Q) : (fun x => Matrix.det (∑ j, c j • (b j x).map φ)) ∈ S := by
  classical

  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let a : Fin (Fintype.card J) → X → Matrix (Fin n) (Fin n) O := fun k => b (e k)

  let A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (Fintype.card J)) (X → O)) :=
    Matrix.of fun i j => ∑ k, MvPolynomial.X k * MvPolynomial.C (fun x => a k x i j)
  have hcoef : ∀ d, MvPolynomial.coeff d A.det ∈ T := by
    intro d
    have h1 : MvPolynomial.coeff d A.det = fun x => MvPolynomial.coeff d (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin (Fintype.card J)) O) •
          (a k x).map MvPolynomial.C)) := by
      funext x
      have h2 : MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x) A.det =
          Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin (Fintype.card J)) O) •
            (a k x).map MvPolynomial.C) := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        simp [A, Matrix.sum_apply]
      rw [← h2, MvPolynomial.coeff_map]
      rfl
    rw [h1]
    exact hR _ a (fun k => hb (e k)) d

  have h3 : ∀ x, Matrix.det (∑ j, c j • (b j x).map φ) =
      MvPolynomial.eval₂ (φ.comp (Pi.evalRingHom (fun _ : X => O) x)) (fun k => c (e k)) A.det := by
    intro x
    rw [← MvPolynomial.coe_eval₂Hom, RingHom.map_det]
    congr 1
    ext i j
    simp only [A, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      MvPolynomial.eval₂_C, RingHom.comp_apply, Pi.evalRingHom_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    exact (e.sum_comp (fun j' => c j' * φ (b j' x i j))).symm
  have key : (fun x => Matrix.det (∑ j, c j • (b j x).map φ)) =
      ∑ d ∈ A.det.support, (fun x => φ (MvPolynomial.coeff d A.det x)) *
        algebraMap Q (X → Q) (∏ k, c (e k) ^ d k) := by
    funext x
    rw [h3, MvPolynomial.eval₂_eq', Finset.sum_apply]
    simp
  rw [key]
  exact S.sum_mem fun d _ => S.mul_mem (hS _ (hcoef d)) (S.algebraMap_mem _)

private theorem mem_coeffSub_iff_forall_coeff_mem {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ)
    (f : X → MvPolynomial (Fin m) O) :
    f ∈ coeffSub T m ↔ ∀ d, (fun x => MvPolynomial.coeff d (f x)) ∈ T := Iff.rfl

theorem main : ∀ {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (n : ℕ) (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O)), (∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T) → ∀ (m g : ℕ) (Θ : Fin m → Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ k p q, Θ k p q ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) * MvPolynomial.C (Θ k pa.1 qb.1 x pa.2 qb.2)))) ∈ T := by
  intro O X _ T n R hR m g Θ hΘ d
  classical

  let ψ : (X → Matrix (Fin n) (Fin n) O) →+* (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) :=
    RingHom.compLeft (MvPolynomial.C : O →+* MvPolynomial (Fin m) O).mapMatrix X
  have hψ : ∀ (a : X → Matrix (Fin n) (Fin n) O) x, ψ a x = (a x).map MvPolynomial.C :=
    fun _ _ => rfl
  let s : Submonoid (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) := R.toSubmonoid.map ψ
  let R' : Subalgebra (MvPolynomial (Fin m) O) (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) :=
    Algebra.adjoin (MvPolynomial (Fin m) O) (s : Set _)

  have hrep : ∀ F ∈ R', ∃ (N : ℕ) (c : Fin N → MvPolynomial (Fin m) O)
      (b : Fin N → X → Matrix (Fin n) (Fin n) O), (∀ j, b j ∈ R) ∧ F = ∑ j, c j • ψ (b j) := by
    intro F hF
    have hF' : F ∈ Submodule.span (MvPolynomial (Fin m) O) (s : Set _) := by
      have h := Algebra.adjoin_eq_span (R := MvPolynomial (Fin m) O)
        (s : Set (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)))
      rw [Submonoid.closure_eq] at h
      rw [← h]
      exact hF
    obtain ⟨N, c, b, hsum⟩ := Submodule.mem_span_set'.mp hF'
    choose b' hb' hbe using fun j => Submonoid.mem_map.mp (b j).2
    refine ⟨N, c, b', fun j => hb' j, ?_⟩
    rw [← hsum]
    simp [hbe]

  have hR' : ∀ (m' : ℕ) (a : Fin m' → X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)),
      (∀ k, a k ∈ R') → ∀ d' : Fin m' →₀ ℕ, (fun x => MvPolynomial.coeff d' (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) •
          (a k x).map MvPolynomial.C))) ∈ coeffSub T m := by
    intro m' a ha d'
    choose N c b hb hab using fun k => hrep (a k) (ha k)
    have hS : ∀ t ∈ T, (fun x => ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
        (MvPolynomial (Fin m) O)).comp MvPolynomial.C) (t x)) ∈ coeffSub (coeffSub T m) m' :=
      fun t ht => C_mem_coeffSub (coeffSub T m) m' _ (C_mem_coeffSub T m t ht)
    have h := det_comb_mem T R hR ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
        (MvPolynomial (Fin m) O)).comp MvPolynomial.C) (coeffSub (coeffSub T m) m') hS
      (J := Σ k, Fin (N k)) (fun kj => b kj.1 kj.2) (fun kj => hb kj.1 kj.2)
      (fun kj => MvPolynomial.X kj.1 * MvPolynomial.C (c kj.1 kj.2))
    have heq : ∀ x, (∑ kj : (Σ k, Fin (N k)), (MvPolynomial.X kj.1 * MvPolynomial.C (c kj.1 kj.2) :
          MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) • (b kj.1 kj.2 x).map
          ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
            (MvPolynomial (Fin m) O)).comp MvPolynomial.C)) =
        ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) •
          (a k x).map MvPolynomial.C := by
      intro x
      ext i j
      simp [hab, hψ, Matrix.sum_apply, Fintype.sum_sigma, Finset.mul_sum, mul_assoc, Finset.sum_apply]
    simp only [heq] at h
    exact (mem_coeffSub_iff_forall_coeff_mem _ _ _).mp h d'

  have hblk : ∀ p q, (fun x => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) •
      (Θ k p q x).map MvPolynomial.C) ∈ R' := by
    intro p q
    have h4 : (fun x => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) •
        (Θ k p q x).map MvPolynomial.C) = ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • ψ (Θ k p q) := by
      funext x
      simp [Finset.sum_apply, hψ]
    rw [h4]
    exact R'.sum_mem fun k _ =>
      R'.smul_mem (Algebra.subset_adjoin (Submonoid.mem_map.mpr ⟨Θ k p q, hΘ k p q, rfl⟩)) _
  have h5 := (mem_coeffSub_iff_forall_coeff_mem _ _ _).mp (GlobalTheory.BlockDet.main (coeffSub T m) n R' hR' g _ hblk) d
  have h6 : ∀ x, (Matrix.of fun (pa qb : Fin g × Fin n) => (∑ k, (MvPolynomial.X k :
        MvPolynomial (Fin m) O) • (Θ k pa.1 qb.1 x).map MvPolynomial.C) pa.2 qb.2) =
      Matrix.of fun (pa qb : Fin g × Fin n) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) *
        MvPolynomial.C (Θ k pa.1 qb.1 x pa.2 qb.2) := by
    intro x
    ext pa qb
    simp [Matrix.sum_apply]
  simp only [h6] at h5
  exact h5

end GlobalTheory.BlockDetPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralLinearFormPiMatrixEqSumTraceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_sum_trace_of_trace_like_pi_matrix : ∀ (k : Type) [Field k] (N : ℕ) (n : Fin N → ℕ) (τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k), (∀ x y, τ (x * y) = τ (y * x)) → ∃ c : Fin N → k, ∀ x, τ x = ∑ i, c i * (x i).trace := by
  first | exact @GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace | exact GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace | (intros; apply GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChainLeIInfSupPowSmulTopOfPrecompleteStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_le_iInf_sup_pow_smul_top_of_precomplete : ∀ (Λ : Type) [CommRing Λ] (I : Ideal Λ) [IsPrecomplete I Λ] (a : ℕ) (N : ℕ → Submodule Λ (Fin a → Λ)),
  (∀ n, N (n + 1) ≤ N n) → (∀ n, I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) ≤ N n) →
  (∀ n, N n ≤ N (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))) →
  ∀ n, N n ≤ (⨅ k, N k) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
  first | exact @GlobalTheory.chain_le_iInf_sup_pow_smul_top | exact GlobalTheory.chain_le_iInf_sup_pow_smul_top | (intros; apply GlobalTheory.chain_le_iInf_sup_pow_smul_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMonoidAlgebraLiftEqOfCharpolyEq
section
open scoped BigOperators

namespace GlobalTheory

open scoped BigOperators in
open Polynomial in
private lemma det_generic_sum_eq_of_charpoly_eq {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k) (h : ∀ g, (ρ g).charpoly = (σ g).charpoly)
    (m : ℕ) (g : Fin m → G) :
    (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) k) • (ρ (g i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin m) k)).det =
      (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) k) • (σ (g i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin m) k)).det := by
  ext d
  let T : Subalgebra k (Bool → k) :=
    AlgHom.equalizer (Pi.evalAlgHom k (fun _ : Bool => k) true) (Pi.evalAlgHom k (fun _ : Bool => k) false)
  have key := _root_.GlobalTheory.coeff_det_generic_sum_mem_of_charpoly_coeff_mem T n
    (fun b => if b then ρ else σ) (by intro g j; simp [T, AlgHom.mem_equalizer, h]) m g d
  simpa [T, AlgHom.mem_equalizer] using key

open scoped BigOperators in
open Polynomial in
private lemma charpoly_sum_smul_eq_of_charpoly_eq {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k) (h : ∀ g, (ρ g).charpoly = (σ g).charpoly)
    (m : ℕ) (c : Fin m → k) (g : Fin m → G) :
    (∑ i, c i • ρ (g i)).charpoly = (∑ i, c i • σ (g i)).charpoly := by
  have hd := det_generic_sum_eq_of_charpoly_eq n ρ σ h (m + 1) (Fin.cons 1 g)
  have key : ∀ τ : G →* Matrix (Fin n) (Fin n) k, (∑ i, c i • τ (g i)).charpoly =
      MvPolynomial.aeval (Fin.cons (X : k[X]) (fun i => -C (c i)) : Fin (m + 1) → k[X])
        (∑ i, (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) k) •
          (τ ((Fin.cons 1 g : Fin (m + 1) → G) i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin (m + 1)) k)).det := by
    intro τ
    rw [AlgHom.map_det]
    unfold Matrix.charpoly
    congr 1
    ext i j
    simp [Fin.sum_univ_succ, Matrix.charmatrix_apply, Matrix.sum_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  rw [key ρ, key σ, hd]

open scoped BigOperators in
open Polynomial in
theorem _root_.GlobalTheory.charpoly_lift_eq_of_charpoly_eq : ∀ {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ g, (ρ g).charpoly = (σ g).charpoly) →
    ∀ a : MonoidAlgebra k G,
      (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ a).charpoly =
      (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G σ a).charpoly := by
  intro k G _ _ n ρ σ h a
  have hsum : ∀ τ : G →* Matrix (Fin n) (Fin n) k,
      MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G τ a =
        ∑ i, a.coeff (a.coeff.support.equivFin.symm i) • τ (a.coeff.support.equivFin.symm i) := by
    intro τ
    rw [MonoidAlgebra.lift_apply, Finsupp.sum, ← Finset.sum_coe_sort a.coeff.support]
    exact (Equiv.sum_comp a.coeff.support.equivFin.symm (fun x : a.coeff.support => a.coeff x • τ x)).symm
  rw [hsum ρ, hsum σ]
  exact charpoly_sum_smul_eq_of_charpoly_eq n ρ σ h _ _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMulLeftEqMapOfSpanningLatticeStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_mulLeft_eq_map_of_span_range_eq : ∀ (R F A S : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] [CommRing A] [Algebra F A] [Algebra R A] [IsScalarTower R F A] [Module.Finite F A] [CommRing S] [Algebra R S] [Module.Finite R S] (ι : S →ₐ[R] A), Function.Injective ι → Submodule.span F (Set.range ι) = ⊤ → ∃ (n : ℕ) (b : Module.Basis (Fin n) R S), ∀ x : S, (LinearMap.mulLeft F (ι x)).charpoly = ((LinearMap.toMatrix b b (LinearMap.mulLeft R x)).charpoly).map (algebraMap R F) := by
  first | exact @GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice | exact GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice | (intros; apply GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMulLeftSeparableOfAdjoinEqTopStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_mulLeft_separable_of_adjoin_eq_of_reduced : ∀ (E A : Type) [Field E] [CharZero E] [CommRing A] [Algebra E A] [Module.Finite E A] (y : A), Algebra.adjoin E ({y} : Set A) = ⊤ → IsReduced A → (LinearMap.mulLeft E y).charpoly.Separable := by
  first | exact @GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top | exact GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top | (intros; apply GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyNilpotentAddScalarStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_nilpotent_add_scalar' : ∀ (k : Type) [Field k] (n : ℕ) (N : Matrix (Fin n) (Fin n) k) (c : k), IsNilpotent N → (N + Matrix.scalar (Fin n) c).charpoly = (X - C c) ^ n := by
  first | exact @GlobalTheory.charpoly_nilpotent_add_scalar | exact GlobalTheory.charpoly_nilpotent_add_scalar | (intros; apply GlobalTheory.charpoly_nilpotent_add_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffAevalOneAddXPowSubOneNeZeroStatement
section
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_aeval_one_add_X_pow_sub_one_ne_zero' : ∀ (k σ : Type) [Field k] [Fintype σ] (l M : ℕ) [Fact l.Prime] [CharP k l] (D u : MvPolynomial σ k) (n e : σ → ℕ), u.coeff 0 ≠ 0 → D - u * ∏ q, MvPolynomial.X q ^ n q ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) → ∑ q, n q * l ^ e q < l ^ M → (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) D).coeff (∑ q, n q * l ^ e q) ≠ 0 := by
  first | exact @GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero | exact GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero | (intros; apply GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroSmulMemMapOfAevalMulEqZero
section
open scoped PowerSeries Pointwise
namespace GlobalTheory

theorem coeff_zero_smul_mem_map_of_aeval_mul_eq_zero : ∀ {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (T : Module.End O V) (Rp : Polynomial O), Polynomial.aeval T Rp * T = 0 → ∀ (Z : Submodule O V), (∀ z ∈ Z, T z ∈ Z) → ∀ w ∈ Z, w ∈ LinearMap.range T → Rp.coeff 0 • w ∈ Z.map T := by
  first
  | exact @_root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map
  | exact _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map
  | (apply _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactDvrAdicCompleteSeparatedUniformizerStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_dvr_adic_complete_separated_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (ϖ : O), Irreducible ϖ → (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧ (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  first | exact @GlobalTheory.compact_dvr_complete_separated | exact GlobalTheory.compact_dvr_complete_separated | (intros; apply GlobalTheory.compact_dvr_complete_separated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceInvariantConstOnFrameTranslateStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruenceInvariant_const_on_frame_translate : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ), (∀ h : GL (Fin r ⊕ Fin t) O, (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O).map (algebraMap O K) * x) = Φ x) → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → Φ x = Φ ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)).map (algebraMap O K) * ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)) := by
  first | exact @GlobalTheory.invariant_const_on_translate | exact GlobalTheory.invariant_const_on_translate | (intros; apply GlobalTheory.invariant_const_on_translate <;> assumption)
end

