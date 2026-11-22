import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionsOfComaximalStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_projections_tensor_of_comaximal : ∀ (R F : Type) [CommRing R] [CommRing F] (a : ℕ) (t : Fin a → (F →+* R)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → ∃ e : Fin a → R ⊗[ℤ] F, ∀ (M : Type) [AddCommGroup M] (Θ : R ⊗[ℤ] F →+* AddMonoid.End M) (i l : Fin a) (m : M), (∀ c : F, Θ (1 ⊗ₜ c) m = Θ (t l c ⊗ₜ 1) m) → Θ (e i) m = if i = l then m else 0 := by
  first | (exact @GlobalTheory.eigenProjections_of_comaximal) | (exact GlobalTheory.eigenProjections_of_comaximal) | (intros; apply GlobalTheory.eigenProjections_of_comaximal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigencharactersFiniteOfCommutingAnnihilatedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_eigencharacters_of_eigenvector : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V)) (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) → (∀ t ∈ T, p t ≠ 0) → ∃ X' : Set (Module.End ℂ V → ℂ), X'.Finite ∧ ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → ∀ (χ' : Module.End ℂ V → ℂ) (u : V), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V))) → u ≠ 0 → (∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), χ' z = χ z := by
  first | exact @GlobalTheory.eigencharacters_finite_of_commuting_annihilated | exact GlobalTheory.eigencharacters_finite_of_commuting_annihilated | (intros; apply GlobalTheory.eigencharacters_finite_of_commuting_annihilated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMapMaximalIdealOfRingKrullDimEqOneStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_map_maximalIdeal_of_ringKrullDim_eq_one' : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A] (p : Ideal A) [p.IsPrime], (maximalIdeal R).map (algebraMap R A) ≤ p → ringKrullDim (Localization.AtPrime p) = 1 → IsDomain (A ⧸ (maximalIdeal R).map (algebraMap R A)) → p = (maximalIdeal R).map (algebraMap R A) := by
  first | exact @GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one | exact GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one | (intros; apply GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def secAlg {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) : A →+* Γ(T, U) :=
  (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.appLE_eq_of_eq {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂)
    (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f₁ ⁻¹ᵁ U) (e₂ : V ≤ f₂ ⁻¹ᵁ U) : f₁.appLE U V e₁ = f₂.appLE U V e₂ := by
  subst h
  rfl

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.kappa_comm {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (_root_.GlobalTheory.HilbAff.str A B) g).IdealSheafData) (U : T.Opens) (a : A) :
    ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
      (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)) =
    ((I.subschemeι ≫ pullback.snd _ g).app U).hom (_root_.GlobalTheory.HilbAff.secAlg A g U a) := by
  have key : (I.subschemeι ≫ pullback.fst _ g) ≫ _root_.GlobalTheory.HilbAff.str A B =
      (I.subschemeι ≫ pullback.snd _ g) ≫ g := by
    simp [pullback.condition]
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a) =
      (_root_.GlobalTheory.HilbAff.str A B).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
    have := congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hm : (_root_.GlobalTheory.HilbAff.str A B).appTop ≫
      (I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
        (by simp) = g.appLE ⊤ U (by simp) ≫ (I.subschemeι ≫ pullback.snd _ g).app U := by
    calc _ = ((I.subschemeι ≫ pullback.fst _ g) ≫ _root_.GlobalTheory.HilbAff.str A B).appLE ⊤
          ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) (by simp) :=
          (Scheme.Hom.comp_appLE _ _ _ _ _).symm
      _ = ((I.subschemeι ≫ pullback.snd _ g) ≫ g).appLE ⊤
          ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) (by simp) :=
          _root_.GlobalTheory.HilbAff.appLE_eq_of_eq key _ _ _ _
      _ = _ := by
        rw [Scheme.Hom.app_eq_appLE]
        exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h1]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) hm

def kappa {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra
    Γ(T, U) ⊗[A] B →+* Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
    (((I.subschemeι ≫ pullback.snd _ g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((I.subschemeι ≫ pullback.snd _ g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => kappa_comm A B g I U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem kappa_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) (c : Γ(T, U)) (b : B) :
    letI := (secAlg A g U).toAlgebra
    kappa A B g I U (c ⊗ₜ[A] b) = ((I.subschemeι ≫ pullback.snd _ g).app U).hom c *
      ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
        (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
    (((I.subschemeι ≫ pullback.snd _ g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

def xI (C : Type) [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) :
    (pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
    (Algebra.TensorProduct.comm A B C).toRingHom)) ≫ (pullbackSpecIso A B C).inv).ker

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.basic_iff_kappa {r N : ℕ} (e : Module.Basis (Fin N) A B)
    (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (_root_.GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (hI : _root_.GlobalTheory.HilbAff.Good A B r g I) :
    _root_.GlobalTheory.HilbAff.Basic A B e σ (T := T) ⟨g, ⟨I, hI⟩⟩ ↔ ∀ U : T.affineOpens,
      letI := (_root_.GlobalTheory.HilbAff.secAlg A g U).toAlgebra
      Function.Bijective fun c : Fin r → Γ(T, U) =>
        _root_.GlobalTheory.HilbAff.kappa A B g I U (∑ k, c k ⊗ₜ[A] e (σ k)) := by
  unfold _root_.GlobalTheory.HilbAff.Basic
  refine forall_congr' fun U => ?_
  simp only [map_sum, _root_.GlobalTheory.HilbAff.kappa_tmul]

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.secAlg_res {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) {U V : T.Opens}
    (h : U ≤ V) : (T.presheaf.map (homOfLE h).op).hom.comp (_root_.GlobalTheory.HilbAff.secAlg A g V) =
      _root_.GlobalTheory.HilbAff.secAlg A g U := by
  ext a
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
    (Scheme.Hom.appLE_map g (U := ⊤) (by simp) (homOfLE h).op)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.secAlg_comp {C : Type} [CommRing C] {T : Scheme.{0}}
    (h : T ⟶ Spec (CommRingCat.of C)) (f : A →+* C) (U : T.Opens) :
    _root_.GlobalTheory.HilbAff.secAlg A (h ≫ Spec.map (CommRingCat.ofHom f)) U =
      (_root_.GlobalTheory.HilbAff.secAlg C h U).comp f := by
  have hm : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (h ≫ Spec.map (CommRingCat.ofHom f)).appLE ⊤ U (by simp) =
      CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ h.appLE ⊤ U (by simp) :=
    calc _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (Spec.map (CommRingCat.ofHom f)).appTop ≫ h.appLE ⊤ U (by simp) :=
          congrArg (_ ≫ ·) (Scheme.Hom.comp_appLE h _ ⊤ U _)
      _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (Spec.map (CommRingCat.ofHom f)).appTop) ≫ h.appLE ⊤ U (by simp) :=
          (Category.assoc _ _ _).symm
      _ = (CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv) ≫
          h.appLE ⊤ U (by simp) := by rw [← Scheme.ΓSpecIso_inv_naturality]
      _ = _ := Category.assoc _ _ _
  ext a
  exact congrArg (fun φ => φ.hom a) hm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.eq_of_secAlg_top {T : Scheme.{0}}
    {g₁ g₂ : T ⟶ Spec (CommRingCat.of A)}
    (h : _root_.GlobalTheory.HilbAff.secAlg A g₁ ⊤ = _root_.GlobalTheory.HilbAff.secAlg A g₂ ⊤) :
    g₁ = g₂ := by
  apply ext_of_isAffine
  have e₁ : g₁.appLE ⊤ ⊤ le_top = g₁.appTop := g₁.appLE_eq_app
  have e₂ : g₂.appLE ⊤ ⊤ le_top = g₂.appTop := g₂.appLE_eq_app
  have h' : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g₁.appLE ⊤ ⊤ le_top =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g₂.appLE ⊤ ⊤ le_top := CommRingCat.hom_ext h
  rw [e₁, e₂] at h'
  exact (cancel_epi _).1 h'

end GlobalTheory.HilbAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEvalHermitian
section
set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial GlobalTheory.FibLine

namespace GlobalTheory.FibLine

theorem eq_zero_of_eval_real {σ : Type} (Q : MvPolynomial σ ℂ)
    (h : ∀ x : σ → ℝ, eval (fun i => (x i : ℂ)) Q = 0) : Q = 0 := by
  refine MvPolynomial.funext_set (fun _ => Set.range Complex.ofReal)
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective) ?_
  intro x hx
  have hx' : ∀ i, ∃ r : ℝ, (r : ℂ) = x i := fun i => hx i (Set.mem_univ i)
  choose r hr using hx'
  have : x = fun i => (r i : ℂ) := funext fun i => (hr i).symm
  rw [this, h, map_zero]

def hermSubst (ab : Fin 2 × Fin 2) : MvPolynomial (Fin 2 × Fin 2) ℂ :=
  !![X (0, 0), X (0, 1) + C Complex.I * X (1, 0); X (0, 1) - C Complex.I * X (1, 0), X (1, 1)] ab.1 ab.2

theorem eval_bind_hermSubst (P : MvPolynomial (Fin 2 × Fin 2) ℂ) (x : Fin 2 × Fin 2 → ℂ) :
    eval x (bind₁ hermSubst P) =
      eval (entries !![x (0, 0), x (0, 1) + Complex.I * x (1, 0); x (0, 1) - Complex.I * x (1, 0), x (1, 1)]) P := by
  have h1 : (fun i => eval x (hermSubst i)) =
      entries !![x (0, 0), x (0, 1) + Complex.I * x (1, 0); x (0, 1) - Complex.I * x (1, 0), x (1, 1)] := by
    funext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [hermSubst, entries]
  rw [← h1]
  exact eval₂Hom_bind₁ (RingHom.id ℂ) x hermSubst P

theorem eq_zero_of_eval_hermitian (P : MvPolynomial (Fin 2 × Fin 2) ℂ)
    (h : ∀ H : Matrix (Fin 2) (Fin 2) ℂ, H.IsHermitian → MvPolynomial.eval (entries H) P = 0) : P = 0 := by
  have hQ : bind₁ hermSubst P = 0 := by
    refine eq_zero_of_eval_real _ fun x => ?_
    rw [eval_bind_hermSubst]
    refine h _ ?_
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.conjTranspose_apply, sub_eq_add_neg]
  refine MvPolynomial.funext fun y => ?_
  have h2 := eval_bind_hermSubst P
    (entries !![y (0, 0), (y (0, 1) + y (1, 0)) / 2; (y (0, 1) - y (1, 0)) / (2 * Complex.I), y (1, 1)])
  rw [hQ] at h2
  rw [map_zero] at h2 ⊢
  rw [h2]
  congr 2
  funext ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> simp [entries] <;> field_simp <;> ring

end GlobalTheory.FibLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallAlgHom
section
open TensorProduct

noncomputable section
namespace GlobalTheory.CxPointsSep

theorem eq_zero_of_forall_algHom {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [IsReduced A] [Algebra.FiniteType k A] (a : A) (h : ∀ e : A →ₐ[k] k, e a = 0) : a = 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hrad : (⊥ : Ideal A).IsRadical := by
    rw [Ideal.isRadical_bot_iff]; infer_instance
  have hj : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance hrad
  rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hb : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : k ≃ₐ[k] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hb
  have := h ((i.symm : (A ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m))
  rw [AlgHom.comp_apply] at this
  have h2 : Ideal.Quotient.mkₐ k m a = 0 := by
    apply i.symm.injective
    rw [map_zero]; exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem isReduced_complex_tensor (D : Type) [CommRing D] [IsDomain D] [Algebra ℚ D]
    [Algebra.FiniteType ℚ D] : IsReduced (ℂ ⊗[ℚ] D) := by
  set K := FractionRing D
  have : Algebra.EssFiniteType ℚ K := inferInstanceAs (Algebra.EssFiniteType ℚ (Localization _))
  have h1 : IsReduced (K ⊗[ℚ] ℂ) := ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_of_essFiniteType K ℂ
  have h2 : IsReduced (ℂ ⊗[ℚ] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ K).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm ℚ ℂ K).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)).toRingHom hinj

theorem exists_det_ne_zero (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (r : ℕ) (f : Fin r → B) (hf : LinearIndependent ℤ f) :
    ∃ x : Fin r → (B →+* ℂ), (Matrix.of fun i j => x i (f j)).det ≠ 0 := by
  classical
  let K := FractionRing B
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ B).FG)
  let D : Subalgebra ℚ K := Algebra.adjoin ℚ ((algebraMap B K) '' (s : Set B))
  have hmem : ∀ b : B, algebraMap B K b ∈ D := by
    intro b
    have hb : b ∈ Algebra.adjoin ℤ (s : Set B) := by rw [hs]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap n => rw [eq_intCast, map_intCast]; exact intCast_mem D n
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  haveI : Algebra.FiniteType ℚ D := by
    rw [← Subalgebra.fg_iff_finiteType]
    have := Subalgebra.fg_adjoin_finset (R := ℚ) (s.image (algebraMap B K))
    simpa [D] using this
  let g : B →+* D := (algebraMap B K).codRestrict D hmem
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective B K (congrArg Subtype.val h)
  have hD : LinearIndependent ℚ (fun j => g (f j)) := by
    rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
    exact hf.map' g.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.mpr hg)
  have hT : LinearIndependent ℂ (fun j => (1 : ℂ) ⊗ₜ[ℚ] g (f j)) :=
    Module.Flat.linearIndependent_one_tmul hD
  haveI : IsReduced (ℂ ⊗[ℚ] D) := isReduced_complex_tensor D
  let pt : ((ℂ ⊗[ℚ] D) →ₐ[ℂ] ℂ) → (B →+* ℂ) := fun φ =>
    (φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℂ) (B := D)).toRingHom).comp g
  let S : Set (Fin r → ℂ) := Set.range fun x : B →+* ℂ => fun j => x (f j)
  have hspan : Submodule.span ℂ S = ⊤ := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let c : Fin r → ℂ := fun i => ℓ (fun j => if i = j then 1 else 0)
    have hℓv : ∀ v, ℓ v = ∑ i, v i * c i := fun v => by
      rw [LinearMap.pi_apply_eq_sum_univ ℓ v]; rfl
    have hu : ∑ i, c i • ((1 : ℂ) ⊗ₜ[ℚ] g (f i)) = 0 := by
      apply eq_zero_of_forall_algHom (k := ℂ)
      intro φ
      have h0 : ℓ (fun j => pt φ (f j)) = 0 := hle (Submodule.subset_span ⟨pt φ, rfl⟩)
      rw [hℓv] at h0
      rw [map_sum, ← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl
    have hc : c = 0 := funext fun i => Fintype.linearIndependent_iff.mp hT c hu i
    apply hℓ
    refine LinearMap.ext fun v => ?_
    rw [hℓv, hc]
    simp
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent ℂ S
  have hb_top : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Fin r → ℂ)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let bb := Module.Basis.mk hli hb_top
  let e : b ≃ Fin r := bb.indexEquiv (Pi.basisFun ℂ (Fin r))
  have hx : ∀ i : Fin r, ∃ x : B →+* ℂ, (fun j => x (f j)) = ((e.symm i : b) : Fin r → ℂ) :=
    fun i => hbS (e.symm i).2
  choose x hx using hx
  refine ⟨x, ?_⟩
  have hrows : LinearIndependent ℂ (fun i => (Matrix.of fun i j => x i (f j)) i) := by
    have : (fun i => (Matrix.of fun i j => x i (f j)) i) = (fun v : b => (v : Fin r → ℂ)) ∘ e.symm := by
      funext i; exact hx i
    rw [this]; exact hli.comp _ e.symm.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

end GlobalTheory.CxPointsSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallResidueFieldFunctionalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_forall_residueField_functional' : ∀ (A M : Type) [CommRing A] [IsReduced A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (x : M), (∀ (p : Ideal A) [p.IsPrime] (l : M →ₗ[A] p.ResidueField), l x = 0) → x = 0 := by
  first | exact @GlobalTheory.eq_zero_of_forall_residueField_functional | exact GlobalTheory.eq_zero_of_forall_residueField_functional | (intros; apply GlobalTheory.eq_zero_of_forall_residueField_functional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssEtaleLocalLeOfDirectedStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_le_of_essEtaleLocal_directed : ∀ (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (U : Subalgebra R T) (μ : Type) [Preorder μ] [IsDirected μ (· ≤ ·)] [Nonempty μ] (V : μ → Subalgebra R T), Monotone V → (∀ x ∈ U, ∃ m, x ∈ V m) → (∀ m, ∀ x ∈ V m, ∀ y ∈ U, x * y = 1 → ∃ z ∈ V m, x * z = 1) → ∀ (W : Subalgebra R T), W ≤ U → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W)) → ∃ m, W ≤ V m := by
  first | exact @GlobalTheory.essEtaleLocal_le_of_directed | exact GlobalTheory.essEtaleLocal_le_of_directed | (intros; apply GlobalTheory.essEtaleLocal_le_of_directed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAdjoinBaseChangeImageStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_adjoin_baseChange_image' : ∀ (R S B : Type) [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] (A₀ : Subalgebra R S) (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.Etale A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀) (S' : Subalgebra R S), A₀ ≤ S' → ∃ (_ : Algebra S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))) (_ : IsScalarTower R S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))), Algebra.Etale S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))) := by
  first | exact @GlobalTheory.etale_adjoin_baseChange_image | exact GlobalTheory.etale_adjoin_baseChange_image | (intros; apply GlobalTheory.etale_adjoin_baseChange_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartLocalizationFiniteTypeFormallyUnramifi
section
open TensorProduct

noncomputable section
namespace GlobalTheory.DenseSec

theorem locQuot_finiteType_formallyUnramified (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A]
    (g : ℕ) (t : Fin g → A) (h : A) (hE : GlobalTheory.DenseSec.EtChart R A t h) (Ω : Type) [Field Ω] [Algebra R Ω]
    (I : Ideal (TensorProduct R Ω A)) :
    letI : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
      (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ I)
        (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
    Algebra.FiniteType (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) ∧
      Algebra.FormallyUnramified (MvPolynomial (Fin g) Ω)
        (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) := by
  letI algPD : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
    (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ I)
      (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
  letI algRA : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  haveI hEt : Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h) := hE
  letI algRP : Algebra (MvPolynomial (Fin g) R) (MvPolynomial (Fin g) Ω) := MvPolynomial.algebraMvPolynomial
  letI algRD : Algebra (MvPolynomial (Fin g) R) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
    ((algebraMap (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))).comp
      (algebraMap (MvPolynomial (Fin g) R) (MvPolynomial (Fin g) Ω))).toAlgebra
  haveI hST := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algRP algPD algRD (fun _ => rfl)
  let f : A →+* Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    (algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))).comp
      ((Ideal.Quotient.mk I).comp (Algebra.TensorProduct.includeRight (R := R) (A := Ω) (B := A)).toRingHom)
  have hf : ∀ a, f a = algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))
      (Ideal.Quotient.mk I (1 ⊗ₜ[R] a)) := fun a => rfl
  have hu : IsUnit (f h) := by rw [hf]; exact IsLocalization.Away.algebraMap_isUnit _
  let ψ0 : Localization.Away h →+* Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    IsLocalization.Away.lift h hu
  have hψ0 : ∀ a, ψ0 (algebraMap A (Localization.Away h) a) = f a := fun a => IsLocalization.lift_eq _ _
  have hΩ : ∀ w : Ω, algebraMap Ω (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) w =
      algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))
        (Ideal.Quotient.mk I (w ⊗ₜ[R] 1)) := by
    intro w
    rw [IsScalarTower.algebraMap_apply Ω (TensorProduct R Ω A ⧸ I)]
    rfl
  have hcomp : ψ0.comp (algebraMap (MvPolynomial (Fin g) R) (Localization.Away h)) =
      algebraMap (MvPolynomial (Fin g) R) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show ψ0 (algebraMap A _ (MvPolynomial.aeval t (MvPolynomial.C r))) =
        MvPolynomial.aeval _ (MvPolynomial.map (algebraMap R Ω) (MvPolynomial.C r))
      rw [hψ0, MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C, hf, hΩ]
      congr 2
      rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
    · intro i
      show ψ0 (algebraMap A _ (MvPolynomial.aeval t (MvPolynomial.X i))) =
        MvPolynomial.aeval _ (MvPolynomial.map (algebraMap R Ω) (MvPolynomial.X i))
      rw [hψ0, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X, hf]
  let ψ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    { ψ0 with commutes' := fun p => RingHom.congr_fun hcomp p }
  let Φ : MvPolynomial (Fin g) Ω ⊗[MvPolynomial (Fin g) R] Localization.Away h →ₐ[MvPolynomial (Fin g) Ω]
      Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ψ (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (p : MvPolynomial (Fin g) Ω) (y : Localization.Away h), Φ (p ⊗ₜ y) = algebraMap _ _ p * ψ0 y :=
    fun p y => Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hQ : ∀ x : TensorProduct R Ω A ⧸ I,
      algebraMap _ (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) x ∈ Φ.range := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul w a =>
      refine ⟨MvPolynomial.C w ⊗ₜ algebraMap A _ a, ?_⟩
      show Φ (MvPolynomial.C w ⊗ₜ algebraMap A _ a) = _
      rw [hΦ, hψ0, hf]
      show MvPolynomial.aeval _ (MvPolynomial.C w) * _ = _
      rw [MvPolynomial.aeval_C, hΩ, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) z
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
    have hs : s = ⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ ^ n := Subtype.ext hn.symm
    have hinv : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I)
        (⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ :
          Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) =
        Φ (1 ⊗ₜ IsLocalization.mk' (Localization.Away h) (1 : A) (⟨h, Submonoid.mem_powers _⟩ : Submonoid.powers h)) := by
      rw [hΦ, map_one, one_mul, IsLocalization.mk'_eq_iff_eq_mul]
      show _ = _ * f h
      rw [← hψ0, ← map_mul, IsLocalization.mk'_spec]
      simp
    have : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) x s ∈ Φ.range := by
      have hpow : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I) s =
          (IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I)
            (⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ :
              Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))) ^ n := by
        rw [hs, ← IsLocalization.mk'_pow, one_pow]
      rw [IsLocalization.mk'_eq_mul_mk'_one, hpow, hinv]
      exact mul_mem (hQ x) (pow_mem (AlgHom.mem_range_self Φ _) n)
    exact this
  exact ⟨Algebra.FiniteType.of_surjective Φ hsurj, Algebra.FormallyUnramified.of_surjective Φ hsurj⟩

end GlobalTheory.DenseSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomToFieldFactorsAlgClosedSubfieldStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_hom_to_field_factors_algClosed_subfield : ∀ (A B K L : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B] [Field K] [IsAlgClosed K] [Field L] (α : A →+* K) (ι : K →+* L) (β : B →+* L), (∀ a ∈ maximalIdeal A, α a = 0) → β.comp (algebraMap A B) = ι.comp α → ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = α ∧ ι.comp ψ = β := by
  first | (exact @GlobalTheory.etale_hom_to_field_lands_in_algClosed_subfield) | (exact GlobalTheory.etale_hom_to_field_lands_in_algClosed_subfield) | (intros; apply GlobalTheory.etale_hom_to_field_lands_in_algClosed_subfield  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureTensorOfEtaleOfIsIntegralStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_integralClosure_tensor : ∀ (S₁ K₁ T : Type) [CommRing S₁] [IsDomain S₁] [IsIntegrallyClosed S₁] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [CommRing T] [Algebra S₁ T],
    Algebra.Etale S₁ T → Algebra.IsIntegral S₁ T →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[S₁] T)) := by
  first | (exact @GlobalTheory.etale_integralClosure_tensor_of_etale_of_isIntegral) | (exact GlobalTheory.etale_integralClosure_tensor_of_etale_of_isIntegral) | (intros; apply GlobalTheory.etale_integralClosure_tensor_of_etale_of_isIntegral  <;> assumption)
end

