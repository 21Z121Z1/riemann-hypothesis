import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraZmodTorsorBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeBoundByPartials
section
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

theorem GlobalTheory.norm_iteratedFDeriv_succ_le_sum_partial :
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : X → ℂ), ContDiff ℝ ∞ g → ∀ (n : ℕ) (z : X),
      ‖iteratedFDeriv ℝ (n + 1) g z‖ ≤ C * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (Module.finBasis ℝ X i)) z‖ := by
  intro X _ _ _
  set b := Module.finBasis ℝ X
  let L : Fin (Module.finrank ℝ X) → ℂ →L[ℝ] X →L[ℝ] ℂ := fun i =>
    ContinuousLinearMap.smulRightL ℝ X ℂ (LinearMap.toContinuousLinearMap (b.coord i))
  refine ⟨∑ i, ‖L i‖, Finset.sum_nonneg (fun i _ => norm_nonneg _), ?_⟩
  intro g hg n z
  have hsm : ∀ i, ContDiff ℝ ∞ (fun w => fderiv ℝ g w (b i)) := fun i =>
    (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdec : fderiv ℝ g = fun w => ∑ i, (L i ∘ (fun w => fderiv ℝ g w (b i))) w := by
    funext w
    apply ContinuousLinearMap.ext
    intro v
    have hv := b.sum_repr v
    simp [L, ContinuousLinearMap.sum_apply]
    conv_lhs => rw [← hv, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, Complex.real_smul]
  have key : iteratedFDeriv ℝ n (fderiv ℝ g) z =
      ∑ i, iteratedFDeriv ℝ n (⇑(L i) ∘ fun w => fderiv ℝ g w (b i)) z := by
    conv_lhs => rw [hdec]
    rw [iteratedFDeriv_sum (fun i _ => ((L i).contDiff.comp (hsm i)).of_le (by exact_mod_cast le_top)),
      Finset.sum_apply]
  rw [← norm_iteratedFDeriv_fderiv, key]
  calc ‖∑ i, iteratedFDeriv ℝ n (⇑(L i) ∘ fun w => fderiv ℝ g w (b i)) z‖
      ≤ ∑ i, ‖iteratedFDeriv ℝ n (⇑(L i) ∘ fun w => fderiv ℝ g w (b i)) z‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖L i‖ * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (b i)) z‖ := by
        gcongr with i
        exact (L i).norm_iteratedFDeriv_comp_left (hsm i).contDiffAt (by exact_mod_cast le_top)
    _ ≤ ∑ i, (∑ j, ‖L j‖) * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (b i)) z‖ := by
        gcongr with i
        exact Finset.single_le_sum (f := fun j => ‖L j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    _ = (∑ j, ‖L j‖) * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (b i)) z‖ := by
        rw [Finset.mul_sum]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdelicSL2
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_ideal_eq_of_span_of_linearIndependent
    (A B R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] {r : ℕ}
    (v : Fin r → B) (J₁ J₂ : Ideal (R ⊗[A] B)) (h12 : J₁ ≤ J₂)
    (hspan : Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) = ⊤)
    (hli : LinearIndependent R (fun k => Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k))) :
    J₁ = J₂ := by
  refine le_antisymm h12 (fun t ht => ?_)
  have hmem : Ideal.Quotient.mk J₁ t ∈ Submodule.span R
      (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  set s : R ⊗[A] B := ∑ k, c k • ((1 : R) ⊗ₜ[A] v k) with hs
  have hmk : ∀ (J : Ideal (R ⊗[A] B)), Ideal.Quotient.mk J s
      = ∑ k, c k • Ideal.Quotient.mk J ((1 : R) ⊗ₜ[A] v k) := by
    intro J
    rw [hs, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Ideal.Quotient.mkₐ_eq_mk R, map_smul]
  have h1 : t - s ∈ J₁ := by
    rw [← Ideal.Quotient.eq, hmk J₁, hc]
  have h2 : s ∈ J₂ := by
    have := J₂.sub_mem ht (h12 h1)
    simpa using this
  have hsum : ∑ k, c k • Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k) = 0 := by
    rw [← hmk J₂, Ideal.Quotient.eq_zero_iff_mem]; exact h2
  have hc0 : ∀ k, c k = 0 := Fintype.linearIndependent_iff.1 hli c hsum
  have hs0 : s = 0 := by simp [hs, hc0]
  rw [hs0, sub_zero] at h1
  exact h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerWedgeFormMapEqSmulOfBasis
section
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.TopFormAppend

theorem dForm_append_eq_smul : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by
  intro k K L _ _ _ cK cL j hc n r x w bK hbK f hf t
  let a : Matrix (Fin n) (Fin n) K := Matrix.of fun i l => bK.repr (dFun cK (x i)) l
  have ha : ∀ i, dFun cK (x i) = ∑ l, a i l • dFun cK (w l) := fun i => by
    conv_lhs => rw [← bK.sum_repr (dFun cK (x i))]
    exact Finset.sum_congr rfl fun l _ => by rw [hbK]; rfl
  have hdet : a.det = f :=
    (isFreeGen_dForm w bK hbK).1 ((dForm_eq_det_smul x w a ha).symm.trans hf)
  have hL : ∀ i, dFun cL (j (x i)) = ∑ l, j (a i l) • dFun cL (j (w l)) := fun i => by
    letI := cK.toAlgebra
    letI := cL.toAlgebra
    letI := j.toAlgebra
    haveI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' hc.symm
    have := congrArg (KaehlerDifferential.map k k K L) (ha i)
    rw [map_sum] at this
    simp only [map_smul, KaehlerDifferential.map_D] at this
    refine this.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [← algebraMap_smul L]
    rfl
  let M : Matrix (Fin (r + n)) (Fin (r + n)) L :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 (j.mapMatrix a))
  have hM : M.det = j f := by
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
      ← RingHom.map_det, hdet]
  rw [← hM]
  refine dForm_eq_det_smul _ _ M fun i => ?_
  rw [Fin.sum_univ_add]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [M, Matrix.one_apply, Fin.append_left]
  · simp [M, Fin.append_right, hL]

end GlobalTheory.TopFormAppend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaApplyEq
section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem theta_comm {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) (a : A) :
    ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)) =
    ((pullback.snd (str A B) g).app U).hom (secAlg A g U a) := by
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a) =
      (str A B).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) :=
    congrArg (fun f => f.hom a) h1
  have key : (str A B).appTop ≫ (pullback.fst (str A B) g).appLE ⊤
      ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) =
      g.appLE ⊤ U (by simp) ≫ (pullback.snd (str A B) g).app U := by
    calc _ = (pullback.fst (str A B) g ≫ str A B).appLE ⊤
          ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) :=
          (Scheme.Hom.comp_appLE _ _ _ _ _).symm
      _ = (pullback.snd (str A B) g ≫ g).appLE ⊤
          ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) :=
          appLE_eq_of_eq (by simp [pullback.condition]) _ _ _ _
      _ = _ := by
          rw [Scheme.Hom.app_eq_appLE]; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h2, secAlg, RingHom.comp_apply, ← CommRingCat.comp_apply, key, CommRingCat.comp_apply]

def theta {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra
    Γ(T, U) ⊗[A] B →+* Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((pullback.snd (str A B) g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((pullback.fst (str A B) g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => theta_comm A B g U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem theta_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens)
    (c : Γ(T, U)) (b : B) :
    letI := (secAlg A g U).toAlgebra
    theta A B g U (c ⊗ₜ[A] b) = ((pullback.snd (str A B) g).app U).hom c *
      ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U)
        (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem kappa_apply_eq {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) (x : letI := (secAlg A g U).toAlgebra; Γ(T, U) ⊗[A] B) :
    kappa A B g I U x =
      (I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U)).hom (theta A B g U x) := by
  letI := (secAlg A g U).toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul c b =>
    rw [kappa_tmul, theta_tmul, map_mul]
    congr 1
    have e : (pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) ≫
        I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U) =
        (I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤
          ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) := by
      rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    rw [← e]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

theorem ker_kappa_eq {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    RingHom.ker (kappa A B g I U) =
      Ideal.comap (theta A B g U) (RingHom.ker (I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U)).hom) := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, kappa_apply_eq]; exact Iff.rfl

def psi (C : Type) [CommRing C] [Algebra A C] :
    C ⊗[A] B →+* Γ(pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C))), ⊤) :=
  (pullbackSpecIso A B C).hom.appTop.hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv.hom.comp
      (Algebra.TensorProduct.comm A C B).toRingHom)

end GlobalTheory.HilbAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorToSubschemeSectionsRestric
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem kappa_res_apply (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (str A B) g).IdealSheafData)
    {U V : T.Opens} (h : U ≤ V) :
    letI := (secAlg A g U).toAlgebra; letI := (secAlg A g V).toAlgebra
    ∀ (ρ : Γ(T, V) →ₐ[A] Γ(T, U)), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom →
    ∀ t : Γ(T, V) ⊗[A] B,
      kappa A B g I U (Algebra.TensorProduct.map ρ (AlgHom.id A B) t) =
        (I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono
          (I.subschemeι ≫ pullback.snd _ g) h)).op).hom (kappa A B g I V t) := by
  letI := (secAlg A g U).toAlgebra; letI := (secAlg A g V).toAlgebra
  intro ρ hρ t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c b =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, kappa_tmul, kappa_tmul, map_mul]
    have hc : ρ c = (T.presheaf.map (homOfLE h).op).hom c := by
      rw [← hρ]; rfl
    rw [hc]
    congr 1
    · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
      rfl
    · have e := Scheme.Hom.appLE_map (I.subschemeι ≫ pullback.fst _ g) (U := ⊤)
          (V := (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ V) (by simp)
          (homOfLE (Scheme.Hom.preimage_mono (I.subschemeι ≫ pullback.snd _ g) h)).op
      exact (congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) e).symm

theorem kappa_res (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (U V : T.affineOpens) (h : (U : T.Opens) ≤ V) :
    letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra; letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
    ∃ ρ : Γ(T, V) →ₐ[A] Γ(T, U), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom ∧
      (RingHom.ker (GlobalTheory.HilbAff.kappa A B g I V)).map
        (Algebra.TensorProduct.map ρ (AlgHom.id A B)) ≤ RingHom.ker (GlobalTheory.HilbAff.kappa A B g I U) := by
  letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra; letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
  let ρ : Γ(T, V) →ₐ[A] Γ(T, U) :=
    { toRingHom := (T.presheaf.map (homOfLE h).op).hom
      commutes' := fun a => by
        change _ = GlobalTheory.HilbAff.secAlg A g U a
        rw [← GlobalTheory.HilbAff.secAlg_res A g h]; rfl }
  refine ⟨ρ, rfl, ?_⟩
  rw [Ideal.map_le_iff_le_comap]
  intro t ht
  rw [RingHom.mem_ker] at ht
  rw [Ideal.mem_comap, RingHom.mem_ker]
  erw [GlobalTheory.HilbAff.kappa_res_apply A B g I h ρ rfl t, ht, map_zero]

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovMatrixConjEqOfCharpolyEqStatement
section
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krylovMatrix_conj_eq_of_charpoly_eq : ∀ {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F) (e e' : Fin r → F), y.charpoly = y'.charpoly → IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det → IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y' e').det → (GlobalTheory.LeviDesc.Krylov.krylov y e)⁻¹ * y * GlobalTheory.LeviDesc.Krylov.krylov y e = (GlobalTheory.LeviDesc.Krylov.krylov y' e')⁻¹ * y' * GlobalTheory.LeviDesc.Krylov.krylov y' e' := by
  first | exact @GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq | exact GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq | (intros; apply GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraFiniteProjectiveFaithfullyFlatStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerAlgebra_finite_projective_faithfullyFlat : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap B (fun _ : Fin q => L) B), 0 < q → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → Module.Finite B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.Projective B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.FaithfullyFlat B (GlobalTheory.KummerAlg.Alg φ) := by
  first | exact @GlobalTheory.KummerAlg.finite_projective_faithfullyFlat | exact GlobalTheory.KummerAlg.finite_projective_faithfullyFlat | (intros; apply GlobalTheory.KummerAlg.finite_projective_faithfullyFlat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraZmodTorsorBijectiveStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerAlgebra_zmod_torsor_bijective : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) [NeZero q] (φ : MultilinearMap B (fun _ : Fin q => L) B), IsUnit (q : B) → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → ∀ (ζ : B) (hζ : ζ ^ q = 1), (∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) → Function.Bijective (Algebra.TensorProduct.productMap (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun _ => AlgHom.id B (GlobalTheory.KummerAlg.Alg φ))) (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun g => (GlobalTheory.KummerAlg.act φ ζ hζ g).toAlgHom))) := by
  first | exact @GlobalTheory.KummerTorsor.bijective | exact GlobalTheory.KummerTorsor.bijective | (intros; apply GlobalTheory.KummerTorsor.bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaCoeffCommutesModeDerivation
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem exL_dL_holds : GlobalTheory.PsCo.Cw2a.T_exL_dL := by
  intro n L ε x b
  have h := GlobalTheory.T.coeff_allOnes_sumAlgEquiv_derivation_eq (σ := EntIdx n) (L := L) (dM ε x) b
  simpa [exL, dL, inL, allOnes] using h

end GlobalTheory.PsCo.Cw2a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeformationMultiplication
section
namespace GlobalTheory

theorem diag_coords_of_holomorphic_lattice_family : ∀ (Ω : Type) [NormedAddCommGroup Ω] [NormedSpace ℂ Ω] (g : ℕ) (K : Type) (ρ : K → Fin g → ℂ),
    (∀ a j, starRingEnd ℂ (ρ a j) = ρ a j) → (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ a, ∀ x ∈ Λ, (fun j ↦ ρ a j * x j) ∈ Λ) →
    ∀ (V : Set Ω) (τ : Ω → Λ →+ (Fin g → ℂ)), IsOpen V → (0 : Ω) ∈ V → (∀ x, τ 0 x = x) →
    (∀ x, DifferentiableOn ℂ (fun z ↦ τ z x) V) →
    (∀ z ∈ V, ∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      ∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
    ∃ (V' : Set Ω) (D : Ω → (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (ζ : Ω → Fin g → ℂ),
      IsOpen V' ∧ (0 : Ω) ∈ V' ∧ V' ⊆ V ∧ DifferentiableOn ℂ ζ V' ∧ ζ 0 = 0 ∧ (∀ z ∈ V', ∀ j, ‖ζ z j‖ < 1) ∧
      (∀ z ∈ V', ∀ x : Λ, D z (τ z x) = fun j ↦ (x : Fin g → ℂ) j + ζ z j * starRingEnd ℂ ((x : Fin g → ℂ) j)) ∧
      ∀ z ∈ V', ∀ a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
        (∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
        ∀ w, D z (M w) = fun j ↦ ρ a j * D z w j := by
  intro Ω _ _ g K ρ hreal hsep Λ hd hs hΛ V τ hV h0 hτ0 hτd hM
  obtain ⟨ρr, hρ⟩ : ∃ ρr : K → Fin g → ℝ, ∀ a j, ((ρr a j : ℝ) : ℂ) = ρ a j :=
    ⟨fun a j ↦ (ρ a j).re, fun a j ↦ Complex.conj_eq_iff_re.mp (hreal a j)⟩
  have hsepr : ∀ j k, j ≠ k → ∃ a, ρr a j ≠ ρr a k := by
    intro j k hjk
    obtain ⟨a, ha⟩ := hsep j k hjk
    exact ⟨a, fun h ↦ ha (by rw [← hρ, ← hρ, h])⟩
  obtain ⟨n, b, c, hbc, hφ⟩ := GlobalTheory.T.lattice_real_coordinate_basis g Λ hd hs
  obtain ⟨T, hTapp⟩ : ∃ T : Ω → (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ),
      ∀ z v, T z v = ∑ i, c i v • τ z (b i) :=
    ⟨fun z ↦ ∑ i, (c i).smulRight (τ z (b i)), fun z v ↦ by simp⟩
  have hTΛ : ∀ z (x : Λ), T z x = τ z x := fun z x ↦ by rw [hTapp]; exact hφ (τ z) x
  have hT0 : ∀ v, T 0 v = v := fun v ↦ by rw [hTapp]; simp only [hτ0]; exact hbc v
  have hTd : ∀ v, DifferentiableOn ℂ (fun z ↦ T z v) V := by
    intro v
    simp only [hTapp]
    have := DifferentiableOn.sum (u := Finset.univ) (A := fun i z ↦ c i v • τ z (b i))
      (fun i _ ↦ (hτd (b i)).const_smul (c i v))
    simpa [Finset.sum_fn] using this
  have hcomm : ∀ z a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
      ∀ v, T z (fun m ↦ (ρr a m : ℂ) * v m) = M (T z v) := by
    intro z a M hMz
    let Dg : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
      { toFun := fun v m ↦ ρ a m * v m
        map_add' := by intro v w; ext m; simp [mul_add]
        map_smul' := by intro r v; ext m; simp; ring }
    have key := LinearMap.ext_on (f := (T z).comp Dg) (g := (M.restrictScalars ℝ).comp (T z)) hs (by
      intro x hx
      have hx' : (fun j ↦ ρ a j * x j) ∈ Λ := hΛ a x hx
      have e := hMz ⟨x, hx⟩ ⟨_, hx'⟩ rfl
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
      rw [← hTΛ, ← hTΛ] at e
      exact e)
    intro v
    have := LinearMap.congr_fun key v
    simpa [Dg, hρ] using this
  obtain ⟨α, hα⟩ : ∃ α : Ω → Fin g → ℂ, ∀ z j,
      α z j = (T z (Pi.single j 1) j - Complex.I * T z (Pi.single j Complex.I) j) / 2 := ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Ω → Fin g → ℂ, ∀ z j,
      β z j = (T z (Pi.single j 1) j + Complex.I * T z (Pi.single j Complex.I) j) / 2 := ⟨_, fun _ _ ↦ rfl⟩
  have hTs : ∀ z j (y : ℂ), T z (Pi.single j y) j = α z j * y + β z j * starRingEnd ℂ y := by
    intro z j y
    have hy : (Pi.single j y : Fin g → ℂ) = y.re • (Pi.single j 1 : Fin g → ℂ) + y.im • (Pi.single j Complex.I : Fin g → ℂ) := by
      ext m
      rcases eq_or_ne m j with rfl | h
      · simp only [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply, Complex.real_smul, mul_one]
        exact (Complex.re_add_im y).symm
      · simp [h]
    rw [hy, map_add, map_smul, map_smul, hα, hβ]
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    have hc : starRingEnd ℂ y = (y.re : ℂ) - (y.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hc]
    have hy2 : y = (y.re : ℂ) + (y.im : ℂ) * Complex.I := (Complex.re_add_im y).symm
    linear_combination (-(T z (Pi.single j 1) j - Complex.I * T z (Pi.single j Complex.I) j) / 2) * hy2
      + ((y.im : ℂ) * T z (Pi.single j Complex.I) j) * Complex.I_sq
  have hα0 : ∀ j, α 0 j = 1 := by
    intro j; rw [hα, hT0, hT0]; simp [Complex.I_mul_I]
  have hβ0 : ∀ j, β 0 j = 0 := by
    intro j; rw [hβ, hT0, hT0]; simp [Complex.I_mul_I]
  have hαd : ∀ j, DifferentiableOn ℂ (fun z ↦ α z j) V := by
    intro j; simp only [hα]
    have h3 : DifferentiableOn ℂ (fun z ↦ T z (Pi.single j 1) j - Complex.I * T z (Pi.single j Complex.I) j) V :=
      (differentiableOn_pi.1 (hTd _) j).sub ((differentiableOn_pi.1 (hTd _) j).const_mul Complex.I)
    simpa [div_eq_mul_inv] using h3.mul_const (2 : ℂ)⁻¹
  have hβd : ∀ j, DifferentiableOn ℂ (fun z ↦ β z j) V := by
    intro j; simp only [hβ]
    have h3 : DifferentiableOn ℂ (fun z ↦ T z (Pi.single j 1) j + Complex.I * T z (Pi.single j Complex.I) j) V :=
      (differentiableOn_pi.1 (hTd _) j).add ((differentiableOn_pi.1 (hTd _) j).const_mul Complex.I)
    simpa [div_eq_mul_inv] using h3.mul_const (2 : ℂ)⁻¹
  set V' : Set Ω := V ∩ ⋂ j, (V ∩ (fun z ↦ ‖α z j‖ - ‖β z j‖) ⁻¹' Set.Ioi 0) with hV'
  have hV'o : IsOpen V' := by
    refine hV.inter (isOpen_iInter_of_finite fun j ↦ ContinuousOn.isOpen_inter_preimage ?_ hV isOpen_Ioi)
    exact ((hαd j).continuousOn.norm).sub (hβd j).continuousOn.norm
  have hV'm : ∀ z ∈ V', z ∈ V ∧ ∀ j, ‖β z j‖ < ‖α z j‖ := by
    intro z hz
    simp only [hV', Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi, sub_pos] at hz
    exact ⟨hz.1, fun j ↦ (hz.2 j).2⟩
  have h0' : (0 : Ω) ∈ V' := by
    simp only [hV', Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi, sub_pos, hα0, hβ0]
    simp [h0]
  have hαne : ∀ z ∈ V', ∀ j, α z j ≠ 0 := fun z hz j ↦
    norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) ((hV'm z hz).2 j))
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω → Fin g → ℂ, ∀ z j, ζ z j = β z j / α z j := ⟨_, fun _ _ ↦ rfl⟩
  have hζd : DifferentiableOn ℂ ζ V' := by
    refine differentiableOn_pi.2 fun j ↦ ?_
    simp only [hζ]
    have hsub : V' ⊆ V := fun z hz ↦ (hV'm z hz).1
    simp only [div_eq_mul_inv]
    exact ((hβd j).mono hsub).mul (((hαd j).mono hsub).inv fun z hz ↦ hαne z hz j)
  have hpt : ∀ z ∈ V', ∃ Dz : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ v, Dz (T z v) = fun j ↦ v j + β z j / α z j * starRingEnd ℂ (v j)) ∧
      ∀ a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ v, T z (fun m ↦ (ρr a m : ℂ) * v m) = M (T z v)) →
        ∀ w, Dz (M w) = fun j ↦ (ρr a j : ℂ) * Dz w j := by
    intro z hz
    have hMex : ∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
        ∀ v, T z (fun m ↦ (ρr a m : ℂ) * v m) = M (T z v) := fun a ↦ by
      obtain ⟨M, hMz⟩ := hM z (hV'm z hz).1 a
      exact ⟨M, hcomm z a M hMz⟩
    obtain ⟨Dz, h1, h2⟩ := GlobalTheory.T.exists_antilinear_normal_form g (T z) (GlobalTheory.T.exists_coordinate_projection_complex g K ρr hsepr (T z) hMex) (α z) (β z) (hV'm z hz).2 (hTs z)
    exact ⟨Dz, h1, fun a M hMa w ↦ h2 (ρr a) M hMa w⟩
  classical
  let D : Ω → (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := fun z ↦
    if hz : z ∈ V' then Classical.choose (hpt z hz) else LinearEquiv.refl ℂ _
  refine ⟨V', D, ζ, hV'o, h0', fun z hz ↦ (hV'm z hz).1, hζd, ?_, ?_, ?_, ?_⟩
  · funext j; rw [hζ, hβ0]; simp
  · intro z hz j
    rw [hζ, norm_div, div_lt_one (norm_pos_iff.mpr (hαne z hz j))]
    exact (hV'm z hz).2 j
  · intro z hz x
    have := (Classical.choose_spec (hpt z hz)).1 x
    simp only [D, dif_pos hz]
    rw [← hTΛ, this]
    funext j; rw [hζ]
  · intro z hz a M hMz w
    have := (Classical.choose_spec (hpt z hz)).2 a M (hcomm z a M hMz) w
    simp only [D, dif_pos hz]
    rw [this]; simp only [hρ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationOfLsmulShiftStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeDetRelation_of_lsmul_shift : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (p q : ℕ) (F : Submodule C (Fin (p + q) → C)) (X0 : Submodule w.valuationSubring (Fin (p + q) → C)) (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F)) (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring), d ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ (d : C)) := by
  first | exact @GlobalTheory.detRel_of_detRel_lsmul | exact GlobalTheory.detRel_of_detRel_lsmul | (intros; apply GlobalTheory.detRel_of_detRel_lsmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpanInfRationalSubspaceIntegersExtStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_span_inf_rational_subspace_integers_ext : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (n : ℕ) (M : Submodule (𝓞 K) (Fin n → K)) (W : Submodule K (Fin n → K)), Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' (M : Set (Fin n → K))) ⊓ (Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K)))).restrictScalars (𝓞 L) = Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
  first | exact @GlobalTheory.span_inf_span_eq_span_inf_of_rational | exact GlobalTheory.span_inf_span_eq_span_inf_of_rational | (intros; apply GlobalTheory.span_inf_span_eq_span_inf_of_rational <;> assumption)
end

