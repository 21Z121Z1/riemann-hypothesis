import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0959
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureSumZero
section
noncomputable section

open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SchrodTheta

variable {F : Type} [Field F] [NumberField F]

def HasTheta {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) (f : W → ℂ) : Prop :=
  ∀ x, HasSum (fun ξ : κ → F => co.rho ψ x Φ fun i => algebraMap F (AF F) (ξ i)) (f x)

def IsPureSum {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (φ₀ : (κ → Fv F v₁) → ℂ) (Φ : (κ → AF F) → ℂ) : Prop :=
  ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ),
    Φ = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in cofinite, φ k v = vac v) ∧
      ∀ k, φ k v₁ = φ₀

theorem isPureSum_zero {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ)
    (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (φ₀ : (κ → Fv F v₁) → ℂ) : IsPureSum vac v₁ φ₀ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, by simp, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0⟩

theorem IsPureSum.smul {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {φ₀ : (κ → Fv F v₁) → ℂ} {Φ : (κ → AF F) → ℂ} (h : IsPureSum vac v₁ φ₀ Φ) (c : ℂ) :
    IsPureSum vac v₁ φ₀ (c • Φ) := by
  obtain ⟨m, f, φ, rfl, h1, h2, h3⟩ := h
  refine ⟨m, fun k => c • f k, φ, ?_, h1, h2, h3⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]
  ring

theorem IsPureSum.add {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {φ₀ : (κ → Fv F v₁) → ℂ} {Φ Ψ : (κ → AF F) → ℂ} (h : IsPureSum vac v₁ φ₀ Φ)
    (h' : IsPureSum vac v₁ φ₀ Ψ) : IsPureSum vac v₁ φ₀ (Φ + Ψ) := by
  first
  | exact @_root_.GlobalTheory.ClosingLemmaThird.main
  | exact _root_.GlobalTheory.ClosingLemmaThird.main
  | (apply _root_.GlobalTheory.ClosingLemmaThird.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosingLemmaThird.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosingLemmaThird.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosingLemmaThird.main ..)

theorem IsPureSum.sum {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {φ₀ : (κ → Fv F v₁) → ℂ} {ι : Type} (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ)
    (h : ∀ k ∈ s, IsPureSum vac v₁ φ₀ (Φ k)) : IsPureSum vac v₁ φ₀ (∑ k ∈ s, Φ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPureSum_zero vac v₁ φ₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

section Theta

variable {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
  (co : Darboux B κ) (ψ : AddChar (AF F) ℂ)

theorem rho_smul (x : W) (c : ℂ) (Φ : (κ → AF F) → ℂ) : co.rho ψ x (c • Φ) = c • co.rho ψ x Φ := by
  funext y
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem hasTheta_zero : HasTheta co ψ 0 0 := fun x => by
  have : co.rho ψ x 0 = 0 := by simpa using rho_smul co ψ x 0 0
  simpa [this] using (hasSum_zero : HasSum (fun _ : κ → F => (0 : ℂ)) 0)

variable {co ψ}

theorem HasTheta.smul {Φ : (κ → AF F) → ℂ} {f : W → ℂ} (h : HasTheta co ψ Φ f) (c : ℂ) :
    HasTheta co ψ (c • Φ) (c • f) := fun x => by
  rw [rho_smul]
  exact (h x).mul_left c

theorem HasTheta.add {Φ Ψ : (κ → AF F) → ℂ} {f g : W → ℂ} (h : HasTheta co ψ Φ f) (h' : HasTheta co ψ Ψ g) :
    HasTheta co ψ (Φ + Ψ) (f + g) := by
  intro x
  have h0 := (h x).add (h' x)
  simpa only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply, mul_add] using h0

theorem HasTheta.sum {ι : Type} (s : Finset ι) {Φ : ι → (κ → AF F) → ℂ} {f : ι → W → ℂ}
    (h : ∀ k ∈ s, HasTheta co ψ (Φ k) (f k)) : HasTheta co ψ (∑ k ∈ s, Φ k) (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasTheta_zero co ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem HasTheta.thetaSum_eq {Φ : (κ → AF F) → ℂ} {f : W → ℂ} (h : HasTheta co ψ Φ f) (x : W) :
    thetaSum F (co.rho ψ x Φ) = f x :=
  (h x).tsum_eq

end Theta

end GlobalTheory.SchrodTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvNLevi

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

def qI (F : Type) [Field F] [NumberField F] : F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    ((RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap F (AdeleRing (𝓞 F) F)))

def qF (F : Type) [Field F] [NumberField F] : F →+* FiniteAdeleRing (𝓞 F) F :=
  (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap F (AdeleRing (𝓞 F) F))

def compM (P : Matrix κ κ F) : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x => P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x)

theorem compM_apply (P : Matrix κ κ F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (x : κ → AdeleRing (𝓞 F) F) :
    compM P φ x = φ (P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) := rfl

def archEquiv (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) where
  toFun y := P.map (qI F) *ᵥ y
  invFun y := Q.map (qI F) *ᵥ y
  map_add' y y' := Matrix.mulVec_add _ _ _
  map_smul' r y := by rw [RingHom.id_apply, Matrix.mulVec_smul]
  left_inv y := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  right_inv y := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def finHomeo (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) where
  toFun z := P.map (qF F) *ᵥ z
  invFun z := Q.map (qF F) *ᵥ z
  left_inv z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  right_inv z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem comp_pureA (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    compM P (pureA F f g) =
      pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv P Q hPQ hQP) f) (g ∘ finHomeo P Q hPQ hQP) := by
  funext x
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let p : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i).1) =
      P.map (qI F) *ᵥ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) := by
    funext i
    change q ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i) = _
    rw [RingHom.map_mulVec, Matrix.map_map]
    rfl
  have h2 : (fun i => ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i).2) =
      P.map (qF F) *ᵥ (fun i => (x i).2) := by
    funext i
    change p ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i) = _
    rw [RingHom.map_mulVec, Matrix.map_map]
    rfl
  simp only [compM_apply, pureA, Function.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rw [h1, h2]
  rfl

theorem comp_mem (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ∀ φ ∈ schA F κ, compM P φ ∈ schA F κ := by
  have hle : schA F κ ≤ (schA F κ).comap (compM P) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    refine Submodule.subset_span ⟨_, _, ⟨hg.1.comp_continuous (finHomeo P Q hPQ hQP).continuous,
      hg.2.comp_homeomorph (finHomeo P Q hPQ hQP)⟩, comp_pureA P Q hPQ hQP f g⟩
  exact fun φ hφ => hle hφ

theorem act_levi {K R ι : Type} [Field K] [CommRing R] [Algebra K R] [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K)
    (w : (ι → R) × (ι → R)) :
    AdelicSvN.act (Matrix.fromBlocks A 0 0 B) w = (A.map (algebraMap K R) *ᵥ w.1, B.map (algebraMap K R) *ᵥ w.2) := by
  have h0 : (0 : Matrix ι ι K).map (algebraMap K R) = 0 := Matrix.map_zero _ (map_zero _)
  simp only [AdelicSvN.act, Matrix.fromBlocks_map, h0, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, add_zero, zero_add]

theorem dot_transpose {R ι : Type} [CommRing R] [Fintype ι] (M : Matrix ι ι R) (x v : ι → R) :
    x ⬝ᵥ (Mᵀ *ᵥ v) = (M *ᵥ x) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem realised_levi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ]
    [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det → Realised ψ (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ) := by
  intro F _ _ ψ κ _ _ A hA
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  let Am : Matrix κ κ (AdeleRing (𝓞 F) F) := A.map (algebraMap F (AdeleRing (𝓞 F) F))
  let Aim : Matrix κ κ (AdeleRing (𝓞 F) F) := A⁻¹.map (algebraMap F (AdeleRing (𝓞 F) F))
  have e1 : Am * Aim = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : Aim * Am = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨compM A⁻¹, comp_mem A⁻¹ A h2 h1, fun φ hφ => ⟨compM A φ, comp_mem A A⁻¹ h1 h2 φ hφ, ?_⟩,
    fun l hl => ⟨l ∘ₗ compM A⁻¹, fun g hg => ?_, fun _ _ => rfl⟩, fun w φ _ => funext fun x => ?_⟩
  · funext x
    change φ (Am *ᵥ (Aim *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A⁻¹ A h2 h1).continuous,
      hg.2.comp_homeomorph (finHomeo A⁻¹ A h2 h1)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A⁻¹ A h2 h1)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A⁻¹ A h2 h1, hT]
    rfl
  · rw [act_levi, Matrix.transpose_map]
    change ψ ((Aim *ᵥ x) ⬝ᵥ w.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)) * φ (Aim *ᵥ x + w.1) =
      ψ (x ⬝ᵥ (Aimᵀ *ᵥ w.2) + ⅟(2 : AdeleRing (𝓞 F) F) * ((Am *ᵥ w.1) ⬝ᵥ (Aimᵀ *ᵥ w.2))) *
        φ (Aim *ᵥ (x + Am *ᵥ w.1))
    rw [dot_transpose, dot_transpose, Matrix.mulVec_add, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]

end GlobalTheory.AdelicSvNLevi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Matrix

namespace GlobalTheory.AdelicSvN.Weyl

variable {F : Type} [Field F] [NumberField F]

theorem trace_eq_mixedTrace (m : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) m = mixedTrace F m := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi, mixedTrace_apply]
  simp only [Algebra.trace_complex_apply, Algebra.trace_self_apply]

theorem isStd_infinite {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (z : InfiniteAdeleRing F) :
    ψ (infiniteAdeleInl z) = (adelicChar F (infiniteAdeleInl z) : ℂ) := by
  have hat : At (evI F) (infiniteAdeleInl z : AF F) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  have h2 : adelicChar F (infiniteAdeleInl z) = Real.fourierChar (-infiniteTrace F z) := adelicChar_infinite z
  rw [hψ.2.2 _ hat, h2, trace_eq_mixedTrace, ← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_apply,
    Real.fourierChar_apply]
  congr 1
  have : evI F (infiniteAdeleInl z) = InfiniteAdeleRing.ringEquiv_mixedSpace F z := rfl
  rw [this]
  push_cast
  ring

theorem isStd_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AF F) : ψ a = (adelicChar F a : ℂ) := by
  have hfin : ∀ y : FiniteAdeleRing (𝓞 F) F,
      ψ (finiteAdeleInr y) = (adelicChar F (finiteAdeleInr y) : ℂ) := by
    intro y
    refine (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).induction_on
      (p := fun y => ψ (finiteAdeleInr y) = (adelicChar F (finiteAdeleInr y) : ℂ)) y
      (isClosed_eq (hψ.1.comp continuous_finiteAdeleInr)
        (continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp continuous_finiteAdeleInr))) fun k => ?_
    have hs := infiniteAdeleInl_add_finiteAdeleInr (algebraMap F (AF F) k)
    rw [adeleRing_algebraMap_fst, adeleRing_algebraMap_snd] at hs
    have e : (finiteAdeleInr (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) : AF F) =
        algebraMap F (AF F) k + infiniteAdeleInl (-algebraMap F (InfiniteAdeleRing F) k) := by
      rw [← hs, map_neg]; abel
    rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.2.1, adelicChar_algebraMap, one_mul, one_mul,
      isStd_infinite hψ]
  rw [← infiniteAdeleInl_add_finiteAdeleInr a, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, Circle.coe_mul,
    isStd_infinite hψ, hfin]

variable {κ : Type} [Fintype κ]

theorem pureA_eq (f : SInf F κ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f g = schwartzBruhatTensorPi f g := by
  funext x
  simp only [pureA, schwartzBruhatTensorPi]
  rfl

omit [Fintype κ] in
theorem mem_SB_iff (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ↔ g ∈ finiteSchwartzBruhatPi F :=
  (mem_finiteSchwartzBruhatPi F).symm

theorem schA_eq : schA F κ = schwartzBruhatPi F κ := by
  unfold schA schwartzBruhatPi
  congr 1

def fourierLin : schA F κ →ₗ[ℂ] (κ → AF F) → ℂ where
  toFun φ := adelicFourierPi F φ.1
  map_add' φ φ' := adelicFourierPi_add (integrable_of_mem_schwartzBruhatPi (schA_eq (F := F) (κ := κ) ▸ φ.2))
    (integrable_of_mem_schwartzBruhatPi (schA_eq (F := F) (κ := κ) ▸ φ'.2))
  map_smul' c φ := adelicFourierPi_smul c φ.1

theorem act_weyl [DecidableEq κ] (w : (κ → AF F) × (κ → AF F)) :
    act (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) w = (w.2, -w.1) := by
  have h0 : (0 : Matrix κ κ F).map (algebraMap F (AF F)) = 0 := Matrix.map_zero _ (map_zero _)
  have h1 : (1 : Matrix κ κ F).map (algebraMap F (AF F)) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : (-1 : Matrix κ κ F).map (algebraMap F (AF F)) = -1 := by rw [Matrix.map_neg _ (map_neg _), h1]
  simp only [act, Matrix.fromBlocks_map, h0, h1, h2, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero]

theorem integral_add_right_pi (f : (κ → AF F) → ℂ) (a : κ → AF F) :
    ∫ x, f (x + a) ∂(adeleMeasurePi F) = ∫ x, f x ∂(adeleMeasurePi F) := by
  let _ : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F
  have : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleRing F
  have : BorelSpace (κ → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have : MeasurableAdd (κ → AdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  exact integral_add_right_eq_self f a

theorem fourier_schr {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ) :
    adelicFourierPi F (schr ψ w φ) = schr ψ (w.2, -w.1) (adelicFourierPi F φ) := by
  funext y
  simp only [adelicFourierPi, schr, ← isStd_eq hψ]
  rw [← integral_const_mul, ← integral_add_right_pi _ (-w.1)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h2 : ⅟(2 : AF F) + ⅟(2 : AF F) = 1 := invOf_two_add_invOf_two
  have e : ((x + -w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (x + -w.1) ⬝ᵥ y =
      (y ⬝ᵥ -w.1 + ⅟(2 : AF F) * (w.2 ⬝ᵥ -w.1)) + x ⬝ᵥ (y + w.2) := by
    simp only [add_dotProduct, dotProduct_add, neg_dotProduct, dotProduct_neg, dotProduct_comm y w.1,
      dotProduct_comm w.2 w.1]
    linear_combination (w.1 ⬝ᵥ w.2) * h2
  have e' := congrArg ψ e
  rw [AddChar.map_add_eq_mul ψ _ ((x + -w.1) ⬝ᵥ y), AddChar.map_add_eq_mul ψ _ (x ⬝ᵥ (y + w.2))] at e'
  simp only [neg_add_cancel_right]
  change _ * _ * ψ ((x + -w.1) ⬝ᵥ y) = _ * (_ * ψ (x ⬝ᵥ (y + w.2)))
  linear_combination φ x * e'

theorem realised_weyl : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ], Realised ψ (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) := by
  intro F _ _ ψ hψ κ _ _
  have hk : ∀ φ ∈ schA F κ, adelicFourierPi F φ ∈ schA F κ := fun φ hφ => by
    rw [schA_eq] at hφ ⊢
    exact adelicFourierPi_mem_schwartzBruhatPi hφ
  have hinv : ∀ φ ∈ schA F κ, adelicFourierPi F (adelicFourierPi F φ) = fun x => φ (-x) := fun φ hφ => by
    rw [schA_eq] at hφ
    exact adelicFourierPi_adelicFourierPi hφ
  refine ⟨adelicFourierPi F, hk, fun φ hφ => ⟨_, hk _ (hk _ (hk _ hφ)), ?_⟩, fun l hl => ?_, fun w φ _ => ?_⟩
  · rw [hinv _ (hk _ (hk _ hφ)), hinv _ hφ]
    simp only [neg_neg]
  · obtain ⟨T, hT⟩ := LinearMap.exists_extend (fourierLin (F := F) (κ := κ))
    have hT' : ∀ φ ∈ schA F κ, T φ = adelicFourierPi F φ := fun φ hφ => LinearMap.congr_fun hT ⟨φ, hφ⟩
    refine ⟨l ∘ₗ T, fun g hg => ?_, fun φ hφ => by rw [LinearMap.comp_apply, hT' φ hφ]⟩
    obtain ⟨U, hU⟩ := hl (finiteFourierPi F g) ((mem_SB_iff _).2 (finiteFourierPi_mem ((mem_SB_iff g).1 hg)))
    refine ⟨U.comp (mixedFourierPiSchwartz F), fun f => ?_⟩
    rw [LinearMap.comp_apply, hT' _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), ContinuousLinearMap.comp_apply, ← hU,
      pureA_eq, pureA_eq, adelicFourierPi_schwartzBruhatTensorPi]
  · rw [act_weyl, fourier_schr hψ]

end GlobalTheory.AdelicSvN.Weyl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOperatorGLnSmoothAffineTranslationSection
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem kerOpInf_section : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T → IsKerOpInf (fun W z g => χ z * T (smoothMatInf α W) z (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹)) := by
  intro E _ _ n Z _ _ _ σ₀ L χ α hχ hχc hσ hα hαc hαs T hT
  have hdet : ∀ w : InfinitePlace E, ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      (Matrix.of (σ₀ + L p.1)).det w := by
    intro w
    simp only [Matrix.det_apply', Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Finset.prod_apply]
    refine ContDiff.sum fun s _ => ?_
    refine ContDiff.mul ?_ (contDiff_prod fun i _ => ?_)
    · exact contDiff_const
    have : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) => σ₀ + L p.1 :=
      contDiff_const.add (L.contDiff.comp contDiff_fst)
    exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 this (s i)) i) w
  have hJ : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) := by
    simp only [jacInf, Complex.ofReal_prod, Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self]
    exact contDiff_prod fun w _ => ((Complex.conjCLE.contDiff.comp (hdet w)).mul (hdet w)).pow n
  have hΦ : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      χ p.1 * ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) * α p.2 :=
    ((hχ.comp contDiff_fst).mul hJ).mul (hα.comp contDiff_snd)
  have hΦc : HasCompactSupport fun p : Z × (Fin n → Fin n → Cinf E) =>
      χ p.1 * ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) * α p.2 := by
    refine HasCompactSupport.intro (hχc.isCompact.prod hαc.isCompact) fun p hp => ?_
    rcases not_and_or.1 hp with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  obtain ⟨X, _, ν, _, κ, τ, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_rapid_superposition_characters' _ _ hΦ hΦc
  obtain ⟨R, hR⟩ := GlobalTheory.T.smoothing_affine_family_eq_integral_kernel E n Z σ₀ L χ α hχc hσ hαc hαs X ν κ τ h1 h2 h3 (fun z a => h4 (z, a))
  exact GlobalTheory.T.archimedeanRapidKernelOperator_comp_rapidFamily E n Z T hT _ _ _ _ _ (GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ h1 h2 h3 R σ₀ L) (smoothMatInf α) _ χ
    (GlobalTheory.T.archimedeanMatrixSmoothing_moderateGrowth E n α hα.continuous hαc hαs) hR

end GlobalTheory.JSW.MirCinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirstStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_isometry_sign_first : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → R.vP i t = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) (R.vacP i) := by
  first | exact @GlobalTheory.DatumFourier.thetaVector_eq_sum_heisenberg | exact GlobalTheory.DatumFourier.thetaVector_eq_sum_heisenberg | (intros; apply GlobalTheory.DatumFourier.thetaVector_eq_sum_heisenberg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkReducedClosedGenericPointEqRank
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory

namespace GlobalTheory.StalkLength

theorem length_stalk_pushforward {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i]
    (F : Y.Modules) (y : Y) :
    Module.length (X.presheaf.stalk (i y))
        (((Scheme.Modules.pushforward i).obj F).presheaf.stalk (i y) :) =
      Module.length (Y.presheaf.stalk y) (F.presheaf.stalk y :) := by
  let G := (Scheme.Modules.pushforward i).obj F
  let φ := i.stalkMap y
  letI : Algebra (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) := φ.hom.toAlgebra
  letI : Module (X.presheaf.stalk (i y)) (F.presheaf.stalk y :) :=
    Module.compHom _ (algebraMap (X.presheaf.stalk (i y)) (Y.presheaf.stalk y))
  haveI : IsScalarTower (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) (F.presheaf.stalk y :) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let Ψ : (G.presheaf.stalk (i y) :) →+ (F.presheaf.stalk y :) :=
    (F.presheaf.stalkPushforward _ i.base y).hom
  have hΨ (U : X.Opens) (hU : i y ∈ U) (s : Γ(G, U)) :
      Ψ (G.presheaf.germ U _ hU s) = F.presheaf.germ (i ⁻¹ᵁ U) y hU s :=
    congr($(TopCat.Presheaf.stalkPushforward_germ _ i.base F.presheaf U y hU).hom s)
  have hiso := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing _
    (f := i.base) i.isClosedEmbedding.isInducing F.presheaf y
  have hbij : Function.Bijective Ψ :=
    ConcreteCategory.bijective_of_isIso (F.presheaf.stalkPushforward _ i.base y)
  have hsmul (a : X.presheaf.stalk (i y)) (m : (G.presheaf.stalk (i y) :)) :
      Ψ (a • m) = φ.hom a • Ψ m := by
    obtain ⟨U₁, hU₁, r, rfl⟩ := X.presheaf.germ_exist a
    obtain ⟨U₂, hU₂, s, rfl⟩ := G.presheaf.germ_exist m
    have hU : i y ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
    rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) _ hU,
      ← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) _ hU]
    generalize X.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op r = r'
    generalize G.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op s = s'
    rw [← GlobalTheory.QCoh.germ_smul G, hΨ, hΨ]
    refine (GlobalTheory.QCoh.germ_smul F (U := i ⁻¹ᵁ (U₁ ⊓ U₂)) _ _ (i.app _ r') s').trans ?_
    congr 1
    exact congr($(Scheme.Hom.germ_stalkMap i (U₁ ⊓ U₂) y hU).hom r').symm
  let e : (G.presheaf.stalk (i y) :) ≃ₗ[X.presheaf.stalk (i y)] (F.presheaf.stalk y :) :=
    { AddEquiv.ofBijective Ψ hbij with map_smul' := hsmul }
  exact e.length_eq.trans (Module.length_eq_of_surjective (i.stalkMap_surjective y))

theorem length_stalk_pushforward_genericPoint : ∀ (X : Scheme.{0}) (Z : Closeds X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
    (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [GlobalTheory.QCoh.IsFiniteQC G],
    Module.length (X.presheaf.stalk (redι Z (genericPoint _)))
      (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk (redι Z (genericPoint _)) :) =
      (GlobalTheory.VB.genRank G : ℕ∞) := by
  intro X Z _ G _
  rw [length_stalk_pushforward]
  exact Module.length_eq_finrank (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.functionField
    (GlobalTheory.VB.genStalk G)

end GlobalTheory.StalkLength
end

