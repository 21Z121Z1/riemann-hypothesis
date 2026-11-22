import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0394
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0052
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.DirectSumHT

theorem finrank_split {L A A₁ A₂ : Type} [Field L] [AddCommGroup A] [Module L A] [AddCommGroup A₁] [Module L A₁]
    [AddCommGroup A₂] [Module L A₂] (i₁ : A₁ →ₗ[L] A) (i₂ : A₂ →ₗ[L] A) (p₁ : A →ₗ[L] A₁) (p₂ : A →ₗ[L] A₂)
    (h11 : ∀ x, p₁ (i₁ x) = x) (h22 : ∀ x, p₂ (i₂ x) = x) (h12 : ∀ x, p₁ (i₂ x) = 0) (h21 : ∀ x, p₂ (i₁ x) = 0)
    (hs : ∀ x, i₁ (p₁ x) + i₂ (p₂ x) = x)
    (S : Submodule L A) (S₁ : Submodule L A₁) (S₂ : Submodule L A₂)
    [FiniteDimensional L S₁] [FiniteDimensional L S₂]
    (a₁ : ∀ x ∈ S₁, i₁ x ∈ S) (a₂ : ∀ x ∈ S₂, i₂ x ∈ S) (b₁ : ∀ x ∈ S, p₁ x ∈ S₁) (b₂ : ∀ x ∈ S, p₂ x ∈ S₂) :
    finrank L S = finrank L S₁ + finrank L S₂ := by
  let f : S →ₗ[L] S₁ × S₂ := (p₁.restrict b₁).prod (p₂.restrict b₂)
  have hf : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have e1 : p₁ x = 0 := congrArg (fun y : S₁ × S₂ => (y.1 : A₁)) hx
      have e2 : p₂ x = 0 := congrArg (fun y : S₁ × S₂ => (y.2 : A₂)) hx
      apply Subtype.ext
      have := hs x
      rw [e1, e2, map_zero, map_zero, add_zero] at this
      exact this.symm
    · rintro ⟨y₁, y₂⟩
      refine ⟨⟨i₁ y₁ + i₂ y₂, S.add_mem (a₁ _ y₁.2) (a₂ _ y₂.2)⟩, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change p₁ (i₁ y₁ + i₂ y₂) = y₁
        rw [map_add, h11, h12, add_zero]
      · apply Subtype.ext
        change p₂ (i₁ y₁ + i₂ y₂) = y₂
        rw [map_add, h21, h22, zero_add]
  rw [(LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_prod]

section Funct

variable {Qp : Type} [Field Qp] {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

noncomputable def ext (R : Type) [AddCommGroup R] [Module Qp R] (f : V →ₗ[LL] V') :
    V ⊗[Qp] R →ₗ[LL] V' ⊗[Qp] R :=
  AlgebraTensorModule.map f (LinearMap.id : R →ₗ[Qp] R)

theorem ext_comm {R R' : Type} [AddCommGroup R] [Module Qp R] [AddCommGroup R'] [Module Qp R']
    (f : V →ₗ[LL] V') (u : V →ₗ[LL] V) (u' : V' →ₗ[LL] V') (h : ∀ v, f (u v) = u' (f v))
    (k : R →ₗ[Qp] R') (x : V ⊗[Qp] R) :
    ext R' f (AlgebraTensorModule.map u k x) = AlgebraTensorModule.map u' k (ext R f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ext, h]
  | add a b ha hb => simp only [map_add, ha, hb]

variable {V₁ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]

theorem finrank_split_tensor (R : Type) [AddCommGroup R] [Module Qp R] (e : V ≃ₗ[LL] V₁ × V₂)
    (S : Submodule LL (V ⊗[Qp] R)) (S₁ : Submodule LL (V₁ ⊗[Qp] R)) (S₂ : Submodule LL (V₂ ⊗[Qp] R))
    [FiniteDimensional LL S₁] [FiniteDimensional LL S₂]
    (a₁ : ∀ x ∈ S₁, ext R (e.symm.toLinearMap ∘ₗ LinearMap.inl LL V₁ V₂) x ∈ S)
    (a₂ : ∀ x ∈ S₂, ext R (e.symm.toLinearMap ∘ₗ LinearMap.inr LL V₁ V₂) x ∈ S)
    (b₁ : ∀ x ∈ S, ext R (LinearMap.fst LL V₁ V₂ ∘ₗ e.toLinearMap) x ∈ S₁)
    (b₂ : ∀ x ∈ S, ext R (LinearMap.snd LL V₁ V₂ ∘ₗ e.toLinearMap) x ∈ S₂) :
    finrank LL S = finrank LL S₁ + finrank LL S₂ := by
  refine finrank_split _ _ _ _ ?_ ?_ ?_ ?_ ?_ S S₁ S₂ a₁ a₂ b₁ b₂
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ext]
    | add a b ha hb => simp only [map_add, ha, hb]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ext]
    | add a b ha hb => simp only [map_add, ha, hb]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ext]
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ext]
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp only [ext, AlgebraTensorModule.map_tmul, LinearMap.id_apply, ← TensorProduct.add_tmul]
      congr 1
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply, LinearMap.inr_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add,
        Prod.mk.eta, LinearEquiv.symm_apply_apply]
    | add a b ha hb =>
      simp only [map_add]
      rw [add_add_add_comm, ha, hb]

end Funct

section Per

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem ext_Dcris (f : V →ₗ[LL] V') (h : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ Dcris PD ρ, ext B f x ∈ Dcris PD ρ' := by
  intro x hx
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := ext_comm f (ρ g) (ρ' g) (h g) (((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp) x
  rw [actVB, ← this]
  exact congrArg _ (hx g)

theorem ext_DdR (f : V →ₗ[LL] V') (h : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ DdR PD ρ, ext BdR f x ∈ DdR PD ρ' := by
  intro x hx
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := ext_comm f (ρ g) (ρ' g) (h g) (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) x
  rw [actVdR, ← this]
  exact congrArg _ (hx g)

theorem ext_FildR (f : V →ₗ[LL] V') (h : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    ∀ x ∈ FildR PD ρ τ a, ext BdR f x ∈ FildR PD ρ' τ a := by
  rintro x ⟨⟨h1, h2⟩, y, hy⟩
  refine ⟨⟨ext_DdR PD f h x h1, ?_⟩, ext _ f y, ?_⟩
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h2 ⊢
    intro c
    have := ext_comm f LinearMap.id LinearMap.id (fun _ => rfl)
      (LinearMap.mulLeft Qp (algebraMap K BdR c)) x
    rw [mulVdR, ← this, ← map_smul]
    exact congrArg _ (h2 c)
  · rw [← hy]
    exact (ext_comm f LinearMap.id LinearMap.id (fun _ => rfl) _ y).symm

variable {V₁ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    {ρ₁ : Representation LL G V₁} {ρ₂ : Representation LL G V₂}

omit [Module Qp V] [IsScalarTower Qp LL V] [Module Qp V₁] [IsScalarTower Qp LL V₁]
  [Module Qp V₂] [IsScalarTower Qp LL V₂] in
theorem equivariant (e : V ≃ₗ[LL] V₁ × V₂) (he : ∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2)) :
    (∀ g v, (e.symm.toLinearMap ∘ₗ LinearMap.inl LL V₁ V₂) (ρ₁ g v) =
      ρ g ((e.symm.toLinearMap ∘ₗ LinearMap.inl LL V₁ V₂) v)) ∧
    (∀ g v, (e.symm.toLinearMap ∘ₗ LinearMap.inr LL V₁ V₂) (ρ₂ g v) =
      ρ g ((e.symm.toLinearMap ∘ₗ LinearMap.inr LL V₁ V₂) v)) ∧
    (∀ g v, (LinearMap.fst LL V₁ V₂ ∘ₗ e.toLinearMap) (ρ g v) =
      ρ₁ g ((LinearMap.fst LL V₁ V₂ ∘ₗ e.toLinearMap) v)) ∧
    (∀ g v, (LinearMap.snd LL V₁ V₂ ∘ₗ e.toLinearMap) (ρ g v) =
      ρ₂ g ((LinearMap.snd LL V₁ V₂ ∘ₗ e.toLinearMap) v)) := by
  refine ⟨fun g v => ?_, fun g v => ?_, fun g v => ?_, fun g v => ?_⟩
  · apply e.injective
    simp [he]
  · apply e.injective
    simp [he]
  · simp [he]
  · simp [he]

theorem finrank_Dcris_add (e : V ≃ₗ[LL] V₁ × V₂)
    (he : ∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2))
    [FiniteDimensional LL (Dcris PD ρ₁)] [FiniteDimensional LL (Dcris PD ρ₂)] :
    finrank LL (Dcris PD ρ) = finrank LL (Dcris PD ρ₁) + finrank LL (Dcris PD ρ₂) := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant e he
  exact finrank_split_tensor B e _ _ _ (ext_Dcris PD _ h1) (ext_Dcris PD _ h2) (ext_Dcris PD _ h3)
    (ext_Dcris PD _ h4)

theorem finrank_DdR_add (e : V ≃ₗ[LL] V₁ × V₂)
    (he : ∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2))
    [FiniteDimensional LL (DdR PD ρ₁)] [FiniteDimensional LL (DdR PD ρ₂)] :
    finrank LL (DdR PD ρ) = finrank LL (DdR PD ρ₁) + finrank LL (DdR PD ρ₂) := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant e he
  exact finrank_split_tensor BdR e _ _ _ (ext_DdR PD _ h1) (ext_DdR PD _ h2) (ext_DdR PD _ h3)
    (ext_DdR PD _ h4)

theorem finrank_FildR_add (e : V ≃ₗ[LL] V₁ × V₂)
    (he : ∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2))
    [FiniteDimensional LL (DdR PD ρ₁)] [FiniteDimensional LL (DdR PD ρ₂)] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ₁ τ a) + finrank LL (FildR PD ρ₂ τ a) := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant e he
  haveI : FiniteDimensional LL (FildR PD ρ₁ τ a) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ₁) (fun x hx => hx.1.1)
  haveI : FiniteDimensional LL (FildR PD ρ₂ τ a) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ₂) (fun x hx => hx.1.1)
  exact finrank_split_tensor BdR e _ _ _ (ext_FildR PD _ h1 τ a) (ext_FildR PD _ h2 τ a)
    (ext_FildR PD _ h3 τ a) (ext_FildR PD _ h4 τ a)

end Per

open GlobalTheory.Per.FontaineBound in

private theorem dcris_finite_le {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) :
    Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
      finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
  have := isDomain_cris (P.PD K) (isField_of_tied T)
  have := (P.PD K).finK₀
  have := LL.2
  refine finite_finrank_le (P.PD K).actB
    (fun b b' hb h => GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K b' b hb fun g hg => ?_) ρ
  have h1 := h ⟨g, hg⟩
  rw [P.PD_actB, P.PD_actB] at h1
  rw [mul_comm, h1, mul_comm]

theorem directSum_hodgeTate : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (e : V ≃ₗ[↥LL.1] (V₁ × V₂)), (∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2)) → (IsDR (P.PD K) ρ ↔ IsDR (P.PD K) ρ₁ ∧ IsDR (P.PD K) ρ₂) ∧ (IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ₁ ∧ IsCrys (P.PD K) ρ₂) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) ρ τ a = multV (P.PD K) ρ₁ τ a + multV (P.PD K) ρ₂ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ e he
  obtain ⟨d1, d1'⟩ := GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V₁ ρ₁
  obtain ⟨d2, d2'⟩ := GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V₂ ρ₂
  obtain ⟨f1, c1⟩ := dcris_finite_le T K LL V₁ ρ₁
  obtain ⟨f2, c2⟩ := dcris_finite_le T K LL V₂ ρ₂
  have hV : finrank ↥LL.1 V = finrank ↥LL.1 V₁ + finrank ↥LL.1 V₂ := by
    rw [e.finrank_eq, Module.finrank_prod]
  refine ⟨?_, ?_, fun τ a => ?_⟩
  · unfold IsDR
    rw [finrank_DdR_add (P.PD K) e he, hV, mul_add]
    omega
  · unfold IsCrys
    rw [finrank_Dcris_add (P.PD K) e he, hV, mul_add]
    omega
  · unfold multV
    rw [finrank_FildR_add (P.PD K) e he, finrank_FildR_add (P.PD K) e he τ (a + 1)]
    push_cast
    ring

end GlobalTheory.Per.DirectSumHT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualSelmerClassFromCoeffsKilledByMul
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.DualSub

section Cup

variable {Γ A M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup M']
  [Module A M'] [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M'] {n : ℕ}
  (χ : Γ → ZMod n) (π : Representation A Γ M) (π' : Representation A Γ M') (P : M →+ M' →+ ZMod n)

omit [TopologicalSpace M] [DiscreteTopology M] in

theorem cupB_left (hP : ∀ g x y, P (π g x) (π' g y) = χ g * P x y) (x x' : Γ → M) (y : Γ → M') (w : M)
    (hy : Continuous y) (hy' : ∀ g h, y (g * h) = y g + π' g (y h)) (hx : ∀ g, x' g = x g + (π g w - w))
    (h : CupB χ (fun g m => π' g m) P x y) : CupB χ (fun g m => π' g m) P x' y := by
  obtain ⟨F, hF, h⟩ := h
  refine ⟨F + fun g => P w (y g), hF.add (((IsLocallyConstant.iff_continuous y).2 hy).comp fun m => P w m), fun g k => ?_⟩
  have h1 := h g k
  simp only [hx, map_add, map_sub, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, Pi.add_apply, hy', hP] at h1 ⊢
  linear_combination h1

theorem cupB_right (hP : ∀ g x y, P (π g x) (π' g y) = χ g * P x y) (x : Γ → M) (y y' : Γ → M') (m : M')
    (hx : Continuous x) (hx' : ∀ g h, x (g * h) = x g + π g (x h)) (hm : Continuous fun g => π' g m)
    (hy : ∀ g, y' g = y g - (π' g m - m))
    (h : CupB χ (fun g m => π' g m) P x y) : CupB χ (fun g m => π' g m) P x y' := by
  obtain ⟨F, hF, h⟩ := h
  refine ⟨F + fun g => P (x g) (π' g m), hF.add (((IsLocallyConstant.iff_continuous _).2 (hx.prodMk hm)).comp
    fun p : M × M' => P p.1 p.2), fun g k => ?_⟩
  have h1 := h g k
  have h2 := hP g (x k) (π' k m)
  simp only [hy, map_add, map_sub, AddMonoidHom.add_apply, Pi.add_apply, hx', map_mul, Module.End.mul_apply] at h1 ⊢
  linear_combination h1 + h2

end Cup

theorem exists_compLeft {A Y Y' : Type} [CommRing A] [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y'] {r : ℕ}
    (e : Y →ₗ[A] Y') (m : Fin r → Y') (h : ∀ a, m a ∈ LinearMap.range e) : ∃ m', e.compLeft (Fin r) m' = m := by
  choose m' hm' using h
  exact ⟨m', funext hm'⟩

theorem dualSel_of_smul_cob : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (Y₂ : Type) [AddCommGroup Y₂] [Module A Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] (Y₂' : Type) [AddCommGroup Y₂'] [Module A Y₂'] [TopologicalSpace Y₂'] [DiscreteTopology Y₂'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))) (β₂ : Y₂ →+ Y₂' →+ ZMod (X.l i ^ (nu X i + 1))) (f : Y →ₗ[A] Y₂) (e : Y₂' →ₗ[A] Y') (c t : A), Bal A β → Bal A β₂ → Function.Surjective f → Function.Injective e → (∀ y', (c * t) • y' = 0 → y' ∈ LinearMap.range e) → (∀ y y', β₂ (f y) y' = β y (e y')) → (∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y' g m = m) → t • m = 0) → ∀ y : Z1 (repOn ρ κ⁻¹ Y'), DualSel bkP i s κ ρ β Q y → Cob (repOn ρ κ⁻¹ Y') (fun g => c • y.1 g) → ∃ y₂ : Z1 (repOn ρ κ⁻¹ Y₂'), DualSel bkP i s κ ρ β₂ Q y₂ ∧ Cob (repOn ρ κ⁻¹ Y') (fun g a => y.1 g a - e (y₂.1 g a)) := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ hS hK hD hNI Y _ _ _ _ Y' _ _ _ _ Y₂ _ _ _ _ Y₂' _ _ _ _ β β₂ f e c t hβ hβ₂ hf he hct
    hfe ht y hy hc
  obtain ⟨hcY, hcY', hP, hU⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hS hK hD Y Y' β hβ
  obtain ⟨-, -, hP₂, -⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hS hK hD Y₂ Y₂' β₂ hβ₂
  obtain ⟨m, hm⟩ := hc
  have hE : Function.Injective (e.compLeft (Fin D.R.r)) := fun a b hab => funext fun j => he (congrFun hab j)

  have hq := hNI (Y' ⧸ LinearMap.range (c • (LinearMap.id : Y' →ₗ[A] Y')))
    ((Submodule.mkQ _).compLeft (Fin D.R.r) m) fun g => by
      rw [← repOn_map, ← sub_eq_zero, ← map_sub, ← hm g]
      funext a
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y.1 g a, rfl⟩
  obtain ⟨m', hm'⟩ := exists_compLeft (c • (LinearMap.id : Y' →ₗ[A] Y')) m fun a =>
    (Submodule.Quotient.mk_eq_zero _).1 (congrFun hq a)
  have hm'' : m = c • m' := hm'.symm
  have hcm : Continuous fun g => repOn ρ κ⁻¹ Y' g m' := hcY'.comp (continuous_id.prodMk continuous_const)
  have hkill : ∀ g, c • (y.1 g - (repOn ρ κ⁻¹ Y' g m' - m')) = 0 := fun g => by
    have := hm g
    simp only at this
    rw [smul_sub, this, hm'', map_smul, smul_sub, sub_self]
  have hex : ∀ g, ∃ z, e.compLeft (Fin D.R.r) z = y.1 g - (repOn ρ κ⁻¹ Y' g m' - m') := fun g =>
    exists_compLeft e _ fun a => hct _ (by
      rw [mul_comm, mul_smul]
      have := congrFun (hkill g) a
      rw [Pi.smul_apply] at this
      rw [this, Pi.zero_apply, smul_zero])
  choose z hz using hex
  have hzc : Continuous z := by
    have h1 : IsLocallyConstant fun g => y.1 g - (repOn ρ κ⁻¹ Y' g m' - m') :=
      (IsLocallyConstant.iff_continuous _).2 (y.2.1.sub (hcm.sub continuous_const))
    exact (IsLocallyConstant.iff_continuous _).1 (IsLocallyConstant.desc z (e.compLeft (Fin D.R.r))
      (by rw [show (e.compLeft (Fin D.R.r)) ∘ z = _ from funext hz]; exact h1) hE)
  have hzz : ∀ g h, z (g * h) = z g + repOn ρ κ⁻¹ Y₂' g (z h) := fun g h => hE (by
    rw [map_add, repOn_map, hz, hz, hz, y.2.2, map_mul, Module.End.mul_apply, map_sub, map_sub]
    abel)
  refine ⟨⟨z, hzc, hzz⟩, ⟨fun v h1 h2 h3 τ hτ => hE ?_, fun v hv => ?_, fun v hv x₂ hx₂ => ?_⟩, m', fun g => ?_⟩
  · show e.compLeft _ (z τ) = _
    rw [hz, hy.1 v h1 h2 h3 τ hτ, (hU v h1 h2 h3 _ (N.plOm.2 v) τ hτ).2]
    simp
  · obtain ⟨m₀, hm₀⟩ := hy.2.1 v hv
    have h1 := ht v hv (c • (m₀ - m')) fun g hg => by
      have := hkill g
      rw [hm₀ g hg] at this
      rw [map_smul, map_sub, ← sub_eq_zero, ← smul_sub, ← this]
      congr 1
      abel
    obtain ⟨m₂, hm₂⟩ := exists_compLeft e (m₀ - m') fun a => hct _ (by
      rw [mul_comm, mul_smul]
      exact congrFun h1 a)
    refine ⟨m₂, fun g hg => hE ?_⟩
    show e.compLeft _ (z g) = _
    rw [hz, map_sub, repOn_map, hm₂, hm₀ g hg, map_sub]
    abel
  · obtain ⟨xc, hxc, hxe⟩ := GlobalTheory.T.bkOn_le_map_h1MapSubgroup_of_surjective D N X bkP i s A κ Q hS hK Y Y₂ f hf v hx₂
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xc
    have h1 := hy.2.2 v hv x hxc
    have h2 := cupB_right _ ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype) ((repOn ρ κ⁻¹ Y').comp (DecV N v).subtype)
      (vecPair D.R.r β) (fun g => hP g.1) x.1 _ (fun g => e.compLeft _ (z g.1)) m' x.2.1 x.2.2
      (hcm.comp continuous_subtype_val) (fun g => hz g.1) h1
    have h3 : (Submodule.Quotient.mk x₂ : H1 _) = Submodule.Quotient.mk (cocycles1MapOfEquivariant _ _ (f.compLeft (Fin D.R.r))
        continuous_of_discreteTopology (fun g m => repOn_map (Tgl i s) κ f g.1 m) x) := hxe.symm
    obtain ⟨w, hw⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 h3)
    refine cupB_left _ ((repOn (Tgl i s) κ Y₂).comp (DecV N v).subtype) ((repOn ρ κ⁻¹ Y₂').comp (DecV N v).subtype)
      (vecPair D.R.r β₂) (fun g => hP₂ g.1) (fun g => f.compLeft _ (x.1 g)) x₂.1 (fun g => z g.1) w
      (hzc.comp continuous_subtype_val) (fun g h => hzz g.1 h.1) (fun g => ?_) ?_
    · rw [← hw g]
      exact (add_sub_cancel _ _).symm
    · obtain ⟨F, hF, h2⟩ := h2
      refine ⟨F, hF, fun g h => ?_⟩
      rw [← h2 g h]
      show vecPair _ β₂ _ (repOn ρ κ⁻¹ Y₂' g.1 (z h.1)) = vecPair _ β _ (repOn ρ κ⁻¹ Y' g.1 (e.compLeft _ (z h.1)))
      rw [← repOn_map, vecPair_apply, vecPair_apply]
      exact Finset.sum_congr rfl fun a _ => hfe _ _
  · have : (fun a => y.1 g a - e (z g a)) = y.1 g - e.compLeft _ (z g) := rfl
    show (fun a => y.1 g a - e (z g a)) = _
    rw [this, hz, sub_sub_cancel]

end GlobalTheory.DualSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdIffDvdCoeffBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (a : bk.S) (x : A), s a ∣ x ↔ ∀ i, a ∣ TB.c i x := by
  intro l _ K bk A _ s ι TB a x
  haveI hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨TB.c i y, TB.c_mul i a y⟩
  · intro h
    by_cases ha : a = 0
    · subst ha
      refine ⟨0, ?_⟩
      rw [mul_zero]
      exact h1 x fun i => zero_dvd_iff.1 (h i)
    · choose z hz using h
      obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul bk.J (M := bk.S) (Submodule.span bk.S {a})
      have key : ∀ (n : ℕ) (w : bk.S), a * w ∈ bk.J ^ (n + k) → w ∈ bk.J ^ n := by
        intro n w hw
        have hmem : a * w ∈ bk.J ^ (n + k) • (⊤ : Submodule bk.S bk.S) ⊓ Submodule.span bk.S {a} := by
          refine Submodule.mem_inf.2 ⟨?_, ?_⟩
          · rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hw
          · exact Submodule.mem_span_singleton.2 ⟨w, by rw [smul_eq_mul, mul_comm]⟩
        rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at hmem
        have h2 : bk.J ^ n • (bk.J ^ k • (⊤ : Submodule bk.S bk.S) ⊓ Submodule.span bk.S {a}) ≤
            bk.J ^ n * Ideal.span {a} :=
          Submodule.smul_mono le_rfl inf_le_right
        obtain ⟨v, hv, hva⟩ := Ideal.mem_mul_span_singleton.1 (h2 hmem)
        have hwv : w = v := mul_left_cancel₀ ha (by rw [← hva, mul_comm])
        exact hwv ▸ hv
      have hfin : ∀ n : ℕ, {i | z i ∉ bk.J ^ n}.Finite := fun n =>
        (TB.fin x (n + k)).subset fun i hi hx => hi (key n (z i) (hz i ▸ hx))
      obtain ⟨y, hy⟩ := h4 z hfin
      refine ⟨y, ?_⟩
      have h0 := h1 (x - s a * y) fun i => by
        rw [map_sub, TB.c_mul, hy, hz, sub_self]
      exact sub_eq_zero.1 h0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowDvdOfBdRPlusDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.DivTransfer

theorem div_transfer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), aDp l (bk.ev bk.E) ≠ 0 ∧
    ∀ (m : ℕ) (s : bk.S), aDp l (bk.ev bk.E) ^ m ∣ aDp l (bk.ev s) → bk.E ^ m ∣ s := by
  intro l _ K bk

  have hF := fun m => (GlobalTheory.AinfEPow.ePow_facts l K bk m).2.2.1
  have hS := fun m => (GlobalTheory.AinfEPow.ePow_facts l K bk m).2.1
  refine ⟨fun h0 => ?_, fun m s hd => ?_⟩
  · have h2 : bk.ev bk.E ^ 2 ∣ bk.ev bk.E := (hF 2 (bk.ev bk.E)).1 (by rw [h0]; exact Ideal.zero_mem _)
    obtain ⟨c, hc⟩ := hS 2 bk.E h2
    have h1 : bk.E * 1 = bk.E * (bk.E * c) := by rw [mul_one]; nth_rewrite 1 [hc]; ring
    have hu : bk.E * c = 1 := (mul_left_cancel₀ bk.E_ne_zero h1).symm
    have hmem : (1 : Ainf l) ∈ RingHom.ker (Per.θ l) := by
      rw [← bk.span_ev, ← map_one bk.ev, ← hu, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [RingHom.mem_ker, map_one] at hmem
    exact one_ne_zero hmem
  · apply hS m s
    apply (hF m _).1
    obtain ⟨c, hc⟩ := hd
    rw [hc, ← map_pow, ← map_pow]
    exact Ideal.mul_mem_right _ _ ((hF m _).2 (by rw [map_pow]))

end GlobalTheory.BSP.DivTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisPhiPowEigenvectorDoubleSeries
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem exists_acris_Lam : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (y : ℕ → Fl l), 2 ≤ h → (∀ k, ‖sh (y k)‖ ≤ ‖(l : ℂ_[l])‖) → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = abelian₂ h j y := by
  intro l _ h y hh hy
  choose w hw hθ using fun k => GlobalTheory.T.exists_frobeniusSeries_acris_untilt l h (y k) hh (hy k)
  haveI : IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := (GlobalTheory.MemLoc.acris_basic l).1
  obtain ⟨W, hW, hsum⟩ := GlobalTheory.T.exists_eigenvector_hasSum_adicComplete_frobenius l (Acris l) (GlobalTheory.MemLoc.phiA l) h w hw
  refine ⟨W, hW, fun Θ hΘ htm j => ?_⟩
  set φ := GlobalTheory.MemLoc.phiA l
  have hS := hsum (Θ.comp (φ ^ j)) (fun a => hΘ _)
  simp only [RingHom.coe_comp, RingHom.coe_pow, Function.comp_apply] at hS
  unfold abelian₂
  rw [← hS.tsum_eq]
  congr 1
  funext k
  rw [hθ k Θ hΘ htm j]

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfLevelBasesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adicTopologicalBasis_of_level_bases : ∀ (A : Type) [CommRing A] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (s : A →+* L) (i : L →+* Q) (J : Ideal A) (ι : Type) (m : ι → L) (k₀ : ι), m k₀ = 1 → IsAdicComplete J A → IsCompl i (J.map s) → (∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s) → (∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n) → ∃ tb : TopBasis (i.comp s) J ι, ∀ k, tb.b k = i (m k) := by
  first | exact @GlobalTheory.BSP.exists_topBasis_of_levels | exact GlobalTheory.BSP.exists_topBasis_of_levels | (intros; apply GlobalTheory.BSP.exists_topBasis_of_levels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemUpperRamificationGroupJumpSumNotMemStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_upperRamificationGroup_jumpSum_not_mem' : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)), lowerRamificationGroup F L 0 = ⊤ → B ≠ ⊤ → ∃ σ ∈ upperRamificationGroup F L ((jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ)), σ ∉ B := by
  first | exact @GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem | exact GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem | (intros; apply GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem <;> assumption)
end

