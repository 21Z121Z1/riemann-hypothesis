import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibrePrincipalBundleSignEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCongruenceSelfDualOfPrincipalLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovolCong

theorem smul_mem_hat (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (S T : Set (Fin n → E)) (b : E) (hb : ∀ x ∈ S, b • x ∈ T) :
    ∀ z ∈ GlobalTheory.AdLat.hat F S, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b) • z ∈ GlobalTheory.AdLat.hat F T := by
  intro z hz
  let φ : (Fin n → GlobalTheory.AdLat.RA F E) →+ (Fin n → GlobalTheory.AdLat.RA F E) :=
    DistribMulAction.toAddMonoidHom _ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b)
  have hle : GlobalTheory.AdLat.hat F S ≤ (GlobalTheory.AdLat.hat F T).comap φ := by
    unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    refine AddSubgroup.subset_closure ⟨a, ha, b • x, hb x hx, ?_⟩
    funext i
    simp only [φ, DistribMulAction.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact hle hz

theorem inv_smul_mem {D : D7} (V : HSp D) (I : Ideal (𝓞 D.host.E)) (b : D.host.E)
    (hb : b ∈ (D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))
    (y : Fin V.rank → D.host.E)
    (hy : y ∈ (I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))) :
    b • y ∈ (I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) := by
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hsub := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.2
  let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    (b • LinearMap.id : (Fin V.rank → D.host.E) →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)
  have hf : (Formalism.L2.Pj.latG V 1).map f ≤ GlobalTheory.Member.latC V := by
    rw [hsub, Submodule.map_span_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    have hba : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [← inv_mul_cancel₀ hA]
      exact FractionalIdeal.mul_mem_mul hb ha
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hba
    have : f (a • x) = r • x := by
      simp only [f, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      rw [← hr, algebraMap_smul]
    rw [this]
    exact Submodule.smul_mem _ r hx
  have h1 : f y ∈ (I • Formalism.L2.Pj.latG V 1).map f := Submodule.mem_map_of_mem hy
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl hf h1

theorem gen_mem {D : D7} (V : HSp D) (K : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E))
    (I : Ideal (𝓞 D.host.E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈
      GlobalTheory.AdLat.hat D.host.F ((I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)))
    (c : FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hc : ∀ v : HeightOneSpectrum (𝓞 D.host.F), c v ∈ HeightOneSpectrum.adicCompletionIntegers D.host.F v)
    (x : Fin V.rank → D.host.E) (hx : x ∈ GlobalTheory.Member.latC V) :
    K *ᵥ (fun i => c ⊗ₜ[D.host.F] x i) - (fun i => c ⊗ₜ[D.host.F] x i) ∈
      GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)) := by
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hsub := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.2
  let ψ : (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) →+ (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    AddMonoidHom.mk' (fun z => K *ᵥ z - z) (fun x y => by rw [Matrix.mulVec_add]; abel)
  have hψs : ∀ (s : GlobalTheory.AdLat.RA D.host.F D.host.E) z, ψ (s • z) = s • ψ z := by
    intro s z
    simp only [ψ, AddMonoidHom.mk'_apply, Matrix.mulVec_smul, smul_sub]
  have h1 : (1 : D.host.E) ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
      ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hA]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have key := Submodule.mul_induction_on (C := fun t : D.host.E => ψ (fun i => c ⊗ₜ[D.host.F] (t * x i)) ∈
      GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E))) h1 ?_ ?_
  · simp only [one_mul] at key
    exact key
  · intro m hm b hb
    have hw : (fun i => c ⊗ₜ[D.host.F] (m * x i)) ∈
        GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)) := by
      refine AddSubgroup.subset_closure ⟨c, hc, m • x, ?_, rfl⟩
      rw [hsub]
      exact Submodule.subset_span ⟨m, hm, x, hx, rfl⟩
    have h2 := smul_mem_hat D.host.F _ _ b (fun y hy => inv_smul_mem V I b hb y hy) _ (h _ hw)
    have e : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • (K *ᵥ (fun i => c ⊗ₜ[D.host.F] (m * x i)) -
        (fun i => c ⊗ₜ[D.host.F] (m * x i))) = ψ (fun i => c ⊗ₜ[D.host.F] (m * b * x i)) := by
      have : (fun i => c ⊗ₜ[D.host.F] (m * b * x i)) =
          ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • (fun i => c ⊗ₜ[D.host.F] (m * x i)) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 1
        ring
      rw [this, hψs]
      rfl
    rw [← e]
    exact h2
  · intro t t' ht ht'
    have : (fun i => c ⊗ₜ[D.host.F] ((t + t') * x i)) =
        (fun i => c ⊗ₜ[D.host.F] (t * x i)) + (fun i => c ⊗ₜ[D.host.F] (t' * x i)) := by
      funext i
      simp only [Pi.add_apply, add_mul, TensorProduct.tmul_add]
    beta_reduce at ht ht' ⊢
    rw [this, AddMonoidHom.map_add ψ]
    exact (GlobalTheory.AdLat.hat _ _).add_mem ht ht'

end GlobalTheory.CovolCong

open GlobalTheory.CovolCong in

theorem GlobalTheory.CovolCong.cong_latC_of_cong_latG : ∀ {D : D7} (V : HSp D) (K : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)) (I : Ideal (𝓞 D.host.E)), (∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  intro D V K I h
  let ψ : (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) →+ (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    AddMonoidHom.mk' (fun z => K *ᵥ z - z) (fun x y => by rw [Matrix.mulVec_add]; abel)
  have hle : GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ≤
      (GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E))).comap ψ := by
    unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨c, hc, x, hx, rfl⟩
    exact gen_mem V K I h c hc x hx
  intro z hz
  exact hle hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicScalarBase
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem Q_base (h : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro PP hPP
  refine (h.Q_ram A.μ0 PP).2 (Or.inl hPP) ?_
  rw [h.xi_base]
  intro x _
  rfl

theorem typePart_base (h : R.toLevCh.Is A.μ0) (i : Fin D.R.m) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart R i (sg0 D A) A.μ0 R.triv c =
      (GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift.cuspPart R i c).comap (R.HW i (sg0 D A)).e := by
  classical
  have e : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS R A.μ0 = GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift.finS R := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift.finS
    rw [Q_base R h]
    congr 1
    ext; simp
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift.cuspPart
  rw [e]

theorem exists_factor {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (e : Y →ₗ[ℂ] Z) (f : X →ₗ[ℂ] Z) (V : Submodule ℂ Z) (hinj : Function.Injective e) (hr : LinearMap.range e = V)
    (hm : ∀ x, f x ∈ V) : ∃ th : X →ₗ[ℂ] Y, ∀ x, e (th x) = f x := by
  subst hr
  refine ⟨(LinearEquiv.ofInjective _ hinj).symm.toLinearMap ∘ₗ f.codRestrict _ hm, fun x => ?_⟩
  have := congrArg Subtype.val ((LinearEquiv.ofInjective _ hinj).apply_symm_apply ⟨f x, hm x⟩)
  rwa [LinearEquiv.ofInjective_apply] at this

theorem exists_lift {F : Face D A} (h : R.Char F) (i : Fin D.R.m) (t : T0) :
    ∃ th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H, ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x :=
  exists_factor (R.HW i (sg0 D A)).e (R.thF i t) (R.Wall i (sg0 D A)) (h.models.HW i (sg0 D A)).1
    (h.models.HW i (sg0 D A)).2.1 (h.thP.thF_mem i t)

theorem integrableOn_of_isThetaLift {G' H' S' Sinf TK Tau X : Type} [MeasurableSpace H'] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK]
    [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau] [AddCommGroup X] [Module ℂ X] {ν : Measure H'} {𝓕 : Set H'}
    {th : G' → H' → S' → ℂ} {pt : Sinf → S'} {io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf} {φ : X →ₗ[ℂ] (H' → Tau)}
    {thP : LinearMap.range φ →ₗ[ℂ] TK →ₗ[ℂ] G' → ℂ} (h : Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range φ) thP)
    (x : X) (e : TK) (g : G') :
    IntegrableOn (fun a => th g a (pt (io e (φ x a)))) 𝓕 ν ∧
      thP (φ.rangeRestrict x) e g = Lift.thetaPInt ν 𝓕 th pt io (φ x) e g :=
  ⟨h.integ (φ.rangeRestrict x) e g, h.eq (φ.rangeRestrict x) e g⟩

theorem adjLev_triv {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.adjLev (D := D) R.triv th = LinearMap.adjoint th := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.adjLev
  have : Nat.card (R.triv).H = 1 := Subgroup.card_bot
  rw [this]; simp

end GlobalTheory.BaseScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointIntertwines
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SecLift

section Lin

theorem exists_lift_lin {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (e : Y →ₗ[ℂ] Z) (he : Function.Injective e) (f : X →ₗ[ℂ] Z) (hf : ∀ x, ∃ y, e y = f x) :
    ∃ g : X →ₗ[ℂ] Y, ∀ x, e (g x) = f x := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ f.codRestrict (LinearMap.range e) hf, fun x => ?_⟩
  have := (LinearEquiv.ofInjective e he).apply_symm_apply (f.codRestrict (LinearMap.range e) hf x)
  exact congrArg Subtype.val this

variable {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]

omit [FiniteDimensional ℂ X] in
theorem inner_of_norm (a : X →ₗ[ℂ] X) (ha : ∀ x, ‖a x‖ = ‖x‖) (x x' : X) : ⟪a x, a x'⟫_ℂ = ⟪x, x'⟫_ℂ :=
  (LinearIsometry.mk a ha).inner_map_map x x'

theorem adjoint_intertwines (th : X →ₗ[ℂ] Y) (a : X →ₗ[ℂ] X) (b : Y →ₗ[ℂ] Y) (ha : ∀ x, ‖a x‖ = ‖x‖) (hb : ∀ y, ‖b y‖ = ‖y‖)
    (hc : ∀ x, th (a x) = b (th x)) (y : Y) : LinearMap.adjoint th (b y) = a (LinearMap.adjoint th y) := by
  have hs : Function.Surjective a := LinearMap.injective_iff_surjective.1 (LinearIsometry.mk a ha).injective
  refine ext_inner_right ℂ fun x => ?_
  obtain ⟨x', rfl⟩ := hs x
  rw [LinearMap.adjoint_inner_left, hc, inner_of_norm b hb, inner_of_norm a ha, LinearMap.adjoint_inner_left]

theorem inner_central {G : Type} [Group G] [Fintype G] (ρ : Representation ℂ G Y) (hρ : ∀ g y, ‖ρ g y‖ = ‖y‖) (c : G → ℂ)
    (hc : ∀ g y, (∑ h, c h • ρ h) (ρ g y) = ρ g ((∑ h, c h • ρ h) y)) (y : Y) (hy : (∑ h, c h • ρ h) y = y) (w : Y) :
    ⟪y, (∑ h, c h • ρ h) w⟫_ℂ = ⟪y, w⟫_ℂ := by
  set E : Y →ₗ[ℂ] Y := ∑ h, c h • ρ h with hE
  have hadj : ∀ w, LinearMap.adjoint E w = ∑ h, star (c h) • ρ h⁻¹ w := fun w => by
    refine ext_inner_right ℂ fun x => ?_
    rw [LinearMap.adjoint_inner_left, hE, LinearMap.sum_apply, inner_sum, sum_inner]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [LinearMap.smul_apply, inner_smul_right, inner_smul_left, ← inner_of_norm (ρ h) (hρ h) (ρ h⁻¹ w),
      Representation.self_inv_apply]
    simp
  have hcomm : E (LinearMap.adjoint E y) = LinearMap.adjoint E y := by
    rw [hadj, map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_smul, hc, hy]
  have h0 : LinearMap.adjoint E y - y = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), inner_sub_left, LinearMap.adjoint_inner_left, map_sub, hcomm, hy, sub_self]
  rw [← LinearMap.adjoint_inner_left, sub_eq_zero.1 h0]

end Lin

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

def evL (v : M.Vec) : MMap M →ₗ[ℂ] (GA D V → ℂ) where
  toFun T := T v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem integral_four {X : Type} [MeasurableSpace X] {μ : Measure X} {f1 f2 f3 f4 : X → ℂ} (i1 : Integrable f1 μ)
    (i2 : Integrable f2 μ) (i3 : Integrable f3 μ) (i4 : Integrable f4 μ) (a : ℂ := Complex.I) :
    ∫ g, (f1 g - f2 g - a * f3 g + a * f4 g) ∂μ =
      ∫ g, f1 g ∂μ - ∫ g, f2 g ∂μ - a * ∫ g, f3 g ∂μ + a * ∫ g, f4 g ∂μ := by
  have j1 : Integrable (fun g => f1 g - f2 g) μ := i1.sub i2
  have j2 : Integrable (fun g => f1 g - f2 g - a * f3 g) μ := j1.sub (i3.const_mul a)
  rw [integral_add j2 (i4.const_mul a), integral_sub j1 (i3.const_mul a), integral_sub i1 i2, integral_const_mul,
    integral_const_mul]

theorem inner_eq_integral {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ)
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hip : ∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) (v : M.Vec)
    (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x y : H) :
    IntegrableOn (fun g => star (e x v g) * e y v g) 𝓕 μ ∧ inner ℂ x y = d * ∫ g in 𝓕, star (e x v g) * e y v g ∂μ := by
  have hp : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1 :=
    Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hv τ]; simp
  have diag : ∀ x, IntegrableOn (fun g => star (e x v g) * e x v g) 𝓕 μ ∧
      inner ℂ x x = d * ∫ g in 𝓕, star (e x v g) * e x v g ∂μ := fun x => by
    by_cases hx : x = 0
    · subst hx; simp
    have hc : ∃ c, IsMultIP M μ 𝓕 (e x) (e x) c := by
      by_contra hc
      apply hx
      rw [← inner_self_eq_zero (𝕜 := ℂ), hip, ipM, dif_neg hc, mul_zero]
    have := ipM_spec M μ 𝓕 _ _ hc v v
    rw [hp, mul_one] at this
    exact ⟨this.1, by rw [hip, this.2]⟩
  have key : (fun g => star (e x v g) * e y v g) = fun g => (1 / 4 : ℂ) *
      (star (e (x + y) v g) * e (x + y) v g - star (e (x - y) v g) * e (x - y) v g -
        Complex.I * (star (e (x + Complex.I • y) v g) * e (x + Complex.I • y) v g) +
        Complex.I * (star (e (x - Complex.I • y) v g) * e (x - Complex.I • y) v g)) := by
    funext g
    simp only [map_add, map_sub, map_smul, _root_.add_apply, _root_.sub_apply, _root_.smul_apply,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub, star_mul', Complex.star_def, Complex.conj_I]
    linear_combination (-(1/2 : ℂ) * ((starRingEnd ℂ) (e y v g) * e x v g - (starRingEnd ℂ) (e x v g) * e y v g)) * Complex.I_mul_I
  obtain ⟨i1, e1⟩ := diag (x + y)
  obtain ⟨i2, e2⟩ := diag (x - y)
  obtain ⟨i3, e3⟩ := diag (x + Complex.I • y)
  obtain ⟨i4, e4⟩ := diag (x - Complex.I • y)
  rw [key]
  refine ⟨(((i1.sub i2).sub (i3.const_mul _)).add (i4.const_mul _)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_four i1 i2 i3 i4]
  generalize (∫ g in 𝓕, star (e (x + y) v g) * e (x + y) v g ∂μ) = a1 at e1
  generalize (∫ g in 𝓕, star (e (x - y) v g) * e (x - y) v g ∂μ) = a2 at e2
  generalize (∫ g in 𝓕, star (e (x + Complex.I • y) v g) * e (x + Complex.I • y) v g ∂μ) = a3 at e3
  generalize (∫ g in 𝓕, star (e (x - Complex.I • y) v g) * e (x - Complex.I • y) v g ∂μ) = a4 at e4
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I] at e1 e2 e3 e4
  linear_combination (1 / 4 : ℂ) * (e1 - e2 - Complex.I * e3 + Complex.I * e4) +
    ((1/2 : ℂ) * (inner ℂ x y - inner ℂ y x)) * Complex.I_mul_I

end Model

section Act

open Formalism.IndefR.Lev

theorem actL_apply {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} {g0 : G0 L.Pg L.r}
    (hk : ∃ κ, IsLevelLift V β L g0 κ) (Φ : GA D V → ℂ) (h : GA D V) :
    Links.actL V β L g0 Φ h = (levChi V β (flagL L) hk.choose)⁻¹ * Φ (h * hk.choose) := by
  show actG0 V β L g0 Φ h = _
  rw [actG0, dif_pos hk]

theorem span_of_pres {G Γ W K H : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
    [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] (G → W))
    (hinj : Function.Injective e) (hr : LinearMap.range e = Bridge.AdForms ι ρ J χ) (j : S.Forms → H)
    (hj : ∀ x, e (j x) = P.extL x) (N : Submodule ℂ H) (hN : ∀ x, j x ∈ N) (y : H) : y ∈ N := by
  have h1 : e y ∈ N.map e := by
    have h2 : e y ∈ Submodule.span ℂ (Set.range P.extL) := by
      rw [GlobalTheory.PresBasic.ext_span]
      exact hr.le (LinearMap.mem_range_self _ y)
    refine Submodule.span_le.2 ?_ h2
    rintro _ ⟨x₀, rfl⟩
    exact ⟨j x₀, hN x₀, hj x₀⟩
  obtain ⟨y', hy', h⟩ := h1
  exact hinj h ▸ hy'

theorem coord_translate {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {κ : GA D V} (hκ : κ ∈ GfC V) (a : ℂ)
    {f f' : Bridge.Gf V → c.W} (hf : ∀ h, f' h = a • f (h * (finHom V).rangeRestrict κ)) (ℓ : c.W →ₗ[ℂ] ℂ) (h : GA D V) :
    ℓ (c.ext f' h) = a * ℓ (c.ext f (h * κ)) := by
  have h1 : c.ext f' h = c.ρ h⁻¹ (f' ((finHom V).rangeRestrict h)) := rfl
  have h2 : c.ext f (h * κ) = c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ))) := rfl
  have h3 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ :=
    (congrArg c.ρ (mul_inv_rev h κ)).trans ((c.ρ.map_mul κ⁻¹ h⁻¹).trans
      ((congrArg (· * c.ρ h⁻¹) (hc.1 κ⁻¹ ((GfC V).inv_mem hκ))).trans (one_mul _)))
  have h4 := MonoidHom.map_mul (finHom V).rangeRestrict h κ
  have h5 : f' ((finHom V).rangeRestrict h) = a • f ((finHom V).rangeRestrict (h * κ)) :=
    (hf _).trans (congrArg (fun q => a • f q) h4.symm)
  rw [h1, h2, h3, h5]
  exact (congrArg ℓ ((c.ρ h⁻¹).map_smul a _)).trans (ℓ.map_smul a _)

theorem exists_translate {Γ W H : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup H] [Module ℂ H]
    (e : H →ₗ[ℂ] (Γ → W)) (he : Function.Injective e) (a : ℂ) (k : Γ)
    (hu : ∀ y, ∃ y', (∀ h, e y' h = a • e y (h * k)) ∧ ‖y'‖ = ‖y‖) :
    ∃ b : H →ₗ[ℂ] H, (∀ y h, e (b y) h = a • e y (h * k)) ∧ ∀ y, ‖b y‖ = ‖y‖ := by
  obtain ⟨b, hb⟩ := exists_lift_lin e he (a • LinearMap.funLeft ℂ W (fun h => h * k) ∘ₗ e)
    fun y => (hu y).imp fun y' h => funext h.1
  have hb' : ∀ y h, e (b y) h = a • e y (h * k) := fun y h => congrFun (hb y) h
  refine ⟨b, hb', fun y => ?_⟩
  obtain ⟨y', h1, h2⟩ := hu y
  rw [← h2, he (funext fun h => (hb' y h).trans (h1 h).symm)]

end Act

end GlobalTheory.SecLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnFibFrEqOfExLeftEq
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.FrameEquiv.anFib_fr_eq_of_ex_left_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → (∀ z, (A'.ex z).left = (A.ex z).left) → ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z = A.fr j z := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y y' A A' hs hx hL he j z hj
  have hch : ∀ z, ∃ i, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U i := fun z => by
    have h : (A.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, Xo.univ.t.PP.L.U i := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi⟩
  choose ch hc using hch
  have hyx : y'.x = y.x := by
    have h1 : (A.ex 0).left ≫ Xo.univ.t.G.hom = y.x := Over.w (A.ex 0)
    have h2 : (A'.ex 0).left ≫ Xo.univ.t.G.hom = y'.x := Over.w (A'.ex 0)
    rw [← h1, ← h2, he]
  have ne' : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z ≠ 0 :=
    fun j z h => A'.fr_ne j z (by rw [he]; exact h)
  let q : (Fin g → ℂ) → ℂ := fun z => A.fr (ch z) z / A'.fr (ch z) z
  have key : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → q z = A.fr j z / A'.fr j z := fun j z h => by
    have hz : ⊤ ≤ (A.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U (ch z)) := fun p hp => ⟨h hp, hc z hp⟩
    have h1 := A.fr_g j (ch z) z hz
    have h2 := A'.fr_g j (ch z) z (by rw [he]; exact hz)
    rw [he] at h2
    rw [h1, h2, mul_div_mul_left _ _ (left_ne_zero_of_mul (h1 ▸ A.fr_ne j z h))]
  have hq : Differentiable ℂ q := fun z0 => by
    have hO : IsOpen {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} := by
      simpa using (A.hol (Xo.univ.t.PP.L.U (ch z0)) 0).1
    have h' : DifferentiableOn ℂ (A'.fr (ch z0)) {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} := by
      simpa only [he] using A'.fr_hol (ch z0)
    have hd : DifferentiableOn ℂ q {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} :=
      ((A.fr_hol (ch z0)).mul (h'.inv fun z hz => ne' _ z hz)).congr fun z hz =>
        (key _ z hz).trans (div_eq_mul_inv _ _)
    exact hd.differentiableAt (hO.mem_nhds (hc z0))
  let pvh : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' (pv X idx x) GlobalTheory.Dict.FrameSign.pv_add
  let P : L →+ (Fin g → ℂ) := pvh.comp L.subtype.toAddMonoidHom
  have hP : Submodule.span ℝ (Set.range P) = ⊤ := by
    rw [← span_image_pv idx hs hx L (TensLat.span_of_selfD X hL)]
    congr 1
    ext w
    exact ⟨fun ⟨a, ha⟩ => ⟨a.1, a.2, ha⟩, fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩⟩
  have hper : ∀ z (a : L), ‖q (z + P a)‖ = ‖q z‖ := fun z a => by
    have h : ⊤ ≤ (A.ex (z + pv X idx x a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z) := by
      rw [GlobalTheory.Dict.FrameSign.ex_add_pv A z a.2]; exact hc z
    have h1 := A.fr_per a a.2 (ch z) z (hc z)
    have h2 := A'.fr_per a a.2 (ch z) z (by rw [he]; exact hc z)
    change ‖q (z + pv X idx x a)‖ = _
    rw [key _ _ h, key _ _ (hc z), h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
      A.χ_norm _ a.2, A'.χ_norm _ a.2,
      mul_div_mul_left _ _ (mul_ne_zero one_ne_zero (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)))]
  have hc0 := ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const_range P hP q hq hper z 0
  have h0 : q 0 = 1 := by
    have := A'.fr_0 (ch 0) (by rw [he]; exact hc 0)
    rw [hyx, ← A.fr_0 (ch 0) (hc 0)] at this
    change A.fr (ch 0) 0 / A'.fr (ch 0) 0 = 1
    rw [this, div_self (A.fr_ne _ _ (hc 0))]
  rw [h0, key j z hj] at hc0
  exact ((div_eq_one_iff_eq (ne' j z hj)).1 hc0).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixSmoothingModerateGrowthStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanMatrixSmoothing_moderateGrowth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → IsModGrowthInf (smoothMatInf α W) := by
  first | (exact @GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth) | (exact GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth) | (intros; apply GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanRapidKernelOperatorCompRapidFamilyStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanRapidKernelOperator_comp_rapidFamily : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ), IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η → ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ), (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) → (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) → IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := by
  first | (exact @GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf) | (exact GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf) | (intros; apply GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTuplePinsOrientationStandardFrameLevelMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BasePins

theorem orient_std_lev : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) , R.toLevCh.Is A.μ0 → LawsJ T → ∀ i, OMPins T R κ v₀ O i → T.pb = R.C.P.pb ∧ VStd D i ∧ LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) (O i).lev := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hL hT i hO
  exact ⟨GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hT.toLawsM hL (hO.2.tuple ()).half, hO.2.lift.std, hO.2.lift.lev⟩

end GlobalTheory.BasePins
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_lbPow_sq_pull_sq2_of_isGen_of_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, LBIso (GlobalTheory.UPel.HT.Hecke.lbPow P (n ^ 2)) (P.pull (GlobalTheory.UPel.HT.Hecke.sq2 ((𝟙 A) ^ n))) := by
  first | (exact @GlobalTheory.BirigidPow.birigidified_pullback_mulPair_iso_tensorPowSq) | (exact GlobalTheory.BirigidPow.birigidified_pullback_mulPair_iso_tensorPowSq) | (intros; apply GlobalTheory.BirigidPow.birigidified_pullback_mulPair_iso_tensorPowSq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentMapContinuousMulDetOneCompactSuppoStatement
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockUnipotentMap_continuous_mul_det_one_compactSupport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → k) → GL (Fin N) k), (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) → Continuous u ∧ (∀ X Y, u (X + Y) = u X * u Y) ∧ (∀ X, (u X : Matrix (Fin N) (Fin N) k).det = 1) ∧ ∀ f : GL (Fin N) k → ℂ, HasCompactSupport f → ∀ g h : GL (Fin N) k, HasCompactSupport (fun X => f (g * (h⁻¹ * u X * h))) := by
  first | exact @GlobalTheory.blockUnipotent_props | exact GlobalTheory.blockUnipotent_props | (intros; apply GlobalTheory.blockUnipotent_props <;> assumption)
end

