import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1452
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsRhoOfAtInf
section
open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

namespace GlobalTheory.ArchUniq

noncomputable def evIHom (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem evI_eq_evIHom {F : Type} [Field F] [NumberField F] (a : AF F) : evI F a = evIHom F a := rfl

theorem trace_evI_heis {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] {κ : Type} [Fintype κ]
    (x a b : κ → AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ b + ⅟(2 : AF F) * a ⬝ᵥ b)) =
      trP F κ (locV x) (locV b) + trP F κ (locV a) (locV b) / 2 := by
  have hdot : ∀ y : κ → AF F, evIHom F (y ⬝ᵥ b) = ∑ i, locV y i * locV b i := by
    intro y
    simp only [dotProduct, map_sum, map_mul, locV, evI_eq_evIHom]
  have h2 : ∀ t : AF F, evIHom F (⅟(2 : AF F) * t) = (1 / 2 : ℝ) • evIHom F t := by
    intro t
    have h : (2 : ℝ) • evIHom F (⅟(2 : AF F) * t) = evIHom F t := by
      rw [two_smul, ← map_add, ← two_mul, ← mul_assoc, mul_invOf_self, one_mul]
    rw [← h, smul_smul]
    norm_num
  rw [evI_eq_evIHom, map_add, h2, hdot, hdot, map_add, map_smul, trP, trP, smul_eq_mul]
  ring

theorem acts_rho_of_at_inf : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {W' : Type} [AddCommGroup W'] [Module (AF F) W'] {Bf : W' → W' → AF F} {κ : Type} [Fintype κ]
      (dc : Darboux Bf κ) (w : W'), At (evI F) w → ∀ f f₁ : SInf F κ,
      ⇑f₁ = schrF (trP F κ) (locV (dc.e w).1, locV (dc.e w).2) ⇑f → Acts (evI F) (dc.rho ψ w) ⇑f ⇑f₁ := by
  intro F _ _ ψ hψ W' _ _ Bf κ _ dc w hw f f₁ hf r hr
  have hab : ∀ u : AF F, evI F u = 0 → u • dc.e w = 0 := fun u hu => by
    rw [← map_smul, hw u hu, map_zero]
  have ha : At (evI F) (dc.e w).1 := fun u hu => congrArg Prod.fst (hab u hu)
  have hb : At (evI F) (dc.e w).2 := fun u hu => congrArg Prod.snd (hab u hu)
  funext x
  have ht : At (evI F) (x ⬝ᵥ (dc.e w).2 + ⅟(2 : AF F) * (dc.e w).1 ⬝ᵥ (dc.e w).2) := fun u hu => by
    have h : ∀ y : κ → AF F, u * (y ⬝ᵥ (dc.e w).2) = 0 := fun y => by
      rw [← smul_eq_mul, ← dotProduct_smul, hb u hu, dotProduct_zero]
    rw [smul_eq_mul, mul_add, h, mul_left_comm, h, mul_zero, add_zero]
  have hloc : (fun i => evI F ((x + (dc.e w).1) i)) = locV x + locV (dc.e w).1 := by
    funext i
    simp only [Pi.add_apply, locV, evI_eq_evIHom, map_add]
  simp only [Darboux.rho, schr, tens]
  rw [hψ.2.2 _ ht, trace_evI_heis, hr.1 x _ ha, hf, hloc, schrF]
  exact (mul_assoc _ _ _).symm

end GlobalTheory.ArchUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneModelRestrictionCompatible
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0

noncomputable section

namespace GlobalTheory.ThK.EvAt0.Coef

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_swap {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (hs : ∀ i j, σ (J j i) = -J i j)
    (hσ : ∀ x, σ (σ x) = x) (a b : Fin d → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hs, Finset.mul_sum, Finset.sum_neg_distrib,
    neg_mul, mul_neg, neg_neg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.ThK.EvAt0.Coef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactFundamentalSet
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
namespace GlobalTheory.AdeleCocompactExt

theorem exists_compact_adeleE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ K : Set (AE F E), IsCompact K ∧ ∀ a : AE F E, ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  intro F E _ _ _ _ _
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K₀, hK₀, hK⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hφ : Continuous B.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap
  refine ⟨B.equivFun.symm '' Set.pi Set.univ (fun _ => K₀),
    (isCompact_univ_pi fun _ => hK₀).image hφ, ?_⟩
  intro a
  choose x hx using fun k => hK (B.equivFun a k)
  refine ⟨∑ k, x k • b k, fun k => B.equivFun a k - algebraMap F (AF F) (x k), fun k _ => hx k, ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  funext k
  have h1 : B.equivFun (inclR (F := F) (AF F) (∑ k, x k • b k)) k = algebraMap F (AF F) (x k) := by
    rw [Module.Basis.equivFun_apply]
    show (B.repr ((1 : AF F) ⊗ₜ[F] (∑ k, x k • b k))) k = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp [b, Module.Basis.repr_sum_self]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Finsupp.single_apply, hj]) (by simp)]
    simp
  simp only [map_sub, Pi.sub_apply, h1]

end GlobalTheory.AdeleCocompactExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixSchwartzMajorantInvMulLeStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixSchwartzMajorant_inv_mul_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) ≤ C * GlobalTheory.Unf.maj θ K' N x := by
  first | exact @GlobalTheory.MajMul.maj_mul_le | exact GlobalTheory.MajMul.maj_mul_le | (intros; apply GlobalTheory.MajMul.maj_mul_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section
open scoped Classical

namespace GlobalTheory.ConjSch

def conjSchwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := starRingEnd ℂ (f x)
  smooth' := Complex.conjCLE.contDiff.comp f.smooth'
  decay' k n := by
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => starRingEnd ℂ (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := by
      funext y; simp
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem conjSchwartz_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSchwartz f x = starRingEnd ℂ (f x) := rfl

theorem conj_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => starRingEnd ℂ (Φ x)) ∈ schA F κ := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, g, hg, rfl⟩ := hΨ
    apply Submodule.subset_span
    refine ⟨conjSchwartz f, fun y => starRingEnd ℂ (g y), ⟨hg.1.comp _, hg.2.comp_left (map_zero _)⟩, ?_⟩
    funext x
    simp [pureA, conjSchwartz_apply, map_mul]
  | zero =>
    convert (schA F κ).zero_mem using 1
    funext x; simp
  | add Ψ₁ Ψ₂ _ _ h₁ h₂ =>
    have := (schA F κ).add_mem h₁ h₂
    convert this using 1
    funext x; simp
  | smul c Ψ _ h =>
    have := (schA F κ).smul_mem (starRingEnd ℂ c) h
    convert this using 1
    funext x; simp

end GlobalTheory.ConjSch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScaleStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicThetaSum_norm_le_polynomial_scale : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k := by
  first | exact @GlobalTheory.LatScaleSum.thetaSum_norm_le_pow | exact GlobalTheory.LatScaleSum.thetaSum_norm_le_pow | (intros; apply GlobalTheory.LatScaleSum.thetaSum_norm_le_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSmul
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.ArchDecay

section Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def heisD (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f : (Fin n × Fin d → AF F) → ℂ) (x : Fin n × Fin d → AF F) : ℂ :=
  deriv (fun t : ℝ => M.heisLine ψ u t f x) 0

def liftI (M : Model σ X W)
    (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    Matrix (Fin n) (Fin d) (AE F E) :=
  M.co.e.symm (fun i => infAd F (ζ.1 i), fun i => infAd F (ζ.2 i))

def movI (M : Model σ X W) (p : UA σ X.J × UA σ W.J)
    (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  (arch F (M.co.e (actAB (cA σ) p⁻¹ (liftI M ζ))).1, arch F (M.co.e (actAB (cA σ) p⁻¹ (liftI M ζ))).2)

def wordH (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (zs : List ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)))
    (f : (Fin n × Fin d → AF F) → ℂ) : (Fin n × Fin d → AF F) → ℂ :=
  zs.foldr (fun ζ g => heisD M ψ (liftI M ζ) g) f

end Model

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def dR (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ)
    (ζ : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (f : (κ → AF F) → ℂ) :
    (κ → AF F) → ℂ :=
  dD F ζ.1 f + c • mM F (T ζ.2) f

def wordR (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ)
    (zs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) (f : (κ → AF F) → ℂ) :
    (κ → AF F) → ℂ :=
  zs.foldr (dR F T c) f

theorem dD_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F)
    (c : ℂ) (f : (κ → AF F) → ℂ) : dD F v (c • f) = c • dD F v f := by
  funext x
  simp only [dD, Pi.smul_apply, smul_eq_mul]
  rw [deriv_const_mul_field']

theorem mM_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (c : ℂ) (f : (κ → AF F) → ℂ) : mM F l (c • f) = c • mM F l f := by
  funext x
  simp only [mM, Pi.smul_apply, smul_eq_mul]
  ring

theorem app_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (o : Op F κ) (c : ℂ)
    (f : (κ → AF F) → ℂ) : app F o (c • f) = c • app F o f := by
  cases o with
  | inl v => exact dD_smul v c f
  | inr l => exact mM_smul l c f

theorem dD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : (κ → AF F) → ℂ) :
    dD F 0 f = 0 := by
  funext x
  have e : ∀ t : ℝ, (x + fun i => infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i)) = x := by
    intro t
    funext i
    have h0 : infAd F (0 : mixedEmbedding.mixedSpace F) = 0 := by unfold infAd; rw [map_zero, map_zero]; rfl
    show x i + infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i) = x i
    rw [Pi.zero_apply, smul_zero, h0, add_zero]
  show deriv (fun t : ℝ => f (x + fun i => infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i))) 0 = 0
  rw [show (fun t : ℝ => f (x + fun i => infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i))) = fun _ => f x from
    funext fun t => by rw [e t]]
  exact deriv_const 0 (f x)

theorem mM_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : (κ → AF F) → ℂ) :
    mM F 0 f = 0 := by
  funext x
  simp [mM]

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
section
open NumberField GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaDecay

def archAt (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) : AF F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding w).comp (evInf F w).toRingHom

def coB (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) :=
  Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)

end GlobalTheory.ThetaDecay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartz
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay LineDeriv

namespace GlobalTheory.ArchDecay.SchAStab

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem pureA_line (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) (t : ℝ) :
    pureA F f g (x + fun i => infAd F (t • v i)) = f (arch F x + t • v) * g (fun i => (x i).2) := by
  unfold pureA
  congr 2
  · funext i
    change InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((x i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • v i)) = evI F (x i) + t • v i
    rw [map_add, RingEquiv.apply_symm_apply]
    rfl
  · funext i
    exact add_zero (x i).2

theorem hasDerivAt_line (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) :
    HasDerivAt (fun t : ℝ => pureA F f g (x + fun i => infAd F (t • v i)))
      (fderiv ℝ f (arch F x) v * g (fun i => (x i).2)) 0 := by
  simp only [pureA_line]
  have h1 : HasDerivAt (fun t : ℝ => arch F x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (arch F x)
  have h2 : HasDerivAt (fun t : ℝ => f (arch F x + t • v)) (fderiv ℝ f (arch F x) v) 0 :=
    (f.differentiableAt (x := arch F x)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
  exact h2.mul_const _

theorem dD_pureA (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (v : κ → mixedEmbedding.mixedSpace F) : dD F v (pureA F f g) = pureA F (∂_{v} f : SchwartzMap _ ℂ) g := by
  funext x
  rw [dD, (hasDerivAt_line F f g x v).deriv]
  show _ = (∂_{v} f : SchwartzMap _ ℂ) (arch F x) * _
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]

def mulL (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (⇑l) f

theorem mulL_apply (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (y : κ → mixedEmbedding.mixedSpace F) :
    mulL F l f y = (l y : ℂ) * f y := by
  rw [mulL, SchwartzMap.smulLeftCLM_apply_apply l.hasTemperateGrowth, Complex.real_smul]

theorem mM_pureA (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) : mM F l (pureA F f g) = pureA F (mulL F l f) g := by
  funext x
  simp only [mM, pureA, mulL_apply, mul_assoc]
  rfl

theorem mem_schA_mM (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    mM F l Φ ∈ schA F κ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    rw [mM_pureA]
    exact Submodule.subset_span ⟨mulL F l f, g, hg, rfl⟩
  | zero =>
    have : mM F l (0 : (κ → AF F) → ℂ) = 0 := by funext x; simp [mM]
    rw [this]; exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    have : mM F l (Φ + Ψ) = mM F l Φ + mM F l Ψ := by funext x; simp [mM, mul_add]
    rw [this]; exact Submodule.add_mem _ h1 h2
  | smul a Φ _ h =>
    have : mM F l (a • Φ) = a • mM F l Φ := by funext x; simp [mM]; ring
    rw [this]; exact Submodule.smul_mem _ a h

theorem archimedeanDirectionalDerivative_mem_adelicSchwartz (v : κ → mixedEmbedding.mixedSpace F) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (∀ x : κ → AF F, DifferentiableAt ℝ (fun t : ℝ => Φ (x + fun i => infAd F (t • v i))) 0) ∧
      dD F v Φ ∈ schA F κ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨fun x => (hasDerivAt_line F f g x v).differentiableAt, ?_⟩
    rw [dD_pureA]
    exact Submodule.subset_span ⟨_, g, hg, rfl⟩
  | zero =>
    refine ⟨fun x => differentiableAt_const _, ?_⟩
    have : dD F v (0 : (κ → AF F) → ℂ) = 0 := by funext x; simp [dD]
    rw [this]; exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    refine ⟨fun x => (h1.1 x).add (h2.1 x), ?_⟩
    have : dD F v (Φ + Ψ) = dD F v Φ + dD F v Ψ := by
      funext x
      simp only [dD, Pi.add_apply]
      exact deriv_add (h1.1 x) (h2.1 x)
    rw [this]; exact Submodule.add_mem _ h1.2 h2.2
  | smul a Φ _ h =>
    refine ⟨fun x => (h.1 x).const_mul a, ?_⟩
    have : dD F v (a • Φ) = a • dD F v Φ := by
      funext x
      simp only [dD, Pi.smul_apply, smul_eq_mul]
      exact deriv_const_mul a (h.1 x)
    rw [this]; exact Submodule.smul_mem _ a h.2

theorem app_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (o : Op F κ),
    ∀ f ∈ schA F κ, app F o f ∈ schA F κ := by
  intro F _ _ κ _ o f hf
  rcases o with v | l
  · exact (archimedeanDirectionalDerivative_mem_adelicSchwartz F v hf).2
  · exact mem_schA_mM F l hf

end GlobalTheory.ArchDecay.SchAStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanWeilOperatorTransportsHeisenbergLineDStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanWeilOperator_transports_heisenbergLineDerivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ →
      ActsD (evI F) (M.heisLine B.ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
  first | exact @GlobalTheory.HeisTransport.actsD_heisLine_transport | exact GlobalTheory.HeisTransport.actsD_heisLine_transport | (intros; apply GlobalTheory.HeisTransport.actsD_heisLine_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelRankDegreeShareLe
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem share_le_of_rankLow (h : RankLow) (F : Type) [Field F] [NumberField F] (X : Data F)
    (hn : IsNef F X.LA) (hb : IsBig F X.LA) : (X.R : ℤ) * X.del ≤ X.d := by
  refine (h F X.toGeo hn hb X.T).trans ?_
  rw [X.d_eq_finrank]
  exact_mod_cast Submodule.finrank_mono (X.global_le X.T le_rfl)

theorem share_le : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F),
    IsNef F X.LA → IsBig F X.LA → (X.R : ℤ) * X.del ≤ X.d :=
  fun q => share_le_of_rankLow (GlobalTheory.T.globalSectionRankLowerBound_of_hilbertSamuel q)

end GlobalTheory.HSCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelGoodFormsDimsAgreePartwiseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLevel_goodForms_dims_agree_partwise : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → R.toRealDat.LUnif → (R.toCx3 F).DimParts false := by
  first | exact @GlobalTheory.DimPartsFull.dimParts | exact GlobalTheory.DimPartsFull.dimParts | (intros; apply GlobalTheory.DimPartsFull.dimParts <;> assumption)
end

