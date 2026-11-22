import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1454
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfSkewUnipotentMemDoubledLatticeStabilizerStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Z : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Z →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 →
    ∃ u ∈ GlobalTheory.DblVac.KD σ W v, u ∈ GlobalTheory.DblVac.PDiag σ W ∧
      GlobalTheory.DblVac.matD u = 1 + (⅟(2 : AF F)) • ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * Z * (GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ) := by
  first | exact @GlobalTheory.DblVacUnip.unip_mem | exact GlobalTheory.DblVacUnip.unip_mem | (intros; apply GlobalTheory.DblVacUnip.unip_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCentreLawZero
section
noncomputable section

namespace GlobalTheory.ThK.DescB.PlaneTwo

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n₁ n₂ : ℕ}

def xTwo (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) : Fin n → E := H₁.ι *ᵥ H₂.x

def yTwo (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) : Fin n → E := H₁.ι *ᵥ H₂.y

def ιTwo (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) : Matrix (Fin n) (Fin n₂) E := H₁.ι * H₂.ι

variable (σ) in

def unipTwo (Y : Spc F E n) (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) : Subgroup (UA σ Y.J) :=
  Subgroup.closure {u | mat u *ᵥ incV F H₁.x = incV F H₁.x ∧ mat u *ᵥ incV F (xTwo H₁ H₂) = incV F (xTwo H₁ H₂) ∧
    ∀ z, ∃ a b : AE F E, mat u *ᵥ (incM F (ιTwo H₁ H₂) *ᵥ z) =
      incM F (ιTwo H₁ H₂) *ᵥ z + a • incV F H₁.x + b • incV F (xTwo H₁ H₂)}

def IsCTTwo {Y : Spc F E n} (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) (f c : UA σ Y.J → ℂ) : Prop :=
  ∀ (μ : Measure (unipTwo σ Y H₁ H₂)) (𝓕 : Set (unipTwo σ Y H₁ H₂)), μ.IsHaarMeasure →
    IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unipTwo σ Y H₁ H₂)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ h, c h = ∫ u in 𝓕, f (u.1 * h) ∂μ

def IsCentreTwo {Y : Spc F E n} (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) (t : (AE F E)ˣ) (h : UA σ Y.J) : Prop :=
  mat h *ᵥ incV F H₁.x = t.1 • incV F H₁.x ∧ mat h *ᵥ incV F (xTwo H₁ H₂) = t.1 • incV F (xTwo H₁ H₂) ∧
    mat h *ᵥ incV F H₁.y = cA σ (t⁻¹).1 • incV F H₁.y ∧
    mat h *ᵥ incV F (yTwo H₁ H₂) = cA σ (t⁻¹).1 • incV F (yTwo H₁ H₂) ∧
    mat h * incM F (ιTwo H₁ H₂) = incM F (ιTwo H₁ H₂)

def HasCentreLaw {Y : Spc F E n} (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) (χ χ' : Chr F E) (w : ℝ) (T : UA σ Y.J → ℂ) :
    Prop :=
  ∀ t m, IsCentreTwo H₁ H₂ t m → ∀ h, T (m * h) = (χ t : ℂ) * (χ' t : ℂ) * (((absE F E t : ℝ) ^ w : ℝ) : ℂ) * T h

end GlobalTheory.ThK.DescB.PlaneTwo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGlobalOneFormFrameOfSmoothGroupScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem hasFrame_of_smooth_grpObj : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    Smooth A.hom → HasFrame (OAff A.hom) := by
  intro R _ A _ hs
  obtain ⟨W, i1, i2, hfin, hproj, ⟨t⟩⟩ := GlobalTheory.T.exists_tangentRepresentation_smooth_groupScheme R A hs
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_global_oneForms_isBaseChange_tangentRep R A W t
  exact GlobalTheory.AbCoh.hasFrame_of_isBaseChange R _ (OAff A.hom) W j hj

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMulLeOfIsCompactStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_height_mul_le_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ B : ℝ, 1 ≤ B ∧ ∀ c ∈ Ω, ∀ y : GL (Fin a) (Cinf E), height (y * c) ≤ B * height y := by
  first | exact @GlobalTheory.AutGrowth.height_mul_le_of_isCompact | exact GlobalTheory.AutGrowth.height_mul_le_of_isCompact | (intros; apply GlobalTheory.AutGrowth.height_mul_le_of_isCompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativePreservesSchwartz
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay.DHMem

open GlobalTheory.HeisDeriv
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem hasDerivAt_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) :
    HasDerivAt (fun t : ℝ => schr ψ (realAd F t • w) (pureA F f g) x)
      (pureA F (heisD F (fun i => evI F (w.1 i)) w.2 f) g x) 0 := by
  set v : κ → mixedEmbedding.mixedSpace F := fun i => evI F (w.1 i) with hv
  set z : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hz
  set P : ℝ := trForm F w.2 z with hP
  set Q : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) with hQ
  have hline : ∀ t : ℝ, schr ψ (realAd F t • w) (pureA F f g) x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (P + t * Q) : ℝ) : ℂ)) *
        (f (z + t • v) * g (fun i => (x i).2)) := by
    intro t
    simp only [schr, Prod.smul_fst, Prod.smul_snd]
    set A : AF F := x ⬝ᵥ (realAd F t • w.2) + ⅟(2 : AF F) * ((realAd F t • w.1) ⬝ᵥ (realAd F t • w.2)) with hAdef
    have hA : A = realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
      simp only [hAdef, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hAt2 : At (evI F) A := fun a ha => by
      rw [hA, smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero ha, zero_mul]
    have hxy : evI F (x ⬝ᵥ w.2) = ∑ i, z i * evI F (w.2 i) := by
      simp only [dotProduct, evI_sum, evI_mul, hz]
    have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) = t * (P + t * Q) := by
      rw [hA, evI_mul, evI_add, evI_mul, evI_realAd, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_add,
        map_smul, hxy, hP, trForm_apply, hQ, smul_eq_mul, smul_eq_mul]
    have harg : (fun i => evI F ((x + realAd F t • w.1) i)) = z + t • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_realAd, hz, hv]
      rw [Algebra.smul_def]
    have hfin : (fun i => ((x + realAd F t • w.1) i).2) = fun i => (x i).2 := by
      funext i
      show (x i).2 + (realAd F t).2 * (w.1 i).2 = (x i).2
      rw [show (realAd F t).2 = 0 from rfl, zero_mul, add_zero]
    rw [hψ.2.2 A hAt2, htr]
    show _ * (f (fun i => evI F ((x + realAd F t • w.1) i)) * g (fun i => ((x + realAd F t • w.1) i).2)) = _
    rw [harg, hfin]
  have h1 : HasDerivAt (fun t : ℝ => t * (P + t * Q)) P 0 := by
    have := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).mul_const Q))
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h4 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) 0 := by
    have := (f.hasFDerivAt (z + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul (h4.mul_const (g (fun i => (x i).2)))
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => hline t)
  show _ = heisD F v w.2 f z * g (fun i => (x i).2)
  simp only [heisD_apply, mult_apply, ← hP]
  simp
  ring

theorem exists_hasDerivAt (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) :
    ∃ Φ' ∈ schA F κ, ∀ x, HasDerivAt (fun t : ℝ => schr ψ (realAd F t • w) Φ x) (Φ' x) 0 := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact ⟨pureA F (heisD F (fun i => evI F (w.1 i)) w.2 f) g, Submodule.subset_span ⟨_, g, hg, rfl⟩,
      fun x => hasDerivAt_pureA ψ hψ w f g x⟩
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_⟩
    refine (hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq (.of_forall fun t => ?_)
    simp only [schr, Pi.zero_apply, mul_zero]
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    obtain ⟨Φ₁', m₁, d₁⟩ := h₁
    obtain ⟨Φ₂', m₂, d₂⟩ := h₂
    refine ⟨Φ₁' + Φ₂', add_mem m₁ m₂, fun x => ?_⟩
    refine ((d₁ x).add (d₂ x)).congr_of_eventuallyEq (.of_forall fun t => ?_)
    simp only [schr, Pi.add_apply, mul_add]
  | smul a Φ _ h =>
    obtain ⟨Φ', m, d⟩ := h
    refine ⟨a • Φ', Submodule.smul_mem _ a m, fun x => ?_⟩
    refine ((d x).const_mul a).congr_of_eventuallyEq (.of_forall fun t => ?_)
    simp only [schr, Pi.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.ThetaDecay.DHMem

open GlobalTheory.ThetaDecay.DHMem in

theorem GlobalTheory.ThetaDecay.dH_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ w : (κ → AF F) × (κ → AF F), IsArch w → ∀ Φ ∈ schA F κ, dH ψ w Φ ∈ schA F κ := by
  intro F _ _ κ _ ψ hψ w _ Φ hΦ
  obtain ⟨Φ', hΦ', hd⟩ := exists_hasDerivAt ψ hψ w Φ hΦ
  have : dH ψ w Φ = Φ' := funext fun x => (hd x).deriv
  rw [this]
  exact hΦ'

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergMatrixMul
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section
namespace GlobalTheory.UnipMass
namespace ProdFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_cA_of_invol (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cA_incM_apply (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    cA σ (incM F J i j) = incM F (J.map σ) i j := by
  simp [cA, incM, inclR]

theorem hA_swap (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → AE F E) : hA σ J w v = - cA σ (hA σ J v w) := by
  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_cA_of_invol σ hσ, cA_incM_apply]
  simp only [incM, Matrix.map_apply, hJ, map_neg]
  simp only [Finset.mul_sum, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hA_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    hA σ J (v + v') w = hA σ J v w + hA σ J v' w := by
  simp only [hA, add_dotProduct]

theorem hA_sub_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    hA σ J (v - v') w = hA σ J v w - hA σ J v' w := by
  simp only [hA, sub_dotProduct]

theorem hA_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (v w : Fin n → AE F E) :
    hA σ J (a • v) w = a * hA σ J v w := by
  simp only [hA, smul_dotProduct, smul_eq_mul]

theorem hA_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → AE F E) :
    hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  have : (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i) := by
    funext i; simp
  simp only [hA, this, Matrix.mulVec_add, dotProduct_add]

end ProdFormula

open ProdFormula in

theorem nmat_mul_nmat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) →
    ∀ (x u u' : Fin n → AE F E) (c c' : AE F E), hA σ J x x = 0 → hA σ J u x = 0 → hA σ J u' x = 0 →
    nmat σ J x u c * nmat σ J x u' c' = nmat σ J x (u + u') (c + c' - hA σ J u' u) := by
  intro F E _ _ _ _ _ σ hσ n J hJ x u u' c c' hxx hux hu'x
  have hxu : hA σ J x u = 0 := by rw [hA_swap σ hσ J hJ u x, hux, map_zero, neg_zero]
  have key : ∀ v, (nmat σ J x u c * nmat σ J x u' c') *ᵥ v =
      nmat σ J x (u + u') (c + c' - hA σ J u' u) *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_mulVec, nmat_mulVec, nmat_mulVec, nmat_mulVec]
    simp only [hA_add_left, hA_sub_left, hA_smul_left, hA_add_right, hxx, hux, hu'x, hxu]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by simpa only [Matrix.toLin'_apply] using key v)

end GlobalTheory.UnipMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergMatrixPreservesForm
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section

namespace GlobalTheory.UnipMass.Unitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_invol (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem cA_inclR (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  simp [cA, inclR]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem bar_add (w w' : Fin n → AE F E) :
    (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i) := by
  funext i; simp

theorem bar_sub (w w' : Fin n → AE F E) :
    (fun i => cA σ ((w - w') i)) = (fun i => cA σ (w i)) - fun i => cA σ (w' i) := by
  funext i; simp

theorem bar_smul (a : AE F E) (w : Fin n → AE F E) :
    (fun i => cA σ ((a • w) i)) = cA σ a • fun i => cA σ (w i) := by
  funext i; simp

theorem hA_add_left (v v' w : Fin n → AE F E) : hA σ J (v + v') w = hA σ J v w + hA σ J v' w := by
  simp [hA, add_dotProduct]

theorem hA_sub_left (v v' w : Fin n → AE F E) : hA σ J (v - v') w = hA σ J v w - hA σ J v' w := by
  simp [hA, sub_dotProduct]

theorem hA_smul_left (a : AE F E) (v w : Fin n → AE F E) : hA σ J (a • v) w = a * hA σ J v w := by
  simp [hA, smul_dotProduct]

theorem hA_add_right (v w w' : Fin n → AE F E) : hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  simp only [hA, bar_add, Matrix.mulVec_add, dotProduct_add]

theorem hA_sub_right (v w w' : Fin n → AE F E) : hA σ J v (w - w') = hA σ J v w - hA σ J v w' := by
  simp only [hA, bar_sub, Matrix.mulVec_sub, dotProduct_sub]

theorem hA_smul_right (a : AE F E) (v w : Fin n → AE F E) : hA σ J v (a • w) = cA σ a * hA σ J v w := by
  simp only [hA, bar_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hA_swap (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → AE F E) :
    hA σ J w v = -cA σ (hA σ J v w) := by
  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_invol σ hσ, incM, Matrix.map_apply, cA_inclR, hJ,
    map_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm (f := fun x x_1 => (cA σ) (v x) * (-(inclR (F := F) (AF F)) (J x_1 x) * w x_1))]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

variable {σ J}

theorem hA_nmat (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j) (x u : Fin n → AE F E) (c : AE F E)
    (hxx : hA σ J x x = 0) (hux : hA σ J u x = 0) (hc : c - cA σ c = -hA σ J u u) (v w : Fin n → AE F E) :
    hA σ J (nmat σ J x u c *ᵥ v) (nmat σ J x u c *ᵥ w) = hA σ J v w := by
  have hxu : hA σ J x u = 0 := by rw [hA_swap σ J hσ hJ u x, hux, map_zero, neg_zero]
  have hxw : hA σ J x w = -cA σ (hA σ J w x) := hA_swap σ J hσ hJ w x
  have huw : hA σ J u w = -cA σ (hA σ J w u) := hA_swap σ J hσ hJ w u
  rw [nmat_mulVec, nmat_mulVec]
  simp only [hA_sub_left, hA_sub_right, hA_smul_left, hA_smul_right, hA_add_left, hA_add_right, hxx, hux, hxu,
    hxw, huw]
  linear_combination (hA σ J v x * cA σ (hA σ J w x)) * hc

theorem entry_eq (T : Matrix (Fin n) (Fin n) (AE F E)) (i j : Fin n) :
    (Tᵀ * incM F J * T.map (cA σ)) i j = hA σ J (T *ᵥ Pi.single i 1) (T *ᵥ Pi.single j 1) := by
  have hs : ∀ m : Fin n, T *ᵥ Pi.single m 1 = fun k => T k m := fun m => by
    funext k; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hs, hs]
  simp only [hA, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem entry_J (hσ : ∀ a, σ (σ a) = a) (i j : Fin n) :
    incM F J i j = hA σ J (Pi.single i 1) (Pi.single j 1) := by
  have hb : (fun l => cA σ ((Pi.single j 1 : Fin n → AE F E) l)) = Pi.single j 1 := by
    funext l; by_cases h : l = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [hA, hb, single_one_dotProduct, Matrix.mulVec_single_one]
  simp

end GlobalTheory.UnipMass.Unitary

namespace GlobalTheory.UnipMass

theorem nmat_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) → ∀ (x u : Fin n → AE F E) (c : AE F E), hA σ J x x = 0 → hA σ J u x = 0 → c - cA σ c = -hA σ J u u → (nmat σ J x u c)ᵀ * incM F J * (nmat σ J x u c).map (cA σ) = incM F J := by
  intro F E _ _ _ _ _ σ hσ n J hJ x u c hxx hux hc
  ext i j
  rw [Unitary.entry_eq, Unitary.hA_nmat hσ hJ x u c hxx hux hc, ← Unitary.entry_J hσ]

end GlobalTheory.UnipMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpArchimedeanVectorActsBySchrodingerTr
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchRhoPure

variable (F : Type) [Field F] [NumberField F] in

def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evHom_apply {F : Type} [Field F] [NumberField F] (a : AF F) : evHom F a = evI F a := rfl

theorem rho_pureA_schrF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ → ∀ u : Matrix α β (AE F E), At (evI F) u →
    ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ),
      d.rho ψ u (pureA F f h) = pureA F (GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ)
        (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) f) h := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ u hu f h
  have hw : At (evI F) (d.e u) := fun r hr => by rw [← map_smul, hu r hr, map_zero]
  show schr ψ (d.e u) (pureA F f h) = _
  generalize d.e u = w at hw ⊢
  obtain ⟨p, q⟩ := w
  funext x
  have hfin : (fun i => ((x + p) i).2) = fun i => (x i).2 := by
    funext i
    have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h1 : (1 : Af F) * (p i).2 = 0 := congrArg (fun z : (κ → AF F) × (κ → AF F) => (z.1 i).2) (hw _ h0)
    change (x i).2 + (p i).2 = _
    rw [one_mul] at h1
    rw [h1, add_zero]
  have hAt : At (evI F) (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q)) := by
    intro v hv
    have hq : v • q = 0 := congrArg Prod.snd (hw v hv)
    rw [smul_add, ← dotProduct_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul v, ← dotProduct_smul, hq]
    simp
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + p) i).1) =
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + ArchUniq.locV p :=
    funext fun i => map_add (evHom F) (x i) (p i)
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q))) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * evI F (q i)) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, evI F (p i) * evI F (q i)) / 2 := by
    set z : mixedEmbedding.mixedSpace F := ∑ i, evI F (p i) * evI F (q i) with hz
    have hpq : evHom F (p ⬝ᵥ q) = z := by
      rw [RingHom.map_dotProduct]; rfl
    have hxq : evHom F (x ⬝ᵥ q) = ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * evI F (q i) := by
      rw [RingHom.map_dotProduct]; rfl
    have key : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evHom F ⅟(2 : AF F) * z) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evHom F ⅟(2 : AF F) * z) =
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z := by
      rw [← map_add, ← add_mul, ← map_add, invOf_two_add_invOf_two, map_one, one_mul]
    rw [← evHom_apply, map_add, map_mul, hpq, hxq, map_add]
    linarith
  simp only [schr, pureA, GlobalTheory.ArchUniq.schrF, GlobalTheory.ArchUniq.trP, GlobalTheory.ArchUniq.locV] at harch ⊢
  rw [hψ.2.2 _ hAt, hfin, htr, harch, ← mul_assoc]

end GlobalTheory.ArchRhoPure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelDegreeZeroResiduesRangeEqTop
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSShort

theorem totRes_incl_zero {K : Type} [Field K] [NumberField K] {X : Data K} {s : Fin X.D → Fin X.N → K} {hs : X.IsGood s} {δ : ℕ}
    (Co : Coord X.toGeo hs δ) (x : X.V 0) : totRes Co (incl X 0 x) = Co.ev 0 (hs.res 0 x.1) := by
  have h : incl X 0 x 0 = x.1 := Pi.single_eq_same (M := fun j => X.toGeo.Sec j) 0 x.1
  simp only [totRes, LinearMap.comp_apply, LinearMap.proj_apply, h, LinearEquiv.coe_coe]

theorem map_totRes_range_incl_zero : Quoted → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), IsNef K X.L₂ → IsBig K X.L₂ → (LinearMap.range (incl X 0)).map (totRes Co) = ⊤ := by
  intro Q K _ _ X s hs δ Co hnef hbig
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨f, hf⟩ := GlobalTheory.HSResOnto.res_onto Q K X.toGeo hnef hbig s hs ((Co.ev 0).symm v)
  have hf' : hs.res 0 (X.toGeo.mulE 0 f) = (Co.ev 0).symm v := hf
  have hm : X.toGeo.mulE 0 f ∈ X.V 0 := X.global_le 0 (Nat.zero_le _) (X.toGeo.mulE_mem_global 0 f)
  refine Submodule.mem_map.2 ⟨incl X 0 ⟨_, hm⟩, LinearMap.mem_range_self _ _, ?_⟩
  rw [totRes_incl_zero, hf', LinearEquiv.apply_symm_apply]

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairLatticeLocalSplitStatement
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_lattice_local_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * y = 0 → cT (σ : E →+* E) x * J * y = 1 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  first | exact @GlobalTheory.IwSplitLine.iwasawa_line_split | exact GlobalTheory.IwSplitLine.iwasawa_line_split | (intros; apply GlobalTheory.IwSplitLine.iwasawa_line_split <;> assumption)
end

