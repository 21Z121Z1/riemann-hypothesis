import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumDoubledWeilFixedDiagonalStabilizer

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LocalIsom

theorem lintegral_sq_eq_of_acts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∀ φ φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ → φ₁ ∈ GlobalTheory.WeilM.SB _ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om' (x, 1)) φ φ₁ →
      ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ₁ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr v x _ φ φ₁ hφ hφ₁ hact μ hμ
  obtain ⟨r, K, hrm, hinv, hsch, hK, hKi, hint⟩ := GlobalTheory.T.exists_periodic_measurable_schwartz_bound (κ := Fin a' × Fin (a + a')) v
  letI mA : MeasurableSpace (Fin a' × Fin (a + a') → AF F) := borel _
  haveI : BorelSpace (Fin a' × Fin (a + a') → AF F) := ⟨rfl⟩
  have hμA : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F)) := inferInstance
  obtain ⟨C, hC0, hCt, hC⟩ := GlobalTheory.T.lintegral_normSq_componentTensor_eq_const_mul v r hrm hinv _ hμA μ hμ K hK hKi (hint _ hμA).1 (hint _ hμA).2
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil').unit
  have e := hU _ hμA (x, 1) _ (hsch φ hφ)
  rw [hact r ⟨hinv, hsch φ hφ⟩, hC φ₁ hφ₁.1.continuous hφ₁.2, hC φ hφ.1.continuous hφ.2] at e
  exact (ENNReal.mul_right_inj hC0 hCt).mp e

end GlobalTheory.LocalIsom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorNormalisesSchroedingerOperator
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocModel

theorem weil_normalises_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (AE F E)),
      (∀ y, At (evFin F v) (Xm y)) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J) (ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v))),
      (∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)) (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ actY : Γ → Y → Y, (∀ g x, actAB (cA σ) (j g) (Xm x) = Xm (actY g x)) →
      ∀ g x, ω g * ρ x = ρ (actY g x) * ω g := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v Y _ Xm hXm ρ hρ Γ _ j ω hω actY hact g x
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a × Fin (a + a')) v
  have hS := IsUWeilPair.isUSplitting hT.weil
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply GlobalTheory.InertAvgDual.eq_of_tens_eq v hR0 (hR _ φ.2).1
  simp only [Module.End.mul_apply]
  have h1 := (hω g (ρ x φ) _).2 rfl R (hR _ (ρ x φ).2)
  have h2 := hρ x φ R (hR _ φ.2)
  have h3 := (hω g φ _).2 rfl R (hR _ φ.2)
  have h4 := hρ (actY g x) (ω g φ) R (hR _ (ω g φ).2)
  have h5 := hS.impl (j g) (Xm x) (tens (evFin F v) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) R) (hR _ φ.2).2
  rw [← h1, ← h4, ← h2, h5, hact, h3]

end GlobalTheory.InertLocModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentHasRationalWeilOperatorQuadraticCh
section
noncomputable section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

def mulQ {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R) :
    ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun φ x := χ (quad h A x) * φ x
  map_add' φ φ' := funext fun x => mul_add _ _ _
  map_smul' a φ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mulQ_apply {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R)
    (φ : (κ → R) → ℂ) (x : κ → R) : mulQ χ h A φ x = χ (quad h A x) * φ x := rfl

theorem mulQ_neg_mulQ {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R)
    (φ : (κ → R) → ℂ) : mulQ χ h (-A) (mulQ χ h A φ) = φ := by
  funext x
  rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul]

theorem mulQ_schr {R κ : Type} [CommRing R] [Invertible (2 : R)] [Fintype κ] (χ : AddChar R ℂ) (B : Matrix κ κ R)
    (hB : Bᵀ = B) (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    mulQ χ (⅟2) (-B) (schr χ w φ) = schr χ (w.1, B *ᵥ w.1 + w.2) (mulQ χ (⅟2) (-B) φ) := by
  have hB' : (-B)ᵀ = -B := by rw [Matrix.transpose_neg, hB]
  funext x
  have key := quad_add (-B) hB' x w.1 w.2
  rw [Matrix.neg_mulVec, neg_neg] at key
  simp only [mulQ_apply, schr]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key]

theorem act_unip {F R κ : Type} [Field F] [CommRing R] [Algebra F R] [Fintype κ] [DecidableEq κ] (b : Matrix κ κ F)
    (w : (κ → R) × (κ → R)) :
    act ((Matrix.fromBlocks 1 0 b 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R)) w =
      (w.1, b.map (algebraMap F R) *ᵥ w.1 + w.2) := by
  rw [Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), act_fromBlocks]
  simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def qI (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem eventually_integral (x : κ → AF F) :
    ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
  eventually_all.2 fun i => (x i).2.2

theorem finite_mulSupport {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (x : κ → AF F) :
    (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
  refine (Filter.eventually_cofinite.1 (hφ.2.and (eventually_integral x))).subset fun v hv => ?_
  intro h
  apply hv
  change φ v _ = 1
  rw [h.1, ind, Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
    from h.2), Pi.one_apply]

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mulQ_mem_SB {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K]
    (χ : AddChar K ℂ) (hχ : Continuous χ) (h : K) (A : Matrix κ κ K) {φ : (κ → K) → ℂ} (hφ : φ ∈ SB (κ → K)) :
    mulQ χ h A φ ∈ SB (κ → K) :=
  ⟨((GlobalTheory.SchrSBFin.isLocallyConstant_addChar χ hχ).comp_continuous (continuous_quad h A)).mul hφ.1, hφ.2.mul_left⟩

theorem mulQ_bijOn {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K]
    (χ : AddChar K ℂ) (hχ : Continuous χ) (h : K) (A : Matrix κ κ K) :
    Set.BijOn (mulQ χ h A) (SB (κ → K) : Set _) (SB (κ → K) : Set _) := by
  refine Set.InvOn.bijOn (f' := mulQ χ h (-A)) ⟨fun φ _ => mulQ_neg_mulQ χ h A φ, fun φ _ => ?_⟩
    (fun φ hφ => mulQ_mem_SB χ hχ h A hφ) (fun φ hφ => mulQ_mem_SB χ hχ h (-A) hφ)
  have := mulQ_neg_mulQ χ h (-A) φ
  rwa [neg_neg] at this

theorem quad_mem {v : Pl F} {h : Fv F v} (hh : h ∈ v.adicCompletionIntegers F) {A : Matrix κ κ (Fv F v)}
    (hA : ∀ i j, A i j ∈ v.adicCompletionIntegers F) {x : κ → Fv F v} (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) :
    quad h A x ∈ v.adicCompletionIntegers F := by
  unfold quad
  refine mul_mem hh (sum_mem fun i _ => mul_mem (hx i) (sum_mem fun j _ => mul_mem (hA i j) (hx j)))

theorem invOf_two_eq (v : Pl F) : ⅟(2 : Fv F v) = algebraMap F (Fv F v) (2⁻¹) := by
  refine (invOf_eq_right_inv ?_)
  rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

theorem eventually_mulQ_ind (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (b : Matrix κ κ F) :
    ∀ᶠ v : Pl F in cofinite, mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))) (ind κ v) = ind κ v := by
  filter_upwards [GlobalTheory.psiLoc_eventually_trivial_integers ψ hψ, eventually_algebraMap_mem_integers (2⁻¹ : F),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_algebraMap_mem_integers (b i j)] with v h1 h2 h3
  funext x
  rw [mulQ_apply]
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have hq : quad (⅟2) (-(b.map (algebraMap F (Fv F v)))) x ∈ v.adicCompletionIntegers F :=
      quad_mem (show ⅟(2 : Fv F v) ∈ v.adicCompletionIntegers F by rw [invOf_two_eq]; exact h2) (fun i j => neg_mem (h3 i j)) hx
    rw [GlobalTheory.LatVac.psiAt_apply, h1 _ hq, one_mul]
  · rw [ind, Set.indicator_of_notMem (show x ∉ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx), mul_zero]

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem invOf_two_eq' (R : Type) [CommRing R] [Algebra F R] [Invertible (2 : R)] : ⅟(2 : R) = algebraMap F R (2⁻¹) := by
  refine (invOf_eq_right_inv ?_)
  rw [← map_ofNat (algebraMap F R) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

theorem evFin_quad (b : Matrix κ κ F) (v : Pl F) (x : κ → AF F) :
    evFin F v (quad (⅟2) (-(b.map (algebraMap F (AF F)))) x) =
      quad (⅟2) (-(b.map (algebraMap F (Fv F v)))) (fun i => evFin F v (x i)) := by
  simp [quad, dotProduct, Matrix.mulVec, map_sum, GlobalTheory.VacAny.evFin_invOf_two]

theorem psi_quad_rat (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (ξ : κ → F) :
    ψ (quad (⅟2) (-(b.map (algebraMap F (AF F)))) (fun i => algebraMap F (AF F) (ξ i))) = 1 := by
  have h := map_quad (algebraMap F (AF F)) (2⁻¹ : F) (-b) ξ
  rw [Matrix.map_neg _ (map_neg _), ← invOf_two_eq'] at h
  rw [← h]
  exact hψ.2.1 _

theorem thetaSum_mulQ (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))) Φ) = thetaSum F Φ := by
  unfold thetaSum
  congr 1
  funext ξ
  rw [mulQ_apply, psi_quad_rat ψ hψ b ξ, one_mul]

theorem archMul_neg_mul (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F))
    (y : κ → mixedEmbedding.mixedSpace F) : archMul h A y * archMul h (-A) y = 1 := by
  unfold archMul
  rw [← AddChar.map_add_eq_mul, quad_neg, map_neg, neg_neg, neg_add_cancel, AddChar.map_zero_eq_one]

theorem surjective_arch (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F)) :
    Function.Surjective (SchwartzMap.smulLeftCLM ℂ (archMul h A) : SInf F κ →L[ℂ] SInf F κ) := by
  intro f
  refine ⟨SchwartzMap.smulLeftCLM ℂ (archMul h (-A)) f, ?_⟩
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
    SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul, smul_eq_mul, ← mul_assoc,
    archMul_neg_mul, one_mul]

theorem at_pairA (a : AF F) : At (evI F) (pairA F (fstA F a) 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem mulQ_pure (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (f : SInf F κ)
    {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) :
    mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (SchwartzMap.smulLeftCLM ℂ
                   (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))) f)
        (fun v => mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))) (φ v)) := by
  funext x
  set Q := quad (⅟2) (-(b.map (algebraMap F (AF F)))) x with hQ
  obtain ⟨hfin, hprod⟩ := GlobalTheory.T.adelicAddChar_eq_archimedean_mul_finprod_local F ψ hψ.1 Q
  simp only [hQ, evFin_quad] at hfin hprod
  have harch : ψ (pairA F (fstA F Q) 0) =
      archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F)) (fun i => evI F (x i)) := by
    rw [hψ.2.2 _ (at_pairA Q)]
    have e1 : evI F (pairA F (fstA F Q) 0) =
        quad (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F)) (fun i => evI F (x i)) :=
      map_quad (qI F) _ _ x
    rw [e1, archMul, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  rw [← hQ] at hprod
  change ψ Q * (f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) =
    (SchwartzMap.smulLeftCLM ℂ (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))) f)
      (fun i => evI F (x i)) * ∏ᶠ v, (GlobalTheory.LatVac.psiAt ψ v (quad (⅟2) (-(b.map (algebraMap F (Fv F v))))
        (fun i => evFin F v (x i))) * φ v fun i => evFin F v (x i))
  rw [finprod_mul_distrib hfin (finite_mulSupport hφ x), SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
    smul_eq_mul, hprod, harch]
  ring

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad archMul)

open scoped Classical in

theorem hasOp_unip : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (b : Matrix κ κ F), bᵀ = b → HasOp ψ (Matrix.fromBlocks 1 0 b 1) := by
  intro F _ _ ψ hψ κ _ _ b hb
  have hB : ∀ (R : Type) [CommRing R] [Algebra F R], (b.map (algebraMap F R))ᵀ = b.map (algebraMap F R) :=
    fun R _ _ => by rw [← Matrix.transpose_map, hb]
  refine ⟨mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))), 1,
    SchwartzMap.smulLeftCLM ℂ (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))),
    fun v => mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))), one_ne_zero,
    surjective_arch _ _, fun v => mulQ_bijOn _ (GlobalTheory.VacAny.continuous_psiV hψ.1 v) _ _, fun v w φ _ => ?_,
    eventually_mulQ_ind ψ hψ.1 b, fun f φ hφ => ⟨mulQ_pure ψ hψ b f hφ, fun w => ?_, ?_⟩⟩
  · rw [act_unip, mulQ_schr _ _ (hB _)]
  · rw [act_unip, mulQ_schr _ _ (hB _)]
  · rw [thetaSum_mulQ ψ hψ b, one_mul]

end GlobalTheory.RatWeilUnip

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCmCoordinateLatticeOfIntegralGramPairing
section
set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

theorem mem_lat_of_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ d : Fin p → E, (∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) →
        d ∈ GlobalTheory.FlatCM.HomLat.lat X := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hG barE hbar d hd
  classical
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image d)
  have hsq : ((y.natAbs ^ 2 : ℕ) : ℤ) = y * y := by rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs, sq]
  have hint : ∀ a, IsIntegral ℤ (((y.natAbs ^ 2 : ℕ) : E) * d a) := fun a => by
    have h1 := hyi (d a) (Finset.mem_image_of_mem d (Finset.mem_univ a))
    have e : ((y.natAbs ^ 2 : ℕ) : E) * d a = (algebraMap ℤ E y) * (y • d a) := by
      rw [zsmul_eq_mul, algebraMap_int_eq, eq_intCast, ← _root_.mul_assoc]
      congr 1
      rw [← Int.cast_natCast (R := E), hsq]
      try push_cast
      try ring
    rw [e]
    exact isIntegral_algebraMap.mul h1
  set n : ℕ := y.natAbs ^ 2 with hn_def
  have hn : 0 < n := pow_pos (Int.natAbs_pos.2 hy0) 2
  let x : Fin p → 𝓞 E := fun a => ⟨(n : E) * d a, hint a⟩
  have hx : ∀ a, (x a : E) = n * d a := fun a => rfl
  have hψ := GlobalTheory.FlatCM.HomLat.isLinearHom_prod X x
  have hk := GlobalTheory.T.linearHom_kills_torsion_of_weilPairing_divisible E H hH K ρ σ₁ p X _ hψ n hn (fun f hf ⟨m, hm, z, hfz⟩ => by
    have hm' : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
    have hc : (fun a => (z a : E) / m) ∈ GlobalTheory.FlatCM.HomLat.lat X := Submodule.subset_span
      ⟨m, hm, z, fun a => by field_simp, f, hf, hfz⟩
    obtain ⟨w, hw⟩ := hd _ hc
    refine ⟨w, GlobalTheory.T.weilPairing_linearHom_span_gramForm E H hH K ρ σ₁ p X gP gQ hG m hm z f hf hfz x _ ?_⟩
    have hb : ∀ b, ((H.bar (x b) : 𝓞 E) : E) = n * barE (d b) := fun b => by
      rw [← hbar, hx, map_mul, map_natCast]
    have key : (m : E) * ((n : E) * (w : E)) =
        ∑ a, ∑ b, (z a : E) * (gP a b : E) * ((H.bar (x b) : 𝓞 E) : E) := by
      simp_rw [hb]
      rw [hw]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      field_simp
    apply RingOfIntegers.coe_injective
    push_cast
    exact key)
  obtain ⟨χ, hχ, hχn⟩ := GlobalTheory.T.exists_linearHom_pow_eq_of_kills_complex_torsion E H K σ₁ (X.A true) X.B _ hψ n hn hk
  exact Submodule.subset_span ⟨n, hn, x, hx, χ, hχ, hχn⟩

end GlobalTheory.FlatCM.HomLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealIntegralTensorSwapIffMemIdealSubgroup
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.IdealDict

open GlobalTheory.StdRead.CharVal

variable {D : D7}

theorem toE_bijective (D : D7) : Function.Bijective (toE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective.comp (GlobalTheory.BotFormula.toAfE D).bijective

theorem toE_inc (b : 𝓞 D.host.E) :
    toE D (inc D (b : D.host.E)) = (Formalism.L2.DIV.oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  rw [← finQ_incA, toE_finQ]
  rfl

theorem inId_of_mem {𝔪 : Ideal (𝓞 D.host.E)} {y : Formalism.MainNotions.StandardLatticesGL3.AE D} (hy : y ∈ hatId D 𝔪) : InId 𝔪 (toE D y) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    have ht' := (toE_int_iff t).2 ht
    have h := Ideal.mul_mem_right (⟨_, ht'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) _
      (Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS D.host.F D.host.E) hb)
    rw [RingHom.map_mul, toE_inc]
    exact ⟨_, h⟩
  | zero => rw [RingHom.map_zero]; exact ⟨zero_mem _, Ideal.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    rw [RingHom.map_add]
    exact ⟨add_mem h1 h3, Ideal.add_mem _ h2 h4⟩
  | neg a _ ha =>
    obtain ⟨h1, h2⟩ := ha
    rw [RingHom.map_neg]
    exact ⟨neg_mem h1, Submodule.neg_mem _ h2⟩

theorem exists_of_mem_idS {𝔪 : Ideal (𝓞 D.host.E)} {u : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hu : u ∈ Ideal.map (Formalism.L2.DIV.oToS D.host.F D.host.E) 𝔪) : ∃ y ∈ hatId D 𝔪, toE D y = u.1 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨inc D (b : D.host.E), AddSubgroup.subset_closure ⟨b, hb, 1, one_mem _, (mul_one _).symm⟩, toE_inc b⟩
  | zero => exact ⟨0, zero_mem _, RingHom.map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨z, hz, e'⟩ := hb
    refine ⟨y + z, add_mem hy hz, ?_⟩
    rw [RingHom.map_add, e, e']
    exact (AddMemClass.coe_add _ a b).symm
  | smul s a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨t, ht⟩ := (toE_bijective D).2 s.1
    have htO : t ∈ OhE D := (toE_int_iff t).1 (by rw [ht]; exact s.2)
    refine ⟨t * y, GlobalTheory.FunObj.StdDatum.mul_mem_hatId htO hy, ?_⟩
    have h1 := (toE D).map_mul t y
    rw [e, ht] at h1
    rw [smul_eq_mul]
    exact h1.trans (MulMemClass.coe_mul _ s a).symm

theorem inId_toE_iff : ∀ {D : D7} (𝔪 : Ideal (𝓞 D.host.E)) (y : Formalism.MainNotions.StandardLatticesGL3.AE D), InId 𝔪 (toE D y) ↔ y ∈ hatId D 𝔪 := by
  intro D 𝔪 y
  refine ⟨fun ⟨h, hm⟩ => ?_, inId_of_mem⟩
  obtain ⟨z, hz, e⟩ := exists_of_mem_idS hm
  rwa [← (toE_bijective D).1 e]

end GlobalTheory.StdRead.IdealDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialNormalizingFactorNeZeroDefiniteBottomStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialNormalizingFactor_ne_zero_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, GlobalTheory.LFun.dSfun D.host.E ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 := by
  first | exact @GlobalTheory.BottomIPData.dSfun_bottom_ne_zero | exact GlobalTheory.BottomIPData.dSfun_bottom_ne_zero | (intros; apply GlobalTheory.BottomIPData.dSfun_bottom_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumDoubledWeilFixedDiagonalStabilizerStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (κ : Type) [Fintype κ], Fintype.card κ = a * b → ∀ (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ), (∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)), IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd → ∀ (χ : Chr F E), IsHecke F E χ → ∀ (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)), IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd → ∀ (p : UG (cA σ) (dbl (incM F JB))) (p₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F p₀ → ∀ (t : GL (Fin b) (AE F E)), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t : Matrix (Fin b) (Fin b) (AE F E)) → ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd p φ) = thetaSum F φ := by
  first | exact @GlobalTheory.ThetaSiegelRat.thetaSum_omd_of_fix_diag | exact GlobalTheory.ThetaSiegelRat.thetaSum_omd_of_fix_diag | (intros; apply GlobalTheory.ThetaSiegelRat.thetaSum_omd_of_fix_diag <;> assumption)
end

