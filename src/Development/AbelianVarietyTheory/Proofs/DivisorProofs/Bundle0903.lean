import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0881
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0888
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0839
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderLatticeEqSteinitzFormCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderOfLocalCongruenceSplitStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedOrder_of_local_congruence_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) → ∀ z : Af E, (∀ v, LocIn (expIn c v) v z) → z ∈ hatO c := by
  first | exact @GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn | exact GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn | (intros; apply GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEigSp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.LieType

def eigSp {F : Type} [Field F] [NumberField F] {g : ℕ} (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (τ : F →+* ℂ) :
    Submodule ℂ (Fin g → ℂ) where
  carrier := {u | ∀ c : 𝓞 F, φ c *ᵥ u = τ (c : F) • u}
  add_mem' := by
    intro u v hu hv c
    rw [Matrix.mulVec_add, hu c, hv c, smul_add]
  zero_mem' := by intro c; simp
  smul_mem' := by
    intro a u hu c
    rw [Matrix.mulVec_smul, hu c, smul_comm]

theorem mem_eigSp {F : Type} [Field F] [NumberField F] {g : ℕ} (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (τ : F →+* ℂ)
    (u : Fin g → ℂ) : u ∈ eigSp φ τ ↔ ∀ c : 𝓞 F, φ c *ᵥ u = τ (c : F) • u := Iff.rfl

end GlobalTheory.UPel.HT.LieType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleLengthDisjointSupport
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem sectionsOn_res_pi_bijective_of_separating {X : Scheme.{0}} (F : X.Modules) [IsFiniteQC F]
    (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] {ι : Type} [Fintype ι] (W : ι → X.Opens)
    (hcov : support F ⊆ ⋃ i, (W i : Set X))
    (hdisj : ∀ i j, i ≠ j → ∀ x ∈ support F, x ∈ W i → x ∉ W j) :
    Function.Bijective
      (LinearMap.pi fun i => sectionsOn.res R F (le_top : W i ≤ ⊤) :
        sectionsOn F ⊤ →ₗ[R] ∀ i, sectionsOn F (W i)) := by
  classical
  refine ⟨?_, fun t => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    apply (sectionsOn.toΓ F ⊤).injective
    rw [map_zero]
    refine section_eq_zero_of_germ _ fun x hx => ?_
    by_cases hxs : x ∈ support F
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hxs)
      have h0 : sectionsOn.res R F (le_top : W i ≤ ⊤) s = 0 := congrFun hs i
      have := congrArg (fun u => F.presheaf.germ (W i) x hi (sectionsOn.toΓ F (W i) u)) h0
      simp only [sectionsOn.toΓ_res, map_zero] at this
      rwa [F.presheaf.germ_res_apply] at this
    · exact (notMem_support_iff.1 hxs).elim _ _
  have key (i : ι) : ∃ s : sectionsOn F ⊤, sectionsOn.res R F (le_top : W i ≤ ⊤) s = t i ∧
      ∀ j, j ≠ i → sectionsOn.res R F (le_top : W j ≤ ⊤) s = 0 := by
    let C : X.Opens := ⟨(support F)ᶜ, (isClosed_support F).isOpen_compl⟩
    let V : X.Opens := (⨆ (j : ι) (_ : j ≠ i), W j) ⊔ C
    have hWV (j : ι) (hj : j ≠ i) : W j ≤ V :=
      le_sup_of_le_left (le_iSup₂ (f := fun (j : ι) (_ : j ≠ i) => W j) j hj)
    have hcovV : (⊤ : X.Opens) ≤ W i ⊔ V := fun x _ => by
      by_cases hxs : x ∈ support F
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov hxs)
        by_cases hji : j = i
        · exact Or.inl (hji ▸ hj)
        · exact Or.inr (hWV j hji hj)
      · exact Or.inr (Or.inr hxs)
    have : Subsingleton Γ(F, W i ⊓ V) := subsingleton_sections_of_notMem_support fun y hy hys => by
      rcases hy.2 with hy' | hy'
      · obtain ⟨j, hj, hyj⟩ : ∃ j, j ≠ i ∧ y ∈ W j := by
          simpa [Opens.mem_iSup] using hy'
        exact hdisj i j (Ne.symm hj) y hys hy.1 hyj
      · exact hy' hys
    obtain ⟨s, h₁, h₂⟩ := Qcqs.exists_section_glue₂ F (V₁ := W i) (V₂ := V) (W := ⊤) le_top le_top
      hcovV (sectionsOn.toΓ F (W i) (t i)) 0 (Subsingleton.elim _ _)
    refine ⟨(sectionsOn.toΓ F ⊤).symm s, (sectionsOn.toΓ F (W i)).injective ?_, fun j hj =>
      (sectionsOn.toΓ F (W j)).injective ?_⟩
    · rw [sectionsOn.toΓ_res, AddEquiv.apply_symm_apply]
      exact h₁
    · rw [sectionsOn.toΓ_res, AddEquiv.apply_symm_apply, map_zero]
      have e := congrArg (F.presheaf.map (homOfLE (hWV j hj)).op) h₂
      rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at e
      exact e
  choose s h₁ h₂ using key
  refine ⟨∑ i, s i, funext fun j => ?_⟩
  rw [LinearMap.pi_apply, map_sum, Finset.sum_eq_single j (fun i _ hi => h₂ i j hi.symm) (by simp),
    h₁]

theorem length_sectionsOn_top_eq_sum_of_separating :
    ∀ {X : Scheme.{0}} (F : X.Modules) [IsFiniteQC F] (R : Type) [CommRing R]
      [Algebra R Γ(X, ⊤)] {ι : Type} [Fintype ι] (W : ι → X.Opens),
      support F ⊆ ⋃ i, (W i : Set X) → (∀ i j, i ≠ j → ∀ x ∈ support F, x ∈ W i → x ∉ W j) →
      Module.length R (sectionsOn F ⊤) = ∑ i, Module.length R (sectionsOn F (W i)) := by
  intro X F _ R _ _ ι _ W hcov hdisj
  rw [(LinearEquiv.ofBijective _
    (sectionsOn_res_pi_bijective_of_separating F R W hcov hdisj)).length_eq,
    Module.length_pi_of_fintype]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulNormDualWeylTensorEvaluationLeFibreNorm
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.TSup

theorem evalAt_intVec {n : ℕ} (la : Fin n → ℕ) (y : Matrix (Fin n) (Fin n) ℂ) (j : Idx la) :
    evalAt y (map (Int.castRingHom ℂ) (intVec la j)) =
      ∑ i, onMat la i j * evalAt y (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ) := by
  rw [← coe_basis]
  have h : basis la ℂ j = ∑ i, onMat la i j • (toSpace la).symm (onBasis la i) := by
    apply (toSpace la).injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply, onMat, Matrix.of_apply]
    exact ((onBasis la).sum_repr _).symm
  rw [h, Submodule.coe_sum, map_sum]
  simp [Submodule.coe_smul, map_smul]

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ}

theorem tval_eq_onb (la : ∀ t, Fin (N t) → ℕ) (z : TIdx la → ℂ) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) :
    tval la z y = ∑ J : TIdx la, ((kron fun t => onMat (la t)) *ᵥ z) J *
      ∏ t, evalAt (y t) (((toSpace (la t)).symm (onBasis (la t) (J t)) : nabla (la t) ℂ) : Pol (N t) ℂ) := by
  unfold tval
  simp_rw [evalAt_intVec, Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [Matrix.mulVec, dotProduct, kron, Matrix.of_apply, Finset.sum_mul, Finset.prod_mul_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  ring

theorem norm_sum_mul_le {ι : Type} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ i, a i * b i‖ ≤ Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  calc ‖∑ i, a i * b i‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem mul_norm_tval_le_fibNorm : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (x : TIdx la → ℂ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) (u : ∀ t, UN (N t)) (s : ℝ), 0 ≤ s → s * ‖tval la x (fun t => X t * (u t).1)‖ ≤ Real.sqrt (∑ I, ‖(fibY la s X *ᵥ x) I‖ ^ 2) := by
  intro T _ _ N la hla x X u s hs
  have h1 : tval la x (fun t => X t * (u t).1) =
      tval la ((kron fun t => rhoMat (la t) (X t)) *ᵥ x) (fun t => (u t).1) := by
    have h := GlobalTheory.T.dualWeylTensorEvaluation_translate_kronecker T N la ℂ ℂ (RingHom.id ℂ) x X (fun t => (u t).1)
    simpa only [RingHom.id_apply, RingHom.coe_id, Matrix.map_id] using h
  have hk := (GlobalTheory.T.kroneckerProductFamily_mul_one_det T (fun t => Idx (la t)) ℂ (fun t => onMat (la t)) (fun t => rhoMat (la t) (X t))).1
  set E : TIdx la → ℂ := fun J => ∏ t, evalAt (u t).1
    (((toSpace (la t)).symm (onBasis (la t) (J t)) : nabla (la t) ℂ) : Pol (N t) ℂ) with hE
  have h2 : (s : ℂ) * tval la x (fun t => X t * (u t).1) = ∑ J, (fibY la s X *ᵥ x) J * E J := by
    rw [h1, tval_eq_onb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    have hsm : ∀ (M : Matrix (TIdx la) (TIdx la) ℂ) (v : TIdx la → ℂ), ((s : ℂ) • M) *ᵥ v = (s : ℂ) • (M *ᵥ v) := by
      intro M v
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [fibY, hsm, ← hk, ← Matrix.mulVec_mulVec, Pi.smul_apply, smul_eq_mul]
    ring
  have h3 : ∑ J, ‖E J‖ ^ 2 ≤ 1 := by
    have : ∑ J, ‖E J‖ ^ 2 = ∏ t, ∑ i, ‖evalAt (u t).1
        (((toSpace (la t)).symm (onBasis (la t) i) : nabla (la t) ℂ) : Pol (N t) ℂ)‖ ^ 2 := by
      rw [Fintype.prod_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      simp only [hE, norm_prod, Finset.prod_pow]
    rw [this]
    exact Finset.prod_le_one (fun t _ => Finset.sum_nonneg fun _ _ => by positivity)
      (fun t _ => GlobalTheory.T.dualWeyl_orthonormal_basis_values_at_unitary_sum_sq_le_one (N t) (la t) (hla t) (u t))
  have h4 : s * ‖tval la x (fun t => X t * (u t).1)‖ = ‖(s : ℂ) * tval la x (fun t => X t * (u t).1)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  rw [h4, h2]
  refine (norm_sum_mul_le _ _).trans ?_
  calc _ ≤ Real.sqrt (∑ I, ‖(fibY la s X *ᵥ x) I‖ ^ 2) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_one]
        exact h3
    _ = _ := mul_one _

end GlobalTheory.TSup

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeRelationOfPullbackIsoThickeningStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_relation_of_pullback_iso_thickening : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ Y Y₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : Y ⟶ Sp R) (i : X₀ ⟶ X) (i' : Y₀ ⟶ Y) (φ₀ φ₁ φ₂ : Y ⟶ X) (w₀ : φ₀ ≫ s = s' ≫ spMap (RingHom.id R)) (w₁ : φ₁ ≫ s = s' ≫ spMap (RingHom.id R)) (w₂ : φ₂ ≫ s = s' ≫ spMap (RingHom.id R)) (ψ₀ ψ₁ ψ₂ : Y₀ ⟶ X₀) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsThick I s' i' → IsBasis (smallG i L) → IsLift s i L u → ψ₀ ≫ i = i' ≫ φ₀ → ψ₁ ≫ i = i' ≫ φ₁ → ψ₂ ≫ i = i' ≫ φ₂ → GlobalTheory.CechPic.pull ψ₀ (cls L hL) = GlobalTheory.CechPic.pull ψ₁ (cls L hL) + GlobalTheory.CechPic.pull ψ₂ (cls L hL) → ∃ (T : Type) (_ : Category.{0} T) (_ : Quiver.IsThin T) (H : T ⥤ AffOp Y) (K₀ K₁ K₂ : T ⥤ (Small i L)ᵒᵖ) (le₀ : ∀ t, (H.obj t).unop.1 ≤ φ₀ ⁻¹ᵁ ((smallG i L).obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ φ₁ ⁻¹ᵁ ((smallG i L).obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ φ₂ ⁻¹ᵁ ((smallG i L).obj (K₂.obj t)).unop.1) (v : C0 (H ⋙ OAff s')), IsBasis H ∧ (∀ t, IsUnit (v t)) ∧ MulRel I (pullMap w₀ _ H K₀ le₀) (pullMap w₁ _ H K₁ le₁) (pullMap w₂ _ H K₂ le₂) u v := by
  first | exact @GlobalTheory.LBLift.IsoRel.mulRel_of_iso | exact GlobalTheory.LBLift.IsoRel.mulRel_of_iso | (intros; apply GlobalTheory.LBLift.IsoRel.mulRel_of_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisConjHeckeCharacterFinitePartEqOne
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CMVal.NormConj

theorem norm_sigma_ratio {E : Type} [Field E] [NumberField E] [IsCMField E] (σ : ℂ ≃+* ℂ) (φ : E →+* ℂ) (α : Eˣ) :
    ‖σ (φ (α : E) / starRingEnd ℂ (φ (α : E)))‖ = 1 := by
  rw [← IsCMField.complexEmbedding_complexConj, map_div₀]
  have e2 : σ (φ (IsCMField.complexConj E (α : E))) = starRingEnd ℂ (((σ : ℂ →+* ℂ).comp φ) (α : E)) := by
    rw [← IsCMField.complexEmbedding_complexConj]; rfl
  have e1 : σ (φ (α : E)) = ((σ : ℂ →+* ℂ).comp φ) (α : E) := rfl
  have h0 : ((σ : ℂ →+* ℂ).comp φ) (α : E) ≠ 0 := by simp
  rw [e2, e1, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h0)]

end GlobalTheory.CMVal.NormConj

open GlobalTheory.CMVal.NormConj in

theorem GlobalTheory.CMVal.norm_conj_finPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E)
    (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ),
    ‖σ (finPart χ y : ℂ)‖ = 1 := by
  intro E _ _ _ I _ φ _ s κ c hc χ hinf hχ σ y
  classical
  have hfin := GlobalTheory.CMVal.PicFin.finite_picO E c hc
  have hpos : 0 < Nat.card (PicO c) := Nat.card_pos
  have hmem : y ^ Nat.card (PicO c) ∈ (princ ⊔ hatOUnits c : Subgroup (Af E)ˣ) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  obtain ⟨p, ⟨α, rfl⟩, u, hu, hpu⟩ := Subgroup.mem_sup.1 hmem
  set h := Nat.card (PicO c)
  have hf : ((finPart χ y : ℂ)) ^ h = ((χ.inf α : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hpu, map_mul, hχ u hu, mul_one,
      eq_inv_of_mul_eq_one_left (finPart_mul_inf χ α), Units.val_inv_eq_inv_val]
  have hn : ‖σ (finPart χ y : ℂ)‖ ^ h = 1 := by
    rw [← norm_pow, ← map_pow, hf, (hasInfRatio_iff χ φ _).1 hinf α, map_inv₀, norm_inv, map_prod, norm_prod]
    simp only [map_zpow₀, norm_zpow, norm_sigma_ratio, one_zpow, Finset.prod_const_one, inv_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').1 hn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneQuaternionNearConjRationalTimesSupported
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSAStep

theorem idem_of_isPlacesIdem {F : Type} [Field F] [NumberField F] {S₁ : Finset (InfinitePlace F)}
    {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext ?_ ?_
  · funext w
    change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, one_mul]
    · rw [h2 w hw, zero_mul]
  · apply RestrictedProduct.ext
    intro v
    change evalV F v (sndA F ε) * evalV F v (sndA F ε) = evalV F v (sndA F ε)
    by_cases hv : v ∈ S₂
    · rw [h3 v hv, one_mul]
    · rw [h4 v hv, zero_mul]

variable {R : Type*} [CommRing R] {a b : R}

theorem nrm_split (x y : ℍ[R, a, b]) (e : R) (he : e * e = e) :
    nrm ((1 - e) • x + e • y) = (1 - e) * nrm x + e * nrm y := by
  simp only [nrm, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  linear_combination ((x.re - y.re) ^ 2 - a * (x.imI - y.imI) ^ 2 - b * (x.imJ - y.imJ) ^ 2 +
    a * b * (x.imK - y.imK) ^ 2) * he

theorem nrm_star (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by
  simp [nrm]

theorem nrm_one : nrm (1 : ℍ[R, a, b]) = 1 := by simp [nrm]

theorem pure_sq (u : ℍ[R, a, b]) (t : R) (hn : nrm u = 1) (hr : u.re = t) :
    (u - algebraMap R ℍ[R, a, b] t).re = 0 ∧
      (u - algebraMap R ℍ[R, a, b] t) * (u - algebraMap R ℍ[R, a, b] t) = algebraMap R ℍ[R, a, b] (t ^ 2 - 1) := by
  unfold nrm at hn
  refine ⟨by simp [hr], ?_⟩
  ext <;> simp [QuaternionAlgebra.algebraMap_eq, hr]
  · linear_combination (-1 : R) * hn + (u.re + t) * hr
  all_goals ring

end GlobalTheory.QSAStep

namespace GlobalTheory.QSAStep

variable {F : Type} [Field F] [NumberField F] {a b : F}

theorem rat_mul (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat]

theorem rat_add (x y : ℍ[F, a, b]) : rat (x + y) = rat x + rat y := by
  ext <;> simp [rat]

theorem rat_algebraMap (c : F) :
    rat (algebraMap F ℍ[F, a, b] c) = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) := by
  ext <;> simp [rat, QuaternionAlgebra.algebraMap_eq]

theorem continuous_affine (ε : AF F) :
    Continuous fun x : DA F a b => (1 - ε) • x + ε • (1 : DA F a b) := by
  apply continuous_induced_rng.2
  have e : (coords ∘ fun x : DA F a b => (1 - ε) • x + ε • (1 : DA F a b)) =
      fun x => (1 - ε) • coords x + coords (ε • (1 : DA F a b)) := by
    funext x i
    fin_cases i <;> simp [coords]
  rw [e]
  have hc : Continuous (coords : DA F a b → Fin 4 → AF F) := continuous_induced_dom
  exact ((continuous_const (y := (1 - ε : AF F))).smul hc).add continuous_const

end GlobalTheory.QSAStep

namespace GlobalTheory.QSAStep

theorem key_step : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → ε • (g - 1) = 0 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ w ∈ W, ∃ y : DA F a b, IsUnit (nrm y) ∧ ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ y * w = rat γ * y * h := by
  classical
  intro F _ _ a b ha hb S₁ S₂ ε hε hS hsplit g hg hg1 W hW
  have hee : ε * ε = ε := idem_of_isPlacesIdem hε
  have h11 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hee
  have h10 : (1 - ε) * ε = 0 := by linear_combination -hee
  have h01 : ε * (1 - ε) = 0 := by linear_combination -hee
  set ι := algebraMap F (AF F) with hι
  set φ : DA F a b → DA F a b := fun x => (1 - ε) • x + ε • (1 : DA F a b) with hφ
  have hφg : φ g = g := by
    have : φ g = g - ε • (g - 1) := by
      simp only [hφ, sub_smul, one_smul, smul_sub]; abel
    rw [this, hg1, sub_zero]
  have hW' : φ ⁻¹' W ∈ 𝓝 g :=
    (continuous_affine ε).continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (φ g); rw [hφg]; exact hW)
  obtain ⟨O, hO, ⟨x, hx⟩, hOu⟩ := GlobalTheory.T.quaternion_norm_one_trace_open_adeles F a b ha hb g hg _ hW'
  obtain ⟨t, htZ, s, hts⟩ := GlobalTheory.T.additive_strongApproximation_avoiding_finset F S₁ S₂ ε hε hS x O (hO.mem_nhds hx) {1, -1}
  obtain ⟨u₀, hu₀W, hu₀n, hu₀r⟩ := hOu _ hts
  obtain ⟨h₁, hh₁n, hh₁r⟩ := hsplit (ι t)
  have hc : t ^ 2 - 1 ≠ 0 := by
    have h1 : t ≠ 1 := fun h => htZ (by simp [h])
    have h2 : t ≠ -1 := fun h => htZ (by simp [h])
    have : t ^ 2 - 1 = (t - 1) * (t + 1) := by ring
    rw [this]
    exact mul_ne_zero (sub_ne_zero.2 h1) (fun h => h2 (eq_neg_of_add_eq_zero_left h))
  obtain ⟨u, hu⟩ : ∃ u : DA F a b, u = (1 - ε) • u₀ + ε • h₁ := ⟨_, rfl⟩
  have hun : nrm u = 1 := by
    rw [hu, nrm_split _ _ _ hee, hu₀n, hh₁n]; ring
  have hur : u.re = ι t := by
    rw [hu]
    simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, smul_eq_mul, hu₀r]
    linear_combination hh₁r - s * hee
  obtain ⟨hq0, hqq⟩ := pure_sq u (ι t) hun hur
  set q := u - algebraMap (AF F) (DA F a b) (ι t) with hq
  have hqq' : q * q = algebraMap (AF F) (DA F a b) (ι (t ^ 2 - 1)) := by
    rw [hqq]; simp [hι]
  obtain ⟨p, hp0, hpp⟩ := GlobalTheory.T.exists_rational_pure_quaternion_sq_of_adelic F a b ha hb _ hc q hq0 hqq'
  have hrp0 : (rat p).re = 0 := by simp [rat, hp0]
  have hrpp : rat p * rat p = algebraMap (AF F) (DA F a b) (ι (t ^ 2 - 1)) := by
    rw [← rat_mul, hpp, rat_algebraMap]
  obtain ⟨y, hy, hyq⟩ := GlobalTheory.T.exists_unit_intertwiner_adelicQuaternion F a b ha hb _ hc (rat p) q hrp0 hq0 hrpp hqq'
  set γ : ℍ[F, a, b] := algebraMap F ℍ[F, a, b] t + p with hγ
  have hγn : nrm γ = 1 := by
    have hre := congrArg QuaternionAlgebra.re hpp
    simp [QuaternionAlgebra.algebraMap_eq, hp0] at hre
    simp [hγ, nrm, QuaternionAlgebra.algebraMap_eq, hp0]
    linear_combination -hre
  have hyu : y * u = rat γ * y := by
    have : u = q + algebraMap (AF F) (DA F a b) (ι t) := by rw [hq]; abel
    rw [this, mul_add, hyq, hγ, rat_add, rat_algebraMap, add_mul, ← Algebra.commutes, add_comm]
  set h' : DA F a b := (1 - ε) • (1 : DA F a b) + ε • h₁ with hh'
  set h'' : DA F a b := (1 - ε) • (1 : DA F a b) + ε • star h₁ with hh''
  have hwh : φ u₀ * h' = u := by
    simp only [hφ, hh', hu, add_mul, mul_add, smul_mul_smul_comm, h11, h10, h01, hee, zero_smul, mul_one, one_mul,
      add_zero, zero_add]
  have hhh : h' * h'' = 1 := by
    simp only [hh', hh'', add_mul, mul_add, smul_mul_smul_comm, h11, h10, h01, hee, zero_smul, mul_one, one_mul,
      add_zero, zero_add, mul_star_eq, hh₁n, map_one]
    rw [← add_smul, sub_add_cancel, one_smul]
  refine ⟨φ u₀, hu₀W, y, hy, γ, hγn, h'', ?_, ?_, ?_⟩
  · rw [hh'', nrm_split _ _ _ hee, nrm_one, nrm_star, hh₁n]; ring
  · have e1 : h'' - 1 = ε • (star h₁ - 1) := by
      simp only [hh'', sub_smul, one_smul, smul_sub]; abel
    rw [e1, smul_smul, hee]
  · calc y * φ u₀ = y * φ u₀ * (h' * h'') := by rw [hhh, mul_one]
      _ = y * (φ u₀ * h') * h'' := by simp only [mul_assoc]
      _ = rat γ * y * h'' := by rw [hwh, hyu]

end GlobalTheory.QSAStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderLatticeEqSteinitzFormCmStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderLattice_eq_steinitzForm_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ θ : E, θ ∉ maximalRealSubfield E → ∃ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (a₀ : maximalRealSubfield E), ∀ x : E, x ∈ lattice c y ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)), x = (a : E) + (b : E) * (θ + (a₀ : E)) := by
  first | exact @GlobalTheory.SteinitzOrder.lattice_eq_steinitz | exact GlobalTheory.SteinitzOrder.lattice_eq_steinitz | (intros; apply GlobalTheory.SteinitzOrder.lattice_eq_steinitz <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresPowEightMulStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ^ 8 * (p : ℂ) ^ 6 = (latticeCurve L).Δ ^ (p - 1) := by
  first | exact @GlobalTheory.CMModel.sqProd_pow_eight_mul | exact GlobalTheory.CMModel.sqProd_pow_eight_mul | (intros; apply GlobalTheory.CMModel.sqProd_pow_eight_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresSqMemStableStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ^ 2 ∈ F ∧ (sqProd p L t ∈ F → Stable L F (sqPt p t)) := by
  first | exact @GlobalTheory.CMModel.sqProd_sq_mem_and_stable | exact GlobalTheory.CMModel.sqProd_sq_mem_and_stable | (intros; apply GlobalTheory.CMModel.sqProd_sq_mem_and_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemePointsValuationRingMulEquivStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_group_scheme_points_valuationRing_mulEquiv : ∀ (U Ω : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [Algebra U Ω] [IsFractionRing U Ω] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsProper G.hom → ∀ u : Sp U ⟶ S, ∃ e : (Over.mk u ⟶ G) ≃* (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G), ∀ P, (e P).left = spMap (algebraMap U Ω) ≫ P.left := by
  first | exact @GlobalTheory.ValPts.points_generic_mulEquiv | exact GlobalTheory.ValPts.points_generic_mulEquiv | (intros; apply GlobalTheory.ValPts.points_generic_mulEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
section
namespace GlobalTheory.ScalarPoin

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def laS (X : Data E r) (k : ℕ) : Wt X.Ψ r := fun _ j => if X.p0 ≤ (j : ℕ) then (k : ℤ) else -(k : ℤ)

def qS (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x : Frame X.Ψ r) : ℂ :=
  ∏ τ, ((KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) ^ k

theorem qS_pow (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x : Frame X.Ψ r) :
    qS X x0 k x = qS X x0 1 x ^ k := by
  simp only [qS, pow_one, Finset.prod_pow]

theorem qS_cpt (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)) :
    qS X x0 k (cpt X x0 z) = 1 := by
  unfold qS
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [KU.Mx_cpt X ho, KU.tl_nM₂₂, ExF.det_unipotentFrame_eq_one, KU.tl, Matrix.det_submatrix_equiv_self, ExF.det_nM]
  simp

end

end GlobalTheory.ScalarPoin
end

