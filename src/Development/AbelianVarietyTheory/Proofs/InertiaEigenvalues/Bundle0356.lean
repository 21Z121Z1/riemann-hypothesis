import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0002
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleDeRhamPeriodMatrixOfIsDR
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per Matrix

noncomputable section

namespace GlobalTheory.DRMat

theorem exists_fixed_of_stable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (S : Set (F →+* F)) (N : Submodule F (ι → F))
    (hN : ∀ σ ∈ S, ∀ v ∈ N, (fun j => σ (v j)) ∈ N) (v₀ : ι → F) (hv₀ : v₀ ∈ N) (h0 : v₀ ≠ 0) :
    ∃ v ∈ N, v ≠ 0 ∧ ∀ σ ∈ S, ∀ j, σ (v j) = v j := by
  classical
  have hex : ∃ k, ∃ v ∈ N, v ≠ 0 ∧ (Finset.univ.filter fun j => v j ≠ 0).card = k :=
    ⟨_, v₀, hv₀, h0, rfl⟩
  obtain ⟨w, hwN, hw0, hwk⟩ := Nat.find_spec hex
  obtain ⟨j₀, hj₀⟩ : ∃ j, w j ≠ 0 := by
    by_contra h; push_neg at h; exact hw0 (funext h)
  set v := (w j₀)⁻¹ • w with hv
  have hvN : v ∈ N := N.smul_mem _ hwN
  have hvj : v j₀ = 1 := by simp [hv, hj₀]
  have hsupp : ∀ j, v j ≠ 0 ↔ w j ≠ 0 := by
    intro j; simp [hv, hj₀]
  refine ⟨v, hvN, fun h => by simp [h] at hvj, fun σ hσ => ?_⟩
  by_contra hne
  push_neg at hne
  set u : ι → F := (fun j => σ (v j)) - v with hu
  have huN : u ∈ N := N.sub_mem (hN σ hσ v hvN) hvN
  have hu0 : u ≠ 0 := by
    obtain ⟨j, hj⟩ := hne
    intro h; apply hj; have := congrFun h j; simpa [hu, sub_eq_zero] using this
  have hlt : (Finset.univ.filter fun j => u j ≠ 0).card < Nat.find hex := by
    rw [← hwk]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨j₀, by simp [hj₀], by simp [hu, hvj]⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [← hsupp]; intro hvj0; apply hj; simp [hu, hvj0]
  exact Nat.find_min hex hlt ⟨u, huN, hu0, rfl⟩

theorem exists_period_matrix_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V), Formalism.MainNotions.N.IsDR (P.PD K) ρ → ∃ Q : GL n P.R.BdR, ∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q := by
  intro l _ P AI T n _ _ K V _ _ b ρ hDR
  set M : ↥(GK K) → Matrix n n P.R.BdR := fun g =>
    (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) with hM
  have hKact : ∀ (g : ↥(GK K)) (k : ↥K.1) (x : P.R.BdR),
      P.actQdR (g : GQ l) (algebraMap ↥K.1 P.R.BdR k * x) = algebraMap ↥K.1 P.R.BdR k * P.actQdR (g : GQ l) x := by
    intro g k x
    rw [← P.PD_actdR, ← P.PD_actdR, map_mul, AlgEquiv.commutes]
  let D : Submodule ↥K.1 (n → P.R.BdR) :=
    { carrier := {c | ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c}
      add_mem' := by
        intro x y hx hy g
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        have : (fun i => P.actQdR (g : GQ l) ((x + y) i)) =
            (fun i => P.actQdR (g : GQ l) (x i)) + (fun i => P.actQdR (g : GQ l) (y i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, hx g, hy g]
      zero_mem' := by
        intro g
        simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      smul_mem' := by
        intro k x hx g
        simp only [Set.mem_setOf_eq] at hx ⊢
        have : (fun i => P.actQdR (g : GQ l) ((k • x) i)) = k • (fun i => P.actQdR (g : GQ l) (x i)) := by
          funext i; simp only [Pi.smul_apply, Algebra.smul_def, hKact]
        rw [this, Matrix.mulVec_smul, hx g] }
  have hmemD : ∀ c, c ∈ D ↔ ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c := fun c => Iff.rfl

  let e : V ⊗[ℚ_[l]] P.R.BdR ≃ₗ[ℚ_[l]] (n → P.R.BdR) :=
    TensorProduct.congr b.equivFun (LinearEquiv.refl ℚ_[l] P.R.BdR) ≪≫ₗ
      TensorProduct.comm ℚ_[l] (n → ℚ_[l]) P.R.BdR ≪≫ₗ TensorProduct.piScalarRight ℚ_[l] ℚ_[l] P.R.BdR n
  have he_tmul : ∀ v β, e (v ⊗ₜ β) = fun i => b.repr v i • β := by
    intro v β
    simp [e]
  have he : ∀ (g : ↥(GK K)) x, e (actVdR (P.PD K) ρ g x) = M g *ᵥ fun i => P.actQdR (g : GQ l) (e x i) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]; exact (Matrix.mulVec_zero _).symm
    | tmul v β =>
      have h1 : actVdR (P.PD K) ρ g (v ⊗ₜ β) = ρ g v ⊗ₜ P.actQdR (g : GQ l) β := by
        simp [actVdR, P.PD_actdR]
      rw [h1, he_tmul, he_tmul]
      funext i
      rw [← LinearMap.toMatrix_mulVec_repr b b (ρ g) v]
      simp only [hM, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, map_mul, AlgEquiv.commutes]
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by rw [map_mul]; ring
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, ← Matrix.mulVec_add]
      congr 1; funext i; simp
  have hmap : (DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)) = D.restrictScalars ℚ_[l] := by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.restrictScalars_mem, hmemD]
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun g => ?_
    rw [← e.injective.eq_iff, he, LinearEquiv.apply_symm_apply]
  have hfr : Module.finrank ℚ_[l] ↥D = Module.finrank ℚ_[l] K.1 * Fintype.card n := by
    have h1 := hDR
    unfold Formalism.MainNotions.N.IsDR at h1
    rw [Module.finrank_eq_card_basis b, LinearEquiv.finrank_eq (e.submoduleMap (DdR (P.PD K) ρ)), hmap] at h1
    exact h1

  rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    refine ⟨1, fun g => ?_⟩
    ext i; exact isEmptyElim i
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hKpos : 0 < Module.finrank ℚ_[l] ↥K.1 := Module.finrank_pos
  haveI : Module.Finite ℚ_[l] ↥D := Module.finite_of_finrank_pos (by rw [hfr]; positivity)
  haveI : Module.Finite ↥K.1 ↥D := Module.Finite.of_restrictScalars_finite ℚ_[l] ↥K.1 ↥D
  have hrank : Module.finrank ↥K.1 ↥D = Fintype.card n := by
    have := Module.finrank_mul_finrank ℚ_[l] ↥K.1 ↥D
    rw [hfr] at this
    exact Nat.eq_of_mul_eq_mul_left hKpos this
  let bK : Module.Basis n ↥K.1 ↥D :=
    (Module.finBasisOfFinrankEq ↥K.1 ↥D hrank).reindex (Fintype.equivFin n).symm
  let Q0 : Matrix n n P.R.BdR := Matrix.of fun i j => (bK j : n → P.R.BdR) i
  have hQ : ∀ g : ↥(GK K), M g * Q0.map (P.actQdR (g : GQ l)) = Q0 := by
    intro g
    ext i j
    have h := congrFun ((hmemD _).1 (bK j).2 g) i
    simpa [Q0, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  have hdet : IsUnit Q0.det := by
    letI : Field P.R.BdR := (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1.toField
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    obtain ⟨v, hv0, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    let S : Set (P.R.BdR →+* P.R.BdR) :=
      Set.range fun g : ↥(GK K) => ((P.actQdR (g : GQ l)) : P.R.BdR →+* P.R.BdR)
    have hstab : ∀ σ ∈ S, ∀ u ∈ LinearMap.ker (Matrix.mulVecLin Q0), (fun j => σ (u j)) ∈ LinearMap.ker (Matrix.mulVecLin Q0) := by
      rintro σ ⟨g, rfl⟩ u hu
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hu ⊢
      rw [← hQ g, ← Matrix.mulVec_mulVec]
      have : (Q0.map (P.actQdR (g : GQ l)) *ᵥ fun j => (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR) (u j)) = 0 := by
        funext i
        have := congrArg (P.actQdR (g : GQ l)) (congrFun hu i)
        simpa [Matrix.mulVec, dotProduct, map_sum, map_mul] using this
      rw [this, Matrix.mulVec_zero]
    obtain ⟨w, hwN, hw0, hwfix⟩ :=
      exists_fixed_of_stable S (LinearMap.ker (Matrix.mulVecLin Q0)) hstab v (by simpa using hQv) hv0
    have hwK : ∀ j, ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c = w j := fun j =>
      (P.PD K).invdR (w j) fun g => by rw [P.PD_actdR]; exact hwfix _ ⟨g, rfl⟩ j
    choose c hc using hwK
    have hQw : Q0 *ᵥ w = 0 := by simpa using hwN
    have hsum : ∑ j, c j • bK j = 0 := by
      apply Subtype.ext
      funext i
      have := congrFun hQw i
      simp only [Matrix.mulVec, dotProduct, Q0, Matrix.of_apply, Pi.zero_apply] at this
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        Algebra.smul_def, Submodule.coe_zero, Pi.zero_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => by rw [← hc j]; exact mul_comm _ _
    have hc0 := Fintype.linearIndependent_iff.mp bK.linearIndependent c hsum
    exact hw0 (funext fun j => by rw [← hc j, hc0 j, map_zero]; rfl)
  refine ⟨((Matrix.isUnit_iff_isUnit_det Q0).mpr hdet).unit, fun g => ?_⟩
  rw [IsUnit.unit_spec]
  exact hQ g

end GlobalTheory.DRMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDet
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.GLq.HCFrobWeight

open scoped Classical

section Reg

variable {H : Type} [Group H] [Fintype H]

theorem sum_irr_coeff (h : H) :
    ∑ σ ∈ (irr_finite_and_finsum_zOf_eq_one H).1.toFinset, (zOf σ).coeff h = if h = 1 then 1 else 0 := by
  obtain ⟨hfin, hsum⟩ := irr_finite_and_finsum_zOf_eq_one H
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
  have e := congrArg (fun z : MonoidAlgebra ℂ H => z.coeff h) hsum
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply] at e
  rw [e, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hh : h = 1
  · simp [hh]
  · simp [hh, Ne.symm hh]

theorem exists_irr_sum_ne_zero (F : H → ℂ) (hF : F 1 ≠ 0) :
    ∃ σ : H → ℂ, IsIrr σ ∧ ∑ h, F h * σ h⁻¹ ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply hF
  set s := (irr_finite_and_finsum_zOf_eq_one H).1.toFinset with hs
  have h0 : ∑ σ ∈ s, σ 1 / (Fintype.card H : ℂ) * ∑ h, F h * σ h⁻¹ = 0 := by
    refine Finset.sum_eq_zero fun σ hσ => ?_
    rw [hc σ (by simpa [hs] using hσ), mul_zero]
  rw [← h0]
  have e : ∑ σ ∈ s, σ 1 / (Fintype.card H : ℂ) * ∑ h, F h * σ h⁻¹ =
      ∑ h, F h * ∑ σ ∈ s, (zOf σ).coeff h := by
    simp_rw [Finset.mul_sum, ZSumOne.zOf_coeff]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [e, hs]
  simp_rw [sum_irr_coeff]
  simp

end Reg

variable {g : ℕ} [Fact g.Prime]

theorem isClass_of_isIrr {n : ℕ} {ψ : Gn g n → ℂ} (hψ : IsIrr ψ) : IsClass ψ := by
  obtain ⟨V, _, hV⟩ := hψ
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem ip_hc_eq_left (a b n : ℕ) (hn : n = a + b) (χ : Gn g n → ℂ) (hχ : IsClass χ) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) :
    ip χ (hc a b α β n) = (Fintype.card (Gn g a × Gn g b) : ℂ)⁻¹ *
      ∑ h : Gn g a, (∑ y : Gn g b, res a b χ h y * β y⁻¹) * α h⁻¹ := by
  rw [hc, FrobRecHC.hcT_adjoint g a b n hn χ _ hχ]
  unfold ip
  rw [Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Prod.fst_inv, Prod.snd_inv]
  ring

theorem ip_hc_eq_right (a b n : ℕ) (hn : n = a + b) (χ : Gn g n → ℂ) (hχ : IsClass χ) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) :
    ip χ (hc a b α β n) = (Fintype.card (Gn g a × Gn g b) : ℂ)⁻¹ *
      ∑ y : Gn g b, (∑ h : Gn g a, res a b χ h y * α h⁻¹) * β y⁻¹ := by
  rw [hc, FrobRecHC.hcT_adjoint g a b n hn χ _ hχ]
  unfold ip
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Prod.fst_inv, Prod.snd_inv]
  ring

theorem thetaInv_det_inv (θ : (ZMod g)ˣ →* ℂˣ) (y : Gn g 1) :
    ((θ⁻¹ (Matrix.GeneralLinearGroup.det y⁻¹) : ℂˣ) : ℂ) = ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) := by
  simp [map_inv]

end GlobalTheory.GLq.HCFrobWeight

namespace GlobalTheory.GLq.HCFrobWeight

open scoped Classical

theorem exists_irr_hc_thetaInv : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsIrr ψ → ∀ θ : (ZMod g)ˣ →* ℂˣ,
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0) ∧
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc 1 n (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0) := by
  intro g _ n ψ hψ θ
  have hcl := isClass_of_isIrr hψ
  constructor
  · intro hS
    obtain ⟨σ, hσ, hne⟩ := exists_irr_sum_ne_zero
      (fun h : Gn g n => ∑ y : Gn g 1, res n 1 ψ h y * ((θ⁻¹ (Matrix.GeneralLinearGroup.det y⁻¹) : ℂˣ) : ℂ))
      (by simp_rw [thetaInv_det_inv]; simpa [mul_comm] using hS)
    refine ⟨σ, hσ, ?_⟩
    rw [ip_hc_eq_left n 1 (n + 1) rfl ψ hcl]
    exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) hne
  · intro hS
    obtain ⟨σ, hσ, hne⟩ := exists_irr_sum_ne_zero
      (fun y : Gn g n => ∑ h : Gn g 1, res 1 n ψ h y * ((θ⁻¹ (Matrix.GeneralLinearGroup.det h⁻¹) : ℂˣ) : ℂ))
      (by simp_rw [thetaInv_det_inv]; simpa [mul_comm] using hS)
    refine ⟨σ, hσ, ?_⟩
    rw [ip_hc_eq_right 1 n (n + 1) (by omega) ψ hcl]
    exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) hne

end GlobalTheory.GLq.HCFrobWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLambdaAlgebraHomEvaluation
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.LamHom

def chr {B ι : Type} [CommRing B] [Fintype ι] {n : ℕ} [NeZero n] (u : ι → B) (hu : ∀ q, u q ^ n = 1) :
    Multiplicative (ι → ZMod n) →* B := GlobalTheory.RootCharacter.rootChar u hu

theorem chr_single {B ι : Type} [CommRing B] [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (hn : 1 < n) (u : ι → B)
    (hu : ∀ q, u q ^ n = 1) (q : ι) : chr u hu (Multiplicative.ofAdd (Pi.single q 1)) = u q := by
  haveI : Fact (1 < n) := ⟨hn⟩
  change ∏ p, u p ^ ((Pi.single q (1 : ZMod n) : ι → ZMod n) p).val = u q
  rw [Finset.prod_eq_single q]
  · simp [ZMod.val_one]
  · intro p _ hp
    simp [Pi.single_eq_of_ne hp]
  · simp

theorem exists_lamHom : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (B : Type) [CommRing B] [Algebra (X.O0 i) B] (ξ : ι → B), 0 < nu X i → nu X i + 1 ≤ M → Kills i B → (∀ q, ξ q ^ X.l i ^ (M - nu X i - 1) = 0) → ∃ φ : abelian₂ X i M ι →ₐ[X.O0 i] B, (∀ F, φ (toLam X i M ι F) = MvPolynomial.aeval ξ F) ∧ ∀ d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))), ∃ κ : GE N →* Bˣ, (∀ g, ((κ g : Bˣ) : B) = φ (delInv i M d g : (abelian₂ X i M ι)ˣ)) ∧ IsChar i κ ξ d := by
  intro D N X i M ι _ B _ _ ξ _ hM hK hξ
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hm : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    X.O_l i (by simpa using hu.map (algebraMap (X.O0 i) (X.O i)))
  have h4 : ((X.l i : ℕ) : B) ^ (nu X i + 1) = 0 := by
    have h := hK _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hm)
    rw [map_mul, map_pow, map_natCast] at h
    rw [pow_succ]
    exact h
  have hn : 1 < X.l i ^ M := Nat.one_lt_pow (by omega) hp.one_lt
  haveI : NeZero (X.l i ^ M) := ⟨by omega⟩
  have hu : ∀ q, (1 + ξ q) ^ (X.l i ^ M) = 1 := fun q =>
    KStar.Tree.one_add_pow_prime_pow_eq_one hp h4 hM (hξ q)
  let φ : abelian₂ X i M ι →ₐ[X.O0 i] B := MonoidAlgebra.lift (X.O0 i) B (Del X i M ι) (chr (fun q => 1 + ξ q) hu)
  have hφ : ∀ x, φ (MonoidAlgebra.of (X.O0 i) (Del X i M ι) x) = chr (fun q => 1 + ξ q) hu x := fun x =>
    MonoidAlgebra.lift_of _ x
  refine ⟨φ, fun F => ?_, fun d => ⟨(Units.map (φ : abelian₂ X i M ι →* B)).comp (delInv i M d), fun g => rfl, fun g => ?_⟩⟩
  · have : φ.comp (toLam X i M ι) = MvPolynomial.aeval ξ := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rw [AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_sub, map_one, hφ]
      have := chr_single hn (fun q => 1 + ξ q) hu q
      rw [sub_eq_iff_eq_add']
      convert this
    exact DFunLike.congr_fun this F
  · have h1 : ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) *
        MonoidAlgebra.of (X.O0 i) (Del X i M ι) (delAll X i M d g) = 1 :=
      Units.inv_mul ((MonoidAlgebra.of (X.O0 i) (Del X i M ι)).toHomUnits (delAll X i M d g))
    have h2 := congrArg φ h1
    rw [map_mul, map_one, hφ] at h2
    exact h2

end GlobalTheory.NewPrime.LamHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroSmulMemOfSpanEqTop
section
namespace GlobalTheory.QuotientLatticeTorsion

theorem exists_ne_zero_smul_mem_of_span_eq_top
    {O K V : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (N : Submodule O V) (hN : Submodule.span K (N : Set V) = ⊤) (v : V) :
    ∃ b : O, b ≠ 0 ∧ b • v ∈ N := by
  have hv : v ∈ Submodule.span K (N : Set V) := hN ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hax
    · rw [mul_smul]
      exact N.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors O) c
    refine ⟨s.1 * a, mul_ne_zero (nonZeroDivisors.ne_zero s.2) ha, ?_⟩
    have key : (s.1 * a) • c • x = r • a • x := by
      rw [← algebraMap_smul K (s.1 * a), ← algebraMap_smul K r, ← algebraMap_smul K a x,
        smul_smul, smul_smul, ← hrs, map_mul]
      congr 1
      ring
    rw [key]
    exact N.smul_mem r hax

theorem quotient_lattice_torsion
    {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {LL : Type} [Field LL]
    [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL] [IsDomain O]
    [IsFractionRing O LL] (T : Formalism.BasicNotions.LocLat G Qp LL O)
    (w : Formalism.BasicNotions.LocLat.V T ⧸ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T)) :
    ∃ (b : O), b ≠ (0 : O) ∧
      b • w = (0 : Formalism.BasicNotions.LocLat.V T ⧸ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T)) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨b, hb, hbv⟩ :=
    exists_ne_zero_smul_mem_of_span_eq_top (K := LL) T.L.T T.L.span v
  refine ⟨b, hb, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact hbv

end GlobalTheory.QuotientLatticeTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOfPowLeOfPowLeSameAdicTopology
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem TopBasis.exists_of_pow_le_of_pow_le :
    ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι)
      (I' : Ideal S) (n m : ℕ), IsHausdorff I S → 0 < n → 0 < m → I ^ n ≤ I' → I' ^ m ≤ I →
      ∃ TB' : TopBasis s I' ι, TB'.b = TB.b ∧ TB'.c = TB.c := by
  intro S A _ _ s I ι TB I' n m _ _ _ h1 h2
  have hk : ∀ k : ℕ, I ^ (n * k) ≤ I' ^ k := fun k => by
    rw [pow_mul]; exact Ideal.pow_right_mono h1 k
  classical
  refine ⟨{ TB with fin := ?_, approx := ?_, complete := ?_ }, rfl, rfl⟩
  · intro x k
    exact (TB.fin x (n * k)).subset fun i hi h => hi (hk k h)
  · intro x k F hF
    set G : Finset ι := F ∪ (TB.fin x (n * k)).toFinset with hG
    have hG' : ∀ i, i ∉ G → TB.c i x ∈ I ^ (n * k) := by
      intro i hi
      by_contra h
      exact hi (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
    have hmain := TB.approx x (n * k) G hG'
    have hmap : (I ^ (n * k)).map s ≤ (I' ^ k).map s := Ideal.map_mono (hk k)
    have hsplit : ∑ i ∈ G, s (TB.c i x) * TB.b i =
        ∑ i ∈ F, s (TB.c i x) * TB.b i + ∑ i ∈ G \ F, s (TB.c i x) * TB.b i := by
      rw [add_comm, Finset.sum_sdiff (Finset.subset_union_left)]
    have hrest : ∑ i ∈ G \ F, s (TB.c i x) * TB.b i ∈ (I' ^ k).map s := by
      refine Ideal.sum_mem _ fun i hi => ?_
      have : i ∉ F := (Finset.mem_sdiff.1 hi).2
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hF i this))
    have : x - ∑ i ∈ F, s (TB.c i x) * TB.b i =
        (x - ∑ i ∈ G, s (TB.c i x) * TB.b i) + ∑ i ∈ G \ F, s (TB.c i x) * TB.b i := by
      rw [hsplit]; ring
    rw [this]
    exact add_mem (hmap hmain) hrest
  · refine GlobalTheory.isAdicComplete_of_pow_le_of_pow_le A (I.map s) (I'.map s) n m ?_ ?_ TB.complete
    · rw [← Ideal.map_pow]; exact Ideal.map_mono h1
    · rw [← Ideal.map_pow]; exact Ideal.map_mono h2

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiGammaModelExtensionCocyclePairStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (A : Ob k G) (z : G → Fin A.m → k), z ∈ M.twistedModelAdmissibleCocycles A → ∃ (N : Lats k n A.m) (b g : ZMod n → Vc k A.m), M.Model A N ∧ Repr F A z b g ∧ InZZ (F.D A) Dt N b g := by
  first | exact @GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ | exact GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ | (intros; apply GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalFormUnramifiedRestrictionScalarsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_form_unramified_restrictionScalars : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)), IsRat r σ →
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) → (∀ k, fr l r (ω k) = ω k) →
    (∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k)) →
    ∃ (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
      (∀ i j, Continuous fun g => (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j) ∧
      (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) ∧
      (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) ∧
      ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) →
        (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) →
        ∃ c₀ : ↥(GK K) → n × Fin r → ℚ_[l], Continuous c₀ ∧ ∀ g,
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1) := by
  first | exact @GlobalTheory.PMon.exists_ratForm | exact GlobalTheory.PMon.exists_ratForm | (intros; apply GlobalTheory.PMon.exists_ratForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFiltrationAcrisStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_deRhamFiltration_acris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]) (Θ : Formalism.Per.Acris l →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧ (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧ (∀ a, ‖Θ a‖ ≤ 1) ∧ (∀ z : Formalism.Per.Fl l, Θ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.tm z)) = sh z) ∧ ∀ a : Formalism.Per.Acris l, ∃ hm, θ ⟨P.ιB (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) a)), hm⟩ = Θ a := by
  first | exact @GlobalTheory.PSer.theta_fil_acris | exact GlobalTheory.PSer.theta_fil_acris | (intros; apply GlobalTheory.PSer.theta_fil_acris <;> assumption)
end

