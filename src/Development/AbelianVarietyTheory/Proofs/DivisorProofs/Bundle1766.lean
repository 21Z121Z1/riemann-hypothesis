import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0459
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Formalism.LocalToGlobal.GlobalTheory.GL3.ProvisionExtensionLink
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
import Formalism.LocalToGlobal.GlobalTheory.GL3.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0326
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1731
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNontrivialHeckeChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDiagonalTorusCharacterFlatLineWeight
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS.FlatDiag

theorem norm_diagChar_flatWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (τ : Psi H) (t : Ix Dw → (CAt σ)ˣ), ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ = (∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖) / ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖ := by
  classical
  intro E _ _ _ H Dw l c σ τ t
  set e := exOf Dw (flatWt Dw τ) 0 with he_def
  have hne : τ.1 ≠ conjEmb τ.1 := fun h => conj_not_mem τ (h ▸ τ.2)
  have hE : ∀ (ρ : E →+* ℂ) (i : Fin (Dw.mult ρ)),
      e (some ⟨ρ, i⟩) = if ρ = τ.1 then -1 else if ρ = conjEmb τ.1 then 1 else 0 := by
    intro ρ i
    obtain ⟨n, hi⟩ := i
    simp only [he_def, exOf, exZ, wtOf, flatWt, parWt, Datum.mult] at hi ⊢
    by_cases h : ρ (H.rt : E) = H.rt0
    · rw [if_pos h] at hi
      rw [dif_pos h, dif_pos hi]
      have h2 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      by_cases h1 : ρ = τ.1
      · subst h1
        simp
      · have h3 : (⟨ρ, h⟩ : Psi H) ≠ τ := fun e => h1 (congrArg Subtype.val e)
        simp [h1, h2, h3]
    · rw [if_neg h] at hi
      rw [dif_neg h]
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      by_cases h' : conjEmb ρ (H.rt : E) = H.rt0
      · rw [dif_pos h', dif_pos hi]
        by_cases h2 : ρ = conjEmb τ.1
        · have h3 : (⟨conjEmb ρ, h'⟩ : Psi H) = τ := Subtype.ext (show conjEmb ρ = τ.1 by rw [h2, conjEmb_conjEmb])
          rw [if_pos h3, if_neg h1, if_pos h2]
          norm_num
        · have h3 : (⟨conjEmb ρ, h'⟩ : Psi H) ≠ τ := fun e => h2 (by
            rw [← congrArg Subtype.val e, conjEmb_conjEmb])
          rw [if_neg h3, if_neg h1, if_neg h2]
          norm_num
      · rw [dif_neg h']
        have h2 : ρ ≠ conjEmb τ.1 := fun e => h' (by rw [e, conjEmb_conjEmb]; exact τ.2)
        simp [h1, h2]
  have e0 : e none = 0 := by simp [he_def, exOf, exZ, wtOf_snd]
  let f : (CAt σ)ˣ →* ℂˣ := Units.map (MonoidHom.id ℂ)
  have hf : ∀ u : (CAt σ)ˣ, ((f u : ℂˣ) : ℂ) = toC (u : CAt σ) := fun _ => rfl
  have e₁ : GlobalTheory.CompHS.diagChar e t = ((∏ ix, f (t ix) ^ e ix : ℂˣ) : ℂ) := by
    have : (∏ ix, f (t ix) ^ e ix) = f (∏ ix, t ix ^ e ix) := by simp only [map_prod, map_zpow]
    rw [this, hf]
    rfl
  let g : (E →+* ℂ) → ℝ := fun ρ => ∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt σ))‖ ^ e (some ⟨ρ, i⟩)
  have e₂ : ‖GlobalTheory.CompHS.diagChar e t‖ = ∏ ρ, g ρ := by
    rw [e₁, Units.coe_prod, norm_prod, Fintype.prod_option, e0, zpow_zero, Units.val_one, norm_one, one_mul,
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun ρ _ => Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, hf]
  have e₃ : ∏ ρ, g ρ = g τ.1 * g (conjEmb τ.1) := by
    rw [← Finset.prod_pair hne]
    refine (Finset.prod_subset (Finset.subset_univ _) fun ρ _ hρ => ?_).symm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hρ
    exact Finset.prod_eq_one fun i _ => by rw [hE, if_neg hρ.1, if_neg hρ.2, zpow_zero]
  have gτ : g τ.1 = (∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [hE, if_pos rfl, zpow_neg_one]
  have gc : g (conjEmb τ.1) = ∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖ :=
    Finset.prod_congr rfl fun i _ => by rw [hE, if_neg hne.symm, if_pos rfl, zpow_one]
  rw [e₂, e₃, gτ, gc, div_eq_mul_inv, mul_comm]

end GlobalTheory.CompHS.FlatDiag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNonzeroThetaVectorsNumberField
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem GlobalTheory.ColNorms.familyVectors : GlobalTheory.ColNorms.FamilyVectors := by
  intro D cc δ B χ _ _ hc hδ hχ _ N N' L L' hA
  obtain ⟨h1, h2⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.vector_bound_link D cc hc δ hδ B χ hχ N N' L L' hA
  refine ⟨h1, h2, ?_⟩
  obtain ⟨χ', e, -, hv, -⟩ := GlobalTheory.TrueTheta.exists_family_of_curve D cc δ ⟨hc, hδ⟩
  obtain ⟨e1, e2, M, hM, hC⟩ := hv N N' L L' hA
  obtain ⟨c, hcE⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ ⟨hc, hδ⟩ N N' _
    (Or.inr ⟨_, _, hA.2.2.1, hA.2.2.2, rfl⟩)).1 _ h1 _ e1 e2
  have hE : B.eNat χ N N' L L' = fun z => c * e N N' L L' z := hcE
  have hQ : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α ∈ Qbar := by
    intro α
    have := GlobalTheory.ThLoc.algTAll D cc δ B χ hc hδ hχ N N' L L' hA 0 ⟨1, one_pos, by simpa using zero_mem _⟩ α
    have hU : U D B.tor 0 (B.eNat χ N N' L L') = B.eNat χ N N' L L' := by
      funext z; simp [U, Hf]
    rwa [hU] at this
  have ht : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α = c * Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α := fun α => by
    rw [hE, GlobalTheory.ProdThetaConj.taylor_const_mul e1.1]
  obtain ⟨α, hα⟩ : ∃ α, Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α ≠ 0 := by
    by_contra h
    push_neg at h
    apply e2
    funext z
    rw [← GlobalTheory.ProdThetaConj.tsum_taylor_mono D e1.1 z]
    simp [h]
  have hMQ : ∀ x ∈ M, x ∈ Qbar := fun x hx => mem_algebraicClosure_iff.2
    (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : M)))
  have hcQ : c ∈ Qbar := by
    have : c = Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α / Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α := by rw [ht, mul_div_cancel_right₀ _ hα]
    rw [this]
    exact div_mem (hQ α) (hMQ _ (hC α))
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {c}) :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.1 hcQ).isIntegral
  refine ⟨M ⊔ IntermediateField.adjoin ℚ {c}, IntermediateField.finiteDimensional_sup _ _, fun β => ?_⟩
  rw [ht]
  exact mul_mem ((le_sup_right : IntermediateField.adjoin ℚ {c} ≤ _) (IntermediateField.subset_adjoin ℚ {c} (Set.mem_singleton _)))
    ((le_sup_left : M ≤ _) (hC β))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNormBoundAbsoluteConstant
section
noncomputable section
namespace GlobalTheory.ColNorms.FamilyBound
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity GlobalTheory.ColNorms

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem genusOne_meanSquare_forms_agree (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : StandardLatticesGL3.nrm1Sq Λ G = GL3Theta.normSq1 Λ G :=
  (GlobalTheory.Glob.normSq1_eq_nrm1Sq Λ G).symm

theorem conj_normSq (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ) (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ))
    {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : admitted D N N' L L') (M : IntermediateField ℚ ℂ) (hD : DataIn D (tor0 D cc δ) M)
    (hcoef : CoefIn D (B.eNat χ N N' L L') M) (ρ : M →ₐ[ℚ] ℂ) {t : ℂ}
    (hT : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) :
    normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L') (fnConj D M ρ (B.eNat χ N N' L L')) =
      GL3Theta.normSq1 (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t) ^ (fF D * N * N') := by
  rw [(GlobalTheory.ConjNorm.useNorm_all D cc δ hc _ B.t0 N N' L L' (StandardLatticesGL3.admissible_self_dual_even hA).1 (StandardLatticesGL3.admissible_self_dual_even hA).2.1 (StandardLatticesGL3.admissible_self_dual_even hA).2.2 _
    (ht _ B.t0 N N' L L' hA) M ρ hD hcoef t hT).1, genusOne_meanSquare_forms_agree]

theorem conj_indep (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ) (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ)) :
    ThetaNormConjugateIndependent D (tor0 D cc δ) (B.eNat χ) := by
  intro N N' L₁ L₁' L₂ L₂' a₁ a₂ M _ hD c₁ c₂ ρ
  have : NumberField M := NumberField.mk
  obtain ⟨t, hT⟩ := GlobalTheory.Glob.exists_isThetaZero hc hD ρ
  rw [conj_normSq B χ hc ht a₁ M hD c₁ ρ hT, conj_normSq B χ hc ht a₂ M hD c₂ ρ hT]

theorem mean_le_of {C : ℝ} (hC : GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D) (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ)
    (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ)) : ThetaMeanBound D (tor0 D cc δ) C (B.eNat χ) := by
  intro Lsc hL N N' L L' hA M _ hD hcoef
  have : NumberField M := NumberField.mk
  have hex : ∀ ρ : M →ₐ[ℚ] ℂ, ∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t := fun ρ => GlobalTheory.Glob.exists_isThetaZero hc hD ρ
  choose t hT using hex
  have hm := hC cc δ M t ⟨hc.1, hc.2, hD, hT⟩ Lsc hL
  have key : meanLogNormSq D (tor0 D cc δ) L L' M (B.eNat χ N N' L L') =
      ((fF D * N * N' : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog M (lamOf D cc δ) t := by
    unfold meanLogNormSq GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.conjNormSq
    simp_rw [fun ρ => conj_normSq B χ hc ht hA M hD hcoef ρ (hT ρ), Real.log_pow]
    rw [← Finset.mul_sum, mul_div_assoc]
    rfl
  rw [key]
  calc ((fF D * N * N' : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog M (lamOf D cc δ) t
      ≤ ((fF D * N * N' : ℕ) : ℝ) * (C * Lsc) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = C * (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc := by push_cast; ring

theorem familyNorms_of (hT : FamilyTie) (hM : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D) : FamilyNorms := by
  obtain ⟨C, -, hC⟩ := hM
  refine ⟨C, fun D cc δ B χ h1 h2 hcc hδ hχ hY => ?_⟩
  have ht := hT D cc δ B χ h1 h2 hcc hδ hχ hY
  have hc : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have h14 := theta_link_holds D cc hcc δ hδ B (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) χ hχ
  exact ⟨h14.1, mean_le_of (hC D) B χ hc ht, conj_indep B χ hc ht, h14.2⟩

theorem familyNorms : FamilyNorms := familyNorms_of GlobalTheory.T.normalisedFamily_eq_tensorPower_vacuum GlobalTheory.T.exists_thetaZeroMeanLogLeConstMul

end GlobalTheory.ColNorms.FamilyBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenSigmaStableUnitNeighborhood
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.IdeleCongr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intAE_mul {s t : FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hs : s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) (ht : t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : s * t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  first
  | exact @_root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem
  | exact _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem
  | (apply _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem ..)

theorem intAE_one : (1 : FiniteAdeleRing (𝓞 F) F ⊗[F] E) ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  refine AddSubgroup.subset_closure ⟨1, fun v => ?_, 1, ?_⟩
  · rw [map_one]; exact one_mem _
  · rw [Algebra.TensorProduct.one_def]; simp

theorem intAE_nat (m : ℕ) : (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  rw [← nsmul_one]; exact nsmul_mem intAE_one m

theorem sigR_intAE (σ : E →ₐ[F] E) {z : FiniteAdeleRing (𝓞 F) F ⊗[F] E} (h : z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, RingOfIntegers.mapRingHom (σ : E →+* E) x, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem finPart_cA (σ : E →ₐ[F] E) (y : AdeleRing (𝓞 F) F ⊗[F] E) : HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.cA σ y) = HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ (HeckeCharacterZeroLocus.ThmBIn.finPart F E y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

end GlobalTheory.IdeleCongr

namespace GlobalTheory.IdeleCongr

theorem exists_open_congruence_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (m : ℕ), 0 < m → ∃ U : Subgroup (AdeleRing (𝓞 F) F ⊗[F] E)ˣ, IsOpen (U : Set (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) ∧
      (∀ x ∈ U, Units.map (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ).toRingHom.toMonoidHom x ∈ U) ∧
      ∀ x ∈ U, ∃ s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E,
        HeckeCharacterZeroLocus.ThmBIn.finPart F E (x : AdeleRing (𝓞 F) F ⊗[F] E) = 1 + (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * s := by
  intro F E _ _ _ _ _ σ m hm
  haveI : IsModuleTopology (HeckeCharacterZeroLocus.ThmBIn.AF F) (HeckeCharacterZeroLocus.ThmBIn.AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (HeckeCharacterZeroLocus.ThmBIn.AE F E) := IsModuleTopology.isTopologicalRing (HeckeCharacterZeroLocus.ThmBIn.AF F) _
  obtain ⟨Φ, hΦc, -, hint⟩ := GlobalTheory.HeckeInhabitant.exists_fin (F := F) (E := E)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  let c : FiniteAdeleRing (𝓞 F) F ⊗[F] E := HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹)
  have hmc : (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * c = 1 := by
    have : (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) = HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)) := by
      rw [map_natCast, map_natCast]
    rw [this, ← map_mul, ← map_mul, mul_inv_cancel₀ hm0, map_one, map_one]
  let C : AdeleRing (𝓞 F) F ⊗[F] E → Prop := fun y =>
    (HeckeCharacterZeroLocus.ThmBIn.finPart F E y - 1) * c ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E
  have hdec : ∀ z : FiniteAdeleRing (𝓞 F) F ⊗[F] E, z = 1 + m * ((z - 1) * c) := fun z => by
    linear_combination (1 - z) * hmc
  have hint' : ∀ y, C y → HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := fun y hy => by
    rw [hdec (HeckeCharacterZeroLocus.ThmBIn.finPart F E y)]
    exact add_mem intAE_one (intAE_mul (intAE_nat m) hy)
  have hCmul : ∀ y z, C y → C z → C (y * z) := fun y z hy hz => by
    have e : (HeckeCharacterZeroLocus.ThmBIn.finPart F E (y * z) - 1) * c = HeckeCharacterZeroLocus.ThmBIn.finPart F E y * ((HeckeCharacterZeroLocus.ThmBIn.finPart F E z - 1) * c)
        + (HeckeCharacterZeroLocus.ThmBIn.finPart F E y - 1) * c := by
      rw [map_mul]; ring
    show _ ∈ _
    rw [e]
    exact add_mem (intAE_mul (hint' y hy) hz) hy
  have hC1 : C 1 := by
    show _ ∈ _
    rw [map_one, sub_self, zero_mul]
    exact zero_mem _
  let U : Subgroup (AdeleRing (𝓞 F) F ⊗[F] E)ˣ :=
    { carrier := {x | C x ∧ C ((x⁻¹ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) : AdeleRing (𝓞 F) F ⊗[F] E)}
      one_mem' := ⟨by rw [Units.val_one]; exact hC1, by rw [inv_one, Units.val_one]; exact hC1⟩
      mul_mem' := fun {x y} hx hy => ⟨by rw [Units.val_mul]; exact hCmul _ _ hx.1 hy.1,
        by rw [mul_inv_rev, Units.val_mul]; exact hCmul _ _ hy.2 hx.2⟩
      inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩ }
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 E) E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hcont : Continuous fun y : AdeleRing (𝓞 F) F ⊗[F] E => (y - 1) * HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹ :=
    (continuous_id.sub continuous_const).mul continuous_const
  have hCo : IsOpen {y | C y} := by
    have h1 : IsOpen {y : AdeleRing (𝓞 F) F ⊗[F] E |
        ∀ P, Valued.v (Φ ((y - 1) * HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹) P) ≤ 1} := (hO.preimage hΦc).preimage hcont
    convert h1 using 1
    ext y
    simp only [Set.mem_setOf_eq]
    rw [← hint, map_mul, map_sub, map_one]
  have hσ : ∀ y, (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ) y
      = HeckeCharacterZeroLocus.ThmBIn.cA σ y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => rfl
  have hsc : HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ c = c := by
    change HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ (HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹)) = _
    rw [← finPart_cA, GlobalTheory.HeckeInhabitant.cA_inc, map_inv₀, map_natCast]
  have hCσ : ∀ y, C y → C (HeckeCharacterZeroLocus.ThmBIn.cA σ y) := fun y hy => by
    show _ ∈ _
    rw [finPart_cA, ← hsc, ← map_one (HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ), ← map_sub, ← map_mul]
    exact sigR_intAE σ hy
  refine ⟨U, ?_, fun x hx => ⟨?_, ?_⟩, fun x hx => ⟨_, hx.1, hdec _⟩⟩
  · exact (hCo.preimage Units.continuous_val).inter (hCo.preimage Units.continuous_coe_inv)
  · change C ((Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ) (x : AdeleRing (𝓞 F) F ⊗[F] E))
    rw [hσ]; exact hCσ _ hx.1
  · rw [← map_inv]
    change C ((Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ) ((x⁻¹ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) : AdeleRing (𝓞 F) F ⊗[F] E))
    rw [hσ]; exact hCσ _ hx.2

end GlobalTheory.IdeleCongr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaValuesAtNegIntUnique
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ZetaValUnique

theorem classZeta_eqOn {E : Type} [Field E] [NumberField E] {C : ClassGroup (GlobalTheory.CMVal.OF E)} {Z Z' : ℂ → ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZeta C Z) (h' : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZeta C Z') :
    Set.EqOn Z Z' {1}ᶜ := by
  have ho : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  refine (h.1.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (h'.1.analyticOnNhd ho) hc
    (z₀ := 2) (by norm_num) ?_
  have hh : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hh.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
  exact (h.2 s hs).unique (h'.2 s hs)

theorem classZetaVals_unique : ∀ {E : Type} [Field E] [NumberField E] {k : ℕ}, 2 ≤ k →
    ∀ {z z' : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ}, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z →
      GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z' → z = z' := by
  intro E _ _ k hk z z' hz hz'
  funext C
  obtain ⟨Z, hZ, hZv⟩ := hz C
  obtain ⟨Z', hZ', hZv'⟩ := hz' C
  have hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_self, Nat.cast_eq_zero]
    omega
  have := classZeta_eqOn hZ hZ' hne
  rw [hZv, hZv'] at this
  exact_mod_cast this

end GlobalTheory.ZetaValUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationTowerCompatible
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BCChar

open scoped GroundTheory.Global.AdicLiesOver

theorem adicCompletionMap_comp_adicCompletionMap {K M L : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M))
    (w : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]
    [w.asIdeal.LiesOver v.asIdeal] :
    (GroundTheory.Global.adicCompletionMap u w).comp (GroundTheory.Global.adicCompletionMap v u) =
      GroundTheory.Global.adicCompletionMap v w := by
  have h := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) v).equalizer
    ((GroundTheory.Global.continuous_adicCompletionMap u w).comp
      (GroundTheory.Global.continuous_adicCompletionMap v u))
    (GroundTheory.Global.continuous_adicCompletionMap v w) (funext fun x ↦ ?_)
  · exact RingHom.ext (congrFun h)
  · simp only [Function.comp_apply]
    rw [GroundTheory.Global.adicCompletionMap_algebraMap, GroundTheory.Global.adicCompletionMap_algebraMap,
      GroundTheory.Global.adicCompletionMap_algebraMap, ← IsScalarTower.algebraMap_apply K M L]

theorem normU_comp_normU {K M L : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M))
    (w : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]
    [w.asIdeal.LiesOver v.asIdeal] :
    (normU v u).comp (normU u w) = normU v w := by
  haveI : IsScalarTower (v.adicCompletion K) (u.adicCompletion M) (w.adicCompletion L) :=
    .of_algebraMap_eq' (adicCompletionMap_comp_adicCompletionMap v u w).symm
  refine MonoidHom.ext fun x => Units.ext ?_
  simp only [normU, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  exact Algebra.norm_norm (R := v.adicCompletion K) (S := u.adicCompletion M) (a := (x : w.adicCompletion L))

end GlobalTheory.BCChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneFgLatticeEqFractionalIdealSmulVector
section
open NumberField

namespace GlobalTheory

theorem latRank_one_eq_ideal_smul {K : Type} [Field K] [NumberField K] {m : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) :
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := by
  intro hr hfg
  unfold ReciprocityTheory.GeometryOfNumbersTheory.latRank at hr
  obtain ⟨w, hw0, hw⟩ := (finrank_eq_one_iff').mp hr
  have hvW : (w : Fin m → K) ≠ 0 := by
    intro h; exact hw0 (Subtype.ext h)
  have hmul : ∀ e ∈ ell, ∃ β : K, e = β • (w : Fin m → K) := by
    intro e he
    obtain ⟨c, hc⟩ := hw ⟨e, Submodule.subset_span he⟩
    refine ⟨c, ?_⟩
    have := congrArg Subtype.val hc
    exact this.symm
  let f : K →ₗ[𝓞 K] (Fin m → K) :=
    { toFun := fun β => β • (w : Fin m → K)
      map_add' := fun a b => add_smul a b _
      map_smul' := fun r b => by
        simp only [RingHom.id_apply]
        exact smul_assoc r b _ }
  have hf : ∀ β, f β = β • (w : Fin m → K) := fun _ => rfl
  have finj : Function.Injective f := by
    intro a b hab
    rw [hf, hf] at hab
    have : (a - b) • (w : Fin m → K) = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hvW
  refine ⟨w, hvW, ell.comap f, ?_, ?_, ?_⟩
  · apply Submodule.fg_of_fg_map_injective f finj
    have : (ell.comap f).map f = ell := by
      apply le_antisymm (Submodule.map_comap_le _ _)
      intro e he
      obtain ⟨β, rfl⟩ := hmul e he
      exact ⟨β, he, rfl⟩
    rw [this]; exact hfg
  · intro hbot
    apply hw0
    have hell : ell = ⊥ := by
      rw [eq_bot_iff]; intro e he
      obtain ⟨β, rfl⟩ := hmul e he
      have : β ∈ ell.comap f := he
      rw [hbot, Submodule.mem_bot] at this
      simp [this]
    have hW : Submodule.span K (ell : Set (Fin m → K)) = ⊥ := by simp [hell]
    have h0 : ∀ x ∈ Submodule.span K (ell : Set (Fin m → K)), x = 0 := by
      rw [hW]; intro x hx; exact (Submodule.mem_bot K).mp hx
    exact Subtype.ext (h0 _ w.2)
  · intro e
    constructor
    · intro he
      obtain ⟨β, rfl⟩ := hmul e he
      exact ⟨β, he, rfl⟩
    · rintro ⟨β, hβ, rfl⟩
      exact hβ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionLeviGLIsotropicFrameStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_leviGL_isotropicFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (W : Set (GAd σ J)) (B : ℝ), IsCompact W ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∃ γ ∈ ratPts σ J, γ ∈ parFlag σ J C (fun _ => 0) ∧ ∃ q ∈ fixG σ J C, ∃ l : Fin j → ℤ, ∃ w ∈ W, γ * p = q * lv (tor F E l) * w ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ := by
  first | exact @GlobalTheory.SphEis.reduce_levi | exact GlobalTheory.SphEis.reduce_levi | (intros; apply GlobalTheory.SphEis.reduce_levi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarEqOfWeilPairingEqPrincipalCMTripleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_eq_of_weilPairing_eq_principalCMTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A : PAT H (Sp (𝓞 K))), ρ ^ 2 = -(H.d : 𝓞 K) →
    HasType H A.t.act ρ 1 0 → ∀ s s' : 𝓞 E,
    WeilEq A.t.PP.L (A.t.act.act s) (𝟙 _) A.t.PP.L (A.t.act.act s') (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    s = s' := by
  first | exact @GlobalTheory.TwistScalarUnique.eq_of_weilEq | exact GlobalTheory.TwistScalarUnique.eq_of_weilEq | (intros; apply GlobalTheory.TwistScalarUnique.eq_of_weilEq <;> assumption)
end

