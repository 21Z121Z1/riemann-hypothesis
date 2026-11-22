import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEntireFactorIsThetaFunctionStandard
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLawOF

theorem theta_of_vacuum_real : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (colLat frS : Set _) (colLat frT : Set _) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank) := by
  intro D ψ θ S T frS frT hS hT δ hC hδ f hf Φ hΦd hΦ
  have hψ := hf.1
  have hθ := hf.2.inf
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hSd := GlobalTheory.FunObj.VecEx.isSelfDualC_colLat S frS hS
  have hTd := GlobalTheory.FunObj.VecEx.isSelfDualC_colLat T frT hT
  obtain ⟨-, -, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T (colLat frS) (colLat frT) hψ hSd hTd
  refine ⟨hΦd.comp ((differentiable_id).const_smul δ⁻¹), ?_⟩
  intro x hx Y
  obtain ⟨v, hv, rfl⟩ := GlobalTheory.T.exists_rational_frameCoords_of_mem_torusLattice S T frS frT hS hT δ x hx
  have hv' : GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (colLat frS : Set _) (colLat frT : Set _) (fun _ => True) := by
    rw [AddMonoidHom.map_neg]; exact neg_mem hv
  obtain ⟨ε, -, hε⟩ := h3 f hf.2.lat _ hv'
  have hsign := GlobalTheory.T.latticePoint_sign_eq_thetaLaw_semicharacter ψ S T frS frT hS hT hψ δ hδ v hv ε (fun g hg => hε g hg)
  have hlaw := GlobalTheory.VacUnique.apply_add_infRat hch hψ hf.2.theta v (hε f hf.2.lat)
  set X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b with hX
  set Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := δ⁻¹ • Y with hZ
  have hZY : Y = δ • Z := by rw [hZ, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  set z : GlobalTheory.FockCompare.RW T S := fun τ => GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ with hz
  have hzτ : ∀ τ, (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) :=
    fun τ => coord_back frS frT Z τ
  have hz1 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) = Z := by
    rw [zCo_iota hch]; funext τ; exact coord_back frS frT Z τ
  have hz2 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T v)) = Z + X := by
    rw [zCo_iota hch]; funext τ
    show (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (z τ) + Matrix.of (GlobalTheory.VacUnique.infRat S T v τ)) * GlobalTheory.FockPos.frAt frS τ = Z τ + X τ
    rw [Matrix.mul_add, Matrix.add_mul, hzτ τ]
    rfl
  have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T v) z = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re := by
    rw [omO_frame frS frT hS hT]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hzτ τ]
    rfl
  have hl := hlaw z
  rw [hΦ _ (hch.real_iota T S _), hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, GlobalTheory.FockPos.gaussO, hz1, hz2, hom, hsign] at hl

  simp only [Formalism.MainNotions.TaylorLogMetric.U]
  have e1 : δ⁻¹ • (Y + δ • X) = Z + X := by rw [smul_add, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [e1, hZY, torusHermitianForm_scaled_coordinate_eq hδ, torusHermitianForm_scaled_coordinate_eq hδ]
  have hZZ : δ⁻¹ • δ • Z = Z := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [hZZ]
  set a := Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) with ha
  have kE : Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) =
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := entry (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
    push_cast at h ⊢
    linear_combination h
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)))
  rw [← kE]
  calc _ = a * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) *
        (Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) * Φ (Z + X)) := by
        rw [kE]; ring
    _ = _ := by
        rw [hl]
        have := al_mul_self (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X)
        rw [← ha] at this
        linear_combination (Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) * Φ Z) * this

end GlobalTheory.ThetaLawOF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIrreducibleIsAdmissible
section
open Formalism.MainNotions.S

namespace GlobalTheory.IrrAdm

theorem isIrrAdm_of_irred : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → GlobalTheory.RealInd.IsIrrAdm ε π := by
  intro n ε H _ _ _ _ π hU hI
  have hK : ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖π k v‖ = ‖v‖ := fun k hk v =>
    hU.2.1 k (GlobalTheory.GKModule.mem_UJset_of_mem_Kset hk) v
  refine ⟨inferInstance, ⟨hU.1, hU.2.2, hK, ?_⟩, hI⟩
  intro Λ
  classical
  by_cases hne : ∃ S₀ : Submodule ℂ H, S₀ ≤ ⊤ ∧ IsKTypeOf ε π Λ S₀
  · obtain ⟨S₀, -, hS₀⟩ := hne
    haveI : FiniteDimensional ℂ S₀ := hS₀.1
    have hY := (GlobalTheory.T.irreducible_K_stable_finite_subspace n ε H π hU hI).1 S₀ hS₀.1 hS₀.2.1
    let b := Module.finBasis ℂ S₀
    choose Y hYf hvY hYB using fun i => hY (b i) (b i).2
    haveI : ∀ i, FiniteDimensional ℂ (Y i) := hYf
    refine Submodule.finiteDimensional_of_le (sSup_le fun S hS => ?_) (S₂ := ⨆ i, Y i)
    obtain ⟨B, hB, rfl⟩ := (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H π hU.1 hU.2.2 hK).2 Λ S₀ S hS₀ hS.2
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    have hx' : (⟨x, hx⟩ : S₀) ∈ Submodule.span ℂ (Set.range b) := b.span_eq ▸ Submodule.mem_top
    have h2 := Submodule.apply_mem_span_image_of_mem_span S₀.subtype hx'
    rw [← Set.range_comp] at h2
    refine (Submodule.span_le.2 ?_) h2
    rintro _ ⟨i, rfl⟩
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, Function.comp_apply, Submodule.subtype_apply,
      SetLike.mem_coe]
    exact Submodule.mem_iSup_of_mem i (hYB i B hB _ (hvY i))
  · have : {S : Submodule ℂ H | S ≤ ⊤ ∧ IsKTypeOf ε π Λ S} = ∅ :=
      Set.eq_empty_of_forall_notMem fun S hS => hne ⟨S, hS⟩
    rw [this, sSup_empty]
    infer_instance

end GlobalTheory.IrrAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalSignEqOneOfIntegralSeparableReductioStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryLocalSign_eq_one_of_integral_separable_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    γ ∈ KL n w → ∀ Q₁ : (w.adicCompletion E)[X],
    Q₁ ∣ P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → kapSign n w Q₁ γ.1 = 1 := by
  first | exact @GlobalTheory.BCT.kapSign_eq_one_of_integral | exact GlobalTheory.BCT.kapSign_eq_one_of_integral | (intros; apply GlobalTheory.BCT.kapSign_eq_one_of_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankOneSphericalIntegrandDiagonalTorusFacStatement
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRankOne_sphericalIntegrand_diagonal_torus_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂˣ) (φ : GU σ n → ℂ), IsSphericalU q (fun i => (α i : ℂ)) φ →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → ∀ w x : GU σ n,
      φ (y⁻¹ * t * w * x) * (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
        chiDeltaU q (fun i => (actU k α i : ℂ)) t * φ (y⁻¹ * w * x) := by
  first | exact @GlobalTheory.WeylCell.U21TorusFactor.torus_factor | exact GlobalTheory.WeylCell.U21TorusFactor.torus_factor | (intros; apply GlobalTheory.WeylCell.U21TorusFactor.torus_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStringForcesLongPart
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem unitary_string_forces_long_part : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (c : ℕ) (d : Fin c → ℕ)
    (S : Fin c → Multiset ℂˣ) (T : Multiset ℂˣ) (t : ℕ) (ν : ℂ),
  1 ≤ t → (∀ i, ∀ s ∈ S i, ‖(s : ℂ)‖ = 1) → ‖ν‖ = 1 →
  ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
    T.map (fun z => (z : ℂ)) →
  (Multiset.range t).map (fun c : ℕ => ν * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - c)) ≤
    T.map (fun z => (z : ℂ)) →
  ∃ i, t ≤ d i := by
  intro E _ _ w c d S T t ν ht hS hν hsum hle
  have hN1 : 1 < Ideal.absNorm w.asIdeal := by
    have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
    have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
    omega
  set N := Ideal.absNorm w.asIdeal with hN
  have hmem : ν * ((N : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) ∈ T.map (fun z => (z : ℂ)) :=
    Multiset.mem_of_le hle (Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (by omega), rfl⟩)
  rw [← hsum] at hmem
  obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hmem
  obtain ⟨k, -, hk⟩ := Multiset.mem_sum.1 hi
  obtain ⟨s, hs, hsk⟩ := Multiset.mem_map.1 hk
  have hs1 : ‖s‖ = 1 := by
    simp only [Multiset.bind_def, Multiset.pure_def, Multiset.mem_bind, Multiset.mem_singleton] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    exact hS i u hu
  have hNpos : 0 < N := by omega
  have hn := congrArg (fun z : ℂ => ‖z‖) hsk
  simp only [norm_mul, hs1, hν, one_mul, Complex.norm_natCast_cpow_of_pos hNpos] at hn
  have hre : ((((d i : ℂ) - 1) / 2 - ((k : ℕ) : ℂ))).re = ((d i : ℝ) - 1) / 2 - (k : ℕ) := by simp
  have hre2 : ((((t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))).re = ((t : ℝ) - 1) / 2 := by simp
  rw [hre, hre2] at hn
  have hN1' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hle' := (Real.rpow_le_rpow_left_iff hN1').1 hn.ge
  have hk' : ((k : ℕ) : ℝ) ≥ 0 := by positivity
  refine ⟨i, ?_⟩
  have : (t : ℝ) ≤ d i := by linarith
  exact_mod_cast this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumRealRestrictionGaussianMulThetaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_real_restriction_gaussian_mul_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) ∧ θ ≠ 0 ∧ ∀ w : WO (G.pS (.top t j)) (G.pT (.top t j)), w.map (finPart D) = 0 → f w = Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ)) * θ (δ • (fun τ => (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ)) := by
  first | exact @GlobalTheory.VacRealForm.vacuum_real_form | exact GlobalTheory.VacRealForm.vacuum_real_form | (intros; apply GlobalTheory.VacRealForm.vacuum_real_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleTwistOfGeneratedAndVeryAmple
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.GenTwist
variable {X : Scheme.{0}} {M H : LB X}

theorem tw_one_g (p q : M.ι) (k l : H.ι) :
    (((tw M H 1).g (p, k) (q, l) : Γ(X, (tw M H 1).U (p, k) ⊓ (tw M H 1).U (q, l))ˣ) :
      Γ(X, (tw M H 1).U (p, k) ⊓ (tw M H 1).U (q, l))) =
    rs X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q) (M.g p q) *
    rs X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l) (H.g k l) := by
  have e : (tw M H 1).g (p, k) (q, l) = (res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q) (M.g p q) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l) (H.g k l ^ (-(1 : ℤ))))⁻¹ :
        Γ(X, M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l))ˣ) := rfl
  rw [e, map_zpow, zpow_neg, zpow_one, inv_inv]
  rfl

def prodSec (u : LB.Sec M) (s : LB.Sec H) : LB.Sec (tw M H 1) where
  f := fun pk => rs X (inf_le_left : M.U pk.1 ⊓ H.U pk.2 ≤ M.U pk.1) (u.f pk.1) *
    rs X (inf_le_right : M.U pk.1 ⊓ H.U pk.2 ≤ H.U pk.2) (s.f pk.2)
  compat := fun pk ql => by
    have key : ∀ (p q : M.ι) (k l : H.ι),
        rs X (inf_le_left : M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ H.U k)
          (rs X inf_le_left (u.f p) * rs X inf_le_right (s.f k)) =
        (rs X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q) (M.g p q) *
         rs X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l) (H.g k l)) *
        rs X (inf_le_right : M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U q ⊓ H.U l)
          (rs X inf_le_left (u.f q) * rs X inf_le_right (s.f l)) := by
      intro p q k l
      have hu := congrArg (rs X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q)) (u.compat p q)
      have hs := congrArg (rs X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l)) (s.compat k l)
      simp only [rs_rs, map_mul] at hu hs ⊢
      rw [hu, hs]
      ring
    exact (key pk.1 ql.1 pk.2 ql.2).trans (congrArg (· * _) (tw_one_g (M := M) (H := H) pk.1 ql.1 pk.2 ql.2).symm)

theorem nonzeroLocus_prodSec (u : LB.Sec M) (s : LB.Sec H) :
    nonzeroLocus (prodSec u s) = nonzeroLocus u ⊓ nonzeroLocus s := by
  have hb : ∀ (p : M.ι) (k : H.ι), X.basicOpen ((prodSec u s).f ((p, k) : (tw M H 1).ι)) =
      X.basicOpen (u.f p) ⊓ X.basicOpen (s.f k) := by
    intro p k
    change X.basicOpen (rs X (inf_le_left : M.U p ⊓ H.U k ≤ M.U p) (u.f p) *
      rs X (inf_le_right : M.U p ⊓ H.U k ≤ H.U k) (s.f k)) = _
    rw [Scheme.basicOpen_mul]
    erw [Scheme.basicOpen_res, Scheme.basicOpen_res]
    refine le_antisymm (inf_le_inf inf_le_right inf_le_right)
      (le_inf (le_inf (le_inf ((inf_le_left).trans (X.basicOpen_le _)) ((inf_le_right).trans (X.basicOpen_le _)))
        inf_le_left) (le_inf (le_inf ((inf_le_left).trans (X.basicOpen_le _))
          ((inf_le_right).trans (X.basicOpen_le _))) inf_le_right))
  refine le_antisymm (iSup_le fun pk => ?_) ?_
  · exact (hb pk.1 pk.2).le.trans (inf_le_inf (le_iSup (fun k => X.basicOpen (u.f k)) pk.1)
      (le_iSup (fun k => X.basicOpen (s.f k)) pk.2))
  · change (⨆ p, X.basicOpen (u.f p)) ⊓ (⨆ k, X.basicOpen (s.f k)) ≤ _
    rw [iSup_inf_eq]
    refine iSup_le fun p => ?_
    rw [inf_iSup_eq]
    exact iSup_le fun k => (hb p k).ge.trans
      (le_iSup (fun pk => X.basicOpen ((prodSec u s).f pk)) ((p, k) : (tw M H 1).ι))

theorem eval₂Hom_ratios_surjective (hM : M.IsLB) {m : ℕ} (u : Fin (m + 1) → LB.Sec M)
    (hu : ⨆ b, nonzeroLocus (u b) = ⊤) (a : Fin (m + 1)) {D N : X.Opens} (hD : IsAffineOpen D)
    (hN : N = nonzeroLocus (u a) ⊓ D) (ρ : Fin (m + 1) → Γ(X, N))
    (hρ : ∀ c q, rs X (inf_le_right : N ⊓ M.U q ≤ M.U q) ((u c).f q) =
      rs X (inf_le_left : N ⊓ M.U q ≤ N) (ρ c) * rs X (inf_le_right : N ⊓ M.U q ≤ M.U q) ((u a).f q)) :
    Function.Surjective (MvPolynomial.eval₂Hom (rs X (hN.le.trans inf_le_right : N ≤ D)) ρ) := by
  subst hN
  have hVD : nonzeroLocus (u a) ⊓ D ≤ D := inf_le_right
  have hV : IsAffineOpen (nonzeroLocus (u a) ⊓ D) := GlobalTheory.isAffineOpen_nonzeroLocus_inf hM (u a) hD
  letI : Algebra Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) := (rs X hVD).toAlgebra
  intro x
  suffices hx : x ∈ Algebra.adjoin Γ(X, D) (Set.range ρ) by
    rw [Algebra.adjoin_range_eq_range_aeval] at hx
    obtain ⟨P, rfl⟩ := hx
    exact ⟨P, rfl⟩
  let T : Set Γ(X, D) := {t | ∃ b p, X.basicOpen t ≤ X.basicOpen ((u b).f p)}
  have hT : Ideal.span T = ⊤ := by
    rw [← hD.self_le_iSup_basicOpen_iff]
    intro y hy
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu.ge (Set.mem_univ y))
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 hb
    obtain ⟨t, ht, hyt⟩ := hD.exists_basicOpen_le ⟨y, hp⟩ hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨t, b, p, ht⟩, hyt⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (Algebra.adjoin Γ(X, D) (Set.range ρ)).toSubmodule T hT x ?_
  rintro ⟨t, b, p, ht⟩
  have hWD : X.basicOpen t ≤ D := X.basicOpen_le t
  have hWp : X.basicOpen t ≤ M.U p := ht.trans (X.basicOpen_le _)
  have hW : IsAffineOpen (X.basicOpen t) := hD.basicOpen t
  let α : Γ(X, X.basicOpen t) := rs X hWp ((u a).f p)
  let β : Γ(X, X.basicOpen t) := rs X hWp ((u b).f p)
  have hβ : IsUnit β := by
    have h0 : IsUnit (rs X (X.basicOpen_le ((u b).f p)) ((u b).f p)) :=
      X.toRingedSpace.isUnit_res_basicOpen _
    have h1 := h0.map (rs X ht)
    rwa [rs_rs] at h1
  have hW'W : X.basicOpen α ≤ X.basicOpen t := X.basicOpen_le α
  have hW'eq : X.basicOpen α = X.basicOpen t ⊓ X.basicOpen ((u a).f p) := Scheme.basicOpen_res _ _ _
  have hW'V : X.basicOpen α ≤ nonzeroLocus (u a) ⊓ D := by
    rw [hW'eq]
    exact le_inf (inf_le_right.trans (GlobalTheory.basicOpen_le_nonzeroLocus _ _)) (inf_le_left.trans hWD)
  have hOW' : X.basicOpen (rs X hVD t) ≤ X.basicOpen α := by
    have e0 : X.basicOpen (rs X hVD t) = (nonzeroLocus (u a) ⊓ D) ⊓ X.basicOpen t :=
      Scheme.basicOpen_res _ _ _
    rw [e0, hW'eq]
    refine le_inf inf_le_right ?_
    rw [← GlobalTheory.nonzeroLocus_inf_chart]
    exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans hWp)
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X (X.basicOpen t)
    hW.isCompact hW.isQuasiSeparated α (rs X hW'V x)
  obtain ⟨k, z, hz⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X D
    hD.isCompact hD.isQuasiSeparated t y
  obtain ⟨k', z', hz'⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X D
    hD.isCompact hD.isQuasiSeparated t ((hβ.unit⁻¹ : Γ(X, X.basicOpen t)ˣ) : Γ(X, X.basicOpen t))
  change rs X hW'W y = (rs X hW'W α) ^ n * rs X hW'V x at hy
  change rs X hWD z = (rs X hWD t) ^ k * y at hz
  change rs X hWD z' = (rs X hWD t) ^ k' * ((hβ.unit⁻¹ : Γ(X, X.basicOpen t)ˣ) : Γ(X, X.basicOpen t)) at hz'
  have hr := congrArg (rs X (le_inf hW'V (hW'W.trans hWp) : X.basicOpen α ≤ (nonzeroLocus (u a) ⊓ D) ⊓ M.U p))
    (hρ b p)
  simp only [map_mul, rs_rs] at hr
  set I : Γ(X, X.basicOpen t) := ((hβ.unit⁻¹ : Γ(X, X.basicOpen t)ˣ) : Γ(X, X.basicOpen t)) with hIdef
  have hIβ : I * β = 1 := hβ.val_inv_mul
  have hz1 := congrArg (rs X hW'W) hz
  have hz1' := congrArg (rs X hW'W) hz'
  have hIβ' := congrArg (rs X hW'W) hIβ
  simp only [map_mul, map_pow, map_one, rs_rs] at hz1 hz1' hIβ'
  have hα : rs X hW'W α = rs X (hW'W.trans hWp) ((u a).f p) := rs_rs _ _ _
  have hβ' : rs X hW'W β = rs X (hW'W.trans hWp) ((u b).f p) := rs_rs _ _ _
  let c : Γ(X, D) := z * z' ^ n
  have e1 : rs X hW'V ((rs X hVD t) ^ (k + n * k') * x - rs X hVD c * ρ b ^ n) = 0 := by
    simp only [c, map_sub, map_mul, map_pow, rs_rs]
    rw [hz1, hz1', hy]
    have hARI : rs X hW'W α * rs X hW'V (ρ b) * rs X hW'W I = 1 := by
      rw [hα, mul_comm (rs X _ ((u a).f p)), ← hr, ← hβ', mul_comm, hIβ']
    calc _ = rs X (hW'W.trans hWD) t ^ (k + n * k') * rs X hW'V x -
          rs X (hW'W.trans hWD) t ^ (k + n * k') * rs X hW'V x *
            (rs X hW'W α * rs X hW'V (ρ b) * rs X hW'W I) ^ n := by ring
      _ = 0 := by rw [hARI, one_pow, mul_one, sub_self]
  obtain ⟨l, hl⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hV.isCompact
    ((rs X hVD t) ^ (k + n * k') * x - rs X hVD c * ρ b ^ n) (rs X hVD t) (by
      change rs X (X.basicOpen_le _) _ = 0
      rw [← rs_rs hW'V hOW', e1, map_zero])
  refine ⟨l + (k + n * k'), ?_⟩
  rw [Subalgebra.mem_toSubmodule, Algebra.smul_def]
  have e2 : algebraMap Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) (t ^ (l + (k + n * k'))) * x =
      algebraMap Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) (t ^ l * c) * ρ b ^ n := by
    change rs X hVD (t ^ (l + (k + n * k'))) * x = rs X hVD (t ^ l * c) * ρ b ^ n
    rw [mul_sub, sub_eq_zero] at hl
    rw [map_pow, map_mul, map_pow, pow_add, mul_assoc, hl, mul_assoc]
  change algebraMap Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) (t ^ (l + (k + n * k'))) * x ∈ _
  rw [e2]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self b)) _)

theorem veryAmpleBy_tw_of_generated : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H M : LB X) (n m : ℕ) (s : Fin (n + 1) → LB.Sec H) (u : Fin (m + 1) → LB.Sec M), H.IsLB → M.IsLB → VeryAmpleBy f H s → (⨆ a, nonzeroLocus (u a) = ⊤) → ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.tw M H 1)), VeryAmpleBy f (GlobalTheory.AbLaw.tw M H 1) s' := by
  intro R _ X f H M n m s u hH hM hs hu
  let e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1) :=
    (finCongr (by ring)).trans finProdFinEquiv.symm
  refine ⟨m * n + m + n, fun j => prodSec (u (e j).1) (s (e j).2), ?_, fun j => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ a, nonzeroLocus (u a) by rw [hu]; trivial)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (a, i), ?_⟩
    rw [nonzeroLocus_prodSec, e.apply_symm_apply]
    exact ⟨ha, hi⟩
  obtain ⟨aff, r, hr, sj⟩ := hs.2 (e j).2
  have loc := nonzeroLocus_prodSec (u (e j).1) (s (e j).2)
  have hNE := loc.le.trans inf_le_left
  have hND := loc.le.trans inf_le_right
  have o : r (e j).2 = 1 := Segre.ratio_self _ _ (hr _)
  choose ρ₀ hρ₀ using fun c => GlobalTheory.AmpleSpan.exists_isRatio (u c) (u (e j).1)
  have o' : ρ₀ (e j).1 = 1 := Segre.ratio_self _ _ (hρ₀ _)
  refine ⟨?_, fun b => rs X hNE (ρ₀ (e b).1) * rs X hND (r (e b).2), fun b kk => ?_, ?_⟩
  · rw [loc]
    exact GlobalTheory.isAffineOpen_nonzeroLocus_inf hM _ aff
  · have h1 : rs X (inf_le_right : nonzeroLocus (u (e j).1) ⊓ M.U kk.1 ≤ M.U kk.1) ((u (e b).1).f kk.1) =
        rs X inf_le_left (ρ₀ (e b).1) * rs X inf_le_right ((u (e j).1).f kk.1) := hρ₀ _ _
    have h2 := hr (e b).2 kk.2
    have hk1 : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
        nonzeroLocus (u (e j).1) ⊓ M.U kk.1 :=
      le_inf (inf_le_left.trans hNE) (inf_le_right.trans inf_le_left)
    have hk2 : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
        nonzeroLocus (s (e j).2) ⊓ H.U kk.2 :=
      le_inf (inf_le_left.trans hND) (inf_le_right.trans inf_le_right)
    replace h1 := congrArg (rs X hk1) h1
    replace h2 := congrArg (rs X hk2) h2
    simp only [map_mul, rs_rs] at h1 h2
    change rs X (inf_le_right : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
          M.U kk.1 ⊓ H.U kk.2)
        (rs X inf_le_left ((u (e b).1).f kk.1) * rs X inf_le_right ((s (e b).2).f kk.2)) =
      rs X (inf_le_left : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
          nonzeroLocus (prodSec (u (e j).1) (s (e j).2)))
        (rs X hNE (ρ₀ (e b).1) * rs X hND (r (e b).2)) *
      rs X (inf_le_right : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
          M.U kk.1 ⊓ H.U kk.2)
        (rs X inf_le_left ((u (e j).1).f kk.1) * rs X inf_le_right ((s (e j).2).f kk.2))
    simp only [map_mul, rs_rs]
    rw [h1, h2]
    ring
  · have hgen := eval₂Hom_ratios_surjective hM u hu (e j).1 aff loc (fun c => rs X hNE (ρ₀ c))
      (fun c q => by
        have h : rs X (inf_le_right : nonzeroLocus (u (e j).1) ⊓ M.U q ≤ M.U q) ((u c).f q) =
            rs X inf_le_left (ρ₀ c) * rs X inf_le_right ((u (e j).1).f q) := hρ₀ c q
        have h' := congrArg (rs X (le_inf (inf_le_left.trans hNE) inf_le_right :
          nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ M.U q ≤ nonzeroLocus (u (e j).1) ⊓ M.U q)) h
        simp only [map_mul, rs_rs] at h' ⊢
        exact h')
    rw [← RingHom.range_eq_top, eq_top_iff]
    rintro x -
    obtain ⟨P, rfl⟩ := hgen x
    induction P using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂Hom_C]
      obtain ⟨F, rfl⟩ := sj c
      induction F using MvPolynomial.induction_on with
      | C c₀ =>
        refine ⟨MvPolynomial.C c₀, ?_⟩
        rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
        simp only [AbLaw.cst, RingHom.comp_apply, rs_rs]
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F l hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e j).1, l)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o', map_one, _root_.one_mul]
    | add P Q hP hQ => rw [map_add]; exact Subring.add_mem _ hP hQ
    | mul_X P c hP =>
      rw [map_mul]
      refine Subring.mul_mem _ hP ⟨MvPolynomial.X (e.symm (c, (e j).2)), ?_⟩
      simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o, map_one, _root_.mul_one]
end GlobalTheory.GenTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_unique_on_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om om' : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f := by
  first | exact @GlobalTheory.WeilUniq.weilDatum_unique | exact GlobalTheory.WeilUniq.weilDatum_unique | (intros; apply GlobalTheory.WeilUniq.weilDatum_unique <;> assumption)
end

