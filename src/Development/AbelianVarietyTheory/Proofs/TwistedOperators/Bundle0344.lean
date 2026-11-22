import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0342
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothVectorMatrixCoeffIntegrable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWordTranslate

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationTransportTopGroupEquiv
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
namespace GlobalTheory.TransportIso

theorem irreducible_admissible_integralOp_transport : ∀ (G G' : Type) [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G'] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G'] (Φ : G ≃ₜ* G') (ν : Measure G) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), (σ.IsIrreducible → Representation.IsIrreducible (σ.comp Φ.symm.toMulEquiv.toMonoidHom)) ∧ (IsAdmissible σ → IsAdmissible (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W)) ∧ ∀ (f : G → ℂ) (f' : G' → ℂ), (∀ g, f' (Φ g) = f g) → ∀ A, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (ν.map Φ) (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W) f' A ↔ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ f A := by
  intro G G' _ _ _ _ _ _ _ _ Φ ν W _ _ σ
  have hs : ∀ g' : G', Φ.symm.toMulEquiv g' = Φ.symm g' := fun _ => rfl
  have hs2 : ∀ g' : G', Φ.symm.toMulEquiv.toMonoidHom g' = Φ.symm g' := fun _ => rfl
  have hcomp' : ∀ g' : G', (σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' = σ (Φ.symm g') := fun _ => rfl
  have hcomp : ∀ g : G, (σ.comp Φ.symm.toMulEquiv.toMonoidHom) (Φ g) = σ g := by
    intro g; rw [hcomp', Φ.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro hσ
    let e : Subrepresentation (σ.comp Φ.symm.toMulEquiv.toMonoidHom) ≃o Subrepresentation σ :=
      { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
          have := U.apply_mem_toSubmodule (Φ g) hv
          rwa [hcomp] at this⟩
        invFun := fun U => ⟨U.toSubmodule, fun g' v hv => by
          rw [hcomp']
          exact U.apply_mem_toSubmodule _ hv⟩
        left_inv := fun U => rfl
        right_inv := fun U => rfl
        map_rel_iff' := Iff.rfl }
    exact e.isSimpleOrder
  · rintro ⟨hsm, hfd⟩
    refine ⟨?_, ?_⟩
    · intro v
      have : {g' : G' | (σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' v = v} = Φ.symm ⁻¹' {g | σ g v = v} := by
        ext g'; exact Iff.rfl
      rw [this]
      exact (hsm v).preimage Φ.symm.continuous
    · intro K' hK'o hK'c
      let K : Subgroup G := K'.comap Φ.toMulEquiv.toMonoidHom
      have hKo : IsOpen (K : Set G) := hK'o.preimage Φ.continuous
      have hKc : IsCompact (K : Set G) := by
        have : (K : Set G) = Φ.symm '' (K' : Set G') := by
          ext g; constructor
          · intro hg; exact ⟨Φ g, hg, by simp⟩
          · rintro ⟨g', hg', rfl⟩
            show Φ (Φ.symm g') ∈ K'
            simpa using hg'
        rw [this]; exact hK'c.image Φ.symm.continuous
      have heq : GlobalTheory.PRep.fixed (σ.comp Φ.symm.toMulEquiv.toMonoidHom) K' = GlobalTheory.PRep.fixed σ K := by
        ext v
        simp only [GlobalTheory.PRep.fixed, GlobalTheory.PRep.eig]
        constructor
        · intro hv h
          have := hv ⟨Φ h, h.2⟩
          simp at this ⊢
          convert this using 3
          exact (Φ.symm_apply_apply _).symm
        · intro hv h
          have := hv ⟨Φ.symm h, show Φ (Φ.symm h) ∈ K' by simpa using h.2⟩
          simp at this ⊢
          convert this using 3
          rfl
      rw [heq]
      exact hfd K hKo hKc
  · intro f f' hf A
    let e : G ≃ᵐ G' := Φ.toHomeomorph.toMeasurableEquiv
    have hmap : ν.map Φ = ν.map e := rfl
    have he : ∀ g, e g = Φ g := fun g => rfl
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp, hmap]
    refine forall_congr' fun v => forall_congr' fun l => ?_
    rw [integrable_map_equiv, integral_map_equiv]
    have hfun : ((fun g' => f' g' * l ((σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' v)) ∘ e) = fun g => f g * l (σ g v) := by
      funext g; simp only [Function.comp_apply, he, hf, hcomp]
    have hfun' : (fun g => f' (e g) * l ((σ.comp Φ.symm.toMulEquiv.toMonoidHom) (e g) v)) = fun g => f g * l (σ g v) := by
      funext g; simp only [Function.comp_apply, he, hf, hcomp]
    rw [hfun, hfun']

end GlobalTheory.TransportIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightDerivativeRightConvolutionEqTestFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_rightConvolution_eq_test_function : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}, X ∈ lieAt V τ → ∃ f' ∈ GlobalTheory.Orb.CcGA V, tsupport f' ⊆ tsupport f ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, Rder θ V τ X (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) = GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) := by
  first | exact @GlobalTheory.ConvRDeriv.Rder_convR | exact GlobalTheory.ConvRDeriv.Rder_convR | (intros; apply GlobalTheory.ConvRDeriv.Rder_convR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightRegularOperatorRepresentedContinuous
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed
open scoped Pointwise

namespace GlobalTheory.RopRep

theorem rop_rep : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, ∀ F : DividedPowerChartLift V μ, (∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ) ∧ Continuous (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ LeftInv (GQ V) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ lift (GQ V) (RopG V μ f F) =ᵐ[μ] fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ := by
  intro D V μ _ _ f hf F
  obtain ⟨hfc, hfs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have hloc : LocallyIntegrable (lift (GQ V) F) μ :=
    (locallyIntegrable_iff).2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
  have hint : ∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ := fun x =>
    hloc.integrable_smul_left_of_hasCompactSupport (hfc.comp (continuous_const_mul _))
      (hfs.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hconv : (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) = convR μ f (lift (GQ V) F) :=
    funext fun x => (convR_eq f _ x).symm
  refine ⟨hint, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun x₀ => ?_
    obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x₀
    obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
    have hC : IsCompact (K * tsupport f) := hK.mul hfs
    have hCi : IntegrableOn (lift (GQ V) F) (K * tsupport f) μ :=
      (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F _ hC).2
    refine continuousAt_of_dominated
      (bound := (K * tsupport f).indicator fun y => M * ‖lift (GQ V) F y‖)
      (.of_forall fun x => (hint x).1) ?_ ?_ (.of_forall fun y => ?_)
    · filter_upwards [hKx] with x hx
      refine .of_forall fun y => ?_
      by_cases hy : f (x⁻¹ * y) = 0
      · rw [hy, zero_mul, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hM 1)) (norm_nonneg _)) _
      · have hmem : y ∈ K * tsupport f :=
          ⟨x, hx, x⁻¹ * y, subset_tsupport f hy, by simp⟩
        rw [Set.indicator_of_mem hmem, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · exact (integrable_indicator_iff hC.isClosed.measurableSet).2 (hCi.norm.const_mul M)
    · exact ((hfc.comp (continuous_inv.mul continuous_const)).mul continuous_const).continuousAt
  · rw [hconv]
    exact (leftInv_lift _).convR f
  · rw [hconv]
    exact (GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ (GQ V) μ f
      (hfc.integrable_of_hasCompactSupport hfs) F).2

end GlobalTheory.RopRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissible
section
namespace GlobalTheory.SchurAdmissibility

theorem schur_admissible (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N)
    (hirr : Representation.IsIrreducible π) (hadm : GlobalTheory.PRep.IsAdmissible π)
    (φ : N →ₗ[ℂ] N) (hφ : ∀ (g : G) (x : N), φ (π g x) = π g (φ x)) :
    ∃ c : ℂ, φ = c • LinearMap.id := by
  by_cases hN : ∀ v : N, v = 0
  · exact ⟨0, LinearMap.ext fun v => by rw [hN (φ v)]; simp⟩
  push Not at hN
  obtain ⟨v, hv⟩ := hN
  let S : Subgroup G :=
    { carrier := {g : G | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hadm.1 v
  have hSc : IsClosed (S : Set G) := S.isClosed_of_isOpen hSo
  have hLo : IsOpen ((K ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter hSo
  have hLc : IsCompact ((K ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKc.inter_right hSc
  haveI hfd := hadm.2 (K ⊓ S) hLo hLc
  have hmem : ∀ w : N, w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) ↔
      ∀ h : (K ⊓ S : Subgroup G), π (h : G) w = w := by
    intro w
    change (∀ h : (K ⊓ S : Subgroup G), π (h : G) w = _) ↔ _
    simp
  have hvm : v ∈ GlobalTheory.PRep.fixed π (K ⊓ S) := (hmem v).2 fun h => h.2.2
  haveI : Nontrivial (GlobalTheory.PRep.fixed π (K ⊓ S)) :=
    ⟨⟨⟨v, hvm⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hres : ∀ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S), φ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) := by
    intro w hw
    rw [hmem] at hw ⊢
    intro h
    rw [← hφ, hw h]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrict hres)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : N) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hw1 : φ w = c • (w : N) := congrArg Subtype.val hw.apply_eq_smul
  let U : Subrepresentation π :=
    { toSubmodule := Module.End.eigenspace φ c
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        rw [hφ, hx, map_smul] }
  refine ⟨c, ?_⟩
  rcases hirr.eq_bot_or_eq_top U with h | h
  · exfalso
    have h1 : (w : N) ∈ U.toSubmodule := Module.End.mem_eigenspace_iff.2 hw1
    rw [h] at h1
    exact hw0 h1
  · ext x
    have h1 : x ∈ U.toSubmodule := by
      rw [h]; trivial
    exact Module.End.mem_eigenspace_iff.1 h1

end GlobalTheory.SchurAdmissibility
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothVectorMatrixCoeffIntegrableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_matrixCoeff_integrable : ∀ (m N : ℕ) (e : Option (Fin m) ≃ Fin N) (ε : Fin N → Bool) (ε' : Fin m → Bool)
  (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (v : H) (K : ℝ),
  Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) π → ε (e none) = true → (∀ i, ε (e (some i)) = ε' i) →
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) π v →
  (∀ g ∈ Formalism.MainNotions.S.UJset ε,
    Integrable (fun h => ⟪v, π (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ) (Formalism.REAL.muG ε')) →
  (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε'), GlobalTheory.SepReal.hsn X ≤ 1 →
    Integrable (fun h => ⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL e X) v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
      (Formalism.REAL.muG ε') ∧
    ∫ h, ‖⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL e X) v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤ K) →
  ∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε'), ∀ s : ℝ,
    Integrable (fun h => ‖⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ε') ∧
    ∫ h, ‖⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤ K * |s| * GlobalTheory.SepReal.hsn X := by
  first | exact @GlobalTheory.PackLip.lip_core | exact GlobalTheory.PackLip.lip_core | (intros; apply GlobalTheory.PackLip.lip_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeries
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFiniteDense

open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.TypeSum

section WordCurve

variable {n : ℕ}

theorem dRep_fsum {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (h : Std ε σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (w : ι → H) (hw : ∀ j, Sm ε σ (w j)) :
    dRep σ Z (∑ j ∈ s, c j • w j) = ∑ j ∈ s, c j • dRep σ Z (w j) := by
  classical
  have hl : ∀ Y ∈ [Z], Y ∈ lieSet ε := by simpa using hZ
  have hsm : ∀ t : Finset ι, Sm ε σ (∑ j ∈ t, c j • w j) := fun t =>
    (GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).sum_mem fun j _ =>
      (GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).smul_mem _ (hw j)
  induction s using Finset.induction_on with
  | empty =>
    have := Dw_smul h.1 hl (0 : ℂ) (x := (0 : H)) (GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).zero_mem
    simp only [zero_smul, Dw, List.foldr_cons, List.foldr_nil] at this
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have e1 := Dw_add h.1 hl ((GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).smul_mem (c a) (hw a)) (hsm s)
    have e2 := Dw_smul h.1 hl (c a) (hw a)
    simp only [Dw, List.foldr_cons, List.foldr_nil] at e1 e2
    rw [e1, e2, ih]

theorem exists_coord (ε : Fin n → Bool) : ∃ (d : ℕ) (B : Fin d → Mx n) (φ : Fin d → (Mx n →ₗ[ℝ] ℝ)),
    (∀ i, B i ∈ lieSet ε) ∧ ∀ Y ∈ lieSet ε, Y = ∑ i, φ i Y • B i := by
  let b := Module.finBasis ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))
  choose g hg using fun i => LinearMap.exists_extend (b.coord i)
  refine ⟨_, fun i => b i, g, fun i => (b i).2, fun Y hY => ?_⟩
  have e := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at e
  conv_lhs => rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := LinearMap.congr_fun (hg i) ⟨Y, hY⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [this]
  rfl

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem analyticAt_coord (X Y : Mx n) (φ : Mx n →ₗ[ℝ] ℝ) :
    AnalyticAt ℝ (fun t : ℝ => ((φ (NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)) : ℝ) : ℂ)) 0 := by
  have h1 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (t • X)) 0 :=
    AnalyticAt.comp (NormedSpace.exp_analytic (𝕂 := ℝ) _) (analyticAt_id.smul analyticAt_const)
  have h2 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (-(t • X))) 0 :=
    AnalyticAt.comp (NormedSpace.exp_analytic (𝕂 := ℝ) _) (analyticAt_id.smul analyticAt_const).neg
  have h3 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)) 0 :=
    (h2.fun_mul analyticAt_const).fun_mul h1
  have h4 := ((LinearMap.toContinuousLinearMap φ).analyticAt _).comp h3
  exact (Complex.ofRealCLM.analyticAt _).comp h4

end

theorem wordCurve : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ → ∀ X : Matrix (Fin n) (Fin n) ℂ, X ∈ GlobalTheory.SmoothGlob.lieSet ε → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Y ∈ GlobalTheory.SmoothGlob.lieSet ε) → ∀ v : H, Formalism.MainNotions.S.IsKFin ε σ v → ∃ (m : ℕ) (c : Fin m → ℝ → ℂ) (w : Fin m → H), (∀ j, AnalyticAt ℝ (c j) 0) ∧ (∀ j, Formalism.MainNotions.S.IsKFin ε σ (w j)) ∧ ∀ t : ℝ, List.foldr (Formalism.L2.Theta.dRep σ) v (l.map fun Y => NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)) = ∑ j, c j t • w j := by
  intro n ε H _ _ _ σ h X hX l hl v hv
  obtain ⟨d, B, φ, hB, hφ⟩ := exists_coord (n := n) ε
  induction l with
  | nil => exact ⟨1, fun _ _ => 1, fun _ => v, fun _ => analyticAt_const, fun _ => hv, fun t => by simp⟩
  | cons Y l ih =>
    obtain ⟨m, c, w, hc, hw, he⟩ := ih (fun Z hZ => hl Z (List.mem_cons_of_mem _ hZ))
    have hY := hl Y List.mem_cons_self
    let A : ℝ → Mx n := fun t => NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)
    have hA : ∀ t, A t ∈ lieSet ε := fun t => by
      show NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X) ∈ lieSet ε
      rw [Matrix.exp_neg]
      exact GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) (exp_mem_UJ hX t) hY
    let e := (finProdFinEquiv (m := m) (n := d)).symm
    refine ⟨m * d, fun k t => c (e k).1 t * ((φ (e k).2 (A t) : ℝ) : ℂ),
      fun k => dRep σ (B (e k).2) (w (e k).1), fun k => (hc _).fun_mul (analyticAt_coord X Y _),
      fun k => isKFin_dRep n ε H σ h _ (hw _) _ (hB _), fun t => ?_⟩
    rw [List.map_cons, List.foldr_cons, he t]
    change dRep σ (A t) _ = _
    rw [dRep_fsum h (hA t) Finset.univ _ w (fun j => h.2.2.1 _ (hw j))]
    have hs : ∀ j, dRep σ (A t) (w j) = ∑ i, ((φ i (A t) : ℝ) : ℂ) • dRep σ (B i) (w j) := fun j => by
      conv_lhs => rw [hφ _ (hA t)]
      exact h.dRep_sum hB (h.2.2.1 _ (hw j)) _
    simp only [hs, Finset.smul_sum, smul_smul]
    rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv e _ _ fun k => rfl).symm

end WordCurve

theorem eq_zero_of_iteratedDeriv_eq_zero : ∀ f : ℝ → ℂ, AnalyticOnNhd ℝ f Set.univ → (∀ m : ℕ, iteratedDeriv m f 0 = 0) → ∀ t, f t = 0 := by
  intro f hf h0 t
  obtain ⟨p, r, hp⟩ := hf 0 trivial
  have hc : ∀ m (y : ℝ), p m (fun _ => y) = 0 := by
    intro m y
    have e1 := hp.factorial_smul 1 m
    rw [← iteratedDeriv_eq_iteratedFDeriv, h0 m] at e1
    have e2 : p m (fun _ => (1 : ℝ)) = 0 := by
      exact (smul_eq_zero.1 e1).resolve_left (Nat.factorial_ne_zero m)
    have e3 := (p m).map_smul_univ (fun _ => y) (fun _ => (1 : ℝ))
    simp only [smul_eq_mul, mul_one] at e3
    rw [e3, e2, smul_zero]
  have hev : f =ᶠ[nhds 0] 0 := by
    filter_upwards [EMetric.ball_mem_nhds (0 : ℝ) hp.r_pos] with y hy
    have := hp.hasSum (y := y) (by simpa using hy)
    simp only [hc, zero_add] at this
    exact (this.unique hasSum_zero).symm ▸ rfl
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ trivial hev trivial

section Coef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem analyticAt_coef (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    AnalyticAt ℝ (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) v)) 0 := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := GlobalTheory.LowTypeDetermined.exists_factor (isUnit_Jm ε) h.1 hℓ
  have hsm : Sm ε σ v := h.2.2.1 v hv
  choose N c w hc hw he using fun i => wordCurve n ε H σ h X hX (S i) (hS i) v hv
  have key : ∀ t : ℝ, ℓ (σ (NormedSpace.exp (t • X)) v) =
      ∑ i, ∑ j, c i j t * Λ i (σ (NormedSpace.exp (t • X)) (w i j)) := by
    intro t
    have hg := exp_mem_UJ hX t
    rw [hΛ _ (hsm.translate h.1 hg)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := Dw_translate h.1 hg hsm (hS i)
    have e2 : (NormedSpace.exp (t • X))⁻¹ = NormedSpace.exp (-(t • X)) := (Matrix.exp_neg _).symm
    simp only [Dw] at e1
    rw [e1, e2, he i t, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
  have ha : ∀ i j, AnalyticAt ℝ (fun t : ℝ => Λ i (σ (NormedSpace.exp (t • X)) (w i j))) 0 := by
    intro i j
    have := ((hHC.analytic h.1 h.2.1 (hw i j)).clm ((Λ i).restrictScalars ℝ)).analytic_exp (g := 1)
      (one_mem_UJ ε) hX 0
    simpa only [one_mul, ContinuousLinearMap.coe_restrictScalars'] using this
  have hsum : AnalyticAt ℝ (fun t : ℝ => ∑ i, ∑ j, c i j t * Λ i (σ (NormedSpace.exp (t • X)) (w i j))) 0 := by
    exact Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ => (hc i j).fun_mul (ha i j)
  exact hsum.congr (Filter.Eventually.of_forall fun t => (key t).symm)

theorem analyticOnNhd_coef (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    AnalyticOnNhd ℝ (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) v)) Set.univ := by
  intro t₀ _
  have hg := exp_mem_UJ hX t₀
  have h1 := analyticAt_coef hHC h (sobCont_translate h.1 hℓ hg) hv hX
  have h2 : AnalyticAt ℝ (fun t : ℝ => t - t₀) t₀ := analyticAt_id.sub analyticAt_const
  have h3 := h1.comp_of_eq h2 (sub_self t₀)
  refine h3.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_def, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [← sigma_mul h.1 hg (exp_mem_UJ hX _), ← exp_add_smul, add_sub_cancel]

theorem hasDerivAt_coef1 (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {u : H} (hu : Sm ε σ u)
    {X : Mx n} (hX : X ∈ lieSet ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) u)) (ℓ (σ (NormedSpace.exp (s • X)) (dRep σ X u))) s := by
  have hs := exp_mem_UJ hX s
  have h1 := h.hasDerivAt_sobFun ((sobFun_of_sobCont hℓ).translate h.1 hs) hu hX
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = ℓ (σ _ (σ _ u))
  rw [← sigma_mul h.1 hs (exp_mem_UJ hX _), ← exp_add_smul, add_sub_cancel]

theorem isKFin_iterate (h : Std ε σ) {X : Mx n} (hX : X ∈ lieSet ε) (m : ℕ) {u : H} (hu : IsKFin ε σ u) :
    IsKFin ε σ ((dRep σ X)^[m] u) := by
  induction m with
  | zero => exact hu
  | succ m ih => rw [Function.iterate_succ_apply']; exact isKFin_dRep n ε H σ h _ ih X hX

theorem iteratedDeriv_coef (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {X : Mx n}
    (hX : X ∈ lieSet ε) (m : ℕ) : ∀ u : H, IsKFin ε σ u →
    iteratedDeriv m (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) u)) =
      fun t => ℓ (σ (NormedSpace.exp (t • X)) ((dRep σ X)^[m] u)) := by
  induction m with
  | zero => intro u _; simp
  | succ m ih =>
    intro u hu
    have hd : deriv (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) u)) =
        fun t => ℓ (σ (NormedSpace.exp (t • X)) (dRep σ X u)) :=
      funext fun t => (hasDerivAt_coef1 h hℓ (h.2.2.1 u hu) hX t).deriv
    rw [iteratedDeriv_succ', hd, ih _ (isKFin_dRep n ε H σ h u hu X hX)]
    funext t
    rw [Function.iterate_succ_apply]

theorem coef_eq_zero (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) (h0 : ∀ u, IsKFin ε σ u → ℓ u = 0) {v : H} (hv : IsKFin ε σ v) {X : Mx n}
    (hX : X ∈ lieSet ε) (t : ℝ) : ℓ (σ (NormedSpace.exp (t • X)) v) = 0 := by
  refine eq_zero_of_iteratedDeriv_eq_zero _ (analyticOnNhd_coef hHC h hℓ hv hX) (fun m => ?_) t
  rw [iteratedDeriv_coef h hℓ hX m v hv]
  simp only [zero_smul, NormedSpace.exp_zero, sigma_one h.1]
  exact h0 _ (isKFin_iterate h hX m hv)

theorem orbit_eq_zero (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) (h0 : ∀ u, IsKFin ε σ u → ℓ u = 0) {v : H} (hv : IsKFin ε σ v) {g : Mx n}
    (hg : g ∈ UJset ε) : ℓ (σ g v) = 0 := by
  have hk := mul_exp_neg_polarLog_mem_compact (ε := ε) hg
  have hL' : polarLog g ∈ lieSet ε := (polarLog_mem_hermitian_part (ε := ε) hg).1
  have e : g = (g * NormedSpace.exp (-polarLog g)) * NormedSpace.exp ((1 : ℝ) • polarLog g) := by
    rw [one_smul]; exact polar_decomposition_eq
  rw [e, sigma_mul h.1 (K_le_UJ hk) (exp_mem_UJ hL' 1)]
  exact coef_eq_zero (ℓ := ℓ ∘ₗ (σ (g * NormedSpace.exp (-polarLog g)) : H →ₗ[ℂ] H)) hHC h
    (sobCont_translate h.1 hℓ (K_le_UJ hk)) (fun u hu => h0 _ (isKFin_translate hu hk)) hv hL' 1

end Coef

theorem eq_zero_of_kFin : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, ℓ w = 0) → ∀ w ∈ M.sm τ, ℓ w = 0 := by
  intro hHC D V S M τ ℓ hℓ h0 w hw
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have h := std_of_isDS hHC (M.ds τ)
  have hℓ' : Sobolev₂ (lieSet (M.ε τ)) (M.σ τ) ℓ :=
    GlobalTheory.SmoothCyclic.sobCont_transport (M.fr_unit τ) (M.fr_gram τ) hℓ
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
  have hw' : Sm (M.ε τ) (M.σ τ) w := (GlobalTheory.SmoothCyclic.sm_eq M τ).le hw
  exact h.eq_zero_of_orbit hℓ' (h.2.2.1 a ha) ha0
    (fun g hg => orbit_eq_zero hHC h hℓ' (fun u hu => h0 u hu) ha hg) hw'

end GlobalTheory.KFiniteDense
end
end

