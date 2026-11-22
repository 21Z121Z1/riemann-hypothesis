import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0905
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0927
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0928
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0756
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0929
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartGlobalWhittakerCoefficient
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

noncomputable section

namespace GlobalTheory.JSW.WhitSmooth

open GroundTheory.Automorphic.FourierWhittaker GlobalTheory.ConstTermSmooth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem chart_oneL (F : GA E a → ℂ) (g : GA E a) : chart F g (oneL E a) = F g := by
  have := chart_val F g 1
  simpa using this

theorem chart_whit (F : GA E a → ℂ) (g : GA E a) :
    chart (GlobalTheory.JSW.whit F) g = fun y => ∫ X in vecDomain E (Pos a),
      chart F (uGL X * g) y * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂vecMeasure E (Pos a) := by
  funext y
  by_cases h : IsUnit (Matrix.of y)
  · simp only [chart, dif_pos h, GlobalTheory.JSW.WhitAlg.whit_eq, mul_assoc]
  · simp only [chart, dif_neg h, zero_mul, integral_zero]

theorem hasFDerivAt_chart_whit {φ : Sm E a} (h : Good φ) (g : GA E a) :
    HasFDerivAt (chart (GlobalTheory.JSW.whit φ.1) g)
      (∫ X in vecDomain E (Pos a), (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) •
        fderiv ℝ (chart φ.1 (uGL X * g)) (oneL E a) ∂vecMeasure E (Pos a)) (oneL E a) := by
  rw [chart_whit]
  have hy : oneL E a ∈ invSet E a := isUnit_one
  obtain ⟨S, hSy, hSU, hS⟩ := local_compact_nhds (isOpen_invSet.mem_nhds hy)
  have hm : Continuous fun p : (Pos a → Ad E) × Lie E a => ((uGL p.1 * g, p.2) : GA E a × Lie E a) :=
    ((continuous_uGL.comp continuous_fst).mul continuous_const).prodMk continuous_snd
  have hmt : Set.MapsTo (fun p : (Pos a → Ad E) × Lie E a => ((uGL p.1 * g, p.2) : GA E a × Lie E a))
      (Set.univ ×ˢ invSet E a) (Set.univ ×ˢ invSet E a) := fun p hp => ⟨Set.mem_univ _, hp.2⟩
  have hc := h.continuousOn_fderiv.comp hm.continuousOn hmt
  have hc0 := h.continuousOn_chart.comp hm.continuousOn hmt
  obtain ⟨C, hC⟩ := (isCompact_closure_vecDomain.prod hS).exists_bound_of_continuousOn
    (hc.mono (Set.prod_mono (Set.subset_univ _) hSU))
  have hint : ∀ z ∈ invSet E a, Integrable (fun X => chart φ.1 (uGL X * g) z *
      (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    fun z hz => ((((hc0.comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨trivial, hz⟩)).mul
      GlobalTheory.JSW.WhitAlg.continuous_psiNeg).continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set
      subset_closure
  have hint' : Integrable (fun X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) •
      fderiv ℝ (chart φ.1 (uGL X * g)) (oneL E a)) ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ((GlobalTheory.JSW.WhitAlg.continuous_psiNeg.smul (hc.comp_continuous (continuous_id.prodMk continuous_const)
      fun _ => ⟨trivial, hy⟩)).continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure
  haveI : IsFiniteMeasure ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ⟨by rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun z X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) • fderiv ℝ (chart φ.1 (uGL X * g)) z) hSy
    (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hy) fun z hz => (hint z hz).1) (hint _ hy) hint'.1
    ?_ (integrable_const C) ?_
  · filter_upwards [ae_restrict_mem measurableSet_vecDomain] with X hX z hz
    rw [norm_smul, Circle.norm_coe, one_mul]
    exact hC (X, z) ⟨subset_closure hX, hz⟩
  · refine .of_forall fun X z hz => ?_
    exact ((contDiffAt_chart φ.2 _ (hSU hz)).differentiableAt (by simp)).hasFDerivAt.mul_const _

theorem hasFDerivAt_chart_whit' {φ : Sm E a} (h : Good φ) (g : GA E a) :
    HasFDerivAt (chart (GlobalTheory.JSW.whit φ.1) g)
      (∑ i, GlobalTheory.JSW.whit (lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 g • coef i (oneL E a)) (oneL E a) := by
  refine (hasFDerivAt_chart_whit h g).congr_fderiv ?_
  have hy : oneL E a ∈ invSet E a := isUnit_one
  have e : ∀ X : Pos a → Ad E, (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) •
      fderiv ℝ (chart φ.1 (uGL X * g)) (oneL E a) = ∑ i,
        (chart (lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 (uGL X * g) (oneL E a) *
          (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) • coef i (oneL E a) := fun X => by
    rw [fderiv_chart φ _ hy, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_const, ← congrFun (chart_whit _ g) (oneL E a), chart_oneL]
  · have hl := h.lie (Module.finBasis ℝ (Lie E a) i)
    refine (Integrable.smul_const ?_ _)
    simp_rw [chart_oneL]
    exact GlobalTheory.JSW.WhitAlg.integrableOn_whit (ContAut.continuous_of_isOpen_stab E a _ hl.2) g

theorem whit_mem_Sm (φ : Sm E a) (h : Good φ) : GlobalTheory.JSW.whit φ.1 ∈ Sm E a := by
  refine GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt E a {f | ∃ ψ : Sm E a, Good ψ ∧ f = GlobalTheory.JSW.whit ψ.1} ?_ _
    ⟨φ, h, rfl⟩
  rintro f ⟨ψ, hψ, rfl⟩
  exact ⟨_, inferInstance, fun i => GlobalTheory.JSW.whit (lie E a (Module.finBasis ℝ (Lie E a) i) ψ).1,
    fun i => coef i (oneL E a), fun i => ⟨_, hψ.lie _, rfl⟩, hasFDerivAt_chart_whit' hψ⟩

theorem whit_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g, ContDiffOn ℝ ∞ (chart (GlobalTheory.JSW.whit φ.1) g) (invSet E a) := by
  intro E _ _ _ a φ hφ g
  exact whit_mem_Sm φ ⟨hφ.left, hφ.level⟩ g

end GlobalTheory.JSW.WhitSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormLinearRelationDefinedOverCoreFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_linear_relation_defined_over_core_field : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ τ : ℂ ≃+* ℂ, (∀ a : T.Q.c.F, τ (a : ℂ) = (a : ℂ)) → ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n), Expands M (κ i) (fun _ => 0) a f → Expands M (κ i) (fun _ => 0) (fun k => τ (a k)) f := by
  first | exact @GlobalTheory.ConjRelation.expands_zero_conj | exact GlobalTheory.ConjRelation.expands_zero_conj | (intros; apply GlobalTheory.ConjRelation.expands_zero_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterEqOfMarkedLatticeIsometryStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detCharacter_eq_of_marked_lattice_isometry : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hio : LinearMap.range io = latG V 1)
    (A A' : Datum H) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La)
    (X X' : Data D.host.E V.rank) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (g g' : GA D V)
    (hW : ModelW V rfl X) (hW' : ModelW V rfl X')
    (hE : ∀ a b, ((A.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin V.rank → D.host.E) (φ b)))
    (hE' : ∀ a b, ((A'.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hL : (X.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g : Set _))
    (hL' : (X'.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g' : Set _))
    (hm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V ((φ (t a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hm' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V ((φ' (t' a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (gam : A.La ≃ₗ[𝓞 D.host.E] A'.La) (hgE : ∀ a b, A'.EF (gam a) (gam b) = A.EF a b)
    (hgm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ x, gam (t a) = t' a + l.M • x)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1), xi (Matrix.GeneralLinearGroup.det (finHom V g')) = xi (Matrix.GeneralLinearGroup.det (finHom V g)) := by
  first | exact @GlobalTheory.MarkIso.xi_det_eq_of_marked_isometry | exact GlobalTheory.MarkIso.xi_det_eq_of_marked_isometry | (intros; apply GlobalTheory.MarkIso.xi_det_eq_of_marked_isometry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNatIntegralFrameOfUniformizerMulStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_integral_frame_of_uniformizer_mul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (ϖ : 𝓞 D.host.E), ϖ ≠ 0 → ∃ k : ℕ, 0 < k ∧ ∀ u : WO S T, IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) → IsIntM (frMapO S T βS βT (k • u)) := by
  first | exact @GlobalTheory.FlatLift.kmul_int | exact GlobalTheory.FlatLift.kmul_int | (intros; apply GlobalTheory.FlatLift.kmul_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnipotentInvariantCompactlySupportedWeight
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix
open GlobalTheory.WhitBump

noncomputable section

namespace GlobalTheory.KappaCut

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem decomp (h : GA E a) :
    h = infGL E a (GeneralLinearGroup.map (pInf E) h) * finGL E a (GeneralLinearGroup.map (pFin E) h) := by
  refine ga_ext ?_ ?_ <;> simp

theorem continuous_of_chart (b : GA E a → ℂ) (U : Subgroup (GL (Fin a) (Af E))) (hU : IsOpen (U : Set (GL (Fin a) (Af E))))
    (hR : ∀ u ∈ U, ∀ g, b (g * finGL E a u) = b g) (hC : ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E a)) :
    Continuous b := by
  rw [continuous_iff_continuousAt]
  intro g
  let pI : GA E a → GL (Fin a) (Cinf E) := fun h => GeneralLinearGroup.map (pInf E) h
  let pF : GA E a → GL (Fin a) (Af E) := fun h => GeneralLinearGroup.map (pFin E) h
  have hpI : Continuous pI := ContAut.continuous_map_pInf E a
  have hpF : Continuous pF := ContAut.continuous_map_pFin E a
  let F : GA E a → Lie E a := fun g' => toL ((pI (g⁻¹ * g') : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))
  have hF : Continuous F := (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp (hpI.comp (continuous_const.mul continuous_id))
  have hFmem : ∀ g', F g' ∈ invSet E a := fun g' => show IsUnit (Matrix.of (F g')) from (pI (g⁻¹ * g')).isUnit
  have heq : ∀ g', pF (g⁻¹ * g') ∈ U → b g' = chart b g (F g') := by
    intro g' hg'
    have hx : IsUnit (Matrix.of (F g')) := (pI (g⁻¹ * g')).isUnit
    rw [chart, dif_pos hx]
    have hu : hx.unit = pI (g⁻¹ * g') := Units.ext rfl
    rw [hu]
    have e : g' = g * infGL E a (pI (g⁻¹ * g')) * finGL E a (pF (g⁻¹ * g')) := by
      rw [mul_assoc, ← decomp, mul_inv_cancel_left]
    rw [show b g' = b (g * infGL E a (pI (g⁻¹ * g')) * finGL E a (pF (g⁻¹ * g'))) from congrArg b e, hR _ hg']
  have hopen : {g' | pF (g⁻¹ * g') ∈ U} ∈ nhds g := by
    refine (hU.preimage (hpF.comp (continuous_const.mul continuous_id))).mem_nhds ?_
    simp [pF, U.one_mem]
  have hcont : ContinuousAt (fun g' => chart b g (F g')) g := by
    have h1 : ContinuousWithinAt (chart b g) (invSet E a) (F g) := (hC g).continuousOn _ (hFmem g)
    have h2 : ContinuousWithinAt (chart b g ∘ F) Set.univ g :=
      h1.comp hF.continuousAt.continuousWithinAt (fun x _ => hFmem x)
    rwa [continuousWithinAt_univ] at h2
  exact hcont.congr (Filter.eventuallyEq_of_mem hopen (fun g' hg' => (heq g' hg').symm))

theorem contDiff_normSq_ofReal : ContDiff ℝ ∞ (fun z : ℂ => ((Complex.normSq z : ℝ) : ℂ)) := by
  have h : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have e : (fun z : ℂ => ((Complex.normSq z : ℝ) : ℂ)) = fun z => Complex.ofRealCLM (‖z‖ ^ 2) := by
    funext z; simp [Complex.normSq_eq_norm_sq]
  rw [e]
  exact Complex.ofRealCLM.contDiff.comp h

end GlobalTheory.KappaCut

open GlobalTheory.KappaCut in

theorem GlobalTheory.KappaCut.exists_kappa : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (x₀ : GA E (m + 1)),
    ∃ κ : GA E (m + 1) → ℝ, Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h, κ h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart (fun h => (κ h : ℂ)) g) (invSet E (m + 1))) ∧ 0 < κ x₀ := by
  intro E _ _ _ m x₀
  obtain ⟨b, hb1, hbN, ⟨C, hC, hCs⟩, ⟨U, hU, hUr⟩, hbc⟩ := GlobalTheory.WhitBump.exists_bump_glob E m
  have hbcont : Continuous b := continuous_of_chart b U hU hUr hbc
  let pI : GA E (m + 1) → GL (Fin (m + 1)) (Cinf E) := fun h => GeneralLinearGroup.map (pInf E) h
  let pF : GA E (m + 1) → GL (Fin (m + 1)) (Af E) := fun h => GeneralLinearGroup.map (pFin E) h
  have hconjF : ∀ k, x₀ * finGL E (m + 1) k * x₀⁻¹ = finGL E (m + 1) (pF x₀ * k * (pF x₀)⁻¹) := by
    intro k; refine ga_ext ?_ ?_ <;> simp [pF]
  have hconjI : ∀ y, x₀ * infGL E (m + 1) y * x₀⁻¹ = infGL E (m + 1) (pI x₀ * y * (pI x₀)⁻¹) := by
    intro y; refine ga_ext ?_ ?_ <;> simp [pI]
  refine ⟨fun h => Complex.normSq (b (h * x₀⁻¹)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.continuous_normSq.comp (hbcont.comp (continuous_id.mul continuous_const))
  · intro h; exact Complex.normSq_nonneg _
  · intro u hu h
    show Complex.normSq (b (u * h * x₀⁻¹)) = Complex.normSq (b (h * x₀⁻¹))
    rw [mul_assoc, hbN u hu, map_mul, GlobalTheory.JSW.psiN, Circle.normSq_coe, one_mul]
  · refine ⟨(fun c => c * x₀) '' C, hC.image (continuous_id.mul continuous_const), fun h hh => ?_⟩
    have hb : b (h * x₀⁻¹) ≠ 0 := fun e => hh (by simp [e])
    obtain ⟨u, hu, huC⟩ := hCs _ hb
    exact ⟨u, hu, ⟨_, huC, by group⟩⟩
  · refine ⟨U.comap (MulAut.conj (pF x₀)).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · intro u hu h
      have hu' : pF x₀ * u * (pF x₀)⁻¹ ∈ U := hu
      show Complex.normSq (b (h * finGL E (m + 1) u * x₀⁻¹)) = Complex.normSq (b (h * x₀⁻¹))
      have e : h * finGL E (m + 1) u * x₀⁻¹ = h * x₀⁻¹ * finGL E (m + 1) (pF x₀ * u * (pF x₀)⁻¹) := by
        rw [← hconjF]; group
      rw [e, hUr _ hu']
  · intro g
    set A : GL (Fin (m + 1)) (Cinf E) := pI x₀ with hA
    let L0 : Lie E (m + 1) →ₗ[ℝ] Lie E (m + 1) :=
      { toFun := fun x => toL ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x *
          ((A⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))
        map_add' := fun x y => by
          show toL (_ * (Matrix.of x + Matrix.of y) * _) = _
          rw [Matrix.mul_add, Matrix.add_mul]; rfl
        map_smul' := fun c x => by
          show toL (_ * (c • Matrix.of x) * _) = _
          rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
    let L : Lie E (m + 1) →L[ℝ] Lie E (m + 1) := LinearMap.toContinuousLinearMap L0
    have hLx : ∀ x : Lie E (m + 1), Matrix.of (L x) = (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x *
        ((A⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) := by
      intro x
      simp only [L]
      erw [LinearMap.coe_toContinuousLinearMap']
      rfl
    have hmaps : Set.MapsTo L (invSet E (m + 1)) (invSet E (m + 1)) := fun x hx => by
      have hx' : IsUnit (Matrix.of x) := hx
      show IsUnit (Matrix.of (L x))
      rw [hLx]
      exact (A.isUnit.mul hx').mul (A⁻¹).isUnit
    have h2 : ContDiffOn ℝ ∞ (fun x => chart b (g * x₀⁻¹) (L x)) (invSet E (m + 1)) :=
      (hbc (g * x₀⁻¹)).comp L.contDiff.contDiffOn hmaps
    have h3 := contDiff_normSq_ofReal.comp_contDiffOn h2
    refine h3.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    have hL' : IsUnit (Matrix.of (L x)) := hmaps hx
    simp only [Function.comp, chart, dif_pos hx', dif_pos hL']
    congr 3
    have hu : hL'.unit = A * hx'.unit * A⁻¹ := Units.ext (by rw [IsUnit.unit_spec, hLx]; simp)
    rw [hu, ← hconjI]; group
  · simp [hb1]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FamilyUniformisationPointsEqMarkedIsometryStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyUniformisation_points_eq_marked_isometry : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g g' : ℕ}
    {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (F' : FamilyUnif Xo σ' ty')
    (hpq : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0) (hty : IsTypeFn H Dw.p Dw.q ty)
    (hty' : IsTypeFn H Dw.p Dw.q ty') (π : Fin g ≃ Fin g') (hπ : ∀ j, ty' (π j) = ty j)
    (k : Fin F.n) (k' : Fin F'.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (P' : (F'.Di k').La →+ (Fin g' → ℂ))
    (hP : IsPeriod (F.Di k) ty P) (hP' : IsPeriod (F'.Di k') ty' P') (h : F.u k P = F'.u k' P'), ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F'.Di k').La, (∀ a b, (F'.Di k').EF (gam a) (gam b) = (F.Di k).EF a b) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F'.t k' a + l.M • x := by
  first | exact @GlobalTheory.PermUnif.isometry_of_point_eq_perm | exact GlobalTheory.PermUnif.isometry_of_point_eq_perm | (intros; apply GlobalTheory.PermUnif.isometry_of_point_eq_perm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatVecExist

open GlobalTheory.PlaceModel

variable {D : D7}

theorem idemSum_split {e : AE D} {P Q : Finset (Pl D.host.E)} (he : IsIdemSum e (P ∪ Q)) (hd : Disjoint P Q) :
    ∃ eP eQ : AE D, IsIdemSum eP P ∧ IsIdemSum eQ Q ∧ eP * eQ = 0 ∧ eP * cA D eQ = 0 ∧ eQ * cA D eP = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, hc⟩ := he
  have h1 : ∀ i ∈ P ∪ Q, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hx := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es (P ∪ Q) h1 hc
  have hcr : ∀ A B : Finset (Pl D.host.E), A ⊆ P ∪ Q → B ⊆ P ∪ Q →
      (∑ i ∈ A, es i) * cA D (∑ j ∈ B, es j) = 0 := fun A B hA hB => by
    rw [map_sum, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => hx i (hA hi) j (hB hj)
  have hP : P ⊆ P ∪ Q := Finset.subset_union_left
  have hQ : Q ⊆ P ∪ Q := Finset.subset_union_right
  refine ⟨∑ i ∈ P, es i, ∑ i ∈ Q, es i, ⟨⟨es, fun i hi => hes i (hP hi), rfl⟩, hcr P P hP hP⟩,
    ⟨⟨es, fun i hi => hes i (hQ hi), rfl⟩, hcr Q Q hQ hQ⟩, ?_, hcr P Q hP hQ, hcr Q P hQ hP⟩
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  exact GlobalTheory.PlaceDatum.idemAt_mul (hes i (hP hi)) (hes j (hQ hj)) (hx i (hP hi) j (hQ hj)) (hx j (hQ hj) i (hP hi))
    fun h => Finset.disjoint_left.1 hd hi (h ▸ hj)

theorem exists_model_of_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} (he : GlobalTheory.PlaceModelSum.IsOrthSum e)
    (hec : e * cA D e = 0) {g : WO S T → ℂ}
    (hf : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, heisO ψ S T u g = g)
    (hf' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), heisO ψ S T u g = g) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 g Tm := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  refine exists_placeModel ψ hec _ (fun u hu y hy => (hdual u (he.infPart_half hu.2)).1 hu.1 y hy.1)
    (he.mem_of_dual hdual) (fun y hy h => ?_) (fun k hk => ?_) one_ne_zero g hf hf'
  · refine he.conj.mem_of_dual hdual y hy fun u hu => ?_
    rw [GlobalTheory.DualPairCheck.cA_cA] at hu
    rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, GlobalTheory.PlaceModelSum.idem_smul_half he.idem hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]

open Classical in

theorem omegaFlat_congr {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {y y' : ∀ PP : Pl D.host.E, Matrix (Fin a) (Fin b) (kP PP)} (h : ∀ PP ∈ Q, y PP = y' PP) :
    GlobalTheory.ConjTwist.omegaFlat Q r ξ y = GlobalTheory.ConjTwist.omegaFlat Q r ξ y' := by
  have hiff : (∀ PP ∈ Q, IsUnit (topL r (y PP)).det) ↔ ∀ PP ∈ Q, IsUnit (topL r (y' PP)).det :=
    forall_congr' fun PP => forall_congr' fun hPP => by rw [h PP hPP]
  unfold GlobalTheory.ConjTwist.omegaFlat
  by_cases h1 : ∀ PP ∈ Q, IsUnit (topL r (y PP)).det
  · rw [dif_pos h1, dif_pos (hiff.1 h1)]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : (h1 PP.1 PP.2).unit = (hiff.1 h1 PP.1 PP.2).unit :=
      Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 PP.2])
    rw [e]
  · rw [dif_neg h1, dif_neg fun h2 => h1 (hiff.2 h2)]

theorem off_of_half {e c : AE D} (hc : e * c = 0) (hc' : cA D e * c = 0) {S T : HSp D} {u : WO S T} (hu : IsHalf c u) :
    ∀ a b, e * u a b = 0 ∧ cA D e * u a b = 0 := fun a b => by
  rw [← hu a b, ← mul_assoc, ← mul_assoc, hc, hc', zero_mul]
  exact ⟨rfl, rfl⟩

theorem flatVec_existsUnique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), (∃ f, IsFlatVec R i t f) ∧ ∀ f f', IsFlatVec R i t f → IsFlatVec R i t f' → f = f' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ i t
  refine ⟨?_, ?_⟩
  · obtain ⟨hvac, e, he, -⟩ := hR.thP.vP i t
    have hψ := hvac.1
    have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
      GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))
    have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
      GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))
    obtain ⟨eg, eQ, hg, hq, h1, h2, h3⟩ := idemSum_split he (Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hR.lev t)
    have hinfg := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
    obtain ⟨fg, hfg⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hψ sV sW (a := cA D eg)
      (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self hg]) hinfg
      (GlobalTheory.PlaceModelSum.placeModelExistsSum D R.ψ hψ _ _ _ _ sV sW _ eg hg _ hvac.2.theta hvac.2.lat).2
      (GlobalTheory.PlaceVec.isSBHalf_of_red sV.1 sW.1 hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
        (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) R.Pg
        (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h)
    have hoQ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hq
    have fix : ∀ u, (∀ a b, cA D eg * u a b = 0 ∧ eg * u a b = 0) →
        heisO R.ψ (Vc D i) (Wc D i) u (R.vacP i) = R.vacP i → heisO R.ψ (Vc D i) (Wc D i) u fg = fg :=
      fun u hu h0 => GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ (cA D eg) _ 1 _ _ fg hfg u
        (fun a b => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hu a b) h0
    have hPM := exists_model_of_fix hψ sV sW hoQ hq.2
      (fun u hu => fix u (fun a b => (off_of_half h1 (by rw [mul_comm, h3])
          ((isHalf_iff _ _).2 hu.2) a b).symm)
        (hoQ.heisO_eq (by rw [mul_comm, hq.2]) hvac.2.lat u hu))
      (fun u hu => fix u (fun a b => (off_of_half h2
          (by rw [← RingHom.map_mul, h1, map_zero]) ((isHalf_iff _ _).2 hu.2) a b).symm)
        (hoQ.conj.heisO_eq (by rw [GlobalTheory.DualPairCheck.cA_cA, hq.2]) hvac.2.lat u hu))
    have hinfQ := GlobalTheory.PlaceDatum.infPart_idemSum hq
    obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO sV.1 sW.1 (R.βV i) (R.βW i)
    obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.exists_isThetaAt hψ sV sW (GlobalTheory.PlaceDatum.idemSum_mul_self hq) hinfQ hPM
      (GlobalTheory.PlaceDatum.isSBHalf_of_red eQ _ (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (GlobalTheory.PlaceDatum.frMapO_add _ _)
        (GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg _ _)
        ⟨K, hK, fun x hx => hC x (GlobalTheory.PlaceDatum.infPart_of_half hinfQ hx)⟩ (R.Q t)
        (fun y => GlobalTheory.ConjTwist.omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) y) fun y y' h => omegaFlat_congr _ _ _ h)
    exact ⟨f, eg, eQ, fg, hg, hq, hfg, hf⟩
  · rintro f f' ⟨eg, eQ, fg, hg, hq, hfg, hf⟩ ⟨eg', eQ', fg', hg', hq', hfg', hf'⟩
    obtain rfl := GlobalTheory.BaseKernelUniq.idemSum_unique (Vc D i) hg hg'
    obtain rfl := GlobalTheory.BaseKernelUniq.idemSum_unique (Vc D i) hq hq'
    obtain rfl : fg = fg' := by
      obtain ⟨⟨Tm, hTm⟩, hall⟩ := hfg
      rw [hall Tm hTm, hfg'.2 Tm hTm]
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
    rw [hall Tm hTm, hf'.2 Tm hTm]

end GlobalTheory.FlatVecExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralLinearHaarIsMulRightInvariantUnramifiedStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generalLinear_haar_isMulRightInvariant_unramified : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (letI := M.mG; M.μG.IsMulRightInvariant) := by
  first | exact @GlobalTheory.JR.gl_unimodular | exact GlobalTheory.JR.gl_unimodular | (intros; apply GlobalTheory.JR.gl_unimodular <;> assumption)
end

