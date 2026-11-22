import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0590
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanGramFibreMeasureFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0005
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0600
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCoordinatesStatement
section
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_coordinates : PositivityTheory.PfSWUS.SchInf.CoordInf := by
  first | exact @GlobalTheory.CompanionTheory.SW.CoordR.coordInf | exact GlobalTheory.CompanionTheory.SW.CoordR.coordInf | (intros; apply GlobalTheory.CompanionTheory.SW.CoordR.coordInf <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFamilyContinuityStatement
section
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_family_continuity : PositivityTheory.PfSWUS.SchInf.FamCont := by
  first | exact @GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push | exact GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push | (intros; apply GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanGramFibreMeasureFormulaStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_gram_fibre_measure_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∀ minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ c : HermR (Ainf F) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, IsSchwartzArch φ → Measurable φ ∧ (∀ᶠ s in nhds c, Integrable φ (minf s)) ∧ ContinuousAt (fun s => ∫ X, φ X ∂(minf s)) c := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.FibN.fibre_schwartzN | exact GlobalTheory.CompanionTheory.SiegelND.Coef.FibN.fibre_schwartzN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.FibN.fibre_schwartzN <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanHermitianScalingByUnitsStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_hermitian_scaling_by_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S i j, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j = algebraMap (Ainf F) (Ainf F ⊗[F] E) (t i) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j * algebraMap (Ainf F) (Ainf F ⊗[F] E) (t j)) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (2 * n)) • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  first | exact @GlobalTheory.CompanionTheory.SW.DiagScale.coordHerm_map_diag_ainf | exact GlobalTheory.CompanionTheory.SW.DiagScale.coordHerm_map_diag_ainf | (intros; apply GlobalTheory.CompanionTheory.SW.DiagScale.coordHerm_map_diag_ainf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMeasureScalingByUnitsStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_measure_scaling_by_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (fun X a i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * X a i) = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  first | exact @GlobalTheory.CompanionTheory.SW.Dil.coordW_map_units | exact GlobalTheory.CompanionTheory.SW.Dil.coordW_map_units | (intros; apply GlobalTheory.CompanionTheory.SW.Dil.coordW_map_units <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanRankOneFreeOfPlacesStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.SW.BB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_rank_one_free_of_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ X : Fin 1 → Fin M → Ainf F ⊗[F] E, (∀ w, xw e b X w ≠ 0) → LinearIndependent (Ainf F ⊗[F] E) X := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec.linearIndependent_of_xw_ne_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec.linearIndependent_of_xw_ne_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec.linearIndependent_of_xw_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanScalingStatement
section
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_scaling : PositivityTheory.PfSWUS.SchInf.ScaleInf := by
  first | exact @GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf | exact GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf | (intros; apply GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanTateIntegral
section
open MeasureTheory Ad3 Set Filter

namespace GlobalTheory.CompanionTheory.RealTateConv

theorem range_units_val : Set.range (Units.val : ℝˣ → ℝ) = {0}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩

theorem measurableEmbedding_units_val : MeasurableEmbedding (Units.val : ℝˣ → ℝ) := by
  refine ⟨Units.val_injective, ?_, ?_⟩
  · exact measurable_iff_comap_le.2 le_rfl
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [Set.image_preimage_eq_inter_range, range_units_val]
    exact ht.inter (measurableSet_singleton 0).compl

theorem integrable_mulR_iff (g : ℝ → ℂ) :
    Integrable (fun a : ℝˣ => g a) mulR ↔ Integrable (fun x : ℝ => |x|⁻¹ • g x) volume := by
  have hm := measurableEmbedding_units_val
  have hρ : Measurable fun x : ℝ => ENNReal.ofReal |x|⁻¹ := measurable_abs.inv.ennreal_ofReal
  have hfull : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹).restrict
      (Set.range (Units.val : ℝˣ → ℝ)) = volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹ := by
    rw [range_units_val]
    apply Measure.restrict_eq_self_of_ae_mem
    exact (withDensity_absolutelyContinuous _ _).ae_le (compl_mem_ae_iff.2 (measure_singleton 0))
  have h1 : Integrable (fun a : ℝˣ => g a) mulR ↔
      Integrable g (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹) := by
    rw [← hfull, ← hm.map_comap, hm.integrable_map_iff]
    rfl
  rw [h1, integrable_withDensity_iff_integrable_smul' hρ
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg _))]

theorem integrableOn_abs_rpow {r : ℝ} (hr : -1 < r) :
    IntegrableOn (fun x : ℝ => |x| ^ r) (Icc (-1) 1) volume := by
  have h0 : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume 0 1 := by
    refine (intervalIntegral.intervalIntegrable_rpow' hr).congr ?_
    intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    simp [abs_of_pos hx.1]
  have h1 : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simp only [abs_neg, neg_neg, neg_zero]
    exact h0.symm
  have h2 := h1.trans h0
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1 h2

theorem tateInt : LR.C.TateInt := by
  intro f e s hs
  let g : ℝ → ℂ := fun x => f x * ((if e ∧ x < 0 then -1 else 1) * ((|x| : ℝ) : ℂ) ^ s)
  have key : Integrable (fun x : ℝ => |x|⁻¹ • g x) volume := by
    have hsgn : Measurable fun x : ℝ => (if e ∧ x < 0 then (-1 : ℂ) else 1) := by
      refine Measurable.ite ?_ measurable_const measurable_const
      cases e
      · simp
      · simpa using measurableSet_lt measurable_id measurable_const
    have hpow : Measurable fun x : ℝ => ((|x| : ℝ) : ℂ) ^ s :=
      (Complex.measurable_ofReal.comp measurable_abs).pow_const s
    have hmeas : AEStronglyMeasurable (fun x : ℝ => |x|⁻¹ • g x) volume :=
      (measurable_abs.inv.smul (f.continuous.measurable.mul (hsgn.mul hpow))).aestronglyMeasurable
    have hbound : ∀ x : ℝ, ‖|x|⁻¹ • g x‖ ≤ ‖f x‖ * |x| ^ (s.re - 1) := by
      intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp only [abs_zero, inv_zero, zero_smul, norm_zero]
        exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg le_rfl _)
      · have hax : 0 < |x| := abs_pos.2 hx
        have hsg : ‖(if e ∧ x < 0 then (-1 : ℂ) else 1)‖ = 1 := by split_ifs <;> simp
        simp only [g]
        rw [norm_smul, norm_mul, norm_mul, hsg, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hax,
          Real.norm_eq_abs, abs_inv, abs_abs, Real.rpow_sub_one hax.ne']
        exact le_of_eq (by ring)
    have hC := SchwartzMap.norm_le_seminorm ℝ f
    have hr : -1 < s.re - 1 := by linarith
    have hI : IntegrableOn (fun x : ℝ => |x|⁻¹ • g x) (Icc (-1) 1) volume := by
      refine Integrable.mono' ((integrableOn_abs_rpow hr).const_mul ((SchwartzMap.seminorm ℝ 0 0) f)) hmeas.restrict ?_
      refine Filter.Eventually.of_forall fun x => (hbound x).trans ?_
      exact mul_le_mul_of_nonneg_right (hC x) (Real.rpow_nonneg (abs_nonneg x) _)
    have hO : IntegrableOn (fun x : ℝ => |x|⁻¹ • g x) (Icc (-1) 1)ᶜ volume := by
      refine Integrable.mono' (f.integrable_pow_mul volume ⌈s.re⌉₊).integrableOn hmeas.restrict ?_
      refine (ae_restrict_iff' measurableSet_Icc.compl).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have h1 : 1 ≤ |x| := by
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]
          linarith
        · rw [abs_of_pos (by linarith)]
          linarith
      refine (hbound x).trans ?_
      rw [Real.norm_eq_abs, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith [Nat.le_ceil s.re])
    have hU := hI.union hO
    rwa [Set.union_compl_self, integrableOn_univ] at hU
  exact (integrable_mulR_iff g).2 key

end GlobalTheory.CompanionTheory.RealTateConv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimensionStatement
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_variety_point_dimension : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ), CharZero ((MP ℤ m n).residueField x) → topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) → Geo.IsArithVar (ptIdeal x) d := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal | exact GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal | (intros; apply GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AuxiliaryCuspLemma
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem exists_twist_isNormalised : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, (∀ τ : E →+* ℂ, ∃ m, π.HasInfChar τ m) →
    ∃ s : ℂ, GlobalTheory.DiscSpec.IsNormalised (π.twist (GlobalTheory.CuspRep.Model.absC E s)) := by
  intro E _ _ _ a ha π hm
  choose m hm using hm
  have hN : (Fintype.card (E →+* ℂ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨-(∑ τ, (m τ).sum) / (a * Fintype.card (E →+* ℂ)), ?_⟩
  set s : ℂ := -(∑ τ, (m τ).sum) / (a * Fintype.card (E →+* ℂ)) with hs
  intro φ hφ t g
  have hsum : ∀ τ : E →+* ℂ, (∑ i : Fin a, Eop τ i i) φ = ((m τ).sum + a * s) • φ := fun τ => by
    have h1 := (hm τ).twist (GlobalTheory.CuspRep.Model.absC E s)
    rw [GlobalTheory.CuspRep.Model.expo_absC] at h1
    rw [GlobalTheory.T.trace_operator_eigenvalue_sum E a _ τ _ h1 φ hφ, Multiset.sum_map_add]
    simp [(hm τ).1]
  have hc : ∑ τ : E →+* ℂ, ((m τ).sum + a * s) = 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs]
    field_simp
    ring
  have hlie : lie E a (oneL E a) φ = (0 : ℂ) • φ := by
    rw [GlobalTheory.T.lie_central_element_trace E a, LinearMap.sum_apply, Finset.sum_congr rfl fun τ _ => hsum τ, ← Finset.sum_smul, hc]
  simpa using GlobalTheory.T.central_eigen_exponential E a φ 0 hlie t g

end GlobalTheory.CompanionTheory.Clozel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalSegmentsReverseOrdered
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.Canon

theorem isRevOrdered_of_isCanon {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k) : IsCanon Γ → IsRevOrdered Γ :=
  fun hc i j hij hp => (hc.1 i j hij).1 hp.2

end GlobalTheory.CompanionTheory.Canon
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapacityEquivalence
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem adjoin_lie_equiv {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    {U : Submodule ℂ (Sm E N)} (T : Sm E N →ₗ[ℂ] Sm E N) (hU : IsStable U)
    (hT : ∀ o, ∀ χ ∈ U, T (act o χ) = act o (T χ)) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Algebra.adjoin ℂ (Set.range (lie E N))) :
    ∀ χ ∈ U, z χ ∈ U ∧ T (z χ) = z (T χ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    exact fun χ hχ => ⟨hU (.lie X) χ hχ, hT (.lie X) χ hχ⟩
  | algebraMap c =>
    intro χ hχ
    simpa [Module.algebraMap_end_apply] using U.smul_mem c hχ
  | add x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨x₁, x₂⟩ := hx χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    exact ⟨by simpa using U.add_mem x₁ y₁, by simp [x₂, y₂]⟩
  | mul x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    obtain ⟨x₁, x₂⟩ := hx _ y₁
    exact ⟨by simpa [Module.End.mul_apply] using x₁, by simp [Module.End.mul_apply, x₂, y₂]⟩

theorem capEquiv : CapEquiv := by
  intro E _ _ _ N U T ψ m hU hT hψ hc τ u
  rw [← (adjoin_lie_equiv T hU hT (GlobalTheory.CentreSmooth.cap_mem τ u) ψ hψ).2, hc τ u, map_smul]

end GlobalTheory.CompanionTheory.EGlue

end
end

