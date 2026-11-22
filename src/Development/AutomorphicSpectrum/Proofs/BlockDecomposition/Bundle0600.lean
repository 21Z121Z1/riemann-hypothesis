import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0574
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0575
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLattice
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem isLat_lam_of_matrix (K : Type) [Field K] [NumberField K] (m : ℕ)
    (c : Matrix (Fin m) (Fin m) K) : IsLat (lam c) := by
  have hL : IsLat (intVec K m) := isLat_intVec m
  refine ⟨Submodule.FG.sup hL.1 (Submodule.FG.map _ hL.1), ?_⟩
  rw [eq_top_iff, ← hL.2]
  exact Submodule.span_mono (fun v hv => (le_sup_left : intVec K m ≤ lam c) hv)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeGramIntegralAlmostAllStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_gram_integral_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)), hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.Grams.sub_gramH_mem_latH | exact GlobalTheory.CompanionTheory.SiegelND.Coef.Grams.sub_gramH_mem_latH | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.Grams.sub_gramH_mem_latH <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

theorem exists_ne_zero_smul_mem_of_mem_span {K : Type} [Field K] [NumberField K] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K)) {v : Fin m → K}
    (hv : v ∈ Submodule.span K (L : Set (Fin m → K))) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ L := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, mul_smul, mul_comm, mul_smul]
      rw [smul_comm a b x, smul_comm b a y]
    rw [e]
    exact L.add_mem (L.smul_mem _ hax) (L.smul_mem _ hby)
  | smul k x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      simpa using hd0
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have e : (d * a) • ((algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d) • x) = n • (a • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      field_simp
    rw [e]
    exact L.smul_mem _ hax

theorem torsionOf_quot_lat_ne_bot : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L →
    ∀ x : (Fin m → K) ⧸ L, Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x ≠ ⊥ := by
  intro K _ _ m L hL x h
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L x
  obtain ⟨a, ha, hav⟩ := exists_ne_zero_smul_mem_of_mem_span L
    (show v ∈ Submodule.span K (L : Set (Fin m → K)) by rw [hL.2]; trivial)
  have hmem : a ∈ Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) (Submodule.Quotient.mk v) := by
    rw [Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero L).2 hav
  rw [h] at hmem
  exact ha ((Submodule.mem_bot _).1 hmem)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSumPartialFourierUnfoldingStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sum_shift_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p₀ : Matrix (Fin V.rank) (Fin r) D.host.E) (q₀ : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s),
    ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 (y₁ + rat p₀) (y₂ + rat q₀) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 y₁ y₂ := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Period.tsum_cellTerm_add_rat | exact GlobalTheory.CompanionTheory.EisUnfold.Period.tsum_cellTerm_add_rat | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Period.tsum_cellTerm_add_rat <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionSkewAdjointL2Statement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_action_skew_adjoint_L2 : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a) (hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1), (∀ φ ∈ π.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) → ∀ (X : Lie E a) (φ ψ : π.V), inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm ψ) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) φ)) = -inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) ψ)) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm φ) := by
  first | exact @GlobalTheory.CompanionTheory.PeterssonSkew.lie_skew_adjoint | exact GlobalTheory.CompanionTheory.PeterssonSkew.lie_skew_adjoint | (intros; apply GlobalTheory.CompanionTheory.PeterssonSkew.lie_skew_adjoint <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTraceStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_central_element_trace : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := by
  first | exact @GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop | exact GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop | (intros; apply GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorGlRelations
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem glRel_EopV : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (τ : E →+* ℂ), Formalism.REAL.GlRel (EopV π τ) := by
  intro E _ _ _ a π τ i j k l
  have key := GlobalTheory.CompanionTheory.ClozelPurity.EopV_val E a π τ
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  have h := LinearMap.congr_fun (glRel_Eop (a := a) τ i j k l) φ.1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, key] at h ⊢
  split_ifs at h ⊢ <;> simpa [key] using h

end GlobalTheory.CompanionTheory.Clozel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorHermitianSkewStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_operator_hermitian_skew : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ), IsHerm π B → ∀ (τ : E →+* ℂ) (i j : Fin a) (φ ψ : π.V), B (EopV π τ i j φ) ψ = -B φ (EopV π (NumberField.ComplexEmbedding.conjugate τ) i j ψ) := by
  first | exact @GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint | exact GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint | (intros; apply GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorVectorEqStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_operator_vector_eq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (i j : Fin a) (φ : π.V), (EopV π τ i j φ).1 = Eop τ i j φ.1 := by
  first | exact @GlobalTheory.CompanionTheory.ClozelPurity.EopV_val | exact GlobalTheory.CompanionTheory.ClozelPurity.EopV_val | (intros; apply GlobalTheory.CompanionTheory.ClozelPurity.EopV_val <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalChartSheetDecomposition
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens

section Change

open Set

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB Y}

theorem restrict_chernPart_of_coords [SecondCountableTopology (GlobalTheory.CxPts q σ)] {φ : GlobalTheory.Weight q σ B} (h : φ.IsCInf)
    (ε : ℤˣ) (c : GlobalTheory.AlgChart q σ D) (e : OpenPartialHomeomorph (GlobalTheory.CxPts q σ) (Fin D → ℂ))
    (hsub : e.source ⊆ c.e.source) (hd : DifferentiableOn ℂ (c.finChart ∘ e.symm) e.target) {ρ : (Fin D → ℂ) → ℝ}
    (hρ : ∀ v ∈ e.target, ρ v = ‖LinearMap.det (fderiv ℂ (c.finChart ∘ e.symm) v :
      (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 * c.chernDens φ (e.symm v)) :
    (φ.chernPart D ε).restrict e.source =
      ((volume.restrict e.target).withDensity fun v => ENNReal.ofReal (((ε : ℤ) : ℝ) * ρ v)).map e.symm := by
  ext T hT
  set κ := c.finChart ∘ e.symm with hκ
  have ht := e.open_target.measurableSet
  have hs : AEMeasurable e.symm (volume.restrict e.target) := e.continuousOn_symm.aemeasurable ht
  have hS : MeasurableSet (T ∩ e.source) := hT.inter e.open_source.measurableSet
  have hSc : T ∩ e.source ⊆ c.finChart.source := inter_subset_right.trans hsub
  have hA : MeasurableSet (e.target ∩ e.symm ⁻¹' T) := by
    have hm : Measurable (e.target.restrict e.symm) :=
      (continuousOn_iff_continuous_restrict.1 e.continuousOn_symm).measurable
    have := ht.subtype_image (hm hT)
    convert this using 1
    ext v
    exact ⟨fun hv => ⟨⟨v, hv.1⟩, hv.2, rfl⟩, by rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩⟩
  have him : c.finChart.target ∩ c.finChart.symm ⁻¹' (T ∩ e.source) = κ '' (e.target ∩ e.symm ⁻¹' T) := by
    rw [← c.finChart.image_source_inter_eq', inter_eq_right.2 hSc]
    ext z
    constructor
    · rintro ⟨y, ⟨hyT, hys⟩, rfl⟩
      exact ⟨e y, ⟨e.map_source hys, by simpa only [mem_preimage, e.left_inv hys] using hyT⟩, by
        simp only [hκ, Function.comp_apply, e.left_inv hys]⟩
    · rintro ⟨v, ⟨hv, hvT⟩, rfl⟩
      exact ⟨e.symm v, ⟨hvT, e.map_target hv⟩, rfl⟩
  have hinj : InjOn κ (e.target ∩ e.symm ⁻¹' T) := fun v hv w hw hvw => by
    have h1 := c.finChart.injOn (hsub (e.map_target hv.1)) (hsub (e.map_target hw.1)) hvw
    exact e.symm.injOn hv.1 hw.1 h1
  have hder : ∀ v ∈ e.target ∩ e.symm ⁻¹' T, HasFDerivWithinAt κ
      ((fderiv ℂ κ v).restrictScalars ℝ) (e.target ∩ e.symm ⁻¹' T) v := fun v hv =>
    (((hd.differentiableAt (e.open_target.mem_nhds hv.1)).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  have hsc : AEMeasurable c.finChart.symm (volume.restrict c.finChart.target) :=
    c.finChart.continuousOn_symm.aemeasurable c.finChart.open_target.measurableSet
  have e1 : φ.chernPart D ε (T ∩ e.source) =
      ((φ.chernPart D ε).restrict c.finChart.source) (T ∩ e.source) := by
    rw [Measure.restrict_apply hS, inter_eq_left.2 hSc]
  rw [Measure.restrict_apply hT, e1, GlobalTheory.ChernMA.restrict_chernPart h ε c,
    Measure.map_apply_of_aemeasurable (hsc.mono_ac (withDensity_absolutelyContinuous _ _)) hS,
    Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hT,
    withDensity_apply', withDensity_apply', Measure.restrict_restrict' c.finChart.open_target.measurableSet,
    Measure.restrict_restrict' ht, inter_comm, him, inter_comm (e.symm ⁻¹' T),
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hder hinj]
  refine setLIntegral_congr_fun hA fun v hv => ?_
  have hdet : ((fderiv ℂ κ v).restrictScalars ℝ).det =
      Complex.normSq (LinearMap.det (fderiv ℂ κ v : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) :=
    ReciprocityTheory.AnForm.A.det_restrictScalars_real _
  have hleft : c.finChart.symm (κ v) = e.symm v := c.finChart.left_inv (hsub (e.map_target hv.1))
  simp only [hleft, hdet, hρ v hv.1]
  rw [abs_of_nonneg (Complex.normSq_nonneg _), ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]
  congr 1
  ring

end Change

section Piece

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {X : Scheme.{0}} (i : X ⟶ MP ℤ m n)

theorem mem_ptsIn_pre (W : (MP ℤ m n).Opens) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ W) ↔ PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ W := by
  rw [CxPts.mem_ptsIn, CxPts.mem_ptsIn]
  rfl

variable [IsClosedImmersion i] {D : ℕ} {e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ)}
  {Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ}

theorem differentiableOn_coords (hΓ : DifferentiableOn ℂ Γ e.target) (hover : ∀ v ∈ e.target, Over i (e.symm v) (Γ v))
    (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) (hsub : e.source ⊆ c.e.source) :
    DifferentiableOn ℂ (c.finChart ∘ e.symm) e.target := by
  refine differentiableOn_pi.2 fun a => ?_
  have h := (GlobalTheory.CompanionTheory.MixZ.Holo.holo m n X i D e.target Γ e.symm e.open_target hΓ hover).2 c.U (c.x a)
  refine (h.mono fun v hv => ⟨hv, c.source_subset (hsub (e.map_target hv))⟩).congr fun v hv => ?_
  exact c.finChart_eq_ev (hsub (e.map_target hv)) a

theorem maDensity_eq (Nh : GlobalTheory.HermLB (mpStr ℤ m n)) (B : HermLine (Bk n)) (hrep : IsHermRep Nh B)
    (hΓ : DifferentiableOn ℂ Γ e.target) (hover : ∀ v ∈ e.target, Over i (e.symm v) (Γ v))
    (hmc : ∀ v ∈ e.target, ∀ k, ∃ j, Γ v ⟨k, j⟩ ≠ 0) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D)
    (hsub : e.source ⊆ c.e.source) {v : Fin D → ℂ} (hv : v ∈ e.target) :
    maDensity (fun _ y' => Real.log (B.h (Γ y'))) v =
      ‖LinearMap.det (fderiv ℂ (c.finChart ∘ e.symm) v : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 *
        c.chernDens ((Nh.restr i).φ σ₀) (e.symm v) := by
  have hκd := differentiableOn_coords i hΓ hover c hsub
  set φ := (Nh.restr i).φ σ₀ with hφ
  have h : φ.IsCInf := (Nh.restr i).cInf σ₀
  set κ := c.finChart ∘ e.symm with hκ
  set y₀ := e.symm v with hy₀def
  have hy₀ : y₀ ∈ c.e.source := hsub (e.map_target hv)
  have hκv : AnalyticAt ℂ κ v := GlobalTheory.SCV.analyticAt_of_differentiableOn hκd (e.open_target.mem_nhds hv)
  have hκy : c.finChart.symm (κ v) = y₀ := c.finChart.left_inv hy₀
  have hz : κ v ∈ c.finChart.target := c.finChart.map_source hy₀
  have hma := h.maDens_eq c hz
  rw [hκy] at hma
  have hr : c.e y₀ = GlobalTheory.FinChart.toV D (κ v) := rfl
  have hd := h.contDiffAt c hy₀ (mem_pick φ.isLB y₀)
  rw [hr] at hd
  have hψ : ContDiffAt ℝ 2 (fun w => φ.locPot.φ y₀ (c.finChart.symm w)) (κ v) :=
    (hd.comp (κ v) (GlobalTheory.FinChart.toV D).contDiff.contDiffAt).div_const 2
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp (fun _ w => φ.locPot.φ y₀ (c.finChart.symm w)) κ v hκv (fun _ => hψ)
  rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hma] at hcomp
  have hC2 : ContDiffAt ℝ 2 ((fun w => φ.locPot.φ y₀ (c.finChart.symm w)) ∘ κ) v :=
    hψ.comp v (hκv.contDiffAt.restrict_scalars ℝ)
  obtain ⟨u, hu⟩ := (isHermRep_iff Nh B).1 hrep
  choose p hp using hmc v hv
  set b := pick φ.isLB y₀ with hbdef
  have hb : PtsOver.map i rfl _ y₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (Nh.B.U (b PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => PtsOver.map i rfl _ y₀) (fun _ => rfl) (mem_pick φ.isLB y₀) PUnit.unit
  have hmch : PtsOver.map i rfl _ y₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart p) :=
    (GlobalTheory.CompanionTheory.MixZ.Holo.mem_ptsIn_mchart p).2 fun k => ((hover v hv) k (p k)).1.2 (hp k)
  set W := i ⁻¹ᵁ (Nh.B.U (b PUnit.unit) ⊓ mchart p) with hW
  let f : Γ(X, W) := i.app _ (u (b PUnit.unit) p).val
  set O := e.target ∩ e.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W with hOdef
  have hO : IsOpen O := e.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  have hvO : v ∈ O := ⟨hv, (mem_ptsIn_pre i _ _).2 (mem_ptsIn_inf.2 ⟨hb, hmch⟩)⟩
  let g : (Fin D → ℂ) → ℂ := fun w => (∏ k, Γ w ⟨k, p k⟩ ^ B.a k) * ev (i ≫ mpStr ℤ m n) σ₀ W f (e.symm w)
  have hF : AnalyticAt ℂ (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ e.symm) v :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn
      ((GlobalTheory.CompanionTheory.MixZ.Holo.holo m n X i D e.target Γ e.symm e.open_target hΓ hover).2 W f) (hO.mem_nhds hvO)
  have hΓk (k) : AnalyticAt ℂ (fun w => Γ w ⟨k, p k⟩) v :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (differentiableOn_pi.1 hΓ _) (e.open_target.mem_nhds hv)
  have hg : AnalyticAt ℂ g v := (Finset.analyticAt_fun_prod _ fun k _ => (hΓk k).zpow (hp k)).mul hF
  have hunit : IsUnit f := (u (b PUnit.unit) p).isUnit.map (i.app _).hom
  have hg0 : g v ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hp k))
    (ev_ne_zero hvO.2 hunit)
  have hev : (fun w => Real.log (B.h (Γ w))) =ᶠ[𝓝 v]
      fun w => ((fun w => φ.locPot.φ y₀ (c.finChart.symm w)) ∘ κ) w + Real.log ‖g w‖ := by
    filter_upwards [hO.mem_nhds hvO] with w hw
    have hy : e.symm w ∈ c.e.source := hsub (e.map_target hw.1)
    have hmem := (mem_ptsIn_pre i _ _).1 hw.2
    have hrep' := hu.2.2 (b PUnit.unit) p (PtsOver.map i rfl _ (e.symm w)) (Γ w) (hover w hw.1) hmem
    have hzk : ∀ k, Γ w ⟨k, p k⟩ ≠ 0 := fun k =>
      ((hover w hw.1) k (p k)).1.1 (ptsIn_mono (mchart_le p k) (mem_ptsIn_inf.1 hmem).2)
    have hu0 : ev (i ≫ mpStr ℤ m n) σ₀ W f (e.symm w) ≠ 0 := ev_ne_zero hw.2 hunit
    have hev' : ev (i ≫ mpStr ℤ m n) σ₀ W f (e.symm w) =
        ev (mpStr ℤ m n) σ₀ _ (u (b PUnit.unit) p).val (PtsOver.map i rfl _ (e.symm w)) :=
      CxPts.ev_app i rfl _ _ _
    have hg0w : g w ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hzk k)) hu0
    have hnorm : ‖g w‖ = (∏ k, ‖Γ w ⟨k, p k⟩‖ ^ B.a k) *
        ‖ev (mpStr ℤ m n) σ₀ _ (u (b PUnit.unit) p).val (PtsOver.map i rfl _ (e.symm w))‖ := by
      simp only [g, norm_mul, norm_prod, norm_zpow, hev']
    have hφb : φ.φ b (e.symm w) = (Nh.φ σ₀).φ (b PUnit.unit) (PtsOver.map i rfl _ (e.symm w)) :=
      GlobalTheory.Weight.pull_φ _ i rfl b _
    have hleft : c.finChart.symm (κ w) = e.symm w := c.finChart.left_inv hy
    change Real.log (B.h (Γ w)) = φ.φ b (c.finChart.symm (κ w)) / 2 + Real.log ‖g w‖
    rw [hleft, hφb, hrep', ← hnorm, Real.log_mul (norm_ne_zero_iff.2 hg0w) (Real.exp_ne_zero _), Real.log_exp, add_comm]
  have hh : hessC (fun w => Real.log (B.h (Γ w))) v =
      hessC ((fun w => φ.locPot.φ y₀ (c.finChart.symm w)) ∘ κ) v :=
    (hessCGerm _ _ _ hev).trans (ReciprocityTheory.AnForm.A.hessC_add_log_norm _ g v hC2 hg hg0)
  change maDens (fun _ y' => Real.log (B.h (Γ y'))) v = _
  rw [maDens_congr_hessC _ (fun _ => (fun w => φ.locPot.φ y₀ (c.finChart.symm w)) ∘ κ) v fun _ => hh, hcomp]
  ring

theorem contDiffOn_log_metric {B : HermLine (Bk n)} (hB : IsSmoothHerm B) (hΓ : DifferentiableOn ℂ Γ e.target)
    (hmc : ∀ v ∈ e.target, ∀ k, ∃ j, Γ v ⟨k, j⟩ ≠ 0) :
    ContDiffOn ℝ 2 (fun y' => Real.log (B.h (Γ y'))) e.target := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Γ e.target :=
    (GlobalTheory.SCV.contDiffOn_of_differentiableOn e.open_target hΓ _).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' => B.h (Γ y')) e.target := hB.comp h1 hmc
  exact (h2.log fun v hv => (B.pos _ (hmc v hv)).ne').of_le (by norm_cast)

end Piece

theorem piece_density : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Nh : GlobalTheory.HermLB (mpStr ℤ m n)) (B : HermLine (Bk n)), IsHermRep Nh B → IsSmoothHerm B →
    ∀ (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
      [SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)]
      (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (N : Pol n)
      (e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ)) (Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ),
      GlobalTheory.CompanionTheory.MixZ.ArchEq.IsPiece i Ψ N e Γ →
      ContinuousOn (maDensity (fun _ y' => Real.log (B.h (Γ y')))) e.target ∧
      ∀ ε : ℤˣ, (((Nh.restr i).φ σ₀).chernPart D ε).restrict e.source =
        ((volume.restrict e.target).withDensity fun v =>
          ENNReal.ofReal (((ε : ℤ) : ℝ) * maDensity (fun _ y' => Real.log (B.h (Γ y'))) v)).map e.symm := by
  intro m n Nh B hrep hB X _ i _ D _ Ψ N e Γ hP
  obtain ⟨⟨c, hsub⟩, hΓ, hall⟩ := hP
  have hover : ∀ v ∈ e.target, Over i (e.symm v) (Γ v) := fun v hv => (hall v hv).1
  have hmc : ∀ v ∈ e.target, ∀ k, ∃ j, Γ v ⟨k, j⟩ ≠ 0 := fun v hv => (hall v hv).2.1.1
  refine ⟨ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ e.open_target fun _ => contDiffOn_log_metric i hB hΓ hmc, fun ε => ?_⟩
  exact restrict_chernPart_of_coords ((Nh.restr i).cInf σ₀) ε c e hsub (differentiableOn_coords i hΓ hover c hsub)
    fun v hv => maDensity_eq i Nh B hrep hΓ hover hmc c hsub hv

end GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCompactCoverByUnitScalingsStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_compact_cover_by_unit_scalings : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 2 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)), IsField (Fv F v ⊗[F] E) → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ), IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧ A ∩ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u i : Fv F v ⊗[F] E) * X p k) '' P := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.SphereCover.coverF | exact GlobalTheory.CompanionTheory.WeilSiegel.SphereCover.coverF | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.SphereCover.coverF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDependentSetNullStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_dependent_set_null : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → coordW (Fv F v) b lam 1 M {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}ᶜ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree.null_nonfree | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree.null_nonfree | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree.null_nonfree <;> assumption)
end

