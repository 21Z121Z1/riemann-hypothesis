import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.OfUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0377
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0098
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0433
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordHighestWeightVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdeleSplitSndDiagonal
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT bc UJ)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ClassFin

section Reduction

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem projFin_ratEmb_val (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (γ : GRat σ J) :
    (GlobalTheory.AdelicU.projFin σ J (ratEmb σ J γ)).1 = bc (inclR (Af F)) γ.1 := by
  refine Units.ext (Matrix.ext fun r s => ?_)
  change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] (γ.1.1 r s)) =
    (1 : Af F) ⊗ₜ[F] (γ.1.1 r s)
  simp

end Reduction

section Lattices

open GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume Module
open scoped Pointwise

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

end Lattices

end GlobalTheory.CompanionTheory.ClassFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorSpannedByWeightVectorsStatement
section
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_spanned_by_weight_vectors : ∀ {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A), (∀ k, φ (e (k, k)) t = rhoVec n k • t) → ∀ x : U n, φ x t = 0 → x ∈ Submodule.span ℂ {y : U n | ∃ μ : Fin n → ℤ, IsAdW μ y ∧ φ y t = 0} := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills | exact GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills | (intros; apply GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicNormFiniteNonzeroStatement
section
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_norm_finite_nonzero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
  ∀ φ : Sm E N, IsAutForm φ → IsSqInt φ.1 → φ ≠ 0 →
    (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ ⊤ ∧ (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.FinDisc.sqMass_ne_top_and_ne_zero | exact GlobalTheory.CompanionTheory.FinDisc.sqMass_ne_top_and_ne_zero | (intros; apply GlobalTheory.CompanionTheory.FinDisc.sqMass_ne_top_and_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSumStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_levi_factorization_sum : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (F : Sm E (r + s)), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → ∀ m : GA E r × GA E s, (cap (a := r + s) τ u F).1 (lev (Ad E) r s m) = (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) F)).1 (lev (Ad E) r s m) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi | exact GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi | (intros; apply GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirEqOfSingularWeightVectorStatement
section
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_eq_of_singular_weight_vector : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n), IsAdW μ x → (∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) → x ∉ Jp n → casC (fun k => rhoVec n k + (μ k : ℂ)) = casC (rhoVec n) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.casC_rho_add_eq | exact GlobalTheory.CompanionTheory.PresRho.casC_rho_add_eq | (intros; apply GlobalTheory.CompanionTheory.PresRho.casC_rho_add_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentredSegmentSquareIntegrableStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centred_segment_square_integrable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  first | exact @GlobalTheory.CompanionTheory.SegLink.centredSegSqInt | exact GlobalTheory.CompanionTheory.SegLink.centredSegSqInt | (intros; apply GlobalTheory.CompanionTheory.SegLink.centredSegSqInt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationIndep
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel

namespace GlobalTheory.CompanionTheory.ChernMass

theorem chernInt_eq_of_presents (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ)
    (r' : L'.ι → Y.Fnˣ) (hL : Presents Δ L r) (hL' : Presents Δ L' r')
    (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) L')
    (hφ : φ.IsCInf) (hψ : ψ.IsCInf) :
    φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  obtain ⟨ψ₀, hψ₀, hmass⟩ := GlobalTheory.T.chern_integral_presentation_transfer Y Δ L L' r r' hL hL' φ hφ
  rw [← hmass]
  exact GlobalTheory.T.chern_integral_weight_indep Y L' ψ₀ ψ hψ₀ hψ

end GlobalTheory.CompanionTheory.ChernMass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralRandomSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem measurable_gW (d : ℕ) (α : Type) [Fintype α] : Measurable (gW d α) := by
  unfold gW
  fun_prop

theorem encard_iUnion_fin {X : Type} {m : ℕ} (B : Fin m → Set X)
    (h : Pairwise (Function.onFun Disjoint B)) :
    (((⋃ t, B t).encard : ℕ∞) : ℝ≥0∞) = ∑ t, (((B t).encard : ℕ∞) : ℝ≥0∞) := by
  classical
  have key : ∀ s : Finset (Fin m), (((⋃ t ∈ s, B t).encard : ℕ∞) : ℝ≥0∞) =
      ∑ t ∈ s, (((B t).encard : ℕ∞) : ℝ≥0∞) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.set_biUnion_insert, Set.encard_union_eq, ENat.toENNReal_add,
        ih]
      exact Set.disjoint_iUnion₂_right.2 fun t ht => h (fun e => ha (e ▸ ht))
  simpa using key Finset.univ

theorem crofton : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∃ μ : Measure (Fin Y.dim → Fin n → ℂ), IsProbabilityMeasure μ ∧ μ ≪ volume ∧ (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernInt Y.dim Set.univ (fun _ => 1) = ∫ C, (({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℝ) ∂μ := by
  intro Y Δ L r hL n b hb _
  have := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  set φ := Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp) with hφdef
  have hφ : φ.IsCInf := Weight.isCInf_fsBasis hL b hb _ _
  have hneg : φ.chernPart Y.dim (-1) = 0 :=
    Weight.chernPart_neg_eq_zero hφ (Weight.semiPosReg_fsBasis hL b hb _ _)
  have hint := GlobalTheory.Published.ChernDegreeComplexModel.integrable Y φ hφ
  have hfin : φ.chernPart Y.dim 1 Set.univ ≠ ⊤ := by
    have h1 := hint.1
    rw [IntegrableOn, Measure.restrict_univ, integrable_const_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 one_ne_zero
    · exact ((isFiniteMeasure_iff _).1 (by simpa using h1)).ne

  let ι := AlgChart Y.str (RingHom.id ℂ) Y.dim × L.ι × Fin n
  let S : ι → Set (CxPts Y.str (RingHom.id ℂ)) := fun t => t.1.e.source ∩
    (ptsIn Y.str (RingHom.id ℂ) (L.U t.2.1) ∩ ptsIn Y.str (RingHom.id ℂ) (nonzeroLocus (b t.2.2)))
  have hSo : ∀ t, IsOpen (S t) := fun t =>
    t.1.e.open_source.inter ((isOpen_ptsIn _).inter (isOpen_ptsIn _))
  have hSc : (⋃ t, S t) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := Y.dim) (p := Y.str) (σ := RingHom.id ℂ) y
    obtain ⟨j, hj⟩ := exists_mem_ptsIn hb y
    exact Set.mem_iUnion.2 ⟨⟨c, pick hL y, j⟩, hc, mem_pick hL y, hj⟩
  obtain ⟨m, l, A, hdis, hun, hsub, hσ⟩ := GlobalTheory.T.sigma_compact_disjoint_refinement _ ι S hSo hSc
  set G : ℝ≥0∞ := ENNReal.ofReal (Real.pi ^ (Y.dim * n)) with hG
  have hGpos : G ≠ 0 := by
    rw [hG, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hGtop : G ≠ ⊤ := ENNReal.ofReal_ne_top
  let Z : (Fin Y.dim → Fin n → ℂ) → Set (CxPts Y.str (RingHom.id ℂ)) := fun C =>
    {y | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
      ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}
  let P : Fin m → (Fin Y.dim → Fin n → ℂ) → Set (CxPts Y.str (RingHom.id ℂ)) := fun t C =>
    {y | y ∈ A t ∧ ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
      ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}
  have hpiece : ∀ t, Measurable (fun C => (((P t C).encard : ℕ∞) : ℝ≥0∞)) ∧
      ∫⁻ C, gW Y.dim (Fin n) C * (((P t C).encard : ℕ∞) : ℝ≥0∞) =
        G * φ.chernPart Y.dim 1 (A t) := fun t =>
    GlobalTheory.T.measurable_local_zero_count Y L hL n b hb (l t).1 (l t).2.1 (l t).2.2 (A t)
      (fun y hy => (hsub t hy).1) (fun y hy => (hsub t hy).2.1)
      (fun y hy => (secVal_ne_zero_iff _ (hsub t hy).2.1).2 (hsub t hy).2.2) (hσ t)
  have hZ : ∀ C, (((Z C).encard : ℕ∞) : ℝ≥0∞) = ∑ t, (((P t C).encard : ℕ∞) : ℝ≥0∞) := by
    intro C
    rw [← encard_iUnion_fin]
    · congr 2
      ext y
      simp only [Set.mem_iUnion, P, Z, Set.mem_setOf_eq]
      constructor
      · intro h
        obtain ⟨t, ht⟩ := Set.mem_iUnion.1 (hun ▸ Set.mem_univ y)
        exact ⟨t, ht, h⟩
      · rintro ⟨t, -, h⟩
        exact h
    · intro s t hst
      exact (hdis hst).mono (fun y hy => hy.1) (fun y hy => hy.1)
  have hNm : Measurable fun C => (((Z C).encard : ℕ∞) : ℝ≥0∞) := by
    simp only [hZ]
    exact Finset.measurable_fun_sum _ fun t _ => (hpiece t).1
  have hAm : ∀ t, MeasurableSet (A t) := fun t => by
    obtain ⟨K, hK, e⟩ := hσ t
    rw [← e]
    exact MeasurableSet.iUnion fun i => (hK i).measurableSet
  have hmass : φ.chernPart Y.dim 1 Set.univ = ∑ t, φ.chernPart Y.dim 1 (A t) := by
    rw [← hun, measure_iUnion hdis hAm, tsum_fintype]
  have hgm := measurable_gW Y.dim (Fin n)
  have hsum : ∫⁻ C, gW Y.dim (Fin n) C * (((Z C).encard : ℕ∞) : ℝ≥0∞) =
      G * φ.chernPart Y.dim 1 Set.univ := by
    simp only [hZ, Finset.mul_sum]
    rw [lintegral_finset_sum Finset.univ (f := fun t C => gW Y.dim (Fin n) C *
      (((P t C).encard : ℕ∞) : ℝ≥0∞)) fun t _ => hgm.mul (hpiece t).1, hmass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => (hpiece t).2
  let μ : Measure (Fin Y.dim → Fin n → ℂ) := G⁻¹ • volume.withDensity (gW Y.dim (Fin n))
  have hlin : ∀ f : (Fin Y.dim → Fin n → ℂ) → ℝ≥0∞, Measurable f →
      ∫⁻ C, f C ∂μ = G⁻¹ * ∫⁻ C, gW Y.dim (Fin n) C * f C := by
    intro f hf
    rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hgm hf]
    rfl
  have hprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have h1 := hlin (fun _ => 1) measurable_const
    simp only [lintegral_one, mul_one] at h1
    rw [h1, GlobalTheory.T.gaussian_weight_total_mass, Fintype.card_fin]
    exact ENNReal.inv_mul_cancel hGpos hGtop
  have hN : ∫⁻ C, (((Z C).encard : ℕ∞) : ℝ≥0∞) ∂μ = φ.chernPart Y.dim 1 Set.univ := by
    rw [hlin _ hNm, hsum, ← mul_assoc, ENNReal.inv_mul_cancel hGpos hGtop, one_mul]
  refine ⟨μ, hprob, ?_, ?_⟩
  · exact (withDensity_absolutelyContinuous _ _).smul_left _
  · have hcast : ∀ C, ((Z C).ncard : ℝ) = ((((Z C).encard : ℕ∞) : ℝ≥0∞)).toReal := by
      intro C
      rw [Set.ncard]
      cases h : (Z C).encard with
      | top => simp
      | coe a => simp
    have hae : ∀ᵐ C ∂μ, (((Z C).encard : ℕ∞) : ℝ≥0∞) < ⊤ :=
      ae_lt_top hNm (by rw [hN]; exact hfin)
    have e := integral_toReal hNm.aemeasurable hae
    rw [hN] at e
    simp only [Z] at hcast e
    simp only [hcast]
    rw [e, Weight.chernInt, hneg]
    simp [Measure.real]
end GlobalTheory.CompanionTheory.FSCrofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordHighestWeightVectorStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clifford_highest_weight_vector : ∀ {n : ℕ} (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V),
    IsCoreMod (infOf lam) E1 E2 σ A → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ),
      IsCliff c → ∀ (τ : Fin n → ℝ) (x : ι → V), x ≠ 0 → Formalism.REAL.KHighest (fun _ => true) (yF (kF E1 E2) c) τ x →
        ∑ a, (m0 lam a) ^ 2 ≤ ∑ a, (τ a + rhoV n a) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.DiracK.dirac_ineq | exact GlobalTheory.CompanionTheory.DiracK.dirac_ineq | (intros; apply GlobalTheory.CompanionTheory.DiracK.dirac_ineq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationVanishingOnOpen
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Off

variable {k : Type} [Field k]

theorem sEmb_row (n : ℕ) (m : Mir k n) (j : Fin (n + 1 + 1)) :
    (((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)
      (Fin.castSucc (Fin.last n)) j = (1 : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) (Fin.castSucc (Fin.last n)) j := by
  have hs : ((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) =
      GlobalTheory.BZMir.glEmb k (n + 1) (m : GL (Fin (n + 1)) k) := rfl
  have hm : Matrix.vecMul (GlobalTheory.BZMir.eLast k n) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      GlobalTheory.BZMir.eLast k n := m.2
  rw [GlobalTheory.BZMir.vecMul_eLast] at hm
  rw [hs]
  show GlobalTheory.BZMir.glEmbMat k (n + 1) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (Fin.castSucc (Fin.last n)) j = _
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne]
  · simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]
    rw [hm]
    by_cases hj : j' = Fin.last n
    · subst hj
      simp [GlobalTheory.BZMir.eLast]
    · rw [Matrix.one_apply_ne (fun e => hj (Fin.castSucc_injective _ e).symm)]
      simp [GlobalTheory.BZMir.eLast, Pi.single_apply, hj]

theorem dEmb_mul_sEmb_mem_Cl (i t : ℕ) (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) :
    dEmb k i t d * sEmb k _ m ∈ Cl k i t := by
  simp only [Cl, Set.mem_ofPred_eq]
  intro c
  rw [_root_.mul_inv_rev, ← map_inv, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  simp_rw [sEmb_row]
  rw [← Matrix.mul_apply, Matrix.one_mul]
  show ((1 : Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k) -
      GlobalTheory.BZMir.colMat k (i + 1 + (t + 1)) (Fin.append 0 d)) _ _ = 0
  rw [Matrix.sub_apply]
  have hRC : (Fin.last (i + 1 + t)).castSucc ≠ (Fin.castLE (by omega) c : Fin (i + 1 + t + 1 + 1)) := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  have hCL : (Fin.castLE (by omega) c : Fin (i + 1 + t + 1 + 1)) ≠ Fin.last (i + 1 + (t + 1)) := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  rw [Matrix.one_apply_ne hRC]
  simp [GlobalTheory.BZMir.colMat, hCL]

end GlobalTheory.CompanionTheory.BZPhiPG.Off

open GlobalTheory.CompanionTheory.BZPhiPG.Off in

theorem GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
    eC ψ f = 0 := by
  intro k _ _ _ _ i t ψ τ σ hτ hσ f hf
  funext m
  have hz : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * sEmb k (i + 1 + t) m) = 0 :=
    fun d => hf _ (dEmb_mul_sEmb_mem_Cl i t d m)
  have hint : intC ψ f (sEmb k (i + 1 + t) m) = 0 := by
    unfold intC
    simp only [hz, smul_zero]
    unfold GlobalTheory.CompanionTheory.Rodier.smInt
    apply finsum_eq_zero_of_forall_eq_zero
    intro w
    by_cases hw : w = 0
    · rw [hw, smul_zero]
    · have hpre : ((fun _ => (0 : TensorProduct ℂ τ.V σ.V)) : (Fin (t + 1) → k) → TensorProduct ℂ τ.V σ.V) ⁻¹' {w} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h0 => hw h0.symm
      rw [hpre, MeasureTheory.measure_empty]
      simp
  simp only [eC, hint, map_zero, smul_zero, Pi.zero_apply]

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedPointsCountComplexStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_points_count_complex : ∀ (Y : Var ℂ) (Z : Set Y.X), (∀ x ∈ Z, IsClosed ({x} : Set Y.X)) → ({y : CxPts Y.str (RingHom.id ℂ) | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z}).ncard = Z.ncard := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.ncard_cxPts_over_closed | exact GlobalTheory.CompanionTheory.KoszulCount.ncard_cxPts_over_closed | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.ncard_cxPts_over_closed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionCongrEquiv
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CIndCongr

variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def mapFun (H : Subgroup G) {σ : Representation ℂ H W} {σ' : Representation ℂ H W'}
    (L : W ≃ₗ[ℂ] W') (hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w))
    (f : cIndSpace H σ) : cIndSpace H σ' :=
  have hind : (fun g => L (f.1.1.1 g)) ∈ indSpace H σ' := by
    intro h g
    have e : f.1.1.1 ((h : G) * g) = σ h (f.1.1.1 g) := f.1.1.2 h g
    show L (f.1.1.1 ((h : G) * g)) = σ' h (L (f.1.1.1 g))
    rw [e, hL]
  have hsm : (⟨fun g => L (f.1.1.1 g), hind⟩ : indSpace H σ') ∈ smoothPart (ind H σ') := by
    obtain ⟨K, hK, hKi⟩ := cInd_right_inv H σ f
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H σ') K hK _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show L (f.1.1.1 (g * x)) = L (f.1.1.1 g)
    rw [hKi g x hx]
  have hc : (⟨⟨fun g => L (f.1.1.1 g), hind⟩, hsm⟩ : smoothPart (ind H σ')) ∈ cIndSpace H σ' := by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g fun h0 => hg ?_⟩
    show L (f.1.1.1 g) = 0
    rw [h0, map_zero]
  ⟨⟨⟨fun g => L (f.1.1.1 g), hind⟩, hsm⟩, hc⟩

theorem mapFun_apply (H : Subgroup G) {σ : Representation ℂ H W} {σ' : Representation ℂ H W'}
    (L : W ≃ₗ[ℂ] W') (hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w))
    (f : cIndSpace H σ) (g : G) : (mapFun H L hL f).1.1.1 g = L (f.1.1.1 g) := rfl

theorem ext_fun {H : Subgroup G} {σ : Representation ℂ H W} {f f' : cIndSpace H σ}
    (h : ∀ g, f.1.1.1 g = f'.1.1.1 g) : f = f' :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem nonempty_equiv_cInd :
    ∀ {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (H : Subgroup G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'),
    σ.Equiv σ' → Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  intro G W W' _ _ _ _ _ _ _ H σ σ' e
  let L : W ≃ₗ[ℂ] W' := e.toLinearEquiv
  have hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w) := fun h w =>
    LinearMap.congr_fun (e.isIntertwining' h) w
  have hL' : ∀ (h : H) (w : W'), L.symm (σ' h w) = σ h (L.symm w) := fun h w => by
    apply L.injective
    rw [L.apply_symm_apply, hL, L.apply_symm_apply]
  let T : cIndSpace H σ ≃ₗ[ℂ] cIndSpace H σ' :=
    { toFun := mapFun H L hL
      map_add' := fun f f' => ext_fun fun g => map_add L (f.1.1.1 g) (f'.1.1.1 g)
      map_smul' := fun c f => ext_fun fun g => map_smul L c (f.1.1.1 g)
      invFun := mapFun H L.symm hL'
      left_inv := fun f => ext_fun fun g => L.symm_apply_apply (f.1.1.1 g)
      right_inv := fun f => ext_fun fun g => L.apply_symm_apply (f.1.1.1 g) }
  refine ⟨Representation.Equiv.mk T fun x => LinearMap.ext fun f => ext_fun fun g => ?_⟩
  rfl

end GlobalTheory.CompanionTheory.CIndCongr

end
end

