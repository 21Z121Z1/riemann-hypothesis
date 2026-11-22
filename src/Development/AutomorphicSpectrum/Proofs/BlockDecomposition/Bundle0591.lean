import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0040
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanRankOneVolumeBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0005
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousScale
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0018
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.IsClosedImmersionLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0566
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0558
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0557
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanHermitianScalingByUnits
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.DiagScale

section Gen

theorem pi_map_scale_family {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (f : ι → X → X) (hf : ∀ i, Measurable (f i)) (c : ι → ℝ≥0) (h : ∀ i, μ.map (f i) = c i • μ) :
    (Measure.pi fun _ : ι => μ).map (fun x i => f i (x i)) =
      (∏ i, c i) • Measure.pi fun _ : ι => μ := by
  haveI : ∀ i, SigmaFinite (μ.map (f i)) := fun i => by rw [h i]; infer_instance
  rw [Measure.pi_map_pi (f := f) (fun i => (hf i).aemeasurable)]
  simp only [h]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
  push_cast
  rfl

theorem map_mul_scale {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [MeasurableSpace A] [BorelSpace A] (lam : Measure A) (u v : A) (c c' : ℝ≥0)
    (hu : lam.map (fun y => u * y) = c • lam) (hv : lam.map (fun y => v * y) = c' • lam) :
    lam.map (fun y => u * v * y) = (c * c') • lam := by
  have hm : ∀ x : A, Measurable (fun y : A => x * y) :=
    fun x => (continuous_const.mul continuous_id).measurable
  have e : (fun y => u * v * y) = (fun y => u * y) ∘ (fun y => v * y) := by
    funext y
    simp [mul_assoc]
  rw [e, ← Measure.map_map (hm u) (hm v), hv, Measure.map_smul, hu, smul_smul, mul_comm]

def mulU (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [MeasurableSpace A] [BorelSpace A] (u : Aˣ) : A ≃ᵐ A :=
  { toEquiv := Units.mulLeft u
    measurable_toFun := (continuous_const.mul continuous_id).measurable
    measurable_invFun := (continuous_const.mul continuous_id).measurable }

theorem prod_pairs {n : ℕ} (c : Fin n → ℝ≥0) :
    (∏ i, c i * c i) * ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (c p.1.1 * c p.1.2) ^ 2 =
      ∏ a, c a ^ (2 * n) := by
  classical
  set g : Fin n × Fin n → ℝ≥0 := fun x => c x.1 * c x.2 with hg
  have h1 : ∏ x : Fin n × Fin n, g x = (∏ a, c a) ^ (2 * n) := by
    rw [Fintype.prod_prod_type]
    simp only [hg, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_pow]
    ring
  have hU : ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2), g x =
      ∏ p : {p : Fin n × Fin n // p.1 < p.2}, g p :=
    Finset.prod_subtype _ (by simp) _
  have hL : ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.2 < x.1), g x =
      ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2), g x :=
    Finset.prod_equiv (Equiv.prodComm _ _) (by simp) (by simp [hg, mul_comm])
  have hD : ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 = x.2), g x =
      ∏ i, c i * c i := by
    symm
    refine Finset.prod_nbij' (fun i => (i, i)) Prod.fst (by simp) (by simp) (by simp) ?_ (by simp [hg])
    rintro ⟨a, b⟩ h
    simpa using (Finset.mem_filter.1 h).2
  have hS : ∏ x : Fin n × Fin n, g x =
      (∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2), g x) *
      ((∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 = x.2), g x) *
       (∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.2 < x.1), g x)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x : Fin n × Fin n => x.1 < x.2) g]
    congr 1
    rw [← Finset.prod_filter_mul_prod_filter_not
      (Finset.univ.filter (fun x : Fin n × Fin n => ¬ x.1 < x.2)) (fun x => x.1 = x.2) g,
      Finset.filter_filter, Finset.filter_filter]
    congr 1
    · refine Finset.prod_congr (Finset.filter_congr fun x _ => ?_) fun _ _ => rfl
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by simp [h], h⟩
    · refine Finset.prod_congr (Finset.filter_congr fun x _ => ?_) fun _ _ => rfl
      constructor
      · intro h
        exact lt_of_le_of_ne (not_lt.1 h.1) (fun e => h.2 e.symm)
      · intro h
        exact ⟨not_lt.2 h.le, h.ne'⟩
  have hP : ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (c p.1.1 * c p.1.2) ^ 2 =
      (∏ p : {p : Fin n × Fin n // p.1 < p.2}, g p) ^ 2 := by
    rw [Finset.prod_pow]
  have hT : ∏ a, c a ^ (2 * n) = (∏ a, c a) ^ (2 * n) := Finset.prod_pow _ _ _
  rw [hT, ← h1, hS, hL, hD, hU, hP]
  ring

end Gen

section H
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

theorem coordHerm_map_diag (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (lam : Measure R) [lam.IsAddHaarMeasure] {n : ℕ}
    (u : Fin n → Rˣ) (c : Fin n → ℝ≥0) (h : ∀ a, lam.map (fun y => (u a : R) * y) = c a • lam)
    (τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n) (hτm : Measurable τ)
    (hτ : ∀ S i j, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j =
      algebraMap R (R ⊗[F] E) (u i) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j *
        algebraMap R (R ⊗[F] E) (u j)) :
    (GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n).map τ =
      (∏ a, c a ^ (2 * n)) • GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  have hd : d = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hσ
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  obtain ⟨hK, -, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ R 2 b lam ‹_›
  haveI := hK
  haveI := hH n
  have hhom := GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6
  let φ := GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord R σ n
  let Q : Measure ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    Measure.pi fun _ => GlobalTheory.CompanionTheory.SW.coordK R b lam
  let P := (Measure.pi fun _ : Fin n => lam).prod Q
  have hν : GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n = Measure.comap φ P := rfl
  have hcond : Function.Injective φ ∧ ∀ s, MeasurableSet s → NullMeasurableSet (φ '' s) P := by
    by_contra hc
    have h0 : GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n = 0 := by
      rw [hν, Measure.comap, dif_neg hc]
    have := isOpen_univ.measure_pos (GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n) Set.univ_nonempty
    simp [h0] at this
  let D1 : (Fin n → R) ≃ᵐ (Fin n → R) :=
    MeasurableEquiv.piCongrRight fun i => mulU R (u i * u i)
  let D2 : ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) ≃ᵐ
      ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    MeasurableEquiv.piCongrRight fun p =>
      mulU (R ⊗[F] E) (Units.map (algebraMap R (R ⊗[F] E)).toMonoidHom (u p.1.1 * u p.1.2))
  have hsc : ∀ a a', lam.map (fun y => ((u a * u a' : Rˣ) : R) * y) = (c a * c a') • lam := by
    intro a a'
    rw [Units.val_mul]
    exact map_mul_scale lam _ _ _ _ (h a) (h a')
  have m1 : (Measure.pi fun _ : Fin n => lam).map D1 =
      (∏ i, c i * c i) • Measure.pi fun _ : Fin n => lam :=
    pi_map_scale_family lam (fun i y => ((u i * u i : Rˣ) : R) * y)
      (fun i => (continuous_const.mul continuous_id).measurable) _ (fun i => hsc i i)
  have m2 : Q.map D2 = (∏ p : {p : Fin n × Fin n // p.1 < p.2}, (c p.1.1 * c p.1.2) ^ 2) • Q :=
    pi_map_scale_family (GlobalTheory.CompanionTheory.SW.coordK R b lam)
      (fun (p : {p : Fin n × Fin n // p.1 < p.2}) y => algebraMap R (R ⊗[F] E) ((u p.1.1 * u p.1.2 : Rˣ) : R) * y)
      (fun p => (continuous_const.mul continuous_id).measurable) _
      (fun p => GlobalTheory.CompanionTheory.SW.Dil.coordK_map_unit R σ hσ b lam _ _ (hsc p.1.1 p.1.2))
  have hD : P.map (D1.prodCongr D2) = (∏ a, c a ^ (2 * n)) • P := by
    have e := Measure.map_prod_map (Measure.pi fun _ : Fin n => lam) Q D1.measurable D2.measurable
    rw [m1, m2, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, prod_pairs] at e
    exact e.symm
  rw [hν]
  refine GlobalTheory.CompanionTheory.SW.Dil.map_comap_scale φ P τ hτm (D1.prodCongr D2) _ hhom.surjective hcond.1 hcond.2 ?_ hD
  intro S
  refine Prod.ext ?_ ?_
  · funext i
    change algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i) =
      ((u i * u i : Rˣ) : R) * (algebraMap F R (1 / 2) *
        Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i))
    have e : algebraMap R (R ⊗[F] E) (u i) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i *
        algebraMap R (R ⊗[F] E) (u i) =
        ((u i * u i : Rˣ) : R) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i := by
      rw [Algebra.smul_def, Units.val_mul, map_mul]
      ring
    rw [hτ, e, map_smul, smul_eq_mul]
    ring
  · funext p
    change (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2 =
      algebraMap R (R ⊗[F] E) ((u p.1.1 * u p.1.2 : Rˣ) : R) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2
    rw [hτ, Units.val_mul, map_mul]
    ring

end H

theorem coordHerm_map_diag_ainf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S i j, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j = algebraMap (Ainf F) (Ainf F ⊗[F] E) (t i) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j * algebraMap (Ainf F) (Ainf F ⊗[F] E) (t j)) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (2 * n)) • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  intro F E _ _ _ _ _ σ hσ n d b lam hlam e he t ht τ hτm hτ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  exact coordHerm_map_diag (Ainf F) σ hσ b lam (fun a => (ht a).unit)
    (fun a => (∏ w, ‖e (t a) w‖₊)⁻¹)
    (fun a => GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar F e he lam hlam (t a) (ht a)) τ hτm hτ

end GlobalTheory.CompanionTheory.SW.DiagScale
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanRankOneVolumeBoundStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.SW.BB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_rank_one_volume_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → (∀ y w, |e y w| = ‖y w‖) → (∀ (A Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (Di : (InfinitePlace F → ℝ) → ℝ), Continuous Di → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) → ∀ f : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U) → ∀ (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ IsCompact {X : Fin 1 → Fin M → Ainf F ⊗[F] E | (fun w => xw e b X w) ∈ coreR δ R} ∧ ∀ A : Set (HermR (Ainf F) σ 1), MeasurableSet A → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' A) ∩ {X | (fun w => xw e b X w) ∈ coreR δ R}ᶜ, ENNReal.ofReal (φ X) ∂μ ≤ ENNReal.ofReal ε * ν A := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.InfTransport.smallDensity_transport | exact GlobalTheory.CompanionTheory.SW.BB.InfTransport.smallDensity_transport | (intros; apply GlobalTheory.CompanionTheory.SW.BB.InfTransport.smallDensity_transport <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanScaling
section
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HaarScale

theorem scaleInf : PositivityTheory.PfSWUS.SchInf.ScaleInf := by
  intro F E _ _ _ _ _ σ hσ n M μ ν hμ hν
  classical
  have hR : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨A, hA, hAf⟩ := exists_scale_tuples σ hσ (Ainf F) hR n M μ hμ
  obtain ⟨B, hB, hBf⟩ := exists_scale_herm σ hσ (Ainf F) hR n ν hν
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, hsig, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI := iB n M
  haveI := iTR
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := jB
  haveI := jT2
  have hs : ∀ x, σ (σ x) = x := GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ
  refine ⟨A, B, hA, hB, fun g hg => ?_⟩
  have hTc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [rmul]
    exact continuous_finset_sum _ fun c _ => ((continuous_apply_apply c i).mul continuous_const)
  have hTm : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g := hTc.measurable
  let τ₀ : HermR (Ainf F) σ n → HermR (Ainf F) σ n := fun S =>
    ⟨conjT (Ainf F) σ g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g, conj_mem (Ainf F) hs _ S⟩
  have hτ₀c : Continuous τ₀ := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have hcT : ∀ S : HermR (Ainf F) σ n, ((τ₀ S : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) =
      cT (sigR (Ainf F) σ) g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g := fun S => rfl
  have hB0 := hBf g hg τ₀ (fun S => rfl)
  refine ⟨?_, ?_, hAf g hg, fun τ hτ => ?_⟩
  · intro h0
    have h1 := hAf g hg
    rw [h0, zero_smul, Measure.map_eq_zero_iff hTm.aemeasurable] at h1
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := μ)).open_pos Set.univ isOpen_univ Set.univ_nonempty
      (by rw [h1]; simp)
  · intro h0
    rw [h0, zero_smul, Measure.map_eq_zero_iff hτ₀c.measurable.aemeasurable] at hB0
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := ν)).open_pos Set.univ isOpen_univ Set.univ_nonempty
      (by rw [hB0]; simp)
  · have : τ = τ₀ := funext fun S => Subtype.ext ((hτ S).trans (hcT S).symm)
    rw [this]
    exact hB0

end GlobalTheory.CompanionTheory.SW.HaarScale
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimension
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.DimVar

open Topology

theorem finiteType_of_chart {Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] {C : Type} [CommRing C]
    [Algebra ℤ C] (j : Spec (.of C) ⟶ Y) [IsOpenImmersion j] (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℤ C))) :
    Algebra.FiniteType ℤ C :=
  RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap ℤ C))).mp (hj ▸ inferInstance)

theorem topologicalKrullDim_closure_eq (Y : Scheme.{0}) (f : Y ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] (y : Y)
    [CharZero (Y.residueField y)] :
    topologicalKrullDim (closure ({y} : Set Y)) =
      (((Algebra.trdeg ℤ (Y.residueField y)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨B, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f y
  subst hq
  have := finiteType_of_chart f j hj
  rw [← GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y B j q inferInstance, ← topologicalKrullDim_range_inter_closure_eq j q]
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun z ↦ ?_)
    (IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  obtain ⟨C, _, _, j', _, y', hy, hj'⟩ := exists_affine_chart_over f z.1
  have := finiteType_of_chart f j' hj'
  obtain ⟨q', hq'⟩ := (specializes_iff_mem_closure.mpr z.2).mem_open
    j'.isOpenEmbedding.isOpen_range ⟨y', hy⟩
  refine ⟨Subtype.val ⁻¹' Set.range j',
    j'.isOpenEmbedding.isOpen_range.preimage continuous_subtype_val, ⟨y', hy⟩, ?_⟩
  rw [← topologicalKrullDim_eq_of_isEmbedding (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    (Z := Set.range j' ∩ closure {j q})
    (by rw [Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe, Set.inter_comm])]
  rw [topologicalKrullDim_range_inter_closure_eq j q, GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y B j q inferInstance]
  conv_lhs => rw [← hq', topologicalKrullDim_range_inter_closure_eq j' q']
  have h0 : CharZero (Y.residueField (j' q')) := hq' ▸ inferInstance
  rw [GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y C j' q' h0, hq']

theorem ptCoord_chart_ne_zero {m : ℕ} {n : Fin (m + 1) → ℕ} (x : MP ℤ m n) (k : Fin (m + 1)) :
    ptCoord x ⟨k, ptChart x k⟩ ≠ 0 := by
  simp [ptCoord, pullRatio_self]

theorem isArithVar_ptIdeal : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ), CharZero ((MP ℤ m n).residueField x) → topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) → Geo.IsArithVar (ptIdeal x) d := by
  intro m n x d hch hd
  have hdim := topologicalKrullDim_closure_eq (MP ℤ m n) (mpStr ℤ m n) x
  rw [hd] at hdim
  have h1 : ((d : ℕ∞)) = (Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat + 1 := WithBot.coe_injective hdim
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat = t := by
    refine ⟨(Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat.toNat, (ENat.coe_toNat ?_).symm⟩
    intro h
    rw [h] at h1
    exact ENat.coe_ne_top d (by simpa using h1)
  have hdt : d = t + 1 := by
    rw [ht] at h1
    exact_mod_cast h1
  subst hdt
  have htr : Algebra.trdeg ℤ (blockFnField (ptCoord x)) = t := by
    rw [GlobalTheory.T.function_field_of_point_coords_top m n x, GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.trdeg_top]
    exact Cardinal.toENat_eq_nat.mp ht
  exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_of_trdeg (ptCoord x) (ptChart x) (ptCoord_chart_ne_zero x) t htr

end GlobalTheory.CompanionTheory.MPDict.DimVar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinMapAbelianUniqueStatement
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_map_abelian_unique : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (Art Art' : Neutral.B1.IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K), Neutral.B1.IsGlobalArtinMap K Art → Neutral.B1.IsGlobalArtinMap K Art' → ∀ (L : IntermediateField K (AlgebraicClosure K)) (h : Neutral.B1.IsFiniteAbelian K L) (c : Neutral.B1.IdeleClassGroup K), Neutral.B1.abRestrict K L h (Art c) = Neutral.B1.abRestrict K L h (Art' c) := by
  first | exact @GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq | exact GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq | (intros; apply GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfoldingStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_weil_action_theta_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E), (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b →
    ∀ (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ (Φ : Mx D V.rank (r + s) → ℂ) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) (v : Mx D V.rank ((r + s) + (r + s))),
    xPart v = -HMul.hMul (colJoin y₁ (0 : Mx D V.rank s)) (rat a) →
    yPart v = HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) →
    ∀ (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E),
      Heisenberg₂ ψ V v Φ (rat (colJoin p q * a)) = cellTerm ψ V b a Φ p q y₁ y₂ := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Summand.summand | exact GlobalTheory.CompanionTheory.EisUnfold.Summand.summand | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Summand.summand <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoxFourierIntegralBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_fourier_integral_bound : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, (∀ x, ‖ψ x‖ = 1) → Continuous ψ → ∀ (L : AddSubgroup (Af E)), IsCompact (L : Set (Af E)) → IsOpen (L : Set (Af E)) → ∀ (c z : Fin k → Af E), ‖∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k‖ ≤ (nuFin E k).real (boxL (L : Set (Af E)) c) ∧ (∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k ≠ 0 → ∀ i, ∀ a ∈ L, ψ (sFin E (a * z i)) = 1) := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.FinFT.box_fourier_main | exact GlobalTheory.CompanionTheory.CutOff.FinFT.box_fourier_main | (intros; apply GlobalTheory.CompanionTheory.CutOff.FinFT.box_fourier_main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponentialStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_eigen_exponential : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (c : ℂ), lie E a (oneL E a) φ = c • φ → ∀ (t : ℝ) (g : GA E a), φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre | exact GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre | (intros; apply GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterQuadraticTrace
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ChzConj

theorem chz_conj : ∀ (D : D7) (ρ p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (b : Mx D p p) (y : Mx D ρ p) (z₀ : hermA D ρ),
  z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) →
    chz ψ b₀ z₀ = ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p))) := by
  intro D ρ p ψ b₀ b y z₀ hz
  unfold chz pr
  rw [hz]
  congr 2
  change Matrix.trace (Matrix.map b₀.1 (incA D) * ((y * b) * adj y)) = Matrix.trace (b * (adj y * (Matrix.map b₀.1 (incA D) * y)))
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.ChzConj

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterIntegralOrthogonalityStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_integral_orthogonality : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (s : ℕ)
    (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)), IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ q : Matrix (Fin V.rank) (Fin s) D.host.E,
      (q = 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 1) ∧
      (q ≠ 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 0) := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality | exact GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernPartNullSetZero
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

namespace GlobalTheory.CompanionTheory.MixZ

theorem chernPart_null_of_chart_null : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB X} (φ : GlobalTheory.Weight q σ B)
    (ε : ℤˣ) (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) → φ.chernPart D ε Z = 0 := by
  intro k _ X q σ D B φ ε Z hZ hc
  have hchart : ∀ (c : GlobalTheory.AlgChart q σ D) (ρ : GlobalTheory.CxPts q σ → ENNReal),
      GlobalTheory.ChartGlue.chartMeas c.e ρ Z = 0 := by
    intro c ρ
    unfold GlobalTheory.ChartGlue.chartMeas
    by_cases hf : AEMeasurable c.e.symm ((volume.restrict c.e.target).withDensity (ρ ∘ c.e.symm))
    · rw [Measure.map_apply_of_aemeasurable hf hZ]
      refine withDensity_absolutelyContinuous _ _ ?_
      rw [Measure.restrict_apply' c.e.open_target.measurableSet, Set.inter_comm]
      exact hc c
    · simp [Measure.map_of_not_aemeasurable hf]
  have hle : ∀ ρ : GlobalTheory.AlgChart q σ D → GlobalTheory.CxPts q σ → ENNReal,
      GlobalTheory.ChartGlue.glueMeas (fun c : GlobalTheory.AlgChart q σ D => c.e) ρ ≤
        (GlobalTheory.ChartGlue.glueMeas (fun c : GlobalTheory.AlgChart q σ D => c.e) ρ).restrict Zᶜ := by
    intro ρ
    unfold GlobalTheory.ChartGlue.glueMeas
    refine iSup_le fun c => ?_
    have hae : ∀ᵐ y ∂(GlobalTheory.ChartGlue.chartMeas c.e (ρ c)), y ∈ Zᶜ := by
      rw [ae_iff]
      simpa using hchart c (ρ c)
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact Measure.restrict_mono subset_rfl
      (le_iSup (fun c : GlobalTheory.AlgChart q σ D => GlobalTheory.ChartGlue.chartMeas c.e (ρ c)) c)
  have h3 : φ.chernPart D ε Z ≤ (φ.chernPart D ε).restrict Zᶜ Z :=
    Measure.le_iff'.mp (hle fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) Z
  rw [Measure.restrict_apply hZ, Set.inter_compl_self, measure_empty] at h3
  exact nonpos_iff_eq_zero.mp h3

end GlobalTheory.CompanionTheory.MixZ
end
end

