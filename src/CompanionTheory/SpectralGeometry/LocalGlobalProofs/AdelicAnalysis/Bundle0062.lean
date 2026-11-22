import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScaling
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0060
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0006
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
import GroundTheory.GlobalFields.LocalAtPlace
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HarrisTaylorCardKilledByIdealEqAbsNormPow
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0061

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScalingStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_measure_scaling : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → (∀ (c : F), c ≠ 0 → ∀ s : Set (A F), MeasurableSet s → lf ((fun x => algebraMap F (A F) c * x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ c : ℚ) : ℝ)|⁻¹) * lf s) ∧ (∀ b : F, lf {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} = ((den b : ℝ≥0∞))⁻¹) ∧ ∀ (a : (A F)ˣ) (s : Set (A F)), MeasurableSet s → lf ((fun x => (a : A F) * x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) * lf s := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale | exact GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale | (intros; apply GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicLevelLatticeCompactOpenStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_level_lattice_compact_open : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ), 0 < N → IsCompact (latN F ι N : Set (ι → A F)) ∧ IsOpen (latN F ι N : Set (ι → A F)) ∧ ∀ a : ι → F, SB (indC N a) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.Lco.main | exact GlobalTheory.CompanionTheory.SW.ThW.Lco.main | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.Lco.main <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContDiffOnChartGlobalWhittakerCoefficient
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatCpt

theorem latV_compact_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)), IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM d b n M v
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  haveI : IsTopologicalRing (Fv F v) := inferInstance
  obtain ⟨-, -, -, -, -, -, hH, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  have hcoord := hH d b
  let H : (Fin n → Fin M → Fv F v ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → Fv F v) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => hcoord.homeomorph
  let O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v))
  have hOc : IsCompact O := GroundTheory.Global.isCompact_adicCompletionIntegers v
  have hOo : IsOpen O := Valued.isOpen_valuationSubring _
  let P : Set (Fin n → Fin M → Fin d → Fv F v) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => O
  have hE : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) = H ⁻¹' P := by
    ext Y
    simp only [latV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, P, O, SetLike.mem_coe]
    rfl
  have hPc : IsCompact P :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc
  have hPo : IsOpen P :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => hOo
  rw [hE]
  exact ⟨H.isCompact_preimage.2 hPc, hPo.preimage H.continuous⟩

end GlobalTheory.CompanionTheory.SW.LatCpt
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureTransport
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.EulerMove

theorem borel_ainf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := by
  obtain ⟨⟨-, scA, -⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have scA' : SecondCountableTopology (Ainf F × Af F) := scA
  haveI : SecondCountableTopology (Ainf F) :=
    (isEmbedding_prodMkLeft (0 : Af F)).secondCountableTopology
  haveI : T2Space (Ainf F) := GlobalTheory.CompanionTheory.AdeleTop.t2Space_infiniteAdeleRing_of_numberField_field F
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)).2.2.2.2.2.2.2.1 n M

theorem borel_af (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := by
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := lcA
  haveI := scA
  haveI := t2A
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)).2.2.2.2.2.2.2.1 n M

theorem borel_fv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.2.1 n M

theorem euler_move : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → IsEulerProd b I 1 minf m → IsEulerProd b (I.map e) 1 minf' m' := by
  intro F E _ _ _ _ _ σ hσ d b n M I minf minf' m m' e einf ev he heinf hev hcomm hgood cinf c hU
    hinf hloc hfin hE
  classical
  obtain ⟨-, hsum, S₀, hS₀⟩ := hE
  obtain ⟨hpi, hpf, hpv, hlat, hint, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b n M
  haveI := borel_af F E σ hσ n M
  haveI := borel_ainf F E σ hσ n M
  haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => borel_fv F E σ hσ n M v
  obtain ⟨S₁, hS₁⟩ := (GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F cinf cinf c c hU hU).2.2.2.2.2.2.2
  let S₂ : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hgood).toFinset
  have hS₂ : ∀ v, v ∉ S₂ → ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v := by
    intro v hv
    by_contra h
    exact hv (by simpa [S₂] using h)
  have hlatM : ∀ v, MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
    fun v => (hlat v).2.measurableSet
  have hcv : ∀ v, v ∉ S₁ ∪ S₂ → c v = 1 := fun v hv =>
    ((hS₁ (S₁ ∪ S₂) Finset.subset_union_left).1 v hv)
  have hmm : ∀ v, v ∉ S₁ ∪ S₂ → m' v (latV b v) = m v (latV b v) := by
    intro v hv
    have hv₂ : v ∉ S₂ := fun h => hv (Finset.mem_union_right _ h)
    have h1 := congrArg (fun μ => μ (latV b v)) (hloc v)
    simp only [Measure.map_apply (hev v) (hlatM v), hcv v hv, one_smul] at h1
    rw [← h1]
    congr 1
    ext X
    exact hS₂ v hv₂ X
  refine ⟨hfin, ?_, S₀ ∪ (S₁ ∪ S₂), ?_⟩
  · refine hsum.congr_cofinite ?_
    have hfinite : (↑(S₁ ∪ S₂) : Set (HeightOneSpectrum (𝓞 F))).Finite := Finset.finite_toSet (S₁ ∪ S₂)
    filter_upwards [hfinite.compl_mem_cofinite] with v hv
    rw [hmm v (by simpa using hv)]
  · intro S hS φinf φ hφinf hφ
    have hSS₀ : S₀ ⊆ S := Finset.union_subset_left hS
    have hSS₃ : S₁ ∪ S₂ ⊆ S := Finset.union_subset_right hS
    have hSS₁ : S₁ ⊆ S := Finset.union_subset_left hSS₃
    have hnot : ∀ v, v ∉ S → v ∉ S₁ ∪ S₂ := fun v hv h => hv (hSS₃ h)
    have hpm : Measurable (pureL b S φinf φ) := by
      refine Measurable.indicator ?_ (hint S).measurableSet
      refine (hφinf.comp hpi.measurable).mul ?_
      refine Finset.measurable_prod _ fun v _ => ?_
      exact (hφ v).comp ((hpv v).comp hpf).measurable
    have hmem : ∀ X, e X ∈ intOff b S ↔ X ∈ intOff b S := by
      intro X
      refine forall_congr' fun v => ?_
      refine imp_congr_right fun hv => ?_
      rw [(hcomm X).2 v]
      exact hS₂ v (fun h => hnot v hv (Finset.mem_union_right _ h)) _
    have hfun : (fun X => pureL b S φinf φ (e X)) =
        pureL b S (fun Y => φinf (einf Y)) (fun v Y => φ v (ev v Y)) := by
      funext X
      unfold pureL
      by_cases hX : X ∈ intOff b S
      · rw [Set.indicator_of_mem ((hmem X).2 hX), Set.indicator_of_mem hX, (hcomm X).1]
        congr 1
        exact Finset.prod_congr rfl fun v _ => by rw [(hcomm X).2 v]
      · rw [Set.indicator_of_notMem (fun h => hX ((hmem X).1 h)), Set.indicator_of_notMem hX]
    have hinfI : ∫⁻ Y, φinf (einf Y) ∂minf = (cinf : ℝ≥0∞) * ∫⁻ Y, φinf Y ∂minf' := by
      rw [← lintegral_map hφinf heinf, hinf, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    have hvI : ∀ v, ∫⁻ Y, φ v (ev v Y) ∂(m v) = (c v : ℝ≥0∞) * ∫⁻ Y, φ v Y ∂(m' v) := by
      intro v
      rw [← lintegral_map (hφ v) (hev v), hloc v, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    have hone : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by
      have := (hS₁ S hSS₁).2
      exact_mod_cast this
    have htail : (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) =
        ∏' v : {v // v ∉ S}, (m' v.1 (latV b v.1)).toReal :=
      tprod_congr fun v => by rw [hmm v.1 (hnot v.1 v.2)]
    rw [lintegral_map hpm he, hfun,
      hS₀ S hSS₀ (fun Y => φinf (einf Y)) (fun v Y => φ v (ev v Y)) (hφinf.comp heinf)
        (fun v => (hφ v).comp (hev v)), hinfI, htail]
    simp only [hvI]
    rw [Finset.prod_mul_distrib]
    congr 2
    calc (cinf : ℝ≥0∞) * (∫⁻ Y, φinf Y ∂minf') *
          ((∏ v ∈ S, (c v : ℝ≥0∞)) * ∏ v ∈ S, ∫⁻ Y, φ v Y ∂(m' v))
        = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) *
            ((∫⁻ Y, φinf Y ∂minf') * ∏ v ∈ S, ∫⁻ Y, φ v Y ∂(m' v)) := by ring
      _ = _ := by rw [hone, one_mul]

end GlobalTheory.CompanionTheory.SW.EulerMove
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeCosetParametrizationStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_coset_parametrization : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ)) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (a : ι → F) (N : ℕ), 0 < N → ∃ e : (ι × InfinitePlace F → ℤ) → ι → F, Function.Injective e ∧ (∀ x : ι → F, toA x - toA a ∈ latN F ι N ↔ x ∈ Set.range e) ∧ ∀ n, emb ρ (e n) = emb ρ a + gM ρ (fun v => b v) N *ᵥ fun p => (n p : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.rational_coset_param | exact GlobalTheory.CompanionTheory.SW.ThW.rational_coset_param | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.rational_coset_param <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ModulusCharacterUnitActionProductStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_character_unit_action_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (M : ℕ) (μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (μA : Measure (AF F)), μW.IsAddHaarMeasure → μA.IsAddHaarMeasure → ∃ χ : (AF F ⊗[F] E)ˣ →* ℝ≥0, Continuous χ ∧ (∀ a : (AF F ⊗[F] E)ˣ, (μW.prod μA).map (fun p => (sigR (AF F) σ (a : AF F ⊗[F] E) • p.1, Algebra.norm (AF F) (a : AF F ⊗[F] E) * p.2)) = χ a • μW.prod μA) ∧ ∀ x : ℝ, (χ (τ (Multiplicative.ofAdd x)) : ℝ) = Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * x)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi | exact GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi | (intros; apply GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.NonarchimedeanSelfdualMeasurePi
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiV

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

def ball (v : HeightOneSpectrum (𝓞 F)) (m : ℤ) : AddSubgroup (Fv F v) where
  carrier := {x | Valued.v x ≤ WithZero.exp m}
  add_mem' := by
    intro a b ha hb
    change Valued.v (a + b) ≤ _
    exact (Valuation.map_add _ a b).trans (max_le ha hb)
  zero_mem' := by
    change Valued.v (0 : Fv F v) ≤ _
    simp
  neg_mem' := by
    intro a ha
    change Valued.v (-a) ≤ _
    rw [Valuation.map_neg]
    exact ha

theorem mem_ball (m : ℤ) (x : Fv F v) : x ∈ ball v m ↔ Valued.v x ≤ WithZero.exp m := Iff.rfl

theorem ball_isCompact (m : ℤ) : IsCompact (ball v m : Set (Fv F v)) :=
  (GlobalTheory.LatticeDensity.ball_compact_open v m).1

theorem ball_isOpen (m : ℤ) : IsOpen (ball v m : Set (Fv F v)) :=
  (GlobalTheory.LatticeDensity.ball_compact_open v m).2

theorem ball_le {a b : ℤ} (hab : a ≤ b) : (ball v a : Set (Fv F v)) ⊆ ball v b :=
  fun _ hx => le_trans ((mem_ball _ _).1 hx) (WithZero.exp_le_exp.2 hab)

theorem exists_mem_ball (x : Fv F v) : ∃ m, x ∈ ball v m := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [mem_ball, hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), by rw [mem_ball, WithZero.exp_log hx]⟩

theorem exists_ball_of_isCompact (K : Set (Fv F v)) (hK : IsCompact K) :
    ∃ m, K ⊆ ball v m := by
  refine hK.elim_directed_cover (fun m : ℤ => (ball v m : Set (Fv F v))) ball_isOpen ?_
    (Monotone.directed_le fun a b hab => ball_le hab)
  intro x _
  obtain ⟨m, hm⟩ := exists_mem_ball x
  exact Set.mem_iUnion.2 ⟨m, hm⟩

theorem exists_ball_subset (U : Set (Fv F v)) (hU : U ∈ 𝓝 (0 : Fv F v)) :
    ∃ m, (ball v m : Set (Fv F v)) ⊆ U := by
  obtain ⟨W, hWU, hWo, h0⟩ := mem_nhds_iff.1 hU
  have hcl : ∀ m : ℤ, IsClosed (ball v m : Set (Fv F v)) := fun m => (ball_isCompact m).isClosed
  obtain ⟨n, hn⟩ := (ball_isCompact (v := v) 0).elim_directed_cover
    (fun n : ℕ => W ∪ (ball v (-(n : ℤ)) : Set (Fv F v))ᶜ)
    (fun n => hWo.union (hcl _).isOpen_compl)
    (by
      intro x _
      by_cases hx : x = 0
      · exact Set.mem_iUnion.2 ⟨0, Or.inl (hx ▸ h0)⟩
      · have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
        refine Set.mem_iUnion.2 ⟨(WithZero.log (Valued.v x)).natAbs + 1, Or.inr fun hm => ?_⟩
        have h1 := WithZero.exp_le_exp.1 ((WithZero.exp_log hv).le.trans ((mem_ball _ _).1 hm))
        omega)
    (Monotone.directed_le fun a b hab x hx => hx.imp id fun h hm =>
      h (ball_le (by omega) hm))
  refine ⟨min (-(n : ℤ)) 0, fun x hx => hWU ?_⟩
  rcases hn (ball_le (min_le_right _ _) hx) with h | h
  · exact h
  · exact absurd (ball_le (min_le_left _ _) hx) h

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y := by
  classical
  have h : pairA F 0 (singleV F v (x + y)) =
      pairA F 0 (singleV F v x) + pairA F 0 (singleV F v y) := by
    have : singleV F v (x + y) = singleV F v x + singleV F v y :=
      RestrictedProduct.single_add _ v x y
    rw [this]
    exact Prod.ext (add_zero (0 : Ainf F)).symm rfl
  rw [psiV, h, AddChar.map_add_eq_mul]
  rfl

theorem ann_isCompact {χ : Fv F v → ℂ} (hc : Continuous χ) (h0 : χ 0 = 1) {y : Fv F v} (hy : χ y ≠ 1)
    (L : AddSubgroup (Fv F v)) (hLo : IsOpen (L : Set (Fv F v))) :
    IsCompact {t | ∀ s ∈ L, χ (s * t) = 1} := by
  obtain ⟨m, hm⟩ := exists_ball_subset (L : Set (Fv F v)) (hLo.mem_nhds L.zero_mem)
  have hy0 : y ≠ 0 := fun h => hy (h ▸ h0)
  have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  have hcl : IsClosed {t | ∀ s ∈ L, χ (s * t) = 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun _ =>
      isClosed_eq (hc.comp (continuous_const.mul continuous_id)) continuous_const
  refine (ball_isCompact (v := v) (WithZero.log (Valued.v y) - m)).of_isClosed_subset hcl ?_
  intro t ht
  by_contra hne
  have hlt : WithZero.exp (WithZero.log (Valued.v y) - m) < Valued.v t :=
    not_le.1 fun h => hne h
  have hvt : Valued.v t ≠ 0 := (lt_of_le_of_lt zero_le' hlt).ne'
  have ht0 : t ≠ 0 := (Valuation.ne_zero_iff _).1 hvt
  have hmem : y / t ∈ ball v m := by
    rw [mem_ball, map_div₀, div_le_iff₀ (zero_lt_iff.2 hvt)]
    calc Valued.v y = WithZero.exp m * WithZero.exp (WithZero.log (Valued.v y) - m) := by
          rw [← WithZero.exp_add, add_sub_cancel, WithZero.exp_log hv]
      _ ≤ WithZero.exp m * Valued.v t := mul_le_mul_right hlt.le _
  have := ht _ (hm hmem)
  rw [div_mul_cancel₀ _ ht0] at this
  exact hy this

theorem selfDual_pi_v : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Measure (Fv F v)), SelfDual k (fun s t => psiV F ψ v (s * t)) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => k) (fun x y => psiV F ψ v (x ⬝ᵥ y)) := by
  intro F _ _ ψ hψ v k hk ι _
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hc, y, hy⟩ := (GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v
  have ha := psiV_add ψ v
  have hn : ∀ x, ‖psiV F ψ v x‖ = 1 := fun x => hψ.2.1 _
  refine GlobalTheory.CompanionTheory.SW.FourierPi.selfDual_pi (Fv F v) (psiV F ψ v) hc ha hn k hk
    ⟨ball v 0, ball_isCompact 0, ball_isOpen 0⟩
    (fun L _ hLo => ann_isCompact hc (GlobalTheory.CompanionTheory.SW.FourierPi.psi_zero ha hn) hy L hLo)
    (fun K hK => ?_) (fun U hU => ?_) ι
  · obtain ⟨m, hm⟩ := exists_ball_of_isCompact K hK
    exact ⟨ball v m, ball_isCompact m, ball_isOpen m, hm⟩
  · obtain ⟨m, hm⟩ := exists_ball_subset U hU
    exact ⟨ball v m, ball_isCompact m, ball_isOpen m, hm⟩

end GlobalTheory.CompanionTheory.SW.PiV
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PureAdelicFunctionMeasurable
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PureMeas

theorem borelSpace_ainf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := by
  obtain ⟨⟨-, scA, -⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have scA' : SecondCountableTopology (Ainf F × Af F) := scA
  haveI : SecondCountableTopology (Ainf F) :=
    (isEmbedding_prodMkLeft (0 : Af F)).secondCountableTopology
  haveI : T2Space (Ainf F) := GlobalTheory.CompanionTheory.AdeleTop.t2Space_infiniteAdeleRing_of_numberField_field F
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)).2.2.2.2.2.2.2.1 n M

theorem borelSpace_af (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := by
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := lcA
  haveI := scA
  haveI := t2A
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)).2.2.2.2.2.2.2.1 n M

theorem borelSpace_fv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.2.1 n M

theorem measurable_pureL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → Measurable (pureL b S φinf φ) := by
  intro F E _ _ _ _ _ σ hσ d b n M S φinf φ hφinf hφ
  obtain ⟨hpi, hpf, hpv, -, hint, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b n M
  haveI := borelSpace_af F E σ hσ n M
  haveI := borelSpace_ainf F E σ hσ n M
  haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => borelSpace_fv F E σ hσ n M v
  refine Measurable.indicator ?_ (hint S).measurableSet
  refine (hφinf.comp hpi.measurable).mul ?_
  refine Finset.measurable_prod _ fun v _ => ?_
  exact (hφ v).comp ((hpv v).comp hpf).measurable

end GlobalTheory.CompanionTheory.SW.PureMeas
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchwartzBruhatSpanIndicatorsStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_span_indicators : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (ι : Type) [Fintype ι] [DecidableEq ι] (χ : (ι → A F) → (ι → A F) → ℂ) (μ : Measure (ι → A F)), NADual (ι → A F) χ μ → (∀ N : ℕ, 0 < N → IsOpen (latN F ι N : Set (ι → A F))) → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∃ (s : Finset (ι → F)) (c : (ι → F) → ℂ), φ = ∑ a ∈ s, c a • indC N a := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators | exact GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueIntegrableStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_mean_value_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Measurable Φ → Integrable Φ (thetaMeas σ J μ 𝓕 S) → meanC μ 𝓕 (thetaS F E σ M J Φ S) = ∫ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaMean.mean_thetaS_eq_integral | exact GlobalTheory.CompanionTheory.SW.ThetaMean.mean_thetaS_eq_integral | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaMean.mean_thetaS_eq_integral <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueNonnegativeStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_mean_value_nonnegative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' X : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaLint.theta_lint_eq | exact GlobalTheory.CompanionTheory.SW.ThetaLint.theta_lint_eq | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaLint.theta_lint_eq <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_adelic_character : ∀ (F : Type) [Field F] [NumberField F], (∃ ψ : AddChar (A F) ℂ, IsStdChar F ψ) ∧ ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → (∀ x, ‖ψ x‖ = 1) ∧ (∀ x ∈ Oh F, ψ x = 1) ∧ ∀ b : F, (∀ x ∈ Oh F, ψ (algebraMap F (A F) b * x) = 1) ↔ ∀ r : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (b * (r : F)) = n := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.StdChar.main | exact GlobalTheory.CompanionTheory.SW.Core.StdChar.main | (intros; apply GlobalTheory.CompanionTheory.SW.Core.StdChar.main <;> assumption)
end

