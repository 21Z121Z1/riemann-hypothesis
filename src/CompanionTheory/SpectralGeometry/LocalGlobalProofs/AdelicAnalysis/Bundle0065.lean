import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaust
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0064
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0006
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RealQuadraticFormLemma
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOperatorIntegralInvariance

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaustStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_boxes_compact_exhaust : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ (N : ℕ) (r : ℝ), 0 < N → IsCompact (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E))) ∧ (∀ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C → ∃ (N : ℕ) (r : ℝ), 0 < N ∧ 0 < r ∧ C ⊆ box b N r) ∧ ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (N : ℕ) (r x : ℝ) (X : Fin n → Fin M → AF F ⊗[F] E), ((τ (Multiplicative.ofAdd (x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X ∈ box b N (Real.exp x * r) ↔ X ∈ box b N r := by
  first | exact @GlobalTheory.CompanionTheory.SW.BoxF.box_facts | exact GlobalTheory.CompanionTheory.SW.BoxF.box_facts | (intros; apply GlobalTheory.CompanionTheory.SW.BoxF.box_facts <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChangeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_measure_linear_change : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ g : Matrix ι ι F, g.det ≠ 0 → ∀ s : Set (ι → A F), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => Bf g *ᵥ x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) * (Measure.pi fun _ : ι => lf) s) ∧ ∀ (a : (A F)ˣ) (s : Set (ι → A F)), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => (a : A F) • x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) ^ Fintype.card ι * (Measure.pi fun _ : ι => lf) s := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale | exact GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale | (intros; apply GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicLatticeMeasureFormulaStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_lattice_measure_formula : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (N : ℕ), 0 < N → (muF B lf (latN F ι N : Set (ι → A F))).toReal = kap F ^ Fintype.card ι * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * (((N : ℝ) ^ Module.finrank ℚ F)⁻¹) ^ Fintype.card ι := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.muF_latN | exact GlobalTheory.CompanionTheory.SW.ThW.muF_latN | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.muF_latN <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicPrimitiveVectorCompactRescale
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PrimA

def phiInf (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    AF F ⊗[F] E →+* Ainf F ⊗[F] E :=
  (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

def phiV (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : AF F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom.comp
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

theorem unimodular_compact_mod_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ),
    ∃ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω ∧
      ∀ y : Fin 1 → Fin M → AF F ⊗[F] E, (∃ z : Fin M → AF F ⊗[F] E, z ⬝ᵥ y 0 = 1) →
        ∃ (a : (AF F ⊗[F] E)ˣ) (z : Fin 1 → Fin M → AF F ⊗[F] E),
          (a : AF F ⊗[F] E) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : AF F ⊗[F] E) • y) 0 = 1 := by
  intro F E _ _ _ _ _ σ hCM M
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨-, almM, glueM, cptM⟩ := GlobalTheory.T.adelic_tuple_local_global_properties F E σ hCM _ b 1 M
  obtain ⟨ext1, alm1, glue1, -⟩ := GlobalTheory.T.adelic_tuple_local_global_properties F E σ hCM _ b 1 1
  obtain ⟨Ωi, hΩi, hi⟩ := GlobalTheory.T.archimedean_primitive_vector_compact_rescale F E σ hCM M
  choose Ωv hΩv hv using GlobalTheory.T.local_primitive_vector_compact_rescale F E σ hCM M
  obtain ⟨good, hgoodEv, hgood⟩ : ∃ good : HeightOneSpectrum (𝓞 F) → Prop,
      (∀ᶠ v in Filter.cofinite, good v) ∧ ∀ v, good v →
        ∀ y : Fin 1 → Fin M → Fv F v ⊗[F] E, (∃ z : Fin M → Fv F v ⊗[F] E, z ⬝ᵥ y 0 = 1) →
          ∃ (a : (Fv F v ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Fv F v ⊗[F] E),
            (a : Fv F v ⊗[F] E) • y ∈ latV b v ∧ z ∈ latV b v ∧
              z 0 ⬝ᵥ ((a : Fv F v ⊗[F] E) • y) 0 = 1 :=
    ⟨_, GlobalTheory.T.primitive_vector_lattice_rescale_almost_all F E σ hCM _ b M, fun _ h => h⟩
  classical
  obtain ⟨Cv, hCg, hCb⟩ : ∃ Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, good v → Cv v = latV b v) ∧ (∀ v, ¬ good v → Cv v = Ωv v) :=
    ⟨fun v => if good v then latV b v else Ωv v, fun v h => if_pos h, fun v h => if_neg h⟩
  have hCcpt : ∀ v, IsCompact (Cv v) := by
    intro v
    by_cases h : good v
    · rw [hCg v h]; exact (GlobalTheory.T.contDiffOn_chart_globalWhittakerCoefficient F E σ hCM _ b 1 M v).1
    · rw [hCb v h]; exact hΩv v
  have hClat : ∀ᶠ v in Filter.cofinite, Cv v ⊆ latV b v :=
    hgoodEv.mono fun v h => (hCg v h).le
  have extK : ∀ x y : AF F ⊗[F] E, phiInf F E x = phiInf F E y →
      (∀ v, phiV F E v x = phiV F E v y) → x = y := by
    intro x y h1 h2
    have := ext1 (fun _ _ => x) (fun _ _ => y) (by funext a i; exact h1)
      (fun v => by funext a i; exact h2 v)
    exact congrFun (congrFun this 0) 0
  have oneLat : ∀ᶠ v in Filter.cofinite,
      (fun _ _ => 1 : Fin 1 → Fin 1 → Fv F v ⊗[F] E) ∈ latV b v := by
    refine (alm1 (fun _ _ => 1)).mono fun v hv => ?_
    have e : (projV v (projFin (fun _ _ => (1 : AF F ⊗[F] E))) : Fin 1 → Fin 1 → Fv F v ⊗[F] E) =
        fun _ _ => 1 := by
      funext a i; exact map_one (phiV F E v)
    rwa [e] at hv
  have glueK : ∀ (xi : Ainf F ⊗[F] E) (xv : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v ⊗[F] E),
      (∀ᶠ v in Filter.cofinite, xv v = 1) →
      ∃ x : AF F ⊗[F] E, phiInf F E x = xi ∧ ∀ v, phiV F E v x = xv v := by
    intro xi xv h
    obtain ⟨X, h1, h2⟩ := glue1 (fun _ _ => xi) (fun v _ _ => xv v) ((h.and oneLat).mono fun v hv => by
      have e : (fun _ _ => xv v : Fin 1 → Fin 1 → Fv F v ⊗[F] E) = fun _ _ => 1 := by
        funext a i; exact hv.1
      rw [e]; exact hv.2)
    exact ⟨X 0 0, congrFun (congrFun h1 0) 0, fun v => congrFun (congrFun (h2 v) 0) 0⟩
  refine ⟨{X | projInf X ∈ Ωi ∧ ∀ v, projV v (projFin X) ∈ Cv v}, cptM Ωi Cv hΩi hCcpt hClat, ?_⟩
  rintro y ⟨z₀, hz₀⟩
  have hzi : (fun i => phiInf F E (z₀ i)) ⬝ᵥ projInf y 0 = 1 := by
    have := congrArg (phiInf F E) hz₀
    rw [map_one, RingHom.map_dotProduct] at this
    exact this
  obtain ⟨ai, zi, hai, hzi', hidi⟩ := hi (projInf y) ⟨_, hzi⟩
  have hzv : ∀ v, (fun i => phiV F E v (z₀ i)) ⬝ᵥ projV v (projFin y) 0 = 1 := by
    intro v
    have := congrArg (phiV F E v) hz₀
    rw [map_one, RingHom.map_dotProduct] at this
    exact this
  have loc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ (a : (Fv F v ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Fv F v ⊗[F] E),
      (a : Fv F v ⊗[F] E) • projV v (projFin y) ∈ Cv v ∧ z ∈ Cv v ∧
        z 0 ⬝ᵥ ((a : Fv F v ⊗[F] E) • projV v (projFin y)) 0 = 1 ∧
        (good v → projV v (projFin y) ∈ latV b v →
          (fun _ i => phiV F E v (z₀ i) : Fin 1 → Fin M → Fv F v ⊗[F] E) ∈ latV b v → a = 1) := by
    intro v
    by_cases hg : good v
    · by_cases hy : projV v (projFin y) ∈ latV b v ∧
          (fun _ i => phiV F E v (z₀ i) : Fin 1 → Fin M → Fv F v ⊗[F] E) ∈ latV b v
      · refine ⟨1, fun _ i => phiV F E v (z₀ i), ?_, ?_, ?_, fun _ _ _ => rfl⟩
        · rw [hCg v hg, Units.val_one, one_smul]; exact hy.1
        · rw [hCg v hg]; exact hy.2
        · rw [Units.val_one, one_smul]; exact hzv v
      · obtain ⟨a, z, h1, h2, h3⟩ := hgood v hg _ ⟨_, hzv v⟩
        refine ⟨a, z, ?_, ?_, h3, fun _ h h' => absurd ⟨h, h'⟩ hy⟩
        · rw [hCg v hg]; exact h1
        · rw [hCg v hg]; exact h2
    · obtain ⟨a, z, h1, h2, h3⟩ := hv v _ ⟨_, hzv v⟩
      refine ⟨a, z, ?_, ?_, h3, fun h => absurd h hg⟩
      · rw [hCb v hg]; exact h1
      · rw [hCb v hg]; exact h2
  choose av zv hav hzv' hidv ha1 using loc
  have ae1 : ∀ᶠ v in Filter.cofinite, av v = 1 := by
    filter_upwards [hgoodEv, almM y, almM (fun _ i => z₀ i)] with v h1 h2 h3
    exact ha1 v h1 h2 h3
  obtain ⟨a, ha_i, ha_v⟩ := glueK (ai : Ainf F ⊗[F] E) (fun v => (av v : Fv F v ⊗[F] E))
    (ae1.mono fun v h => by simp [h])
  obtain ⟨a', ha'_i, ha'_v⟩ := glueK ((ai⁻¹ : (Ainf F ⊗[F] E)ˣ) : Ainf F ⊗[F] E)
    (fun v => (((av v)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E))
    (ae1.mono fun v h => by simp [h])
  have haa : a * a' = 1 := by
    refine extK _ _ ?_ fun v => ?_
    · rw [map_mul, map_one, ha_i, ha'_i, Units.mul_inv]
    · rw [map_mul, map_one, ha_v, ha'_v, Units.mul_inv]
  obtain ⟨Z, hZi, hZv⟩ := glueM zi zv (hgoodEv.mono fun v h => by
    have := hzv' v
    rwa [hCg v h] at this)
  have eI : projInf ((a : AF F ⊗[F] E) • y) = (ai : Ainf F ⊗[F] E) • projInf y := by
    funext p i
    show phiInf F E (a * y p i) = (ai : Ainf F ⊗[F] E) * phiInf F E (y p i)
    rw [map_mul, ha_i]
  have eV : ∀ v, projV v (projFin ((a : AF F ⊗[F] E) • y)) =
      (av v : Fv F v ⊗[F] E) • projV v (projFin y) := by
    intro v
    funext p i
    show phiV F E v (a * y p i) = (av v : Fv F v ⊗[F] E) * phiV F E v (y p i)
    rw [map_mul, ha_v]
  refine ⟨⟨a, a', haa, by rw [mul_comm]; exact haa⟩, Z, ⟨?_, fun v => ?_⟩, ⟨?_, fun v => ?_⟩, ?_⟩
  · show projInf ((a : AF F ⊗[F] E) • y) ∈ Ωi
    rw [eI]; exact hai
  · show projV v (projFin ((a : AF F ⊗[F] E) • y)) ∈ Cv v
    rw [eV]; exact hav v
  · rw [hZi]; exact hzi'
  · rw [hZv]; exact hzv' v
  · show Z 0 ⬝ᵥ ((a : AF F ⊗[F] E) • y) 0 = 1
    refine extK _ _ ?_ fun v => ?_
    · rw [map_one, RingHom.map_dotProduct]
      have e1 : (phiInf F E ∘ Z 0) = zi 0 := by
        funext i; exact congrFun (congrFun hZi 0) i
      have e2 : (phiInf F E ∘ ((a : AF F ⊗[F] E) • y) 0) = ((ai : Ainf F ⊗[F] E) • projInf y) 0 := by
        funext i; exact congrFun (congrFun eI 0) i
      rw [e1, e2]; exact hidi
    · rw [map_one, RingHom.map_dotProduct]
      have e1 : (phiV F E v ∘ Z 0) = zv v 0 := by
        funext i; exact congrFun (congrFun (hZv v) 0) i
      have e2 : (phiV F E v ∘ ((a : AF F ⊗[F] E) • y) 0) =
          ((av v : Fv F v ⊗[F] E) • projV v (projFin y)) 0 := by
        funext i; exact congrFun (congrFun (eV v) 0) i
      rw [e1, e2]; exact hidv v

end GlobalTheory.CompanionTheory.SW.PrimA
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DualLatticeMembershipTraceStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_membership_trace : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ), IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), 0 < N → ∀ y : ι → F, toA y ∈ perp (chiB ψ (Bf B)) (latN F ι N : Set (ι → A F)) ↔ ∀ i v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.toA_mem_perp_latN_iff | exact GlobalTheory.CompanionTheory.SW.ThW.toA_mem_perp_latN_iff | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.toA_mem_perp_latN_iff <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSumStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_thetaMeas_block_one_eq_rank_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (μ : Measure (HA (AF F) σ (blockOne (algebraMap F E t) J))) 𝓕, IsHaarH F E σ (M + 1) _ μ → IsFDH F E σ (M + 1) _ μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ (Φ : (Fin (n + 1) → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), Ψ (actW (AF F) σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, Φ (actW (AF F) σ _ h (consTup X)) ∂(thetaMeas σ J μ₁ 𝓕₁ {X | gramE σ J X = T})) → ∫⁻ X, Φ X ∂(thetaMeas σ _ μ 𝓕 {X | gramE σ (blockOne (algebraMap F E t) J) X = blockOne (algebraMap F E t) T}) = ∫⁻ y, Ψ y ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaStage.theta_stage | exact GlobalTheory.CompanionTheory.SW.ThetaStage.theta_stage | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaStage.theta_stage <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RealQuadraticFormLemmaStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_quadratic_form_lemma : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ a : ℕ, 0 < a → ∀ β : F, β ≠ 0 → ∀ N : ℕ, 0 < N → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → (∀ y : ι → A F, (∀ i, (a : A F) * y i ∈ Oh F) → (N : A F) * qf (hf F) (Bf B) y ∈ Oh F) → ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = β}, ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (I : ℝ≥0∞) ∧ IntegrableOn (fun x : InfinitePlace F → ℝ => (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) D volume ∧ ∫ x in D, (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = ((volume D).toReal : ℂ) * ((I : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.CoefTheta.fourier_coefficient | exact GlobalTheory.CompanionTheory.SW.CoefTheta.fourier_coefficient | (intros; apply GlobalTheory.CompanionTheory.SW.CoefTheta.fourier_coefficient <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageIntegralFormulaStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_average_integral_formula : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → Integrable (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) Pr ∧ ENNReal.ofReal ‖(∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0‖ ≤ ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral.main | exact GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral.main | (intros; apply GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral.main <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaIntegralOverCoordinatesStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_over_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (S : Set (Fin M × Fin d → F)) (T : Set (Fin 1 → Fin M → E)), (∀ x, ofF b x ∈ T ↔ x ∈ S) → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 T) = ∫⁻ ω, ∑' x : S, Φ (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) ∂(prH μ 𝓕) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.PullCoord.lintegral_thetaMeas_coord | exact GlobalTheory.CompanionTheory.SW.BB.PullCoord.lintegral_thetaMeas_coord | (intros; apply GlobalTheory.CompanionTheory.SW.BB.PullCoord.lintegral_thetaMeas_coord <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOperatorIntegralInvarianceStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_integral_invariance : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ ∧ ∀ y : A F, fstar ψ (hf F) (Bf B) (muF B lf) φ (y + (N : A F) * x) = fstar ψ (hf F) (Bf B) (muF B lf) φ y := by
  first | exact @GlobalTheory.CompanionTheory.SW.FstarPer.fstar_periodic | exact GlobalTheory.CompanionTheory.SW.FstarPer.fstar_periodic | (intros; apply GlobalTheory.CompanionTheory.SW.FstarPer.fstar_periodic <;> assumption)
end

