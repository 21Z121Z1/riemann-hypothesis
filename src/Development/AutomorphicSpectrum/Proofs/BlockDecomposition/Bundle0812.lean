import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0806
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0799
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0802
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0800
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0807
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilOrbitalMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0342
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0804
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0776
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0808
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0647
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0654
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0619
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ISupMulISupMono
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0751
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedNodeStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_typed_node : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)), (∀ (K : Subgroup (GL (Fin r) (Af E))) (W : Submodule ℂ (Kinf E r → ℂ)), IsOpen (K : Set (GL (Fin r) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₁ K W)) → (∀ (K : Subgroup (GL (Fin s) (Af E))) (W : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K : Set (GL (Fin s) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₂ K W)) → ∀ (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed (indSpan U₁ U₂) K W) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.FdNode.finiteDimensional_typed_indSpan | exact GlobalTheory.CompanionTheory.LimV.FdNode.finiteDimensional_typed_indSpan | (intros; apply GlobalTheory.CompanionTheory.LimV.FdNode.finiteDimensional_typed_indSpan <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockSplittingMaximalCompactStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_splitting_maximal_compact : PositivityTheory.PfSWUS.FockSplitK := by
  first | exact @GlobalTheory.CompanionTheory.PfSWUS.fockSplitK | exact GlobalTheory.CompanionTheory.PfSWUS.fockSplitK | (intros; apply GlobalTheory.CompanionTheory.PfSWUS.fockSplitK <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneIsotropic
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeFact

theorem free_act {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (X : Fin n → Fin M → R ⊗[F] E) (hX : LinearIndependent (R ⊗[F] E) X) :
    LinearIndependent (R ⊗[F] E) (actW R σ J h X) := by
  let g : GL (Fin M) (R ⊗[F] E) := HA.mat R σ J h
  let e : (Fin M → R ⊗[F] E) ≃ₗ[R ⊗[F] E] (Fin M → R ⊗[F] E) :=
    Matrix.toLin'OfInv (M := ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)))
      (M' := (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))) (by simp) (by simp)
  have he : actW R σ J h X = e.toLinearMap ∘ X := by
    funext a
    simp [e, g, actW, actTup, Matrix.toLin'OfInv]
  rw [he]
  exact hX.map' e.toLinearMap (LinearEquiv.ker e)

theorem fib_compact_lt_top {V X Y : Type} [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V}
    {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib) (hU : IsOpen U) (b : X)
    {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨φ, hc, hcs, hs, h0, -, h1⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump hK hU hKU
  have hi := (h.2.2 φ hc hcs hs).1 b (Set.mem_univ b)
  refine lt_of_le_of_lt (GlobalTheory.CompanionTheory.SW.FibreFam.le_lintegral_bump _ hK h0 h1) ?_
  exact hi.lintegral_lt_top

theorem local_pack_free {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R)
    (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b)
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hm : IsGramFibFree R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m) :
    (∀ K : Set (Fin 1 → Fin M → R ⊗[F] E), IsCompact K →
      K ⊆ {Y | LinearIndependent (R ⊗[F] E) Y} → m (hermOf R σ 0 h₀) K < ⊤) ∧
    (∀ h : HA R σ J, (m (hermOf R σ 0 h₀)).map (actW R σ J h) = m (hermOf R σ 0 h₀)) ∧
    m (hermOf R σ 0 h₀) ({Y | gramR R σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR R)} ∩
      {Y | LinearIndependent (R ⊗[F] E) Y})ᶜ = 0 ∧
    (({Y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR R)} ∩
      {Y | LinearIndependent (R ⊗[F] E) Y}).Nonempty → m (hermOf R σ 0 h₀) ≠ 0) ∧
    (∀ X ∈ {Y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR R)} ∩
        {Y | LinearIndependent (R ⊗[F] E) Y},
      ∀ Y ∈ {Y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR R)} ∩
        {Y | LinearIndependent (R ⊗[F] E) Y},
      ∃ h : HA R σ J, actW R σ J h X = Y) := by
  obtain ⟨tr, lc, sc, t2, art, red, -⟩ := id hR
  haveI := tr
  haveI := lc
  haveI := sc
  haveI := t2
  obtain ⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (Fin 1 → Fin M → R ⊗[F] E) := tK8 1 M
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam
  haveI := hW 1 M
  haveI := hH 1
  have hU := GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hσ R hR 1 M
  have hz : (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (F := F) R) = 0 := by
    ext a c
    simp
  refine ⟨fun K hK hKU => fib_compact_lt_top hm hU _ hK hKU,
    fun h => GlobalTheory.T.local_gram_fibration_disintegration F E σ hσ M J hJ R hR 1 _ _ m (hW 1 M) (hH 1) hm h _, ?_, ?_, ?_⟩
  · exact hm.1 (hermOf R σ 0 h₀)
  · rintro ⟨X, hX, hXf⟩
    exact GlobalTheory.T.rank_one_fibre_measure_local F E σ hσ M J hJ R hR _ _ m (hW 1 M) (hH 1) hm X hXf (hX.trans hz) _
  · rintro X ⟨hX, hXf⟩ Y ⟨hY, hYf⟩
    exact GlobalTheory.T.isotropic_free_vectors_same_gram F E σ hσ M J hJ R hR X Y hXf hYf (hX.trans hz) (hY.trans hz)

theorem fact_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ I : Measure (Fin 1 → Fin M → AF F ⊗[F] E), IsLocallyFiniteMeasure I → (∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I) → I {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧ LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ = 0 → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ℝ≥0, ∀ (φinf : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → ∫⁻ X, pureL b S φinf φ X ∂I = (c : ℝ≥0∞) * ((∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b laminf lam hinf hlam minf hminf m hm I hIl hIinv hIT S
  classical
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  have hRI := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  have hRv := GlobalTheory.T.completion_is_local_ring F
  obtain ⟨trI, lcI, scI, t2I, -⟩ := id hRI
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hRv v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hRv v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hRv v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hRv v).2.2.2.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have kA := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  have kI := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  have kV := fun v => GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI := kA.1
  haveI := kA.2.1
  haveI := kA.2.2.1
  haveI := kA.2.2.2.1
  haveI := kA.2.2.2.2.2.2.2.1 1 M
  haveI := kI.1
  haveI := kI.2.1
  haveI := kI.2.2.1
  haveI := kI.2.2.2.1
  haveI := kI.2.2.2.2.2.2.2.1 1 M
  haveI : ∀ v, IsTopologicalRing (Fv F v ⊗[F] E) := fun v => (kV v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v ⊗[F] E) := fun v => (kV v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v ⊗[F] E) := fun v => (kV v).2.2.1
  haveI : ∀ v, T2Space (Fv F v ⊗[F] E) := fun v => (kV v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fin 1 → Fin M → Fv F v ⊗[F] E) := fun v => (kV v).2.2.2.2.2.2.2.1 1 M
  have uA := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  have uI := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (Ainf F)
  have uV := fun v => GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (Fv F v)
  haveI := uI.1
  haveI := uI.2.1
  haveI := uI.2.2.1
  haveI := uI.2.2.2.1
  haveI : ∀ v, IsTopologicalGroup (HA (Fv F v) σ J) := fun v => (uV v).1
  haveI : ∀ v, LocallyCompactSpace (HA (Fv F v) σ J) := fun v => (uV v).2.1
  haveI : ∀ v, SecondCountableTopology (HA (Fv F v) σ J) := fun v => (uV v).2.2.1
  haveI : ∀ v, T2Space (HA (Fv F v) σ J) := fun v => (uV v).2.2.2.1
  have LI := local_pack_free σ hσ J hJ (Ainf F) hRI h₀ b laminf hinf.1 minf hminf
  have LV := fun v => local_pack_free σ hσ J hJ (Fv F v) (hRv v) h₀ b (lam v) (hlam v).1 (m v) (hm v)
  obtain ⟨cI, cF, cV, hlat, hint, -, -, -, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hσ d b 1 M
  have hprc : Continuous (FactS.pr S : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
    cI.prodMk (continuous_pi fun v => (cV v.1).comp cF)
  have hprm : Measurable (FactS.pr S : (Fin 1 → Fin M → AF F ⊗[F] E) → _) := hprc.measurable
  have hintm : MeasurableSet (intOff b S : Set (Fin 1 → Fin M → AF F ⊗[F] E)) :=
    (hint S).measurableSet
  have actC : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] ,
      (Continuous fun p : HA R σ J × (Fin 1 → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) →
      ∀ h : HA R σ J, Continuous (actW R σ J h : (Fin 1 → Fin M → R ⊗[F] E) → _) :=
    fun R _ _ _ hc h => hc.comp (Continuous.prodMk_right h)
  have cAI := (uI.2.2.2.2.2 1).1
  have cAV := fun v => ((uV v).2.2.2.2.2 1).1
  have cAA := (uA.2.2.2.2.2 1).1
  set P := (I.restrict (intOff b S)).map (FactS.pr S) with hPdef
  haveI hPc : IsFiniteMeasureOnCompacts P := ⟨fun K hK => by
    rw [hPdef, Measure.map_apply hprm hK.isClosed.measurableSet,
      Measure.restrict_apply (hprm hK.isClosed.measurableSet)]
    exact FactS.preimage_lt_top σ hσ b S I K hK⟩
  have hPinv : ∀ (g₀ : HA (Ainf F) σ J) (g : ∀ v : S, HA (Fv F v.1) σ J),
      P.map (fun x => (actW (Ainf F) σ J g₀ x.1, fun v => actW (Fv F v.1) σ J (g v) (x.2 v))) = P := by
    intro g₀ g
    refine FactS.push_inv σ hσ J hJ b S I hIinv (fun v X => ((uV v).2.2.2.2.2 1).2.1 X) hprm
      (fun h => (actC _ cAA h).measurable) hintm g₀ g ?_
    refine Continuous.measurable (Continuous.prodMk ((actC _ cAI g₀).comp continuous_fst)
      (continuous_pi fun v => ?_))
    exact (actC _ (cAV v.1) (g v)).comp ((continuous_apply v).comp continuous_snd)
  have hZ₀ : IsClosed {Y : Fin 1 → Fin M → Ainf F ⊗[F] E |
      gramR (Ainf F) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Ainf F))} :=
    isClosed_eq (kI.2.2.2.2.2.2.2.2.2 1 M J) continuous_const
  have hZ : ∀ v : S, IsClosed {Y : Fin 1 → Fin M → Fv F v.1 ⊗[F] E |
      gramR (Fv F v.1) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Fv F v.1))} := fun v =>
    isClosed_eq ((kV v.1).2.2.2.2.2.2.2.2.2 1 M J) continuous_const
  have hU₀ := GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hσ (Ainf F) hRI 1 M
  have hU : ∀ v : S, IsOpen {Y : Fin 1 → Fin M → Fv F v.1 ⊗[F] E |
      LinearIndependent (Fv F v.1 ⊗[F] E) Y} := fun v =>
    GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hσ (Fv F v.1) (hRv v.1) 1 M
  have hPZ : P (({Y : Fin 1 → Fin M → Ainf F ⊗[F] E |
        gramR (Ainf F) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Ainf F))} ∩
        {Y | LinearIndependent (Ainf F ⊗[F] E) Y}) ×ˢ
      Set.univ.pi fun v : S => {Y : Fin 1 → Fin M → Fv F v.1 ⊗[F] E |
        gramR (Fv F v.1) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Fv F v.1))} ∩
        {Y | LinearIndependent (Fv F v.1 ⊗[F] E) Y})ᶜ = 0 := by
    have hms : MeasurableSet (({Y : Fin 1 → Fin M → Ainf F ⊗[F] E |
        gramR (Ainf F) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Ainf F))} ∩
        {Y | LinearIndependent (Ainf F ⊗[F] E) Y}) ×ˢ
      Set.univ.pi fun v : S => {Y : Fin 1 → Fin M → Fv F v.1 ⊗[F] E |
        gramR (Fv F v.1) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Fv F v.1))} ∩
        {Y | LinearIndependent (Fv F v.1 ⊗[F] E) Y}) :=
      (hZ₀.measurableSet.inter hU₀.measurableSet).prod
        (MeasurableSet.univ_pi fun v => (hZ v).measurableSet.inter (hU v).measurableSet)
    rw [hPdef, Measure.map_apply hprm hms.compl]
    refine le_antisymm (le_trans (Measure.restrict_apply_le _ _) ?_) bot_le
    refine le_trans (measure_mono ?_) hIT.le
    rintro X hX ⟨hXg, hXi, hXv⟩
    apply hX
    have hg := ((GlobalTheory.T.gram_matrix_local_global F E σ hσ M J hJ 1 X 0).1.mp hXg)
    exact ⟨⟨hg.1, hXi⟩, fun v _ => ⟨hg.2 v.1, hXv v.1⟩⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.restricted_product_haar_measure (ι := S) (G := fun v : S => HA (Fv F v.1) σ J)
    (W := fun v : S => Fin 1 → Fin M → Fv F v.1 ⊗[F] E)
    (actW (Ainf F) σ J) (fun v => actW (Fv F v.1) σ J)
    cAI (uI.2.2.2.2.2 1).2.1 (uI.2.2.2.2.2 1).2.2.1
    (fun v => cAV v.1) (fun v => ((uV v.1).2.2.2.2.2 1).2.1) (fun v => ((uV v.1).2.2.2.2.2 1).2.2.1)
    _ _ hU₀ hU
    (fun g x hx => free_act _ σ J g x hx) (fun v g x hx => free_act _ σ J g x hx)
    _ _ hZ₀ hZ
    (fun g x hx => ((uI.2.2.2.2.2 1).2.2.2 g x).trans hx)
    (fun v g x hx => (((uV v.1).2.2.2.2.2 1).2.2.2 g x).trans hx)
    LI.2.2.2.2 (fun v => (LV v.1).2.2.2.2)
    (minf (hermOf (Ainf F) σ 0 h₀)) (fun v => m v.1 (hermOf (Fv F v.1) σ 0 h₀))
    LI.1 (fun v => (LV v.1).1)
    LI.2.1 (fun v => (LV v.1).2.1) LI.2.2.1 (fun v => (LV v.1).2.2.1)
    LI.2.2.2.1 (fun v => (LV v.1).2.2.2.1) P hPc hPinv hPZ
  refine ⟨c, fun φinf φ hφinf hφ => ?_⟩
  have h := hc φinf (fun v => φ v.1) hφinf (fun v => hφ v.1)
  have hΦ : Measurable fun x : (Fin 1 → Fin M → Ainf F ⊗[F] E) ×
      ∀ v : S, Fin 1 → Fin M → Fv F v.1 ⊗[F] E => φinf x.1 * ∏ v : S, φ v.1 (x.2 v) :=
    (hφinf.comp measurable_fst).mul
      (Finset.measurable_prod _ fun v _ => (hφ v.1).comp ((measurable_pi_apply v).comp measurable_snd))
  rw [hPdef, lintegral_map hΦ hprm, Finset.prod_coe_sort S fun v => ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ 0 h₀))] at h
  rw [← h]
  unfold pureL
  rw [lintegral_indicator hintm]
  refine lintegral_congr fun X => ?_
  simp only [FactS.pr]
  rw [Finset.prod_coe_sort S fun v => φ v (projV v (projFin X))]

end GlobalTheory.CompanionTheory.WeilSiegel.FreeFact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerSummableRationalHermitianStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_power_summable_rational_hermitian : ∀ (D : D7) (ρ : ℕ) (H : G D ρ → ℝ≥0), IsHt H → ∀ (w : G D ρ) (nb : hermA D ρ → G D ρ),
  mat w = blk4 0 1 (-1) 0 → (∀ z : hermA D ρ, mat (nb z) = blk4 1 z.1 0 1) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Summable (fun ζ : ratHerm D ρ => (H (w * nb ζ.1) : ℝ) ^ τ) := by
  first | exact @GlobalTheory.CompanionTheory.HermSum.summable_height_rpow | exact GlobalTheory.CompanionTheory.HermSum.summable_height_rpow | (intros; apply GlobalTheory.CompanionTheory.HermSum.summable_height_rpow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFibreFreeExtensionStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_fibre_free_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (hypOne J) (n + 1) (coordW R b lam (n + 1) (M + 2)) (coordHerm R σ b lam (n + 1)) m → IsGramFibFree R σ (hypOne J) 1 (coordW R b lam 1 (M + 2)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → (∀ X, 0 ≤ φ X) → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m 0) = ∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (φ (chartS R σ J x a 0 Y)) ∂(m' 0) ∂(coordW R b lam 1 n) ∂(m₁ 0) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicRankOneGlobalVolume
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimOne

theorem abs_sub_one_le {P L : ℝ≥0∞} {r A : ℝ} (hr : 0 ≤ r) (hL : L < ⊤) (hPL : P ≤ L)
    (h : L ≤ P + ENNReal.ofReal (2 * r) * L) (hA : |L.toReal - 1| ≤ A) :
    |P.toReal - 1| ≤ |L.toReal - 1| + 2 * (1 + A) * r := by
  have hP : P < ⊤ := lt_of_le_of_lt hPL hL
  have h1 : P.toReal ≤ L.toReal := ENNReal.toReal_mono hL.ne hPL
  have h2 : L.toReal ≤ P.toReal + 2 * r * L.toReal := by
    have hfin : P + ENNReal.ofReal (2 * r) * L ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hP.ne, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL.ne⟩
    have := ENNReal.toReal_mono hfin h
    rwa [ENNReal.toReal_add hP.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL.ne),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have h3 : L.toReal ≤ 1 + A := by
    have := (abs_le.1 hA).2
    linarith
  have h4 : 2 * r * L.toReal ≤ 2 * (1 + A) * r := by
    have : 2 * r * L.toReal ≤ 2 * r * (1 + A) := mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have h5 : |P.toReal - L.toReal| ≤ 2 * (1 + A) * r := by
    rw [abs_le]
    constructor <;> linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 * r) (ENNReal.toReal_nonneg (a := L))]
  calc |P.toReal - 1| = |(P.toReal - L.toReal) + (L.toReal - 1)| := by ring_nf
    _ ≤ |P.toReal - L.toReal| + |L.toReal - 1| := abs_add_le _ _
    _ ≤ |L.toReal - 1| + 2 * (1 + A) * r := by linarith

theorem prim_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)), IsGramFibFree (Ainf F) σ (hypOne J) 1 (coordW (Ainf F) b laminf 1 (M + 2)) (coordHerm (Ainf F) σ b laminf 1) minf → (∀ v, IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b (lam v) 1 (M + 2)) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ I : Measure (Fin 1 → Fin (M + 2) → AF F ⊗[F] E), IsEulerProd b I 1 (minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)) (fun v => m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)) → Summable (fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v)).toReal - 1|) ∧ ∃ S₃ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₃ ⊆ S → ∀ (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → ∫⁻ y, purePr σ J b S Ψinf Ψ y ∂I = ((∫⁻ y, Ψinf y ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂))) * ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂))) * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v.1)).toReal) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM d b laminf lam hinf hlam h₂ minf m hfinf hfv I hE
  have hND := (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem F E σ hCM M J hJ).1
  have hSF := GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero F E σ hCM (M + 2) (hypOne J) hND (by omega) h₂ d b laminf lam hinf hlam
    minf hfinf m hfv
  have hgood := (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimLoc.prim_local F E σ hCM M J hJ (by omega) d b).and (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.eventually_measurableSet_primV F E σ hCM M J hJ d b)
  obtain ⟨hfin, hsumL, -⟩ := id hE
  have hsum : Summable (fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)
      (primV σ J b v)).toReal - 1|) := by
    set A : ℝ := ∑' v, |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)
      (latV b v)).toReal - 1| with hAdef
    have hb := (hsumL.add (((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left
      (2 * (1 + A)))))
    refine Summable.of_norm_bounded_eventually hb ?_
    filter_upwards [hgood] with v hv
    obtain ⟨⟨hsub, hmass⟩, -⟩ := hv
    have h := hmass (lam v) (hlam v) (m v) (hfv v) h₂
    have hle : |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v)).toReal - 1| ≤ A :=
      hsumL.le_tsum v (fun _ _ => abs_nonneg _)
    have hr : (0 : ℝ) ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by positivity
    have h' := abs_sub_one_le hr (hfin v) (measure_mono hsub) (by
      have e : (2 : ℝ) * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) = 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
        ring
      rw [e]
      exact h) hle
    rw [Real.norm_eq_abs, abs_abs]
    simpa [mul_assoc] using h'
  refine ⟨hsum, ?_⟩
  have hfinS : {v | ¬ ((primV σ J b v ⊆ latV b v) ∧ MeasurableSet (primV σ J b v))}.Finite := by
    have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        (primV σ J b v ⊆ latV b v) ∧ MeasurableSet (primV σ J b v) := by
      filter_upwards [hgood] with v hv
      exact ⟨hv.1.1, hv.2⟩
    exact Filter.eventually_cofinite.1 h
  exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimFormula.prim_formula F E σ hCM M J hJ d b I _ _ hE hSF.1 hSF.2.1 hfinS.toFinset
    (fun v hv => by
      by_contra hc
      exact hv (hfinS.mem_toFinset.2 hc)) hsum

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimOne
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}

theorem absA_pos (z : (AE D)ˣ) : 0 < absA D z := by
  have h : absA D z * absA D z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.2 fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h

theorem npow_neg_nat {r : ℝ≥0} (hr : 0 < r) (m : ℕ) : ((((r ^ m)⁻¹ : ℝ≥0) : ℝ) : ℂ) = npow r (-(m : ℂ)) := by
  have h0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem integral_comp_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (f : A → ℂ) :
    ∫ y, f (φ y) ∂μ = ((((addEquivAddHaarChar φ)⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ y, f y ∂μ := by
  have hmap : μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
    have key := addEquivAddHaarChar_smul_map μ φ
    have hne : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
    calc μ.map φ = ((addEquivAddHaarChar φ)⁻¹ * addEquivAddHaarChar φ) • μ.map φ := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = (addEquivAddHaarChar φ)⁻¹ • μ := by rw [mul_smul, key]
  have hint : ∫ u, f u ∂(μ.map φ) = ∫ y, f (φ y) ∂μ :=
    integral_map_equiv (μ := μ) φ.toHomeomorph.toMeasurableEquiv f
  rw [← hint, hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem nb_add {nb : hermA D n → G D n} (h : IsNMap nb) (x y : hermA D n) : nb (x + y) = nb x * nb y :=
  mat_inj (by
    rw [mat_mul, h, h, h, submatrix_fromBlocks_mul]
    simp [add_comm])

def cg (a : GL (Fin n) (AE D)) (c : hermA D n) : hermA D n :=
  ⟨a.1 * c.1 * adj a.1, by
    change adj (a.1 * c.1 * adj a.1) = a.1 * c.1 * adj a.1
    have hc : adj c.1 = c.1 := c.2
    rw [adj_mul, adj_mul, adj_adj, hc, Matrix.mul_assoc]⟩

theorem adj_mul_adj_inv (a : GL (Fin n) (AE D)) : (adj a.1 : Mx D n n) * adj (a⁻¹).1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

theorem adj_inv_mul_adj (a : GL (Fin n) (AE D)) : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

def ad (a : GL (Fin n) (AE D)) : GL (Fin n) (AE D) :=
  ⟨adj (a⁻¹).1, adj a.1, adj_inv_mul_adj a, adj_mul_adj_inv a⟩

theorem nb_cg_mul {nb : hermA D n → G D n} (h : IsNMap nb) (a : GL (Fin n) (AE D)) {m : G D n}
    (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) (c : hermA D n) : nb (cg a c) * m = m * nb c :=
  mat_inj (by
    rw [mat_mul, mat_mul, hm, h, h, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    have e : a.1 * c.1 * adj a.1 * adj (a⁻¹).1 = a.1 * c.1 := by
      rw [Matrix.mul_assoc, adj_mul_adj_inv, Matrix.mul_one]
    simp [cg, e, -Matrix.coe_units_inv])

theorem weyl_mul {w m m' : G D n} (hw : mat w = blk4 0 1 (-1) 0) (a : GL (Fin n) (AE D))
    (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) (hm' : mat m' = blk4 (adj (a⁻¹).1) 0 0 a.1) : w * m = m' * w :=
  mat_inj (by
    rw [mat_mul, mat_mul, hm, hw, hm', submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    simp)

theorem mulVec_mem_upper {g : G D n} {x y : Mx D n n} (hg : mat g = blk4 x 0 0 y) {v : Fin (n + n) → AE D}
    (hv : v ∈ upperHalf D n) : (mat g).mulVec v ∈ upperHalf D n := by
  have hv' : ∀ i : Fin n, v (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0 := fun i => congrFun hv i
  refine LinearMap.mem_ker.2 (funext fun i => ?_)
  simp only [LinearMap.funLeft_apply, Pi.zero_apply, hg, Matrix.mulVec, dotProduct]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    hv', mul_zero, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

theorem levi_mem_P {g g' : G D n} {x y x' y' : Mx D n n} (hg : mat g = blk4 x 0 0 y) (hg' : mat g' = blk4 x' 0 0 y')
    (h1 : g' * g = 1) : g ∈ P D n := by
  have hinv : g⁻¹ = g' := inv_eq_of_mul_eq_one_left h1
  intro v
  refine ⟨fun hv => mulVec_mem_upper hg hv, fun hv => ?_⟩
  have h2 := mulVec_mem_upper hg' (v := (mat g).mulVec v) hv
  rwa [Matrix.mulVec_mulVec, ← mat_mul, h1, mat_one, Matrix.one_mulVec] at h2

theorem height_mul {H : G D n → ℝ≥0} (hH : IsHeight H) {p : G D n} (hp : p ∈ P D n) (a : GL (Fin n) (AE D))
    (ha : blkA (mat p) = a.1) (x : G D n) :
    H (p * x) = absA D (Matrix.GeneralLinearGroup.det a) * H x := by
  obtain ⟨q, hq, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
  obtain ⟨c, hc⟩ := exists_blkA hq
  have e : blkA (mat (p * q)) = (a * c).1 := by rw [blkA_mul hq, ha, hc, Units.val_mul]
  rw [← mul_assoc, hH _ ((P D n).mul_mem hp hq) (a * c) e k hk, hH q hq c hc k hk, map_mul, map_mul]

end GlobalTheory.CompanionTheory.IwaAd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalIsotropicOrbitOfE0
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypOrbit

theorem exists_actW_e0_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E), LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ (hypOne J) y = 0 → ∃ g : HA (Fv F v) σ (hypOne J), actW (Fv F v) σ (hypOne J) g (e0 _ M) = y := by
  intro F E _ _ _ _ _ σ hσ M J hJ v y hy gy
  exact GlobalTheory.CompanionTheory.WeilSiegel.HypWitt.witt_e0 F E σ hσ M J hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) y hy gy

end GlobalTheory.CompanionTheory.WeilSiegel.HypOrbit
end
end

