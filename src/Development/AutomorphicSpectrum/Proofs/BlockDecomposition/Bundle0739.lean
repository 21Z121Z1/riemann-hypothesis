import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalProductEquivMultiplicityOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeCuspidalPairLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0738
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalFormL2Mem
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalProductEquivMultiplicityOneStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_product_equiv_multiplicity_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL k) (hd : ∑ a, (y a).1 = N), IsCanon Γ → (∀ i, IsLSeg (Γ i) (y i).rep) → ∃ (g : ℕ) (z : Fin g → IrrGL k) (hz : ∑ b, (z b).1 = N), Nonempty ((prodIrr y hd).Equiv (prodIrr z hz)) ∧ jm z hz (prodIrr z hz) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.GroupCount.groupCount | exact GlobalTheory.CompanionTheory.GroupCount.groupCount | (intros; apply GlobalTheory.CompanionTheory.GroupCount.groupCount <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerate
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem traceGram_isSymm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Matrix.of fun k l : Fin d => Algebra.trace F E (b k * σ (b l))).IsSymm := by
  have hσ : ∀ e, σ (σ e) = e := sig_invol hCM
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  ext k l
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  have h := Algebra.trace_eq_of_algEquiv s (b l * σ (b k))
  have hs : s (b l * σ (b k)) = b k * σ (b l) := by
    show σ (b l * σ (b k)) = b k * σ (b l)
    rw [map_mul, hσ, mul_comm]
  rw [hs] at h
  exact h.symm ▸ rfl

theorem traceGram_det_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Matrix.of fun k l : Fin d => Algebra.trace F E (b k * σ (b l))).det ≠ 0 := by
  have hσ : ∀ e, σ (σ e) = e := sig_invol hCM
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  intro h0
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  set y : E := ∑ l, v l • b l with hy
  have hk : ∀ k, Algebra.trace F E (b k * σ y) = 0 := by
    intro k
    have := congrFun hmul k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [hy, map_sum, Finset.mul_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hsm : σ (v l • b l) = v l • σ (b l) := by
      rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def]
    rw [hsm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hz : ∀ x, Algebra.traceForm F E (σ y) x = 0 := by
    intro x
    rw [← b.sum_repr x]
    simp only [map_sum, map_smul, Algebra.traceForm_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_comm (σ y), hk, smul_zero]
  have hσy : σ y = 0 := (traceForm_nondegenerate F E).1 _ hz
  have hy0 : y = 0 := by rw [← hσ y, hσy, map_zero]
  have := (Fintype.linearIndependent_iff.1 b.linearIndependent) v hy0
  exact funext this

theorem coordForm_isSymm_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), (coordForm σ b n).IsSymm ∧ (coordForm σ b n).det ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM d b n
  constructor
  · refine Matrix.IsSymm.fromBlocks (Matrix.isSymm_one) (by simp) ?_
    unfold Matrix.IsSymm
    rw [Matrix.blockDiagonal_transpose]
    congr 1
    funext _
    exact traceGram_isSymm hCM b
  · unfold coordForm
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => traceGram_det_ne_zero hCM b

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneInvariantUnderMatrix
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.PiCovol

theorem isFD_pi {ι Y : Type} [Fintype ι] [AddCommGroup Y] [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    {G : AddSubgroup Y} {D : Set Y} (hF : IsAddFundamentalDomain G D ν) :
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : ι => G) (Set.univ.pi fun _ : ι => D)
      (Measure.pi fun _ : ι => ν) := by
  have hq (i : ι) := Measure.quasiMeasurePreserving_eval (fun _ : ι => ν) i
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.univ_pi_eq_iInter]
    exact NullMeasurableSet.iInter fun i => hF.nullMeasurableSet.preimage (hq i)
  · have := (ae_all_iff (μ := (Measure.pi fun _ : ι => ν))).2 fun i => (hq i).ae hF.ae_covers
    filter_upwards [this] with z hz
    choose a ha using hz
    exact ⟨⟨fun i => a i, fun i _ => (a i).2⟩, fun i _ => ha i⟩
  · intro a b hab
    obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
      by_contra! h
      exact hab (Subtype.ext (funext h))
    have h := hF.aedisjoint (i := ⟨a.1 i, a.2 i trivial⟩) (j := ⟨b.1 i, b.2 i trivial⟩)
      fun e => hi (congrArg Subtype.val e)
    refine measure_mono_null ?_ ((hq i).preimage_null h)
    rintro z ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩
    exact ⟨⟨u i, hu i trivial, congrFun hu' i⟩, ⟨v i, hv i trivial, congrFun hv' i⟩⟩

theorem map_eq_of_isFD {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (P : Measure V) [P.IsAddHaarMeasure] (G : AddSubgroup V) [Countable G] {D : Set V}
    (hD : IsAddFundamentalDomain G D P) (h0 : P D ≠ 0) (h1 : P D ≠ ⊤) (e : V ≃ₜ+ V)
    (hG : ∀ v ∈ G, e.symm v ∈ G) (hG' : ∀ v ∈ G, e v ∈ G) : P.map e = P := by
  haveI : (P.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map P
  set c := Measure.addHaarScalarFactor (P.map e) P with hc
  have h : P.map e = c • P := Measure.isAddLeftInvariant_eq_smul _ P
  have hm : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hpre : IsAddFundamentalDomain G (e ⁻¹' D) P := by
    refine hD.preimage_of_equiv (f := e) ⟨hm.measurable, ?_⟩
      (e := fun b : G => (⟨e.symm b, hG _ b.2⟩ : G)) ⟨fun b b' h => ?_, fun a => ?_⟩ fun b v => ?_
    · rw [h]; exact Measure.smul_absolutelyContinuous
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
    · exact ⟨⟨e a, hG' _ a.2⟩, Subtype.ext (e.symm_apply_apply _)⟩
    · change e (e.symm b + v) = b + e v
      simp
  have e1 : P (e ⁻¹' D) = P D := hpre.measure_eq hD
  have e2 : P (e ⁻¹' D) = c * P D := by rw [← hm.map_apply, h]; rfl
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have : (c : ℝ≥0∞) * P D = 1 * P D := by rw [← e2, e1, one_mul]
    exact (ENNReal.mul_left_inj h0 h1).1 this
  have : c = 1 := by exact_mod_cast hc1
  rw [h, this, one_smul]

end GlobalTheory.CompanionTheory.SiegelND.PiCovol

open GlobalTheory.CompanionTheory.SiegelND.PiCovol in

theorem GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix : ∀ (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)), GlobalTheory.CompanionTheory.Hypotheses₂.OneV.IsCovolOne ν → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → (Measure.pi fun _ : ι => ν).map (fun x => (A.map (algebraMap F (AF F))).mulVec x) = Measure.pi fun _ : ι => ν := by
  intro F _ _ ν hν ι _ _ A hA
  obtain ⟨hH, D, hD, hD1⟩ := hν
  haveI := hH
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  set G₀ : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range with hG₀
  set G : AddSubgroup (ι → AF F) := AddSubgroup.pi Set.univ fun _ : ι => G₀ with hGdef
  have hmemG : ∀ v : ι → AF F, v ∈ G ↔ ∃ ξ : ι → F, v = fun i => algebraMap F (AF F) (ξ i) := by
    intro v
    constructor
    · intro hv
      choose ξ hξ using fun i => hv i trivial
      exact ⟨ξ, funext fun i => (hξ i).symm⟩
    · rintro ⟨ξ, rfl⟩ i _
      exact ⟨ξ i, rfl⟩
  haveI : Countable G := by
    have : Function.Surjective (fun ξ : ι → F => (⟨fun i => algebraMap F (AF F) (ξ i), (hmemG _).2 ⟨ξ, rfl⟩⟩ : G)) := by
      rintro ⟨v, hv⟩
      obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
      exact ⟨ξ, rfl⟩
    exact this.countable
  have hFD := isFD_pi (ι := ι) ν hD
  have hmass : (Measure.pi fun _ : ι => ν) (Set.univ.pi fun _ : ι => D) = 1 := by
    rw [Measure.pi_pi]; simp [hD1]
  have hrat : ∀ (B : Matrix ι ι F) (ξ : ι → F), (B.map (algebraMap F (AF F))).mulVec (fun i => algebraMap F (AF F) (ξ i)) =
      fun i => algebraMap F (AF F) (B.mulVec ξ i) := by
    intro B ξ
    funext i
    exact (RingHom.map_mulVec (algebraMap F (AF F)) B ξ i).symm
  have hu := GlobalTheory.CompanionTheory.SW.SdCoord.isUnit_det_map (R := AF F) A hA
  have hinv : (A.map (algebraMap F (AF F)))⁻¹ = A⁻¹.map (algebraMap F (AF F)) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  have := map_eq_of_isFD (Measure.pi fun _ : ι => ν) G hFD (by rw [hmass]; simp) (by rw [hmass]; simp)
    (GlobalTheory.CompanionTheory.SW.SdCoord.matE _ hu) ?_ ?_
  · exact this
  · intro v hv
    obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
    refine (hmemG _).2 ⟨A⁻¹.mulVec ξ, ?_⟩
    change (A.map (algebraMap F (AF F)))⁻¹.mulVec _ = _
    rw [hinv, hrat]
  · intro v hv
    obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
    refine (hmemG _).2 ⟨A.mulVec ξ, ?_⟩
    exact hrat A ξ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalContragredientCentralCharacter
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.ContraCusp

theorem contra_facts : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ),
    (contra σ.ρ).IsIrreducible ∧ IsCuspidal (contra σ.ρ) ∧
    ∃ (z : GL (Fin (m + 1)) k) (ϖ : k) (ω : ℂ), (z : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ϖ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ∧
      ValuativeRel.valuation k ϖ < 1 ∧ ϖ ≠ 0 ∧ ω ≠ 0 ∧ (∀ a, σ.ρ z a = ω • a) ∧ ∀ l, contra σ.ρ z l = ω⁻¹ • l := by
  intro k _ _ _ _ m σ hc
  have hadm : IsAdmissible σ.ρ :=
    PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k (m + 1) _ σ.ρ σ.smooth σ.irr
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k (m + 1)
  refine ⟨GlobalTheory.ContraRefl.contra_isIrreducible hG hadm σ.irr,
    GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k (m + 1) _ _
      (GlobalTheory.CompanionTheory.DualCusp.isSupercuspidal_contra hG hadm
        (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k (m + 1) _ _ hc)), ?_⟩
  obtain ⟨ϖ, -, hϖ0, hϖ, -⟩ := GlobalTheory.CompanionTheory.LocalField.exists_uniformiser k
  obtain ⟨χ, -, hχ⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar σ.smooth σ.irr
  let t : kˣ := Units.mk0 ϖ hϖ0
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) t, ϖ, (χ t : ℂ), ?_, hϖ, hϖ0, (χ t).ne_zero,
    fun a => hχ t a, fun l => ?_⟩
  · ext i j
    simp [Matrix.GeneralLinearGroup.scalar, t, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  · refine Subtype.ext (LinearMap.ext fun v => ?_)
    have h1 : (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) t)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) t⁻¹ := (map_inv _ t).symm
    have h2 : ((χ t⁻¹ : ℂˣ) : ℂ) = ((χ t : ℂˣ) : ℂ)⁻¹ := by
      rw [map_inv, Units.val_inv_eq_inv_val]
    rw [contra_apply, h1, hχ t⁻¹ v, map_smul, h2]
    rfl

end GlobalTheory.CompanionTheory.ContraCusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeCuspidalPairLengthStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_cuspidal_pair_length : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {p q N c : ℕ} (u v : IrrGL k) (s : Fin p → IrrGL k) (t : Fin q → IrrGL k) (hs : ∑ i, (s i).1 = u.1) (ht : ∑ i, (t i).1 = v.1) (d : ℕ) (hsd : ∀ i, (s i).1 = d) (htd : ∀ j, (t j).1 = d) (hsc : ∀ i, (s i).IsCusp) (htc : ∀ i, (t i).IsCusp) (hu : Nonempty ((jac (stdBlocks (fun i => (s i).1) hs) u.rep).Equiv (piTensor fun i => (s i).rep))) (hv : Nonempty ((jac (stdBlocks (fun i => (t i).1) ht) v.rep).Equiv (piTensor fun i => (t i).rep))) (hd : ∑ i, (![u, v] i).1 = N) (y : Fin c → IrrGL k) (hy : ∑ i, (y i).1 = N) (hyc : ∀ i, (y i).IsCusp) (h : 1 ≤ jm y hy (prodIrr ![u, v] hd)), ∃ (f : Fin p ↪o Fin c) (g : Fin q ↪o Fin c), Disjoint (Set.range f) (Set.range g) ∧ (∀ i, y (f i) = s i) ∧ ∀ j, y (g j) = t j := by
  first | exact @GlobalTheory.CompanionTheory.Shuffle2.shuffle2 | exact GlobalTheory.CompanionTheory.Shuffle2.shuffle2 | (intros; apply GlobalTheory.CompanionTheory.Shuffle2.shuffle2 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeUnitaryAction
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.IntegrateK

variable {n : ℕ}

theorem exp_smul_mem_unitary (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

def onePar (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp ((s : ℂ) • X), exp_smul_mem_unitary X hX s⟩

theorem onePar_zero (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) : onePar X hX 0 = 1 := by
  apply Subtype.ext
  simp [onePar]

theorem onePar_add (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (h s : ℝ) :
    onePar X hX (h + s) = onePar X hX h * onePar X hX s := by
  apply Subtype.ext
  have hc : Commute ((h : ℂ) • X) ((s : ℂ) • X) :=
    ((Commute.refl X).smul_left _).smul_right _
  show NormedSpace.exp (((h + s : ℝ) : ℂ) • X) = _ * _
  simp only [onePar]
  rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]

theorem inner_sum_left {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Kf : Fin n → Fin n → Module.End ℂ V)
    (hs : ∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (x y : V) :
    ⟪∑ a, ∑ b, X a b • Kf a b x, y⟫_ℂ = -⟪x, ∑ a, ∑ b, X a b • Kf a b y⟫_ℂ := by
  have hent : ∀ a b, (starRingEnd ℂ) (X a b) = -X b a := by
    intro a b
    have := congrFun (congrFun hX b) a
    simpa [Matrix.conjTranspose_apply] using this
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hs, hent]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem intertwines_unitary : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H), (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → ∀ (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf → (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → ∀ T : H →ₗ[ℂ] V, (∀ a b w, T (G a b w) = Kf a b (T w)) → ∀ k w, T (ρ k w) = σ k (T w) := by
  intro n H V _ _ _ _ _ ρ G hG σ Kf hK hskew T hT k w
  obtain ⟨X, hX, hk⟩ := GlobalTheory.CompanionTheory.UnitaryExp.exists_skew_exp_eq n k
  have hk1 : onePar X hX 1 = k := by
    apply Subtype.ext
    have := congrArg Units.val hk
    have h4 : ((uG k : _ˣ) : Matrix (Fin n) (Fin n) ℂ) = k.1 := rfl
    rw [h4] at this
    simpa [onePar] using this.symm
  let Tc : H →L[ℝ] V :=
    (⟨T, T.continuous_of_finiteDimensional⟩ : H →L[ℂ] V).restrictScalars ℝ
  have hsub : ∀ u s : ℝ, onePar X hX (u - s) * onePar X hX s = onePar X hX u := by
    intro u s
    rw [← onePar_add, sub_add_cancel]
  have hY : ∀ s, HasDerivAt (fun s => T (ρ (onePar X hX s) w))
      (∑ a, ∑ b, X a b • Kf a b (T (ρ (onePar X hX s) w))) s := by
    intro s
    have h0 := hG X (onePar X hX) hX (fun _ => rfl) (ρ (onePar X hX s) w)
    have h1 : HasDerivAt (fun t => T (ρ (onePar X hX t) (ρ (onePar X hX s) w)))
        (T (∑ a, ∑ b, X a b • G a b (ρ (onePar X hX s) w))) 0 :=
      Tc.hasFDerivAt.comp_hasDerivAt 0 h0
    have h2 := HasDerivAt.comp_sub_const (f := fun t => T (ρ (onePar X hX t) (ρ (onePar X hX s) w)))
      s s (by simpa using h1)
    have e : (fun u => T (ρ (onePar X hX (u - s)) (ρ (onePar X hX s) w)))
        = fun u => T (ρ (onePar X hX u) w) := by
      funext u
      rw [← hsub u s, map_mul]
      rfl
    rw [e] at h2
    simpa only [hT] using h2
  have hU : ∀ (v : V) (s : ℝ), HasDerivAt (fun s => σ (onePar X hX s) v)
      (∑ a, ∑ b, X a b • Kf a b (σ (onePar X hX s) v)) s := by
    intro v s
    obtain ⟨S, _, hmem, _, _, hd⟩ := hK.2 (σ (onePar X hX s) v)
    have h0 := hd X (onePar X hX) (fun _ => rfl) _ hmem
    have h2 := HasDerivAt.comp_sub_const (f := fun t => σ (onePar X hX t) (σ (onePar X hX s) v))
      s s (by simpa using h0)
    have e : (fun u => σ (onePar X hX (u - s)) (σ (onePar X hX s) v))
        = fun u => σ (onePar X hX u) v := by
      funext u
      rw [← hsub u s, map_mul]
      rfl
    rw [e] at h2
    exact h2
  have hconst : ∀ v : V, ⟪T (ρ k w), σ k v⟫_ℂ = ⟪T w, v⟫_ℂ := by
    intro v
    have hf : ∀ s : ℝ, HasDerivAt
        (fun s : ℝ => ⟪T (ρ (onePar X hX s) w), σ (onePar X hX s) v⟫_ℂ) 0 s := by
      intro s
      have h := (hY s).inner ℂ (hU v s)
      rw [inner_sum_left Kf hskew X hX, add_neg_cancel] at h
      exact h
    have h := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt)
      (fun s => (hf s).deriv) 1 0
    simp only [hk1, onePar_zero, map_one] at h
    simpa using h
  have horth : ∀ v : V, ⟪T (ρ k w) - σ k (T w), σ k v⟫_ℂ = 0 := by
    intro v
    rw [inner_sub_left, hconst v, hK.1 k, sub_self]
  have hsurj : σ k (σ k⁻¹ (T (ρ k w) - σ k (T w))) = T (ρ k w) - σ k (T w) := by
    have : (σ k * σ k⁻¹) (T (ρ k w) - σ k (T w)) = T (ρ k w) - σ k (T w) := by
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    exact this
  have hz := horth (σ k⁻¹ (T (ρ k w) - σ k (T w)))
  rw [hsurj, inner_self_eq_zero] at hz
  exact sub_eq_zero.1 hz

end GlobalTheory.CompanionTheory.RealCount.IntegrateK
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSocleSegmentProductStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_socle_segment_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (dec Δ a).1 = N), ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr (dec Δ) hd) := by
  first | exact @GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec | exact GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec | (intros; apply GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwoStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fine_jacquet_segment_length_two : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) (h : Δ.len = 2), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegFine2.fineJac_of_len_eq_two | exact GlobalTheory.CompanionTheory.SegFine2.fineJac_of_len_eq_two | (intros; apply GlobalTheory.CompanionTheory.SegFine2.fineJac_of_len_eq_two <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicSiegelWeilIntegralIdentityStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_siegel_weil_integral_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Af F) σ n), ν.IsAddHaarMeasure →
  ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    Integrable (starLoc (Af F) σ J (psiFin F ψ) μ Q) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.integrable_starLoc_fin | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.integrable_starLoc_fin | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.integrable_starLoc_fin <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HCoContinuousAddEquiv
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem hCo_continuousAddEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), ∃ e : HermR R σ n ≃ₜ+ (Idx n d → R), ∀ S, e S = hCo R σ b S := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ d b n
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM
  have hfin : Module.finrank F E = 2 := hCM.2.2.1
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  let h1 : HermR R σ n ≃ₜ (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv hfin hδ hσδ n t5 t6).homeomorph _
  let h2 : (R ⊗[F] E) ≃ₜ (Fin d → R) := (t7 d b).homeomorph _
  have h2a : ∀ y k, h2 y k = (Algebra.TensorProduct.basis R b).repr y k := fun _ _ => rfl
  let G : ((Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) ≃ₜ (Idx n d → R) :=
    { toFun := fun x => Sum.elim x.1 (fun q => h2 (x.2 q.2) q.1)
      invFun := fun f => (fun i => f (Sum.inl i), fun p => h2.symm fun k => f (Sum.inr (k, p)))
      left_inv := by
        rintro ⟨x, y⟩
        refine Prod.ext rfl ?_
        funext p
        exact h2.symm_apply_apply (y p)
      right_inv := by
        intro f
        funext q
        rcases q with i | ⟨k, p⟩
        · rfl
        · simp
      continuous_toFun := by
        refine continuous_pi fun q => ?_
        rcases q with i | ⟨k, p⟩
        · exact (continuous_apply i).comp continuous_fst
        · exact (continuous_apply k).comp
            (h2.continuous.comp ((continuous_apply p).comp continuous_snd))
      continuous_invFun := by
        refine Continuous.prodMk (continuous_pi fun i => continuous_apply _) (continuous_pi fun p => ?_)
        exact h2.symm.continuous.comp (continuous_pi fun k => continuous_apply _) }
  let H : HermR R σ n ≃ₜ (Idx n d → R) := h1.trans G
  have hH : ∀ S, H S = hCo R σ b S := by
    intro S
    funext q
    rcases q with i | ⟨k, p⟩ <;> rfl
  refine ⟨{ toEquiv := H.toEquiv
            map_add' := ?_
            continuous_toFun := H.continuous
            continuous_invFun := H.symm.continuous }, hH⟩
  intro S T
  show H (S + T) = H S + H T
  rw [hH, hH, hH]
  funext q
  rcases q with i | ⟨k, p⟩
  · simp [hCo, map_add, mul_add]
  · simp [hCo, map_add]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalFormL2MemStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_cuspidal_form_l2_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ W : Submodule ℂ (Sm E a), IsStable W → (∀ φ ∈ W, IsAutForm φ ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → (classes W μ).topologicalClosure = H → ∀ φ : Sm E a, IsAutForm φ → ∀ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H → φ ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem | exact GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem | (intros; apply GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem <;> assumption)
end

