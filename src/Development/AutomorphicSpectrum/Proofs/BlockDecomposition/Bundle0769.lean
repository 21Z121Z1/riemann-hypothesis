import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInduction
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0763
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0757
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0761
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.BoxIntegrals.MeanBlocks
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0764
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0152
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0765

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsResidueCharacterOfConductor
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.ResChar

theorem local_component_additive_character_add {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s := by
  have h1 : singleV F v (r + s) = singleV F v r + singleV F v s := by
    classical
    unfold singleV
    first
    | exact Subtype.ext (Pi.single_add v r s)
    | (apply Subtype.ext
       exact Pi.single_add v r s)
    | (apply Subtype.ext
       funext w
       show Pi.single v (r + s) w = Pi.single v r w + Pi.single v s w
       rw [Pi.single_add]
       rfl)
  have h2 : pairA F 0 (singleV F v (r + s)) = pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) := by
    rw [h1]
    show ((0 : Ainf F), singleV F v r + singleV F v s) = ((0 : Ainf F) + 0, singleV F v r + singleV F v s)
    rw [add_zero]
  simp only [psiV]
  rw [h2, AddChar.map_add_eq_mul]

theorem dvd_of_nonunit {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R] {p x : R}
    (hp : Irreducible p) (hx : ¬ IsUnit x) : p ∣ x := by
  rcases ValuationRing.dvd_total p x with h | ⟨c, hc⟩
  · exact h
  · rcases hp.isUnit_or_isUnit hc with h | h
    · exact absurd h hx
    · exact ⟨↑h.unit⁻¹, by rw [hc, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ ϖ : Ov D v, Irreducible ϖ → ∀ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → ∃ ψ₀ : AddChar (kv D v) ℂ, ψ₀ ≠ 1 ∧ ∀ c : Ov D v, psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) = ψ₀ (IsLocalRing.residue (Ov D v) c) := by
  intro D ψ v hψ ϖ hϖ w hw
  classical
  set f : Ov D v → ℂ := fun c => psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) with hf
  have hadd : ∀ a b, f (a + b) = f a * f b := by
    intro a b
    simp only [hf, map_add, mul_add]
    exact local_component_additive_character_add ψ v _ _
  have hker : ∀ d, f (ϖ * d) = 1 := by
    intro d
    have e : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) (ϖ * d) = algebraMap (Ov D v) (Lv D v) d := by
      rw [map_mul, ← hw, ← mul_assoc, Units.inv_mul, one_mul]
    simp only [hf, e]
    exact hψ.1 _ d.2
  have hwd : ∀ a b, IsLocalRing.residue (Ov D v) a = IsLocalRing.residue (Ov D v) b → f a = f b := by
    intro a b h
    have h0 : IsLocalRing.residue (Ov D v) (a - b) = 0 := by rw [map_sub, h, sub_self]
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp h0
    obtain ⟨d, hd⟩ := dvd_of_nonunit hϖ (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hm))
    have e : a = b + ϖ * d := by rw [← hd]; ring
    rw [e, hadd, hker, mul_one]
  have hf0 : f 0 = 1 := by simpa using hker 0
  let g : kv D v → Ov D v := fun z => Classical.choose (IsLocalRing.residue_surjective z)
  have hg : ∀ z, IsLocalRing.residue (Ov D v) (g z) = z := fun z =>
    Classical.choose_spec (IsLocalRing.residue_surjective z)
  let ψ₀ : AddChar (kv D v) ℂ :=
    { toFun := fun z => f (g z)
      map_zero_eq_one' := by
        show f (g 0) = 1
        rw [hwd (g 0) 0 (by rw [hg, map_zero]), hf0]
      map_add_eq_mul' := by
        intro z z'
        show f (g (z + z')) = f (g z) * f (g z')
        rw [← hadd]
        exact hwd _ _ (by rw [hg, map_add, hg, hg]) }
  have hψ₀ : ∀ c, ψ₀ (IsLocalRing.residue (Ov D v) c) = f c := fun c => by
    show f (g _) = f c
    exact hwd _ _ (hg _)
  refine ⟨ψ₀, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hψ.2 ϖ hϖ
    intro h1
    apply hb
    have e1 : ψ₀ (IsLocalRing.residue (Ov D v) b) = 1 := by rw [h1]; exact AddChar.one_apply _
    rw [hψ₀] at e1
    have e : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) b = (b : Fv D.host.F v) / (ϖ : Fv D.host.F v) := by
      rw [Units.val_inv_eq_inv_val, hw, div_eq_inv_mul]; rfl
    rw [← e]
    exact e1
  · intro c
    exact (hψ₀ c).symm

end GlobalTheory.CompanionTheory.Jp.ResChar

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInductionStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fine_jacquet_segment_induction : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h3 : 3 ≤ Δ.len) (ih : ∀ Δ' : Segment k, Δ'.len < Δ.len → FineJac Δ'), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegFine.fineJac_step | exact GlobalTheory.CompanionTheory.SegFine.fineJac_step | (intros; apply GlobalTheory.CompanionTheory.SegFine.fineJac_step <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierCoefficientConjugationStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_coefficient_conjugation : ∀ {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ F : G D n → ℂ, Continuous F → LeftInv (GF D n) F → ∀ {nb : hermA D n → G D n} {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}, CoefData nb lam 𝓖 → ∀ (a : GL (Fin n) D.host.E) (β : HermE D n), ∃ q : G D n, ∀ g, fc ψ lam 𝓖 nb F β (q * g) = fc ψ lam 𝓖 nb F (cg a β) g := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.fc_levi | exact GlobalTheory.CompanionTheory.PcFc.fc_levi | (intros; apply GlobalTheory.CompanionTheory.PcFc.fc_levi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDiagonalNormalFormStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_block_diagonal_normal_form : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (β : HermE D n), ρ ≤ β.1.rank → ∃ (a : GL (Fin n) D.host.E) (b₀ : HermE D ρ) (β' : HermE D p), IsDiagInv b₀ ∧ cg a β = dsum hn b₀ β' := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum | exact GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum | (intros; apply GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianEulerProductStandardStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_euler_product_standard : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ n : ℕ, 0 < n → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → HermR (Ainf F) σ n → ℝ) (U : ℕ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (HermR (Fv F v) σ n)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : HermR (Fv F v) σ n) ∈ U k v) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets) ∧ (∀ k v, 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal) ∧ (∀ k, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k))) db ∧ ∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y * ψ (pairHerm (AF F) σ n y z) ∂db = GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ) * ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℂ)) ∧ (∀ k y, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y‖ ≤ ‖∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db‖) ∧ ∀ y, Filter.Tendsto (fun k => GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) Filter.atTop (nhds ((GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ y))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg.exists_test_approx | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg.exists_test_approx | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg.exists_test_approx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianIntegralBlockFubini
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_integral_block_fubini : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (m : Meas D ρ p) {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}, IsCovolOneH lam 𝓖 → ∀ {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)}, IsCovolOneH lp 𝓖p → ∀ Φ : hermA D n → ℂ, Continuous Φ → IsPer Φ → ∫ b in 𝓖, Φ b ∂lam = ∫ y in 𝓖p, ∫ x in m.𝓕, ∫ z in m.𝓖, Φ (bT hn z x y) ∂m.lz ∂m.μ ∂lp := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.mean_blocks | exact GlobalTheory.CompanionTheory.PcFc.mean_blocks | (intros; apply GlobalTheory.CompanionTheory.PcFc.mean_blocks <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzRestrictionColumns
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColSlice

variable {D : D7} {n r t a : ℕ}

def colIdx (hn : r + t = n) (j : Fin t) : Fin n := finCongr hn (finSumFinEquiv (Sum.inr j))

theorem colIdx_injective (hn : r + t = n) : Function.Injective (colIdx hn) := fun _ _ h =>
  Sum.inr_injective (finSumFinEquiv.injective ((finCongr hn).injective h))

def colPr (hn : r + t = n) (y : Mx D a n) : Mx D a t := y.submatrix id (colIdx hn)

theorem colPr_jn (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) : colPr hn (jn hn x v) = v := by
  ext i j
  simp [colPr, colIdx, jn, Matrix.submatrix_apply]

theorem continuous_colPr (hn : r + t = n) : Continuous (colPr (D := D) (a := a) hn) :=
  continuous_id.matrix_submatrix _ _

theorem continuous_jn (hn : r + t = n) (x : Mx D a r) : Continuous (jn (D := D) hn x) :=
  continuous_matrix fun i j => by
    show Continuous fun v : Mx D a t => Matrix.fromCols x v i ((finSumFinEquiv.trans (finCongr hn)).symm j)
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with s | s
    · exact continuous_const
    · exact continuous_id.matrix_elem i s

theorem realSize_le (θ : InfFam D) (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) :
    GlobalTheory.Unf.realSize θ v ≤ GlobalTheory.Unf.realSize θ (jn hn x v) := by
  unfold GlobalTheory.Unf.realSize
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => ?_
  have e : ∀ j, compAt θ τ v i j = compAt θ τ (jn hn x v) i (colIdx hn j) := fun j => by
    have := colPr_jn hn x v
    conv_lhs => rw [← this]
    rfl
  simp only [e]
  have h := Finset.sum_le_univ_sum_of_nonneg (f := fun j => ‖compAt θ τ (jn hn x v) i j‖)
    (s := Finset.univ.map ⟨colIdx hn, colIdx_injective hn⟩) fun _ => norm_nonneg _
  rw [Finset.sum_map] at h
  exact h

theorem maj_jn_le (θ : InfFam D) (hn : r + t = n) (K : Set (Mx D a n)) (N : ℕ) (x : Mx D a r) (v : Mx D a t) :
    GlobalTheory.Unf.maj θ K N (jn hn x v) ≤ GlobalTheory.Unf.maj θ (colPr hn '' K) N v := by
  by_cases hb : GlobalTheory.Unf.InBox K (jn hn x v)
  · have hb' : GlobalTheory.Unf.InBox (colPr hn '' K) v := by
      obtain ⟨k, hk, h0⟩ := hb
      refine ⟨colPr hn k, ⟨k, hk, rfl⟩, ?_⟩
      ext i j
      have := congrFun (congrFun h0 i) (colIdx hn j)
      have e : v i j = jn hn x v i (colIdx hn j) := by
        conv_lhs => rw [← colPr_jn hn x v]
        rfl
      show finPart D (v i j - k i (colIdx hn j)) = 0
      rw [e]
      exact this
    unfold GlobalTheory.Unf.maj
    rw [if_pos hb, if_pos hb']
    have h1 := GlobalTheory.Unf.realSize_nonneg θ v
    have h2 := realSize_le θ hn x v
    gcongr
  · have h0 : GlobalTheory.Unf.maj θ K N (jn hn x v) = 0 := by unfold GlobalTheory.Unf.maj; rw [if_neg hb]
    rw [h0]
    exact GlobalTheory.Unf.maj_nonneg θ _ N v

theorem integrable_slice : ∀ {D : D7} {n r t : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) {a : ℕ} (hn : r + t = n)
    (μt : Measure (Mx D a t)) [μt.IsAddHaarMeasure] (Φ : schwartzA θ a n) (x : Mx D a r),
    Integrable (fun v => Φ.1 (jn hn x v)) μt := by
  intro D n r t θ hθ a hn μt _ Φ x
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D a t
  haveI : BorelSpace (Mx D a t) := ⟨rfl⟩
  obtain ⟨hc, K, hK, hC⟩ := GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ a n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ a n Φ.1 Φ.2)
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajInt.maj_integrable D θ hθ a t (fun _ _ => True) 0 μt inferInstance
    (.of_forall fun _ _ _ h => (h trivial).elim) (fun s _ => map_add_right_eq_self μt s)
  obtain ⟨C, hC⟩ := hC N
  have hK' : IsCompact (colPr hn '' K) := hK.image (continuous_colPr hn)
  have hC0 : ∀ v, ‖Φ.1 (jn hn x v)‖ ≤ |C| * GlobalTheory.Unf.maj θ (colPr hn '' K) N v := fun v =>
    (hC _).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (GlobalTheory.Unf.maj_nonneg θ K N _)).trans
      (mul_le_mul_of_nonneg_left (maj_jn_le θ hn K N x v) (abs_nonneg C)))
  exact ((hN _ hK').const_mul |C|).mono' (hc.comp (continuous_jn hn x)).aestronglyMeasurable (.of_forall hC0)

end GlobalTheory.CompanionTheory.ColSlice
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfCharacterTrivialOnLattice
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.DualInt

private theorem trace_single_one_mul {n : ℕ} {R : Type} [CommRing R] (i j : Fin n) (c : R)
    (T : Matrix (Fin n) (Fin n) R) : (Matrix.single j i c * T).trace = c * T i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem mem_of_dual_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) (Fv D.host.F v)), (∀ X : Matrix (Fin n) (Fin n) (Fv D.host.F v), (∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) → psiV D.host.F ψ v (Matrix.trace (X * T)) = 1) → ∀ i j, T i j ∈ v.adicCompletionIntegers D.host.F := by
  intro D ψ v hψ n T hT i j
  by_contra hx
  set O := v.adicCompletionIntegers D.host.F with hO
  have hx0 : T i j ≠ 0 := by
    intro h
    exact hx (h ▸ O.zero_mem)
  have hy : (T i j)⁻¹ ∈ O := (O.mem_or_inv_mem (T i j)).resolve_left hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : (ϖ : v.adicCompletion D.host.F) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hw : (T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F) ∈ O := by
    rcases O.mem_or_inv_mem ((T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F)) with h | h
    · exact h
    · have h' : (ϖ : v.adicCompletion D.host.F) / (T i j)⁻¹ ∈ O := by
        simpa [inv_div] using h
      have hfac : ϖ = (⟨(T i j)⁻¹, hy⟩ : O) * ⟨_, h'⟩ := by
        apply Subtype.ext
        simp only [MulMemClass.coe_mul]
        field_simp
      rcases hϖ.isUnit_or_isUnit hfac with hu | hu
      · exfalso
        apply hx
        obtain ⟨u, hu⟩ := hu
        have hmem : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) ∈ O := Subtype.property _
        have heq : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) = T i j := by
          have h1 : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) * (((u : Oˣ) : O) : v.adicCompletion D.host.F) = 1 := by
            rw [← MulMemClass.coe_mul, Units.inv_mul]
            rfl
          rw [hu] at h1
          field_simp at h1
          simpa using h1
        exact heq ▸ hmem
      · obtain ⟨u, hu⟩ := hu
        have hmem : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) ∈ O := Subtype.property _
        have heq : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) = (T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F) := by
          have h1 : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) * (((u : Oˣ) : O) : v.adicCompletion D.host.F) = 1 := by
            rw [← MulMemClass.coe_mul, Units.inv_mul]
            rfl
          rw [hu] at h1
          simp only at h1
          rw [eq_div_iff hϖ0]
          rw [div_inv_eq_mul, ← mul_assoc] at h1
          exact eq_inv_of_mul_eq_one_left h1
        exact heq ▸ hmem
  obtain ⟨b, hb⟩ := hψ.2 ϖ hϖ
  have hb2 : (b : v.adicCompletion D.host.F) ∈ O := b.2
  apply hb
  have hX := hT (Matrix.single j i ((b : v.adicCompletion D.host.F) * ((T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F)))) (by
    intro k l
    rw [Matrix.single_apply]
    split_ifs
    · exact mul_mem hb2 hw
    · exact O.zero_mem)
  rw [trace_single_one_mul] at hX
  convert hX using 2
  field_simp

end GlobalTheory.CompanionTheory.Jp.DualInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsExhaustionGlStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_multisegments_of_exhaustion_gl : (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSocleGL k) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSegJacquet k) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LOrderFree k) → GlobalTheory.Published.LanglandsExhaustionGL → GlobalTheory.Published.LanglandsMultisegments := by
  first | exact @GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses | exact GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses | (intros; apply GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalImageOfUnipotentElement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem block_unipotent_map {A B : Type} {m : ℕ} [Zero A] [One A] [Zero B] [One B] [DecidableEq (Fin m)] (f : A → B) (f0 : f 0 = 0)
    (f1 : f 1 = 1) (x : Matrix (Fin m) (Fin m) A) :
    (blk4 (1 : Matrix (Fin m) (Fin m) A) x 0 1).map f = blk4 1 (x.map f) 0 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite f, f0, f1]

theorem splitHom_proj_nMap (D : D7) (n : ℕ) (nb : hermA D n → G D n) (h : IsNMap nb) (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n) :
    (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 =
      blk4 1 (tauC τ x.1) 0 1 := by
  have e1 := GlobalTheory.LocIntw.matR_mapH (evFin D.host.F v) (nb x)
  rw [GlobalTheory.LocIntw.matR_adele, h x] at e1
  have e2 : (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 =
      (GlobalTheory.LocIntw.matR (Fv D.host.F v) D.sp.cm.sig
        (proj D.sp.cm.sig (Jst D n) v (nb x))).map (splitProj τ) := rfl
  have e3 : (GlobalTheory.LocIntw.matR (Fv D.host.F v) D.sp.cm.sig
      (proj D.sp.cm.sig (Jst D n) v (nb x))) = (blk4 1 x.1 0 1).map (cv D v) := e1
  rw [e2, e3, block_unipotent_map _ (map_zero _) (map_one _), block_unipotent_map _ (map_zero _) (map_one _)]
  rfl

theorem thU_proj_nMap (D : D7) (n : ℕ) (nb : hermA D n → G D n) (h : IsNMap nb) (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n) :
    thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x)) = nU (tauC τ x.1) := by
  have e := splitHom_proj_nMap D n nb h v τ x
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e' : (thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 i j =
      (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1
        (finSumFinEquiv i) (finSumFinEquiv j) := rfl
  rw [e', e]
  change (Matrix.fromBlocks 1 (tauC τ x.1) 0 1 : Matrix _ _ _)
    (finSumFinEquiv.symm (finSumFinEquiv i)) (finSumFinEquiv.symm (finSumFinEquiv j)) =
      (Matrix.fromBlocks 1 (tauC τ x.1) 0 1 : Matrix _ _ _) i j
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.Jp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedValuationUniformizer
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem nvOK_nvL : ∀ (D : D7) (v : Pl D) (ϖ : Ov D v), Irreducible ϖ → ∀ w : (Lv D v)ˣ,
    (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → NvOK (O := Ov D v) (nvL D v) w := by
  intro D v ϖ hϖ w hw
  have hu1 : Formalism.UG.IsUnifV D.host.F v (algebraMap (Ov D v) (Lv D v) ϖ) := by
    unfold Formalism.UG.IsUnifV
    rw [GlobalTheory.SplitDetValue.valued_irreducible v hϖ] <;> rfl
  have hn : ‖algebraMap (Ov D v) (Lv D v) ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ :=
    GlobalTheory.norm_uniformiser_eq_inv_absNorm D.host.F v _ hu1
  have hc : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ ≠ 0 := by
    rw [Ne, inv_eq_zero, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  unfold NvOK
  refine ⟨fun u => ?_, ?_⟩
  · show ‖algebraMap (Ov D v) (Lv D v) (u : Ov D v)‖₊ = 1
    have hu2 : Formalism.UG.IsUnifV D.host.F v (algebraMap (Ov D v) (Lv D v) ((u : Ov D v) * ϖ)) := by
      unfold Formalism.UG.IsUnifV
      rw [map_mul, map_mul, GlobalTheory.SplitDetValue.valued_unit v u, GlobalTheory.SplitDetValue.valued_irreducible v hϖ,
        one_mul] <;> rfl
    have h2 := GlobalTheory.norm_uniformiser_eq_inv_absNorm D.host.F v _ hu2
    rw [map_mul, nnnorm_mul, hn] at h2
    exact (mul_eq_right₀ hc).mp h2
  · show ‖(w : Lv D v)‖₊ = _
    rw [hw, hn, Fintype.card_eq_nat_card, GlobalTheory.SplitDetValue.card_residue_eq]

end GlobalTheory.CompanionTheory.Jp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientUnipotentMeanStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_coefficient_unipotent_mean : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (F : G D n → ℂ) {nb : hermA D n → G D n}, IsNMap nb → ∀ (g : G D n) (y : hermA D p), pc M m ψ b₀ F (nb (bT hn 0 0 y) * g) = pm hn m ψ b₀ (fun b => F (nb b * g)) y := by
  first | exact @GlobalTheory.CompanionTheory.PcNb.pc_nb | exact GlobalTheory.CompanionTheory.PcNb.pc_nb | (intros; apply GlobalTheory.CompanionTheory.PcNb.pc_nb <;> assumption)
end

