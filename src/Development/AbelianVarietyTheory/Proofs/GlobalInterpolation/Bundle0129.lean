import Mathlib
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0125
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0126
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralPeriodElement
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChiLastStepFiniteOrderSymTie
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem chi_last_step_finite_order_symTie : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), (∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)) → ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) := by
  intro D u Ch chOf Tf hζ
  have hpos : ∀ i, 0 < D.host.g i * (D.host.g i - 1) := fun i =>
    Nat.mul_pos (D.host.g_prime i).pos (Nat.sub_pos_of_lt (D.host.g_prime i).one_lt)
  refine ⟨∏ i, D.host.g i * (D.host.g i - 1), Finset.prod_pos fun i _ => hpos i, ?_⟩
  refine GlobalTheory.gLevH_chi_pow_eq_one_and_mem_range _ _ _ _ _ _ _ _ _ _ _ _ _ Tf.glevM D.what₂.LL D.what₂.embLL _ D.host.g_prime ?_
  intro a v h M
  have key : (∃ r : D.what₂.LL, D.what₂.embLL r = ((Tf.lamM a v h M : ℂˣ) : ℂ)) ∧
      (((Tf.lamM a v h M : ℂˣ) : ℂ) ≠ 0 → ((Tf.lamM a v h M : ℂˣ) : ℂ) ^ (D.host.g a * (D.host.g a - 1)) = 1) := by
    rw [Tf.lamM_eq]
    unfold lamSym
    exact GlobalTheory.lamJ_mem_range_and_pow_eq_one _ D.what₂.LL D.what₂.embLL _ (D.host.g_prime a) (GlobalTheory.T.card_residue_field_totally_real_type_prime D a v h) (hζ a).1 (hζ a).2
      _ _ _ _ _ _ _ _
  refine ⟨?_, key.1⟩
  obtain ⟨c, hc⟩ : D.host.g a * (D.host.g a - 1) ∣ ∏ i, D.host.g i * (D.host.g i - 1) :=
    Finset.dvd_prod_of_mem (fun i => D.host.g i * (D.host.g i - 1)) (Finset.mem_univ a)
  rw [hc, pow_mul, key.2 (Units.ne_zero _), one_pow]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassPairingIntegralFormRowIsIntegral
section
noncomputable section

namespace GlobalTheory.PairAtClass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

section

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
  (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hQ : Q.Ok)

theorem petersson_single_left (g w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) w = Q.wt c * ipVal emb σ Q.sgT (g c) (w c) := by
  letI := Q.clFin hQ
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

theorem petersson_single_right (g w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    Q.ipP emb σ hQ g (fun c' => if c' = c then w c' else 0) = Q.wt c * ipVal emb σ Q.sgT (g c) (w c) := by
  letI := Q.clFin hQ
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

theorem period_single (hI : I.Ok) (hc : ι → HCParam R) (G : Q.Mt emb σ)
    (w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    (Q.per emb σ hI hQ hc).period (fun c' => if c' = c then w c' else 0) G =
      Q.wt c * pairB Q.sgT (polOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) (fr0 emb σ (R.N R.m - 1)) (w c))
        (Q.rd emb σ G c) := by
  letI := Q.clFin hQ
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

end

theorem pair_integral : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hI : I.Ok) (hQ : Q.Ok) (hc : ι → HCParam R) (hF : (Q.S'.fam emb Q.sgT).Ok) (G : Q.Mt emb σ) (g : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ), (∀ w, (Q.per emb σ hI hQ hc).period w G = Q.ipP emb σ hQ g w) → ∀ (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] (y : Formalism.L2.DIV.VV K Q.sgT), y ∈ nabAt emb Q.sgT (Q.S'.Lsh c.1 (Q.S'.rep c)) → Q.rd emb σ G c = MvPolynomial.map σ y.1 → ∀ x ∈ (Q.S'.hlat emb Q.sgT hF).L, ∃ a : 𝓞 K, σ (a : K) = ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) * Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
  intro E K ι _ _ _ _ _ _ _ emb σ R I Q hI hQ hc hF G g hP c _ y hy hG x hx
  have hfin := hQ.step.fin_stab c.1 (Q.S'.rep c)
  have hne : ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) ≠ 0 := by
    haveI := hfin
    exact_mod_cast Nat.card_pos.ne'
  have hint := ((GlobalTheory.PeriodClassSum.pairBDual E K ι _ emb Q.sgT _ (hQ.step.lsh_lat c.1 (Q.S'.rep c)) (x.1 c)).1.1
    (hx c)) y hy
  obtain ⟨a, ha⟩ := hint
  refine ⟨a, ?_⟩
  have e12 : Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0)
      (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) =
      Q.ipP emb σ hQ g (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
    rw [petersson_single_left, petersson_single_right]
    simp
  rw [e12, ← hP, period_single, hG]
  show _ = _ * (Q.wt c * pairB Q.sgT (polOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) (fr0 emb σ (R.N R.m - 1))
    (evV emb (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) E) Q.sgT σ (x.1 c))) (MvPolynomial.map σ y.1))
  rw [GlobalTheory.PeriodOnStep.polOf_evV, ← GlobalTheory.PeriodOnStep.map_pairB, ← pairBK_apply, PerIn.wt, ← mul_assoc,
    mul_inv_cancel₀ hne, one_mul]
  rw [← ha, LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_one]

end GlobalTheory.PairAtClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOneStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measure_isCov1 : ∀ (F : Type) [Field F] [NumberField F], ∃ ν : Measure (AF F), IsCov1 ν := by
  first | exact @GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one | exact GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one | (intros; apply GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjPolynomialDefiniteUnitaryRationalStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_polynomial_definiteUnitary_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ), ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ p' ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  first | exact @GlobalTheory.UnitaryBC.exists_conj_polyFun | exact GlobalTheory.UnitaryBC.exists_conj_polyFun | (intros; apply GlobalTheory.UnitaryBC.exists_conj_polyFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEqStandardAdeleCharRationalDilate
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

namespace GlobalTheory.AdelicCharDilate

theorem exists_eq_std_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ ψ₀, IsStdChar F ψ₀ → ∀ ψ, IsCharAF F ψ →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x) := by
  intro F E _ _ _ _ _ _ σ hCM _ _ ψ₀ h₀ ψ h
  haveI := hCM.1
  exact GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real F ψ₀ ψ h₀.1 h

end GlobalTheory.AdelicCharDilate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralPeriodElementStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_period_element : EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement →
    ∀ (D : D7), Formalism.MainNotions.GL3Theta.admJ D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
      [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
      ∃ X : M, X ≠ 0 ∧ IsIntegral ℤ (X : ℂ) ∧ ∀ (ρ : M →ₐ[ℚ] ℂ) (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im →
        JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ (lamOf D cc δ)) ω₁ τ → ∀ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b →
        JacobiThetaHalfCharacteristic.thetaChar a b (t ρ / ω₁) τ = 0 →
        ‖ρ X‖ = (‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ / ‖ModularForm.eta τ‖) ^ 12 := by
  first | exact @GlobalTheory.IntegralX.exists_integral_theta_ratio | exact GlobalTheory.IntegralX.exists_integral_theta_ratio | (intros; apply GlobalTheory.IntegralX.exists_integral_theta_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnif
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section
namespace GlobalTheory.SumMaj
open scoped Classical
variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem re_add (x y : Ainf F) (w : InfinitePlace F) : re (x + y) w = re x w + re y w := by
  show (InfinitePlace.Completion.extensionEmbedding w (x w + y w)).re = _
  rw [map_add, Complex.add_re]; rfl

theorem abs_re_algebraMap (hF : IsTotallyReal F) (x : F) (w : InfinitePlace F) :
    |re (algebraMap F (Ainf F) x) w| = w x := by
  unfold re
  have hw : w.IsReal := hF.isReal w
  rw [InfiniteAdeleRing.algebraMap_apply]
  rw [InfinitePlace.Completion.extensionEmbedding_coe]
  rw [← InfinitePlace.embedding_of_isReal_apply hw, Complex.ofReal_re]
  first
  | (rw [← Real.norm_eq_abs]; exact InfinitePlace.norm_embedding_of_isReal hw x)
  | simpa [Real.norm_eq_abs] using InfinitePlace.norm_embedding_of_isReal hw x

theorem sz_nonneg (u : Fin N → AF F) : 0 ≤ sz u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem sz_sub_le (u y : Fin N → AF F) : sz u - sz y ≤ sz (u + y) := by
  unfold sz
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  have h : re (inf (u + y) l) w = re (inf u l) w + re (inf y l) w := by
    rw [← re_add]; congr 1
  rw [h]
  have := abs_sub_abs_le_abs_sub (re (inf u l) w) (-(re (inf y l) w))
  simpa [abs_neg, sub_neg_eq_add] using this

theorem continuous_sz : Continuous (sz : (Fin N → AF F) → ℝ) := by
  unfold sz
  refine continuous_finset_sum _ fun l _ => continuous_finset_sum _ fun w _ => ?_
  have h1 : Continuous fun u : Fin N → AF F => inf u l := by
    show Continuous fun u : Fin N → AF F => (u l).1
    exact continuous_fst.comp (continuous_apply l)
  have h2 : Continuous fun x : Ainf F => re x w :=
    Complex.continuous_re.comp ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      (continuous_apply w))
  exact continuous_abs.comp (h2.comp h1)

theorem continuous_fin : Continuous (fin : (Fin N → AF F) → Fin N → Af F) := by
  refine continuous_pi fun l => ?_
  show Continuous fun u : Fin N → AF F => (u l).2
  exact continuous_snd.comp (continuous_apply l)

theorem fin_add (u y : Fin N → AF F) : fin (u + y) = fin u + fin y := by
  funext l; simp [fin, map_add]

theorem inf_rat (ξ : Fin N → F) (l : Fin N) : inf (rat ξ) l = algebraMap F (Ainf F) (ξ l) := by
  simp [inf, rat]

theorem fin_rat (ξ : Fin N → F) (l : Fin N) : fin (rat ξ) l = algebraMap F (Af F) (ξ l) := by
  simp [fin, rat]

theorem norm_le_sz (hF : IsTotallyReal F) (ξ : Fin N → F) :
    ‖(fun l => mixedEmbedding F (ξ l))‖ ≤ sz (rat ξ) := by
  refine (pi_norm_le_iff_of_nonneg (sz_nonneg _)).2 fun l => ?_
  classical
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply]
  unfold sz
  calc w (ξ l) = |re (inf (rat ξ) l) w| := by rw [inf_rat, abs_re_algebraMap hF]
    _ ≤ ∑ w', |re (inf (rat ξ) l) w'| :=
        Finset.single_le_sum (f := fun w' => |re (inf (rat ξ) l) w'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ w)
    _ ≤ _ := Finset.single_le_sum (f := fun l' => ∑ w', |re (inf (rat ξ) l') w'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l)

theorem finrank_le_of_discrete {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] : Module.finrank ℤ L ≤ Module.finrank ℝ E := by
  let E' := Submodule.span ℝ (L : Set E)
  let L' : Submodule ℤ E' := ZLattice.comap ℝ L E'.subtype
  haveI : DiscreteTopology L' :=
    ZLattice.comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
  haveI : IsZLattice ℝ L' :=
    ⟨Submodule.map_injective_of_injective E'.subtype_injective (by simp [E', L'])⟩
  let e : L' ≃ₗ[ℤ] L := Submodule.comapSubtypeEquivOfLe (p := L) (q := E'.restrictScalars ℤ)
    Submodule.subset_span
  rw [← e.finrank_eq, ZLattice.rank ℝ L']
  exact Submodule.finrank_le E'

end GlobalTheory.SumMaj

namespace GlobalTheory.SumMaj
open scoped Classical

theorem summable_majorant : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ K : Set (Fin N → Af F), IsCompact K → ∃ k : ℕ, ∀ ω : Set (Fin N → AF F), IsCompact ω →
      ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧
        ∀ ξ, ∀ y ∈ ω, fin (rat ξ + y) ∈ K → 1 ≤ c ξ * (1 + sz (rat ξ + y)) ^ k := by
  intro F _ _ N hF K hK
  refine ⟨Module.finrank ℝ (Fin N → mixedEmbedding.mixedSpace F) + 1, fun ω hω => ?_⟩
  set k := Module.finrank ℝ (Fin N → mixedEmbedding.mixedSpace F) + 1 with hk
  obtain ⟨B, hB⟩ := hω.bddAbove_image (continuous_sz (F := F) (N := N)).continuousOn
  set B0 := max B 0 with hB0
  have hB0n : 0 ≤ B0 := le_max_right _ _
  have hszB : ∀ y ∈ ω, sz y ≤ B0 := fun y hy => (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  set K' : Set (Fin N → Af F) := (fun p : (Fin N → Af F) × (Fin N → Af F) => p.1 - p.2) '' (K ×ˢ (fin '' ω))
    with hK'
  have hK'c : IsCompact K' :=
    (hK.prod (hω.image continuous_fin)).image (continuous_fst.sub continuous_snd)
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hK'c
  set S : Set (Fin N → F) := {ξ | fin (rat ξ) ∈ K'} with hS
  set c : (Fin N → F) → ℝ := S.indicator fun ξ => (1 + B0) ^ k / (1 + sz (rat ξ)) ^ k with hc
  have hc0 : ∀ ξ, 0 ≤ c ξ := fun ξ =>
    Set.indicator_nonneg (fun ξ _ => div_nonneg (pow_nonneg (by linarith) _)
      (pow_nonneg (by linarith [sz_nonneg (rat ξ)]) _)) ξ
  refine ⟨c, ?_, hc0, fun ξ y hy hξ => ?_⟩
  · haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F (Fin N) hM0
    set L := GlobalTheory.WeilM.denomLattice F (Fin N) M with hL
    have memL : ∀ ξ ∈ S, (fun i => mixedEmbedding F (ξ i)) ∈ L := by
      intro ξ hξ i
      obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((M : F) * ξ i)
        fun v => by
          rw [map_mul, map_natCast]
          have := hM _ hξ i v
          rwa [fin_rat] at this
      refine ⟨y, ?_⟩
      have h2 := congrArg (mixedEmbedding F) hy
      rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
      exact h2.symm
    let j : S → L := fun ξ => ⟨_, memL ξ.1 ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    have hkL : Module.finrank ℤ L < k := Nat.lt_succ_of_le (finrank_le_of_discrete L)
    have hg : Summable fun z : L => ((1 + ‖z‖) ^ k)⁻¹ := by
      refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L k hkL) ?_
      refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
      by_contra h0
      apply hz
      show ‖((1 + ‖z‖) ^ k)⁻¹‖ ≤ ‖z‖⁻¹ ^ k
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
      rw [Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg (by positivity) _)), inv_pow]
      exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)
    refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
    · intro ξ hξ
      have : ξ ∉ S := fun h => hξ ⟨⟨ξ, h⟩, rfl⟩
      exact Set.indicator_of_notMem this _
    · refine Summable.of_nonneg_of_le (fun ξ => hc0 _) (fun ξ => ?_) ((hg.comp_injective hj).mul_left ((1 + B0) ^ k))
      show c ξ.1 ≤ (1 + B0) ^ k * ((1 + ‖j ξ‖) ^ k)⁻¹
      rw [hc, Set.indicator_of_mem ξ.2, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _)
      have hn : ‖j ξ‖ ≤ sz (rat ξ.1) := norm_le_sz hF ξ.1
      exact inv_anti₀ (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) (by linarith) _)
  · have hS' : ξ ∈ S := by
      refine ⟨(fin (rat ξ + y), fin y), ⟨hξ, y, hy, rfl⟩, ?_⟩
      simp [fin_add]
    rw [hc, Set.indicator_of_mem hS']
    have hs0 := sz_nonneg (rat ξ)
    have ht0 := sz_nonneg (rat ξ + y)
    have hst := sz_sub_le (rat ξ) y
    have hy0 := hszB y hy
    have key : 1 + sz (rat ξ) ≤ (1 + B0) * (1 + sz (rat ξ + y)) := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos (by linarith) _), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) key _

end GlobalTheory.SumMaj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourfoldLatticeIsometryDenominatorCoprimeStatement
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourfoldLattice_isometry_denominator_coprime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ x : Fin 4 → D.host.E, (∀ a, x a ∈ D.host.AA0) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ w, (s : D.host.K) * G (B.γ₀.g x) w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  first | exact @GlobalTheory.MomKapi.denom_prime_to | exact GlobalTheory.MomKapi.denom_prime_to | (intros; apply GlobalTheory.MomKapi.denom_prime_to <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralAdelicVectorsCharacterOrthogonalityStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_adelicVectors_character_orthogonality : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ ξ : Fin N → F, ξ ≠ 0 → ∫ u in D, ψ (Bd (AF F) a u (rat ξ)) ∂(muV N ν) = 0 := by
  first | exact @GlobalTheory.SWQ.charOrth | exact GlobalTheory.SWQ.charOrth | (intros; apply GlobalTheory.SWQ.charOrth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InverseIsometryFourfoldLatticeDenominatorCoprimeStatement
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseIsometry_fourfoldLattice_denominator_coprime_alt : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, (∀ w, v w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ a, (s : D.host.E) * B.γ₀.g.symm (G.symm v) a ∈ D.host.AA0 := by
  first | exact @GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime | exact GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime | (intros; apply GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCountableDiscreteWithFundDomainsRationalVector
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure MeasureTheory

namespace GlobalTheory.RationalStabiliserDomains

theorem isDiscreteWithDomains_inf_subgroupOf {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ S : Subgroup G) [Countable Γ] [DiscreteTopology Γ] :
    IsDiscreteWithDomains ((Γ ⊓ S).subgroupOf S) := by
  let f : (Γ ⊓ S).subgroupOf S → Γ := fun g => ⟨g.1.1, g.2.1⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h))
  have hc : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have : Countable ((Γ ⊓ S).subgroupOf S) := hf.countable
  have : DiscreteTopology ((Γ ⊓ S).subgroupOf S) := DiscreteTopology.of_continuous_injective hc hf
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology (S : Set G)
  exact GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_of_discrete _

theorem isDiscreteWithDomains_HstabFin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsDiscreteWithDomains (HstabFin (AF F) σ J x) := by
  intro F E _ _ _ _ _ σ _ M J _ x _
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have h := GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts' F E σ M J
  have := h.1
  have := h.2.1
  exact isDiscreteWithDomains_inf_subgroupOf (ratPts (AF F) σ J) (Hstab (AF F) σ J x)

end GlobalTheory.RationalStabiliserDomains
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeFactsAll
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
open IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.ThetaMove.SeamMoves Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

noncomputable section

namespace GlobalTheory.MomLat

theorem latticeFactsAll : GlobalTheory.MomT.LatticeFactsAll := by
  intro D X s cc δ B χ cD hX hs hcc hδ hχ a b ha hb
  have hL := GlobalTheory.ThetaMove.LatticeFacts.latAll B hcc hδ
  have hVm := B.vec_mem_ne hcc hδ (delta_ne_zero B) (B.stdOK hcc hδ) χ hχ
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ B χ cD hs
  have hq := qIntAll_of_latAll D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s B χ cD, fun N N' h h' => ?_⟩, fun N N' h h' k => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N N') (lam (ambOf s B χ cD) N N') (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N'))
      (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
    exact ⟨h3 (B.eNat χ a b (s.lat N) (s.lat N')) (hVm a b _ _ (hadm N N' h h')).1.2, h1, h2⟩
  · have hd : ContDiff ℂ (k : WithTop ℕ∞) (B.eNat χ a b (s.lat N) (s.lat N')) :=
      GlobalTheory.SCV.contDiff_of_differentiable (hVm a b _ _ (hadm N N' h h')).1.1 _
    exact hd.comp (reidx s a b).toLinearMap.toContinuousLinearMap.contDiff

end GlobalTheory.MomLat
end
end

