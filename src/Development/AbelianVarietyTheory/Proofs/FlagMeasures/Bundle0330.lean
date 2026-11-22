import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0016
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PowLePowRatio
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0213
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0152
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0322
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicLatticeClosureIffSwapMemSpan
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicLatticeSwap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))

private lemma mem_intAf_of_mem_intAd {a : Af F} (ha : a ∈ Formalism.UG.intAd F) : a ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  exact ha v

private lemma mem_intAd_of_mem_intAf {a : Af F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) : a ∈ Formalism.UG.intAd F := by
  intro v
  exact ha v

private lemma intAf_mul_mem {a b : Af F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) (hb : b ∈ Formalism.MainNotions.StandardLattice.intAf F) :
    a * b ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

private lemma one_mem_intAf_flag_measures : (1 : Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  rw [map_one]
  exact one_mem _

omit [NumberField E] in

theorem gen_smul_mem (a : Af F) (ha : a ∈ Formalism.UG.intAd F) (c : 𝓞 E)
    (y : Fin n → Af F ⊗[F] E) (hy : y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))) :
    (a ⊗ₜ[F] (c : E) : Af F ⊗[F] E) • y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.StandardLattice.latHat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    refine ⟨a * b, intAf_mul_mem (mem_intAf_of_mem_intAd ha) hb, c • x, L.smul_mem c hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

theorem int_smul_mem (t : E ⊗[F] Af F) (ht : t ∈ Formalism.MainNotions.S.IntAf F E) :
    ∀ y : Fin n → Af F ⊗[F] E, y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) →
      (Algebra.TensorProduct.comm F (Af F) E).symm t • y ∈
        Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at ht
  induction ht using Subring.closure_induction with
  | mem s hs =>
    intro y hy
    rcases hs with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
    · obtain ⟨c, rfl⟩ := he
      rw [Algebra.TensorProduct.comm_symm_tmul]
      exact gen_smul_mem L 1 (one_mem _) c y hy
    · rw [Algebra.TensorProduct.comm_symm_tmul]
      simpa using gen_smul_mem L b hb 1 y hy
  | zero => intro y _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro y hy; rw [map_one, one_smul]; exact hy
  | add s u _ _ hs hu => intro y hy; rw [map_add, add_smul]; exact add_mem (hs y hy) (hu y hy)
  | neg s _ hs => intro y hy; rw [map_neg, neg_smul]; exact neg_mem (hs y hy)
  | mul s u _ _ hs hu => intro y hy; rw [map_mul, mul_smul]; exact hs _ (hu y hy)

theorem symm_mem_of_mem (z : Fin n → E ⊗[F] Af F) (hz : z ∈ Formalism.MainNotions.S.lamAf (F := F) L) :
    (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (z i)) ∈
      Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.S.lamAf at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨x, hx⟩, rfl⟩ := hw
    unfold Formalism.MainNotions.StandardLattice.latHat
    apply AddSubgroup.subset_closure
    refine ⟨1, one_mem_intAf_flag_measures, x, hx, ?_⟩
    funext i
    show (Algebra.TensorProduct.comm F (Af F) E).symm ((x i) ⊗ₜ[F] (1 : Af F)) = (1 : Af F) ⊗ₜ[F] x i
    simp
  | zero =>
    have h0 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((0 : Fin n → E ⊗[F] Af F) i)) = 0 := by
      funext i
      simp
    rw [h0]
    exact zero_mem _
  | add u w _ _ hu hw =>
    have h1 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((u + w) i)) =
        (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (u i)) +
          fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (w i) := by
      funext i
      simp
    rw [h1]
    exact add_mem hu hw
  | smul s u _ hu =>
    have h2 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((s • u) i)) =
        (Algebra.TensorProduct.comm F (Af F) E).symm (s : E ⊗[F] Af F) •
          fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (u i) := by
      funext i
      simp [Subring.smul_def]
    rw [h2]
    exact int_smul_mem L s s.2 _ hu

theorem mem_latHat_iff_comm_mem_lamAf (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → Af F ⊗[F] E) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (Af F) E (y i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  constructor
  · intro hy
    unfold Formalism.MainNotions.StandardLattice.latHat at hy
    induction hy using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hw
      have hg : (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L :=
        Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      have hs : ((1 : E) ⊗ₜ[F] a : E ⊗[F] Af F) ∈ Formalism.MainNotions.S.IntAf F E :=
        Subring.subset_closure (Or.inr ⟨⟨a, mem_intAd_of_mem_intAf ha⟩, rfl⟩)
      convert Submodule.smul_mem _ (⟨_, hs⟩ : Formalism.MainNotions.S.IntAf F E) hg using 1
      funext i
      simp [Subring.smul_def, Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]
    | zero =>
      convert zero_mem (Formalism.MainNotions.S.lamAf (F := F) L) using 1
      funext i
      simp
    | add u w _ _ hu hw =>
      convert add_mem hu hw using 1
      funext i
      simp
    | neg u _ hu =>
      convert neg_mem hu using 1
      funext i
      simp
  · intro hz
    simpa using symm_mem_of_mem L _ hz

end GlobalTheory.AdelicLatticeSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUnitaryGroupGramMatrixIffMapSymm
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

private theorem host_star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  haveI := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (star x) = starRingEnd ℂ (D.host.φ₀ x) :=
    NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (φ := D.host.φ₀) (x := x)
  have h2 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := by
    rw [← D.embE_φ₀, RingHom.comp_apply, RingHom.comp_apply, D.embE_conj, D.starLL_cx]
  rw [h1, h2]

theorem mem_UJ_gramN_iff_map_symm : ∀ (D : D7) (X : HidaSetting D) (g : GL (Fin (D.R.N 0)) D.host.E), g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ↔ (((g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm).map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm := by
  intro D X g

  have hc : ∀ y : D.host.E, X.ιE.symm ((Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) y) =
      starRingEnd X.B.I.E (X.ιE.symm y) := by
    intro y
    apply X.ιE.injective
    rw [starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact host_star_eq_conj D y
  have hm : ∀ A B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E,
      (A * B).map X.ιE.symm = A.map X.ιE.symm * B.map X.ιE.symm := by
    intro A B
    ext i j
    simp [Matrix.mul_apply, map_sum]
  have hb : ∀ A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E,
      (A.map X.ιE.symm).map (starRingEnd X.B.I.E) =
        (A.map (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)).map X.ιE.symm := by
    intro A
    ext i j
    exact (hc (A i j)).symm
  have hT : ∀ A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E,
      Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) A =
        (A.map (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E))ᵀ := by
    intro A
    unfold Formalism.UG.cT
    first
      | rfl
      | (ext i j; rfl)
  have hinj : Function.Injective
      (fun A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E => A.map X.ιE.symm) :=
    Matrix.map_injective X.ιE.symm.injective
  refine Iff.trans (Iff.rfl : _ ↔ Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) * Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) *
      (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ?_
  rw [hT, hb, ← Matrix.transpose_map (f := ⇑X.ιE.symm), ← hm, ← hm]
  exact hinj.eq_iff.symm

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTermsModeratePointsOneTypeBound
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.NearType

open GlobalTheory.FlagMeas

theorem layerProd_meas (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (de : ℝ) :
    Measurable fun τ : Fin a → ℝ => layerProd n f j τ (fun la => 1 + 12 * de / la) := by
  unfold layerProd
  fun_prop

theorem layerProd_nonneg (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (de : ℝ) (hde : 0 ≤ de) (τ : Fin a → ℝ)
    (hτ : ∀ i, 0 < τ i) : 0 ≤ layerProd n f j τ (fun la => 1 + 12 * de / la) := by
  have hG : ∀ la : ℝ, 0 < la → 0 ≤ 1 + 12 * de / la := fun la hla =>
    add_nonneg zero_le_one (div_nonneg (mul_nonneg (by norm_num) hde) hla.le)
  unfold layerProd
  apply mul_nonneg
  · refine Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun k _ => ?_
    exact mul_nonneg (pow_nonneg (hG _ (div_pos (hτ i) (hτ k))) _)
      (pow_nonneg (hG _ (mul_pos (hτ i) (hτ k))) _)
  · refine Finset.prod_nonneg fun i _ => ?_
    exact mul_nonneg (pow_nonneg (hG _ (hτ i)) _) (pow_nonneg (hG _ (pow_pos (hτ i) 2)) _)

theorem integral_count_dens (n f q a : ℕ) (j : Fin a → ℕ) (de lo M : ℝ) (hj : ∑ i, j i ≤ q) (hq : 2 * q ≤ n)
    (hde : 0 ≤ de) (hd : de * q * n * f ≤ 1 / 100) (hlo : 0 < lo) (hlo2 : lo ≤ 1 / 2) (hM : 0 ≤ M) :
    ∫⁻ τ in simplexH a, {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
        (fun τ => ENNReal.ofReal (M * layerProd n f j τ (fun la => 1 + 12 * de / la))) τ *
        ENNReal.ofReal (FlagMeas.dens n f j τ) ≤
      ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i * Real.log (1 / (2 * lo))) := by
  let S : Set (Fin a → ℝ) := Set.pi Set.univ (fun _ => Set.Icc lo (1 / 2))
  have hSm : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hc : ∀ i, 0 ≤ 2 * (f : ℝ) * j i := fun i => by positivity

  have hpt : ∀ τ ∈ simplexH a,
      {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
          (fun τ => ENNReal.ofReal (M * layerProd n f j τ (fun la => 1 + 12 * de / la))) τ *
        ENNReal.ofReal (FlagMeas.dens n f j τ) ≤
      S.indicator (fun τ => ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i)) τ := by
    intro τ hτ
    obtain ⟨hmono, h01⟩ := hτ
    by_cases hl : ∀ i, lo ≤ τ i
    · have hmem : τ ∈ S := fun i _ => ⟨hl i, (h01 i).2.le⟩
      rw [Set.indicator_of_mem (show τ ∈ {τ : Fin a → ℝ | ∀ i, lo ≤ τ i} from hl),
        Set.indicator_of_mem hmem,
        ← ENNReal.ofReal_mul (mul_nonneg hM (layerProd_nonneg n f j de hde τ fun i => (h01 i).1))]
      apply ENNReal.ofReal_le_ofReal
      have h2 : layerProd n f j τ (fun la => 1 + 12 * de / la) * layerProd n f j τ id ≤ 2 :=
        (GlobalTheory.Count.layerProd_count_mul_density_le_two n f q a j τ de hj hq hmono h01 hde hd).1
      have hP : 0 ≤ ∏ i, 2 * (f : ℝ) * j i / τ i :=
        Finset.prod_nonneg fun i _ => div_nonneg (hc i) (h01 i).1.le
      rw [FlagMeas.dens]
      calc M * layerProd n f j τ (fun la => 1 + 12 * de / la) *
            (layerProd n f j τ id * ∏ i, 2 * (f : ℝ) * j i / τ i)
          = M * (layerProd n f j τ (fun la => 1 + 12 * de / la) * layerProd n f j τ id) *
              ∏ i, 2 * (f : ℝ) * j i / τ i := by ring
        _ ≤ M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hM) hP
    · simp [Set.indicator_apply, hl]
  have hcont : ContinuousOn (fun τ : Fin a → ℝ => M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i) S := by
    refine continuousOn_const.mul (continuousOn_finset_prod _ fun i _ => ?_)
    exact continuousOn_const.div (continuous_apply i).continuousOn
      fun τ hτ => ne_of_gt (lt_of_lt_of_le hlo (hτ i (Set.mem_univ _)).1)
  have hint : IntegrableOn (fun τ : Fin a → ℝ => M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i) S :=
    hcont.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
  have hnn : ∀ᵐ τ ∂(volume.restrict S), (0 : (Fin a → ℝ) → ℝ) τ ≤ M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i := by
    refine ae_restrict_of_forall_mem hSm fun τ hτ => ?_
    have hpos : ∀ i, 0 < τ i := fun i => lt_of_lt_of_le hlo (hτ i (Set.mem_univ _)).1
    exact mul_nonneg (mul_nonneg hM (by norm_num))
      (Finset.prod_nonneg fun i _ => div_nonneg (hc i) (hpos i).le)
  have key := (GlobalTheory.sizeIntegrals_and_card_compositions).1 a (fun i => 2 * (f : ℝ) * j i) lo hlo hlo2 hc
  calc _ ≤ ∫⁻ τ in simplexH a,
          S.indicator (fun τ => ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i)) τ :=
        setLIntegral_mono' (GlobalTheory.FlagPush.simplex_meas a) hpt
    _ ≤ ∫⁻ τ, S.indicator (fun τ => ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i)) τ :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ τ in S, ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i) := lintegral_indicator hSm _
    _ = ENNReal.ofReal (∫ τ in S, M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i * Real.log (1 / (2 * lo))) := by
        rw [integral_const_mul]
        exact congrArg (fun r => ENNReal.ofReal (M * 2 * r)) key

theorem tsum_le_card {α : Type} (s t : Set α) (hst : s ⊆ t) (ht : t.Finite) (g : α → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hg : ∀ y, ‖g y‖ ≤ M) : ∑' y : s, ‖g y.1‖ₑ ≤ ENNReal.ofReal (M * (t.ncard : ℝ)) := by
  have hs : s.Finite := ht.subset hst
  haveI : Fintype s := hs.fintype
  calc ∑' y : s, ‖g y.1‖ₑ ≤ ∑' _ : s, ENNReal.ofReal M := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hg y.1)
    _ = (Fintype.card s : ENNReal) * ENNReal.ofReal M := by
        rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ (t.ncard : ENNReal) * ENNReal.ofReal M := by
        gcongr
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
        exact Set.ncard_le_ncard hst ht
    _ = ENNReal.ofReal (M * (t.ncard : ℝ)) := by
        rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_natCast, mul_comm]

theorem near_terms_one_type : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Dec.NearUnip → GlobalTheory.Deep.PtBound → ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ x, 1 / 2 ≤ least B.I x → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x = 0) ∧ ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund, {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (mainTerm B d * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j * (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a)) := by
  intro hF hN hP B Cg n₀ d p q b hn0 hq hC
  obtain ⟨-, -, hf1, -, -, h2q, -, hmin, hdpos, hX16, htpos, hsmall, h, -, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn0 hC
  obtain ⟨hDS, hSig, hn0n, hq2, -, -, -, -, -, -, -, hg0p, hg0, hsplit, -⟩ := hC
  have hn1 : 1 ≤ B.I.n := by omega
  have hnpos : (0 : ℝ) < B.I.n := by exact_mod_cast (show 0 < B.I.n by omega)
  have hfpos : (0 : ℝ) < B.I.f := by exact_mod_cast (show 0 < B.I.f by omega)
  have hrad : (Ideal.span {(B.g₀ : 𝓞 B.I.E)}).IsRadical :=
    GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver B.I.E B.g₀ hg0p hsplit

  set δ : ℝ := 3 * Real.sqrt (B.I.n * epN B) with hδdef
  obtain ⟨hnear, hδ4, hδq⟩ := hN B d (1 / 10 ^ 6) (by norm_num) (by norm_num) hn1 hg0 hrad (epN B) δ rfl rfl
  have hep : 0 < epN B := by
    unfold epN
    exact div_pos (by norm_num) (mul_pos (pow_pos hnpos 8) (pow_pos hfpos 2))
  have hδpos : 0 < δ := mul_pos (by norm_num) (Real.sqrt_pos.2 (mul_pos hnpos hep))
  have h120' : 120 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by rw [hmin]; exact h120
  obtain ⟨-, hbd, -, -, he1, -, -⟩ := hP B d p q h hDS hSig hgap h120'
  refine ⟨fun x hx => ?_, fun a j ha hj hjq => ?_⟩
  ·
    refine GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs_eq_zero B d x fun γ hγ => ?_
    have hmem := (hnear x γ hγ).2.2
    rw [GlobalTheory.NearLower.nearSet_eq B.I x δ hδpos hδ4 hx] at hmem
    exact hmem
  · set M : ℝ := (∏ v, d v) * (B.e 1).re with hMdef
    have hM : 0 ≤ M := mul_nonneg hdpos.le he1
    set lo : ℝ := tauStar B q b with hlodef
    have hlo2 : lo ≤ 1 / 2 := (hsmall hq).1.le
    have hmeasS : MeasurableSet {τ : Fin a → ℝ | ∀ i, lo ≤ τ i} := by
      rw [Set.setOf_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)
    have hGm : Measurable (fun τ : Fin a → ℝ => {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
        (fun τ => ENNReal.ofReal (M * layerProd B.I.n B.I.f j τ (fun la => 1 + 12 * δ / la))) τ) :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul (layerProd_meas B.I.n B.I.f j δ))).indicator
        hmeasS

    have hΦ : ∀ x τ, HasType B.I x j τ →
        {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ≤
          {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
            (fun τ => ENNReal.ofReal (M * layerProd B.I.n B.I.f j τ (fun la => 1 + 12 * δ / la))) τ := by
      intro x τ hx
      by_cases hl : tauStar B q b ≤ least B.I x
      · obtain ⟨S, hS, -⟩ := id hx
        have h0 := ((GlobalTheory.PointFlag.flag_spec B.I x).2.2 a S τ hS).2 hn1
        have hapos : 0 < a := by omega
        have hlo : ∀ i, lo ≤ τ i := by
          intro i
          have hm : τ ⟨0, hapos⟩ ≤ τ i := hS.2.2.2.1.monotone (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
          rw [h0.2 hapos] at hm
          exact le_trans hl hm
        rw [Set.indicator_of_mem (show x ∈ {x | tauStar B q b ≤ least B.I x} from hl),
          Set.indicator_of_mem (show τ ∈ {τ : Fin a → ℝ | ∀ i, lo ≤ τ i} from hlo)]
        obtain ⟨hfin, hcount⟩ := GlobalTheory.NearCount.near_count B.I x δ hδpos hδ4 a j τ hx
        have hsub : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x ⊆ nearSet B.I x δ := fun γ hγ => (hnear x γ hγ.1).2.2
        calc GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x
            ≤ ENNReal.ofReal (M * ((nearSet B.I x δ).ncard : ℝ)) :=
              tsum_le_card _ _ hsub hfin (fun y => phe B d (x⁻¹ * y * x)) M hM fun y => hbd _
          _ ≤ ENNReal.ofReal (M * layerProd B.I.n B.I.f j τ (fun la => 1 + 12 * δ / la)) :=
              ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcount hM)
      · simp [Set.indicator_apply, hl]
    have hfund := hF B.I B.μf B.fund B.fund_spec p q hSig h2q a j ha hj hjq (simplexH a)
      (GlobalTheory.FlagPush.simplex_meas a) le_rfl
    have hfin : B.I.muA B.μf B.fund ≠ ⊤ := hfund.2.2.1.ne
    have hint := integral_count_dens B.I.n B.I.f q a j δ lo M hjq (by omega) hδpos.le (hδq q hq2)
      htpos hlo2 hM

    have hX : 0 < bigX B b := lt_of_lt_of_le (by norm_num) hX16
    have hloX : lo * bigX B b ^ (11 * q) = 1 := by
      rw [hlodef]; unfold tauStar; rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hX.ne')]
    have hL0 : 0 ≤ Real.log (1 / (2 * lo)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hL : Real.log (1 / (2 * lo)) ≤ 11 * q * Real.log (bigX B b) := by
      have h1 : 1 / (2 * lo) ≤ bigX B b ^ (11 * q) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hloX]
      calc Real.log (1 / (2 * lo)) ≤ Real.log (bigX B b ^ (11 * q)) :=
            Real.log_le_log (by positivity) h1
        _ = 11 * q * Real.log (bigX B b) := by rw [Real.log_pow]; push_cast; ring
    have hPQ : ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo)) ≤
        (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a := by
      calc ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo))
          ≤ ∏ _i : Fin a, 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) := by
            refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
            have hji : (j i : ℝ) ≤ q := by
              exact_mod_cast le_trans (Finset.single_le_sum (fun k _ => Nat.zero_le (j k))
                (Finset.mem_univ i)) hjq
            have : 0 ≤ 2 * (B.I.f : ℝ) := by positivity
            calc 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo))
                ≤ 2 * (B.I.f : ℝ) * q * Real.log (1 / (2 * lo)) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hji this) hL0
              _ ≤ 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) :=
                  mul_le_mul_of_nonneg_left hL (by positivity)
        _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hmain : mainTerm B d = (B.I.muA B.μf B.fund).toReal * M := by
      rw [hMdef]; unfold mainTerm Formalism.MainNotions.S.AutInst.Dstar Formalism.MainNotions.S.AutInst.vol; ring
    calc ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund,
          {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf)
        ≤ B.I.muA B.μf B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
            ∫⁻ τ in simplexH a, {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
              (fun τ => ENNReal.ofReal (M * layerProd B.I.n B.I.f j τ (fun la => 1 + 12 * δ / la))) τ *
              ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) :=
          GlobalTheory.FlagPush.lintegral_type_le hF B p q hSig h2q a j ha hj hjq _ _ hGm hΦ
      _ ≤ B.I.muA B.μf B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
            ENNReal.ofReal (M * 2 * ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo))) :=
          mul_le_mul' le_rfl hint
      _ ≤ _ := by
          by_cases hk : GlobalTheory.FlagMeas.kapBd B.I.E p q j ≤ 0
          · rw [ENNReal.ofReal_of_nonpos hk, mul_zero, zero_mul]
            positivity
          · push_neg at hk
            have hvol : 0 ≤ (B.I.muA B.μf B.fund).toReal := ENNReal.toReal_nonneg
            rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hvol,
              ← ENNReal.ofReal_mul (mul_nonneg hvol hk.le)]
            apply ENNReal.ofReal_le_ofReal
            rw [hmain]
            have hc : 0 ≤ (B.I.muA B.μf B.fund).toReal * M * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j) :=
              mul_nonneg (mul_nonneg hvol hM) (by linarith)
            calc (B.I.muA B.μf B.fund).toReal * GlobalTheory.FlagMeas.kapBd B.I.E p q j *
                  (M * 2 * ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo)))
                = (B.I.muA B.μf B.fund).toReal * M * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
                    ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo)) := by ring
              _ ≤ (B.I.muA B.μf B.fund).toReal * M * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
                    (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a :=
                  mul_le_mul_of_nonneg_left hPQ hc
              _ = _ := by ring

end GlobalTheory.NearType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OfClassification
section
namespace GlobalTheory.DiscreteSeriesConsequences

theorem of_classification : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Dec.LowKMultOne ∧ GlobalTheory.Dec.DSInfChar ∧
    GlobalTheory.Dec.DSExists ∧ GlobalTheory.Dec.DSUnique ∧ GlobalTheory.Published.DiscreteSeriesUpqExists := by
  intro h
  obtain ⟨hE, -, hU, hI, hM, -, -⟩ :=
    GlobalTheory.ClassificationConsequences.consequences_of_dsClass (GlobalTheory.Published.discreteSeriesClassification_iff.1 h)
  exact ⟨hM, hI, hE, hU, GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hE⟩

end GlobalTheory.DiscreteSeriesConsequences
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeBetweenFrameAndComplementPartsStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitLattice_between_frameAndComplementParts : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∃ N : ℕ, 0 < N ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')) := by
  first | exact @GlobalTheory.FrameProj.lattice_between_parts | exact GlobalTheory.FrameProj.lattice_between_parts | (intros; apply GlobalTheory.FrameProj.lattice_between_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalHyperbolicFrameAnisotropicMemSpanTransStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_hyperbolicFrame_anisotropic_mem_span_transported : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) → (VS D).hT (X.zu u) y = 0 → ∃ d : Fin (D.R.N 0) → D.host.E, Fintype.linearCombination D.host.E (qFr wt) d = y := by
  first | exact @GlobalTheory.St.orth_mem_span_qFr | exact GlobalTheory.St.orth_mem_span_qFr | (intros; apply GlobalTheory.St.orth_mem_span_qFr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsScalarInUnipotentRadicalDoubleCosetStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_isScalar_in_unipotentRadical_doubleCoset : ∀ (D : D7) {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (VS D) D.R.rS T) (F' F'' : LFlag (VS D) D.R.rS T'), Submodule.IsLattice D.host.E Λ → F.zt = F.fl.z → F'.zt = F'.fl.z → F''.zt = F''.fl.z → ∀ n ∈ NRat F, ∀ m ∈ NRat F', (∀ a, frame F'' a = (n * m) (frame F' a)) → IsScalar Λ F F' F'' (n * m) := by
  first | exact @GlobalTheory.SnFam.CvScal.pair_scalar | exact GlobalTheory.SnFam.CvScal.pair_scalar | (intros; apply GlobalTheory.SnFam.CvScal.pair_scalar <;> assumption)
end

