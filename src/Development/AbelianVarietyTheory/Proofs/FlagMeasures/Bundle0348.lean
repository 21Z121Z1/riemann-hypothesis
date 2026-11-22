import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0341
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0274
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0340
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0277
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearIsometryCompactUnitaryTypeWeylMo
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0018
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelSchurOfFormalDegreeDensity
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FdegDens

theorem volUn_pos (j : ℕ) : 0 < volUn j := by
  unfold volUn
  refine Finset.prod_pos fun i _ => ?_
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  exact div_pos (pow_pos h2π _) (by exact_mod_cast Nat.factorial_pos i)

theorem exists_sort {n : ℕ} (ε : Fin n → Bool) : ∃ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin n), p + q = n ∧
    (∀ i, ε (e (Sum.inl i)) = true) ∧ ∀ j, ε (e (Sum.inr j)) = false := by
  classical
  let A := {i : Fin n // ε i = true}
  let B := {i : Fin n // ¬ε i = true}
  let e : Fin (Fintype.card A) ⊕ Fin (Fintype.card B) ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivFin A).symm (Fintype.equivFin B).symm).trans
      (Equiv.sumCompl fun i => ε i = true)
  refine ⟨Fintype.card A, Fintype.card B, e, ?_, fun i => ?_, fun j => ?_⟩
  · simpa using Fintype.card_congr e
  · exact ((Fintype.equivFin A).symm i).2
  · show ε (((Fintype.equivFin B).symm j : B) : Fin n) = false
    simpa using ((Fintype.equivFin B).symm j).2

theorem measurable_reindex {n p q : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n) :
    Measurable fun g : Formalism.BasicNotions.UpqT p q =>
      (Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) : PI.MtM n) := by
  haveI : BorelSpace (Formalism.BasicNotions.UpqT p q) := ⟨rfl⟩
  have hmat : Continuous (Formalism.BasicNotions.UpqT.mat : Formalism.BasicNotions.UpqT p q → _) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous fun g : Formalism.BasicNotions.UpqT p q =>
      (Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) : PI.MtM n) :=
    hmat.matrix_reindex e e
  exact hc.measurable

theorem reindex_mem {n p q : ℕ} (ε : Fin n → Bool) (e : Fin p ⊕ Fin q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) (g : Formalism.BasicNotions.UpqT p q) :
    Formalism.REAL.inUJ ε (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) := by
  obtain ⟨g0, hg0⟩ := g
  have hg : ((g0 : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * Formalism.UG.Jpq p q *
      (g0 : GL (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hg0
  show (Matrix.reindex e e ((g0 : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))ᴴ *
      Formalism.REAL.Jm ε * Matrix.reindex e e (g0 : GL (Fin p ⊕ Fin q) ℂ) = Formalism.REAL.Jm ε
  rw [GlobalTheory.OmegaFrobenius.jm_eq h1 h2, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]

theorem hasDens_unique {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (Fin m → Fin m → ℂ)} {c c' : ℝ≥0∞}
    (h : HasDens S μ c) (h' : HasDens S μ c') : c = c' := by
  unfold HasDens at h h'
  exact tendsto_nhds_unique h h'

theorem hasDens_smul {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (Fin m → Fin m → ℂ)} {c : ℝ≥0∞}
    (h : HasDens S μ c) (t : NNReal) : HasDens S (t • μ) (t * c) := by
  unfold HasDens at h ⊢
  refine (ENNReal.Tendsto.const_mul h (Or.inr ENNReal.coe_ne_top) (a := (t : ℝ≥0∞))).congr fun ρ => ?_
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc]

theorem cd_dens {n p q : ℕ} (ε : Fin n → Bool) (e : Fin p ⊕ Fin q ≃ Fin n) (hpq : p + q = n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) (cd : Formalism.BasicNotions.CDHaar) :
    PI.IsHaarOnM (UH (Formalism.REAL.Jm ε))
      ((cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) ∧
    HasDens (UH (Formalism.REAL.Jm ε))
      ((cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)))
      (ENNReal.ofReal (volUn n)⁻¹) := by
  subst hpq
  obtain ⟨c0, -, -, hc1, hc2⟩ := cd.trick p q
  have hK := GlobalTheory.T.hasDensityAtIdentityLieAlgebra_of_omegaDensity (p + q) (fun _ => true) (p + q) 0 (Equiv.sumEmpty _ _) (fun _ => rfl)
    (fun j => j.elim0) (cd.cd (p + q) 0) c0 (cd.haar _ _) hc2
  have hJ : Formalism.REAL.Jm (fun _ : Fin (p + q) => true) = 1 := by
    unfold Formalism.REAL.Jm
    simp
  rw [hJ] at hK
  have hprob : ((cd.cd (p + q) 0).map fun g => Matrix.of.symm (Matrix.reindex
      (Equiv.sumEmpty (Fin (p + q)) (Fin 0)) (Equiv.sumEmpty (Fin (p + q)) (Fin 0))
      (Formalism.BasicNotions.UpqT.mat g))) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_reindex _) MeasurableSet.univ, Set.preimage_univ]
    haveI := cd.prob (p + q)
    exact measure_univ
  have hc0 : c0 = ENNReal.ofReal (volUn (p + q))⁻¹ :=
    hasDens_unique hK.2 (GlobalTheory.T.hasDensityAtIdentity_unitaryGroup_probability (p + q) _ hK.1 hprob)
  have hM := GlobalTheory.T.hasDensityAtIdentityLieAlgebra_of_omegaDensity (p + q) ε p q e h1 h2 (cd.cd p q) c0 (cd.haar p q) hc1
  rw [hc0] at hM
  exact hM

theorem umat_emb {n : ℕ} (ε : Fin n → Bool) :
    MeasurableEmbedding fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM n) := by
  have h : Topology.IsClosedEmbedding (fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM n)) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  exact h.measurableEmbedding

theorem conj_emb {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    MeasurableEmbedding fun x : PI.MtM n => (Matrix.of.symm (P⁻¹ * Matrix.of x * P) : PI.MtM n) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hm : ∀ A B : Matrix (Fin n) (Fin n) ℂ,
      Measurable fun x : PI.MtM n => (Matrix.of.symm (A * Matrix.of x * B) : PI.MtM n) := by
    intro A B
    have hx : Continuous fun x : PI.MtM n => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ) := continuous_id
    have hc : Continuous fun x : PI.MtM n => (Matrix.of.symm (A * Matrix.of x * B) : PI.MtM n) :=
      (continuous_const.matrix_mul hx).matrix_mul continuous_const
    exact hc.measurable
  let φ : PI.MtM n ≃ PI.MtM n :=
    { toFun := fun x => Matrix.of.symm (P⁻¹ * Matrix.of x * P)
      invFun := fun y => Matrix.of.symm (P * Matrix.of y * P⁻¹)
      left_inv := fun x => by
        show Matrix.of.symm (P * (P⁻¹ * Matrix.of x * P) * P⁻¹) = x
        simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, ← Matrix.mul_assoc P P⁻¹,
          Matrix.mul_nonsing_inv_cancel_left _ _ hu]
      right_inv := fun y => by
        show Matrix.of.symm (P⁻¹ * (P * Matrix.of y * P⁻¹) * P) = y
        simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hu] }
  exact (MeasurableEquiv.mk φ (hm _ _) (hm _ _)).measurableEmbedding

theorem schur_of_dens : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (cd : Formalism.BasicNotions.CDHaar) (sc : NNReal) (P : Mat k r) (d c : ℝ) (μG : Measure (Mt k r)), (∀ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin (2 * r + k + 1)), (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) → ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A → ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) A = cd.cd p q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}) → IsCayley k r ε P → IsFdeg ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P)) d → 0 < c → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → SchurH μG σ (d / (c * volUn (2 * r + k + 1))) := by
  intro k r H _ _ _ σ ε cd sc P d c μG hcomp hP hF hc hμG hdG
  obtain ⟨p, q, e, hpq, h1, h2⟩ := exists_sort ε
  have hU := umat_emb ε
  have hC := conj_emb P hP.1

  have hν : ((sc : ℝ≥0∞) • Formalism.REAL.muG ε).map (fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM (2 * r + k + 1))) =
      (cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) := by
    ext B hB
    rw [Measure.map_apply hU.measurable hB, Measure.map_apply (measurable_reindex e) hB,
      hcomp p q e h1 h2 _ (hU.measurable hB)]
    congr 1
    ext g
    constructor
    · rintro ⟨a, ha, hag⟩
      show Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) ∈ B
      rw [← hag]
      exact ha
    · intro hg
      have hmem : Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g) ∈ Set.range
          (fun a : Formalism.REAL.UJ ε => ((a : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
            Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := by
        rw [(Formalism.REAL.isClosedEmbeddingMatrix _ ε).2]
        exact reindex_mem ε e h1 h2 g
      obtain ⟨a, ha⟩ := hmem
      refine ⟨a, ?_, ha⟩
      show Matrix.of.symm (umat a) ∈ B
      rw [show umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g) from ha]
      exact hg
  have hcd := cd_dens ε e hpq h1 h2 cd
  rw [← hν] at hcd
  have hHk := Formalism.QuantumDeterminants.hpkFacts k r
  have hD := GlobalTheory.T.haar_density_conj_unitaryHermitianGroups (2 * r + k + 1) (Formalism.QuantumDeterminants.Hpk k r) (Formalism.REAL.Jm ε) P hHk.1 hHk.2.1
    (Formalism.REAL.Jm_conjTranspose ε) (Formalism.REAL.Jm_mul_self ε) hP.1 hP.2 _ _ hcd.1 hcd.2
  obtain ⟨t, -, httop, hμt⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ _
    (GlobalTheory.AdDens.isMatGroup_UH _ hHk.2.1) hD.1).1 μG hμG
  have hdt : HasDens (GG k r) μG (t * ENNReal.ofReal (volUn (2 * r + k + 1))⁻¹) := by
    have h := hasDens_smul hD.2 t.toNNReal
    rwa [ENNReal.smul_def, ENNReal.coe_toNNReal httop.ne, ← hμt] at h
  have hV := volUn_pos (2 * r + k + 1)
  have htr : t.toReal = c * volUn (2 * r + k + 1) := by
    have h := congrArg ENNReal.toReal (hasDens_unique hdG hdt)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal (inv_nonneg.mpr hV.le)] at h
    rw [h, mul_assoc, inv_mul_cancel₀ hV.ne', mul_one]
  rw [Measure.map_map hC.measurable hU.measurable] at hμt
  have hemb := hC.comp hU
  obtain ⟨hd, hFd⟩ := hF
  refine ⟨div_pos hd (mul_pos hc hV), fun v w v' w' => ?_⟩
  obtain ⟨hI, hE⟩ := hFd v w v' w'
  rw [hμt]
  refine ⟨Integrable.smul_measure ?_ httop.ne, ?_⟩
  · rw [hemb.integrable_map_iff]
    exact hI
  rw [integral_smul_measure, hemb.integral_map]
  refine (congrArg (fun z : ℂ => t.toReal • z) hE).trans ?_
  rw [htr, Complex.real_smul]
  push_cast
  rw [div_div_eq_mul_div]
  ring

end GlobalTheory.FdegDens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassificationOfSpecialUnitary
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.SUtoU

variable {n : ℕ}

theorem equivOn_of_ext (hn : 1 ≤ n) (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (m : ℤ)
    {σ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (h : Ext ε m σ π) (h' : Ext ε m σ' π') (hT : EquivOn (SUset ε) σ σ') : EquivOn (UJset ε) π π' := by
  obtain ⟨T, hT⟩ := hT
  refine ⟨T, fun g hg v => ?_⟩
  obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := (GlobalTheory.T.unitary_to_special_unitary_local n hn ε).1 g hg
  rw [h z hz g₀ hg₀, h' z hz g₀ hg₀, _root_.smul_apply, _root_.smul_apply,
    LinearIsometryEquiv.map_smul, hT g₀ hg₀ v]

def meanFree (lam : Fin n → ℝ) : Fin n → ℝ := fun a => lam a - (∑ b, lam b) / n

def ExtProp (ε : Fin n → Bool) (F : Fam n) (lam : Fin n → ℝ)
    (π : Matrix (Fin n) (Fin n) ℂ → (F.H (meanFree lam) →L[ℂ] F.H (meanFree lam))) : Prop :=
  ∃ m : ℤ, ∑ a, lam a = (m : ℝ) ∧ Ext ε m (F.π (meanFree lam)) π ∧ IsHCU ε lam π

def famU (ε : Fin n → Bool) (F : Fam n) : Fam n where
  H lam := F.H (meanFree lam)
  nacg _ := inferInstance
  ips _ := inferInstance
  π lam := Classical.epsilon (ExtProp ε F lam)

theorem parS_meanFree (hn : 1 ≤ n) {lam : Fin n → ℝ} (hlam : IsParU lam) : IsParS (meanFree lam) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [meanFree, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hn0, sub_self]
  · intro a b h
    exact hlam.1 (by simpa [meanFree] using h)
  · intro a b
    obtain ⟨p, hp⟩ := hlam.2 a
    obtain ⟨q, hq⟩ := hlam.2 b
    exact ⟨p - q, by simp only [meanFree]; push_cast; linarith⟩

theorem exists_ext (hn : 1 ≤ n) (ε : Fin n → Bool) (F : Fam n) (hF : ParamS ε F) (lam : Fin n → ℝ)
    (hlam : IsParU lam) : ∃ π, ExtProp ε F lam π := by
  obtain ⟨m, hsum, -, hext⟩ := GlobalTheory.T.harish_chandra_parameter_descent n hn ε (F.H (meanFree lam)) (F.π (meanFree lam)) lam hlam
  have hμ : meanFree lam = fun a => lam a - (m : ℝ) / n := by funext a; simp [meanFree, hsum]
  have key : ∀ ν, ν = meanFree lam → IsHCS ε ν (F.π (meanFree lam)) := by
    rintro ν rfl; exact hF.1 _ (parS_meanFree hn hlam)
  obtain ⟨π, hπ1, hπ2⟩ := hext (key _ hμ.symm)
  exact ⟨π, m, hsum, hπ1, hπ2⟩

theorem famU_spec (hn : 1 ≤ n) (ε : Fin n → Bool) (F : Fam n) (hF : ParamS ε F) (lam : Fin n → ℝ)
    (hlam : IsParU lam) : ExtProp ε F lam ((famU ε F).π lam) :=
  Classical.epsilon_spec (exists_ext hn ε F hF lam hlam)

theorem classF_of_classS : ∀ (n : ℕ), 1 ≤ n → ∀ ε : Fin n → Bool, ClassS ε → ClassF ε := by
  intro n hn ε hS
  obtain ⟨F, hP, hE⟩ := hS
  refine ⟨famU ε F, fun lam hlam => ?_, ?_, ?_⟩
  · obtain ⟨-, -, -, h⟩ := famU_spec hn ε F hP lam hlam
    exact h
  · rintro lam lam' hlam ⟨w, hw, rfl⟩
    have hlam' : IsParU (lam ∘ w) := ⟨hlam.1.comp w.injective, fun a => hlam.2 (w a)⟩
    obtain ⟨m, hs, he, -⟩ := famU_spec hn ε F hP lam hlam
    obtain ⟨m', hs', he', -⟩ := famU_spec hn ε F hP _ hlam'
    have hsum : ∑ a, lam (w a) = ∑ a, lam a := Equiv.sum_comp w lam
    have hmm : m' = m := by exact_mod_cast (hs'.symm.trans ((show ∑ a, (lam ∘ w) a = ∑ a, lam a from hsum).trans hs))
    subst hmm
    refine equivOn_of_ext hn ε _ he he' ?_
    have hc : ConjK ε (meanFree lam) (meanFree (lam ∘ w)) := ⟨w, hw, by funext a; simp [meanFree, Function.comp_apply, hsum]⟩
    exact (hP.2 _ _ (parS_meanFree hn hlam) (parS_meanFree hn hlam')).2 hc
  · intro H' _ _ σ hσ
    obtain ⟨hc, hnt, hu, hirr, hsq⟩ := hσ
    obtain ⟨m, hm⟩ := GlobalTheory.CentralChar.central_char n hn ε H' σ hc hnt hu hirr
    obtain ⟨huS, hirrS, -, -⟩ := GlobalTheory.T.extension_preserves_properties n hn ε H' m σ σ hm
    have hsqS := (GlobalTheory.T.square_integrable_iff_extension n hn ε H' m σ σ hm hu).1 hsq
    obtain ⟨lam', hpar', T, hT⟩ := hE H' σ ⟨hc, hnt, huS hu, hirrS.1 hirr, hsqS⟩
    let ρ : Matrix (Fin n) (Fin n) ℂ → (F.H lam' →L[ℂ] F.H lam') := fun g =>
      (T.toContinuousLinearEquiv : H' →L[ℂ] F.H lam').comp
        ((σ g).comp (T.symm.toContinuousLinearEquiv : F.H lam' →L[ℂ] H'))
    have hρ : Ext ε m (F.π lam') ρ := by
      intro z hz g hg
      ext v
      have h1 : ρ (z • g) v = T (σ (z • g) (T.symm v)) := rfl
      rw [h1, hm z hz g hg, _root_.smul_apply, _root_.smul_apply,
        LinearIsometryEquiv.map_smul, hT g hg, LinearIsometryEquiv.apply_symm_apply]
    obtain ⟨S, hS, -⟩ := (hP.1 lam' hpar').2.2.1
    obtain ⟨hparU, hsumU⟩ := GlobalTheory.T.lowest_type_parameter_ascent n hn ε (F.H lam') m (F.π lam') ρ hρ lam' hpar' ⟨S, hS⟩
    refine ⟨fun a => lam' a + (m : ℝ) / n, hparU, ?_⟩
    obtain ⟨m₁, hs₁, he₁, -⟩ := famU_spec hn ε F hP _ hparU
    have hm₁ : m₁ = m := by exact_mod_cast hs₁.symm.trans hsumU
    subst hm₁
    have hμ : meanFree (fun a => lam' a + (m₁ : ℝ) / n) = lam' := by
      funext a; simp only [meanFree]; rw [hsumU]; ring
    have key : ∀ ν, ν = lam' → EquivOn (SUset ε) σ (F.π ν) := by rintro ν rfl; exact ⟨T, hT⟩
    exact equivOn_of_ext hn ε _ hm he₁ (key _ hμ)

end GlobalTheory.SUtoU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof : GlobalTheory.TypeAsm.FibC := by
  first | exact @GlobalTheory.TypeAsm.FibProof.fibC | exact GlobalTheory.TypeAsm.FibProof.fibC | (intros; apply GlobalTheory.TypeAsm.FibProof.fibC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryGroupModelsEquiv
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AdelicModels

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (HA HR HFinIn AF Ainf IsCMExt IsHermND)
open Formalism.MainNotions.StandardLattice (finMat infMat IsInfEmb)
open GlobalTheory.Mem.Vol.Scale
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_real_equiv (I : AutInst) (hcm : IsCMExt I.F I.E I.cm.sig)
    (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)) (hθ : ∀ v, IsInfEmb (I.φ v) (θ v)) :
    ∃ e : HA (Ainf I.F) I.cm.sig I.J ≃ₜ* I.Ginf, ∀ h v, uMat (e h v) =
      (I.P v)⁻¹ * ((HA.mat (Ainf I.F) I.cm.sig I.J h : GL (Fin I.n) (Ainf I.F ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Ainf I.F ⊗[I.F] I.E)).map (θ v) * I.P v := by
  obtain ⟨e, he, hc, hc', hs⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv I.F I.E I.cm.sig _ I.φ θ hcm
    (GlobalTheory.GaussDecay.isCMFam_of_over _ hcm I.φ I.φ_over) hθ
  choose p q s hsort using fun v => exists_sorts (I.ε v)
  have hd : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h1 : ∀ v, (I.P v)⁻¹ * I.P v = 1 := fun v => Matrix.nonsing_inv_mul _ (hd v)
  have h2 : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v => Matrix.mul_nonsing_inv _ (hd v)
  have hJ : ∀ v, Formalism.UG.Jpq (p v) (q v) = (Formalism.REAL.Jm (I.ε v)).submatrix (s v) (s v) := fun v => by
    rw [← (hsort v).reindex_Jpq]
    ext a b
    simp
  obtain ⟨f, hf⟩ := GlobalTheory.Mem.InfGroup.exists_equiv he hc hc' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf I.F) I.cm.sig)
    (fun x i => by rw [← he, ← he, hs]) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Ainf I.F) I.J) p q
    (fun v => (I.P v)⁻¹.submatrix (s v) (Equiv.refl _)) (fun v => (I.P v).submatrix (Equiv.refl _) (s v))
    (fun v => by rw [Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_one_equiv])
    (fun v => by rw [Matrix.submatrix_mul_equiv, h2, Matrix.submatrix_one_equiv])
    (fun v => by
      have h3 : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Ainf I.F) I.J).map (θ v) = I.J.map (I.φ v) := by
        ext a b
        exact (hθ v).1 (I.J a b)
      rw [h3, hJ, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
        ← I.P_spec v]
      change (I.P v)⁻¹ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹ = _
      calc _ = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [h2]; simp)
  let g : (∀ v, Formalism.BasicNotions.UpqT (p v) (q v)) ≃ₜ* I.Ginf :=
    { toFun := fun x v => (hsort v).equiv (x v)
      invFun := fun y v => (hsort v).equiv.symm (y v)
      left_inv := fun x => funext fun v => (hsort v).equiv.symm_apply_apply _
      right_inv := fun x => funext fun v => (hsort v).equiv.apply_symm_apply _
      map_mul' := fun x y => funext fun v => map_mul (hsort v).equiv _ _
      continuous_toFun := continuous_pi fun v => (hsort v).equiv.continuous.comp (continuous_apply v)
      continuous_invFun := continuous_pi fun v => (hsort v).equiv.symm.continuous.comp (continuous_apply v) }
  refine ⟨f.trans g, fun h v => ?_⟩
  have h4 := hf h v
  change Matrix.reindex (s v) (s v) (Formalism.BasicNotions.UpqT.mat (f h v)) = (I.P v)⁻¹ * (h.1.1).map (θ v) * I.P v
  generalize Formalism.BasicNotions.UpqT.mat (f h v) = X at h4 ⊢
  generalize (h.1.1).map (θ v) = Y at h4 ⊢
  have h5 : Matrix.reindex (s v) (s v) X * (I.P v)⁻¹ = (I.P v)⁻¹ * Y := by
    ext a b
    have := congrFun (congrFun h4 ((s v).symm a)) b
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.coe_refl, id] at this
    rw [Matrix.mul_apply, Matrix.mul_apply, ← this, ← (s v).sum_comp]
    simp
  rw [← h5, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem bc_mem {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {γ : GL (Fin M) E}
    (hγ : γ ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R) γ ∈ HR R σ J := by
  have h : Formalism.UG.cT (σ : E →+* E) γ.1 * J * γ.1 = J := hγ
  have h2 := congrArg (fun X => Matrix.map X (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) h
  simp only [Matrix.map_mul] at h2
  change Formalism.UG.cT _ (γ.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) * J.map _ * γ.1.map _ = J.map _
  rw [← h2]
  congr 2

theorem exists_adelic_equiv : ∀ I : AutInst, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt I.F I.E I.cm.sig ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND I.cm.sig I.J ∧ ∃ T : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ≃ₜ* I.GA, (∀ h, (show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J from h) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ↔ T h ∈ I.GFset) ∧ (∀ h, I.fmat (T h).2 = (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _)) ∧ ∀ v θ, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ → ∀ h, uMat ((T h).1 v) = (I.P v)⁻¹ * Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θ h * I.P v := by
  intro I
  have hcm : IsCMExt I.F I.E I.cm.sig := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1
  refine ⟨hcm, ⟨fun i j => congrFun (congrFun I.J_herm i) j, I.J_det⟩, ?_⟩
  have hex := GlobalTheory.Mem.VolEmb.existsUnique_infEmb I.F I.E I.cm.sig hcm
  choose θ hθ hθu using fun v => hex (I.φ v)
  obtain ⟨er, her⟩ := exists_real_equiv I hcm θ hθ
  obtain ⟨ef, hef, -⟩ := GlobalTheory.T.exists_continuousMulEquiv_congruenceTopology_adelicUnitary I
  obtain ⟨sp, hsp⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split I.F I.E I.cm.sig I.n I.J
  let g : HA (Ainf I.F) I.cm.sig I.J × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af I.F) I.cm.sig I.J ≃ₜ* I.GA :=
    { toFun := fun x => (er x.1, ef.symm x.2)
      invFun := fun y => (er.symm y.1, ef y.2)
      left_inv := fun x => Prod.ext (er.symm_apply_apply _) (ef.apply_symm_apply _)
      right_inv := fun x => Prod.ext (er.apply_symm_apply _) (ef.symm_apply_apply _)
      map_mul' := fun x y => Prod.ext (map_mul er _ _) (map_mul ef.symm _ _)
      continuous_toFun := (er.continuous.comp continuous_fst).prodMk (ef.symm.continuous.comp continuous_snd)
      continuous_invFun := (er.symm.continuous.comp continuous_fst).prodMk (ef.continuous.comp continuous_snd) }
  have hfin : ∀ h, I.fmat ((sp.trans g) h).2 =
      (finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _) := by
    intro h
    have h1 := hef (ef.symm (sp h).2)
    rw [ef.apply_symm_apply, (hsp h).1] at h1
    rw [h1]
    change I.fmat (ef.symm (sp h).2) = _
    ext a b
    exact ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm_apply_apply _).symm
  have hinf : ∀ v h, uMat (((sp.trans g) h).1 v) = (I.P v)⁻¹ * infMat I.cm.sig I.J (θ v) h * I.P v := by
    intro v h
    have h1 := her (sp h).1 v
    rw [(hsp h).2] at h1
    exact h1
  have hrat : ∀ (γ : GL (Fin I.n) I.E) (h : HA (AF I.F) I.cm.sig I.J),
      Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := I.F) (AF I.F)) γ = HA.mat _ _ _ h →
      (∀ v, uMat (((sp.trans g) h).1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat ((sp.trans g) h).2 =
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    intro γ h hh
    refine ⟨fun v => ?_, ?_⟩
    · rw [hinf]
      congr 2
      unfold infMat
      rw [← hh]
      ext a b
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, ← (hθ v).1]
      change θ v (Algebra.TensorProduct.map _ _ ((1 : AF I.F) ⊗ₜ[I.F] γ.1 a b)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
    · rw [hfin]
      unfold finMat
      rw [← hh]
      ext a b
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
      change Algebra.TensorProduct.comm I.F _ _
        (Algebra.TensorProduct.map _ _ ((1 : AF I.F) ⊗ₜ[I.F] γ.1 a b)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
  refine ⟨sp.trans g, fun h => ⟨?_, ?_⟩, hfin, fun v θ' hθ' h => ?_⟩
  · rintro ⟨γ, hγ, hh⟩
    exact ⟨γ, hγ, hrat γ h hh⟩
  · rintro ⟨γ, hγ, h1, h2⟩
    let h' : HA (AF I.F) I.cm.sig I.J :=
      (⟨_, bc_mem (AF I.F) I.cm.sig I.J hγ⟩ : HR (AF I.F) I.cm.sig I.J)
    obtain ⟨h3, h4⟩ := hrat γ h' rfl
    have : h = h' := (sp.trans g).injective (Prod.ext
      (funext fun v => Subtype.ext (Units.ext ((h1 v).trans (h3 v).symm)))
      (Subtype.ext (Units.ext (h2.trans h4.symm))))
    rw [this]
    exact ⟨γ, hγ, rfl⟩
  · rw [hθu v θ' hθ']
    exact hinf v h

end GlobalTheory.AdelicModels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearIsometryCompactUnitaryTypeWeylMoStatement
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjLinear_isometry_compact_unitary_type_weyl_module : ∀ (k n : ℕ) (h : k = n) (lam : DomWeight n) (u : Fin k → ℝ), (∀ i : Fin k, u i = (lam.w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)), IsHCTypeU k u π → ∃ j : W →ₗ⋆[ℂ] MvPolynomial (Fin n × Fin n) ℂ, (∀ ξ, j ξ ∈ delSq ℂ n lam) ∧ (∀ p ∈ delSq ℂ n lam, ∃ ξ, j ξ = p) ∧ (∀ ξ η, normFock lam (j η) (j ξ) = ⟪η, ξ⟫_ℂ) ∧ ∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ ξ, j (π (g.submatrix (Fin.cast h) (Fin.cast h)) ξ) = (g.det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := by
  first | exact @GlobalTheory.WeylConjType.exists_conj_weyl | exact GlobalTheory.WeylConjType.exists_conj_weyl | (intros; apply GlobalTheory.WeylConjType.exists_conj_weyl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowLevelWithAnalyticFactsOfStepsStatement
section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsRowLevelWithAnalyticFacts_of_steps : TieOfCtx → StepChoiceConstantsC → StepAnalyticP → StepAnalyticConstantsP := by
  first | exact @GlobalTheory.NGRow.exists_row_level_analytic | exact GlobalTheory.NGRow.exists_row_level_analytic | (intros; apply GlobalTheory.NGRow.exists_row_level_analytic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreFamilyUnique
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreUnique

theorem fibre_family_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ fib' : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib' → fib = fib' := by
  intro F E _ _ _ _ _ σ hE n J hJ v a μ ν hμ hν fib h1 fib' h2
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hE.2.2.2
  have := PI.VolStabS.secondCountable_Fv F v
  have := PI.VolStabS.locallyCompact_Fv F v
  exact PI.VolStabS.FibUniq.fib_eq_tens σ hσ J hJ.1 a (Fv F v) (PI.VolStabS.isOpen_units_Fv F v)
    (PI.VolStabS.TensAllW.lip_field _) μ ν fib fib' h1 h2

end GlobalTheory.LocalFibreUnique
end

