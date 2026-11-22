import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0002
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.BridgeA
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasUpq
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitEmbeddingIntegralAndMaximalIdeal
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem GlobalTheory.adicEmbedding_integral_place (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F) :
    (∀ a : 𝓞 E, Valued.v (τ a) ≤ 1) ∧ ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ ∀ a : 𝓞 E, a ∈ Q ↔ Valued.v (τ a) < 1 := by
  set O := v.adicCompletionIntegers F
  have hv : (Valued.v : Valuation (v.adicCompletion F) _).Integers O := by
    have := Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)
    exact this
  have ha : ∀ a : 𝓞 E, Valued.v (τ a) ≤ 1 := by
    intro a
    have h1 : IsIntegral ℤ (τ a) := IsIntegral.map τ (NumberField.RingOfIntegers.isIntegral_coe a)
    have h2 : IsIntegral O (τ a) := h1.tower_top
    exact hv.mem_of_integral h2
  refine ⟨ha, ?_⟩
  let φ : 𝓞 E →+* O :=
    ((τ : E →+* v.adicCompletion F).comp (algebraMap (𝓞 E) E)).codRestrict O.toSubring
      (fun a => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 (ha a))
  have hmem : ∀ a : 𝓞 E, a ∈ (IsLocalRing.maximalIdeal O).comap φ ↔ Valued.v (τ a) < 1 := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]
    change ¬ Valued.v (τ a) = 1 ↔ _
    exact ⟨fun h => lt_of_le_of_ne (ha a) h, fun h => ne_of_lt h⟩
  refine ⟨(IsLocalRing.maximalIdeal O).comap φ, ?_, hmem⟩
  apply Ideal.IsPrime.isMaximal inferInstance
  intro hbot
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hlt : Valued.v (algebraMap F (v.adicCompletion F) (π : F)) < 1 := by
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v π).2 hπ
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at this
    exact this
  have hne : (algebraMap (𝓞 F) (𝓞 E) π) ≠ 0 := by
    intro h
    apply hπ0
    apply FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
    simpa using h
  apply hne
  have : algebraMap (𝓞 F) (𝓞 E) π ∈ (IsLocalRing.maximalIdeal O).comap φ := by
    rw [hmem]
    have e : ((algebraMap (𝓞 F) (𝓞 E) π : 𝓞 E) : E) = algebraMap F E (π : F) := by
      exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E π).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F E π)
    rw [e, AlgHom.commutes]
    exact hlt
  rw [hbot] at this
  simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableRangeOneDetUnitElementary
section
open NumberField IsDedekindDomain GlobalTheory.HaarLin

namespace GlobalTheory.HaarLin.Gauss

open Matrix

variable {R : Type} [CommRing R]

theorem transvection_mem {κ : Type} [Fintype κ] [DecidableEq κ] {i j : κ} (h : i ≠ j) (c : R) :
    transvection i j c ∈ TD R κ :=
  Submonoid.subset_closure (Or.inl ⟨i, j, c, h, rfl⟩)

theorem diagonal_mem {κ : Type} [Fintype κ] [DecidableEq κ] (d : κ → Rˣ) :
    (diagonal fun i => (d i : R)) ∈ TD R κ :=
  Submonoid.subset_closure (Or.inr ⟨d, rfl⟩)

theorem exists_inv {κ : Type} [Fintype κ] [DecidableEq κ] {A : Matrix κ κ R} (hA : A ∈ TD R κ) :
    ∃ B ∈ TD R κ, B * A = 1 ∧ A * B = 1 := by
  induction hA using Submonoid.closure_induction with
  | mem N hN =>
    rcases hN with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · refine ⟨transvection i j (-c), transvection_mem hij _, ?_, ?_⟩ <;>
        simp [transvection_mul_transvection_same _ _ hij]
    · refine ⟨_, diagonal_mem (fun i => (d i)⁻¹), ?_, ?_⟩ <;>
        simp [diagonal_mul_diagonal]
  | one => exact ⟨1, one_mem _, by simp, by simp⟩
  | mul A B _ _ IA IB =>
    obtain ⟨A', hA', h1, h2⟩ := IA
    obtain ⟨B', hB', h3, h4⟩ := IB
    refine ⟨B' * A', mul_mem hB' hA', ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc A', h1, one_mul, h3]
    · rw [mul_assoc, ← mul_assoc B, h4, one_mul, h2]

theorem of_left {κ : Type} [Fintype κ] [DecidableEq κ] {E M : Matrix κ κ R} (hE : E ∈ TD R κ)
    (hM : IsUnit M.det) (h : IsUnit (E * M).det → E * M ∈ TD R κ) : M ∈ TD R κ := by
  obtain ⟨B, hB, h1, h2⟩ := exists_inv hE
  have hd : IsUnit E.det := IsUnit.of_mul_eq_one B.det (by rw [← det_mul, h2, det_one])
  have := mul_mem hB (h (by rw [det_mul]; exact hd.mul hM))
  rwa [← mul_assoc, h1, one_mul] at this

theorem of_right {κ : Type} [Fintype κ] [DecidableEq κ] {E M : Matrix κ κ R} (hE : E ∈ TD R κ)
    (hM : IsUnit M.det) (h : IsUnit (M * E).det → M * E ∈ TD R κ) : M ∈ TD R κ := by
  obtain ⟨B, hB, h1, h2⟩ := exists_inv hE
  have hd : IsUnit E.det := IsUnit.of_mul_eq_one B.det (by rw [← det_mul, h2, det_one])
  have := mul_mem (h (by rw [det_mul]; exact hM.mul hd)) hB
  rwa [mul_assoc, h2, mul_one] at this

theorem rowOp {κ : Type} [Fintype κ] [DecidableEq κ] (p : κ) (w : κ → R) (s : Finset κ) (hs : p ∉ s) :
    ∃ E ∈ TD R κ, ∀ M : Matrix κ κ R, (∀ b, (E * M) p b = M p b + ∑ k ∈ s, w k * M k b) ∧
      ∀ a b, a ≠ p → (E * M) a b = M a b := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert k s hk IH =>
    have hkp : p ≠ k := fun h => hs (by simp [h])
    obtain ⟨E, hE, H⟩ := IH (fun h => hs (by simp [h]))
    refine ⟨transvection p k (w k) * E, mul_mem (transvection_mem hkp _) hE, fun M => ⟨fun b => ?_, fun a b ha => ?_⟩⟩
    · rw [mul_assoc, transvection_mul_apply_same, (H M).1, (H M).2 _ _ hkp.symm, Finset.sum_insert hk]
      ring
    · rw [mul_assoc, transvection_mul_apply_of_ne _ _ _ _ ha, (H M).2 _ _ ha]

theorem colOpLeft {κ : Type} [Fintype κ] [DecidableEq κ] (p : κ) (w : κ → R) (s : Finset κ) (hs : p ∉ s) :
    ∃ E ∈ TD R κ, ∀ (M : Matrix κ κ R) a b, (E * M) a b = M a b + if a ∈ s then w a * M p b else 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert k s hk IH =>
    have hkp : p ≠ k := fun h => hs (by simp [h])
    have hps : p ∉ s := fun h => hs (by simp [h])
    obtain ⟨E, hE, H⟩ := IH hps
    refine ⟨transvection k p (w k) * E, mul_mem (transvection_mem hkp.symm _) hE, fun M a b => ?_⟩
    by_cases ha : a = k
    · subst ha
      rw [mul_assoc, transvection_mul_apply_same, H, H]
      simp [hk, hps]
    · rw [mul_assoc, transvection_mul_apply_of_ne _ _ _ _ ha, H]
      simp [ha]

theorem colOpRight {κ : Type} [Fintype κ] [DecidableEq κ] (p : κ) (w : κ → R) (s : Finset κ) (hs : p ∉ s) :
    ∃ E ∈ TD R κ, ∀ (M : Matrix κ κ R) a b, (M * E) a b = M a b + if b ∈ s then w b * M a p else 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert k s hk IH =>
    have hkp : p ≠ k := fun h => hs (by simp [h])
    have hps : p ∉ s := fun h => hs (by simp [h])
    obtain ⟨E, hE, H⟩ := IH hps
    refine ⟨E * transvection p k (w k), mul_mem hE (transvection_mem hkp _), fun M a b => ?_⟩
    by_cases hb : b = k
    · subst hb
      rw [← mul_assoc, mul_transvection_apply_same, H, H]
      simp [hk, hps]
    · rw [← mul_assoc, mul_transvection_apply_of_ne _ _ _ _ hb, H]
      simp [hb]

theorem reindex_mem {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
    {A : Matrix κ κ R} (hA : A ∈ TD R κ) : A.submatrix e.symm e.symm ∈ TD R κ' := by
  induction hA using Submonoid.closure_induction with
  | mem N hN =>
    rcases hN with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · have : (transvection i j c).submatrix e.symm e.symm = transvection (e i) (e j) c := by
        ext a b
        simp [transvection, Matrix.one_apply, Matrix.single_apply, Equiv.eq_symm_apply]
      rw [this]
      exact transvection_mem (e.injective.ne hij) c
    · rw [submatrix_diagonal_equiv]
      exact diagonal_mem (fun i => d (e.symm i))
  | one => rw [submatrix_one_equiv]; exact one_mem _
  | mul A B _ _ IA IB =>
    rw [← submatrix_mul_equiv A B e.symm e.symm e.symm]
    exact mul_mem IA IB

theorem fromBlocks_mem {κ : Type} [Fintype κ] [DecidableEq κ]
    {A : Matrix κ κ R} (hA : A ∈ TD R κ) : fromBlocks A 0 0 (1 : Matrix Unit Unit R) ∈ TD R (κ ⊕ Unit) := by
  induction hA using Submonoid.closure_induction with
  | mem N hN =>
    rcases hN with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · have : transvection (Sum.inl i) (Sum.inl j) c = fromBlocks (transvection i j c) 0 0 (1 : Matrix Unit Unit R) :=
        TransvectionStruct.toMatrix_sumInl Unit (⟨i, j, hij, c⟩ : TransvectionStruct κ R)
      rw [← this]
      exact transvection_mem (Sum.inl_injective.ne hij) c
    · rw [← diagonal_one, fromBlocks_diagonal]
      convert diagonal_mem (R := R) (Sum.elim d (fun _ : Unit => 1)) using 2
      ext x
      cases x <;> rfl
  | one => rw [fromBlocks_one]; exact one_mem _
  | mul A B _ _ IA IB =>
    have := mul_mem IA IB
    rw [fromBlocks_multiply] at this
    simpa using this

theorem step {κ : Type} [Fintype κ] [DecidableEq κ] (hR : HasStableRangeOne R)
    (IH : ∀ N : Matrix κ κ R, IsUnit N.det → N ∈ TD R κ)
    (M : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R) (hM : IsUnit M.det) : M ∈ TD R (κ ⊕ Unit) := by
  set l : κ ⊕ Unit := Sum.inr () with hl
  set s : Finset (κ ⊕ Unit) := Finset.univ.erase l with hs
  have hls : l ∉ s := Finset.notMem_erase _ _
  have hin : ∀ i : κ, Sum.inl i ∈ s := fun i => by simp [hs, hl]
  have h1 : (M⁻¹ * M) l l = 1 := by rw [nonsing_inv_mul M hM, one_apply_eq]
  rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ l)] at h1
  obtain ⟨t, ht⟩ := hR (M l l) (∑ k ∈ s, M⁻¹ l k * M k l) ⟨M⁻¹ l l, 1, by rw [one_mul]; exact h1⟩
  obtain ⟨E₁, hE₁, H₁⟩ := rowOp l (fun k => t * M⁻¹ l k) s hls
  refine of_left hE₁ hM fun hM₁ => ?_
  have hu : IsUnit ((E₁ * M) l l) := by
    rw [(H₁ M).1]
    simpa [Finset.mul_sum, mul_assoc] using ht
  generalize E₁ * M = M₁ at hM₁ hu
  obtain ⟨u, hu⟩ := hu
  obtain ⟨E₂, hE₂, H₂⟩ := colOpLeft l (fun a => - M₁ a l * ↑u⁻¹) s hls
  refine of_left hE₂ hM₁ fun hM₂ => ?_
  have hu₂ : (E₂ * M₁) l l = u := by rw [H₂, if_neg hls, add_zero, hu]
  have hc₂ : ∀ i : κ, (E₂ * M₁) (Sum.inl i) l = 0 := fun i => by
    rw [H₂, if_pos (hin i), ← hu, mul_assoc, Units.inv_mul]; ring
  generalize E₂ * M₁ = M₂ at hM₂ hu₂ hc₂
  obtain ⟨E₃, hE₃, H₃⟩ := colOpRight l (fun b => - M₂ l b * ↑u⁻¹) s hls
  refine of_right hE₃ hM₂ fun hM₃ => ?_
  have hu₃ : (M₂ * E₃) l l = u := by rw [H₃, if_neg hls, add_zero, hu₂]
  have hc₃ : ∀ i : κ, (M₂ * E₃) (Sum.inl i) l = 0 := fun i => by
    rw [H₃, if_neg hls, add_zero, hc₂]
  have hr₃ : ∀ i : κ, (M₂ * E₃) l (Sum.inl i) = 0 := fun i => by
    rw [H₃, if_pos (hin i), hu₂, mul_assoc, Units.inv_mul]; ring
  generalize M₂ * E₃ = M₃ at hM₃ hu₃ hc₃ hr₃
  have hform : M₃ = (diagonal fun i => ((Sum.elim (fun _ => 1) (fun _ => u) : κ ⊕ Unit → Rˣ) i : R)) *
      fromBlocks M₃.toBlocks₁₁ 0 0 (1 : Matrix Unit Unit R) := by
    ext a b
    rw [diagonal_mul]
    rcases a with a | ⟨⟩ <;> rcases b with b | ⟨⟩
    · simp [toBlocks₁₁]
    · simpa using hc₃ a
    · simpa using hr₃ b
    · simpa using hu₃
  have hN : IsUnit M₃.toBlocks₁₁.det := by
    rw [hform, det_mul, det_fromBlocks_zero₂₁, det_one, mul_one] at hM₃
    exact isUnit_of_mul_isUnit_right hM₃
  rw [hform]
  exact mul_mem (diagonal_mem _) (fromBlocks_mem (IH _ hN))

theorem mem_TD_of_isUnit_det : ∀ (R : Type) [CommRing R], HasStableRangeOne R → ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ R), IsUnit M.det → M ∈ TD R κ := by
  intro R _ hR κ _ _
  have key : ∀ n : ℕ, ∀ N : Matrix (Fin n) (Fin n) R, IsUnit N.det → N ∈ TD R (Fin n) := by
    intro n
    induction n with
    | zero => intro N _; rw [Subsingleton.elim N 1]; exact one_mem _
    | succ n IH =>
      intro N hN
      let e : Fin n ⊕ Unit ≃ Fin (n + 1) := (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
      have := reindex_mem e (step hR IH (N.submatrix e e) (by rwa [det_submatrix_equiv_self]))
      simpa using this
  intro M hM
  let e := (Fintype.equivFin κ).symm
  have := reindex_mem e (key _ (M.submatrix e e) (by rwa [det_submatrix_equiv_self]))
  simpa using this

end GlobalTheory.HaarLin.Gauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardMeasureUnitaryPQEqVolumeSmulCompactDual
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.CompactDualScale

theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ENNReal} (a : ENNReal) (ha : a ≠ ⊤)
    (h : OmegaDensity μ c) : OmegaDensity (a • μ) (a * c) := by
  obtain ⟨lam, hlam, hl⟩ := h
  refine ⟨lam, hlam, ?_⟩
  refine (ENNReal.Tendsto.const_mul hl (Or.inr ha)).congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ENNReal}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c = c' := by
  obtain ⟨lam, hlam, hl⟩ := h
  obtain ⟨lam', hlam', hl'⟩ := h'
  rw [Formalism.IndefR.Eqv.MU.omegaLeb_unique hlam hlam'] at hl'
  exact tendsto_nhds_unique hl hl'

theorem isMinf_eq_volU_smul_cd : ∀ (cd : CDHaar) (p q : ℕ) (m : Measure (UpqT p q)), Lev.IsMinf m →
    m = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q := by
  intro cd p q m hm
  obtain ⟨c, hc0, hctop, hpq, hN⟩ := cd.trick p q
  haveI := cd.haar (p + q) 0
  haveI := cd.prob (p + q)
  haveI := cd.haar p q
  have hmain := ReciprocityTheory.ChartRestriction.DS.PolarCoordinateComparison.omegaDensity_main (N := p + q) (cd.cd (p + q) 0)
  have hc := omegaDensity_unique hN hmain
  have hV : 0 < ReciprocityTheory.ChartRestriction.DS.volU (p + q) := ReciprocityTheory.ChartRestriction.DS.PolarCoordinateComparison.volU_pos (p + q)
  have hκ : (0 : ℝ) < 2 ^ ((p + q) * (p + q - 1) / 2) := by positivity
  have hmul : ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) * c = Formalism.L2.Theta.minfDensity (p + q) := by
    rw [hc, ← ENNReal.ofReal_mul hV.le, Formalism.L2.Theta.minfDensity]
    have e : ReciprocityTheory.ChartRestriction.DS.volU (p + q) * (1 / (2 ^ ((p + q) * (p + q - 1) / 2) * ReciprocityTheory.ChartRestriction.DS.volU (p + q)))
        = ((2 : ℝ) ^ ((p + q) * (p + q - 1) / 2))⁻¹ := by
      field_simp
    rw [e, ENNReal.ofReal_inv_of_pos hκ, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hV0 : ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) ≠ 0 := (ENNReal.ofReal_pos.2 hV).ne'
  have hm' : Lev.IsMinf (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q) := by
    refine ⟨Measure.IsHaarMeasure.smul _ hV0 ENNReal.ofReal_ne_top, ?_⟩
    rw [← hmul]
    exact omegaDensity_smul _ ENNReal.ofReal_ne_top hpq
  exact Formalism.IndefR.Eqv.MU.isMinf_unique hm' hm

end GlobalTheory.LowRow.CompactDualScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.StdCharWeilDatum

section Char

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA (x : Ainf F) : At (evI F) (pairA F x 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
  rw [h1, zero_mul, mul_zero]

theorem psi_pairA {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : Ainf F) :
    ψ (pairA F x 0) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ)) :=
  hψ.2.2 _ (at_pairA x)

theorem norm_exp_real (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_psi_inf {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : Ainf F) : ‖ψ (pairA F x 0)‖ = 1 := by
  rw [psi_pairA hψ]; exact norm_exp_real _

theorem pairA_split (x : AF F) : x = pairA F x.1 0 + pairA F 0 x.2 := by
  show x = ((x.1 + 0 : Ainf F), (0 + x.2 : Af F))
  rw [add_zero, zero_add]
  rfl

theorem norm_psi_fin {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (y : Af F) : ‖ψ (pairA F 0 y)‖ = 1 := by
  have hc : Continuous fun y : Af F => ‖ψ (pairA F 0 y)‖ :=
    (hψ.1.comp (continuous_const.prodMk continuous_id)).norm
  have hcl : IsClosed {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := isClosed_eq hc continuous_const
  have hrange : Set.range (algebraMap F (Af F)) ⊆ {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_psi_inf hψ, one_mul, norm_one] at h2
    exact h2
  have := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at this
  exact this (Set.mem_univ y)

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]

theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)
  have hn : 0 < n := Module.finrank_pos
  set t : ℝ := 1 / (2 * n)
  refine ⟨pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) 0, ?_⟩
  rw [psi_pairA hψ, RingEquiv.apply_symm_apply, Algebra.trace_algebraMap]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have eR : (n • t : ℝ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    simp only [t]
    rw [mul_one_div, div_eq_div_iff (by positivity) two_ne_zero]
    ring
  have e : ((n • t : ℝ) : ℂ) = 1 / 2 := by
    rw [eR]; push_cast; ring
  rw [e]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem isCharAF {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : IsCharAF F ψ :=
  ⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩

end Char

section Trace

variable {F : Type} [Field F] [NumberField F]

theorem sum_eq_trace (x : Ainf F) :
    ∑ v : InfinitePlace F, (v.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding v (x v)).re =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [Algebra.trace_complex_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2,
      Complex.ofReal_re]
    simp
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_
    have h := InfinitePlace.mult_isComplex ⟨w.1, InfinitePlace.not_isReal_iff_isComplex.1 w.2⟩
    simp only at h
    rw [h]
    push_cast
    rfl

end Trace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sum_infFam [IsTotallyReal F] (B : Base F E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ))
    (hθ : Formalism.IndefR.DatumF.IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ) (x : Ainf F) :
    ∑ w, θ w (x ⊗ₜ[F] (1 : E)) =
      ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) := by
  rw [← sum_eq_trace]
  push_cast
  refine Fintype.sum_congr _ _ fun w => ?_
  have hv : w.IsReal := IsTotallyReal.isReal w
  rw [GlobalTheory.DualPairCompare.gen_inf_val (B.emb w).1 w (B.emb w).2.symm (θ w) (hθ w) x,
    InfinitePlace.mult_isReal ⟨_, hv⟩, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv,
    Complex.ofReal_re]
  simp

theorem isStdCharF_of_isGood : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsTotallyReal F := hB.cm.1
  refine ⟨isCharAF hB.std, ⟨?_, fun θ hθ x => ?_⟩⟩
  · choose θ hθ using fun w : InfinitePlace F =>
      GlobalTheory.DualPairCompare.gen_inf_exists (B.emb w).1 w (B.emb w).2.symm
    exact ⟨θ, hθ⟩
  · show B.ψ (pairA F x 0) = _
    rw [psi_pairA hB.std, sum_infFam B θ hθ x]
    congr 1
    push_cast
    ring

end GlobalTheory.StdCharWeilDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleFrameMembershipStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subbundle_frame_membership : ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (c : Fin N → Γ(F, U)), VB.IsFrame c → ∀ (S : ∀ x : X, Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) (l : ℕ), (∀ (y : X) (hy : y ∈ U), S y = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = F.presheaf.germ U y hy (c j)}) → ∀ {V : X.Opens} (h : V ≤ U) (a : Fin N → Γ(X, V)), (∑ j, a j • resM F h (c j)) ∈ (VB.Sub.ofStalks S).sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0 := by
  first | exact @GlobalTheory.VB.sum_smul_frame_mem_ofStalks_iff | exact GlobalTheory.VB.sum_smul_frame_mem_ofStalks_iff | (intros; apply GlobalTheory.VB.sum_smul_frame_mem_ofStalks_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TCAlt
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls

def TC (D : Type) [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (R : Type) [CommRing R] [Algebra ℚ R]
    (z : (R ⊗[ℚ] D)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] D) * ((1 : R) ⊗ₜ β) * (starT σ R (z.1 : R ⊗[ℚ] D)).unop =
      algebraMap R (R ⊗[ℚ] D) (z.2 : R) * ((1 : R) ⊗ₜ β) ∧
    Commute (z.1 : R ⊗[ℚ] D) ((1 : R) ⊗ₜ y)

end GlobalTheory.CentCls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TieInOfFwTie
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Div

theorem tieIn_of_fwTie : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), FWTie T R κ v₀ → TieIn T R κ v₀ :=
  fun _ _ _ _ _ t => ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩

end GlobalTheory.Div
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDomaStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → (∃ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure ∧ IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ ∧ IsCompact (closure 𝓕)) ∧ (∀ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure → IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤) ∧ ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ z ∈ ZI V ξ, ∃ γ ∈ ZI V ξ, γ ∈ GQ V ∧ ∃ u ∈ ZI V ξ, u ∈ GinfC V ∧ ∃ k ∈ ZI V ξ, k ∈ GfC V ∧ k ∈ U ∧ z = γ * u * k := by
  first | exact @GlobalTheory.TransvMeasure.transvection_measure | exact GlobalTheory.TransvMeasure.transvection_measure | (intros; apply GlobalTheory.TransvMeasure.transvection_measure <;> assumption)
end

