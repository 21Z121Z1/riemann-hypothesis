import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0008

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.DetScale

open Matrix
open scoped Pointwise

section Ring

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R]
  [BorelSpace R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem measurable_mulVec (A : Matrix ι ι R) :
    Measurable (fun x : ι → R => A *ᵥ x) :=
  (continuous_const.matrix_mulVec continuous_id : Continuous fun x : ι → R => A *ᵥ x).measurable

theorem char_smul_map (lam : Measure R) [lam.IsAddHaarMeasure] (u : Rˣ) :
    distribHaarChar R u • lam.map (fun x => (u : R) * x) = lam := by
  have hm : Measurable fun x : R => (u : R) * x :=
    (continuous_const.mul continuous_id).measurable
  ext S hS
  rw [Measure.smul_apply, Measure.map_apply hm hS]
  have h1 := distribHaarChar_mul lam u ((fun x : R => (u : R) * x) ⁻¹' S)
  have e : u • ((fun x : R => (u : R) * x) ⁻¹' S) = S := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e] at h1
  rw [ENNReal.smul_def, smul_eq_mul]
  exact h1

theorem map_transvection (lam : Measure R) [lam.IsAddHaarMeasure] (i j : ι) (c : R) (hij : i ≠ j) :
    (Measure.pi fun _ : ι => lam).map (fun x => transvection i j c *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  have ht := measurable_mulVec (transvection i j c)
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  simp [transvection, add_mulVec, single_mulVec, hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x i xᵢ)]

theorem map_diagonal (lam : Measure R) [lam.IsAddHaarMeasure] (d : ι → Rˣ) :
    distribHaarChar R (∏ i, d i) •
        (Measure.pi fun _ : ι => lam).map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.smul_apply, Measure.map_apply (measurable_mulVec _) (MeasurableSet.univ_pi hs)]
  have h1 : (fun x : ι → R => diagonal (fun i => (d i : R)) *ᵥ x) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun i => (fun y : R => (d i : R) * y) ⁻¹' s i := by
    ext f
    simp [mulVec_diagonal]
  have hm : ∀ i, Measurable fun x : R => (d i : R) * x := fun i =>
    (continuous_const.mul continuous_id).measurable
  rw [h1, Measure.pi_pi, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_finset_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 := congrArg (fun m : Measure R => m (s i)) (char_smul_map lam (d i))
  simp only [Measure.smul_apply, Measure.map_apply (hm i) (hs i)] at h2
  rw [← h2]
  rfl

end Ring

theorem smul_map_pi {F : Type} [Field F] {R : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    {ι : Type} [Fintype ι] [DecidableEq ι] (lam : Measure R) [lam.IsAddHaarMeasure]
    (A : Matrix ι ι F) (h : A.det ≠ 0) :
    distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det h)) •
        (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  let u : Fˣ →* Rˣ := Units.map (algebraMap F R : F →* R)
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun A : Matrix ι ι F => ∀ h : A.det ≠ 0, distribHaarChar R (u (Units.mk0 A.det h)) •
        (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      Measure.pi fun _ : ι => lam) A h ?_ ?_ ?_ h
  · intro D hD h
    have hD' : ∀ i, D i ≠ 0 := fun i => by
      rw [det_diagonal] at hD
      exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have e1 : u (Units.mk0 (diagonal D).det h) = ∏ i, u (Units.mk0 (D i) (hD' i)) := by
      rw [← map_prod]
      congr 1
      ext
      simp [det_diagonal]
    have e2 : (diagonal D).map (algebraMap F R) =
        diagonal fun i => ((u (Units.mk0 (D i) (hD' i)) : Rˣ) : R) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [u]
      · simp [u, hab]
    rw [e1, e2]
    exact map_diagonal lam _
  · intro t h
    obtain ⟨i, j, hij, c⟩ := t
    have e1 : u (Units.mk0 (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩).det h) = 1 := by
      rw [show Units.mk0 (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩).det h = 1 from
        Units.ext (by simpa [TransvectionStruct.toMatrix] using det_transvection_of_ne i j hij c), map_one]
    have e2 : (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ : Matrix ι ι F).map (algebraMap F R) =
        transvection i j (algebraMap F R c) := by
      ext a b
      simp [TransvectionStruct.toMatrix, transvection, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply, apply_ite (algebraMap F R)]
    rw [e1, e2, map_one, one_smul]
    exact map_transvection lam i j _ hij
  · intro A B hA hB IHA IHB h
    have e1 : Units.mk0 (A * B).det h = Units.mk0 A.det hA * Units.mk0 B.det hB :=
      Units.ext (by simp [det_mul])
    have e2 : (fun x : ι → R => (A * B).map (algebraMap F R) *ᵥ x) =
        (fun x => A.map (algebraMap F R) *ᵥ x) ∘ (fun x => B.map (algebraMap F R) *ᵥ x) := by
      ext1 x
      simp [Matrix.map_mul, mulVec_mulVec]
    rw [e1, e2, map_mul, map_mul, mul_smul,
      ← Measure.map_map (measurable_mulVec _) (measurable_mulVec _), ← Measure.map_smul, IHB hB]
    exact IHA hA

theorem map_mulVec_eq_smul : ∀ (F : Type) [Field F] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (ι : Type)
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∀ (lam : Measure R),
    lam.IsAddHaarMeasure → ∀ c : ℝ≥0, lam.map (fun x => algebraMap F R A.det * x) = c • lam →
    ∀ μ : Measure (ι → R), μ.IsAddHaarMeasure →
      μ.map (fun x => A.map (algebraMap F R) *ᵥ x) = c • μ := by
  intro F _ R _ _ _ _ _ _ _ _ _ ι _ _ A hA lam hlam c hc μ hμ
  have h1 := smul_map_pi lam A hA
  have h2 := char_smul_map lam (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))
  set d := distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))
  have h2' : d • lam.map (fun x => algebraMap F R A.det * x) = lam := h2
  rw [hc] at h2'
  obtain ⟨K, hKc, hK0⟩ : ∃ K : Set R, IsCompact K ∧ K ∈ 𝓝 (0 : R) := exists_compact_mem_nhds 0
  have hdc : d * c = 1 := by
    have h3 := congrArg (fun m : Measure R => m K) h2'
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    rw [← mul_assoc, ← ENNReal.coe_mul] at h3
    have h4 : ((d * c : ℝ≥0) : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds lam hK0).ne' hKc.measure_lt_top.ne).1
        (h3.trans (one_mul _).symm)
    exact_mod_cast h4
  have h4 : (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      c • Measure.pi fun _ : ι => lam := by
    conv_rhs => rw [← h1]
    rw [smul_smul, mul_comm c d, hdc, one_smul]
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • Measure.pi fun _ : ι => lam :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul_of_regular μ (Measure.pi fun _ : ι => lam)⟩
  rw [hk, Measure.map_smul, h4, smul_comm]

end GlobalTheory.CompanionTheory.SW.DetScale
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermTop

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_sigR {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) :
    sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, h]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem sigR_inclR (σ : E →ₐ[F] E) (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := by
  simp [sigR, inclR]

theorem gramR_mem {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) {n M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := by
  intro a b
  simp only [gramR, hR, hform, JR, Matrix.map_apply, map_sum, map_mul, sigR_sigR R h, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem isModTop : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

theorem isTopRing [Module.Finite F E] : IsTopologicalRing (R ⊗[F] E) :=
  haveI := isModTop (F := F) (E := E) R
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

theorem exists_homeo [Module.Finite F E] :
    Nonempty ((R ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → R)) := by
  haveI := isModTop (F := F) (E := E) R
  haveI := isTopRing (F := F) (E := E) R
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩

theorem continuous_sigR [Module.Finite F E] (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI := isModTop (F := F) (E := E) R
  haveI := isTopRing (F := F) (E := E) R
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

end

theorem herm_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ n : ℕ, LocallyCompactSpace (HermR R σ n) ∧ SecondCountableTopology (HermR R σ n) ∧ T2Space (HermR R σ n) ∧ BorelSpace (HermR R σ n) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ g : (Fin n → Fin M → R ⊗[F] E) → HermR R σ n, Continuous g ∧ ∀ X, gramR R σ J X = (g X : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ n
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  haveI := isTopRing (F := F) (E := E) R
  obtain ⟨e⟩ := exists_homeo (F := F) (E := E) R
  haveI : LocallyCompactSpace (R ⊗[F] E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (R ⊗[F] E) := e.secondCountableTopology
  haveI : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  have hs := continuous_sigR R σ
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R ⊗[F] E))
  have hc : IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
    have : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
        ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
      ext S
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
    · exact hs.comp (continuous_id.matrix_elem b a)
    · exact continuous_id.matrix_elem a b
  refine ⟨hc.locallyCompactSpace, ?_, inferInstance, ⟨rfl⟩, ?_⟩
  · exact TopologicalSpace.Subtype.secondCountableTopology _
  · intro M J hJ
    refine ⟨fun X => ⟨gramR R σ J X, gramR_mem R (sigma_sigma hσ) hJ.1 X⟩, ?_, fun _ => rfl⟩
    refine Continuous.subtype_mk ?_ _
    refine continuous_matrix fun a b => ?_
    simp only [gramR, hR, hform]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    refine ((hs.comp ?_).mul continuous_const).mul ?_
    · exact (continuous_apply i).comp (continuous_apply a)
    · exact (continuous_apply j).comp (continuous_apply b)

end GlobalTheory.CompanionTheory.SW.HermTop
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianUnitFormDiagonalizes
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.RingDiag

open HeckeCharacterZeroLocus.SiegelWeilU

variable {A : Type} [CommRing A] {m : ℕ}

def bd (a : A) (M : Matrix (Fin m) (Fin m) A) : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
  fun i j => Fin.cases (Fin.cases a (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => M i' j') j) i

@[simp] lemma bd_zero_zero (a : A) (M : Matrix (Fin m) (Fin m) A) : bd a M 0 0 = a := rfl
@[simp] lemma bd_zero_succ (a : A) (M : Matrix (Fin m) (Fin m) A) (j : Fin m) :
    bd a M 0 j.succ = 0 := rfl
@[simp] lemma bd_succ_zero (a : A) (M : Matrix (Fin m) (Fin m) A) (i : Fin m) :
    bd a M i.succ 0 = 0 := rfl
@[simp] lemma bd_succ_succ (a : A) (M : Matrix (Fin m) (Fin m) A) (i j : Fin m) :
    bd a M i.succ j.succ = M i j := rfl

lemma bd_mul (a b : A) (M N : Matrix (Fin m) (Fin m) A) :
    bd a M * bd b N = bd (a * b) (M * N) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

lemma det_bd (a : A) (M : Matrix (Fin m) (Fin m) A) : (bd a M).det = a * M.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have : (bd a M).submatrix Fin.succ Fin.succ = M := by
    ext i j; simp
  simp [this]

lemma cT_bd (σ : A →+* A) (a : A) (M : Matrix (Fin m) (Fin m) A) :
    cT σ (bd a M) = bd (σ a) (cT σ M) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [cT]

lemma bd_diagonal (a : A) (d : Fin m → A) :
    bd a (Matrix.diagonal d) = Matrix.diagonal (Fin.cons a d : Fin (m + 1) → A) := by
  have h0 : ∀ j' : Fin m, (0 : Fin (m + 1)) ≠ j'.succ := fun j' => (Fin.succ_ne_zero j').symm
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.diagonal_apply, h0]

def uni (r : Fin m → A) : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
  fun i j => Fin.cases (Fin.cases 1 r j)
    (fun i' => Fin.cases 0 (fun j' => (1 : Matrix (Fin m) (Fin m) A) i' j') j) i

@[simp] lemma uni_zero_zero (r : Fin m → A) : uni r 0 0 = 1 := rfl
@[simp] lemma uni_zero_succ (r : Fin m → A) (j : Fin m) : uni r 0 j.succ = r j := rfl
@[simp] lemma uni_succ_zero (r : Fin m → A) (i : Fin m) : uni r i.succ 0 = 0 := rfl
@[simp] lemma uni_succ_succ (r : Fin m → A) (i j : Fin m) :
    uni r i.succ j.succ = (1 : Matrix (Fin m) (Fin m) A) i j := rfl

lemma det_uni (r : Fin m → A) : (uni r).det = 1 := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have : (uni r).submatrix Fin.succ Fin.succ = 1 := by
    ext i j; simp
  simp [this]

def schur (K : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (b : A) : Matrix (Fin m) (Fin m) A :=
  fun i j => K i.succ j.succ - K i.succ 0 * b * K 0 j.succ

lemma mul_uni (K : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (r : Fin m → A) (i : Fin (m + 1)) :
    (K * uni r) i 0 = K i 0 ∧ ∀ j : Fin m, (K * uni r) i j.succ = K i j.succ + K i 0 * r j := by
  constructor
  · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · intro j
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, add_comm]

lemma cT_uni_mul (σ : A →+* A) (P : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (r : Fin m → A)
    (j : Fin (m + 1)) :
    (cT σ (uni r) * P) 0 j = P 0 j ∧
      ∀ i : Fin m, (cT σ (uni r) * P) i.succ j = P i.succ j + σ (r i) * P 0 j := by
  constructor
  · simp [cT, Matrix.mul_apply, Fin.sum_univ_succ]
  · intro i
    simp [cT, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, add_comm,
      apply_ite σ]

lemma schur_step (σ : A →+* A) (K : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hK : ∀ i j, σ (K j i) = K i j) (b : A) (hb : b * K 0 0 = 1) (hσb : σ b = b) :
    cT σ (uni fun j => -(b * K 0 j.succ)) * K * (uni fun j => -(b * K 0 j.succ)) =
      bd (K 0 0) (schur K b) := by
  set r : Fin m → A := fun j => -(b * K 0 j.succ) with hr
  have hσr : ∀ i, σ (r i) = -(b * K i.succ 0) := by
    intro i; simp [hr, hσb, hK]
  have hzero : ∀ j : Fin m, K 0 j.succ + K 0 0 * r j = 0 := by
    intro j
    have : K 0 0 * r j = -((b * K 0 0) * K 0 j.succ) := by simp only [hr]; ring
    rw [this, hb]; ring
  rw [Matrix.mul_assoc]
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · rw [(cT_uni_mul σ _ r 0).1, (mul_uni K r 0).1]; simp
  · rw [(cT_uni_mul σ _ r _).1, (mul_uni K r 0).2, hzero]; simp
  · rw [(cT_uni_mul σ _ r 0).2, (mul_uni K r _).1, (mul_uni K r 0).1, hσr]
    simp only [bd_succ_zero]
    have : b * K i'.succ 0 * K 0 0 = (b * K 0 0) * K i'.succ 0 := by ring
    rw [neg_mul, this, hb]; ring
  · rw [(cT_uni_mul σ _ r _).2, (mul_uni K r _).2, (mul_uni K r 0).2, hzero, hσr]
    simp only [bd_succ_succ, schur, hr]; ring

lemma det_cT (σ : A →+* A) (g : Matrix (Fin m) (Fin m) A) : (cT σ g).det = σ g.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl

lemma cT_cT (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) {p q : Type}
    (M : Matrix p q A) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

lemma cT_congr_herm (σ : A →+* A) {n : ℕ} (hσ : ∀ y, σ (σ y) = y)
    (J g : Matrix (Fin n) (Fin n) A) (hJ : ∀ i j, σ (J j i) = J i j) :
    ∀ i j, σ ((cT σ g * J * g) j i) = (cT σ g * J * g) i j := by
  have hJ' : cT σ J = J := by ext i j; exact hJ i j
  have : cT σ (cT σ g * J * g) = cT σ g * J * g := by
    rw [cT_mul, cT_mul, cT_cT σ hσ, hJ', Matrix.mul_assoc]
  intro i j
  exact congrFun (congrFun this i) j

lemma corner (σ : A →+* A) {n : ℕ} (J g : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (x : Fin (n + 1) → A) (hg : ∀ i, g i 0 = x i) :
    (cT σ g * J * g) 0 0 = hform σ J x x := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, hg, hform,
    Finset.sum_mul]
  exact Finset.sum_comm

lemma unimodular (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (x : Fin n → A) (b : A)
    (hb : b * hform σ J x x = 1) : ∃ c : Fin n → A, ∑ i, c i * x i = 1 := by
  refine ⟨fun j => b * ∑ i, σ (x i) * J i j, ?_⟩
  rw [← hb, hform, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (b * ∑ i : Fin n, σ (x i) * J i j) * x j = b * ∑ i : Fin n, σ (x i) * J i j * x j
  rw [mul_assoc, Finset.sum_mul]

theorem diagonalise : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A), (∀ y, σ (σ y) = y) → (∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x)) → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ (g : Matrix (Fin m) (Fin m) A) (d : Fin m → A), IsUnit g.det ∧ (∀ i, IsUnit (d i) ∧ σ (d i) = d i) ∧ HeckeCharacterZeroLocus.SiegelWeilU.cT σ g * J * g = Matrix.diagonal d := by
  intro A _ _ σ hσ H m
  induction m with
  | zero =>
    intro J _ _
    exact ⟨1, Fin.elim0, by simp, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ m ih =>
    intro J hJ hdet
    obtain ⟨x, hx⟩ := H m J hJ hdet
    obtain ⟨b, hb⟩ := hx.exists_left_inv
    obtain ⟨g₀, hg₀, hcol⟩ := GlobalTheory.CompanionTheory.SW.SemilocalColumn.exists_invertible_first_column A m x (unimodular σ J x b hb)
    set K := cT σ g₀ * J * g₀ with hKdef
    have hK : ∀ i j, σ (K j i) = K i j := cT_congr_herm σ hσ J g₀ hJ
    have hcorner : K 0 0 = hform σ J x x := corner σ J g₀ x hcol
    have hbK : b * K 0 0 = 1 := by rw [hcorner]; exact hb
    have hβ : IsUnit (K 0 0) := by rw [hcorner]; exact hx
    have hσβ : σ (K 0 0) = K 0 0 := hK 0 0
    have hσb : σ b = b := by
      have h1 : σ b * K 0 0 = 1 := by
        have := congrArg σ hbK
        rwa [map_mul, hσβ, map_one] at this
      calc σ b = σ b * (K 0 0 * b) := by rw [mul_comm (K 0 0), hbK, mul_one]
        _ = (σ b * K 0 0) * b := by ring
        _ = b := by rw [h1, one_mul]
    set r : Fin m → A := fun j => -(b * K 0 j.succ) with hr
    have hstep := schur_step σ K hK b hbK hσb
    have hKdet : IsUnit K.det := by
      rw [hKdef, Matrix.det_mul, Matrix.det_mul, det_cT]
      exact ((hg₀.map σ).mul hdet).mul hg₀
    have hJ₁det : IsUnit (schur K b).det := by
      have h2 : (K 0 0) * (schur K b).det = K.det := by
        rw [← det_bd, ← hstep, Matrix.det_mul, Matrix.det_mul, det_cT, det_uni]; simp
      rw [← h2] at hKdet
      exact isUnit_of_mul_isUnit_right hKdet
    have hJ₁ : ∀ i j, σ (schur K b j i) = schur K b i j := by
      intro i j
      simp only [schur, map_sub, map_mul, hσb, hK]
      ring
    obtain ⟨g₁, d₁, hg₁, hd₁, hdiag⟩ := ih (schur K b) hJ₁ hJ₁det
    refine ⟨g₀ * uni r * bd 1 g₁, Fin.cons (K 0 0) d₁, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, det_uni, det_bd]
      simpa using hg₀.mul hg₁
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · simpa using ⟨hβ, hσβ⟩
      · simpa using hd₁ i'
    · have e : cT σ (g₀ * uni r * bd 1 g₁) * J * (g₀ * uni r * bd 1 g₁) =
          cT σ (bd 1 g₁) * (cT σ (uni r) * K * uni r) * bd 1 g₁ := by
        rw [hKdef, cT_mul, cT_mul]
        simp only [Matrix.mul_assoc]
      rw [e, hstep, cT_bd, bd_mul, bd_mul, hdiag, map_one, one_mul, mul_one, bd_diagonal]

end GlobalTheory.CompanionTheory.SW.RingDiag
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlaces
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodInt

theorem valued_algebraMap {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem eventually_le_one {F : Type} [Field F] [NumberField F] (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x ≤ 1 := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  rw [Filter.eventually_cofinite]
  refine h.subset fun v hv => ?_
  exact not_le.mp hv

theorem eventually_eq_one {F : Type} [Field F] [NumberField F] (x : F) (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x = 1 := by
  filter_upwards [eventually_le_one x, eventually_le_one x⁻¹] with v h1 h2
  refine le_antisymm h1 ?_
  rw [map_inv₀] at h2
  have h0 : v.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  exact (inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2

theorem repr_inclR {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R x) k = algebraMap F R (b.repr x k) := by
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] x) k = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem rational_integral_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ x : E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) x) k ∈ v.adicCompletionIntegers F) ∧ ∀ x : F, x ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) x) = 1 := by
  intro F E _ _ _ _ _ σ _ d b
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · have h : ∀ k : Fin d, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        v.valuation F (b.repr x k) ≤ 1 := fun k => eventually_le_one _
    filter_upwards [Filter.eventually_all.mpr h] with v hv k
    rw [repr_inclR, HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
    exact hv k
  · filter_upwards [eventually_eq_one x hx] with v hv
    rw [valued_algebraMap, hv]

end GlobalTheory.CompanionTheory.SW.GoodInt
end

