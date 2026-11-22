import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses.BaseChangeSign

section Gen
variable {L : Type} [Field L] (τ : L →+* L) {n : ℕ}

theorem hform_eq_mat (J : Matrix (Fin n) (Fin n) L) {ι : Type} [Fintype ι] (f : ι → Fin n → L) (i j : ι) :
    hform τ J (f i) (f j) = (cT τ (Matrix.of fun r i => f i r) * J * Matrix.of fun r i => f i r) i j := by
  simp only [hform, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_det_change (J : Matrix (Fin n) (Fin n) L) (V : Submodule L (Fin n → L)) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c b : Module.Basis ι L V) :
    (Matrix.of fun i j => hform τ J (b i).1 (b j).1).det =
      τ (c.toMatrix b).det * (Matrix.of fun i j => hform τ J (c i).1 (c j).1).det * (c.toMatrix b).det := by
  have hM : (Matrix.of fun r i => ((b i : V) : Fin n → L) r) =
      (Matrix.of fun r i => ((c i : V) : Fin n → L) r) * c.toMatrix b := by
    ext r j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    have h := c.sum_toMatrix_smul_self b j
    calc ((b j : V) : Fin n → L) r = ((∑ i, c.toMatrix b i j • c i : V) : Fin n → L) r := by rw [h]
      _ = _ := by
        simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e1 : (Matrix.of fun i j => hform τ J (b i).1 (b j).1) =
      cT τ (Matrix.of fun r i => ((b i : V) : Fin n → L) r) * J * Matrix.of fun r i => ((b i : V) : Fin n → L) r := by
    ext i j; exact hform_eq_mat τ J (fun i => ((b i : V) : Fin n → L)) i j
  have e2 : (Matrix.of fun i j => hform τ J (c i).1 (c j).1) =
      cT τ (Matrix.of fun r i => ((c i : V) : Fin n → L) r) * J * Matrix.of fun r i => ((c i : V) : Fin n → L) r := by
    ext i j; exact hform_eq_mat τ J (fun i => ((c i : V) : Fin n → L)) i j
  have hdet : ∀ P : Matrix ι ι L, (cT τ P).det = τ P.det := by
    intro P; unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl
  rw [e1, e2, hM, cT_mul]
  set Mc := Matrix.of fun r i => ((c i : V) : Fin n → L) r
  set P := c.toMatrix b
  have : cT τ P * cT τ Mc * J * (Mc * P) = cT τ P * (cT τ Mc * J * Mc) * P := by
    simp only [Matrix.mul_assoc]
  rw [this, Matrix.det_mul, Matrix.det_mul, hdet]

theorem toMatrix_det_ne {V : Submodule L (Fin n → L)} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c b : Module.Basis ι L V) : (c.toMatrix b).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (c.toMatrix_mul_toMatrix_flip b)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

end Gen

section BC
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ}

theorem mem_ker_map {A : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hx : x ∈ LinearMap.ker (Matrix.toLin' A)) :
    (φ ∘ x) ∈ LinearMap.ker (Matrix.toLin' (A.map φ)) := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx ⊢
  funext i
  rw [← RingHom.map_mulVec, hx]; simp

theorem finrank_ker_map (A : Matrix (Fin n) (Fin n) K) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' (A.map φ))) =
      Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (A.map φ))
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  have h3 : (A.map φ).rank = A.rank := GlobalTheory.Core.Rk.rank_map_field φ A
  change (A.map φ).rank + _ = _ at h1
  change A.rank + _ = _ at h2
  simp only [Module.finrank_fin_fun] at h1 h2
  omega

end BC

section Val
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dif_neg hx', dif_neg hy', dif_neg hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]
  rw [this, toAdd_mul]; ring

theorem sign_conj_mul {τ : L →+* L} (hv : ∀ x, Valued.v (τ x) = Valued.v x) {t : L} (ht : t ≠ 0) (a : L) :
    (-1 : ℂ) ^ ordL (τ t * a * t) = (-1) ^ ordL a := by
  by_cases ha : a = 0
  · simp [ha]
  have hτ : τ t ≠ 0 := (map_ne_zero τ).2 ht
  have ho : ordL (τ t) = ordL t := by
    unfold ordL; simp only [hv]
  rw [ordL_mul (mul_ne_zero hτ ha) ht, ordL_mul hτ ha, ho,
    show ordL t + ordL a + ordL t = ordL a + 2 * ordL t by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]
  norm_num

end Val

section Main
variable {K L : Type} [Field K] [Field L] (σ : K →+* K) (τ : L →+* L) (φ : K →+* L) {n : ℕ}

theorem gram_det_map (hφ : ∀ x, τ (φ x) = φ (σ x)) (H A : Matrix (Fin n) (Fin n) K) :
    ∃ t : L, t ≠ 0 ∧ (gramOn τ (H.map φ) (LinearMap.ker (Matrix.toLin' (A.map φ)))).det =
      τ t * φ (gramOn σ H (LinearMap.ker (Matrix.toLin' A))).det * t := by
  letI := φ.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 φ.injective
  set V := LinearMap.ker (Matrix.toLin' A) with hV
  set V' := LinearMap.ker (Matrix.toLin' (A.map φ)) with hV'
  have hk : Module.finrank L V' = Module.finrank K V := finrank_ker_map φ A
  rcases isEmpty_or_nonempty (Fin (Module.finrank L V')) with he | hne
  · haveI : IsEmpty (Fin (Module.finrank K V)) := hk ▸ he
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Matrix.det_isEmpty, Matrix.det_isEmpty]; simp
  let b := Module.finBasis K V
  let v : Fin (Module.finrank L V') → V' := fun i =>
    ⟨φ ∘ ((b (Fin.cast hk i) : V) : Fin n → K), mem_ker_map φ (b (Fin.cast hk i)).2⟩
  have hli : LinearIndependent L v := by
    apply LinearIndependent.of_comp V'.subtype
    have h0 : LinearIndependent K (fun i => ((b (Fin.cast hk i) : V) : Fin n → K)) :=
      (b.linearIndependent.map' V.subtype V.ker_subtype).comp _ (Fin.cast_injective hk)
    exact linearIndependent_algebraMap_comp_iff.2 h0
  let c := basisOfLinearIndependentOfCardEqFinrank hli (Fintype.card_fin _)
  have hc : ∀ i, c i = v i := fun i => by simp [c]
  refine ⟨(c.toMatrix (Module.finBasis L V')).det, toMatrix_det_ne c _, ?_⟩
  have e1 : gramOn τ (H.map φ) V' =
      Matrix.of fun i j => hform τ (H.map φ) (Module.finBasis L V' i).1 (Module.finBasis L V' j).1 := rfl
  rw [e1, gram_det_change τ (H.map φ) V' c (Module.finBasis L V')]
  have e2 : (Matrix.of fun i j => hform τ (H.map φ) (c i).1 (c j).1) =
      ((gramOn σ H V).map φ).submatrix (finCongr hk) (finCongr hk) := by
    ext i j
    simp only [Matrix.of_apply, hc, v, Matrix.submatrix_apply, Matrix.map_apply, gramOn, hform, map_sum, map_mul,
      Function.comp_apply, hφ, finCongr_apply]
    rfl
  rw [e2, Matrix.det_submatrix_equiv_self,
    show ((gramOn σ H V).map φ).det = φ (gramOn σ H V).det from (RingHom.map_det φ _).symm]

end Main

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (n : ℕ) (H A : Matrix (Fin n) (Fin n) E),
    (-1 : ℂ) ^ ordL (gramOn (cj w) (H.map (algebraMap E (w.adicCompletion E)))
      (LinearMap.ker (Matrix.toLin' (A.map (algebraMap E (w.adicCompletion E)))))).det =
    (-1) ^ ordL (algebraMap E (w.adicCompletion E)
      (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H (LinearMap.ker (Matrix.toLin' A))).det) := by
  intro E _ _ _ hU w hw n H A
  have hc := GlobalTheory.ConjAtPlace.main E hU w
  have hφ : ∀ x : E, cj w (algebraMap E (w.adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) ((IsCMField.complexConj E).toRingEquiv.toRingHom x) :=
    fun x => (hc.2.2.2.1 hw).1 x
  obtain ⟨t, ht, hdet⟩ := gram_det_map (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w)
    (algebraMap E (w.adicCompletion E)) hφ H A
  rw [hdet, sign_conj_mul hc.2.2.1 ht]

end GlobalTheory.UnitaryClasses.BaseChangeSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergAnnihilationCreationCommutatorEqDelta
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock.CommDM
open GlobalTheory.CCRFock

private lemma unitAt_apply_eq_ite {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ)
    (w : W) (a : Ix P Q) (b : Ix R S) : unitAt j z w a b = if (w, (a, b)) = j then z else 0 := by
  obtain ⟨j1, j2, j3⟩ := j
  by_cases h1 : w = j1
  · subst h1
    by_cases h2 : a = j2
    · subst h2
      by_cases h3 : b = j3
      · subst h3
        simp [unitAt]
      · simp [unitAt, h3, Ne.symm h3]
    · simp [unitAt, h2, Ne.symm h2]
  · simp [unitAt, h1]

theorem sum_unitAt {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (j k : W × (Ix P Q × Ix R S)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAt j z w a b * star (unitAt k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  have key : ∀ (w : W) (a : Ix P Q) (b : Ix R S), lineSign a b * unitAt j z w a b * star (unitAt k z' w a b) =
      if (w, (a, b)) = j then (if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0) else 0 := by
    intro w a b
    rw [unitAt_apply_eq_ite, unitAt_apply_eq_ite]
    by_cases hj : (w, (a, b)) = j
    · subst hj
      by_cases hk : (w, (a, b)) = k
      · subst hk
        simp
      · simp [hk]
    · simp [hj]
  simp only [key]
  rw [Fintype.sum_eq_single j.1, Fintype.sum_eq_single j.2.1, Fintype.sum_eq_single j.2.2]
  all_goals first
    | (intro x hx; simp [Prod.ext_iff, hx])
    | simp

theorem lineSign_cases {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : (lineSign a b : ℂ) = 1 ∨ (lineSign a b : ℂ) = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem comm_expand {V : Type} [AddCommGroup V] [Module ℂ V] (A A' B B' : Module.End ℂ V) (c u v : ℂ) :
    -(c • (A + u • A')) * (c • (B - v • B')) - (c • (B - v • B')) * -(c • (A + u • A')) =
      -((c * c) • ((A * B - B * A) - v • (A * B' - B' * A) + u • (A' * B - B * A') - (u * v) • (A' * B' - B' * A'))) := by
  simp only [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_smul, mul_add, add_mul, mul_sub, sub_mul,
    smul_add, smul_sub, smul_neg]
  module

theorem inv_sq : (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ * (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ =
    (8 * (Real.pi : ℂ))⁻¹ := by
  rw [← mul_inv]
  congr 1
  have h : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  linear_combination 4 * h

theorem fockD_fockM_comm : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ j k : W × (Ix P Q × Ix R S), GlobalTheory.CCRFock.fockD H j * GlobalTheory.CCRFock.fockM H k - GlobalTheory.CCRFock.fockM H k * GlobalTheory.CCRFock.fockD H j =
      if j = k then 1 else 0 := by
  intro V _ _ W _ _ P Q R S H _ _ hcomm j k
  simp only [GlobalTheory.CCRFock.fockD, GlobalTheory.CCRFock.fockM]
  rw [comm_expand, hcomm, hcomm, hcomm, hcomm, sum_unitAt, sum_unitAt, sum_unitAt, sum_unitAt, inv_sq]
  by_cases hjk : j = k
  · subst hjk
    rcases lineSign_cases j.2.1 j.2.2 with h | h
    · simp only [if_true, h]
      match_scalars
      simp
      field_simp
      ring_nf
      simp [Complex.I_sq]
    · simp only [if_true, h]
      match_scalars
      simp
      field_simp
      ring_nf
      simp [Complex.I_sq]
  · simp [hjk]

end GlobalTheory.CCRFock.CommDM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCreationOperatorsCommuteOfCcr
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem fockM_comm_sum {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (j k : W × (Ix P Q × Ix R S)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAt j z w a b * star (unitAt k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  obtain ⟨w, a, b⟩ := j
  obtain ⟨w', a', b'⟩ := k
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · by_cases hw : w = w'
    · subst hw
      by_cases ha : a = a'
      · subst ha
        by_cases hb : b = b'
        · subst hb; simp [unitAt]
        · simp [unitAt, hb, Ne.symm hb]
      · simp [unitAt, ha, Ne.symm ha]
    · simp [unitAt, hw]
  · intro c _ hc; simp [unitAt, Ne.symm hc]
  · simp
  · intro c _ hc; simp [unitAt, Ne.symm hc]
  · simp
  · intro c _ hc; simp [unitAt, hc]
  · simp

theorem fockM_comm : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ j k : W × (Ix P Q × Ix R S), GlobalTheory.CCRFock.fockM H j * GlobalTheory.CCRFock.fockM H k = GlobalTheory.CCRFock.fockM H k * GlobalTheory.CCRFock.fockM H j := by
  intro V _ _ W _ _ P Q R S H _ _ hc j k
  have h11 := hc (unitAt j 1) (unitAt k 1)
  have h1i := hc (unitAt j 1) (unitAt k Complex.I)
  have hi1 := hc (unitAt j Complex.I) (unitAt k 1)
  have hii := hc (unitAt j Complex.I) (unitAt k Complex.I)
  rw [fockM_comm_sum] at h11 h1i hi1 hii
  by_cases hjk : j = k
  · rw [hjk]
  · simp only [if_neg hjk, Complex.zero_im, Complex.ofReal_zero, mul_zero, zero_smul, sub_eq_zero] at h11 h1i hi1 hii
    unfold fockM
    have c : Commute (H (unitAt j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I))
        (H (unitAt k 1) - (lineSign k.2.1 k.2.2 * Complex.I) • H (unitAt k Complex.I)) :=
      Commute.sub_left (Commute.sub_right h11 (Commute.smul_right h1i _))
        (Commute.smul_left (Commute.sub_right hi1 (Commute.smul_right hii _)) _)
    exact ((c.smul_left _).smul_right _).eq

end GlobalTheory.CCRFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativeOnSchwartzTensorConj
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory

theorem heisenbergDeriv_tensor_conj (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a₁ b₁ a₂ b₂ : κ → AF F)
    (f g₁ g₂ : SInf F κ) (f₀ h : SInf F (κ ⊕ κ))
    (hg₁ : ∀ y, g₁ y = fderiv ℝ f y (fun i => evI F (a₁ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₁ i)) : ℝ) * f y)
    (hg₂ : ∀ y, g₂ y = fderiv ℝ f y (fun i => evI F (a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₂ i)) : ℝ) * f y)
    (hh : ∀ x, h x = fderiv ℝ f₀ x (fun i => evI F (Sum.elim a₁ a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ) * f₀ x)
    (hf₀ : ∀ x, f₀ x = f (x ∘ Sum.inl) * star (f (x ∘ Sum.inr))) (x : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    h x = g₁ (x ∘ Sum.inl) * star (f (x ∘ Sum.inr)) + f (x ∘ Sum.inl) * star (g₂ (x ∘ Sum.inr)) := by
  let L₁ : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Sum.inl i))
  let L₂ : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Sum.inr i))
  have hL₁ : ∀ y, L₁ y = y ∘ Sum.inl := fun y => rfl
  have hL₂ : ∀ y, L₂ y = y ∘ Sum.inr := fun y => rfl
  have hfun : (f₀ : (κ ⊕ κ → mixedEmbedding.mixedSpace F) → ℂ) = fun y => f (L₁ y) * Complex.conjCLE (f (L₂ y)) := by
    funext y; rw [hf₀]; rfl
  have hd₁ : HasFDerivAt (fun y => f (L₁ y)) ((fderiv ℝ f (L₁ x)).comp L₁) x :=
    (f.differentiableAt.hasFDerivAt).comp x L₁.hasFDerivAt
  have hd₂ : HasFDerivAt (fun y => Complex.conjCLE (f (L₂ y)))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ f (L₂ x)).comp L₂)) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x ((f.differentiableAt.hasFDerivAt).comp x L₂.hasFDerivAt)
  have hD : fderiv ℝ f₀ x = f (L₁ x) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ f (L₂ x)).comp L₂)) + Complex.conjCLE (f (L₂ x)) • ((fderiv ℝ f (L₁ x)).comp L₁) := by
    rw [hfun]
    exact (hd₁.mul hd₂).fderiv
  have hevneg : ∀ b : AF F, evI F (-b) = - evI F b := by
    intro b
    unfold evI
    rw [show (-b).1 = -b.1 from rfl, map_neg]
  have htr : (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ)
      = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, (x ∘ Sum.inl) i * evI F (b₁ i))
        - Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, (x ∘ Sum.inr) i * evI F (b₂ i)) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, hevneg, mul_neg, Finset.sum_neg_distrib,
      map_add, map_neg, Function.comp_apply]
    ring
  rw [hh x, hg₁, hg₂, hD, htr, hf₀]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, hL₁, hL₂, smul_eq_mul]
  have e1 : ((fun i => evI F (Sum.elim a₁ a₂ i)) ∘ Sum.inl) = fun i => evI F (a₁ i) := rfl
  have e2 : ((fun i => evI F (Sum.elim a₁ a₂ i)) ∘ Sum.inr) = fun i => evI F (a₂ i) := rfl
  rw [e1, e2]
  simp only [star_sub, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFamilyExpandCreationAnnihilation
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem lineSign_mul_self {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem sum_unitAt {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (c : W → Matrix (Ix P Q) (Ix R S) ℂ) :
    c = ∑ j : W × (Ix P Q × Ix R S), unitAt j (c j.1 j.2.1 j.2.2) := by
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [← Finset.univ_sum_single c]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [Matrix.matrix_eq_sum_single (c w)]
  funext v
  simp only [unitAt, Finset.sum_apply]
  by_cases h : v = w
  · subst h
    simp
  · simp [h]

theorem unitAt_re_im {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ) :
    unitAt j z = ((z.re : ℝ) : ℂ) • unitAt j 1 + ((z.im : ℝ) : ℂ) • unitAt j Complex.I := by
  simp only [unitAt, ← Pi.single_smul', ← Pi.single_add, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul, mul_one,
    Complex.re_add_im]

theorem heis_expand : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    ∀ c : W → Matrix (Ix P Q) (Ix R S) ℂ, H c = ∑ j : W × (Ix P Q × Ix R S),
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • GlobalTheory.CCRFock.fockM H j +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • GlobalTheory.CCRFock.fockD H j) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul c
  have h0 : H 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let H' : (W → Matrix (Ix P Q) (Ix R S) ℂ) →+ Module.End ℂ V := ⟨⟨H, h0⟩, hadd⟩
  have hsum : H c = ∑ j : W × (Ix P Q × Ix R S), H (unitAt j (c j.1 j.2.1 j.2.2)) := by
    conv_lhs => rw [sum_unitAt c]
    exact map_sum H' _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [unitAt_re_im, hadd, hsmul, hsmul]
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  have he := lineSign_mul_self j.2.1 j.2.2
  unfold fockM fockD coefM coefD
  generalize ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = s at hs ⊢
  generalize lineSign j.2.1 j.2.2 = e at he ⊢
  generalize H (unitAt j 1) = A
  generalize H (unitAt j Complex.I) = B
  generalize ((c j.1 j.2.1 j.2.2).re : ℂ) = x
  generalize ((c j.1 j.2.1 j.2.2).im : ℂ) = y
  have hI := Complex.I_mul_I
  match_scalars
  · field_simp
    ring
  · field_simp
    linear_combination (2 * y * e * e) * hI - 2 * y * he

end GlobalTheory.CCRFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoArchimedeanAdelicPureTensorStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergRho_archimedean_adelicPureTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    IsStd ψ → ∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f : SInf F κ,
      ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h := by
  first | exact @GlobalTheory.ArchHeisPure.rho_pureA | exact GlobalTheory.ArchHeisPure.rho_pureA | (intros; apply GlobalTheory.ArchHeisPure.rho_pureA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoSplitArchimedeanFiniteStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergRho_split_archimedean_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    ∀ w : Matrix α β (AE F E),
    ∃ (u : Matrix α β (AE F E)) (H : ((κ → Af F) → ℂ) → (κ → Af F) → ℂ), At (evI F) u ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        ∀ (f f₁ : SInf F κ) (h : (κ → Af F) → ℂ),
          (∀ h' : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F f h') = pureA F f₁ h') →
            d.rho ψ (actB (cA σ) g w) (pureA F f h) = pureA F f₁ (H h) := by
  first | exact @GlobalTheory.HeisSplit.rho_split | exact GlobalTheory.HeisSplit.rho_split | (intros; apply GlobalTheory.HeisSplit.rho_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMultiplicationFlatColumnsEvalStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMultiplicationFlat_columns_eval : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∃ c' : Fin d → A' →ₗ[E] E, (∀ x ∈ Submodule.span E (Φ.ι '' S.V S.T), ∑ i, c' i x • Φ.ι (b i) = x) ∧ ∀ (κ : S.Col) (u : Fin (S.D + 1) × Fin S.N → E), word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x) ∈ Submodule.span E (Φ.ι '' S.V S.T) ∧ ∀ i, aeval u (coordP S.mul (c i) κ.β (κ.x : A)) = c' i (word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x)) := by
  first | exact @GlobalTheory.HSShort.ColEval.columns_eval | exact GlobalTheory.HSShort.ColEval.columns_eval | (intros; apply GlobalTheory.HSShort.ColEval.columns_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyBoundTwistNegOfRegularSectionStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherCohomology_bound_twist_neg_of_regular_section' : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ (B : LB X) (hB : B.IsLB) (s : B.Sec), Mono (cutHom F hB s) → (∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (twistZ F B (-1)) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.higherCohomology_bound_twist_neg_of_regular_section | exact GlobalTheory.higherCohomology_bound_twist_neg_of_regular_section | (intros; apply GlobalTheory.higherCohomology_bound_twist_neg_of_regular_section <;> assumption)
end

