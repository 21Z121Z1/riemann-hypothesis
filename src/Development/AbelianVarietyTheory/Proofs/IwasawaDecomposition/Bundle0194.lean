import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0186
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0168
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HformMulVecRight
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Matrix

namespace GlobalTheory.GaugeEx.GramPair

section Ring

variable {A : Type} [CommRing A] (s : A →+* A) {M N : ℕ} (G : Matrix (Fin M) (Fin M) A)

theorem hform_eq_dot (x y : Fin M → A) :
    Formalism.UG.hform s G x y = (fun i => s (x i)) ⬝ᵥ G *ᵥ y := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (P : Matrix (Fin M) (Fin N) A) (x y : Fin N → A) :
    Formalism.UG.hform s G (P *ᵥ x) (P *ᵥ y) = Formalism.UG.hform s (Formalism.UG.cT s P * G * P) x y := by
  have e : (fun i => s ((P *ᵥ x) i)) = (fun i => s (x i)) ᵥ* Formalism.UG.cT s P := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose]
    exact RingHom.map_mulVec _ _ _ i
  rw [hform_eq_dot, hform_eq_dot, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

theorem hform_mulVec_right (P : Matrix (Fin M) (Fin N) A) (x : Fin M → A) (w : Fin N → A) :
    Formalism.UG.hform s G x (P *ᵥ w) = ∑ j, Formalism.UG.hform s G x (fun i => P i j) * w j := by
  simp only [Formalism.UG.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem hform_symm (hs : ∀ a, s (s a) = a) (hG : ∀ i j, s (G j i) = G i j) (x y : Fin M → A) :
    Formalism.UG.hform s G y x = s (Formalism.UG.hform s G x y) := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hG]
  ring

theorem hform_lin (a b c d : A) (x y : Fin M → A) :
    Formalism.UG.hform s G (a • x + b • y) (c • x + d • y) =
      s a * c * Formalism.UG.hform s G x x + s a * d * Formalism.UG.hform s G x y +
        s b * c * Formalism.UG.hform s G y x + s b * d * Formalism.UG.hform s G y y := by
  simp only [Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, map_add, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Ring

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R]

theorem conj_conj (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [conj_conj σ h]

omit [NumberField F] [NumberField E] in
theorem sigR_alg (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  show r ⊗ₜ[F] σ 1 = r ⊗ₜ[F] 1
  rw [map_one]

omit [NumberField F] [NumberField E] in
theorem hR_rat {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x z : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (z i)) = inclR R (hE σ J x z) := by
  simp [hR, hE, Formalism.UG.hform, sigR, JR, inclR, TensorProduct.tmul_sum]

theorem half_trace (h : IsCMExt F E σ) (k : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (algebraMap R (R ⊗[F] E) k) = k := by
  have h2 : Algebra.trace F E 1 = 2 := by
    have := Algebra.trace_algebraMap (R := F) (S := E) 1
    rw [map_one, h.2.2.1] at this
    rw [this]; norm_num
  have h1 : Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] (1 : E)) = algebraMap F R 2 := by
    rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange,
      ← Algebra.trace_apply, h2]
  rw [Algebra.algebraMap_eq_smul_one k, map_smul, Algebra.TensorProduct.one_def, h1, smul_eq_mul,
    mul_left_comm, ← map_mul, show (1 / 2 * 2 : F) = 1 by norm_num, map_one, mul_one]

omit [NumberField F] [NumberField E] in
theorem JR_cT {M N : ℕ} (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M) (Fin N) E) :
    Formalism.UG.cT (sigR R σ) (B.map (inclR (F := F) R)) * JR (F := F) R J * B.map (inclR (F := F) R) =
      JR (F := F) R (Formalism.UG.cT (σ : E →+* E) B * J * B) := by
  rw [JR, JR, Matrix.map_mul, Matrix.map_mul]
  rfl

end Tens

theorem gram_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → Continuous (gram3 R σ J) ∧ ∃ n : R ⊗[F] E → R, Continuous n ∧ n 0 = 0 ∧ ∀ (g : HA R σ J) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (y' : Fin 1 → Fin M → R ⊗[F] E) (r r' : R) (t : R ⊗[F] E), g • ratTup (F := F) R x = y → gram3 R σ J ![algebraMap R (R ⊗[F] E) r • y 0, t • y 0 + algebraMap R (R ⊗[F] E) r' • pairOf R σ J B y g y' 1] = (r * r * algebraMap F R a, algebraMap R (R ⊗[F] E) (r * algebraMap F R a) * t, n t + r' * r' * qR R σ J' (y' 0)) := by
  intro F E _ _ _ _ _ σ h R _ _ _ _ _ _ _ _ _ M J x a B J' hS
  obtain ⟨hJ, -, hx, hB, hJ', -⟩ := hS
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  have hc : ∀ i j : Fin 2, Continuous fun X : Fin 2 → Fin (M + 1) → R ⊗[F] E =>
      hR R σ J (X i) (X j) := by
    intro i j
    unfold hR Formalism.UG.hform
    fun_prop
  refine ⟨(continuous_const.mul (h1.comp (hc 0 0))).prodMk
    ((hc 0 1).prodMk (continuous_const.mul (h1.comp (hc 1 1)))),
    fun t => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (sigR R σ t * t * algebraMap R (R ⊗[F] E) (algebraMap F R a)),
    continuous_const.mul (h1.comp ((h2.mul continuous_id).mul continuous_const)), by simp, ?_⟩
  intro g y y' r r' t hy
  set G : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) := (HA.mat R σ J g).1 with hG
  have hk : Formalism.UG.cT (sigR R σ) G * JR R J * G = JR R J := (show HR R σ J from g).2
  have hact : ∀ u v, hR R σ J (G *ᵥ u) (G *ᵥ v) = hR R σ J u v := fun u v => by
    rw [hR, hform_mulVec, hk, hR]
  have hy0 : y 0 = G *ᵥ (fun i => inclR R (x 0 i)) := by rw [← hy]; rfl
  set z := pairOf R σ J B y g y' 1 with hz
  have hz0 : z = G *ᵥ (B.map (inclR (F := F) R) *ᵥ y' 0) := rfl
  have e00 : hR R σ J (y 0) (y 0) = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    rw [hy0, hact, hR_rat, hx, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes a
  have e01 : hR R σ J (y 0) z = 0 := by
    rw [hy0, hz0, hact, hR, hform_mulVec_right]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := hR_rat σ R J (x 0) (fun i => B i j)
    rw [hB, map_zero] at this
    exact mul_eq_zero_of_left this _
  have hJs : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  have e10 : hR R σ J z (y 0) = 0 := by
    rw [hR, hform_symm _ _ (sigR_sigR σ R h) hJs, ← hR, e01, map_zero]
  have e11 : hR R σ J z z = hR R σ J' (y' 0) (y' 0) := by
    rw [hz0, hact, hR, hform_mulVec, JR_cT, ← hJ', hR]
  have lin : ∀ p q u v : R ⊗[F] E, hR R σ J (p • y 0 + q • z) (u • y 0 + v • z) =
      sigR R σ p * u * algebraMap R (R ⊗[F] E) (algebraMap F R a) +
        sigR R σ q * v * hR R σ J' (y' 0) (y' 0) := by
    intro p q u v
    rw [hR, hform_lin, ← hR, ← hR, ← hR, ← hR, e00, e01, e10, e11]
    ring
  have f0 : algebraMap R (R ⊗[F] E) r • y 0 =
      algebraMap R (R ⊗[F] E) r • y 0 + (0 : R ⊗[F] E) • z := by simp
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show qR R σ J (algebraMap R (R ⊗[F] E) r • y 0) = r * r * algebraMap F R a
    rw [qR, f0, lin, sigR_alg, mul_zero, zero_mul, add_zero, ← map_mul, ← map_mul, half_trace σ R h]
  · show hR R σ J (algebraMap R (R ⊗[F] E) r • y 0) (t • y 0 + algebraMap R (R ⊗[F] E) r' • z) =
      algebraMap R (R ⊗[F] E) (r * algebraMap F R a) * t
    rw [f0, lin, sigR_alg, map_zero, map_mul]
    ring
  · show qR R σ J (t • y 0 + algebraMap R (R ⊗[F] E) r' • z) =
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (sigR R σ t * t * algebraMap R (R ⊗[F] E) (algebraMap F R a)) + r' * r' * qR R σ J' (y' 0)
    rw [qR, lin, sigR_alg, ← map_mul, ← Algebra.smul_def (r' * r'), map_add, map_smul, qR, smul_eq_mul]
    ring

end GlobalTheory.GaugeEx.GramPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
section
noncomputable section

namespace GlobalTheory.GaugeEx.IntBasis

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem ev_int (a : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F := by
  have h := (algebraMap F (Af F) a).2
  filter_upwards [h] with v hv
  exact hv

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
theorem _root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord {d : ℕ}
    (b : Module.Basis (Fin d) F E) (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (b.repr e k) ∈ v.adicCompletionIntegers F := by
  rw [Filter.eventually_all]
  intro k
  exact RestrictedProduct.eventually _ _ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.repr e k))

theorem eq_sum {d : ℕ} (b : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R]
    (y : R ⊗[F] E) :
    y = ∑ i, (Algebra.TensorProduct.basis R b).repr y i ⊗ₜ[F] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem mem_intV_iff_basis_repr_mem_integers (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) :
    y ∈ _root_.GlobalTheory.GaugeEx.intV b v ↔
      ∀ k, (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).repr y k ∈
        v.adicCompletionIntegers F := by
  unfold _root_.GlobalTheory.GaugeEx.intV
  rfl

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem {r : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v}
    (hr : r ∈ v.adicCompletionIntegers F) {e : E}
    (he : ∀ k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (b.repr e k) ∈ v.adicCompletionIntegers F) :
    r ⊗ₜ[F] e ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers]
  intro k
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
    smul_eq_mul]
  exact mul_mem hr (he k)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' {ι : Type} (s : Finset ι)
    (f : ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) (hf : ∀ i ∈ s, f i ∈ _root_.GlobalTheory.GaugeEx.intV b v) :
    ∑ i ∈ s, f i ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers]
  intro k
  rw [map_sum, Finsupp.finset_sum_apply]
  exact sum_mem fun i hi => (mem_intV_iff_basis_repr_mem_integers b v (f i)).1 (hf i hi) k

theorem compact_open : IsCompact (intV b v) ∧ IsOpen (intV b v) := by
  let l := (Algebra.TensorProduct.basis (Fv F v) b).equivFun
  have h1 : Continuous l := IsModuleTopology.continuous_of_linearMap l.toLinearMap
  have h2 : Continuous l.symm := by
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
    exact IsModuleTopology.continuous_of_linearMap l.symm.toLinearMap
  let e : (Fv F v ⊗[F] E) ≃ₜ (Fin d → Fv F v) := ⟨l.toEquiv, h1, h2⟩
  have he : intV b v = e ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
    rfl
  have ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
    exact isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  rw [he]
  exact ⟨e.isCompact_preimage.2 (isCompact_univ_pi fun _ => hc),
    (isOpen_set_pi Set.finite_univ fun _ _ => ho).preimage e.continuous⟩

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem eventually_basis_repr_mem_adicCompletionIntegers {ι : Type} [Finite ι] (e : ι → E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w) (b.repr (e i) k) ∈ w.adicCompletionIntegers F :=
  Filter.eventually_all.2 fun i => _root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord b (e i)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem eq_sum_basis_repr_tmul_basis (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) :
    y = ∑ k, (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).repr y k ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).sum_repr y]
  simp only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem zero_mem_intV : (0 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers]
  intro k
  rw [map_zero, Finsupp.zero_apply]
  exact zero_mem _

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem add_mem_intV {y z : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E}
    (hy : y ∈ _root_.GlobalTheory.GaugeEx.intV b v) (hz : z ∈ _root_.GlobalTheory.GaugeEx.intV b v) :
    y + z ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers] at hy hz ⊢
  intro k
  rw [map_add, Finsupp.add_apply]
  exact add_mem (hy k) (hz k)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem intV_subset_intV_of_basis_repr_integral {d' : ℕ} (b' : Module.Basis (Fin d') F E)
    (h : ∀ i k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (b'.repr (b i) k) ∈ v.adicCompletionIntegers F) :
    _root_.GlobalTheory.GaugeEx.intV b v ⊆ _root_.GlobalTheory.GaugeEx.intV b' v := by
  intro y hy
  rw [eq_sum_basis_repr_tmul_basis b v y]
  exact _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b' v _ _ fun i _ =>
    _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b' v
      ((mem_intV_iff_basis_repr_mem_integers b v y).1 hy i) (h i)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.GaugeEx.IntBasis.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ v : HeightOneSpectrum (𝓞 F), IsCompact (_root_.GlobalTheory.GaugeEx.intV b v) ∧ IsOpen (_root_.GlobalTheory.GaugeEx.intV b v)) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) ∈ _root_.GlobalTheory.GaugeEx.intV b v ∧ (∀ y ∈ _root_.GlobalTheory.GaugeEx.intV b v, ∀ z ∈ _root_.GlobalTheory.GaugeEx.intV b v, y * z ∈ _root_.GlobalTheory.GaugeEx.intV b v) ∧ ∀ y ∈ _root_.GlobalTheory.GaugeEx.intV b v, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ y ∈ _root_.GlobalTheory.GaugeEx.intV b v) ∧ (∀ z : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, _root_.GlobalTheory.GaugeEx.prV v z ∈ _root_.GlobalTheory.GaugeEx.intV b v) ∧ ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, _root_.GlobalTheory.GaugeEx.intV b v = _root_.GlobalTheory.GaugeEx.intV b' v := by
  intro F E _ _ _ _ _ σ d b
  refine ⟨fun v => ?_, ?_, fun z => ?_, fun d' b' => ?_⟩
  · let φ := (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).equivFun
    have hφ : Continuous φ := IsModuleTopology.continuous_of_linearMap φ.toLinearMap
    have hφs : Continuous φ.symm := IsModuleTopology.continuous_of_linearMap φ.symm.toLinearMap
    let h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E ≃ₜ (Fin d → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :=
      { φ.toEquiv with continuous_toFun := hφ, continuous_invFun := hφs }
    have hS : _root_.GlobalTheory.GaugeEx.intV b v =
        h ⁻¹' Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))) := by
      ext y
      rw [mem_intV_iff_basis_repr_mem_integers]
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      rfl
    have hO : IsCompact (v.adicCompletionIntegers F : Set (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) :=
      isCompact_iff_compactSpace.mpr (_root_.GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
    rw [hS]
    exact ⟨h.isCompact_preimage.2 (isCompact_univ_pi fun _ => hO),
      (isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_integer _).preimage h.continuous⟩
  · filter_upwards [_root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord b (1 : E),
      eventually_basis_repr_mem_adicCompletionIntegers b (fun p : Fin d × Fin d => b p.1 * b p.2),
      eventually_basis_repr_mem_adicCompletionIntegers b (fun k => σ (b k))] with v hv1 hv2 hv3
    refine ⟨?_, ?_, ?_⟩
    · rw [Algebra.TensorProduct.one_def]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v (one_mem _) hv1
    · intro y hy z hz
      rw [eq_sum_basis_repr_tmul_basis b v y, eq_sum_basis_repr_tmul_basis b v z, Finset.sum_mul_sum]
      refine _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun k _ =>
        _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun l _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v
        (mul_mem ((mem_intV_iff_basis_repr_mem_integers b v y).1 hy k)
          ((mem_intV_iff_basis_repr_mem_integers b v z).1 hz l)) (hv2 (k, l))
    · intro y hy
      rw [eq_sum_basis_repr_tmul_basis b v y, map_sum]
      refine _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun k _ => ?_
      simp only [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v
        ((mem_intV_iff_basis_repr_mem_integers b v y).1 hy k) (hv3 k)
  · induction z using TensorProduct.induction_on with
    | zero =>
      exact Filter.Eventually.of_forall fun v => by
        rw [map_zero]
        exact zero_mem_intV b v
    | tmul a e =>
      filter_upwards [RestrictedProduct.eventually _ _ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F a),
        _root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord b e] with v ha he
      simp only [_root_.GlobalTheory.GaugeEx.prV, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v ha he
    | add x y hx hy =>
      filter_upwards [hx, hy] with v hxv hyv
      rw [map_add]
      exact add_mem_intV b v hxv hyv
  · filter_upwards [eventually_basis_repr_mem_adicCompletionIntegers b' (fun k => b k),
      eventually_basis_repr_mem_adicCompletionIntegers b (fun k => b' k)] with v h h'
    exact Set.Subset.antisymm (intV_subset_intV_of_basis_repr_integral b v b' h)
      (intV_subset_intV_of_basis_repr_integral b' v b h')

end GlobalTheory.GaugeEx.IntBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDvdOfAdicValuationLtOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelUnif

open GlobalTheory.LevelHecke

theorem le_exp_sub_one {x : WithZero (Multiplicative ℤ)} {n : ℤ} (h : x < WithZero.exp n) :
    x ≤ WithZero.exp (n - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  rw [← WithZero.exp_log hx] at h ⊢
  rw [WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem T_notMem_sq (D : D7) (u : D.what₂.Word) (A : Formalism.L2.Forms.AtTTied u)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 := by
  set v0 := A.eV.symm ⟨v, hv⟩ with hv0
  have hU := GlobalTheory.LevelUnram.unram D u A v0
  set P := RingHom.ker (A.res v0) with hP
  haveI hPp : P.IsPrime := RingHom.ker_isPrime _
  have hvP : ∀ x, x ∈ v.asIdeal → algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P := by
    intro x hx
    have h := (A.res_v v0 x).1 (by rw [hv0, Equiv.apply_symm_apply]; exact hx)
    exact h
  have hTP : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ P := hU.1
  have hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hPbot : P ≠ ⊥ := fun h => hT0 (by rw [h] at hTP; exact (Ideal.mem_bot).1 hTP)
  have hlt : P ^ 2 < P ^ 1 := Ideal.pow_right_strictAnti P hPbot hPp.ne_top (by norm_num)
  rw [pow_one] at hlt
  obtain ⟨a, haP, ha2⟩ := SetLike.exists_of_lt hlt
  have hTE : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ P ^ 2 := by
    intro hT2
    obtain ⟨s, b, hs, hsab⟩ := hU.2 a haP
    have h1 : s * a ∈ P ^ 2 := by rw [hsab]; exact Ideal.mul_mem_right _ _ hT2
    rcases Ideal.IsPrime.mul_mem_pow P h1 with h | h
    · exact hs h
    · exact ha2 h
  intro hv2
  apply hTE
  have hle : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal ≤ P :=
    Ideal.map_le_iff_le_comap.2 (fun x hx => hvP x hx)
  have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hv2
  rw [Ideal.map_pow] at h3
  have h4 := Ideal.pow_right_mono hle 2 h3
  simpa using h4

theorem dvd_of_val_lt_one : ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (A : Formalism.L2.Forms.AtTTied u)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (_ : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal)
    (a : v.adicCompletionIntegers D.host.F) (_ : Valued.v (a : v.adicCompletion D.host.F) < 1),
    ∃ b : v.adicCompletionIntegers D.host.F, a = (((D.mem u).A.T : ℕ) : v.adicCompletionIntegers D.host.F) * b := by
  intro D u A v hv a ha
  have hT2 := T_notMem_sq D u A v hv
  have hval : v.intValuation (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) = WithZero.exp (-1) := by
    apply le_antisymm
    · have h := (v.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hv)
      simpa using h
    · by_contra h
      push_neg at h
      have h2 := le_exp_sub_one h
      norm_num at h2
      exact hT2 ((v.intValuation_le_pow_iff_mem _ 2).1 (by simpa using h2))
  have hTv : Valued.v ((((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F)) = WithZero.exp (-1) := by
    have h := v.valuedAdicCompletion_eq_valuation (K := D.host.F) (((D.mem u).A.T : ℕ) : 𝓞 D.host.F)
    rw [HeightOneSpectrum.valuation_of_algebraMap, hval] at h
    simpa using h
  have hc0 : ((((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F)) ≠ 0 := by
    intro h; rw [h, map_zero] at hTv; exact WithZero.zero_ne_coe hTv
  have hale : Valued.v (a : v.adicCompletion D.host.F) ≤ WithZero.exp (-1) := by
    have h := le_exp_sub_one (n := 0) (by simpa using ha)
    simpa using h
  set c : v.adicCompletion D.host.F := (((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F) with hc
  have hb : (a : v.adicCompletion D.host.F) / c ∈ v.adicCompletionIntegers D.host.F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hTv]
    rw [div_le_one₀ (by simp)]
    exact hale
  refine ⟨⟨_, hb⟩, Subtype.ext ?_⟩
  push_cast
  rw [← hc, mul_div_cancel₀ _ hc0]

end GlobalTheory.LevelUnif

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharEqOfTameRepCongrStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameChar_eq_of_tameRep_congr : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)), ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → 0 < normV P - 1 → ((normV P - 1 : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (normV P - 1) = 1) → ∀ (σ σ' : G E Ω) (u u' : 𝓞 E), NX.TameRep P 1 σ u → NX.TameRep P 1 σ' u' → u - u' ∈ P.asIdeal → χ σ = χ σ' := by
  first | exact @GlobalTheory.TameTau.char_eq_of_tameRep_congr | exact GlobalTheory.TameTau.char_eq_of_tameRep_congr | (intros; apply GlobalTheory.TameTau.char_eq_of_tameRep_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorMemAdelicFormsStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upwardOperator_mem_adelicForms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E) (lam : ι → DomWeight n), ∀ g ∈ AdForms S emb lam, upAd res t v p g ∈ AdForms S emb lam := by
  first | exact @GlobalTheory.LevelHecke.UpKeeps.upAd_mem_adForms | exact GlobalTheory.LevelHecke.UpKeeps.upAd_mem_adForms | (intros; apply GlobalTheory.LevelHecke.UpKeeps.upAd_mem_adForms <;> assumption)
end

