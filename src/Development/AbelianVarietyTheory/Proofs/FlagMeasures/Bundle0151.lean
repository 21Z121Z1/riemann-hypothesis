import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0134
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.RealPlaceAnalysis.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0136

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefExtendsHolomorphically
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.KHolExt

variable {n : ℕ} {ε : Fin n → Bool}

def Hol (ε : Fin n → Bool) (a : KG ε → ℂ) : Prop :=
  ∃ F : (Fin n → Fin n → ℂ) → ℂ, DifferentiableOn ℂ F {y | Matrix.of y ∈ KC ε} ∧
    ∀ k : KG ε, F (fun i j => toMK k i j) = a k

lemma Hol.const (c : ℂ) : Hol ε (fun _ => c) :=
  ⟨fun _ => c, differentiableOn_const c, fun _ => rfl⟩

lemma Hol.add {a b : KG ε → ℂ} (ha : Hol ε a) (hb : Hol ε b) : Hol ε (fun k => a k + b k) := by
  obtain ⟨F, hF, hFa⟩ := ha
  obtain ⟨G, hG, hGb⟩ := hb
  refine ⟨fun y => F y + G y, hF.add hG, fun k => ?_⟩
  simp only [hFa, hGb]

lemma Hol.mul {a b : KG ε → ℂ} (ha : Hol ε a) (hb : Hol ε b) : Hol ε (fun k => a k * b k) := by
  obtain ⟨F, hF, hFa⟩ := ha
  obtain ⟨G, hG, hGb⟩ := hb
  refine ⟨fun y => F y * G y, hF.mul hG, fun k => ?_⟩
  simp only [hFa, hGb]

lemma Hol.sum {ι : Type} (s : Finset ι) {a : ι → KG ε → ℂ} (ha : ∀ i, Hol ε (a i)) :
    Hol ε (fun k => ∑ i ∈ s, a i k) := by
  choose F hF hFa using ha
  refine ⟨fun y => ∑ i ∈ s, F i y, ?_, fun k => ?_⟩
  · have hs := DifferentiableOn.sum (𝕜 := ℂ) (u := s) (fun i _ => hF i)
    have e : (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, F i := by
      funext y
      rw [Finset.sum_apply]
    rw [e]
    exact hs
  simp only [hFa]

lemma Hol.entry (i j : Fin n) : Hol ε (fun k => toMK k i j) := by
  refine ⟨fun y => y i j, ?_, fun k => rfl⟩
  have hd : Differentiable ℂ (fun y : Fin n → Fin n → ℂ => y i j) := by fun_prop
  exact hd.differentiableOn

lemma differentiable_det (f : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (hf : ∀ i j, Differentiable ℂ (fun y => f y i j)) : Differentiable ℂ (fun y => (f y).det) := by
  simp only [Matrix.det_apply']
  have hp : ∀ σ : Equiv.Perm (Fin n), Differentiable ℂ (fun y => ∏ i, f y (σ i) i) := fun σ => by
    have h : Differentiable ℂ (∏ i, (fun y : Fin n → Fin n → ℂ => f y (σ i) i)) :=
      Finset.prod_induction (fun i => (fun y : Fin n → Fin n → ℂ => f y (σ i) i))
        (fun g => Differentiable ℂ g) (fun a b ha hb => ha.mul hb) (differentiable_const 1)
        (fun i _ => hf (σ i) i)
    have e : (fun y => ∏ i, f y (σ i) i) = ∏ i, (fun y => f y (σ i) i) := by
      funext y
      rw [Finset.prod_apply]
    rw [e]
    exact h
  have hs := Differentiable.sum (𝕜 := ℂ) (u := Finset.univ)
    (A := fun (σ : Equiv.Perm (Fin n)) (y : Fin n → Fin n → ℂ) => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i)
    (fun σ _ => (differentiable_const (((Equiv.Perm.sign σ : ℤ) : ℂ))).mul (hp σ))
  have e : (fun y => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i) =
      ∑ σ : Equiv.Perm (Fin n), (fun y => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i) := by
    funext y
    rw [Finset.sum_apply]
  rw [e]
  exact hs

lemma toMK_inv (k : KG ε) : toMK k⁻¹ = star (toMK k) := by
  have hu : toMK k * star (toMK k) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 ((mem_KG ε (k : UJ ε)).1 k.2).1
  have hl : toMK k⁻¹ * toMK k = 1 := Units.inv_mul ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  calc toMK k⁻¹ = toMK k⁻¹ * (toMK k * star (toMK k)) := by rw [hu, mul_one]
    _ = star (toMK k) := by rw [← mul_assoc, hl, one_mul]

lemma toMK_mul (g k : KG ε) : toMK (g * k) = toMK g * toMK k := rfl

lemma Hol.conjEntry (i j : Fin n) : Hol ε (fun k => star (toMK k i j)) := by
  refine ⟨fun y => ((Matrix.of y).det)⁻¹ * (Matrix.of y).adjugate j i, ?_, fun k => ?_⟩
  · have hdet : Differentiable ℂ (fun y : Fin n → Fin n → ℂ => (Matrix.of y).det) :=
      differentiable_det (fun y => Matrix.of y) (fun a b => by simp only [Matrix.of_apply]; fun_prop)
    have hadj : Differentiable ℂ (fun y : Fin n → Fin n → ℂ => (Matrix.of y).adjugate j i) := by
      simp only [Matrix.adjugate_apply]
      exact differentiable_det _ (fun a b => by
        simp only [Matrix.updateRow_apply, Matrix.of_apply]
        split_ifs <;> fun_prop)
    intro y hy
    have hy1 : IsUnit (Matrix.of y) := by
      simp only [Set.mem_setOf_eq, KC] at hy
      exact hy.1
    have hne : (Matrix.of y).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hy1).ne_zero
    exact ((hdet y).inv hne).differentiableWithinAt.mul (hadj y).differentiableWithinAt
  · have hu : toMK k * star (toMK k) = 1 :=
      Matrix.mem_unitaryGroup_iff.1 ((mem_KG ε (k : UJ ε)).1 k.2).1
    have hinv : (toMK k)⁻¹ = star (toMK k) := Matrix.inv_eq_right_inv hu
    have key : (toMK k)⁻¹ j i = ((toMK k).det)⁻¹ * (toMK k).adjugate j i := by
      rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
    change ((toMK k).det)⁻¹ * (toMK k).adjugate j i = star (toMK k i j)
    rw [← key, hinv, Matrix.star_apply]

def Sep (ε : Fin n → Bool) (p : KG ε → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → KG ε → ℂ) (b : ι → C(KG ε, ℂ)), (∀ i, Hol ε (a i)) ∧
    ∀ g k, p (g⁻¹ * k) = ∑ i, a i g * b i k

lemma Sep.const (c : ℂ) : Sep ε (fun _ => c) :=
  ⟨Unit, inferInstance, fun _ _ => c, fun _ => ContinuousMap.const _ 1, fun _ => Hol.const c,
    fun g k => by simp⟩

lemma Sep.add {p q : KG ε → ℂ} (hp : Sep ε p) (hq : Sep ε q) : Sep ε (fun k => p k + q k) := by
  obtain ⟨ι, _, a, b, ha, hab⟩ := hp
  obtain ⟨κ, _, c, d, hc, hcd⟩ := hq
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim a c, Sum.elim b d, ?_, fun g k => ?_⟩
  · rintro (i | i)
    · exact ha i
    · exact hc i
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hab, hcd]

lemma Sep.mul {p q : KG ε → ℂ} (hp : Sep ε p) (hq : Sep ε q) : Sep ε (fun k => p k * q k) := by
  obtain ⟨ι, _, a, b, ha, hab⟩ := hp
  obtain ⟨κ, _, c, d, hc, hcd⟩ := hq
  refine ⟨ι × κ, inferInstance, fun x g => a x.1 g * c x.2 g, fun x => b x.1 * d x.2,
    fun x => (ha x.1).mul (hc x.2), fun g k => ?_⟩
  show p (g⁻¹ * k) * q (g⁻¹ * k) = _
  rw [hab, hcd, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ContinuousMap.mul_apply]
  ring

lemma isEmb (ε : Fin n → Bool) : Topology.IsEmbedding (fun k : KG ε => toMK k) := by
  have hc : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hi : Function.Injective (fun k : KG ε => toMK k) := fun a b h =>
    Subtype.ext (Subtype.ext (Units.ext h))
  exact (hc.isClosedEmbedding hi).isEmbedding

def ent (ε : Fin n → Bool) (i j : Fin n) : C(KG ε, ℂ) :=
  ⟨fun k => toMK k i j, (continuous_apply_apply i j).comp (isEmb ε).continuous⟩

lemma Sep.entry (i j : Fin n) : Sep ε (ent ε i j) := by
  refine ⟨Fin n, inferInstance, fun l g => star (toMK g l i), fun l => ent ε l j,
    fun l => Hol.conjEntry l i, fun g k => ?_⟩
  show toMK (g⁻¹ * k) i j = ∑ l, star (toMK g l i) * toMK k l j
  rw [toMK_mul, toMK_inv, Matrix.mul_apply]
  simp only [Matrix.star_apply]

lemma Sep.conjEntry (i j : Fin n) : Sep ε (star (ent ε i j) : C(KG ε, ℂ)) := by
  refine ⟨Fin n, inferInstance, fun l g => toMK g l i, fun l => star (ent ε l j),
    fun l => Hol.entry l i, fun g k => ?_⟩
  show star (toMK (g⁻¹ * k) i j) = ∑ l, toMK g l i * star (toMK k l j)
  rw [toMK_mul, toMK_inv, Matrix.mul_apply, star_sum]
  simp only [Matrix.star_apply, star_mul', star_star]

def sepAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) where
  carrier := {p | Sep ε p ∧ Sep ε (star p : C(KG ε, ℂ))}
  mul_mem' := fun {p q} hp hq => ⟨hp.1.mul hq.1, by
    rw [star_mul']; exact hp.2.mul hq.2⟩
  add_mem' := fun {p q} hp hq => ⟨hp.1.add hq.1, by
    rw [star_add]; exact hp.2.add hq.2⟩
  algebraMap_mem' := fun c => ⟨by
    have : ((algebraMap ℂ C(KG ε, ℂ) c : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => c := by
      funext k; simp
    rw [this]; exact Sep.const c, by
    have : ((star (algebraMap ℂ C(KG ε, ℂ) c) : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => star c := by
      funext k; simp
    rw [this]; exact Sep.const _⟩
  star_mem' := fun {p} hp => ⟨hp.2, by rw [star_star]; exact hp.1⟩

lemma sepAlg_dense (ε : Fin n → Bool) : (sepAlg ε).topologicalClosure = ⊤ := by
  refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
  intro x y hxy
  have hne : toMK x ≠ toMK y := fun h => hxy ((isEmb ε).injective h)
  obtain ⟨i, j, hij⟩ : ∃ i j, toMK x i j ≠ toMK y i j := by
    by_contra hcon
    push_neg at hcon
    exact hne (Matrix.ext hcon)
  have hmem : ent ε i j ∈ sepAlg ε := ⟨Sep.entry i j, Sep.conjEntry i j⟩
  exact ⟨_, ⟨ent ε i j, hmem, rfl⟩, hij⟩

private theorem integrable_of_continuous_isFiniteMeasure {E : Type*} [NormedAddCommGroup E] {f : KG ε → E} (hf : Continuous f) :
    Integrable f (muK ε) :=
  hf.integrable_of_hasCompactSupport (isClosed_tsupport f).isCompact

lemma eq_zero_of_orth (φ : C(KG ε, ℂ))
    (h : ∀ p : C(KG ε, ℂ), Sep ε p → ∫ k, p k * φ k ∂(muK ε) = 0) : φ = 0 := by
  let L : C(KG ε, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun p => ∫ k, p k * φ k ∂(muK ε)
      map_add' := fun p q => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (integrable_of_continuous_isFiniteMeasure (p.continuous.mul φ.continuous))
          (integrable_of_continuous_isFiniteMeasure (q.continuous.mul φ.continuous))
      map_smul' := fun c p => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
  have hL : Continuous L := by
    refine AddMonoidHomClass.continuous_of_bound L (∫ k, ‖φ k‖ ∂(muK ε)) fun p => ?_
    calc ‖L p‖ = ‖∫ k, p k * φ k ∂(muK ε)‖ := rfl
      _ ≤ ∫ k, ‖p‖ * ‖φ k‖ ∂(muK ε) := by
          refine norm_integral_le_of_norm_le ((integrable_of_continuous_isFiniteMeasure φ.continuous).norm.const_mul _) ?_
          refine Filter.Eventually.of_forall fun k => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (p.norm_coe_le_norm k) (norm_nonneg _)
      _ = (∫ k, ‖φ k‖ ∂(muK ε)) * ‖p‖ := by rw [integral_const_mul, mul_comm]
  have hcl : IsClosed {p : C(KG ε, ℂ) | L p = 0} := isClosed_eq hL continuous_const
  have hsub : ((sepAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) ⊆ {p | L p = 0} := by
    intro p hp
    exact h p hp.1
  have hall : ∀ p : C(KG ε, ℂ), L p = 0 := by
    intro p
    have hp : p ∈ closure ((sepAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) := by
      rw [← StarSubalgebra.topologicalClosure_coe, SetLike.mem_coe, sepAlg_dense]
      exact StarSubalgebra.mem_top
    exact closure_minimal hsub hcl hp
  have h1 : ∫ k, (star φ) k * φ k ∂(muK ε) = 0 := hall (star φ)
  have e : ∀ k, (star φ) k * φ k = ((‖φ k‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [ContinuousMap.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  simp only [e, integral_ofReal] at h1
  have hreal : ∫ k, ‖φ k‖ ^ 2 ∂(muK ε) = 0 := by exact_mod_cast h1
  have hae : (fun k => ‖φ k‖ ^ 2) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg ‖φ k‖)
      (integrable_of_continuous_isFiniteMeasure (φ.continuous.norm.pow 2))).1 hreal
  have heq : (fun k => ‖φ k‖ ^ 2) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) (φ.continuous.norm.pow 2) continuous_const).1 hae
  ext k
  have hk := congrFun heq k
  simpa using hk

end GlobalTheory.KHolExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeffEqZeroOfLipschitzUnitaryFlowDecay
section
open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.LipFlow

theorem herm {V : Type} [AddCommGroup V] [Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (h : ∀ x, 0 ≤ I x x) (x y : V) : (starRingEnd ℂ) (I y x) = I x y := by
  have him : ∀ x, (I x x).im = 0 := fun x => ((Complex.le_def.1 (h x)).2).symm
  have h1 := him (x + y)
  have h2 := him (x + Complex.I • y)
  have hx := him x
  have hy := him y
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply, Complex.conj_I, Complex.add_im, Complex.add_re, Complex.mul_im,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im] at h1 h2
  apply Complex.ext
  · simp only [Complex.conj_re]; linarith
  · simp only [Complex.conj_im]; linarith

theorem cauchy {V : Type} [AddCommGroup V] [Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (h : ∀ x, 0 ≤ I x x) (x y : V) : ‖I x y‖ ^ 2 ≤ (I x x).re * (I y y).re := by
  first
  | exact @_root_.GlobalTheory.HermitianCauchySchwarz.main
  | exact _root_.GlobalTheory.HermitianCauchySchwarz.main
  | (apply _root_.GlobalTheory.HermitianCauchySchwarz.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianCauchySchwarz.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianCauchySchwarz.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianCauchySchwarz.main ..)

theorem integrable_exp_abs {e : ℝ} (he : 0 < e) :
    Integrable (fun s : ℝ => Real.exp (-(e * |s|))) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0:ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic he 0).congr_fun (fun x hx => ?_) measurableSet_Iic
    simp only [abs_of_nonpos (Set.mem_Iic.1 hx)]
    congr 1; ring
  · refine (exp_neg_integrableOn_Ioi 0 he).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [abs_of_pos (Set.mem_Ioi.1 hx)]
    congr 1; ring

theorem decay_shift {φ : ℝ → ℂ} {A e : ℝ} (he : 0 < e)
    (h : ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) (r t : ℝ) :
    ‖φ (r + t)‖ ≤ A * Real.exp (e * |r|) * Real.exp (-(e * |t|)) := by
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (h 0)
    simpa using this
  refine (h _).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  gcongr
  have : |t| ≤ |r| + |r + t| := by
    have := abs_sub (r + t) r
    simp only [add_sub_cancel_left] at this
    linarith
  nlinarith

theorem integrable_fourier {φ : ℝ → ℂ} (hc : Continuous φ) {A e : ℝ} (he : 0 < e)
    (h : ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) (ξ : ℝ) :
    Integrable (fun s : ℝ => Complex.exp (-(Complex.I * ξ * s)) * φ s) := by
  refine ((integrable_exp_abs he).const_mul A).mono' (by fun_prop) (ae_of_all _ fun s => ?_)
  rw [norm_mul, Complex.norm_exp]
  simpa using h s

theorem fourier_shift (φ : ℝ → ℂ) (ξ r : ℝ) :
    ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ (r + s)
      = Complex.exp (Complex.I * ξ * r) * ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s := by
  rw [← integral_const_mul,
    ← integral_add_left_eq_self (fun s : ℝ => Complex.exp (Complex.I * ξ * r) *
      (Complex.exp (-(Complex.I * ξ * s)) * φ s)) r]
  congr 1; funext s
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem coeff_eq_zero : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (U : ℝ → V →ₗ[ℂ] V) (C : ℝ) (v : V), (∀ x, 0 ≤ I x x) → U 0 = LinearMap.id → (∀ s t, U (s + t) = (U s).comp (U t)) → (∀ s x y, I (U s x) (U s y) = I x y) → (∀ s x, |s| ≤ 1 → (I (U s x - x) (U s x - x)).re ≤ C * s ^ 2 * (I x x).re) → (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖I v (U s v)‖ ≤ A * Real.exp (-(e * |s|))) → I v v = 0 := by
  intro V _ _ I U C v hpos h0 hadd hiso hlip ⟨A, e, he, hdec⟩
  set φ : ℝ → ℂ := fun s => I v (U s v) with hφ
  have hU : ∀ s t x, U s (U t x) = U (s + t) x := fun s t x => by rw [hadd]; rfl
  have hre : ∀ x, 0 ≤ (I x x).re := fun x => (Complex.le_def.1 (hpos x)).1
  have him : ∀ x, (I x x).im = 0 := fun x => ((Complex.le_def.1 (hpos x)).2).symm
  have hcont : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro t
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ᶠ u in nhds t, ‖φ u - φ t‖ ≤
        Real.sqrt ((I v v).re * (C * (u - t) ^ 2 * (I v v).re)) := by
      filter_upwards [Metric.closedBall_mem_nhds t one_pos] with u hu
      have hu' : |u - t| ≤ 1 := by simpa [Real.dist_eq] using hu
      apply Real.le_sqrt_of_sq_le
      have e1 : φ u - φ t = I v (U (u - t) (U t v) - U t v) := by
        simp [hφ, hU]
      rw [e1]
      refine (cauchy I hpos _ _).trans ?_
      have := hlip (u - t) (U t v) hu'
      rw [hiso] at this
      exact mul_le_mul_of_nonneg_left this (hre v)
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hb ?_
    have : Continuous fun u : ℝ => Real.sqrt ((I v v).re * (C * (u - t) ^ 2 * (I v v).re)) := by
      fun_prop
    simpa using this.tendsto t
  have hsum : ∀ (k : ℕ) (t : Fin k → ℝ) (z : Fin k → ℂ) (r : ℝ),
      I (∑ i, z i • U (t i) v) (U r (∑ i, z i • U (t i) v))
        = ∑ i, ∑ j, star (z i) * z j * φ (r + (t j - t i)) := by
    intro k t z r
    rw [map_sum (U r), map_sum I, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : I (U (t i) v) (U r (U (t j) v)) = φ (r + (t j - t i)) := by
      simp only [hφ]
      rw [← hiso (t i) v (U (r + (t j - t i)) v), hU, hU]
      congr 3; ring
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, this]
    simp only [RCLike.star_def]
    ring
  have hφpos := GlobalTheory.PosDefFT.fourier_nonneg φ hcont ⟨A, e, he, hdec⟩ (fun k t z => by
    have := hsum k t z 0
    simp only [h0, LinearMap.id_apply, zero_add] at this
    rw [← this]; exact hpos _)
  have hzero : φ = 0 := by
    refine GlobalTheory.eq_zero_of_exp_decay_of_fourier_eq_zero_on_halfLine φ (Real.pi * (|C| + 1)) hcont ⟨A, e, he, hdec⟩ fun ξ hξ => ?_
    have hC : 0 ≤ |C| := abs_nonneg C
    have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξ
    set s : ℝ := Real.pi / ξ with hs
    have hs0 : 0 < s := by positivity
    have hs1 : s * (|C| + 1) ≤ 1 := by
      rw [hs, div_mul_eq_mul_div, div_le_one hξ0]; exact hξ
    have hs2 : s ≤ 1 := by nlinarith
    have hCs : C * s ^ 2 ≤ 1 := by
      have := le_abs_self C
      nlinarith [mul_nonneg hC hs0.le]
    let ψ : ℝ → ℂ := fun t => ((C * s ^ 2 - 2 : ℝ) : ℂ) * φ t + φ (s + t) + φ (-s + t)
    have hψc : Continuous ψ := by fun_prop
    have hψd : ∀ t, ‖ψ t‖ ≤ (|C * s ^ 2 - 2| * A + A * Real.exp (e * |s|)
        + A * Real.exp (e * |-s|)) * Real.exp (-(e * |t|)) := by
      intro t
      have a1 := decay_shift he hdec s t
      have a2 := decay_shift he hdec (-s) t
      have a3 : ‖((C * s ^ 2 - 2 : ℝ) : ℂ) * φ t‖
          ≤ |C * s ^ 2 - 2| * (A * Real.exp (-(e * |t|))) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hdec t) (abs_nonneg _)
      refine (norm_add₃_le).trans ?_
      refine (add_le_add (add_le_add a3 a1) a2).trans (le_of_eq (by ring))
    have hψpos := GlobalTheory.PosDefFT.fourier_nonneg ψ hψc ⟨_, e, he, hψd⟩ (fun k t z => by
      set x := ∑ i, z i • U (t i) v with hx
      have b0 := hsum k t z 0
      have b1 := hsum k t z s
      have b2 := hsum k t z (-s)
      rw [← hx] at b0 b1 b2
      simp only [h0, LinearMap.id_apply, zero_add] at b0
      have b3 : I (U s x) x = I x (U (-s) x) := by
        rw [← hiso s x (U (-s) x), hU]; simp [h0]
      have b4 : ∑ i, ∑ j, star (z i) * z j * ψ (t j - t i)
          = ((C * s ^ 2 - 2 : ℝ) : ℂ) * I x x + I x (U s x) + I x (U (-s) x) := by
        rw [b0, b1, b2]
        simp only [ψ, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have b5 : ((C * s ^ 2 - 2 : ℝ) : ℂ) * I x x + I x (U s x) + I x (U (-s) x)
          = ((C * s ^ 2 : ℝ) : ℂ) * I x x - I (U s x - x) (U s x - x) := by
        simp only [map_sub, LinearMap.sub_apply, hiso, b3]
        push_cast; ring
      rw [b4, b5, Complex.le_def]
      have := hlip s x (by rwa [abs_of_pos hs0])
      constructor
      · rw [Complex.sub_re, Complex.re_ofReal_mul]; simpa using this
      · rw [Complex.sub_im, Complex.im_ofReal_mul, him, him]; simp) ξ
    have i0 := integrable_fourier hcont he hdec ξ
    have i1 := integrable_fourier (φ := fun t => φ (s + t)) (by fun_prop) he
      (decay_shift he hdec s) ξ
    have i2 := integrable_fourier (φ := fun t => φ (-s + t)) (by fun_prop) he
      (decay_shift he hdec (-s)) ξ
    have hξs : Complex.I * ξ * s = Real.pi * Complex.I := by
      have : (ξ : ℂ) * s = Real.pi := by
        rw [← Complex.ofReal_mul, hs, mul_div_cancel₀ _ hξ0.ne']
      rw [← this]; ring
    have hF : ∫ t : ℝ, Complex.exp (-(Complex.I * ξ * t)) * ψ t
        = ((C * s ^ 2 - 4 : ℝ) : ℂ) * ∫ t : ℝ, Complex.exp (-(Complex.I * ξ * t)) * φ t := by
      have : (fun t : ℝ => Complex.exp (-(Complex.I * ξ * t)) * ψ t) = fun t : ℝ =>
          ((C * s ^ 2 - 2 : ℝ) : ℂ) * (Complex.exp (-(Complex.I * ξ * t)) * φ t)
          + Complex.exp (-(Complex.I * ξ * t)) * φ (s + t)
          + Complex.exp (-(Complex.I * ξ * t)) * φ (-s + t) := by
        funext t; simp only [ψ]; ring
      rw [this, integral_add (by exact (i0.const_mul _).add i1) i2, integral_add (i0.const_mul _) i1,
        integral_const_mul, fourier_shift, fourier_shift, hξs]
      have h2 : Complex.I * ξ * ((-s : ℝ) : ℂ) = -(Real.pi * Complex.I) := by
        rw [← hξs]; push_cast; ring
      rw [h2, Complex.exp_neg, Complex.exp_pi_mul_I]
      push_cast; ring
    rw [hF] at hψpos
    have p0 := hφpos ξ
    set F := ∫ t : ℝ, Complex.exp (-(Complex.I * ξ * t)) * φ t
    obtain ⟨p1, p2⟩ := Complex.le_def.1 p0
    have p3 := (Complex.le_def.1 hψpos).1
    rw [Complex.re_ofReal_mul] at p3
    simp only [Complex.zero_re, Complex.zero_im] at p1 p2 p3
    apply Complex.ext
    · simp only [Complex.zero_re]; nlinarith
    · simp [← p2]
  have := congrFun hzero 0
  simpa [hφ, h0] using this

end GlobalTheory.LipFlow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexSpanAtRealPlaceAutPointLatticePropertiesStatement
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), (∀ v, spanAt I R v = Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (Submodule.span I.E (R : Set (Fin I.n → I.E)) : Set (Fin I.n → I.E)))) ∧ (∀ v, spanAt I (lamX I x) v = ⊤) ∧ (∀ v, (spanAt I (perpIn I x R) v : Set (Fin I.n → ℂ)) = perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v)) ∧ (∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ nilReal I R) ∧ ∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InCen (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ cenReal I R := by
  first | exact @GlobalTheory.RealSpan.spanAt_properties | exact GlobalTheory.RealSpan.spanAt_properties | (intros; apply GlobalTheory.RealSpan.spanAt_properties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengthsStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_majorantFlagLengths : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), (∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r)) ∧ ContinuousOn (Sg k r z) (GG k r) := by
  first | exact @GlobalTheory.Amp.LenCont.lA_Sg_continuousOn | exact GlobalTheory.Amp.LenCont.lA_Sg_continuousOn | (intros; apply GlobalTheory.Amp.LenCont.lA_Sg_continuousOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringRadiusHomSubquotientSublatticeStatement
section
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coveringRadius_hom_subquotient_sublattice : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (A S R : Submodule (𝓞 K) (Fin n → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → A.FG → IsSat (realize (Pi.basisFun K (Fin n)) X) A S → R.FG → 0 < lo → 0 < hi → (∀ N, S < N → N ≤ A → lo ≤ sizeQ (Pi.basisFun K (Fin n)) X N S) → largestSize (Pi.basisFun K (Fin n)) X R ≤ hi → ∀ T : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ S, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = 0) → (∀ w, ∀ y ∈ A, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K)))) → ∃ φ : Matrix (Fin n) (Fin n) K, (∀ y ∈ S, φ *ᵥ y = 0) ∧ (∀ y ∈ A, φ *ᵥ y ∈ R) ∧ ∃ D : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ A, D w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = (T w - (X w)⁻¹ * φ.map w.embedding * X w) *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) ∧ Real.sqrt (∑ w, Formalism.REAL.hs (D w)) ≤ ((rkK A : ℝ) - rkK S) * rkK R * Real.sqrt (nPl K) * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (nPl K : ℝ))) * hi / (2 * lo) := by
  first | exact @GlobalTheory.SubquotCover.subquot_cover | exact GlobalTheory.SubquotCover.subquot_cover | (intros; apply GlobalTheory.SubquotCover.subquot_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegralStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_computes_besselQuotientIntegral : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → ν {x | Matrix.of x ∉ GG k r} = 0 ∧ (∀ A : Set (Mt k r), MeasurableSet A → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ A ↔ x ∈ A)) → μG A = 0 → ν A = 0) ∧ ∃ φ, SubCut (GG k r) μR φ ∧ ∀ F : Mt k r → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) → ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  first | exact @GlobalTheory.Amp.CutQuot.cut_quotient | exact GlobalTheory.Amp.CutQuot.cut_quotient | (intros; apply GlobalTheory.Amp.CutQuot.cut_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubledFlagSumEqUnipotentDimAndLayerProdStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledFlag_sum_eq_unipotentDim_and_layerProd : ∀ (n a : ℕ) (j : Fin a → ℕ) (D : ℕ → ℝ) (ν : ℕ → ℕ), (∀ i, 1 ≤ j i) → (∀ s, 0 < D s) → D 0 = 1 → ν 0 = 0 → (∀ i : Fin a, ν (i + 1) = ν i + j i) → 2 * ν a ≤ n → (∀ s, s ≤ a → D (2 * a + 1 - s) = D s ∧ ν (2 * a + 1 - s) + ν s = n) → ∑ s ∈ Finset.range (2 * a + 1), (ν (s + 1) - ν s) * ν s = dimN n j ∧ layerProd n 1 j (fun i : Fin a => (D (i + 1) / D i) ^ (-(1 : ℝ) / j i)) id = (∏ s ∈ Finset.range (2 * a + 1), D s ^ ν (s + 1) / D (s + 1) ^ ν s)⁻¹ := by
  first | exact @GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq | exact GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq | (intros; apply GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBlockDiagUnitaryProductHomStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockDiag_unitary_product_hom : ∀ (n : ℕ) (ε : Fin n → Bool) (σ ι : Type) [Fintype σ] [Fintype ι] (π : σ → ι) (m : ι → ℕ) (T : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ), Function.Surjective π → (∀ s, (T s)ᴴ * T s = 1) → (∀ s t, s ≠ t → (T s)ᴴ * T t = 0) → ∑ s, T s * (T s)ᴴ = 1 → (∀ k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ, Formalism.REAL.Jm ε * ∑ s, T s * k (π s) * (T s)ᴴ = (∑ s, T s * k (π s) * (T s)ᴴ) * Formalism.REAL.Jm ε) → ∃ Φ : (∀ i, Formalism.REAL.UJ (allPos (m i))) →* Formalism.REAL.UJ ε, Continuous Φ ∧ Function.Injective Φ ∧ (∀ g, uMat (Φ g) = ∑ s, T s * uMat (g (π s)) * (T s)ᴴ) ∧ ∀ g, Formalism.REAL.hs (uMat (Φ g) - 1) = ∑ s, Formalism.REAL.hs (uMat (g (π s)) - 1) := by
  first | exact @GlobalTheory.BlockDiagEmb.exists_blockDiag_hom | exact GlobalTheory.BlockDiagEmb.exists_blockDiag_hom | (intros; apply GlobalTheory.BlockDiagEmb.exists_blockDiag_hom <;> assumption)
end

