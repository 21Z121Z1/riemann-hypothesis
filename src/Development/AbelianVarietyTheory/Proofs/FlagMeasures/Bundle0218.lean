import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0203
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0153
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0134
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0151
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0200
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankTwoDefiniteUnimodularHermitianClassBound
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0204
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableTranslatedLatticeFunctions
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.LatMeasurable

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def oneInf : MatInf E j := fun _ a b => (1 : Matrix (Fin j) (Fin j) ℂ) a b

theorem of_oneInf (w : InfinitePlace E) : Matrix.of (oneInf E j w) = 1 := rfl

theorem detNorm_oneInf : 0 < detNorm E j (oneInf E j) := by
  unfold detNorm
  simp [of_oneInf]

variable {E j}

theorem isUnit_det_of_pos {g : MatInf E j} (hg : 0 < detNorm E j g) (w : InfinitePlace E) :
    IsUnit (Matrix.of (g w)).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have hz : detNorm E j g = 0 := by
    unfold detNorm
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by simp [h0])
  linarith

def act (A : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) : VecInf E j →ₗ[ℤ] VecInf E j where
  toFun x w := A w *ᵥ x w
  map_add' x y := by funext w; simp [Matrix.mulVec_add]
  map_smul' c x := by funext w; exact Matrix.mulVec_smul (A w) c (x w)

theorem act_apply (A : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) (x : VecInf E j) (w : InfinitePlace E) :
    act A x w = A w *ᵥ x w := rfl

theorem act_act {A B : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ} (h : ∀ w, A w * B w = 1) (x : VecInf E j) :
    act A (act B x) = x := by
  funext w
  simp only [act_apply, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem latAt_eq (Λ : Submodule (𝓞 E) (Fin j → E)) (g : MatInf E j) :
    latAt E j Λ g = (latAt E j Λ (oneInf E j)).map (act fun w => (Matrix.of (g w))⁻¹) := by
  unfold latAt
  rw [Submodule.map_span, ← Set.image_comp]
  congr 2
  funext y w
  simp [act_apply, of_oneInf]

private lemma dualAt_act_transpose (A : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) (x y : VecInf E j) :
    ∑ w, (act A x w ⬝ᵥ y w).re = ∑ w, (x w ⬝ᵥ act (fun w => (A w)ᵀ) y w).re := by
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [act_apply]
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]

theorem dualAt_map (L : Submodule ℤ (VecInf E j)) {A B : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ}
    (h : ∀ w, A w * B w = 1) :
    dualAt E j (L.map (act A)) = (dualAt E j L).map (act fun w => (B w)ᵀ) := by
  have hBA : ∀ w, B w * A w = 1 := fun w => mul_eq_one_comm.mp (h w)
  have hT : ∀ y, act (fun w => (B w)ᵀ) (act (fun w => (A w)ᵀ) y) = y := fun y =>
    act_act (fun w => by rw [← Matrix.transpose_mul, h w, Matrix.transpose_one]) y
  have hT' : ∀ y, act (fun w => (A w)ᵀ) (act (fun w => (B w)ᵀ) y) = y := fun y =>
    act_act (fun w => by rw [← Matrix.transpose_mul, hBA w, Matrix.transpose_one]) y
  unfold dualAt
  rw [Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hy
    refine ⟨act (fun w => (A w)ᵀ) y, fun x hx => ?_, hT y⟩
    obtain ⟨z, hz⟩ := hy _ (Submodule.mem_map_of_mem hx)
    exact ⟨z, by rw [← dualAt_act_transpose A x y]; exact hz⟩
  · rintro ⟨y', hy', rfl⟩ x hx
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨z, hz⟩ := hy' x' hx'
    exact ⟨z, by rw [dualAt_act_transpose A x' _, hT' y']; exact hz⟩

theorem tsum_map (L : Submodule ℤ (VecInf E j)) {A B : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ}
    (h : ∀ w, A w * B w = 1) (Φ : VecInf E j → ENNReal) :
    ∑' x : {x : VecInf E j // x ∈ L.map (act A) ∧ x ≠ 0}, Φ x.1 =
      ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, Φ (act A x.1) := by
  have hBA : ∀ w, B w * A w = 1 := fun w => mul_eq_one_comm.mp (h w)
  let e : {x : VecInf E j // x ∈ L ∧ x ≠ 0} ≃ {x : VecInf E j // x ∈ L.map (act A) ∧ x ≠ 0} :=
    { toFun := fun x => ⟨act A x.1, Submodule.mem_map_of_mem x.2.1, fun h0 => x.2.2 (by
          rw [← act_act hBA x.1, h0, map_zero])⟩
      invFun := fun y => ⟨act B y.1, by
          obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp y.2.1
          rw [← hxy, act_act hBA]
          exact hx, fun h0 => y.2.2 (by rw [← act_act h y.1, h0, map_zero])⟩
      left_inv := fun x => Subtype.ext (act_act hBA x.1)
      right_inv := fun y => Subtype.ext (act_act h y.1) }
  exact (e.tsum_eq (fun x => Φ x.1)).symm

def pairL (y : VecInf E j) : VecInf E j →ₗ[ℝ] ℝ where
  toFun x := ∑ w, (x w ⬝ᵥ y w).re
  map_add' x x' := by simp [add_dotProduct, Finset.sum_add_distrib]
  map_smul' c x := by simp [smul_dotProduct, Finset.mul_sum]

theorem pairL_injective : Function.Injective (pairL : VecInf E j → _) := by
  classical
  intro y y' hyy
  have key : ∀ (w : InfinitePlace E) (a : Fin j) (c : ℂ), (c * y w a).re = (c * y' w a).re := by
    intro w a c
    have hv : ∀ z : VecInf E j, pairL z (Pi.single w (Pi.single a c)) = (c * z w a).re := by
      intro z
      show ∑ v, ((Pi.single w (Pi.single a c) : VecInf E j) v ⬝ᵥ z v).re = _
      rw [Finset.sum_eq_single w (fun v _ hne => by simp [hne]) (by simp)]
      simp [single_dotProduct]
    rw [← hv y, ← hv y', hyy]
  funext w a
  apply Complex.ext
  · simpa using key w a 1
  · simpa using key w a Complex.I

theorem countable_dualAt (L : Submodule ℤ (VecInf E j)) (hL : Submodule.span ℝ (L : Set (VecInf E j)) = ⊤) :
    Countable (dualAt E j L) := by
  have hsym : ∀ x y : VecInf E j, pairL y x = pairL x y := fun x y => by
    show ∑ w, (x w ⬝ᵥ y w).re = ∑ w, (y w ⬝ᵥ x w).re
    exact Finset.sum_congr rfl fun w _ => by rw [dotProduct_comm]
  have hint : ∀ y ∈ dualAt E j L, ∀ x ∈ L, ∃ z : ℤ, pairL x y = z := by
    intro y hy x hx
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨z, hz⟩ := hy' x hx
      exact ⟨z, by rw [← hsym x y]; exact hz⟩
    | zero => exact ⟨0, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨a, ha⟩ := h1
      obtain ⟨c, hc⟩ := h2
      exact ⟨a + c, by rw [map_add, ha, hc]; push_cast; ring⟩
    | smul n y _ h1 =>
      obtain ⟨a, ha⟩ := h1
      exact ⟨n * a, by rw [map_zsmul, ha, zsmul_eq_mul]; push_cast; ring⟩
  obtain ⟨b, hbL, hbspan, hbli⟩ := exists_linearIndependent ℝ (L : Set (VecInf E j))
  haveI : Finite b := hbli.finite
  choose φ hφ using fun (y : dualAt E j L) (i : b) => hint y.1 y.2 i.1 (hbL i.2)
  refine Function.Injective.countable (f := φ) ?_
  intro y y' hyy
  apply Subtype.ext
  apply pairL_injective
  refine LinearMap.ext_on (s := (b : Set (VecInf E j))) (hbspan.trans hL) ?_
  intro x hx
  have e1 := hφ y ⟨x, hx⟩
  have e2 := hφ y' ⟨x, hx⟩
  dsimp only at e1 e2
  rw [hsym x y.1, hsym x y'.1, e1, e2, hyy]

theorem measurable_of_continuous {β : Type} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (w : InfinitePlace E) (f : Matrix (Fin j) (Fin j) ℂ → β) (hf : Continuous f) :
    Measurable fun g : MatInf E j => f (Matrix.of (g w)) := by
  have hc : Continuous fun g : InfinitePlace E → Fin j → Fin j → ℂ => f (Matrix.of (g w)) :=
    hf.comp (continuous_apply w)
  exact hc.measurable

theorem measurable_detNorm : Measurable (detNorm E j) := by
  unfold detNorm
  exact Finset.measurable_prod _ fun w _ =>
    measurable_of_continuous w (fun M => ‖M.det‖ ^ 2) (continuous_id.matrix_det.norm.pow 2)

theorem measurable_act_inv (x : VecInf E j) :
    Measurable fun g : MatInf E j => act (fun w => (Matrix.of (g w))⁻¹) x := by
  refine measurable_pi_lambda _ fun w => ?_
  simp only [act_apply]
  have hinv : ∀ M : Matrix (Fin j) (Fin j) ℂ, M⁻¹ = (M.det)⁻¹ • M.adjugate := fun M => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [hinv]
  have hd : Measurable fun g : MatInf E j => (Matrix.of (g w)).det :=
    measurable_of_continuous w (fun M => M.det) continuous_id.matrix_det
  refine measurable_pi_lambda _ fun a => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun b _ => ?_
  exact (hd.inv.mul (measurable_of_continuous w (fun M => M.adjugate a b)
    (continuous_id.matrix_adjugate.matrix_elem a b))).mul_const _

theorem measurable_act_transpose (x : VecInf E j) :
    Measurable fun g : MatInf E j => act (fun w => (Matrix.of (g w))ᵀ) x := by
  refine measurable_pi_lambda _ fun w => ?_
  simp only [act_apply]
  exact measurable_of_continuous w (fun M => Mᵀ *ᵥ x w)
    (continuous_id.matrix_transpose.matrix_mulVec continuous_const)

theorem measurable_indicator_of_eqOn {f f' : MatInf E j → ENNReal} (hf' : Measurable f')
    (h : ∀ g, 0 < detNorm E j g → f g = f' g) :
    Measurable fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator f g := by
  have hS : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} :=
    measurableSet_lt measurable_const measurable_detNorm
  convert hf'.indicator hS using 1
  funext g
  exact congrFun (Set.indicator_congr fun g hg => h g hg) g

private lemma countable_nonzero_lattice_vectors (L : Submodule ℤ (VecInf E j)) [Countable L] :
    Countable {x : VecInf E j // x ∈ L ∧ x ≠ 0} :=
  Function.Injective.countable (f := fun x : {x : VecInf E j // x ∈ L ∧ x ≠ 0} => (⟨x.1, x.2.1⟩ : L))
    fun _ _ hab => Subtype.ext (congrArg (fun y : L => (y : VecInf E j)) hab)

theorem measurable_latFun : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => w (covAt E j (latAt E j Λ g))) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ g ∧ x ≠ 0}, Φ x.1) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ g) ∧ x ≠ 0}, Φ x.1) g) := by
  intro E _ _ hE j wt Φ hw hΦ Λ hΛ
  obtain ⟨κ, -, hK⟩ := (GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE j).1 Λ hΛ
  obtain ⟨⟨hd, hz⟩, -, -, -⟩ := hK (oneInf E j) (detNorm_oneInf E j)
  haveI : Countable (latAt E j Λ (oneInf E j)) :=
    TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  haveI : Countable (dualAt E j (latAt E j Λ (oneInf E j))) := countable_dualAt _ hz.span_top
  haveI := countable_nonzero_lattice_vectors (latAt E j Λ (oneInf E j))
  haveI := countable_nonzero_lattice_vectors (dualAt E j (latAt E j Λ (oneInf E j)))
  have hinv : ∀ g : MatInf E j, 0 < detNorm E j g → ∀ w, (Matrix.of (g w))⁻¹ * Matrix.of (g w) = 1 :=
    fun g hg w => Matrix.nonsing_inv_mul _ (isUnit_det_of_pos hg w)
  have htr : ∀ g : MatInf E j, 0 < detNorm E j g →
      ∀ w, (Matrix.of (g w))ᵀ * ((Matrix.of (g w))⁻¹)ᵀ = 1 := by
    intro g hg w
    rw [← Matrix.transpose_mul, hinv g hg w, Matrix.transpose_one]
  refine ⟨?_, ?_, ?_⟩
  · exact measurable_indicator_of_eqOn (f' := fun g => wt (κ / detNorm E j g))
      (hw.comp (measurable_const.div measurable_detNorm)) fun g hg => by simp only [(hK g hg).2.1]
  · refine measurable_indicator_of_eqOn
      (f' := fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ (oneInf E j) ∧ x ≠ 0},
        Φ (act (fun w => (Matrix.of (g w))⁻¹) x.1))
      (Measurable.ennreal_tsum fun x => hΦ.comp (measurable_act_inv x.1)) fun g hg => ?_
    try dsimp only
    rw [latAt_eq Λ g, tsum_map _ (hinv g hg) Φ]
  · refine measurable_indicator_of_eqOn
      (f' := fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ (oneInf E j)) ∧ x ≠ 0},
        Φ (act (fun w => (Matrix.of (g w))ᵀ) x.1))
      (Measurable.ennreal_tsum fun x => hΦ.comp (measurable_act_transpose x.1)) fun g hg => ?_
    try dsimp only
    rw [latAt_eq Λ g, dualAt_map _ (hinv g hg), tsum_map _ (htr g hg) Φ]

end GlobalTheory.LatMeasurable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MultipliableOfRealReOfComplex
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory

theorem multipliable_ofReal_re_of_complex (ι : Type) (c : ι → ℂ) (hc : Multipliable c)
    (hcr : ∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) :
    Multipliable (fun i => ENNReal.ofReal (c i).re) ∧
      ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re := by
  obtain ⟨a, ha⟩ := hc
  have hc' : ∀ i, c i = ((c i).re : ℂ) := fun i => Complex.ext (by simp) (by simp [(hcr i).1])
  have hre : HasProd (fun i => (c i).re) a.re := by
    have h := (Complex.continuous_re.tendsto a).comp ha
    refine h.congr ?_
    intro s
    simp only [Function.comp]
    rw [Finset.prod_congr rfl (fun i _ => hc' i), ← Complex.ofReal_prod, Complex.ofReal_re]
  have h2 : HasProd (fun i => ENNReal.ofReal (c i).re) (ENNReal.ofReal a.re) := by
    have h := (ENNReal.continuous_ofReal.tendsto a.re).comp hre
    refine h.congr ?_
    intro s
    simp only [Function.comp]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (hcr i).2)]
  exact ⟨h2.multipliable, by rw [h2.tprod_eq, ha.tprod_eq]⟩

theorem multipliable_ofReal_re_of_complex' : ∀ (ι : Type) (c : ι → ℂ), Multipliable c → (∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) → Multipliable (fun i => ENNReal.ofReal (c i).re) ∧ ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re :=
  multipliable_ofReal_re_of_complex

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilradicalFirstLayerCoveringRadiusLe
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.Count.FirstLayer

theorem inNil_sub {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (W : Submodule A (Fin n → A)) (Y Y' : Matrix (Fin n) (Fin n) A)
    (h : InNil s J W Y) (h' : InNil s J W Y') : InNil s J W (Y - Y') := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := h'
  have l1 : ∀ a b c : Fin n → A, Formalism.UG.hform s J (a - b) c = Formalism.UG.hform s J a c - Formalism.UG.hform s J b c := by
    intro a b c
    simp [Formalism.UG.hform, sub_mul, Finset.sum_sub_distrib]
  have l2 : ∀ a b c : Fin n → A, Formalism.UG.hform s J c (a - b) = Formalism.UG.hform s J c a - Formalism.UG.hform s J c b := by
    intro a b c
    simp [Formalism.UG.hform, mul_sub, Finset.sum_sub_distrib]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u u'
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, l1, l2]
    have a := h1 u u'
    have b := g1 u u'
    linear_combination a - b
  · intro u w hw
    rw [Matrix.sub_mulVec, l2, h2 u w hw, g2 u w hw, sub_zero]
  · intro u hu
    rw [Matrix.sub_mulVec]
    exact W.sub_mem (h3 u hu) (g3 u hu)
  · intro u hu
    rw [Matrix.sub_mulVec, h4 u hu, g4 u hu, sub_zero]

theorem map_mulVec_emb (I : AutInst) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) I.E)
    (y : Fin I.n → I.E) :
    M.map (I.φ v) *ᵥ (fun i => I.φ v (y i)) = fun i => I.φ v ((M *ᵥ y) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem mem_spanAt (I : AutInst) (v : InfinitePlace I.F) (R : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (y : Fin I.n → I.E) (hy : y ∈ R) : (fun i => I.φ v (y i)) ∈ spanAt I R v :=
  Submodule.subset_span ⟨y, hy, rfl⟩

theorem mulVec_mem_of_span (I : AutInst) (v : InfinitePlace I.F) (A : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (M : Matrix (Fin I.n) (Fin I.n) ℂ) (W : Submodule ℂ (Fin I.n → ℂ))
    (h : ∀ y ∈ A, M *ᵥ (fun i => I.φ v (y i)) ∈ W) : ∀ u ∈ spanAt I A v, M *ᵥ u ∈ W := by
  have : spanAt I A v ≤ W.comap (Matrix.mulVecLin M) := by
    unfold spanAt
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  intro u hu
  exact this hu

theorem frame_inv (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) ℂ) :
    uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * M * I.P v * uMat (x.1 v) =
      (I.P v * uMat (x.1 v))⁻¹ * M * (I.P v * uMat (x.1 v)) := by
  rw [Matrix.mul_inv_rev]
  have : uMat (x.1 v)⁻¹ = (uMat (x.1 v))⁻¹ := by
    simp only [uMat, Subgroup.coe_inv, Matrix.coe_units_inv]
  rw [this]
  simp only [Matrix.mul_assoc]

theorem frame_det (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) :
    IsUnit (I.P v * uMat (x.1 v)).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact (I.P_unit v).mul (Units.isUnit _)

theorem frame_spec (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) :
    (I.P v * uMat (x.1 v))ᴴ * I.J.map (I.φ v) * (I.P v * uMat (x.1 v)) = Jm (I.ε v) := by
  have h : (uMat (x.1 v))ᴴ * Jm (I.ε v) * uMat (x.1 v) = Jm (I.ε v) := (x.1 v).2
  rw [← h, ← I.P_spec v, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem arith (n f k j rd lo hi rho : ℝ) (hf : 0 < f) (hrd : 0 ≤ rd) (hkj : k + j = n) (hlo : 0 < lo)
    (hhi : 0 < hi) (hr : hi ≤ rho * lo) :
    Real.sqrt 2 * ((k - j) * j * Real.sqrt f * rd * hi / (2 * lo)) ≤
      (n ^ 2 * f) / 8 * rd * rho / Real.sqrt (2 * f) := by
  have h1 : (k - j) * j ≤ n ^ 2 / 8 := by
    rw [← hkj]; nlinarith [sq_nonneg (k - 3 * j)]
  have h2 : hi / lo ≤ rho := by rwa [div_le_iff₀ hlo]
  have h3 : 0 < hi / lo := div_pos hhi hlo
  have hs : 0 < Real.sqrt (2 * f) := Real.sqrt_pos.2 (by linarith)
  have e : Real.sqrt 2 * Real.sqrt f = Real.sqrt (2 * f) := (Real.sqrt_mul (by norm_num) f).symm
  have e2 : Real.sqrt (2 * f) * Real.sqrt (2 * f) = 2 * f := Real.mul_self_sqrt (by linarith)
  have e3 : (n ^ 2 * f) / 8 * rd * rho / Real.sqrt (2 * f) =
      n ^ 2 / 8 * rho * (Real.sqrt (2 * f) * rd / 2) := by
    rw [div_eq_iff hs.ne']
    linear_combination (-(n ^ 2 / 8 * rho * rd / 2)) * e2
  have e4 : Real.sqrt 2 * ((k - j) * j * Real.sqrt f * rd * hi / (2 * lo)) =
      (k - j) * j * (hi / lo) * (Real.sqrt (2 * f) * rd / 2) := by
    rw [← e]; field_simp
  rw [e3, e4]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc (k - j) * j * (hi / lo) ≤ n ^ 2 / 8 * (hi / lo) := mul_le_mul_of_nonneg_right h1 h3.le
    _ ≤ n ^ 2 / 8 * rho := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem main : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → 0 < lo → hi ≤ rho * lo → ∀ Y ∈ nilReal I R, ∃ Y₀ ∈ nilInt I x R, ∃ Z ∈ cenReal I R, normAt I x (Y - diagEmb I Y₀ - Z) ≤ ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * rho / Real.sqrt (2 * I.f) := by
  intro I x R lo hi rho hsat hiso hhi hlarge hlow hlo hr Y hY
  have hpl : perpIn I x R ≤ lamX I x := by
    unfold perpIn
    rw [Submodule.span_le]
    exact fun y hy => hy.1
  have hfg : (lamX I x).FG := (GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x).2.1
  have hsat' : IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) R := by
    refine ⟨hiso, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hiso hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩ hz
      exact hsat.2.2 _ ⟨y, hpl hy, rfl⟩ hz
  obtain ⟨-, -, hperp, hnil, -⟩ := GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R
  have hP : ∀ v u, u ∈ perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) ↔
      u ∈ spanAt I (perpIn I x R) v := by
    intro v u
    rw [← hperp v]; rfl
  have hmono : ∀ v, spanAt I R v ≤ spanAt I (perpIn I x R) v := fun v =>
    Submodule.span_mono (Set.image_mono hiso)
  obtain ⟨Φ, hΦ0, hΦ1, D, hD, hDn⟩ := GlobalTheory.T.subquotient_covering_radius_real_places I x (perpIn I x R) R R lo hi (hfg.of_le hpl) hsat'
    (hfg.of_le hsat.1) hlo hhi (fun N h1 h2 => hlow N h1 (h2.trans hpl)) hlarge Y
    (fun v y hy => (hY v).2.2.2 _ (mem_spanAt I v R y hy))
    (fun v y hy => (hY v).2.2.1 _ ((hP v _).2 (mem_spanAt I v _ y hy)))
  obtain ⟨Y₀, hY₀, hY₀Φ⟩ := GlobalTheory.T.exists_stabilizerNilradicalIntegral_lift_of_orthogonal I x R hiso Φ hΦ0 hΦ1
  have hA : ∀ v, ∃ A : Matrix (Fin I.n) (Fin I.n) ℂ,
      InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) A ∧
      (∀ u ∈ perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v), A *ᵥ u = D v *ᵥ u) ∧
      hs ((I.P v * uMat (x.1 v))⁻¹ * A * (I.P v * uMat (x.1 v))) ≤
        2 * hs ((I.P v * uMat (x.1 v))⁻¹ * D v * (I.P v * uMat (x.1 v))) := by
    intro v
    refine GlobalTheory.T.exists_stabilizerNilradical_lift_of_isotropic I.n (I.ε v) _ _ (D v) _ (frame_det I x v) (frame_spec I x v)
      (fun u hu => (hP v u).2 (hmono v hu)) ?_ ?_
    · intro u hu
      have h0 : Φ.map (I.φ v) *ᵥ u ∈ (⊥ : Submodule ℂ (Fin I.n → ℂ)) := by
        refine mulVec_mem_of_span I v R _ ⊥ ?_ u hu
        intro y hy
        rw [map_mulVec_emb, hΦ0 y hy, Submodule.mem_bot]
        funext i; simp
      rw [hD v u (hmono v hu), Matrix.sub_mulVec, (hY v).2.2.2 u hu, (Submodule.mem_bot ℂ).1 h0, sub_zero]
    · intro u hu
      have h0 : Φ.map (I.φ v) *ᵥ u ∈ spanAt I R v := by
        refine mulVec_mem_of_span I v _ _ _ ?_ u ((hP v u).1 hu)
        intro y hy
        rw [map_mulVec_emb]
        exact mem_spanAt I v R _ (hΦ1 y hy)
      rw [hD v u ((hP v u).1 hu), Matrix.sub_mulVec]
      exact Submodule.sub_mem _ ((hY v).2.2.1 u hu) h0
  choose A hA1 hA2 hA3 using hA
  refine ⟨Y₀, hY₀, Y - diagEmb I Y₀ - A, ?_, ?_⟩
  · intro v
    refine ⟨inNil_sub _ _ _ _ _ (inNil_sub _ _ _ _ _ (hY v) (hnil Y₀ hY₀.1 v)) (hA1 v), ?_⟩
    intro u hu
    have h0 : (Y₀.map (I.φ v) - Φ.map (I.φ v)) *ᵥ u ∈ (⊥ : Submodule ℂ (Fin I.n → ℂ)) := by
      refine mulVec_mem_of_span I v _ _ ⊥ ?_ u ((hP v u).1 hu)
      intro y hy
      rw [Matrix.sub_mulVec, map_mulVec_emb, map_mulVec_emb, hY₀Φ y hy, sub_self]
      exact Submodule.zero_mem _
    rw [Submodule.mem_bot, Matrix.sub_mulVec, sub_eq_zero] at h0
    show (Y v - Y₀.map (I.φ v) - A v) *ᵥ u = 0
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hA2 v u hu, hD v u ((hP v u).1 hu), Matrix.sub_mulVec, h0,
      sub_self]
  · rw [sub_sub_cancel]
    have hAD : normAt I x A ≤ Real.sqrt 2 * normAt I x D := by
      unfold normAt
      rw [← Real.sqrt_mul (by norm_num), Finset.mul_sum]
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro v _
      rw [frame_inv, frame_inv]
      exact hA3 v
    have hrk : rkK (perpIn I x R) + rkK R = I.n :=
      ((GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x).2.2.2 R R hsat hsat le_rfl).2.1
    have hf : (0 : ℝ) < I.f := by
      have : 0 < I.f := Module.finrank_pos
      exact_mod_cast this
    have hrd : 0 ≤ I.rd := Real.rpow_nonneg (abs_nonneg _) _
    refine hAD.trans ((mul_le_mul_of_nonneg_left hDn (Real.sqrt_nonneg _)).trans ?_)
    exact arith _ _ _ _ _ _ _ _ hf hrd (by exact_mod_cast hrk) hlo hhi hr

end GlobalTheory.Count.FirstLayer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLayerHeightQuotientsEqSqStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_layer_height_quotients_eq_sq : ∀ (n f a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ) (τ : Fin a → ℝ) (h : ℕ → ℝ), (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i → (∀ b, 2 * a + 1 ≤ b → r b = 0) → (∀ i : Fin a, 0 < τ i ∧ h i = τ i ^ (2 * f * j i) ∧ h (2 * a - i) = (τ i ^ (2 * f * j i))⁻¹) → h a = 1 → (∀ b, 2 * a + 1 ≤ b → h b = 1) → ∏ c ∈ Finset.range (2 * a + 1), ∏ b ∈ Finset.range (2 * a + 1), h b ^ r (b + c + 1) / h (b + c + 1) ^ r b = layerProd n f j τ id ^ 2 := by
  first | exact @GlobalTheory.HtProd.htProd | exact GlobalTheory.HtProd.htProd | (intros; apply GlobalTheory.HtProd.htProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivarianceStatement
section
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_complexifiedK_equivariance : PsEquiv := by
  first | exact @GlobalTheory.Dec.Equivar.psEquiv | exact GlobalTheory.Dec.Equivar.psEquiv | (intros; apply GlobalTheory.Dec.Equivar.psEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankTwoDefiniteUnimodularHermitianClassBoundStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_two_definite_unimodular_hermitian_class_bound : RankTwoClasses := by
  first | exact @GlobalTheory.RankTwoCount.rankTwoClasses | exact GlobalTheory.RankTwoCount.rankTwoClasses | (intros; apply GlobalTheory.RankTwoCount.rankTwoClasses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBlockFrameLocalSplitStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_block_frame_local_split : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' → (∀ b, Submodule.IsLattice E (Λ b)) → (∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) → (∀ (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) ∧ ∀ k y, y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0) ∧ ∀ c, (∀ Y ∈ lowers F c, ∀ b, ∀ y ∈ Λ (b + c + 1), (T' b * Y * T (b + c + 1)) *ᵥ y ∈ Λ b) ∧ ∀ Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) E, (∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) → ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  first | exact @GlobalTheory.RadCov.LocSplit.locSplit | exact GlobalTheory.RadCov.LocSplit.locSplit | (intros; apply GlobalTheory.RadCov.LocSplit.locSplit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealComplexSpanOrthonormalSkewFamilyStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_complex_span_orthonormal_skew_family : ∀ (n d : ℕ) (ε : Fin n → Bool) (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (s : Set (Fin d)), (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) → (∀ i, Formalism.REAL.inG ε (B i)) → (∀ X, (X ∈ Submodule.span ℂ (B '' s) ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (B '' s)) ∧ (∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0) ∧ ∀ X i, (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * (B i)ᴴ).trace = - starRingEnd ℂ (X * (B i)ᴴ).trace := by
  first | exact @GlobalTheory.SkewSpan.real_span | exact GlobalTheory.SkewSpan.real_span | (intros; apply GlobalTheory.SkewSpan.real_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesMatchIsomorphicCMInstancesStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaces_match_isomorphic_CM_instances : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E), (∀ y, e (star y) = star (e y)) → ∃ (β : InfinitePlace I.F ≃ InfinitePlace I.E) (σ : InfinitePlace I.F ≃ InfinitePlace I₀.F) (τ τ₀ : InfinitePlace I.F → (ℂ →+* ℂ)), (∀ v, τ v = RingHom.id ℂ ∨ τ v = starRingEnd ℂ) ∧ (∀ v, τ₀ v = RingHom.id ℂ ∨ τ₀ v = starRingEnd ℂ) ∧ (∀ v y, I.φ v y = τ v ((β v).embedding y)) ∧ ∀ v y, I.φ v (e y) = τ₀ v (I₀.φ (σ v) y) := by
  first | exact @GlobalTheory.LeviIso.Places.places_match | exact GlobalTheory.LeviIso.Places.places_match | (intros; apply GlobalTheory.LeviIso.Places.places_match <;> assumption)
end

