import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0032
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsBoundedAtOfIsBoundedH
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CoordinateSecondPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial Filter

noncomputable section

theorem geoNum_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] :
    ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin n → K → ℤ), (∀ j k, 0 ≤ a j k) → 0 ≤ geoNum n V a
  | 0, V, a, _ => by
    unfold geoNum
    split_ifs <;> simp
  | n + 1, V, a, ha => by
    unfold geoNum
    split_ifs with h
    · refine Finset.sum_nonneg fun k _ ↦ mul_nonneg (ha _ _) (finsum_nonneg fun W ↦ finsum_nonneg fun _ ↦ ?_)
      exact mul_nonneg (Nat.cast_nonneg _) (geoNum_nonneg n W _ fun j k ↦ ha _ _)
    · exact le_rfl

theorem nefOnFibres_of_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {a : K → ℤ} (ha : ∀ k, 0 ≤ a k) : NefOnFibres P a :=
  fun W _ _ _ _ ↦ geoNum_nonneg 1 W _ fun _ k ↦ ha k

namespace P1

theorem sum_blk (m : J2 →₀ ℕ) : ∑ i : Fin 2, m ⟨(), i⟩ = ∑ q, m q := by
  rw [sum_twoPoint, Fin.sum_univ_two]; rfl

theorem isMultiHomog_iff (f : MvPolynomial J2 ℤ) (d : ℕ) :
    IsMultiHomog (ι := GlobalTheory (Fin 2)) f (fun _ ↦ d) ↔ f.IsHomogeneous d := by
  constructor
  · intro h m hm
    have := h m (mem_support_iff.mpr hm) ()
    rw [sum_blk] at this
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [Finsupp.sum_fintype _ _ (by simp)]
    exact this
  · intro h m hm k
    have := h (mem_support_iff.mp hm)
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at this
    rw [Finsupp.sum_fintype _ _ (by simp)] at this
    rw [sum_blk]
    exact this

theorem isMultiHomog_X (q : J2) : IsMultiHomog (ι := GlobalTheory (Fin 2)) (X q : MvPolynomial J2 ℤ) fun _ ↦ 1 :=
  (isMultiHomog_iff _ 1).mpr (isHomogeneous_X ℤ q)

theorem isMultiHomog_one : IsMultiHomog (ι := GlobalTheory (Fin 2)) (1 : MvPolynomial J2 ℤ) fun _ ↦ 0 :=
  (isMultiHomog_iff _ 0).mpr (isHomogeneous_one _ _)

abbrev Afs : HermLine (GlobalTheory (Fin 2)) := HermLine.ofCone fs

theorem ratio_mem (c : ∀ k, GlobalTheory (Fin 2) k) (q : J2) :
    x q / x ⟨(), c ()⟩ ∈ chartRingZ (ι := GlobalTheory (Fin 2)) x c :=
  Algebra.subset_adjoin ⟨q, rfl⟩

def e2 : Fin 2 → J2 := fun i ↦ ⟨(), i⟩

end P1

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.EventuallyBlocksNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

theorem eventually_blocks_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ᶠ w in 𝓝 z, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := by
  refine Filter.eventually_all.2 fun k => ?_
  obtain ⟨i, hi⟩ := hz k
  exact ((continuous_apply (⟨k, i⟩ : Σ k, ι k)).continuousAt.eventually_ne hi).mono fun w hw => ⟨i, hw⟩

theorem leviForm_congr_add_const {N : Type} [Fintype N] {φ ψ : (N → ℂ) → ℝ} {z : N → ℂ} (c : ℝ)
    (h : φ =ᶠ[𝓝 z] fun w => ψ w + c) (w : N → ℂ) : leviForm φ z w = leviForm ψ z w := by
  have h2 : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z := by
    have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ :=
      h.fderiv.trans (Eventually.of_forall fun x => fderiv_add_const c)
    exact h1.fderiv_eq
  unfold leviForm
  rw [h2]

theorem SuccessiveMinimaDual.proof (hG1 : G1.Statement) (hW : EmbeddingWeight.Statement)
    (hT : TwistIntersection.Statement) : SuccessiveMinimaDual.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D a A P0 II Λ hD hII hvar hbir ha hP0 hsemi hconj hΛ hΛc huniq hmon
  obtain ⟨B, hBa, hBs, hBc, hBloc⟩ := hW K ι Ω F y Λ hΛ hΛc huniq
  have hA' : (A.tensor B).a = fun k => (a k : ℤ) := by
    rw [show (A.tensor B).a = A.a + B.a from rfl, ha, hBa, add_zero]
  have hsemi' : IsSemipositiveRel P0 (mCoordIdeal y) (A.tensor B) := by
    refine ⟨hsemi.1.mul hBs, fun z hz w hw => ?_⟩
    obtain ⟨sg, hsg, -⟩ := huniq z hz
    have hev : (fun x => Real.log ((A.tensor B).h x)) =ᶠ[𝓝 z]
        fun x => Real.log (A.h x) + Real.log (Λ sg) := by
      filter_upwards [hBloc z hz sg hsg, eventually_blocks_ne_zero hz.1] with x h1 h2
      rw [show (A.tensor B).h x = A.h x * B.h x from rfl, h1,
        Real.log_mul (A.pos x h2).ne' (hΛ sg).ne']
    rw [leviForm_congr_add_const _ hev]
    exact hsemi.2 z hz w hw
  have hconj' : IsConjInvariantH (A.tensor B) := fun z => by
    show A.h _ * B.h _ = A.h z * B.h z
    rw [hconj z, hBc z]
  have hmon' : MonomialsBounded (mCoordIdeal y) (A.tensor B) a := by
    intro z hz μ hμ
    obtain ⟨sg, hsg, -⟩ := huniq z hz
    have hb := hmon z hz sg hsg μ hμ
    have hBz : B.h z = Λ sg := (hBloc z hz sg hsg).eq_of_nhds
    show _ ≤ A.h z * B.h z
    rw [hBz, mul_comm]
    exact hb
  have h0 := hG1 K ι Ω y D a (A.tensor B) P0 II hD hII hvar hbir hA' hP0 hsemi' hmon' hconj'
  rwa [hT K ι Ω F y D a A B II Λ hD hII hvar hbir ha hsemi.1 hBa hBs hΛ huniq hBloc] at h0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedMod (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) : Prop :=
  ∀ I : KH.Cell K ι 0, ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d,
    ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ) (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
      t ∈ KH.cellMon S I.1 ∧ IsMultiHomog t a ∧ (∀ j, IsMultiHomog (p j) a) ∧
      (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ t • x = ∑ j, p j • z j I

def H1GenAmple (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
    Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
    ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c →
      Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1) ∧ GeneratedMod S ι 𝓜 (e + c • N)

section Point

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

theorem cell_zero_subsingleton : Subsingleton (KH.Cell K ι 0) :=
  ⟨fun I J => Subtype.ext (funext fun k => (I.2.1 k).eq_univ.trans (J.2.1 k).eq_univ.symm)⟩

omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in

theorem cell_succ_isEmpty (n : ℕ) : IsEmpty (KH.Cell K ι (n + 1)) := by
  refine ⟨fun I => ?_⟩
  have h : ∑ k, ((I.1 k).card - 1) = 0 :=
    Finset.sum_eq_zero fun k _ => Nat.sub_eq_zero_of_le (Finset.card_le_one_of_subsingleton _)
  have := I.2.2
  omega

theorem cechHc_one_subsingleton {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    Subsingleton (KH.cechHc ι 𝓜 d 1) := by
  have := cell_succ_isEmpty (K := K) (ι := ι) 0
  have : Subsingleton (KH.CechC S ι M 1) := ⟨fun f g => funext fun I => (IsEmpty.false I).elim⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

omit [Fintype K] [∀ k, Subsingleton (ι k)] in

theorem isMultiHomog_one_zero : IsMultiHomog (1 : MRingOver S ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    rw [mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · exact h.symm
    · exact absurd rfl hm
  simp [this]

theorem generatedMod_of_subsingleton {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    GeneratedMod S ι 𝓜 d := by
  have := cell_zero_subsingleton (K := K) (ι := ι)
  have := cell_succ_isEmpty (K := K) (ι := ι) 0
  intro I x hx
  let z : KH.CechC S ι M 0 := fun J => (Subsingleton.elim I J ▸ x : LocalizedModule (KH.cellMon S J.1) M)
  refine ⟨1, 0, 1, fun _ => 1, fun _ => z, Submonoid.one_mem _, isMultiHomog_one_zero,
    fun _ => isMultiHomog_one_zero, fun _ => ⟨?_, ?_⟩, ?_⟩
  · intro J _
    obtain rfl : I = J := Subsingleton.elim _ _
    exact hx
  · show KH.cechD S ι M 0 z = 0
    exact funext fun J => (IsEmpty.false J).elim
  · simp only [one_smul, Finset.univ_unique, Finset.sum_singleton]
    rfl

theorem h1GenAmple_of_subsingleton (V : Ideal (MRingOver S ι)) (N : K → ℤ) : H1GenAmple S V N := by
  intro M _ _ _ _ 𝓜 _ _ _ e
  exact ⟨0, fun c _ => ⟨cechHc_one_subsingleton 𝓜 _, generatedMod_of_subsingleton 𝓜 _⟩⟩

end Point

abbrev pointIdx : Unit → Type := fun _ => Fin 1

theorem bot_isMultiProjPrime_point : IsMultiProjPrime (⊥ : Ideal (MRingOver ℚ pointIdx)) :=
  ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, by simp [X_ne_zero]⟩⟩

theorem h1GenAmple_projectivePoint : H1GenAmple ℚ (⊥ : Ideal (MRingOver ℚ pointIdx)) 0 :=
  h1GenAmple_of_subsingleton _ _

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology

theorem L1Convergence.proof : L1Convergence.Statement := by
  intro Ω _ μ _ g b C hg hb hC hlim hint

  have hp_int : ∀ n, Integrable (fun x => max (g n x - b x) 0) μ :=
    fun n => ((hg n).sub hb).pos_part
  have hbound_int : Integrable (fun x => C + |b x|) μ := (integrable_const C).add hb.abs
  have hpt : Tendsto (fun n => ∫ x, max (g n x - b x) 0 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => max (g n x - b x) 0) (f := fun _ => (0 : ℝ)) (fun x => C + |b x|)
      (fun n => (hp_int n).aestronglyMeasurable) hbound_int
      (fun n => Filter.Eventually.of_forall fun x => by
        have h1 := hC n x
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [neg_abs_le (b x)]) (by linarith [abs_nonneg (b x)]))
      (Filter.Eventually.of_forall fun x => by
        refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n =>
          lt_of_lt_of_le ha (le_max_right _ _), fun a ha => ?_⟩
        filter_upwards [hlim x (a / 2) (by linarith)] with n hn
        exact lt_of_le_of_lt (max_le (show g n x - b x ≤ a / 2 by linarith)
          (show (0 : ℝ) ≤ a / 2 by linarith)) (by linarith))
    simpa using h

  have hid : ∀ n, ∫ x, |g n x - b x| ∂μ =
      2 * ∫ x, max (g n x - b x) 0 ∂μ - (∫ x, g n x ∂μ - ∫ x, b x ∂μ) := by
    intro n
    have hpt' : ∀ x, |g n x - b x| = 2 * max (g n x - b x) 0 - (g n x - b x) := by
      intro x
      rcases le_total 0 (g n x - b x) with h | h
      · rw [abs_of_nonneg h, max_eq_left h]; ring
      · rw [abs_of_nonpos h, max_eq_right h]; ring
    simp_rw [hpt']
    have hgb : Integrable (fun x => g n x - b x) μ := (hg n).sub hb
    rw [integral_sub ((hp_int n).const_mul 2) hgb, integral_const_mul,
      integral_sub (hg n) hb]
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n =>
    lt_of_lt_of_le ha (integral_nonneg fun x => abs_nonneg _), fun a ha => ?_⟩
  filter_upwards [(tendsto_order.1 hpt).2 (a / 4) (by linarith), hint (a / 4) (by linarith)]
    with n hn1 hn2
  rw [hid n]
  linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBisAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

noncomputable section

def TensorPowerL2Degree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (μ : Measure ((Σ k, ι k) → ℂ)) (m : ℕ),
      IsProbabilityMeasure μ ∧ μ (mcPts (mCoordIdeal y))ᶜ = 0 ∧ IsZariskiDenseMeasure (mCoordIdeal y) μ ∧
      1 ≤ m ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop,
        ∀ (r : ℕ) (ψ : chartLat y A.a (m * q) →+ EuclideanSpace ℝ (Fin r)), Function.Injective ψ →
          (∀ s : chartLat y A.a (m * q), ‖ψ s‖ = sectionL2Norm μ y A (m * q) (s : Ω)) →
          ∀ [DiscreteTopology (imageLattice ψ)] [IsZLattice ℝ (imageLattice ψ)],
            -Real.log (ZLattice.covolume (imageLattice ψ)) ≤
              (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
                (((m * q : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ArithmeticVolumeBigDimensionOne.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    II K ι (mCoordIdeal y) 1 (fun _ => A) ≤ arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 0

namespace ArithmeticVolumeBigDimensionOne

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end ArithmeticVolumeBigDimensionOne

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

noncomputable section

theorem L2GramLattice.proof : L2GramLattice.Statement := by
  intro E _ _ _ X _ μ _ w hmeas hbdd hind
  classical
  set n := Module.finrank ℤ E
  let b : Module.Basis (Fin n) ℤ E := Module.finBasis ℤ E
  have hmem : ∀ s, MemLp (w s) 2 μ := fun s => by
    obtain ⟨C, hC⟩ := hbdd s
    exact (memLp_top_of_bound (hmeas s) C hC).mono_exponent le_top
  let F : Fin n → Lp ℂ 2 μ := fun i => (hmem (b i)).toLp _
  let ψ : (Fin n → ℝ) →ₗ[ℝ] Lp ℂ 2 μ :=
    { toFun := fun c => ∑ i, c i • F i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }

  have hψ : ∀ c : Fin n → ℝ, (ψ c : X → ℂ) =ᵐ[μ] fun z => ∑ i, (c i : ℂ) * w (b i) z := by
    intro c
    show ((∑ i, c i • F i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] _
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero ℂ 2 μ] with z h
      rw [h]
      rfl
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • F i) (∑ j ∈ s, c j • F j), Lp.coeFn_smul (c i) (F i),
        (hmem (b i)).coeFn_toLp, ih] with z h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Complex.real_smul]
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    apply hind n b b.linearIndependent c
    filter_upwards [hψ c, hc ▸ Lp.coeFn_zero ℂ 2 μ] with z h1 h2
    rw [← h1]
    exact h2

  have hcoord : ∀ s : E, ψ (fun i => (b.equivFun s i : ℝ)) = (hmem s).toLp _ := by
    intro s
    ext1
    filter_upwards [hψ (fun i => (b.equivFun s i : ℝ)), (hmem s).coeFn_toLp] with z h1 h2
    have hs : w s = ∑ i, b.repr s i • w (b i) := by
      conv_lhs => rw [← b.sum_repr s]
      rw [map_sum]
      simp only [map_zsmul]
    rw [h1, h2, hs, Finset.sum_apply]
    simp [zsmul_eq_mul]
  let W := LinearMap.range ψ
  let e₁ : (Fin n → ℝ) ≃ₗ[ℝ] W := LinearEquiv.ofInjective ψ hinj
  have hW : Module.finrank ℝ W = n := by
    rw [← e₁.finrank_eq, Module.finrank_fin_fun]
  let o := (stdOrthonormalBasis ℝ W).reindex (finCongr hW)
  let T : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := e₁.trans o.repr.toLinearEquiv
  have hT : ∀ c, ‖T c‖ = ‖ψ c‖ := by
    intro c
    simp only [T, e₁, LinearEquiv.trans_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map]
    rw [Submodule.coe_norm, LinearEquiv.ofInjective_apply]
  let cast : (Fin n → ℤ) →+ (Fin n → ℝ) := AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin n)
  let φ : E →+ EuclideanSpace ℝ (Fin n) :=
    (T.toLinearMap.toAddMonoidHom.comp cast).comp b.equivFun.toLinearMap.toAddMonoidHom
  have hφ : ∀ s, φ s = T (fun i => (b.equivFun s i : ℝ)) := fun s => rfl
  let v : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := (Pi.basisFun ℝ (Fin n)).map T
  have hφb : ∀ i, φ (b i) = v i := by
    intro i
    rw [hφ]
    simp only [v, Module.Basis.map_apply, Pi.basisFun_apply, Module.Basis.equivFun_self]
    congr 1
    funext j
    by_cases h : i = j <;> simp [h, eq_comm]
  have hL : imageLattice φ = Submodule.span ℤ (Set.range v) := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      rw [← b.sum_repr s, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul, hφb]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨b i, hφb i⟩
  have key : ∀ L : Submodule ℤ (EuclideanSpace ℝ (Fin n)), L = Submodule.span ℤ (Set.range v) →
      DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L := by
    rintro _ rfl
    exact ⟨inferInstance, by intro _; infer_instance⟩
  refine ⟨φ, ?_, (key _ hL).1, (key _ hL).2, ?_⟩
  · intro s t hst
    rw [hφ, hφ] at hst
    apply b.equivFun.injective
    funext i
    exact_mod_cast congrFun (T.injective hst) i
  · intro s
    rw [hφ, hT, hcoord, Lp.norm_toLp,
      MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top (hmem s),
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAmpleOfGenTwist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem AmpleOfGenTwist.proof (hGen : GenTwistGenerated.Statement) (hVan : GenTwistVanish.Statement) :
    AmpleOfGenTwist.Statement := by
  intro S _ K _ _ ι _ _ V α p q hV hα hp
  refine ⟨1, le_rfl, ?_, fun e => ?_⟩
  · rw [one_smul]
    exact hGen S K ι V α q p hα
  · obtain ⟨c₀, hc₀⟩ := hVan S K ι V α hV hα e
    refine ⟨c₀, fun c hc => ?_⟩
    have hN : e + (c * 1) • ((q : ℤ) • α + fun _ => (p : ℤ)) =
        e + ((c * q : ℕ) : ℤ) • α + fun _ => ((c * p : ℕ) : ℤ) := by
      funext k
      change e k + (c * 1) • ((q : ℤ) • α k + (p : ℤ)) = e k + ((c * q : ℕ) : ℤ) • α k + ((c * p : ℕ) : ℤ)
      simp only [nsmul_eq_mul, smul_eq_mul]
      push_cast
      ring
    rw [hN]
    exact hc₀ (c * q) (c * p) (le_trans hc (Nat.le_mul_of_pos_right c hp))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleimanTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedKleimanTop.Statement : Prop :=
  ∀ d : ℕ, 2 ≤ d → MixedKleiman.AtDim (d - 1) → MixedKleiman.LowAt d → MixedKleiman.TopAt d

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

