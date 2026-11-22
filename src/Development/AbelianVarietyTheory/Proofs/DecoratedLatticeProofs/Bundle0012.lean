import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetIntegralScaledBoxPiCosetReps
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.BoxReps

def boxSubgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) (s : kˣ) : AddSubgroup (n → k) where
  carrier := box n s
  add_mem' hx hy i _ := add_mem_cball (hx i trivial) (hy i trivial)
  zero_mem' i _ := by simp [cball]
  neg_mem' hx i _ := neg_mem_cball (hx i trivial)

theorem exists_finset_box_reps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ), valuation k (r : k) ≤ valuation k (R : k) → ∃ S : Finset (n → k), (∀ b ∈ S, b ∈ box n R) ∧ ∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r := by
  intro k _ _ _ _ n _ r R _
  classical
  set H := boxSubgroup k n r
  have hH : ∀ x, x ∈ H ↔ x ∈ box n r := fun _ => Iff.rfl
  have hq : ∀ a b : n → k, (QuotientAddGroup.mk a : (n → k) ⧸ H) = QuotientAddGroup.mk b ↔ a - b ∈ box n r := by
    intro a b
    rw [QuotientAddGroup.eq, ← hH, ← H.neg_mem_iff]
    simp [neg_add_eq_sub]
  obtain ⟨T, hTsub, hTfin, hcov⟩ := (isCompact_box (n := n) R).elim_finite_subcover_image
    (b := box n R) (c := fun a => (fun x => x - a) ⁻¹' box n r)
    (fun a _ => (isOpen_box r).preimage (continuous_id.sub continuous_const))
    (fun x hx => Set.mem_biUnion hx (show x - x ∈ box n r by rw [sub_self]; exact (boxSubgroup k n r).zero_mem))
  set π : (n → k) → (n → k) ⧸ H := QuotientAddGroup.mk
  let f : (n → k) ⧸ H → (n → k) := fun q =>
    if h : ∃ a ∈ box n R, π a = q then Classical.choose h else 0
  have hf : ∀ a ∈ box n R, f (π a) ∈ box n R ∧ π (f (π a)) = π a := by
    intro a ha
    have h : ∃ b ∈ box n R, π b = π a := ⟨a, ha, rfl⟩
    simp only [f, dif_pos h]
    exact Classical.choose_spec h
  refine ⟨(hTfin.toFinset.image π).image f, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hb
    obtain ⟨q, ⟨t, ht, rfl⟩, rfl⟩ := hb
    exact (hf t (hTsub ht)).1
  · intro a ha
    obtain ⟨t, ht, hat⟩ := Set.mem_iUnion₂.mp (hcov ha)
    have hat' : π a = π t := (hq a t).mpr hat
    refine ⟨f (π a), ⟨?_, ?_⟩, ?_⟩
    · simp only [Finset.mem_image, Set.Finite.mem_toFinset]
      exact ⟨π t, ⟨t, ht, rfl⟩, by rw [hat']⟩
    · exact (hq a _).mp (hf a ha).2.symm
    · rintro b ⟨hb, hab⟩
      simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hb
      obtain ⟨q, ⟨t', ht', rfl⟩, rfl⟩ := hb
      have h1 : π a = π (f (π t')) := (hq a _).mpr hab
      rw [(hf t' (hTsub ht')).2] at h1
      rw [h1]

end GlobalTheory.BoxReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetNormOne
section
noncomputable section

open NumberField IsDedekindDomain Topology Filter

namespace GlobalTheory.HeckeSplitAll.Approx

variable {F : Type} [Field F] [NumberField F]

theorem norm_alg_inf (w : InfinitePlace F) (x : F) : ‖algebraMap F w.Completion x‖ = w x := by
  rw [show algebraMap F w.Completion x = (x : w.Completion) from rfl]
  simp only [InfinitePlace.Completion.norm_ofCompletion, UniformSpace.Completion.norm_coe]; rfl

theorem norm_le_one_iff_int (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem norm_nat_le_one (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) : ‖(m : v.adicCompletion F)‖ ≤ 1 :=
  (norm_le_one_iff_int v _).2 (natCast_mem _ m)

theorem norm_int_le_one (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) :
    ‖algebraMap F (v.adicCompletion F) (o : F)‖ ≤ 1 :=
  (norm_le_one_iff_int v _).2 (PI.UnipApproxD.IntegersDenseFiniteAdeles.int_R v o)

theorem norm_int_eq_one (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) (ho : o ∉ v.asIdeal) :
    ‖algebraMap F (v.adicCompletion F) (o : F)‖ = 1 := by
  refine le_antisymm (norm_int_le_one v o) (not_lt.1 fun h => ho ?_)
  rw [Valued.toNormedField.norm_lt_one_iff] at h
  have e := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R (K := F) v o
  rw [show algebraMap F (v.adicCompletion F) (o : F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F o) from rfl,
    e] at h
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v o).1 h

theorem nat_ne_zero_fin (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (hm : m ≠ 0) : (m : v.adicCompletion F) ≠ 0 := by
  have h := (algebraMap F (v.adicCompletion F)).injective.ne (Nat.cast_ne_zero.2 hm : (m : F) ≠ 0)
  rwa [map_natCast, map_zero] at h

theorem norm_natCast_lt_one (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : (c : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hval := (HeightOneSpectrum.intValuation_lt_one_iff_mem v (c : 𝓞 F)).2 hmem
  rw [Valued.toNormedField.norm_lt_one_iff]
  have e := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R (K := F) v (c : 𝓞 F)
  rw [map_natCast, map_natCast] at e
  rw [e]
  exact hval

theorem exists_finset_norm_one (x : F) (hx : x ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ‖algebraMap F (v.adicCompletion F) x‖ = 1 := by
  classical
  have h1 := Filter.eventually_cofinite.mp (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2
  have h2 := Filter.eventually_cofinite.mp (algebraMap F (FiniteAdeleRing (𝓞 F) F) x⁻¹).2
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hv
  obtain ⟨ha, hb⟩ := hv
  have ha' : ‖algebraMap F (v.adicCompletion F) x‖ ≤ 1 := (norm_le_one_iff_int v _).2 ha
  have hb' : ‖algebraMap F (v.adicCompletion F) x⁻¹‖ ≤ 1 := (norm_le_one_iff_int v _).2 hb
  rw [map_inv₀, norm_inv] at hb'
  have hpos : 0 < ‖algebraMap F (v.adicCompletion F) x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
  have hm := mul_inv_cancel₀ hpos.ne'
  refine le_antisymm ha' ?_
  nlinarith [mul_nonneg hpos.le (sub_nonneg.2 hb')]

theorem exists_nat_small (x : F) (hx : x ≠ 0) : ∃ P : ℕ, P ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
    ‖algebraMap F (v.adicCompletion F) x‖ ≠ 1 → ‖(P : v.adicCompletion F)‖ < 1 := by
  classical
  obtain ⟨B, hB⟩ := exists_finset_norm_one x hx
  refine ⟨∏ v ∈ B, Ideal.absNorm v.asIdeal, ?_, fun v hv => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)).ne'
  · exact norm_natCast_lt_one v _ (Finset.dvd_prod_of_mem _ (by_contra fun h => hv (hB v h)))

theorem exists_int_near (F : Type) [Field F] [NumberField F] : ∃ C : ℝ, 0 < C ∧ ∀ t : InfiniteAdeleRing F,
    ∃ o : 𝓞 F, ∀ w : InfinitePlace F, ‖algebraMap F w.Completion (o : F) - t w‖ < C := by
  classical
  set b := integralBasis F with hb
  refine ⟨1 + ∑ w : InfinitePlace F, ∑ i, w (b i), by positivity, fun t => ?_⟩
  have hopen : IsOpen {y : InfiniteAdeleRing F | ∀ w, ‖y w - t w‖ < 1} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (((continuous_apply w : Continuous fun y : InfiniteAdeleRing F => y w).sub
        continuous_const).norm) continuous_const
  obtain ⟨f, hf⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hopen
    ⟨t, fun w => by
      show ‖t w - t w‖ < 1
      rw [sub_self, norm_zero]; exact one_pos⟩
  have hf' : ∀ w, ‖algebraMap F w.Completion f - t w‖ < 1 := hf
  refine ⟨∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i, fun w => ?_⟩
  have e : ((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f =
      ∑ i, (((⌊b.repr f i⌋ : ℚ) - b.repr f i : ℚ) : F) * b i := by
    conv_lhs => arg 2; rw [← b.sum_repr f]
    rw [show ((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) =
      algebraMap (𝓞 F) F (∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i) from rfl, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← integralBasis_apply, ← hb, Rat.smul_def, zsmul_eq_mul]
    push_cast
    ring
  have h2 : ‖algebraMap F w.Completion (((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f)‖ ≤
      ∑ i, w (b i) := by
    rw [e, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_alg_inf, map_mul]
    refine mul_le_of_le_one_left (apply_nonneg _ _) ?_
    rw [← InfinitePlace.norm_embedding_eq, map_ratCast, Complex.norm_ratCast, ← Rat.cast_abs, ← Rat.cast_one, Rat.cast_le,
      abs_le]
    constructor <;> linarith [Int.floor_le (b.repr f i), Int.lt_floor_add_one (b.repr f i)]
  have h3 : ∑ i, w (b i) ≤ ∑ w : InfinitePlace F, ∑ i, w (b i) :=
    Finset.single_le_sum (f := fun w : InfinitePlace F => ∑ i, w (b i))
      (fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _) (Finset.mem_univ w)
  have h4 := norm_add_le (algebraMap F w.Completion (((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f))
    (algebraMap F w.Completion f - t w)
  rw [map_sub, sub_add_sub_cancel, ← map_sub] at h4
  linarith [hf' w]

open NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory ENNReal Module in
open scoped nonZeroDivisors in

theorem exists_small_elt (v₀ : HeightOneSpectrum (𝓞 F)) (η : ℝ) (hη : 0 < η) :
    ∃ x : F, x ≠ 0 ∧ (∀ w : InfinitePlace F, w x < η) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ → ‖algebraMap F (v.adicCompletion F) x‖ ≤ 1 := by
  classical
  let f : InfinitePlace F → NNReal := fun _ => ⟨η, hη.le⟩
  have hV : volume (convexBodyLT F f) ≠ ⊤ := by
    rw [convexBodyLT_volume]; exact mul_ne_top coe_ne_top coe_ne_top
  have hV0 : 0 < (volume (convexBodyLT F f)).toReal := by
    rw [convexBodyLT_volume, toReal_mul, coe_toReal, coe_toReal]
    have h1 : (1 : ℝ) ≤ convexBodyLTFactor F := by exact_mod_cast one_le_convexBodyLTFactor F
    refine mul_pos (by linarith) ?_
    rw [NNReal.coe_prod]
    exact Finset.prod_pos fun w _ => by rw [NNReal.coe_pow]; exact pow_pos hη _
  set B : ℝ := (volume (ZSpan.fundamentalDomain (latticeBasis F))).toReal * 2 ^ finrank ℝ (mixedSpace F) with hB
  have hq : (1 : ℝ) < Ideal.absNorm v₀.asIdeal := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v₀
  have ht : Tendsto (fun k : ℕ => ((Ideal.absNorm v₀.asIdeal : ℝ)⁻¹) ^ k * B) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (Ideal.absNorm v₀.asIdeal : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hq)).mul_const B
    rwa [zero_mul] at this
  obtain ⟨k, hk⟩ := (ht.eventually (Iio_mem_nhds hV0)).exists
  have hI : ((v₀.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero k v₀.ne_bot)
  let J : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 _ (inv_ne_zero hI)
  have h : minkowskiBound F J < volume (convexBodyLT F f) := by
    rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top F J).ne hV]
    refine lt_of_eq_of_lt ?_ hk
    rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis, toReal_mul, toReal_mul, toReal_pow,
      ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)), hB]
    simp only [J, Units.val_mk0, map_inv₀, FractionalIdeal.coeIdeal_absNorm, map_pow, toReal_ofNat]
    push_cast
    rw [inv_pow]
    ring
  obtain ⟨a, ha, hne, hlt⟩ := exists_ne_zero_mem_ideal_lt F J h
  refine ⟨a, hne, fun w => hlt w, fun v hv => ?_⟩
  obtain ⟨p, hp0, hpv⟩ : ∃ p ∈ v₀.asIdeal, p ∉ v.asIdeal := by
    by_contra hc
    push Not at hc
    exact hv (HeightOneSpectrum.ext (v₀.isMaximal.eq_of_le v.isPrime.ne_top hc).symm)
  have hm : a * algebraMap (𝓞 F) F (p ^ k) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← inv_mul_cancel₀ hI]
    exact FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.pow_mem_pow hp0 k))
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  have h1 := norm_int_le_one v o
  rw [show (o : F) = algebraMap (𝓞 F) F o from rfl, ho, map_mul, norm_mul, map_pow, map_pow, norm_pow] at h1
  have h2 := norm_int_eq_one v p hpv
  rw [show (p : F) = algebraMap (𝓞 F) F p from rfl] at h2
  rwa [h2, one_pow, mul_one] at h1

theorem strong_approx (v₀ : HeightOneSpectrum (𝓞 F)) (t : InfiniteAdeleRing F) (s : FiniteAdeleRing (𝓞 F) F)
    (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : F, c ≠ 0 ∧ (∀ w : InfinitePlace F, ‖algebraMap F w.Completion c - t w‖ < ε) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        ‖algebraMap F (v.adicCompletion F) c - s v‖ ≤ ‖(M : v.adicCompletion F)‖ := by
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMR : (0 : ℝ) < M := Nat.cast_pos.2 (Nat.pos_of_ne_zero hM)
  obtain ⟨u, hu⟩ := PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_approx_adele
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F)⁻¹ * s)
  obtain ⟨C, hC, hCt⟩ := exists_int_near F
  obtain ⟨x, hx0, hxw, hxv⟩ := exists_small_elt v₀ (ε / (M * (C + 1))) (by positivity)
  obtain ⟨o, ho⟩ := hCt fun w => (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)
  have key : ∀ o' : 𝓞 F, (∀ w : InfinitePlace F, ‖algebraMap F w.Completion (o' : F) -
      (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)‖ < C + 1) →
      (∀ w : InfinitePlace F, ‖algebraMap F w.Completion (M * u + M * x * o') - t w‖ < ε) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        ‖algebraMap F (v.adicCompletion F) (M * u + M * x * o') - s v‖ ≤ ‖(M : v.adicCompletion F)‖ := by
    intro o' ho'
    refine ⟨fun w => ?_, fun v hv => ?_⟩
    · have h0 : algebraMap F w.Completion (M * x) ≠ 0 := (map_ne_zero _).2 (mul_ne_zero hMF hx0)
      have e : algebraMap F w.Completion (M * u + M * x * o') - t w = algebraMap F w.Completion (M * x) *
          (algebraMap F w.Completion (o' : F) -
            (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)) := by
        rw [map_add, map_mul _ (M * x), mul_sub, mul_div_cancel₀ _ h0]; ring
      rw [e, norm_mul, norm_alg_inf, map_mul, InfinitePlace.map_natCast]
      calc _ ≤ (M * w x) * (C + 1) := mul_le_mul_of_nonneg_left (ho' w).le (by positivity)
        _ < (M * (ε / (M * (C + 1)))) * (C + 1) := by gcongr; exact hxw w
        _ = ε := by field_simp
    · have h0 := nat_ne_zero_fin v hM
      have hu' : ‖algebraMap F (v.adicCompletion F) (M : F)⁻¹ * s v - algebraMap F (v.adicCompletion F) u‖ ≤ 1 :=
        (norm_le_one_iff_int v _).2 (hu v)
      have e : algebraMap F (v.adicCompletion F) (M * u + M * x * o') - s v = (M : v.adicCompletion F) *
          (-(algebraMap F (v.adicCompletion F) (M : F)⁻¹ * s v - algebraMap F (v.adicCompletion F) u) +
            algebraMap F (v.adicCompletion F) x * algebraMap F (v.adicCompletion F) (o' : F)) := by
        simp only [map_add, map_mul, map_inv₀, map_natCast]
        field_simp
        ring
      rw [e, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))
      · rwa [norm_neg]
      · rw [norm_mul]; exact mul_le_one₀ (hxv v hv) (norm_nonneg _) (norm_int_le_one v o')
  by_cases hc : (M : F) * u + M * x * o = 0
  · refine ⟨M * u + M * x * (o + 1 : 𝓞 F), ?_, key (o + 1) fun w => ?_⟩
    · have : (M : F) * u + M * x * (o + 1 : 𝓞 F) = M * x := by push_cast; linear_combination hc
      rw [this]; exact mul_ne_zero hMF hx0
    · have h1 := norm_add_le (1 : w.Completion) (algebraMap F w.Completion (o : F) -
        (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x))
      have e : ((o + 1 : 𝓞 F) : F) = 1 + o := by push_cast; ring
      rw [e, map_add, map_one, add_sub_assoc]
      rw [norm_one] at h1
      linarith [ho w]
  · exact ⟨_, hc, key o fun w => (ho w).trans (lt_add_one C)⟩

end GlobalTheory.HeckeSplitAll.Approx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralScaledBoxPiSupersetOfIsCompact
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

namespace GlobalTheory

theorem box_subset_box_of_valuation_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) {s t : kˣ}
    (h : valuation k (s : k) ≤ valuation k (t : k)) : box n s ⊆ box n t :=
  fun x hx i _ => show valuation k (x i) ≤ _ from le_trans (hx i trivial) h

theorem exists_box_superset_of_isCompact (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (K : Set (n → k)) :
    IsCompact K → ∀ r : kˣ, ∃ R : kˣ, valuation k (r : k) ≤ valuation k (R : k) ∧ K ⊆ box n R := by
  intro hK r
  let ι := {s : kˣ // valuation k (r : k) ≤ valuation k (s : k)}
  haveI : Nonempty ι := ⟨⟨r, le_rfl⟩⟩
  have hcov : K ⊆ ⋃ s : ι, box n (s : kˣ) := by
    intro x _
    rw [Set.mem_iUnion]
    by_cases hn : Nonempty n
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => valuation k (x i))
        Finset.univ_nonempty
      by_cases hle : valuation k (x i0) ≤ valuation k (r : k)
      · refine ⟨⟨r, le_rfl⟩, fun i _ => ?_⟩
        exact le_trans (hi0 i (Finset.mem_univ i)) hle
      · push_neg at hle
        have hx0 : x i0 ≠ 0 := by
          intro h0
          rw [h0, map_zero] at hle
          exact not_lt_zero' hle
        refine ⟨⟨Units.mk0 (x i0) hx0, by simpa using hle.le⟩, fun i _ => ?_⟩
        simpa [cball] using hi0 i (Finset.mem_univ i)
    · refine ⟨⟨r, le_rfl⟩, fun i _ => (hn ⟨i⟩).elim⟩
  have hdir : Directed (· ⊆ ·) (fun s : ι => box n (s : kˣ)) := by
    intro s t
    rcases le_total (valuation k ((s : kˣ) : k)) (valuation k ((t : kˣ) : k)) with h | h
    · exact ⟨t, box_subset_box_of_valuation_le n h, le_rfl⟩
    · exact ⟨s, le_rfl, box_subset_box_of_valuation_le n h⟩
  obtain ⟨s, hs⟩ := hK.elim_directed_cover (fun s : ι => box n (s : kˣ))
    (fun s => isOpen_box _) hcov hdir
  exact ⟨s, s.2, hs⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBoxInvariantEqMeasureRealMulSumReps
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil.FourierPi

theorem integral_eq_measureReal_box_mul_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)), (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) → ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) → (∀ y ∉ box n R, F y = 0) → ∫ y, F y ∂(Measure.pi fun _ => ν) = ((Measure.pi fun _ : n => ν).real (box n r) : ℂ) * ∑ b ∈ S, F b := by
  intro k _ _ _ _ _ _ ν hν n _ r R S hS hrep F hF hF0
  classical
  have : ν.IsAddHaarMeasure := hν
  have : SecondCountableTopology k := secondCountable k
  have : SigmaFinite ν := inferInstance
  have : (Measure.pi fun _ : n => ν).IsAddHaarMeasure := inferInstance
  set μ : Measure (n → k) := Measure.pi fun _ => ν
  have hmeas : MeasurableSet (box n r) :=
    MeasurableSet.univ_pi fun _ => (isOpen_cball r).measurableSet
  have hfin : μ (box n r) < ⊤ := (isCompact_box r).measure_lt_top

  have key : ∀ y, F y = ∑ b ∈ S, (box n r).indicator (fun _ => F b) (y - b) := by
    intro y
    by_cases hy : y ∈ box n R
    · obtain ⟨b, ⟨hbS, hb⟩, huniq⟩ := hrep y hy
      rw [Finset.sum_eq_single b]
      · rw [Set.indicator_of_mem hb]
        have h := hF (y - b) hb b
        rwa [add_sub_cancel] at h
      · intro b' hb'S hne
        have hnot : y - b' ∉ box n r := fun hmem => hne (huniq b' ⟨hb'S, hmem⟩)
        exact Set.indicator_of_notMem hnot _
      · intro hbn
        exact absurd hbS hbn
    · rw [hF0 y hy]
      symm
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hmem : y - b ∈ box n r
      · rw [Set.indicator_of_mem hmem]
        have h := hF (y - b) hmem b
        rw [add_sub_cancel] at h
        rw [← h, hF0 y hy]
      · exact Set.indicator_of_notMem hmem _
  have hint : ∀ b ∈ S, Integrable (fun y => (box n r).indicator (fun _ => F b) (y - b)) μ := by
    intro b _
    have h1 : Integrable ((box n r).indicator fun _ : n → k => F b) μ := by
      refine (integrable_indicator_iff hmeas).2 ?_
      exact integrableOn_const hfin.ne
    exact h1.comp_sub_right b
  calc ∫ y, F y ∂μ = ∫ y, ∑ b ∈ S, (box n r).indicator (fun _ => F b) (y - b) ∂μ := by
        congr 1
        funext y
        exact key y
    _ = ∑ b ∈ S, ∫ y, (box n r).indicator (fun _ => F b) (y - b) ∂μ := integral_finsetSum S hint
    _ = ∑ b ∈ S, (μ.real (box n r) : ℂ) * F b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [integral_sub_right_eq_self (fun y => (box n r).indicator (fun _ => F b) y) b,
          integral_indicator_const _ hmeas, Complex.real_smul]
    _ = _ := by rw [Finset.mul_sum]

end GlobalTheory.SplitWeil.FourierPi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralLastFactorSliceMemSchwartzBruhat
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SliceIntegral

theorem integral_slice_mem_SB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂]
    (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) :
    (fun x => ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∈ SB (I₀ → k) := by
  haveI := t2Space k
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro (IsCompact.image Φ.2.2 continuous_fst) fun x hx => ?_⟩
  · have ht : Filter.Tendsto (fun x' : I₀ → k => ((x - x', (0 : I₁ → k), (0 : I₂ → k)) :
        (I₀ → k) × (I₁ → k) × (I₂ → k))) (𝓝 x) (𝓝 0) := by
      have hc : Continuous (fun x' : I₀ → k => ((x - x', (0 : I₁ → k), (0 : I₂ → k)) :
          (I₀ → k) × (I₁ → k) × (I₂ → k))) := by fun_prop
      have := hc.tendsto x
      rwa [sub_self, ← Prod.zero_eq_mk, ← Prod.zero_eq_mk] at this
    filter_upwards [ht.eventually (GlobalTheory.SBConv.eventually_translate Φ.2)] with x' hx'
    congr 1
    funext a
    have := hx' (x, 0, a)
    simpa using this
  · have h0 : ∀ a, Φ.1 (x, 0, a) = 0 := fun a =>
      image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩
    simp [h0]

end GlobalTheory.SliceIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelReducedIntegralFormBoundedEntriesStatement
section
open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelReduced_integral_form_bounded_entries : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ) (B B' : Matrix (Fin N) (Fin N) ℤ) (μ : ℝ), μ ≠ 0 → |μ| ≤ R → (∀ i j, |X i j| ≤ R) → B.map (Int.cast : ℤ → ℝ) = (k * diagonal a * n)ᵀ * X * (k * diagonal a * n) → (k * diagonal a * n) * B'.map (Int.cast : ℤ → ℝ) * (k * diagonal a * n)ᵀ = μ • X → ∀ i j, |(B i j : ℝ)| ≤ C' := by
  first | exact @GlobalTheory.RedBound.reduced_bound | exact GlobalTheory.RedBound.reduced_bound | (intros; apply GlobalTheory.RedBound.reduced_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralScaledBoxPiCosetRepsShiftInvariant
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

namespace GlobalTheory.CosetSumShift

theorem sum_shift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)),
    (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) →
    ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) →
    ∀ a ∈ box n R, ∑ b ∈ S, F (a + b) = ∑ b ∈ S, F b := by
  intro k _ _ _ _ n _ r R S hS huniq F hF a ha
  classical
  have hadd : ∀ {s : kˣ} {x y : n → k}, x ∈ box n s → y ∈ box n s → x + y ∈ box n s :=
    fun hx hy i _ => add_mem_cball (hx i trivial) (hy i trivial)
  have hneg : ∀ {s : kˣ} {x : n → k}, x ∈ box n s → -x ∈ box n s :=
    fun hx i _ => neg_mem_cball (hx i trivial)
  have hzero : (0 : n → k) ∈ box n r := fun i _ => by simp [cball]
  have hmem : ∀ b ∈ S, a + b ∈ box n R := fun b hb => hadd ha (hS b hb)
  choose! c hc using fun b (hb : b ∈ S) => (huniq (a + b) (hmem b hb)).exists
  have hF' : ∀ b ∈ S, F (a + b) = F (c b) := by
    intro b hb
    have := hF _ (hc b hb).2 (c b)
    rwa [add_sub_cancel] at this
  have hinj : ∀ x ∈ S, ∀ y ∈ S, c x = c y → x = y := by
    intro x hx y hy h
    have e : x - y = (a + x - c x) + -(a + y - c y) := by rw [h]; abel
    have h1 : x - y ∈ box n r := e ▸ hadd (hc x hx).2 (hneg (hc y hy).2)
    obtain ⟨z, -, huq⟩ := huniq x (hS x hx)
    exact (huq x ⟨hx, by simpa using hzero⟩).trans (huq y ⟨hy, h1⟩).symm
  have himg : S.image c = S := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      exact (hc b hb).1
    · rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)]
  rw [Finset.sum_congr rfl hF', ← Finset.sum_image hinj, himg]

end GlobalTheory.CosetSumShift
end

