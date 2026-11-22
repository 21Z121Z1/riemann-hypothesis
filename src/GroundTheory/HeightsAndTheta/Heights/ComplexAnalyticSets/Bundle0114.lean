import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0102
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0105
import GroundTheory.HeightsAndTheta.Theta.SplitLinear.RankMinors
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0108
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0109

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Matrix

noncomputable section

theorem PosPartIndep.proof (h : SheetOnlyNull.Statement) (hL : PosPartLocal.Statement)
    (hS : PosPartSplit.Statement) : PosPartIndep.Statement := by
  intro n d J A A' f φ hJ hd hA hA' hf hφ

  have key : ∀ x : Fin n → ℂ, ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      ((∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') → x ∈ W) ∧
      ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) =
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A' (E.indicator f) φ y) := by
    intro x
    by_cases hx : (∃ s, IsSheetAt J A x s) ∧ ∃ s', IsSheetAt J A' x s'
    · obtain ⟨W, hW, hxW, hWE⟩ := hL n d J A A' f φ x hf hφ hx.1 hx.2
      exact ⟨W, hW, fun _ _ => hxW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun h1 h2 => absurd ⟨h1, h2⟩ hx, fun E _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [chartPosDens, sheetSum]
  choose W hWo hxW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (SheetSumMeasurable.isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hWo (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ W (e k) := fun k x hx => disjointed_subset (fun k => W (e k)) k hx.2
  have hEd : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
    ((disjoint_disjointed (fun k => W (e k))) hij).mono Set.inter_subset_right
      Set.inter_subset_right
  have hcov : ∀ x ∈ zeroSet J, (∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') →
      ∃ k, x ∈ E k := by
    intro x hxZ h1 h2
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x h1 h2⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hxi⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  have hae : ∀ B B' : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J B → IsFiniteProjection J B' →
      (∀ x ∈ zeroSet J, (∃ s, IsSheetAt J B x s) → (∃ s', IsSheetAt J B' x s') → ∃ k, x ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y) := by
    intro B B' hB hB' hc
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h n d J B B' hJ hd hB hB')] with y hy
    refine hS n d J B f φ E y hB hEd fun x hx hs => hc x hx.1 hs ?_
    by_contra hn
    exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2⟩
  have hint : ∀ B : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J B →
      (∀ᵐ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y)) →
      ∫⁻ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y) := by
    intro B hB hB2
    rw [lintegral_congr_ae hB2, lintegral_tsum fun k =>
      (IntegralIndep.measurable_chartPosDens hB (hf.indicator (hEm k)) φ).ennreal_ofReal.aemeasurable]
  rw [hint A hA (hae A A' hA hA' hcov),
    hint A' hA' (hae A' A hA' hA fun x hx h1 h2 => hcov x hx h2 h1)]
  exact tsum_congr fun k => hWE (e k) (E k) (hEm k) (hEW k)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeBranchDimOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem PrimeBranchDimOne.proof : PrimeBranchDimOne.Statement := by
  intro n J q c hJ hloc

  have hq : q ∈ zeroSet J := by
    have := c.mapsTo (Metric.mem_ball_self c.radius_pos)
    rwa [c.map_zero] at this

  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    have h1 := ringKrullDim_quotient_le J
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ringKrullDim_nonneg_of_nontrivial
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (e : ℕ) := by
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at hle hnn
    induction d using WithBot.recBotCoe with
    | bot => exact absurd hnn (by simp)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hle
        exact absurd (WithBot.coe_le_coe.mp h3) (by simp)
      | coe e => exact ⟨e, rfl⟩
  have hdim : ringKrullDim (localRingAt J q) = (e : ℕ) := LocalDimDomain.proof n e J hJ he q hq
  have he1 : e ≤ 1 := by
    have h2 : ((e : ℕ) : WithBot ℕ∞) ≤ 1 := hdim ▸ hloc
    exact_mod_cast h2
  rw [he]
  obtain h0 | h1 : e = 0 ∨ e = 1 := by omega
  swap
  · rw [h1]
  exfalso
  subst h0

  have hfield : IsField (MvPolynomial (Fin n) ℂ ⧸ J) := by
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (ringKrullDimZero_iff_ringKrullDim_eq_zero).2 (by simpa using he)
    exact Ring.KrullDimLE.isField_of_isDomain
  have hmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField J hfield
  have hJM : J = RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) :=
    hmax.eq_of_le (RingHom.ker_ne_top _) (fun f hf => RingHom.mem_ker.mpr (hq f hf))

  have hZ : ∀ x ∈ zeroSet J, x = q := by
    intro x hx
    funext i
    have hmem : X i - C (q i) ∈ J := by
      rw [hJM, RingHom.mem_ker]
      simp
    have := hx _ hmem
    simp only [map_sub, eval_X, eval_C] at this
    exact sub_eq_zero.mp this

  set r := c.radius
  let v : Fin 1 → ℂ := fun _ => ((r / 2 : ℝ) : ℂ)
  have hv : v ∈ Metric.ball (0 : Fin 1 → ℂ) r := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff c.radius_pos]
    intro i
    simp only [v, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (half_pos c.radius_pos)]
    exact half_lt_self c.radius_pos
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := Metric.mem_ball_self c.radius_pos
  have heq : c.toFun v = c.toFun 0 := by
    rw [hZ _ (c.mapsTo hv), hZ _ (c.mapsTo h0)]
  have := congrFun (c.injOn hv h0 heq) 0
  simp only [v, Pi.zero_apply, Complex.ofReal_eq_zero] at this
  exact (half_pos c.radius_pos).ne' this

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionUnramifiedGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjectionUnramifiedGeneric

theorem pderiv_inr_rename_inl {α β : Type} (b : β) (a : MvPolynomial α ℂ) :
    pderiv (Sum.inr b) (rename (Sum.inl : α → α ⊕ β) a) = 0 := by
  classical
  induction a using MvPolynomial.induction_on with
  | C c => simp
  | add p p' hp hp' => simp [hp, hp']
  | mul_X p i hp => simp [pderiv_mul, hp, pderiv_X, Pi.single_apply]

theorem proof : ProjectionUnramifiedGeneric.Statement := by
  classical
  intro α β _ _ Q r q t hQ hint hqQ htQ hgen
  let L := FractionRing (MvPolynomial (α ⊕ β) ℂ ⧸ Q)
  let φ : MvPolynomial (α ⊕ β) ℂ →+* L := (algebraMap (MvPolynomial (α ⊕ β) ℂ ⧸ Q) L).comp (Ideal.Quotient.mk Q)
  have hφ : ∀ p, φ p = 0 ↔ p ∈ Q := by
    intro p
    have hinj := IsFractionRing.injective (MvPolynomial (α ⊕ β) ℂ ⧸ Q) L
    simp only [φ, RingHom.comp_apply]
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_zero (algebraMap (MvPolynomial (α ⊕ β) ℂ ⧸ Q) L)]
    exact hinj.eq_iff
  let ι : MvPolynomial α ℂ →+* MvPolynomial (α ⊕ β) ℂ := (rename Sum.inl : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial (α ⊕ β) ℂ).toRingHom

  let D : (β → L) → MvPolynomial (α ⊕ β) ℂ → L := fun c p => ∑ b, φ (pderiv (Sum.inr b) p) * c b
  have hDadd : ∀ c p p', D c (p + p') = D c p + D c p' := by
    intro c p p'
    simp only [D, map_add, add_mul, Finset.sum_add_distrib]
  have hDmul : ∀ c p p', D c (p * p') = φ p * D c p' + φ p' * D c p := by
    intro c p p'
    simp only [D]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [pderiv_mul]
    simp only [map_add, map_mul]
    ring
  have hDsum : ∀ c (f : Fin r → MvPolynomial (α ⊕ β) ℂ), D c (∑ j, f j) = ∑ j, D c (f j) := by
    intro c f
    simp only [D, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hDX : ∀ c b, D c (X (Sum.inr b)) = c b := by
    intro c b
    simp [D, pderiv_X, Pi.single_apply]
  have hDι : ∀ c a, D c (ι a) = 0 := by
    intro c a
    simp [D, ι, pderiv_inr_rename_inl]
  have hDpoly : ∀ c b (G : Polynomial (MvPolynomial α ℂ)),
      D c (G.eval₂ ι (X (Sum.inr b))) =
        φ ((Polynomial.derivative G).eval₂ ι (X (Sum.inr b))) * c b := by
    intro c b G
    induction G using Polynomial.induction_on with
    | C a => simp [hDι]
    | add f g hf hg => simp only [Polynomial.eval₂_add, hDadd, hf, hg, Polynomial.derivative_add,
        map_add, add_mul]
    | monomial n a h =>
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial (MvPolynomial α ℂ)) =
          Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by ring
      rw [e, Polynomial.eval₂_mul, hDmul, h, Polynomial.eval₂_X, hDX]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.eval₂_add,
        Polynomial.eval₂_mul, Polynomial.eval₂_one, Polynomial.eval₂_X, map_add, map_mul, mul_one]
      ring

  have hker : ∀ c : β → L, (∀ j, D c (q j) = 0) → c = 0 := by
    intro c hc
    have hDQ : ∀ p ∈ Q, D c p = 0 := by
      intro p hp
      obtain ⟨i, hi⟩ := hgen p hp
      obtain ⟨g, hg⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hi
      have h1 : D c (t ^ i * p) = 0 := by
        rw [← hg, hDsum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hDmul, hc j, (hφ _).2 (hqQ j)]
        ring
      rw [hDmul, (hφ p).2 hp, zero_mul, add_zero] at h1
      have ht : φ t ≠ 0 := fun h => htQ ((hφ t).1 h)
      rw [map_pow] at h1
      exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ ht)
    funext b
    obtain ⟨F, hFm, hF⟩ := hint b
    set y : L := φ (X (Sum.inr b))
    set Fb : Polynomial L := F.map (φ.comp ι)
    have hFb0 : Fb ≠ 0 := (hFm.map _).ne_zero
    have hev : ∀ G : Polynomial (MvPolynomial α ℂ),
        φ (G.eval₂ ι (X (Sum.inr b))) = (G.map (φ.comp ι)).eval y := by
      intro G
      rw [Polynomial.eval_map, Polynomial.hom_eval₂]
    have hroot : Fb.IsRoot y := by
      show Fb.eval y = 0
      rw [← hev]
      exact (hφ _).2 hF
    set k := Polynomial.rootMultiplicity y Fb
    have hk : 0 < k := (Polynomial.rootMultiplicity_pos hFb0).2 hroot
    set G := Polynomial.derivative^[k - 1] F
    have hG : G.eval₂ ι (X (Sum.inr b)) ∈ Q := by
      rw [← hφ, hev, ← Polynomial.iterate_derivative_map]
      exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (Nat.sub_lt hk one_pos)
    have hG' : φ ((Polynomial.derivative G).eval₂ ι (X (Sum.inr b))) ≠ 0 := by
      have e : Polynomial.derivative G = Polynomial.derivative^[k] F := by
        rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk).symm, Function.iterate_succ_apply']
      rw [e, hev, ← Polynomial.iterate_derivative_map, Polynomial.eval_iterate_derivative_rootMultiplicity]
      have : CharZero L := charZero_of_injective_ringHom (φ.comp MvPolynomial.C).injective
      rw [nsmul_eq_mul]
      exact mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
        (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero y hFb0)
    have h0 := hDQ _ hG
    rw [hDpoly] at h0
    exact (mul_eq_zero.1 h0).resolve_left hG'

  let M : Matrix (Fin r) β L := Matrix.of fun j b => φ (pderiv (Sum.inr b) (q j))
  have hMinj : Function.Injective M.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    apply hker c
    intro j
    have := congrFun hc j
    simpa [M, Matrix.mulVec, dotProduct, D] using this
  have hrank : M.rank = Fintype.card β := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hMinj, Module.finrank_fintype_fun_eq_card]
  obtain ⟨I, J, hIJ⟩ := GroundTheory.Heights₂.Theta.SplitLinear.exists_minor_ne_zero M hrank.ge
  have hJinj : Function.Injective J := by
    intro x x' hxx'
    by_contra hne
    exact hIJ (Matrix.det_zero_of_column_eq hne fun p => by simp [M, hxx'])
  have hJbij : Function.Bijective J :=
    (Fintype.bijective_iff_injective_and_card J).2 ⟨hJinj, by simp⟩
  let e := Equiv.ofBijective J hJbij
  let μ : MvPolynomial (α ⊕ β) ℂ := (Matrix.of fun p p' => pderiv (Sum.inr (J p')) (q (I p))).det
  refine ⟨μ, ?_, ?_⟩
  · intro hμ
    apply hIJ
    rw [← (hφ μ).2 hμ, RingHom.map_det]
    congr 1
  · intro w _ hw v hvX hv
    have hdet : (Matrix.of fun p p' => eval w (pderiv (Sum.inr (J p')) (q (I p)))).det ≠ 0 := by
      rw [RingHom.map_det] at hw
      convert hw using 2
      ext p p'
      simp [RingHom.mapMatrix_apply]
    have hsub : Matrix.mulVec (Matrix.of fun p p' => eval w (pderiv (Sum.inr (J p')) (q (I p))))
        (fun p => v (Sum.inr (J p))) = 0 := by
      funext p
      have h1 := hv (I p)
      rw [Fintype.sum_sum_type] at h1
      simp only [hvX, mul_zero, Finset.sum_const_zero, zero_add] at h1
      rw [← Equiv.sum_comp e] at h1
      simpa [Matrix.mulVec, dotProduct, e] using h1
    have hz := Matrix.eq_zero_of_mulVec_eq_zero hdet hsub
    funext s
    cases s with
    | inl a => exact hvX a
    | inr b =>
      have h1 : v (Sum.inr (J (e.symm b))) = 0 := congrFun hz (e.symm b)
      have h2 : J (e.symm b) = b := e.apply_symm_apply b
      rwa [h2] at h1

end ProjectionUnramifiedGeneric

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRadialPrimitive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ContDiff

noncomputable section

theorem RadialPrimitive.primitive_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    ContDiff ℝ ∞ (fun t => ∫ τ in c..t, f τ) ∧ deriv (fun t => ∫ τ in c..t, f τ) = f := by
  have hd : deriv (fun t => ∫ τ in c..t, f τ) = f :=
    funext fun t => hf.continuous.deriv_integral f c t
  refine ⟨contDiff_infty_iff_deriv.2 ⟨fun t => ?_, by rw [hd]; exact hf⟩, hd⟩
  exact (hf.continuous.integral_hasStrictDerivAt c t).hasDerivAt.differentiableAt

theorem RadialPrimitive.proof : RadialPrimitive.Statement := by
  intro e a t₀ T ha ht₀ hconst hzero hint
  set c : ℝ := ((e + 1 : ℕ) : ℝ) with hc
  set g : ℝ → ℝ := fun τ => a τ * (c * τ ^ (e + 1 - 1)) with hg
  set P : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, g τ with hP
  have hgs : ContDiff ℝ ∞ g := ha.mul (contDiff_const.mul (contDiff_id.pow _))
  obtain ⟨hPs, hPd⟩ := RadialPrimitive.primitive_contDiff g hgs 0
  have hrt : ∀ t, radialTransform (e + 1) a t = a t * t ^ (e + 1) - P t := fun t => rfl

  have hPc : ∀ t ∈ Set.Icc 0 t₀, P t = a 0 * t ^ (e + 1) := by
    intro t ht
    have h0 := radialTransform_eq_zero_of_const e a hconst ht
    rw [hrt, hconst t ht] at h0
    linarith
  set h : ℝ → ℝ := fun t => if t < t₀ then a 0 else P t / t ^ (e + 1) with hh
  have hlow : ∀ t, t < t₀ → h t = a 0 := fun t ht => if_pos ht
  have hpos : ∀ t, 0 < t → h t = P t / t ^ (e + 1) := by
    intro t ht
    by_cases h1 : t < t₀
    · rw [hlow t h1, hPc t ⟨ht.le, h1.le⟩, mul_div_assoc, div_self (pow_ne_zero _ ht.ne'), mul_one]
    · exact if_neg h1
  have hlowE : ∀ x, x < t₀ → h =ᶠ[nhds x] fun _ => a 0 := fun x hx =>
    Filter.eventually_of_mem (isOpen_Iio.mem_nhds hx) fun t ht => hlow t ht
  have hposE : ∀ x, 0 < x → h =ᶠ[nhds x] fun t => P t / t ^ (e + 1) := fun x hx =>
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) fun t ht => hpos t ht
  have hs : ContDiff ℝ ∞ h := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < t₀
    · exact contDiffAt_const.congr_of_eventuallyEq (hlowE x hx)
    · have hx0 : 0 < x := lt_of_lt_of_le ht₀ (not_lt.1 hx)
      exact (hPs.contDiffAt.div (contDiff_id.pow _).contDiffAt (pow_ne_zero _ hx0.ne')).congr_of_eventuallyEq
        (hposE x hx0)

  set R : ℝ := max T t₀ with hR
  have hPz : ∀ t, R ≤ t → P t = 0 := by
    intro t ht
    have hTt : T ≤ t := le_trans (le_max_left _ _) ht
    have hgc : Continuous g := hgs.continuous
    have htail : ∫ τ in T..t, g τ = 0 := by
      have hcg : ∫ τ in T..t, g τ = ∫ τ in T..t, (0 : ℝ) :=
        intervalIntegral.integral_congr fun τ hτ => by
          rw [Set.uIcc_of_le hTt] at hτ
          simp [hg, hzero τ hτ.1]
      rw [hcg]
      simp
    have := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := T) (c := t)
      (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
    simp only [hP]
    rw [← this, htail, add_zero]
    exact hint
  have hhz : ∀ t, R ≤ t → h t = 0 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ht₀ (le_trans (le_max_right _ _) ht)
    rw [hpos t ht0, hPz t ht, zero_div]
  obtain ⟨hQs, hQd⟩ := RadialPrimitive.primitive_contDiff h hs R
  refine ⟨fun t => ∫ τ in R..t, h τ, hQs, ⟨R, fun t ht => ?_⟩, ?_, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · have hcg : ∫ τ in R..t, h τ = ∫ τ in R..t, (0 : ℝ) :=
      intervalIntegral.integral_congr fun τ hτ => by
        rw [Set.uIcc_of_le ht] at hτ
        exact hhz τ hτ.1
    show ∫ τ in R..t, h τ = 0
    rw [hcg]
    simp
  · rw [hQd]
    exact hlow 0 ht₀
  · rw [hQd, (hlowE 0 ht₀).deriv_eq]
    simp
  · rw [hQd, hpos t ht, hrt, div_mul_cancel₀ _ (pow_ne_zero _ ht.ne')]
    ring
  · rw [hQd, (hposE t ht).deriv_eq, hrt]
    have hPt : HasDerivAt P (g t) t := (hgs.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hq : HasDerivAt (fun s => P s / s ^ (e + 1))
        ((g t * t ^ (e + 1) - P t * (((e + 1 : ℕ) : ℝ) * t ^ (e + 1 - 1))) / (t ^ (e + 1)) ^ 2) t :=
      hPt.div (hasDerivAt_pow (e + 1) t) (pow_ne_zero _ ht.ne')
    rw [hq.deriv]
    simp only [hg, hc, Nat.add_sub_cancel]
    have ht' : t ≠ 0 := ht.ne'
    push_cast
    field_simp
    ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

theorem SliceRegTail.exists_bound {n : ℕ} {a : (Fin n → ℂ) → ℝ}
    (ha : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) (hac : ContinuousOn a {x | x ≠ 0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |a x| ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn
    (hac.mono fun x hx => ne_zero_of_mem_unit_sphere ⟨x, hx⟩)
  refine ⟨max C₀ |a 0| + 1, by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; linarith [le_max_right C₀ |a 0|]
  · have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
    have hy : (‖x‖ : ℂ)⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have := hC₀ _ hy
    rw [Real.norm_eq_abs, ← ha (‖x‖ : ℂ) _ hn, smul_inv_smul₀ hn] at this
    linarith [le_max_left C₀ |a 0|]

theorem SliceRegTail.proof (hB : SliceRegVarBound.Statement) (hT : SliceRegTailMass.Statement)
    (hM : SliceCutTailMass.Statement) : SliceRegTail.Statement := by
  intro n e h W F u' ℓ a hW hF hu hℓ hℓP ha hac δ hδ
  obtain ⟨C, hC0, hC⟩ := SliceRegTail.exists_bound ha hac
  have hδ' : 0 < δ / (3 * C) := by positivity
  obtain ⟨K₁, hK₁⟩ := hT n e h W F u' ℓ hW hF hu hℓ hℓP _ hδ'
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp
    (Filter.Tendsto.eventually_lt_const hδ' (hM n e h W F ℓ hW hF hℓ))
  refine ⟨max K₁ K₂, fun k hk ε hε => ?_⟩
  have hma : Measurable a := measurable_of_continuousOn_compl_singleton 0 hac
  have hI := SliceCut.mem_Icc h k
  have hb := hB n e h W F u' ℓ ε C a (fun x => sliceCut h k x * a x) (fun x => 1 - sliceCut h k x)
    hW hF hℓ hε.1 hma ((SliceCut.measurable h k).mul hma) (measurable_const.sub (SliceCut.measurable h k)) hC
    (fun x => by
      rw [abs_mul, abs_of_nonneg (hI x).1]
      nlinarith [hC x, (hI x).1, (hI x).2, abs_nonneg (a x)])
    (fun x => ⟨by linarith [(hI x).2], by linarith [(hI x).1]⟩)
    (fun x => by
      rw [show a x - sliceCut h k x * a x = (1 - sliceCut h k x) * a x by ring, abs_mul,
        abs_of_nonneg (by linarith [(hI x).2] : (0 : ℝ) ≤ 1 - sliceCut h k x)]
      nlinarith [hC x, (hI x).1, (hI x).2, abs_nonneg (a x)])
  have h1 := hK₁ k (le_of_max_le_left hk) ε hε
  have h2 := hK₂ k (le_of_max_le_right hk)
  refine hb.trans ?_
  have h3 : C * (δ / (3 * C)) = δ / 3 := by field_simp
  nlinarith

end GroundTheory.Heights₂.Heights
end

