import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0062
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0083
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0112
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0102
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0114
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0069
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0104
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBranchChartIntX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem BranchChartInt.proof : GroundTheory.Heights₂.Heights.BranchChartInt.Statement :=
  GroundTheory.Heights₂.Heights.BranchChartInt.proof
    (GroundTheory.Heights₂.Heights.HolomorphicFibreSumInt.proof GroundTheory.Heights₂.Heights.WeightedAreaFormula.proof)
    (GroundTheory.Heights₂.Heights.BranchSheetAE.proof
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.proof
      GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof
      (GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof
        (GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.proof
          GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.proof)))
    GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof

end GroundTheory.Heights₂.Heights.Swarm
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDivisionNearS
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

open DivisionNearS in

theorem DivisionNearS.proof : DivisionNearS.Statement := by
  intro D T X Z φA hD hDT F hFv hfil t ht
  obtain ⟨hF, hFn⟩ := hFv
  set d : Fin X.A.n → X.U → ℝ≥0∞ := fun a x => ENNReal.ofReal (2 ^ D * ‖F a x‖ ^ 2 *
    (∑ i, ‖Z.s i a x‖ ^ 2) ^ (-(t + 1)) *
      Real.exp (-(φA.φ a x + ((T : ℝ) - 1 - t) * fsWeight X.e a x))) with hd
  set n : Fin X.A.n → X.U → ℝ≥0∞ := fun a x => ENNReal.ofReal (2 ^ D * ‖F a x‖ ^ 2 *
    Real.exp (-(φA.φ a x + (T : ℝ) * fsWeight X.e a x))) with hn
  have hnT : chartIntegral X.A n < ⊤ := hFn
  show chartIntegral X.A d < ⊤

  have hcmp : ∀ a x (M : ℝ), 0 ≤ M → (x ∈ (X.A.chart a).source →
      (∑ i, ‖Z.s i a x‖ ^ 2) ^ (-(t + 1)) * (∑ k, ‖X.e k a x‖ ^ 2) ^ (t + 1) ≤ M) →
      d a x ≤ ENNReal.ofReal M * n a x := by
    intro a x M hM hR
    by_cases hx : x ∈ (X.A.chart a).source
    · simp only [hd, hn]
      rw [← ENNReal.ofReal_mul hM]
      apply ENNReal.ofReal_le_ofReal
      rw [dens_eq X φA T t a x hx]
      calc 2 ^ D * ‖F a x‖ ^ 2 * Real.exp (-(φA.φ a x + (T : ℝ) * fsWeight X.e a x)) *
            ((∑ i, ‖Z.s i a x‖ ^ 2) ^ (-(t + 1)) * (∑ k, ‖X.e k a x‖ ^ 2) ^ (t + 1))
          ≤ 2 ^ D * ‖F a x‖ ^ 2 * Real.exp (-(φA.φ a x + (T : ℝ) * fsWeight X.e a x)) * M :=
            mul_le_mul_of_nonneg_left (hR hx) (by positivity)
        _ = _ := by ring
    · have h0 : F a x = 0 := hF.2.2 a x hx
      simp [hd, h0]
  rcases le_or_gt (t + 1) 0 with ht1 | ht1
  ·
    have hr : 0 ≤ rSq Z.c := by unfold rSq; positivity
    have hM : 0 ≤ rSq Z.c ^ (-(t + 1)) := Real.rpow_nonneg hr _
    calc chartIntegral X.A d
        ≤ chartIntegral X.A (fun a x => ENNReal.ofReal (rSq Z.c ^ (-(t + 1))) * n a x) :=
          ExtensionProof.chartIntegral_mono _ fun a x => hcmp a x _ hM fun hx =>
            ratio_le_of_nonpos t _ _ _ ht1 (esum_pos X a x hx) (by positivity) hr
              (ssum_le X Z a x)
      _ = ENNReal.ofReal (rSq Z.c ^ (-(t + 1))) * chartIntegral X.A n :=
          ExtensionProof.chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hnT
  ·
    have hSfin : (zeroSet X.A Z.s).Finite := Z.finite
    choose ε hε K hsub hbd using fun x₀ : zeroSet X.A Z.s =>
      local_bound X Z φA T hDT F hF hfil t ht1 x₀ x₀.2 (chartIdx X.A x₀) rfl
    set W : zeroSet X.A Z.s → Set X.U := fun x₀ => (X.A.chart (chartIdx X.A x₀)).source ∩
      X.A.chart (chartIdx X.A x₀) ⁻¹' Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀) with hW
    have hWo : ∀ x₀, IsOpen (W x₀) := fun x₀ =>
      (X.A.chart _).continuousOn.isOpen_inter_preimage (X.A.chart _).open_source Metric.isOpen_ball
    have hWc : ∀ x₀ : zeroSet X.A Z.s, W x₀ ⊆ (X.A.chart (chartIdx X.A x₀)).source := fun _ _ h => h.1
    have hWimg : ∀ x₀ : zeroSet X.A Z.s, X.A.chart (chartIdx X.A x₀) '' W x₀ ⊆
        Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀) := by
      rintro x₀ _ ⟨y, hy, rfl⟩; exact hy.2
    set V : Set X.U := ⋃ x₀, W x₀ with hV
    have hVo : IsOpen V := isOpen_iUnion hWo
    have hSV : zeroSet X.A Z.s ⊆ V := fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_source_chartIdx X.A x, by
        simpa [Metric.mem_ball] using hε ⟨x, hx⟩⟩
    obtain ⟨C, hC⟩ := Z.fl V hVo hSV

    have hoff : ∀ a x, x ∈ (X.A.chart a).source → x ∉ V →
        (∑ i, ‖Z.s i a x‖ ^ 2) ^ (-(t + 1)) * (∑ k, ‖X.e k a x‖ ^ 2) ^ (t + 1) ≤
          |C| ^ (t + 1) := by
      intro a x hx hxV
      have hc' := mem_source_chartIdx X.A x
      have h1 : ∑ k, ‖X.e k (chartIdx X.A x) x‖ ^ 2 ≤
          C * ∑ i, ‖Z.s i (chartIdx X.A x) x‖ ^ 2 := hC x hxV
      have hnz : x ∉ zeroSet X.A Z.s := fun h => hxV (hSV h)
      have hG : 0 < ‖X.L.g a (chartIdx X.A x) x‖ ^ 2 := by
        have := X.L.ne_zero a (chartIdx X.A x) x ⟨hx, hc'⟩; positivity
      have hSpos : 0 < ∑ i, ‖Z.s i a x‖ ^ 2 := by
        simp only [zeroSet, mem_ofPred_eq, not_forall] at hnz
        obtain ⟨i, hi⟩ := hnz
        have hne : Z.s i a x ≠ 0 := by
          rw [s_transform X Z i a (chartIdx X.A x) x ⟨hx, hc'⟩]
          exact mul_ne_zero (X.L.ne_zero a _ x ⟨hx, hc'⟩) hi
        exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum
          (f := fun i => ‖Z.s i a x‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))
      have hSE : ∑ k, ‖X.e k a x‖ ^ 2 ≤ |C| * ∑ i, ‖Z.s i a x‖ ^ 2 := by
        rw [esum_transform X a (chartIdx X.A x) x ⟨hx, hc'⟩,
          ssum_transform X Z a (chartIdx X.A x) x ⟨hx, hc'⟩]
        have h2 : C * ∑ i, ‖Z.s i (chartIdx X.A x) x‖ ^ 2 ≤
            |C| * ∑ i, ‖Z.s i (chartIdx X.A x) x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        calc ‖X.L.g a (chartIdx X.A x) x‖ ^ 2 * ∑ k, ‖X.e k (chartIdx X.A x) x‖ ^ 2
            ≤ ‖X.L.g a (chartIdx X.A x) x‖ ^ 2 * (|C| * ∑ i, ‖Z.s i (chartIdx X.A x) x‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) hG.le
          _ = _ := by ring
      exact ratio_le_of_nonneg t _ _ _ ht1.le (esum_pos X a x hx) hSpos hSE

    have htr : ∀ x₀ : zeroSet X.A Z.s, ∀ a, ∀ p ∈ (X.A.chart a).source ∩ W x₀,
        d a p = ENNReal.ofReal (‖jac X.A a (chartIdx X.A x₀) p‖ ^ 2) * d (chartIdx X.A x₀) p := by
      intro x₀ a p hp
      simp only [hd]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact dens_transform X Z φA T t F hF a (chartIdx X.A x₀) p ⟨hp.1, hp.2.1⟩
    have hexp : ∀ x₀ : zeroSet X.A Z.s, ∫⁻ w in Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀),
        ENNReal.ofReal (K x₀ * ‖w - X.A.chart (chartIdx X.A x₀) x₀‖ ^
          (2 * ((T : ℝ) - D) - 2 * (t + 1))) < ⊤ := by
      intro x₀
      have ha : -(2 * D : ℝ) < 2 * ((T : ℝ) - D) - 2 * (t + 1) := by linarith
      calc _ ≤ ∫⁻ w in Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀),
            ENNReal.ofReal |K x₀| * ENNReal.ofReal (‖w - X.A.chart (chartIdx X.A x₀) x₀‖ ^
              (2 * ((T : ℝ) - D) - 2 * (t + 1))) := by
            refine lintegral_mono fun w => ?_
            rw [← ENNReal.ofReal_mul (abs_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _)
              (Real.rpow_nonneg (norm_nonneg _) _))
        _ = ENNReal.ofReal |K x₀| * ∫⁻ w in Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀),
            ENNReal.ofReal (‖w - X.A.chart (chartIdx X.A x₀) x₀‖ ^
              (2 * ((T : ℝ) - D) - 2 * (t + 1))) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lintegral_ball_rpow_lt_top hD _ _ _ ha)
    have : Finite (zeroSet X.A Z.s) := hSfin.to_subtype
    have : Fintype (zeroSet X.A Z.s) := Fintype.ofFinite _
    unfold chartIntegral
    refine ENNReal.sum_lt_top.mpr fun j _ => ?_
    set O := (X.A.chart j).target ∩ (X.A.chart j).symm ⁻¹' V with hOdef
    have hO : IsOpen O :=
      (X.A.chart j).continuousOn_symm.isOpen_inter_preimage (X.A.chart j).open_target hVo
    rw [← inter_union_sdiff (piece X.A j) O]
    refine (lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    ·
      have hcov : piece X.A j ∩ O ⊆
          ⋃ x₀, piece X.A j ∩ ((X.A.chart j).target ∩ (X.A.chart j).symm ⁻¹' W x₀) := by
        rintro y ⟨hp, hyt, hyV⟩
        obtain ⟨x₀, hx₀⟩ := mem_iUnion.mp hyV
        exact mem_iUnion.mpr ⟨x₀, hp, hyt, hx₀⟩
      refine (lintegral_mono_set hcov).trans_lt ((lintegral_iUnion_le _ _).trans_lt ?_)
      rw [tsum_fintype]
      refine ENNReal.sum_lt_top.mpr fun x₀ _ => ?_
      refine (setLIntegral_piece_le_chart X.A d (chartIdx X.A x₀) (W x₀) (hWo x₀) (hWc x₀)
        (htr x₀) j).trans_lt ?_
      refine (lintegral_mono_set (hWimg x₀)).trans_lt ?_
      exact (setLIntegral_mono' measurableSet_ball fun w hw => hbd x₀ w hw).trans_lt (hexp x₀)
    ·
      have hmeas : MeasurableSet (piece X.A j \ O) :=
        (ExtensionProof.measurableSet_piece X.A j).diff hO.measurableSet
      have hM : (0 : ℝ) ≤ |C| ^ (t + 1) := Real.rpow_nonneg (abs_nonneg _) _
      refine (setLIntegral_mono' hmeas (g := fun y => ENNReal.ofReal (|C| ^ (t + 1)) *
        n j ((X.A.chart j).symm y)) fun y hy => ?_).trans_lt ?_
      · have hyt : y ∈ (X.A.chart j).target := hy.1.1
        have hyV : (X.A.chart j).symm y ∉ V := fun h => hy.2 ⟨hyt, h⟩
        exact hcmp j _ _ hM fun hx => hoff j _ hx hyV
      · refine (lintegral_mono_set sdiff_subset).trans_lt ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt ?_ hnT)
        exact Finset.single_le_sum (f := fun k => ∫⁻ y in piece X.A k, n k ((X.A.chart k).symm y))
          (fun _ _ => by simp) (Finset.mem_univ j)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PIntegralIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IntegralIndep.closed : IntegralIndep.Statement :=
  IntegralIndep.proof
    (PosPartIndep.proof
      (SheetOnlyNull.proof IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof
        IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.proof)
      PosPartLocal.proof PosPartSplit.proof)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumAdditive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Monoid

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

abbrev twistMonoid : CommMonoid (SubSystem S x Ω) where
  mul F Q := F.twist Q
  one := twistSys S x 0
  mul_assoc F P Q := SubSystem.twist_assoc F P Q
  one_mul F := twistSys_zero_twist F
  mul_one F := SubSystem.twist_twistSys_zero F
  mul_comm F Q := SubSystem.twist_comm F Q

attribute [local instance] twistMonoid

theorem foldl_twist_eq_mul {n : ℕ} (L : Fin n → SubSystem S x Ω) (l : List (Fin n)) (F : SubSystem S x Ω) :
    l.foldl (fun F i => F.twist (L i)) F = F * (l.map L).prod := by
  induction l generalizing F with
  | nil => exact (mul_one F).symm
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, ← mul_assoc]
    rfl

theorem prod_map_filter {α M : Type*} [CommMonoid M] (p : α → Bool) (f : α → M) (l : List α) :
    ((l.filter p).map f).prod = (l.map fun a => if p a then f a else 1).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [h, ih]
    · simp [h, ih]

theorem tensorSub_eq_prod {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub L T = ∏ j ∈ T, L j := by
  unfold tensorSub
  rw [foldl_twist_eq_mul]
  change 1 * _ = _
  rw [one_mul, prod_map_filter, ← Fin.prod_univ_def, ← Finset.prod_filter]
  congr 1
  ext j
  simp

end Monoid

section MixDiff

theorem powerset_map_emb {α β : Type*} (e : α ↪ β) (s : Finset α) :
    (s.map e).powerset = s.powerset.map (Finset.mapEmbedding e).toEmbedding := by
  ext T
  simp only [Finset.mem_powerset, Finset.mem_map, Finset.subset_map_iff, RelEmbedding.coe_toEmbedding,
    Finset.mapEmbedding_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

variable {G : Type*} [CommMonoid G]

def mixDiff (f : G → ℤ) {n : ℕ} (L : Fin n → G) : ℤ :=
  ∑ T : Finset (Fin n), (-1) ^ (n - T.card) * f (∏ j ∈ T, L j)

theorem mixDiff_snoc (f : G → ℤ) {m : ℕ} (L : Fin m → G) (X : G) :
    mixDiff f (Fin.snoc (α := fun _ => G) L X) = mixDiff (fun g => f (X * g)) L - mixDiff f L := by
  classical
  unfold mixDiff
  rw [← Finset.powerset_univ, ← Finset.powerset_univ, Fin.univ_castSuccEmb, Finset.cons_eq_insert,
    Finset.sum_powerset_insert (by simp), powerset_map_emb, Finset.sum_map, Finset.sum_map,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun U _ => ?_
  have hU : U.card ≤ m := by simpa using U.card_le_univ
  have hlast : Fin.last m ∉ U.map Fin.castSuccEmb := by simp [Fin.castSucc_ne_last]
  have hp : ∏ j ∈ U.map Fin.castSuccEmb, Fin.snoc (α := fun _ => G) L X j = ∏ j ∈ U, L j := by
    rw [Finset.prod_map]
    simp
  simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply, Finset.card_insert_of_notMem hlast,
    Finset.card_map, Finset.prod_insert hlast, hp, Fin.snoc_last]
  rw [show m + 1 - U.card = m - U.card + 1 by omega, show m + 1 - (U.card + 1) = m - U.card by omega, pow_succ]
  ring

theorem mixDiff_snoc_mul (f : G → ℤ) {m : ℕ} (L : Fin m → G) (X Y : G) :
    mixDiff f (Fin.snoc (α := fun _ => G) L (X * Y)) =
      mixDiff f (Fin.snoc (α := fun _ => G) L X) + mixDiff f (Fin.snoc (α := fun _ => G) L Y) +
        mixDiff f (Fin.snoc (α := fun _ => G) (Fin.snoc (α := fun _ => G) L X) Y) := by
  simp only [mixDiff_snoc]
  have h : mixDiff (fun g => f (Y * (X * g))) L = mixDiff (fun g => f (X * Y * g)) L := by
    congr 1
    funext g
    rw [mul_left_comm, mul_assoc]
  simp only [h]
  ring

end MixDiff

section Main

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

attribute [local instance] twistMonoid

theorem interSum_eq_mixDiff (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω) (c : ℕ) :
    interSum pp L c = mixDiff (fun F => restrLen pp (F.twist (twistSys S x (c : ℤ)))) L := by
  unfold interSum mixDiff
  simp only [tensorSub_eq_prod]

end Main

attribute [local instance] twistMonoid

theorem InterNumAdditive.proof (hE : InterNumEventual.Statement.{u, w})
    (hZ : InterSumTopVanish.Statement.{u, w}) : InterNumAdditive.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L i L' L'' hW
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  set σ := Equiv.swap i (Fin.last m) with hσ
  set L₀ : Fin m → LineBundle k x := fun j => L (σ (Fin.castSucc j)) with hL₀

  have hfam : ∀ B : LineBundle k x, Function.update (fun j => (L j).toSubSystem) i B.toSubSystem =
      fun j => (Function.update L i B j).toSubSystem := fun B => by
    funext j
    exact (Function.apply_update (fun _ B => B.toSubSystem) L i B j).symm

  have hmove : ∀ (Y : SubSystem k x Ω) (c : ℕ),
      interSum pp (Function.update (fun j => (L j).toSubSystem) i Y) c =
        interSum pp (Fin.snoc (α := fun _ => SubSystem k x Ω) (fun j => (L₀ j).toSubSystem) Y) c := by
    intro Y c
    rw [← interSum_comp_perm pp _ σ c]
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [hσ]
    · have hne : σ (Fin.castSucc j) ≠ i := by
        rw [hσ, Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
        exact Fin.castSucc_ne_last j
      simp [Function.update_of_ne hne, hL₀]

  have hev : ∀ B : LineBundle k x, ∀ᶠ c : ℕ in atTop,
      interSum pp (Function.update (fun j => (L j).toSubSystem) i B.toSubSystem) c =
        interNum pp (Function.update (fun j => (L j).toSubSystem) i B.toSubSystem) := fun B => by
    obtain ⟨a, ha⟩ := hE k Ω N x (m + 1) pp (Function.update L i B) hW
    rw [hfam B]
    exact interSum_eventually_eq_interNum pp _ ha
  have hz := hZ k Ω N x (m + 1) pp
    (Fin.snoc (α := fun _ => LineBundle k x) (Fin.snoc (α := fun _ => LineBundle k x) L₀ L') L'') hW
  obtain ⟨c, h1, h2, h3, h4⟩ :=
    ((hev (L'.tensorProd L'')).and ((hev L').and ((hev L'').and hz))).exists
  have hs : (fun j => (Fin.snoc (α := fun _ => LineBundle k x)
      (Fin.snoc (α := fun _ => LineBundle k x) L₀ L') L'' j).toSubSystem) =
      Fin.snoc (α := fun _ => SubSystem k x Ω) (Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun j => (L₀ j).toSubSystem) L'.toSubSystem) L''.toSubSystem := by
    have e1 := Fin.comp_snoc (fun B : LineBundle k x => B.toSubSystem)
      (Fin.snoc (α := fun _ => LineBundle k x) L₀ L') L''
    have e2 := Fin.comp_snoc (fun B : LineBundle k x => B.toSubSystem) L₀ L'
    simp only [Function.comp_def] at e1 e2
    rw [e1, e2]
  have key := mixDiff_snoc_mul (fun F => restrLen pp (F.twist (twistSys k x (c : ℤ))))
    (fun j => (L₀ j).toSubSystem) L'.toSubSystem L''.toSubSystem
  rw [← interSum_eq_mixDiff, ← interSum_eq_mixDiff, ← interSum_eq_mixDiff, ← interSum_eq_mixDiff, ← hs, h4,
    add_zero, ← hmove, ← hmove, ← hmove] at key
  have e : (L'.tensorProd L'').toSubSystem = L'.toSubSystem.twist L''.toSubSystem := rfl
  rw [e] at h1
  rw [← h1, ← h2, ← h3]
  exact key

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVeryAmpleZRowsX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem VeryAmpleZRows.proof_closed : VeryAmpleZRows.Statement.{u, v, w} :=
  VeryAmpleZRows.proof CechPartition.proof ZChartSmul.proof (ZChartLocal.proof ZChartSmul.proof)

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.RayGenVanishSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (IsModelWithBase IsGenerated baseDeg pnPt isModelWithBase_pnPt
  veryAmple_pnPt)

def RayGenVanish.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IsModelWithBase F y k₀ → ∀ β : K → ℤ, IsGenerated F y β → ∀ e : K → ℤ,
      ∃ c₀ : ℕ, ∀ n c : ℕ, c₀ ≤ c →
        Subsingleton (cechHc ι (fun δ => quotPart F (mIdealOver F y) (δ + e)) (n • β + c • baseDeg k₀) 1)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsNefBigCountAlongMultiples
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def NefBigCountAlongMultiples.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsNefBigDatum P0 y D A →
    ∀ ε : ℝ, 0 < ε → ∃ a : ℕ, 1 ≤ a ∧ ∀ᶠ k : ℕ in atTop,
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) - ε) *
          (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k)

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsOscLineDensity
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian ReciprocityTheory.ChartRestriction.G.Geo

def OscLineDensity.Statement : Prop :=
  ∀ (A B : Fin 2 → ℂ) (y : Fin 1 → ℂ), A 0 * B 1 - A 1 * B 0 ≠ 0 → A 0 + B 0 * y 0 ≠ 0 →
    A 1 + B 1 * y 0 ≠ 0 →
    maDensity (fun _ y' => Real.log (OscLine.oscMuNorm (fun p => A p.2 + B p.2 * y' 0))) y =
      ‖A 0 * B 1 - A 1 * B 0‖ ^ 2 / (2 * Real.pi * ‖A 0 + B 0 * y 0‖ ^ 4) *
        Δ OscLine.oscChartPot ((A 1 + B 1 * y 0) / (A 0 + B 0 * y 0))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

