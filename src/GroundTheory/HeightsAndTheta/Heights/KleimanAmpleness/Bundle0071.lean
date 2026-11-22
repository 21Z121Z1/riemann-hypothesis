import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0064
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0065

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Charts

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra S Ω]

theorem prod_zpow_add_baseDeg (y : (Σ k, ι k) → Ω) (k₀ : K) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (δ : K → ℤ) (m : ℤ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(δ + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      (∏ k, y ⟨k, c k⟩ ^ (-δ k)) * y ⟨k₀, c k₀⟩ ^ (-m) := by
  have hterm : ∀ k, y ⟨k, c k⟩ ^ (-(δ + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      y ⟨k, c k⟩ ^ (-δ k) * (if k = k₀ then y ⟨k, c k⟩ ^ (-m) else 1) := by
    intro k
    simp only [Pi.add_apply, Pi.smul_apply, IndefiniteRowSideFullHecke.Kleiman2.baseDeg, smul_eq_mul]
    by_cases hk : k = k₀
    · subst hk
      rw [Pi.single_eq_same, if_pos rfl, mul_one, neg_add, zpow_add₀ (hc _)]
    · rw [Pi.single_eq_of_ne hk, if_neg hk, mul_zero, add_zero, mul_one]
  rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_mul_distrib, Finset.prod_ite_eq',
    if_pos (Finset.mem_univ _)]

def baseRatio (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (c : ∀ k, ι k) : Ω :=
  Kleiman.xProd I * (y ⟨k₀, c k₀⟩ ^ I.1.card)⁻¹

omit [Fintype K] [DecidableEq K] in

theorem baseRatio_mem (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (c : ∀ k, ι k) :
    baseRatio y k₀ I c ∈ chartRingOver S y c := by
  have h : baseRatio y k₀ I c = ∏ i ∈ I.1, y ⟨k₀, e.symm i⟩ / y ⟨k₀, c k₀⟩ := by
    rw [Finset.prod_div_distrib, Finset.prod_const, div_eq_mul_inv]
    rfl
  rw [h]
  exact prod_mem fun i _ => Algebra.subset_adjoin ⟨⟨k₀, e.symm i⟩, rfl⟩

theorem mem_chartSecOver_iff (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (δ : K → ℤ)
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (t : Ω) :
    t ∈ chartSecOver S y k₀ e δ I ↔ ∃ n : ℕ, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      baseRatio y k₀ I c ^ n * (t * ∏ k, y ⟨k, c k⟩ ^ (-δ k)) ∈ chartRingOver S y c := by
  simp only [chartSecOver, Set.mem_ofPred_eq]
  refine exists_congr fun n => ?_
  rw [mem_secOver_iff_charts]
  refine forall_congr' fun c => forall_congr' fun hc => ?_
  rw [prod_zpow_add_baseDeg y k₀ c hc]
  have h : Kleiman.xProd I ^ n * t * ((∏ k, y ⟨k, c k⟩ ^ (-δ k)) *
      y ⟨k₀, c k₀⟩ ^ (-(((n * I.1.card : ℕ) : ℤ)))) =
      baseRatio y k₀ I c ^ n * (t * ∏ k, y ⟨k, c k⟩ ^ (-δ k)) := by
    rw [zpow_neg, zpow_natCast, baseRatio, mul_pow, inv_pow, ← pow_mul, mul_comm I.1.card n]
    ring
  rw [h]

omit [DecidableEq K] in

theorem exists_forall_baseRatio [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ}
    {e : ι k₀ ≃ Fin (N + 1)} (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (w : (∀ k, ι k) → Ω)
    (h : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      ∃ n : ℕ, baseRatio y k₀ I c ^ n * w c ∈ chartRingOver S y c) :
    ∃ n : ℕ, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      baseRatio y k₀ I c ^ n * w c ∈ chartRingOver S y c := by
  have hev : ∀ c : ∀ k, ι k, ∀ᶠ n : ℕ in Filter.atTop, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      baseRatio y k₀ I c ^ n * w c ∈ chartRingOver S y c := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n₀, hn₀⟩ := h c hc
      refine Filter.eventually_atTop.mpr ⟨n₀, fun n hn _ => ?_⟩
      have hsplit : baseRatio y k₀ I c ^ n * w c =
          baseRatio y k₀ I c ^ (n - n₀) * (baseRatio y k₀ I c ^ n₀ * w c) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
      rw [hsplit]
      exact mul_mem (pow_mem (baseRatio_mem y k₀ I c) _) hn₀
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' hc
  exact (Filter.eventually_all.mpr hev).exists

theorem prod_zpow_mem_secOver (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℤ) (hδ : ∀ k, 0 ≤ δ k) :
    ∏ k, y ⟨k, c k⟩ ^ δ k ∈ secOver S y δ := by
  rw [mem_secOver_iff_charts]
  intro c' _
  rw [← Finset.prod_mul_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (hδ k)
  have h : y ⟨k, c k⟩ ^ δ k * y ⟨k, c' k⟩ ^ (-δ k) = (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ m := by
    rw [hm, zpow_neg, zpow_natCast, zpow_natCast, div_pow, div_eq_mul_inv]
  rw [h]
  refine pow_mem ?_ m
  exact Algebra.subset_adjoin ⟨⟨k, c k⟩, rfl⟩

end Charts

theorem ChartSecMul.proof (h₁ : BundleOfDeg.Statement) : ChartSecMul.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ N e hM γ β I
  have hsub : ∀ δ : K → ℤ, ∃ Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
      (Q.sub I : Set Ω) = chartSecOver S y k₀ e δ I := by
    intro δ
    obtain ⟨Q, hQ⟩ := h₁ S K ι Ω y k₀ N e hM δ
    refine ⟨Q, Set.ext fun t => ?_⟩
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hQ]
  choose Q hQ using hsub
  have hmemP : ∀ δ t, t ∈ (Q δ).sub I ↔ t ∈ chartSecOver S y k₀ e δ I := fun δ t =>
    Set.ext_iff.mp (hQ δ) t

  have hmul : ∀ a b c : K → ℤ, a + b = c → (Q a).sub I * (Q b).sub I ≤ (Q c).sub I := by
    rintro a b _ rfl
    rw [Submodule.mul_le]
    intro g hg f hf
    rw [hmemP, mem_chartSecOver_iff] at hg hf ⊢
    obtain ⟨n₁, hn₁⟩ := hg
    obtain ⟨n₂, hn₂⟩ := hf
    refine ⟨n₁ + n₂, fun c hc => ?_⟩
    have hY : ∏ k, y ⟨k, c k⟩ ^ (-(a + b) k) =
        (∏ k, y ⟨k, c k⟩ ^ (-a k)) * ∏ k, y ⟨k, c k⟩ ^ (-b k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, neg_add, zpow_add₀ (hc k)]
    have hsplit : baseRatio y k₀ I c ^ (n₁ + n₂) * (g * f * ∏ k, y ⟨k, c k⟩ ^ (-(a + b) k)) =
        (baseRatio y k₀ I c ^ n₁ * (g * ∏ k, y ⟨k, c k⟩ ^ (-a k))) *
          (baseRatio y k₀ I c ^ n₂ * (f * ∏ k, y ⟨k, c k⟩ ^ (-b k))) := by
      rw [hY, pow_add]
      ring
    rw [hsplit]
    exact mul_mem (hn₁ c hc) (hn₂ c hc)

  have hA : ∀ a : Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I, (a : Ω) ∈ (Q 0).sub I := by
    intro a
    have h1 : (1 : Ω) ∈ (Q 0).sub I := by
      refine (hmemP 0 1).mpr (mem_chartSecOver_of_mem S y k₀ e 0 I ?_)
      rw [mem_secOver_iff_charts]
      intro c _
      simp
    have := ((Q 0).sub I).smul_mem a h1
    rwa [Kleiman.chartRing_smul_def, mul_one] at this

  have hinv : ∀ δ : K → ℤ, (∀ k, 0 ≤ δ k) → 1 ≤ (Q δ).sub I * (Q (-δ)).sub I := by
    intro δ hδ
    obtain ⟨Q', hQ'⟩ := (Q δ).invertible I
    rw [← hQ']
    refine mul_le_mul_right (fun z hz => ?_) _
    rw [hmemP, mem_chartSecOver_iff]
    refine exists_forall_baseRatio y k₀ I _ fun c hc => ?_
    have hyc : (∏ k, y ⟨k, c k⟩ ^ δ k) ∈ (Q δ).sub I :=
      (hmemP δ _).mpr (mem_chartSecOver_of_mem S y k₀ e δ I (prod_zpow_mem_secOver y c δ hδ))
    have hw : z * ∏ k, y ⟨k, c k⟩ ^ δ k ∈ (1 : Submodule (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) Ω) := by
      rw [← hQ', mul_comm z]
      exact Submodule.mul_mem_mul hyc hz
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hw
    obtain ⟨n, hn⟩ := (mem_chartSecOver_iff y k₀ e 0 I _).mp ((hmemP 0 _).mp (hA a))
    refine ⟨n, ?_⟩
    have he : z * ∏ k, y ⟨k, c k⟩ ^ (-(-δ) k) = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ (-(0 : K → ℤ) k) := by
      simp only [Pi.neg_apply, neg_neg, Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]
      exact ha.symm
    rw [he]
    exact hn c hc
  have hshift : ∀ ε δ : K → ℤ, (∀ k, 0 ≤ δ k) →
      (Q ε).sub I ≤ (Q (ε + δ)).sub I * (Q (-δ)).sub I := by
    intro ε δ hδ
    calc (Q ε).sub I = (Q ε).sub I * 1 := (mul_one _).symm
      _ ≤ (Q ε).sub I * ((Q δ).sub I * (Q (-δ)).sub I) := mul_le_mul_right (hinv δ hδ) _
      _ = (Q ε).sub I * (Q δ).sub I * (Q (-δ)).sub I := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_left (hmul _ _ _ rfl) _
  have hshift' : ∀ ε δ : K → ℤ, (∀ k, 0 ≤ δ k) →
      (Q ε).sub I ≤ (Q (ε - δ)).sub I * (Q δ).sub I := by
    intro ε δ hδ
    calc (Q ε).sub I = (Q ε).sub I * 1 := (mul_one _).symm
      _ ≤ (Q ε).sub I * ((Q δ).sub I * (Q (-δ)).sub I) := mul_le_mul_right (hinv δ hδ) _
      _ = (Q ε).sub I * (Q (-δ)).sub I * (Q δ).sub I := by rw [mul_comm ((Q δ).sub I), mul_assoc]
      _ ≤ _ := mul_le_mul_left (hmul _ _ _ (sub_eq_add_neg ε δ).symm) _

  have hbp : ∀ k, 0 ≤ (fun k => max (β k) 0) k := fun k => le_max_right _ _
  have hbm : ∀ k, 0 ≤ (fun k => max (-β k) 0) k := fun k => le_max_right _ _
  have hγ : γ + β + (fun k => max (-β k) 0) - (fun k => max (β k) 0) = γ := by
    funext k
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [max_def, max_def]
    split_ifs <;> omega
  have hβ : (fun k => max (β k) 0) + -(fun k => max (-β k) 0) = β := by
    funext k
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [max_def, max_def]
    split_ifs <;> omega
  have hle : (Q (γ + β)).sub I ≤ (Q γ).sub I * (Q β).sub I := by
    calc (Q (γ + β)).sub I
        ≤ (Q (γ + β + fun k => max (-β k) 0)).sub I * (Q (-fun k => max (-β k) 0)).sub I :=
          hshift _ _ hbm
      _ ≤ (Q (γ + β + (fun k => max (-β k) 0) - fun k => max (β k) 0)).sub I *
            (Q fun k => max (β k) 0).sub I * (Q (-fun k => max (-β k) 0)).sub I :=
          mul_le_mul_left (hshift' _ _ hbp) _
      _ = (Q γ).sub I * ((Q fun k => max (β k) 0).sub I * (Q (-fun k => max (-β k) 0)).sub I) := by
          rw [hγ, mul_assoc]
      _ ≤ (Q γ).sub I * (Q β).sub I := mul_le_mul_right (hmul _ _ _ hβ) _
  have heq : (Q γ).sub I * (Q β).sub I = (Q (γ + β)).sub I := le_antisymm (hmul _ _ _ rfl) hle
  rw [← hQ γ, ← hQ β, ← Submodule.mul_eq_span_mul_set, heq, hQ]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointSecsLen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace CycleSplit.PointSecs

variable {S : Type u} [CommRing S] {K : Type w} [Field K] [Algebra S K] {N : ℕ} {y : Fin (N + 1) → K}

variable (S y) in

def dehomAt (j : Fin (N + 1)) : Poly S N →ₐ[S] K :=
  ((Polynomial.aeval (y j)⁻¹ : Polynomial K →ₐ[K] K).restrictScalars S).comp (cone (S := S) y)

theorem dehomAt_of_isHomogeneous (j : Fin (N + 1)) {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    dehomAt S y j f = aeval y f / y j ^ e := by
  change ((Polynomial.aeval (y j)⁻¹ : Polynomial K →ₐ[K] K).restrictScalars S) (cone (S := S) y f) = _
  rw [cone_of_isHomogeneous y hf, AlgHom.restrictScalars_apply, map_mul, map_pow, Polynomial.aeval_C,
    Polynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply, inv_pow, div_eq_mul_inv]

theorem isField_dehomAt_range (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1) {j : Fin (N + 1)}
    (hj : y j ≠ 0) : IsField (dehomAt S y j).range := by
  have h1 : ringKrullDim (cone (S := S) y).range ≤ 1 := by
    rw [primeOf_eq] at hdim
    rwa [← ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (cone (S := S) y)).toRingEquiv]
  have hne : cone (S := S) y (X j - 1) ≠ 0 := by
    intro h
    have := congrArg (fun p => Polynomial.coeff p 0) h
    simp [cone_eq, coneGen] at this
  have hkill : ((Polynomial.aeval (y j)⁻¹ : Polynomial K →ₐ[K] K).restrictScalars S)
      (cone (S := S) y (X j - 1)) = 0 := by
    simp [cone_eq, coneGen, hj]
  have key := SectionsOverLocalization.ringKrullDim_range_comp_add_one_le (cone (S := S) y)
    ((Polynomial.aeval (y j)⁻¹ : Polynomial K →ₐ[K] K).restrictScalars S) (X j - 1) hne hkill
  have key2 : ringKrullDim (dehomAt S y j).range + 1 ≤ 1 := key.trans h1
  have hle : ringKrullDim (dehomAt S y j).range ≤ 0 :=
    SectionsOverLocalization.le_zero_of_add_natCast_le (n := 1) (by simpa using key2)
  have : Ring.KrullDimLE 0 (dehomAt S y j).range := Ring.krullDimLE_iff.mpr (by simpa using hle)
  exact Ring.KrullDimLE.isField_of_isDomain

theorem dehomAt_range_le (j : Fin (N + 1)) (hj : y j ≠ 0) :
    (dehomAt S y j).range ≤ chartRing S y (singleChart hj) := by
  have : dehomAt S y j = (chartRing S y (singleChart hj)).val.comp (aeval (ratio (S := S) hj)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [dehomAt, cone_eq, coneGen, ratio, div_eq_mul_inv]
  rw [this]
  exact (AlgHom.range_comp_le_range _ _).trans (Subalgebra.range_val _).le

theorem chartRing_le_dehomAt_range (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1)
    {j : Fin (N + 1)} (hj : y j ≠ 0) (I : Chart y) : chartRing S y I ≤ (dehomAt S y j).range := by
  have hF := isField_dehomAt_range hdim hj
  rintro _ ⟨f, s, e, hs, hf, hse, rfl⟩
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hje : y j ^ e ≠ 0 := pow_ne_zero _ hj
  have hb : (⟨dehomAt S y j s, AlgHom.mem_range_self _ _⟩ : (dehomAt S y j).range) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    simp only [dehomAt_of_isHomogeneous j hse, ZeroMemClass.coe_zero] at this
    exact div_ne_zero hs0 hje this
  obtain ⟨c, hc⟩ := hF.mul_inv_cancel hb
  have hc' : (c : K) = aeval y (X j ^ e : Poly S N) / aeval y s := by
    have := congrArg Subtype.val hc
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one, dehomAt_of_isHomogeneous j hse] at this
    simp only [map_pow, aeval_X]
    field_simp at this ⊢
    linear_combination this
  have : aeval y f / aeval y s = dehomAt S y j f * c := by
    rw [hc', dehomAt_of_isHomogeneous j hf]
    simp only [map_pow, aeval_X]
    field_simp
  rw [this]
  exact mul_mem (AlgHom.mem_range_self _ _) c.2

theorem mem_chartRing_iff (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1) {j : Fin (N + 1)}
    (hj : y j ≠ 0) (I : Chart y) (z : K) : z ∈ chartRing S y I ↔ z ∈ chartRing S y (singleChart hj) := by
  obtain ⟨i, hi⟩ := I.2.1
  have hyi : y i ≠ 0 := (mem_support y).mp (I.2.2 hi)
  refine ⟨fun hz => dehomAt_range_le j hj (chartRing_le_dehomAt_range hdim hj I hz), fun hz => ?_⟩
  exact chartRing_mono (x := y) (I := singleChart hyi) (J := I) (Finset.singleton_subset_iff.mpr hi)
    (dehomAt_range_le i hyi (chartRing_le_dehomAt_range hdim hyi _ hz))

theorem chart_inv_mem (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1) {j : Fin (N + 1)}
    (hj : y j ≠ 0) {z : K} (hz : z ∈ chartRing S y (singleChart hj)) : z⁻¹ ∈ chartRing S y (singleChart hj) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [inv_zero]
    exact zero_mem _
  have hF := isField_dehomAt_range hdim hj
  have hb : (⟨z, chartRing_le_dehomAt_range hdim hj _ hz⟩ : (dehomAt S y j).range) ≠ 0 :=
    fun h => hz0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := hF.mul_inv_cancel hb
  have : (c : K) = z⁻¹ := by
    have := congrArg Subtype.val hc
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    exact (eq_inv_of_mul_eq_one_right this)
  rw [← this]
  exact dehomAt_range_le j hj c.2

theorem twist_sub_line (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1) {j : Fin (N + 1)}
    (hj : y j ≠ 0) (Q : LineBundle S y) (c : ℤ) (I : Chart y) :
    ∃ f : K, f ≠ 0 ∧ ∀ z, z ∈ (Q.twist (twistSys S y c)).sub I ↔
      ∃ a ∈ chartRing S y (singleChart hj), z = a * f := by
  have hI := mem_chartRing_iff hdim hj I
  obtain ⟨Q', hQ'⟩ := Q.invertible I
  have h1 : (1 : K) ∈ Q.sub I * Q' := by
    rw [hQ', Submodule.mem_one]
    exact ⟨1, map_one _⟩
  have hex : ∃ m ∈ Q.sub I, ∃ n ∈ Q', m * n ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : Q.sub I * Q' ≤ ⊥ := Submodule.mul_le.mpr fun m hm n hn => by
      rw [Submodule.mem_bot]; exact hcon m hm n hn
    exact one_ne_zero ((Submodule.mem_bot _).mp (hle h1))
  obtain ⟨m0, hm0, n, hn, hmn⟩ := hex
  have hqn : ∀ q ∈ Q.sub I, q * n ∈ chartRing S y (singleChart hj) := by
    intro q hq
    have := Submodule.mul_mem_mul hq hn
    rw [hQ', Submodule.mem_one] at this
    obtain ⟨a, ha⟩ := this
    rw [← ha]
    exact (hI _).mp a.2
  obtain ⟨i, hi⟩ := I.2.1
  have hyi : y i ≠ 0 := (mem_support y).mp (I.2.2 hi)
  have hm0' : m0 ≠ 0 := left_ne_zero_of_mul hmn
  have hn0 : n ≠ 0 := right_ne_zero_of_mul hmn
  have hinv := chart_inv_mem hdim hj (hqn m0 hm0)
  have hyic : y i ^ c ≠ 0 := zpow_ne_zero _ hyi
  refine ⟨y i ^ c * m0, mul_ne_zero hyic hm0', fun z => ⟨fun hz => ?_, ?_⟩⟩
  · refine Submodule.span_induction (p := fun z _ => ∃ a ∈ chartRing S y (singleChart hj), z = a * (y i ^ c * m0))
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, x, hx, rfl⟩
      change q ∈ twistMod S y c I at hq
      rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
      obtain ⟨b, rfl⟩ := hq
      refine ⟨b * (x * n) * (m0 * n)⁻¹, mul_mem (mul_mem ((hI _).mp b.2) (hqn x hx)) hinv, ?_⟩
      rw [chartRing_smul_def, smul_eq_mul]
      field_simp
    · exact ⟨0, zero_mem _, by simp⟩
    · rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, add_mem ha hb, by ring⟩
    · rintro b _ _ ⟨a, ha, rfl⟩
      exact ⟨b * a, mul_mem ((hI _).mp b.2) ha, by rw [chartRing_smul_def]; ring⟩
  · rintro ⟨a, ha, rfl⟩
    have hyc : y i ^ c ∈ (twistSys S y c).sub I := by
      change y i ^ c ∈ twistMod S y c I
      rw [twistMod_eq_span c I hi]
      exact Submodule.mem_span_singleton_self _
    have hgen : y i ^ c * m0 ∈ (Q.twist (twistSys S y c)).sub I :=
      Submodule.subset_span ⟨y i ^ c, hyc, m0, hm0, rfl⟩
    have := Submodule.smul_mem _ (⟨a, (hI a).mpr ha⟩ : chartRing S y I) hgen
    rwa [chartRing_smul_def] at this

theorem secs_line (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1) {j : Fin (N + 1)}
    (hj : y j ≠ 0) (Q : LineBundle S y) (c : ℤ) :
    ∃ f : K, f ≠ 0 ∧ ∀ z, z ∈ (Q.twist (twistSys S y c)).secs ↔
      ∃ a ∈ chartRing S y (singleChart hj), z = a * f := by
  obtain ⟨f, hf, hL⟩ := twist_sub_line hdim hj Q c (singleChart hj)
  refine ⟨f, hf, fun z => ⟨fun hz => (hL z).mp ?_, fun hz => ?_⟩⟩
  · rw [SubSystem.secs, Submodule.mem_iInf] at hz
    exact hz (singleChart hj)
  · rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    change z ∈ (Q.twist (twistSys S y c)).sub I
    let U : Chart y := ⟨(singleChart hj).1 ∪ I.1, I.2.1.mono Finset.subset_union_right,
      Finset.union_subset (singleChart hj).2.2 I.2.2⟩
    obtain ⟨g, hg, hLU⟩ := twist_sub_line hdim hj Q c U
    obtain ⟨h, hh, hLI⟩ := twist_sub_line hdim hj Q c I
    obtain ⟨b, hb, hfb⟩ := (hLU f).mp ((Q.twist (twistSys S y c)).mono _ U Finset.subset_union_left f
      ((hL f).mpr ⟨1, one_mem _, (one_mul f).symm⟩))
    obtain ⟨d, hd, hhd⟩ := (hLU h).mp ((Q.twist (twistSys S y c)).mono I U Finset.subset_union_right h
      ((hLI h).mpr ⟨1, one_mem _, (one_mul h).symm⟩))
    obtain ⟨a, ha, rfl⟩ := hz
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hhd
      exact hh hhd
    refine (hLI _).mpr ⟨a * b * d⁻¹, mul_mem (mul_mem ha hb) (chart_inv_mem hdim hj hd), ?_⟩
    rw [hfb, hhd]
    field_simp

theorem length_secs (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1) {j : Fin (N + 1)}
    (hj : y j ≠ 0) (Q : LineBundle S y) (c : ℤ) :
    Module.length S (Q.twist (twistSys S y c)).secs = Module.length S (chartRing S y (singleChart hj)) := by
  obtain ⟨f, hf, hline⟩ := secs_line hdim hj Q c
  let φ : chartRing S y (singleChart hj) →ₗ[S] (Q.twist (twistSys S y c)).secs :=
    { toFun := fun a => ⟨(a : K) * f, (hline _).mpr ⟨a, a.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (by simp [add_mul])
      map_smul' := fun s a => Subtype.ext (by simp) }
  have hbij : Function.Bijective φ := by
    refine ⟨fun a b hab => Subtype.ext (mul_right_cancel₀ hf (congrArg Subtype.val hab)), fun z => ?_⟩
    obtain ⟨a, ha, hz⟩ := (hline z).mp z.2
    exact ⟨⟨a, ha⟩, Subtype.ext hz.symm⟩
  exact ((LinearEquiv.ofBijective φ hbij).length_eq).symm

end CycleSplit.PointSecs

theorem CycleSplit.PointSecs.proof : CycleSplit.PointSecs.Statement.{u, w} := by
  intro S _ K _ _ N y ⟨j, hj⟩ hdim Q₁ Q₂ c₁ c₂
  have hyj : y j ≠ 0 := fun h =>
    hj ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X S j)).mpr (by rw [aeval_X, h]))
  rw [CycleSplit.PointSecs.length_secs hdim hyj, CycleSplit.PointSecs.length_secs hdim hyj]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

