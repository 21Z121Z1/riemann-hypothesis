import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace IdealTwistFamily

section Forms

variable {R : Type u} [CommRing R] {N : ℕ}

theorem homogeneousComponent_mul_form (r g : Poly R N) {d : ℕ} (hg : g.IsHomogeneous d) (e : ℕ) :
    homogeneousComponent e (r * g) ∈ Submodule.span R
      {z | ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧ d' + d = e ∧ z = h * g} := by
  rw [show r * g = ∑ i ∈ Finset.range (r.totalDegree + 1), homogeneousComponent i r * g by
    rw [← Finset.sum_mul, sum_homogeneousComponent], map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hm : homogeneousComponent i r * g ∈ homogeneousSubmodule (Fin (N + 1)) R (i + d) :=
    (mem_homogeneousSubmodule _ _).mpr ((homogeneousComponent_isHomogeneous i r).mul hg)
  rw [homogeneousComponent_of_mem hm]
  split_ifs with h
  · exact Submodule.subset_span ⟨_, i, homogeneousComponent_isHomogeneous i r, h.symm, rfl⟩
  · exact Submodule.zero_mem _

theorem mem_span_forms_of_mem_ideal {G : Set (Poly R N)} (deg : Poly R N → ℕ)
    (hG : ∀ g ∈ G, g.IsHomogeneous (deg g)) {f : Poly R N} {e : ℕ} (hf : f ∈ Ideal.span G)
    (he : f.IsHomogeneous e) :
    f ∈ Submodule.span R {z | ∃ g ∈ G, ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧
      d' + deg g = e ∧ z = h * g} := by
  obtain ⟨c, t, htG, -, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hf
  rw [← homogeneousComponent_eq_self he, map_sum]
  refine Submodule.sum_mem _ fun g hg => ?_
  have hc := homogeneousComponent_mul_form (c g) g (hG g (htG hg)) e
  rw [smul_eq_mul]
  refine Submodule.span_le.mpr ?_ hc
  rintro _ ⟨h, d', hh, hd, rfl⟩
  exact Submodule.subset_span ⟨g, htG hg, h, d', hh, hd, rfl⟩

theorem isHomogeneous_totalDegree {g : Poly R N} {d : ℕ} (hg : g.IsHomogeneous d) :
    g.IsHomogeneous g.totalDegree := by
  by_cases h0 : g = 0
  · rw [h0]; exact isHomogeneous_zero _ _ _
  · rwa [hg.totalDegree h0]

theorem exists_finset_forms [IsNoetherianRing R] (J : Ideal (Poly R N))
    (hJ : ∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) :
    ∃ H : Finset (Poly R N), (↑H : Set (Poly R N)) ⊆ J ∧ Ideal.span (↑H : Set (Poly R N)) = J ∧
      ∀ g ∈ (↑H : Set (Poly R N)), g.IsHomogeneous g.totalDegree := by
  classical
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian J : J.FG)
  have hsub : (↑(G.biUnion fun g => (Finset.range (g.totalDegree + 1)).image
      fun i => homogeneousComponent i g) : Set (Poly R N)) ⊆ J := by
    intro h hh
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image,
      Finset.mem_coe] at hh
    obtain ⟨g, hg, i, -, rfl⟩ := hh
    exact hJ g (hG ▸ Ideal.subset_span hg) i
  refine ⟨G.biUnion fun g => (Finset.range (g.totalDegree + 1)).image
      fun i => homogeneousComponent i g, hsub, le_antisymm (Ideal.span_le.mpr hsub) ?_, ?_⟩
  · rw [← hG]
    refine Submodule.span_le.mpr fun g hg => ?_
    have hsum := sum_homogeneousComponent g
    rw [SetLike.mem_coe, ← hsum]
    refine Ideal.sum_mem _ fun i hi => Ideal.subset_span ?_
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
    exact ⟨g, hg, i, hi, rfl⟩
  · intro h hh
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image,
      Finset.mem_coe] at hh
    obtain ⟨g, -, i, -, rfl⟩ := hh
    exact isHomogeneous_totalDegree (homogeneousComponent_isHomogeneous i g)

end Forms

section Chart

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem twist_sub_eq_mul (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  show Submodule.span (chartRing S x I) {z | ∃ q ∈ Q.sub I, ∃ y ∈ F.sub I, z = q • y} = _
  congr 1
  ext z
  simp only [Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨q, hq, y, hy, rfl⟩
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨q, hq, y, hy, rfl⟩

theorem exists_unit_mul_mem_of_span {I J : Chart x} (h : I.1 ⊆ J.1)
    (M : Submodule (chartRing S x I) Ω) {G : Set Ω}
    (hG : ∀ g ∈ G, ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * g ∈ M)
    {y : Ω} (hy : y ∈ Submodule.span (chartRing S x J) G) :
    ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * y ∈ M := by
  induction hy using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => exact ⟨1, by simp, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
    have : ((a * b : chartRing S x I) : Ω) * (y + z) = b • ((a : Ω) * y) + a • ((b : Ω) * z) := by
      simp only [chartRing_smul_def, MulMemClass.coe_mul]; ring
    rw [this]
    exact M.add_mem (M.smul_mem b hay) (M.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbc⟩ := exists_isUnit_mul_mem h c
    refine ⟨b * a, by rw [map_mul]; exact hb.mul ha, ?_⟩
    have : ((b * a : chartRing S x I) : Ω) * (c • y) =
        (⟨_, hbc⟩ : chartRing S x I) • ((a : Ω) * y) := by
      simp only [chartRing_smul_def, MulMemClass.coe_mul]; ring
    rw [this]
    exact M.smul_mem _ hay

theorem idealMod_loc {I J : Chart x} (h : I.1 ⊆ J.1) (J' : Ideal (Poly S N)) {y : Ω}
    (hy : y ∈ idealMod J' J) :
    ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * y ∈ idealMod J' I := by
  refine exists_unit_mul_mem_of_span h _ ?_ hy
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have hs0 := eval_ne_zero_of_mem_monos J hs
  have hX0 : aeval x (X i ^ e : Poly S N) ≠ 0 := by
    rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
  refine ⟨⟨aeval x s / aeval x (X i ^ e), s, X i ^ e, e, pow_mem (X_mem_monos hi) e, hse,
    isHomogeneous_X_pow i e, rfl⟩, ?_, ?_⟩
  · rw [isUnit_iff_exists_inv]
    refine ⟨⟨aeval x (X i ^ e) / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse, rfl⟩, ?_⟩
    apply Subtype.ext
    change aeval x s / aeval x (X i ^ e) * (aeval x (X i ^ e) / aeval x s) = 1
    field_simp
  · change aeval x s / aeval x (X i ^ e) * (aeval x f / aeval x s) ∈ idealMod J' I
    rw [show aeval x s / aeval x (X i ^ e) * (aeval x f / aeval x s) =
      aeval x f / aeval x (X i ^ e) by field_simp]
    exact Submodule.subset_span ⟨f, X i ^ e, e, hf, pow_mem (X_mem_monos hi) e, hfe,
      isHomogeneous_X_pow i e, rfl⟩

theorem idealMod_fg [IsNoetherianRing S] (J' : Ideal (Poly S N))
    (hJ' : ∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') (I : Chart x) :
    (idealMod J' I).FG := by
  classical
  obtain ⟨H, hHJ, hspan, hH⟩ := exists_finset_forms J' hJ'
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have heq : idealMod J' I = Submodule.span (chartRing S x I)
      ((fun g : Poly S N => aeval x g / aeval x (X i ^ g.totalDegree : Poly S N)) ''
        (↑H : Set (Poly S N))) := by
    apply le_antisymm
    · rw [idealMod, Submodule.span_le]
      rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
      have hs0 := eval_ne_zero_of_mem_monos I hs
      rw [← hspan] at hf
      have hmem := mem_span_forms_of_mem_ideal totalDegree hH hf hfe
      refine Submodule.span_induction (p := fun p _ => aeval x p / aeval x s ∈
        Submodule.span (chartRing S x I) ((fun g : Poly S N =>
          aeval x g / aeval x (X i ^ g.totalDegree : Poly S N)) '' (↑H : Set (Poly S N))))
        ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨g, hg, h', d', hh', hd, rfl⟩
        have hX : aeval x (X i ^ g.totalDegree : Poly S N) ≠ 0 := by
          rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
        let c : chartRing S x I := ⟨aeval x (h' * X i ^ g.totalDegree) / aeval x s,
          h' * X i ^ g.totalDegree, s, e, hs, hd ▸ hh'.mul (isHomogeneous_X_pow i _), hse, rfl⟩
        have hc : aeval x (h' * g) / aeval x s =
            c • (aeval x g / aeval x (X i ^ g.totalDegree : Poly S N)) := by
          rw [chartRing_smul_def]
          change _ = aeval x (h' * X i ^ g.totalDegree) / aeval x s * _
          rw [map_mul, map_mul]
          field_simp
        rw [hc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)
      · simp
      · intro p q _ _ hp hq
        rw [map_add, add_div]
        exact Submodule.add_mem _ hp hq
      · intro r p _ hp
        rw [map_smul, smul_div_assoc]
        exact Submodule.smul_of_tower_mem _ r hp
    · rw [Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact Submodule.subset_span ⟨g, X i ^ g.totalDegree, g.totalDegree, hHJ hg,
        pow_mem (X_mem_monos hi) _, hH g hg, isHomogeneous_X_pow i _, rfl⟩
  rw [heq]
  exact Submodule.fg_span (H.finite_toSet.image _)

theorem twist_mem_iff (Q : LineBundle S x) (J' : Ideal (Poly S N)) (I J : Chart x)
    (h : I.1 ⊆ J.1) (y : Ω) :
    y ∈ (Q.twist (idealSys x J')).sub J ↔ ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
      (a : Ω) • y ∈ (Q.twist (idealSys x J')).sub I := by
  constructor
  · intro hy
    refine exists_unit_mul_mem_of_span (G := {z | ∃ q ∈ (idealSys x J').sub J, ∃ y ∈ Q.sub J,
      z = q • y}) h ((Q.twist (idealSys x J')).sub I) ?_ hy
    rintro _ ⟨q, hq, z, hz, rfl⟩
    obtain ⟨a, ha, haq⟩ := idealMod_loc h J' hq
    obtain ⟨b, hb, hbz⟩ := (Q.mem_iff I J h z).mp hz
    refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
    have : ((a * b : chartRing S x I) : Ω) * (q • z) = ((a : Ω) * q) • ((b : Ω) • z) := by
      simp only [smul_eq_mul, MulMemClass.coe_mul]; ring
    rw [this]
    exact Submodule.subset_span ⟨_, haq, _, hbz, rfl⟩
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hJ := (Q.twist (idealSys x J')).mono I J h _ hay
    have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
      rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
    rw [hy]
    exact Submodule.smul_mem _ _ hJ

end Chart

theorem proof : IdealTwistFamily.Statement := by
  intro S _ _ Ω _ _ N x Q J' hJ'
  refine ⟨{ Q.twist (idealSys x J') with mem_iff := twist_mem_iff Q J' }, rfl, fun I => ?_⟩
  change ((Q.twist (idealSys x J')).sub I).FG
  rw [twist_sub_eq_mul]
  exact (idealMod_fg J' hJ' I).mul (Q.fg I)

end IdealTwistFamily

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefPlusAmple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem SubSystem.twist_sub_eq_mul (F Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨y, hy, q, hq, by rw [smul_eq_mul, mul_comm]⟩
  · rintro ⟨y, hy, q, hq, rfl⟩
    exact ⟨q, hq, y, hy, by rw [smul_eq_mul, mul_comm]⟩

theorem twistMod_zero_eq_one (I : Chart x) : twistMod k x 0 I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

theorem twistMod_mul_twistMod (a b : ℤ) (I : Chart x) :
    twistMod k x a I * twistMod k x b I = twistMod k x (a + b) I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [twistMod_eq_span a I hi, twistMod_eq_span b I hi, twistMod_eq_span (a + b) I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi]

theorem twistMod_pow_eq (c : ℤ) (n : ℕ) (I : Chart x) :
    twistMod k x c I ^ n = twistMod k x (n * c) I := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, twistMod_zero_eq_one]
  | succ n ih => rw [pow_succ, ih, twistMod_mul_twistMod]; push_cast; ring_nf

theorem SubSystem.pow_sub_eq_pow (Q : SubSystem k x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact twistMod_zero_eq_one I
  | succ n ih => rw [pow_succ, ← ih]; exact SubSystem.twist_sub_eq_mul _ _ I

theorem SubSystem.span_secs_le (F : SubSystem k x Ω) (I : Chart x) :
    Submodule.span (chartRing k x I) (F.secs : Set Ω) ≤ F.sub I := by
  rw [Submodule.span_le]
  intro z hz
  exact (Submodule.mem_iInf _).mp hz I

theorem SubSystem.generated_twist {F Q : SubSystem k x Ω} (hF : F.Generated) (hQ : Q.Generated) :
    (F.twist Q).Generated := by
  intro I
  apply le_antisymm (SubSystem.span_secs_le _ I)
  rw [SubSystem.twist_sub_eq_mul, ← hF I, ← hQ I, Submodule.span_mul_span]
  apply Submodule.span_mono
  rintro _ ⟨a, ha, b, hb, rfl⟩
  refine (Submodule.mem_iInf _).mpr fun J => ?_
  change a * b ∈ (F.twist Q).sub J
  rw [SubSystem.twist_sub_eq_mul]
  exact Submodule.mul_mem_mul ((Submodule.mem_iInf _).mp ha J) ((Submodule.mem_iInf _).mp hb J)

theorem generated_twistSys_zero : (twistSys k x 0).Generated := by
  intro I
  apply le_antisymm (SubSystem.span_secs_le _ I)
  change twistMod k x 0 I ≤ _
  rw [twistMod_zero_eq_one, Submodule.one_eq_span]
  apply Submodule.span_mono
  rintro _ rfl
  exact (Submodule.mem_iInf _).mpr fun J => one_mem_twistMod_zero J

theorem SubSystem.generated_pow {Q : SubSystem k x Ω} (hQ : Q.Generated) (n : ℕ) :
    (Q.pow n).Generated := by
  induction n with
  | zero => exact generated_twistSys_zero
  | succ n ih => exact SubSystem.generated_twist ih hQ

theorem isUnit_twistMod (c : ℤ) (I : Chart x) : IsUnit (twistMod k x c I) :=
  IsUnit.of_mul_eq_one (twistMod k x (-c) I) (by
    rw [twistMod_mul_twistMod, add_neg_cancel, twistMod_zero_eq_one])

theorem LineBundle.isUnit_sub (Q : LineBundle k x) (I : Chart x) : IsUnit (Q.sub I) := by
  obtain ⟨Q', h⟩ := Q.invertible I
  exact IsUnit.of_mul_eq_one _ h

theorem twist_pow_eq_twistMul_twist (M H T : SubSystem k x Ω)
    (hT : ∀ I, T.sub I = twistMod k x (-1) I) (q c m : ℕ) :
    (M.pow q).twist (H.pow (c * m)) =
      (twistMul M q (m : ℤ)).twist ((T.twist (H.pow c)).pow m) := by
  refine SubSystem.ext_sub fun I => ?_
  simp only [twistMul, SubSystem.twist_sub_eq_mul, SubSystem.pow_sub_eq_pow, hT]
  change _ = _ * twistMod k x (m : ℤ) I * _
  have key : twistMod k x (m : ℤ) I * twistMod k x (-1) I ^ m = 1 := by
    rw [twistMod_pow_eq, twistMod_mul_twistMod, mul_neg_one, add_neg_cancel, twistMod_zero_eq_one]
  calc M.sub I ^ q * H.sub I ^ (c * m)
      = M.sub I ^ q * H.sub I ^ (c * m) * (twistMod k x (m : ℤ) I * twistMod k x (-1) I ^ m) := by
        rw [key, mul_one]
    _ = _ := by ring

theorem exists_isSubvar_primeOf (hx : x ≠ 0) : ∃ d : ℕ, IsSubvar x (primeOf (S := k) x) d := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hXi : (X i : Poly k N) ∉ primeOf (S := k) x := by
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X]
    exact hi
  have hle : ringKrullDim (Poly k N ⧸ primeOf (S := k) x) ≤ ((N + 1 : ℕ) : WithBot ℕ∞) := by
    refine (ringKrullDim_quotient_le _).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  have hpos : ¬ ringKrullDim (Poly k N ⧸ primeOf (S := k) x) ≤ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (Poly k N ⧸ primeOf (S := k) x) := Ring.krullDimLE_iff.mpr (by simpa using h0)
    have hF : IsField (Poly k N ⧸ primeOf (S := k) x) := Ring.KrullDimLE.isField_of_isDomain
    have hne : Ideal.Quotient.mk (primeOf (S := k) x) (X i) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hmem : X i * g - 1 ∈ primeOf (S := k) x := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hb, map_one, sub_self]
    have h0' := homogeneousComponent_mem_primeOf x hmem 0
    have hc : coeff 0 (X i * g - 1 : Poly k N) = -1 := by
      rw [← congrFun constantCoeff_eq]
      simp
    rw [homogeneousComponent_zero, hc] at h0'
    exact (Ideal.IsPrime.ne_top inferInstance)
      (Ideal.eq_top_of_isUnit_mem _ h0' ((isUnit_one.neg).map (C : k →+* Poly k N)))
  have hbot : ringKrullDim (Poly k N ⧸ primeOf (S := k) x) ≠ ⊥ := fun h => hpos (h ▸ bot_le)
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have htop : e ≠ ⊤ := by
    rintro rfl
    rw [← he] at hle
    have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := hle
    exact ENat.natCast_ne_top (N + 1) (top_le_iff.mp (WithBot.coe_le_coe.mp h'))
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp htop
  have hn1 : 1 ≤ n := by
    by_contra h
    push Not at h
    apply hpos
    rw [← he]
    interval_cases n
    simp
  refine ⟨n - 1, ⟨inferInstance, fun f hf d => homogeneousComponent_mem_primeOf x hf d, le_rfl,
    ⟨i, hXi⟩, ?_⟩⟩
  rw [← he, Nat.sub_add_cancel hn1]
  rfl

theorem isVeryAmple_of_eq_zero (hx : x = 0) (F : SubSystem k x Ω) : IsVeryAmple F := by
  have hI : IsEmpty (Chart x) := ⟨fun I => by
    obtain ⟨i, hi⟩ := I.2.1
    exact (mem_support x).mp (I.2.2 hi) (by rw [hx]; rfl)⟩
  exact ⟨0, fun _ => 0, ⟨fun _ => zero_mem _, fun I => (hI.false I).elim,
    fun _ h => (h rfl).elim, fun _ h => (h rfl).elim⟩⟩

end Lemmas

theorem NefPlusAmple.proof (hGA : GeneratedAmple.Statement.{u, w})
    (hK : VeryAmpleNefPlusAmple.Statement.{u, w}) (hJ : VeryAmpleTwistGenerated.Statement.{u, w}) :
    NefPlusAmple.Statement.{u, w} := by
  intro k _ Ω _ _ N x M H hH hM ε hε
  by_cases hx : x = 0
  · refine ⟨ε.den, ε.num.toNat, ε.den_pos, ?_, isVeryAmple_of_eq_zero hx _⟩
    rw [Rat.den_mul_eq_num, ← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_pos.mpr hε).le]
  obtain ⟨d, hd⟩ := exists_isSubvar_primeOf (k := k) hx
  obtain ⟨c₀, hc₀⟩ := hGA k Ω N x H hH (twistBundle k x (-1))
  have hc : 1 ≤ max c₀ 1 := le_max_right _ _
  have hgen := hc₀ (max c₀ 1) (le_max_left _ _)
  have hcq : (0 : ℚ) < (max c₀ 1 : ℕ) := by exact_mod_cast hc
  obtain ⟨q, m, hq, hm, hVA⟩ := hK k d Ω N x M hd hM (ε / (max c₀ 1 : ℕ)) (div_pos hε hcq)
  have hm0 : 0 ≤ m := by
    have : (0 : ℚ) ≤ m := by rw [hm]; positivity
    exact_mod_cast this
  have hmq : ((m.toNat : ℕ) : ℚ) = m := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0]
  refine ⟨q, max c₀ 1 * m.toNat, hq, ?_, ?_⟩
  · rw [Nat.cast_mul, hmq, hm]
    field_simp
  · rw [twist_pow_eq_twistMul_twist M.toSubSystem H.toSubSystem (twistBundle k x (-1)).toSubSystem
      (fun _ => rfl)]
    refine hJ k Ω N x _ _ (fun I => ?_) (fun I => ?_) ?_ (SubSystem.generated_pow hgen _)
    · refine IsUnit.exists_right_inv ?_
      simp only [twistMul, SubSystem.twist_sub_eq_mul, SubSystem.pow_sub_eq_pow]
      exact ((M.isUnit_sub I).pow q).mul (isUnit_twistMod _ I)
    · refine IsUnit.exists_right_inv ?_
      simp only [SubSystem.twist_sub_eq_mul, SubSystem.pow_sub_eq_pow]
      exact ((isUnit_twistMod (-1) I).mul ((H.isUnit_sub I).pow _)).pow _
    · rwa [Int.toNat_of_nonneg hm0]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

theorem VeryAmpleDegree.proof (hDim : VeryAmpleDim.Statement.{u, w})
    (hSecs : VeryAmpleSecs.Statement.{u, w}) (hHilb : VeryAmpleHilbert.Statement.{u, w}) :
    VeryAmpleDegree.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb r h hZ hV
  obtain ⟨-, P, -, hP, hPn⟩ := hHilb k Ω N x e Nb hZ ⟨r, h, hV⟩
  obtain ⟨-, Q, -, hQ, hQn⟩ := hHilb k Ω r h e (twistBundle k h 1) (hDim k Ω N x e Nb r h hZ hV)
    isVeryAmple_twistSys_one
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hPn.and hQn)
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + n₀ : ℕ) : ℚ)) ?_ ?_
    · intro a b hab
      have : a + n₀ = b + n₀ := by simpa using hab
      omega
    · intro m
      obtain ⟨h1, h2⟩ := hn₀ (m + n₀) (Nat.le_add_left n₀ m)
      change P.eval _ = Q.eval _
      rw [← h1, ← h2, hSecs k Ω N x Nb r h hV (m + n₀)]
      rfl
  have hnum : (interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) : ℚ) =
      (interNum (primeOf (S := k) h) (fun _ : Fin e => twistSys k h 1) : ℚ) := by
    rw [← hP, hPQ, hQ]
    rfl
  exact_mod_cast hnum

end

end GroundTheory.Heights₂.Heights.Kleiman
end

