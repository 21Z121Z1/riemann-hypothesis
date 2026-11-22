import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LengthQuotientEqLengthH0
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace QuotientH0Length

section CechH

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type w}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type w} [AddCommGroup M] [Module R M]

def toH0OfCocycle (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0) : M →ₗ[R] Cech.H G ρ 0 :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (LinearMap.ker (Cech.d G ρ 0)) φ
    (fun m => LinearMap.mem_ker.mpr (hφ m))

theorem toH0OfCocycle_eq_zero_iff (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0) (m : M) :
    toH0OfCocycle φ hφ m = 0 ↔ φ m = 0 := by
  have e : toH0OfCocycle φ hφ m = (Submodule.Quotient.mk (⟨φ m, LinearMap.mem_ker.mpr (hφ m)⟩ :
      LinearMap.ker (Cech.d G ρ 0)) : Cech.H G ρ 0) := rfl
  rw [e]
  exact (Submodule.Quotient.mk_eq_zero _).trans (Submodule.mem_comap.trans (Submodule.mem_bot R))

theorem toH0OfCocycle_surjective (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0)
    (h : ∀ z : Cech.Cochain G 0, Cech.d G ρ 0 z = 0 → ∃ m, φ m = z) : Function.Surjective (toH0OfCocycle φ hφ) := by
  intro ξ
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  obtain ⟨m, hm⟩ := h z (LinearMap.mem_ker.mp z.2)
  refine ⟨m, ?_⟩
  have e : toH0OfCocycle φ hφ m = (Submodule.Quotient.mk (⟨φ m, LinearMap.mem_ker.mpr (hφ m)⟩ :
      LinearMap.ker (Cech.d G ρ 0)) : Cech.H G ρ 0) := rfl
  rw [e]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hm)

theorem length_quotient_eq_length_H0 (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0)
    (h : ∀ z : Cech.Cochain G 0, Cech.d G ρ 0 z = 0 → ∃ m, φ m = z) (K : Submodule R M)
    (hK : ∀ m, φ m = 0 ↔ m ∈ K) : Module.length R (M ⧸ K) = Module.length R (Cech.H G ρ 0) := by
  have hker : LinearMap.ker (toH0OfCocycle φ hφ) = K := by
    ext m
    rw [LinearMap.mem_ker, toH0OfCocycle_eq_zero_iff, hK]
  rw [← hker]
  exact (LinearMap.quotKerEquivOfSurjective _ (toH0OfCocycle_surjective φ hφ h)).length_eq

theorem sgn_mul_self' (L : Finset (Fin n)) (j : Fin n) : Cech.sgn L j * Cech.sgn L j = 1 := by
  rw [Cech.sgn, ← mul_pow]
  norm_num

end CechH

section Quot

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_sub_of_mem_secs {F : SubSystem S x Ω} {t : Ω} (ht : t ∈ F.secs) (I : Chart x) :
    t ∈ F.sub I :=
  (Submodule.mem_iInf _).mp ht I

def secsTo (F₁ F₂ : SubSystem S x Ω) (I : Chart x) :
    F₁.secs →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
  (SubSystem.quotSub F₁ F₂ I).mkQ ∘ₗ
    { toFun := fun t => ⟨t.1, mem_sub_of_mem_secs t.2 I⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def toCochain (F₁ F₂ : SubSystem S x Ω) :
    F₁.secs →ₗ[S] Cech.Cochain (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) 0 :=
  LinearMap.pi fun I : Cech.Idx (support x) 0 => secsTo F₁ F₂ I.1

theorem d_toCochain (F₁ F₂ : SubSystem S x Ω) (t : F₁.secs) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0
      (toCochain F₁ F₂ t) = 0 := by
  have hv : ∀ (I J : Chart x) (h : I.1 ⊆ J.1),
      SubSystem.quotRes F₁ F₂ I J h (secsTo F₁ F₂ I t) = secsTo F₁ F₂ J t := fun _ _ _ => rfl
  exact Cech.d_zero_of_compat (fun I => secsTo F₁ F₂ I t) hv

def sing {a : Fin (N + 1)} (ha : a ∈ support x) : Cech.Idx (support x) 0 :=
  ⟨⟨{a}, Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr ha⟩, Finset.card_singleton a⟩

theorem eq_sing (I : Cech.Idx (support x) 0) : ∃ (a : Fin (N + 1)) (ha : a ∈ support x), I = sing ha := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  have hmem : a ∈ support x := I.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self a)
  exact ⟨a, hmem, Subtype.ext (Subtype.ext ha)⟩

theorem toCochain_eq_zero_iff (F₁ F₂ : SubSystem S x Ω) (t : F₁.secs) :
    toCochain F₁ F₂ t = 0 ↔ t ∈ F₂.secs.comap F₁.secs.subtype := by
  rw [Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro h
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro T
    obtain ⟨a, haT⟩ := T.2.1
    have ha : a ∈ support x := T.2.2 haT
    have h1 : (Submodule.Quotient.mk (⟨(t : Ω), mem_sub_of_mem_secs t.2 _⟩ : F₁.sub (sing ha).1) :
        F₁.sub (sing ha).1 ⧸ SubSystem.quotSub F₁ F₂ (sing ha).1) = 0 := congrFun h (sing ha)
    have h2 : (t : Ω) ∈ F₂.sub (sing ha).1 :=
      (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ (sing ha).1)).mp h1
    exact F₂.mono _ T (Finset.singleton_subset_iff.mpr haT) _ h2
  · intro h
    funext I
    show (Submodule.Quotient.mk (⟨(t : Ω), mem_sub_of_mem_secs t.2 _⟩ : F₁.sub I.1) :
        F₁.sub I.1 ⧸ SubSystem.quotSub F₁ F₂ I.1) = 0
    exact (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I.1)).mpr (mem_sub_of_mem_secs h I.1)

theorem d_mk (F₁ F₂ : SubSystem S x Ω) (u : Cech.Idx (support x) 0 → Ω) (hu : ∀ I, u I ∈ F₁.sub I.1)
    (J : Cech.Idx (support x) 1) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0
        (fun I => Submodule.Quotient.mk ⟨u I, hu I⟩) J =
      Submodule.Quotient.mk ⟨∑ j : J.1.1, Cech.sgn J.1.1 j • u (Cech.face J j),
        Submodule.sum_mem _ fun j _ =>
          zsmul_mem (F₁.mono _ _ (Cech.face_subset J j) _ (hu (Cech.face J j))) _⟩ := by
  rw [Cech.d_apply]
  have : (⟨∑ j : J.1.1, Cech.sgn J.1.1 j • u (Cech.face J j),
        Submodule.sum_mem _ fun j _ =>
          zsmul_mem (F₁.mono _ _ (Cech.face_subset J j) _ (hu (Cech.face J j))) _⟩ : F₁.sub J.1) =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • F₁.res _ J.1 (Cech.face_subset J j) ⟨u (Cech.face J j), hu _⟩ := by
    apply Subtype.ext
    simp [SubSystem.res]
  rw [this, ← Submodule.mkQ_apply, map_sum]
  simp only [map_zsmul]
  rfl

set_option maxHeartbeats 1000000 in

theorem exists_toCochain_eq (F₁ F₂ : SubSystem S x Ω)
    (hlift : ∀ s : Chart x → Ω, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I)
    (z : Cech.Cochain (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) 0)
    (hz : Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0 z = 0) :
    ∃ t : F₁.secs, toCochain F₁ F₂ t = z := by
  classical
  have hrep : ∀ I : Cech.Idx (support x) 0, ∃ v : Ω, ∃ hv : v ∈ F₁.sub I.1,
      (Submodule.Quotient.mk ⟨v, hv⟩ : F₁.sub I.1 ⧸ SubSystem.quotSub F₁ F₂ I.1) = z I := by
    intro I
    obtain ⟨⟨v, hv⟩, h⟩ := Submodule.Quotient.mk_surjective _ (z I)
    exact ⟨v, hv, h⟩
  choose v hv hvz using hrep
  have hz' : z = fun I => Submodule.Quotient.mk ⟨v I, hv I⟩ := funext fun I => (hvz I).symm
  have hpair : ∀ J : Cech.Idx (support x) 1,
      ∑ j : J.1.1, Cech.sgn J.1.1 j • v (Cech.face J j) ∈ F₂.sub J.1 := by
    intro J
    have e := congrFun hz J
    rw [hz', d_mk] at e
    exact (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ J.1)).mp e
  let V : Finset (Fin (N + 1)) → Ω := fun T =>
    if h : (T.Nonempty ∧ T ⊆ support x) ∧ T.card = 0 + 1 then v ⟨⟨T, h.1⟩, h.2⟩ else 0
  have hV : ∀ I : Cech.Idx (support x) 0, V I.1.1 = v I := fun I => by
    simp only [V]
    rw [dif_pos ⟨I.1.2, I.2⟩]
  have hVpair : ∀ (a b : Fin (N + 1)) (ha : a ∈ support x) (hb : b ∈ support x) (T : Chart x),
      a ∈ T.1 → b ∈ T.1 → V {a} - V {b} ∈ F₂.sub T := by
    intro a b ha hb T haT hbT
    by_cases hab : a = b
    · subst hab
      rw [sub_self]
      exact Submodule.zero_mem _
    have hsupp : ({a, b} : Finset (Fin (N + 1))) ⊆ support x := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨ha, hb⟩
    let J : Cech.Idx (support x) 1 :=
      ⟨⟨{a, b}, Finset.insert_nonempty _ _, hsupp⟩, Finset.card_pair hab⟩
    have e := hpair J
    have hj : ∀ j : J.1.1, v (Cech.face J j) = V (J.1.1.erase j) := fun j => (hV (Cech.face J j)).symm
    simp only [hj] at e
    have e2 := Cech.sum_sgn_of_card_two (J := ({a, b} : Finset (Fin (N + 1)))) (Finset.card_pair hab)
    rw [Finset.sum_coe_sort ({a, b} : Finset (Fin (N + 1)))
      (fun j => Cech.sgn {a, b} j • V (({a, b} : Finset (Fin (N + 1))).erase j))] at e
    rw [Finset.sum_pair hab] at e e2
    have ea : ({a, b} : Finset (Fin (N + 1))).erase a = {b} :=
      Finset.erase_insert (by simpa using hab)
    have eb : ({a, b} : Finset (Fin (N + 1))).erase b = {a} := by
      rw [Finset.pair_comm]
      exact Finset.erase_insert (by simpa using Ne.symm hab)
    rw [ea, eb, eq_neg_of_add_eq_zero_right e2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at e
    have e3 := zsmul_mem e (Cech.sgn {a, b} a)
    rw [smul_smul, sgn_mul_self', one_smul] at e3
    have e4 : V {a} - V {b} ∈ F₂.sub J.1 := by
      rw [← neg_sub]
      exact neg_mem e3
    refine F₂.mono J.1 T ?_ _ e4
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨haT, hbT⟩
  let s : Chart x → Ω := fun I => V {I.1.min' I.2.1}
  have hs : ∀ I, s I ∈ F₁.sub I := by
    intro I
    have hm := I.1.min'_mem I.2.1
    have h1 : V {I.1.min' I.2.1} ∈ F₁.sub (sing (I.2.2 hm)).1 := by
      rw [show V {I.1.min' I.2.1} = v (sing (I.2.2 hm)) from hV (sing (I.2.2 hm))]
      exact hv _
    exact F₁.mono _ I (Finset.singleton_subset_iff.mpr hm) _ h1
  have hcomp : ∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂ := by
    intro I₁ I₂ h
    exact hVpair _ _ (I₁.2.2 (I₁.1.min'_mem I₁.2.1)) (I₂.2.2 (I₂.1.min'_mem I₂.2.1)) I₂
      (h (I₁.1.min'_mem I₁.2.1)) (I₂.1.min'_mem I₂.2.1)
  obtain ⟨t, ht, hts⟩ := hlift s hs hcomp
  refine ⟨⟨t, ht⟩, ?_⟩
  rw [hz']
  funext I
  obtain ⟨a, ha, rfl⟩ := eq_sing I
  change (Submodule.Quotient.mk (⟨t, mem_sub_of_mem_secs ht _⟩ : F₁.sub (sing ha).1) :
      F₁.sub (sing ha).1 ⧸ SubSystem.quotSub F₁ F₂ (sing ha).1) = Submodule.Quotient.mk ⟨v (sing ha), hv _⟩
  rw [Submodule.Quotient.eq]
  change t - v (sing ha) ∈ F₂.sub (sing ha).1
  have hsa : s (sing ha).1 = v (sing ha) := by
    have hmin : ({a} : Finset (Fin (N + 1))).min' (Finset.singleton_nonempty a) = a :=
      Finset.min'_singleton a
    change V {({a} : Finset (Fin (N + 1))).min' _} = v (sing ha)
    rw [hmin]
    exact hV (sing ha)
  rw [← hsa]
  exact hts _

set_option maxHeartbeats 400000 in

theorem length_secs_eq (F₁ F₂ : SubSystem S x Ω)
    (hlift : ∀ s : Chart x → Ω, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I) :
    Module.length S (F₁.secs ⧸ F₂.secs.comap F₁.secs.subtype) =
      Module.length S (SubSystem.quotH F₁ F₂ 0) := by
  have hφ := d_toCochain F₁ F₂
  have hh := exists_toCochain_eq F₁ F₂ hlift
  have hK := toCochain_eq_zero_iff F₁ F₂
  have e : Module.length S (F₁.secs ⧸ F₂.secs.comap F₁.secs.subtype) =
      Module.length S (Cech.H (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
        (SubSystem.quotRes F₁ F₂) 0) :=
    length_quotient_eq_length_H0 (toCochain F₁ F₂) hφ hh _ hK
  rw [e]
  rfl

end Quot

end QuotientH0Length

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleRingIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

namespace AmpleRingIntegral

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

theorem mem_valuationSubring {H : LineBundle S x} (D : AmpleData S x H) (j : Fin (D.r + 1))
    (hj : D.h j ≠ 0) (hne : (support x).Nonempty) (V : ValuationSubring Ω)
    (hV : (ampleBase (S := S) D.h j : Set Ω) ⊆ V) {f : Ω}
    (hf : f ∈ ampleRing H.toSubSystem D.m (D.h j)) : f ∈ V := by
  set v := V.valuation
  have hVle : ∀ {a : Ω}, a ∈ V → v a ≤ 1 := fun ha => (V.valuation_le_one_iff _).mpr ha
  obtain ⟨i, hi, hmax⟩ := (support x).exists_max_image (fun a => v (x a)) hne
  have hxi : x i ≠ 0 := (mem_support x).mp hi
  set I : Chart x := singleChart hxi

  let Vs : Subalgebra S Ω :=
    { V.toSubring with algebraMap_mem' := fun r => hV (Subalgebra.algebraMap_mem _ r) }
  have hA : ∀ a ∈ chartRing S x I, a ∈ V := by
    intro a ha
    have hB := mem_ampleBase_of_mem_chartRing hxi ha
    refine (Algebra.adjoin_le (S := Vs) ?_) hB
    rintro _ ⟨l, rfl⟩
    by_cases hl : x l = 0
    · simp only [hl, zero_div]; exact V.zero_mem
    · refine V.mem_of_valuation_le_one _ ?_
      have hvi : v (x i) ≠ 0 := (Valuation.ne_zero_iff _).mpr hxi
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hvi)]
      exact hmax l ((mem_support x).mpr hl)

  obtain ⟨Q', hQ'⟩ := H.invertible I
  have hPQ : H.toSubSystem.sub I ^ D.m * Q' ^ D.m = 1 := by
    rw [← mul_pow]; exact (congrArg (· ^ D.m) hQ').trans (one_pow _)
  have hgen : H.toSubSystem.sub I ^ D.m = Submodule.span (chartRing S x I) (Set.range D.h) := by
    rw [← SubSystem.pow_sub, D.generates I]

  have hunit : ∃ l, ∃ w ∈ Q' ^ D.m, 1 ≤ v (D.h l * w) := by
    by_contra hcon
    push Not at hcon
    have hone : (1 : Ω) ∈ H.toSubSystem.sub I ^ D.m * Q' ^ D.m :=
      hPQ ▸ Submodule.mem_one.mpr ⟨1, map_one _⟩
    rw [hgen] at hone
    have : v 1 < 1 := by
      refine Submodule.mul_induction_on hone (fun p hp w hw => ?_) (fun a b ha hb => v.map_add_lt ha hb)
      induction hp using Submodule.span_induction with
      | mem y hy => obtain ⟨l, rfl⟩ := hy; exact hcon l w hw
      | zero => simp
      | add a b _ _ ha hb => rw [add_mul]; exact v.map_add_lt ha hb
      | smul c a _ ha =>
        rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hVle (hA _ c.2))) ha
    simp at this
  obtain ⟨l, w, hw, hlw⟩ := hunit

  have hjw : 1 ≤ v (D.h j * w) := by
    have hlj : v (D.h l / D.h j) ≤ 1 := hVle (hV (Algebra.subset_adjoin ⟨l, rfl⟩))
    have : D.h l * w = D.h l / D.h j * (D.h j * w) := by field_simp
    rw [this, map_mul] at hlw
    exact hlw.trans (mul_le_of_le_one_left' hlj)

  obtain ⟨n, hn⟩ := Set.mem_iInter.mp hf I
  rw [SubSystem.pow_sub, pow_mul] at hn
  have hmem : f * D.h j ^ n * w ^ n ∈ (H.toSubSystem.sub I ^ D.m) ^ n * (Q' ^ D.m) ^ n :=
    Submodule.mul_mem_mul hn (Submodule.pow_mem_pow _ hw n)
  rw [← mul_pow, hPQ, one_pow] at hmem
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp hmem
  have hle : v (f * D.h j ^ n * w ^ n) ≤ 1 := hVle (hy ▸ hA _ y.2)
  rw [mul_assoc, ← mul_pow, map_mul, map_pow] at hle
  exact V.mem_of_valuation_le_one _
    ((le_mul_of_one_le_right' (one_le_pow_of_one_le' hjw n)).trans hle)

end AmpleRingIntegral

theorem AmpleRingIntegral.proof : AmpleRingIntegral.Statement := by
  intro S _ N Ω _ _ x H D j hj f hf
  set B := ampleBase (S := S) D.h j
  rcases (support x).eq_empty_or_nonempty with hne | hne
  ·
    have hI : IsEmpty (Chart x) := ⟨fun I => by
      obtain ⟨i, hi⟩ := I.2.1
      have := I.2.2 hi; rw [hne] at this; exact absurd this (Finset.notMem_empty i)⟩
    obtain ⟨t, ht⟩ := D.finite j hj
    have htop : Submodule.span B (t : Set Ω) = ⊤ :=
      eq_top_iff.mpr fun z _ => ht (by simp [ampleRing])
    refine IsIntegral.of_mem_of_fg (⊤ : Subalgebra B Ω) ?_ f trivial
    rw [Algebra.top_toSubmodule, ← htop]
    exact ⟨t, rfl⟩
  · have key : f ∈ ⨅ V : {V : ValuationSubring Ω // (B : Set Ω) ⊆ V.toSubring}, V.1.toSubring :=
      Subring.mem_iInf.mpr fun V => AmpleRingIntegral.mem_valuationSubring D j hj hne V.1 V.2 hf
    rw [iInf_valuationSubring_superset] at key
    have hcl : Subring.closure (B : Set Ω) = B.toSubring := Subring.closure_eq B.toSubring
    rw [hcl] at key
    exact key

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGlobalFunctionsIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

theorem GlobalFunctionsIntegral.proof : GlobalFunctionsIntegral.Statement := by
  intro k _ K _ _ N y a hy ha
  classical

  have key : ∀ i : Fin (N + 1), ∃ (e : ℕ) (f : MvPolynomial (Fin (N + 1)) k),
      f.IsHomogeneous e ∧ a * y i ^ e = aeval y f := by
    intro i
    by_cases hi : y i = 0
    · exact ⟨1, 0, isHomogeneous_zero _ _ _, by simp [hi]⟩
    · obtain ⟨f, s, e, hs, hf, hse, hrep⟩ := ha i hi
      obtain ⟨n, rfl⟩ := exists_eq_X_pow_of_mem_monos_single hs
      have hne : (X i ^ n : MvPolynomial (Fin (N + 1)) k) ≠ 0 := pow_ne_zero _ (X_ne_zero i)
      have hn : n = e := (isHomogeneous_X_pow i n).inj_right hse hne
      subst hn
      refine ⟨n, f, hf, ?_⟩
      have hyn : y i ^ n ≠ 0 := pow_ne_zero _ hi
      rw [hrep, map_pow, aeval_X, div_mul_cancel₀ _ hyn]
  choose e f hf hrel using key
  set E := ∑ i, e i with hE
  let M : Submodule k K :=
    (homogeneousSubmodule (Fin (N + 1)) k E).map (aeval y : MvPolynomial (Fin (N + 1)) k →ₐ[k] K).toLinearMap
  refine isIntegral_of_smul_mem_submodule M ?_ ((homogeneousSubmodule_fg (Fin (N + 1)) k E).map _) a ?_
  ·
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    refine (Submodule.ne_bot_iff M).mpr ⟨y i ^ E, ⟨X i ^ E, ?_, by simp⟩, pow_ne_zero _ hi⟩
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X_pow i E)
  ·
    rintro _ ⟨g, hg, rfl⟩
    have hgE : g.IsHomogeneous E := (mem_homogeneousSubmodule _ _).mp hg
    rw [smul_eq_mul, AlgHom.toLinearMap_apply, g.as_sum, map_sum, Finset.mul_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hmE : m.degree = E := by
      by_contra h
      exact mem_support_iff.mp hm (hgE.coeff_eq_zero h)
    have hsum : ∑ i, e i ≤ ∑ i, m i := by
      rw [← hE, ← hmE, Finsupp.degree_eq_sum]
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
    set m' := m - Finsupp.single i (e i) with hm'
    have hsplit : m' + Finsupp.single i (e i) = m :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)
    have hdeg : m'.degree + e i = E := by
      rw [← hmE, ← hsplit, map_add, Finsupp.degree_single]
    refine ⟨monomial m' (coeff m g) * f i, ?_, ?_⟩
    · refine (mem_homogeneousSubmodule _ _).mpr ?_
      rw [← hdeg]
      exact (isHomogeneous_monomial _ rfl).mul (hf i)
    · have hmono : (monomial m (coeff m g) : MvPolynomial (Fin (N + 1)) k) =
          monomial m' (coeff m g) * X i ^ e i := by
        rw [X_pow_eq_monomial, monomial_mul, mul_one, hsplit]
      rw [AlgHom.toLinearMap_apply, map_mul, ← hrel i, hmono, map_mul, map_pow, aeval_X]
      ring

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltration
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem PrimeFiltration.proof (hE : PrimeFiltration.Exists.Statement.{u, v, w}) :
    PrimeFiltration.Statement.{u, v, w} :=
  ⟨hE, PrimeFiltration.Irrelevant.proof, PrimeFiltration.Point.proof,
    PrimeFiltration.Restrict.proof⟩

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem TwistVanish.proof (hE : Extension.Statement.{u, w, w}) (hV : SerreVanish.Statement.{u, w})
    (hT : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hη hspan
  obtain ⟨M₀, -, hM₀⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨M, _, _, _, _, 𝓜, hfin, hsplit⟩ :=
    hT S Ω N x M₀ G.toSubSystem B.toSubSystem r η hM₀ hη hspan
  obtain ⟨c₀, hc₀⟩ := hV (MvPolynomial (Fin (r + 1)) S) N M 𝓜 hfin
  refine ⟨c₀, fun b c hc => ?_⟩
  obtain ⟨ι, π, hπ⟩ := hsplit b c 1
  have := hc₀ 1 le_rfl c hc
  exact ⟨fun z z' => by rw [← hπ z, ← hπ z', Subsingleton.elim (ι z) (ι z')]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistVanishAll
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem TwistVanishAll.proof (hE : Extension.Statement.{u, w, w}) (hV : SerreVanish.Statement.{u, w})
    (hT : TwistSplit.Statement.{u, w}) : TwistVanishAll.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hη hspan
  obtain ⟨M₀, -, hM₀⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨M, _, _, _, _, 𝓜, hfin, hsplit⟩ :=
    hT S Ω N x M₀ G.toSubSystem B.toSubSystem r η hM₀ hη hspan
  obtain ⟨c₀, hc₀⟩ := hV (MvPolynomial (Fin (r + 1)) S) N M 𝓜 hfin
  refine ⟨c₀, fun i b c hi hc => ?_⟩
  obtain ⟨ι, π, hπ⟩ := hsplit b c i
  have := hc₀ i hi c hc
  exact ⟨fun z z' => by rw [← hπ z, ← hπ z', Subsingleton.elim (ι z) (ι z')]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

