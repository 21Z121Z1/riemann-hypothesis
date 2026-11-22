import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismPushoutModAdicPowUniversal
section
open GlobalTheory.Prism GlobalTheory.BSP CategoryTheory

namespace GlobalTheory.BSP.PoUniv

variable {l : ℕ} {R : Type} [CommRing R]

def deltaLocus {A B : Type} [CommRing A] [CommRing B] (D : Delta l A) (D' : Delta l B) (c : A →+* B) :
    Subring A where
  carrier := {x | c (D.δ x) = D'.δ (c x)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    simp [D.δ_mul, D'.δ_mul, ha, hb]
  one_mem' := by simp [D.δ_one, D'.δ_one]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    simp [D.δ_add, D'.δ_add, ha, hb]
  zero_mem' := by simp [D.δ_zero, D'.δ_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    have e1 := congrArg c (D.δ_add a (-a))
    have e2 := D'.δ_add (c a) (-c a)
    rw [add_neg_cancel, D.δ_zero] at e1
    rw [add_neg_cancel, D'.δ_zero] at e2
    simp only [map_zero, map_sub, map_add, map_sum, map_mul, map_pow, map_natCast, map_neg, ha] at e1 ⊢
    linear_combination e2 - e1

open CategoryTheory in
private lemma exists_ringHom_of_isPushout {A X Y P W : Type} [CommRing A] [CommRing X]
    [CommRing Y] [CommRing P] [CommRing W] {f : A →+* X} {g : A →+* Y} {i : X →+* P}
    {j : Y →+* P}
    (hP : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom i)
      (CommRingCat.ofHom j)) (u : X →+* W) (v : Y →+* W) (huv : u.comp f = v.comp g) :
    ∃ w : P →+* W, w.comp i = u ∧ w.comp j = v := by
  have hw : CommRingCat.ofHom f ≫ CommRingCat.ofHom u =
      CommRingCat.ofHom g ≫ CommRingCat.ofHom v := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, huv]
  exact ⟨(hP.desc (W := CommRingCat.of W) _ _ hw).hom,
    congrArg CommRingCat.Hom.hom (hP.inl_desc (W := CommRingCat.of W) _ _ hw),
    congrArg CommRingCat.Hom.hom (hP.inr_desc (W := CommRingCat.of W) _ _ hw)⟩

open CategoryTheory in
private lemma ringHom_eq_of_isPushout_of_comp_eq {A X Y P W : Type} [CommRing A] [CommRing X] [CommRing Y]
    [CommRing P] [CommRing W] {f : A →+* X} {g : A →+* Y} {i : X →+* P} {j : Y →+* P}
    (hP : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom i)
      (CommRingCat.ofHom j)) {u v : P →+* W} (hi : u.comp i = v.comp i)
    (hj : u.comp j = v.comp j) : u = v := by
  have h := hP.hom_ext (W := CommRingCat.of W) (k := CommRingCat.ofHom u)
    (l := CommRingCat.ofHom v) (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi])
    (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hj])
  exact congrArg CommRingCat.Hom.hom h

open CategoryTheory in
private lemma factorPow_comp_qmap_eq_qmap_comp_factorPow {l : ℕ} {R : Type} [CommRing R]
    {P P' : _root_.GlobalTheory.Prism.Obj l R} (f : _root_.GlobalTheory.Prism.Hom P P') {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI P') hle).comp
        (_root_.GlobalTheory.BSP.qmap f n) =
      (_root_.GlobalTheory.BSP.qmap f m).comp
        (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI P) hle) := by
  refine Ideal.Quotient.ringHom_ext ?_
  ext x
  simp only [RingHom.comp_apply, _root_.GlobalTheory.BSP.qmap_mk]
  rfl

open CategoryTheory in
private lemma eq_of_forall_mk_pow_eq_of_isHausdorff {A : Type} [CommRing A] (I : Ideal A) [IsHausdorff I A]
    {x y : A} (hxy : ∀ n, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) :
    x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  exact hxy n

open CategoryTheory in
private lemma mem_subring_of_isPushout_of_maps_mem {A X Y P : Type} [CommRing A] [CommRing X] [CommRing Y]
    [CommRing P] {f : A →+* X} {g : A →+* Y} {i : X →+* P} {j : Y →+* P}
    (hP : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom i)
      (CommRingCat.ofHom j)) (T : Subring P) (hi : ∀ x, i x ∈ T) (hj : ∀ y, j y ∈ T)
    (p : P) : p ∈ T := by
  have hcomm : i.comp f = j.comp g := congrArg CommRingCat.Hom.hom hP.w
  obtain ⟨r, hr1, hr2⟩ := exists_ringHom_of_isPushout hP (i.codRestrict T hi)
    (j.codRestrict T hj) (by
      ext z
      exact RingHom.congr_fun hcomm z)
  have hid : T.subtype.comp r = RingHom.id P := by
    refine ringHom_eq_of_isPushout_of_comp_eq hP ?_ ?_
    · ext x
      show ((r (i x) : T) : P) = i x
      rw [← RingHom.comp_apply, hr1]
      rfl
    · ext y
      show ((r (j y) : T) : P) = j y
      rw [← RingHom.comp_apply, hr2]
      rfl
  have hp : T.subtype (r p) = p := RingHom.congr_fun hid p
  rw [← hp]
  exact (r p).2

open CategoryTheory in

theorem _root_.GlobalTheory.BSP.PoUniv.isPO_univ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R]
    (B C B' C' : _root_.GlobalTheory.Prism.Obj l R) (h : _root_.GlobalTheory.Prism.Hom B C)
    (k : _root_.GlobalTheory.Prism.Hom B B') (k' : _root_.GlobalTheory.Prism.Hom C C') (h' : _root_.GlobalTheory.Prism.Hom B' C')
    (H : _root_.GlobalTheory.BSP.IsPO h k k' h') (Q : _root_.GlobalTheory.Prism.Obj l R)
    (a : _root_.GlobalTheory.Prism.Hom C Q) (b : _root_.GlobalTheory.Prism.Hom B' Q)
    (hab : a.comp h = b.comp k) :
    ∃! c : _root_.GlobalTheory.Prism.Hom C' Q,
      c.comp k' = a ∧ c.comp h' = b := by
  haveI : IsAdicComplete (_root_.GlobalTheory.BSP.adI Q) Q.A :=
    Q.complete
  have hex : ∀ m, ∃ ψ : C'.A ⧸ _root_.GlobalTheory.BSP.adI C' ^ m →+*
      Q.A ⧸ _root_.GlobalTheory.BSP.adI Q ^ m,
      ψ.comp (_root_.GlobalTheory.BSP.qmap k' m) = _root_.GlobalTheory.BSP.qmap a m ∧
      ψ.comp (_root_.GlobalTheory.BSP.qmap h' m) = _root_.GlobalTheory.BSP.qmap b m := fun m =>
    exists_ringHom_of_isPushout (H.po m) _ _ (by
      rw [← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hab])
  choose ψ hψa hψb using hex
  have hψa' : ∀ m x, ψ m (Ideal.Quotient.mk _ (k'.f x)) =
      Ideal.Quotient.mk _ (a.f x) := by
    intro m x
    have hx := RingHom.congr_fun (hψa m) (Ideal.Quotient.mk _ x)
    simpa [_root_.GlobalTheory.BSP.qmap_mk] using hx
  have hψb' : ∀ m y, ψ m (Ideal.Quotient.mk _ (h'.f y)) =
      Ideal.Quotient.mk _ (b.f y) := by
    intro m y
    have hy := RingHom.congr_fun (hψb m) (Ideal.Quotient.mk _ y)
    simpa [_root_.GlobalTheory.BSP.qmap_mk] using hy
  have hcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI Q) hle).comp
        ((ψ n).comp (Ideal.Quotient.mk _)) = (ψ m).comp (Ideal.Quotient.mk _) := by
    intro m n hle
    have key : (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI Q) hle).comp (ψ n) =
        (ψ m).comp (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI C') hle) := by
      refine ringHom_eq_of_isPushout_of_comp_eq (H.po n) ?_ ?_
      · rw [RingHom.comp_assoc, hψa, RingHom.comp_assoc, factorPow_comp_qmap_eq_qmap_comp_factorPow,
          factorPow_comp_qmap_eq_qmap_comp_factorPow, ← RingHom.comp_assoc, hψa]
      · rw [RingHom.comp_assoc, hψb, RingHom.comp_assoc, factorPow_comp_qmap_eq_qmap_comp_factorPow,
          factorPow_comp_qmap_eq_qmap_comp_factorPow, ← RingHom.comp_assoc, hψb]
    rw [← RingHom.comp_assoc, key, RingHom.comp_assoc]
    congr 1
  obtain ⟨c0, hc0⟩ : ∃ c0 : C'.A →+* Q.A, ∀ n x,
      Ideal.Quotient.mk (_root_.GlobalTheory.BSP.adI Q ^ n) (c0 x) = ψ n (Ideal.Quotient.mk _ x) :=
    ⟨_, fun n x => IsAdicComplete.mk_liftRingHom _ _ hcompat n x⟩
  have hmap : ∀ n z, z ∈ _root_.GlobalTheory.BSP.adI C' ^ n →
      c0 z ∈ _root_.GlobalTheory.BSP.adI Q ^ n := by
    intro n z hz
    rw [← Ideal.Quotient.eq_zero_iff_mem, hc0, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
  have hk : ∀ x, c0 (k'.f x) = a.f x := fun x =>
    eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => by rw [hc0, hψa']
  have hh : ∀ y, c0 (h'.f y) = b.f y := fun y =>
    eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => by rw [hc0, hψb']
  have hδ : ∀ x, c0 (C'.D.δ x) =
      Q.D.δ (c0 x) := by
    intro x
    have hS : ∀ n, ∃ s ∈ _root_.GlobalTheory.BSP.PoUniv.deltaLocus C'.D Q.D c0,
        x - s ∈ _root_.GlobalTheory.BSP.adI C' ^ n := by
      intro n
      have hT := mem_subring_of_isPushout_of_maps_mem (H.po n)
        ((_root_.GlobalTheory.BSP.PoUniv.deltaLocus C'.D Q.D c0).map
          (Ideal.Quotient.mk (_root_.GlobalTheory.BSP.adI C' ^ n)))
        (fun y => by
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [_root_.GlobalTheory.BSP.qmap_mk]
          refine Subring.mem_map.mpr ⟨_, ?_, rfl⟩
          show c0 (C'.D.δ (k'.f y)) =
            Q.D.δ (c0 (k'.f y))
          rw [← k'.f_δ, hk, hk, a.f_δ])
        (fun y => by
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [_root_.GlobalTheory.BSP.qmap_mk]
          refine Subring.mem_map.mpr ⟨_, ?_, rfl⟩
          show c0 (C'.D.δ (h'.f y)) =
            Q.D.δ (c0 (h'.f y))
          rw [← h'.f_δ, hh, hh, b.f_δ])
        (Ideal.Quotient.mk _ x)
      obtain ⟨s, hs, hsx⟩ := Subring.mem_map.mp hT
      exact ⟨s, hs, Ideal.Quotient.eq.mp hsx.symm⟩
    refine sub_eq_zero.mp (eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => ?_)
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨s, hs, hxs⟩ := hS (n + 1)
    have hs' : c0 (C'.D.δ s) =
        Q.D.δ (c0 s) := hs
    have hlC : (l : C'.A) ∈ _root_.GlobalTheory.BSP.adI C' :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    have hlQ : (l : Q.A) ∈ _root_.GlobalTheory.BSP.adI Q :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    have h1 := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l C'.A C'.D _ hlC n s
      (x - s) hxs
    have h2 := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l Q.A Q.D _ hlQ n (c0 s)
      (c0 (x - s)) (hmap _ _ hxs)
    rw [add_sub_cancel] at h1
    rw [← map_add, add_sub_cancel] at h2
    have h3 := hmap n _ h1
    rw [map_sub, hs'] at h3
    have h4 := Ideal.sub_mem _ h3 h2
    convert h4 using 1
    ring
  have hI : ∀ z ∈ C'.I, c0 z ∈ Q.I := by
    intro z hz
    have hcb : c0.comp h'.f = b.f := RingHom.ext hh
    have hz' : z ∈ Ideal.map h'.f B'.I := by
      rw [_root_.GlobalTheory.Prism.Rigid.map_I_eq l R B' C' h']
      exact hz
    have hmem := Ideal.mem_map_of_mem c0 hz'
    rwa [Ideal.map_map, hcb, _root_.GlobalTheory.Prism.Rigid.map_I_eq l R B' Q b] at hmem
  have hstr : ∀ (r : R) (z : C'.A),
      Ideal.Quotient.mk C'.I z = C'.str r →
      Ideal.Quotient.mk Q.I (c0 z) = Q.str r := by
    intro r z hz
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (B'.str r)
    have h1 := h'.f_str r y hy
    have h2 := b.f_str r y hy
    rw [← h2, ← hh, Ideal.Quotient.eq, ← map_sub]
    refine hI _ ?_
    rw [← Ideal.Quotient.eq, hz, h1]
  let c : _root_.GlobalTheory.Prism.Hom C' Q := ⟨c0, hδ, hI, hstr⟩
  have hcomm : c.comp k' = a ∧ c.comp h' = b :=
    ⟨_root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext hk),
      _root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext hh)⟩
  refine ⟨c, hcomm, fun c' hc' => ?_⟩
  refine _root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext fun x =>
    eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => ?_)
  have hq : _root_.GlobalTheory.BSP.qmap c' n = _root_.GlobalTheory.BSP.qmap c n := by
    refine ringHom_eq_of_isPushout_of_comp_eq (H.po n) ?_ ?_
    · rw [← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hc'.1, hcomm.1]
    · rw [← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hc'.2, hcomm.2]
  have hx := RingHom.congr_fun hq (Ideal.Quotient.mk _ x)
  simpa only [_root_.GlobalTheory.BSP.qmap_mk] using hx

end GlobalTheory.BSP.PoUniv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomExtDense
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysEval

section Abstract

variable {B P R : Type} [CommRing B] [CommRing P] [CommRing R] (l : ℕ) (ι : B →+* P) (f : B →+* R)

def Approx (F : P) (r : ℕ) (y : R) : Prop :=
  ∃ (n : ℕ) (b : B) (p h : P), n ≠ 0 ∧ (n : P) * p = ι b ∧ F = p + (l : P) ^ r * h ∧ (n : R) * y = f b

variable {l ι f}

theorem approx_add {F G : P} {r : ℕ} {y z : R} (hF : Approx l ι f F r y) (hG : Approx l ι f G r z) :
    Approx l ι f (F + G) r (y + z) := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hF
  obtain ⟨m, c, q, k, hm, hq, hG, hz⟩ := hG
  refine ⟨n * m, (m : B) * b + (n : B) * c, p + q, h + k, mul_ne_zero hn hm, ?_, ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, map_natCast, map_natCast, ← hp, ← hq]; push_cast; ring
  · rw [hF, hG]; ring
  · rw [map_add, map_mul, map_mul, map_natCast, map_natCast, ← hy, ← hz]; push_cast; ring

theorem approx_mul {F G : P} {r : ℕ} {y z : R} (hF : Approx l ι f F r y) (hG : Approx l ι f G r z) :
    Approx l ι f (F * G) r (y * z) := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hF
  obtain ⟨m, c, q, k, hm, hq, hG, hz⟩ := hG
  refine ⟨n * m, b * c, p * q, p * k + h * q + (l : P) ^ r * h * k, mul_ne_zero hn hm, ?_, ?_, ?_⟩
  · rw [map_mul, ← hp, ← hq]; push_cast; ring
  · rw [hF, hG]; ring
  · rw [map_mul, ← hy, ← hz]; push_cast; ring

theorem approx_ι (b : B) (r : ℕ) : Approx l ι f (ι b) r (f b) :=
  ⟨1, b, ι b, 0, one_ne_zero, by simp, by simp, by simp⟩

theorem approx_one (r : ℕ) : Approx l ι f 1 r 1 := by
  simpa using approx_ι (l := l) (ι := ι) (f := f) 1 r

theorem approx_zero (r : ℕ) : Approx l ι f 0 r 0 := by
  simpa using approx_ι (l := l) (ι := ι) (f := f) 0 r

variable (htf : ∀ (n : ℕ) (x : R), n ≠ 0 → (n : R) * x = 0 → x = 0)
  (hK : ∀ (n : ℕ) (b : B) (p : P), n ≠ 0 → (n : P) * p = ι b → ∃ y : R, (n : R) * y = f b) (hl0 : l ≠ 0)
include htf hK hl0

theorem approx_dvd {F : P} {r s : ℕ} (hrs : r ≤ s) {y z : R} (hy : Approx l ι f F r y)
    (hz : Approx l ι f F s z) : (l : R) ^ r ∣ y - z := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hy
  obtain ⟨m, c, q, k, hm, hq, hF', hz⟩ := hz
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
  have h0 : p - q = (l : P) ^ r * ((l : P) ^ d * k - h) := by linear_combination hF' - hF
  have h1 : ((n * m * l ^ r : ℕ) : P) * ((l : P) ^ d * k - h) = ι ((m : B) * b - (n : B) * c) := by
    rw [map_sub, map_mul, map_mul, map_natCast, map_natCast, ← hp, ← hq]
    push_cast
    linear_combination ((n : P) * m) * h0.symm
  obtain ⟨w, hw⟩ := hK _ _ _ (mul_ne_zero (mul_ne_zero hn hm) (pow_ne_zero _ hl0)) h1
  refine ⟨w, (sub_eq_zero.1 (htf (n * m) _ (mul_ne_zero hn hm) ?_)).symm⟩
  rw [map_sub, map_mul, map_mul, map_natCast, map_natCast, ← hy, ← hz] at hw
  push_cast at hw ⊢
  linear_combination hw

variable [IsAdicComplete (Ideal.span {(l : R)}) R]
  (hD : ∀ (F : P) (r : ℕ), ∃ (n : ℕ) (b : B) (p h : P), n ≠ 0 ∧ (n : P) * p = ι b ∧ F = p + (l : P) ^ r * h)

omit htf hl0 in
include hD in
theorem exists_approx (F : P) (r : ℕ) : ∃ y, Approx l ι f F r y := by
  obtain ⟨n, b, p, h, hn, hp, hF⟩ := hD F r
  obtain ⟨y, hy⟩ := hK n b p hn hp
  exact ⟨y, n, b, p, h, hn, hp, hF, hy⟩

omit htf hK hl0 in
variable (l) in

theorem sep_l (x : R) (h : ∀ r : ℕ, (l : R) ^ r ∣ x) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(l : R)}) x fun n => by
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h n

include hD in
theorem exists_lim (F : P) : ∃ L : R, ∀ r y, Approx l ι f F r y → (l : R) ^ r ∣ L - y := by
  choose y hy using exists_approx hK hD F
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(l : R)}) y (fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact approx_dvd htf hK hl0 hmn (hy m) (hy n))
  refine ⟨L, fun r z hz => ?_⟩
  have h1 := hL r
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  have h2 := approx_dvd htf hK hl0 le_rfl (hy r) hz
  have e : L - z = (y r - z) - (y r - L) := by ring
  rw [e]
  exact dvd_sub h2 h1

include hD in

theorem exists_ringHom : ∃ E : P →+* R, ∀ F r y, Approx l ι f F r y → (l : R) ^ r ∣ E F - y := by
  choose L hL using exists_lim htf hK hl0 hD
  have key : ∀ F z, (∀ r, ∃ y, Approx l ι f F r y ∧ (l : R) ^ r ∣ z - y) → L F = z := fun F z hz =>
    sub_eq_zero.1 (sep_l l _ fun r => by
      obtain ⟨y, hy, hzy⟩ := hz r
      have e : L F - z = (L F - y) - (z - y) := by ring
      rw [e]
      exact dvd_sub (hL F r y hy) hzy)
  have h1 : L 1 = 1 := key 1 1 fun r => ⟨1, approx_one r, by simp⟩
  have h0 : L 0 = 0 := key 0 0 fun r => ⟨0, approx_zero r, by simp⟩
  have hm : ∀ F G, L (F * G) = L F * L G := by
    intro F G
    refine key _ _ fun r => ?_
    obtain ⟨y, hy⟩ := exists_approx hK hD F r
    obtain ⟨z, hz⟩ := exists_approx hK hD G r
    obtain ⟨c, hc⟩ := hL F r y hy
    obtain ⟨d, hd⟩ := hL G r z hz
    exact ⟨y * z, approx_mul hy hz, c * z + y * d + (l : R) ^ r * c * d, by
      linear_combination (L G) * hc + (y + (l : R) ^ r * c) * hd⟩
  have ha : ∀ F G, L (F + G) = L F + L G := by
    intro F G
    refine key _ _ fun r => ?_
    obtain ⟨y, hy⟩ := exists_approx hK hD F r
    obtain ⟨z, hz⟩ := exists_approx hK hD G r
    obtain ⟨c, hc⟩ := hL F r y hy
    obtain ⟨d, hd⟩ := hL G r z hz
    exact ⟨y + z, approx_add hy hz, c + d, by linear_combination hc + hd⟩
  exact ⟨{ toFun := L, map_one' := h1, map_zero' := h0, map_mul' := hm, map_add' := ha }, hL⟩

omit hK in
include hD in

theorem ringHom_ext_dense (G₁ G₂ : P →+* R) (h : ∀ b, G₁ (ι b) = G₂ (ι b)) : G₁ = G₂ := by
  ext F
  refine sub_eq_zero.1 (sep_l l _ fun r => ?_)
  obtain ⟨n, b, p, k, hn, hp, hF⟩ := hD F r
  have e1 : (n : R) * (G₁ p - G₂ p) = G₁ ((n : P) * p) - G₂ ((n : P) * p) := by
    rw [map_mul, map_mul, map_natCast, map_natCast]; ring
  have h1 : G₁ p = G₂ p := sub_eq_zero.1 (htf n _ hn (by rw [e1, hp, h, sub_self]))
  exact ⟨G₁ k - G₂ k, by rw [hF, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, h1]; ring⟩

end Abstract

section Concrete

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [Algebra O K] (t : Wq l a →ₐ[ℤ_[l]] O)

variable (K) in

def embK (τ : ZMod a) : Wq l a →+* K := (algebraMap O K).comp (emb t τ).toRingHom

variable (l a) in

abbrev Bp : Type := Polynomial (Polynomial (Wq l a))

variable (K) in

def rhoK (τ : ZMod a) : Polynomial (Wq l a) →+* K⟦X⟧ :=
  (PowerSeries.map (embK K t τ)).comp Polynomial.coeToPowerSeries.ringHom

variable (K) in

def iotaP : Bp l a →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => (PowerSeries.map (rhoK K t τ)).comp Polynomial.coeToPowerSeries.ringHom

theorem coeff_iotaP (b : Bp l a) (τ : ZMod a) (i n : ℕ) :
    coeff n (coeff i (iotaP K t b τ)) = embK K t τ ((b.coeff i).coeff n) := by
  rw [show iotaP K t b τ = PowerSeries.map (rhoK K t τ) (b : (Polynomial (Wq l a))⟦X⟧) from rfl, coeff_map,
    Polynomial.coeff_coe, rhoK, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, coeff_map,
    Polynomial.coeff_coe]

theorem rhoK_eq_toAc [IsUltrametricDist K] [IsUnitBall O K] (q : Polynomial (Wq l a)) (τ : ZMod a) :
    rhoK K t τ q = (toAc t K (q : (Wq l a)⟦X⟧) τ : K⟦X⟧) := by
  ext n
  rw [coeff_toAc]
  simp [rhoK, embK, coeff_map, Polynomial.coeff_coe]

theorem charZero_K [NormedAlgebra ℚ_[l] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective

theorem embK_injective [NormedAlgebra ℚ_[l] K] (τ : ZMod a) : Function.Injective (embK K t τ) := by
  have := charZero_K (l := l) (K := K)
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  by_contra h0
  obtain ⟨m, v, hv, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  have hu : IsUnit v := WittVector.isUnit_of_coeff_zero_ne_zero v hv
  rw [map_mul, map_pow, map_natCast] at hw
  exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)) (hu.map _).ne_zero hw

include t in

theorem wq_nat_cancel [NormedAlgebra ℚ_[l] K] {n : ℕ} (hn : n ≠ 0) {x : Wq l a}
    (h : (n : Wq l a) * x = 0) : x = 0 := by
  have := charZero_K (l := l) (K := K)
  refine embK_injective (K := K) t 0 ?_
  have h1 := congrArg (embK K t 0) h
  rw [map_mul, map_natCast, map_zero] at h1
  rw [map_zero]
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hn)

variable {e : ℕ} (ϖ : PiSys l e)

theorem ev_coe (q : Polynomial (Wq l a)) :
    ϖ.ev a (q : (Wq l a)⟦X⟧) = q.eval₂ (wA l a).toRingHom ϖ.teich := by
  have h := Polynomial.ringHom_ext (f := (ϖ.ev a).comp Polynomial.coeToPowerSeries.ringHom)
    (g := Polynomial.eval₂RingHom (wA l a).toRingHom ϖ.teich) (fun w => by simp) (by simp)
  exact RingHom.congr_fun h q

variable (a) in

def evC : Polynomial (Wq l a) →+* Per.Acris l :=
  ((ainfToAcris l).toRingHom.comp (ϖ.ev a)).comp Polynomial.coeToPowerSeries.ringHom

variable (a) in

def fP (g : GQ l) : Bp l a →+* Per.Acris l :=
  Polynomial.eval₂RingHom (evC a ϖ) (ainfToAcris l (ϖ.mu g * ϖ.teich))

end Concrete

end GlobalTheory.CrysEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltedSeriesRowSubUntiltTruncatedAdditiveRowStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tiltedSeriesRow_sub_untilt_truncatedAdditiveRow : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CharP F l]
    [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (h : ℕ) (m x : Fin h → Fl l) (ϖ : F) (K : ℕ) (τ : Fin h → ℝ) (r : Fin h), 1 ≤ h → tsh ϖ = l →
      (∀ j, ‖sh (x j)‖ < 1) →
      (∀ (j : Fin h) (n : ℤ), ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r ∧
        ((K : ℤ) < |n| → ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r / l)) →
      ‖∑ j, sh (m j) * lam h r (x j) - tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
  first | exact @GlobalTheory.PSer.row_lam_sub_untilt_rowT | exact GlobalTheory.PSer.row_lam_sub_untilt_rowT | (intros; apply GlobalTheory.PSer.row_lam_sub_untilt_rowT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToBcrisPhiStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toBcris_phi_alt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ) (Y : Matrix ι ι (OA l O)), (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) → ∀ m m' : P.MMl, m'.1 = P.phi m.1 → toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • toBcris t ϖ P m' = (Y.map (frobOA l O)).map (toB l O) *ᵥ fun i => frobOB l O (toBcris t ϖ P m i) := by
  first | exact @GlobalTheory.BKGal.FrobCoord.toBcris_phi | exact GlobalTheory.BKGal.FrobCoord.toBcris_phi | (intros; apply GlobalTheory.BKGal.FrobCoord.toBcris_phi <;> assumption)
end

