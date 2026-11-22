import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRYBasic
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

private lemma int_range {L A : Type} [Field L] [Algebra ℂ L] [CommRing A] [Algebra ℂ A] [Algebra A L]
    [IsScalarTower ℂ A L] (hA : ∀ a : A, a ∈ (algebraMap ℂ A).range) {y : L} (h : IsIntegral A y) :
    y ∈ (algebraMap ℂ L).range := by
  haveI : Algebra.IsIntegral ℂ A := ⟨fun a => by
    obtain ⟨c, rfl⟩ := hA a
    exact isIntegral_algebraMap⟩
  have hy : IsIntegral ℂ y := isIntegral_trans y h
  exact minpoly.mem_range_of_degree_eq_one ℂ y
    (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hy))

private lemma int_mono {E L : Type} [CommRing E] [Algebra ℂ E] [CommRing L] [Algebra E L]
    {A B : Subalgebra ℂ E} (h : A ≤ B) {y : L} (hy : IsIntegral A y) : IsIntegral B y := by
  obtain ⟨p, hp, he⟩ := hy
  refine ⟨p.map (Subalgebra.inclusion h).toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact he

private lemma int_scale {L : Type} [Field L] [Algebra ℂ L] (A A' : Subalgebra ℂ L) (s : L) (hs : s ∈ A)
    (hc : ∀ c ∈ A', ∃ N : ℕ, s ^ N * c ∈ A) {y : L} (hy : IsIntegral A' y) :
    ∃ N : ℕ, IsIntegral A (y * s ^ N) := by
  obtain ⟨p, hp, he⟩ := hy
  set q : Polynomial L := p.map (algebraMap A' L) with hq
  have hqm : q.Monic := hp.map _
  have hqe : q.eval₂ (RingHom.id L) y = 0 := by
    rw [hq, Polynomial.eval₂_map]
    simpa using he
  have hcoef : ∀ i, q.coeff i ∈ A' := fun i => by
    rw [hq, Polynomial.coeff_map]
    exact (p.coeff i).2
  have hM : ∀ t : Finset ℕ, ∃ M : ℕ, ∀ i ∈ t, s ^ M * q.coeff i ∈ A := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert a t _ ih =>
      obtain ⟨M, hM⟩ := ih
      obtain ⟨N, hN⟩ := hc _ (hcoef a)
      refine ⟨M + N, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [pow_add, mul_assoc]
        exact A.mul_mem (A.pow_mem hs _) hN
      · rw [add_comm, pow_add, mul_assoc]
        exact A.mul_mem (A.pow_mem hs _) (hM i hi)
  obtain ⟨M, hM⟩ := hM (Finset.range (q.natDegree + 1))
  refine ⟨M, ?_⟩
  have hrm : (Polynomial.scaleRoots q (s ^ M)).Monic := (Polynomial.monic_scaleRoots_iff _).2 hqm
  have hre : (Polynomial.scaleRoots q (s ^ M)).eval₂ (RingHom.id L) (y * s ^ M) = 0 := by
    have := Polynomial.scaleRoots_eval₂_mul (p := q) (RingHom.id L) y (s ^ M)
    rw [hqe, mul_zero] at this
    rw [mul_comm]
    exact this
  have hA : ∀ i, (Polynomial.scaleRoots q (s ^ M)).coeff i ∈ A := by
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i q.natDegree with hi | hi | hi
    · obtain ⟨k, hk⟩ : ∃ k, q.natDegree - i = k + 1 := ⟨q.natDegree - i - 1, by omega⟩
      rw [hk, pow_succ, mul_comm, mul_assoc]
      refine A.mul_mem (A.pow_mem (A.pow_mem hs _) _) ?_
      rw [mul_comm]
      exact mul_comm (s ^ M) (q.coeff i) ▸ hM i (Finset.mem_range.2 (by omega))
    · subst hi
      simp [hqm.coeff_natDegree, A.one_mem]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact A.zero_mem
  have hlift : Polynomial.scaleRoots q (s ^ M) ∈ Polynomial.lifts (algebraMap A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hA i⟩, rfl⟩
  obtain ⟨r, hr, -, hrm'⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hrm
  refine ⟨r, hrm', ?_⟩
  rw [← hr, Polynomial.eval₂_map] at hre
  simpa using hre

private lemma omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q :=
  Submodule.span_mono fun _ ⟨b, hb, v, hv, e⟩ => ⟨b, h hb, v, fun j => h (hv j), e⟩

private lemma omB_stab {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (q : ℕ) :
    Stab (Algebra.lsmul ℂ ℂ (DR ℂ L)) B (omB ℂ L B q) := by
  intro r hr m hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hz
    exact Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, by simp [mul_smul]⟩
  | zero => simp
  | add a c _ _ ha hc =>
    rw [map_add]
    exact add_mem ha hc
  | smul t a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ ha

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K')

private lemma rA_mono' {I I' : Finset (Fin (d + 1))} (h : I ⊆ I') : rA ℂ x I ≤ rA ℂ x I' :=
  Algebra.adjoin_mono fun _ ⟨i, hi, j, e⟩ => ⟨i, h hi, j, e⟩

private lemma rB_mono' {I I' : Finset (Fin (d + 1))} (h : I ⊆ I') : rB ℂ K x I ≤ rB ℂ K x I' :=
  fun _ hy => int_mono (rA_mono' x h) hy

private lemma integralClosure_mono_subset {J J' : Finset (Fin (d + 1))} (h : J ⊆ J') : R2 x j2 J ≤ R2 x j2 J' :=
  fun _ hy => int_mono (Subalgebra.map_mono (rB_mono' x h)) hy

private lemma ratio_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    x a / x i ∈ rA ℂ x I :=
  Algebra.subset_adjoin ⟨i, hi, a, rfl⟩

private lemma rA_mem_rB {I : Finset (Fin (d + 1))} {f : F} (hf : f ∈ rA ℂ x I) :
    algebraMap F K f ∈ rB ℂ K x I :=
  show IsIntegral (rA ℂ x I) (algebraMap F K f) from
    isIntegral_algebraMap (R := rA ℂ x I) (A := K) (x := ⟨f, hf⟩)

private lemma rB_empty {b : K} (hb : b ∈ rB ℂ K x ∅) : b ∈ (algebraMap ℂ K).range := by
  refine int_range (A := rA ℂ x ∅) (fun a => ?_) hb
  have h0 : rA ℂ x ∅ = ⊥ := by simp [rA]
  have ha : (a : F) ∈ (⊥ : Subalgebra ℂ F) := h0 ▸ a.2
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 ha
  exact ⟨c, Subtype.ext hc⟩

private lemma integralClosure_empty_const {y : K'} (hy : y ∈ R2 x j2 ∅) : y ∈ (algebraMap ℂ K').range := by
  refine int_range (A := (rB ℂ K x ∅).map j2) (fun a => ?_) hy
  obtain ⟨b, hb, hba⟩ := a.2
  obtain ⟨c, rfl⟩ := rB_empty x hb
  exact ⟨c, Subtype.ext (by rw [← hba]; simp)⟩

private lemma j2_mem_R2_of_mem_rB {J : Finset (Fin (d + 1))} {b : K} (hb : b ∈ rB ℂ K x J) : j2 b ∈ R2 x j2 J :=
  show IsIntegral ((rB ℂ K x J).map j2) (j2 b) from
    isIntegral_algebraMap (R := (rB ℂ K x J).map j2) (A := K') (x := ⟨j2 b, b, hb, rfl⟩)

private lemma rB_shift (h : IsFinCover ℂ K x) {J : Finset (Fin (d + 1))} {j j' : Fin (d + 1)} (hj : j ∈ J) {b : K}
    (hb : b ∈ rB ℂ K x (insert j' J)) : ∃ N : ℕ, algebraMap F K (x j' / x j) ^ N * b ∈ rB ℂ K x J := by
  by_cases hj' : j' ∈ J
  · refine ⟨0, ?_⟩
    rw [Finset.insert_eq_of_mem hj'] at hb
    simpa using hb
  · obtain ⟨N, hN⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d x h (insert j' J) j (Finset.mem_insert_of_mem hj)).2 b).1 hb
    refine ⟨N, ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d x h J j hj).2 _).2 ⟨N, ?_⟩⟩
    rw [Finset.prod_insert hj', map_mul, mul_pow] at hN
    convert hN using 1
    ring

private lemma integralClosure_shift_power (h : IsFinCover ℂ K x) {J : Finset (Fin (d + 1))} {j j' : Fin (d + 1)} (hj : j ∈ J) {y : K'}
    (hy : y ∈ R2 x j2 (insert j' J)) : ∃ N : ℕ, y * j2 (algebraMap F K (x j' / x j)) ^ N ∈ R2 x j2 J := by
  have hs : j2 (algebraMap F K (x j' / x j)) ∈ (rB ℂ K x J).map j2 :=
    ⟨_, rA_mem_rB x (ratio_mem x hj j'), rfl⟩
  obtain ⟨N, hN⟩ := int_scale ((rB ℂ K x J).map j2) ((rB ℂ K x (insert j' J)).map j2) _ hs (by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨N, hN⟩ := rB_shift x h hj hb
    exact ⟨N, ⟨_, hN, by simp⟩⟩) hy
  exact ⟨N, hN⟩

end

theorem UpperTheory.Gal.productCup_of_system.rYBasic_of :
    RYBasic := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY
  have hpull : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I := by
    intro I b hb
    have hb' : IsIntegral (rA ℂ (xv x) I) b := hb
    exact (IsIntegral.algebraMap hb' : IsIntegral (rA ℂ (xv x) I) (algebraMap K K' b))
  have hmono : ∀ I I' J J', I ⊆ I' → J ⊆ J' → RY (xv x) j2 I J ≤ RY (xv x) j2 I' J' :=
    fun I I' J J' hI hJ => sup_le_sup (rB_mono' (xv x) hI) (integralClosure_mono_subset (xv x) j2 hJ)
  refine ⟨fun I => ?_, fun a => ?_, hmono, fun I b hb => ⟨hpull I b hb, j2_mem_R2_of_mem_rB (xv x) j2 hb⟩, ?_⟩
  · refine sup_eq_left.2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := integralClosure_empty_const (xv x) j2 hy
    exact (rB ℂ K' (xv x) I).algebraMap_mem c
  · refine ⟨fun I I' J J' _ _ hI hJ => hmono I I' J J' hI hJ,
      fun I I' J J' _ _ hI hJ => omB_mono' (hmono I I' J J' hI hJ) a,
      fun I J _ _ => omB_stab _ a, fun I J _ i hi b => ?_, fun I J _ j hj b => ?_⟩
    · have e : (((sysY x j2 a).X b * ((sysY x j2 a).X i)⁻¹ : K'ˣ) : K') = algebraMap F K' (xv x b / xv x i) := by
        simp [sysY, map_div₀, div_eq_mul_inv]
      rw [e]
      exact (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (rA_mem_rB (xv x) (ratio_mem (xv x) hi b))
    · have e : (((sysY x j2 a).Y b * ((sysY x j2 a).Y j)⁻¹ : K'ˣ) : K') = j2 (algebraMap F K (xv x b / xv x j)) := by
        simp [sysY, map_div₀, div_eq_mul_inv]
      rw [e]
      exact (le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J)
        (j2_mem_R2_of_mem_rB (xv x) j2 (rA_mem_rB (xv x) (ratio_mem (xv x) hj b)))
  · intro J j hj j' y hy
    exact integralClosure_shift_power (xv x) j2 hY.covZ hj hy
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PValBasic
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ)

private theorem mem_loc' {v : L} : v ∈ loc B e ↔ ∃ b : B, e b ≠ 0 ∧ (b : L) * v ∈ B := Iff.rfl

private theorem val_indep {v : L} (b b' c c' : B) (hb : e b ≠ 0) (hb' : e b' ≠ 0)
    (h : (b : L) * v = c) (h' : (b' : L) * v = c') : e c / e b = e c' / e b' := by
  have h1 : b' * c = b * c' := Subtype.ext (by
    push_cast
    rw [← h, ← h']
    ring)
  have h2 := congrArg e h1
  rw [map_mul, map_mul] at h2
  rw [div_eq_div_iff hb hb']
  linear_combination h2

private noncomputable def evF (w : loc B e) : ℂ :=
  e ⟨_, (Classical.choose_spec ((mem_loc' B e).1 w.2)).2⟩ / e (Classical.choose ((mem_loc' B e).1 w.2))

private theorem evF_eq (w : loc B e) (b c : B) (hb : e b ≠ 0) (h : (b : L) * w = c) :
    evF B e w = e c / e b := by
  obtain ⟨hb0, hc0⟩ := Classical.choose_spec ((mem_loc' B e).1 w.2)
  unfold evF
  exact val_indep B e _ b _ c hb0 hb rfl h

private noncomputable def evH : loc B e →ₐ[ℂ] ℂ where
  toFun := evF B e
  map_one' := by
    rw [evF_eq B e 1 1 1 (by simp) (by simp)]
    simp
  map_zero' := by
    rw [evF_eq B e 0 1 0 (by simp) (by simp)]
    simp
  map_mul' w w' := by
    obtain ⟨b, hb, h⟩ := (mem_loc' B e).1 w.2
    obtain ⟨b', hb', h'⟩ := (mem_loc' B e).1 w'.2
    rw [evF_eq B e w b ⟨_, h⟩ hb rfl, evF_eq B e w' b' ⟨_, h'⟩ hb' rfl,
      evF_eq B e (w * w') (b * b') (⟨_, h⟩ * ⟨_, h'⟩) (by simp [hb, hb'])
        (by push_cast; ring), map_mul, map_mul, mul_div_mul_comm]
  map_add' w w' := by
    obtain ⟨b, hb, h⟩ := (mem_loc' B e).1 w.2
    obtain ⟨b', hb', h'⟩ := (mem_loc' B e).1 w'.2
    rw [evF_eq B e w b ⟨_, h⟩ hb rfl, evF_eq B e w' b' ⟨_, h'⟩ hb' rfl,
      evF_eq B e (w + w') (b * b') (b' * ⟨_, h⟩ + b * ⟨_, h'⟩) (by simp [hb, hb'])
        (by push_cast; ring), map_add, map_mul, map_mul, map_mul]
    field_simp
  commutes' r := by
    rw [evF_eq B e (algebraMap ℂ _ r) 1 (algebraMap ℂ B r) (by simp) (by simp)]
    simp

private theorem evH_eq (w : loc B e) (b c : B) (hb : e b ≠ 0) (h : (b : L) * w = c) :
    evH B e w = e c / e b :=
  evF_eq B e w b c hb h

end

theorem UpperTheory.Gal.productCup_of_system.valBasic_of :
    ValBasic := by
  intro L _ _ B e
  refine ⟨fun b hb => ⟨1, by simp, by simpa using hb⟩, ⟨evH B e, fun v c => ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · rintro ⟨b, hb, hbv, h1, h2⟩
    refine ⟨⟨⟨b, hb⟩, h1, hbv⟩, ?_⟩
    rw [evH_eq B e _ ⟨b, hb⟩ ⟨_, hbv⟩ h1 rfl, h2]
    field_simp
  · rintro ⟨h, rfl⟩
    obtain ⟨b, hb, hbv⟩ := (mem_loc' B e).1 h
    refine ⟨b, b.2, hbv, hb, ?_⟩
    rw [evH_eq B e ⟨v, h⟩ b ⟨_, hbv⟩ hb rfl]
    field_simp
  · intro b
    refine ⟨1, B.one_mem, by simp, by simpa using (map_one e).symm ▸ one_ne_zero, ?_⟩
    have h1 : (⟨1, B.one_mem⟩ : B) = 1 := rfl
    have h2 : (⟨1 * (b : L), by simp⟩ : B) = b := Subtype.ext (one_mul _)
    rw [h1, h2, map_one, one_mul]
  · rintro v c ⟨b, hb, hbv, h1, h2⟩ hc
    have h3 : e ⟨b * v, hbv⟩ ≠ 0 := by
      rw [h2]
      exact mul_ne_zero h1 hc
    have hv : v ≠ 0 := by
      rintro rfl
      apply h3
      have : (⟨b * 0, hbv⟩ : B) = 0 := Subtype.ext (mul_zero _)
      rw [this, map_zero]
    refine ⟨hv, ⟨b * v, hbv⟩, h3, ?_⟩
    show b * v * v⁻¹ ∈ B
    rwa [mul_inv_cancel_right₀ hv]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PYCols
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma pk_mem' {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  rw [pk, dif_pos h]
  exact Finset.min'_mem I h

private lemma pk_zero' {d : ℕ} : pk ({0} : Finset (Fin (d + 1))) = 0 := by
  simp [pk]

private lemma inSp_sub {S κ κ' : Type} [CommRing S] [Algebra ℂ S] [Fintype κ] [Fintype κ']
    (R : Subalgebra ℂ S) (r : κ → S) (f : κ' → κ) {g : S} (h : InSp R (fun a => r (f a)) g) : InSp R r g := by
  classical
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨fun l => ∑ b ∈ Finset.univ.filter (fun b => f b = l), a b, fun l => R.sum_mem fun b _ => ha b, ?_⟩
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := f) (f := fun b => a b * r (f b))]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b hb => ?_
  rw [(Finset.mem_filter.mp hb).2]

private lemma inSp_self {S κ : Type} [CommRing S] [Algebra ℂ S] [Fintype κ]
    (R : Subalgebra ℂ S) (r : κ → S) (l : κ) : InSp R r (r l) := by
  classical
  refine ⟨fun l' => if l' = l then 1 else 0, fun l' => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  · simp

private lemma col_of_kos (hRS : RS) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ : Type} [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → S) (I J : Finset (Fin (d + 1))) (m : ℤ)
    (h : (kos T.act (T.M I J) (T.r n z (pk I) (pk J))).Z m ≤ (kos T.act (T.M I J) (T.r n z (pk I) (pk J))).B m) :
    (T.colCx n z I J).Z m ≤ (T.colCx n z I J).B m := by
  intro c hc
  have H := hRS S E T.act κ (T.M I J) (T.u n (pk I) (pk J)) (T.r n z (pk I) (pk J)) z (fun l => rfl) m c
  exact H.2.2.1.2 (h (H.2.1.1 hc))

private lemma admissible_append {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ κ' : Type} [LinearOrder κ] [LinearOrder κ'] (n : κ → ℕ × ℕ) (z : κ → S)
    (n' : κ' → ℕ × ℕ) (z' : κ' → S) (h : T.admitted n z) (h' : T.admitted n' z') : T.admitted (app n n') (app z z') := by
  intro i j l
  rcases hl : ofLex l with a | a
  · have := h i j a
    simpa [Sys.r, Sys.u, app, hl] using this
  · have := h' i j a
    simpa [Sys.r, Sys.u, app, hl] using this

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private lemma gS_X (i : Fin (d + 1)) :
    Units.map ((gS j2 : K ⊗[ℂ] K →ₐ[ℂ] K') : K ⊗[ℂ] K →* K') ((sysZ K x 0).X i) = (sysY x j2 d).X i := by
  ext
  simp [sysZ, sysY, gS, ← IsScalarTower.algebraMap_apply]

private lemma gS_Y (i : Fin (d + 1)) :
    Units.map ((gS j2 : K ⊗[ℂ] K →ₐ[ℂ] K') : K ⊗[ℂ] K →* K') ((sysZ K x 0).Y i) = (sysY x j2 d).Y i := by
  ext
  simp [sysZ, sysY, gS]

private lemma gS_r {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K) (i j : Fin (d + 1)) (k : κ) :
    gS j2 ((sysZ K x 0).r n z i j k) = (sysY x j2 d).r n (fun l => gS j2 (z l)) i j k := by
  simp only [Sys.r, Sys.u, map_mul]
  congr 1
  have := congrArg (fun v : K'ˣ => ((v⁻¹ : K'ˣ) : K'))
    (show Units.map ((gS j2 : K ⊗[ℂ] K →ₐ[ℂ] K') : K ⊗[ℂ] K →* K')
        ((sysZ K x 0).X i ^ (n k).1 * (sysZ K x 0).Y j ^ (n k).2) =
        (sysY x j2 d).X i ^ (n k).1 * (sysY x j2 d).Y j ^ (n k).2 by
      rw [map_mul, map_pow, map_pow, gS_X x j2, gS_Y x j2])
  simpa [Units.coe_map_inv] using this

private lemma rT (i j : Fin (d + 1)) (l : Fin d) (hi : i = 0) :
    (sysY x j2 d).r n10 (gT x j2) i j l = tt K' x l := by
  subst hi
  simp [Sys.r, Sys.u, n10, gT, sysY, tt, div_eq_mul_inv]

private lemma cols_gen (hKE : YKE) (hOk : SysOk) (hRS : RS) (h0 : Y0 x j2) (hG : (sysY x j2 d).Good)
    {κ : Type} [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K') (ha : (sysY x j2 d).admitted n z)
    (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (hJ : J.Nonempty) :
    ((∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ, (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n z (pk I) (pk J) l) 0) →
        ∃ e0, Over x j2 e e0 ∧ ∀ l, InSp (loc (rB ℂ K' (xv x) {0}) e0.1) ((sysY x j2 d).r n z (pk I) (pk J)) (tt K' x l)) →
      KE ((sysY x j2 d).colCx n z I J) d) ∧
    ((∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ, ¬ ∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n z (pk I) (pk J) l) 0) →
      ∀ m, ((sysY x j2 d).colCx n z I J).Z m ≤ ((sysY x j2 d).colCx n z I J).B m) := by
  have hr : ∀ l, (sysY x j2 d).r n z (pk I) (pk J) l ∈ RY (xv x) j2 I J :=
    ((hOk d K' (DR ℂ K') (sysY x j2 d) κ n z hG ha).2.1 I J _ (pk_mem' hI) _ (pk_mem' hJ)).1
  have hk := hKE F K K' d x j2 h0 κ ((sysY x j2 d).r n z (pk I) (pk J)) I J hI hr
  exact ⟨fun h m hm => col_of_kos hRS _ n z I J m (hk.1 h m hm),
    fun h m => col_of_kos hRS _ n z I J m fun c hc => hk.2.1 m c hc fun e he => absurd he (h e)⟩

end

theorem UpperTheory.Gal.productCup_of_system.yCols_of :
    YKE → PtG → PtT → FixLoc → GMap → ThMuLat → SysOk → RS → RYBasic → YCols := by
  intro hKE hPtG hPtT hFix hGM hTh hOk hRS hRY F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY κ _ _ n z hZ
  have h0 : Y0 x j2 := hY.toY0
  have hG : (sysY x j2 d).Good := (hRY F K K' d x j2 h0).2.1 d
  have hA0 : (sysY x j2 d).admitted n11 (sysY x j2 d).mu := (hTh d K' (DR ℂ K') (sysY x j2 d) hG).1
  have hAz : (sysY x j2 d).admitted n (fun l => gS j2 (z l)) := fun i j k => by
    have h2 := (hGM F K K' d x j2 h0 0 (Nat.zero_le _)).2.2.1 {i} {j} _ (hZ.adm i j k)
    rw [gS_r] at h2
    exact h2
  have hA1 : (sysY x j2 d).admitted (app n11 n) (gG x j2 z) := admissible_append _ _ _ _ _ hA0 hAz
  have hA2 : (sysY x j2 d).admitted n10 (gT x j2) := fun i j l => by
    have := hG.memX {i} {j} (Finset.singleton_nonempty j) i (Finset.mem_singleton_self i) l.succ
    simpa [Sys.r, Sys.u, n10, gT] using this
  have hA3 : (sysY x j2 d).admitted (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) := admissible_append _ _ _ _ _ hA1 hA2
  refine ⟨hA1, hA2, hA3, fun I J hI hJ => ?_⟩
  have c1 := cols_gen x j2 hKE hOk hRS h0 hG _ _ hA1 I J hI hJ
  have c2 := cols_gen x j2 hKE hOk hRS h0 hG _ _ hA2 I J hI hJ
  have c3 := cols_gen x j2 hKE hOk hRS h0 hG _ _ hA3 I J hI hJ
  have hi := pk_mem' hI
  have hj := pk_mem' hJ
  have pG : ∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ,
      (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r (app n11 n) (gG x j2 z) (pk I) (pk J) l) 0) →
      J = {0} ∧ ∃ e0 ∈ Fx, Over x j2 e e0 :=
    fun e he => hPtG F K K' d x j2 Fx A hY κ n z hZ I J _ hi _ hj e he
  have pT : ∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ,
      (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n10 (gT x j2) (pk I) (pk J) l) 0) →
      ∃ e0, Over x j2 e e0 :=
    fun e he => hPtT F K K' d x j2 h0 I J _ hi _ hj e he
  refine ⟨c1.1 ?_, c2.1 ?_, c3.1 ?_, fun hne m => ⟨c1.2 ?_ m, c3.2 ?_ m⟩⟩
  · intro e he
    obtain ⟨hJ0, e0, he0, hO⟩ := pG e he
    refine ⟨e0, hO, fun l => ?_⟩
    rw [hO.1, hJ0, pk_zero']
    obtain ⟨N, -, -, -, hN⟩ := hFix F K K' d x j2 Fx A hY e0 he0
    exact inSp_sub _ ((sysY x j2 d).r (app n11 n) (gG x j2 z) 0 0) (fun a => toLex (Sum.inl (dj 0 a))) (hN l)
  · intro e he
    obtain ⟨e0, hO⟩ := pT e he
    refine ⟨e0, hO, fun l => ?_⟩
    rw [← rT x j2 (pk I) (pk J) l (by rw [hO.1, pk_zero'])]
    exact inSp_self _ _ l
  · intro e he
    obtain ⟨e0, hO⟩ := pT e fun l => he (toLex (Sum.inr l))
    refine ⟨e0, hO, fun l => ?_⟩
    rw [← rT x j2 (pk I) (pk J) l (by rw [hO.1, pk_zero'])]
    exact inSp_sub _ ((sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) (pk I) (pk J))
      (fun a => toLex (Sum.inr a)) (inSp_self _ ((sysY x j2 d).r n10 (gT x j2) (pk I) (pk J)) l)
  · intro e he
    obtain ⟨hJ0, e0, -, hO⟩ := pG e he
    exact hne.elim (fun h => h hO.1) (fun h => h hJ0)
  · intro e he
    obtain ⟨hJ0, e0, -, hO⟩ := pG e fun l => he (toLex (Sum.inl l))
    exact hne.elim (fun h => h hO.1) (fun h => h hJ0)
end

