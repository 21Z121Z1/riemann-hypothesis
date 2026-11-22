import Formalism.ThetaLogCoordinates.DualWeylCoordinates.Bundle0002
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0001

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.BCoreW
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qb_domLE_refl (mu : Fin n → ℤ) : DomLE mu mu := ⟨fun _ => le_rfl, rfl⟩

lemma qb_domLE_trans {a b c : Fin n → ℤ} (h1 : DomLE a b) (h2 : DomLE b c) : DomLE a c :=
  ⟨fun i => (h1.1 i).trans (h2.1 i), h1.2.trans h2.2⟩

lemma qb_eq_of_psum_eq {f g : Fin n → ℤ}
    (h : ∀ a : Fin n, ∑ b ∈ univ.filter (· ≤ a), f b = ∑ b ∈ univ.filter (· ≤ a), g b) : f = g := by
  funext a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    have h1 := h a
    have e : (univ.filter (· ≤ a) : Finset (Fin n)) = insert a (univ.filter (· < a)) := by
      ext b; simp [le_iff_eq_or_lt]
    rw [e, sum_insert (by simp), sum_insert (by simp)] at h1
    have h2 : ∑ b ∈ univ.filter (· < a), f b = ∑ b ∈ univ.filter (· < a), g b :=
      sum_congr rfl fun b hb => ih b (by simpa using hb)
    linarith

def qb_psi (mu : Fin n → ℤ) : ℤ := ∑ a, ∑ b ∈ univ.filter (· ≤ a), mu b

lemma qb_psi_le {nu mu : Fin n → ℤ} (h : DomLE nu mu) : qb_psi nu ≤ qb_psi mu :=
  sum_le_sum fun a _ => h.1 a

lemma qb_eq_of_psi {nu mu : Fin n → ℤ} (h : DomLE nu mu) (h2 : qb_psi mu ≤ qb_psi nu) : nu = mu := by
  apply qb_eq_of_psum_eq
  by_contra hne
  push Not at hne
  obtain ⟨a, ha⟩ := hne
  have : qb_psi nu < qb_psi mu :=
    sum_lt_sum (fun i _ => h.1 i) ⟨a, mem_univ _, lt_of_le_of_ne (h.1 a) ha⟩
  linarith

lemma qb_domLE_antisymm {nu mu : Fin n → ℤ} (h1 : DomLE nu mu) (h2 : DomLE mu nu) : nu = mu :=
  qb_eq_of_psi h1 (qb_psi_le h2)

lemma qb_exists_max (s : Finset (Fin n → ℤ)) (hs : s.Nonempty) :
    ∃ nu ∈ s, ∀ mu ∈ s, DomLE nu mu → mu = nu := by
  obtain ⟨nu, hnu, hmax⟩ := s.exists_max_image qb_psi hs
  exact ⟨nu, hnu, fun mu hmu hle => (qb_eq_of_psi hle (hmax mu hmu)).symm⟩

lemma qb_exists_max_above (s : Finset (Fin n → ℤ)) {mu0 : Fin n → ℤ} (h0 : mu0 ∈ s) :
    ∃ nu ∈ s, DomLE mu0 nu ∧ ∀ mu ∈ s, DomLE nu mu → mu = nu := by
  classical
  obtain ⟨nu, hnu, hmax⟩ := qb_exists_max (s.filter fun mu => DomLE mu0 mu)
    ⟨mu0, by simp [h0, qb_domLE_refl]⟩
  rw [mem_filter] at hnu
  exact ⟨nu, hnu.1, hnu.2, fun mu hmu hle =>
    hmax mu (by rw [mem_filter]; exact ⟨hmu, qb_domLE_trans hnu.2 hle⟩) hle⟩

variable [NeZero n]

def qb_wtT (mu : Fin n → ℤ) (I : TIdx mu) : Fin n → ℤ :=
  fun a => mu (lastIdx n) + ((univ.filter fun c : ↥(TCols mu) => a ∈ (I c).1).card : ℤ)

lemma qb_sum_wtT (mu : Fin n → ℤ) (I : TIdx mu) (s : Finset (Fin n)) :
    ∑ b ∈ s, qb_wtT mu I b =
      (s.card : ℤ) * mu (lastIdx n) + ∑ c : ↥(TCols mu), ((s.filter (· ∈ (I c).1)).card : ℤ) := by
  unfold qb_wtT
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  congr 1
  simp only [card_filter, Nat.cast_sum]
  rw [sum_comm]

lemma qb_mem_canT (mu : Fin n → ℤ) (c : ↥(TCols mu)) (b : Fin n) :
    b ∈ (canT mu c).1 ↔ b.val < colH mu c := by
  simp only [canT, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩; exact x.2
  · intro h; exact ⟨⟨b.val, h⟩, by ext; rfl⟩

lemma qb_col_le (mu : Fin n → ℤ) (c : ↥(TCols mu)) (J : Finset (Fin n)) (hJ : J.card = colH mu c) (a : Fin n) :
    ((univ.filter (· ≤ a)).filter (· ∈ J)).card ≤ ((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card := by
  by_cases h : a.val < colH mu c
  · apply card_le_card
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    exact ⟨hb.1, (qb_mem_canT mu c b).2 (lt_of_le_of_lt hb.1 h)⟩
  · calc ((univ.filter (· ≤ a)).filter (· ∈ J)).card ≤ J.card :=
          card_le_card fun b hb => (mem_filter.1 hb).2
      _ = (canT mu c).1.card := by rw [hJ, (canT mu c).2]
      _ ≤ _ := card_le_card fun b hb => by
          simp only [mem_filter, mem_univ, true_and]
          refine ⟨?_, hb⟩
          have := (qb_mem_canT mu c b).1 hb
          exact Fin.le_def.2 (by omega)

lemma qb_col_eq (mu : Fin n → ℤ) (c : ↥(TCols mu)) (J : Finset (Fin n)) (hJ : J.card = colH mu c)
    (h : ∀ a : Fin n, ((univ.filter (· ≤ a)).filter (· ∈ J)).card =
      ((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card) : J = (canT mu c).1 := by
  rcases Nat.eq_zero_or_pos (colH mu c) with h0 | hpos
  · have h1 : J = ∅ := card_eq_zero.1 (hJ.trans h0)
    have h2 : (canT mu c).1 = ∅ := card_eq_zero.1 ((canT mu c).2.trans h0)
    rw [h1, h2]
  · have hn := colH_le mu c
    let a : Fin n := ⟨colH mu c - 1, by omega⟩
    have hc : (canT mu c).1 ⊆ (univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1) := fun b hb => by
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨?_, hb⟩
      have := (qb_mem_canT mu c b).1 hb
      exact Fin.le_def.2 (by simp only [a]; omega)
    have h3 : J.card ≤ ((univ.filter (· ≤ a)).filter (· ∈ J)).card := by
      rw [h a, hJ]; exact (canT mu c).2.symm.le.trans (card_le_card hc)
    have h4 : (univ.filter (· ≤ a)).filter (· ∈ J) = J :=
      eq_of_subset_of_card_le (fun b hb => (mem_filter.1 hb).2) h3
    apply eq_of_subset_of_card_le
    · intro b hb
      rw [← h4] at hb
      simp only [mem_filter, mem_univ, true_and] at hb
      have := Fin.le_def.1 hb.1
      exact (qb_mem_canT mu c b).2 (by simp only [a] at this; omega)
    · rw [hJ, (canT mu c).2]

lemma qb_lt_colH_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (b : Fin n) :
    b.val < colH mu c ↔ c ≤ mu b := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    have : (univ.filter fun m => c ≤ mu m) ⊆ Finset.Iio b := fun m hm => by
      simp only [mem_filter, mem_univ, true_and] at hm
      rw [mem_Iio]
      by_contra hmb
      exact hc (hm.trans (hmu (not_lt.1 hmb)))
    have := card_le_card this
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have : Finset.Iic b ⊆ (univ.filter fun m => c ≤ mu m) := fun m hm => by
      simp only [mem_filter, mem_univ, true_and]
      exact h.trans (hmu (mem_Iic.1 hm))
    have := card_le_card this
    rw [Fin.card_Iic] at this
    omega

lemma qb_le_lastIdx (b : Fin n) : b ≤ lastIdx n := Fin.le_def.2 (by have := b.2; simp only [lastIdx]; omega)

lemma qb_wtT_can {mu : Fin n → ℤ} (hmu : Dominant mu) : qb_wtT mu (canT mu) = mu := by
  funext b
  unfold qb_wtT
  have e : ((univ.filter fun c : ↥(TCols mu) => b ∈ (canT mu c).1).map (Function.Embedding.subtype _)) =
      Finset.Ioc (mu (lastIdx n)) (mu b) := by
    ext c
    rw [mem_map, mem_Ioc]
    constructor
    · rintro ⟨⟨c', hc'⟩, h1, rfl⟩
      rw [mem_filter, qb_mem_canT, qb_lt_colH_iff hmu] at h1
      exact ⟨(mem_Ioc.1 hc').1, h1.2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨c, mem_Ioc.2 ⟨h1, h2.trans (hmu (Fin.zero_le b))⟩⟩, ?_, rfl⟩
      rw [mem_filter, qb_mem_canT, qb_lt_colH_iff hmu]
      exact ⟨mem_univ _, h2⟩
  rw [← card_map (Function.Embedding.subtype _), e, Int.card_Ioc]
  have := hmu (qb_le_lastIdx b)
  rw [Int.toNat_of_nonneg (by omega)]
  ring

lemma qb_wtT_le {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) : DomLE (qb_wtT mu I) mu := by
  constructor
  · intro a
    conv_rhs => rw [← qb_wtT_can hmu]
    rw [qb_sum_wtT, qb_sum_wtT]
    have : ∑ c : ↥(TCols mu), (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) ≤
        ∑ c : ↥(TCols mu), (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) :=
      sum_le_sum fun c _ => by exact_mod_cast qb_col_le mu c (I c).1 (I c).2 a
    linarith
  · conv_rhs => rw [← qb_wtT_can hmu]
    rw [qb_sum_wtT, qb_sum_wtT]
    congr 1
    refine sum_congr rfl fun c _ => ?_
    simp only [filter_univ_mem]
    rw [(I c).2, (canT mu c).2]

lemma qb_wtT_eq_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) : qb_wtT mu I = mu ↔ I = canT mu := by
  constructor
  · intro h
    funext c
    apply Subtype.ext
    apply qb_col_eq mu c (I c).1 (I c).2
    intro a
    have h1 : ∑ b ∈ univ.filter (· ≤ a), qb_wtT mu I b = ∑ b ∈ univ.filter (· ≤ a), qb_wtT mu (canT mu) b := by
      rw [h, qb_wtT_can hmu]
    rw [qb_sum_wtT, qb_sum_wtT] at h1
    have h2 : ∑ c : ↥(TCols mu), ((((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) -
        (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ)) = 0 := by
      rw [sum_sub_distrib]; linarith
    have h3 := (sum_eq_zero_iff_of_nonneg (fun c _ => by
      have := qb_col_le mu c (I c).1 (I c).2 a
      have : (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) ≤
        (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) := by exact_mod_cast this
      linarith)).1 h2 c (mem_univ c)
    have : (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) =
        (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) := by linarith
    exact_mod_cast this
  · rintro rfl; exact qb_wtT_can hmu

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcEvGLGenPtInt
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qc_genMat_det_ne (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (genMat R n).det ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin n) R

lemma qc_isDomain (R : Type) [CommRing R] [IsDomain R] (n : ℕ) : IsDomain (GLCoord R n) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (R := MvPolynomial (Fin n × Fin n) R) (S := GLCoord R n)
    (M := Submonoid.powers (genMat R n).det)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (qc_genMat_det_ne R n))

def qc_genPt (F : Type) [CommRing F] (n : ℕ) : GL (Fin n) (GLCoord F n) :=
  Matrix.nonsingInvUnit ((algebraMap _ (GLCoord F n)).mapMatrix (genMat F n))
    (by rw [← RingHom.map_det]; exact IsLocalization.Away.algebraMap_isUnit _)

lemma qc_genPt_val (F : Type) [CommRing F] (n : ℕ) (a b : Fin n) :
    (qc_genPt F n).val a b = algebraMap (MvPolynomial (Fin n × Fin n) F) (GLCoord F n) (X (a, b)) := rfl

lemma qc_mapCoord_alg {n : ℕ} (F : Type) [CommRing F] (P : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) F (algebraMap _ (GLCoord ℤ n) P) =
      algebraMap _ (GLCoord F n) (MvPolynomial.map (Int.castRingHom F) P) :=
  IsLocalization.Away.lift_eq _ _ _

lemma qc_hom_ext {n : ℕ} {R : Type} [CommRing R] (f g : GLCoord ℤ n →+* R)
    (h : ∀ a b, f (algebraMap (MvPolynomial (Fin n × Fin n) ℤ) _ (X (a, b))) =
      g (algebraMap (MvPolynomial (Fin n × Fin n) ℤ) _ (X (a, b)))) : f = g := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (genMat ℤ n).det) ?_
  apply MvPolynomial.ringHom_ext
  · intro r; simp
  · rintro ⟨a, b⟩; exact h a b

lemma qc_evGL_genPt (F : Type) [CommRing F] (n : ℕ) : evGL (qc_genPt F n) = mapCoord F := by
  apply qc_hom_ext
  intro a b
  rw [qc_evGL_alg, qc_mapCoord_alg]
  simp [qc_genPt_val]

lemma qc_evGL_genPt_int (n : ℕ) : evGL (qc_genPt ℤ n) = RingHom.id _ := by
  apply qc_hom_ext
  intro a b
  rw [qc_evGL_alg]
  simp [qc_genPt_val]

lemma qc_evGL_map {n : ℕ} {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (g : GL (Fin n) R) :
    evGL (Matrix.GeneralLinearGroup.map φ g) = φ.comp (evGL g) := by
  apply qc_hom_ext
  intro a b
  rw [RingHom.comp_apply, qc_evGL_alg, qc_evGL_alg]
  simp only [coe_eval₂Hom, eval₂_X]
  rfl

lemma qc_map_span_mem {A B F : Type} [CommRing A] [CommRing B] [Field F] [Module F B] (φ : A →+* B) (S : Set A)
    (y : A) (hy : y ∈ Submodule.span ℤ S) : φ y ∈ Submodule.span F (φ '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul m x _ hx => rw [map_zsmul]; exact zsmul_mem hx m

lemma qc_span_eq {A B F : Type} [CommRing A] [CommRing B] [Field F] [Module F B] (φ : A →+* B) (S T : Set A)
    (h : Submodule.span ℤ S = Submodule.span ℤ T) : Submodule.span F (φ '' S) = Submodule.span F (φ '' T) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact qc_map_span_mem φ T x (h ▸ Submodule.subset_span hx)
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact qc_map_span_mem φ S x (h.symm ▸ Submodule.subset_span hx)

section SMu

variable {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}

lemma qc_card_eq (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β) : Fintype.card M.ι = dMu mu := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  have h1 := finrank_span_eq_card hβ.1
  have h2 := finrank_span_eq_card (hS n mu hmu).1
  rw [hβ.2.1] at h1
  rw [(hS n mu hmu).2] at h2
  rw [dMu, Nat.card_eq_fintype_card, ← h1, ← h2]

lemma qc_li_field (hA : LemmaA) (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β) (F : Type) [Field F] :
    LinearIndependent F (fun i => mapCoord (n := n) F (β i)) := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  rw [linearIndependent_iff_card_eq_finrank_span]
  have h1 := linearIndependent_iff_card_eq_finrank_span.1 (hA n mu hmu F)
  have h2 : Set.range (fun i => mapCoord (n := n) F (β i)) = mapCoord (n := n) F '' Set.range β := by
    rw [← Set.range_comp]; rfl
  have h3 : Set.range (fun I : {I : TIdx mu // StdT I} => mapCoord (n := n) F (brk mu I.1)) =
      mapCoord (n := n) F '' Set.range (fun I : {I : TIdx mu // StdT I} => brk mu I.1) := by
    rw [← Set.range_comp]; rfl
  have h4 := qc_span_eq (F := F) (mapCoord (n := n) F) _ _ (hβ.2.1.trans (hS n mu hmu).2.symm)
  rw [Set.finrank, h2, h4, ← h3, ← Set.finrank, ← h1, qc_card_eq hS hmu hβ, dMu, Nat.card_eq_fintype_card]

lemma qc_two (hβ : IsSMu M mu β) (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I)
    {R : Type} [CommRing R] (x g : GL (Fin n) R) (I : TIdx mu) :
    ∑ j, evGL g ((M.A * ph.map (Int.castRingHom (GLCoord ℤ n)) : Matrix _ _ _) j I) * evGL x (β j) =
      ∑ j, evGL g ((ph.map (Int.castRingHom (GLCoord ℤ n)) * TMat mu : Matrix _ _ _) j I) * evGL x (β j) := by
  have e1 : evGL (x * g) (brk mu I) = ∑ j, evGL g ((M.A * ph.map (Int.castRingHom (GLCoord ℤ n)) : Matrix _ _ _) j I) * evGL x (β j) := by
    rw [← hph I]
    simp only [map_sum, map_zsmul, hβ.2.2, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_mul, eq_intCast,
      map_intCast, zsmul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : evGL (x * g) (brk mu I) = ∑ j, evGL g ((ph.map (Int.castRingHom (GLCoord ℤ n)) * TMat mu : Matrix _ _ _) j I) * evGL x (β j) := by
    rw [brk, qc_TMat_mul]
    have : ∀ K, evGL x (TMat mu (canT mu) K) = ∑ j, (ph j K : R) * evGL x (β j) := by
      intro K
      show evGL x (brk mu K) = _
      rw [← hph K]
      simp only [map_sum, zsmul_eq_mul, map_mul, map_intCast]
    simp only [this, map_sum, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_mul, eq_intCast,
      map_intCast]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [← e1, e2]

theorem qc_equiv (hA : LemmaA) (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) :
    M.A * ph.map (Int.castRingHom _) = ph.map (Int.castRingHom _) * TMat mu := by
  have := qc_isDomain ℤ n
  let F := FractionRing (GLCoord ℤ n)
  let ψ : GLCoord ℤ n →+* GLCoord F n := (algebraMap F (GLCoord F n)).comp (algebraMap (GLCoord ℤ n) F)
  have hli := qc_li_field hA hS hmu hβ F
  ext i I
  have h := qc_two hβ ph hph (qc_genPt F n) (Matrix.GeneralLinearGroup.map ψ (qc_genPt ℤ n)) I
  rw [qc_evGL_genPt, qc_evGL_map, qc_evGL_genPt_int, RingHom.comp_id] at h
  have h' : ∑ j, (algebraMap (GLCoord ℤ n) F ((M.A * ph.map (Int.castRingHom (GLCoord ℤ n)) : Matrix _ _ _) j I) -
      algebraMap (GLCoord ℤ n) F ((ph.map (Int.castRingHom (GLCoord ℤ n)) * TMat mu : Matrix _ _ _) j I)) • mapCoord (n := n) F (β j) = 0 := by
    simp only [Algebra.smul_def, map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact h
  have h'' := Fintype.linearIndependent_iff.1 hli _ h' i
  exact IsFractionRing.injective (GLCoord ℤ n) F (sub_eq_zero.1 h'')

end SMu

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsMnTranspose
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def qs_sg (A : Finset (Fin n)) (m : Fin n) : ℤ := (-1) ^ (A.filter (m < ·)).card

def qs_mn {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R) (J I : Finset (Fin n)) : R :=
  if h : J.card = I.card then
    Matrix.det (Matrix.of fun a b : Fin I.card => g (J.orderEmbOfFin h a) (I.orderEmbOfFin rfl b)) else 0

variable {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R)

lemma qs_mn_eq {h : ℕ} (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h) :
    qs_mn g J I = Matrix.det (Matrix.of fun a b : Fin h => g (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) := by
  subst hI; rw [qs_mn, dif_pos hJ]

lemma qs_mn_ne {J I : Finset (Fin n)} (h : J.card ≠ I.card) : qs_mn g J I = 0 := dif_neg h

lemma qs_mn_transpose (J I : Finset (Fin n)) : qs_mn g.transpose J I = qs_mn g I J := by
  by_cases h : J.card = I.card
  · rw [qs_mn_eq _ J I h rfl, qs_mn_eq _ I J rfl h, ← Matrix.det_transpose]; rfl
  · rw [qs_mn_ne _ h, qs_mn_ne _ (Ne.symm h)]

lemma qs_oe_succAbove {h : ℕ} (s : Finset (Fin n)) (hs : s.card = h + 1) (j : Fin (h + 1))
    (hs' : (s.erase (s.orderEmbOfFin hs j)).card = h) (i : Fin h) :
    s.orderEmbOfFin hs (j.succAbove i) = (s.erase (s.orderEmbOfFin hs j)).orderEmbOfFin hs' i := by
  have := Finset.orderEmbOfFin_unique hs' (f := fun i => s.orderEmbOfFin hs (j.succAbove i))
    (fun x => Finset.mem_erase.2 ⟨(s.orderEmbOfFin hs).injective.ne (Fin.succAbove_ne j x),
      Finset.orderEmbOfFin_mem _ _ _⟩)
    ((s.orderEmbOfFin hs).strictMono.comp (Fin.strictMono_succAbove j))
  exact congrFun this i

lemma qs_card_gt {h : ℕ} (s : Finset (Fin n)) (hs : s.card = h + 1) (j : Fin (h + 1)) :
    ((s.erase (s.orderEmbOfFin hs j)).filter (s.orderEmbOfFin hs j < ·)).card = h - j := by
  have : (s.erase (s.orderEmbOfFin hs j)).filter (s.orderEmbOfFin hs j < ·) =
      (Finset.Ioi j).map (s.orderEmbOfFin hs).toEmbedding := by
    ext x
    simp only [mem_filter, mem_erase, mem_map, mem_Ioi, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨⟨_, hx⟩, hlt⟩
      have hx' : x ∈ Set.range (s.orderEmbOfFin hs) := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨i, rfl⟩ := hx'
      exact ⟨i, (s.orderEmbOfFin hs).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨((s.orderEmbOfFin hs).lt_iff_lt.2 hi).ne', Finset.orderEmbOfFin_mem _ _ _⟩,
        (s.orderEmbOfFin hs).lt_iff_lt.2 hi⟩
  rw [this, card_map, Fin.card_Ioi]; omega

lemma qs_sum_oe {M : Type*} [AddCommMonoid M] {h : ℕ} (I : Finset (Fin n)) (hI : I.card = h) (f : Fin n → M) :
    ∑ m ∈ I, f m = ∑ j : Fin h, f (I.orderEmbOfFin hI j) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ I hI]
  rw [Finset.sum_map]; rfl

lemma qs_lap_row {h : ℕ} (r : Fin (h + 1) → Fin n) (p : Fin (h + 1)) (I : Finset (Fin n)) (hI : I.card = h + 1)
    (A : Finset (Fin n)) (hA : A.card = h) (hr : ∀ i, r (p.succAbove i) = A.orderEmbOfFin hA i) :
    ∑ m ∈ I, ((qs_sg (I.erase m) m : ℤ) : R) * qs_mn g A (I.erase m) * g (r p) m =
      (-1) ^ (h - (p : ℕ)) * Matrix.det (Matrix.of fun a b : Fin (h + 1) => g (r a) (I.orderEmbOfFin hI b)) := by
  rw [Matrix.det_succ_row _ p, Finset.mul_sum, qs_sum_oe I hI]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (I.erase (I.orderEmbOfFin hI j)).card = h := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hI]; rfl
  rw [qs_mn_eq g A _ hA hc, qs_sg, qs_card_gt I hI j]
  have hM : (Matrix.of fun a b : Fin (h + 1) => g (r a) (I.orderEmbOfFin hI b)).submatrix p.succAbove j.succAbove =
      Matrix.of fun a b : Fin h => g (A.orderEmbOfFin hA a) ((I.erase (I.orderEmbOfFin hI j)).orderEmbOfFin hc b) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    rw [hr, qs_oe_succAbove I hI j hc]
  rw [hM]
  have hs : ((-1 : R)) ^ (h - (j : ℕ)) = (-1) ^ (h - (p : ℕ)) * (-1) ^ ((p : ℕ) + (j : ℕ)) := by
    rw [← pow_add]
    have hj := j.2; have hp := p.2
    have : h - (p : ℕ) + ((p : ℕ) + (j : ℕ)) = (h - (j : ℕ)) + 2 * (j : ℕ) := by omega
    rw [this, pow_add, pow_mul]; simp
  push_cast
  rw [hs]
  simp only [Matrix.of_apply]
  ring

theorem qs_laplace (A I : Finset (Fin n)) (k : Fin n) :
    ∑ m ∈ I, ((qs_sg (I.erase m) m : ℤ) : R) * qs_mn g A (I.erase m) * g k m =
      if k ∈ A then 0 else ((qs_sg A k : ℤ) : R) * qs_mn g (insert k A) I := by
  by_cases hc : I.card = A.card + 1
  · split_ifs with hk
    ·
      have hk' : k ∈ Set.range (A.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hk
      obtain ⟨q, hq⟩ := hk'
      have := qs_lap_row g (Fin.cons k (A.orderEmbOfFin rfl)) 0 I hc A rfl (fun i => by simp)
      simp only [Fin.cons_zero] at this
      rw [this, Matrix.det_zero_of_row_eq (i := 0) (j := q.succ) (Fin.succ_ne_zero q).symm, mul_zero]
      ext b; simp [hq]
    · have hs : (insert k A).card = A.card + 1 := Finset.card_insert_of_notMem hk
      have hk' : k ∈ Set.range ((insert k A).orderEmbOfFin hs) := by
        rw [Finset.range_orderEmbOfFin]; simp
      obtain ⟨p, hp⟩ := hk'
      have he : (insert k A).erase ((insert k A).orderEmbOfFin hs p) = A := by
        rw [hp, Finset.erase_insert hk]
      have hAc : ((insert k A).erase ((insert k A).orderEmbOfFin hs p)).card = A.card := by rw [he]
      have := qs_lap_row g ((insert k A).orderEmbOfFin hs) p I hc _ hAc
        (fun i => qs_oe_succAbove _ hs p hAc i)
      have h2 := qs_card_gt (insert k A) hs p
      rw [he, hp] at this h2
      rw [this, qs_mn_eq g _ _ hs hc, qs_sg, h2]
      push_cast; rfl
  · have h1 : ∀ m ∈ I, qs_mn g A (I.erase m) = 0 := fun m hm => qs_mn_ne g (by
      rw [Finset.card_erase_of_mem hm]
      have := Finset.card_pos.2 ⟨m, hm⟩
      omega)
    rw [Finset.sum_eq_zero (fun m hm => by rw [h1 m hm]; simp)]
    split_ifs with hk
    · rfl
    · rw [qs_mn_ne g (by rw [Finset.card_insert_of_notMem hk]; omega), mul_zero]

theorem qs_laplace_col (A I : Finset (Fin n)) (m : Fin n) :
    ∑ k ∈ A, ((qs_sg (A.erase k) k : ℤ) : R) * qs_mn g (A.erase k) I * g k m =
      if m ∈ I then 0 else ((qs_sg I m : ℤ) : R) * qs_mn g A (insert m I) := by
  have := qs_laplace g.transpose I A m
  simpa only [qs_mn_transpose, Matrix.transpose_apply] using this

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

