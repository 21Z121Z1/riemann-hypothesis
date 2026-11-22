import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0012
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0006
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.Bundle0001

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ABridge
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

lemma qa_can_emb {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have := Finset.orderEmbOfFin_unique (s := (canT mu c).1) (canT mu c).2
    (f := fun a : Fin (colH mu c) => Fin.castLE (colH_le mu c) a) (by intro x; simp [canT])
    (Fin.strictMono_castLE _)
  exact (congrFun this a).symm

lemma qa_minor (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) :
    Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat R n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b)) =
    rename Prod.swap (initMinor R (qa_row I c) (colH_le mu c)) := by
  conv_rhs => rw [initMinor, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext a b
  simp [Matrix.transpose_apply, genMat, qa_row, qa_can_emb]

lemma qa_prod_minor (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    ∏ c : ↥(TCols mu), Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat R n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b)) =
    rename Prod.swap (qa_P R I) := by
  unfold qa_P
  rw [map_prod]
  exact Finset.prod_congr rfl fun c _ => qa_minor R I c

theorem qa_brk_eq {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brk mu I = ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      algebraMap (MvPolynomial (Fin n × Fin n) ℤ) (GLCoord ℤ n) (rename Prod.swap (qa_P ℤ I)) := by
  unfold brk TMat minorC
  rw [← qa_prod_minor, map_prod]

theorem qa_brkPol_eq {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brkPol mu I = (genMat ℤ n).det ^ (mu (lastIdx n)).toNat * rename Prod.swap (qa_P ℤ I) := by
  unfold brkPol
  rw [qa_prod_minor]

lemma qa_det_ne (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) : (genMat R n).det ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin n) R

lemma qa_algebraMap_inj (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) :
    Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) :=
  IsLocalization.injective (GLCoord R n)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (qa_det_ne R n))

def qa_Phi (R : Type*) [CommRing R] (n : ℕ) (u : GLCoord R n) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] GLCoord R n :=
  (LinearMap.mulLeft R u) ∘ₗ (IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).toLinearMap ∘ₗ
    (rename (R := R) (Prod.swap : Fin n × Fin n → Fin n × Fin n)).toLinearMap

lemma qa_Phi_apply (R : Type*) [CommRing R] (n : ℕ) (u : GLCoord R n) (f : MvPolynomial (Fin n × Fin n) R) :
    qa_Phi R n u f = u * algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (rename Prod.swap f) := rfl

lemma qa_Phi_inj (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) (u : GLCoord R n) (hu : IsUnit u) :
    Function.Injective (qa_Phi R n u) := by
  intro f g h
  rw [qa_Phi_apply, qa_Phi_apply] at h
  exact rename_injective _ Prod.swap_injective (qa_algebraMap_inj R n (hu.mul_left_cancel h))

def qa_intLin {M N : Type*} [AddCommGroup M] {i1 : Module ℤ M} [AddCommGroup N] {i2 : Module ℤ N}
    (f : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 i2) :
    @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 (AddCommGroup.toIntModule N) :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 (AddCommGroup.toIntModule N) ⟨f, f.map_add⟩
    (fun z x => (f.map_smul z x).trans (int_smul_eq_zsmul i2 z (f x)))

def qa_PhiZ (n : ℕ) (u : GLCoord ℤ n) := qa_intLin (qa_Phi ℤ n u)

lemma qa_PhiZ_apply (n : ℕ) (u : GLCoord ℤ n) (f : MvPolynomial (Fin n × Fin n) ℤ) :
    qa_PhiZ n u f = u * algebraMap (MvPolynomial (Fin n × Fin n) ℤ) (GLCoord ℤ n) (rename Prod.swap f) := rfl

lemma qa_PhiZ_inj (n : ℕ) (u : GLCoord ℤ n) (hu : IsUnit u) : Function.Injective (qa_PhiZ n u) :=
  qa_Phi_inj ℤ n u hu

lemma qa_mapCoord_algebraMap {n : ℕ} (F : Type) [CommRing F] (f : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) F (algebraMap _ (GLCoord ℤ n) f) =
      algebraMap _ (GLCoord F n) (MvPolynomial.map (Int.castRingHom F) f) := by
  unfold mapCoord
  rw [IsLocalization.Away.lift_eq]
  rfl

theorem qa_mapCoord_brk {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (F : Type) [CommRing F] (I : TIdx mu) :
    mapCoord (n := n) F (brk mu I) =
      qa_Phi F n (mapCoord (n := n) F ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) (qa_P F I) := by
  rw [qa_brk_eq, map_mul, qa_mapCoord_algebraMap, qa_Phi_apply, MvPolynomial.map_rename, map_tableauBideterminant]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.HighestVectorsRationalSpan
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qd_ev_point (M : GLMod n) (nu : Fin n → ℤ) (x : M.ι → ℚ) {R' : Type} [CommRing R'] [Algebra ℚ R']
    (g : GL (Fin n) R') (i : M.ι) :
    evGLR (R := ℚ) g (qb_ev M ℚ nu x i) =
      Matrix.mulVec ((prMu M nu).map (Int.castRingHom R'))
        (Matrix.mulVec (M.A.map (evGL g)) (fun l => algebraMap ℚ R' (x l))) i := by
  rw [qb_ev_apply]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_intCast, qd_evGLR_mapCoord, qd_ev_algebraMap,
    Matrix.map_apply, Int.coe_castRingHom]

lemma qd_ev_inv (M : GLMod n) (la nu : Fin n → ℤ) (x : M.ι → ℚ) (hx : IsHighest M ℚ la x)
    {R' : Type} [CommRing R'] [Algebra ℚ R'] (g u : GL (Fin n) R') (hu1 : ∀ a, u.val a a = 1)
    (hu2 : ∀ a b, b < a → u.val a b = 0) (i : M.ι) :
    evGLR (R := ℚ) (g * u) (qb_ev M ℚ nu x i) = evGLR (R := ℚ) g (qb_ev M ℚ nu x i) := by
  rw [qd_ev_point, qd_ev_point, M.mul, ← Matrix.mulVec_mulVec, hx.2 R' u hu1 hu2]

variable [NeZero n]

lemma qd_canT_std (mu : Fin n → ℤ) : StdT (canT mu) := by
  intro c hc t
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x hx
  simp only [canT, Finset.mem_map, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  have hle : colH mu ((c : ℤ) + 1) ≤ colH mu c := by
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    omega
  exact ⟨⟨a.1, lt_of_lt_of_le a.2 hle⟩, rfl⟩

def qd_f {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (j : CF.J) : GLCoord ℚ n :=
  ∑ I : {I : TIdx (CF.mu j) // StdT I}, a ⟨j, I⟩ • mapCoord ℚ (brk (CF.mu j) I.1)

lemma qd_f_mem {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (j : CF.J) :
    qd_f CF a j ∈ Submodule.span ℚ (Set.range fun I : TIdx (CF.mu j) => mapCoord ℚ (brk (CF.mu j) I)) :=
  Submodule.sum_mem _ fun I _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨I.1, rfl⟩)

lemma qd_ev_expand {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (nu : Fin n → ℤ)
    (hmax : ∀ y, a y ≠ 0 → DomLE nu (CF.mu y.1) → CF.mu y.1 = nu) (i : M.ι) :
    qb_ev M ℚ nu (∑ y, a y • qb_vecF CF ℚ y) i =
      ∑ j : {j : CF.J // CF.mu j = nu}, ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : ℚ) • qd_f CF a j.1 := by
  classical
  rw [← qb_evL_apply, map_sum, Finset.sum_apply, Fintype.sum_sigma,
    ← Finset.sum_subtype (univ.filter fun j => CF.mu j = nu) (by simp)
      (fun j => ((CF.ph j i (canT (CF.mu j)) : ℤ) : ℚ) • qd_f CF a j), Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · subst hj
    rw [qd_f, Finset.smul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, Pi.smul_apply, qb_evL_apply, qb_vecF_def, qb_key_eq, smul_comm, Algebra.smul_def (R := ℚ)
      ((CF.ph j i (canT (CF.mu j)) : ℤ) : ℚ), map_intCast]
  · refine Finset.sum_eq_zero fun I _ => ?_
    rw [map_smul, Pi.smul_apply, qb_evL_apply, qb_vecF_def]
    by_cases ha : a ⟨j, I⟩ = 0
    · rw [ha, zero_smul]
    · rw [qb_key_zero CF ℚ j I.1 nu (fun hd => hj (hmax ⟨j, I⟩ ha hd)), Pi.zero_apply, smul_zero]

theorem highest_vectors_rational_span_of : LemmaA → HighestVectorsRationalSpan := by
  intro hA n _ M CF la hla x hx
  classical
  have hsp := (qb_basisR hA CF ℚ).2
  have hli := (qb_basisR hA CF ℚ).1
  obtain ⟨a, ha⟩ : ∃ a : qb_Idx CF → ℚ, ∑ y, a y • qb_vecF CF ℚ y = x := by
    have : x ∈ Submodule.span ℚ (Set.range (qb_vecF CF ℚ)) := by rw [hsp]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).1 this
  subst ha

  have h1 : ∀ y, a y ≠ 0 → qb_wtT (CF.mu y.1) y.2.1 = la := by
    have hpr : ∀ y, Matrix.mulVec ((prMu M la).map (Int.castRingHom ℚ)) (qb_vecF CF ℚ y) =
        if qb_wtT (CF.mu y.1) y.2.1 = la then qb_vecF CF ℚ y else 0 := by
      intro y
      funext i
      have := congrArg (Int.cast : ℤ → ℚ) (qb_prMu_ph CF y.1 la i y.2.1)
      push_cast at this
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.coe_castRingHom, qb_vecF, ColFam.vec]
      rw [this]
      split_ifs <;> rfl
    have h : Matrix.mulVecLin ((prMu M la).map (Int.castRingHom ℚ)) (∑ y, a y • qb_vecF CF ℚ y) =
        ∑ y, a y • qb_vecF CF ℚ y := hx.1
    rw [map_sum] at h
    simp only [map_smul, Matrix.mulVecLin_apply, hpr, smul_ite, smul_zero] at h
    have h0 := Fintype.linearIndependent_iff.1 hli
      (fun y => (if qb_wtT (CF.mu y.1) y.2.1 = la then a y else 0) - a y) (by
        simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul]
        rw [sub_eq_zero]
        exact h)
    intro y hy
    by_contra hne
    have := h0 y
    simp only [if_neg hne, zero_sub, neg_eq_zero] at this
    exact hy this

  have h3 : ∀ nu, (∀ y, a y ≠ 0 → DomLE nu (CF.mu y.1) → CF.mu y.1 = nu) →
      ∀ y, CF.mu y.1 = nu → a y ≠ 0 → y.2.1 = canT (CF.mu y.1) := by
    intro nu hmax
    have hinv : ∀ (j : {j : CF.J // CF.mu j = nu}) (R' : Type) [CommRing R'] [Algebra ℚ R'] (g u : GL (Fin n) R'),
        (∀ a, u.val a a = 1) → (∀ a b, b < a → u.val a b = 0) →
        evGLR (R := ℚ) (g * u) (qd_f CF a j.1) = evGLR (R := ℚ) g (qd_f CF a j.1) := by
      intro j R' _ _ g u hu1 hu2
      have := qb_indep_ext (k := ℚ) (W := R') _ (CF.indepQ nu)
        (fun j => evGLR (R := ℚ) (g * u) (qd_f CF a j.1) - evGLR (R := ℚ) g (qd_f CF a j.1)) (fun i => ?_) j
      · exact sub_eq_zero.1 this
      · have e := qd_ev_inv M la nu _ hx g u hu1 hu2 i
        rw [qd_ev_expand CF a nu hmax i, map_sum, map_sum] at e
        simp only [smul_sub, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        convert e using 2 <;>
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, qd_ev_algebraMap]
    intro y hy hay
    obtain ⟨c, hc⟩ := eq_smul_canonical_of_unipotent_invariant (CF.mu y.1) (qd_f CF a y.1) (qd_f_mem CF a y.1) (hinv ⟨y.1, hy⟩)
    have hind := hA n (CF.mu y.1) (CF.dom y.1) ℚ
    by_contra hne
    have := Fintype.linearIndependent_iff.1 hind
      (fun I => a ⟨y.1, I⟩ - if I = ⟨canT (CF.mu y.1), qd_canT_std _⟩ then c else 0) (by
        simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
          if_true]
        rw [sub_eq_zero]
        exact hc) y.2
    rw [if_neg (fun h => hne (congrArg Subtype.val h)), sub_zero] at this
    exact hay this
  have h4 : ∀ y, a y ≠ 0 → CF.mu y.1 = la ∧ y.2.1 = canT (CF.mu y.1) := by
    intro y0 hy0
    let s : Finset (Fin n → ℤ) := (univ.filter fun y => a y ≠ 0).image fun y => CF.mu y.1
    have hs0 : CF.mu y0.1 ∈ s := mem_image.2 ⟨y0, by simp [hy0], rfl⟩
    obtain ⟨nu, hnu, hle, hmax⟩ := qb_exists_max_above s hs0
    obtain ⟨y1, hy1, hy1nu⟩ := mem_image.1 hnu
    have hay1 : a y1 ≠ 0 := by simpa using hy1
    have hmax' : ∀ y, a y ≠ 0 → DomLE nu (CF.mu y.1) → CF.mu y.1 = nu :=
      fun y hy hd => hmax _ (mem_image.2 ⟨y, by simp [hy], rfl⟩) hd
    have hcan := h3 nu hmax' y1 hy1nu hay1
    have hw := h1 y1 hay1
    rw [hcan, qb_wtT_can (CF.dom y1.1)] at hw
    have hnula : nu = la := hy1nu.symm.trans hw
    have hle2 : DomLE la (CF.mu y0.1) := by
      rw [← h1 y0 hy0]; exact qb_wtT_le (CF.dom _) _
    have heq : CF.mu y0.1 = la := qb_domLE_antisymm (hnula ▸ hle) hle2
    exact ⟨heq, (qb_wtT_eq_iff (CF.dom _) _).1 ((h1 y0 hy0).trans heq.symm)⟩
  refine Submodule.sum_mem _ fun y _ => ?_
  by_cases hy : a y = 0
  · rw [hy, zero_smul]; exact zero_mem _
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    obtain ⟨e1, e2⟩ := h4 y hy
    refine ⟨y.1, e1, ?_⟩
    funext i
    simp only [qb_vecF]
    rw [e2]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnInterlacedLowerTri
section
open MvPolynomial

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility
open scoped MonomialOrder

theorem qn_interlaced_lowerTri {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (h : Interlaced m) : LowerTri m := by
  have key : ∀ k : ℕ, ∀ s : Fin n, s.val = k → ∀ a : Fin r, a.val < k → m (a, s) = 0 := by
    intro k
    induction k with
    | zero =>
      intro s _ a ha
      omega
    | succ k ih =>
      intro s hs a ha
      have hl : k < n := by
        have := s.isLt
        omega
      have hI := h ⟨k, hl⟩ s (by simp [hs]) a
      have hR : (∑ b : Fin r with b < a, m (b, (⟨k, hl⟩ : Fin n))) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have hba : b.val < a.val := hb
        exact ih ⟨k, hl⟩ rfl b (by omega)
      rw [hR, add_zero, Nat.le_zero, Finset.sum_eq_zero_iff] at hI
      exact hI a (by simp)
  intro a s has
  exact key s.val s rfl a has

theorem qn_lowerTriIntegral : LowerTriIntegral := by
  classical
  intro r n ν
  haveI := (colLex r n).wellFoundedLT_syn
  obtain ⟨b, hbB, hbdeg⟩ := sSBasis ℤ r n ν
  have hBmem : ∀ i, intQ r n (b i) ∈ dualWeyl ℚ r n ν := by
    intro i
    rw [← span_map_weightBasis_eq_dualWeyl (K := ℚ) hbB]
    apply Submodule.subset_span
    exact ⟨i, by rw [algebraMap_int_eq]; rfl⟩
  suffices H : ∀ s : (colLex r n).syn, ∀ Q : MvPolynomial (Fin r × Fin n) ℚ,
      (colLex r n).toSyn ((colLex r n).degree Q) = s → Q ∈ dualWeyl ℚ r n ν →
      (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e Q = z) →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' by
    intro Q hQ hint
    exact H _ Q rfl hQ hint
  intro s
  induction s using WellFoundedLT.induction with
  | ind s ih =>
    intro Q hs hQ hint
    by_cases hQ0 : Q = 0
    · exact ⟨0, by rw [hQ0, map_zero]⟩
    set m := (colLex r n).degree Q with hm
    have hInt : Interlaced m := leadInterlaced ℚ r n ν Q hQ hQ0
    have hLT : LowerTri m := qn_interlaced_lowerTri m hInt
    have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t := by
      have hhom : IsWeightedHomogeneous (colW r n) Q ν :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hQ).1
      have hw : Finsupp.weight (colW r n) m = ν :=
        hhom ((colLex r n).leadingCoeff_ne_zero_iff.2 hQ0)
      intro t
      rw [← hw]
      simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_prod_type, colW, Pi.single_apply]
    let mi : ssIdx r n ν := ⟨m, hInt, hcol⟩
    obtain ⟨hbd, hblc, -⟩ := hbdeg mi
    set B := intQ r n (b mi) with hB
    have hBmap : B = map (Int.castRingHom ℚ) (b mi) := rfl
    have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
    have hBsupp : B.support = (b mi).support := by
      rw [hBmap]
      exact support_map_of_injective _ hinj
    have hBdeg : (colLex r n).degree B = m := by
      have h1 : (colLex r n).degree (b mi) = m := hbd
      rw [← h1]
      unfold MonomialOrder.degree
      rw [hBsupp]
    have hBlc : (colLex r n).leadingCoeff B = 1 := by
      unfold MonomialOrder.leadingCoeff
      rw [hBdeg, hBmap, coeff_map]
      have h1 : (colLex r n).degree (b mi) = m := hbd
      have h2 : (b mi).coeff ((colLex r n).degree (b mi)) = 1 := hblc
      rw [h1] at h2
      rw [h2, map_one]
    obtain ⟨z, hz⟩ := hint m hLT
    have hlcQ : (colLex r n).leadingCoeff Q = (z : ℚ) := hz
    set Q1 := Q - (colLex r n).leadingCoeff Q • B with hQ1
    have hQ1mem : Q1 ∈ dualWeyl ℚ r n ν :=
      Submodule.sub_mem _ hQ (Submodule.smul_mem _ _ (hBmem mi))
    have hQ1int : ∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z' : ℤ, coeff e Q1 = z' := by
      intro e he
      obtain ⟨w, hw⟩ := hint e he
      refine ⟨w - z * (b mi).coeff e, ?_⟩
      rw [hQ1, coeff_sub, coeff_smul, hw, hlcQ, hBmap, coeff_map]
      push_cast
      simp [smul_eq_mul]
    have hfinal : ∀ Q1' : MvPolynomial (Fin r × Fin n) ℤ, Q1 = intQ r n Q1' →
        ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' := by
      intro Q1' h
      refine ⟨Q1' + z • b mi, ?_⟩
      rw [map_add, map_zsmul, ← h, ← hB, hQ1, hlcQ, Int.cast_smul_eq_zsmul]
      abel
    by_cases hQ10 : Q1 = 0
    · exact hfinal 0 (by rw [hQ10, map_zero])
    · have hlt := lcassem_sub_lt (colLex r n) (hBdeg.trans hm) hBlc hQ10
      obtain ⟨Q1', h⟩ := ih _ (by rw [← hs]; exact hlt) Q1 rfl hQ1mem hQ1int
      exact hfinal Q1' h

end Formalism.InvariantFactorPaths.ColumnFamilies
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.TransposeVariables
section
open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def transposeVariables (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] MvPolynomial (Fin n × Fin n) R := rename Prod.swap

theorem transposeVariables_involutive (R : Type*) [CommRing R] (n : ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    transposeVariables R n (transposeVariables R n f) = f := by
  simp only [transposeVariables, AlgHom.coe_comp, Function.comp_apply, MvPolynomial.rename_rename]
  have h : (Prod.swap ∘ Prod.swap : Fin n × Fin n → Fin n × Fin n) = id := by
    funext x
    simp
  rw [h]
  exact MvPolynomial.rename_id_apply f

theorem qn_T_X (R : Type*) [CommRing R] (n : ℕ) (l a : Fin n) : transposeVariables R n (X (l, a)) = X (a, l) := by
  simp [transposeVariables]

theorem qn_T_map (n : ℕ) (f : MvPolynomial (Fin n × Fin n) ℤ) :
    transposeVariables ℚ n (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℚ) (transposeVariables ℤ n f) := by
  simp only [transposeVariables]
  exact (MvPolynomial.map_rename _ _ _).symm

def qn_D (n : ℕ) (a b : Fin n) :
    Derivation ℚ (MvPolynomial (Fin n × Fin n) ℚ) (MvPolynomial (Fin n × Fin n) ℚ) :=
  ∑ l : Fin n, (X (l, a) : MvPolynomial (Fin n × Fin n) ℚ) • pderiv (l, b)

theorem qn_D_apply (n : ℕ) (a b : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    qn_D n a b f = ∑ l : Fin n, X (l, a) * pderiv (l, b) f := by
  unfold qn_D
  have h := map_sum (Derivation.coeFnAddMonoidHom (R := ℚ) (A := MvPolynomial (Fin n × Fin n) ℚ)
    (M := MvPolynomial (Fin n × Fin n) ℚ)) (fun l : Fin n => (X (l, a) : MvPolynomial (Fin n × Fin n) ℚ) • pderiv (l, b))
    Finset.univ
  have h2 := congrFun h f
  simp only [Finset.sum_apply] at h2
  exact h2.trans (Finset.sum_congr rfl fun l _ => by simp [Derivation.coeFnAddMonoidHom, smul_eq_mul])

theorem qn_E_eq (n : ℕ) (a b : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    glOps ℚ n (rowLetters n) Set.univ a b f = qn_D n a b f := by
  rw [qn_D_apply]
  simp [glOps, glAct, rowLetters, LinearMap.sum_apply]

theorem qn_D_X (n : ℕ) (a b : Fin n) (l c : Fin n) :
    qn_D n a b (X (l, c)) = if c = b then X (l, a) else 0 := by
  rw [qn_D_apply]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply, Prod.mk.injEq]
  by_cases hc : c = b
  · subst hc
    simp
  · simp [hc]

theorem qn_deriv_rowGen (n : ℕ) (a b : Fin n) (hab : a ≠ b) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    Polynomial.derivative (rowGen ℚ a b (transposeVariables ℚ n f)) = rowGen ℚ a b (transposeVariables ℚ n (qn_D n a b f)) := by
  have hX : ∀ i : Fin n × Fin n, Polynomial.derivative (rowGen ℚ a b (transposeVariables ℚ n (X i))) =
      rowGen ℚ a b (transposeVariables ℚ n (qn_D n a b (X i))) := by
    rintro ⟨l, c⟩
    rw [qn_D_X, qn_T_X]
    by_cases hc : c = b
    · subst hc
      simp [rowGen, qn_T_X, hab]
    · simp [rowGen, hc]
  induction f using MvPolynomial.induction_on with
  | C r =>
    have hD : qn_D n a b (C r) = 0 := by
      rw [qn_D_apply]
      simp
    rw [hD]
    simp [transposeVariables, rowGen]
  | add p q hp hq =>
    simp only [map_add, Polynomial.derivative_add, hp, hq]
  | mul_X p i hp =>
    have hL : qn_D n a b (p * X i) = p * qn_D n a b (X i) + X i * qn_D n a b p := by
      rw [Derivation.leibniz]
      simp [smul_eq_mul]
    rw [hL]
    simp only [map_add, map_mul, Polynomial.derivative_mul, hp, hX i]
    ring

theorem qn_deriv_rowGen_diag (n : ℕ) (a : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    (1 + Polynomial.X) * Polynomial.derivative (rowGen ℚ a a (transposeVariables ℚ n f)) =
      rowGen ℚ a a (transposeVariables ℚ n (qn_D n a a f)) := by
  have hX : ∀ i : Fin n × Fin n, (1 + Polynomial.X) * Polynomial.derivative (rowGen ℚ a a (transposeVariables ℚ n (X i))) =
      rowGen ℚ a a (transposeVariables ℚ n (qn_D n a a (X i))) := by
    rintro ⟨l, c⟩
    rw [qn_D_X, qn_T_X]
    by_cases hc : c = a
    · subst hc
      simp [rowGen, qn_T_X]
      ring
    · simp [rowGen, hc]
  induction f using MvPolynomial.induction_on with
  | C r =>
    have hD : qn_D n a a (C r) = 0 := by
      rw [qn_D_apply]
      simp
    rw [hD]
    simp [transposeVariables, rowGen]
  | add p q hp hq =>
    simp only [map_add, Polynomial.derivative_add, mul_add, hp, hq]
  | mul_X p i hp =>
    have hL : qn_D n a a (p * X i) = p * qn_D n a a (X i) + X i * qn_D n a a p := by
      rw [Derivation.leibniz]
      simp [smul_eq_mul]
    rw [hL, map_mul, map_mul, Polynomial.derivative_mul, mul_add, ← mul_assoc,
      mul_left_comm (1 + Polynomial.X) (rowGen ℚ a a (transposeVariables ℚ n p)), hp, hX i]
    simp only [map_add, map_mul]
    ring

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

