import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0003

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcColESymmVal
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

def qc_sh {n : ℕ} (mu : Fin n → ℤ) (ε : ℤ) : Fin n → ℤ := fun a => mu a + ε

lemma qc_colH_sh {n : ℕ} (mu : Fin n → ℤ) (ε c : ℤ) : colH (qc_sh mu ε) (c + ε) = colH mu c := by
  unfold colH qc_sh
  congr 1
  ext m
  simp

lemma qc_mem_sh (mu : Fin n → ℤ) (ε c : ℤ) : c + ε ∈ TCols (qc_sh mu ε) ↔ c ∈ TCols mu := by
  simp [TCols, qc_sh]

def qc_colE (mu : Fin n → ℤ) (ε : ℤ) : ↥(TCols mu) ≃ ↥(TCols (qc_sh mu ε)) where
  toFun c := ⟨c.1 + ε, (qc_mem_sh mu ε c.1).2 c.2⟩
  invFun c := ⟨c.1 - ε, (qc_mem_sh mu ε _).1 (by rw [sub_add_cancel]; exact c.2)⟩
  left_inv c := Subtype.ext (by simp)
  right_inv c := Subtype.ext (by simp)

lemma qc_colE_val (mu : Fin n → ℤ) (ε : ℤ) (c : ↥(TCols mu)) : ((qc_colE mu ε c : ↥(TCols (qc_sh mu ε))) : ℤ) = c.1 + ε := rfl

def qc_idxE (mu : Fin n → ℤ) (ε : ℤ) : TIdx (qc_sh mu ε) ≃ TIdx mu where
  toFun I c := ⟨(I (qc_colE mu ε c)).1, (I (qc_colE mu ε c)).2.trans (qc_colH_sh mu ε c.1)⟩
  invFun I c := ⟨(I ((qc_colE mu ε).symm c)).1, (I ((qc_colE mu ε).symm c)).2.trans (by
    have := qc_colH_sh mu ε (c.1 - ε)
    rw [sub_add_cancel] at this
    exact this.symm)⟩
  left_inv I := by
    funext c
    apply Subtype.ext
    show (I (qc_colE mu ε ((qc_colE mu ε).symm c))).1 = (I c).1
    rw [Equiv.apply_symm_apply]
  right_inv I := by
    funext c
    apply Subtype.ext
    show (I ((qc_colE mu ε).symm (qc_colE mu ε c))).1 = (I c).1
    rw [Equiv.symm_apply_apply]

lemma qc_idxE_val (mu : Fin n → ℤ) (ε : ℤ) (I : TIdx (qc_sh mu ε)) (c : ↥(TCols mu)) :
    (qc_idxE mu ε I c).1 = (I (qc_colE mu ε c)).1 := rfl

lemma qc_init_congr {n h h' : ℕ} (e : h = h') (hn : h ≤ n) (hn' : h' ≤ n) :
    (univ : Finset (Fin h)).map (Fin.castLEEmb hn) = (univ : Finset (Fin h')).map (Fin.castLEEmb hn') := by
  subst e; rfl

lemma qc_idxE_can (mu : Fin n → ℤ) (ε : ℤ) : qc_idxE mu ε (canT (qc_sh mu ε)) = canT mu := by
  funext c
  apply Subtype.ext
  exact qc_init_congr (qc_colH_sh mu ε c.1) _ _

lemma qc_colE_succ (mu : Fin n → ℤ) (ε : ℤ) (c : ↥(TCols mu)) (hc : c.1 + 1 ∈ TCols mu)
    (hc' : (qc_colE mu ε c).1 + 1 ∈ TCols (qc_sh mu ε)) :
    qc_colE mu ε ⟨c.1 + 1, hc⟩ = ⟨(qc_colE mu ε c).1 + 1, hc'⟩ :=
  Subtype.ext (by show c.1 + 1 + ε = c.1 + ε + 1; ring)

lemma qc_idxE_std (mu : Fin n → ℤ) (ε : ℤ) (I : TIdx (qc_sh mu ε)) : StdT I ↔ StdT (qc_idxE mu ε I) := by
  constructor
  · intro h c hc t
    have hc' : (qc_colE mu ε c).1 + 1 ∈ TCols (qc_sh mu ε) := by
      have := (qc_mem_sh mu ε (c.1 + 1)).2 hc
      rw [qc_colE_val]
      convert this using 1
      ring
    have h1 := h (qc_colE mu ε c) hc' t
    rw [qc_idxE_val, qc_idxE_val, qc_colE_succ mu ε c hc hc']
    exact h1
  · intro h c' hc' t
    obtain ⟨c, rfl⟩ := (qc_colE mu ε).surjective c'
    have hc : c.1 + 1 ∈ TCols mu := by
      apply (qc_mem_sh mu ε (c.1 + 1)).1
      rw [qc_colE_val] at hc'
      convert hc' using 1
      ring
    have h1 := h c hc t
    rw [qc_idxE_val, qc_idxE_val, qc_colE_succ mu ε c hc hc'] at h1
    exact h1

lemma qc_dMu_sh (mu : Fin n → ℤ) (ε : ℤ) : dMu (qc_sh mu ε) = dMu mu :=
  Nat.card_congr ((qc_idxE mu ε).subtypeEquiv (qc_idxE_std mu ε))

lemma qc_minorC_congr {n h h' : ℕ} (e : h = h') (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h)
    (hJ' : J.card = h') (hI' : I.card = h') : minorC J I hJ hI = minorC J I hJ' hI' := by
  subst e; rfl

lemma qc_TMat_sh (mu : Fin n → ℤ) (ε : ℤ) (J I : TIdx (qc_sh mu ε)) :
    TMat (qc_sh mu ε) J I =
      ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * TMat mu (qc_idxE mu ε J) (qc_idxE mu ε I) := by
  unfold TMat
  rw [← Equiv.prod_comp (qc_colE mu ε)]
  have h1 : qc_sh mu ε (lastIdx n) = ε + mu (lastIdx n) := add_comm _ _
  rw [h1, zpow_add, Units.val_mul, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun c _ => ?_
  exact qc_minorC_congr (qc_colH_sh mu ε c.1) _ _ _ _ _ _

lemma qc_dom_sh {mu : Fin n → ℤ} (h : Dominant mu) (ε : ℤ) : Dominant (qc_sh mu ε) :=
  fun _ _ hab => add_le_add_left (h hab) ε

lemma qc_indep_tw {K : Type} [CommRing K] {M : GLMod n} (CF : ColFam M) {ι' : Type} (e : ι' ≃ M.ι) (ε : ℤ)
    (h : ∀ nu : Fin n → ℤ, LinearIndependent K
      (fun j : {j : CF.J // CF.mu j = nu} => fun i => ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : K)))
    (nu : Fin n → ℤ) : LinearIndependent K
      (fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => fun i' : ι' =>
        ((CF.ph j.1 (e i') (qc_idxE (CF.mu j.1) ε (canT (qc_sh (CF.mu j.1) ε))) : ℤ) : K)) := by
  have hj : ∀ j : {j : CF.J // qc_sh (CF.mu j) ε = nu}, CF.mu j.1 = qc_sh nu (-ε) := by
    intro j
    funext a
    have := congrFun j.2 a
    simp only [qc_sh] at this ⊢
    omega
  have h1 := ((h (qc_sh nu (-ε))).map' (LinearEquiv.funCongrLeft K K e).toLinearMap (LinearEquiv.ker _)).comp
    (fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => (⟨j.1, hj j⟩ : {j : CF.J // CF.mu j = qc_sh nu (-ε)}))
    (fun j j' hjj => Subtype.ext (congrArg (fun x => x.1) hjj))
  have h2 : (fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => fun i' : ι' =>
        ((CF.ph j.1 (e i') (qc_idxE (CF.mu j.1) ε (canT (qc_sh (CF.mu j.1) ε))) : ℤ) : K)) =
      ((⇑(LinearEquiv.funCongrLeft K K e).toLinearMap ∘
        fun (j : {j : CF.J // CF.mu j = qc_sh nu (-ε)}) i => ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : K)) ∘
        fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => (⟨j.1, hj j⟩ : {j : CF.J // CF.mu j = qc_sh nu (-ε)})) := by
    funext j i'
    simp only [qc_idxE_can]
    rfl
  rw [h2]
  exact h1

theorem qc_colFam_tw (M M' : GLMod n) (ε : ℤ) (e : M'.ι ≃ M.ι)
    (hA : ∀ i j, M'.A i j = ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * M.A (e i) (e j))
    (CF : ColFam M) : Nonempty (ColFam M') := by
  refine ⟨{ J := CF.J, mu := fun j => qc_sh (CF.mu j) ε, dom := fun j => qc_dom_sh (CF.dom j) ε,
            ph := fun j => fun i' I' => CF.ph j (e i') (qc_idxE (CF.mu j) ε I'),
            equiv := ?_, indepP := ?_, indepQ := ?_, rank := ?_ }⟩
  · intro j
    ext i' I'
    have h : ∑ k, M.A (e i') k * (Int.castRingHom (GLCoord ℤ n)) (CF.ph j k (qc_idxE (CF.mu j) ε I')) =
        ∑ K, (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e i') K) * TMat (CF.mu j) K (qc_idxE (CF.mu j) ε I') :=
      congrFun (congrFun (CF.equiv j) (e i')) (qc_idxE (CF.mu j) ε I')
    show ∑ k', M'.A i' k' * (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e k') (qc_idxE (CF.mu j) ε I')) =
      ∑ K', (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e i') (qc_idxE (CF.mu j) ε K')) *
        TMat (qc_sh (CF.mu j) ε) K' I'
    simp only [hA, qc_TMat_sh]
    rw [Equiv.sum_comp e (fun k => ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * M.A (e i') k *
        (Int.castRingHom (GLCoord ℤ n)) (CF.ph j k (qc_idxE (CF.mu j) ε I'))),
      Equiv.sum_comp (qc_idxE (CF.mu j) ε) (fun K => (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e i') K) *
        (((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * TMat (CF.mu j) K (qc_idxE (CF.mu j) ε I')))]
    simp only [mul_assoc, mul_left_comm _ ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n), ← Finset.mul_sum]
    rw [h]
  · intro p hp nu
    exact qc_indep_tw CF e ε (CF.indepP p hp) nu
  · intro nu
    exact qc_indep_tw CF e ε CF.indepQ nu
  · rw [Fintype.card_congr e, CF.rank]
    exact Finset.sum_congr rfl fun j _ => (qc_dMu_sh (CF.mu j) ε).symm

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsSymDMatEq
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def qs_cnt {ι : Type*} [Fintype ι] (a : ι → Fin n) (x : Fin n) : ℕ := (univ.filter fun c => a c = x).card

def qs_SM {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A) (b : ℕ) : Matrix (SymIdx n b) (SymIdx n b) A :=
  fun α β => MvPolynomial.coeff (symMono α) (∏ m : Fin n, (∑ a : Fin n, MvPolynomial.C (G a m) * X a) ^ (β.1 m : ℕ))

lemma qs_sum_cnt {ι : Type*} [Fintype ι] (a : ι → Fin n) : ∑ x, qs_cnt a x = Fintype.card ι := by
  classical
  simp only [qs_cnt]
  rw [← Finset.card_eq_sum_card_fiberwise (f := a) (s := univ) (t := univ) (fun _ _ => by simp)]
  simp

lemma qs_sym_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A)
    (m : ι → Fin n) (β : Fin n → ℕ) (hβ : ∀ x, qs_cnt m x = β x) (α : Fin n →₀ ℕ) :
    MvPolynomial.coeff α (∏ x : Fin n, (∑ a : Fin n, MvPolynomial.C (G a x) * X a) ^ (β x)) =
      ∑ a : ι → Fin n, if (∀ x, qs_cnt a x = α x) then ∏ c, G (a c) (m c) else 0 := by
  classical
  have h1 : (∏ x : Fin n, (∑ a : Fin n, (MvPolynomial.C (G a x) * X a : MvPolynomial (Fin n) A)) ^ (β x)) =
      ∏ c : ι, ∑ a : Fin n, MvPolynomial.C (G a (m c)) * X a := by
    rw [← Finset.prod_fiberwise (s := univ) (g := m)]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => ∑ a : Fin n, (MvPolynomial.C (G a x) * X a : MvPolynomial (Fin n) A))
      (fun c hc => by rw [(Finset.mem_filter.1 hc).2]), Finset.prod_const, ← hβ x]
    rfl
  rw [h1, Fintype.prod_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : (∏ c : ι, (MvPolynomial.C (G (a c) (m c)) * X (a c) : MvPolynomial (Fin n) A)) =
      MvPolynomial.monomial (∑ c : ι, Finsupp.single (a c) 1) (∏ c, G (a c) (m c)) := by
    rw [MvPolynomial.monomial_sum_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [MvPolynomial.C_mul_X_eq_monomial]
  rw [h2, MvPolynomial.coeff_monomial]
  have h3 : (∑ c : ι, Finsupp.single (a c) 1 = α) ↔ ∀ x, qs_cnt a x = α x := by
    rw [Finsupp.ext_iff]
    refine forall_congr' fun x => ?_
    rw [Finsupp.finsetSum_apply, qs_cnt, Finset.card_filter]
    simp only [Finsupp.single_apply]
  simp only [h3]

def qs_mon {ι : Type*} [Fintype ι] {b : ℕ} (hb : Fintype.card ι = b) (m : ι → Fin n) : SymIdx n b :=
  ⟨fun x => ⟨qs_cnt m x, by
    have := qs_sum_cnt m
    have h2 : qs_cnt m x ≤ ∑ x, qs_cnt m x := Finset.single_le_sum (f := qs_cnt m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    omega⟩, by simpa using (qs_sum_cnt m).trans hb⟩

theorem qs_sum_sym {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A) {b : ℕ}
    (hb : Fintype.card ι = b) (m : ι → Fin n) (α : SymIdx n b) (r : A) :
    ∑ β : SymIdx n b, qs_SM G b α β * (if (∀ x, qs_cnt m x = (β.1 x : ℕ)) then r else 0) =
      (∑ a : ι → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then ∏ c, G (a c) (m c) else 0) * r := by
  classical
  rw [Finset.sum_eq_single (qs_mon hb m)]
  · have h0 : ∀ x, qs_cnt m x = ((qs_mon hb m).1 x : ℕ) := fun x => rfl
    rw [if_pos h0]
    congr 1
    exact qs_sym_mul G m _ h0 (symMono α)
  · intro β _ hβ
    rw [if_neg, mul_zero]
    intro h
    exact hβ (Subtype.ext (funext fun x => Fin.ext (h x).symm))
  · intro h; exact absurd (Finset.mem_univ _) h

def qs_gC (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord ℤ n) :=
  Matrix.of fun a b => algebraMap _ (GLCoord ℤ n) (genMat ℤ n a b)

def qs_gI (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord ℤ n) := Matrix.of fun a b => ginvC n a b

lemma qs_SymMat_eq (n b : ℕ) : SymMat n b = qs_SM (qs_gC n) b := rfl

lemma qs_SymDMat_eq (n b : ℕ) : SymDMat n b = qs_SM (qs_gI n).transpose b := rfl

lemma qs_gC_mul_gI (n : ℕ) : qs_gC n * qs_gI n = 1 := by
  have h1 : qs_gC n = (genMat ℤ n).map (algebraMap _ (GLCoord ℤ n)) := rfl
  have h2 : qs_gI n = (((detU n)⁻¹ : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) •
      ((genMat ℤ n).adjugate).map (algebraMap _ (GLCoord ℤ n)) := by
    ext a b; simp [qs_gI, ginvC]
  rw [h1, h2, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  ext a b
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact (detU n).inv_mul
  · simp [Matrix.one_apply_ne hab]

lemma qs_SM_diag {A : Type*} [CommRing A] (d : Fin n → A) (b : ℕ) (α β : SymIdx n b) :
    qs_SM (Matrix.diagonal d) b α β = if α = β then ∏ x, d x ^ (β.1 x : ℕ) else 0 := by
  classical
  have h1 : ∀ x : Fin n, (∑ a : Fin n, (MvPolynomial.C (Matrix.diagonal d a x) * X a : MvPolynomial (Fin n) A)) =
      MvPolynomial.monomial (Finsupp.single x 1) (d x) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [Matrix.diagonal_apply_eq, MvPolynomial.C_mul_X_eq_monomial]
    · intro a _ ha; rw [Matrix.diagonal_apply_ne _ ha]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [qs_SM]
  simp_rw [h1, MvPolynomial.monomial_pow]
  rw [← MvPolynomial.monomial_sum_prod, MvPolynomial.coeff_monomial]
  have h3 : (∑ x : Fin n, (β.1 x : ℕ) • Finsupp.single x 1 = symMono α) ↔ α = β := by
    rw [Finsupp.ext_iff]
    constructor
    · intro h
      refine Subtype.ext (funext fun x => Fin.ext ?_)
      have := h x
      rw [Finsupp.finsetSum_apply] at this
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    · rintro rfl x
      rw [Finsupp.finsetSum_apply]
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
  simp only [h3]

lemma qs_SM_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (G : Matrix (Fin n) (Fin n) A) (b : ℕ)
    (α β : SymIdx n b) : f (qs_SM G b α β) = qs_SM (G.map f) b α β := by
  rw [qs_SM, qs_SM, ← MvPolynomial.coeff_map]
  simp [map_prod, map_pow, map_sum]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

