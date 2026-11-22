import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0013
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0008
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0001
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.Bundle0001
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0002

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.EvalIdBracketCanonical
section
open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qn_delta (n : ℕ) : MvPolynomial (Fin n × Fin n) ℤ := lpMinor ℤ n (le_refl n) (le_refl n)

theorem qn_T_det (n : ℕ) : transposeVariables ℤ n (genMat ℤ n).det = qn_delta n := by
  unfold qn_delta lpMinor transposeVariables
  rw [AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext p q
  simp [genMat]

theorem qn_full (n : ℕ) (J : Fin n → Fin n) :
    ∃ ε : ℤ, initMinor ℤ J (le_refl n) = ε • qn_delta n := by
  classical
  set M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) :=
    Matrix.of fun p q : Fin n => X (Fin.castLE (le_refl n) p, Fin.castLE (le_refl n) q) with hM
  have h1 : initMinor ℤ J (le_refl n) = (M.submatrix J id).det := rfl
  by_cases hJ : Function.Injective J
  · have hb : Function.Bijective J := Finite.injective_iff_bijective.mp hJ
    refine ⟨((Equiv.Perm.sign (Equiv.ofBijective J hb) : ℤˣ) : ℤ), ?_⟩
    have h2 := Matrix.det_permute (Equiv.ofBijective J hb) M
    rw [h1]
    have h3 : M.submatrix J id = M.submatrix (Equiv.ofBijective J hb) id := rfl
    rw [h3, h2, zsmul_eq_mul]
    simp [qn_delta, lpMinor, hM]
  · refine ⟨0, ?_⟩
    rw [zero_smul, h1]
    unfold Function.Injective at hJ
    push Not at hJ
    obtain ⟨p, p', hpp, hne⟩ := hJ
    exact Matrix.det_zero_of_row_eq hne (by funext q; simp [Matrix.submatrix, hpp])

theorem qn_full' (n s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n) (h : s = n) :
    ∃ ε : ℤ, initMinor ℤ J hs = ε • qn_delta n := by
  subst h
  exact qn_full s J

theorem qn_divide (n : ℕ) [NeZero n] (ν' : Fin n → ℕ) :
    dualWeyl ℤ n n (fun t => ν' t + 1) ≤
      (dualWeyl ℤ n n ν').map (LinearMap.mulLeft ℤ (qn_delta n)) := by
  classical
  rw [standardMonomialSpanDomain ℤ n n _, Submodule.span_le]
  rintro f ⟨K, sz, hsz, I, hshape, rfl⟩
  have h1 : 0 < shapeDeg sz (lastIdx n) := by rw [hshape]; exact Nat.succ_pos _
  unfold shapeDeg at h1
  obtain ⟨k0, hk0⟩ := Finset.card_pos.mp h1
  have hk0' : (lastIdx n).val < sz k0 := (Finset.mem_filter.mp hk0).2
  have hsz0 : sz k0 = n := by
    have := hsz k0
    have h2 : (lastIdx n).val = n - 1 := rfl
    omega
  obtain ⟨ε, hε⟩ := qn_full' n (sz k0) (hsz k0) (I k0) hsz0
  have hrest : (∏ k ∈ Finset.univ.erase k0, initMinor ℤ (I k) (hsz k)) ∈ dualWeyl ℤ n n ν' := by
    refine dualWeyl_of_eq (dualWeyl_prod (Finset.univ.erase k0) (fun k => initW n (sz k))
      (fun k => initMinor ℤ (I k) (hsz k)) (fun k _ => initMinor_mem (I k) (hsz k))) ?_
    have h3 := sum_initW_eq_shapeDeg (n := n) sz
    rw [hshape, ← Finset.add_sum_erase _ _ (Finset.mem_univ k0)] at h3
    funext t
    have h4 := congrFun h3 t
    have h5 : initW n (sz k0) t = 1 := by
      unfold initW
      rw [hsz0, if_pos t.isLt]
    rw [Pi.add_apply, h5] at h4
    omega
  refine ⟨ε • ∏ k ∈ Finset.univ.erase k0, initMinor ℤ (I k) (hsz k), Submodule.smul_mem _ _ hrest, ?_⟩
  rw [LinearMap.mulLeft_apply]
  unfold bideterminant
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k0), hε, mul_smul_comm, smul_mul_assoc]

theorem qn_divideN (n : ℕ) [NeZero n] (ν0 : Fin n → ℕ) {ι : Type} (Q : ι → MvPolynomial (Fin n × Fin n) ℤ)
    (h : dualWeyl ℤ n n ν0 ≤ Submodule.span ℤ (Set.range Q)) (N : ℕ) :
    dualWeyl ℤ n n (fun t => ν0 t + N) ≤ Submodule.span ℤ (Set.range fun i => qn_delta n ^ N * Q i) := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    intro f hf
    obtain ⟨g, hg, rfl⟩ := qn_divide n (fun t => ν0 t + N) hf
    have hx := Submodule.mem_map_of_mem (f := LinearMap.mulLeft ℤ (qn_delta n)) (ih hg)
    rw [Submodule.map_span] at hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by simp only [LinearMap.mulLeft_apply]; ring⟩

def qn_nu {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Fin n → ℕ :=
  fun t => (mu t + ((-(mu (lastIdx n))).toNat : ℤ)).toNat

theorem qn_le_last {n : ℕ} [NeZero n] (a : Fin n) : a ≤ lastIdx n := by
  have h2 : (lastIdx n).val = n - 1 := rfl
  have := a.isLt
  exact Fin.le_def.mpr (by omega)

theorem qn_nu_eq {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    qn_nu mu = fun t => qa_nu mu t + (mu (lastIdx n)).toNat := by
  funext t
  have h := hmu (qn_le_last t)
  unfold qn_nu qa_nu
  omega

theorem qn_nu_cast {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    (fun a => ((qn_nu mu a : ℕ) : ℤ)) = fun a => mu a + ((-(mu (lastIdx n))).toNat : ℤ) := by
  funext t
  have h := hmu (qn_le_last t)
  unfold qn_nu
  omega

theorem qn_nu_anti {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) : Antitone (qn_nu mu) := by
  intro a b hab
  have h := hmu hab
  unfold qn_nu
  omega

theorem qn_T_brkPol {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    transposeVariables ℤ n (brkPol mu I) = qn_delta n ^ (mu (lastIdx n)).toNat * qa_P ℤ I := by
  rw [qa_brkPol_eq, map_mul, map_pow, qn_T_det]
  congr 1
  exact transposeVariables_involutive ℤ n (qa_P ℤ I)

theorem bracket_mem_dualWeyl {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    transposeVariables ℤ n (brkPol mu I) ∈ dualWeyl ℤ n n (qn_nu mu) := by
  rw [qn_T_brkPol]
  have h1 : qn_delta n ∈ dualWeyl ℤ n n (initW n n) :=
    initMinor_mem (R := ℤ) (fun p : Fin n => Fin.castLE (le_refl n) p) (le_refl n)
  refine dualWeyl_of_eq (dualWeyl_mul (dualWeyl_pow h1 (mu (lastIdx n)).toNat) (tableauBideterminant_mem_dualWeyl ℤ hmu I)) ?_
  rw [qn_nu_eq hmu]
  funext t
  simp [initW]
  ring

theorem dualWeyl_le_span_bracket {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    dualWeyl ℤ n n (qn_nu mu) ≤ Submodule.span ℤ (Set.range fun I : TIdx mu => transposeVariables ℤ n (brkPol mu I)) := by
  rw [qn_nu_eq hmu]
  simp only [qn_T_brkPol]
  exact qn_divideN n (qa_nu mu) (fun I : TIdx mu => qa_P ℤ I) (le_of_eq (dualWeyl_eq_span_tableauBideterminant ℤ hmu)) _

theorem eval_id_bracket_canonical {n : ℕ} [NeZero n] (mu : Fin n → ℤ) :
    eval (idFrame ℤ n n) (transposeVariables ℤ n (brkPol mu (canT mu))) = 1 := by
  rw [qn_T_brkPol, map_mul, map_pow]
  have h1 : eval (idFrame ℤ n n) (qn_delta n) = 1 := eval_idPoint_lpMinor ℤ n (le_refl n) (le_refl n)
  rw [h1, one_pow, one_mul]
  unfold qa_P
  rw [map_prod]
  refine Finset.prod_eq_one fun c _ => ?_
  have h2 : initMinor ℤ (qa_row (canT mu) c) (colH_le mu c) =
      lpMinor ℤ (colH mu c) (colH_le mu c) (colH_le mu c) := by
    unfold initMinor lpMinor
    congr 1
    ext p q
    simp [qa_row, qa_can_emb]
  rw [h2]
  exact eval_idPoint_lpMinor ℤ (colH mu c) (colH_le mu c) (colH_le mu c)

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.HighestVectorsEqLattice
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qd_high_zero (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) : IsHighest M R mu 0 :=
  ⟨Matrix.mulVec_zero _, fun R' _ _ u _ _ => by
    have e : (fun i => algebraMap R R' ((0 : M.ι → R) i)) = 0 := by funext i; simp
    rw [e, Matrix.mulVec_zero]⟩

lemma qd_high_add (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) {x y : M.ι → R}
    (hx : IsHighest M R mu x) (hy : IsHighest M R mu y) : IsHighest M R mu (x + y) :=
  ⟨by rw [Matrix.mulVec_add, hx.1, hy.1], fun R' _ _ u h1 h2 => by
    have e : (fun i => algebraMap R R' ((x + y) i)) =
        (fun i => algebraMap R R' (x i)) + fun i => algebraMap R R' (y i) := by funext i; simp
    rw [e, Matrix.mulVec_add, hx.2 R' u h1 h2, hy.2 R' u h1 h2]⟩

lemma qd_high_smul (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) (c : R) {x : M.ι → R}
    (hx : IsHighest M R mu x) : IsHighest M R mu (c • x) :=
  ⟨by rw [Matrix.mulVec_smul, hx.1], fun R' _ _ u h1 h2 => by
    have e : (fun i => algebraMap R R' ((c • x) i)) = algebraMap R R' c • fun i => algebraMap R R' (x i) := by
      funext i; simp
    rw [e, Matrix.mulVec_smul, hx.2 R' u h1 h2]⟩

lemma qd_det_unitri {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) : Matrix.GeneralLinearGroup.det u = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular (fun a b hab => h2 a b hab)]
  simp [h1]

variable [NeZero n]

lemma qd_minor_unitri {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) (mu : Fin n → ℤ) (c : ↥(TCols mu))
    (J : {J : Finset (Fin n) // J.card = colH mu c}) :
    evGL u (minorC J.1 (canT mu c).1 J.2 (canT mu c).2) = if J = canT mu c then 1 else 0 := by
  rw [qb_evGL_minorC]
  split_ifs with hJ
  · subst hJ
    rw [Matrix.det_of_isUpperTriangular]
    · simp [h1]
    · intro a b hab
      exact h2 _ _ ((OrderEmbedding.lt_iff_lt _).2 hab)
  · obtain ⟨j, hjJ, hj⟩ : ∃ j ∈ J.1, colH mu c ≤ j.val := by
      by_contra hcon
      push Not at hcon
      apply hJ
      apply Subtype.ext
      apply Finset.eq_of_subset_of_card_le
      · intro j hj
        exact (qb_mem_canT mu c j).2 (hcon j hj)
      · rw [J.2, (canT mu c).2]
    have hr : j ∈ Set.range (J.1.orderEmbOfFin J.2) := by
      rw [Finset.range_orderEmbOfFin]; exact hjJ
    obtain ⟨a, ha⟩ := hr
    apply Matrix.det_eq_zero_of_row_eq_zero a
    intro b
    rw [Matrix.of_apply, ha, qd_can_emb]
    apply h2
    exact Fin.lt_def.2 (lt_of_lt_of_le (show (Fin.castLE (colH_le mu c) b).val < colH mu c from b.2) hj)

lemma unipotent_eval_canonical {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) (mu : Fin n → ℤ) (K : TIdx mu) :
    evGL u (TMat mu K (canT mu)) = if K = canT mu then 1 else 0 := by
  unfold TMat
  rw [map_mul, map_prod, qd_evGL_detU, qd_det_unitri u h1 h2, one_zpow, Units.val_one, one_mul]
  simp only [qd_minor_unitri u h1 h2]
  split_ifs with hK
  · subst hK
    simp
  · obtain ⟨c, hc⟩ : ∃ c, K c ≠ canT mu c := by
      by_contra hcon
      push Not at hcon
      exact hK (funext hcon)
    exact Finset.prod_eq_zero (Finset.mem_univ c) (if_neg hc)

lemma qd_vec_can_high {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] (j : CF.J) :
    IsHighest M R (CF.mu j) (fun i => (CF.vec j (canT (CF.mu j)) i : R)) := by
  constructor
  · funext i
    have := congrArg (Int.cast : ℤ → R) (qb_prMu_ph CF j (CF.mu j) i (canT (CF.mu j)))
    rw [if_pos (qb_wtT_can (CF.dom j))] at this
    push_cast at this
    simpa [Matrix.mulVec, dotProduct, ColFam.vec] using this
  · intro R' _ _ u h1 h2
    funext i
    have h := congrArg (evGL u) (qb_equiv_apply CF j i (canT (CF.mu j)))
    simp only [map_sum, map_mul, map_intCast, unipotent_eval_canonical u h1 h2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    simpa [Matrix.mulVec, dotProduct, ColFam.vec] using h

lemma qd_high_cast (M : GLMod n) (mu : Fin n → ℤ) (x : M.ι → ℤ) (hx : IsHighest M ℤ mu x) :
    IsHighest M ℚ mu (fun i => (x i : ℚ)) := by
  constructor
  · funext i
    have := congrArg (Int.cast : ℤ → ℚ) (congrFun hx.1 i)
    simpa [Matrix.mulVec, dotProduct] using this
  · intro R' _ _ u h1 h2
    have := hx.2 R' u h1 h2
    simpa using this

theorem highest_vectors_eq_lattice_of : LemmaA → HighestVectorsEqLattice := by
  intro hA n _ M CF mu hmu
  classical
  ext x
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => IsHighest M ℤ mu x) ?_ (qd_high_zero M ℤ mu)
      (fun x y _ _ hx hy => qd_high_add M ℤ mu hx hy) (fun c x _ hx => qd_high_smul M ℤ mu c hx) hx
    rintro _ ⟨j, rfl, rfl⟩
    have := qd_vec_can_high CF ℤ j
    simpa using this
  · intro hx
    have hQ := highest_vectors_rational_span_of hA n M CF mu hmu _ (qd_high_cast M mu x hx)
    obtain ⟨b, hb⟩ : ∃ b : qb_Idx CF → ℤ, ∑ y, b y • qb_vecF CF ℤ y = x := by
      have : x ∈ Submodule.span ℤ (Set.range (qb_vecF CF ℤ)) := by rw [(qb_basisR hA CF ℤ).2]; trivial
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
    let S : Set (qb_Idx CF) := {y | CF.mu y.1 = mu ∧ y.2.1 = canT (CF.mu y.1)}
    have hcast : (fun i => (x i : ℚ)) = ∑ y, (b y : ℚ) • qb_basis hA CF ℚ y := by
      funext i
      rw [← hb]
      simp [qb_basis_apply, qb_vecF, Finset.sum_apply]
    have hS : (fun i => (x i : ℚ)) ∈ Submodule.span ℚ (qb_basis hA CF ℚ '' S) := by
      refine Submodule.span_mono ?_ hQ
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨⟨j, ⟨canT (CF.mu j), qd_canT_std _⟩⟩, ⟨hj, rfl⟩, by rw [qb_basis_apply]; rfl⟩
    rw [Module.Basis.mem_span_image, hcast] at hS
    have hsupp : ∀ y, b y ≠ 0 → y ∈ S := by
      intro y hy
      apply hS
      rw [Finset.mem_coe, Finsupp.mem_support_iff, Module.Basis.repr_sum_self]
      exact_mod_cast hy
    rw [← hb]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : b y = 0
    · rw [hy, zero_smul]; exact zero_mem _
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      obtain ⟨e1, e2⟩ := hsupp y hy
      refine ⟨y.1, e1, ?_⟩
      funext i
      simp only [qb_vecF, Int.cast_id]
      rw [e2]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.LemmaA
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem claimA_straightening : LemmaA := by
  intro n _ mu _ F _
  have hu : IsUnit (mapCoord (n := n) F ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) :=
    (Units.isUnit _).map _
  have h := (linearIndependent_standard_tableauBideterminant F mu).map' (qa_Phi F n _) (LinearMap.ker_eq_bot.mpr (qa_Phi_inj F n _ hu))
  have he : (fun I : {I : TIdx mu // StdT I} => mapCoord (n := n) F (brk mu I.1)) =
      (qa_Phi F n (mapCoord (n := n) F ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n))) ∘
        fun I : {I : TIdx mu // StdT I} => qa_P F I.1 := by
    funext I
    exact qa_mapCoord_brk mu F I.1
  rw [he]
  exact h

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnFactRowDivDiag
section
open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

theorem qn_rowDiv_zero (n : ℕ) (a b : Fin n) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    rowDiv ℚ a b 0 F = F := by
  unfold rowDiv
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have h : (Polynomial.evalRingHom (0 : MvPolynomial (Fin n × Fin n) ℚ)).comp
      (rowGen ℚ (r := n) (n := n) a b).toRingHom =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rowGen, aeval_X,
        Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C, RingHom.id_apply]
      split_ifs <;> simp
  have h2 := RingHom.congr_fun h F
  simpa using h2

theorem qn_natsmul (n : ℕ) (k : ℕ) (p : MvPolynomial (Fin n × Fin n) ℚ) :
    p * ((k : MvPolynomial (Fin n × Fin n) ℚ) + 1) = ((k + 1 : ℕ) : ℚ) • p := by
  rw [MvPolynomial.smul_eq_C_mul, mul_comm]
  congr 1
  simp

theorem qn_rowDiv_succ (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    ((k + 1 : ℕ) : ℚ) • rowDiv ℚ a b (k + 1) (transposeVariables ℚ n f) = rowDiv ℚ a b k (transposeVariables ℚ n (qn_D n a b f)) := by
  unfold rowDiv
  rw [← qn_deriv_rowGen n a b hab f, Polynomial.coeff_derivative, qn_natsmul]

theorem qn_rowDiv_succ_diag (n : ℕ) (a : Fin n) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    ((k + 1 : ℕ) : ℚ) • rowDiv ℚ a a (k + 1) (transposeVariables ℚ n f) =
      rowDiv ℚ a a k (transposeVariables ℚ n (qn_D n a a f - (k : ℚ) • f)) := by
  unfold rowDiv
  rw [map_sub, map_smul, map_sub, map_smul, ← qn_deriv_rowGen_diag n a f, Polynomial.coeff_sub,
    Polynomial.coeff_smul, add_mul, one_mul, Polynomial.coeff_add]
  cases k with
  | zero =>
    rw [Polynomial.coeff_X_mul_zero, Polynomial.coeff_derivative]
    simp
  | succ m =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    simp only [MvPolynomial.smul_eq_C_mul, map_natCast, Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

theorem qn_fact_rowDiv (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    ∀ f : MvPolynomial (Fin n × Fin n) ℚ,
    (k.factorial : ℚ) • rowDiv ℚ a b k (transposeVariables ℚ n f) =
      transposeVariables ℚ n (((glOps ℚ n (rowLetters n) Set.univ a b) ^ k) f) := by
  induction k with
  | zero =>
    intro f
    simp [qn_rowDiv_zero]
  | succ k ih =>
    intro f
    rw [Nat.factorial_succ, Nat.cast_mul, mul_comm ((k + 1 : ℕ) : ℚ), mul_smul, qn_rowDiv_succ n a b hab k f,
      ih, pow_succ, Module.End.mul_apply, qn_E_eq]

theorem qn_T_divPowE (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    transposeVariables ℚ n (divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k f) = rowDiv ℚ a b k (transposeVariables ℚ n f) := by
  have hk : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  rw [divPowE, LinearMap.smul_apply, map_smul, ← qn_fact_rowDiv n a b hab k f, smul_smul,
    inv_mul_cancel₀ hk, one_smul]

theorem qn_fact_rowDiv_diag (n : ℕ) (a : Fin n) (k : ℕ) :
    ∀ f : MvPolynomial (Fin n × Fin n) ℚ,
    (k.factorial : ℚ) • rowDiv ℚ a a k (transposeVariables ℚ n f) =
      transposeVariables ℚ n ((((List.range k).map fun j : ℕ => glOps ℚ n (rowLetters n) Set.univ a a -
        (j : ℚ) • (1 : Module.End ℚ (MvPolynomial (Fin n × Fin n) ℚ))).prod) f) := by
  induction k with
  | zero =>
    intro f
    simp [qn_rowDiv_zero]
  | succ k ih =>
    intro f
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, qn_E_eq, ← ih,
      Nat.factorial_succ, Nat.cast_mul, mul_comm ((k + 1 : ℕ) : ℚ), mul_smul, qn_rowDiv_succ_diag]

theorem qn_T_binomE (n : ℕ) (a : Fin n) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    transposeVariables ℚ n (binomE (glOps ℚ n (rowLetters n) Set.univ) a k f) = rowDiv ℚ a a k (transposeVariables ℚ n f) := by
  have hk : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  rw [binomE, LinearMap.smul_apply, map_smul, ← qn_fact_rowDiv_diag n a k f, smul_smul,
    inv_mul_cancel₀ hk, one_smul]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.SBasis
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

lemma qa_brk_Phi {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brk mu I = qa_PhiZ n ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) (qa_P ℤ I) := by
  rw [qa_brk_eq, qa_PhiZ_apply]

theorem qa_SMu_eq {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    SMu mu = (dualWeyl ℤ n n (qa_nu mu)).map
      (qa_PhiZ n ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) := by
  rw [dualWeyl_eq_span_tableauBideterminant ℤ hmu, Submodule.map_span, ← Set.range_comp]
  unfold SMu
  congr 2
  funext I
  exact qa_brk_Phi mu I

theorem standard_basis_theorem : SBasis := by
  intro n _ mu hmu
  have he : (fun I : {I : TIdx mu // StdT I} => brk mu I.1) =
      (qa_PhiZ n ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) ∘
        fun I : {I : TIdx mu // StdT I} => qa_P ℤ I.1 := by
    funext I
    exact qa_brk_Phi mu I.1
  constructor
  · rw [he]
    exact (linearIndependent_standard_tableauBideterminant ℤ mu).map' (qa_PhiZ n _)
      (LinearMap.ker_eq_bot.mpr (qa_PhiZ_inj n _ (Units.isUnit _)))
  · rw [qa_SMu_eq hmu, dualWeyl_eq_span_standard_tableauBideterminant ℤ hmu, Submodule.map_span, ← Set.range_comp, he]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

