import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QaNuAntitone
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.EqSmulCanonicalOfUnipotentInvariant
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0001

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QaExpEqBidetExp
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qa_P (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    MvPolynomial (Fin n × Fin n) R :=
  ∏ c : ↥(TCols mu), initMinor R (qa_row I c) (colH_le mu c)

def qa_e {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Fin (Fintype.card ↥(TCols mu)) ≃ ↥(TCols mu) :=
  (Fintype.equivFin ↥(TCols mu)).symm

lemma tableauBideterminant_eq_bideterminant (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_P R I = bideterminant R (fun k => colH mu (qa_e mu k)) (fun k => colH_le mu (qa_e mu k))
      (fun k => qa_row I (qa_e mu k)) := by
  unfold qa_P bideterminant
  exact (Fintype.prod_equiv (qa_e mu) _ _ (fun _ => rfl)).symm

lemma qa_exp_eq_bidetExp {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_exp I = bidetExp (fun k => colH mu (qa_e mu k)) (fun k => colH_le mu (qa_e mu k))
      (fun k => qa_row I (qa_e mu k)) := by
  unfold qa_exp bidetExp
  exact (Fintype.sum_equiv (qa_e mu) _ _ (fun _ => rfl)).symm

private theorem lt_colH_iff_le {n : ℕ} {mu : Fin n → ℤ} (hmu : Antitone mu) (c : ℤ) (t : Fin n) :
    (t : ℕ) < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (Finset.univ.filter fun m : Fin n => c ≤ mu m) ⊆ Finset.Iio t := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [Finset.mem_Iio]
      by_contra hmt
      push_neg at hmt
      have := hmu hmt
      omega
    exact absurd (lt_of_lt_of_le h ((Finset.card_le_card hsub).trans (Fin.card_Iio t).le)) (lt_irrefl _)
  · intro h
    have hsub : Finset.Iic t ⊆ (Finset.univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.trans (hmu hm)
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ((Fin.card_Iic t).symm.le.trans (Finset.card_le_card hsub))

lemma qa_shape {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    shapeDeg (n := n) (fun k => colH mu (qa_e mu k)) = qa_nu mu := by
  have hmu' : Antitone mu := hmu
  funext t
  unfold shapeDeg qa_nu
  have h1 : (Finset.univ.filter fun k => (t : ℕ) < colH mu ↑(qa_e mu k)).card =
      (Finset.univ.filter fun c : ↥(TCols mu) => (t : ℕ) < colH mu ↑c).card :=
    Finset.card_equiv (qa_e mu) (by simp)
  have h2 : (Finset.univ.filter fun c : ↥(TCols mu) => (t : ℕ) < colH mu ↑c).card =
      ((TCols mu).filter fun c => (t : ℕ) < colH mu c).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Finset.sum_coe_sort (TCols mu) (fun c => if (t : ℕ) < colH mu c then 1 else 0)
  have h3 : ((TCols mu).filter fun c => (t : ℕ) < colH mu c) = Finset.Ioc (mu (lastIdx n)) (mu t) := by
    ext c
    have h0 : mu t ≤ mu 0 := hmu' (by simp [Fin.le_iff_val_le_val])
    simp only [TCols, Finset.mem_filter, Finset.mem_Ioc, lt_colH_iff_le hmu']
    constructor <;> intro h <;> omega
  exact h1.trans (h2.trans (by rw [h3, Int.card_Ioc]))

lemma tableauBideterminant_degree_leadingCoeff (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    (colLex n n).degree (qa_P R I) = qa_exp I ∧ (colLex n n).leadingCoeff (qa_P R I) = 1 := by
  rw [tableauBideterminant_eq_bideterminant, qa_exp_eq_bidetExp]
  exact column_lex_bideterminant R n n _ _ _ _ fun k => qa_row_strictMono I _

lemma tableauBideterminant_mem_dualWeyl (R : Type) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    qa_P R I ∈ dualWeyl R n n (qa_nu mu) := by
  rw [tableauBideterminant_eq_bideterminant, ← qa_shape hmu]
  exact bidetMem R n n _ _ _ _

lemma tableauBideterminant_ne_zero (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_P R I ≠ 0 := by
  intro h
  have := (tableauBideterminant_degree_leadingCoeff R I).2
  rw [h] at this
  simp at this

lemma map_tableauBideterminant {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} [NeZero n] {mu : Fin n → ℤ}
    (I : TIdx mu) : MvPolynomial.map φ (qa_P R I) = qa_P S I := by
  unfold qa_P
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp

lemma qa_exp_mem {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    qa_exp I ∈ ssIdx n n (qa_nu mu) := by
  have h1 := leadInterlaced ℤ n n (qa_nu mu) (qa_P ℤ I) (tableauBideterminant_mem_dualWeyl ℤ hmu I) (tableauBideterminant_ne_zero ℤ I)
  have h2 := colSums ℤ n n (qa_nu mu) (qa_P ℤ I) (tableauBideterminant_mem_dualWeyl ℤ hmu I) _
    (((colLex n n).degree_mem_support_iff _).mpr (tableauBideterminant_ne_zero ℤ I))
  rw [(tableauBideterminant_degree_leadingCoeff ℤ I).1] at h1 h2
  exact ⟨h1, h2⟩

def qa_stdEquiv {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    {I : TIdx mu // StdT I} ≃ ssIdx n n (qa_nu mu) :=
  Equiv.ofBijective (fun I => ⟨qa_exp I.1, qa_exp_mem hmu I.1⟩)
    ⟨fun I J h => Subtype.ext (qa_exp_inj I.1 J.1 I.2 J.2 (congrArg Subtype.val h)),
     fun m => by
      obtain ⟨I, hI, he⟩ := qa_exp_surj hmu m.1 m.2
      exact ⟨⟨I, hI⟩, Subtype.ext he⟩⟩

theorem linearIndependent_standard_tableauBideterminant (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] (mu : Fin n → ℤ) :
    LinearIndependent R (fun I : {I : TIdx mu // StdT I} => qa_P R I.1) := by
  refine ldbasis_linearIndependent (colLex n n) _ ?_ fun I => (tableauBideterminant_degree_leadingCoeff R I.1).2
  intro I J h
  simp only [(tableauBideterminant_degree_leadingCoeff R _).1] at h
  exact Subtype.ext (qa_exp_inj I.1 J.1 I.2 J.2 h)

theorem dualWeyl_eq_span_standard_tableauBideterminant (B : Type) [CommRing B] [IsDomain B] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    dualWeyl B n n (qa_nu mu) =
      Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) := by
  apply le_antisymm
  · suffices key : ∀ d : (colLex n n).syn, ∀ f ∈ dualWeyl B n n (qa_nu mu),
        (colLex n n).toSyn ((colLex n n).degree f) = d →
          f ∈ Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) by
      intro f hf
      exact key _ f hf rfl
    intro d
    induction d using WellFoundedLT.induction with
    | _ d ih =>
      intro f hf hd
      by_cases hf0 : f = 0
      · rw [hf0]; exact Submodule.zero_mem _
      have hint : Interlaced ((colLex n n).degree f) := leadInterlaced B n n _ f hf hf0
      have hcol := colSums B n n _ f hf _ (((colLex n n).degree_mem_support_iff f).mpr hf0)
      obtain ⟨I, hI, he⟩ := qa_exp_surj hmu _ ⟨hint, hcol⟩
      have hbS : qa_P B I ∈ Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) :=
        Submodule.subset_span ⟨⟨I, hI⟩, rfl⟩
      have hdecomp : f = (f - (colLex n n).leadingCoeff f • qa_P B I) + (colLex n n).leadingCoeff f • qa_P B I := by
        abel
      rw [hdecomp]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hbS)
      by_cases h0 : f - (colLex n n).leadingCoeff f • qa_P B I = 0
      · rw [h0]; exact Submodule.zero_mem _
      have hlt := lcassem_sub_lt (colLex n n) (f := f) (g := qa_P B I) ((tableauBideterminant_degree_leadingCoeff B I).1.trans he)
        (tableauBideterminant_degree_leadingCoeff B I).2 h0
      exact ih _ (hd ▸ hlt) _ (Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (tableauBideterminant_mem_dualWeyl B hmu I))) rfl
  · rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact tableauBideterminant_mem_dualWeyl B hmu I.1

theorem dualWeyl_eq_span_tableauBideterminant (B : Type) [CommRing B] [IsDomain B] {n : ℕ} [NeZero n] {mu : Fin n → ℤ}
    (hmu : Dominant mu) :
    dualWeyl B n n (qa_nu mu) = Submodule.span B (Set.range fun I : TIdx mu => qa_P B I) := by
  apply le_antisymm
  · rw [dualWeyl_eq_span_standard_tableauBideterminant B hmu]
    apply Submodule.span_mono
    rintro _ ⟨I, rfl⟩
    exact ⟨I.1, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact tableauBideterminant_mem_dualWeyl B hmu I

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.TranslatesSpanCanonical
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

lemma qd_vander {σ : Type} (W : Submodule ℚ (MvPolynomial σ ℚ)) (p : Polynomial (MvPolynomial σ ℚ))
    (h : ∀ t : ℕ, p.eval (C (t : ℚ)) ∈ W) (k : ℕ) : p.coeff k ∈ W := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℚ]
  intro φ
  set ψ : MvPolynomial σ ℚ →ₗ[ℚ] ℚ := φ ∘ₗ W.mkQ with hψ
  have hW : ∀ x ∈ W, ψ x = 0 := by
    intro x hx
    rw [hψ, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hx, map_zero]
  set q : Polynomial ℚ := ∑ i ∈ range (p.natDegree + 1), Polynomial.monomial i (ψ (p.coeff i)) with hq
  have hev : ∀ t : ℕ, q.eval (t : ℚ) = 0 := by
    intro t
    rw [← hW _ (h t), Polynomial.eval_eq_sum_range (p := p), map_sum, hq, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_monomial, ← map_pow, mul_comm (p.coeff i), ← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.range (fun t : ℕ => (t : ℚ)))
    · rintro _ ⟨t, rfl⟩
      exact hev t
    · exact Set.infinite_range_of_injective Nat.cast_injective
  have hc : q.coeff k = ψ (p.coeff k) := by
    rw [hq, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' ]
    split_ifs with hk
    · rfl
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hk), map_zero]
  rw [hq0, Polynomial.coeff_zero] at hc
  exact hc.symm

variable {n : ℕ}

lemma qd_eval_rowGen (a b : Fin n) (t : ℚ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    (rowGen ℚ a b f).eval (C t) = rowAct ℚ (1 + Matrix.single b a t) f := by
  have h : ((Polynomial.aeval (R := MvPolynomial (Fin n × Fin n) ℚ) (C t : MvPolynomial (Fin n × Fin n) ℚ)).restrictScalars
      ℚ).comp (rowGen ℚ a b) = rowAct ℚ (1 + Matrix.single b a t) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, rowGen_X, rowAct, aeval_X]
    simp only [AlgHom.restrictScalars_apply, map_add, Polynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
      Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply, Matrix.single_apply]
    congr 1
    · simp
    · split_ifs with hv
      · simp only [hv, true_and, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_self,
          RingHom.id_apply]
        rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
        simp
      · simp [Ne.symm hv]
  have := congrArg (fun φ => φ f) h
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using this

lemma qd_det_E (a b : Fin n) (t : ℕ) : IsUnit (1 + Matrix.single b a (t : ℚ)).det := by
  by_cases hab : b = a
  · subst hab
    have : (1 + Matrix.single b b (t : ℚ)) = Matrix.diagonal (fun i => if i = b then (1 + t : ℚ) else 1) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hi : i = b <;> simp [hi, Matrix.single_apply]
        intro h; exact absurd h.symm hi
      · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij, Matrix.single_apply]
        intro h1 h2; exact absurd (h1.symm.trans h2) hij
    rw [this, Matrix.det_diagonal, Finset.prod_ite_eq']
    simp only [mem_univ, if_true]
    exact isUnit_iff_ne_zero.2 (by positivity)
  · have : (1 + Matrix.single b a (t : ℚ)) = Matrix.transvection b a (t : ℚ) := rfl
    rw [this, Matrix.det_transvection_of_ne _ _ hab]
    exact isUnit_one

variable [NeZero n]

def translatesSpanCanonical (mu : Fin n → ℤ) : Submodule ℚ (MvPolynomial (Fin n × Fin n) ℚ) :=
  Submodule.span ℚ {f | ∃ g : Matrix (Fin n) (Fin n) ℚ, IsUnit g.det ∧ f = rowAct ℚ g (qd_P mu (canT mu))}

lemma qd_W_closed (mu : Fin n → ℤ) : RowDivClosed (translatesSpanCanonical mu) := by
  intro a b k f hf
  have : translatesSpanCanonical mu ≤ (translatesSpanCanonical mu).comap (rowDivL ℚ a b k) := by
    unfold translatesSpanCanonical
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, rowDivL_apply]
    apply qd_vander
    intro t
    rw [qd_eval_rowGen, ← AlgHom.comp_apply, rowActMul]
    apply Submodule.subset_span
    exact ⟨_, by rw [Matrix.det_mul]; exact hg.mul (qd_det_E a b t), rfl⟩
  exact this hf

lemma qd_W_eq (mu : Fin n → ℤ) : translatesSpanCanonical mu = dualWeyl ℚ n n (qd_nu mu) := by
  have hcan : qd_P mu (canT mu) ∈ translatesSpanCanonical mu := by
    apply Submodule.subset_span
    exact ⟨1, by simp, by rw [ldrow_rowAct_one]; rfl⟩
  apply closedEqNabla n n le_rfl (qd_nu mu) (qd_nu_anti mu) _ _ (qd_W_closed mu)
  · obtain ⟨c0, hc0, h0⟩ := tableauBideterminant_canonical_eq_smul_highestWeight mu
    have : hw ℚ le_rfl (qd_nu mu) = c0⁻¹ • qd_P mu (canT mu) := by
      rw [h0, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hcan
  · unfold translatesSpanCanonical
    rw [Submodule.span_le]
    rintro _ ⟨g, _, rfl⟩
    exact dualWeylRowStable ℚ n n _ g _ (tableauBideterminant_mem_dualWeyl' mu _)

omit [NeZero n] in
lemma qd_evGL_map {R' : Type} [CommRing R'] [Algebra ℚ R'] (γ : GL (Fin n) ℚ) (z : GLCoord ℤ n) :
    evGL (Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) z = algebraMap ℚ R' (evGL γ z) := by
  have h : evGL (Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) = (algebraMap ℚ R').comp (evGL γ) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (genMat ℤ n).det)
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp [evGL, IsLocalization.Away.lift_eq]
  exact congrArg (fun φ => φ z) h

omit [NeZero n] in
lemma qd_aeval_mul {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (γ : GL (Fin n) ℚ)
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ).val v.2 v.1) P
      = aeval (fun v : Fin n × Fin n => x.val v.2 v.1) (rowAct ℚ γ.val.transpose P) := by
  have h : aeval (R := ℚ) (fun v : Fin n × Fin n => (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ).val v.2 v.1)
      = (aeval (R := ℚ) (fun v : Fin n × Fin n => x.val v.2 v.1)).comp (rowAct ℚ γ.val.transpose) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, rowAct, aeval_X, aeval_X, map_sum, Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, aeval_X, aeval_C, Matrix.transpose_apply, mul_comm]
    rfl
  exact congrArg (fun φ => φ P) h

omit [NeZero n] in
lemma qd_ev_algebraMap {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (c : ℚ) :
    evGLR (R := ℚ) x (algebraMap ℚ (GLCoord ℚ n) c) = algebraMap ℚ R' c := by
  rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n), evGLR,
    IsLocalization.Away.lift_eq, MvPolynomial.algebraMap_eq, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]

lemma qd_ev_L_mul {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (γ : GL (Fin n) ℚ) (mu : Fin n → ℤ)
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    evGLR (R := ℚ) (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) (qd_L mu P)
      = evGLR (R := ℚ) x (qd_L mu
        (((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ) • rowAct ℚ γ.val.transpose P)) := by
  rw [map_smul, qd_L_apply, qd_L_apply, map_mul, qd_ev_sig, qd_aeval_mul, Algebra.smul_def, map_mul, map_mul,
    qd_ev_sig]
  have h1 : evGLR (R := ℚ) (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) (qd_U mu)
      = evGLR (R := ℚ) x (algebraMap ℚ (GLCoord ℚ n) ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ))
        * evGLR (R := ℚ) x (qd_U mu) := by
    have h2 : evGLR (R := ℚ) x (algebraMap ℚ (GLCoord ℚ n) ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ))
        = algebraMap ℚ R' ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ) :=
      qd_ev_algebraMap x _
    rw [h2, ← qd_evGL_detU, ← qd_evGL_map]
    unfold qd_U
    rw [qd_evGLR_mapCoord, qd_evGLR_mapCoord, qd_evGL_detU, qd_evGL_detU, qd_evGL_detU, map_mul, mul_zpow,
      Units.val_mul, mul_comm]
  rw [h1]
  ring

lemma qd_L_inj (mu : Fin n → ℤ) (P Q : MvPolynomial (Fin n × Fin n) ℚ)
    (h : evGLR (R := ℚ) (qd_genPt n) (qd_L mu P) = evGLR (R := ℚ) (qd_genPt n) (qd_L mu Q)) : P = Q := by
  rw [qd_L_apply, qd_L_apply, map_mul, map_mul] at h
  have h2 := (qd_U_unit (qd_genPt n) mu).mul_left_cancel h
  rw [qd_ev_sig, qd_ev_sig, aeval_generic_point, aeval_generic_point] at h2
  exact qd_sig_inj n (Polynomial.C_injective h2)

def qd_Lam (mu : Fin n → ℤ) : (TIdx mu → ℚ) →ₗ[ℚ] GLCoord ℚ n :=
  Fintype.linearCombination ℚ (fun K : TIdx mu => mapCoord ℚ (brk mu K))

lemma qd_Lam_apply (mu : Fin n → ℤ) (w : TIdx mu → ℚ) :
    qd_Lam mu w = ∑ K, w K • mapCoord ℚ (brk mu K) := by
  rw [qd_Lam, Fintype.linearCombination_apply]

lemma qd_Lam_L (mu : Fin n → ℤ) (w : TIdx mu → ℚ) : qd_Lam mu w = qd_L mu (∑ K, w K • qd_P mu K) := by
  rw [qd_Lam_apply, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, qd_L_P]

def qd_gcan (mu : Fin n → ℤ) (γ : GL (Fin n) ℚ) : TIdx mu → ℚ := fun K => evGL γ (TMat mu K (canT mu))

lemma qd_translate (mu : Fin n → ℤ) (γ : GL (Fin n) ℚ) :
    ∑ K, qd_gcan mu γ K • qd_P mu K =
      ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ) • rowAct ℚ γ.val.transpose (qd_P mu (canT mu)) := by
  apply qd_L_inj mu
  rw [← qd_ev_L_mul, qd_L_P, qd_evGLR_mapCoord, brk, qc_TMat_mul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, qd_L_P, Algebra.smul_def, map_mul, qd_evGLR_mapCoord, qd_evGL_map, mul_comm]
  rw [qd_ev_algebraMap]
  rfl

theorem qd_gen (mu : Fin n → ℤ) (w : TIdx mu → ℚ) :
    ∃ w' ∈ Submodule.span ℚ (Set.range (qd_gcan mu)), qd_Lam mu w = qd_Lam mu w' := by
  have h1 : (∑ K, w K • qd_P mu K) ∈ translatesSpanCanonical mu := by
    rw [qd_W_eq]
    exact Submodule.sum_mem _ fun K _ => Submodule.smul_mem _ _ (tableauBideterminant_mem_dualWeyl' mu K)
  have h2 : translatesSpanCanonical mu ≤ (Submodule.span ℚ (Set.range (qd_gcan mu))).map
      (Fintype.linearCombination ℚ (fun K : TIdx mu => qd_P mu K)) := by
    unfold translatesSpanCanonical
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    set γ : GL (Fin n) ℚ := Matrix.GeneralLinearGroup.mk'' g.transpose (by rwa [Matrix.det_transpose]) with hγ
    have hv : γ.val.transpose = g := by
      rw [hγ]; exact Matrix.transpose_transpose g
    refine ⟨(((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ))⁻¹ • qd_gcan mu γ,
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, rfl⟩), ?_⟩
    rw [map_smul, Fintype.linearCombination_apply, qd_translate, hv, smul_smul,
      inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  obtain ⟨w', hw', he⟩ := h2 h1
  refine ⟨w', hw', ?_⟩
  rw [qd_Lam_L, qd_Lam_L, ← he, Fintype.linearCombination_apply]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

