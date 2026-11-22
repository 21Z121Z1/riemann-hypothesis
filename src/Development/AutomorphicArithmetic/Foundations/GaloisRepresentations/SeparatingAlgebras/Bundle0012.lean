import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0010
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0050
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LatFacts
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.latFacts_pf :
    UpperTheory.Gal.Gen.LatFacts := by
  classical
  intro l _ ι σ V _
  refine ⟨fun φ => ?_, fun x => ?_⟩
  · let B := Module.finBasis ℂ V
    choose s a ha using fun i => GlobalTheory.IntStruct.exists_coord_eq_sum_coeff V B i
    refine ⟨∑ i, ∑ m : s i, ‖ι.symm (a i m)‖ * ‖ι.symm (φ (B i))‖,
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun m _ => mul_nonneg (norm_nonneg _) (norm_nonneg _),
      fun R x hx => ?_⟩
    have e : φ x = ∑ i, B.repr x i * φ (B i) := by
      have h := congrArg φ (B.sum_repr x)
      rw [map_sum] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    have h1 : ∀ i, ‖ι.symm (B.repr x i)‖ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R := by
      intro i
      rw [ha i x, map_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [map_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _)
    rw [e, map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_mul, norm_mul, Finset.sum_mul]
    calc _ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R * ‖ι.symm (φ (B i))‖ :=
          mul_le_mul_of_nonneg_right (h1 i) (norm_nonneg _)
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by ring
  · have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by linarith)
    set T : ℝ := ∑ m ∈ x.1.support, ‖ι.symm (MvPolynomial.coeff m x.1)‖ + 1 with hTdef
    have hS : 0 ≤ ∑ m ∈ x.1.support, ‖ι.symm (MvPolynomial.coeff m x.1)‖ :=
      Finset.sum_nonneg fun m _ => norm_nonneg _
    have hT : 0 < T := by linarith
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hT) (inv_lt_one_of_one_lt₀ hl)
    have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    refine ⟨(l : ℂ) ^ k, pow_ne_zero _ hlc, fun m => ?_⟩
    have hnl : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
      have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
      rw [map_natCast, Padic.norm_p] at h
      exact h
    have hn : ‖ι.symm ((l : ℂ) ^ k)‖ = ((l : ℝ)⁻¹) ^ k := by
      rw [map_pow, map_natCast, norm_pow, hnl]
    have hc : ‖ι.symm (MvPolynomial.coeff m x.1)‖ ≤ T := by
      by_cases hm : m ∈ x.1.support
      · have := Finset.single_le_sum (f := fun m => ‖ι.symm (MvPolynomial.coeff m x.1)‖)
          (fun m _ => norm_nonneg _) hm
        linarith
      · rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, norm_zero]
        exact hT.le
    have e : MvPolynomial.coeff m (((l : ℂ) ^ k • x : V) : MvPolynomial σ ℂ) =
        (l : ℂ) ^ k * MvPolynomial.coeff m x.1 := by
      rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    rw [e, map_mul, norm_mul, hn]
    calc _ ≤ ((l : ℝ)⁻¹) ^ k * T := mul_le_mul_of_nonneg_left hc (pow_nonneg hl0.le _)
      _ ≤ T⁻¹ * T := mul_le_mul_of_nonneg_right hk.le hT.le
      _ = 1 := inv_mul_cancel₀ hT.ne'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LocRho
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen.Loc

section CoefLeLemmas

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {σ : Type}

theorem coefLe_sum {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ a ∈ s, CoefLe ι R (f a)) : CoefLe ι R (∑ a ∈ s, f a) := by
  intro m
  rw [MvPolynomial.coeff_sum, map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR (fun a ha => h a ha m)

theorem coefLe_mul {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) {p q : MvPolynomial σ ℂ}
    (hp : CoefLe ι R p) (hq : CoefLe ι S q) : CoefLe ι (R * S) (p * q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hR hS) ?_
  intro x _
  rw [map_mul, norm_mul]
  exact mul_le_mul (hp _) (hq _) (norm_nonneg _) hR

theorem coefLe_one : CoefLe ι 1 (1 : MvPolynomial σ ℂ) := by
  classical
  intro m
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

theorem coefLe_pow {R : ℝ} (hR : 0 ≤ R) {p : MvPolynomial σ ℂ} (hp : CoefLe ι R p) (k : ℕ) :
    CoefLe ι (R ^ k) (p ^ k) := by
  induction k with
  | zero => simpa using coefLe_one ι
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact coefLe_mul ι (pow_nonneg hR _) hR ih hp

theorem coefLe_prod {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (h : ∀ a ∈ s, CoefLe ι (r a) (f a)) :
    CoefLe ι (∏ a ∈ s, r a) (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coefLe_one ι
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact coefLe_mul ι (hr a) (Finset.prod_nonneg fun b _ => hr b) (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem coefLe_C_mul_X {c : ℂ} {R : ℝ} (hR : 1 ≤ R) (hc : ‖ι.symm c‖ ≤ R) (v : σ) :
    CoefLe ι R (MvPolynomial.C c * MvPolynomial.X v) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
  split_ifs
  · simpa using hc
  · simpa using zero_le_one.trans hR

end CoefLeLemmas

theorem norm_det_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hR : 1 ≤ R) (h : ∀ i j, ‖ι.symm (M i j)‖ ≤ R) : ‖ι.symm M.det‖ ≤ R ^ n :=
  _root_.UpperTheory.Reformulated.B.Qh58.norm_det_le ι M R hR h

def sz {a : ℕ} (lam : DomWeight a) : ℕ := ∑ k, (lam.w k).natAbs

theorem sz_dual {a : ℕ} (lam : DomWeight a) : sz lam.dual = sz lam := by
  unfold sz
  simp only [DomWeight.dual, Int.natAbs_neg]
  exact Equiv.sum_comp Fin.revPerm (fun k => (lam.w k).natAbs)

theorem one_le {a : ℕ} (lam : DomWeight a) :
    ∑ i, lam.natW i + a * lam.detShift.natAbs ≤ a * (2 * sz lam) := by
  cases a with
  | zero => simp
  | succ n =>
    have hd : lam.detShift = lam.w (Fin.last n) := by
      simp [DomWeight.detShift, Fin.last]
    have hl : lam.natW (Fin.last n) = 0 := by
      simp [DomWeight.natW, hd]
    have hi : ∀ i : Fin n, lam.natW i.castSucc ≤ (lam.w i.castSucc).natAbs + (lam.w (Fin.last n)).natAbs := by
      intro i
      simp only [DomWeight.natW, hd]
      omega
    have h1 : ∑ i : Fin n, lam.natW i.castSucc ≤
        (∑ i : Fin n, (lam.w i.castSucc).natAbs) + n * (lam.w (Fin.last n)).natAbs := by
      calc ∑ i : Fin n, lam.natW i.castSucc
          ≤ ∑ i : Fin n, ((lam.w i.castSucc).natAbs + (lam.w (Fin.last n)).natAbs) :=
            Finset.sum_le_sum fun i _ => hi i
        _ = _ := by simp [Finset.sum_add_distrib]
    rw [Fin.sum_univ_castSucc, hl, hd]
    unfold sz
    rw [Fin.sum_univ_castSucc]
    generalize (∑ i : Fin n, (lam.w i.castSucc).natAbs) = t at h1 ⊢
    generalize (lam.w (Fin.last n)).natAbs = e at h1 ⊢
    generalize (∑ i : Fin n, lam.natW i.castSucc) = u at h1 ⊢
    nlinarith [Nat.zero_le (n * t), Nat.zero_le (n * e)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

noncomputable def emb : InfinitePlace E ⊕ InfinitePlace E → (E →+* ℂ)
  | .inl v => v.embedding
  | .inr v => ComplexEmbedding.conjugate v.embedding

theorem mk_emb_inl (v : InfinitePlace E) : InfinitePlace.mk (emb (.inl v)) = v :=
  InfinitePlace.mk_embedding v

theorem mk_emb_inr (v : InfinitePlace E) : InfinitePlace.mk (emb (.inr v)) = v := by
  simp only [emb]
  rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

theorem emb_injective : Function.Injective (emb (E := E)) := by
  rintro (v | v) (w | w) h
  · have := congrArg InfinitePlace.mk h
    rw [mk_emb_inl, mk_emb_inl] at this
    rw [this]
  · exfalso
    have := congrArg InfinitePlace.mk h
    rw [mk_emb_inl, mk_emb_inr] at this
    subst this
    exact conjugate_ne v.embedding h.symm
  · exfalso
    have := congrArg InfinitePlace.mk h
    rw [mk_emb_inr, mk_emb_inl] at this
    subst this
    exact conjugate_ne v.embedding h
  · have := congrArg InfinitePlace.mk h
    rw [mk_emb_inr, mk_emb_inr] at this
    rw [this]

def wI {T : Type} [DecidableEq T] (I : Finset T) (n : ℕ) : T × Fin n × Fin n → ℕ := fun v => if v.1 ∈ I then 1 else 0

theorem homog_of_mem {T : Type} [Fintype T] [DecidableEq T] (I : Finset T) (n : ℕ) (lam : T → DomWeight n)
    (x : MvPolynomial (T × Fin n × Fin n) ℂ) (hx : x ∈ Formalism.L2.DIV.VV ℂ lam) :
    MvPolynomial.IsWeightedHomogeneous (wI I n) x (∑ τ, if τ ∈ I then ∑ i, (lam τ).natW i else 0) := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hx
  rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
  refine (Submodule.span_le.2 ?_) hx
  rintro _ ⟨F, hF, rfl⟩
  refine (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 ?_
  refine MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun τ _ => ?_
  intro d hd
  obtain ⟨m, rfl, hm⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _ hd
  have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) m = (lam τ).natW :=
    (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (hF τ).1 hm
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul])]
  by_cases hτ : τ ∈ I
  · rw [if_pos hτ, ← hw, Finsupp.weight_apply]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul, wI, if_pos hτ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [Pi.single_apply]
  · simp [wI, hτ, Finsupp.sum]

theorem block_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {T : Type} [DecidableEq T] (I : Finset T) {n : ℕ}
    (A : T → Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 1 ≤ R) (hA : ∀ τ i j, ‖ι.symm (A τ i j)‖ ≤ if τ ∈ I then R else 1)
    (D : ℕ) (x : MvPolynomial (T × Fin n × Fin n) ℂ) (hx : MvPolynomial.IsWeightedHomogeneous (wI I n) x D)
    (h1 : CoefLe ι 1 x) : CoefLe ι (R ^ D) (Formalism.GradedWeylDivisibility.blockAct ℂ A x) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  set y : T × Fin n × Fin n → MvPolynomial (T × Fin n × Fin n) ℂ :=
    fun v => ∑ b : Fin n, MvPolynomial.C (A v.1 v.2.1 b) * MvPolynomial.X (v.1, (b, v.2.2)) with hydef
  have hr : ∀ τ, (if τ ∈ I then R else 1) = R ^ (if τ ∈ I then 1 else 0) := fun τ => by split_ifs <;> simp
  have hy : ∀ v, CoefLe ι (R ^ wI I n v) (y v) := fun v =>
    coefLe_sum ι _ _ (pow_nonneg hR0 _) fun b _ => coefLe_C_mul_X ι (one_le_pow₀ hR) ((hA _ _ _).trans_eq (hr _)) _
  have e : Formalism.GradedWeylDivisibility.blockAct ℂ A x =
      ∑ m ∈ x.support, MvPolynomial.C (MvPolynomial.coeff m x) * (m.prod fun v e => y v ^ e) := by
    conv_lhs => rw [x.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_monomial]
    rfl
  rw [e]
  refine coefLe_sum ι _ _ (pow_nonneg hR0 _) fun m hm k => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul, norm_mul]
  have hdeg : Finsupp.weight (wI I n) m = D := hx (MvPolynomial.mem_support_iff.1 hm)
  have h := coefLe_prod ι m.support (fun v => y v ^ m v) (fun v => (R ^ wI I n v) ^ m v)
    (fun _ => by positivity) (fun v _ => coefLe_pow ι (pow_nonneg hR0 _) (hy v) (m v))
  have e2 : ∏ v ∈ m.support, (R ^ wI I n v) ^ m v = R ^ D := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun v _ => by rw [← pow_mul, smul_eq_mul, mul_comm]
  rw [e2] at h
  exact (mul_le_mul (h1 m) (h k) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem det_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {T : Type} [Fintype T] [DecidableEq T] (I : Finset T) {n : ℕ}
    (lam : T → DomWeight n) (A : T → GL (Fin n) ℂ) (R : ℝ) (hR : 1 ≤ R)
    (h : ∀ τ i j, (‖ι.symm (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ if τ ∈ I then R else 1) ∧
      ‖ι.symm ((((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ if τ ∈ I then R else 1) :
    ‖ι.symm (Formalism.L2.DIV.detTwK lam A)‖ ≤ R ^ (∑ τ, if τ ∈ I then n * (lam τ).detShift.natAbs else 0) := by
  rw [Formalism.L2.DIV.detTw_eq, map_prod, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
  have hR' : 1 ≤ if τ ∈ I then R else 1 := by split_ifs; exacts [hR, le_rfl]
  have h1 := norm_det_le ι ((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) _ hR' fun i j => (h τ i j).1
  have h2 := norm_det_le ι (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) _ hR' fun i j => (h τ i j).2
  have hinv : (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det =
      (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have e : R ^ (if τ ∈ I then n * (lam τ).detShift.natAbs else 0) =
      ((if τ ∈ I then R else 1) ^ n) ^ (lam τ).detShift.natAbs := by
    split_ifs <;> simp [pow_mul]
  rw [e]
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (lam τ).detShift
  · rw [hk, zpow_natCast, map_pow, norm_pow, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 k
  · rw [hk, zpow_neg, zpow_natCast, ← inv_pow, ← hinv, map_pow, norm_pow, Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 k

theorem rho_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : Wt E a) [DecidableEq (InfinitePlace E)]
    (I : Finset (InfinitePlace E)) (A : InfinitePlace E → GL (Fin a) ℂ) (R : ℝ) (hR : 1 ≤ R)
    (hA : ∀ τ i j, (‖ι.symm (((A τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ if τ ∈ I then R else 1) ∧
      ‖ι.symm ((((A τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ if τ ∈ I then R else 1)
    (x : W.Sp) (hx : CoefLe ι 1 x.1) :
    CoefLe ι (R ^ (a * ∑ v ∈ I, 2 * sz (W v))) (Formalism.L2.DIV.rhoK (K := ℂ) W A x).1 := by
  intro m
  have hb := block_le ι I (fun τ => Matrix.transpose ((A τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) R hR
    (fun τ i j => by simpa [Matrix.transpose_apply] using (hA τ j i).1) _ x.1 (homog_of_mem I a W x.1 x.2) hx m
  have hd := det_le ι I W A R hR hA
  have hcoe : (Formalism.L2.DIV.rhoK (K := ℂ) W A x).1 =
      Formalism.L2.DIV.detTwK W A • Formalism.L2.DIV.trAct A x.1 := rfl
  rw [hcoe, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, norm_mul]
  have hR0 : (0 : ℝ) ≤ R := by linarith
  refine (mul_le_mul hd hb (norm_nonneg _) (pow_nonneg hR0 _)).trans ?_
  rw [← pow_add]
  refine pow_le_pow_right₀ hR ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_ite_mem_eq I]
  refine Finset.sum_le_sum fun v _ => ?_
  split_ifs
  · rw [add_comm]; exact one_le (W v)
  · simp

end UpperTheory.Gal.Gen.Loc
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.NormMapIntegerLeOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem norm_map_integer_le_one {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l) (hl : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hj : Continuous j) (y : u.adicCompletion E) (hy : y ∈ u.adicCompletionIntegers E) : ‖j y‖ ≤ 1 := by
  have hvl : Valued.v ((l : ℕ) : u.adicCompletion E) < 1 := by
    have h1 : u.valuation E (((l : ℕ) : 𝓞 E) : E) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) u _).2 hl
    have h2 : (((l : ℕ) : u.adicCompletion E)) = algebraMap E (u.adicCompletion E) (((l : ℕ) : 𝓞 E) : E) := by simp
    rw [h2]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).trans_lt h1
  have hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹ := by
    have h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]
  have hlt : ∀ k : ℕ, ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k < 1 := by
    intro k
    have hyv : Valued.v y ≤ 1 := hy
    have hv : Valued.v (((l : ℕ) : u.adicCompletion E) * y ^ k) < 1 := by
      rw [map_mul, map_pow]
      exact mul_lt_one_of_lt_of_le hvl (pow_le_one' hyv k)
    have ht := Valued.tendsto_zero_pow_of_v_lt_one hv
    have ht2 : Filter.Tendsto (fun m : ℕ => (j (((l : ℕ) : u.adicCompletion E) * y ^ k)) ^ m) Filter.atTop (nhds 0) := by
      have := (hj.tendsto 0).comp ht
      simpa [Function.comp_def, map_pow] using this
    have := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ht2
    simpa [map_mul, map_pow, norm_mul, norm_pow] using this
  by_contra hcon
  have hgt : 1 < ‖j y‖ := not_le.1 hcon
  have hlpos : 0 < ‖j ((l : ℕ) : u.adicCompletion E)‖ := by
    rw [hlnorm]
    exact inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖j ((l : ℕ) : u.adicCompletion E)‖⁻¹) hgt
  have := hlt k
  have h3 : 1 < ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k := by
    rw [inv_lt_iff_one_lt_mul₀ hlpos] at hk
    exact hk.trans_eq (mul_comm _ _)
  linarith

private theorem norm_map_entry_le {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] {n : ℕ}
    (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l) (hl : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hj : Continuous j) (d : ℕ) (M : Matrix (Fin n) (Fin n) (u.adicCompletion E))
    (hM : GlobalTheory.CongW.IntMat u (((l : u.adicCompletion E) ^ d) • M)) (a b : Fin n) : ‖j (M a b)‖ ≤ (l : ℝ) ^ d := by
  have h1 := norm_map_integer_le_one l u j hl hj _ (hM a b)
  have hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹ := by
    have h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]
  have hl0 : (0 : ℝ) < (l : ℝ) ^ d := pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) d
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, norm_mul, norm_pow, hlnorm, inv_pow] at h1
  rwa [inv_mul_le_iff₀ hl0, mul_one] at h1

theorem UpperTheory.Gal.Gen.kappa_pf :
    UpperTheory.Gal.Gen.Kappa := by
  intro E _ _ _ l _ ι n
  have hex := fun v : InfinitePlace E =>
    GlobalTheory.LadicInf.exists_place E l (ι.symm.toRingHom.comp v.embedding)
  choose u j hl hj hjE using hex
  let f : InfinitePlace E → Af E →+* ℂ := fun v =>
    ι.toRingHom.comp ((j v).comp (pLoc E (u v)))
  let κ : UA E n →* (InfinitePlace E → GL (Fin n) ℂ) :=
    MonoidHom.pi fun v => (Matrix.GeneralLinearGroup.map ((f v).comp (pFin E))).comp (UA E n).subtype
  have hκ : ∀ (g : UA E n) (v : InfinitePlace E),
      κ g v = Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (j v)) (cLoc (u v) g) := by
    intro g v
    ext
    rfl
  refine ⟨κ, ?_, ?_, ?_⟩
  · rintro γ ⟨g₀, hg₀⟩
    funext v
    ext a b
    change (f v) (pFin E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b)) =
      coord v.embedding (pInf E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b))
    have hg₁ : (γ.1 : GL (Fin n) (Ad E)) = ratGL E n g₀ := hg₀.symm
    rw [hg₁]
    change (f v) (pFin E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b))) =
      coord v.embedding (pInf E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b)))
    rw [coord_algebraMap]
    have h := congrArg (fun φ : E →+* Qbar l => φ ((g₀ : Matrix (Fin n) (Fin n) E) a b)) (hjE v)
    simp only [RingHom.coe_comp, Function.comp_apply] at h
    change ι (j v (algebraMap E (u v |>.adicCompletion E) _)) = _
    rw [h]
    simp
  · intro x hx
    funext v
    have hx' : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
    have h2 : Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 =
        Matrix.GeneralLinearGroup.map (f v) (Matrix.GeneralLinearGroup.map (pFin E) x.1) := by ext; rfl
    change Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 = 1
    rw [h2, hx', map_one]
  · intro g d hd v a b
    obtain ⟨h1, h2⟩ := hd (u v) (hl v)
    constructor
    · rw [hκ g v]
      change ‖ι.symm (ι (j v (((cLoc (u v) g : GL (Fin n) ((u v).adicCompletion E)) :
        Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _
      rw [RingEquiv.symm_apply_apply]
      exact norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h1 a b
    · rw [hκ g v, ← map_inv]
      change ‖ι.symm (ι (j v ((((cLoc (u v) g)⁻¹ : GL (Fin n) ((u v).adicCompletion E)) :
        Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _
      rw [RingEquiv.symm_apply_apply]
      exact norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h2 a b
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.PowNhds
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen
open Topology Filter

section
variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [NormedRing R] [NormedAlgebra 𝕜 R]

private lemma strict_pow (N : ℕ) :
    HasStrictFDerivAt (fun x : R => x ^ N) ((N : 𝕜) • ContinuousLinearMap.id 𝕜 R) (1 : R) := by
  refine (hasStrictFDerivAt_pow' (𝕜 := 𝕜) N (x := (1 : R))).congr_fderiv ?_
  simp only [one_pow, MulOpposite.op_one, one_smul, Finset.sum_const, Finset.card_range]
  rw [Nat.cast_smul_eq_nsmul]

private lemma map_pow_nhds [CharZero 𝕜] [CompleteSpace 𝕜] [CompleteSpace R] {N : ℕ} (hN : N ≠ 0) :
    map (fun x : R => x ^ N) (𝓝 1) = 𝓝 1 := by
  have hN' : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let e : R ≃L[𝕜] R := ContinuousLinearEquiv.equivOfInverse ((N : 𝕜) • ContinuousLinearMap.id 𝕜 R)
    ((N : 𝕜)⁻¹ • ContinuousLinearMap.id 𝕜 R) (fun x => by simp [smul_smul, hN'])
    (fun x => by simp [smul_smul, hN'])
  have hf : HasStrictFDerivAt (fun x : R => x ^ N) (e : R →L[𝕜] R) 1 := strict_pow (𝕜 := 𝕜) N
  simpa using hf.map_nhds_eq_of_equiv

private lemma units_pow_nhds [CharZero 𝕜] [CompleteSpace 𝕜] [CompleteSpace R] {N : ℕ} (hN : N ≠ 0)
    {V : Set Rˣ} (hV : V ∈ 𝓝 (1 : Rˣ)) : (fun x => x ^ N) '' V ∈ 𝓝 (1 : Rˣ) := by
  have he := Units.isOpenEmbedding_val (R := R)
  have h1 : ((↑) : Rˣ → R) '' V ∈ 𝓝 (1 : R) := by
    simpa using he.image_mem_nhds.mpr hV
  have h2 : (fun x : R => x ^ N) '' (((↑) : Rˣ → R) '' V) ∈ 𝓝 (1 : R) := by
    rw [← map_pow_nhds (𝕜 := 𝕜) hN]
    exact image_mem_map h1
  rw [← he.image_mem_nhds]
  rw [Set.image_image, Units.val_one]
  rw [Set.image_image] at h2
  simpa using h2
end

theorem UpperTheory.Gal.Gen.powNhds_pf :
    UpperTheory.Gal.Gen.PowNhds := by
  intro E _ _ w a N hN V hV
  letI : NontriviallyNormedField (w.adicCompletion E) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  letI : NormedRing (Matrix (Fin a) (Fin a) (w.adicCompletion E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra (w.adicCompletion E) (Matrix (Fin a) (Fin a) (w.adicCompletion E)) :=
    Matrix.linftyOpNormedAlgebra
  haveI : @CompleteSpace (Matrix (Fin a) (Fin a) (w.adicCompletion E))
      (@Matrix.linftyOpNormedRing (Fin a) (w.adicCompletion E) _ _ _).toUniformSpace :=
    inferInstanceAs (CompleteSpace (Fin a → Fin a → w.adicCompletion E))
  exact units_pow_nhds (𝕜 := w.adicCompletion E) hN hV
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RhoBound
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.rhoBound_pf :
    UpperTheory.Gal.Gen.DegLe → UpperTheory.Gal.Gen.BlockBound → UpperTheory.Gal.Gen.DetBound → UpperTheory.Gal.Gen.SizeLe → UpperTheory.Gal.Gen.RhoBound := by
  intro hdeg hblk hdet hsize E _ _ _ l _ ι a W A R hR hA x hx m
  have hx' : (x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ).totalDegree
      ≤ ∑ τ, ∑ i, (W τ).natW i := hdeg (InfinitePlace E) a W x x.2
  have hb := hblk l ι (InfinitePlace E) a (fun τ => ((A τ : Matrix (Fin a) (Fin a) ℂ)).transpose) R hR
    (fun τ i j => (hA τ j i).1) _ x hx' hx m
  have hd := hdet l ι (InfinitePlace E) a W A R hR hA
  have hs := hsize E a W
  have hcoe : (((Formalism.L2.DIV.rhoK W) A) x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ)
      = Formalism.L2.DIV.detTwK W A • Formalism.L2.DIV.trAct A (x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ) := rfl
  rw [hcoe, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, norm_mul]
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  calc ‖ι.symm (Formalism.L2.DIV.detTwK W A)‖ * ‖ι.symm (MvPolynomial.coeff m (Formalism.L2.DIV.trAct A (x : MvPolynomial _ ℂ)))‖
      ≤ R ^ (∑ τ, a * (W τ).detShift.natAbs) * R ^ (∑ τ, ∑ i, (W τ).natW i) :=
        mul_le_mul hd hb (norm_nonneg _) (pow_nonneg hR0 _)
    _ = R ^ (∑ τ, ∑ i, (W τ).natW i + ∑ τ, a * (W τ).detShift.natAbs) := by
        rw [← pow_add, add_comm]
    _ ≤ R ^ (a * GlobalTheory.CongW.wtSize W.at) := pow_le_pow_right₀ hR hs
end

