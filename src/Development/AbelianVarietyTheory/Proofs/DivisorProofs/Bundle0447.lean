import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthLeDividedPowerContent
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth.DepthLeContent

noncomputable section

section Lead

variable {S τ : Type} [CommRing S]

def Near (k n : ℕ) (P Q : MvPowerSeries τ S) : Prop :=
  (n : ℕ∞) ≤ P.order ∧ (n : ℕ∞) ≤ Q.order ∧ ((k + n : ℕ) : ℕ∞) ≤ (P - Q).order + 1

theorem Near.one (k : ℕ) : Near k 0 (1 : MvPowerSeries τ S) 1 := by
  simp [Near]

theorem Near.mul {k n m : ℕ} {P Q P' Q' : MvPowerSeries τ S} (h : Near k n P Q)
    (h' : Near k m P' Q') : Near k (n + m) (P * P') (Q * Q') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · push_cast; exact (add_le_add h1 h1').trans le_order_mul
  · push_cast; exact (add_le_add h2 h2').trans le_order_mul
  · have e : P * P' - Q * Q' = P * (P' - Q') + (P - Q) * Q' := by ring
    rw [e]
    refine le_trans ?_ (add_le_add_left min_order_le_add 1)
    rw [← min_add_add_right]
    refine le_min ?_ ?_
    · refine le_trans ?_ (add_le_add_left le_order_mul 1)
      rw [add_assoc]
      refine le_trans (le_of_eq ?_) (add_le_add h1 h3')
      push_cast; ring
    · refine le_trans ?_ (add_le_add_left le_order_mul 1)
      rw [add_right_comm]
      refine le_trans (le_of_eq ?_) (add_le_add h3 h2')
      push_cast; ring

theorem Near.prod {σ : Type} {k : ℕ} {a b : σ → MvPowerSeries τ S}
    (h : ∀ s, Near k 1 (a s) (b s)) (d : σ →₀ ℕ) :
    Near k d.degree (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  induction d using Finsupp.induction_linear with
  | zero => simpa using Near.one k
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
      Finsupp.prod_add_index' (by simp) (by simp [pow_add]), map_add]
    exact hf.mul hg
  | single s n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      Finsupp.degree_single]
    induction n with
    | zero => simpa using Near.one k
    | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul (h s)

theorem lead_prod (Y : τ → MvPowerSeries τ S) (hY : ∀ s, 2 ≤ (Y s - X s).order) (α : τ →₀ ℕ) :
    ((α.degree + 1 : ℕ) : ℕ∞) ≤ ((α.prod fun s k => Y s ^ k) - monomial α 1).order := by
  classical
  have hc : ∀ s, Near 2 1 (Y s) (X s) := fun s => by
    have hX : (1 : ℕ∞) ≤ (X s : MvPowerSeries τ S).order :=
      one_le_order_iff_constCoeff_eq_zero.mpr (by simp)
    refine ⟨?_, hX, ?_⟩
    · have : Y s = (Y s - X s) + X s := by ring
      rw [this]
      exact le_trans (le_min ((by norm_num : (1 : ℕ∞) ≤ 2).trans (hY s)) hX) min_order_le_add
    · have := add_le_add (hY s) (le_refl (1 : ℕ∞))
      push_cast
      exact this
  have h := (Near.prod hc α).2.2
  have hm : (α.prod fun s e => (X s : MvPowerSeries τ S) ^ e) = monomial α 1 := by
    have := subst_monomial (R := S) (HasSubst.X (S := S) (σ := τ)) α (1 : S)
    rw [subst_self] at this
    simpa using this.symm
  rw [hm] at h
  have h2 : ((α.degree + 1 : ℕ) : ℕ∞) + 1 = ((2 + α.degree : ℕ) : ℕ∞) := by
    push_cast; ring
  exact (ENat.add_le_add_iff_right (by simp)).mp (h2.le.trans h)

end Lead

section Int

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))

theorem isInt_mul {τ : Type} {f g : MvPowerSeries τ C} (hf : MvIsInt v f) (hg : MvIsInt v g) :
    MvIsInt v (f * g) := by
  classical
  intro α
  unfold IsIntV
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun x => 0 ≤ v x)
    (fun a b ha hb => le_trans (le_min ha hb) (v.map_add a b)) (by simp) ?_
  intro p _
  rw [v.map_mul]
  exact add_nonneg (hf _) (hg _)

open Classical in

def intSub (τ : Type) : Subring (MvPowerSeries τ C) where
  carrier := {f | MvIsInt v f}
  mul_mem' := isInt_mul v
  one_mem' := by
    classical
    intro α; unfold IsIntV; rw [coeff_one]; split_ifs <;> simp
  add_mem' := by
    intro f g hf hg α; unfold IsIntV; rw [map_add]
    exact le_trans (le_min (hf α) (hg α)) (v.map_add _ _)
  zero_mem' := by intro α; unfold IsIntV; simp
  neg_mem' := by intro f hf α; unfold IsIntV; rw [map_neg, v.map_neg]; exact hf α

theorem isInt_smul_X {τ : Type} {c : C} (hc : IsIntV v c) (t : τ) :
    MvIsInt v (c • (X t : MvPowerSeries τ C)) := by
  classical
  intro α; unfold IsIntV
  rw [coeff_smul, coeff_X]
  split_ifs
  · rw [mul_one]; exact hc
  · simp

theorem isInt_prod {σ τ : Type} (L : σ → MvPowerSeries τ C) (hL : ∀ s, MvIsInt v (L s))
    (α : σ →₀ ℕ) : MvIsInt v (α.prod fun s k => L s ^ k) := by
  classical
  show _ ∈ intSub v τ
  unfold Finsupp.prod
  exact prod_mem fun s _ => pow_mem (hL s) _

end Int

theorem coeff_single_exp {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
    (G : LogFGL v d) {ex : Fin d → MvPowerSeries (Fin d) C} (h : IsExp G ex) (a b : Fin d) :
    coeff (Finsupp.single b 1) (ex a) = if a = b then 1 else 0 := by
  have e := congrArg (coeff (Finsupp.single b 1)) (h.2 a)
  rw [GlobalTheory.FormalSeries.coeff_single_subst h.1] at e
  simp only [G.lg_lin, smul_eq_mul, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, coeff_X] at e
  rw [e]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Finsupp.single_left_inj one_ne_zero, Ne.symm hab]

theorem depth_le_content : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (κ : Type) [Fintype κ] [DecidableEq κ] (d n : κ → ℕ) (G : ∀ b, LogFGL v (d b))
    (u : ∀ b, Fin (n b) → Fin (d b) → C) (P : MvPolynomial (Σ b, Fin (n b)) C) (D : ℕ),
    P.IsHomogeneous D → (∀ b, IsSatFrame v (u b)) →
      depth G (ι := fun b => Fin (n b)) u P ≤ content v P := by
  intro C _ _ v κ _ _ d n G u P D hP hu
  classical
  choose l hlint hldual using fun b => GlobalTheory.T.exists_integral_dual_frame_of_isSatFrame C v (n b) (d b) (u b) (hu b)
  have hexp : ∀ b, IsExp (G b) (expOf (G b)) := fun b => (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v (d b) (G b)).1
  have hlin0 : ∀ b (e : Fin (d b)), constantCoeff
      (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, Fin (n b)) C)) = 0 := by
    intro b e; simp
  have hlin1 : ∀ b (e : Fin (d b)) (y : Σ b, Fin (n b)), coeff (Finsupp.single y 1)
      (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, Fin (n b)) C)) =
        ∑ a, u b a e * if y = ⟨b, a⟩ then 1 else 0 := by
    intro b e y
    simp only [map_sum, coeff_smul, coeff_X, Finsupp.single_left_inj one_ne_zero, smul_eq_mul]
  set A := expAlong G u with hAdef
  have hA0 : ∀ x, constantCoeff (A x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hlin0 x.1)) (hlin0 x.1)
      ((hexp x.1).1 x.2)
  have hA1 : ∀ x y, coeff (Finsupp.single y 1) (A x) =
      ∑ a, u x.1 a x.2 * if y = ⟨x.1, a⟩ then 1 else 0 := by
    intro x y
    show coeff (Finsupp.single y 1) (subst _ (expOf (G x.1) x.2)) = _
    rw [GlobalTheory.FormalSeries.coeff_single_subst (hlin0 x.1)]
    simp only [coeff_single_exp (G x.1) (hexp x.1), hlin1, smul_eq_mul, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  set Y : (Σ b, Fin (n b)) → MvPowerSeries (Σ b, Fin (n b)) C :=
    fun y => ∑ e, l y.1 y.2 e • A ⟨y.1, e⟩ with hYdef
  have hY : ∀ y, 2 ≤ (Y y - X y).order := by
    intro y
    rw [GlobalTheory.FormalSeries.two_le_order_iff]
    refine ⟨by simp [hYdef, hA0], fun z => ?_⟩
    rw [map_sub, hYdef]
    simp only [map_sum, coeff_smul, hA1, smul_eq_mul, coeff_X,
      Finsupp.single_left_inj one_ne_zero]
    simp_rw [Finset.mul_sum]
    rw [sub_eq_zero]
    have key : ∀ a : Fin (n y.1), ∑ e, l y.1 y.2 e * (u y.1 a e * if z = ⟨y.1, a⟩ then (1 : C) else 0)
        = (if y.2 = a then 1 else 0) * if z = ⟨y.1, a⟩ then 1 else 0 := by
      intro a
      rw [← hldual y.1 y.2 a, Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by ring
    have key2 : ∑ e : Fin (d y.1), ∑ a : Fin (n y.1),
        l y.1 y.2 e * (u y.1 a e * if z = ⟨y.1, a⟩ then (1 : C) else 0) = if z = y then 1 else 0 := by
      rw [Finset.sum_comm]
      simp_rw [key, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact key2
  have hAs : HasSubst A := hasSubst_of_constantCoeff_zero hA0
  unfold content
  refine le_iInf₂ fun α hα => ?_
  set L : (Σ b, Fin (n b)) → MvPowerSeries (Σ b, Fin (d b)) C :=
    fun y => ∑ e, l y.1 y.2 e • X ⟨y.1, e⟩ with hLdef
  have hLint : ∀ y, MvIsInt v (L y) := fun y =>
    (intSub v _).sum_mem fun e _ => isInt_smul_X v (hlint y.1 y.2 e) _
  set f := α.prod fun y k => L y ^ k with hfdef
  have hfint : MvIsInt v f := isInt_prod v L hLint α
  have hsub : subst A f = α.prod fun y k => Y y ^ k := by
    rw [hfdef, ← coe_substAlgHom hAs, map_finsuppProd]
    simp only [map_pow, hLdef, hYdef, map_sum, map_smul, substAlgHom_X]
  have hord := lead_prod Y hY α
  rw [← hsub] at hord
  have hdeg : ∀ β ∈ P.support, β.degree = D := fun β hβ => by
    have := hP (MvPolynomial.mem_support_iff.mp hβ)
    rw [← this, Finsupp.degree_eq_weight_one]; rfl
  have hval : derivAt0 P (subst A f) = P.coeff α * mfact α := by
    unfold derivAt0
    rw [Finset.sum_eq_single α]
    · rw [GlobalTheory.FormalSeries.coeff_eq_of_le_order_sub hord (Nat.lt_succ_self _),
        coeff_monomial_same, mul_one]
    · intro β hβ hne
      rw [GlobalTheory.FormalSeries.coeff_eq_of_le_order_sub hord
        (by rw [hdeg β hβ, ← hdeg α hα]; exact Nat.lt_succ_self _), coeff_monomial,
        if_neg hne, mul_zero]
    · intro h; exact absurd hα h
  unfold depth
  refine (iInf_le _ ⟨f, hfint⟩).trans (le_of_eq ?_)
  rw [← hAdef, hval]

end

end GlobalTheory.FGDepth.DepthLeContent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthRestrictColumns
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

theorem coeff_subst_extend_zero {σ τ : Type} [Finite σ] {j : τ → σ} (hj : Function.Injective j)
    (g : MvPowerSeries σ C) (α : τ →₀ ℕ) :
    coeff α (subst (Function.extend j (X : τ → MvPowerSeries τ C) 0) g) =
      coeff (Finsupp.mapDomain j α) g := by
  classical
  have hc : ∀ s, constantCoeff (Function.extend j (X : τ → MvPowerSeries τ C) 0 s) = 0 := by
    intro s
    rw [Function.extend_def]
    split_ifs <;> simp
  have ha := hasSubst_of_constantCoeff_zero hc
  rw [coeff_subst ha, finsum_eq_single _ (Finsupp.mapDomain j α)]
  · rw [Finsupp.prod_mapDomain_index_inj hj]
    simp only [hj.extend_apply]
    rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_same, smul_eq_mul, mul_one]
  · intro D hD
    by_cases hsupp : ↑D.support ⊆ Set.range j
    · obtain ⟨β, rfl⟩ : ∃ β, Finsupp.mapDomain j β = D :=
        ⟨_, Finsupp.mapDomain_comapDomain j hj D hsupp⟩
      rw [Finsupp.prod_mapDomain_index_inj hj]
      simp only [hj.extend_apply]
      rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_ne, smul_zero]
      rintro rfl
      exact hD rfl
    · obtain ⟨s, hs, hsr⟩ := Set.not_subset.mp hsupp
      have hz : Function.extend j (X : τ → MvPowerSeries τ C) 0 s = 0 :=
        Function.extend_apply' _ _ _ (fun h => hsr h)
      have hs' : D s ≠ 0 := Finsupp.mem_support_iff.mp hs
      rw [Finsupp.prod, Finset.prod_eq_zero hs (by simp [hz, hs']), map_zero, smul_zero]

theorem subst_zero_of_constantCoeff {σ τ : Type} [Finite σ] (h : MvPowerSeries σ C)
    (h0 : constantCoeff h = 0) : subst (0 : σ → MvPowerSeries τ C) h = 0 := by
  exact subst_zero_of_constantCoeff_zero h0

theorem subst_sum_smul_X {σ τ ι : Type} [Fintype ι] {s : σ → MvPowerSeries τ C} (hs : HasSubst s)
    (c : ι → C) (k : ι → σ) :
    subst s (∑ a, c a • (X (k a) : MvPowerSeries σ C)) = ∑ a, c a • s (k a) := by
  rw [← coe_substAlgHom hs, map_sum]
  simp only [map_smul, substAlgHom_X]

end

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C] [CharZero C] {v : AddValuation C (WithTop ℝ)}

theorem constantCoeff_expAlong {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (x : Σ b, Fin (d b)) :
    constantCoeff (expAlong G u x) = 0 := by
  have hE := (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v (d x.1) (G x.1)).1
  unfold IsExp at hE
  simp only [expAlong]
  refine constantCoeff_subst_eq_zero ?_ ?_ (hE.1 x.2)
  · exact hasSubst_of_constantCoeff_zero (fun e => by simp [MvPowerSeries.smul_eq_C_mul])
  · intro e
    simp [MvPowerSeries.smul_eq_C_mul]

theorem depth_rename (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ)
    (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
    (u : ∀ b, ι b → Fin (d b) → C) (κ' : Type) [Fintype κ'] [DecidableEq κ'] (e : κ' ↪ κ)
    (P : MvPolynomial (Σ b : κ', ι (e b)) C) :
    depth G u (MvPolynomial.rename (fun x => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) =
      depth (fun b => G (e b)) (fun b => u (e b)) P := by
  have hinj : ∀ (β : κ → Type),
      Function.Injective (fun x : (Σ b : κ', β (e b)) => (⟨e x.1, x.2⟩ : Σ b, β b)) := by
    intro β
    rintro ⟨a, x⟩ ⟨c, y⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := e.injective h1
    rw [heq_eq_eq] at h2
    rw [h2]
  have hjt : Function.Injective (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) := hinj ι
  have hjv : Function.Injective (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) := hinj (fun b => Fin (d b))
  have hcc : ∀ {σ τ : Type} (j : τ → σ) (s : σ),
      constantCoeff (Function.extend j (X : τ → MvPowerSeries τ C) 0 s) = 0 := by
    intro σ τ j s
    classical
    rw [Function.extend_def]
    split_ifs <;> simp
  have hE : ∀ b (k : Fin (d b)), constantCoeff (expOf (G b) k) = 0 := by
    intro b k
    have h := (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v (d b) (G b)).1
    unfold IsExp at h
    exact h.1 k
  have hA : HasSubst (expAlong G u) := hasSubst_of_constantCoeff_zero (constantCoeff_expAlong G u)
  have hA' : HasSubst (expAlong (fun b => G (e b)) (fun b => u (e b))) :=
    hasSubst_of_constantCoeff_zero (constantCoeff_expAlong _ _)
  have hRt : HasSubst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) :=
    hasSubst_of_constantCoeff_zero (hcc _)
  have hRv : HasSubst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) :=
    hasSubst_of_constantCoeff_zero (hcc _)
  have hin : ∀ b, HasSubst (fun e' : Fin (d b) =>
      ∑ a, u b a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) := fun b =>
    hasSubst_of_constantCoeff_zero (fun e' => by simp [MvPowerSeries.smul_eq_C_mul])

  have K1 : ∀ F : MvPowerSeries (Σ b, ι b) C,
      derivAt0 (MvPolynomial.rename (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) F =
        derivAt0 P (subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) F) := by
    intro F
    unfold derivAt0
    rw [MvPolynomial.support_rename_of_injective hjt,
      Finset.sum_image (Finsupp.mapDomain_injective hjt).injOn]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hm : (mfact (Finsupp.mapDomain (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) α) : C) = mfact α := by
      unfold mfact
      exact Finsupp.prod_mapDomain_index_inj hjt
    rw [MvPolynomial.coeff_rename_mapDomain _ hjt, coeff_subst_extend_zero hjt, hm]

  have K2 : ∀ x : Σ b, Fin (d b),
      subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) (expAlong G u x) =
        subst (expAlong (fun b => G (e b)) (fun b => u (e b))) (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 x) := by
    rintro ⟨b, k⟩
    by_cases hb : ∃ b', e b' = b
    · obtain ⟨b', rfl⟩ := hb
      have h1 : Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 ⟨e b', k⟩ = X ⟨b', k⟩ := hjv.extend_apply _ _ ⟨b', k⟩
      have h2 : ∀ a, Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0 ⟨e b', a⟩ = X ⟨b', a⟩ :=
        fun a => hjt.extend_apply _ _ ⟨b', a⟩
      rw [h1, subst_X hA']
      simp only [expAlong]
      rw [subst_comp_subst_apply (hin (e b')) hRt]
      congr 1
      funext e'
      rw [subst_sum_smul_X hRt]
      simp only [h2]
    · have h1 : Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 ⟨b, k⟩ = 0 :=
        Function.extend_apply' _ _ _ (by
          rintro ⟨⟨b', k'⟩, h⟩
          exact hb ⟨b', congrArg Sigma.fst h⟩)
      have h2 : ∀ a, Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0 ⟨b, a⟩ = 0 := fun a =>
        Function.extend_apply' _ _ _ (by
          rintro ⟨⟨b', a'⟩, h⟩
          exact hb ⟨b', congrArg Sigma.fst h⟩)
      rw [h1, ← coe_substAlgHom hA', map_zero]
      simp only [expAlong]
      rw [subst_comp_subst_apply (hin b) hRt]
      have h3 : (fun e' : Fin (d b) => subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0)
          (∑ a, u b a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C))) = 0 := by
        funext e'
        rw [subst_sum_smul_X hRt]
        simp [h2]
      rw [h3]
      exact subst_zero_of_constantCoeff _ (hE b k)
  have K : ∀ f : MvPowerSeries (Σ b, Fin (d b)) C,
      derivAt0 (MvPolynomial.rename (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) (subst (expAlong G u) f) =
        derivAt0 P (subst (expAlong (fun b => G (e b)) (fun b => u (e b))) (subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f)) := by
    intro f
    rw [K1, subst_comp_subst_apply hA hRt, subst_comp_subst_apply hRv hA']
    exact congrArg (fun F => derivAt0 P (subst F f)) (funext K2)

  have Rint : ∀ f : MvPowerSeries (Σ b, Fin (d b)) C, MvIsInt v f →
      MvIsInt v (subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f) := by
    intro f hf α
    rw [coeff_subst_extend_zero hjv]
    exact hf _
  have Rsec : ∀ g : MvPowerSeries (Σ b : κ', Fin (d (e b))) C, MvIsInt v g →
      ∃ f, MvIsInt v f ∧ subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f = g := by
    intro g hg
    classical
    refine ⟨@id (MvPowerSeries (Σ b, Fin (d b)) C)
      (Function.extend (Finsupp.mapDomain (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b)))) (fun α => coeff α g) 0), ?_, ?_⟩
    · intro β
      show IsIntV v (Function.extend (Finsupp.mapDomain (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b)))) (fun α => coeff α g) 0 β)
      rw [Function.extend_def]
      split_ifs with h
      · exact hg _
      · simp [IsIntV]
    · ext α
      rw [coeff_subst_extend_zero hjv]
      exact (Finsupp.mapDomain_injective hjv).extend_apply _ _ α
  unfold depth
  apply le_antisymm
  · refine le_iInf fun g => ?_
    obtain ⟨f, hf, hfg⟩ := Rsec g.1 g.2
    refine (iInf_le _ ⟨f, hf⟩).trans_eq ?_
    dsimp only
    rw [K f, hfg]
  · refine le_iInf fun f => ?_
    refine (iInf_le _ ⟨subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f.1, Rint f.1 f.2⟩).trans_eq ?_
    dsimp only
    rw [K f.1]

end

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem depth_restrict : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (κ' : Type) [Fintype κ'] [DecidableEq κ'] (e : κ' ↪ κ) (P : MvPolynomial (Σ b : κ', ι (e b)) C), depth G u (MvPolynomial.rename (fun x => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) = depth (fun b => G (e b)) (fun b => u (e b)) P := by
  intro C _ _ v κ _ _ d G ι _ _ u κ' _ _ e P
  exact depth_rename κ d G ι u κ' e P

end GlobalTheory.FGDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexPointNormLtOfNotIsUnitStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_point_norm_lt_of_not_isUnit' : ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] (σ : K →+* ℂ) (n : ℕ) (w : Fin n → B) (u q : B), ¬ IsUnit u → q ≠ 0 → ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ φ : B →+* ℂ, φ.comp (algebraMap K B) = σ ∧ φ q ≠ 0 ∧ ‖φ u‖ < ε ∧ ∀ i, ‖φ (w i)‖ ≤ M := by
  first | exact @GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit | exact GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit | (intros; apply GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPosStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_discreteSpace_cocycle_vanishing_pos : ∀ (R : Type) [CommRing R] (F : PSh) (I : Cx R) (n : ℤ) (x : CohomologyClass ((chains R).obj (disc.obj F)) I n), ∃ α : Cocycle ((chains R).obj (disc.obj F)) I n, CohomologyClass.mk α = x ∧ ∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0 := by
  first | (exact @GlobalTheory.EtC.discRep) | (exact GlobalTheory.EtC.discRep) | (intros; apply GlobalTheory.EtC.discRep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueFunctionsAffineOpenFromPairs
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem pair_glue : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R')
    (W : X'.affineOpens) (k : ∀ p : Pair φ, p.1.1 ≤ W → (OAff s').obj (op p.1.1)),
    (∀ (p q : Pair φ) (hp : p.1.1 ≤ W) (hq : q.1.1 ≤ W) (hqp : q ≤ p),
      mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (k p hp) = k q hq) →
    ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op G = k p hp := by
  intro R' _ X X' φ s' W k hk
  let U : {p : Pair φ // p.1.1 ≤ W} → X'.Opens := fun i ↦ i.1.1.1.1
  let sf : ∀ i : {p : Pair φ // p.1.1 ≤ W}, ToType (X'.sheaf.1.obj (op (U i))) := fun i ↦ k i.1 i.2

  have key : ∀ (i : {p : Pair φ // p.1.1 ≤ W}) (r : Pair φ) (hr : r ≤ i.1) {x : X'} (hx : x ∈ r.1.1.1),
      X'.presheaf.germ (U i) x (Pair.le_fst hr hx) (sf i) =
        X'.presheaf.germ r.1.1.1 x hx (k r ((Pair.le_fst hr).trans i.2)) := by
    intro i r hr x hx
    rw [← hk i.1 r i.2 ((Pair.le_fst hr).trans i.2) hr]
    exact (X'.presheaf.germ_res_apply (homOfLE (show r.1.1.1 ≤ U i from Pair.le_fst hr)) x hx _).symm
  have hcomp : TopCat.Presheaf.IsCompatible X'.sheaf.1 U sf := by
    intro i j
    refine TopCat.Presheaf.section_ext X'.sheaf _ _ _ fun x hx ↦ ?_
    obtain ⟨r, hri, hrj, hxr⟩ := Pair.exists_le_le φ i.1 j.1 hx
    change X'.presheaf.germ _ x hx (X'.presheaf.map _ (sf i)) = X'.presheaf.germ _ x hx (X'.presheaf.map _ (sf j))
    exact ((X'.presheaf.germ_res_apply (TopologicalSpace.Opens.infLELeft (U i) (U j)) x hx (sf i)).trans
      (key i r hri hxr)).trans ((X'.presheaf.germ_res_apply (TopologicalSpace.Opens.infLERight (U i) (U j))
        x hx (sf j)).trans (key j r hrj hxr)).symm
  have hcov : W.1 ≤ iSup U := fun x hx ↦ by
    obtain ⟨p, hp, hxp⟩ := Pair.exists_le φ W hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨G, hG, -⟩ := X'.sheaf.existsUnique_gluing' U W.1 (fun i ↦ homOfLE i.2) hcov sf hcomp
  exact ⟨G, fun p hp ↦ hG ⟨p, hp⟩⟩

end GlobalTheory.CechDR
end

