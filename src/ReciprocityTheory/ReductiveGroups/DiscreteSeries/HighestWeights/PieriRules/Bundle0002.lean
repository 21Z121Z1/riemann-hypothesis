import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensRepA
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

section Gen

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] [DecidableEq ι]

def piIn (i : ι) : V →L[ℂ] PiLp 2 (fun _ : ι => V) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => V)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : ι => V) i

theorem piIn_apply (i : ι) (v : V) (j : ι) : piIn i v j = Pi.single (M := fun _ : ι => V) i v j := rfl

theorem piIn_same (i : ι) (v : V) : piIn i v i = v :=
  (piIn_apply i v i).trans (Pi.single_eq_same (M := fun _ : ι => V) i v)

theorem piIn_ne {i j : ι} (h : j ≠ i) (v : V) : piIn i v j = 0 :=
  (piIn_apply i v j).trans (Pi.single_eq_of_ne (M := fun _ : ι => V) h v)

def tensL (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) : PiLp 2 (fun _ : ι => V) →L[ℂ] PiLp 2 (fun _ : ι => V) :=
  ∑ i, ∑ j, m i j • (piIn i ∘L S ∘L PiLp.proj 2 (fun _ : ι => V) j)

@[simp] theorem tensL_apply (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensL m S x i = ∑ j, m i j • S (x j) := by
  simp only [tensL, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    PiLp.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp only [piIn_same]
  · intro k _ hk
    simp only [piIn_ne (Ne.symm hk), smul_zero, Finset.sum_const_zero]
  · simp

theorem tensL_mul (m m' : Matrix ι ι ℂ) (S S' : V →L[ℂ] V) :
    tensL (m * m') (S * S') = tensL m S * tensL m' S' := by
  refine ContinuousLinearMap.ext fun x => PiLp.ext fun i => ?_
  have hSS : ∀ v : V, (S * S') v = S (S' v) := fun v => rfl
  show tensL (m * m') (S * S') x i = tensL m S (tensL m' S' x) i
  simp only [tensL_apply, hSS, Matrix.mul_apply, map_sum, map_smul,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem tensL_one : tensL (1 : Matrix ι ι ℂ) (1 : V →L[ℂ] V) = 1 := by
  refine ContinuousLinearMap.ext fun x => PiLp.ext fun i => ?_
  simp [Matrix.one_apply, ite_smul]

theorem tensL_star [CompleteSpace V] (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    star (tensL m S) = tensL (star m) (star S) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, tensL_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left, starRingEnd_apply, star_star]
  exact Finset.sum_comm

theorem tensL_mem_unitary [CompleteSpace V] {m : Matrix ι ι ℂ} {S : V →L[ℂ] V}
    (hm : m ∈ unitary (Matrix ι ι ℂ)) (hS : S ∈ unitary (V →L[ℂ] V)) :
    tensL m S ∈ unitary (PiLp 2 (fun _ : ι => V) →L[ℂ] PiLp 2 (fun _ : ι => V)) := by
  rw [Unitary.mem_iff] at hm hS ⊢
  rw [tensL_star, ← tensL_mul, ← tensL_mul, hm.1, hm.2, hS.1, hS.2, tensL_one]
  exact ⟨rfl, rfl⟩

theorem continuous_tensL {X : Type*} [TopologicalSpace X] {m : X → Matrix ι ι ℂ} {S : X → V →L[ℂ] V}
    (hm : Continuous m) (hS : Continuous S) : Continuous fun x => tensL (m x) (S x) := by
  simp only [tensL]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (hm.matrix_elem i j).smul (continuous_const.clm_comp (hS.clm_comp continuous_const))

theorem hasDerivAt_tensL {m : ℝ → Matrix ι ι ℂ} {m' : Matrix ι ι ℂ} {S : ℝ → V →L[ℂ] V}
    {S' : V →L[ℂ] V} {t₀ : ℝ} (hm : ∀ i j, HasDerivAt (fun t => m t i j) (m' i j) t₀)
    (hS : HasDerivAt S S' t₀) :
    HasDerivAt (fun t => tensL (m t) (S t)) (tensL m' (S t₀) + tensL (m t₀) S') t₀ := by
  have h : ∀ i j, HasDerivAt
      (fun t => m t i j • (piIn i ∘L S t ∘L PiLp.proj 2 (fun _ : ι => V) j))
      (m t₀ i j • (piIn i ∘L S' ∘L PiLp.proj 2 (fun _ : ι => V) j) +
        m' i j • (piIn i ∘L S t₀ ∘L PiLp.proj 2 (fun _ : ι => V) j)) t₀ := by
    intro i j
    let L : (V →L[ℂ] V) →L[ℂ] (PiLp 2 (fun _ : ι => V) →L[ℂ] PiLp 2 (fun _ : ι => V)) :=
      (ContinuousLinearMap.compL ℂ (PiLp 2 (fun _ : ι => V)) V (PiLp 2 (fun _ : ι => V)) (piIn i)).comp
        ((ContinuousLinearMap.compL ℂ (PiLp 2 (fun _ : ι => V)) V V).flip
          (PiLp.proj 2 (fun _ : ι => V) j))
    have hc : HasDerivAt (fun t => L (S t)) (L S') t₀ :=
      (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t₀ hS
    exact (hm i j).smul hc
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ => h i j
  refine hs.congr_deriv ?_
  simp only [tensL, Finset.sum_add_distrib]
  exact add_comm _ _

variable {G : Type*} [Monoid G] [CompleteSpace V]

def tensHom (ρ : G →* unitary (Matrix ι ι ℂ)) (σ : G →* unitary (V →L[ℂ] V)) :
    G →* unitary (PiLp 2 (fun _ : ι => V) →L[ℂ] PiLp 2 (fun _ : ι => V)) where
  toFun g := ⟨tensL ((ρ g : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) ((σ g : unitary (V →L[ℂ] V)) : V →L[ℂ] V),
    tensL_mem_unitary (ρ g).2 (σ g).2⟩
  map_one' := Subtype.ext (by simp only [map_one, OneMemClass.coe_one, tensL_one])
  map_mul' g h := Subtype.ext (by simp only [map_mul, Submonoid.coe_mul, tensL_mul])

theorem continuous_tensHom [TopologicalSpace G] {ρ : G →* unitary (Matrix ι ι ℂ)}
    {σ : G →* unitary (V →L[ℂ] V)}
    (hρ : Continuous (fun g : G => ((ρ g : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ))) (hσ : Continuous σ) :
    Continuous (tensHom ρ σ) :=
  continuous_induced_rng.2 (continuous_tensL hρ (continuous_subtype_val.comp hσ))

end Gen

section KT

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
  (ρ : KG ε →* unitary (Matrix ι ι ℂ))

def tensOp (k : KG ε) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V) :=
  tensL ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) (T.op k)

theorem tensOp_eq (k : KG ε) :
    tensOp T ρ k = tensL ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) (T.op k) := rfl

@[simp] theorem tensOp_apply (k : KG ε) (x : PiLp 2 (fun _ : ι => T.V)) (i : ι) :
    tensOp T ρ k x i = ∑ j, ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j • T.op k (x j) :=
  tensL_apply _ _ _ _

def tensTau : KG ε →* unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) :=
  tensHom ρ T.τ

@[simp] theorem tensTau_coe (k : KG ε) :
    ((tensTau T ρ k : unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V))) :
      PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) = tensOp T ρ k := rfl

theorem tensTau_cont (h : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ))) :
    Continuous (tensTau T ρ) :=
  continuous_tensHom h T.cont

example (τ : KG ε →* unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
    (hc : Continuous τ)
    (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t : ℝ => ((τ (γ t) : unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ]
        PiLp 2 (fun _ : ι => T.V))) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
        (D X) 0)
    (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hu : ∀ a b, ((D (Matrix.single a b 1) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) :
        Module.End ℂ (PiLp 2 (fun _ : ι => T.V))) =
          tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) a b) :
    (⟨PiLp 2 (fun _ : ι => T.V), τ, hc, D, hd⟩ : KRep ε).units =
      tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) := by
  funext a b
  exact hu a b

end KT

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylPos
section
open Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS

private lemma weylPos_above_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    (univ.filter fun c => b < c ∧ ε c = ε b).card + 1 ≤ (univ.filter fun c => a < c ∧ ε c = ε a).card := by
  have hsub : (univ.filter fun c => b < c ∧ ε c = ε b) ⊆ (univ.filter fun c => a < c ∧ ε c = ε a) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨hab.trans hc.1, hc.2.trans he.symm⟩
  have hss : (univ.filter fun c => b < c ∧ ε c = ε b) ⊂ (univ.filter fun c => a < c ∧ ε c = ε a) := by
    rw [Finset.ssubset_iff_of_subset hsub]
    exact ⟨b, by simp [hab, he], by simp⟩
  exact Finset.card_lt_card hss

private lemma weylPos_below_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    (univ.filter fun c => c < a ∧ ε c = ε a).card + 1 ≤ (univ.filter fun c => c < b ∧ ε c = ε b).card := by
  have hsub : (univ.filter fun c => c < a ∧ ε c = ε a) ⊆ (univ.filter fun c => c < b ∧ ε c = ε b) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨hc.1.trans hab, hc.2.trans he⟩
  have hss : (univ.filter fun c => c < a ∧ ε c = ε a) ⊂ (univ.filter fun c => c < b ∧ ε c = ε b) := by
    rw [Finset.ssubset_iff_of_subset hsub]
    exact ⟨a, by simp [hab, he], by simp⟩
  exact Finset.card_lt_card hss

theorem rhoC_sub_ge_one {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    1 ≤ rhoC ε a - rhoC ε b := by
  have h1 := weylPos_above_lt ε hab he
  have h2 := weylPos_below_lt ε hab he
  have h1' : ((univ.filter fun c => b < c ∧ ε c = ε b).card : ℝ) + 1 ≤
      ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) := by exact_mod_cast h1
  have h2' : ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) + 1 ≤
      ((univ.filter fun c => c < b ∧ ε c = ε b).card : ℝ) := by exact_mod_cast h2
  unfold rhoC
  linarith

theorem rhoC_consec {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b)
    (hc : ∀ c, a < c → c < b → ε c ≠ ε a) : rhoC ε a - rhoC ε b = 1 := by
  have h1 := weylPos_above_lt ε hab he
  have h2 := weylPos_below_lt ε hab he
  have h3 : (univ.filter fun c => a < c ∧ ε c = ε a).card ≤
      (univ.filter fun c => b < c ∧ ε c = ε b).card + 1 := by
    refine (Finset.card_le_card ?_).trans (Finset.card_insert_le b _)
    intro c hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hc' ⊢
    rcases lt_trichotomy c b with h | h | h
    · exact absurd hc'.2 (hc c hc'.1 h)
    · exact Or.inl h
    · exact Or.inr ⟨h, hc'.2.trans he⟩
  have h4 : (univ.filter fun c => c < b ∧ ε c = ε b).card ≤
      (univ.filter fun c => c < a ∧ ε c = ε a).card + 1 := by
    refine (Finset.card_le_card ?_).trans (Finset.card_insert_le a _)
    intro c hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hc' ⊢
    rcases lt_trichotomy c a with h | h | h
    · exact Or.inr ⟨h, hc'.2.trans he.symm⟩
    · exact Or.inl h
    · exact absurd (hc'.2.trans he.symm) (hc c h hc'.1)
  have e1 : ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) =
      ((univ.filter fun c => b < c ∧ ε c = ε b).card : ℝ) + 1 := by
    exact_mod_cast le_antisymm h3 h1
  have e2 : ((univ.filter fun c => c < b ∧ ε c = ε b).card : ℝ) =
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) + 1 := by
    exact_mod_cast le_antisymm h4 h2
  unfold rhoC
  rw [e1, e2]
  ring

theorem weylPos : WeylPosStatement := by
  intro n ε μ hμ
  unfold weylK
  refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have hr := rhoC_sub_ge_one ε hb.1 hb.2
  have hd := hμ a b hb.1 hb.2
  apply div_pos
  · simp only [Pi.add_apply]
    linarith
  · linarith

end ReciprocityTheory.ChartRestriction.DS.HW
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylRatio
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem weylRatio_rhoC_sub_ge_one {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b)
    (he : ε a = ε b) : 1 ≤ rhoC ε a - rhoC ε b := by
  have h1 : (univ.filter fun x => b < x ∧ ε x = ε b).card + 1 ≤
      (univ.filter fun x => a < x ∧ ε x = ε a).card := by
    apply Nat.succ_le_of_lt
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨b, by simp [hab, he], by simp⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hab.trans hx.1, hx.2.trans he.symm⟩
  have h2 : (univ.filter fun x => x < a ∧ ε x = ε a).card + 1 ≤
      (univ.filter fun x => x < b ∧ ε x = ε b).card := by
    apply Nat.succ_le_of_lt
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨a, by simp [hab, he], by simp⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hx.1.trans hab, hx.2.trans he⟩
  have h1' : ((univ.filter fun x => b < x ∧ ε x = ε b).card : ℝ) + 1 ≤
      ((univ.filter fun x => a < x ∧ ε x = ε a).card : ℝ) := by exact_mod_cast h1
  have h2' : ((univ.filter fun x => x < a ∧ ε x = ε a).card : ℝ) + 1 ≤
      ((univ.filter fun x => x < b ∧ ε x = ε b).card : ℝ) := by exact_mod_cast h2
  simp only [rhoC]
  linarith

theorem weylRatio_prodW {n : ℕ} (ε : Fin n → Bool) (s : Fin n) (h : Fin n → ℝ) :
    ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ ε a = ε b),
        (if b = s then h a else if a = s then h b else 1) =
      ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), h b := by
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ s)]
  have h1 : ∏ b ∈ univ.filter (fun b => s < b ∧ ε s = ε b),
      (if b = s then h s else if s = s then h b else 1) =
        ∏ b ∈ univ.filter (fun b => s < b ∧ ε s = ε b), h b :=
    Finset.prod_congr rfl fun b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp [ne_of_gt hb.1]
  have h2 : ∏ a ∈ univ.erase s, ∏ b ∈ univ.filter (fun b => a < b ∧ ε a = ε b),
      (if b = s then h a else if a = s then h b else 1) =
        ∏ a ∈ univ.filter (fun a => a < s ∧ ε a = ε s), h a := by
    rw [Finset.prod_filter,
      ← Finset.mul_prod_erase univ (fun a => if a < s ∧ ε a = ε s then h a else 1) (Finset.mem_univ s)]
    simp only [lt_self_iff_false, false_and, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun a ha => ?_
    have has : a ≠ s := Finset.ne_of_mem_erase ha
    simp only [has, ↓reduceIte]
    rw [Finset.prod_ite_eq']
    simp [Finset.mem_filter]
  rw [h1, h2, ← Finset.prod_union]
  · congr 1
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨ne_of_gt h1, h2.symm⟩
      · exact ⟨ne_of_lt h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases lt_or_gt_of_ne h1 with h | h
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl ⟨h, h2.symm⟩
  · exact Finset.disjoint_filter.mpr fun b _ h1 h2 => lt_asymm h1.1 h2.1

theorem weylK_shift_mul {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (s : Fin n) (c : ℝ) :
    weylK ε (Λ + Pi.single s c) *
        ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), ((Λ + rhoC ε) s - (Λ + rhoC ε) b) =
      weylK ε Λ *
        ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), ((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) := by
  rw [← weylRatio_prodW ε s (fun b => (Λ + rhoC ε) s - (Λ + rhoC ε) b),
    ← weylRatio_prodW ε s (fun b => (Λ + rhoC ε) s - (Λ + rhoC ε) b + c)]
  simp only [weylK]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have hab : a ≠ b := ne_of_lt hb.1
  by_cases hbs : b = s
  · subst hbs
    simp only [Pi.add_apply, Pi.single_apply, hab, ↓reduceIte]
    ring
  · by_cases has : a = s
    · subst has
      simp only [Pi.add_apply, Pi.single_apply, hbs, ↓reduceIte]
      ring
    · simp only [Pi.add_apply, Pi.single_apply, hbs, has, ↓reduceIte]
      ring

theorem weylRatio_ell_ne {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) {s b : Fin n}
    (hbs : b ≠ s) (he : ε b = ε s) : (Λ + rhoC ε) s - (Λ + rhoC ε) b ≠ 0 := by
  intro h
  simp only [Pi.add_apply] at h
  rcases lt_or_gt_of_ne hbs with hlt | hlt
  · have h1 := weylRatio_rhoC_sub_ge_one ε hlt he
    have h2 := hΛ b s hlt he
    linarith
  · have h1 := weylRatio_rhoC_sub_ge_one ε hlt he.symm
    have h2 := hΛ s b hlt he.symm
    linarith

theorem weylRatio_prod_ne {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (s : Fin n) :
    ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), ((Λ + rhoC ε) s - (Λ + rhoC ε) b) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun b hb => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact weylRatio_ell_ne ε Λ hΛ hb.1 hb.2

theorem weylK_shift {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (s : Fin n) (c : ℝ) :
    weylK ε (Λ + Pi.single s c) =
      weylK ε Λ * ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
        (((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) / ((Λ + rhoC ε) s - (Λ + rhoC ε) b)) := by
  rw [Finset.prod_div_distrib, ← mul_div_assoc, eq_div_iff (weylRatio_prod_ne ε Λ hΛ s)]
  exact weylK_shift_mul ε Λ s c

theorem weylK_add_smul_single {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (s : Fin n)
    (c : ℝ) :
    weylK ε (Λ + c • (Pi.single s (1 : ℝ) : Fin n → ℝ)) = weylK ε Λ *
      ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
        ((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) / ((Λ + rhoC ε) s - (Λ + rhoC ε) b) := by
  have h : c • (Pi.single s (1 : ℝ) : Fin n → ℝ) = Pi.single s c := by
    ext x
    by_cases hx : x = s <;> simp [hx]
  rw [h]
  exact weylK_shift ε Λ hΛ s c

theorem weylK_two {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) {i j : Fin n}
    (hij : ε i ≠ ε j) :
    weylK ε (Λ + (Pi.single i 1 - Pi.single j 1)) =
      weylK ε Λ *
        (∏ b ∈ univ.filter (fun b => b ≠ i ∧ ε b = ε i),
          (((Λ + rhoC ε) i - (Λ + rhoC ε) b + 1) / ((Λ + rhoC ε) i - (Λ + rhoC ε) b))) *
        ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
          (((Λ + rhoC ε) j - (Λ + rhoC ε) b - 1) / ((Λ + rhoC ε) j - (Λ + rhoC ε) b)) := by
  have hji : j ≠ i := fun h => hij (by rw [h])
  have hF : ∀ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
      (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) j - (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) b =
        (Λ + rhoC ε) j - (Λ + rhoC ε) b := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hbi : b ≠ i := fun h => hij (by rw [← h, hb.2])
    simp only [Pi.add_apply, Pi.single_apply, hji, hbi, ↓reduceIte]
    ring
  have hP0 : ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
      ((Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) j - (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) b) =
        ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j), ((Λ + rhoC ε) j - (Λ + rhoC ε) b) :=
    Finset.prod_congr rfl hF
  have hP1 : ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
      ((Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) j - (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) b + -1) =
        ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j), ((Λ + rhoC ε) j - (Λ + rhoC ε) b - 1) :=
    Finset.prod_congr rfl fun b hb => by rw [hF b hb]; ring
  have hmul := weylK_shift_mul ε (Λ + Pi.single i 1) j (-1)
  rw [hP0, hP1, weylK_shift ε Λ hΛ i 1] at hmul
  have hΛe : Λ + (Pi.single i 1 - Pi.single j 1) = Λ + Pi.single i 1 + Pi.single j (-1) := by
    rw [sub_eq_add_neg, ← Pi.single_neg, add_assoc]
  rw [hΛe, Finset.prod_div_distrib (s := univ.filter (fun b => b ≠ j ∧ ε b = ε j)), ← mul_div_assoc, eq_div_iff (weylRatio_prod_ne ε Λ hΛ j), hmul]

theorem weylK_add_single_sub_single {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ)
    (i j : Fin n) (hij : ε i ≠ ε j) :
    weylK ε (Λ + ((Pi.single i (1 : ℝ) : Fin n → ℝ) - Pi.single j 1)) = weylK ε Λ *
      (∏ b ∈ univ.filter (fun b => b ≠ i ∧ ε b = ε i),
        ((Λ + rhoC ε) i - (Λ + rhoC ε) b + 1) / ((Λ + rhoC ε) i - (Λ + rhoC ε) b)) *
      (∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
        ((Λ + rhoC ε) j - (Λ + rhoC ε) b - 1) / ((Λ + rhoC ε) j - (Λ + rhoC ε) b)) :=
  weylK_two ε Λ hΛ hij

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

