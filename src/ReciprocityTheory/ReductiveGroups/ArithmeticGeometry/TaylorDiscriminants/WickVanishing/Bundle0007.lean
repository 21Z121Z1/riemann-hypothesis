import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0006
import Mathlib
import ReciprocityTheory.ReductiveGroups.Models.FiniteGeneration.FiniteGenerationProofs.Bundle0001

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ETGMulQ
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen

open ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {S : Type} [CommRing S] {ι : Type}
  (D : ι → S → S) (κ : k →+* S)
  (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
  (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)

def TG (w : List ι) (A : S) : S := w.foldr (fun l g => D l g) A

include hadd in
theorem D_zero (l : ι) : D l 0 = 0 := by
  simpa using hadd l 0 0

include hadd in
theorem D_list_sum (l : ι) (L : List S) : D l L.sum = (L.map (D l)).sum := by
  induction L with
  | nil => simpa using D_zero D hadd l
  | cons a L ih => simp [hadd, ih]

theorem TG_append (w w' : List ι) (A : S) : TG D (w ++ w') A = TG D w (TG D w' A) := by
  simp only [TG, List.foldr_append]

include hadd in
theorem TG_add (w : List ι) (A B : S) : TG D w (A + B) = TG D w A + TG D w B := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    show D l (TG D w (A + B)) = D l (TG D w A) + D l (TG D w B)
    rw [ih, hadd]

include hadd hmul in
theorem TG_mul (w : List ι) (A B : S) :
    TG D w (A * B) = ((splits w).map (fun p => TG D p.1 A * TG D p.2 B)).sum := by
  induction w with
  | nil => simp [TG, splits]
  | cons l w ih =>
    have e : ∀ (v : List ι) (X : S), TG D (l :: v) X = D l (TG D v X) := fun _ _ => rfl
    rw [e, ih, D_list_sum D hadd]
    simp only [splits, List.map_append, List.sum_append, List.map_map, Function.comp_def, e, hmul,
      List.sum_map_add]

section Q
variable (e : S →+* k) (c : ι → ι → k) (q : S)
  (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))

include hadd hC hq2 in
theorem TG_q_long (w : List ι) (hw : 3 ≤ w.length) : TG D w q = 0 := by
  induction w with
  | nil => simp at hw
  | cons l w ih =>
    show D l (TG D w q) = 0
    rcases Nat.lt_or_ge w.length 3 with h | h
    · have h2 : w.length = 2 := by
        simp only [List.length_cons] at hw
        omega
      obtain ⟨y, z, rfl⟩ := List.length_eq_two.mp h2
      show D l (D y (D z q)) = 0
      rw [hq2, hC]
    · rw [ih h, D_zero D hadd]

variable (he : ∀ a, e (κ a) = a)

include hadd hC hq0 hq1 hq2 he in
theorem e_TG_q (b : List ι) : e (TG D b q) = ev2 c b := by
  match b with
  | [] => exact hq0
  | [x] => exact hq1 x
  | [x, y] =>
    show e (D x (D y q)) = c x y
    rw [hq2, he]
  | x :: y :: z :: r =>
    rw [TG_q_long (D := D) (κ := κ) (hadd := hadd) (hC := hC) (c := c) (q := q) (hq2 := hq2)
      (w := x :: y :: z :: r) (by simp)]
    exact map_zero e

include hadd hmul hC hq0 hq1 hq2 he in
theorem e_TG_mul_q (w : List ι) (A : S) :
    e (TG D w (A * q)) = ((splits w).map (fun p => e (TG D p.1 A) * ev2 c p.2)).sum := by
  simp only [TG_mul (D := D) (hadd := hadd) (hmul := hmul), map_list_sum, List.map_map,
    Function.comp_def, map_mul, e_TG_q (D := D) (κ := κ) (hadd := hadd) (hC := hC) (e := e) (c := c)
      (q := q) (hq0 := hq0) (hq1 := hq1) (hq2 := hq2) (he := he)]

end Q

end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FoldrIterateDerivationEq
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {d : ℕ}

section Mon
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)

end Mon

section abelian₂
variable {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : List ι → k)

def lamW (P : MvPolynomial ι k) : k :=
  (AddMonoidAlgebra.coeff P).sum (fun n a => a * ψ (word (Finset.univ : Finset ι).toList n))

theorem lamW_add (P Q : MvPolynomial ι k) : lamW ψ (P + Q) = lamW ψ P + lamW ψ Q := by
  show (AddMonoidAlgebra.coeff P + AddMonoidAlgebra.coeff Q).sum _ = _
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem lamW_monomial (n : ι →₀ ℕ) (a : k) :
    lamW ψ (MvPolynomial.monomial n a) = a * ψ (word (Finset.univ : Finset ι).toList n) := by
  show (Finsupp.single n a).sum _ = _
  exact Finsupp.sum_single_index (zero_mul _)

theorem lamW_sum (s : Finset ι) (f : ι → MvPolynomial ι k) :
    lamW ψ (∑ i ∈ s, f i) = ∑ i ∈ s, lamW ψ (f i) := by
  let L : MvPolynomial ι k →+ k :=
    { toFun := lamW ψ, map_zero' := by simpa using lamW_add ψ 0 0, map_add' := lamW_add ψ }
  exact map_sum L f s

def rW (c : ι → ι → k) (n : ι →₀ ℕ) : k :=
  ((Finset.univ : Finset ι).toList.map (fun x => ((Finset.univ : Finset ι).toList.map (fun y =>
    c x y * ((n y * (n - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
      ψ (word (Finset.univ : Finset ι).toList (n - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum

theorem secondOrder_add (c : ι → ι → k) (p q : MvPolynomial ι k) :
    secondOrder k c (p + q) = secondOrder k c p + secondOrder k c q := by
  unfold secondOrder
  simp only [map_add, mul_add, add_mul, Finset.sum_add_distrib]
  done

theorem lamW_secondOrder (c : ι → ι → k) (P : MvPolynomial ι k) :
    lamW ψ (secondOrder k c P) = (AddMonoidAlgebra.coeff P).sum (fun n a => a * rW ψ c n) := by
  refine MvPolynomial.induction_on' P (fun n a => ?_) (fun p q hp hq => ?_)
  · show lamW ψ (secondOrder k c (MvPolynomial.monomial n a)) =
      (Finsupp.single n a).sum fun m b => b * rW ψ c m
    have hL : ∀ g : ι → k, ((Finset.univ : Finset ι).toList.map g).sum = ∑ i, g i := by
      intro g
      first
        | exact Finset.sum_map_toList _ _
        | exact Finset.sum_toList _ _
        | rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList, Multiset.map_coe, Multiset.sum_coe]
    rw [Finsupp.sum_single_index (zero_mul _)]
    simp only [secondOrder, lamW_sum, MvPolynomial.pderiv_monomial, MvPolynomial.C_mul_monomial,
      lamW_monomial, rW, hL, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [Nat.cast_mul]
    ring
  · rw [secondOrder_add, lamW_add, hp, hq]
    show _ = (AddMonoidAlgebra.coeff p + AddMonoidAlgebra.coeff q).sum _
    rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

end abelian₂

end ReciprocityTheory.ChartRestriction.G.TB.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries Formalism.FG.SolveVAux

namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {σ τ : Type}

theorem low_pderiv {N : ℕ} {g : MvPowerSeries τ k} (hg : Low (N + 1) g) (t : τ) : Low N (pderiv k t g) := by
  intro d hd
  rw [MvPowerSeries.coeff_pderiv, hg, zero_mul]
  have e : Finsupp.degree (d + Finsupp.single t 1) = Finsupp.degree d + 1 := by
    first
    | rw [map_add, Finsupp.degree_single]
    | simp [Finsupp.degree, Finsupp.sum_add_index']
    | (unfold Finsupp.degree; rw [Finsupp.sum_add_index' (by simp) (by simp)]; simp)
  omega

private theorem low_mul_lemma {m n : ℕ} {f g : MvPowerSeries τ k} (hf : Low m f) (hg : Low n g) :
    Low (m + n) (f * g) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  first
  | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  | simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  | simp only [Finset.mem_antidiagonal] at hx
  have e : Finsupp.degree x.1 + Finsupp.degree x.2 = Finsupp.degree d := by
    rw [← hx]
    first
    | exact (map_add _ _ _).symm
    | simp [Finsupp.degree, Finsupp.sum_add_index']
  by_cases h1 : Finsupp.degree x.1 < m
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

private theorem low_pow_lemma_2 {f : MvPowerSeries τ k} (hf : Low 1 f) (n : ℕ) : Low n (f ^ n) := by
  induction n with
  | zero => intro d hd; omega
  | succ n ih => rw [pow_succ]; exact low_mul_lemma ih hf

private theorem low_prod_lemma_3 {a : σ → MvPowerSeries τ k} (ha : ∀ s, Low 1 (a s)) (e : σ →₀ ℕ)
    (S : Finset σ) : Low (∑ s ∈ S, e s) (∏ s ∈ S, a s ^ e s) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · intro d hd
    simp at hd
  · intro s S hs ih
    rw [Finset.sum_insert hs, Finset.prod_insert hs]
    exact low_mul_lemma (low_pow_lemma_2 (ha s) _) ih

private theorem finsupp_apply_le_degree' {ι : Type} (d : ι →₀ ℕ) (i : ι) : d i ≤ d.degree := by
  first
  | exact Finsupp.le_degree i d
  | exact Finsupp.le_degree d i
  | exact Finsupp.le_degree

theorem low_subst_of_low [Finite σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, Low 1 (a s)) {N : ℕ}
    {g : MvPowerSeries σ k} (hg : Low N g) : Low N (subst a g) := by
  classical
  have hc : ∀ s, constantCoeff (a s) = 0 := fun s => by
    have h0 := ha s 0 (by simp)
    simpa using h0
  intro d hd
  have hS : HasSubst a := by
    exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  rw [MvPowerSeries.coeff_subst hS]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e.degree < N
  · exact smul_eq_zero_of_left (hg e he) _
  · have hl : Low e.degree (e.prod fun s n => a s ^ n) := by
      have h := low_prod_lemma_3 ha e e.support
      have hdeg : e.degree = ∑ s ∈ e.support, e s := by
        first
        | rfl
        | exact Finsupp.degree_eq_sum e
        | simp [Finsupp.degree]
      rw [hdeg]
      exact h
    exact smul_eq_zero_of_right _ (hl d (by omega))

theorem pderiv_aeval [Fintype σ] (a : σ → MvPowerSeries τ k) (p : MvPolynomial σ k) (t : τ) :
    pderiv k t (MvPolynomial.aeval a p) =
      ∑ s, MvPolynomial.aeval a (MvPolynomial.pderiv s p) * pderiv k t (a s) := by
  classical
  induction p using MvPolynomial.induction_on
  next c =>
    simp
  next p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  next p s0 hp =>
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul, Finset.mul_sum]
    simp only [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, map_add, map_mul,
      MvPolynomial.aeval_X, add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, map_one, map_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [apply_ite (MvPolynomial.aeval a), map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, mul_assoc]
    try ring

private theorem pderiv_coe_mvPolynomial (s : σ) (p : MvPolynomial σ k) :
    pderiv k s (p : MvPowerSeries σ k) = ((MvPolynomial.pderiv s p : MvPolynomial σ k) : MvPowerSeries σ k) := by
  ext m
  rw [MvPowerSeries.coeff_pderiv, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe, MvPolynomial.coeff_pderiv]

private theorem Low_finset_sum {N : ℕ} {ι : Type} (S : Finset ι) (F : ι → MvPowerSeries τ k)
    (h : ∀ i ∈ S, Low N (F i)) : Low N (∑ i ∈ S, F i) := by
  intro d hd
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi d hd

theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ k) (t : τ) :
    pderiv k t (subst a f) = ∑ s, subst a (pderiv k s f) * pderiv k t (a s) := by
  classical
  have hS : HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have ha1 : ∀ s, Low 1 (a s) := by
    intro s d hd
    have hd0 : d = 0 := Finsupp.ext fun i => by
      have := finsupp_apply_le_degree' d i
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    subst hd0
    simpa using ha s
  have hpoly : ∀ M : ℕ, ∃ p : MvPolynomial σ k, Low M (f - (p : MvPowerSeries σ k)) := by
    intro M
    refine ⟨MvPowerSeries.trunc' k (Finsupp.equivFunOnFinite.symm fun _ => M) f, ?_⟩
    intro m hm
    rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos, sub_self]
    rw [Finsupp.le_def]
    intro s
    have h1 := finsupp_apply_le_degree' m s
    first
    | (change m s ≤ M; omega)
    | (simp; omega)
  ext d
  obtain ⟨p, hp⟩ := hpoly (d.degree + 1 + 1)
  have hf : f = (f - (p : MvPowerSeries σ k)) + (p : MvPowerSeries σ k) := (sub_add_cancel _ _).symm
  generalize f - (p : MvPowerSeries σ k) = g at hp hf
  subst hf
  have hpol := pderiv_aeval a p t
  simp only [map_add, MvPowerSeries.subst_add hS, MvPowerSeries.subst_coe, pderiv_coe_mvPolynomial, add_mul,
    Finset.sum_add_distrib, hpol]
  congr 1
  have h1 : Low (d.degree + 1) (pderiv k t (subst a g)) := low_pderiv (low_subst_of_low ha1 hp) t
  have h2 : Low (d.degree + 1 + 0) (∑ s, subst a (pderiv k s g) * pderiv k t (a s)) :=
    Low_finset_sum _ _ fun s _ => low_mul_lemma (low_subst_of_low ha1 (low_pderiv hp s)) (fun e he => by omega)
  rw [h1 d (by omega), h2 d (by omega)]

theorem pderiv_comm (u v : τ) (g : MvPowerSeries τ k) : pderiv k u (pderiv k v g) = pderiv k v (pderiv k u g) := by
  ext n
  simp only [MvPowerSeries.coeff_pderiv]
  by_cases huv : u = v
  · subst huv
    rfl
  · have h1 : (n + Finsupp.single u 1 : τ →₀ ℕ) v = n v := by simp [Finsupp.single_apply, huv]
    have h2 : (n + Finsupp.single v 1 : τ →₀ ℕ) u = n u := by simp [Finsupp.single_apply, Ne.symm huv]
    rw [h1, h2, add_right_comm n]
    ring

theorem eq_C_of_pderiv_zero [Algebra ℚ k] {g : MvPowerSeries τ k} (h : ∀ v, pderiv k v g = 0) :
    g = C (constantCoeff g) := by
  classical
  ext n
  rw [MvPowerSeries.coeff_C]
  split_ifs with hn
  · subst hn
    simp
  · obtain ⟨v, hv⟩ : ∃ v, n v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hn (Finsupp.ext fun i => by simpa using hcon i)
    set m := n - Finsupp.single v 1 with hm
    have hnm : n = m + Finsupp.single v 1 :=
      (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv))).symm
    have h0 := congrArg (MvPowerSeries.coeff m) (h v)
    rw [MvPowerSeries.coeff_pderiv, ← hnm, map_zero] at h0
    have hu : IsUnit ((m v : k) + 1) := by
      have e : ((m v : k) + 1) = algebraMap ℚ k ((m v : ℚ) + 1) := by simp
      rw [e]
      exact (IsUnit.mk0 _ (by positivity)).map _
    exact (hu.mul_left_eq_zero).mp h0

end ReciprocityTheory.ChartRestriction.G.TB.LogPf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SCWick
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem betaH_zero_zero (φ φ' : Fin d → k) : betaH k (0, φ) (0, φ') = 0 := by
  simp [betaH]

theorem betaH_antisymm (ξ η : (Fin d → k) × (Fin d → k)) : betaH k ξ η = -betaH k η ξ := by
  unfold betaH
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

def kapW (m : ℕ) {ι : Type} (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (l l' : ι) : k :=
  if s l = true ∧ s l' = false then (m : k) * betaH k (ξb l) (ξa l') else 0

theorem kapW_supp (m : ℕ) {ι : Type} (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (l l' : ι)
    (h : kapW m s ξa ξb l l' ≠ 0) : s l = true ∧ s l' = false := by
  unfold kapW at h
  by_contra hc
  exact h (if_neg hc)

theorem ordNabla_wick (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type}
    [Fintype ι] (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (hb0 : ∀ l, (ξb l).1 = 0)
    (haa : ∀ l l', s l = s l' → betaH k (ξa l) (ξa l') = 0)
    (hab : ∀ l l', s l = s l' → betaH k (ξa l) (ξb l') = 0) (P : MvPolynomial ι k) (f : PS k 1 d) :
    ordNabla k B h m s (fun l => ξa l + ξb l) P (liftX k f) =
      ∑ n ∈ Finset.range ((MvPolynomial.rename (sideE s) P).totalDegree + 1),
        PI.WickFormula.ordEval (opL B h m s ξa) (opR B h m s ξa)
          (((n.factorial : ℚ)⁻¹) • MvPolynomial.rename (sideE s) ((secondOrder k (kapW m s ξa ξb))^[n] P))
          (liftX k f) := by
  have hbb : ∀ l l', betaH k (ξb l) (ξb l') = 0 := fun l l' => by
    rw [show ξb l = (0, (ξb l).2) from Prod.ext (hb0 l) rfl, show ξb l' = (0, (ξb l').2) from Prod.ext (hb0 l') rfl]
    exact betaH_zero_zero _ _
  have hba : ∀ l l', s l = s l' → betaH k (ξb l) (ξa l') = 0 := fun l l' e => by
    rw [betaH_antisymm, hab l' l e.symm, neg_zero]
  have cA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
    fun l l' e => nablaL_comm hN2 B h m _ _ (haa l l' e)
  have cAB : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
    fun l l' e => nablaL_comm hN2 B h m _ _ (hab l l' e)
  have cBA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
    fun l l' e => nablaL_comm hN2 B h m _ _ (hba l l' e)
  have cB : ∀ l l', Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
    fun l l' => nablaL_comm hN2 B h m _ _ (hbb l l')
  have hsum : ∀ l, nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2 =
      nablaL B h m (ξa l).1 (ξa l).2 + nablaL B h m (ξb l).1 (ξb l).2 := fun l =>
    nablaL_add B h m _ _ _ _
  have cAll : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2)
      (nablaL B h m (ξa l' + ξb l').1 (ξa l' + ξb l').2) := fun l l' e => by
    rw [hsum, hsum]
    exact ((cA l l' e).add_right (cAB l l' e)).add_left ((cBA l l' e).add_right (cB l l'))
  rw [ordNabla_eq B h m s (fun l => ξa l + ξb l) cAll P (liftX k f)]
  have hL : opL B h m s (fun l => ξa l + ξb l) = opL B h m s ξa + opL B h m s ξb := funext fun i => hsum _
  have hR : opR B h m s (fun l => ξa l + ξb l) = opR B h m s ξa + opR B h m s ξb := funext fun j => hsum _
  have key := _root_.wick_formula k (Module.End k (AA k d)) (AA k d) _ _ (opL B h m s ξa) (opL B h m s ξb)
    (opR B h m s ξa) (opR B h m s ξb) (kapE s (kapW m s ξa ξb)) (liftX k f)
    (fun i i' => ⟨cA _ _ (by rw [side_inl s i, side_inl s i']), cAB _ _ (by rw [side_inl s i, side_inl s i']),
      cB _ _⟩)
    (fun j j' => ⟨cA _ _ (by rw [side_inr s j, side_inr s j']), cAB _ _ (by rw [side_inr s j, side_inr s j']),
      cB _ _⟩)
    (fun i j => cB _ _)
    (fun i j => by
      rw [nablaL_bracket hN2 B h m]
      unfold kapE kapW
      rw [if_pos ⟨side_inl s i, side_inr s j⟩])
    (fun i => by
      rw [Module.End.smul_def, opL, hb0]
      exact hN3 R d O k B h m _ f)
    (fun j => by
      rw [Module.End.smul_def, opR, hb0]
      exact hN3 R d O k B h m _ f)
    (MvPolynomial.rename (sideE s) P)
  rw [hL, hR, ← Module.End.smul_def, key]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Module.End.smul_def, delta_pow_rename s _ (kapW_supp m s ξa ξb)]

theorem ordNabla_u (hN2 : ConnectionCommutator) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type} [Fintype ι] (s : ι → Bool)
    (u : ι → Fin d → k) (P : MvPolynomial ι k) (G : AA k d) :
    ordNabla k B h m s (fun l => (u l, 0)) P G = nablaPoly k B h m u P G := by
  have hcomm : ∀ a b : ι, Function.Commute (nabla k B h m (u a) 0) (nabla k B h m (u b) 0) := by
    intro a b z
    have hz := hN2 R d O k B h m (u a, 0) (u b, 0) z
    have hb : betaH k (u a, (0 : Fin d → k)) (u b, 0) = 0 := by simp [betaH]
    rw [hb, mul_zero, map_zero, zero_mul] at hz
    exact sub_eq_zero.mp hz
  unfold ordNabla nablaPoly
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [← List.foldr_append]
  refine List.Perm.foldr_eq' (List.filter_append_perm _ _) ?_ _
  intro x _ y _ z
  exact (hcomm y x).iterate_iterate (n y) (n x) z

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end

