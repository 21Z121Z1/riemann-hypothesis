import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasSubstEv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleLawAdd
section
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FormalCalc

theorem coeff_single_subst {σ τ R : Type*} [CommRing R] [Fintype σ]
    {a : σ → MvPowerSeries τ R} (ha0 : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ R) (j : τ) :
    coeff (Finsupp.single j 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single j 1) (a s) := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have hsplit : f = C (constantCoeff f) + ∑ s, C (coeff (Finsupp.single s 1) f) * X s +
      (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s) := by ring
  have hlow : ∀ e : σ →₀ ℕ, Finsupp.degree e < 2 →
      coeff e (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s) = 0 := by
    intro e he
    have hle : Finsupp.degree e ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · obtain rfl : e = 0 := (Finsupp.degree_eq_zero_iff e).mp h0
      simp [coeff_zero_X, coeff_zero_eq_constantCoeff_apply]
    · have hr : e ∈ Set.range (fun t : σ => Finsupp.single t 1) := by
        rw [Finsupp.range_single_one]; exact h1
      obtain ⟨t, rfl⟩ := hr
      simp [coeff_X, coeff_C, Finsupp.single_eq_single_iff]
  have hord : coeff (Finsupp.single j 1)
      (subst a (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s)) = 0 := by
    apply coeff_of_lt_order
    have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order :=
      le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.mpr (ha0 i)
    have h2 : (2 : ℕ∞) ≤
        (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s).order :=
      le_order fun e he => hlow e (by exact_mod_cast he)
    calc ((Finsupp.degree (Finsupp.single j 1) : ℕ) : ℕ∞) < 2 := by
          rw [Finsupp.degree_single]; norm_num
      _ = 1 * 2 := by norm_num
      _ ≤ _ := mul_le_mul' h1 h2
      _ ≤ _ := le_order_subst ha _
  have hexp : subst a f = subst a (C (constantCoeff f)) +
      subst a (∑ s, C (coeff (Finsupp.single s 1) f) * X s) +
      subst a (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s) := by
    conv_lhs => rw [hsplit]
    rw [subst_add ha, subst_add ha]
  rw [hexp, map_add, map_add, hord, add_zero, subst_C' ha, subst_sum' ha, map_sum]
  simp [subst_mul ha, subst_C' ha, subst_X ha, coeff_C_mul, coeff_C]

variable {R : Type} [CommRing R] {d : ℕ}

theorem coeff_single_ev_two {n : ℕ} (p q : Pt R n d) (hp : ∀ i, constantCoeff (p i) = 0)
    (hq : ∀ i, constantCoeff (q i) = 0) (f : PS R 2 d) (j : Fin n × Fin d) :
    coeff (Finsupp.single j 1) (ev ![p, q] f) =
      ∑ l, coeff (Finsupp.single ((0 : Fin 2), l) 1) f * coeff (Finsupp.single j 1) (p l) +
      ∑ l, coeff (Finsupp.single ((1 : Fin 2), l) 1) f * coeff (Finsupp.single j 1) (q l) := by
  have h0 : ∀ s : Fin 2 × Fin d, constantCoeff ((![p, q] : Fin 2 → Pt R n d) s.1 s.2) = 0 := by
    rintro ⟨b, i⟩
    fin_cases b
    · exact hp i
    · exact hq i
  unfold ev
  rw [coeff_single_subst h0, Fintype.sum_prod_type, Fin.sum_univ_two]
  all_goals rfl

theorem coeff_single_X {σ : Type*} [DecidableEq σ] (s t : σ) :
    coeff (Finsupp.single s 1) (X t : MvPowerSeries σ R) = if s = t then 1 else 0 := by
  by_cases h : s = t
  · subst h
    simp [coeff_X]
  · simp [coeff_X, h, Finsupp.single_eq_single_iff]

theorem constantCoeff_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  unfold pt
  exact constantCoeff_X (j, i)

theorem coeff_law_snd (G : FGLaw R d) (i l : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), l) 1) (G.F i) = if l = i then 1 else 0 := by
  have hu := congrArg (coeff (Finsupp.single ((0 : Fin 1), l) 1)) (G.unit i)
  rw [coeff_single_ev_two (n := 1) 0 (pt R d 0) (fun _ => by simp) (fun m => constantCoeff_pt 0 m)] at hu
  simpa [pt, coeff_single_X, mul_boole, Finset.sum_ite_eq, Finset.sum_ite_eq'] using hu

theorem coeff_law_fst (G : FGLaw R d) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), l) 1) (G.F i) = if l = i then 1 else 0 := by
  have hc := congrArg (coeff (Finsupp.single ((0 : Fin 2), l) 1)) (G.comm i)
  rw [coeff_single_ev_two (n := 2) (pt R d 1) (pt R d 0) (fun m => constantCoeff_pt 1 m)
    (fun m => constantCoeff_pt 0 m)] at hc
  rw [← hc]
  simp [pt, coeff_single_X, coeff_law_snd, mul_boole, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem coeff_single_law_add {n : ℕ} (G : FGLaw R d) (p q : Pt R n d)
    (hp : ∀ i, constantCoeff (p i) = 0) (hq : ∀ i, constantCoeff (q i) = 0) (i : Fin d)
    (j : Fin n × Fin d) :
    coeff (Finsupp.single j 1) (G.add p q i) =
      coeff (Finsupp.single j 1) (p i) + coeff (Finsupp.single j 1) (q i) := by
  show coeff (Finsupp.single j 1) (ev ![p, q] (G.F i)) = _
  rw [coeff_single_ev_two p q hp hq]
  simp [coeff_law_fst, coeff_law_snd, boole_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem dAct_add_and_one : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O]
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O),
    (∀ a b : O, dAct k B (a + b) = dAct k B a + dAct k B b) ∧ dAct k B 1 = 1 := by
  intro R _ d O _ _ k _ _ _ B
  constructor
  · intro a b
    ext i j
    rw [Matrix.add_apply]
    unfold dAct FB.actK
    rw [B.A.add_act]
    simp only [coeff_map]
    rw [coeff_single_law_add B.G (B.A.act a) (B.A.act b) (B.A.const a) (B.A.const b), map_add]
  · ext i j
    unfold dAct FB.actK
    simp only [B.A.one_act, coeff_map, Matrix.one_apply, pt, coeff_single_X, Prod.mk.injEq, true_and]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h, Ne.symm h]

end GlobalTheory.FormalCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Comp1Scalar
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
namespace GlobalTheory.AdditiveBiext
variable {R : Type} [CommRing R] {d : ℕ}
lemma comp1_scalar {n : ℕ} (a : R) (p : Pt R n d) (hp : ∀ i, constantCoeff (p i) = 0) :
    comp1 (fun i => (C a * X ((0:Fin 1), i) : PS R 1 d)) p = fun i => C a * p i := by
  funext i
  have h : ∀ (j : Fin 1) (l : Fin d), constantCoeff ((![p] : Fin 1 → Pt R n d) j l) = 0 := by
    intro j l; fin_cases j; simpa using hp l
  unfold comp1
  rw [ev_mul _ h, ev_C, ev_X _ h]; simp
lemma addLaw_add {n : ℕ} (p q : Pt R n d) (hp : ∀ i, constantCoeff (p i) = 0) (hq : ∀ i, constantCoeff (q i) = 0) :
    (addLaw R d).add p q = fun i => p i + q i := by
  funext i
  have h : ∀ (j : Fin 2) (l : Fin d), constantCoeff ((![p, q] : Fin 2 → Pt R n d) j l) = 0 := by
    intro j l; fin_cases j
    · simpa using hp l
    · simpa using hq l
  show ev ![p, q] (X ((0 : Fin 2), i) + X ((1 : Fin 2), i)) = _
  rw [ev_add _ h, ev_X _ h, ev_X _ h]; simp

def scalarAct (R : Type) [CommRing R] (d : ℕ) : OAct R (addLaw R d) where
  act := fun a i => C a * X ((0:Fin 1), i)
  const := by intro a i; simp
  hom := by
    intro a
    rw [addLaw_add _ _ (by simp [pt]) (by simp [pt]), comp1_scalar _ _ (by simp [pt]), comp1_scalar _ _ (by simp [pt]), comp1_scalar _ _ (by simp [pt]), addLaw_add _ _ (by simp [pt]) (by simp [pt])]
    funext i; ring
  add_act := by
    intro a b
    rw [addLaw_add _ _ (by simp) (by simp)]
    funext i; rw [map_add]; ring
  mul_act := by
    intro a b
    rw [comp1_scalar _ _ (by simp)]
    funext i; rw [map_mul]; ring
  one_act := by funext i; simp [pt]

def additiveFB (R : Type) [CommRing R] [StarRing R] (d : ℕ) : FB R d R := FB.triv (addLaw R d) (scalarAct R d)

theorem main : ∀ (R : Type) [CommRing R] [StarRing R] (d : ℕ), ∃ B : FB R d R,
    (∀ i, B.G.F i = X ((0 : Fin 2), i) + X ((1 : Fin 2), i)) ∧ ∀ a i, B.A.act a i = C a * X ((0 : Fin 1), i) :=
  fun R _ _ d => ⟨additiveFB R d, fun _ => rfl, fun _ _ => rfl⟩
end GlobalTheory.AdditiveBiext
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpSNegMulExpS
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.NablaExpConj

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

section Lift

variable (k : Type) [CommRing k]

theorem liftX_hasSubst : HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem liftX_one : liftX k (1 : PS k 1 d) = 1 :=
  FormalCalc.subst_one' (liftX_hasSubst k)

theorem liftX_mul (f g : PS k 1 d) : liftX k (f * g) = liftX k f * liftX k g :=
  subst_mul (liftX_hasSubst k) f g

theorem liftX_sum {ι : Type} (s : Finset ι) (f : ι → PS k 1 d) :
    liftX k (∑ i ∈ s, f i) = ∑ i ∈ s, liftX k (f i) :=
  FormalCalc.subst_sum' (liftX_hasSubst k) s f

theorem pderiv_inl_liftX (f : PS k 1 d) (j : Fin d) :
    pderiv k (Sum.inl j) (liftX k f) = liftX k (pderiv k ((0 : Fin 1), j) f) := by
  unfold liftX
  rw [FormalCalc.pderiv_subst (liftX_hasSubst k), Finset.sum_eq_single ((0 : Fin 1), j)]
  · rw [pderiv_X_self, mul_one]
  · rintro ⟨a, b⟩ _ hne
    have hb : b ≠ j := fun h => hne (by subst h; rw [Subsingleton.elim a 0])
    rw [pderiv_X_of_ne (fun h => hb (Sum.inl_injective h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem pderiv_inr_liftX (f : PS k 1 d) (i : Fin d) : pderiv k (Sum.inr i) (liftX k f) = 0 := by
  unfold liftX
  rw [FormalCalc.pderiv_subst (liftX_hasSubst k)]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [pderiv_X_of_ne Sum.inl_ne_inr, mul_zero]

end Lift

variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

omit [Algebra ℚ k] in

theorem Dx_liftX (B : FB R d O) (u : Fin d → k) (f : PS k 1 d) :
    Dx k B u (liftX k f) = liftX k (Dof (B.FK k) u f) := by
  simp only [Dx, Dof, pderiv_inl_liftX, liftX_sum, liftX_mul]

omit [Algebra ℚ k] in

theorem Dx_mul (B : FB R d O) (u : Fin d → k) (f G : AA k d) :
    Dx k B u (f * G) = Dx k B u f * G + f * Dx k B u G := by
  simp only [Dx, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

omit [Algebra ℚ k] in

theorem nabla_liftX_mul (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (f : PS k 1 d)
    (G : AA k d) :
    nabla k B h m u φ (liftX k f * G) =
      liftX k f * nabla k B h m u φ G + liftX k (Dof (B.FK k) u f) * G := by
  have e : ∀ c : Fin d → AA k d, ∑ i : Fin d, c i * pderiv k (Sum.inr i) (liftX k f * G) =
      liftX k f * ∑ i : Fin d, c i * pderiv k (Sum.inr i) G := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz, pderiv_inr_liftX, smul_zero, add_zero, smul_eq_mul]
    ring
  unfold nabla
  rw [Dx_mul, Dx_liftX, e, e]
  ring

theorem Dof_expS (F : Fin d → PS k 2 d) (u : Fin d → k) {g : PS k 1 d}
    (hg : constantCoeff g = 0) : Dof F u (FB.expS k g) = FB.expS k g * Dof F u g := by
  have e : ∀ i, pderiv k i (FB.expS k g) = FB.expS k g * pderiv k i g :=
    FormalCalc.pderiv_formalExp hg
  unfold Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e]
  ring

theorem expS_neg_mul_expS {n : ℕ} {g : PS k n d} (hg : constantCoeff g = 0) :
    FB.expS k (-g) * FB.expS k g = 1 := by
  rw [mul_comm]
  exact FormalCalc.formalExp_mul_formalExp_neg hg

theorem main : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (g : PS k 1 d), constantCoeff g = 0 → ∀ G : AA k d, liftX k (FB.expS k (-g)) * nabla k B h m u φ (liftX k (FB.expS k g) * G) = nabla k B h m u φ G + liftX k (Dof (B.FK k) u g) * G := by
  intro R _ d O _ _ k _ _ _ B h m u φ g hg G
  have e : liftX k (FB.expS k (-g)) * liftX k (FB.expS k g) = 1 := by
    rw [← liftX_mul, expS_neg_mul_expS k hg, liftX_one]
  rw [nabla_liftX_mul, Dof_expS k _ u hg, liftX_mul]
  linear_combination (nabla k B h m u φ G + liftX k (Dof (B.FK k) u g) * G) * e

end GlobalTheory.NablaExpConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntAASubstOfHasSubst
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IntSeries

variable {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] {σ τ : Type}

theorem intAA_zero : IntAA (R := R) k (0 : MvPowerSeries σ k) := fun n => by
  rw [map_zero]; exact Subring.zero_mem _

theorem intAA_map (f : MvPowerSeries σ R) :
    IntAA (R := R) k (MvPowerSeries.map (algebraMap R k) f) := fun n => by
  rw [coeff_map]; exact ⟨_, rfl⟩

theorem intAA_one : IntAA (R := R) k (1 : MvPowerSeries σ k) := by
  simpa using intAA_map (k := k) (1 : MvPowerSeries σ R)

theorem intAA_X (s : σ) : IntAA (R := R) k (X s : MvPowerSeries σ k) := by
  simpa using intAA_map (k := k) (X s : MvPowerSeries σ R)

theorem intAA_C (r : R) : IntAA (R := R) k (C (algebraMap R k r) : MvPowerSeries σ k) := by
  simpa using intAA_map (k := k) (C r : MvPowerSeries σ R)

theorem intAA_iff_exists_map {f : MvPowerSeries σ k} :
    IntAA (R := R) k f ↔ ∃ g : MvPowerSeries σ R, MvPowerSeries.map (algebraMap R k) g = f := by
  refine ⟨fun h => ?_, fun ⟨g, hg⟩ => hg ▸ intAA_map g⟩
  choose g hg using h
  exact ⟨g, MvPowerSeries.ext fun n => (coeff_map _ _ _).trans (hg n)⟩

theorem intAA_add {f g : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (hg : IntAA (R := R) k g) :
    IntAA (R := R) k (f + g) := fun n => by
  rw [map_add]; exact Subring.add_mem _ (hf n) (hg n)

theorem intAA_neg {f : MvPowerSeries σ k} (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (-f) := fun n => by
  rw [map_neg]; exact Subring.neg_mem _ (hf n)

theorem intAA_sub {f g : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (hg : IntAA (R := R) k g) :
    IntAA (R := R) k (f - g) := fun n => by
  rw [map_sub]; exact Subring.sub_mem _ (hf n) (hg n)

theorem intAA_mul {f g : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (hg : IntAA (R := R) k g) :
    IntAA (R := R) k (f * g) := fun n => by
  classical
  rw [coeff_mul]
  exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (hf _) (hg _)

theorem intAA_smul (r : R) {f : MvPowerSeries σ k} (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (algebraMap R k r • f) := fun n => by
  rw [map_smul, smul_eq_mul]; exact Subring.mul_mem _ ⟨r, rfl⟩ (hf n)

theorem intAA_pow {f : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (m : ℕ) :
    IntAA (R := R) k (f ^ m) := by
  induction m with
  | zero => simpa using intAA_one
  | succ m ih => rw [pow_succ]; exact intAA_mul ih hf

theorem intAA_sum {ι : Type*} (t : Finset ι) {f : ι → MvPowerSeries σ k}
    (hf : ∀ i ∈ t, IntAA (R := R) k (f i)) : IntAA (R := R) k (∑ i ∈ t, f i) := fun n => by
  rw [map_sum]; exact Subring.sum_mem _ fun i hi => hf i hi n

theorem intAA_prod {ι : Type*} (t : Finset ι) {f : ι → MvPowerSeries σ k}
    (hf : ∀ i ∈ t, IntAA (R := R) k (f i)) : IntAA (R := R) k (∏ i ∈ t, f i) :=
  Finset.prod_induction f (IntAA (R := R) k) (fun _ _ => intAA_mul) intAA_one hf

theorem intAA_pderiv {f : MvPowerSeries σ k} (s : σ) (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (pderiv k s f) := fun n => by
  rw [coeff_pderiv]
  exact Subring.mul_mem _ (hf _) (Subring.add_mem _ (natCast_mem _ _) (Subring.one_mem _))

theorem intAA_subst_of_hasSubst {a : σ → MvPowerSeries τ k} (ha : HasSubst a)
    {f : MvPowerSeries σ k} (hai : ∀ s, IntAA (R := R) k (a s)) (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (MvPowerSeries.subst a f) := fun n => by
  rw [coeff_subst ha]
  refine finsum_induction (· ∈ (algebraMap R k).range) (Subring.zero_mem _)
    (fun _ _ => Subring.add_mem _) fun d => ?_
  rw [smul_eq_mul]
  exact Subring.mul_mem _ (hf d) (intAA_prod _ (fun s _ => intAA_pow (hai s) _) n)

theorem intAA_subst [Finite σ] {a : σ → MvPowerSeries τ k} {f : MvPowerSeries σ k}
    (ha : ∀ s, constantCoeff (a s) = 0) (hai : ∀ s, IntAA (R := R) k (a s))
    (hf : IntAA (R := R) k f) : IntAA (R := R) k (MvPowerSeries.subst a f) :=
  intAA_subst_of_hasSubst (hasSubst_of_constantCoeff_zero ha) hai hf

theorem main : ∀ (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k],
  (∀ (σ : Type) (f g : MvPowerSeries σ k), IntAA (R := R) k f → IntAA (R := R) k g → IntAA (R := R) k (f + g) ∧ IntAA (R := R) k (f - g) ∧ IntAA (R := R) k (f * g)) ∧
  (∀ (σ : Type) (f : MvPowerSeries σ k) (s : σ), IntAA (R := R) k f → IntAA (R := R) k (pderiv k s f)) ∧
  (∀ (σ : Type) (f : MvPowerSeries σ R), IntAA (R := R) k (MvPowerSeries.map (algebraMap R k) f)) ∧
  (∀ (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ k) (f : MvPowerSeries σ k), (∀ s, constantCoeff (a s) = 0) → (∀ s, IntAA (R := R) k (a s)) → IntAA (R := R) k f → IntAA (R := R) k (MvPowerSeries.subst a f)) :=
  fun _ _ _ _ _ =>
    ⟨fun _ _ _ hf hg => ⟨intAA_add hf hg, intAA_sub hf hg, intAA_mul hf hg⟩,
      fun _ _ s hf => intAA_pderiv s hf, fun _ f => intAA_map f,
      fun _ _ _ _ _ ha hai hf => intAA_subst ha hai hf⟩

end GlobalTheory.IntSeries
end

