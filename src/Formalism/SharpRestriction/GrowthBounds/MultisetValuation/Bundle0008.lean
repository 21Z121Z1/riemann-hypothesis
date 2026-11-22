import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0006
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.JpSubstExpand
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ValuationBoundAdd
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0007

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EnGePProdRat
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

theorem en_p_mem : (p : Y.Kc) ∈ Y.Oc := by
  exact natCast_mem Y.Oc p

theorem en_ppow_mem (N : ℤ) (hN : 0 ≤ N) : (p : Y.Kc) ^ N ∈ Y.Oc := by
  lift N to ℕ using hN
  rw [zpow_natCast]
  exact Y.Oc.pow_mem (en_p_mem Y) _

theorem en_root (z : Y.Kc) (M : ℕ) (hM : 0 < M) (h : z ^ M ∈ Y.Oc) : z ∈ Y.Oc := by
  rcases Y.Oc_val z with hz | hz
  · exact hz
  · by_cases h0 : z = 0
    · rw [h0]
      exact Y.Oc.zero_mem
    · have e : z = z ^ M * (z⁻¹) ^ (M - 1) := by
        rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ h0), ← pow_succ']
        congr 1
        omega
      rw [e]
      exact Y.Oc.mul_mem h (Y.Oc.pow_mem hz _)

theorem en_geC_one : Y.geC 1 0 := by
  intro a b hb hab
  rw [one_pow, one_mul]
  have h' : (a : ℝ) ≤ 0 := by linarith
  have h'' : a ≤ 0 := by exact_mod_cast h'
  exact en_ppow_mem Y (-a) (by omega)

theorem en_geC_mul_rat {x y : Y.Kc} (q1 q2 : ℚ) (hx : Y.geC x q1) (hy : Y.geC y q2) :
    Y.geC (x * y) ((q1 + q2 : ℚ) : ℝ) := by
  intro a b hb hab
  have hp := pKc_ne Y
  have hM0 : 0 < q1.den * q2.den := Nat.mul_pos q1.den_pos q2.den_pos
  obtain ⟨a1, ha1⟩ : ∃ a1 : ℤ, (a1 : ℝ) = (q1 : ℝ) * ((b * (q1.den * q2.den) : ℕ) : ℝ) := by
    refine ⟨q1.num * q2.den * b, ?_⟩
    have hd : (q1.den : ℝ) ≠ 0 := by exact_mod_cast q1.den_pos.ne'
    rw [Rat.cast_def]
    push_cast
    field_simp
  obtain ⟨a2, ha2⟩ : ∃ a2 : ℤ, (a2 : ℝ) = (q2 : ℝ) * ((b * (q1.den * q2.den) : ℕ) : ℝ) := by
    refine ⟨q2.num * q1.den * b, ?_⟩
    have hd : (q2.den : ℝ) ≠ 0 := by exact_mod_cast q2.den_pos.ne'
    rw [Rat.cast_def]
    push_cast
    field_simp
  have hx' := hx a1 (b * (q1.den * q2.den)) (Nat.mul_pos hb hM0) ha1.le
  have hy' := hy a2 (b * (q1.den * q2.den)) (Nat.mul_pos hb hM0) ha2.le
  have hle : a * ((q1.den * q2.den : ℕ) : ℤ) ≤ a1 + a2 := by
    have h' : ((a * ((q1.den * q2.den : ℕ) : ℤ) : ℤ) : ℝ) ≤ ((a1 + a2 : ℤ) : ℝ) := by
      push_cast
      rw [ha1, ha2]
      push_cast at hab ⊢
      have hM' : (0 : ℝ) ≤ (q1.den : ℝ) * q2.den := by positivity
      nlinarith
    exact_mod_cast h'
  have key : ((x * y) ^ b * (p : Y.Kc) ^ (-a)) ^ (q1.den * q2.den) =
      (x ^ (b * (q1.den * q2.den)) * (p : Y.Kc) ^ (-a1)) * (y ^ (b * (q1.den * q2.den)) * (p : Y.Kc) ^ (-a2)) *
        (p : Y.Kc) ^ (a1 + a2 - a * ((q1.den * q2.den : ℕ) : ℤ)) := by
    have h1 : ((p : Y.Kc) ^ (-a)) ^ (q1.den * q2.den) =
        (p : Y.Kc) ^ (-a1) * (p : Y.Kc) ^ (-a2) * (p : Y.Kc) ^ (a1 + a2 - a * ((q1.den * q2.den : ℕ) : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hp, ← zpow_add₀ hp]
      congr 1
      push_cast
      ring
    rw [mul_pow, h1]
    ring
  apply en_root Y _ (q1.den * q2.den) hM0
  rw [key]
  exact Y.Oc.mul_mem (Y.Oc.mul_mem hx' hy') (en_ppow_mem Y _ (by omega))

theorem en_geC_sum {α : Type} (s : Finset α) (f : α → Y.Kc) (g : ℝ) (h : ∀ i ∈ s, Y.geC (f i) g) :
    Y.geC (∑ i ∈ s, f i) g := by
  exact Finset.sum_induction f (fun x => Y.geC x g) (fun _ _ ha hb => geC_add Y ha hb) (geC_zero Y g) h

def geP {τ : Type} (a : MvPolynomial τ Y.Kc) (g : ℝ) : Prop := ∀ n, Y.geC (MvPolynomial.coeff n a) g

theorem valuation_coeff_one_nonneg {τ : Type} : geP Y (1 : MvPolynomial τ Y.Kc) 0 := by
  classical
  intro n
  rw [MvPolynomial.coeff_one]
  split_ifs
  · exact en_geC_one Y
  · exact geC_zero Y 0

theorem valuation_coeff_ge_mul_rat {τ : Type} {a b : MvPolynomial τ Y.Kc} (q1 q2 : ℚ) (ha : geP Y a q1) (hb : geP Y b q2) :
    geP Y (a * b) ((q1 + q2 : ℚ) : ℝ) := by
  classical
  intro n
  rw [MvPolynomial.coeff_mul]
  exact en_geC_sum Y _ _ _ fun x _ => en_geC_mul_rat Y q1 q2 (ha x.1) (hb x.2)

theorem valuation_coeff_ge_prod_rat {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ Y.Kc) (q : α → ℚ)
    (h : ∀ i ∈ s, geP Y (a i) (q i)) : geP Y (∏ i ∈ s, a i) ((∑ i ∈ s, q i : ℚ) : ℝ) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using valuation_coeff_one_nonneg Y (τ := τ)
  · intro i t hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact valuation_coeff_ge_mul_rat Y _ _ (h i (Finset.mem_insert_self i t))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem valuation_coeff_ge_sum {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ Y.Kc) (g : ℝ) (h : ∀ i ∈ s, geP Y (a i) g) :
    geP Y (∑ i ∈ s, a i) g := by
  intro n
  rw [MvPolynomial.coeff_sum]
  exact en_geC_sum Y _ _ _ fun i hi => h i hi n

theorem valuation_coeff_ge_smul {τ : Type} {a : MvPolynomial τ Y.Kc} {g : ℝ} {c : Y.Kc} (hc : c ∈ Y.Oc) (h : geP Y a g) :
    geP Y (c • a) g := by
  intro n
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact geC_mul_Oc Y (h n) hc

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EntryAOneParity
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def ea_geR {K : Type} [Field K] (p : ℕ) (R : Subring K) (x : K) (g : ℝ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℝ) ≤ g * b → x ^ b * (p : K) ^ (-a) ∈ R

theorem ea_ext_gen {Kc : Type} [Field Kc] (Oc : Subring Kc) (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc) (K' : Type)
    [Field K'] [Algebra Kc K'] :
    ∃ R' : Subring K', (∀ x : K', x ∈ R' ∨ x⁻¹ ∈ R') ∧ ∀ x : Kc, algebraMap Kc K' x ∈ R' ↔ x ∈ Oc := by
  let V : ValuationSubring Kc := ⟨Oc, hval⟩
  obtain ⟨B, hle, hloc⟩ := LocalSubring.exists_le_valuationSubring (V.toLocalSubring.map (algebraMap Kc K'))
  refine ⟨B.toSubring, B.mem_or_inv_mem, fun x => ⟨fun hx => ?_, fun hx => hle ⟨x, hx, rfl⟩⟩⟩
  rcases hval x with h | h
  · exact h
  · by_cases hx0 : x = 0
    · rw [hx0]; exact Oc.zero_mem
    let a : (V.toLocalSubring.map (algebraMap Kc K')).toSubring := ⟨algebraMap Kc K' x⁻¹, ⟨x⁻¹, h, rfl⟩⟩
    have hu : IsUnit (Subring.inclusion hle a) := by
      refine IsUnit.of_mul_eq_one (⟨algebraMap Kc K' x, hx⟩ : B.toLocalSubring.toSubring) (Subtype.ext ?_)
      show algebraMap Kc K' x⁻¹ * algebraMap Kc K' x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    have hua : IsUnit a := hloc.map_nonunit a hu
    obtain ⟨b, hb⟩ := hua.exists_right_inv
    obtain ⟨y, hy, hyb⟩ := b.2
    have h1 : algebraMap Kc K' x⁻¹ * algebraMap Kc K' y = 1 := by
      have := congrArg Subtype.val hb
      rw [hyb]
      exact this
    rw [← map_mul, ← map_one (algebraMap Kc K')] at h1
    have h2 := (algebraMap Kc K').injective h1
    have h3 : y = x := by
      field_simp at h2
      exact h2
    rw [← h3]
    exact hy

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

abbrev ea_K (Y : Pend X) : Type := AlgebraicClosure Y.Kc

theorem ea_ext (Y : Pend X) : ∃ (R' : Subring (ea_K Y)) (vp : ea_K Y), vp ^ (p ^ 2 - 1) = (p : ea_K Y) ∧
    Rp p (ea_K Y) vp ≤ R' ∧ (∀ x : ea_K Y, x ∈ R' ∨ x⁻¹ ∈ R') ∧
    ∀ x : Y.Kc, algebraMap Y.Kc (ea_K Y) x ∈ R' ↔ x ∈ Y.Oc := by
  obtain ⟨R', hv, htr⟩ := ea_ext_gen Y.Oc Y.Oc_val (ea_K Y)
  have hn : 0 < p ^ 2 - 1 := by
    have := (Fact.out : p.Prime).two_le
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  obtain ⟨vp, hvp⟩ := IsAlgClosed.exists_pow_nat_eq (p : ea_K Y) hn
  refine ⟨R', vp, hvp, ?_, hv, htr⟩
  unfold Rp
  rw [Subring.closure_le]
  rintro x (⟨y, rfl⟩ | hx)
  · show algebraMap (K0 p) (ea_K Y) (algebraMap (WW p) (K0 p) y) ∈ R'
    rw [IsScalarTower.algebraMap_apply (K0 p) Y.Kc (ea_K Y)]
    exact (htr _).2 (Y.witt_mem_integers_Cp y)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rcases hv x with h | h
    · exact h
    · by_cases h0 : x = 0
      · rw [h0]; exact R'.zero_mem
      have e : x = (p : ea_K Y) * x⁻¹ ^ (p ^ 2 - 1 - 1) := by
        rw [← hvp]
        have : x ^ (p ^ 2 - 1) = x ^ (p ^ 2 - 1 - 1) * x := by
          rw [← pow_succ, Nat.sub_add_cancel hn]
        rw [this, inv_pow, mul_comm (x ^ (p ^ 2 - 1 - 1)), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ h0), mul_one]
      show x ∈ R'
      rw [e]
      exact R'.mul_mem (natCast_mem R' p) (R'.pow_mem h _)

theorem ea_geC_of (Y : Pend X) {K' : Type} [Field K'] [Algebra Y.Kc K'] (R' : Subring K')
    (htr : ∀ x : Y.Kc, algebraMap Y.Kc K' x ∈ R' ↔ x ∈ Y.Oc) {x : Y.Kc} {g : ℝ}
    (h : ea_geR p R' (algebraMap Y.Kc K' x) g) : Y.geC x g := by
  intro a b hb hab
  have h1 := h a b hb hab
  rw [← (htr _)]
  rwa [map_mul, map_pow, map_zpow₀, map_natCast]

theorem ea_applyD_map {σ τ K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ K) :
    applyD P (MvPowerSeries.map φ f) = MvPolynomial.map φ (applyD P f) := by
  unfold applyD
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have e : φ.comp (Int.castRingHom K) = Int.castRingHom K' := RingHom.ext_int _ _
  have e2 : φ (∏ x ∈ n.support, ((n x).factorial : K)) = ∏ x ∈ n.support, ((n x).factorial : K') := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun x _ => map_natCast φ _
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map φ), MvPolynomial.map_C,
    MvPolynomial.map_map, e, MvPowerSeries.coeff_map, map_mul φ, e2]

def ea_InClassA (X : Sys p) {K' : Type} [Field K'] (R' : Subring K') (j : ℕ) (h F : MvPowerSeries (X.ZA j) K') : Prop :=
  ∃ g : ℕ → MvPowerSeries (X.ZA j) K', (∀ i, IntR R' (g i)) ∧ ∀ α : X.ZA j →₀ ℕ,
    MvPowerSeries.coeff α F = ∑ i ∈ range (α.degree + 1),
      (((p : K') ^ i)⁻¹ * MvPowerSeries.coeff α (h ^ i * g i))

def ea_RestSU (X : Sys p) (Y : Pend X) : Prop :=
  DworkLemma p → BeProp p Y.be → ∀ (v : X.Pl) (j : ℕ) (U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc),
    IntR Y.Oc (inParamK p Y.Kc U) →
    ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra Y.Kc K'] [IsScalarTower (K0 p) Y.Kc K'] (R' : Subring K')
      (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ Y.Oc, algebraMap Y.Kc K' x ∈ R') →
      ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ R') ∧
        ea_InClassA X R' j (X.hhA K' j v u) (atPi vp (MvPowerSeries.map (algebraMap Y.Kc K')
          (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U))))

structure ea_Cls (X : Sys p) (j : ℕ) (v : X.Pl) (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K') (vp : K')
    (F : MvPowerSeries (X.ZA j) K') : Prop where
  vp_pow : vp ^ (p ^ 2 - 1) = (p : K')
  Rp_le : Rp p K' vp ≤ R'
  val : ∀ x : K', x ∈ R' ∨ x⁻¹ ∈ R'
  cls : ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ R') ∧ ea_InClassA X R' j (X.hhA K' j v u) (atPi vp F)

def SeriesGaussValuationFirst (X : Sys p) : Prop :=
  ∀ (v : X.Pl), ∀ j < X.mm, ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K') (vp : K')
    (F : MvPowerSeries (X.ZA j) K'), ea_Cls X j v K' R' vp F → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      ea_geR p R' (MvPolynomial.coeff n (applyD (X.PIv j I v) F)) (X.g0v v (j + 1))

def SeriesGaussValuationSecond (X : Sys p) : Prop :=
  ∀ (v : X.Pl), ∀ j < X.mm, ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K') (vp : K')
    (F : MvPowerSeries (X.ZA j) K'), ea_Cls X j v K' R' vp F → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      ea_geR p R' (MvPolynomial.coeff n (applyD (X.PIv j I v) F)) (X.gv v (j + 1) - X.alEven v)

def ea_RestKerB (X : Sys p) : Prop :=
  ∀ (v : X.Pl), ∀ j < X.mm, ∀ i ∈ Icc 1 X.G.P.r, ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K')
    (vp : K') (F : MvPowerSeries (X.ZA j) K'), ea_Cls X j v K' R' vp F → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      ea_geR p R' (MvPolynomial.coeff n (applyD (PIvS X j I (fun _ => i) v) F)) (X.gv v (j + 1))

theorem ea_low (D : Formalism.BasicNotions.D7) (Y : Pend X) (hS : ea_RestSU X Y) (hA : admitted D X Y) (v : X.Pl) (j : ℕ)
    (P : X.ColCh j → MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) (g : ℝ)
    (hK : ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K') (vp : K')
      (F : MvPowerSeries (X.ZA j) K'), ea_Cls X j v K' R' vp F → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      ea_geR p R' (MvPolynomial.coeff n (applyD (P I) F)) g) :
    ∀ U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc, IntR Y.Oc (inParamK p Y.Kc U) →
      ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
        Y.geC (MvPolynomial.coeff n (applyD (P I)
          (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U)))) g := by
  intro U hU I n
  obtain ⟨R', vp, hvp, hRp, hval, htr⟩ := ea_ext Y
  have hcls := hS (hA.1 p) hA.2.2.2.1 v j U hU (ea_K Y) R' vp hvp hRp fun x hx => (htr x).2 hx
  have h1 := hK (ea_K Y) R' vp _ ⟨hvp, hRp, hval, hcls⟩ I n
  rw [ea_applyD_map, MvPolynomial.coeff_map] at h1
  exact ea_geC_of Y R' htr h1

theorem first_theorem_place_of_series (D : Formalism.BasicNotions.D7) (Y : Pend X) (hS : ea_RestSU X Y) (hK : SeriesGaussValuationFirst X) : EntryBoundOfHypotheses X Y D :=
  fun hA v j hj => ea_low D Y hS hA v j (fun I => X.PIv j I v) _ (hK v j hj)

theorem second_lemma_place_of_series (D : Formalism.BasicNotions.D7) (Y : Pend X) (hS : ea_RestSU X Y) (hK : SeriesGaussValuationSecond X) : PlacewiseLowerBoundEvenShift X Y D :=
  fun hA v j hj => ea_low D Y hS hA v j (fun I => X.PIv j I v) _ (hK v j hj)

theorem ea_restBU (D : Formalism.BasicNotions.D7) (Y : Pend X) (hS : ea_RestSU X Y) (hK : ea_RestKerB X) : RestBU X Y D :=
  fun hA v j hj i hi => ea_low D Y hS hA v j (fun I => PIvS X j I (fun _ => i) v) _ (hK v j hj i hi)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IsLatticeBetween
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf.Cnt

open Formalism.MainNotions.G

section Gen

variable {R : Type*} [CommRing R] {M M1 M2 : Type*} [AddCommGroup M] [AddCommGroup M1] [AddCommGroup M2]
  [Module R M] [Module R M1] [Module R M2]

theorem card_eq_of_ker_eq (f1 : M →ₗ[R] M1) (f2 : M →ₗ[R] M2) (h1 : Function.Surjective f1)
    (h2 : Function.Surjective f2) (hk : LinearMap.ker f1 = LinearMap.ker f2) : Nat.card M1 = Nat.card M2 := by
  have e1 := (f1.quotKerEquivOfSurjective h1).toEquiv
  have e2 := (f2.quotKerEquivOfSurjective h2).toEquiv
  have e3 := (Submodule.quotEquivOfEq _ _ hk).toEquiv
  exact Nat.card_congr (e1.symm.trans (e3.trans e2))

theorem card_quot (T S : Submodule R M1) (φ : M →ₗ[R] M1) (hφ : LinearMap.range φ = T) (f2 : M →ₗ[R] M2)
    (h2 : Function.Surjective f2) (hk : ∀ m, φ m ∈ S ↔ f2 m = 0) :
    Nat.card (↥T ⧸ Submodule.comap T.subtype S) = Nat.card M2 := by
  have hmem : ∀ m, φ m ∈ T := fun m => hφ ▸ LinearMap.mem_range_self φ m
  let f1 : M →ₗ[R] (↥T ⧸ Submodule.comap T.subtype S) :=
    (Submodule.comap T.subtype S).mkQ.comp (φ.codRestrict T hmem)
  apply card_eq_of_ker_eq f1 f2 _ h2
  · ext m
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← hk m]
    show (Submodule.comap T.subtype S).mkQ (φ.codRestrict T hmem m) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rfl
  · intro y
    obtain ⟨⟨t, ht⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [← hφ] at ht
    obtain ⟨m, rfl⟩ := ht
    exact ⟨m, rfl⟩

end Gen

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {n : ℕ}

def psi (g : Matrix (Fin n) (Fin n) Qq) : (Fin n → W) →ₗ[W] (Fin n → Qq) :=
  ((Matrix.mulVecLin g).restrictScalars W).comp ((Algebra.linearMap W Qq).compLeft (Fin n))

theorem psi_apply (g : Matrix (Fin n) (Fin n) Qq) (w : Fin n → W) :
    psi g w = g.mulVec (fun c => algebraMap W Qq (w c)) := rfl

theorem mem_colSpan (G : Matrix (Fin n) (Fin n) Qq) (x : Fin n → Qq) :
    x ∈ colSpan W G ↔ ∃ y : Fin n → W, x = G.mulVec (fun c => algebraMap W Qq (y c)) := by
  unfold colSpan
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    funext i
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    funext i
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem range_psi (g : Matrix (Fin n) (Fin n) Qq) : LinearMap.range (psi (W := W) g) = colSpan W g := by
  ext x
  rw [LinearMap.mem_range, mem_colSpan]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩

theorem mulVec_cancel (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) {u v : Fin n → Qq}
    (h : g.mulVec u = g.mulVec v) : u = v := by
  have := congrArg (g⁻¹).mulVec h
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hg] using this

theorem psi_inj (hinj : Function.Injective (algebraMap W Qq)) (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) :
    Function.Injective (psi (W := W) g) := by
  intro a b h
  have := mulVec_cancel g hg h
  funext c
  exact hinj (congrFun this c)

theorem psi_smul_mat (c : Qq) (g : Matrix (Fin n) (Fin n) Qq) (w : Fin n → W) :
    psi (c • g) w = c • psi g w := by
  rw [psi_apply, psi_apply, Matrix.smul_mulVec]

theorem isLattice_between [IsDomain W] [IsPrincipalIdealRing W] [IsFractionRing W Qq] (π : W) (hπ : π ≠ 0)
    (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) (S : Submodule W (Fin n → Qq))
    (h1 : S ≤ colSpan W g) (h2 : ∀ y ∈ colSpan W g, π • y ∈ S) : IsLattice W S := by
  classical
  have hinj := psi_inj (IsFractionRing.injective W Qq) g hg
  set Sb : Submodule W (Fin n → W) := S.comap (psi g) with hSb
  obtain ⟨m, ⟨bS⟩⟩ := Submodule.nonempty_basis_of_pid (Pi.basisFun W (Fin n)) Sb
  have hfin : Module.Finite W Sb := Module.Finite.of_basis bS
  have hfr : Module.finrank W Sb = m := by rw [Module.finrank_eq_card_basis bS, Fintype.card_fin]
  let c : Fin m → (Fin n → Qq) := fun i => psi g (bS i : Fin n → W)
  have hliW : LinearIndependent W c := by
    have := bS.linearIndependent.map' ((psi g).comp Sb.subtype)
      (by rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.2 hinj, Submodule.comap_bot, Submodule.ker_subtype])
    exact this
  have hliQ : LinearIndependent Qq c := (LinearIndependent.iff_fractionRing W Qq).1 hliW
  have hmn : m ≤ n := by
    have := hliQ.fintype_card_le_finrank
    simpa using this
  have hnm : n ≤ m := by
    have hmem : ∀ i : Fin n, π • (Pi.basisFun W (Fin n) i) ∈ Sb := by
      intro i
      show psi g (π • (Pi.basisFun W (Fin n) i)) ∈ S
      rw [map_smul]
      exact h2 _ (by rw [← range_psi]; exact LinearMap.mem_range_self _ _)
    have hli : LinearIndependent W (fun i : Fin n => (⟨π • (Pi.basisFun W (Fin n) i), hmem i⟩ : Sb)) := by
      apply LinearIndependent.of_comp Sb.subtype
      have := (Pi.basisFun W (Fin n)).linearIndependent.map' (π • (LinearMap.id : (Fin n → W) →ₗ[W] (Fin n → W)))
        (by
          rw [LinearMap.ker_eq_bot]
          intro a b hab
          exact smul_right_injective _ hπ hab)
      exact this
    have := hli.fintype_card_le_finrank
    rw [hfr] at this
    simpa using this
  obtain rfl : m = n := le_antisymm hmn hnm
  refine ⟨Matrix.of fun a b => c b a, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det]
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hliQ
  · unfold colSpan
    have e1 : (Set.range fun b : Fin m => fun a => (Matrix.of fun a b => c b a) a b) =
        (psi g).comp Sb.subtype '' Set.range bS := by
      rw [← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, bS.span_eq, Submodule.map_comp, Submodule.map_subtype_top, hSb,
      Submodule.map_comap_eq, range_psi, inf_eq_right.2 h1]

end Formalism.MainNotions.FormalGroupSystem.Pf.Cnt
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LambdaIndexTwo
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Local

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem lambda_index_one (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) : lamI (G.P.lam0 v) s 1 = G.P.lam0 v s ⟨0, by omega⟩ := by
  unfold lamI; rw [dif_pos ⟨le_rfl, by omega⟩]

theorem lambda_index_two (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) : lamI (G.P.lam0 v) s 2 = G.P.lam0 v s ⟨1, by omega⟩ := by
  unfold lamI; rw [dif_pos ⟨by omega, by omega⟩]

theorem nc_w_ge (s : Fin (G.P.n' v)) (j : ℕ) (hj : 1 ≤ j) : Fl.w v 1 s ≤ Fl.w v j s := by
  induction j, hj using Nat.le_induction with
  | base => exact le_rfl
  | succ l hl ih => exact le_trans ih (Fl.w_mono v s l hl)

end Local

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

