import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmAExpand
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.Intersections.LinEmbedAlg

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsFunFieldMulEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def funField {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u v : MRing ι) (a : K → ℕ)
    (hv : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P)),
    IsMultiHomog u a ∧ IsMultiHomog v a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩}

theorem exists_funField_mul_eq {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} [P.IsPrime] {f g : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) (hgP : g ∉ P) :
    ∃ x : funField P, (x : FractionRing (MRing ι ⧸ P)) *
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) := by
  have hv : Ideal.Quotient.mk P g ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  exact ⟨⟨IsLocalization.mk' _ (Ideal.Quotient.mk P f) ⟨_, hv⟩,
    Subring.subset_closure ⟨f, g, a, hv, hf, hg, rfl⟩⟩, IsLocalization.mk'_spec _ _ _⟩

def regularityEmbedding_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (R : Finset ((Σ k, ι k) → ℂ)),
    IsArithVar P 1 → (∀ t ∈ R, t ∈ mcPts P) → (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) →
    ∃ e : R ≃ (funField P →+* ℂ), ∀ (t : R) (u v : MRing ι) (a : K → ℕ),
      IsMultiHomog u a → IsMultiHomog v a → v ∉ P → ∀ x : funField P,
      (x : FractionRing (MRing ι ⧸ P)) *
          algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) →
      e t x * eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) v) =
        eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) u)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem TheoremA.proof (hP0 : ProjectivePointSetting.Statement) (hA' : PropAPrime.Statement) : TheoremA.Statement := by
  intro I hI D S X A hX hA hAb c
  have hfam : IsIntersectionFamily (I T.YBlk S.YIdx) := hI T.YBlk S.YIdx
  have hXs : IsSmoothHerm X := hX.2.1
  obtain ⟨Q, hQdef⟩ : ∃ Q : Polynomial ℝ, Q = ∑ j ∈ Finset.range (D + 1 + 1),
      Polynomial.C (((D + 1).choose j : ℝ) * ((1 / 2 : ℝ) ^ j * I T.YBlk S.YIdx S.YY (D + 1) (mix j X A)) *
        ((-1) ^ j + 1)) * Polynomial.X ^ j := ⟨_, rfl⟩
  have hQc : ∀ m, Q.coeff m = ((D + 1).choose m : ℝ) *
      ((1 / 2 : ℝ) ^ m * I T.YBlk S.YIdx S.YY (D + 1) (mix m X A)) * ((-1) ^ m + 1) := by
    intro m
    rw [hQdef]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · rw [Nat.choose_eq_zero_of_lt (by simpa using hm)]
      simp
  have hQ : Q = tsgPoly D kappa (volPoly D fun j =>
      (1 / 2 : ℝ) ^ j * ptsIntegral S.YY (pot (mix j X A : Fin D → HermLine S.YIdx)) (fun _ => 1)) := by
    ext m
    rw [hQc]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · have h0 : I T.YBlk S.YIdx S.YY (D + 1) (mix 0 X A) = 0 := by
          have hm : (mix 0 X A : Fin (D + 1) → HermLine S.YIdx) = fun _ => A := funext fun i => by simp [mix]
          rw [hm]
          exact hP0 I hI D S A hA hAb
        rw [mul_zero, h0, tsgPoly_coeff_zero]
        simp
      · rw [tsgPoly_volPoly_coeff_even D _ kappa k hk, (even_two_mul k).neg_one_pow]
        by_cases hkD : 2 * k ≤ D + 1
        · rw [hA' I hI D S X A hX hA hAb k hk hkD]
          obtain ⟨i, hi⟩ : ∃ i, 2 * k = i + 1 := ⟨2 * k - 1, by omega⟩
          rw [hi, Nat.add_sub_cancel]
          ring
        · rw [Nat.choose_eq_zero_of_lt (by omega : D + 1 < 2 * k)]
          simp
    · rw [tsgPoly_coeff_odd, (odd_two_mul_add_one k).neg_one_pow]
      simp
  rw [fam_lamLine_expand hfam S.arithYY hA hXs c, fam_lamLine_expand hfam S.arithYY hA hXs (-c), ← mul_add,
    ← hQ, hQdef]
  congr 1
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Int.cast_neg, neg_neg]
  rw [neg_div, neg_pow, div_eq_mul_one_div (c : ℝ) 2, mul_pow]
  ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.LogNormDivSameOrbit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem log_norm_div_sameOrbit {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖) =
      Real.log (‖eval z' (map (Int.castRingHom ℂ) f)‖ / ‖eval z' (map (Int.castRingHom ℂ) g)‖) := by
  obtain ⟨c, hc, rfl⟩ := h
  have hc0 : ‖∏ k, c k ^ a k‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  rw [eval_smul_homog f a hf c z', eval_smul_homog g a hg c z', norm_mul, norm_mul,
    mul_div_mul_left _ _ hc0]

theorem RegularityProductFormula.proof (hPts : regularityPointsSum_holds.Statement) (hVert : VerticalClosedPoints.Statement) :
    RegularityProductFormula.Statement := by
  intro K _ ι _ P f g a hP hf hg hfP hgP
  obtain ⟨R, hRP, hRu, hsum⟩ := hPts K ι P hP
  rw [hVert K ι P f g a R hP hf hg hfP hgP hRP hRu]
  exact (hsum _ fun z z' _ h => log_norm_div_sameOrbit hf hg h).symm

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLinEmbed
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 LinEmbed

theorem LinEmbed.proof : LinEmbed.Statement := by
  intro F _ K K' _ _ ι ι' _ _ e A hA I I' hI hI' V d L hV
  induction d generalizing V with
  | zero =>
    have hV' := isProjVarF_comap hA hV
    have hi : IsChart V fun k => (hV.1.2.2 k).choose := fun k => (hV.1.2.2 k).choose_spec
    have hi' : IsChart (V.comap (blockLinSubst e A).toRingHom) fun k' => (hV'.1.2.2 k').choose :=
      fun k' => (hV'.1.2.2 k').choose_spec
    rw [hI'.1 _ _ _ hV' hi', hI.1 V L _ hV hi, ptDeg_comap hA hV hi hi']
  | succ n ih =>
    obtain ⟨L0, a, rfl⟩ : ∃ (L0 : Fin n → K → ℤ) (a : K → ℤ),
        L = Fin.snoc (α := fun _ => K → ℤ) L0 a :=
      ⟨Fin.init L, L (Fin.last n), (Fin.snoc_init_self L).symm⟩
    have hL : (fun j => Fin.snoc (α := fun _ => K → ℤ) L0 a j ∘ e) =
        Fin.snoc (α := fun _ => K' → ℤ) (fun j => L0 j ∘ e) (a ∘ e) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc]
    have hV' := isProjVarF_comap hA hV
    set i' : ∀ k', ι' k' := fun k' => (hV'.1.2.2 k').choose
    have hi' : IsChart (V.comap (blockLinSubst e A).toRingHom) i' := fun k' => (hV'.1.2.2 k').choose_spec
    have hf' := isMultiHomog_coordProd (F := F) i' (fun k' => (a (e k')).toNat)
    have hg' := isMultiHomog_coordProd (F := F) i' (fun k' => (-a (e k')).toNat)
    have hf'V := coordProd_not_mem hV'.1.1 i' hi' (fun k' => (a (e k')).toNat)
    have hg'V := coordProd_not_mem hV'.1.1 i' hi' (fun k' => (-a (e k')).toNat)
    have hsec' : IsRatSection (V.comap (blockLinSubst e A).toRingHom) (a ∘ e) _ _ :=
      ⟨_, _, hf', hg', hf'V, hg'V, fun k' => Int.toNat_sub_toNat_neg _⟩
    have hφf := isMultiHomog_blockLinSubst (A := A) hf'
    have hφg := isMultiHomog_blockLinSubst (A := A) hg'
    have hsec : IsRatSection V a (blockLinSubst e A (∏ k', (X ⟨k', i' k'⟩ : MRingOver F ι') ^ (a (e k')).toNat))
        (blockLinSubst e A (∏ k', (X ⟨k', i' k'⟩ : MRingOver F ι') ^ (-a (e k')).toNat)) :=
      ⟨_, _, hφf, hφg, hf'V, hg'V, fun k => by
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
        exact Int.toNat_sub_toNat_neg _⟩
    rw [hL, hI'.2 _ n _ _ _ _ hV' hsec', hI.2 V n L0 a _ _ hV hsec, ratDiv_comap hA,
      cycEval_mapDomain]
    refine cycEval_congr fun W hW => ?_
    have hmem : W ∈ divSupp V (blockLinSubst e A (∏ k', (X ⟨k', i' k'⟩ : MRingOver F ι') ^ (a (e k')).toNat)) ∨
        W ∈ divSupp V (blockLinSubst e A (∏ k', (X ⟨k', i' k'⟩ : MRingOver F ι') ^ (-a (e k')).toNat)) := by
      by_contra h
      push Not at h
      apply hW
      simp only [ratDiv, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply,
        DivisorCycleSwap.divCycle_apply_of_not_mem h.1, DivisorCycleSwap.divCycle_apply_of_not_mem h.2, Nat.cast_zero, sub_zero]
    have hWn : IsProjVarF W n :=
      hmem.elim (isProjVarF_of_mem_divSupp hV hφf hf'V) (isProjVarF_of_mem_divSupp hV hφg hg'V)
    exact ih W L0 hWn

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

section Statements

def DiagForms.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
      ∃ (n : ℕ) (g h : MRing (T.wwIdx ι ν κ)), IsMultiHomog g (T.wwDeg n 1) ∧
        IsMultiHomog h (T.wwDeg (n + 3) 0) ∧ h ∉ T.wwIdeal x δ e φ (a 0) (a 1) ∧
        aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h

def DiagOrd.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ (n : ℕ) (g h : MRing (T.wwIdx ι ν κ)), IsMultiHomog g (T.wwDeg n 1) →
      IsMultiHomog h (T.wwDeg (n + 3) 0) → h ∉ T.wwIdeal x δ e φ (a 0) (a 1) →
      aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h →
        T.wwIdeal x δ e φ (a 0) (a 0) ∈ divSupp (T.wwIdeal x δ e φ (a 0) (a 1)) (g * h) ∧
        ∀ W ∈ divSupp (T.wwIdeal x δ e φ (a 0) (a 1)) (g * h),
          (multAt (T.wwIdeal x δ e φ (a 0) (a 1) ⊔ Ideal.span {g}) W : ℤ) -
              multAt (T.wwIdeal x δ e φ (a 0) (a 1) ⊔ Ideal.span {h}) W =
            if W = T.wwIdeal x δ e φ (a 0) (a 0) then 1 else 0

end Statements

section Inhabit

end Inhabit

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagPull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def DiagPull.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.DiagPullStatement (Φ := Φ) x δ e φ

end

end GroundTheory.Heights₂.Heights.Inter
end

