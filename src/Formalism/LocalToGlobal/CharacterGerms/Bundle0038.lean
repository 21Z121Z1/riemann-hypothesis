import Formalism.LocalToGlobal.CharacterGerms.Bundle0037
import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.TripleMultiplicationConstantCoeff
import Formalism.LocalToGlobal.CharacterGerms.Bundle0036
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
import Formalism.LocalToGlobal.CharacterGerms.Bundle0023

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ChartHypothesisOfCharacters
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ChG

open VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem integralSeries_uncurry_one {χ : PS C 1 dd} (h : IntS V χ) : IntS V (un1 χ) := by
  intro μ
  exact h _

def lin {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) (i : Fin dd) : MvPowerSeries (I g) C :=
  ∑ c', p.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)

theorem cc_lin {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) (i : Fin dd) :
    MvPowerSeries.constantCoeff (lin p g i) = 0 := by
  unfold lin
  simp

theorem subst_lin_linF {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) (χ : PS C 1 dd) :
    MvPowerSeries.subst (lin p g) (linF (dlogC χ)) =
      ∑ x : I g, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries (I g) C) := by
  unfold linF
  rw [subst_sum (cc_lin p g)]
  have h1 : ∀ i : Fin dd, MvPowerSeries.subst (lin p g) (dlogC χ i • (MvPowerSeries.X i : MvPowerSeries (Fin dd) C)) =
      ∑ x : I g, (dlogC χ i * p.u g x i) • (MvPowerSeries.X x : MvPowerSeries (I g) C) := by
    intro i
    rw [subst_smul (cc_lin p g), subst_X (cc_lin p g)]
    unfold lin
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold PairData.yOf
  rw [Finset.sum_smul]

end ChG

open ChG VP in
theorem charGerm_holds : CharGermSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p Hc χ hχ g S t ht
  obtain ⟨P, hP0, hPI, -, hPt⟩ := FormalGermZero.sys_P Y p (Hc g) (S g)
  have ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0 := fun g c => (ht g).1 c
  have hI : IntS V (MvPowerSeries.subst P (un1 χ)) := IntS.subst hP0 hPI (integralSeries_uncurry_one hχ.1)
  have key : MvPowerSeries.subst (t g) (MvPowerSeries.subst P (un1 χ)) =
      mvExp (∑ x : I g, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries (I g) C)) := by
    rw [subst_subst hP0 (ht0 g)]
    have h1 : (fun j => MvPowerSeries.subst (t g) (P j)) = fun j => MvPowerSeries.subst (lin p g) (e Y j) := by
      funext j
      exact hPt (t g) (ht g) j
    rw [h1, ← subst_subst (cc_e Y) (cc_lin p g)]
    show MvPowerSeries.subst (lin p g) (Psi Y χ) = _
    rw [chi_exp Y hχ, subst_exp (cc_lin p g) (constantCoeff_linF _), subst_lin_linF]
  refine ⟨upG g (MvPowerSeries.subst P (un1 χ)), ?_, ?_⟩
  · exact IntS.subst (fun _ => cc_X _) (fun _ => IntS_X _) hI
  · rw [AbstractGermZero.upG_subst t ht0 g, key]

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem chart_hypothesis_of_characters (h : CharacterHypothesisCharts Xo c) : CharacterHypothesisAllCharts Xo c :=
  chart_hypothesis_of_character Xo c charGerm_holds h

end Chart

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.GermLiftSelfSt
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

abbrev IS (I0 : Orb → Type) : Orb → Fin 2 → Type := fun o _ => I0 o

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

def uS (w : WVO (IS I0)) : Fin 2 × Fin dd → C := (Y.rawSelf (p w.1)).u w.2.1 w.2.2

def pull2 (F : PS C 2 dd) : MvPowerSeries (WVO (IS I0)) C := VP.linPull Y (uS Y p) F

def MS {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (x : Fin N × WVO (IS I0)) (q : Fin n × Fin dd) : C :=
  ∑ col : Fin 2, if pl (x.1, col) = q.1 then uS Y p x.2 (col, q.2) else 0

def pullS {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (F : PS C n dd) : MvPowerSeries (Fin N × WVO (IS I0)) C :=
  VP.linPull Y (MS Y p pl) F

def UnitSelfSt : Prop :=
  SelfSep Y p → ∃ U : PS C 2 dd, IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0 ∧
    pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)

def GermLiftSelfSt (H : ∀ o, (Y.rawSelf (p o)).Hyps V) : Prop :=
  SelfSep Y p → ∀ (o : Orb) (S : ∀ g, Sys (((Y.rawSelf (p o)).rowData (H o)).G g))
    (t : ∀ _ : Fin 2, I0 o → MvPowerSeries (I0 o) C), (∀ g, (S g).IsT (t g)) →
    ∀ F ∈ IntGerm V t, ∃ G : PS C 2 dd, IntS V G ∧ pull2 Y p G = toAllS (I := IS I0) o F

end Defs

namespace VP

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n)

theorem MS_pl (ρ' ρ : Fin N) (w : WVO (IS I0)) (col : Fin 2) (i : Fin dd) :
    MS Y p pl (ρ', w) (pl (ρ, col), i) = if ρ' = ρ then uS Y p w (col, i) else 0 := by
  simp only [MS, pl.injective.eq_iff, Prod.mk.injEq]
  by_cases h : ρ' = ρ
  · simp [h]
  · simp [h]

theorem MS_off (x : Fin N × WVO (IS I0)) (b : Fin n) (hb : b ∉ Set.range pl) (i : Fin dd) :
    MS Y p pl x (b, i) = 0 := by
  simp only [MS]
  exact Finset.sum_eq_zero fun col _ => if_neg fun h => hb ⟨_, h⟩

theorem linPt_pl (ρ : Fin N) (col : Fin 2) (i : Fin dd) :
    linPt Y (MS Y p pl) (pl (ρ, col), i) = rowOf ρ (linPt Y (uS Y p) (col, i)) := by
  simp only [linPt]
  rw [rowOf_eq, rename_subst_linS]
  congr 1
  funext j
  simp only [linS, colLin, map_sum, map_smul, MvPowerSeries.rename_X]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single ρ]
  · simp only [MS_pl, if_true]
    rfl
  · intro ρ' _ hρ'
    simp [MS_pl, hρ']
  · simp

theorem linPt_off (b : Fin n) (hb : b ∉ Set.range pl) (i : Fin dd) : linPt Y (MS Y p pl) (b, i) = 0 := by
  have h0 : linS (colLin (MS Y p pl) b) = 0 := by
    funext j
    simp [linS, colLin, MS_off Y p pl _ b hb]
  have hc := cc_linPt Y (MS Y p pl) (b, i)
  simp only [linPt, h0, MvPowerSeries.subst_zero_eq_C_constantCoeff] at hc ⊢
  simp at hc
  simp [hc]

theorem cc_ptPl (ρ : Fin N) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] : Fin 2 → Pt C n dd) q.1 q.2) = 0 := by
  obtain ⟨c, i⟩ := q
  fin_cases c <;> simp [pt]

theorem pullS_plane (ρ : Fin N) (G : PS C 2 dd) :
    pullS Y p pl (ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] G) = rowOf ρ (pull2 Y p G) := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
      (![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] : Fin 2 → Pt C n dd) q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_ptPl pl ρ q)
  have hL : MvPowerSeries.HasSubst (linPt Y (MS Y p pl)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  have hL2 : MvPowerSeries.HasSubst (linPt Y (uS Y p)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  have hR : MvPowerSeries.HasSubst (fun w : WVO (IS I0) =>
      (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WVO (IS I0)) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)
  simp only [pullS, pull2, linPull, ev, rowOf]
  rw [MvPowerSeries.subst_comp_subst_apply hA hL, MvPowerSeries.subst_comp_subst_apply hL2 hR]
  congr 1
  funext ⟨c, i⟩
  have hc : (![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] : Fin 2 → Pt C n dd) c i =
      MvPowerSeries.X (pl (ρ, c), i) := by
    fin_cases c <;> rfl
  rw [hc, MvPowerSeries.subst_X hL, linPt_pl]
  rfl

theorem pullS_col (ρ : Fin N) (col : Fin 2) (E : PS C 1 dd) :
    pullS Y p pl (ev (n := n) ![pt C dd (pl (ρ, col))] E) = rowOf ρ (pull2 Y p (ev (n := 2) ![pt C dd col] E)) := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd =>
      (![pt C dd (pl (ρ, col))] : Fin 1 → Pt C n dd) q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by obtain ⟨c, i⟩ := q; fin_cases c; simp [pt])
  have hA' : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd =>
      (![pt C dd col] : Fin 1 → Pt C 2 dd) q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by obtain ⟨c, i⟩ := q; fin_cases c; simp [pt])
  have hL : MvPowerSeries.HasSubst (linPt Y (MS Y p pl)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  have hL2 : MvPowerSeries.HasSubst (linPt Y (uS Y p)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  have hR : MvPowerSeries.HasSubst (fun w : WVO (IS I0) =>
      (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WVO (IS I0)) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)
  have hcol : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => linPt Y (uS Y p) (col, q.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ _)
  have hin : (fun q : Fin 1 × Fin dd => MvPowerSeries.subst (linPt Y (uS Y p))
      ((![pt C dd col] : Fin 1 → Pt C 2 dd) q.1 q.2)) = fun q => linPt Y (uS Y p) (col, q.2) := by
    funext ⟨c, i⟩
    fin_cases c
    exact MvPowerSeries.subst_X hL2 (col, i)
  simp only [pullS, pull2, linPull, ev, rowOf]
  rw [MvPowerSeries.subst_comp_subst_apply hA hL, MvPowerSeries.subst_comp_subst_apply hA' hL2, hin,
    MvPowerSeries.subst_comp_subst_apply hcol hR]
  congr 1
  funext ⟨c, i⟩
  have hc0 : c = 0 := Subsingleton.elim _ _
  subst hc0
  change MvPowerSeries.subst (linPt Y (MS Y p pl)) (MvPowerSeries.X (pl (ρ, col), i)) =
    MvPowerSeries.subst (fun w => MvPowerSeries.X (ρ, w)) (linPt Y (uS Y p) (col, i))
  rw [MvPowerSeries.subst_X hL, linPt_pl]
  rfl

theorem pullS_off (b : Fin n) (hb : b ∉ Set.range pl) (E : PS C 1 dd) :
    pullS Y p pl (ev (n := n) ![pt C dd b] E) = MvPowerSeries.C (MvPowerSeries.constantCoeff E) := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd =>
      (![pt C dd b] : Fin 1 → Pt C n dd) q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by obtain ⟨c, i⟩ := q; fin_cases c; simp [pt])
  have hL : MvPowerSeries.HasSubst (linPt Y (MS Y p pl)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  simp only [pullS, linPull, ev]
  rw [MvPowerSeries.subst_comp_subst_apply hA hL]
  have h0 : (fun q : Fin 1 × Fin dd => MvPowerSeries.subst (linPt Y (MS Y p pl))
      ((![pt C dd b] : Fin 1 → Pt C n dd) q.1 q.2)) = 0 := by
    funext ⟨c, i⟩
    have hc0 : c = 0 := Subsingleton.elim _ _
    subst hc0
    change MvPowerSeries.subst (linPt Y (MS Y p pl)) (MvPowerSeries.X (b, i)) = 0
    rw [MvPowerSeries.subst_X hL, linPt_off Y p pl b hb i]
  rw [h0, MvPowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem hco_of_img {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (ℓ : ι)
    (co : Fin N × WVO (IS I0) → C)
    (h : ∃ ρ col, pl (ρ, col) = cp ℓ ∧ (∀ ρ' w, ρ' ≠ ρ → co (ρ', w) = 0) ∧
      (fun x : Fin 2 × Fin dd => if x.1 = col then uv ℓ x.2 else 0) =
        ∑ w : WVO (IS I0), co (ρ, w) • (Y.rawSelf (p w.1)).u w.2.1 w.2.2) (b : Fin n) (i : Fin dd) :
    ∑ x, co x * MS Y p pl x (b, i) = if b = cp ℓ then uv ℓ i else 0 := by
  obtain ⟨ρ, col, hpl, hco0, hvec⟩ := h
  have key : ∀ c : Fin 2, (∑ x : Fin N × WVO (IS I0),
      co x * (if pl (x.1, c) = b then uS Y p x.2 (c, i) else 0)) =
      if pl (ρ, c) = b then (if c = col then uv ℓ i else 0) else 0 := by
    intro c
    rw [Fintype.sum_prod_type, Finset.sum_eq_single ρ
      (fun ρ' _ hρ' => Finset.sum_eq_zero fun w _ => by simp [hco0 ρ' w hρ']) (by simp)]
    by_cases hb' : pl (ρ, c) = b
    · have h1 := congrFun hvec (c, i)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      simp only [hb', if_true]
      rw [h1]
      rfl
    · simp [hb']
  simp only [MS, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [key]
  rw [Finset.sum_eq_single col (fun c _ hc => by simp [hc]) (by simp)]
  simp only [if_true]
  by_cases hb : b = cp ℓ
  · simp [hb, hpl]
  · have h2 : pl (ρ, col) ≠ b := fun h' => hb (h'.symm.trans hpl)
    simp [h2, hb]

end VP

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.PderivTripleMultiplicationMaximal
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob Formalism.L2.FormalSeriesBounds.LiftedCoordinateEvaluation
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem pderiv_first_unit_series_maximal (Y : FBChart C V O dd) (i : Fin dd) : MaximalIdealCongruence.MMS V (pderiv C ((0 : Fin 2), i) Y.u1) := by
  have hu : Y.u1 = FB.expS C (evl Y V.l Y.h - (V.l : C) • Y.h) := rfl
  have hE0 : constantCoeff (evl Y V.l Y.h - (V.l : C) • Y.h) = 0 := by
    rw [map_sub, show (V.l : C) • Y.h = ((V.l : ℕ) : PS C 2 dd) * Y.h by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul], map_mul, PartialDerivEval.h_const, mul_zero, sub_zero]
    exact FirstUnitSeriesIntegrality.height_multiple_constantCoeff Y V.l
  have hd : pderiv C ((0 : Fin 2), i) Y.u1 =
      (V.l : PS C 2 dd) * (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i) := by
    rw [hu, PartialDerivEval.pderiv_expS hE0, dE, ← hu]; ring
  have hint : IntS V (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i) := by
    refine PartialDerivEval.intS_mul (first_unit_series_integral C V O dd Y)
      (PartialDerivEval.intS_sum _ fun m _ => PartialDerivEval.intS_mul ?_ ?_)
    · have hP : IntS V (Pm Y m) := by
        refine PartialDerivEval.intS_ev constant_zero_lift_triple (fun k j => ?_) (PartialDerivEval.intS_pderiv Y.intPh1 _)
        fin_cases k
        · exact PartialDerivEval.intS_X _
        · exact PartialDerivEval.intS_zero
        · exact PartialDerivEval.intS_X _
      have hP' : IntS V (evl Y V.l (Pm Y m)) := by
        refine PartialDerivEval.intS_ev (constant_zero_double_multiplication Y V.l) (fun k j => ?_) hP
        fin_cases k
        · exact FirstUnitSeriesIntegrality.double_multiplication_integral Y.B.G Y.intF V.l j
        · exact PartialDerivEval.intS_X _
      rw [sub_eq_add_neg]
      exact PartialDerivEval.intS_add hP (PartialDerivEval.intS_neg hP')
    · refine PartialDerivEval.intS_ev (PartialDerivEval.z0_1 _ z0P0) (fun k j => ?_) (MulLFrob.JL_int Y m i)
      fin_cases k
      exact PartialDerivEval.intS_X _
  rw [hd]; exact MaximalIdealCongruence.mms_l_mul hint

theorem int_two {w : Pt C 3 dd} (P : Pt C 3 dd) (hP : ∀ j, IntS V (P j)) (hw : ∀ j, IntS V (w j)) :
    ∀ k j, IntS V ((![P, w] : Fin 2 → Pt C 3 dd) k j) := fun k j => by
  fin_cases k
  · exact hP j
  · exact hw j

theorem triple_coordinate_integral (k : Fin 3) (j : Fin dd) : IntS V ((p3 k : Pt C 3 dd) j) := intS_X _

theorem UU_int (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0)
    (hw : ∀ j, IntS V (w j)) : IntS V (UU Y w) :=
  intS_ev (constant_zero_two_points _ (z0p3 0) hw0) (int_two _ (triple_coordinate_integral 0) hw) (first_unit_series_integral C V O dd Y)

theorem UU_frob (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0)
    (hw : ∀ j, IntS V (w j)) (hd : ∀ i j, pderiv C ((0 : Fin 3), i) (w j) = 0) : FrobD V (UU Y w) := by
  intro i
  unfold UU
  rw [d_ev_keep hw0 i (hd i)]
  exact MaximalIdealCongruence.MMS.ev_of (constant_zero_two_points _ (z0p3 0) hw0) (int_two _ (triple_coordinate_integral 0) hw) (pderiv_first_unit_series_maximal Y i)

theorem UU_one (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0) :
    ev (rz 2) (UU Y w) = 1 := by
  have hz := constant_zero_two_points (p3 0) (z0p3 0) hw0
  have hw' : ∀ j, constantCoeff (ev (rz (C := C) (dd := dd) 2) (w j)) = 0 := fun j => const_ev (constant_zero_restrict_points 2) (hw0 j)
  have hE0 : constantCoeff (ev (n := 3) ![m3 Y.B.G V.l, w] Y.h - (V.l : C) • ev (n := 3) ![p3 0, w] Y.h) = 0 := by
    rw [map_sub, eval_height_constantCoeff Y (triple_multiplication_constantCoeff _ _) hw0, show (V.l : C) • ev (n := 3) ![p3 0, w] Y.h =
      MvPowerSeries.C (V.l : C) * ev (n := 3) ![p3 0, w] Y.h from MvPowerSeries.smul_eq_C_mul _ _, map_mul,
      eval_height_constantCoeff Y (z0p3 0) hw0, mul_zero, sub_zero]
  rw [UU_eq Y w hw0, ev_ex (constant_zero_restrict_points 2) _ hE0, ev_sub (constant_zero_restrict_points 2), ev_smulC (constant_zero_restrict_points 2),
    ev_ev (constant_zero_two_points _ (triple_multiplication_constantCoeff _ _) hw0) (constant_zero_restrict_points 2), ev_ev hz (constant_zero_restrict_points 2)]
  have e1 : (fun k j => ev (rz (C := C) (dd := dd) 2) ((![m3 Y.B.G V.l, w] : Fin 2 → Pt C 3 dd) k j)) =
      ![0, fun j => ev (rz 2) (w j)] := by
    funext k j; fin_cases k
    · exact restrict_triple_multiplication _ _ j
    · rfl
  have e2 : (fun k j => ev (rz (C := C) (dd := dd) 2) ((![p3 0, w] : Fin 2 → Pt C 3 dd) k j)) =
      ![0, fun j => ev (rz 2) (w j)] := by
    funext k j; fin_cases k
    · exact ev_X (constant_zero_restrict_points 2) 0 j
    · rfl
  rw [e1, e2, height_at_zero_first Y _ hw', smul_zero, sub_zero, ex_zero]

theorem constant_zero_triple_multiplication (Y : FBChart C V O dd) : Z0 (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) := fun k j => by
  fin_cases k
  · exact triple_multiplication_constantCoeff _ _ j
  · exact z0p3 1 j
  · exact z0p3 2 j

theorem QQ_int (Y : FBChart C V O dd) : IntS V (QQ Y) := by
  refine intS_ev (constant_zero_triple_multiplication Y) (fun k j => ?_) Y.intPh2
  fin_cases k
  · exact triple_multiplication_integral _ Y.intF _ j
  · exact intS_X _
  · exact intS_X _

theorem pderiv_triple_multiplication (Y : FBChart C V O dd) (k i : Fin dd) :
    pderiv C ((0 : Fin 3), i) (m3 Y.B.G V.l k) = ev ![(p3 0 : Pt C 3 dd)] (Jac (mulL Y.B.G.F V.l) k i) := by
  show pderiv C ((0 : Fin 3), i) (ev ![(p3 0 : Pt C 3 dd)] (mulL Y.B.G.F V.l k)) = _
  rw [pderiv_eval_single (P := (p3 0 : Pt C 3 dd)) (z0p3 0), Finset.sum_eq_single i (fun j _ hj => by
      show _ * pderiv C _ (pt C (n := 3) dd 0 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
  show _ * pderiv C _ (pt C (n := 3) dd 0 i) = _
  rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_pos rfl, mul_one]
  rfl

theorem pderiv_triple_multiplication_maximal (Y : FBChart C V O dd) (k i : Fin dd) : MaximalIdealCongruence.MMS V (pderiv C ((0 : Fin 3), i) (m3 Y.B.G V.l k)) := by
  rw [pderiv_triple_multiplication, jac_l, Matrix.smul_apply, ev_eq_alg (z0_1 _ (z0p3 0)), map_nsmul, ← ev_eq_alg (z0_1 _ (z0p3 0)),
    nsmul_eq_mul]
  refine MaximalIdealCongruence.mms_l_mul (intS_ev (z0_1 _ (z0p3 0)) (fun k' j => by fin_cases k'; exact intS_X _) ?_)
  rw [Matrix.mul_apply]
  refine intS_sum _ fun j _ => intS_mul ?_ (JL_int Y j i)
  refine intS_ev (z0_1 _ (multiplication_constantCoeff_zero Y.B.G V.l)) (fun k' j' => ?_) (JF_int Y k j)
  fin_cases k'
  exact mulL_int Y.B.G Y.intF V.l j'

theorem QQ_frob (Y : FBChart C V O dd) : FrobD V (QQ Y) := by
  intro i
  unfold QQ
  rw [pderiv_eval_triple (constant_zero_triple_multiplication Y)]
  have h1 : ∑ j, ev ![m3 Y.B.G V.l, p3 1, p3 2] (pderiv C ((1 : Fin 3), j) Y.B.ph2) *
      pderiv C ((0 : Fin 3), i) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) 1 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      show _ * pderiv C _ (pt C (n := 3) dd 1 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (1 : Fin 3) ≠ 0), mul_zero]
  have h2 : ∑ j, ev ![m3 Y.B.G V.l, p3 1, p3 2] (pderiv C ((2 : Fin 3), j) Y.B.ph2) *
      pderiv C ((0 : Fin 3), i) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) 2 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      show _ * pderiv C _ (pt C (n := 3) dd 2 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (2 : Fin 3) ≠ 0), mul_zero]
  rw [h1, h2, add_zero, add_zero]
  refine MaximalIdealCongruence.mms_sum _ fun j _ => MaximalIdealCongruence.MMS.mul_left ?_ (pderiv_triple_multiplication_maximal Y j i)
  refine intS_ev (constant_zero_triple_multiplication Y) (fun k m => ?_) (intS_pderiv Y.intPh2 _)
  fin_cases k
  · exact triple_multiplication_integral _ Y.intF _ m
  · exact intS_X _
  · exact intS_X _

theorem rz_eq : (rz (C := C) (dd := dd) 2) = ![0, pt C (n := 2) dd 0, pt C dd 1] := by
  funext k j
  fin_cases k <;> rfl

theorem QQ_one (Y : FBChart C V O dd) : ev (rz 2) (QQ Y) = 1 := by
  unfold QQ
  rw [ev_ev (constant_zero_triple_multiplication Y) (constant_zero_restrict_points 2)]
  have e : (fun k j => ev (rz (C := C) (dd := dd) 2)
      ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) k j)) = ![0, pt C (n := 2) dd 0, pt C dd 1] := by
    funext k j; fin_cases k
    · exact restrict_triple_multiplication _ _ j
    · exact ev_X (constant_zero_restrict_points 2) 1 j
    · exact ev_X (constant_zero_restrict_points 2) 2 j
  rw [e]
  exact Y.B.cocycleRight_zero_fst

theorem second_pairing_restrict_one (Y : FBChart C V O dd) : ev (rz 2) Y.B.ph2 = 1 := by
  rw [rz_eq]; exact Y.B.cocycleRight_zero_fst

theorem second_pairing_pow_restrict_one (Y : FBChart C V O dd) : ev (rz 2) (Y.B.ph2 ^ V.l) = 1 := by
  rw [ev_eq_alg (constant_zero_restrict_points 2), map_pow, ← ev_eq_alg (constant_zero_restrict_points 2), second_pairing_restrict_one, one_pow]

theorem second_pairing_pow_frobenius (Y : FBChart C V O dd) : FrobD V (Y.B.ph2 ^ V.l) := by
  intro i
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  exact MaximalIdealCongruence.mms_l_mul (intS_mul (intS_pow Y.intPh2 _) (intS_pderiv Y.intPh2 _))

end Formalism.L2.FormalSeriesBounds.FunEq
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePPTClose
section
namespace Formalism.L2.FormalSeriesBounds

theorem ptFB_of_proj2 (hP : ProjFBSt) : PTFBSt := ptFB_of_proj hP hStabFB

theorem cartFB_of_proj2 (hP : ProjFBSt) : CartFBSt := cartFB_of_proj hP hStabFB

theorem typical_curves_of_lie (hLie : RowTiePProj.ProjLieSt) : PTFBSt := ptFB_of_lie hLie hStabFB

theorem ptSelf_of_start2 (hS : AllStartSelfSt) : PTSelfSt :=
  ptSelf_of_start hS OActSelf.oActSelf_holds hStabSelf_holds

theorem ptAvgSelf_holds : PTAvgSelfSt := ptAvgSelf_of OActSelf.oActSelf_holds limSelf_holds

end Formalism.L2.FormalSeriesBounds
end

