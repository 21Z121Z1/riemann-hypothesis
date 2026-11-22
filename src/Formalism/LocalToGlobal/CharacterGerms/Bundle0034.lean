import Formalism.LocalToGlobal.CharacterGerms.Bundle0031
import Formalism.LocalToGlobal.CharacterGerms.PderivDoubleMultiplicationJacobian
import Formalism.LocalToGlobal.CharacterGerms.Bundle0026
import Formalism.LocalToGlobal.CharacterGerms.CoeffLMulCvFrob
import Formalism.LocalToGlobal.CharacterGerms.Bundle0032
import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyRes2
import Formalism.LocalToGlobal.CharacterGerms.Bundle0033
import Formalism.LocalToGlobal.CharacterGerms.Bundle0020
import Formalism.LocalToGlobal.CharacterGerms.Bundle0030

-- bundled from Formalism.LocalToGlobal.CharacterGerms.CoeffSliceMultiplication
section
noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace CocycleSliceMultiplication

open PartialDerivEval CocycleIdentity CocycleCoordinateParts

section Gen

variable {C : Type} [Field C] {V : VF C} {σ : Type}

def FrobG (V : VF C) (F : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, (∃ s, ¬ V.l ∣ μ s) → V.MM (coeff μ F)

end Gen

section Ser

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def z1 (ζ : Fin dd →₀ ℕ) : Fin 1 × Fin dd →₀ ℕ := ζ.mapDomain fun j => ((0 : Fin 1), j)

theorem z2 : Z0 (![pt C dd 2] : Fin 1 → Pt C 3 dd) := by
  intro k i
  simp [pt]

variable {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)

def TT (ν : Fin 2 × Fin dd →₀ ℕ) (ζ : Fin dd →₀ ℕ) (d : Fin 3 × Fin dd →₀ ℕ) : C :=
  coeff d Y.B.ph1 * (if lpart d = ν then coeff (z1 ζ) (∏ j, Y.nmul V.l j ^ d ((2 : Fin 3), j)) else 0)

end Ser

section Facts

variable {dd : ℕ}

def gg (ν : Fin 2 × Fin dd →₀ ℕ) (j : Fin dd) : Fin 3 × Fin dd →₀ ℕ := lo ν + zup (Finsupp.single j 1)

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)

end Facts

section Slice

variable {dd : ℕ} {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
  (Y : FBChart C V O dd)

end Slice

end CocycleSliceMultiplication

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ConstantZeroRestrictPoints
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def up (m : ℕ) : Fin m × Fin dd → Fin (m + 1) × Fin dd := fun p => (p.1.succ, p.2)

theorem up_inj (m : ℕ) : Function.Injective (up (dd := dd) m) := by
  intro a b h
  simp only [up, Prod.mk.injEq, Fin.succ_inj] at h
  exact Prod.ext h.1 h.2

def rz (m : ℕ) : Fin (m + 1) → Pt C m dd := Fin.cons 0 (fun k => pt C dd k)

theorem constant_zero_restrict_points (m : ℕ) : Z0 (rz (C := C) (dd := dd) m) := by
  intro k i
  refine Fin.cases ?_ (fun k => ?_) k
  · show MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin m × Fin dd) C) = 0
    simp
  · exact MvPowerSeries.constantCoeff_X (R := C) (k, i)

theorem rz_zero (m : ℕ) (i : Fin dd) : rz (C := C) (dd := dd) m 0 i = 0 := rfl

theorem up_ne_zero (m : ℕ) (i : Fin dd) : ((0 : Fin (m + 1)), i) ∉ Set.range (up (dd := dd) m) := by
  rintro ⟨p, hp⟩
  exact Fin.succ_ne_zero _ (congrArg Prod.fst hp)

theorem coeff_rz (m : ℕ) (f : PS C (m + 1) dd) (ν : Fin m × Fin dd →₀ ℕ) :
    coeff ν (ev (rz m) f) = coeff (ν.mapDomain (up m)) f := by
  unfold ev
  rw [coeff_subst (hasSubst_ev (constant_zero_restrict_points m)), finsum_eq_single _ (ν.mapDomain (up m))]
  · rw [Finsupp.prod_mapDomain_index_inj (up_inj m)]
    have e : (ν.prod fun t e => (fun p : Fin (m + 1) × Fin dd => rz (C := C) (dd := dd) m p.1 p.2) (up m t) ^ e) =
        monomial ν (1 : C) := by
      have h1 := monomial_eq (R := C) ν (fun _ => (1 : C))
      simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
      rw [Finsupp.prod, h1]
      rfl
    rw [e, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    by_cases hx : ∃ j, d ((0 : Fin (m + 1)), j) ≠ 0
    · obtain ⟨j, hj⟩ := hx
      rw [Finsupp.prod, Finset.prod_eq_zero (i := ((0 : Fin (m + 1)), j)) (Finsupp.mem_support_iff.2 hj)
        (by show (rz (C := C) (dd := dd) m 0 j) ^ _ = 0; rw [rz_zero]; exact zero_pow hj),
        map_zero, smul_zero]
    · push_neg at hx
      have hsub : ↑d.support ⊆ Set.range (up (dd := dd) m) := by
        intro s hs
        obtain ⟨s1, s2⟩ := s
        have hs1 : s1 ≠ 0 := by
          rintro rfl
          exact (Finsupp.mem_support_iff.1 hs) (hx s2)
        exact ⟨(s1.pred hs1, s2), by simp [up, Fin.succ_pred]⟩
      set e := Finsupp.comapDomain (up m) d ((up_inj m).injOn) with he
      have hde : e.mapDomain (up m) = d := Finsupp.mapDomain_comapDomain _ (up_inj m) d hsub
      have hne : e ≠ ν := by
        intro h; apply hd; rw [← hde, h]
      rw [← hde, Finsupp.prod_mapDomain_index_inj (up_inj m)]
      have e2 : (e.prod fun t k => (fun p : Fin (m + 1) × Fin dd => rz (C := C) (dd := dd) m p.1 p.2) (up m t) ^ k) =
          monomial e (1 : C) := by
        have h1 := monomial_eq (R := C) e (fun _ => (1 : C))
        simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
        rw [Finsupp.prod, h1]
        rfl
      rw [e2, coeff_monomial, if_neg (Ne.symm hne), smul_zero]

theorem coeff_iter_pderiv {σ : Type} (q : σ) (L : ℕ) (f : MvPowerSeries σ C) (n : σ →₀ ℕ) :
    coeff n ((pderiv C q)^[L] f) =
      coeff (n + L • Finsupp.single q 1) f * ∏ r ∈ Finset.range L, ((n q : C) + r + 1) := by
  induction L generalizing f with
  | zero => simp
  | succ L ih =>
    have h1 : n + (L + 1) • Finsupp.single q 1 = n + L • Finsupp.single q 1 + Finsupp.single q 1 := by
      rw [add_smul, one_smul, add_assoc]
    rw [Function.iterate_succ_apply, ih, coeff_pderiv, Finset.prod_range_succ, h1]
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    ring

theorem coeff_rz_iter (m : ℕ) (i : Fin dd) (L : ℕ) (f : PS C (m + 1) dd) (ν : Fin m × Fin dd →₀ ℕ) :
    coeff ν (ev (rz m) ((pderiv C ((0 : Fin (m + 1)), i))^[L] f)) =
      (L.factorial : C) * coeff (Finsupp.single ((0 : Fin (m + 1)), i) L + ν.mapDomain (up m)) f := by
  rw [coeff_rz, coeff_iter_pderiv, Finsupp.mapDomain_notin_range _ _ (up_ne_zero m i)]
  simp only [Nat.cast_zero, zero_add]
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, Finsupp.smul_single_one,
    add_comm (Finsupp.mapDomain (up m) ν)]
  push_cast
  ring

end Formalism.L2.FormalSeriesBounds.FunEq
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.FirstVanishingCore
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LogarithmSeriesLinearTerm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem lg0 (Y : FBChart C V O dd) (j : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg j)) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) (Y.lg j) = 0
  rw [Finsupp.mapDomain_zero, Y.lg_lin j 0 (by simp), MvPowerSeries.coeff_zero_X]

theorem exlg (Y : FBChart C V O dd) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex i)) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  rw [uncurry_comp Y.lg_const, Y.ex_lg]
  exact uncurry_X i

theorem ex_lg_at' (Y : FBChart C V O dd) {τ : Type} (A : Fin dd → MvPowerSeries τ C)
    (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst A (un1 (Y.lg j))) (un1 (Y.ex i)) = A i := by
  have hA' := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
  have hL : MvPowerSeries.HasSubst (fun j => un1 (Y.lg j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (lg0 Y)
  rw [← MvPowerSeries.subst_comp_subst_apply hL hA', exlg Y, MvPowerSeries.subst_X hA']

theorem lin (Y : FBChart C V O dd) (i : Fin dd) (μ : Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ (un1 (Y.lg i)) = MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  have hinj : Function.Injective (fun x : Fin dd => ((0 : Fin 1), x)) := fun a b h => (Prod.mk.inj h).2
  show MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) μ) (Y.lg i) = _
  rw [Y.lg_lin i _ (by rw [Finsupp.degree_mapDomain]; exact hμ), MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
  congr 1
  apply propext
  rw [← Finsupp.mapDomain_single, (Finsupp.mapDomain_injective hinj).eq_iff]

theorem coeff1_of_lgLin (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) {U : Fin dd → C}
    (hL : Y.LgLin γ U) (i : Fin dd) : PowerSeries.coeff 1 (γ i) = U i := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hlin : Agr 2 (un1 (Y.lg i)) (MvPowerSeries.X i) := fun e he => lin Y i e (by omega)
  have h2 := agr_subst_right (a := γ) hγ0 hlin
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0)] at h2
  have h3 := (hL i).mono (show 2 ≤ V.l ^ 2 by nlinarith)
  have h4 := (h2.symm.trans h3) (Finsupp.single () 1) (by rw [Finsupp.degree_single]; omega)
  change PowerSeries.coeff 1 (γ i) = PowerSeries.coeff 1 _ at h4
  rw [h4, map_smul, coeffX', if_pos rfl, smul_eq_mul, mul_one]

theorem lg_mulCv' (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C}
    (hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0) (n : ℕ) (j : Fin dd) :
    MvPowerSeries.subst (fun k => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F n k))
        (un1 (Y.lg j)) = (n : C) • alongCv γ (un1 (Y.lg j)) := by
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hM : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => mulL Y.B.G.F n q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G n q.2
  have hL0 : ∀ k, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F n k)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_subst_eq_zero hG (fun q => hγ0 q.2) (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G n k)
  have h := congrArg (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2)) (MulLFrob.lg_mulL Y n j)
  rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply hM hG,
    show (n • Y.lg j) = (n : C) • Y.lg j from (Nat.cast_smul_eq_nsmul C n _).symm,
    MvPowerSeries.subst_smul hG] at h
  show _ = (n : C) • MvPowerSeries.subst γ (un1 (Y.lg j))
  rw [subst_singlePointUncurry hL0, subst_singlePointUncurry hγ0]
  exact h

theorem coeff_l_mulCv_core (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) {U : Fin dd → C}
    (hL : Y.LgLin γ U) (k : Fin dd) :
    V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k))) := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hL0 : ∀ k, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_subst_eq_zero hG (fun q => hγ0 q.2) (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l k)
  have hX0 : ∀ (a : C), MvPowerSeries.constantCoeff (a • (MvPowerSeries.X () : PowerSeries C)) = 0 := by
    intro a
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hcl : ∀ j, MvPowerSeries.constantCoeff (alongCv γ (un1 (Y.lg j))) = 0 := fun j =>
    MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0) hγ0 (lg0 Y j)
  have eL := ex_lg_at' Y _ hL0 k
  simp only [lg_mulCv' Y hγ0 V.l] at eL
  have hAL : Agr (V.l ^ 2) (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k))
      (MvPowerSeries.subst (fun j => ((V.l : C) * U j) • (MvPowerSeries.X () : PowerSeries C)) (un1 (Y.ex k))) := by
    rw [← eL]
    refine agr_subst_left (fun j => by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hcl j, mul_zero])
      (fun j => hX0 _) (fun j => ?_) _
    have := FirstVanishing.Agr.smul (hL j) (V.l : C)
    rwa [smul_smul] at this
  have eG := ex_lg_at' Y γ hγ0 k
  have hAG : Agr (V.l ^ 2) (γ k)
      (MvPowerSeries.subst (fun j => U j • (MvPowerSeries.X () : PowerSeries C)) (un1 (Y.ex k))) := by
    rw [← eG]
    exact agr_subst_left hcl (fun j => hX0 _) (fun j => hL j) _
  have hdeg : (Finsupp.single () V.l).degree < V.l ^ 2 := by
    rw [Finsupp.degree_single]
    nlinarith
  have e1 := hAL _ hdeg
  have e2 := hAG _ hdeg
  change PowerSeries.coeff V.l _ = PowerSeries.coeff V.l _ at e1 e2
  rw [e1, FirstVanishing.coeff_subst_scale, ← e2]
  obtain ⟨m, hm⟩ : ∃ m, V.l = m + 1 := ⟨V.l - 1, by omega⟩
  have e3 : (V.l : C) ^ V.l = (V.l : C) * (V.l : C) ^ m := by
    rw [← pow_succ', ← hm]
  rw [e3, mul_assoc]
  exact mm_l_mul ((VF.Ge.pow (ge_natCast V.l) m).mul_int ((hγ k).2 V.l))

end LogarithmSeriesLinearTerm

theorem first_vanishing_core : FirstVanishingCore := by
  intro C _ _ V O _ _ dd Y γ U hγ hL k
  have hB := LogarithmSeriesLinearTerm.coeff_l_mulCv_core Y hγ hL k
  have hA := FirstVanishing.coeff_l_mulCv_frob Y hγ k
  simp only [LogarithmSeriesLinearTerm.coeff1_of_lgLin Y hγ hL] at hA
  have h := MaximalIdealCongruence.mm_sub hB hA
  rwa [sub_sub_cancel] at h

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.FrobPowSmul
section
noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem frobPow_smul : ∀ (C : Type) [Field C] (V : VF C) (σ : Type) (f : MvPowerSeries σ C), IntS V f →
    ∀ μ : σ →₀ ℕ, V.MM (MvPowerSeries.coeff (V.l • μ) (f ^ V.l) - MvPowerSeries.coeff μ f ^ V.l) := by
  intro C _ V σ f hf μ
  have hl : 0 < V.l := V.l_prime.pos
  have h := PhPowP.frobPowMv f hf (V.l • μ)
  have hdiv : ∀ t, V.l ∣ (V.l • μ) t := fun t => by simp [Finsupp.smul_apply]
  have hdl : PhPowP.divL V.l (V.l • μ) = μ := by
    ext t
    rw [PhPowP.divL_apply, Finsupp.smul_apply, smul_eq_mul, Nat.mul_div_cancel_left _ hl]
  rw [if_pos hdiv, hdl] at h
  exact h

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ProjFBOfEig
section
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

theorem projFB_of_eig (hE : KeyEigSt) : ProjFBSt := projFB_of_eig_res hE RowTiePKeyRes.keyRes_holds

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.PullbackLogCoordsEvalZero
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def exZero (Y : FBChart C V O dd) : Fin 2 × Fin dd → MvPowerSeries (Fin dd) C :=
  fun q => if q.1 = 0 then un1 (Y.ex q.2) else 0

def ExpODESt (Y : FBChart C V O dd) : Prop :=
  ∀ i j : Fin dd, MvPowerSeries.pderiv C i (un1 (Y.ex j)) =
    MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.FK C j))

namespace VP

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

def Mu : WVO I → Fin dd → C := fun w i => (p w.1).u w.2.1 w.2.2 i

theorem expAll_eq (x : Fin dd) : expAll Y p x = MvPowerSeries.subst (linS (Mu Y p)) (un1 (Y.ex x)) := rfl

theorem cc_exZero (q : Fin 2 × Fin dd) : MvPowerSeries.constantCoeff (exZero Y q) = 0 := by
  unfold exZero
  split_ifs
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.ex q.2) = 0
    rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Y.ex_const _
  · exact map_zero _

theorem subst_zero' {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.subst a (0 : MvPowerSeries σ C) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom (Formalism.L2.FormalSeriesBounds.VP.hs ha), map_zero]

theorem pderiv_rowOf {n : ℕ} (b b' : Fin n) (w : WVO I) (E : MvPowerSeries (WVO I) C) :
    MvPowerSeries.pderiv C (b, w) (rowOf b' E) = if b' = b then rowOf b (MvPowerSeries.pderiv C w E) else 0 := by
  unfold rowOf
  rw [Formalism.L2.FormalSeriesBounds.pderiv_subst (Formalism.L2.FormalSeriesBounds.VP.og (fun v => MvPowerSeries.constantCoeff_X _))]
  by_cases h : b' = b
  · subst h
    simp [MvPowerSeries.pderiv_X, Pi.single_apply, Prod.ext_iff]
  · simp [MvPowerSeries.pderiv_X, Pi.single_apply, Prod.ext_iff, h]

theorem constantCoeff_two_points_zero {n : ℕ} (b : Fin n) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd b, 0] : Fin 2 → Pt C n dd) q.1 q.2) = 0 := by
  rcases q with ⟨i, j⟩
  fin_cases i
  · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  · simp

theorem pullback_log_coords_eval_zero {n : ℕ} (b : Fin n) (G : PS C 2 dd) :
    pullN Y p (ev (n := n) ![pt C dd b, 0] G) =
      rowOf b (MvPowerSeries.subst (linS (Mu Y p)) (MvPowerSeries.subst (exZero Y) G)) := by
  have hl : ∀ w, MvPowerSeries.constantCoeff (linS (Mu Y p) w) = 0 :=
    fun w => (Formalism.L2.FormalSeriesBounds.ordGE_one_iff _).1 (Formalism.L2.FormalSeriesBounds.ordGE_linS _ w)
  have h1 : MvPowerSeries.HasSubst
      (fun q : Fin 2 × Fin dd => ((![pt C dd b, 0] : Fin 2 → Pt C n dd) q.1 q.2)) :=
    Formalism.L2.FormalSeriesBounds.VP.hs (fun q => constantCoeff_two_points_zero b q)
  have h2 : MvPowerSeries.HasSubst (fun q : Fin n × Fin dd => rowOf q.1 (expAll Y p q.2)) :=
    Formalism.L2.FormalSeriesBounds.VP.hs (fun q => cc_pullPt Y p q)
  have h3 : MvPowerSeries.HasSubst (exZero Y) := Formalism.L2.FormalSeriesBounds.VP.hs (cc_exZero Y)
  have h4 : MvPowerSeries.HasSubst (linS (Mu Y p)) := Formalism.L2.FormalSeriesBounds.VP.hs hl
  have h5 : MvPowerSeries.HasSubst
      (fun w : WVO I => (MvPowerSeries.X (b, w) : MvPowerSeries (Fin n × WVO I) C)) :=
    Formalism.L2.FormalSeriesBounds.VP.hs (fun w => MvPowerSeries.constantCoeff_X _)
  have h6 : MvPowerSeries.HasSubst (fun q => MvPowerSeries.subst (linS (Mu Y p)) (exZero Y q)) :=
    Formalism.L2.FormalSeriesBounds.VP.hs (fun q => Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero hl (cc_exZero Y q))
  unfold pullN ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  conv_rhs => unfold rowOf
  rw [MvPowerSeries.subst_comp_subst_apply h1 h2, MvPowerSeries.subst_comp_subst_apply h3 h4,
    MvPowerSeries.subst_comp_subst_apply h6 h5]
  congr 1
  funext q
  rcases q with ⟨i, j⟩
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
    rw [MvPowerSeries.subst_X h2]
    simp only [exZero, if_true]
    rw [← expAll_eq]
    rfl
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply]
    simp only [exZero, one_ne_zero, if_false]
    rw [subst_zero' (fun q => cc_pullPt Y p q), subst_zero' hl, subst_zero' (fun w => MvPowerSeries.constantCoeff_X _)]

theorem pderiv_pullN {n : ℕ} (b : Fin n) (w : WVO I) (F : PS C n dd) :
    MvPowerSeries.pderiv C (b, w) (pullN Y p F) =
      ∑ j : Fin dd, rowOf b (MvPowerSeries.pderiv C w (expAll Y p j)) *
        pullN Y p (MvPowerSeries.pderiv C (b, j) F) := by
  unfold pullN
  rw [Formalism.L2.FormalSeriesBounds.pderiv_subst (Formalism.L2.FormalSeriesBounds.VP.og (fun q => cc_pullPt Y p q))]
  simp only [pderiv_rowOf]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp
  · intro a _ hab; simp [hab]
  · simp

end VP

theorem dpull_of_ode {Y : FBChart C V O dd} (p : ∀ o, PairData Y d (I o)) (hE : ExpODESt Y) : DPullSt Y p := by
  intro n b c F
  have hP : MvPowerSeries.HasSubst (fun q : Fin n × Fin dd => rowOf q.1 (expAll Y p q.2)) :=
    VP.hs (fun q => VP.cc_pullPt Y p q)
  have hR : MvPowerSeries.HasSubst
      (fun w : WVO I => (MvPowerSeries.X (b, w) : MvPowerSeries (Fin n × WVO I) C)) :=
    VP.hs (fun w => MvPowerSeries.constantCoeff_X _)
  have hpull : ∀ G : PS C n dd, pullN Y p G = MvPowerSeries.substAlgHom hP G := fun G => by
    rw [MvPowerSeries.coe_substAlgHom]; rfl
  have hrow : ∀ G : MvPowerSeries (WVO I) C, rowOf b G = MvPowerSeries.substAlgHom hR G := fun G => by
    rw [MvPowerSeries.coe_substAlgHom]; rfl
  have key : ∀ j : Fin dd, ∑ w : WVO I, c w • rowOf b (MvPowerSeries.pderiv C w (expAll Y p j)) =
      ∑ i : Fin dd, (∑ w : WVO I, c w * (p w.1).u w.2.1 w.2.2 i) •
        rowOf b (MvPowerSeries.subst (linS (VP.Mu Y p)) (MvPowerSeries.subst (exZero Y)
          (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.FK C j)))) := by
    intro j
    have e1 : ∀ w, MvPowerSeries.pderiv C w (expAll Y p j) = ∑ i : Fin dd, VP.Mu Y p w i •
        MvPowerSeries.subst (linS (VP.Mu Y p)) (MvPowerSeries.subst (exZero Y)
          (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.FK C j))) := by
      intro w
      rw [VP.expAll_eq, Formalism.L2.FormalSeriesBounds.pderiv_subst_linS]
      exact Finset.sum_congr rfl fun i _ => by rw [hE i j]
    simp only [e1, hrow, map_sum, map_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    rfl
  simp only [VP.pderiv_pullN]
  unfold DofN
  simp only [← MvPowerSeries.smul_eq_C_mul]
  rw [hpull, map_sum]
  simp only [map_mul, map_sum, map_smul]
  simp only [← hpull, VP.pullback_log_coords_eval_zero]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [← smul_mul_assoc, ← Finset.sum_mul]
  congr 1
  rw [key j]

theorem logCoord_of_ode {Y : FBChart C V O dd} (p : ∀ o, PairData Y d (I o)) (hE : ExpODESt Y) : LogCoordSt Y p := logCoord_of_dpull (dpull_of_ode p hE)

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePLimSelf
section
noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem limSelf_holds : LimSelfSt := by
  unfold LimSelfSt AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p g x x' hx hlim
  exact LimTy.lim_mem (Y.rawSelf p) V.l_prime.two_le
    (fun i => FBChart.self_chart_log_constantCoeff (Y := Y) (p := p) i)
    (fun i => FBChart.self_chart_exp_constantCoeff (Y := Y) (p := p) i)
    (fun i => FBChart.rawSelf_lgex (Y := Y) (p := p) i)
    (fun i => FBChart.rawSelf_exlg (Y := Y) (p := p) i)
    g x x' hx hlim

end Formalism.L2.FormalSeriesBounds
end
end

