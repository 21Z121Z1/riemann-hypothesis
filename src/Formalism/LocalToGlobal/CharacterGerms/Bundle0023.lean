import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
import Formalism.LocalToGlobal.CharacterGerms.Bundle0020
import Formalism.LocalToGlobal.CharacterGerms.Bundle0021
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
import Formalism.LocalToGlobal.CharacterGerms.Bundle0019
import Formalism.LocalToGlobal.CharacterGerms.Bundle0008
import Formalism.DropLevelBounds.ConstantCoeffVanishing.UbintConstantCoeffEqZero

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section Rename₂

theorem coeff_rename_outside {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (ν : τ →₀ ℕ) {s : τ}
    (hs : ν s ≠ 0) (hr : ∀ x, φ x ≠ s) :
    coeff ν (MvPowerSeries.subst (fun x => (X (φ x) : MvPowerSeries τ C)) F) = 0 := by
  refine coeff_subst_rename_out φ F ν fun e' he => hs ?_
  rw [← he]
  exact Finsupp.mapDomain_notin_range _ _ (by rintro ⟨x, hx⟩; exact hr x hx)

variable {dd : ℕ}

theorem coeff_hCol (h : PS C 2 dd) (col c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (hCol col h) =
      if c1 = col ∧ c2 = col then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by
  unfold hCol
  split_ifs with hc
  · obtain ⟨h1, h2⟩ := hc
    rw [h1, h2]
    have hφ : Function.Injective (fun p : Fin 2 × Fin dd => (p.1, (col, p.2))) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext hab.1 hab.2.2
    have he : E2 ((0 : Fin 2), (col, i)) ((1 : Fin 2), (col, j)) =
        (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)).mapDomain (fun p : Fin 2 × Fin dd => (p.1, (col, p.2))) := by
      simp [E2, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    rw [he, coeff_subst_rename_inj _ hφ]
  · by_cases h1 : c1 = col
    · have h2 : c2 ≠ col := fun h2 => hc ⟨h1, h2⟩
      refine coeff_rename_outside _ h (E2 _ _) (s := ((1 : Fin 2), (c2, j))) ?_ ?_
      · simp [E2, Finsupp.single_apply]
      · intro x hx
        simp only [Prod.mk.injEq] at hx
        exact h2 hx.2.1.symm
    · refine coeff_rename_outside _ h (E2 _ _) (s := ((0 : Fin 2), (c1, i))) ?_ ?_
      · simp [E2, Finsupp.single_apply]
      · intro x hx
        simp only [Prod.mk.injEq] at hx
        exact h1 hx.2.1.symm

end Rename₂

section Self

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I0 : Type} [Fintype I0]

theorem coeff_E2_sum_hCol_eq_ite (h : PS C 2 dd) (c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (∑ col, hCol col h) =
      if c1 = c2 then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by
  rw [map_sum]
  simp only [coeff_hCol]
  rw [Fin.sum_univ_two]
  by_cases h12 : c1 = c2
  · subst h12
    fin_cases c1 <;> simp
  · fin_cases c1 <;> fin_cases c2 <;> simp_all

theorem FBChart.self_raw_first_pairing_eq (Y : FBChart C V O dd) (p : SelfData Y d I0) (w v : Fin 2 × Fin dd → C) :
    (Y.rawSelf p).sg1 w v = -∑ col, bil Y.h (fun i => w (col, i)) (fun j => v (col, j)) := by
  have hsg : ∀ x : Fin 2 × Fin dd, MvPowerSeries.coeff (Finsupp.single x 1) ((Y.rawSelf p).sg v) =
      -∑ i : Fin 2 × Fin dd, v i *
        (if x.1 = i.1 then MvPowerSeries.coeff (E2 ((0 : Fin 2), x.2) ((1 : Fin 2), i.2)) Y.h else 0) := by
    intro x
    show (-∑ i, v i * MvPowerSeries.coeff ((Finsupp.single x 1).mapDomain (fun y => ((0 : Fin 2), y)) +
      Finsupp.single ((1 : Fin 2), i) 1) (∑ col, hCol col Y.h)) = _
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.mapDomain_single]
    rw [show Finsupp.single ((0 : Fin 2), x) 1 + Finsupp.single ((1 : Fin 2), i) 1 =
      E2 ((0 : Fin 2), (x.1, x.2)) ((1 : Fin 2), (i.1, i.2)) from rfl, coeff_E2_sum_hCol_eq_ite]
  simp only [RawChart.sg1, hsg, bil, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, if_true, zero_ne_one, one_ne_zero, if_false, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_add]
  congr 1 <;> (congr 1; exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)

end Self

theorem hStabSelf_holds : HStabSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g c q hty
  have hne : p.ty0 c ≠ p.ty0 q + p.hd := by
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · exact hty
    · intro e
      apply hty
      show p.ty0 c + p.hd = p.ty0 q
      rw [e, add_assoc, p.hd_two, add_zero]
  obtain ⟨a, ha⟩ := p.em_sep _ _ hne
  have hb := Y.bil_ad a (p.e c) (p.e q)
  rw [p.e_eig c a, p.e_eig q (star a), p.em_conj, bil_smul_left, bil_smul_right, ← sub_mul] at hb
  have hint : V.Ge 0 (bil (Y.B.ad a) (p.e c) (p.e q)) := bil_int (Y.intAd a) (p.e_int c) (p.e_int q)
  rw [hb] at hint
  have hβ : V.Ge 0 (bil Y.h (p.e c) (p.e q)) := by
    unfold VF.Ge at hint ⊢
    rwa [V.v.map_mul, ha, zero_add] at hint
  have hgm : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    obtain ⟨M, hM⟩ := p.gm_lim 0
    intro a r s
    have h1 : V.Ge 0 (p.gm a r s - p.em a (M r s)) := by simpa using hM a r s
    have h2 := h1.add (p.em_int a (M r s))
    simpa using h2
  show V.Ge 0 ((Y.rawSelf p).sg1 (fun x => p.gm (p.ty0 c) x.1 g * p.e c x.2)
    (fun x => p.gm (p.ty0 q) x.1 (1 - g) * p.e q x.2))
  rw [Y.self_raw_first_pairing_eq]
  apply VF.Ge.neg
  apply VF.Ge.sum
  intro col _
  show V.Ge 0 (bil Y.h (p.gm (p.ty0 c) col g • p.e c) (p.gm (p.ty0 q) col (1 - g) • p.e q))
  rw [bil_smul_left, bil_smul_right]
  exact (hgm _ _ _).mul_int ((hgm _ _ _).mul_int hβ)

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSg
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OActSg

open PartialDerivEval LogEx OActLog

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem actK_self (B : FB C dd O) (a : O) : B.actK C a = B.A.act a := by
  funext i
  simp [FB.actK, Algebra.algebraMap_self]

theorem pderiv_second_eval_first (f : PS C 1 dd) (i : Fin dd) : pderiv C ((1 : Fin 2), i) (ev (n := 2) ![pt C dd 0] f) = 0 := by
  rw [pderiv_eval_single (pt C dd 0) (coordinate_point_constantCoeff 0), sum_d_pt_other (0 : Fin 2) 1 (by decide)]

theorem pderiv_second_eval_second (f : PS C 1 dd) (i : Fin dd) :
    pderiv C ((1 : Fin 2), i) (ev (n := 2) ![pt C dd 1] f) = ev (n := 2) ![pt C dd 1] (pderiv C ((0 : Fin 1), i) f) := by
  rw [pderiv_eval_single (pt C dd 1) (coordinate_point_constantCoeff 1), sum_d_pt_self]

theorem eval_first_then_zero (f : PS C 1 dd) : ev (n := 1) ![pt C dd 0, 0] (ev (n := 2) ![pt C dd 0] f) = f := by
  have ha : MvPowerSeries.HasSubst
      (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 2 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by simp [pt])
  have hb : MvPowerSeries.HasSubst
      (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨j, i⟩
      fin_cases j <;> simp [pt])
  unfold ev
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  have hX : (fun s : Fin 1 × Fin dd => MvPowerSeries.subst
      (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
      ((![pt C dd 0] : Fin 1 → Pt C 2 dd) s.1 s.2)) = MvPowerSeries.X := by
    funext s
    rcases s with ⟨j, i⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    show MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
      (MvPowerSeries.X ((0 : Fin 2), i)) = MvPowerSeries.X ((0 : Fin 1), i)
    rw [MvPowerSeries.subst_X hb]
    rfl
  rw [hX, MvPowerSeries.subst_self]
  rfl

theorem eval_second_then_zero (f : PS C 1 dd) :
    ev (n := 1) ![pt C dd 0, 0] (ev (n := 2) ![pt C dd 1] f) = MvPowerSeries.C (constantCoeff f) := by
  have ha : MvPowerSeries.HasSubst
      (fun p : Fin 1 × Fin dd => (![pt C dd 1] : Fin 1 → Pt C 2 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by simp [pt])
  have hb : MvPowerSeries.HasSubst
      (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨j, i⟩
      fin_cases j <;> simp [pt])
  unfold ev
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  have hX : (fun s : Fin 1 × Fin dd => MvPowerSeries.subst
      (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
      ((![pt C dd 1] : Fin 1 → Pt C 2 dd) s.1 s.2)) = 0 := by
    funext s
    rcases s with ⟨j, i⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    show MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
      (MvPowerSeries.X ((1 : Fin 2), i)) = 0
    rw [MvPowerSeries.subst_X hb]
    rfl
  rw [hX, MvPowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem sg_act (Y : FBChart C V O dd) (α : O) (v : Fin dd → C) (hv : ∀ i, V.Ge 0 (v i)) :
    IntS V (ev (n := 1) ![Y.B.A.act α] (Y.sgP v) - Y.sgP (linAct (Y.B.A.act (star α)) v)) := by
  set φ := Y.B.A.act α with hφdef
  set ψ := Y.B.A.act (star α) with hψdef
  have hφ0 : ∀ j, constantCoeff (φ j) = 0 := Y.B.A.const α
  have hψ0 : ∀ j, constantCoeff (ψ j) = 0 := Y.B.A.const (star α)
  set A : Pt C 2 dd := comp1 φ (pt C (n := 2) dd 0) with hA
  set Bp : Pt C 2 dd := comp1 ψ (pt C (n := 2) dd 1) with hBp
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => const_ev (z0_1 _ (coordinate_point_constantCoeff 0)) (hφ0 j)
  have hB0 : ∀ j, constantCoeff (Bp j) = 0 := fun j => const_ev (z0_1 _ (coordinate_point_constantCoeff 1)) (hψ0 j)
  have hZA : Z0 (![A, pt C dd 1] : Fin 2 → Pt C 2 dd) := by
    intro k j; fin_cases k
    · exact hA0 j
    · exact z0_pt 1 j
  have hZB : Z0 (![pt C dd 0, Bp] : Fin 2 → Pt C 2 dd) := by
    intro k j; fin_cases k
    · exact z0_pt 0 j
    · exact hB0 j
  set H : PS C 2 dd := ev (n := 2) ![A, pt C dd 1] Y.h - ev (n := 2) ![pt C dd 0, Bp] Y.h with hH
  have had : Y.B.ad α = FB.expS C H := by
    have := Y.gauge.ad α; rwa [toK_self, actK_self, actK_self] at this
  have hH0 : constantCoeff H = 0 := by
    rw [hH, map_sub, const_ev hZA (h_const Y), const_ev hZB (h_const Y), sub_zero]

  have t1 : ∀ i, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (ev (n := 2) ![A, pt C dd 1] Y.h)) =
      ev (n := 1) ![φ, 0] (pderiv C ((1 : Fin 2), i) Y.h) := by
    intro i
    rw [pderiv_eval_pair hZA]
    have e1 : ∑ j, ev (n := 2) ![A, pt C dd 1] (pderiv C ((0 : Fin 2), j) Y.h) *
        pderiv C ((1 : Fin 2), i) ((![A, pt C dd 1] : Fin 2 → Pt C 2 dd) 0 j) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [show ((![A, pt C dd 1] : Fin 2 → Pt C 2 dd) 0 j) = ev (n := 2) ![pt C dd 0] (φ j) from rfl, pderiv_second_eval_first,
          mul_zero]
    rw [e1, zero_add]
    rw [show (∑ j, ev (n := 2) ![A, pt C dd 1] (pderiv C ((1 : Fin 2), j) Y.h) *
        pderiv C ((1 : Fin 2), i) ((![A, pt C dd 1] : Fin 2 → Pt C 2 dd) 1 j)) =
        ∑ j, ev (n := 2) ![A, pt C dd 1] (pderiv C ((1 : Fin 2), j) Y.h) * pderiv C ((1 : Fin 2), i) (pt C dd 1 j) from rfl,
      sum_d_pt_self]
    exact eval_eval_pair hZA constant_zero_first_zero (a' := φ) (b' := 0)
      (fun j => eval_first_then_zero (φ j)) (fun j => ev_X constant_zero_first_zero 1 j) _
  have t2 : ∀ i, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (ev (n := 2) ![pt C dd 0, Bp] Y.h)) =
      ∑ j, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), j) Y.h) * MvPowerSeries.C (linM ψ j i) := by
    intro i
    rw [pderiv_eval_pair hZB]
    rw [show (∑ j, ev (n := 2) ![pt C dd 0, Bp] (pderiv C ((0 : Fin 2), j) Y.h) *
        pderiv C ((1 : Fin 2), i) ((![pt C dd 0, Bp] : Fin 2 → Pt C 2 dd) 0 j)) =
        ∑ j, ev (n := 2) ![pt C dd 0, Bp] (pderiv C ((0 : Fin 2), j) Y.h) * pderiv C ((1 : Fin 2), i) (pt C dd 0 j) from rfl,
      sum_d_pt_other (0 : Fin 2) 1 (by decide), zero_add, ev_sum constant_zero_first_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((![pt C dd 0, Bp] : Fin 2 → Pt C 2 dd) 1 j) = ev (n := 2) ![pt C dd 1] (ψ j) from rfl, pderiv_second_eval_second,
      ev_mul constant_zero_first_zero, eval_second_then_zero, cc_pderiv]
    congr 1
    exact eval_eval_pair hZB constant_zero_first_zero (a' := pt C dd 0) (b' := 0) (fun k => ev_X constant_zero_first_zero 0 k)
      (fun k => by
        show ev (n := 1) ![pt C dd 0, 0] (ev (n := 2) ![pt C dd 1] (ψ k)) = 0
        rw [eval_second_then_zero, hψ0 k, map_zero]) _
  have hi : ∀ i, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (Y.B.ad α)) =
      ev (n := 1) ![φ, 0] (pderiv C ((1 : Fin 2), i) Y.h) -
        ∑ j, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), j) Y.h) * MvPowerSeries.C (linM ψ j i) := by
    intro i
    rw [had, pderiv_expS hH0, ← had, ev_mul constant_zero_first_zero, Y.B.adjoint_zero_snd, one_mul, hH, map_sub, ev_sub constant_zero_first_zero, t1, t2]
  have hl : ∀ j, linAct ψ v j = ∑ i, linM ψ j i * v i := fun j => rfl
  have e : ∑ j, MvPowerSeries.C (linAct ψ v j) * ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), j) Y.h) =
      ∑ i, MvPowerSeries.C (v i) *
        ∑ j, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), j) Y.h) * MvPowerSeries.C (linM ψ j i) := by
    simp only [hl, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have key : ev (n := 1) ![φ] (Y.sgP v) - Y.sgP (linAct ψ v) =
      -∑ i, MvPowerSeries.C (v i) * ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (Y.B.ad α)) := by
    rw [ev_sgP Y v φ hφ0, show Y.sgP (linAct ψ v) = -∑ j, MvPowerSeries.C (linAct ψ v j) *
        ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), j) Y.h) from rfl, e]
    simp only [hi, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [key]
  have hpts : ∀ k i, IntS V ((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) k i) := by
    intro k i; fin_cases k
    · exact intS_X _
    · exact intS_zero
  exact intS_neg (intS_sum _ fun i _ => intS_C_mul (hv i) (intS_ev constant_zero_first_zero hpts (intS_pderiv (Y.intAd α) _)))

end OActSg

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFBTop
section
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePProj

theorem projFB_of_lie (hLie : ProjLieSt) : ProjFBSt := projFB_of RowTiePLSmall.lSmall_holds hLie

end RowTiePProj

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.SubstSubst
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace VP

section Gen

variable {C : Type} [Field C] {σ τ ρ : Type}

theorem hs [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.HasSubst a := hasSubst_of_ordGE (fun s => by
    unfold Formalism.BaseCaseIdentities.OrdGE
    intro A hA
    have h0 : A = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]
      omega
    subst h0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ha s)

theorem og {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (s : σ) :
    Formalism.BaseCaseIdentities.OrdGE 1 (a s) := by
  unfold Formalism.BaseCaseIdentities.OrdGE
  intro A hA
  have h0 : A = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]
    omega
  subst h0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact ha s

theorem cc_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
  have h : Formalism.BaseCaseIdentities.OrdGE 1 (MvPowerSeries.subst a f) :=
    ordGE_subst (og ha) (og (a := fun _ : Unit => f) (fun _ => hf) ())
  have h0 := h 0 (by simp)
  rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0

theorem subst_mul [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (f g : MvPowerSeries σ C) :
    MvPowerSeries.subst a (f * g) = MvPowerSeries.subst a f * MvPowerSeries.subst a g := MvPowerSeries.subst_mul (hs ha) f g

theorem subst_one [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (1 : MvPowerSeries σ C) = 1 := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_one _

theorem subst_prod [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∏ i ∈ s, F i) = ∏ i ∈ s, MvPowerSeries.subst a (F i) := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_prod _ _ _

theorem subst_sum [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∑ i ∈ s, F i) = ∑ i ∈ s, MvPowerSeries.subst a (F i) := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_sum _ _ _

theorem subst_smul [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (c : C) (f : MvPowerSeries σ C) :
    MvPowerSeries.subst a (c • f) = c • MvPowerSeries.subst a f := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_smul _ c f

theorem subst_exp [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := subst_mvExp (og ha) (og (a := fun _ : Unit => f) (fun _ => hf) ())

theorem subst_subst [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C} {b : τ → MvPowerSeries ρ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : MvPowerSeries σ C) :
    MvPowerSeries.subst b (MvPowerSeries.subst a f) =
      MvPowerSeries.subst (fun s => MvPowerSeries.subst b (a s)) f := MvPowerSeries.subst_comp_subst_apply (hs ha) (hs hb) f

theorem subst_X [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (s : σ) :
    MvPowerSeries.subst a (MvPowerSeries.X s : MvPowerSeries σ C) = a s := MvPowerSeries.subst_X (hs ha) s

end Gen

section Exp

variable {C : Type} [Field C] [CharZero C] {n dd : ℕ}

theorem expS_eq (f : PS C n dd) (hf : MvPowerSeries.constantCoeff f = 0) : FB.expS C f = mvExp f := by
  have hpow : ∀ (k : ℕ) (m : Fin n × Fin dd →₀ ℕ), m.degree < k → MvPowerSeries.coeff m (f ^ k) = 0 := by
    intro k m hm
    have h1 := ordGE_finsupp_prod (fun _ : Unit => f) (fun _ => og (a := fun _ : Unit => f) (fun _ => hf) ())
      (Finsupp.single () k)
    simp only [Finsupp.prod_single_index, pow_zero, Finsupp.degree_single] at h1
    exact h1 m hm
  ext m
  rw [FB.expS, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf)]
  change _ = ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (f ^ k) / (k.factorial : C)
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (m.degree + 1)) ?_]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [PowerSeries.coeff_exp]
    simp only [smul_eq_mul, map_div₀, map_one, map_natCast]
    ring
  · intro k hk
    rw [Function.mem_support] at hk
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hk (by rw [hpow k m (by omega), smul_zero])

end Exp

end VP

end Formalism.L2.FormalSeriesBounds
end
end

