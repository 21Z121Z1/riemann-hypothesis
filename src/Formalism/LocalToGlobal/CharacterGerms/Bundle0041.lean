import Formalism.LocalToGlobal.CharacterGerms.IteratePderivTripleMultiplication
import Formalism.LocalToGlobal.CharacterGerms.CoeffLMulCvFrob
import Formalism.LocalToGlobal.CharacterGerms.Bundle0040
import Formalism.LocalToGlobal.CharacterGerms.Bundle0039
import Formalism.LocalToGlobal.CharacterGerms.Bundle0034
import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

-- bundled from Formalism.LocalToGlobal.CharacterGerms.FunEqCoreHolds
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob Formalism.L2.FormalSeriesBounds.LiftedCoordinateEvaluation
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem aOf_eq (Y : FBChart C V O dd) (u : Fin dd → C) :
    Y.aOf u = ∑ i, MvPowerSeries.C (u i ^ V.l * ((V.l.factorial : C))⁻¹) *
      ev (rz 1) ((pderiv C ((0 : Fin 2), i))^[V.l] Y.u1) := by
  ext ν
  rw [map_sum]
  simp only [coeff_C_mul]
  show (∑ i, u i ^ V.l * coeff (Finsupp.single ((0 : Fin 2), i) V.l +
    ν.mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1) = _
  have hup : (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2)) = up 1 := by
    funext q; obtain ⟨q1, q2⟩ := q; fin_cases q1; rfl
  rw [hup]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_rz_iter]
  have hf : (V.l.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

theorem link (Y : FBChart C V O dd) (u : Fin dd → C) (W : Pt C 2 dd) (hW : ∀ j, constantCoeff (W j) = 0)
    (Wup : Pt C 3 dd) (hW0 : ∀ j, constantCoeff (Wup j) = 0) (hd : ∀ i j, pderiv C ((0 : Fin 3), i) (Wup j) = 0)
    (hr : ∀ j, ev (rz 2) (Wup j) = W j) (γ : Fin 2 × Fin dd →₀ ℕ) :
    coeff γ (ev (n := 2) ![W] (Y.aOf u)) = Phi V u (UU Y Wup) γ := by
  have hz1 := z0_1 W hW
  have hz2 := constant_zero_two_points (p3 0) (z0p3 0) hW0
  rw [aOf_eq, ev_sum hz1]
  simp only [ev_mul hz1, ev_C, map_sum, coeff_C_mul]
  unfold Phi
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : ev ![W] (ev (rz 1) ((pderiv C ((0 : Fin 2), i))^[V.l] Y.u1)) =
      ev (n := 2) ![0, W] ((pderiv C ((0 : Fin 2), i))^[V.l] Y.u1) := by
    rw [ev_ev (constant_zero_restrict_points 1) hz1]
    congr 1
    funext k j
    fin_cases k
    · exact ev_zero hz1
    · exact ev_X hz1 0 j
  have e2 : ev (rz 2) ((pderiv C ((0 : Fin 3), i))^[V.l] (UU Y Wup)) =
      ev (n := 2) ![0, W] ((pderiv C ((0 : Fin 2), i))^[V.l] Y.u1) := by
    unfold UU
    rw [d_ev_keep_iter hW0 i (hd i), ev_ev hz2 (constant_zero_restrict_points 2)]
    congr 1
    funext k j
    fin_cases k
    · exact ev_X (constant_zero_restrict_points 2) 0 j
    · exact hr j
  have h3 := coeff_rz_iter 2 i V.l (UU Y Wup) γ
  rw [e2] at h3
  rw [e1, h3]
  have hf : (V.l.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  rfl

theorem coeff_U_eq (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) (γ : Fin 2 × Fin dd →₀ ℕ) :
    V.MM (Phi V u (UU Y (SS Y.B.G)) γ - Phi V u (UU Y (p3 1)) γ - Phi V u (UU Y (p3 2)) γ -
      Phi V u (Y.B.ph2 ^ V.l) γ + Phi V u (QQ Y) γ) := by
  have hU : ∀ {w : Pt C 3 dd}, (∀ j, constantCoeff (w j) = 0) → (∀ j, IntS V (w j)) →
      (∀ i j, pderiv C ((0 : Fin 3), i) (w j) = 0) → IntS V (UU Y w) ∧ FrobD V (UU Y w) ∧ ev (rz 2) (UU Y w) = 1 :=
    fun hw0 hw hd => ⟨UU_int Y hw0 hw, UU_frob Y hw0 hw hd, UU_one Y hw0⟩
  obtain ⟨iS, fS, oS⟩ := hU (triple_sum_constantCoeff Y.B.G) (SS_int Y.B.G Y.intF) (SS_d Y.B.G)
  obtain ⟨i1, f1, o1⟩ := hU (z0p3 1) (fun j => triple_coordinate_integral 1 j) (fun i j => triple_point_pderiv_first_zero 1 (by decide) i j)
  obtain ⟨i2, f2, o2⟩ := hU (z0p3 2) (fun j => triple_coordinate_integral 2 j) (fun i j => triple_point_pderiv_first_zero 2 (by decide) i j)
  have iQ := QQ_int Y
  have iP : IntS V (Y.B.ph2 ^ V.l) := intS_pow Y.intPh2 _
  have i12 : IntS V (UU Y (p3 1) * UU Y (p3 2)) := intS_mul i1 i2
  have f12 : FrobD V (UU Y (p3 1) * UU Y (p3 2)) := frobD_mul i1 i2 f1 f2
  have o12 : ev (rz 2) (UU Y (p3 1) * UU Y (p3 2)) = 1 := by rw [ev_mul (constant_zero_restrict_points 2), o1, o2, one_mul]
  unfold Phi
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine GmExArith.mm_sum fun i _ => ?_
  have cS := coeff_mul_cong iS iQ (frobX_of iS fS) (frobX_of iQ (QQ_frob Y)) oS (QQ_one Y) i γ
  have cR1 := coeff_mul_cong i12 iP (frobX_of i12 f12) (frobX_of iP (second_pairing_pow_frobenius Y)) o12 (second_pairing_pow_restrict_one Y) i γ
  have cR2 := coeff_mul_cong i1 i2 (frobX_of i1 f1) (frobX_of i2 f2) o1 o2 i γ
  rw [ident] at cS
  have e : u i ^ V.l * coeff (ix i V.l γ) (UU Y (SS Y.B.G)) - u i ^ V.l * coeff (ix i V.l γ) (UU Y (p3 1)) -
      u i ^ V.l * coeff (ix i V.l γ) (UU Y (p3 2)) - u i ^ V.l * coeff (ix i V.l γ) (Y.B.ph2 ^ V.l) +
      u i ^ V.l * coeff (ix i V.l γ) (QQ Y) =
      u i ^ V.l * (-(coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2) * Y.B.ph2 ^ V.l) -
        coeff (ix i V.l γ) (UU Y (SS Y.B.G)) - coeff (ix i V.l γ) (QQ Y)) +
        (coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2) * Y.B.ph2 ^ V.l) -
          coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2)) - coeff (ix i V.l γ) (Y.B.ph2 ^ V.l)) +
        (coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2)) - coeff (ix i V.l γ) (UU Y (p3 1)) -
          coeff (ix i V.l γ) (UU Y (p3 2)))) := by ring
  rw [e]
  exact GmExArith.mm_int_mul ((hu i).pow _) (GmExArith.mm_add (GmExArith.mm_add (GmExArith.mm_neg cS) cR1) cR2)

end Formalism.L2.FormalSeriesBounds.FunEq

namespace Formalism.L2.FormalSeriesBounds

open FunEq MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem funEqCore_holds : FunEqCoreSt := by
  intro C _ _ V O _ _ dd Y u hu hV1 μ
  have hS := link Y u (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1))
    (fun j => PartialDerivEval.const_ev (PartialDerivEval.z0_pp 0 1) (Y.B.G.const j)) (SS Y.B.G) (triple_sum_constantCoeff _) (SS_d _)
    (fun j => by
      show ev (rz 2) (ev (n := 3) ![p3 1, p3 2] (Y.B.G.F j)) = _
      rw [PartialDerivEval.ev_ev (PartialDerivEval.z0_pp 1 2) (constant_zero_restrict_points 2)]
      congr 1
      funext k m
      fin_cases k
      · exact PartialDerivEval.ev_X (constant_zero_restrict_points 2) 1 m
      · exact PartialDerivEval.ev_X (constant_zero_restrict_points 2) 2 m) μ
  have h1 := link Y u (pt C (n := 2) dd 0) (fun j => PartialDerivEval.z0_pt 0 j) (p3 1) (z0p3 1)
    (fun i j => triple_point_pderiv_first_zero 1 (by decide) i j) (fun j => PartialDerivEval.ev_X (constant_zero_restrict_points 2) 1 j) μ
  have h2 := link Y u (pt C (n := 2) dd 1) (fun j => PartialDerivEval.z0_pt 1 j) (p3 2) (z0p3 2)
    (fun i j => triple_point_pderiv_first_zero 2 (by decide) i j) (fun j => PartialDerivEval.ev_X (constant_zero_restrict_points 2) 2 j) μ
  unfold cobd
  rw [map_sub, map_sub, map_sub, hS, h1, h2]
  have hA := coeff_U_eq Y u hu μ
  have hB := phiP Y u hu μ
  have hC := phiQ Y u hu hV1 μ
  have e : Phi V u (UU Y (SS Y.B.G)) μ - Phi V u (UU Y (p3 1)) μ - Phi V u (UU Y (p3 2)) μ -
      coeff μ (frobTw V.l (Y.chartLinearTerm u)) =
      (Phi V u (UU Y (SS Y.B.G)) μ - Phi V u (UU Y (p3 1)) μ - Phi V u (UU Y (p3 2)) μ -
        Phi V u (Y.B.ph2 ^ V.l) μ + Phi V u (QQ Y) μ) +
      (Phi V u (Y.B.ph2 ^ V.l) μ - coeff μ (frobTw V.l (Y.chartLinearTerm u))) - Phi V u (QQ Y) μ := by ring
  rw [e]
  exact GmExArith.mm_sub (GmExArith.mm_add hA hB) hC

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePPTEig
section
namespace Formalism.L2.FormalSeriesBounds

theorem ptFB_of_eig (hE : RowTiePKey.KeyEigSt) : PTFBSt :=
  ptFB_of_proj2 (RowTiePProj.projFB_of RowTiePLSmall.lSmall_holds
    (RowTiePLie.projLie_of (RowTiePKey.key_of hE RowTiePKeyRes.keyRes_holds RowTiePKey.keyDelta_holds)
      RowTiePSplit.split_holds))

theorem cartFB_of_eig (hE : RowTiePKey.KeyEigSt) : CartFBSt :=
  cartFB_of_proj2 (RowTiePProj.projFB_of RowTiePLSmall.lSmall_holds
    (RowTiePLie.projLie_of (RowTiePKey.key_of hE RowTiePKeyRes.keyRes_holds RowTiePKey.keyDelta_holds)
      RowTiePSplit.split_holds))

theorem ptSelf_of_eig (hE : RowTiePKey.KeyEigSt) : PTSelfSt :=
  ptSelf_of_start2 (allStartSelf_of_eig hE)

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieSelfU
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def EnoughCharactersSelfUnramified : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d) (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, CHCharSelfSt Y (selfOfLab ha hg o)

def CharacterHypothesisSelfUnramified : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d) (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o (Hc : ∀ g, (Y.rawSelf (selfOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc

variable {Xo c}
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

theorem hypotheses_of_self_labelling_unramified (hCart : CartSelfSt) (hAx : AxesSelfSt) (hG0 : GermZeroSelfConjugate) (hC : CEqSelfSt) (hR1 : IndependenceBoundSelfConjugate)
    (hR2 : RankMaximalSelfCharts Xo c) (hCH : CharacterHypothesisSelfUnramified Xo c) (hstar : ∀ a : 𝓞 E, star a = H.bar a)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    (hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E)))) {k : ℕ}
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ι k Y) {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.rawSelf (selfOfLab ha hg o)).Hyps V where
  charZero := inferInstance
  algClosed := Y.algClosed
  l_odd := Y.l_odd
  k_unit := Y.k_unit
  cartH := hCart C V (𝓞 E) _ Y d _ (selfOfLab ha hg o)
  rank := rankHyp_ofLabS ha hg hr o
  axes := hAx C V (𝓞 E) _ Y d _ (selfOfLab ha hg o)
  G0 := hG0 C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) _
  CEq := hC C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) _
  R1 := hR1 C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) _
    (hR2 hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hr o _)
  R2 := hR2 hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hr o _
  CH := hCH hstar T io y C3 C V ι hι hd k Y hY Orb d lab ha hg hr o _

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBr
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CharacteristicFromRanks ValuationFitting
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (IsCh dl res HasAF)

section Series

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ}
variable {R : Type} [CommRing R] [Algebra R C]

abbrev toC {n : ℕ} (f : PS R n dd) : PS C n dd := MvPowerSeries.map (algebraMap R C) f

theorem mpt_pt {n : ℕ} (j : Fin n) : MapFB.mpt (algebraMap R C) (pt R dd j) = pt C dd j := by
  funext i
  simp [MapFB.mpt, pt]

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt R dd j i) = 0 := by
  simp [pt]

theorem isChar_of_isCh (Y : FBChart C V OE dd) (hR : ∀ x : R, V.Ge 0 (algebraMap R C x))
    (FR : Fin dd → PS R 2 dd) (hF : ∀ i, Y.B.G.F i = toC (FR i))
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (FR i) = 0) {u : PS R 1 dd} (hu : IsCh FR u) :
    Y.IsChar (toC u) := by
  refine ⟨fun μ => ?_, ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map]; exact hR _
  · rw [MvPowerSeries.constantCoeff_map, hu.1, map_one]
  · have h := congrArg (MvPowerSeries.map (algebraMap R C)) hu.2
    have hadd : ∀ i, MvPowerSeries.constantCoeff (addOf FR (pt R (n := 2) dd 0) (pt R (n := 2) dd 1) i) = 0 := by
      intro i
      refine MapFB.cc_ev _ ?_ _ (hF0 i)
      intro j i'
      fin_cases j <;> simp [pt]
    rw [map_mul, MapFB.map_ev1 _ _ hadd, MapFB.map_ev1 _ _ (cc_pt 0), MapFB.map_ev1 _ _ (cc_pt 1), mpt_pt, mpt_pt] at h
    have e : MapFB.mpt (algebraMap R C) (addOf FR (pt R (n := 2) dd 0) (pt R (n := 2) dd 1)) =
        addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) := by
      funext i
      show MvPowerSeries.map (algebraMap R C) (ev ![pt R (n := 2) dd 0, pt R (n := 2) dd 1] (FR i)) = _
      rw [MapFB.map_ev2 _ _ _ (cc_pt 0) (cc_pt 1), mpt_pt, mpt_pt]
      show _ = ev ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] (Y.B.G.F i)
      rw [hF i]
    rw [e] at h
    exact h

theorem dlogC_toC (u : PS R 1 dd) (i : Fin dd) : dlogC (toC u) i = algebraMap R C (dl u i) := by
  unfold dlogC dl
  rw [MvPowerSeries.coeff_map]

end Series

section Len

theorem lenCoker_mono {R : Type} [CommRing R] (v : AddValuation R (WithTop ℝ)) {m h h' : ℕ}
    (B : Matrix (Fin m) (Fin h') R) (f : Fin h → Fin h') :
    S4.lenCoker v B ≤ S4.lenCoker v (B.submatrix id f) := by
  unfold S4.lenCoker
  refine Finset.le_inf fun g _ => ?_
  exact Finset.inf_le (f := fun g : Fin m → Fin h' => v (B.submatrix id g).det) (Finset.mem_univ (f ∘ g))

variable {C : Type} [Field C] {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] {dd : ℕ}

theorem lenCoker_le_of_hasLen (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) {s N : ℕ} (W : Fin s → Fin dd → R) (u : Fin N → PS R 1 dd) {x : NNReal}
    (hx : ReciprocityTheory.PGsh.Up.HasLen vm R
      ((Fin s → R) ⧸ Submodule.span R (Set.range fun k => res W (dl (u k)))) x)
    {S : ℝ} (hS : vm (V.l : C) ^ S ≤ x) :
    S4.lenCoker V.v (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) ≤
      ((S : ℝ) : WithTop ℝ) := by
  set α : Matrix (Fin s) (Fin N) R := Matrix.of fun c k => res W (dl (u k)) c with hα
  have hr : LinearMap.range α.mulVecLin = Submodule.span R (Set.range fun k => res W (dl (u k))) := by
    rw [Matrix.range_mulVecLin]
    rfl
  rw [← hr] at hx
  have hSr : (vm (V.l : C) : ℝ) ^ S ≤ (x : ℝ) := by exact_mod_cast hS
  have hpos : 0 < (x : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos h0 S) hSr
  have e := lenCoker_eq_logb hT hv h0 h1 α hx hpos
  have e2 : (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) =
      Matrix.of fun c k => algebraMap R C (α c k) := by
    ext c k
    simp only [Matrix.of_apply, hα, res, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e2, e]
  refine WithTop.coe_le_coe.mpr ?_
  have h2 : Real.logb (vm (V.l : C) : ℝ) x ≤ Real.logb (vm (V.l : C) : ℝ) ((vm (V.l : C) : ℝ) ^ S) :=
    (Real.logb_le_logb_of_base_lt_one h0 h1 hpos (Real.rpow_pos_of_pos h0 S)).mpr hSr
  rwa [Real.logb_rpow h0 (ne_of_lt h1)] at h2

end Len

section Sum

theorem frobSum_conj_alt {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (big : ZMod d → Prop)
    (halt : ∀ b, big (b + 1) ↔ ¬ big b) (q : ZMod d → ℕ)
    (hqb : ∀ b, big b → q b = j') (hqs : ∀ b, ¬ big b → q b = n + j) (a : ZMod d) (ha : big a) :
    S4.frobSum l q a = upB l (n + j) j' (gam l) := by
  rw [S4.frobSum_alt hl j' 0 (n + j) big halt q (fun b hb => by rw [hqb b hb]; rfl) hqs a ha]
  have h1 := S4.one_div_eq_gam_add_rho hl
  have hg : gam l = S4.gam l := rfl
  have hdiv : (j' : ℝ) / ((l : ℝ) - 1) = j' * (S4.gam l + S4.rho l) := by rw [← h1]; ring
  unfold upB
  rw [hg, hdiv]
  push_cast
  ring

theorem frobSum_conj_all {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (q : ZMod d → ℕ) (hq : ∀ b, q b = j')
    (a : ZMod d) : S4.frobSum l q a = upB l (n + j) j' 0 := by
  rw [S4.frobSum_const hl j' q hq a]
  unfold upB
  ring

end Sum

section Core

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def rk {Y : FBChart C V OE dd} (p : PairData Y d I) (g : Fin 2) (b : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I g => p.ty g c = b).card

def AFBound (Y : FBChart C V OE dd) (p : PairData Y d I) (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (FR : Fin dd → PS R 2 dd) : Prop :=
  ∀ g a, p.big g a → ∃ (s : ℕ) (e : Fin s ≃ {x : I g // p.ty g x = a}) (W : Fin s → Fin dd → R) (xs : NNReal),
    (∀ c i, algebraMap R C (W c i) = p.u g (e c) i) ∧ HasAF vm FR W xs ∧
      vm (V.l : C) ^ (S4.frobSum V.l (rk p (1 - g)) a) ≤ xs

theorem upChar_of_afBound (Y : FBChart C V OE dd) (p : PairData Y d I) (hr : (Y.raw p).RankHyp)
    (Hc : ∀ g, (Y.raw p).CartHyp V g) (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1)
    (FR : Fin dd → PS R 2 dd) (hF : ∀ i, Y.B.G.F i = toC (FR i))
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (FR i) = 0) (h : AFBound Y p vm R FR) : UPCharSt Y p Hc := by
  have hR : ∀ x : R, V.Ge 0 (algebraMap R C x) := fun x => vA_nonneg hT hv h0 h1 x
  have hl1 : 1 < V.l := V.l_prime.one_lt
  have key : ∀ g a, ∃ (N : ℕ) (u : Fin N → PS C 1 dd), (∀ k, Y.IsChar (u k)) ∧ (p.big g a →
      ∃ e : Fin (pT (fun g => RawChart.cart (Hc g)) g a) ≃ {x : I g // (RawChart.cart (Hc g)).ty (Sum.inl x) = a},
        S4.lenCoker V.v (Matrix.of fun c k => p.yOf g (u k) (e c)) ≤
          ((S4.frobSum V.l (rk p (1 - g)) a : ℝ) : WithTop ℝ)) := by
    intro g a
    by_cases hb : p.big g a
    · obtain ⟨s, e, W, xs, hW, ⟨N, u, hu, hx⟩, hS⟩ := h g a hb
      have hs : s = pT (fun g => RawChart.cart (Hc g)) g a := by
        have := Fintype.card_congr e
        rw [Fintype.card_fin, Fintype.card_subtype] at this
        exact this
      subst hs
      refine ⟨N, fun k => toC (u k), fun k => isChar_of_isCh Y hR FR hF hF0 (hu k), fun _ => ⟨e, ?_⟩⟩
      have := lenCoker_le_of_hasLen hT hv h0 h1 W u hx hS
      simp only [hW] at this
      exact this
    · exact ⟨0, fun k => k.elim0, fun k => k.elim0, fun hb' => absurd hb' hb⟩
  choose N u hu he using key
  let eq : ∀ g, (Σ a : ZMod d, Fin (N g a)) ≃ Fin (Fintype.card (Σ a : ZMod d, Fin (N g a))) := fun g => Fintype.equivFin _
  refine ⟨fun g => Fintype.card (Σ a : ZMod d, Fin (N g a)),
    fun g i => u g ((eq g).symm i).1 ((eq g).symm i).2, fun g i => hu g _ _, fun g a hb => ?_⟩
  obtain ⟨e, hle⟩ := he g a hb
  have hle' : S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (u g ((eq g).symm i).1 ((eq g).symm i).2) (e c)) ≤
      ((S4.frobSum V.l (rk p (1 - g)) a : ℝ) : WithTop ℝ) := by
    refine le_trans (lenCoker_mono V.v _ (fun k : Fin (N g a) => eq g ⟨a, k⟩)) ?_
    have e3 : (Matrix.of fun c i => p.yOf g (u g ((eq g).symm i).1 ((eq g).symm i).2) (e c)).submatrix id
        (fun k : Fin (N g a) => eq g ⟨a, k⟩) = Matrix.of fun c k => p.yOf g (u g a k) (e c) := by
      ext c k
      simp only [Matrix.submatrix_apply, Matrix.of_apply, id]
      rw [Equiv.symm_apply_apply]
    rw [e3]
    exact hle
  have hc1 : ∀ b, p.big g b → rk p (1 - g) b = p.j' := fun b hb' =>
    hr.rk_small (1 - g) b (fun hh => (hr.big_compl g b).mp hh hb')
  have hc2 : ∀ b, ¬ p.big g b → rk p (1 - g) b = p.n + p.j := fun b hb' =>
    hr.rk_big (1 - g) b ((hr.big_compl g b).mpr hb')
  refine ⟨e, fun hA => ?_, fun hB => ?_⟩
  · rw [← frobSum_conj_alt hl1 p.n p.j p.j' (p.big g) (alt_step p.big hr.big_compl hA g) (rk p (1 - g)) hc1 hc2 a hb]
    exact hle'
  · rw [← frobSum_conj_all hl1 p.n p.j p.j' (rk p (1 - g)) (fun b => hc1 b (hB b)) a]
    exact hle'

end Core

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

