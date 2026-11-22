import Mathlib
import Formalism.LocalToGlobal.Divisibility.LinkDIVL2R3Col
import Formalism.LocalToGlobal.Divisibility.LinkDef
import Formalism.LocalToGlobal.Divisibility.ConstantGeTwentyEight
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.LocalToGlobal.GlobalTheory.Bundle0003
import Formalism.LocalRingCardinality.DataParams₂

-- bundled from Formalism.LocalToGlobal.Divisibility.LinkDIVL2R3Rec
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.L2.Col

section ConcreteCol3

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}
  {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

theorem linkDIV_L2R3_rec [IsTotallyComplex X.K] (A3 : FamIn3 X.K G Pl0 I0 Ty T m) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    (hsep : A3.fam3.TypesSep3) (P0 : Subgroup G) (ψ0 : P0 →* X.Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* X.Kˣ) (hX : X.Ok)
    {P : LevFam X.E X.K Rk.r Pr.vGs} (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs Rk.r → X.K)) {m2 : ℕ} {Gc : ChGlob X Rk.m}
    (mu : A3.fam3.base3.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Am : Formalism.L2.Ker.Amb X) (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu A3.fam3.base3.μ0) P (wd x)).Ok)
    (ev : ∀ (Zs : DefSub A3.fam3.amb3) t, (Fin ((A3.side3 P1 ψ1 Zs).nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P)
    (Sp : ∀ Zs : DefSub A3.fam3.amb3,
      SPer (colFace hX (A3.side3 P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF (ev Zs)))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (cf : ConvFace A3.fam3.base3) (C CH : ℝ)
    (Pk : IndefPkgR A3.fam3.amb3
      (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1
        (fun Zs => colFace hX (A3.side3 P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF (ev Zs)) Sp Zsc)
      cf C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A3.fam3.base3.J Pl) (x : Mem)
    (Nu : Submodule (𝓞 X.K) (Fin (ramDim W Ch hX (wd x)) → X.K)) (sg : HeightOneSpectrum (𝓞 X.K) → ℝ)
    (I : DivInputsR Pk.core R x Nu sg)
    (hQ : ChainTie I.ch (memQ (A := kerRec mu cst L wd b hY Am hK) (hF := hF) hE (x := x))) (h0 : FirstCols hE hQ) :
    DivClausesR Pk.core R x Nu sg ∧
      (∀ y : Fin (I.ch.c 0) → X.K,
        hQ.coL ((chainMat I.ch.Kj ⟨(memQ (A := kerRec mu cst L wd b hY Am hK) (hF := hF) hE (x := x)).n + 1, by have := hQ.hmm; omega⟩).mulVec y) =
          Formalism.L2.Ker.colMu W Ch sel (mu A3.fam3.base3.μ0) (cst A3.fam3.base3.μ0) (L A3.fam3.base3.μ0) Am (wd x) m2 (b A3.fam3.base3.μ0 x)
            (hY A3.fam3.base3.μ0 x) P (hK A3.fam3.base3.μ0 x) (hF A3.fam3.base3.μ0 x) (hL A3.fam3.base3.μ0)
            (colOfCoord W Ch hX (wd x) fun i => y (Fin.cast I.ch.c0.symm i))) ∧
      ∀ (φ : Fin (ramDim W Ch hX (wd x)) → X.K) (F : Fin ((A3.side3 P1 ψ1 Pk.Zs).nV A3.fam3.base3.μ0) → X.K),
        I.ch.PtL ((chainMat I.ch.Kj (Fin.last I.ch.mm)).mulVec fun i => φ (Fin.cast I.ch.c0 i)) F =
          colPerL (hP A3.fam3.base3.μ0) Xg (wd x) (ev Pk.Zs A3.fam3.base3.μ0)
            (Formalism.L2.Ker.colMu W Ch sel (mu A3.fam3.base3.μ0) (cst A3.fam3.base3.μ0) (L A3.fam3.base3.μ0) Am (wd x) m2 (b A3.fam3.base3.μ0 x)
              (hY A3.fam3.base3.μ0 x) P (hK A3.fam3.base3.μ0 x) (hF A3.fam3.base3.μ0 x) (hL A3.fam3.base3.μ0) (colOfCoord W Ch hX (wd x) φ)) F :=
  ⟨divClausesR_of (A3.side_well_formed hOk P0 ψ0 Pk.Zs Pk.stable Pk.inBlock hsep)
    (A3.side_well_formed hOk P1 ψ1 Pk.Zs Pk.stable Pk.inBlock hsep) Pk.core R x Nu sg I, FirstCols.chain hE h0, fun φ F => (I.ch.fact φ F).symm⟩

end ConcreteCol3

end Formalism.L2.DIV
end
end

-- bundled from Formalism.LocalToGlobal.Divisibility.SmallTies
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions

section Weights

variable {D : D7}

theorem lw_plEq (w : D.what₂.places.Pl) : SizeData₂.lwP w = Formalism.DivisionValues.lw (D.plEq w) := by
  rfl

theorem ramw_plEq (w : D.what₂.places.Pl) : ((D.what₂.places.ramIdx w : ℕ) : ℝ) = ((ramw (D.plEq w) : ℤ) : ℝ) := by
  rw [← lf_eW_eq_ramw, D.ram_eq w, Int.cast_natCast]
  rfl

end Weights

section Fo

variable {D : D7} {Bs : DefBase D.what₂.LL} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}

def FTie (L : SizeData₂ D) (N : IndefNum Bs) (eJ : Bs.J ≃ Fin D.R.m) : Prop :=
  ∀ y j, N.F0 y j = L.F ((eJ j).1 + 1) (D.plEq.symm y)

theorem fTie_num_iff (L : SizeData₂ D) (Z : IndefScale Bs) (C CH : ℝ) (eJ : Bs.J ≃ Fin D.R.m) :
    FTie L (Z.num C CH) eJ ↔ ∀ y j, Z.F0 y j = L.F ((eJ j).1 + 1) (D.plEq.symm y) := Iff.rfl

theorem sum_lifts_eJ (eJ : Bs.J ≃ Fin D.R.m) (f : ℕ → ℝ) :
    ∑ j ∈ SizeData₂.lifts D, f j = ∑ j : Bs.J, f ((eJ j).1 + 1) := by
  rw [Equiv.sum_comp eJ (fun i : Fin D.R.m => f (i.1 + 1)), Fin.sum_univ_eq_sum_range (fun i => f (i + 1)),
    Finset.range_eq_Ico, Finset.sum_Ico_add']
  unfold SizeData₂.lifts
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

theorem two_sumTw_eq_Fo (L : SizeData₂ D) (S0 : IndefSide Df0 N) (hU : S0.toIndefData.Untwisted N) (eJ : Bs.J ≃ Fin D.R.m)
    (hF : FTie L N eJ) :
    2 * (∑ j, ∑ y ∈ S0.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)) = L.Fo := by
  classical
  have hF' : ∀ y j, N.F0 y j = L.F ((eJ j).1 + 1) (D.plEq.symm y) := hF
  unfold SizeData₂.Fo
  rw [sum_lifts_eJ eJ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∑ y ∈ S0.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)
      = ∑ y ∈ S0.Tw ∪ L.supp.map D.plEq.toEmbedding, lw y * ((ramw y : ℝ) * N.F0 y j) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro y _ hy
    rw [(hU y hy j).2, mul_zero, mul_zero]
  have h2 : ∑ y ∈ L.supp.map D.plEq.toEmbedding, 2 * (lw y * ((ramw y : ℝ) * N.F0 y j))
      = ∑ y ∈ S0.Tw ∪ L.supp.map D.plEq.toEmbedding, 2 * (lw y * ((ramw y : ℝ) * N.F0 y j)) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro y _ hy'
    have hw : D.plEq.symm y ∉ L.supp := by
      intro hw
      apply hy'
      rw [Finset.mem_map]
      exact ⟨_, hw, by simp⟩
    rw [hF', L.F_supp _ _ hw, mul_zero, mul_zero, mul_zero]
  have h3 : ∑ w ∈ L.supp, SizeData₂.sz w (L.F ((eJ j).1 + 1) w)
      = ∑ y ∈ L.supp.map D.plEq.toEmbedding, 2 * (lw y * ((ramw y : ℝ) * N.F0 y j)) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Equiv.coe_toEmbedding]
    rw [hF', Equiv.symm_apply_apply, SizeData₂.sz, lw_plEq, ramw_plEq]
    ring
  rw [h1, h3, h2, Finset.mul_sum]

theorem two_FoOf_eq_Fo (L : SizeData₂ D) (P : IndefCore Df0 Df1 Dc Sp N) (eJ : Bs.J ≃ Fin D.R.m) (hF : FTie L N eJ) :
    2 * FoOf P = L.Fo := by
  unfold FoOf
  exact two_sumTw_eq_Fo L P.base P.extra.untw eJ hF

theorem two_FoOfR_eq_Fo (L : SizeData₂ D) (P : IndefCoreR Df0 Df1 Dc Sp N) (eJ : Bs.J ≃ Fin D.R.m) (hF : FTie L N eJ) :
    2 * FoOfR P = L.Fo := by
  unfold FoOfR
  exact two_sumTw_eq_Fo L P.base P.extra.untw eJ hF

theorem foTie_pkg {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (L : SizeData₂ D) (A : FamIn D.what₂.LL G Pl0 T m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (Cp CHp : ℝ)
    (Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) Cp CHp) (eJ : A.fam.base.J ≃ Fin D.R.m)
    (hF : FTie L ((Zsc Pk.Zs).num Cp CHp) eJ) : 2 * FoOf Pk.core = L.Fo := two_FoOf_eq_Fo L Pk.core eJ hF

theorem foTie_pkgR {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (L : SizeData₂ D) (A : FamIn D.what₂.LL G Pl0 T m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (cf : ConvFace A.fam.base) (Cp CHp : ℝ)
    (Pk : IndefPkgR A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cf Cp CHp) (eJ : A.fam.base.J ≃ Fin D.R.m)
    (hF : FTie L ((Zsc Pk.Zs).num Cp CHp) eJ) : 2 * FoOfR Pk.core = L.Fo := two_FoOfR_eq_Fo L Pk.core eJ hF

end Fo

section Sg

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

theorem sg_fin_sgD (C : Formalism.L2.Col.ColObj K I) (u : I) :
    (Function.support (shiftZ (Formalism.L2.GlobalTheoryTheory.FamRows.sgD C u))).Finite := Formalism.L2.GlobalTheoryTheory.FamRows.flD_support_finite C u

end Sg

section Mu1

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

theorem package_column_tuple_eq (A : FamIn D.what₂.LL G Pl0 T m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (Cp CHp : ℝ)
    (Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) Cp CHp) :
    Pk.core.cols.toIndefData.μ = Pk.core.base.toIndefData.μ := column_tuple_of_level_link Pk.core.extra.level

theorem package_column_tuple_eq_of_conventions (A : FamIn D.what₂.LL G Pl0 T m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (cf : ConvFace A.fam.base) (Cp CHp : ℝ)
    (Pk : IndefPkgR A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cf Cp CHp) :
    Pk.core.cols.toIndefData.μ = Pk.core.base.toIndefData.μ := column_tuple_of_level_link Pk.core.extra.level

end Mu1

end Formalism.L2.DIV

end
end

