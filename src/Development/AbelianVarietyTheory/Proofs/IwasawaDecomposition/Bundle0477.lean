import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertNeighboursLiftsDoubleCosetTranslates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0409
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelValueRationalStep
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChiDValuesAndCcTop
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.ChiDVal

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

section Gen

variable {L : Type} [Field L] [NumberField L]

theorem ideles_snd_mul (a b : Ideles L) (v : HeightOneSpectrum (𝓞 L)) :
    ((a * b : Ideles L) : AdeleRing (𝓞 L) L).2 v = (a : AdeleRing (𝓞 L) L).2 v * (b : AdeleRing (𝓞 L) L).2 v := rfl

theorem ideles_snd_inv_mul (a : Ideles L) (v : HeightOneSpectrum (𝓞 L)) :
    ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v * (a : AdeleRing (𝓞 L) L).2 v = 1 := by
  rw [← ideles_snd_mul, inv_mul_cancel]
  rfl

theorem ideles_finite (a : Ideles L) : {v : HeightOneSpectrum (𝓞 L) | ¬ Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1}.Finite := by
  have h1 := (a : AdeleRing (𝓞 L) L).2.2
  have h2 := ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2.2
  refine Filter.eventually_cofinite.1 ((h1.and h2).mono fun v hv => ?_)
  have e1 : Valued.v ((a : AdeleRing (𝓞 L) L).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv.1
  have e2 : Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv.2
  have e3 := congrArg Valued.v (ideles_snd_inv_mul a v)
  rw [map_mul, map_one] at e3
  refine le_antisymm e1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) * Valued.v ((a : AdeleRing (𝓞 L) L).2 v) := e3.symm
    _ ≤ 1 * Valued.v ((a : AdeleRing (𝓞 L) L).2 v) := mul_le_mul_left e2 _
    _ = _ := one_mul _

theorem exists_unif_zpow (v : HeightOneSpectrum (𝓞 L)) (y : v.adicCompletion L) (hy : y ≠ 0) :
    ∃ n : ℤ, Valued.v (((atFin v (unif v)) ^ n : (v.adicCompletion L)ˣ) : v.adicCompletion L) = Valued.v y := by
  have h0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  refine ⟨-WithZero.log (Valued.v y), ?_⟩
  have hu : Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hu, ← WithZero.exp_zsmul]
  simp [WithZero.exp_log h0]

theorem ideles_values {Gp : Type} [CommGroup Gp] (f : Ideles L →* Gp)
    (hU : ∀ a : Ideles L, (∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1) → f a = 1) (S : Subgroup Gp)
    (hS : ∀ v, f (localIdele L v (atFin v (unif v))) ∈ S) (a : Ideles L) : f a ∈ S := by
  classical
  have key : ∀ (T : Finset (HeightOneSpectrum (𝓞 L))) (a : Ideles L),
      (∀ v, v ∉ T → Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1) → f a ∈ S := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro a ha
      rw [hU a fun v => ha v (Finset.notMem_empty v)]
      exact S.one_mem
    | insert v0 T _ ih =>
      intro a ha
      have hy : (a : AdeleRing (𝓞 L) L).2 v0 ≠ 0 := by
        intro h0
        have := ideles_snd_inv_mul a v0
        rw [h0, mul_zero] at this
        exact zero_ne_one this
      obtain ⟨n, hn⟩ := exists_unif_zpow v0 _ hy
      have h1 : f (a * (localIdele L v0 ((atFin v0 (unif v0)) ^ n))⁻¹) ∈ S := by
        refine ih _ fun v hv => ?_
        rw [← map_inv, ideles_snd_mul]
        by_cases hvv : v = v0
        · subst hvv
          rw [localIdele_snd_self, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hn]
          exact mul_inv_cancel₀ ((Valuation.ne_zero_iff _).2 hy)
        · rw [(localIdele_isSupportedAt L v0 _).2 v hvv, mul_one]
          exact ha v fun h => (Finset.mem_insert.1 h).elim hvv hv
      have h2 : f a = f (a * (localIdele L v0 ((atFin v0 (unif v0)) ^ n))⁻¹) * f (localIdele L v0 (atFin v0 (unif v0))) ^ n := by
        rw [map_mul, map_inv, map_zpow (localIdele L v0), map_zpow f, inv_mul_cancel_right]
      rw [h2]
      exact S.mul_mem h1 (S.zpow_mem (hS v0) n)
  exact key (ideles_finite a).toFinset a fun v hv => by
    by_contra h
    exact hv ((ideles_finite a).mem_toFinset.2 h)

end Gen

def coeffUnits (D : D7) : Subgroup ℂˣ where
  carrier := {z | ∃ r : D.what₂.LL, D.what₂.embLL r = (z : ℂ)}
  one_mem' := ⟨1, map_one _⟩
  mul_mem' := by
    rintro a b ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r * s, by rw [map_mul, hr, hs, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨r, hr⟩
    exact ⟨r⁻¹, by rw [map_inv₀, hr, Units.val_inv_eq_inv_val]⟩

theorem chiD_mem_of {D : D7} {C : CharFrame D} (T : DtTied D C) (hV : C.chiPsi.ValuesIn 0 D.what₂.embLL) :
    ∀ z : D.Dt, ∃ r : D.what₂.LL, D.what₂.embLL r = ((D.chiD z : ℂˣ) : ℂ) := by
  intro z
  obtain ⟨a, rfl⟩ := T.surj z
  refine ideles_values (D.chiD.comp T.eDt) (fun a ha => D.chiD_UO _ ((T.UO_eq _).2 ⟨a, ha, rfl⟩)) (coeffUnits D) (fun v => ?_) a
  obtain ⟨y, hy⟩ := hV v (C.isChi.unr v)
  refine ⟨y, ?_⟩
  rw [hy]
  show _ = ((D.chiD (T.eDt (localIdele D.host.E v (atFin v (unif v)))) : ℂˣ) : ℂ)
  rw [T.chiD_eq _ (fun w => (localIdele_isSupportedAt D.host.E v _).1 w)]
  unfold HChar.valTw
  rw [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
  rfl

theorem chiD_values_and_cc_top : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), (∀ z : (w.D Z).Dt, ∃ r : (w.D Z).what₂.LL, (w.D Z).what₂.embLL r = (((w.D Z).chiD z : ℂˣ) : ℂ)) ∧ ∀ (L : SizeData₂ (w.D Z)) (hT : GatTies (w.D Z)) (Gi : G.Inst (w.D Z) L) (Gl : G.LatInst (w.D Z)) (K : G.Consts) (Y : DivX (w.D Z)) (cX : ExtraC) (ex : Extra (w.D Z) L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.cc = ⊤ := by
  intro B f T w Z
  refine ⟨?_, fun L hT Gi Gl K Y cX ex t => t.cc_rec.trans B.toPre.ccK_top⟩
  obtain ⟨dt, -⟩ := TC.dtTied_true w.I w.ok w.pins w.l Z
  have hv : Formalism.L2.Host.ValLL0 (w.D Z) (TC.cf w.I w.l Z) := by
    rcases w with ⟨px, I, ok, C_eq, S_eq, xi_range, pins, l, l0, δ, exact, fld, val⟩
    subst C_eq
    exact val _ _ _ _ _ _
  exact chiD_mem_of dt hv.toLL.chiPsi

end GlobalTheory.Mem.ChiDVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjHeckeFamIApply
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.RowAd.Inert

theorem conj_heckeFamI_apply {X : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (C : Formalism.L2.Col.CoefPk X n (Formalism.L2.Col.DecoSet X.E n ST SG)) (Λ : Formalism.L2.Col.LevFam X.E X.K n SG)
    (hS : (Formalism.L2.Col.formGSD C Λ).Ok) (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : Formalism.L2.Col.LevOffI ST SG S0 × List ℕ)
    (f : ((Formalism.L2.Col.formGSD C Λ).toCSD hS).Forms) (d : Formalism.L2.Col.DecoSet X.E n ST SG) :
    ((((Formalism.L2.Col.formGSD C Λ).res hS).symm ((((Formalism.L2.Col.formGSD C Λ).res hS).conj
      (Formalism.L2.Col.heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y)) f) : (Formalism.L2.Col.formGSD C Λ).EqFun) :
        Formalism.L2.Col.DecoSet X.E n ST SG → C.V) d =
      ∑ e ∈ d.inertNb y.1.1.asIdeal y.2, ((((Formalism.L2.Col.formGSD C Λ).res hS).symm f : (Formalism.L2.Col.formGSD C Λ).EqFun) :
        Formalism.L2.Col.DecoSet X.E n ST SG → C.V) e := by
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [Formalism.L2.Col.heckeFamI_formPts_apply]
  rfl

theorem colIn3_heckeRI_apply {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R)
    (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
    (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (trIv : Fin R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Formalism.L2.Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
    (τ : TupF TU) (q : ↑((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).okI τ) × List ℕ)
    (f : ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.MtildeCSD τ).Forms) (d : (Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).D) :
    (((Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).res (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX)).symm
      ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).heckeRI τ q f)).1 d =
      ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb q.1.1.1.asIdeal q.2 d,
        (((Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).res (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX)).symm f).1 e :=
  conj_heckeFamI_apply _ _ (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX) S0 (offSubI.lev q.1, q.2) f d

theorem opEq (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U) (cX : CoefA X.toD7.sp.X') {J : Subgroup (Bridge.Gf X.toD7.sp.X')} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ J χ)
    (hP : ReadsDeco X I hX Xg tr cX t P)
    (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (R : Finset (Bridge.Gf X.toD7.sp.X'))
    (hN : ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet X.B.fields.E (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) → M) (g : Bridge.Gf X.toD7.sp.X'),
        ∑ a ∈ R, ψ (decoAd X I t (g * a)) =
          ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb (q.1.1 : PlI X.B px).1.asIdeal q.2 (decoAd X I t g : Formalism.L2.Col.DecoSet X.B.fields.E (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)), ψ e)
    (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
    P.ext ((((famR X I hX U Xg tr).heckeRI t q f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
        ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) =
      Bridge.dcOp R (P.ext (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) := by
  obtain ⟨m, hm⟩ := hP
  funext g
  have e1 := hm ((famR X I hX U Xg tr).heckeRI t q f) g
  have e2 := colIn3_heckeRI_apply (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I U)
    Xg ∅ (xiValOf I) tr t q f (decoAd X I t g)
  have e3 := hN _ (fun e => m ((((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 e)) g
  refine e1.trans ?_
  refine (congrArg m e2).trans ?_
  refine (map_sum m _ _).trans ?_
  refine e3.symm.trans ?_
  exact (Finset.sum_congr rfl (fun a _ => hm f (g * a))).symm

theorem chi_eq_one {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (Q : Pl D.host.E)
    (hQc : Formalism.L2.Col.conjPrime₂ Q = Q) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q) (j : (levEnv V β L).J)
    (hj : IsLocElt V Q (j : Bridge.Gf V)) : (levEnv V β L).χ j = 1 := by
  have e : (levEnv V β L).χ j = Formalism.L2.DIV.levFn β (flag1L L) (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) := rfl
  have hm : Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L) := j.2
  have hSt := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hm)
  have hloc := LiftInertChi.locAt_of_isLocElt V _ _ hj
  have hconj : Formalism.DivisionValues.conjPl Q = Q := GlobalTheory.InertNbr.conjPl_eq_of_conjP hQc
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q →
      Formalism.L2.DIV.redFn β PP (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) = 1 := fun PP hPP =>
    LiftInertChi.redFn_eq_one_of_locAt _ _ hSt _ hloc PP (fun hu => by
      rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with h | h
      · exact hoff PP hPP h
      · exact hoff PP hPP (h.trans hconj))
  have hr1 : Formalism.L2.DIV.rTup β (flag1L L) (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn _ PP.1 _) = 1
    rw [hred PP.1 (Or.inl PP.2)]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  rw [e]
  unfold Formalism.L2.DIV.levFn
  rw [hr1, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hPP
    rw [hred PP (Or.inr hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hPP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hred PP (Or.inl hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]

theorem gram_eq_one (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hI : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem off_level (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) {U : Set I.ι}
    {L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)} (hL : LevOf X I U L) (t : TupU I U) (Q : PlI X.B px) :
    ∀ PP, PP ∈ (L.datXt t).Pg ∨ PP ∈ (L.datXt t).Q → PP ≠ Q.1 := by
  rintro PP (h | h) rfl
  · have h' : Q.1 ∈ L.Pg := h
    rw [hL.Pg] at h'
    exact Q.2.2.2 (Or.inr h')
  · refine (hL.is.Q_pl t _ h).2 _ h ?_
    exact GlobalTheory.InertNbr.isConjPl_self (D := X.toD7) Q.2.1

theorem inert_neighbours (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) {U : Set I.ι}
    {L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)} (hI : I.Ok) (hL : LevOf X I U L) (t : TupU I U) (Q : PlI X.B px)
    (hQ : Q.1 ∉ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (s : List ℕ) (hs : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank s) :
    ∃ (x : Bridge.Gf X.toD7.sp.X') (A : Finset (Bridge.Gf X.toD7.sp.X')), IsLabElt X.toD7.sp.X' Q.1 (labIn X.toD7.sp.X'.rank s) x ∧
      (∀ a ∈ A, IsLocElt X.toD7.sp.X' Q.1 a) ∧ Bridge.IsDC (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J x A ∧
      ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet X.B.fields.E (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) → M) (g : Bridge.Gf X.toD7.sp.X'),
        ∑ a ∈ A, ψ (decoAd X I t (g * a)) =
          ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb Q.1.asIdeal s (decoAd X I t g : Formalism.L2.Col.DecoSet X.B.fields.E (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)), ψ e := by
  obtain ⟨m, hm⟩ := hL.is.βX
  rw [one_pow] at hm
  have hβ := hL.beta.2
  rw [hβ] at hm
  have key := GlobalTheory.InertNbr.exists_hecke X.toD7.sp.X' (n := X.B.R.N X.B.R.m - 1) (rank_X' X).symm L.ΛX (L.datXt t) hm Q.1 Q.2.1
    (off_level X I hL t Q) hQ 1 1 (one_mem _)
    (fun x => by
      rw [gram_eq_one X I hI, one_mul, inv_one, mul_one]
      exact (LiftBrg.castGL_mem_UA_one X.toD7.sp.cm (rank_X' X).symm x).symm)
    (one_mem _) (one_mem _) s hs
  simp only [inv_one, one_mul, mul_one] at key
  rw [hβ]
  exact key

theorem exists_inertTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') P ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1) := by
  intro X px I hX U Xg tr L eG hI _ hL _ cX gramR c0R _ _ _ _ t P hP
  classical
  have hN := fun (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2) =>
    inert_neighbours X I hI hL t (q.1.1 : PlI X.B px) (fun h => q.1.2 (Or.inr h)) q.2 hq
  exact ⟨{
    hx := fun q => if hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2 then (hN q hq).choose else 1
    hA := fun q => if hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2 then (hN q hq).choose_spec.choose else ∅
    hx_ok := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.1
    hA_loc := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.1
    chi_loc := fun q _ j hj => chi_eq_one X.toD7.sp.X' L.βX (L.datXt t) (q.1.1 : PlI X.B px).1 (q.1.1 : PlI X.B px).2.1
      (off_level X I hL t (q.1.1 : PlI X.B px)) j hj
    hDC := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.2.1
    op_eq := fun q hq f => by
      simp only [dif_pos hq]
      exact opEq X I hX U Xg tr t cX P hP q _ (hN q hq).choose_spec.choose_spec.2.2.2 f }⟩

end GlobalTheory.Mem.R3.RowAd.Inert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesPreimageUnderLift
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

open Classical GlobalTheory.TopStep in

theorem sub_mem_stdAt_of_redV {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (m : GLint E n P) (x : Sp E n)
    (hx : (qOf P : E) • x ∈ stdAt E n P) (hred : ∀ v ∈ stdAt E n P, redV P (m.1 v) = redV P v) :
    m.1 x - x ∈ stdAt E n P := by
  have hq0 : (qOf P : E) ≠ 0 := qOf_ne_zero
  have hk0 := glint_mem m hx
  refine mem_stdAt.2 fun j => ?_
  have hi1 := mem_stdAt.1 hk0 j
  have hi2 := mem_stdAt.1 hx j
  have hr : redP P ((m.1 ((qOf P : E) • x) - (qOf P : E) • x) j) = 0 := by
    rw [Pi.sub_apply, reduction_sub hi1 hi2, sub_eq_zero]
    exact congrFun (hred _ hx) j
  have := intAt_div_of_redP hq (intAt_sub hi1 hi2) hr
  convert this using 1
  rw [LinearEquiv.map_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

set_option maxHeartbeats 1600000 in
open Classical GlobalTheory.TopStep in

theorem cosetIn_act_of_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (p : (I.stp u a i).D b) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), (I.stp u a i).gam b κ = 1 → LiftsInv I κ P g → ∀ z, z ∈ cosetIn ((I.stp u a i).act b κ p) P ↔ g z ∈ cosetIn p P := by
  intro B X I _ u a i b κ p P g hgam hL z
  have hX : B.fields.Ok := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hPr : (B.primes X).Ok := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨γ, h, c⟩ := κ
  have hγ : γ = 1 := by
    have e : ufGL B.fields.E (B.R.N i) γ = 1 := hgam
    have e2 : (toGLm B.fields.E (B.R.N i)) γ.1 = (toGLm B.fields.E (B.R.N i)) 1 := by
      rw [map_one]; exact e
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective e2)
  subst hγ
  set p' := (I.stp u a i).act b ((1 : UF B.fields.E (B.R.N i)), h, c) p with hp'
  have hys : p'.1.2 = p.1.2 := by
    show (fun v => ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) v) '' p.1.2 = p.1.2
    simp
  have hg : ∀ x, g x ∈ stdAt B.fields.E (B.R.N i) P.1 ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1 := hL.1
  have key : ∀ y ∈ p.1.2, ((qOf P.1 : B.fields.E) ^ (if P.1 ∈ (B.primes X).vGs then 0 else (I.cst a).M))⁻¹ •
      (g ((frsF I.sel (I.tup a) p'.1.1 P).symm y) - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
    intro y hy
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · rw [if_pos hP, pow_zero, inv_one, one_smul]
      by_cases hj : i + 1 = B.R.m
      swap
      · have h0 : p.1.2 = ∅ := by
          have := p.2
          rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj] at this
          exact this
        rw [h0] at hy
        exact absurd hy (Set.notMem_empty y)
      obtain ⟨y0, hy0, hY⟩ := PtAt.mem_ybSet p hj
      have hy' : y - y0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup a)) p.1.1.deco.1.N
          (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst a).M : ℤ)) := by
        rw [hY] at hy
        exact hy
      have hA : (qOf P.1 : B.fields.E) • y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy0 P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hB : y - y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy' P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hx : (qOf P.1 : B.fields.E) • y ∈ p.1.1.deco.1.at P.1 := by
        have e : (qOf P.1 : B.fields.E) • y = (qOf P.1 : B.fields.E) • y0 + (qOf P.1 : B.fields.E) • (y - y0) := by
          rw [← smul_add, add_sub_cancel]
        rw [e]
        exact add_mem hA (smul_mem_locP (intAt_nat _) hB)
      let w : (B.primes X).vGs := ⟨P.1, hP⟩
      have hd : p'.1.1.deco.1 = p.1.1.deco.1.act ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) h.1 := rfl
      have hf : IsLiftFr p.1.1.deco.1 w (p.1.1.deco.1.liftFr w) := liftFr_spec p.1.1.deco.2 w
      have hf' : IsLiftFr (p.1.1.deco.1.act ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) h.1) w (p'.1.1.deco.1.liftFr w) := by
        rw [← hd]
        exact liftFr_spec p'.1.1.deco.2 w
      have e1 : frsF I.sel (I.tup a) p.1.1 P = p.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dif_pos hP]
      have e2 : frsF I.sel (I.tup a) p'.1.1 P = p'.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dif_pos hP]
      rw [e1, e2]
      have e3 : (p'.1.1.deco.1.liftFr w).symm y = (passFr (w := w) _ h.1 hf hf').1 ((p.1.1.deco.1.liftFr w).symm y) := by
        show _ = (p'.1.1.deco.1.liftFr w).symm (((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) ((p.1.1.deco.1.liftFr w) ((p.1.1.deco.1.liftFr w).symm y)))
        rw [LinearEquiv.apply_symm_apply]
        rfl
      rw [e3]
      have hv0 : (qOf P.1 : B.fields.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        rw [← LinearEquiv.map_smul, ← hf.1, LinearEquiv.apply_symm_apply]
        exact hx
      have hκ : GlobalTheory.TopStep.redGL (B.R.N i) P.1 (passFr (w := w) _ h.1 hf hf') = h.1 w := redGL_passFr (w := w) _ h.1 hf hf'
      have hq := (degOneUnram_of_mem_vGs hX hPr hP).2
      have hred : ∀ v ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (g ((passFr (w := w) _ h.1 hf hf').1 v)) = redV P.1 v := by
        intro v hv
        rw [hL.2.1 hP _ (glint_mem _ hv), redV_redGL _ hv, hκ, Matrix.mulVec_mulVec]
        show ((h.1 w)⁻¹.1 * (h.1 w).1).mulVec _ = _
        rw [Units.inv_mul, Matrix.one_mulVec]
      have hm := sub_mem_stdAt_of_redV P.1 hq (⟨g, hL.1⟩ * passFr (w := w) _ h.1 hf hf') _ hv0 hred
      exact hm
    · rw [if_neg hP]
      have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
      have hF' : frsF I.sel (I.tup a) p'.1.1 P = frsF I.sel (I.tup a) p.1.1 P * g := by
        unfold frsF
        rw [dif_neg hP, dif_neg hP, hL.2.2 hQ]
        exact LinearEquiv.ext fun x => rfl
      have e : g ((frsF I.sel (I.tup a) p'.1.1 P).symm y) = (frsF I.sel (I.tup a) p.1.1 P).symm y := by
        rw [eq_comm, LinearEquiv.symm_apply_eq]
        rw [hF']
        exact ((frsF I.sel (I.tup a) p.1.1 P * g).apply_symm_apply y).symm
      rw [e, sub_self, smul_zero]
      exact zero_mem _
  simp only [cosetIn, Set.mem_ofPred_eq]
  rw [hys]
  constructor
  · rintro ⟨y, hy, hz⟩
    refine ⟨y, hy, ?_⟩
    have := add_mem ((hg _).2 hz) (key y hy)
    rwa [map_smul, map_sub, ← smul_add, sub_add_sub_cancel] at this
  · rintro ⟨y, hy, hz⟩
    refine ⟨y, hy, ?_⟩
    have := sub_mem hz (key y hy)
    rw [← smul_sub, sub_sub_sub_cancel_right, ← map_sub, ← map_smul] at this
    exact (hg _).1 this

end GlobalTheory.Mem.Col2.AdT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBadPrimeOverBadPlaceOfChain
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

theorem exists_SBof_over : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P ∈ SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P) := by
  classical
  intro B X I hOk l Z a v hv
  obtain ⟨-, hPr, -⟩ := base_fields_primes_ok B X
  rcases hv with hv | ⟨P, hP, rfl⟩
  · have key : ∀ (i : Fin 2), v ∈ plUnder (I.rec7 l Z).host.F (E := (I.rec7 l Z).host.E) ((B.primes X).vG i) ↔ ((B.primes X).g i : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
      intro i
      have h0 : B.fields.conjO ((B.primes X).piG i) ≠ 0 := by
        intro h
        have h1 := hPr.piG_norm i
        rw [h, mul_zero] at h1
        exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) h1.symm
      refine mem_plUnder_iff_norm (I.rec7 l Z).sp.cm (fun P => mem_divs h0 P) ((B.primes X).g i) ?_ v
      have h2 : cO (I.rec7 l Z).host.E (B.fields.conjO ((B.primes X).piG i)) = (B.primes X).piG i := cO_cO ((B.primes X).piG i)
      rw [h2]
      have h3 : B.fields.conjO ((B.primes X).piG i) * (B.primes X).piG i = ((B.primes X).g i : 𝓞 B.fields.E) := by
        rw [mul_comm]
        exact hPr.piG_norm i
      exact h3
    have hv' : v ∈ plUnder (I.rec7 l Z).host.F (E := (I.rec7 l Z).host.E) (B.primes X).vGs := by
      rcases hv with h | h
      · obtain ⟨P, hP, hPv⟩ := (key 0).2 h
        exact ⟨P, Finset.mem_union_left _ hP, hPv⟩
      · obtain ⟨P, hP, hPv⟩ := (key 1).2 h
        exact ⟨P, Finset.mem_union_right _ hP, hPv⟩
    obtain ⟨P, hP, hPv⟩ := hv'
    refine ⟨P, Finset.mem_union_left _ hP, ?_⟩
    exact hPv
  · refine ⟨P, Finset.mem_union_right _ hP, ?_⟩
    exact rfl

end GlobalTheory.Mem.Col2.AdT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelValueRationalStepStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomialModel_value_rational_step : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∃ v : ValQ O u μ i, evC O u μ i v = f := by
  first | exact @GlobalTheory.CmpEx.exists_valQ | exact GlobalTheory.CmpEx.exists_valQ | (intros; apply GlobalTheory.CmpEx.exists_valQ <;> assumption)
end

