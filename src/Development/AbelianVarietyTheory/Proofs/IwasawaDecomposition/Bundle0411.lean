import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.Bundle0035
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.Columns.Bundle0017
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0403
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0093
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamRdefEqSgTrue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowWeight

lemma isWtOfPar_eq {N n : ℕ} (h : N = n) {lam : DomWeight N} {S : SPar} (hS : Bridge.IsWtOfPar lam S)
    (hs : ∀ x ∈ S, x.2 = true) (c' : Fin n → ℚ) (hc' : StrictAnti c') (hm' : ∀ i, (c' i, true) ∈ S) (i : Fin N) :
    (lam.w i : ℚ) = c' (Fin.cast h i) - rhoVec n (Fin.cast h i) := by
  subst h
  obtain ⟨hcard, c, hc, hm, hw⟩ := hS
  have key : ∀ d : Fin N → ℚ, StrictAnti d → (∀ i, (d i, true) ∈ S) → Set.range d = {x | (x, true) ∈ S} := by
    intro d hd hdm
    have h1 : Finset.univ.image (fun i => (d i, true)) = S := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        exact hdm i
      · rw [Finset.card_image_of_injective _ (fun x y h => hd.injective (Prod.ext_iff.mp h).1), hcard]
        simp
    ext x
    rw [← h1]
    simp
  have hm2 : ∀ i, (c i, true) ∈ S := fun i => by
    obtain ⟨s, hs'⟩ := hm i
    have : s = true := hs _ hs'
    rwa [this] at hs'
  have e : c = c' := (hc.range_inj hc').1 ((key c hc hm2).trans (key c' hc' hm').symm)
  rw [hw, e]
  rfl

lemma sgHC_mem {R : Ranks} (P : HCParam R) (n : ℕ) (hn : n < R.N R.m - 1) :
    ∃ x, GlobalTheory.ForcedWeights.entry P x = (Formalism.L2.Col.RowPar.of P).sgHC n - Formalism.L2.Col.RowPar.sh R := by
  have hk := R.m_add_three_le_k
  unfold Ranks.N at hn
  by_cases h1 : n < R.k - 1
  · refine ⟨.inl ⟨n, h1⟩, ?_⟩
    rw [Formalism.L2.Col.RowPar.sgHC_lo _ h1, Formalism.L2.Col.RowPar.vb_lo _ h1]
    simp [GlobalTheory.ForcedWeights.entry]
  · obtain ⟨B, ρ, hρ, rfl⟩ : ∃ B ρ, ρ < R.t + 1 ∧ n = R.k - 1 + B * (R.t + 1) + ρ := by
      refine ⟨(n - (R.k - 1)) / (R.t + 1), (n - (R.k - 1)) % (R.t + 1), Nat.mod_lt _ (by omega), ?_⟩
      have := Nat.div_add_mod (n - (R.k - 1)) (R.t + 1)
      rw [Nat.mul_comm] at this
      omega
    have hBm : B < R.m := by
      apply Nat.lt_of_mul_lt_mul_right (a := R.t + 1)
      omega
    rcases ρ with _ | ρ
    · refine ⟨.inr (.inl ⟨B, hBm⟩), ?_⟩
      rw [Nat.add_zero, Formalism.L2.Col.RowPar.sgHC_b, Formalism.L2.Col.RowPar.bAt_of _ hBm]
      simp [GlobalTheory.ForcedWeights.entry]
    · refine ⟨.inr (.inr (⟨B, hBm⟩, ⟨ρ, by omega⟩)), ?_⟩
      rw [Formalism.L2.Col.RowPar.sgHC_e _ B (ρ + 1) (by omega) (by omega), Formalism.L2.Col.RowPar.eAt_of _ hBm]
      simp only [GlobalTheory.ForcedWeights.entry]
      push_cast
      ring

lemma sgHC_strictAnti {R : Ranks} (P : HCParam R) :
    StrictAnti fun i : Fin (R.N R.m - 1) => (Formalism.L2.Col.RowPar.of P).sgHC i.1 - Formalism.L2.Col.RowPar.sh R := by
  intro i j hij
  have h := Formalism.L2.Col.anti_sub_rho (N := R.N R.m - 1) (Formalism.L2.Col.RowPar.of P).sgHC
    (fun _ hn => Formalism.L2.Col.RowPar.sgHC_step P hn) hij.le
  have h2 : (i.1 : ℚ) < (j.1 : ℚ) := by exact_mod_cast (show i.1 < j.1 from hij)
  simp only [rhoVec] at h ⊢
  linarith

theorem lamRdef_eq (D : D7) (h : D.sp.X'.rank = D.R.N D.R.m - 1) (τ : D.what₂.Tau) (i : Fin D.sp.X'.rank) :
    (Bridge.lamRdef (Ptw D) τ).w i = (Formalism.L2.Col.RowPar.of (D.hc τ)).sgTrue.w (Fin.cast h i) := by
  have hF := GlobalTheory.ForcedWeights.lamRForced D τ
  rw [GlobalTheory.ForcedWeights.dpar_eq] at hF
  have h1 := isWtOfPar_eq h hF (fun x hx => by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
      rfl) _ (sgHC_strictAnti (D.hc τ)) (fun a => by
      obtain ⟨x, hx⟩ := sgHC_mem (D.hc τ) a.1 a.2
      exact Finset.mem_image.2 ⟨x, Finset.mem_univ _, by rw [hx]⟩) i
  rw [← Formalism.L2.Col.RowPar.sgTrue_eq] at h1
  exact_mod_cast h1

theorem lamRdef_eq_sgTrue : ∀ (X : Stages) (τ : X.B.fields.Tau) (i : Fin X.toD7.sp.X'.rank), (Bridge.lamRdef (Ptw X.toD7) τ).w i = (X.B.wts.sgTrue τ).w (Fin.cast (RowAd.rank_X' X) i) :=
  fun X τ i => lamRdef_eq X.toD7 (RowAd.rank_X' X) τ i

end GlobalTheory.Mem.R3.RowWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLevelSplitsAtOffLevelSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg.LevSplitAt

set_option maxHeartbeats 4000000

theorem lev_split_at : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (j : Bridge.Gf (Vc X.toD7 i)) (hj : j ∈ (envL X I hX U Xg tr L cV i t).lev.J),
    ∃ j₁ ∈ (envL X I hX U Xg tr L cV i t).lev.J, ∃ j₂ ∈ (envL X I hX U Xg tr L cV i t).lev.J,
      (envL X I hX U Xg tr L cV i t).isLoc x j₁ ∧ j = j₁ * j₂ ∧
      ∀ l, (envL X I hX U Xg tr L cV i t).isLoc x l → Commute j₂ l := by
  intro X px I hX U Xg tr L hI hV hL cV i t x j hj
  classical
  set L' := L.datVt i t with hL'
  set P : Formalism.L2.DIV.Pl X.toD7.host.E := (x.1.1.1 : Formalism.L2.DIV.Pl X.toD7.host.E) with hPdef
  have hoffP : P ∈ Formalism.L2.DIV.offSet ∅ (sgL X I U t) ∅ := x.1.2
  obtain ⟨hPc, hPn, hPq⟩ := hoffP

  obtain ⟨c, hβ⟩ := hL.is.βV i
  rw [one_pow] at hβ

  have hPg : ∀ PP ∈ (flag1L L').Pg, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L L').Pg = L.Pg from rfl, hL.Pg] at hPP
    exact Finset.mem_union.2 (Or.inl hPP)
  have hQ : ∀ PP ∈ (flag1L L').Q, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L L').Q = L.Q t from rfl, hL.Q t] at hPP
    have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
      simp only [ColIn.Q, tup_ixOf]
    rw [e4] at hPP
    exact Finset.mem_union.2 (Or.inr hPP)
  have hoff : ∀ PP, PP ∈ (flag1L L').Pg ∨ PP ∈ (flag1L L').Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    have hm : PP ∈ sgL X I U t := hPP.elim (hPg PP) (hQ PP)
    refine ⟨fun e => hPn ?_, fun hc => hPq PP ?_ ?_⟩
    · subst e; simp [hm]
    · simp [hm]
    · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]

  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hPc
  have hpi : IsPrimeIdem P e (e + cA X.toD7 e) := Or.inl ⟨he, rfl⟩
  have h01 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Vc X.toD7 i)).2.2.1 P e _ hpi
  have hff := h01.1
  have hcf := h01.2.1
  have h1 : ((1 : ℕ) : 𝓞 X.toD7.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  obtain ⟨-, -, hsp⟩ := (GlobalTheory.LevSplit.lev_split (Vc X.toD7 i) (L.βV i) (L.ΛV i) 1 (flag1L L') hβ).2 P e _ hpi h1 hoff
  obtain ⟨g, hg, hgj⟩ := GlobalTheory.SplitHeckeAdj.fin_lift (Vc X.toD7 i) j
  have hj' : GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) g ∈ (levEnv (Vc X.toD7 i) (L.βV i) L').J := by rw [hgj]; exact hj
  obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, hk⟩ := hsp g ((GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' hg).1 hj')
  refine ⟨GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) k₁, (GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' h₁.1).2 h₁,
    GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) k₂, (GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' h₂.1).2 h₂, ⟨e, k₁, he, h₁.1, s₁, rfl⟩,
    by rw [← hgj, hk, map_mul], ?_⟩
  intro l hl
  obtain ⟨a, ha, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp (Vc X.toD7 i) hl he
  exact (GlobalTheory.SplitHeckeAdj.commute_compl (Vc X.toD7 i) _ hff hcf ha s₂).symm.map (GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i))

end GlobalTheory.Mem.R3.LiftBrg.LevSplitAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelCharacterTypePrimeEqColumnCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.Mem.R3.LevChi

theorem chi_succ_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (w : {w // w ∈ (X.B.primes px).vGs}) (c : (𝓞 X.B.fields.E ⧸ w.1.asIdeal)ˣ),
      L.chi ((i : ℕ) + 1) w.1 c = Units.map X.toD7.what₂.embLL.toMonoidHom (Formalism.L2.Col.chiAt I.Ch w (i : ℕ) c) := by
  intro X px I U L hI hL i w c
  have hw : w.1 ∈ L.Pg := by rw [hL.Pg]; exact w.2
  have hres := hL.is.chi i w.1 hw
  have hmu : L.C.mu0 i = I.C.mu0 i := by rw [hL.C]; rfl
  rw [hmu] at hres
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 X.B.fields.E ⧸ w.1.asIdeal)
  have hy0 : ((y : 𝓞 X.B.fields.E) : X.B.fields.E) ≠ 0 := by
    intro h
    have h0 : y = 0 := RingOfIntegers.ext h
    apply c.ne_zero
    rw [← hy, h0, map_zero]
  let x : X.B.fields.Eˣ := Units.mk0 _ hy0
  have h1 := hres y x c rfl hy.symm
  have h2 := (hI.ch_tied.mu0 i).atg w x y c rfl hy.symm
  have h3 : (((L.chi ((i : ℕ) + 1) w.1 c)⁻¹ : ℂˣ) : ℂ) = X.B.embLL (((I.Ch.chi i w c)⁻¹ : X.B.fields.Kˣ) : X.B.fields.K) :=
    (congrArg Units.val h1).trans h2
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀] at h3
  have h5 : ((L.chi ((i : ℕ) + 1) w.1 c : ℂˣ) : ℂ) = X.B.embLL ((I.Ch.chi i w c : X.B.fields.Kˣ) : X.B.fields.K) :=
    inv_injective h3
  have e : Formalism.L2.Col.chiAt I.Ch w (i : ℕ) = I.Ch.chi i w := by
    unfold Formalism.L2.Col.chiAt Formalism.L2.Col.extChi
    rw [dif_pos (show (i : ℕ) < X.B.R.m from i.2)]
    rfl
  rw [e]
  exact Units.ext h5

end GlobalTheory.Mem.R3.LevChi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftResidueTwistCharacterEqResChar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.LevResXi

theorem xiR_eq_map_resChar : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ (t : TupU I U) (PP : HeightOneSpectrum (𝓞 X.B.fields.E)), PP ∈ Formalism.L2.Col.QE I.sel t.1 →
      ∀ c : (𝓞 X.B.fields.E ⧸ PP.asIdeal)ˣ, L.xiR t PP c = Units.map X.toD7.what₂.embLL.toMonoidHom
        (Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) PP c) := by
  intro X px I U L hI hV hL t PP hPP c
  have hQ : PP ∈ L.Q t := by
    rw [hL.Q t]
    change PP ∈ Formalism.L2.Col.QE I.sel (I.tup (ixOf I U t))
    rw [tup_ixOf]
    exact hPP
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 X.B.fields.E ⧸ PP.asIdeal)
  have hn : b ∉ PP.asIdeal := fun hm => c.ne_zero (hb ▸ Ideal.Quotient.eq_zero_iff_mem.2 hm)
  have h0 : (b : X.B.fields.E) ≠ 0 := fun e => hn ((RingOfIntegers.coe_eq_zero_iff.1 e) ▸ zero_mem _)
  have h1 := hL.is.xiR t PP hQ b (Units.mk0 _ h0) c rfl hb.symm
  have ht : ∀ P, (I.xi (ixOf I U t)).TameAt P := fun P => hL.xiH t ▸ hL.is.xi_tame t P
  have h2 := GlobalTheory.NormOneUnit.resChar_eq (hI.xi_reads (ixOf I U t)) ht PP c b (Units.mk0 _ h0) rfl hb
  rw [tup_ixOf] at h2
  rw [hL.xiH t] at h1
  refine Units.ext ?_
  rw [h1]
  exact h2.symm

end GlobalTheory.Mem.LevResXi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalReciprocityUnramifiedSphericalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_reciprocity_unramified_spherical : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) x,
    GlobalTheory.AutQuot.LocAt π s.w x → π.SphAt s.v → (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 s.w) x).unr := by
  first | exact @GlobalTheory.SphLoc.main | exact GlobalTheory.SphLoc.main | (intros; apply GlobalTheory.SphLoc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCompletedSelfDualLatticeIffIntegralStdFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.SDFrameStd

theorem lamHat_iff_int : ∀ {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V 1 Λ 1 → ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D V Λ hβ y
  obtain ⟨c, hf, -, -, h1, h2⟩ := hβ
  have hset : (Λ : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext x
    constructor
    · intro hx
      have := h2 x hx
      simpa using this
    · intro hx
      have := h1 x hx
      simpa using this
  have e1 : y ∈ Formalism.L2.NTheta.LamHat V ↔ (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [← GlobalTheory.LevSplit.latHat_iff Λ y, hset]
  rw [e1, hf]
  simp only [inv_one, Units.val_one, one_mulVec]
  rfl

end GlobalTheory.Mem.SDFrameStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemHeightOneSpectrumIffAdditiveValuationPos
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

open Classical in

noncomputable def pickIxTw {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) (χ : Formalism.L2.Host.HChar B.host.E) : I.ι :=
  if h : ∃ a, I.xi a = χ then h.choose else I.mu0

theorem xi_pickIxTw {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) {χ : Formalism.L2.Host.HChar B.host.E}
    (h : χ ∈ Set.range I.xi) : I.xi (pickIxTw I χ) = χ := by
  have h' : ∃ a, I.xi a = χ := h
  unfold pickIxTw
  rw [dif_pos h']
  exact h'.choose_spec

theorem plc_eq_of_natCast_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime)
    (h : (p : 𝓞 F) ∈ v.asIdeal) : Formalism.EigenvalueLevelCeiling.plc v = p := by
  have hd : Formalism.EigenvalueLevelCeiling.plc v ∣ p := by
    unfold Formalism.EigenvalueLevelCeiling.plc
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h
  haveI : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact absurd h1 (CharP.ringChar_ne_one)
  · exact h1

section UnitConjugation
open Formalism.BasicNotions.DV

theorem additiveValuation_conjugatePlace_eq_star (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by
  by_cases hx : x = 0
  · subst hx; simp [vAdd]
  · have h1 := D.conj_val w x
    rw [D.val_eq _ x hx, D.val_eq _ (star x) (star_ne_zero.2 hx)] at h1
    exact_mod_cast h1

theorem mem_heightOneSpectrum_iff_additiveValuation_pos {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ≠ 0) : x ∈ w.asIdeal ↔ 0 < vAdd w (x : K) := by
  have hx' : w.valuation K (x : K) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast hx)
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  unfold vAdd
  rw [neg_pos, ← WithZero.log_one, WithZero.log_lt_log hx' one_ne_zero]

theorem plEq_conjPl (D : D7) (w : D.what₂.places.Pl) :
    D.plEq (D.what₂.places.conj w) = Formalism.DivisionValues.conjPl (D.plEq w) := by
  apply HeightOneSpectrum.ext
  ext x
  have key : ∀ y : 𝓞 D.what₂.LL, y ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔
      Formalism.DivisionValues.cO D.what₂.LL y ∈ (D.plEq w).asIdeal := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp
    · rw [mem_heightOneSpectrum_iff_additiveValuation_pos _ y hy, mem_heightOneSpectrum_iff_additiveValuation_pos _ _ ((map_ne_zero_iff _ (Formalism.DivisionValues.cO D.what₂.LL).injective).2 hy),
        additiveValuation_conjugatePlace_eq_star, Formalism.DivisionValues.ValuationRepresentative.cO_apply]
  rw [key]
  change _ ↔ x ∈ (D.plEq w).asIdeal.map (Formalism.DivisionValues.cO D.what₂.LL)
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro h
    exact ⟨_, h, Formalism.DivisionValues.ValuationRepresentative.cO_cO x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [Formalism.DivisionValues.ValuationRepresentative.cO_cO]

end UnitConjugation

end GlobalTheory.Mem.R3

open GlobalTheory.Mem.R3 in

theorem GlobalTheory.Mem.R3.tupL_of_twisted : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))), Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C → L.C = Top.Fr.at X I.C → (∀ t, L.xiH t = I.xi (ixOf I (usedOf I T Wt) t)) → ∃ (mu : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → TupU I (usedOf I T Wt)) (twPl : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))), MuOf X I T Wt mu twPl ∧ ∀ Xg tr, Seed.TupL (famR X I hX (usedOf I T Wt) Xg tr) L mu twPl := by
  classical
  intro X px I hX T Wt L hWf hWc hI hrng hC hxi

  have hmemR : ∀ w ∈ Wt, T.xiTw I.C w ∈ Set.range I.xi := fun w _ => by
    rw [hrng]; exact Or.inr ⟨w, rfl⟩
  have hpickU : ∀ w ∈ Wt, pickIxTw I (T.xiTw I.C w) ∈ (usedOf I T Wt) := fun w hw => ⟨w, hw, xi_pickIxTw I (hmemR w hw)⟩

  let muP : X.B.places.Pl → TupU I (usedOf I T Wt) := fun w =>
    if h : w ∈ Wt then ⟨I.tup (pickIxTw I (T.xiTw I.C w)), Or.inr ((tup_mem_tuOf I).2 (hpickU w h))⟩
    else mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))
  have muP_in : ∀ w (h : w ∈ Wt), muP w = ⟨I.tup (pickIxTw I (T.xiTw I.C w)), Or.inr ((tup_mem_tuOf I).2 (hpickU w h))⟩ :=
    fun w h => dif_pos h
  have muP_of_notMem : ∀ w, w ∉ Wt → muP w = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt)) := fun w h => dif_neg h
  have ix_in : ∀ w ∈ Wt, ixOf I (usedOf I T Wt) (muP w) = pickIxTw I (T.xiTw I.C w) := fun w h => by
    rw [muP_in w h]; exact ixOf_eq I rfl
  have hcc : ∀ w, X.B.places.conj (X.B.places.conj w) = w := fun w => by
    apply X.toD7.plEq.injective
    have e1 := plEq_conjPl X.toD7 (X.toD7.what₂.places.conj w)
    have e2 := plEq_conjPl X.toD7 w
    change X.toD7.plEq (X.toD7.what₂.places.conj (X.toD7.what₂.places.conj w)) = X.toD7.plEq w
    rw [e1, e2, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  have hconjIff : ∀ w, X.B.places.conj w ∈ Wt ↔ w ∈ Wt := fun w =>
    ⟨fun h => hcc w ▸ hWc _ h, hWc w⟩
  have muP_conj : ∀ w, muP (X.B.places.conj w) = muP w := fun w => by
    by_cases h : w ∈ Wt
    · rw [muP_in w h, muP_in _ ((hconjIff w).2 h)]
      congr 2
      rw [(GlobalTheory.Mem.Top.TwFin.tw_fin X.B I.C T).2.2.1 w]
    · rw [muP_of_notMem w h, muP_of_notMem _ (fun h' => h ((hconjIff w).1 h'))]
  have hss : ∀ w : X.B.places.Pl, muP (X.toD7.plEq.symm (X.toD7.plEq w)) = muP w :=
    fun w => congrArg muP (X.toD7.plEq.symm_apply_apply w)
  refine ⟨fun v => muP (X.toD7.plEq.symm v), hWf.toFinset.image X.toD7.plEq, ?_, ?_⟩
  · intro w
    refine ⟨?_, ?_⟩
    · erw [Finset.mem_image]
      constructor
      · rintro ⟨w', hw', e⟩
        rw [X.toD7.plEq.injective e] at hw'
        exact (Set.Finite.mem_toFinset hWf).1 hw'
      · intro h
        exact ⟨w, (Set.Finite.mem_toFinset hWf).2 h, rfl⟩
    · show I.xi (ixOf I (usedOf I T Wt) (muP (X.toD7.plEq.symm (X.toD7.plEq w)))) = _
      rw [hss]
      by_cases h : w ∈ Wt
      · rw [if_pos h, ix_in w h, xi_pickIxTw I (hmemR w h)]
      · rw [if_neg h, muP_of_notMem w h, ixOf_mu0F]
        exact hI.trueColumnChoices_heckeChar_reference_eq_one
  · intro Xg tr
    have hμ0 : (famR X I hX (usedOf I T Wt) Xg tr).A.μ0 = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt)) := rfl
    have memTw : ∀ v, v ∈ hWf.toFinset.image X.toD7.plEq ↔ X.toD7.plEq.symm v ∈ Wt := fun v => by
      erw [Finset.mem_image]
      constructor
      · rintro ⟨w', hw', rfl⟩
        rw [Equiv.symm_apply_apply]
        exact (Set.Finite.mem_toFinset hWf).1 hw'
      · intro h
        exact ⟨_, (Set.Finite.mem_toFinset hWf).2 h, Equiv.apply_symm_apply _ _⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [hμ0]
      exact muP_of_notMem _ (fun h => hv ((memTw v).2 h))
    · intro t
      rw [hμ0]
      rcases t.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · right
        obtain ⟨b, hb, e⟩ := (mem_tuOf I).1 h
        obtain ⟨w, hw, hbw⟩ := hb
        refine ⟨X.toD7.plEq w, ?_⟩
        show muP (X.toD7.plEq.symm (X.toD7.plEq w)) = t
        rw [hss, muP_in w hw]
        apply Subtype.ext
        show I.tup (pickIxTw I (T.xiTw I.C w)) = t.1
        rw [← e]
        congr 1
        apply hI.xi_inj
        rw [xi_pickIxTw I (hmemR w hw), hbw]
    · intro v hv e
      rw [hμ0] at e
      have hw := (memTw v).1 hv
      have h1 := congrArg (ixOf I (usedOf I T Wt)) e
      rw [ix_in _ hw, ixOf_mu0F] at h1
      have h2 := congrArg I.xi h1
      rw [xi_pickIxTw I (hmemR _ hw), hI.trueColumnChoices_heckeChar_reference_eq_one] at h2
      exact (GlobalTheory.Mem.Top.TwFin.tw_fin X.B I.C T).2.1 _ h2
    · intro v
      have e : Formalism.DivisionValues.conjPl v = X.toD7.plEq (X.B.places.conj (X.toD7.plEq.symm v)) := by
        have := plEq_conjPl X.toD7 (X.toD7.plEq.symm v)
        rw [Equiv.apply_symm_apply] at this
        exact this.symm
      show muP (X.toD7.plEq.symm (Formalism.DivisionValues.conjPl v)) = muP (X.toD7.plEq.symm v)
      rw [e, hss]
      exact muP_conj _
    · intro v hv
      have hw := (memTw v).1 hv
      set w := X.toD7.plEq.symm v with hwdef
      have hv' : v = X.toD7.plEq w := by rw [hwdef, Equiv.apply_symm_apply]
      have hpl : Formalism.EigenvalueLevelCeiling.plc v = X.B.places.resChar w := by
        rw [hv']
        exact plc_eq_of_natCast_mem _ (X.B.places.resChar_prime w) (GlobalTheory.LvT.Inh.resChar_mem_plEq X.toD7 w)
      refine ⟨T.psi w, T.Q w, ?_, ?_⟩
      · rw [hpl]; exact T.psi_is w
      · rw [hxi, hpl, hC]
        show I.xi (ixOf I (usedOf I T Wt) (muP w)) = _
        rw [ix_in w hw, xi_pickIxTw I (hmemR w hw)]
        rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricCharacterMulOfTameStatement
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricCharacter_mul_of_tame : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (δ : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) (P.adicCompletion L)), k ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → k' ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by
  first | exact @GlobalTheory.Mem.LamMul.lamJ_mul | exact GlobalTheory.Mem.LamMul.lamJ_mul | (intros; apply GlobalTheory.Mem.LamMul.lamJ_mul <;> assumption)
end

