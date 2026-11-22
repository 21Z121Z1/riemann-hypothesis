import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0007
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0134
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0001
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0036

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepGroupCharacterInverseTypeAtLifts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT

section Split

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S Q : Finset (HeightOneSpectrum (𝓞 E))}

open Classical in

def compVal (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) (p : HeightOneSpectrum (𝓞 E)) : Kˣ :=
  if h : p ∈ S then (Λ ⟨p, h⟩).lam ⟨k1.1 ⟨p, h⟩, k1.2 _ (Set.mem_univ _)⟩
  else if h' : p ∈ Q then (Θ ⟨p, h'⟩).lam ⟨k2.1 ⟨p, h'⟩, k2.2 _ (Set.mem_univ _)⟩ else 1

theorem compVal_left (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) {p : HeightOneSpectrum (𝓞 E)} (h : p ∈ S) :
    compVal Λ Θ k1 k2 p = (Λ ⟨p, h⟩).lam ⟨k1.1 ⟨p, h⟩, k1.2 _ (Set.mem_univ _)⟩ := by
  unfold compVal
  rw [dif_pos h]

theorem compVal_right (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) {p : HeightOneSpectrum (𝓞 E)} (h : p ∉ S)
    (h' : p ∈ Q) : compVal Λ Θ k1 k2 p = (Θ ⟨p, h'⟩).lam ⟨k2.1 ⟨p, h'⟩, k2.2 _ (Set.mem_univ _)⟩ := by
  unfold compVal
  rw [dif_neg h, dif_pos h']

open Classical in

theorem prod_compVal (hd : Disjoint S Q) (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) :
    ∏ p ∈ S ∪ Q, compVal Λ Θ k1 k2 p = Λ.chr k1 * Θ.chr k2 := by
  have e1 : Λ.chr k1 = _ := piChar_apply (fun w => (Λ w).H) (fun w => (Λ w).lam) k1
  have e2 : Θ.chr k2 = _ := piChar_apply (fun w => (Θ w).H) (fun w => (Θ w).lam) k2
  rw [e1, e2, Finset.prod_union hd, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort Q]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
  · exact dif_pos w.2
  · exact (dif_neg (Finset.disjoint_right.1 hd w.2)).trans (dif_pos w.2)

end Split
end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

section Cong

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem congE_mul_one {P : HeightOneSpectrum (𝓞 E)} {c : ℕ} {k g g' : Sp E n ≃ₗ[E] Sp E n}
    (hk : k ∈ GLint E n P) (hkg : k * g' = 1) (h : CongE P c g g') : CongE P c (k * g) 1 := by
  intro x hx
  have e1 : (k * g) x - (1 : Sp E n ≃ₗ[E] Sp E n) x = k (g x - g' x) := by
    rw [map_sub, ← LinearEquiv.mul_apply k g', hkg]
    rfl
  rw [e1, ← map_smul]
  exact (hk _).2 (h x hx)

end Cong
end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

variable {B : Base} {X : PreX B.toPre}

theorem chiInv_at_type (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (al : (I.idx a).β i) (P : SBof I a)
    (hP : P.1 ∈ (B.primes X).vGs) (gP g'P : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (r : AutY B.fields B.R i)
    (hr : r ∈ Loc.Cbe (Jat (Pr := B.primes X) (I.cst a).sharp i P.1) ((I.idx a).h i al P))
    (hrx : ∀ x, r (Loc.inX B.fields.E (B.R.N i) (cOf B.R i) x) = Loc.inX B.fields.E (B.R.N i) (cOf B.R i) (gP x))
    (κw : GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ P.1.asIdeal)) (hκw : κw ∈ (((I.idx a).levG i al) ⟨P.1, hP⟩).H)
    (hred' : ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (g'P x) = (κw⁻¹).1.mulVec (redV P.1 x))
    (hcong : CongE P.1 ((I.cst a).D P) gP g'P) :
    chiInv I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) r =
      (((((I.idx a).levG i al) ⟨P.1, hP⟩).lam ⟨κw, hκw⟩ : B.fields.Kˣ) : B.fields.K)⁻¹ := by
  have hL := hOk.idx_ok a
  have hD : (I.cst a).D P = 1 := hL.depthG P hP
  have hred : ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (gP x) = (κw⁻¹).1.mulVec (redV P.1 x) := by
    intro x hx
    rw [← hred' x hx]
    have h1 := (mem_localization_standardLattice _ _).1 (hcong x hx)
    rw [hD, pow_one] at h1
    have hq0 : ((qOf P.1 : ℕ) : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
    funext l
    have e1 : gP x l = g'P x l + (qOf P.1 : B.fields.E) * (((qOf P.1 : ℕ) : B.fields.E)⁻¹ • (gP x - g'P x)) l := by
      rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      field_simp
      ring
    show redP P.1 (gP x l) = redP P.1 (g'P x l)
    rw [e1]
    exact GlobalTheory.LastSteps.redP_add_q (h1 l)
  have hc := hL.chrG i al ⟨P.1, hP⟩ (⟨κw, hκw⟩)⁻¹ gP r hr hrx hred
  exact hc.symm.trans ((congrArg Units.val (map_inv (((I.idx a).levG i al) ⟨P.1, hP⟩).lam _)).trans (Units.val_inv_eq_inv_val _))

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

variable {B : Base} {X : PreX B.toPre}

theorem chiInv_at_twist (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (al : (I.idx a).β i) (P : SBof I a)
    (hQ : P.1 ∈ I.Q a) (gP g'P : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (r : AutY B.fields B.R i)
    (hr : r ∈ Loc.Cbe (Jat (Pr := B.primes X) (I.cst a).sharp i P.1) ((I.idx a).h i al P))
    (hrx : ∀ x, r (Loc.inX B.fields.E (B.R.N i) (cOf B.R i) x) = Loc.inX B.fields.E (B.R.N i) (cOf B.R i) (gP x))
    (κQ : ↥(GLint B.fields.E (B.R.N i) P.1)) (hκQ : κQ ∈ (((I.idx a).levQ i al) ⟨P.1, hQ⟩).H)
    (hg' : g'P = (κQ⁻¹).1) (hcong : CongE P.1 ((I.cst a).D P) gP g'P) :
    chiInv I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) r =
      (((((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨κQ, hκQ⟩ : B.fields.Kˣ) : B.fields.K)⁻¹ := by
  have hL := hOk.idx_ok a
  have hg : gP ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp i P.1 ((I.idx a).h i al P) := ⟨r, hr, hrx⟩
  let gI : ↥(GLint B.fields.E (B.R.N i) P.1) := ⟨gP, hL.int i al P hg⟩
  have hH : gI ∈ (((I.idx a).levQ i al) ⟨P.1, hQ⟩).H := by
    rw [hL.grpQ i al ⟨P.1, hQ⟩]
    exact Subgroup.mem_subgroupOf.2 hg
  have hc := hL.chrQ i al ⟨P.1, hQ⟩ ⟨gI, hH⟩ r hr hrx
  have hkg : κQ.1 * g'P = 1 := by
    rw [hg']
    exact congrArg Subtype.val (mul_inv_cancel κQ)
  have hcd : CongE P.1 ((I.cst a).D P) (κQ * gI).1 1 := congE_mul_one (g := gP) κQ.2 hkg hcong
  obtain ⟨hdH, hdl⟩ := levQ_deep I hOk a i hi al P hQ (κQ * gI) hcd
  have e2 : (⟨gI, hH⟩ : ↥(((I.idx a).levQ i al) ⟨P.1, hQ⟩).H) = (⟨κQ, hκQ⟩)⁻¹ * ⟨κQ * gI, hdH⟩ :=
    Subtype.ext (by show gI = κQ⁻¹ * (κQ * gI); group)
  have h4 : (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ((⟨κQ, hκQ⟩)⁻¹ * ⟨κQ * gI, hdH⟩) = ((((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨κQ, hκQ⟩)⁻¹ :=
    ((map_mul (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam _ _).trans ((congrArg _ hdl).trans (mul_one _))).trans (map_inv (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam _)
  exact hc.symm.trans ((congrArg Units.val ((congrArg (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam e2).trans h4)).trans (Units.val_inv_eq_inv_val _))

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

open Classical in

theorem chr_mul_prod_midAt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, MidAt I hi b P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 ((I.cst a).D P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  intro B X I hOk u a i hi b κ g g' z H
  obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al hi := ⟨_, (Idx.of_get b hi hi).symm⟩
  let k1 : ↥((I.idx a).levG i al).grp := κ.2.1
  let k2 : ↥((I.idx a).levQ i al).grp := κ.2.2
  have e : (((I.stp u a i).chr (Idx.of al hi) κ : B.fields.Kˣ) : B.fields.K) =
      ((((I.idx a).levG i al).chr k1 * ((I.idx a).levQ i al).chr k2 : B.fields.Kˣ) : B.fields.K) := rfl
  rw [e]
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_right.2 fun {P} hP => GlobalTheory.Mem.Col2.TC.Q_notMem_of_ok hOk a P hP
  have hprod : ∏ P : SBof I a, compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2 P.1 =
      ((I.idx a).levG i al).chr k1 * ((I.idx a).levQ i al).chr k2 := by
    rw [Finset.prod_coe_sort (SBof I a) (compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2)]
    exact prod_compVal hd _ _ k1 k2
  have hz : ∀ P : SBof I a, z P = ((compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2 P.1 : B.fields.Kˣ) : B.fields.K)⁻¹ := by
    intro P
    obtain ⟨⟨r, hr, hrx, hzr⟩, hlift, hcong⟩ := H P
    rw [hzr]
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · refine (chiInv_at_type I hOk a i al P hP (g P) (g' P) r hr hrx (k1.1 ⟨P.1, hP⟩) (k1.2 _ (Set.mem_univ _))
        (hlift.2.1 hP) hcong).trans ?_
      rw [compVal_left _ _ k1 k2 hP]
    · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
      refine (chiInv_at_twist I hOk a i hi al P hQ (g P) (g' P) r hr hrx (k2.1 ⟨P.1, hQ⟩) (k2.2 _ (Set.mem_univ _))
        (hlift.2.2 hQ) hcong).trans ?_
      exact congrArg (fun x : B.fields.Kˣ => (x : B.fields.K)⁻¹) (compVal_right _ _ k1 k2 hP hQ).symm
  rw [← hprod, Finset.prod_congr rfl fun P _ => hz P, Units.coe_prod, Finset.prod_inv_distrib]
  exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.2 fun P _ => Units.ne_zero _)

end GlobalTheory.Mem.Col2.AdT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueKernelJetsLiftDegreesAlgebraic
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.LvT.Built.KMap

set_option maxHeartbeats 1000000 in

theorem jetC_th_mem_Qbar : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ)
    (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ColIn.JetsIn I →
    ∀ u μ i, i < B.R.m → ∀ (c : ((I.rec7 l Z).chTw u μ).cls i) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1))
      (m : DVar (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) →₀ ℕ),
      (∀ τ, ∑ β, ∑ α, m (τ, β, α) = ∑ r, nuT (I.rec7 l Z) u i τ r) → jetC (O u μ).dgen ((O u μ).Th i c c') m ∈ Qbar := by
  classical
  intro B X I hOk hPins l Z Qp O hO hJ u μ i hi c c' m hm
  rw [hO.dgen, hO.Th]
  have hdeg : ∀ τ, (monoDeg m τ : ℤ) = nuDeg B u i τ := by
    intro τ
    rw [monoDeg_eq_sum, hm τ, Nat.cast_sum]
    unfold nuDeg
    refine Finset.sum_congr rfl fun r _ => ?_
    have e1 : ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℝ) = DV.nuRow (I.rec7 l Z) u (i + 1) τ r := (nu_t_identity (I.rec7 l Z) u i hi τ r).1
    have e2 := GlobalTheory.ColPeriod.nuRow_succ_eq_wt (I.rec7 l Z) u i hi τ r r.2
    have e3 := B.wts.nuW_eq u hi τ r
    have e4 := lamOf_wtN (B.wts.hc u τ) hi.le r
    have key : (((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) : ℝ) = (((B.wts.nuW u (i + 1) τ).w r : ℤ) : ℝ) := by
      rw [Int.cast_natCast, e1, e2, ← Rat.cast_intCast, e3]
      unfold Wts.lamN at e3 ⊢
      rw [e4]
      rfl
    exact_mod_cast key
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := GlobalTheory.T.trueColumn_periodLattice_vacuumSmooth I hOk hPins l Z μ u i hi
  set p := (I.stp u μ i).rep c
  set p' := (I.stp u μ (i + 1)).rep c'
  have hN : IsSdLat p.1.1.deco.1.N := ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩
  have hN' : IsSdLat p'.1.1.deco.1.N := ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) :=
    pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB : 0 < cBof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) u := GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup μ) (I.cst μ) (I.idx μ) _ _ u i hX hPr
    hOk.sel_ok (hOk.T_mem u) hOk.g_mem (hOk.idx_ok μ) hi ⟨_, _, _, _, hOk.ch_tied⟩ c.1 c'.1 p p'
  set N := p.1.1.deco.1.N
  set N' := p'.1.1.deco.1.N
  set cA := cAof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ)
  set cB := cBof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) u
  set Ξ := xiAt (Pr := B.primes X) I.Ch I.sel (I.tup μ) (I.cst μ) (I.idx μ) u i c.1 c'.1 p p'
  have hth := GlobalTheory.latSum_thInd_eq_thC B.fields I.A _ _ (I.Sb μ u) N N' cA cB (fun x => I.A.σ₀ (Ξ x))
    (indTieD_of_la I.A _ _ _ _ (Nat.mul_pos hA hB) hLa) hN hN' hA hB (volC_pos_of_laHyp I.A _ _ _ hLa hN hN')
    (GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ _ _ _ _ _ hN.1 hN'.1 hA hB) (fun x hx => hbox.1 x ((map_ne_zero _).1 hx))
    (fun x y hy => congrArg I.A.σ₀ (hbox.2 x y hy))
  have hfin := GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ (I.Sb μ u) N N' cA cB hN.1 hN'.1 hA hB
  let _ := @Fintype.ofFinite _ hfin
  rw [show I.th u μ i c.1 c'.1 p p' = fun z => _ from funext fun z => (hth z).symm]
  unfold latSum
  simp only [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((Formalism.L2.Col.mulLat cB (homAt (I.Sb μ u) N N')).comap (divLat cA (homAt (I.Sb μ u) N N')).subtype))
  have hs : ∀ q (k : ℕ), ContDiff ℂ k (I.A.thInd (I.Sb μ u) N N' cB (r q)) := fun q =>
    indSmooth_of I.A _ _ (I.Sb μ u) (cA * cB) hE N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩
  rw [show I.J.cD = I.A.cD from rfl]
  have hsum := jetC_sum I.A.cD (fun q => I.A.σ₀ (Ξ (r q))) (fun q => I.A.thInd (I.Sb μ u) N N' cB (r q)) hs m
  have hchi : ∀ 𝔞, I.chi 𝔞 ≠ 0 := fun 𝔞 => by
    unfold ColIn.chi chiId
    exact Units.ne_zero _
  have hF0 : I.A.chiF _ _ N N' ≠ 0 := by
    show Th.chiFac B.host I.chi _ _ N N' ≠ 0
    unfold Th.chiFac
    exact mul_ne_zero (zpow_ne_zero _ (hchi _)) (zpow_ne_zero _ (hchi _))
  have hF : I.A.chiF _ _ N N' ∈ B.embLL.fieldRange := by
    show Th.chiFac B.host I.chi _ _ N N' ∈ B.embLL.fieldRange
    unfold Th.chiFac
    have hv := (GlobalTheory.Mem.ChiVal.chi_values B X I hOk).2
    exact mul_mem (zpow_mem (hv _) _) (zpow_mem (hv _) _)
  have hmem : (∑ q, I.A.σ₀ (Ξ (r q)) * jetC I.A.cD (I.A.thInd (I.Sb μ u) N N' cB (r q)) m) ∈ B.embLL.fieldRange := by
    refine Subfield.sum_mem _ fun q _ => Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) ?_
    obtain ⟨y, hy⟩ := hJ.exists_eq (a := μ) (u := u) (N := N) (N' := N') (c := cB) (x := (r q).1) (e := m) hi
      ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩ hdeg
    rw [← mul_inv_cancel_left₀ hF0 (jetC I.A.cD (I.A.thInd (I.Sb μ u) N N' cB (r q)) m)]
    exact Subfield.mul_mem _ hF ⟨y, hy⟩
  have hQ : ∀ x ∈ B.embLL.fieldRange, x ∈ Qbar := by
    rintro _ ⟨y, rfl⟩
    exact mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) y).algHom B.embLL.toRatAlgHom)
  show jetC I.A.cD (fun z => ∑ q, I.A.σ₀ (Ξ (r q)) * I.A.thInd (I.Sb μ u) N N' cB (r q) z) m ∈ Qbar
  rw [hsum]
  exact hQ _ hmem

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3

theorem twArgs_lev : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t), HEq a.x.R.C (Top.Fr.at (w.st Z) f) ∧ HEq a.x.R.Pg (B.primes w.px).vGs ∧ (∀ μ, Formalism.IndefR.RecTie.Used0 (w.st Z).toD7 μ → HEq (a.x.R.Q (a.x.Y.tupT μ)) (w.I.Q μ) ∧ HEq (a.x.R.toLevCh.xiH (a.x.Y.tupT μ)) (w.I.xi μ)) ∧ (∀ i p v s, a.x.R.EEp3 p ≠ ⊥ → ∃ p' s', HEq p' p ∧ HEq s' s ∧ a.x.R.lam3 i s p v = t.r.z.R.lam3 i s' p' v) := by
  intro K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tupT = t.r.Y.tupT := eq_of_heq htupT
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact heq_of_eq (t.r.z.lev.C.trans (congrArg _ w.C_eq))
  · exact heq_of_eq t.r.z.lev.Pg
  · intro μ hμ
    have hix : ixOf w.I (usedOf w.I T Wt) (t.r.Y.tupT μ) = μ := (t.r.tup_ix _).symm.trans (t.r.Y.tupTie μ hμ)
    have e1 : t.r.z.R.Q (Y.tupT μ) = w.I.Q μ :=
      (congrArg (fun g => t.r.z.R.Q (g μ)) hT').trans ((t.r.z.lev.Q _).trans (congrArg _ hix))
    have e2 : t.r.z.R.xiH (Y.tupT μ) = w.I.xi μ :=
      (congrArg (fun g => t.r.z.R.xiH (g μ)) hT').trans ((t.r.z.lev.xiH _).trans (congrArg _ hix))
    refine ⟨?_, ?_⟩
    · exact (by with_unfolding_all exact (heq_of_eq e1 :))
    · exact (by with_unfolding_all exact (heq_of_eq e2 :))
  · intro i p v s hp
    refine ⟨p, s, HEq.rfl, HEq.rfl, ?_⟩
    kexactB lam_eq i s p v (by kexactB hp)

end GlobalTheory.Mem.R3
end

