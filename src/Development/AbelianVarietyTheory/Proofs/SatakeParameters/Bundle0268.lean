import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly
import Formalism.LocalToGlobal.InertKernelTheory.K2OfAgreements
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.XtSumSingle
import Formalism.LocalToGlobal.Columns.Bundle0054
import Formalism.LocalToGlobal.Columns.ChainTopLawB
import Formalism.LocalToGlobal.Columns.Bundle0057
import Formalism.LocalToGlobal.Columns.ChainTopLawTw
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0262
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.Bundle0063
import Formalism.LocalToGlobal.Columns.Bundle0064
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0263

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsSharpAtOfValTied
section
noncomputable section

namespace GlobalTheory.FormsSharpTie

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.KerInert.K2

theorem natW_antitone {n : ℕ} (l : DomWeight n) : Antitone l.natW := by
  intro a b h
  simp only [DomWeight.natW]
  exact Int.toNat_le_toNat (by have := l.anti h; omega)

theorem ratSpan_le_wtPol (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) :
    ∀ P ∈ RatSpan D lam, P ∈ WtPol ℂ (fun τ r => (lam τ).natW r) := by
  intro P hP
  have hle : RatSpan D lam ≤ (WtPol ℂ (fun τ r => (lam τ).natW r)).toAddSubgroup := by
    unfold RatSpan
    rw [AddSubgroup.closure_le]
    rintro p ⟨r, f, hf, rfl⟩
    show _ ∈ WtPol ℂ _
    apply Submodule.smul_mem
    apply GlobalTheory.KerWt.VV_le_WtPol lam
    unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
    apply Submodule.subset_span
    refine ⟨fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ), fun τ => ?_, rfl⟩
    have h1 : MvPolynomial.map (Int.castRingHom ℂ) (f τ) ∈ delSq ℂ n (lam τ) := by
      rw [← GlobalTheory.Published.span_map_delSq ℤ ℂ (Int.castRingHom ℂ) n (lam τ)]
      exact Submodule.subset_span ⟨f τ, hf τ, rfl⟩
    exact Formalism.GradedWeylDivisibility.weylLeDual ℂ n n le_rfl _ (natW_antitone (lam τ)) h1
  exact hle hP

theorem eval_colSub {ι : Type} [Fintype ι] {a : ℕ} (β x : ι → Matrix (Fin a) (Fin a) ℂ) (p : Formalism.L2.DIV.Pol ℂ ι a) :
    MvPolynomial.eval (fun k : ι × Fin a × Fin a => x k.1 k.2.1 k.2.2) (colSub β p) =
      MvPolynomial.eval (fun k : ι × Fin a × Fin a => (x k.1 * β k.1) k.2.1 k.2.2) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [colSub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, colSub, MvPolynomial.aeval_X, MvPolynomial.eval_X, Matrix.mul_apply]
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [mul_comm]

theorem zpow_mul_pow_toNat {x : ℂ} (hx : x ≠ 0) (s : ℤ) : x ^ s * x ^ (-s).toNat = x ^ s.toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  omega

theorem isVLam_of_wtPol {ι : Type} [Fintype ι] {a : ℕ} {Y : Type} (fr g : Y → ι → Matrix (Fin a) (Fin a) ℂ)
    (B : ι → Matrix (Fin a) (Fin a) ℂ) (hB : ∀ τ, (B τ).det ≠ 0) (hg : ∀ y τ, (g y τ).det ≠ 0)
    (hfr : ∀ y τ, fr y τ = B τ * g y τ) (ν : ι → Fin a → ℕ) (s : ι → ℤ) (P : Formalism.L2.DIV.Pol ℂ ι a)
    (hP : P ∈ WtPol ℂ ν) :
    IsVLam fr (fun τ r => (ν τ r : ℤ) + s τ)
      (fun y => (∏ τ, (g y τ).det ^ s τ) * MvPolynomial.eval (fun x : ι × Fin a × Fin a => g y x.1 x.2.1 x.2.2) P) := by
  have hBu : ∀ τ, IsUnit (B τ).det := fun τ => isUnit_iff_ne_zero.2 (hB τ)
  have hg' : ∀ y τ, g y τ = (B τ)⁻¹ * fr y τ := by
    intro y τ
    rw [hfr, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hBu τ), Matrix.one_mul]
  refine ⟨?_, ?_⟩
  ·
    let sub : Formalism.L2.DIV.Pol ℂ ι a →ₐ[ℂ] Formalism.L2.DIV.Pol ℂ ι a :=
      MvPolynomial.aeval fun v => ∑ c, MvPolynomial.C ((B v.1)⁻¹ v.2.1 c) * MvPolynomial.X (v.1, c, v.2.2)
    have hsub : ∀ y (p : Formalism.L2.DIV.Pol ℂ ι a), MvPolynomial.eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (sub p) =
        MvPolynomial.eval (fun k : ι × Fin a × Fin a => g y k.1 k.2.1 k.2.2) p := by
      intro y p
      induction p using MvPolynomial.induction_on with
      | C c => simp [sub]
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p v hp =>
        simp only [map_mul, hp, sub, MvPolynomial.aeval_X, MvPolynomial.eval_X, hg', Matrix.mul_apply, map_sum]
        simp
    have hdet : ∀ y τ, MvPolynomial.eval (fun k : ι × Fin a × Fin a => g y k.1 k.2.1 k.2.2) (frDet ℂ a τ) = (g y τ).det := by
      intro y τ
      unfold frDet
      rw [RingHom.map_det]
      congr 1
      ext i k
      simp
    refine ⟨MvPolynomial.C (∏ τ, (B τ).det ^ (-s τ).toNat) * (∏ τ, sub (frDet ℂ a τ) ^ (s τ).toNat) * sub P,
      fun τ => (-s τ).toNat, fun y => ?_⟩
    simp only [frPolyG, LinearMap.coe_mk, AddHom.coe_mk, map_mul, map_prod, map_pow, MvPolynomial.eval_C, hsub, hdet]
    have e2 : ∀ τ, (g y τ).det ^ s τ * (g y τ).det ^ (-s τ).toNat = (g y τ).det ^ (s τ).toNat :=
      fun τ => zpow_mul_pow_toNat (hg y τ) (s τ)
    simp only [hfr, Matrix.det_mul, mul_pow, Finset.prod_mul_distrib]
    rw [← Finset.prod_congr rfl fun τ _ => e2 τ, Finset.prod_mul_distrib]
    ring
  ·
    intro y y₂ β hβ hy
    have hgy : ∀ τ, g y₂ τ = g y τ * β τ := by
      intro τ
      have h := hy τ
      rw [hfr, hfr, Matrix.mul_assoc] at h
      have h2 := congrArg (fun M => (B τ)⁻¹ * M) h
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hBu τ), Matrix.one_mul] at h2
      exact h2
    have hdβ : ∀ τ, (β τ).det = ∏ r, β τ r r := fun τ =>
      Matrix.det_of_upperTriangular (fun r s h => (hβ τ).1 r s h)
    have hev : MvPolynomial.eval (fun x : ι × Fin a × Fin a => g y₂ x.1 x.2.1 x.2.2) P =
        (∏ τ, ∏ r, β τ r r ^ ν τ r) * MvPolynomial.eval (fun x : ι × Fin a × Fin a => g y x.1 x.2.1 x.2.2) P := by
      have := eval_colSub β (g y) P
      rw [hP β hβ, MvPolynomial.smul_eval] at this
      simp only [hgy]
      rw [← this]
    have hne : ∀ τ r, β τ r r ≠ 0 := fun τ r => (hβ τ).2 r
    have e3 : ∀ τ r, β τ r r ^ ((ν τ r : ℤ) + s τ) = β τ r r ^ ν τ r * β τ r r ^ s τ := by
      intro τ r
      rw [zpow_add₀ (hne τ r), zpow_natCast]
    dsimp only
    rw [hev]
    simp only [hgy, Matrix.det_mul, hdβ, mul_zpow, e3, Finset.prod_mul_distrib, ← Finset.prod_zpow]
    ring

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset in

theorem sharpWt_rat (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) (r : Fin (D.R.N j)) :
    ((((nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ : ℤ)) : ℚ) =
        ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) - (j : ℚ) * ((D.R.t : ℚ) + 1) / 2 := by
  have h1 := (GlobalTheory.KerWt.nu_t_identity D u j hj τ r).1
  have h2 := (D.chTw u μ).sSharp_eq j hj τ
  have h3 := (Tw.fm u μ).lam_eq j hj.le τ r
  have h2' : (((D.chTw u μ).sSharp j τ : ℤ) : ℝ) =
      (((D.hcW u τ).e ⟨j, hj⟩ : ℚ) : ℝ) - ((D.R.k : ℝ) + ((j : ℝ) + 1) * ((D.R.t : ℝ) + 1)) / 2 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h2
    simp only [sExp', Ranks.N] at this
    push_cast at this
    exact this
  have he : ∀ (k : ℕ) (hk : k < D.R.m), k = j → (D.hc τ).e ⟨k, hk⟩ = (D.hcW u τ).e ⟨j, hj⟩ := by
    rintro k hk rfl; rw [D.hcW_e]
  apply Rat.cast_injective (α := ℝ)
  have hw : ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℝ) = (((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  push_cast
  rw [h1, h2', hw, h3]
  unfold DV.nuRow DV.srcPar DV.wSz
  rw [dif_pos (show 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m by omega), he _ _ (by omega)]
  simp only [Ranks.N]
  by_cases hr : r.1 < D.R.k
  · rw [dif_pos hr, dif_pos hr]
    simp only [hcToWeightQ, rhoVec]
    push_cast
    ring
  · have hb : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by
      have := D.R.blk_lt hj.le r hr
      omega
    rw [dif_neg hr, dif_neg hr, dif_pos hb]
    have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
    have hrk : (r.1 : ℝ) = D.R.k + (D.R.t + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have : r.1 = D.R.k + (D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1) := by omega
      exact_mod_cast this
    simp only [wG]
    push_cast
    rw [hrk]
    ring

theorem nuT_sub_sSharp (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) (r : Fin (D.R.N j)) :
    (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ = (lamTG (Tw.fm u μ) j τ).w r := by
  have h := sharpWt_rat D Tw u μ j hj τ r
  set z : ℤ := (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ with hz
  set w : ℤ := ((Tw.fm u μ).lam j τ).w r with hw
  show z = ((Tw.fm u μ).lam j τ).w r - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ)
  rw [← hw]
  generalize hn : j * (D.R.t + 1) = n
  have h2 : (2 * (w - z) : ℚ) = (n : ℚ) := by
    rw [← hn]; push_cast; rw [h]; ring
  have h3 : 2 * (w - z) = (n : ℤ) := by exact_mod_cast h2
  omega

theorem natW_add_shift {N : ℕ} (l : DomWeight N) (c : ℤ) (r : Fin N) :
    ((l.natW r : ℕ) : ℤ) + (shW l c).detShift = (shW l c).w r := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) r.2
  have hle : l.w ⟨N - 1, by omega⟩ ≤ l.w r := l.anti (show r ≤ ⟨N - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
  simp only [DomWeight.natW, DomWeight.detShift, shW, dif_pos hN]
  rw [Int.toNat_of_nonneg (by omega)]
  ring

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

theorem formsSharpAt_of_valTied (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    {T : ℕ} {bad : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F))}
    {eY : (D.chTw u μ).Y j ≃ Fr D j hj.le} {okW : D.what₂.places.Pl → Prop} {Ch : Type} {chOf : (D.chTw u μ).cls j → Ch}
    {lat : (D.chTw u μ).cls j → Submodule (NumberField.RingOfIntegers D.host.E) (Fin (D.R.N j) → D.host.E)}
    {K : ∀ β : Ch, LevelChart D T bad j hj.le (fun c : {c // chOf c = β} => (D.chTw u μ).stab j c.1) (fun c => lat c.1)}
    (hV : ValuationCompatibleChart (ex.tw.fm u μ) eY okW chOf K) (crd : GL (Fin (D.R.N j)) D.host.E)
    (hfrm : ∀ y τ, (t.O u μ).frm j y τ = atInf (embT D) crd.1 τ * (eY y).1 τ) :
    ∀ x, ∃ Q, SharpQ t ex.tw u μ j x Q := by
  intro x
  have hx := (hV.rat ((ex.tw.fm u μ).emb j x)).1 ⟨x, rfl⟩
  choose P hP hE using hx.2
  have hB : ∀ τ, (atInf (embT D) crd.1 τ).det ≠ 0 := by
    intro τ
    show ((crd : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ)).det ≠ 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (Matrix.isUnits_det_units crd).ne_zero
  have hg : ∀ y τ, ((eY y).1 τ).det ≠ 0 := fun y τ => ((eY y).2 τ).ne_zero
  have key : ∀ c, IsVLam ((t.O u μ).frm j) (fun τ r => (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ)
      ((ex.tw.fm u μ).emb j x c) := by
    intro c
    have h1 := isVLam_of_wtPol ((t.O u μ).frm j) (fun y => (eY y).1) (fun τ => atInf (embT D) crd.1 τ) hB hg hfrm
      (fun τ r => ((ex.tw.fm u μ).lam j τ).natW r) (shiftOf (lamTG (ex.tw.fm u μ) j)) (P c)
      (ratSpan_le_wtPol D _ (P c) (hP c))
    have hw : (fun τ r => (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ) =
        (fun τ r => ((((ex.tw.fm u μ).lam j τ).natW r : ℕ) : ℤ) + shiftOf (lamTG (ex.tw.fm u μ) j) τ) := by
      funext τ r
      rw [nuT_sub_sSharp D ex.tw u μ j hj τ r]
      exact (natW_add_shift _ _ r).symm
    have hf : (ex.tw.fm u μ).emb j x c = fun y => (∏ τ, ((eY y).1 τ).det ^ shiftOf (lamTG (ex.tw.fm u μ) j) τ) *
        MvPolynomial.eval (fun k : D.what₂.Tau × Fin (D.R.N j) × Fin (D.R.N j) => (eY y).1 k.1 k.2.1 k.2.2) (P c) := by
      funext y
      rw [hE c y]
      simp [fnOf]
    rw [hw, hf]
    exact h1
  have := fun c => forms_sharp_description Formalism.L2.KerInert.SharpPolyP.sharp_polynomial_frames D u (D.chTw u μ) (t.O u μ) j hj.le
    (nuT D u j) _ (key c)
  choose Q hQ hQE using this
  exact ⟨Q, hQ, hQE⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem formsSharpAt_of_pins (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : GlobalTheory.TwU.ChainCharts D u μ)
    (A : GlobalTheory.TwU.AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (hP : GlobalTheory.TwU.AdPins A dtU)
    (okW : ℕ → D.what₂.places.Pl → Prop)
    (hV : ∀ j (hj : j < D.R.m), ValuationCompatibleChart (ex.tw.fm u μ) (St j hj.le).eY (okW j) (St j hj.le).chOf (St j hj.le).K) :
    ∀ j, j < D.R.m → ∀ x, ∃ Q, SharpQ t ex.tw u μ j x Q :=
  fun j hj => formsSharpAt_of_valTied t u μ j hj (hV j hj) (A.crd j hj.le) (hP.frm j hj.le)

end GlobalTheory.FormsSharpTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawTopLevelStabilizer
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.StabTopLaw

set_option maxHeartbeats 4000000 in

theorem xiTop_stab_law : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → 2 * cst.M ≤ twTopDepth R → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) (a : FrmG (twLt Ch (m2 + 1 + 1)) (twTt (R := R) sel mu (m2 + 1 + 1))), Y ∈ ybSet sel mu cst p.deco.1.N → a • p' = p' → ∀ x, XiTop Ch sel mu cst (m2 + 1) p Y p' (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst (m2 + 1) P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((twLt Ch (m2 + 1 + 1)).chr a.2.1 * (twTt (R := R) sel mu (m2 + 1 + 1)).chr a.2.2 : X.Kˣ) : X.K) * XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hgS hTS hL hCh hsh hA hb hMd u p Y p' a hY hfix x
  have hm : R.m = m2 + 2 := hL.hm
  have hc : cst.Ok := hL.cst_ok
  have hn : TopNum R (m2 + 1) := topNum_of hm
  have hS : QSep Pr sel mu := qSep_of sel mu hPr hsel hgS
  have hU : QUnif sel mu := qUnif_of sel mu hX hPr hsel
  have hLaw := topLawG_sym Ch sel mu cst control_phi_law hX hPr hm hsh
  have hRow := lastRow_colLevSym Ch hm
  choose κ' hκ' hκr' hκQ' using fun w : rowSG Pr sel mu =>
    frsF_smulQ sel mu u p' (twLt Ch (m2 + 1 + 1)) (twTt (R := R) sel mu (m2 + 1 + 1)) a w
  rw [hfix] at hκ'
  have e0 : phiT X.K p.deco.1 p'.deco.1 (a.1.1.toLinearMap ∘ₗ x) = phiT X.K p.deco.1 p'.deco.1 x := by
    have h := phiT_smul X.K p.deco p'.deco 1 1 a.1 (a.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) x
    have hd : (a • p').deco = (a.1, (a.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs)) • p'.deco := rfl
    rw [← hd, hfix, ← Prod.one_eq_mk, one_smul] at h
    exact h

  rw [XiTop_eq, XiTop_eq, e0]

  have hsym : ∀ w z, (frsF sel mu p' w).symm (a.1.1 z) = (κ' w).1.symm ((frsF sel mu p' w).symm z) := by
    intro w z
    have h := hκ' w
    generalize frsF sel mu p' w = F' at h ⊢
    rw [LinearEquiv.symm_apply_eq]
    calc a.1.1 z = (a.1.1 * F' * (κ' w).1) ((κ' w).1.symm (F'.symm z)) := by
          simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
      _ = F' ((κ' w).1.symm (F'.symm z)) := by rw [← h]
  have hF : ∀ w, inFr (frsF sel mu p w) (frsF sel mu p' w) (a.1.1.toLinearMap ∘ₗ x) =
      (κ' w).1.symm.toLinearMap ∘ₗ inFr (frsF sel mu p w) (frsF sel mu p' w) x := by
    intro w
    apply LinearMap.ext
    intro v
    simp only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact hsym w _

  have hdet : ∀ w, ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = ((LinearEquiv.det ((κ' w)⁻¹).1 : X.Eˣ) : X.E) := by
    intro w
    have hd := congrArg (fun f => ((LinearEquiv.det f : X.Eˣ) : X.E)) (hκ' w)
    simp only [map_mul, Units.val_mul] at hd
    have hdF : ((LinearEquiv.det (frsF sel mu p' w) : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
    have hdK : ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
    have hAK : ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) * ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E) = 1 := by
      have h2 : ((LinearEquiv.det (frsF sel mu p' w) : X.Eˣ) : X.E) *
          (((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) * ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E)) =
          ((LinearEquiv.det (frsF sel mu p' w) : X.Eˣ) : X.E) * 1 := by
        rw [mul_one]
        conv_rhs => rw [hd]
        ring
      exact mul_left_cancel₀ hdF h2
    have e1 : ((LinearEquiv.det ((κ' w)⁻¹).1 : X.Eˣ) : X.E) = ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E)⁻¹ := by
      show ((LinearEquiv.det ((κ' w).1)⁻¹ : X.Eˣ) : X.E) = _
      rw [map_inv, Units.val_inv_eq_inv_val]
    rw [e1]
    exact eq_inv_of_mul_eq_one_left hAK

  have hmu : ∀ w, muAt Ch sel mu cst (m2 + 1) w ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) =
      rhoT Ch sel mu (m2 + 1) w ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E) := by
    intro w
    rw [hdet w]
    have hun : IsUnit (redP w.1 ((LinearEquiv.det ((κ' w)⁻¹).1 : X.Eˣ) : X.E)) :=
      isUnit_reduction_of_integralAt_inv (intAt_det _ ((κ' w)⁻¹).2) (intAt_det_inv _ ((κ' w)⁻¹).2) (Units.ne_zero _)
    have e2 := GlobalTheory.TopLaw.rhoT_inv (Ch := Ch) (sel := sel) (mu := mu) (m2 + 1) w (κ' w)⁻¹
    rw [inv_inv] at e2
    rw [e2]
    unfold muAt rhoS
    rw [GlobalTheory.LastSteps.locChar_unit _ _ hun]

  have hchr : (((twLt Ch (m2 + 1 + 1)).chr a.2.1 * (twTt (R := R) sel mu (m2 + 1 + 1)).chr a.2.2 : X.Kˣ) : X.K) =
      ∏ w : rowSG Pr sel mu,
        (if hw : w.1 ∈ Pr.vGs then
          (((twLt Ch (m2 + 1 + 1) ⟨w.1, hw⟩).lam ⟨(a.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hw⟩, a.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)
        else
          (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam
              ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩,
                a.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)) := by
    rw [prod_uSG_dite hS
      (fun w => (((twLt Ch (m2 + 1 + 1) w).lam ⟨(a.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) w, a.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K))
      (fun Q => (((twTt (R := R) sel mu (m2 + 1 + 1) Q).lam ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) Q,
        a.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K))]
    rw [Units.val_mul, levFam_chr_apply_coe]
    congr 1
    exact piChar_apply_coe' _ _ a.2.2

  have hper : ∀ w : rowSG Pr sel mu,
      muAt Ch sel mu cst (m2 + 1) w ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) *
        topDat Ch sel mu cst (m2 + 1) w (inFr (frsF sel mu p w) (frsF sel mu p' w) (a.1.1.toLinearMap ∘ₗ x)) ((frsF sel mu p w).symm (repY Y)) =
      (if hw : w.1 ∈ Pr.vGs then
          (((twLt Ch (m2 + 1 + 1) ⟨w.1, hw⟩).lam ⟨(a.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hw⟩, a.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)
        else
          (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam
              ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩,
                a.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)) *
        topDat Ch sel mu cst (m2 + 1) w (inFr (frsF sel mu p w) (frsF sel mu p' w) x) ((frsF sel mu p w).symm (repY Y)) := by
    intro w
    rw [hmu w, hF w]
    have hFst : ∀ z, z ∈ localization₂ w.1.asIdeal p.deco.1.N → (frsF sel mu p w).symm z ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      intro z hz
      apply (frsF_isFr sel mu p w _).1
      rw [LinearEquiv.apply_symm_apply]
      exact hz
    by_cases hw : w.1 ∈ Pr.vGs
    · rw [dif_pos hw]
      obtain ⟨hne, -, hqm⟩ := ybSet_props2 sel mu cst hY w hw
      have hr0 := representative_mem hne
      have hq : ((qOf w.1 : ℕ) : X.E) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
        rw [← LinearEquiv.map_smul]
        exact hFst _ (hqm _ hr0)
      have key := topDat_law hc hn hLaw hRow w hw 1 ⟨(a.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hw⟩, a.2.1.2 _ (Set.mem_univ _)⟩
        1 (κ' w) (fun z _ => by simp) (hκr' w hw) (ciQ_notMem_sq hX hPr hw)
        (inFr (frsF sel mu p w) (frsF sel mu p' w) x) ((frsF sel mu p w).symm (repY Y)) ((frsF sel mu p w).symm (repY Y)) (by simp) hq
      have h1 : rhoS Ch sel mu (m2 + 1) w ((LinearEquiv.det ((1 : ↥(GLint X.E (R.N (m2 + 1)) w.1)) : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) : X.Eˣ) : X.E) = 1 := by
        simp [rhoS, LocE.unitV, redP_one]
      rw [h1, one_mul, map_one, inv_one, Units.val_one, mul_one] at key
      exact key
    · rw [dif_neg hw]
      obtain ⟨hne, hqm⟩ := coupling_index_scaled_mem_local sel mu cst hY w hw
      have hr0 := representative_mem hne
      have hq : ((qOf w.1 : X.E) ^ cst.M) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
        rw [← LinearEquiv.map_smul]
        exact hFst _ (hqm _ hr0)
      have hQw := (Finset.mem_union.mp w.2).resolve_left hw
      have hc' : (κ' w)⁻¹ ∈ (twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, hQw⟩).H := by
        rw [hκQ' w hw, inv_inv]
        exact a.2.2.2 _ (Set.mem_univ _)
      have key := GlobalTheory.T.twTt_k1Depth_twice_m Ch sel mu cst w hw (κ' w) hc' (inFr (frsF sel mu p w) (frsF sel mu p' w) x) ((frsF sel mu p w).symm (repY Y))
        hm hc (hU w.1 hQw) (hL.depthQ w hw) hMd hq
      have e4 : (⟨(κ' w)⁻¹, hc'⟩ : ↥(twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, hQw⟩).H) =
          ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, hQw⟩, a.2.2.2 _ (Set.mem_univ _)⟩ :=
        Subtype.ext (by show (κ' w)⁻¹ = _; rw [hκQ' w hw, inv_inv])
      rw [e4] at key
      exact key
  rw [hchr]
  have := prod_mul_eq_of_forall_cross_mul_eq _ _ _ _ (phiT X.K p.deco.1 p'.deco.1 x) hper
  linear_combination this

end GlobalTheory.StabTopLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationInverseHalfDifferentEqOneUnramified
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory.TwV.Xc

theorem not_dvd_absDifferent_of_not_mem_sq {E : Type} [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (P : HeightOneSpectrum (𝓞 E)) (h1 : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal)
    (h2 : ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) : ¬ P.asIdeal ∣ differentIdeal ℤ (𝓞 E) := by
  have hP : P.asIdeal.IsMaximal := P.isMaximal
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime _
  have : Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod p).toEquiv.symm
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) =
      Ideal.span {((p : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P.asIdeal := by
    rw [hmap, Ideal.span_singleton_le_iff_mem]
    exact h1
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hle
  have hcop : IsCoprime P.asIdeal Q := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have heq := hP.eq_of_le hne le_sup_left
    have hQP : Q ≤ P.asIdeal := heq ▸ le_sup_right
    apply h2
    have hmem : ((p : ℕ) : 𝓞 E) ∈
        Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) := by
      rw [hmap]; exact Ideal.subset_span rfl
    rw [hQ] at hmem
    rw [pow_two]
    exact Ideal.mul_mono_right hQP hmem
  exact not_dvd_differentIdeal_of_isCoprime ℤ P.asIdeal Q hcop hQ.symm

theorem inverseHalfDifferent_local_trivial_at_prime_norm : ∀ (D : D7) (p : ℕ), p.Prime → ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ((p : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  intro D p hp P h1 h2
  have hnd := not_dvd_absDifferent_of_not_mem_sq p hp P h1 h2
  have ht : differentIdeal ℤ (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) *
      (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) :=
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)
  have hspec : D.host.𝔟 ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) := ⟨_, D.host.𝔟_spec.1⟩
  have hn : ¬ D.host.𝔟 ≤ P.asIdeal := fun h => hnd (by
    rw [ht]
    exact ((Ideal.dvd_iff_le.2 h).trans hspec).mul_right _)
  obtain ⟨t, htb, htP⟩ := SetLike.not_le_iff_exists.1 hn
  have hb : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => hn (h ▸ bot_le)
  ext x
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨t * s, fun h => (P.isPrime.mem_or_mem h).elim htP hs, ?_⟩
    obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff hb).1 hx _ (FractionalIdeal.mem_coeIdeal_of_mem _ htb))
    rw [Submodule.mem_one]
    refine ⟨u, ?_⟩
    rw [hu, mul_smul, Algebra.smul_def t, mul_comm]
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    obtain ⟨u, hu⟩ := Submodule.mem_one.1 hx
    refine (FractionalIdeal.mem_inv_iff hb).2 fun y hy => ?_
    obtain ⟨z, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨u * z, by rw [map_mul, hu]⟩

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTypeCharacterBlockSumOneEqStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTypeCharacter_blockSumOne_eq : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N n : ℕ} (hN : N = n + 1) (r : ℕ), r ≤ n → ∀ j : Sp E n ≃ₗ[E] Sp E n, LocE.lamQB ξ r N (sumE hN j 1).toLinearMap = LocE.lamQB ξ r n j.toLinearMap := by
  first | exact @GlobalTheory.SumRowType.lamQB_sumE | exact GlobalTheory.SumRowType.lamQB_sumE | (intros; apply GlobalTheory.SumRowType.lamQB_sumE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecompositionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_k1_block_decomposition : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b → ∀ g : GLint E N P, g ∈ twK1H P N r (c + 1) → ∃ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b ∧ (extI hN P j)⁻¹ * g ∈ prinCong N P (c + 1) := by
  first | exact @GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 | exact GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 | (intros; apply GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 <;> assumption)
end

