import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0298
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0299
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0271
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0257
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0286
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0295
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0294
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0283
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0296
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentsCosetSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaMovedCosetIndicatorVacuumShape
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0089
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0090
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0127
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0139
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFrames_mul_adele_at_badPrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), x₁.1 = x.1 * κ →
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (dep : SB t μ → ℕ) (g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)),
      1 ≤ dep P → dep P ≤ (t.cst μ).D P → g ∈ GLint t.X.E (D.R.N j) P.1 →
      InFrame t.seam (A.fb j hj β) dep P κ g →
      (frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) ∈ GLint t.X.E (D.R.N j) P.1 ∧
      ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ dep P)⁻¹ •
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) w - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  first | exact @GlobalTheory.FrameMove.frames_mul | exact GlobalTheory.FrameMove.frames_mul | (intros; apply GlobalTheory.FrameMove.frames_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsRebasedOneOffLevelPrimeKilled
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.TwU.AtTrue.charts_funKilled_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K0 : Fam I l Z u a i hi bad chOf), I.ReadsK l Z u a i hi chOf K0 → (∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K0 β).lev.chi κ ^ n = 1) → ∃ Kc : Fam I l Z u a i hi bad chOf, ReadsOne I l Z u a i hi chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K0 hK hfin
  obtain ⟨K', hK', hprop⟩ := TC.charts_funKilled I hI hP l Z u a i hi bad Ch chOf K0 hK
  obtain ⟨k, hk⟩ := GlobalTheory.T.chartsReadingStep_moveBasePoints_one_offLevelPrime I hI hP l Z u a i hi bad Ch chOf K' hK'
  refine ⟨fun β => moveChart (K' β) (k β), hk, fun β => ⟨(hprop β).1, ?_⟩⟩
  obtain ⟨hF, -, -, hU, hchi, -, -⟩ := hprop β
  obtain ⟨n, hn, hn'⟩ := hfin β
  refine ⟨n, hn, fun κ => ?_⟩
  have hm : (k β).1 * κ.1 * (k β).1⁻¹ ∈ (K0 β).lev.U := hU ▸ κ.2
  show ((K' β).lev.chi ⟨(k β).1 * κ.1 * (k β).1⁻¹, κ.2⟩) ^ n = 1
  have e := hchi ⟨(k β).1 * κ.1 * (k β).1⁻¹, κ.2⟩ ⟨_, hm⟩ rfl
  exact e.symm ▸ hn' _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassSumTermLawStabiliserTarget
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

theorem gmap_of_fix {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {Λ : LevFam X.E X.K n SG}
    {Θ : LevQFam X.E X.K n Q} (a : FrmG Λ Θ) (p : DecoF X.E n ST SG Q) (h : a • p = p) :
    gmap a.1.1 p.deco.1.N = p.deco.1.N :=
  congrArg (fun q : DecoF X.E n ST SG Q => q.deco.1.N) h

theorem mulLat_mul_le {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (a b : ℕ)
    (M : Submodule (𝓞 E) H) : mulLat (a * b) M ≤ mulLat b M := by
  rintro z ⟨w, hw, rfl⟩
  refine ⟨((a : 𝓞 E)) • w, M.smul_mem _ hw, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, Nat.cast_mul, mul_comm]

theorem term_law : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → ∀ u μ (G : StabDat (D.chTw u μ)), StabPin t u μ G → ∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw (t.O u μ) i c c' g := by
  intro D L hT Gi Gl K Y cX ex t hC u μ G hG i hi c c' g hg
  have hok := t.idx_ok μ
  have hm := hok.hm
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  obtain ⟨pt, ix, yb, pT, hN, hyb, hE, hC1, hTop, hGi, hGm, hGT⟩ := hG
  have dat := GlobalTheory.T.pairKernelLaw_of_finiteDatumLaw D L hT Gi Gl K Y cX ex t hC.fields hC.sel hC.bad.1 hC.bad.2.1 hC.bad.2.2.1 hC.bad.2.2.2 hC.chars u μ i hi c c'
  have fin : ∀ (f : HomE t.X.E (D.R.N i) (D.R.N (i + 1)) → t.X.K) (N : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)))
      (N' : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N (i + 1)))) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K),
      (t.rd u μ).N i c = N → (t.rd u μ).N (i + 1) c' = N' → (∀ x, (t.rd u μ).Xi i c c' x = t.seam.σ₀ (f x)) →
      gmap γ.1 N' = N' →
      (∀ x z, z ∈ mulLat (cBof t.sel (t.tup μ) (t.cst μ) (t.word u)) (homAt (Sall t.sel (t.tup μ) (t.word u)) N N') → f (x + z) = f x) →
      (∀ x, f (γ.1.toLinearMap ∘ₗ x) * ∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E) = k * f x) →
      TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
    intro f N N' γ k hN1 hN2 hf hγ hinv hlaw
    subst hN1 hN2
    refine dat γ k hγ (fun x z hz => ?_) fun x => ?_
    · rw [hlev, hSS] at hz
      rw [hf, hf, hinv x z (mulLat_mul_le _ _ _ hz)]
    · rw [hf, hf, ← map_mul, ← map_mul, hlaw]
  rcases lt_trichotomy i t.m2 with hlt | heq | hgt
  · rw [hGi (i + 1) (by omega) (by omega) c'] at hg
    obtain ⟨a, hfix, -, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN i (by omega) c) (hN (i + 1) (by omega) c') (hE i hlt c c') (gmap_of_fix a _ hfix)
      (fun x z hz => xiEntry_invA t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.pr_ok hok i hlt _ _ _ _ x z hz)
      (GlobalTheory.FiLaw.xiEntry_stab t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (t.word u) i hlt _ _ _ _ a hfix)
  · subst heq
    obtain ⟨b, -⟩ := hok.last_uniq
    rw [hGm b c'] at hg
    obtain ⟨a, hfix, hY, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN _ (Nat.le_succ _) c) (hN _ le_rfl c') (hC1 c c') (gmap_of_fix a _ hfix)
      (fun x z hz => xiCpl1_invA t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.pr_ok hok _ _ _ _ x z hz)
      (GlobalTheory.StabLaw.xiCpl1_stab t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob _ hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (t.word u) _ b _ _ _ a (hyb c') hfix hY)
  · have hi' : i = t.m2 + 1 := by omega
    subst hi'
    rw [hGT c'] at hg
    obtain ⟨a, hfix, -, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN _ le_rfl c) (hTop.1 c') (hTop.2 c c') (gmap_of_fix a _ hfix)
      (fun x z hz => GlobalTheory.T.lastStep_datum_invariant_cB_hom_twist_primes t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok
        (t.word u) _ _ _ x z (hyb c) hz)
      (GlobalTheory.T.lastStepDatum_law_topLevelStabilizer t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (hC.deep μ).2 (t.word u) _ _ _ a (hyb c) hfix)

end GlobalTheory.KerJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldConditionOfStandardKernelCompari
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Pdv

private theorem nuT_cast_eq_nuW {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : B.fields.Tau) (r : Fin (B.R.N i)) :
    ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) = (B.wts.nuW u (i + 1) τ).w r := by

  have hq : ((B.wts.nuW u (i + 1) τ).w r : ℚ) = Examples₂.wtN (B.hcW u τ) r.1 + wG B.R ((B.hcW u τ).e ⟨i, hi⟩) (i + 1) := by
    rw [Formalism.L2.Col.Wts.nuW_eq _ u hi τ r]
    rw [show B.wts.lamN u i τ = Examples₂.lamOf (B.hcW u τ) i from rfl, Formalism.L2.Col.lamOf_wtN _ hi.le r]

  have hrow : DV.nuRow (I.rec7 l Z) u (i + 1) τ r = (((B.wts.nuW u (i + 1) τ).w r : ℤ) : ℝ) := by
    rw [GlobalTheory.ColPeriod.nuRow_succ_eq_wt (I.rec7 l Z) u i hi τ r r.2]
    have h := congrArg (fun x : ℚ => (x : ℝ)) hq.symm
    simp only [Rat.cast_intCast] at h
    exact h

  have hnn : 0 ≤ (B.wts.nuW u (i + 1) τ).w r := by
    have h1 := Formalism.L2.Ker.natW_cast (B.wts.nuW u (i + 1) τ) r
    have h2 := GlobalTheory.MoveCompare.nuW_detShift_nonneg B.wts u hi τ
    omega
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
  show ((⌊DV.nuRow (I.rec7 l Z) u (i + 1) τ r⌋₊ : ℕ) : ℤ) = _
  rw [hrow, hn, Int.cast_natCast, Nat.floor_natCast]

private theorem monoDeg_eq_nuDeg_of_degAt_eq_sum_nuT {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : B.fields.Tau)
    (m : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ)
    (hm : degAt m τ = ∑ r, nuT (I.rec7 l Z) u i τ r) : (monoDeg m τ : ℤ) = nuDeg B u i τ := by
  have h3 : ((∑ r, nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) = nuDeg B u i τ := by
    push_cast
    exact Finset.sum_congr rfl fun r _ => nuT_cast_eq_nuW I l Z u hi τ r
  exact (congrArg (Nat.cast : ℕ → ℤ) hm).trans h3

set_option maxHeartbeats 800000 in

theorem rk_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → t.RK := by
  intro B X I hok hpins l Z L hT Gi Gl K Y cX ex t hJ hS u μ hμ i hi c c' m hm
  rw [hS.O.dgen u μ, hS.O.Th u μ i c c']
  exact GlobalTheory.T.trueKernelJets_mul_detCharacters_mem_coefficientField I hok hpins l Z hJ u μ i hi c c' m fun τ => monoDeg_eq_nuDeg_of_degAt_eq_sum_nuT I l Z u hi τ m (hm τ)

set_option maxHeartbeats 800000 in

theorem rk_of_stdTie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKerTie l Z t → t.RK := by
  intro B X I hok hpins l Z L hT Gi Gl K Y cX ex t hJ hS u μ hμ i hi c c' m hm
  rw [hS.O.dgen u μ, hS.O.Th u μ i c c']
  exact GlobalTheory.T.trueKernelJets_mul_detCharacters_mem_coefficientField I hok hpins l Z hJ u μ i hi c c' m fun τ => monoDeg_eq_nuDeg_of_degAt_eq_sum_nuT I l Z u hi τ m (hm τ)

end GlobalTheory.Pdv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConsecutiveClassesKernelEqKernelFunctionTranspor
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem th_eq_kerTh : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', (t.rd u μ).Th t.seam t.amb i c c' = kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie Xi muT hL i hi c c'
  obtain ⟨hδ, -, hV, -⟩ := GlobalTheory.T.kernelEntry_period_ne_zero_and_lattice_laws t
  obtain ⟨hl, hS⟩ := GlobalTheory.T.finiteDatum_level_pos_badPrimes_no_conjugate_pair A dtU a hP hTie
  exact GlobalTheory.T.columnFieldKernel_pushforward_eq_hostKernelFunction t.seam t.seam_ok t.B t.χ _ (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')
    ((t.rd u μ).Xi i c c') t.cc_ok t.δ_ok hδ hV hl hS (GlobalTheory.T.transportedLattices_two_classes_admissible t u μ i (i + 1) c c')
    (GlobalTheory.T.finiteDatum_pair_classes_has_level A dtU a hP hTie Xi muT hL i hi c c')

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepDatumRationalUnitaryEquivariantStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstCoupledStepDatum_rationalUnitary_equivariant : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), i = t.m2 → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG t.X.E (D.R.N (i + 1)) t.Pr.vGs × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  first | exact @GlobalTheory.CplRat.xiPt_cpl_smul | exact GlobalTheory.CplRat.xiPt_cpl_smul | (intros; apply GlobalTheory.CplRat.xiPt_cpl_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetLossOfFamilyFacts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.LiftTypePrime.Jets (intAt_mul intAt_sum intAt_of_isIntegral isIntegral_exp)
open GlobalTheory.MomT.CosetSum

noncomputable section

namespace GlobalTheory.DatumJets

section Int

variable {p : ℕ} [Fact p.Prime] {lam : TaylorLogMetric.Qbar →+* ℂ_[p]}

end Int

section Idx

variable {X : Fields} {a b : ℕ}

end Idx

theorem map_jetSum {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) {cA c : ℕ}
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (hcA0 : 0 < cA) (hc0 : 0 < c) (Ξ : HomE X.E a b → X.K) {e : DVar X.Tau a b →₀ ℕ} (he : e ∈ RatIdx A S cA c N N' Ξ) :
    A.σ₀ (jetSum A S cA c N N' Ξ e) = (A.chiF a b N N')⁻¹ *
      latSum (divLat cA (homAt S N N')) (mulLat c (homAt S N N')) fun x => A.σ₀ (Ξ x) * jetC A.cD (A.thInd S N N' c x) e := by
  have := GlobalTheory.MomT.finite_quot_divLat_mulLat_homAt X.E a b S N N' cA c hN.1 hN'.1 hcA0 hc0
  have := Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)
  rw [jetSum, latSum, latSum, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  generalize Function.surjInv (Submodule.Quotient.mk_surjective _) z = x
  by_cases h0 : Ξ x = 0
  · simp [h0]
  · have h := he x x.2 h0
    rw [map_mul, Amb.jetK, desc, dif_pos h, h.choose_spec]
    ring

end GlobalTheory.DatumJets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelStepCharacterEqOneIntegralUnitaryStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelStepCharacter_eq_one_integralUnitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E → (∀ v, UnderSB t μ v → Formalism.UG.prV (E := D.host.E) v ((Matrix.GeneralLinearGroup.det y.1 : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) = 1) → (t.O u μ).mt (i + 1) (dtU y) = 1) := by
  first | exact @GlobalTheory.TieUnr.mt_eq_one_of_intUnit | exact GlobalTheory.TieUnr.mt_eq_one_of_intUnit | (intros; apply GlobalTheory.TieUnr.mt_eq_one_of_intUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorLevelValuesTypePrime
section
noncomputable section

namespace GlobalTheory.TwTop

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem locAt_vG : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP g z g' z' hC hF hT hF' Z
  have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
  have hDt : topDep t.sel (t.tup μ) (t.cst μ) P = 1 := by unfold topDep; simp [hP]
  obtain ⟨Gg, rfl, hsrc⟩ := GlobalTheory.T.last_step_local_factor_source_law_coupled_level hPin.fields.ok t.pr_ok hPin.sel (t.idx_ok μ) _ P hP g z hC.1
  obtain ⟨Gt, rfl, htgt⟩ := GlobalTheory.T.last_step_local_factor_target_law_top_level hPin.fields.ok t.pr_ok hPin.sel (t.idx_ok μ) P hP g' z' hT
  obtain ⟨k, hk, hkr⟩ := GlobalTheory.T.type_prime_frames_right_translate_differ_integral_GL A dtU a hPin hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ κ hx p p₁ hp hp₁ P hP (t.cst μ).D hD Gg hF
  obtain ⟨k', hk', hkr'⟩ := GlobalTheory.T.type_prime_frames_right_translate_differ_integral_GL A dtU a hPin hTie (t.m2 + 1 + 1) hi β' x' x₁' κ' hx' p' p₁' hp' hp₁' P hP _ hDt Gt hF'
  obtain ⟨i0, i1, hdiff⟩ := GlobalTheory.T.coupling_cosets_right_translate_in_frames_type_prime A dtU a hPin hTie (Nat.le_of_succ_le hi) β p p₁ P hP Gg k z hC hkr hk
  have e1 : inFr (frsF t.sel (t.tup μ) p₁ P) (frsG t.sel (t.tup μ) p₁' P) Z =
      (k'⁻¹).1.toLinearMap ∘ₗ (inFr (frsF t.sel (t.tup μ) p P) (frsG t.sel (t.tup μ) p' P) Z ∘ₗ k.1.toLinearMap) := by
    rw [frsG_eq, frsG_eq, hk, hk']
    rfl
  have hs := hsrc k hkr (inFr (frsF t.sel (t.tup μ) p P) (frsG t.sel (t.tup μ) p' P) Z) _ _ i0 hdiff
  have ht := htgt k' hkr' (inFr (frsF t.sel (t.tup μ) p P) (frsG t.sel (t.tup μ) p' P) Z ∘ₗ k.1.toLinearMap) _ i1
  unfold topF
  rw [e1]
  linear_combination rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det Gg.1 : t.X.Eˣ) : t.X.E) * ht + hs

end GlobalTheory.TwTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelMovedPointFramesMatrixSteps
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.MatFrames

set_option maxHeartbeats 1000000 in

theorem frames_mat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j < D.R.m), j ≤ t.m2 → ∀ (β : (St j hj.le).Ch) (x x₁ : UA D j hj.le) (κ : ((St j hj.le).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj.le β x p → IsPtAd A a j hj.le β x₁ p₁ →
    ∃ (k : GLQ t.X.E (D.R.N j) (SB t μ)) (c : SB t μ → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * ((k P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P (k P) (c P)) ∧
      ((((St j hj.le).K β).lev.chi κ : ℂˣ) : ℂ) = t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) ∧
      ∀ P : SB t μ, IntAtA (F := D.host.F) (seamP t.seam P.1)
        (iA D.host.F D.host.E ((qOf (seamP t.seam P.1) : D.host.E))⁻¹ *
          ((((Matrix.GeneralLinearGroup.det κ.1)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
            iA D.host.F D.host.E (t.seam.iE ((LinearEquiv.det ((k P)⁻¹).1 : t.X.Eˣ) : t.X.E)) - 1))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie j hj hjm β x x₁ κ hx p p₁ hp hp₁
  classical
  have hok := t.idx_ok μ
  obtain ⟨hLe, -, hChi⟩ := hTie.levMid j hj hjm β
  have hLoc : ∀ P : SB t μ, ∃ g z, A.midRel j hj β P g z ∧ InFrame t.seam (A.fb j hj.le β) (t.cst μ).D P κ.1 g := by
    intro P
    have hv : IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
      unfold IsOver
      rw [HeightOneSpectrum.under_asIdeal]
    have hU := (((St j hj.le).K β).lev.U_eq κ.1).1 κ.2
    exact hLe P _ hv κ.1 hU.1 (hU.2 _)
  choose g z hgz using hLoc
  have hpr : ∀ P, g P ∈ prCat (Pr := t.Pr) (t.cst μ).sharp j P.1 ((t.idx μ).h j (A.ib j hj β) P) := fun P =>
    (exists_midLev_iff t.Ch t.sel (t.tup μ) (t.cst μ) j P _ (g P)).1 ⟨z P, (hgz P).1⟩
  let gg : ∀ P : SB t μ, GLint t.X.E (D.R.N j) P.1 := fun P => ⟨g P, hok.int j _ P (hpr P)⟩
  have hB := fun P => GlobalTheory.T.frames_of_right_translate_point_principal_congruence A a j hj.le β x x₁ κ.1 hx p p₁ hp hp₁ P (gg P) (hgz P).2
  choose C hCp hCc hCf using hB
  have hD : ∀ P : SB t μ, 1 ≤ (t.cst μ).D P := fun P => hok.cst_ok.D_pos P
  have hc : ∀ P : SB t μ, ∃ c : t.X.Kˣ, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P
      (gg P * C P)⁻¹ c ∧ (c : t.X.K) = (z P)⁻¹ := by
    intro P
    obtain ⟨r, hr, hrx, hz⟩ := (hgz P).1
    by_cases hP : P.1 ∈ t.Pr.vGs
    · have hH : redGL _ P.1 (gg P) ∈ ((t.idx μ).levG j (A.ib j hj β) ⟨P.1, hP⟩).H :=
        (hok.grpG j _ ⟨P.1, hP⟩ _).2 ⟨g P, hpr P, fun y hy => redV_redGL (gg P) hy⟩
      have hlam := hok.chrG j _ ⟨P.1, hP⟩ ⟨_, hH⟩ (g P) r hr hrx (fun y hy => redV_redGL (gg P) hy)
      have hred : redGL _ P.1 (gg P * C P)⁻¹ = (redGL _ P.1 (gg P))⁻¹ := by
        rw [map_inv, map_mul, GlobalTheory.TopStep.redGL_of_prinCong (hD P) (hCp P), mul_one]
      refine ⟨(((t.idx μ).levG j (A.ib j hj β) ⟨P.1, hP⟩).lam ⟨_, hH⟩)⁻¹, ⟨fun hP' => ⟨hred ▸ inv_mem hH, ?_⟩, fun _ hP' => absurd hP hP'⟩, ?_⟩
      · rw [← map_inv]
        congr 1
        exact Subtype.ext hred.symm
      · rw [Units.val_inv_eq_inv_val, hlam, hz]
    · have hQ : P.1 ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K) := (Finset.mem_union.mp P.2).resolve_left hP
      obtain ⟨r', hr', hr'x, hr'1⟩ := GlobalTheory.T.principal_congruence_subgroup_mem_level_twist_prime hPin.fields.ok t.pr_ok hok (j := j) hjm (A.ib j hj β) P hP (C P) (hCp P)
      have hgH : gg P ∈ ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H := by
        rw [hok.grpQ]
        exact Subgroup.mem_subgroupOf.2 (hpr P)
      have hCH : C P ∈ ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H := by
        rw [hok.grpQ]
        exact Subgroup.mem_subgroupOf.2 ⟨r', hr', hr'x⟩
      have hlg := hok.chrQ j _ ⟨P.1, hQ⟩ ⟨gg P, hgH⟩ r hr hrx
      have hlC := hok.chrQ j _ ⟨P.1, hQ⟩ ⟨C P, hCH⟩ r' hr' hr'x
      have hC1 : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).lam ⟨C P, hCH⟩ = 1 := Units.ext (hlC.trans hr'1)
      refine ⟨(((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).lam ⟨gg P, hgH⟩)⁻¹,
        ⟨fun hP' => absurd hP' hP, fun hQ' _ => ⟨inv_mem (mul_mem hgH hCH), ?_⟩⟩, ?_⟩
      · have e : (⟨(gg P * C P)⁻¹, inv_mem (mul_mem hgH hCH)⟩ : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H) =
            ((⟨gg P, hgH⟩ : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H) * ⟨C P, hCH⟩)⁻¹ := Subtype.ext (by simp)
        rw [e, map_inv, map_mul, hC1, mul_one]
      · rw [Units.val_inv_eq_inv_val, hlg, hz]
  choose c hcL hcz using hc
  refine ⟨fun P => (gg P * C P)⁻¹, c, fun P => ?_, hcL, ?_, fun P => ?_⟩
  · rw [inv_inv]
    exact hCf P
  · have h1 := hChi κ g z hgz
    have h2 : (((∏ P, c P : t.X.Kˣ)) : t.X.K) = (∏ P, z P)⁻¹ := by
      rw [Units.coe_prod, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun P _ => hcz P
    rw [h2, map_inv₀]
    exact eq_inv_of_mul_eq_one_left h1
  · rw [inv_inv]
    exact GlobalTheory.T.det_inv_mul_frame_reading_congruent_one_mod_norm t.seam (A.fb j hj.le β) (t.cst μ).D P (hD P) κ.1 (g P) (C P).1 (hgz P).2 (hCc P)

end GlobalTheory.MatFrames

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesLocalModelsOfOtherDivisionLatticesHeightsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuplesLocalModels_of_otherDivisionLatticesHeights : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), ModelsAt D O → ModelsAt (setDiv D N h) (O.tr N h) := by
  first | exact @GlobalTheory.Svd.modelsAt_tr | exact GlobalTheory.Svd.modelsAt_tr | (intros; apply GlobalTheory.Svd.modelsAt_tr <;> assumption)
end

