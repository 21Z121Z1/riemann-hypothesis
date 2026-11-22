import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanCw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0533
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0538
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0504
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0407
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0513
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0541
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFormsLiftBaseLevelExtensionSpan
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem goodForms_lift_bc : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        z'.R.toRealDat.WL z'.F.lv2 false j' = Submodule.span (w'.st Z').toD7.what₂.LL {x' | ∃ x ∈ z.R.toRealDat.WL z.F.lv2 false j, ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  intro p1 p2 p3 p4 p5 p6 p7
  have H := StepW.and (StepW.and (GlobalTheory.T.finiteGroupAction_coordinatewise_fieldEmbedding p1 p2 p3 p4 p5 p6 p7) (GlobalTheory.T.finiteGroupCharactersOnLiftForms_extendedData p1 p2 p3 p4 p5 p6 p7))
    (StepW.and (GlobalTheory.T.baseLevels_extendedData_correspond_fieldEmbedding p1 p2 p3 p4 p5 p6 p7) (GlobalTheory.T.goodIdempotent_coeffs_correspond_fieldEmbedding p1 p2 p3 p4 p5 p6 p7))
  refine StepW.trans H (StepW.of_all fun K B' f' T' w' _ _ hq => ?_)
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ
  have S1 := hq.1.1 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ
  have S2 := hq.1.2 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ
  have S3 := hq.2.1 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ
  have S4 := hq.2.2 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ
  obtain ⟨e, he⟩ := GlobalTheory.Mem.R3.GoodBC.gc_iso B B' hE.1 w.px w'.px hpx
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1
  have hn : z.R.nW j = z'.R.nW j' := (GlobalTheory.Mem.R3.GoodBC.nat_heq_app hm _ _ hEx.nW j j' hj).symm
  unfold RealDat.WL
  refine GlobalTheory.Mem.R3.GoodBC.wgood_bc_rel hn (z.R.toRealDat.FW j) (z'.R.toRealDat.FW j') φ e _ _ _ _ _ _
    (fun g x x' hx k k' hk => S1 g (e g) (he g) x x' hx k k' hk) (fun g => S2 g (e g) (he g))
    (fun g => (S3 g (e g) (he g)).1) (fun g hg hg' => ?_) (fun g => S4 g (e g) (he g))
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀,
    (S3 g (e g) (he g)).2 hg hg']

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MidLevMulBeforeLast
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi

theorem last_rep_one {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∃ b : (I.idx a).β (B.R.m - 1), ∀ P, (I.idx a).h (B.R.m - 1) b P = 1 := by
  have hL := hOk.idx_ok a
  have e : B.R.m - 1 = B.R.m - 2 + 1 := by have := hL.hm; omega
  rw [e]
  obtain ⟨b, -⟩ := hL.last_uniq
  exact ⟨b, hL.last_h b⟩

theorem prCat_last_le_GLint {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (P : SBof I a) :
    prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 ≤ Formalism.L2.Col.GLint B.fields.E (B.R.N (B.R.m - 1)) P.1 := by
  obtain ⟨b, hb⟩ := last_rep_one I hOk a
  have h := (hOk.idx_ok a).int (B.R.m - 1) b P
  rwa [hb P] at h

theorem inv_mul_rearrange {G : Type*} [Group G] (A B C D : G) : (A * B)⁻¹ * (C * D) = (B⁻¹ * D) * (D⁻¹ * (A⁻¹ * C) * D) := by
  group

theorem nearAt_prod_of_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ex ey : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (rg rg' : GL (Fin N) E)
    (hx : GlobalTheory.TwU.CongAt P n (ex⁻¹ * GlobalTheory.TwU.ratA F rg)) (hy : GlobalTheory.TwU.CongAt P n (ey⁻¹ * GlobalTheory.TwU.ratA F rg'))
    (hint : ∀ a b, IntAt P ((rg' : Matrix (Fin N) (Fin N) E) a b) ∧ IntAt P (((rg'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) a b)) :
    GlobalTheory.TwU.CongAt P n ((ex * ey)⁻¹ * GlobalTheory.TwU.ratA F (rg * rg')) := by
  rw [map_mul, inv_mul_rearrange]
  exact GlobalTheory.CplPt.congAt_mul _ hy (GlobalTheory.CplPt.congAt_conj _ hx hint)

theorem nearV_mul_pairs : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (P : SBof I a) (x y : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) (g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z z' : B.fields.K), GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P x g z → GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P y g' z' → GlobalTheory.Mem.Col2.QChi.NearV I l Z a v P (x * y) (g * g') := by
  intro B X I hOk l Z a v P x y g g' z z' hx hy
  have hg' : g' ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 :=
    (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g').1 ⟨z', hy.1⟩
  have hint := prCat_last_le_GLint I hOk a P hg'
  have hx2 := hx.2
  have hy2 := hy.2
  unfold NearV GlobalTheory.TwU.NearAt at hx2 hy2 ⊢
  have key := nearAt_prod_of_conj _ _ _ _ _ _ hx2 hy2 (GlobalTheory.CplPt.seamGL_int (sm I l Z) ⟨g', hint⟩)
  rw [map_mul (GlobalTheory.Mem.Col2.ChartLevel.emb v)]
  erw [map_mul (GlobalTheory.TwU.seamGL (sm I l Z)) g g']
  exact key

theorem chiInv_last_eq_char {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (P : SBof I a) :
    ∃ φ : ↥(prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1) →* B.fields.Kˣ,
      ∀ r ∈ Loc.Cbe (Jat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1) 1,
      ∀ g (hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1),
      (∀ x, r (Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) x) = Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) (g x)) →
      chiInv I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 r = φ ⟨g, hg⟩ := by
  have hL := hOk.idx_ok a
  obtain ⟨b, hb⟩ := last_rep_one I hOk a
  have hint := prCat_last_le_GLint I hOk a P
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · have hH : ∀ g (hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1),
        GlobalTheory.TopStep.redGL _ P.1 ⟨g, hint hg⟩ ∈ ((I.idx a).levG (B.R.m - 1) b ⟨P.1, hP⟩).H := fun g hg =>
      (hL.grpG _ b ⟨P.1, hP⟩ _).2 ⟨g, by rw [hb]; exact hg, fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hint hg⟩ hx⟩
    refine ⟨((I.idx a).levG (B.R.m - 1) b ⟨P.1, hP⟩).lam.comp
      (MonoidHom.codRestrict ((GlobalTheory.TopStep.redGL _ P.1).comp (Subgroup.inclusion hint)) _ fun g => hH g.1 g.2), ?_⟩
    intro r hr g hg hrx
    have hc := hL.chrG (B.R.m - 1) b ⟨P.1, hP⟩ ⟨_, hH g hg⟩ g r (by rw [hb]; exact hr) hrx
      (fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hint hg⟩ hx)
    rw [hb] at hc
    exact hc.symm
  · classical
    have hQ := (Finset.mem_union.mp P.2).resolve_left hP
    have hH : ∀ g (hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1),
        (⟨g, hint hg⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N (B.R.m - 1)) P.1)) ∈ ((I.idx a).levQ (B.R.m - 1) b ⟨P.1, hQ⟩).H := fun g hg => by
      rw [hL.grpQ _ b ⟨P.1, hQ⟩, hb]
      exact Subgroup.mem_subgroupOf.2 hg
    refine ⟨((I.idx a).levQ (B.R.m - 1) b ⟨P.1, hQ⟩).lam.comp
      (MonoidHom.codRestrict (Subgroup.inclusion hint) _ fun g => hH g.1 g.2), ?_⟩
    intro r hr g hg hrx
    have hc := hL.chrQ (B.R.m - 1) b ⟨P.1, hQ⟩ ⟨⟨g, hint hg⟩, hH g hg⟩ r (by rw [hb]; exact hr) hrx
    rw [hb] at hc
    exact hc.symm

theorem midLev_mul_beforeLast : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z z' : B.fields.K), GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z → GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g' z' → GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 (g * g') (z * z') := by
  intro B X I hOk a P g g' z z' ⟨r, hr, hrx, hz⟩ ⟨r', hr', hrx', hz'⟩
  obtain ⟨φ, hφ⟩ := chiInv_last_eq_char I hOk a P
  have hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 := ⟨r, hr, hrx⟩
  have hg' : g' ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 := ⟨r', hr', hrx'⟩
  have hrr : ∀ x, (r * r') (Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) x) =
      Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) ((g * g') x) := fun x => by
    rw [LinearEquiv.mul_apply, hrx', hrx]
    rfl
  refine ⟨r * r', mul_mem hr hr', hrr, ?_⟩
  rw [hz, hz', hφ r hr g hg hrx, hφ r' hr' g' hg' hrx', hφ (r * r') (mul_mem hr hr') (g * g') (mul_mem hg hg') hrr,
    ← Units.val_mul, ← map_mul]
  rfl

theorem midLev_one_last : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a), GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 1 1 := by
  intro B X I hOk a P
  obtain ⟨φ, hφ⟩ := chiInv_last_eq_char I hOk a P
  refine ⟨1, one_mem _, fun x => rfl, ?_⟩
  rw [hφ 1 (one_mem _) 1 (one_mem _) (fun x => rfl)]
  exact (congrArg Units.val (map_one φ)).symm

theorem nearV_one_one {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (P : SBof I a) : NearV I l Z a v P 1 1 := by
  unfold NearV GlobalTheory.TwU.NearAt
  erw [map_one (GlobalTheory.TwU.seamGL (sm I l Z)), map_one, map_one, inv_one, one_mul]
  exact GlobalTheory.TwU.congAt_one _ _

open Classical in
theorem valV_factor {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (x : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))
    (P : SBof I a) (g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z : B.fields.K)
    (hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)) (hn : NearPair I l Z a v P x g z) :
    (if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z then h.2.choose_spec.choose else 1) = z := by
  rw [dif_pos ⟨hP, g, z, hn⟩]
  exact GlobalTheory.Mem.Col2.QChi.nearPair_val_unique I hOk l Z a v P x _ g _ z (Exists.choose_spec (Exists.choose_spec (⟨hP, g, z, hn⟩ : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z).2)) hn

open Classical in
theorem valV_factor_off {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (x : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))
    (P : SBof I a) (hP : ¬ IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)) :
    (if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z then h.2.choose_spec.choose else 1) = 1 :=
  dif_neg fun h => hP h.1

theorem valV_mul : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), GlobalTheory.Mem.Col2.QChi.valV I l Z a v 1 = 1 ∧ ∀ x y, x ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → y ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → GlobalTheory.Mem.Col2.QChi.valV I l Z a v (x * y) = GlobalTheory.Mem.Col2.QChi.valV I l Z a v x * GlobalTheory.Mem.Col2.QChi.valV I l Z a v y := by
  intro B X I hOk l Z a v
  constructor
  · unfold valV
    rw [Finset.prod_eq_one, map_one]
    intro P _
    by_cases hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    · exact valV_factor I hOk l Z a v 1 P 1 1 hP ⟨midLev_one_last I hOk a P, nearV_one_one I l Z a v P⟩
    · exact valV_factor_off I l Z a v 1 P hP
  · intro x y hx hy
    unfold valV
    rw [← map_mul, ← Finset.prod_mul_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
    by_cases hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    · have hx' : ∃ g z, NearPair I l Z a v P x g z := hx P hP
      have hy' : ∃ g z, NearPair I l Z a v P y g z := hy P hP
      obtain ⟨g, z, hgz⟩ := hx'
      obtain ⟨g', z', hgz'⟩ := hy'
      have hxy : NearPair I l Z a v P (x * y) (g * g') (z * z') := ⟨midLev_mul_beforeLast I hOk a P g g' z z' hgz.1 hgz'.1, nearV_mul_pairs I hOk l Z a v P x y g g' z z' hgz hgz'⟩
      rw [valV_factor I hOk l Z a v (x * y) P _ _ hP hxy, valV_factor I hOk l Z a v x P _ _ hP hgz, valV_factor I hOk l Z a v y P _ _ hP hgz']
    · rw [valV_factor_off I l Z a v (x * y) P hP, valV_factor_off I l Z a v x P hP, valV_factor_off I l Z a v y P hP, mul_one]

end GlobalTheory.Mem.Col2.QChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFormsReferenceTupleIsometryColumnPairing
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.St

attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 1000000 in

theorem eMt0_isometry : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u F G, inner ℂ ((w.D x.o.Z).eMt u F) ((w.D x.o.Z).eMt u G) = TC.ipMt w.I w.l u w.I.mu0 F G := by
  intro K B f T w hO hF hP P x hη u F G
  show inner ℂ (P.q.e.e0 u F) (P.q.e.e0 u G) = _
  have hN : ∀ m : (Df.MtHL w.I P.hX w.I.mu0).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL w.I P.hX w.I.mu0).b (Df.MtHL w.I P.hX w.I.mu0).X
      (InfinitePlace.mk B.embLL) m = ‖P.q.per.e w.I.mu0 (Df.toCx w.I P.hX w.I.mu0 m)‖ :=
    GlobalTheory.T.periodRelation_preserves_levelForm_lattice_norm (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr w.I.mu0 (P.q.t.tA true w.I.mu0) (P.q.per.e w.I.mu0) (P.q.per.crd w.I.mu0)
  have hin : ∀ y y' : Df.MtCx w.I w.I.mu0, inner ℂ (P.q.per.e w.I.mu0 y) (P.q.per.e w.I.mu0 y') = Df.cSum w.I P.hX w.I.mu0 y y' := by
    intro y y'
    obtain ⟨-, ⟨j, hj⟩, -, hsp⟩ := GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis w.I P.hX w.I.mu0
    obtain ⟨k, hk⟩ := Df.exists_embLL_im_ne (B := B) P.hX
    have hspan : Submodule.span ℂ (Set.range j) = ⊤ := by
      rw [eq_top_iff, ← hsp]
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, hj _⟩)
    exact Df.inner_eq_of_norm_sq B.embLL j hspan k hk (P.q.per.e w.I.mu0).toLinearMap (Df.cSum w.I P.hX w.I.mu0) (fun m => by
      rw [hj, LinearEquiv.coe_toLinearMap, ← hN m, GlobalTheory.T.normAt_sq_integralForm_eq_classSumMetric w.I P.hX w.I.mu0 m]) y y'
  have key : ∀ F : ((w.D x.o.Z).mem u).P.Mt,
      Df.SameForm w.I w.l u w.I.mu0 ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F)) F := fun F => by
    have h := P.q.per.ref u ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F))
    erw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h
    exact h
  have h1 : ∀ F : ((w.D x.o.Z).mem u).P.Mt, P.q.e.e0 u F = P.q.per.e w.I.mu0 ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F)) :=
    fun F => ((P.q.per.e w.I.mu0).apply_symm_apply _).symm
  rw [h1 F, h1 G]
  exact (hin _ _).trans (GlobalTheory.T.rowFormMetric_eq_classSumMetric w.I w.ok w.pins w.l P.hX x.o.Z u w.I.mu0 F G _ _ (key F) (key G)).symm

end GlobalTheory.Mem.R3.Rw.St

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputs
section
noncomputable section

namespace GlobalTheory.PtSt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

theorem map_MjSig_eq (D : D7) (i : D.nd.Loc) (hInt : Rows.IsotInternal D.what₂) (h42 : SumRepresentations.At.Conclusion42 D.nd D.naut i)
    (hUp : ParUpRec D.nd D.naut i) (hDown : DownMemRec D.nd D.naut i) (hNZ : TypeNZRec D.nd D.naut i) :
    ∀ x ∈ ZgoodN D.nd D.naut i, ∀ Sig, HasParamX D.nd D.naut i x Sig →
      (MjSig D.nd D.naut i Sig).map (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) = eigC D.nd D.naut i x := by
  intro x hx Sig hS
  refine Submodule.eq_of_le_of_finrank_le (hUp x hx Sig hS) ?_
  have hinj := SumRepresentations.thetaT_injective D.nd D.naut i hInt h42
  have h1 : Module.finrank ℂ ↥((MjSig D.nd D.naut i Sig).map (D.what₂.thetaT (D.nd.mu i) (D.nd.j i))) =
      Module.finrank ℂ ↥(MjSig D.nd D.naut i Sig) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (MjSig D.nd D.naut i Sig))).symm
  have hfi : Function.Injective ((D.what₂.thetaP (D.nd.mu i) (D.nd.j i)).domRestrict (eigC D.nd D.naut i x)) := by
    rw [injective_iff_map_eq_zero]
    intro F hF
    exact Subtype.ext (hNZ x hx F.1 F.2 hF)
  have h2 : Module.finrank ℂ ↥(eigC D.nd D.naut i x) =
      Module.finrank ℂ ↥((eigC D.nd D.naut i x).map (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))) := by
    rw [← LinearMap.range_domRestrict]
    exact (LinearMap.finrank_range_of_inj hfi).symm
  rw [h1, h2]
  exact Submodule.finrank_mono (hDown x hx Sig hS)

theorem reducedMultiplicity_of_rows :
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.NRows.Inputs hL D → GlobalTheory.NRows.Rows D → SumRepresentations.ReducedMultiplicityStatement D := by
  intro hL D I R i _
  have hInt : Rows.IsotInternal D.what₂ := I.isot
  have h42 : SumRepresentations.Conclusion42 D := (I.Conclusion1 (GlobalTheory.T.parts_give_dimension D) R.a R.b).2.2
  have h1 := map_MjSig_eq D i hInt (h42 i) (R.c.parUp i) (R.c.downMem i) (R.typeNZ i)
  exact ⟨h1, (SumRepresentations.good_part_image_iff D.nd D.naut i hInt (h42 i) h1).2 (R.c.goodPart i)⟩

end GlobalTheory.PtSt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCompatibilitiesTransportReplacedStagesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowCompatibilities_transport_replacedStages : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), RowsSame t t' → Nonempty (RXs t) → Nonempty (RXs t') := by
  first | exact @GlobalTheory.Mem.R3.Rw.Up.rxs_up | exact GlobalTheory.Mem.R3.Rw.Up.rxs_up | (intros; apply GlobalTheory.Mem.R3.Rw.Up.rxs_up <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsPassToMovedDivisionLatticesHeightsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_pass_to_moved_divisionLatticesHeights : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (O : Obj2 (w.D Z)) (t : RowsT K w Z Wt O.p0) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (O' : Obj2 (w.D (Db.setDivZ Z N h))), O' = O.tr N h → ∃ t' : RowsT K w (Db.setDivZ Z N h) Wt O'.p0, RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z Z.S N h) (iK := t.r.z.alg) t.r.z.geo) ∧ HEq (SRe.pkOf t') ((SRe.pkOf t).up Z Z.S N h) ∧ (ObjT O t → ObjT O' t') ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  first | exact @GlobalTheory.Mem.R3.Rw.DivMv.rows_move_geo | exact GlobalTheory.Mem.R3.Rw.DivMv.rows_move_geo | (intros; apply GlobalTheory.Mem.R3.Rw.DivMv.rows_move_geo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueChainsKernelDatumSourceSideLatticeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChains_kernelDatum_sourceSideLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls i → ((I.rec7 l Z).chTw u μ).Y i → ℂ, (∃ x ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat i).L, ((I.tw l l0 Z).fm u μ).emb i x = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi i ∧ ∀ c, ∃ v : ValQ O u μ i, evC O u μ i v = φ c ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  first | exact @GlobalTheory.KerLatS.kerEntHyp_latS | exact GlobalTheory.KerLatS.kerEntHyp_latS | (intros; apply GlobalTheory.KerLatS.kerEntHyp_latS <;> assumption)
end

