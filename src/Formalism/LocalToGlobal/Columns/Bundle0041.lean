import Formalism.LocalToGlobal.Columns.Bundle0038
import Formalism.LocalToGlobal.Columns.ChainOneB
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0017
import Formalism.LocalToGlobal.Columns.RecChainCUnfPol
import Formalism.LocalToGlobal.Columns.Bundle0039

-- bundled from Formalism.LocalToGlobal.Columns.HsExtUHLast
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hs_padL_succ (n : ℕ) : padL E n (n + 1) = incl E n := by
  apply LinearMap.ext
  intro x
  funext j
  rw [padL_apply]
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [incl]
  · simp [incl]

theorem hs_extUH_pad {N n : ℕ} (hN : N = n + 1) (g : UF E n) (x : Fin n → E) :
    (extUH hN g).1 (padL E n N x) = padL E n N (g.1 x) := by
  subst hN
  rw [hs_padL_succ]
  show extE g.1 (incl E n x) = incl E n (g.1 x)
  apply sp_ext
  · rw [initL_extE, initL_incl, initL_incl]
  · rw [extE_last]
    simp [incl]

theorem hs_extUH_last {N n : ℕ} (hN : N = n + 1) [NeZero N] (g : UF E n) (p : E) :
    (extUH hN g).1 (Pi.single (lastIdx N) p) = Pi.single (lastIdx N) p := by
  subst hN
  rw [← lastVector_eq_single]
  show extE g.1 (z0 E n p) = z0 E n p
  apply sp_ext
  · rw [initL_extE]
    simp [z0]
  · rw [extE_last]

theorem hs_conj {N : ℕ} (g e : UF E N) (w : Sp E N) : g.1 ((g⁻¹ * e * g⁻¹⁻¹).1 (g.1.symm w)) = e.1 w := by
  rw [inv_inv]
  show g.1 (g.1.symm (e.1 (g.1 (g.1.symm w)))) = e.1 w
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem hs_core {V V' : Type} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V'] {N n : ℕ} (hN : N = n + 1) [NeZero N]
    (e : V ≃ₗ[E] (Fin N → E)) (e' : V' ≃ₗ[E] (Fin n → E)) (ι : V' →ₗ[E] V) (hι : ∀ x, e (ι x) = padL E n N (e' x))
    (γ M : V ≃ₗ[E] V) (S : V' ≃ₗ[E] V') (g₀ : UF E N) (s : UF E n)
    (hγ : ∀ x, e (γ x) = g₀.1 (e x)) (hM : ∀ x, e (M x) = (g₀⁻¹ * extUH hN s * g₀⁻¹⁻¹).1 (e x)) (hSs : ∀ x, e' (S x) = s.1 (e' x))
    (z : V) (p : E) (hz : e z = Pi.single (lastIdx N) p) :
    (∀ x, γ (M (γ.symm (ι x))) = ι (S x)) ∧ γ (M (γ.symm z)) = z := by
  have hγs : ∀ y, e (γ.symm y) = g₀.1.symm (e y) := fun y => by
    rw [LinearEquiv.eq_symm_apply, ← hγ, LinearEquiv.apply_symm_apply]
  constructor
  · intro x
    apply e.injective
    rw [hγ, hM, hγs, hs_conj, hι, hs_extUH_pad, hι, hSs]
  · apply e.injective
    rw [hγ, hM, hγs, hs_conj, hz, hs_extUH_last]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem hs_stab_crd (hc : CMData F E) {V : Type} [AddCommGroup V] [Module E V] {n' n : ℕ} [NeZero n] (b : Basis (Fin n') E V) (h : n' = n)
    (g : GL (Fin n') E) (t : UF E n) (hg : Formalism.L2.Forms.reGL h E g = ((ratEquiv hc n).symm t).1) (x : V) :
    hqCrd b h ((Formalism.L2.Herm.toGLb b).symm g x) = t.1 (hqCrd b h x) := by
  have h1 := hq_reGL_mulVec b h ((Formalism.L2.Herm.toGLb b).symm g) x
  rw [MulEquiv.apply_symm_apply, hg, ← rlc_ratHom_apply hc n] at h1
  have h2 : ratHom hc n ((ratEquiv hc n).symm t) = t := (ratEquiv hc n).apply_symm_apply t
  rw [h2] at h1
  exact h1.symm

end Gen

section GenL

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem levPack_stabI (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) (c : DecoCl n (Pr.vT u) Pr.vGs Λ.grp)
    (t : MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) :
    Formalism.L2.Forms.reGL H.hn X.E ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.stabI c t).1 = ((ratEquiv hc n).symm t.1.1).1 := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact Formalism.L2.Forms.reGL_rfl _ _

end GenL

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (hQ : PtSurj d) (hK : LocalLevelIsKOneEverywhere d)
  (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)

include hS in

theorem hs_iX (x : d.sp.X'.V) :
    CF.crdN (d.colRec a) d.R.m le_rfl (d.sp.iX' x) = padL d.host.E (d.R.N d.R.m - 1) (d.R.N d.R.m) (CF.crdP (d.colRec a) x) := by
  rw [← iXc_eq a hS]
  show _ = CF.crdN (d.colRec a) d.R.m le_rfl (d.sp.iX' ((CF.crdP (d.colRec a)).symm (CF.crdP (d.colRec a) x)))
  rw [LinearEquiv.symm_apply_apply]

theorem hs_tilG (u : d.what₂.Word) (c : PCl d) (x : (d.sp.X d.R.m).V) :
    CF.crdN (d.colRec a) d.R.m le_rfl (((levelExponentAtT a hS hH hP u).tilG c).1 x) =
      (d.tilMv u c).1.1 (CF.crdN (d.colRec a) d.R.m le_rfl x) :=
  (hqG_crd d.R.m le_rfl ((tildeLatticeAgreement a hS hH hP u).ga c) x).trans (tilGa_mulVec u c _)

set_option maxHeartbeats 4000000 in

theorem stabMapTied (disc : ∀ u, AtTDisc (d.colRec a) u)
    (moves : ∀ u, AtTMoves (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)) :
    CH.StabMapTied (d.colRec a) (hermCols a hS hQ hK S hI) (hermAtT a hS hH ⟨disc, moves, levelExponentAtT a hS hH hP⟩) := by
  intro u h1 c s
  exact hs_core (E := d.X.E) (N_m_succ d.R) (CF.crdN (d.colRec a) d.R.m le_rfl) (CF.crdP (d.colRec a)) d.sp.iX' (hs_iX a hS)
    ((levelExponentAtT a hS hH hP u).tilG c).1 _ _ (d.tilMv u c).1 s.1.1 (hs_tilG a hS hH hP u c)
    (fun x => hs_stab_crd d.sp.cm (d.sp.X d.R.m).frame (CF.rankN (d.colRec a) d.R.m le_rfl) _ _
      (levPack_stabI d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m) _ _ _ _ (hK u d.R.m) (hCrd hS u d.R.m le_rfl) _
        (stabMapR (Pr := d.Pr) (W := d.W) (Λ := d.lev) (Finset.Subset.refl _) (ΛM := d.levP) d.hPr u (a.piT_off u) a.levExt c s)) x)
    (fun x => hs_stab_crd d.sp.cm d.sp.X'.frame (CF.rankP (d.colRec a)) _ _
      (levelPacking_stabilizer d.sp.cm d.hPr d.σ₀ d.levP.inv d.reprP hP _ (hCrdP a hS hH hP u) c s) x)
    (levelExponentAtT a hS hH hP u).z0 (d.piT u : d.host.E) (joint_lastVector a hS hH hP u).symm

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ResidueFieldUnfoldingClaimsHold
section
namespace Formalism.L2.Col

theorem residueFieldUnfolding_claims_hold : ResidueFieldUnfoldingSupport ∧ ResidueFieldUnfoldingNonzero := by
  refine ⟨?_, ?_⟩
  · intro k _ _ ψ₀ χ k₀ m t j n' c n _ hr h hne
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    exact (support_oneCoset k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).1 h hne
  · intro k _ _ ψ₀ χ k₀ m t j n' c n _ hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    exact (support_oneCoset k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).2

end Formalism.L2.Col
end

-- bundled from Formalism.LocalToGlobal.Columns.StabMapRLInjective
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section XpL

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Λm : LevFam X.E X.K (R.N R.m) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG')
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

@[reducible] def topGSD (u : Pr.Word) : GSD X.K := formGSD (colVal W u R.m (Pr.vT u) Pr.vGs) Λm

def topEv (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) : (topGSD W Λm u).Ev σ₀ :=
  roundEv σ₀ hσ (W.lamTrue u R.m) (fun d => d.1.Lsh) Λm

variable {W ΛM}

variable (ΛM) in

def LevExtL : Prop := ∀ h : ↥(ΛM.inv).grp, (extR R hSG ((1 : UF X.E (R.N R.m - 1)), h.1)).2 ∈ Λm.grp

variable {Λm}

def extFL (hL : LevExtL Λm hSG ΛM) (u : Pr.Word) : (ptGSD W ΛM).G →* (topGSD W Λm u).G where
  toFun a := ((extR R hSG (a.1, a.2.1)).1, ⟨(extR R hSG (a.1, a.2.1)).2, hL a.2⟩)
  map_one' := by
    apply Prod.ext
    · exact map_one (extUH (N_m_succ R))
    · apply Subtype.ext
      exact congrArg Prod.snd (map_one (extR R hSG))
  map_mul' a b := by
    apply Prod.ext
    · exact map_mul (extUH (N_m_succ R)) a.1 b.1
    · apply Subtype.ext
      exact congrArg Prod.snd (map_mul (extR R hSG) (a.1, a.2.1) (b.1, b.2.1))

theorem tilR_smulFL (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL Λm hSG ΛM)
    (a : (ptGSD W ΛM).G) (d : DecoSet X.E (R.N R.m - 1) ∅ SG') :
    tilR hSG u (a • d) = extFL hSG hL u a • tilR hSG u d := by
  show tilR hSG u (FormG.incl _ a • d) = FormG.incl _ (extFL hSG hL u a) • tilR hSG u d
  exact tilR_smul hSG hPr u hpi (a.1, a.2.1) d

variable (W Λm ΛM) in

def tilClL (u : Pr.Word) (c : (ptGSD W ΛM).Cl) : (topGSD W Λm u).Cl :=
  (topGSD W Λm u).cls (tilR hSG u ((ptGSD W ΛM).outSec.rep c))

def stabMapRL (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL Λm hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →* MulAction.stabilizer (topGSD W Λm u).G ((topGSD W Λm u).outSec.rep (tilClL W Λm hSG ΛM u c)) :=
  ((MulAut.conj ((topGSD W Λm u).outSec.mv (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))⁻¹).toMonoidHom.comp
    ((extFL hSG hL u).comp (Subgroup.subtype _))).codRestrict _ (fun s => by
      rw [MulAction.mem_stabilizer_iff]
      show (((topGSD W Λm u).outSec.mv (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))⁻¹ * extFL hSG hL u s.1 *
        ((topGSD W Λm u).outSec.mv (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))⁻¹⁻¹) •
          (topGSD W Λm u).outSec.rep (tilClL W Λm hSG ΛM u c) = _
      rw [inv_inv, mul_smul, mul_smul]
      have h1 : (topGSD W Λm u).outSec.mv (tilR hSG u ((ptGSD W ΛM).outSec.rep c)) •
          (topGSD W Λm u).outSec.rep (tilClL W Λm hSG ΛM u c) = tilR hSG u ((ptGSD W ΛM).outSec.rep c) :=
        (topGSD W Λm u).outSec.mv_smul _
      rw [h1, ← tilR_smulFL hSG hPr u hpi hL, s.2, inv_smul_eq_iff, h1])

theorem stabMapRL_injective (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL Λm hSG ΛM)
    (c : (ptGSD W ΛM).Cl) : Function.Injective (stabMapRL hSG hPr u hpi hL c) := by
  intro s s' h
  have h1 := congrArg Subtype.val h
  have h2 : extFL hSG hL u s.1 = extFL hSG hL u s'.1 := (MulAut.conj _).injective h1
  have h3 : s.1.1 = s'.1.1 := rec_extUH_injective (N_m_succ R) (congrArg Prod.fst h2)
  exact Subtype.ext (formGSD_stab_inj _ _ _ s.2 s'.2 h3)

variable (W Λm ΛM) in

def lowCL (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) :
    (FrS X σ₀ (R.N R.m) → ℂ) →ₗ[ℂ] (FrS X σ₀ (R.N R.m - 1) → ℂ) :=
  (topEv W Λm σ₀ hσ u).extend ((ptEv W ΛM σ₀ hσ).ev.comp (brC W u))

theorem lowCL_ev (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (x : VV X.K (W.lamTrue u R.m)) :
    lowCL W Λm ΛM σ₀ hσ u ((topEv W Λm σ₀ hσ u).ev x) = (ptEv W ΛM σ₀ hσ).ev (brC W u x) :=
  (topEv W Λm σ₀ hσ u).extend_ev _ x

end XpL

section XpC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R) (bm : Λ.β R.m)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG')
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

theorem stepF_mem_top (u : Pr.Word) : (stepF W Λ u R.m).mem bm = topGSD W (Λ.lev R.m bm) u := rfl

def LevExtC : Prop := LevExtL (Λ.lev R.m bm) hSG ΛM

variable {W Λ bm ΛM}

def extFC (hL : LevExtC Λ bm hSG ΛM) (u : Pr.Word) : (ptGSD W ΛM).G →* (stepF W Λ u R.m).G bm :=
  extFL (W := W) hSG hL u

theorem tilR_smulFC (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtC Λ bm hSG ΛM)
    (a : (ptGSD W ΛM).G) (d : DecoSet X.E (R.N R.m - 1) ∅ SG') :
    tilR hSG u (a • d) = (extFC hSG hL u a : (topGSD W (Λ.lev R.m bm) u).G) • tilR hSG u d :=
  tilR_smulFL hSG hPr u hpi hL a d

variable (W Λ bm ΛM) in

def tilClC (u : Pr.Word) (c : (ptGSD W ΛM).Cl) : StClC W Λ u R.m := ⟨bm, tilClL W (Λ.lev R.m bm) hSG ΛM u c⟩

def stabMapRC (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtC Λ bm hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →* FamStab (stepF W Λ u R.m) (tilClC W Λ bm hSG ΛM u c) :=
  stabMapRL hSG hPr u hpi hL c

theorem stabMapRC_injective (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtC Λ bm hSG ΛM)
    (c : (ptGSD W ΛM).Cl) : Function.Injective (stabMapRC (W := W) hSG hPr u hpi hL c) :=
  stabMapRL_injective hSG hPr u hpi hL c

variable (W Λ bm ΛM) in

def lowCC (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) :
    (FrS X σ₀ (R.N R.m) → ℂ) →ₗ[ℂ] (FrS X σ₀ (R.N R.m - 1) → ℂ) :=
  lowCL W (Λ.lev R.m bm) ΛM σ₀ hσ u

theorem lowCC_ev (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (x : VV X.K (W.lamTrue u R.m)) :
    lowCC W Λ bm ΛM σ₀ hσ u (evV X.emb 1 (W.lamTrue u R.m) σ₀ x) = (ptEv W ΛM σ₀ hσ).ev (brC W u x) :=
  lowCL_ev σ₀ hσ u x

variable (W Λ bm) in

def resTop (σ₀ : X.K →+* ℂ) (u : Pr.Word) :
    (StClC W Λ u R.m → FrS X σ₀ (R.N R.m) → ℂ) →ₗ[ℂ] ((topGSD W (Λ.lev R.m bm) u).Cl → FrS X σ₀ (R.N R.m) → ℂ) :=
  LinearMap.funLeft ℂ (FrS X σ₀ (R.N R.m) → ℂ) fun c₀ : (topGSD W (Λ.lev R.m bm) u).Cl => (⟨bm, c₀⟩ : StClC W Λ u R.m)

theorem resTop_apply (σ₀ : X.K →+* ℂ) (u : Pr.Word) (F : StClC W Λ u R.m → FrS X σ₀ (R.N R.m) → ℂ)
    (c₀ : (topGSD W (Λ.lev R.m bm) u).Cl) : resTop W Λ bm σ₀ u F c₀ = F ⟨bm, c₀⟩ := rfl

variable (bm) in

def recPerC (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) : PeriodMap R (recChainC hX σ₀ G u A) where
  Mt := Fin ((rowGSD W ΛM).hDim hM) → ℂ
  Wz := (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m) → ℂ
  evz := ((topEv W (Λ.lev R.m bm) σ₀ hσ u).evAt fun c => tilR hSG u ((ptGSD W ΛM).outSec.rep c)) ∘ₗ resTop W Λ bm σ₀ u
  Wrow := (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m - 1) → ℂ
  lowerMap := LinearMap.pi fun c => lowCC W Λ bm ΛM σ₀ hσ u ∘ₗ LinearMap.proj c
  period := periodC W ΛM hX σ₀ hσ hM

structure ThArgC (W : Wts X Pr.Word R) (Λ : LevCh X Pr R) (u : Pr.Word) where

  beOn : X.Tau → ℝ
  beOn_nonneg : ∀ τ, 0 ≤ beOn τ

  thN : ∀ i, (X.K →+* ℂ) → StClC W Λ u i → StClC W Λ u (i + 1) → ℝ
  thN_nonneg : ∀ i s L L', 0 ≤ thN i s L L'

  thFree : ∀ i, (X.K →+* ℂ) → StClC W Λ u i → StClC W Λ u (i + 1) → ℝ
  thFree_nonneg : ∀ i s L L', 0 ≤ thFree i s L L'

theorem recPerC_evz (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) (F : StClC W Λ u R.m → FrS X σ₀ (R.N R.m) → ℂ)
    (c : (ptGSD W ΛM).Cl) :
    (recPerC bm hSG hX σ₀ hσ u G A hM).evz F c =
      (topEv W (Λ.lev R.m bm) σ₀ hσ u).trPt (tilR hSG u ((ptGSD W ΛM).outSec.rep c)) (F (tilClC W Λ bm hSG ΛM u c)) := rfl

def recXpC (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal)
    (hL : LevExtC Λ bm hSG ΛM) (Th : ThArgC W Λ u) : XpArg σ₀ (recChainC hX σ₀ G u A) (recPerC bm hSG hX σ₀ hσ u G A hM) where
  clsP := (ptGSD W ΛM).Cl
  clsPFin := (ptOk W ΛM hX).fintypeCl
  stabilizer₂ := fun c => MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c)
  stabPGrp := fun _ => inferInstance
  stabPFin := fun _ => (ptOk W ΛM hX).fin_stab _
  til := tilClC W Λ bm hSG ΛM u
  stabMap := stabMapRC hSG hPr u hpi hL
  stabMap_inj := stabMapRC_injective hSG hPr u hpi hL
  evz_til := fun φ ψ h => by
    funext c
    exact (recPerC_evz hSG hX σ₀ hσ u G A hM φ c).trans
      ((congrArg ((topEv W (Λ.lev R.m bm) σ₀ hσ u).trPt (tilR hSG u ((ptGSD W ΛM).outSec.rep c))) (h c)).trans
        (recPerC_evz hSG hX σ₀ hσ u G A hM ψ c).symm)
  ptC := (ptEv W ΛM σ₀ hσ).Fi
  ipP := (ptEv W ΛM σ₀ hσ).ipCl (ptOk W ΛM hX)
  ptLat := ptH W ΛM hX
  ptLat_good := ptH_good W ΛM hX
  ptEmb := (ptEv W ΛM σ₀ hσ).emb
  ptEmb_basis := ⟨(ptEv W ΛM σ₀ hσ).emb_li (ptOk W ΛM hX) _ ((ptGSD W ΛM).hB (ptOk W ΛM hX)).linearIndependent,
    (ptEv W ΛM σ₀ hσ).span_basis _⟩
  ptEmb_norm := fun x => (ptEv W ΛM σ₀ hσ).norm_ipCl (ptOk W ΛM hX) (ptRat W ΛM hX) hσ x
  beOn := Th.beOn
  beOn_nonneg := Th.beOn_nonneg
  thN := Th.thN
  thN_nonneg := Th.thN_nonneg
  thFree := Th.thFree
  thFree_nonneg := Th.thFree_nonneg

theorem recPerC_lower_emb (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) (F : StClC W Λ u R.m → FrS X σ₀ (R.N R.m) → ℂ)
    (φ : (topGSD W (Λ.lev R.m bm) u).EqFun) (hF : resTop W Λ bm σ₀ u F = (topEv W (Λ.lev R.m bm) σ₀ hσ u).emb φ) (c : (ptGSD W ΛM).Cl) :
    (recPerC bm hSG hX σ₀ hσ u G A hM).lowerMap ((recPerC bm hSG hX σ₀ hσ u G A hM).evz F) c =
      (ptEv W ΛM σ₀ hσ).ev (brC W u ((φ : (topGSD W (Λ.lev R.m bm) u).D → (topGSD W (Λ.lev R.m bm) u).V)
        (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))) := by
  show lowCL W (Λ.lev R.m bm) ΛM σ₀ hσ u ((topEv W (Λ.lev R.m bm) σ₀ hσ u).atPt (tilR hSG u ((ptGSD W ΛM).outSec.rep c))
    (resTop W Λ bm σ₀ u F)) = _
  rw [hF, GSD.Ev.atPt_emb]
  exact lowCL_ev σ₀ hσ u _

theorem recPerC_lower_fam (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) (φ : (stepF W Λ u R.m).Forms) (c : (ptGSD W ΛM).Cl) :
    (recPerC bm hSG hX σ₀ hσ u G A hM).lowerMap ((recPerC bm hSG hX σ₀ hσ u G A hM).evz
        (fun c' : StClC W Λ u R.m => evV X.emb 1 (W.lamTrue u R.m) σ₀ ((φ c'.1).1 (repC c')))) c =
      (ptEv W ΛM σ₀ hσ).ev (brC W u ((φ bm).1 (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))) :=
  recPerC_lower_emb hSG hX σ₀ hσ u G A hM _ (φ bm) rfl c

end XpC

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ₀ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

theorem LevExtC_one : LevExtC (LevCh.one Λ₀) () hSG ΛM ↔ LevExt Λ₀ hSG ΛM := Iff.rfl

theorem tilClC_one (u : Pr.Word) (c : (ptGSD W ΛM).Cl) :
    tilClC W (LevCh.one Λ₀) () hSG ΛM u c = ⟨(), tilCl W Λ₀ hSG ΛM u c⟩ := rfl

theorem lowCC_one (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) :
    lowCC W (LevCh.one Λ₀) () ΛM σ₀ hσ u = lowC W Λ₀ ΛM σ₀ hσ u := rfl

theorem recPerC_evz_one (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W (LevCh.one Λ₀) G u) (A₀ : ChainArg W Λ₀ G u) (hM : (rowGSD W ΛM).Ok)
    (F : StClC W (LevCh.one Λ₀) u R.m → FrS X σ₀ (R.N R.m) → ℂ) :
    (recPerC () hSG hX σ₀ hσ u G A hM).evz F = (recPer hSG hX σ₀ hσ u G A₀ hM).evz fun c₀ : StCl W Λ₀ u R.m => F ⟨(), c₀⟩ := rfl

end One

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQDCls
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QCls

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

variable (ST SG Q) in

def FrExists : Prop :=
  ∀ (d : DecoSet E n ST SG) (P : Q), ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ y, f y ∈ d.1.at P.1 ↔ y ∈ stdAt E n P.1

theorem qdf_toGLm_ratHom (γ : URat hc n) : toGLm E n (ratHom hc n γ).1 = (γ : GL (Fin n) E) := by
  simp [toGLm, ratHom, Formalism.UG.glEquiv]

variable (H : Subgroup (GLG E n SG))

theorem qdf_rel_of_orbit (q : QLoc hc n Q Θ) {x x' : UAd hc n} {p : DecoF E n ST SG Q} (a : UF E n × H × Θ.grp)
    (hx : FrOver q x.1 p) (hx' : FrOver q x'.1 (a • p)) :
    ∃ (γ : URat hc n) (κ : levUQ hc n ST SG Q H q), ratHom hc n γ = a.1 ∧
      (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
        (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
  have hd : decoOf ST SG (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((a.1, a.2.1) : UF E n × H) • decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [hx'.1, hx.1]; rfl
  obtain ⟨γ, k, h1, -, e⟩ := rlc_rel_of_orbit hc n ST SG H (a.1, a.2.1) hd
  have hkQ : ∀ P : Q, q.at P (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ q.U P := by
    intro P
    have hke : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      rw [e]; group
    have hA := hx'.2 P
    have hB := hx.2 P
    have hθ : (a.2.2.1 P) ∈ (Θ P).H := (Subgroup.mem_pi _).1 a.2.2.2 P (Set.mem_univ _)
    have hC := (q.U_rat P (a.2.2.1 P)).2 hθ
    have hfr : (a • p).fr P = a.1.1 * p.fr P * ((a.2.2.1 P)⁻¹).1 := rfl
    have hγ : toGLm E n a.1.1 = (γ : GL (Fin n) E) := by rw [← h1]; exact qdf_toGLm_ratHom γ
    have key : q.at P (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        ((bc (q.phi P) (qGL n ((a • p).fr P)))⁻¹ * q.at P x')⁻¹ * bc (q.phi P) (qGL n (a.2.2.1 P).1) *
          ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x) := by
      rw [hke, qdf_at_mul, qdf_at_mul, qdf_at_inv, qdf_at_rat, hfr]
      simp only [qGL, map_mul, map_inv, Subgroup.coe_inv]
      rw [hγ]
      group
    rw [key]
    exact mul_mem (mul_mem (inv_mem hA) hC) hB
  exact ⟨γ, ⟨k.1, k.2, Subgroup.mem_iInf.2 hkQ⟩, h1, e⟩

theorem qdf_over_exists (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hE : FrExists (n := n) ST SG Q) (x : UAd hc n) :
    ∃ p : DecoF E n ST SG Q, FrOver q x.1 p := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : ∀ P : Q, Sp E n ≃ₗ[E] Sp E n,
      ∀ (P : Q) y, f P y ∈ (decoOf ST SG x.1).1.at P.1 ↔ y ∈ stdAt E n P.1 :=
    ⟨fun P => (hE (decoOf ST SG x.1) P).choose, fun P => (hE (decoOf ST SG x.1) P).choose_spec⟩
  let p0 : DecoF E n ST SG Q := ⟨(decoOf ST SG x.1, f), fun P y => hf P y⟩
  have hk := fun P : Q => hF x p0 rfl P
  choose g hg using fun P : Q => q.U_dense P _ (hk P).1 (hk P).2
  refine ⟨⟨(decoOf ST SG x.1, fun P => f P * (g P).1), fun P y => ?_⟩, rfl, fun P => ?_⟩
  · show f P ((g P).1 y) ∈ _ ↔ _
    rw [hf P]
    exact (g P).2 y
  · show (Formalism.UG.bc (q.phi P) (qGL n (f P * (g P).1)))⁻¹ * q.at P x.1 ∈ q.U P
    rw [show qGL n (f P * (g P).1) = qGL n (f P) * qGL n (g P).1 from map_mul _ _ _, map_mul, _root_.mul_inv_rev,
      mul_assoc]
    exact hg P

end QCls

end Formalism.L2.Col
end
end

