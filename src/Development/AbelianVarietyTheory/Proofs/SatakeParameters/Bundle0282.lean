import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0264
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0274
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90RangeEqNormOneOfIsQuad
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0461
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0261
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0271
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0265
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0267
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0256
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0273
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0272
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.PrimesOverExistence.Places
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
import GroundTheory.GlobalFields.TateThesis.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumInvarianceSupportTransportFrames
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0275

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralHilbert90DetHostField
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwU.IntegralHilbert90
open GlobalTheory.AdeleBaseChange
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def evP (P : HeightOneSpectrum (𝓞 E)) : FiniteAdeleRing (𝓞 E) E →+* P.adicCompletion E where
  toFun z := z P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem localComponent_apply₂ (P : HeightOneSpectrum (𝓞 E)) (z : FiniteAdeleRing (𝓞 E) E) : evP P z = z P := rfl

theorem localComponent_algebraMap (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    evP P (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) = algebraMap E (P.adicCompletion E) x := rfl

variable [StarRing E]

end GlobalTheory.TwU.IntegralHilbert90
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsStd
section
noncomputable section

namespace GlobalTheory.TwU.AtTrue.Cl

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : ChainCharts D u μ)
  (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E)

def TChain : Prop :=
  IsChainTopW t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) (t.rd u μ) t.seam.σ₀ (t.word u) t.m2
    (fun i hi => A.pt i (hi.trans (cpl_lt t μ).le))
    (fun i hi c => A.ib i ((Nat.lt_succ_of_le hi).trans (cpl_lt t μ)) ((St i _).chOf c)) A.yb (A.pt _ (top_le t μ))

def TTeq : Prop := ∀ i hi, (St i hi).T = (D.mem u).A.T

def TBad : Prop := ∀ i hi, ∀ v ∈ (St i hi).bad, UnderSB t μ v

def TLat : Prop := ∀ i hi c, t.seam.lat ((t.rd u μ).N i c) =
    latCo D.sp (gramN D i hi) (A.crd i hi) a ((St i hi).y c).1 ((St i hi).K ((St i hi).chOf c)).lev.Lb

def TFrame : Prop := ∀ i hi c (P : SB t μ), NearAt (seamP t.seam P.1) ((t.cst μ).D P)
    (A.mov i hi c * ratA D.host.F (A.fb i hi ((St i hi).chOf c) P)) (seamGL t.seam (frsF t.sel (t.tup μ) (A.pt i hi c) P))

def TFnl : Prop := ∀ i hi (β : (St i hi).Ch) (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
    IsOver v (seamP t.seam P.1) → ∃ ι : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal,
      ∀ c, (St i hi).chOf c = β → FunMoved t.seam ((St i hi).K β).lev P v h ι (A.mov i hi c) (A.pt i hi c).deco.1

def TCoset : Prop := ∀ c, ∀ y ∈ A.yb c, ∀ P : SB t μ, SameCoset t.sel (t.tup μ) (t.cst μ) P
    ((frsF t.sel (t.tup μ) (A.pt _ (cpl_lt t μ).le c) P).symm y) (A.y0 ((St _ (cpl_lt t μ).le).chOf c) P)

def TLevMid : Prop := ∀ i (hi : i < D.R.m), i ≤ t.m2 → ∀ β,
    LocLe t.seam ((St i hi.le).K β).lev (A.fb i hi.le β) (t.cst μ).D (A.midRel i hi β) ∧
    LocGe t.seam ((St i hi.le).K β).lev (A.fb i hi.le β) (t.cst μ).D (A.midRel i hi β) ∧
    ChiIs t.seam ((St i hi.le).K β).lev (A.fb i hi.le β) (t.cst μ).D (A.midRel i hi β)

def TLevCpl : Prop := ∀ β,
    LocLe t.seam ((St _ (cpl_lt t μ).le).K β).lev (A.fb _ _ β) (t.cst μ).D (A.cplRel β) ∧
    LocGe t.seam ((St _ (cpl_lt t μ).le).K β).lev (A.fb _ _ β) (t.cst μ).D (A.cplRel β) ∧
    ChiIs t.seam ((St _ (cpl_lt t μ).le).K β).lev (A.fb _ _ β) (t.cst μ).D (A.cplRel β)

def TLevTop : Prop := ∀ β,
    LocLe t.seam ((St _ (top_le t μ)).K β).lev (A.fb _ _ β) (topDep t.sel (t.tup μ) (t.cst μ))
      (TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1)) ∧
    ChiIs t.seam ((St _ (top_le t μ)).K β).lev (A.fb _ _ β) (topDep t.sel (t.tup μ) (t.cst μ))
      (TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1))

def TDt : Prop := ∀ i hi c (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm),
    Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det ((St i hi).y c).1 → (t.O u μ).dt i c = dtU y

def TAa : Prop := t.amb.AAUnit (Sall t.sel (t.tup μ) (t.word u))

variable {t u μ St A dtU a}

end Gen

section Std

open GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {Kc : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC}
  {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX} (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 B.host.F)))
  (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi)
  (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (K : ∀ i hi, Fam I l Z u a i hi bad (chOf i hi))

structure IsStd (A : AdData t u a (charts I l Z u a bad Ch chOf eY K)) : Prop where
  crd : ∀ i hi, A.crd i hi = 1
  iA : HEq A.iA (RingEquiv.refl (AfE B.host.F B.host.E))
  q : HEq A.q ((QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E)))
  pt : HEq A.pt (fun i (_ : i ≤ B.R.m) (c : (I.stp u a i).Cl) => ((I.stp u a i).rep c).1.1)
  yb : HEq A.yb (fun c : (I.stp u a (B.R.m - 2 + 1)).Cl => ((I.stp u a (B.R.m - 2 + 1)).rep c).1.2)
  ib : ∀ i (hi : i < B.R.m) (c : (I.stp u a i).Cl), HEq (A.ib i hi (chOf i hi.le c)) (Idx.get c.1 hi)
  fb : ∀ i hi β P, A.fb i hi β P = 1
  y0 : ∀ (h : B.R.m - 2 + 1 ≤ B.R.m) (c : (I.stp u a (B.R.m - 2 + 1)).Cl) (P : rowSG (B.primes X) I.sel (I.tup a))
    (β : (charts I l Z u a bad Ch chOf eY K (t.m2 + 1) (cpl_lt t a).le).Ch) (P' : SB t a),
    HEq β (chOf (B.R.m - 2 + 1) h c) → HEq P' P → (cosetIn ((I.stp u a (B.R.m - 2 + 1)).rep c) P).Nonempty →
      ∃ y ∈ cosetIn ((I.stp u a (B.R.m - 2 + 1)).rep c) P, HEq (A.y0 β P') y

def Hyp (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt) (A : AdData t u a (charts I l Z u a bad Ch chOf eY K)) : Prop :=
  I.Ok ∧ TC.Pins B X ∧ StdData I l Z t dt ∧ Side I l Z u a bad Ch chOf eY K ∧ (∀ i hi, ReadsOne I l Z u a i hi (chOf i hi) (K i hi)) ∧
    IsStd I l Z t u a bad Ch chOf eY K A

end Std

section Pf

open GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE

end Pf

end GlobalTheory.TwU.AtTrue.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelAwayAdapted
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem apart_of_apart_not_apart {w w₀ u : HeightOneSpectrum (𝓞 E)} (hw : Apart w w₀) (hu : ¬ Apart u w₀) : Apart u w := by
  unfold Apart at *
  intro h
  exact hw (h.symm.trans (not_not.1 hu))

theorem mem_levelOf_iff_of_locU {w₀ w : HeightOneSpectrum (𝓞 E)} {H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)}
    (hle : ∀ w, H w ≤ locU a w) (hfib : ∀ w u, ¬ Apart w u → H w = H u) (hw : Apart w w₀) {x : UA E a}
    (hx : x ∈ locU a w) : x ∈ levelOf a w₀ H ↔ x ∈ H w := by
  have hx' := (GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx
  constructor
  · intro h
    obtain ⟨y, hy, e⟩ := (mem_levelOf.1 h).2.2 w hw
    rw [← eq_of_cLoc_eq (hle w hy) hx e]
    exact hy
  · intro h
    refine mem_levelOf.2 ⟨hx'.1, fun u hu => hx'.2 u (apart_of_apart_not_apart hw hu), fun w' hw' => ?_⟩
    by_cases hw'w : Apart w' w
    · exact ⟨1, one_mem _, by rw [map_one, hx'.2 w' hw'w]⟩
    · exact ⟨x, by rw [hfib w' w hw'w]; exact h, rfl⟩

theorem map_eq_image {w : HeightOneSpectrum (𝓞 E)} {L : Subgroup (UA E a)} (hL : L ≤ locU a w)
    (e : locU a w ≃ₜ* GL (Fin a) (w.adicCompletion E)) (he : ∀ x : locU a w, e x = cLoc w (x : UA E a)) :
    ((L.map (cLoc w) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) =
      e '' ((L.subgroupOf (locU a w) : Subgroup (locU a w)) : Set (locU a w)) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hL hx⟩, Subgroup.mem_subgroupOf.2 hx, he _⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, Subgroup.mem_subgroupOf.1 hy, (he y).symm⟩

theorem injective_of_compAlong {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W}
    (hirr : σ.IsIrreducible) (f : W →ₗ[ℂ] (UA E a → ℂ)) (hf0 : f ≠ 0)
    (hf : ∀ (x : locU a w) v, f (σ (((cLoc w).comp (locU a w).subtype) x) v) = RU E a x (f v)) :
    Function.Injective f := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  rw [← LinearMap.ker_eq_bot]
  refine (((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hirr).2 _ (fun g u hu => ?_)).resolve_right fun h => hf0 ?_
  · rw [LinearMap.mem_ker] at hu ⊢
    have := hf (e.symm g) u
    have hg : ((cLoc w).comp (locU a w).subtype) (e.symm g) = g := by
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← he, e.apply_symm_apply]
    rw [hg] at this
    rw [this, hu, map_zero]
  · refine LinearMap.ext fun v => ?_
    have : v ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    simpa using this

theorem fix_of_fixed {U : Submodule ℂ (UA E a → ℂ)} {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hc : IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ)
    {J : Subgroup (GL (Fin a) (w.adicCompletion E))} (hJ : GlobalTheory.PRep.fixed σ.ρ J ≠ ⊥) :
    ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ J → RU E a x φ = φ := by
  obtain ⟨hirr, f, hf0, hfU, hf⟩ := hc
  have hinj := injective_of_compAlong hw hirr f hf0 hf
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hJ
  refine ⟨f v, hfU v, fun h => hv0 (hinj (by rw [h, map_zero])), fun x hx hxJ => ?_⟩
  have := hf ⟨x, hx⟩ v
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, GlobalTheory.LGrp.mem_fixed.1 hv _ hxJ] at this
  exact this.symm

theorem fixed_ne_bot_of_fix {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) {w : HeightOneSpectrum (𝓞 E)}
    (hw : IsSplitAt w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hc : IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ)
    {L : Subgroup (UA E a)} (hL : L ≤ locU a w) {φ : UA E a → ℂ} (hφU : φ ∈ U) (hφ0 : φ ≠ 0)
    (hφ : ∀ x ∈ L, RU E a x φ = φ) : GlobalTheory.PRep.fixed σ.ρ (L.map (cLoc w)) ≠ ⊥ := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hp : (cLoc w).comp (locU a w).subtype = e.toMulEquiv.toMonoidHom := MonoidHom.ext fun x => (he x).symm
  have hirr : Representation.IsIrreducible (σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) := by
    rw [hp]; exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ.ρ e.toMulEquiv σ.irred
  have hsup := GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component E a U hU w hw σ hc φ hφU
  let ι := {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}
  have hf' : ∀ (i : ι) (g : locU a w) (u : σ.V), i.1 ((σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) g u) =
      ((RU E a).comp (locU a w).subtype) g (i.1 u) := fun i g u => i.2.2 g u
  have hK : ∀ k ∈ {x : locU a w | (x : UA E a) ∈ L}, ((RU E a).comp (locU a w).subtype) k φ = (1 : ℂ) • φ :=
    fun k hk => by rw [one_smul]; exact hφ k.1 hk
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.SplitEigen.exists_eigen_of_mem_iSup (ι := ι) ((RU E a).comp (locU a w).subtype)
    (σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) hirr (fun i => i.1) hf'
    {x : locU a w | (x : UA E a) ∈ L} (fun _ => 1) φ hφ0 hK hsup
  refine (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 ?_, hv0⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hv ⟨x, hL hx⟩ hx
  rw [one_smul] at this
  exact this

theorem KGL_le_map {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) :
    GlobalTheory.LFun.KGL w a ≤ (intU a w).map (cLoc w) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  intro g hg
  have h1 : cLoc w ((e.symm g : locU a w) : UA E a) = g := by rw [← he, e.apply_symm_apply]
  exact ⟨(e.symm g).1, mem_intU_of (e.symm g).2 (by rw [h1]; exact hg), h1⟩

end GlobalTheory.Cong.AdaptLev

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupWeilElementCharacterKernel
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem exists_open_sub_charKer : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (n : ℕ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ V : Subgroup (Dec (F := E) A), IsOpen (V : Set (Dec (F := E) A)) ∧ commutator (Dec (F := E) A) ≤ V ∧ (⟨(g : G E Ω), Weil_le_Dec h g.2⟩ : Dec (F := E) A) ∈ V ∧ ∀ t : Ine (F := E) A, ∀ x ∈ V, (x : G E Ω) = t → ∀ j, ξ j (a (ineIncl h t)) = 1 := by
  intro Ω _ E _ _ _ _ w A h n ξ hξ a ha g hg
  let χ : Fin n → Weil h →* ℂˣ := fun j => (ξ j).comp a
  have hχ : ∀ j, IsSmooth (χ j) := fun j => ha.smooth (hξ j)
  let b := WDRep.ofChars h χ hχ
  have hy : AbW (WD.mk b) := by
    intro g₁ g₂
    rw [WD.charPol_mk, WD.lpDim_mk]
    have hc : ∀ i, χ i (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = 1 := fun i => by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm (χ i g₁ * χ i g₂),
        mul_inv_cancel_right, mul_inv_cancel]
    have e : b.ρ (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = 1 := by
      rw [WDRep.ofChars_ρ]
      refine LinearMap.ext fun v => funext fun i => ?_
      rw [diagEnd_apply, hc i, Units.val_one, one_mul, Module.End.one_apply]
    rw [e, LinearMap.charpoly_one]
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := GlobalTheory.AboveL.AbSub.exists_open_sub E Ω A w h (WD.mk b) hy g hg
  refine ⟨V, hV1, hV2, hV3, ?_⟩
  intro t x hx hxt j
  have hc := hV4 t x hx hxt
  rw [WD.charPol_mk, WD.lpDim_mk] at hc
  have h1 := GlobalTheory.AboveL.AbSub.eq_one_of_charpoly _ (b.semisimple _) hc
  have h2 := congrArg (fun f : Module.End ℂ (Fin n → ℂ) => f (Pi.single j 1) j) h1
  simp only [b, WDRep.ofChars_ρ, diagEnd_apply, Module.End.one_apply, Pi.single_eq_same, mul_one, χ,
    MonoidHom.comp_apply] at h2
  exact Units.ext h2

end GlobalTheory.RoadU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOtherSplitPlaceWithDistinctRealPlaceStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_other_split_place_with_distinct_real_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w₀ : HeightOneSpectrum (𝓞 E)), ∃ w₁ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₁ ∧ w₁.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) := by
  first | exact @GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne | exact GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne | (intros; apply GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionAbelianCompletion
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.AboveL.DecRes

variable {Ω F E : Type} [Field Ω] [Field F] [Field E] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]
  (A : ValuationSubring Ω)

def lift (h : G F Ω) (hh : ∀ x : E, h (algebraMap E Ω x) = algebraMap E Ω x) : G E Ω :=
  { (h : Ω ≃+* Ω) with commutes' := hh }

def resHom : Dec (F := E) A →* Dec (F := F) A where
  toFun g := ⟨AlgEquiv.restrictScalarsHom F (g : G E Ω), g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem resHom_injective : Function.Injective (resHom (F := F) (E := E) A) := by
  intro g g' hgg
  apply Subtype.ext
  ext z
  have := congrArg (fun k : Dec (F := F) A => (k : G F Ω) z) hgg
  exact this

theorem mem_map_iff (V : Subgroup (Dec (F := E) A)) (g : Dec (F := E) A) :
    resHom (F := F) A g ∈ V.map (resHom (F := F) (E := E) A) ↔ g ∈ V :=
  (Subgroup.mem_map_iff_mem (resHom_injective (E := E) A))

variable (hfix : ∀ g ∈ Dec (F := F) A, ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x)
include hfix

theorem resHom_surjective : Function.Surjective (resHom (F := F) (E := E) A) := by
  intro k
  exact ⟨⟨lift (k : G F Ω) (hfix _ k.2), k.2⟩, Subtype.ext (by ext z; rfl)⟩

theorem isOpen_map [FiniteDimensional F E] (V : Subgroup (Dec (F := E) A)) (hV : IsOpen (V : Set (Dec (F := E) A))) :
    IsOpen ((V.map (resHom (F := F) (E := E) A)) : Set (Dec (F := F) A)) := by
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp hV
  have h1 : (1 : Dec (F := E) A) ∈ V := V.one_mem
  have hU1 : (1 : G E Ω) ∈ U := by
    have : (1 : Dec (F := E) A) ∈ Subtype.val ⁻¹' U := by rw [hUV]; exact h1
    exact this
  obtain ⟨K, hK, hKU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp (hU.mem_nhds hU1)
  haveI := hK
  haveI : FiniteDimensional F (K.restrictScalars F) :=
    (Module.Finite.trans E K : Module.Finite F K)
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  have hO : IsOpen (Subtype.val ⁻¹' ((K.restrictScalars F).fixingSubgroup : Set (G F Ω)) : Set (Dec (F := F) A)) :=
    (IntermediateField.fixingSubgroup_isOpen (K.restrictScalars F)).preimage continuous_subtype_val
  refine Filter.mem_of_superset (hO.mem_nhds ((K.restrictScalars F).fixingSubgroup.one_mem)) ?_
  intro k hk
  obtain ⟨g, rfl⟩ := resHom_surjective (E := E) A hfix k
  refine ⟨g, ?_, rfl⟩
  have hgU : (g : G E Ω) ∈ U := by
    apply hKU
    intro z
    exact hk ⟨z.1, z.2⟩
  have : g ∈ Subtype.val ⁻¹' U := hgU
  rw [hUV] at this
  exact this

theorem commutator_le_map (V : Subgroup (Dec (F := E) A)) (hc : commutator (Dec (F := E) A) ≤ V) :
    commutator (Dec (F := F) A) ≤ V.map (resHom (F := F) (E := E) A) := by
  have hs := resHom_surjective (E := E) A hfix
  rw [commutator_def, ← Subgroup.map_top_of_surjective _ hs, ← Subgroup.map_commutator]
  exact Subgroup.map_mono (by rw [← commutator_def]; exact hc)

end GlobalTheory.AboveL.DecRes

namespace GlobalTheory.AboveL

open GlobalTheory.AboveL.DecRes in

theorem exists_cm_solvDisj_dec_eq : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ g ∈ Dec (F := maximalRealSubfield E) A, ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x) → ∀ V : Subgroup (Dec (F := E) A), IsOpen (V : Set (Dec (F := E) A)) → commutator (Dec (F := E) A) ≤ V → ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ ∀ g : Dec (F := E) A, (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ↔ g ∈ V := by
  intro Ω _ E _ _ _ _ _ A w h hfix V hVo hVc N hNo
  haveI : IsAlgClosure (maximalRealSubfield E) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩
  obtain ⟨n, hn, hnv⟩ := (Formalism.MainNotions.V.Pf.ShaCmp.exists_over_iff (K := E) A).mp ⟨w, h⟩
  obtain ⟨v, hv⟩ := (Formalism.MainNotions.V.Pf.ShaCmp.exists_over_iff (K := maximalRealSubfield E) A).mpr ⟨n, hn, hnv⟩
  obtain ⟨T, hvT, hT⟩ := GlobalTheory.T.exists_cmField_lift_disjoint_of_real_solvable Ω E v N hNo
  obtain ⟨F₁, hfin, hab, hreal, hdecF, hsplit⟩ := GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion Ω (maximalRealSubfield E) A v hv
    (V.map (resHom (F := maximalRealSubfield E) (E := E) A)) (isOpen_map A hfix V hVo)
    (commutator_le_map A hfix V hVc) T hvT
  have hsolv : IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) :=
    isSolvable_of_comm fun a b => hab.toIsMulCommutative.is_comm.comm a b
  obtain ⟨M, i1, i2, i3, i4, i5, i6, i7, hSD, hM, -⟩ :=
    hT F₁ hfin hab.toIsGalois hsolv hreal hsplit
  refine ⟨M, i1, i2, i3, i4, i5, i6, i7, hSD, fun g => ?_⟩
  rw [hM (g : G E Ω), ← mem_map_iff (F := maximalRealSubfield E) A V g, ← hdecF, IntermediateField.mem_fixingSubgroup_iff]
  rfl

end GlobalTheory.AboveL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedResiduesInFramesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vector_prescribed_residues_in_frames : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ),
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) := by
  first | exact @GlobalTheory.CRTFrame.approx_frames_target | exact GlobalTheory.CRTFrame.approx_frames_target | (intros; apply GlobalTheory.CRTFrame.approx_frames_target <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorSameCouplingCosetAllBadPrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vector_sameCouplingCoset_all_bad_primes : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (fr : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n)) (y0 : rowSG Pr sel mu → Sp X.E n), ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((fr P).symm y) (y0 P) := by
  first | exact @GlobalTheory.FrameCongApprox.exists_sameCoset | exact GlobalTheory.FrameCongApprox.exists_sameCoset | (intros; apply GlobalTheory.FrameCongApprox.exists_sameCoset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FieldPointLiftsGenericFibre
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.SatSupp.hasSupport_of_hasSatGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 1 ≤ n → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∃ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (ϖ : (w.adicCompletion E)ˣ), HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep (chars ξ hξ) ∧ (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) ∧ Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) ∧ B = Finset.univ.val.map fun j => ξ j ϖ := by
  intro E _ _ n _ w σ B hB
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_ringHom (algebraMap E (w.adicCompletion E)).injective
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  have hϖ : Valued.v ((GroundTheory.Global.uniformizerUnit w : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := by
    simpa using GroundTheory.Global.valued_uniformizerUnit_zpow w 1
  refine ⟨fun j => GlobalTheory.SmGL.unrChar _ (α j),
    fun j => GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_unrChar _ (α j)),
    GroundTheory.Global.uniformizerUnit w, ?_, ?_, hϖ, ?_⟩
  · let π : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)) := ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩
    exact (GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries _ n _ _ π hα.2.2).of_equiv
      (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  · intro j x hx
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion, hx]
    simp
  · rw [← hαB]
    congr 1
    funext j
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion, hϖ]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumInvarianceSupportTransportFramesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_invariance_support_transport_frames : ∀ {D : D7} {X : Fields} (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (S : Finset (HeightOneSpectrum (𝓞 X.E))) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E)) (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) (cA cB : ℕ), 0 < cA → 0 < cB → ∀ (Ξ : HomE X.E a b → X.K), (∀ P ∈ S, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E)) → (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) → (∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) → DatLoc D cc (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (cA * cB) ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E))) (fun z => s.σ₀ (Ξ (seamHom s (inFr f f' z)))) ∧ ∀ z, s.σ₀ (Ξ (seamHom s (inFr f f' z))) ≠ 0 → z ∈ divLat (cA * cB) (homAt (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))) := by
  first | exact @GlobalTheory.DatTransport.datLoc_seam_inFr | exact GlobalTheory.DatTransport.datLoc_seam_inFr | (intros; apply GlobalTheory.DatTransport.datLoc_seam_inFr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharacterNormOneEqInfinityTypeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelChainCharacter_normOne_eq_infinityType : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧ ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 → ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 = ratId D.host.F D.host.E z → (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ) := by
  first | exact @GlobalTheory.TwV.mt_ratId | exact GlobalTheory.TwV.mt_ratId | (intros; apply GlobalTheory.TwV.mt_ratId <;> assumption)
end

