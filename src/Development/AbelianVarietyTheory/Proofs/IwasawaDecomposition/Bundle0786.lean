import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0768
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0522
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBaseStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftCharacters_agree_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh → LevSame z Wt' R' := by
  first | exact @GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf | exact GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf | (intros; apply GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedConstructionStatesCharactersAgree
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.LevExt

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove

theorem frat_delAt_heq {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'} (hP : B'.toPre = B.toPre)
    {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) (l : ℕ) :
    HEq ((Top.Fr.at a'.st f').delAt l) ((Top.Fr.at a.st f).delAt l) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl ((Top.Fr.at a.st f).delAt l)) :))

set_option maxHeartbeats 4000000 in

theorem chars_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Chars (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have hP : B'.toPre = B.toPre := l.enl.1
  have hC : x.m.z.R.toLevCh.C = Top.Fr.at (w.st x.o.Z) f := x.m.z.lev.C.trans (by rw [w.C_eq])
  have hC' : x'.m.z.R.toLevCh.C = Top.Fr.at (w'.st x'.o.Z) f' := x'.m.z.lev.C.trans (by rw [w'.C_eq])
  have hs := x.m.z.lev.is
  have hs' := x'.m.z.lev.is
  have hm : (Dof x').R.m = (Dof x).R.m := by
    exact congrArg (fun p : Pre => p.R.m) hP
  have hmu0 : ∀ (i : Fin (Dof x).R.m) (i' : Fin (Dof x').R.m), (i : ℕ) = i' →
      HEq (x'.m.z.R.toLevCh.C.mu0 i') (x.m.z.R.toLevCh.C.mu0 i) := by
    intro i i' h
    rw [hC, hC']
    exact hermitianCodeCharFrame_referenceCharacter_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr h
  refine ⟨?_, fun j => ?_, fun j j' h => ?_, fun l0 => ?_⟩
  · have heta : HEq x'.m.z.R.toLevCh.C.eta x.m.z.R.toLevCh.C.eta := by
      rw [hC, hC']
      exact frat_eta_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr
    exact (idc_heq (a := x.o.Z) (a' := x'.o.Z) hP heta hs.eta hs'.eta).symm
  · let j' : Fin (Dof x').R.m := ⟨j, lt_of_lt_of_eq j.2 hm.symm⟩
    exact (idc_heq (a := x.o.Z) (a' := x'.o.Z) hP (hmu0 j j' rfl) (hs.mu0 j) (hs'.mu0 j')).symm
  · exact (hmu0 j j' h).symm
  · show HEq (x.m.z.R.toLevCh.C.delAt l0) (x'.m.z.R.toLevCh.C.delAt l0)
    rw [hC, hC']
    exact (frat_delAt_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr l0).symm

end GlobalTheory.HeightCounting.SerMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCoefficientFieldFiniteGroupEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove.Ids

theorem coeffF_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H'}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l'}
    (hH : H' = H) (hl : HEq l' l) (hc : HEq c' c) : c'.F = c.F := by
  subst hH
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  rfl

theorem gc_equiv {B B' : Base} {px : PreX B.toPre} {px' : PreX B'.toPre} (h : Enl B B') (hp : HEq px' px) :
    ∃ γ : GlobalTheory.Mem.R3.Gc B px ≃* GlobalTheory.Mem.R3.Gc B' px', ∀ u, HEq (γ u) u := by
  obtain ⟨e, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e
  subst e
  cases hp
  exact ⟨MulEquiv.refl _, fun _ => HEq.rfl⟩

theorem dat_F_eq {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (h : Enl B B') (e : ExtN z z') : z'.core.Q.c.F = z.core.Q.c.F := by
  have hH := e.H
  have hl := e.l
  have hc := e.c
  clear e
  obtain ⟨e0, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e0
  subst e0
  exact coeffF_eq (eq_of_heq hH) hl hc

theorem field_group_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∃ (eK : ↥(sideAt x g hg a).core.Q.c.F ≃+* ↥(sideAt x' g' hg' a').core.Q.c.F) (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ y, ((eK y : ↥(sideAt x' g' hg' a').core.Q.c.F) : ℂ) = (y : ℂ)) ∧ ∀ u, HEq (γ u) u := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have hc := l.extN.c
  have hH := l.extN.H
  have hl := l.extN.l
  show ∃ (eK : x.m.z.core.Q.c.F ≃+* x'.m.z.core.Q.c.F) (γ : GlobalTheory.Mem.R3.Gc B w.px ≃* GlobalTheory.Mem.R3.Gc B' w'.px), _
  obtain ⟨γ, hγ⟩ := gc_equiv l.enl l.px
  have hF : x'.m.z.core.Q.c.F = x.m.z.core.Q.c.F := dat_F_eq (z := datAt x g) (z' := datAt x' g') l.enl l.extN
  exact ⟨(IntermediateField.equivOfEq hF.symm).toRingEquiv, γ, fun y => rfl, hγ⟩

end GlobalTheory.HeightCounting.SerMove.Ids
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCorrespondingFormsSameAdelicFunction
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open GlobalTheory.Mem.R3.Tr GlobalTheory.TwInputs.Move

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove.ReadMove

set_option maxHeartbeats 4000000 in

theorem sameMap_of_heq {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt}
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (l : HEq M'.lam M.lam) (e : HEq M'.ε M.ε)
    (g : HEq M'.fr M.fr) (X : HMod (Formalism.IndefR.Mult.MMap M)) (X' : HMod (Formalism.IndefR.Mult.MMap M')) (hX : HEq X' X)
    (u : X.H) (u' : X'.H) (hu : HEq u' u) : SameMap (X.e u) (X'.e u') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  have e' : X' = X := eq_of_heq hX
  subst e'
  have e'' : u' = u := eq_of_heq hu
  subst e''
  intro v v' hv y y' hy
  cases hy
  have : v' = v := funext fun τ => Subtype.ext (eq_of_heq (hv τ τ HEq.rfl)).symm
  subst this
  rfl

set_option maxHeartbeats 4000000 in

theorem read_same {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (hE : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hx : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) :
    ∀ (σ : (w.st Z).toD7.what₂.LL →+* ℂ) (σ' : (w'.st Z').toD7.what₂.LL →+* ℂ), σ = (w.st Z).toD7.what₂.embLL →
      σ' = (w'.st Z').toD7.what₂.embLL →
      SameMap ((z.R.HW j σ).e ((z.R.FW j).j σ x)) ((z'.R.HW j' σ').e ((z'.R.FW j').j σ' x')) := by
  rintro σ σ' rfl rfl
  obtain ⟨a, b, c, d, l, e, g, -, hW, -, -⟩ := hE.MW j j' hj
  exact sameMap_of_heq q j j' hj _ _ a b c d l e g _ _ hW _ _
    (GlobalTheory.Mem.R3.LiftRead.read_extN q hE j j' hj φ hφ x x' hx)

end GlobalTheory.HeightCounting.SerMove.ReadMove

namespace GlobalTheory.HeightCounting.SerMove

set_option maxHeartbeats 4000000 in

theorem reading_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → GlobalTheory.TwInputs.Move.SameMap (GlobalTheory.TwInputs.Move.evidence (sideAt x g hg a) j y) (GlobalTheory.TwInputs.Move.evidence (sideAt x' g' hg' a') j' y') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' j j' hj y y' hy
  exact ReadMove.read_same l.enl.1 l.extN j j' hj ι l.cp.embLL y y' hy _ _ (GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x g hg a))
    (GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x' g' hg' a'))

end GlobalTheory.HeightCounting.SerMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFiniteGroupCharactersCorrespond
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr

theorem chi_link_side : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ u : (sideAt x g hg a).Γ, ((((sideAt x' g' hg' a').R.FW j').chi (γ u) : (Dof x').what₂.LLˣ) : (Dof x').what₂.LL) = ι ((((sideAt x g hg a).R.FW j).chi u : (Dof x).what₂.LLˣ) : (Dof x).what₂.LL) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' γ hγ j j' hj u
  apply RingHom.injective (Dof x').what₂.embLL
  have hC : x.m.z.R.toLevCh.C.mu0 j = f.mu0 j := by
    rw [x.m.z.lev.C, w.C_eq]; rfl
  have hC' : x'.m.z.R.toLevCh.C.mu0 j' = f'.mu0 j' := by
    rw [x'.m.z.lev.C, w'.C_eq]; rfl
  refine (x'.m.z.pins.char.base.grp.chiW j' (γ u)).trans
    (Eq.trans ?_ ((l.cp.embLL _).trans (x.m.z.pins.char.base.grp.chiW j u)).symm)
  exact GlobalTheory.Mem.R3.ChiExt.prod_eq l.enl.1 l.fr l.px j j' hj l.extN.Pg x.m.z.R.eG x'.m.z.R.eG l.extN.eG
    (x.m.z.R.chi ((j : ℕ) + 1)) (x'.m.z.R.chi ((j' : ℕ) + 1))
    (fun PP hP => hC ▸ x.m.z.lev.is.chi j PP hP) (fun PP hP => hC' ▸ x'.m.z.lev.is.chi j' PP hP) u (γ u) (hγ u)

end GlobalTheory.HeightCounting.SerMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFiniteGroupsLevelsCorrespond
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove.GrpsPf

theorem eG_heq (B B' : Base) (h : B'.toPre = B.toPre) (px : PreX B.toPre) (px' : PreX B'.toPre) (hp : HEq px' px)
    (Pg : Finset (Formalism.L2.DIV.Pl B.host.E)) (Pg' : Finset (Formalism.L2.DIV.Pl B'.host.E)) (hPg : HEq Pg' Pg)
    (eG : Gc B px ≃* Formalism.L2.DIV.G0 Pg B.R.r) (eG' : Gc B' px' ≃* Formalism.L2.DIV.G0 Pg' B'.R.r) (he : HEq eG' eG)
    (u : Gc B px) (u' : Gc B' px') (hu : HEq u' u) : HEq (eG u) (eG' u') := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h px px' hp Pg Pg' hPg eG eG' he u u' hu ⊢
  subst h
  cases hp
  cases hPg
  cases he
  cases hu
  rfl

end GlobalTheory.HeightCounting.SerMove.GrpsPf

namespace GlobalTheory.HeightCounting.SerMove.GrpsPf

theorem cG_heq (B B' : Base) (h : B'.toPre = B.toPre) (Pg : Finset (Formalism.L2.DIV.Pl B.host.E)) (Pg' : Finset (Formalism.L2.DIV.Pl B'.host.E))
    (hPg : HEq Pg' Pg) (Q Q' : Fin 2 → Type) (hQ : Q = Q') (pw : ∀ k, Q k → Formalism.L2.DIV.Pl B.host.E)
    (pw' : ∀ k, Q' k → Formalism.L2.DIV.Pl B'.host.E) (hpw : HEq pw pw')
    (c : Formalism.L2.DIV.G0 Pg B.R.r ≃* ∀ kv : (Σ k : Fin 2, Q k), GL (Fin B.R.r) (ZMod (B.host.g kv.1)))
    (c' : Formalism.L2.DIV.G0 Pg' B'.R.r ≃* ∀ kv : (Σ k : Fin 2, Q' k), GL (Fin B'.R.r) (ZMod (B'.host.g kv.1)))
    (hc : ∃ (plg : (Σ k : Fin 2, Q k) ≃ Pg) (iso : ∀ kv, ZMod (B.host.g kv.1) ≃+* Formalism.L2.DIV.kP (plg kv).1),
      (∀ kv, ((plg kv : Pg) : Formalism.L2.DIV.Pl B.host.E) = pw kv.1 kv.2) ∧
      ∀ y kv, y (plg kv) = Formalism.UG.bc (iso kv : ZMod (B.host.g kv.1) →+* Formalism.L2.DIV.kP (plg kv).1) (c y kv))
    (hc' : ∃ (plg : (Σ k : Fin 2, Q' k) ≃ Pg') (iso : ∀ kv, ZMod (B'.host.g kv.1) ≃+* Formalism.L2.DIV.kP (plg kv).1),
      (∀ kv, ((plg kv : Pg') : Formalism.L2.DIV.Pl B'.host.E) = pw' kv.1 kv.2) ∧
      ∀ y kv, y (plg kv) = Formalism.UG.bc (iso kv : ZMod (B'.host.g kv.1) →+* Formalism.L2.DIV.kP (plg kv).1) (c' y kv)) :
    HEq c c' := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h Pg Pg' hPg pw pw' hpw c c' hc hc' ⊢
  subst h
  cases hPg
  subst hQ
  cases hpw
  apply heq_of_eq
  obtain ⟨p, i, h1, h2⟩ := hc
  obtain ⟨p', i', h1', h2'⟩ := hc'
  obtain rfl : p = p' := Equiv.ext fun kv => Subtype.ext ((h1 kv).trans (h1' kv).symm)
  refine MulEquiv.ext fun y => funext fun kv => ?_
  have h3 := (h2 y kv).symm.trans (h2' y kv)
  refine Units.ext (Matrix.ext fun a b => (i' kv).injective ?_)
  have h4 : (i kv) ((c y kv).1 a b) = (i' kv) ((c' y kv).1 a b) := congrArg (fun m : GL _ _ => m.1 a b) h3
  have h5 : (i kv) ((c y kv).1 a b) = (i' kv) ((c y kv).1 a b) :=
    RingHom.congr_fun (Subsingleton.elim (i kv).toRingHom (i' kv).toRingHom) _
  exact h5.symm.trans h4

end GlobalTheory.HeightCounting.SerMove.GrpsPf

namespace GlobalTheory.HeightCounting.SerMove.GrpsPf

theorem cG_read {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : TwDat X.B} {Wt : Set X.B.places.Pl}
    (z : Dat X I hX T Wt) :
    ∃ (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ z.R.Pg) (iso : ∀ kv, ZMod (X.toD7.host.g kv.1) ≃+* Formalism.L2.DIV.kP (plg kv).1),
      (∀ kv, ((plg kv : z.R.Pg) : Formalism.L2.DIV.Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧
      ∀ y kv, y (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* Formalism.L2.DIV.kP (plg kv).1) (z.cG y kv) := by
  obtain ⟨plg, iso, h1, -, -, h4⟩ := z.pins.keep.grp
  refine ⟨plg, iso, h1, fun y kv => ?_⟩
  obtain ⟨u, rfl⟩ := z.R.eG.surjective y
  exact h4 u kv

theorem grps_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → Grps (sideAt x g hg a) (sideAt x' g' hg' a') ι γ := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' γ hγ
  refine ⟨fun u => ?_, ?_, fun u => ?_, fun u u' hu => ?_⟩
  · exact eG_heq B B' l.enl.1 w.px w'.px l.px x.m.z.R.Pg x'.m.z.R.Pg l.extN.Pg x.m.z.R.eG x'.m.z.R.eG l.extN.eG u (γ u) (hγ u)
  · exact cG_heq B B' l.enl.1 x.m.z.R.Pg x'.m.z.R.Pg l.extN.Pg (Dof x).nd.PlG (Dof x').nd.PlG (eq_of_heq l.gal.gal.PlG)
      (Dof x).naut.plGw (Dof x').naut.plGw l.gal.pl x.m.z.cG x'.m.z.cG (cG_read x.m.z) (cG_read x'.m.z)
  · exact (GlobalTheory.Mem.R3.LevBC.lev_bc B B' l.enl.1 w.px w'.px l.px w.I w'.I w.ok w'.ok ι l.cp.embLL u (γ u) (hγ u)).1.symm
  · have h : HEq (u' : (sideAt x' g' hg' a').Γ) (u : (sideAt x g hg a).Γ) := hu ▸ hγ u
    exact (GlobalTheory.Mem.R3.LevBC.lev_bc B B' l.enl.1 w.px w'.px l.px w.I w'.I w.ok w'.ok ι l.cp.embLL u.1 u'.1 h).2 u.2 u'.2

end GlobalTheory.HeightCounting.SerMove.GrpsPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFramesLatticesModelsAgree
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.SerMove.FrameValuesAtLevel
variable {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}

set_option maxHeartbeats 4000000 in

theorem ΛV_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.ΛV i) (z'.R.ΛV i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.ΛV) i).symm

set_option maxHeartbeats 4000000 in

theorem ΛW_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.ΛW i) (z'.R.ΛW i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.ΛW) i).symm

set_option maxHeartbeats 4000000 in

theorem βV_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.βV i) (z'.R.βV i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.βV) i).symm

set_option maxHeartbeats 4000000 in

theorem βW_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.βW i) (z'.R.βW i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.βW) i).symm

set_option maxHeartbeats 4000000 in

theorem sameVec_gen (q : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → Formalism.BasicNotions.TH.SPar} {S' : (w'.st Z').toD7.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (M : Formalism.IndefR.Mult.DSModel (Formalism.IndefR.Links.Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Formalism.IndefR.Links.Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (g : HEq M'.fr M.fr)
    (v : M.Vec) (v' : M'.Vec) (hv : HEq v' v) : GlobalTheory.TwInputs.Move.SameVec v v' := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d g
  cases a; cases b; cases c; cases d; cases g
  intro τ τ' hτ
  cases hτ
  have e := eq_of_heq hv
  subst e
  rfl

set_option maxHeartbeats 4000000 in

theorem v₀_of_extN (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    GlobalTheory.TwInputs.Move.SameVec (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) (z'.geo.v₀ i' (w'.st Z').toD7.what₂.embLL) :=
  have h := hx.MW i i' hi
  sameVec_gen q i i' hi _ _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.2.1 _ _ h.2.2.2.2.2.2.2.2.2.1

end GlobalTheory.HeightCounting.SerMove.FrameValuesAtLevel

namespace GlobalTheory.HeightCounting.SerMove

set_option maxHeartbeats 4000000 in

theorem frames_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Frames (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have q : B'.toPre = B.toPre := l.enl.1
  have hx := l.extN
  refine ⟨hx.Pg.symm, hx.ψ.symm, hx.θ.symm, fun j j' h => FrameValuesAtLevel.ΛV_at q hx j j' h, fun j j' h => FrameValuesAtLevel.ΛW_at q hx j j' h,
    fun j j' h => FrameValuesAtLevel.βV_at q hx j j' h, fun j j' h => FrameValuesAtLevel.βW_at q hx j j' h,
    fun j j' h => ((hx.BV j j' h).2.2.2.2.2).symm, fun j j' h => ((hx.BV j j' h).2.2.1).symm, fun j j' h => ?_, fun j j' h => ?_⟩
  · show GlobalTheory.TwInputs.Move.SameModel (x.m.z.R.MW j (Formalism.IndefR.Links.sg0 (Dof x) (sideAt x g hg a).A3.A)) (x'.m.z.R.MW j' (Formalism.IndefR.Links.sg0 (Dof x') (sideAt x' g' hg' a').A3.A))
    rw [GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x g hg a), GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x' g' hg' a')]
    have m := hx.MW j j' h
    exact ⟨m.1.symm, m.2.1.symm, m.2.2.1.symm, m.2.2.2.1.symm, m.2.2.2.2.1.symm, m.2.2.2.2.2.1.symm, m.2.2.2.2.2.2.1.symm⟩
  · show GlobalTheory.TwInputs.Move.SameVec (g.v₀ j (Formalism.IndefR.Links.sg0 (Dof x) (sideAt x g hg a).A3.A)) (g'.v₀ j' (Formalism.IndefR.Links.sg0 (Dof x') (sideAt x' g' hg' a').A3.A))
    rw [GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x g hg a), GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x' g' hg' a')]
    exact FrameValuesAtLevel.v₀_of_extN q hx j j' h

end GlobalTheory.HeightCounting.SerMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalRepresentationInputsImplyStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_representation_inputs_imply : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.PseudoCoefficientUpq → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.Published.LanglandsClassification → GlobalTheory.Published.LabesseWaldspurger → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), MultQ (prmR N S Γ) := by
  first | exact @GlobalTheory.Mem.Top.Bl.MultQClose.multQ_prmR | exact GlobalTheory.Mem.Top.Bl.MultQClose.multQ_prmR | (intros; apply GlobalTheory.Mem.Top.Bl.MultQClose.multQ_prmR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormPiecesInEveryCellConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marked_form_pieces_in_every_cell_cone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀),
  IsCell H.bar φ δ₀ → ∀ t : Fin m₀ → ℝ, (∀ i, 0 ≤ t i) →
  ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] (π : X₀ →ₗ[𝓞 E] Y), Function.Surjective π → ∀ (τ : 𝓞 E ≃+* 𝓞 E) (f : X →+ Y), τ H.w0 = H.w0 →
    Function.Surjective f → (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
  ∀ u : Fin m₀ → LinearMap.BilinForm ℤ Y,
    (∀ i, 0 < t i → pull π (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms H.bar X ∧ ∀ y, 0 ≤ pullAdd f (u i) y y) →
  ∀ β : LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (pullAdd f (u i)) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  ∀ i, 0 < t i → InRCone δ (pullAdd f (u i)) := by
  first | exact @GlobalTheory.PolFan.OrbMark.inRCone_pullAdd_of_isCell | exact GlobalTheory.PolFan.OrbMark.inRCone_pullAdd_of_isCell | (intros; apply GlobalTheory.PolFan.OrbMark.inRCone_pullAdd_of_isCell <;> assumption)
end

