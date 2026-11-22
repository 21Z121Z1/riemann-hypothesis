import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0528
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanCw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2Transport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0768
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesGeometricActionsCorrespond
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
open GlobalTheory.Mem.R3.Tr

noncomputable section

section General
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.HeightCounting.SerMove.RhoLink

open Formalism.IndefR.FWT GlobalTheory.Mem.R3.GoodBC

theorem rel_of_span {LL LL' : Type} [Field LL] [Field LL'] (φ : LL →+* LL') {n n' : ℕ} (hn : n = n')
    (S : Set (Fin n → LL)) (hS : Submodule.span LL S = ⊤)
    (ρ : (Fin n → LL) →ₗ[LL] (Fin n → LL)) (ρ' : (Fin n' → LL') →ₗ[LL'] (Fin n' → LL'))
    (h : ∀ s ∈ S, ∀ (x' : Fin n' → LL'), (∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (s k)) →
      ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → ρ' x' k' = φ (ρ s k))
    (x : Fin n → LL) (x' : Fin n' → LL') (hx : ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)) :
    ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → ρ' x' k' = φ (ρ x k) := by
  subst hn
  have hx' : x' = cw φ x := funext fun k => hx k k rfl
  subst hx'
  have key : ∀ y ∈ Submodule.span LL S, ρ' (cw φ y) = cw φ (ρ y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem s hs =>
      funext k
      exact h s hs (cw φ s) (fun k k' hk => by rw [Fin.ext hk]; rfl) k k rfl
    | zero => rw [cw_zero, map_zero, map_zero, cw_zero]
    | add a b _ _ ha hb => rw [cw_add, map_add, ha, hb, map_add, cw_add]
    | smul c a _ ha => rw [cw_smul, LinearMap.map_smul, ha, LinearMap.map_smul, cw_smul]
  intro k k' hk
  rw [← Fin.ext hk]
  exact congrFun (key x (hS ▸ Submodule.mem_top)) k

variable {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
  {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Wt' : Set B'.places.Pl}

set_option maxHeartbeats 2000000 in

theorem cusp_gen (hB : B'.toPre = B.toPre) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hx : ExtN z z')
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j') :
    z'.core.R ((j' : ℕ) + 1) = z.core.R ((j : ℕ) + 1) ∧
    (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)), HEq r' r → (r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n ↔ r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) ∧
    (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)) (h : r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n) (h' : r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n), HEq r' r →
      HEq (⟨r', h'⟩ : z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n) (⟨r, h⟩ : z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have e : j' = j := Fin.ext hj.symm
  subst e
  obtain ⟨h1, h2, h3⟩ := hx.κ j' j' rfl
  have e1 : (z'.geo.κ j').aP = (z.geo.κ j').aP := eq_of_heq h1
  have e2 : (z'.geo.κ j').aM = (z.geo.κ j').aM := eq_of_heq h2
  have hw : Formalism.L2.Pj.wtA (z'.geo.κ j') = Formalism.L2.Pj.wtA (z.geo.κ j') := by
    funext x
    unfold Formalism.L2.Pj.wtA
    rw [e1, e2]
    rfl
  obtain ⟨hR, hm, hs⟩ := GlobalTheory.Mem.R3.CuspExt.cusp_heq (r := (w.st Z).toD7.R.r) (eq_of_heq hx.H) hx.l hx.c hx.Dw hx.Xo hx.U hw h3 ((j' : ℕ) + 1)
  exact ⟨hR, hm, hs⟩

set_option maxHeartbeats 2000000 in

theorem act_gen (hB : B'.toPre = B.toPre) (hf : HEq f' f) (hp : HEq w'.px w.px) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hx : ExtN z z')
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px) (hg : HEq g' g)
    (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)) (hr : HEq r' r) :
    HEq (Formalism.L2.Pj.actLev z'.core.Q.c (z'.geo.O j').lev2 g' r') (Formalism.L2.Pj.actLev z.core.Q.c (z.geo.O j).lev2 g r) := by
  have hA := GlobalTheory.OneMapAllCompare.second_level_eq_one (z.geo.pins j).2.cov ()
  have h : GlobalTheory.Mem.R3.ActExt.LevB _ j z.R.Pg z.R.βW z.R.eG (z.core.iota _) _ _ (z.geo.O j).lev := (z.geo.pins j).2.lift.lev
  have h' : GlobalTheory.Mem.R3.ActExt.LevB _ j' z'.R.Pg z'.R.βW z'.R.eG (z'.core.iota _) _ _ (z'.geo.O j').lev := (z'.geo.pins j').2.lift.lev
  have hU := letI := z.alg; GlobalTheory.LevelUnique.levUnique _ _ _ _ _ z.core z.R.toRealDat z.lev.is z.geo.fw.laws ((z.geo.pins j).2.tuple ()).half.1 j
  have e1 := hx.H
  have e2 := hx.l
  have e3 := hx.c
  have e4 := hx.Dw
  have e5 := hx.Xo
  have e6 := hx.iota
  have e7 := hx.Pg
  have e8 := hx.βW
  have e9 := hx.eG
  clear hx
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hB
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  obtain ⟨j', hj'⟩ := j'
  dsimp only at hj
  subst hj
  exact GlobalTheory.Mem.R3.ActExt.act_heq (w.st Z).toD7 j ((j : ℕ) + 1) e1 e2 e3 e4 e5 e6 e7 e8 e9 hA hU h h' g g' hg r r' hr

set_option maxHeartbeats 4000000 in

theorem rho_gen     (hB : B'.toPre = B.toPre) (hf : HEq f' f) (hpx : HEq w'.px w.px)
    {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hx : ExtN z z')
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL) (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px) (hg : HEq g' g)
    (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hxx' : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) :
    ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → (z'.R.toRealDat.FW j').ρ g' x' k' = φ ((z.R.toRealDat.FW j).ρ g x k) := by
  obtain ⟨hR, hmem, hsub⟩ := cusp_gen hB z z' hx j j' hj
  have hact := act_gen hB hf hpx z z' hx j j' hj
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P => P.R.m) hB
  have hn : z'.R.nW j' = z.R.nW j := nat_heq_app hm z.R.nW z'.R.nW hx.nW j j' hj
  obtain ⟨eG, heG⟩ := gc_iso (w.st Z).B (w'.st Z').B hB w.px w'.px hpx
  have hF : ∀ f f', HEq f' f → ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' →
      ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) k' =
        φ (((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) k) :=
    fun f f' h k k' hk => (w'.st Z').toD7.what₂.embLL.injective ((hx.forms j j' hj f f' h k k' hk).trans (hφ _).symm)
  have hkeep : ActKeeps (κ := z'.geo.κ) z'.geo.O j' ↔ ActKeeps (κ := z.geo.κ) z.geo.O j := by
    constructor
    · intro hk g0 f0 hf0
      have hr : HEq (cast hR.symm f0) f0 := cast_heq _ _
      have h1 := hk (eG g0) (cast hR.symm f0) ((hmem _ _ hr).2 hf0)
      exact (hmem _ _ (hact g0 (eG g0) (heG g0) f0 _ hr)).1 h1
    · intro hk g0' f0' hf0'
      have hr : HEq f0' (cast hR f0') := (cast_heq _ _).symm
      have hg0 : HEq g0' (eG.symm g0') := by
        have := heG (eG.symm g0')
        rwa [MulEquiv.apply_symm_apply] at this
      have h1 := hk (eG.symm g0') (cast hR f0') ((hmem _ _ hr).1 hf0')
      exact (hmem _ _ (hact _ _ hg0 _ _ hr)).2 h1
  by_cases hk : ActKeeps (κ := z.geo.κ) z.geo.O j
  · have A := (z.geo.rhoGeo j).1 hk
    have A' := (z'.geo.rhoGeo j').1 (hkeep.2 hk)
    have hS : Submodule.span (w.st Z).toD7.what₂.LL ((z.R.FW j).WK : Set (Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL)) = ⊤ := by
      obtain ⟨m, b, hb, -, -, -, hsp⟩ := z.geo.fw.ks j
      exact top_unique (hsp ▸ Submodule.span_mono (Set.range_subset_iff.2 hb))
    refine rel_of_span φ hn.symm _ hS ((z.R.toRealDat.FW j).ρ g) ((z'.R.toRealDat.FW j').ρ g') ?_ x x' hxx'
    intro s hs y' hy' k k' hk'
    obtain ⟨f0, hf0⟩ : ∃ f0, f0 = (z.geo.fw.e j).symm ⟨s, hs⟩ := ⟨_, rfl⟩
    have hs0 : ((z.geo.fw.e j f0 : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = s := by
      rw [hf0, LinearEquiv.apply_symm_apply]
    have hr : HEq (cast hR.symm (f0 : z.core.R ((j : ℕ) + 1))) (f0 : z.core.R ((j : ℕ) + 1)) := cast_heq _ _
    obtain ⟨f0', hf0'⟩ : ∃ f0' : z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n,
        (f0' : z'.core.R ((j' : ℕ) + 1)) = cast hR.symm (f0 : z.core.R ((j : ℕ) + 1)) :=
      ⟨⟨_, (hmem _ _ hr).2 f0.2⟩, rfl⟩
    have hff : HEq f0' f0 := hsub f0.1 f0'.1 f0.2 f0'.2 (hf0' ▸ hr)
    have hy : ((z'.geo.fw.e j' f0' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) = y' := by
      funext k1'
      have e1 := hF f0 f0' hff (Fin.cast hn k1') k1' rfl
      rw [e1, hs0, hy' (Fin.cast hn k1') k1' rfl]
    obtain ⟨h1, e1⟩ := A g f0
    obtain ⟨h1', e1'⟩ := A' g' f0'
    have hh := hsub _ _ h1 h1' (hact g g' hg _ _ (hf0' ▸ hr))
    rw [← hy, ← e1', hF _ _ hh k k' hk', e1, hs0]
  · have e0 : (z.R.toRealDat.FW j).ρ g = 1 := (z.geo.rhoGeo j).2 hk g
    have e0' : (z'.R.toRealDat.FW j').ρ g' = 1 := (z'.geo.rhoGeo j').2 (fun h => hk (hkeep.1 h)) g'
    intro k k' hk'
    rw [e0, e0', Module.End.one_apply, Module.End.one_apply]
    exact hxx' k k' hk'

end GlobalTheory.HeightCounting.SerMove.RhoLink
end General

theorem GlobalTheory.HeightCounting.SerMove.rho_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → ∀ (u : (sideAt x g hg a).Γ) (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → ((sideAt x' g' hg' a').R.FW j').ρ (γ u) y' k' = ι (((sideAt x g hg a).R.FW j).ρ u y k) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' γ hγ j j' hj y y' hy u k k' hk
  exact GlobalTheory.HeightCounting.SerMove.RhoLink.rho_gen l.enl.1 l.fr l.px (datAt x g) (datAt x' g') l.extN j j' hj ι l.cp.embLL u (γ u) (hγ u) y y' hy k k' hk

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesRationalFormsCorrespondCoordinatewis
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove

theorem exists_addEquiv_of_coord {L L' R R' : Type} [Field L] [Field L'] [Semiring R] [Semiring R'] {n n' : ℕ}
    [Module R (Fin n → L)] [Module R' (Fin n' → L')] (hn : n = n') (W : Submodule R (Fin n → L))
    (W' : Submodule R' (Fin n' → L')) (ι : L →+* L')
    (h1 : ∀ y : W, ∃ y' : W', ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → y'.1 k' = ι (y.1 k))
    (h2 : ∀ y' : W', ∃ y : W, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → y'.1 k' = ι (y.1 k)) :
    ∃ φ : W ≃+ W', ∀ (y : W) (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → (φ y).1 k' = ι (y.1 k) := by
  subst hn
  choose F hF using h1
  have hF' : ∀ y k, (F y).1 k = ι (y.1 k) := fun y k => hF y k k rfl
  let ψ : W →+ W' :=
    { toFun := F
      map_zero' := Subtype.ext (funext fun k => by rw [hF']; simp)
      map_add' := fun a b => Subtype.ext (funext fun k => by
        simp only [Submodule.coe_add, Pi.add_apply, hF', map_add]) }
  have hb : Function.Bijective ψ := by
    constructor
    · intro a b hab
      refine Subtype.ext (funext fun k => ι.injective ?_)
      rw [← hF', ← hF']
      exact congrArg (fun v : W' => v.1 k) hab
    · intro y'
      obtain ⟨y, hy⟩ := h2 y'
      exact ⟨y, Subtype.ext (funext fun k => (hF' y k).trans (hy k k rfl).symm)⟩
  exact ⟨AddEquiv.ofBijective ψ hb, fun y k k' hk => hF y k k' hk⟩

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem cusp_type_eq_of_heq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {H H' : Host E} (hH : H' = H) {l : Level H} {l' : Level H'} (hl : HEq l' l)
    {c : Coeff l} {c' : Coeff l'} (hc : HEq c' c) {Dw : ℕ → Datum H} {Dw' : ℕ → Datum H'} (hDw : HEq Dw' Dw)
    {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'} (hXo : HEq Xo' Xo)
    {U : ∀ j (σ : c.F →+* ℂ), Formalism.L2.Pj.Unf (Xo j) c σ r} {U' : ∀ j (σ : c'.F →+* ℂ), Formalism.L2.Pj.Unf (Xo' j) c' σ r}
    (hU : HEq U' U) {a a' : (E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n n' : ℕ} (hn : n' = n) {j j' : ℕ} (hj : j' = j) :
    (Formalism.L2.Pj.cusp (Xo' j') c' (U' j') a' n' : Type) = (Formalism.L2.Pj.cusp (Xo j) c (U j) a n : Type) := by
  subst hH ha hn hj
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hDw
  obtain rfl := eq_of_heq hXo
  obtain rfl := eq_of_heq hU
  rfl

theorem extendByZero_congr_of_heq {Tau : Type} (p : ℕ → ℕ) {j j' : ℕ} (hj : j' = j) {a : Tau → Fin (p j) → ℕ}
    {a' : Tau → Fin (p j') → ℕ} (h : HEq a' a) (t : Tau) : Formalism.L2.Pj.ext0 (a' t) = Formalism.L2.Pj.ext0 (a t) := by
  subst hj; cases h; rfl

set_option maxHeartbeats 4000000 in

theorem cusp_type_eq_dat {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (hB : B'.toPre = B.toPre) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hN : ExtN z z')
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j') :
    z.R.nW j = z'.R.nW j' ∧
    (z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n : Type) =
      (z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n : Type) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have hH : z'.core.Q.H = z.core.Q.H := eq_of_heq hN.H
  have hκ := hN.κ j j' hj
  have ha : Formalism.L2.Pj.wtA (z'.geo.κ j') = Formalism.L2.Pj.wtA (z.geo.κ j) := by
    funext x
    unfold Formalism.L2.Pj.wtA
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : Formalism.L2.Pj.ext0 ((z'.geo.κ j').aP t) = Formalism.L2.Pj.ext0 ((z.geo.κ j).aP t) :=
      extendByZero_congr_of_heq (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t
    have e2 : Formalism.L2.Pj.ext0 ((z'.geo.κ j').aM t) = Formalism.L2.Pj.ext0 ((z.geo.κ j).aM t) :=
      extendByZero_congr_of_heq (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t
    rw [e1, e2]
    rfl
  have hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1 := by rw [hj]
  have M := cusp_type_eq_of_heq hH hN.l hN.c hN.Dw hN.Xo hN.U ha hκ.2.2 hj1
  have hn : z'.R.nW j' = z.R.nW j :=
    (congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))
  refine ⟨hn.symm, ?_⟩
  exact (by with_unfolding_all exact (M :))

set_option maxHeartbeats 4000000 in

theorem forms_match_dat {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (hB : B'.toPre = B.toPre) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hN : ExtN z z') (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ t, (w'.st Z').toD7.what₂.embLL (φ t) = (w.st Z).toD7.what₂.embLL t)
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j') :
    z.R.nW j = z'.R.nW j' ∧
    (∀ y : (z.R.FW j).WK, ∃ y' : (z'.R.FW j').WK, ∀ (k : Fin (z.R.nW j))
      (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → y'.1 k' = φ (y.1 k)) ∧
    (∀ y' : (z'.R.FW j').WK, ∃ y : (z.R.FW j).WK, ∀ (k : Fin (z.R.nW j))
      (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → y'.1 k' = φ (y.1 k)) := by
  obtain ⟨hn, M⟩ := cusp_type_eq_dat hB z z' hN j j' hj
  have hinj : Function.Injective (w'.st Z').toD7.what₂.embLL := RingHom.injective _
  refine ⟨hn, fun y => ?_, fun y' => ?_⟩
  · obtain ⟨u, rfl⟩ : ∃ u, z.geo.fw.e j u = y := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    exact ⟨z'.geo.fw.e j' (cast M.symm u), fun k k' hk =>
      hinj ((hN.forms j j' hj u (cast M.symm u) (cast_heq _ _) k k' hk).trans (hφ _).symm)⟩
  · obtain ⟨u', rfl⟩ : ∃ u', z'.geo.fw.e j' u' = y' := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    exact ⟨z.geo.fw.e j (cast M u'), fun k k' hk =>
      hinj ((hN.forms j j' hj (cast M u') u' (cast_heq _ _).symm k k' hk).trans (hφ _).symm)⟩

theorem forms_corr_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → (sideAt x g hg a).R.nW j = (sideAt x' g' hg' a').R.nW j' ∧ ∃ φ : ↥((sideAt x g hg a).R.FW j).WK ≃+ ↥((sideAt x' g' hg' a').R.FW j').WK, ∀ (y : ↥((sideAt x g hg a).R.FW j).WK) (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → (φ y).1 k' = ι (y.1 k) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' j j' hj
  obtain ⟨hn, h1, h2⟩ := forms_match_dat l.enl.1 (datAt x g) (datAt x' g') l.extN ι l.cp.embLL j j' hj
  exact ⟨hn, exists_addEquiv_of_coord hn _ _ ι h1 h2⟩

end GlobalTheory.HeightCounting.SerMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesSupLatticeMemIffCoordinateImage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove.MKLink
open GlobalTheory.Mem.R3.MKExt Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 4000000 in

theorem mk_iff_of_extN {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hB : B'.toPre = B.toPre) (hN : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (y : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (y' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hyy : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → y' k' = φ (y k))
    (hy : y ∈ (z.R.FW j).WK) : y ∈ (z.R.FW j).MK ↔ y' ∈ (z'.R.FW j').MK := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have hH : z'.core.Q.H = z.core.Q.H := eq_of_heq hN.H
  have hκ := hN.κ j j' hj
  have ha : wtA (z'.geo.κ j') = wtA (z.geo.κ j) := by
    funext x
    unfold wtA
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : ext0 ((z'.geo.κ j').aP t) = ext0 ((z.geo.κ j).aP t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t
    have e2 : ext0 ((z'.geo.κ j').aM t) = ext0 ((z.geo.κ j).aM t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t
    rw [e1, e2]
    rfl
  have hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1 := by rw [hj]
  have hn : z'.R.nW j' = z.R.nW j :=
    (congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))
  have hinj : Function.Injective (w'.st Z').toD7.what₂.embLL := RingHom.injective _
  obtain ⟨g, he⟩ : ∃ g, z.geo.fw.e j g = ⟨y, hy⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
  obtain ⟨g', hgg, hP⟩ := cusp_match' hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 g
  have hx : ((z.geo.fw.e j g : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = y :=
    congrArg Subtype.val he
  have hx' : y' = ((z'.geo.fw.e j' g' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) := by
    funext k'
    have hk : ((Fin.cast hn k' : Fin (z.R.nW j)) : ℕ) = k' := rfl
    have h3 := hN.forms j j' hj g g' hgg (Fin.cast hn k') k' hk
    have h4 := hyy (Fin.cast hn k') k' hk
    apply hinj
    rw [h4]
    exact (hφ _).trans ((congrArg (fun v => (w.st Z).toD7.what₂.embLL (v (Fin.cast hn k'))) hx).symm.trans h3.symm)
  subst hx'
  subst hx
  constructor
  · rintro ⟨_, h2⟩
    exact ⟨(z'.geo.fw.e j' g').2, (nrm_le_one_iff z'.geo.fw j' g').2 (hP.2 ((nrm_le_one_iff z.geo.fw j g).1 h2))⟩
  · rintro ⟨_, h2⟩
    exact ⟨(z.geo.fw.e j g).2, (nrm_le_one_iff z.geo.fw j g).2 (hP.1 ((nrm_le_one_iff z'.geo.fw j' g').1 h2))⟩

end GlobalTheory.HeightCounting.SerMove.MKLink

namespace GlobalTheory.HeightCounting.SerMove
open GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 4000000 in

theorem mk_iff_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → y ∈ ((sideAt x g hg a).R.FW j).WK → (y ∈ ((sideAt x g hg a).R.FW j).MK ↔ y' ∈ ((sideAt x' g' hg' a').R.FW j').MK) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' j j' hj y y' hyy hy
  exact MKLink.mk_iff_of_extN (datAt x g) (datAt x' g') l.enl.1 l.extN j j' hj ι (fun t => l.cp.embLL t) y y' hyy hy

end GlobalTheory.HeightCounting.SerMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesTuplePlacesOverFixedCharacterPrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove.Places

theorem sel_eq_of_conj {X : Formalism.L2.Col.Fields} (hX : X.Ok) {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    (hs : Formalism.L2.Col.IsSel X sel) {u u' : HeightOneSpectrum (𝓞 X.F)}
    (h : letI := X.starE; ∀ c ∈ (sel u).asIdeal, ∃ c' ∈ (sel u').asIdeal, (c' : X.E) = star (c : X.E)) : sel u = sel u' := by
  have hle : u.asIdeal ≤ u'.asIdeal := fun y hy => by
    rw [← hs u] at hy
    rw [← hs u']
    obtain ⟨c', hc', e⟩ := h _ hy
    have : c' = algebraMap (𝓞 X.F) (𝓞 X.E) y := RingOfIntegers.ext (e.trans (hX.star_F (y : X.F)))
    rw [this] at hc'
    exact hc'
  rw [HeightOneSpectrum.ext (u.isMaximal.eq_of_le u'.isPrime.ne_top hle)]

theorem unrAt_mul_iff {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h' : χ'.UnrAt v) :
    (χ * χ').UnrAt v ↔ χ.UnrAt v :=
  forall₂_congr fun x hx => by rw [HChar.loc_mul, h' x hx, mul_one]

def delAt {P : Pre} (f : Top.Fr P) (n : ℕ) : HChar P.host.E := if n = P.host.pde then f.del' else f.del

def OverDel {P : Pre} (Q : HeightOneSpectrum (𝓞 P.host.E)) : Prop :=
  ((P.host.pde : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal ∨ ((P.host.pde' : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal

theorem unrAt_xiTw_iff {B : Base} (T : TwDat B) (f : Top.Fr B.toPre) (v : B.places.Pl) {Q : HeightOneSpectrum (𝓞 B.host.E)}
    (hQ : OverDel (P := B.toPre) Q) : (T.xiTw f v).UnrAt Q ↔ (delAt f (B.places.resChar v)).UnrAt Q := by
  refine unrAt_mul_iff ?_
  by_contra h
  obtain ⟨-, hpr, -, hnot⟩ := (T.psi_tw v).2.2.2 Q h
  rcases hQ with hQ | hQ
  · by_cases e : Ideal.absNorm Q.asIdeal = B.host.pde
    · exact hnot (Or.inr (Or.inr (Or.inl e)))
    · exact GlobalTheory.RowEx.DatTw.not_two_primes Q.asIdeal hpr B.host.pde_prime e (Ideal.absNorm_mem _) hQ
  · by_cases e : Ideal.absNorm Q.asIdeal = B.host.pde'
    · exact hnot (Or.inr (Or.inr (Or.inr (Or.inl e))))
    · exact GlobalTheory.RowEx.DatTw.not_two_primes Q.asIdeal hpr B.host.pde'_prime e (Ideal.absNorm_mem _) hQ

theorem transport {P P' : Pre} (h : P' = P) {f : Top.Fr P} {f' : Top.Fr P'} (hf : HEq f' f)
    {sel : HeightOneSpectrum (𝓞 P.host.F) → HeightOneSpectrum (𝓞 P.host.E)}
    {sel' : HeightOneSpectrum (𝓞 P'.host.F) → HeightOneSpectrum (𝓞 P'.host.E)} (hs : HEq sel' sel) (n : ℕ)
    {Q' : HeightOneSpectrum (𝓞 P'.host.E)} (h1 : OverDel Q') (h2 : ¬ (delAt f' n).UnrAt Q') (h3 : ∃ u, sel' u = Q') :
    ∃ Q : HeightOneSpectrum (𝓞 P.host.E), HEq Q Q' ∧ OverDel Q ∧ ¬ (delAt f n).UnrAt Q ∧ ∃ u, sel u = Q := by
  subst h
  cases hf
  cases hs
  exact ⟨Q', HEq.rfl, h1, h2, h3⟩

variable {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}

theorem exists_of_mem_Q (z : Dat (w.st Z) w.I hX T Wt) {t : TupU w.I (usedOf w.I T Wt)} {Q : HeightOneSpectrum (𝓞 B.host.E)}
    (hQ : Q ∈ z.R.Q t) : (∃ v ∈ Wt, ¬ (T.xiTw f v).UnrAt Q) ∧ ∃ u, w.I.sel u = Q := by
  have hr := (z.lev.is.Q_ram t Q).2 (Or.inl hQ)
  have hq : Q ∈ w.I.Q (ixOf w.I (usedOf w.I T Wt) t) := (iff_of_eq (congrArg (Q ∈ ·) (z.lev.Q t))).1 hQ
  refine ⟨?_, (w.I.exists_of_mem_Q hq).imp fun u hu => hu.2.1⟩
  rcases (mem_range_ixOf w.I).1 ⟨t, rfl⟩ with h | ⟨v, hv, h⟩
  · rw [h, w.I.twistPrimes_reference_tuple_eq_empty] at hq
    exact absurd hq (Finset.notMem_empty _)
  · refine ⟨v, hv, fun hu => hr ?_⟩
    have e : z.R.xiH t = T.xiTw f v := (z.lev.xiH t).trans (h.trans (congrArg (T.xiTw · v) w.C_eq))
    exact (iff_of_eq (congrArg (fun c : HChar B.host.E => c.UnrAt Q) e)).2 hu

theorem exists_mem_Q (z : Dat (w.st Z) w.I hX T Wt) {v : B.places.Pl} (hv : v ∈ Wt) {Q : HeightOneSpectrum (𝓞 B.host.E)}
    (hr : ¬ (T.xiTw f v).UnrAt Q) (hu : ∃ u, w.I.sel u = Q) : ∃ t, Q ∈ z.R.Q t := by
  obtain ⟨a, ha⟩ : T.xiTw f v ∈ Set.range w.I.xi := by
    rw [w.xi_range]
    exact Or.inr ⟨v, rfl⟩
  obtain ⟨t, ht⟩ := (mem_range_ixOf w.I (U := usedOf w.I T Wt) (a := a)).2
    (Or.inr ⟨v, hv, ha.trans (congrArg (T.xiTw · v) w.C_eq.symm)⟩)
  have e : z.R.xiH t = T.xiTw f v := (z.lev.xiH t).trans ((congrArg w.I.xi ht).trans ha)
  refine ⟨t, ?_⟩
  rcases (z.lev.is.Q_ram t Q).1 (fun h => hr ((iff_of_eq (congrArg (fun c : HChar B.host.E => c.UnrAt Q) e)).1 h)) with
    h | ⟨Q₁, h, hc⟩
  · exact h
  · obtain ⟨u₁, -, rfl, -⟩ := w.I.exists_of_mem_Q ((iff_of_eq (congrArg (Q₁ ∈ ·) (z.lev.Q t))).1 h)
    obtain ⟨u, rfl⟩ := hu
    exact (iff_of_eq (congrArg (· ∈ z.R.Q t) (sel_eq_of_conj hX w.ok.sel_ok hc))).1 h

theorem plCl_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), PlCl (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' i' t' Q' hQ hD
  have h1 : Q' ∈ x'.m.z.R.Q t' := hQ
  obtain ⟨⟨v', hv', hr⟩, hu⟩ := exists_of_mem_Q x'.m.z h1
  have hD' : OverDel (P := B'.toPre) Q' := by
    have h2 := (iff_of_eq (congrArg (Q' ∈ ·) ((Dof x').ntw.pD_eq i'))).1 hD
    split_ifs at h2
    · exact Or.inr h2
    · exact Or.inl h2
  obtain ⟨Q, hh, h2, h3, h4⟩ := transport l.enl.1 l.fr l.sel (B'.places.resChar v') hD'
    (fun h => hr ((unrAt_xiTw_iff T' f' v' hD').2 h)) hu
  rw [← GlobalTheory.Mem.Top.TwChar.resChar_plUnder l.enl v'] at h3
  obtain ⟨t, ht⟩ := exists_mem_Q x.m.z ((GlobalTheory.HeightCounting.Up.CopyEx.mem_Wt_iff l.enl l.ext v').2 hv')
    (fun h => h3 ((unrAt_xiTw_iff T f _ h2).1 h)) h4
  exact ⟨t, Q, ht, hh⟩

end GlobalTheory.HeightCounting.SerMove.Places

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedOrbitFormPrimitiveStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedOrbit_form_primitive : ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (v : LinearMap.BilinForm ℤ X₀) (hv : v ∈ balForms bar X₀), IsPrim bar (⟨v, hv⟩ : balForms bar X₀) →
  ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
    ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  first | exact @GlobalTheory.PolFan.OrbMark.eq_one_of_smul_eq_of_orbFun_evalZ_eq_one | exact GlobalTheory.PolFan.OrbMark.eq_one_of_smul_eq_of_orbFun_evalZ_eq_one | (intros; apply GlobalTheory.PolFan.OrbMark.eq_one_of_smul_eq_of_orbFun_evalZ_eq_one <;> assumption)
end

