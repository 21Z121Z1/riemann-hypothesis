import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0036
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.PieriBlockIdeals.StatementE
import Formalism.PieriBlockIdeals.Bundle0007
import Formalism.SharpRestriction.Divisibility.JumpSets
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB

namespace GlobalTheory.Fc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Point

variable {D : D7} {O : Obj D} {c : ℝ}

def Bundle.TiePins (b : Bundle D O c) (Rr : RealRec b.B.Q) : Prop :=
  PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG ∧ RealPins3 b.B.Q ∧ ∃ pins : RealPins b.B.Q, RealRecPins pins Rr

abbrev Bundle.Comparison₂ (b : Bundle D O c) : Type 1 := {Rr : RealRec b.B.Q // b.TiePins Rr}

abbrev Bundle.mkTie (b : Bundle D O c) (Rr : RealRec b.B.Q) (psi : PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG)
    (pins : RealPins b.B.Q) (pins3 : RealPins3 b.B.Q) (recPins : RealRecPins pins Rr) : b.Comparison₂ :=
  ⟨Rr, psi, pins3, pins, recPins⟩

theorem Bundle.Comparison₂.psi {b : Bundle D O c} (t : b.Comparison₂) : PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG := t.2.1

theorem Bundle.Comparison₂.pins3 {b : Bundle D O c} (t : b.Comparison₂) : RealPins3 b.B.Q := t.2.2.1

theorem Bundle.Comparison₂.pins {b : Bundle D O c} (t : b.Comparison₂) : RealPins b.B.Q := let ⟨h, _⟩ := t.2.2.2; h

theorem Bundle.Comparison₂.recPins {b : Bundle D O c} (t : b.Comparison₂) : RealRecPins t.pins t.1 := let ⟨_, h⟩ := t.2.2.2; h

@[reducible] def Bundle.part (b : Bundle D O c) (t : b.Comparison₂) : Ind.Part D O c where
  R := b.R
  S := b.S
  P := b.P
  pin := b.pin
  DH := b.DH
  Dcf := b.C.c.face
  Spf := b.C.Sp
  ok1 := b.C.ok1
  B := b.B
  Rr := t.1
  psi := t.psi
  pins := t.pins
  muDef := t.pins3.muDef
  recPins := t.recPins

theorem zsc_eq_ind (P : RowSideFamily O.ex) (Del h0 : ℕ) (c : ℝ) : Ind.zsc P Del h0 c = zsc P Del h0 c := rfl

theorem exists_part_eq (p : Ind.Part D O c) (C : GlobalTheory.Cp.SquareIntegrableColumnsCompatible p.R.T p.P) (hD : p.Dcf = C.c.face) (hS : HEq p.Spf C.Sp) :
    ∃ (b : Bundle D O c) (t : b.Comparison₂), b.part t = p := by
  revert C
  obtain ⟨R, S, P, pin, DH, Dcf, Spf, ok1, B, Rr, psi, pins, muDef, recPins⟩ := p
  show ∀ C : GlobalTheory.Cp.SquareIntegrableColumnsCompatible R.T P, Dcf = C.c.face → HEq Spf C.Sp → _
  intro C hD hS
  subst hD
  obtain rfl := eq_of_heq hS
  exact ⟨⟨R, S, P, pin, DH, C, B⟩, ⟨Rr, psi, ⟨muDef⟩, pins, recPins⟩, rfl⟩

example (b : Bundle D O c) (t : b.Comparison₂) : (b.part t).B = b.B := rfl

example (b : Bundle D O c) (t : b.Comparison₂) : (b.part t).P = b.P := rfl

example (b : Bundle D O c) (t : b.Comparison₂) : (b.part t).Rr = t.1 := rfl

example (b : Bundle D O c) (t : b.Comparison₂) : Ind.PRB D O c (b.part t) ↔ RowsB b.B := Iff.rfl

example (b : Bundle D O c) (t : b.Comparison₂) : (b.part t).pt.R = b.B.Q.Rl := rfl

end Point

def HasTie : BdP Bundle := fun _ _ _ b => Nonempty b.Comparison₂

abbrev TiedBundle : BdT := fun D O c => Σ b : Bundle D O c, b.Comparison₂

abbrev TiedBundle.base : ∀ D O c, TiedBundle D O c → Bundle D O c := fun _ _ _ b => b.1

abbrev TiedBundle.part : ∀ D O c, TiedBundle D O c → Ind.Part D O c := fun _ _ _ b => b.1.part b.2

abbrev LkT.onTied (Lk : LkT Bundle) : LkT TiedBundle := fun K β c b => Lk K β c b.1

section Sel

variable {𝒜 : FamClass}

abbrev TieSel (σ : RawSel Bundle 𝒜) : Type 1 :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), (σ Fm hc x hx i).Comparison₂

def compatibleSelection (σ : RawSel Bundle 𝒜) (τ : TieSel σ) : RawSel TiedBundle 𝒜 :=
  fun Fm hc x hx i => ⟨σ Fm hc x hx i, τ Fm hc x hx i⟩

def partSel (σ : RawSel Bundle 𝒜) (τ : TieSel σ) : RawSel Ind.Part 𝒜 :=
  fun Fm hc x hx i => (σ Fm hc x hx i).part (τ Fm hc x hx i)

def tieSelOf {σ : RawSel Bundle 𝒜} (h : AtAll HasTie 𝒜 σ) : TieSel σ :=
  fun Fm hc x hx i => Classical.choice (h Fm hc x hx i)

theorem map_base_tiedSel (σ : RawSel Bundle 𝒜) (τ : TieSel σ) :
    (RawSel.map TiedBundle.base (compatibleSelection σ τ) : RawSel Bundle 𝒜) = @σ := rfl

theorem map_part_tiedSel (σ : RawSel Bundle 𝒜) (τ : TieSel σ) :
    (RawSel.map TiedBundle.part (compatibleSelection σ τ) : RawSel Ind.Part 𝒜) = @partSel 𝒜 σ τ := rfl

end Sel

section Construction₂

open GlobalTheory.Mem GlobalTheory.Mem.Top

variable {Q Q' : V4.Slot} {Lk : LkT Bundle}

theorem Row.of_tied {Lk' : LkT TiedBundle} (hQ : ∀ K X f T c, Q K X f T c → Q' K X f T c)
    (hL : EvP fun _ K => ∀ β : BPt K, β.Is Q → ∀ (c : ℝ) (b : Bundle β.D β.O c), Lk K β c b → ∃ t : b.Comparison₂, Lk' K β c ⟨b, t⟩)
    {H : ∀ 𝒜 : FamClass, RawSel TiedBundle 𝒜 → Prop} (h : Row Q' Lk' H) :
    Row Q Lk fun 𝒜 σ => ∃ τ : TieSel σ, H 𝒜 (compatibleSelection σ τ) := by
  obtain ⟨E, e, h⟩ := h
  refine ⟨fun κ D O c b => ∃ t : b.Comparison₂, Built Q' Lk' κ D O c ⟨b, t⟩ ∧ E κ D O c ⟨b, t⟩,
    (EvP.and hL e).mono fun κ K hk H β hq c b hl => ?_, fun 𝒜 σ s => ?_⟩
  · obtain ⟨t, ht⟩ := H.1 β hq c b hl
    exact ⟨t, Built.intro hk (hQ _ _ _ _ _ hq) ht, H.2 β (hQ _ _ _ _ _ hq) c _ ht⟩
  · choose κ h1 h2 h3 using @s
    choose τ h4 using fun (eps : ℝ) (Fm : FamP eps) (hc : 𝒜 Fm) x hx i => (h3 Fm hc x hx i).2
    exact ⟨fun Fm hc => τ _ Fm hc, h 𝒜 _ fun Fm hc => ⟨κ Fm hc, h1 Fm hc, h2 Fm hc, h4 _ Fm hc⟩⟩

theorem Row.descend {Lk' : LkT TiedBundle} (hQ : ∀ K X f T c, Q K X f T c → Q' K X f T c)
    (hL : EvP fun _ K => ∀ β : BPt K, β.Is Q → ∀ (c : ℝ) (b : Bundle β.D β.O c), Lk K β c b → ∃ t : b.Comparison₂, Lk' K β c ⟨b, t⟩)
    {H : ∀ 𝒜 : FamClass, RawSel Bundle 𝒜 → Prop} (h : Row Q' Lk' fun 𝒜 σ => H 𝒜 (RawSel.map TiedBundle.base σ)) :
    Row Q Lk H :=
  (Row.of_tied hQ hL h).imp fun _ _ _ H => let ⟨_, t⟩ := H; t

theorem Row.of_part {Lk' : LkT Ind.Part} (hQ : ∀ K X f T c, Q K X f T c → Q' K X f T c)
    (hL : EvP fun _ K => ∀ β : BPt K, β.Is Q → ∀ (c : ℝ) (b : Bundle β.D β.O c), Lk K β c b → ∃ t : b.Comparison₂, Lk' K β c (b.part t))
    {H : ∀ 𝒜 : FamClass, RawSel Ind.Part 𝒜 → Prop} (h : Row Q' Lk' H) :
    Row Q Lk fun 𝒜 σ => ∃ τ : TieSel σ, H 𝒜 (partSel σ τ) :=
  Row.of_tied (Lk' := fun K β c b => Lk' K β c (TiedBundle.part _ _ c b)) hQ hL
    (H := fun 𝒜 σ => H 𝒜 (RawSel.map TiedBundle.part σ))
    (Row.map (Bd := TiedBundle) TiedBundle.part (fun _ _ _ _ _ t => t) (fun _ _ _ _ _ t => t) h)

theorem Row.onTied {H : ∀ 𝒜 : FamClass, RawSel Bundle 𝒜 → Prop} (h : Row Q Lk H) :
    Row Q Lk.onTied fun 𝒜 σ => H 𝒜 (RawSel.map TiedBundle.base σ) :=
  Row.map (Bd := TiedBundle) TiedBundle.base (fun _ _ _ _ _ t => t) (fun _ _ _ _ _ t => t) h

theorem Row.of_onTied (hT : RowE Q Lk fun _ => HasTie) {H : ∀ 𝒜 : FamClass, RawSel Bundle 𝒜 → Prop}
    (h : Row Q Lk.onTied fun 𝒜 σ => H 𝒜 (RawSel.map TiedBundle.base σ)) : Row Q Lk H :=
  Row.descend (fun _ _ _ _ _ t => t)
    (EvP.mono (fun _ _ _ H β hq c b hl => let ⟨t⟩ := H β hq c b hl; ⟨t, hl⟩) hT) h

end Construction₂

end GlobalTheory.Fc

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotLeafMMZero
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.BigTop.Fun.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

variable {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF)

theorem N_eq : d.O.N = GlobalTheory.ChiGrid.bigN D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (D.R.r + 6) + 1)
  have : D.R.r + 6 = D.R.k + D.R.m + 5 := by unfold Ranks.r; omega
  rw [this]

theorem nr_eq : d.O.nr = GlobalTheory.ChiGrid.nRk D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m = D.R.r + 1
  unfold Ranks.r; omega

theorem s_eq : d.O.s = GlobalTheory.ChiGrid.sLen D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m + 5 = D.R.r + 6
  unfold Ranks.r; omega

theorem PPF_eq (C b : ℝ) : d.O.PPF C b = GlobalTheory.ChiGrid.sizeP D C b := by
  unfold FunData.PPF GlobalTheory.ChiGrid.sizeP
  rw [nr_eq]; rfl

theorem Lc_eq : d.O.Lc = GlobalTheory.ChiGrid.cloudLen D := by
  classical
  have h : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
  unfold FunData.Lc GlobalTheory.ChiGrid.cloudLen
  refine le_antisymm (Finset.sup_le fun τ hτ => ?_) (Finset.sup_le fun τ _ => ?_)
  · have hτ' : τ < Fintype.card D.what₂.Tau := h ▸ Finset.mem_range.1 hτ
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun τ =>
      ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k).toNat)
      (Finset.mem_univ ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, hτ'⟩)))
    show (cloud D τ 2 - cloud D τ D.R.k).toNat = _
    simp only [cloud, dif_pos hτ']
  · refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun τ => (d.O.cl τ 2 - d.O.cl τ d.O.k).toNat)
      (Finset.mem_range.2 (show ((Fintype.equivFin D.what₂.Tau τ : Fin _) : ℕ) < D.R.f from h ▸ (Fintype.equivFin D.what₂.Tau τ).2)))
    show _ = (cloud D _ 2 - cloud D _ D.R.k).toNat
    simp only [cloud, dif_pos (Fintype.equivFin D.what₂.Tau τ).2, Fin.eta, Equiv.symm_apply_apply]

theorem ga_eq (C : ℝ) : d.O.ga C = GlobalTheory.ChiGrid.gap D C := by
  unfold FunData.ga GlobalTheory.ChiGrid.gap
  rw [N_eq, nr_eq, s_eq, Lc_eq d]; rfl

theorem ee_eq (h : Ideal.absNorm d.G.pl.v0.asIdeal = GlobalTheory.ChiGrid.q0 D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    d.O.ee CF p.Z.b v = d.G.pl.depth ⟨1, CF, p.Z.b⟩ v := by
  unfold FunData.ee GlobalTheory.ChiGrid.Places.depth GlobalTheory.ChiGrid.depth0
  rw [PPF_eq]
  have e : d.O.qq d.O.sv0 = GlobalTheory.ChiGrid.q0 D := h
  rw [e]
  by_cases hv : v = d.G.pl.v0
  · rw [if_pos hv]; exact if_pos hv
  · rw [if_neg hv]; exact if_neg hv

theorem square_ranks (C b : ℝ) : (∀ ij, d.O.dd ij = 2 * d.O.hd ij) ∧ (∀ ij, d.O.dd ij ≤ 2 * d.O.N) ∧
    (∀ ij, d.O.yy ij + 1 ≤ d.O.m) ∧ ∀ q ∈ d.O.S0, d.O.cc q ≤ d.O.ee C b q := by
  refine ⟨fun ij => ?_, fun ij => ?_, fun ij => ?_, fun q _ => ?_⟩
  · show sqRank D ij = 2 * (sqRank D ij / 2)
    have : Even (sqRank D ij) := by
      unfold sqRank
      rw [Nat.even_add, GlobalTheory.ChiGrid.even_rankV, GlobalTheory.ChiGrid.even_rankV]
      have : (ij.1 : ℕ) + (ij.2 + 1) = ij.1 + 1 + ij.2 := by ring
      rw [this]
    obtain ⟨a, ha⟩ := this
    omega
  · rw [N_eq]
    show sqRank D ij ≤ _
    unfold sqRank GlobalTheory.ChiGrid.rankV GlobalTheory.ChiGrid.bigN
    have h1 : (ij.1 : ℕ) + 1 ≤ D.R.m := ij.1.2
    have h2 : (ij.2 : ℕ) + 1 ≤ D.R.m := ij.2.2
    have h3 : D.R.r ≤ D.R.k + D.R.m := by unfold Ranks.r; omega
    nlinarith [Nat.mul_le_mul_right D.R.t h2, Nat.mul_le_mul_right (GlobalTheory.ChiGrid.sLen D) h1]
  · have := D.R.two_le_m
    show D.R.m - 1 - ij.2 + 1 ≤ D.R.m
    omega
  · unfold FunData.ee
    by_cases hv : q = d.O.sv0
    · rw [if_pos hv]
      have : d.O.cc q = 1 := if_pos hv
      omega
    · rw [if_neg hv]
      exact le_of_eq (if_neg hv)

theorem yy_eq (ij : Sq D) : d.O.yy ij =
    (GlobalTheory.ChiGrid.Node.grid ij.1 (ij.2 + 1)).neg D.R.m + (GlobalTheory.ChiGrid.Node.grid (ij.1 + 1) ij.2).neg D.R.m := by
  have := ij.2.2
  show D.R.m - 1 - ij.2 = (D.R.m - (ij.2 + 1)) / 2 + (D.R.m - ij.2) / 2
  omega

theorem not_leafMM_zero (G : Grid p CF) (W : G.Weil) (h : W.Over p.R.toRealDat) (C : ℝ) :
    ¬ LeafMM (FunIn.ofGrid G W h 0 fun _ => 0).O C := fun hM =>
  hM.2.1 ((Submodule.eq_bot_iff _).2 fun _ _ => funext fun i => i.elim0)

theorem ofGrid_lattice (G : Grid p CF) (W : G.Weil) (h : W.Over p.R.toRealDat) (V) :
    (FunIn.ofGrid G W h 1 V).M.FG ∧ (FunIn.ofGrid G W h 1 V).M ≠ ⊥ ∧ ∀ v, IsUnit ((FunIn.ofGrid G W h 1 V).X' v).det := by
  refine ⟨Submodule.fg_span (Set.finite_range _), fun e => ?_, fun v => ?_⟩
  · have e' : Submodule.span (𝓞 D.what₂.LL) (Set.range (Pi.basisFun D.what₂.LL (Fin 1))) = ⊥ := e
    exact (Pi.basisFun D.what₂.LL (Fin 1)).ne_zero 0 (Submodule.span_eq_bot.1 e' _ ⟨0, rfl⟩)
  · show IsUnit (1 : Matrix (Fin 1) (Fin 1) ℂ).det
    simp

end GlobalTheory.BigTop.Fun.Model

namespace GlobalTheory.BigTop.Fun.FieldProbe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pow_le_finrank {K : Type} [Field K] [NumberField K] {q e : ℕ} (hq : q.Prime) {z : K}
    (hz : IsPrimitiveRoot z (q ^ (e + 1))) : q ^ e ≤ Module.finrank ℚ K := by
  have h0 : 0 < q ^ (e+1) := pow_pos hq.pos _
  have h1 := (IsPrimitiveRoot.lcm_totient_le_finrank hz hz (by
    rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat h0) : _ ≤ Module.finrank ℚ K)
  rw [Nat.lcm_self, Nat.totient_prime_pow_succ hq] at h1
  have : 1 ≤ q - 1 := by have := hq.two_le; omega
  nlinarith [pow_pos hq.pos e]

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem degree_of_fit (p : PtAt ex Csz) (CF : ℝ) (G : Grid p CF) (h : GridFit p G)
    (h0 : Ideal.absNorm G.pl.v0.asIdeal = GlobalTheory.ChiGrid.q0 D) :
    GlobalTheory.ChiGrid.q0 D ^ ⌊GlobalTheory.ChiGrid.sizeP D CF p.Z.b / Real.log (GlobalTheory.ChiGrid.q0 D)⌋₊ ≤ Module.finrank ℚ D.LL0 := by
  obtain ⟨z, hz⟩ := h.field.roots _ (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  rw [h0] at hz
  refine pow_le_finrank (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1 (z := z) ?_
  simpa [GlobalTheory.ChiGrid.Places.depth, GlobalTheory.ChiGrid.depth0] using hz

theorem nonempty_iff (p : PtAt ex Csz) (CF : ℝ) : Nonempty (FunIn p CF) ↔
    ∃ (G : GlobalTheory.ChiGrid.GridData p.R.toRealDat.toLevCh ⟨1, CF, p.Z.b⟩) (W : G.Weil), W.Over p.R.toRealDat :=
  ⟨fun ⟨d⟩ => ⟨d.G, d.W, d.ext⟩, fun ⟨G, W, h⟩ => ⟨.ofGrid G W h 1 fun _ => 0⟩⟩

end GlobalTheory.BigTop.Fun.FieldProbe

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.TestLat

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Numbers

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T)
  {K K' : Type} [Field K] [Field K']

def BottomsWith (Q : ℂ → Prop) : Prop :=
  ∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
    IsBottom G μ₀ ij.1 ij.2 (SqNum.condE G.pl) P P' ∧ Q (P.norm : ℂ) ∧ Q (P'.norm : ℂ)

structure SqIn (σ : K →+* ℂ) : Prop where

  norms : BottomsWith G μ₀ (fun _ => True) → BottomsWith G μ₀ fun z => z ∈ Set.range σ

  toric : ∀ (i j : Fin D.R.m) (s : ℕ) (c : Bool) (x y : ℂ), 1 ≤ s → s ≤ halfRank D i j → IsTor G i j s (nuH G μ₀ i j) x →
    IsTor G i j s (nuH G μ₀ i j * delOf Lc c) y → y / x ∈ Set.range σ

variable {G μ₀}

theorem SqIn.mono {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : SqIn G μ₀ σ) (hσ : Set.range σ ⊆ Set.range σ') : SqIn G μ₀ σ' :=
  ⟨fun a => let ⟨δ, t0, b⟩ := h.norms a
    ⟨δ, t0, fun ij => let ⟨P, P', c⟩ := b ij; ⟨P, P', c.1, hσ c.2.1, hσ c.2.2⟩⟩,
    fun i j s c x y a b d e => hσ (h.toric i j s c x y a b d e)⟩

end Numbers

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure SlopeTestRemainingChoices (p : PtAt ex Csz) {CF : ℝ} (G : Grid p CF) (W : G.Weil) (n : ℕ) where

  M : Vol G

  ρ : G.RealVec

  ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W

  cv : ChainVec p.R.toRealDat

  rm : RealMatch W

  S : SumChoice W Set.univ

  rp : ClassReps G

  e : Fin n ≃ TestIx G × VVIdx (LaP G)

  c : Fin D.R.m → Fin D.R.m → p.P.T → ℂ

def SlopeTestRemainingChoices.ch {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) : Choice p.R.toRealDat :=
  ⟨⟨1, CF, p.Z.b⟩, G, W, a.M, a.ρ, a.ξ, a.cv, a.rm, a.S, a.rp, n, a.e, a.c⟩

theorem SlopeTestRemainingChoices.atScale {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) :
    a.ch.AtScale CF p.Z.b := rfl

structure SlopeTestRemainingChoices.OK {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) : Prop where

  is : a.ch.Is

  eser : GlobalTheory.GLq.ESerTie D

  field : a.ch.FieldOK

  sq : SqIn G p.P.A3.A.μ0 D.what₂.embLL

def Fld : FldT := fun p _ G W => ∃ (n : ℕ) (a : SlopeTestRemainingChoices p G W n), a.OK

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)

namespace GlobalTheory.ExpTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LIncl {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0)
    (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ) : Prop :=
  ∀ z ∈ B.cutZ ℓ Z, (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (B.delZ ℓ Z)

def Covers {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0)
    (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) {ι : Type} {N : ℕ} {lam : ι → ℕ → ℕ} {I : Type}
    (X : I → HidaSetting ι N lam) : Prop :=
  ∀ J : ℕ, (∀ i, (X i).Incl (Formalism.EigenvalueLevelCeiling.plc w) J) → LIncl B ℓ Z w J

def reFr {ι : Type} (W : Wts ι) (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) : Wts ι := { W with fr := fr, cj := cj }

variable {D : D7}

structure Dict (L : SizeData₂ D) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) : Prop where
  k : P.k = D.R.k
  m : P.m = D.R.m
  t : P.t = D.R.t
  f : P.f = D.R.f
  card : Nat.card D.what₂.Tau = P.f
  Nr : P.Nr = (Vc D j).rank
  x : P.x = L.sc.x
  log : P.L = L.sc.x ^ L.sc.eps
  b : P.b = L.sc.b
  lam : ∀ τ, ∃ c : ℤ, ∀ a : Fin (Vc D j).rank,
    (W.lam τ a : ℤ) = (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ).w a + c
  forced : ∀ τ, Formalism.IndefR.Bridge.IsLamPrime (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ
  box : ∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)
  thick : W.T2.card ≤ D.host.T2.card
  special : W.Sp = Formalism.MainNotions.JumpSetsAlt.excSet D
  big : ∀ i, P.h < (D.host.g i : ℝ)

def NumOk {ι : Type} (P : Par) (W : Wts ι) : Prop :=
  P.Hyp ∧ P.Large ∧ W.Ok P ∧ ∃ X' A : ℝ, Formalism.CohomologicalDescent.LargeParameterEstimates.Rows P X' A ∧ Formalism.CohomologicalDescent.LargeParameterEstimates.Big P.L P.x X' A

theorem LIncl.succ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {w : HeightOneSpectrum (𝓞 K)} {J : ℕ}
    (h : LIncl B ℓ Z w J) : LIncl B ℓ Z w (J + 1) := fun z hz => by
  rw [pow_succ', mul_smul]
  exact Submodule.smul_mem _ _ (h z hz)

section Point

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

abbrev blk (j : Fin D.R.m) (t : p.P.T) := p.P.A3.A.fam.L j t

abbrev lvlL := p.P.A3.A.fam.lvlA p.P.P0 p.P.ψ0

abbrev subZ (j : Fin D.R.m) (t : p.P.T) : Submodule D.what₂.LL (blk p j t).S.Forms :=
  (p.P.A3.fam3.toSub2 (p.R.toCx3 p.F).zs).Zl j t

open Classical in

def ModelAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∃ (fr : ℕ → D.what₂.Tau → D.what₂.Tau) (cj : ℕ → D.what₂.Tau → Bool) (I : Type) (X : I → HidaSetting D.what₂.Tau P.Nr W.lam),
    Covers (blk p j (p.R.mu w)) (lvlL p) (subZ p j (p.R.mu w)) w X ∧
      ∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)

end Point

def NumSt : Prop := AtPts fun Fm x _ i _ => ∀ j, ∃ (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W ∧ NumOk P W

open Classical in

def SumExpSt : Prop := AtPts fun Fm x _ i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
  ∀ t w, LIncl (blk p j t) (lvlL p) (subZ p j t) w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w))

def ModelSt : Prop := AtPts fun Fm x _ i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
  ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ModelAt p j P W w

end GlobalTheory.ExpTie

end
end

