import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}

set_option maxHeartbeats 2000000 in

structure ExtN (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') : Prop where
  H : HEq z'.core.Q.H z.core.Q.H
  l : HEq z'.core.Q.l z.core.Q.l
  c : HEq z'.core.Q.c z.core.Q.c
  Dw : HEq z'.core.Q.Dw z.core.Q.Dw
  Xo : HEq z'.core.Q.Xo z.core.Q.Xo
  U : HEq z'.core.U z.core.U
  V : HEq z'.core.V z.core.V
  dict : HEq z'.core.dict z.core.dict
  mu : HEq z'.core.mu z.core.mu
  Kf : HEq z'.core.Kf z.core.Kf
  cE : HEq z'.core.cE z.core.cE
  chiW : HEq z'.core.chiW z.core.chiW
  x₀ : HEq z'.core.x₀ z.core.x₀
  iota : HEq z'.core.iota z.core.iota
  ψ : HEq z'.R.ψ z.R.ψ
  θ : HEq z'.R.θ z.R.θ
  βW : HEq z'.R.βW z.R.βW
  βY : HEq z'.R.βY z.R.βY
  nW : HEq z'.R.nW z.R.nW
  βV : HEq z'.R.βV z.R.βV
  ΛV : HEq z'.R.ΛV z.R.ΛV
  ΛW : HEq z'.R.ΛW z.R.ΛW
  Pg : HEq z'.R.Pg z.R.Pg
  eG : HEq z'.R.eG z.R.eG
  Sb : HEq z'.R.Sb z.R.Sb
  BV : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.cV i').W (z.R.cV i).W ∧ HEq (z'.R.cV i').ρ (z.R.cV i).ρ ∧ HEq (z'.R.vacP i') (z.R.vacP i) ∧
    HEq (z'.R.ioP i') (z.R.ioP i) ∧ HEq (z'.R.ωP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.ωP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (z'.R.BV i') (z.R.BV i)
  MW : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).H (z.R.MW i (w.st Z).toD7.what₂.embLL).H ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).nacg (z.R.MW i (w.st Z).toD7.what₂.embLL).nacg ∧
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).ips (z.R.MW i (w.st Z).toD7.what₂.embLL).ips ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).σ (z.R.MW i (w.st Z).toD7.what₂.embLL).σ ∧
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).lam (z.R.MW i (w.st Z).toD7.what₂.embLL).lam ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).ε (z.R.MW i (w.st Z).toD7.what₂.embLL).ε ∧
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).fr (z.R.MW i (w.st Z).toD7.what₂.embLL).fr ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).enum (z.R.MW i (w.st Z).toD7.what₂.embLL).enum ∧
    HEq (z'.R.HW i' (w'.st Z').toD7.what₂.embLL) (z.R.HW i (w.st Z).toD7.what₂.embLL) ∧
    HEq (z'.geo.v₀ i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) ∧
    ∀ φ φ', HEq φ' φ → HEq ((z'.R.FW i').j (w'.st Z').toD7.what₂.embLL (z'.geo.fw.e i' φ' : (z'.R.FW i').WK).1)
      ((z.R.FW i).j (w.st Z).toD7.what₂.embLL (z.geo.fw.e i φ : (z.R.FW i).WK).1)
  forms : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
    ∀ (k : Fin (z.R.nW i)) (k' : Fin (z'.R.nW i')), (k : ℕ) = k' →
      (w'.st Z').toD7.what₂.embLL ((z'.geo.fw.e i' φ' : (z'.R.FW i').WK).1 k') =
        (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)
  cV : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.cV i').nW (z.R.cV i).nW ∧ HEq (z'.R.cV i').iW (z.R.cV i).iW
  pb : HEq z'.core.pb z.core.pb
  ΛY : HEq z'.R.ΛY z.R.ΛY
  κ : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.geo.κ i').aP (z.geo.κ i).aP ∧ HEq (z'.geo.κ i').aM (z.geo.κ i).aM ∧ (z'.geo.κ i').n = (z.geo.κ i).n
  ref : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.vP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.vP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.HV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.thF i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thF i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.thG i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thG i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.νV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.νV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.fdV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.fdV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.νW i') (z.R.νW i) ∧ HEq (z'.R.fdW i') (z.R.fdW i)
  jL : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok)
      (ok' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).Ok)
      (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (φ' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).EqFun),
      (∀ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (φ'.1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 d).1)) →
      HEq (z'.R.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) (by exact (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res ok' φ'))
        (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) (by exact (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ))

set_option maxHeartbeats 2000000 in

theorem ExtN.ext {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'} (e : ExtN z z')
    (h : ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 fun _ _ => 0)) : Ext z z' :=
  { e with W1 := h }

set_option maxHeartbeats 2000000 in

theorem Ext.extN {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'} (e : Ext z z') : ExtN z z' :=
  { e with }

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Enl0 (B B' : Base) : Prop :=
  B'.toPre = B.toPre ∧ B'.embLL '' (B'.Ks : Set B'.LL) = B.embLL '' (B.Ks : Set B.LL) ∧
    B.embLL '' (B.LL0 : Set B.LL) ⊆ B'.embLL '' (B'.LL0 : Set B'.LL) ∧ Set.range B.embLL ⊆ Set.range B'.embLL

theorem isBaseEnlargementFixedCoefField_of_coeffEnlargement {B B' : Base} (h : Enl B B') : Enl0 B B' := ⟨h.1, h.2.1, h.2.2.1.ge, h.2.2.2⟩

theorem enlarges_refl (B : Base) : Enl0 B B := ⟨rfl, rfl, subset_rfl, subset_rfl⟩

def DatExt0 : Prop := StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' ∧ Ext z z'

theorem datExt_of_datExt0 (h : DatExt0) : DatExt :=
  StepW.trans h (StepW.of_all fun _ _ _ _ _ _ _ H B f T w e => H B f T w (isBaseEnlargementFixedCoefField_of_coeffEnlargement e))

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroIndexPlacesAdelicDataResizedEq
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
namespace GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt}

set_option maxHeartbeats 2000000 in

theorem ExtModel.same_carriers (h : Enl B B') : HEq (w'.st Z').toD7.host (w.st Z).toD7.host ∧ HEq (w'.st Z').toD7.sp (w.st Z).toD7.sp ∧
    HEq (tauE (w'.st Z').toD7) (tauE (w.st Z).toD7) ∧ HEq (fun V => GA (w'.st Z').toD7 V) (fun V => GA (w.st Z).toD7 V) ∧
    HEq (PolF (w'.st Z').toD7) (PolF (w.st Z).toD7) ∧ HEq (@Formalism.IndefR.Datum.WO (w'.st Z').toD7) (@Formalism.IndefR.Datum.WO (w.st Z).toD7) ∧
    HEq (@Bridge.Gf (w'.st Z').toD7) (@Bridge.Gf (w.st Z).toD7) ∧ HEq (w'.st Z').toD7.hc (w.st Z).toD7.hc ∧
    Formalism.IndefR.Datum.InfFam (w'.st Z').toD7 = Formalism.IndefR.Datum.InfFam (w.st Z).toD7 ∧
    HEq (@lieAt (w'.st Z').toD7) (@lieAt (w.st Z).toD7) ∧
    HEq (Formalism.L2.Pj.hostOfRecord (w'.st Z').toD7) (Formalism.L2.Pj.hostOfRecord (w.st Z).toD7) ∧
    HEq (Formalism.L2.Pj.datumOfRecord (w'.st Z').toD7) (Formalism.L2.Pj.datumOfRecord (w.st Z).toD7) := by
  obtain ⟨e, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e
  subst e
  refine ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem ExtModel.QE_one (sel) : Formalism.L2.Col.QE (X := B.fields) sel 1 = ∅ := by
  unfold Formalism.L2.Col.QE
  split
  · rename_i h
    have : Qprime (1 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := by
      ext v; simp [Qprime]
    simp [this]
  · rfl

theorem ExtModel.rowSG_ref (U : Set w.I.ι) :
    Formalism.L2.Col.rowSG (B.primes w.px) w.I.sel (mu0F (X := B.fields) (tuOf w.I U)).1 = (B.primes w.px).vGs := by
  show Formalism.L2.Col.uSG _ (Formalism.L2.Col.QE (X := B.fields) w.I.sel 1) = _
  rw [ExtModel.QE_one]
  simp [Formalism.L2.Col.uSG]

set_option maxHeartbeats 2000000 in

theorem ExtModel.deco_eq (h : Enl B B') (hp : HEq w'.px w.px) (U : Set w.I.ι) (U' : Set w'.I.ι) (j : ℕ) :
    (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I U')).1 j).D =
      (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I U)).1 j).D ∧
    Gc B' w'.px = Gc B w.px := by
  have a := ExtModel.rowSG_ref (w := w) U
  have a' := ExtModel.rowSG_ref (w := w') U'
  show (letI := B'.fields.starE; Formalism.L2.Col.DecoSet B'.fields.E B'.R.nV ∅ (Formalism.L2.Col.rowSG (B'.primes w'.px) w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I U')).1)) =
    (letI := B.fields.starE; Formalism.L2.Col.DecoSet B.fields.E B.R.nV ∅ (Formalism.L2.Col.rowSG (B.primes w.px) w.I.sel (mu0F (X := B.fields) (tuOf w.I U)).1)) ∧ _
  rw [a, a']
  clear a a'
  generalize w'.px = p' at hp ⊢
  generalize w.px = p at hp ⊢
  obtain ⟨e, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e
  subst e
  cases hp
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 2000000 in

theorem ExtModel.par_eq (h : Enl B B') :
    HEq (fun W : HSp (w'.st Z').toD7 => parAt W (w'.st Z').toD7.what₂.embLL) (fun W : HSp (w.st Z).toD7 => parAt W (w.st Z).toD7.what₂.embLL) := by
  have a : labE (D := (w.st Z).toD7) (w.st Z).toD7.what₂.embLL = tauE (w.st Z).toD7 := funext fun τ => B.fields_embC τ
  have a' : labE (D := (w'.st Z').toD7) (w'.st Z').toD7.what₂.embLL = tauE (w'.st Z').toD7 := funext fun τ => B'.fields_embC τ
  unfold parAt kapAt lab
  rw [a, a']
  clear a a'
  obtain ⟨e, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e
  subst e
  exact HEq.rfl

variable {hX : B.fields.Ok} {Wt W₁ : Set B.places.Pl}

theorem ExtModel.not_ext {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w.st Z) w.I hX T W₁}
    (h : z'.R.ψ ≠ z.R.ψ ∨ z'.R.nW ≠ z.R.nW) : ¬ Ext z z' :=
  fun e => h.elim (fun q => q (eq_of_heq e.ψ)) fun q => q (eq_of_heq e.nW)

theorem ExtModel.nonzeroIndexPlaces_adelicDataResized_eq {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w.st Z) w.I hX T W₁} (e : Ext z z') :
    z.W1 (fun _ _ => 0) = z'.W1 fun _ _ => 0 :=
  Set.ext fun v => e.W1 v v fun x x' q => by
    have : x = x' := RingOfIntegers.ext ((w.D Z).what₂.embLL.injective q)
    rw [this]

theorem ExtModel.below_exists (D D' : D7) (h : Set.range D.what₂.embLL ⊆ Set.range D'.what₂.embLL) (v' : D'.what₂.places.Pl) :
    ∃! v, Below D D' v v' := by
  choose g hg using fun x => h ⟨x, rfl⟩
  have inj := D'.what₂.embLL.injective
  let ι : D.what₂.LL →+* D'.what₂.LL :=
    { toFun := g
      map_one' := inj (by rw [hg, map_one, map_one])
      map_mul' := fun a b => inj (by rw [hg, map_mul, map_mul, hg, hg])
      map_zero' := inj (by rw [hg, map_zero, map_zero])
      map_add' := fun a b => inj (by rw [hg, map_add, map_add, hg, hg]) }
  letI : Algebra D.what₂.LL D'.what₂.LL := ι.toAlgebra
  have key : ∀ (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL), D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) ↔
      algebraMap (𝓞 D.what₂.LL) (𝓞 D'.what₂.LL) x = x' := fun x x' => by
    constructor
    · intro q
      exact RingOfIntegers.ext (inj ((hg _).trans q))
    · rintro rfl
      exact (hg _).symm
  refine ⟨D.plEq.symm ((D'.plEq v').under (𝓞 D.what₂.LL)), fun x x' q => ?_, fun v hv => ?_⟩
  · rw [Equiv.apply_symm_apply, ← (key x x').1 q]
    rfl
  · rw [Equiv.eq_symm_apply]
    ext x
    exact hv x _ ((key x _).2 rfl)

set_option maxHeartbeats 4000000 in

theorem ExtModel.mmap_eq (h : Enl B B') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (l : HEq M'.lam M.lam) (e : HEq M'.ε M.ε)
    (g : HEq M'.fr M.fr) :
    Formalism.IndefR.Mult.MMap M' = Formalism.IndefR.Mult.MMap M ∧ LowT M' = LowT M ∧ M'.Vec = M.Vec ∧
      HEq (inferInstance : Module ℂ (Formalism.IndefR.Mult.MMap M')) (inferInstance : Module ℂ (Formalism.IndefR.Mult.MMap M)) ∧
      HEq (inferInstance : Module ℂ (LowT M')) (inferInstance : Module ℂ (LowT M)) := by
  obtain ⟨q, -⟩ := h
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
  exact ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩

theorem ExtModel.sign_at_base_place_eq_embedding (z : Dat (w.st Z) w.I hX T Wt) :
    sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A = (w.st Z).toD7.what₂.embLL :=
  if_pos z.R.hv0

set_option maxHeartbeats 4000000 in

theorem ExtModel.more_carriers (h : Enl B B') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    (k : WeightFamilies.Wt (w.st Z).toD7 ((i : ℕ) + 1)) :
    (∃ k' : WeightFamilies.Wt (w'.st Z').toD7 ((i' : ℕ) + 1), HEq k'.aP k.aP ∧ HEq k'.aM k.aM ∧ k'.n = k.n) ∧
    Measure (GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i')) = Measure (GA (w.st Z).toD7 (Vc (w.st Z).toD7 i)) ∧
    Measure (GA (w'.st Z').toD7 (Wc (w'.st Z').toD7 i')) = Measure (GA (w.st Z).toD7 (Wc (w.st Z).toD7 i)) := by
  obtain ⟨q, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact ⟨⟨{ k with }, HEq.rfl, HEq.rfl, rfl⟩, rfl, rfl⟩

set_option maxHeartbeats 4000000 in

theorem ExtModel.pol_eq (h : Enl B B') (n : ℕ) :
    Formalism.L2.DIV.Pol ℂ B'.fields.Tau n = Formalism.L2.DIV.Pol ℂ B.fields.Tau n ∧ HEq B'.wts.lamV B.wts.lamV := by
  obtain ⟨q, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  exact ⟨rfl, HEq.rfl⟩

theorem ExtModel.meas_eq {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w.st Z) w.I hX T W₁} (e : Ext z z') (i : Fin (w.st Z).toD7.R.m) :
    z'.R.νW i = z.R.νW i ∧ z'.R.fdW i = z.R.fdW i ∧ z'.R.ΛY = z.R.ΛY :=
  ⟨eq_of_heq (e.ref i i rfl).2.2.2.2.2.2.1, eq_of_heq (e.ref i i rfl).2.2.2.2.2.2.2, eq_of_heq e.ΛY⟩

set_option maxHeartbeats 4000000 in

theorem ExtModel.premise_zero (h : Enl B B') (U : Set w.I.ι) (U' : Set w'.I.ι) (j : ℕ) (d d') :
    HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ)
      ((0 : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I U')).1 j).EqFun).1 d').1)
      (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ)
      ((0 : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I U)).1 j).EqFun).1 d).1) := by
  refine HEq.trans (heq_of_eq (map_zero _)) (HEq.trans ?_ (heq_of_eq (map_zero _)).symm)
  clear d d'
  obtain ⟨q, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  exact HEq.rfl

end GlobalTheory.Mem.R3.Rw
end
end

