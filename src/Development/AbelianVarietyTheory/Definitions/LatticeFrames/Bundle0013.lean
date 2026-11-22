import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.L2.SG.PackageTie2 Formalism.L2.SG.SpectralTiesReal
open scoped TensorProduct

namespace GlobalTheory.Core.Rk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Link (D : D7) (u : D.what₂.Word) (W : Tower D) where

  P : W.Lv

  eT : (D.mem u).P.Mt →ₗ[ℂ] W.CXP P
  eT_onto : Function.Surjective eT

  jE : W.CP P 0 →ₗ⋆[ℂ] D.s.HH
  jE_onto : Function.Surjective jE

  Θ : Desc D u
  Θ_eq : ∀ F, ∃ T₀ : W.CP P 0, W.IsDn (eT F) T₀ ∧ Θ F = jE T₀

namespace Link

variable {D : D7} {u : D.what₂.Word} {W : Tower D} (L : Link D u W)

theorem ontoAll (h : W.Onto L.P) : OntoAll D u L.Θ := by
  intro y
  obtain ⟨T₀, rfl⟩ := L.jE_onto y
  obtain ⟨T, hT, h1, h2⟩ := h T₀.1 T₀.2
  obtain ⟨F, hF⟩ := L.eT_onto ⟨T, hT⟩
  obtain ⟨T₁, ⟨h3, h4⟩, h5⟩ := L.Θ_eq F
  refine ⟨F, ?_⟩
  rw [h5]
  congr 1
  apply Subtype.ext
  have e : (⟨(L.eT F).1, h3⟩ : W.CX) = ⟨T, h1⟩ := Subtype.ext (show (L.eT F).1 = T by rw [hF])
  rw [h4, h2, e]

open Classical in

def TopPin {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) : Prop :=
  ∃ J : SmT W.MX →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ), Function.Injective J ∧
    (∀ v, J v ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramP D) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.sgT u)) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ (v : W.MX.Vec) (w : W.MX.sm τ), (w : W.MX.H τ) = W.MX.rep τ g (v τ) →
      ∀ y y' : Formalism.L2.Forms.FrP D,
        Formalism.L2.Forms.IsTr (Function.update (fun _ => 1) τ
          (g.reindex (finCongr (Formalism.L2.Forms.rankP D)) (finCongr (Formalism.L2.Forms.rankP D)))) y' y →
        J (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = J (PiTensorProduct.tprod ℂ v) y') ∧
    ∀ (F : (D.mem u).P.Mt) (c : (D.fm u).clsP) (v : SmT W.MX) (h : GA D D.sp.X'), h ∈ GfC D.sp.X' →
      (∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom D.sp.X' h)).1 i j =
        (Tf.clsP.y c).1.1 (finCongr (Formalism.L2.Forms.rankP D) i) (finCongr (Formalism.L2.Forms.rankP D) j)) →
      (L.eT F).1 v h = (Nat.card ((D.fm u).stabilizer₂ c) : ℂ) *
        (D.mem u).P.period (Tf.valP.eW.symm (Pi.single c (J v))) F

def RowPinAt (S : STies D) (hF : FinX S.Y) (v₀ : (W.MY 0).Vec) (t : GA D (Yc D 0)) : Prop :=
  (∀ τ, ‖(v₀ τ : (W.MY 0).H τ)‖ = 1) ∧ S.X.B.I = RationalEmbedding.inst D ∧
    ∃ ι : GA D (Yc D 0) ≃* S.X.B.I.GA, HEq ι (RationalEmbedding.iota D).toMulEquiv ∧ ∀ T : W.CP L.P 0,
      (((show Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX S.X from (S.hI hF).eHH (L.jE T)) : Formalism.L2.SG.RowDict.L2X S.X) : S.X.B.I.GA → ℂ)
        =ᵐ[Formalism.L2.SG.RowDict.muX S.X] fun x => star (T.1 (PiTensorProduct.tprod ℂ v₀) (ι.symm x * t))

def RowPin (S : STies D) (hF : FinX S.Y) : Prop := ∃ v₀ t, L.RowPinAt S hF v₀ t

def RowPinE (S : STies D) (hF : FinX S.Y) : Prop := (∀ x : S.X.B.I.E, HEq (S.X.ιE x) x) ∧ L.RowPin S hF

end Link

structure STrue0 (D : D7) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) extends STies D where
  tr : ∀ u, Formalism.L2.SG.ColDict.Transport X u (F₀ u)
  into : ∀ u, Formalism.L2.SG.ColDict.ColDictInto X (tr u) Y.hK
  bij : ∀ u, Formalism.L2.SG.ColDict.ColDictBij X (tr u) Y.hK
  lev : ∀ u, Formalism.L2.SG.ColDict.LevelMatch X (tr u) Y.hK
  colPin : ∀ (hF : FinX Y) (u : D.what₂.Word) (x : D.s.Cu u),
    Formalism.L2.SG.ColDict.colDict X (tr u) Y.hK (into u) (bij u) ((hI hF).eCu u x) = D.s_Cu u x
  inst : X.B.I = RationalEmbedding.inst D
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D

  pin : ∀ x : X.B.I.E, HEq (X.ιE x) x

structure STrue (D : D7) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) extends STies D where

  hF : FinX Y
  tr : ∀ u, Formalism.L2.SG.ColDict.Transport X u (F₀ u)
  into : ∀ u, Formalism.L2.SG.ColDict.ColDictInto X (tr u) Y.hK
  bij : ∀ u, Formalism.L2.SG.ColDict.ColDictBij X (tr u) Y.hK
  lev : ∀ u, Formalism.L2.SG.ColDict.LevelMatch X (tr u) Y.hK
  colPin : ∀ (u : D.what₂.Word) (x : D.s.Cu u),
    Formalism.L2.SG.ColDict.colDict X (tr u) Y.hK (into u) (bij u) ((hI hF).eCu u x) = D.s_Cu u x
  inst : X.B.I = RationalEmbedding.inst D
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D

  pin : ∀ x : X.B.I.E, HEq (X.ιE x) x

section Bare

variable {D : D7} {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u}

def STrue.bare (S : STrue D F₀) : STrue0 D F₀ where
  toSTies := S.toSTies
  tr := S.tr
  into := S.into
  bij := S.bij
  lev := S.lev
  colPin := fun _ => S.colPin
  inst := S.inst
  locTied := S.locTied
  pin := S.pin

def STrue0.withFin (S : STrue0 D F₀) (hF : FinX S.Y) : STrue D F₀ where
  toSTies := S.toSTies
  hF := hF
  tr := S.tr
  into := S.into
  bij := S.bij
  lev := S.lev
  colPin := S.colPin hF
  inst := S.inst
  locTied := S.locTied
  pin := S.pin

def STrue.equivBare : STrue D F₀ ≃ {S : STrue0 D F₀ // FinX S.Y} where
  toFun S := ⟨S.bare, S.hF⟩
  invFun S := S.1.withFin S.2
  left_inv _ := rfl
  right_inv _ := rfl

end Bare

section Built

open GlobalTheory.Mem GlobalTheory.Mem.Col2

structure World {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) where
  ok : I.Ok
  pins : TC.Pins B X
  C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)
  std : I.StdC l Z C
  S : STrue (I.rec7 l Z) fun u => (C.forms u).to0

def TrueD (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), D = I.rec7 l Z ∧ Nonempty (World I l Z)

theorem TrueD.elim {Q : D7 → Prop}
    (h : ∀ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), World I l Z → Q (I.rec7 l Z))
    {D : D7} (hD : TrueD D) : Q D := by
  obtain ⟨B, X, I, l, Z, rfl, ⟨w⟩⟩ := hD
  exact h B X I l Z w

theorem TrueD.sTies {D : D7} (hD : TrueD D) :
    ∃ S : STies D, FinX S.Y ∧ Formalism.L2.SG.Pf.LocCP.LocTied D :=
  TrueD.elim (Q := fun D => ∃ S : STies D, FinX S.Y ∧ Formalism.L2.SG.Pf.LocCP.LocTied D)
    (fun _ _ _ _ _ w => ⟨w.S.toSTies, w.S.hF, w.S.locTied⟩) hD

structure World0 {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) where
  ok : I.Ok
  pins : TC.Pins B X
  C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)
  std : I.StdC l Z C
  S : STrue0 (I.rec7 l Z) fun u => (C.forms u).to0

def IsTrueColumnDatum (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), D = I.rec7 l Z ∧ Nonempty (World0 I l Z)

section Maps

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}

def World.bare (w : World I l Z) : World0 I l Z := ⟨w.ok, w.pins, w.C, w.std, w.S.bare⟩

def World0.withFin (w : World0 I l Z) (hF : FinX w.S.Y) : World I l Z := ⟨w.ok, w.pins, w.C, w.std, w.S.withFin hF⟩

end Maps

theorem TrueD.bare {D : D7} (hD : TrueD D) : IsTrueColumnDatum D :=
  let ⟨B, X, I, l, Z, e, ⟨w⟩⟩ := hD; ⟨B, X, I, l, Z, e, ⟨w.bare⟩⟩

theorem trueD_iff {D : D7} (h : ∀ T : STies D, FinX T.Y) : TrueD D ↔ IsTrueColumnDatum D := by
  refine ⟨TrueD.bare, ?_⟩
  rintro ⟨B, X, I, l, Z, rfl, ⟨w⟩⟩
  exact ⟨B, X, I, l, Z, rfl, ⟨w.withFin (h w.S.toSTies)⟩⟩

end Built

variable (D : D7) (u : D.what₂.Word)

def MITower : Prop := ∃ (W : Tower D) (L : Link D u W), W.Is ∧ MIMap D u L.Θ

def MIKerTower : Prop := ∃ (W : Tower D) (L : Link D u W), W.Is ∧ MIKer D u L.Θ

def OntoTower : Prop := ∀ W : Tower D, W.Is → ∀ P : W.Lv, W.Onto P

theorem MITower.ker (h : MITower D u) : MIKerTower D u :=
  let ⟨W, L, h1, h2⟩ := h; ⟨W, L, h1, MIMap.miKer D u h2⟩

theorem kerIncl_of_tower (h : MIKerTower D u) (h' : OntoTower D) : KerIncl D u :=
  let ⟨W, L, h1, h2⟩ := h
  kerIncl_of D u h2 (OntoAll.ontoP D u (L.ontoAll (h' W h1 L.P)))

def MIPinned {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws}
    {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} (w : World I l Z) (u : (I.rec7 l Z).what₂.Word) : Prop :=
  ∃ (W : Tower (I.rec7 l Z)) (L : Link (I.rec7 l Z) u W), W.Is ∧ L.TopPin (w.C.forms u) ∧ L.RowPinE w.S.toSTies w.S.hF ∧
    MIMap (I.rec7 l Z) u L.Θ

def MIPinned0 {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws}
    {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} (w : World0 I l Z) (u : (I.rec7 l Z).what₂.Word) : Prop :=
  ∃ (W : Tower (I.rec7 l Z)) (L : Link (I.rec7 l Z) u W), W.Is ∧ L.TopPin (w.C.forms u) ∧
    (∀ hF : FinX w.S.Y, L.RowPinE w.S.toSTies hF) ∧ MIMap (I.rec7 l Z) u L.Θ

theorem miPinned_withFin_iff {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws}
    {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} (w : World0 I l Z) (hF : FinX w.S.Y) (u : (I.rec7 l Z).what₂.Word) :
    MIPinned (w.withFin hF) u ↔ MIPinned0 w u :=
  ⟨fun ⟨W, L, h1, h2, h3, h4⟩ => ⟨W, L, h1, h2, fun _ => h3, h4⟩, fun ⟨W, L, h1, h2, h3, h4⟩ => ⟨W, L, h1, h2, h3 hF, h4⟩⟩

def thetaRec (V : D.what₂.EE →ₗ[ℂ] D.what₂.EE) : Desc D u :=
  D.sEE.toLinearMap ∘ₛₗ (V ∘ₗ D.iota0 ∘ₗ (D.eMt u).toLinearMap)

def RowsAll : Prop := Function.Surjective D.sEE

end GlobalTheory.Core.Rk

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.OntoOfSurjectiveDescents
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.TowerModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Laws

theorem multT_anti {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (hJ : J ⊆ J') (hχ : ∀ k ∈ J, χ k = χ' k) : MultT θ M J' χ' ≤ MultT θ M J χ := by
  unfold MultT Mult
  refine Submodule.map_mono (Submodule.span_mono fun T hT => ?_)
  exact ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k (hJ hk) g, hT.equiv, hT.cont⟩

theorem multT_withP_le {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ) :
    MultT θ M (levS V β (withP L P)) (levChi V β (withP L P)) ≤ MultT θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) := by
  refine multT_anti θ M (fun k hk => ?_) (fun k hk => ?_)
  · have h1 : rTup β L (finE V k) = 1 := Subgroup.mem_bot.1 hk.2.2
    refine ⟨hk.1, hk.2.1, ?_⟩
    show rTup β L (finE V k) ∈ P.H
    rw [h1]; exact P.H.one_mem
  · have h1 : rTup β L (finE V k) = 1 := Subgroup.mem_bot.1 hk.2.2
    unfold levChi
    rw [levFn_withP, levFn_flag1, h1, blockDiagonalExtendByOnePrimeField_one, one_mul]

variable (W : Tower D)

theorem cp_le (P : W.Lv) (j : ℕ) : W.CP P j ≤ W.CC j := multT_withP_le W.θ (W.MY j) (W.βY j) (W.datYt () j W.triv) P

theorem cxp_le (P : W.Lv) : W.CXP P ≤ W.CX := multT_withP_le W.θ W.MX W.βX (W.datXt ()) P

theorem cxp_triv : W.CXP W.triv = W.CX := rfl

theorem exists_isDn (P : W.Lv) {T} (hT : T ∈ W.CXP P) : ∃ T₀ ∈ W.CC 0, W.IsDn T T₀ :=
  ⟨_, (W.thDn ⟨T, cxp_le W P hT⟩).2, cxp_le W P hT, rfl⟩

theorem isDn_unique {T T₀ T₁} (h : W.IsDn T T₀) (h' : W.IsDn T T₁) : T₀ = T₁ := by
  obtain ⟨_, rfl⟩ := h
  obtain ⟨_, rfl⟩ := h'
  rfl

theorem dnLev_triv : W.DnLev W.triv := fun _ hT => exists_isDn W _ hT

theorem onto_triv_iff : W.Onto W.triv ↔ W.Onto1 := by
  constructor
  · intro h y
    obtain ⟨T, _, hT, e⟩ := h y.1 y.2
    exact ⟨⟨T, hT⟩, Subtype.ext e.symm⟩
  · intro h T₀ h₀
    obtain ⟨x, hx⟩ := h ⟨T₀, h₀⟩
    exact ⟨x.1, x.2, x.2, by rw [show (⟨x.1, x.2⟩ : W.CX) = x from rfl, hx]⟩

theorem dnFrom_surj (n : ℕ) (h : ∀ k < n, Function.Surjective (W.ioY k)) : Function.Surjective (Lift.dnFrom W.CC W.ioY n) := by
  induction n with
  | zero => exact Function.surjective_id
  | succ n ih => exact (ih fun k hk => h k (by omega)).comp (h n (by omega))

theorem onto_of_surjective_descents (h : W.StepsOnto) : W.Onto1 :=
  (dnFrom_surj W (D.R.m - 1) fun k hk => h.1 k (by omega)).comp h.2

theorem onto_iff_bot (h : W.ioX = 0) (P : W.Lv) : W.Onto P ↔ W.CP P 0 = ⊥ := by
  have h0 : W.thDn = 0 := by unfold Tower.thDn; rw [h, LinearMap.comp_zero]
  constructor
  · intro ho
    rw [eq_bot_iff]
    intro T₀ h₀
    obtain ⟨T, _, hT, e⟩ := ho T₀ h₀
    rw [h0] at e
    exact e
  · intro hb T₀ h₀
    replace h₀ : T₀ = 0 := (Submodule.eq_bot_iff _).1 hb T₀ h₀
    refine ⟨0, (W.CXP P).zero_mem, W.CX.zero_mem, ?_⟩
    have e : W.thDn ⟨0, W.CX.zero_mem⟩ = 0 := W.thDn.map_zero
    exact h₀.trans (congrArg Subtype.val e).symm

theorem xi_one (h : W.Pre) : W.xiH () = 1 := h.chars.xi_base

theorem Q_empty (h : W.Pre) : W.Q () = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
  have := (h.chars.Q_ram () PP).2 (Or.inl hP)
  rw [h.chars.xi_base] at this
  exact this (by intro; simp)

theorem vX_ne (h : W.Pre) (τ : D.what₂.Tau) : W.vX ≠ 0 := by
  intro h0
  have hp : ∀ φ, W.ptX φ = 0 := by
    intro φ
    have : pureTensorO W.ψ W.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (W.MY (D.R.m - 1))) (cart W.MX) (onb (W.MY (D.R.m - 1)))
        (onb W.MX) W.vX = 0 := by
      rw [h0]
      unfold pureTensorO pureTensorL
      refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
      rw [Module.Basis.constr_basis, LinearMap.zero_apply]
      unfold opPow
      induction (Multiset.toList (Finsupp.toMultiset k)) with
      | nil => rfl
      | cons a l ih =>
        rw [List.foldr_cons, ih]
        funext x
        simp [aPlusAll, aPlus, crea, Datum.dRho, heisO]
    unfold Tower.ptX
    rw [this]; rfl
  refine h.ItX.ne (LinearMap.ext fun φ => LinearMap.ext fun v => ?_)
  have e := h.ItX.invg τ 0 (by simp [lieAt]) φ φ v 0 (fun z => by simp only [hp, map_zero, Pi.zero_apply]; exact hasDerivAt_const _ _)
    (fun w => by simp only [smul_zero, map_zero]; exact hasDerivAt_const _ _)
  simpa using e

theorem dnFrom_congr (io io' : ∀ k, W.CC (k + 1) →ₗ[ℂ] W.CC k) (n : ℕ) (h : ∀ k < n, io k = io' k) :
    Lift.dnFrom W.CC io n = Lift.dnFrom W.CC io' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Lift.dnFrom W.CC io n ∘ₗ io n = Lift.dnFrom W.CC io' n ∘ₗ io' n
    rw [ih fun k hk => h k (by omega), h n (by omega)]

end Laws

theorem nonempty_tower (D : D7) (L : LevCh D Unit) (hY : ∀ j, Nonempty (DSModel (Yc D j) (parB (Ptw D) (min j D.R.m))))
    (hX : Nonempty (DSModel D.sp.X' (parB (Ptw D) D.R.m))) :
    ∃ W : Tower D, W.toLevCh = L ∧ IsInfFam W.θ ∧ IsStdChar D W.ψ (-1) ∧ ¬ W.Pre := by
  obtain ⟨MX⟩ := hX
  obtain ⟨⟨θ, hθ⟩, ψ, hψ⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  exact ⟨{ toLevCh := L, θ := θ, ψ := ψ, MY := fun j => (hY j).some, MX := MX, νY := fun _ => 0, fdY := fun _ => ∅,
           νX := 0, fdX := ∅, ωY := fun _ => 1, ωX := 1, vac := fun _ => 0, vacX := 0, vY := fun _ => 0, vX := 0,
           ItY := fun _ => 0, ItX := 0, ioY := fun _ => 0, ioX := 0 }, rfl, hθ, hψ, fun h => h.ItX.ne rfl⟩

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def levAt (L : LevCh D T) (t : T) : LevCh D Unit :=
  { L with xiH := fun _ => L.xiH t, xi := fun _ => L.xi t, Q := fun _ => L.Q t, xiR := fun _ => L.xiR t }

theorem levAt_is {L : LevCh D T} {t : T} (h : L.Is t) : (levAt L t).Is () :=
  ⟨h.mu0, h.eta, fun _ => h.xi t, fun _ _ _ => rfl, h.xi_base, fun _ => h.xi_fin t, fun _ => h.xi_triv t, fun _ => h.xi_tame t,
    h.Pg, fun _ => h.Q_pl t, fun _ => h.Q_off t, fun p hp => (h.Q_de p hp).imp fun _ hq _ => hq t, fun _ => h.Q_ram t, h.chi,
    fun _ => h.xiR t, h.βY, h.βX, h.βV, h.βW⟩

set_option maxHeartbeats 2000000 in

def ofReal (R : RealDat D A Ks) (hT : R.TopMult) (t : T) : Tower D where
  toLevCh := levAt R.toLevCh t
  θ := R.θ
  ψ := R.ψ
  MY := R.MY
  MX := R.MX
  νY := R.νY t
  fdY := R.fdY t
  νX := R.νX t
  fdX := R.fdX t
  ωY := R.ωY t
  ωX := R.ωX t
  vac := R.vac
  vacX := R.vacX
  vY := R.vY t
  vX := R.vX t
  ItY := R.ItY
  ItX := R.ItX
  ioY := R.ioY t
  ioX := R.ioX t ∘ₗ (LinearEquiv.ofEq _ _ (hT t).symm).toLinearMap

theorem isIo_ofEq {G H S Sinf Ds Dt : Type} [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds]
    [AddCommGroup Dt] [Module ℂ Dt] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {pt : Sinf → S}
    {It : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt} {C C' : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))} {Ct : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))}
    {io : C →ₗ[ℂ] Ct} (e : C' = C) (h : Lift.IsIo ν 𝓕 th pt It C Ct io) :
    Lift.IsIo ν 𝓕 th pt It C' Ct (io ∘ₗ (LinearEquiv.ofEq _ _ e).toLinearMap) := by
  subst e; exact h

set_option maxHeartbeats 2000000 in

theorem ofReal_is (R : RealDat D A Ks) (hT : R.TopMult) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) :
    (ofReal R hT A.μ0).Is :=
  { chars := levAt_is hl
    inf := hm.inf
    std := (hc.ωX A.μ0).std
    νY := hm.νY A.μ0
    νY' := hm.νY' A.μ0
    νX := hm.νX A.μ0
    ωY := hc.ωY A.μ0
    ωX := hc.ωX A.μ0
    vY := hc.vY A.μ0
    vX := hc.vX A.μ0
    ptY := hc.ptY A.μ0
    ptX := hc.ptX A.μ0
    ItY := hc.ItY A.μ0
    ItX := hc.ItX A.μ0
    ioY := hc.ioY A.μ0
    ioX := isIo_ofEq (hT A.μ0).symm (hc.ioX A.μ0) }

theorem exists_is_of_char (R : RealDat D A Ks) (F : Face D A) (h : R.Char F) : ∃ W : Tower D, W.Is :=
  ⟨_, ofReal_is R (fun t => GlobalTheory.DefiniteMult.range_top R h.models.inf h.models.cX h.models.prX h.models.HX t) h.lev h.models h.chain⟩

set_option maxHeartbeats 2000000 in

theorem ofReal_isDn (R : RealDat D A Ks) (hT : R.TopMult) (t : T) (x : (R.HX t).H) :
    (ofReal R hT t).IsDn (R.cX.toMap R.prX ((R.HX t).e x)) (R.thDn t x) :=
  ⟨(hT t).le ⟨x, rfl⟩, rfl⟩

end Real

end GlobalTheory.Core.Rk.TowerModel

end
end

