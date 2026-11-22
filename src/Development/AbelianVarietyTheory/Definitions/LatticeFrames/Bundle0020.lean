import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

variable {D : D7} {u : D.what₂.Word}

def chart0 (F : Formalism.L2.Forms.Forms0 D u) : GlobalTheory.AdForm.Chart D u 0 (Nat.zero_le _) where
  cl := (D.mem u).C.cls 0
  inc := id
  K := F.cls0.toChart
  eY := F.val0.eY

theorem rd_zero {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : Formalism.L2.Forms.FormsTiedSym D u Ch chOf)
    (θ : InfFam D) (β : Ch 0) : GlobalTheory.AdForm.rd F θ 0 (Nat.zero_le _) β = (chart0 F.to0).rd θ := by
  funext ψ y
  unfold GlobalTheory.AdForm.rd GlobalTheory.AdForm.chart
  rw [dif_pos (Or.inl rfl)]
  rfl

def IsTransportAdelicCorrection {X : HidaSetting D} {F : Formalism.L2.Forms.Forms0 D u} (tr : Formalism.L2.SG.ColDict.Transport X u F) (a : GA D (D.sp.X 0)) : Prop :=
  a ∈ GfC (D.sp.X 0) ∧ GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = tr.h0.1.1

def IsSymLev {Pg : Finset (Pl D.host.E)} (P : LevelP Pg D.R.r ℂ) : Prop :=
  ∃ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi Pg ψ0 ∧
    ∃ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π ∧
      (∀ g, g ∈ P.H ↔ reord π g ∈ (PsharpSym Pg D.R.r D.R.rS D.R.k ψ0).H) ∧
      ∀ g hg hg', P.chi ⟨g, hg⟩ = (PsharpSym Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨reord π g, hg'⟩

def IsTypePlaces (Pg : Finset (Pl D.host.E)) : Prop :=
  (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      ∃! PP, PP ∈ Pg ∧ PP.under (𝓞 D.host.F) = v

variable {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)

def PinBot : Prop :=
  ∃ (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)),
    B.lev = d.B 0 D.R.rS h0 ∧ B.Adapted (S.tr u).wt ∧ IsTransportAdelicCorrection (S.tr u) a₀ ∧
    a ∈ GfC (D.sp.X 0) ∧ a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧
    Matches S.X S.inst (d.lev 0) (levChi (D.sp.Y 0) d.bot.β d.bot.L)
      (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) ∧
    d.rd 0 = (chart0 (F₀ u)).rd d.c.θ

end GlobalTheory.Core.Mi

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevelLawOfPairLaw
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto.FlagModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {c : Com D} {s s' : PiLocalization₂ D}

theorem inFlag_one : s.InFlag 1 := ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩

theorem inFlag_mul {κ κ' : GA D s.V} (h : s.InFlag κ) (h' : s.InFlag κ') : s.InFlag (κ * κ') :=
  ⟨Subgroup.mul_mem _ h.1 h'.1, by rw [map_mul]; exact Subgroup.mul_mem _ h.2 h'.2⟩

theorem ch_ne_zero (κ : GA D s.V) : s.ch κ ≠ 0 := Lev.levChi_ne_zero _ _

theorem ch_mul {κ κ' : GA D s.V} (h : s.InFlag κ) (h' : s.InFlag κ') : s.ch (κ * κ') = s.ch κ * s.ch κ' := by
  unfold PiLocalization₂.ch Lev.levChi
  rw [map_mul, Lev.levFn_flag_mul h.2 h'.2, Units.val_mul]

theorem ch_one : s.ch 1 = 1 := by
  have h := ch_mul (s := s) inFlag_one inFlag_one
  rw [mul_one] at h
  exact (mul_eq_left₀ (ch_ne_zero _)).1 h.symm

theorem moved_one (y : s.CC c) : Moved 1 y y := by
  intro w g; rw [ch_one, mul_one, inv_one, one_mul]

theorem moved_unique {κ : GA D s.V} {y a b : s.CC c} (ha : Moved κ y a) (hb : Moved κ y b) : a = b := by
  apply Subtype.ext
  refine LinearMap.ext fun w => funext fun g => ?_
  exact (ha w g).trans (hb w g).symm

theorem moved_mul {κ κ' : GA D s.V} (h : s.InFlag κ) (h' : s.InFlag κ') {y a b : s.CC c}
    (ha : Moved κ' y a) (hb : Moved κ a b) : Moved (κ * κ') y b := by
  intro w g
  rw [hb w g, ha w (g * κ), ch_mul h h', mul_assoc g, mul_inv]; ring

theorem inFlag_iff (κ : GA D s.V) :
    s.InFlag κ ↔ Lev.IsLevelLift s.V s.β s.L (rTup s.β s.L (Lev.finE s.V κ)) κ :=
  ⟨fun h => ⟨h.1, h.2, rfl⟩, fun h => ⟨h.1, h.2.1⟩⟩

theorem ch_eq_levChi {j : ℕ} (hs : s.Is c j) (hP : c.P.H = ⊥) (κ : GA D s.V) :
    s.ch κ = Lev.levChi s.V s.β s.L κ := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  have h1 : ext1 s.L.P.H s.L.P.chi (rTup s.β s.L (Lev.finE s.V κ)) = 1 := by
    have hb : s.L.P.H = ⊥ := by rw [hL]; exact hP
    unfold ext1
    split_ifs with hh
    · have : (⟨_, hh⟩ : s.L.P.H) = 1 := by
        apply Subtype.ext
        have := hh
        rw [hb] at this
        exact Subgroup.mem_bot.1 this
      rw [this, map_one]
    · rfl
  have h2 : ext1 (Lev.flagL s.L).P.H (Lev.flagL s.L).P.chi (rTup s.β (Lev.flagL s.L) (Lev.finE s.V κ)) = 1 :=
    Lev.subgroupCharExtension_one_apply _ _
  unfold PiLocalization₂.ch Lev.levChi levFn
  rw [h1, h2]
  rfl

theorem rTup_eq_one {j : ℕ} (hs : s.Is c j) (hP : c.P.H = ⊥) {κ : GA D s.V} (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    rTup s.β s.L (Lev.finE s.V κ) = 1 := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  have hb : s.L.P.H = ⊥ := by rw [hL]; exact hP
  have h : rTup s.β s.L (Lev.finE s.V κ) ∈ s.L.P.H := hκ.2.2
  rw [hb] at h
  exact Subgroup.mem_bot.1 h

theorem sameBlock_of_one {j j' : ℕ} (hs : s.Is c j) (hs' : s'.Is c j') {κ : GA D s.V} {κ' : GA D s'.V}
    (h : rTup s.β s.L (Lev.finE s.V κ) = 1) (h' : rTup s'.β s'.L (Lev.finE s'.V κ') = 1) : SameBlock s s' κ κ' := by
  unfold SameBlock
  rw [h, h']
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  obtain ⟨hr', ξ', hL'⟩ := hs'.lev
  rw [hL, hL']
  exact HEq.rfl

theorem exists_sameBlock {j j' : ℕ} (hs : s.Is c j) (hs' : s'.Is c j') (hl : Lev.LiftsExist s'.V s'.β s'.L)
    (κ : GA D s.V) : ∃ κ', s'.InFlag κ' ∧ SameBlock s s' κ κ' := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  obtain ⟨hr', ξ', hL'⟩ := hs'.lev
  have e : G0 s.L.Pg s.L.r = G0 s'.L.Pg s'.L.r := by rw [hL, hL']; rfl
  obtain ⟨κ', h1, h2, h3⟩ := hl (cast e (rTup s.β s.L (Lev.finE s.V κ)))
  refine ⟨κ', ⟨h1, h2⟩, ?_⟩
  unfold SameBlock
  rw [h3]
  exact (cast_heq _ _).symm

theorem levelLaw_of_pairLaw (h : PairLaw D) : ForStep D fun c _ s s' p => c.P.H = ⊥ → ∀ φ,
    VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) (Lev.levG s'.V s'.β s'.L)
      (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) (p.pt φ) := by
  intro hg c hc k hk s s' hs hs' p hp hP φ
  have H := h hg c hc k hk s s' hs hs' p hp hP
  have o : rTup s.β s.L (Lev.finE s.V 1) = 1 := by rw [map_one]; exact rTup_one
  have o' : rTup s'.β s'.L (Lev.finE s'.V 1) = 1 := by rw [map_one]; exact rTup_one
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · have := H κ 1 ⟨hκ.1, hκ.2.1⟩ inFlag_one (sameBlock_of_one hs hs' (rTup_eq_one hs hP hκ) o') φ
    rw [this, ch_one, ch_eq_levChi hs hP, inv_one, mul_one]
  · have := H 1 κ inFlag_one ⟨hκ.1, hκ.2.1⟩ (sameBlock_of_one hs hs' o (rTup_eq_one hs' hP hκ)) φ
    rw [this, ch_one, ch_eq_levChi hs' hP, one_mul]

theorem steps_of_is (W : GlobalTheory.Core.Rk.Tower D) (hW : W.Is) (hQ : W.Q () = ∅) :
    (∀ k, k + 1 < D.R.m → (stepY W k).Is (k + 1)) ∧ (stepX W).Is D.R.m := by
  refine ⟨fun k hk => ⟨hW.ωY k hk, ⟨W.xiR (), W.vac k, ?_⟩, hW.ptY k hk, hW.ItY k hk, hW.ioY k (by omega)⟩,
    ⟨hW.ωX, ⟨W.xiR (), W.vacX, ?_⟩, hW.ptX, hW.ItX, hW.ioX⟩⟩
  · have := hW.vY k hk
    rw [hQ] at this
    exact this
  · have := hW.vX
    rw [hQ] at this
    exact this

theorem lev_of_Q (W : GlobalTheory.Core.Rk.Tower D) (hQ : W.Q () = ∅) :
    (∀ j, ∃ hr ξ, (stageY W j).L = Lev.datY (stageY W j).V.rank D.R.r D.R.t j hr (comOf W).Pg ∅ (comOf W).P (comOf W).chi ξ Lev.Frm.B) ∧
    (∃ hr ξ, (stageX W).L = Lev.datY (stageX W).V.rank D.R.r D.R.t D.R.m hr (comOf W).Pg ∅ (comOf W).P (comOf W).chi ξ Lev.Frm.B) ∧
    (comOf W).P.H = ⊥ := by
  refine ⟨fun j => ⟨r_le_Y j, W.xiR (), ?_⟩, ⟨r_le_X, W.xiR (), ?_⟩, rfl⟩
  · rw [← hQ]; rfl
  · rw [← hQ]; rfl

theorem q_empty (W : GlobalTheory.Core.Rk.Tower D) (hW : W.Is) : W.Q () = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
  have h := (hW.chars.Q_ram () PP).2 (Or.inl hP)
  rw [hW.chars.xi_base] at h
  exact h fun x _ => rfl

theorem steps_of_is' (W : GlobalTheory.Core.Rk.Tower D) (hW : W.Is) :
    (∀ k, k + 1 < D.R.m → (stepY W k).Is (k + 1)) ∧ (stepX W).Is D.R.m := steps_of_is W hW (q_empty W hW)

end GlobalTheory.ChainOnto.FlagModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RapidVal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

open GlobalTheory.ChainOnto (Com PiLocalization₂)

def DenseTwo (D : D7) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ c : Com D, c.Is → ∀ j, j + 2 ≤ D.R.m → ∀ s s' s'' : PiLocalization₂ D, s.Is c j → s'.Is c (j + 1) →
    s''.Is c (j + 1 + 1) → ∀ (p : GlobalTheory.ChainOnto.Step c s s') (p' : GlobalTheory.ChainOnto.Step c s' s''), p.Is (j + 1) → p'.Is (j + 1 + 1) →
    ∀ (A : HSp D) (ρ : ℕ) (b : BesAt s.V A ρ) (vA : Vol A) (φ : GA D A → ℂ) (t : GA D s.V) (G : s.CC c), IsContAut A φ →
      (∀ P₁ P₂ v, (b.lev vA).per c.ψ φ (rTrans t (G.1 (p.It P₁ (p'.It P₂ v)))) = 0) →
      ∀ v, (b.lev vA).per c.ψ φ (rTrans t (G.1 v)) = 0

def RapidVal (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ),
    ∀ G ∈ MultT θ M J χ, ∀ v, RapidDec V (G v)

def ValMove (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ),
    (∀ G ∈ MultT θ M J χ, ∀ v, ∀ k ∈ J, rTrans k (G v) = χ k • G v) ∧
    ∀ a ∈ GinfC V, ∀ v, ∃ w, ∀ G ∈ MultT θ M J χ, rTrans a (G v) = G w

def PerSum (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (f : GA D B.V → ℂ), IsContAut B.V f →
    ∀ (I : Type) (s : Finset I) (a : I → ℂ) (φ : I → GA D B.A → ℂ), (∀ i ∈ s, IsContAut B.A (φ i)) →
      B.per ψ (∑ i ∈ s, a i • φ i) f = ∑ i ∈ s, a i * B.per ψ (φ i) f

def LiftSum (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is →
    ∀ k : KerDat S T, k.Is ψ θ x y → ∀ P, IsThetaFunO ψ S T (k.pt ψ θ x y P) ∧
      (∀ φ, IsContAut S φ → IsContAut T (k.lift ψ θ x y P φ)) ∧
      ∀ (I : Type) (s : Finset I) (a : I → ℂ) (φ : I → GA D S → ℂ), (∀ i ∈ s, IsContAut S (φ i)) →
        k.lift ψ θ x y P (∑ i ∈ s, a i • φ i) = ∑ i ∈ s, a i • k.lift ψ θ x y P (φ i)

namespace Dat

variable {D : D7} {u : D.what₂.Word} (d : Dat D u)

def TwoCol : Prop :=
  ∀ j, j + 2 ≤ D.R.m → ∀ C, d.IsReal j C → ∀ y, ∃ a : (D.mem u).C.Y (j + 1 + 1) →₀ ℂ, ∀ ψ ∈ d.Ram j,
    d.two j (d.rd j ψ y) C = ∑ y' ∈ a.support, a y' • d.rd (j + 1 + 1) ((D.mem u).C.K (j + 1) ((D.mem u).C.K j ψ)) y'

end Dat

def cenProj {D : D7} {S T : HSp D} (om : Om S T) (ν : Measure ↥(GinfC S ⊓ Subgroup.center (GA D S))) (χ : GA D S → ℂ)
    (f : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ∫ z, χ z.1⁻¹ * om (z.1, 1) f w ∂ν

def CenFock (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is →
    ∀ k : KerDat S T, k.Is ψ θ x y → ∀ χ : GA D S → ℂ, ∃ W : Submodule ℂ (PolF D T.rank S.rank), FiniteDimensional ℂ W ∧
      ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f →
        (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → k.om (z, 1) f = χ z • f) →
        ∃ P ∈ W, f = pureTensorO ψ θ S T x.s y.s x.B y.B k.vac P

end GlobalTheory.SeeSaw

end
end

