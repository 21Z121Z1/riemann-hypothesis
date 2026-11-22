import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  MeasureTheory NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev JR (R : RealDat D A Ks) (F : Face D A) : Set (GA D (Yc D 0)) := levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))

abbrev chiR (R : RealDat D A Ks) (F : Face D A) : GA D (Yc D 0) → ℂ := levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))

abbrev MultR (R : RealDat D A Ks) (F : Face D A) : Submodule ℂ (MMap (MP R)) := Mult R.θ (R.MY 0) (JR R F) (chiR R F)

def DallTie (R : RealDat D A Ks) (F : Face D A) : Prop := D.what₂.Dall = Module.finrank ℂ (MultR R F)

def concreteLevelAdelicSubset (X : HidaSetting D) : Set X.B.I.GA := {x | x.1 = 1 ∧ x.2 ∈ X.K2}

def adelicCharacterOfHidaSetting (X : HidaSetting D) : X.B.I.GA → ℂ := fun x => star (X.chi2 x.2)

def GrpPin (R : RealDat D A Ks) : Prop :=
  ∃ (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
    (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff (eR g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧
      ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)

structure SeeAt (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (D.sp.Y 0)) : Prop where

  fin : t ∈ GfC (Yc D 0)

  conj : ConjLevel t⁻¹ (JR R F) (chiR R F) (iotaX X h ⁻¹' concreteLevelAdelicSubset X) (fun k => adelicCharacterOfHidaSetting X (iotaX X h k))

  mat : RowLevelMatchAt R F X h t

def conjRows (X : HidaSetting D) : Submodule ℂ (L2X X) := (HHX X).comap (conjL (muX X)).toLinearEquiv.toLinearMap

def EvalOn (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (v₀ : (MP R).Vec) (c : ℝ) (E : Submodule ℂ (MMap (MP R))) (E' : Submodule ℂ (L2X X)) : Prop :=
  ∃ J : E ≃ₗ[ℂ] E', ∀ S : E,
    ((J S : E') : L2X X) =ᵐ[muX X] (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) ∧
      ‖((J S : E') : L2X X)‖ ^ 2 = c * (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re

def RowJ (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (G : GoodOp X) (t : GA D (D.sp.Y 0)) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) : Prop :=
  ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ a : ℝ, 0 < a ∧ ∀ x : D.what₂.EE,
    ((j x : EEC X G) : L2X X) =ᵐ[muX X] fun g => (a : ℂ) * ev (MP R) v₀ (R.HE.e (eE x)) ((iotaX X h).symm g * t)

theorem mem_conjRows_iff (X : HidaSetting D) (f : L2X X) : f ∈ conjRows X ↔ conjL (muX X) f ∈ HHX X := Iff.rfl

theorem EEC_le_conjRows (X : HidaSetting D) (G : GoodOp X) : EEC X G ≤ conjRows X := fun _ hF => hF.1

example (X : HidaSetting D) (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    ((1, k) : X.B.I.GA) ∈ concreteLevelAdelicSubset X ∧ adelicCharacterOfHidaSetting X (1, k) = star (X.chi2 k) := ⟨⟨rfl, hk⟩, rfl⟩

theorem evalTieT_iff_evalOn (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X)
    (t : GA D (D.sp.Y 0)) (c : ℝ) (E : Submodule ℂ (MMap (MP R))) :
    EvalTieT (MP R) R.ν0 R.fd0 E X G (iotaX X h).toMulEquiv t c ↔
      ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ EvalOn R X h t v₀ c E (EEC X G) := Iff.rfl

example (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (v₀ : (MP R).Vec) (x : X.B.I.GA) : ev (MP R) v₀ 0 ((iotaX X h).symm x * t) = 0 := by
  rw [map_zero]; rfl

theorem SeeAt.levelMatchA {R : RealDat D A Ks} {F : Face D A} {X : HidaSetting D}
    {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {t : GA D (D.sp.Y 0)} (hs : SeeAt R F X h t) : LevelMatchA R F X h t := by
  intro k hk
  have e : (t⁻¹⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ : GA D (D.sp.Y 0)) = (iotaX X h).symm (1, k) := by group
  obtain ⟨h1, h2⟩ := hs.conj (t⁻¹ * (iotaX X h).symm (1, k) * t)
  rw [e] at h1 h2
  have hm := h1.2 (by simp [concreteLevelAdelicSubset, hk])
  refine ⟨hm, ?_⟩
  have := h2 hm
  simp only [adelicCharacterOfHidaSetting, ContinuousMulEquiv.apply_symm_apply] at this
  exact this.symm

theorem exists_rowJ_of_evalOn {R : RealDat D A Ks} {F : Face D A} {X : HidaSetting D}
    {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {G : GoodOp X} {t : GA D (D.sp.Y 0)} {v₀ : (MP R).Vec} {c : ℝ}
    {eE : D.what₂.EE →ₗ[ℂ] R.HE.H} (hc : 0 < c) (hv₀ : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) (hE : R.models_HE)
    (hrange : LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e)
    (hnorm : ∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) (hle : R.EEat (R.levR F true) ≤ R.EEat R.triv)
    (hJ2 : EvalOn R X h t v₀ c (EP R F) (EEC X G)) : ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  obtain ⟨J2, hJ2⟩ := hJ2
  obtain ⟨he_inj, he_range, he_ip⟩ := hE
  have hnP : 0 < RealDat.nP F true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have heE_inj : Function.Injective eE := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hnorm x
    rw [hx, norm_zero] at h1
    have h2 : RealDat.nP F true * ‖x‖ ^ 2 = 0 := by rw [← h1]; ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hnP.ne'
    · exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)
  have hmem : ∀ x, (R.HE.e ∘ₗ eE) x ∈ EP R F := fun x => by
    have : eE x ∈ (R.EEat (R.levR F true)).comap R.HE.e := hrange ▸ LinearMap.mem_range_self eE x
    exact this
  let k : D.what₂.EE →ₗ[ℂ] EP R F := LinearMap.codRestrict (EP R F) (R.HE.e ∘ₗ eE) hmem
  have hk : Function.Bijective k := by
    constructor
    · intro x y hxy
      exact heE_inj (he_inj (congrArg Subtype.val hxy))
    · rintro ⟨y, hy⟩
      have hy' : y ∈ LinearMap.range R.HE.e := he_range ▸ hle hy
      obtain ⟨z, rfl⟩ := hy'
      have hz : z ∈ LinearMap.range eE := by rw [hrange]; exact hy
      obtain ⟨x, rfl⟩ := hz
      exact ⟨x, rfl⟩
  let L : D.what₂.EE ≃ₗ[ℂ] EEC X G := (LinearEquiv.ofBijective k hk).trans J2
  have hLn : ∀ x, ‖L x‖ ^ 2 = (c * RealDat.nP F true) * ‖x‖ ^ 2 := by
    intro x
    have h1 := (hJ2 (k x)).2
    have h2 : ((k x : EP R F) : MMap (MP R)) = R.HE.e (eE x) := rfl
    have h3 : (ipM (MP R) R.ν0 R.fd0 (R.HE.e (eE x)) (R.HE.e (eE x))).re = ‖eE x‖ ^ 2 := by
      calc (ipM (MP R) R.ν0 R.fd0 (R.HE.e (eE x)) (R.HE.e (eE x))).re
          = (inner ℂ (eE x) (eE x)).re := by rw [he_ip]; rfl
        _ = ‖eE x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (eE x)
    show ‖((J2 (k x) : EEC X G) : L2X X)‖ ^ 2 = _
    rw [h1, h2, h3, hnorm x]
    ring
  set a : ℝ := (Real.sqrt (c * RealDat.nP F true))⁻¹ with ha_def
  have hs : 0 < Real.sqrt (c * RealDat.nP F true) := Real.sqrt_pos.mpr (mul_pos hc hnP)
  have ha : 0 < a := inv_pos.mpr hs
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G :=
    { toLinearEquiv := L.trans (LinearEquiv.smulOfNeZero ℂ (EEC X G) (a : ℂ) haC)
      norm_map' := fun x => by
        show ‖(a : ℂ) • L x‖ = ‖x‖
        have hL : ‖L x‖ = Real.sqrt (c * RealDat.nP F true) * ‖x‖ := by
          rw [← Real.sqrt_sq (norm_nonneg (L x)), hLn x, Real.sqrt_mul' _ (sq_nonneg _),
            Real.sqrt_sq (norm_nonneg x)]
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ha.le, hL, ← mul_assoc, ha_def,
          inv_mul_cancel₀ hs.ne', one_mul] }
  refine ⟨j, v₀, hv₀, a, ha, fun x => ?_⟩
  have h1 : ((j x : EEC X G) : L2X X) = (a : ℂ) • ((J2 (k x) : EEC X G) : L2X X) := rfl
  rw [h1]
  filter_upwards [Lp.coeFn_smul (a : ℂ) ((J2 (k x) : EEC X G) : L2X X), (hJ2 (k x)).1] with g h2 h3
  rw [h2, Pi.smul_apply, h3, smul_eq_mul]
  rfl

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameFOfDiv
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000

def SPack.re {F : ∀ u, Forms0 D u} (P : SPack D F) {F' : ∀ u, Forms0 (reD D Z) u} (h : SameForms0LevelsAndValues Z F F')
    (hF : FinX (reY Z P.Y)) : SPack (reD D Z) F' where
  X := reX Z P.X
  hb := (by with_unfolding_all exact (P.hb :))
  Y := reY Z P.Y
  fin := hF
  ψ := (by with_unfolding_all exact (P.ψ :))
  measTie := (by with_unfolding_all exact (measTie_reX Z P.measTie :))
  ψ_char := (by with_unfolding_all exact (P.ψ_char :))
  ψ_std := (by with_unfolding_all exact (P.ψ_std :))
  measCompat := (by with_unfolding_all exact (measCompat_reX Z P.measCompat :))
  locCompat := (by with_unfolding_all exact (fun w : D.what₂.Word => locCompat_reX Z (P.locCompat w) :))
  tr := (by with_unfolding_all exact (fun u : D.what₂.Word => reTr Z (P.tr u) (h u).2.1 (h u).2.2 :))
  into := (by with_unfolding_all exact (fun u : D.what₂.Word => colDictInto_reTr Z (P.tr u) (h u).2.1 (h u).2.2 P.Y (P.into u) :))
  bij := (by with_unfolding_all exact (fun u : D.what₂.Word => colDictBij_reTr Z (P.tr u) (h u).2.1 (h u).2.2 P.Y (P.bij u) :))
  lev := (by with_unfolding_all exact (fun u : D.what₂.Word => levelMatch_reTr Z (P.tr u) (h u).1 (h u).2.1 (h u).2.2 P.Y (P.lev u) :))
  isom := (by with_unfolding_all exact (fun u : D.what₂.Word => colDictIsom_reTr Z (P.tr u) (h u).2.1 (h u).2.2 P.Y P.fin hF (P.isom u) :))
  inst := (by with_unfolding_all exact (P.inst :))
  G := reG Z P.G
  pin := (by with_unfolding_all exact (P.pin :))

section API

variable {F : ∀ u, Forms0 D u} (P : SPack D F) {F' : ∀ u, Forms0 (reD D Z) u} (h : SameForms0LevelsAndValues Z F F') (hF : FinX (reY Z P.Y))

theorem SPack.re_ψ : HEq (P.re Z h hF).ψ P.ψ := (by with_unfolding_all exact (HEq.refl P.ψ :))

end API

theorem conjHH_eEECre {X : HidaSetting D} (G : GoodOp X) (x : EEC X G) :
    conjHH (reX Z X) (reG Z G) (eEECre Z G x) = eHHre Z X (conjHH X G x) := (by with_unfolding_all exact (Eq.refl (eHHre Z X (conjHH X G x)) :))

example {X : HidaSetting D} (G : GoodOp X) :
    Module.finrank ℂ (EEC X G) = Module.finrank ℂ (EEC (reX Z X) (reG Z G)) := (eEECre Z G).toLinearEquiv.finrank_eq

example {F : ∀ u, Forms0 D u} (P : SPack D F) {F' : ∀ u, Forms0 (reD D Z) u} (h : SameForms0LevelsAndValues Z F F') (hF : FinX (reY Z P.Y)) :
    (P.re Z h hF).X.B.I = Formalism.L2.SG.InstExistsPf.instOf D := (by with_unfolding_all exact (P.inst :))

theorem exists_sameF_ofDiv (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (ht : D.what₂.Word → ℝ) (F : ∀ u, Forms0 D u) :
    ∃ F' : ∀ u, Forms0 (reD D (New.ofDiv D N ht)) u, SameForms0LevelsAndValues (New.ofDiv D N ht) F F' := by
  let G : ∀ u : D.what₂.Word, Forms0 (GlobalTheory.EX.OB.setDiv D N ht) u := fun u =>
    { F u with
      atT := { (F u).atT with }
      cls0 := { (F u).cls0 with }
      val0 := { (F u).val0 with }
      lv0 := { (F u).lv0 with } }
  refine ⟨(by with_unfolding_all exact (G :)), fun u => ⟨?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (Eq.refl (F u).cls0.lev :))
  · exact (by with_unfolding_all exact (Eq.refl (F u).cls0.y :))
  · exact (by with_unfolding_all exact (Eq.refl (F u).val0.eY :))

theorem SPack.exists_re_ofDiv (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (ht : D.what₂.Word → ℝ) {F : ∀ u, Forms0 D u}
    (P : SPack D F) :
    ∃ (F' : ∀ u, Forms0 (reD D (New.ofDiv D N ht)) u) (P' : SPack (reD D (New.ofDiv D N ht)) F'),
      P'.X = reX (New.ofDiv D N ht) P.X :=
  (exists_sameF_ofDiv N ht F).elim fun F' h => ⟨F', P.re _ h (finX_reY D _ P.X P.Y P.fin), rfl⟩

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinTypRepCast
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

def rowPsi {V : HSp a.D} {n : ℕ} (P : principalLevelFrame.RowPsi V n) : @principalLevelFrame.RowPsi b.D ((V)) n where
  ψ := (by with_unfolding_all exact (P.ψ :))
  inj := (by with_unfolding_all exact (P.inj :))
  into := (by with_unfolding_all exact (P.into :))
  onto := (by with_unfolding_all exact (P.onto :))

variable (a) in

def isotLB : type_of% (@principalLevelFrame.isotL b.D) := @fun V n S θ P M J χ e π =>
  (by with_unfolding_all exact ((@principalLevelFrame.isotL a.D ((V)) n ((S)) ((θ)) (((rowPsi a P))) (((ds a M))) ((J)) ((χ)) ((e)) ((π))) : _))

variable (a) in

theorem isotL_eq : @principalLevelFrame.isotL b.D = @isotLB B C a b := by
  funext V n S θ P M J χ e π
  exact (by with_unfolding_all exact ((congrArg₂ (fun (g : type_of% (@goodPart b.D)) (m : type_of% (@Mult.Mult b.D)) =>
    g θ M J χ e ⊓ principalLevelFrame.isotIn (principalLevelFrame.actM P M) (⨆ N : ℕ, m θ M (principalLevelFrame.levN P (N + 1)) fun _ => 1) π) (goodPart_eq a b) (mult_eq a b)) :))

theorem finTypRep_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S S' : Set (Formalism.L2.NG.FinTyp E n)} (e : S = S')
    (σ : Formalism.L2.Col.FinTypCls S) :
    Formalism.L2.Col.finTypRep S σ = Formalism.L2.Col.finTypRep S' (cast (congrArg Formalism.L2.Col.FinTypCls e) σ) := by
  subst e
  rfl

section General

variable {D : D7} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def topW (m : type_of% (@MultT D)) (R : RealDat D A Ks) : Prop :=
  ∀ t, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) = m R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))

abbrev ccJ (m : type_of% (@MultT D)) (R : RealDat D A Ks) (t : T) (j : ℕ) : Submodule ℂ (AmbT (R.MY j)) :=
  m R.θ (R.MY j) (if j < D.R.m then levS _ (R.βY j) (R.datYt t j R.triv) else Set.univ)
    (if j < D.R.m then levChi _ (R.βY j) (R.datYt t j R.triv) else 0)

def ioCW (m : type_of% (@MultT D)) (R : RealDat D A Ks) (y : IoYT (@m) R) (t : T) (k : ℕ) :
    ccJ (@m) R t (k + 1) →ₗ[ℂ] ccJ (@m) R t k :=
  if h : k + 1 < D.R.m then
    (LinearEquiv.ofEq _ _ (by simp only [ccJ, if_pos (show k < D.R.m by omega)])).toLinearMap ∘ₗ
      y t k ∘ₗ (LinearEquiv.ofEq _ _ (by simp only [ccJ, if_pos h])).toLinearMap
  else 0

def ioXW (m : type_of% (@MultT D)) (R : RealDat D A Ks) (x : IoXT (@m) R) (hm : 0 < D.R.m) (hT : topW (@m) R) (t : T) :
    m R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t)) →ₗ[ℂ] ccJ (@m) R t (D.R.m - 1) :=
  (LinearEquiv.ofEq _ _ (by simp only [ccJ, if_pos (show D.R.m - 1 < D.R.m by omega)])).toLinearMap ∘ₗ
    x t ∘ₗ (LinearEquiv.ofEq _ _ (hT t).symm).toLinearMap

def ioOKW (m : type_of% (@MultT D)) (Ch : ChainReal D) (c : Bool) (μ : D.what₂.Tup)
    (y : ∀ k, m Ch.θ (Ch.MY (k + 1)) (Ch.J c μ (k + 1)) (Ch.χ c μ (k + 1)) →ₗ[ℂ] m Ch.θ (Ch.MY k) (Ch.J c μ k) (Ch.χ c μ k))
    (x : m Ch.θ Ch.MX (Ch.JX c μ) (Ch.χX c μ) →ₗ[ℂ] m Ch.θ (Ch.MY (D.R.m - 1)) (Ch.J c μ (D.R.m - 1)) (Ch.χ c μ (D.R.m - 1))) :
    Prop :=
  Lift.IsChainIo (G := fun j => GA D (Ch.Y j)) (D := fun j => ⨂[ℂ] τ, (Ch.MY j).sm τ)
    (fun j => m Ch.θ (Ch.MY j) (Ch.J c μ j) (Ch.χ c μ j)) (D.R.m - 1) (Ch.meas c μ) (Ch.fd μ) (Ch.th μ) (Ch.pt c μ) Ch.It y ∧
  (1 ≤ D.R.m → Lift.IsIo (Ch.measX c μ) (Ch.fdX μ) (Ch.thX μ) (Ch.ptX c μ) Ch.ItX (m Ch.θ Ch.MX (Ch.JX c μ) (Ch.χX c μ))
    (m Ch.θ (Ch.MY (D.R.m - 1)) (Ch.J c μ (D.R.m - 1)) (Ch.χ c μ (D.R.m - 1))) x)

end General

variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Chain

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks}

theorem topMult_tr (h : TopMultH R) : letI := alg b iK; TopMultH (real b R) := by
  tr_via (fun m : type_of% (@MultT a.D) => topW (@m) R) (multT_eq b a) h

variable (F : Face a.D A) (tupT : a.D.what₂.Tup → T) (hm : 0 < a.D.R.m) (hTop : TopMultH R)

abbrev chainB : ChainReal b.D :=
  @toChainReal b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) (face b F) ((by with_unfolding_all exact (tupT :))) ((by with_unfolding_all exact (hm :))) (topMult_tr b hTop)

theorem chain_EEc : (toChainReal R F tupT hm hTop).EEc = ((chainB b F tupT hm hTop).EEc) :=
  (by with_unfolding_all exact ((congrArg (fun (g : type_of% (@goodPart a.D)) (c : Bool) =>
    (g R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F c))) (levChi _ (R.βY 0) (R.dat0 (R.levR F c))) R.e0).map
      (PiTensorProduct.lift : MMap (R.MY 0) ≃ₗ[ℂ] AmbT (R.MY 0)).toLinearMap) (goodPart_eq b a)) :))

theorem chain_CC : (toChainReal R F tupT hm hTop).CC = ((chainB b F tupT hm hTop).CC) :=
  (by with_unfolding_all exact ((congrFun (congrArg (fun (m : type_of% (@MultT a.D)) (Ch : ChainReal a.D) => fun c μ j => m Ch.θ (Ch.MY j) (Ch.J c μ j) (Ch.χ c μ j)) (multT_eq b a) :)
    (toChainReal R F tupT hm hTop)) :))

theorem chain_CCP : (toChainReal R F tupT hm hTop).CCP = ((chainB b F tupT hm hTop).CCP) :=
  (by with_unfolding_all exact ((congrFun (congrArg (fun (m : type_of% (@MultT a.D)) (Ch : ChainReal a.D) => fun c μ j => m Ch.θ (Ch.MY j) (Ch.JP c μ j) (Ch.χP c μ j)) (multT_eq b a) :)
    (toChainReal R F tupT hm hTop)) :))

theorem chain_CCX : (toChainReal R F tupT hm hTop).CCX = ((chainB b F tupT hm hTop).CCX) :=
  (by with_unfolding_all exact ((congrFun (congrArg (fun (m : type_of% (@MultT a.D)) (Ch : ChainReal a.D) => fun c μ => m Ch.θ Ch.MX (Ch.JX c μ) (Ch.χX c μ)) (multT_eq b a) :)
    (toChainReal R F tupT hm hTop)) :))

theorem chain_CCXP : (toChainReal R F tupT hm hTop).CCXP = ((chainB b F tupT hm hTop).CCXP) :=
  (by with_unfolding_all exact ((congrFun (congrArg (fun (m : type_of% (@MultT a.D)) (Ch : ChainReal a.D) => fun c μ => m Ch.θ Ch.MX (Ch.JXP c μ) (Ch.χXP c μ)) (multT_eq b a) :)
    (toChainReal R F tupT hm hTop)) :))

theorem chain_ioC (t : T) (k : ℕ) (v : AmbT (R.MY (k + 1))) (hv : v ∈ ccJ (@multTB B C b a) R t (k + 1))
    (hv0 : v ∈ ccJ (@MultT a.D) R t (k + 1)) :
    (ioCW (@multTB B C b a) R (ioYB b R) t k ⟨v, hv⟩).1 = (ioCW (@MultT a.D) R ((R.ioY)) t k ⟨v, hv0⟩).1 :=
  (by with_unfolding_all exact ((cast (io_congr R (multT_eq b a) (fun m y _ => ∀ hv : v ∈ ccJ (@m) R t (k + 1),
    (ioCW (@m) R y t k ⟨v, hv⟩).1 = (ioCW (@MultT a.D) R ((R.ioY)) t k ⟨v, hv0⟩).1) ((R.ioY)) ((R.ioX))) (fun _ => rfl) hv) : _))

theorem chain_ioX (t : T) (v : AmbT R.MX) (hT : topW (@multTB B C b a) R)
    (hv : v ∈ multTB b a R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t)))
    (hv0 : v ∈ MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))) :
    (ioXW (@multTB B C b a) R (ioXB b R) hm hT t ⟨v, hv⟩).1 = (ioXW (@MultT a.D) R ((R.ioX)) hm hTop t ⟨v, hv0⟩).1 :=
  (by with_unfolding_all exact ((cast (io_congr R (multT_eq b a) (fun m _ x => ∀ (hT : topW (@m) R)
      (hv : v ∈ m R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))),
    (ioXW (@m) R x hm hT t ⟨v, hv⟩).1 = (ioXW (@MultT a.D) R ((R.ioX)) hm hTop t ⟨v, hv0⟩).1) ((R.ioY)) ((R.ioX)))
    (fun _ _ => rfl) hT hv) : _))

theorem chain_ioOK {c : Bool} {μ : a.D.what₂.Tup} (h : (chainB b F tupT hm hTop).IoOK c ((μ))) :
    (toChainReal R F tupT hm hTop).IoOK c μ := by
  have e := io_congr R (multT_eq b a) (fun m y x => ∃ hT : topW (@m) R,
    ioOKW (@m) (toChainReal R F tupT hm hTop) c μ ((by with_unfolding_all exact ((ioCW (@m) R y (tupT μ)) :))) ((by with_unfolding_all exact ((ioXW (@m) R x hm hT (tupT μ)) :))))
    ((by with_unfolding_all exact (R.ioY :))) ((by with_unfolding_all exact (R.ioX :)))
  obtain ⟨_, h'⟩ := cast e.symm (Exists.intro ((by with_unfolding_all exact ((topMult_tr b hTop) :))) ((by with_unfolding_all exact (h :))))
  exact (by with_unfolding_all exact (h' :))

variable (hinj : ∀ i t, Function.Injective (R.extV i t))

include hinj in

theorem inj_tr : letI := alg b iK; ∀ i t, Function.Injective ((real b R).extV i t) := (by with_unfolding_all exact (hinj :))

abbrev liftB : LiftReal b.D (chainB b F tupT hm hTop) :=
  (by with_unfolding_all exact ((@toLiftReal b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) (face b F) ((tupT)) ((hm)) (topMult_tr b hTop)
    (inj_tr b hinj)) : _))

theorem lift_Wc : (toLiftReal R F tupT hm hTop hinj).Wc = ((liftB b F tupT hm hTop hinj).Wc) :=
  (by with_unfolding_all exact ((congrFun (congrArg (fun (g : type_of% (@goodPart a.D)) (L : LiftReal a.D (toChainReal R F tupT hm hTop)) => fun i =>
    (g R.θ (L.MW i) (L.JW i) (L.χW i) (L.eW i)).map (PiTensorProduct.lift : MMap (L.MW i) ≃ₗ[ℂ] L.AmbW i).toLinearMap)
    (goodPart_eq b a) :) (toLiftReal R F tupT hm hTop hinj)) :))

theorem lift_MultW : (toLiftReal R F tupT hm hTop hinj).MultW = ((liftB b F tupT hm hTop hinj).MultW) :=
  (by with_unfolding_all exact ((congrFun (congrArg (fun (m : type_of% (@MultT a.D)) (L : LiftReal a.D (toChainReal R F tupT hm hTop)) => fun i =>
    m R.θ (L.MW i) (L.JA i) (L.χA i)) (multT_eq b a) :) (toLiftReal R F tupT hm hTop hinj)) :))

end Chain

end GlobalTheory.Mem.R3.Tr

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.CxPts Formalism.BasicNotions

namespace GlobalTheory.ProjVar.Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv}

end GlobalTheory.ProjVar.Var

namespace GlobalTheory.TrueGeo

def cxSt (F : Type) [Field F] [NumberField F] : CxSt F := ProjVar.cxStage F

variable {F : Type} [Field F] [NumberField F]

theorem cxSt_cx : (cxSt F).cx = Var.cx := rfl

theorem cxSt_pn : (cxSt F).pn = Var.pn := rfl

variable {Y : Var F} {σ : F →+* ℂ} {Δ Δ' : Y.Dv}

example (n : ℕ) (y : Pts (proj F n) σ) : (cxSt F).mSmooth _ σ _ (projMet F σ n) ∧
    ∑ j, (cxSt F).pn _ σ _ (projMet F σ n)
      ((cxSt F).cx _ σ ((proj F n).coordFn (proj_gen_mem F n 0) j)) y = 1 ∧
    ((cxSt F).pn _ σ _ (projMet F σ n) ((cxSt F).cx _ σ 1) y = 0 ↔
      under y ∈ (proj F n).supp (projHyp F n)) := by
  have hy := (mSmooth_projMet F σ n).1 (mem_univ y)
  have he : (projHyp F n).Eff := (proj F n).eff_hyp _
  exact ⟨mSmooth_projMet F σ n, sum_pn_fsMet hy,
    ((pn_eq_zero_iff hy (secReg_cx_iff.2 (he _))).trans secZero_cx_iff).trans he.mem_supp_iff.symm⟩

example (c : ℂ) (y : Pts Y σ) :
    (cxSt F).pn Y σ 0 ((cxSt F).fsMet Y σ 0 fun _ : Unit => c • (cxSt F).cx Y σ 1)
      ((cxSt F).cx Y σ 1) y = 1 / ‖c‖ ^ 2 := by
  have hg : y ∈ eqnSet σ (0 : Y.Dv) 1 := isEqn_zero _
  have h₁ : HasVal y (Y.cx σ 1) 1 := map_one (Y.cx σ) ▸ hasVal_one
  change pn Y σ 0 (fsMet Y σ 0 fun _ : Unit => c • Y.cx σ 1) (Y.cx σ 1) y = _
  rw [pn_fsMet (fun _ => ⟨1, hg, ((h₁.smul c).mul h₁).regC⟩) hg, fval_one, h₁.val_eq]
  simp only [fval_one, (h₁.smul c).val_eq]
  simp

example : ¬ (cxSt F).mSmooth Y σ Δ ((cxSt F).fsMet Y σ Δ (k := Empty) Empty.elim) := fun h =>
  have ⟨y⟩ := nonempty_pts (Y := Y) (σ := σ)
  have ⟨k, _⟩ := (mSmooth_fsMet_iff.1 h y).2
  k.elim

end GlobalTheory.TrueGeo
end
end

