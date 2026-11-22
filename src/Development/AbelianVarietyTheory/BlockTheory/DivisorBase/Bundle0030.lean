import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateLiftSL
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateLiftSL

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable (D) in

def OverK (σ : D.what₂.LL →+* ℂ) : Prop :=
  ∀ a : D.host.K, σ (D.embE (algebraMap D.host.K D.host.E a)) = D.what₂.embLL (D.embE (algebraMap D.host.K D.host.E a))

example : OverK D D.what₂.embLL := fun _ => rfl

def LabPerm (σ : D.what₂.LL →+* ℂ) : Prop :=
  Function.Bijective (lab (D := D) σ) ∧ ∀ ρ, labE σ (lab σ ρ) = tauE D ρ

variable (D) in

def hookSum (i : Fin D.R.m) (l : D.what₂.Tau → D.what₂.Tau) : ℝ :=
  ∑ ρ, (Formalism.BasicNotions.DV.logHook ((Wc D i).sig (tauE D ρ)).1 (fun n => (aPl D i ((Wc D i).sig (tauE D ρ)).1 (l ρ) n : ℝ)) +
    Formalism.BasicNotions.DV.logHook ((Wc D i).sig (tauE D ρ)).2
      (fun n => (aMi D i ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (l ρ) n : ℝ)))

def deltaAtEmb (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : PolF D (Wc D i).rank (Vc D i).rank :=
  delta (fun ρ => ((Wc D i).sig (tauE D ρ)).1) (fun ρ => ((Wc D i).sig (tauE D ρ)).2)
    (fun ρ => aPl D i ((Wc D i).sig (tauE D ρ)).1 (lab σ ρ))
    (fun ρ => aMi D i ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (lab σ ρ))

def IsCompUnit (V : HSp D) (J : Subgroup (GA D V)) (u : GA D V → ℂ) : Prop :=
  (∀ g, ‖u g‖ = 1) ∧ (∀ γ ∈ GQ V, ∀ g, u (γ * g) = u g) ∧ (∀ k ∈ GinfC V, ∀ g, u (g * k) = u g) ∧
    ∀ k ∈ J, ∀ g, u (g * k) = u g

example (V : HSp D) (J : Subgroup (GA D V)) : IsCompUnit V J fun _ => 1 :=
  ⟨fun _ => norm_one, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

section Conj

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  (σ : D.what₂.LL →+* ℂ)

def EtaAt (η' : (AE D)ˣ →* Circle) : Prop :=
  IsHeckeChar D η' ∧ ResEta D η' 1 ∧ (∀ ρ, HasInfExp D η' ρ (1 / 2)) ∧
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.JoinChr.IsPlIdem D e P → ∀ (k : D.host.Eˣ) (x : (AE D)ˣ),
      (x : AE D) = Formalism.L2.JoinChr.locE D e (k : D.host.E) → ∃ y : D.what₂.LL,
        D.what₂.embLL y = ((R.eta x : Circle) : ℂ) * ((Real.sqrt (FinitePlace.mk P (k : D.host.E)) : ℝ) : ℂ) ∧
        σ y = ((η' x : Circle) : ℂ) * ((Real.sqrt (FinitePlace.mk P (k : D.host.E)) : ℝ) : ℂ)

def ResAt (χ' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ PP ∈ R.Pg, ∀ u, ∃ y : D.what₂.LL,
    D.what₂.embLL y = ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) ∧ σ y = ((χ' PP u : ℂˣ) : ℂ)

def datV (χ' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ (Vc D i).rank :=
  datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg (R.Q A.μ0) (LevelP.triv _ _ _) (fun _ => χ') (R.xiR A.μ0) Frm.A

example : datV R i (R.chi ((i : ℕ) + 1)) = R.datVt i A.μ0 := rfl

def valAt (x : A.fam.amb.FL i A.μ0) (c : (A.MtCSD i A.μ0).Cl) : (A.MtCSD i A.μ0).V :=
  ((show (A.MtCSD i A.μ0).Forms from x) : (A.MtCSD i A.μ0).Cl → (A.MtCSD i A.μ0).V) c

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure ConjLift where

  mu : (AE D)ˣ →* Circle

  eta : (AE D)ˣ →* Circle

  chi : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ

  cV : CoefA (Vc D i)

  coef : (A.MtCSD i A.μ0).V →ₛₗ[σ] cV.W

  HV : HMod (Bridge.Gf (Vc D i) → cV.W)

  jV : A.fam.amb.FL i A.μ0 →ₛₗ[σ] HV.H

  om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)

  BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ

  vac : WO (Vc D i) (Wc D i) → ℂ

  vec : WO (Vc D i) (Wc D i) → ℂ

  io : LowT (R.MW i σ) →ₗ[ℂ] cV.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank

  thF : HV.H →ₗ[ℂ] MMap (R.MW i σ)

  thG : HV.H →ₗ[ℂ] (R.HW i σ).H

namespace ConjLift

variable {R i σ} (Y : ConjLift R i σ)

def pt : PolF D (Wc D i).rank (Vc D i).rank → (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) Y.BW Y.vec

def extV : Y.HV.H →ₗ[ℂ] (GA D (Vc D i) → Y.cV.W) := Y.cV.ext ∘ₗ Y.HV.e

abbrev lev : Bridge.LevDat D (Vc D i) := levEnv (Vc D i) (R.βV i) (datV R i Y.chi)

structure IsChr : Prop where
  mu : ChiAt R i σ Y.mu
  eta : EtaAt R σ Y.eta
  chi : ResAt R i σ Y.chi

structure IsSrc : Prop where
  cV : Y.cV.Is
  coef_li : LinearIndependent ℂ fun a => Y.coef ((A.MtCSD i A.μ0).bV a)
  coef_span : Submodule.span ℂ (Set.range fun a => Y.coef ((A.MtCSD i A.μ0).bV a)) = ⊤
  coef_pair : ∀ a b, inner ℂ (Y.coef ((A.MtCSD i A.μ0).bV a)) (Y.coef ((A.MtCSD i A.μ0).bV b)) =
    σ ((A.MtCSD i A.μ0).pair ((A.MtCSD i A.μ0).bV a) ((A.MtCSD i A.μ0).bV b))
  coef_rat : ∀ (γ : GQ (Vc D i)) (x x' : (A.MtCSD i A.μ0).V),
    (R.B.L i A.μ0).pres.coef x' = (R.cV i).coef.ρ γ ((R.B.L i A.μ0).pres.coef x) → Y.coef x' = Y.cV.coef.ρ γ (Y.coef x)
  HV : Y.HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) Y.cV.coef.ρ Y.lev.J Y.lev.χ)
    (Bridge.adInner (Bridge.ratF (Vc D i)) Y.lev.J (R.B.L i A.μ0).pres.y)
  jV : ∀ x c, Y.HV.e (Y.jV x) ((R.B.L i A.μ0).pres.y c) = Y.coef (valAt i x c)

structure IsLift : Prop where
  om : IsWeilDatumO R.ψ (Vc D i) (Wc D i) Y.mu (Y.mu * Y.eta⁻¹) Y.om
  BW : ∀ ρ, IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (Y.BW ρ) ((Wc D i).sig (tauE D ρ)).1
  vec : IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
    R.Pg (R.Q A.μ0) (R.xiR A.μ0) Y.vac Y.vec
  pt : ∀ P, IsThetaFunO R.ψ (Vc D i) (Wc D i) (Y.pt P)
  io : IsIoW R.θ (R.MW i σ) Y.cV Y.om Y.pt (deltaAtEmb i σ) Y.io
  thF_mem : ∀ x, Y.thF x ∈ R.Wall i σ
  thF : ∃ thP, Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h f => thetaKO Y.om h g f) Y.pt Y.io
      (LinearMap.range Y.extV) thP ∧
    ∀ x (v : ∀ ρ, lowT (R.MW i σ) ρ),
      Y.thF x (fun ρ => v ρ) = thP (Y.extV.rangeRestrict x) (PiTensorProduct.tprod ℂ v)
  thG : ∀ x, (R.HW i σ).e (Y.thG x) = postOn _ (R.eWf i σ) (Y.thF x)

structure Is : Prop where
  chr : Y.IsChr
  src : Y.IsSrc
  lift : Y.IsLift

end ConjLift

structure IsCentralTr (z : G) : Prop where
  center : z ∈ Subgroup.center G
  lift : ∃ (k : GA D (Wc D i)) (e : AE D), IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) k ∧
    k ∈ Subgroup.center (GA D (Wc D i)) ∧ IsIdemSum e R.Pg ∧ SuppAt e (Wc D i) k ∧
    ∀ x v g, (R.HW i σ).e (R.gW i σ z x) v g = (R.HW i σ).e x v (g * k)
  unitary : ∀ x y, inner ℂ (R.gW i σ z x) (R.gW i σ z y) = inner ℂ x y
  comm_fin : ∀ g x, R.gW i σ z (R.gW i σ g x) = R.gW i σ g (R.gW i σ z x)
  comm_hecke : ∀ S : Finset (GA D (Wc D i)), (∀ γ ∈ S, γ ∈ GfC (Wc D i)) → ∀ x y,
    (R.HW i σ).e y = heckeOn (R.MW i σ) S ((R.HW i σ).e x) →
      (R.HW i σ).e (R.gW i σ z y) = heckeOn (R.MW i σ) S ((R.HW i σ).e (R.gW i σ z x))

def IsRatLift (ph : ℂ) (th : A.fam.amb.FL i A.μ0 →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  ∀ x, (R.FW i).j (sg0 D A) (th x) = ph • R.thG i A.μ0 (R.jV i A.μ0 x)

variable {R i σ} in

def ConjLift.Ident (Y : ConjLift R i σ) (th : A.fam.amb.FL i A.μ0 →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  ∃ (κ : ℂ) (z : G) (u : GA D (Wc D i) → ℂ), ‖κ‖ = 1 ∧ IsCentralTr R i σ z ∧
    IsCompUnit (Wc D i) (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) u ∧
    ∀ x v g, u g * (R.HW i σ).e ((R.FW i).j σ (th x)) v g = κ * (R.HW i σ).e (R.gW i σ z (Y.thG (Y.jV x))) v g

def GalAt (th : A.fam.amb.FL i A.μ0 →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  LabPerm (D := D) σ ∧ hookSum D i (lab σ) = hookSum D i id ∧
    (∃ Y : ConjLift R i σ, Y.Is) ∧ ∀ Y : ConjLift R i σ, Y.Is → Y.Ident th

end Conj

def GalD (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) : Prop :=
  R.Char F → ∀ t : FWTie T R κ v₀,
    (∀ (i : Fin D.R.m) (ph : ℂ), OMPins T R κ v₀ O i →
      (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph →
        (∃ th, IsRatLift R i ph th) ∧ ∀ th, IsRatLift R i ph th → ∀ σ, OverK D σ → GalAt R i σ th) ∧
    (∀ σ, OverK D σ ∨ OverK D ((starRingEnd ℂ).comp σ)) ∧
    (BarTie t → JConj R)

section Base

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def castSL {K X Z : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Z] [Module ℂ Z] {s s' : K →+* ℂ} (h : s = s')
    (f : X →ₛₗ[s] Z) : X →ₛₗ[s'] Z where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := by rw [← h]; exact f.map_smulₛₗ a x

include R in
theorem sign_at_base_place_eq_embedding : D.what₂.embLL = sg0 D A := (sgAt_mk _ R.hv0).symm

def base : ConjLift R i (sg0 D A) where
  mu := R.toLevCh.mu A.μ0 ((i : ℕ) + 1)
  eta := R.eta
  chi := R.chi ((i : ℕ) + 1)
  cV := R.cV i
  coef := castSL (sign_at_base_place_eq_embedding R) (R.B.L i A.μ0).pres.coef
  HV := R.HV i A.μ0
  jV := castSL (sign_at_base_place_eq_embedding R) (R.jV i A.μ0)
  om := R.ωP i A.μ0
  BW := onb (R.MW i (sg0 D A))
  vac := R.vacP i
  vec := R.vP i A.μ0
  io := R.ioP i
  thF := R.thF i A.μ0
  thG := R.thG i A.μ0

end Base

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateLiftSL
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.IotaEmbeddingColumns
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.IotaEmbeddingColumns

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable (D) in

def fieldLL : IntermediateField ℚ ℂ := D.what₂.embLL.toRatAlgHom.fieldRange

def iotaW (T : CoreJ D) (i : Fin D.R.m) :
    (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

section Row

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def RowAt (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) {Tup : Type} (tup : Tup → T0)
    (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) : Prop :=
  ∃ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (jL : D.what₂.LL →+* c'.F)
    (c0' : VsV D i c'.F →ₛₗ[c'.F.val.toRingHom] (R.cV i).W)
    (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) ×
      ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))
    (io : VVc c' (lamV D i) →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F) (hw : VVc c' (lamV D i))
    (dδ : Tup → DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank)
    (U₂ : ∀ s, Unf (dδ s).Xo₂ (dδ s).c₂
      (c'.F.val.toRingHom.comp ((dδ s).eF.symm : (dδ s).c₂.F →+* c'.F)) D.R.r)
    (dict₂ : ∀ s, GA D (Wc D i) → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U₂ s).X k).Ψ D.R.r)
    (Cl : Tup → Type) (_ : ∀ s, Fintype (Cl s)) (bad : Tup → ℕ)
    (Lh : ∀ s, Cl s → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (La : ∀ s, Cl s → GenLat D.host.E (Vc D i).rank) (Nc gam : ∀ s, Cl s → ℕ) (vol : Tup → c'.F)
    (ep : ∀ s, Cl s → c'.F) (B : Tup → Ideal (𝓞 D.host.E) → c'.F)
    (epF : Tup → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E) → c'.F)
    (xi : Tup → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (φ : ∀ s, (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) (dδ s).l₂) → c'.F)
    (w : ∀ s, Cl s → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (dδ s).l₂) → c'.F)
    (thAd : ∀ s, (Cl s → VsV D i c'.F) → AutQ (Wc D i) → ℂ) (Plc : ∀ s, (Cl s → VsV D i c'.F) → Prop),
    ThPinsR R i jL c'.F.val.toRingHom (v₀ i (sg0 D A)) c0' (iotaW T i) T.Q.l.M (Mfr T.Q.l) (fun g => (lev g).1) ∧
    (∀ s, ThPinsT R i c'.F.val.toRingHom (tup s) (v₀ i (sg0 D A)) c0' (iotaW T i) (bad s) T.Q.l.Mb (dδ s).I
      (Mfr (dδ s).l₂ • ⊤) (Lh s) (gam s) (vol s) (B s) (xi s) (φ s) (thAd s) (Plc s)) ∧
    OneMapTieP hle (fieldLL D) (T.U ((i : ℕ) + 1)) c'.F.val.toRingHom (Wc D i) (rank_Wc i)
      (castDict hV (T.dict ((i : ℕ) + 1) T.toCore.σ₀)) (castDict hV (T.mu ((i : ℕ) + 1) T.toCore.σ₀)) (xiR D) (wtA (κ i)) lev
      dδ Cl bad Lh La Nc gam vol ep B epF (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1) (tauE D) (lamV D i) io hw φ w U₂ dict₂
      (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) xi thAd Plc cc ph

def RowBase (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i)
    (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) : Prop :=
  RowAt T R κ v₀ i hV (fun _ : Unit => A.μ0) cc ph

def RowAll (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i)
    (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) : Prop :=
  RowAt T R κ v₀ i hV (fun t : T0 => t) cc ph

def PlaceGuard : Prop :=
  (∀ t, ∀ PP ∈ R.Q t, ∀ PP' ∈ R.Q t, PP.asIdeal.under ℤ = PP'.asIdeal.under ℤ →
      PP.asIdeal.under (𝓞 D.host.K) = PP'.asIdeal.under (𝓞 D.host.K)) ∧
    ∀ t PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

def HalfTie : Prop := T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal

def ConstTie : Prop :=
  ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i),
    (∃ cc ph, RowAll T R κ v₀ i hV cc ph) → ∃ ph, RowAll T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) ph

def PhaseAtBase (phs : Fin D.R.m → ℂ) : Prop :=
  ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i),
    (∃ ph, RowBase T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) ph) →
      RowBase T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (phs i)

def BaseNonzero : Prop :=
  ∀ i : Fin D.R.m, ∃ x₀ : A.fam.amb.FL i A.μ0,
    onQ (Wc D i) (R.thF i A.μ0 (jVx R i A.μ0 x₀) (v₀ i (sg0 D A))) ≠ 0

def Ties (F : Face D A) : Prop :=
  R.Char F ∧ TieIn T R κ v₀ ∧ (∀ i, VStd D i) ∧ HalfTie T R

def OneMapFree (F : Face D A) : Prop :=
  Ties T R κ v₀ F → PlaceGuard T R →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i), ∃ cc ph, RowAll T R κ v₀ i hV cc ph

def OneMapAll (F : Face D A) (phs : Fin D.R.m → ℂ) : Prop :=
  Ties T R κ v₀ F → ConstTie T R κ v₀ → PhaseAtBase T R κ v₀ phs → BaseNonzero T R v₀ → PlaceGuard T R →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i),
      RowAll T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (phs i)

theorem space_eq {F : Face D A} (h : Ties T R κ v₀ F) (i : Fin D.R.m) : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i :=
  h.2.1.laws.spaceW _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀

theorem RowAt.norm {i : Fin D.R.m} {hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i} {Tup : Type} {tup : Tup → T0}
    {cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ} {ph : ℂ} (h : RowAt T R κ v₀ i hV tup cc ph) :
    (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h
  have h1 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact ⟨h1.1, h1.2.1⟩

end Row

end GlobalTheory.IndefiniteRowSideFullHecke.IotaEmbeddingColumns
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
open scoped ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def dimAt (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) : ℝ :=
  ((dimK _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) τ) : ℚ) : ℝ)

def ratio (D : D7) (i : Fin D.R.m) (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) : ℝ :=
  (μ 𝓕).toReal * ∏ τ, dimAt D i τ

def wtSize (D : D7) (i : Fin D.R.m) : ℝ :=
  ∑ τ, ∑ a, |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ)|

def Sizes (D : D7) (L : ℝ) : Prop :=
  (D.R.f : ℝ) * D.R.r * D.R.nV ≤ Real.exp L ∧ (∀ i, wtSize D i ≤ Real.exp L ^ 2) ∧
    Real.log ((D.host.g 0 : ℝ) * D.host.g 1) ≤ 30 * L ∧ Real.log D.host.rdE + |dlogL D 1| ≤ 2 * L

variable {D : D7}

abbrev levW {Tu : Type} (C : LevCh D Tu) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) :
    Subgroup (GL (Fin (Wc D i).rank) (Formalism.IndefR.Lev.EAf D)) :=
  lev D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P)

abbrev formsW {Tu : Type} (C : LevCh D Tu) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (θ : InfFam D)
    {S : D.what₂.Tau → SPar} (M : DSModel (Wc D i) S) : Submodule ℂ (MMap M) :=
  Mult θ M (levS _ (C.βW i) (C.datWp i P)) (levChi _ (C.βW i) (C.datWp i P))

def expW (D : D7) (i : Fin D.R.m) : WTZ D.host.E := wtZ (wtA (kapTop D i)) (kapTop D i).n

variable (T : CoreJ D) (i : Fin D.R.m)

def scalarForms (s : T.Q.c.F →+* ℂ) : Submodule ℂ (FDSec (T.U ((i : ℕ) + 1) s).X) :=
  holSub (T.U ((i : ℕ) + 1) s).X (modelWt (T.U ((i : ℕ) + 1) s) (expW D i))

def probSq (s : T.Q.c.F →+* ℂ) (f : FDSec (T.U ((i : ℕ) + 1) s).X) : ℝ :=
  (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (expW D i) *
    (petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s))
      (modelWt (T.U ((i : ℕ) + 1) s) (expW D i)) f).toReal) ^ 2

def adFun {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) (f : FDSec (T.U ((i : ℕ) + 1) s).X) :
    GA D (Wc D i) → ℂ :=
  hV ▸ ((lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (expW D i) : ℂ) •
    adel (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s)
      (muPin (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (T.mu ((i : ℕ) + 1) s) (T.cE ((i : ℕ) + 1) s)) f)

theorem probSq_rdU (s : T.Q.c.F →+* ℂ) (f : T.R ((i : ℕ) + 1)) :
    probSq T i s (rdU (T.U ((i : ℕ) + 1) s) f) =
      petAt (T.U ((i : ℕ) + 1) s) (xiR D) (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s)
        (muQ1 (T.V ((i : ℕ) + 1) s)) (expW D i) f ^ 2 := rfl

theorem adFun_rdU {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) (f : T.R ((i : ℕ) + 1)) :
    adFun T i hV (rdU (T.U ((i : ℕ) + 1) s) f) = phiC T hV (wtA (kapTop D i)) f := by
  unfold adFun phiC CoreJ.phiJ expW
  rw [lieFacZ_wtZ]

variable [Algebra T.Q.c.F D.what₂.LL]

abbrev gd (σ : D.what₂.LL →+* ℂ) : T.Q.c.F →+* ℂ := goodOf T.Q.c (res T σ)

def Corr (σ : D.what₂.LL →+* ℂ) (hV : T.V ((i : ℕ) + 1) (gd T σ) = Wc D i) {M : DSModel (Wc D i) (parAt (Wc D i) σ)}
    (F : MMap M) (f : FDSec (T.U ((i : ℕ) + 1) (gd T σ)).X) : Prop :=
  (GoodEmb T.Q.c (res T σ) ∧ ∃ v, IsExtVec M v ∧ F v = adFun T i hV f) ∨
    (¬ GoodEmb T.Q.c (res T σ) ∧ ∃ v : M.Vec, IsUnitV v ∧ F v = fun g => conj (adFun T i hV f g))

def ExactRatio {Tu : Type} (C : LevCh D Tu) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ)
    (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) : Prop :=
  ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL], LawsJ T → AlgTie T → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (σ : D.what₂.LL →+* ℂ) (M : DSModel (Wc D i) (parAt (Wc D i) σ)) (hV : T.V ((i : ℕ) + 1) (gd T σ) = Wc D i),
      ∀ F ∈ formsW C i P θ M, ∀ f ∈ scalarForms T i (gd T σ), Corr T i σ hV F f →
        (∃ c, IsMultIP M μ 𝓕 F F c) ∧ ipAt M μ 𝓕 F F = ((ratio D i μ 𝓕 * probSq T i (gd T σ) f : ℝ) : ℂ)

def RatioBound (i : Fin D.R.m) (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (L : ℝ) : Prop :=
  (∀ τ, Real.log (dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L) ∧
    Real.log (μ 𝓕).toReal ≤ D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) + (38 + 81) * (D.R.f * (D.R.r : ℝ) ^ 2 * L) ∧
    Real.log (ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L)

def IndexBound {Tu : Type} (C : LevCh D Tu) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) : Prop :=
  (levW C i P).relIndex (levW C i (LevelP.full _ _ _)) ≠ 0 ∧
    Real.log ((levW C i P).relIndex (levW C i (LevelP.full _ _ _))) ≤
      2 * D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.host.g 0 : ℝ) * D.host.g 1)

def OneMeasure (D : D7) : Prop :=
  ∀ (Tu : Type) (C : LevCh D Tu) (t0 : Tu), C.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ),
    IndexBound C i P ∧ (∀ τ, 1 ≤ dimAt D i τ) ∧
      ∀ (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))), IsMeasFD (Wc D i) (levW C i P) μ 𝓕 →
        μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ ExactRatio C i P μ 𝓕 ∧ ∀ L, Sizes D L → RatioBound i μ 𝓕 L

omit [Algebra T.Q.c.F D.what₂.LL] in

theorem OneMeasure.models (h : OneMeasure D) {G : Type} [Group G] [Fintype G] {Pl0 Tu : Type}
    {A : FamIn D.what₂.LL G Pl0 Tu D.R.m} [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hT : LawsJ T) (ha : AlgTie T) (large₂ : SizeData₂ D) (hs : Sizes D large₂.sc.L)
    (n : ℝ) (hn : 1 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ Real.log c ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * large₂.sc.L) ∧
      ∀ (σ : D.what₂.LL →+* ℂ) (hV : T.V ((i : ℕ) + 1) (gd T σ) = Wc D i) (x : (R.HW i σ).H),
        ∀ f ∈ scalarForms T i (gd T σ), Corr T i σ hV ((R.HW i σ).e x) f →
          n⁻¹ * ‖x‖ ^ 2 = c * probSq T i (gd T σ) f := by
  obtain ⟨-, hdim, hmeas⟩ := h Tu R.toLevCh A.μ0 hl i R.toLevCh.triv
  obtain ⟨h0, htop, hex, hbd⟩ := hmeas (R.νW i) (R.fdW i) (hm.νW i)
  have hpos : 0 < ratio D i (R.νW i) (R.fdW i) :=
    mul_pos (ENNReal.toReal_pos h0 htop) (Finset.prod_pos fun τ _ => lt_of_lt_of_le one_pos (hdim τ))
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  obtain ⟨-, -, hb3⟩ := hbd large₂.sc.L hs
  refine ⟨ratio D i (R.νW i) (R.fdW i) / n, div_pos hpos hn0, ?_, ?_⟩
  · exact (Real.log_le_log (div_pos hpos hn0) (div_le_self hpos.le hn)).trans hb3
  · intro σ hV x f hf hcorr
    have hmem : (R.HW i σ).e x ∈ R.Wall i σ := by
      rw [← (hm.HW i σ).2.1]
      exact LinearMap.mem_range_self _ x
    have hip := (hex T hT ha R.θ hm.inf σ (R.MW i σ) hV _ hmem f hf hcorr).2
    have hnorm : ((‖x‖ ^ 2 : ℝ) : ℂ) =
        ((ratio D i (R.νW i) (R.fdW i) * probSq T i (gd T σ) f : ℝ) : ℂ) := by
      rw [← hip, ← (hm.HW i σ).2.2 x x, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [Complex.ofReal_injective hnorm]
    ring

end GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes
end
end

