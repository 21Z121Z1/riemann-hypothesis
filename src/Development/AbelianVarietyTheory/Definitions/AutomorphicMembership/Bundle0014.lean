import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll
import Formalism.LocalToGlobal.HermitianForms.Bundle0007
import Formalism.LocalToGlobal.KernelLattices.Bundle0004
import Formalism.LocalToGlobal.KernelLattices.KerMtPin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
section
noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def TopPt (u : B.Word) (a : I.ι) (k : GA B (B.R.N B.R.m)) : Prop :=
  ∀ (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
    IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
    PtOf (g * k) (tilF I.sel (I.tup a) u d)

def ReadsTop (u : B.Word) (a : I.ι) {Ch : Type} (chOf : (I.stp u a B.R.m).Cl → Ch)
    (Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)) (U : Ch → Subgroup (GA B (B.R.N B.R.m))) (chi : ∀ β, U β →* ℂˣ)
    (y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)) (st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E) : Prop :=
  ∃ k, I.Reads u a B.R.m chOf Lb U chi y st k ∧ ∀ β, I.TopPt l Z u a (k β)

set_option maxHeartbeats 800000 in

theorem ReadsTop.mem_chi {u : B.Word} {a : I.ι} {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)} {st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E}
    (h : I.ReadsTop l Z u a chOf Lb U chi y st) (c : (I.stp u a B.R.m).Cl) (d : XPt (B.primes X) B.R I.sel (I.tup a))
    (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)) (hc : ((I.stp u a B.R.m).rep c).1.1 = tilF I.sel (I.tup a) u d) (hd : PtOf g' d)
    (hg : IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1) :
    ∃ hm : g⁻¹ * y c ∈ U (chOf c), chi (chOf c) ⟨_, hm⟩ = 1 := by
  obtain ⟨k, hR, hk⟩ := h
  have h1 : (I.stp u a B.R.m).act c.1 1 ((I.stp u a B.R.m).rep c) = (I.stp u a B.R.m).rep c :=
    @one_smul _ _ _ ((I.stp u a B.R.m).actD c.1) _
  have e : y c * ((y c)⁻¹ * g) * k (chOf c) = g * k (chOf c) := by group
  have hq : PtOf (y c * ((y c)⁻¹ * g) * k (chOf c)) ((I.stp u a B.R.m).act c.1 1 ((I.stp u a B.R.m).rep c)).1.1 := by
    rw [e, h1, hc]
    exact hk _ d g' g hd hg
  have hx : (y c)⁻¹ * g ∈ U (chOf c) := (hR.lev c _ _ hq).2 ⟨1, map_one _, rfl, by rw [h1]⟩
  have hχ := hR.chr c ⟨_, hx⟩ 1 (map_one _) hq
  rw [map_one, Units.val_one, map_one] at hχ
  have e2 : g⁻¹ * y c = ((y c)⁻¹ * g)⁻¹ := by group
  refine ⟨e2 ▸ inv_mem hx, ?_⟩
  have e3 : (⟨g⁻¹ * y c, e2 ▸ inv_mem hx⟩ : U (chOf c)) = (⟨_, hx⟩ : U (chOf c))⁻¹ := Subtype.ext e2
  rw [e3, map_inv, inv_eq_one]
  exact Units.ext hχ

theorem ReadsTop.topBase {u : B.Word} {a : I.ι} {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)} {st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E}
    (h : I.ReadsTop l Z u a chOf Lb U chi y st) (β : Ch) (hβ : ∀ c, U (chOf c) = U β) : I.TopBase l Z u a (U β) y :=
  fun c d g' g hc hd hg => hβ c ▸ (h.mem_chi I l Z c d g' g hc hd hg).1

def ReadsKTop (u : B.Word) (a : I.ι) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a B.R.m).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad B.R.m le_rfl (fun c : {c // chOf c = β} => (I.chain l u a).stab B.R.m c.1)
      (fun c => latCrd (I.rec7 l Z) B.R.m le_rfl (I.latAt u a B.R.m c.1))) : Prop :=
  I.ReadsTop l Z u a chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
    (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1)

theorem ReadsKTop.readsK {u : B.Word} {a : I.ι} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad B.R.m le_rfl (fun c : {c // chOf c = β} => (I.chain l u a).stab B.R.m c.1)
      (fun c => latCrd (I.rec7 l Z) B.R.m le_rfl (I.latAt u a B.R.m c.1))} (h : I.ReadsKTop l Z u a chOf K) :
    I.ReadsK l Z u a B.R.m le_rfl chOf K :=
  h.imp fun _ hk => hk.1

section Tw

variable (l0 : I.Law0 l) {inQ : (I.rec7 l Z).what₂.Tup → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}

structure StdP {W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F} {Lv : SymmetricTwistedLevelData W} (P : TwPTiedS Lv) (E : TwPEvzS P) : Prop where

  what₂ : ∀ u a ha, I.ReadsP a (P.cls u a ha).lev.Lb (P.cls u a ha).lev.U (P.cls u a ha).lev.chi (fun c => ((P.cls u a ha).y c).1)
    (P.cls u a ha).lat fun c s => ((P.cls u a ha).stabI c s).1

  eW : ∀ u a ha z c (s : FrP (I.rec7 l Z)) s', s'.1 = s.1 → (P.val u a ha).eW z c s = z c s'

  z0 : ∀ u a ha h1, (P.til u a ha h1).z0 = TC.z0 X u

  eWz : ∀ u a z, E.eWz u a z = z

def TopK (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F) : Prop := ∀ u a (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m),
  I.ReadsTop l Z u a (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
    (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
    (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
    (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1)

variable {I l Z l0} {W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F} {Lv : SymmetricTwistedLevelData W}

theorem StdP.lat_eq {P : TwPTiedS Lv} {E : TwPEvzS P} (h : I.StdP l Z l0 P E) (u a ha) (c : (I.stX a).Cl) :
    (P.cls u a ha).lat c = ((I.stX a).rep c).1.1.deco.1.N :=
  (h.what₂ u a ha).lat c

theorem StdP.unique {P P' : TwPTiedS Lv} {E : TwPEvzS P} {E' : TwPEvzS P'} (h : I.StdP l Z l0 P E) (h' : I.StdP l Z l0 P' E') (u a) :
    E.eWz u a = E'.eWz u a ∧ ∀ ha, (∀ c, (P.cls u a ha).lat c = (P'.cls u a ha).lat c) ∧
      ∀ h1, (P.til u a ha h1).z0 = (P'.til u a ha h1).z0 :=
  ⟨LinearEquiv.ext fun z => (h.eWz u a z).trans (h'.eWz u a z).symm,
    fun ha => ⟨fun c => (h.lat_eq u a ha c).trans (h'.lat_eq u a ha c).symm,
      fun h1 => (h.z0 u a ha h1).trans (h'.z0 u a ha h1).symm⟩⟩

end Tw

def StdTw (l0 : I.Law0 l) {cf : Formalism.L2.Host.CharFrame (I.rec7 l Z)} {nch : NChoice (I.rec7 l Z)}
    {tp : Formalism.L2.Host.TupTied (I.rec7 l Z) cf nch} {C : ColsTiedSym (I.rec7 l Z)} (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)) : Prop :=
  I.StdW l Z l0 t.forms ∧ I.StdLv l Z l0 t.lv ∧ I.StdP l Z l0 t.pt t.ptE

def EntOk {D : D7} {Y : DivX D} {Tw : TwForms D} (E : KerEnt D Y Tw) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  (∃ kf : ∀ u μ w, LevFree Y u μ w → GL3Columns.KFTie E (O u μ) w, ∀ u μ w (h : LevFree Y u μ w), (kf u μ w h).UnIs) ∧ AdaptedTh E O

example (u : B.Word) (j : Fin (B.R.N B.R.m)) (hj : j.1 + 1 = B.R.N B.R.m) :
    TC.z0 X u j = ((X.piT u : 𝓞 B.host.E) : B.host.E) := if_pos hj

example (u : B.Word) (j : Fin (B.R.N B.R.m)) (hj : j.1 + 1 ≠ B.R.N B.R.m) : TC.z0 X u j = 0 := if_neg hj

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoExV
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

def GeoExV (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL]
    (F : Face D A3.A) : Prop :=
  ∀ (R : RealDat D A3.A C.Q.c.F) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Formalism.L2.Host.ValLL D R.C → GlobalTheory.RealGeo.PreChar R → R.grp_levels F → C.pb = R.C.P.pb →
    Keep (A3 := A3) R F cG → ∃ dict mu chiW x₀ cE nW FW,
      (R.upd5 nW FW R.mu R.twPl R.err0).grp_chiW ∧
      Nonempty (@GlobalTheory.RealGeo.GeoHalf D G _ _ Pl0 T A3.A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE)
        (inferInstanceAs (Algebra C.Q.c.F D.what₂.LL)) (R.upd5 nW FW R.mu R.twPl R.err0) fun _ => 1) ∧
      ∀ i x, ∃ y, (FW i).j (sg0 D A3.A) y = R.thG i A3.A.μ0 (R.jV i A3.A.μ0 x)

theorem GeoEx.geoExV {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL]
    {F : Face D A3.A} (h : GeoEx A3 C F) : GeoExV A3 C F := fun R cG _ => h R cG

end GlobalTheory.Mem.R3
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle
open scoped Matrix

namespace GlobalTheory.GoodMetric

variable {ι : Type} {m : ι → ℕ}

abbrev EntIx (m : ι → ℕ) : Type := Σ τ, Fin (m τ) × Fin (m τ)

def evEnt {M : ℕ} (P : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ)) {R : Type} [CommRing R] (A : Mat m R) :
    Matrix (Fin M) (Fin M) R :=
  P.map (aeval fun v : EntIx m => A v.1 v.2.1 v.2.2)

structure PolyRep (m : ι → ℕ) : Type where

  M : ℕ

  ent : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ)
  one : ∀ (R : Type) [CommRing R], evEnt ent (1 : Mat m R) = 1
  mul : ∀ (R : Type) [CommRing R] (A B : Mat m R), evEnt ent (A * B) = evEnt ent A * evEnt ent B
  transp : ∀ (R : Type) [CommRing R] (A : Mat m R), evEnt ent (fun τ => (A τ)ᵀ) = (evEnt ent A)ᵀ

namespace PolyRep

def ev (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) : Matrix (Fin ρ.M) (Fin ρ.M) R := evEnt ρ.ent A

def lie [Fintype ι] (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) : Matrix (Fin ρ.M) (Fin ρ.M) R :=
  Matrix.of fun i j => ∑ v : EntIx m,
    aeval (fun w : EntIx m => (1 : Mat m R) w.1 w.2.1 w.2.2) (pderiv v (ρ.ent i j)) * A v.1 v.2.1 v.2.2

def proj (m : ι → ℕ) (τ : ι) : PolyRep m where
  M := m τ
  ent := Matrix.of fun i j => X ⟨τ, (i, j)⟩
  one R _ := by ext i j; simp [evEnt]
  mul R _ A B := by ext i j; simp [evEnt, Matrix.mul_apply]
  transp R _ A := by ext i j; simp [evEnt]

theorem ev_proj (τ : ι) {R : Type} [CommRing R] (A : Mat m R) : (proj m τ).ev A = A τ := by
  ext i j
  exact aeval_X (R := ℤ) (fun v : EntIx m => A v.1 v.2.1 v.2.2) ⟨τ, (i, j)⟩

end PolyRep

end GlobalTheory.GoodMetric

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealIoX
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def real {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @RealDat b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) :=
  @RealDat.mk b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK)
    (toLevCh := levCh b R.toLevCh)
    (hv0 := (by with_unfolding_all exact (R.hv0 :)))
    (eG := (by with_unfolding_all exact (R.eG :)))
    (pl := (by with_unfolding_all exact (R.pl :)))
    (Sb := (by with_unfolding_all exact (R.Sb :)))
    (θ := (by with_unfolding_all exact (R.θ :)))
    (ψ := (by with_unfolding_all exact (R.ψ :)))
    (MY := fun j => (by with_unfolding_all exact ((ds b (R.MY j)) :)))
    (MX := (by with_unfolding_all exact ((ds b R.MX) :)))
    (MW := fun i σ => (by with_unfolding_all exact ((ds b (R.MW ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (σ :))))) :)))
    (cX := (by with_unfolding_all exact ((coefA b R.cX) :)))
    (cV := fun i => (by with_unfolding_all exact ((coefA b (R.cV ((by with_unfolding_all exact (i :))))) :)))
    (B := (by with_unfolding_all exact ((famReal b R.B) :)))
    (prX := (by with_unfolding_all exact (R.prX :)))
    (HX := (by with_unfolding_all exact (R.HX :)))
    (HV := (by with_unfolding_all exact (R.HV :)))
    (HE := (by with_unfolding_all exact (R.HE :)))
    (HW := (by with_unfolding_all exact (R.HW :)))
    (gE := (by with_unfolding_all exact (R.gE :)))
    (gW := (by with_unfolding_all exact (R.gW :)))
    (jX := (by with_unfolding_all exact (R.jX :)))
    (jV := (by with_unfolding_all exact (R.jV :)))
    (νY := (by with_unfolding_all exact (R.νY :)))
    (fdY := (by with_unfolding_all exact (R.fdY :)))
    (ν0 := (by with_unfolding_all exact (R.ν0 :)))
    (fd0 := (by with_unfolding_all exact (R.fd0 :)))
    (νX := (by with_unfolding_all exact (R.νX :)))
    (fdX := (by with_unfolding_all exact (R.fdX :)))
    (νV := (by with_unfolding_all exact (R.νV :)))
    (fdV := (by with_unfolding_all exact (R.fdV :)))
    (νW := (by with_unfolding_all exact (R.νW :)))
    (fdW := (by with_unfolding_all exact (R.fdW :)))
    (ωY := (by with_unfolding_all exact (R.ωY :)))
    (ωX := (by with_unfolding_all exact (R.ωX :)))
    (ωP := (by with_unfolding_all exact (R.ωP :)))
    (vac := (by with_unfolding_all exact (R.vac :)))
    (vacX := (by with_unfolding_all exact (R.vacX :)))
    (vacP := (by with_unfolding_all exact (R.vacP :)))
    (vY := (by with_unfolding_all exact (R.vY :)))
    (vX := (by with_unfolding_all exact (R.vX :)))
    (vP := (by with_unfolding_all exact (R.vP :)))
    (ItY := (by with_unfolding_all exact (R.ItY :)))
    (ItX := (by with_unfolding_all exact (R.ItX :)))
    (ioY := (by with_unfolding_all exact ((ioYB b R) :)))
    (ioX := (by with_unfolding_all exact ((ioXB b R) :)))
    (Th := (by with_unfolding_all exact (R.Th :)))
    (BV := (by with_unfolding_all exact (R.BV :)))
    (ioP := (by with_unfolding_all exact (R.ioP :)))
    (thF := (by with_unfolding_all exact (R.thF :)))
    (thG := (by with_unfolding_all exact (R.thG :)))
    (nW := (by with_unfolding_all exact (R.nW :)))
    (FW := (by with_unfolding_all exact (R.FW :)))
    (mu := (by with_unfolding_all exact (R.mu :)))
    (twPl := (by with_unfolding_all exact (R.twPl :)))
    (kap := (by with_unfolding_all exact (R.kap :)))
    (lam := (by with_unfolding_all exact (R.lam :)))
    (err0 := (by with_unfolding_all exact (R.err0 :)))

theorem real_ioY {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @HEq (IoYT (@MultT a.D) R) ((R.ioY)) _ (@RealDat.ioY b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R)) :=
  (by with_unfolding_all exact ((castAlong (congrArg (fun m : type_of% (@MultT a.D) => IoYT (@m) R) (multT_eq b a)) ((by with_unfolding_all exact (R.ioY :)))).2 :))

theorem real_ioX {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @HEq (IoXT (@MultT a.D) R) ((R.ioX)) _ (@RealDat.ioX b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R)) :=
  (by with_unfolding_all exact ((castAlong (congrArg (fun m : type_of% (@MultT a.D) => IoXT (@m) R) (multT_eq b a)) ((by with_unfolding_all exact (R.ioX :)))).2 :))

def real3 {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) :
    @RealDat3 b.D G _ _ Pl0 I0 T (famInThreeCoefficientChange b A) Ks _ _ (alg b iK) :=
  @RealDat3.mk b.D G _ _ Pl0 I0 T (famInThreeCoefficientChange b A) Ks _ _ (alg b iK) ((by with_unfolding_all exact ((real b R.toRealDat) :))) ((by with_unfolding_all exact (R.plI :))) ((by with_unfolding_all exact (R.SF :))) ((by with_unfolding_all exact (R.phs :)))
    ((by with_unfolding_all exact (R.lam3 :)))

scoped macro "tr_delta" : tactic => `(tactic|
  try
    delta
      RealDat.chain_vY RealDat.models_HE RealDat.thP_vP RealDat.cw_ItX RealDat.cw_ItY RealDat.chain_vX IsStepVecOf
      RealDat.models_HW RealDat.EEat RealDat.ex_ItX RealDat.ex_ItY RealDat3.full_P RealDat3.full_X
      WeilFull.RealAtO WeilFull.SphInertAtO RealDat3.full_Y RealDat3.in_tie RealDat.thP_pt_theta IsThPVecOf
      RealDat.thP_ωP RealDat.PItX RealDat.PItY RealDat.chain_ptX RealDat.chain_ptY IsThetaAt IsVacO
      RealDat.chain_ωX RealDat.chain_ωY RealDat.Wall Mult.goodPart RealDat.fam_tie)

scoped macro "tr_leaves " a:term:max b:term:max : tactic => `(tactic| (
      (try rewrite [mult_eq $a $b])
      (try rewrite [thetaFun_eq $a $b])
      (try rewrite [vacuum_eq $a $b])
      (try rewrite [placeModel_eq $a $b])
      (try rewrite [itW_eq $a $b])
      (try rewrite [pairSetup_eq $a $b])
      (try rewrite [inertTie_eq $a $b])
      (try rewrite [famTie_eq $a $b])
      (try rewrite [weilDatum_eq $a $b])
      (try rewrite [weilFull_eq $a $b])))

scoped macro "tr_clause " a:term:max b:term:max h:term:max : tactic => `(tactic| (tr_delta; tr_leaves $a $b; kexactB $h))

end GlobalTheory.Mem.R3.Tr

end
end

