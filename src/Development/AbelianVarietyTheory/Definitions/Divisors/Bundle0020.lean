import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero
section
noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem wSub_zero (D : Datum p) (w0 : Ideal (𝓞 D.F)) : wSub D w0 0 = ⊤ := by
  refine eq_top_iff.2 fun z _ => Submodule.subset_span ⟨1, by simp, z, by simp⟩

theorem isEtLev_zero {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) :
    IsEtLev o w0 0 (fun _ => 1) := by
  refine ⟨fun _ _ => (mul_one 1).symm, fun c x => ?_, fun _ _ => rfl, ?_⟩
  · haveI := o.act.hom c
    exact (MonObj.one_comp _).symm
  intro k _ _ x
  refine ⟨fun y _ => by rw [wSub_zero]; trivial, fun g hg => ⟨0, ?_⟩⟩
  have := hg 1 (by simp)
  rw [map_one, o.act.one, Category.comp_id] at this
  rw [this, MonObj.comp_one]

section act
variable {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
  {lv : D.La → (𝟙_ (Over S) ⟶ o.A)}

theorem IsEtLev.congr (h : IsEtLev o w0 r lv) {x y : D.La} (hxy : x - y ∈ wSub D w0 r) : lv x = lv y := by
  have : x = y + (x - y) := by abel
  rw [this, h.1, h.2.2.1 _ hxy, _root_.mul_one]

theorem IsEtLev.congr_mk (h : IsEtLev o w0 r lv) {x y : D.La}
    (hxy : Submodule.Quotient.mk (p := wSub D w0 r) x = Submodule.Quotient.mk y) : lv x = lv y :=
  h.congr ((Submodule.Quotient.eq _).1 hxy)

def liftAct (g : LevGrp D w0 r) (x : D.La) : D.La :=
  (Submodule.Quotient.mk_surjective (wSub D w0 r) (g (Submodule.Quotient.mk x))).choose

theorem mk_liftAct (g : LevGrp D w0 r) (x : D.La) :
    Submodule.Quotient.mk (p := wSub D w0 r) (liftAct g x) = g (Submodule.Quotient.mk x) :=
  (Submodule.Quotient.mk_surjective (wSub D w0 r) (g (Submodule.Quotient.mk x))).choose_spec

theorem IsEtLev.twist (h : IsEtLev o w0 r lv) (g : LevGrp D w0 r) :
    IsEtLev o w0 r (fun x => lv (liftAct g x)) := by
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ pt => ⟨fun y hy => ?_, fun q hq => ?_⟩⟩
  · rw [← h.1]; apply h.congr_mk
    simp only [mk_liftAct, Submodule.Quotient.mk_add, map_add]
  · rw [← h.2.1]; apply h.congr_mk
    simp only [mk_liftAct, Submodule.Quotient.mk_smul, map_smul]
  · have : Submodule.Quotient.mk (p := wSub D w0 r) (liftAct g x) = 0 := by
      rw [mk_liftAct, (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero]
    exact h.2.2.1 _ ((Submodule.Quotient.mk_eq_zero _).1 this)
  · have h1 := ((Submodule.Quotient.mk_eq_zero _).2 ((h.2.2.2 k pt).1 _ hy))
    rw [mk_liftAct, LinearEquiv.map_eq_zero_iff] at h1
    exact (Submodule.Quotient.mk_eq_zero _).1 h1
  · obtain ⟨y, hy⟩ := (h.2.2.2 k pt).2 q hq
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (wSub D w0 r) (g.symm (Submodule.Quotient.mk y))
    refine ⟨x, ?_⟩
    rw [← hy, h.congr_mk (by rw [mk_liftAct, hx, LinearEquiv.apply_symm_apply])]

end act

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
section
noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

def IsHecke (g : D.La →ₗ[D.O] D.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : Obj b (N * k) s) (o' : Obj b N s)
    (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta (g x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (heckeSub o g N) (fun h => (transl h.1).left) ψ.left ∧
    Nonempty (LBIso (lbPow o.P (k ^ 2 / c)) (o'.P.pull (sq2 ψ))) ∧ c ∣ k ^ 2

def IsHeckeMap (g : D.La →ₗ[D.O] D.La) (c k N : ℕ) (F : RepFam b N) (F' : RepFam b (N * k))
    (π : F'.X ⟶ F.X) : Prop :=
  π ≫ F.s = F'.s ∧ ∃ (o' : Obj b N F'.s) (ψ : F'.univ.A ⟶ o'.A), IsHecke g c k N F'.univ o' ψ ∧
    Nonempty (ObjMap o' F.univ π)

theorem IsHecke.dvd {g : D.La →ₗ[D.O] D.La} {c k N : ℕ} {s : S ⟶ Sp R} {o : Obj b (N * k) s} {o' : Obj b N s}
    {ψ : o.A ⟶ o'.A} (h : IsHecke g c k N o o' ψ) : c ∣ k ^ 2 :=
  h.2.2.2.2.2

theorem IsHecke.pol {g : D.La →ₗ[D.O] D.La} {c k N : ℕ} {s : S ⟶ Sp R} {o : Obj b (N * k) s} {o' : Obj b N s}
    {ψ : o.A ⟶ o'.A} (h : IsHecke g c k N o o' ψ) :
    Nonempty (LBIso (lbPow o.P (k ^ 2 / c)) (o'.P.pull (sq2 ψ))) :=
  h.2.2.2.2.1

theorem IsHecke.eta {g : D.La →ₗ[D.O] D.La} {c k N : ℕ} {s : S ⟶ Sp R} {o : Obj b (N * k) s} {o' : Obj b N s}
    {ψ : o.A ⟶ o'.A} (h : IsHecke g c k N o o' ψ) (x : D.La) : o'.eta x = o.eta (g x) ≫ ψ :=
  h.2.2.1 x

theorem IsHeckeMap.over {g : D.La →ₗ[D.O] D.La} {c k N : ℕ} {F : RepFam b N} {F' : RepFam b (N * k)}
    {π : F'.X ⟶ F.X} (h : IsHeckeMap g c k N F F' π) : π ≫ F.s = F'.s :=
  h.1

theorem IsHeckeMap.dvd {g : D.La →ₗ[D.O] D.La} {c k N : ℕ} {F : RepFam b N} {F' : RepFam b (N * k)}
    {π : F'.X ⟶ F.X} (h : IsHeckeMap g c k N F F' π) : c ∣ k ^ 2 := by
  obtain ⟨-, o', ψ, hH, -⟩ := h
  exact IsHecke.dvd hH

example (g : D.La →ₗ[D.O] D.La) (N : ℕ) {s : S ⟶ Sp R} (o : Obj b (N * 3) s) (o' : Obj b N s)
    (ψ : o.A ⟶ o'.A) : ¬ IsHecke g 5 3 N o o' ψ :=
  fun h => absurd h.dvd (by decide)

example (k : ℕ) (hk : 0 < k) : k ^ 2 / k ^ 2 = 1 := Nat.div_self (by positivity)

example (k : ℕ) : (1 : ℕ) ∣ k ^ 2 ∧ k ^ 2 / 1 = k ^ 2 := ⟨one_dvd _, Nat.div_one _⟩

end GlobalTheory.UPel.HT.Hecke
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.AbCoh

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsAffineHom φ]

def preU (U : X.affineOpens) : X'.affineOpens := ⟨φ ⁻¹ᵁ U.1, U.2.preimage φ⟩

theorem preU_mono : Monotone (preU φ) := fun _ _ h _ hx ↦ h hx

def prePair (U : X.affineOpens) : Pair φ := ⟨(preU φ U, U), le_rfl⟩

def preAff : AffOp X ⥤ AffOp X' := (preU_mono φ).functor.op

abbrev OPre (s' : X' ⟶ Sp R') : AffOp X ⥤ CommAlgCat.{0} R' := preAff φ ⋙ OAff s'

def preRes (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OAff s') (OPre φ s') := CoefMap.restrict _ _

def preα (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (U : AffOp X) : (OAff s).obj U →+* (OPre φ s').obj U :=
  secPull s s' (prePair φ U.unop)

variable {φ} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}

def preCoef (h : φ ≫ s = s' ≫ spMap σ) : CoefMap σ (OAff s) (OPre φ s') where
  G := 𝟭 _
  α U := preα φ s s' U
  naturality {p q} a b := (pairPull h).naturality
    (homOfLE (show prePair φ q.unop ≤ prePair φ p.unop from
      ⟨preU_mono φ (leOfHom a.unop), leOfHom a.unop⟩)).op b
  smul U := semiHom_secPull h (prePair φ U.unop)

example (U : X.affineOpens) : preU (𝟙 X) U = U := rfl

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZM
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLev

def SRelBy {h n' n : ℕ} {B' B : Type} [CommRing B'] [CommRing B] {ζ' : B'} {ζ : B} {S' S : Scheme.{0}} {s' : S' ⟶ Sp B'}
    {s : S ⟶ Sp B} (c' : SiegPre h n' ζ' s') (c : SiegPre h n ζ s) (d' d : ℕ) (f : S' ⟶ S) (φ : c'.A.left ⟶ c.A.left) :
    Prop :=
  IsGrpPullback c'.A c.A f φ ∧ (∃ φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left, IsSquare φ φ₂ ∧ LBIso c'.P (c.P.pull φ₂)) ∧
    ∀ a, (c'.lev a ^ d').left ≫ φ = f ≫ (c.lev a ^ d).left

def SRel {h n' n : ℕ} {B' B : Type} [CommRing B'] [CommRing B] {ζ' : B'} {ζ : B} {S' S : Scheme.{0}} {s' : S' ⟶ Sp B'}
    {s : S ⟶ Sp B} (c' : SiegPre h n' ζ' s') (c : SiegPre h n ζ s) (d' d : ℕ) (f : S' ⟶ S) : Prop :=
  ∃ φ, SRelBy c' c d' d f φ

theorem sRel_one_one_iff {h n : ℕ} {B' B : Type} [CommRing B'] [CommRing B] {ζ' : B'} {ζ : B} {S' S : Scheme.{0}}
    {s' : S' ⟶ Sp B'} {s : S ⟶ Sp B} (c' : SiegPre h n ζ' s') (c : SiegPre h n ζ s) (f : S' ⟶ S) :
    SRel c' c 1 1 f ↔ SiegPB c' c f := by
  unfold SRel SRelBy SiegPB
  simp only [pow_one]
  constructor
  · rintro ⟨φ, hpb, ⟨φ₂, hsq, hiso⟩, hlev⟩
    exact ⟨φ, φ₂, hpb, hsq, hiso, hlev⟩
  · rintro ⟨φ, φ₂, hpb, hsq, hiso, hlev⟩
    exact ⟨φ, hpb, ⟨φ₂, hsq, hiso⟩, hlev⟩

structure SQuot {h N : ℕ} {o' : Type} [CommRing o'] {ζ' : o'} (F : SFam h N ζ') (n : ℕ) {o : Type} [CommRing o] (ζ : o)
    (j : o →+* o') where

  X : Scheme.{0}

  s : X ⟶ Sp o

  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s

  qproj : IsQProjOver s

  univ : SiegPre h n ζ s

  princ : univ.Principal

  π : F.X ⟶ X

  base : π ≫ s = F.s ≫ spMap j

  fin : IsFinite π

  etale : Etale π

  onto : Surjective π

  low : SRel F.univ univ (N / n) 1 π

  fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'),
    y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j → SRel c F.univ 1 (N / n) y → SRel c F.univ 1 (N / n) y' → y ≫ π = y' ≫ π

def SQuot.self {h N : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam h N ζ) (hN : 0 < N)
    (hid : SiegPB F.univ F.univ (𝟙 _)) : SQuot F N ζ (RingHom.id o) where
  X := F.X
  s := F.s
  smooth := F.smooth
  qproj := F.qproj
  univ := F.univ
  princ := F.princ
  π := 𝟙 _
  base := by rw [show spMap (RingHom.id o) = 𝟙 _ from Spec.map_id _]; simp
  fin := inferInstance
  etale := inferInstance
  onto := inferInstance
  low := by rw [Nat.div_self hN, sRel_one_one_iff]; exact hid
  fibre R _ _ y y' s' c h₁ h₂ h₃ := by
    rw [Nat.div_self hN, sRel_one_one_iff] at h₂ h₃
    rw [show spMap (RingHom.id o) = 𝟙 _ from Spec.map_id _] at h₁
    simpa using F.inj R y y' s' c (by simpa using h₁) h₂ h₃

end GlobalTheory.SiegLev
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
section
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} {k : Type} [CommRing k]

def IsConn (G : PDivGroup p k) : Prop := ∀ n, ∀ a ∈ augIdeal k (G.A n), IsNilpotent a

def IsEt (G : PDivGroup p k) : Prop := ∀ n, IsReduced (G.A n)

end PDivGroup

def WittOn (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (P : PDivGroup p k → Prop) : Prop :=
  ∃ (M : {G // P G} → ModuleCat.{0} (WittVector p k))
    (map : ∀ G H : {G // P G}, (G.1 ⟶ H.1) →+ (M H →ₗ[WittVector p k] M G))
    (red : ∀ G : {G // P G},
      M G →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.1.RigExt),
    (∀ G : {G // P G}, Module.Free (WittVector p k) (M G) ∧ Module.Finite (WittVector p k) (M G) ∧
      Function.Surjective (red G) ∧ (∀ m, red G m = 0 ↔ ∃ n, m = p • n) ∧
      map G G (𝟙 G.1) = LinearMap.id) ∧
    (∀ (G H K : {G // P G}) (f : G.1 ⟶ H.1) (g : H.1 ⟶ K.1),
      map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
    ∀ (G H : {G // P G}) (f : G.1 ⟶ H.1) (m : M H),
      red G (map G H f m) = PDivGroup.rigExtMap f (red H m)

end GlobalTheory
end
end

