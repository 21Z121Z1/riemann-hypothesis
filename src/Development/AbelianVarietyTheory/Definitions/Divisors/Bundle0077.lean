import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovHt

section Steps

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i)

def ShortAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∃ abelian₂ : ℝ, (∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)),
      IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂) ∧
    Real.log abelian₂ * (6 * dimFlag (dat p i) + 10 + lenT p i PP * (zed p i PP u1 + 2 * rhoB (dat p i) u1)) ≤ C * unitE p

def GeomAt (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) ∧
    GlobalTheory.DegVal.BirOn Y.U Z (wtOf (dat p i) u1 0) ∧ (1 - rhoB (dat p i) u1) * Y.dg u1 Z ≤ delPrime Y.U Z u1

def MultAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧
    ∀ Z, Mult Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z u1 (uPrime (dat p i) u1) cc

def BudgetAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  Y.d.l₂.M'.primeFactors.card ≤ 15 ∧
  ∃ g : ℝ, WtGap (uPrime (dat p i) u1) g ∧ 0 ≤ errX (ell D) (uPrime (dat p i) u1) g ∧
    lenT p i PP * errX (ell D) (uPrime (dat p i) u1) g ≤ C * unitE p ∧
    0 ≤ htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) ∧
    lenT p i PP * (htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1)) ≤ C * unitE p

end Steps

def Short : Prop := Covers fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → ShortAt p i Y PP C u1

def Geom : Prop := Covers fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → GeomAt p i Y u1

def MultC : Prop := Covers fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → MultAt p i Y PP C u1

def Budget : Prop := Covers fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → BudgetAt p i Y PP C u1

end GlobalTheory.CovHt

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EtLevForget
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtC GlobalTheory.UPel.HT GlobalTheory.PELU GlobalTheory.KS
open scoped TensorProduct Matrix

namespace GlobalTheory.EtaleLevelHecke

def ModelExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (Model b N)

def ModelProj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.CompactB → ∀ M : Model b N, IsProjOver M.s

def HeckeFet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π ∧ IsFinite π ∧ Etale π ∧ Surjective π

def EtLevCover : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), 3 ≤ N → N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (o' : Obj b N (π ≫ s)) (m : ObjMap o' o π) (lv : D.La → (𝟙_ (Over Y) ⟶ o'.A)) (ρ : LevGrp D w0 r → (Y ⟶ Y)), IsEtLev o' w0 r lv ∧ GlobalTheory.ZM.IsGaloisCover (LevGrp D w0 r) ρ π ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (o₁ : Obj b N (t ≫ s)) (m₁ : ObjMap o₁ o t) (l : D.La → (𝟙_ (Over T) ⟶ o₁.A)), IsEtLev o₁ w0 r l → ∃! f : T ⟶ Y, f ≫ π = t ∧ ∃ m₂ : ObjMap o₁ o' f, ∀ y, (l y).left ≫ m₂.φ = f ≫ (lv y).left

def EtLevModel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ M : Model b N, ∃ (E : EtModel b N w0 r) (π : E.X ⟶ M.X) (ρ : LevGrp D w0 r → (E.X ⟶ E.X)), π ≫ M.s = E.s ∧ Nonempty (ObjMap E.univ M.univ π) ∧ GlobalTheory.ZM.IsGaloisCover (LevGrp D w0 r) ρ π

def EtLevHecke : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (E : EtModel b N w0 r) (E' : EtModel b (N * k) w0 r), ∃ π : E'.X ⟶ E.X, π ≫ E.s = E'.s ∧ IsFinite π ∧ Etale π ∧ ∃ (o' : Obj b N E'.s) (ψ : E'.univ.A ⟶ o'.A), IsHecke g c k N E'.univ o' ψ ∧ ∃ m : ObjMap o' E.univ π, ∀ y, (E'.lv y ≫ ψ).left ≫ m.φ = π ≫ (E.lv y).left

def EtLevForget : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p), 3 ≤ N → ∀ (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (E : EtModel b N w0 r) (E' : EtModel b N' w0 r), ∃ π : E'.X ⟶ E.X, π ≫ E.s = E'.s ∧ IsFinite π ∧ Etale π ∧ ∃ m : ObjMap (E'.univ.forget N hd hc) E.univ π, ∀ y, (E'.lv y).left ≫ m.φ = π ≫ (E.lv y).left

def GenExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R'] [IsNoetherianRing R'] (gb : GBase D.toG R') (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (GenModel gb N)

def GenCmp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (R' : Type) [CommRing R'] [Algebra ℚ R'] (φ : R →+* R') (gb : GBase D.toG R'), gb.ρ = φ b.ρ → (∀ i, gb.t i = φ.comp (b.t i)) → ∀ (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (X : GenModel gb N), ∃ j : X.X ⟶ pullback M.s (spMap φ), IsOpenImmersion j ∧ IsClosedImmersion j ∧ j ≫ pullback.snd _ _ = X.s ∧ IsGPull X.univ M.univ (j ≫ pullback.fst _ _)

def GenHecke : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R'] [IsNoetherianRing R'] (gb : GBase D.toG R') (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (X : GenModel gb N) (X' : GenModel gb (N * k)), ∃ π : X'.X ⟶ X.X, IsGHeckeMap g c k N X X' π ∧ IsFinite π ∧ Etale π ∧ Surjective π

def GenHeckeBC : Prop :=
  ∀ (G : GDatum) (R₁ R₂ : Type) [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂] (ψ : R₁ →+* R₂) (gb₁ : GBase G R₁) (gb₂ : GBase G R₂) (g : G.La →ₗ[G.O] G.La) (c k N : ℕ), 3 ≤ N → 0 < k → ∀ (X₁ : GenModel gb₁ N) (X₁' : GenModel gb₁ (N * k)) (X₂ : GenModel gb₂ N) (X₂' : GenModel gb₂ (N * k)) (π₁ : X₁'.X ⟶ X₁.X) (π₂ : X₂'.X ⟶ X₂.X) (j : X₂.X ⟶ pullback X₁.s (spMap ψ)) (j' : X₂'.X ⟶ pullback X₁'.s (spMap ψ)), IsGHeckeMap g c k N X₁ X₁' π₁ → IsGHeckeMap g c k N X₂ X₂' π₂ → j ≫ pullback.snd _ _ = X₂.s → j' ≫ pullback.snd _ _ = X₂'.s → IsGGPull X₂.univ X₁.univ (j ≫ pullback.fst _ _) → IsGGPull X₂'.univ X₁'.univ (j' ≫ pullback.fst _ _) → π₂ ≫ j ≫ pullback.fst _ _ = j' ≫ pullback.fst _ _ ≫ π₁

def GenCxPoint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (gb : GBase D.toG ℂ) (N : ℕ), 3 ≤ N → N.Coprime p → gb.ρ = D.ρc → (∀ i (c : 𝓞 D.F), gb.t i c = D.tau i (c : D.F)) → ∀ X : GenModel gb N, ∃ x : Sp ℂ ⟶ X.X, x ≫ X.s = 𝟙 _

def UnifCx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N), 3 ≤ N → N.Coprime p → b.IsType σ ρ → M.Uniformised σ ρ

def UnifCxQuot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N), 3 ≤ N → N.Coprime p → b.IsType σ ρ → IsProjOver M.s → ∃ (h : _) (hL : _) (U : Unif (M.univ.fam h hL) σ ρ N (D.Cls N)) (r : Fin U.n → ℕ) (bs : ∀ i, Module.Basis (Fin (r i)) ℤ (U.Di i).La), (∀ i, (Dom (U.Di i) (bs i)).Nonempty ∧ ContractibleSpace (Dom (U.Di i) (bs i)) ∧ DiscreteTopology (Gam (U.Di i) (bs i) N) ∧ (∀ x ∈ Gam (U.Di i) (bs i) N, IsOfFinOrder x → x = 1) ∧ ∃ K : Set (UG (U.Di i) (bs i) ℝ), IsCompact K ∧ ∀ x, ∃ q ∈ Gam (U.Di i) (bs i) N, q * x ∈ K) ∧ Nonempty (GlobalTheory.CxPts M.s σ ≃ₜ (Σ i, DomQuot (U.Di i) (bs i) (Gam (U.Di i) (bs i) N)))

def KSProj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N) (l : ℕ) [Fact l.Prime], l ≠ p → ∀ (E : Type) [Field E] [CharZero E] [Algebra ℚ_[l] E] (m : ℕ) (ε : Matrix (Fin m) (Fin m) D.O →₀ E) (k : ℕ), 3 ≤ N → N.Coprime p → b.IsType σ ρ → IsProjOver M.s → ArtinQE l E → IsCut (Module.toModuleEnd ℤ (S := D.O) D.La) ε k → ∀ n : ℕ, op l M.univ.act M.s (spMap σ) ε n * op l M.univ.act M.s (spMap σ) ε n = op l M.univ.act M.s (spMap σ) ε n

def Top : Prop :=
  ModelExists ∧ ModelProj ∧ HeckeFet ∧ EtLevCover ∧ EtLevModel ∧ EtLevHecke ∧ EtLevForget ∧ GenExists ∧ GenCmp ∧ GenHecke ∧ GenHeckeBC ∧ GenCxPoint ∧ UnifCx ∧ UnifCxQuot ∧ KSProj

end GlobalTheory.EtaleLevelHecke
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB

namespace GlobalTheory.CovTest

def IsFlagBundle {B Y : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) : Prop :=
  ∀ (T : Scheme.{0}) (g : T ⟶ B) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)),
    ∃! g' : T ⟶ Y, ∃ w : g' ≫ π = g, ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
      e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp g' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)

theorem isFlagBundle_empty (B : Scheme.{0}) (E : Empty → B.Modules) (n : Empty → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback (𝟙 B)).obj (E a)) (n a)) : IsFlagBundle (𝟙 B) E n fl :=
  fun _ g _ => ⟨g, ⟨Category.comp_id g, fun a => a.elim⟩, fun _ ⟨w, _⟩ => (Category.comp_id _).symm.trans w⟩

theorem isFlagBundle_rank_one (B : Scheme.{0}) {ι : Type} (E : ι → B.Modules)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback (𝟙 B)).obj (E a)) 1) : IsFlagBundle (𝟙 B) E (fun _ => 1) fl := by
  intro T g fl'
  refine ⟨g, ⟨Category.comp_id g, fun a i => ?_⟩, fun _ ⟨w, _⟩ => (Category.comp_id _).symm.trans w⟩
  induction i using Fin.lastCases with
  | last =>
    have := (fl a).isIso_last
    have := (fl' a).isIso_last
    exact ⟨asIso ((Scheme.Modules.pullback g).map ((fl a).ι (Fin.last 1)) ≫
        (Scheme.Modules.pullbackComp g (𝟙 B)).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr (Category.comp_id g)).hom.app (E a)) ≪≫ (asIso ((fl' a).ι (Fin.last 1))).symm,
      by simp⟩
  | cast i =>
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have z : Limits.IsZero ((Scheme.Modules.pullback g).obj ((fl a).F (0 : Fin 1).castSucc)) :=
      isVB_zero_iff.1 (((fl a).isVB _).pullback g)
    exact ⟨z.iso (isVB_zero_iff.1 ((fl' a).isVB _)), z.eq_of_src _ _⟩

theorem exists_isFlagBundle_rank_one (B : Scheme.{0}) {ι : Type} (E : ι → B.Modules) (hE : ∀ a, IsVB (E a) 1) :
    ∃ fl, IsFlagBundle (𝟙 B) E (fun _ => 1) fl :=
  ⟨fun a => .ofRankOne ((hE a).pullback _), isFlagBundle_rank_one B E _⟩

def Homog (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) : Prop := ∀ D a b, (G D a b).IsHomogeneous D

def Swap2 (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) : Prop :=
  ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Φ Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsArFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Φ →
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
      ∀ a b : ℤ, Φ (lin ![(a : ℝ), b, 1] ^ (d + 2)) + Φ (lin ![(b : ℝ), a, 1] ^ (d + 2)) = Ψ (G (d + 1) a b)

open Classical in

def swapPol {κ : Type} [Fintype κ] (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) (D : ℕ) (x y : κ) (n : κ → ℤ) :
    MvPolynomial κ ℝ :=
  aeval ![X x, X y, lin fun z => if z = x ∨ z = y then 0 else (n z : ℝ)] (G D (n x) (n y))

open Classical in

def SwapFl (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) : Prop :=
  ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ),
    IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ)
    (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (Φ Ψ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ),
      IsArFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Φ →
      IsGeoFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Ψ →
      ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 → ∀ n : (Σ a, Fin (r a)) → ℤ,
        Φ (lin (fun z => (n z : ℝ)) ^ (D + 1)) +
            Φ (lin (fun z => (n (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩ z) : ℝ)) ^ (D + 1)) =
          Ψ (swapPol G D ⟨a, i⟩ ⟨a, i'⟩ n)

def Ch2Const (r : ℝ) : Prop :=
  ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 →
    ∀ P : PPAS X, P.IsCh2Omega p (r / 2 * (P.degOmega p : ℝ))

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam.Pad

section One

variable {D : D7} (Y : ShimX D.what₂.Tau)

open Classical in

def SwapEq (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) (Φ Ψ : Pol D.what₂.Tau Y.N → ℝ) : Prop :=
  ∀ (τ : D.what₂.Tau) (a b : Fin Y.N), (b : ℕ) = a + 1 → (b : ℕ) ≠ Y.j → ∀ n : D.what₂.Tau × Fin Y.N → ℤ,
    Φ (lin (fun z => (n z : ℝ)) ^ (dimFl D.what₂.Tau Y.N + 1)) +
        Φ (lin (fun z => (n (swapAt τ a b z) : ℝ)) ^ (dimFl D.what₂.Tau Y.N + 1)) =
      Ψ (swapPol G (dimFl D.what₂.Tau Y.N) (τ, a) (τ, b) n)

def PrimeLocalCondition : Prop := ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime →
  ∀ Q : MvPolynomial (Rt D.what₂.Tau Y.N) ℝ, Q.IsHomogeneous (dimFl D.what₂.Tau Y.N - 1) →
    Y.arMix Sx R p ((X (Sum.inr (false, 2)) - X (Sum.inr (true, 2))) * tagDR D.what₂.Tau _ Q) =
      -(Real.log p * ((p : ℝ) / ((p : ℝ) ^ 2 - 1)) * Y.chern (chLieA D _ Y.j 1 * Q))

def PrimeLocalSplitCondition : Prop := ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime →
  ∀ Q : MvPolynomial (Rt D.what₂.Tau Y.N) ℝ,
    Y.arMix Sx R p (X (Sum.inr (true, 2)) * (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

def sieg (T : Finset ℕ) (R : ℝ) : ℝ :=
  Y.arMix T R 1 (X (Sum.inr (false, 2)) * tagDR D.what₂.Tau _ (curveCl D.what₂.Tau Y.N Y.j))

def SiegRead : Prop := ∀ (T : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime → p ∉ T → (∀ q ∈ T, q.Prime) →
  sieg Y T R = Y.arMix T R p (X (Sum.inr (false, 2)) * tagDR D.what₂.Tau _ (curveCl D.what₂.Tau Y.N Y.j)) ∧
  sieg Y (insert p T) R = Y.arMix T R p (X (Sum.inr (true, 2)) * tagHT D.what₂.Tau _ (curveCl D.what₂.Tau Y.N Y.j))

def LatAt : Prop := ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → Y.arDeg (setB Y B) R (testF Y) = sieg Y (setB Y B) R

def bcFl : ℝ := (1 / (Y.j : ℝ) - 1 / ((Y.N : ℝ) - Y.j)) * testI Y

theorem bcFl_eq : bcFl Y =
    -(((Y.j : ℝ) - 1) / Y.j) * testI Y + -(((Y.N : ℝ) - Y.j - 1) / ((Y.N : ℝ) - Y.j)) * -testI Y := by
  have h₁ : (Y.j : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 Y.j_pos)
  have h₂ : (Y.N : ℝ) - Y.j ≠ 0 := (sub_pos.2 (Nat.cast_lt.2 Y.j_lt)).ne'
  rw [bcFl]
  field_simp
  ring

theorem bcFl_of_eq_two_mul (h : Y.N = 2 * Y.j) : bcFl Y = 0 := by
  rw [bcFl, show (Y.N : ℝ) - Y.j = Y.j by rw [h]; push_cast; ring, sub_self, zero_mul]

example (h : Y.N = 3) (h' : Y.j = 1) : bcFl Y = testI Y / 2 := by
  rw [bcFl, show (Y.N : ℝ) = 3 by rw [h]; norm_num, show (Y.j : ℝ) = 1 by rw [h']; norm_num]
  ring

def HhTest (hh : Fn Y) : Prop := hh (testF Y) = bcFl Y - testI Y

def DRAt (r : ℝ) : Prop := Tendsto (sieg Y ∅) atTop (𝓝 (Y.vol * bcFl Y - 2 * r * Y.vol * testI Y))

theorem HhTest.vol_mul {hh : Fn Y} (h : HhTest Y hh) (r s : ℝ) :
    Y.vol * bcFl Y - 2 * r * Y.vol * testI Y + s * (2 * Y.vol * testI Y) =
      Y.vol * (hh (testF Y) - 2 * testI Y * (r - 1 / 2 - s)) := by
  rw [h]
  ring

end One

def rkB (ι : Type) (N j : ℕ) (a : ι × Bool) : ℕ := cond a.2 j (N - j)

structure BunModel {D : D7} (O : Setup D) (P : Finset ℕ) (R : ℝ) (c : O.s.Comp) : Type 1 where

  V : Cover (O.var c)

  B : Scheme.{0}
  [int : IsIntegral B]

  q : B ⟶ Sp (𝓞 D.what₂.LL)
  ar : IsArithVar q (dimGr D.what₂.Tau O.N O.j)

  π : V.X ⟶ B
  w : π ≫ q = V.p

  E : D.what₂.Tau × Bool → B.Modules

  h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)
  H : ∀ a, (h a).IsCInf

  fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (rkB D.what₂.Tau O.N O.j a)
  univ : IsFlagBundle π E (rkB D.what₂.Tau O.N O.j) fl
  ind : ∀ (a : D.what₂.Tau × Bool) (i : Fin (rkB D.what₂.Tau O.N O.j a)),
    V.Induces (adlOf (O.Φ.C c) (O.met.hm c)
      (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))) (VMetric.grLB (fl a) i ((H a).pull π w)) 1

def BunSt : Prop := ∀ (D : D7) (O : Setup D), O.Core → ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → ∀ c,
  Nonempty (BunModel O (setB O.Y B) R c)

end GlobalTheory.CovTest

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegJoin

open GlobalTheory.SiegMin GlobalTheory.Poinc GlobalTheory.PolDeg

variable {g n : ℕ}

def MinAt (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) : Prop :=
  ∃ (o' : Type) (_ : CommRing o') (β : cycAway n →+* o') (S' : Scheme.{0}) (s' : S' ⟶ Sp o') (U : S'.Opens)
    (c : U.toScheme ⟶ F.X) (π : S' ⟶ Z) (G : Over S') (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left)
    (_ : IsCommMonObj G) (L : LB G.left) (N : ℕ),
    (IsThetaCompact F z i ∧ IsProjOver z ∧ IsNormalScheme Z ∧ i ≫ z = F.s ∧ Dense (Set.range i) ∧ OZ.IsLB ∧ IsAmpleLB OZ) ∧
    (β.Finite ∧ Function.Injective β ∧ IsProjOver s' ∧ IsNormalScheme S' ∧ Dense (U : Set S') ∧ IsFinite c ∧
      Surjective c ∧ U.ι ≫ π = c ≫ i ∧ π ⁻¹' Set.range i = U ∧ π ≫ z = s' ≫ spMap β ∧ Surjective π ∧ IsProper π ∧
      IsNoetherian Z) ∧
    (IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧
      IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e ∧ abLocus G = U) ∧
    (1 ≤ N ∧ LBIso (OZ.pull π) (lbPow (hodge G g) N)) ∧
    (L.IsLB ∧ ∃ (α₂ : (G2 ((Over.pullback c).obj F.univ.A)).left ⟶ (G2 F.univ.A).left)
      (e₂ : (G2 ((Over.pullback c).obj F.univ.A)).left ⟶ (G2 G).left),
      IsSquare (pullback.fst F.univ.A.hom c) α₂ ∧ IsSquare e e₂ ∧ LBIso ((abelian₂ G L).pull e₂) (lbPow (F.univ.P.pull α₂) 2)) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x y : Sp K ⟶ S'), x ≫ π = y ≫ π → SameAbPart G x y

def BlowAt (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (φ : InvFun ℤ) (d : ℕ)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : F.X ⟶ S) (BD : EffCartierData S) : Prop :=
  ∃ J : Z.IdealSheafData, 1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ ValOn F i φ J d ∧ IsNormBl π J ∧
    IsProjOver (π ≫ z) ∧ Dense (Set.range j) ∧ j ≫ π = i ∧ π ⁻¹' Set.range i = Set.range j ∧
    BD.idealSheaf = J.comap π ∧ ValOn F j φ BD.idealSheaf d

def ChartSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n →
    ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ)
      (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S),
      MinAt F z i OZ → BlowAt F z i φ d π j BD →
      SmoothOfRelativeDimension (g * (g + 1) / 2) (π ≫ z) ∧ ∀ x : S, PreChart F (π ≫ z) j φ BD d x

def DescSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, ∀ n : ℕ, 3 ≤ n → Odd n →
    ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ)
      (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S),
      MinAt F z i OZ → BlowAt F z i φ d π j BD → SmoothOfRelativeDimension (g * (g + 1) / 2) (π ≫ z) →
      (∀ x : S, PreChart F (π ≫ z) j φ BD d x) →
      ∃ (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left), IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧
        IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j

end GlobalTheory.SiegJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
section
noncomputable section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

def Factor.Alg {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} (F : Factor D D') : Prop :=
  (∃ b : ℕ, 0 < b ∧ Star.star F.e * F.e = b • (Star.star F.e * F.f * F.e)) ∧
    Star.star F.e * F.f * F.e = Star.star F.e * Star.star F.f * F.e ∧ ∃ g : F.O, g * (Star.star F.e * F.f * F.e) = F.e

theorem Wit.fac_alg : Wit.fac.Alg := by
  have hf : Wit.fac.f = 1 := rfl
  have hs : Star.star Wit.fac.e = Wit.fac.e := rfl
  have hi := Wit.fac.idem
  refine ⟨⟨1, one_pos, ?_⟩, ?_, 1, ?_⟩
  · rw [hf, mul_one, one_smul]
  · rw [hf, star_one]
  · rw [hf, hs, mul_one, one_mul, hi]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R]

def EndData (D : DegPre R) (a a' : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) : Prop :=
  IsMonHom a ∧ IsMonHom a' ∧ RosatiAdj D.P.A D.P.L a a' ∧ (∀ y, D.c (h y) = D.c y ≫ a) ∧ (∀ y, D.c (h' y) = D.c y ≫ a') ∧
    D.TauBal a a' h h'

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def FormalEnd (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G) : Prop :=
  (∀ e, IsMonHom (b e)) ∧ (∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G) ∧
    (∀ e, b e ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map a) ∧
    ∀ e, ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X,
      TorusEndOf D.toPre.X h' t ∧ (U.gt e).i ≫ b e = t ≫ (U.gt e).i

def LinEnd (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (b : G ⟶ G) : Prop :=
  IsMonHom b ∧ FormalEnd U a h' fun e => (Over.pullback (thick R I e)).map b

def ExtLam (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB ((Over.pullback (jK R)).obj G).left)
    (PP : LB (G2 G).left) : Prop :=
  PP.IsLB ∧ ∀ κ₂ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left,
    Geo.Tor.IsSquare (G' := (Over.pullback (jK R)).obj G) (G := G) (pullback.fst G.hom (jK R)) κ₂ →
      LBIso (abelian₂ ((Over.pullback (jK R)).obj G) L) (PP.pull κ₂)

end GlobalTheory.Mum
end
end

