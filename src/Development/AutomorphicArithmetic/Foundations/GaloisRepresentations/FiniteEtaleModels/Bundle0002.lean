import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsQuotTriv
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

structure IsQuot {E : Type} [Field E] {Γ : Type} [Group Γ] (X : G3.Tower (Sp E) Γ) (O : Type) [CommRing O] [Algebra O E]
    (K₀ : Subgroup Γ) (i : X.ι) {Y : Scheme.{0}} (pY : Y ⟶ Spec (CommRingCat.of O)) (π : X.Z i ⟶ Y) : Prop where
  ov : π ≫ pY = X.q i ≫ gen O E
  le : X.K i ≤ K₀
  idx : (X.K i).relIndex K₀ ≠ 0
  adm : ∀ u ∈ K₀, X.admitted i i u
  inv : ∀ u ∈ K₀, ∀ a b, X.tr i i u a b ≫ π = π
  fib : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x y : sp Ω ⟶ X.Z i), x ≫ π = y ≫ π → ∃ u ∈ K₀, ∃ a b, y = x ≫ X.tr i i u a b
  free : ∀ u ∈ K₀, ∀ a b (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ X.Z i), x ≫ X.tr i i u a b = x → u ∈ X.K i
  onto : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : sp Ω ⟶ Y) (σ : sp Ω ⟶ sp E), y ≫ pY = σ ≫ gen O E → ∃ x, x ≫ π = y

def DegGen : Prop :=
  ∀ (E : Type) [Field E] (Γ : Type) [Group Γ] (X : G3.Tower (Sp E) Γ) (O : Type) [CommRing O] [Algebra O E] (K₀ K₁ : Subgroup Γ) (i : X.ι)
    (Y Y' : Scheme.{0}) (pY : Y ⟶ Spec (CommRingCat.of O)) (π' : X.Z i ⟶ Y') (s : Y' ⟶ Y), K₁ ≤ K₀ →
    IsQuot X O K₀ i pY (π' ≫ s) → IsQuot X O K₁ i (s ≫ pY) π' →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : sp Ω ⟶ Y) (σ : sp Ω ⟶ sp E), y ≫ pY = σ ≫ gen O E →
      Nat.card {y' : sp Ω ⟶ Y' // y' ≫ s = y} = K₁.relIndex K₀

def FEtExt : Prop :=
  ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (Y Y' : Scheme.{0})
    (pY : Y ⟶ Spec (CommRingCat.of O)) (s : Y' ⟶ Y) (d : ℕ), Flat pY → IsFinite s → Etale s →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : sp Ω ⟶ Y) (σ : sp Ω ⟶ sp E), y ≫ pY = σ ≫ gen O E →
      Nat.card {y' : sp Ω ⟶ Y' // y' ≫ s = y} = d) → FEt s d

def SigmaFEt : Prop :=
  ∀ (Y Y' : Scheme.{0}) (s : Y' ⟶ Y) (d : ℕ) (I : Type) [Finite I], FEt s d → FEt (Sigma.desc fun _ : I => s) (Nat.card I * d)

def LiesAbs : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [Algebra ℚ E] (gb : GBase D.toG E) (k : ℕ)
    (T : KS L gb k) (N : Lv p) (J A : Type) [Field A] (g : J → Mem L N) (θ : J → A) (O : Type) [CommRing O] [Algebra O E]
    (C : Cover (T.tower N g) θ O) (j : J) (K₀ K₁ : Subgroup G.GAf) (Y' : Scheme.{0}) (π' : T.X.Z (T.lev (g j).M) ⟶ Y') (s : Y' ⟶ C.Y) (d : ℕ),
    K₁ ≤ K₀ → L.KN N.1 ≤ K₀ → IsQuot T.X O K₀ (T.lev (g j).M) C.p (π' ≫ s) → IsQuot T.X O K₁ (T.lev (g j).M) (s ≫ C.p) π' →
    (∀ a b, T.X.tr (T.lev (g j).M) (T.lev N) 1 a b ≫ C.π = π' ≫ s) → FEt s d →
    (∀ u ∈ K₀, ∃ a ∈ (g j).K, a ∈ K₀ ∧ a⁻¹ * u ∈ K₁) →
    (∀ x ∈ (g j).K, ∃ t : Y' ⟶ C.Y, t ≫ C.p = s ≫ C.p ∧
      ∀ a b, π' ≫ t = T.X.tr (T.lev (g j).M) (T.lev N) ((g j).h * x) a b ≫ C.π) →
    ∃ (Z : Scheme.{0}) (s' t' : Z ⟶ C.Y) (d' m : ℕ), FEt s' d' ∧ t' ≫ C.p = s' ≫ C.p ∧ C.Lies j s' t' m

def LiftLev : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → ∀ (q : ℕ) (r : ℤ) (𝔴 𝔞 : Ideal (𝓞 D.F)) (N₀ : ℕ),
    AtPrime D q r 𝔴 → (∃ e : ℕ, uId D q r ^ e ≤ 𝔞) → N₀.Coprime q → ∀ gg : LevGrp D 𝔞 1, ∃ u ∈ L.KN N₀,
      ∀ x y : D.La, gg ((wSub D 𝔞 1).mkQ x) = (wSub D 𝔞 1).mkQ y → L.actG u (inAf D x) - inAf D y ∈ idHat D 𝔞

def NormExt : Prop :=
  ∀ (U S Y B : Scheme.{0}) (i : U ⟶ S) (f : S ⟶ B) (g : Y ⟶ B) (y : U ⟶ Y), IsOpenImmersion i → IsDominant i → IsLocallyNoetherian S →
    (∀ x : S, IsDomain (S.presheaf.stalk x)) → (∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x)) → IsFinite g → y ≫ g = i ≫ f →
    ∃ y' : S ⟶ Y, i ≫ y' = y ∧ y' ≫ g = f

end UpperTheory.Gal.FiniteEtaleModels
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFinCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private theorem level_congr {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s} {𝔞 : Ideal (𝓞 D.F)} {r : ℕ} {T : Over S}
    {l : D.La → (T ⟶ o.A)} (hl : IsEtLevOver o 𝔞 r l) {u v : D.La}
    (e : (wSub D 𝔞 r).mkQ u = (wSub D 𝔞 r).mkQ v) : l u = l v := by
  have hmem : u - v ∈ wSub D 𝔞 r := (Submodule.Quotient.eq _).mp e
  have h1 : l (u - v) = 1 := hl.2.2.1 _ hmem
  calc l u = l ((u - v) + v) := by rw [sub_add_cancel]
    _ = l (u - v) * l v := hl.1 _ _
    _ = l v := by rw [h1, _root_.one_mul]

private theorem rep_ext {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s} {𝔞 : Ideal (𝓞 D.F)} {r : ℕ} {Y : Scheme.{0}} {π : Y ⟶ S}
    {lu : D.La → (Over.mk π ⟶ o.A)} (hlu : IsEtLevOver o 𝔞 r lu)
    (hrep : ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), IsEtLevOver o 𝔞 r l → ∃! f : T ⟶ Over.mk π, ∀ y, f ≫ lu y = l y)
    {T : Over S} {f f' : T ⟶ Over.mk π} (h : ∀ y, f ≫ lu y = f' ≫ lu y) : f = f' := by
  obtain ⟨g, -, huniq⟩ := hrep T (fun y => f ≫ lu y)
    (GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 r _ _ lu f hlu)
  rw [huniq f (fun y => rfl), huniq f' (fun y => (h y).symm)]

theorem UpperTheory.Gal.FiniteEtaleModels.finCover_holds :
    RepAll → PtAll → GrpFin → FinCover := by
  intro hRep hPt hGrp p _ D R _ b N 𝔞 r hN hcop het S _ s o
  obtain ⟨Y, π, lu, hfin, het', hlu, hrep⟩ := hRep p D R b N 𝔞 r hcop het S s o
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S Y s π o
  have hpb := m.cart.1
  have hluw : ∀ y, (lu y).left ≫ o.A.hom = 𝟙 Y ≫ π := fun y => by
    rw [Category.id_comp]; exact Over.w (lu y)
  let lv : D.La → (𝟙_ (Over Y) ⟶ o'.A) := fun y =>
    Over.homMk (hpb.lift (lu y).left (𝟙 Y) (hluw y)) (by rw [hpb.lift_snd]; rfl)
  have hlv : ∀ y, (lv y).left ≫ m.φ = (lu y).left := fun y => hpb.lift_fst _ _ _
  have hlv2 : ∀ y, (lv y).left ≫ o'.A.hom = 𝟙 Y := fun y => hpb.lift_snd _ _ _
  have hpt : ∀ y, ptOf m (lv y) = lu y := fun y => by
    ext1; exact hlv y
  have hcomp : ∀ (a c : LevGrp D 𝔞 r) (y : D.La), lu (levAct a (levAct c y)) = lu (levAct (a * c) y) :=
    fun a c y => level_congr hlu (by rw [mkQ_levAct, mkQ_levAct, mkQ_levAct]; rfl)
  have hone : ∀ y, lu (levAct (1 : LevGrp D 𝔞 r) y) = lu y :=
    fun y => level_congr hlu (by rw [mkQ_levAct]; rfl)
  have hact : ∀ g : LevGrp D 𝔞 r, ∃ f : Over.mk π ⟶ Over.mk π, ∀ y, f ≫ lu y = lu (levAct g y) :=
    fun g => (hrep _ _ (GlobalTheory.T.etale_level_group_action p D R b N S s o 𝔞 r _ lu g hlu)).exists
  choose fg hfg using hact
  have hfgeq : ∀ (f : Over.mk π ⟶ Over.mk π) (g : LevGrp D 𝔞 r),
      (∀ y, f ≫ lu y = lu (levAct g y)) → f = fg g :=
    fun f g hf => rep_ext hlu hrep (fun y => by rw [hf, hfg])
  refine ⟨Y, π, o', m, lv, fun g => (fg g).left, ?_, ?_, ?_⟩
  · rw [GlobalTheory.T.isEtLev_iff_isEtLevOver' p D R b N S Y s π (π ≫ s) o o' m 𝔞 r lv]
    simpa only [hpt] using hlu
  · refine ⟨(hGrp p D 𝔞 r het.1).2, ?_, ?_, ?_, hfin, het', ?_, ?_⟩
    · show (fg 1).left = 𝟙 Y
      rw [← hfgeq (𝟙 _) 1 (fun y => by rw [Category.id_comp, hone])]
      rfl
    · intro a c
      show (fg (a * c)).left = (fg a).left ≫ (fg c).left
      rw [← hfgeq (fg a ≫ fg c) (a * c) (fun y => by rw [Category.assoc, hfg, hfg, hcomp])]
      rfl
    · intro a
      exact Over.w (fg a)
    · constructor
      intro x
      obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point S x
      obtain ⟨l, hl⟩ := hPt p D R b N 𝔞 r hcop het S s o k a
      obtain ⟨f, -, -⟩ := hrep _ l hl
      have hx : x ∈ Set.range ⇑a := by rw [ha]; rfl
      obtain ⟨q, hq⟩ := hx
      have hw : f.left ≫ π = a := Over.w f
      refine ⟨f.left q, ?_⟩
      rw [← hq, ← Scheme.Hom.comp_apply, hw]
    · intro K _ _ y y' hyy
      let j : Over.mk (y ≫ π) ⟶ Over.mk π := Over.homMk y rfl
      let j' : Over.mk (y ≫ π) ⟶ Over.mk π := Over.homMk y' hyy.symm
      have hl := GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 r _ _ lu j hlu
      have hl' := GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 r _ _ lu j' hlu
      obtain ⟨g, hg, hguniq⟩ := GlobalTheory.T.existsUnique_levGrp_of_isEtLevOver p D R b N S s o 𝔞 r K (y ≫ π) _ _ hl hl'
      refine ⟨g, ?_, ?_⟩
      · have : j ≫ fg g = j' := rep_ext hlu hrep (fun z => by rw [Category.assoc, hfg]; exact hg z)
        exact congrArg (fun q => Over.Hom.left q) this
      · intro a ha
        apply hguniq
        intro z
        show j ≫ lu (levAct a z) = j' ≫ lu z
        have : j ≫ fg a = j' := by ext1; exact ha
        rw [← hfg, ← Category.assoc, this]
  · intro T t o₁ m₁ l hl
    have hl' := (GlobalTheory.T.isEtLev_iff_isEtLevOver' p D R b N S T s t (t ≫ s) o o₁ m₁ 𝔞 r l).mp hl
    obtain ⟨g, hg, hguniq⟩ := hrep (Over.mk t) _ hl'
    have hgw : g.left ≫ π = t := Over.w g
    have hφ : ∀ (f : T ⟶ Y) (_ : f ≫ π = t) (m₃ : GlobalTheory.UPel.HT.ObjMap o₁ o (f ≫ π)), m₃.φ = m₁.φ :=
      fun f hf m₃ => Rigid.objMap_phi_unique p D R b N hN hcop S T s (t ≫ s) o o₁ (f ≫ π) t m₃ m₁ hf
    have hgl : ∀ y, (l y).left ≫ m₁.φ = g.left ≫ (lu y).left := fun y => by
      have := congrArg (fun q => Over.Hom.left q) (hg y)
      exact this.symm
    refine ⟨g.left, ⟨hgw, ?_⟩, ?_⟩
    · obtain ⟨m₂, hm₂⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ
        (by rw [hgw]; exact m₁ : GlobalTheory.UPel.HT.ObjMap o₁ o (g.left ≫ π)) m
      refine ⟨m₂, fun y => ?_⟩
      apply hpb.hom_ext
      · rw [Category.assoc, hm₂, hφ _ hgw, Category.assoc, hlv, hgl]
      · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, Over.w (l y), Category.assoc, hlv2,
          Category.comp_id]
        exact Category.id_comp _
    · rintro f' ⟨hf', m₂', hm₂'⟩
      obtain ⟨m₃, hm₃⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₂' m
      have : (Over.homMk f' hf' : Over.mk t ⟶ Over.mk π) = g := by
        apply hguniq
        intro y
        ext1
        show f' ≫ (lu y).left = (l y).left ≫ m₁.φ
        rw [← hlv, ← Category.assoc, ← hm₂' y, Category.assoc, ← hm₃, hφ f' hf' m₃]
      exact congrArg (fun q => Over.Hom.left q) this
end

