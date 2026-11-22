import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegrallyClosedOverring
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0987
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberDividingThetaConstantNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

theorem UMem.yK_th_ne_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ hd h0
  obtain ⟨c, -, h⟩ := GlobalTheory.ZH.GoodOut.exists_th_notMem GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 X₁.ρ
    ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime 𝔪.yK⟩ 0
  refine h (RingHom.mem_ker.2 ?_)
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (0 + c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1] at e
  rw [𝔪.yK_eq] at h0 ⊢
  exact e.trans ((congrArg (_ * ·) h0).trans (mul_zero _))

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperSetup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.Transport

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

open GlobalTheory.Poinc.Extend in

theorem extend {O Ω Γ : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω]
    [IsFractionRing O Ω] {S₁ S₂ T₁ T₂ U K : Scheme.{0}} [U.IsSeparated] {A₁ : Over S₁} {A₂ : Over S₂} {G₁ : Over T₁}
    {G₂ : Over T₂} [GrpObj G₁] [GrpObj G₂] (ab₁ : IsAbelianScheme G₁) (ab₂ : IsAbelianScheme G₂) {σ₁ : T₁ ⟶ S₁}
    {σ₂ : T₂ ⟶ S₂} {α₁ : G₁.left ⟶ A₁.left} {α₂ : G₂.left ⟶ A₂.left} (hα₁ : IsPullback α₁ G₁.hom A₁.hom σ₁)
    (hα₂ : IsPullback α₂ G₂.hom A₂.hom σ₂) (k₁ : Sp O ⟶ T₁) (k₂ : Sp O ⟶ T₂) (β₁ : G₁.left ⟶ U) (β₂ : G₂.left ⟶ U)
    (t₁ : Γ → (S₁ ⟶ A₁.left)) (t₂ : Γ → (S₂ ⟶ A₂.left)) (ht₁ : ∀ x, t₁ x ≫ A₁.hom = 𝟙 _) (ht₂ : ∀ x, t₂ x ≫ A₂.hom = 𝟙 _)
    {P : Over (Sp Ω)} [GrpObj P] {a₁ : P.left ⟶ G₁.left} {a₂ : P.left ⟶ G₂.left}
    (h₁ : IsGrpPullback P G₁ (spMap (algebraMap O Ω) ≫ k₁) a₁) (h₂ : IsGrpPullback P G₂ (spMap (algebraMap O Ω) ≫ k₂) a₂)
    (hβ : a₁ ≫ β₁ = a₂ ≫ β₂)
    (hx : ∀ x, ∃ w : Sp Ω ⟶ P.left, w ≫ a₁ ≫ α₁ = (spMap (algebraMap O Ω) ≫ k₁ ≫ σ₁) ≫ t₁ x ∧
      w ≫ a₂ ≫ α₂ = (spMap (algebraMap O Ω) ≫ k₂ ≫ σ₂) ≫ t₂ x)
    (v : K ⟶ Sp O) {A : Over K} [GrpObj A] {e₁ : A.left ⟶ G₁.left} (he : IsGrpPullback A G₁ (v ≫ k₁) e₁) :
    ∃ e₂ : A.left ⟶ G₂.left, IsGrpPullback A G₂ (v ≫ k₂) e₂ ∧ e₁ ≫ β₁ = e₂ ≫ β₂ ∧
      ∀ x, ∃ w : K ⟶ A.left, w ≫ A.hom = 𝟙 _ ∧ w ≫ e₁ ≫ α₁ = (v ≫ k₁ ≫ σ₁) ≫ t₁ x ∧
        w ≫ e₂ ≫ α₂ = (v ≫ k₂ ≫ σ₂) ≫ t₂ x := by
  obtain ⟨Q₁, _, b₁, g₁⟩ : ∃ (Q : Over (Sp O)) (_ : GrpObj Q) (b : Q.left ⟶ G₁.left), IsGrpPullback Q G₁ k₁ b :=
    ⟨_, _, _, isGrpPullback_pullback G₁ k₁⟩
  obtain ⟨Q₂, _, b₂, g₂⟩ : ∃ (Q : Over (Sp O)) (_ : GrpObj Q) (b : Q.left ⟶ G₂.left), IsGrpPullback Q G₂ k₂ b :=
    ⟨_, _, _, isGrpPullback_pullback G₂ k₂⟩
  obtain ⟨c₁, l₁, rfl⟩ := exists_factor g₁ h₁
  obtain ⟨c₂, l₂, rfl⟩ := exists_factor g₂ h₂
  obtain ⟨d, ld, rfl⟩ := exists_factor g₁ he
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp O) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have hj : IsGenericPointHom (spMap (algebraMap O Ω)) := IsGenericPointHom.fractionField O Ω
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  have s₁ := isSemiAbelian_of_isAbelianScheme Q₁ (PolPull.isAbelianScheme_of_isGrpPullback ab₁ g₁)
  have s₂ := isSemiAbelian_of_isAbelianScheme Q₂ (PolPull.isAbelianScheme_of_isGrpPullback ab₂ g₂)
  have := s₁.smooth
  have := s₂.smooth
  have := s₁.separated
  have := s₂.separated
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := semiAbelianHomExtension_holds.generic_of_isGrpPullback hn hj s₁ s₂ l₁ l₂ (𝟙 P)
  obtain ⟨F', ⟨-, eF'⟩, -⟩ := semiAbelianHomExtension_holds.generic_of_isGrpPullback hn hj s₂ s₁ l₂ l₁ (𝟙 P)
  rw [Over.id_left, Category.id_comp] at eF eF'
  let I : Q₁ ≅ Q₂ :=
    ⟨F, F', ExtUnique.over_hom_ext_of_isPullback l₁.1 (by
        rw [Over.comp_left, ← Category.assoc, ← eF, ← eF', Over.id_left, Category.comp_id]),
      ExtUnique.over_hom_ext_of_isPullback l₂.1 (by
        rw [Over.comp_left, ← Category.assoc, ← eF', ← eF, Over.id_left, Category.comp_id])⟩
  have : IsMonHom I.hom := hF
  have g₂' : IsGrpPullback Q₁ G₂ k₂ (F.left ≫ b₂) :=
    ((isGrpPullback_of_iso I).comp g₂).congr (Category.id_comp _) rfl
  have : IsSchemeTheoreticallyDominant c₁ := .of_isPullback l₁.1.flip
  have hb : b₁ ≫ β₁ = F.left ≫ b₂ ≫ β₂ :=
    ExtUnique.hom_ext_of_dominant (terminal.from U) (terminal.hom_ext _ _) c₁ (by
      rw [← Category.assoc, hβ, eF, Category.assoc, Category.assoc])
  refine ⟨d ≫ F.left ≫ b₂, ld.comp g₂', by rw [Category.assoc, hb, Category.assoc, Category.assoc], fun x => ?_⟩
  obtain ⟨w, u₁, u₂⟩ := hx x
  obtain ⟨d₁, v₁, z₁, w₁⟩ := exists_sec (g₁.1.paste_horiz hα₁) l₁.1.w (t₁ x) (ht₁ x) w (by
    simpa only [Category.assoc] using u₁)
  obtain ⟨d₂, v₂, z₂, w₂⟩ := exists_sec (g₂.1.paste_horiz hα₂) l₂.1.w (t₂ x) (ht₂ x) w (by
    simpa only [Category.assoc] using u₂)
  have : Surjective (w ≫ P.hom) := ⟨fun y => ⟨y, Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
  have hd : d₁ ≫ F.left = d₂ := ext_of_isDominant_of_isSeparated Q₂.hom
    (by rw [Category.assoc, Over.w, z₁, z₂]) ((w ≫ P.hom) ≫ spMap (algebraMap O Ω))
    (by rw [← Category.assoc, w₁, w₂, eF, Category.assoc])
  have sq : (v ≫ d₁) ≫ Q₁.hom = 𝟙 K ≫ v := by rw [Category.assoc, z₁, Category.comp_id, Category.id_comp]
  have e := ld.1.lift_fst _ _ sq
  refine ⟨ld.1.lift _ _ sq, ld.1.lift_snd _ _ sq, ?_, ?_⟩
  · rw [Category.assoc, reassoc_of% e, v₁]; simp only [Category.assoc]
  · rw [Category.assoc, Category.assoc, reassoc_of% e, reassoc_of% hd, v₂]; simp only [Category.assoc]

section Model

variable {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
  [Algebra Ω Ω'] {M : RatModel o Ω} {M' : RatModel o' Ω'} {f : M'.Z ⟶ M.Z}

theorem valF_app (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {U : M.Z.Opens}
    (hU : (U : Set M.Z).Nonempty) (a : Γ(M.Z, U)) :
    valF M'.pt (f ⁻¹ᵁ U) (f.app U a) = algebraMap Ω Ω' (valF M.pt U a) := by
  refine (GlobalTheory.Points.valR_comp M'.pt f U a).symm.trans ?_
  rw [hf]
  exact GlobalTheory.Points.valR_spMap_comp _ M.pt U (M.top_le_preimage_pt hU) a

theorem map_mem_O (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {z : M'.Z} {x : Ω}
    (hx : x ∈ M.O (f z)) : algebraMap Ω Ω' x ∈ M'.O z := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  exact ⟨f ⁻¹ᵁ U, f.app U a, hz, valF_app hf ⟨_, hz⟩ a⟩

theorem val_comp (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {K : Type} [Field K] (y : Sp K ⟶ M'.Z)
    (w : Sp K) {x : Ω} (hx : x ∈ M.O (f (y w))) : M.val (y ≫ f) x = M'.val y (algebraMap Ω Ω' x) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ (f ⁻¹ᵁ U : M'.Z.Opens) := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [RatModel.val_eq h1 (valF_app hf ⟨_, hz⟩ a), RatModel.val_valF (U := U) (by rintro _ ⟨w', rfl⟩; exact h1 ⟨w', rfl⟩)]
  exact GlobalTheory.Points.valR_comp y f U a

end Model

theorem pt_iff {K C R : Type} [CommRing K] [CommRing C] [CommRing R] {A : Over (Sp K)} {G : Over (Sp R)} {h : R →+* K}
    {a : A.left ⟶ G.left} (c : IsPullback a A.hom G.hom (spMap h)) (j : K →+* C) {s : Sp R ⟶ G.left} {w : Sp K ⟶ A.left}
    (hw : w ≫ A.hom = 𝟙 _) (hs : w ≫ a = spMap h ≫ s) (x : Sp C ⟶ A.left) (hx : x ≫ A.hom = spMap j) :
    x ≫ a = spMap (j.comp h) ≫ s ↔ x = spMap j ≫ w := by
  rw [spMap_comp₂, Category.assoc, ← hs]
  constructor
  · intro e
    exact c.hom_ext (by rw [e, Category.assoc]) (by rw [hx, Category.assoc, hw, Category.comp_id])
  · intro e
    rw [e, Category.assoc]

theorem isSeparated_univ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) : Xo.univ.t.G.left.IsSeparated := by
  have := Xo.univ.t.semi.separated
  have : IsSeparated Xo.s := by
    obtain ⟨N, i, hi, -, e⟩ := Xo.qproj
    have : IsSeparated (PSpace.str (KA l) N) := by
      unfold PSpace.str
      infer_instance
    rw [← e]
    infer_instance
  refine ⟨?_⟩
  rw [← terminal.comp_from (Xo.univ.t.G.hom ≫ Xo.s)]
  infer_instance

end GlobalTheory.UPoinc.Transport

open GlobalTheory.UPoinc.Transport in

theorem GlobalTheory.UPoinc.uTest_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame X₁.ρ ρ' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → spMap (ratHull R').val.toRingHom ≫ u' = X₁.uΩ → R' ≤ X₁.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀) (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (u₂' : Sp (ratHull R₂) ⟶ Xo.XF cf), USame D.X.ρ ρ₂ (fun x => x) (RingHom.id _) → ρ₂.i₀ = D.X.ρ.i₀ → spMap (ratHull R₂).val.toRingHom ≫ u₂' = D.X.uΩ → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₂ ρ₂.P.A (spMap (toRat R₂)) α₂ → IsGrpPullback G₂ Xo.univ.t.G (u₂' ≫ pullback.fst _ _) β₂ → LBIso (ρ₂.P.L.pull α₂) (Xo.univ.t.PP.L.pull β₂) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) → (∀ a : D.X.o₁, ‖y₂ (algebraMap D.X.o₁ R₂ a)‖ ≤ 1) → (∃ (P₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj P₀) (a : P₀.left ⟶ G.left) (a₂ : P₀.left ⟶ G₂.left), IsGrpPullback P₀ G (spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (ratHull R').val.toRingHom)) a ∧ IsGrpPullback P₀ G₂ (spMap (ratHull R₂).val.toRingHom) a₂ ∧ a ≫ β = a₂ ≫ β₂ ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ P₀.left, w ≫ a ≫ α = spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom) ≫ (ρ'.pt x).left ∧ w ≫ a₂ ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt (D.lab x)).left) → ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧ (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧ (∀ x₂ (w₂ : Sp (PadicAlgCl p) ⟶ G₂.left), w₂ ≫ α₂ = x₂.left ≫ u₂.φ → ∃ w : Sp (PadicAlgCl p) ⟶ G.left, w ≫ α = (T x₂).left ≫ u.φ ∧ w ≫ β = w₂ ≫ β₂) ∧ (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧ (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  intro E _ _ _ H Dw l Xo cf C X₁ D p _ z₁ ct y h c₀ hc R' fg frac hth hev ρ' u' _ _ _ hR' G _ α β hα hβ hL y₀ hy₀ u
    c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ u₂' _ _ _ hR₂ G₂ _ α₂ β₂ hα₂ hβ₂ hL₂ y₂ hy₂ _ ⟨P₀, _, a, a₂, ha, ha₂, hab, hpt⟩
  obtain ⟨V₂, _, _, _, _, hV₂c, hV₂n, σ, hσ, hval⟩ :=
    GlobalTheory.UPoinc.exists_complete_dvr_values_unitary E H Dw l Xo cf C X₁ D p z₁ ct y h u.V u.complete u.norm_le
  obtain ⟨u₁, τ, e, T, hτ, hpsi, hT, hfw, hbw⟩ :=
    GlobalTheory.Poinc.UTestBaseChange.baseChange _ _ _ ρ' p y₀ u V₂ hV₂c hV₂n σ hσ
  let j : FractionRing u₁.V →+* PadicAlgCl p := algebraMap _ _
  have hf' : j.comp u₁.yK = y₀ := u₁.fac
  haveI := X₁.ar.char
  haveI := D.X.ar.char
  haveI := isSeparated_univ Xo

  set x₂ := (gPt p ≫ y) (closedPoint (PadicAlgCl p)) with hx₂
  have hx₁ : (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) = D.q x₂ := by
    rw [← h, ← Category.assoc]; rfl
  haveI : IsDedekindDomain D.X.o₁ := ArithBase.ded (Ω := D.X.Ω₁)
  haveI : IsNoetherianRing (D.X.M.O x₂) := D.X.M.isNoetherianRing_O x₂
  haveI : IsIntegrallyClosed (D.X.M.O x₂) := haveI := D.X.normal; RatModel.isIntegrallyClosed_O (GlobalTheory.IsNormalScheme.pred _) x₂
  have hmem : ∀ a : R', algebraMap X₁.Ω₁ D.X.Ω₁ a ∈ D.X.M.O x₂ := fun a =>
    map_mem_O D.gen (hx₁ ▸ hR' a.2)
  let g₁ : R' →+* D.X.M.O x₂ := ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom).codRestrict _ hmem
  let g₂ : R₂ →+* D.X.M.O x₂ := (Subalgebra.inclusion hR₂).toRingHom

  have hrg : Set.range (gPt p ≫ y) = {x₂} := RatModel.range_eq_singleton _ _
  let vO : D.X.M.O x₂ →+* PadicAlgCl p := D.X.M.valHom (gPt p ≫ y) x₂ hrg
  have hvr : ∀ a, vO a ∈ j.range := fun a => by
    obtain ⟨b, hb⟩ := hval a a.2
    exact ⟨τ b, (RingHom.congr_fun hτ b).trans hb⟩
  let jE : FractionRing u₁.V ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict ⟨fun a b hab => j.injective
    (congrArg Subtype.val hab), j.rangeRestrict_surjective⟩
  let v : D.X.M.O x₂ →+* FractionRing u₁.V := jE.symm.toRingHom.comp (vO.codRestrict j.range hvr)
  have hjv : ∀ a, j (v a) = vO a := fun a => congrArg Subtype.val (jE.apply_symm_apply (vO.codRestrict j.range hvr a))
  have hf₂ : j.comp (v.comp g₂) = y₂ := RingHom.ext fun a => (hjv _).trans (hy₂ a).symm
  have hf'v : u₁.yK = v.comp g₁ := RingHom.ext fun a => j.injective <| by
    rw [← RingHom.comp_apply j u₁.yK, hf', hy₀ a, RingHom.comp_apply, hjv]
    show X₁.M.val (gPt p ≫ ct.y) a = D.X.M.val (gPt p ≫ y) (algebraMap X₁.Ω₁ D.X.Ω₁ a)
    rw [← h, ← Category.assoc]
    have hm : (a : X₁.Ω₁) ∈ X₁.M.O (D.q ((gPt p ≫ y) (closedPoint (PadicAlgCl p)))) := hx₁ ▸ hR' a.2
    exact val_comp D.gen (gPt p ≫ y) (closedPoint (PadicAlgCl p)) hm

  have hun : ∀ n : ℤ, n ≠ 0 → IsUnit (n : D.X.M.O x₂) := fun n hn =>
    (RatModel.val_ne_zero_iff hrg _).1 (by
      show vO n ≠ 0
      rw [map_intCast]
      exact Int.cast_ne_zero.2 hn)
  have hunΩ : ∀ n : ℤ, n ≠ 0 → IsUnit (n : D.X.Ω₁) := fun n hn => IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)
  obtain ⟨k₁, hk₁, -⟩ := existsUnique_ratLift R' hun g₁
  obtain ⟨k₂, hk₂, -⟩ := existsUnique_ratLift R₂ hun g₂
  have ek₁ : (algebraMap X₁.Ω₁ D.X.Ω₁).comp (ratHull R').val.toRingHom = (algebraMap (D.X.M.O x₂) D.X.Ω₁).comp k₁ :=
    (existsUnique_ratLift R' hunΩ ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom)).unique rfl
      (by rw [RingHom.comp_assoc, hk₁]; rfl)
  have ek₂ : (ratHull R₂).val.toRingHom = (algebraMap (D.X.M.O x₂) D.X.Ω₁).comp k₂ :=
    (existsUnique_ratLift R₂ hunΩ R₂.val.toRingHom).unique rfl (by rw [RingHom.comp_assoc, hk₂]; rfl)
  have sk₁ : spMap k₁ ≫ spMap (toRat R') = spMap g₁ := by rw [← spMap_comp₂, hk₁]
  have sk₂ : spMap k₂ ≫ spMap (toRat R₂) = spMap g₂ := by rw [← spMap_comp₂, hk₂]
  have sg₁ : spMap (algebraMap (D.X.M.O x₂) D.X.Ω₁) ≫ spMap k₁ ≫ spMap (toRat R') =
      spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom) := by rw [sk₁, ← spMap_comp₂]; rfl
  have sg₂ : spMap (algebraMap (D.X.M.O x₂) D.X.Ω₁) ≫ spMap k₂ ≫ spMap (toRat R₂) = spMap R₂.val.toRingHom := by
    rw [sk₂, ← spMap_comp₂]; rfl
  have sv₁ : spMap v ≫ spMap k₁ ≫ spMap (toRat R') = spMap u₁.yK := by rw [sk₁, ← spMap_comp₂, hf'v]
  have sv₂ : spMap v ≫ spMap k₂ ≫ spMap (toRat R₂) = spMap (v.comp g₂) := by rw [sk₂, ← spMap_comp₂]
  obtain ⟨e₁, he₁, ee₁⟩ := GlobalTheory.Poinc.Extend.exists_factor (j := spMap v ≫ spMap k₁) hα
    (u₁.cart.congr (by rw [Category.assoc, sv₁]) rfl)
  obtain ⟨e₂, he₂, hee, hw⟩ := extend (Γ := X₁.S.Gam) (PolPull.isAbelianScheme_of_isGrpPullback ρ'.P.isAb hα)
    (PolPull.isAbelianScheme_of_isGrpPullback ρ₂.P.isAb hα₂) hα.1 hα₂.1 (spMap k₁) (spMap k₂) β β₂
    (fun x => (ρ'.pt x).left) (fun x => (ρ₂.pt (D.lab x)).left) (fun x => Over.w (ρ'.pt x))
    (fun x => Over.w (ρ₂.pt (D.lab x))) (ha.congr (by rw [ek₁, spMap_comp₂]) rfl)
    (ha₂.congr (by rw [ek₂, spMap_comp₂]) rfl) hab (by rw [sg₁, sg₂]; exact hpt) (spMap v) he₁
  have hcart : IsGrpPullback u₁.A.A ρ₂.P.A (spMap (v.comp g₂)) (e₂ ≫ α₂) :=
    (he₂.comp hα₂).congr (by rw [Category.assoc, sv₂]) rfl
  have hU := Xo.univ.t.PP.isLB
  have hlb : LBIso u₁.A.L (ρ₂.P.L.pull (e₂ ≫ α₂)) :=
    LBIso.trans u₁.A.isLB (pull_isLB ρ'.P.isLB _) (pull_isLB ρ₂.P.isLB _) u₁.lb
      (LBIso.trans (pull_isLB ρ'.P.isLB _) (pull_isLB hU _) (pull_isLB ρ₂.P.isLB _)
        (GenSpread.lbIso_pull_comp e₁ ee₁.symm rfl hL) (GenSpread.lbIso_pull_comp e₂ rfl hee hL₂).symm)
  let u₂ : ρ₂.UTest p y₂ :=
    { V := u₁.V, complete := u₁.complete, norm_le := u₁.norm_le, yK := v.comp g₂, fac := hf₂, A := u₁.A, φ := e₂ ≫ α₂,
      cart := hcart, lb := hlb, G := u₁.G, semi := u₁.semi, D := u₁.D, U := u₁.U }
  refine ⟨u₂, e, T, hpsi, fun x a => ?_, fun x w₂ hw₂ => ⟨x.left ≫ e₁, ?_, ?_⟩, hfw, hbw⟩
  · obtain ⟨w, w₀, w₁, w₂⟩ := hw a
    rw [sv₁, ee₁] at w₁
    rw [sv₂] at w₂
    rw [hT]
    have i₁ := pt_iff u₁.cart.1 j w₀ w₁ x.left (Over.w x)
    have i₂ := pt_iff hcart.1 j w₀ w₂ x.left (Over.w x)
    rw [hf'] at i₁
    rw [hf₂] at i₂
    exact i₂.trans i₁.symm
  · rw [hT, Category.assoc, ee₁]
  · have hw₂' : w₂ ≫ α₂ = (x.left ≫ e₂) ≫ α₂ := hw₂.trans (Category.assoc _ _ _).symm
    have : w₂ = x.left ≫ e₂ := hα₂.1.hom_ext hw₂'
      ((existsUnique_ratPoint R₂ (w₂ ≫ α₂ ≫ ρ₂.P.A.hom)).unique (by rw [Category.assoc, hα₂.1.w])
        (by rw [Category.assoc, ← hα₂.1.w, ← Category.assoc, ← hw₂', Category.assoc]))
    rw [this, Category.assoc, hee, Category.assoc]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTriangularFactorUniqueStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_triangular_factor_unique : ∀ (R : Type) [CommRing R] (m : ℕ) (n n' : Low m → R) (M M' : Matrix (Fin m) (Fin m) R), M.BlockTriangular id → M'.BlockTriangular id → IsUnit M.det → uniR n * M = uniR n' * M' → n = n' := by
  first | exact @GlobalTheory.FlagCell.uniR_unique_of_mul_eq | exact GlobalTheory.FlagCell.uniR_unique_of_mul_eq | (intros; apply GlobalTheory.FlagCell.uniR_unique_of_mul_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulProductArrowVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlipVacB

open GlobalTheory.RouteSeesaw GlobalTheory.SquareDict.AlgSmall GlobalTheory.PairLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem heis_rd (hψ : IsStdChar D ψ (-1)) (S V : HSp D) (w : WO S V) (g : WO (negSp V) S → ℂ) :
    heisO ψ S V w (rd S V g) = rd S V (heisO ψ (negSp V) S (adjO (negSp V) S w) g) := by
  rw [rd_eq, GlobalTheory.CjNeg.heis_negT' hψ, GlobalTheory.AdjLawPf.adj_heis ψ hψ.1.2.1, ← rd_eq]

theorem heisenbergOperator_externalProductOnHermitianSum (S A B : HSp D) (u : WO S (GlobalTheory.Doubling.hsum A B)) (f : WO S A → ℂ) (g : WO S B → ℂ) :
    heisO ψ S (GlobalTheory.Doubling.hsum A B) u (box2 f g) =
      box2 (heisO ψ S A (topR (A := A) (B := B) u) f) (heisO ψ S B (botR (A := A) (B := B) u) g) := by
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.MixModel.OrthDec.heisO_boxT, GlobalTheory.SeesawSumTarget.boxT_sumDec,
    GlobalTheory.MixModel.OrthDec.resT_apply, GlobalTheory.SeesawSumTarget.pA_sumDec, GlobalTheory.SeesawSumTarget.pB_sumDec]

theorem externalProduct_latticeVacua_adjoint_isLatticeVacuum (hψ : IsStdChar D ψ (-1)) {S A B : HSp D} {Λ : AddSubgroup (WO S (GlobalTheory.Doubling.hsum A B))}
    {ΛA : AddSubgroup (WO S A)} {ΛB : AddSubgroup (WO (negSp B) S)}
    (h : ∀ u ∈ Λ, topR (A := A) (B := B) u ∈ ΛA ∧ adjO (negSp B) S (botR (A := A) (B := B) u) ∈ ΛB)
    {f : WO S A → ℂ} {g : WO (negSp B) S → ℂ} (hf : IsLatVac (heisO ψ S A) ΛA f)
    (hg : IsLatVac (heisO ψ (negSp B) S) ΛB g) :
    IsLatVac (heisO ψ S (GlobalTheory.Doubling.hsum A B)) Λ (box2 f (rd S B g)) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have e1 : topR (A := A) (B := B) (2 • u) = 2 • topR (A := A) (B := B) u := rfl
    have e2 : adjO (negSp B) S (botR (A := A) (B := B) (2 • u)) = 2 • adjO (negSp B) S (botR (A := A) (B := B) u) := by
      have e3 : botR (A := A) (B := B) (2 • u) = botR (A := A) (B := B) u + botR (A := A) (B := B) u := by
        rw [two_nsmul]; rfl
      rw [e3, two_nsmul]
      exact GlobalTheory.AdjLawPf.adj_add (negSp B) S _ _
    rw [heisenbergOperator_externalProductOnHermitianSum, heis_rd hψ, e1, e2, hf.1 _ (h u hu).1, hg.1 _ (h u hu).2]
  · have h1 : IsHalf e (topR (A := A) (B := B) u) := fun a b => hh _ _
    have h2 : IsHalf e (botR (A := A) (B := B) u) := fun a b => hh _ _
    have he' : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
    rw [heisenbergOperator_externalProductOnHermitianSum, heis_rd hψ, hf.2 e he _ (h u hu).1 h1,
      hg.2 _ he' _ (h u hu).2 (GlobalTheory.AdjLawPf.adj_half (negSp B) S e _ h2)]

theorem vac_ne_zero {θ : InfFam D} {S T : HSp D} {sS sT LS LT} {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT LS LT f) :
    f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 (0 : WO S T → ℂ) = 1 := hn p hp
  simp [nrm2] at n1

theorem externalProduct_readThroughAdjoint_ne_zero {S A B : HSp D} {f : WO S A → ℂ} {g : WO (negSp B) S → ℂ} (hf : f ≠ 0) (hg : g ≠ 0) :
    box2 f (rd S B g) ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hf
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
  intro h0
  have := congrFun h0 (((GlobalTheory.BiTransfer.sumDec A B).resT S).symm (x, adjO S (negSp B) y))
  simp only [GlobalTheory.MixModel.OrthDec.boxT, AddEquiv.apply_symm_apply, Pi.zero_apply, rd] at this
  erw [GlobalTheory.AdjLawPf.adj_invol] at this
  exact mul_ne_zero hx hy this

theorem vac_eq_smul_vacB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ (fun _ => True) : Set _) = orderingsOnSpWOne G i j →
      ∀ f, IsVacO W.ψ W.θ (spW₁ G i j) (spX G i j) (W.cart (.grid i j)) (frSum AV AV₁).cart
        (G.Λ (.grid i j)) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacB ρ i j := by
  intro D T L sc G μ₀ hL W ρ i j AV AV₁ hV hV₁ Λ hΛ hlat f hf
  obtain ⟨A₁, h₁⟩ := exists_isGridFr W (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩
  have v1 := ρ.vT_is μ₀ i j i.2.le j.2
  have v2 := ρ.vX_is i j i.2 j.2.le
  have c₁ : A₁.cart = W.cart _ := funext fun s => (h₁ s).2
  have cV : AV.cart = W.cart _ := funext fun s => (hV s).2
  have cV₁ : (negFr AV₁).cart = fun s => -W.cart (.grid (i + 1) j) s := funext fun s => by rw [negFr_cart, (hV₁ s).2]
  have w1 : IsVacF W.ψ W.θ A₁ AV (ρ.vT i j) := ⟨v1.2.theta, fun s => by rw [c₁, cV]; exact v1.2.fock s⟩
  have w2 : IsVacF W.ψ W.θ (negFr AV₁) A₁ (ρ.vX i j) := ⟨v2.2.theta, fun s => by rw [c₁, cV₁]; exact v2.2.fock s⟩
  have key := fockVacuum_externalProductOnHermitianSum AV AV₁ W.ψ_std W.θ_is A₁ w1 (rd_vac W.ψ_std W.θ_is A₁ AV₁ w2)
  have e : vacB ρ i j = box2 (ρ.vT i j) (rd (spW₁ G i j) (spV₁ G i j) (ρ.vX i j)) := rfl
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have hl : IsLatVac (heisO W.ψ (spW₁ G i j) (spX G i j))
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ fun _ => True) (vacB ρ i j) := by
    rw [e]
    refine externalProduct_latticeVacua_adjoint_isLatticeVacuum W.ψ_std (fun u hu => ?_) v1.2.lat v2.2.lat
    have hu' : u ∈ orderingsOnSpWOne G i j := by rw [← hlat]; exact hu
    exact hu'
  obtain ⟨a, ha⟩ := GlobalTheory.LevelSeries.eq_smul_vacuum W.ψ_std W.θ_is (W.cart_is (.grid i j) ⟨i.2.le, j.2.le⟩)
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv (frSum AV AV₁)) s0 hΛ hf (f' := vacB ρ i j) key.1 hl
    (fun s => by have := key.2 s; rw [c₁] at this; exact this)
  have hne : vacB ρ i j ≠ 0 := by rw [e]; exact externalProduct_readThroughAdjoint_ne_zero (vac_ne_zero v1) (vac_ne_zero v2)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hne (by rw [ha, zero_smul])
  exact ⟨a⁻¹, inv_ne_zero ha0, by rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

end GlobalTheory.TopFlipVacB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRechartingClassicalTraitSameGeometricFibr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.USpread.noeth (o Ω : Type) [CommRing o] [IsNoetherianRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (z : M.Z) : IsNoetherianRing (M.O z) := by
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  exact isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

theorem GlobalTheory.UPoinc.USpread.same_of_uSame {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω']
    [Algebra o' Ω'] {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {lab : S.Gam → S'.Gam}
    {φ : Ω →+* Ω'} (h : USame ρ ρ' lab φ) :
    Same ρ (fun _ => 𝟙 _) ρ' (fun _ => 𝟙 _) lab φ := by
  obtain ⟨P₀, a, a', ha, ha', hL, hL', ht⟩ := h
  exact ⟨P₀, a, a', fun _ => 𝟙 _, ha, ha', hL, hL', fun _ => ⟨by simp, by simp⟩, ht⟩

theorem GlobalTheory.UPoinc.USpread.endo_id {R O : Type} [CommRing R] [CommRing O] [IsDomain O] (f : R →+* O)
    (hf : ∀ o : O, ∃ a b : R, f b ≠ 0 ∧ f b * o = f a) (σ : Sp O ⟶ Sp O) (h : σ ≫ spMap f = spMap f) : σ = 𝟙 _ := by
  obtain ⟨s, rfl⟩ := Spec.map_surjective σ
  rw [← Spec.map_comp] at h
  have h' := Spec.map_injective h
  have hs : ∀ r, s.hom (f r) = f r := fun r => congrArg (fun g => g.hom r) h'
  have : s = 𝟙 _ := by
    ext o
    obtain ⟨a, b, hb, e⟩ := hf o
    have e2 := congrArg s.hom e
    rw [map_mul, hs, hs, ← e] at e2
    exact mul_left_cancel₀ hb e2
  rw [this, Spec.map_id]

theorem GlobalTheory.UPoinc.USpread.sec {R₁ R₂ O M Γ : Type} [CommRing R₁] [CommRing R₂] [CommRing O] [IsDomain O] {P₁ : PolAV (Sp R₁)} {P₂ : PolAV (Sp R₂)} {f₁ : R₁ →+* O} {f₂ : R₂ →+* O} {e₁ : M → (P₁.A ⟶ P₁.A)} {e₂ : M → (P₂.A ⟶ P₂.A)} {t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)} {t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)}
    (hf : ∀ o : O, ∃ a b : R₁, f₁ b ≠ 0 ∧ f₁ b * o = f₁ a) (h : SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂) :
    ∃ (P : PolAV (Sp O)) (b₁ : P.A.left ⟶ P₁.A.left) (b₂ : P.A.left ⟶ P₂.A.left), IsGrpPullback P.A P₁.A (spMap f₁) b₁ ∧ IsGrpPullback P.A P₂.A (spMap f₂) b₂ ∧ LBIso P.L (P₁.L.pull b₁) ∧ LBIso P.L (P₂.L.pull b₂) ∧ (∀ E, ∃ e : P.A ⟶ P.A, e.left ≫ b₁ = b₁ ≫ (e₁ E).left ∧ e.left ≫ b₂ = b₂ ≫ (e₂ E).left) ∧ ∀ x, ∃ w : Sp O ⟶ P.A.left, w ≫ P.A.hom = 𝟙 _ ∧ w ≫ b₁ = spMap f₁ ≫ (t₁ x).left ∧ w ≫ b₂ = spMap f₂ ≫ (t₂ x).left := by
  obtain ⟨P, b₁, b₂, h₁, h₂, l₁, l₂, he, ht⟩ := h
  refine ⟨P, b₁, b₂, h₁, h₂, l₁, l₂, he, fun x => ?_⟩
  obtain ⟨w, w₁, w₂⟩ := ht x
  refine ⟨w, GlobalTheory.UPoinc.USpread.endo_id f₁ hf _ ?_, w₁, w₂⟩
  have := Over.w (t₁ x)
  rw [Category.assoc, ← h₁.1.w, ← Category.assoc, w₁, Category.assoc, this]
  exact Category.comp_id _

theorem GlobalTheory.UPoinc.USpread.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real), USame X.ρ ρ' (fun x => x) (RingHom.id _) → R' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X.M.val (gPt p ≫ ct.y) a) → ∀ (c₁ : X.Ω₁) (hc₁ : c₁ ≠ 0) (R'' : Subalgebra X.o₁ X.Ω₁) (fg₁ : R''.FG) (frac₁ : ∀ x : X.Ω₁, ∃ a ∈ R'', ∃ b ∈ R'', x = a / b) (hth₁ : ∀ x, c₁ * X.S.th x ∈ R'') (hev₁ : ∀ x k, c₁ * X.S.ev x k ∈ R'') (ρ'' : (X.S.rechart c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁).Real), USame X.ρ ρ'' (fun x => x) (RingHom.id _) → R'' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (y₁ : R'' →+* PadicAlgCl p), (∀ a : R'', y₁ a = X.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀) (u' : ρ''.UTest p y₁), ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u'.A.L.pull a') ∧ ∀ b : X.S.Gam, ∃ (w : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt b).left ∧ x'.left ≫ u'.φ = spMap y₁ ≫ (ρ''.pt b).left := by
  intro E _ _ _ H Dw l Xo cf C X p _ z ct c₀ hc R' fg frac hth hev ρ' hS' hR' y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' hS'' hR'' y₁ hy₁ u u'
  set z' := (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) with hz'
  haveI : IsDedekindDomain X.o₁ := ArithBase.ded (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.O z') := GlobalTheory.UPoinc.USpread.noeth X.o₁ X.Ω₁ X.M z'
  haveI : IsIntegrallyClosed (X.M.Z.presheaf.stalk z') := X.normal.isIntegrallyClosed_stalk z'
  haveI : IsIntegrallyClosed (X.M.O z') := IsIntegrallyClosed.of_equiv (X.M.stalkEquiv z')
  let ι' : R' →+* X.M.O z' := (Subalgebra.inclusion hR').toRingHom
  let ι'' : R'' →+* X.M.O z' := (Subalgebra.inclusion hR'').toRingHom
  have h0 := GlobalTheory.T.realisations_common_generic_fibre_of_common_third _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (GlobalTheory.UPoinc.USpread.same_of_uSame hS') (GlobalTheory.UPoinc.USpread.same_of_uSame hS'')
  have h1 := GlobalTheory.T.sameAt_of_sameAt_comp_algebraMap (X.M.O z') X.Ω₁ _ _ _ _ _ _ ι' ι'' _ _ _ _ h0
  let v : X.M.O z' →+* PadicAlgCl p := RatModel.valHom (gPt p ≫ ct.y) z' (RatModel.range_eq_singleton _ _)
  have e₀ : v.comp ι' = y₀ := RingHom.ext fun a => (hy₀ a).symm
  have e₁ : v.comp ι'' = y₁ := RingHom.ext fun a => (hy₁ a).symm
  have hfr : ∀ o : X.M.O z', ∃ a b : R', ι' b ≠ 0 ∧ ι' b * o = ι' a := by
    intro o
    obtain ⟨a, ha, b, hb, e⟩ := frac (o : X.Ω₁)
    by_cases hb0 : b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      have : o = 0 := Subtype.ext (by simpa [hb0] using e)
      simp [this]
    · refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hb0 (congrArg Subtype.val h), Subtype.ext ?_⟩
      change b * (o : X.Ω₁) = a
      rw [e]; field_simp
  obtain ⟨P₀, a, a', ha, ha', hL, hL', ht, -⟩ := GlobalTheory.Poinc.Special.main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.UPoinc.USpread.sec hfr h1) v u.yK u'.yK
    (u.fac.trans e₀.symm) (u'.fac.trans e₁.symm) u.A u'.A u.φ u'.φ u.cart u'.cart u.lb u'.lb
  refine ⟨P₀, a, a', ha, ha', hL, hL', fun b => ?_⟩
  obtain ⟨w, hw, h₁, h₂⟩ := ht b
  have q₁ : (w ≫ a) ≫ u.A.A.hom = jFK (R := u.V) (PadicAlgCl p) := by
    rw [Category.assoc, ha.1.w, ← Category.assoc, hw, Category.id_comp]
  have q₂ : (w ≫ a') ≫ u'.A.A.hom = jFK (R := u'.V) (PadicAlgCl p) := by
    rw [Category.assoc, ha'.1.w, ← Category.assoc, hw, Category.id_comp]
  refine ⟨w, Over.homMk (w ≫ a) q₁, Over.homMk (w ≫ a') q₂, hw, rfl, rfl, ?_, ?_⟩
  · simpa [e₀] using h₁
  · simpa [e₁] using h₂
end

