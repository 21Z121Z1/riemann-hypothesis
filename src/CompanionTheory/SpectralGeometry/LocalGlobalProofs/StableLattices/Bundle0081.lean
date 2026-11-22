import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0080
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0079

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechAcyclicityOverAffineBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjFibre

theorem cech_fibre_acyclic : ∀ {k : Type} [Field k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hac : (cechLB f (G.pull π) D).Acyclic)
    (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z) (hs : s ≫ t ≫ b = 𝟙 _) (h₁ : σ ≫ p = 𝟙 X)
    (h₂ : σ ≫ q = a ≫ s ≫ t), ∃ D' : κ → X.Opens, (∀ i, IsAffineOpen (D' i)) ∧ ⨆ i, D' i = ⊤ ∧ (cechLB a (G.pull σ) D').Acyclic := by
  intro k _ X T Z a b p q H _ _ G hG R _ t Y π f Hy κ _ _ D hD hc hac s σ hs h₁ h₂
  obtain ⟨χ, rfl⟩ : ∃ χ : R →+* k, Spec.map (CommRingCat.ofHom χ) = s :=
    ⟨(Spec.preimage s).hom, by simp⟩
  have Hx : IsPullback (π ≫ p) f a (t ≫ b) := Hy.paste_horiz H
  haveI : Flat f := MorphismProperty.of_isPullback (P := @Flat) Hx inferInstance
  haveI : IsSeparated f := MorphismProperty.of_isPullback (P := @IsSeparated) Hx inferInstance
  have hM := LB.isLB_pull hG π
  have hI := GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated f hD
  have Hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
  obtain ⟨F, π', g, Hs⟩ : ∃ (F : Scheme.{0}) (π' : F ⟶ Y) (g : F ⟶ Spec (CommRingCat.of k)),
      IsPullback π' g f (Spec.map (CommRingCat.ofHom χ)) := ⟨_, _, _, Hs⟩
  have hext := GlobalTheory.T.flat_bounded_acyclic_base_change R k χ (cechLB f (G.pull π) D) (Fintype.card κ)
    (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hM hI) hac
  have hF : (cechLB g ((G.pull π).pull π') fun i => π' ⁻¹ᵁ D i).Acyclic :=
    fun n => (hext n).of_iso (cechLBBaseChangeIso hM Hs hI)
  have Hu : IsPullback (π' ≫ π ≫ p) g a (Spec.map (CommRingCat.ofHom χ) ≫ t ≫ b) :=
    Hs.paste_horiz Hx
  rw [hs] at Hu
  obtain ⟨u, hu⟩ : ∃ u : F ⟶ X, u = π' ≫ π ≫ p := ⟨_, rfl⟩
  rw [← hu] at Hu
  haveI : IsIso u := Hu.isIso_fst_of_isIso
  have hua : u ≫ a = g := Hu.w.trans (Category.comp_id _)
  have he : u ≫ σ = π' ≫ π := by
    refine H.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, Category.comp_id, hu, Category.assoc]
    · rw [Category.assoc, h₂, ← Category.assoc, hua, Category.assoc π', Hy.w, ← Category.assoc π',
        Hs.w, Category.assoc]
  refine ⟨fun i => inv u ⁻¹ᵁ π' ⁻¹ᵁ D i,
    fun i => (isAffineOpen_preimage_of_isPullback Hs (hD i)).preimage_of_isIso _, ?_, ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, hc]
    rfl
  · have hN := LB.isLB_pull hG σ
    obtain ⟨i₁⟩ := cechLB_pull_iso_of_isOpenImmersion k X a (G.pull σ) F u κ
      (fun i => inv u ⁻¹ᵁ π' ⁻¹ᵁ D i) hN
      (fun i => by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
    have hD' : (fun i => u ⁻¹ᵁ inv u ⁻¹ᵁ π' ⁻¹ᵁ D i) = fun i => π' ⁻¹ᵁ D i := funext fun i => by
      rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id]
      rfl
    rw [hua, hD'] at i₁
    obtain ⟨w₁, hw₁⟩ := GlobalTheory.MumfordSupport.exists_iso_pull_pull hG π π'
    obtain ⟨w₂, hw₂⟩ : ∃ w : LB.Iso ((G.pull σ).pull u) (G.pull (π' ≫ π)), w.IsGen :=
      he ▸ GlobalTheory.MumfordSupport.exists_iso_pull_pull hG σ u
    have hP := LB.isLB_pull hG (π' ≫ π)
    have i₂ := cechLBCongr g (fun i => π' ⁻¹ᵁ D i) (LB.isLB_pull hM π') hP w₁ hw₁
    have i₃ := cechLBCongr g (fun i => π' ⁻¹ᵁ D i) (LB.isLB_pull hN u) hP w₂ hw₂
    exact fun n => (hF n).of_iso (i₂ ≪≫ i₃.symm ≪≫ i₁)

end GlobalTheory.CompanionTheory.PointSurjFibre
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CocycleDefinesDescendedLineBundle
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.LbCocycle

theorem gm_comp_val {W' W X : Scheme.{0}} (p : W' ⟶ W) (y : W') (f : W ⟶ X) (V : X.Opens)
    (hy : f (p y) ∈ V) (x : Γ(X, V)ˣ) :
    (gm (p ≫ f) y V x).val = (p.stalkMap y).hom (gm f (p y) V x).val := by
  rw [gm_val (p ≫ f) y V hy, gm_val f (p y) V hy, Scheme.Hom.comp_app]
  exact (Scheme.Hom.germ_stalkMap_apply p (f ⁻¹ᵁ V) y hy _).symm

theorem gm_top_val {W' X : Scheme.{0}} (V : X.Opens) (g : W' ⟶ V.toScheme) (w : W') (τ : Γ(X, V)ˣ) :
    (gm (g ≫ V.ι) w V τ).val =
      (W'.presheaf.germ ⊤ w trivial).hom (g.appTop.hom ((GlobalTheory.FunDescent.res V).hom τ.val)) := by
  have hm : (g ≫ V.ι) w ∈ V := (g w).2
  have hl : ⊤ ≤ (g ≫ V.ι) ⁻¹ᵁ V := fun x _ => (g x).2
  have e := congrArg (fun ψ => ψ.hom τ.val) (GlobalTheory.FunDescent.res_comp_appTop V g (g ≫ V.ι) rfl hl)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [gm_val _ w V hm, e, Scheme.Hom.appLE]
  exact (TopCat.Presheaf.germ_res_apply W'.presheaf (homOfLE hl) w trivial _).symm

theorem gm_global_val {W' X : Scheme.{0}} (k : W' ⟶ X) (w : W') (u : Γ(X, ⊤)ˣ) :
    (gm k w ⊤ u).val = (W'.presheaf.germ ⊤ w trivial).hom (k.appTop.hom u.val) :=
  gm_val k w ⊤ trivial u

theorem exists_local_unit (H : H90) {Z Q : Scheme.{0}} (h : Z ⟶ Q) (hf : Flat h)
    (hl : LocallyOfFinitePresentation h) (hs : Surjective h) (u : Γ(pullback h h, ⊤)) (hu : IsUnit u)
    (hc : ∀ (W : Scheme.{0}) (a b c : W ⟶ Z) (hab : a ≫ h = b ≫ h) (hbc : b ≫ h = c ≫ h),
      (pullback.lift a c (hab.trans hbc)).appTop u =
        (pullback.lift a b hab).appTop u * (pullback.lift b c hbc).appTop u) (y : Q) :
    ∃ U : Q.Opens, y ∈ U ∧ ∃ τ : Γ(Z, h ⁻¹ᵁ U)ˣ,
      ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : a ≫ h = b ≫ h) (w : W), h (a w) ∈ U →
        gm a w (h ⁻¹ᵁ U) τ = gm (pullback.lift a b hab) w ⊤ hu.unit * gm b w (h ⁻¹ᵁ U) τ := by
  obtain ⟨U, hy, t, ht, F⟩ := H Z Q h hf hl hs u hu hc y
  refine ⟨U, hy, ?_⟩
  obtain ⟨τ₀, hτ₀⟩ := (GlobalTheory.FunDescent.res_bijective (h ⁻¹ᵁ U)).2 t
  obtain ⟨σ₀, hσ₀⟩ := (GlobalTheory.FunDescent.res_bijective (h ⁻¹ᵁ U)).2 (ht.unit⁻¹).val
  have e₁ : τ₀ * σ₀ = 1 := (GlobalTheory.FunDescent.res_bijective (h ⁻¹ᵁ U)).1 (by
    rw [map_mul, map_one, hτ₀, hσ₀]
    exact ht.unit.mul_inv)
  let τ : Γ(Z, h ⁻¹ᵁ U)ˣ := ⟨τ₀, σ₀, e₁, (mul_comm _ _).trans e₁⟩
  refine ⟨τ, fun W a b hab w hw => ?_⟩
  let O : W.Opens := a ⁻¹ᵁ (h ⁻¹ᵁ U)
  have hO : ∀ x : O.toScheme, h (b (O.ι x)) ∈ U := fun x => by
    have : h (a (O.ι x)) ∈ U := x.2
    have e : h (a (O.ι x)) = h (b (O.ι x)) := congrArg (fun m : W ⟶ Q => m (O.ι x)) hab
    rwa [e] at this
  have lft : ∀ c : W ⟶ Z, (∀ x : O.toScheme, h (c (O.ι x)) ∈ U) →
      ∃ c' : O.toScheme ⟶ (h ⁻¹ᵁ U).toScheme, c' ≫ (h ⁻¹ᵁ U).ι = O.ι ≫ c := fun c hc' =>
    ⟨IsOpenImmersion.lift _ (O.ι ≫ c) (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hc' q), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨a', ha'⟩ := lft a fun x => x.2
  obtain ⟨b', hb'⟩ := lft b hO
  have hab' : (a' ≫ (h ⁻¹ᵁ U).ι) ≫ h = (b' ≫ (h ⁻¹ᵁ U).ι) ≫ h := by
    rw [ha', hb', Category.assoc, Category.assoc, hab]
  have hk : pullback.lift (a' ≫ (h ⁻¹ᵁ U).ι) (b' ≫ (h ⁻¹ᵁ U).ι) hab' = O.ι ≫ pullback.lift a b hab := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ha']
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hb']
  have E := F O.toScheme a' b' hab'
  rw [hk] at E
  obtain ⟨w', rfl⟩ : ∃ w' : O.toScheme, O.ι w' = w := ⟨⟨w, hw⟩, rfl⟩
  have hτ : (GlobalTheory.FunDescent.res (h ⁻¹ᵁ U)).hom τ.val = t := hτ₀
  have inj : Function.Injective (O.ι.stalkMap w').hom :=
    (ConcreteCategory.bijective_of_isIso (O.ι.stalkMap w')).1
  have A : (O.ι.stalkMap w').hom (gm a (O.ι w') (h ⁻¹ᵁ U) τ).val =
      (O.toScheme.presheaf.germ ⊤ w' trivial).hom (a'.appTop.hom t) := by
    rw [← gm_comp_val O.ι w' a _ hw τ, ← ha', gm_top_val, hτ]
  have B : (O.ι.stalkMap w').hom (gm b (O.ι w') (h ⁻¹ᵁ U) τ).val =
      (O.toScheme.presheaf.germ ⊤ w' trivial).hom (b'.appTop.hom t) := by
    rw [← gm_comp_val O.ι w' b _ (hO w') τ, ← hb', gm_top_val, hτ]
  have C : (O.ι.stalkMap w').hom (gm (pullback.lift a b hab) (O.ι w') ⊤ hu.unit).val =
      (O.toScheme.presheaf.germ ⊤ w' trivial).hom ((O.ι ≫ pullback.lift a b hab).appTop.hom u) := by
    rw [← gm_comp_val O.ι w' (pullback.lift a b hab) ⊤ trivial hu.unit, gm_global_val]
    rfl
  apply Units.ext
  apply inj
  rw [Units.val_mul, map_mul, A, B, C, E, map_mul]

def lbOf {Q : Scheme.{0}} (U : Q → Q.Opens) (g : ∀ y y', Γ(Q, U y ⊓ U y')ˣ) : LB Q := ⟨Q, U, g⟩

theorem exists_lb : H90 → ∀ {Z Q : Scheme.{0}} (h : Z ⟶ Q), Flat h → LocallyOfFinitePresentation h → Surjective h →
    ∀ (u : Γ(pullback h h, ⊤)) (hu : IsUnit u),
    (∀ (W : Scheme.{0}) (a b c : W ⟶ Z) (hab : a ≫ h = b ≫ h) (hbc : b ≫ h = c ≫ h),
      (pullback.lift a c (hab.trans hbc)).appTop u =
        (pullback.lift a b hab).appTop u * (pullback.lift b c hbc).appTop u) →
    ∃ N : LB Q, N.IsLB ∧ ∃ T : LB.Gen (N.pull h), T.IsGen ∧
      ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : a ≫ h = b ≫ h) (w : W) (i : N.ι), h (a w) ∈ N.U i →
        gm a w ((N.pull h).U fun _ => i) (T.s fun _ => i) =
          gm (pullback.lift a b hab) w ⊤ hu.unit * gm b w ((N.pull h).U fun _ => i) (T.s fun _ => i) := by
  intro H Z Q h hf hl hs u hu hc
  choose U hU τ hτ using fun y => exists_local_unit H h hf hl hs u hu hc y
  have D := fun V => GlobalTheory.T.flat_descent_of_units h hf hl hs V
  have l₁ : ∀ y y' : Q, h ⁻¹ᵁ (U y ⊓ U y') ≤ h ⁻¹ᵁ U y := fun _ _ _ hx => hx.1
  have l₂ : ∀ y y' : Q, h ⁻¹ᵁ (U y ⊓ U y') ≤ h ⁻¹ᵁ U y' := fun _ _ _ hx => hx.2
  have ex : ∀ y y' : Q, ∃ s : Γ(Q, U y ⊓ U y')ˣ,
      pullU h _ s = res (l₁ y y') (τ y) * (res (l₂ y y') (τ y'))⁻¹ := fun y y' =>
    (D _).2 _ fun W b c e w hw => by
      have e' : h (b w) = h (c w) := congrArg (fun m : W ⟶ Q => m w) e
      have hc₁ : c w ∈ h ⁻¹ᵁ U y := show h (c w) ∈ U y from e' ▸ hw.1
      have hc₂ : c w ∈ h ⁻¹ᵁ U y' := show h (c w) ∈ U y' from e' ▸ hw.2
      have hw' : c w ∈ h ⁻¹ᵁ (U y ⊓ U y') := ⟨hc₁, hc₂⟩
      rw [map_mul, map_mul, map_inv, map_inv, gm_res b w _ hw, gm_res b w _ hw, gm_res c w _ hw',
        gm_res c w _ hw', hτ y W b c e w hw.1, hτ y' W b c e w hw.2, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul]
  choose g hg using ex
  have ext : ∀ (V : Q.Opens) (a b : Γ(Q, V)ˣ), (∀ z : Z, h z ∈ V → gm h z V a = gm h z V b) → a = b :=
    fun V a b e => (D V).1 (unit_ext fun z hz => by
      have k : ∀ c : Γ(Q, V)ˣ, gm (𝟙 Z) z (h ⁻¹ᵁ V) (pullU h V c) = gm h z V c := fun c =>
        (gm_pull (𝟙 Z) h z V hz c).trans (by rw [Category.id_comp])
      rw [k, k]
      exact e z hz)
  have K : ∀ (W : Scheme.{0}) (f : W ⟶ Z) (w : W) (y y' : Q) (_ : h (f w) ∈ U y ⊓ U y'),
      gm (f ≫ h) w _ (g y y') = gm f w _ (τ y) * (gm f w _ (τ y'))⁻¹ := fun W f w y y' hm => by
    have hm' : f w ∈ h ⁻¹ᵁ (U y ⊓ U y') := hm
    rw [← gm_pull f h w _ hm, hg, map_mul, map_inv, gm_res f w _ hm', gm_res f w _ hm']
  have K₁ : ∀ (z : Z) (y y' : Q) (_ : h z ∈ U y ⊓ U y'),
      gm h z _ (g y y') = gm (𝟙 Z) z _ (τ y) * (gm (𝟙 Z) z _ (τ y'))⁻¹ := fun z y y' hm => by
    have := K Z (𝟙 Z) z y y' hm
    rwa [Category.id_comp] at this
  have isLB : (lbOf U g).IsLB :=
    { cover := eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hU y⟩
      g_self := fun y => ext _ _ _ fun z hz => by
        have hm : h z ∈ U y ⊓ U y := ⟨hz, hz⟩
        refine (gm_res h z _ hz _).trans ?_
        refine (K₁ z y y hm).trans ?_
        rw [map_one, mul_inv_cancel]
      cocycle := fun i j k => ext _ _ _ fun z hz => by
        have h₁ : h z ∈ U i ⊓ U j := hz.1
        have h₂ : h z ∈ U j ⊓ U k := ⟨hz.1.2, hz.2⟩
        have h₃ : h z ∈ U i ⊓ U k := ⟨hz.1.1, hz.2⟩
        refine (map_mul _ _ _).trans ?_
        refine (congrArg₂ (· * ·) ((gm_res h z _ hz _).trans (K₁ z i j h₁))
          ((gm_res h z _ hz _).trans (K₁ z j k h₂))).trans ?_
        refine Eq.trans ?_ ((gm_res h z _ hz _).trans (K₁ z i k h₃)).symm
        rw [_root_.mul_assoc, inv_mul_cancel_left] }
  have hle : ∀ J : PUnit → Q, ((lbOf U g).pull h).U J ≤ h ⁻¹ᵁ U (J PUnit.unit) :=
    fun J x hx => mem_pull.1 hx
  let T : LB.Gen ((lbOf U g).pull h) := ⟨fun J => res (hle J) (τ (J PUnit.unit))⟩
  have hT : ∀ (W : Scheme.{0}) (f : W ⟶ Z) (w : W) (J : PUnit → Q), f w ∈ ((lbOf U g).pull h).U J →
      gm f w _ (T.s J) = gm f w _ (τ (J PUnit.unit)) := fun W f w J hm => gm_res f w (hle J) hm _
  refine ⟨lbOf U g, isLB, T, ?_, ?_⟩
  · intro J J'
    apply unit_ext
    intro z hz
    have hm : h z ∈ U (J PUnit.unit) ⊓ U (J' PUnit.unit) := ⟨hle J hz.1, hle J' hz.2⟩
    refine (gm_res _ z _ hz _).trans ((hT Z (𝟙 Z) z J hz.1).trans ?_)
    refine Eq.trans ?_ (map_mul _ _ _).symm
    refine Eq.trans ?_ (congrArg₂ (· * ·) rfl (gm_res _ z _ hz _).symm)
    rw [hT Z (𝟙 Z) z J' hz.2]
    have := gm_pull_g (lbOf U g) h (𝟙 Z) z J J' hz.1 hz.2
    refine Eq.trans ?_ (congrArg₂ (· * ·) (this.trans (K Z (𝟙 Z) z _ _ hm)).symm rfl)
    rw [inv_mul_cancel_right]
  · intro W a b hab w i hi
    have e' : h (a w) = h (b w) := congrArg (fun m : W ⟶ Q => m w) hab
    have hb : h (b w) ∈ (lbOf U g).U i := e' ▸ hi
    rw [hT W a w _ (mem_pull.2 hi), hT W b w _ (mem_pull.2 hb)]
    exact hτ i W a b hab w hi

end GlobalTheory.CompanionTheory.LbCocycle
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOfSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_acyclicity_of_sections : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → FibAc a (G.pull σ)), FibAc (p ≫ a) G := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjTotal.fibAc_comp_of_fibres | exact GlobalTheory.CompanionTheory.PointSurjTotal.fibAc_comp_of_fibres | (intros; apply GlobalTheory.CompanionTheory.PointSurjTotal.fibAc_comp_of_fibres <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialOfDescendedGenerator
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FnDesc

theorem triv_of_invariant_gen : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f →
    ∀ (D : LB Q), D.IsLB → ∀ (t : LB.Gen (D.pull f)), t.IsGen →
      (∀ (W : Scheme.{0}) (a b : W ⟶ P), a ≫ f = b ≫ f → ∀ (w : W) (i : D.ι), f (a w) ∈ D.U i →
        gm a w ((D.pull f).U fun _ => i) (t.s fun _ => i) = gm b w ((D.pull f).U fun _ => i) (t.s fun _ => i)) →
      Triv D := by
  intro P Q f hfl hlf hsu D hD t ht hinv
  have hle : ∀ i : D.ι, f ⁻¹ᵁ D.U i ≤ (D.pull f).U (fun _ => i) := fun i x hx => mem_pull.2 hx
  have hex : ∀ i : D.ι, ∃ s : Γ(Q, D.U i)ˣ, pullU f (D.U i) s = res (hle i) (t.s fun _ => i) := by
    intro i
    refine (GlobalTheory.T.flat_descent_of_units f hfl hlf hsu (D.U i)).2 _ ?_
    intro W b c hbc w hw
    have hw' : f (c w) ∈ D.U i := by
      have : f (b w) = f (c w) := by
        have := congrArg (fun q : W ⟶ Q => q w) hbc
        simpa using this
      exact this ▸ hw
    rw [gm_res b w (hle i) hw, gm_res c w (hle i) hw']
    exact hinv W b c hbc w i hw
  choose s hs using hex
  have key : ∀ (i : D.ι) (x : P) (hx : f x ∈ D.U i),
      gm (𝟙 P ≫ f) x (D.U i) (s i) = gm (𝟙 P) x ((D.pull f).U fun _ => i) (t.s fun _ => i) := by
    intro i x hx
    rw [← gm_pull (𝟙 P) f x (D.U i) hx, hs i]
    exact gm_res (𝟙 P) x (hle i) hx _
  refine ⟨⟨s⟩, fun i j => ?_⟩
  apply (GlobalTheory.T.flat_descent_of_units f hfl hlf hsu (D.U i ⊓ D.U j)).1
  apply unit_ext
  intro x hx
  have hi : f x ∈ D.U i := hx.1
  have hj : f x ∈ D.U j := hx.2
  have hij : f x ∈ D.U i ⊓ D.U j := hx
  have hm : x ∈ (D.pull f).U (fun _ => i) ⊓ (D.pull f).U (fun _ => j) := ⟨mem_pull.2 hi, mem_pull.2 hj⟩
  have e := congrArg (gm (𝟙 P) x _) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, gm_res (𝟙 P) x _ hm, gm_res (𝟙 P) x _ hm] at e
  have eg : gm (𝟙 P) x ((D.pull f).U (fun _ => i) ⊓ (D.pull f).U (fun _ => j)) ((D.pull f).g (fun _ => i) (fun _ => j)) =
      gm (𝟙 P ≫ f) x _ (D.g i j) := by
    show gm (𝟙 P) x _ (∏ _k : PUnit, (res _ (pullU f _ (D.g i j))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res (𝟙 P) x _ hm _).trans (gm_pull (𝟙 P) f x (D.U i ⊓ D.U j) hij _)
  rw [eg, ← key i x hi, ← key j x hj] at e
  rw [gm_pull (𝟙 P) f x _ hij, gm_pull (𝟙 P) f x _ hij, map_mul,
    gm_res (𝟙 P ≫ f) x _ hij, gm_res (𝟙 P ≫ f) x _ hij]
  exact e

end GlobalTheory.CompanionTheory.FnDesc
end

