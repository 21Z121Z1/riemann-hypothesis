import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0612
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcComparison
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.GlobalLocalRange

theorem mem_range_generic {F : Type} [Field F] [NumberField F] (V : ValuationSubring F) (bV : 𝓞 F →+* V)
    (hbV : ∀ x, ((bV x : V) : F) = (x : F)) (v : Sp V)
    (h : spMap bV v ∈ Set.range (spMap (algebraMap (𝓞 F) F))) : v ∈ Set.range (spMap V.subtype) := by
  obtain ⟨u, hu⟩ := h
  have hu0 : u.asIdeal = ⊥ := (Ideal.eq_bot_or_top u.asIdeal).resolve_right u.isPrime.ne_top
  have hc : Ideal.comap bV v.asIdeal = ⊥ := by
    have : (spMap (algebraMap (𝓞 F) F) u).asIdeal = (spMap bV v).asIdeal := by rw [hu]
    change Ideal.comap (algebraMap (𝓞 F) F) u.asIdeal = Ideal.comap bV v.asIdeal at this
    rw [← this, hu0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)
  have hv0 : v.asIdeal = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (x : F)
    have hb0 : (algebraMap (𝓞 F) F b) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero hb)
    have hax : bV a = x * bV b := by
      apply Subtype.ext
      change ((bV a : V) : F) = ((x : V) : F) * ((bV b : V) : F)
      rw [hbV, hbV, ← hab]
      change (algebraMap (𝓞 F) F a) = _ / _ * (algebraMap (𝓞 F) F b)
      field_simp
    have ha : a ∈ Ideal.comap bV v.asIdeal := by
      rw [Ideal.mem_comap, hax]; exact v.asIdeal.mul_mem_right _ hx
    rw [hc, Ideal.mem_bot] at ha
    rw [ha, map_zero, zero_div] at hab
    rw [Ideal.mem_bot]
    exact Subtype.ext (by simpa using hab.symm)
  refine ⟨u, PrimeSpectrum.ext ?_⟩
  change Ideal.comap V.subtype u.asIdeal = v.asIdeal
  rw [hu0, hv0]
  exact Ideal.comap_bot_of_injective _ Subtype.val_injective

end GlobalTheory.GlobalLocalRange

namespace GlobalTheory.GlobalLocalRange

theorem exists_generic_preimage {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} {W : ValuationSubring ℂ}
    (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (bV : 𝓞 c.F →+* c.V W)
    (hβ : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV)
    (q : (pullback Z.s (spMap bV) : Scheme.{0}))
    (hq : pullback.snd Z.s (spMap bV) q ∈ Set.range (spMap (c.V W).subtype)) :
    ∃ w : (pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) : Scheme.{0}),
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (c.V W).subtype)
        (by rw [pullback.condition, hβ, Category.assoc]) w = q := by
  obtain ⟨u, hu⟩ := hq
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd Z.s (spMap bV))
    (g := spMap (c.V W).subtype) q u hu.symm
  have hw : pullback.fst (pullback.snd Z.s (spMap bV)) (spMap (c.V W).subtype) ≫ pullback.fst _ _ ≫ Z.s =
      pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [pullback.condition, ← Category.assoc, pullback.condition, hβ, Category.assoc]
  let L : pullback (pullback.snd Z.s (spMap bV)) (spMap (c.V W).subtype) ⟶
      pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by rw [Category.assoc, hw])
  refine ⟨L z, ?_⟩
  rw [← Scheme.Hom.comp_apply]
  have : L ≫
      pullback.lift (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) (pullback.snd _ _ ≫ spMap (c.V W).subtype)
        (by rw [pullback.condition, hβ, Category.assoc]) = pullback.fst _ _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, pullback.condition]
  rw [this, hz1]

end GlobalTheory.GlobalLocalRange

namespace GlobalTheory.GlobalLocalRange

theorem fst_mem_range_j_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ q : (pullback Z.s (spMap bV) : Scheme.{0}), pullback.fst Z.s (spMap bV) q ∈ Set.range Z.j ↔ f q ∈ Set.range Y.j := by
  intro E _ _ _ H D l Xo c p W _ _ Z Y bV hbV f t m₁ m₂ hf hj _ q
  have hβ : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV := by
    rw [← spMap_comp]
    congr 1
    exact RingHom.ext fun x => (hbV x).symm
  have hcond : pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ≫ Z.s =
      (pullback.snd Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ≫ spMap (c.V W).subtype) ≫ spMap bV := by
    rw [pullback.condition, hβ, Category.assoc]
  let e : pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ pullback Z.s (spMap bV) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (c.V W).subtype) hcond
  have he : e ≫ pullback.fst Z.s (spMap bV) = pullback.fst _ _ := pullback.lift_fst _ _ _

  have hgen : ∀ w, pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) w ∈ abLocus Z.t.G → w ∈ Set.range Z.jQ := by
    intro w hw
    rw [← Z.ab_gen]; exact hw
  constructor
  · rintro ⟨x, hx⟩
    have hs : pullback.snd Z.s (spMap bV) q ∈ Set.range (spMap (c.V W).subtype) := by
      refine mem_range_generic (c.V W) bV hbV _ ⟨pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) x, ?_⟩
      have e1 : spMap bV (pullback.snd Z.s (spMap bV) q) = Z.s (pullback.fst Z.s (spMap bV) q) := by
        rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
      have e2 : Z.s (Z.j x) = spMap (algebraMap (𝓞 c.F) c.F)
          (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) x) := by
        rw [← Scheme.Hom.comp_apply, Model.j_s, Scheme.Hom.comp_apply]
      rw [e1, ← hx, e2]
    obtain ⟨w, hw⟩ := exists_generic_preimage Z bV hβ q hs
    change e w = q at hw
    have hab : pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) w ∈ abLocus Z.t.G := by
      have h1 : Z.jQ x ∈ pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' abLocus Z.t.G := by
        rw [Z.ab_gen]; exact ⟨x, rfl⟩
      have h2 : pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) w = pullback.fst Z.s (spMap bV) q := by
        rw [← hw, ← Scheme.Hom.comp_apply, he]
      rw [h2, ← hx]
      exact h1
    obtain ⟨x', hx'⟩ := hgen w hab
    refine ⟨x', ?_⟩
    have ha : (Z.jQ ≫ e) ≫ pullback.fst Z.s (spMap bV) = Z.j := by rw [Category.assoc, he]; rfl
    rw [← hj _ ha, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx', hw]
  · rintro ⟨y, hy⟩
    have hs : pullback.snd Z.s (spMap bV) q ∈ Set.range (spMap (c.V W).subtype) := by
      refine ⟨pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) y, ?_⟩
      have e2 : Y.s (Y.j y) = spMap (c.V W).subtype
          (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) y) := by
        rw [← Scheme.Hom.comp_apply, Model.j_s, Scheme.Hom.comp_apply]
      rw [← hf, Scheme.Hom.comp_apply, ← hy, e2]
    obtain ⟨w, hw⟩ := exists_generic_preimage Z bV hβ q hs
    change e w = q at hw
    have hY : f q ∈ abLocus Y.t.G := by
      have h1 : Y.jQ y ∈ pullback.fst Y.s (spMap (c.V W).subtype) ⁻¹' abLocus Y.t.G := by
        rw [Y.ab_gen]; exact ⟨y, rfl⟩
      rw [← hy]; exact h1
    have hq : q ∈ abLocus t.G := (abLocus_pullback abLocusOne Y.t.semi m₂.cart.1 q).1 hY
    have hZ : pullback.fst Z.s (spMap bV) q ∈ abLocus Z.t.G :=
      (abLocus_pullback abLocusOne Z.t.semi m₁.cart.1 q).2 hq
    have h2 : pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) w = pullback.fst Z.s (spMap bV) q := by
      rw [← hw, ← Scheme.Hom.comp_apply, he]
    obtain ⟨x, hx⟩ := hgen w (h2 ▸ hZ)
    refine ⟨x, ?_⟩
    rw [← h2, ← hx]
    rfl

end GlobalTheory.GlobalLocalRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcFrame
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolArcData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {W : ValuationSubring ℂ}

theorem mono_spMap_incl (bV : 𝓞 c.F →+* c.V W) (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) :
    Mono (spMap bV) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  have hβ : IsDedFrac (algebraMap (𝓞 c.F) c.F) := ⟨⟨inferInstance, inferInstance⟩, inferInstance,
    (inferInstance : IsFractionRing (𝓞 c.F) c.F)⟩
  exact GlobalTheory.ModelRelCompare.mono_spMap_of_overring (β' := (c.V W).subtype) hβ Subtype.val_injective bV
    (RingHom.ext fun x => hbV x)

theorem spMap_algebraMap_eq (bV : 𝓞 c.F →+* c.V W) (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) :
    spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV := by
  rw [← spMap_comp]
  congr 1
  exact (RingHom.ext hbV).symm

theorem eq_comp_of_comp (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype)
    (bV : 𝓞 c.F →+* c.V W) (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f)
    (hf : f ≫ Y.s = pullback.snd Z.s (spMap bV)) (a₀ : Xo.XF c ⟶ pullback Z.s (spMap bV))
    (ha₀ : a₀ ≫ pullback.fst Z.s (spMap bV) = Z.j) (ha₀f : a₀ ≫ f = Y.j) {T : Scheme.{0}}
    (χ' : T ⟶ pullback Z.s (spMap bV)) (y : T ⟶ Xo.XF c) (h : y ≫ Y.j = χ' ≫ f) : χ' = y ≫ a₀ := by
  haveI := mono_spMap_incl bV hbV
  have hYj : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  have hw : (χ' ≫ pullback.fst Z.s (spMap bV)) ≫ Z.s =
      (y ≫ pullback.snd _ _) ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, pullback.condition, ← hf, spMap_algebraMap_eq bV hbV]
    simp only [← Category.assoc]
    rw [← h]
    simp only [Category.assoc]
    rw [← Category.assoc Y.j, Model.j_s]
    simp only [Category.assoc]
  have hr : Set.range (pullback.lift _ _ hw) ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Z.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    refine (abLocus_pullback abLocusOne Z.t.semi m₁.cart.1 _).2 ?_
    refine (abLocus_pullback abLocusOne Y.t.semi m₂.cart.1 _).1 ?_
    rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
    exact GlobalTheory.ThetaShiftProofs.j_mem_abLocus Y _
  have := Z.jQ_open
  have hg := IsOpenImmersion.lift_fac Z.jQ _ hr
  have e1 : χ' = IsOpenImmersion.lift Z.jQ _ hr ≫ a₀ := by
    rw [← cancel_mono (pullback.fst Z.s (spMap bV)), Category.assoc, ha₀, Model.j, ← Category.assoc, hg,
      pullback.lift_fst]
  have e2 : IsOpenImmersion.lift Z.jQ _ hr = y := by
    rw [← cancel_mono Y.j, ← ha₀f, ← Category.assoc, ← e1, ← h, ha₀f]
  rw [e1, e2]

theorem hasArcData_iff_moveV : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] (b' : c.V W →+* O') (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV))
      (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (f₀ : O' →+* R) (u : R) (χV : Sp R ⟶ pullback Z.s (spMap bV)),
      χV ≫ pullback.snd Z.s (spMap bV) = spMap f₀ ≫ spMap b' →
      (Z.HasArcData a I f₀ u (χV ≫ pullback.fst Z.s (spMap bV)) ↔
        Y.HasArcData (GlobalTheory.PolArc.moveV bV hbV b' a) I f₀ u (χV ≫ f)) := by
  intro E _ _ _ H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hf hj hc O' _ _ b' a R _ _ I f₀ u χV _
  haveI := mono_spMap_incl bV hbV
  let a₀ : Xo.XF c ⟶ pullback Z.s (spMap bV) :=
    pullback.lift Z.j (pullback.snd _ _ ≫ spMap (c.V W).subtype)
      (by rw [Model.j_s, spMap_algebraMap_eq bV hbV, Category.assoc])
  have ha₀ : a₀ ≫ pullback.fst Z.s (spMap bV) = Z.j := pullback.lift_fst _ _ _
  have ha₀f : a₀ ≫ f = Y.j := hj a₀ ha₀

  have tr : ∀ {T : Scheme.{0}} (g : T ⟶ t.G.left) (yF : T ⟶ Xo.XF c) (σZ : 𝟙_ (Over (Xo.XF c)) ⟶ Z.oF.t.G)
      (σY : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G), σZ.left ≫ Z.m0.toSABMap.φ = σY.left ≫ Y.m0.toSABMap.φ →
      g ≫ t.G.hom = yF ≫ a₀ → (g ≫ m₁.φ = yF ≫ σZ.left ≫ Z.m.φ ↔ g ≫ m₂.φ = yF ≫ σY.left ≫ Y.m.φ) := by
    intro T g yF σZ σY h0 hb
    have b₁ : σZ.left ≫ Z.oF.t.G.hom = 𝟙 _ := Over.w σZ
    have b₂ : σY.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σY
    have := dom_iff m₁ m₂ hc a₀ ha₀ g (yF ≫ σZ.left) (yF ≫ σY.left) (by rw [Category.assoc, h0, Category.assoc])
      (by rw [Category.assoc, b₁, Category.assoc, b₂]) (by rw [hb, Category.assoc, ← Category.assoc σZ.left, b₁,
        Category.id_comp])
    simpa only [Category.assoc] using this

  have base : ∀ (t' : SAB H (Sp R)) (P : PELUnif I t') (F : Type) [Field F] [Algebra (FractionRing R) F]
      (x : Out.TFK (R := R) F ⟶ P.A.A),
      (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R)) ≫ t'.G.hom = Out.jFK (R := R) F ≫ Out.jK R := by
    intro t' P F _ _ x
    have a₁ : P.U.gen.inv.left ≫ pullback.snd t'.G.hom (Out.jK R) = P.A.A.hom := Over.w P.U.gen.inv
    have a₂ : x.left ≫ P.A.A.hom = Out.jFK (R := R) F := Over.w x
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd _ _), a₁,
      ← Category.assoc, a₂]
  constructor
  · rintro ⟨t', m, P, φ, he, w, e, s1, s2, s3, s4, s5, s6⟩
    obtain ⟨n, hn⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m₁ m
    obtain ⟨m', hm'⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₂ n
    refine ⟨t', m', P, φ, he, w, e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF ha hu =>
      ⟨(s6 F uF ha hu).1, fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => ?_⟩⟩
    have hχ : Out.jFK (R := R) F ≫ Out.jK R ≫ χV = yF ≫ a₀ :=
      eq_comp_of_comp Z Y bV hbV f t m₁ m₂ hf a₀ ha₀ ha₀f _ yF (by rw [hyF]; simp only [Category.assoc])
    have hyZ : yF ≫ Z.j = Out.jFK (R := R) F ≫ Out.jK R ≫ χV ≫ pullback.fst _ _ := by
      rw [← ha₀, ← Category.assoc, ← hχ]; simp only [Category.assoc]
    have hb : (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ n.φ) ≫ t.G.hom = yF ≫ a₀ := by
      have h₀ := congrArg (· ≫ χV) (base t' P F x)
      rw [← hχ]
      simp only [Category.assoc] at h₀ ⊢
      rw [n.cart.1.w]
      exact h₀
    have go : ∀ σZ : 𝟙_ (Over (Xo.XF c)) ⟶ Z.oF.t.G, σZ.left ≫ Z.m0.toSABMap.φ = σ.left ≫ Y.m0.toSABMap.φ →
        x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ m.φ = yF ≫ σZ.left ≫ Z.m.φ := by
      intro σZ h0
      have := (tr _ yF σZ σ h0 hb).2 (by rw [hm'] at e4; simpa only [Category.assoc] using e4)
      rw [hn]; simpa only [Category.assoc] using this
    rcases hσ with ⟨hk, v, hv, rfl⟩ | ⟨hk, v, hvm, hv, rfl⟩
    · exact (s6 F uF ha hu).2 yF hyZ k p₀ (Z.oF.etaA v) (Or.inl ⟨hk, v, hv, rfl⟩) q₀ q x e1 e2 e3
        (go _ ((Z.m0.etaA v).trans (Y.m0.etaA v).symm))
    · exact (s6 F uF ha hu).2 yF hyZ k p₀ (Z.oF.eta v) (Or.inr ⟨hk, v, hvm, hv, rfl⟩) q₀ q x e1 e2 e3
        (go _ ((Z.m0.eta v).trans (Y.m0.eta v).symm))
  · rintro ⟨t', m', P, φ, he, w, e, s1, s2, s3, s4, s5, s6⟩
    obtain ⟨n, hn⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m₂ m'
    obtain ⟨m, hm⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₁ n
    refine ⟨t', m, P, φ, he, w, e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF ha hu =>
      ⟨(s6 F uF ha hu).1, fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => ?_⟩⟩
    have hχ : Out.jFK (R := R) F ≫ Out.jK R ≫ χV = yF ≫ a₀ := by
      rw [← cancel_mono (pullback.fst Z.s (spMap bV))]
      simp only [Category.assoc]
      rw [ha₀, hyF]
    have hyY : yF ≫ Y.j = Out.jFK (R := R) F ≫ Out.jK R ≫ χV ≫ f := by
      rw [← ha₀f, ← Category.assoc, ← hχ]; simp only [Category.assoc]
    have hb : (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ n.φ) ≫ t.G.hom = yF ≫ a₀ := by
      have h₀ := congrArg (· ≫ χV) (base t' P F x)
      rw [← hχ]
      simp only [Category.assoc] at h₀ ⊢
      rw [n.cart.1.w]
      exact h₀
    have go : ∀ σY : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G, σ.left ≫ Z.m0.toSABMap.φ = σY.left ≫ Y.m0.toSABMap.φ →
        x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ m'.φ = yF ≫ σY.left ≫ Y.m.φ := by
      intro σY h0
      have := (tr _ yF σ σY h0 hb).1 (by rw [hm] at e4; simpa only [Category.assoc] using e4)
      rw [hn]; simpa only [Category.assoc] using this
    rcases hσ with ⟨hk, v, hv, rfl⟩ | ⟨hk, v, hvm, hv, rfl⟩
    · exact (s6 F uF ha hu).2 yF hyY k p₀ (Y.oF.etaA v) (Or.inl ⟨hk, v, hv, rfl⟩) q₀ q x e1 e2 e3
        (go _ ((Z.m0.etaA v).trans (Y.m0.etaA v).symm))
    · exact (s6 F uF ha hu).2 yF hyY k p₀ (Y.oF.eta v) (Or.inr ⟨hk, v, hvm, hv, rfl⟩) q₀ q x e1 e2 e3
        (go _ ((Z.m0.eta v).trans (Y.m0.eta v).symm))

end GlobalTheory.PolArcData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SkewEqSumRankOneIsotropic
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem skew_eq_sum_rk1_of_finrank (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (G : Matrix (Fin N) (Fin N) E) (κ : E) (hG : ∀ a b, cc (G a b) = G b a) (hdet : G.det ≠ 0)
    (hκ : cc κ = -κ) (hκ0 : κ ≠ 0) :
    ∀ r, ∀ (W : Submodule E (Fin N → E)), Module.finrank E W = r →
      (∀ u ∈ W, ∀ v ∈ W, herm G u v = 0) → ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n →
      (∀ y, n.mulVec y ∈ W) → ∃ (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E),
        (∀ j, ξ j ∈ W) ∧ (∀ j, cc (t j) = t j) ∧ n = ∑ j, (t j * κ) • rk1 G (ξ j) (ξ j) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro W hr hW n hn hnW
  by_cases h0 : n = 0
  · exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp [h0]⟩
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_nonzero_herm_of_skew E N G κ hG hdet hκ hκ0 n hn h0
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = n.mulVec x := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = herm G ξ x := ⟨_, rfl⟩
  have hβ0 : β ≠ 0 := by rw [hβ, hξ]; exact hx
  have hβcc : cc β = -β := by
    rw [hβ, cc_herm G hG, hξ]
    have := hn x x
    linear_combination this
  obtain ⟨c, hc⟩ : ∃ c : E, c = -β⁻¹ := ⟨_, rfl⟩
  obtain ⟨t0, ht0⟩ : ∃ t0 : E, t0 = -(κ * β)⁻¹ := ⟨_, rfl⟩
  have hct : c = t0 * κ := by rw [hc, ht0]; field_simp
  have ht0cc : cc t0 = t0 := by rw [ht0, cc_neg, cc_inv, cc_mul, hκ, hβcc, neg_mul_neg]
  have hcc : cc c = -c := by rw [hc, cc_neg, cc_inv, hβcc, inv_neg]
  have hcβ : c * β = -1 := by rw [hc]; field_simp
  obtain ⟨n1, hn1⟩ : ∃ n1, n1 = n - c • rk1 G ξ ξ := ⟨_, rfl⟩
  have h1 : ∀ y, n1.mulVec y = n.mulVec y - (c * herm G y ξ) • ξ := by
    intro y
    rw [hn1, Matrix.sub_mulVec, Matrix.smul_mulVec, one_add_smul_vecMulVec_mulVec, smul_smul]
  have hsk : IsSkew G n1 := by
    intro y z
    rw [h1 y, h1 z, herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right, hn y z, cc_mul,
      hcc, cc_herm G hG]
    ring
  let f : (Fin N → E) →ₗ[E] E :=
    { toFun := fun v => herm G v x
      map_add' := fun a b => herm_add_left G a b x
      map_smul' := fun a v => by simp only [herm_smul_left, RingHom.id_apply, smul_eq_mul] }
  let W' : Submodule E (Fin N → E) := W ⊓ LinearMap.ker f
  have hξW : ξ ∈ W := hξ ▸ hnW x
  have hn1W : ∀ y, n1.mulVec y ∈ W' := by
    intro y
    refine ⟨?_, ?_⟩
    · rw [h1]; exact W.sub_mem (hnW y) (W.smul_mem _ hξW)
    · show herm G (n1.mulVec y) x = 0
      rw [h1, herm_sub_left, herm_smul_left, ← hβ]
      have := hn y x
      rw [← hξ] at this
      linear_combination this - herm G y ξ * hcβ
  have hlt : W' < W := by
    refine SetLike.lt_iff_le_and_exists.2 ⟨inf_le_left, ξ, hξW, fun h => hβ0 ?_⟩
    have : herm G ξ x = 0 := h.2
    rw [hβ, this]
  have hrk : Module.finrank E W' < r := hr ▸ Submodule.finrank_lt_finrank_of_lt hlt
  obtain ⟨d, ξ', t', hmem, hreal, heq⟩ := ih _ hrk W' rfl
    (fun u hu v hv => hW u hu.1 v hv.1) n1 hsk hn1W
  refine ⟨d + 1, Fin.cons ξ ξ', Fin.cons t0 t', ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hξW
    · simpa using (hmem j).1
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using ht0cc
    · simpa using hreal j
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← heq, ← hct, hn1]
    abel

theorem skew_eq_sum_rk1 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (G : Matrix (Fin N) (Fin N) E) (κ : E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 →
    cc κ = -κ → κ ≠ 0 → ∀ (W : Submodule E (Fin N → E)), (∀ u ∈ W, ∀ v ∈ W, herm G u v = 0) →
    ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n → (∀ y, n.mulVec y ∈ W) →
    ∃ (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E), (∀ j, ξ j ∈ W) ∧ (∀ j, cc (t j) = t j) ∧
      n = ∑ j, (t j * κ) • rk1 G (ξ j) (ξ j) := by
  intro E _ _ _ N G κ hG hdet hκ hκ0 W hW n hn hnW
  exact skew_eq_sum_rk1_of_finrank E N G κ hG hdet hκ hκ0 _ W rfl hW n hn hnW

end GlobalTheory.UnipKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTop
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan

namespace GlobalTheory.PeriodSpan

theorem span_ker_eq_top : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsSemiAbelian G → ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective (e) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) ∧ (∀ w, ∃! v : epsPt (y) ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt (y) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) → Submodule.span ℂ {z | e z = 1} = ⊤ := by
  intro X G _ y g e hG ⟨hadd, hsurj, hhol, _, hd2⟩
  have hhol' : IsHolTo Set.univ (fun z => (e z).left) := hhol
  have h0 : e 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hsub : ∀ z w, e (z - w) = e z * (e w)⁻¹ := fun z w =>
    eq_mul_inv_of_mul_eq (by rw [← hadd, sub_add_cancel])
  by_contra hne
  obtain ⟨ℓ, hℓ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have hℓK : ∀ z, e z = 1 → ℓ z = 0 := fun z hz => hle (Submodule.subset_span hz)
  have hℓeq : ∀ z w, e z = e w → ℓ z = ℓ w := fun z w h => by
    have := hℓK (z - w) (by rw [hsub, h, mul_inv_cancel])
    rwa [map_sub, sub_eq_zero] at this
  let lam : (Over.mk y ⟶ G) → ℂ := fun x => ℓ (hsurj x).choose
  have hlam : ∀ z, lam (e z) = ℓ z := fun z => hℓeq _ _ (hsurj (e z)).choose_spec
  let S : Subgroup (Over.mk y ⟶ G) :=
    { carrier := {x | lam x = 0}
      one_mem' := by
        show lam 1 = 0
        rw [← h0, hlam, map_zero]
      mul_mem' := by
        intro x x' hx hx'
        obtain ⟨a, rfl⟩ := hsurj x
        obtain ⟨b, rfl⟩ := hsurj x'
        show lam (e a * e b) = 0
        have hx : lam (e a) = 0 := hx
        have hx' : lam (e b) = 0 := hx'
        rw [← hadd, hlam, map_add, ← hlam, ← hlam, hx, hx', add_zero]
      inv_mem' := by
        intro x hx
        obtain ⟨a, rfl⟩ := hsurj x
        have hx : lam (e a) = 0 := hx
        show lam (e a)⁻¹ = 0
        have hinv : (e a)⁻¹ = e (-a) :=
          inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
        rw [hinv, hlam, map_neg, ← hlam, hx, neg_zero] }
  have hper : perHolSub G y ≤ S := by
    refine Subgroup.closure_le _ |>.2 (Set.iUnion₂_subset fun ψ hψ => Set.range_subset_iff.2 fun s => ?_)
    obtain ⟨hψadd, hψhol, hψper⟩ := hψ
    obtain ⟨h, hh, -⟩ := (GlobalTheory.holomorphic_hom_determined X G).2.2.1 y ℂ g ψ e hψadd hadd hψhol hhol' hd2
    have hlin : ∀ s : ℂ, h s = s • h 1 := fun s => by rw [← h.map_smul, smul_eq_mul, _root_.mul_one]
    have h1 : ℓ (h 1) = 0 := by
      have h2 : ℓ (h (2 * Real.pi * Complex.I)) = 0 := hℓK _ (by rw [← hh, hψper])
      rw [hlin, map_smul, smul_eq_mul] at h2
      refine (mul_eq_zero.1 h2).resolve_left ?_
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    show lam (ψ s) = 0
    rw [hh, hlam, hlin, map_smul, h1, smul_zero]
  obtain ⟨E⟩ := hG.fibres ℂ y
  have htor : ∀ x ∈ torusPts G y E, lam x = 0 := fun x hx => hper (GlobalTheory.T.torusPoints_subset_holPeriodicOneParamSpan X G y E hx)
  obtain ⟨C, hC, hCz⟩ := GlobalTheory.T.exists_compact_representatives_mod_torusPoints X G y g e E hG hadd hsurj hhol' hd2
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (LinearMap.continuous_of_finiteDimensional ℓ).continuousOn
  have hbd : ∀ z, ‖ℓ z‖ ≤ M := fun z => by
    obtain ⟨c, hc, hzc⟩ := hCz z
    have := htor _ hzc
    rw [hlam, map_sub, sub_eq_zero] at this
    rw [this]
    exact hM c hc
  apply hℓ0
  refine LinearMap.ext fun z => ?_
  by_contra hz0
  have hz : ℓ z ≠ 0 := by simpa using hz0
  have hpos : 0 < ‖ℓ z‖ := norm_pos_iff.2 hz
  have := hbd ((((|M| + 1) / ‖ℓ z‖ : ℝ) : ℂ) • z)
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_mul_cancel₀ _ hpos.ne'] at this
  linarith [le_abs_self M]

end GlobalTheory.PeriodSpan
end

