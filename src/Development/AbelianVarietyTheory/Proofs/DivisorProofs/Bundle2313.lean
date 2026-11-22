import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0053
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2301

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentredPointPhiPositive
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal

theorem core (hP : Hypotheses2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c)
    (y : Y₀ TF.X Z) (hy : y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ)
    (ν : Valuation ((Y₀ TF.X Z).presheaf.stalk y) (WithZero (Multiplicative ℤ))) (hν : Centred y ν) :
    ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ := by
  obtain ⟨h1, h2, h3⟩ := hν
  haveI := GlobalTheory.T.charZero_stalk_compactFlagSpaceOverComponent TF Z y
  haveI : IsDomain ((Y₀ TF.X Z).presheaf.stalk y) := by
    refine @NoZeroDivisors.to_isDomain _ _ inferInstance ⟨fun {a b} hab => ?_⟩
    have := congrArg ν hab
    rw [map_mul, map_zero, mul_eq_zero] at this
    exact this.imp (h3 a) (h3 b)
  obtain ⟨T, g, ρ, hρ, hinj, hloc, hval⟩ := GlobalTheory.T.exists_completeDVR_reading_centredValuation _ ν h1 h2 h3
  have hz := GlobalTheory.T.traitGenericPoint_mem_compactFlagSpaceOpenPart TF Z y T.Fr ((algebraMap T.V T.Fr).comp g)
    ((IsFractionRing.injective T.V T.Fr).comp hinj)
  obtain ⟨io, hP'⟩ := GlobalTheory.T.exists_framedPoint_of_compactFlagSpaceOpenPart TF.X T.Fr _ hz
  letI := io.toAlgebra
  obtain ⟨P, hPz⟩ := hP'
  let w : Sp T.V ⟶ TF.Y.X :=
    Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z ≫ TF.X.π
  have hw : spMap (algebraMap T.V T.Fr) ≫ w = TF.X.ptY P ≫ TF.X.π := by
    rw [hPz]
    simp only [w, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  obtain ⟨T', i, j, r, y', G, m3, Pu, t', m1, m2, hr, hv, hij, hjloc, hpt⟩ := GlobalTheory.T.exists_extension_dvr_flag_lift hP TF T io P w hw
  obtain ⟨φT, hφT⟩ := GlobalTheory.SlopeRec.exists_hasPhi y' G t' m1 m2 Pu
  have hcl : ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (f : A →+* B),
      (∀ a ∈ IsLocalRing.maximalIdeal A, f a ∈ IsLocalRing.maximalIdeal B) →
      (Spec.map (CommRingCat.ofHom f)) (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A := by
    intro A B _ _ _ _ f hf
    have : IsLocalHom f := ⟨fun a ha => by
      by_contra h
      exact (IsLocalRing.mem_maximalIdeal _).1 (hf a ((IsLocalRing.mem_maximalIdeal _).2 h)) ha⟩
    exact IsLocalRing.comap_closedPoint f
  have hpos : 0 < φT := by
    refine GlobalTheory.T.slope_phi_group_extension_dvr hP T' _ y' φT hφT G t' m1 m2 fun hab => hy ?_
    have h := GlobalTheory.T.mem_modelInterior_of_mem_abelianLocus_pullback TF.Y _ _ G m3 _ hab
    have e1 : (spMap j) (IsLocalRing.closedPoint T'.V) = IsLocalRing.closedPoint T.V := hcl j hjloc
    have e2 : (Spec.map (CommRingCat.ofHom g)) (IsLocalRing.closedPoint T.V) =
        IsLocalRing.closedPoint ((Y₀ TF.X Z).presheaf.stalk y) := hcl g hloc
    change TF.X.π (inc₀ TF.X Z ((Y₀ TF.X Z).fromSpecStalk y
      ((Spec.map (CommRingCat.ofHom g)) ((spMap j) (IsLocalRing.closedPoint T'.V))))) ∈ _ at h
    rw [e1, e2, Scheme.fromSpecStalk_closedPoint] at h
    exact h
  refine ⟨(ρ / r) * φT, mul_pos (div_pos hρ (Nat.cast_pos.2 hr)) hpos, T', i.comp io, y', j.comp g, ρ / r, φT,
    div_pos hρ (Nat.cast_pos.2 hr), hφT, rfl, ?_, ?_⟩
  · letI := (i.comp io).toAlgebra
    rw [hpt, hPz, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    rw [← RingHom.comp_assoc, hij, RingHom.comp_assoc]
  · intro a ha
    rw [hval a ha]
    have e : algebraMap T'.V T'.Fr (j (g a)) = i (algebraMap T.V T.Fr (g a)) :=
      (RingHom.congr_fun hij (g a)).symm
    rw [RingHom.comp_apply, e, hv]
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    field_simp

end GlobalTheory.DegVal

namespace GlobalTheory.DegVal

theorem exists_phiAt_pos : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ := by
  intro hP hD _ _
  refine Formalism.MainNotions.Closed.imp hD fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, h⟩ := h
  exact ⟨C, hC, x0, fun x hx hle ι p hp i _ Y _ Z TF y hy ν hν => core hP TF Z y hy ν hν⟩

end GlobalTheory.DegVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPointGenericFibre
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue.EvalPt

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

theorem norm_algebraMap_unit (p : ℕ) [Fact p.Prime] (u : (𝓞_ℂ_[p])ˣ) :
    ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (u : 𝓞_ℂ_[p])‖ = 1 := by
  have hm : ∀ a : 𝓞_ℂ_[p], ‖(a : ℂ_[p])‖ ≤ 1 := fun a => by
    have this : (Valued.v (a : ℂ_[p]) : NNReal) ≤ 1 := a.2
    rw [PadicComplex.norm_eq_norm]
    exact (Valued.toNormedField.norm_le_one_iff).2 this
  have h1 : ((u : 𝓞_ℂ_[p]) : ℂ_[p]) * ((u⁻¹ : (𝓞_ℂ_[p])ˣ) : 𝓞_ℂ_[p]) = 1 := by
    exact_mod_cast u.mul_inv
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one] at h2
  have h3 := hm (u : 𝓞_ℂ_[p])
  have h4 := hm ((u⁻¹ : (𝓞_ℂ_[p])ˣ) : 𝓞_ℂ_[p])
  show ‖((u : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1
  nlinarith [norm_nonneg ((u : 𝓞_ℂ_[p]) : ℂ_[p]), norm_nonneg (((u⁻¹ : (𝓞_ℂ_[p])ˣ) : 𝓞_ℂ_[p]) : ℂ_[p])]

theorem isUnit_natCast_fraction {F : Type} [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ)
    [Fact p.Prime] : IsUnit (p : FractionRing V) := by
  refine IsUnit.mk0 _ ?_
  intro h0
  have hV : (p : V) = 0 :=
    IsFractionRing.injective V (FractionRing V) (by rw [map_natCast, h0, map_zero])
  have hF : (p : F) = 0 := by
    have := map_natCast V.subtype p
    rw [hV, map_zero] at this
    exact this.symm
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hF

theorem isUnit_natCast_generic {F : Type} [Field F] [NumberField F] {V : ValuationSubring F}
    [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (s : X ⟶ Sp V)
    (U : (genericFibre s).Opens) : IsUnit (p : Γ(genericFibre s, U)) := by
  have h1 : IsUnit (p : Γ(Spec (.of (FractionRing V)), ⊤)) := by
    have := (isUnit_natCast_fraction V p).map (Scheme.ΓSpecIso (.of (FractionRing V))).inv.hom
    rwa [map_natCast] at this
  have h2 := h1.map (genericStr s).appTop.hom
  rw [map_natCast] at h2
  have h3 := h2.map ((genericFibre s).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
  rwa [map_natCast] at h3

theorem preimage_Xp_generic {F : Type} [Field F] [NumberField F] {V : ValuationSubring F}
    [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (s : X ⟶ Sp V) :
    genericι s ⁻¹ᵁ Xp X p = ⊤ := by
  rw [Xp, Scheme.preimage_basicOpen, map_natCast]
  exact Scheme.basicOpen_of_isUnit _ (isUnit_natCast_generic p s _)

theorem appLE_congr {T Z : Scheme.{0}} {f g : T ⟶ Z} (e : f = g) (U : Z.Opens) (V : T.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) : f.appLE U V hV = g.appLE U V (e ▸ hV) := by
  subst e; rfl

theorem appLE_top_top {T Z : Scheme.{0}} (f : T ⟶ Z) (hV : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ hV = f.appTop :=
  Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)

end GlobalTheory.UnitGlue.EvalPt

namespace GlobalTheory.UnitGlue.EvalPt
open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

theorem evalPt_norm : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x) (x : X) (φ : cR h x →+* 𝓞_ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ X), spMap φ ≫ cξ h x = yb → ∀ y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s, y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb → ∀ (e : ((glueLB h).pull yb).Gen) (cc : ℂ_[p]ˣ), GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord s (glueLB h) (sigGen h s) yb y e cc → ∃ ψ : Localization.Away (p : cR h x) →+* ℂ_[p], ψ.comp (algebraMap (cR h x) _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ ∧ ‖ψ (cu h x : Localization.Away (p : cR h x))‖ = ‖(cc : ℂ_[p])‖ := by
  intro F _ _ V _ p _ X s Xw K h x φ yb hyb y hy e cc hc
  subst hyb
  let j : PUnit → (glueLB h).ι := fun _ => x
  have hW : ∀ {T : Scheme.{0}} (f : T ⟶ X),
      LB.wchart (glueLB h) (fun _ : PUnit => f) j = f ⁻¹ᵁ Uc h x :=
    fun f => TopologicalSpace.Opens.ext (by ext z; simp [LB.wchart, glueLB, j])
  have hYb : (spMap φ ≫ cξ h x) ⁻¹ᵁ Uc h x = ⊤ := by
    change spMap φ ⁻¹ᵁ (cξ h x ⁻¹ᵁ (cξ h x ''ᵁ ⊤)) = ⊤
    rw [Scheme.Hom.preimage_image_eq]
    rfl
  have hYg : y ⁻¹ᵁ (genericι s ⁻¹ᵁ Uc h x) = ⊤ := by
    change (y ≫ genericι s) ⁻¹ᵁ Uc h x = ⊤
    rw [hy]
    change Spec.map _ ⁻¹ᵁ ((spMap φ ≫ cξ h x) ⁻¹ᵁ Uc h x) = ⊤
    rw [hYb]
    rfl
  have h₁ : (⊤ : (Spec (.of ℂ_[p])).Opens) ≤ y ⁻¹ᵁ ((glueLB h).pull (genericι s)).U j := by
    change ⊤ ≤ y ⁻¹ᵁ LB.wchart (glueLB h) (fun _ : PUnit => genericι s) j
    rw [hW, hYg]
  have h₂ : (⊤ : (Spec (.of ℂ_[p])).Opens) ≤
      Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ⁻¹ᵁ ((glueLB h).pull (spMap φ ≫ cξ h x)).U j := by
    change ⊤ ≤ Spec.map _ ⁻¹ᵁ LB.wchart (glueLB h) (fun _ : PUnit => spMap φ ≫ cξ h x) j
    rw [hW, hYb]
    exact le_top
  have hcond : LB.wchart (glueLB h) (fun _ : PUnit => genericι s) j ≤ genericι s ⁻¹ᵁ (Uc h x ⊓ Xp X p) := by
    rw [hW]
    intro z hz
    show z ∈ genericι s ⁻¹ᵁ Uc h x ⊓ genericι s ⁻¹ᵁ Xp X p
    rw [preimage_Xp_generic p s]
    exact ⟨hz, trivial⟩
  have hsig : (sigGen h s).s j = res hcond (pullU (genericι s) _ (Cx h x)) := dif_pos hcond
  have key := hc j ⊤ h₁ h₂
  rw [hsig] at key
  let χ : Γ(X, Uc h x ⊓ Xp X p) ⟶ Γ(Spec (.of ℂ_[p]), ⊤) :=
    (genericι s).appLE (Uc h x ⊓ Xp X p) _ hcond ≫ y.appLE _ ⊤ h₁
  let ψ : Localization.Away (p : cR h x) →+* ℂ_[p] :=
    (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom.comp (χ.hom.comp (ev h x))
  have hψc : ψ (cu h x : Localization.Away (p : cR h x)) = (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom
      ((res h₁ (pullU y _ (res hcond (pullU (genericι s) _ (Cx h x))))) : Γ(Spec (.of ℂ_[p]), ⊤)) := rfl
  have hF1 : (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom
      ((res (U := ⊤) (V := ⊤) le_top (constUnit (𝟙 (Spec (.of ℂ_[p]))) cc) : Γ(Spec (.of ℂ_[p]), ⊤))) = cc := by
    have hid : (homOfLE (le_top : (⊤ : (Spec (.of ℂ_[p])).Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    simp [res, constUnit, hid]
  have htop : (⊤ : (Sp 𝓞_ℂ_[p]).Opens) ≤ ((glueLB h).pull (spMap φ ≫ cξ h x)).U j := by
    change ⊤ ≤ LB.wchart (glueLB h) (fun _ : PUnit => spMap φ ≫ cξ h x) j
    rw [hW, hYb]
  have hM : (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]))).app
        (((glueLB h).pull (spMap φ ≫ cξ h x)).U j) ≫
      (Spec (.of ℂ_[p])).presheaf.map (homOfLE h₂).op ≫ (Scheme.ΓSpecIso (.of ℂ_[p])).hom =
      (Sp 𝓞_ℂ_[p]).presheaf.map (homOfLE htop).op ≫ (Scheme.ΓSpecIso (.of 𝓞_ℂ_[p])).hom ≫
        CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := by
    have e1 : (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]))).app
        (((glueLB h).pull (spMap φ ≫ cξ h x)).U j) ≫ (Spec (.of ℂ_[p])).presheaf.map (homOfLE h₂).op =
        (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]))).appLE _ ⊤ h₂ := rfl
    rw [← Category.assoc, e1, ← Scheme.Hom.map_appLE _ (U := ⊤) (by simp) (homOfLE htop).op,
      Category.assoc]
    erw [appLE_top_top]
    rw [Scheme.ΓSpecIso_naturality]
  have hF2 : (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom
      ((res h₂ (pullU (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]))) _ (e.s j))) :
        Γ(Spec (.of ℂ_[p]), ⊤)) =
      algebraMap 𝓞_ℂ_[p] ℂ_[p] ((Units.map (Scheme.ΓSpecIso (.of 𝓞_ℂ_[p])).hom.hom.toMonoidHom
        (res htop (e.s j)) : (𝓞_ℂ_[p])ˣ) : 𝓞_ℂ_[p]) := by
    have := congrArg (fun m => m.hom ((e.s j : Γ(Sp 𝓞_ℂ_[p], ((glueLB h).pull (spMap φ ≫ cξ h x)).U j)))) hM
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hinvapp : ((cξ h x).appIso ⊤).inv ≫ (cξ h x).app (Uc h x) =
      (Sp (cR h x)).presheaf.map (eqToHom (Scheme.Hom.preimage_image_eq (cξ h x) ⊤)).op := by
    show ((cξ h x).appIso ⊤).inv ≫ (cξ h x).app (cξ h x ''ᵁ ⊤) = _
    rw [Iso.inv_comp_eq, Scheme.Hom.appIso_hom, Category.assoc, ← Functor.map_comp]
    simp [Uc]
  have hinvapp' : ∀ {Z : CommRingCat.{0}} (k : Γ(Sp (cR h x), cξ h x ⁻¹ᵁ Uc h x) ⟶ Z),
      ((cξ h x).appIso ⊤).inv ≫ (cξ h x).app (Uc h x) ≫ k =
        (Sp (cR h x)).presheaf.map (eqToHom (Scheme.Hom.preimage_image_eq (cξ h x) ⊤)).op ≫ k := by
    intro Z k
    rw [← hinvapp]
    exact (Category.assoc _ _ _).symm
  have hmor : (Scheme.ΓSpecIso (.of (cR h x))).inv ≫ ((cξ h x).appIso ⊤).inv ≫
      X.presheaf.map (homOfLE (inf_le_left : Uc h x ⊓ Xp X p ≤ Uc h x)).op ≫ χ ≫
        (Scheme.ΓSpecIso (.of ℂ_[p])).hom =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := by
    rw [show χ = _ from Scheme.Hom.appLE_comp_appLE y (genericι s) _ _ _ hcond h₁]
    erw [reassoc_of% (Scheme.Hom.map_appLE (y ≫ genericι s) _ (homOfLE (inf_le_left : Uc h x ⊓ Xp X p ≤ Uc h x)).op)]
    rw [appLE_congr (hy.trans (Category.assoc _ _ _).symm), Scheme.Hom.comp_appLE, Category.assoc]
    erw [hinvapp']
    erw [reassoc_of% (Scheme.Hom.map_appLE (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ spMap φ) _ (eqToHom (Scheme.Hom.preimage_image_eq (cξ h x) ⊤)).op)]
    erw [appLE_top_top]
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, reassoc_of% (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)), Iso.inv_hom_id_assoc]
  refine ⟨ψ, ?_, ?_⟩
  · ext r
    have := congrArg (fun m => m.hom r) hmor
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    show (Scheme.ΓSpecIso _).hom.hom (χ.hom (ev h x (algebraMap _ _ r))) = algebraMap 𝓞_ℂ_[p] ℂ_[p] (φ r)
    rw [← this, ev, IsLocalization.Away.lift, IsLocalization.lift_eq]
    rfl
  · have key' := congrArg (fun u : Γ(Spec (.of ℂ_[p]), ⊤)ˣ =>
      (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom (u : Γ(Spec (.of ℂ_[p]), ⊤))) key
    dsimp only at key'
    rw [Units.val_mul, map_mul] at key'
    rw [hψc, key', hF1, hF2, norm_mul, norm_algebraMap_unit, _root_.mul_one]
end GlobalTheory.UnitGlue.EvalPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRestrEqGerm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.LogKSDiv.Spread'

theorem germ_pt' {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) {U : X.Opens} (hU : IsAffineOpen U)
    (hy : B.ι y ∈ U) :
    spMap (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y).hom ≫ hU.fromSpec = B.toScheme.fromSpecStalk y ≫ B.ι := by
  show Spec.map (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

end GlobalTheory.LogKSDiv.Spread'

set_option autoImplicit false

theorem GlobalTheory.LogKSDiv.chartRestr_eq_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ r, ρ r = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hU hx ρ hρ r
  have hη : (barComp TF.Y Z).ι (genericPoint (X₀ TF.Y Z)) ∈ U.1 := by
    have h := (genericPoint_spec (X₀ TF.Y Z)).mem_open_set_iff ((barComp TF.Y Z).ι ⁻¹ᵁ U.1).isOpen
    exact h.2 ⟨x, trivial, hx⟩
  set ψ := (TF.Y.X.presheaf.germ U.1 _ hη ≫ (barComp TF.Y Z).ι.stalkMap (genericPoint (X₀ TF.Y Z))).hom with hψ
  have hg := GlobalTheory.LogKSDiv.Spread'.germ_pt' (barComp TF.Y Z) (genericPoint (X₀ TF.Y Z)) U.2 hη
  have hmono : Mono (LogKS.chart U) := by
    unfold LogKS.chart
    have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    infer_instance
  have e1 : spMap ρ = spMap ψ := by
    rw [← cancel_mono (LogKS.chart U), hρ]
    exact hg.symm
  have e2 : ρ = ψ := by
    have := Spec.map_injective e1
    exact congrArg CommRingCat.Hom.hom this
  rw [e2, hψ, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.germ_stalkMap_apply]
  simp only [GlobalTheory.LogKSDiv.stalkHom, RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
  change _ = ((X₀ TF.Y Z).presheaf.germ _ x hx ≫ (X₀ TF.Y Z).presheaf.stalkSpecializes _).hom _
  erw [TopCat.Presheaf.germ_stalkSpecializes]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRestrictOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem isTest_comp_opens_ι {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} (U Xw : X.Opens)
    (yb : Sp 𝓞_ℂ_[p] ⟶ U.toScheme) (h : IsTest p (U.ι ⁻¹ᵁ Xw) yb) : IsTest p Xw (yb ≫ U.ι) := by
  obtain ⟨⟨T, kO, yT, hT, hk, he⟩, hr⟩ := h
  refine ⟨⟨T, kO, yT ≫ U.ι, hT, hk, by rw [← Category.assoc, he]⟩, ?_⟩
  rintro _ ⟨w, rfl⟩
  have := hr ⟨w, rfl⟩
  simpa [Scheme.Hom.comp_apply] using this

theorem chartAt_opens_restrict : ∀ (p n : ℕ) [Fact p.Prime] (X : Scheme.{0}) (U Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p])
    (x : U.toScheme), ChartAt p n Xw K (U.ι x) → ChartAt p n (U.ι ⁻¹ᵁ Xw) (fun yb => K (yb ≫ U.ι)) x := by
  intro p n _ X U Xw K x h
  obtain ⟨R, _, ξ, J, _, Q, u, hξ, ⟨z, hz⟩, hT⟩ := h
  have hxU : U.ι x ∈ (U : Set X) := by rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
  have hzU : z ∈ ((ξ ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R)) := by
    show ξ z ∈ U
    rw [hz]; exact hxU
  obtain ⟨_, ⟨f, rfl⟩, hzf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hzU (ξ ⁻¹ᵁ U).isOpen
  let ι' := algebraMap R (Localization.Away f)
  have hrange : Set.range (spMap ι') = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hsub : Set.range (spMap ι' ≫ ξ) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    have hy : (spMap ι') y ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := hrange ▸ ⟨y, rfl⟩
    exact hfU hy
  obtain ⟨ξ₁, hfac⟩ : ∃ ξ₁ : Sp (Localization.Away f) ⟶ U.toScheme, ξ₁ ≫ U.ι = spMap ι' ≫ ξ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hsub⟩
  have hξ₁ : IsOpenImmersion ξ₁ := by
    haveI : IsOpenImmersion (ξ₁ ≫ U.ι) := by rw [hfac]; infer_instance
    exact IsOpenImmersion.of_comp ξ₁ U.ι
  let Q' : J → Localization.Away f := fun j => ι' (Q j)
  have hunit : ∀ j, IsUnit (((algebraMap (Localization.Away f) (Localization.Away ((p : Localization.Away f) * Q' j))).comp ι')
      ((p : R) * Q j)) := by
    intro j
    rw [RingHom.comp_apply, map_mul, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨g, hg⟩ : ∃ g : ∀ j, Localization.Away ((p : R) * Q j) →+* Localization.Away ((p : Localization.Away f) * Q' j),
      ∀ j, (g j).comp (algebraMap R _) = (algebraMap (Localization.Away f) _).comp ι' :=
    ⟨fun j => IsLocalization.Away.lift ((p : R) * Q j) (hunit j),
      fun j => IsLocalization.Away.lift_comp _ (hunit j)⟩
  refine ⟨Localization.Away f, inferInstance, ξ₁, J, inferInstance, Q', fun j => Units.map (g j : _ →* _) (u j), hξ₁,
    ?_, ?_⟩
  · have hz' : z ∈ Set.range (spMap ι') := hrange ▸ hzf
    obtain ⟨z', rfl⟩ := hz'
    refine ⟨z', (Scheme.Hom.isOpenEmbedding U.ι).injective ?_⟩
    rw [← hz, ← Scheme.Hom.comp_apply, hfac, Scheme.Hom.comp_apply]
  · intro φ' hφ'
    have heq : spMap (φ'.comp ι') ≫ ξ = (spMap φ' ≫ ξ₁) ≫ U.ι := by
      rw [Category.assoc, hfac, sp_sp]
    obtain ⟨⟨j0, hj0⟩, hall⟩ := hT (φ'.comp ι') (by rw [heq]; exact isTest_comp_opens_ι U Xw _ hφ')
    refine ⟨⟨j0, hj0⟩, fun j hj ψ' hψ' κ hκ => ?_⟩
    have := hall j hj (ψ'.comp (g j))
      (by rw [RingHom.comp_assoc, hg j, ← RingHom.comp_assoc, hψ', RingHom.comp_assoc]) κ (by rw [heq]; exact hκ)
    exact this

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearingIntegerShortSeriesIntegralCoprimeLevelStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat GlobalTheory.ShortBound
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clearingInteger_shortSeries_integral_coprimeLevel : ∀ (D : D7) (H : Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ → (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ = 1) → (∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) → d.l₂.M ≠ 0 → ∀ (Λ : GenLat D.host.E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g → ∀ la : HeightOneSpectrum (𝓞 c.F), (∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → ¬ ℓ ∣ d.l₂.M) → ∀ s : c.F, Submodule.span (𝓞 c.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : D.host.E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v ((s * betaH (Dw := Dw) c Λ * (intZ D Dw d.l₂ n w : c.F)) • g) := by
  first | exact @GlobalTheory.CovInt.smul_intZ_nonneg_coprime | exact GlobalTheory.CovInt.smul_intZ_nonneg_coprime | (intros; apply GlobalTheory.CovInt.smul_intZ_nonneg_coprime <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointEigenbasisChangeDetIntegralAlmostAllPrime
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM fullB tv)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

theorem GlobalTheory.DetInt.det_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S, ∀ (T : CDVR) (iK : z.K →+* T.Fr), T.FinRes →
      (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ (M : GlobalTheory.LamT.LocMod z T iK),
      letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
      ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
        (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
        φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → (∀ b, IsUnit (g b).det) →
        GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u →
        (∏ b, (g b).det) ∈ Set.range (algebraMap T.V T.Fr) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finset_valuation_div_le_one_of_isLocGen z.K z.LamL.I z.U.det
  refine ⟨S, fun p hp T iK _hfin hval M => ?_⟩
  letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
  intro φ yT y' g a hφ hmap hchg hg hint
  obtain ⟨A, hA, hloc⟩ := hz.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p
  obtain ⟨nu, mu, C, hCint, hU, hAmu, hC⟩ :=
    GlobalTheory.T.tangent_letters_integralLieBasis_eigenframe_relation E H Dw l Xo c z f La hz p T iK M hval A hA φ yT y' g a hφ hmap hchg hg hint
  let Cv : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) T.V := Matrix.of fun i k => (hCint (z.e.symm i) k).choose
  have hCv : Cv.map (algebraMap T.V T.Fr) = Matrix.of fun i k => C (z.e.symm i) k := by
    ext i k; exact (hCint (z.e.symm i) k).choose_spec
  obtain ⟨hUdet, hdet⟩ := GlobalTheory.T.det_block_change_of_basis_via_two_families_implicit Dw.mult z.e (fullB yT) (ReciprocityTheory.ChartRestriction.G.PullbackSections.fullB_basis yT) nu mu
    (z.U.map iK) (A.map iK) C g (by simpa using hU) (by simpa using hAmu) hC
  have e1 : (z.U.map iK).det = iK z.U.det := (RingHom.map_det iK z.U).symm
  have e2 : (A.map iK).det = iK A.det := (RingHom.map_det iK A).symm
  have e3 : (Cv.map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr Cv.det := (RingHom.map_det _ Cv).symm
  rw [e1] at hUdet hdet
  rw [e2] at hdet
  have hU0 : z.U.det ≠ 0 := fun h => hUdet (by rw [h, map_zero])
  obtain ⟨r, hr⟩ := (hval _).2 (hS p hp A.det hloc hU0)
  refine ⟨Cv.det * r, ?_⟩
  rw [map_mul, ← e3, hCv, hr, map_div₀, ← mul_div_assoc, div_eq_iff hUdet, hdet]
end

