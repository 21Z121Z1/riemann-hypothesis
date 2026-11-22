import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0015

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.MemPowOfThickZero
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem mem_pow_of_thick_zero' (G : Over (Spec (CommRingCat.of V))) [Flat G.hom] (ϖ : V) (hϖ : Irreducible ϖ)
    (U : G.left.Opens) (x : Γ(G.left, U)) (e : ℕ)
    (hx : ((fstG (maximalIdeal V) e G).left.app U).hom x = 0) :
    x ∈ Ideal.span {(G.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      ((G.hom.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ϖ))} ^ (e + 1) := by
  obtain ⟨g, hg⟩ := exists_div G.hom (pow_ne_zero (e + 1) hϖ.ne_zero) U x fun y hy => by
    obtain ⟨W, hW, hyW, le₀⟩ := exists_isAffineOpen_mem_and_subset hy
    have le : W ≤ U := le₀
    let alg : V →+* Γ(G.left, W) :=
      (G.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
    have s₀ : hW.fromSpec ≫ G.hom = spMap alg := by
      rw [← IsAffineOpen.SpecMap_appLE_fromSpec G.hom (isAffineOpen_top _) hW (fun _ _ => trivial),
        IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl
    let J : Ideal Γ(G.left, W) := Ideal.span {alg (ϖ ^ (e + 1))}
    let q : V ⧸ maximalIdeal V ^ (e + 1) →+* Γ(G.left, W) ⧸ J := Ideal.quotientMap J alg (by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span rfl)
    have sq : (spMap (Ideal.Quotient.mk J) ≫ hW.fromSpec) ≫ G.hom = spMap q ≫ thick V (maximalIdeal V) e := by
      rw [Category.assoc, s₀, ← spMap_comp]
      exact (congrArg spMap (Ideal.quotientMap_comp_mk _).symm).trans (spMap_comp _ _)
    let r : Sp (Γ(G.left, W) ⧸ J) ⟶ (thickObj V (maximalIdeal V) e G).left := pullback.lift _ _ sq
    have r₁ : r ≫ fGl (maximalIdeal V) G e = spMap (Ideal.Quotient.mk J) ≫ hW.fromSpec := pullback.lift_fst _ _ _
    have z₀ : Ideal.Quotient.mk J ((G.left.presheaf.map (homOfLE le).op).hom x) = 0 := cst_ext fun z => by
      have hm : fGl (maximalIdeal V) G e (r z) ∈ U := (congrArg (fun m => m z ∈ U) r₁).mpr
        (le (hW.range_fromSpec.le ⟨spMap (Ideal.Quotient.mk J) z, rfl⟩))
      have e₁ := (gs_fromSpec hW le (spMap (Ideal.Quotient.mk J)) z x).trans (gs_spec _ z _)
      rw [← r₁] at e₁
      rw [← e₁, cst, map_zero, gs_zero _ z ⊤ trivial]
      exact (gs_pull r _ z U hm x).symm.trans ((congrArg (gs r z _) hx).trans (gs_zero r z _ hm))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 z₀)
    refine ⟨gs (𝟙 _) y W c, (gs_res (𝟙 _) y le hyW _).symm.trans ((congrArg (gs (𝟙 _) y W) hc).trans
      ((gs_mul _ y W hyW _ _).trans (congrArg₂ (· * ·) ?_ rfl)))⟩
    exact (gs_constFn G.hom W (𝟙 _) y hyW _).trans (by rw [Category.id_comp])
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hg, constFn, map_pow, map_pow]
  exact dvd_mul_right _ _

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenPf
section
set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing TG

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem isTheta_of_nonzeroOnSpecial' (hLaws : Laws) (hL4 : Laws4) (hR : CLND R)
    [IsDiscreteValuationRing R] (hI : I = maximalIdeal R) (U : Unif I D A G) (s : H0 U.LG.L 1)
    (hs : NonzeroOnSpecial U s) : IsTheta U s := by
  have := flat_G U.toUnifPre
  have := flat_B (D := D)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hIϖ : I = Ideal.span {ϖ} := by
    rw [hI, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  obtain ⟨F, hF, -⟩ := (U.expand 1 le_rfl).1 (secK U.toUnifPre s)
  obtain ⟨r, hr0, σ, f, hσ, hfK, hexp⟩ := hF
  have hσr := sec_eq_of_secScal U.toUnifPre s σ (secK U.toUnifPre s) r (secK_rel U.toUnifPre s) hσ
  obtain ⟨n, u, hru⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
  let τ : H0 U.LG.L 1 := SecOps.secScale (scal G.hom (u : R)) s
  have hστ : ∀ j, σ.f j = toW G.hom _ (ϖ ^ n) * τ.f j := fun j => by
    rw [hσr, hru]
    show _ = _ * (toW G.hom _ (u : R) * s.f j)
    rw [map_mul, mul_comm (toW G.hom _ (u : R)), _root_.mul_assoc]
  obtain ⟨g, hfg, hexpg⟩ := expand_div_pow U.toUnifPre hL4.weightIndep hϖ.ne_zero hIϖ n σ τ hστ f hexp
  let g' : ∀ α, D.toPre.SecB 1 α := fun α => SecOps.secScale (scal D.toPre.P.A.hom ((u⁻¹ : Rˣ) : R)) (g α)
  have hexp' : ∀ e, U.ExpandsAt e 1 s g' := fun e =>
    expandsAt_scale U.toUnifPre ((u⁻¹ : Rˣ) : R) τ s (fun j => by
      show _ = _ * (toW G.hom _ (u : R) * s.f j)
      rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]) g g' (fun α j => rfl) e (hexpg e)
  have hgF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (F.s α)
      (D.toPre.famφB α) (DegPre.famε 1) (g' α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
    intro α j₁ j₂ hc
    have e := hfK α j₁ j₂ hc
    have hf' : (f α).f j₂ = toW D.toPre.P.A.hom _ r * (g' α).f j₂ := by
      rw [hfg α j₂]
      show _ = _ * (toW _ _ ((u⁻¹ : Rˣ) : R) * (g α).f j₂)
      rw [← _root_.mul_assoc, ← map_mul, hru, mul_comm (u : R), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    have hBF : (DegPre.BF D.toPre (FractionRing R)).hom =
        (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
      simp [DegPre.BF, TF]
    have hw : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom = (DegPre.BF D.toPre (FractionRing R)).hom :=
      Over.w _
    erw [hf', map_mul, app_toW, map_mul, toW_res, resTop_scal, toW_congr hw] at e
    have hu := isUnit_toW_of_K (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R))
      (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂) hr0
    rw [← toW_congr hBF] at hu
    have e2 := hu.mul_left_cancel e
    have h1 : resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂)
        (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1 := map_one _
    rw [h1, _root_.one_mul]
    exact e2
  have hv := terms_vanish hϖ hI F g' hgF
  have h0 := leading_expansion_term_ne_zero hI U s hs g' (hexp' 0) hv
  exact fun e => ⟨g', hexp' e, generates_of_ne hLaws hI (g' 0) h0⟩

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

