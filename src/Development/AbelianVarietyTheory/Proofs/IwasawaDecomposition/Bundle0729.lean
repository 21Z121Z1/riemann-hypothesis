import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0702
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0708
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0709
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0676
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0971
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0423
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0710
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0518
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0711
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageIUnionOpensEqRangeFlagCells
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem preimage_iUnion_eq_range_cells : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (F Z : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)) (j : F ⟶ Z) (ν : Z ⟶ P), IsImmersion f → (∀ b w, IsOpenImmersion (i b w)) → (∀ b w, i b w ≫ f = h b w) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → IsOpenImmersion j → j ≫ ν = f → Dense (Set.range j) → TopologicalSpace.NoetherianSpace F → IsSeparated (ν ≫ p0) → (ν ≫ p0) ⁻¹' ⋃ b, ((V b).1 : Set X) = Set.range j := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hC hP F Z f i j ν hf hi hif hcov hj hjν hd hF hsep
  have hcb : ∀ b w, i b w ≫ f ≫ p0 = cbase m (V b) := fun b w => by
    rw [← Category.assoc, hif, hP.base]
  have hjf : j ≫ ν ≫ p0 = f ≫ p0 := by rw [← Category.assoc, hjν]
  have hU : ((⨆ b, (V b).1 : X.Opens) : Set X) = ⋃ b, ((V b).1 : Set X) := by
    simp [TopologicalSpace.Opens.coe_iSup]
  rw [← hU]
  refine GlobalTheory.preimage_opens_eq_range_of_valuative F Z X j (ν ≫ p0) _ hj hd hsep hF ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨b, w, y, rfl⟩ := hcov x
    rw [hU, hjf, ← Scheme.Hom.comp_apply, hcb b w]
    refine Set.mem_iUnion.2 ⟨b, ?_⟩
    have hr := (V b).2.range_fromSpec
    unfold cbase
    rw [Scheme.Hom.comp_apply]
    exact hr ▸ Set.mem_range_self _
  · intro A k _ _ _ _ _ _ a x hx hax
    rw [hU] at hx
    haveI : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    haveI : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨y⟩ := ‹Nonempty (Sp k)›
    obtain ⟨b', w', hy⟩ := hcov (a y)
    have hra : Set.range a ⊆ Set.range (i b' w') := by
      rintro _ ⟨z, rfl⟩
      rwa [Subsingleton.elim z y]
    haveI := hi b' w'
    let a' := IsOpenImmersion.lift (i b' w') a hra
    have ha' : a' ≫ i b' w' = a := IsOpenImmersion.lift_fac _ _ _
    have h1 : a' ≫ cbase m (V b') = spMap (algebraMap A k) ≫ x := by
      rw [← hcb b' w', ← Category.assoc, ha', ← hax, hjf]
    obtain ⟨b, w, l, hl, hl2⟩ := GlobalTheory.T.flagCell_valuativeExistence_over_union_of_opens O K β X s T m M B V α c D P p0 p h hC hP A k b' w' a' x hx h1
    haveI : Mono f := inferInstance
    refine ⟨l ≫ i b w, ?_, ?_⟩
    · rw [← cancel_mono f, Category.assoc, Category.assoc, hif, hl2, ← hif b' w', ← Category.assoc, ha']
    · rw [hjf, Category.assoc, hcb b w, hl]

end GlobalTheory.FlagEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhereStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_of_abelian_everywhere : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → abLocus t.G = Set.univ → IsProper t.G.hom := by
  first | exact @GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus | exact GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus | (intros; apply GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateTwoNsmulAssociatedPowFourStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (y : D.toPre.X) (r s : R), PsiCoord D.toPre y r → PsiCoord D.toPre (2 • y) s → Associated s (r ^ 4) := by
  first | exact @GlobalTheory.PsiDoubleCoord.main | exact GlobalTheory.PsiDoubleCoord.main | (intros; apply GlobalTheory.PsiDoubleCoord.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullAddInjective
section
noncomputable section

namespace GlobalTheory.PolFan.OrbMark

variable {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

def pullAdd (f : X →+ Y) (u : LinearMap.BilinForm ℤ Y) : LinearMap.BilinForm ℤ X :=
  u.compl₁₂ f.toIntLinearMap f.toIntLinearMap

@[simp] theorem pullAdd_apply (f : X →+ Y) (u : LinearMap.BilinForm ℤ Y) (x y : X) : pullAdd f u x y = u (f x) (f y) := rfl

theorem pullAdd_injective {f : X →+ Y} (hf : Function.Surjective f) : Function.Injective (pullAdd f) :=
  fun u u' h => LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    exact LinearMap.congr_fun₂ h a b

def pullAddLin (f : X →+ Y) : LinearMap.BilinForm ℤ Y →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pullAdd f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pullAddLin_apply (f : X →+ Y) (u : LinearMap.BilinForm ℤ Y) : pullAddLin f u = pullAdd f u := rfl

example : pullAdd (zmultiplesHom ℤ 2 : ℤ →+ ℤ) mulForm 1 1 = 4 := by simp

end GlobalTheory.PolFan.OrbMark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcTorus
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolArcExtend

theorem powerSeries_props (O' : Type) [CommRing O'] [IsDomain O'] (ϖ : O') (h : IsArcBase O' ϖ) :
    ∃ (_ : IsLocalRing (PowerSeries O')), IsNoetherianRing (PowerSeries O') ∧ IsIntegrallyClosed (PowerSeries O') := by
  rcases h with ⟨hF, -⟩ | ⟨hD, -, -⟩
  · letI := hF.toField
    exact ⟨inferInstance, inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩
  · exact ⟨inferInstance, inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩

theorem spMap_jK' {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'}
    {gam : FractionRing R →+* FractionRing R'} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R' _ (g r)) :
    spMap gam ≫ Out.jK R = Out.jK R' ≫ spMap g := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext h)

theorem extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
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
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ χ : Sp (PowerSeries O') ⟶ Z.X, Out.jK (PowerSeries O') ≫ χ = x₀ ≫ Z.j := by
  intro E _ _ _ H D l Xo c p W hp hpW Z Y bV hbV f t m₁ m₂ hfs hgen huniv φ m BD hhom hpol O' _ _ _ b' ϖ a χ₀ hO hχ₀ x₀ hx₀
  obtain ⟨_, _, _⟩ := powerSeries_props O' ϖ hO
  have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  have := isProper_toroidalModel_structureMap Z
  have : CompactSpace Z.X := hpol.2.compactSpace
  have : QuasiSeparatedSpace Z.X := quasiSeparatedSpace_of_quasiSeparated Z.s
  have eF : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV := by
    rw [← spMap_comp]
    congr 1
    ext x
    exact congrArg (fun y : c.F => (y : ℂ)) (hbV x).symm
  have hZs : x₀ ≫ Z.j ≫ Z.s = Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV := by
    have hY : x₀ ≫ Y.j ≫ Y.s = Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' := by
      rw [← Category.assoc, ← hx₀, Category.assoc, hχ₀.1]
    rw [Model.j_s] at hY ⊢
    rw [eF]
    simp only [← Category.assoc] at hY ⊢
    rw [hY]
  obtain ⟨n, hn⟩ := GlobalTheory.T.pullback_model_arc_period E H D l Xo c p W hp hpW Z Y bV hbV f t m₁ m₂ hfs hgen huniv φ m BD hhom hpol O' b' ϖ a
    χ₀ hO hχ₀ x₀ hx₀
  obtain ⟨e, he, htr⟩ := GlobalTheory.T.pullback_model_arc_limit E H D l Xo c p W hp hpW Z Y bV hbV f t m₁ m₂ hfs hgen huniv φ m BD hhom hpol O' b' ϖ
    a χ₀ hO hχ₀ x₀ hx₀ n hn
  refine GlobalTheory.T.generic_section_extends_normal Z.X (polOf Z m BD) hpol.2.isLB (fun z => GlobalTheory.PolFin.exists_H0_of_isAmpleLB hpol.2 z) (PowerSeries O')
    (x₀ ≫ Z.j) e he fun V _ _ _ hV ψ gam hg => ?_
  have := hV.1
  obtain ⟨χ, hχ, -⟩ := val_exists Z.s (spMap gam ≫ x₀ ≫ Z.j)
    (spMap ψ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV) (by
      rw [Category.assoc, Category.assoc, hZs, ← Category.assoc (spMap gam), spMap_jK' hg, Category.assoc])
  exact ⟨χ, hχ.symm, htr V hV ψ gam hg χ hχ.symm⟩

end GlobalTheory.PolArcExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatioAgreeOnOverlap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLine.Overlap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_chart_gen (Z : Mdl Y i₀) (y : Z.Pt) :
    ∃ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen := by
  obtain ⟨pt⟩ : Nonempty (Sp ↥y.C.S) := inferInstance
  have e : y.gen ≫ Z.π = y.P.y ≫ (Y Z.i).j := by
    rw [Mdl.Pt.gen, Category.assoc, y.z_π, y.P.ext]
  have hpt : y.gen pt ∈ Z.opn := by
    change Z.π (y.gen pt) ∈ Set.range (Y Z.i).j
    refine ⟨y.P.y pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← e, Scheme.Hom.comp_apply]
  rw [← Z.cover] at hpt
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hpt
  obtain ⟨φ, hφ⟩ := Pull.exists_fromSpec (Z.U a).2 y.gen (fun q _ => by
    rw [Subsingleton.elim q pt]; exact ha)
  exact ⟨a, φ, hφ⟩

theorem valF_res {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem valF_pow_natCast {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (n : ℕ) : valF x U ((p : Γ(X, U)) ^ n) = (p : F) ^ n := by
  rw [valF, dif_pos h, map_pow, map_pow, map_natCast, map_natCast]

theorem exists_pow_of_rad {X : Scheme.{0}} {U : X.Opens} {C : Γ(X, U)}
    (h : (p : Γ(X, U)) ∈ (Ideal.span (Set.range ![C])).radical) : ∃ (n : ℕ) (c : Γ(X, U)), c * C = (p : Γ(X, U)) ^ n := by
  obtain ⟨n, hn⟩ := h
  rw [show Set.range ![C] = {C} by simp] at hn
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  exact ⟨n, c, hc⟩

theorem valF_ne_zero (hp : p ≠ 0) {F : Type} [Field F] [CharZero F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) {C c : Γ(X, U)} {n : ℕ} (hc : c * C = (p : Γ(X, U)) ^ n) : valF x U C ≠ 0 := by
  intro h0
  have := congrArg (valF x U) hc
  rw [Pull.valF_mul h, h0, mul_zero, valF_pow_natCast h] at this
  exact pow_ne_zero n (Nat.cast_ne_zero.2 hp) this.symm

theorem ratioAt_overlap_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) st (V V' : Z.X.Opens) (A B : Γ(Z.X, V)) (A' B' : Γ(Z.X, V')), IsAffineOpen (V ⊓ V') → RatioAt Z st V ![A] ![B] → RatioAt Z st V' ![A'] ![B'] → ∃ u : Γ(Z.X, V ⊓ V')ˣ, u.val * ((Z.X.presheaf.map (homOfLE (inf_le_right : V ⊓ V' ≤ V')).op).hom A' * (Z.X.presheaf.map (homOfLE (inf_le_left : V ⊓ V' ≤ V)).op).hom B) = (Z.X.presheaf.map (homOfLE (inf_le_right : V ⊓ V' ≤ V')).op).hom B' * (Z.X.presheaf.map (homOfLE (inf_le_left : V ⊓ V' ≤ V)).op).hom A := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z st V V' A B A' B' hI hR hR'
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨nA, cA, hA⟩ := exists_pow_of_rad hR.1
  obtain ⟨nB, cB, hB⟩ := exists_pow_of_rad hR.2.1
  obtain ⟨nA', cA', hA'⟩ := exists_pow_of_rad hR'.1
  obtain ⟨nB', cB', hB'⟩ := exists_pow_of_rad hR'.2.1
  set rl := (Z.X.presheaf.map (homOfLE (inf_le_left : V ⊓ V' ≤ V)).op).hom with hrl
  set rr := (Z.X.presheaf.map (homOfLE (inf_le_right : V ⊓ V' ≤ V')).op).hom with hrr
  have rA : rl cA * rl A = (p : Γ(Z.X, V ⊓ V')) ^ nA := by rw [← map_mul, hA, map_pow, map_natCast]
  have rB : rl cB * rl B = (p : Γ(Z.X, V ⊓ V')) ^ nB := by rw [← map_mul, hB, map_pow, map_natCast]
  have rA' : rr cA' * rr A' = (p : Γ(Z.X, V ⊓ V')) ^ nA' := by rw [← map_mul, hA', map_pow, map_natCast]
  have rB' : rr cB' * rr B' = (p : Γ(Z.X, V ⊓ V')) ^ nB' := by rw [← map_mul, hB', map_pow, map_natCast]
  obtain ⟨a, ha⟩ : ∃ a, rl A * rr B' = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, rr A' * rl B = b := ⟨_, rfl⟩
  have pa : (rl cA * rr cB') * a = (p : Γ(Z.X, V ⊓ V')) ^ (nA + nB') := by
    rw [← ha, pow_add, ← rA, ← rB']; ring
  have pb : (rr cA' * rl cB) * b = (p : Γ(Z.X, V ⊓ V')) ^ (nA' + nB) := by
    rw [← hb, pow_add, ← rA', ← rB]; ring
  have rada : (p : Γ(Z.X, V ⊓ V')) ∈ (Ideal.span {a}).radical :=
    ⟨_, Ideal.mem_span_singleton'.2 ⟨_, pa⟩⟩
  have radb : (p : Γ(Z.X, V ⊓ V')) ∈ (Ideal.span {b}).radical :=
    ⟨_, Ideal.mem_span_singleton'.2 ⟨_, pb⟩⟩
  have norms : ∀ y : Z.Pt, ⊤ ≤ y.z ⁻¹ᵁ (V ⊓ V') → ‖valF y.gen (V ⊓ V') a‖ = ‖valF y.gen (V ⊓ V') b‖ := by
    intro y hy
    obtain ⟨a₀, φ, hφ⟩ := exists_chart_gen Z y
    have hV : ⊤ ≤ y.z ⁻¹ᵁ V := fun q hq => (hy hq).1
    have hV' : ⊤ ≤ y.z ⁻¹ᵁ V' := fun q hq => (hy hq).2
    have g : ⊤ ≤ y.gen ⁻¹ᵁ (V ⊓ V') := fun q _ => hy (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
    have gV : ⊤ ≤ y.gen ⁻¹ᵁ V := fun q _ => hV (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
    have gV' : ⊤ ≤ y.gen ⁻¹ᵁ V' := fun q _ => hV' (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
    have e := (hR.2.2 y a₀ φ hφ hV).symm.trans (hR'.2.2 y a₀ φ hφ hV')
    simp only [Matrix.cons_val_fin_one, pi_norm_const, pi_norm_const'] at e
    have n1 := norm_pos_iff.2 (valF_ne_zero hp0 gV hA)
    have n2 := norm_pos_iff.2 (valF_ne_zero hp0 gV hB)
    have n3 := norm_pos_iff.2 (valF_ne_zero hp0 gV' hA')
    have n4 := norm_pos_iff.2 (valF_ne_zero hp0 gV' hB')
    rw [← ha, ← hb, Pull.valF_mul g, Pull.valF_mul g, valF_res _ g, valF_res _ g, valF_res _ g, valF_res _ g,
      norm_mul, norm_mul, ← Real.exp_log (mul_pos n1 n4), ← Real.exp_log (mul_pos n3 n2),
      Real.log_mul n1.ne' n4.ne', Real.log_mul n3.ne' n2.ne']
    congr 1
    linarith
  have hba : b ∣ a := GlobalTheory.T.divides_of_norm_bounded_points E H Dw Xo p W Y i₀ hp hW Z (V ⊓ V') hI a b radb fun y hy => (norms y hy).le
  have hab : a ∣ b := GlobalTheory.T.divides_of_norm_bounded_points E H Dw Xo p W Y i₀ hp hW Z (V ⊓ V') hI b a rada fun y hy => (norms y hy).ge
  obtain ⟨c, hc⟩ := hba
  obtain ⟨d, hd⟩ := hab
  have hdc : d * c = 1 := by
    have h0 : ((p ^ (nA + nB') : ℕ) : Γ(Z.X, V ⊓ V')) * (d * c - 1) = 0 := by
      rw [Nat.cast_pow, ← pa]
      linear_combination -(rl cA * rr cB') * hc - (rl cA * rr cB') * c * hd
    exact sub_eq_zero.1 (Z.isSMulRegular_natCast hI (pow_ne_zero _ hp0) h0)
  refine ⟨⟨c, d, by rw [mul_comm]; exact hdc, hdc⟩, ?_⟩
  change c * (rr A' * rl B) = rr B' * rl A
  rw [hb, mul_comm, ← hc, ← ha, mul_comm]

end GlobalTheory.HTLine.Overlap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalHeckeAtLevels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeFamRead

theorem rationalHecke_allSt : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ i : Fin (Dof x).R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke x.m.z.R.toRealDat i := by
  intro hL hD hT hR
  have hrat := GlobalTheory.HeckeFamRead.rat_side hT (GlobalTheory.T.heckeTransform_cuspForms_reads_cosetSum hD hR) GlobalTheory.T.exists_rationalHecke_read_as_cosetSums
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine ((hId.and (ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x _ i
  obtain ⟨hHo, -⟩ := H.1.2 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := H.2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T P.Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T P.Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T P.Wt)).finite_toSet
    exact hs.to_subtype
  exact hrat (Dof x) (GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize) i

end GlobalTheory.HeckeFamRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadWMemGoodW
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def iotaR (R : RealDat3 D A3 Ks) (i : Fin D.R.m) :
    (Fin (R.nW i) → D.what₂.LL) →ₛₗ[sg0 D A3.A] Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A)) :=
  (R.HW i (sg0 D A3.A)).e.comp ((R.FW i).j (sg0 D A3.A))

theorem iotaR_apply (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (v : Fin (R.nW i) → D.what₂.LL) :
    iotaR R i v = (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) v) := rfl

variable {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

theorem readW_mem_goodW (Y : Read (A3 := A3) R F X0) (i : Fin D.R.m) (y : D.what₂.Mj ((i : ℕ) + 1)) :
    GlobalTheory.EigRows.readW Y i y ∈ GlobalTheory.EigRows.goodW R F i := by
  obtain ⟨a, ha, e⟩ := Submodule.mem_map.1 (Y.IL.jMj i y).2
  have h' : a = GlobalTheory.EigRows.readW Y i y :=
    (PiTensorProduct.lift : Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective
      (e.trans (GlobalTheory.EigRows.lift_readW Y i y).symm)
  exact h' ▸ ha

theorem goodW_le_parts (Y : Read (A3 := A3) R F X0) (hI : Rows.IsotInternal D.what₂) (hG : GlobalTheory.EigRows.OccGood D)
    (i : Fin D.R.m) (n : ℕ) (hn : (i : ℕ) + 1 = n) :
    GlobalTheory.EigRows.goodW R F i ≤ ⨆ σ ∈ {σ | D.what₂.isot n σ ≠ ⊥ ∧ D.nd.goodRow σ},
      (D.what₂.isot ((i : ℕ) + 1) σ).map (GlobalTheory.EigRows.readW Y i) := by
  subst hn
  intro z hz
  obtain ⟨y, rfl⟩ := GlobalTheory.EigRows.exists_readW Y i hz
  have hy : y ∈ ⨆ σ, D.what₂.isot ((i : ℕ) + 1) σ := by
    rw [(hI _ (Nat.le_add_left 1 i) i.2).submodule_iSup_eq_top]; trivial
  have key : (⨆ σ, D.what₂.isot ((i : ℕ) + 1) σ) ≤ (⨆ σ ∈ {σ | D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ ∧ D.nd.goodRow σ},
      (D.what₂.isot ((i : ℕ) + 1) σ).map (GlobalTheory.EigRows.readW Y i)).comap (GlobalTheory.EigRows.readW Y i) := by
    refine iSup_le fun σ => ?_
    by_cases h0 : D.what₂.isot ((i : ℕ) + 1) σ = ⊥
    · rw [h0]; exact bot_le
    · intro u hu
      exact Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem
        (show σ ∈ {σ | D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ ∧ D.nd.goodRow σ} from ⟨h0, hG _ (Nat.le_add_left 1 i) i.2 σ h0⟩)
        (Submodule.mem_map_of_mem hu)))
  exact key hy

end Real

end GlobalTheory.EigSpanDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPointStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realCone_covered_by_star_at_point : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) → v ≠ 0 → InRCone γ v → B ∈ rcone γ → ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h ∧ 0 < h v ∧ B ∈ rcone (Fin.cons v fun j => γ (s j)) := by
  first | exact @GlobalTheory.StarCover.star_cover | exact GlobalTheory.StarCover.star_cover | (intros; apply GlobalTheory.StarCover.star_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepOfHeq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.CopyRead

theorem occ_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {y : Hd R} {Φ : Type}
    {rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r} (h : Reps y F rep) : y.occ F = {ρ | ∃ π, (rep π).Iso ρ} := by
  refine Set.ext fun ρ => ⟨h.all ρ, fun ⟨π, hi⟩ => ?_⟩
  obtain ⟨b, hb⟩ := h.mem π
  refine ⟨b, ?_⟩
  unfold principalLevelFrame.isotE at hb ⊢
  rw [← principalLevelFrame.isotL_iso _ _ _ _ _ _ (principalLevelFrame.conjT_iso hi)]
  exact hb

theorem rep_eq {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {S S' U : Set (Formalism.L2.NG.FinTyp L n)} (e : S = U) (e' : S' = U)
    {c : Formalism.L2.Col.FinTypCls S} {c' : Formalism.L2.Col.FinTypCls S'} {ρ : Formalism.L2.NG.FinTyp L n}
    (h : (Formalism.L2.Col.finTypRep S c).Iso ρ) (h' : (Formalism.L2.Col.finTypRep S' c').Iso ρ) :
    Formalism.L2.Col.finTypRep S c = Formalism.L2.Col.finTypRep S' c' := by
  subst e e'
  exact congrArg _ (Formalism.L2.Col.finTypRep_inj (Formalism.L2.NG.IsoRep.trans h (Formalism.L2.NG.IsoRep.symm (Formalism.L2.Col.finTypRep _ c').stable h')))

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀}

set_option maxHeartbeats 2000000 in

theorem rep_pin {o : q.Over} {m : Moved o} (hco : m.Coh) {s : Side0 o} (r : ReadPk m s) (hp : r.Pin) (π : q.p.Φ) :
    ∃ (S : Set (Formalism.L2.NG.FinTyp (w.st Z₀).toD7.host.E (w.st Z₀).toD7.R.r)) (c : Formalism.L2.Col.FinTypCls S),
      S = {ρ | ∃ π', (q.t.rep π').Iso ρ} ∧ (Formalism.L2.Col.finTypRep S c).Iso (q.t.rep π) ∧
        HEq (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT ((π)))) (Formalism.L2.Col.finTypRep S c) := by
  have e : ((by with_unfolding_all exact (m.t.rep :)) : type_of% q.t.rep) = q.t.rep := eq_of_heq ((by with_unfolding_all exact (hco.rep :)))
  have h1 := occ_iff m.t.reps
  have h2 := congrArg (fun P : type_of% m.y.PY => principalLevelFrame.OccRows m.z.R.θ P (m.z.R.MY 0)
    (fun b => levS _ (m.z.R.βY 0) (m.z.R.dat0 (m.z.R.toRealDat.levR m.z.F.lv2 b)))
    (fun b => levChi _ (m.z.R.βY 0) (m.z.R.dat0 (m.z.R.toRealDat.levR m.z.F.lv2 b))) (fun _ => m.z.R.toRealDat.e0)) r.PY
  have h3 := h2.trans h1
  have h4 := hp.rep ((by with_unfolding_all exact (π :)))
  rw [← e]
  have h5 : ∃ (S : Set (Formalism.L2.NG.FinTyp (w.st o.Z).toD7.host.E (w.st o.Z).toD7.R.r)) (c : Formalism.L2.Col.FinTypCls S),
      S = {ρ | ∃ π', (m.t.rep π').Iso ρ} ∧ (Formalism.L2.Col.finTypRep S c).Iso (m.t.rep π) ∧
        HEq (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT ((by with_unfolding_all exact (π :))))) (Formalism.L2.Col.finTypRep S c) := ⟨_, r.Y.eFT π, h3, h4, HEq.rfl⟩
  exact (by with_unfolding_all exact (h5 :))

set_option maxHeartbeats 2000000 in

theorem repOf_heq {o o' : q.Over} {m : Moved o} (hco : m.Coh) {s : Side0 o} (r : ReadPk m s) (hp : r.Pin)
    {m' : Moved o'} (hco' : m'.Coh) {s' : Side0 o'} (r' : ReadPk m' s') (hp' : r'.Pin) :
    HEq (GlobalTheory.HeightCounting.repOf r'.Y) (GlobalTheory.HeightCounting.repOf r.Y) := by
  have h : ∀ π : q.p.Φ, ((by with_unfolding_all exact ((GlobalTheory.HeightCounting.repOf r'.Y ((π))) : _)) : Formalism.L2.NG.FinTyp (w.st Z₀).toD7.host.E (w.st Z₀).toD7.R.r) =
      (by with_unfolding_all exact ((GlobalTheory.HeightCounting.repOf r.Y ((π))) : _)) := fun π => by
    obtain ⟨S, c, h1, h2, h3⟩ := rep_pin hco r hp π
    obtain ⟨S', c', h1', h2', h3'⟩ := rep_pin hco' r' hp' π
    exact eq_of_heq ((by with_unfolding_all exact ((h3'.trans ((heq_of_eq (rep_eq h1' h1 h2' h2)).trans h3.symm)) :)))
  exact (by with_unfolding_all exact ((heq_of_eq (funext h)) :))

end GlobalTheory.Mem.R3.Rw.CopyRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelGramMemConeIntegerSquaresStatement
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelGram_mem_cone_integer_squares : ∀ n : ℕ, ∃ S : Finset (Fin n → ℤ), ∀ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → ∃ c : (Fin n → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧ gram d u = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  first | exact @GlobalTheory.SiegelCone.gram_mem_cone | exact GlobalTheory.SiegelCone.gram_mem_cone | (intros; apply GlobalTheory.SiegelCone.gram_mem_cone <;> assumption)
end

