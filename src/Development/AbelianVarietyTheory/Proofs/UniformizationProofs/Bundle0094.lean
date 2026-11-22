import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalSecScale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0071
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyGtCoordOfIsGt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfPowEqOneOfLocalHom
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem eq_one_of_pow_eq_one_of_localHom {W Ω : Type} [CommRing W] [IsLocalRing W] [Field Ω] (f : W →+* Ω)
    [IsLocalHom f] {N : ℕ} (hN : IsUnit (N : W)) {ζ : W} (h : ζ ^ N = 1) (hf : f ζ = 1) : ζ = 1 := by
  have hu : IsUnit (∑ i ∈ Finset.range N, ζ ^ i) := by
    refine isUnit_of_map_unit f _ ?_
    have := hN.map f
    simpa [map_sum, hf] using this
  have := geom_sum_mul ζ N
  rw [h, sub_self] at this
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 this)

theorem unit_eq_one_of_localHom {W Ω : Type} [CommRing W] [IsLocalRing W] [Field Ω] (f : W →+* Ω)
    [IsLocalHom f] {N : ℕ} (hN : IsUnit (N : W)) {ζ : Γ(Spec (CommRingCat.of W), ⊤)ˣ} (h : ζ ^ N = 1)
    (hf : Units.map (Spec.map (CommRingCat.ofHom f)).appTop.hom.toMonoidHom ζ = 1) : ζ = 1 := by
  have nat := congrArg (fun q => q.hom ζ.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  have hf' : (Spec.map (CommRingCat.ofHom f)).appTop.hom ζ.val = 1 := congrArg Units.val hf
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, hf', map_one, CommRingCat.hom_ofHom] at nat
  have h1 := eq_one_of_pow_eq_one_of_localHom f hN
    (ζ := (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom ζ.val)
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, map_one]) nat.symm
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.injective
  rw [Units.val_one, map_one]
  exact h1

theorem IsCPMap.cubWeil_iff {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] {P : CP G} {P' : CP G'} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {N : ℕ} {T : Over S'} {x y : T ⟶ G'} (hx : x ^ N = 1) (hy : y ^ N = 1)
    (ζ : Γ(T.left, ⊤)ˣ) : CubWeil P'.c N x y ζ ↔ CubWeil P.c N (toBase hw x) (toBase hw y) ζ := by
  refine ⟨cubWeil_map _ _ _ _ _ _ _ _ _ _ h N T x y ζ, fun h' => ?_⟩
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil P'.c hx hy
  have := (cubWeil_map _ _ _ _ _ _ _ _ _ _ h N T x y ξ hξ).unique h'
  exact this ▸ hξ

theorem TQ.Desc.cubWeil_one_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
    {Q : TQ G X} {P : CP G} (D : Q.Desc P) {N : ℕ} {T : Over S} {x y : T ⟶ G} (hx : x ^ N = 1) (hy : y ^ N = 1) :
    CubWeil P.c N x y 1 ↔ CubWeil D.M.c N (x ≫ Q.q) (y ≫ Q.q) 1 := by
  rw [D.map.cubWeil_iff hx hy]
  let ρ : T ⟶ Over.mk (T.hom ≫ 𝟙 S) := Over.homMk (𝟙 T.left) (by simp)
  let ρ' : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have hw : Q.q.left ≫ Q.B.hom = G.hom ≫ 𝟙 S := by simp
  have e : ∀ a : T ⟶ G, ρ ≫ toBase hw a = a ≫ Q.q := fun a =>
    Over.OverMorphism.ext (Category.id_comp (a.left ≫ Q.q.left))
  have e' : ∀ a : T ⟶ G, ρ' ≫ (a ≫ Q.q) = toBase hw a := fun a =>
    Over.OverMorphism.ext (Category.id_comp (a.left ≫ Q.q.left))
  constructor
  · intro h
    have := h.comp ρ
    rwa [e, e, map_one] at this
  · intro h
    have := h.comp ρ'
    rwa [e', e', map_one] at this

theorem cubWeil_one_iff_closedFibre : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (W Ω : Type) [CommRing W] [IsLocalRing W] [Algebra V W] [Field Ω] (f' : W →+* Ω), IsLocalHom f' → ∀ (p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1)))) (N : ℕ), IsUnit (N : V) → ∀ (y y' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (x x' : Over.mk p ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G), y ^ N = 1 → y' ^ N = 1 → x.left ≫ (fstG _ 0 G).left = (Spec.map (CommRingCat.ofHom f')) ≫ y.left → x'.left ≫ (fstG _ 0 G).left = (Spec.map (CommRingCat.ofHom f')) ≫ y'.left → (CubWeil s.P.c N y y' 1 ↔ CubWeil (t.l 0).D.M.c N (x ≫ (t.l 0).Q.q) (x' ≫ (t.l 0).Q.q) 1) := by
  intro V _ _ _ A G _ _ s t W Ω _ _ _ _ f' hf' p N hN y y' x x' hy hy' hx hx'
  let I := IsLocalRing.maximalIdeal V
  have hw : pullback.fst G.hom (thick V I 0) ≫ G.hom = (thickObj V I 0 G).hom ≫ thick V I 0 := pullback.condition
  obtain ⟨w, hl⟩ := (t.l 0).lev
  have hρ : Spec.map (CommRingCat.ofHom f') ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) =
      (Over.mk p).hom ≫ thick V I 0 := by
    have a := Over.w (toBase hw x)
    have b := Over.w y
    exact (congrArg (Spec.map (CommRingCat.ofHom f') ≫ ·) b).symm.trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) hx).symm.trans a))
  let ρ : Over.mk ((Over.mk p).hom ≫ thick V I 0) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom f')) hρ
  have e : ρ ≫ y = toBase hw x := Over.OverMorphism.ext hx.symm
  have e' : ρ ≫ y' = toBase hw x' := Over.OverMorphism.ext hx'.symm
  have inj : ∀ a b : Over.mk p ⟶ thickObj V I 0 G, toBase hw a = toBase hw b → a = b := fun a b h =>
    Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) h) ((Over.w a).trans (Over.w b).symm))
  have tor : ∀ (a : Over.mk p ⟶ thickObj V I 0 G) (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G),
      b ^ N = 1 → ρ ≫ b = toBase hw a → a ^ N = 1 := fun a b hb h => by
    refine inj _ _ ((map_pow (toBaseHom hl.mul _) a N).trans (Eq.trans ?_ (map_one (toBaseHom hl.mul _)).symm))
    exact (congrArg (· ^ N) h.symm).trans (by rw [← MonObj.comp_pow, hb, MonObj.comp_one])
  have hxN := tor x y hy e
  have hxN' := tor x' y' hy' e'
  refine Iff.trans ?_ ((t.l 0).D.cubWeil_one_iff hxN hxN')
  refine Iff.trans ?_ (hl.cubWeil_iff hxN hxN' 1).symm
  constructor
  · intro h
    have := h.comp ρ
    rw [e, e', map_one] at this
    exact this
  · intro h
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil s.P.c hy hy'
    have c := hζ.comp ρ
    rw [e, e'] at c
    have hNW : IsUnit (N : W) := by simpa using hN.map (algebraMap V W)
    have : ζ = 1 := unit_eq_one_of_localHom f' hNW hζ.pow_eq_one (c.unique h)
    exact this ▸ hζ

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFinsetPointExtendsValuationSubalgebra
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_finset_point_extends_valuationSubalgebra (V F : Type) [CommRing V] [Field F]
    [Algebra V F] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f]
    (x : Spec (CommRingCat.of F) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V F))) :
    ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W →
      (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) →
      ∃ y : Spec (CommRingCat.of W) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V W)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap W F)) ≫ y = x := by
  first
  | exact @_root_.GlobalTheory.AffineFactorExists.exists_finset_extends
  | exact _root_.GlobalTheory.AffineFactorExists.exists_finset_extends
  | (apply _root_.GlobalTheory.AffineFactorExists.exists_finset_extends <;> assumption)
  | (intros; apply _root_.GlobalTheory.AffineFactorExists.exists_finset_extends <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AffineFactorExists.exists_finset_extends <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AffineFactorExists.exists_finset_extends ..)

theorem exists_finset_points_extend_valuationSubalgebra : ∀ (V F : Type) [CommRing V] [Field F] [Algebra V F] (B : Over (Spec (CommRingCat.of V))) [IsProper B.hom] (s : Set (Spec (CommRingCat.of F) ⟶ B.left)), s.Finite → (∀ x ∈ s, x ≫ B.hom = (Spec.map (CommRingCat.ofHom (algebraMap V F)))) → ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W → (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) → ∀ x ∈ s, ∃ y : Spec (CommRingCat.of W) ⟶ B.left, y ≫ B.hom = (Spec.map (CommRingCat.ofHom (algebraMap V W))) ∧ (Spec.map (CommRingCat.ofHom (algebraMap W F))) ≫ y = x := by
  intro V F _ _ _ B _ s hs hx
  classical
  choose t ht using fun x : s =>
    exists_finset_point_extends_valuationSubalgebra V F B.hom x.1 (hx x.1 x.2)
  haveI := hs.fintype
  refine ⟨Finset.univ.biUnion t, fun W hW h x hxs => ht ⟨x, hxs⟩ W hW fun a ha => h a ?_⟩
  exact Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, ha⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverFieldStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fourierJacobi_expansion_over_field : Laws → Laws2 → (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ t, ∃ s, U.ExpF F k t s) := by
  first | exact @GlobalTheory.UU.ExpTotal.expF_total | exact GlobalTheory.UU.ExpTotal.expF_total | (intros; apply GlobalTheory.UU.ExpTotal.expF_total <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFunctionalEquationSectionNonzeroClass
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.FESection

theorem main : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ k : ℕ, 1 ≤ k → U.FE (Kbar V) 1 → U.FE (Kbar V) k → (∃ β, U.Supp (Kbar V) 1 β) → (∃ β, U.Supp (Kbar V) k β) → ∀ α, ∃ t s, U.ExpF (Kbar V) (k + 1) t s ∧ DegPre.FamFE D (Kbar V) (k + 1) s ∧ ∃ j, (s α).f j ≠ 0 := by
  intro hL hL2 V _ _ _ hV D A G _ _ U hB k hk hF1 hFk ⟨β₁, hβ₁⟩ ⟨β₀, hβ₀⟩ α
  have hG := hL.globalFns
  obtain ⟨σ, f, sf, hσ, hpf, hfef, -, hf0⟩ := IntWit.integral_witness V hV D A G U (Kbar V) k β₀ hFk hβ₀
  obtain ⟨ϑ, g, sg, hϑ, hpg, hfeg, ⟨j₁, hs1⟩, -⟩ := IntWit.integral_witness V hV D A G U (Kbar V) 1 β₁ hF1 hβ₁
  have hg0 : ∃ j, (g (α - β₀)).f j ≠ 0 := by
    by_contra hn
    push_neg at hn
    have h1 : ∀ j, (sg (α - β₀)).f j = 0 := fun j =>
      sec_ext_val (s' := DVR.SecOps.secZero) D.P.isLB (fun y J hJ => by
        rw [hpg _ y J hJ, DVR.UUA.sval_zero_of hn _ y J (hJ.mem _ _),
          DVR.UUA.sval_zero_of (s := DVR.SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]) j
    exact hs1 (FamFree.zero_of_eq_add_nsmul hG (⟨sg, hfeg⟩ : Fam D (Kbar V) 1)
      ⟨β₁ - (α - β₀), by rw [one_smul, add_sub_cancel]⟩ h1 j₁)
  obtain ⟨W, _, _, _, φ, a, hW, hφ, hnv⟩ := GlobalTheory.UU.exists_twist_conv_ne_zero V hV D k f g α β₀
    (GlobalTheory.NullExp.main V _ D A G U _ k σ f hσ) hf0 hg0
  obtain ⟨σ', f', hσ', hff, hpf'⟩ := expT_pull V _ D A G U _ (TA V W) (toUnit _) k σ f hσ
  obtain ⟨ϑ', g', hϑ', hgg, hpg'⟩ := expT_pull V _ D A G U _ (TA V W) (toUnit _) 1 ϑ g hϑ
  have hu : φ ≫ toUnit _ = toUnit _ := toUnit_unique _ _
  obtain ⟨x, hx⟩ := TorPtEx.main V hV D A G U W hW a
  obtain ⟨σ'', hprod⟩ := GlobalTheory.UU.prodExp_opposite_translates hG V hV D A G U W hW a x hx k σ' ϑ' f' g' hσ' hϑ'
  obtain ⟨h, hh, hext⟩ := GlobalTheory.UU.ExpExt.main hL hL2 V hV D A G U W hW (k + 1) (by omega) σ''
  have hconv := GlobalTheory.ConvOfProd.main V _ D A G U _ k 1 _ _ h σ'' hprod hh
  obtain ⟨ht, hs⟩ := PullSec.pullEx V hV D A G U (Kbar V) (TA V W) φ (k + 1)
  obtain ⟨t, ht, -⟩ := ht σ''
  obtain ⟨s, hs, -⟩ := hs h
  refine ⟨t, s, hext _ φ t s ht hs, ?_, ?_⟩
  · refine GlobalTheory.ConvFE.conv_famFE hG V hV D hB W hW (Kbar V) φ hφ k 1 f' g' h sf sg s a (a ^ k)⁻¹ (fun mu => ?_)
      ((hpf' _ φ sf).2 (hu ▸ hpf)) ((hpg' _ φ sg).2 (hu ▸ hpg)) hs hfef hfeg hconv
    rw [one_smul, ofAdd_nsmul, map_pow, MonoidHom.inv_apply, MonoidHom.pow_apply, mul_inv_cancel]
  · obtain ⟨j, hj⟩ := hnv f' g' h hff hgg hconv
    by_contra hn
    push_neg at hn
    haveI := D.P.isAb.smooth
    haveI : Flat D.P.A.hom := inferInstance
    haveI : IsAffine (TA V W).left := inferInstanceAs (IsAffine (Spec _))
    haveI : IsAffine (TF (R := V) (Kbar V)).left := inferInstanceAs (IsAffine (Spec _))
    refine hj (sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A _ _ φ hφ _ D.P.L D.P.isLB _ _ _ (h α)
      (fun z J hJ => ?_) j)
    exact (hs α z J hJ).symm.trans (DVR.UUA.sval_zero_of hn _ z J (hJ.mem _ _))

end GlobalTheory.UU.FESection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtCoordOfTorusQuotient
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotCoord

open WeightGen

theorem exists_flat {X B Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (B ⟶ X)} {ε : K → ℤ}
    (f : Y ⟶ B) (u : LB.Gen ((LB.LinComb L φ ε).pull f)) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => f ≫ φ k) j →
        r z ∈ ((LB.LinComb L φ ε).pull f).U (fun _ => j) ∧
        gm r z (LB.wchart L (fun k => f ≫ φ k) j) (t.s j) =
          gm r z (((LB.LinComb L φ ε).pull f).U (fun _ => j)) (u.s fun _ => j) := by
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => f ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull f).U (fun _ => j) :=
    fun _ _ hy => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  refine ⟨⟨fun j => res (le j) (u.s fun _ => j)⟩, fun j j' => unit_ext fun y hy => ?_,
    fun Z r z j hj => ⟨le j hj, gm_res r z (le j) hj _⟩⟩
  refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 Y) y (le j) hy.1 _)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)
        ((gm_res _ y _ hy _).trans (gm_res (𝟙 Y) y (le j') hy.2 _)))).symm)
  refine (gm_gen hu (𝟙 Y) y (le j hy.1) (le j' hy.2)).trans (congrArg (· * _) ?_)
  refine (gm_pull_g _ f (𝟙 Y) y _ _ (le j hy.1) (le j' hy.2)).trans
    ((gm_linComb L φ ε (𝟙 Y ≫ f) y j j' (mem_pull.1 (le j hy.1)) (mem_pull.1 (le j' hy.2))).trans ?_)
  simp only [Category.assoc]

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

noncomputable abbrev tact (i : splitTorus S X ⟶ G) : splitTorus S X ⊗ G ⟶ G :=
  lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]

theorem comp_tact (i : splitTorus S X ⟶ G) {Z : Over S} (ρ : Z ⟶ splitTorus S X ⊗ G) :
    ρ ≫ tact i = ((ρ ≫ fst _ _) ≫ i) * (ρ ≫ snd _ _) := by
  rw [Hom.mul_def, comp_lift_assoc, Category.assoc]

theorem exists_wt_gen (i : splitTorus S X ⟶ G) {Y B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K]
    {φ : K → (B ⟶ Y)} {ε : K → ℤ} (f : G.left ⟶ B)
    (hf : (tact i).left ≫ f = (snd (splitTorus S X) G).left ≫ f) (χ : X)
    (u : LB.Gen ((LB.LinComb L φ ε).pull f)) (hu : u.IsGen) (hw : ∀ j, IsWt i _ (u.s j).val χ) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S X ⊗ G).left) (z : Z) (J), Good L z J →
        val t (r ≫ (tact i).left) z J = wt X G χ Z r z * val t (r ≫ (snd (splitTorus S X) G).left) z J := by
  obtain ⟨t, ht, hv⟩ := exists_flat f u hu
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  have m := hJ.mem (fun k => f ≫ φ k) (r ≫ (snd (splitTorus S X) G).left)
  have m' := hJ.mem (fun k => f ≫ φ k) (r ≫ (tact i).left)
  have e : ∀ k, J ((r ≫ (tact i).left) ≫ f ≫ φ k) = J ((r ≫ (snd (splitTorus S X) G).left) ≫ f ≫ φ k) :=
    fun k => by rw [Category.assoc, Category.assoc, reassoc_of% hf]
  rw [funext e] at m'
  rw [val_of _ (r ≫ (tact i).left) z J _ e]
  obtain ⟨n, v⟩ := hv Z _ z _ m
  obtain ⟨n', v'⟩ := hv Z _ z _ m'
  refine v'.trans (Eq.trans ?_ (congrArg _ v).symm)
  let Z' : Over S := Over.mk (r ≫ (splitTorus S X ⊗ G).hom)
  let ρ : Z' ⟶ splitTorus S X ⊗ G := Over.homMk r rfl
  have k := WtBundle.gm_of_isWt (hw fun _ => fun k => J ((r ≫ (snd (splitTorus S X) G).left) ≫ f ≫ φ k))
    (ρ ≫ fst _ _) (ρ ≫ snd _ _) z (by rw [← comp_tact]; exact n') n
  rw [← comp_tact, ← gm_charUnit] at k
  exact k

variable (Q : TQ G X)

theorem tact_q : tact Q.i ≫ Q.q = snd _ _ ≫ Q.q := WtBundle.act_comp Q (fst _ _) (snd _ _)

theorem exists_const (hG : GlobalFnsSt) (f : Γ(G.left, ⊤))
    (hf : (tact Q.i).left.appTop.hom f = (snd (splitTorus S X) G).left.appTop.hom f) :
    ∃ c, G.hom.appTop.hom c = f := by
  have := Q.q_affine
  obtain ⟨b, hb⟩ := (invariant_functions_descend S G Q.B _ Q.q Q.i Q.q_hom Q.i_hom Q.q_flat
    Q.q_surj inferInstance Q.isKernel ⊤).2.2 f (fun Z t g h₁ h₂ => by
      have e₁ : (t ≫ Q.i) * g = lift t g ≫ tact Q.i := by
        rw [comp_tact, lift_fst, lift_snd]
      have key : ((t ≫ Q.i) * g).left.appTop.hom f = g.left.appTop.hom f := by
        rw [e₁, Over.comp_left, FunDescent.comp_appTop_apply, hf, ← FunDescent.comp_appTop_apply,
          ← Over.comp_left, lift_snd]
      rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.app_eq_appLE] at key
      exact key)
  obtain ⟨c, hc⟩ := (hG S Q.B Q.isAb).2 b
  refine ⟨c, ?_⟩
  rw [← Over.w Q.q, FunDescent.comp_appTop_apply, hc]
  exact hb

end

theorem exists_iso_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    ∃ e : G' ≅ (Over.pullback f).obj G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst G.hom f = F := by
  let e : G' ≅ (Over.pullback f).obj G := Over.isoMk h.1.isoPullback h.1.isoPullback_hom_snd
  have he : e.hom.left ≫ pullback.fst G.hom f = F := h.1.isoPullback_hom_fst
  refine ⟨e, isMonHom_of_mul _ fun T x y => ?_, he⟩
  have h₁ := h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl
  have h₂ := (isGrpPullback_pullback G f).2 T (x ≫ e.hom) (y ≫ e.hom) (pushPt h.1.w x) (pushPt h.1.w y)
    (by rw [Over.comp_left, Category.assoc, he]; rfl) (by rw [Over.comp_left, Category.assoc, he]; rfl)
  refine Over.OverMorphism.ext ((isGrpPullback_pullback G f).1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  rw [← h₂, h₁, Over.comp_left, Category.assoc, he]

section
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem prod_transl {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 2, h (p.left ≫ ![((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A).left, 𝟙 D.P.A.left] k) ^
      (![-1, 1] : Fin 2 → ℤ) k = (h ((toUnit T ≫ D.c χ) * p).left)⁻¹ * h p.left := by
  have e : p ≫ ((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A) = (toUnit T ≫ D.c χ) * p := by
    rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]
  rw [Fin.prod_univ_two, ← e]
  show h (p ≫ ((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A)).left ^ (-1 : ℤ) * h (p.left ≫ 𝟙 _) ^ (1 : ℤ) = _
  rw [Category.comp_id, zpow_one, zpow_neg, zpow_one]

theorem exists_four {T : Over (Spec (CommRingCat.of R))} (q : T ⟶ D.P.A) (σ : T ⟶ T) (hσ : σ ≫ q = 1) (χ : D.X)
    (f : T.left ⟶ D.P.A.left) (hf : q.left = f)
    (t₀ : LB.Gen (LB.LinComb D.P.L (K := Fin 2)
      (fun k => f ≫ ![((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A).left, 𝟙 D.P.A.left] k) ![-1, 1])) (g₀ : t₀.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (D.Oφ q χ) Oinvε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val t r z J = val t₀ r z J * (val t₀ (r ≫ σ.left) z J)⁻¹ := by
  subst hf
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := D.Oφ q χ) (ε' := Oinvε) (fun U _ h => by
      have a := prod_transl D (σ ≫ q) χ h
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _
        (prod_transl D q χ h) (DVR.prod_neg _ _
          ((Finset.prod_congr rfl fun k _ =>
            congrArg (fun g => h g ^ (![-1, 1] : Fin 2 → ℤ) k) (Category.assoc _ _ _).symm).trans a))) ?_
      rw [prod_Oφ, hσ, _root_.mul_one, mul_comm q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen D.P.L _ _ _ _ t₀ (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ t₀ σ.left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ g₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ g₀ _)))
  exact ⟨t, ht, fun Z r z J hJ => by rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ]⟩

end

end GlobalTheory.QuotCoord

namespace GlobalTheory

open WeightGen QuotCoord

theorem exists_gtCoord_of_torusQuotient : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (Q : TQ (thickObj R I e G) D.X) (b : Q.B.left ⟶ D.P.A.left), IsGrpPullback Q.B D.P.A (thick R I e) b → (∀ χ, ∃ u : LB.Gen ((LB.LinComb D.P.L (K := Fin 2) ![((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A).left, 𝟙 D.P.A.left] ![-1, 1]).pull (Q.q.left ≫ b)), u.IsGen ∧ ∀ j, IsWt Q.i _ (u.s j).val χ) → ∃ g : GtCoord I D e G, g.i = Q.i ∧ g.pG.left = Q.q.left ≫ b := by
  intro hG R _ _ _ I D e G _ _ Q b hb hu
  obtain ⟨β, hβ, hβb⟩ : ∃ β : Q.B ≅ thickObj R I e D.P.A, IsMonHom β.hom ∧
    β.hom.left ≫ pullback.fst D.P.A.hom (thick R I e) = b := exists_iso_pullback hb
  have hL := D.P.isLB
  have := Q.q_hom
  have := Q.i_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  let F := Over.map (thick R I e)
  have hp : (F.map (Q.q ≫ β.hom) ≫ D.prBe I e).left = Q.q.left ≫ b := by
    rw [← hβb, ← Category.assoc]
    rfl
  have unit_q : F.map η[thickObj R I e G] ≫ F.map (Q.q ≫ β.hom) ≫ D.prBe I e = 1 := by
    rw [← F.map_comp_assoc, IsMonHom.one_hom]
    exact Over.OverMorphism.ext (unit_fst (thick R I e) D.P.A)
  have hπ : F.map (tact Q.i) ≫ F.map (toUnit _) = F.map (snd _ _) ≫ F.map (toUnit _) := by
    rw [← F.map_comp, ← F.map_comp, comp_toUnit, comp_toUnit]
  obtain ⟨t, g, m, u, w⟩ := exists_normalised D (F.map (Q.q ≫ β.hom) ≫ D.prBe I e)
    (F.map (toUnit _)) (F.map η[thickObj R I e G])
    (by rw [← F.map_comp, comp_toUnit, toUnit_unit, F.map_id]) unit_q
    (F.map (tact Q.i)) (F.map (snd _ _))
    (by rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← Category.assoc (tact Q.i), tact_q Q,
      Category.assoc])
    hπ (QuotCoord.exists_const Q hG) (fun χ => wt D.X (thickObj R I e G) χ)
    (fun χ χ' Z r z => wt_add _ _ _ _ Z r z)
    (fun χ => by
      obtain ⟨u, gu, wu⟩ := hu χ
      obtain ⟨t₀, g₀, w₀⟩ := exists_wt_gen Q.i (Q.q.left ≫ b) (by
        rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, tact_q]) χ u gu wu
      obtain ⟨t, g, v⟩ := exists_four D (F.map (Q.q ≫ β.hom) ≫ D.prBe I e)
        (F.map (toUnit _) ≫ F.map η[thickObj R I e G])
        (by rw [Category.assoc, unit_q, MonObj.comp_one]) χ _ hp t₀ g₀
      refine ⟨t, g, fun Z r z J hJ => ?_⟩
      have k : (F.map (tact Q.i)).left ≫ (F.map (toUnit _) ≫ F.map η[thickObj R I e G]).left =
          (F.map (snd _ _)).left ≫ (F.map (toUnit _) ≫ F.map η[thickObj R I e G]).left :=
        congrArg (fun g => g.left) (show F.map (tact Q.i) ≫ F.map (toUnit _) ≫ F.map η[thickObj R I e G] =
          F.map (snd _ _) ≫ F.map (toUnit _) ≫ F.map η[thickObj R I e G] by rw [reassoc_of% hπ])
      rw [v _ _ z J hJ, v _ _ z J hJ, Category.assoc, Category.assoc, k, ← _root_.mul_assoc]
      exact congrArg (· * _) (w₀ Z r z J hJ))
  refine ⟨{ q := Q.q ≫ β.hom
            q_hom := inferInstance
            q_flat := by rw [Over.comp_left]; infer_instance
            q_surj := by rw [Over.comp_left]; infer_instance
            q_affine := by rw [Over.comp_left]; infer_instance
            i := Q.i
            i_hom := inferInstance
            isKernel := Q.isKernel.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) β (by simp)
              (toUnit_unique _ _) (by simp) (by simp)
            t := t
            t_gen := g
            t_mul := m
            t_unit := fun χ => corr_of_val hL fun y J hJ => ?_
            t_weight := fun χ => corr_of_val hL fun y J hJ => ?_ }, rfl, hp⟩
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [Category.id_comp]
    exact u χ y J hJ
  · exact (val_pull hJ _ _ _).trans ((w χ _ (𝟙 _) y J hJ).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))).symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDimStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expF_of_theta_degree_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → (∃ j, th.f j ≠ 0) ∧ U.ExpF (Kbar V) 1 th s₀ ∧ ∀ t s, U.ExpF (Kbar V) 1 t s → ∃ c : (Kbar V), ∀ α j, (s α).f j = DegPre.constBF D (Kbar V) c _ * (s₀ α).f j) := by
  first | exact @GlobalTheory.UU.OneDim.expF_one_dim | exact GlobalTheory.UU.OneDim.expF_one_dim | (intros; apply GlobalTheory.UU.OneDim.expF_one_dim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtCancelNonzeroScalarStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.expandsAt_cancel_nonzero_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) [QuasiCompact G.hom] (r : R), r ≠ 0 → ∀ (σ₀ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ f : ∀ α, D.toPre.SecB k α), (∀ α, (∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j)) → (∀ j, (σ₀).f j = resTop _ (scal G.hom r) * (σ).f j) → (∀ e, U.ExpandsAt e k σ₀ f₀) → ∀ e, U.ExpandsAt e k σ f := by
  first | exact @GlobalTheory.expandsAt_cancel_scalar | exact GlobalTheory.expandsAt_cancel_scalar | (intros; apply GlobalTheory.expandsAt_cancel_scalar <;> assumption)
end

