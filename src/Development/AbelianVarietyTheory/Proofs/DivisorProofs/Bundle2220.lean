import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0046
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open IsLocalRing

namespace GlobalTheory.NsmulPull

variable {R : Type} [CommRing R] [IsDomain R]

theorem one_left (D : DegPre R) : (1 : D.P.A ⟶ D.P.A).left = D.P.A.hom ≫ eSec D.P.A := by
  have e : (toUnit D.P.A).left = D.P.A.hom := by simpa using Over.w (toUnit D.P.A)
  show (toUnit D.P.A ≫ η[D.P.A]).left = _
  rw [Over.comp_left, e]
  rfl

theorem unit_left (D : DegPre R) : (toUnit D.P.A ≫ η[D.P.A]).left = D.P.A.hom ≫ eSec D.P.A := one_left D

theorem comp_padd (D : DegPre R) (a x : D.P.A ⟶ D.P.A) :
    a ≫ padd D.P.A (𝟙 D.P.A) x = padd D.P.A a (a ≫ x) := by
  simp only [padd, ← Category.assoc, comp_lift, Category.comp_id]

theorem gen_shape (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k' k : ℕ) (hk : k ≤ k') (χ' χ : D.X)
    (κ : LB.Gen (kapLB D a k' k)) (hκ : κ.IsGen)
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 D.P.A) χ') (D.Oφ a χ)) (Sum.elim Oε Oinvε))) (hu : u.IsGen) :
    ∃ eB : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB χ') (fun i => a.left ≫ D.famφB χ i))
        (Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i))), eB.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
        val eB r z J = val κ r z J * rigV D (r ≫ D.P.A.hom) z J ^ ((k' : ℤ) - k) * val u r z J := by
  have hL := D.P.isLB
  let ρ := LB.pullGen D.P.L (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom
  have hρ : ρ.IsGen := pullGen_isGen _ _ _ _ D.rig_gen _
  let t := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ κ (GeneratorPullback.powGen D.P.L _ _ ρ (k' - k))) u
  have ht : t.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hκ (powGen_isGen _ _ _ _ hρ _)) hu
  have e₁ := comp_padd D a (toUnit D.P.A ≫ D.c χ)
  have e₂ : a ≫ toUnit D.P.A = toUnit D.P.A := toUnit_unique _ _
  have e₃ : a.left ≫ D.P.A.hom = D.P.A.hom := Over.w a
  obtain ⟨eB, he, hv⟩ := exists_gen hL (φ' := Sum.elim (D.famφB χ') (fun i => a.left ≫ D.famφB χ i))
    (ε' := Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i)) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three, Finset.univ_unique,
        Finset.prod_singleton, DegPre.famφB, DegPre.famε, DegPre.Oφ, Oε, Oinvε, kapLB, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Category.comp_id, ← Over.comp_left, e₁, ← Category.assoc, e₂, one_left, unit_left, Over.id_left, Nat.cast_sub hk, e₃, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, mul_one, zpow_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module) t ht
  refine ⟨eB, he, fun Z r z J hJ => ?_⟩
  rw [hv Z r z J hJ, val_mul hJ, val_mul hJ, val_pow, val_pull hJ, show ((k' : ℤ) - k) = ((k' - k : ℕ) : ℤ) by omega, zpow_natCast]
  rfl

end GlobalTheory.NsmulPull

namespace GlobalTheory.NsmulPull

end GlobalTheory.NsmulPull

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentGeometricallyIrreducible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel

noncomputable section
namespace GlobalTheory.GeomIrrComp

theorem residue_germ_injective {X : Scheme.{0}} [IsReduced X] (V : X.Opens) (x : X) (hx : x ∈ V)
    (hgen : ∀ y ∈ V, x ⤳ y) : Function.Injective (X.presheaf.germ V x hx ≫ X.residue x).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro y hy
  have hxy := hgen y (X.basicOpen_le s hy)
  have hxb : x ∈ X.basicOpen s := hxy.mem_open (X.basicOpen s).isOpen hy
  rw [Scheme.mem_basicOpen _ _ _ hx] at hxb
  exfalso
  have := hxb.map (X.residue x).hom
  rw [CommRingCat.comp_apply] at hs
  rw [hs] at this
  exact not_isUnit_zero this

theorem residue_comp_appTop {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F) (x : X) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x =
      Spec.preimage (X.fromSpecResidueField x ≫ g) := by
  apply Spec.map_injective
  rw [Spec.map_preimage]
  simp only [Spec.map_comp, Category.assoc]
  rw [← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id, Scheme.fromSpecResidueField, Category.assoc]

theorem irreducibleSpace_pullback_of_isDomain {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F)
    (V : X.Opens) (hV : IsAffineOpen V) (k : Type) [Field k] (f : F →+* k) :
    letI : Algebra F Γ(X, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    letI : Algebra F k := f.toAlgebra
    IsDomain (k ⊗[F] Γ(X, V)) → IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f)) :=
  GlobalTheory.T.irreducibleSpace_pullback_affine_open_of_isDomain_tensor g V hV k f

theorem irreducibleSpace_pullback_of_cover {F : Type} [Field F] {X : Scheme.{0}} (h : X ⟶ Sp F)
    (k : Type) [Field k] (f : F →+* k) (U : X.Opens) (hU : IsIrreducible (U : Set X))
    (hV : ∀ y ∈ U, ∃ V : X.Opens, V ≤ U ∧ y ∈ V ∧ IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f))) :
    IrreducibleSpace ↑(pullback (U.ι ≫ h) (spMap f)) :=
  GlobalTheory.T.irreducibleSpace_pullback_field_of_irreducible_cover h k f U hU hV

theorem irreducibleSpace_pullback_affine {F : Type} [Field F] [CharZero F] {X : Scheme.{0}} [IsReduced X]
    (g : X ⟶ Sp F) [LocallyOfFiniteType g] (x : X)
    (hac : letI := (Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra
      ∀ a : X.residueField x, IsAlgebraic F a → a ∈ (algebraMap F (X.residueField x)).range)
    (V : X.Opens) (hV : IsAffineOpen V) (hx : x ∈ V) (hgen : ∀ y ∈ V, x ⤳ y)
    (k : Type) [Field k] (f : F →+* k) : IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f)) := by
  let φ : CommRingCat.of F ⟶ Γ(X, V) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op
  letI : Algebra F Γ(X, V) := φ.hom.toAlgebra
  letI : Algebra F (X.residueField x) := (Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra
  letI : Algebra F k := f.toAlgebra
  have hft : Algebra.FiniteType F Γ(X, V) := by
    have h1 : (g.appLE ⊤ V le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType g inferInstance ⟨⊤, isAffineOpen_top (Sp F)⟩ ⟨V, hV⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2
    have e : φ = (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appLE ⊤ V le_top := by
      simp [φ, Scheme.Hom.appLE]
    have h3 : φ.hom.FiniteType := by rw [e]; exact h1.comp h2
    exact h3
  let j : Γ(X, V) →ₐ[F] X.residueField x :=
    { toRingHom := (X.presheaf.germ V x hx ≫ X.residue x).hom
      commutes' := fun c => by
        have e := congrArg (fun m => m.hom c) (residue_comp_appTop g x)
        have e2 : φ ≫ X.presheaf.germ V x hx ≫ X.residue x = (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
            g.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
          simp [φ]
        change (φ ≫ X.presheaf.germ V x hx ≫ X.residue x).hom c = _
        rw [e2]
        exact e }
  have hd := GlobalTheory.GeomConn.isDomain_tensor j (residue_germ_injective V x hx hgen) hac k
  exact irreducibleSpace_pullback_of_isDomain g V hV k f hd

theorem irreducibleSpace_pullback {F : Type} [Field F] [CharZero F] {X : Scheme.{0}} [IsReduced X]
    (g : X ⟶ Sp F) [LocallyOfFiniteType g] (x : X)
    (hac : letI := (Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra
      ∀ a : X.residueField x, IsAlgebraic F a → a ∈ (algebraMap F (X.residueField x)).range)
    (U : X.Opens) (hx : x ∈ U) (hgen : ∀ y ∈ U, x ⤳ y)
    (k : Type) [Field k] (f : F →+* k) : IrreducibleSpace ↑(pullback (U.ι ≫ g) (spMap f)) := by
  have hU : IsIrreducible (U : Set X) := by
    have hc : closure (U : Set X) = closure {x} := by
      apply le_antisymm
      · rw [isClosed_closure.closure_subset_iff]
        exact fun y hy => specializes_iff_mem_closure.mp (hgen y hy)
      · exact closure_mono (Set.singleton_subset_iff.mpr hx)
    rw [← isIrreducible_iff_closure, hc]
    exact isIrreducible_singleton.closure
  refine irreducibleSpace_pullback_of_cover g k f U hU fun y hy => ?_
  obtain ⟨V, hVa, hyV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hy
  refine ⟨V, hVU, hyV, irreducibleSpace_pullback_affine g x hac V hVa ((hgen y hy).mem_open V.isOpen hyV)
    (fun z hz => hgen z (hVU hz)) k f⟩

theorem algClosed_kap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hac : FnAlgClosed Xo c) (Z : Comp Xo c)
    (a : kap Z) (ha : IsAlgebraic c.F a) : a ∈ (algebraMap c.F (kap Z)).range := by
  have hb : IsAlgebraic c.F (algebraMap (kap Z) (Om Z) a) := ha.algebraMap
  obtain ⟨b, hb'⟩ := hac Z _ hb
  refine ⟨b, (algebraMap (kap Z) (Om Z)).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply]
  exact hb'

end GlobalTheory.GeomIrrComp

open GlobalTheory.GeomIrrComp in

theorem GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), FnAlgClosed Xo c → ∀ Z : Comp Xo c,
    ∃ U : (Xo.XF c).Opens, (U : Set (Xo.XF c)) = Z ∧ ∀ (k : Type) [Field k] (f : c.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (spMap f)) := by
  intro E _ _ _ H Dw l Xo c hac Z
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  haveI : Smooth (strK (Xo := Xo) (c := c)) := inferInstance
  haveI : GlobalTheory.IsNormalScheme (Xo.XF c) := GlobalTheory.isNormalScheme_of_smooth strK
  haveI : LocallyOfFiniteType (strK (Xo := Xo) (c := c)) := inferInstance
  haveI : IsLocallyNoetherian (Xo.XF c) := LocallyOfFiniteType.isLocallyNoetherian strK
  haveI : IsReduced (Xo.XF c) := GlobalTheory.IsNormalScheme.isReduced
  refine ⟨GlobalTheory.IsNormalScheme.component Z, rfl, fun k _ f => ?_⟩
  have hZc : IsClosed (Z : Set (Xo.XF c)) := isClosed_of_mem_irreducibleComponents _ Z.2
  have hg : IsGenericPoint (genPt Z) (Z : Set (Xo.XF c)) := by
    have := (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  exact irreducibleSpace_pullback strK (genPt Z) (fun a ha => algClosed_kap hac Z a ha)
    (GlobalTheory.IsNormalScheme.component Z) hg.mem (fun y hy => hg.specializes hy) k f
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRanksDegreesAddWithMassesStatement
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_ranks_degrees_add_with_masses : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : WTZ D.host.E), Splits U G → Orthogonal U V dict G → Adds U V dict G := by
  first | exact @GlobalTheory.CompAdds.adds | exact GlobalTheory.CompAdds.adds | (intros; apply GlobalTheory.CompAdds.adds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentStabilizerActsByLevelChange
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompLevelStab

theorem mem_iff_of_inv {X : Scheme.{0}} (Z : Set X) (hZ : IsClopen Z) (hI : IsIrreducible Z) (f g : X ⟶ X)
    (hfg : f ≫ g = 𝟙 X) (x : X) (hx : x ∈ Z) (hfx : f.base x ∈ Z) (y : X) : f.base y ∈ Z ↔ y ∈ Z := by
  have hgf : ∀ z, g.base (f.base z) = z := fun z => by
    have := congrArg (fun h : X ⟶ X => h.base z) hfg
    simpa using this
  have A : f.base '' Z ⊆ Z :=
    (hI.image _ f.continuous.continuousOn).isPreirreducible.isPreconnected.subset_isClopen hZ ⟨_, ⟨x, hx, rfl⟩, hfx⟩
  have B : g.base '' Z ⊆ Z :=
    (hI.image _ g.continuous.continuousOn).isPreirreducible.isPreconnected.subset_isClopen hZ
      ⟨_, ⟨f.base x, hfx, rfl⟩, by rw [hgf]; exact hx⟩
  exact ⟨fun h => hgf y ▸ B ⟨_, h, rfl⟩, fun h => A ⟨y, h, rfl⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

section Moves

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)

def mv (γ : LevelAut Dw l) : Xo.X ⟶ Xo.X := (GlobalTheory.LevelActionLaws.exists_move hpq hA Xo γ).choose

theorem mv_spec (γ : LevelAut Dw l) : ∃ ν : SABMap Xo.univ.t Xo.univ.t (mv hpq hA Xo γ),
    IsIso (mv hpq hA Xo γ) ∧ IsLevMove (mv hpq hA Xo γ) ν (liftLa γ) LinearMap.id :=
  (GlobalTheory.LevelActionLaws.exists_move hpq hA Xo γ).choose_spec

theorem x_move (c : Coeff l) (γ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    (move Xo c γ y).x = y.x ≫ mv hpq hA Xo γ := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  exact (GlobalTheory.LevelActionLaws.frMove_transfer hpq hA Xo c γ i h (GlobalTheory.LevDesc.levR_move hpq hA γ y)).1

theorem mv_over (γ : LevelAut Dw l) : mv hpq hA Xo γ ≫ Xo.s = Xo.s := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  exact h.1

theorem mv_mul (c : Coeff l) (γ δ : LevelAut Dw l) : mv hpq hA Xo (γ * δ) = mv hpq hA Xo γ ≫ mv hpq hA Xo δ := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  obtain ⟨ν', i', h'⟩ := mv_spec hpq hA Xo δ
  obtain ⟨ν₂, i₂, h₂⟩ := mv_spec hpq hA Xo (γ * δ)
  obtain ⟨μ, hμ, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).2.1 _ _ ν ν'
  have hc : IsLevMove (mv hpq hA Xo γ ≫ mv hpq hA Xo δ) μ (liftLa (γ * δ)) LinearMap.id := by
    refine ⟨?_, fun a => ?_, fun a => ?_⟩
    · rw [Category.assoc, h'.1, h.1]
    · rw [GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub γ δ a), hμ, ← Category.assoc, h.2.1,
        Category.assoc, h'.2.1, Category.assoc]
    · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a = (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
      rw [e, hμ, ← Category.assoc, h.2.2, Category.assoc, h'.2.2, Category.assoc]
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c (γ * δ) i₂ inferInstance h₂ hc).1

theorem mv_one (c : Coeff l) : mv hpq hA Xo 1 = 𝟙 Xo.X := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo 1
  obtain ⟨ι, hι, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).1
  have hc : IsLevMove (𝟙 Xo.X) ι (liftLa (1 : LevelAut Dw l)) LinearMap.id := by
    refine ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c 1 i inferInstance h hc).1

end Moves

section Base

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l) (c : Coeff l)

def mvF (γ : LevelAut Dw l) : Xo.XF c ⟶ Xo.XF c :=
  pullback.lift (pullback.fst _ _ ≫ mv hpq hA Xo γ) (pullback.snd _ _) (by
    rw [Category.assoc, mv_over, pullback.condition])

theorem mvF_fst (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ mv hpq hA Xo γ :=
  pullback.lift_fst _ _ _

theorem mvF_snd (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

theorem mvF_mul (γ δ : LevelAut Dw l) : mvF hpq hA Xo c (γ * δ) = mvF hpq hA Xo c γ ≫ mvF hpq hA Xo c δ := by
  apply pullback.hom_ext
  · rw [mvF_fst, Category.assoc, mvF_fst, ← Category.assoc, mvF_fst, Category.assoc, mv_mul hpq hA Xo c]
  · rw [mvF_snd, Category.assoc, mvF_snd, mvF_snd]

theorem mvF_one : mvF hpq hA Xo c 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mvF_fst, mv_one hpq hA Xo c, Category.comp_id, Category.id_comp]
  · rw [mvF_snd, Category.id_comp]

theorem mvF_inv_comp (γ : LevelAut Dw l) : mvF hpq hA Xo c γ⁻¹ ≫ mvF hpq hA Xo c γ = 𝟙 _ := by
  rw [← mvF_mul, inv_mul_cancel, mvF_one]

theorem mvF_comp_inv (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ mvF hpq hA Xo c γ⁻¹ = 𝟙 _ := by
  rw [← mvF_mul, mul_inv_cancel, mvF_one]

theorem ptF_move (γ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ptF (move Xo c γ y) = ptF y ≫ mvF hpq hA Xo c γ := by
  apply pullback.hom_ext
  · rw [Category.assoc, mvF_fst, ← Category.assoc]
    simp only [ptF, pullback.lift_fst]
    exact x_move hpq hA Xo c γ y
  · rw [Category.assoc, mvF_snd]
    simp only [ptF, pullback.lift_snd]

variable (Z : Comp Xo c)

def stab : Subgroup (LevelAut Dw l) where
  carrier := {h | ∀ x, (mvF hpq hA Xo c h⁻¹).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c))}
  one_mem' := fun x => by rw [inv_one, mvF_one]; rfl
  mul_mem' := by
    intro a b ha hb x
    rw [Set.mem_setOf_eq] at ha hb
    rw [mul_inv_rev, mvF_mul, Scheme.Hom.comp_apply, ha, hb]
  inv_mem' := by
    intro a ha x
    rw [Set.mem_setOf_eq] at ha
    have e : (mvF hpq hA Xo c a⁻¹).base ((mvF hpq hA Xo c a).base x) = x := by
      have := congrArg (fun f : Xo.XF c ⟶ Xo.XF c => f.base x) (mvF_comp_inv hpq hA Xo c a)
      simpa using this
    rw [inv_inv, ← ha, e]

end Base

section Restrict

variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c)

theorem mem_V₀ (x : Xo.XF c) : x ∈ Y.j ⁻¹ᵁ barComp Y Z ↔ x ∈ (Z : Set (Xo.XF c)) := j_mem_barComp Z x

theorem le_V₀ (g : LevelAut Dw l) (hg : ∀ x, (mvF hpq hA Xo c g).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c))) :
    Y.j ⁻¹ᵁ barComp Y Z ≤ mvF hpq hA Xo c g ⁻¹ᵁ (Y.j ⁻¹ᵁ barComp Y Z) := fun x hx =>
  (mem_V₀ Y Z _).2 ((hg x).2 ((mem_V₀ Y Z x).1 hx))

theorem inv_mem_stab {h : LevelAut Dw l} (hh : h ∈ stab hpq hA Xo c Z) :
    ∀ x, (mvF hpq hA Xo c h).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c)) := by
  have h2 := (stab hpq hA Xo c Z).inv_mem hh
  change ∀ x, (mvF hpq hA Xo c h⁻¹⁻¹).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c)) at h2
  simpa only [inv_inv] using h2

def resAut (h : LevelAut Dw l) (hh : h ∈ stab hpq hA Xo c Z) : Aut (V₀ Y Z) where
  hom := (mvF hpq hA Xo c h⁻¹).resLE _ _ (le_V₀ Y Z h⁻¹ hh)
  inv := (mvF hpq hA Xo c h).resLE _ _ (le_V₀ Y Z h (inv_mem_stab Z hh))
  hom_inv_id := by
    rw [← cancel_mono (Y.j ⁻¹ᵁ barComp Y Z).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, mvF_inv_comp, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (Y.j ⁻¹ᵁ barComp Y Z).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, mvF_comp_inv, Category.comp_id, Category.id_comp]

theorem resAut_ι (h : LevelAut Dw l) (hh : h ∈ stab hpq hA Xo c Z) :
    (resAut Y Z h hh).hom ≫ i₀ Y Z = i₀ Y Z ≫ mvF hpq hA Xo c h⁻¹ :=
  Scheme.Hom.resLE_comp_ι _ _

def resHom (S : Subgroup (LevelAut Dw l)) : ↥(S ⊓ stab hpq hA Xo c Z) →* Aut (V₀ Y Z) :=
  MonoidHom.mk' (fun g => resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2) fun a b => by
    apply Iso.ext
    rw [Aut.Aut_mul_def]
    change (resAut Y Z (a * b).1 (Subgroup.mem_inf.1 (a * b).2).2).hom =
      (resAut Y Z b.1 (Subgroup.mem_inf.1 b.2).2).hom ≫ (resAut Y Z a.1 (Subgroup.mem_inf.1 a.2).2).hom
    rw [← cancel_mono (i₀ Y Z), Category.assoc, resAut_ι, resAut_ι,
      ← Category.assoc, resAut_ι, Category.assoc, ← mvF_mul, Subgroup.coe_mul, mul_inv_rev]

theorem j₀_s₀ : j₀ Y Z ≫ s₀ Y Z = i₀ Y Z ≫ pullback.snd _ _ ≫ spMap (RingHom.id c.F) := by
  show j₀ Y Z ≫ (barComp Y Z).ι ≫ Y.s = _
  rw [← Category.assoc, j₀_ι, Category.assoc, Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ,
    Y.jQ_over]

end Restrict

theorem stab_acts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ S : Subgroup (LevelAut Dw l), ∃ (Γ : Subgroup (LevelAut Dw l)) (ρ : Γ →* Aut (V₀ Y Z)), Γ ≤ S ∧ ActsBy Γ.subtype ρ ∧ ∀ h ∈ S, ∀ y : FrPt Xo c ℂ, LiesOn Z y → LiesOn Z (move Xo c h⁻¹ y) → h ∈ Γ := by
  intro E _ _ _ H Dw l Xo c Y Z hpq hl S
  have hA : l.A.Coprime l.M := by rw [hl]; exact Nat.coprime_one_left _
  refine ⟨S ⊓ stab hpq hA Xo c Z, resHom (hpq := hpq) (hA := hA) Y Z S, inf_le_left, ⟨fun g => ?_, ?_⟩, ?_⟩
  · show (resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2).hom ≫ j₀ Y Z ≫ s₀ Y Z = j₀ Y Z ≫ s₀ Y Z
    rw [j₀_s₀, ← Category.assoc, resAut_ι, Category.assoc, ← Category.assoc (mvF _ _ _ _ _), mvF_snd]
  · intro g R _ _ y v hv
    show v ≫ (resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2).hom ≫ i₀ Y Z = _
    rw [resAut_ι, ← Category.assoc, hv, ← ptF_move]
    rfl
  · intro h hS y hy hy'
    refine Subgroup.mem_inf.2 ⟨hS, ?_⟩
    let pt : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    have h1 := hy' pt
    rw [ptF_move hpq hA Xo c, Scheme.Hom.comp_apply] at h1
    exact mem_iff_of_inv _ (TrivOrderTieCompare.isClopen_comp Z) Z.2.1 (mvF hpq hA Xo c h⁻¹) (mvF hpq hA Xo c h)
      (mvF_inv_comp hpq hA Xo c h) _ (hy pt) h1

end GlobalTheory.CompLevelStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthArchSectionEqSmulOfSameWeightStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constLengthArchSection_eq_smul_of_same_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → FnAlgClosed Xo c → ∀ (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (s t : ArchSec U x Z la), ∃ a : c.F, a ≠ 0 ∧ t.sig = a • s.sig := by
  first | exact @GlobalTheory.FlatCore.archSec_exists_eq_smul | exact GlobalTheory.FlatCore.archSec_exists_eq_smul | (intros; apply GlobalTheory.FlatCore.archSec_exists_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSectionStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_length_of_reading_horizontal_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig → f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) → Reads Y V τ sig f → ∀ σ, GoodEmb c σ → ∃ b : ℝ, 0 < b ∧ homN (U σ) x (wtOf Dw (flatWt Dw τ) 0) f '' framesOn (U σ) Z = {b} := by
  first | exact @GlobalTheory.BdryUnit.const_length_of_reads | exact GlobalTheory.BdryUnit.const_length_of_reads | (intros; apply GlobalTheory.BdryUnit.const_length_of_reads <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnReadingIntegerExponentSectionStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_reading_integerExponent_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (e : Ix Dw → ℤ), e none = 0 → ∀ s ∈ secZ Xo c e, ∀ σ, GoodEmb c σ → ∀ k, ContinuousOn (rdU (U σ) s k) ((U σ).X k).dom := by
  first | exact @GlobalTheory.ReadCont.continuousOn_rdU | exact GlobalTheory.ReadCont.continuousOn_rdU | (intros; apply GlobalTheory.ReadCont.continuousOn_rdU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatesIntegralOfLinearlyIndependentReductio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.MBLow.coords_integral_of_closed_indep :
  ∀ (W : Type) [CommRing W] [IsDomain W] (K₀ K₁ : Type) [Field K₀] [Field K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a, i₁ a ≠ 0 → IsUnit a) → ∀ (I Λ : Type) [Fintype Λ] (u : I → Λ → W), (∀ c : Λ → K₁, (∀ i, ∑ l, c l * i₁ (u i l) = 0) → c = 0) → ∀ (w : I → W) (z : Λ → K₀), (∀ i, i₀ (w i) = ∑ l, z l * i₀ (u i l)) → ∃ z₀ : Λ → W, (∀ l, i₀ (z₀ l) = z l) ∧ ∀ i, w i = ∑ l, z₀ l * u i l := by
  first
  | exact @_root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients
  | exact _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients
  | (apply _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients ..)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBoundsStatement
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_from_gram_and_bounds : Gram → Rec → Cut → Bad → abelian₂ → Size → CoreLe → Low → CovolX := by
  first | exact @GlobalTheory.CovTop.Assembly.covolX_of_steps | exact GlobalTheory.CovTop.Assembly.covolX_of_steps | (intros; apply GlobalTheory.CovTop.Assembly.covolX_of_steps <;> assumption)
end

