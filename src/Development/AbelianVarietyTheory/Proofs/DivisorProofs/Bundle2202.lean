import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0012
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0049
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivCoefNeZero
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2171
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory.Limits
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.IsogenyQuasiInverse

theorem isIntegral_left {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  exact isIntegral_of_smooth_of_geometricallyConnected A.hom

theorem nonempty_left {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] : Nonempty A.left :=
  ⟨η[A].left (IsLocalRing.closedPoint K)⟩

theorem krullDim_eq {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ)
    (hAg : SmoothOfRelativeDimension g A.hom) : Order.krullDim A.left = g := by
  have := nonempty_left A
  rw [← PosBaseChange.dim_eq_krullDim]
  exact HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth A.hom g hAg

theorem apply_genericPoint {K : Type} [Field K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g : ℕ)
    [IsIntegral A.left] [IsIntegral B.left] (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [LocallyQuasiFinite f.left] :
    f.left (genericPoint A.left) = genericPoint B.left := by
  have hdA := krullDim_eq A g hAg
  have hdB := krullDim_eq B g hBg
  have hs := FiniteEndFlat.strictMono_of_locallyQuasiFinite f.left
  have h1 : (g : WithBot ℕ∞) ≤ Order.height (genericPoint A.left) := by
    rw [← hdA, Order.krullDim_eq_iSup_height]
    exact iSup_le fun a => WithBot.coe_le_coe.mpr (Order.height_mono (genericPoint_specializes a))
  have h2 := Order.height_le_height_apply_of_strictMono _ hs (genericPoint A.left)
  have h3 : (Order.height (genericPoint B.left) : WithBot ℕ∞) ≤ g := by
    rw [← hdB]; exact Order.height_le_krullDim _
  by_contra hne
  have hle : f.left (genericPoint A.left) ≤ genericPoint B.left := genericPoint_specializes _
  have hlt : f.left (genericPoint A.left) < genericPoint B.left :=
    lt_of_le_not_ge hle fun h => hne (Specializes.antisymm (show f.left (genericPoint A.left) ⤳ genericPoint B.left from h) hle).eq
  have hfin : Order.height (f.left (genericPoint A.left)) < ⊤ := by
    exact lt_of_le_of_lt (Order.height_mono hlt.le) (lt_of_le_of_lt (WithBot.coe_le_coe.mp h3) (ENat.coe_lt_top g))
  have h4 := Order.height_strictMono hlt hfin
  have : (g : WithBot ℕ∞) < g := calc
    (g : WithBot ℕ∞) ≤ Order.height (genericPoint A.left) := h1
    _ ≤ Order.height (f.left (genericPoint A.left)) := WithBot.coe_le_coe.mpr h2
    _ < Order.height (genericPoint B.left) := WithBot.coe_lt_coe.mpr h4
    _ ≤ g := h3
  exact lt_irrefl _ this

end GlobalTheory.IsogenyQuasiInverse

namespace GlobalTheory.IsogenyQuasiInverse

theorem pullback_data {S T : Scheme.{0}} (s : T ⟶ S) (A : Over S) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hAg : SmoothOfRelativeDimension g A.hom) :
    IsAbelianScheme ((Over.pullback s).obj A) ∧
      SmoothOfRelativeDimension g ((Over.pullback s).obj A).hom :=
  ⟨isAbelianScheme_pullback_obj s A hA,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.hom s) hAg⟩

theorem flat_surjective_of_field {K : Type} [Field K] [IsAlgClosed K] (A B : Over (Sp K))
    [GrpObj A] [GrpObj B] (g : ℕ) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    (hAg : SmoothOfRelativeDimension g A.hom) (hBg : SmoothOfRelativeDimension g B.hom)
    (f : A ⟶ B) [IsMonHom f] [LocallyQuasiFinite f.left] : Flat f.left ∧ Surjective f.left := by
  have := isIntegral_left A hA
  have := isIntegral_left B hB
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  have : IsProper (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.left := IsProper.of_comp _ B.hom
  have hξ := apply_genericPoint A B g hAg hBg f
  have hd : DenseRange f.left := by
    rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro y
    exact ((genericPoint_specializes y).mem_closed isClosed_closure (subset_closure ⟨_, hξ⟩))
  have : IsDominant f.left := ⟨hd⟩
  refine ⟨SS.flat_of_isDominant_grpHom K A B f, ⟨fun y => ?_⟩⟩
  have hc : IsClosed (Set.range f.left) := f.left.isClosedMap.isClosed_range
  exact (genericPoint_specializes y).mem_closed hc ⟨_, hξ⟩

end GlobalTheory.IsogenyQuasiInverse

namespace GlobalTheory.IsogenyQuasiInverse

theorem flat_surjective_geomFibre {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (g : ℕ)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [IsMonHom f] [LocallyQuasiFinite f.left]
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S) :
    Flat ((Over.pullback t).map f).left ∧ Surjective ((Over.pullback t).map f).left := by
  obtain ⟨hA', hAg'⟩ := pullback_data t A g hA hAg
  obtain ⟨hB', hBg'⟩ := pullback_data t B g hB hBg
  have : LocallyQuasiFinite ((Over.pullback t).map f).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (AbLaw.MulN.isPullback_baseChange t f)
      inferInstance
  exact flat_surjective_of_field _ _ g hA' hB' hAg' hBg' _

theorem flat_fibre {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (g : ℕ)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [IsMonHom f] [LocallyQuasiFinite f.left]
    (k : Type) [Field k] (s : Sp k ⟶ S) : Flat ((Over.pullback s).map f).left := by
  refine flat_of_flat_fieldBaseChange k (AlgebraicClosure k) (algebraMap _ _) _ _ _ ?_
  obtain ⟨hA', hAg'⟩ := pullback_data s A g hA hAg
  obtain ⟨hB', hBg'⟩ := pullback_data s B g hB hBg
  have : LocallyQuasiFinite ((Over.pullback s).map f).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (AbLaw.MulN.isPullback_baseChange s f)
      inferInstance
  exact (flat_surjective_geomFibre _ _ g hA' hB' hAg' hBg' _ _ _).1

end GlobalTheory.IsogenyQuasiInverse

namespace GlobalTheory.IsogenyQuasiInverse

theorem exists_quasiInverse : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A B : Over (Sp R))
    [GrpObj A] [GrpObj B] (g : ℕ),
    IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
    SmoothOfRelativeDimension g B.hom → ∀ f : A ⟶ B, IsMonHom f → ∀ m : ℕ, 0 < m →
    (∀ (T : Over (Sp R)) (x : T ⟶ A), x ≫ f = 1 → x ^ m = 1) →
    ∃ h : B ⟶ A, IsMonHom h ∧ f ≫ h = 𝟙 A ^ m ∧ h ≫ f = 𝟙 B ^ m := by
  intro R _ _ A B _ _ g hA hB hAg hBg f hf m hm hker
  have := hA.smooth
  have := hB.smooth
  have := hA.proper
  have := hB.proper
  have := hA.comm
  have : LocallyOfFiniteType (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp _ B.hom
  have hSA := isSemiAbelian_of_isAbelianScheme A hA
  have : LocallyQuasiFinite f.left :=
    locallyQuasiFinite_of_finite_geometric_ker _ A B f hf inferInstance inferInstance
      fun Ω _ _ t => by
        have := HomExt.finite_torsion_points hSA t hm
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ m = 1})
          (fun x => ⟨x.1, hker _ x.1 x.2⟩) fun a b e => Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ m = 1} => z.1) e)
  have hflat : Flat f.left :=
    SemiAbMulFlat.flat_of_flatOver_fields f.left B.hom inferInstance
      (by rw [Over.w]; infer_instance) (by rw [Over.w]; infer_instance) inferInstance
      fun k _ s => FibreFlat.flatOver_of_pullback f s (flat_fibre A B g hA hB hAg hBg f k s)
  have hsurj : Surjective f.left :=
    AbLaw.MulN.surjective_of_geomFibres f fun K _ _ t =>
      (flat_surjective_geomFibre A B g hA hB hAg hBg f K t).2
  have hmA : IsMonHom (𝟙 A ^ m) := AbLaw.MulN.isMonHom_mulA A m
  obtain ⟨⟨h, hh, hfh⟩, hepi⟩ := exists_monHom_factor_of_flat_surjective _ A B A f (𝟙 A ^ m) hf hmA
    hflat hsurj inferInstance fun T x hx => by
      rw [MonObj.comp_pow, Category.comp_id, hker T x hx]
  refine ⟨h, hh, hfh, ?_⟩
  rw [← cancel_epi f, ← Category.assoc, hfh, MonObj.pow_comp, Category.id_comp, MonObj.comp_pow,
    Category.comp_id]

end GlobalTheory.IsogenyQuasiInverse
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory.OrbitSep

section Lin

variable {X : Scheme.{0}} [IsIntegral X] {Γ : Type} [Group Γ]

def fnAct (ρ : Γ →* Aut X) (γ : Γ) : X.functionFieldˣ →* X.functionFieldˣ :=
  haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  Units.map (GlobalTheory.functionFieldMap (ρ γ).hom).toMonoidHom

def RatLin (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB) : Prop :=
  ∃ (D : CartierDiv X) (c : Γ → X.functionFieldˣ), cls (toLB D) (isLB_toLB D) = cls L hL ∧
    (∀ γ δ, c (γ * δ) = fnAct ρ δ (c γ) * c δ) ∧
    (∀ γ x g, D.IsEqn ((ρ γ).hom x) g → D.IsEqn x (fnAct ρ γ g * (c γ)⁻¹)) ∧
    ∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).hom = X.fromSpecResidueField x → D.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * (c γ)⁻¹ * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1)

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Base

variable (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c)

abbrev X₀ : Scheme.{0} := (barComp Y Z).toScheme

abbrev s₀ : X₀ Y Z ⟶ Sp c.F := (barComp Y Z).ι ≫ Y.s

abbrev V₀ : Scheme.{0} := (Y.j ⁻¹ᵁ barComp Y Z).toScheme

abbrev i₀ : V₀ Y Z ⟶ Xo.XF c := (Y.j ⁻¹ᵁ barComp Y Z).ι

abbrev j₀ : V₀ Y Z ⟶ X₀ Y Z := Y.j ∣_ barComp Y Z

variable {Y} in

abbrev π₀ (X : FlagCover Y) (Z : Comp Xo c) : Y₀ X Z ⟶ X₀ Y Z := X.π ∣_ barComp Y Z

variable {Y} in

theorem π₀_s₀ (X : FlagCover Y) (Z : Comp Xo c) : π₀ X Z ≫ s₀ Y Z = str₀ X Z := by
  dsimp only [π₀, s₀, str₀, inc₀, flagStr]
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]

theorem j₀_ι : j₀ Y Z ≫ (barComp Y Z).ι = i₀ Y Z ≫ Y.j :=
  morphismRestrict_ι _ _

variable {Y Z} in

def ActsBy {Γ : Type} [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ Y Z)) : Prop :=
  (∀ γ, (ρ γ).hom ≫ j₀ Y Z ≫ s₀ Y Z = j₀ Y Z ≫ s₀ Y Z) ∧
    ∀ (γ : Γ) (R : Type) [CommRing R] [Algebra c.F R] (y : FrPt Xo c R) (v : Sp R ⟶ V₀ Y Z), v ≫ i₀ Y Z = ptF y →
      v ≫ (ρ γ).hom ≫ i₀ Y Z = ptF (move Xo c (ι γ)⁻¹ y)

end Base

variable (Dw) in

def kapBase : AllWt.Weight Dw := fun _ i => if (i : ℕ) < Dw.p then (Dw.q : ℤ) else -(Dw.p : ℤ)

def UnipAt (I : Ideal (𝓞 E)) (γ : LevelAut Dw l) : Prop :=
  ∃ m : ℕ, ∀ x : Dw.La, ((liftLa γ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La)

def NeatPrime (I : Ideal (𝓞 E)) (g r : ℕ) : Prop :=
  g.Prime ∧ Ideal.absNorm I = g ∧ (g : 𝓞 E) ∉ I ^ 2 ∧ r + 1 < g

theorem gapGe_sub_kapBase (t : ℤ) (ht : ((Dw.p + Dw.q : ℕ) : ℤ) ≤ t) : GapGe 0 (t • hodgeWt Dw - kapBase Dw) := by
  intro τ k hk
  rw [gap_eq _ (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl]
  simp only [Pi.sub_apply, Pi.smul_apply, hodgeWt, GlobalTheory.CompHt.barWt, kapBase, smul_eq_mul]
  push_cast at ht ⊢
  split_ifs <;> omega

theorem gapGe_hodgeWt : GapGe 0 (hodgeWt Dw) := by
  intro τ k hk
  rw [gap_eq _ (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl]
  simp only [hodgeWt, GlobalTheory.CompHt.barWt]
  split_ifs <;> omega

end GlobalTheory.OrbitSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCoverComponentExtendsToRankOneCuspData
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

namespace GlobalTheory.CovData

theorem hasPrinc_good (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (Y.U σ))
      (Y.d.l₂.M * (D.host.g 0 * D.host.g 1 * Y.d.pd)) := by
  have hr : 0 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hN : 3 ≤ D.host.g 0 * D.host.g 1 * Y.d.pd := by
    have h0 := (D.host.g_prime 0).two_le
    have h1 := (D.host.g_prime 1).two_le
    have hp : 1 ≤ Y.d.pd := by rw [hG.pd]; exact Nat.one_le_pow _ _ (by norm_num)
    have : 4 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul h0 h1
    nlinarith
  intro k γ hγ hc
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)) hG.lev.2 hr k γ hγ
    (fun x hx => by
      obtain ⟨y, hy, h⟩ := hc x hx
      refine ⟨((D.host.g 0 * D.host.g 1 * Y.d.pd : ℕ) : D.host.E) • y, ?_, ?_⟩
      · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy _
      · rw [h, smul_smul, ← Nat.cast_mul])
  obtain ⟨th, hrk, hth, hD⟩ := hG.dictU σ hσ
  have hmu : MuUnit (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) :=
    ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, hG.unit σ hσ⟩
  have h1 := GlobalTheory.PrincCore.root_eq_one (D.sp.W j) hrk hr (Y.U σ).X (Y.dict σ) (fun _ => (1 : ℂ)) Y.Kf th hth hD
    hmu _ hN hG.levelK k γ γ' hγ'
    (fun x hx => by
      obtain ⟨y, hy, h⟩ := hc x hx
      refine ⟨((Y.d.l₂.M : ℕ) : D.host.E) • y, ?_, ?_⟩
      · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy _
      · rw [h, smul_smul, ← Nat.cast_mul, mul_comm])
    u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

end GlobalTheory.CovData

namespace GlobalTheory.CovData

theorem exists_dataX_good : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    ∀ σ, GoodEmb Y.d.c₂ σ → ∀ k : (Y.U σ).Comp, ∃ (Xx : FD.DataX D.host.E D.R.r)
      (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), Xx.toData = (Y.U σ).X k ∧ 𝔄 ≠ 0 ∧
      Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  intro D T j Y e o hG σ hσ k
  obtain ⟨hr, hm⟩ := hG.modelW σ hσ
  have hx1 : xiR D ≤ 1 := (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_le_half D).trans (by norm_num)
  have habs := hG.xiAbs σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)) k
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((Y.U σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [(hm k).2, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
      ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
    exact h1
  have hA : D.host.AA ≠ 0 := by
    intro e0
    rw [e0] at hone
    simp at hone
  have hM : 0 < Y.d.l₂.M * (D.host.g 0 * D.host.g 1 * Y.d.pd) := by
    have h0 := (D.host.g_prime 0).pos
    have h1 := (D.host.g_prime 1).pos
    have hp : 0 < Y.d.pd := by rw [hG.pd]; positivity
    have hl : 0 < Y.d.l₂.M := by have := Y.d.l₂.three_le; omega
    positivity
  obtain ⟨Xx, h1, -, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((Y.U σ).X k) D.host.AA D.host.AAbar
    (xiR D) _
    (fun a => by
      rw [GlobalTheory.LatticeData.cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (hasPrinc_good D T j Y e o hG σ hσ k)
  exact ⟨Xx, D.host.AA, h1, hA, h3⟩

end GlobalTheory.CovData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFrMulInv
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.FlipTranslate

open GlobalTheory.ExportSeries.Model (ct)

variable {D : D7}

def gramFr (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Datum.EAf D) :=
  ct β.val * V.gram.map (eToEAf D) * β.val

def gramFrInv (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Datum.EAf D) :=
  (β⁻¹).val * (V.gram⁻¹).map (eToEAf D) * ct (β⁻¹).val

def diagW (D : D7) (n r : ℕ) (a : D.host.E) : Matrix (Fin n) (Fin n) (Datum.EAf D) :=
  Matrix.diagonal fun k => if k.val < r then 1 else eToEAf D a

def IsFlipElt (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (r : ℕ) (e : AE D) (a : D.host.E) (g : GA D V) : Prop :=
  SuppAt e V g ∧ toEAf D e • ((β⁻¹).val * (mt V g).map (toEAf D) * β.val) = toEAf D e • (diagW D V.rank r a * gramFr V β)

def conjK (PP : Pl D.host.E) : kP PP →+* kP (conjPl PP) :=
  Ideal.quotientMap (conjPl PP).asIdeal starOHom fun a ha => by
    show starO (starO a) ∈ PP.asIdeal
    rwa [starO_starO]

theorem conjK_mk (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    conjK PP (Ideal.Quotient.mk PP.asIdeal a) = Ideal.Quotient.mk (conjPl PP).asIdeal (starO a) := rfl

theorem resS_conj (PP : Pl D.host.E) (s s' : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : (s' : Datum.EAf D) = GlobalTheory.AdelicLatMove.cF D (s : Datum.EAf D)) :
    resS D.host.F (conjPl PP) s' = conjK PP (resS D.host.F PP s) := by
  have e : s' = sigS D.sp.cm s := Subtype.ext (h.trans (sigS_coe _ _).symm)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (resS D.host.F PP s)
  have h0 : resS D.host.F PP (s - oToS D.host.F D.host.E a) = 0 := by rw [map_sub, resS_oToS, ha, sub_self]
  have h1 := (resS_sigS_eq_zero_iff D.sp.cm (isConjPl_conjPl PP) _).2 h0
  rw [map_sub, map_sub, sigS_oToS, resS_oToS, sub_eq_zero] at h1
  rw [e, h1, ← ha, conjK_mk]

theorem gramFr_mul_inv (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) : gramFr V β * gramFrInv V β = 1 := by
  have h1 : ct β.val * ct (β⁻¹).val = 1 := by
    rw [← GlobalTheory.ExportSeries.Model.ct_mul, Units.inv_mul]
    simp [ct]
  unfold gramFr gramFrInv
  calc _ = ct β.val * (V.gram.map (eToEAf D) * (β.val * (β⁻¹).val) * (V.gram⁻¹).map (eToEAf D)) * ct (β⁻¹).val := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, GlobalTheory.PlaceVec.gram_map_mul_inv, Matrix.mul_one, h1]

theorem gramFr_int {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Datum.EAf D)}
    (hV : IsSelfDualC V Λ) (f : Formalism.L2.DIV.IsFrame β Λ) : IsIntM (gramFr V β) ∧ IsIntM (gramFrInv V β) :=
  GlobalTheory.ExportSeries.Model.gram_frame_int V hV f

theorem diagW_mul (n r : ℕ) (a b : D.host.E) : diagW D n r a * diagW D n r b = diagW D n r (a * b) := by
  unfold diagW
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  split_ifs
  · rw [one_mul]
  · rw [map_mul]

theorem diagW_one (n r : ℕ) : diagW D n r 1 = 1 := by
  unfold diagW
  simp only [map_one, ite_self, Matrix.diagonal_one]

theorem diagW_int (n r : ℕ) (a : 𝓞 D.host.E) : IsIntM (diagW D n r (a : D.host.E)) := by
  intro i j
  unfold diagW
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact one_mem _
  · exact Subring.subset_closure (Or.inl ⟨⟨(a : D.host.E), ⟨a, rfl⟩⟩, rfl⟩)
  · exact zero_mem _

end GlobalTheory.FlipTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityCharactersFockTensorProductStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howe_duality_characters_fock_tensor_product : ∀ (T : Type) [Fintype T] [DecidableEq T] (P Q R S : T → ℕ) (x : T → ℂ), HoweAlg (fun w => actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (tensAny fun w => coinv (P w) (Q w) (R w) (S w) (x w)) := by
  first | exact @GlobalTheory.howeAlg_fock_tensor | exact GlobalTheory.howeAlg_fock_tensor | (intros; apply GlobalTheory.howeAlg_fock_tensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_basic_properties : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ThetaBasic := by
  first | exact @GlobalTheory.ThKBasic.thetaBasic | exact GlobalTheory.ThKBasic.thetaBasic | (intros; apply GlobalTheory.ThKBasic.thetaBasic <;> assumption)
end

