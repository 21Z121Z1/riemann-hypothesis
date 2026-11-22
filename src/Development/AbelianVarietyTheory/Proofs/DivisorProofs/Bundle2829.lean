import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0151
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoInclLast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermitianPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AHExists

theorem dotProduct_pullback {g n : ℕ} (J : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (H : Matrix (Fin n) (Fin n) ℂ)
    (z w : Fin g → ℂ) :
    z ⬝ᵥ ((LinearMap.toMatrix' J).transpose * H * (LinearMap.toMatrix' J).map star).mulVec (star w) =
      J z ⬝ᵥ H.mulVec (star (J w)) := by
  have e : ((LinearMap.toMatrix' J).map star).mulVec (star w) = star (J w) := by
    rw [← LinearMap.toMatrix'_mulVec J w]
    generalize LinearMap.toMatrix' J = N
    funext a
    simp [Matrix.mulVec, dotProduct, star_sum, _root_.mul_comm]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    LinearMap.toMatrix'_mulVec]

theorem isHermitian_pullback {g n : ℕ} (N : Matrix (Fin n) (Fin g) ℂ) {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) : (N.transpose * H * N.map star).IsHermitian := by
  have e : N.transpose = (N.map star).conjTranspose := by
    ext a b
    simp
  rw [e]
  exact Matrix.isHermitian_conjTranspose_mul_mul _ hH

theorem exists_isAH : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (L : LB A.left) (u : HolUnif A L g), ∃ (M : LB A.left) (u' : HolUnif A M g) (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ), M.IsLB ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsAH H χ := by
  intro A _ g hA L u
  obtain ⟨Q, v, i, r, J, R, m, -, hi, -, hm, hJ, -, -, -, hRJ⟩ :=
    GlobalTheory.HolUnifHom.exists_linear_factor A g hA (GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u) L u
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v', Hm, χ', -, hAH, -, hv1, hv2, -⟩ := thetaUnifAV_all Q rig hrig
  obtain ⟨J', hJ', hJΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v'
    hv1 hv2 i hi
  have hinj : ∀ z, J' z = 0 → z = 0 := by
    intro z hz
    have h0 : J z = 0 := LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by
      rw [← map_smul, ← v.ker, hJ, ← hJ', map_smul, hz, smul_zero, v'.ker]
      exact v'.Λ.zero_mem
    have h1 := hRJ z
    rw [h0, map_zero, ← Nat.cast_smul_eq_nsmul ℂ] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (by exact_mod_cast (show m ≠ 0 by omega))
  obtain ⟨u₁, hex, hΛ₁, hfr⟩ := GlobalTheory.exists_holUnif_linComb A Q.A L Q.L g Q.g u v' PUnit (fun _ => i)
    (fun _ => J') (fun _ => 1) (fun _ z => hJ' z)
  have hmem : ∀ l : u₁.Λ, J' (l : Fin g → ℂ) ∈ v'.Λ := fun l => hJΛ _ (hΛ₁ ▸ l.2)
  refine ⟨_, u₁, (LinearMap.toMatrix' J').transpose * Hm * (LinearMap.toMatrix' J').map star,
    fun l => χ' ⟨J' l.1, hmem l⟩, LB.isLB_linComb Q.isLB _ _, hex, hΛ₁, isHermitian_pullback _ hAH.1,
    fun z hz => ?_, fun l => hAH.2.2.1 _, ?_⟩
  · rw [dotProduct_pullback]
    exact hAH.2.1 _ fun h => hz (hinj z h)
  intro l j z hz
  rw [hex] at hz
  have hz' : ⊤ ≤ (v'.ex (J' z)).left ⁻¹ᵁ Q.L.U (j PUnit.unit) := by
    rw [hJ' z]
    exact (CubeValues.le_preimage_wchart (u.ex z).left Q.L (fun _ => i.left) j).1 hz PUnit.unit
  have e1 : u₁.fr j z = v'.fr (j PUnit.unit) (J' z) := by simpa using hfr j z
  have e2 : u₁.fr j (z + l) = v'.fr (j PUnit.unit) (J' z + J' l) := by simpa using hfr j (z + l)
  rw [e1, e2, dotProduct_pullback, dotProduct_pullback]
  exact hAH.2.2.2 ⟨J' l.1, hmem l⟩ (j PUnit.unit) (J' z) hz'

end GlobalTheory.AHExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemOfValNonnegOverCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntOverCdvr

open IsLocalRing

theorem isIntegralElem_of_val_nonneg : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v → ∀ z : F, 0 ≤ v z → ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).IsIntegralElem z := by
  intro V _ _ _ hV ϖ hϖ F _ _ _ v hv z hz
  obtain ⟨hdvr, hcomp, hchar⟩ := hV
  let K := FractionRing V
  letI : Algebra V F := ((algebraMap K F).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).mpr
    ((algebraMap K F).injective.comp (IsFractionRing.injective V K))
  haveI : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := F)).mpr inferInstance
  obtain ⟨W, hW, -, -, hfin, -, hloc, hs, -⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra V F {z}
  haveI := hfin

  have hVnn : ∀ r : V, 0 ≤ v (algebraMap V F r) := fun r =>
    GlobalTheory.FiniteDVRValuation.val_nonneg hϖ hv r

  let S : ValuationSubring F := GlobalTheory.FiniteDVRValuation.nonnegSubring v (RingHom.id F)
  have hWnn : ∀ w ∈ W, 0 ≤ v w := by
    intro w hw
    have hint : IsIntegral V w := (Algebra.IsIntegral.isIntegral (R := V) (⟨w, hw⟩ : W)).map W.val
    let φ : V →+* S := (algebraMap V F).codRestrict S (fun r => hVnn r)
    have hS : (algebraMap S F).IsIntegralElem w := RingHom.IsIntegralElem.of_comp (f := φ) hint
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := F)).1 hS
    rw [← hy]
    exact y.2

  have hϖpos : 0 < v (algebraMap V F ϖ) := by
    obtain ⟨n, hn, hu⟩ := GlobalTheory.FiniteDVRValuation.exists_nat_val hϖ hv hϖ.ne_zero
    have hn0 : n ≠ 0 := fun h => hϖ.not_isUnit (hu h)
    change 0 < v (algebraMap K F (algebraMap V K ϖ))
    rw [hn]
    exact_mod_cast Nat.pos_of_ne_zero hn0

  have hunit : ∀ c : W, v (c : F) = 0 → IsUnit c := by
    intro c hc
    by_contra hnu
    have hinj : Function.Injective (algebraMap V W) := by
      intro a b hab
      apply FaithfulSMul.algebraMap_injective V F
      have := congrArg Subtype.val hab
      simpa using this
    set ϖW : W := algebraMap V W ϖ
    have hϖW0 : ϖW ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    obtain ⟨N, hN⟩ : ∃ N : ℕ, IsDiscreteValuationRing.addVal W ϖW = N := by
      rcases h : IsDiscreteValuationRing.addVal W ϖW with _ | N
      · exact absurd (IsDiscreteValuationRing.addVal_eq_top_iff.1 h) hϖW0
      · exact ⟨N, rfl⟩
    have hc1 : 1 ≤ IsDiscreteValuationRing.addVal W c := by
      rw [ENat.one_le_iff_ne_zero]
      exact fun h => hnu (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
    have hdvd : ϖW ∣ c ^ N := by
      rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow, hN]
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • IsDiscreteValuationRing.addVal W c := nsmul_le_nsmul_right hc1 N
    obtain ⟨d, hd⟩ := hdvd
    have h1 : v ((c : F) ^ N) = 0 := by rw [AddValuation.map_pow, hc, nsmul_zero]
    have h2 : v ((c : F) ^ N) = v (algebraMap V F ϖ) + v (d : F) := by
      rw [← AddValuation.map_mul]
      congr 1
      have h := congrArg Subtype.val hd
      simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul] at h
      exact h
    have h3 : 0 < v ((c : F) ^ N) := by
      rw [h2]
      exact lt_of_lt_of_le hϖpos (le_add_of_nonneg_right (hWnn d d.2))
    rw [h1] at h3
    exact lt_irrefl _ h3

  obtain ⟨a, ha, b, hb, hb0, hab⟩ := hs z (Finset.mem_singleton_self z)
  have hzW : z ∈ W := by
    let a' : W := ⟨a, ha⟩
    let b' : W := ⟨b, hb⟩
    rcases le_total (IsDiscreteValuationRing.addVal W b') (IsDiscreteValuationRing.addVal W a') with h | h
    · obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h
      have hc' : a = b * c := congrArg Subtype.val hc
      have : z = c := by
        apply mul_left_cancel₀ hb0
        rw [mul_comm, hab, hc']
      rw [this]; exact c.2
    · obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h
      have hc' : b = a * c := congrArg Subtype.val hc
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hb0 (by simpa using hc')
      have hzc : z * c = 1 := by
        apply mul_left_cancel₀ ha0
        calc a * (z * c) = z * (a * c) := by ring
          _ = a * 1 := by rw [← hc', hab, _root_.mul_one]
      have hz0 : z ≠ 0 := left_ne_zero_of_mul_eq_one hzc
      have hvc : v (c : F) = 0 := by
        have hsum : v z + v (c : F) = 0 := by rw [← AddValuation.map_mul, hzc, AddValuation.map_one]
        have hc0 := hWnn c c.2
        refine le_antisymm ?_ hc0
        calc v (c : F) = 0 + v (c : F) := (zero_add _).symm
          _ ≤ v z + v (c : F) := by gcongr
          _ = 0 := hsum
      obtain ⟨u, hu⟩ := hunit c hvc
      have : z = ((u⁻¹ : Wˣ) : W) := by
        have h1 : ((u : W) : F) * (((u⁻¹ : Wˣ) : W) : F) = 1 := by
          rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
        rw [hu] at h1
        calc z = z * ((c : F) * (((u⁻¹ : Wˣ) : W) : F)) := by rw [h1, _root_.mul_one]
          _ = (z * c) * (((u⁻¹ : Wˣ) : W) : F) := by ring
          _ = _ := by rw [hzc, _root_.one_mul]
      rw [this]; exact Subtype.property _

  exact (Algebra.IsIntegral.isIntegral (R := V) (⟨z, hzW⟩ : W)).map W.val

end GlobalTheory.IntOverCdvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleFibreFst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MoverFibre

theorem isIrreducible_fibre_fst : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, IsIrreducible ((fst G G).left ⁻¹' {x}) := by
  intro R _ G _ hG x
  let j := G.left.fromSpecResidueField x
  let p₁ : pullback G.hom G.hom ⟶ G.left := pullback.fst G.hom G.hom
  have hp : (fst G G).left = p₁ := rfl
  have hirr0 := GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ G hG _ (j ≫ G.hom)
  haveI hirr : IrreducibleSpace (pullback G.hom (j ≫ G.hom) : Scheme.{0}) := hirr0
  let e : pullback G.hom (j ≫ G.hom) ≅ p₁.fiber x :=
    pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso G.hom G.hom j).symm ≪≫ pullbackSymmetry _ _
  have hr := (IrreducibleSpace.isIrreducible_univ (pullback G.hom (j ≫ G.hom) : Scheme.{0})).image _
      ((e.hom ≫ Scheme.Hom.fiberι p₁ x).continuous.continuousOn)
  rw [Set.image_univ] at hr
  have hrange : Set.range (e.hom ≫ Scheme.Hom.fiberι p₁ x) = Set.range (Scheme.Hom.fiberι p₁ x) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e.hom z, by rw [Scheme.Hom.comp_apply]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨e.inv z, by rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e.inv e.hom, e.inv_hom_id]; rfl⟩
  show IsIrreducible (p₁ ⁻¹' {x})
  rw [← Scheme.Hom.range_fiberι p₁ x, ← hrange]
  exact hr

end GlobalTheory.MoverFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFlagModelFlagBundleOverModuli
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.VarFlag

theorem isIso_restrict_Vo : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (h : GlobalTheory.CompHS.Y₀ X Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) (z ≫ h)) → IsIso (h ∣_ GlobalTheory.VarFlag.Vo C) := by
  intro E _ _ _ H Dw l Xo c Y X Z hF C hT B j _ f hπ hB h _ hU hH
  have := C.Y.isNormalScheme
  have hN := GlobalTheory.IsNormalScheme.pred (GlobalTheory.VarFlag.Vo C).toScheme
  have : IsLocallyNoetherian C.Y.X := LocallyOfFiniteType.isLocallyNoetherian C.Y.str
  refine GlobalTheory.isIso_of_isProper_of_existsUnique_field_point _ _ _ inferInstance inferInstance hN inferInstance
    fun K _ w => ?_
  have hp : ∀ s, (w ≫ (GlobalTheory.VarFlag.Vo C).ι) s ∈ GlobalTheory.VarFlag.Vo C := fun s => by
    rw [Scheme.Hom.comp_apply]; exact (w s).2
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.exists_flagModel_point_of_flagBundle_fieldPoint X Z hF C hT B j f hπ hB K _ hp
  have e₀ : z₀ ≫ h = w ≫ (GlobalTheory.VarFlag.Vo C).ι := (hU K z₀).unique (hH K z₀) hz₀
  have P := (isPullback_morphismRestrict h (GlobalTheory.VarFlag.Vo C)).flip
  refine ⟨P.lift z₀ w e₀, P.lift_snd _ _ _, fun y hy => ?_⟩
  apply P.hom_ext
  · rw [P.lift_fst]
    have ey : (y ≫ (h ⁻¹ᵁ GlobalTheory.VarFlag.Vo C).ι) ≫ h = w ≫ (GlobalTheory.VarFlag.Vo C).ι := by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy]
    have hr := hH K (y ≫ (h ⁻¹ᵁ GlobalTheory.VarFlag.Vo C).ι)
    rw [ey] at hr
    have := GlobalTheory.T.flagBundle_point_flags_unique_flagCover_point X C hF hT K _ _ _ hp hr hz₀
    exact (cancel_mono (GlobalTheory.CompHS.inc₀ X Z)).1 this
  · rw [P.lift_snd]; exact hy

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoInclLastStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_incl_last' : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι), IsIso (incl ι N τ (Fin.last N)) := by
  first | exact @GlobalTheory.FlagZ.Univ.isIso_incl_last | exact GlobalTheory.FlagZ.Univ.isIso_incl_last | (intros; apply GlobalTheory.FlagZ.Univ.isIso_incl_last <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

variable {S : Scheme.{0}} (G : Over S) (L : LB G.left)

abbrev LocSec (N : S.Opens) : Type := ∀ i : L.ι, Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ N)

variable {G L}

def IsLocSec {N : S.Opens} (s : LocSec G L N) : Prop :=
  ∀ i j, resG _ (fun _ hx => ⟨hx.1.1, hx.2⟩ : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
    resG _ (fun _ hx => hx.1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U i ⊓ L.U j) (L.g i j : Γ(G.left, L.U i ⊓ L.U j)) *
      resG _ (fun _ hx => ⟨hx.1.2, hx.2⟩ : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U j ⊓ G.hom ⁻¹ᵁ N) (s j)

theorem lpow_U_le [GrpObj G] {K : Type} [Field K] {ξ : Sp K ⟶ S} {N : S.Opens} (hξ : Set.range ξ ⊆ N)
    (j : Fin 1 → L.ι) :
    (LPow G L 1 (Over.mk ξ)).U j ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ (L.U (j 0) ⊓ G.hom ⁻¹ᵁ N) := by
  intro y hy
  refine ⟨Set.mem_iInter.1 hy 0, ?_⟩
  have e : (snd (Over.mk ξ) G).left ≫ G.hom = (fst (Over.mk ξ) G).left ≫ ξ :=
    (Over.w (snd (Over.mk ξ) G)).trans (Over.w (fst (Over.mk ξ) G)).symm
  show G.hom ((snd (Over.mk ξ) G).left y) ∈ N
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact hξ ⟨_, rfl⟩

def genPull [GrpObj G] {K : Type} [Field K] {ξ : Sp K ⟶ S} {N : S.Opens} (hξ : Set.range ξ ⊆ N)
    (s : LocSec G L N) (j : Fin 1 → L.ι) : Γ((Over.mk ξ ⊗ G).left, (LPow G L 1 (Over.mk ξ)).U j) :=
  ((snd (Over.mk ξ) G).left.appLE _ _ (lpow_U_le hξ j)).hom (s (j 0))

def GenIs [GrpObj G] {K : Type} [Field K] (ξ : Sp K ⟶ S) {N : S.Opens} (s : LocSec G L N)
    (v : SecM G L 1 (Over.mk ξ)) : Prop :=
  ∃ hξ : Set.range ξ ⊆ N, genPull hξ s = v.1

def FibNz {N : S.Opens} (s : LocSec G L N) (W : S.Opens) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), Set.range x ⊆ W →
    ∃ (y : Sp K ⟶ G.left) (i : L.ι), y ≫ G.hom = x ∧ Set.range y ⊆ (L.U i ⊓ G.hom ⁻¹ᵁ N : G.left.Opens) ∧
      valF y _ (s i) ≠ 0

theorem isLocSec_zero {N : S.Opens} : IsLocSec (0 : LocSec G L N) := fun i j => by
  simp [Pi.zero_apply, map_zero, mul_zero]

end GlobalTheory.UMin.ThBdl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalHomCompletedStalkToDvrOverTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TraitLocal

theorem comap_maximalIdeal_of_irreducible {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : V →+* V') (ϖ : V) (hϖ : Irreducible (h ϖ)) :
    Ideal.comap h (maximalIdeal V') = maximalIdeal V := by
  have hne : Ideal.comap h (maximalIdeal V') ≠ ⊥ := by
    intro h0
    have : ϖ ∈ Ideal.comap h (maximalIdeal V') := hϖ.not_isUnit
    rw [h0, Ideal.mem_bot] at this
    exact hϖ.ne_zero (by rw [this, map_zero])
  haveI : (Ideal.comap h (maximalIdeal V')).IsPrime := Ideal.comap_isPrime _ _
  exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne)

theorem maximalIdeal_le_map {O R : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R]
    [IsLocalRing R] (j : O →+* R) (hj : IsCpl j) : maximalIdeal R ≤ Ideal.map j (maximalIdeal O) := by
  obtain ⟨e, he⟩ := hj
  have fg : (maximalIdeal O).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal O) O) := AdicCompletion.isLocalRing_of_fg fg
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  intro r hr
  have h1 : e.symm r ∈ maximalIdeal (AdicCompletion (maximalIdeal O) O) := by
    intro hu
    have := hu.map e
    rw [RingEquiv.apply_symm_apply] at this
    exact hr this
  rw [hm] at h1
  have h2 := Ideal.mem_map_of_mem (e : AdicCompletion (maximalIdeal O) O →+* R) h1
  rw [Ideal.map_map] at h2
  have h3 : (e : AdicCompletion (maximalIdeal O) O →+* R).comp (algebraMap O _) = j := by
    first | exact he | exact RingHom.ext he | exact he.symm
  rw [h3] at h2
  simpa using h2

end GlobalTheory.Poinc.TraitLocal

theorem GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : V →+* V') (g' : R →+* V') (ξ : Sp V ⟶ M.Z), Irreducible (h ϖ) → ξ (IsLocalRing.closedPoint V) = x → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → IsLocalHom g' := by
  intro o' Ω _ _ _ hA M x R _ _ j hj V _ _ _ ϖ V' _ _ _ h g' ξ hϖ hξ hsq
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have h1 : spMap h (closedPoint V') = closedPoint V :=
    PrimeSpectrum.ext (GlobalTheory.Poinc.TraitLocal.comap_maximalIdeal_of_irreducible h ϖ hϖ)
  have h2 : (spMap h ≫ ξ) (closedPoint V') = x :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg ξ h1).trans hξ)
  rw [← hsq] at h2
  have h3 : M.Z.fromSpecStalk x (spMap j (spMap g' (closedPoint V'))) =
      M.Z.fromSpecStalk x (closedPoint (M.Z.presheaf.stalk x)) :=
    h2.trans Scheme.fromSpecStalk_closedPoint.symm
  have h4 := (M.Z.fromSpecStalk x).isEmbedding.injective h3
  have h5 : Ideal.comap j (Ideal.comap g' (maximalIdeal V')) = maximalIdeal (M.Z.presheaf.stalk x) :=
    congrArg PrimeSpectrum.asIdeal h4
  have h6 : maximalIdeal R ≤ Ideal.comap g' (maximalIdeal V') :=
    (GlobalTheory.Poinc.TraitLocal.maximalIdeal_le_map j hj).trans (Ideal.map_le_iff_le_comap.2 h5.ge)
  refine ⟨fun r hr => ?_⟩
  by_contra hn
  exact h6 (show r ∈ maximalIdeal R from hn) hr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfSmoothOverModification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isLocallyNoetherian_of_smooth_over_modif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → IsLocallyNoetherian G.left := by
  intro R _ _ _ M G hG
  haveI : IsLocallyNoetherian (Sp R) := inferInstance
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  haveI := hG
  exact LocallyOfFiniteType.isLocallyNoetherian G.hom

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfSumMapCompFixingNearOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_of_sumMap_comp_fixing_nearOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ φ : (Over.pullback p).obj G' ⟶ (Over.pullback p').obj G', Desc.sum N p hp ≫ φ = Desc.sum N p' hp' → Desc.emb N p hp ≫ φ = Desc.emb N p' hp' → IsMonHom φ := by
  first | exact @GlobalTheory.Mum.DescHom.isMonHom_of_sum_of_emb | exact GlobalTheory.Mum.DescHom.isMonHom_of_sum_of_emb | (intros; apply GlobalTheory.Mum.DescHom.isMonHom_of_sum_of_emb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomSectionOfProdTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory

theorem isMonHom_section_of_prod_trivial :
    ∀ (S : Scheme.{0}) (B B₁ B₂ : Over S) [GrpObj B] [GrpObj B₁] [GrpObj B₂] (p₁ : B ⟶ B₁) (p₂ : B ⟶ B₂) (i₁ : B₁ ⟶ B), IsMonHom p₁ → IsMonHom p₂ → IsIso (lift p₁ p₂) → i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[B₂] → IsMonHom i₁ := by
  intro S B B₁ B₂ _ _ _ p₁ p₂ i₁ h₁ h₂ hiso hi₁ hi₂
  have key : ∀ {X : Over S} (f g : X ⟶ B), f ≫ p₁ = g ≫ p₁ → f ≫ p₂ = g ≫ p₂ → f = g := by
    intro X f g e₁ e₂
    rw [← cancel_mono (lift p₁ p₂)]
    ext <;> simp [e₁, e₂]
  constructor
  · apply key
    · simp [hi₁]
    · simp only [Category.assoc, hi₂, IsMonHom.one_hom]
  · apply key
    · simp only [Category.assoc, hi₁, IsMonHom.mul_hom, Category.comp_id]
      rw [tensorHom_comp_tensorHom_assoc, hi₁, tensorHom_id, id_whiskerRight, Category.id_comp]
    · simp only [Category.assoc, hi₂, IsMonHom.mul_hom]
      rw [tensorHom_comp_tensorHom_assoc, hi₂]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomThickenedGroupEndomorphismTorusCoordinatStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_thickenedGroup_endomorphism_torusCoordinates : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), (∀ χ, D.c (h' χ) = D.c χ ≫ a') → ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → IsMonHom F := by
  first | exact @GlobalTheory.Mum.EndThick.isMonHom_of_isCoordEnd | exact GlobalTheory.Mum.EndThick.isMonHom_of_isCoordEnd | (intros; apply GlobalTheory.Mum.EndThick.isMonHom_of_isCoordEnd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricTwoCocycleOfAdditiveStructureTorsorStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSymmetricTwoCocycle_of_additiveStructure_torsor : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (f : Fn1 A) (g : Fn2 A), IsAdd f g → IsSymCoc g := by
  first | exact @GlobalTheory.PtExt.isSymCoc_of_isAdd | exact GlobalTheory.PtExt.isSymCoc_of_isAdd | (intros; apply GlobalTheory.PtExt.isSymCoc_of_isAdd <;> assumption)
end

