import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainCuspFormRanksShiftedWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainEigenspaceShare
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialSquareZeroExtensionPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_square_zero_extension_pullback : ∀ (K : Type) [Field K] (V W₁ W₂ : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁] [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂] (p : V →ₗ[K] W₁) (q : V →ₗ[K] W₂), Function.Bijective (LinearMap.prod p q) → IsPullback (CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom) := by
  first | exact @GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt | exact GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt | (intros; apply GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsEmbedRegularRepresentationCopieStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_embed_regularRepresentation_copies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → ∀ ep c : ℝ, Ranks M ka (sOf M) ep c → ∀ H : Subgroup U, LevelHyp (sub M H) → ∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := by
  first | exact @GlobalTheory.CuspEmb.cusp_embReg | exact GlobalTheory.CuspEmb.cusp_embReg | (intros; apply GlobalTheory.CuspEmb.cusp_embReg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainCuspFormRanksShiftedWeightsStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelFlagDomain_cuspForm_ranks_shifted_weights : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), LevelHyp (sub M ⊥) → 0 < M.p0 → M.p0 < r → ∀ (ka : Wt M.Ψ r) (T : ℕ), ArchOn M ka T → sOf M ≤ T → Ranks M ka (sOf M) ((M.dimY : ℝ) * (M.dimY + 6) / T) 2 := by
  first | exact @GlobalTheory.ShareRanks.ranks | exact GlobalTheory.ShareRanks.ranks | (intros; apply GlobalTheory.ShareRanks.ranks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainEigenspaceShareStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelFlagDomain_eigenspace_share : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → ∀ ep c : ℝ, Ranks M ka (sOf M) ep c → ∀ H : Subgroup U, LevelHyp (sub M H) → ∀ lam : H →* ℂˣ, finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (sOf M))) ≤ Nat.card H * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) ∧ (1 - ep) * finrank ℂ (M.cusp ka) ≤ (Nat.card H : ℝ) * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) := by
  first | exact @GlobalTheory.ShareEig.share_eig | exact GlobalTheory.ShareEig.share_eig | (intros; apply GlobalTheory.ShareEig.share_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFibreFrameAtOriginEqRigidificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedFibre_frame_at_origin_eq_rigidification : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left) (he : eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A)
    (w : LB.Iso x.P.L (D.P.L.pull φ)), w.IsGen →
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) he D.P.L D.rig) →
    ∀ (g : ℕ) (u : HolUnif x.P.A x.P.L g), u.IsRig x.rig → ∀ (k : x.P.L.ι) (j : D.P.L.ι),
      ⊤ ≤ (u.ex 0).left ⁻¹ᵁ x.P.L.U k → ⊤ ≤ (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A) ⁻¹ᵁ D.P.L.U j →
      valAt' (u.ex 0).left _ (w.s (fun _ => j, k)).val * u.fr k 0 =
        valF (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => j)) (D.rig.s (fun _ => j)).val := by
  first | exact @GlobalTheory.RigAtOrigin.frame_at_origin | exact GlobalTheory.RigAtOrigin.frame_at_origin | (intros; apply GlobalTheory.RigAtOrigin.frame_at_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAboveDenseOpenEqGlobalMulPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.UnitAboveOpen

theorem exists_extend (T H : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T]
    (hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T) (U : T.Opens) (hU : (U : Set T).Nonempty)
    (p : H ⟶ T) (e : T ⟶ H) (hs : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _)
    (F : Γ(H, p ⁻¹ᵁ U)ˣ) (hF : ∀ y : U.toScheme, gm (U.ι ≫ e) y (p ⁻¹ᵁ U) F = 1) :
    ∃ G : Γ(H, ⊤)ˣ, F = res (le_top : p ⁻¹ᵁ U ≤ ⊤) G := by
  have : Nonempty U.toScheme := ⟨⟨hU.some, hU.some_mem⟩⟩
  have : IsIntegral H := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  have hP : IsPullback (p ⁻¹ᵁ U).ι (p ∣_ U) p U.ι := (isPullback_morphismRestrict p U).flip
  let eU : U.toScheme ⟶ (p ⁻¹ᵁ U).toScheme := hP.lift (U.ι ≫ e) (𝟙 _) (by simp [he])
  have heU : eU ≫ (p ⁻¹ᵁ U).ι = U.ι ≫ e := hP.lift_fst _ _ _
  have : Nonempty (p ⁻¹ᵁ U).toScheme := ⟨eU (Nonempty.some inferInstance)⟩
  let L : LB H := ⟨PUnit, fun _ ↦ ⊤, fun _ _ ↦ 1⟩
  have hL : L.IsLB := ⟨by simp [L], fun _ ↦ map_one _, fun _ _ _ ↦ by simp [L]⟩
  let φ : PEmpty → (H ⟶ H) := PEmpty.elim
  let ε : PEmpty → ℤ := PEmpty.elim
  have hw {Y : Scheme.{0}} (ψ : PEmpty → (Y ⟶ H)) (a) (y : Y) : y ∈ LB.wchart L ψ a :=
    Set.mem_iInter.2 fun k ↦ k.elim
  have hm (y : (p ⁻¹ᵁ U).toScheme) : (p ⁻¹ᵁ U).ι y ∈ p ⁻¹ᵁ U := y.2
  let t : LB.Gen (LB.LinComb L (fun i ↦ (p ⁻¹ᵁ U).ι ≫ φ i) ε) :=
    ⟨fun a ↦ res (fun y _ ↦ hm y) (pullU (p ⁻¹ᵁ U).ι _ F)⟩
  have htg {Z : Scheme.{0}} (r : Z ⟶ (p ⁻¹ᵁ U).toScheme) (z : Z) (a) :
      gm r z (LB.wchart L (fun i ↦ (p ⁻¹ᵁ U).ι ≫ φ i) a) (t.s a) =
        gm (r ≫ (p ⁻¹ᵁ U).ι) z (p ⁻¹ᵁ U) F :=
    (gm_res r z _ (hw _ _ _) _).trans (gm_pull r _ z _ (hm _) F)
  let ρ : LB.Gen (LB.LinComb L (fun i ↦ e ≫ φ i) ε) := ⟨fun a ↦ 1⟩
  have ht : t.IsGen := fun a b ↦ by
    obtain rfl : a = b := funext fun k ↦ PEmpty.elim k
    simp [LB.LinComb]
  have hρ : ρ.IsGen := fun a b ↦ by
    obtain rfl : a = b := funext fun k ↦ PEmpty.elim k
    simp [LB.LinComb]
  have hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ U.ι) := by
    intro a b _ _ _
    refine unit_ext fun y hy ↦ ?_
    rw [gm_res _ y _ hy, gm_res _ y _ hy]
    refine Eq.trans (b := 1) ((gm_res _ y _ (hw _ _ _) _).trans
      ((gm_pull _ _ y _ (hw _ _ _) _).trans ((htg _ _ _).trans ?_))) ?_
    · rw [Category.id_comp, heU, hF]
    · refine Eq.symm ((gm_res _ y _ (hw _ _ _) _).trans ((gm_pull _ _ y _ (hw _ _ _) _).trans ?_))
      exact map_one _
  obtain ⟨c, ⟨-, hc'⟩, -⟩ := GlobalTheory.GenExtendNormal.existsUnique_gen_extend T hT U.toScheme H
    (p ⁻¹ᵁ U).toScheme H U.ι p e (p ⁻¹ᵁ U).ι (p ∣_ U) eU hs hg he hP heU L hL PEmpty φ ε t ρ
    ht hρ hc
  let a : PEmpty → L.ι := PEmpty.elim
  refine ⟨res (fun y _ ↦ hw φ a y : (⊤ : H.Opens) ≤ LB.wchart L φ a) (c.s a),
    GlobalTheory.GenExtendNormal.unit_ext_of_isOpenImmersion (p ⁻¹ᵁ U).ι fun y hy ↦ ?_⟩
  rw [gm_res _ y _ hy, gm_res (p ⁻¹ᵁ U).ι y (V := ⊤) _ trivial]
  have h₁ := htg (𝟙 _) y a
  rw [← hc', Category.id_comp] at h₁
  rw [← h₁]
  exact (gm_res _ y _ (hw _ _ _) _).trans ((gm_pull _ _ y _ (hw _ _ _) _).trans
    (by rw [Category.id_comp]))

theorem exists_eq_res_mul_pullU :
    ∀ (T H : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : H ⟶ T) (e : T ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ F : Γ(H, p ⁻¹ᵁ U)ˣ, ∃ (G : Γ(H, ⊤)ˣ) (w : Γ(T, U)ˣ), F = res (le_top : p ⁻¹ᵁ U ≤ ⊤) G * pullU p U w := by
  intro T H _ _ hT U hU p e hs hg he F
  have hle : U ≤ e ⁻¹ᵁ p ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, he]; rfl
  let w : Γ(T, U)ˣ := res hle (pullU e _ F)
  obtain ⟨G, hG⟩ := exists_extend T H hT U hU p e hs hg he (F * (pullU p U w)⁻¹) fun y ↦ by
    have hy : U.ι y ∈ U := y.2
    have hy' : p ((U.ι ≫ e) y) ∈ U := hle hy
    rw [map_mul, map_inv, gm_pull _ p y U hy', Category.assoc, he, Category.comp_id,
      gm_res _ y hle hy, gm_pull _ e y _ (hle hy), mul_inv_cancel]
  exact ⟨G, w, by rw [← hG, inv_mul_cancel_right]⟩

end GlobalTheory.UnitAboveOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAtInvertiblePStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_chart_at_invertible_p : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (x : X),
    x ∈ X.basicOpen (p : Γ(X, ⊤)) → UnitChartAt p Xw K x := by
  first | exact @GlobalTheory.FlatModel.unitChartAt_of_mem_basicOpen_p | exact GlobalTheory.FlatModel.unitChartAt_of_mem_basicOpen_p | (intros; apply GlobalTheory.FlatModel.unitChartAt_of_mem_basicOpen_p <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitOfTestPointEstimate
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

theorem norm_coe_of_isUnit_padicComplexInt (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) (hx : IsUnit x) :
    ‖(x : ℂ_[p])‖ = 1 := by
  have h1 := (PadicComplexInt.integers p).isUnit_iff_valuation_eq_one.1 hx
  rw [← coe_valued]
  change ((Valued.v ((algebraMap 𝓞_ℂ_[p] ℂ_[p]) x) : ℝ≥0) : ℝ) = 1
  rw [h1]; rfl

theorem sub_one_mem_radical_of_isTest : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → Flat s → LocallyOfFiniteType s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (A : Type) [CommRing A] (w : Sp A ⟶ X), IsOpenImmersion w → ∀ u : A, (∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ‖(φ u : ℂ_[p]) - 1‖ < 1) → u - 1 ∈ (Ideal.span {(p : A)}).radical := by
  intro F _ _ V p _ hp hD X s Xw hX hflat hlft hXw hne A _ w hw u hu
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro 𝔮 ⟨hle, h𝔮⟩
  by_contra hf
  let f : A := u - 1
  let B := Localization.Away f
  haveI : IsOpenImmersion (spMap (algebraMap A B)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))
  let ξ : Sp B ⟶ X := spMap (algebraMap A B) ≫ w
  have hpq : (p : A) ∈ 𝔮 := hle (Ideal.subset_span rfl)
  have hdisj : Disjoint (Submonoid.powers f : Set A) (𝔮 : Set A) :=
    (Ideal.disjoint_powers_iff_notMem _ h𝔮.isRadical).2 hf
  let Q : Ideal B := Ideal.map (algebraMap A B) 𝔮
  haveI hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) B 𝔮 h𝔮 hdisj
  have hpQ : (p : B) ∈ Q := by
    rw [← map_natCast (algebraMap A B)]; exact Ideal.mem_map_of_mem _ hpq
  let y : Sp B := (⟨Q, hQ⟩ : PrimeSpectrum B)
  have hx : ξ y ∉ X.basicOpen (p : Γ(X, ⊤)) := by
    have h1 : y ∉ ξ ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) := by
      rw [Scheme.preimage_basicOpen_top, map_natCast]
      have h2 : ((p : Γ(Sp B, ⊤))) = (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (p : B) := (map_natCast _ _).symm
      rw [h2, basicOpen_eq_of_affine]
      intro h3
      exact ((PrimeSpectrum.mem_basicOpen _ _).1 h3) hpQ
    exact h1
  obtain ⟨φ, hφ⟩ := hD F V p hp X s Xw hX hflat hlft hXw hne B ξ inferInstance ⟨ξ y, ⟨y, rfl⟩, hx⟩
  have hφ' : IsTest p Xw (spMap (φ.comp (algebraMap A B)) ≫ w) := by
    rw [← sp_sp]; exact hφ
  have h1 := hu _ hφ'
  have hunit : IsUnit ((φ.comp (algebraMap A B)) f) :=
    (IsLocalization.Away.algebraMap_isUnit (S := B) f).map φ
  have h2 : ((φ.comp (algebraMap A B) u : 𝓞_ℂ_[p]) : ℂ_[p]) - 1 = (((φ.comp (algebraMap A B)) f : 𝓞_ℂ_[p]) : ℂ_[p]) := by
    simp [f, map_sub]
  rw [h2, norm_coe_of_isUnit_padicComplexInt p _ hunit] at h1
  exact lt_irrefl _ h1

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitRatioOnChartOverlap
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

namespace GlobalTheory.UnitGlueTransport

theorem radical_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : ℕ) {a : R}
    (ha : a ∈ (Ideal.span {(p : R)}).radical) : f a ∈ (Ideal.span {(p : S)}).radical := by
  obtain ⟨n, hn⟩ := ha
  refine ⟨n, ?_⟩
  rw [Ideal.mem_span_singleton] at hn ⊢
  obtain ⟨c, hc⟩ := hn
  exact ⟨f c, by rw [← map_pow, hc, map_mul, map_natCast]⟩

theorem specMap_appLE {R A : Type} [CommRing R] [CommRing A] (a : R →+* A) (O : (Sp A).Opens)
    (e : O ≤ spMap a ⁻¹ᵁ ⊤) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (spMap a).appLE ⊤ O e =
    CommRingCat.ofHom a ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Sp A).presheaf.map (homOfLE le_top : O ⟶ ⊤).op := by
  have h1 : (spMap a).appLE ⊤ O e =
      (spMap a).appLE ⊤ ⊤ le_top ≫ (Sp A).presheaf.map (homOfLE le_top : O ⟶ ⊤).op :=
    (Scheme.Hom.appLE_map _ _ _).symm
  have e1 : (spMap a).appTop = (spMap a).appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE _
  rw [h1, ← e1, Scheme.ΓSpecIso_inv_naturality_assoc]

theorem appLE_chart {X : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A] (c : Sp R ⟶ X)
    [IsOpenImmersion c] (a : R →+* A) (w : Sp A ⟶ X) (hw : spMap a ≫ c = w) (U : X.Opens)
    (hU : U ≤ c ''ᵁ ⊤) (O : (Sp A).Opens) (hO : O ≤ w ⁻¹ᵁ U) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (c.appIso ⊤).inv ≫ X.presheaf.map (homOfLE hU).op ≫
      w.appLE U O hO =
    CommRingCat.ofHom a ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Sp A).presheaf.map (homOfLE le_top : O ⟶ ⊤).op := by
  subst hw
  rw [Scheme.Hom.map_appLE, ← Scheme.Hom.appLE_comp_appLE (spMap a) c (c ''ᵁ ⊤) ⊤ O
    (by rw [Scheme.Hom.preimage_image_eq]) le_top, Scheme.Hom.appIso_inv_appLE_assoc]
  erw [Scheme.Hom.map_appLE]
  exact specMap_appLE a O _

end GlobalTheory.UnitGlueTransport

namespace GlobalTheory.UnitGlueTransport

theorem map_map {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (z : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom z) =
      (X.presheaf.map (homOfLE h3).op).hom z := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl

variable {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} {Xw : X.Opens} {K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]}
  (h : ∀ x : X, UnitChartAt p Xw K x)

theorem ev_transport (x : X) {A : Type} [CommRing A] (w : Sp A ⟶ X) (a : cR h x →+* A)
    (hw : spMap a ≫ cξ h x = w) (W : X.Opens) (hW : W ≤ Uc h x ⊓ Xp X p)
    (θ : Localization.Away (p : A) →+* Γ(Sp A, w ⁻¹ᵁ W))
    (hθ : θ.comp (algebraMap A _) = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Sp A).presheaf.map (homOfLE le_top : w ⁻¹ᵁ W ⟶ ⊤).op).hom)
    (χ : Localization.Away (p : cR h x) →+* Localization.Away (p : A))
    (hχ : χ.comp (algebraMap (cR h x) _) = (algebraMap A _).comp a)
    (c : Localization.Away (p : cR h x)) :
    (w.app W).hom ((X.presheaf.map (homOfLE hW).op).hom (ev h x c)) = θ (χ c) := by
  have m : (Scheme.ΓSpecIso (CommRingCat.of (cR h x))).inv ≫ ((cξ h x).appIso ⊤).inv ≫
      X.presheaf.map (homOfLE (inf_le_left : Uc h x ⊓ Xp X p ≤ cξ h x ''ᵁ ⊤)).op ≫
      X.presheaf.map (homOfLE hW).op ≫ w.appLE W (w ⁻¹ᵁ W) le_rfl =
      CommRingCat.ofHom a ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Sp A).presheaf.map (homOfLE le_top : w ⁻¹ᵁ W ⟶ ⊤).op := by
    have hc := appLE_chart (cξ h x) a w hw W (hW.trans inf_le_left) (w ⁻¹ᵁ W) le_rfl
    erw [Scheme.Hom.map_appLE, Scheme.Hom.map_appLE]
    erw [Scheme.Hom.map_appLE] at hc
    exact hc
  have key : ((w.app W).hom.comp (X.presheaf.map (homOfLE hW).op).hom).comp (ev h x) = θ.comp χ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : cR h x))
    ext r
    have e1 := congrArg (fun f => f.hom r) m
    have e2 := congrArg (fun f => f (a r)) hθ
    have e3 := congrArg (fun f => f r) hχ
    simp only [RingHom.comp_apply] at e2 e3 ⊢
    rw [e3, e2]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e1
    rw [ev, IsLocalization.Away.lift, IsLocalization.lift_eq, Scheme.Hom.app_eq_appLE]
    exact e1
  exact congrArg (fun f => f c) key

end GlobalTheory.UnitGlueTransport

namespace GlobalTheory.UnitGlueTransport

theorem ratioProp_of_chart : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x) (x y : X) (A : Type) [CommRing A] (w : Sp A ⟶ X) (a1 : cR h x →+* A) (a2 : cR h y →+* A), IsOpenImmersion w → spMap a1 ≫ cξ h x = w → spMap a2 ≫ cξ h y = w → Set.range w = Set.range (cξ h x) ∩ Set.range (cξ h y) → ∀ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical → (∀ (χ1 : Localization.Away (p : cR h x) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : cR h y) →+* Localization.Away (p : A)), χ1.comp (algebraMap (cR h x) _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap (cR h y) _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (cu h y : Localization.Away (p : cR h y)) = χ1 (cu h x : Localization.Away (p : cR h x))) → ∃ u' : Γ(X, Uc h x ⊓ Uc h y)ˣ, RatioProp h x y u' := by
  intro p _ X Xw K h x y A _ w a1 a2 hw hw1 hw2 hrange u hu hχ
  have hVeq : Uc h x ⊓ Uc h y = w.opensRange := by
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_inf, Uc, Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.coe_opensRange]
    exact hrange.symm
  set V := Uc h x ⊓ Uc h y with hVdef
  set W := V ⊓ Xp X p with hWdef
  have hWV : W ≤ V := inf_le_left
  have hWx : W ≤ Uc h x ⊓ Xp X p := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hWy : W ≤ Uc h y ⊓ Xp X p := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hιiso : IsIso (w.app W) := Scheme.Hom.isIso_app w W (hWV.trans hVeq.le)
  have hιinj : Function.Injective (w.app W).hom := (ConcreteCategory.bijective_of_isIso (w.app W)).1
  have hV : ⊤ ≤ w ⁻¹ᵁ V := by rw [hVeq, Scheme.Hom.preimage_opensRange]
  have hφ : IsIso (w.appLE V ⊤ hV) := by
    have h1 : IsIso (w.app V) := Scheme.Hom.isIso_app w V hVeq.le
    have h2 : (⊤ : (Sp A).Opens) = w ⁻¹ᵁ V := le_antisymm hV le_top
    have h3 : IsIso (homOfLE hV) := by
      have : homOfLE hV = eqToHom h2 := rfl
      rw [this]; infer_instance
    rw [Scheme.Hom.appLE]; infer_instance
  let φ := w.appLE V ⊤ hV ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom
  let e : Γ(X, V) ≃+* A := RingEquiv.ofBijective φ.hom (ConcreteCategory.bijective_of_isIso φ)
  have he : ∀ z, (w.appLE V ⊤ hV).hom (e.symm z) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom z := by
    intro z
    have h0 : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((w.appLE V ⊤ hV).hom (e.symm z)) = z :=
      e.apply_symm_apply z
    have h1 : (w.appLE V ⊤ hV).hom (e.symm z) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((w.appLE V ⊤ hV).hom (e.symm z))) := by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    exact h1.trans (congrArg _ h0)
  let u' : Γ(X, V)ˣ := Units.map e.symm.toRingHom.toMonoidHom u
  refine ⟨u', ?_⟩
  unfold RatioProp
  refine ⟨?_, ?_⟩
  · let gB : A →+* Γ(Sp A, w ⁻¹ᵁ W) := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Sp A).presheaf.map (homOfLE le_top : w ⁻¹ᵁ W ⟶ ⊤).op).hom
    have hpB : IsUnit ((p : Γ(Sp A, w ⁻¹ᵁ W))) := by
      have h0 := (isUnit_natCast_res h x).map ((w.app W).hom.comp (X.presheaf.map (homOfLE hWx).op).hom)
      erw [map_natCast, map_natCast] at h0
      exact h0
    have hgp : IsUnit (gB (p : A)) := by rw [map_natCast]; exact hpB
    let θ : Localization.Away (p : A) →+* Γ(Sp A, w ⁻¹ᵁ W) := IsLocalization.Away.lift (p : A) hgp
    have hθ : θ.comp (algebraMap A _) = gB := IsLocalization.Away.lift_comp _ hgp
    have hp1 : IsUnit (((algebraMap A (Localization.Away (p : A))).comp a1) (p : cR h x)) := by
      rw [map_natCast, ← map_natCast (algebraMap A (Localization.Away (p : A))) p]
      exact IsLocalization.Away.algebraMap_isUnit _
    have hp2 : IsUnit (((algebraMap A (Localization.Away (p : A))).comp a2) (p : cR h y)) := by
      rw [map_natCast, ← map_natCast (algebraMap A (Localization.Away (p : A))) p]
      exact IsLocalization.Away.algebraMap_isUnit _
    let χ1 : Localization.Away (p : cR h x) →+* Localization.Away (p : A) := IsLocalization.Away.lift _ hp1
    let χ2 : Localization.Away (p : cR h y) →+* Localization.Away (p : A) := IsLocalization.Away.lift _ hp2
    have hχ1 : χ1.comp (algebraMap _ _) = (algebraMap A _).comp a1 := IsLocalization.Away.lift_comp _ hp1
    have hχ2 : χ2.comp (algebraMap _ _) = (algebraMap A _).comp a2 := IsLocalization.Away.lift_comp _ hp2
    have key := hχ χ1 χ2 hχ1 hχ2
    have ex := ev_transport h x w a1 hw1 W hWx θ hθ χ1 hχ1 (cu h x)
    have ey := ev_transport h y w a2 hw2 W hWy θ hθ χ2 hχ2 (cu h y)
    have eu : (w.app W).hom ((X.presheaf.map (homOfLE hWV).op).hom (u' : Γ(X, V))) = gB u := by
      have m : X.presheaf.map (homOfLE hWV).op ≫ w.app W =
          w.appLE V ⊤ hV ≫ (Sp A).presheaf.map (homOfLE le_top : w ⁻¹ᵁ W ⟶ ⊤).op := by
        rw [Scheme.Hom.app_eq_appLE]
        erw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
      have m' := congrArg (fun f => f.hom (u' : Γ(X, V))) m
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at m'
      rw [m']
      have : (u' : Γ(X, V)) = e.symm (u : A) := rfl
      rw [this, he]
      rfl
    have goalEq : (w.app W).hom ((X.presheaf.map (homOfLE hWV).op).hom (u' : Γ(X, V))) *
        (w.app W).hom ((X.presheaf.map (homOfLE hWy).op).hom (ev h y (cu h y))) =
        (w.app W).hom ((X.presheaf.map (homOfLE hWx).op).hom (ev h x (cu h x))) := by
      rw [eu, ey, ex, ← key, map_mul]
      congr 1
      exact (congrArg (fun f => f (u : A)) hθ).symm
    apply Units.ext
    apply hιinj
    rw [Units.val_mul, map_mul]
    exact goalEq
  · have h0 : ((u' : Γ(X, V)) - 1) = e.symm ((u : A) - 1) := by
      rw [map_sub, map_one]; rfl
    rw [h0]
    exact radical_map e.symm.toRingHom p hu

end GlobalTheory.UnitGlueTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

def Cond {X X' Z : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) : Prop :=
  ∀ W : X.Opens, IsAffineOpen W → Function.Injective (p.app W) ∧
    ∀ x : Γ(X, W), i.app W x = 0 → ∀ r : Γ(X', p ⁻¹ᵁ W), ∃ y : Γ(X, W), i.app W y = 0 ∧ p.app W y = p.app W x * r

def UnitsPatch {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) : Prop :=
  ∀ W : X.Opens, Function.Injective (pullU p W) ∧
    ∀ (u' : Γ(X', p ⁻¹ᵁ W)ˣ) (v : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) u' = gm p' z (i ⁻¹ᵁ W) v) → ∃ u : Γ(X, W)ˣ, pullU p W u = u'

def LocGen {Y : Scheme.{0}} (L : LB Y) (V : Y.Opens) (a : ∀ k, Γ(Y, V ⊓ L.U k)ˣ) : Prop :=
  ∀ (y : Y) (k k' : L.ι), y ∈ V → y ∈ L.U k → y ∈ L.U k' →
    gm (𝟙 Y) y (V ⊓ L.U k) (a k) = gm (𝟙 Y) y (L.U k ⊓ L.U k') (L.g k k') * gm (𝟙 Y) y (V ⊓ L.U k') (a k')

def Matches {X' Z Z' : Scheme.{0}} (i' : Z' ⟶ X') (p' : Z' ⟶ Z) {L' : LB X'} {N : LB Z}
    (w : LB.Iso (L'.pull i') (N.pull p')) {V' : X'.Opens} {V : Z.Opens} (a : ∀ k, Γ(X', V' ⊓ L'.U k)ˣ)
    (b : ∀ l, Γ(Z, V ⊓ N.U l)ˣ) : Prop :=
  ∀ (z : Z') (k : L'.ι) (l : N.ι), i' z ∈ V' → p' z ∈ V → i' z ∈ L'.U k → p' z ∈ N.U l →
    gm p' z (V ⊓ N.U l) (b l) =
      gm (𝟙 Z') z ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) *
        gm i' z (V' ⊓ L'.U k) (a k)

def Pinched (g : ℕ) {S S' Z B' C Y : Scheme.{0}} (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z)
    (i : Y ⟶ B') (q : Y ⟶ C) (x : B') : Prop :=
  ∃ (U U' V : Scheme.{0}) (u : U ⟶ S) (p : U' ⟶ U) (j : U' ⟶ B') (n : V ⟶ U) (k : V ⟶ C),
    SmoothOfRelativeDimension g u ∧ IsPullback p (j ≫ b') u s' ∧ IsOpenImmersion j ∧ x ∈ Set.range j ∧
    IsPullback n (k ≫ e) u z ∧
    ∀ (T : Scheme.{0}) (a : T ⟶ U') (a' : T ⟶ V), a ≫ p = a' ≫ n → ∃ y : T ⟶ Y, y ≫ i = a ≫ j ∧ y ≫ q = a' ≫ k

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsGoodLevelStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_points_good_level : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → (∀ p : ℕ, p.Prime → l.GoodAt p) → UnramPts Xo c (badPrimes H l) := by
  first | exact @GlobalTheory.UnramCM.unramPts_of_cm | exact GlobalTheory.UnramCM.unramPts_of_cm | (intros; apply GlobalTheory.UnramCM.unramPts_of_cm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringFractionsOfEssFiniteTypeComplexStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_fractions_of_essFiniteType_complex : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (hψ : ∀ a, ψ a ∈ V), (ψ.codRestrict V hψ).EssFiniteType → ∃ s₀ : Finset L, (∀ x ∈ s₀, x ∈ V) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  first | exact @GlobalTheory.valuationSubring_fractions_of_essFiniteType | exact GlobalTheory.valuationSubring_fractions_of_essFiniteType | (intros; apply GlobalTheory.valuationSubring_fractions_of_essFiniteType <;> assumption)
end

