import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationCompactSetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFormallyUnramifiedStandardSmoothSameRelDiStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_formallyUnramified_standardSmooth_same_relDim : ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (g : ℕ), Algebra.IsStandardSmoothOfRelativeDimension g A B → Algebra.IsStandardSmoothOfRelativeDimension g A C → Algebra.FormallyUnramified B C → Algebra.Etale B C := by
  first | exact @GlobalTheory.etale_of_formallyUnramified_of_relDim | exact GlobalTheory.etale_of_formallyUnramified_of_relDim | (intros; apply GlobalTheory.etale_of_formallyUnramified_of_relDim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationCompactSetBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_compact_set_bound : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (κ : UA σ X.J) (h : UA σ W.J), κ ∈ Cc →
      ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * (ht h : ℝ) ^ k ∧ ∀ z : Fin n × Fin d → AF F,
        ‖e (om (κ, h) (pureA F f φ)) z‖ ≤
          C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j))) ^ N)⁻¹ ∧
        (e (om (κ, h) (pureA F f φ)) z ≠ 0 → ∀ j (v : Pl F), evFin F v ((m : AF F) * z j) ∈ v.adicCompletionIntegers F) := by
  first | exact @GlobalTheory.ThKTorusBound.major_bound | exact GlobalTheory.ThKTorusBound.major_bound | (intros; apply GlobalTheory.ThKTorusBound.major_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDefectDegenerationDataBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem gm_spMap_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) (y : Sp B) :
    gm (spMap f) y ⊤ (unitOn u) = gm (𝟙 (Sp B)) y ⊤ (unitOn (Units.map f.toMonoidHom u)) := by
  apply Units.ext
  rw [gm_val _ y ⊤ trivial, gm_val _ y ⊤ trivial]
  have nat := congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact congrArg ((Sp B).presheaf.germ ⊤ y trivial).hom nat.symm

theorem evenDefect_baseChange : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β → v.IsGen → (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) → GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v → GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) → ∀ h : D₁.X → (FractionRing R₁)ˣ, EvenDefect D₁ h → EvenDefect D₂ fun χ => Units.map gam.toMonoidHom (h (xe χ)) := by
  intro R₁ _ _ R₂ _ _ σ D₁ D₂ β v xe gam hgam gp hv hc _ hψ h hE χ z J₂ hJ₂
  beta_reduce
  have hgam' : spMap gam ≫ jK R₁ = jK R₂ ≫ spMap σ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hgam
  have cx : ∀ a, D₂.xK a ≫ β = spMap gam ≫ D₁.xK (xe a) := fun a => by
    show (jK R₂ ≫ (D₂.c a).left) ≫ β = spMap gam ≫ jK R₁ ≫ (D₁.c (xe a)).left
    rw [Category.assoc, hc, ← Category.assoc, ← hgam', Category.assoc]
  have cn : D₂.xK (-χ) = D₂.xK χ ≫ (ι[D₂.P.A]).left := by
    show (toUnit _ ≫ D₂.c (-χ)).left = _
    rw [GlobalTheory.PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  choose J₁ hJ₀ using fun φ : (TK R₂).left ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (φ z)
  have hJ₁ : Good D₁.P.L z J₁ := hJ₀
  have vψ : ∀ a, val (D₁.psi (xe a)) (spMap gam) z J₁ =
      (gw v (D₂.xK a) z (J₁ (D₂.xK a ≫ β)) (J₂ (D₂.xK a)))⁻¹ * val (D₂.psi a) (𝟙 _) z J₂ := fun a => by
    have := GlobalTheory.CubTransport.val_pmaps (fun _ => cx a) (hψ a) (𝟙 _) hJ₁ hJ₂
    rwa [Fintype.prod_unique, Category.id_comp, Category.id_comp, zpow_neg_one] at this
  have hcorr := corr_of_val D₁.P.isLB (t := LB.mulGen _ _ _ _ _ (D₁.psi (-(xe χ))) (LB.pullGen _ _ _ D₁.sym (D₁.xK (xe χ))))
    (t' := GlobalTheory.UU.scaleGen (unitOn (h (xe χ))) (D₁.psi (xe χ))) fun y J hJ => by
      rw [val_mul hJ, val_pull hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, Category.id_comp]
      exact hE (xe χ) y J hJ
  have e := val_corr hJ₁ hcorr (spMap gam)
  have hg : gm (spMap gam) z ⊤ (unitOn (h (xe χ))) =
      gm (𝟙 (TK R₂).left) z ⊤ (unitOn (Units.map gam.toMonoidHom (h (xe χ)))) := gm_spMap_unitOn gam _ z
  rw [val_mul hJ₁, val_pull hJ₁, GlobalTheory.UU.val_scaleGen _ _ _ hJ₁, hg, ← cx, ← map_neg xe χ, vψ, vψ] at e
  have hs := GlobalTheory.PsiRing.val_sym_comp GlobalTheory.globalFns_holds gp hv (D₂.xK χ) z hJ₁ hJ₂
  rw [← cn] at hs
  rw [hs] at e
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianQuotientAffineCover
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbQuotientLocal

theorem exists_quotient_of_openImmersion (S : Scheme.{0}) [IsLocallyNoetherian S] (R : CommRingCat.{0})
    (f : Spec R ⟶ S) [IsOpenImmersion f] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A)
    (hA : IsAbelianScheme A) (hi : IsMonHom i) (hm : Mono i) (hf : IsFinite H.hom) (hfl : Flat H.hom) :
    ∃ (B : Over (Spec R)) (_ : GrpObj B) (q : (Over.pullback f).obj A ⟶ B),
      IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst ((Over.pullback f).obj H) ((Over.pullback f).obj A) ≫
          (Over.pullback f).map i) * snd ((Over.pullback f).obj H) ((Over.pullback f).obj A))
        (snd ((Over.pullback f).obj H) ((Over.pullback f).obj A)) q q := by
  have hN : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherianRing R := (isLocallyNoetherian_Spec (R := R)).1 hN
  have hA' : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have hi' : IsMonHom ((Over.pullback f).map i) := inferInstance
  have hm' : Mono ((Over.pullback f).map i) := inferInstance
  have hf' : IsFinite ((Over.pullback f).obj H).hom := by
    show IsFinite (pullback.snd H.hom f)
    infer_instance
  have hfl' : Flat ((Over.pullback f).obj H).hom := by
    show Flat (pullback.snd H.hom f)
    infer_instance
  obtain ⟨B, hB, q, -, h1, h2, h3, h4, h5, -, h6⟩ :=
    GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme R ((Over.pullback f).obj A)
      ((Over.pullback f).obj H) ((Over.pullback f).map i) hA' hi' hm' hf' hfl'
  exact ⟨B, hB, q, h1, h2, h3, h4, h5, h6⟩

theorem exists_local_quotient : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A),
    IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∀ j : S.affineCover.I₀,
    ∃ (B : Over (S.affineCover.X j)) (_ : GrpObj B) (q : (Over.pullback (S.affineCover.f j)).obj A ⟶ B),
      IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A) ≫
          (Over.pullback (S.affineCover.f j)).map i) *
          snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A))
        (snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A)) q q := by
  intro S _ A _ H _ i hA hi hm hf hfl j
  haveI : IsOpenImmersion (S.affineCover.f j) := S.affineCover.map_prop j
  exact @exists_quotient_of_openImmersion S _ _ (S.affineCover.f j) this A _ H _ i hA hi hm hf hfl

end GlobalTheory.AbQuotientLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquare
section
open CategoryTheory Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbBaseChangeSq

theorem exists_baseChange_and_sq : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (A : Over (Sp R₀)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (B : Over (Sp R₁)) (_ : GrpObj B) (pr : B.left ⟶ A.left) (pr' : (B ⊗ B).left ⟶ (A ⊗ A).left), IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsPullback pr B.hom A.hom (spMap (algebraMap R₀ R₁)) ∧ IsPullback pr' (B ⊗ B).hom (A ⊗ A).hom (spMap (algebraMap R₀ R₁)) ∧ (μ[B]).left ≫ pr = pr' ≫ (μ[A]).left ∧ (fst B B).left ≫ pr = pr' ≫ (fst A A).left ∧ (snd B B).left ≫ pr = pr' ≫ (snd A A).left ∧ (CartesianMonoidalCategory.lift (𝟙 B) (1 : B ⟶ B)).left ≫ pr' = pr ≫ (CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ A)).left ∧ (CartesianMonoidalCategory.lift (1 : B ⟶ B) (𝟙 B)).left ≫ pr' = pr ≫ (CartesianMonoidalCategory.lift (1 : A ⟶ A) (𝟙 A)).left := by
  intro R₀ R₁ _ _ _ A _ g hA hg
  let f : Sp R₁ ⟶ Sp R₀ := spMap (algebraMap R₀ R₁)
  let F := Over.pullback f
  let B : Over (Sp R₁) := F.obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsGrpPullback B A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  obtain ⟨hAB, hgB⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ A B _ g hB hA hg
  have mapL : ∀ {X Y : Over (Sp R₀)} (a : X ⟶ Y),
      (F.map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left := fun a => pullback.lift_fst _ _ _
  let m := Functor.LaxMonoidal.μ F A A
  refine ⟨B, inferInstance, pullback.fst A.hom f, m.left ≫ pullback.fst (A ⊗ A).hom f, hAB, hgB, hB.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · haveI : IsIso m := inferInstanceAs (IsIso (Functor.Monoidal.μIso F A A).hom)
    haveI : IsIso m.left := (Over.forget _).map_isIso m
    have h1 : IsPullback m.left (B ⊗ B).hom (F.obj (A ⊗ A)).hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w m⟩
    have h2 := h1.paste_horiz (IsPullback.of_hasPullback (A ⊗ A).hom f)
    rwa [Category.id_comp] at h2
  · have e : μ[B] = m ≫ F.map μ[A] := Functor.obj.μ_def (F := F) A
    rw [e, Over.comp_left, Category.assoc, mapL, Category.assoc]
  · rw [Category.assoc, ← mapL, ← Category.assoc, ← Over.comp_left]
    simp [m]
    rfl
  · rw [Category.assoc, ← mapL, ← Category.assoc, ← Over.comp_left]
    simp [m]
    rfl
  · have e : lift (𝟙 B) (1 : B ⟶ B) ≫ m = F.map (lift (𝟙 A) (1 : A ⟶ A)) := by
      rw [← Functor.Monoidal.lift_μ, F.map_id, Functor.map_one]
    rw [← Category.assoc, ← Over.comp_left, e, mapL]
  · have e : lift (1 : B ⟶ B) (𝟙 B) ≫ m = F.map (lift (1 : A ⟶ A) (𝟙 A)) := by
      rw [← Functor.Monoidal.lift_μ, F.map_id, Functor.map_one]
    rw [← Category.assoc, ← Over.comp_left, e, mapL]

end GlobalTheory.AbBaseChangeSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineIntersectionChartsStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_intersection_charts : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∀ (R1 R2 : Type) [CommRing R1] [CommRing R2] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → ∃ (A : Type) (_ : CommRing A) (w : Sp A ⟶ X) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion w ∧ spMap a1 ≫ ξ1 = w ∧ spMap a2 ≫ ξ2 = w ∧ Set.range w = Set.range ξ1 ∩ Set.range ξ2 := by
  first | exact @GlobalTheory.UnitGlue.chart_inter_factor | exact GlobalTheory.UnitGlue.chart_inter_factor | (intros; apply GlobalTheory.UnitGlue.chart_inter_factor <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdBasicOpenStandardSmooth
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.Pinch

theorem appTop_ι_comp_eq {C Z : Scheme.{0}} (e : C ⟶ Z) (U : C.Opens) :
    (U.ι ≫ e).appTop = e.appLE ⊤ U le_top ≫ U.topIso.inv := by
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso, Scheme.Hom.comp_appTop, Scheme.Opens.ι_app]
  simp [← Functor.map_comp]

theorem exists_affine_basicOpen_standardSmooth : ∀ (g : ℕ) (C Z : Scheme.{0}) [IsAffine Z] (e : C ⟶ Z),
    SmoothOfRelativeDimension g e → ∀ x : C, ∃ O : C.Opens, IsAffineOpen O ∧ x ∈ O ∧
      ∀ r : Γ(C, O), (((C.basicOpen r).ι ≫ e).appTop).hom.IsStandardSmoothOfRelativeDimension g := by
  intro g C Z _ e he x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) e he
    ⟨⊤, isAffineOpen_top Z⟩ ⟨W, hW⟩ le_top
  obtain ⟨s, hs, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 hs hxW
  obtain ⟨⟨t, ht⟩, hxt⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen t
  have h1 := h' t ht Γ(C, C.basicOpen t)
  refine ⟨C.basicOpen t, hW.basicOpen t, hxt, fun r => ?_⟩
  have hl2 := (hW.basicOpen t).isLocalization_basicOpen r
  have h2 := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).right
    Γ(C, C.basicOpen r) r _ h1
  have h3 : (e.appLE ⊤ (C.basicOpen r) le_top).hom.IsStandardSmoothOfRelativeDimension g := by
    convert h2 using 1
    ext a
    change _ = (C.presheaf.map (homOfLE (C.basicOpen_le r)).op) ((C.presheaf.map (homOfLE (C.basicOpen_le t)).op) _)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_map]
  rw [appTop_ι_comp_eq, CommRingCat.hom_comp]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    (C.basicOpen r).topIso.symm.commRingCatIsoToRingEquiv h3

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusDescendFlatBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.FlatSec
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AmplePoint

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem exists_of_mem_map [Algebra R R'] {A A' : Type} [CommRing A] [CommRing A'] [Algebra R A] (p : A →+* A')
    (s' : R' →+* A') (e : R' ⊗[R] A ≃+ A') (he : ∀ c v, e (c ⊗ₜ v) = s' c * p v) (N : Ideal A) {y : A'}
    (hy : y ∈ N.map p) : ∃ x : R' ⊗[R] (N.restrictScalars R), e ((N.restrictScalars R).subtype.lTensor R' x) = y := by
  suffices h : ∀ r, ∃ x : R' ⊗[R] (N.restrictScalars R), e ((N.restrictScalars R).subtype.lTensor R' x) = r * y by
    simpa using h 1
  refine Submodule.span_induction (p := fun y _ => ∀ r, ∃ x : R' ⊗[R] (N.restrictScalars R),
    e ((N.restrictScalars R).subtype.lTensor R' x) = r * y) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨v, hv, rfl⟩ r
    obtain ⟨t, rfl⟩ := e.surjective r
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c a => exact ⟨c ⊗ₜ ⟨a * v, N.mul_mem_left a hv⟩, by simp [he, mul_assoc]⟩
    | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨x', hx'⟩ := hb
      exact ⟨x + x', by rw [map_add, map_add, hx, hx', map_add, add_mul]⟩
  · exact fun r => ⟨0, by simp⟩
  · intro a b _ _ ha hb r
    obtain ⟨x, hx⟩ := ha r
    obtain ⟨x', hx'⟩ := hb r
    exact ⟨x + x', by rw [map_add, map_add, hx, hx', mul_add]⟩
  · intro a b _ hb r
    obtain ⟨x, hx⟩ := hb (r * a)
    exact ⟨x, by rw [hx, smul_eq_mul, mul_assoc]⟩

def vanIdeal (W U : X.Opens) : Ideal Γ(X, W) where
  carrier := {v | X.basicOpen v ≤ U}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => (X.basicOpen_add_le a b).trans (sup_le ha hb)
  smul_mem' := fun c a ha => by
    change X.basicOpen (c * a) ≤ U
    rw [Scheme.basicOpen_mul]
    exact inf_le_right.trans ha

theorem exists_pow_mem (π : X' ⟶ X) [IsAffineHom π] {W : X.Opens} (hW : IsAffineOpen W) (U : X.Opens)
    (t : Γ(X', π ⁻¹ᵁ W)) (ht : X'.basicOpen t ≤ π ⁻¹ᵁ U) : ∃ m, t ^ m ∈ (vanIdeal W U).map (π.app W).hom := by
  have hW' := hW.preimage π
  change t ∈ ((vanIdeal W U).map (π.app W).hom).radical
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hP, hp⟩
  by_contra h
  let z : Spec Γ(X', π ⁻¹ᵁ W) := ⟨P, hp⟩
  have key : ∀ s : Γ(X', π ⁻¹ᵁ W), hW'.fromSpec z ∈ X'.basicOpen s ↔ s ∉ P := fun s => by
    change z ∈ hW'.fromSpec ⁻¹ᵁ X'.basicOpen s ↔ _
    rw [hW'.fromSpec_preimage_basicOpen]
    rfl
  have hz := (key t).2 h
  obtain ⟨v, hv, hzv⟩ := hW.exists_basicOpen_le (V := U) ⟨π (hW'.fromSpec z), ht hz⟩ (X'.basicOpen_le t hz)
  refine (key ((π.app W).hom v)).1 ?_ (hP (Ideal.mem_map_of_mem _ hv))
  rw [← Scheme.preimage_basicOpen]
  exact hzv

theorem exists_sec_mem (g : R →+* R') (hg : g.Flat) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R'))
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (M : LB X) (hM : M.IsLB) {α : Type} [Fintype α]
    (W : α → X.Opens) (j : α → M.ι) (hA : ∀ a, IsAffineOpen (W a)) (hW : ∀ a, W a ≤ M.U (j a))
    (hc : ∀ y : X, ∃ a, y ∈ W a) (N : ∀ a, Ideal Γ(X, W a)) (σ : LB.Sec (M.pull π))
    (hσ : ∀ a, rs X' (le_pull M π (hW a)) (σ.f fun _ => j a) ∈ (N a).map (π.app (W a)).hom)
    (z : X') (hz : z ∈ nonzeroLocus σ) :
    ∃ u : M.Sec, π z ∈ nonzeroLocus u ∧ ∀ a, rs X (hW a) (u.f (j a)) ∈ N a := by
  let _ : Algebra R R' := g.toAlgebra
  have : Module.Flat R R' := hg
  let _ : ∀ U : X.Opens, Algebra R Γ(X, U) := fun U => (cst f U).toAlgebra
  choose e he using fun a => exists_equiv_of_isPushout (R := R) (π.app (W a)) (cst f' (π ⁻¹ᵁ W a))
    (isPushout_app hg H (hA a).isCompact (hA a).isQuasiSeparated)
  choose e' he' using fun p : α × α => exists_equiv_of_isPushout (R := R) (π.app (W p.1 ⊓ W p.2))
    (cst f' (π ⁻¹ᵁ (W p.1 ⊓ W p.2))) (isPushout_app hg H
      (QuasiSeparatedSpace.inter_isCompact _ _ (W p.1).isOpen (hA p.1).isCompact (W p.2).isOpen (hA p.2).isCompact)
      (IsQuasiSeparated.of_quasiSeparatedSpace _))
  let d : (∀ a, (N a).restrictScalars R) →ₗ[R] (∀ p : α × α, Γ(X, W p.1 ⊓ W p.2)) :=
    { toFun := fun v p => rs X inf_le_left (v p.1).1 -
        rs X (inf_le_inf (hW p.1) (hW p.2)) (M.g (j p.1) (j p.2)).val * rs X inf_le_right (v p.2).1
      map_add' := fun v w => funext fun p => by
        simp only [Pi.add_apply, Submodule.coe_add, map_add]; ring
      map_smul' := fun r v => funext fun p => by
        simp only [Pi.smul_apply, Submodule.coe_smul, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, rs_cst,
          RingHom.id_apply]; ring }
  choose x hxe using fun a => exists_of_mem_map (π.app (W a)).hom (cst f' (π ⁻¹ᵁ W a)) (e a) (he a) (N a) (hσ a)
  have hx : ∀ {n : ℕ} {c : Fin n → R'} {v : Fin n → ∀ a, (N a).restrictScalars R},
      (∀ a, x a = ∑ i, AddEquiv.refl _ (c i ⊗ₜ v i a)) →
      ∀ a z, π z ∈ W a → gs (𝟙 X') z _ (σ.f fun _ => j a) =
        ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ (v i a).1 := fun {n c v} h a z hz => by
    have h' := congrArg (gs (𝟙 X') z (π ⁻¹ᵁ W a)) (hxe a).symm
    simp only [h a, map_sum, AddEquiv.refl_apply, LinearMap.lTensor_tmul, Submodule.subtype_apply, he] at h'
    rw [gs_comb f' π _ z hz] at h'
    exact (gs_res (𝟙 X') z _ hz _).symm.trans h'
  obtain ⟨n, c, v, hv, hd⟩ := exists_comb_ker (fun a => AddEquiv.refl _) e' d x
    (fun n c v h p => fn_ext fun z hz => by
      simp only [he']
      rw [gs_comb f' π _ z hz, LBGerm.gs_zero (𝟙 X') z _ hz]
      have h₁ := gs_pull_trans σ z (hW _ hz.1) (hW _ hz.2)
      rw [hx h p.1 z hz.1, hx h p.2 z hz.2, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
      refine (congrArg _ (gs_diff (hW p.1) (hW p.2) (v i p.1).1 (v i p.2).1 π z hz)).trans ?_
      ring)
  choose u hu using fun i => exists_sec_of_refinement hM W j hW hc (fun a => (v i a).1) fun y a b ha hb => by
    have h := congrArg (gs (𝟙 X) y (W a ⊓ W b)) (congrFun (hd i) (a, b))
    exact sub_eq_zero.1 ((gs_diff (hW a) (hW b) (v i a).1 (v i b).1 (𝟙 X) y ⟨ha, hb⟩).symm.trans
      (h.trans (LBGerm.gs_zero (𝟙 X) y _ ⟨ha, hb⟩)))
  have hu' : ∀ i a, rs X (hW a) ((u i).f (j a)) = (v i a).1 := fun i a => fn_ext fun y hy => by
    rw [gs_res (𝟙 X) y _ hy, hu i y (j a) a (hW a hy) hy, gm_self hM (𝟙 X) y (hW a hy), Units.val_one,
      _root_.one_mul]
  obtain ⟨a, ha⟩ := hc (π z)
  have h₁ := (mem_nonzeroLocus_iff_isUnit σ (k := fun _ => j a) (mem_pull.2 (hW a ha))).1 hz
  replace h₁ := hx hv a z ha ▸ h₁
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum h₁
  refine ⟨u i, (mem_nonzeroLocus_iff_pull (u i) π z (hW a ha)).2 ?_, fun b => hu' i b ▸ (v i b).2⟩
  rw [← gs_res π z (hW a) ha]
  exact (congrArg (fun w => IsUnit (gs π z _ w)) (hu' i a)).mpr (isUnit_of_mul_isUnit_right hi)

def chartPullPullPow (L : LB X) (f : X' ⟶ X) (n : ℕ) :
    ChartPull ((lbPow L n).pull f) (lbPow (L.pull f) n) (𝟙 X') where
  idx J := fun _ _ => J PUnit.unit PUnit.unit
  le _ _ hy := mem_powChart.2 (mem_pull.2 (mem_powChart.1 (mem_pull.1 hy)))
  g y J J' hJ hJ' := by
    have h₁ := mem_pull.1 hJ
    have h₂ := mem_pull.1 hJ'
    refine (gm_pull_g (lbPow L n) f (𝟙 X') y J J' hJ hJ').trans (Eq.symm ?_)
    refine ((chartPullPowPull L f n).g y _ _ (mem_powChart.2 (mem_pull.2 (mem_powChart.1 h₁)))
      (mem_powChart.2 (mem_pull.2 (mem_powChart.1 h₂)))).trans ?_
    rw [Category.id_comp]
    rfl

theorem exists_affine_locus : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Flat → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), QuasiCompact q → QuasiSeparated q → ∀ (L : LB X), L.IsLB → ∀ (x' : ↥(Limits.pullback q (spMap ρ))), (∃ n, 1 ≤ n ∧ ∃ s : (lbPow (L.pull (pullback.fst q (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) → ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, pullback.fst q (spMap ρ) x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  rintro R R' _ _ ρ hρ X q _ _ L hL x' ⟨n, hn, s, hs, ha⟩
  have H := IsPullback.of_hasPullback q (spMap ρ)
  generalize pullback.snd q (spMap ρ) = q' at H
  have hπ : IsAffineHom (pullback.fst q (spMap ρ)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q (spMap ρ)).flip inferInstance
  generalize pullback.fst q (spMap ρ) = π at *
  generalize Limits.pullback q (spMap ρ) = X' at *
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated q
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated π
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := π x') trivial
  obtain ⟨φ, hφ, hxφ⟩ := ha.exists_basicOpen_le (V := π ⁻¹ᵁ U) ⟨x', hx⟩ hs
  obtain ⟨k, hk, t, ht⟩ := exists_nonzeroLocus_eq_basicOpen (LB.isLB_pull hL π) s φ
  obtain ⟨α, _, W, J, hWa, hW, hc⟩ : ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (J : α → PUnit → L.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ powChart L (J a)) ∧ ∀ y : X, ∃ a, y ∈ W a :=
    exists_finite_affine_refinement (isLB_lbPow hL 0)
  have le : ∀ a, π ⁻¹ᵁ W a ≤ powChart (L.pull π) (fun _ _ => J a PUnit.unit) := fun a y hy =>
    mem_powChart.2 (mem_pull.2 (mem_powChart.1 (hW a hy)))
  choose m hm using fun a => exists_pow_mem π (hWa a) U (resG X' (le a) (powFn t _)) fun y hy => by
    have hy₁ : y ∈ π ⁻¹ᵁ W a := X'.basicOpen_le _ hy
    have h := (LBGerm.isUnit_gs_iff (𝟙 X') y _ hy₁ _).2 hy
    exact hφ (ht.le ((mem_nonzeroLocus_iff_powFn t (le a hy₁)).2
      ((congrArg IsUnit (gs_res (𝟙 X') y (le a) hy₁ _)).mp h)))
  let K := Finset.univ.sup m + 1
  have hK : 1 ≤ K := Nat.le_add_left _ _
  obtain ⟨u, hxu, hu⟩ := exists_sec_mem ρ hρ q π q' H (lbPow L (n * k * K)) (isLB_lbPow hL _) W J hWa hW hc
    (fun a => vanIdeal (W a) U) (chartSec (chartPullPullPow L π _) (secPow t K)) (fun a => by
      have e : rs X' (le_pull (lbPow L (n * k * K)) π (hW a))
          ((chartSec (chartPullPullPow L π _) (secPow t K)).f fun _ => J a) = resG X' (le a) (powFn t _) ^ K :=
        fn_ext fun y hy => by
          refine (gs_res (𝟙 X') y _ hy _).trans ((gs_chartSec _ _ (𝟙 X') y _
            (le_pull (lbPow L (n * k * K)) π (hW a) hy)).trans ?_)
          rw [Category.comp_id, LBGerm.gs_pow (𝟙 X') y _ hy, gs_res (𝟙 X') y _ hy]
          exact LBGerm.gs_pow (𝟙 X') y _ (le a hy) _ _
      rw [e]
      exact Ideal.pow_mem_of_pow_mem _ (hm a) ((Finset.le_sup (f := m) (Finset.mem_univ a)).trans (Nat.le_succ _)))
    x' (by
      rw [nonzeroLocus_chartSec_id (chartPullPullPow L π _) _ fun y I hI => ⟨fun _ _ => I PUnit.unit PUnit.unit,
        mem_pull.2 (mem_powChart.2 (mem_pull.1 (mem_powChart.1 hI)))⟩, nonzeroLocus_secPow t hK, ht]
      exact hxφ)
  have hle : nonzeroLocus u ≤ U := fun y hy => by
    obtain ⟨a, hya⟩ := hc y
    refine (show X.basicOpen _ ≤ U from hu a) ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hya _).1 ?_)
    exact (congrArg IsUnit (gs_res (𝟙 X) y (hW a) hya _)).mpr ((mem_nonzeroLocus_iff_isUnit u (hW a hya)).1 hy)
  have h := isAffineOpen_nonzeroLocus_inf (isLB_lbPow hL _) u hU
  rw [inf_eq_left.2 hle] at h
  exact ⟨_, Nat.mul_pos (Nat.mul_pos hn hk) hK, u, hxu, h⟩

end GlobalTheory.AmplePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleGrpScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymAmple

open GlobalTheory.CechPic

theorem exists_isAmpleLB_symm (S : Scheme.{0}) (G : Over S) [GrpObj G] (M₀ : LB G.left) (h₀ : IsAmpleLB M₀) :
    ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  set i : G.left ⟶ G.left := (GrpObj.inv : G ⟶ G).left with hi_def
  have hii : i ≫ i = 𝟙 G.left := by
    rw [hi_def, ← Over.comp_left, GrpObj.inv_comp_inv G, Over.id_left]
  have : IsIso i := ⟨⟨i, hii, hii⟩⟩
  have hL := h₀.isLB
  have h₁ : IsAmpleLB (M₀.pull i) := h₀.pull_of_isAffineHom i
  let M : LB G.left := LB.LinComb M₀ (K := Fin 2) ![𝟙 G.left, i] ![1, 1]
  have hM : M.IsLB := LB.isLB_linComb hL _ _
  have hc : cls M hM = cls M₀ hL + pull i (cls M₀ hL) := by
    rw [cls_linComb hL]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_zsmul, pull_id]
  refine ⟨M, h₀.tensor h₁ hM ?_, ?_⟩
  · have hd₁ := LB.isLB_div hM hL
    have hd₂ := LB.isLB_div hd₁ (pull_isLB hL i)
    refine (cls_eq_zero_iff hd₂).1 ?_
    rw [cls_div hd₁ (pull_isLB hL i), cls_div hM hL, hc, cls_pull hL]
    abel
  · refine (cls_eq_iff (pull_isLB hM i) hM).1 ?_
    rw [cls_pull hM, hc, map_add, ← pull_comp, hii, pull_id]
    exact add_comm _ _

end GlobalTheory.SymAmple
end

