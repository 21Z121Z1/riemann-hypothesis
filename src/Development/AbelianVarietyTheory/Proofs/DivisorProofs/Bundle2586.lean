import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0705
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModification
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgeDominates

theorem exists_sec_div {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X] {L A : LB X} (hL : L.IsLB)
    (hA : A.IsLB) (t : L.Sec) (i : A.ι) (hi : nonzeroLocus t ≤ A.U i) :
    ∃ r : ℕ, 0 < r ∧ ∀ (M : LB X) (hM : M.IsLB), cls M hM = r • cls L hL - cls A hA →
      ∃ s : M.Sec, nonzeroLocus t ≤ nonzeroLocus s := by
  have hA' := isLB_dual hA
  obtain ⟨N, u, hu⟩ := TwistGen.exists_sec_of_le_chart hA' hL 1 t.f
    (fun y j j' hj hj' => by rw [pow_one]; exact gs_compat t (𝟙 X) y hj hj')
    (nonzeroLocus t) (fun y j hj => mem_nonzeroLocus_iff_isUnit t hj) i hi
  obtain ⟨v, hv⟩ := TwistGen.exists_mul_pow (1 * N) 1 u t
  refine ⟨1 * N + 1, Nat.succ_pos _, fun M hM e => ?_⟩
  have hT := AbLaw.isLB_tw hA' hL ((1 * N + 1 : ℕ) : ℤ)
  have e' : cls _ hT = cls _ hA' - cls _ (AbLaw.isLB_pw hL (-((1 * N + 1 : ℕ) : ℤ))) :=
    cls_div hA' (AbLaw.isLB_pw hL _) _
  obtain ⟨s, hs⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hM hT ((cls_eq_iff hM hT).1 (by
    rw [e, e', AmpleStabFinite.cls_pw hL, cls_dual hA]
    module)) v
  exact ⟨s, fun y hy => hs.ge (hv ⟨hu hy, hy⟩)⟩

theorem nonzeroLocus_lbSecPull {X Y : Scheme.{0}} (L : LB X) (s : L.Sec) (f : Y ⟶ X) :
    nonzeroLocus (lbSecPull L s f) = f ⁻¹ᵁ nonzeroLocus s := Cartier.nonzeroLocus_secPull _ _

theorem exists_sec_of_common {N X X' : Scheme.{0}} [CompactSpace N] [QuasiSeparatedSpace N] (p : N ⟶ X) (p' : N ⟶ X')
    (hp : ∀ V, Function.Bijective (p.app V).hom) (n₀ : N)
    (hn : ∀ W : X.Opens, p n₀ ∈ W → ∃ W' : X'.Opens, p' n₀ ∈ W' ∧ p' ⁻¹ᵁ W' ≤ p ⁻¹ᵁ W)
    {ω : LB X} {ω' P B : LB X'} (hω : ω.IsLB) (hω' : ω'.IsLB) (hP : IsAmpleLB P) (hB : B.IsLB)
    (e : LBIso (ω.pull p) (ω'.pull p')) {k : ℕ} (hk : 0 < k) (ek : cls P hP.isLB + cls B hB = k • cls ω' hω')
    (b : B.Sec) (hb : p' n₀ ∈ nonzeroLocus b) {A : LB X} (hA : A.IsLB) :
    ∃ m : ℕ, 0 < m ∧ ∃ s : (LB.div (lbPow ω m) A).Sec, p n₀ ∈ nonzeroLocus s := by
  obtain ⟨i, hi⟩ := exists_chart hA (p n₀)
  obtain ⟨W', hW', hle⟩ := hn _ hi
  obtain ⟨n, hn, t, h₁, h₂, -⟩ := hP.exists_affine_le hW'
  have hT := isLB_tens hP.isLB hB
  obtain ⟨t', ht'⟩ := exists_sec_pow_nonzeroLocus_eq_inf hP.isLB hB hT
    ((cls_eq_iff hB (LB.isLB_div hT hP.isLB)).1 (by
      rw [cls_div hT hP.isLB, cls_tens hP.isLB hB]; abel)) t (secToPow b n)
  rw [nonzeroLocus_secToPow b hn] at ht'
  have hL := pull_isLB (isLB_lbPow hT n) p'
  obtain ⟨r, hr, H⟩ := exists_sec_div hL (pull_isLB hA p) (lbSecPull _ t' p') (fun _ => i) (by
    rw [nonzeroLocus_lbSecPull, ht', lb_pull_U]
    exact fun y hy => hle (h₂ hy.2))
  have hD := LB.isLB_div (isLB_lbPow hω (r * (n * k))) hA
  obtain ⟨s', hs'⟩ := H _ (pull_isLB hD p) (by
    have e' := (cls_eq_iff (pull_isLB hω p) (pull_isLB hω' p')).2 e
    rw [cls_pull hω, cls_pull hω'] at e'
    rw [cls_pull hD, cls_pull (isLB_lbPow hT n), cls_pull hA, cls_div (isLB_lbPow hω _) hA, cls_lbPow hω,
      cls_lbPow hT, cls_tens hP.isLB hB, ek, map_sub, map_nsmul, map_nsmul, map_nsmul, e', smul_smul, smul_smul,
      mul_assoc])
  obtain ⟨s, rfl⟩ := (bijective_lbSecPull p hp _).2 s'
  refine ⟨_, Nat.mul_pos hr (Nat.mul_pos hn hk), s, ?_⟩
  have := hs' (show n₀ ∈ _ by rw [nonzeroLocus_lbSecPull, ht']; exact ⟨hb, h₁⟩)
  rwa [nonzeroLocus_lbSecPull] at this

theorem bijective_app {U N X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (u : U ⟶ N) (p : N ⟶ X)
    [QuasiCompact u] [IsSchemeTheoreticallyDominant u] [UniversallyClosed p] [IsOpenImmersion (u ≫ p)]
    [IsDominant (u ≫ p)] (V : X.Opens) :
    Function.Bijective (p.app V).hom := by
  have : IsDominant p := .of_comp u p
  have : IsSchemeTheoreticallyDominant p := .of_isDominant p
  refine ⟨p.app_injective V, fun t => mem_range_app_of_forall_isAffineOpen p V t fun W hW _ => ?_⟩
  generalize N.presheaf.map _ t = t
  have ht : (p.app W).hom.IsIntegralElem t := GenPush.isIntegral_app_of_universallyClosed p W hW t
  have hs : ((u ≫ p).app W).hom.IsIntegralElem (u.app (p ⁻¹ᵁ W) t) := by
    change ((u.app (p ⁻¹ᵁ W)).hom.comp (p.app W).hom).IsIntegralElem _
    exact RingHom.IsIntegralElem.map ht _
  obtain ⟨h, hh⟩ := GenPush.exists_app_eq_of_isIntegralElem (u ≫ p) (u ≫ p).denseRange W _ hs
  refine ⟨h, u.app_injective (p ⁻¹ᵁ W) ?_⟩
  rw [← hh]
  rfl

theorem apply_eq_of_apply_eq {U N X X' : Scheme.{0}} [IsReduced N] [X.IsSeparated] (u : U ⟶ N) (p : N ⟶ X)
    (p' : N ⟶ X') [IsDominant u] [IsOpenImmersion (u ≫ p')] (n : N) (w : U) (h : p' n = (u ≫ p') w) :
    p n = (u ≫ p) w := by
  let O : N.Opens := p' ⁻¹ᵁ (u ≫ p').opensRange
  have h₁ : Set.range (O.ι ≫ p') ⊆ Set.range (u ≫ p') := by
    rintro _ ⟨z, rfl⟩
    exact z.2
  have h₂ : Set.range u ⊆ Set.range O.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨u z, z, rfl⟩, rfl⟩
  let q := IsOpenImmersion.lift (u ≫ p') (O.ι ≫ p') h₁
  let u' := IsOpenImmersion.lift O.ι u h₂
  have hq : q ≫ u ≫ p' = O.ι ≫ p' := IsOpenImmersion.lift_fac _ _ _
  have hu : u' ≫ O.ι = u := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant u' := ⟨by
    refine (u.denseRange.preimage O.ι.isOpenEmbedding.isOpenMap).mono ?_
    rintro z ⟨y, hy⟩
    refine ⟨y, O.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hu, hy]⟩
  have hid : u' ≫ q = 𝟙 U := by
    rw [← cancel_mono (u ≫ p'), Category.assoc, hq, reassoc_of% hu, Category.id_comp]
  have key : q ≫ u ≫ p = O.ι ≫ p := ext_of_isDominant u' (by rw [reassoc_of% hid, reassoc_of% hu])
  let z : O.toScheme := (⟨n, w, h.symm⟩ : O)
  have hz : q z = w := (u ≫ p').isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hq]; exact h)
  rw [← hz, ← Scheme.Hom.comp_apply q, key]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem j_s (Y : Model Xo c (RingHom.id c.F)) : Y.j ≫ Y.s = pullback.snd _ _ := by
  have h1 : spMap (RingHom.id c.F) = 𝟙 _ := by
    unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, h1, Category.comp_id]

theorem exists_common_modification (hE : GlobalTheory.Published.SemiAbelianHomExtension) (Y Y' : Model Xo c (RingHom.id c.F))
    (hY : (FlagMod.detOm Y).IsLB) (hY' : (FlagMod.detOm Y').IsLB) :
    ∃ (N : Scheme.{0}) (_ : CompactSpace N) (_ : QuasiSeparatedSpace N) (u : Xo.XF c ⟶ N) (p : N ⟶ Y.X) (p' : N ⟶ Y'.X),
      u ≫ p = Y.j ∧ u ≫ p' = Y'.j ∧ (∀ V, Function.Bijective (p.app V).hom) ∧ (∀ n w, p' n = Y'.j w → p n = Y.j w) ∧
      LBIso ((FlagMod.detOm Y).pull p) ((FlagMod.detOm Y').pull p') := by
  have := c.fin
  have := Y.flat
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y'.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : AlgebraicGeometry.IsNoetherian Y.X := {}
  have := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have : Y.X.IsSeparated := ⟨by rw [← terminal.comp_from Y.s]; infer_instance⟩
  have : IsDominant Y.j := ⟨LogKS.dense_interior Y⟩
  have : QuasiCompact Y.j := inferInstance
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := GlobalTheory.IsNormalScheme.of_isIso_stalkMap Y.j
  have : IsLocallyNoetherian (Xo.XF c) := isLocallyNoetherian_of_isOpenImmersion Y.j
  let f : Xo.XF c ⟶ pullback Y.s Y'.s := pullback.lift Y.j Y'.j ((j_s Y).trans (j_s Y').symm)
  have hf₁ : f ≫ pullback.fst Y.s Y'.s = Y.j := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd Y.s Y'.s = Y'.j := pullback.lift_snd _ _ _
  have : IsImmersion (f ≫ pullback.fst Y.s Y'.s) := hf₁ ▸ inferInstance
  have : QuasiCompact (f ≫ pullback.fst Y.s Y'.s) := hf₁ ▸ inferInstance
  have : IsImmersion f := .of_comp f (pullback.fst Y.s Y'.s)
  have : QuasiCompact f := .of_comp f (pullback.fst Y.s Y'.s)
  have : Flat (f ≫ pullback.fst Y.s Y'.s ≫ Y.s) := by
    rw [reassoc_of% hf₁]; infer_instance
  have : IsFinite f.fromNormalization := AmpUniq.isFinite_fromNormalization_graph f (pullback.fst Y.s Y'.s ≫ Y.s)
  let u := f.toNormalization
  let p := f.fromNormalization ≫ pullback.fst Y.s Y'.s
  let p' := f.fromNormalization ≫ pullback.snd Y.s Y'.s
  have hu₁ : u ≫ p = Y.j := by simp [u, p, hf₁]
  have hu₂ : u ≫ p' = Y'.j := by simp [u, p', hf₂]
  have : IsOpenImmersion u := inferInstance
  have hN := GlobalTheory.IsNormalScheme.pred f.normalization
  have : IsLocallyNoetherian f.normalization := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace f.normalization := QuasiCompact.compactSpace_of_compactSpace p
  have : AlgebraicGeometry.IsNoetherian f.normalization := {}
  have : IsOpenImmersion (u ≫ p) := hu₁ ▸ inferInstance
  have : IsDominant (u ≫ p) := hu₁ ▸ inferInstance
  have : IsOpenImmersion (u ≫ p') := hu₂ ▸ inferInstance
  refine ⟨f.normalization, inferInstance, inferInstance, u, p, p', hu₁, hu₂, bijective_app u p,
    fun n w h => hu₁ ▸ apply_eq_of_apply_eq u p p' n w (hu₂ ▸ h), ?_⟩
  obtain ⟨_, _, _, _, _, n₁, -⟩ := sabPull Out.CubePf.cubePull p Y.t
  obtain ⟨_, _, _, _, _, n₂, -⟩ := sabPull Out.CubePf.cubePull p' Y'.t
  obtain ⟨m₀, -⟩ := ObjMaps.exists_sab_cancel (g := 𝟙 _) Y'.m0.toSABMap
    (by rw [Category.id_comp]; exact Y.m0.toSABMap : SABMap Y.oF.t Xo.univ.t (𝟙 _ ≫ pullback.fst _ _))
  obtain ⟨m₂, -⟩ := ObjMaps.exists_sab_comp Y'.m m₀
  obtain ⟨a₁, -⟩ := ObjMaps.exists_sab_cancel n₁ (hu₁ ▸ Y.m : SABMap Y.oF.t Y.t (u ≫ p))
  obtain ⟨a₂, -⟩ := ObjMaps.exists_sab_cancel n₂
    ((((Category.id_comp _).trans hu₂.symm : 𝟙 _ ≫ Y'.j = u ≫ p')) ▸ m₂ : SABMap Y.oF.t Y'.t (u ≫ p'))
  obtain ⟨e, ⟨_, -⟩, -⟩ := hE.existsUnique_iso_of_extensions hN (IsSemiAbelian.pullback p Y.t.G Y.t.semi)
    (IsSemiAbelian.pullback p' Y'.t.G Y'.t.semi) a₁.cart a₂.cart
  have h₂ := ((isGrpPullback_of_iso e).comp n₂.cart).congr (Category.id_comp _) rfl
  have hdet := PolExt.lbIso_detLie_pull (G := (Over.pullback p).obj Y.t.G) n₁.cart h₂ fun U U' hU hU' =>
    (PolExt.isAffineOpen_snd_inf_fst Y.s Y'.s hU' hU).preimage f.fromNormalization
  have hL : (FlagMod.detLie Y).IsLB :=
    FlagMod.isLB_of_ev _ hY.cover fun i j k _ _ z => FlagMod.ev_detChg_mul i j k z
  have hL' : (FlagMod.detLie Y').IsLB :=
    FlagMod.isLB_of_ev _ hY'.cover fun i j k _ _ z => FlagMod.ev_detChg_mul i j k z
  have e₁ := (cls_eq_iff (pull_isLB hL p) (pull_isLB hL' p')).2 hdet
  rw [cls_pull hL, cls_pull hL'] at e₁
  refine (cls_eq_iff (pull_isLB hY p) (pull_isLB hY' p')).1 ?_
  rw [cls_pull hY, cls_pull hY', show cls _ hY = _ from cls_dual hL hY, show cls _ hY' = _ from cls_dual hL' hY',
    map_neg, map_neg, e₁]

end GlobalTheory.HodgeDominates
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullDegTraitAndBaseUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CommonPull

open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

theorem exists_rig_iso_of_eq {S : Scheme.{0}} {H : Over S} [GrpObj H] (L₁ L₂ : RigLB H) (h : L₁ = L₂) :
    ∃ w : LB.Iso L₂.L L₁.L, w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec H) (fun _ => 1)) L₂.rig L₁.rig := by
  subst h
  exact ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso L₁.L, idIso_isGen L₁.isLB, fun p => L₁.rigGen p.1 p.2⟩

theorem exists_common_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → UnifTrait D G L →
    ∀ (D₂ : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U₂ : Unif (maximalIdeal R) D₂ A G),
    U₂.LG.L = L → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (φ : R →+* W) (D' : DegPre W),
      Function.Injective φ ∧ Nonempty (IsPullDeg φ D.toPre D') ∧ Nonempty (IsPullDeg φ D₂.toPre D') := by
  intro R _ _ _ hR D G _ _ L _ hG hT D₂ A U₂ hL
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, hφ, hloc, hβ, hLβ, hD⟩ := hT
  subst hL
  obtain ⟨hLw, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have h6 := GlobalTheory.sixthLaws_and_unifUniq.2
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hβ (isGrpPullback_pullback G (spMap φ))
  haveI := mbc
  have hG' : IsSemiAbelian G' := GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap φ) G hG)

  have sq : spMap (fracMap hφ) ≫ jK R = jK W ≫ spMap φ := (fracMap_sq hφ).symm.trans (Category.id_comp _)
  obtain ⟨A'', gA, pA, dA, mA, tA⟩ := hLw.polBaseChange _ _ (spMap (fracMap hφ)) A
  have gpA : IsGrpPullback A''.A A.A (spMap (fracMap hφ)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U₂.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK W)).obj G') G (spMap (fracMap hφ) ≫ jK R)
      (pullback.fst G'.hom (jK W) ≫ β) :=
    ((isGrpPullback_pullback G' (jK W)).comp hβ).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U₂.gen.inv.left ≫ U₂.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A''.L.pull eA.hom.left) (U₂.LG.L.pull (pullback.fst G'.hom (jK W) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ))) := by
    refine LBIso.trans (pull_isLB A''.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U₂.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A''.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U₂.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U₂.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U₂.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U₂.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · show pullback.fst G'.hom (jK W) ≫ bc.hom.left ≫ pullback.fst G.hom (spMap φ) = _
      rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G := by
    show eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (spMap φ) = _
    rw [hbc]; exact (cubeMapOf hβ).e_comm
  obtain ⟨wL, gwL, rwL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf φ) G G'
    (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) he U₂.LG U'.LG (by
      show ∃ w : LB.Iso U'.LG.L (U₂.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (spMap φ))), w.IsGen
      rw [hbc]; exact hLβ)
  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R (maximalIdeal R) hR.1 D₂
  have hgen : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) ∈ Wo := by
    have : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective φ hφ)
    rw [this]; exact hWo
  obtain ⟨D₂', hD₂, U₂', hLG, -, -⟩ := h4.unifBaseChange R W (maximalIdeal R) (maximalIdeal W) hR.1 hW' φ
    (map_maximalIdeal_le φ) D₂ A G hG U₂ Wo hψ hgen G' bc mbc A'' dA eA mE wA U'.LG wL he gwL rwL
  obtain ⟨wU, gU, rU⟩ := exists_rig_iso_of_eq U₂'.LG U'.LG hLG
  obtain ⟨hU, -⟩ := h6 W (maximalIdeal W) hW' D₂' D' A'' A' G' hG' U₂' U' wU gU rU
  obtain ⟨hD'⟩ := hD
  refine ⟨W, inferInstance, inferInstance, φ, D'.toPre, hφ, ⟨hD'⟩, ?_⟩
  exact RingHom.id_comp φ ▸ GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hφ Function.injective_id hD₂ hU

end GlobalTheory.Mum.CommonPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackFractionFieldFiniteLocalExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.CommonCover

theorem exists_cover_field (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (K' : Type) [Field K']
    (io : FractionRing R →+* K') (hfin : io.Finite) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (τ : K' →+* FractionRing R'),
      FinExt ρ ∧ IsLocalHom ρ ∧ τ.comp (io.comp (algebraMap R (FractionRing R))) = (algebraMap R' (FractionRing R')).comp ρ := by
  obtain ⟨⟨hN, -, hIC, hC⟩, hc0⟩ := hR
  letI : Algebra (FractionRing R) K' := io.toAlgebra
  letI : Algebra R K' := (io.comp (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional (FractionRing R) K' := hfin
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : Algebra.IsSeparable (FractionRing R) K' := inferInstance
  let C := integralClosure R K'
  haveI : Module.Finite R C := IsIntegralClosure.finite R (FractionRing R) K' C
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension (FractionRing R) K'
  have hφ : Function.Injective (algebraMap R C) := fun a b h => by
    have h' : io (algebraMap R (FractionRing R) a) = io (algebraMap R (FractionRing R) b) := congrArg Subtype.val h
    exact IsFractionRing.injective R (FractionRing R) (io.injective h')
  obtain ⟨R', _, _, _, ρ, σ, hCN, hρ, hfin', hloc, hσ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (algebraMap R C) ⟨hN, hIC, hC, hc0⟩ hφ (RingHom.finite_algebraMap.2 inferInstance)
  have hσi : Function.Injective σ := by
    refine (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := R) ?_)
    rw [RingHom.comap_ker, hσ]
    exact (RingHom.injective_iff_ker_eq_bot ρ).1 hρ
  have hg : Function.Injective ((algebraMap R' (FractionRing R')).comp σ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hσi
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, IsFractionRing.lift (A := C) hg,
    ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hρ, hfin'⟩, hloc, ?_⟩
  ext r
  have e : io (algebraMap R (FractionRing R) r) = algebraMap C K' (algebraMap R C r) := rfl
  simp only [RingHom.comp_apply]
  rw [e, IsFractionRing.lift_algebraMap, RingHom.comp_apply, ← RingHom.comp_apply σ, hσ]

theorem exists_common_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegPre R) (E₁ E₂ : DegPre (FractionRing R)), IsPullDeg (algebraMap R (FractionRing R)) D₁ E₁ → IsPullDeg (algebraMap R (FractionRing R)) D₂ E₂ → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (E₃ : DegPre K'), io.Finite → IsPullDeg io E₁ E₃ → IsPullDeg io E₂ E₃ → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (E : DegPre (FractionRing R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) := by
  intro R _ _ _ hR D₁ D₂ E₁ E₂ p₁ p₂ K' _ io E₃ hfin q₁ q₂
  obtain ⟨R', _, _, _, ρ, τ, hE, hloc, hτ⟩ := exists_cover_field R hR K' io hfin
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨E, t, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hL.polBaseChange K' (FractionRing R') τ E₃ ⊤
    (GlobalTheory.FieldPull.nonempty_psiOn_field E₃) trivial
  have ha : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hio : Function.Injective (io.comp (algebraMap R (FractionRing R))) := io.injective.comp ha
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, E, hE, hloc, ?_, ?_⟩
  · obtain ⟨a⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp ha io.injective p₁ q₁
    rw [← hτ]
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hio τ.injective a t
  · obtain ⟨a⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp ha io.injective p₂ q₂
    rw [← hτ]
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hio τ.injective a t

end GlobalTheory.CommonCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleMapsModPowMaximalIdealBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_maximalIdeal_pow_le_map_maximalIdeal (R : Type) [CommRing R] [IsLocalRing R]
    (R' : Type) [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R']
    [Module.Finite R R'] :
    ∃ N : ℕ, maximalIdeal R' ^ N ≤ (maximalIdeal R).map (algebraMap R R') := by
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hIP, hP⟩
    haveI := hP
    have hc : P.comap (algebraMap R R') = maximalIdeal R := by
      apply le_antisymm
      · exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap (algebraMap R R')).ne_top
      · exact Ideal.map_le_iff_le_comap.1 hIP
    have hmax : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P (by rw [hc]; infer_instance)
    exact (IsLocalRing.eq_maximalIdeal hmax).ge
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg _
    (IsNoetherian.noetherian ((maximalIdeal R).map (algebraMap R R')).radical)
  exact ⟨n, (Ideal.pow_right_mono hrad n).trans hn⟩

theorem exists_compatible_maps_mod_pow_maximalIdeal_base : ∀ (R : Type) [CommRing R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R'] [Module.Finite R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (Γ : Type) (actC : Γ → (C' ≃ₐ[R] C')) (O : Type) [CommRing O] [Algebra R O] (i' : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')), (∀ e x y, Ideal.Quotient.mk _ y = i' (e + 1) x → Ideal.Quotient.mk _ y = i' e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i' e x → Ideal.Quotient.mk _ (actC σ y) = i' e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i' e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i' e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R' ^ (e + 1)).map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R')) → ∃ i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C'), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) ∧ (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (actC σ y) = i e x) ∧ (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) := by
  intro R _ _ R' _ _ _ _ _ C' _ _ _ _ Γ actC O _ _ i' hcomp hinv hsk
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_map_maximalIdeal R R'
  have hR' : ∀ e : ℕ, maximalIdeal R' ^ (N * (e + 1) + 1) ≤
      (maximalIdeal R ^ (e + 1)).map (algebraMap R R') := by
    intro e
    calc maximalIdeal R' ^ (N * (e + 1) + 1) ≤ maximalIdeal R' ^ (N * (e + 1)) :=
          Ideal.pow_le_pow_right (Nat.le_succ _)
      _ = (maximalIdeal R' ^ N) ^ (e + 1) := pow_mul _ _ _
      _ ≤ ((maximalIdeal R).map (algebraMap R R')) ^ (e + 1) := Ideal.pow_right_mono hN _
      _ = _ := (Ideal.map_pow _ _ _).symm
  have hle : ∀ e : ℕ, (maximalIdeal R' ^ (N * (e + 1) + 1)).map (algebraMap R' C') ≤
      (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
    intro e
    rw [Ideal.map_le_iff_le_comap]
    refine (hR' e).trans ?_
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp only [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact Ideal.mem_map_of_mem _ hr
  have hJ : ∀ e : ℕ, (maximalIdeal R ^ (e + 1 + 1)).map (algebraMap R C') ≤
      (maximalIdeal R ^ (e + 1)).map (algebraMap R C') :=
    fun e => Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))
  have hiter : ∀ a b : ℕ, a ≤ b → ∀ x y,
      Ideal.Quotient.mk ((maximalIdeal R' ^ (b + 1)).map (algebraMap R' C')) y = i' b x →
      Ideal.Quotient.mk ((maximalIdeal R' ^ (a + 1)).map (algebraMap R' C')) y = i' a x := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact fun x y h => h
    | succ b _ ih => exact fun x y h => ih x y (hcomp b x y h)
  let i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') :=
    fun e => (Ideal.Quotient.factorₐ R (hle e)).comp (i' (N * (e + 1)))
  have hi : ∀ e x, i e x = Ideal.Quotient.factorₐ R (hle e) (i' (N * (e + 1)) x) :=
    fun _ _ => rfl
  have hlift : ∀ e x y, Ideal.Quotient.mk ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')) y
      = i e x → ∃ y', Ideal.Quotient.mk ((maximalIdeal R' ^ (N * (e + 1) + 1)).map
        (algebraMap R' C')) y' = i' (N * (e + 1)) x ∧
        y - y' ∈ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
    intro e x y h
    obtain ⟨y', hy'⟩ := Ideal.Quotient.mk_surjective (i' (N * (e + 1)) x)
    refine ⟨y', hy', ?_⟩
    rw [← Ideal.Quotient.eq, h, hi, ← hy', Ideal.Quotient.factorₐ_apply_mk]
  refine ⟨i, ?_, ?_, ?_⟩
  · intro e x y h
    obtain ⟨y', hy', hd⟩ := hlift (e + 1) x y h
    have h2 := hiter (N * (e + 1)) (N * (e + 1 + 1)) (Nat.mul_le_mul_left _ (Nat.le_succ _)) x y' hy'
    rw [Ideal.Quotient.eq.2 (hJ e hd), hi, ← h2, Ideal.Quotient.factorₐ_apply_mk]
  · intro e σ x y h
    obtain ⟨y', hy', hd⟩ := hlift e x y h
    have hst : (maximalIdeal R ^ (e + 1)).map (algebraMap R C') ≤
        ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')).comap (actC σ) := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, AlgEquiv.commutes]
      exact Ideal.mem_map_of_mem _ hr
    have hσ : actC σ y - actC σ y' ∈ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
      rw [← map_sub]; exact hst hd
    rw [Ideal.Quotient.eq.2 hσ, hi, ← hinv (N * (e + 1)) σ x y' hy', Ideal.Quotient.factorₐ_apply_mk]
  · intro e
    obtain ⟨hsur, hker⟩ := hsk (N * (e + 1))
    set L' := Algebra.TensorProduct.lift (i' (N * (e + 1)))
      ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _
      with hL'
    have hfac : Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _)
        = (Ideal.Quotient.factorₐ R (hle e)).comp L' := by
      apply Algebra.TensorProduct.ext'
      intro a b
      rw [AlgHom.comp_apply, hL', Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
        map_mul, hi]
      congr 1
    rw [hfac]
    refine ⟨?_, ?_⟩
    · intro z
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨t, ht⟩ := hsur (Ideal.Quotient.mk _ c)
      exact ⟨t, by simp [ht, Ideal.Quotient.factorₐ_apply_mk]⟩
    apply le_antisymm
    · intro t ht
      rw [RingHom.mem_ker, AlgHom.comp_apply] at ht
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (L' t)
      have hcJ : c ∈ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.factorₐ_apply_mk R (hle e), hc]
        exact ht
      have hsub : (maximalIdeal R ^ (e + 1)).map (algebraMap R C') ≤
          (((maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))).map L').comap
            (Ideal.Quotient.mk ((maximalIdeal R' ^ (N * (e + 1) + 1)).map (algebraMap R' C'))) := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        simp only [Ideal.mem_comap, Ideal.Quotient.mk_algebraMap]
        rw [← AlgHom.commutes L' r]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr)
      have hmem := hsub hcJ
      rw [Ideal.mem_comap, hc] at hmem
      obtain ⟨t', ht'K, ht'⟩ := (Ideal.mem_map_iff_of_surjective L' hsur).1 hmem
      have hdiff : t - t' ∈ RingHom.ker L' := by
        rw [RingHom.mem_ker, map_sub, ht', sub_self]
      rw [hker] at hdiff
      have hKK : (maximalIdeal R' ^ (N * (e + 1) + 1)).map
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R') ≤
          (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R')) := by
        rw [Ideal.map_le_iff_le_comap]
        refine (hR' e).trans ?_
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        simp only [Ideal.mem_comap, AlgHom.commutes]
        exact Ideal.mem_map_of_mem _ hr
      simpa using Ideal.add_mem _ (hKK hdiff) ht'K
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
      rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hr

end GlobalTheory
end

