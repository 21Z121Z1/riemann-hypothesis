import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0215
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3167
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0420
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3156
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0645
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationMovesAlongDvrInjectionGivenFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.UnifMoveGiven

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear GlobalTheory.UnifMove in

theorem exists_pull_given {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
    {I' : Ideal R'} (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g)
    (hI : I.map g ≤ I') (gK : FractionRing R →+* FractionRing R') (sq : spMap gK ≫ jK R = jK R' ≫ spMap g)
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G)
    (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (gA : A'.A.left ⟶ A.A.left)
    (gpA : IsGrpPullback A'.A A.A (spMap gK) gA) (hL : LBIso A'.L (A.L.pull gA)) (dA : A'.g = A.g) :
    ∃ (D' : DegData R' I') (hD : IsPullDeg g D.toPre D'.toPre)
      (U' : Unif I' D' A' ((Over.pullback (specOf g)).obj G)),
      IsPullUnif g hD (Iso.refl _) U U' ∧
      U'.gen.hom.left ≫ gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
        pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g) := by
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap gK ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = pullback.fst G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      (hL.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec ((Over.pullback (specOf g)).obj G))
      (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) := ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
    rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, hgenU, hPU⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, U', hPU, by rw [hgenU]; exact heA⟩

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear GlobalTheory.UnifMove in

theorem move_given : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → ∀ (φ : V →+* V') (φK : FractionRing V →+* FractionRing V'), φK.comp (algebraMap V _) = (algebraMap V' _).comp φ → (maximalIdeal V).map φ ≤ maximalIdeal V' → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (A' : PolAV (Sp (FractionRing V'))) (ψ : A'.A.left ⟶ A.A.left), IsGrpPullback A'.A A.A (spMap φK) ψ → LBIso A'.L (A.L.pull ψ) → A'.g = A.g → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing V') F], (algebraMap (FractionRing V') F).comp φK = algebraMap (FractionRing V) F → ∃ (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg φ D.toPre D'.toPre) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal V') D' A' G'), IsSemiAbelian G' ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (q : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), QkToAkU U.toUnifPre F k q x → ∃ (q' : QkPt D'.toPre F k) (x' : TFK (R := V') F ⟶ A'.A), hD.xe q'.y = q.y ∧ x'.left ≫ ψ = x.left ∧ QkToAkU U'.toUnifPre F k q' x' := by
  intro V V' _ _ _ _ _ _ hV hV' φ φK hK hI D A G _ _ U A' ψ gp hL hg F _ _ _ hF
  have aV : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have aV' : AdmBase V' (IsLocalRing.maximalIdeal V') := ⟨inferInstance, inferInstance, inferInstance, hV'⟩
  have hK' : ∀ r, φK (algebraMap V _ r) = algebraMap V' _ (φ r) := fun r => RingHom.congr_fun hK r
  have hφ : Function.Injective φ := fun a b h =>
    IsFractionRing.injective V (FractionRing V) (φK.injective (by rw [hK', hK', h]))
  have sq : spMap φK ≫ jK V = jK V' ≫ spMap φ := by
    refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hK
  have hFc : ∀ r : V, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) r) =
      algebraMap (FractionRing V') F (algebraMap V' (FractionRing V') (φ r)) := fun r => by
    rw [← hK', ← hF]; rfl
  have sF : jFK (R := V') F ≫ spMap φK = jFK (R := V) F := by
    refine (Spec.map_comp _ _).symm.trans ?_
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hF
  obtain ⟨D', hD, U', hU, hgen⟩ := exists_pull_given aV aV' φ hφ hI φK sq
    (isSemiAbelian_of_unifPre_dvr V D A G U.toUnifPre) U A' ψ gp hL hg
  refine ⟨D', hD, _, inferInstance, inferInstance, U',
    isSemiAbelian_of_unifPre_dvr V' D' A' _ U'.toUnifPre, fun k hk q x H => ?_⟩
  obtain ⟨τ, hτ, -⟩ := exists_qk_pull_equiv abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 V V' φ D.toPre D'.toPre hD
    D.tau_bimult D'.tau_bimult F hFc k
  obtain ⟨hy, hg'⟩ := (hτ q _).1 rfl
  have w : x.left ≫ A.A.hom = jFK (R := V') F ≫ spMap φK := (Over.w x).trans sF.symm
  let x' : TFK (R := V') F ⟶ A'.A := Over.homMk (gp.1.lift x.left (jFK (R := V') F) w) (gp.1.lift_snd _ _ _)
  have hx : x'.left ≫ ψ = x.left := gp.1.lift_fst _ _ _
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  refine ⟨τ q, x', by rw [hy]; exact hD.xe.apply_symm_apply _, hx,
    qkToAk_baseChange abelianSchemeLaws_all.1.globalFns abelianSchemeLaws_all.1.secBaseChange V V' _ _ aV aV' φ D A G U
      _ (Iso.refl _) mR A' D' hD U' hU F hFc k hk q x (τ q) x' hy hg' ?_ H⟩
  have n : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst G.hom (spMap φ) := Category.id_comp _
  rw [hbc, ← hgen, ← Category.assoc U'.gen.inv.left, n, Category.id_comp, ← Category.assoc, hx]

end GlobalTheory.UnifMoveGiven

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionNearClosedFibreDescendsToBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnitDescent

theorem one_left_pullback {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] :
    (1 : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f =
      f ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by
  rw [Hom.one_def, Hom.one_def]
  erw [Functor.obj.η_def]
  have hw : (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
      pullback.snd (𝟙_ (Over S)).hom f = 𝟙 T := by
    simpa using Over.w (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f))
  have hb : (toUnit (Over.mk (𝟙 S))).left = 𝟙 S := by
    simpa using Over.w (toUnit (Over.mk (𝟙 S)))
  have hc : pullback.fst (𝟙_ (Over S)).hom f = pullback.snd (𝟙_ (Over S)).hom f ≫ f := by
    have := pullback.condition (f := (𝟙_ (Over S)).hom) (g := f)
    simpa using this
  have hm : ((Over.pullback f).map (η : 𝟙_ (Over S) ⟶ G)).left ≫ pullback.fst G.hom f =
      pullback.fst (𝟙_ (Over S)).hom f ≫ (η : 𝟙_ (Over S) ⟶ G).left := by
    simp only [Over.pullback_map_left]
    erw [pullback.lift_fst]
  simp only [Over.comp_left, Category.assoc] at hw ⊢
  rw [hm, hc, hb]
  simp only [← Category.assoc] at hw ⊢
  rw [hw]
  simp

theorem unit_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u → ∃ e : Sp R ⟶ N.U.left, e ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hSA N hL hr
  haveI : IsNoetherianRing R := hA.1
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI := N.isOpen
  have hone_w : (1 : Over.mk (𝟙 S) ⟶ G').left ≫ G'.hom = 𝟙 S := by
    simpa using Over.w (1 : Over.mk (𝟙 S) ⟶ G')
  let x₀ := IsOpenImmersion.lift N.u (1 : Over.mk (𝟙 S) ⟶ G').left hr
  have hx₀u : x₀ ≫ N.u = (1 : Over.mk (𝟙 S) ⟶ G').left := IsOpenImmersion.lift_fac _ _ _
  have hx₀s : x₀ ≫ pullback.snd N.U.hom π = 𝟙 S := by
    rw [← N.u_over, ← Category.assoc, hx₀u, hone_w]
  let h := x₀ ≫ pullback.fst N.U.hom π
  have hh : h ≫ N.U.hom = π := by
    simp only [h, Category.assoc, pullback.condition]
    rw [← Category.assoc, hx₀s]
    simp
  obtain ⟨φ, hmon, hφ⟩ := GlobalTheory.T.exists_descentDatum_of_descendedMultiplication R hA S π hP hS hI G' hSA N hL
  let x := (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G').left
  have hxs : x ≫ pullback.snd G'.hom (pullback.fst π π) = 𝟙 _ := by
    simpa using Over.w (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G')
  have hxf : x ≫ pullback.fst G'.hom (pullback.fst π π) = pullback.fst π π ≫ (1 : Over.mk (𝟙 S) ⟶ G').left :=
    one_left_pullback _ _
  have hφ1 : x ≫ φ.hom.left =
      (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.snd π π)).obj G').left := by
    rw [← Over.comp_left]
    congr 1
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have hprem : N.Pt (x ≫ pullback.snd G'.hom (pullback.fst π π) ≫ pullback.fst π π) (pullback.fst π π ≫ h)
      (x ≫ pullback.fst G'.hom (pullback.fst π π)) := by
    rw [reassoc_of% hxs, hxf]
    exact ⟨pullback.fst π π ≫ x₀, by simp [h], by rw [Category.assoc, hx₀s, Category.comp_id],
      by rw [Category.assoc, hx₀u]⟩
  obtain ⟨y₀, hy1, -, hy3⟩ := hφ _ _ x hprem
  rw [← Category.assoc, hφ1, one_left_pullback] at hy3
  have hy : y₀ = pullback.snd π π ≫ x₀ := by
    rw [← cancel_mono N.u, hy3, Category.assoc, hx₀u]
  have heq : pullback.fst π π ≫ h = pullback.snd π π ≫ h := by
    rw [← hy1, hy, Category.assoc]
  have sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π := IsPullback.of_vert_isIso ⟨by simp⟩
  obtain ⟨e, he, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S N.U.left π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq h heq
  obtain ⟨e₁, -, huniq⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S (Sp R) π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq π
    pullback.condition
  refine ⟨e, ?_, x₀, he.symm, hx₀s, hx₀u⟩
  rw [huniq (e ≫ N.U.hom) (show π ≫ e ≫ N.U.hom = π by rw [← Category.assoc, he, hh]),
    huniq (𝟙 _) (show π ≫ 𝟙 _ = π by simp)]

end GlobalTheory.UnitDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFormTensorRangeLeUnitaryAutFormsWeightLeve
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer.RangeLe

theorem contW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (u : Wsp lam) (ℓ : Module.Dual ℂ (Wsp lam)), Continuous fun g : UA E n => ℓ (wInf lam g u) := GlobalTheory.T.continuous_matrixCoeff_infinitePlacesWeightRep

theorem ratSplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ γ ∈ ratU E n, ∃ γ₀ : UE E n, splitFin E n γ = finPt γ₀ ∧ ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1 := GlobalTheory.T.definiteUnitaryRationalPoint_split_finite_infinite

theorem spanW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), Submodule.span ℂ (Set.range ((wInf lam).comp (infU E n).subtype)) = ⊤ := GlobalTheory.T.span_realPoints_weightRepresentation_eq_top

theorem semis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ (K : Subgroup (finU E n)), IsOpen (K : Set (finU E n)) → ∀ f : W →ₗ[ℂ] (UA E n → ℂ), (∀ u, IsAutFormU (f u)) → (∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u)) → (∀ u, f u ∈ fixed (RF E n) K) → ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := GlobalTheory.T.fixedVectorForm_values_mem_iSup_fixedParts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def dualW (lam : InfinitePlace E → DomWeight n) : UA E n →* Module.End ℂ (Module.Dual ℂ (Wsp lam)) where
  toFun g := (wInf lam g⁻¹).dualMap
  map_one' := by
    refine LinearMap.ext fun φ => LinearMap.ext fun w => ?_
    simp [LinearMap.dualMap_apply]
  map_mul' a b := by
    refine LinearMap.ext fun φ => LinearMap.ext fun w => ?_
    simp [LinearMap.dualMap_apply, _root_.mul_inv_rev, map_mul]

theorem dualW_apply (lam : InfinitePlace E → DomWeight n) (g : UA E n) (φ : Module.Dual ℂ (Wsp lam)) (w : Wsp lam) :
    dualW lam g φ w = φ (wInf lam g⁻¹ w) := rfl

theorem wInf_inv_rat (lam : InfinitePlace E → DomWeight n) (γ : UA E n) (γ₀ : UE E n)
    (h : ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1) :
    wInf lam γ⁻¹ = wAt lam γ₀⁻¹ := by
  have e : ∀ v : InfinitePlace E, cEmb v.embedding γ⁻¹ = GeneralLinearGroup.map v.embedding (γ₀⁻¹ : UE E n).1 :=
    fun v => by rw [map_inv, h v, InvMemClass.coe_inv, map_inv]
  unfold wInf wAt
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, e]

theorem phiFun_wInf (lam : InfinitePlace E → DomWeight n) (F : finU E n → Module.Dual ℂ (Wsp lam)) (x : infU E n)
    (w : Wsp lam) : phiFun lam F (wInf lam x.1 w) = RU E n x.1 (phiFun lam F w) := by
  funext g
  change F (splitFin E n g) (wInf lam g (wInf lam x.1 w)) = F (splitFin E n (g * x.1)) (wInf lam (g * x.1) w)
  rw [map_mul (splitFin E n), splitFin_inf x, mul_one, map_mul (wInf lam), Module.End.mul_apply]

theorem phiFun_mem_fixed (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (F : finU E n → Module.Dual ℂ (Wsp lam)) (hF : F ∈ vecM S lam K') (w : Wsp lam) :
    phiFun lam F w ∈ fixed (RF E n) (globLev S K') := by
  intro k
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  funext g
  change phiFun lam F w (g * ((k : finU E n) : UA E n)) = phiFun lam F w g
  rw [phiFun_mul_fin]
  have e : rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam)) (k : finU E n) F = F := funext fun x => hF.2 k k.2 x
  rw [e]

theorem isAutFormU_phiFun (hU : Unr E) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n)
    (K' : ∀ w : Pl E, Subgroup (UL n w)) (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K')
    (F : finU E n → Module.Dual ℂ (Wsp lam)) (hF : F ∈ vecM S lam K') (w : Wsp lam) :
    IsAutFormU (phiFun lam F w) := by
  have hfin : ∀ k ∈ finU E n, dualW lam k = 1 := by
    intro k hk
    refine LinearMap.ext fun φ => LinearMap.ext fun u => ?_
    rw [dualW_apply, wInf_fin lam ⟨k⁻¹, (finU E n).inv_mem hk⟩]
    rfl
  have hcont : ∀ (u : Module.Dual ℂ (Wsp lam)) (ℓ : Module.Dual ℂ (Module.Dual ℂ (Wsp lam))),
      Continuous fun g => ℓ (dualW lam g u) := by
    intro u ℓ
    obtain ⟨w', rfl⟩ := (Module.evalEquiv ℂ (Wsp lam)).surjective ℓ
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, dualW_apply]
    exact (contW E n lam w' u).comp continuous_inv
  have hinf : ∀ y ∈ infU E n, ∀ g, (fun g => F (splitFin E n g)) (g * y) = F (splitFin E n g) := by
    intro y hy g
    simp only [map_mul, splitFin_inf ⟨y, hy⟩, mul_one]
  have hrat : ∀ γ ∈ ratU E n, ∀ g, (fun g => F (splitFin E n g)) (γ * g) = dualW lam γ (F (splitFin E n g)) := by
    intro γ hγ g
    obtain ⟨γ₀, h1, h2⟩ := ratSplit E n γ hγ
    simp only [map_mul, h1]
    rw [hF.1 γ₀ (splitFin E n g)]
    refine LinearMap.ext fun u => ?_
    rw [dualW_apply, wInf_inv_rat lam γ γ₀ h2]
    rfl
  have hsm : ∀ᶠ y in 𝓝 (1 : UA E n), ∀ g, (fun g => F (splitFin E n g)) (g * y) = F (splitFin E n g) := by
    have ho : IsOpen ((splitFin E n) ⁻¹' (globLev S K' : Set (finU E n))) :=
      (isOpen_globLev E hU n S K' hK).preimage continuous_splitFin
    filter_upwards [ho.mem_nhds (by simp [(globLev S K').one_mem])] with y hy g
    simp only [map_mul]
    exact hF.2 _ hy _
  have h := GlobalTheory.EquivCoef.isAutFormU_coef E n (Module.Dual ℂ (Wsp lam)) (dualW lam) (fun g => F (splitFin E n g))
    hfin hcont hinf hrat hsm (Module.Dual.eval ℂ (Wsp lam) w)
  convert h using 1
  funext g
  simp [dualW_apply]

theorem hasWeightAt_of_wInf (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ))
    (f' : Wsp lam →ₗ[ℂ] (UA E n → ℂ)) (h0 : f' ≠ 0) (hπ : ∀ u, f' u ∈ π)
    (heq : ∀ (x : infU E n) u, f' (wInf lam x.1 u) = RU E n x.1 (f' u)) (v : InfinitePlace E) :
    HasWeightAt π v.embedding (lam v) := by
  obtain ⟨e, he⟩ : ∃ e : ∀ v, nablaSq ℂ n (lam v), f' (PiTensorProduct.tprod ℂ e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (PiTensorProduct.ext (MultilinearMap.ext fun e => by simpa using hc e))
  refine ⟨GlobalTheory.DefU.isIrreducible_sqRep n (lam v), f' ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap e v, ?_,
    fun a => hπ _, fun x a => ?_⟩
  · intro h
    apply he
    have := LinearMap.congr_fun h (e v)
    simpa [MultilinearMap.toLinearMap] using this
  · have hx : x.1 ∈ infU E n := GlobalTheory.DefU.embU_le_infU _ x.2
    have h2 := heq ⟨x.1, hx⟩ (PiTensorProduct.tprod ℂ (Function.update e v a))
    have h3 : wInf lam x.1 (PiTensorProduct.tprod ℂ (Function.update e v a)) =
        PiTensorProduct.tprod ℂ (Function.update e v (GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding x.1) a)) := by
      change PiTensorProduct.map _ _ = _
      rw [PiTensorProduct.map_tprod]
      congr 1
      funext u
      by_cases h : u = v
      · subst h
        simp
      · have h1 := (Subgroup.mem_inf.1 x.2).2
        rw [Subgroup.mem_iInf] at h1
        have h4 := h1 u.embedding
        rw [Subgroup.mem_iInf] at h4
        have h5 : cEmb u.embedding x.1 = 1 := MonoidHom.mem_ker.1 (h4 (by simpa using h))
        simp only [Function.update_of_ne h, h5, map_one, Module.End.one_apply]
    rw [h3] at h2
    simpa [MultilinearMap.toLinearMap] using h2

theorem phiFun_mem_forms (hU : Unr E) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n)
    (K' : ∀ w : Pl E, Subgroup (UL n w)) (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K')
    (F : finU E n → Module.Dual ℂ (Wsp lam)) (hF : F ∈ vecM S lam K') (w : Wsp lam) :
    phiFun lam F w ∈ forms S lam K' := by
  have h := semis E n (Wsp lam) ((wInf lam).comp (infU E n).subtype) (spanW E n lam) (globLev S K')
    (isOpen_globLev E hU n S K' hK) (phiFun lam F) (fun u => isAutFormU_phiFun hU S lam K' hK F hF u)
    (fun x u => phiFun_wInf lam F x u) (fun u => phiFun_mem_fixed S lam K' F hF u) w
  refine SetLike.le_def.1 ?_ h
  refine iSup_mono fun π => iSup_mono' fun hP => ⟨⟨hP.1, fun v => ?_⟩, le_rfl⟩
  obtain ⟨f', h0, hπ, heq⟩ := hP.2
  exact hasWeightAt_of_wInf lam π f' h0 hπ (fun x u => heq x u) v

end GlobalTheory.BCT.TrKer.RangeLe

namespace GlobalTheory.BCT.TrKer

open GlobalTheory.BCT.TrKer.RangeLe in

theorem range_Phi_le_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → LinearMap.range (Phi S lam K') ≤ forms S lam K' := by
  intro E _ _ _ hU n _ S _ lam K' hK
  rw [LinearMap.range_eq_map, ← TensorProduct.span_tmul_eq_top, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨F, w, rfl⟩, rfl⟩
  rw [Phi_tmul]
  exact phiFun_mem_forms hU S lam K' hK F.1 F.2 w

end GlobalTheory.BCT.TrKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsOfHeckeLbPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.BiextPairing

open GlobalTheory.UPel.HT

theorem lbIso_lbPow_hecke {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) (k : ℕ) :
    LBIso (lbPow P k) ((Hecke.lbPow P k).pull (𝟙 X)) := by
  have hQ : (Hecke.lbPow P k).IsLB := LB.isLB_linComb hP _ _
  have h₁ : LBIso (lbPow P k) (Hecke.lbPow P k) := by
    unfold Hecke.lbPow lbPow
    refine (GlobalTheory.PrimNorm.lbIso_iff hP _ _ _ _).2 ?_
    simp
  exact h₁.trans (LB.isLB_linComb hP _ _) hQ (pull_isLB hQ _) (GlobalTheory.DescendedPrincipal.lbIso_pull_id hQ).symm

theorem weilIs_of_hecke_lbPow {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {P : LB A.left} (hP : P.IsLB) (k : ℕ) {T : Over S} {X Y : T ⟶ A} {u : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A (Hecke.lbPow P k) 1 X Y u) : Out.WeilIs A P k X Y u := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hQ : (Hecke.lbPow P k).IsLB := LB.isLB_linComb hP _ _
  have := (GlobalTheory.weilIs_along_hom hG S A A (𝟙 _) P (Hecke.lbPow P k) k 1 T X Y u u hA hA hP hQ inferInstance
    (lbIso_lbPow_hecke hP k) (by simpa using h)).1
  simpa using this

end GlobalTheory.BiextPairing

namespace GlobalTheory.BiextPairing

open GlobalTheory.UPel.HT

end GlobalTheory.BiextPairing
end
end

