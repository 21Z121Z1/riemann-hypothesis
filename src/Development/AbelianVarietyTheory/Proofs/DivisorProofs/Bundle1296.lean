import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.VB GlobalTheory.Conormal

namespace GlobalTheory.ConormalFrame

theorem sub_isLocalizedModule {X : Scheme.{0}} {F : X.Modules} [F.IsQuasicoherent] (N : Sub F)
    {U : X.Opens} (hU : IsAffineOpen U)
    (h : ∀ (f : Γ(X, U)) (t : Γ(F, U)),
      GlobalTheory.Twist.resM F (X.basicOpen_le f) t ∈ N.sec _ → ∃ n : ℕ, f ^ n • t ∈ N.sec U)
    (f : Γ(X, U)) : IsLocalizedModule.Away f (GlobalTheory.QCoh.resBasicOpen N.toMod f) := by
  refine (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff _ f).2 ⟨fun s => ?_, fun t ht => ?_⟩
  · obtain ⟨n, t, e⟩ := GlobalTheory.QCoh.exists_pow_smul_eq_res F hU f (X.basicOpen_le f) rfl
      (N.incl.app _ s)
    obtain ⟨m, hm⟩ := h f t (by
      change F.presheaf.map _ t ∈ _
      rw [← e]
      exact (N.sec _).smul_mem _ (N.incl_app_mem s))
    refine ⟨m + n, N.mkSec _ hm, N.incl_app_injective _ ?_⟩
    rw [Scheme.Modules.Hom.app_smul, GlobalTheory.QCoh.app_res, Sub.incl_app_mkSec, Scheme.Modules.map_smul,
      ← e, pow_add, mul_smul, map_pow]
  · obtain ⟨n, e⟩ := GlobalTheory.QCoh.exists_pow_smul_eq_zero F hU f (X.basicOpen_le f) rfl
      (N.incl.app _ t) (by rw [← GlobalTheory.QCoh.app_res, ht, map_zero])
    exact ⟨n, N.incl_app_injective _ (by rw [Scheme.Modules.Hom.app_smul, e, map_zero])⟩

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}

include he in

theorem preimage_eq (c : IsChart π e U W) : e ⁻¹ᵁ W = U :=
  le_antisymm ((le_preimage_iff he).1 (e.preimage_mono c.le_base)) c.le

include he in

theorem isQuasicoherent_restrict_ideal (c : IsChart π e U W) :
    ((ideal e).restrict c.affine.fromSpec).IsQuasicoherent := by
  have := (isVB_structureModule X).isQuasicoherent
  refine (GlobalTheory.QCoh.isQuasicoherent_restrict_fromSpec_iff _ c.affine).2
    (sub_isLocalizedModule _ c.affine fun f (t : Γ(X, W)) ht => ?_)
  have hcpt : IsCompact ((e ⁻¹ᵁ W : S.Opens) : Set S) := by
    rw [preimage_eq he c]; exact c.affine_base.isCompact
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact S
    (U := e ⁻¹ᵁ W) hcpt (e.appLE W _ le_rfl t) (e.appLE W _ le_rfl f) (by
      have hle : S.basicOpen (e.appLE W _ le_rfl f) ≤ e ⁻¹ᵁ X.basicOpen f := by
        rw [Scheme.Hom.appLE_eq_app, e.preimage_basicOpen]
      have := congrArg (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG S hle)
        (show e.appLE _ _ le_rfl (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X (X.basicOpen_le f) t) = 0 from ht)
      rw [GlobalTheory.DualPull.resG_appLE, GlobalTheory.DualPull.appLE_resG, map_zero] at this
      exact (GlobalTheory.DualPull.resG_appLE e _ _ _).trans this)
  refine ⟨n, ?_⟩
  change e.appLE W _ le_rfl (f ^ n * t) = 0
  rw [map_mul, map_pow, hn]

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}

include he in

theorem isQuasicoherent_conormal : (conormal e).IsQuasicoherent := by
  refine GlobalTheory.QCoh.isQuasicoherent_of_forall_exists_affine _ fun x => ?_
  obtain ⟨U, W, hx, -, c⟩ := exists_isChart he (x := x) (V := ⊤) trivial
  have := isQuasicoherent_restrict_ideal he c
  refine ⟨U, c.affine_base, hx,
    (GlobalTheory.QCoh.isQuasicoherent_restrict_fromSpec_iff _ c.affine_base).mp ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec Γ(S, U)).ringCatSheaf).prop_of_iso
    ((GlobalTheory.QCoh.restrictPullbackIso
      (IsAffineOpen.SpecMap_appLE_fromSpec e c.affine c.affine_base c.le)).app (ideal e))
    (GlobalTheory.QCoh.isQuasicoherent_pullback_Spec (e.appLE W U c.le) ((ideal e).restrict c.affine.fromSpec))

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

open GlobalTheory.QCoh

set_option backward.isDefEq.respectTransparency false in

theorem isBaseChange_pullbackSections {X Y : Scheme.{0}} (f : X ⟶ Y) (G : Y.Modules)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    [(G.restrict hV.fromSpec).IsQuasicoherent] (e : U ≤ f ⁻¹ᵁ V) :
    letI := appLEAlgebra f e
    letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
    haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
    IsBaseChange Γ(X, U) (pullbackSections f G e) := by
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  obtain ⟨a, ha⟩ := exists_equiv_pullback_Spec (f.appLE V U e) (G.restrict hV.fromSpec)
  have w := IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e
  let κ : Γ((Scheme.Modules.pullback (Spec.map (f.appLE V U e))).obj (G.restrict hV.fromSpec), ⊤)
      ≃ₗ[Γ(X, U)] Γ(((Scheme.Modules.pullback f).obj G).restrict hU.fromSpec, ⊤) :=
    (moduleSpecΓFunctor.mapIso ((restrictPullbackIso w).app G)).toLinearEquiv
  refine IsBaseChange.of_equiv
    ((sectionsEquivFromSpec G hV).baseChange Γ(Y, V) Γ(X, U) _ _ ≪≫ₗ a ≪≫ₗ κ ≪≫ₗ
      (sectionsEquivFromSpec _ hU).symm) fun s ↦ ?_
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_eq, LinearEquiv.baseChange_tmul, ha, sectionsEquivFromSpec_apply,
    sectionsEquivFromSpec_apply, res_pullbackSections]
  refine Eq.trans ?_ (restrictPullbackIso_hom_app_pullbackSections w G (V' := ⊤) (U' := ⊤)
    (fromSpec_image_le hV ⊤) le_rfl _ s)
  exact congr(κ $(res_self _ le_rfl _)).symm

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}

theorem ofAugCot_bijective (c : IsChart π e U W) : Function.Bijective (c.ofAugCot he) := by
  letI := c.algebra
  letI := GlobalTheory.QCoh.appLEAlgebra e c.le
  letI := GlobalTheory.QCoh.appLEModule e ((Scheme.Modules.pullback e).obj (ideal e)) c.le
  haveI := GlobalTheory.QCoh.appLE_isScalarTower e ((Scheme.Modules.pullback e).obj (ideal e)) c.le
  haveI := AugCot.isScalarTower_of_algebraMap_eq (c.aug he) fun _ => rfl
  haveI := isQuasicoherent_restrict_ideal he c
  have hb := isBaseChange_pullbackSections e (ideal e) c.affine_base c.affine c.le
  let g : Γ(ideal e, W) →ₗ[Γ(X, W)] AugCot (c.aug he) := (RingHom.ker (c.aug he)).toCotangent ∘ₗ
    (GlobalTheory.QCoh.appLinear (idealSub e).incl W).codRestrict (RingHom.ker (c.aug he)) fun s =>
      (c.aug_eq_zero_iff he).2 ((idealSub e).incl_app_mem s)
  have key (x : RingHom.ker (c.aug he)) : c.ofAugCot he ((RingHom.ker (c.aug he)).toCotangent x) =
      cls c.le x ((c.aug_eq_zero_iff he).1 x.2) := d_eq_cls he _ _ _
  refine Function.bijective_iff_has_inverse.2 ⟨hb.lift g, fun x => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := (RingHom.ker (c.aug he)).toCotangent_surjective x
    rw [key]
    exact hb.lift_eq g _
  · refine hb.inductionOn y (fun y => c.ofAugCot he (hb.lift g y) = y)
      (by rw [map_zero, map_zero]; rfl) (fun s => ?_) (fun r y hy => ?_) fun y z hy hz => ?_
    · rw [hb.lift_eq]
      exact key _
    · rw [map_smul, map_smul, hy]
      rfl
    · rw [map_add, map_add, hy, hz]
      rfl

include he in

theorem exists_isFrame [Smooth π] (x : S) :
    ∃ (U : S.Opens) (n : ℕ) (s : Fin n → Γ(conormal e, U)), x ∈ U ∧ IsFrame s := by
  have := isQuasicoherent_conormal he
  obtain ⟨U, W, hx, -, c⟩ := exists_isChart he (x := x) (V := ⊤) trivial
  letI := c.algebra
  have : Algebra.Smooth Γ(S, U) Γ(X, W) := Smooth.smooth_appLE π c.affine_base c.affine c.le_base
  let E := LinearEquiv.ofBijective (c.ofAugCot he) (ofAugCot_bijective he c)
  have := Module.Finite.equiv E
  have := Module.Projective.of_equiv E
  exact Summand.exists_frame_of_projective c.affine_base ⟨x, hx⟩

end GlobalTheory.ConormalFrame

theorem GlobalTheory.ConormalFrame.exists_isFrame_omega : ∀ (O : Type) [CommRing O] (A : Over (Sp O))
    [GrpObj A] [Smooth A.hom] (x : Sp O), ∃ (U : (Sp O).Opens) (n : ℕ)
    (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)), x ∈ U ∧ GlobalTheory.VB.IsFrame s :=
  fun _ _ A _ _ x => GlobalTheory.ConormalFrame.exists_isFrame (GlobalTheory.LieVB.sec_hom η[A]) x
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLLatticeSpannedByGLColumnsEqFullLatticeStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_latticeSpannedByGLColumns_eq_fullLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ q : GLw a w, GlobalTheory.TwLat.lat e b q = L := by
  first | exact @GlobalTheory.TwOrbLat.exists_lat_eq | exact GlobalTheory.TwOrbLat.exists_lat_eq | (intros; apply GlobalTheory.TwOrbLat.exists_lat_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPairFlagsDifferingOneStep
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Gen

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap g = spMap (h.comp g) := by
  rw [← Spec.map_comp]
  rfl

theorem exists_genPair : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∃ ψ₂ : Y.Fn →+* RatFunc Y.Fn, GenPair Y (algebraMap Y.Fn (RatFunc Y.Fn)) ψ₂ ∧ (∀ u : X.Fn, algebraMap Y.Fn (RatFunc Y.Fn) (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) * (B.map (algebraMap Y.Fn (RatFunc Y.Fn)) * (B.map ψ₂)⁻¹)) := by
  intro F _ X Y ι _ m E E' φ f hf B hB τ a b hab
  obtain ⟨V, c, t, hc, ht, hr⟩ := GlobalTheory.T.exists_valuationSubring_ratFunc_X_residue_zero Y.Fn
  obtain ⟨A, hA⟩ := E.nonempty (f (genericPoint Y.X))
  have hM : Par 0 ((ratOf Y).O (genericPoint Y.X)).toSubring (B * (A.map φ)⁻¹) := hf.sub _ B hB A hA
  obtain ⟨pt, hpt⟩ : ∃ pt : Sp Y.Fn ⟶ Y.X, pt = (ratOf Y).pt := ⟨_, rfl⟩
  have hpa (w) : pt w = genericPoint Y.X := hpt ▸ (ratOf Y).pt_apply w
  have hps : pt ≫ Y.str = spMap (algebraMap F Y.Fn) := hpt ▸ (ratOf Y).pt_s
  have hq : spMap (algebraMap V (RatFunc Y.Fn)) ≫ spMap c ≫ pt = spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt := by
    rw [← Category.assoc, spMap_comp, hc]
  have hh : Par 0 ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) *
      (B * (A.map φ)⁻¹).map (algebraMap Y.Fn (RatFunc Y.Fn))) := by
    refine Par.mul (ClosedPt.par_zero_top fun σ => ?_) (hM.map _ fun _ _ => trivial)
    rw [(GlobalTheory.T.blockMatrixElementaryShear_properties ι m τ a b hab _ _).1 σ]
    exact one_ne_zero
  have hx : ((spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f)
      (IsLocalRing.closedPoint (RatFunc Y.Fn)) = f (genericPoint Y.X) :=
    congrArg f (hpa _)
  have hA' : A ∈ E.S (((spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f)
      (IsLocalRing.closedPoint (RatFunc Y.Fn))) := (congrArg (fun z : X.X => A ∈ E.S z) hx).mpr hA
  obtain ⟨q₂, hq₂, hb⟩ : ∃ q₂ : Sp (RatFunc Y.Fn) ⟶ Y.X,
      q₂ ≫ f = (spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f ∧ Bears E' φ A (shear τ a b (RatFunc.X : RatFunc Y.Fn) *
      (B * (A.map φ)⁻¹).map (algebraMap Y.Fn (RatFunc Y.Fn))) q₂ := (hf.lifts (RatFunc Y.Fn) _ A hA' _ hh).exists
  have hs : f ≫ X.str = Y.str := hf.hom.inducedModelMorphism_comp_structureMap
  obtain ⟨v₂, hv₂, hv₂f⟩ := GlobalTheory.T.exists_lift_valuative_criterion_varieties F X Y f hs _ V (spMap c ≫ pt) q₂ (by
    rw [hq₂, ← hq]; simp only [Category.assoc])
  have hmeet : spMap (IsLocalRing.residue V) ≫ spMap c ≫ pt = spMap (IsLocalRing.residue V) ≫ v₂ := by
    subst hpt
    exact GlobalTheory.T.shearedGenericFlag_eq_genericFlag_at_special F X Y ι m E E' φ f hf B hB A hA τ a b hab _ V c t hr v₂
      (hv₂f.trans (Category.assoc _ _ _)) (by subst hv₂; rw [hc, ht]; exact hb)
  have h1 : (spMap c ≫ pt) (IsLocalRing.closedPoint V) = genericPoint Y.X := hpa _
  have h2 : v₂ (IsLocalRing.closedPoint V) = genericPoint Y.X := by
    rw [← ClosedPt.closedPt_comp v₂, ← hmeet, ClosedPt.closedPt_comp, h1]
  letI : Algebra F (RatFunc Y.Fn) := ((algebraMap Y.Fn (RatFunc Y.Fn)).comp (algebraMap F Y.Fn)).toAlgebra
  have hsp : q₂ (IsLocalRing.closedPoint (RatFunc Y.Fn)) ⤳ genericPoint Y.X := by
    have := ClosedPt.gen_specializes v₂ (IsLocalRing.closedPoint (RatFunc Y.Fn))
    rwa [hv₂, h2] at this
  have hstr : q₂ ≫ Y.str = spMap ((algebraMap Y.Fn (RatFunc Y.Fn)).comp (algebraMap F Y.Fn)) := by
    rw [← hs, ← Category.assoc, hq₂, Category.assoc, hs, Category.assoc, ← spMap_comp, hps]
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_specializes_genericPoint F Y (RatFunc Y.Fn) q₂ hsp hstr
  subst hpt
  have hcv := GlobalTheory.T.flag_of_dominant_point_as_triangular_matrix F X Y ι m E E' φ f hf B hB A hA _ (algebraMap Y.Fn (RatFunc Y.Fn)) ψ.toRingHom
    (shear τ a b RatFunc.X) (by
      subst hψ
      exact (Category.assoc _ _ _).symm.trans (hq₂.symm.trans (Category.assoc _ _ _))) (by subst hψ; exact hb)
  refine ⟨ψ.toRingHom, ⟨?_, V, spMap c ≫ (ratOf Y).pt, v₂, hq, hv₂.trans hψ, hmeet, h1⟩, hcv.1, hcv.2⟩
  exact RingHom.ext fun r => (ψ.commutes r).symm

end GlobalTheory.FlagPush.Gen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGenerationAmplePairMultiples
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.AmpleGen

theorem exists_genAt_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ j : ℕ, GenAt P (c₀ * j) := by
  intro k _ X _ p D _ P hA
  obtain ⟨c, hc, N, s, hs⟩ := hA.exists_isGenerated_pow
  have hrep : P.Rep 0 (c : ℤ) (P.A.pow c) := by
    have := Pair.rep_pow k X p P 0 1 P.A c (Pair.rep_base k X p P).2.1
    simpa using this
  obtain ⟨e, -, hrange, hnu, -⟩ := RepDict.rep_dict k X p P 0 c (P.A.pow c) hrep
  have hmem : ∀ i, e (s i) ∈ P.H 0 c := fun i => by
    have : e (s i) ∈ Set.range e := ⟨s i, rfl⟩
    rw [hrange] at this
    exact this
  have hne : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, P.nu 0 c σ y (e (s i)) ≠ 0 := by
    intro σ y
    obtain ⟨i, hi⟩ := exists_mem_ptsIn hs y
    refine ⟨i, fun h0 => ?_⟩
    have h2 := hnu (s i) σ y
    have hpick := mem_pick ((P.A.pow c).φ σ).isLB y
    have hv := (secVal_ne_zero_iff (s i) hpick).2 hi
    have hpos : ((P.A.pow c).φ σ).nsq (secVal p σ (s i)) y ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hv)) (Real.exp_pos _).ne'
    rw [h0] at h2
    exact hpos (by rw [← h2]; ring)
  refine ⟨c, hc, fun j => ⟨N, fun i => e (s i) ^ j, fun i => ?_, fun σ y => ?_⟩⟩
  · obtain ⟨h1, -⟩ := NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j
    have e1 : (j : ℤ) * 0 = 0 := by ring
    have e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at h1
    exact h1
  · obtain ⟨i, hi⟩ := hne σ y
    obtain ⟨-, h2⟩ := NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j
    have e1 : (j : ℤ) * 0 = 0 := by ring
    have e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ) := by push_cast; ring
    have h3 := h2 σ y
    rw [e1, e2] at h3
    exact ⟨i, by rw [h3]; exact pow_ne_zero _ hi⟩

end GlobalTheory.HSNef.AmpleGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPatchOfComplexPointOpenPartStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodPatch_of_complexPoint_openPart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ y ∈ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  first | exact @GlobalTheory.GoodTop.exists_goodPatch_of_mem | exact GlobalTheory.GoodTop.exists_goodPatch_of_mem | (intros; apply GlobalTheory.GoodTop.exists_goodPatch_of_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantWachModuleBasisOfNonnegJumpsStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_wachModule_basis_of_nonneg_jumps : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n : ℕ), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u) → Module.finrank ↥(OL LL) ↥T.L.T = n → ∀ γ : ((HW l).W K 1 LL hA.2.2).Gam, ∃ (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N := by
  first | exact @GlobalTheory.WachFrame.exists_frame | exact GlobalTheory.WachFrame.exists_frame | (intros; apply GlobalTheory.WachFrame.exists_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsOpenSubgroupAdicUnitsNoRootsOfUnity
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RootOpen

open Classical in

theorem finite_roots (E : Type) [Field E] [NumberField E] :
    {t : Eˣ | ∃ n : ℕ, 0 < n ∧ t ^ n = 1}.Finite := by
  have hF : Finite (NumberField.Units.torsion E) := inferInstance
  have hT : ((NumberField.Units.torsion E : Set (𝓞 E)ˣ)).Finite := Set.finite_coe_iff.1 hF
  refine (hT.image (Units.map (algebraMap (𝓞 E) E).toMonoidHom)).subset ?_
  rintro t ⟨n, hn, ht⟩
  have h1 : IsIntegral ℤ (t : E) := IsIntegral.of_pow hn (by rw [← Units.val_pow_eq_pow_val, ht]; exact isIntegral_one)
  have h2 : IsIntegral ℤ ((t⁻¹ : Eˣ) : E) :=
    IsIntegral.of_pow hn (by rw [← Units.val_pow_eq_pow_val, inv_pow, ht, inv_one]; exact isIntegral_one)
  let u : (𝓞 E)ˣ := ⟨⟨t, h1⟩, ⟨(t⁻¹ : Eˣ), h2⟩,
    NumberField.RingOfIntegers.ext (show (t : E) * ((t⁻¹ : Eˣ) : E) = 1 by simp),
    NumberField.RingOfIntegers.ext (show ((t⁻¹ : Eˣ) : E) * (t : E) = 1 by simp)⟩
  refine ⟨u, ?_, ?_⟩
  · show u ∈ CommGroup.torsion (𝓞 E)ˣ
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩)
    ext
    show ((t ^ n : Eˣ) : E) = 1
    simp [ht]
  · ext; rfl

variable {E : Type} [Field E] [NumberField E]

theorem val_eq_one_of_lt (w : HeightOneSpectrum (𝓞 E)) {z : w.adicCompletion E} (hz : Valued.v (z - 1) < 1) :
    Valued.v z = 1 := by
  have := Valuation.map_add_eq_of_lt_left (Valued.v) (x := (1 : w.adicCompletion E)) (y := z - 1) (by simpa using hz)
  simpa using this

def congOne (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) (hm : m < 0) : Subgroup (w.adicCompletion E)ˣ where
  carrier := {z | Valued.v ((z : w.adicCompletion E) - 1) ≤ WithZero.exp m}
  one_mem' := by simp
  mul_mem' := by
    intro z u hz hu
    have hz' : Valued.v ((z : w.adicCompletion E) - 1) ≤ WithZero.exp m := hz
    have hu' : Valued.v ((u : w.adicCompletion E) - 1) ≤ WithZero.exp m := hu
    have hlt : WithZero.exp m < 1 := by
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 hm
    have h1 := val_eq_one_of_lt w (hz'.trans_lt hlt)
    show Valued.v (((z * u : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ WithZero.exp m
    have e : ((z * u : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        (z : w.adicCompletion E) * ((u : w.adicCompletion E) - 1) + ((z : w.adicCompletion E) - 1) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine Valuation.map_add_le _ ?_ hz'
    rw [map_mul, h1, one_mul]; exact hu'
  inv_mem' := by
    intro z hz
    have hz' : Valued.v ((z : w.adicCompletion E) - 1) ≤ WithZero.exp m := hz
    have hlt : WithZero.exp m < 1 := by
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 hm
    have h1 := val_eq_one_of_lt w (hz'.trans_lt hlt)
    show Valued.v (((z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ WithZero.exp m
    have e : ((z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        ((z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) * (1 - (z : w.adicCompletion E)) := by
      rw [mul_sub, mul_one, Units.inv_mul]
    rw [e, map_mul, Valuation.map_sub_swap, Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one, one_mul]
    exact hz'

theorem isOpen_congOne (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) (hm : m < 0) :
    IsOpen (congOne w m hm : Set (w.adicCompletion E)ˣ) :=
  (GlobalTheory.Mem.UnitOpen.isOpen_val_le w m).preimage (Units.continuous_val.sub continuous_const)

end GlobalTheory.RootOpen

namespace GlobalTheory.RootOpen

theorem exists_open_subgroup_no_roots : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ V : Subgroup (w.adicCompletion E)ˣ,
    IsOpen (V : Set (w.adicCompletion E)ˣ) ∧ ∀ t : Eˣ, (∃ n : ℕ, 0 < n ∧ t ^ n = 1) →
      Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom t ∈ V → t = 1 := by
  intro E _ _ w
  set S := {t : Eˣ | ∃ n : ℕ, 0 < n ∧ t ^ n = 1}
  have hL : ((fun t : Eˣ => WithZero.log (Valued.v ((algebraMap E (w.adicCompletion E) (t : E)) - 1))) ''
      (S \ {1})).Finite := ((finite_roots E).diff).image _
  obtain ⟨b, hb⟩ := hL.bddBelow
  refine ⟨congOne w (min b 0 - 1) (by omega), isOpen_congOne w _ _, fun t ht hV => ?_⟩
  by_contra h1
  have hmem := hb ⟨t, ⟨ht, h1⟩, rfl⟩
  have hne : Valued.v ((algebraMap E (w.adicCompletion E) (t : E)) - 1) ≠ 0 := by
    rw [Ne, map_eq_zero, sub_eq_zero, ← map_one (algebraMap E (w.adicCompletion E))]
    intro e
    exact h1 (Units.ext ((algebraMap E (w.adicCompletion E)).injective e))
  have hV' : Valued.v ((algebraMap E (w.adicCompletion E) (t : E)) - 1) ≤ WithZero.exp (min b 0 - 1) := hV
  rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at hV'
  simp only at hmem
  omega

end GlobalTheory.RootOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwistedOrbitalPointTermNeZero
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

theorem exists_ne_zero_of_twTerm_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (δ : G) (f : G → ℂ) (y : G) (h : GlobalTheory.EulerAbs.twTerm θ K δ f y ≠ 0) :
    ∃ k ∈ K, f ((y * k)⁻¹ * δ * θ (y * k)) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  have hu : (fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))) = fun _ => 0 := by
    funext k
    exact hc k k.2
  unfold GlobalTheory.EulerAbs.twTerm
  rw [hu]
  simp [GlobalTheory.BCT.avg]

end GlobalTheory.EulerAbs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactIntegralMatrixAddSubgroupStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_compact_integralMatrixAddSubgroup : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ), ∃ Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ IsCompact (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ intMat a b w = AddSubgroup.toSubgroup Λ := by
  first | exact @GlobalTheory.IntMatOpen.intMat_open_compact | exact GlobalTheory.IntMatOpen.intMat_open_compact | (intros; apply GlobalTheory.IntMatOpen.intMat_open_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenConjStableSubgroupOfSplitLevelStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_conjStable_subgroup_of_splitLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)), IsSplitAt w →
    IsLevel (MonoidHom.id _) (KL n w) K' → ∃ N : Subgroup (GLw n w), IsOpen (N : Set (GLw n w)) ∧
      N ≤ K'.map (UL n w).subtype ∧ (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ x ∈ N, k⁻¹ * x * k ∈ N) ∧
      (K' = KL n w → N = GlobalTheory.LFun.KGL w n) := by
  first | exact @GlobalTheory.BCT.CtLevel.exists_open_conjStable_sub_level | exact GlobalTheory.BCT.CtLevel.exists_open_conjStable_sub_level | (intros; apply GlobalTheory.BCT.CtLevel.exists_open_conjStable_sub_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveVarietyOfIsLocalRingOfVarietyPoiStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projectiveVariety_of_isLocalRingOfVarietyPoint : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L) (n : ℕ) (x : Fin n → L), IsLocModel c R → TrBasis c x →
  ∃ (Y : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral Y) (p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (e : Y.functionField ≃+* L) (y : Y),
    IsProjOver p ∧ topologicalKrullDim Y = n ∧ (∀ a, e (GlobalTheory.Cartier.constFn p a) = c a) ∧ (locRing y).map e.toRingHom = R := by
  first | exact @GlobalTheory.LocModelProj.exists_projective_of_isLocModel | exact GlobalTheory.LocModelProj.exists_projective_of_isLocModel | (intros; apply GlobalTheory.LocModelProj.exists_projective_of_isLocModel <;> assumption)
end

