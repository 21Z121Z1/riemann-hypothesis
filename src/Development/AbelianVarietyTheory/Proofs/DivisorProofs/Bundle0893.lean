import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0870
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonAffineRefinementAlongMorphism
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
section
open NumberField IsDedekindDomain

noncomputable section
open scoped Classical

namespace GlobalTheory.WeilM

variable (F : Type) [Field F] [NumberField F]

theorem thetaSum_pureA_bound {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
    ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ‖thetaSum F (pureA F f g)‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hg.2.isCompact
  haveI := discreteTopology_denomLattice F κ hN
  have hw := ZLattice.summable_norm_pow_inv (denomLattice F κ N) (Module.finrank ℤ (denomLattice F κ N) + 1)
    (Nat.lt_succ_self _)
  set k := Module.finrank ℤ (denomLattice F κ N) + 1 with hkdef
  set W := ∑' z : denomLattice F κ N, ‖z‖⁻¹ ^ k with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => by positivity
  refine ⟨{(0, 0), (k, 0)}, max B 0 * (1 + W), mul_nonneg (le_max_right _ _) (by linarith), fun f => ?_⟩
  set M := (({(0, 0), (k, 0)} : Finset (ℕ × ℕ)).sup
    (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f with hMdef
  have h00 : ∀ x, ‖f x‖ ≤ M := fun x => (SchwartzMap.norm_le_seminorm ℂ f x).trans
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)
      (i := (0, 0)) (by simp))
  have hk0 : ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ M := fun x => by
    have := SchwartzMap.le_seminorm ℂ k 0 f x
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)
      (i := (k, 0)) (by simp))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (h00 0)
  have hpt : ∀ z : denomLattice F κ N, ‖f z‖ ≤ (if z = 0 then M else 0) + ‖z‖⁻¹ ^ k * M := fun z => by
    by_cases hz : z = 0
    · subst hz; simp only [if_true]
      have := h00 0
      have h2 : 0 ≤ ‖(0 : denomLattice F κ N)‖⁻¹ ^ k * M := by positivity
      simpa using (show ‖f 0‖ ≤ M + ‖(0 : denomLattice F κ N)‖⁻¹ ^ k * M by linarith)
    · rw [if_neg hz, zero_add]
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
      rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hz0 _), mul_comm]
      exact hk0 z
  have hs1 : HasSum (fun z : denomLattice F κ N => if z = 0 then M else 0) M := by
    convert hasSum_ite_eq (0 : denomLattice F κ N) M
  have hsumL : Summable fun z : denomLattice F κ N => (if z = 0 then M else 0) + ‖z‖⁻¹ ^ k * M :=
    hs1.summable.add (hw.mul_right M)
  have hfL : Summable fun z : denomLattice F κ N => ‖f z‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumL
  have hLbound : ∑' z : denomLattice F κ N, ‖f z‖ ≤ (1 + W) * M := by
    refine (hfL.tsum_le_tsum hpt hsumL).trans (le_of_eq ?_)
    rw [hs1.summable.tsum_add (hw.mul_right M), hs1.tsum_eq, tsum_mul_right]
    ring

  have hmem : pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  have hsupp : Function.support (fun ξ : κ → F => ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖)
      ⊆ S := by
    intro ξ hξ
    rw [Function.mem_support, norm_ne_zero_iff, pureA_algebraMap] at hξ
    have h0 := right_ne_zero_of_mul hξ
    show ∀ i, _
    intro i
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ (subset_tsupport _ h0) i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
    mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
  have hterm : ∀ ξ : S, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))‖ ≤
      max B 0 * ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ := fun ξ => by
    rw [pureA_algebraMap, norm_mul, mul_comm, Function.comp_apply]
    exact mul_le_mul (le_max_of_le_left (hB _)) le_rfl (norm_nonneg _) (le_max_right _ _)
  have hsumS : Summable ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) := hfL.comp_injective hj
  calc ‖thetaSum F (pureA F f g)‖
      ≤ ∑' ξ : κ → F, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ :=
        norm_tsum_le_tsum_norm (summable_norm_of_mem_schA F hmem)
    _ = ∑' ξ : S, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))‖ :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ ≤ ∑' ξ : S, max B 0 * ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ :=
        ((summable_norm_of_mem_schA F hmem).subtype S).tsum_le_tsum hterm (hsumS.mul_left _)
    _ = max B 0 * ∑' ξ : S, ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ := tsum_mul_left
    _ ≤ max B 0 * ∑' z : denomLattice F κ N, ‖f z‖ :=
        mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hfL (fun _ => norm_nonneg _) hj) (le_max_right _ _)
    _ ≤ max B 0 * ((1 + W) * M) := mul_le_mul_of_nonneg_left hLbound (le_max_right _ _)
    _ = max B 0 * (1 + W) * M := by ring

theorem exists_adm_eq_thetaSum_of_locallyCompact (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)]
    (κ : Type) [Fintype κ] : ∃ l : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm κ ∧
      ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ := by
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (thetaLin F κ)
  have hl' : ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ := fun Φ h => by
    have := LinearMap.congr_fun hl ⟨Φ, h⟩
    simpa using this
  refine ⟨l, fun g hg => ?_, hl'⟩
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ :=
    fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hadd : ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      pureA F (f + f') g = pureA F f g + pureA F f' g := fun f f' => by
    funext x; simp [pureA, add_mul]
  have hsmul : ∀ (a : ℂ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      pureA F (a • f) g = a • pureA F f g := fun a f => by
    funext x; simp [pureA, mul_assoc]
  let T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => thetaSum F (pureA F f g))
      (fun f f' => by rw [hadd]; exact thetaSum_add F (hmem f) (hmem f'))
      (fun a f => by rw [hsmul, thetaSum_smul]; rfl) (thetaSum_pureA_bound F hg)
  exact ⟨T, fun f => hl' _ (hmem f)⟩

end GlobalTheory.WeilM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechLineBundleAmbientOfOpenImmersion
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue.OpenExt

variable {X X' : Scheme.{0}} (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X')

theorem image_inf_le (a b : L.ι) : f ''ᵁ L.U a ⊓ f ''ᵁ L.U b ≤ f ''ᵁ (L.U a ⊓ L.U b) := fun x hx ↦ by
  obtain ⟨w, hw, rfl⟩ := hx.1
  exact f.apply_mem_image_iff.2 ⟨hw, f.apply_mem_image_iff.1 hx.2⟩

def extLB : LB X :=
  ⟨L.ι, fun a ↦ f ''ᵁ L.U a, fun a b ↦ res (image_inf_le f L a b) (GlobalTheory.GlueLineBundle.imU f _ (L.g a b))⟩

theorem gm_ext_g {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (a b : L.ι) (ha : r z ∈ L.U a) (hb : r z ∈ L.U b) :
    gm (r ≫ f) z ((extLB f L).U a ⊓ (extLB f L).U b) ((extLB f L).g a b) = gm r z (L.U a ⊓ L.U b) (L.g a b) := by
  have hm : (r ≫ f) z ∈ f ''ᵁ L.U a ⊓ f ''ᵁ L.U b := ⟨f.apply_mem_image_iff.2 ha, f.apply_mem_image_iff.2 hb⟩
  exact (gm_res (r ≫ f) z (image_inf_le f L a b) hm _).trans
    (GlobalTheory.GlueLineBundle.gm_imU f r z (L.U a ⊓ L.U b) ⟨ha, hb⟩ _)

variable {f} in

theorem gm_eq_map {Y : Scheme.{0}} (g : Y ⟶ X) (y : Y) (U : X.Opens) (h : g y ∈ U) (a : Γ(X, U)ˣ) :
    gm g y U a = Units.map (g.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (g y) U a) := by
  apply Units.ext
  rw [Units.coe_map, gm_val g y U h, GlobalTheory.GlueLineBundle.gm_id_val h]
  exact (Scheme.Hom.germ_stalkMap_apply g U y h a.val).symm

end GlobalTheory.PicGlue.OpenExt

namespace GlobalTheory.PicGlue.OpenExt

variable {X X' : Scheme.{0}} (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X')

theorem isOn_extLB (hL : L.IsLB) : IsOn f.opensRange (extLB f L) where
  le a x hx := by
    obtain ⟨w, -, rfl⟩ := hx
    exact ⟨w, rfl⟩
  cov x hx := by
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨a, ha⟩ := exists_chart hL w
    exact ⟨a, f.apply_mem_image_iff.2 ha⟩
  coc x a b c hxa hxb hxc := by
    obtain ⟨w, ha, rfl⟩ := hxa
    have hb : w ∈ L.U b := f.apply_mem_image_iff.1 hxb
    have hc : w ∈ L.U c := f.apply_mem_image_iff.1 hxc
    have e : ∀ (d d' : L.ι) (hd : w ∈ L.U d) (hd' : w ∈ L.U d'),
        Units.map (f.stalkMap w).hom.toMonoidHom (gm (𝟙 X) (f w) _ ((extLB f L).g d d')) =
          gm (𝟙 X') w (L.U d ⊓ L.U d') (L.g d d') := by
      intro d d' hd hd'
      rw [← gm_eq_map f w ((extLB f L).U d ⊓ (extLB f L).U d') ⟨f.apply_mem_image_iff.2 hd, f.apply_mem_image_iff.2 hd'⟩]
      have k := gm_ext_g f L (𝟙 X') w d d' hd hd'
      rwa [Category.id_comp] at k
    apply Units.map_injective (f := (f.stalkMap w).hom.toMonoidHom)
      (fun u v h ↦ (ConcreteCategory.bijective_of_isIso (f.stalkMap w)).1 h)
    refine (MonoidHom.map_mul _ _ _).trans ?_
    exact (congrArg₂ (· * ·) (e a b ha hb) (e b c hb hc)).trans
      ((gm_cocycle hL (𝟙 X') w ha hb hc).trans (e a c ha hc).symm)

end GlobalTheory.PicGlue.OpenExt

open GlobalTheory.PicGlue.OpenExt in

theorem GlobalTheory.PicGlue.exists_isOn_of_openImmersion : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X'),
    L.IsLB → ∃ L' : LB X, IsOn f.opensRange L' ∧ LBIso (L'.pull f) L := by
  intro X X' f _ L hL
  refine ⟨extLB f L, isOn_extLB f L hL, iso_of_chart hL ⟨fun J ↦ J PUnit.unit, ?_, ?_⟩⟩
  · intro J y hy
    exact f.apply_mem_image_iff.1 (mem_pull.1 hy)
  · intro y J J' hj hj'
    exact (gm_pull_g (extLB f L) f (𝟙 X') y J J' hj hj').trans
      (gm_ext_g f L (𝟙 X') y _ _ (f.apply_mem_image_iff.1 (mem_pull.1 hj)) (f.apply_mem_image_iff.1 (mem_pull.1 hj')))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleCorrectionSquareZeroIdealStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_correction_square_zero_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R) (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), PrimI I n₀ n₁ n₂ → ∀ (u : C1 F) (v : C0 F'), (∀ t t' a, IsUnit (u t t' a)) → In2 I F (mdef F u) → (∀ t, IsUnit (v t)) → MulRel I n₀ n₁ n₂ u v → ∃ u' : C1 F, In1 I F (u' - u) ∧ mdef F u' = 0 := by
  first | exact @GlobalTheory.LBLift.cocycle_of_sqZero | exact GlobalTheory.LBLift.cocycle_of_sqZero | (intros; apply GlobalTheory.LBLift.cocycle_of_sqZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonAffineRefinementAlongMorphismStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_affine_refinement_along_morphism : ∀ (X Z : Scheme.{0}) (φ : Z ⟶ X) (C C' : Type) [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C'] (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp Z), IsBas (opOf G) → IsBas (opOf G') → ∃ (D : Type) (_ : Category.{0} D) (_ : Quiver.IsThin D) (K : D ⥤ (Pair φ)ᵒᵖ) (H : D ⥤ C) (H' : D ⥤ C'), Nonempty (H ⋙ G ⟶ K ⋙ pairSnd φ) ∧ Nonempty (H' ⋙ G' ⟶ K ⋙ pairFst φ) ∧ IsBas (opOf (K ⋙ pairFst φ)) := by
  first | exact @GlobalTheory.LBObs.exists_pair_refine | exact GlobalTheory.LBObs.exists_pair_refine | (intros; apply GlobalTheory.LBObs.exists_pair_refine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexAbelianVarietySectionRatioAffineCov
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RatioCover

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r := by
  intro A _ g L u hA
  haveI := hA.comm
  obtain ⟨H, _, m, s, hv⟩ := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA
  refine ⟨m + 1, fun k => ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k),
    fun k j => GlobalTheory.ProjSpace.secRatio (s k) (s j), fun k => (hv.2 k).1, hv.1,
    fun k j => GlobalTheory.ProjSpace.basicOpen_secRatio _ _, fun k => GlobalTheory.ProjSpace.secRatio_self _, ?_⟩
  intro k j l z hk hj
  have hkj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) ⊓ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s j)) :=
    (GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨hk, hj⟩
  have e := congrArg (valAt' (u.ex z).left _)
    (GlobalTheory.ProjSpace.secRatio_mul_secRatio (s k) (s j) (s l) (inf_le_left) (inf_le_right))
  rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_res _ _ _ hkj, GlobalTheory.valAt'_res _ _ _ hkj, GlobalTheory.valAt'_res _ _ _ hkj] at e
  exact e.symm

end GlobalTheory.RatioCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexBaseChangePolarizedAbelianFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.PELU

theorem exists_isBC : ∀ (O : Type) [Ring O] (g : ℕ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g),
    ∃ F' : Fam ℂ O Λ g, IsBC F' F σ := by
  intro O _ g R _ σ Λ F
  let f : pullback F.s (spMap σ) ⟶ F.X := pullback.fst _ _
  let A' : Over (pullback F.s (spMap σ)) := (Over.pullback f).obj F.A
  letI : GrpObj A' := Functor.grpObjObj
  have hP : IsGrpPullback A' F.A f (pullback.fst F.A.hom f) := isGrpPullback_pullback F.A f
  haveI : IsCommMonObj A' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hP
  obtain ⟨act', ⟨hh, h1, hm, ha⟩, hc⟩ := GlobalTheory.ActPull.exists_act_pull _ _ f F.A A' _ hP Oᵐᵒᵖ
    (fun a => F.act a.unop) (fun a => F.hom _) F.act_one (fun a b => F.act_mul b.unop a.unop)
    (fun a b => F.act_add _ _)
  have hLB := LB.isLB_pull F.isLB (pullback.fst F.A.hom f)
  have hpol := GlobalTheory.pol_pull _ _ F.A A' f _ F.L (F.L.pull _) F.isLB hLB F.ab hP (GlobalTheory.PolBaseChange.lbIso_refl hLB)
  have hdim : SmoothOfRelativeDimension g A'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hP.1 F.dim
  let eta' : Λ → (𝟙_ (Over (pullback F.s (spMap σ))) ⟶ A') := fun a =>
    Over.homMk (hP.1.lift (f ≫ (F.eta a).left) (𝟙 _) (by
      rw [Category.assoc, Over.w]; simp)) (hP.1.lift_snd _ _ _)
  refine ⟨Fam.mk (pullback F.s (spMap σ)) (pullback.snd _ _) A' hpol.1 hdim (fun a => act' (MulOpposite.op a))
    (fun a => hh _) h1 (fun a b => by rw [MulOpposite.op_mul]; exact hm _ _)
    (fun a b => by rw [MulOpposite.op_add]; exact ha _ _)
    (F.L.pull (pullback.fst F.A.hom f)) hLB (hpol.2.1 F.ample) eta',
    f, pullback.fst F.A.hom f, IsPullback.of_hasPullback _ _, hP, fun a => hc _,
    GlobalTheory.PolBaseChange.lbIso_refl hLB, fun a => hP.1.lift_fst _ _ _⟩

end GlobalTheory.PELU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingLieMultiplicityZeroCharZeroStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_embedding_lie_multiplicity_zero_char_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), 2 * D.a < Module.finrank ℚ D.F → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ σ : 𝓞 D.F →+* k, LieMult (o.act.toF D) x σ 0 := by
  first | exact @GlobalTheory.HTLie.exists_lieMult_zero | exact GlobalTheory.HTLie.exists_lieMult_zero | (intros; apply GlobalTheory.HTLie.exists_lieMult_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFrameOffFiniteZeroSetStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_frame_off_finite_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → (∃ H : La, ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → (A.zeroSet s).Finite → ∃ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y := by
  first | exact @GlobalTheory.exists_etale_frame_of_finite_zeroSet | exact GlobalTheory.exists_etale_frame_of_finite_zeroSet | (intros; apply GlobalTheory.exists_etale_frame_of_finite_zeroSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnitMemOpenArchimedeanUnitsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_unit_mem_open_archimedean_units : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (V : Set (Cinf E)ˣ), IsOpen V → V.Nonempty → ∃ α : Eˣ, Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom α ∈ V := by
  first | exact @GlobalTheory.UnitsDense.exists_unit_mem_open | exact GlobalTheory.UnitsDense.exists_unit_mem_open | (intros; apply GlobalTheory.UnitsDense.exists_unit_mem_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCharacterSumEqLocallyConstantOnCompaStatement
section
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_characterSum_eq_locallyConstant_on_compact : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ {ι : Type} [Fintype ι] (K : Set (ι → F)), IsCompact K → ∀ Φ : (ι → F) → ℂ, IsLocallyConstant Φ → ∃ T : (ι → F) →₀ ℂ, ∀ r ∈ K, (T.sum fun v c => c * ψ (r ⬝ᵥ v)) = Φ r := by
  first | exact @GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact | exact GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact | (intros; apply GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCosetsUnitIdelesCompletedOrderStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_cosets_unitIdeles_completedOrder : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), c ≠ ⊥ → ∃ R : Finset (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) = 1) → ∃ r ∈ R, r⁻¹ * y ∈ hatOUnits c := by
  first | exact @GlobalTheory.CMVal.Euler.exists_finset_cover_units | exact GlobalTheory.CMVal.Euler.exists_finset_cover_units | (intros; apply GlobalTheory.CMVal.Euler.exists_finset_cover_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeomPointThrough
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_geomPoint_through : ∀ (T : Scheme.{0}) (p : T), ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (s : Sp K ⟶ T), p ∈ Set.range s := by
  intro T p
  refine ⟨AlgebraicClosure (T.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField p) (AlgebraicClosure (T.residueField p)))) ≫ T.fromSpecResidueField p, ?_⟩
  obtain ⟨x⟩ : Nonempty (Sp (AlgebraicClosure (T.residueField p))) := inferInstance
  refine ⟨x, ?_⟩
  show (T.fromSpecResidueField p).base _ = p
  exact Scheme.fromSpecResidueField_apply p _

end GlobalTheory
end

