import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.H0IsIffNonemptyLinearEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2474
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalSymmetricStructureOfGenericSymmetri
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CubSymPkg

theorem exists_cp_of_generic_sym : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) → ∀ L : LB G.left, L.IsLB → Out.Sym ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  intro R _ _ _ _ _ G _ _ hG hP L hL hS
  have laws : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  have := hG.smooth
  have := hG.geomConnected
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have hN : Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.ZJ.isNormalScheme_sp R
  let A := (Over.pullback (jK R)).obj G
  let F : A.left ⟶ G.left := pullback.fst G.hom (jK R)
  have gp : IsGrpPullback A G (jK R) F := isGrpPullback_pullback G (jK R)
  have hsA : IsSemiAbelian A := Geo.Tor.IsSemiAbelian.pullback (jK R) G hG
  have : IsProper A.hom := hP
  have hA : IsAbelianScheme A := Geo.Tor.AbelianSchemeGerms.isAbelianScheme_of_proper A hsA
  have hM : (L.pull F).IsLB := pull_isLB hL F

  obtain ⟨rA, hrA⟩ := DVR.exists_gen_of_isLB_local _ (pull_isLB hM (eSec A))
  let LA : RigLB A := ⟨L.pull F, rA, hM, hrA⟩
  obtain ⟨t, ht⟩ := GlobalTheory.GenericAmpleDvr.triv_theta hA hM
  obtain ⟨t', ht', hn⟩ := AbLaw.Cube.exists_normalised hM t ht
  let cA : CubicalStr A LA := AbLaw.Cube.cubicalOfNormalised laws.globalFns hA LA t' ht' hn
  obtain ⟨s₀, hs₀⟩ := (GlobalTheory.ZV.symB_iff_exists_gen _).1 ((GlobalTheory.ZV.symB_iff_sym hM).2 hS)
  obtain ⟨s₁, hs₁, hr₁⟩ := GlobalTheory.AbPackage.exists_rigidified_sym hM s₀ hs₀
  have symA : LA.IsSymmetric := (GlobalTheory.isSymmetric_iff_exists_gen _ A LA).2 ⟨s₁, hs₁, hr₁⟩

  obtain ⟨r, hr⟩ := DVR.exists_gen_of_isLB_local _ (pull_isLB hL (eSec G))
  let L' : RigLB G := ⟨L, r, hL, hr⟩
  have hw : PGen (GlobalTheory.UU.pullIso L F) := (isGen_iff _).1 (GlobalTheory.UU.pullIso_isGen hL F)
  obtain ⟨c', -⟩ := GlobalTheory.DenseCubeExt.exists_cubical (L := LA) hN gp cA L' hw
  obtain ⟨s, hs, hrs⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ G L').1
    (GlobalTheory.DenseCubeExt.isSymmetric (L := LA) hN gp L' hw symA)
  exact ⟨⟨L', c', s, hs, hrs, GlobalTheory.T.symmetry_cubicalBundle_of_dense_abelian_normal_base hN (jK R) G A F gp laws.globalFns hA L' c' s hs hrs⟩, rfl⟩

end GlobalTheory.CubSymPkg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalTrivialisationSplitTorusFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubicalTrivialisation_splitTorus_field : ∀ (k : Type) [CommRing k], IsField k → ∀ (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (P₀ : GlobalTheory.UU.CP G₀) (i : splitTorus (Sp k) X ⟶ G₀), IsMonHom i → Nonempty (GlobalTheory.UU.CubTriv P₀.c i) := by
  first | exact @GlobalTheory.Mum.TorusCubTriv.exists_cubTriv | exact GlobalTheory.Mum.TorusCubTriv.exists_cubTriv | (intros; apply GlobalTheory.Mum.TorusCubTriv.exists_cubTriv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclotomicAwayFiniteEtaleCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomicAway_finiteEtale_cover : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := by
  first | (exact @GlobalTheory.CycAwayCover.exists_cycAway_cover) | (exact GlobalTheory.CycAwayCover.exists_cycAway_cover) | (intros; apply GlobalTheory.CycAwayCover.exists_cycAway_cover  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDatOfIsAdd
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem exists_dat_of_isAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))), CatCoh.H1.mk _ f = c.1 →
    ∀ g : Fn2 A, IsAdd (fv f) g → ∃ d : Dat t c, d.f = f ∧ d.g = g := by
  intro R _ A _ p G t c f hf g hg
  choose s hs using fun n ↦ G.res_surjective n
  let h : ∀ n, G.A n := fun n ↦ Nat.rec 0 (fun n a ↦ s n (a -
    fv f (G.A (n + 1)) (G.A n) (G.res n : G.A (n + 1) →ₐ[R] G.A n) (t.y (n + 1)))) n
  refine ⟨⟨f, hf, g, hg, h, fun n ↦ ?_⟩, rfl, rfl⟩
  rw [show G.res n (h (n + 1)) = _ from hs n _]
  ring

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefectCoboundaryOfObstructionClassZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ObsCob

theorem exists_cob : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F) (θ : ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), Ω[F.obj T⁄R₀] →+ L.B T''), L.IsObs θ → L.IsOb2 α w 0 → ∃ g : ∀ (T T' : C) (_ : T ⟶ T'), L.B T', (∀ T T' a, g T T' a ∈ I.map (algebraMap R (L.B T'))) ∧ ∀ T T' T'' a b, θ T T' T'' a b (w.1 T) = L.ρ b (g T T' a) - g T T'' (a ≫ b) + g T' T'' b := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w θ hθ h0
  obtain ⟨θ', σ, z, hθ', hσ, hz, hzv⟩ := h0
  obtain ⟨f, hf⟩ := (H2.mk_eq_zero (F := ext R₁ F)).1 hz.symm
  refine ⟨fun T T' a ↦ σ T' (f T T' a), fun T T' a ↦ ?_, fun T T' T'' a b ↦ ?_⟩
  · exact (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (σ T') (hσ T')).1 _
  · have huniq := ((GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T)
      (L.ker T) (L.B T'') _ _ (L.ρ (a ≫ b)) _ _ (hθ T T' T'' a b)).2.2.1 (hθ' T T' T'' a b))
    rw [huniq, ← (hzv T T' T'' a b).2]
    have hnat := (GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (L.ρ b) (mp F b)
      (L.nat b) (σ T') (σ T'') (hσ T') (hσ T'')).1 (f T T' a)
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') a) b
    rw [← e, d1_apply, map_add, map_sub, hnat]
    rfl

end GlobalTheory.ObsCob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationData_pullback_injective_localHom : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → IsLocalHom ρ → ∀ D : DegData R (maximalIdeal R), ∃ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D.toPre D'.toPre) := by
  first | exact @GlobalTheory.MumPull.exists_pull | exact GlobalTheory.MumPull.exists_pull | (intros; apply GlobalTheory.MumPull.exists_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataValuesUltrametricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationData_values_ultrametric : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∃ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN := by
  first | exact @GlobalTheory.IntGauge.exists_intN | exact GlobalTheory.IntGauge.exists_intN | (intros; apply GlobalTheory.IntGauge.exists_intN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.UT

set_option maxHeartbeats 1000000

namespace GlobalTheory.UT

open GlobalTheory.EndData in

theorem exists_degenerationEndomorphism_of_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif I D A G, ∀ (aG : G ⟶ G) (aA : A.A ⟶ A.A), IsMonHom aG → IsMonHom aA → (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA → ∃ E : EndU U.toUnifPre, E.aG = aG ∧ E.aA = aA := by
  intro R _ _ I hR D A G _ _ _ U aG aA hG hA hext
  have hL := GlobalTheory.firstFiveLaws
  have hC := hR.2.2.2
  have hB := D.toPre.P.isLB
  obtain ⟨aB, haB, hq⟩ := exists_abelian hL hR U.toUnifPre aG
  obtain ⟨h, hh⟩ := T.uniformisation_endomorphism_character_map_constant hL R I hR D A G U.toUnifPre aG hG
  choose t ht hi using hh
  choose v hv vv using fun χ e => T.exists_gen_of_torusEnd_compat R I D.toPre e G (U.gt e) ((Over.pullback (thick R I e)).map aG) aB h (t e)
    inferInstance (ht e) (hi e) (hq e) χ
  have down : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      val ((U.gt (e + 1)).t χ) (r ≫ thickMap R I e G) z J = val ((U.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U.gt_t e χ) r)
  choose u hu uv using fun χ => T.exists_generator_of_compatible_thickening_generators R I hC D.toPre.P.A D.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ D.toPre.P.L _ _ _ _ hB (fun _ _ => rfl)
    (v χ) (hv χ) (fun e z J hJ => by
      have := (U.gt e).q_flat
      have := (U.gt e).q_surj
      refine val_eq_of_flat hB _ _ _ _ (fun k => ?_) (U.gt e).q.left (fun x J hJ => ?_) z J hJ
      · rw [← Category.assoc, trans_fst, Category.id_comp]
      · have k₁ := vv χ (e + 1) _ (𝟙 _ ≫ thickMap R I e G) x J hJ
        have k₀ := vv χ e _ (𝟙 _) x J hJ
        rw [down _ _ _ _ _ _ hJ, Category.assoc, trans_map, ← Category.assoc, down _ _ _ _ _ _ hJ, k₀,
          Category.id_comp, Category.id_comp, UnifCompare.trans_comp_q] at k₁
        rw [Category.comp_id]
        exact (mul_left_cancel k₁).symm)
  refine ⟨⟨aG, aA, aB, hG, hA, haB, h, hext, hq, fun e => ⟨t e, ht e, hi e⟩, u, fun χ => ⟨hu χ, ?_⟩,
    fun e χ Z x z J hJ => ?_⟩, rfl, rfl⟩
  · refine corr_of_val hB fun y J hJ => Eq.trans ?_ (val_one _).symm
    refine val_eq_one I hB (fun V _ k => ?_) _ (pullGen_isGen _ _ _ _ (hu χ) _) (fun e z J hJ => ?_) y J hJ
    · refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) (prod_unit D.toPre (𝟙 _) (h χ) k).1
        (prod_unit D.toPre aB χ k).2).trans ((_root_.mul_one _).trans (Fintype.prod_empty _).symm))
    · have := (U.gt e).q_hom
      have k := vv χ e _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul, ← uv χ e _ _ z J hJ] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D.toPre.P.A) =
        η[thickObj R I e D.toPre.P.A] := by simp [Hom.one_def]
      rw [o] at k
      exact (val_pull hJ _ _ _).trans ((congrArg (fun p => val (u χ) p z J)
        (UnitValue.eSec_pullback_fst (thick R I e) D.toPre.P.A).symm).trans k.symm)
  · refine (vv χ e Z x z J hJ).trans (congrArg (_ * ·) ((uv χ e Z _ z J hJ).symm.trans ?_))
    exact congrArg (fun p => val (u χ) p z J) (Category.assoc _ _ _)

open GlobalTheory.EndRosati GlobalTheory.CechPic in

theorem rosatiAdjoint_and_linear_of_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif I D A G, ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → RosatiAdj A.A A.L E.aA E'.aA ∧ RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB ∧ (∀ χ, D.toPre.c (E.h χ) = D.toPre.c χ ≫ E'.aB) ∧ ∀ χ, D.toPre.c (E'.h χ) = D.toPre.c χ ≫ E.aB := by
  intro R _ _ I hR D A G _ _ hG U E E' H
  have hLL := GlobalTheory.firstFiveLaws
  have hGF := hLL.1.globalFns
  obtain ⟨-, -, -, hC⟩ := hR
  have := E.homG
  have := E'.homG
  have := E.homB
  have := E'.homB
  have := hG.geomConnected
  obtain ⟨u, hu, h₀⟩ := (NormRos.normRos_of_lbIso _ G U.LG.L U.LG.isLB E.aG E'.aG H).1
  have hP : AbLaw.IsProjBy D.toPre.P.A.hom := AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)
  have hB : RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB :=
    loc_gen_of_thickenings hGF I _ (AbelianSchemeGerms.isAbelianScheme_tensor _ _ D.toPre.P.isAb D.toPre.P.isAb)
      (AbLaw.isProjBy_tensor R _ _ hP hP) D.toPre.P.isLB _ _ fun e => by
      have := EndTorus.connectedSpace_thickening I e
      have : GeometricallyConnected (thickObj R I e G).hom :=
        inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
      have : ConnectedSpace (thickObj R I e G).left :=
        GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
      exact exists_gen_thick U.toUnifPre e (E.q_lin e) (E'.q_lin e)
        (FamGerm.surjective_appTop_sq_cube U.toUnifPre).2 u hu h₀
  obtain ⟨r, hr, -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB E.aB E'.aB hB
  refine ⟨rosatiAdj_generic U.toUnifPre E.ext E'.ext u hu, hB, fun χ => ?_, fun χ => ?_⟩
  · have h₁ := cls_of_gen D.toPre E.aB χ _ (E.u χ) (E.u_norm χ).1
    have h₂ := cls_of_rosati D.toPre.P.isLB r hr (𝟙 _) (toUnit _ ≫ D.toPre.c χ)
    rw [Category.id_comp, Category.assoc] at h₂
    refine eq_of_translate_cls D.toPre.P.isLB D.toPre.P.ktriv _ _ ?_
    linear_combination (norm := abel) h₁ + h₂
  · have h₁ := cls_of_gen D.toPre E'.aB χ _ (E'.u χ) (E'.u_norm χ).1
    have h₂ := cls_of_rosati D.toPre.P.isLB r hr (toUnit _ ≫ D.toPre.c χ) (𝟙 _)
    rw [Category.id_comp, Category.assoc, mul_comm _ (𝟙 D.toPre.P.A), mul_comm _ E'.aB] at h₂
    refine eq_of_translate_cls D.toPre.P.isLB D.toPre.P.ktriv _ _ ?_
    linear_combination (norm := abel) h₁ - h₂

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeOneObstructionClass
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem exists_isOb1 : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsFun → L'.IsFun → L.IsLift L' n l → ∀ w : Glob1 F, ∃ c, L.IsOb1 L' n l α w c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C' _ F' L L' n l hL hL' hl w
  classical
  have hdiff : ∀ (T T' : C') (a : T ⟶ T') (b : L.B (n.G.obj T)),
      (L'.ρ a).comp (l T) b - (l T').comp (L.ρ (n.G.map a)) b ∈ I.map (algebraMap R (L'.B T')) := by
    intro T T' a b
    rw [← L'.ker, map_sub, sub_eq_zero]
    simp only [AlgHom.comp_apply, L'.nat]
    rw [hl, hl, L.nat]
    exact (n.naturality a _).symm
  have hκ : ∀ (T T' : C') (a : T ⟶ T'), ∃ κ : Ω[F.obj (n.G.obj T)⁄R₀] →+ L'.B T',
      IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) κ := fun T T' a ↦
    ((theta_classify R R₀ (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L'.B T') I hI π hπ (L.p _) (L.semi _)
      (L.surj _) (L.ker _) _).1 _ (hdiff T T' a)).exists
  choose κ hκ using hκ
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F'.obj T →+ L'.B T, α.IsSig (L'.p T) σ := fun T ↦
    GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L'.B T) (F'.obj T) (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T)
  choose σ hσ using hσ
  have hz : ∀ (T T' : C') (a : T ⟶ T'), ∃ y : R₁ ⊗[R₀] F'.obj T', α.KerQ y ∧ σ T' y = κ T T' a (w.1 _) :=
    fun T T' a ↦ (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L'.B T') (F'.obj T') (L'.p T') (L'.semi T')
      (L'.surj T') (L'.ker T') (σ T') (hσ T')).2.2.2 _ ((hκ T T' a).mem _)
  choose z hzq hzs using hz

  have hcomp : ∀ (T T' T'' : C') (a : T ⟶ T') (b : T' ⟶ T'') (x : Ω[F.obj (n.G.obj T)⁄R₀]),
      κ T T'' (a ≫ b) x = L'.ρ b (κ T T' a x) + κ T' T'' b (p1 F (n.G.map a) x) := by
    intro T T' T'' a b x
    have t1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _)
      (L'.B T') (L'.B T'') _ _ _ (hκ T T' a)).1 (L'.ρ b)
    have t2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj T')) (F.obj (n.G.obj T')) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _)
      (L'.B T'') (L'.B T'') _ _ _ (hκ T' T'' b)).2 (L.ρ (n.G.map a)) (mp F (n.G.map a)) (fun y ↦ L.nat _ y)
    have e0 : ((L'.ρ b).comp (l T')).comp (L.ρ (n.G.map a)) = (L'.ρ b).comp ((l T').comp (L.ρ (n.G.map a))) :=
      AlgHom.ext fun _ ↦ rfl
    rw [e0] at t2
    have t3 := ((GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L'.B T'') _ _ _ _ _ t1).2.1 t2)
    have e1 : (L'.ρ b).comp ((L'.ρ a).comp (l T)) = (L'.ρ (a ≫ b)).comp (l T) :=
      AlgHom.ext fun y ↦ (hL' a b _).symm
    have e2 : ((l T'').comp (L.ρ (n.G.map b))).comp (L.ρ (n.G.map a)) = (l T'').comp (L.ρ (n.G.map (a ≫ b))) :=
      AlgHom.ext fun y ↦ by
        show l T'' (L.ρ (n.G.map b) (L.ρ (n.G.map a) y)) = l T'' (L.ρ (n.G.map (a ≫ b)) y)
        rw [Functor.map_comp, hL]
    rw [e1, e2] at t3
    have e3 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L'.B T'') _ _ ((l T'').comp (L.ρ (n.G.map (a ≫ b)))) _ _ (hκ T T'' (a ≫ b))).2.2.1 t3
    exact congrArg (fun f ↦ f x) e3
  let zc : Z1 (ext R₁ F') := ⟨fun T T' a ↦ z T T' a, fun T T' T'' a b ↦ by
    have sn := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L'.B T') (F'.obj T') (L'.p T') (L'.semi T') (L'.surj T')
      (L'.ker T') (L'.B T'') (F'.obj T'') (L'.p T'') (L'.semi T'') (L'.surj T'') (L'.ker T'') (L'.ρ b) (mp F' b)
      (fun y ↦ L'.nat b y) (σ T') (σ T'') (hσ T') (hσ T'')
    change z T T'' (a ≫ b) = extHom R₁ (mp F' b) (z T T' a) + z T' T'' b
    rw [← sub_eq_zero]
    haveI := L'.smooth T''
    refine GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L'.B T'') (F'.obj T'') (L'.p T'') (L'.semi T'') (L'.surj T'')
      (L'.ker T'') (σ T'') (hσ T'') _ ?_ ?_
    · have h1 := hzq T T'' (a ≫ b)
      have h2 := sn.2 _ (hzq T T' a)
      have h3 := hzq T' T'' b
      unfold Aug.KerQ at h1 h2 h3 ⊢
      rw [map_sub, map_add, h1, h2, h3]; simp
    · rw [map_sub, map_add, ← sn.1, hzs, hzs, hzs, hcomp, w.2 (n.G.map a)]
      simp⟩
  exact ⟨H1.mk _ zc, κ, σ, zc, hκ, hσ, rfl, fun T T' a ↦ ⟨hzq T T' a, hzs T T' a⟩⟩

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeTwoObstructionClass
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_isOb2 : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F), ∃ c, L.IsOb2 α w c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w
  have hθ : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ θ : Ω[F.obj T⁄R₀] →+ L.B T'',
      IsTheta I (L.p T) ((L.ρ b).comp (L.ρ a)) (L.ρ (a ≫ b)) θ := by
    intro T T' T'' a b
    obtain ⟨θ, hθ, -⟩ := (theta_classify R R₀ (L.B T) (F.obj T) (L.B T'') I hI π hπ (L.p T) (L.semi T)
      (L.surj T) (L.ker T) ((L.ρ b).comp (L.ρ a))).1 (L.ρ (a ≫ b)) (fun x ↦ by
        rw [← L.ker T'', map_sub, AlgHom.comp_apply, L.nat, L.nat, L.nat, mp_comp, sub_self])
    exact ⟨θ, hθ⟩
  choose θ hθ using hθ
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F.obj T →+ L.B T, α.IsSig (L.p T) σ := fun T ↦
    GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
  choose σ hσ using hσ
  have hz : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ y : R₁ ⊗[R₀] F.obj T'',
      α.KerQ y ∧ σ T'' y = θ T T' T'' a b (w.1 T) := fun T T' T'' a b ↦
    (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
      (L.ker T'') (σ T'') (hσ T'')).2.2.2 _ ((hθ T T' T'' a b).mem _)
  choose z hzK hzσ using hz
  have key : ∀ (T T' T'' T''' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T''') (x : Ω[F.obj T⁄R₀]),
      L.ρ c (θ T T' T'' a b x) + θ T T'' T''' (a ≫ b) c x =
        θ T T' T''' a (b ≫ c) x + θ T' T'' T''' b c (p1 F a x) := by
    intro T T' T'' T''' a b c x
    have h1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.B T'') (L.B T''') _ _ _
      (hθ T T' T'' a b)).1 (L.ρ c)
    have s1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ _ _ _ h1).2.1 (hθ T T'' T''' (a ≫ b) c)
    have h2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.B T''') (L.B T''') _ _ _
      (hθ T' T'' T''' b c)).2 (L.ρ a) (mp F a) (L.nat a)
    have s2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ _ _ _ h2).2.1 (hθ T T' T''' a (b ≫ c))
    rw [Category.assoc] at s1
    rw [AlgHom.comp_assoc] at s2
    have e := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ (L.ρ (a ≫ b ≫ c)) _ _ s1).2.2.1 s2
    have ex := DFunLike.congr_fun e x
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply] at ex
    exact ex.trans (add_comm _ _)
  have hZ : (fun T T' T'' a b ↦ z T T' T'' a b : C2 (ext R₁ F)) ∈ Z2 (ext R₁ F) := by
    intro T T' T'' T''' a b c
    haveI := L.smooth T'''
    haveI : Module.Flat R (L.B T''') := Algebra.Smooth.flat R _
    have nat := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'')
      (L.surj T'') (L.ker T'') (L.B T''') (F.obj T''') (L.p T''') (L.semi T''') (L.surj T''') (L.ker T''')
      (L.ρ c) (mp F c) (L.nat c) (σ T'') (σ T''') (hσ T'') (hσ T''')
    have em : ∀ y, mp (ext R₁ F) c y = extHom R₁ (mp F c) y := fun _ ↦ rfl
    rw [← sub_eq_zero]
    apply GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L.B T''') (F.obj T''') (L.p T''') (L.semi T''')
      (L.surj T''') (L.ker T''') (σ T''') (hσ T''')
    · have k1 := nat.2 _ (hzK T T' T'' a b)
      have k2 := hzK T T'' T''' (a ≫ b) c
      have k3 := hzK T T' T''' a (b ≫ c)
      have k4 := hzK T' T'' T''' b c
      unfold Aug.KerQ at k1 k2 k3 k4 ⊢
      rw [em]
      simp only [map_sub, map_add, k1, k2, k3, k4, sub_self, add_zero]
    · rw [em, map_sub, map_add, map_add, ← (nat.1 _), hzσ, hzσ, hzσ, hzσ, w.2 a, key, sub_self]
  exact ⟨H2.mk _ ⟨_, hZ⟩, θ, σ, ⟨_, hZ⟩, hθ, hσ, rfl, fun T T' T'' a b ↦ ⟨hzK T T' T'' a b, hzσ T T' T'' a b⟩⟩

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorPrimeToLFiniteAdeleStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_prime_to_l_finiteAdele : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (z : Af E), l.Prime → (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → Valued.v (z w) ≤ 1) → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((algebraMap E (Af E) (M : E) * z) w) ≤ 1 := by
  first | exact @GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to | exact GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to | (intros; apply GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentCocycleDefectOfCompatibleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descentCocycleDefect_of_compatible : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ), L.IsLB → DescCompat f L φ → ∃ D : Γ(Triple f, ⊤)ˣ, Defect f L φ D := by
  first | exact @GlobalTheory.DescDefect.defect_exists | exact GlobalTheory.DescDefect.defect_exists | (intros; apply GlobalTheory.DescDefect.defect_exists <;> assumption)
end

