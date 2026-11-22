import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3368
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3159
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3641
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenNearOfFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledFibreOpen

theorem eq_one_of_local {S' : Scheme.{0}} {G : Over S'} [GrpObj G] (T : Over S') (x : T ⟶ G)
    (h : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ x = 1) : x = 1 := by
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨U, hp, hx⟩ := h p
  refine ⟨U, hp, ?_⟩
  have h1 : (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ (1 : T ⟶ G) = 1 := MonObj.comp_one _
  rw [← h1] at hx
  exact congrArg (fun q => q.left) hx

theorem unit_residue : ∀ (S' : Scheme.{0}) (W : S'.Opens) (s : S'), s ∈ W → ∀ d : ℕ, IsUnit ((d : ℕ) : Γ(W.toScheme, ⊤)) → IsUnit ((d : ℕ) : S'.residueField s) := by
  intro S' W s hs d hd
  let x : W.toScheme := ⟨s, hs⟩
  have h1 : IsUnit ((d : ℕ) : W.toScheme.residueField x) := by
    have := hd.map (W.toScheme.evaluation ⊤ x trivial).hom
    simpa using this
  have hx : W.ι.base x = s := rfl
  rw [isUnit_iff_ne_zero] at h1 ⊢
  intro h0
  apply h1
  have := congrArg (Scheme.Hom.residueFieldMap W.ι x).hom (hx ▸ h0 : ((d : ℕ) : S'.residueField (W.ι.base x)) = 0)
  simpa using this

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison GlobalTheory.KerKilledLocal in

theorem kerKilledOn_of_global : ∀ (d : ℕ) (S' : Scheme.{0}) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (V : S'.Opens), (∀ (T : Over S') (x : T ⟶ G), Set.range T.hom.base ⊆ (V : Set S') → (∃ c : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, c.IsGen) → x ^ d = 1) → GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' G _ _ P V h T x hs
  apply down_injective G V
  rw [down_pow, down_one]
  let T' : Over S' := Over.mk (T.hom ≫ V.ι)
  let GV := (Over.pullback V.ι).obj G
  have hr : Set.range T'.hom.base ⊆ (V : Set S') := by
    rintro _ ⟨t, rfl⟩
    have h' : T'.hom.base t ∈ Set.range V.ι.base := ⟨T.hom.base t, rfl⟩
    rwa [Scheme.Opens.range_ι] at h'
  refine h T' (down G V x) hr ?_
  let Y : Over V.toScheme := Over.mk ((snd G T').left ≫ T.hom)
  have w1 : (fst G T').left ≫ G.hom = (G ⊗ T').hom := Over.w (fst G T')
  have w2 : (snd G T').left ≫ (T.hom ≫ V.ι) = (G ⊗ T').hom := Over.w (snd G T')
  let u : Y ⟶ GV := Over.homMk (pullback.lift (fst G T').left ((snd G T').left ≫ T.hom) (by
      rw [w1, Category.assoc, w2])) (pullback.lift_snd _ _ _)
  let v : Y ⟶ T := Over.homMk (snd G T').left rfl
  have heq : (lift u v).left ≫ (lift (snd GV T ≫ x) (fst GV T)).left ≫ pφ₂ V.ι G =
      (lift (snd G T' ≫ down G V x) (fst G T')).left ≫ 𝟙 _ := by
    rw [Category.comp_id]
    apply adelic_GL2_ext_of_local_components G
    · simp only [Category.assoc, pφ₂_fst]
      rw [lift_left_fst'_assoc, lift_left_fst']
      simp only [Over.comp_left, Category.assoc]
      rw [lift_left_snd'_assoc]
      rfl
    · simp only [Category.assoc, pφ₂_snd]
      rw [lift_left_snd'_assoc, lift_left_snd', lift_left_fst'_assoc]
      change pullback.lift _ _ _ ≫ pullback.fst G.hom V.ι = _
      rw [pullback.lift_fst]
  obtain ⟨t, ht⟩ := gen_pull3 P (pφ₂ V.ι G) _ (lift u v).left _ (𝟙 _) heq hs
  exact gen_chartPull (chartPullUnpull _ _ rfl) t ht

theorem comp_pow_overScheme_grpObj {S' : Scheme.{0}} {G T T' : Over S'} [GrpObj G] (u : T' ⟶ T) (x : T ⟶ G) :
    ∀ n : ℕ, u ≫ x ^ n = (u ≫ x) ^ n
  | 0 => by rw [pow_zero, pow_zero, MonObj.comp_one]
  | n + 1 => by rw [pow_succ, pow_succ, MonObj.comp_mul, comp_pow_overScheme_grpObj u x n]

theorem kerKilledOn_near_of_fibre : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → IsUnit ((d : ℕ) : Γ(W.toScheme, ⊤)) → ∀ s ∈ W, GlobalTheory.KerKilledNear.FibreKilled d G P s → ∃ V : S'.Opens, s ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' _ G _ _ P hA hP hg₁ hg₂ hsym W hamp hd s hs hfib
  obtain ⟨V₀, Z, i, hs₀, hmono, hfin, h1, hmul, hinv, hfac, hloc⟩ := GlobalTheory.T.exists_finite_kernel_near_diagonal_ample S' G P hA hP hg₁ hg₂ hsym W hamp s hs
  have hfibZ : ∀ (T : Over S') (z : T ⟶ Z), (∃ f : T.left ⟶ Spec (S'.residueField s),
      T.hom = f ≫ S'.fromSpecResidueField s) → (z ≫ i) ^ d = 1 := by
    rintro T z ⟨f, hf⟩
    have hT : Set.range T.hom.base ⊆ (V₀ : Set S') := by
      rintro _ ⟨p, rfl⟩
      have e : (f ≫ S'.fromSpecResidueField s).base p = s :=
        Set.mem_singleton_iff.mp (Scheme.range_fromSpecResidueField s ▸ Set.mem_range_self (f.base p))
      rw [hf, e]
      exact hs₀
    refine eq_one_of_local T _ fun p => ?_
    obtain ⟨U, hp, c, hc⟩ := hloc T z hT p
    refine ⟨U, hp, ?_⟩
    rw [comp_pow_overScheme_grpObj]
    exact hfib (Over.mk (U.ι ≫ T.hom)) _ ⟨U.ι ≫ f, by simp [hf]⟩ ⟨c, hc⟩
  obtain ⟨V, hsV, hVV₀, hV⟩ := GlobalTheory.T.finite_subgroup_killed_near_point_of_fibre S' G Z i V₀ d s hmono hs₀ hfin h1 hmul hinv (unit_residue S' W s hs d hd) hfibZ
  refine ⟨V, hsV, kerKilledOn_of_global d S' G P V fun T x hT hx => ?_⟩
  obtain ⟨z, rfl⟩ := hfac T x (hT.trans hVV₀) hx
  exact hV T z hT

end GlobalTheory.KerKilledFibreOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfForallMem
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual

namespace GlobalTheory.BirigLift

theorem mem_smul_top_of_forall_mem {R : Type} [CommRing R] (I : Ideal R) {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] (x : Module.Dual R P) (hx : ∀ c, x c ∈ I) :
    x ∈ I • (⊤ : Submodule R (Module.Dual R P)) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have e : x = ∑ i, x (f (Pi.single i 1)) • ((LinearMap.proj i : (Fin n → R) →ₗ[R] R) ∘ₗ s) := by
    ext c
    have hc : c = f (s c) := (LinearMap.congr_fun hs c).symm
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, smul_eq_mul]
    conv_lhs => rw [hc, pi_eq_sum_univ (s c), map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
    congr 3
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [e]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hx _) trivial

theorem apply_mem_of_mem_smul_top {R : Type} [CommRing R] (I : Ideal R) {P : Type*} [AddCommGroup P] [Module R P]
    {x : Module.Dual R P} (hx : x ∈ I • (⊤ : Submodule R (Module.Dual R P))) (c : P) : x c ∈ I := by
  refine Submodule.smul_induction_on (p := fun y : Module.Dual R P ↦ y c ∈ I) hx (fun r hr y _ ↦ ?_) fun y z hy hz ↦ ?_
  · rw [LinearMap.smul_apply, smul_eq_mul]; exact I.mul_mem_right _ hr
  · rw [LinearMap.add_apply]; exact I.add_mem hy hz

theorem exists_perfect_mod {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) {D H : Type*}
    [AddCommGroup D] [Module R D] [AddCommGroup H] [Module R₀ H] (red : D →ₛₗ[π] H)
    (φ : D →ₗ[R] D →ₗ[R] R) (ψ : H →ₗ[R₀] H →ₗ[R₀] R₀) (hπ : Function.Surjective π)
    (hψ : Function.Surjective ψ.flip) (hred : Function.Surjective red)
    (hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule R D))
    (hrel : ∀ x y, ψ (red x) (red y) = π (φ x y)) (l : D →ₗ[R] R) :
    ∃ z, ∀ x, l x - φ x z ∈ RingHom.ker π := by
  have hl : ∀ x, x ∈ (RingHom.ker π) • (⊤ : Submodule R D) → π (l x) = 0 := by
    intro x hx
    refine Submodule.smul_induction_on (p := fun y : D ↦ π (l y) = 0) hx (fun r hr y _ ↦ ?_) fun y z hy hz ↦ ?_
    · rw [map_smul, smul_eq_mul, map_mul, RingHom.mem_ker.1 hr, zero_mul]
    · rw [map_add, map_add, hy, hz, add_zero]
  let s := Function.surjInv hred
  have hs : ∀ h, red (s h) = h := Function.surjInv_eq hred
  have key : ∀ x x', red x = red x' → π (l x) = π (l x') := fun x x' e ↦ by
    have := hl (x - x') (hker _ (by rw [map_sub, e, sub_self]))
    rwa [map_sub, map_sub, sub_eq_zero] at this
  let l₀ : H →ₗ[R₀] R₀ :=
    { toFun h := π (l (s h))
      map_add' a b := by
        rw [key (s (a + b)) (s a + s b) (by rw [map_add, hs, hs, hs]), map_add, map_add]
      map_smul' r h := by
        obtain ⟨r', rfl⟩ := hπ r
        rw [key (s (π r' • h)) (r' • s h) (by rw [map_smulₛₗ, hs, hs]), map_smul, smul_eq_mul, map_mul]
        rfl }
  obtain ⟨w, hw⟩ := hψ l₀
  obtain ⟨z, rfl⟩ := hred w
  refine ⟨z, fun x ↦ RingHom.mem_ker.2 ?_⟩
  have e := LinearMap.congr_fun hw (red x)
  rw [LinearMap.flip_apply, hrel] at e
  rw [map_sub, e, sub_eq_zero]
  exact key _ _ (hs _).symm

end GlobalTheory.BirigLift

namespace GlobalTheory.BirigLift

theorem lagr_univ {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) {D : Type*} [AddCommGroup D] [Module R D]
    [Module.Finite R D] [Module.Projective R D] (φ : D →ₗ[R] D →ₗ[R] R) (hI : I ^ 2 = ⊥) (h2 : IsUnit (2 : R))
    (anti : ∀ x y, φ x y = -φ y x) (perf : ∀ l : D →ₗ[R] R, ∃ z, ∀ x, l x - φ x z ∈ I) (F N : Submodule R D)
    (hFN : IsCompl F N) (iso : ∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) :
    ∃ E N' : Submodule R D, IsCompl E N' ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧
      E ⊔ I • (⊤ : Submodule R D) = F ⊔ I • (⊤ : Submodule R D) := by
  haveI : Module.Free R D := Module.free_of_flat_of_isLocalRing
  let ε := (Module.finBasis R D).equivFun
  let ψ : (Fin (Module.finrank R D) → R) →ₗ[R] (Fin (Module.finrank R D) → R) →ₗ[R] R :=
    φ.compl₁₂ ε.symm.toLinearMap ε.symm.toLinearMap
  have hψ : ∀ x y, ψ x y = φ (ε.symm x) (ε.symm y) := fun _ _ ↦ rfl
  obtain ⟨E, N', hEN, hE, hEF⟩ := GlobalTheory.T.maximal_isotropic_lift_mod_ideal R I _ ψ hI h2 (fun x y ↦ by simp only [hψ]; exact anti _ _)
    (fun l ↦ by
      obtain ⟨z, hz⟩ := perf (l ∘ₗ ε.toLinearMap)
      refine ⟨ε z, fun x ↦ ?_⟩
      have := hz (ε.symm x)
      simpa [hψ] using this)
    (F.map ε.toLinearMap) (N.map ε.toLinearMap) ((Submodule.orderIsoMapComap ε).isCompl hFN)
    (fun x hx y hy ↦ by
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      simpa [hψ] using iso a ha b hb)
  refine ⟨E.map ε.symm.toLinearMap, N'.map ε.symm.toLinearMap,
    (Submodule.orderIsoMapComap ε.symm).isCompl hEN, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simpa [hψ] using hE a ha b hb
  · have := congrArg (Submodule.map ε.symm.toLinearMap) hEF
    rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range,
      ← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id] at this
    exact this

end GlobalTheory.BirigLift

namespace GlobalTheory.BirigLift

open GlobalTheory.Published.GrothendieckMessing in

theorem exists_lift_lam : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → IsUnit (2 : R) → ∀ P₀ : PolAV (Sp R₀), ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : P₀.A.left ⟶ A.left) (l : (P₀.A ⊗ P₀.A).left ⟶ (A ⊗ A).left) (Q : LB (A ⊗ A).left), IsAbelianScheme A ∧ IsGrpPullback P₀.A A (spMap π) i ∧ IsSquare i l ∧ Q.IsLB ∧ GlobalTheory.AbDual.IsAdditive Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ LBIso (Q.pull l) (abelian₂ P₀.A P₀.L) := by
  intro R R₀ _ _ _ _ _ π hπ hI2 h2 P₀
  have hI0 : RingHom.ker π ^ 2 = 0 := hI2
  let κ := divided₂ hI0
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hI0
  have ADD : GlobalTheory.Published.DualAbelianScheme := GlobalTheory.T.dualAbelianScheme_exists_biduality
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal_of_dualAbelianScheme ADD
  have GD : GlobalTheory.Published.GrothendieckDeformation := GlobalTheory.Published.grothendieckDeformation₂
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates ADD GlobalTheory.T.poincareDeRhamDuality_abelianScheme GlobalTheory.T.print_abelianLifting
  haveI := P₀.isAb.comm
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.T.abelianScheme_unobstructed_squareZero_affine R (RingHom.ker π) hI0 R₀ π hπ rfl P₀.A P₀.isAb
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim R A' hA'
  have C := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA' hg hA' hg h' h'
  have hΛ := isPerfect_lam P₀.isLB P₀.ktriv
  obtain ⟨φ₀, hφ₀⟩ := exists_isCorrForm C hΛ.isLB hΛ.zero_left hΛ.zero_right
  have anti := GlobalTheory.JetIsotropic.corrForm_antisymm C hΛ.isLB (GlobalTheory.FullSiegel.lam_symm P₀.isLB) hφ₀

  have HC := (GD R (RingHom.ker π) κ hκ R₀ π hπ rfl).1
  obtain ⟨bij, ⟨N0, hN0⟩, hAdm⟩ := HC g P₀.A A' i' h' hA' hg
  let e := LinearEquiv.ofBijective (crysToDR κ h') (HC.crysToDR_bijective h' hA' hg)
  have ee : ∀ xA, crysToDR κ h' (e.symm xA) = xA := e.apply_symm_apply
  letI : Algebra R R₀ := π.toAlgebra
  have hBC := (ADR.2.2.1 R A' g hA' hg R₀ P₀.A i' h').1
  obtain ⟨hfinA, hprojA, -⟩ := ADR.1.prim hA' hg
  haveI := hfinA
  haveI := hprojA
  haveI : Module.Finite R (Crys κ (spMap π) P₀.A) := Module.Finite.equiv e.symm
  haveI : Module.Projective R (Crys κ (spMap π) P₀.A) := Module.Projective.of_equiv e.symm

  let red : Crys κ (spMap π) P₀.A →ₛₗ[π] HdR P₀.A := hBC.bcMap.comp (crysToDR κ h')
  have hm : ∀ x, (crysRedMor κ rfl P₀.A).Corr x (red x) := fun x ↦
    (corr_crysToDR_iff rfl h' bij.2 x (red x)).1 (by exact hBC.corr_iff.2 rfl)
  have iso : LBIso ((abelian₂ P₀.A P₀.L).pull (Over.Hom.left (𝟙 (P₀.A ⊗ P₀.A)))) (abelian₂ P₀.A P₀.L) :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hΛ.isLB _) hΛ.isLB).1
      (by rw [GlobalTheory.CechPic.cls_pull hΛ.isLB, Over.id_left, GlobalTheory.CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ₀.pull hΛ.isLB (crysRedMor κ rfl P₀.A) (crysRedMor κ rfl P₀.A)
    (h := Over.Hom.left (𝟙 (P₀.A ⊗ P₀.A))) (by simp) (by simp) hΛ.isLB iso
  obtain ⟨perf, filL, -⟩ := (GlobalTheory.Published.AbelianDualCrystal.duality ADR P₀.isAb P₀.smoothDim P₀.isAb P₀.smoothDim
    hΛ).2 φ' hφ'
  have hrel : ∀ x y, φ' (red x) (red y) = π (φ₀ x y) := fun x y ↦ e' x (red x) y (red y) (hm x) (hm y)
  have hred : Function.Surjective red := by
    intro y
    let l : primDR A' →ₗ[R] R₀ :=
      { toFun c := y ((redMor h').pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨xA, hx⟩ := Module.projective_lifting_property (Algebra.linearMap R R₀) l hπ
    refine ⟨e.symm xA, ?_⟩
    show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
    rw [ee]
    exact hBC.corr_iff.1 fun c ↦ (LinearMap.congr_fun hx c).symm
  have hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule R (Crys κ (spMap π) P₀.A)) := by
    intro x hx
    have hc := hBC.corr_iff.2 hx
    have hmem := mem_smul_top_of_forall_mem (RingHom.ker π) (crysToDR κ h' x) fun c ↦
      RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))
    have := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) hmem
    rw [Submodule.map_smul''] at this
    have ex : e.symm.toLinearMap (crysToDR κ h' x) = x := e.symm_apply_apply x
    rw [ex] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hperf := exists_perfect_mod π red φ₀ φ' hπ perf.bijective_right.2 hred hker hrel

  have hFN : IsCompl (liftFil κ h') (N0.comap (crysToDR κ h')) :=
    (Submodule.orderIsoMapComap e).symm.isCompl hN0
  have hredFil : ∀ x ∈ liftFil κ h', red x ∈ Fil P₀.A := fun x hx ↦
    (hAdm (red x)).2 ⟨crysToDR κ h' x, hx, by exact hBC.corr_iff.2 rfl⟩
  have hFiso : ∀ x ∈ liftFil κ h', ∀ y ∈ liftFil κ h', φ₀ x y ∈ RingHom.ker π := fun x hx y hy ↦
    RingHom.mem_ker.2 ((hrel x y).symm.trans (((filL _).1 (hredFil x hx)) _ (hredFil y hy)))
  obtain ⟨E, N', hEN, hEiso, hEF⟩ := lagr_univ (RingHom.ker π) φ₀ hI2 h2
    (fun x y ↦ anti x y) hperf (liftFil κ h') _ hFN hFiso

  have shift : ∀ d d' (y : HdR P₀.A), d - d' ∈ (RingHom.ker π) • (⊤ : Submodule R (Crys κ (spMap π) P₀.A)) →
      (crysRedMor κ rfl P₀.A).Corr d y → (crysRedMor κ rfl P₀.A).Corr d' y := by
    intro d d' y hd H c
    rw [H c]
    have := RingHom.mem_ker.1 (apply_mem_of_mem_smul_top (RingHom.ker π) hd c)
    rw [LinearMap.sub_apply, map_sub, sub_eq_zero] at this
    exact this
  have hFE : ∀ y : HdR P₀.A, y ∈ Fil P₀.A ↔ ∃ d ∈ E, (crysRedMor κ rfl P₀.A).Corr d y := by
    intro y
    constructor
    · intro hy
      obtain ⟨xA, hxA, hc⟩ := (hAdm y).1 hy
      have d0F : e.symm xA ∈ liftFil κ h' := by
        show crysToDR κ h' (e.symm xA) ∈ Fil A'
        rw [ee]; exact hxA
      have hc0 : (crysRedMor κ rfl P₀.A).Corr (e.symm xA) y :=
        (corr_crysToDR_iff rfl h' bij.2 _ y).1 (by rw [ee]; exact hc)
      have hmem : e.symm xA ∈ E ⊔ (RingHom.ker π) • (⊤ : Submodule R (Crys κ (spMap π) P₀.A)) := by
        rw [hEF]; exact Submodule.mem_sup_left d0F
      obtain ⟨d, hd, j, hj, hdj⟩ := Submodule.mem_sup.1 hmem
      refine ⟨d, hd, shift _ _ y ?_ hc0⟩
      rw [← hdj, add_sub_cancel_left]; exact hj
    · rintro ⟨d, hd, hc⟩
      have hmem : d ∈ liftFil κ h' ⊔ (RingHom.ker π) • (⊤ : Submodule R (Crys κ (spMap π) P₀.A)) := by
        rw [← hEF]; exact Submodule.mem_sup_left hd
      obtain ⟨f, hf, j, hj, hfj⟩ := Submodule.mem_sup.1 hmem
      have hcf : (crysRedMor κ rfl P₀.A).Corr f y := shift d f y (by rw [← hfj, add_sub_cancel_left]; exact hj) hc
      exact (hAdm y).2 ⟨crysToDR κ h' f, hf, (corr_crysToDR_iff rfl h' bij.2 f y).2 hcf⟩

  obtain ⟨A, _, i, h, hA, hgA, hEq⟩ := GlobalTheory.RMDeform.exists_lift_abelian GD ADR κ hκ π hπ rfl h' hA' hg E ⟨N', hEN⟩ hFE
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback h h
  obtain ⟨Q, hQ, -, -, a₁, a₂, eQ⟩ := GlobalTheory.BirigidLift.exists_lift GD ADR ADC hκ hπ rfl hA hgA hA hgA h h l₁ l₂
    P₀.isLB P₀.ample P₀.isLB P₀.ample hΛ.isLB hΛ.zero_left hΛ.zero_right hφ₀ (by rw [hEq]; exact hEiso)
  exact ⟨A, _, i, l, Q, hA, h, ⟨l₁, l₂⟩, hQ, a₁, a₂, eQ⟩

end GlobalTheory.BirigLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianUniformizationLinearActionTransfer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorTrait

theorem exists_trait_of_unif (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] (hR : Base R₀)
    (D₀ : DegData R₀ (maximalIdeal R₀)) (A₀ : PolAV (Sp (FractionRing R₀))) (G₀ : Over (Sp R₀)) [GrpObj G₀]
    [IsCommMonObj G₀] (hG : IsSemiAbelian G₀) (U₀ : Unif (maximalIdeal R₀) D₀ A₀ G₀) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₀ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW)
      (_ : IsCommMonObj GW) (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W)))
      (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧
      IsGrpPullback GW G₀ (spMap φ) β ∧ LBIso UW.LG.L (U₀.LG.L.pull β) ∧ Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  have := hR.2
  have := hR.1.1
  obtain ⟨W, _, _, _, φ, hW, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R₀ (maximalIdeal R₀)
  haveI hloc : IsLocalHom φ := ((IsLocalRing.local_hom_TFAE φ).out 0 4).mpr hc
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨DW, hD, AW, UW, hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR.1 hW' φ hφ (map_maximalIdeal_le φ) hG U₀
  have hb : (Iso.refl ((Over.pullback (specOf φ)).obj G₀)).hom.left ≫ pullback.fst G₀.hom (specOf φ) =
      pullback.fst G₀.hom (specOf φ) := Category.id_comp _
  refine ⟨W, _, inferInstance, inferInstance, φ, (Over.pullback (specOf φ)).obj G₀, inferInstance, inferInstance,
    (Iso.refl ((Over.pullback (specOf φ)).obj G₀)).hom.left ≫ pullback.fst G₀.hom (specOf φ), DW, AW, UW, hW, hφ, hloc,
    ?_, ⟨hP.lg.choose, hP.lg.choose_spec.1⟩, ⟨hD⟩⟩
  exact (isGrpPullback_pullback G₀ (spMap φ)).congr rfl hb.symm

theorem factor_unif_at_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (D₀ : DegData R₀ (maximalIdeal R₀)) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₀ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), FinExt ρ₀ ∧ Nonempty (IsPullDeg ρ₀ D.toPre D₀.toPre) ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₀ (spMap φ) β ∧ LBIso UW.LG.L (P.L.L.pull β) ∧ Nonempty (IsPullDeg φ D₀.toPre DW.toPre) ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hO G _ _ hG inc pr hinc hpr h1 h2
  obtain ⟨R₉, _, _, _, ρ₉, G₉, _, _, β₉, β₉₂, P₉, A₉, gen₉, a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    GlobalTheory.T.exists_finExt_cubicalSymmetric_even_factor R hR D D' F hA A' G' hG' U' oA oG hO G hG inc pr hinc hpr h1 h2
  obtain ⟨R₀, _, _, _, ρ₀, D₀, G₀, _, _, β₀, β₀₂, P, A₀, gen₀, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ :=
    GlobalTheory.T.semiabelian_uniformization_linear_action_descent R hR D D' F A' G' hG' U' oA oG hO G hG inc pr hinc hpr h1 h2 R₉ ρ₉ G₉ β₉ β₉₂ P₉ A₉ gen₉ a1 a2 a3 a4 a5 a6 a7 a8
  haveI := hR.2
  have hR₀ : Base R₀ := ⟨c1.1, charZero_of_injective_ringHom c1.2.1⟩
  obtain ⟨D'', U'', hLG, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R₀ hR₀ G₀ P c5 c7 A₀ gen₀ c8 c9
  obtain ⟨W, _, _, _, φ, GW, _, _, β, DW, AW, UW, w1, w2, w3, w4, w5, -⟩ := exists_trait_of_unif R₀ hR₀ D'' A₀ G₀ c5 U''
  rw [hLG] at w5
  exact ⟨R₀, _, _, _, ρ₀, D₀, G₀, _, _, β₀, β₀₂, P, W, _, _, _, φ, GW, _, _, β, DW, AW, UW, c1, c2, c3, c4, c5, w1, w2, w3,
    w4, w5, c10 W w1 φ w2 w3 GW β DW AW UW w4 w5, c6⟩

end GlobalTheory.Mum.FactorTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsDifferAffineTwoMembersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedSum_exponents_differ_affine_two_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∃ ε1 ε2 : X₁.S.Gam → X₁.S.Gam → ℕ, (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ (ε1 (lab c) τ)) ∧ (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y2 → C → V2, 𝔪2.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪2 lab T sg c τ (ε2 (lab c) τ)) ∧ ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((ε1 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((ε2 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  first | exact @GlobalTheory.GSep.twistSum_exp_affine | exact GlobalTheory.GSep.twistSum_exp_affine | (intros; apply GlobalTheory.GSep.twistSum_exp_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitsFourierTermsAllLevelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_classicalTraits_fourierTerms_all_levels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → Φ.Four !![(1 : ℤ)] (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.UPoinc.four_of_classical | exact GlobalTheory.UPoinc.four_of_classical | (intros; apply GlobalTheory.UPoinc.four_of_classical <;> assumption)
end

