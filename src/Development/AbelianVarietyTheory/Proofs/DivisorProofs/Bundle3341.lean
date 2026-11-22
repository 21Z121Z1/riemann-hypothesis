import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3332
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedArchIntegralEqSumClosureIntegrals
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem logSec_restr_secPull {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} (N : HermLB p) (t : N.B.Sec)
    (i : Y ⟶ X) (σ : k →+* ℂ) :
    (MLine.ofHerm (N.restr i) σ).logSec (Cartier.secPull t i) =
      fun y => (MLine.ofHerm N σ).logSec t (ptMap i rfl σ y) :=
  funext fun y => congrArg (fun a => Real.log a / 2) ((N.φ σ).nsq_pull_secPull i rfl t y)

theorem resArch_eq_finsum_cycInt : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → HermLB p) (N : HermLB p) (t : N.B.Sec) (z : X), Order.coheight z = 1 → z ∈ nonzeroLocus t → MixHt.resArch L N t z = ∑ᶠ σ : k →+* ℂ, cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t) z := by
  intro hP k _ X _ _ p e hX L N t z hz htz
  have hamb : IsAmb p := isAmb_of_isArithVar hX
  have hgen : genericPoint (clo z) ∈ nonzeroLocus (Cartier.secPull t (cloι z)) := by
    rw [Cartier.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rw [cloι_genericPoint]; exact htz
  have hd : topologicalKrullDim (clo z) = (e + 1 : ℕ) :=
    ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k X p hamb (e + 1) hX.dim_eq).2 z (genericPoint (clo z)) hz).1
  have hamb' : IsAmb (cloι z ≫ p) := hamb.sub (cloι z)
  have hc (σ : k →+* ℂ) := (GlobalTheory.T.mixed_chern_integral_point_closure_closed_subscheme k X (clo z) p (cloι z ≫ p) σ hX.isProjOver (cloι z) rfl e
    (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t)).2
  simp only [cloι_genericPoint] at hc
  refine (dif_pos hgen).trans ?_
  rcases isArithVar_or_isEmpty hamb' hd with hv | hE
  · refine (GlobalTheory.T.mixedArchLogNormIntegral_eq_sum_embeddings hP k (clo z) (cloι z ≫ p) e hv (fun a => (L a).restr (cloι z)) (N.restr (cloι z))
      (Cartier.secPull t (cloι z)) hgen).trans (finsum_congr fun σ => ?_)
    rw [hc σ, logSec_restr_secPull]
    rfl
  · refine (mixArch_eq_zero_of_isEmpty hE _ _ _).trans (finsum_eq_zero_of_forall_eq_zero fun σ => ?_).symm
    rw [hc σ]
    haveI := hE σ
    simp only [Mix.int, MeasureTheory.integral_of_isEmpty, sub_zero]

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedLineBundleTrivialOfTorsionGeometricFib
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.AbDual

noncomputable section

namespace GlobalTheory.RigTorsTriv

theorem triv_of_geometricFibres : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over S) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit ((k : Γ(S, ⊤))) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (M.pull (pullback.fst A.hom y)).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
  intro S A _ _ hA M hM hrig k hk hpow hfib
  have key : ∀ {Y : Scheme.{0}} (f : Y ⟶ A.left), (∃ t : (M.pull f).Gen, t.IsGen) ↔ pull f (cls M hM) = 0 :=
    fun f => (cls_eq_zero_iff (pull_isLB hM f)).symm.trans (by rw [cls_pull hM f])
  have hsurj : ∀ V : S.Opens, Function.Surjective (A.hom ∣_ V).appTop.hom := fun V => by
    have hG : Out.GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
    have h1 := hG _ _ (Out.TLinPf.isAb_pullback V.ι A hA)
    let e := IsPullback.isoIsPullback _ _ (isPullback_morphismRestrict A.hom V)
      (IsPullback.of_hasPullback A.hom V.ι).flip
    have he : e.hom ≫ pullback.snd A.hom V.ι = A.hom ∣_ V := IsPullback.isoIsPullback_hom_fst _ _ _ _
    have hi : Function.Surjective e.hom.appTop.hom := by
      have : IsIso (e.hom.app ⊤) := inferInstance
      exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
    rw [← he, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    exact hi.comp h1.2
  have hc0 : pull (1 : 𝟙_ (Over S) ⟶ A).left (cls M hM) = 0 := (key _).1 hrig
  have hkM : k • cls M hM = 0 := by
    have h := (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).2 hpow
    rw [cls_linComb hM] at h
    simpa [pull_id] using h
  refine GlobalTheory.CubeGlue.triv_of_locally_triv hM A.hom (1 : 𝟙_ (Over S) ⟶ A).left
    (by simpa using Over.w (1 : 𝟙_ (Over S) ⟶ A)) hsurj hrig ?_
  intro s
  obtain ⟨R, j, hj, ⟨p, hp⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial
  let j' : Sp R ⟶ S := j
  haveI : IsOpenImmersion j' := hj
  let A' := (Over.pullback j').obj A
  have hA' : IsAbelianScheme A' := Out.TLinPf.isAb_pullback j' A hA
  let φ := pullback.fst A.hom j'
  have hM' : (M.pull φ).IsLB := pull_isLB hM φ
  have key' : ∀ {Y : Scheme.{0}} (f : Y ⟶ A'.left),
      (∃ t : ((M.pull φ).pull f).Gen, t.IsGen) ↔ pull (f ≫ φ) (cls M hM) = 0 := fun f =>
    (cls_eq_zero_iff (pull_isLB hM' f)).symm.trans (by rw [cls_pull hM' f, cls_pull hM φ, pull_comp])
  have hone : (1 : 𝟙_ (Over (Sp R)) ⟶ A').left ≫ φ = j' ≫ (1 : 𝟙_ (Over S) ⟶ A).left := by
    have h := GlobalTheory.TorsFrameInt.one_comm (isGrpPullback_pullback A j')
    rw [Hom.one_def, Hom.one_def]
    simpa using h
  have hrig' := (key' _).2 (by rw [hone, pull_comp, hc0, map_zero])
  have hk' : IsUnit (k : R) := by
    have h := hk.map ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp j'.appTop.hom)
    simpa using h
  have hpow' : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (M.pull φ) k).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM' _ _)).1 ?_
    rw [cls_linComb hM']
    simp [pull_id, cls_pull hM φ, ← map_nsmul, hkM]
  let P : PrimeSpectrum R := p
  haveI : P.asIdeal.IsPrime := P.isPrime
  let F := AlgebraicClosure P.asIdeal.ResidueField
  let ψ : R →+* F := (algebraMap P.asIdeal.ResidueField F).comp (algebraMap R P.asIdeal.ResidueField)
  have hfib' : ∃ t : ((M.pull φ).pull (pullback.fst A'.hom (spMap ψ))).Gen, t.IsGen := by
    rw [key']
    have h0 := (key _).1 (hfib F (spMap ψ ≫ j'))
    have e : pullback.fst A'.hom (spMap ψ) ≫ φ =
        pullback.lift (pullback.fst A'.hom (spMap ψ) ≫ φ) (pullback.snd A'.hom (spMap ψ))
          (by
            have hc : pullback.fst A'.hom (spMap ψ) ≫ A'.hom = pullback.snd A'.hom (spMap ψ) ≫ spMap ψ :=
              pullback.condition
            rw [Category.assoc, pullback.condition, ← Category.assoc]
            exact (congrArg (· ≫ j') hc).trans (Category.assoc _ _ _))
          ≫ pullback.fst A.hom (spMap ψ ≫ j') := (pullback.lift_fst _ _ _).symm
    rw [e, pull_comp, h0, map_zero]
  obtain ⟨r, hr, ht⟩ := GlobalTheory.T.localTriviality_of_noetherian_descent (GlobalTheory.T.torsionLineBundle_trivial_basicOpen_of_trivial_fibre GlobalTheory.T.exists_generator_torsion_bundle_abelianScheme_sqZero) R A' hA' (M.pull φ) hM' hrig' k hk' hpow' F ψ hfib'
  have hrp : P ∈ PrimeSpectrum.basicOpen r := by
    intro hm
    apply hr
    show algebraMap _ F (algebraMap R P.asIdeal.ResidueField r) = 0
    rw [(Ideal.algebraMap_residueField_eq_zero).2 hm, map_zero]
  refine ⟨j' ''ᵁ PrimeSpectrum.basicOpen r, ⟨p, hrp, hp⟩, ?_⟩
  refine (key _).2 ?_
  let D : (Sp R).Opens := PrimeSpectrum.basicOpen r
  let W := A.hom ⁻¹ᵁ (j' ''ᵁ D)
  have h1 : Set.range (W.ι ≫ A.hom) ⊆ Set.range j' := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨q, -, hq⟩ := y.2
    exact ⟨q, hq⟩
  let m : W.toScheme ⟶ A'.left :=
    pullback.lift W.ι (IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1) (IsOpenImmersion.lift_fac _ _ _).symm
  have h2 : Set.range m ⊆ Set.range (A'.hom ⁻¹ᵁ D).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have e : m ≫ A'.hom = IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1 := pullback.lift_snd _ _ _
    show (m ≫ A'.hom) y ∈ D
    rw [e]
    obtain ⟨q, hqD, hq⟩ := y.2
    have : IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1 y = q := j'.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]; exact hq.symm)
    rw [this]; exact hqD
  have hfac : W.ι = IsOpenImmersion.lift (A'.hom ⁻¹ᵁ D).ι m h2 ≫ (A'.hom ⁻¹ᵁ D).ι ≫ φ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (pullback.lift_fst _ _ _).symm
  rw [hfac, pull_comp, (key' _).1 ht, map_zero]

end GlobalTheory.RigTorsTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelExtendsNoetherianNormalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.SympLevelExt

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem map_linComb {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {T : Over S}
    {T' : Over S'} (ρ : (T ⟶ A) →* (T' ⟶ A')) {n : ℕ} (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) :
    ρ (linComb y a) = linComb (fun i => ρ (y i)) a := by
  unfold linComb
  rw [map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  exact map_pow ρ (y i) (a i)

theorem dense_of_bot_mem {R : Type} [CommRing R] [IsDomain R] (D : Set (Sp R))
    (hD : (⊥ : PrimeSpectrum R) ∈ D) : Dense D := by
  intro p
  have hs : (⊥ : PrimeSpectrum R) ⤳ p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  exact closure_mono (Set.singleton_subset_iff.2 hD) (specializes_iff_mem_closure.1 hs)

theorem extend_torsion {R F : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    [IsProper G.hom] (n : ℕ) (hn : IsUnit (n : R))
    (x : Over.mk ((baseOver (Sp F)).hom ≫ spMap (algebraMap R F)) ⟶ G) (hx : x ^ n = 1) :
    ∃ σ : baseOver (Sp R) ⟶ G, σ ^ n = 1 ∧ spMap (algebraMap R F) ≫ σ.left = x.left := by
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  have hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := fun p => by
    refine ⟨inferInstance, ?_⟩
    have : (PrimeSpectrum.asIdeal p).IsPrime := PrimeSpectrum.isPrime p
    have h := StructureSheaf.IsLocalization.to_stalk R p
    exact @isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk p) _ _ (_) _ _
      (PrimeSpectrum.asIdeal p).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h
  have j₁ : IsPreimmersion (spMap (algebraMap R F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have j₂ : Flat (spMap (algebraMap R F)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat F (nonZeroDivisors R)))
  have j₃ : IsDominant (spMap (algebraMap R F)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro a ha
    have : a = 0 := IsFractionRing.injective R F (ha.trans (map_zero _).symm)
    rw [this]; exact Ideal.zero_mem _)⟩
  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_section_of_pow_eq_one hT (spMap (algebraMap R F)) G n hn' _ x hx (𝟙 _)
    (by simp)
  let σ' : baseOver (Sp R) ⟶ G := Over.homMk σ (by simpa using hσ₁)
  have hσ : spMap (algebraMap R F) ≫ σ'.left = x.left := by
    show spMap (algebraMap R F) ≫ σ = x.left
    simpa using hσ₂
  refine ⟨σ', ?_, hσ⟩
  let U : Over.mk ((baseOver (Sp F)).hom ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R F)) (by simp)
  have hU : U ≫ σ' = x := Over.OverMorphism.ext hσ
  have e : U ≫ σ' ^ n = U ≫ 1 := by rw [MonObj.comp_pow, MonObj.comp_one, hU, hx]
  exact over_points_ext_of_injective _ G R F (algebraMap R F) (IsFractionRing.injective R F) _ _ _
    (congrArg (fun q => q.left) e)

end GlobalTheory.SympLevelExt

namespace GlobalTheory.SympLevelExt

theorem generic_basis {R F : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    {Q : PolAV (Sp F)} (G : Over (Sp R)) [GrpObj G] (φ : Q.A.left ⟶ G.left)
    (hp : IsGrpPullback Q.A G (spMap (algebraMap R F)) φ) (k : ℕ) [NeZero k] (ze₀ : Γ(Sp F, ⊤)ˣ)
    (lev₀ : Out.Level Q k ze₀) (y : Fin (2 * Q.g) → (baseOver (Sp R) ⟶ G))
    (hy : ∀ i, (lev₀.pt i).left ≫ φ = spMap (algebraMap R F) ≫ (y i).left)
    (z : Over.mk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F)) ⟶ G) (hz : z ^ k = 1) :
    ∃! c : Fin (2 * Q.g) → ZMod k,
      linComb (fun i => (Over.homMk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F))
        (by simp) : Over.mk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F)) ⟶
          baseOver (Sp R)) ≫ y i) (fun i => (c i).val) = z := by
  let s : Sp (AlgebraicClosure F) ⟶ Sp F := spMap (algebraMap F (AlgebraicClosure F))
  let T : Over (Sp F) := Over.mk s
  let ρ := pushHom hp T
  have hinj : Function.Injective ρ := fun a b hab => by
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext
    · exact congrArg (fun q => q.left) hab
    · rw [Over.w a, Over.w b]
  have hsurj : ∀ w : Over.mk (T.hom ≫ spMap (algebraMap R F)) ⟶ G, ∃ a, ρ a = w := fun w =>
    ⟨Over.homMk (hp.1.lift w.left T.hom (Over.w w)) (hp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩
  have hcomp : ∀ i, ρ ((Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) =
      (Over.homMk (s ≫ spMap (algebraMap R F)) (by simp) :
        Over.mk (s ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)) ≫ y i := fun i => by
    apply Over.OverMorphism.ext
    show (s ≫ (lev₀.pt i).left) ≫ φ = (s ≫ spMap (algebraMap R F)) ≫ (y i).left
    rw [Category.assoc, hy, Category.assoc]
  have hlin : ∀ d : Fin (2 * Q.g) → ℕ,
      ρ (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) d) =
      linComb (fun i => (Over.homMk (s ≫ spMap (algebraMap R F)) (by simp) :
        Over.mk (s ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)) ≫ y i) d := fun d => by
    rw [map_linComb]
    simp only [hcomp]
  obtain ⟨a, rfl⟩ := hsurj z
  have ha : a ^ k = 1 := hinj (by rw [map_pow, hz, map_one])
  obtain ⟨c, hc⟩ := lev₀.span (AlgebraicClosure F) s a ha
  refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, ?_⟩
  · show linComb _ (fun i => (((c i : ℕ) : ZMod k)).val) = ρ a
    simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)]
    rw [← hlin, hc]
  · intro c' hc'
    have e : ρ (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i)
        (fun i => ((⟨(c' i).val, ZMod.val_lt (c' i)⟩ : Fin k) : ℕ))) = ρ a := by
      rw [hlin]; exact hc'
    have e' := lev₀.indep (AlgebraicClosure F) s _ c ((hinj e).trans hc.symm)
    funext i
    have := congrArg (fun f => ((f i : ℕ) : ZMod k)) e'
    simpa using this

end GlobalTheory.SympLevelExt

namespace GlobalTheory.SympLevelExt

theorem level_extends : ∀ {R₁ : Type} [CommRing R₁] (P₁ : PolAV (Sp R₁)) (R F : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field F] [Algebra R F] [IsFractionRing R F] (h : R₁ →+* R) (Q : PolAV (Sp F)) (φ : Q.A.left ⟶ P₁.A.left) (K : ℕ) (ze : Rˣ), 0 < K → IsUnit (K : R) → Q.g = P₁.g → IsGrpPullback Q.A P₁.A (spMap ((algebraMap R F).comp h)) φ → LBIso Q.L (P₁.L.pull φ) → Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap R F).toMonoidHom ze))) → ∃ (P : PolAV (Sp R)) (ψ : P.A.left ⟶ P₁.A.left), P.g = P₁.g ∧ IsGrpPullback P.A P₁.A (spMap h) ψ ∧ LBIso P.L (P₁.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ze)) := by
  intro R₁ _ P₁ R F _ _ _ _ _ _ _ h Q φ K ze hK hKu hg hpb hQL hlev
  obtain ⟨lev₀⟩ := hlev
  cases Q with
  | mk QA QisAb Qg Qsm QL QisLB Qrig Qsym Qamp Qkt =>
  dsimp only at hg
  subst hg
  have hL := abelianSchemeLaws_all.1
  haveI : NeZero K := ⟨hK.ne'⟩
  let j := spMap (algebraMap R F)
  let P : PolAV (Sp R) := StrictPull.polPull P₁ (spMap h)
  let ψ : P.A.left ⟶ P₁.A.left := pullback.fst P₁.A.hom (spMap h)
  have hψ : IsGrpPullback P.A P₁.A (spMap h) ψ := isGrpPullback_pullback P₁.A (spMap h)
  have hc : spMap ((algebraMap R F).comp h) = j ≫ spMap h := by
    simp only [spMap, j, CommRingCat.ofHom_comp, Spec.map_comp]
  have hw : φ ≫ P₁.A.hom = (QA.hom ≫ j) ≫ spMap h := by rw [hpb.1.w, hc, Category.assoc]
  let φ' : QA.left ⟶ P.A.left := hψ.1.lift φ (QA.hom ≫ j) hw
  have e₁ : φ' ≫ ψ = φ := hψ.1.lift_fst _ _ _
  have e₂ : φ' ≫ P.A.hom = QA.hom ≫ j := hψ.1.lift_snd _ _ _
  have hpb' : IsGrpPullback QA P.A j φ' := hψ.cancel (by rw [e₁, ← hc]; exact hpb) e₂
  have hQL' : LBIso QL (P.L.pull φ') := by
    refine LBIso.trans QisLB (pull_isLB P₁.isLB _) (pull_isLB P.isLB _) hQL ?_
    have := lbIso_pull_comp P₁.isLB ψ φ'
    rw [e₁] at this
    exact this
  have hP : IsProper P.A.hom := P.isAb.proper
  have := P.isAb.comm
  choose y hy₁ hy₂ using fun i : Fin (2 * P₁.g) =>
    extend_torsion (R := R) (F := F) P.A K hKu (pushHom hpb' (baseOver (Sp F)) (lev₀.pt i))
      (by rw [← map_pow, lev₀.torsion, map_one])
  have hy : ∀ i, (lev₀.pt i).left ≫ φ' = j ≫ (y i).left := fun i => (hy₂ i).symm
  have hKu' : IsUnit (K : Γ(Sp R, ⊤)) := by
    have := hKu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  let x : Sp (AlgebraicClosure F) ⟶ Sp R := spMap (algebraMap F (AlgebraicClosure F)) ≫ j
  have hx : (⊥ : PrimeSpectrum R) ∈ Set.range x := by
    obtain ⟨w⟩ : Nonempty (Sp (AlgebraicClosure F)) := inferInstance
    refine ⟨w, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R F) (Ideal.comap (algebraMap F (AlgebraicClosure F)) (PrimeSpectrum.asIdeal w)) = ⊥
    rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal w) (PrimeSpectrum.isPrime w),
      Ideal.comap_bot_of_injective _ (algebraMap F (AlgebraicClosure F)).injective,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective R F)]
  have hbasis := torsion_basis_of_dense (Sp R) P.A K (2 * P₁.g) y (Set.range x) P.isAb hK hKu' hy₁
    (dense_of_bot_mem _ hx) (fun p hp => ⟨AlgebraicClosure F, inferInstance, inferInstance, x, hp,
      fun z hz => generic_basis (Q := ⟨QA, QisAb, P₁.g, Qsm, QL, QisLB, Qrig, Qsym, Qamp, Qkt⟩) P.A φ' hpb' K _ lev₀ y hy z hz⟩)
  have hind : ∀ (F' : Type) [Field F'] [IsAlgClosed F'] (s : Spec (CommRingCat.of F') ⟶ Sp R)
      (c c' : Fin (2 * P.g) → Fin K),
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)) =
        linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c' i : ℕ)) →
      c = c' := by
    intro F' _ _ s c c' hcc
    obtain ⟨d, -, hd⟩ := hbasis F' s
      (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)))
      (DenseBasis.linComb_pow_eq_one _ (fun i => by rw [← MonObj.comp_pow, hy₁, MonObj.comp_one]) _)
    have h₁ := hd (fun i => ((c i : ℕ) : ZMod K)) (by simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)])
    have h₂ := hd (fun i => ((c' i : ℕ) : ZMod K)) (by simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)]; exact hcc.symm)
    funext i
    apply Fin.ext
    have := congrArg (fun f => (f i).val) (h₁.trans h₂.symm)
    simpa only [ZMod.val_natCast_of_lt (Fin.is_lt _)] using this
  obtain ⟨lev, -⟩ := level_of_generic_of_indep hL R F P ⟨QA, QisAb, P₁.g, Qsm, QL, QisLB, Qrig, Qsym, Qamp, Qkt⟩ φ'
    hpb' hQL' rfl K ze _ hKu rfl lev₀ y (fun i₀ i hi => by
      obtain rfl : i₀ = i := Fin.ext hi
      exact hy i₀) hind
  exact ⟨P, ψ, rfl, hψ, GlobalTheory.PolBaseChange.lbIso_refl P.isLB, ⟨lev⟩⟩

end GlobalTheory.SympLevelExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyGenericFibreHenselLineSubsingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_ht_one_genericFibre_of_sh_etale_cover : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) → ∀ i : ℤ, Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) 1 i) := by
  first | (exact @GlobalTheory.LocAcycDegOne.tateTwistCohomology_genericFibre_henselLine_subsingleton) | (exact GlobalTheory.LocAcycDegOne.tateTwistCohomology_genericFibre_henselLine_subsingleton) | (intros; apply GlobalTheory.LocAcycDegOne.tateTwistCohomology_genericFibre_henselLine_subsingleton  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRealisationLabelsInjectiveOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem realPt_comp_pow {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (u : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    u ≫ x ^ n = (u ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem realPt_inj_of_grpPullback : ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₂ : ThetaSys o₂ Ω₂) (ρ₂ : S₂.Real) {T : Scheme.{0}} (G : Over T) [GrpObj G] (f : Sp S₂.R ⟶ T) (φ : ρ₂.P.A.left ⟶ G.left), IsGrpPullback ρ₂.P.A G f φ → ∀ x y : S₂.Gam, (ρ₂.pt x).left ≫ φ = (ρ₂.pt y).left ≫ φ → x = y := by
  intro o₂ Ω₂ _ _ _ S₂ ρ₂ T G _ f φ hφ x y hxy
  have hpt : ρ₂.pt x = ρ₂.pt y := by
    ext
    exact hφ.1.hom_ext hxy (by simp only [Category.assoc, Over.w])
  have hzero : ρ₂.pt 0 = 1 := by
    have h := ρ₂.pt_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hsmul : ∀ (a : S₂.Gam) (n : ℕ), ρ₂.pt (n • a) = ρ₂.pt a ^ n := by
    intro a n
    induction n with
    | zero => rw [zero_smul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, ρ₂.pt_add, ih, pow_succ]
  have hkill : ∀ a : S₂.Gam, ρ₂.pt a ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [← hsmul]
    have : (S₂.r * S₂.N) • a = 0 := by
      funext i
      simp [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self]
    rw [this, hzero]
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap ((algebraMap Ω₂ K).comp (S₂.R.val : S₂.R →+* Ω₂))
  let u : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  have hz : (u ≫ ρ₂.pt x) ^ (S₂.r * S₂.N) = 1 := by
    rw [← realPt_comp_pow, hkill, MonObj.comp_one]
  obtain ⟨a, _, huniq⟩ := ρ₂.pt_bij K x₀ (u ≫ ρ₂.pt x) hz
  have h1 := huniq x rfl
  have h2 := huniq y (by rw [hpt])
  exact h1.trans h2.symm

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR : TraitExtSt := by
  first | exact @GlobalTheory.Poinc.traitExtSt | exact GlobalTheory.Poinc.traitExtSt | (intros; apply GlobalTheory.Poinc.traitExtSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDataTranslateOrderTwoIsTwistStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationData_translate_orderTwo_isTwist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g := by
  first | exact @GlobalTheory.MumCmp.isTwist_of_translate | exact GlobalTheory.MumCmp.isTwist_of_translate | (intros; apply GlobalTheory.MumCmp.isTwist_of_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPulledBackFactorSamePolarisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_pulledBackFactor_samePolarisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₉ : Type) [CommRing R₉] [IsDomain R₉] [IsLocalRing R₉] (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) [GrpObj G₉] [IsCommMonObj G₉] (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉), FinExt ρ₉ → IsGrpPullback G₉ G (spMap ρ₉) β₉ → Geo.Tor.IsSquare β₉ β₉₂ → IsSemiAbelian G₉ → LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) → ∀ (A₉ : PolAV (Sp (FractionRing R₉))) (D₉' : DegData R₉ (maximalIdeal R₉)) (U₉ : Unif (maximalIdeal R₉) D₉' A₉ G₉), U₉.LG = P₉.L → ∃ D₉ : DegData R₉ (maximalIdeal R₉), Nonempty (IsPullDeg ρ₉ D.toPre D₉.toPre) ∧ SamePol D₉.toPre D₉'.toPre := by
  first | exact @GlobalTheory.Mum.FactorIdent.samePol_pull | exact GlobalTheory.Mum.FactorIdent.samePol_pull | (intros; apply GlobalTheory.Mum.FactorIdent.samePol_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthCompositionStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_module_length_composition : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B C : Type) [AddCommGroup A] [Module (WittVector p k) A] [AddCommGroup B] [Module (WittVector p k) B] [AddCommGroup C] [Module (WittVector p k) C], (∀ (u : B →ₗ[(WittVector p k)] A) (v : C →ₗ[(WittVector p k)] B), Function.Injective u → Module.length (WittVector p k) (A ⧸ LinearMap.range (u ∘ₗ v)) = Module.length (WittVector p k) (A ⧸ LinearMap.range u) + Module.length (WittVector p k) (B ⧸ LinearMap.range v)) ∧ (Module.Free (WittVector p k) A → Module.Finite (WittVector p k) A → ∀ (n : ℕ) (u : A →ₗ[(WittVector p k)] A), (∀ a, u a = p ^ n • a) → Module.length (WittVector p k) (A ⧸ LinearMap.range u) = (n * Module.finrank (WittVector p k) A : ℕ)) ∧ ∀ L L' : Submodule (WittVector p k) A, L ≤ L' → Module.length (WittVector p k) (A ⧸ L) = Module.length (WittVector p k) (A ⧸ L') → Module.length (WittVector p k) (A ⧸ L) ≠ ⊤ → L = L' := by
  first | exact @GlobalTheory.Dieu.colength_add_and_pow_and_eq | exact GlobalTheory.Dieu.colength_add_and_pow_and_eq | (intros; apply GlobalTheory.Dieu.colength_add_and_pow_and_eq <;> assumption)
end

