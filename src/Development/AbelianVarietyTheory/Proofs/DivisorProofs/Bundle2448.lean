import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0012
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2382
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianAmpleSymmPreservedFieldBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_ample_symm_preserved_field_baseChange : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ L : LB A₀.left, L.IsLB → RelAmple A₀ L → LBIso (L.pull (GrpObj.inv : A₀ ⟶ A₀).left) L → IsAbelianScheme ((Over.pullback (spMap σ)).obj A₀) ∧ RelAmple ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) ∧ LBIso ((L.pull (pullback.fst A₀.hom (spMap σ))).pull (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left) (L.pull (pullback.fst A₀.hom (spMap σ))) := by
  first | exact @GlobalTheory.FieldBaseChange.abelian_ample_symm_baseChange | exact GlobalTheory.FieldBaseChange.abelian_ample_symm_baseChange | (intros; apply GlobalTheory.FieldBaseChange.abelian_ample_symm_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparison
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof.AbelianDeRhamFreeOfHodge

def extSqEquiv {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (E : M ≃ₗ[R] N) : ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 (E : M →ₗ[R] N)) (exteriorPower.map 2 (E.symm : N →ₗ[R] M))
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])

theorem extSqEquiv_ιMulti {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) (a b : M) :
    extSqEquiv E (exteriorPower.ιMulti R 2 ![a, b]) = exteriorPower.ιMulti R 2 ![E a, E b] := by
  change exteriorPower.map 2 (E : M →ₗ[R] N) _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem free_of (hC : GlobalTheory.Published.CrystallineSmoothLift) (hA : GlobalTheory.Published.AbelianHodgeDeRham)
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (s : A.left ⟶ Sp R) (hs : s = A.hom) :
    Module.Finite R (FirstDeRham s) ∧ Module.Projective R (FirstDeRham s) ∧
    (∀ p : PrimeSpectrum R, Module.rankAtStalk (FirstDeRham s) p = 2 * g) ∧
    ∃ e : ⋀[R]^2 (FirstDeRham s) ≃ₗ[R] SecondDeRham s,
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup _ a b := by
  subst hs
  haveI : Smooth A.hom := hab.smooth
  haveI : IsProper A.hom := hab.proper
  obtain ⟨⟨hfin, hproj, hrank⟩, ⟨eH, heH⟩, -⟩ := hA R A g hab hg
  obtain ⟨hbij, e2, he2⟩ := GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left A.hom inferInstance inferInstance inferInstance
  let E1 : FirstDeRham A.hom ≃ₗ[R] HH1 A.hom := LinearEquiv.ofBijective (cmp1 A.hom) hbij
  refine ⟨Module.Finite.equiv E1.symm, Module.Projective.of_equiv E1.symm, ?_, ?_⟩
  · intro p
    rw [Module.rankAtStalk_eq_of_equiv E1]
    exact hrank p
  · refine ⟨(extSqEquiv E1).trans (eH.trans e2.symm), fun a b => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, extSqEquiv_ιMulti, heH, LinearEquiv.symm_apply_eq]
    exact (he2 a b).symm

end GlobalTheory.Proof.AbelianDeRhamFreeOfHodge

open GlobalTheory.Proof.AbelianDeRhamFreeOfHodge in

theorem GlobalTheory.Proof.abelianDeRhamFree_of_hodge :
    GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRhamFree := by
  intro hC hA R _ A _ g hab hg
  exact free_of hC hA R A g hab hg _ (Category.comp_id _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCrystalReducesToDeRhamSqZeroStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_crystal_reduces_to_deRham_sqZero : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → RhoBC hI hk A₀.hom := by
  first | exact @GlobalTheory.LiftSys.rhoBC_of_abelianLift | exact GlobalTheory.LiftSys.rhoBC_of_abelianLift | (intros; apply GlobalTheory.LiftSys.rhoBC_of_abelianLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_descends_galoisCover_noetherian_base : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  first | exact @GlobalTheory.abelianScheme_descends_galoisCover_noetherian | exact GlobalTheory.abelianScheme_descends_galoisCover_noetherian | (intros; apply GlobalTheory.abelianScheme_descends_galoisCover_noetherian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentWithUniformization
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EllPowModel

def isPowGrpIso {S : Scheme.{0}} {G' G H : Over S} [GrpObj G'] [GrpObj G] [GrpObj H] {j : ℕ}
    (p : Out.IsPowGrp G' G j) (e : G ≅ H) [IsMonHom e.hom] : Out.IsPowGrp G' H j where
  pr i := p.pr i ≫ e.hom
  hom i := by haveI := p.hom i; infer_instance
  lim := mkFanLimit _ (fun s => p.lim.lift (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)))
    (fun s i => by
      have h : p.lim.lift (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ≫ p.pr i = s.proj i ≫ e.inv :=
        p.lim.fac (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ⟨i⟩
      show _ ≫ (p.pr i ≫ e.hom) = _
      rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id])
    (fun s m hm => p.lim.hom_ext fun ⟨i⟩ => by
      have h : p.lim.lift (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ≫ p.pr i = s.proj i ≫ e.inv :=
        p.lim.fac (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ⟨i⟩
      have hmi : m ≫ p.pr i ≫ e.hom = s.proj i := hm i
      show m ≫ p.pr i = p.lim.lift (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ≫ p.pr i
      rw [h, ← hmi, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id])

theorem main : ∀ (k : Type) [Field k] (σ : k →+* ℂ) (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp ℂ)) [GrpObj A]
    (p : A.left ⟶ A₀.left) (L : LB A.left) (u : HolUnif A L 1), IsAbelianScheme A₀ → SmoothOfRelativeDimension 1 A₀.hom →
    IsGrpPullback A A₀ (spMap σ) p → L.IsLB → ∀ n : ℕ,
  ∃ (B₀ : Over (Sp k)) (_ : GrpObj B₀) (B : Over (Sp ℂ)) (_ : GrpObj B) (q : B.left ⟶ B₀.left) (M : LB B.left)
    (v : HolUnif B M n), IsAbelianScheme B₀ ∧ SmoothOfRelativeDimension n B₀.hom ∧ IsAbelianScheme B ∧
    SmoothOfRelativeDimension n B.hom ∧ IsGrpPullback B B₀ (spMap σ) q ∧ ∀ z ∈ v.Λ, ∀ j, (fun _ : Fin 1 ↦ z j) ∈ u.Λ := by
  intro k _ σ A₀ _ A _ p L u hA₀ hd hp hL n
  let B₀ : Over (Sp k) := Out.powObj A₀ n
  let B : Over (Sp ℂ) := (Over.pullback (spMap σ)).obj B₀
  have P := PowGrp.powers (Sp k) B₀ A₀ n (Out.powIsPowGrp A₀ n)
  have hB₀ : IsAbelianScheme B₀ := P.2.2.2.1 hA₀
  have hdB₀ : SmoothOfRelativeDimension n B₀.hom := by
    have := P.2.2.1 1 hd
    rwa [Nat.mul_one] at this
  have hB : IsAbelianScheme B := isAbelianScheme_pullback_obj (spMap σ) B₀ hB₀
  have hdB : SmoothOfRelativeDimension n B.hom := by
    have : SmoothOfRelativeDimension n (pullback.snd B₀.hom (spMap σ)) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _) hdB₀
    exact this
  obtain ⟨p', -⟩ := isPowGrp_baseChange (Sp k) (Sp ℂ) (spMap σ) B₀ A₀ n (Out.powIsPowGrp A₀ n)
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback A₀ (spMap σ)) hp
  let pw : Out.IsPowGrp B A n := isPowGrpIso p' e
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (LB.isLB_linComb hL (fun i => (pw.pr i).left) (fun _ => (1 : ℤ)))
  obtain ⟨v, hv, -, -⟩ := PowUnif.exists_powUnif pw u hL (LB.isLB_linComb hL (fun i => (pw.pr i).left) (fun _ => (1 : ℤ)))
    w hw (Equiv.prodUnique (Fin n) (Fin 1))
  refine ⟨B₀, inferInstance, B, inferInstance, pullback.fst B₀.hom (spMap σ), _, v, hB₀, hdB₀, hB, hdB,
    isGrpPullback_pullback B₀ (spMap σ), fun z hz j => ?_⟩
  have := (hv z).1 hz j
  rw [PowUnif.blockPr_apply] at this
  convert this using 2 with a
  rw [Fin.fin_one_eq_zero a]
  rfl

end GlobalTheory.EllPowModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalFormsPrimitiveOfFramesStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeGlobalFormsPrimitive_of_frames : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) → FormSt := by
  first | exact @GlobalTheory.FormsOnAb.formSt_of | exact GlobalTheory.FormsOnAb.formSt_of | (intros; apply GlobalTheory.FormsOnAb.formSt_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimensionStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_isIso_of_mono_same_dimension : ∀ (S : Scheme.{0}) (B B' : Over S) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension g B'.hom → ∀ x : B ⟶ B', IsMonHom x → Mono x → IsIso x := by
  first | exact @GlobalTheory.AbMonoIsoAny.isIso_of_mono | exact GlobalTheory.AbMonoIsoAny.isIso_of_mono | (intros; apply GlobalTheory.AbMonoIsoAny.isIso_of_mono <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePrimeToCharTorsionRational
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsRat

theorem exists_factor_of_isFinite {K₀ K : Type} [Field K₀] [IsAlgClosed K₀] [Field K]
    (e : K₀ →+* K) {Z : Scheme.{0}} (s : Z ⟶ Sp K₀) [IsFinite s] (w : Sp K ⟶ Z)
    (hw : w ≫ s = spMap e) : ∃ w₀ : Sp K₀ ⟶ Z, w = spMap e ≫ w₀ := by
  haveI : IsAffine Z := isAffine_of_isAffineHom s
  let φ : CommRingCat.of K₀ ⟶ Γ(Z, ⊤) := Spec.preimage (Z.isoSpec.inv ≫ s)
  have hφ : Spec.map φ = Z.isoSpec.inv ≫ s := Spec.map_preimage _
  have hF : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hF' : φ.hom.Finite := (IsFinite.SpecMap_iff φ).1 hF
  let ψ : Γ(Z, ⊤) ⟶ CommRingCat.of K := Spec.preimage (w ≫ Z.isoSpec.hom)
  have hψ : Spec.map ψ = w ≫ Z.isoSpec.hom := Spec.map_preimage _
  have hφψ : φ ≫ ψ = CommRingCat.ofHom e := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hw]
  letI : Algebra K₀ Γ(Z, ⊤) := φ.hom.toAlgebra
  letI : Algebra K₀ K := e.toAlgebra
  haveI : Module.Finite K₀ Γ(Z, ⊤) := hF'
  have hmem : ∀ b, ψ.hom b ∈ e.range := by
    intro b
    have hb : IsIntegral K₀ b := Algebra.IsIntegral.isIntegral b
    let ψa : Γ(Z, ⊤) →ₐ[K₀] K :=
      { ψ.hom with commutes' := fun c => congrArg (fun g => g.hom c) hφψ }
    have hi : IsIntegral K₀ (ψ.hom b) := hb.map ψa
    exact minpoly.mem_range_of_degree_eq_one K₀ _
      (IsAlgClosed.degree_eq_one_of_irreducible K₀ (minpoly.irreducible hi))
  let E : K₀ ≃+* e.range := RingEquiv.ofBijective e.rangeRestrict
    ⟨fun a b h => e.injective (congrArg Subtype.val h), e.rangeRestrict_surjective⟩
  let ψ₀ : Γ(Z, ⊤) →+* K₀ := E.symm.toRingHom.comp (ψ.hom.codRestrict e.range hmem)
  refine ⟨Spec.map (CommRingCat.ofHom ψ₀) ≫ Z.isoSpec.inv, ?_⟩
  have h2 : CommRingCat.ofHom ψ₀ ≫ CommRingCat.ofHom e = ψ := by
    ext b
    show e (E.symm ⟨ψ.hom b, hmem b⟩) = ψ.hom b
    exact congrArg Subtype.val (E.apply_symm_apply ⟨ψ.hom b, hmem b⟩)
  rw [← Category.assoc, ← Spec.map_comp, h2, hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem torsion_point_rational : ∀ (K₀ K : Type) [Field K₀] [IsAlgClosed K₀] [Field K] (e : K₀ →+* K)
    (Y : Over (Sp K₀)) [GrpObj Y],
    IsAbelianScheme Y → ∀ n : ℕ, IsUnit (n : K₀) → ∀ y : Over.mk (spMap e) ⟶ Y, y ^ n = 1 →
    ∃ y₀ : Sp K₀ ⟶ Y.left, y.left = spMap e ≫ y₀ := by
  intro K₀ K _ _ _ e Y _ hY n hn y hy
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hn
    · exact h
  haveI := GlobalTheory.MulFiniteAny.isFinite_mulA K₀ Y hY n hn1
  let o : Sp K₀ ⟶ Y.left := (η[Y] : 𝟙_ (Over (Sp K₀)) ⟶ Y).left
  have hyo : y.left ≫ (mulA Y n).left = spMap e ≫ o := by
    have h1 : y ≫ mulA Y n = 1 := by
      rw [mulA, MonObj.comp_pow, Category.comp_id, hy]
    have h2 : y.left ≫ (mulA Y n).left = (toUnit (Over.mk (spMap e)) ≫ η[Y]).left := by
      rw [← Over.comp_left, h1, Hom.one_def]
    have h3 : (toUnit (Over.mk (spMap e))).left = spMap e := by
      have := Over.w (toUnit (Over.mk (spMap e)))
      simpa using this
    rw [h2, Over.comp_left, h3]
  obtain ⟨w₀, hw₀⟩ := exists_factor_of_isFinite e (pullback.snd (mulA Y n).left o)
    (pullback.lift y.left (spMap e) hyo) (pullback.lift_snd _ _ _)
  refine ⟨w₀ ≫ pullback.fst (mulA Y n).left o, ?_⟩
  rw [← Category.assoc, ← hw₀, pullback.lift_fst]

end GlobalTheory.TorsRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1VanishStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_square_affine_h1_vanish : ∀ (R : Type) [CommRing R], (∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom) ∧ ∀ (X : Scheme.{0}) [IsAffine X] (s : X ⟶ Sp R) (c : HO1 s), c = 0 := by
  first | exact @GlobalTheory.Obs.sq_abelian_and_affine_H1 | exact GlobalTheory.Obs.sq_abelian_and_affine_H1 | (intros; apply GlobalTheory.Obs.sq_abelian_and_affine_H1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyChartAffineOfChartFiniteType
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualApprox

theorem evc_comp_of_same {S : Scheme.{0}} {A T T₀ Y : Over S} {N : LB (A ⊗ T).left} {N₀ : LB (A ⊗ T₀).left}
    (hN : N.IsLB) (hN₀ : N₀.IsLB) (h : T ⟶ T₀) (hs : Same A N N₀ (𝟙 T) h) (y : Y ⟶ T) :
    evc hN (fst A Y) (snd A Y ≫ y) = evc hN₀ (fst A Y) (snd A Y ≫ y ≫ h) := by
  rw [same_iff hN hN₀, Category.comp_id] at hs
  have := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ y)).left) hs
  rw [pull_evc, pull_evc] at this
  simp only [lift_fst, lift_snd, lift_snd_assoc, Category.assoc] at this
  exact this

theorem chartAt_of_finiteType : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), Fam A M → (∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N) → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  intro R _ _ A _ hA U M hM hfin T _ N hN
  obtain ⟨T₀, h, N₀, hT₀, hft, hN₀, hs⟩ := GlobalTheory.T.exists_finiteType_additiveLineBundleFamily_affine R A hA T N hN
  obtain ⟨W₀, hW₀⟩ := hfin T₀ hft N₀ hN₀
  refine ⟨h.left ⁻¹ᵁ W₀, fun Y y ↦ ?_⟩
  have key : ∀ u : Y ⟶ U, Same A N M y u ↔ Same A N₀ M (y ≫ h) u := fun u ↦ by
    rw [same_iff hN.isLB hM.isLB, same_iff hN₀.isLB hM.isLB, evc_comp_of_same hN.isLB hN₀.isLB h hs y]
  simp_rw [key, hW₀ Y (y ≫ h)]
  rfl

end GlobalTheory.DualApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleEqMumfordLambdaOfAmpleAlgClose
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AddLineField

open GlobalTheory.PrimitiveOverField in

theorem additive_eq_lam_of_ample : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ N : LB (A ⊗ 𝟙_ (Over (Sp K))).left, Fam A N → ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, Same A N (abelian₂ A L) (𝟙 _) a := by
  intro K _ _ A _ hA L hL hamp N hN
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have hpr : IsProjBy A.hom := by
    obtain ⟨_, _, m, s, hH, hv⟩ := veryAmpleBy_of_relAmple hL hamp (𝟙 A.left) (Category.id_comp _)
      (pull_isLB hL (𝟙 A.left)) (GlobalTheory.lbIso_self (pull_isLB hL _))
    exact ⟨_, hH, m, s, hv⟩
  have hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f A.hom u → IsProjBy f :=
    fun R _ u X π f h => GlobalTheory.StabFlat.isProjBy_baseChange hpr h
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen := GlobalTheory.exists_gen_theta_of_isProjBy K A hA hpr L hL
  obtain ⟨S, hS, hSK⟩ := GlobalTheory.T.kernelOfLineBundle_rationalPoints_finite_closed K A hA L hL hamp
  let O : LB A.left := ev N (𝟙 A) (toUnit A)
  have hO : O.IsLB := pull_isLB hN.isLB _
  have hLam : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have pO : ∀ {Y : Over (Sp K)} (u : Y ⟶ A), CechPic.pull u.left (cls O hO) = evc hN.isLB u (toUnit Y) := by
    intro Y u
    rw [cls_ev hN.isLB, pull_evc, Category.comp_id, comp_toUnit]
  have lamO : lam (cls O hO) (fst A A) (snd A A) = 0 := by
    have e := (isAdditive_iff hN.isLB).1 hN.add (A ⊗ A) (fst A A) (snd A A) (toUnit _)
    have e1 := hN.add.evc_one hN.isLB (toUnit (A ⊗ A))
    simp only [lam, pO, e, e1]
    abel
  have key : ∀ x : 𝟙_ (Over (Sp K)) ⟶ A, cls O hO = lam (cls L hL) (toUnit A ≫ x) (𝟙 A) →
      Same A N (abelian₂ A L) (𝟙 _) x := by
    intro x hx
    rw [same_iff hN.isLB hLam]
    have e1 : evc hN.isLB (fst A (𝟙_ (Over (Sp K)))) (snd A _ ≫ 𝟙 _) =
        CechPic.pull (fst A (𝟙_ (Over (Sp K)))).left (cls O hO) := by
      rw [pO, Category.comp_id, toUnit_unique (toUnit _) (snd A _)]
    have e2 : evc hLam (fst A (𝟙_ (Over (Sp K)))) (snd A _ ≫ x) =
        CechPic.pull (fst A (𝟙_ (Over (Sp K)))).left (lam (cls L hL) (toUnit A ≫ x) (𝟙 A)) := by
      have cL : cls (abelian₂ A L) hLam = lam (cls L hL) (fst A A) (snd A A) := cls_cube_two hL _ _ hLam
      rw [evc, cL, pull_lam, pull_lam, lift_fst,
        lift_snd, Category.comp_id, ← Category.assoc, toUnit_unique (fst A _ ≫ toUnit A) (snd A _), lam_comm]
    rw [e1, e2, hx]
  by_contra hno
  have hno' : ∀ x : 𝟙_ (Over (Sp K)) ⟶ A, cls O hO ≠ lam (cls L hL) (toUnit A ≫ x) (𝟙 A) :=
    fun x e => hno ⟨x, key x e⟩
  obtain ⟨F, hF, eF⟩ := cls_surj (lam (cls L hL) (fst A A) (snd A A) - CechPic.pull (snd A A).left (cls O hO))
  have hpq : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have cst_left : ∀ x : 𝟙_ _ ⟶ A, (toUnit A ≫ x).left = A.hom ≫ x.left := fun x =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit A)))
  have s₁ : ∀ x : 𝟙_ _ ⟶ A, cls _ (pull_isLB hF (lift (toUnit A ≫ x) (𝟙 A)).left) =
      lam (cls L hL) (toUnit A ≫ x) (𝟙 A) - cls O hO := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, Over.id_left, pull_id]
  have s₂ : ∀ x : 𝟙_ _ ⟶ A, cls _ (pull_isLB hF (lift (𝟙 A) (toUnit A ≫ x)).left) =
      lam (cls L hL) (toUnit A ≫ x) (𝟙 A) := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, pull_const, sub_zero,
      lam_comm]
  have total : Ac ((fst A A).left ≫ A.hom) F := by
    refine (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq inferInstance inferInstance inferInstance inferInstance F hF).1
      fun R _ t Y π f h ht => ac_of_slices hproj hpq h hF fun x hx _ => ?_
    let x' : 𝟙_ _ ⟶ A := Over.homMk x hx
    refine ⟨(lift (toUnit A ≫ x') (𝟙 A)).left, ?_, ?_, ac_of_primitive hA hpr (pull_isLB hF _) ?_ ?_⟩
    · exact (congrArg CommaMorphism.left (lift_fst (toUnit A ≫ x') (𝟙 A))).trans (cst_left x')
    · exact congrArg CommaMorphism.left (lift_snd (toUnit A ≫ x') (𝟙 A))
    · rw [s₁, lam_sub, lam_lam hL hΘ, lamO, sub_zero]
    · rw [s₁, sub_ne_zero]
      exact fun e => hno' x' e.symm
  rw [hpq.w] at total
  let o : Spec (CommRingCat.of K) ⟶ A.left := η[A].left
  have ho : o ≫ A.hom = 𝟙 _ := Over.w η[A]
  have all := GlobalTheory.T.lineBundle_product_acyclic_over_affine_finite_closed K _ _ _ _ _ _ _ hpq.flip inferInstance inferInstance inferInstance
    inferInstance F hF S hS (fun R _ t Y π f h ht hne => ac_of_slices hproj hpq.flip h hF fun x hx hr => by
      let x' : 𝟙_ _ ⟶ A := Over.homMk x hx
      refine ⟨(lift (𝟙 A) (toUnit A ≫ x')).left, ?_, ?_, ac_of_primitive hA hpr (pull_isLB hF _) ?_ ?_⟩
      · exact (congrArg CommaMorphism.left (lift_snd (𝟙 A) (toUnit A ≫ x'))).trans (cst_left x')
      · exact congrArg CommaMorphism.left (lift_fst (𝟙 A) (toUnit A ≫ x'))
      · rw [s₂, lam_lam hL hΘ]
      · rw [s₂]
        intro e
        have hm := hSK x' e
        obtain ⟨y, hy⟩ := hr (IsLocalRing.closedPoint K)
        exact hne y (by rw [hy]; exact hm)) total
  have hs := ac_slice hproj hpq.flip hF all o ho (lift (𝟙 A) (toUnit A ≫ η[A])).left
    ((congrArg CommaMorphism.left (lift_snd (𝟙 A) (toUnit A ≫ η[A]))).trans (cst_left η[A]))
    (congrArg CommaMorphism.left (lift_fst (𝟙 A) (toUnit A ≫ η[A])))
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : Nonempty A.left := ⟨o (IsLocalRing.closedPoint K)⟩
  exact not_ac_of_cls_eq_zero _ (pull_isLB hF _) ((s₂ _).trans (lam_one_left _ _)) hs

end GlobalTheory.AddLineField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyOfDisjointOpenPieces
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.ProdGlue

theorem fam_of_pieces {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left] (hcov : ⨆ i, (j i).left.opensRange = ⊤) (hdisj : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left) (hP : ∀ i, Fam A (P i)) (hPt : Pt.IsLB) (hiso : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) : Fam A Pt := by
  refine ⟨hPt, (GlobalTheory.AbDual.isAdditive_iff hPt).mpr ?_⟩
  intro Y a a' t

  have hcovY : ⨆ i, (pullback.fst t.left (j i).left).opensRange = ⊤ := by
    simp only [Scheme.Hom.opensRange_pullbackFst]
    rw [← Scheme.Hom.preimage_iSup, hcov]
    try simp
  have hdisjY : Pairwise fun i i' => Disjoint (pullback.fst t.left (j i).left).opensRange
      (pullback.fst t.left (j i').left).opensRange := by
    intro i i' hii
    have h : Disjoint (j i).left.opensRange (j i').left.opensRange := hdisj hii
    rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_pullbackFst]
    rw [disjoint_iff] at h ⊢
    refine le_antisymm (fun x hx => ?_) bot_le
    have hx' : t.left x ∈ (j i).left.opensRange ⊓ (j i').left.opensRange := ⟨hx.1, hx.2⟩
    rw [h] at hx'
    simp at hx'

  rw [← sub_eq_zero]
  refine GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover (fun i => pullback.fst t.left (j i).left) hcovY hdisjY _ (fun i => ?_)
  let Zi : Over S := Over.mk (pullback.fst t.left (j i).left ≫ Y.hom)
  let u : Zi ⟶ Y := Over.homMk (pullback.fst t.left (j i).left) rfl
  have hv : pullback.snd t.left (j i).left ≫ (B i).hom = Zi.hom := by
    show pullback.snd t.left (j i).left ≫ (B i).hom = pullback.fst t.left (j i).left ≫ Y.hom
    rw [← Over.w (j i), ← Over.w t, ← Category.assoc, ← Category.assoc, pullback.condition]
  let v : Zi ⟶ B i := Over.homMk (pullback.snd t.left (j i).left) hv
  have huv : u ≫ t = v ≫ j i := by
    ext
    simp [u, v, pullback.condition]
  change GlobalTheory.CechPic.pull u.left _ = 0
  rw [map_sub, map_add, GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, huv,
    evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i),
    evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), MonObj.comp_mul,
    (GlobalTheory.AbDual.isAdditive_iff (hP i).isLB).mp (hP i).add]
  exact sub_self _

end GlobalTheory.DualCon.ProdGlue
end
end

