import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0156
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0157

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Pts
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
include hp hτ

theorem exists_torsion_up [IsIso τ] {n : ℕ} (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ x₀ : T₀ ⟶ G, τ ≫ x₀.left = x.left ≫ φ ∧ x₀ ^ n = 1 := by
  let x₀ : T₀ ⟶ G := Over.homMk (inv τ ≫ x.left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hp.1.w, IsIso.inv_comp_eq, hτ, ← Category.assoc, Over.w])
  have e : τ ≫ x₀.left = x.left ≫ φ := IsIso.hom_inv_id_assoc _ _
  refine ⟨x₀, e, Over.OverMorphism.ext ((cancel_epi τ).1 ?_)⟩
  rw [over_pow hp τ hτ e, hx, over_one hp τ hτ]

theorem exists_torsion_down {n : ℕ} (x₀ : T₀ ⟶ G) (hx : x₀ ^ n = 1) :
    ∃ x : T ⟶ A, τ ≫ x₀.left = x.left ≫ φ ∧ x ^ n = 1 := by
  have w : (τ ≫ x₀.left) ≫ G.hom = T.hom ≫ f := by rw [Category.assoc, Over.w, hτ]
  let x : T ⟶ A := Over.homMk (hp.1.lift _ _ w) (hp.1.lift_snd _ _ _)
  have e : τ ≫ x₀.left = x.left ≫ φ := (hp.1.lift_fst _ _ _).symm
  refine ⟨x, e, Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩
  rw [← over_pow hp τ hτ e, hx, over_one hp τ hτ]

theorem secRel_smul {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)} {a : ℤ} {B : Over S}
    (σ : T.left ⟶ B.left) (hσ : σ ≫ B.hom = T.hom ≫ f) (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ)
    {th : LB.Sec (LPow A L₁ a T)} {th₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w th th₀)
    {th' : LB.Sec (LPow G L₀ a B)} {c : Γ(B.left, ⊤)}
    (hc : SecM.ofSec G th' = c • SecM.ofSec G (VVRank.pullS G a β th₀)) :
    SecRel hp σ hσ w (SecM.toSec A (σ.appTop.hom c • SecM.ofSec A th)) th' := by
  intro Z r z J J' hJ hJ'
  have e : psi hp σ hσ ≫ (β ▷ G).left = psi hp τ hτ := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst', psi_fst',
        Category.assoc, hβ]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', psi_snd']
  rw [sv_of_eq_mul (s := th') (t := VVRank.pullS G a β th₀) (c := c) (fun j => congrArg (fun q => q.1 j) hc) _ z hJ,
    sv_of_eq_mul (s := SecM.toSec A (σ.appTop.hom c • SecM.ofSec A th)) (t := th) (c := σ.appTop.hom c)
      (fun j => rfl) _ z hJ',
    VVRank.sv_pullS _ _ _ _ _ _ hJ, Category.assoc r _ (β ▷ G).left, e, h _ _ _ _ _ hJ hJ', mul_left_comm,
    Category.assoc r _ (fst B G).left, psi_fst', ← Category.assoc]
  exact congrArg (fun q => _ * (q * _)) (gs_pull _ σ z ⊤ trivial c).symm

end Pts

theorem exists_gen_thG_generic : Laws → Laws2 → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x₀ : Sp K ⟶ S) (P : PolAV (Sp K)) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G x₀ φ → LBIso P.L (L.pull φ) → ∀ (m : ℕ), Odd m → ∀ (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ y, y ^ (m ^ 2) = 1 ↔ ∃ i, x i = y) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x₀)), IsGenSec G L ((1 : ℕ) : ℤ) th ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (e : K →+* F) (x' : Sp F ⟶ S) (h : spMap e ≫ x₀ = x') (a : F) (th' : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x'))), SecM.ofSec G th' = @id Γ((Over.mk x').left, ⊤) (fnOf a) • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀) th) → (∀ i, ∃ z, ThG G L ρ m th' z (fnOf (a * e (v i)))) ∧ ∀ z (c : F), ThG G L ρ m th' z (fnOf c) → ∃ i, c = a * e (v i) := by
  intro hLaw _ S G _ L ρ hL hρ K _ _ _ x₀ P φ hp ⟨w, hw⟩ m hm Ix x v hx hv
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  have hx' : ∀ i, x i ^ (m ^ 2) = 1 := fun i => (hx _).2 ⟨i, rfl⟩
  obtain ⟨thP, hg, hth⟩ := GlobalTheory.T.exists_generator_thetaPoint_normalised_thetaConstants K P ρ' hρ' m Ix x v hx' hv
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x₀).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x₀).hom = (baseOver (Sp K)).hom ≫ x₀ := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨th, hrel⟩ := exists_secRel_up hp τ hτ hw hL hL₁ thP
  refine ⟨th, ThetaPtUp.isGenSec_up hp τ hτ hw hL hL₁ hrel hg, fun F _ _ e x' h a th' hth' => ?_⟩
  choose y hy hy' using fun i => exists_torsion_up hp τ hτ (x i) (hx' i)
  have up : ∀ i, ThG G L ρ m th (y i) (fnOf (v i)) := fun i => by
    have q := ThG.up hp τ hτ hw hL hL₁ hr (hy i) (hy' i) hrel (hth i)
    rw [hi] at q
    exact q
  let T' : Over (Sp K) := Over.mk (spMap e)
  let u : T' ⟶ baseOver (Sp K) := Over.homMk (spMap e) (Category.comp_id _)
  let τ' : T'.left ⟶ (Over.mk x₀).left := spMap e
  have hτ' : τ' ≫ (Over.mk x₀).hom = T'.hom ≫ x₀ := rfl
  let σ : T'.left ⟶ (Over.mk x').left := 𝟙 (Sp F)
  haveI : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp F)))
  have hσ : σ ≫ (Over.mk x').hom = T'.hom ≫ x₀ := (Category.id_comp _).trans h.symm
  have hj : inv σ = 𝟙 (Sp F) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨t, ht⟩ := exists_secRel hp τ' hτ' hw hL hL₁ th
  have hrel' := secRel_smul hp τ' hτ' σ hσ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀)
    (Category.id_comp _) ht hth'
  have hu : ∀ i, (u ≫ x i) ^ (m ^ 2) = 1 := fun i => by rw [← MonObj.comp_pow, hx', MonObj.comp_one]
  have down : ∀ i, ThG P.A P.L ρ' m (SecM.toSec P.A (σ.appTop.hom (fnOf a) • SecM.ofSec P.A t)) (u ≫ x i)
      (fnOf (a * e (v i))) := fun i => by
    have e₁ : τ' ≫ (y i).left = (u ≫ x i).left ≫ φ :=
      (congrArg (spMap e ≫ ·) ((Category.id_comp _).symm.trans (hy i))).trans (Category.assoc _ _ _).symm
    have q := ThG.smul (th' := SecM.toSec P.A (σ.appTop.hom (fnOf a) • SecM.ofSec P.A t)) hL₁ rfl
      (ThG.move hp τ' hτ' hw hL hL₁ hr e₁ (hu i) ht (up i))
    have e₂ : σ.appTop.hom (fnOf a) * τ'.appTop.hom (fnOf (v i)) = fnOf (a * e (v i)) :=
      (congrArg (fnOf a * ·)
        (congrArg (fun q => q.hom (v i)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e))).symm).trans
        (map_mul (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom _ _).symm
    rw [e₂] at q
    exact q
  have hK : ((m ^ 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hm.pos.ne')
  refine ⟨fun i => ?_, fun z c hz => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := exists_torsion_up hp σ hσ _ (hu i)
    have q := ThG.up hp σ hσ hw hL hL₁ hr hz hz' hrel' (down i)
    rw [hj] at q
    exact ⟨z, q⟩
  · obtain ⟨z', hz₁, hz₂⟩ := exists_torsion_down hp σ hσ z hz.1
    obtain ⟨y', hy₁, rfl⟩ := TorsionFieldExt.exists_of_isAlgClosed hLaw P u hK
      (by rw [← map_natCast e]; exact (map_ne_zero e).2 hK) z' hz₂
    obtain ⟨i, rfl⟩ := (hx y').1 hy₁
    have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
      rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom]
      exact (IsUnit.mk0 _ hK).map _
    have q : fnOf c = fnOf (a * e (v i)) :=
      ThG.unique hLaw P hm hun (ThG.move hp σ hσ hw hL hL₁ hr hz₁ hz₂ hrel' hz) (down i)
    exact ⟨i, (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective q⟩

end GlobalTheory.Ex.OneGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialFibreTestGeometricTestStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_special_fibre_test_geometric_test : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c) (τ : ex.core.Test y), S.Big → ex.core.Fib → ∃ e : (Over.pullback (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)).obj τ.H ≅ t.mod.Φ.G, IsMonHom e.hom ∧ e.hom.left ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  first | exact @GlobalTheory.ZH.exists_iso_special_fibre_of_test | exact GlobalTheory.ZH.exists_iso_special_fibre_of_test | (intros; apply GlobalTheory.ZH.exists_iso_special_fibre_of_test <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLinearUniformisationBaseChangeAdmissible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait

theorem exists_pelUnif_baseChange : Laws → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ g : R →+* R', Function.Injective g → I.map g ≤ I' → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap g)) (P' : PELUnif I' t') (ψ : P'.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left), IsGrpPullback P'.D.toPre.P.A P.D.toPre.P.A (spMap g) ψ := by
  intro h1 h3 h4 h5 E _ _ _ H R R' _ _ _ _ I I' hR hR' g hg hI t P
  obtain ⟨t', m₀, P', hD, -⟩ := GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange h4.unifBaseChange h5
    hR hR' t P g hg hI
  have := hD.e_hom
  exact ⟨t', m₀, P', hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf g),
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback P.D.toPre.P.A (specOf g))).congr
      (Category.id_comp _) rfl⟩

end GlobalTheory.Ex.Trait
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAtStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nz_of_polAt' : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → ∃ σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ)), ∀ (W' : Type) [CommRing W'] [IsLocalRing W'] (i : W →+* W') (χ' : Sp W' ⟶ S) (h : spMap i ≫ χ = χ'), NZ t.G t.PP.L χ' (VVRank.pullS t.G _ (Over.homMk (spMap i) h : Over.mk χ' ⟶ Over.mk χ) σ) := by
  first | exact @GlobalTheory.Ex.OneGen.exists_nz_of_polAt | exact GlobalTheory.Ex.OneGen.exists_nz_of_polAt | (intros; apply GlobalTheory.Ex.OneGen.exists_nz_of_polAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsBasisBaseChangeH1Vanishing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecBasis

theorem exists_sec_of_ker {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)}
    {M : LB Y} (P : Perf f M) (v : Fin P.a → R) (hv : P.D₀.mulVec v = 0) :
    ∃ s : LB.Sec M, ∀ i, rs Y (P.le i) (s.f (P.ch i)) = Seesaw.loc₀ P v i := by
  have h : IsPullback (𝟙 Y) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec R (RingHom.id R) Y (𝟙 Y) f h
  let t := E ⟨v, hv⟩
  have le : ∀ j, M.U j ≤ (M.pull (𝟙 Y)).U (fun _ => j) := fun j => le_pull M (𝟙 Y) le_rfl
  refine ⟨⟨fun j => rs Y (le j) (t.f fun _ => j), fun i j => ?_⟩, fun i => ?_⟩
  · have e := GlobalTheory.LB.sec_rel t (fun _ => i) (fun _ => j) (inf_le_left.trans (le i))
      (inf_le_right.trans (le j)) (inf_le_inf (le i) (le j))
    have e' := (GlobalTheory.LB.resG_pull_g (L := M) (𝟙 Y) (fun _ => i) (fun _ => j)
      (inf_le_inf (le i) (le j))).trans (rs_self _ _)
    exact (rs_rs _ _ _).trans (e.trans (congrArg₂ (· * ·) e' (rs_rs _ _ _).symm))
  · exact (rs_rs _ _ _).trans (hE ⟨v, hv⟩ i)

theorem exists_sec_iso {X X' : Scheme.{0}} {β : X' ⟶ X} {M : LB X} {M' : LB X'} (hM : M.IsLB) (hM' : M'.IsLB)
    (w : LB.Iso M' (M.pull β)) (hw : w.IsGen) (s : LB.Sec M') :
    ∃ t : LB.Sec (M.pull β), ∀ z k k', β z ∈ M.U k → z ∈ M'.U k' →
      gs (𝟙 X') z _ (t.f fun _ => k) = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 X') z _ (s.f k') := by
  refine ⟨SecOn.topEquiv _ (SecOn.congr hM' (LB.isLB_pull hM β) w hw ⊤ ((SecOn.topEquiv M').symm s)),
    fun z k k' hk hk' => ?_⟩
  have hz : z ∈ (M.pull β).U (fun _ => k) ⊓ M'.U k' := ⟨mem_pull.2 hk, hk'⟩
  have e := congrArg (gs (𝟙 X') z _) (SecOn.coord_congr hM' (LB.isLB_pull hM β) w hw
    ((SecOn.topEquiv M').symm s) (fun _ => k) k' (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl)
  rw [gs_mul _ _ _ hz, gs_res _ _ _ hz, gs_res _ _ _ hz, gs_res _ _ _ hz] at e
  refine (gs_res _ _ _ hz.1 _).trans (e.trans (congrArg₂ (· * ·) (gs_unit _ _ _ hz _) ?_))
  exact gs_res (𝟙 X') z (inf_le_right : ⊤ ⊓ M'.U k' ≤ _) ⟨trivial, hk'⟩ (s.f k')

theorem gs_comb {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (z : X)
    {U : X.Opens} (h : z ∈ U) {n : ℕ} (c : Fin n → R) (x : Fin n → Γ(X, U)) :
    gs (𝟙 X) z U (∑ j, AbLaw.cst f U (c j) * x j) = ∑ j, gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ (c j)) * gs (𝟙 X) z U (x j) := by
  rw [gs_eq _ _ _ h, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← gs_eq _ _ _ h, gs_mul _ _ _ h, ← rs_cst f (le_top : U ≤ ⊤), gs_res _ _ _ h]

theorem loc_mulVec {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (P : Perf f M) (π : X' ⟶ X)
    (f' : X' ⟶ Spec (CommRingCat.of R')) {n : ℕ} (B : Matrix (Fin P.a) (Fin n) R') (c : Fin n → R') (i : P.I) :
    Seesaw.loc P π f' (B.mulVec c) i = ∑ j, AbLaw.cst f' _ (c j) * Seesaw.loc P π f' (fun k => B k j) i := by
  simp only [Seesaw.loc, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem exists_basis : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∃ (n : ℕ) (τ : Fin n → LB.Sec M), ∀ (A' : Type) [CommRing A'] (g : A →+* A') (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)) (τ' : Fin n → LB.Sec M'), M'.IsLB → w.IsGen → (∀ i, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((τ i).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ' i).f k'))) → ∀ s' : LB.Sec M', ∃! c : Fin n → A', ∀ k : M'.ι, s'.f k = ∑ i, AbLaw.cst f' (M'.U k) (c i) * (τ' i).f k := by
  intro A _ _ _ X f hf hp M hM K _ g₀ hg₀ X₀ π f₀ h₀ M₀ w₀ hM₀ hw₀ hH
  obtain ⟨P⟩ := nonempty_perf_of_noetherian A X f hf hp M hM
  obtain ⟨w₁, hw₁⟩ := LBIso.symm (⟨w₀, hw₀⟩ : LBIso _ _)
  obtain ⟨r, n, B, hr, hB, hu⟩ := exists_matrix_basis_ker_of_exact_at_point A K g₀ _ _ _ P.D₀ P.D₁
    P.comp (P.exact K g₀ X₀ π f₀ h₀ (H1Iso.firstCohomologyVanishes_of_iso_of_isGen hM₀.cover (LB.isLB_pull hM π) w₁ hw₁ hH))
  have hru : IsUnit r := by
    by_contra hn
    have := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g₀ hg₀)
    exact hr ((RingHom.mem_ker).1 (this ▸ (show r ∈ IsLocalRing.maximalIdeal A from hn)))
  choose τ hτ using fun j => exists_sec_of_ker P (fun k => B k j) (funext fun l => congrFun₂ hB l j)
  refine ⟨n, τ, fun A' _ g X' β f' h M' w τ' hM' hw hτ' s' => ?_⟩
  obtain ⟨E, hE⟩ := P.sec A' g X' β f' h
  obtain ⟨t, ht⟩ := exists_sec_iso hM hM' w hw s'
  obtain ⟨v, rfl⟩ := E.surjective t
  have hA : ∀ z i k', β z ∈ P.W i → z ∈ M'.U k' → gs (𝟙 X') z _ (Seesaw.loc P β f' v.1 i) =
      (Geo.Tor.gw w (𝟙 _) z (P.ch i) k').val * gs (𝟙 X') z _ (s'.f k') := fun z i k' hi hk' =>
    (congrArg (gs (𝟙 X') z _) (hE v i).symm).trans ((gs_res (𝟙 X') z (le_pull M β (P.le i)) hi _).trans (ht z _ k' (P.le i hi) hk'))
  have hC : ∀ (c : Fin n → A') z i k', β z ∈ P.W i → z ∈ M'.U k' →
      gs (𝟙 X') z _ (Seesaw.loc P β f' ((B.map g).mulVec c) i) =
      (Geo.Tor.gw w (𝟙 _) z (P.ch i) k').val *
        gs (𝟙 X') z _ (∑ j, AbLaw.cst f' (M'.U k') (c j) * (τ' j).f k') := fun c z i k' hi hk' => by
    rw [loc_mulVec, gs_comb f' z (show z ∈ β ⁻¹ᵁ P.W i from hi), gs_comb f' z hk', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm, ← hτ' j z _ k' (P.le i hi) hk']
    refine congrArg (_ * ·) ?_
    refine (congrArg (gs (𝟙 X') z _) (Seesaw.loc_comp P h (fun k => B k j) i)).trans ?_
    rw [← hτ j i]
    refine (gs_pull (𝟙 X') β z _ hi _).trans ?_
    rw [Category.id_comp]
    exact gs_res β z _ hi _
  refine (existsUnique_congr fun c => ⟨fun hc k' => fn_ext fun z hz => ?_, fun hc => ?_⟩).1
    (hu A' g (hru.map g) v.1 v.2)
  · obtain ⟨i, hi⟩ := Seesaw.exists_mem P (β z)
    have e := hC c z i k' hi hz
    rw [hc, hA z i k' hi hz] at e
    exact (Units.mul_right_inj _).1 e
  · have hk : (P.D₀.map g).mulVec ((B.map g).mulVec c) = 0 := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hB, Matrix.map_zero _ (map_zero g), Matrix.zero_mulVec]
    refine congrArg Subtype.val (E.injective (a₁ := ⟨_, hk⟩) (a₂ := v) ?_)
    refine Seesaw.sec_ext _ _ (fun i => β ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M β (P.le i))
      (fun y => Seesaw.exists_mem P (β y)) fun i => ?_
    refine (hE ⟨_, hk⟩ i).trans (Eq.trans (fn_ext fun z hz => ?_) (hE v i).symm)
    obtain ⟨k', hk'⟩ := exists_chart hM' z
    exact (hC c z i k' hz hk').trans ((congrArg (fun x => _ * gs (𝟙 X') z _ x) (hc k').symm).trans
      (hA z i k' hz hk').symm)

end GlobalTheory.SecBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryTwistByRootsOfDataIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel

theorem exists_tateIsoQ_twJ : BrGtSt → BrWpSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → ActCompat A.ν A.oa ν' oa' β u r J → ∃ I' : TateIsoQ D D' oa' F, I'.ζ = A.I.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ q', TwJ β u (r j) J (A.q j x) q' ∧ ν'.QPt (I'.ev j x) q' := by
  intro hGt hWp
  unfold BrGtSt AllN at hGt
  unfold BrWpSt AllN at hWp
  unfold AllD
  intro E _ _ _ H D R R' _ _ _ _ F _ _ _ _ A D' _ oa' hE' hB' N' ν' k β u r J hr hact
  unfold ActCompat at hact
  have hG := hGt R A.D₀ A.even A.bimult F A.N A.ν
  have hG' := hGt R' D' hE' hB' F N' ν'
  have hW := hWp R A.D₀ A.even A.bimult F A.N A.ν
  have hW' := hWp R' D' hE' hB' F N' ν'
  have hI := GlobalTheory.T.twist_iso_torsionRepresentative_mulEquiv F A.N N' k β u J
  choose τ hτ using fun n (hn : 0 < n) => hI.1 (r n) n (hr.pow hn)
  have hex : ∀ n (a : D.La), ∃ p : QkPt D' F n, ∀ hn : 0 < n, ν'.QPt p (τ n hn (A.q n a)) := by
    intro n a
    by_cases hn : 0 < n
    · obtain ⟨p, hp⟩ := (hG'.2.2.2.2 n).2.1 (τ n hn (A.q n a))
      exact ⟨p, fun _ => hp⟩
    · obtain ⟨p, -⟩ := (hG'.2.2.2.2 n).2.1 1
      exact ⟨p, fun h => absurd h hn⟩
  choose ev hev using hex
  let I' : TateIsoQ D D' oa' F :=
    { ζ := A.I.ζ
      ζ_prim := A.I.ζ_prim
      ζ_pow := A.I.ζ_pow
      ev := ev
      add := by
        intro n hn a b
        obtain ⟨q₀, hy, hadd, heq⟩ := A.I.add n hn a b
        obtain ⟨w₀, hw₀, -⟩ := (hG.2.2.2.2 n).1 q₀
        have hw : w₀ = A.q n a * A.q n b := by
          apply Subtype.ext
          apply Prod.ext
          · apply Multiplicative.toAdd.injective
            apply A.ν.eX.injective
            rw [hw₀.1, hy, ← (A.hq n a).1, ← (A.hq n b).1, ← map_add]
            rfl
          · exact (hG.2.2.1 _ _ _ _ _ _ (A.hq n a).2 (A.hq n b).2 hw₀.2).mp hadd
        have hqe := ((hG.2.2.2.2 n).2.2 _ _ _ _ hw₀ (A.hq n (a + b))).mp heq
        rw [hw] at hqe
        have hqe' := ((hτ n hn).2.1 _ _).mp hqe
        rw [map_mul] at hqe'
        obtain ⟨p, hp⟩ := (hG'.2.2.2.2 n).2.1 (τ n hn (A.q n a) * τ n hn (A.q n b))
        refine ⟨p, ?_, ?_, ?_⟩
        · rw [← hp.1, ← (hev n a hn).1, ← (hev n b hn).1, ← map_add]
          rfl
        · exact (hG'.2.2.1 _ _ _ _ _ _ (hev n a hn).2 (hev n b hn).2 hp.2).mpr rfl
        · exact ((hG'.2.2.2.2 n).2.2 _ _ _ _ hp (hev n (a + b) hn)).mpr hqe'
      lin := by
        intro n hn x a
        exact hact n hn x _ _ _ _ _ _ _ _ (A.I.lin n hn x a) (A.hq n a) (A.hq n (x • a))
          (((hτ n hn).1 _ _).mp rfl) (((hτ n hn).1 _ _).mp rfl) (hev n a hn) (hev n (x • a) hn)
      ker := by
        intro n hn a b
        rw [(hG'.2.2.2.2 n).2.2 _ _ _ _ (hev n a hn) (hev n b hn), ← (hτ n hn).2.1,
          ← (hG.2.2.2.2 n).2.2 _ _ _ _ (A.hq n a) (A.hq n b)]
        exact A.I.ker n hn a b
      onto := by
        intro n hn p
        obtain ⟨v, hv, -⟩ := (hG'.2.2.2.2 n).1 p
        obtain ⟨p₀, hp₀⟩ := (hG.2.2.2.2 n).2.1 ((τ n hn).symm v)
        obtain ⟨a, ha⟩ := A.I.onto n hn p₀
        refine ⟨a, ?_⟩
        rw [(hG'.2.2.2.2 n).2.2 _ _ _ _ (hev n a hn) hv]
        have h := ((hτ n hn).2.1 _ _).mp (((hG.2.2.2.2 n).2.2 _ _ _ _ (A.hq n a) hp₀).mp ha)
        rwa [MulEquiv.apply_symm_apply] at h
      tower := by
        intro n m hn hm a
        have hnm : 0 < n * m := Nat.mul_pos hn hm
        obtain ⟨q₀, hy, hns, heq⟩ := A.I.tower n m hn hm a
        obtain ⟨w₀, hw₀, -⟩ := (hG.2.2.2.2 n).1 q₀
        have h1 : w₀.1.1 = (A.q (n * m) a).1.1 := by
          apply Multiplicative.toAdd.injective
          apply A.ν.eX.injective
          rw [hw₀.1, hy, (A.hq (n * m) a).1]
        have h2 : w₀.1.2 = (A.q (n * m) a).1.2 ^ m :=
          (GtValues.isNsmul_val A.ν m (A.hq (n * m) a).2 hw₀.2).mp hns
        obtain ⟨e1, e2⟩ := hI.2 (r n) (r (n * m)) n (n * m) m w₀ (A.q (n * m) a) (τ n hn w₀)
          (τ (n * m) hnm (A.q (n * m) a)) (hr.2 n m hn hm) h1 h2 (((hτ n hn).1 _ _).mp rfl)
          (((hτ (n * m) hnm).1 _ _).mp rfl)
        obtain ⟨p, hp⟩ := (hG'.2.2.2.2 n).2.1 (τ n hn w₀)
        refine ⟨p, ?_, ?_, ?_⟩
        · rw [← hp.1, ← (hev (n * m) a hnm).1, e1]
        · exact (GtValues.isNsmul_val ν' m (hev (n * m) a hnm).2 hp.2).mpr e2
        · rw [(hG'.2.2.2.2 n).2.2 _ _ _ _ hp (hev n a hn), ← (hτ n hn).2.1,
            ← (hG.2.2.2.2 n).2.2 _ _ _ _ hw₀ (A.hq n a)]
          exact heq
      isom := by
        intro n hn a b
        have h1 : 1 ≤ n := hn
        rw [hW' n h1 _ _ _ _ _ (hev n a hn) (hev n b hn), (hτ n hn).2.2]
        exact (hW n h1 _ _ _ _ _ (A.hq n a) (A.hq n b)).mp (A.I.isom n hn a b) }
  exact ⟨I', rfl, fun j hj x => ⟨τ j hj (A.q j x), ((hτ j hj).1 _ _).mp rfl, hev j x hj⟩⟩

end GlobalTheory.Relabel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisedModelValuedExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisedModel_valued_extension : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] (A : Lift a K) (o : Full D K), o.ρ = A.ρ → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] [Algebra (FractionRing W) C], CDV W → CExt W (IsLocalRing.maximalIdeal W) C → ∀ (K₁ : Type) [Field K₁] [Algebra (FractionRing W) K₁] [Algebra.IsAlgebraic (FractionRing W) K₁] (gam : K₁ →+* C) (e : K →+* K₁) (φ : O' →+* W), (∀ x, gam (algebraMap (FractionRing W) K₁ x) = algebraMap (FractionRing W) C x) → (∀ x, e (algebraMap (FractionRing O') K (algebraMap O' _ x)) = algebraMap (FractionRing W) K₁ (algebraMap W _ (φ x))) → ∀ o' : Full D C, FullExt (gam.comp e) o o' → ∃ (M : Mdl o') (f : W →+* M.W), ∀ x, algebraMap (FractionRing M.W) C (algebraMap _ _ (f x)) = algebraMap (FractionRing W) C (algebraMap _ _ x) := by
  first | exact @GlobalTheory.Ex.ExtModel.exists_mdl_ext | exact GlobalTheory.Ex.ExtModel.exists_mdl_ext | (intros; apply GlobalTheory.Ex.ExtModel.exists_mdl_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfRetractStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemiAbelian_of_retract' : ∀ (S : Scheme.{0}) (G G₁ : Over S) [GrpObj G] [GrpObj G₁], IsSemiAbelian G → SmConn G₁ → ∀ (i : G₁ ⟶ G) (r : G ⟶ G₁), IsMonHom r → i ≫ r = 𝟙 G₁ → IsSemiAbelian G₁ := by
  first | exact @GlobalTheory.SS.isSemiAbelian_of_retract | exact GlobalTheory.SS.isSemiAbelian_of_retract | (intros; apply GlobalTheory.SS.isSemiAbelian_of_retract <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionOfOneAlgClosedFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCondition_of_one_algClosed_field : GlobalTheory.UT.LL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R O' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing O'] [IsDomain O'] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t) (D₀ : DegPre O'), D₀.TauBimult → ∀ (f : O' →+* R) (ψ : P.D.toPre.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.D.toPre.P.L (D₀.P.L.pull ψ)) (e : D₀.X ≃+ P.D.toPre.X), IsGrpPullback P.D.toPre.P.A D₀.P.A (spMap f) ψ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀ (FractionRing O') k) (s : D₀.X → FractionRing R) (x₀ : Sp (FractionRing R) ⟶ P.A.A.left) (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (q₀ : QkPt D₀ C k) (q : QkPt P.D.toPre C k) (x : TFK (R := R) C ⟶ P.A.A), QkExt (algebraMap _ C) p₀ q₀ → q.y = e q₀.y → (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (algebraMap _ C (s χ))) → x.left = jFK (R := R) C ≫ x₀ → P.ToA C k q x → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F], Along f F → ∀ (q₀' : QkPt D₀ F k) (q' : QkPt P.D.toPre F k) (x' : TFK (R := R) F ⟶ P.A.A), QkExt (algebraMap _ F) p₀ q₀' → q'.y = e q₀'.y → (∀ χ, GenRel w (q'.g.s (e χ)) (q₀'.g.s χ) (algebraMap _ F (s χ))) → x'.left = jFK (R := R) F ≫ x₀ → P.ToA F k q' x' := by
  first | exact @GlobalTheory.LevelField.toA_of_toA | exact GlobalTheory.LevelField.toA_of_toA | (intros; apply GlobalTheory.LevelField.toA_of_toA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelIsoOfValuedAgreementOverFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelIso_of_valued_agreement_over_field : GlobalTheory.UT.LL → AllS fun {_} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {C} _ _ A u _ {_} M f {_} ν' J => ∀ u₀ : M.W, (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → ∀ ψ (he : eSec M.P.D.toPre.P.A ≫ ψ = spMap f ≫ eSec a.D₀.P.A) w e, Fit A u M f ν' J ψ w e → LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec M.P.D.toPre.P.A) (fun _ => 1)) M.P.D.toPre.rig (rigPullOf ψ (spMap f) he a.D₀.P.L a.D₀.rig) → (letI := H.starRing; ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left) → GlobalTheory.LN.Match a f u₀ M.P.D.toPre M.P.oD ψ he w e := by
  first | exact @GlobalTheory.FitMatch.match_of_fit | exact GlobalTheory.FitMatch.match_of_fit | (intros; apply GlobalTheory.FitMatch.match_of_fit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreImageTestIndependentStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialFibre_image_test_independent : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ x : Sp (kb p) ⟶ Q.P.left, x ≫ Q.P.hom = rPt p ≫ y → ((∃ c' : Sp (kb p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x) ↔ (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  first | exact @GlobalTheory.ZH.TestFib.image_special_fibre_iff | exact GlobalTheory.ZH.TestFib.image_special_fibre_iff | (intros; apply GlobalTheory.ZH.TestFib.image_special_fibre_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionsIndependentOnClosedFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSections_independent_on_closed_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0 := by
  first | exact @GlobalTheory.ZH.IndepFib.indep_on_closed_fibre | exact GlobalTheory.ZH.IndepFib.indep_on_closed_fibre | (intros; apply GlobalTheory.ZH.IndepFib.indep_on_closed_fibre <;> assumption)
end

