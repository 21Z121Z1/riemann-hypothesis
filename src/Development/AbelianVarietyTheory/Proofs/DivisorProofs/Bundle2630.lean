import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2529
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicKb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LabBC

open GlobalTheory GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem qkExt_id' {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C]
    [Algebra (FractionRing R) C] {k : ℕ} (p : QkPt D C k) : QkExt (RingHom.id C) p p := by
  have e : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
  refine ⟨rfl, by rw [e, Category.id_comp], fun χ => ?_⟩
  rw [e]
  exact corr_of_val D.P.isLB fun y J hJ =>
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val (p.g.s χ) r y J) (Category.id_comp _))).symm

theorem isAlgebraic_kb {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁)
    (hρ : ρ.Finite) [Algebra (FractionRing R) (Kb R₁)]
    (hc : ∀ r, algebraMap (FractionRing R) (Kb R₁) (algebraMap R _ r) =
      algebraMap (FractionRing R₁) (Kb R₁) (algebraMap R₁ _ (ρ r))) :
    Algebra.IsAlgebraic (FractionRing R) (Kb R₁) := by
  letI : Algebra R R₁ := ρ.toAlgebra
  have h1 : ∀ r : R, algebraMap R (Kb R₁) r = algebraMap R₁ (Kb R₁) (ρ r) := fun r => by
    rw [IsScalarTower.algebraMap_apply R (FractionRing R₁) (Kb R₁), IsScalarTower.algebraMap_apply R R₁ (FractionRing R₁),
      IsScalarTower.algebraMap_apply R₁ (FractionRing R₁) (Kb R₁)]
    rfl
  haveI : IsScalarTower R R₁ (Kb R₁) := IsScalarTower.of_algebraMap_eq fun r => h1 r
  haveI : IsScalarTower R (FractionRing R) (Kb R₁) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [h1, hc, IsScalarTower.algebraMap_apply R₁ (FractionRing R₁) (Kb R₁)]
  haveI : Module.Finite R R₁ := hρ
  haveI : Algebra.IsAlgebraic R R₁ := Algebra.IsAlgebraic.of_finite R R₁
  haveI : Algebra.IsAlgebraic R₁ (Kb R₁) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R₁) (K := FractionRing R₁)).2 inferInstance
  haveI : Algebra.IsAlgebraic R (Kb R₁) := Algebra.IsAlgebraic.trans R R₁ (Kb R₁)
  exact (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := FractionRing R)).1 inferInstance

theorem galEqN_of_rel {R R₁ : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁]
    [IsLocalRing R₁] (ρ : R →+* R₁) (hρ : FinExt ρ) (D : DegData R (maximalIdeal R))
    (D₁ : DegData R₁ (maximalIdeal R₁)) (hD : IsPullDeg ρ D.toPre D₁.toPre) (A : PolAV (Sp (FractionRing R)))
    (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left) (hfib : IsFib ρ A A₁ a) (lab : Labels D.toPre A)
    (n : ℕ) (hn : 1 ≤ n) (hGal : GalEqN n lab) [Algebra (FractionRing R) (Kb R₁)]
    (em : Kb R →ₐ[FractionRing R] Kb R₁) (lab₁ : Labels D₁.toPre A₁)
    (hc : ∀ r, algebraMap (FractionRing R) (Kb R₁) (algebraMap R _ r) =
      algebraMap (FractionRing R₁) (Kb R₁) (algebraMap R₁ _ (ρ r)))
    (hrel : ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre (Kb R) k) (p₁ : QkPt D.toPre (Kb R₁) k)
      (p' : QkPt D₁.toPre (Kb R₁) k), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y →
      IsPullGtF ρ hD (Kb R₁) p₁.g p'.g → (lab₁ k p').left ≫ a = spMap em.toRingHom ≫ (lab k p).left) :
    GalEqN n lab₁ := by
  obtain ⟨ga, hga, hpb, -⟩ := hfib
  have hK : algebraMap (FractionRing R) (Kb R₁) = (algebraMap (FractionRing R₁) (Kb R₁)).comp ga :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
      simp only [RingHom.comp_apply, hga, hc])
  haveI : Algebra.IsAlgebraic (FractionRing R) (Kb R₁) := isAlgebraic_kb ρ hρ.2.2 hc
  let mu : Kb R₁ →ₐ[FractionRing R] Kb R := IsAlgClosed.lift
  have hsurj : Function.Surjective em := fun z => by
    obtain ⟨w, hw⟩ := (Algebra.IsAlgebraic.algHom_bijective (em.comp mu)).2 z
    exact ⟨mu w, hw⟩
  let τ : Kb R ≃ₐ[FractionRing R] Kb R₁ := AlgEquiv.ofBijective em ⟨em.toRingHom.injective, hsurj⟩
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  have hG := hL.globalFns
  have hB := D.tau_bimult
  have hB₁ := D₁.tau_bimult
  have hF : Compat ρ (Kb R₁) := hc
  intro σ₁ j P P' hPP'
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn
  set e : Kb R →+* Kb R₁ := em.toRingHom with he_def
  set e' : Kb R₁ →+* Kb R := τ.symm.toAlgHom.toRingHom with he'_def
  set s₁ : Kb R₁ →+* Kb R₁ := σ₁.toRingHom with hs₁_def
  have hee' : e.comp e' = RingHom.id _ := RingHom.ext fun x => τ.apply_symm_apply x
  have hfσ : s₁.comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R₁) := by
    rw [hK, ← RingHom.comp_assoc]
    exact congrArg (fun f => f.comp ga) σ₁.comp_algebraMap
  have hfσ₁ : s₁.comp (algebraMap (FractionRing R₁) (Kb R₁)) = algebraMap (FractionRing R₁) (Kb R₁) :=
    σ₁.comp_algebraMap
  have hfe : e.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R₁) := em.comp_algebraMap
  have hfe' : e'.comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R) :=
    τ.symm.toAlgHom.comp_algebraMap
  have hfid : (RingHom.id (Kb R₁)).comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R₁) :=
    RingHom.id_comp _

  let σ : Kb R →ₐ[FractionRing R] Kb R :=
    τ.symm.toAlgHom.comp ((({ σ₁.toRingHom with commutes' := fun x => RingHom.congr_fun hfσ x } : Kb R₁ →ₐ[FractionRing R] Kb R₁)).comp em)
  have hσ_def : σ.toRingHom = e'.comp (s₁.comp e) := rfl
  have hfσR : σ.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R) :=
    σ.comp_algebraMap
  have hes : e.comp σ.toRingHom = s₁.comp e := by
    rw [hσ_def, ← RingHom.comp_assoc, hee', RingHom.id_comp]
  obtain ⟨q, rfl⟩ := pullQk_surjective hD hG hF hB hB₁ P
  obtain ⟨q', rfl⟩ := pullQk_surjective hD hG hF hB hB₁ P'
  have hq' : q' = qkExt hB s₁ hfσ q := by
    apply GlobalTheory.QkPullEquiv.pullQk_injective hD hG hF hB hB₁
    rw [(qkExt_iff hB₁ s₁ hfσ₁ _ _).1 hPP',
      (qkExt_iff hB₁ s₁ hfσ₁ _ _).1 (GlobalTheory.QkRationalExt.qkExt_pullQk hD hG hB hB₁ hF hF s₁ hfσ hfσ₁ q)]
  have hid : ∀ z : QkPt D.toPre (Kb R₁) (n ^ j), qkExt hB (RingHom.id _) hfid z = z := fun z =>
    ((qkExt_iff hB _ hfid z z).1 (qkExt_id' z)).symm

  have hpq : ∀ z : QkPt D.toPre (Kb R₁) (n ^ j), QkExt e (qkExt hB e' hfe' z) z := fun z => by
    rw [qkExt_iff hB e hfe, GlobalTheory.QkRationalExt.qkExt_qkExt hB e' hfe' e hfe (RingHom.id _) hfid hee', hid]
  have hσpp : QkExt σ.toRingHom (qkExt hB e' hfe' q) (qkExt hB e' hfe' q') := by
    rw [qkExt_iff hB _ hfσR, GlobalTheory.QkRationalExt.qkExt_qkExt hB e' hfe' σ.toRingHom hfσR (e'.comp s₁)
      (by rw [RingHom.comp_assoc, hfσ, hfe']) (by rw [hσ_def, RingHom.comp_assoc, RingHom.comp_assoc, hee',
        RingHom.comp_id]), hq', GlobalTheory.QkRationalExt.qkExt_qkExt hB s₁ hfσ e' hfe' (e'.comp s₁) _ rfl]
  have hgal := hGal σ j _ _ hσpp
  have h₁ := hrel _ hk _ _ _ (hpq q) ((eq_pullQk_iff hD hG hF hB hB₁ q _).1 rfl).1
    ((eq_pullQk_iff hD hG hF hB hB₁ q _).1 rfl).2
  have h₂ := hrel _ hk _ _ _ (hpq q') ((eq_pullQk_iff hD hG hF hB hB₁ q' _).1 rfl).1
    ((eq_pullQk_iff hD hG hF hB hB₁ q' _).1 rfl).2
  apply hpb.1.hom_ext
  · rw [h₂, Category.assoc, h₁, hgal, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', hes]
  · rw [Category.assoc, Over.w (lab₁ (n ^ j) (pullQk hD hG hF hB hB₁ q')), Over.w (lab₁ (n ^ j) (pullQk hD hG hF hB hB₁ q))]
    show jFK (R := R₁) (Kb R₁) = spMap s₁ ≫ jFK (R := R₁) (Kb R₁)
    rw [spMap_comp', hfσ₁]

end GlobalTheory.Mum.LabBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenTorsionKernelLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section
namespace GlobalTheory.LevCover

theorem clopenCond_comp_eq_one {Y : Scheme.{0}} (Zt B : Over Y) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ)
    (hn : IsUnit (n : Γ(Y, ⊤))) (g : Zt ⟶ B) (hg : g ^ n = 1) :
    ClopenCond Zt (fun _ z => z ≫ g = 1) := by
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B (hG := hB) hn
  obtain ⟨u, hu, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B n g hg
  obtain ⟨u', hu', -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B n (1 : Zt ⟶ B) (one_pow n)
  refine (clopenCond_eq u u').congr fun T z => ⟨fun h => ?_, fun h => ?_⟩
  · have hz : (z ≫ g) ^ n = 1 := by rw [← MonObj.comp_pow, hg, MonObj.comp_one]
    refine (GlobalTheory.LatticeTorsion.existsUnique_torsion B n (z ≫ g) hz).unique ?_ ?_
    · rw [Category.assoc, hu]
    · rw [Category.assoc, hu', MonObj.comp_one, h]
  · rw [← hu, ← Category.assoc, h, Category.assoc, hu', MonObj.comp_one]

theorem kerlocus_open_closed : ∀ (Y : Scheme.{0}) (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) (J : Type) [Finite J] (B : J → Over Y) [∀ i, GrpObj (B i)] (f : ∀ i, A ⟶ B i) (B' : Over Y) [GrpObj B'] (f' : A ⟶ B'), IsAbelianScheme A → (∀ i, IsAbelianScheme (B i)) → IsAbelianScheme B' → (∀ i, IsMonHom (f i)) → IsMonHom f' → IsUnit (n : Γ(Y, ⊤)) → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
  intro Y A _ _ n J _ B _ f B' _ f' hA hB hB' hf hf' hn
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
  have hι : torsion.ι A n ^ n = 1 := GlobalTheory.LatticeTorsion.torsionι_pow_eq_one A n
  have hpow : ∀ (C : Over Y) [GrpObj C] (g : A ⟶ C) [IsMonHom g], (torsion.ι A n ≫ g) ^ n = 1 := by
    intro C _ g _
    rw [← MonObj.pow_comp, hι, MonObj.one_comp]
  obtain ⟨W, hWo, hWc, H1, H2⟩ := implocus_open_closed Y (torsion A n)
    (fun _ z => ∀ i, z ≫ (torsion.ι A n ≫ f i) = 1) (fun _ z => z ≫ (torsion.ι A n ≫ f') = 1) hfin het
    (ClopenCond.forall_finite fun i =>
      clopenCond_comp_eq_one _ (B i) (hB i) n hn _ (hpow (B i) (f i)))
    (clopenCond_comp_eq_one _ B' hB' n hn _ (hpow B' f'))
  have key : ∀ T : Over Y, (∀ z : T ⟶ torsion A n, (∀ i, z ≫ (torsion.ι A n ≫ f i) = 1) →
      z ≫ (torsion.ι A n ≫ f') = 1) ↔
      ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
    intro T
    constructor
    · intro H a ha hfa
      obtain ⟨z, hz, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion A n a ha
      have h := H z (fun i => by rw [← Category.assoc, hz, hfa i])
      rwa [← Category.assoc, hz] at h
    · intro H z hz
      have h := H (z ≫ torsion.ι A n) (by rw [← MonObj.comp_pow, hι, MonObj.comp_one])
        (fun i => by rw [Category.assoc]; exact hz i)
      rwa [Category.assoc] at h
  refine ⟨W, hWo, hWc, fun Tb t => (H1 Tb t).trans ?_, fun k _ _ x => (H2 k x).trans (key _)⟩
  exact forall_congr' fun T => forall_congr' fun σ => forall_congr' fun _ => key T

end GlobalTheory.LevCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSplitTorusIntoTorusExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory.TorusFieldCrit

theorem exists_prime_hom_of_not_surjective {X : Type} [AddCommGroup X] {r : ℕ}
    (M : X →+ (Fin r → ℤ)) (hM : ¬ Function.Surjective M) :
    ∃ p : ℕ, p.Prime ∧ ∃ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 ∧ φ.comp M = 0 := by
  obtain ⟨y, hy⟩ := not_forall.1 hM
  have hQ : Nontrivial ((Fin r → ℤ) ⧸ M.range) :=
    ⟨⟨(y : (Fin r → ℤ) ⧸ M.range), 0, fun h => hy ((QuotientAddGroup.eq_zero_iff y).1 h)⟩⟩
  haveI : AddGroup.FG ((Fin r → ℤ) ⧸ M.range) := inferInstance
  obtain ⟨n, κ, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod ((Fin r → ℤ) ⧸ M.range)
  suffices h : ∃ q, q.Prime ∧ ∃ ψ : ((Fin r → ℤ) ⧸ M.range) →+ ZMod q, Function.Surjective ψ by
    obtain ⟨q, hq, ψ, hψ⟩ := h
    haveI := Fact.mk hq
    refine ⟨q, hq, ψ.comp (QuotientAddGroup.mk' M.range), fun h => ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hψ 1
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective M.range x
      have := DFunLike.congr_fun h z
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.zero_apply] at this
      rw [this] at hx
      exact zero_ne_one hx
    · ext x
      simp [(QuotientAddGroup.eq_zero_iff _).2 (AddMonoidHom.mem_range.2 ⟨x, rfl⟩)]
  by_cases hn : 0 < n
  · refine ⟨2, Nat.prime_two, ((Int.castAddHom (ZMod 2)).comp
        ((Finsupp.applyAddHom (⟨0, hn⟩ : Fin n)).comp (AddMonoidHom.fst _ _))).comp f.toAddMonoidHom, ?_⟩
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨f.symm (Finsupp.single ⟨0, hn⟩ k, 0), ?_⟩
    simp
  · have hn0 : n = 0 := by omega
    subst hn0
    obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra h
      push_neg at h
      apply not_subsingleton ((Fin r → ℤ) ⧸ M.range)
      refine ⟨fun a b => f.injective ?_⟩
      have key : ∀ x : (Fin 0 →₀ ℤ) × DirectSum κ (fun j ↦ ZMod (p j ^ e j)), x = 0 := fun x => by
        refine Prod.ext (Finsupp.ext fun j => j.elim0) (DFinsupp.ext fun j => ?_)
        haveI : Subsingleton (ZMod (p j ^ e j)) := by rw [h j, pow_zero]; infer_instance
        exact Subsingleton.elim _ _
      rw [key (f a), key (f b)]
    classical
    haveI := Fact.mk (hp i)
    refine ⟨p i, hp i, ((ZMod.castHom (dvd_pow_self (p i) hi) (ZMod (p i))).toAddMonoidHom.comp
      ((DirectSum.component ℤ κ (fun j => ZMod (p j ^ e j)) i).toAddMonoidHom.comp
        (AddMonoidHom.snd _ _))).comp f.toAddMonoidHom, ?_⟩
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨f.symm (0, DirectSum.lof ℤ κ (fun j => ZMod (p j ^ e j)) i (k : ZMod (p i ^ e i))), ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.apply_symm_apply, AddMonoidHom.coe_snd, LinearMap.toAddMonoidHom_coe,
      DirectSum.component.lof_self, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ZMod.castHom_apply]
    exact ZMod.cast_intCast (dvd_pow_self (p i) hi) k

theorem isClosedImmersion_of_torusExtension (Ω : Type) [Field Ω] (H : Over (Spec (CommRingCat.of Ω)))
    [GrpObj H] (E : TorusExtension H) (r : ℕ) (v : splitTorus (Spec (CommRingCat.of Ω)) (Fin r → ℤ) ⟶ H)
    (hv : IsMonHom v)
    (hker : ∀ (p : ℕ), p.Prime → ∀ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 →
      GlobalTheory.SplitTorus.torusMap (Spec (CommRingCat.of Ω)) φ ≫ v ≠ 1) :
    IsClosedImmersion v.left := by
  letI := E.addCommGroup; letI := E.grpB
  haveI := E.free; haveI := E.finite
  haveI := E.i_hom; haveI := E.q_hom; haveI := E.isAbelian.proper
  haveI : ConnectedSpace (Spec (CommRingCat.of Ω)) := GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing Ω
  have h1 : v ≫ E.q = toUnit _ ≫ η[E.B] :=
    GlobalTheory.splitTorus_hom_proper_trivial_local Ω (Fin r → ℤ) E.B (v ≫ E.q) inferInstance
  let w := E.isKernel.lift v (toUnit _) h1
  have hw : w ≫ E.i = v := E.isKernel.lift_fst _ _ _
  have hmono : Mono E.i := ⟨fun a b e => E.isKernel.hom_ext e (toUnit_unique _ _)⟩
  haveI : IsMonHom w := GlobalTheory.Serre.isMonHom_of_mul_comp w fun T x y => by
    rw [← cancel_mono E.i, MonObj.mul_comp (x ≫ w), Category.assoc, Category.assoc, Category.assoc, hw,
      MonObj.mul_comp]
  obtain ⟨M, hM⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap w
  by_cases hs : Function.Surjective M
  · have hdiag : w = GlobalTheory.Diag.diagMap _ M := by
      rw [hM]; symm
      exact (GlobalTheory.SplitTorus.eq_torusMap_iff _ M).2 fun b => GlobalTheory.Diag.diagMap_chi _ M b
    have hη : IsClosedImmersion (η[E.B] : 𝟙_ _ ⟶ E.B).left :=
      GlobalTheory.isClosedImmersion_of_section_of_isSeparated E.B.hom _ (by simpa using Over.w η[E.B])
    have hpb : IsPullback E.i.left (toUnit _ : splitTorus _ E.X ⟶ 𝟙_ _).left E.q.left (η[E.B] : 𝟙_ _ ⟶ E.B).left :=
      E.isKernel.map (Over.forget _)
    have hi : IsClosedImmersion E.i.left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip hη
    have hw' : IsClosedImmersion w.left := hdiag ▸ GlobalTheory.Diag.isClosedImmersion_diagMap _ hs
    rw [← hw, Over.comp_left]
    infer_instance
  · exfalso
    obtain ⟨p, hp, φ, hφ, hφM⟩ := exists_prime_hom_of_not_surjective M hs
    apply hker p hp φ hφ
    rw [← hw, hM, ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, hφM, GlobalTheory.SplitTorus.torusMap_zero,
      MonObj.one_comp]

end GlobalTheory.TorusFieldCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCobWholeOfIsCobCover
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt

theorem isCob_whole_of_isCob_cover : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc (whole X) u → ∀ k : Fn0 X, IsCob W u k → ∃ k' : Fn0 X, IsCob (whole X) u k' := by
  intro R _ X K W hW u hu k hk
  have ex : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), ∃! d : D,
      ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), Sm W (spOver ψ ≫ x) →
        k E (spOver ψ ≫ x) - u D E ψ x = ψ d := by
    intro D _ _ x
    refine natFamily_existsUnique R X K W hW D x (fun E _ _ ψ ↦ k E (spOver ψ ≫ x) - u D E ψ x) ?_
    intro E _ _ E' _ _ ψ θ hψ
    have c := hu D E E' ψ θ x (sm_whole x)
    have b := hk E E' θ (spOver ψ ≫ x) hψ
    have e : spOver (θ.comp ψ) ≫ x = spOver θ ≫ spOver ψ ≫ x := by
      rw [← Category.assoc, spOver_comp]
    show k E' (spOver (θ.comp ψ) ≫ x) - u D E' (θ.comp ψ) x = θ (k E (spOver ψ ≫ x) - u D E ψ x)
    rw [e, c, b, map_sub]
    ring
  let k' : Fn0 X := fun D _ _ x ↦ (ex D x).exists.choose
  have hk' : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D) (E : Type) [CommRing E] [Algebra R E]
      (ψ : D →ₐ[R] E), Sm W (spOver ψ ≫ x) → k E (spOver ψ ≫ x) - u D E ψ x = ψ (k' D x) :=
    fun D _ _ x ↦ (ex D x).exists.choose_spec
  refine ⟨k', fun D _ _ D' _ _ φ x _ ↦ ?_⟩
  have huniq : k' D' (spOver φ ≫ x) = u D D' φ x + φ (k' D x) := by
    refine (ex D' (spOver φ ≫ x)).unique (hk' D' (spOver φ ≫ x)) ?_
    intro E _ _ ψ hψ
    have e : spOver (ψ.comp φ) ≫ x = spOver ψ ≫ spOver φ ≫ x := by
      rw [← Category.assoc, spOver_comp]
    have h1 := hk' D x E (ψ.comp φ) (by rw [e]; exact hψ)
    have c := hu D D' E φ ψ x (sm_whole x)
    rw [e, c, AlgHom.comp_apply] at h1
    rw [map_add, ← h1]
    ring
  rw [huniq]
  ring

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordEnd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Mum.EndThick

def IsCoordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a a' : D.P.A ⟶ D.P.A) (h' : D.X →+ D.X) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε))
    (F : thickObj R I e G ⟶ thickObj R I e G) : Prop :=
  F.left ≫ g.pG.left = g.pG.left ≫ a.left ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J →
      val (g.t χ) (r ≫ F.left) z J =
        val (g.t (h' χ)) r z J * val (LB.pullGen D.P.L _ _ u (lift (toUnit _ ≫ D.c χ) g.pG).left) r z J

end GlobalTheory.Mum.EndThick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeformationChartPointSpecMap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

theorem valR_spMap_comp {Z : Scheme.{0}} {S S' : Type} [CommRing S] [CommRing S'] (σ : S →+* S')
    (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (f : Γ(Z, U)) :
    valR (spMap σ ≫ z) U f = σ (valR z U f) := by
  have h' := GlobalTheory.FlagMod.le_preimage_comp (spMap σ) h
  rw [valR_eq_ev _ _ h', valR_eq_ev _ _ h, GlobalTheory.FlagMod.ev_spMap σ z U h h']
  rfl

theorem top_le_transl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) {v : epsR K ⟶ A} (hv : IsTangent v) {U : A.left.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ (transl φ x v) ⁻¹ᵁ U := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap B (DualNumber B) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← (isTransl_transl φ x hx v).red hv] at this
  exact this

theorem transl_spMap {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B B' : Type} [CommRing B] [CommRing B']
    (φ : K →+* B) (σ : B →+* B') (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (v : epsR K ⟶ A) :
    transl (σ.comp φ) (spMap σ ≫ x) v = spMap (dualMap σ) ≫ transl φ x v := by
  have hx' : (spMap σ ≫ x) ≫ A.hom = spMap (σ.comp φ) := by
    rw [Category.assoc, hx, Cris.spMap_comp]
  exact (isTransl_transl _ _ hx' v).unique ((isTransl_transl φ x hx v).map σ)

theorem baseMap_eq {K : Type} [Field K] {B B' : Type} [CommRing B] [Algebra (DualNumber K) B] [CommRing B']
    [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B') :
    baseMap K B' = (ρ : B →+* B').comp (baseMap K B) :=
  RingHom.ext fun k ↦ by simp [baseMap]

theorem dualMap_snd {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') (c : DualNumber B) :
    (dualMap σ c).snd = σ c.snd := by
  simp [dualMap]

section Map

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
  {B B' : Type} [CommRing B] [Algebra (DualNumber K) B] [CommRing B'] [Algebra (DualNumber K) B']

theorem dlogAt_spMap (ρ : B →ₐ[DualNumber K] B') {x : Sp B ⟶ A.left}
    (hx : x ≫ A.hom = spMap (baseMap K B)) {v : epsR K ⟶ A} (hv : IsTangent v) {Wo : A.left.Opens}
    (g : Γ(A.left, Wo)ˣ) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) :
    dlogAt (baseMap K B') (spMap (ρ : B →+* B') ≫ x) v Wo g = ρ (dlogAt (baseMap K B) x v Wo g) := by
  rw [dlogAt, dlogAt, baseMap_eq ρ, transl_spMap _ _ x hx v,
    valR_spMap_comp _ _ _ (top_le_transl _ x hx hv hxWo), valR_spMap_comp _ _ _ hxWo, dualMap_snd, map_mul]
  rfl

theorem chartVal_spMap {Z : Scheme.{0}} (m : A.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω))
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    (ρ : B →ₐ[DualNumber K] B') {x : Sp B ⟶ A.left}
    (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo)
    (hut : ∀ a, IsTangent (u a)) (f : Γ(Z, Ω)) :
    chartVal m Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) f = ρ (chartVal m Ω δ u θ Wo g x f) := by
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω := hxΩ
  have ht : ∀ a, ⊤ ≤ (transl (baseMap K B) x (u a) ≫ m) ⁻¹ᵁ Ω := fun a ↦
    top_le_transl _ x hx (hut a) hxΩ
  have hd : ∀ b, dlogAt (baseMap K B') (spMap (ρ : B →+* B') ≫ x) (u b) Wo g =
      ρ (dlogAt (baseMap K B) x (u b) Wo g) := fun b ↦ dlogAt_spMap ρ hx (hut b) g hxWo
  have htr : ∀ a, transl (baseMap K B') (spMap (ρ : B →+* B') ≫ x) (u a) =
      spMap (dualMap (ρ : B →+* B')) ≫ transl (baseMap K B) x (u a) := fun a ↦ by
    rw [baseMap_eq ρ]; exact transl_spMap _ _ x hx (u a)
  simp only [chartVal, hd, htr, Category.assoc]
  simp only [valR_spMap_comp _ _ _ hxm, valR_spMap_comp _ _ _ (ht _), dualMap_snd, map_add, map_mul, map_sum]
  simp only [RingHom.coe_coe, AlgHom.commutes, baseMap_eq ρ, RingHom.comp_apply]

end Map

theorem isChartPt_spMap : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} {Z : Scheme.{0}} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} {Ω : Z.Opens} {δ : Γ(Z, Ω) → Γ(Z, Ω)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) (hut : ∀ a, IsTangent (u a)) (hl : IsChartPt A' m m' Ω δ u θ Wo g x l) (B' : Type) [CommRing B'] [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B'), IsChartPt A' m m' Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) (spMap (ρ : B →+* B') ≫ l) := by
  intro K _ A _ A' Z m m' Ω δ n u θ Wo g B _ _ x l hx hxΩ hxWo hut hl B' _ _ ρ
  obtain ⟨h1, h2, h3⟩ := hl
  refine ⟨?_, ?_, fun f ↦ ?_⟩
  · rw [Category.assoc, h1, ← Cris.spMap_comp, AlgHom.comp_algebraMap]
  · rw [Category.assoc]
    exact GlobalTheory.FlagMod.le_preimage_comp _ h2
  · rw [Category.assoc, valR_spMap_comp _ _ _ h2, h3 f, chartVal_spMap m Ω δ u θ Wo g ρ hx hxΩ hxWo hut f]
    rfl

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfIsIsoRestrictStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDominant_of_isIso_restrict' : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) (U : X.Opens), (U : Set X).Nonempty → IsIso (s ∣_ U) → IsDominant s := by
  first | exact @GlobalTheory.Discrepancy.isDominant_of_isIso_restrict | exact GlobalTheory.Discrepancy.isDominant_of_isIso_restrict | (intros; apply GlobalTheory.Discrepancy.isDominant_of_isIso_restrict <;> assumption)
end

