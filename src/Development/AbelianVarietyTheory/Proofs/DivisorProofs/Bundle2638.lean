import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMorphismDeterminantGeneratorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_morphism_determinant_generator : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen)
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))), m.IsBC →
    ∀ (X' : Obj F 𝔠 (Sp J.B)) (i : X.A.left ⟶ X'.A.left) (pull : X.IsPullBy X' (spMap J.π) i),
      liftFil J.κ pull.grp = Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} →
      ∃ δ' : X'.DetGen, ∀ (x : Fin (Module.finrank ℚ F) → HdR X.A) (d : Fin (Module.finrank ℚ F) → Crys J.κ (spMap J.π) X.A)
        (v : Fin (Module.finrank ℚ F) → X.Lie) (v' : Fin (Module.finrank ℚ F) → X'.Lie),
        (∀ j, IsJetElt J X N m (x j) (d j) ∧ IsLieImage (x j) (v j).hom ∧ IsLieImage (crysToDR J.κ pull.grp (d j)) (v' j).hom) →
          δ'.1 v' = algebraMap R J.B (δ.1 v) := by
  first | exact @GlobalTheory.JetGen.main | exact GlobalTheory.JetGen.main | (intros; apply GlobalTheory.JetGen.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMorphismIsBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_morphism_is_base_change : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
    m.IsBC := by
  first | exact @GlobalTheory.LatJet.grpMor_isBC | exact GlobalTheory.LatJet.grpMor_isBC | (intros; apply GlobalTheory.LatJet.grpMor_isBC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingComplexEmbeddingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_complex_embedding : ∀ {R : Type} [CommRing R] (σ : R →+* ℂ) {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (J' : JetRing ℂ I n),
    ∃ τ : J.B →+* J'.B, (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) ∧ IsDPMorphism J.κ J'.κ τ := by
  first | exact @GlobalTheory.LatJet.jet_coeffMap | exact GlobalTheory.LatJet.jet_coeffMap | (intros; apply GlobalTheory.LatJet.jet_coeffMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismCompatibleNilpotent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.JetStable

set_option autoImplicit false

theorem isJetElt_act {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)) (hN : ∀ i (a : 𝓞 F), Commute (N i) (act (dp0 R) (𝟙 _) X.rm a))
    (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A)))
    (a : 𝓞 F) (x : HdR X.A) (d : Crys J.κ (spMap J.π) X.A) (hd : IsJetElt J X N m x d) :
    IsJetElt J X N m (act (dp0 R) (𝟙 _) X.rm a x) (act J.κ (spMap J.π) X.rm a d) := by
  haveI := X.rm.hom a
  intro c
  have k := (homMor (dp0 R) (𝟙 _) (X.rm.act a)).comp m
  have e1 : primPull J.κ (spMap J.π) (X.rm.act a) (m.pull c) = k.pull c :=
    GrpMor.pull_pull m (homMor J.κ (spMap J.π) (X.rm.act a)) k (fun _ ↦ rfl) (by simp) c
  have e2 : m.pull (primPull (dp0 R) (𝟙 _) (X.rm.act a) c) = k.pull c :=
    GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) (X.rm.act a)) m k (fun _ ↦ rfl) rfl c
  have hc : ∀ i, N i (act (dp0 R) (𝟙 _) X.rm a x) = act (dp0 R) (𝟙 _) X.rm a (N i x) := fun i ↦
    LinearMap.congr_fun (hN i a).eq x
  rw [act_apply, push_apply, e1, ← e2, hd]
  simp only [hc]
  rfl

theorem act_mem_Fil {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (a : 𝓞 F) {x : HdR X.A} (hx : x ∈ Fil X.A) :
    act (dp0 R) (𝟙 _) X.rm a x ∈ Fil X.A := by
  haveI := X.rm.hom a
  rw [act_apply]
  exact push_mem_Fil _ hx

end GlobalTheory.LatJet.JetStable

open GlobalTheory.LatJet.JetStable in

theorem GlobalTheory.LatJet.jetFil_act_stable : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      ∀ (a : 𝓞 F), ∀ d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, act J.κ (spMap J.π) X.rm a d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} := by
  intro _ _ _ F _ _ _ 𝔠 R _ _ _ _ I _ n J X N hN m a
  have key : Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} ≤
      (Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}).comap (act J.κ (spMap J.π) X.rm a) := by
    refine Submodule.span_le.2 fun d ⟨x, hx, hd⟩ ↦ Submodule.subset_span ?_
    exact ⟨_, act_mem_Fil X a hx, isJetElt_act J X N hN.1 m a x d hd⟩
  exact fun d hd ↦ key hd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw GlobalTheory.Published GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetIsotropic

section Gen

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A : Over S} [GrpObj A]

theorem corrForm_antisymm (C : CupSquare κ t (A ⊗ A)) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (hs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {φ : Crys κ t A →ₗ[R] Crys κ t A →ₗ[R] R} (H : IsCorrForm κ t A A P φ) (x y : Crys κ t A) :
    φ x y = -φ y x := by
  obtain ⟨n, a, b, hc, hφ⟩ := id H
  let s : A ⊗ A ⟶ A ⊗ A := lift (snd A A) (fst A A)
  have ms : IsMor κ ((A ⊗ A).hom ≫ t) κ ((A ⊗ A).hom ≫ t) (RingHom.id R) s.left :=
    IsMor.of_over κ (φ := s.left) (by rw [← Category.assoc, Over.w])
  have hz := isChern_pull ms hc
  rw [crystallinePull2_sum_cup s ms] at hz
  simp only [pullOver_pullOver, s, lift_fst, lift_snd] at hz
  have e' : LBIso (P.pull s.left) P :=
    (cls_eq_iff (pull_isLB hP _) hP).1 ((cls_eq_iff hP (pull_isLB hP _)).2 hs).symm
  have hz' := (isChern_existsUnique_and_iso R _ κ _ _).2 _ _ (pull_isLB hP _) hP e' _ hz
  have H' : IsCorrForm κ t A A P (-φ.flip) := by
    refine ⟨n, fun k ↦ -b k, a, (congrArg (IsChern κ ((A ⊗ A).hom ≫ t) P) ?_).mp hz', fun u v ↦ ?_⟩
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Submodule.coe_neg, map_neg, LinearMap.map_neg, LinearMap.neg_apply]
      exact (neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)).symm
    · simp only [LinearMap.neg_apply, LinearMap.flip_apply]
      rw [hφ, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_neg, neg_mul, mul_comm]
  have e := congrArg (fun f ↦ f x y) (H.unique C hP H')
  simpa using e

end Gen

section Jet

variable {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

theorem cupSquare_jet (HR : AbelianDeRham) (HD : AbelianDualCrystal) (J : JetRing R I n) {A : Over (Sp R)} [GrpObj A]
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    CupSquare J.κ (spMap J.π) (A ⊗ A) := by
  obtain ⟨A', _, ψ, hψ⟩ := FlagTan.exists_isGrpPullback A (spMap (algebraMap R J.B))
  have e : (𝟙 (Sp R)) = spMap J.π ≫ spMap (algebraMap R J.B) := by
    rw [← GlobalTheory.Cris.spMap_comp]
    have : J.π.comp (algebraMap R J.B) = RingHom.id R := RingHom.ext fun r ↦ JetRing.π_algebraMap J r
    rw [this, GlobalTheory.Cris.spMap_id]
  have hn := (GlobalTheory.CrysConn.isGrpPullback_refl A).congr e rfl
  let i' : A.left ⟶ A'.left :=
    hψ.1.lift (Over.Hom.left (𝟙 A)) (A.hom ≫ spMap J.π) (hn.1.w.trans (Category.assoc _ _ _).symm)
  have ei : i' ≫ ψ = Over.Hom.left (𝟙 A) := hψ.1.lift_fst _ _ _
  have h' : IsGrpPullback A A' (spMap J.π) i' := hψ.cancel (hn.congr rfl ei.symm) (hψ.1.lift_snd _ _ _)
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hA hψ
  have hg' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hψ.1 hg
  exact AbelianDualCrystal.cupSquare_crys_prod HR.1 HD.2 J.nil (fun r ↦ ⟨algebraMap R J.B r, JetRing.π_algebraMap J r⟩)
    rfl hA' hg' hA' hg' h' h'

end Jet

section Diag

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

theorem polForm_diag {P : LB (A ⊗ A).left} {φ : HdR A →ₗ[R] HdR A →ₗ[R] R}
    (H : IsCorrForm (dp0 R) (𝟙 _) A A P φ) :
    ∃ ψ, IsPolForm (dp0 R) (𝟙 _) A (P.pull (lift (𝟙 A) (𝟙 A)).left) ψ ∧ ∀ x y, ψ x y = φ x y - φ y x := by
  obtain ⟨ψ', hψ', eψ'⟩ := H.isPolForm
  obtain ⟨ψ, hψ, eψ⟩ := hψ'.pull (homMor (dp0 R) (𝟙 _) (lift (𝟙 A) (𝟙 A)))
  refine ⟨ψ, hψ, fun x y ↦ ?_⟩
  rw [eψ (push (dp0 R) (𝟙 _) (lift (𝟙 A) (𝟙 A)) x) x (push (dp0 R) (𝟙 _) (lift (𝟙 A) (𝟙 A)) y) y
    (fun _ ↦ rfl) (fun _ ↦ rfl), RingHom.id_apply, eψ', push_push _ _ _ (lift_fst _ _),
    push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_id]
  rfl

end Diag

section Props

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] [IsDomain R] [CharZero R]
  {I : Type} [Fintype I]

theorem form_props (HR : AbelianDeRham) (X : Obj F 𝔠 (Sp R)) (N : I → Module.End R (HdR X.A)) (hN : admitted X N)
    (c : 𝔠.elt) :
    ∃ φ₀ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R, IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ₀ ∧
      (∀ x ∈ Fil X.A, ∀ y ∈ Fil X.A, φ₀ x y = 0) ∧ (∀ i x y, φ₀ (N i x) y + φ₀ x (N i y) = 0) ∧
      ∀ i j x y, φ₀ (N i x) (N j y) = 0 := by
  have C := cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim)
  obtain ⟨φ₀, hφ₀⟩ := exists_isCorrForm C (X.isLB c) (X.rig₁ c) (X.rig₂ c)
  have anti := corrForm_antisymm C (X.isLB c) (X.symm c) hφ₀
  obtain ⟨ψ, hψ, eψ⟩ := polForm_diag hφ₀
  have two : ∀ x y, ψ x y = 2 * φ₀ x y := fun x y ↦ by rw [eψ, anti y x]; ring
  have canc : ∀ r : R, 2 * r = 0 → r = 0 := fun r h ↦ (mul_eq_zero.1 h).resolve_left two_ne_zero
  obtain ⟨s1, s2⟩ := hN.2.2 c ψ hψ
  have iso := (HR.2.2.2.2 R X.A _ X.ab X.dim (X.diag c) (pull_isLB (X.isLB c) _) ψ hψ).1
  refine ⟨φ₀, hφ₀, fun x hx y hy ↦ canc _ (by rw [← two]; exact iso x hx y hy), fun i x y ↦ canc _ ?_,
    fun i j x y ↦ canc _ ?_⟩
  · rw [mul_add, ← two, ← two]; exact s1 i x y
  · rw [← two]; exact s2 i j x y

end Props

section BC

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A] {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'}
  {A' : Over S'} [GrpObj A'] {b : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem ext_of_isBC {m : GrpMor κ t A κ' t' A' (algebraMap R R') b φ} (hm : m.IsBC) {d₁ d₂ : Crys κ' t' A'}
    (h : ∀ c, d₁ (m.pull c) = d₂ (m.pull c)) : d₁ = d₂ := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

end BC

theorem jetFil_isotropic : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      ∀ (c : 𝔠.elt) (φ : Crys J.κ (spMap J.π) X.A →ₗ[J.B] Crys J.κ (spMap J.π) X.A →ₗ[J.B] J.B),
        GlobalTheory.AbDual.IsCorrForm J.κ (spMap J.π) X.A X.A (X.P c) φ → ∀ a ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, ∀ b ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, φ a b = 0 := by
  intro HG HR HD F _ _ _ 𝔠 R _ _ _ _ I _ n J X N hN m c φ hφ
  have hm := isBC_jetRing HG HR HD F 𝔠 R I n J X m
  obtain ⟨φ₀, hφ₀, z0, z1, z2⟩ := form_props HR X N hN c
  have iso : LBIso ((X.P c).pull (Over.Hom.left (𝟙 (X.A ⊗ X.A)))) (X.P c) :=
    (cls_eq_iff (pull_isLB (X.isLB c) _) (X.isLB c)).1 (by rw [cls_pull (X.isLB c), Over.id_left, CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ₀.pull (X.isLB c) m m (h := Over.Hom.left (𝟙 (X.A ⊗ X.A))) (by simp) (by simp)
    (X.isLB c) iso
  have eφ := hφ.unique (cupSquare_jet HR HD J X.ab X.dim) (X.isLB c) hφ'
  have hv : ∀ u c, hm.bcMap u (m.pull c) = algebraMap R J.B (u c) := fun u ↦ hm.corr_iff.2 rfl
  have hb : ∀ u v, φ (hm.bcMap u) (hm.bcMap v) = algebraMap R J.B (φ₀ u v) := fun u v ↦ by
    rw [eφ]; exact e' _ _ _ _ (hm.corr_iff.2 rfl) (hm.corr_iff.2 rfl)
  have hd : ∀ x d, IsJetElt J X N m x d → d = hm.bcMap x + ∑ i, J.t i • hm.bcMap (N i x) := fun x d hx ↦
    ext_of_isBC hm fun c ↦ by
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hv]
      exact hx c
  have key : ∀ x ∈ Fil X.A, ∀ y ∈ Fil X.A, ∀ d d', IsJetElt J X N m x d → IsJetElt J X N m y d' → φ d d' = 0 := by
    intro x hx y hy d d' hdx hdy
    rw [hd x d hdx, hd y d' hdy]
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hb, z0 x hx y hy, z2, map_zero, mul_zero, Finset.sum_const_zero, add_zero,
      zero_add]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [← mul_add, ← map_add, z1, map_zero, mul_zero]
  intro a ha b hb
  induction ha using Submodule.span_induction generalizing b with
  | mem a ha' =>
    obtain ⟨x, hx, hxa⟩ := ha'
    induction hb using Submodule.span_induction with
    | mem b hb' =>
      obtain ⟨y, hy, hyb⟩ := hb'
      exact key x hx y hy a b hxa hyb
    | zero => exact map_zero _
    | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
    | smul r u _ hu => rw [map_smul, hu, smul_zero]
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add u v _ _ hu hv => rw [map_add, LinearMap.add_apply, hu b hb, hv b hb, add_zero]
  | smul r u _ hu => rw [map_smul, LinearMap.smul_apply, hu b hb, smul_zero]

end GlobalTheory.JetIsotropic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingProdEqZeroOfLongStatement
section
open GlobalTheory.LatJet
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_prod_eq_zero_of_long : ∀ {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I), n + 1 < l.length → (l.map J.t).prod = 0 := by
  first | exact @GlobalTheory.LatJet.ProdZero.prod_eq_zero | exact GlobalTheory.LatJet.ProdZero.prod_eq_zero | (intros; apply GlobalTheory.LatJet.ProdZero.prod_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingReprMulPowerSeriesStatement
section
open GlobalTheory.LatJet
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_repr_mul_power_series : ∀ {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (F G : MvPowerSeries I ℂ) (x y : J.B), (∀ ν : Idx I n, J.b.repr x ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F) → (∀ ν : Idx I n, J.b.repr y ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) G) → ∀ ν : Idx I n, J.b.repr (x * y) ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) (F * G) := by
  first | exact @GlobalTheory.JetMul.reprMul | exact GlobalTheory.JetMul.reprMul | (intros; apply GlobalTheory.JetMul.reprMul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialDescendsFlatSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KTrivFlatDescent

theorem trivAlong_of_flat_surjective : ∀ {S S' S'' : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (g : S' ⟶ S) (f : S'' ⟶ S') [Flat f] [Surjective f], L.IsLB → GlobalTheory.KTrivSpread.TrivAlong G L (f ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  intro S S' S'' G _ L g f _ _ _ h T a ha x hx
  let u := pullback.fst a f
  have hu : Epi u := Flat.epi_of_flat_of_surjective _
  let T' : Over S := Over.mk (u ≫ T.hom)
  let U : T' ⟶ T := Over.homMk u rfl
  have hs : pullback.snd a f ≫ f ≫ g = T'.hom := by
    show pullback.snd a f ≫ f ≫ g = u ≫ T.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc, ha]
  have e₁ : U ≫ x = 1 := h T' (pullback.snd a f) hs (U ≫ x) (hx.comp U)
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ G) := by rw [e₁, MonObj.comp_one]
  exact Over.OverMorphism.ext ((cancel_epi u).1 (congrArg (fun q => q.left) e₂))

end GlobalTheory.KTrivFlatDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialSpreadsFromDvrGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.UU
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KTrivDvrSpread

theorem symGen_of_local {V : Type} [CommRing V] [IsLocalRing V] {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (L : LB G.left) (hs : Out.Sym G L) (g : Sp V ⟶ S) :
    ∃ t : LB.Gen (LB.LinComb (L.pull (pullback.fst G.hom g)) (K := Fin 2)
      ![(ι[(Over.pullback g).obj G]).left, 𝟙 ((Over.pullback g).obj G).left] ![1, -1]), t.IsGen := by
  obtain ⟨U, hU, t, ht⟩ := hs (g (IsLocalRing.closedPoint V))
  have hU' : ⊤ ≤ g ⁻¹ᵁ U := (top_le_iff_cpt g U).2 hU
  have hr : Set.range (pullback.fst G.hom g) ⊆ Set.range (G.hom ⁻¹ᵁ U).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show G.hom (pullback.fst G.hom g y) ∈ U
    have e : G.hom (pullback.fst G.hom g y) = g (pullback.snd G.hom g y) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [e]
    exact hU' trivial
  have hψ : IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι =
      pullback.fst G.hom g := IsOpenImmersion.lift_fac _ _ _
  refine gen_chartPull (chartPullLinComb L (pullback.fst G.hom g) _ _ _
    (IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr) fun k => ?_) t ht
  fin_cases k
  · show (ι[(Over.pullback g).obj G]).left ≫ pullback.fst G.hom g =
      IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left
    rw [← Category.assoc, hψ]
    exact GlobalTheory.PolBaseChange.inv_comm (isGrpPullback_pullback G g)
  · show 𝟙 _ ≫ pullback.fst G.hom g = IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι
    rw [hψ, Category.id_comp]

theorem trivAlong_of_generic : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), IsAbelianScheme G → L.IsLB → Out.RelAmple G L → Out.Rigidified G L → Out.Sym G L → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (g : Sp V ⟶ S), GlobalTheory.KTrivSpread.TrivAlong G L (spMap (algebraMap V (FractionRing V)) ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  intro S G _ _ L hG hL ha hR hS V _ _ _ g h
  have hl := GlobalTheory.abelianSchemeLaws_all.1
  have hp := isGrpPullback_pullback G g
  have hLB : (L.pull (pullback.fst G.hom g)).IsLB := pull_isLB hL _
  have hB : IsAbelianScheme ((Over.pullback g).obj G) := TLinPf.isAb_pullback g G hG
  have := hG.proper
  have haB : Out.RelAmple ((Over.pullback g).obj G) (L.pull (pullback.fst G.hom g)) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL ha (IsPullback.of_hasPullback G.hom g)
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V ((Over.pullback g).obj G) _ hLB).1 haB
  have hP : GlobalTheory.AbLaw.IsProjBy ((Over.pullback g).obj G).hom := ⟨_, GlobalTheory.AbLaw.isLB_pw hLB _, n, s, hs⟩
  obtain ⟨t, ht⟩ := GlobalTheory.AbLaw.CubeProj.exists_gen_theta_of_isProjBy hl.globalFns V _ hB hP _ hLB
  obtain ⟨r, hr⟩ := GlobalTheory.PolBaseChange.rigidified_pull hp hR
  obtain ⟨u, hu⟩ := symGen_of_local G L hS g
  obtain ⟨M, hM⟩ := GlobalTheory.AbPackage.exists_cp hl.globalFns hB ⟨L.pull (pullback.fst G.hom g), r, hLB, hr⟩
    ⟨t, ht⟩ ⟨u, hu⟩
  have hML : M.L.L = L.pull (pullback.fst G.hom g) := by rw [hM]
  let j := spMap (algebraMap V (FractionRing V))
  let B := (Over.pullback g).obj G
  have hq := isGrpPullback_pullback B j
  have hA : IsAbelianScheme ((Over.pullback j).obj B) := TLinPf.isAb_pullback j B hB
  have := hA.smooth
  have := hA.geomConnected
  have := hB.proper
  have : ConnectedSpace ((Over.pullback j).obj B).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback j).obj B).hom
  obtain ⟨dim, hdim⟩ := exists_dim_of_preconnected ((Over.pullback j).obj B).hom
    (eSec ((Over.pullback j).obj B) (IsLocalRing.closedPoint (FractionRing V)))
  have hLA := pull_isLB hLB (pullback.fst B.hom j)
  have hK : GlobalTheory.KTrivSpread.TrivAlong ((Over.pullback j).obj B)
      ((L.pull (pullback.fst G.hom g)).pull (pullback.fst B.hom j)) (𝟙 _) :=
    GlobalTheory.KTrivSpread.TrivAlong.pull hq hLB ((GlobalTheory.KTrivSpread.TrivAlong.pull hp hL h).comp (𝟙 _))
  let P : Out.PolAV (Sp (FractionRing V)) :=
    { A := (Over.pullback j).obj B
      isAb := hA
      g := dim
      smoothDim := hdim
      L := (L.pull (pullback.fst G.hom g)).pull (pullback.fst B.hom j)
      isLB := hLA
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hq ⟨r, hr⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hq (GlobalTheory.PolBaseChange.sym_pull hp hS)
      ample := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hLB haB (IsPullback.of_hasPullback B.hom j)
      ktriv := kTriv_iff_forall.2 fun T x hx => hK T T.hom (Category.comp_id _) x hx }
  have hw : LBIso P.L (M.L.L.pull (pullback.fst B.hom j)) := by
    rw [hML]
    exact GlobalTheory.PolBaseChange.lbIso_refl hLA
  have hK' : Out.KTriv B M.L.L :=
    GlobalTheory.KTrivSpread.kTriv_of_generic_fibre hl V (FractionRing V) P B M (pullback.fst B.hom j) hB hq hw
      (by rw [hML]; exact haB)
  rw [hML] at hK'
  exact GlobalTheory.KTrivSpread.trivAlong_of_kTriv hp hL hK'

end GlobalTheory.KTrivDvrSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerWedgeFormMapEqSmulOfBasisStatement
section
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehlerWedgeForm_map_eq_smul_of_basis : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by
  first | exact @GlobalTheory.TopFormAppend.dForm_append_eq_smul | exact GlobalTheory.TopFormAppend.dForm_append_eq_smul | (intros; apply GlobalTheory.TopFormAppend.dForm_append_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPolarisationTrivialLiftsSqZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelPolarisation_trivial_lifts_sqZero : ∀ (R R₀ : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → ∀ (L₀ : LB Y₀.left) (L : LB Y.left), L₀.IsLB → L.IsLB → RelAmple Y L → LBIso L₀ (L.pull i) → KTriv Y₀ L₀ → KTriv Y L := by
  first | exact @GlobalTheory.KTrivSqZero.kTriv_lift | exact GlobalTheory.KTrivSqZero.kTriv_lift | (intros; apply GlobalTheory.KTrivSqZero.kTriv_lift <;> assumption)
end

