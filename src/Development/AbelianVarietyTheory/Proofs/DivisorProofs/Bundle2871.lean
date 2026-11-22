import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertRealMultiplication
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.CubicForms.ImportsBis

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianExtensionOverNormalBase
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SelfDualSpread

section General

variable {S S' : Scheme.{0}}

theorem pull_evc_gen {A B : Over S} {A' B' : Over S'} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    {m : (A' ⊗ A').left ⟶ (A ⊗ A).left} {m' : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (m₁ : m' ≫ (fst A B).left = (fst A' B').left ≫ f) (m₂ : m' ≫ (snd A B).left = (snd A' B').left ≫ g)
    {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (hQ' : (Q.pull m').IsLB)
    (a b : A ⊗ A ⟶ A) (a' b' : A' ⊗ A' ⟶ A') (y : A ⟶ B) (y' : A' ⟶ B')
    (ha : m ≫ a.left = a'.left ≫ f) (hb : m ≫ b.left = b'.left ≫ f) (ey : f ≫ y.left = y'.left ≫ g) :
    CechPic.pull m (evc hQ a (b ≫ y)) = evc hQ' a' (b' ≫ y') := by
  rw [evc, evc, CechPic.cls_pull hQ, ← CechPic.pull_comp, ← CechPic.pull_comp]
  congr 2
  apply left_ext
  · rw [Category.assoc, Category.assoc, lift_left_fst, m₁, lift_left_fst_assoc, ha]
  · rw [Category.assoc, Category.assoc, lift_left_snd, m₂, lift_left_snd_assoc, Over.comp_left, Over.comp_left,
      ← Category.assoc, hb, Category.assoc, Category.assoc, ey]

end General

theorem exists_generic_iso (hD : GlobalTheory.Published.DualAbelianScheme) {K : Type} [Field K] (Q : Out.PolAV (Sp K))
    (hΛ : (abelian₂ Q.A Q.L).IsLB) {D : Over (Sp K)} [GrpObj D] {R : LB (Q.A ⊗ D).left} (hR : IsDual Q.A D R)
    (hR' : IsAdditive (swap R)) :
    ∃ x : Q.A ⟶ D, IsMonHom x ∧ IsIso x ∧ CechPic.cls (abelian₂ Q.A Q.L) hΛ = evc hR.isLB (fst Q.A Q.A) (snd Q.A Q.A ≫ x) := by
  have := Q.isAb.comm
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hΛ a b = CechPic.lam (CechPic.cls Q.L Q.isLB) a b := fun Y a b ↦ by
    rw [evc, show CechPic.cls _ hΛ = CechPic.lam (CechPic.cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A) from
      CechPic.cls_cube_two Q.isLB _ _ hΛ, CechPic.pull_lam, lift_fst, lift_snd]
  have hd : IsDual Q.A Q.A (abelian₂ Q.A Q.L) := PerfectDual.isDual_of_isPerfect hD Q.A Q.A Q.isAb Q.isAb Q.smoothDim
    Q.smoothDim (isPerfect_lam Q.isLB Q.ktriv)
  have a₂ : IsAdditive (swap (abelian₂ Q.A Q.L)) := (BirigidLift.isAdditive_swap_iff hΛ).2 fun Y a b b' ↦ by
    rw [e, e, e, CechPic.lam_comm, CechPic.lam_comm _ a b, CechPic.lam_comm _ a b', ← e, ← e, ← e]
    exact (isAdditive_iff hΛ).1 hd.additive _ _ _ _
  obtain ⟨x, hx, ex⟩ := BirigidLift.exists_hom hR hR' hΛ hd.additive a₂
  exact ⟨x, hx, hd.isIso_of_cls hR ex, ex⟩

section Generic

variable {S : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {K : Type} [Field K] {η : Sp K ⟶ S}
  {A B : Over S} [GrpObj A] [GrpObj B] {A' B' : Over (Sp K)} [GrpObj A'] [GrpObj B'] {φ : A'.left ⟶ A.left}
  {ψ : B'.left ⟶ B.left}

omit [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] in

theorem exists_res (hφ : IsGrpPullback A' A η φ) (hψ : IsGrpPullback B' B η ψ) (y : A ⟶ B) :
    ∃ y' : A' ⟶ B', φ ≫ y.left = y'.left ≫ ψ :=
  ⟨Over.homMk (hψ.1.lift (φ ≫ y.left) A'.hom (by rw [Category.assoc, Over.w y, hφ.1.w])) (hψ.1.lift_snd _ _ _),
    (hψ.1.lift_fst _ _ _).symm⟩

theorem lbIso_of_generic (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hη : IsGenericPointHom η)
    (hφ : IsGrpPullback A' A η φ) (hψ : IsGrpPullback B' B η ψ) {R : LB (A ⊗ B).left} (hR : IsDual A B R)
    {m' : (A' ⊗ B').left ⟶ (A ⊗ B).left} (m₁ : m' ≫ (fst A B).left = (fst A' B').left ≫ φ)
    (m₂ : m' ≫ (snd A B).left = (snd A' B').left ≫ ψ) (hR' : IsDual A' B' (R.pull m'))
    {m : (A' ⊗ A').left ⟶ (A ⊗ A).left} (l₁ : m ≫ (fst A A).left = (fst A' A').left ≫ φ)
    (l₂ : m ≫ (snd A A).left = (snd A' A').left ≫ φ) {M₁ M₂ : LB (A ⊗ A).left} (h₁ : M₁.IsLB) (h₂ : M₂.IsLB)
    (a₁ : IsAdditive M₁) (a₂ : IsAdditive M₂)
    (e : CechPic.pull m (CechPic.cls M₁ h₁) = CechPic.pull m (CechPic.cls M₂ h₂)) : LBIso M₁ M₂ := by
  obtain ⟨y₁, hy₁, -⟩ := hR.univ A M₁ h₁ a₁
  obtain ⟨y₂, hy₂, -⟩ := hR.univ A M₂ h₂ a₂
  have c₁ : CechPic.cls M₁ h₁ = evc hR.isLB (fst A A) (snd A A ≫ y₁) :=
    (CechPic.cls_eq_iff h₁ (pull_isLB hR.isLB _)).2 hy₁
  have c₂ : CechPic.cls M₂ h₂ = evc hR.isLB (fst A A) (snd A A ≫ y₂) :=
    (CechPic.cls_eq_iff h₂ (pull_isLB hR.isLB _)).2 hy₂
  obtain ⟨y₁', e₁⟩ := exists_res hφ hψ y₁
  obtain ⟨y₂', e₂⟩ := exists_res hφ hψ y₂
  have k := fun (y : A ⟶ B) (y' : A' ⟶ B') (ey : φ ≫ y.left = y'.left ≫ ψ) ↦
    pull_evc_gen m₁ m₂ hR.isLB hR'.isLB (fst A A) (snd A A) (fst A' A') (snd A' A') y y' l₁ l₂ ey
  have e' : y₁' = y₂' := BirigidLift.dual_ext hR' (by rw [← k _ _ e₁, ← k _ _ e₂, ← c₁, ← c₂, e])
  obtain ⟨_, _⟩ := hη.quasiCompact_and_dominant
  have := hA.smooth
  have := hB.proper
  have ey : y₁ = y₂ := ExtUnique.over_hom_ext_of_isPullback hφ.1 (by rw [e₁, e₂, e'])
  subst ey
  exact (CechPic.cls_eq_iff h₁ h₂).1 (c₁.trans c₂.symm)

end Generic

theorem exists_selfDual : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (O : Type) [CommRing O] (c : O →+* O)
    (S : Scheme.{0}) [IsIntegral S] [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S →
    ∀ (K : Type) [Field K] (η : Sp K ⟶ S), GlobalTheory.IsGenericPointHom η →
    ∀ (A : Over S) [GrpObj A] (i : OAct O A), IsAbelianScheme A →
    ∀ (Q : Out.PolAV (Sp K)) (j : OAct O Q.A) (φ : Q.A.left ⟶ A.left), GlobalTheory.CurveRootGeometry.IsActPull j i η φ →
      GlobalTheory.CurveRootGeometry.IsRosati c Q j →
    ∃ P : LB (A ⊗ A).left, IsSelfDual c i P ∧ ∀ m : (Q.A ⊗ Q.A).left ⟶ (A ⊗ A).left,
      m ≫ (fst A A).left = (fst Q.A Q.A).left ≫ φ → m ≫ (snd A A).left = (snd Q.A Q.A).left ≫ φ →
      LBIso (P.pull m) (abelian₂ Q.A Q.L) := by
  intro hD hE O _ c S _ _ hS K _ η hη A _ i hA Q j φ hact hros
  obtain ⟨hφ, hj⟩ := hact
  have := Q.isAb.comm
  obtain ⟨B, _, R, hB, -, hR, hRs⟩ := hD S A hA
  have hψ := isGrpPullback_pullback B η
  obtain ⟨m', m₁, m₂⟩ := exists_prod_pullback hφ hψ
  have hR' : (R.pull m').IsLB := pull_isLB hR.isLB m'
  have dR' := hR.baseChange hφ hψ m₁ m₂ hR' ((CechPic.cls_eq_iff hR' hR').1 rfl)
  have aR' := (BirigidLift.additive_pull hφ hψ m₁ m₂ hR.isLB hR' ((CechPic.cls_eq_iff hR' hR').1 rfl)
    hR.additive hRs.additive).2
  have hΛ : (abelian₂ Q.A Q.L).IsLB := (isPerfect_lam Q.isLB Q.ktriv).isLB
  obtain ⟨x, hx, ix, ex⟩ := exists_generic_iso hD Q hΛ dR' aR'
  have : IsMonHom (asIso x).hom := hx
  obtain ⟨E, ⟨hE₁, hE₂⟩, -⟩ := hE.generic_existsUnique_iso_of_isGrpPullback hS hη
    (isSemiAbelian_of_isAbelianScheme A hA) (isSemiAbelian_of_isAbelianScheme B hB) hφ hψ (asIso x)
  replace hE₂ : φ ≫ E.hom.left = x.left ≫ pullback.fst B.hom η := hE₂.symm
  have hP : (ev R (fst A A) (snd A A ≫ E.hom)).IsLB := pull_isLB hR.isLB _
  obtain ⟨a₁, a₂⟩ := BirigidLift.additive_ev hR.isLB hR.additive hRs.additive E.hom
  have eΛ : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hΛ a b = CechPic.lam (CechPic.cls Q.L Q.isLB) a b :=
    fun Y a b ↦ by
      rw [evc, show CechPic.cls _ hΛ = CechPic.lam (CechPic.cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A) from
        CechPic.cls_cube_two Q.isLB _ _ hΛ, CechPic.pull_lam, lift_fst, lift_snd]

  have key : ∀ (m : (Q.A ⊗ Q.A).left ⟶ (A ⊗ A).left) (a b : A ⊗ A ⟶ A) (a' b' : Q.A ⊗ Q.A ⟶ Q.A),
      m ≫ a.left = a'.left ≫ φ → m ≫ b.left = b'.left ≫ φ →
      CechPic.pull m (evc hP a b) = CechPic.lam (CechPic.cls Q.L Q.isLB) a' b' := fun m a b a' b' ha hb ↦ by
    rw [BirigidLift.evc_of_cls hR.isLB hP rfl, pull_evc_gen m₁ m₂ hR.isLB hR' a b a' b' E.hom x ha hb hE₂, ← eΛ,
      BirigidLift.evc_of_cls hR' hΛ ex]
  have c₀ : CechPic.cls _ hP = evc hP (fst A A) (snd A A) := by
    rw [evc, lift_fst_snd, Over.id_left, CechPic.pull_id]
  obtain ⟨m, l₁, l₂⟩ := exists_prod_pullback hφ hφ
  refine ⟨ev R (fst A A) (snd A A ≫ E.hom), ⟨isDual_of_iso S A A B _ R hR hP E.hom inferInstance hE₁
    ((CechPic.cls_eq_iff hP hP).1 rfl), ?_, fun a ↦ ?_⟩, fun n n₁ n₂ ↦ ?_⟩
  · refine lbIso_of_generic hA hB hη hφ hψ hR m₁ m₂ dR' l₁ l₂ (pull_isLB hP _) hP a₂ a₁ ?_
    rw [c₀, cls_ev hP, key m _ _ _ _ l₂ l₁, key m _ _ _ _ l₁ l₂, CechPic.lam_comm]
  · have := i.hom a
    have hM₁ := pull_isLB hP (lift (fst A A ≫ i.act a) (snd A A)).left
    have hM₂ := pull_isLB hP (lift (fst A A) (snd A A ≫ i.act (c a))).left
    refine lbIso_of_generic hA hB hη hφ hψ hR m₁ m₂ dR' l₁ l₂ hM₁ hM₂
      ((isAdditive_iff hM₁).2 fun Y u u' t ↦ ?_) ((isAdditive_iff hM₂).2 fun Y u u' t ↦ ?_) ?_
    · rw [evc_ev hP, evc_ev hP, evc_ev hP]
      simp only [lift_fst_assoc, lift_snd, MonObj.mul_comp]
      exact (isAdditive_iff hP).1 a₁ _ _ _ _
    · rw [evc_ev hP, evc_ev hP, evc_ev hP]
      simp only [lift_snd_assoc, lift_fst]
      exact (isAdditive_iff hP).1 a₁ _ _ _ _
    · rw [cls_ev hP, cls_ev hP, key m _ _ (fst Q.A Q.A ≫ j.act a) _ (by
          rw [Over.comp_left, Over.comp_left, ← Category.assoc, l₁, Category.assoc, Category.assoc, hj]) l₂,
        key m _ _ _ (snd Q.A Q.A ≫ j.act (c a)) l₁ (by
          rw [Over.comp_left, Over.comp_left, ← Category.assoc, l₂, Category.assoc, Category.assoc, hj])]
      exact EndOnTorsion.lam_rosati Q (hros a) _ _
  · refine (CechPic.cls_eq_iff (pull_isLB hP n) hΛ).1 ?_
    rw [CechPic.cls_pull hP, c₀, key n _ _ _ _ n₁ n₂]
    exact (CechPic.cls_cube_two Q.isLB _ _ hΛ).symm

end GlobalTheory.SelfDualSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusEqPreimageModuliAndPrincipalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianLocus_eq_preimage_moduli_and_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : Scheme.{0}) (π : T ⟶ Y.X) (t : SAB H T), Nonempty (SABMap t Y.t π) → abLocus t.G = π ⁻¹' Set.range Y.j ∧ IsOpen (abLocus t.G) ∧ ∀ W : T.Opens, (W : Set T) ⊆ abLocus t.G → RelAmple ((Over.pullback W.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom W.ι)) := by
  first | exact @GlobalTheory.ModelAbLocus.abLocus_eq_and_pol | exact GlobalTheory.ModelAbLocus.abLocus_eq_and_pol | (intros; apply GlobalTheory.ModelAbLocus.abLocus_eq_and_pol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIsoOfTwoUniformisations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp

theorem abelianPart_iso_of_twoUnif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom ∧ ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left := by
  intro R _ _ _ hBase D A G _ _ hG U g _ a _ _ A₂ D₂ U₂ _
  have hR : AdmBase R (maximalIdeal R) := hBase.1
  have hN : IsNoetherianRing R := hR.1
  have hC : IsAdicComplete (maximalIdeal R) R := hR.2.2.2
  have hJ : maximalIdeal R ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot _
  obtain ⟨b₁, hb₁, h₁⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R (maximalIdeal R) hR D₂ D A₂ A G G
    U₂.toUnifPre U.toUnifPre (𝟙 G) inferInstance
  obtain ⟨b₂, hb₂, h₂⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R (maximalIdeal R) hR D D₂ A A₂ G G
    U.toUnifPre U₂.toUnifPre (𝟙 G) inferInstance

  have q₁ : ∀ e, (U.gt e).q = (U₂.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map b₁ := by
    intro e
    have := h₁ e
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at this
    exact this
  have q₂ : ∀ e, (U₂.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map b₂ := by
    intro e
    have := h₂ e
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at this
    exact this
  have epi : ∀ {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
      (V : UnifPre (maximalIdeal R) D' A' G) (e : ℕ), Epi (V.gt e).q := by
    intro D' A' V e
    have := (V.gt e).q_flat
    have := (V.gt e).q_surj
    have : Epi (V.gt e).q.left := Flat.epi_of_flat_of_surjective _
    exact Over.epi_of_epi_left _
  have k₁ : b₂ ≫ b₁ = 𝟙 _ := by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq hJ _ _ _ fun n => ?_
    have := epi U.toUnifPre n
    rw [← cancel_epi (U.gt n).q, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.comp_id, ← Category.assoc, ← q₂, ← q₁]
  have k₂ : b₁ ≫ b₂ = 𝟙 _ := by
    have := D₂.toPre.P.isAb.smooth
    have := D₂.toPre.P.isAb.geomConnected
    have := D₂.toPre.P.isAb.proper
    refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq hJ _ _ _ fun n => ?_
    have := epi U₂.toUnifPre n
    rw [← cancel_epi (U₂.gt n).q, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.comp_id, ← Category.assoc, ← q₁, ← q₂]
  refine ⟨⟨b₁, b₂, k₂, k₁⟩, hb₁, fun e => ?_⟩
  show (U₂.gt e).q.left ≫ (fstG (maximalIdeal R) e D₂.toPre.P.A).left ≫ b₁.left =
    (U.gt e).q.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left
  have m : ((Over.pullback (thick R (maximalIdeal R) e)).map b₁).left ≫
      (fstG (maximalIdeal R) e D.toPre.P.A).left = (fstG (maximalIdeal R) e D₂.toPre.P.A).left ≫ b₁.left :=
    pullback.lift_fst _ _ _
  rw [← m, q₁ e, Over.comp_left, Category.assoc]

end GlobalTheory.MumCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfConstantDimensionStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeUnobstructed_of_constantDimension : UnobDim → GlobalTheory.Published.AbelianUnobstructed := by
  first | exact @GlobalTheory.DimRed.abelianUnobstructed_of_unobDim | exact GlobalTheory.DimRed.abelianUnobstructed_of_unobDim | (intros; apply GlobalTheory.DimRed.abelianUnobstructed_of_unobDim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsOnThickeningsOfPullbackUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.TorusCoord GlobalTheory.PullLinear in

theorem actsAs_of_isPullUnif : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (I : Ideal R) (I' : Ideal V) (D : DegData R I) (D' : DegData V I') (hD : IsPullDeg θ D.toPre D'.toPre) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf θ)).obj G) (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif θ hD bc U U' → ∀ (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g : G ⟶ G) (b' : D'.toPre.P.A ⟶ D'.toPre.P.A) (h' : D'.toPre.X → D'.toPre.X) (g' : G' ⟶ G'), IsMonHom b' → ActsAs U.toUnifPre b h g → g' ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf θ)).map g → b' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map b → (∀ y, hD.xe (h' y) = h (hD.xe y)) → ActsAs U'.toUnifPre b' h' g' := by
  intro R R' _ _ _ _ φ I I' D D' hD A A' G _ _ G' _ _ bc U U' hU b k₀ g b' k' g' hb' hlin hG hB hx
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  choose h hf hpt _hw using H
  have hact : ∀ (e : ℕ), ((Over.pullback (thick R' I' e)).map g').left ≫ h e =
      h e ≫ ((Over.pullback (thick R I e)).map g).left := by
    intro e
    have hf' : h e ≫ pullback.fst G.hom (thick R I e) = pullback.fst G'.hom (thick R' I' e) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ) := hf e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G.hom (thick R I e)), Category.assoc, Category.assoc, map_left_fst,
      ← Category.assoc (h e), hf', ← Category.assoc, map_left_fst, Category.assoc,
      act_proj _ bc.hom hG, Category.assoc, Category.assoc, Category.assoc]
  have hq : ∀ (e : ℕ), (Over.pullback (thick R' I' e)).map g' ≫ (U'.gt e).q =
      (U'.gt e).q ≫ (Over.pullback (thick R' I' e)).map b' := by
    intro e
    have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S}
        {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (c : GtCoord J E e K)
        (u : E.P.A ⟶ E.P.A), (c.q ≫ (Over.pullback (thick S J e)).map u).left ≫
          pullback.fst E.P.A.hom (thick S J e) = c.pG.left ≫ u.left := by
      intro S _ _ J E K _ _ c u
      rw [Over.comp_left, Category.assoc, map_left_fst, PullLinear.pG_left, Category.assoc]
    have k₁ : ((Over.pullback (thick R I e)).map g).left ≫ (U.gt e).pG.left =
        (U.gt e).pG.left ≫ b.left := by
      rw [← k, ← (hlin e).1]
      exact (Category.assoc _ _ _).symm
    have k₂ : (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map g') ≫
        (U'.gt e).pG = (U'.gt e).pG ≫ b' := by
      refine ext_of_iso_pullback _ hD.e ?_
      change (((Over.pullback (thick R' I' e)).map g').left ≫ (U'.gt e).pG.left) ≫ _ =
        ((U'.gt e).pG.left ≫ b'.left) ≫ _
      rw [Category.assoc, Category.assoc, act_proj _ hD.e.hom hB, (hpt e).1,
        ← Category.assoc (U'.gt e).pG.left, (hpt e).1, ← Category.assoc, hact, Category.assoc,
        Category.assoc, k₁]
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) k₂
  refine fun e => ⟨hq e, ?_⟩
  obtain ⟨t, ht, hi⟩ := (hlin e).2
  have hk : ((U'.gt e).i ≫ (Over.pullback (thick R' I' e)).map g') ≫ (U'.gt e).q =
      toUnit _ ≫ η[thickObj R' I' e D'.toPre.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc,
      IsMonHom.one_hom]
  have hi' := (U'.gt e).isKernel.lift_fst _ _ hk
  generalize (U'.gt e).isKernel.lift _ _ hk = t' at hi'
  refine ⟨t', ?_, hi'.symm⟩
  obtain ⟨s, τ, hτ⟩ := exists_point (U.gt e) (U'.gt e) (hpt e).1 ((hpt e).2 0).1 (𝟙 _)
  have hτ' : ((τ ≫ t) ≫ (U.gt e).i).left = (t' ≫ (U'.gt e).i).left ≫ h e := by
    rw [Category.assoc, ← hi, ← Category.assoc, Over.comp_left, hτ, hi', Category.id_comp,
      Over.comp_left, Category.assoc, Category.assoc, hact]
  intro χ
  refine unit_ext fun z _ => ?_
  have e₁ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 χ).1 ((hpt e).2 χ).2 t' (τ ≫ t) hτ' z
  have e₂ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 (k' χ)).1 ((hpt e).2 (k' χ)).2
    (𝟙 _) τ hτ z
  have e₃ := (torusEndOf_iff _ _ t).1 ht _ τ.left z (hD.xe χ)
  rw [hx] at e₂
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
  rw [Category.id_comp]
  exact e₁.symm.trans (e₃.trans e₂)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFramesAgreeOnOverlapStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frames_agree_on_overlap : ∀ {ι : Type} [Fintype ι] {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ)
    (fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N) (V W : T.Opens)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (G : ι → GL (Fin N) Γ(T, V)) (H : ι → GL (Fin N) Γ(T, W)),
    Loc.Adapted g fl' V G → Loc.Adapted g fl' W H →
    T.homOfLE (inf_le_left : V ⊓ W ≤ V) ≫ hV.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G =
      T.homOfLE (inf_le_right : V ⊓ W ≤ W) ≫ hW.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd H := by
  first | exact @GlobalTheory.FlagZ.Loc.flagPt_inf_eq | exact GlobalTheory.FlagZ.Loc.flagPt_inf_eq | (intros; apply GlobalTheory.FlagZ.Loc.flagPt_inf_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanishStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧ ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom), ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b) → PrimitiveStructureSheafDegTwoVanish := by
  first | exact @GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso | exact GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso | (intros; apply GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoVanishAffineBasesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveClassDegreeTwo_vanish_affineBases_alt : PrimitiveExtendedDegTwoVanish → ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] [Quiver.IsThin D] [Quiver.IsThin T] (G : D ⥤ AffOp A.left) (H : T ⥤ AffOp (A ⊗ A).left) (K₀ K₁ K₂ : T ⥤ D) (le₀ : ∀ t, (H.obj t).unop.1 ≤ (μ[A]).left ⁻¹ᵁ (G.obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ (fst A A).left ⁻¹ᵁ (G.obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ (snd A A).left ⁻¹ᵁ (G.obj (K₂.obj t)).unop.1), IsBasis G → IsBasis H → ∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ (G ⋙ OAff A.hom)), (extMap R₁ (pullMap (overW μ[A]) G H K₀ le₀)).pull2 c = (extMap R₁ (pullMap (overW (fst A A)) G H K₁ le₁)).pull2 c + (extMap R₁ (pullMap (overW (snd A A)) G H K₂ le₂)).pull2 c → c = 0 := by
  first | exact @GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases | exact GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases | (intros; apply GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumFractionFieldEqMulIntegralCongr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.Poinc.AdicTerm

theorem eq_zero_of_mem_pow_smul {V E : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    [AddCommGroup E] [Module V E] (N : Submodule V E) (hN : N.FG) (w : E)
    (h : ∀ n : ℕ, w ∈ maximalIdeal V ^ n • N) : w = 0 := by
  have hw : w ∈ N := Submodule.smul_le_right (h 0)
  haveI : Module.Finite V N := Module.Finite.iff_fg.mpr hN
  have hb := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (maximalIdeal V)
    (maximalIdeal.isMaximal V).ne_top
  have hm : (⟨w, hw⟩ : N) ∈ (⨅ n : ℕ, maximalIdeal V ^ n • ⊤ : Submodule V N) := by
    rw [Submodule.mem_iInf]
    intro n
    exact (Submodule.mem_smul_top_iff _ N _).mpr (h n)
  rw [hb, Submodule.mem_bot] at hm
  exact congrArg Subtype.val hm

theorem sumI_smul {V E : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    [AddCommGroup E] [Module V E] {Ix : Type} (i₀ : Ix) (x : Ix → E) (y : Ix → V) (k v : E)
    (hx : ∀ i, x i = y i • k) (hy : ∀ i, i ≠ i₀ → y i ∈ maximalIdeal V)
    (hs : SumI (maximalIdeal V) x v) :
    ∃ S : V, v = S • k ∧ S - y i₀ ∈ maximalIdeal V := by
  classical
  obtain ⟨N, hN, -, -, hS⟩ := hs
  let P : Submodule V E := Submodule.map (LinearMap.toSpanSingleton V E k) (maximalIdeal V)
  have key : P.mkQ (v - y i₀ • k) = 0 := by
    refine eq_zero_of_mem_pow_smul (N.map P.mkQ) (hN.map _) _ fun n => ?_
    obtain ⟨S, hS⟩ := hS n
    have h1 := hS (insert i₀ S) (Finset.subset_insert _ _)
    have h2 : P.mkQ (v - ∑ i ∈ insert i₀ S, x i) ∈ maximalIdeal V ^ n • N.map P.mkQ := by
      rw [← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem h1
    have h3 : ∑ i ∈ (insert i₀ S).erase i₀, x i ∈ P := by
      refine Submodule.sum_mem _ fun i hi => ?_
      exact ⟨y i, hy i (Finset.ne_of_mem_erase hi), by simp [hx i]⟩
    have h4 : P.mkQ (∑ i ∈ (insert i₀ S).erase i₀, x i) = 0 :=
      (Submodule.Quotient.mk_eq_zero P).mpr h3
    have h5 : v - y i₀ • k =
        (v - ∑ i ∈ insert i₀ S, x i) + ∑ i ∈ (insert i₀ S).erase i₀, x i := by
      rw [← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S), hx i₀]
      abel
    rw [h5, map_add, h4, add_zero]
    exact h2
  obtain ⟨a, ha, hak⟩ := (Submodule.Quotient.mk_eq_zero P).mp key
  refine ⟨y i₀ + a, ?_, by simpa using ha⟩
  have hak' : a • k = v - y i₀ • k := by simpa using hak
  rw [add_smul, hak']
  abel

theorem sumF_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Ix : Type) (i₀ : Ix) (x : Ix → FractionRing V) (y : Ix → V) (κ v : FractionRing V), (∀ i, x i = κ * algebraMap V (FractionRing V) (y i)) → (∀ i, i ≠ i₀ → y i ∈ maximalIdeal V) → SumF (maximalIdeal V) (FractionRing V) x v → ∃ S : V, v = κ * algebraMap V (FractionRing V) S ∧ S - y i₀ ∈ maximalIdeal V := by
  intro V _ _ _ _ Ix i₀ x y κ v hx hy hs
  have h := @sumI_smul V (FractionRing V) _ _ _ _
    (Module.compHom (FractionRing V) (algebraMap V (FractionRing V))) Ix i₀ x y κ v
    (fun i => (hx i).trans (mul_comm _ _)) hy hs
  obtain ⟨S, h1, h2⟩ := h
  exact ⟨S, h1.trans (mul_comm _ _), h2⟩

end GlobalTheory.Poinc.AdicTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumSectionsPullbacksValueAbelianPartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicSum_sections_pullbacks_value_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ X)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb N φ ε)) (n₀ : LB.Sec (LB.LinComb N φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good N z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb N (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good N z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  first | exact @GlobalTheory.SecAdicSumAny.sumF_of_sum_on_thickenings_any | exact GlobalTheory.SecAdicSumAny.sumF_of_sum_on_thickenings_any | (intros; apply GlobalTheory.SecAdicSumAny.sumF_of_sum_on_thickenings_any <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertRealMultiplicationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appell_humbert_real_multiplication : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) → (F →+* ℂ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ e j (a : F) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (Hm : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    ∀ (a : 𝓞 F) i j, e i (a : F) * Hm i j = Hm i j * starRingEnd ℂ (e j (a : F)) := by
  first | exact @GlobalTheory.RosatiAH.rosati_diag | exact GlobalTheory.RosatiAH.rosati_diag | (intros; apply GlobalTheory.RosatiAH.rosati_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
section
theorem GlobalTheory.CubeTop.cubeTheorem : GlobalTheory.Published.CubeTheorem := GlobalTheory.SpreadingModels.cubeTheorem_holds
end

