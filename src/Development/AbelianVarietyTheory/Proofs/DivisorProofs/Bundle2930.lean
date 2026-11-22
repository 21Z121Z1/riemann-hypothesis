import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2853
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2851
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatSurjectiveKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCorrFormPullTensorForm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.AbDatum GlobalTheory.ConjSeq
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrobAdjoint

section Dual

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] {P : LB (A ⊗ A).left}

omit [GrpObj A] in

theorem evc_comm (hP : P.IsLB) (hs : LBIso (swap P) P) (a b : Y ⟶ A) : evc hP a b = evc hP b a := by
  have h' : (swap P).IsLB := pull_isLB hP _
  rw [← evc_swap hP h', evc, evc, (cls_eq_iff h' hP).2 hs]

theorem evc_mul_right (hd : IsDual A A P) (hs : LBIso (swap P) P) (a b b' : Y ⟶ A) :
    evc hd.isLB a (b * b') = evc hd.isLB a b + evc hd.isLB a b' := by
  rw [evc_comm _ hs, (isAdditive_iff hd.isLB).1 hd.additive, evc_comm _ hs b, evc_comm _ hs b']

theorem evc_pow_right (hd : IsDual A A P) (hs : LBIso (swap P) P) (a b : Y ⟶ A) (n : ℕ) :
    evc hd.isLB a (b ^ n) = n • evc hd.isLB a b := by
  induction n with
  | zero => rw [pow_zero, evc_one_right hd.isLB hd.zero, zero_smul]
  | succ n ih => rw [pow_succ, evc_mul_right hd hs, ih, succ_nsmul]

theorem dual_ext {B : Over S} [GrpObj B] {P : LB (A ⊗ B).left} (hd : IsDual A B P) {x y : T ⟶ B}
    (h : evc hd.isLB (fst A T) (snd A T ≫ x) = evc hd.isLB (fst A T) (snd A T ≫ y)) : x = y := by
  have hM : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB hd.isLB _
  refine (hd.univ T _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ ?_)).unique
    ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB hd.isLB _)).1 h)
  simp only [evc_ev hd.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hd.isLB).1 hd.additive _ _ _ _

end Dual

section Down

variable {R R' : Type} [CommRing R] [CommRing R'] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
  {σ : R →+* R'} {φ : A'.left ⟶ A.left}

def down (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x : Y ⟶ A') :
    Over.mk (Y.hom ≫ spMap σ) ⟶ A :=
  Over.homMk (x.left ≫ φ) (by simp [m.w])

theorem down_mul (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x y : Y ⟶ A') :
    down m (x * y) = down m x * down m y :=
  Over.OverMorphism.ext (m.mul Y x y (down m x) (down m y) rfl rfl).symm

theorem exists_corr (H : GlobalTheory.Published.AbelianDeRham) {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (h : IsGrpPullback A' A (spMap σ) φ) (y : HdR A) :
    ∃ y' : HdR A', ∀ c, y' ((grpMor_of_isGrpPullback h).pull c) = σ (y c) :=
  letI := σ.toAlgebra
  (H.2.2.1 R A g hA hg R' A' φ h).1.exists y

end Down

section Frob

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0) {A A₁ : Over (Sp R)} [GrpObj A] [GrpObj A₁]
  {π : A₁.left ⟶ A.left}

theorem exists_frob_versch (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) {P : LB (A ⊗ A).left}
    (hd : IsDual A A P) (hs : LBIso (swap P) P) :
    ∃ (F : A ⟶ A₁) (V : A₁ ⟶ A) (h : (A ⊗ A₁).left ⟶ (A ⊗ A).left), IsMonHom F ∧ IsMonHom V ∧
      F.left ≫ π = VB.frob A.left p (cast_left p R hR A) ∧ F ≫ V = 𝟙 A ^ p ∧
      h ≫ (fst A A).left = (fst A A₁).left ≫ VB.frob A.left p (cast_left p R hR A) ∧
      h ≫ (snd A A).left = (snd A A₁).left ≫ π ∧ LBIso (P.pull h) (ev P (fst A A₁) (snd A A₁ ≫ V)) := by
  have mF := frobMor p R hR A (cast_left p R hR A)
  have mπ := grpMor_of_isGrpPullback hπ
  let F : A ⟶ A₁ := liftPt hπ A.hom _ mF.w
  have hF : F.left ≫ π = _ := liftPt_left hπ A.hom _ mF.w
  have dF : ∀ {Y : Over (Sp R)} (t : Y ⟶ A), down mπ (t ≫ F) = down mF t := fun t ↦
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans (congrArg (t.left ≫ ·) hF))
  obtain ⟨h, h₁, h₂⟩ : ∃ h : (A ⊗ A₁).left ⟶ (A ⊗ A).left,
      h ≫ (fst A A).left = (fst A A₁).left ≫ VB.frob A.left p (cast_left p R hR A) ∧
      h ≫ (snd A A).left = (snd A A₁).left ≫ π :=
    ⟨pullback.lift _ _ (by
      rw [Category.assoc, Category.assoc, mF.w, mπ.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hM : (P.pull h).IsLB := pull_isLB hd.isLB _
  have eM : ∀ {Y : Over (Sp R)} (a : Y ⟶ A) (b : Y ⟶ A₁), evc hM a b = evc hd.isLB (down mF a) (down mπ b) :=
    fun a b ↦ evc_eq h₁ h₂ hd.isLB hM ((cls_eq_iff hM hM).1 rfl) a b _ _ rfl rfl
  obtain ⟨V, hV, -⟩ := hd.univ A₁ _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ by
    rw [eM, eM, eM, down_mul]
    exact (isAdditive_iff hd.isLB).1 hd.additive _ _ _ _)
  have eV : ∀ {Y : Over (Sp R)} (a : Y ⟶ A) (b : Y ⟶ A₁),
      evc hd.isLB a (b ≫ V) = evc hd.isLB (down mF a) (down mπ b) := fun a b ↦ by
    have h' : (ev P (fst A A₁) (snd A A₁ ≫ V)).IsLB := pull_isLB hd.isLB _
    have e : evc hM a b = evc h' a b := by rw [evc, evc, (cls_eq_iff hM h').2 hV]
    rw [← eM, e, evc_ev hd.isLB, lift_fst, lift_snd_assoc]
  refine ⟨F, V, h, isMonHom_of_mul _ fun T x y ↦ pt_ext hπ ?_, isMonHom_of_mul _ fun T x y ↦ dual_ext hd ?_,
    hF, dual_ext hd ?_, h₁, h₂, hV⟩
  · have e : down mπ ((x * y) ≫ F) = down mπ ((x ≫ F) * (y ≫ F)) := by rw [down_mul, dF, dF, dF, down_mul]
    exact congrArg (fun z ↦ z.left) e
  · rw [MonObj.comp_mul, evc_mul_right hd hs, ← Category.assoc, ← Category.assoc, ← Category.assoc, eV, eV, eV,
      MonObj.comp_mul, down_mul, evc_mul_right hd hs]
  · have h0 := cast_left p R hR (A ⊗ A)
    have hP' : (P.pull (VB.frob _ p h0)).IsLB := pull_isLB hd.isLB _
    rw [← Category.assoc, eV, dF, MonObj.comp_pow, evc_pow_right hd hs, Category.comp_id,
      ← evc_eq (VB.frob_naturality p _ (fst A A).left h0) (VB.frob_naturality p _ (snd A A).left h0) hd.isLB hP'
        ((cls_eq_iff hP' hP').1 rfl) (fst A A) (snd A A) _ _ rfl rfl, evc, evc, VB.cls_pull_frob p h0 hd.isLB, map_nsmul]

variable {G : PDivGroup p R} (t : G.TorsionTower A)

theorem absFrob_y (n : ℕ) : spMap ((absFrob hR G).app n).toRingHom ≫ (t.y n).left =
    (t.y n).left ≫ VB.frob A.left p (cast_left p R hR A) := by
  have h := natCast_eq_zero_of_algebra hR (G.A n)
  exact (congrArg (· ≫ (t.y n).left) (frob_sp p _ h (SS.FrobField.cast_zero_sp _ h)).symm).trans
    (VB.frob_naturality p _ (t.y n).left _)

theorem exists_tower (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) :
    ∃ t₁ : (frobTwist hR G).TorsionTower A₁, ∀ n,
      spMap ((frobProj hR G).app n).toRingHom ≫ (t.y n).left = (t₁.y n).left ≫ π :=
  letI := (frobRing hR).toAlgebra
  ⟨t.baseChange (O' := R) hπ, t.toBase_y (O' := R) hπ⟩

theorem map_eq_verschiebung (t₁ : (frobTwist hR G).TorsionTower A₁)
    (ht : ∀ n, spMap ((frobProj hR G).app n).toRingHom ≫ (t.y n).left = (t₁.y n).left ≫ π)
    (F : A ⟶ A₁) (V : A₁ ⟶ A) [IsMonHom F] [IsMonHom V]
    (hF : F.left ≫ π = VB.frob A.left p (cast_left p R hR A)) (hV : F ≫ V = 𝟙 A ^ p) :
    t₁.map t V = verschiebung hR G := by
  have e : t.map t₁ F = relFrob hR G := frobTwist_hom_ext hR fun n a ↦
    (t₁.semiOf_semiOf t t (s' := SemiHom.ofHom (t.map t₁ F)) (s'' := absFrob hR G) (ψ := F.left) ht
      (fun n ↦ congrArg Over.Hom.left (t.map_y t₁ F n)) (fun n ↦ by rw [hF]; exact absFrob_y hR t n) n a).symm.trans
      ((absFrob_app hR G n a).trans (relFrob_app_frobProj hR n a).symm)
  have : IsMonHom (𝟙 A ^ p) := hV ▸ inferInstance
  refine eq_verschiebung_of_relFrob_comp hR ?_
  rw [← e, ← t.map_comp, t.map_congr t hV, t.map_pow_id]

end Frob

section Pairing

open GlobalTheory.CatCoh GlobalTheory.AbLaw

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A B : Over S} [GrpObj A] [GrpObj B]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' B' : Over S'} [GrpObj A'] [GrpObj B']

theorem isCorrForm_pull_tensorForm {P : LB (A ⊗ B).left} (hP : P.IsLB) {N : ℕ} {a : Fin N → prim κ t A}
    {c : Fin N → prim κ t B} (hc : IsChern κ ((A ⊗ B).hom ≫ t) P
      (∑ k, cup _ (pullOver κ t (fst A B) (a k).1) (pullOver κ t (snd A B) (c k).1)))
    {σ : R →+* R'} {b : S' ⟶ S} {f : A'.left ⟶ A.left}
    {g : B'.left ⟶ B.left} (m : GrpMor κ t A κ' t' A' σ b f) (n : GrpMor κ t B κ' t' B' σ b g)
    {h : (A' ⊗ B').left ⟶ (A ⊗ B).left} (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f)
    (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsCorrForm κ' t' A' B' (P.pull h) (tensorForm κ' t' A' B' (fun i ↦ m.pull (a i)) fun i ↦ n.pull (c i)) := by
  have k := grpMor_prod m n h₁ h₂
  refine ⟨N, _, _, ?_, tensorForm_apply _ _ _ _ _ _⟩
  have := isChern_pull k.isMor hc
  rw [map_sum] at this
  convert this using 2 with i
  rw [IsMor.pullCohomologyTwo_cup]
  congr 1
  · congr 1
    exact (IsMor.pullback1_comp _ _ (m.comp (homMor κ' t' (fst A' B'))).isMor (fun _ ↦ rfl) rfl _).trans
      (IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) h₁ _).symm
  · exact (IsMor.pullback1_comp _ _ (n.comp (homMor κ' t' (snd A' B'))).isMor (fun _ ↦ rfl) rfl _).trans
      (IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) h₂ _).symm

theorem exists_eq_sum {K : Type} [Field K] {M : Type*} [AddCommGroup M] [Module K M] [Module.Finite K M] {N : ℕ}
    (a c : Fin N → M) (β : M → Module.Dual K M) (hβ : ∀ s (y : Module.Dual K M), ∑ k, β s (a k) * y (c k) = y s)
    (z : M) : ∃ y : Module.Dual K M, ∑ k, y (c k) • a k = z := by
  let T : Module.Dual K M →ₗ[K] M := ∑ k, (Module.Dual.eval K M (c k)).smulRight (a k)
  have hT : ∀ y, T y = ∑ k, y (c k) • a k := fun y ↦ by simp [T, LinearMap.sum_apply]
  have inj : Function.Injective T := (injective_iff_map_eq_zero _).2 fun y hy ↦ LinearMap.ext fun s ↦ by
    have e := congrArg (β s) ((hT y).symm.trans hy)
    rw [map_sum, map_zero] at e
    rw [← hβ, LinearMap.zero_apply, ← e]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq).1 inj z
  exact ⟨y, (hT y).symm.trans hy⟩

end Pairing

theorem frob_adjoint_verschiebung : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.CubeTheorem → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (hK : (p : K) = 0) (A : Over (Sp K)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A), SmoothOfRelativeDimension g A.hom → ∀ P : LB (A ⊗ A).left, IsDual A A P → LBIso (swap P) P → ∀ (ψ : HdR A →ₗ[K] HdR A →ₗ[K] K) (β : primDR A →ₗ[K] HdR A), IsCorrForm (dp0 K) (𝟙 _) A A P ψ → (∀ s y, ψ (β s) y = y s) → ∀ (e : GlobalTheory.Published.DeRhamVectorExtension.Family p), e.Natural → ∀ (hn : IsNilpotent (p : K)) (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A), (∀ z, e hn hA t (frobDR p K hK A z) = (absFrob hK 𝒜).rig (e hn hA t z)) ∧ ∀ (s z : primDR A) (n : ℕ) (r : Fin n → K) (w : Fin n → primDR A), rigExtMap (verschiebung hK 𝒜) (e hn hA t s) = ∑ i, r i • (frobProj hK 𝒜).rig (e hn hA t (w i)) → β s (frobDR p K hK A z) = ∑ i, r i * (β (w i) z) ^ p := by
  intro H _ p _ K _ hK A _ g hA hg P hd hs ψ β hψ hβ e he hn 𝒜 t
  refine ⟨fun z ↦ ?_, fun s z n r w hw ↦ ?_⟩
  · rw [(t.eq_semiOf_iff t (frobMor p K hK A (cast_left p K hK A)) (absFrob hK 𝒜)).2 (absFrob_y hK t)]
    exact he hn hn hA hA t t _ z
  let A₁ := (Over.pullback (spMap (frobR p K hK))).obj A
  have hπ : IsGrpPullback A₁ A _ _ := isGrpPullback_pullback A (spMap (frobR p K hK))
  have hA₁ : IsAbelianScheme A₁ := isAbelianScheme_pullback_obj _ A hA
  have hg₁ : SmoothOfRelativeDimension g A₁.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hπ.1 hg
  obtain ⟨F, V, h, _, _, hF, hV, h₁, h₂, hh⟩ := exists_frob_versch hK hπ hd hs
  obtain ⟨t₁, ht⟩ := exists_tower hK t hπ
  have mF := frobMor p K hK A (cast_left p K hK A)
  have mπ := grpMor_of_isGrpPullback hπ
  have hw' : primPull (dp0 K) (𝟙 _) V s = ∑ i, r i • mπ.pull (w i) := (e hn hA₁ t₁).injective (by
    rw [he.primPull hn hA₁ hA t₁ t, map_eq_verschiebung hK t t₁ ht F V hF hV, hw, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, he hn hn hA hA₁ t t₁ mπ, (t₁.eq_semiOf_iff t mπ (frobProj hK 𝒜)).2 ht])
  have C := cupSquare_of_free H.1 (AbelianSchemeGerms.isAbelianScheme_tensor A A₁ hA hA₁) (smooth_prod hg hg₁)
  have hM : (P.pull h).IsLB := LB.isLB_pull hd.isLB _
  have hM' : (ev P (fst A A₁) (snd A A₁ ≫ V)).IsLB := LB.isLB_pull hd.isLB _
  obtain ⟨χ, hχ, k⟩ := hψ.pull hd.isLB (homMor (dp0 K) (𝟙 _) (𝟙 A)) (homMor (dp0 K) (𝟙 _) V)
    (h := (lift (fst A A₁) (snd A A₁ ≫ V)).left)
    (by simp only [← Over.comp_left, lift_fst, Category.comp_id]) (by simp only [← Over.comp_left, lift_snd]) hM
    ((CechPic.cls_eq_iff hM' hM).1 ((CechPic.cls_eq_iff hM hM').2 hh).symm)
  obtain ⟨N, a, c, hc, hφ⟩ := hψ
  obtain rfl := (isCorrForm_pull_tensorForm hd.isLB hc mF mπ h₁ h₂).unique C hM hχ
  have := (GlobalTheory.Published.AbelianDeRham.Free.prim H.1 hA hg).1
  obtain ⟨y, rfl⟩ := exists_eq_sum a c β (fun s y ↦ (hφ _ _).symm.trans (hβ s y)) z
  obtain ⟨y₁, hy⟩ := exists_corr H hA hg hπ y
  have k₁ := k (push _ _ (𝟙 A) (β s)) (β s) (push _ _ V y₁) y₁ (fun _ ↦ rfl) fun _ ↦ rfl
  rw [push_id, LinearMap.id_apply, hβ, RingHom.id_apply, push_apply, hw', tensorForm_apply, map_sum] at k₁
  have hz : ∀ x : HdR A, x (∑ k, y (c k) • a k) = ψ x y := fun x ↦ by
    rw [hφ, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
  simp only [hz, hβ]
  rw [map_sum, map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun k _ ↦ ?_) (k₁.trans (Finset.sum_congr rfl fun i _ ↦ ?_))
  · rw [map_smulₛₗ, map_smul, smul_eq_mul, mul_comm, hy]
    rfl
  · rw [map_smul, smul_eq_mul, hy, frobR_apply]

end GlobalTheory.FrobAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCompletionOfQuasiFiniteGaloisRigid
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QFEtale

theorem isEtaleCompletion_of_galRigid : ∀ (O R : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (f : O →+* R) [IsLocalHom f], IsAdicComplete (maximalIdeal R) R → (∀ p : Ideal R, p.IsPrime → (maximalIdeal O).map f ≤ p → p = maximalIdeal R) → ((residue R).comp f).Finite → ringKrullDim O ≤ ringKrullDim R → GalRigid f → IsEtaleCompletion f ∧ ((residue R).comp f).FormallyUnramified := by
  intro O R _ _ _ _ _ _ _ _ _ _ f _ hRc hqf hfin hdim hrig
  haveI hOn : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℤ O
  letI : Algebra (ResidueField O) (ResidueField R) := (ResidueField.map f).toAlgebra
  have hres : (residue R).comp f = (ResidueField.map f).comp (residue O) := by
    ext o; simp [ResidueField.map_residue]
  have hfin' : (ResidueField.map f).Finite := by
    rw [hres] at hfin; exact RingHom.Finite.of_comp_finite hfin
  haveI : Module.Finite (ResidueField O) (ResidueField R) := hfin'
  let M := separableClosure (ResidueField O) (ResidueField R)
  let m : ResidueField O →+* M := algebraMap (ResidueField O) M
  have hmf : m.Finite := RingHom.finite_algebraMap.2 inferInstance
  haveI : Algebra.IsSeparable (ResidueField O) M := inferInstance
  haveI : Algebra.FormallyUnramified (ResidueField O) M := Algebra.FormallyUnramified.of_isSeparable _ _
  have hmu : m.FormallyUnramified := RingHom.formallyUnramified_algebraMap.2 inferInstance
  obtain ⟨A, _, _, _, ψ, hψl, E, hAcn, hψe, hψu, hE⟩ := GlobalTheory.T.exists_etaleCompletion_with_residueField_equiv O M m hmf hmu
  obtain ⟨hAn, hAi, hAc, hA0⟩ := hAcn
  let u' : A →+* ResidueField R := (algebraMap M (ResidueField R)).comp ((E.symm : ResidueField A →+* M).comp (residue A))
  have hu' : ∀ a, u' a = 0 ↔ a ∈ maximalIdeal A := by
    intro a
    rw [← residue_eq_zero_iff]
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, map_eq_zero_iff _ (algebraMap M (ResidueField R)).injective,
      map_eq_zero_iff _ E.symm.injective]
  have hker : RingHom.ker u' = maximalIdeal A := by ext a; exact hu' a
  have hc : (residue R).comp f = u'.comp ψ := by
    ext o
    have h1 := RingHom.congr_fun hE (residue O o)
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ResidueField.map_residue] at h1
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, ← h1, RingEquiv.symm_apply_apply, m]
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  obtain ⟨b, hb1, hb2⟩ := GlobalTheory.EtaleCompletionLift.exists_extension O A R (ResidueField R) ψ f u' (residue R) hψe hψu hRc
    inferInstance hker (ker_residue) hc (fun r => residue_surjective _)
  have hbm : ∀ a, b a ∈ maximalIdeal R ↔ a ∈ maximalIdeal A := by
    intro a
    rw [← residue_eq_zero_iff, ← hu', ← RingHom.comp_apply, hb2]
  haveI hbl : IsLocalHom b := ⟨fun a ha => by
    by_contra h
    exact (mem_maximalIdeal _).1 ((hbm a).2 ((mem_maximalIdeal a).2 h)) ha⟩
  have hbfin : b.Finite := by
    refine GlobalTheory.T.ringHom_finite_of_quasiFinite_complete_local A R b hAc (fun p hp h => hqf p hp ?_) ?_
    · rw [← hb1, ← Ideal.map_map, hψe.2.1]; exact h
    · refine RingHom.Finite.of_comp_finite (f := ψ) ?_
      rw [RingHom.comp_assoc, hb1]; exact hfin
  have hbinj : Function.Injective b := GlobalTheory.T.injective_of_finite_of_ringKrullDim_le' A R b hbfin ((GlobalTheory.T.ringKrullDim_le_of_isEtaleCompletion' O A ψ hψe).trans hdim)
  obtain ⟨R', _, _, _, θ, hR'cn, hθl, hθi, hθf, hfix⟩ := GlobalTheory.T.exists_completeNormal_galois_cover_of_finite A R b ⟨hAn, hAi, hAc, hA0⟩ hbfin hbinj
  let q := ringExpChar M
  haveI : ExpChar M q := ringExpChar.expChar M
  haveI : ExpChar (ResidueField R) q := expChar_of_injective_algebraMap (algebraMap M (ResidueField R)).injective q
  have hpi : ∀ x : ResidueField R, ∃ n : ℕ, ∃ a : A, x ^ q ^ n = residue R (b a) := by
    intro x
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem M q x
    obtain ⟨a, ha⟩ := residue_surjective (E y)
    refine ⟨n, a, ?_⟩
    rw [← RingHom.comp_apply, hb2, ← hy]
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, ha, RingEquiv.symm_apply_apply]
  have hbsurj : Function.Surjective b := by
    intro r
    refine hfix r fun σ hσ hσb => hrig R' θ σ hR'cn hθi hθf hσ (fun o => ?_) (fun r => GlobalTheory.T.ringEquiv_sub_mem_maximalIdeal_of_purelyInsep_residue A R R' b θ q σ hpi hσb r) r
    rw [← hb1]; exact hσb (ψ o)
  have hmapsurj : Function.Surjective (ResidueField.map b) := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hbsurj r
    exact ⟨residue A a, ResidueField.map_residue _ _⟩
  have hres2 : (residue R).comp f = (ResidueField.map b).comp ((residue A).comp ψ) := by
    rw [← hb1]; ext o; simp [ResidueField.map_residue]
  refine ⟨⟨?_, ?_, hfin⟩, ?_⟩
  · rw [← hb1]; exact RingHom.Flat.comp hψe.1 (RingHom.Flat.of_bijective ⟨hbinj, hbsurj⟩)
  · rw [← hb1, ← Ideal.map_map, hψe.2.1]; exact map_maximalIdeal_of_surjective b hbsurj
  · rw [hres2]; exact RingHom.FormallyUnramified.comp hψu (RingHom.FormallyUnramified.of_surjective hmapsurj)

end GlobalTheory.QFEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteNormalNormalisationProjectiveSpaceArithStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_normal_normalisation_projectiveSpace_arith : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → IsFinite f.fromNormalization ∧ Geo.Tor.IsNormalScheme f.normalization := by
  first | exact @GlobalTheory.ThetaFin.isFinite_fromNormalization_and_normal | exact GlobalTheory.ThetaFin.isFinite_fromNormalization_and_normal | (intros; apply GlobalTheory.ThetaFin.isFinite_fromNormalization_and_normal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackPasteFactorisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GrpPullbackPaste

theorem mul_left_congr {B : Scheme.{0}} (Gb : Over B) [GrpObj Gb] {X : Scheme.{0}} (a b : X ⟶ B) (hab : a = b)
    (x y : Over.mk a ⟶ Gb) (x' y' : Over.mk b ⟶ Gb) (hx : x.left = x'.left) (hy : y.left = y'.left) :
    (x * y).left = (x' * y').left := by
  subst hab
  have h1 : x = x' := Over.OverMorphism.ext hx
  have h2 : y = y' := Over.OverMorphism.ext hy
  rw [h1, h2]

end GlobalTheory.GrpPullbackPaste

open GlobalTheory.GrpPullbackPaste in
theorem GlobalTheory.isGrpPullback_paste : ∀ {B S T T' : Scheme.{0}} (Gb : Over B) [GrpObj Gb] (Gs : Over S) [GrpObj Gs] (Gt : Over T) [GrpObj Gt] (Gt' : Over T') [GrpObj Gt'] (fS : S ⟶ B) (fT : T ⟶ B) (g : T' ⟶ T) (h : T' ⟶ S) (φS : Gs.left ⟶ Gb.left) (φT : Gt.left ⟶ Gb.left) (ψ : Gt'.left ⟶ Gt.left), IsGrpPullback Gs Gb fS φS → IsGrpPullback Gt Gb fT φT → IsGrpPullback Gt' Gt g ψ → h ≫ fS = g ≫ fT → ∃ φ : Gt'.left ⟶ Gs.left, IsGrpPullback Gt' Gs h φ ∧ φ ≫ φS = ψ ≫ φT := by
  intro B S T T' Gb _ Gs _ Gt _ Gt' _ fS fT g h φS φT ψ hS hT hψ hcomm
  have hsq : (ψ ≫ φT) ≫ Gb.hom = (Gt'.hom ≫ h) ≫ fS := by
    rw [Category.assoc, hT.1.w, ← Category.assoc, hψ.1.w, Category.assoc, Category.assoc, hcomm]
  refine ⟨hS.1.lift (ψ ≫ φT) (Gt'.hom ≫ h) hsq, ⟨?_, ?_⟩, hS.1.lift_fst _ _ hsq⟩
  · have hpaste := hψ.1.paste_horiz hT.1
    refine IsPullback.of_right ?_ (hS.1.lift_snd _ _ hsq) hS.1
    rw [hS.1.lift_fst _ _ hsq, hcomm]
    exact hpaste
  · intro X x y x₀ y₀ hx hy
    set φ := hS.1.lift (ψ ≫ φT) (Gt'.hom ≫ h) hsq with hφ
    have hφ1 : φ ≫ φS = ψ ≫ φT := hS.1.lift_fst _ _ hsq
    have hφ2 : φ ≫ Gs.hom = Gt'.hom ≫ h := hS.1.lift_snd _ _ hsq
    let mk1 (z : Over.mk (X.hom ≫ h) ⟶ Gs) : Over.mk ((Over.mk (X.hom ≫ h)).hom ≫ fS) ⟶ Gb :=
      Over.homMk (z.left ≫ φS) (by
        simp only [Over.mk_hom, Category.assoc]
        rw [hS.1.w, ← Category.assoc, Over.w z]
        rfl)
    let mk2 (z : X ⟶ Gt') : Over.mk (X.hom ≫ g) ⟶ Gt :=
      Over.homMk (z.left ≫ ψ) (by
        simp only [Over.mk_hom, Category.assoc]
        rw [hψ.1.w, ← Category.assoc, Over.w z])
    let mk3 (z : Over.mk (X.hom ≫ g) ⟶ Gt) : Over.mk ((Over.mk (X.hom ≫ g)).hom ≫ fT) ⟶ Gb :=
      Over.homMk (z.left ≫ φT) (by
        simp only [Over.mk_hom, Category.assoc]
        rw [hT.1.w, ← Category.assoc, Over.w z]
        rfl)
    have e1 := hS.2 (Over.mk (X.hom ≫ h)) x₀ y₀ (mk1 x₀) (mk1 y₀) rfl rfl
    have e2 := hψ.2 X x y (mk2 x) (mk2 y) rfl rfl
    have e3 := hT.2 (Over.mk (X.hom ≫ g)) (mk2 x) (mk2 y) (mk3 (mk2 x)) (mk3 (mk2 y)) rfl rfl
    have hab : (Over.mk (X.hom ≫ h)).hom ≫ fS = (Over.mk (X.hom ≫ g)).hom ≫ fT := by
      simp only [Over.mk_hom, Category.assoc, hcomm]
    have e4 := mul_left_congr Gb _ _ hab (mk1 x₀) (mk1 y₀) (mk3 (mk2 x)) (mk3 (mk2 y))
      (by simp only [mk1, mk2, mk3, Over.homMk_left, hx, Category.assoc, hφ1])
      (by simp only [mk1, mk2, mk3, Over.homMk_left, hy, Category.assoc, hφ1])
    apply hS.1.hom_ext
    · rw [Category.assoc, hφ1, ← e1, e4, e3, ← Category.assoc, e2]
    · rw [Category.assoc, hφ2, ← Category.assoc, Over.w (x * y), Over.w (x₀ * y₀)]
      rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackThickeningOfCarriesTorusCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_thickening_of_carries_torusCoordinates : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → IsGrpPullback (thickObj R' I e G') Y.H (thick R' I e ≫ spMap ρ) φ := by
  first | exact @GlobalTheory.FormalModel.isGrpPullback_of_carries | exact GlobalTheory.FormalModel.isGrpPullback_of_carries | (intros; apply GlobalTheory.FormalModel.isGrpPullback_of_carries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImmersionOfForallAffineSurjectiveAppLE
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isImmersion_of_forall_affine_surjective_appLE : ∀ (Y Z : Scheme.{0}) (φ : Y ⟶ Z), (∀ y : Y, ∃ (U : Z.Opens) (W : Y.Opens) (h : W ≤ φ ⁻¹ᵁ U), IsAffineOpen U ∧ φ y ∈ U ∧ φ ⁻¹ᵁ U ≤ W ∧ IsAffineOpen W ∧ Function.Surjective (φ.appLE U W h).hom) → IsImmersion φ := by
  intro Y Z φ H
  have H' : ∀ y : Y, ∃ U : Z.Opens, φ y ∈ U ∧ IsClosedImmersion (φ ∣_ U) := by
    intro y
    obtain ⟨U, W, h, hU, hy, hW, hWa, hs⟩ := H y
    obtain rfl : W = φ ⁻¹ᵁ U := le_antisymm h hW
    refine ⟨U, hy, ?_⟩
    have : IsAffine U := hU
    have : IsAffine (φ ⁻¹ᵁ U) := hWa
    rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (Arrow.isoMk hWa.isoSpec hU.isoSpec (Scheme.Opens.toSpecΓ_naturality φ _) :
        Arrow.mk (φ ∣_ U) ≅ Arrow.mk (Spec.map (φ.app U)))]
    rw [Scheme.Hom.app_eq_appLE]
    exact IsClosedImmersion.spec_of_surjective _ hs
  choose U hyU hU using H'
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) U ?_ fun y => ?_
  · rintro _ ⟨y, rfl⟩
    exact (le_iSup U y : U y ≤ ⨆ i, U i) (hyU y)
  · have := hU y
    infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemOfValNonnegOverCompleteDVRStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralElem_of_val_nonneg_over_completeDVR : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v → ∀ z : F, 0 ≤ v z → ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).IsIntegralElem z := by
  first | exact @GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg | exact GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg | (intros; apply GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularFderivConstantVectorUniformisedStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegular_fderiv_constant_vector_uniformised : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (b : Γ(A.left, U)) (w : Fin g → ℂ), IsReg u.ex U fun z => fderiv ℂ (val u.ex U b) z w := by
  first | exact @GlobalTheory.CechPer.isReg_fderiv_val | exact GlobalTheory.CechPer.isReg_fderiv_val | (intros; apply GlobalTheory.CechPer.isReg_fderiv_val <;> assumption)
end

