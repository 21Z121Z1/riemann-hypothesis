import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PhiRelTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem isPullback_kernel_baseChange {S S' : Scheme.{0}} (f : S' ⟶ S) {T G B : Over S} [GrpObj B]
    {i : T ⟶ G} {q : G ⟶ B} (h : IsPullback i (toUnit _) q (η[B])) :
    IsPullback ((Over.pullback f).map i) (toUnit _) ((Over.pullback f).map q) (η[(Over.pullback f).obj B]) := by
  refine (h.map (Over.pullback f)).of_iso (Iso.refl _) (Iso.refl _)
    (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _) (by simp) (toUnit_unique _ _) (by simp) ?_
  simp [Functor.obj.η_def]

theorem isPullback_pullback_map_left {S S' : Scheme.{0}} (f : S' ⟶ S) {G B : Over S} (q : G ⟶ B) :
    IsPullback (pullback.fst G.hom f) ((Over.pullback f).map q).left q.left (pullback.fst B.hom f) := by
  have h₁ : IsPullback (pullback.fst G.hom f) (((Over.pullback f).map q).left ≫ pullback.snd B.hom f)
      (q.left ≫ B.hom) f := by
    have : ((Over.pullback f).map q).left ≫ pullback.snd B.hom f = pullback.snd G.hom f :=
      Over.w ((Over.pullback f).map q)
    rw [this, Over.w]
    exact IsPullback.of_hasPullback _ _
  exact h₁.of_bot (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)

theorem TQ.exists_isGrpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S)
    [GrpObj G] (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F →
    ∀ (Q : TQ G X) (Q' : TQ G' X), TorusCompat f F Q'.i Q.i →
    ∃ β : Q'.B.left ⟶ Q.B.left, Q'.q.left ≫ β = F ≫ Q.q.left ∧ IsGrpPullback Q'.B Q.B f β := by
  intro S S' f X _ G _ G' _ F hF Q Q' hT
  obtain ⟨e, he, heF⟩ := grpPullback_iso hF (isGrpPullback_pullback G f)
  have := Q.q_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have := Q'.q_affine
  have sq := isPullback_pullback_map_left f Q.q
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hi : Q'.i ≫ e.hom = (SplitTorus.bcIso f X).hom ≫ (Over.pullback f).map Q.i := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have a := (isPullback_pullback_map_left f Q.i).w
    have b := SplitTorus.bcIso_hom_fst f X
    exact ((Category.assoc _ _ _).trans ((congrArg (Q'.i.left ≫ ·) heF).trans (torusCompat_iff.1 hT).symm)).trans
      ((congrArg (· ≫ Q.i.left) b.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) a).trans (Category.assoc _ _ _).symm)))
  have hk : IsPullback Q'.i (toUnit _) (e.hom ≫ (Over.pullback f).map Q.q) (η[(Over.pullback f).obj Q.B]) := by
    refine (isPullback_kernel_baseChange f Q.isKernel).of_iso (SplitTorus.bcIso f X).symm e.symm (Iso.refl _)
      (Iso.refl _) ?_ (toUnit_unique _ _) (by simp) (by simp)
    rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hi, Iso.inv_hom_id_assoc]
  have h₁ : Flat ((Over.pullback f).map Q.q).left := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
  have h₂ : Surjective ((Over.pullback f).map Q.q).left :=
    MorphismProperty.of_isPullback (P := @Surjective) sq inferInstance
  have h₃ : QuasiCompact ((Over.pullback f).map Q.q).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  obtain ⟨β, hβ, hq⟩ := flatQuotient_iso_of_same_kernel S' G' ((Over.pullback f).obj Q.B) Q'.B _ _
    (e.hom ≫ (Over.pullback f).map Q.q) Q'.i Q'.q Q'.i inferInstance Q'.i_hom
    (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
    (by rw [Over.comp_left]; infer_instance) hk Q'.q_hom Q'.i_hom Q'.q_flat Q'.q_surj inferInstance Q'.isKernel
    hk.w Q'.isKernel.w
  refine ⟨β.hom.left ≫ pullback.fst Q.B.hom f, ?_,
    ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback Q.B f)).congr (Category.id_comp f) rfl⟩
  rw [← Category.assoc, ← Over.comp_left, hq, Over.comp_left, Category.assoc, ← heF, Category.assoc]
  exact congrArg (_ ≫ ·) sq.w.symm

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LbIsoPwPullPowLocal
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem lbIso_pw_pull_of_hasGen {X : Scheme.{0}} {L : LB X} (F : X ⟶ X) (t : ℤ)
    (h : MulPull.HasGen L (K := Fin 2) ![F, 𝟙 X] ![1, -t]) : LBIso (pw L t) (L.pull F) := by
  obtain ⟨a, ha⟩ := h
  have mem : ∀ (x : X) (j k : L.ι), F x ∈ L.U j → x ∈ L.U k → x ∈ LB.wchart L ![F, 𝟙 X] ![j, k] :=
    fun x j k hj hk => Set.mem_iInter.2 fun i => by
      fin_cases i
      · exact hj
      · exact hk
  have le : ∀ p : (L.pull F).ι × L.ι,
      (L.pull F).U p.1 ⊓ L.U p.2 ≤ LB.wchart L ![F, 𝟙 X] ![p.1 PUnit.unit, p.2] :=
    fun p x hx => mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso (pw L t) (L.pull F) := ⟨fun p => res (le p) (a.s _)⟩
  refine ⟨w, (isGen_iff w).2 fun Y r y j j' k k' hj hj' hk hk' => ?_⟩
  have e : ∀ j k, F (r y) ∈ L.U j → r y ∈ L.U k →
      gw w r y j k = gm r y (LB.wchart L ![F, 𝟙 X] ![j, k]) (a.s ![j, k]) := fun j k hj hk =>
    gm_res r y (le (fun _ => j, k)) ⟨mem_pull.2 hj, hk⟩ _
  rw [e j k hj hk, e j' k' hj' hk', gen_trans ha r y (mem _ _ _ hj hk) (mem _ _ _ hj' hk'), trF, Fin.prod_univ_two]
  congr 1
  show gm (r ≫ F) y _ (L.g j j') ^ (1 : ℤ) * gm (r ≫ 𝟙 X) y _ (L.g k k') ^ (-t) =
    gm (r ≫ F) y _ (L.g j j') * (gm r y (L.U k ⊓ L.U k') (L.g k k' ^ t))⁻¹
  rw [zpow_one, Category.comp_id, map_zpow, zpow_neg]

theorem CP.lbIso_pw_pull_pow {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ) :
    LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) := by
  have hL := M.L.isLB
  have hcube : MulPull.HasGen M.L.L (thφ B (x3 B)) thε := ⟨M.c.t, M.c.isGen⟩
  have hrig : MulPull.HasGen M.L.L (K := PUnit) (fun _ => eSec B) (fun _ => 1) := ⟨M.L.rig, M.L.rigGen⟩
  have hsym : MulPull.HasGen M.L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1] := ⟨M.sym, M.sym_gen⟩
  have h := MulPull.hasGen_pow hL hcube (𝟙 B) ((hrig.pull B.hom).of_formEq hL (fun U _ h => by
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one, one_left]
      rfl))
    (hsym.inv.of_formEq hL (fun U _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
      rfl)) n
  refine lbIso_pw_pull_of_hasGen _ _ (h.inv.of_formEq hL fun U _ h => ?_)
  rw [Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
  rfl

theorem lbIso_pw_pull_pow_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ), LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) :=
  fun _ _ _ _ _ _ M n => M.lbIso_pw_pull_pow n

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaBaseChange

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

theorem exists_fraction_map {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) :
    ∃ g : Spec (CommRingCat.of (FractionRing R')) ⟶ Spec (CommRingCat.of (FractionRing R)),
      g ≫ jK R = jK R' ≫ specOf φ ∧ jFK (R := R') F ≫ g = jFK (R := R) F := by
  have inj : Function.Injective ((algebraMap R' (FractionRing R')).comp φ) :=
    (injective_iff_map_eq_zero _).2 fun r hr => by
      have e := hF r
      rw [show algebraMap R' (FractionRing R') (φ r) = 0 from hr, map_zero] at e
      exact (IsFractionRing.injective R (FractionRing R))
        (((algebraMap (FractionRing R) F).injective (e.trans (map_zero _).symm)).trans (map_zero _).symm)
  obtain ⟨ψ, h₁⟩ : ∃ ψ : FractionRing R →+* FractionRing R',
      ψ.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp φ :=
    ⟨IsFractionRing.lift (K := FractionRing R) inj, RingHom.ext fun r => by
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
  have h₂ : (algebraMap (FractionRing R') F).comp ψ = algebraMap (FractionRing R) F :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r =>
      (congrArg (algebraMap (FractionRing R') F) (RingHom.congr_fun h₁ r)).trans (hF r).symm)
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · exact (Spec.map_comp _ _).symm.trans ((congrArg (fun q => Spec.map (CommRingCat.ofHom q)) h₁).trans
      (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R' (FractionRing R')))))
  · exact (Spec.map_comp _ _).symm.trans (congrArg (fun q => Spec.map (CommRingCat.ofHom q)) h₂)

theorem grp_generic {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) :
    IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) := by
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl

end GlobalTheory.ThetaBaseChange

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaBaseChange in
set_option maxHeartbeats 1600000 in

theorem qkToAk_baseChange : GlobalFnsSt → SecBaseChangeSt → QkBaseChangeSt := by
  intro hG _ R R' _ _ _ _ I I' _ _ φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU F _ _ _ hF k hk p x p' x' hy hg hx H w' hw'
  obtain ⟨wL, hwL, -, -, hlev⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨hx1, H⟩ := H w hw
  obtain ⟨g, hg₁, hg₂⟩ := exists_fraction_map φ F hF
  have gA := grp_generic U.toUnifPre
  have gΨ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have hΘF : (jFK (R := R') F ≫ jK R') ≫ specOf φ = jFK (R := R) F ≫ jK R := by
    rw [Category.assoc, ← hg₁, ← Category.assoc, hg₂]
  obtain ⟨Θ, hΘ₁, hΘ₂⟩ := exists_cmp hΘF (pull_grp hD).1.w
  have gA' := (grp_generic U'.toUnifPre).comp gΨ
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ : ∃ Φ : A'.A.left ⟶ A.A.left, Φ ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧
      Φ ≫ A.A.hom = A'.A.hom ≫ g :=
    ⟨gA.1.lift _ (A'.A.hom ≫ g) (by rw [gA'.1.w, Category.assoc, hg₁]), gA.1.lift_fst _ _ _, gA.1.lift_snd _ _ _⟩
  have gΦ : IsGrpPullback A'.A A.A g Φ := gA.cancel (gA'.congr hg₁.symm hΦ₁.symm) hΦ₂
  have hxΦ : x'.left ≫ Φ = x.left := gA.1.hom_ext (by
    rw [Category.assoc, hΦ₁, ← hx]; simp only [Category.assoc]) (by
    rw [Category.assoc, hΦ₂, ← Category.assoc, Over.w x', Over.w x]; exact hg₂)
  refine ⟨pow_eq_one_of_push hg₂ gΦ hxΦ hx1, fun θ' hθ' => ?_⟩
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have n₂ : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  have n₃ : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.hom_inv_id, Over.id_left]
  have hΦ₃ : (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) := by
    rw [Category.assoc, hΦ₁, ← Category.assoc, ← Category.assoc U'.gen.hom.left, n₃]
    exact congrArg (· ≫ _) (Category.id_comp _)
  obtain ⟨v₂, hv₂, hsq⟩ := exists_side A.isLB A'.isLB U.LG.isLB U'.LG.isLB hw _ n₁ hw' hwL _ hΦ₃
  obtain ⟨v, hv, hvv⟩ := exists_unpull hv₂ _ n₂ (P := Φ) (by rw [← Category.assoc, n₂, Category.id_comp])
  obtain ⟨Ω, hΩ₁, hΩ₂⟩ := exists_cmp hg₂ hΦ₂
  obtain ⟨ω, hω₁, hω₂⟩ := exists_cmp_inv hg₂ gΦ.1
  have hΩω : Ω ≫ ω = 𝟙 _ := cmp_ext gΦ.1 (by rw [Category.assoc, hω₁, hΩ₁, Category.id_comp])
    (by rw [Category.assoc, hω₂, hΩ₂, Category.id_comp])
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n.left ≫ (U.toUnifPre.genF F).left = 𝟙 _ := congrArg (fun q => q.left) (show n ≫ U.toUnifPre.genF F = 𝟙 _ by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n])
  have hn₁ : n.left ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : n ≫ fst _ _ = _)
  have hn₂ : n.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : n ≫ snd _ _ = _)
  have hh₁ : (U'.toUnifPre.genF F).left ≫ (fst (TFK (R := R') F) A'.A).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : U'.toUnifPre.genF F ≫ fst _ _ = _)
  have hh₂ : (U'.toUnifPre.genF F).left ≫ (snd (TFK (R := R') F) A'.A).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ U'.gen.hom.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : U'.toUnifPre.genF F ≫ snd _ _ = _)
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : (UnifPre.GF (G := G') F).left ⟶ (UnifPre.GF (G := G) F).left,
      Ξ = (U'.toUnifPre.genF F).left ≫ Ω ≫ n.left := ⟨_, rfl⟩
  have x₁ : (Ξ ≫ (U.toUnifPre.genF F).left) ≫ ω = (U'.toUnifPre.genF F).left := by
    rw [hΞ, Category.assoc _ (Ω ≫ n.left), Category.assoc Ω, hn, Category.comp_id, Category.assoc, hΩω,
      Category.comp_id]
  have x₂ : Ξ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₂, ← Category.assoc Ω]
    refine (congrArg (fun a => _ ≫ a ≫ _) hΩ₂).trans ?_
    rw [← Category.assoc, ← Category.assoc, hh₂]
    simp only [Category.assoc]
  have hΞ₁ : Ξ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₁]
    exact (congrArg (_ ≫ ·) hΩ₁).trans hh₁
  have hΞ₂ : Ξ ≫ UnifPre.gFK (G := G) F = UnifPre.gFK (G := G') F ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) x₂).trans ?_)
    refine Eq.trans ?_ ((congrArg (_ ≫ ·) hΦ₃).trans (Category.assoc _ _ _).symm)
    simp only [Category.assoc]
  obtain ⟨θ, hθ, hact⟩ := exists_theta_moved A.isLB A'.isLB hg₂ gΦ hv hω₁ hω₂ θ' (x := x) (by rw [hθ']; exact hxΦ)
  obtain ⟨ν, hν, Hν⟩ := H θ hθ
  obtain ⟨ν', hν', Hν'⟩ := GlobalTheory.phiRel_transport hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k p p' hy hg ν hν
  refine ⟨ν', hν', fun t' t₂' s' s₂' E E₂ hA => ?_⟩
  have bij := (expandsF_bijective U.toUnifPre F hG hk (U.expand k hk) hw).1
  have bij' := (expandsF_bijective U'.toUnifPre F hG hk (U'.expand k hk) hw').1
  choose pl hpl using exists_fam_field_pull hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k
  have key : ∀ a' b', U'.toUnifPre.ExpandsF F k w' a' b' → ∃ a b, Moved v ω a' a ∧
      U.toUnifPre.ExpandsF F k w a b ∧ pl b = b' := fun a' b' E => by
    obtain ⟨a, ha⟩ := exists_moved A.isLB A'.isLB hω₂ n₂ hv₂ hvv a'
    obtain ⟨b, σ, h₁, h₂⟩ := (bij a).exists
    refine ⟨a, b, ha, ⟨σ, h₁, h₂⟩, (bij' a').unique ?_ E⟩
    obtain ⟨σ', h₁', -⟩ := E
    exact ⟨σ', h₁', expandsG_transport R R' I I' φ D D' hD A A' G G' bc hbc U.toUnifPre U'.toUnifPre wL hwL hlev F hF
      Θ hΘ₁ hΘ₂ Ξ hΞ₁ hΞ₂ k σ σ' b (pl b)
      (moved_sec A.isLB A'.isLB n₃ n₁ hΦ₃ hsq hvv x₁ x₂ ha h₁ h₁') (hpl b) h₂⟩
  obtain ⟨t, s, m, e, rfl⟩ := key t' s' E
  obtain ⟨t₂, s₂, m₂, e₂, rfl⟩ := key t₂' s₂' E₂
  exact Hν' s s₂ _ _ (hpl s) (hpl s₂) (Hν t t₂ s s₂ e e₂ (hact t' t₂' t t₂ m m₂ hA))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepComb
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange

namespace GlobalTheory

theorem sval_eq_zero_of_indep_comb :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (X Y Y' : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of R)) [Flat π] (π' : Y' ⟶ Spec (CommRingCat.of R')) (p : Y' ⟶ Y), IsPullback p π' π (Spec.map (CommRingCat.ofHom f)) → ∀ (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (M : Type) [Fintype M] (β : M → R'), (∀ c : M → R, ∑ m, f (c m) * β m = 0 → ∀ m, c m = 0) → ∀ d : M → LB.Sec (LB.LinComb L φ ε), (∀ (y : Y') (J), Good L y J → ∑ m, constVal π' y (β m) * sval (d m) p y J = 0) → ∀ (m : M) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval (d m) r z J = 0 := by
  intro R R' _ _ f X Y Y' π _ π' p H L hL K _ φ ε M _ β hβ d hd m Z r z J hJ
  let e := (Fintype.equivFin M).symm
  have key := ThetaSpecialise.sec_indep H ε (φ := φ) (φ' := fun k => p ≫ φ k) (fun _ => rfl) (fun i => β (e i))
    (fun a ha i => by
      have := hβ (fun m => a (e.symm m)) (by
        rw [← ha, ← e.sum_comp]
        simp only [Equiv.symm_apply_apply]) (e i)
      simpa only [Equiv.symm_apply_apply] using this)
    (fun i => d (e i)) (sec_ext' hL fun y J hJ => by
      rw [sval_sum' hJ, sval_zero' hJ, ← hd y J hJ, ← e.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sval_smul' hJ]
      exact congrArg₂ (· * ·) (by rw [Category.id_comp])
        ((sval_pullOver H.w _ _ _ hJ).trans (by rw [Category.id_comp]))) (e.symm m)
  rw [Equiv.apply_symm_apply] at key
  exact (congrArg (fun s => sval s r z J) key).trans (sval_zero' (π := π) hJ r)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPairEqOfThetaOperatorRel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace OperatorPoint

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem trPt_inv_comp (b : TF (R := R) F ⟶ D.P.A) : DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
  · have e : (DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b) ≫ DegPre.prB D F = DegPre.prB D F := by
      rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc,
        ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one]
    exact e.trans (Category.id_comp _).symm

theorem phiVal_inv {n : ℕ} (p : QkPt D F n)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)))
    {s t : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε n))} (h : PhiVal p w s t)
    (α β : D.X) (hβ : α + p.y = β) (b : TF (R := R) F ⟶ D.P.A) (hb : p.g.b = b) (y : (DegPre.BF D F).left) (J)
    (hJ : Good D.P.L y J) :
    sval (t β) (DegPre.trPt D F b⁻¹).left y J = sval (s α) (𝟙 _) y J *
      (uVal D F n α b (DegPre.trPt D F b⁻¹) y J * (val (p.g.s α) (fst (TF (R := R) F) D.P.A).left y J *
        val w (fst (TF (R := R) F) D.P.A).left y J)).val := by
  subst hb
  have e := h α β hβ _ (DegPre.trPt D F p.g.b⁻¹) y J hJ
  rw [trPt_inv_comp, tr_fst, val_mul hJ] at e
  exact e

end OperatorPoint

open ReciprocityTheory.ChartRestriction.G.DVR OperatorPoint in

theorem qkPt_g_eq_of_phiRel :
    GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → p'.y = p.y → p.g.b = p'.g.b → p.g = p'.g := by
  intro hG hT R _ _ D hB F _ _ n hn p p' w w' hw hw' H hy hb
  have hI := (degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk R D F).1
  have key : ∀ (α : D.X) (y : (DegPre.BF D F).left) (J), Good D.P.L y J →
      val (p.g.s α) (fst (TF (R := R) F) D.P.A).left y J * val w (fst (TF (R := R) F) D.P.A).left y J =
        val (p'.g.s α) (fst (TF (R := R) F) D.P.A).left y J * val w' (fst (TF (R := R) F) D.P.A).left y J := by
    intro α y J hJ
    obtain ⟨σ, hσ⟩ := FamFree.exists_sec_ne_zero (D := D) (F := F) hT hn α
    obtain ⟨s, rfl, -⟩ := FamFree.exists_fam_single hG hB hn α σ
    obtain ⟨t, h₁, h₂⟩ := H s
    have e₁ := phiVal_inv p w ((phiRel_iff hG p w hw s t).1 h₁) α (α + p.y) rfl _ rfl y J hJ
    have e₂ := phiVal_inv p' w' ((phiRel_iff hG p' w' hw' s t).1 h₂) α (α + p.y) (by rw [hy]) _ hb.symm y J hJ
    have hne : sval (s.s α) (𝟙 _) y J ≠ 0 :=
      RootUnit.sec_gs_ne_zero (s.s α) (not_forall.1 hσ) y _ (hJ.mem _ (𝟙 _))
    exact mul_left_cancel (Units.ext (mul_left_cancel₀ hne (e₁.symm.trans e₂)))
  have key' : ∀ (α : D.X) (y : (DegPre.BF D F).left) (J), Good D.P.L y J →
      val (p.g.s α) (fst (TF (R := R) F) D.P.A).left y J = val (p'.g.s α) (fst (TF (R := R) F) D.P.A).left y J := by
    intro α y J hJ
    have e₀ := key 0 y J hJ
    rw [val_corr hJ p.g.s_zero, val_corr hJ p'.g.s_zero, val_one, _root_.one_mul, _root_.one_mul] at e₀
    have e := key α y J hJ
    rw [e₀] at e
    exact mul_right_cancel e
  refine TorusExt.gt_ext hb fun χ => corr_of_val D.P.isLB fun y J hJ => ?_
  have hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (p.g.s χ) (fst (TF (R := R) F) D.P.A).left)
      (LB.pullGen D.P.L _ _ (p'.g.s χ) (fst (TF (R := R) F) D.P.A).left) :=
    corr_of_val D.P.isLB fun y J hJ => by
      rw [val_pull hJ, val_pull hJ, Category.id_comp]; exact key' χ y J hJ
  have z₁ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (show DegPre.zF D F ≫ fst _ _ = 𝟙 _ from lift_fst _ _)
  have e := val_corr hJ hc (DegPre.zF D F).left
  rwa [val_pull hJ, val_pull hJ, z₁] at e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableOfSurjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem torus_stable_of_surjective {S S' : Scheme.{0}} (f : S' ⟶ S) [Surjective f]
    (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] (G₀ : Over S') [GrpObj G₀]
    (F : G₀.left ⟶ G.left) (hF : IsGrpPullback G₀ G f F)
    (i₀ : splitTorus _ X ⟶ G₀) (i : splitTorus _ X ⟶ G) (hi : TorusCompat f F i₀ i)
    (W : G.left.Opens)
    (hW : (snd (splitTorus _ X) G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) ≤
      ((fst (splitTorus _ X) G₀ ≫ i₀) * snd _ G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W)) :
    (snd (splitTorus _ X) G).left ⁻¹ᵁ W ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ W := by
  rw [torusCompat_iff] at hi
  let P : Over S := splitTorus S X ⊗ G
  let p : pullback P.hom f ⟶ P.left := pullback.fst P.hom f
  let Z₀ : Over S' := Over.mk (pullback.snd P.hom f)
  have hT := SplitTorus.isPullback_bcMap f X
  have w₁ : (p ≫ (fst (splitTorus S X) G).left) ≫ (splitTorus S X).hom = pullback.snd P.hom f ≫ f := by
    rw [Category.assoc, Over.w]; exact pullback.condition
  have w₂ : (p ≫ (snd (splitTorus S X) G).left) ≫ G.hom = pullback.snd P.hom f ≫ f := by
    rw [Category.assoc, Over.w]; exact pullback.condition
  let t₀ : Z₀ ⟶ splitTorus S' X := Over.homMk (hT.lift _ _ w₁) (hT.lift_snd _ _ w₁)
  let g₀ : Z₀ ⟶ G₀ := Over.homMk (hF.1.lift _ _ w₂) (hF.1.lift_snd _ _ w₂)
  have ht₀ : t₀.left ≫ SplitTorus.bcMap f X = p ≫ (fst (splitTorus S X) G).left := hT.lift_fst _ _ w₁
  have hg₀ : g₀.left ≫ F = p ≫ (snd (splitTorus S X) G).left := hF.1.lift_fst _ _ w₂
  let ρ : Over.mk (Z₀.hom ≫ f) ⟶ P := Over.homMk p pullback.condition
  have h1 : (ρ ≫ fst (splitTorus S X) G ≫ i).left = (t₀ ≫ i₀).left ≫ F := by
    change _ = (t₀.left ≫ i₀.left) ≫ F
    rw [Category.assoc, ← hi, ← Category.assoc t₀.left, ht₀, Category.assoc]; rfl
  have h2 : (ρ ≫ snd (splitTorus S X) G).left = g₀.left ≫ F := hg₀.symm
  have h3 := hF.2 Z₀ (t₀ ≫ i₀) g₀ _ _ h1 h2
  let l : Z₀ ⟶ splitTorus S' X ⊗ G₀ := lift t₀ g₀
  have h4 : p ≫ ((fst (splitTorus S X) G ≫ i) * snd _ G).left =
      l.left ≫ ((fst (splitTorus S' X) G₀ ≫ i₀) * snd _ G₀).left ≫ F := by
    have e : l ≫ ((fst (splitTorus S' X) G₀ ≫ i₀) * snd _ G₀) = (t₀ ≫ i₀) * g₀ := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    rw [← Category.assoc, ← Over.comp_left, e, ← h3, ← MonObj.comp_mul]; rfl
  have h5 : p ≫ (snd (splitTorus S X) G).left = l.left ≫ (snd (splitTorus S' X) G₀).left ≫ F := by
    rw [← Category.assoc, ← Over.comp_left, lift_snd, hg₀]
  have h6 : (p ≫ (snd (splitTorus S X) G).left) ⁻¹ᵁ W ≤
      (p ≫ ((fst (splitTorus S X) G ≫ i) * snd _ G).left) ⁻¹ᵁ W := by
    rw [h4, h5]
    exact fun z hz => hW hz
  intro x hx
  obtain ⟨z, rfl⟩ := p.surjective x
  exact h6 hx

theorem torus_stable_of_red : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F → ∀ (i₀ : splitTorus _ X ⟶ G₀) (i : splitTorus _ X ⟶ G), TorusCompat (red J) F i₀ i → ∀ W : G.left.Opens, (snd (splitTorus _ X) G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) ≤ ((fst (splitTorus _ X) G₀ ≫ i₀) * snd _ G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) → (snd (splitTorus _ X) G).left ⁻¹ᵁ W ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ W := by
  intro A _ J hJ X _ G _ G₀ _ F hF i₀ i hi W hW
  haveI := surjective_red hJ
  exact torus_stable_of_surjective (red J) X G G₀ F hF i₀ i hi W hW

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorusStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.weilQk_pairing_existsUnique_torus : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, (∃! ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ) ∧ ∀ t, p.y = 0 → IsTor t p.g → WeilQkIs D.toPre F k p p' (t (Multiplicative.ofAdd p'.y)).val := by
  first | exact @GlobalTheory.weilQk_existsUnique | exact GlobalTheory.weilQk_existsUnique | (intros; apply GlobalTheory.weilQk_existsUnique <;> assumption)
end

