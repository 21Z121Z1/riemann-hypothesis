import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitLevels
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.RedTotal

section Units

variable {S : Type} [CommRing S] (J : Ideal S)

theorem appTop_specMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom a) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a) :=
  congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem ΓSpecIso_injective (A : Type) [CommRing A] :
    Function.Injective (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective

theorem fn_ext_levels [IsHausdorff J S] {a b : Γ(Spec (CommRingCat.of S), ⊤)}
    (h : ∀ e, (adicLevelι J (e + 1)).appTop.hom a = (adicLevelι J (e + 1)).appTop.hom b) : a = b := by
  apply ΓSpecIso_injective
  have := IsHausdorff.StrictMono.funext' J (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom b) fun n _ =>
      (appTop_specMap _ a).symm.trans ((congrArg _ (h n)).trans (appTop_specMap _ b))
  exact congrFun this ()

theorem exists_fn_levels [IsAdicComplete J S] (ρ : ∀ e : ℕ, Γ(Spec (CommRingCat.of (S ⧸ J ^ (e + 1))), ⊤))
    (h : ∀ e, (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom (ρ (e + 1)) = ρ e) :
    ∃ a : Γ(Spec (CommRingCat.of S), ⊤), ∀ e, (adicLevelι J (e + 1)).appTop.hom a = ρ e := by
  have ha : StrictMono fun n : ℕ => n + 1 := strictMono_id.add_const 1
  let f : ∀ n : ℕ, Polynomial ℤ →+* S ⧸ J ^ (n + 1) := fun n =>
    Polynomial.eval₂RingHom (Int.castRingHom _) ((Scheme.ΓSpecIso (CommRingCat.of _)).hom.hom (ρ n))
  have hf : ∀ n, f n Polynomial.X = (Scheme.ΓSpecIso (CommRingCat.of _)).hom.hom (ρ n) := fun n =>
    Polynomial.eval₂_X _ _
  have hc : ∀ {m : ℕ}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp (f (m + 1)) = f m := by
    intro m
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, hf, hf, ← h m]
    exact (appTop_specMap _ _).symm
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    (IsAdicComplete.StrictMono.liftRingHom J ha f hc Polynomial.X), fun e => ΓSpecIso_injective _ ?_⟩
  rw [appTop_specMap, Iso.inv_hom_id_apply, ← hf]
  exact congrArg (fun q => q Polynomial.X) (IsAdicComplete.StrictMono.mk_comp_liftRingHom J ha f hc (n := e))

theorem exists_unit_levels [IsAdicComplete J S] (ρ : ∀ e : ℕ, Γ(Spec (CommRingCat.of (S ⧸ J ^ (e + 1))), ⊤)ˣ)
    (h : ∀ e, (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom (ρ (e + 1)).val = (ρ e).val) :
    ∃ a : Γ(Spec (CommRingCat.of S), ⊤)ˣ, ∀ e, pullU (adicLevelι J (e + 1)) ⊤ a = ρ e := by
  obtain ⟨a, ha⟩ := exists_fn_levels J (fun e => (ρ e).val) h
  obtain ⟨b, hb⟩ := exists_fn_levels J (fun e => ((ρ e)⁻¹).val) fun e => by
    have : Units.map (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom.toMonoidHom (ρ (e + 1)) = ρ e :=
      Units.ext (h e)
    rw [← this]; rfl
  have hab : a * b = 1 := fn_ext_levels J fun e => by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, fun e => Units.ext (ha e)⟩

end Units

section Gens

variable {S : Type} [CommRing S] (J : Ideal S) {X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_of_levels [IsHausdorff J S] (hL : L.IsLB) {φ : K → (Spec (CommRingCat.of S) ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Spec (CommRingCat.of S) ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) {u' : LB.Gen (LB.LinComb L φ' ε')} (hu' : u'.IsGen)
    (hv : ∀ e z C, Good L z C → val u (adicLevelι J (e + 1)) z C = val u' (adicLevelι J (e + 1)) z C) :
    LB.Gen.Corr L φ ε φ' ε' u u' := by
  obtain ⟨a, ha⟩ := TorusCoord.exists_ratio hL h u hu u' hu'
  have h2 : a = 1 := Units.ext (fn_ext_levels J fun e =>
    (FormalPoint.appTop_eq_one_of_gm _ a fun z => by
      obtain ⟨C, hC⟩ := exists_good_pt hL z
      exact mul_eq_right.1 ((ha _ _ z C hC).symm.trans (hv e z C hC))).trans (map_one _).symm)
  exact corr_of_val hL fun y C hC => by rw [ha _ _ y C hC, h2, map_one, _root_.one_mul]

theorem exists_gen_levels [IsLocalRing S] [IsAdicComplete J S] (hL : L.IsLB)
    (φ : K → (Spec (CommRingCat.of S) ⟶ X)) (ε : K → ℤ) {Y : ℕ → Scheme.{0}} {ψ : ∀ e, K' → (Y e ⟶ X)}
    {ε' : K' → ℤ} (u : ∀ e, LB.Gen (LB.LinComb L (ψ e) ε')) (hu : ∀ e, (u e).IsGen)
    (y : ∀ e : ℕ, Spec (CommRingCat.of (S ⧸ J ^ (e + 1))) ⟶ Y e)
    (h : ∀ e, FormEq (fun k => adicLevelι J (e + 1) ≫ φ k) ε (fun k => y e ≫ ψ e k) ε')
    (hc : ∀ e z C, Good L z C →
      val (u (e + 1)) (adicLevelMap J (Nat.le_succ (e + 1)) ≫ y (e + 1)) z C = val (u e) (y e) z C) :
    ∃ s : LB.Gen (LB.LinComb L φ ε), s.IsGen ∧ ∀ e (Z : Scheme.{0}) (k : Z ⟶ _) z C, Good L z C →
      val (u e) (k ≫ y e) z C = val s (k ≫ adicLevelι J (e + 1)) z C := by
  obtain ⟨s₀, hs₀⟩ := DVR.exists_gen_of_local L hL φ ε
  choose ρ hρ using fun e => TorusCoord.exists_ratio hL (fun U _ f => (h e U f).symm)
    (LB.pullGen L _ _ (u e) (y e)) (DVR.pullGen_isGen _ _ _ _ (hu e) _)
    (LB.pullGen L _ _ s₀ (adicLevelι J (e + 1))) (DVR.pullGen_isGen _ _ _ _ hs₀ _)
  have hρ' : ∀ e (Z : Scheme.{0}) (k : Z ⟶ _) z C, Good L z C →
      val (u e) (k ≫ y e) z C = gm k z ⊤ (ρ e) * val s₀ (k ≫ adicLevelι J (e + 1)) z C := fun e Z k z C hC =>
    (val_pull hC _ _ _).symm.trans ((hρ e Z k z C hC).trans (congrArg₂ (· * ·) rfl (val_pull hC _ _ _)))
  obtain ⟨a, ha⟩ := exists_unit_levels J ρ fun e => by
    refine (FormalPoint.appTop_eq_of_gm _ (𝟙 _) (ρ (e + 1)) (ρ e) fun z => ?_).trans (by simp)
    obtain ⟨C, hC⟩ := exists_good_pt hL z
    have e₁ := hρ' (e + 1) _ (adicLevelMap J (Nat.le_succ (e + 1))) z C hC
    have e₂ := hρ' e _ (𝟙 _) z C hC
    rw [Category.id_comp, Category.id_comp] at e₂
    rw [hc e z C hC, adicLevelMap_ι, e₂] at e₁
    exact (mul_right_cancel e₁).symm
  refine ⟨scaleGen a s₀, scaleGen_isGen a hs₀, fun e Z k z C hC => ?_⟩
  rw [val_scaleGen a s₀ _ hC, hρ' e Z k z C hC, ← ha e]
  exact congrArg (· * _) (gm_pull k _ z ⊤ trivial a)

end Gens

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}

theorem formEq_mult {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ χ' : D.X) :
    FormEq (Sum.elim (DegPre.gtφT D T b (χ + χ'))
        (fun k => (lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') b)).left ≫ thφ D.P.A (x3 D.P.A) k))
      (Sum.elim DegPre.gtε thε)
      (Sum.elim (DegPre.gtφT D T b χ) (DegPre.gtφT D T b χ')) (Sum.elim DegPre.gtε DegPre.gtε) := by
  intro U _ f
  have p : ∀ α, ∏ k, f (DegPre.gtφT D T b α k) ^ DegPre.gtε k =
      (f (DVR.cP D T α * b).left)⁻¹ * f (DVR.cP D T α).left * f b.left * (f (1 : T ⟶ D.P.A).left)⁻¹ := fun α => by
    have := FormalPoint.prod_gtφT (𝟙 T) b α f
    simpa only [Over.id_left, Category.id_comp] using this
  have q := prod_cub (DVR.cP D T χ) (DVR.cP D T χ') b f
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [p, p, p]
  refine (congrArg (_ * ·) q).trans ?_
  rw [DVR.cPoint_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : PreU I D A G) {S : Type} [CommRing S] {φ : R →+* S}

open FormalPoint in

theorem red_of_reduction (x : Over.mk (spMap φ) ⟶ G) (g : GtPt D (Over.mk (spMap φ)))
    (h₁ : ∀ e, reduction I x e ≫ (U.gt e).pG.left = adicLevelι (I.map φ) (e + 1) ≫ g.b.left)
    (h₂ : ∀ e χ (Z : Scheme.{0}) (k : Z ⟶ _) z C, Good D.P.L z C →
      val ((U.gt e).t χ) (k ≫ reduction I x e) z C = val (g.s χ) (k ≫ adicLevelι (I.map φ) (e + 1)) z C) :
    U.Red x g := by
  intro e Z r y hy
  have w : r ≫ (Over.mk (spMap φ)).hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
  obtain ⟨l, rfl⟩ := exists_factor_level I φ r _ w
  obtain rfl : y = l ≫ reduction I x e := by
    rw [← cancel_mono (fstG I e G).left, Category.assoc, reduction_fstG]
    exact hy.trans (Category.assoc _ _ _)
  exact ⟨(Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (h₁ e)).trans (Category.assoc _ _ _).symm),
    fun χ z C hC => h₂ e χ Z l z C hC⟩

omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
open FormalPoint in

theorem reduction_succ (x : Over.mk (spMap φ) ⟶ G) (e : ℕ) :
    adicLevelMap (I.map φ) (Nat.le_succ (e + 1)) ≫ reduction I x (e + 1) = reduction I x e ≫ thickMap R I e G := by
  have h₄ : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, h₄, reduction_fstG, reduction_fstG]
  exact adicLevelMap_ι_assoc _ _ _

variable [IsLocalRing S]

open FormalPoint in

theorem red_unique [IsHausdorff (I.map φ) S] {x : Over.mk (spMap φ) ⟶ G} {g g' : GtPt D (Over.mk (spMap φ))}
    (h : U.Red x g) (h' : U.Red x g') : g = g' := by
  have H := fun e => h e _ _ _ (reduction_fstG I x e)
  have H' := fun e => h' e _ _ _ (reduction_fstG I x e)
  obtain ⟨b, s, hs, _, _⟩ := g
  obtain ⟨b', s', hs', _, _⟩ := g'
  obtain rfl : b = b' := Over.OverMorphism.ext
    (hom_ext_of_isHausdorff (I.map φ) fun e => (H e).1.symm.trans (H' e).1)
  obtain rfl : s = s' := funext fun χ => TorusCoord.gen_eq_of_corr D.P.isLB (hs χ) (hs' χ)
    (corr_of_levels (I.map φ) D.P.isLB (fun _ _ _ => rfl) (hs χ) (hs' χ) fun e z C hC =>
      ((H e).2 χ z C hC).symm.trans ((H' e).2 χ z C hC))
  rfl

open FormalPoint in

theorem exists_red [IsAdicComplete (I.map φ) S] (x : Over.mk (spMap φ) ⟶ G) :
    ∃ g : GtPt D (Over.mk (spMap φ)), U.Red x g := by
  have hf : IsAdicFamily (I.map φ) fun e => reduction I x e ≫ (U.gt e).pG.left := fun e => by
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [reduction_succ, Category.assoc, U.gt_q]
  obtain ⟨b₀, ⟨hb₁, hb₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (spMap φ) D.P.A.hom hf fun e => by
    have h₁ : (U.gt e).pG.left ≫ D.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (U.gt e).pG
    rw [Category.assoc, h₁, ← Category.assoc, reduction_hom, levelMap_thick]
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (spMap φ)
  let b : T ⟶ D.P.A := Over.homMk b₀ hb₁
  have hb : ∀ e, adicLevelι (I.map φ) (e + 1) ≫ b.left = reduction I x e ≫ (U.gt e).pG.left := hb₂
  choose s hs vs using fun χ => exists_gen_levels (I.map φ) D.P.isLB (DegPre.gtφT D T b χ) DegPre.gtε
    (fun e => (U.gt e).t χ) (fun e => (U.gt e).t_gen χ) (reduction I x)
    (fun e => TorusCoord.formEq_of_left b (U.gt e).pG _ _ (hb e) χ) fun e z C hC => by
      rw [reduction_succ]
      exact (val_pull hC _ _ _).symm.trans (val_corr hC (U.gt_t e χ) _)
  have hm : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (s (χ + χ')) (DegPre.cubAtT D T (DegPre.cT D T χ) (DegPre.cT D T χ') b))
      (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ')) := fun χ χ' => by
    refine corr_of_levels (I.map φ) D.P.isLB (formEq_mult b χ χ')
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hs _) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hs _) (hs _)) fun e z C hC => ?_
    have v : ∀ α, val ((U.gt e).t α) (reduction I x e) z C = val (s α) (adicLevelι (I.map φ) (e + 1)) z C :=
      fun α => by simpa only [Category.id_comp] using vs α e _ (𝟙 _) z C hC
    have m := TorusCoord.val_t_mul (U.gt e) (reduction I x e) χ χ' z C hC
    rw [v, v, v, ← (TorusCoord.comp_eq_of_left b (U.gt e).pG _ _ (hb e)).2 χ χ'] at m
    exact (val_mul hC _ _ _).trans ((congrArg₂ (· * ·) rfl (val_pull hC _ _ _)).trans
      (m.trans (val_mul hC _ _ _).symm))
  refine ⟨⟨b, s, hs, corr_of_val D.P.isLB fun y C hC => ?_, hm⟩,
    red_of_reduction U x _ (fun e => (hb e).symm) fun e χ => vs χ e⟩
  have h := ((val_mul hC _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hC _ _ _))).symm.trans
    ((val_corr hC (hm 0 0) (𝟙 _)).trans (val_mul hC _ _ _))
  have c0 : DegPre.cT D T 0 = 1 := cPoint_zero T
  have c1 : TorusCoord.cubVal (𝟙 _ ≫ (lift (DegPre.cT D T 0) (lift (DegPre.cT D T 0) b)).left) y C = 1 := by
    rw [c0, Category.id_comp]
    exact (isCub_cubV D.cub hC).face 1 b
  have h' := (congrArg (_ * ·) c1).symm.trans h
  rw [add_zero, _root_.mul_one] at h'
  exact (mul_eq_left.1 h'.symm).trans (val_one _).symm

theorem existsUnique_red [IsAdicComplete (I.map φ) S] (x : Over.mk (spMap φ) ⟶ G) :
    ∃! g : GtPt D (Over.mk (spMap φ)), U.Red x g :=
  existsUnique_of_exists_of_unique (exists_red U x) fun _ _ h h' => red_unique U h h'

end Main

theorem main : AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W],
    FinExt V W → ∀ x : TA V W ⟶ G, ∃! g : GtPt D (TA V W), U.Red x g := by
  intro V _ _ _ _ D A G _ _ U W _ _ _ hW x
  have := hW.2.2.2.2
  exact existsUnique_red U (φ := algebraMap V W) x

end GlobalTheory.RedTotal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFLinear
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLin

theorem sval_comb {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t t' t'' : LB.Sec (LB.LinComb L φ ε)} (a : Γ(Y, ⊤))
    (h : ∀ j, t''.f j = (Y.presheaf.map (homOfLE le_top).op).hom a * t.f j + t'.f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval t'' r z J = gs r z ⊤ a * sval t r z J + sval t' r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ?_
  refine (gs_add _ _ _ hm _ _).trans (congrArg (· + _) ((gs_mul _ _ _ hm _ _).trans (congrArg (· * _) ?_)))
  exact gs_res r z le_top hm a

theorem gs_scal_mul {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (a b : R) : gs r z ⊤ (scal p (a * b)) = gs r z ⊤ (scal p a) * gs r z ⊤ (scal p b) := by
  rw [← gs_mul r z ⊤ trivial]
  simp only [scal, map_mul]

theorem sum_append {α β M : Type*} [AddCommMonoid M] {n m : ℕ} (g : α → β → M) (c : Fin n → α) (c' : Fin m → α)
    (s : Fin n → β) (s' : Fin m → β) :
    ∑ i, g (Fin.append c c' i) (Fin.append s s' i) = ∑ i, g (c i) (s i) + ∑ i, g (c' i) (s' i) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem expF_linear : (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' t'' s s' s'' (c : F), U.ExpF F k t s → U.ExpF F k t' s' → (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) → (∀ α j, (s'' α).f j = DegPre.constBF D F c _ * (s α).f j + (s' α).f j) → U.ExpF F k t'' s'') := by
  intro V _ _ _ _ D A G _ _ U F _ _ k t t' t'' s s' s'' c ⟨n, a, σ, f, h1, h2, h3⟩ ⟨m, a', σ', f', h1', h2', h3'⟩ ht hs
  refine ⟨n + m, Fin.append (fun i => c * a i) a', Fin.append σ σ', Fin.append f f', fun i => ?_,
    fun Z rA y rG e1 e2 z JA JG hA hG => ?_, fun α Z rF rB e z J hJ => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact h1 i
    · simp only [Fin.append_right]; exact h1' i
  · rw [sum_append (fun x y => gs rA z ⊤ (scal (fst (TFK (R := V) F) A.A).left x) * sval y rG z JG),
      ← h2' Z rA y rG e1 e2 z JA JG hA hG]
    simp only [gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h2 Z rA y rG e1 e2 z JA JG hA hG,
      sval_comb (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left) (ε := fun _ => (k : ℤ))
        (scal (fst (TFK (R := V) F) A.A).left c) ht rA z hA]
    ring
  · rw [sum_append (fun x (y : ∀ α, SecBT D (𝟙_ _) k α) =>
      gs rF z ⊤ (scal (fst (TF (R := V) F) D.P.A).left x) * sval (y α) rB z J), ← h3' α Z rF rB e z J hJ]
    simp only [gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h3 α Z rF rB e z J hJ]
    exact sval_comb (scal (fst (TF (R := V) F) D.P.A).left c) (hs α) rF z hJ

end GlobalTheory.UU.ExpLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfExpT
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.IntExp

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ f) z U a = (r.stalkMap z).hom (gs f (r z) U a) := by
  rw [gs_eq f (r z) U h, gs_eq (r ≫ f) z U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _).symm

theorem sval_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) (J) (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem gs_scal_one {F : Type} [CommRing F] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : Y ⟶ Spec (CommRingCat.of F)) :
    gs r z ⊤ (scal p (1 : F)) = 1 := by
  rw [gs_eq r z ⊤ trivial]
  simp only [scal, map_one]

theorem expF_of_expT : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (t) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f → U.PullG F (toUnit _) k σ t → PullB D F (toUnit _) k f s → U.ExpF F k t s := by
  intro R _ _ I D A G _ _ U F _ _ k σ f t s hE hG hB
  refine ⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE, ?_, ?_⟩
  · intro Z rA y rG h₁ h₂ z JA JG hJA hJG
    rw [Fin.sum_univ_one]
    refine (hG Z rA y rG h₁ h₂ ?_ z JA JG hJA hJG).trans ?_
    · have e₁ : (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left = (snd (𝟙_ _) G).left ≫ G.hom := by
        have a := Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G)
        have b := Over.w (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) G)
        exact ((Category.comp_id _).symm.trans a).trans b.symm
      have e₂ : (toUnit (TF (R := R) F)).left = jFK (R := R) F ≫ jK R := by
        have a := Over.w (toUnit (TF (R := R) F))
        exact (Category.comp_id _).symm.trans a
      have e₃ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
        (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
      have e₄ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
      calc rG ≫ (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left
          = (rG ≫ (snd (𝟙_ _) G).left) ≫ G.hom := by rw [e₁]; exact (Category.assoc _ _ _).symm
        _ = y ≫ pullback.fst G.hom (jK R) ≫ G.hom := by rw [h₂]; exact Category.assoc _ _ _
        _ = y ≫ (U.gen.hom.left ≫ A.A.hom) ≫ jK R := by rw [e₄]; exact congrArg (y ≫ ·) pullback.condition
        _ = (rA ≫ (snd (TFK (R := R) F) A.A).left) ≫ A.A.hom ≫ jK R := by rw [h₁]; simp only [Category.assoc]
        _ = rA ≫ ((fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F) ≫ jK R := by rw [e₃]; simp only [Category.assoc]
        _ = _ := by rw [e₂]; exact congrArg (rA ≫ ·) (Category.assoc _ _ _)
    · exact ((congrArg (· * _) (gs_scal_one rA z _)).trans (one_mul _)).symm
  · intro α Z rF rB h z J hJ
    rw [Fin.sum_univ_one]
    refine Eq.trans ?_ ((congrArg (· * _) (gs_scal_one rF z _)).trans (one_mul _)).symm
    have e : rB = rF ≫ (toUnit (TF (R := R) F) ▷ D.P.A).left := by
      have w : (toUnit (TF (R := R) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
        congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := R) F)) D.P.A)
      have i : IsIso (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A).left := by
        rw [← leftUnitor_hom]; exact inferInstanceAs (IsIso ((Over.forget _).map (λ_ D.P.A).hom))
      rw [← cancel_mono (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A).left, Category.assoc, w, h]
    rw [e, sval_comp (f α) _ rF z J hJ, ← hB α (rF z) _ (fun ψ => hJ (rF ≫ ψ)), ← sval_comp (s α) _ rF z J hJ,
      Category.comp_id]

end GlobalTheory.UU.IntExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamEqOfCoefEq
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefDet

theorem fn_ext_of_points {F : Type} [Field F] [IsAlgClosed F] {Y : Scheme.{0}} [IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType p] {U : Y.Opens} {a b : Γ(Y, U)}
    (h : ∀ r : Spec (CommRingCat.of F) ⟶ Y, r ≫ p = 𝟙 _ → ∀ z, r z ∈ U → gs r z U a = gs r z U b) : a = b := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hn : ((Y.basicOpen (a - b) : Y.Opens) : Set Y).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hn (Y.basicOpen (a - b)).isOpen.isLocallyClosed
  let r := pointOfClosedPoint p c hc
  let z : Spec (CommRingCat.of F) := IsLocalRing.closedPoint F
  have hz : r z ∈ Y.basicOpen (a - b) := (congrArg (· ∈ Y.basicOpen (a - b)) (pointOfClosedPoint_apply p c hc z)).mpr hcW
  have hU : r z ∈ U := Y.basicOpen_le _ hz
  have e := h r (pointOfClosedPoint_comp p c hc) z hU
  have hu : IsUnit (gs r z U (a - b)) := by
    rw [gs_eq r z U hU, ← Scheme.mem_basicOpen _ _ z hU, ← Scheme.preimage_basicOpen]
    exact hz
  rw [gs_eq r z U hU, gs_eq r z U hU, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  rw [gs_eq r z U hU, e] at hu
  exact not_isUnit_zero hu

theorem fam_eq_of_coef_eq : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ) (s s' : Fam D.toPre F k), (∀ g : GtPtF D.toPre F, ∃ w : Frm D.toPre F k g.b, w.IsGen ∧ ∀ χ, coef s g w χ = coef s' g w χ) → s = s' := by
  intro hL R _ _ _ I hA D F _ _ _ k s s' H
  have hsm := D.toPre.P.isAb.smooth
  let p : (DegPre.BF D.toPre F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.toPre.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.toPre.P.A.hom))
  have : IsReduced (DegPre.BF D.toPre F).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  refine fam_ext fun χ j => fn_ext_of_points p fun r hr z hz => ?_
  let r' : TF (R := R) F ⟶ DegPre.BF D.toPre F := Over.homMk r (by
    rw [← Over.w (fst (TF (R := R) F) D.toPre.P.A), ← Category.assoc]
    exact (congrArg (· ≫ (TF (R := R) F).hom) hr).trans (Category.id_comp _))
  obtain ⟨g, hg⟩ := (gt_onto_divisible_kernel hL R I hA D F).1 (r' ≫ snd _ _)
  have er : lift (𝟙 (TF (R := R) F)) g.b = r' := by
    rw [hg]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
    rw [lift_fst]
    exact Over.OverMorphism.ext hr.symm
  obtain ⟨w, hw, hc⟩ := H g
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TF (R := R) F).left) D.toPre.P.isLB z
  have a := CoefBasic.isCoef_coef g hw χ s z J hJ
  have a' := CoefBasic.isCoef_coef g hw χ s' z J hJ
  rw [hc χ, a', Units.mul_left_inj, Units.mul_left_inj, er] at a
  exact (sec_trans (s.s χ) r z hz (hJ.mem _ r)).trans ((congrArg _ a.symm).trans
    (sec_trans (s'.s χ) r z hz (hJ.mem _ r)).symm)

end GlobalTheory.UT.CoefDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullBValues
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem pullB_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T₀ : Over (Spec (CommRingCat.of R))) (φ : TF (R := R) F ⟶ T₀) (k : ℕ) (f : ∀ α, SecBT D T₀ k α) (s : Raw D F k), PullB D F φ k f s → ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ TF (R := R) F) (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval (s α) (lift ρ x).left z J = sval (f α) (lift (ρ ≫ φ) x).left z J := by
  intro R _ _ D F _ _ T₀ φ k f s h α T ρ x z J hJ
  have e : (lift ρ x).left ≫ (φ ▷ D.P.A).left = (lift (ρ ≫ φ) x).left := by
    rw [← Over.comp_left, lift_whiskerRight]
  have a := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (𝟙 (DegPre.BF D F).left) (lift ρ x).left z J hJ).2.1 (s α)
  have b := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (φ ▷ D.P.A).left (lift ρ x).left z J hJ).2.1 (f α)
  have hJ' : Good D.P.L ((lift ρ x).left z) (fun ψ => J ((lift ρ x).left ≫ ψ)) := fun ψ => hJ _
  rw [e] at b
  rw [Category.comp_id] at a
  exact a.trans ((congrArg _ (h α _ _ hJ')).trans b.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.qkToAk_descends_along_baseChange : GlobalFnsSt → SecBaseChangeSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A) (p' : QkPt D'.toPre F k) (x' : TFK (R := R') F ⟶ A'.A), p'.y = hD.xe.symm p.y → IsPullGtF φ hD F p.g p'.g → x'.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) → QkToAkU U'.toUnifPre F k p' x' → QkToAkU U.toUnifPre F k p x := by
  first | exact @GlobalTheory.qkToAk_of_baseChange | exact GlobalTheory.qkToAk_of_baseChange | (intros; apply GlobalTheory.qkToAk_of_baseChange <;> assumption)
end

