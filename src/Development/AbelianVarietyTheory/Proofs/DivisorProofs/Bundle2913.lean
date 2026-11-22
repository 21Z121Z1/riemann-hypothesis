import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2836
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2772
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.RankOneModel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorDataBiextensionPeriods
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem tens_lam_core : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W), ∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb D.toPre.P.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I D D' r W T
  obtain ⟨v, hv, hvv⟩ := GlobalTheory.T.exists_linCombPullbackTransportIso_with_values (L := D.toPre.P.L) (L' := D'.toPre.P.L) (tensφ T.pr) (tensε W) T.w T.w_gen
    D.toPre.P.isLB D'.toPre.P.isLB
    (fun K : ULift.{0} (Finset (Fin 2)) => (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left)
    (fun K => (-1 : ℤ) ^ (2 - K.down.card))
  obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.exists_cubeStep_generator_tensorPowerPairs (⟨D.toPre.P.L, D.toPre.rig, D.toPre.P.isLB, D.toPre.rig_gen⟩ : RigLB D.toPre.P.A)
    D.toPre.cub W T.pr T.pr_hom
  obtain ⟨u, hu, huv⟩ := GlobalTheory.T.exists_lineBundleIso_comp_linCombGenerator (A := abelian₂ D'.toPre.P.A D'.toPre.P.L) _ _
    (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1)
      (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2)
    (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) D.toPre.P.isLB (LB.isLB_linComb D'.toPre.P.isLB _ _) v hv c hc
  refine ⟨u, hu, fun a b z J J' hJ hJ' => ?_⟩
  have e1 := hvv _ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' hJ hJ'
  have e2 := hcv (TK R) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)) z J hJ
  rw [huv _ _ z J _ (hJ'.mem _ _) hJ, e2]
  refine (GlobalTheory.T.theta_value_product_formula_degeneration R I D D' W T a b z J J' hJ hJ').trans ?_
  exact congrArg (· * _) (congrArg (· * _) e1.symm)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermNonzeroClosed
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_term_nonzero_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (Y : Ext D.toPre), ∃ (b : D.toPre.SecB 1 0) (τ : SecK D.toPre.P.L Y.q.left 1)
      (y : Y.H.left), IsTermOf Y b τ ∧ Y.H.hom y = closedPoint R ∧ y ∈ nonzeroLocus τ := by
  intro R _ _ _ hB D Y
  haveI : IsNoetherianRing R := hB.1.1
  obtain ⟨-, -, hsurj, -, hterm⟩ := GlobalTheory.T.torusExtension_smooth_affine_surjective_fourierTerms R D.toPre Y
  obtain ⟨th, x, hx, hn⟩ :=
    GlobalTheory.ThetaSectionTest.exists_nonzero_closed GlobalTheory.abelianSchemeLaws_all.1.secBaseChange D.toPre
  obtain ⟨τ, hτ⟩ := hterm 1 0 th
  obtain ⟨y, rfl⟩ := Y.q.left.surjective x
  refine ⟨th, τ, y, hτ, ?_, ?_⟩
  · rw [← hx, ← Scheme.Hom.comp_apply, Over.w]
  · obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.toPre.P.isLB y
    have e := hτ Y.H (𝟙 _) y J hJ
    have hu : IsUnit (sval th (𝟙 Y.H ≫ Y.q).left y J) := by
      rw [Category.id_comp]
      exact GlobalTheory.ThetaUnit.isUnit_sval th _ y hn hJ
    have hτu : IsUnit (sval τ (𝟙 Y.H : Y.H ⟶ Y.H).left y J) := by
      rw [e]; exact hu.mul (Units.isUnit _)
    rw [Over.id_left] at hτu
    exact (GlobalTheory.SectionBaseChange.mem_nonzeroLocus τ _).2
      ⟨_, hJ.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left),
        (GlobalTheory.ThetaUnit.isUnit_gs_iff _ y _ (hJ.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left)) _).1 hτu⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantValueNeZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaConstant_value_ne_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ b, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := by
  first | exact @GlobalTheory.Poinc.Sep.UMem.exists_th_ne_zero | exact GlobalTheory.Poinc.Sep.UMem.exists_th_ne_zero | (intros; apply GlobalTheory.Poinc.Sep.UMem.exists_th_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsGenericFibreTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem spMap_comp_tfk {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F) :
    spMap em.toRingHom ≫ (TFK (R := R) (Kb R)).hom = (TFK (R := R) F).hom := by
  simp only [TFK, Over.mk_hom, jFK]
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp

theorem Trait.exists_lab_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∃ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ p', QkToAkU T.U.toUnifPre F (C.n ^ j) p' (lab' p')) ∧ ∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α := by
  intro R _ _ _ hR D C j W _ _ _ T F _ _ _ _ em hF f hfi hf1 hf2
  have : CharZero R := hR.2
  have hN : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  have hbij := qkPt_algClosure_bijective R D.toPre F em (C.n ^ j) hN
  have hpull : ∀ p' : QkPt T.D'.toPre F (C.n ^ j), ∃ p₁ : QkPt D.toPre F (C.n ^ j),
      p'.y = T.hD.xe.symm p₁.y ∧ IsPullGtF T.φ T.hD F p₁.g p'.g := fun p' =>
    qkPullExists GlobalTheory.globalFns_holds R W T.φ D.toPre T.D'.toPre T.hD F hF (C.n ^ j) p'
  have huniq : ∀ (p' : QkPt T.D'.toPre F (C.n ^ j)) (p₁ p₂ : QkPt D.toPre F (C.n ^ j)),
      p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g →
      p'.y = T.hD.xe.symm p₂.y → IsPullGtF T.φ T.hD F p₂.g p'.g → p₁ = p₂ :=
    fun p' p₁ p₂ h₁ g₁ h₂ g₂ => GlobalTheory.TorusExt.qk_ext (T.hD.xe.symm.injective (h₁.symm.trans h₂))
      (GlobalTheory.ArcPull.pullGt_unique' T.hD g₁ g₂)
  choose P₁ hP₁ using hpull
  choose P hP using fun p' => (hbij.2 (P₁ p')).exists

  let y : QkPt D.toPre (Kb R) (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A) := fun p =>
    Over.homMk (spMap em.toRingHom ≫ (C.lab j p).left) (by
      rw [Category.assoc, Over.w, spMap_comp_tfk])
  let g : QkPt D.toPre (Kb R) (C.n ^ j) → (TFK (R := R) F ⟶ TFK (R := R) F ⊗ C.A.A) := fun p => lift (𝟙 _) (y p)
  have hg1 : ∀ p, (g p).left ≫ (fst (TFK (R := R) F) C.A.A).left = 𝟙 _ := fun p => by
    rw [← Over.comp_left, lift_fst]; rfl
  have hg2 : ∀ p, (g p).left ≫ (snd (TFK (R := R) F) C.A.A).left = spMap em.toRingHom ≫ (C.lab j p).left := fun p => by
    rw [← Over.comp_left, lift_snd]; rfl
  have hfst : inv f ≫ (fst (TFK (R := W) F) T.A.A).left = (fst (TFK (R := R) F) C.A.A).left := by
    rw [← hf1, IsIso.inv_hom_id_assoc]
  let lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A) := fun p' =>
    Over.homMk ((g (P p')).left ≫ inv f ≫ (snd (TFK (R := W) F) T.A.A).left) (by
      rw [Category.assoc, Category.assoc, Over.w (snd (TFK (R := W) F) T.A.A), ← Over.w (fst (TFK (R := W) F) T.A.A),
        reassoc_of% hfst, reassoc_of% (hg1 (P p'))])
  have heq : ∀ p', (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β =
      spMap em.toRingHom ≫ (C.lab j (P p')).left ≫ C.α := fun p' => by
    simp only [lab', Over.homMk_left, Category.assoc]
    rw [← hf2, IsIso.inv_hom_id_assoc, reassoc_of% (hg2 (P p'))]
  refine ⟨lab', fun p' => T.lab F em hF j (P p') (P₁ p') p' (lab' p') (hP p') (hP₁ p').1 (hP₁ p').2 (heq p'), ?_⟩
  intro p p₁ p' hE hy hgp
  obtain rfl : p₁ = P₁ p' := huniq p' p₁ (P₁ p') hy hgp (hP₁ p').1 (hP₁ p').2
  obtain rfl : p = P p' := (hbij.2 (P₁ p')).unique hE (hP p')
  exact heq p'

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointFromFractionAlgClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Mum.UpExt

theorem torsion_from_closure : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 → ∃ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ N = 1 ∧ x.left = spMap em.toRingHom ≫ y.left := by
  intro R _ _ A F _ _ _ em N hN x hx
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A N)
    (AbTorsionAnyBase.isFinite_and_flat_torsion (Sp (FractionRing R)) A.A A.isAb N hN).1
  let i : K' →ₐ[FractionRing R] Kb R := IsAlgClosed.lift
  let : Algebra K' (Kb R) := i.toRingHom.toAlgebra
  have : IsScalarTower (FractionRing R) K' (Kb R) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  have hmul : x ≫ mulN A.A N = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]
  let t0 : _ ⟶ torsion A.A N := pullback.lift x (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι A.A N = x := pullback.lift_fst _ _ _
  have hs : (TFK (R := R) F).hom = spMap (em.toRingHom.comp (algebraMap (FractionRing R) (Kb R))) :=
    congrArg spMap em.comp_algebraMap.symm
  obtain ⟨w, hw⟩ := H (Kb R) F em.toRingHom t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion A.A N).hom = (TFK (R := R) (Kb R)).hom := by
    refine spec_map_field_cancel em.toRingHom _ _ ?_
    rw [← Category.assoc, hw, Over.w t0, hs, ← spMap_comp_spMap]
    rfl
  let w1 : TFK (R := R) (Kb R) ⟶ torsion A.A N := Over.homMk w hw2
  refine ⟨w1 ≫ torsion.ι A.A N, ?_, ?_⟩
  · have hc : torsion.ι A.A N ≫ mulN A.A N = toUnit _ ≫ η :=
      pullback.condition.trans (congrArg (· ≫ η) (toUnit_unique _ _))
    have h1 : (w1 ≫ torsion.ι A.A N) ≫ mulN A.A N = toUnit _ ≫ η := by
      rw [Category.assoc, hc, ← Category.assoc, comp_toUnit]
    rwa [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, ← Hom.one_def] at h1
  · rw [← ht0, Over.comp_left, ← hw, Category.assoc]
    rfl

end GlobalTheory.Mum.UpExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateLabelThetaConstantDividesA
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.TorTrans

theorem exists_trait_pull {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (φ : R →+* W)
      (ga : FractionRing R →+* FractionRing W) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
      (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal W) D' A' G')
      (a : A'.A.left ⟶ A.A.left) (xe : D'.toPre.X ≃+ D.toPre.X)
      (em : AlgebraicClosure (FractionRing R) →+* AlgebraicClosure (FractionRing W)),
      IsAdicComplete (maximalIdeal W) W ∧ IsLocalHom φ ∧ (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧
      IsSemiAbelian G' ∧ IsGrpPullback A'.A A.A (spMap ga) a ∧ LBIso A'.L (A.L.pull a) ∧
      em.comp (algebraMap (FractionRing R) _) = (algebraMap (FractionRing W) _).comp ga ∧
      ∀ k, 1 ≤ k → ∀ (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) k)
        (x : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A.A),
        QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing R)) k p x →
        ∃ (p' : QkPt D'.toPre (AlgebraicClosure (FractionRing W)) k)
          (x' : TFK (R := W) (AlgebraicClosure (FractionRing W)) ⟶ A'.A), p'.y = xe.symm p.y ∧
          QkToAkU U'.toUnifPre (AlgebraicClosure (FractionRing W)) k p' x' ∧ x'.left ≫ a = spMap em ≫ x.left := by
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  haveI := hR.1
  obtain ⟨W, _, _, _, φ, hW, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have hloc : IsLocalHom φ := ⟨fun r hr => by
    by_contra h
    have : r ∈ (maximalIdeal W).comap φ := hc.symm ▸ (mem_maximalIdeal r).2 h
    exact (mem_maximalIdeal _).1 this hr⟩
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨D', hD, A', U', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR hW' φ hφ (Ideal.map_le_iff_le_comap.2 hc.ge) hG U
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp φ) := (IsFractionRing.injective W _).comp hφ
  let ga : FractionRing R →+* FractionRing W := IsFractionRing.lift hinj
  have hga : ∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r) := fun r => IsFractionRing.lift_algebraMap hinj r
  have hsq : jK W ≫ spMap φ = spMap ga ≫ jK R := by
    rw [← Spec.map_comp, ← Spec.map_comp]; congr 1; ext1; exact RingHom.ext fun r => (hga r).symm
  have g₁ := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have g₂ := ((GlobalTheory.ThetaBaseChange.grp_generic U'.toUnifPre).comp (isGrpPullback_pullback G (spMap φ))).congr hsq rfl
  let a : A'.A.left ⟶ A.A.left := g₁.1.lift _ (A'.A.hom ≫ spMap ga) (g₂.1.w.trans (Category.assoc _ _ _).symm)
  have ha : a ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = _ := g₁.1.lift_fst _ _ _
  have hb : (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst G.hom (specOf φ) := Category.id_comp _
  have gp : IsGrpPullback A'.A A.A (spMap ga) a := g₁.cancel (g₂.congr rfl ha.symm) (g₁.1.lift_snd _ _ _)
  letI : Algebra (FractionRing R) (AlgebraicClosure (FractionRing W)) :=
    ((algebraMap (FractionRing W) (AlgebraicClosure (FractionRing W))).comp ga).toAlgebra
  obtain ⟨em⟩ : Nonempty (AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] AlgebraicClosure (FractionRing W)) :=
    ⟨IsAlgClosed.lift⟩
  have hF : GlobalTheory.ArcPull.Compat φ (AlgebraicClosure (FractionRing W)) := fun r =>
    congrArg (algebraMap (FractionRing W) (AlgebraicClosure (FractionRing W))) (hga r)
  refine ⟨W, _, _, hW.1, hW.2.2, φ, ga, D', A', _, _, _, U', a, hD.xe, em.toRingHom, hW.2.1, hloc, hga,
    IsSemiAbelian.pullback _ G hG, gp, ?_, em.comp_algebraMap, fun k hk p x hpx => ?_⟩
  · have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have hgi' : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have H₀ : LBIso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
      LBIso.chartPull (h := U.gen.inv.left) (chartPullSec A.L _ _ hgi)
        (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => rfl) U.ext
    have H₁ : LBIso A'.L (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst _ (jK W))) :=
      LBIso.chartPull (h := U'.gen.inv.left) (chartPullSec A'.L _ _ hgi')
        (chartPullSame U'.LG.L _ (fun _ => pullback.fst _ (jK W)) _ _ fun _ => rfl) U'.ext
    have H₂ : LBIso (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst _ (jK W)))
        (U.LG.L.pull (a ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
      LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullSame U.LG.L _ (fun _ => _) _ _ fun _ => ha.trans (congrArg (_ ≫ ·) hb.symm))
        ⟨hP.lg.choose, hP.lg.choose_spec.1⟩
    have H₃ : LBIso (A.L.pull a) (U.LG.L.pull (a ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
      LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSame U.LG.L _ (fun _ => _) _ _ fun _ => rfl) H₀
    exact (H₁.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB U.LG.isLB _) H₂).trans A'.isLB (pull_isLB U.LG.isLB _)
      (pull_isLB A.isLB _) H₃.symm
  · obtain ⟨⟨p₁, h₁⟩, hx, hgal⟩ := GlobalTheory.UT.ClModel.galois_all R _ hR D A G hG U _ _ em k hk p
    obtain ⟨x₁, hx₁⟩ := hx x
    have hw : x₁.left ≫ A.A.hom = jFK (R := W) (AlgebraicClosure (FractionRing W)) ≫ spMap ga :=
      (Over.w x₁).trans (Spec.map_comp (CommRingCat.ofHom ga) (CommRingCat.ofHom (algebraMap _ _)))
    let x' : TFK (R := W) (AlgebraicClosure (FractionRing W)) ⟶ A'.A :=
      Over.homMk (gp.1.lift x₁.left _ hw) (gp.1.lift_snd _ _ _)
    have h₄ : x'.left ≫ a = x₁.left := gp.1.lift_fst _ _ _
    obtain ⟨h₂, h₃⟩ := (GlobalTheory.ArcPull.eq_pullQk_iff hD hL.globalFns hF D.tau_bimult D'.tau_bimult p₁ _).1 rfl
    refine ⟨_, x', h₂.trans (congrArg _ h₁.1), ?_, h₄.trans hx₁⟩
    refine h5.qkBaseChange R W _ _ hR hW' φ D A G U _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hP
      _ hF k hk p₁ x₁ _ x' h₂ h₃ ?_ ((hgal p₁ x x₁ h₁ hx₁).1 hpx)
    rw [← h₄, Category.assoc, ha, hb, Category.assoc]

theorem div_and_translate {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type}
    [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {m : ℕ}
    {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ) {x₀ : X₁.S.Gam}
    (hx₀ : X₁.M.Div X₁.S.th x₀ z₁) (a : X₁.S.Gam) (mu : Fin 8 → X) (ha : 𝔪.YY a mu) :
    (a ∈ X₁.S.supI X₁.M z₁ → ∃ w, mu = (X₁.S.r * X₁.S.N) • w) ∧
      ((∃ w, mu = (X₁.S.r * X₁.S.N) • w) → ∃ b : X₁.S.Gam, X₁.ρ.n • b = 0 ∧ a + b ∈ X₁.S.supI X₁.M z₁) := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI := 𝔪.loc
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨T, _, _, _, _, φ, ga, D', A', G', _, _, U', α, xe, em, hc, hloc, hga, hG', gp, lb, hem, hmove⟩ :=
    exists_trait_pull hA 𝔪.semi 𝔪.U
  let ξ : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁
  have hx : ξ (closedPoint V) = z₁ := by
    show X₁.M.Z.fromSpecStalk z₁ (spMap ev (closedPoint V)) = z₁
    rw [show spMap ev (closedPoint V) = closedPoint _ from IsLocalRing.comap_closedPoint ev]
    exact Scheme.fromSpecStalk_closedPoint
  have hU : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : T) := by
    have := (X₁.S.unit.map (Spec.preimage (ξ ≫ X₁.M.s)).hom).map φ
    rwa [map_natCast, map_natCast] at this
  haveI : CharZero (FractionRing T) := charZero_of_injective_algebraMap (IsFractionRing.injective T (FractionRing T))
  have cart : IsGrpPullback A'.A X₁.ρ.P.A (spMap (ga.comp 𝔪.yK)) (α ≫ 𝔪.φ) :=
    (gp.comp 𝔪.cart).congr (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom ga)).symm rfl
  have lb' : LBIso A'.L (X₁.ρ.P.L.pull (α ≫ 𝔪.φ)) :=
    LBIso.trans A'.isLB (pull_isLB 𝔪.A.isLB _) (pull_isLB X₁.ρ.P.isLB _) lb (lbIso_pull_comp ⟨𝔪.wl, 𝔪.wl_gen⟩ α)
  obtain ⟨s, v, hs, hsv, -, hcl⟩ := GlobalTheory.Poinc.ScaleAtModel.scale_at_model _ _ X₁.S X₁.ρ T hc hU (ga.comp 𝔪.yK) A' _
    cart lb' G' hG' D' U' (GlobalTheory.ThetaGeneric.exists_th_ne_zero GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 _ _ _ X₁.ρ _ _)
  have tr : ∀ a mu, 𝔪.YY a mu → (IsUnit (v a) → ∃ w, mu = (X₁.S.r * X₁.S.N) • w) ∧
      ((∃ w, mu = (X₁.S.r * X₁.S.N) • w) → ∃ b : X₁.S.Gam, X₁.ρ.n • b = 0 ∧ IsUnit (v (a + b))) := by
    rintro a mu ⟨p, x, hp, hq, hxa⟩
    obtain ⟨p', x', hp', hq', hx'⟩ := hmove _ hk p x hq
    obtain ⟨h₁, h₂⟩ := hcl a p' x' hq' (by
      rw [← Category.assoc, hx', Category.assoc, hxa, ← Category.assoc, ← RingHom.comp_assoc, ← hem, RingHom.comp_assoc]
      exact congrArg (· ≫ _) (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom em)).symm)
    rw [hp] at hp'
    refine ⟨fun h => ?_, fun ⟨w, hw⟩ => h₂ ⟨xe.symm (𝔪.e₈ w), by rw [hp', hw, map_nsmul, map_nsmul]⟩⟩
    obtain ⟨z, hz⟩ := h₁ h
    refine ⟨𝔪.e₈.symm (xe z), ?_⟩
    rw [← map_nsmul, ← map_nsmul, ← hz, hp', AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  have hsp : ∀ w, (jK V ≫ ξ) w ⤳ (jK V ≫ ξ) (closedPoint (FractionRing V)) := fun w => by
    rw [Subsingleton.elim w (closedPoint (FractionRing V))]
  have hsx : ξ (closedPoint V) ⤳ z₁ := hx ▸ specializes_rfl
  let wv : X₁.S.Gam → V := fun b => RatModel.valLoc ξ z₁ hsx ⟨X₁.S.th b / X₁.S.th x₀, hx₀.2 b⟩
  have hw : ∀ b, φ (wv b) * v x₀ = v b := fun b => by
    have e1 : X₁.M.val (jK V ≫ ξ) (X₁.S.th b / X₁.S.th x₀) = algebraMap V (FractionRing V) (wv b) :=
      RatModel.val_spMap_comp (algebraMap V (FractionRing V)) ξ hsx ⟨X₁.S.th b / X₁.S.th x₀, hx₀.2 b⟩
    have e2 := RatModel.val_mul hsp (RatModel.O_le_of_specializes (hx ▸ (IsLocalRing.specializes_closedPoint
      (jK V (closedPoint (FractionRing V)))).map ξ.continuous) (hx₀.2 b)) (𝔪.reg _ (X₁.S.th_mem x₀))
    rw [div_mul_cancel₀ _ hx₀.1, e1] at e2
    have e3 : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ =
        algebraMap V (FractionRing V) (wv b) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
      rw [𝔪.yK_eq, 𝔪.yK_eq]; exact e2
    have e4 := congrArg ga e3
    rw [map_mul, hga] at e4
    have e5 := hsv b
    have e6 := hsv x₀
    rw [RingHom.comp_apply] at e5 e6
    rw [e5, e6, ← _root_.mul_assoc, mul_comm _ s, _root_.mul_assoc, ← map_mul] at e4
    exact IsFractionRing.injective T (FractionRing T) (mul_left_cancel₀ hs e4).symm
  obtain ⟨a₀, ha₀⟩ := (GlobalTheory.Poinc.Sep.Labels.yy_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 𝔪).2.1 0
  obtain ⟨b₀, -, hb₀⟩ := (tr a₀ 0 ha₀).2 ⟨0, (nsmul_zero _).symm⟩
  have hv0 : IsUnit (v x₀) := isUnit_of_mul_isUnit_right (show IsUnit (φ (wv (a₀ + b₀)) * v x₀) by rw [hw]; exact hb₀)
  have hset : ∀ b, b ∈ X₁.S.supI X₁.M z₁ ↔ IsUnit (v b) := fun b => by
    show X₁.M.Div X₁.S.th b z₁ ↔ IsUnit (v b)
    rw [hx₀.div_iff_isUnit b, ← RatModel.isUnit_valLoc_iff ξ hx, ← hw b, IsUnit.mul_iff, and_iff_left hv0,
      isUnit_map_iff φ]
  simp only [hset]
  exact tr a mu ha

theorem exists_translate_mem_supI : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ a, 𝔪.YY a 0 → ∃ b : X₁.S.Gam, X₁.ρ.n • b = 0 ∧ a + b ∈ X₁.S.supI X₁.M z₁ := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ hx₀ a ha
  exact (div_and_translate 𝔪 hx₀ a 0 ha).2 ⟨0, (nsmul_zero _).symm⟩

end GlobalTheory.Poinc.Sep.TorTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateThetaSectionUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem gs_comp_stalkMap {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)) : gs (f ≫ g) z U a = (f.stalkMap z).hom (gs g (f z) U a) := by
  rw [← gs_pull f g z U h a, gs_eq f z _ h, gs_eq g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).symm

theorem formEq_famφB_zero {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) {Y : Scheme.{0}} (h : Y ⟶ D.P.A.left) :
    FormEq (fun i => h ≫ D.famφB 0 i) (DegPre.famε 1) (fun _ : Fin 1 => h) (fun _ => (1 : ℤ)) := by
  intro U _ hh
  have e0 : D.famφB 0 0 = 𝟙 _ := rfl
  have e1 : D.famφB 0 1 = 𝟙 _ := by
    show (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = _
    rw [ThetaOne.c_zero, MonObj.comp_one]
    show ((𝟙 D.P.A) * 1).left = _
    rw [_root_.mul_one]; rfl
  have e2 : D.famφB 0 2 = D.famφB 0 3 := by
    show (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left
    rw [ThetaOne.c_zero, MonObj.comp_one]
    rfl
  simp only [Fin.prod_univ_four, Fin.prod_univ_one, e0, e1, e2]
  simp [DegPre.famε]

theorem exists_unitAt_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ N : ℕ, 2 ≤ N → IsUnit (N : V) → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ D.P.A)), IntTerm.Exhausts D.P N b → ∀ a : 𝟙_ (Over (Sp V)) ⟶ D.P.A, ∃ c, IntTerm.UnitAt D θ (a * b c) := by
  intro V _ _ _ D θ hθ N hN hNV C b hb a
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  let k := AlgebraicClosure (ResidueField V)
  let f : V →+* k := (algebraMap (ResidueField V) k).comp (residue V)
  let r : Sp k ⟶ Sp V := Spec.map (CommRingCat.ofHom f)
  have hNk : (N : k) ≠ 0 := by
    have := (hNV.map f).ne_zero
    rwa [map_natCast] at this
  let θ' := ThetaOne.pullTo D f θ
  have hbasis := hθ k f θ' (ThetaOne.isPullSecLC_pullTo D f θ)
  obtain ⟨j₀, hj₀⟩ := ThetaOne.exists_ne_zero D f θ' hbasis
  obtain ⟨th, hth⟩ := exists_sec D.P.isLB (formEq_famφB_zero D (snd (Over.mk r) D.P.A).left) θ'
  have hne : SecM.ofSec D.P.A (L := D.P.L) (a := 1) (T := Over.mk r) th ≠ 0 := by
    intro h0
    apply hj₀
    have hz : ∀ j, th.f j = 0 := fun j => congrFun (congrArg Subtype.val h0) j
    refine sec_ext_val D.P.isLB (s' := H1.SectionArithmetic.secZero _) (fun y J hJ => ?_) j₀
    rw [← hth _ (𝟙 _) y J hJ]
    show gs _ y _ (th.f _) = gs _ y _ 0
    erw [hz]
    have gz : ∀ {Y : Scheme.{0}} (y : Y) (U : Y.Opens), gs (𝟙 Y) y U 0 = 0 := fun y U => by
      unfold gs; split_ifs <;> simp only [map_zero]
    exact (gz _ _).trans (gz _ _).symm
  obtain ⟨y, hy, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange D.P r hN hNk th hne
    (toUnit (Over.mk r) ≫ a)
  obtain ⟨c, hc⟩ := hb k r y hy
  refine ⟨c, ?_⟩
  have hmul : (toUnit (Over.mk r) ≫ a) * y = toUnit (Over.mk r) ≫ (a * b c) := by rw [hc, MonObj.comp_mul]
  rw [hmul] at hu
  let g := a * b c
  let q : Sp k := closedPoint k
  obtain ⟨J, hJ, -⟩ := exists_good D.P.L D.P.isLB q (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
  have h1 := hu q J hJ
  have hρ : (ptSecT D.P.A (toUnit (Over.mk r) ≫ g)).left ≫ (snd (Over.mk r) D.P.A).left = r ≫ g.left := by
    rw [← Over.comp_left, ptSecT, lift_snd, Over.comp_left]
    congr 1
  have hθ'e : θ' = H1.SectionArithmetic.pullSec θ (snd (Over.mk r) D.P.A).left :=
    SecOps.sec_ext fun j => ThetaOne.isPullSecLC_pullTo D f θ j
  have h2 : IsUnit (sval θ (r ≫ g.left) q J) := by
    have e := hth _ (ptSecT D.P.A (toUnit (Over.mk r) ≫ g)).left q J hJ
    rw [← hρ, ← H1.SectionArithmetic.sval_pullSec θ _ _ q hJ, ← hθ'e, ← e]
    exact h1
  have hrq : r q = closedPoint V := by
    show (Spec.map (CommRingCat.ofHom f)).base (closedPoint k) = _
    rw [Spec.map_base]
    exact IsLocalRing.comap_closedPoint f
  refine ⟨fun σ => J (r ≫ σ), fun σ => ?_, ?_⟩
  · have := hJ (r ≫ σ)
    rwa [Scheme.Hom.comp_apply, hrq] at this
  · rw [sval_of θ (r ≫ g.left) q J (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) (fun i => by rw [Category.assoc])] at h2
    have hm : g.left (r q) ∈ (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).U
        (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) :=
      show g.left (r q) ∈ LB.wchart D.P.L (D.famφB 0) (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) from Set.mem_iInter.2 fun i => by
        have := hJ (r ≫ g.left ≫ D.famφB 0 i)
        simpa [Scheme.Hom.comp_apply] using this
    have h2' : IsUnit ((r.stalkMap q).hom (gs g.left (r q) _ (θ.f (fun i => J (r ≫ g.left ≫ D.famφB 0 i))))) := by
      rw [← gs_comp_stalkMap r g.left q _ hm]; exact h2
    have h3 := isUnit_of_map_unit (r.stalkMap q).hom _ h2'
    rw [hrq] at h3
    exact h3

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueUnitsGlueArtinFibreProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_units_glue_artinFibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), Flat Y.hom → IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) → IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ Y₂.hom = Y₀.hom ≫ Spec.map g₂ → (∀ (U : Y.left.Opens) (a₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)ˣ) (a₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)ˣ), (∀ x : Y₀.left, i₁ x ∈ j₁ ⁻¹ᵁ U → gm i₁ x (j₁ ⁻¹ᵁ U) a₁ = gm i₂ x (j₂ ⁻¹ᵁ U) a₂) → ∃ d : Γ(Y.left, U)ˣ, pullU j₁ U d = a₁ ∧ pullU j₂ U d = a₂) ∧ (∀ (U : Y.left.Opens) (d d' : Γ(Y.left, U)ˣ), pullU j₁ U d = pullU j₁ U d' → pullU j₂ U d = pullU j₂ U d' → d = d') := by
  first | exact @GlobalTheory.PinchUnits.main | exact GlobalTheory.PinchUnits.main | (intros; apply GlobalTheory.PinchUnits.main <;> assumption)
end

