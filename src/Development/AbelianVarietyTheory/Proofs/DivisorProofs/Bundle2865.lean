import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2774
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VGeIffExtended
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulIncl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2775
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTermsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_smooth_affine_surjective_fourierTerms : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D), Smooth Y.H.hom ∧ IsAffineHom Y.q.left ∧ Surjective Y.q.left ∧ IsMonHom Y.q ∧ ∀ (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ τ : SecK D.P.L Y.q.left k, IsTermOf Y b τ := by
  first | exact @GlobalTheory.Mum.ext_smooth_affine_surj_terms | exact GlobalTheory.Mum.ext_smooth_affine_surj_terms | (intros; apply GlobalTheory.Mum.ext_smooth_affine_surj_terms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLengthLowerBoundQuotientStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_length_lower_bound_quotient : Size → Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → zBase (Fm.L x ι) ^ 24 ≤ lenT p i PP ∧ ∀ u1, Quo p i PP u1 → lenT p i PP * GlobalTheory.CovHt.l1 u1 ≤ C * unitE p ∧ ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (lenT p i PP : ℤ) ≤ u1 τ a - u1 τ b := by
  first | exact @GlobalTheory.CovHt.DividedNum.dividedWeight | exact GlobalTheory.CovHt.DividedNum.dividedWeight | (intros; apply GlobalTheory.CovHt.DividedNum.dividedWeight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyPositivePolarizationProjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.ProjOverC

theorem isProjOver_A : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → IsProjOver X.A.hom := by
  intro F _ _ 𝔠 X c hc
  have hL : (X.diag c).IsLB := LB.isLB_pull (X.isLB c) _
  have hq : IsQProjOver (X.A.hom ≫ 𝟙 (Sp ℂ)) :=
    GlobalTheory.RelAmpleQProj.isQProjOver_of_relAmple ℂ (Sp ℂ) (𝟙 _) X.A (X.diag c)
      (GlobalTheory.ZM.OnePoint.isQProjOver_id ℂ) hL (X.pos c hc)
  rw [Category.comp_id] at hq
  have hp : IsProper X.A.hom := X.ab.proper
  have : IsProper (𝟙 X.A.left ≫ X.A.hom) := by rw [Category.id_comp]; exact hp
  have h := GlobalTheory.isProjOver_of_isProper_of_isImmersion (𝟙 X.A.left) hq
  rwa [Category.id_comp] at h

example : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → IsProjOver X.A.hom := isProjOver_A

end GlobalTheory.RealMult.ProjOverC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitScalarCancelOfIsFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_scalar_cancel_of_isField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (b : W) (c : FractionRing R), IsField R → b ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom b) * sval σ p z J = gs p z ⊤ (scal T.G.hom b) * (gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J)) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J := by
  first | exact @GlobalTheory.Mum.cancel_field | exact GlobalTheory.Mum.cancel_field | (intros; apply GlobalTheory.Mum.cancel_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitSectionIntegralExpansionMemRangeInverseExpa
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Mum.TraitValue

theorem value_of_expands {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (F : Type) [Field F] [Algebra (FractionRing W) F] {k : ℕ} (hk : 1 ≤ k)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK W))))
    (t : SecK A.L (snd (TFK (R := W) F) A.A).left k) (s : Fam D.toPre F k) (h : U.ExpandsF F k w t s)
    (σ : H0 U.LG.L k) (f : ∀ x, D.toPre.SecB k x) (hσ : ∀ e, U.ExpandsAt e k σ f)
    (hs : ∀ x, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F x) (DegPre.famε k) (s.s x) (D.toPre.famφB x)
      (DegPre.famε k) (f x) (DegPre.prB D.toPre F).left 1)
    (Z : Scheme.{0}) (q : Z ⟶ (TFK (R := W) F ⊗ A.A).left) (z : Z) JG Jt (hG : Good U.LG.L z JG) (ht : Good A.L z Jt) :
    sval σ (q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W)) z JG =
      (gw w (q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left) z
        (JG (q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W)))
        (fun _ => Jt (q ≫ (snd (TFK (R := W) F) A.A).left)) ^ k).val * sval t q z Jt := by
  obtain ⟨σ', h₁, h₂⟩ := h
  have h₃ : U.ExpandsG F k (extendSec U.toUnifPre F k (genericSec U.toUnifPre k σ)) s := by
    refine (expandsG_iff U.toUnifPre F k _ s).2 ⟨1, fun _ => 1, fun _ => (σ, f), fun _ => hσ, ?_, fun α => ?_⟩
    · rw [Fin.sum_univ_one, one_smul]
    · rw [Fin.sum_univ_one, one_smul]
      refine sec_ext' D.toPre.P.isLB fun y J hJ => ?_
      have a := (secScal_iff_val D.toPre.P.isLB _ _ _ _).1 (hs α) y J hJ
      rw [gs_eq _ y ⊤ trivial, map_one, map_one, _root_.one_mul] at a
      exact a.symm.trans ((sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (f α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing W) F))))))).symm
  obtain rfl : σ' = _ :=
    ((expandsG_bijective U.toUnifPre F GlobalTheory.allSixLaws.1.globalFns hk (U.expand k hk)).2 s).unique h₂ h₃
  let n : TFK (R := W) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have e₁ : (q ≫ n.left) ≫ (U.genF F).left = q := by
    rw [Category.assoc, ← Over.comp_left, hn, Over.id_left, Category.comp_id]
  have e₂ : (q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left =
      q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left := by
    rw [Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left]
  have e₃ : (q ≫ n.left) ≫ UnifPre.gFK (G := G) F =
      q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W) := by
    rw [← Category.assoc, e₂, Category.assoc, Category.assoc]
  have e₄ : ((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫ U.gen.hom.left =
      q ≫ (snd (TFK (R := W) F) A.A).left := by
    rw [e₂, Category.assoc, Category.assoc, ← Over.comp_left _ _ _ U.gen.inv, Iso.inv_hom_id, Over.id_left,
      Category.comp_id]
  have key := (isoRelM_iff w _ k _ h₁.1 _ h₁.2.1 _ _).1 h₁ Z (q ≫ n.left) z
    (JG ((q ≫ n.left) ≫ UnifPre.gFK (G := G) F))
    (Jt (((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫ U.gen.hom.left))
    (hG ((q ≫ n.left) ≫ UnifPre.gFK (G := G) F))
    (ht (((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫ U.gen.hom.left))
  rw [Category.comp_id, e₁, e₄, zpow_natCast] at key
  have v : sval (extendSec U.toUnifPre F k (genericSec U.toUnifPre k σ)) (q ≫ n.left) z JG =
      sval σ (((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫
        pullback.fst G.hom (jK W)) z JG :=
    (sval_pullOver _ _ _ _ hG).trans (sval_pullOver _ _ _ _ hG)
  have key' := v.symm.trans key
  rw [e₂, e₃, Category.assoc, Category.assoc] at key'
  exact key'

theorem value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W)))), w₀.IsGen → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), (∀ s', T.U.ExpandsF F (C.n ^ j) w₀ (E' s') s') → ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s' : Fam T.D'.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((s').s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1) → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), p ≫ T.β = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JG Jt, Good C.P.L.L z JP → Good T.U.LG.L z JG → Good T.A.L z Jt → sval σ p z JP = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' s') q z Jt := by
  intro R _ _ _ _ D C j W _ _ _ T F _ _ _ w₀ _ E' hE F₀ s' σ hs ⟨σ'', f'', hc, hp, he⟩ Z p q h₁ h₂ z JP JG Jt gP gG gt
  have hk : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  have ep : p = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) := by
    refine T.cart.1.hom_ext (by rw [h₁]; simp only [Category.assoc]) ?_
    have a₁ : T.U.gen.inv.left ≫ pullback.snd T.G.hom (jK W) = T.A.A.hom := Over.w T.U.gen.inv
    have a₂ : (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom =
        (fst (TFK (R := W) F) T.A.A).left ≫ jFK (R := W) F :=
      (Over.w (snd (TFK (R := W) F) T.A.A)).trans (Over.w (fst (TFK (R := W) F) T.A.A)).symm
    have a₃ : spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) = jFK (R := W) F ≫ jK W :=
      Spec.map_comp (CommRingCat.ofHom (algebraMap W (FractionRing W))) (CommRingCat.ofHom (algebraMap (FractionRing W) F))
    rw [h₂, a₃, Category.assoc, Category.assoc, Category.assoc, pullback.condition, reassoc_of% a₁, reassoc_of% a₂]
  have c := hc Z p z JP JG gP gG
  have h1 : Out.scal T.G.hom (1 : W) = 1 := by unfold Out.scal; rw [map_one, map_one]
  rw [h1, gs_eq _ z ⊤ trivial, map_one, map_one, _root_.one_mul] at c
  have v := value_of_expands T.U F hk w₀ (E' s') s' (hE s') σ'' f'' he (hs f'' hp) Z q z JG Jt gG gt
  rw [c, _root_.mul_assoc, ← v, ← ep]

end GlobalTheory.Mum.TraitValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedCubicalBundleClosedFibreUniformisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedCubicalBundle_closedFibre_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G), a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
    ∀ P₁ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G),
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₁ (GlobalTheory.ValueForm.modelCP U.toUnifPre GlobalTheory.firstFiveLaws.1.globalFns) →
    ∃ (a₀ : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) ⟶ thickObj R (maximalIdeal R) 0 G)
      (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)),
      a₀.left ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0) = thick R (maximalIdeal R) 0 ≫ a.left ∧ a₀ ^ 2 = 1 ∧
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P ∧
      P₀.L.L = P₁.L.L.pull ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        val P₀.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a₀) * x).left z J * (val P₁.sym (toUnit T ≫ a₀).left z J)⁻¹) ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x y u : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        cubV P₀.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a₀) * u) * (cubV P₁.c z J x y (toUnit T ≫ a₀))⁻¹) := by
  first | exact @GlobalTheory.Mum.TranslateLevel.exists_level_translate | exact GlobalTheory.Mum.TranslateLevel.exists_level_translate | (intros; apply GlobalTheory.Mum.TranslateLevel.exists_level_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedUniformizationPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory
namespace TorusPullFrame

open GlobalTheory.PullHermitian

variable {X Y : Scheme.{0}}

lemma chart_pull_iff (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (j : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull f).U j ↔ ⊤ ≤ (x ≫ f) ⁻¹ᵁ L.U (j PUnit.unit) :=
  ⟨fun h _ hp => Set.mem_iInter.1 (h hp) PUnit.unit, fun h _ hp => Set.mem_iInter.2 fun _ => h hp⟩

lemma le_left {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ U :=
  h.trans (fun _ hp => And.left hp)

lemma le_right {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ V :=
  h.trans (fun _ hp => And.right hp)

lemma valAt'_pull_g (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (i j : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull f).U i ⊓ (L.pull f).U j)) :
    valAt' x ((L.pull f).U i ⊓ (L.pull f).U j) ((L.pull f).g i j).val =
      valAt' (x ≫ f) (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
        (L.g (i PUnit.unit) (j PUnit.unit)).val := by
  have hi := (chart_pull_iff x L f i).1 (le_left h)
  have hj := (chart_pull_iff x L f j).1 (le_right h)
  rw [valAt'_eq_unitVal x h, valAt'_eq_unitVal _ (inf_of _ hi hj)]
  have := unitVal_linComb x L f 1 (i PUnit.unit) (j PUnit.unit) h (inf_of _ hi hj)
  exact congrArg Units.val (this.trans (zpow_one _))

lemma differentiable_append {g : ℕ} (x₀ : Fin g → ℂ) :
    Differentiable ℂ (fun z : Fin g → ℂ => (Fin.append z x₀ : Fin (g + g) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [Fin.append_left]; exact differentiable_apply a
  · simp only [Fin.append_right]; exact differentiable_const _

theorem exists_holUnif_pull_right : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L₀ : LB A.left) (g : ℕ) (u : HolUnif A L₀ g)
    (L : LB (A ⊗ A).left) (U : HolUnif (A ⊗ A) L (g + g)),
    (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → ∀ x₀ : Fin g → ℂ,
    ∃ u' : HolUnif A (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left) g, u'.ex = u.ex ∧
      (∀ j z, (⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left).U j ↔
        ⊤ ≤ (U.ex (Fin.append z x₀)).left ⁻¹ᵁ L.U (j PUnit.unit))) ∧
      ∀ j z, u'.fr j z = U.fr (j PUnit.unit) (Fin.append z x₀) := by
  intro A _ L₀ g u L U hU x₀
  have key : ∀ z, u.ex z ≫ lift (𝟙 A) (toUnit A ≫ u.ex x₀) = U.ex (Fin.append z x₀) := by
    intro z
    rw [hU, comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _), Category.id_comp]
  have keyl : ∀ z, (u.ex z).left ≫ (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left =
      (U.ex (Fin.append z x₀)).left := fun z => by rw [← Over.comp_left, key]
  have hch : ∀ j z, (⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left).U j ↔
      ⊤ ≤ (U.ex (Fin.append z x₀)).left ⁻¹ᵁ L.U (j PUnit.unit)) := fun j z =>
    (chart_pull_iff _ L _ j).trans (iff_of_eq (by rw [keyl z]))
  refine ⟨⟨u.ex, u.ex_add, u.ex_onto, u.Λ, u.ker, u.discrete, u.full, u.hol,
      fun j z => U.fr (j PUnit.unit) (Fin.append z x₀),
      fun j => (U.fr_hol (j PUnit.unit)).comp (differentiable_append x₀).differentiableOn
        (fun z hz => (hch j z).1 hz),
      fun j z hz => U.fr_ne _ _ ((hch j z).1 hz),
      fun i j z h => by
        have hi := (hch i z).1 (le_left h)
        have hj := (hch j z).1 (le_right h)
        show U.fr (i PUnit.unit) (Fin.append z x₀) = _ * U.fr (j PUnit.unit) (Fin.append z x₀)
        rw [valAt'_pull_g _ L _ i j h, keyl z]
        exact U.fr_compat _ _ _ (inf_of _ hi hj)⟩, rfl, hch, fun _ _ => rfl⟩

end TorusPullFrame
end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationIsosCommuteOfCommutatorPairingOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}

theorem snd_transl (x : 𝟙_ (Over S) ⟶ G) :
    (snd (𝟙_ (Over S)) G ≫ transl x).left = (Out.translPt G x).left := by
  congr 1
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (snd (𝟙_ (Over S)) G ≫ toUnit G)
    (fst (𝟙_ (Over S)) G), mul_comm]
  rfl

theorem exists_theta (hL : L.IsLB) (x : 𝟙_ (Over S) ⟶ G)
    (φ : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (transl x).left] ![1, -1])) (hφ : φ.IsGen) :
    ∃ θ : Out.ThetaGrp G L 1 (𝟙_ (Over S)), θ.pt = x ∧ ∀ (Z : Over S) (t : Z ⟶ 𝟙_ (Over S)) (a : Z ⟶ G)
      (z : Z.left) (J), Good L z J → CommutatorPairing.thetaVal θ t a z J = val φ a.left z J := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2)
    (φ' := ![(snd (𝟙_ (Over S)) G).left, (Out.translPt G x).left]) (ε' := ![1, -1]) (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id]
      rw [← Over.comp_left, snd_transl])
    (LB.pullGen L _ _ φ (snd (𝟙_ (Over S)) G).left) (DVR.pullGen_isGen _ _ _ _ hφ _)
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_pull hJ _ _ _).trans ?_)
  rw [← Over.comp_left, lift_snd]

theorem gen_commute_of_weilIs : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G →
    ∀ (L : LB G.left), L.IsLB → ∀ (x y : 𝟙_ (Over S) ⟶ G)
    (φx : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl x).left] ![1, -1]))
    (φy : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl y).left] ![1, -1])),
    φx.IsGen → φy.IsGen → Out.WeilIs G L 1 x y 1 →
    LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ φx (LB.pullGen L _ _ φy (GlobalTheory.UPel.HT.Hecke.transl x).left))
      (LB.mulGen L _ _ _ _ φy (LB.pullGen L _ _ φx (GlobalTheory.UPel.HT.Hecke.transl y).left)) := by
  intro S G _ _ hA L hL x y φx φy hx hy hW
  obtain ⟨θx, hθx, ex⟩ := exists_theta hL x φx hx
  obtain ⟨θy, hθy, ey⟩ := exists_theta hL y φy hy
  rw [← hθx, ← hθy] at hW
  have hC := (GlobalTheory.CommutatorPairing.commIsOf_iff hL θx θy 1).1
    ((GlobalTheory.GlobalLift.weilIs_iff_commIsOf GlobalTheory.globalFns_holds hA hL θx θy 1).1 hW)
  refine corr_of_val hL fun g J hJ => ?_
  have h := hC G (toUnit G) (𝟙 G) g J hJ
  rw [map_one, CommutatorPairing.commVal, mul_inv_eq_one, ex _ _ _ _ _ hJ, ex _ _ _ _ _ hJ, ey _ _ _ _ _ hJ,
    ey _ _ _ _ _ hJ] at h
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]
  rw [hθx, hθy, show toUnit G ≫ x * 𝟙 G = transl x from mul_comm _ _,
    show toUnit G ≫ y * 𝟙 G = transl y from mul_comm _ _] at h
  exact h

end GlobalTheory.UPel.HT.Hecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaMove

variable {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT}
  {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG}

def tf (wA : LB.Iso LA (LP.pull α)) (ℓ : LB.Iso LG (LP.pull β)) (w : LB.Iso LT (LG.pull c)) (f : Y' ⟶ Y)
    (sA : Y ⟶ XA) (sT : Y' ⟶ XT) {Z : Scheme.{0}} (q : Z ⟶ Y') (z : Z) (JP : (Z ⟶ XP) → LP.ι)
    (JA : (Z ⟶ XA) → LA.ι) (JG : (Z ⟶ XG) → LG.ι) (Jt : (Z ⟶ XT) → LT.ι) : (Z.presheaf.stalk z)ˣ :=
  (gw wA (q ≫ f ≫ sA) z (JP (q ≫ sT ≫ c ≫ β)) (JA (q ≫ f ≫ sA)))⁻¹ *
    gw ℓ (q ≫ sT ≫ c) z (JP (q ≫ sT ≫ c ≫ β)) (JG (q ≫ sT ≫ c)) *
    gw w (q ≫ sT) z (JG (q ≫ sT ≫ c)) (Jt (q ≫ sT))

end GlobalTheory.ThetaMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleFiberProductOverMulTwoIsPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TwoTors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tripleFiberProductOverMulTwo_isPullback : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A], IsPullback (t₁ A).left (ψ A).left A.hom (Two A ⊗ Two A).hom := by
  first | exact @GlobalTheory.TwoTors.TripleProd.isPullback | exact GlobalTheory.TwoTors.TripleProd.isPullback | (intros; apply GlobalTheory.TwoTors.TripleProd.isPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwicePicardClassEqZeroOfTranslatesMemOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualTriv

theorem range_sub {S : Scheme.{0}} (A : Over S) (U : S.Opens) (Y : Over S) (p : Y ⟶ A)
    (hY : ∀ y, Y.hom y ∈ U) : Set.range p.left ⊆ Set.range (A.hom ⁻¹ᵁ U).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  show A.hom (p.left y) ∈ U
  rw [← Scheme.Hom.comp_apply, Over.w p]
  exact hY y

noncomputable def liftU {S : Scheme.{0}} (A : Over S) (U : S.Opens) (Y : Over S)
    (hY : ∀ y, Y.hom y ∈ U) (p : Y ⟶ A) : Y.left ⟶ (A.hom ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (A.hom ⁻¹ᵁ U).ι p.left (range_sub A U Y p hY)

theorem liftU_fac {S : Scheme.{0}} (A : Over S) (U : S.Opens) (Y : Over S)
    (hY : ∀ y, Y.hom y ∈ U) (p : Y ⟶ A) : liftU A U Y hY p ≫ (A.hom ⁻¹ᵁ U).ι = p.left :=
  IsOpenImmersion.lift_fac _ _ _

end GlobalTheory.DualTriv

open GlobalTheory.DualTriv in
theorem GlobalTheory.twice_cls_eq_zero_of_translates_mem : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), A.hom ⁻¹ᵁ U ≤ W → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A), (∀ y, Y.hom y ∈ U) → (∀ y, v.left y ∈ V) → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → ∀ l : Y.left ⟶ W.toScheme, l ≫ W.ι = x.left → GlobalTheory.CechPic.pull l (2 • c) = 0 := by
  intro S _ A _ _ U V W hV hW c hc Y x a v hY hv hxa l hl
  set cU := GlobalTheory.CechPic.pull (A.left.homOfLE hW) c with hcU
  have zero_of : ∀ p : Y ⟶ A, (∀ y, p.left y ∈ V) →
      GlobalTheory.CechPic.pull (liftU A U Y hY p) cU = 0 := by
    intro p hp
    have H : Set.range p.left ⊆ Set.range V.ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hp y
    have e : liftU A U Y hY p ≫ A.left.homOfLE hW = IsOpenImmersion.lift V.ι p.left H ≫ A.left.homOfLE hV := by
      rw [← cancel_mono W.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
        liftU_fac, IsOpenImmersion.lift_fac]
    rw [hcU, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp, hc, map_zero]
  have s1 := GlobalTheory.T.square_theorem_pic_class_over_open S A ‹_› U cU Y (liftU A U Y hY) hY (liftU_fac A U Y hY) x a
  have s2 := GlobalTheory.T.square_theorem_pic_class_over_open S A ‹_› U cU Y (liftU A U Y hY) hY (liftU_fac A U Y hY) v a
  rw [zero_of _ (fun y => (hxa y).1), zero_of _ (fun y => (hxa y).2.1)] at s1
  rw [zero_of _ (fun y => (hxa y).2.2.1), zero_of _ (fun y => (hxa y).2.2.2), zero_of _ hv] at s2
  have two : 2 • GlobalTheory.CechPic.pull (liftU A U Y hY x) cU = 0 := by
    calc 2 • GlobalTheory.CechPic.pull (liftU A U Y hY x) cU
        = (2 • GlobalTheory.CechPic.pull (liftU A U Y hY x) cU + GlobalTheory.CechPic.pull (liftU A U Y hY a) cU +
            GlobalTheory.CechPic.pull (liftU A U Y hY a⁻¹) cU - 2 • GlobalTheory.CechPic.pull (liftU A U Y hY 1) cU) -
          (2 • (0 : GlobalTheory.CechPic.Pic _) + GlobalTheory.CechPic.pull (liftU A U Y hY a) cU +
            GlobalTheory.CechPic.pull (liftU A U Y hY a⁻¹) cU - 2 • GlobalTheory.CechPic.pull (liftU A U Y hY 1) cU) := by abel
      _ = 0 := by rw [← s1, ← s2, sub_self]
  have el : l = liftU A U Y hY x ≫ A.left.homOfLE hW := by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, liftU_fac, hl]
  rw [map_nsmul, el, GlobalTheory.CechPic.pull_comp, ← hcU, two]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismCarriesPeriodPointBalaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationEndomorphism_carries_periodPoint_balanced : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := by
  first | exact @GlobalTheory.Mum.KeepsIota.main | exact GlobalTheory.Mum.KeepsIota.main | (intros; apply GlobalTheory.Mum.KeepsIota.main <;> assumption)
end

