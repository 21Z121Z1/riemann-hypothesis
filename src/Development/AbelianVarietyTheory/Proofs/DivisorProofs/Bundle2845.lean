import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImaginaryGeneratorCmType
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0691
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0714

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumInsertKilledCoordinateComp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.PsumCancel

theorem padd_comp_of_kill {S : Scheme.{0}} {B B₂ T : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B₂]
    [IsCommMonObj B₂] (p : B ⟶ B₂) [IsMonHom p] (a s : T ⟶ B) (ha : a ≫ p = toUnit T ≫ η[B₂]) :
    padd B a s ≫ p = s ≫ p := by
  unfold padd
  rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map, ha, lift_comp_one_left]

theorem psum_insert_zero_comp : ∀ (S : Scheme.{0}) (B B₂ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₂]
    [IsCommMonObj B₂] (p : B ⟶ B₂) (x : Fin 2 → (T ⟶ B)), IsMonHom p → x 0 ≫ p = toUnit T ≫ η[B₂] →
    ∀ I : Finset (Fin 2), psum B x I ≫ p = psum B x (insert 0 I) ≫ p := by
  intro S B B₂ T _ _ _ _ p x hp hx I
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl
  all_goals first
    | rw [Finset.insert_eq_of_mem (by decide)]
    | (simp only [psum, List.foldr_cons, List.foldr_nil, show (List.finRange 2) = [0, 1] by decide,
          List.filter_cons, List.filter_nil]
       try simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, decide_true, decide_false,
          Fin.isValue, zero_ne_one, one_ne_zero, or_true, true_or, or_false, if_true, if_false]
       try exact (padd_comp_of_kill p _ _ hx).symm)

end GlobalTheory.MumProd.PsumCancel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRelationPullbackMonomialConstants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodPull

open GlobalTheory.TChart

theorem gm_unitOn_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (u : Rˣ) (z : Sp R') :
    gm (𝟙 (Sp R')) z ⊤ (unitOn (Units.map f.toMonoidHom u)) =
      Units.map ((spMap f).stalkMap z).hom.toMonoidHom (gm (𝟙 (Sp R)) (spMap f z) ⊤ (unitOn u)) := by
  rw [← GlobalTheory.ConstFam.gm_comp_stalkMap (spMap f) (𝟙 _) z ⊤ trivial, Category.comp_id]
  apply Units.ext
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
  have e := congrArg (fun g => g.hom (u : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [e]
  simp [Scheme.Hom.appTop]
  rfl

theorem periods_pull : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.X) {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁) (κ₁ : W →+* V₁) (e : (Fin T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β₂ : (G2 B').left ⟶ (G2 D.P.A).left) (β₂' : (G2 B').left ⟶ (G2 T.B).left) (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (w₁ : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ), Function.Injective f₁ → PeriodRel D T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D') (Φ : D'.P.A.left ⟶ B'.left) (gΦ : IsGrpPullback D'.P.A B' (spMap f₂) Φ), (∀ a, (D'.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left) → ∀ (w : LB.Iso (abelian₂ D'.P.A D'.P.L) ((abelian₂ T.B T.M.L).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂'))), (∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D'.P.A).left) (z : Z) (J : (Z ⟶ T.B.left) → T.M.L.ι) (J₁ : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good T.M.L z J → Good D.P.L z J₁ → Good D'.P.L z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw hD.w (p ≫ lamφ D'.P.A I) z (J₁ ((p ≫ lamφ D'.P.A I) ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' (p ≫ lamφ D'.P.A I)) ^ lamε I) → ∀ a b : D'.X, ∃ k : (FractionRing V₂)ˣ, (k : FractionRing V₂) = ∏ i, algebraMap V₂ (FractionRing V₂) (s i) ^ ((n : ℤ) * ε i (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)) ∧ ∀ z J J', Good T.M.L z J → Good D'.P.L z J' → val (D'.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V₂).left) z ⊤ (unitOn k) * (lamVal w (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J' * val (T.τ₀ ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) a) ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
  intro n V _ _ D r e₀ o W _ _ _ T V₁ _ _ f₁ κ₁ e B' _ β₂ β₂' x w₁ q hf₁ hP V₂ _ _ f₂ fK I _ s ε hfK hq D' hD Φ gΦ hc w hw a b
  refine ⟨Units.map fK.toMonoidHom (q (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)),
    hq _ _, ?_⟩
  intro z J J' hJ hJ'
  set E := hD.xe.trans (e₀.symm.trans e.symm) with hE
  obtain ⟨κK, hκK, -⟩ := GlobalTheory.HalfBC.exists_kappa f₁ f₂ fK hfK hf₁
  let g₀ : (TK V₂).left ⟶ (TK V₁).left := spMap fK
  have sg : g₀ ≫ jK V₁ = jK V₂ ≫ spMap f₂ := GlobalTheory.HalfBC.gam_comm f₂ fK hfK
  choose J₁ hJ₀ using fun χ : (TK V₂).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  have hJ₁ : Good D.P.L z J₁ := hJ₀
  have cE : ∀ a, (e.trans e₀) (E a) = hD.xe a := fun a => by simp [E]
  have t₁ := hP κK hκK (E a) (E b) (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))
    (fun ψ => hJ (g₀ ≫ ψ)) (fun ψ => hJ₁ (g₀ ≫ ψ))
  rw [cE, cE] at t₁
  have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_mul _ _ _)))
  have n₁ : val (D.tau (hD.xe a) (hD.xe b)) (g₀ ≫ κK) z J₁ = Units.map (g₀.stalkMap z).hom.toMonoidHom
      (val (D.tau (hD.xe a) (hD.xe b)) κK (g₀ z) (fun ψ => J₁ (g₀ ≫ ψ))) :=
    Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ κK g₀ z J₁ hJ₁).2.2.1 _)
  have h0 : g₀ ≫ (TK V₁).hom ≫ spMap κ₁ = (TK V₂).hom ≫ spMap (f₂.comp κ₁) := by
    show g₀ ≫ jK V₁ ≫ spMap κ₁ = jK V₂ ≫ spMap (f₂.comp κ₁)
    rw [← Category.assoc, sg, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap']
  have n₀ : val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b))
        ((TK V₁).hom ≫ spMap κ₁) (g₀ z) (fun ψ => J (g₀ ≫ ψ))) := by
    rw [← h0]; exact Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ _ g₀ z J hJ).2.2.1 _)
  have nC : gm (𝟙 (TK V₂).left) z ⊤ (unitOn (Units.map fK.toMonoidHom (q (E a) (E b)))) =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (gm (𝟙 (TK V₁).left) (g₀ z) ⊤ (unitOn (q (E a) (E b)))) :=
    gm_unitOn_map fK _ z
  have ni : isoVal w₁ (g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left) z J J₁ =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (isoVal w₁ (lift (toUnit (TK V₁) ≫ x (E a))
        (toUnit (TK V₁) ≫ x (E b))).left (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))) := by
    unfold isoVal
    simp only [Category.assoc]
    refine GlobalTheory.ConstFam.gm_comp_stalkMap g₀ _ z _ ?_ _
    exact ⟨mem_pull.2 (Set.mem_iInter.2 fun I => hJ _), mem_pull.2 (Set.mem_iInter.2 fun I => hJ₁ _)⟩
  have hr : 𝟙 _ ≫ jK V₂ ≫ spMap (f₂.comp f₁) = (g₀ ≫ κK) ≫ jK V := by
    rw [Category.id_comp, Category.assoc, hκK, ← Category.assoc, sg, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap' f₁ f₂]
  have tv := GlobalTheory.ArcPull.tau_val hD (g₀ ≫ κK) (𝟙 _) hr hJ₁ hJ' a b
  have A : val (D.tau (hD.xe a) (hD.xe b)) (g₀ ≫ κK) z J₁ =
      gm (𝟙 (TK V₂).left) z ⊤ (unitOn (Units.map fK.toMonoidHom (q (E a) (E b)))) *
        (isoVal w₁ (g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left) z J J₁ *
          val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
    rw [n₁, t₂, nC, ni, n₀]
  have hx : ∀ χ, (toUnit (TK V₂) ≫ D'.c χ).left ≫ Φ = g₀ ≫ (toUnit (TK V₁) ≫ x (E χ)).left := fun χ => by
    show (jK V₂ ≫ (D'.c χ).left) ≫ Φ = spMap fK ≫ jK V₁ ≫ (x (E χ)).left
    rw [Category.assoc, hc, ← Category.assoc, ← sg, Category.assoc]
  have hPq : (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left ≫ GlobalTheory.HalfBC.sqOf gΦ =
      g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left := by
    have sq1 : GlobalTheory.HalfBC.sqOf gΦ ≫ (fst B' B').left = (fst D'.P.A D'.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_fst (pushPt gΦ.1.w (fst D'.P.A D'.P.A)) (pushPt gΦ.1.w (snd D'.P.A D'.P.A)))
    have sq2 : GlobalTheory.HalfBC.sqOf gΦ ≫ (snd B' B').left = (snd D'.P.A D'.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_snd (pushPt gΦ.1.w (fst D'.P.A D'.P.A)) (pushPt gΦ.1.w (snd D'.P.A D'.P.A)))
    apply pullback.hom_ext
    · show _ ≫ (fst B' B').left = _ ≫ (fst B' B').left
      rw [Category.assoc, sq1, ← Category.assoc, ← Over.comp_left, lift_fst,
        Category.assoc, ← Over.comp_left, lift_fst]
      exact hx a
    · show _ ≫ (snd B' B').left = _ ≫ (snd B' B').left
      rw [Category.assoc, sq2, ← Category.assoc, ← Over.comp_left, lift_snd,
        Category.assoc, ← Over.comp_left, lift_snd]
      exact hx b
  let h : ((TK V₂).left ⟶ D'.P.A.left) → ((TK V₂).left.presheaf.stalk z)ˣ :=
    fun q => gw hD.w q z (J₁ (q ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' q)
  have K := (hw _ (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J₁ J' hJ hJ₁ hJ').trans
    (congrArg₂ (· * ·) (congrArg (fun q => isoVal w₁ q z J J₁) hPq)
      (prod_lam (DVR.cP D' (TK V₂) a) (DVR.cP D' (TK V₂) b) h))
  rw [← DVR.cPoint_add] at K
  have c₀ : ∀ χ, GlobalTheory.ArcPull.om hD.w z J₁ J' (𝟙 _ ≫ D'.xK χ) = h (DVR.cP D' (TK V₂) χ).left := fun χ => by
    rw [Category.id_comp]; rfl
  have c₁ : GlobalTheory.ArcPull.om hD.w z J₁ J' (𝟙 _ ≫ (1 : TK V₂ ⟶ D'.P.A).left) = h (1 : TK V₂ ⟶ D'.P.A).left := by
    rw [Category.id_comp]; rfl
  rw [c₀, c₀, c₀, c₁] at tv
  rw [K]
  have F := tv.symm.trans A
  generalize val (D'.tau a b) (𝟙 _) z J' = X at F ⊢
  generalize h (DVR.cP D' (TK V₂) (a + b)).left = Y₀ at F ⊢
  generalize h (DVR.cP D' (TK V₂) a).left = Y₁ at F ⊢
  generalize h (DVR.cP D' (TK V₂) b).left = Y₂ at F ⊢
  generalize h (1 : TK V₂ ⟶ D'.P.A).left = Y₃ at F ⊢
  have F' := congrArg Additive.ofMul F
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at F' ⊢
  linear_combination (norm := abel) F'

end GlobalTheory.PeriodPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfPullbacksEqZeroArtinFibreProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ArtinPicGlue

theorem units_lift_of_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (hR : Nontrivial R₀ → IsLocalRing R) (g : R →+* R₀)
    (hg : Function.Surjective g) (r : R₀ˣ) : ∃ r' : Rˣ, g r' = r := by
  rcases subsingleton_or_nontrivial R₀ with h | h
  · exact ⟨1, Subsingleton.elim _ _⟩
  · haveI := hR h
    haveI : IsLocalHom g := IsLocalHom.of_surjective g hg
    obtain ⟨a, ha⟩ := hg r
    exact ⟨(isUnit_of_map_unit g a (ha ▸ r.isUnit)).unit, ha⟩

theorem units_lift_baseChange (P R₂ R₀ : CommRingCat.{0}) (f₂ : P ⟶ R₂) (g₂ : R₂ ⟶ R₀) (hR : Nontrivial R₀ → IsLocalRing R₂)
    (hg₂ : Function.Surjective g₂) (A : Over (Spec P)) [GrpObj A] (hA : IsAbelianScheme A) :
    Function.Surjective (Units.map (A ◁ (Over.homMk (Spec.map g₂) (by simp [Spec.map_comp]) :
      Over.mk (Spec.map (f₂ ≫ g₂)) ⟶ Over.mk (Spec.map f₂))).left.appTop.hom.toMonoidHom) := by
  have hpb : IsPullback (fst A (Over.mk (Spec.map (f₂ ≫ g₂)))).left (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left
      A.hom (Over.mk (Spec.map (f₂ ≫ g₂))).hom := IsPullback.of_hasPullback _ _
  obtain ⟨G, -, hAb, -⟩ := GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback P R₀ (f₂ ≫ g₂).hom A _ _ _ hpb
  letI := G
  have hbij := GlobalTheory.globalFns_holds _ _ (hAb hA)
  let e := RingEquiv.ofBijective _ hbij
  intro u
  let u₀ : Γ((Over.mk (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left).left, ⊤) := u.1
  have hu' : IsUnit (e.symm u₀) := by have := u.isUnit.map e.symm; exact this
  have hr : IsUnit ((Scheme.ΓSpecIso R₀).hom.hom (e.symm u₀)) := hu'.map _
  obtain ⟨r₂, hr₂⟩ := units_lift_of_surjective hR g₂.hom hg₂ hr.unit
  have hv : IsUnit ((snd A (Over.mk (Spec.map f₂))).left.appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂)) :=
    (r₂.isUnit.map (Scheme.ΓSpecIso R₂).inv.hom).map _
  refine ⟨hv.unit, Units.ext ?_⟩
  have hw : (A ◁ (Over.homMk (Spec.map g₂) (by simp [Spec.map_comp]) :
      Over.mk (Spec.map (f₂ ≫ g₂)) ⟶ Over.mk (Spec.map f₂))).left ≫ (snd A (Over.mk (Spec.map f₂))).left =
      (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left ≫ Spec.map g₂ := by
    rw [← Over.comp_left, whiskerLeft_snd]; rfl
  have hn := Scheme.ΓSpecIso_inv_naturality g₂
  have h1 : (Spec.map g₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂) =
      (Scheme.ΓSpecIso R₀).inv.hom (g₂.hom r₂) := by
    have := congrArg (fun φ => φ.hom (r₂ : R₂)) hn
    exact this.symm
  have key : (Spec.map g₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂) = e.symm u₀ := by
    rw [h1, hr₂, IsUnit.unit_spec]
    exact congrArg (fun φ => φ.hom (e.symm u₀)) (Scheme.ΓSpecIso R₀).hom_inv_id
  have h2 := congrArg (fun φ => φ.appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂)) hw
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h2
  simp only [Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe]
  exact h2.trans ((congrArg _ key).trans (e.apply_symm_apply u₀))

theorem surjective_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀}
    {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁) : Function.Surjective f₂ := by
  intro y
  obtain ⟨x, hx⟩ := hg₁ (g₂ y)
  have H := (Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))
  obtain ⟨p, -, hp⟩ := H.2.2 x y hx
  exact ⟨p, hp⟩

theorem pic_eq_zero_of_pull_eq_zero : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A : Over (Spec P)) [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A → IsPullback φ₁ A₁.hom A.hom (Spec.map f₁) → IsPullback φ₂ A₂.hom A.hom (Spec.map f₂) → ∀ c : GlobalTheory.CechPic.Pic A.left, GlobalTheory.CechPic.pull φ₁ c = 0 → GlobalTheory.CechPic.pull φ₂ c = 0 → c = 0 := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h hP _ hg₁ hg₂ A _ A₁ A₂ φ₁ φ₂ hA h₁ h₂ c hc₁ hc₂
  haveI : Flat A.hom := by have := hA.smooth; infer_instance
  have hf₂ := surjective_of_isPullback h hg₁
  have hloc : Nontrivial R₀ → IsLocalRing R₂ := fun _ => by
    haveI : Nontrivial R₂ := g₂.hom.domain_nontrivial
    exact IsLocalRing.of_surjective' f₂.hom hf₂
  let T : Over (Spec P) := Over.mk (𝟙 (Spec P))
  let T₁ : Over (Spec P) := Over.mk (Spec.map f₁)
  let T₂ : Over (Spec P) := Over.mk (Spec.map f₂)
  let T₀ : Over (Spec P) := Over.mk (Spec.map (f₂ ≫ g₂))
  let j₁ : T₁ ⟶ T := Over.homMk (Spec.map f₁) (by simp [T, T₁])
  let j₂ : T₂ ⟶ T := Over.homMk (Spec.map f₂) (by simp [T, T₂])
  let k₁ : T₀ ⟶ T₁ := Over.homMk (Spec.map g₁) (by simp only [T₀, T₁, Over.mk_hom]; rw [← Spec.map_comp, h.w])
  let k₂ : T₀ ⟶ T₂ := Over.homMk (Spec.map g₂) (by simp [T₀, T₂, Spec.map_comp])
  have hM : GlobalTheory.DualOpen.Milnor j₁.left j₂.left k₁.left k₂.left := GlobalTheory.DualOpen.Milnor.of_isPullback h hg₂
  have key := GlobalTheory.DualOpen.pic_eq_zero_of_milnor (Spec P) A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ hM
    (units_lift_baseChange P R₂ R₀ f₂ g₂ hloc hg₂ A hA)
  let s : A ⟶ A ⊗ T := lift (𝟙 A) (Over.homMk A.hom (by simp [T]))
  have hs : s.left ≫ (fst A T).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst]; rfl
  have hc : c = GlobalTheory.CechPic.pull s.left (GlobalTheory.CechPic.pull (fst A T).left c) := by
    rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id]
  rw [hc, key (GlobalTheory.CechPic.pull (fst A T).left c) ?_ ?_, map_zero]
  · rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, whiskerLeft_fst]
    have hm := h₁.lift_fst (fst A T₁).left (snd A T₁).left ((Over.w (fst A T₁)).trans (Over.w (snd A T₁)).symm)
    rw [← hm, GlobalTheory.CechPic.pull_comp, hc₁, map_zero]
  · rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, whiskerLeft_fst]
    have hm := h₂.lift_fst (fst A T₂).left (snd A T₂).left ((Over.w (fst A T₂)).trans (Over.w (snd A T₂)).symm)
    rw [← hm, GlobalTheory.CechPic.pull_comp, hc₂, map_zero]

end GlobalTheory.ArtinPicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingModelPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel.EigenForm

theorem exists_eigenForm (R : Subring ℂ) [IsPrincipalIdealRing R] {g : ℕ} {V : Type} [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin g) R V) (ψ : V →ₗ[R] (Fin g → ℂ)) (hψ : LinearIndependent ℂ fun k ↦ ψ (b k))
    {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ) (hT : ∀ a v j, ψ (T a v) j = lam a j * ψ v j)
    (hsep : ∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k)
    (hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) (i : Fin g) :
    ∃ (e : V →ₗ[R] R) (c : ℂ), c ≠ 0 ∧ (∀ v, ((e v : R) : ℂ) = c * ψ v i) ∧
      ∀ (e' : V →ₗ[R] R) (c' : ℂ), (∀ v, ((e' v : R) : ℂ) = c' * ψ v i) → ∃ t : R, e' = t • e :=
  GlobalTheory.T.simultaneous_eigenbasis_integral R b ψ hψ T lam hT hsep hK i

open ReciprocityTheory.ChartRestriction.G.Chart (isTan_iff) in

theorem exists_diffEquiv {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) {L : LB X.A.left}
    (u : HolUnif X.A L (Module.finrank ℚ F)) :
    ∃ D : X.Lie ≃ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ), ∀ (v : X.Lie) W, u.IsDiff W v.hom ↔ W = D v := by
  obtain ⟨h1, h2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  choose Df hDf using fun v : X.Lie ↦ (h1 v.hom v.isTangent).exists
  have huq : ∀ (v : X.Lie) W, u.IsDiff W v.hom ↔ W = Df v := fun v W ↦
    ⟨fun h ↦ (h1 v.hom v.isTangent).unique h (hDf v), fun h ↦ h ▸ hDf v⟩
  let Dl : X.Lie →ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ) :=
    { toFun := Df
      map_add' := fun v w ↦ by
        refine ((huq (v + w) _).1 ?_).symm
        rw [Serre.Lie.hom_add]
        exact GlobalTheory.UnifLieBasis.isDiff_add u ((isTan_iff _).2 v.isTangent) ((isTan_iff _).2 w.isTangent) (hDf v) (hDf w)
      map_smul' := fun c v ↦ by
        have hs : u.IsDiff (c • Df v) (c • v).hom := by
          have := GlobalTheory.UnifLieBasis.isDiff_smul u ((isTan_iff _).2 v.isTangent) (hDf v) c
          convert this using 1
          rfl
        rw [RingHom.id_apply]
        exact ((huq (c • v) _).1 hs).symm }
  have hinj : Function.Injective Dl := by
    intro v w hvw
    have e0 : Dl v = Df v := rfl
    have e1 : u.IsDiff (Df v) w.hom := (huq w (Df v)).2 (hvw.symm.trans rfl).symm
    have e2 : v.hom = w.hom := (h2 (Df v)).unique (y₁ := v.hom) (y₂ := w.hom) ⟨v.isTangent, hDf v⟩ ⟨w.isTangent, e1⟩
    exact Serre.Lie.ext e2
  have hsurj : Function.Surjective Dl := by
    intro W
    obtain ⟨v₀, ⟨ht, hd⟩, -⟩ := h2 W
    refine ⟨Serre.Lie.mk X.rm v₀ ht, ?_⟩
    have hd' : u.IsDiff W (Serre.Lie.mk X.rm v₀ ht).hom := hd
    exact ((huq _ W).1 hd').symm
  exact ⟨LinearEquiv.ofBijective Dl ⟨hinj, hsurj⟩, fun v W ↦ huq v W⟩

theorem isDiff_act {E : Type} [Field E] [NumberField E] {I : Type} {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
    {z : I → ℂ} {X : Obj (FR E) 𝔠 (Sp ℂ)} (U : Unif φ L z X) (a : 𝓞 (FR E)) (v : X.Lie)
    (W : Fin (Module.finrank ℚ (FR E)) → ℂ) (h : U.u.IsDiff W v.hom) :
    U.u.IsDiff (fun j ↦ φ (U.e j) ((a : FR E) : E) * W j) (a • v).hom := by
  haveI := X.rm.hom a
  let Fm : (Fin (Module.finrank ℚ (FR E)) → ℂ) →L[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ φ (U.e j) ((a : FR E) : E) • ContinuousLinearMap.proj j
  have hF : ∀ w, Fm w = fun j ↦ φ (U.e j) ((a : FR E) : E) * w j := fun w ↦ by
    ext j; simp [Fm]
  have := GlobalTheory.UnifLieBasis.isDiff_comp U.u (X.rm.act a) Fm (fun w ↦ by rw [hF]; exact U.act a w) v.isTangent h
  rw [hF] at this
  exact this

theorem lieCorr_act {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} (σ : R →+* R') {b : Sp R' ⟶ Sp R} {p : X'.A.left ⟶ X.A.left}
    (hp : X'.IsPullBy X b p) (a : 𝓞 F) {v : X.Lie} {v' : X'.Lie} (h : Obj.LieCorr σ p v v') :
    Obj.LieCorr σ p (a • v) (a • v') := by
  unfold Obj.LieCorr at h ⊢
  change (v'.hom ≫ X'.rm.act a).left ≫ p = _ ≫ (v.hom ≫ X.rm.act a).left
  rw [Over.comp_left, Over.comp_left, Category.assoc, hp.act a, ← Category.assoc, h, Category.assoc]

end GlobalTheory.LatModel.EigenForm

namespace GlobalTheory.LatModel.EigenForm

theorem exists_periodGen : GlobalTheory.Published.AbelianDeRham →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ), IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (L : Set E) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left),
      X.IsPullBy X₀ (spMap R.subtype) p → ∀ i : I, ∃ (e : X₀.Lie →ₗ[R] R) (a : ℂ), a ≠ 0 ∧ IsPeriodGen X₀ U p i e a ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e := by
  intro _ E _ _ _ I _ φ hφ l _ lam 𝔠 R hR X₀ X L U p hp i
  classical
  obtain ⟨hdvr, -, -, hKR⟩ := hR
  haveI := hdvr
  obtain ⟨eq, hcorr⟩ := GlobalTheory.T.lie_algebra_base_change_iso (R := R) (R' := ℂ) (X := X₀) (X' := X) (φ := p) hp
  obtain ⟨D, hD⟩ := exists_diffEquiv X U.u
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X₀
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R X₀.Lie := Module.free_of_flat_of_isLocalRing
  have hdim : Module.finrank R X₀.Lie = Module.finrank ℚ (FR E) := by
    have := hrk (IsLocalRing.closedPoint R)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  let b : Module.Basis (Fin (Module.finrank ℚ (FR E))) R X₀.Lie :=
    (Module.finBasis R X₀.Lie).reindex (finCongr hdim)
  let ψ : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun v ↦ D (eq (1 ⊗ₜ v))
      map_add' := fun v w ↦ by simp [TensorProduct.tmul_add]
      map_smul' := fun r v ↦ by
        have e1 : (1 : ℂ) ⊗ₜ[R] (r • v) = (r : ℂ) • ((1 : ℂ) ⊗ₜ[R] v) := by
          rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
          rfl
        simp only [e1, map_smul, RingHom.id_apply]
        rfl }
  have hψ : ∀ v, ψ v = D (eq (1 ⊗ₜ v)) := fun v ↦ rfl
  let T : 𝓞 (FR E) → X₀.Lie →ₗ[R] X₀.Lie := fun a ↦
    { toFun := fun v ↦ a • v
      map_add' := smul_add a
      map_smul' := fun r v ↦ smul_comm a r v }
  let lamv : 𝓞 (FR E) → Fin (Module.finrank ℚ (FR E)) → ℂ := fun a j ↦ φ (U.e j) ((a : FR E) : E)
  have hT : ∀ a v j, ψ (T a v) j = lamv a j * ψ v j := by
    intro a v j
    have c0 : Obj.LieCorr R.subtype p v (eq (1 ⊗ₜ v)) := (hcorr v _).2 rfl
    have c1 := lieCorr_act R.subtype hp a c0
    have e1 : a • eq (1 ⊗ₜ v) = eq (1 ⊗ₜ (a • v)) := (hcorr _ _).1 c1
    have d0 : U.u.IsDiff (D (eq (1 ⊗ₜ v))) (eq (1 ⊗ₜ v)).hom := (hD _ _).2 rfl
    have d1 := isDiff_act U a _ _ d0
    have e2 := (hD _ _).1 d1
    change D (eq (1 ⊗ₜ (a • v))) j = _
    rw [← e1, ← e2]
    rfl
  have hsep : ∀ j k, j ≠ k → ∃ a, lamv a j ≠ lamv a k := by
    intro j k hjk
    by_contra hc
    push_neg at hc
    exact hjk (U.e.injective (GlobalTheory.SignGen.cm_restrict_inj E I φ hφ (U.e j) (U.e k) fun a ↦ hc a))
  have hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lamv a j * y = x := fun a j ↦ hKR (φ (U.e j)) _
  have hli : LinearIndependent ℂ fun k ↦ ψ (b k) := by
    convert ((b.baseChange ℂ).map (eq.trans D)).linearIndependent using 1
    ext k : 1
    simp [hψ, Module.Basis.baseChange_apply]
  obtain ⟨e, c, hc, he, huniq⟩ := exists_eigenForm R b ψ hli T lamv hT hsep hK (U.e.symm i)
  refine ⟨e, c, hc, ?_, ?_⟩
  · intro v v' W hvv hW
    rw [(hcorr v v').1 hvv] at hW
    rw [(hD _ W).1 hW, he v]
    rfl
  · intro e' c' h'
    exact huniq e' c' fun v ↦ h' v (eq (1 ⊗ₜ v)) (ψ v) ((hcorr _ _).2 rfl) ((hD _ _).2 rfl)

end GlobalTheory.LatModel.EigenForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormOverDvrPrimeToLStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_form_over_dvr_prime_to_l : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F)
    (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
    (∀ n : ℕ, n.Coprime l → IsUnit (n : R)) → ∀ (X : Obj F 𝔠 (Sp R)) (c₀ : 𝔠.elt), (c₀ : F) ≠ 0 →
    (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 F), n.Coprime l ∧ n • c = t • c₀) →
    ∀ ψ : LinearMap.BilinForm R (HdR X.A), GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c₀) ψ → Function.Bijective ψ := by
  first | exact @GlobalTheory.PolPrimeTo.perfect_of_primeTo | exact GlobalTheory.PolPrimeTo.perfect_of_primeTo | (intros; apply GlobalTheory.PolPrimeTo.perfect_of_primeTo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianVarietyPullbackAffineOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_abelian_variety_pullback_affine_open : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (U : X₁.M.Z.Opens) (P' : PolAV (Sp (X₁.M.ringOn U))) (P₀ : PolAV (Sp X₁.Ω₁)) (a : P₀.A.left ⟶ X₁.ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsAffineOpen U → (U : Set X₁.M.Z).Nonempty → IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a → IsGrpPullback P₀.A P'.A (spMap (X₁.M.ringOn U).val.toRingHom) a' → LBIso P₀.L (X₁.ρ.P.L.pull a) → LBIso P₀.L (P'.L.pull a') → ∃ pt' : X₁.S.Gam → (baseOver (Sp (X₁.M.ringOn U)) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp (X₁.M.ringOn U)) (z : Over.mk x ⟶ P'.A), z ^ (X₁.S.r * X₁.S.N) = 1 → ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp (X₁.M.ringOn U))) ≫ pt' c = z) ∧ (∀ x y (c : (X₁.M.ringOn U)ˣ), (c : (X₁.M.ringOn U)) = algebraMap X₁.o₁ (X₁.M.ringOn U) (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)) → WeilIs P'.A P'.L (X₁.S.r * X₁.S.N : ℕ) (pt' x) (pt' y) (unitOn c)) ∧ (∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt' x).left) := by
  first | exact @GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart | exact GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart | (intros; apply GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOfGroupSchemeIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPolarisation_of_groupScheme_iso : ∀ (S : Scheme.{0}) (P : PolAV S) (B : Over S) [GrpObj B] (e : B ≅ P.A), IsMonHom e.hom → ∀ L : LB B.left, L.IsLB → LBIso L (P.L.pull e.hom.left) → IsProper B.hom ∧ SmoothOfRelativeDimension P.g B.hom ∧ Sym B L ∧ RelAmple B L ∧ KTriv B L := by
  first | exact @GlobalTheory.polarisation_of_iso | exact GlobalTheory.polarisation_of_iso | (intros; apply GlobalTheory.polarisation_of_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEvenCoordinatesNegDifferByUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiEven_coordinates_neg_differ_by_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.PsiEven →
    ∀ (y : D.X) (x x' : (FractionRing R)ˣ), IsPsiCoord D y x → IsPsiCoord D (-y) x' →
      ∃ u : Rˣ, (x' : FractionRing R) = algebraMap R (FractionRing R) u * x := by
  first | exact @GlobalTheory.PsiEvenCoordUnit.main | exact GlobalTheory.PsiEvenCoordUnit.main | (intros; apply GlobalTheory.PsiEvenCoordUnit.main <;> assumption)
end

