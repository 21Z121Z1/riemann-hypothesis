import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusFlat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3198
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3199
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3200

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateOfMumfordBundleMatch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem pull_inv_cls {R : Type} [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) :
    pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
  obtain ⟨U, hU, t, ht⟩ := P.sym (IsLocalRing.closedPoint R)
  obtain rfl : U = ⊤ := DVR.eq_top_of_closedPoint_mem U hU
  have h := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 ⟨t, ht⟩
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul, pull_comp] at h
  obtain ⟨m, hm⟩ : ∃ m : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme, m ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨P.A.left.topIso.inv, P.A.left.topIso.inv_hom_id⟩
  have h' := congrArg (pull m) h
  rw [map_add, map_neg, map_zero, ← pull_comp m, ← pull_comp m, hm, pull_id, pull_id, add_neg_eq_zero] at h'
  exact h'

theorem pull_one_eq_zero {R : Type} [CommRing R] [IsLocalRing R] {G Y : Over (Sp R)} [GrpObj G] (d : Pic G.left) :
    pull (1 : Y ⟶ G).left d = 0 := by
  have e : (1 : Y ⟶ G) = toUnit Y ≫ η[G] := rfl
  rw [e, Over.comp_left, pull_comp, GlobalTheory.DualOpen.pic_sp_local_eq_zero R (pull η[G].left d), map_zero]

theorem exists_translate_of_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D₀ D : DegPre R)
  (β : D₀.P.A ≅ D.P.A), IsMonHom β.hom →
  (∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
      ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
    wΛ.IsGen) →
  ∃ b : 𝟙_ (Over (Sp R)) ⟶ D.P.A, padd D.P.A b b = η[D.P.A] ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β.hom b) GlobalTheory.MumCmp.twε), w.IsGen := by
  intro R _ _ _ _ D₀ D β hβ hw
  have := D.P.isAb.comm
  have := D₀.P.isAb.comm
  have hL₀ := D₀.P.isLB
  have hL := D.P.isLB
  set c₀ := cls D₀.P.L hL₀ with hc₀
  set c := cls D.P.L hL with hc
  have hd : IsDual D.P.A D.P.A (abelian₂ D.P.A D.P.L) :=
    CompanionTheory.PfDual.kTrivDual R D.P.A D.P.g D.P.isAb D.P.smoothDim D.P.L hL D.P.ktriv
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := hd.isLB
  have e : ∀ (Y : Over (Sp R)) (a t : Y ⟶ D.P.A), evc hΛ a t = lam c a t := fun Y a t ↦ by
    rw [evc, show cls _ hΛ = lam c (fst D.P.A D.P.A) (snd D.P.A D.P.A) from
      cls_cube_two hL _ _ hΛ, pull_lam, lift_fst, lift_snd]
  have l₁ : ∀ (Y : Over (Sp R)) (a a' t : Y ⟶ D.P.A), lam c (a * a') t = lam c a t + lam c a' t :=
    fun Y a a' t ↦ by
      rw [← e, ← e, ← e]
      exact (isAdditive_iff hΛ).1 hd.additive Y a a' t
  have l₂ : ∀ (Y : Over (Sp R)) (a t t' : Y ⟶ D.P.A), lam c a (t * t') = lam c a t + lam c a t' :=
    fun Y a t t' ↦ by rw [lam_comm, l₁, lam_comm _ t, lam_comm _ t']

  obtain ⟨wΛ, hwΛ⟩ := hw
  have hΛ₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := LB.isLB_linComb hL₀ _ _
  have eΛ : lam c₀ (fst D₀.P.A D₀.P.A) (snd D₀.P.A D₀.P.A) =
      lam c (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) := by
    have h := (cls_eq_iff hΛ₀ (pull_isLB hΛ _)).2 ⟨wΛ, hwΛ⟩
    have h₁ : cls _ hΛ₀ = lam c₀ (fst D₀.P.A D₀.P.A) (snd D₀.P.A D₀.P.A) := cls_cube_two hL₀ _ _ hΛ₀
    have h₂ : cls _ hΛ = lam c (fst D.P.A D.P.A) (snd D.P.A D.P.A) := cls_cube_two hL _ _ hΛ
    rw [← h₁, h, cls_pull hΛ, h₂, pull_lam, lift_fst, lift_snd]
  have s₁ : ∀ (Y : Over (Sp R)) (u v : Y ⟶ D₀.P.A), lam c₀ u v = lam c (u ≫ β.hom) (v ≫ β.hom) := fun Y u v ↦ by
    have h := congrArg (pull (lift u v).left) eΛ
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h

  have Fadd : ∀ (Y : Over (Sp R)) (a a' : Y ⟶ D.P.A),
      pull ((a * a') ≫ β.inv).left c₀ - pull (a * a').left c =
        (pull (a ≫ β.inv).left c₀ - pull a.left c) + (pull (a' ≫ β.inv).left c₀ - pull a'.left c) := by
    intro Y a a'
    have h := s₁ Y (a ≫ β.inv) (a' ≫ β.inv)
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, lam, pull_one_eq_zero, add_zero] at h
    rw [MonObj.mul_comp, ← sub_eq_zero]
    have h' := sub_eq_zero.2 h
    convert h' using 1
    abel
  let N : LB (D.P.A ⊗ 𝟙_ (Over (Sp R))).left :=
    tens (D₀.P.L.pull (fst D.P.A (𝟙_ (Over (Sp R))) ≫ β.inv).left)
      (dual (D.P.L.pull (fst D.P.A (𝟙_ (Over (Sp R)))).left))
  have hN : N.IsLB := isLB_tens (pull_isLB hL₀ _) (isLB_dual (pull_isLB hL _))
  have clsN : cls N hN = pull (fst D.P.A (𝟙_ (Over (Sp R))) ≫ β.inv).left c₀ -
      pull (fst D.P.A (𝟙_ (Over (Sp R)))).left c := by
    rw [show cls N hN = _ from cls_tens (pull_isLB hL₀ _) (isLB_dual (pull_isLB hL _)) hN,
      cls_dual (pull_isLB hL _), cls_pull hL₀, cls_pull hL, sub_eq_add_neg]
  have evN : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A) (t : Y ⟶ 𝟙_ (Over (Sp R))),
      evc hN a t = pull (a ≫ β.inv).left c₀ - pull a.left c := by
    intro Y a t
    rw [evc, clsN, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, lift_fst_assoc, lift_fst]
  have hadd : IsAdditive N := (isAdditive_iff hN).2 fun Y a a' t ↦ by rw [evN, evN, evN, Fadd]
  obtain ⟨b, hb, -⟩ := hd.univ _ N hN hadd
  have eb := (cls_eq_iff hN (pull_isLB hΛ _)).2 hb
  have key : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A),
      pull (a ≫ β.inv).left c₀ - pull a.left c = lam c a (toUnit Y ≫ b) := by
    intro Y a
    have h : evc hN a (toUnit Y) = evc hΛ a (toUnit Y ≫ b) := by
      have h := congrArg (pull (lift a (toUnit Y)).left) eb
      rw [cls_pull hΛ] at h
      change evc hN a (toUnit Y) = pull (lift a (toUnit Y)).left
        (evc hΛ (fst D.P.A (𝟙_ (Over (Sp R)))) (snd D.P.A (𝟙_ (Over (Sp R))) ≫ b)) at h
      rw [pull_evc, lift_fst, lift_snd_assoc] at h
      exact h
    rw [← evN Y a (toUnit Y), h, e]
  refine ⟨b, ?_, ?_⟩
  ·
    have sym₀ : pull (GrpObj.inv : D₀.P.A ⟶ D₀.P.A).left c₀ = c₀ := pull_inv_cls D₀.P
    have sym : pull (GrpObj.inv : D.P.A ⟶ D.P.A).left c = c := pull_inv_cls D.P
    have odd : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A), lam c a (toUnit Y ≫ b) + lam c a (toUnit Y ≫ b) = 0 := by
      intro Y a
      have ia : a⁻¹ = a ≫ GrpObj.inv := rfl
      have ia' : (a ≫ β.inv)⁻¹ = (a ≫ β.inv) ≫ GrpObj.inv := rfl
      have h₁ : lam c a⁻¹ (toUnit Y ≫ b) = lam c a (toUnit Y ≫ b) := by
        rw [← key, ← key, GrpObj.inv_comp, ia, ia']
        simp only [Over.comp_left, pull_comp, sym₀, sym]
      have h₂ : lam c (a⁻¹ * a) (toUnit Y ≫ b) = 0 := by rw [inv_mul_cancel, lam_one_left]
      rw [l₁, h₁] at h₂
      exact h₂
    have two : b * b = 1 := by
      refine hd.eq_one (b * b) ((triv_ev_iff hΛ _ _).2 ?_)
      have hs : snd D.P.A (𝟙_ (Over (Sp R))) = toUnit _ := toUnit_unique _ _
      rw [e, hs, MonObj.comp_mul, l₂, odd]
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by
      rw [show (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = toUnit _ ≫ η[D.P.A] from rfl,
        toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    exact two.trans e₁
  ·
    have hC : (LB.LinComb D.P.L (twφ D₀ D β.hom b) twε).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff hL₀ hC).1 ?_
    have h := key D₀.P.A β.hom
    rw [Iso.hom_inv_id, Over.id_left, pull_id, sub_eq_iff_eq_add] at h
    have e₁ : padd D.P.A β.hom (toUnit D₀.P.A ≫ b) = β.hom * (toUnit D₀.P.A ≫ b) := rfl
    have e₂ : toUnit D₀.P.A ≫ η[D.P.A] = 1 := rfl
    rw [cls_linComb hL, Fin.sum_univ_three]
    simp only [twφ, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, one_smul, neg_smul, e₁, e₂]
    rw [← hc, ← hc₀, h, lam]
    abel

end GlobalTheory.MumCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFormsFunctionalAbelianBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_forms_functional_abelian_base_change : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (A' : Over (Sp R')) (φ : A'.left ⟶ A.left), IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) → ∀ (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (l : GlobForm (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R'), ∃! ψ : Form (A'.hom ≫ 𝟙 (Sp R')) →ₗ[R'] R', (∀ f, cmpForm (A'.hom ≫ 𝟙 (Sp R')) f = 0 → ψ f = 0) ∧ ∀ f, ψ (m.pullForm f) = l (GlobalTheory.LieDual.glob (A.hom ≫ 𝟙 (Sp R)) f) := by
  first | exact @GlobalTheory.BaseChangeForm.existsUnique_functional | exact GlobalTheory.BaseChangeForm.existsUnique_functional | (intros; apply GlobalTheory.BaseChangeForm.existsUnique_functional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterNormStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_hecke_character_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∃ (U : Subgroup (Neutral.B1.Ideles E)) (ψ : Neutral.B1.Ideles E →* ℂˣ), IsOpen (U : Set (Neutral.B1.Ideles E)) ∧
      Continuous ψ ∧ (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (k : Eˣ) (b : Neutral.B1.Ideles (maximalRealSubfield E)) (u : Neutral.B1.Ideles E), u ∈ GlobalTheory.MuExist.nsUnits E →
        Neutral.B1.diagUnits E k * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b * u ∈ U →
        (GlobalTheory.GalOfCusp.quadChar E).1 b =
          ψ (Neutral.B1.diagUnits E k * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b * u) := by
  first | exact @GlobalTheory.ConsEta.exists_open_subgroup_eta_consistent | exact GlobalTheory.ConsEta.exists_open_subgroup_eta_consistent | (intros; apply GlobalTheory.ConsEta.exists_open_subgroup_eta_consistent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulCardLeDegreeAmpleSemiPositiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorial_mul_card_le_degree_ample_semiPositive : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → P.L.SemiPos D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  first | exact @GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam | exact GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam | (intros; apply GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreThetaConstantsAlgebraicOverCompleteAlgCloseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_thetaConstants_algebraic_over_completeAlgClosed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (n : ℕ), n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → ∀ (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) → ∀ (B : PolAV (Sp (Kb W))) (b : B.A.left ⟶ A'.A.left), IsGrpPullback B.A A'.A (spMap (algebraMap (FractionRing W) (Kb W))) b → LBIso B.L (A'.L.pull b) → ∀ j : ℕ, 1 ≤ j → ∃ (C : Type) (_ : Field C) (jC : Kb W →+* C) (Ix : Type) (x : Ix → (baseOver (Sp (Kb W)) ⟶ B.A)) (v : Ix → Kb R), (∀ z : baseOver (Sp (Kb W)) ⟶ B.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧ (∀ i, x i ^ ((n ^ j) ^ 2) = 1) ∧ IsThetaPt B (n ^ j) (fun i => (Over.homMk (spMap jC) (Category.comp_id _) : Over.mk (spMap jC) ⟶ baseOver (Sp (Kb W))) ≫ x i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (jC (e₀ (v i)))) := by
  first | exact @GlobalTheory.Mum.FibreTheta.theta_consts_algebraic | exact GlobalTheory.Mum.FibreTheta.theta_consts_algebraic | (intros; apply GlobalTheory.Mum.FibreTheta.theta_consts_algebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetRationalProductOfLocalLevels
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.ClassFinLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPart : UA E n →* finU E n where
  toFun u := ⟨⟨finGL E n (GeneralLinearGroup.map (pFin E) u.1), GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin u)⟩,
    pInf_finGL _⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' a b := Subtype.ext (Subtype.ext (by simp))

theorem finPart_fin (k : finU E n) : finPart (k : UA E n) = k :=
  Subtype.ext (Subtype.ext (GlobalTheory.DefU.ClassFin.finGL_pFin k))

theorem finPart_inf {x : UA E n} (hx : x ∈ infU E n) : finPart x = 1 := by
  have h : GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  refine Subtype.ext (Subtype.ext ?_)
  change finGL E n (GeneralLinearGroup.map (pFin E) x.1) = 1
  rw [h, map_one]

theorem finPart_rat {γ : UA E n} (hγ : γ ∈ ratU E n) : finPart γ ∈ ratFinU E n := by
  obtain ⟨γ₀, hγ₀'⟩ := hγ
  have hγ₀ : ratGL E n γ₀ = γ.1 := hγ₀'
  have hg : cT (conjAd E) γ.1.val * 1 * γ.1.val = 1 := γ.2
  rw [← hγ₀, mul_one] at hg
  have hv : (ratGL E n γ₀).val = γ₀.val.map (algebraMap E (Ad E)) := rfl
  rw [hv, GlobalTheory.DefU.ClassFin.cT_map (algebraMap E (Ad E)) (IsCMField.complexConj E).toRingEquiv.toRingHom (conjAd E)
    (fun y => (conjAd_algebraMap y).symm), ← Matrix.map_mul] at hg
  have hU : γ₀ ∈ UE E n := by
    change cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * 1 * γ₀.val = 1
    rw [mul_one]
    ext i j
    have := congrFun₂ hg i j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    rw [Matrix.one_apply]
    haveI hnt : Nontrivial (Ad E) := show Nontrivial (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E) from inferInstance
    apply (algebraMap E (Ad E)).injective
    rw [this]
    split_ifs <;> simp
  refine ⟨γ₀, hU, ?_⟩
  change finGL E n (ratF E n γ₀) = finGL E n (GeneralLinearGroup.map (pFin E) γ.1)
  rw [← hγ₀]
  rfl

theorem finite_doubleCoset_of_isOpen (K : Subgroup (finU E n)) (hK : IsOpen (K : Set (finU E n))) :
    Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (K : Set (finU E n))) := by
  obtain ⟨T, hT⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hK
  let φ : T → DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (K : Set (finU E n)) :=
    fun s => DoubleCoset.mk _ _ (finPart (s : UA E n))
  refine Finite.of_surjective φ fun q => ?_
  obtain ⟨g, rfl⟩ : ∃ g, DoubleCoset.mk _ _ g = q := ⟨q.out, DoubleCoset.out_eq' _ _ q⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, e⟩ := hT (g : UA E n)
  refine ⟨⟨s, hs⟩, ?_⟩
  have hg : g = finPart γ * finPart s * k := by
    have := congrArg finPart e
    rw [finPart_fin, map_mul, map_mul, map_mul, finPart_inf hx, mul_one, finPart_fin] at this
    exact this
  show DoubleCoset.mk _ _ (finPart (s : UA E n)) = DoubleCoset.mk _ _ g
  rw [hg]
  exact (DoubleCoset.eq _ _ _ _).2 ⟨finPart γ, finPart_rat hγ, k, hk, rfl⟩

end GlobalTheory.BCT.ClassFinLev

open GlobalTheory.BCT.ClassFinLev in

theorem GlobalTheory.BCT.finite_doubleCoset_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (globLev S K' : Set (finU E n))) := by
  intro E _ _ _ hE n _ S _ K' hK
  exact finite_doubleCoset_of_isOpen _ (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hE n S K' hK)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTestDivisorsKltLcPencilBoundaries
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem finite_test_divisors : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G D₀ : CartierDiv X), η ≠ 0 → 0 < m → ∃ S : Set (DivOver p), S.Finite ∧ ∀ (x : X) (g f : X.functionFieldˣ) (c : ℚ), G.IsEqn x g → D₀.IsEqn x f → ((∀ E ∈ S, E.Through x → -1 < discrep E η m g - c * E.ord f) → ∀ E : DivOver p, E.Through x → -1 < discrep E η m g - c * E.ord f) ∧ ((∀ E ∈ S, E.Through x → -1 ≤ discrep E η m g - c * E.ord f) → ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g - c * E.ord f) := by
  intro hP X _ _ p n hproj hn η m G D₀ hη hm
  haveI : LocallyOfFiniteType p := by
    obtain ⟨h1, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj
    infer_instance
  obtain ⟨Y, hYi, hYn, s, hsd, B, hsm, hprop, hbij, hfin, hη', hchart, hG, hD, hK⟩ :=
    GlobalTheory.T.exists_resolution_divisors_topForm_normalCrossings hP X p n hproj hn η G D₀ hη
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth (s ≫ p)
  have hnY : topologicalKrullDim Y = n := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth Y (s ≫ p) n
  set S : Set (DivOver p) := ⋃ v ∈ {v : Y | v ∈ B ∧ Order.coheight v = 1},
    {E : DivOver p | ∀ f, f ∈ E.ring ↔ RegAt v (functionFieldMap s f)} with hSdef
  refine ⟨S, hfin.biUnion fun v _ => Set.Subsingleton.finite fun E hE E₂ hE₂ => ?_, ?_⟩
  · have hr : E.ring = E₂.ring := SetLike.ext fun f => (hE f).trans (hE₂ f).symm
    cases E; cases E₂
    cases hr
    rfl
  intro x g f c hg hf
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm

  have core : ∀ E : DivOver p, E.Through x → ∃ (ι : Type) (_ : Fintype ι) (Es : ι → DivOver p) (t : ι → ℤ),
      (∀ j, Es j ∈ S ∧ (Es j).Through x ∧ 0 ≤ t j) ∧
      ((∀ j, t j = 0) → (1 : ℚ) ≤ 1 + (discrep E η m g - c * E.ord f)) ∧
      ((∃ j, t j ≠ 0) → ∑ j, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) ≤
        1 + (discrep E η m g - c * E.ord f)) := by
    intro E hE
    obtain ⟨E', hE'⟩ := GlobalTheory.T.exists_primeDivisor_over_source_of_birational p s hbij E
    obtain ⟨y, hyx, hy⟩ := GlobalTheory.T.exists_centre_of_valuationSubring_proper_dominant s E'.ring x fun a ha => (hE' a).1 (hE a ha)
    obtain ⟨U, hyU, z, J, w, u, hc⟩ := hchart y
    have hgen := isFreeGen_formOf (gen_mem hyU) hc.frame
    set ω0 := formOf U (gen_mem hyU) (dOn (s ≫ p) z) with hω0
    have h0 : ω0 ≠ 0 := fun h =>
      one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
    obtain ⟨h, hh⟩ := hgen.2 (ratPull p s n η)
    have hh0 : h ≠ 0 := fun e => hη' (by simp [← hh, e])
    set H : Y.functionFieldˣ := Units.mk0 h hh0 with hH
    have hHη : ratPull p s n η = (H : Y.functionField) • ω0 := hh.symm

    have hgy : G.IsEqn (s y) g := by
      obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
      exact hgV _ (hyx.mem_open V.isOpen hV)
    have hfy : D₀.IsEqn (s y) f := by
      obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
      exact hfV _ (hyx.mem_open V.isOpen hV)

    have hoff : ∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j : J, v ≠ w j) → v ∉ B := by
      intro v hv h1 hne hvB
      obtain ⟨j, hj, rfl⟩ := (hc.mem v hv h1).1 hvB
      exact hne ⟨j, hj⟩ rfl
    have hHv : ∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j : J, v ≠ w j) →
        Scheme.ord (H : Y.functionField) v = 0 := by
      intro v hv h1 hne
      obtain ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) h1
      have e1 := hK v F h1 (hoff v hv h1 hne) hF
      rw [hHη, F.formOrd_smul hnY h0, DivOver.formOrd_formOf_eq_zero (hv.mem_open U.isOpen hyU) hF hc.frame,
        add_zero, hF.ord_eq] at e1
      exact e1
    have hM := fun φ hφ => GlobalTheory.T.primeDivisorOver_ord_eq_sum_adaptedMonomial E' y hy (ι := J) (fun j => w j) (fun j => u j)
      (fun a b e => Subtype.ext (hc.inj a.2 b.2 e)) (fun j => hc.spec j j.2) (fun j => hc.coheight j j.2)
      (fun j => hc.ord_self j j.2) (fun j v hv _ hne => hc.ord_other j j.2 v hv hne) φ hφ
    have hMH := hM H hHv
    have hMg := hM (fnPull s g) fun v hv h1 hne => hG y v g hv h1 (hoff v hv h1 hne) hgy
    have hMf := hM (fnPull s f) fun v hv h1 hne => hD y v f hv h1 (hoff v hv h1 hne) hfy

    have hFj : ∀ j : J, ∃ F : DivOver (s ≫ p), F.IsAt (w j) := fun j =>
      DivOver.exists_isAt_of_coheight_eq_one (hc.coheight j j.2)
    choose F hF using hFj
    have hEj : ∀ j : J, ∃ Ej : DivOver p, DivOver.Over s (F j) Ej := fun j => GlobalTheory.T.exists_primeDivisor_over_target_of_birational p s hbij (F j)
    choose Es hEs using hEj
    have hA := GlobalTheory.T.birational_primeDivisor_orders_functions_topForms p n hn s hbij E E' hE'
    have hAj := fun j => GlobalTheory.T.birational_primeDivisor_orders_functions_topForms p n hn s hbij (Es j) (F j) (hEs j)

    set t : J → ℤ := fun j => E'.ord (u j) with ht
    have htn : ∀ j, 0 ≤ t j := fun j => by
      refine (E'.ord_nonneg_iff _).2 (hy _ ?_)
      rw [hc.val j j.2]
      exact regAt_fnOf hyU _ _
    set Fo := E'.formOrd ω0 with hFo
    have hlog : ∑ j : J, t j - 1 ≤ Fo :=
      GlobalTheory.T.sum_ord_sub_one_le_ord_wedgeDifferentials hnY E' hyU hy z h0 (J := J) Subtype.val Subtype.val_injective (fun j => u j)
        fun j => hc.val j j.2
    have hnn : 0 ≤ Fo := DivOver.formOrd_formOf_nonneg hnY hyU hy (dOn (s ≫ p) z) h0
    have eFE : E.formOrd η = ∑ j : J, Scheme.ord (H : Y.functionField) (w j) * t j + Fo := by
      rw [← hA.2 η hη, hHη, E'.formOrd_smul hnY h0, hMH]
    have egE : E.ord g = ∑ j : J, Scheme.ord (fnPull s g : Y.functionField) (w j) * t j := by
      rw [← hA.1 g, hMg]
    have efE : E.ord f = ∑ j : J, Scheme.ord (fnPull s f : Y.functionField) (w j) * t j := by
      rw [← hA.1 f, hMf]
    have eFj : ∀ j, (Es j).formOrd η = Scheme.ord (H : Y.functionField) (w j) := fun j => by
      rw [← (hAj j).2 η hη, hHη, (F j).formOrd_smul hnY h0,
        DivOver.formOrd_formOf_eq_zero ((hc.spec j j.2).mem_open U.isOpen hyU) (hF j) hc.frame, add_zero,
        (hF j).ord_eq]
    have egj : ∀ j, (Es j).ord g = Scheme.ord (fnPull s g : Y.functionField) (w j) := fun j => by
      rw [← (hAj j).1 g, (hF j).ord_eq]
    have efj : ∀ j, (Es j).ord f = Scheme.ord (fnPull s f : Y.functionField) (w j) := fun j => by
      rw [← (hAj j).1 f, (hF j).ord_eq]
    have key : ∑ j : J, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) =
        1 + (discrep E η m g - c * E.ord f) - (1 + Fo - ∑ j : J, (t j : ℚ)) := by
      simp only [discrep, eFE, egE, efE, eFj, egj, efj]
      push_cast
      rw [Finset.sum_div, Finset.mul_sum]
      have : ∀ j : J, (1 + ((Scheme.ord (H : Y.functionField) (w j) : ℚ) -
          (Scheme.ord (fnPull s g : Y.functionField) (w j) : ℚ) / m -
          c * (Scheme.ord (fnPull s f : Y.functionField) (w j) : ℚ))) * (t j : ℚ) =
          (t j : ℚ) + (Scheme.ord (H : Y.functionField) (w j) : ℚ) * t j -
          (Scheme.ord (fnPull s g : Y.functionField) (w j) : ℚ) * t j / m -
          c * ((Scheme.ord (fnPull s f : Y.functionField) (w j) : ℚ) * t j) := fun j => by ring
      rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      ring
    refine ⟨J, inferInstance, Es, t, fun j => ⟨?_, ?_, htn j⟩, fun h0' => ?_, fun ⟨j0, hj0⟩ => ?_⟩
    · refine Set.mem_biUnion (x := w j) ⟨(hc.mem _ (hc.spec j j.2) (hc.coheight j j.2)).2 ⟨j, j.2, rfl⟩,
        hc.coheight j j.2⟩ fun a => (hEs j a).trans (hF j _)
    · intro a ha
      refine (hEs j a).2 ((hF j _).2 (regAt_of_specializes (hc.spec j j.2) ?_))
      exact GlobalTheory.Cartier.PullDominant.regAt_map s (regAt_of_specializes hyx ha)
    · have hs0 : ∑ j : J, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [h0' j]; simp
      have ht0 : ∑ j : J, (t j : ℚ) = 0 := Finset.sum_eq_zero fun j _ => by rw [h0' j]; simp
      have : (0 : ℚ) ≤ Fo := by exact_mod_cast hnn
      linarith
    · have h1 : 1 ≤ ∑ j : J, t j := by
        have := Finset.single_le_sum (f := t) (fun j _ => htn j) (Finset.mem_univ j0)
        have : 1 ≤ t j0 := by have := htn j0; omega
        omega
      have h1q : (1 : ℚ) ≤ ∑ j : J, (t j : ℚ) := by exact_mod_cast h1
      have hlq : (∑ j : J, (t j : ℚ)) - 1 ≤ Fo := by exact_mod_cast hlog
      rw [key]
      linarith
  refine ⟨fun hS E hE => ?_, fun hS E hE => ?_⟩
  · obtain ⟨ι, _, Es, t, hEs, h0, h1⟩ := core E hE
    by_cases hall : ∀ j, t j = 0
    · have := h0 hall
      linarith
    · push_neg at hall
      have hpos : 0 < ∑ j, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) := by
        obtain ⟨j0, hj0⟩ := hall
        refine Finset.sum_pos' (fun j _ => mul_nonneg ?_ ?_) ⟨j0, Finset.mem_univ _, mul_pos ?_ ?_⟩
        · have := hS (Es j) (hEs j).1 (hEs j).2.1; linarith
        · exact_mod_cast (hEs j).2.2
        · have := hS (Es j0) (hEs j0).1 (hEs j0).2.1; linarith
        · have : 0 < t j0 := lt_of_le_of_ne (hEs j0).2.2 (Ne.symm hj0)
          exact_mod_cast this
      have := h1 hall
      linarith
  · obtain ⟨ι, _, Es, t, hEs, h0, h1⟩ := core E hE
    by_cases hall : ∀ j, t j = 0
    · have := h0 hall
      linarith
    · push_neg at hall
      have hnn : 0 ≤ ∑ j, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) := by
        refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ ?_
        · have := hS (Es j) (hEs j).1 (hEs j).2.1; linarith
        · exact_mod_cast (hEs j).2.2
      have := h1 hall
      linarith

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosedStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstChern_real_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ L : HermLB p, (hX.atlas σ).IsRealForm 1 (fld _ (c1F hX σ L)) ∧ (hX.atlas σ).del (fld _ (c1F hX σ L)) = 0 ∧ (hX.atlas σ).dbar (fld _ (c1F hX σ L)) = 0 := by
  first | exact @GlobalTheory.LineForm.FirstChern.c1F_isRealForm_closed | exact GlobalTheory.LineForm.FirstChern.c1F_isRealForm_closed | (intros; apply GlobalTheory.LineForm.FirstChern.c1F_isRealForm_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingEssFiniteTypeIntStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalFibre_isRegularRing_essFiniteType_int : ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Algebra.EssFiniteType ℤ R] [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  first | exact @GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int | exact GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int | (intros; apply GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int <;> assumption)
end

