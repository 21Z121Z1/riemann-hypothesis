import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoEqRosatiGeneratorMulComparison
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem lam_eq_ros_mul_cmp : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (inc : D₀.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D₀.P.A) [IsMonHom inc] [IsMonHom pr] (ea fa ea' : D'.P.A ⟶ D'.P.A) [IsMonHom ea] [IsMonHom fa] [IsMonHom ea'], pr ≫ inc = ea → ∀ (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa) : G2 D₀.P.A ⟶ G2 D'.P.A).left)), w.IsGen → (∀ (T : Over (Sp R)) (y : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι) (J' : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D'.P.L z J → Good D₀.P.L z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ D₀.P.A) y).left z J J' = 1) → ∀ (ur : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A ea ea') rosatiε)), ur.IsGen → (∀ (T : Over (Sp R)) (y : T ⟶ D'.P.A) (z : T.left) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val ur (lift (1 : T ⟶ D'.P.A) y).left z J = 1) → ∀ (χ' : D'.X) (χ : D₀.X) (q : 𝟙_ (Over (Sp R)) ⟶ D'.P.A), D₀.c χ ≫ inc ≫ fa = q → D'.c χ' = q ≫ ea' → ∀ (u : LB.Gen (CmpLB D' D₀ pr χ' χ)), Nrm u → ∀ (T : Over (Sp R)) (x : T ⟶ D'.P.A) (z : T.left) (J : (T.left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → GlobalTheory.PolDeg.lamVal w (lift (x ≫ pr) (toUnit T ≫ D₀.c χ)).left z (rl J) (rr J) = val ur (lift x (toUnit T ≫ q)).left z (rl J) * val u x.left z J := by
  intro R _ _ D₀ D' inc pr _ _ ea fa ea' _ _ _ hea w hw hw1 ur hur hur1 χ' χ q hq hq' u hu T x z J hJ
  have hN : (JN D' D₀).IsLB := jn_isLB D' D₀
  have h₁ := isPart_inl D'.P.L D₀.P.L
  have h₂ := isPart_inr D'.P.L D₀.P.L
  obtain ⟨t, ht, htv⟩ := exists_gen_of_iso h₁ h₂ w hw
  let m : D'.P.A.left ⟶ (G2 D₀.P.A).left := (lift pr (toUnit _ ≫ D₀.c χ)).left
  let n : D'.P.A.left ⟶ (G2 D'.P.A).left := (lift (𝟙 _) (toUnit _ ≫ q)).left
  let t₁ := LB.pullGen _ _ _ t m
  let t₂ := LB.mulGen _ _ _ _ _ (h₁.gen (LB.pullGen _ _ _ ur n)) u
  have hG := GlobalTheory.globalFns_holds
  have key := gen_unique' hN (u := t₁) (u' := t₂) ?fe D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (DVR.pullGen_isGen _ _ _ _ ht m) (DVR.mulGen_isGen _ _ _ _ _ _ _ (h₁.gen_isGen (DVR.pullGen_isGen _ _ _ _ hur n)) hu.1)
    ?ev T.left x.left z J hJ
  · have e₁ : x.left ≫ m = (lift (x ≫ pr) (toUnit T ≫ D₀.c χ)).left := by
      rw [← Over.comp_left, comp_lift, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
    have e₂ : x.left ≫ n = (lift x (toUnit T ≫ q)).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
    rw [val_pull hJ, htv _ _ z J hJ, val_mul hJ, h₁.val_gen _ _ z hJ, val_pull (h₁.good hJ), e₁, e₂] at key
    exact key
  case fe =>
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have mβ : m ≫ (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa)).left =
        (lift ea (toUnit _ ≫ q)).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, hea, Category.assoc, hq]
    have A1 : ∏ a₁ : ULift (Finset (Fin 2)), h (m ≫ (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa)).left ≫
        (psum D'.P.A (x2 D'.P.A) a₁.down).left ≫ coprod.inl) ^ ((-1 : ℤ) ^ (2 - a₁.down.card)) =
        h ((ea * (toUnit _ ≫ q)).left ≫ coprod.inl) * (h (ea.left ≫ coprod.inl))⁻¹ *
          (h ((toUnit _ ≫ q).left ≫ coprod.inl))⁻¹ * h ((1 : D'.P.A ⟶ D'.P.A).left ≫ coprod.inl) := by
      refine (Finset.prod_congr rfl fun k _ => ?_).trans
        (GlobalTheory.PrimCocycle.prod_lam ea (toUnit _ ≫ q) (fun g => h (g ≫ coprod.inl)))
      rw [← Category.assoc, ← Category.assoc, mβ]
    have A2 : ∏ a₂ : ULift (Finset (Fin 2)), h (m ≫ (psum D₀.P.A (x2 D₀.P.A) a₂.down).left ≫ coprod.inr) ^
        (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((pr * (toUnit _ ≫ D₀.c χ)).left ≫ coprod.inr) * (h (pr.left ≫ coprod.inr))⁻¹ *
          (h ((toUnit _ ≫ D₀.c χ).left ≫ coprod.inr))⁻¹ * h ((1 : D'.P.A ⟶ D₀.P.A).left ≫ coprod.inr))⁻¹ := by
      rw [← GlobalTheory.PrimCocycle.prod_lam pr (toUnit _ ≫ D₀.c χ) (fun g => h (g ≫ coprod.inr)), ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    have A3 := prod_ros ea ea' (𝟙 D'.P.A) (toUnit _ ≫ q) (fun g => h (g ≫ coprod.inl))
    beta_reduce at A3
    rw [A1, A2, A3, Fin.prod_univ_four, Fin.prod_univ_four]
    clear * - h hq'
    have pm : ∀ {X Y : Over (Sp R)} [GrpObj Y] (a b : X ⟶ Y), padd Y a b = a * b := fun _ _ => rfl
    simp only [DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, pm, ← Hom.one_def, hq', Category.id_comp,
      Category.assoc]
    simp only [zpow_one, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  case ev =>
    intro y I hI
    have o₀ : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have o' : (1 : 𝟙_ (Over (Sp R)) ⟶ D'.P.A) = η[D'.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have e₁ : eSec D'.P.A ≫ m = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) (toUnit _ ≫ D₀.c χ)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, IsMonHom.one_hom, ← Category.assoc,
        toUnit_unique (η[D'.P.A] ≫ toUnit _) (toUnit _), o₀]
    have e₂ : eSec D'.P.A ≫ n = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D'.P.A) (toUnit _ ≫ q)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D'.P.A] ≫ toUnit _) (toUnit _), o']
    rw [val_pull hI, htv _ _ y I hI, val_mul hI, h₁.val_gen _ _ y hI, val_pull (h₁.good hI), e₁, e₂]
    have a := hw1 (𝟙_ _) (toUnit _ ≫ D₀.c χ) y (rl I) (rr I) (h₁.good hI) (h₂.good hI)
    have b := hur1 (𝟙_ _) (toUnit _ ≫ q) y (rl I) (h₁.good hI)
    have c := hu.2 _ (𝟙 _) y I hI
    rw [Category.id_comp] at c
    rw [show isoVal w (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) (toUnit _ ≫ D₀.c χ)).left y (rl I) (rr I) = 1 from a, b, c,
      _root_.one_mul]

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomPropertiesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordTensorData_matrixAction_ringHom_properties : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W), (∀ a, IsMonHom (T.act a)) ∧ T.act 1 = 𝟙 _ ∧ (∀ a b, T.act (a * b) = T.act b ≫ T.act a) ∧ ∀ a b, T.act (a + b) = padd D'.P.A (T.act a) (T.act b) := by
  first | exact @GlobalTheory.Mum.TensAct.act_ring | exact GlobalTheory.Mum.TensAct.act_ring | (intros; apply GlobalTheory.Mum.TensAct.act_ring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesDegreeAdicFiltrationMulLeStatement
section
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le : ∀ (σ R : Type) [CommRing R] (I : Ideal R) (j k : ℕ), filt (σ := σ) I j * filt I k ≤ filt I (j + k) := by
  first | exact @GlobalTheory.FormalOrigin.Extend.filt_mul_filt_le | exact GlobalTheory.FormalOrigin.Extend.filt_mul_filt_le | (intros; apply GlobalTheory.FormalOrigin.Extend.filt_mul_filt_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenEmbeddingCompOfSumMapCompStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nearOpenEmbedding_comp_of_sumMap_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ φ : (Over.pullback p).obj G' ⟶ (Over.pullback p').obj G', Desc.sum N p hp ≫ φ = Desc.sum N p' hp' → Desc.emb N p hp ≫ φ = Desc.emb N p' hp' := by
  first | exact @GlobalTheory.Mum.DescFix.emb_comp_of_sum_comp | exact GlobalTheory.Mum.DescFix.emb_comp_of_sum_comp | (intros; apply GlobalTheory.Mum.DescFix.emb_comp_of_sum_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenPullbackToSelfProductSurjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nearOpenPullbackToSelfProduct_surjective : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → ∀ (G' : Over S) [GrpObj G'] (N : Near π G'), Surjective (Desc.UT N).hom := by
  first | exact @GlobalTheory.Mum.Desc.surjective_UT_hom | exact GlobalTheory.Mum.Desc.surjective_UT_hom | (intros; apply GlobalTheory.Mum.Desc.surjective_UT_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenSumEqEmbeddingDescendedMultiplication
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Desc.toS N p hp ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

theorem toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Desc.toS N p hp ≫ pullback.snd _ _ = pullback.snd _ _ ≫ p := pullback.lift_snd _ _ _

theorem embL_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.emb N p hp).left ≫ pullback.fst G.hom p = Desc.toS N p hp ≫ N.u := pullback.lift_fst _ _ _

theorem embL_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.emb N p hp).left ≫ pullback.snd G.hom p = pullback.snd _ _ := pullback.lift_snd _ _ _

theorem pairU_fst' (N : Near π G) :
    pairU N ≫ (fst N.U N.U).left = (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ := by
  show (lift (fstU N) (sndU N) ≫ fst _ _).left = _
  rw [lift_fst]; rfl

theorem pairU_snd' (N : Near π G) :
    pairU N ≫ (snd N.U N.U).left = (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ := by
  show (lift (fstU N) (sndU N) ≫ snd _ _).left = _
  rw [lift_snd]; rfl

theorem fst_hom' (N : Near π G) :
    (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.snd N.U.hom (pullback.fst π π ≫ π) = (Desc.UT N ⊗ Desc.UT N).hom :=
  Over.w (fst (Desc.UT N) (Desc.UT N))

theorem snd_hom' (N : Near π G) :
    (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.snd N.U.hom (pullback.fst π π ≫ π) = (Desc.UT N ⊗ Desc.UT N).hom :=
  Over.w (snd (Desc.UT N) (Desc.UT N))

theorem mT_fst' (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) : mT N V m hm ≫ pullback.fst _ _ = (pairU N ∣_ V) ≫ m :=
  pullback.lift_fst _ _ _

theorem mT_snd' (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) :
    mT N V m hm ≫ pullback.snd _ _ = (VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.DescKP

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem fst_toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.fst _ _ =
      (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ :=
  (Category.assoc _ _ _).trans (congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_fst' N p hp))

theorem snd_toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.fst _ _ =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ :=
  (Category.assoc _ _ _).trans (congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_fst' N p hp))

theorem fst_toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.snd _ _ = (Desc.UT N ⊗ Desc.UT N).hom ≫ p :=
  (Category.assoc _ _ _).trans ((congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_snd' N p hp)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (fst_hom' N))))

theorem snd_toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.snd _ _ = (Desc.UT N ⊗ Desc.UT N).hom ≫ p :=
  (Category.assoc _ _ _).trans ((congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_snd' N p hp)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (snd_hom' N))))

theorem fst_toS_u' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ N.u =
      (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.emb N p hp).left ≫ pullback.fst G.hom p :=
  (Category.assoc _ _ _).trans (congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (embL_fst' N p hp).symm)

theorem snd_toS_u' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ N.u =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ (Desc.emb N p hp).left ≫ pullback.fst G.hom p :=
  (Category.assoc _ _ _).trans (congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (embL_fst' N p hp).symm)

end GlobalTheory.Mum.DescKP

namespace GlobalTheory.Mum.DescKP

theorem sum_eq_mT_emb : ∀ {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G] (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left) (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom), (∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G), N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left → N.Pt s (v ≫ m) (x * y).left) → ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π), (DescKP.VT N V).ι ≫ (Desc.sum N p hp).left = DescKP.mT N V m hm ≫ (Desc.emb N p hp).left := by
  intro R _ _ S π G _ N V m hm law p hp
  let T0 : Over (pullback π π) := Over.mk ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)
  let ι0 : T0 ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk (VT N V).ι rfl
  let a : T0 ⟶ (Over.pullback p).obj G := ι0 ≫ fst _ _ ≫ Desc.emb N p hp
  let b : T0 ⟶ (Over.pullback p).obj G := ι0 ≫ snd _ _ ≫ Desc.emb N p hp
  have hab : ι0 ≫ Desc.sum N p hp = a * b := by rw [Desc.sum, comp_mul]
  have wpt : ∀ c : T0 ⟶ (Over.pullback p).obj G, (c.left ≫ pullback.fst G.hom p) ≫ G.hom = T0.hom ≫ p := by
    intro c
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ p) (Over.w c)
  let x : Over.mk (T0.hom ≫ p) ⟶ G := Over.homMk (a.left ≫ pullback.fst G.hom p) (wpt a)
  let y : Over.mk (T0.hom ≫ p) ⟶ G := Over.homMk (b.left ≫ pullback.fst G.hom p) (wpt b)
  have hxy : (x * y).left = (a * b).left ≫ pullback.fst G.hom p :=
    (isGrpPullback_pullback G p).2 T0 a b x y rfl rfl
  have e : (pairU N ∣_ V) ≫ V.ι = (VT N V).ι ≫ pairU N := morphismRestrict_ι _ _
  have e' : ∀ {Z : Scheme.{0}} (h : (N.U ⊗ N.U).left ⟶ Z), (pairU N ∣_ V) ≫ V.ι ≫ h = (VT N V).ι ≫ pairU N ≫ h :=
    fun h => by rw [← Category.assoc, e, Category.assoc]
  have ptx : N.Pt (T0.hom ≫ p) ((pairU N ∣_ V) ≫ V.ι ≫ (fst N.U N.U).left) x.left := by
    refine ⟨(VT N V).ι ≫ (fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp, ?_, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) ((fst_toS_fst' N p hp).trans (pairU_fst' N).symm)).trans (e' _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (fst_toS_snd' N p hp)).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (fst_toS_u' N p hp)).trans (Category.assoc _ _ _).symm)
  have pty : N.Pt (T0.hom ≫ p) ((pairU N ∣_ V) ≫ V.ι ≫ (snd N.U N.U).left) y.left := by
    refine ⟨(VT N V).ι ≫ (snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp, ?_, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) ((snd_toS_fst' N p hp).trans (pairU_snd' N).symm)).trans (e' _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (snd_toS_snd' N p hp)).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (snd_toS_u' N p hp)).trans (Category.assoc _ _ _).symm)
  obtain ⟨x₀, h₁, h₂, h₃⟩ := law (VT N V).toScheme (pairU N ∣_ V) (T0.hom ≫ p) x y ptx pty
  have hx₀ : x₀ = mT N V m hm ≫ Desc.toS N p hp := by
    apply pullback.hom_ext
    · exact h₁.trans (((Category.assoc _ _ _).trans ((congrArg (mT N V m hm ≫ ·) (toS_fst' N p hp)).trans (mT_fst' N V m hm))).symm)
    · exact h₂.trans (((Category.assoc _ _ _).trans ((congrArg (mT N V m hm ≫ ·) (toS_snd' N p hp)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (mT_snd' N V m hm))))).symm)
  apply pullback.hom_ext
  · rw [Category.assoc (mT N V m hm), embL_fst']
    refine (?_ : _ = (mT N V m hm ≫ Desc.toS N p hp) ≫ N.u).trans (Category.assoc _ _ _)
    rw [← hx₀, h₃, hxy, ← hab]
    rfl
  · have w : (Desc.sum N p hp).left ≫ pullback.snd G.hom p = (Desc.UT N ⊗ Desc.UT N).hom := Over.w _
    rw [Category.assoc, w, Category.assoc, embL_snd', mT_snd']

end GlobalTheory.Mum.DescKP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefShiftOfGeneratedAtCharZeroPointsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_shift_of_generated_at_charZero_points : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (m N : ℕ) (s : Fin N → (M.pow m).B.Sec), 1 ≤ m → (∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.SemiPos D → NefFib M → ∃ t : ℝ, 0 ≤ t ∧ (M.shift (fun _ => t) fun _ => rfl).IsNef D := by
  first | exact @GlobalTheory.NefOfGen.nef_of_gen | exact GlobalTheory.NefOfGen.nef_of_gen | (intros; apply GlobalTheory.NefOfGen.nef_of_gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame KSIso)

theorem isUnit_ger_of_ev {Z : Scheme.{0}} {V : Z.Opens} (a : Γ(Z, V)) (y : Z) (hy : y ∈ V)
    (h : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), GlobalTheory.FlagMod.ev z V hz a ≠ 0) :
    IsUnit (ger y hy a) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
  have hWV : W ≤ V := hWV
  replace hW : IsAffineOpen W := hW
  let p := hW.primeIdealOf ⟨y, hyW⟩
  have hne := h p.asIdeal.ResidueField (spMap (algebraMap Γ(Z, W) p.asIdeal.ResidueField) ≫ GlobalTheory.FlagMod.tau hW)
    (GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le hW hWV))
  rw [← GlobalTheory.FlagMod.ev_res _ hWV (GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le hW le_rfl)),
    GlobalTheory.FlagMod.ev_spMap_tau] at hne
  have hnm : resG Z hWV a ∈ p.asIdeal.primeCompl := fun hm => hne (Ideal.algebraMap_residueField_eq_zero.2 hm)
  letI := Z.presheaf.algebra_section_stalk (⟨y, hyW⟩ : W)
  have := hW.isLocalization_stalk ⟨y, hyW⟩
  have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk y) p.asIdeal (resG Z hWV a)).2 hnm
  rw [← ger_resG hWV y hyW]
  exact hu

theorem canId_nonempty : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F))
    (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)),
    (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) →
    Nonempty (CanId M) := by
  intro hdR E _ _ _ H Dw l Xo c Y X Z M hKS
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth (dimFlag Dw) M.str
  haveI : IsReduced M.X := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isReduced_of_smooth M.str
  have hBLB : (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).IsLB :=
    LB.isLB_div M.K.isLB (LB.isLB_pull ((common₀ X Z).isLB _) M.σ)
  have hloc : ∀ t : M.K.bundle.ι × X.F.J, ∃ a : Γ(M.X, ksOpen M t.1 t.2), ∀ (K : Type) [Field K]
      (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ ksOpen M t.1 t.2), KSRel M t.1 t.2 z (GlobalTheory.FlagMod.ev z _ hz a) := fun t =>
    GlobalTheory.FlagMod.glue_field (ksOpen M t.1 t.2) (fun L _ z x => KSRel M t.1 t.2 z x)
      (fun L _ z hz x y hx hy => (GlobalTheory.T.kodairaSpencer_coordinate_unique_ne_zero M hKS t.1 t.2 L z hz).1 x y hx hy)
      (fun W hW hle => GlobalTheory.T.exists_regular_kodairaSpencerCoordinate_affine_off_boundary M hdR hKS t.1 t.2 W hW hle)
  choose a ha using hloc
  have cover : ∀ y ∈ M.off, ∃ t : M.K.bundle.ι × X.F.J, y ∈ ksOpen M t.1 t.2 := by
    intro y hy
    obtain ⟨i, hi⟩ := exists_chart M.K.isLB y
    obtain ⟨k, hk⟩ := ((common₀ X Z).pull M.σ).cover y
    exact ⟨(i, k), hy, hi, (((common₀ X Z).pull M.σ).mem _ k y).2 hk⟩
  have rule : ∀ (y : M.X) (t t' : M.K.bundle.ι × X.F.J) (h : y ∈ ksOpen M t.1 t.2) (h' : y ∈ ksOpen M t'.1 t'.2),
      ger y h (a t) = (tr (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) y (t.1, flagIdx M _ t.2)
        (t'.1, flagIdx M _ t'.2) : _) * ger y h' (a t') := by
    intro y t t' h h'
    have hle : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤
        (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (t.1, flagIdx M _ t.2) ⊓
          (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (t'.1, flagIdx M _ t'.2) :=
      fun q hq => ⟨hq.1.2, hq.2.2⟩
    rw [val_tr _ y (hle ⟨h, h'⟩)]
    have e : resG M.X (inf_le_left : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤ _) (a t) =
        resG M.X hle ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g (t.1, flagIdx M _ t.2)
          (t'.1, flagIdx M _ t'.2)).val * resG M.X inf_le_right (a t') := by
      refine GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => ?_
      have h1 := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
      have h2 := GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz
      have hg := GlobalTheory.FlagMod.le_preimage_mono hle hz
      rw [map_mul, GlobalTheory.FlagMod.ev_res z _ hz h1, GlobalTheory.FlagMod.ev_res z _ hz h2, GlobalTheory.FlagMod.ev_res z _ hz hg]
      exact GlobalTheory.T.kodairaSpencerCoords_two_charts_transition M hKS t.1 t'.1 t.2 t'.2 L z h1 h2 hg _ _ (ha t L z h1) (ha t' L z h2)
    have := congrArg (ger y (⟨h, h'⟩ : y ∈ ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2)) e
    have e1 := ger_resG (inf_le_left : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤ _) y ⟨h, h'⟩ (a t)
    have e2 := ger_resG (inf_le_right : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤ _) y ⟨h, h'⟩ (a t')
    have e3 := ger_resG hle y ⟨h, h'⟩ ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g (t.1, flagIdx M _ t.2)
          (t'.1, flagIdx M _ t'.2)).val
    rw [map_mul, e1, e2, e3] at this
    exact this
  obtain ⟨f, hf⟩ := H0.exists_of_germs (p := M.str) (O := M.off) hBLB
    (fun t : M.K.bundle.ι × X.F.J => ksOpen M t.1 t.2) (fun t => (t.1, flagIdx M _ t.2))
    (fun t => inf_le_left) (fun t => inf_le_right) cover a rule
  have hloc' : ∀ i k, f.loc (i, flagIdx M _ k) = a (i, k) := fun i k =>
    fun_ext_ger fun y hy => (H0.germ_apply _ y hy.1 hy.2 f).symm.trans (hf (i, k) y hy)
  refine ⟨⟨f, nowhereZero_of_exists fun y hy => ?_, (isKS_iff_ksRel M f).2 @fun K _ z i k ho hi => ?_⟩⟩
  · obtain ⟨t, ht⟩ := cover y hy
    refine ⟨(t.1, flagIdx M _ t.2), ht.2, ?_⟩
    rw [hf t y ht]
    exact isUnit_ger_of_ev (a t) y ht fun L _ z hz => (GlobalTheory.T.kodairaSpencer_coordinate_unique_ne_zero M hKS t.1 t.2 L z hz).2 _ (ha t L z hz)
  · have hk : KSRel M i k z (GlobalTheory.FlagMod.ev z (ksOpen M i k) (GlobalTheory.FlagMod.le_preimage_inf ho hi) (a (i, k))) :=
      ha (i, k) K z (GlobalTheory.FlagMod.le_preimage_inf ho hi)
    have e : H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi f =
        GlobalTheory.FlagMod.ev z (ksOpen M i k) (GlobalTheory.FlagMod.le_preimage_inf ho hi) (a (i, k)) := by
      rw [← hloc' i k]
      rfl
    rw [e]
    exact @hk

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLink
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM

namespace GlobalTheory.GenDeg

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {O : Type} [CommRing O] {β : O →+* i₀.c.F}

structure Link (Z : LocM.Mdl Y i₀) (T : Model (Xo i₀.l) i₀.c β) : Type 1 where

  τ : (Y Z.i).X ⟶ (Y i₀).X

  mu : SABMap (Y Z.i).t (Y i₀).t τ

  trans : IsTrans i₀ Z.i τ mu

  h : gen T ⟶ (Y i₀).X

  tg : SAB H (gen T)

  m₁ : SABMap tg T.t (genι T)

  m₂ : SABMap tg (Y i₀).t h

  jQ_h : T.jQ ≫ h = (Y i₀).j

  h_s : h ≫ (Y i₀).s = genStr T ≫ spMap (i₀.c.V W).subtype

variable {Z : LocM.Mdl Y i₀} {T : Model (Xo i₀.l) i₀.c β}

def Link.Match (L : Link Z T) {F : Type} [Field F] {e : F ≃+* i₀.c.F} (C : FlagCpt T e) {k : Type} [Field k]
    (w : Sp k ⟶ Z.X) (q : Sp k ⟶ C.Y.X) : Prop :=
  ∃ (x : Sp k ⟶ (Xo i₀.l).XF i₀.c) (u : Vecs Dw (Y Z.i).t k) (φ : i₀.c.F →+* k) (g : EigFrame T φ ((q ≫ C.π) ≫ genι T)),
    w ≫ Z.π ≫ L.τ = x ≫ (Y i₀).j ∧ q ≫ C.π = x ≫ T.jQ ∧ x ≫ pullback.snd _ _ = spMap φ ∧ Z.FlagAt w u ∧ C.Carries q g ∧
    ∀ σ j, ∃ v : Sp (DualNumber k) ⟶ L.tg.G.left,
      IsTanAtG L.tg (q ≫ C.π) v ∧ v ≫ L.m₁.φ = g.v σ j ∧ v ≫ L.m₂.φ = u σ j ≫ L.mu.φ

def FlagExt (z : admitted Y i₀) : Prop :=
  ∀ x : z.Z.X, z.Z.inQ x → ∃ (f : z.Z.i.c.F →+* z.Z.X.presheaf.stalk x) (u : Vecs Dw (Y z.Z.i).t (z.Z.X.presheaf.stalk x)),
    z.Z.X.fromSpecStalk x ≫ z.Z.s = spMap (f.comp (z.Z.i.c.V W).subtype) ∧
    LocM.IsFrame (Y z.Z.i).t f (z.Z.X.fromSpecStalk x ≫ z.Z.π) u ∧
    ∀ (ℓ : Letter Dw) (h : letterOf Dw (.inl (ℓ.1, ℓ.2)) = some ℓ) (i : Fin (z.line false _ ℓ h).L.n),
      x ∈ (z.line false _ ℓ h).L.U i → ∃ ε : (z.Z.X.presheaf.stalk x)ˣ,
        ∀ (k : Type) [Field k] (ψ : z.Z.X.presheaf.stalk x →+* k) (a : Fin z.Z.m) (φ : Γ(z.Z.X, (z.Z.U a).1) →+* k),
          Function.Injective ψ → spMap ψ ≫ z.Z.X.fromSpecStalk x = spMap φ ≫ z.Z.chart a →
          ∃ cf : Fin (Dw.mult ℓ.1) → k,
            cf ℓ.2 = ψ ε * valF (spMap φ ≫ z.Z.chart a) _ ((z.line false _ ℓ h).r a i).val ∧ (∀ m, ℓ.2 < m → cf m = 0) ∧
            IsCombAtG (Y z.Z.i).t (spMap φ ≫ z.Z.chart a ≫ z.Z.π) ((z.Z.fr a).bc φ ℓ.1) cf (u.bc ψ ℓ.1 ℓ.2)

end Free

theorem nonempty_link {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) {p : ℕ} (hp : p.Prime)
    {W : ValuationSubring ℂ} (hW : (p : ℂ) ∈ W.nonunits)
    (Z : LocM.Mdl (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩) : Nonempty (Link Z s.T.Z) := by
  obtain ⟨τ, mu, hτ⟩ := exists_isTrans (S.sys.clauses p W hp hW).1 Z.dvd Z.le
  let b : 𝓞 κ.c.F →+* κ.c.V W := (algebraMap (𝓞 κ.c.F) κ.c.F).codRestrict (κ.c.V W) fun x => by
    have hx : IsIntegral ℤ (x : κ.c.F) := x.2
    have h₂ : IsIntegral (κ.c.V W) (x : κ.c.F) := hx.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h₂
    exact (show ((y : κ.c.V W) : κ.c.F) = algebraMap _ _ x from hy) ▸ y.2
  have hb : spMap (κ.c.V W).subtype ≫ spMap b = spMap (algebraMap (𝓞 κ.c.F) κ.c.F) := (Spec.map_comp _ _).symm
  obtain ⟨f, t, n₁, n₂, hf, hj, -⟩ := s.glob.2.1 p W hp hW b fun _ => rfl
  let k : gen s.T.Z ⟶ pullback s.Ygl.s (spMap b) :=
    pullback.lift (genι s.T.Z ≫ s.T.b) (genStr s.T.Z ≫ spMap (κ.c.V W).subtype) (by
      rw [Category.assoc, s.T.b_s, Category.assoc, hb]
      exact pullback.condition)
  have hk : k ≫ pullback.fst _ _ = genι s.T.Z ≫ s.T.b := pullback.lift_fst _ _ _
  obtain ⟨tg, ⟨m⟩⟩ := exists_sab k t
  obtain ⟨m₂, -⟩ := GlobalTheory.LevelCover.sab_comp m n₂ rfl
  obtain ⟨n, -⟩ := GlobalTheory.LevelCover.sab_comp m n₁ hk
  obtain ⟨m₁, -⟩ := GlobalTheory.LevelCover.sab_cancel s.T.pull n (genι s.T.Z) rfl
  refine ⟨⟨τ, mu, hτ, k ≫ f, tg, m₁, m₂, ?_, ?_⟩⟩
  · rw [← Category.assoc]
    refine hj _ ?_
    rw [Category.assoc, hk, ← Category.assoc]
    exact s.T.j_b
  · exact (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) hf).trans (pullback.lift_snd _ _ _))

end GlobalTheory.GenDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPrimitiveDeRhamTorsionTowerPresentationStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_primitiveDeRhamTorsionTowerPresentation : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A), Nonempty (Dat t c) := by
  first | exact @GlobalTheory.PtExt.nonempty_dat | exact GlobalTheory.PtExt.nonempty_dat | (intros; apply GlobalTheory.PtExt.nonempty_dat <;> assumption)
end

