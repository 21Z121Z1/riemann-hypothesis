import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2909
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2949
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2959
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.TorsKer

theorem pow_eq_one_of_points : ∀ (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n m : ℕ), (n : K) ≠ 0 →
    (∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1 → x ^ m = 1) →
    ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ^ n = 1 → x ≫ f.hom = 1 → x ^ m = 1 := by
  intro K _ A C f n m hn hpt T x hx hf
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    have : IsUnit (n : K) := isUnit_iff_ne_zero.2 hn
    simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨-, hZf, hZe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A.X (hG := A.ab) hu
  let Z := torsion A.X n
  let iZ : Z ⟶ A.X := torsion.ι A.X n
  have hiZ : iZ ^ n = 1 := by
    rw [← GlobalTheory.GrpTangent.comp_mulN]
    exact (pullback.condition (f := mulN A.X n) (g := (η : 𝟙_ (Over (Sp K)) ⟶ A.X))).trans
      (by rw [CategoryTheory.Hom.one_def]; congr 1; exact toUnit_unique _ _)
  let a : Z.left ⟶ C.X.left := (iZ ≫ f.hom).left
  have : IsClosedImmersion (η[C.X]).left :=
    isClosedImmersion_of_comp_eq_id (Y := Sp K) C.X.hom _ (Over.w _)
  let H : Over (Sp K) := Over.mk (pullback.fst a (η[C.X]).left ≫ Z.hom)
  let j : H ⟶ Z := Over.homMk (pullback.fst a (η[C.X]).left) rfl
  have hHf : IsFinite H.hom := by
    haveI := hZf; show IsFinite (pullback.fst a (η[C.X]).left ≫ Z.hom); infer_instance
  have hHe : Etale H.hom := by
    haveI := hZe
    haveI : FormallyUnramified Z.hom := by infer_instance
    haveI : LocallyOfFinitePresentation Z.hom := by infer_instance
    haveI : IsClosedImmersion (pullback.fst a (η[C.X]).left) := inferInstance
    haveI : FormallyUnramified (pullback.fst a (η[C.X]).left) := inferInstance
    haveI : FormallyUnramified H.hom := by
      show FormallyUnramified (pullback.fst a (η[C.X]).left ≫ Z.hom)
      exact MorphismProperty.comp_mem @FormallyUnramified _ _ ‹_› ‹FormallyUnramified Z.hom›
    haveI : LocallyOfFinitePresentation H.hom := by
      show LocallyOfFinitePresentation (pullback.fst a (η[C.X]).left ≫ Z.hom); infer_instance
    exact Etale.of_formallyUnramified_of_flat _
  have hjf : j ≫ iZ ≫ f.hom = 1 := by
    apply Over.OverMorphism.ext
    have h1 : (toUnit H).left = H.hom := by simpa using Over.w (toUnit H)
    have h2 : (η[C.X]).left ≫ C.X.hom = 𝟙 _ := by simpa using Over.w (η[C.X])
    have h3 : a ≫ C.X.hom = Z.hom := Over.w (iZ ≫ f.hom)
    have hs : pullback.snd a (η[C.X]).left = (toUnit H).left := by
      rw [h1]
      show pullback.snd a _ = pullback.fst a _ ≫ Z.hom
      rw [← h3, ← Category.assoc, pullback.condition, Category.assoc, h2]
      exact (Category.comp_id _).symm
    rw [CategoryTheory.Hom.one_def]
    show pullback.fst a _ ≫ a = (toUnit H).left ≫ (η[C.X]).left
    rw [← hs]
    exact pullback.condition
  have hsep : IsSeparated A.X.hom := by
    have := A.ab.proper; infer_instance
  have key : (j ≫ iZ) ^ m = 1 := by
    refine GlobalTheory.GenTorsMap.hom_ext_points hHf hHe hsep _ _ fun y => ?_
    rw [MonObj.comp_one, MonObj.comp_pow]
    refine hpt (y ≫ j ≫ iZ) ?_ ?_
    · rw [← MonObj.comp_pow, ← MonObj.comp_pow, hiZ, MonObj.comp_one, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, hjf, MonObj.comp_one]
  have hx1 : x ≫ mulN A.X n = toUnit T ≫ η[A.X] := by
    rw [GlobalTheory.GrpTangent.comp_mulN, hx, CategoryTheory.Hom.one_def]
  let x₁ : T ⟶ Z := pullback.lift x (toUnit T) hx1
  have hx₁ : x₁ ≫ iZ = x := pullback.lift_fst _ _ _
  have hw : x₁.left ≫ a = T.hom ≫ (η[C.X]).left := by
    have e := congrArg (fun g => g.left) hf
    simp only [CategoryTheory.Hom.one_def, Over.comp_left] at e
    have hT : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
    rw [← hT, ← e, ← hx₁]
    simp [a]
  let x₂ : T ⟶ H := Over.homMk (pullback.lift x₁.left T.hom hw)
    (by show _ ≫ pullback.fst a _ ≫ Z.hom = _; rw [← Category.assoc, pullback.lift_fst]; exact Over.w x₁)
  have hx₂ : x₂ ≫ j ≫ iZ = x := by
    rw [← hx₁, ← Category.assoc]
    congr 1
    apply Over.OverMorphism.ext
    simp [x₂, j]
    exact pullback.lift_fst _ _ _
  rw [← hx₂, ← MonObj.comp_pow, key, MonObj.comp_one]

end GlobalTheory.AV.TorsKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerDataTensorBundleIsoWithPsiValues
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.PowData

theorem tens_iso_psi : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D.P.A ⟶ D₀.P.A)) (j : Fin r → (D₀.P.A ⟶ D.P.A)) (h : Fin r → D₀.X → D.X) (k : Fin r → D.X → D₀.X), (∀ a χ, D.c (h a χ) = D₀.c χ ≫ j a) → (∀ a y, D₀.c (k a y) = D.c y ≫ pr a) → (∀ a, PeriodRel D D₀ (pr a) (h a) (k a)) → (∀ a, CmpTwo D D₀ (pr a) (j a)) → Expand D (fun ab : Fin r × Fin r => W ab.1 ab.2) (𝟙 D.P.A) (fun ab => pr ab.2 ≫ j ab.1) → PrimVal D (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) (fun y => ∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y)) → ∃ w : LB.Iso D.P.L (LB.LinComb D₀.P.L (tensφ pr) (tensε W)), w.IsGen ∧ ∀ y z J J', Good D₀.P.L z J → Good D.P.L z J' → val (D.psi y) (𝟙 _) z J' = gm (D.xK y) z _ (w.s (fun k => J (D.xK y ≫ tensφ pr k), J' (D.xK y))) * ∏ a, ∏ b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z J ^ W a b := by
  intro R _ _ D D₀ r W pr j h k h1 h2 h3 h4 h5 h6
  obtain ⟨u, hu, hu'⟩ := h6
  obtain ⟨κ, hκ, hκ'⟩ := h5
  choose Γ hΓ hΓ' using h4
  have hp₁ := isPart_inl D.P.L D₀.P.L
  let g : Fin r → (D.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left) := fun b => (lift (𝟙 D.P.A) (pr b)).left
  let Φ : Fin r → Fin 4 ⊕ Fin 4 → ((D.P.A ⊗ D₀.P.A).left ⟶ D.P.A.left ⨿ D₀.P.A.left) := fun a =>
    Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j a) k ≫ coprod.inl)
      (fun k => lamPts (fst D.P.A D₀.P.A ≫ pr a) (snd D.P.A D₀.P.A) k ≫ coprod.inr)
  let P := prodZGen (JN D D₀) (fun ab : Fin r × Fin r => fun m => g ab.2 ≫ Φ ab.1 m) (fun _ => Sum.elim Oε Oinvε)
    (fun ab => -W ab.1 ab.2) (fun ab => LB.pullGen (JN D D₀) _ _ (Γ ab.1) (g ab.2))
  have hP : P.IsGen := prodZGen_isGen (jn_isLB D D₀) _ fun ab =>
    ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (hΓ ab.1) _
  let rig0 := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (toUnit D.P.A).left
  have hrig0 : rig0.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ D.rig_gen _
  let T0 := LB.mulGen (JN D D₀) _ _ _ _ (LB.mulGen (JN D D₀) _ _ _ _ (LB.mulGen (JN D D₀) _ _ _ _ (hp₁.gen u)
    (LB.invGen (JN D D₀) _ _ (hp₁.gen κ))) P) (LB.invGen (JN D D₀) _ _ (hp₁.gen rig0))
  have hT0 : T0.IsGen := by
    refine ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hp₁.gen_isGen hu) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _
        (hp₁.gen_isGen hκ))) hP) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hp₁.gen_isGen hrig0))
  obtain ⟨t, ht, htv⟩ := exists_gen (jn_isLB D D₀)
    (φ' := Sum.elim (fun k => tensφ pr k ≫ coprod.inr) (fun _ : PUnit => 𝟙 D.P.A.left ≫ coprod.inl))
    (ε' := Sum.elim (tensε W) (fun _ => -1)) (by
      intro U _ hh
      clear hu' hκ' hΓ' h3 h1 h2 hT0 hP hrig0
      have cl : ∀ {T T' : Over (Sp R)} {B : Over (Sp R)} [GrpObj B] (s : T' ⟶ T) (x y : T ⟶ B) (i : Fin 4),
          s.left ≫ lamPts x y i = lamPts (s ≫ x) (s ≫ y) i := by
        intro T T' B _ s x y i
        fin_cases i
        · exact congrArg (fun q => q.left) (MonObj.comp_mul s x y)
        · rfl
        · rfl
        · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one s)
      have hD1 : ∀ a b i, g b ≫ Φ a (Sum.inl i) = lamPts (𝟙 D.P.A) (pr b ≫ j a) i ≫ coprod.inl := by
        intro a b i
        show (lift (𝟙 D.P.A) (pr b)).left ≫ lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j a) i ≫ coprod.inl = _
        rw [← Category.assoc, cl, lift_fst, lift_snd_assoc]
      have hD2 : ∀ a b i, g b ≫ Φ a (Sum.inr i) = tensφ pr ((a, b), i) ≫ coprod.inr := by
        intro a b i
        show (lift (𝟙 D.P.A) (pr b)).left ≫ lamPts (fst D.P.A D₀.P.A ≫ pr a) (snd D.P.A D₀.P.A) i ≫ coprod.inr = _
        rw [← Category.assoc, cl, lift_fst_assoc, lift_snd, Category.id_comp]
        rfl
      have hOi : ∀ i, Oinvε i = - Oε i := by intro i; fin_cases i <;> rfl
      have hCD : (∏ p : (Fin r × Fin r) × Fin 4,
            hh (lamPts (𝟙 D.P.A) (pr p.1.2 ≫ j p.1.1) p.2 ≫ coprod.inl) ^ (- -(W p.1.1 p.1.2 * Oε p.2))) *
          (∏ p : (Fin r × Fin r) × (Fin 4 ⊕ Fin 4), hh (g p.1.2 ≫ Φ p.1.1 p.2) ^ (-W p.1.1 p.1.2 * Sum.elim Oε Oinvε p.2)) =
          ∏ p : (Fin r × Fin r) × Fin 4, hh (tensφ pr p ≫ coprod.inr) ^ (tensε W p) := by
        rw [Fintype.prod_prod_type (α₁ := Fin r × Fin r), Fintype.prod_prod_type (α₁ := Fin r × Fin r),
          Fintype.prod_prod_type (α₁ := Fin r × Fin r), ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun ab _ => ?_
        rw [Fintype.prod_sum_type, ← _root_.mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hD1, hD2, Sum.elim_inl, Sum.elim_inr, hOi]
        simp only [tensε, neg_neg, neg_mul, mul_neg, zpow_neg, mul_inv_cancel, _root_.one_mul, Prod.mk.eta]
      have hAB : (∏ i : Fin 4, hh (![(padd D.P.A (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2)).left,
            𝟙 D.P.A.left, (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2).left, (toUnit D.P.A ≫ η[D.P.A]).left] i ≫
              coprod.inl) ^ ((![1, -2, -1, 2] : Fin 4 → ℤ) i)) *
          (∏ i : Fin 4, hh (lamPts (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) i ≫ coprod.inl) ^
            (-Oε i)) =
          (hh (𝟙 D.P.A.left ≫ coprod.inl))⁻¹ * hh ((toUnit D.P.A ≫ η[D.P.A]).left ≫ coprod.inl) := by
        simp only [Fin.prod_univ_four, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        have e0 : (𝟙 D.P.A * ∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) =
            padd D.P.A (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) := rfl
        have e1 : (1 : D.P.A ⟶ D.P.A) = toUnit D.P.A ≫ η[D.P.A] := rfl
        have e2 : (𝟙 D.P.A : D.P.A ⟶ D.P.A).left = 𝟙 D.P.A.left := rfl
        rw [e0, e1, e2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
      have key : ∀ A B C D E Q I O : U, A * B = I⁻¹ * O → C * D = Q → E = O ^ (-1 : ℤ) →
          A * (B * C) * D * E = Q * I ^ (-1 : ℤ) := by
        intro A B C D E Q I O h₁ h₂ h₃
        rw [← _root_.mul_assoc A B C, h₁, _root_.mul_assoc _ C D, h₂, h₃]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.prod_singleton]
      exact key _ _ _ _ _ _ _ _ hAB hCD rfl) T0 hT0
  obtain ⟨w, hw, hwv⟩ := exists_iso_of_joinGen D.P.isLB D₀.P.isLB t ht
  refine ⟨w, hw, fun y z J J' hJ hJ' => ?_⟩
  obtain ⟨Jn, hJn, e1, e2⟩ := exists_good_join D.P.isLB D₀.P.isLB hJ' hJ
  subst e1 e2
  rw [hwv _ (D.xK y) z Jn hJn, htv _ _ z Jn hJn]
  have hp₂ := isPart_inr D.P.L D₀.P.L
  have hJ1 : Good D.P.L z (rl Jn) := hp₁.good hJn
  have vT : val T0 (D.xK y) z Jn = val u (D.xK y) z (rl Jn) * (val κ (D.xK y) z (rl Jn))⁻¹ *
      (∏ ab : Fin r × Fin r, val (Γ ab.1) (D.xK y ≫ g ab.2) z Jn ^ (-W ab.1 ab.2)) *
      (val D.rig (D.xK y ≫ (toUnit D.P.A).left) z (rl Jn))⁻¹ := by
    simp only [T0, P, rig0, val_mul hJn, val_inv, hp₁.val_gen _ _ _ hJn, val_prodZGen _ _ _ _ _ hJn, val_pull hJn,
      val_pull hJ1]
  have c1 := val_corr hJ1 (hu' y) (𝟙 _)
  rw [val_mul hJ1, val_mul hJ1, val_pull hJ1, Category.id_comp] at c1
  have cE := hκ' (toUnit (TK R) ≫ D.c y) y (fun ab => h ab.1 (k ab.2 y)) (Category.comp_id _)
    (fun ab => by simp only [h1, h2, Category.assoc]) z (rl Jn) hJ1
  have hrig : D.xK y ≫ (toUnit D.P.A).left = 𝟙 _ ≫ (toUnit (TK R)).left := by
    rw [Category.id_comp]
    show (toUnit (TK R) ≫ D.c y).left ≫ (toUnit D.P.A).left = _
    rw [← Over.comp_left, Category.assoc, comp_toUnit, comp_toUnit]
  have vrig : val D.rig (D.xK y ≫ (toUnit D.P.A).left) z (rl Jn) = val D.rigK (𝟙 _) z (rl Jn) := by
    rw [hrig]; exact (val_pull hJ1 _ _ _).symm
  have hper : ∀ a b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z (rr Jn) =
      val (D.tau y (h a (k b y))) (𝟙 _) z (rl Jn) * val (Γ a) (D.xK y ≫ g b) z Jn := by
    intro a b
    obtain ⟨u', hu'n, hu'v⟩ := h3 a (k b y)
    rw [hu'v y z Jn hJn]
    refine congrArg (_ * ·) ((hΓ' a (h a (k b y)) (k b y) (h1 a (k b y)) u' hu'n (TK R) (toUnit _ ≫ D.c y) z Jn hJn).trans
      (congrArg (fun q => val (Γ a) q z Jn) ?_))
    show (lift (toUnit (TK R) ≫ D.c y) (toUnit (TK R) ≫ D₀.c (k b y))).left =
      (toUnit (TK R) ≫ D.c y).left ≫ (lift (𝟙 D.P.A) (pr b)).left
    rw [h2, ← Over.comp_left, comp_lift, Category.comp_id, Category.assoc]
  have hG : ∏ ab : Fin r × Fin r, val (Γ ab.1) (D.xK y ≫ g ab.2) z Jn ^ (-W ab.1 ab.2) =
      (∏ a, ∏ b, val (Γ a) (D.xK y ≫ g b) z Jn ^ W a b)⁻¹ := by
    rw [Fintype.prod_prod_type]; simp only [zpow_neg, Finset.prod_inv_distrib]
  have key2 : ∀ {V : Type} [CommGroup V] (ψ ρ Tm Uu Kk Tp Gp : V), Tm * Uu = ψ * ρ → Tm * Kk = Tp →
      ψ = Uu * Kk⁻¹ * Gp⁻¹ * ρ⁻¹ * (Tp * Gp) := by
    intro V _ ψ ρ Tm Uu Kk Tp Gp e₁ e₂
    rw [eq_inv_mul_of_mul_eq e₁, eq_inv_mul_of_mul_eq e₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [vT, vrig, hG]
  simp only [hper, mul_zpow, Finset.prod_mul_distrib]
  have cE' : val (D.tau y (∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y))) (𝟙 _) z (rl Jn) *
      val κ (D.xK y) z (rl Jn) = ∏ a, ∏ b, val (D.tau y (h a (k b y))) (𝟙 _) z (rl Jn) ^ W a b := by
    refine Eq.trans cE ?_
    rw [Fintype.prod_prod_type]
  exact key2 _ _ _ _ _ _ _ c1 cE'

end GlobalTheory.Mum.PowData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem thetaNZ_of_preU : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → GlobalTheory.LN.ThetaNZ G U.P.L.L := by
  intro R _ _ _ hB D A G _ _ U hE
  obtain ⟨V, _, _, _, φ, D', A', G', _, _, U', U₀, F, C, hV, hφ, hc, hU⟩ := GlobalTheory.T.exists_completeDVR_comparison_preUniformised R hB D A G U hE
  obtain ⟨σ, f, g, q, hq, hf, hfg, hg0, hgm⟩ := GlobalTheory.T.exists_coefficientData_of_nonzero_section R hB D A G U V φ D' A' G' U' U₀ F C hV hφ hc hU
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_section_quotient_of_expansion_dvd R hB D A G U σ f g q hq hf hfg
  have := U.semi.smooth
  exact GlobalTheory.UnifNormal.thetaNZ_of_closedPoint G _ (GlobalTheory.T.exists_mem_nonzeroLocus_of_weightZero_expansion R D A G U τ g hτ hg0 hgm)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageLe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PushEigen

variable {K : Type} [Field K]

def tors (B : AbVar K) (n : ℕ) : Subgroup (𝟙_ (Over (Sp K)) ⟶ B.X) := (powMonoidHom n).ker

theorem mem_tors {B : AbVar K} {n : ℕ} {y : 𝟙_ (Over (Sp K)) ⟶ B.X} : y ∈ tors B n ↔ y ^ n = 1 := Iff.rfl

abbrev mulN (B : AbVar K) (n : ℕ) : B.X.left ⟶ B.X.left := (𝟙 B.X ^ (n : ℤ)).left

def transl (B : AbVar K) (y : 𝟙_ (Over (Sp K)) ⟶ B.X) : B.X ⟶ B.X := (toUnit B.X ≫ y) * 𝟙 B.X

theorem transl_mulN (B : AbVar K) (n : ℕ) (y : 𝟙_ (Over (Sp K)) ⟶ B.X) (hy : y ∈ tors B n) :
    (transl B y).left ≫ mulN B n = mulN B n := by
  rw [mulN, ← Over.comp_left]
  congr 1
  rw [zpow_natCast, transl, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow,
    mem_tors.1 hy, MonObj.comp_one, _root_.one_mul]

theorem preimage_le (B : AbVar K) (n : ℕ) (y : 𝟙_ (Over (Sp K)) ⟶ B.X) (hy : y ∈ tors B n) (V : B.X.left.Opens) :
    mulN B n ⁻¹ᵁ V ≤ (transl B y).left ⁻¹ᵁ (mulN B n ⁻¹ᵁ V) := fun x hx => by
  change ((transl B y).left ≫ mulN B n) x ∈ V
  rw [transl_mulN B n y hy]
  exact hx

def act (B : AbVar K) (n : ℕ) (y : tors B n) (V : B.X.left.Opens) :
    Γ(B.X.left, mulN B n ⁻¹ᵁ V) →+* Γ(B.X.left, mulN B n ⁻¹ᵁ V) :=
  ((transl B y.1).left.appLE (mulN B n ⁻¹ᵁ V) (mulN B n ⁻¹ᵁ V) (preimage_le B n y.1 y.2 V)).hom

def cst (B : AbVar K) (W : B.X.left.Opens) : K →+* Γ(B.X.left, W) :=
  (B.X.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

def IsEig (B : AbVar K) (n : ℕ) (χ : tors B n →* Kˣ) (V : B.X.left.Opens) (u : Γ(B.X.left, mulN B n ⁻¹ᵁ V)ˣ) :
    Prop :=
  ∀ y : tors B n, act B n y V (u : Γ(B.X.left, mulN B n ⁻¹ᵁ V)) = cst B _ ((χ y : Kˣ) : K) * (u : Γ(B.X.left, mulN B n ⁻¹ᵁ V))

def eigen (B : AbVar K) (n : ℕ) (χ : tors B n →* Kˣ) : LB B.X.left :=
  GlobalTheory.EigenDescent.eigenLB (mulN B n) (IsEig B n χ)

end GlobalTheory.PushEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegRigid

open GlobalTheory.CechPic GlobalTheory.AmpleRigid

theorem serreAmple : SerreAmpleSt :=
  serreAmple_of_finiteOrder_of_separated (GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube constSt GlobalTheory.AmpleCube.cubeSt)
    (separatedSt_of_const_cube constSt GlobalTheory.AmpleCube.cubeSt)

theorem exists_aut {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback A' A f φ') :
    ∃ σ : A' ≅ A', IsMonHom σ.hom ∧ σ.hom.left ≫ φ' = φ := by
  let ψ : A'.left ⟶ A'.left := h'.1.lift φ A'.hom h.1.w
  have e₁ : ψ ≫ φ' = φ := h'.1.lift_fst _ _ _
  have e₂ : ψ ≫ A'.hom = A'.hom := h'.1.lift_snd _ _ _
  have hψ : IsGrpPullback A' A' (𝟙 _) ψ :=
    IsGrpPullback.cancel h' (by rw [Category.id_comp, e₁]; exact h) (by rw [e₂, Category.comp_id])
  haveI : IsIso ψ := hψ.1.isIso_fst_of_isIso
  let σ : A' ≅ A' := Over.isoMk (asIso ψ) e₂
  exact ⟨σ, isMonHom_of_mul_comp σ.hom fun T x y => mul_comp_of_grpPullback_id σ.hom hψ x y, e₁⟩

theorem eq_of_field {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hamp : Out.RelAmple A L)
    {K : Type} [Field K] [IsAlgClosed K] {A' : Over (Sp K)} [GrpObj A'] (hA' : IsAbelianScheme A') {z : Sp K ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A z φ) (h' : IsGrpPullback A' A z φ')
    (hc : pull φ (cls L hL) = pull φ' (cls L hL)) {N : ℕ} (hN : 3 ≤ N) (hNK : (N : K) ≠ 0)
    (hfix : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (x : Over.mk t ⟶ A'), x ^ N = 1 →
      x.left ≫ φ = x.left ≫ φ') : φ = φ' := by
  obtain ⟨σ, hσ, e⟩ := exists_aut h h'
  have := hA'.comm
  have hL' := pull_isLB hL φ'
  obtain ⟨w, hw⟩ := (cls_eq_iff hL' hL').1 rfl
  obtain ⟨U, hU, hcl, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K)) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hcl)).mpr trivial
  have key := serreAmple K A' hA' (L.pull φ') hL'
    (relAmple_pull h'.1 hL hL' ((isGen_iff w).1 hw) U hU hy hamp) N hN hNK σ hσ
    (by rw [cls_pull hL, ← pull_comp, e, hc]) fun Ω _ _ t x hx => by
      apply Over.OverMorphism.ext
      apply h'.1.hom_ext
      · rw [Over.comp_left, Category.assoc, e]
        exact hfix Ω t x hx
      · rw [Over.w, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

variable {h n n' : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
  {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}

theorem pull_cls_diag {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {φ : c'.A.left ⟶ c.A.left}
    {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) :
    pull φ (cls c.diag (pull_isLB c.isLB _)) = cls c'.diag (pull_isLB c'.isLB _) := by
  have e : (lift (𝟙 c'.A) (𝟙 c'.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 c.A) (𝟙 c.A)).left := by
    have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 c.A) (𝟙 c.A))
    have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 c.A) (𝟙 c.A))
    have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 c'.A) (𝟙 c'.A))
    have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 c'.A) (𝟙 c'.A))
    simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = (_ ≫ _) ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
    · show (_ ≫ _) ≫ (snd c.A c.A).left = (_ ≫ _) ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp
  have h1 : pull φ₂ (cls c.P c.isLB) = cls c'.P c'.isLB :=
    ((cls_eq_iff c'.isLB (pull_isLB c.isLB φ₂)).2 hw).symm
  unfold SiegPre.diag
  rw [cls_pull c.isLB, cls_pull c'.isLB, ← pull_comp, ← e, pull_comp, h1]

theorem eq_on_torsion (hζ : IsUnit ζ) (c : SiegPre h n ζ s) {A' : Over S'} [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ c.A.left} (hφ : IsGrpPullback A' c.A f φ)
    (lv : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A'))
    (h₁ : ∀ a, (lv a).left ≫ φ = f ≫ (c.lev a).left) (h₂ : ∀ a, (lv a).left ≫ φ' = f ≫ (c.lev a).left)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ A') (hy : y ^ n = 1) :
    y.left ≫ φ = y.left ≫ φ' := by
  let β : B →+* k := (Spec.preimage ((x ≫ f) ≫ s)).hom
  obtain ⟨-, hs, -⟩ := c.geom k (x ≫ f) β (hζ.map β).unit (Spec.map_preimage _).symm rfl
  have hy₁ : pushHom hφ (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := hs _ hy₁
  have hu : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := (Category.comp_id _).symm.trans (Over.w (toUnit _))
  have e : (x ≫ f) ≫ (c.lev a).left = y.left ≫ φ := by
    rw [← hu]
    exact congrArg (fun q => q.left) ha
  have e₁ : y.left = x ≫ (lv a).left := by
    apply hφ.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h₁ a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h₁ a).trans (h₂ a).symm)

theorem eq_of_sRelBy : ∀ (h n n' d' : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (c : SiegPre h n (b.ζ : B) s) (c' : SiegPre h n' ζ' s') (f : S' ⟶ S) (φ φ' : c'.A.left ⟶ c.A.left), 3 ≤ n → Odd n → c.Principal → SRelBy c' c d' 1 f φ → SRelBy c' c d' 1 f φ' → φ = φ' := by
  intro h n n' d' B B' _ _ b ζ' S S' s s' c c' f φ φ' hn _ hc ⟨g, ⟨φ₂, q, w⟩, l⟩ ⟨g', ⟨φ₂', q', w'⟩, l'⟩
  simp only [pow_one] at l l'
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 c'.A c'.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback c'.A j
    have := c'.ab.smooth
    have := c'.ab.proper
    have := c'.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj c'.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd c'.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd c'.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd c'.A.hom j); infer_instance }
    have hNK : (n : K) ≠ 0 := by
      have hu := b.unit.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hc.1 hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ ((pull_cls_diag q w).trans (pull_cls_diag q' w').symm)) hn hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion b.ζ.isUnit c g _ l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.SiegRigid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedGenericFibreUniformisedTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principallyPolarised_genericFibre_uniformised_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)), Nonempty (SABMap t' t χ) → Nonempty (PELUnif (IsLocalRing.maximalIdeal V) t') → ∃ g : ℕ, ∀ (R : Type) [CommRing R] (e : FractionRing V →+* R), PolFib t.G t.PP.L g (spMap e ≫ jK V ≫ χ) := by
  first | exact @GlobalTheory.UMin.UnifPolFib.polFib_of_unif | exact GlobalTheory.UMin.UnifPolFib.polFib_of_unif | (intros; apply GlobalTheory.UMin.UnifPolFib.polFib_of_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiZeroMulRigidificationConstantNeZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_zero_mul_rigidification_constant_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), ∃ c₀ : FractionRing V, c₀ ≠ 0 ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = GlobalTheory.UT.cst (FractionRing V) z c₀ := by
  first | exact @GlobalTheory.Poinc.IntTerm.psi_zero_rig_const | exact GlobalTheory.Poinc.IntTerm.psi_zero_rig_const | (intros; apply GlobalTheory.Poinc.IntTerm.psi_zero_rig_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyScalarIsUnitOnIntegralModelsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyScalar_isUnit_on_integralModels : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.KeyUnitOnModels := by
  first | exact @GlobalTheory.KeyUnitModels.keyUnitOnModels | exact GlobalTheory.KeyUnitModels.keyUnitOnModels | (intros; apply GlobalTheory.KeyUnitModels.keyUnitOnModels <;> assumption)
end

