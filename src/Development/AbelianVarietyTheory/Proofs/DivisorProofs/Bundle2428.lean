import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegeneratePairingOfGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NondegSpread
open GlobalTheory.CechPic

theorem pairing_add_and_symm : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) ∧
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) := by
  intro S A _ _ hA P hP r₁ r₂ hs ha
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  refine ⟨fun T x x' y => ?_, fun T x y => ?_⟩
  · obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD ha P hP r₁ r₂ T x x' y).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := (cls_eq_iff hP (pull_isLB hP _)).2 hs
    rw [cls_pull hP] at e
    conv_lhs => rw [e]
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem over_hom_ext_of_local : ∀ (S : Scheme.{0}) (T X : Over S) (a b : T ⟶ X),
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ Out.overResι V ≫ a = Out.overResι V ≫ b) → a = b := by
  intro S T X a b h
  choose V hV e using h
  apply Over.OverMorphism.ext
  exact Scheme.hom_ext_of_forall _ _ fun p => ⟨V p, hV p, congrArg (fun q => q.left) (e p)⟩

theorem hom_ext_of_generic_points : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (H X : Over (Sp O))
    [IsSeparated X.hom] (a b : H ⟶ X), IsFinite H.hom → Flat H.hom →
    (∀ (T : Over (Sp O)) (t : T.left ⟶ Sp K), T.hom = t ≫ spMap (algebraMap O K) → ∀ z : T ⟶ H, z ≫ a = z ≫ b) → a = b := by
  intro O K _ _ _ _ _ H X _ a b hfin hflat h
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField O K
  have : IsSchemeTheoreticallyDominant (pullback.fst H.hom (spMap (algebraMap O K))) :=
    .of_isPullback (IsPullback.of_hasPullback H.hom (spMap (algebraMap O K))).flip
  let T : Over (Sp O) := Over.mk (pullback.fst H.hom (spMap (algebraMap O K)) ≫ H.hom)
  let z : T ⟶ H := Over.homMk (pullback.fst _ _) rfl
  refine GlobalTheory.over_ext_of_schemeTheoreticallyDominant (pullback.fst H.hom (spMap (algebraMap O K))) ?_
  exact congrArg (fun q => q.left) (h T (pullback.snd _ _) pullback.condition z)

theorem cls_translDiff : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    ∀ (T : Over S) (x : T ⟶ A) (h : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) x).IsLB),
    CechPic.cls _ h = CechPic.pull (fst T A).left (CechPic.pull (lift x x).left (CechPic.cls P hP)) + CechPic.pull (lift (fst T A ≫ x ^ 2) (snd T A)).left (CechPic.cls P hP) := by
  intro S A _ P hP hB hS T x h
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have dg : ∀ g : T ⊗ A ⟶ A, CechPic.pull g.left (CechPic.cls _ hD) =
      CechPic.pull (lift g g).left (CechPic.cls P hP) := fun g => by
    rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
  have hm : lift (fst T A ≫ x) (snd T A) ≫ μ[A] = (fst T A ≫ x) * snd T A := rfl
  refine (cls_linComb hD (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _) ![1, -1] h).trans ?_
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul]
  rw [hm, dg, dg, hB, hS _ (fst T A ≫ x) (_ * _), hS _ (snd T A) (_ * _), hB, hB, ← pull_comp,
    ← Over.comp_left, comp_lift, MonObj.comp_pow, pow_two, hB, hS _ (snd T A) (fst T A ≫ x)]
  abel

theorem memKL_of_pairing_sq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    ∀ (T : Over S) (x : T ⟶ A), CechPic.pull (lift (fst T A ≫ x ^ 2) (snd T A)).left (CechPic.cls P hP) = 0 →
    MemKL A (P.pull (lift (𝟙 A) (𝟙 A)).left) x := by
  intro S A _ P hP hB hS T x h0 p
  have hD := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have hM : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) x).IsLB := LB.isLB_linComb hD _ _
  have e := cls_translDiff S A P hP hB hS T x hM
  rw [h0, add_zero] at e
  obtain ⟨N, hN, hc⟩ := cls_surj (CechPic.pull (lift x x).left (CechPic.cls P hP))
  have e' : cls (N.pull (fst T A).left) (pull_isLB hN _) = cls _ hM := by rw [cls_pull hN, hc, e]
  obtain ⟨u, hu⟩ := (cls_eq_iff _ _).1 e'
  exact GlobalTheory.CubeLawCompare.locally_trivial_of_iso_pull (fst T A).left _ hN u hu p

theorem exists_local_triv_sq_of_memKL : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    ∀ (T : Over S) (x : T ⟶ A), MemKL A (P.pull (lift (𝟙 A) (𝟙 A)).left) x → ∀ p : T.left,
    ∃ V : T.left.Opens, p ∈ V ∧ ∃ t : (P.pull (lift (snd A (Out.overRes V) ≫ Out.overResι V ≫ x ^ 2) (fst A (Out.overRes V))).left).Gen, t.IsGen := by
  intro S A _ P hP hB hS r₂ T x hx p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  have hD := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have hM : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) x).IsLB := LB.isLB_linComb hD _ _
  have nat : ∀ {Y Z : Over S} (g : Y ⟶ Z) (a b : Z ⟶ A), CechPic.pull g.left (CechPic.pull (lift a b).left (CechPic.cls P hP)) = CechPic.pull (lift (g ≫ a) (g ≫ b)).left (CechPic.cls P hP) :=
    fun g a b => by rw [← pull_comp, ← Over.comp_left, comp_lift]
  have ax : ∀ {Y : Over S} (a : Y ⟶ A), CechPic.pull (lift a (1 : Y ⟶ A)).left (CechPic.cls P hP) = 0 := fun a => by
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 r₂
    rw [cls_pull hP] at e
    have e' := congrArg (CechPic.pull a.left) e
    rwa [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at e'
  let Vo := Out.overRes V
  let u : Vo ⟶ T := Out.overResι V
  let W := (fst T A).left ⁻¹ᵁ V
  let U : Vo ⊗ A ⟶ T ⊗ A := lift (fst Vo A ≫ u) (snd Vo A)
  have k₁ : U ≫ fst T A = fst Vo A ≫ u := lift_fst _ _
  have k₂ : U ≫ snd T A = snd Vo A := lift_snd _ _
  obtain ⟨n, hn⟩ : ∃ n : (Vo ⊗ A).left ⟶ W.toScheme, n ≫ W.ι = U.left :=
    ⟨IsOpenImmersion.lift _ U.left (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (U ≫ fst T A).left y ∈ V
      rw [k₁]
      show V.ι ((fst Vo A).left y) ∈ V
      have hy := Set.mem_range_self (f := V.ι) ((fst Vo A).left y)
      rwa [Scheme.Opens.range_ι] at hy), IsOpenImmersion.lift_fac _ _ _⟩
  have e0 := (cls_eq_zero_iff (pull_isLB hM _)).2 ⟨c, hc⟩
  rw [cls_pull hM, cls_translDiff S A P hP hB hS T x hM] at e0
  have e1 := congrArg (CechPic.pull n) e0
  rw [map_zero, ← pull_comp, hn, map_add, ← pull_comp, ← Over.comp_left, nat, nat] at e1
  simp only [← Category.assoc, k₁, k₂] at e1
  simp only [Category.assoc] at e1
  have e2 := congrArg (CechPic.pull (lift (𝟙 Vo) (1 : Vo ⟶ A)).left) e1
  rw [map_zero, map_add, nat, nat, lift_fst_assoc, lift_snd, Category.id_comp, ax, add_zero] at e2
  have e3 : CechPic.pull (fst Vo A).left (CechPic.pull (lift (u ≫ x) (u ≫ x)).left (CechPic.cls P hP)) = 0 := by rw [e2, map_zero]
  rw [nat] at e3
  rw [e3, zero_add] at e1
  have e4 := congrArg (CechPic.pull (lift (snd A Vo) (fst A Vo)).left) e1
  rw [map_zero, nat, lift_fst_assoc, lift_snd] at e4
  refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
  rw [cls_pull hP]
  exact e4

theorem eq_one_of_generic_nondeg : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A']
    (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left),
    P.IsLB → P'.IsLB → LBIso P' (P.pull φ₂) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (T : Over (Sp O)) (t : T.left ⟶ Sp K), T.hom = t ≫ spMap (algebraMap O K) → ∀ x : T ⟶ A,
    (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro O K _ _ _ A _ A' _ φ φ₂ h sq P P' hP hP' H gen T t ht x hx
  obtain ⟨T, ⟨⟨⟩⟩, hT⟩ := T
  change T ⟶ Sp K at t
  change T ⟶ Sp O at hT
  change hT = t ≫ _ at ht
  subst ht
  let T' : Over (Sp K) := Over.mk t
  obtain ⟨x', rfl⟩ := GlobalTheory.SiegelPull.push_surjective h T' x
  rw [← map_one (pushHom h T')]
  congr 1
  apply gen T' x'
  obtain ⟨u, hu⟩ := H
  obtain ⟨c, hc⟩ := hx
  let f := spMap (algebraMap O K)
  let B : Over (Sp O) := Over.mk ((A' ⊗ T').hom ≫ f)
  let a : B ⟶ A := Over.homMk ((fst A' T').left ≫ φ) (by
    show (fst A' T').left ≫ φ ≫ A.hom = (A' ⊗ T').hom ≫ f
    rw [h.1.w, ← Category.assoc, Over.w (fst A' T')])
  let b : B ⟶ Over.mk (t ≫ f) := Over.homMk (snd A' T').left (by
    show (snd A' T').left ≫ t ≫ f = (A' ⊗ T').hom ≫ f
    rw [← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (snd A' T')))
  let χ : (A' ⊗ T').left ⟶ (A ⊗ Over.mk (t ≫ f)).left := (lift a b).left
  have c₁ : χ ≫ (fst A (Over.mk (t ≫ f))).left = (fst A' T').left ≫ φ :=
    congrArg (fun q => q.left) (lift_fst a b)
  have c₂ : χ ≫ (snd A (Over.mk (t ≫ f))).left = (snd A' T').left :=
    congrArg (fun q => q.left) (lift_snd a b)
  have sqr : (lift (snd A' T' ≫ x') (fst A' T')).left ≫ φ₂ =
      χ ≫ (lift (snd A (Over.mk (t ≫ f)) ≫ pushHom h T' x') (fst A (Over.mk (t ≫ f)))).left :=
    (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := B) (𝟙 _) _ _ χ _ _
      (by rw [Category.id_comp, Over.comp_left, Over.comp_left, ← Category.assoc χ, c₂, Category.assoc]; rfl)
      (by rw [Category.id_comp, c₁]))
  obtain ⟨c₂', h₂⟩ := gen_chartPull (chartPullSame P (fun _ : PUnit => (lift (snd A' T' ≫ x') (fst A' T')).left ≫ φ₂)
    _ _ χ fun _ => sqr) c hc
  exact exists_down ((isGen_iff u).1 hu) hP hP' c₂' h₂

theorem sq_eq_one_of_memKL_generic : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A']
    (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left)
    (hP : P.IsLB), P'.IsLB → LBIso P' (P.pull φ₂) →
    (∀ (T : Over (Sp O)) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over (Sp O)) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (T : Over (Sp O)) (t : T.left ⟶ Sp K), T.hom = t ≫ spMap (algebraMap O K) → ∀ x : T ⟶ A,
    MemKL A (P.pull (lift (𝟙 A) (𝟙 A)).left) x → x ^ 2 = 1 := by
  intro O K _ _ _ A _ A' _ φ φ₂ h sq P P' hP hP' H hB hS r₂ gen T t ht x hx
  refine over_hom_ext_of_local _ T A (x ^ 2) 1 fun p => ?_
  obtain ⟨V, hV, hg⟩ := exists_local_triv_sq_of_memKL _ A P hP hB hS r₂ T x hx p
  refine ⟨V, hV, ?_⟩
  rw [MonObj.comp_one]
  exact eq_one_of_generic_nondeg O K A A' φ φ₂ h sq P P' hP hP' H gen (Out.overRes V) (V.ι ≫ t)
    (by simp only [Out.overRes, Over.mk_hom, ht, Category.assoc]) _ hg

theorem nondeg_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left), IsAbelianScheme A → IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left), P.IsLB → P'.IsLB → LBIso P' (P.pull φ₂) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro O K _ _ _ _ _ _ A _ A' _ φ φ₂ hA h sq P P' hP hP' H r₁ r₂ hs ha gen T y hy
  haveI := hA.comm
  haveI := hA.proper
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨hB, hS⟩ := pairing_add_and_symm _ A hA P hP r₁ r₂ hs ha
  obtain ⟨H₀, _, i, -, -, hfin, hflat, hZ⟩ := GlobalTheory.kernel_finiteFlat_subgroup O A hA _ hL ha
  have hi : i ^ 2 = 1 := by
    refine hom_ext_of_generic_points O K H₀ A (i ^ 2) 1 hfin hflat fun T t ht z => ?_
    rw [MonObj.comp_pow, MonObj.comp_one]
    exact sq_eq_one_of_memKL_generic O K A A' φ φ₂ h sq P P' hP hP' H hB hS r₂ gen T t ht (z ≫ i) ((hZ T _).2 ⟨z, rfl⟩)
  obtain ⟨-, hfl, hsu⟩ := GlobalTheory.MulAmple.finite_flat_surjective_pow GlobalTheory.abelianSchemeLaws_all.1 O A hA _ hL ha 2
    (by norm_num)
  obtain ⟨T', e, x, he, he', hx⟩ := GlobalTheory.DivisibleHom.exists_lift_point ((𝟙 A) ^ 2) y
  have hx2 : x ^ 2 = e ≫ y := by rw [← hx, MonObj.comp_pow, Category.comp_id]
  have hmem : MemKL A _ x := memKL_of_pairing_sq _ A P hP hB hS T' x (by
    obtain ⟨t, ht⟩ := hy
    have e0 := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨t, ht⟩
    rw [cls_pull hP] at e0
    have e1 := congrArg (CechPic.pull (lift (snd T' A) (fst T' A ≫ e)).left) e0
    rw [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst] at e1
    rw [hx2]
    exact e1)
  obtain ⟨w, hw⟩ := (hZ T' x).1 hmem
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective e
  rw [← hx2, ← hw, ← MonObj.comp_pow, hi, MonObj.comp_one, MonObj.comp_one]

end GlobalTheory.NondegSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLevelOfTorsionBasis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RealMult

theorem span_torsion_of_indep {O : Type} [CommRing O] {G : Type} [CommGroup G] (N : ℕ)
    [Finite (O ⧸ Ideal.span {(N : O)})] (act : O → G →* G) (hone : ∀ x, act 1 x = x)
    (hmul : ∀ a b x, act (a * b) x = act b (act a x)) (hadd : ∀ a b x, act (a + b) x = act a x * act b x)
    (p q : Fin 2 → G) (hp : ∀ i, p i ^ N = 1) (hq : ∀ i, q i ^ N = 1)
    (ip : ∀ a b, act a (p 0) * act b (p 1) = 1 → (N : O) ∣ a ∧ (N : O) ∣ b)
    (iq : ∀ a b, act a (q 0) * act b (q 1) = 1 → (N : O) ∣ a ∧ (N : O) ∣ b)
    (sq : ∀ y, y ^ N = 1 → ∃ a b, y = act a (q 0) * act b (q 1)) :
    ∀ y, y ^ N = 1 → ∃ a b, y = act a (p 0) * act b (p 1) := by
  have hzero : ∀ x, act 0 x = 1 := fun x ↦ by
    have := hadd 0 0 x
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hnat : ∀ (n : ℕ) x, act (n : O) x = x ^ n := fun n x ↦ by
    induction n with
    | zero => simp [hzero]
    | succ n ih => rw [Nat.cast_succ, hadd, ih, hone, pow_succ]
  let f : (Fin 2 → G) → (O × O →+ Additive G) := fun r ↦ AddMonoidHom.mk'
    (fun c ↦ Additive.ofMul (act c.1 (r 0) * act c.2 (r 1))) (fun c d ↦ by
      rw [← ofMul_mul, Prod.fst_add, Prod.snd_add, hadd, hadd, _root_.mul_mul_mul_comm])
  let I : AddSubgroup O := (Ideal.span {(N : O)}).toAddSubgroup
  have hker : ∀ r : Fin 2 → G, (∀ i, r i ^ N = 1) →
      (∀ a b, act a (r 0) * act b (r 1) = 1 → (N : O) ∣ a ∧ (N : O) ∣ b) → (f r).ker = I.prod I := by
    intro r hr ir
    ext ⟨a, b⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_prod]
    change act a (r 0) * act b (r 1) = 1 ↔ a ∈ Ideal.span {(N : O)} ∧ b ∈ Ideal.span {(N : O)}
    rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    refine ⟨ir a b, ?_⟩
    rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    rw [hmul, hmul, hnat, hnat, hr, hr, map_one, map_one, _root_.one_mul]
  have hI : I.index ≠ 0 := by
    have : Finite (O ⧸ I) := ‹Finite (O ⧸ Ideal.span {(N : O)})›
    exact AddSubgroup.index_ne_zero_of_finite
  have cp : Nat.card (f p).range = I.index * I.index := by
    rw [← AddSubgroup.index_ker, hker p hp ip, AddSubgroup.index_prod]
  have cq : Nat.card (f q).range = I.index * I.index := by
    rw [← AddSubgroup.index_ker, hker q hq iq, AddSubgroup.index_prod]
  have : Finite (f q).range := Nat.finite_of_card_ne_zero (cq ▸ mul_ne_zero hI hI)
  have hle : (f p).range ≤ (f q).range := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    obtain ⟨c, d, h⟩ := sq (act a (p 0) * act b (p 1)) (by
      rw [mul_pow, ← map_pow, ← map_pow, hp, hp, map_one, map_one, _root_.one_mul])
    exact ⟨(c, d), congrArg Additive.ofMul h.symm⟩
  have heq := AddSubgroup.eq_of_le_of_card_ge hle (by rw [cp, cq])
  intro y hy
  obtain ⟨c, d, h⟩ := sq y hy
  have hm : Additive.ofMul y ∈ (f p).range := heq ▸ ⟨(c, d), congrArg Additive.ofMul h.symm⟩
  obtain ⟨⟨a, b⟩, hab⟩ := hm
  exact ⟨a, b, (congrArg Additive.toMul hab).symm⟩

theorem nonempty_level_of_torsion_basis (hT : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (S : Scheme.{0}) (X : Obj F 𝔠 S)
    (N : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), (N : Ω) ≠ 0 →
    ∃ p : Fin 2 → (Over.mk t ⟶ X.A), (∀ i, p i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : Over.mk t ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b)) :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ) (K : Type) [Field K] [IsAlgClosed K],
    (N : K) ≠ 0 → ∀ X : Obj F 𝔠 (Sp K), Nonempty (X.Level N) := by
  intro F _ _ _ 𝔠 N K _ _ hN X
  obtain ⟨p, hp, ip, -⟩ : ∃ p : Fin 2 → (𝟙_ (Over (Sp K)) ⟶ X.A), (∀ i, p i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : 𝟙_ (Over (Sp K)) ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) :=
    hT F 𝔠 (Sp K) X N K (𝟙 _) hN
  have inj : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (a b : 𝓞 F),
      (toUnit (Over.mk t) ≫ p 0 ≫ X.rm.act a) * (toUnit (Over.mk t) ≫ p 1 ≫ X.rm.act b) = 1 →
        (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
    intro Ω _ _ t a b h
    apply ip
    rw [← MonObj.comp_mul, ← MonObj.comp_one (toUnit (Over.mk t))] at h
    have ht : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
    have : Epi t := inferInstance
    apply Over.OverMorphism.ext
    have h' := congrArg (fun z ↦ z.left) h
    simp only [Over.comp_left, ht] at h'
    exact (cancel_epi t).1 h'
  refine ⟨⟨p, hp, inj, fun Ω _ _ t ↦ ?_⟩⟩
  have hNΩ : (N : Ω) ≠ 0 := by
    have := (Spec.preimage t).hom.injective.ne hN
    simpa using this
  have hN0 : (N : 𝓞 F) ≠ 0 := by
    have : N ≠ 0 := by rintro rfl; simp at hN
    exact_mod_cast this
  obtain ⟨q, hq, iq, sq⟩ := hT F 𝔠 (Sp K) X N Ω t hNΩ
  have : Finite (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN0)
  let act : 𝓞 F → (Over.mk t ⟶ X.A) →* (Over.mk t ⟶ X.A) := fun a ↦
    haveI := X.rm.hom a
    { toFun := fun y ↦ y ≫ X.rm.act a
      map_one' := MonObj.one_comp _
      map_mul' := fun x y ↦ MonObj.mul_comp _ _ _ }
  have key := span_torsion_of_indep N act (fun x ↦ by simp [act, X.rm.one])
    (fun a b x ↦ by simp [act, X.rm.mul]) (fun a b x ↦ by simp [act, X.rm.add, MonObj.comp_mul])
    (fun i ↦ toUnit (Over.mk t) ≫ p i) q
    (fun i ↦ by rw [← MonObj.comp_pow, hp, MonObj.comp_one]) hq
    (fun a b h ↦ inj Ω t a b (by simpa [act] using h)) iq sq
  intro y hy
  obtain ⟨a, b, h⟩ := key y hy
  exact ⟨a, b, by simpa [act] using h⟩

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLocIsoSquareZeroSmoothLiftSystems
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.LocalIsomorphism

theorem fix_of_mem {R B B₀ : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B₀]
    (I : Ideal R) (hJ : I.map (algebraMap R B) ^ 2 = 0) (p : B →+* B₀)
    (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (e : B →ₐ[R] B) (he : ∀ b, p (e b) = p b)
    (x : B) (hx : x ∈ I.map (algebraMap R B)) : e x = x := by
  set J := I.map (algebraMap R B) with hJdef
  have hδ : ∀ y, e y - y ∈ J := fun y ↦ (hker _).1 (by rw [map_sub, he, sub_self])
  have hsq : ∀ a ∈ J, ∀ b ∈ J, a * b = 0 := fun a ha b hb ↦ by
    have : a * b ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hJ] at this
    simpa using this
  let T : Ideal B :=
    { carrier := {x | ∀ y, e (x * y) = x * y}
      add_mem' := fun {a b} ha hb y ↦ by simp only [Set.mem_setOf_eq] at *; rw [add_mul, map_add, ha, hb]
      zero_mem' := fun y ↦ by simp
      smul_mem' := fun c {a} ha y ↦ by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        rw [mul_assoc, mul_left_comm, ha, mul_left_comm] }
  have hIT : J ≤ T := by
    rw [hJdef, Ideal.map_le_iff_le_comap]
    intro r hr y
    show e (algebraMap R B r * y) = algebraMap R B r * y
    have hr' : algebraMap R B r ∈ J := Ideal.mem_map_of_mem _ hr
    rw [map_mul, AlgHom.commutes]
    have h0 := hsq _ hr' _ (hδ y)
    rw [mul_sub] at h0
    exact sub_eq_zero.1 h0
  have := hIT hx 1
  simpa using this

theorem bij {R B B₀ : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B₀]
    (I : Ideal R) (hJ : I.map (algebraMap R B) ^ 2 = 0) (p : B →+* B₀)
    (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (e : B →ₐ[R] B) (he : ∀ b, p (e b) = p b) :
    Function.Bijective e := by
  have hδ : ∀ y, e y - y ∈ I.map (algebraMap R B) := fun y ↦ (hker _).1 (by rw [map_sub, he, sub_self])
  refine ⟨(injective_iff_map_eq_zero e).2 fun b hb ↦ ?_, fun c ↦ ?_⟩
  · have hb' : b ∈ I.map (algebraMap R B) := (hker b).1 (by rw [← he, hb, map_zero])
    rw [← fix_of_mem I hJ p hker e he b hb', hb]
  · refine ⟨c - (e c - c), ?_⟩
    rw [map_sub, fix_of_mem I hJ p hker e he _ (hδ c)]
    ring

theorem nil {R C D : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing D] [Algebra R D] (I : Ideal R)
    (q : C →ₐ[R] D) (h : ∀ b, q b = 0 ↔ b ∈ I.map (algebraMap R C)) (h2 : I.map (algebraMap R C) ^ 2 = 0) :
    IsNilpotent (RingHom.ker (q : C →+* D)) := ⟨2, by
  have : RingHom.ker (q : C →+* D) = I.map (algebraMap R C) := Ideal.ext fun b ↦ by
    rw [RingHom.mem_ker]; exact h b
  rw [this, h2]⟩

theorem exists_iso {R R₀ B B' B₀ : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B] [CommRing B']
    [Algebra R B'] [CommRing B₀] [Algebra R₀ B₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (p : B →+* B₀) (p' : B' →+* B₀) (hp : SemiHom π p) (hp' : SemiHom π p')
    (hs : Function.Surjective p) (hs' : Function.Surjective p')
    (hk : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (hk' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B'))
    [Algebra.FormallySmooth R B] [Algebra.FormallySmooth R B'] :
    ∃ φ : B ≃ₐ[R] B', ∀ b, p' (φ b) = p b := by
  letI : Algebra R B₀ := ((algebraMap R₀ B₀).comp π).toAlgebra
  let P : B →ₐ[R] B₀ := { p with commutes' := fun r ↦ hp.map_algebraMap r }
  let P' : B' →ₐ[R] B₀ := { p' with commutes' := fun r ↦ hp'.map_algebraMap r }
  have hJ := map_sq hI B
  have hJ' := map_sq hI B'
  let φ : B →ₐ[R] B' := Algebra.FormallySmooth.liftOfSurjective P P' hs' (nil I P' hk' hJ')
  let ψ : B' →ₐ[R] B := Algebra.FormallySmooth.liftOfSurjective P' P hs (nil I P hk hJ)
  have hφ : ∀ b, p' (φ b) = p b := fun b ↦
    Algebra.FormallySmooth.liftOfSurjective_apply P P' hs' (nil I P' hk' hJ') b
  have hψ : ∀ b, p (ψ b) = p' b := fun b ↦
    Algebra.FormallySmooth.liftOfSurjective_apply P' P hs (nil I P hk hJ) b
  have b1 := bij I hJ p hk (ψ.comp φ) fun b ↦ by simp [hψ, hφ]
  have b2 := bij I hJ' p' hk' (φ.comp ψ) fun b ↦ by simp [hψ, hφ]
  refine ⟨AlgEquiv.ofBijective φ ⟨fun x y h ↦ b1.1 (by simp [h]), fun c ↦ ?_⟩, hφ⟩
  obtain ⟨d, hd⟩ := b2.2 c
  exact ⟨ψ d, hd⟩

end GlobalTheory.LiftSys.LocalIsomorphism

namespace GlobalTheory.LiftSys

theorem locIso_nonempty : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀),
    ∀ S S' : Sys I π s₀, Nonempty (S.LocIso S') := by
  intro R R₀ _ _ I hI π _ _ X₀ s₀ S S'
  have h : ∀ U, ∃ φ : S.F.obj U ≃ₐ[R] S'.F.obj U, ∀ b, S'.p U (φ b) = S.p U b := fun U ↦ by
    haveI := (S.smooth U).formallySmooth
    haveI := (S'.smooth U).formallySmooth
    exact LocalIsomorphism.exists_iso I hI π (S.p U) (S'.p U) (S.semi U) (S'.semi U) (S.surj U) (S'.surj U)
      (S.ker U) (S'.ker U)
  exact ⟨⟨fun U ↦ (h U).choose, fun U ↦ (h U).choose_spec⟩⟩

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLocalEquationEqUniformiserPowClassicalPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.EqNormAt

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem norm_val_eqAt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (D : GlobalTheory.EffCartierData M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ϖ : V) (a : ℕ) (ξ : Sp V ⟶ M.Z) (p : ℕ) [Fact p.Prime] (ι : FractionRing V →+* PadicAlgCl p) (j : V →+* OO p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ v, (j v : PadicAlgCl p) = ι (algebraMap V (FractionRing V) v)) → idlAlong D.idealSheaf ξ = Ideal.span {ϖ ^ a} → ∀ f, EqAt M D (ξ (closedPoint V)) f → ‖M.val (gPt p ≫ spMap j ≫ ξ) f‖ = ‖ι (algebraMap V (FractionRing V) ϖ)‖ ^ a := by
  intro o Ω _ _ _ M D V _ _ _ ϖ a ξ p _ ι j hι hj hid f hf
  obtain ⟨i, hxi, rfl⟩ := hf
  set z := ξ (closedPoint V) with hz
  set e : V := (Scheme.stalkClosedPointTo ξ).hom ((M.Z.presheaf.germ _ z hxi).hom (D.f i)) with he
  have key : Ideal.span {e} = Ideal.span {ϖ ^ a} := by
    rw [← hid, idlAlong, D.stalkId_idealSheaf i z hxi, Ideal.map_span, Set.image_singleton]
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton).1 key

  have hval : M.val (gPt p ≫ spMap j ≫ ξ) (valF M.pt (D.U i) (D.f i)) = ((j e : OO p) : PadicAlgCl p) := by
    rw [← Category.assoc, gPt, spectrumMap_comp, RatModel.val_spMap_comp _ ξ (specializes_rfl : z ⤳ z)
      ⟨valF M.pt (D.U i) (D.f i), RatModel.valF_mem_O hxi _⟩]
    have hv : M.valLoc ξ z specializes_rfl ⟨valF M.pt (D.U i) (D.f i), RatModel.valF_mem_O hxi _⟩ = e := by
      simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        ← RatModel.stalkEquiv_germ hxi, RingEquiv.symm_apply_apply, TopCat.Presheaf.stalkSpecializes_refl,
        Category.id_comp, he]
      rw [Category.id_comp]
    rw [RingHom.comp_apply, hv]
    rfl
  rw [hval, hj]
  have hunit : ∀ w : Vˣ, ‖ι (algebraMap V (FractionRing V) (w : V))‖ = 1 := by
    intro w
    have h1 := (hι _).2 ⟨(w : V), rfl⟩
    have h2 := (hι _).2 ⟨((w⁻¹ : Vˣ) : V), rfl⟩
    have h3 : ‖ι (algebraMap V (FractionRing V) (w : V))‖ * ‖ι (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (ι (algebraMap V (FractionRing V) (w : V))),
      norm_nonneg (ι (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V)))]
  have he' : e = ϖ ^ a * ((u⁻¹ : Vˣ) : V) := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [he', map_mul, map_mul, norm_mul, hunit, mul_one, map_pow, map_pow, norm_pow]

end GlobalTheory.Poinc.EqNormAt
end

