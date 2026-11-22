import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibres
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.ZM GlobalTheory.AbLaw.CubeGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AddFib

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

def quad {Z : Over S} (x x' : Z ⟶ A) (y : Z ⟶ T) : Fin 4 → (Z.left ⟶ (A ⊗ T).left) :=
  ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left, (lift 1 y).left]

abbrev uquad (A T : Over S) [GrpObj A] : Fin 4 → ((A ⊗ (A ⊗ T)).left ⟶ (A ⊗ T).left) :=
  quad (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)

theorem comp_quad {Z Z' : Over S} (r : Z' ⟶ Z) (x x' : Z ⟶ A) (y : Z ⟶ T) (i : Fin 4) :
    r.left ≫ quad x x' y i = quad (r ≫ x) (r ≫ x') (r ≫ y) i := by
  fin_cases i <;>
  · simp only [quad, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
    rw [← Over.comp_left, comp_lift]
    try simp only [MonObj.comp_mul, MonObj.comp_one]

theorem prod_quad {Z : Over S} {x x' : Z ⟶ A} (y : Z ⟶ T) (h : x = 1 ∨ x' = 1)
    (U : Type) [CommGroup U] (k : (Z.left ⟶ (A ⊗ T).left) → U) :
    ∏ i, k (quad x x' y i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  rcases h with rfl | rfl
  · simp [Fin.prod_univ_four, quad, -Over.comp_left]
  · simp [Fin.prod_univ_four, quad, -Over.comp_left, mul_comm]

theorem homMk_comp_eq_one {Y : Over S} {Z : Scheme.{0}} (r : Z ⟶ Y.left) (u : Y ⟶ A) (b : Z ⟶ S)
    (h : r ≫ u.left = b ≫ η[A].left) : (Over.homMk r rfl : Over.mk (r ≫ Y.hom) ⟶ Y) ≫ u = 1 := by
  have hb : b = r ≫ Y.hom := by
    have := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at this
    exact (this.trans (Category.comp_id _)).symm
  apply Over.OverMorphism.ext
  rw [Hom.one_def]
  exact h.trans (by rw [hb]; rfl)

theorem formal_quad {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ (A ⊗ T)).left) (b : Z ⟶ S)
    (h : r ≫ (fst A (A ⊗ T)).left = b ≫ η[A].left ∨ r ≫ (snd A (A ⊗ T) ≫ fst A T).left = b ≫ η[A].left)
    (U : Type) [CommGroup U] (k : (Z ⟶ (A ⊗ T).left) → U) :
    ∏ i, k (r ≫ uquad A T i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  have e : ∀ i, r ≫ uquad A T i = quad ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ fst A (A ⊗ T))
      ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ snd A (A ⊗ T) ≫ fst A T)
      ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ snd A (A ⊗ T) ≫ snd A T) i :=
    fun i ↦ comp_quad (Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) _ _ _ i
  simp only [e]
  exact prod_quad _ (h.imp (homMk_comp_eq_one r _ b) (homMk_comp_eq_one r _ b)) U k

theorem triv_quad_iff {N : LB (A ⊗ T).left} (hN : N.IsLB) {Z : Over S} (x x' : Z ⟶ A) (y : Z ⟶ T) :
    Triv (LB.LinComb N (quad x x' y) ![1, -1, -1, 1]) ↔
      evc hN (x * x') y - evc hN x y - evc hN x' y + evc hN 1 y = 0 := by
  refine (cls_eq_zero_iff (LB.isLB_linComb hN _ _)).symm.trans ?_
  rw [cls_linComb hN, Fin.sum_univ_four]
  have e : ∀ a b c d : Pic Z.left, (1 : ℤ) • a + (-1 : ℤ) • b + (-1 : ℤ) • c + (1 : ℤ) • d = a - b - c + d :=
    fun a b c d ↦ by simp only [one_smul, neg_smul]; abel
  simp only [quad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
  rw [e]
  rfl

omit [GrpObj A] in

theorem exists_chart {X : Scheme.{0}} (j : X ⟶ T.left) :
    ∃ q : ((Over.pullback (j ≫ T.hom)).obj A ⊗ (Over.pullback (j ≫ T.hom)).obj A).left ⟶ (A ⊗ (A ⊗ T)).left,
      IsPullback q ((Over.pullback (j ≫ T.hom)).obj A ⊗ (Over.pullback (j ≫ T.hom)).obj A).hom
        (snd A (A ⊗ T) ≫ snd A T).left j ∧
      q ≫ (fst A (A ⊗ T)).left =
        (fst _ _ : _ ⟶ (Over.pullback (j ≫ T.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ T.hom) ∧
      q ≫ (snd A (A ⊗ T) ≫ fst A T).left =
        (snd _ _ : _ ⟶ (Over.pullback (j ≫ T.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ T.hom) := by
  set B := (Over.pullback (j ≫ T.hom)).obj A
  have hB : IsPullback (pullback.fst A.hom (j ≫ T.hom)) B.hom A.hom (j ≫ T.hom) := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback _ _
  have h3 : IsPullback (fst A (A ⊗ T)).left (snd A (A ⊗ T)).left A.hom (A ⊗ T).hom := IsPullback.of_hasPullback _ _
  have hBB : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  obtain ⟨m, m₁, m₂⟩ : ∃ m : B.left ⟶ (A ⊗ T).left, m ≫ (fst A T).left = pullback.fst A.hom (j ≫ T.hom) ∧
      m ≫ (snd A T).left = B.hom ≫ j :=
    ⟨h2.lift _ _ (by rw [hB.w, Category.assoc]), h2.lift_fst _ _ _, h2.lift_snd _ _ _⟩
  have hm : IsPullback m B.hom (snd A T).left j := IsPullback.of_right (by rw [m₁]; exact hB) m₂ h2
  have mw : m ≫ (A ⊗ T).hom = B.hom ≫ j ≫ T.hom := by
    rw [← Over.w (snd A T), ← Category.assoc, m₂, Category.assoc]
  have ho : IsPullback ((fst B B).left ≫ pullback.fst A.hom (j ≫ T.hom)) (snd B B).left A.hom
      (m ≫ (A ⊗ T).hom) := by
    rw [mw]; exact hBB.paste_horiz hB
  obtain ⟨q, q₁, q₂⟩ : ∃ q : (B ⊗ B).left ⟶ (A ⊗ (A ⊗ T)).left,
      q ≫ (fst A (A ⊗ T)).left = (fst B B).left ≫ pullback.fst A.hom (j ≫ T.hom) ∧
      q ≫ (snd A (A ⊗ T)).left = (snd B B).left ≫ m :=
    ⟨h3.lift _ _ (by rw [ho.w, Category.assoc]), h3.lift_fst _ _ _, h3.lift_snd _ _ _⟩
  have hq : IsPullback q (snd B B).left (snd A (A ⊗ T)).left m :=
    IsPullback.of_right (by rw [q₁]; exact ho) q₂ h3
  refine ⟨q, ?_, q₁, ?_⟩
  · rw [← Over.w (snd B B)]
    exact hq.paste_vert hm
  · show q ≫ (snd A (A ⊗ T)).left ≫ (fst A T).left = _
    rw [← Category.assoc, q₂, Category.assoc, m₁]

theorem isAdditive_of_geomFibres (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left]
    (hA : IsAbelianScheme A) (N : LB (A ⊗ T).left) (hN : N.IsLB) (h0 : Triv (ev N (1 : T ⟶ A) (𝟙 T)))
    (hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ T),
      IsAdditive (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t))) : IsAdditive N := by
  have hG : Out.GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  have := hA.geomConnected
  have := hA.smooth
  have := hA.proper
  have one₁ : ∀ {Z : Over S} (y : Z ⟶ T), evc hN (1 : Z ⟶ A) y = 0 := fun y ↦ by
    have e := congrArg (CechPic.pull y.left) ((triv_ev_iff hN _ _).1 h0)
    rwa [pull_evc, map_zero, Category.comp_id, MonObj.comp_one] at e
  have H := GlobalTheory.CubeNoeth.fibTriv_clopen N (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left
    (fun R _ _ j ↦ by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_chart (A := A) j
    have hB := isAb_baseChange hA (j ≫ T.hom)
    have one := one_left_fst (A := A) (j ≫ T.hom)
    let B := (Over.pullback (j ≫ T.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN' : (LB.LinComb N (fun k ↦ q ≫ uquad A T k) ![1, -1, -1, 1]).IsLB := DVR.linComb_isLB _ hN _ _
    have pf : ∀ M : LB (B ⊗ B).left, M.IsLB → Nonempty (Perf (B ⊗ B).hom M) := fun M hM ↦
      ProperFinite.nonempty_perf_of_isProper (R := R) (B ⊗ B).hom hM
    refine ⟨_, q, (B ⊗ B).hom, hq, TrivLocus.isClosed_trivLocus R _ _ _ hN' (pf _ hN') (pf _ (isLB_pw hN' _)) pr
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ sm gc),
      fun F _ g Z π f' ↦ CubeOpen.triv_basicOpen_of_triv_fibre hG Seesaw.seesaw
        (SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective)
        R B hB _ hN' (pf _ hN') ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hN _ (formal_quad _ (B.hom ≫ j ≫ T.hom) (Or.inr ?_))
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hN _ (formal_quad _ (B.hom ≫ j ≫ T.hom) (Or.inl ?_))
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have all : ∀ t, t ∈ fibTriv N (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left := fun t ↦ by
    let K := AlgebraicClosure (T.left.residueField t)
    let g : Spec (CommRingCat.of K) ⟶ T.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) ≫ T.left.fromSpecResidueField t
    let s : Sp K ⟶ S := g ≫ T.hom
    let t' : Over.mk s ⟶ T := Over.homMk g rfl
    have hadd := hgeo K s t'
    let π := pullback.fst (snd A (A ⊗ T) ≫ snd A T).left g
    let f' := pullback.snd (snd A (A ⊗ T) ≫ snd A T).left g
    refine ⟨K, inferInstance, g, _, π, f', ⟨IsLocalRing.closedPoint K, ?_⟩, IsPullback.of_hasPullback _ _, ?_⟩
    · have := (Scheme.range_fromSpecResidueField t).le
        ⟨Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) (IsLocalRing.closedPoint K), rfl⟩
      exact this
    let Zs : Over S := Over.mk (f' ≫ s)
    have w : π ≫ (A ⊗ (A ⊗ T)).hom = f' ≫ s := by
      rw [← Over.w (snd A (A ⊗ T) ≫ snd A T), ← Category.assoc, pullback.condition, Category.assoc]
    let x : Zs ⟶ A ⊗ (A ⊗ T) := Over.homMk π w
    let τ : Zs ⟶ Over.mk s := Over.homMk f' rfl
    have hx : x ≫ snd A (A ⊗ T) ≫ snd A T = τ ≫ t' := Over.OverMorphism.ext pullback.condition
    have hM : (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t')).IsLB := pull_isLB hN _
    have ev₁ : ∀ a : Zs ⟶ A, evc hM a τ = evc hN a (x ≫ snd A (A ⊗ T) ≫ snd A T) := fun a ↦ by
      rw [evc_ev hN, lift_fst, lift_snd_assoc, hx]
    have e := (isAdditive_iff hM).1 hadd Zs (x ≫ fst A (A ⊗ T)) (x ≫ snd A (A ⊗ T) ≫ fst A T) τ
    rw [ev₁, ev₁, ev₁] at e
    have ef : (fun k ↦ π ≫ uquad A T k) = quad (x ≫ fst A (A ⊗ T)) (x ≫ snd A (A ⊗ T) ≫ fst A T)
        (x ≫ snd A (A ⊗ T) ≫ snd A T) := funext fun k ↦ comp_quad x _ _ _ k
    unfold TrivAt
    rw [ef, triv_quad_iff hN, one₁, e]
    abel
  let e : T ⟶ A ⊗ (A ⊗ T) := lift 1 (lift 1 (𝟙 T))
  have e₀ : e ≫ fst A (A ⊗ T) = 1 := by simp [e]
  have e₂ : e ≫ snd A (A ⊗ T) ≫ snd A T = 𝟙 _ := by simp [e]
  have htr := triv_of_local hN (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left e.left
    (congrArg (fun q ↦ q.left) e₂) (fun Z b ↦ formal_quad (b ≫ e.left) (b ≫ T.hom) (Or.inl ?_))
    (fun V ↦ ?_) (fun s ↦ H.1 (all s))
  rotate_left
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_chart (A := A) V.ι
    have hB := isAb_baseChange hA (V.ι ≫ T.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2
  refine (isAdditive_iff hN).2 fun Y a a' t ↦ ?_
  have h1 : TrivAt N (uquad A T) ![1, -1, -1, 1] (lift a (lift a' t)).left := by
    have h0' : TrivAt N (uquad A T) ![1, -1, -1, 1] (𝟙 _) := by
      unfold TrivAt; simp only [Category.id_comp]; exact htr
    have := h0'.comp (lift a (lift a' t)).left
    rwa [Category.comp_id] at this
  have ef : (fun k ↦ (lift a (lift a' t)).left ≫ uquad A T k) = quad a a' t := funext fun k ↦ by
    rw [comp_quad]; simp only [lift_fst, lift_snd_assoc, lift_snd]
  have h2 : Triv (LB.LinComb N (quad a a' t) ![1, -1, -1, 1]) := by
    have h1' : Triv (LB.LinComb N (fun k ↦ (lift a (lift a' t)).left ≫ uquad A T k) ![1, -1, -1, 1]) := h1
    rwa [ef] at h1'
  have h3 := (triv_quad_iff hN a a' t).1 h2
  rw [one₁, add_zero, sub_sub, sub_eq_zero] at h3
  exact h3

end GlobalTheory.AddFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfIsPullback
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Obs.BaseChg

section Nat
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F F' : C ⥤ CommAlgCat.{0} R}

def ofNat (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (sm : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) : CoefMap (RingHom.id R) F F' where
  G := 𝟭 C
  α := α
  naturality := nat
  smul := sm

theorem ofNat_pull2_bijective (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (sm : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) (hb : ∀ T, Function.Bijective (α T)) :
    Function.Bijective (ofNat α nat sm).pull2 := by
  let e : ∀ T, F.obj T ≃+* F'.obj T := fun T ↦ RingEquiv.ofBijective (α T) (hb T)
  let β : ∀ T, F'.obj T →+* F.obj T := fun T ↦ (e T).symm.toRingHom
  have hβα : ∀ T b, β T (α T b) = b := fun T b ↦ (e T).symm_apply_apply b
  have hαβ : ∀ T b, α T (β T b) = b := fun T b ↦ (e T).apply_symm_apply b
  have natβ : ∀ {T T' : C} (a : T ⟶ T') (b : F'.obj T), β T' (mp F' a b) = mp F a (β T b) := fun a b ↦ by
    apply (hb _).1; rw [hαβ, nat, hαβ]
  have smβ : ∀ T (r : R) (b : F'.obj T), β T (r • b) = r • β T b := fun T r b ↦ by
    apply (hb T).1; rw [hαβ, sm, hαβ]
  have h1 : ∀ c, (ofNat β natβ smβ).pull2 ((ofNat α nat sm).pull2 c) = c := fun c ↦ by
    rw [← CoefMap.pullCohomologyTwo_comp]
    conv_rhs => rw [← CoefMap.pullCohomologyTwo_id c]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app := fun T ↦ 𝟙 T, naturality := fun _ _ f ↦ by dsimp [ofNat, CoefMap.comp, CoefMap.id]; simp } (fun T b ↦ by
      exact (mp_id F T b).trans (hβα T b).symm) c
  have h2 : ∀ c, (ofNat α nat sm).pull2 ((ofNat β natβ smβ).pull2 c) = c := fun c ↦ by
    rw [← CoefMap.pullCohomologyTwo_comp]
    conv_rhs => rw [← CoefMap.pullCohomologyTwo_id c]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app := fun T ↦ 𝟙 T, naturality := fun _ _ f ↦ by dsimp [ofNat, CoefMap.comp, CoefMap.id]; simp } (fun T b ↦ by
      exact (mp_id F' T b).trans (hαβ T b).symm) c
  exact ⟨fun x y hxy ↦ by rw [← h1 x, hxy, h1], fun y ↦ ⟨_, h2 y⟩⟩

end Nat

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}

theorem isAffineHom_of_isPullback (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : IsAffineHom pr :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip inferInstance

abbrev pre (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) : X₁.affineOpens :=
  haveI := isAffineHom_of_isPullback hp
  ⟨pr ⁻¹ᵁ U.1, U.2.preimage pr⟩

def preF (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : AffOp X₀ ⥤ AffOp X₁ :=
  (Monotone.functor (f := pre hp) fun _ _ h ↦ (show pr ⁻¹ᵁ _ ≤ pr ⁻¹ᵁ _ from
    fun _ hx ↦ (Subtype.coe_le_coe.2 h) hx)).op

abbrev pairOf (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) : Pair pr :=
  ⟨(pre hp U, U), le_rfl⟩

def secP (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) :
    Sec s₀ U.1 →+* Sec s₁ (pr ⁻¹ᵁ U.1) :=
  GlobalTheory.CechDR.secPull s₀ s₁ (pairOf hp U)

theorem pullbackSection_smul₂ (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (r : R₀)
    (b : Sec s₀ U.1) : secP hp U (r • b) = algebraMap R₀ R₁ r • secP hp U b :=
  semiHom_secPull hp.w (pairOf hp U) r b

def beta (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) :
    R₁ ⊗[R₀] Sec s₀ U.1 →+* Sec s₁ (pr ⁻¹ᵁ U.1) :=
  letI : Algebra R₀ (Sec s₁ (pr ⁻¹ᵁ U.1)) := ((algebraMap R₁ _).comp (algebraMap R₀ R₁)).toAlgebra
  haveI : IsScalarTower R₀ R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId R₁ _)
    { toRingHom := secP hp U
      commutes' := fun r ↦ by
        have := pullbackSection_smul₂ hp U r 1
        rw [map_one] at this
        change secP hp U (algebraMap R₀ _ r) = _
        rw [Algebra.algebraMap_eq_smul_one r, this, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
          Algebra.algebraMap_eq_smul_one r]
        exact (Algebra.algebraMap_eq_smul_one _).symm }
    (fun _ _ ↦ Commute.all _ _)).toRingHom

theorem beta_tmul (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (r : R₁)
    (b : Sec s₀ U.1) : beta hp U (r ⊗ₜ b) = algebraMap R₁ _ r * secP hp U b := by
  simp [beta]

theorem beta_smul (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (r : R₁)
    (x : R₁ ⊗[R₀] Sec s₀ U.1) : beta hp U (r • x) = r • beta hp U x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, beta_tmul, beta_tmul, map_mul, _root_.mul_assoc, Algebra.smul_def]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem beta_nat (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) {U V : AffOp X₀} (a : U ⟶ V)
    (x : (ext R₁ (OAff s₀)).obj U) :
    beta hp V.unop (mp (ext R₁ (OAff s₀)) a x) = mp (preF hp ⋙ OAff s₁) a (beta hp U.unop x) := by
  revert x
  change ∀ x : R₁ ⊗[R₀] Sec s₀ U.unop.1, _
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact (map_zero _).symm
  | tmul r b =>
    have hn := (pairPull hp.w).naturality
      (homOfLE (show pairOf hp V.unop ≤ pairOf hp U.unop from
        Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨fun _ hx ↦ (Subtype.coe_le_coe.2 (leOfHom a.unop) : V.unop.1 ≤ U.unop.1) hx,
          leOfHom a.unop⟩))).op b
    change beta hp V.unop (r ⊗ₜ mp (OAff s₀) a b) = mp (preF hp ⋙ OAff s₁) a (beta hp U.unop (r ⊗ₜ b))
    rw [beta_tmul, beta_tmul]
    erw [map_mul]
    congr 1
    all_goals first | exact ((Sec.res s₁ _).commutes r).symm | exact hn
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (map_add _ _ _).symm

def fwd (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) :
    CoefMap (RingHom.id R₁) (ext R₁ (OAff s₀)) (preF hp ⋙ OAff s₁) :=
  ofNat (fun U ↦ beta hp U.unop) (fun a x ↦ beta_nat hp a x) (fun U r x ↦ beta_smul hp U.unop r x)

section PairMaps
variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}

theorem comp_base_eq (hf : f₁ ≫ pr = pr' ≫ f₀) (y : Y₁) : pr.base (f₁.base y) = f₀.base (pr'.base y) := by
  have := congrArg (fun g : Y₁ ⟶ X₀ ↦ g.base y) hf
  simpa using this

abbrev preP (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) (p : Pair f₀) : Pair f₁ :=
  ⟨(pre hp' p.1.1, pre hp p.1.2), fun y hy ↦ by
    show pr.base (f₁.base y) ∈ p.1.2.1
    rw [comp_base_eq hf]; exact p.2 hy⟩

def preFP (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) :
    (Pair f₀)ᵒᵖ ⥤ (Pair f₁)ᵒᵖ :=
  (Monotone.functor (f := preP hp hp' hf) fun _ _ h ↦ Subtype.coe_le_coe.1 (Prod.le_def.2
    ⟨show pr' ⁻¹ᵁ _ ≤ pr' ⁻¹ᵁ _ from fun _ hx ↦ (Subtype.coe_le_coe.2 (Pair.le_fst h)) hx,
     show pr ⁻¹ᵁ _ ≤ pr ⁻¹ᵁ _ from fun _ hx ↦ (Subtype.coe_le_coe.2 (Pair.le_snd h)) hx⟩)).op

def zMap (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀)
    (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) :
    CoefMap (RingHom.id R₁) (preF hp ⋙ OAff s₁) (preFP hp hp' hf ⋙ OPair f₁ t₁) where
  G := pairSnd f₀
  α p := (pairPull h₁).α ((preFP hp hp' hf).obj p)
  naturality a b := (pairPull h₁).naturality ((preFP hp hp' hf).map a) b
  smul p r b := (pairPull h₁).smul ((preFP hp hp' hf).obj p) r b

def zRes (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) :
    CoefMap (RingHom.id R₁) (preF hp' ⋙ OAff t₁) (preFP hp hp' hf ⋙ OPair f₁ t₁) where
  G := pairFst f₀
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def kMap (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) :
    CoefMap (RingHom.id R₁) (ext R₁ (OPair f₀ t₀)) (preFP hp hp' hf ⋙ OPair f₁ t₁) :=
  ofNat (fun p ↦ beta hp' p.unop.1.1) (fun a x ↦ beta_nat hp' ((pairFst f₀).map a) x)
    (fun p r x ↦ beta_smul hp' _ r x)

end PairMaps

section Pointwise
variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}

theorem preF_cover (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hW : ∀ W : X₁.Opens, ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W) (x : X₁) (U : X₁.Opens) (hx : x ∈ U) :
    ∃ t : AffOp X₀, x ∈ ((preF hp).obj t).unop.1 ∧ ((preF hp).obj t).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := pr.base x) (U := W₀) hx
  exact ⟨Opposite.op ⟨V, hV⟩, hxV, fun y hy ↦ hVW hy⟩

theorem preF_dir (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hW : ∀ W : X₁.Opens, ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W) (t₁ t₂ : AffOp X₀) (x : X₁) (U : X₁.Opens)
    (hx : x ∈ U) (h₁ : x ∈ ((preF hp).obj t₁).unop.1) (h₂ : x ∈ ((preF hp).obj t₂).unop.1) :
    ∃ t₃ : AffOp X₀, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((preF hp).obj t₃).unop.1 ∧
      ((preF hp).obj t₃).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := pr.base x)
    (U := W₀ ⊓ t₁.unop.1 ⊓ t₂.unop.1) ⟨⟨hx, h₁⟩, h₂⟩
  exact ⟨Opposite.op ⟨V, hV⟩,
    ⟨(homOfLE (show (⟨V, hV⟩ : X₀.affineOpens) ≤ t₁.unop from fun y hy ↦ (hVW hy).1.2)).op⟩,
    ⟨(homOfLE (show (⟨V, hV⟩ : X₀.affineOpens) ≤ t₂.unop from fun y hy ↦ (hVW hy).2)).op⟩,
    hxV, fun y hy ↦ (hVW hy).1.1⟩

theorem preFP_cover (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀)
    (hW : ∀ W : Y₁.Opens, ∃ W₀ : Y₀.Opens, pr' ⁻¹ᵁ W₀ = W) (x : Y₁) (U : Y₁.Opens) (hx : x ∈ U) :
    ∃ t : (Pair f₀)ᵒᵖ, x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj t).unop.1 ∧
      ((preFP hp hp' hf ⋙ pairFst f₁).obj t).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f₀.base (pr'.base x))
    (U := (⊤ : X₀.Opens)) trivial
  obtain ⟨V', hV', hxV', hV'W⟩ := exists_isAffineOpen_mem_and_subset (x := pr'.base x)
    (U := W₀ ⊓ f₀ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨V', hV'⟩, ⟨V, hV⟩), fun z hz ↦ (hV'W hz).2⟩, hxV', fun z hz ↦ (hV'W hz).1⟩

theorem preFP_directed (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀)
    (hW : ∀ W : Y₁.Opens, ∃ W₀ : Y₀.Opens, pr' ⁻¹ᵁ W₀ = W) (a₁ a₂ : (Pair f₀)ᵒᵖ) (x : Y₁) (U : Y₁.Opens)
    (hx : x ∈ U) (h₁ : x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₁).unop.1)
    (h₂ : x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₂).unop.1) :
    ∃ a₃ : (Pair f₀)ᵒᵖ, Nonempty (a₁ ⟶ a₃) ∧ Nonempty (a₂ ⟶ a₃) ∧
      x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₃).unop.1 ∧ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₃).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  have g₁ : f₀.base (pr'.base x) ∈ a₁.unop.1.2.1 := a₁.unop.2 h₁
  have g₂ : f₀.base (pr'.base x) ∈ a₂.unop.1.2.1 := a₂.unop.2 h₂
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := f₀.base (pr'.base x))
    (U := a₁.unop.1.2.1 ⊓ a₂.unop.1.2.1) ⟨g₁, g₂⟩
  obtain ⟨V', hV', hxV', hV'W⟩ := exists_isAffineOpen_mem_and_subset (x := pr'.base x)
    (U := W₀ ⊓ a₁.unop.1.1.1 ⊓ a₂.unop.1.1.1 ⊓ f₀ ⁻¹ᵁ V) ⟨⟨⟨hx, h₁⟩, h₂⟩, hxV⟩
  let a₃ : Pair f₀ := ⟨(⟨V', hV'⟩, ⟨V, hV⟩), fun z hz ↦ (hV'W hz).2⟩
  refine ⟨Opposite.op a₃, ⟨(homOfLE (show a₃ ≤ a₁.unop from Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨fun z hz ↦ (hV'W hz).1.1.2, fun z hz ↦ (hVW hz).1⟩))).op⟩,
    ⟨(homOfLE (show a₃ ≤ a₂.unop from Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨fun z hz ↦ (hV'W hz).1.2, fun z hz ↦ (hVW hz).2⟩))).op⟩, hxV', fun z hz ↦ (hV'W hz).1.1.1⟩

end Pointwise

end GlobalTheory.Obs.BaseChg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageTranslatesSeparatedGrp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TransAff

theorem comp_mul_hom {R' : Type} [CommRing R'] {G' T T' : Over (Sp R')} [GrpObj G'] (x : T' ⟶ T) (f g : T ⟶ G') :
    x ≫ (f * g) = (x ≫ f) * (x ≫ g) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem comp_one_hom {R' : Type} [CommRing R'] {G' T T' : Over (Sp R')} [GrpObj G'] (x : T' ⟶ T) :
    x ≫ (1 : T ⟶ G') = 1 := by
  simp [Hom.one_def]

theorem comp_inv_eq (R' : Type) [CommRing R'] (G' : Over (Sp R')) [GrpObj G']
    (a : 𝟙_ (Over (Sp R')) ⟶ G') (b : 𝟙_ (Over (Sp R')) ⟶ G') (hab : a * b = 1) :
    (𝟙 G' * (toUnit G' ≫ a)) ≫ (𝟙 G' * (toUnit G' ≫ b)) = 𝟙 G' := by
  rw [comp_mul_hom, Category.comp_id, ← Category.assoc, toUnit_unique (_ ≫ toUnit G') (toUnit G'),
    _root_.mul_assoc, ← comp_mul_hom, hab, comp_one_hom, _root_.mul_one]

theorem isAffineOpen_translates :
    ∀ (R' : Type) [CommRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSeparated G'.hom → ∀ (a : 𝟙_ (Over (Sp R')) ⟶ G') (W : G'.left.Opens), IsAffineOpen W → IsAffineOpen ((𝟙 G' * (toUnit G' ≫ a)).left ⁻¹ᵁ W ⊓ (𝟙 G' * (toUnit G' ≫ a⁻¹)).left ⁻¹ᵁ W) := by
  intro R' _ G' _ hs a W hW
  have e1 := comp_inv_eq R' G' a a⁻¹ (mul_inv_cancel a)
  have e2 := comp_inv_eq R' G' a⁻¹ a (inv_mul_cancel a)
  have i1 : IsIso (𝟙 G' * (toUnit G' ≫ a)).left :=
    ⟨⟨(𝟙 G' * (toUnit G' ≫ a⁻¹)).left, by rw [← Over.comp_left, e1]; rfl,
      by rw [← Over.comp_left, e2]; rfl⟩⟩
  have i2 : IsIso (𝟙 G' * (toUnit G' ≫ a⁻¹)).left :=
    ⟨⟨(𝟙 G' * (toUnit G' ≫ a)).left, by rw [← Over.comp_left, e2]; rfl,
      by rw [← Over.comp_left, e1]; rfl⟩⟩
  have : IsSeparated G'.hom := hs
  have : G'.left.IsSeparated := ⟨by rw [← terminal.comp_from G'.hom]; infer_instance⟩
  exact (hW.preimage_of_isIso _).inf (hW.preimage_of_isIso _)

end GlobalTheory.TransAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralGeometricallyConnectedOpenModuliStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_geometricallyConnected_open_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens), GeometricallyConnected (U.ι ≫ toF Xo c) → IsIntegral U.toScheme := by
  first | exact @GlobalTheory.DetLine.isIntegral_open_of_geometricallyConnected | exact GlobalTheory.DetLine.isIntegral_open_of_geometricallyConnected | (intros; apply GlobalTheory.DetLine.isIntegral_open_of_geometricallyConnected <;> assumption)
end

