import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0018
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionFieldExt

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLeftInverse
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TensorAmple

open GlobalTheory.CechPic GlobalTheory.HermTensorLB

theorem exists_leftInverse {O : Type} [CommRing O] (bar : O →+* O) {M : Type} [AddCommGroup M] [Module O M]
    (h : M → M → O) (hadd : ∀ m m' n, h (m + m') n = h m n + h m' n)
    (hsmul : ∀ (c : O) m n, h (c • m) n = c * h m n) (hsym : ∀ m n, h n m = bar (h m n))
    (hperf : ∀ l : M →ₗ[O] O, ∃! n, ∀ m, l m = h m n) {n k : ℕ} (l : Fin k → (M →ₗ[O] O))
    (hl : ∀ m m', (n : O) * h m m' = ∑ i, l i m * bar (l i m')) :
    ∃ r : (Fin k → O) →ₗ[O] M, ∀ m, r (LinearMap.pi l m) = n • m := by
  choose e he using fun i => (hperf (l i)).exists
  let f : M → (M →ₗ[O] O) := fun y =>
    { toFun := fun x => h x y, map_add' := fun a b => hadd a b y, map_smul' := fun c a => hsmul c a y }
  refine ⟨Fintype.linearCombination O e, fun m => ?_⟩
  refine (hperf (f (n • m))).unique (fun x => ?_) (fun x => rfl)
  change h x (n • m) = h x _
  rw [hsym (n • m), hsym (Fintype.linearCombination O e _), Fintype.linearCombination_apply]
  change bar (f x (n • m)) = bar (f x _)
  rw [map_sum, map_nsmul, map_sum, map_nsmul]
  change n • bar (h m x) = ∑ i, bar (h (l i m • e i) x)
  simp only [hsmul, map_mul, ← hsym, ← he]
  rw [nsmul_eq_mul, hl]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem lam_self (laws : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}
    (x : T ⟶ P.A) : lam (cls P.L P.isLB) x x = 2 • pull x.left (cls P.L P.isLB) := by
  have h₂ := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 (laws.mulPull S P 2)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h₂
  have h₀ : pull (eSec P.A) (cls P.L P.isLB) = 0 := (cls_eq_zero_iff (pull_isLB P.isLB _)).2 P.rigid
  have h₁ : pull (1 : T ⟶ P.A).left (cls P.L P.isLB) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    exact (congrArg _ h₀).trans (map_zero _)
  have h₃ := congrArg (pull x.left) h₂
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_zsmul, ← pull_comp, Category.comp_id,
    ← Over.comp_left, Out.mulA, MonObj.comp_pow, map_zero, pow_two, MonObj.comp_mul] at h₃
  rw [lam, h₁, add_zero, ← sub_eq_zero, ← neg_eq_zero, ← h₃]
  push_cast
  abel

theorem relAmple_tensor : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) [IsCommMonObj P.A] (O : Type) [CommRing O] (bar : O →+* O) (M : Type) [AddCommGroup M] [Module O M] (h : M → M → O) [Module.Finite O M] [Module.Projective O M] (A : Over S) [GrpObj A] [IsCommMonObj A] (a : OAct O P.A) (b : OAct O A) (t : IsTensor A b P.A a M) (w : O) (N N' : LB A.left), N.IsLB → N'.IsLB → (∃ tθ : LB.Gen (Theta A N), tθ.IsGen) → (∀ m n, LBIso (cubeLB A ![fst P.A P.A ≫ t.tmul m, snd P.A P.A ≫ t.tmul n] N) (cubeLB P.A ![fst P.A P.A ≫ a.act (h m n), snd P.A P.A] P.L)) → (∀ c, LBIso (cubeLB P.A ![fst P.A P.A ≫ a.act c, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a.act (bar c)] P.L)) → ((∀ c, bar (bar c) = c) ∧ (∀ m m' n, h (m + m') n = h m n + h m' n) ∧ (∀ (c : O) m n, h (c • m) n = c * h m n) ∧ ∀ m n, h n m = bar (h m n)) → (∀ l : M →ₗ[O] O, ∃! n, ∀ m, l m = h m n) → (∃ (n k : ℕ) (l : Fin k → (M →ₗ[O] O)), 0 < n ∧ ∀ m m', (n : O) * h m m' = ∑ i, l i m * bar (l i m')) → w + bar w = 1 → LBIso N' (cubeLB A ![𝟙 A, b.act w] N) → Out.RelAmple A N' := by
  intro laws S _ P _ O _ bar M _ _ h _ _ A _ _ a b t w N N' hN hN' hT H hadj ⟨hbar, hadd, hsmul, hsym⟩ hperf
    ⟨n, k, l, hn, hl⟩ hw hiso
  have hL := P.isLB
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (laws.cube S P ⟨P.L, rig, hL, hrig⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  let q := Out.powIsPowGrp P.A k
  let ψ := t.mapLeft (IsTensor.pow q a) (LinearMap.pi l)
  let p : Fin k → (A ⟶ P.A) := fun i => ψ ≫ q.pr i
  have pl : ∀ i, IsLinearHom b a (p i) := fun i =>
    (t.isLinearHom_mapLeft _ _).comp (isLinearHom_pr q a i)
  have pm : ∀ i, IsMonHom (p i) := fun i => (pl i).1
  have hp : ∀ m i, t.tmul m ≫ p i = a.act (l i m) := fun m i => by simp [p, ψ]
  have am := a.hom
  have adj : ∀ {T : Over S} (x y : T ⟶ P.A) (c : O),
      lam (cls P.L hL) (x ≫ a.act c) y = lam (cls P.L hL) x (y ≫ a.act (bar c)) := by
    intro T x y c
    have h₀ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (hadj c)
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hL _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
  have base : ∀ {T : Over S} (x y : T ⟶ P.A) (m m' : M),
      lam (cls N hN) (x ≫ t.tmul m) (y ≫ t.tmul m') = lam (cls P.L hL) (x ≫ a.act (h m m')) y := by
    intro T x y m m'
    have h₀ := (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hL _ _)).2 (H m m')
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hN _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
  have key : ∀ {T : Over S} (x y : T ⟶ A),
      n • lam (cls N hN) x y = ∑ i, lam (cls P.L hL) (x ≫ p i) (y ≫ p i) := by
    intro T x y
    induction x using t.induction_on with
    | one => simp only [MonObj.one_comp, lam_one_left, smul_zero, Finset.sum_const_zero]
    | mul x x' hx hx' =>
      simp only [MonObj.mul_comp, lam_mul_left hN hT, lam_mul_left hL hΘ, smul_add, hx, hx', Finset.sum_add_distrib]
    | tmul m x =>
      induction y using t.induction_on with
      | one => simp only [MonObj.one_comp, lam_one_right, smul_zero, Finset.sum_const_zero]
      | mul y y' hy hy' =>
        simp only [MonObj.mul_comp, lam_mul_right hN hT, lam_mul_right hL hΘ, smul_add, hy, hy',
          Finset.sum_add_distrib]
      | tmul m' y =>
        let φ : O →+ Pic T.left := AddMonoidHom.mk' (fun c => lam (cls P.L hL) (x ≫ a.act c) y) fun c d => by
          simp only [a.add, MonObj.comp_mul, lam_mul_left hL hΘ]
        have hφ : ∀ c d, lam (cls P.L hL) (x ≫ a.act c) (y ≫ a.act d) = φ (c * bar d) := by
          intro c d
          have := adj (x ≫ a.act c) y (bar d)
          rw [hbar, Category.assoc, ← a.mul] at this
          exact this.symm
        simp only [Category.assoc, hp, hφ, ← map_sum, ← hl, base, ← nsmul_eq_mul, map_nsmul]
        rfl
  have dbl : ∀ x : A ⟶ P.A, 2 • lam (cls P.L hL) x (x ≫ a.act w) = 2 • pull x.left (cls P.L hL) := by
    intro x
    rw [two_nsmul, ← lam_self laws P x]
    nth_rw 2 [lam_comm]
    rw [adj, ← lam_mul_right hL hΘ, ← MonObj.comp_mul, ← a.add, hw, a.one, Category.comp_id]
  have hB : (Out.boxLB P.L q.pr).IsLB := LB.isLB_linComb hL _ _
  have hψB := pull_isLB hB ψ.left
  have final : LBIso (lbPow ((Out.boxLB P.L q.pr).pull ψ.left) 2) (lbPow N' (2 * n)) := by
    refine (cls_eq_iff (LB.isLB_linComb hψB _ _) (LB.isLB_linComb hN' _ _)).1 ?_
    rw [cls_lbPow hψB, cls_lbPow hN', cls_pull hB, cls_linComb hL,
      (cls_eq_iff hN' (LB.isLB_linComb hN _ _)).2 hiso]
    erw [cls_cube_two hN]
    rw [mul_smul, key, map_sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Category.id_comp, (pl i).comm, dbl, one_smul, ← pull_comp]
    rfl
  obtain ⟨r, hr⟩ := exists_leftInverse bar h hadd hsmul hsym hperf l hl
  have hfin : IsFinite ψ.left := GlobalTheory.T.tensor_map_finite_of_split laws S P O M A a b t n k _ r hn hr
  have hA : IsAbelianScheme A := t.isAbelianScheme P.isAb
  have hG : IsAbelianScheme (Out.powObj P.A k) := (IsTensor.pow q a).isAbelianScheme P.isAb
  have hid : IsFinite (𝟙 A : A ⟶ A).left := by rw [Over.id_left]; infer_instance
  have a₁ := (relAmple_finite_pow_iso S A _ ψ _ 1 one_pos hA hG hB hfin).1
    (relAmple_boxLB S _ P.A k q P.L hL P.ample)
  have a₂ := (relAmple_finite_pow_iso S A A (𝟙 A) _ 2 two_pos hA hA hψB hid).2.1.2 a₁
  have a₃ := (relAmple_finite_pow_iso S A A (𝟙 A) _ 1 one_pos hA hA (LB.isLB_linComb hψB _ _) hid).2.2.2 _
    (LB.isLB_linComb hN' _ _) final a₂
  exact (relAmple_finite_pow_iso S A A (𝟙 A) N' (2 * n) (by omega) hA hA hN' hid).2.1.1 a₃

end GlobalTheory.TensorAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNormalisedPolarisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

open GlobalTheory.PrimNorm GlobalTheory.MulPull

theorem exists_normalised_polarisation : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (P : Out.PolAV (Sp R)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A →
    LamEq P.L w (𝟙 P.A) P.L (𝟙 P.A) w' →
    ∃ L' : LB P.A.left, L'.IsLB ∧ Out.Rigidified P.A L' ∧ Out.Sym P.A L' ∧ Out.RelAmple P.A L' ∧ Out.KTriv P.A L' ∧
      LamEq L' (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) ∧ LBIso L' (cubeLB P.A ![𝟙 P.A, w] L') := by
  intro laws R _ _ P w w' hw hw' hs ha
  have : IsCommMonObj P.A := P.isAb.comm
  have hM := P.isLB
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := laws.cube _ P ⟨P.L, rig, hM, hrig⟩ rfl
  have hT : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨c.t, c.isGen⟩
  have ha' : LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] P.L)
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] P.L) := by
    simpa only [LamEq, Category.comp_id] using ha
  obtain ⟨Q, -, e, -, iso⟩ := exists_normalised_bundle laws.globalFns P.isAb hM hT w w' hs ha'
  have hc := fun T : Over (Sp R) => diff₃_ptCls (T := T) hM hT
  have hQ := Q.isLB
  have lam : LamEq Q.L (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) := iso _ _ _
  refine ⟨Q.L, hQ, ⟨Q.rig, Q.rigGen⟩, fun s => ⟨⊤, trivial, ?_⟩, ?_, kTriv_of_lamEq _ _ _ _ hM hQ lam P.ktriv, lam, ?_⟩
  · have h : HasGen Q.L (K := Fin 2) ![(GrpObj.inv (X := P.A)).left, 𝟙 _] ![1, -1] := by
      rw [e]
      refine hasGen_nested hM _ _ _ _ ?_
      rw [Fin.prod_univ_two]
      show normCls P.L w (GrpObj.inv (X := P.A)).left ^ (1 : ℤ) *
        normCls P.L w (𝟙 P.A : P.A ⟶ P.A).left ^ (-1 : ℤ) = 1
      have e : GrpObj.inv (X := P.A) = (𝟙 P.A)⁻¹ := by simp [Hom.inv_def]
      have e' : (𝟙 P.A)⁻¹ ≫ w = (𝟙 P.A ≫ w)⁻¹ := map_inv (postHom w P.A) _
      rw [normCls_left, normCls_left, e, e', diff₂_inv_inv (hc P.A), zpow_neg, zpow_one, mul_inv_cancel]
    have h' := h.pull (P.A.hom ⁻¹ᵁ ⊤).ι
    have e₁ : (fun k => (P.A.hom ⁻¹ᵁ ⊤).ι ≫ (![(GrpObj.inv (X := P.A)).left, 𝟙 _] : Fin 2 → _) k) =
        ![(P.A.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : P.A ⟶ P.A).left, (P.A.hom ⁻¹ᵁ ⊤).ι] := by
      funext k
      fin_cases k
      exacts [rfl, Category.comp_id _]
    rw [e₁] at h'
    exact h'
  · have one : ptCls P.L P.A 1 = 1 := by
      have h := (hasGen_iff hM _ _).1 (HasGen.pull (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1)
        ⟨rig, hrig⟩ (toUnit P.A).left)
      rw [Fintype.prod_unique, zpow_one] at h
      exact h
    have two : ptCls P.L P.A (𝟙 P.A * 𝟙 P.A) = ptCls P.L P.A (𝟙 P.A) ^ (4 : ℤ) := by
      have h := (hasGen_iff hM _ _).1 (laws.mulPull _ P 2)
      rw [Fin.prod_univ_two] at h
      have h' : ptCls P.L P.A (𝟙 P.A) ^ (((2 : ℕ) : ℤ) ^ 2) * ptCls P.L P.A (𝟙 P.A ^ 2) ^ (-1 : ℤ) = 1 := h
      rw [zpow_neg, zpow_one, mul_inv_eq_one, pow_two (𝟙 P.A)] at h'
      exact h'.symm
    have sq : LBIso (lbPow Q.L 2) (lbPow P.L 2) := by
      rw [e]
      refine lbIso_nested hM _ _ _ _ _ _ ?_
      refine (Fintype.prod_unique _).trans (Eq.trans ?_ (Fintype.prod_unique _).symm)
      show normCls P.L w (𝟙 P.A : P.A ⟶ P.A).left ^ ((2 : ℕ) : ℤ) = ptCls P.L P.A (𝟙 P.A) ^ ((2 : ℕ) : ℤ)
      rw [normCls_left, zpow_natCast, zpow_natCast, pow_two, Category.id_comp]
      have adj := diff₂_ptCls_adj hM ha' (𝟙 P.A) (𝟙 P.A)
      rw [Category.id_comp, Category.id_comp, diff₂_comm w] at adj
      nth_rewrite 2 [adj]
      rw [← diff₂_mul_right (hc P.A), hs, diff₂, one, two]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one, ofMul_zpow, ofMul_pow]
      abel
    have A₁ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb hM
      (show IsFinite (𝟙 P.A.left) from inferInstance)
    have A₂ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) Q.L 2 two_pos P.isAb P.isAb hQ
      (show IsFinite (𝟙 P.A.left) from inferInstance)
    have A₃ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) (lbPow P.L 2) 2 two_pos P.isAb P.isAb
      (DVR.linComb_isLB _ hM _ _) (show IsFinite (𝟙 P.A.left) from inferInstance)
    exact A₂.2.1.1 (A₃.2.2.2 _ (DVR.linComb_isLB _ hQ _ _) sq.symm (A₁.2.1.2 P.ample))
  · have := (iso P.A (𝟙 P.A) w).symm
    rwa [← e] at this

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldPointOfCountable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_numberField_factor (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k]
    {k₀ A : Type} [Field k₀] [CommRing A] (j : k₀ →+* k) (α : k₀ →+* A) (hα : α.FiniteType)
    (ψ : A →+* ℂ) (hψ : ∀ a, ψ (α a) = (j a : ℂ)) (halg : ∀ c, IsAlgebraic k (ψ c)) :
    ∃ (K₁ : IntermediateField ℚ ℂ) (hk : k ≤ K₁) (ψ₁ : A →+* K₁), FiniteDimensional ℚ K₁ ∧
      ψ₁.comp α = (IntermediateField.inclusion hk).toRingHom.comp j ∧
      (algebraMap K₁ ℂ).comp ψ₁ = ψ := by
  letI := α.toAlgebra
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (self := hα)
  haveI : Finite (ψ '' (t : Set A)) := (t.finite_toSet.image _).to_subtype
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (ψ '' (t : Set A))) := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨x, -, rfl⟩
    exact ((halg x).restrictScalars ℚ).isIntegral
  let K₁ : IntermediateField ℚ ℂ := k ⊔ IntermediateField.adjoin ℚ (ψ '' (t : Set A))
  have hk : k ≤ K₁ := le_sup_left
  have hmem : ∀ x, ψ x ∈ K₁ := by
    intro x
    have hx : x ∈ Algebra.adjoin k₀ (t : Set A) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact (le_sup_right : _ ≤ K₁) (IntermediateField.subset_adjoin ℚ _ ⟨x, hx, rfl⟩)
    | algebraMap r =>
      change ψ (α r) ∈ K₁
      rw [hψ]; exact hk (j r).2
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨K₁, hk, ψ.codRestrict K₁ hmem, IntermediateField.finiteDimensional_sup _ _, ?_, ?_⟩
  · ext a
    exact hψ a
  · rfl

theorem exists_fg_le_range_subset {k : Type} [Field k] [Algebra k ℂ] (R : Subalgebra k ℂ) (hR : R.FG)
    {X : Scheme.{0}} (y : Sp R ⟶ X) (U : X.Opens)
    (hU : (spMap R.val.toRingHom ≫ y) (IsLocalRing.closedPoint ℂ) ∈ U) :
    ∃ (R' : Subalgebra k ℂ) (h : R ≤ R'), R'.FG ∧
      Set.range (spMap (Subalgebra.inclusion h).toRingHom ≫ y) ⊆ (U : Set X) := by
  classical
  let p : PrimeSpectrum R := PrimeSpectrum.comap R.val.toRingHom (IsLocalRing.closedPoint ℂ)
  have hp : p ∈ ((y ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R)) := hU
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := ((y ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R))) hp (y ⁻¹ᵁ U).2
  have hr0 : (r : ℂ) ≠ 0 := by
    intro h
    have : r = 0 := Subtype.ext h
    subst this
    exact hr (Ideal.zero_mem _)
  obtain ⟨t, ht⟩ := hR
  have hle : R ≤ Algebra.adjoin k (↑(insert (r : ℂ)⁻¹ t) : Set ℂ) := by
    conv_lhs => rw [← ht]
    exact Algebra.adjoin_mono (by simp)
  refine ⟨_, hle, ⟨_, rfl⟩, ?_⟩
  rintro _ ⟨q, rfl⟩
  have hq : PrimeSpectrum.comap (Subalgebra.inclusion hle).toRingHom q ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    intro h
    have h' : Subalgebra.inclusion hle r ∈ q.asIdeal := h
    have hu : (r : ℂ)⁻¹ ∈ Algebra.adjoin k (↑(insert (r : ℂ)⁻¹ t) : Set ℂ) :=
      Algebra.subset_adjoin (by simp)
    have h1 : Subalgebra.inclusion hle r * ⟨_, hu⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hr0)
    exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ Ideal.mul_mem_right _ _ h'))
  exact hsub hq

theorem exists_numberField_point_of_countable :
    ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (R : Subalgebra k ℂ), R.FG → ∀ (k₀ : Type) [Field k₀] (j : k₀ →+* k) (X : Scheme.{0}) (s : X ⟶ Sp k₀) [LocallyOfFiniteType s] (y : Sp R ⟶ X), y ≫ s = spMap ((algebraMap k R).comp j) → Set.Countable (Set.range fun ρ : R →ₐ[k] ℂ => spMap ρ.toRingHom ≫ y) →
  ∃ (K₁ : IntermediateField ℚ ℂ) (hk : k ≤ K₁) (y₁ : Sp K₁ ⟶ X), FiniteDimensional ℚ K₁ ∧ y₁ ≫ s = spMap ((IntermediateField.inclusion hk).toRingHom.comp j) ∧ spMap (algebraMap K₁ ℂ) ≫ y₁ = spMap R.val.toRingHom ≫ y := by
  intro k _ R hR k₀ _ j X s _ y hy hc
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => (Spec.map_comp _ _).symm
  have hinj : ∀ {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}, spMap f = spMap g → f = g :=
    fun h => congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((spMap R.val.toRingHom ≫ y) (IsLocalRing.closedPoint ℂ))) isOpen_univ
  obtain ⟨R', hle, hR', hsub⟩ := exists_fg_le_range_subset R hR y U hxU
  have hU' : IsAffineOpen U := hU
  let A : Type := Γ(X, U)
  let i : Sp A ⟶ X := hU'.fromSpec
  haveI : IsOpenImmersion i := hU'.isOpenImmersion_fromSpec
  have hsub' : Set.range (spMap (Subalgebra.inclusion hle).toRingHom ≫ y) ⊆ Set.range i :=
    hsub.trans hU'.range_fromSpec.ge
  obtain ⟨φ, hφ⟩ : ∃ φ : A →+* R', spMap φ ≫ i = spMap (Subalgebra.inclusion hle).toRingHom ≫ y := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i _ hsub')
    exact ⟨φ.hom, (congrArg (· ≫ i) hφ).trans (IsOpenImmersion.lift_fac _ _ _)⟩
  obtain ⟨α, hα⟩ : ∃ α : k₀ →+* A, spMap α = i ≫ s := by
    obtain ⟨α, hα⟩ := Spec.map_surjective (i ≫ s)
    exact ⟨α.hom, hα⟩
  have hft : α.FiniteType := by
    have : LocallyOfFiniteType (spMap α) := by rw [hα]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hφα : φ.comp α = (Subalgebra.inclusion hle).toRingHom.comp ((algebraMap k R).comp j) := by
    apply hinj
    rw [← hcomp, hα, ← Category.assoc, hφ, Category.assoc, hy, hcomp]
  have hcnt : Set.Countable ((fun ψ : A →+* ℂ => spMap ψ ≫ i) ⁻¹'
      (Set.range fun ρ : R →ₐ[k] ℂ => spMap ρ.toRingHom ≫ y)) :=
    hc.preimage_of_injOn fun a _ b _ h => hinj ((cancel_mono i).1 h)
  have halg : ∀ c, IsAlgebraic k ((R'.val.toRingHom.comp φ) c) := by
    intro c
    refine IsAlgebraic.algHom R'.val (a := φ c) ?_
    refine (specialisation_numberField_and_countable_values k R' hR' (φ c) 1 one_ne_zero).2
      _ (hcnt.image fun ψ => ψ c) fun ρ => ⟨ρ.toRingHom.comp φ, ⟨ρ.comp (Subalgebra.inclusion hle), ?_⟩, rfl⟩
    change spMap (ρ.toRingHom.comp (Subalgebra.inclusion hle).toRingHom) ≫ y = spMap (ρ.toRingHom.comp φ) ≫ i
    rw [← hcomp, ← hcomp, Category.assoc, Category.assoc, hφ]
  obtain ⟨K₁, hk, ψ₁, hfd, h1, h2⟩ := exists_numberField_factor k j α hft (R'.val.toRingHom.comp φ)
    (fun a => congrArg Subtype.val (RingHom.congr_fun hφα a)) halg
  refine ⟨K₁, hk, spMap ψ₁ ≫ i, hfd, ?_, ?_⟩
  · rw [Category.assoc, ← hα, hcomp, h1]
  · rw [← Category.assoc, hcomp, h2, ← hcomp, Category.assoc, hφ, ← Category.assoc, hcomp]
    rfl

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldTorsionPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.TorsionField

theorem exists_field_alg (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (B : Type) [CommRing B] [Algebra k B]
    [Module.Finite k B] : ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧
      ∀ (φ : B →ₐ[k] ℂ) (b : B), φ b ∈ k₁ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := B)
  let S : Set ℂ := ⋃ b ∈ s, (minpoly k b).rootSet ℂ
  have hS : S.Finite := s.finite_toSet.biUnion fun b _ => Polynomial.rootSet_finite _ _
  have hint : ∀ b : B, _root_.IsIntegral k b := fun b => Algebra.IsIntegral.isIntegral b
  have hI : ∀ x ∈ S, _root_.IsIntegral k x := fun x hx => by
    simp only [S, Set.mem_iUnion] at hx
    obtain ⟨b, -, hb⟩ := hx
    exact ⟨minpoly k b, minpoly.monic (hint b), (Polynomial.mem_rootSet.1 hb).2⟩
  have : Finite S := hS
  have hfd : FiniteDimensional k (IntermediateField.adjoin k S) := IntermediateField.finiteDimensional_adjoin hI
  have hfd' : FiniteDimensional ℚ (IntermediateField.adjoin k S) := Module.Finite.trans k _
  refine ⟨(IntermediateField.adjoin k S).restrictScalars ℚ, hfd', fun x hx => ?_, fun φ b => ?_⟩
  · exact (IntermediateField.adjoin k S).algebraMap_mem ⟨x, hx⟩
  · change φ b ∈ IntermediateField.adjoin k S
    have hb : b ∈ Submodule.span k (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem b hb =>
      refine IntermediateField.subset_adjoin _ _ ?_
      simp only [S, Set.mem_iUnion]
      refine ⟨b, hb, Polynomial.mem_rootSet.2 ⟨minpoly.ne_zero (hint b), ?_⟩⟩
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact IntermediateField.smul_mem _ ha

theorem exists_field_finite (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (Z : Over (Sp k)) [IsFinite Z.hom] :
    ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧
      ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ y : Over.mk (spMap (algebraMap k ℂ)) ⟶ Z,
        ∃ y₂ : Over.mk (spMap (IntermediateField.inclusion h₂).toRingHom) ⟶ Z,
          spMap (algebraMap k₂ ℂ) ≫ y₂.left = y.left := by
  have : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let φ : CommRingCat.of k ⟶ Γ(Z.left, ⊤) := Spec.preimage (Z.left.isoSpec.inv ≫ Z.hom)
  have hφ : Spec.map φ = Z.left.isoSpec.inv ≫ Z.hom := Spec.map_preimage _
  have h₁ : φ.hom.Finite := by rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  let := φ.hom.toAlgebra
  have : Module.Finite k Γ(Z.left, ⊤) := h₁
  obtain ⟨k₁, hfd, hk, H⟩ := exists_field_alg k Γ(Z.left, ⊤)
  refine ⟨k₁, hfd, hk, fun k₂ h₂ h₁₂ y => ?_⟩
  let y' : Sp ℂ ⟶ Z.left := y.left
  have hy : y' ≫ Z.hom = spMap (algebraMap k ℂ) := Over.w y
  let ψ : Γ(Z.left, ⊤) ⟶ CommRingCat.of ℂ := Spec.preimage (y' ≫ Z.left.isoSpec.hom)
  have hψ : Spec.map ψ = y' ≫ Z.left.isoSpec.hom := Spec.map_preimage _
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap k ℂ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hy]
  have hc' : ∀ c : k, ψ.hom (φ.hom c) = (c : ℂ) := fun c => congrArg (fun f => f.hom c) hc
  let ψa : Γ(Z.left, ⊤) →ₐ[k] ℂ := { ψ.hom with commutes' := hc' }
  let ψ₂ : Γ(Z.left, ⊤) →+* k₂ := ψ.hom.codRestrict k₂ fun b => h₁₂ (H ψa b)
  refine ⟨Over.homMk (spMap ψ₂ ≫ Z.left.isoSpec.inv) ?_, ?_⟩
  · change (Spec.map (CommRingCat.ofHom ψ₂) ≫ Z.left.isoSpec.inv) ≫ Z.hom =
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h₂).toRingHom)
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext c
    exact hc' c
  · change Spec.map (CommRingCat.ofHom (algebraMap k₂ ℂ)) ≫ Spec.map (CommRingCat.ofHom ψ₂) ≫ Z.left.isoSpec.inv = y'
    rw [← Category.assoc, ← Spec.map_comp, Iso.comp_inv_eq, ← hψ]
    rfl

end GlobalTheory.TorsionField

namespace GlobalTheory

theorem exists_numberField_torsion_points : Out.Laws → ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (P : Out.PolAV (Sp k)) (n : ℕ), 0 < n → ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ x : Over.mk (spMap (algebraMap k ℂ)) ⟶ P.A, x ^ n = 1 → ∃! x₂ : Over.mk (spMap (IntermediateField.inclusion h₂).toRingHom) ⟶ P.A, spMap (algebraMap k₂ ℂ) ≫ x₂.left = x.left := by
  intro _ k _ P n hn
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    have h : IsUnit (n : k) := (Nat.cast_ne_zero.2 hn.ne').isUnit
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨-, hfin, -⟩ := GrpTangent.finiteEtale_mulN_torsion P.A (hG := P.isAb) hu
  obtain ⟨k₁, hfd, hk, H⟩ := TorsionField.exists_field_finite k (torsion P.A n)
  refine ⟨k₁, hfd, hk, fun k₂ h₂ h₁₂ x hx => ?_⟩
  obtain ⟨y, hy, -⟩ := LatticeTorsion.existsUnique_torsion P.A n x hx
  obtain ⟨y₂, hy₂⟩ := H k₂ h₂ h₁₂ y
  have : Flat (spMap (algebraMap k₂ ℂ)) := inferInstance
  have : Surjective (spMap (algebraMap k₂ ℂ)) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have : Epi (spMap (algebraMap k₂ ℂ)) := Flat.epi_of_flat_of_surjective _
  refine existsUnique_of_exists_of_unique ⟨y₂ ≫ torsion.ι P.A n, ?_⟩ fun a b ha hb => ?_
  · rw [← hy, Over.comp_left, Over.comp_left, ← hy₂]
    exact (Category.assoc _ _ _).symm
  · exact Over.OverMorphism.ext ((cancel_epi (spMap (algebraMap k₂ ℂ))).1 (ha.trans hb.symm))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosKeyArchAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF.KeyArch

theorem pos_of_isArchNorm (hU : ThetaUnifAV) (x : KeyIn ℂ) {nth nη : ℝ} (h : KeyPow.IsArchNorm x nth nη) :
    0 < nth ∧ 0 < nη := by
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  obtain ⟨u', τ, M, a, b, c, -, -, -, -, -, -, -, -, -, -, e⟩ :=
    keyIn_normal_form_and_archimedean_constant hU x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have p₁ : 0 ≤ nth :=
    h₆ ▸ div_nonneg (MeasureTheory.integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg
  have p₂ : 0 ≤ nη := h₇ ▸ by positivity
  have hne : ‖M.det ^ 4 / c ^ 8‖ * nth ^ 4 * nη ^ 2 ≠ 0 := by
    rw [e]; have := Real.pi_pos; positivity
  have q₁ := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have q₂ := right_ne_zero_of_mul hne
  exact ⟨p₁.lt_of_ne' fun h0 => q₁ (by rw [h0]; norm_num), p₂.lt_of_ne' fun h0 => q₂ (by rw [h0]; norm_num)⟩

theorem exists_pos_keyArchAt : ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (σ : K →+* ℂ), ∃ t n : ℝ, 0 < t ∧ 0 < n ∧ ∀ T abelian₂ : MLine K, T.n σ = t → abelian₂.n σ = n → KeyArchAt x T abelian₂ σ := by
  intro hU K _ _ x σ
  obtain ⟨x', hx⟩ := KeyPow.exists_keyPB x σ
  obtain ⟨nth, nη, h⟩ := KeyPow.exists_isArchNorm hU x'
  obtain ⟨p₁, p₂⟩ := pos_of_isArchNorm hU x' h
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨Real.sqrt nth, Real.sqrt nη⁻¹, Real.sqrt_pos.2 p₁, Real.sqrt_pos.2 (inv_pos.2 p₂), fun T abelian₂ hT hL =>
    ⟨x', u, Hm, W, χ, θ, Fd, hx, h₁, h₂, h₃, h₄, h₅, ?_, ?_⟩⟩
  · rw [hT, Real.sq_sqrt p₁.le, h₆]
  · rw [hL, Real.sq_sqrt (inv_pos.2 p₂).le, h₇, inv_div]

end GlobalTheory.LamF.KeyArch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionFieldExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_torsion_injective_weil_compatible : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (j : k →+* k') (t : Sp k ⟶ S), ∃ r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A), (∀ x, (r x).left = spMap j ≫ x.left) ∧ Function.Injective r ∧ (∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) ∧ ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → (Out.WeilIs P.A P.L n x y (unitOn c) ↔ Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c))) := by
  first | exact @GlobalTheory.exists_torsion_fieldExt | exact GlobalTheory.exists_torsion_fieldExt | (intros; apply GlobalTheory.exists_torsion_fieldExt <;> assumption)
end

