import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
import ReciprocityTheory.SemistableReduction.Bundle0025
import ReciprocityTheory.SemistableReduction.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialDoubleComplexDifferentials
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ

theorem fc_eq_δ (n : ℕ) (i : Fin (n + 2)) : fc (n + 1) n i = SimplexCategory.δ i := by
  ext j
  simp only [fc, clampHom, faceFun, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.coe_mk, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rcases Fin.lt_or_le (Fin.castSucc j) i with hj | hj
  · rw [Fin.succAbove_of_castSucc_lt _ _ hj]
    have : (j : ℕ) < i := hj
    simp only [this, if_true, Fin.coe_castSucc]
    have := j.isLt
    simp only [SimplexCategory.len_mk] at this ⊢
    omega
  · rw [Fin.succAbove_of_le_castSucc _ _ hj]
    have : ¬ (j : ℕ) < i := by simpa [Fin.le_iff_val_le_val] using hj
    simp only [this, if_false, Fin.val_succ]
    have := j.isLt
    simp only [SimplexCategory.len_mk] at this ⊢
    omega

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  simp [idc, clampHom, SimplexCategory.mkHom]
  omega

theorem hsum_f {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} {α : Type} (s : Finset α) (f : α → (K ⟶ L)) (i : ι) :
    (∑ x ∈ s, f x).f i = ∑ x ∈ s, (f x).f i :=
  (HomologicalComplex.eval C c i).map_sum f s

section
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem dbl_d_f (Y : SimplicialObject (SimplicialObject C)) (a b : ℕ) :
    ((dbl Y).d (a + 1) a).f b = (ev Y).map (dH (a + 1) b a b) := by
  simp only [dH, and_self, if_true, Functor.map_sum, Functor.map_zsmul, ev_map_bop,
    idc_self, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Finset.sum_range]
  dsimp only [dbl, alternatingFaceMapComplex]
  rw [AlternatingFaceMapComplex.obj_d_eq, hsum_f]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [HomologicalComplex.zsmul_f_apply, fc_eq_δ]
  rfl

theorem dbl_X_d (Y : SimplicialObject (SimplicialObject C)) (a b : ℕ) :
    ((dbl Y).X a).d (b + 1) b = (ev Y).map (dV a (b + 1) a b) := by
  simp only [dV, and_self, if_true, Functor.map_sum, Functor.map_zsmul, ev_map_bop,
    idc_self, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rw [Finset.sum_range]
  change (AlternatingFaceMapComplex.obj (Y.obj (op (SimplexCategory.mk a)))).d (b + 1) b = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [fc_eq_δ]
  rfl

variable [HasFiniteCoproducts C]

theorem ιTotal_D₁ (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (dbl Y).D₁ (ComplexShape.down ℕ) (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dH a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  rw [HomologicalComplex₂.ι_D₁]
  rcases a with _ | a
  · rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp)]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    have hx : ¬ (0 = x.1.1 + 1 ∧ b = x.1.2) := by omega
    simp only [dH, hx, if_false, Functor.map_zero]
    exact zero_comp
  · rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.down ℕ).Rel (a + 1) a from rfl) b k
      (by simp only [ComplexShape.π_def]; omega)]
    rw [Finset.sum_eq_single ⟨(a, b), by simp; omega⟩]
    · rw [dbl_d_f]
      simp
      rfl
    · rintro ⟨⟨x1, x2⟩, hx⟩ _ hne
      have : ¬ (a + 1 = x1 + 1 ∧ b = x2) := by
        rintro ⟨h1, h2⟩
        apply hne
        subst h2
        have : x1 = a := by omega
        subst this
        rfl
      simp only [dH, this, if_false, Functor.map_zero]
      exact zero_comp
    · intro hn
      exact absurd (Finset.mem_attach _ _) hn

theorem ιTotal_D₂ (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (dbl Y).D₂ (ComplexShape.down ℕ) (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, ((-1 : ℤ) ^ a) • ((ev Y).map (dV a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2)) := by
  rw [HomologicalComplex₂.ι_D₂]
  rcases b with _ | b
  · rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp)]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    have hx : ¬ (a = x.1.1 ∧ 0 = x.1.2 + 1) := by omega
    simp only [dV, hx, if_false, Functor.map_zero]
    exact (congrArg _ zero_comp).trans (zsmul_zero _)
  · rw [HomologicalComplex₂.d₂_eq _ _ a (show (ComplexShape.down ℕ).Rel (b + 1) b from rfl) k
      (by simp only [ComplexShape.π_def]; omega)]
    rw [Finset.sum_eq_single ⟨(a, b), by simp; omega⟩]
    · rw [dbl_X_d]
      simp
      rfl
    · rintro ⟨⟨x1, x2⟩, hx⟩ _ hne
      have : ¬ (a = x1 ∧ b + 1 = x2 + 1) := by
        rintro ⟨h1, h2⟩
        apply hne
        subst h1
        have : x2 = b := by omega
        subst this
        rfl
      simp only [dV, this, if_false, Functor.map_zero]
      exact (congrArg _ zero_comp).trans (zsmul_zero _)
    · intro hn
      exact absurd (Finset.mem_attach _ _) hn

theorem ιTotal_tot_d (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ)
    (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (tot Y).d (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  change _ ≫ ((dbl Y).total (ComplexShape.down ℕ)).d (k + 1) k = _
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add, ιTotal_D₁ Y a b k h, ιTotal_D₂ Y a b k h]
  refine Eq.trans Finset.sum_add_distrib.symm (Finset.sum_congr rfl (fun x _ => ?_))
  rw [dT, Functor.map_add, Functor.map_zsmul]
  first
    | (rw [Preadditive.add_comp, Preadditive.zsmul_comp])
    | (simp only [Preadditive.add_comp, Preadditive.zsmul_comp])
    | (erw [Preadditive.add_comp, Preadditive.zsmul_comp])
  rfl

end

end GlobalTheory.EZ

example : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1), (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫ (tot Y).d (k + 1) k = ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫ (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := @GlobalTheory.EZ.ιTotal_tot_d
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereProbZeroSetEqZero
section
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.SphereMeanNull

theorem exists_blockSphere_eval_ne_zero {B n : ℕ} (hn : 0 < n) {a : Fin B → ℕ}
    {g : MvPolynomial (Fin B × Fin n) ℂ} (hg0 : g ≠ 0) (hg : IsMultiHomogeneous a g) :
    ∃ u : BlockSphere B n, eval (blockPoint u) g ≠ 0 := by
  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hg0
  obtain ⟨z, hz1, hz⟩ := exists_torus_coeff_le g s
  set r : ℝ := (Real.sqrt n)⁻¹ with hrdef
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hnR)
  have hr2 : r ^ 2 * n = 1 := by
    rw [hrdef, inv_pow, Real.sq_sqrt hnR.le, inv_mul_cancel₀ hnR.ne']
  let u : BlockSphere B n := fun b => ⟨WithLp.toLp 2 (fun j => (r : ℂ) * z (b, j)), by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, hz1, mul_one]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm, hr2,
      Real.sqrt_one]⟩
  have hbp : blockPoint u = fun p => (r : ℂ) * z p := rfl
  have heval : eval (blockPoint u) g = (r : ℂ) ^ (∑ b, a b) * eval z g := by
    rw [hbp]; exact eval_mul_of_isMultiHomogeneous hg _ z
  have hne : eval z g ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (norm_pos_iff.mpr hs) hz)
  exact ⟨u, by rw [heval]; exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hr.ne')) hne⟩

theorem blockSphereProb_zeroSet_eq_zero : ∀ (B n : ℕ) (a : Fin B → ℕ)
    (g : MvPolynomial (Fin B × Fin n) ℂ), 0 < n → g ≠ 0 → IsMultiHomogeneous a g →
    blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by
  intro B n a g hn hg0 hg
  obtain ⟨u, hu⟩ := exists_blockSphere_eval_ne_zero hn hg0 hg
  exact null_of_logBound hn ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable
    (blockSphere_logMean_bound ReciprocityTheory.MultiplicativeHeights.Closed.sj ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable hn B)
    a g u hg hu

end GlobalTheory.SphereMeanNull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanQuasiIsoOfLocalQuasiIsoBoundedBelowDescent
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CartanOne

variable {T : Type 1} [Category.{0} T]

lemma nat_el {C D : T ⥤ AbCx} (φ : C ⟶ D) {U V : T} (g : U ⟶ V) (n : ℤ) (c : (C.obj U).X n) :
    (φ.app V).f n ((C.map g).f n c) = (D.map g).f n ((φ.app U).f n c) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, φ.naturality]

lemma comm_el {A B : AbCx} (f : A ⟶ B) (n m : ℤ) (a : A.X n) : f.f m (A.d n m a) = B.d n m (f.f n a) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, f.comm]

lemma map_comp_el (C : T ⥤ AbCx) {U V W : T} (g : U ⟶ V) (h : V ⟶ W) (n : ℤ) (c : (C.obj U).X n) :
    (C.map (g ≫ h)).f n c = (C.map h).f n ((C.map g).f n c) := by
  rw [Functor.map_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]

lemma hom_zero' {A B : AddCommGrpCat.{1}} (f : A ⟶ B) : f (0 : A) = 0 := map_zero f.hom

lemma locInj' {Cov : MorphismProperty T} {C D : T ⥤ AbCx} {φ : C ⟶ D} (h : LocInj Cov φ) (k m : ℤ) (hk : k + 1 = m)
    (U : T) (c : (C.obj U).X m) (hc : (C.obj U).d m (m + 1) c = 0)
    (hy : ∃ y : (D.obj U).X k, (φ.app U).f m c = (D.obj U).d k m y) :
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ b : (C.obj V).X k, (C.obj V).d k m b = (C.map g).f m c := by
  obtain rfl : k = m - 1 := by omega
  exact h m U c hc hy

lemma locSurj' {Cov : MorphismProperty T} {C D : T ⥤ AbCx} {φ : C ⟶ D} (h : LocSurj Cov φ) (k n : ℤ) (hk : k + 1 = n)
    (U : T) (z : (D.obj U).X n) (hz : (D.obj U).d n (n + 1) z = 0) :
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ (c : (C.obj V).X n) (y : (D.obj V).X k), (C.obj V).d n (n + 1) c = 0 ∧
      (φ.app V).f n c = (D.map g).f n z + (D.obj V).d k n y := by
  obtain rfl : k = n - 1 := by omega
  exact h n U z hz

theorem cartan_one : ∀ (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition]
    (C D : T ⥤ AbCx) (φ : C ⟶ D), (∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((C.obj U).X n) ∧ IsZero ((D.obj U).X n)) →
    Refines Cov (fun U X a => ∀ n, WExact (term C n) a ∧ WExact (term D n) a) → LocSurj Cov φ → LocInj Cov φ →
    ∀ U, SurjH (φ.app U) ∧ InjH (φ.app U) := by
  intro T _ Cov _ C D φ hb hR hS hI
  obtain ⟨K, p, q, hbij, hd⟩ := GlobalTheory.EtC.coneEl_exists T C D φ
  have ext : ∀ n U (x y : (K.obj U).X n), (p n).app U x = (p n).app U y → (q n).app U x = (q n).app U y → x = y :=
    fun n U x y h1 h2 => (hbij n U).1 (Prod.ext h1 h2)
  have mk : ∀ n U (c : (C.obj U).X (n + 1)) (z : (D.obj U).X n), ∃ x : (K.obj U).X n, (p n).app U x = c ∧ (q n).app U x = z := by
    intro n U c z
    obtain ⟨x, hx⟩ := (hbij n U).2 (c, z)
    exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  have dp := fun n U x => (hd n U x).1
  have dq := fun n U x => (hd n U x).2
  have natP : ∀ n {U V : T} (g : U ⟶ V) (x : (K.obj U).X n),
      (p n).app V ((K.map g).f n x) = (C.map g).f (n + 1) ((p n).app U x) :=
    fun n _ _ g x => NatTrans.naturality_apply (p n) g x
  have natQ : ∀ n {U V : T} (g : U ⟶ V) (x : (K.obj U).X n),
      (q n).app V ((K.map g).f n x) = (D.map g).f n ((q n).app U x) :=
    fun n _ _ g x => NatTrans.naturality_apply (q n) g x
  have cyc : ∀ n U (x : (K.obj U).X n), (C.obj U).d (n + 1) (n + 1 + 1) ((p n).app U x) = 0 →
      (φ.app U).f (n + 1) ((p n).app U x) + (D.obj U).d n (n + 1) ((q n).app U x) = 0 →
      (K.obj U).d n (n + 1) x = 0 := by
    intro n U x h1 h2
    apply ext
    · rw [dp, h1, neg_zero]; exact (hom_zero' _).symm
    · rw [dq, h2]; exact (hom_zero' _).symm

  have hbK : ∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((K.obj U).X n) := by
    obtain ⟨b, hb⟩ := hb
    refine ⟨b - 1, fun n hn U => ?_⟩
    have h1 := AddCommGrpCat.subsingleton_of_isZero (hb (n + 1) (by omega) U).1
    have h2 := AddCommGrpCat.subsingleton_of_isZero (hb n (by omega) U).2
    haveI : Subsingleton ((K.obj U).X n) :=
      ⟨fun x y => ext n U x y (@Subsingleton.elim _ h1 _ _) (@Subsingleton.elim _ h2 _ _)⟩
    exact AddCommGrpCat.isZero_of_subsingleton _

  have hRK : Refines Cov (fun U X a => ∀ n, WExact (term K n) a) := by
    intro U V g hg
    obtain ⟨X, a, h, hga, hQ⟩ := hR U V g hg
    refine ⟨X, a, h, hga, fun n => ?_⟩
    refine GlobalTheory.EtC.WExactProd.wexact_of_prod T U X a Bool (fun i => cond i (term C (n + 1)) (term D n)) (term K n)
      (fun i => match i with | true => p n | false => q n) ?_ ?_
    · intro W
      constructor
      · intro x y hxy
        exact ext n W x y (congrFun hxy true) (congrFun hxy false)
      · intro f
        obtain ⟨x, hx1, hx2⟩ := mk n W (f true) (f false)
        refine ⟨x, funext fun i => ?_⟩
        cases i
        · exact hx2
        · exact hx1
    · intro i
      cases i
      · exact (hQ n).2
      · exact (hQ (n + 1)).1

  have gen : ∀ (j : ℤ) (U : T) (x : (K.obj U).X (j + 1)), (K.obj U).d (j + 1) (j + 1 + 1) x = 0 →
      ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : (K.obj V).X j, (K.obj V).d j (j + 1) y = (K.map g).f (j + 1) x := by
    intro j U x hx
    obtain ⟨c, hc⟩ : ∃ c : (C.obj U).X (j + 1 + 1), (p (j + 1)).app U x = c := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : (D.obj U).X (j + 1), (q (j + 1)).app U x = z := ⟨_, rfl⟩
    have h1 : (C.obj U).d (j + 1 + 1) (j + 1 + 1 + 1) c = 0 := by
      have := dp (j + 1) U x
      rw [hx] at this
      erw [hom_zero'] at this
      rw [hc] at this
      exact neg_eq_zero.mp this.symm
    have h2 : (D.obj U).d (j + 1) (j + 1 + 1) z + (φ.app U).f (j + 1 + 1) c = 0 := by
      have := dq (j + 1) U x
      rw [hx] at this
      erw [hom_zero'] at this
      rw [hc, hz] at this
      exact (add_comm _ _).trans this.symm
    obtain ⟨V₁, g₁, hg₁, b, hb⟩ := locInj' hI (j + 1) (j + 1 + 1) rfl U c h1
      ⟨-z, by rw [map_neg]; exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h2)⟩
    obtain ⟨w, hw⟩ : ∃ w : (D.obj V₁).X (j + 1), (D.map g₁).f (j + 1) z + (φ.app V₁).f (j + 1) b = w := ⟨_, rfl⟩
    have hw0 : (D.obj V₁).d (j + 1) (j + 1 + 1) w = 0 := by
      rw [← hw, map_add, ← comm_el (D.map g₁), ← comm_el (φ.app V₁), hb, nat_el, ← map_add, h2, map_zero]
    obtain ⟨V₂, g₂, hg₂, c', y', hc', hy'⟩ := locSurj' hS j (j + 1) rfl V₁ w hw0
    obtain ⟨y, hyp, hyq⟩ := mk j V₂ (c' - (C.map g₂).f (j + 1) b) (-y')
    refine ⟨V₂, g₁ ≫ g₂, Cov.comp_mem _ _ hg₁ hg₂, y, ?_⟩
    apply ext
    · rw [dp, hyp, natP, hc, map_sub, hc', ← comm_el (C.map g₂), hb, map_comp_el, zero_sub, neg_neg]
    · rw [dq, hyp, hyq, natQ, hz, map_sub, map_neg, hy', ← hw, map_add, nat_el, map_comp_el]
      abel
  have hLK : LocExact Cov K := by
    have gen' : ∀ k n : ℤ, k + 1 = n → ∀ (U : T) (x : (K.obj U).X n), (K.obj U).d n (n + 1) x = 0 →
        ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : (K.obj V).X k, (K.obj V).d k n y = (K.map g).f n x := by
      intro k n hkn
      subst hkn
      exact gen k
    intro n U x hx
    exact gen' (n - 1) n (by omega) U x hx

  have exK : ∀ (U : T) (k n : ℤ), k + 1 = n → ∀ x : (K.obj U).X n, (K.obj U).d n (n + 1) x = 0 →
      ∃ y : (K.obj U).X k, (K.obj U).d k n y = x := by
    intro U k n hkn x hx
    obtain rfl : k = n - 1 := by omega
    exact GlobalTheory.CartanZero.cartan_zero T Cov K hbK hRK hLK U n x hx
  intro U
  constructor
  · have sg : ∀ (j : ℤ) (z : (D.obj U).X (j + 1)), (D.obj U).d (j + 1) (j + 1 + 1) z = 0 →
        ∃ (c : (C.obj U).X (j + 1)) (y : (D.obj U).X j), (C.obj U).d (j + 1) (j + 1 + 1) c = 0 ∧
          (φ.app U).f (j + 1) c = z + (D.obj U).d j (j + 1) y := by
      intro j z hz
      obtain ⟨x, hxp, hxq⟩ := mk (j + 1) U 0 z
      have hx : (K.obj U).d (j + 1) (j + 1 + 1) x = 0 :=
        cyc _ _ _ (by rw [hxp, map_zero]) (by rw [hxp, hxq, map_zero, zero_add, hz])
      obtain ⟨y, hy⟩ := exK U j (j + 1) rfl x hx
      obtain ⟨u, hu⟩ : ∃ u : (D.obj U).X j, (q j).app U y = u := ⟨_, rfl⟩
      obtain ⟨v, hv⟩ : ∃ v : (C.obj U).X (j + 1), (p j).app U y = v := ⟨_, rfl⟩
      refine ⟨v, -u, ?_, ?_⟩
      · have := dp j U y
        rw [hy, hxp, hv] at this
        exact neg_eq_zero.mp this.symm
      · have := dq j U y
        rw [hy, hxq, hu, hv] at this
        rw [map_neg, this]
        abel
    have sg' : ∀ k n : ℤ, k + 1 = n → ∀ (z : (D.obj U).X n), (D.obj U).d n (n + 1) z = 0 →
        ∃ (c : (C.obj U).X n) (y : (D.obj U).X k), (C.obj U).d n (n + 1) c = 0 ∧
          (φ.app U).f n c = z + (D.obj U).d k n y := by
      intro k n hkn
      subst hkn
      exact sg k
    intro n z hz
    exact sg' (n - 1) n (by omega) z hz
  · have ij : ∀ (j : ℤ) (c : (C.obj U).X (j + 1 + 1)), (C.obj U).d (j + 1 + 1) (j + 1 + 1 + 1) c = 0 →
        ∀ y : (D.obj U).X (j + 1), (φ.app U).f (j + 1 + 1) c = (D.obj U).d (j + 1) (j + 1 + 1) y →
        ∃ b : (C.obj U).X (j + 1), (C.obj U).d (j + 1) (j + 1 + 1) b = c := by
      intro j c hc y hy
      obtain ⟨x, hxp, hxq⟩ := mk (j + 1) U c (-y)
      have hx : (K.obj U).d (j + 1) (j + 1 + 1) x = 0 :=
        cyc _ _ _ (by rw [hxp, hc]) (by rw [hxp, hxq, map_neg, hy, add_neg_cancel])
      obtain ⟨y', hy'⟩ := exK U j (j + 1) rfl x hx
      obtain ⟨v, hv⟩ : ∃ v : (C.obj U).X (j + 1), (p j).app U y' = v := ⟨_, rfl⟩
      refine ⟨-v, ?_⟩
      have := dp j U y'
      rw [hy', hxp, hv] at this
      rw [map_neg]
      exact this.symm
    have ij' : ∀ i n : ℤ, i + 1 = n → ∀ c : (C.obj U).X n, (C.obj U).d n (n + 1) c = 0 →
        ∀ y : (D.obj U).X i, (φ.app U).f n c = (D.obj U).d i n y → ∃ b : (C.obj U).X i, (C.obj U).d i n b = c := by
      intro i n hin
      subst hin
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact ij j
    intro n c hc ⟨y, hy⟩
    exact ij' (n - 1) n (by omega) c hc y hy

end GlobalTheory.CartanOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveMapEqCechNerveOfPreservesWidePushouts
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConerveNerve

variable {T : Type 1} [Category.{0} T] (Ψ : T ⥤ PShᵒᵖ) {U V : T} (g : U ⟶ V) (J : Type) [HasWidePushout U (fun _ : J => V) (fun _ => g)]

def cmp : (Ψ.obj (widePushout U (fun _ : J => V) fun _ => g)).unop ⟶
    widePullback (Ψ.obj U).unop (fun _ : J => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) :=
  WidePullback.lift (Ψ.map (WidePushout.head _)).unop (fun i => (Ψ.map (WidePushout.ι _ i)).unop)
    (fun i => by rw [← unop_comp, ← Ψ.map_comp]; exact congrArg (fun k => (Ψ.map k).unop) (WidePushout.arrow_ι (fun _ : J => g) i))

@[reassoc (attr := simp)]
lemma cmp_π (i : J) : cmp Ψ g J ≫ WidePullback.π _ i = (Ψ.map (WidePushout.ι _ i)).unop := by
  simp only [cmp, WidePullback.lift_π]

@[reassoc (attr := simp)]
lemma cmp_base : cmp Ψ g J ≫ WidePullback.base _ = (Ψ.map (WidePushout.head _)).unop := by
  simp only [cmp, WidePullback.lift_base]

def coc : Cocone (WidePushoutShape.wideSpan U (fun _ : J => V) (fun _ => g) ⋙ Ψ) :=
  WidePushoutShape.mkCocone (X := op (widePullback (Ψ.obj U).unop (fun _ : J => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop)))
    (WidePullback.base _).op (fun i => (WidePullback.π _ i).op) (fun i => by
      apply Quiver.Hom.unop_inj
      exact WidePullback.π_arrow (fun _ : J => (Ψ.map g).unop) i)

lemma isIso_cmp [PreservesColimitsOfShape (WidePushoutShape J) Ψ] : IsIso (cmp Ψ g J) := by
  let hC := isColimitOfPreserves Ψ (colimit.isColimit (WidePushoutShape.wideSpan U (fun _ : J => V) (fun _ => g)))
  refine ⟨(hC.desc (coc Ψ g J)).unop, ?_, ?_⟩
  · apply Quiver.Hom.op_inj
    show hC.desc (coc Ψ g J) ≫ (cmp Ψ g J).op = 𝟙 _
    apply hC.hom_ext
    intro j
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (cmp Ψ g J).op) (hC.fac (coc Ψ g J) j)).trans ?_
    refine Eq.trans ?_ (Category.comp_id _).symm
    apply Quiver.Hom.unop_inj
    rcases j with _ | i
    · exact cmp_base Ψ g J
    · exact cmp_π Ψ g J i
  · apply WidePullback.hom_ext
    · intro i
      have := congrArg Quiver.Hom.unop (hC.fac (coc Ψ g J) (some i))
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg _ (cmp_π Ψ g J i)).trans ?_
      exact this.trans (Category.id_comp _).symm
    · have := congrArg Quiver.Hom.unop (hC.fac (coc Ψ g J) none)
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg _ (cmp_base Ψ g J)).trans ?_
      exact this.trans (Category.id_comp _).symm

end GlobalTheory.EtC.ConerveNerve

namespace GlobalTheory.EtC.ConerveNerve

theorem conerve_nerve : ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), ∃ e : ((((Arrow.mk g).cechConerve ⋙ Ψ).leftOp : Spc) ⟶ (Arrow.mk (Ψ.map g).unop).cechNerve), IsIso e ∧ e ≫ (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom = lev Ψ (coAug g) := by
  intro T _ _ Ψ hΨ U V g
  refine ⟨{ app := fun n => cmp Ψ g (Fin (n.unop.len + 1)), naturality := ?_ }, ?_, ?_⟩
  · intro m n f
    apply WidePullback.hom_ext
    · intro i
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine (congrArg _ (cmp_π Ψ g _ i)).trans ?_
      have hN : (Arrow.mk (Ψ.map g).unop).cechNerve.map f ≫ WidePullback.π (fun _ => (Arrow.mk (Ψ.map g).unop).hom) i =
          WidePullback.π (fun _ => (Arrow.mk (Ψ.map g).unop).hom) (f.unop.toOrderHom i) :=
        WidePullback.lift_π _ _ _ _ _
      refine Eq.trans ?_ (congrArg _ hN).symm
      refine Eq.trans ?_ (cmp_π Ψ g _ _).symm
      change (Ψ.map (WidePushout.ι _ i) ≫ Ψ.map ((Arrow.mk g).cechConerve.map f.unop)).unop = _
      refine (congrArg Quiver.Hom.unop (Ψ.map_comp _ _).symm).trans ?_
      exact congrArg (fun k => (Ψ.map k).unop) (by apply WidePushout.ι_desc)
    · refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine (congrArg _ (cmp_base Ψ g _)).trans ?_
      have hN : (Arrow.mk (Ψ.map g).unop).cechNerve.map f ≫ WidePullback.base (fun _ : Fin ((unop n).len + 1) => (Arrow.mk (Ψ.map g).unop).hom) =
          WidePullback.base (fun _ : Fin ((unop m).len + 1) => (Arrow.mk (Ψ.map g).unop).hom) := by
        apply WidePullback.lift_base
      refine Eq.trans ?_ (congrArg _ hN).symm
      refine Eq.trans ?_ (cmp_base Ψ g _).symm
      change (Ψ.map (WidePushout.head _) ≫ Ψ.map ((Arrow.mk g).cechConerve.map f.unop)).unop = _
      refine (congrArg Quiver.Hom.unop (Ψ.map_comp _ _).symm).trans ?_
      exact congrArg (fun k => (Ψ.map k).unop) (by apply WidePushout.head_desc)
  · have : ∀ n : SimplexCategoryᵒᵖ, IsIso (cmp Ψ g (Fin (n.unop.len + 1))) := fun n => by
      haveI := hΨ n.unop.len
      exact isIso_cmp Ψ g _
    exact (NatTrans.isIso_iff_isIso_app _).2 this
  · refine NatTrans.ext (funext fun n => ?_)
    exact cmp_base Ψ g _

end GlobalTheory.EtC.ConerveNerve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenSubgroupExhaustionStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V], Good V := by
  first | exact @GlobalTheory.KSp.good_of_finiteDimensional | exact GlobalTheory.KSp.good_of_finiteDimensional | (intros; apply GlobalTheory.KSp.good_of_finiteDimensional <;> assumption)
end

