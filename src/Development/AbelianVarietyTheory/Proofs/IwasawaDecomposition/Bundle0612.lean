import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0595

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDlogUniqueModuloP
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv tv_add tv_zero tv_smul)

namespace GlobalTheory.DlogEx

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {O : Type} [CommRing O] {x : Sp O ⟶ X} (R : Type) [CommRing R] [Algebra O R]

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

variable (x) in

def redEps : Over.mk (spMap (algebraMap O (DualNumber R)) ≫ x) ⟶ overAt x (DualNumber O) :=
  Over.homMk (spMap (dualMap (algebraMap O R))) (by
    show spMap (dualMap (algebraMap O R)) ≫ spMap (algebraMap O (DualNumber O)) ≫ x =
      spMap (algebraMap O (DualNumber R)) ≫ x
    rw [← Category.assoc, sp_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl'])

def red (v : TanM x t.G) : Over.mk (spMap (algebraMap O (DualNumber R)) ≫ x) ⟶ t.G := redEps x R ≫ tv v

theorem red_left (v : TanM x t.G) : (red R v).left = spMap (dualMap (algebraMap O R)) ≫ (tv v).left := rfl

theorem red_add (v w : TanM x t.G) : red R (v + w) = red R v * red R w := MonObj.comp_mul _ _ _

theorem red_zero : red R (0 : TanM x t.G) = 1 := MonObj.comp_one _

def epsAlg (a : R) : DualNumber R →ₐ[O] DualNumber R :=
  (TrivSqZeroExt.map (a • LinearMap.id : R →ₗ[R] R)).restrictScalars O

theorem red_smul (a : O) (v : TanM x t.G) :
    (red R (a • v)).left = spMap (epsAlg (O := O) R (algebraMap O R a)).toRingHom ≫ (red R v).left := by
  show spMap (dualMap (algebraMap O R)) ≫ spMap (epsMul a) ≫ (tv v).left =
    spMap _ ≫ spMap (dualMap (algebraMap O R)) ≫ (tv v).left
  rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
  congr 2
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap, epsMul, epsAlg, -Algebra.smul_def, mul_smul]

theorem red_nsmul (k : ℕ) (v : TanM x t.G) : red R (k • v) = red R v ^ k := by
  induction k with
  | zero => rw [zero_nsmul, red_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, red_add, ih, pow_succ]

theorem red_pow {q : ℕ} (hq : (q : R) = 0) (v : TanM x t.G) : red R v ^ q = 1 := by
  rw [← red_nsmul, ← Nat.cast_smul_eq_nsmul O, ← red_zero R, ← zero_smul O v]
  refine Over.OverMorphism.ext ?_
  rw [red_smul, red_smul, map_natCast, hq, map_zero]

variable [Module.Finite O (DualNumber R)] {q : ℕ} (hq : (q : R) = 0) (c : TorsChar t x q)

include hq

theorem chi_smul (a : O) (v : TanM x t.G) :
    (c.χ _ (red R (a • v)) : DualNumber R) = epsAlg (O := O) R (algebraMap O R a) (c.χ _ (red R v)) :=
  c.nat _ _ _ _ _ (red_pow R hq v) (red_smul R a v)

theorem chi_add (v w : TanM x t.G) : c.χ _ (red R (v + w)) = c.χ _ (red R v) * c.χ _ (red R w) := by
  rw [red_add]
  exact c.mul _ _ _ (red_pow R hq v) (red_pow R hq w)

theorem chi_zero : c.χ _ (red R (0 : TanM x t.G)) = 1 := by
  have h := chi_add R hq c 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem chi_fst (v : TanM x t.G) : (c.χ _ (red R v) : DualNumber R).fst = 1 := by
  have h := congrArg TrivSqZeroExt.fst (chi_smul R hq c 0 v)
  rw [zero_smul, chi_zero R hq c] at h
  simpa [epsAlg] using h.symm

def dlog : TanM x t.G →ₗ[O] R where
  toFun v := (c.χ _ (red R v) : DualNumber R).snd
  map_add' v w := by
    rw [chi_add R hq c, Units.val_mul, TrivSqZeroExt.snd_mul, chi_fst R hq c, chi_fst R hq c]
    simp [add_comm]
  map_smul' a v := by
    rw [chi_smul R hq c]
    simp [epsAlg, Algebra.smul_def]

omit hq

theorem dlog_exists_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (O : Type) [CommRing O] (x : Sp O ⟶ X) (p n : ℕ) (c : TorsChar t x (p ^ n)) (g : ℕ) (e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)), (∀ i, IsTanAtG t x (e i)) → (∃ h : Fin g → O, DlogIs t p n c e h) ∧ ∀ h h' : Fin g → O, DlogIs t p n c e h → DlogIs t p n c e h' → ∀ i, h i - h' i ∈ Ideal.span {(p : O) ^ n} := by
  intro E _ _ _ H X t O _ x p n c g e he
  classical
  have hq : ((p ^ n : ℕ) : O ⧸ Ideal.span {(p : O) ^ n}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : O) ^ n})), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.mem_span_singleton_self _
  constructor
  · choose h hh using fun i => Ideal.Quotient.mk_surjective (dlog _ hq c (LieMet.tanOf (he i)))
    refine ⟨h, fun a v hv w hw => ?_⟩
    have h1 := (LieMet.isComb_iff (fun i => LieMet.tanOf (he i)) a _).2 rfl
    have h2 : (tv (∑ i, a i • LieMet.tanOf (he i))).left = v :=
      ((isCombAtG_iff t x (fun j => ovT (he j)) a _).1 h1).symm.trans ((isCombAtG_iff t x (fun j => ovT (he j)) a _).1 hv)
    have h3 : w = red _ (∑ i, a i • LieMet.tanOf (he i)) := Over.OverMorphism.ext (by rw [hw, red_left, h2])
    rw [h3]
    show dlog _ hq c _ = _
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← hh, mul_comm]
    rfl
  · intro h h' hh hh' i
    have h1 := hh _ _ (isCombAtG_single t x he i) (red _ (LieMet.tanOf (he i))) rfl
    have h2 := hh' _ _ (isCombAtG_single t x he i) (red _ (LieMet.tanOf (he i))) rfl
    rw [← Ideal.Quotient.eq]
    simpa [Pi.single_apply] using h1.symm.trans h2

end GlobalTheory.DlogEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartRescaleFrameChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exists_isExpChart_rescale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) (ρ : ℝ) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), 0 < ρ → Metric.ball 0 ρ ⊆ e0.target → (∀ j, HolAlong e0.source fun x => e0 x j) → IsHolTo e0.target (fun z => (e0.symm z).1) → IsHolTo (Metric.ball 0 ρ ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) → (∀ x ∈ e0.source, ‖e0 x‖ < ρ → IsExpAt Z.t (x.1 ≫ genι Z) (ex x)) → DifferentiableOn ℂ A (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (A z).det) → ∃ (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex' : ExpMaps Z σ g), IsExpChart e ex' ∧ e.source = e0.source ∩ {x | ‖e0 x‖ < ρ} ∧ (∀ x ∈ e.source, e x = ρ⁻¹ • e0 x) ∧ ∀ x ∈ e.source, ∀ w, ex' x w = ex x (A (e0 x) *ᵥ w) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e0 ex ρ A hρ hball hhol hsymm hjoint hexp hA hdet
  have hss : ∀ z : Fin n → ℂ, (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ.ne')).symm z = ρ • z := fun z => by
    simp [Homeomorph.smulOfNeZero, Units.smul_def]
  have hnorm : ∀ z : Fin n → ℂ, ‖ρ • z‖ < ρ ↔ ‖z‖ < 1 := fun z => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact mul_lt_iff_lt_one_right hρ
  let e1 := e0.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : Fin n → ℂ) ρ) Metric.isOpen_ball)
  let hs : (Fin n → ℂ) ≃ₜ (Fin n → ℂ) := Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ.ne')
  let e := e1.transHomeomorph hs
  have he_app : ∀ x, e x = ρ⁻¹ • e0 x := fun x => rfl
  have he_symm : ∀ z, e.symm z = e0.symm (ρ • z) := fun z => by
    simp [e, e1, hs, Homeomorph.smulOfNeZero, Units.smul_def]
  have he_src : e.source = e0.source ∩ {x | ‖e0 x‖ < ρ} := by
    ext x
    simp [e, e1]
  have hss' : ∀ z, hs.symm z = ρ • z := hss
  have he_tgt : e.target = Metric.ball 0 1 := by
    ext z
    show z ∈ (e1.transHomeomorph hs).target ↔ _
    rw [OpenPartialHomeomorph.transHomeomorph_target, Set.mem_preimage, hss']
    show ρ • z ∈ (e0.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : Fin n → ℂ) ρ) Metric.isOpen_ball)).target ↔ _
    rw [OpenPartialHomeomorph.trans_target]
    show ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ρ • z ∈ e0.target ↔ _
    rw [mem_ball_zero_iff, mem_ball_zero_iff]
    constructor
    · rintro ⟨h, -⟩
      exact (hnorm z).1 h
    · intro h
      exact ⟨(hnorm z).2 h, hball (mem_ball_zero_iff.2 ((hnorm z).2 h))⟩
  have hsrc : ∀ x ∈ e.source, x ∈ e0.source ∧ ‖e0 x‖ < ρ := fun x hx => by
    rw [he_src] at hx
    exact hx
  refine ⟨e, fun x w => ex x (A (e0 x) *ᵥ w), ⟨he_tgt, ?_, ?_, ?_, ?_, ?_⟩, he_src, fun x _ => he_app x, fun _ _ _ => rfl⟩
  · intro k V _ _ _ B x hB hx hm
    have hd := hhol k V B x hB hx fun b hb => (hsrc _ (hm hb)).1
    refine (hd.const_mul ((ρ⁻¹ : ℝ) : ℂ)).congr fun b _ => ?_
    simp [he_app, Complex.real_smul]
  · rw [he_tgt]
    refine GlobalTheory.HolPeriods.isHolTo_congr (GlobalTheory.HolPeriods.isHolTo_comp hsymm Metric.isOpen_ball
      (φ := fun z => ρ • z) ?_ ?_) fun z _ => by rw [he_symm]
    · exact differentiableOn_id.const_smul ρ
    · intro z hz
      exact hball (mem_ball_zero_iff.2 ((hnorm z).2 (mem_ball_zero_iff.1 hz)))
  · intro x hx v w
    obtain ⟨h1, h2⟩ := hsrc x hx
    simp only [Matrix.mulVec_add]
    exact (hexp x h1 h2).1 _ _
  · rw [he_tgt]
    have hmaps : Set.MapsTo (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ρ • zw.1, A (ρ • zw.1) *ᵥ zw.2))
        (Metric.ball 0 1 ×ˢ Set.univ) (Metric.ball 0 ρ ×ˢ Set.univ) := fun zw hzw =>
      ⟨mem_ball_zero_iff.2 ((hnorm _).2 (mem_ball_zero_iff.1 hzw.1)), trivial⟩
    have hdiff : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ρ • zw.1, A (ρ • zw.1) *ᵥ zw.2))
        (Metric.ball 0 1 ×ˢ Set.univ) := by
      have h1 : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => ρ • zw.1) (Metric.ball 0 1 ×ˢ Set.univ) :=
        differentiableOn_fst.const_smul ρ
      refine h1.prodMk (differentiableOn_pi.2 fun i => ?_)
      simp only [Matrix.mulVec, dotProduct]
      refine DifferentiableOn.fun_sum fun j _ => ?_
      have hij : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => A (ρ • zw.1) i j)
          (Metric.ball 0 1 ×ˢ Set.univ) := by
        have hA2 : DifferentiableOn ℂ (fun z => (Matrix.of.symm (A z) : Fin g → Fin g → ℂ)) (Metric.ball 0 ρ) := hA
        have hL : DifferentiableOn ℂ (fun z => A z i j) (Metric.ball 0 ρ) :=
          differentiableOn_pi.1 (differentiableOn_pi.1 hA2 i) j
        exact hL.comp h1
          fun zw hzw => (hmaps hzw).1
      exact hij.mul (differentiableOn_pi.1 differentiableOn_snd j)
    refine GlobalTheory.HolPeriods.isHolTo_congr (GlobalTheory.HolPeriods.isHolTo_comp hjoint (Metric.isOpen_ball.prod isOpen_univ)
      hdiff hmaps) fun zw hzw => ?_
    have hz : ρ • zw.1 ∈ e0.target := hball (hmaps hzw).1
    simp only [he_symm, e0.right_inv hz]
    rw [he_symm]
  · intro x hx
    obtain ⟨h1, h2⟩ := hsrc x hx
    have hU : IsUnit (A (e0 x)).det := hdet _ (mem_ball_zero_iff.2 h2)
    let k := Matrix.toLinearEquiv' (A (e0 x)) (Matrix.invertibleOfIsUnitDet _ hU)
    have hk : ∀ w, k w = A (e0 x) *ᵥ w := fun _ => rfl
    have hD : ∀ w v, IsDerivAt0 (fun u => (ex x (A (e0 x) *ᵥ u)).left) w v ↔
        IsDerivAt0 (fun u => (ex x u).left) (A (e0 x) *ᵥ w) v := fun w v => by
      simpa only [hk] using GlobalTheory.HolPeriods.isDerivAt0_comp_equiv (fun u => (ex x u).left) k w v
    obtain ⟨-, hT1, hT2⟩ := hexp x h1 h2
    refine ⟨fun w => ?_, fun v hv => ?_⟩
    · simp only [hD]
      exact hT1 _
    · obtain ⟨w', hw', hu⟩ := hT2 v hv
      refine ⟨k.symm w', ?_, fun w hw => ?_⟩
      · beta_reduce
        rw [hD, ← hk, k.apply_symm_apply]
        exact hw'
      · beta_reduce at hw
        rw [hD, ← hk] at hw
        rw [← hu _ hw, k.symm_apply_apply]

end GlobalTheory.ShFam.Hor.LogCh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagCellOfNonvanishingLeadingMinors
section
noncomputable section

open Matrix

namespace GlobalTheory.FlagEmb.CellLU

variable {K : Type} [Field K] {n : ℕ}

theorem exists_lower_mul_upper (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ (k : ℕ) (h : k ≤ n), (A.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0) :
    ∃ L : Matrix (Fin n) (Fin n) K, (∀ i k, i < k → L i k = 0) ∧ (∀ i, L i i = 1) ∧
      ∀ i j, j < i → (L * A) i j = 0 := by
  have hw : ∀ i : Fin n, ∃ v : Fin i → K, vecMul v (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)) =
      fun j : Fin i => A i (Fin.castLE i.isLt.le j) := fun i =>
    ⟨vecMul (fun j : Fin i => A i (Fin.castLE i.isLt.le j))
      (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le))⁻¹, by
      rw [vecMul_vecMul, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA _ _)), vecMul_one]⟩
  choose v hv using hw
  refine ⟨Matrix.of fun i k => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then 1 else 0, ?_, ?_, ?_⟩
  · intro i k h
    simp only [Matrix.of_apply]
    rw [dif_neg (by have := Fin.lt_def.mp h; omega), if_neg (ne_of_gt h)]
  · intro i
    simp
  · intro i j h
    rw [Matrix.mul_apply]
    have hsplit : ∀ k : Fin n,
        (Matrix.of fun i k : Fin n => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then (1 : K) else 0) i k * A k j =
        (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) + (if k = i then A i j else 0) := by
      intro k
      simp only [Matrix.of_apply]
      rcases lt_trichotomy k i with h | h | h
      · have hk : (k : ℕ) < i := h
        rw [dif_pos hk, dif_pos hk, if_neg (ne_of_lt h), add_zero]
      · subst h; simp
      · have hk : ¬ (k : ℕ) < i := by have := Fin.lt_def.mp h; omega
        rw [dif_neg hk, dif_neg hk, if_neg (ne_of_gt h), if_neg (ne_of_gt h), zero_mul, add_zero]
    rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
    have hs : ∑ k : Fin i, -v i k * A (Fin.castLE i.isLt.le k) j =
        ∑ k : Fin n, (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) := by
      refine Fintype.sum_of_injective (Fin.castLE i.isLt.le) (Fin.castLE_injective _) _ _ (fun k hk => ?_)
        (fun k => by simp)
      rw [dif_neg]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    rw [← hs]
    have hj := congrFun (hv i) ⟨j, h⟩
    simp only [vecMul, dotProduct, Matrix.submatrix_apply] at hj
    have hcj : Fin.castLE i.isLt.le (⟨j, h⟩ : Fin i) = j := Fin.ext rfl
    rw [hcj] at hj
    rw [← hj]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

theorem exists_lu (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ (k : ℕ) (h : k ≤ n), (A.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0) :
    ∃ N b : Matrix (Fin n) (Fin n) K, (∀ i k, i < k → N i k = 0) ∧ (∀ i, N i i = 1) ∧
      (∀ i j, j < i → b i j = 0) ∧ (∀ i, b i i ≠ 0) ∧ A = N * b := by
  obtain ⟨L, hup, hd, hz⟩ := exists_lower_mul_upper A hA
  have hLt : L.BlockTriangular OrderDual.toDual := fun i k h => hup i k h
  have hL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L hLt]
    simp [hd]
  have hu : IsUnit L.det := by rw [hL]; exact isUnit_one
  letI := L.invertibleOfIsUnitDet hu
  have hN : L⁻¹.BlockTriangular OrderDual.toDual := blockTriangular_inv_of_blockTriangular hLt
  refine ⟨L⁻¹, L * A, fun i k h => hN h, fun i => ?_, hz, fun i => ?_, ?_⟩
  · have h1 : (L * L⁻¹) i i = 1 := by rw [mul_nonsing_inv _ hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hd, one_mul] at h1
    · exact h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hN (show OrderDual.toDual i < OrderDual.toDual k from h), mul_zero]
      · rw [hup i k h, zero_mul]
    · simp
  · have h1 : (L * A).det ≠ 0 := by
      rw [det_mul, hL, one_mul]
      simpa using hA n le_rfl
    rw [Matrix.det_of_upperTriangular (fun i j h => hz i j h)] at h1
    exact Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ _)
  · rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]

theorem sum_lform_plk {S : Type} [CommRing S] {M k : ℕ} {ι ι' : Type} (D : ι' → Fin (M + 1) → S)
    (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι) :
    ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det := by
  have h := Equiv.sum_comp (plE M k)
    (fun q : Fin k → Fin (M + 1) => (∏ l, D (ρ l) (q l)) * (Matrix.of fun l l' => u (e l) (q l')).det)
  refine Eq.trans h ?_
  simp only [det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

theorem exists_cell (T : Type) (m : T → ℕ) (K : Type) [Field K] (M : ℕ) (D c u : Let m → Fin (M + 1) → K) (w : Pm m)
    (hD : LeftInv D c) (hu : InBlock c u)
    (h : ∀ τ j hj, ∑ q, lform D (wLet w ∘ std τ j hj) q * plk u (std τ j hj) q ≠ 0) :
    ∃ (x : CellVar m → K) (d : Let m → K), (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  have hA : ∀ τ, ∃ A : Matrix (Fin (m τ)) (Fin (m τ)) K, ∀ j, u ⟨τ, j⟩ = ∑ i, A i j • c ⟨τ, w τ i⟩ := fun τ => by
    have := fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hu ⟨τ, j⟩)
    choose a ha using this
    refine ⟨Matrix.of fun i j => a j (w τ i), fun j => ?_⟩
    rw [← ha j]
    exact (Equiv.sum_comp (w τ) (fun i => a j i • c ⟨τ, i⟩)).symm
  choose A hA using hA
  have hent : ∀ τ i j, ∑ r, D (wLet w ⟨τ, i⟩) r * u ⟨τ, j⟩ r = A τ i j := fun τ i j => by
    rw [hA]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ i', ∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r) = if i' = i then A τ i' j else 0 := by
      intro i'
      have h1 := hD (wLet w ⟨τ, i⟩) ⟨τ, w τ i'⟩
      rw [show (∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r)) =
        A τ i' j * ∑ r, D (wLet w ⟨τ, i⟩) r * c ⟨τ, w τ i'⟩ r by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring, h1]
      by_cases hi : i' = i
      · subst hi; simp [wLet]
      · rw [if_neg hi, if_neg, mul_zero]
        intro he
        simp only [wLet, Sigma.mk.injEq, heq_eq_eq, true_and] at he
        exact hi ((w τ).injective he).symm
    simp [this]
  have hmin : ∀ τ (k : ℕ) (hk : k ≤ m τ), ((A τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
    intro τ k hk
    have h1 := h τ k hk
    rw [sum_lform_plk, ← det_transpose] at h1
    convert h1 using 2
    ext l l'
    exact (hent τ _ _).symm
  choose N b hN hN1 hb hb1 hNb using fun τ => exists_lu (A τ) (hmin τ)
  refine ⟨fun y => N y.1 y.2.1.1 y.2.1.2, fun z => b z.1 z.2 z.2, fun z => hb1 _ _, ?_⟩
  have hcell : ∀ τ i j, cell (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) τ i j = N τ i j := by
    intro τ i j
    unfold cell
    rcases lt_trichotomy i j with h | h | h
    · rw [dif_neg (not_lt.2 h.le), if_neg h.ne, hN τ i j h]
    · subst h; simp [hN1]
    · rw [dif_pos h]
  rintro ⟨τ, j⟩
  have hexp : u ⟨τ, j⟩ = ∑ k, b τ k j • cellVec c w (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) ⟨τ, k⟩ := by
    rw [hA, hNb]
    simp only [cellVec, hcell, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_left]
  refine Submodule.sum_mem _ fun k hk => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk) with h | h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, h, rfl⟩)
  · rw [hb τ k j h, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.FlagEmb.CellLU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFibreExponentialsNearCentre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpAt_homMk {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    {g : ℕ} (y₁ y₂ : Sp ℂ ⟶ X) (hy : y₁ = y₂) (e : (Fin g → ℂ) → (Over.mk y₁ ⟶ t.G))
    (hw : ∀ w, (e w).left ≫ t.G.hom = y₂)
    (hadd : ∀ z w, e (z + w) = e z * e w)
    (h1 : ∀ w, ∃! v : epsPt y₁ ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left)
    (h2 : ∀ v : epsPt y₁ ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) :
    IsExpAt t y₂ (fun w => (Over.homMk (e w).left (hw w) : Over.mk y₂ ⟶ t.G)) := by
  subst hy
  have he : (fun w => (Over.homMk (e w).left (hw w) : Over.mk y₁ ⟶ t.G)) = e :=
    funext fun w => Over.OverMorphism.ext rfl
  rw [he]
  have hzero : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  refine ⟨hadd, fun w => ?_, fun v hv => ?_⟩
  · obtain ⟨V, hV, hVu⟩ := h1 w
    refine ⟨V.left, ⟨⟨V.w, ?_⟩, hV⟩, fun v hv => ?_⟩
    · rw [hV.1]; exact congrArg Over.Hom.left hzero
    · have := hVu (Over.homMk v hv.1.1) hv.2
      exact congrArg CommaMorphism.left this
  · exact h2 (Over.homMk v hv.1) (by rw [hzero]; exact hv.2)

end GlobalTheory.ShFam.Hor.LogCh

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exists_expMaps_near_chart_centre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n : ℕ) (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)), (0 : Fin n → ℂ) ∈ e0.target → IsHolTo e0.target (fun z => (e0.symm z).1) → ∃ (g : ℕ) (ρ : ℝ) (ex : ExpMaps Z σ g), 0 < ρ ∧ Metric.ball 0 ρ ⊆ e0.target ∧ IsHolTo (Metric.ball 0 ρ ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) ∧ ∀ x ∈ e0.source, ‖e0 x‖ < ρ → Function.Surjective (ex x) ∧ IsExpAt Z.t (x.1 ≫ genι Z) (ex x) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n e0 h0 hsy
  let y : (Fin n → ℂ) → (Sp ℂ ⟶ Z.X) := fun z => (e0.symm z).1 ≫ genι Z
  have hy : IsHolTo e0.target y := GlobalTheory.RelExp.isHolTo_of_holAt e0.open_target fun z hz =>
    GlobalTheory.RelExp.HolAt.post ⟨e0.target, e0.open_target, hz, hsy⟩ (genι Z)
  obtain ⟨g, B', e, hB', hb', hfib, -⟩ := GlobalTheory.RelExp.exists_relative_exp_of_smooth _ Z.t.G n e0.target y 0
    Z.t.semi.smooth Z.t.semi.geomConnected e0.open_target h0 hy
  obtain ⟨ρ, hρ, hρB⟩ := Metric.isOpen_iff.1 (hB'.inter e0.open_target) 0 ⟨hb', h0⟩
  have hyx : ∀ x ∈ e0.source, y (e0 x) = x.1 ≫ genι Z := fun x hx => by simp only [y, e0.left_inv hx]
  have hw : ∀ x (hx : x ∈ e0.source) w, (e (e0 x) w).left ≫ Z.t.G.hom = x.1 ≫ genι Z := fun x hx w =>
    (e (e0 x) w).w.trans (hyx x hx)
  classical
  let ex : ExpMaps Z σ g := fun x w =>
    if hx : x ∈ e0.source then Over.homMk (e (e0 x) w).left (hw x hx w) else 1
  refine ⟨g, ρ, ex, hρ, fun z hz => (hρB hz).2, ?_, fun x hx hxρ => ?_⟩
  · refine GlobalTheory.RelExp.isHolTo_of_holAt (Metric.isOpen_ball.prod isOpen_univ) fun q hq => ?_
    refine ((hfib q.1 (hρB hq.1).1).1 q.2).congr ?_
    filter_upwards [(Metric.isOpen_ball.prod isOpen_univ).mem_nhds hq] with q' hq'
    have hs : e0.symm q'.1 ∈ e0.source := e0.map_target (hρB hq'.1).2
    have hr : e0 (e0.symm q'.1) = q'.1 := e0.right_inv (hρB hq'.1).2
    simp only [ex, dif_pos hs, Over.homMk_left]
    rw [hr]
  · have hb : e0 x ∈ B' := (hρB (mem_ball_zero_iff.2 hxρ)).1
    obtain ⟨-, hadd, hsurj, -, h1, h2⟩ := hfib _ hb
    have hex : ex x = fun w => (Over.homMk (e (e0 x) w).left (hw x hx w) : Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G) := funext fun w => dif_pos hx
    rw [hex]
    refine ⟨fun a => ?_, isExpAt_homMk Z.t _ _ (hyx x hx) _ (hw x hx) hadd h1 h2⟩
    obtain ⟨z, hz⟩ := hsurj (Over.homMk a.left (a.w.trans (hyx x hx).symm))
    have hzl := congrArg CommaMorphism.left hz
    exact ⟨z, Over.OverMorphism.ext hzl⟩

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocallyHolomorphicPeriodsFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locally_holomorphic_periods_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → ∀ b₀ ∈ B, ∃ (B' : Set V) (i : Fin Fu.n) (Q : V → ((Fu.Di i).La →+ (Letter Dw → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ b ∈ B', Per Fu (a b) i (Q b)) ∧ ∀ v z, DifferentiableOn ℂ (fun b => Q b v z) B' := by
  first | exact @GlobalTheory.ShFam.HorLift.exists_hol_per | exact GlobalTheory.ShFam.HorLift.exists_hol_per | (intros; apply GlobalTheory.ShFam.HorLift.exists_hol_per <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulIsIntegralIwasawaDecompositionStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_smul_mem_lattice' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (v : Fin N → E), ∃ d : ℕ, 0 < d ∧ (d : E) • v ∈ X.Λ := by
  first | exact @GlobalTheory.UnipKill.exists_nat_smul_mem_lattice | exact GlobalTheory.UnipKill.exists_nat_smul_mem_lattice | (intros; apply GlobalTheory.UnipKill.exists_nat_smul_mem_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroHermOfSkewStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_herm_of_skew : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (G : Matrix (Fin N) (Fin N) E) (κ : E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → cc κ = -κ → κ ≠ 0 → ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n → n ≠ 0 → ∃ x, herm G (n.mulVec x) x ≠ 0 := by
  first | exact @GlobalTheory.UnipKill.exists_herm_mulVec_self_ne_zero | exact GlobalTheory.UnipKill.exists_herm_mulVec_self_ne_zero | (intros; apply GlobalTheory.UnipKill.exists_herm_mulVec_self_ne_zero <;> assumption)
end

