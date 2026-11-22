import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormEqOfCsq
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

noncomputable section

namespace GlobalTheory.IsoDeg

open Module
open scoped ComplexConjugate

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem form_eq_of_csq (n : HermFam K V) (n' : HermFam K W) (e : V ≃ₗ[K] W)
    (hc : ∀ σ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → V), csq n σ c g = csq n' σ c fun i => e (g i))
    (σ : K →+* ℂ) (x y : V) : n'.form σ (e x) (e y) = n.form σ x y := by
  have h1 := hc σ 2 ![1, 1] ![x, y]
  have h2 := hc σ 2 ![1, Complex.I] ![x, y]
  have hx := hc σ 1 ![1] ![x]
  have hy := hc σ 1 ![1] ![y]
  simp only [csq, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, map_one, one_mul, mul_one, Complex.add_re] at h1 h2 hx hy
  rw [← n.conj_symm σ x y, ← n'.conj_symm σ (e x) (e y)] at h1 h2
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.conj_I, Complex.neg_re, Complex.neg_im, Complex.mul_im] at h1 h2
  apply Complex.ext
  · linarith
  · nlinarith

theorem deg_map_eq : ∀ (K V W : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (n : HermFam K V) (n' : HermFam K W) (e : V ≃ₗ[K] W), (∀ σ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → V), csq n σ c g = csq n' σ c fun i => e (g i)) → ∀ L : Submodule (𝓞 K) V, L.FG → deg n' (L.map (e.toLinearMap.restrictScalars (𝓞 K))) = deg n L := by
  intro K V W _ _ _ _ _ _ _ _ _ _ n n' e hc L hL
  set f := e.toLinearMap.restrictScalars (𝓞 K) with hf
  have hfi : Function.Injective f := e.injective
  obtain ⟨v, hv⟩ := exists_isFrame L hL
  have hfv : IsFrame K (L.map f) (fun i => e (v i)) := by
    refine ⟨fun i => ⟨v i, hv.1 i, rfl⟩, hv.2.1.map' e.toLinearMap e.ker, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h0 : e x ∈ (Submodule.span K (Set.range v)).map e.toLinearMap := ⟨x, hv.2.2 hx, rfl⟩
    rw [Submodule.map_span, ← Set.range_comp] at h0
    exact h0
  rw [arakelovDegree_eq_degreeOfFamily n' (hL.map f) hfv, arakelovDegree_eq_degreeOfFamily n hL hv]
  unfold degreeOfFamily
  have hs : Submodule.span (𝓞 K) (Set.range fun i => e (v i)) =
      (Submodule.span (𝓞 K) (Set.range v)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hidx : (Submodule.span (𝓞 K) (Set.range fun i => e (v i))).toAddSubgroup.relIndex
      (L.map f).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup := by
    have key : ∀ P : Submodule (𝓞 K) V, (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom :=
      fun P => by
        ext y
        simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map,
          LinearMap.toAddMonoidHom_coe]
    rw [hs, key, key]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hfi
  have hg : ∀ σ, n'.gram σ (fun i => e (v i)) = n.gram σ v := fun σ => by
    ext i j
    simp only [HermFam.gram, Matrix.of_apply]
    exact GlobalTheory.IsoDeg.form_eq_of_csq n n' e hc σ (v i) (v j)
  simp only [hidx, hg]

end GlobalTheory.IsoDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyBundleIsNefOfNonnegWeights
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.FSNef

section Sec

variable {X : Scheme.{0}} [IsIntegral X]

open Classical in

def fnOnOpen (U : X.Opens) (g : X.functionField) (hg : ∀ x ∈ U, RegAt x g) : Γ(X, U) :=
  if h : genericPoint X ∈ U then (exists_fnOf_eq h hg).choose else 0

theorem fnOf_fnOnOpen {U : X.Opens} {g : X.functionField} (hg : ∀ x ∈ U, RegAt x g) (h : genericPoint X ∈ U) :
    fnOf U h (fnOnOpen U g hg) = g := by
  classical
  rw [fnOnOpen, dif_pos h]
  exact (exists_fnOf_eq h hg).choose_spec

def secOfRat (B : LB X) (ρ : B.ι → X.functionFieldˣ) (hρ : IsRatSec B ρ) (g : X.functionField)
    (hg : ∀ c, ∀ x ∈ B.U c, RegAt x (g * ρ c)) : B.Sec where
  f c := fnOnOpen (B.U c) _ (hg c)
  compat i j := fn_ext fun h => by
    change fnOf _ h (resG X inf_le_left _) =
      fnOf _ h ((B.g i j : Γ(X, B.U i ⊓ B.U j)) * resG X inf_le_right _)
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_fnOnOpen, fnOf_fnOnOpen, hρ i j h]
    ring

theorem fnOf_secOfRat {B : LB X} {ρ : B.ι → X.functionFieldˣ} (hρ : IsRatSec B ρ) {g : X.functionField}
    (hg : ∀ c, ∀ x ∈ B.U c, RegAt x (g * ρ c)) (c : B.ι) (h : genericPoint X ∈ B.U c) :
    fnOf _ h ((secOfRat B ρ hρ g hg).f c) = g * ρ c :=
  fnOf_fnOnOpen (hg c) h

end Sec

theorem isNef_of_isFS : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ),
    IsFS M f w → (∀ j, 0 ≤ w j) → M.IsNef D := by
  intro hA k _ X _ p D hX M J _ f w hFS hw
  have hsemi := GlobalTheory.T.semiPos_of_isFubiniStudyOfRatFnFamily k X p D M J f w hFS
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hFS
  let s : J → M.B.Sec := fun j => secOfRat M.B ρ hρ (f j) fun c x hx => (hreg x c hx).1 j
  have hs : ∀ j c (h : genericPoint X ∈ M.B.U c), fnOf _ h ((s j).f c) = f j * ρ c :=
    fun j c h => fnOf_secOfRat hρ _ c h
  let e := Fintype.equivFin J
  refine GlobalTheory.T.isNef_of_semiPos_generated_by_smallSections hA k X p D hX M (Fintype.card J) (fun i => s (e.symm i)) hsemi (fun i => ?_) (fun x => ?_)
  · intro σ y
    have hy : y ∈ ptsIn p σ (M.B.U (pick (M.φ σ).isLB y)) := mem_pick _ y
    have hg : genericPoint X ∈ M.B.U (pick (M.φ σ).isLB y) := gen_mem (mem_ptsIn.1 hy)
    have hval : ∀ l, secVal p σ (s l) (pick (M.φ σ).isLB y) y =
        ratVal (f l * (ρ (pick (M.φ σ).isLB y) : X.functionField)) y := fun l => by
      rw [secVal_apply, ← ratVal_fnOf hy hg, hs]
    rw [Weight.nsq, hval, hφ σ y _ hy]
    obtain ⟨l, hl⟩ := (hreg _ _ (mem_ptsIn.1 hy)).2
    have hnn : ∀ m ∈ Finset.univ, 0 ≤ ‖ratVal (f m * (ρ (pick (M.φ σ).isLB y) : X.functionField)) y‖ ^ 2 * Real.exp (2 * w m) :=
      fun m _ => by positivity
    have hpos : 0 < ∑ m, ‖ratVal (f m * (ρ (pick (M.φ σ).isLB y) : X.functionField)) y‖ ^ 2 * Real.exp (2 * w m) :=
      lt_of_lt_of_le (mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hl)) 2) (Real.exp_pos _))
        (Finset.single_le_sum hnn (Finset.mem_univ l))
    rw [Real.exp_neg, Real.exp_log hpos, ← div_eq_mul_inv, div_le_one hpos]
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ (e.symm i)))
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by linarith [hw (e.symm i)]))
  · obtain ⟨c, hc⟩ := exists_chart M.isLB x
    obtain ⟨j, hj⟩ := (hreg x c hc).2
    refine ⟨e j, ?_⟩
    rw [e.symm_apply_apply, mem_nonzeroLocus_iff _ c hc, ← unitAt_fnOf_iff hc (gen_mem hc), hs]
    exact hj

end GlobalTheory.HSNef.FSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAbsEqISup
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice.BaseChange

theorem gaussAbs_eq_iSup {K ι : Type} [Field K] [NumberField K] (v : FinitePlace K) (g : MvPolynomial ι K)
    (s : Finset (ι →₀ ℕ)) (hs : g.support ⊆ s) (hne : s.Nonempty) :
    gaussAbs v g = ⨆ k : s, v (coeff (k : ι →₀ ℕ) g) := by
  classical
  have : Nonempty s := hne.to_subtype
  have hsup : (g.support.sup fun m => (v (coeff m g)).toNNReal) = s.sup fun m => (v (coeff m g)).toNNReal := by
    refine le_antisymm (Finset.sup_mono hs) (Finset.sup_le fun m hm => ?_)
    by_cases hm' : m ∈ g.support
    · exact Finset.le_sup (f := fun m => (v (coeff m g)).toNNReal) hm'
    · rw [MvPolynomial.notMem_support_iff.1 hm', map_zero, Real.toNNReal_zero]
      exact bot_le
  unfold gaussAbs
  rw [hsup]
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup s hne fun m => (v (coeff m g)).toNNReal
  rw [hkeq, Real.coe_toNNReal _ (apply_nonneg _ _)]
  refine le_antisymm (le_ciSup (f := fun k : s => v (coeff (k : ι →₀ ℕ) g)) (Set.finite_range _).bddAbove ⟨k, hk⟩)
    (ciSup_le fun m => ?_)
  have h1 : (v (coeff (m : ι →₀ ℕ) g)).toNNReal ≤ (v (coeff k g)).toNNReal := by
    rw [← hkeq]; exact Finset.le_sup (f := fun m => (v (coeff m g)).toNNReal) m.2
  have h2 := (Real.toNNReal_le_toNNReal_iff (apply_nonneg _ _)).1 h1
  exact h2

end GlobalTheory.HSChoice.BaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAbsProdLeOne
section
set_option autoImplicit false

open NumberField MvPolynomial

namespace GlobalTheory.GaussSubst

variable {E : Type} [Field E] [NumberField E] (v : FinitePlace E)

theorem gaussAbs_nonneg {τ : Type} (f : MvPolynomial τ E) : 0 ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs v f := by
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
  exact NNReal.coe_nonneg _

theorem gaussAbs_mul_le {τ : Type} (f g : MvPolynomial τ E) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs v (f * g) ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs v f * ReciprocityTheory.MultiplicativeHeights.gaussAbs v g := by
  classical
  have hf := gaussAbs_nonneg v f
  have hg := gaussAbs_nonneg v g
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le v _ (mul_nonneg hf hg) fun u => ?_
  rw [MvPolynomial.coeff_mul]
  refine ReciprocityTheory.MultiplicativeHeights.finite_place_sum_le v _ _ (mul_nonneg hf hg) fun x _ => ?_
  rw [map_mul]
  exact mul_le_mul (ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v f _) (ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v g _)
    (apply_nonneg v _) hf

theorem gaussAbs_one_le {τ : Type} : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (1 : MvPolynomial τ E) ≤ 1 := by
  classical
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le v _ zero_le_one fun s => ?_
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

theorem gaussAbs_pow_le_one {τ : Type} (f : MvPolynomial τ E)
    (hf : ReciprocityTheory.MultiplicativeHeights.gaussAbs v f ≤ 1) (n : ℕ) : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (f ^ n) ≤ 1 := by
  induction n with
  | zero => simpa using gaussAbs_one_le v
  | succ n ih =>
    rw [pow_succ]
    exact (gaussAbs_mul_le v _ _).trans
      (mul_le_one₀ ih (gaussAbs_nonneg v f) hf)

theorem gaussAbs_prod_le_one {τ ι : Type} (t : Finset ι) (F : ι → MvPolynomial τ E)
    (hF : ∀ i ∈ t, ReciprocityTheory.MultiplicativeHeights.gaussAbs v (F i) ≤ 1) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs v (∏ i ∈ t, F i) ≤ 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using gaussAbs_one_le v
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    exact (gaussAbs_mul_le v _ _).trans
      (mul_le_one₀ (hF a (Finset.mem_insert_self a t)) (gaussAbs_nonneg v _)
        (ih fun i hi => hF i (Finset.mem_insert_of_mem hi)))

theorem gaussAbs_C_mul_le {τ : Type} (a : E) (f : MvPolynomial τ E)
    (hf : ReciprocityTheory.MultiplicativeHeights.gaussAbs v f ≤ 1) : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (C a * f) ≤ v a := by
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le v _ (apply_nonneg v _) fun s => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul]
  exact mul_le_of_le_one_right (apply_nonneg v _)
    ((ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v f s).trans hf)

theorem gaussAbs_aeval_le : ∀ (E : Type) [Field E] [NumberField E] (v : FinitePlace E) (σ τ : Type)
    (φ : σ → MvPolynomial τ E) (g : MvPolynomial σ E),
    (∀ i, ReciprocityTheory.MultiplicativeHeights.gaussAbs v (φ i) ≤ 1) →
      ReciprocityTheory.MultiplicativeHeights.gaussAbs v (aeval φ g) ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs v g := by
  intro E _ _ v σ τ φ g h
  have h0 := gaussAbs_nonneg v g
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le v _ h0 fun t => ?_
  rw [aeval_def, eval₂_eq, coeff_sum]
  refine ReciprocityTheory.MultiplicativeHeights.finite_place_sum_le v _ _ h0 fun s _ => ?_
  have hprod : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (∏ i ∈ s.support, φ i ^ s i) ≤ 1 :=
    gaussAbs_prod_le_one v _ _ fun i _ => gaussAbs_pow_le_one v _ (h i) _
  have hC := gaussAbs_C_mul_le v (coeff s g) _ hprod
  rw [MvPolynomial.algebraMap_eq]
  exact (ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v _ t).trans
    (hC.trans (ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v g s))

end GlobalTheory.GaussSubst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorSchemeLineBundleAffineFiniteType
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace GenAffine

open GeneratorFunctor

set_option backward.isDefEq.respectTransparency false

theorem exists_torus_one (S : Scheme.{0}) :
    ∃ (T : Scheme.{0}) (p : T ⟶ S) (t : Γ(T, ⊤)ˣ), IsAffineHom p ∧ LocallyOfFiniteType p ∧
      (∀ (Z : Scheme.{0}) (c : Z ⟶ S) (v : Γ(Z, ⊤)ˣ), ∃ g : Z ⟶ T, g ≫ p = c ∧
        g.appTop.hom t.val = v.val) ∧
      ∀ (Z : Scheme.{0}) (g g' : Z ⟶ T), g ≫ p = g' ≫ p →
        g.appTop.hom t.val = g'.appTop.hom t.val → g = g' := by
  refine ⟨(splitTorus S ℤ).left, (splitTorus S ℤ).hom, charUnit S ℤ 1, inferInstance,
    inferInstance, fun Z c v => ?_, fun Z g g' h hk => ?_⟩
  · let φ : ℤ →+ Additive Γ(Z, ⊤)ˣ := zmultiplesHom _ (Additive.ofMul v)
    obtain ⟨g, hg⟩ := (splitTorusPointsEquiv S ℤ (Over.mk c)).surjective
      (AddMonoidHom.toMultiplicativeLeft φ)
    refine ⟨g.left, Over.w g, ?_⟩
    refine (splitTorusPointsEquiv_val S _ (Over.mk c) g _).symm.trans ?_
    rw [hg]
    simp [φ]
  · let Z' : Over S := Over.mk (g' ≫ (splitTorus S ℤ).hom)
    let a : Z' ⟶ splitTorus S ℤ := Over.homMk g h
    let a' : Z' ⟶ splitTorus S ℤ := Over.homMk g' rfl
    have : a = a' := by
      apply (splitTorusPointsEquiv S ℤ Z').injective
      apply AddMonoidHom.toMultiplicativeLeft.symm.injective
      refine AddMonoidHom.ext_int ?_
      apply Additive.toMul.injective
      apply Units.ext
      exact ((splitTorusPointsEquiv_val S _ Z' a _).trans hk).trans
        (splitTorusPointsEquiv_val S _ Z' a' _).symm
    exact congrArg (·.left) this

theorem pb_inv_val {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (W : Z.Opens) (h : W ≤ f ⁻¹ᵁ U)
    (x : Γ(Y, U)ˣ) : (f.appLE U W h).hom (x⁻¹).val = ((pb f U W h x)⁻¹).val := by
  rw [← map_inv, pb_val]

end GenAffine

set_option backward.isDefEq.respectTransparency false in
open GeneratorFunctor GenAffine Opposite in

theorem generatorScheme_affine_finiteType : ∀ (B : Scheme.{0}) (N : LB B), N.IsLB → ∃ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ i : N.ι, Γ(G, q ⁻¹ᵁ N.U i)ˣ), IsAffineHom q ∧ LocallyOfFiniteType q ∧ (∀ i i', res (Scheme.Hom.preimage_mono q (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (u i) = pullU q _ (N.g i i') * res (Scheme.Hom.preimage_mono q (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (u i')) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ i : N.ι, Γ(Z, b ⁻¹ᵁ N.U i)ˣ), (∀ i i', res (Scheme.Hom.preimage_mono b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (s i) = pullU b _ (N.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (s i')) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ i, (g.appLE (q ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl)).hom (u i).val = (s i).val := by
  intro B N hN
  obtain ⟨G, ⟨e⟩⟩ := (isRepresentable_genFunctor (N := fun _ : Unit => N) fun _ => hN).has_representation
  let x : Pt (fun _ : Unit => N) G := e.homEquiv (𝟙 G)
  have he : ∀ {Z : Scheme.{0}} (g : Z ⟶ G), e.homEquiv g = Pt.map g x := fun g => by
    rw [e.homEquiv_eq]; rfl
  have hinj : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ G), Pt.map g x = Pt.map g' x → g = g' :=
    fun g g' h => e.homEquiv.injective (by rw [he, he]; exact h)
  have hsurj : ∀ {Z : Scheme.{0}} (y : Pt (fun _ : Unit => N) Z), ∃ g : Z ⟶ G, Pt.map g x = y :=
    fun y => ⟨e.homEquiv.symm y, by rw [← he, Equiv.apply_symm_apply]⟩
  have hloc : ∀ i, IsAffineHom (x.b ∣_ N.U i) ∧ LocallyOfFiniteType (x.b ∣_ N.U i) := by
    intro i
    obtain ⟨T, p, t, hpa, hpl, hex, hun⟩ := exists_torus_one (N.U i).toScheme
    have hb : ∀ k : Unit, ⊤ ≤ (p ≫ (N.U i).ι) ⁻¹ᵁ ((fun _ : Unit => N) k).U ((fun _ => i) k) :=
      fun k z _ => (p z).2
    let yT : Pt (fun _ : Unit => N) T :=
      Pt.ofChart (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t)
    obtain ⟨ψ, hψ⟩ := hsurj yT
    have hψb : ψ ≫ x.b = p ≫ (N.U i).ι := congrArg Pt.b hψ
    let ψ₀ : T ⟶ (x.b ⁻¹ᵁ N.U i).toScheme := IsOpenImmersion.lift (x.b ⁻¹ᵁ N.U i).ι ψ (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      change x.b (ψ z) ∈ N.U i
      rw [← Scheme.Hom.comp_apply, hψb, Scheme.Hom.comp_apply]
      exact (p z).2)
    have hψ₀ : ψ₀ ≫ (x.b ⁻¹ᵁ N.U i).ι = ψ := IsOpenImmersion.lift_fac _ _ _
    have hv : ⊤ ≤ (x.b ⁻¹ᵁ N.U i).ι ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => z.2
    obtain ⟨φ, hφp, hφt⟩ := hex _ (x.b ∣_ N.U i) (pb (x.b ⁻¹ᵁ N.U i).ι _ ⊤ hv (x.s () i))
    have h2 : ψ₀ ≫ φ = 𝟙 T := by
      refine hun T _ _ ?_ ?_
      · rw [Category.assoc, hφp, Category.id_comp, ← cancel_mono (N.U i).ι, Category.assoc,
          morphismRestrict_ι, ← Category.assoc, hψ₀, hψb]
      · have htop : ∀ {Y Z : Scheme.{0}} (f : Z ⟶ Y), ⊤ ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := fun f z _ => trivial
        have hφu : pb φ ⊤ ⊤ (htop φ) t = pb (x.b ⁻¹ᵁ N.U i).ι _ ⊤ hv (x.s () i) :=
          Units.ext ((pb_top _ _ _).trans hφt)
        have hψ' : ⊤ ≤ 𝟙 T ⁻¹ᵁ (ψ ≫ x.b) ⁻¹ᵁ N.U i := fun z _ => by
          have : (ψ ≫ x.b) z ∈ N.U i := by rw [hψb]; exact (p z).2
          exact this
        have hψ'' : ⊤ ≤ ψ ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => by
          have : (ψ ≫ x.b) z ∈ N.U i := by rw [hψb]; exact (p z).2
          exact this
        have e1 : pb (ψ₀ ≫ (x.b ⁻¹ᵁ N.U i).ι) (x.b ⁻¹ᵁ N.U i) ⊤ (hψ₀ ▸ hψ'') (x.s () i) =
            pb ψ (x.b ⁻¹ᵁ N.U i) ⊤ hψ'' (x.s () i) := pb_congr hψ₀ _ _ _ _
        have e2 : pb ψ (x.b ⁻¹ᵁ N.U i) ⊤ hψ'' (x.s () i) =
            pb (𝟙 T) _ ⊤ hψ' ((Pt.map ψ x).s () i) := (pb_id_comp ψ _ _ _ le_rfl hψ' _).symm
        have hbT : ⊤ ≤ 𝟙 T ⁻¹ᵁ (p ≫ (N.U i).ι) ⁻¹ᵁ N.U i := fun z _ => (p z).2
        have e3 : pb (𝟙 T) _ ⊤ hψ' ((Pt.map ψ x).s () i) = pb (𝟙 T) _ ⊤ hbT (yT.s () i) :=
          Pt.congr hψ () i (𝟙 T) ⊤ hψ' hbT
        have e4 : (pb (𝟙 T) _ ⊤ hbT (yT.s () i)).val = (Scheme.Hom.appTop (𝟙 T)).hom t.val :=
          Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t) () (𝟙 T) _
        refine (pb_top (ψ₀ ≫ φ) (htop _) t).symm.trans ?_
        rw [← pb_pb ψ₀ φ ⊤ ⊤ ⊤ (htop φ) (htop ψ₀), hφu, pb_pb]
        exact (congrArg Units.val (e1.trans (e2.trans e3))).trans e4
    have h1 : φ ≫ ψ₀ = 𝟙 _ := by
      rw [← cancel_mono (x.b ⁻¹ᵁ N.U i).ι, Category.assoc, hψ₀, Category.id_comp]
      refine hinj _ _ ?_
      have hbeq : (φ ≫ ψ) ≫ x.b = (x.b ⁻¹ᵁ N.U i).ι ≫ x.b := by
        rw [Category.assoc, hψb, ← Category.assoc, hφp, morphismRestrict_ι]
      have hx' : ⊤ ≤ φ ⁻¹ᵁ (ψ ≫ x.b) ⁻¹ᵁ N.U i := fun z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have hy' : ⊤ ≤ φ ⁻¹ᵁ (p ≫ (N.U i).ι) ⁻¹ᵁ N.U i := fun z _ => (p (φ z)).2
      have hA : ∀ k : Unit, ⊤ ≤ 𝟙 (x.b ⁻¹ᵁ N.U i).toScheme ⁻¹ᵁ ((φ ≫ ψ) ≫ x.b) ⁻¹ᵁ N.U i := fun _ z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have hB : ∀ k : Unit, ⊤ ≤ 𝟙 (x.b ⁻¹ᵁ N.U i).toScheme ⁻¹ᵁ ((x.b ⁻¹ᵁ N.U i).ι ≫ x.b) ⁻¹ᵁ N.U i := fun _ z _ => z.2
      have hC : ⊤ ≤ (φ ≫ ψ) ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have f1 : pb (𝟙 (x.b ⁻¹ᵁ N.U i).toScheme) _ ⊤ (hA ()) ((Pt.map (φ ≫ ψ) x).s () i) =
          pb (φ ≫ ψ) (x.b ⁻¹ᵁ N.U i) ⊤ hC (x.s () i) := pb_id_comp _ _ _ _ _ _ _
      have f2 : pb (𝟙 (x.b ⁻¹ᵁ N.U i).toScheme) _ ⊤ (hB ()) ((Pt.map (x.b ⁻¹ᵁ N.U i).ι x).s () i) =
          pb (x.b ⁻¹ᵁ N.U i).ι (x.b ⁻¹ᵁ N.U i) ⊤ hv (x.s () i) := pb_id_comp _ _ _ _ _ _ _
      have f3 : pb (φ ≫ ψ) (x.b ⁻¹ᵁ N.U i) ⊤ hC (x.s () i) =
          pb φ _ ⊤ hx' ((Pt.map ψ x).s () i) := (pb_pb φ ψ (x.b ⁻¹ᵁ N.U i) ((ψ ≫ x.b) ⁻¹ᵁ N.U i) ⊤ le_rfl hx' (x.s () i)).symm
      have f4 : pb φ _ ⊤ hx' ((Pt.map ψ x).s () i) = pb φ _ ⊤ hy' (yT.s () i) :=
        Pt.congr hψ () i φ ⊤ hx' hy'
      have f5 : (pb φ _ ⊤ hy' (yT.s () i)).val = φ.appTop.hom t.val :=
        Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t) () φ hy'
      refine Pt.ext_chart hbeq (fun _ => i) hA hB (fun k => ?_)
      cases k
      refine f1.trans (f3.trans (f4.trans (Units.ext ?_))) |>.trans f2.symm
      exact f5.trans hφt
    have : IsIso φ := ⟨⟨ψ₀, h1, h2⟩⟩
    rw [← hφp]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨G, x.b, fun i => (x.s () i)⁻¹, IsZariskiLocalAtTarget.of_iSup_eq_top N.U hN.cover
    fun i => (hloc i).1, IsZariskiLocalAtTarget.of_iSup_eq_top N.U hN.cover fun i => (hloc i).2,
    fun i i' => ?_, fun Z b s hs => ?_⟩
  · have hc : res (Scheme.Hom.preimage_mono x.b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (x.s () i') =
        pullU x.b _ (N.g i i') *
          res (Scheme.Hom.preimage_mono x.b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (x.s () i) := by
      rw [res_eq_pb, res_eq_pb, pullU_eq_pb]
      exact x.compat () i i' _ inf_le_left inf_le_right
    dsimp only
    rw [map_inv, map_inv, hc, mul_inv, mul_inv_cancel_left]
  · have hs' : ∀ i i' (W : Z.Opens) (h : W ≤ b ⁻¹ᵁ N.U i) (h' : W ≤ b ⁻¹ᵁ N.U i'),
        pb (𝟙 Z) (b ⁻¹ᵁ N.U i') W h' (s i')⁻¹ =
          pb b (N.U i ⊓ N.U i') W (le_inf h h') (N.g i i') * pb (𝟙 Z) (b ⁻¹ᵁ N.U i) W h (s i)⁻¹ := by
      intro i i' W h h'
      have := congrArg (pb (𝟙 Z) (b ⁻¹ᵁ (N.U i ⊓ N.U i')) W (le_inf h h')) (hs i i')
      rw [map_mul, res_eq_pb, res_eq_pb, pullU_eq_pb, pb_id_comp, pb_id_comp, pb_id_comp] at this
      rw [map_inv, map_inv, this, mul_inv, mul_inv_cancel_left]
    let y : Pt (fun _ : Unit => N) Z := ⟨b, fun _ i => (s i)⁻¹, fun _ i i' W h h' => hs' i i' W h h'⟩
    have key : ∀ g : Z ⟶ G, (∃ hg : g ≫ x.b = b, ∀ i, (g.appLE (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i)
        (by rw [← hg]; exact le_rfl)).hom ((x.s () i)⁻¹).val = (s i).val) ↔ Pt.map g x = y := by
      intro g
      constructor
      · rintro ⟨hg, h⟩
        refine (Pt.ext' (x := y) (y := Pt.map g x) hg.symm fun k i => ?_).symm
        cases k
        have h2 : (pb g _ (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i))⁻¹ = s i :=
          Units.ext ((pb_inv_val _ _ _ _ _).symm.trans (h i))
        have h3 : pb (𝟙 Z) ((g ≫ x.b) ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [hg]; exact le_rfl)
            (pb g (x.b ⁻¹ᵁ N.U i) ((g ≫ x.b) ⁻¹ᵁ N.U i) le_rfl (x.s () i)) =
              pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) :=
          pb_id_comp _ _ _ _ _ _ _
        exact (inv_eq_iff_eq_inv.1 h2).symm.trans h3.symm
      · intro h
        have hg : g ≫ x.b = b := congrArg Pt.b h
        refine ⟨hg, fun i => ?_⟩
        have := Pt.congr h () i (𝟙 Z) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) le_rfl
        have h3 : pb (𝟙 Z) ((g ≫ x.b) ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [hg]; exact le_rfl)
            (pb g (x.b ⁻¹ᵁ N.U i) ((g ≫ x.b) ⁻¹ᵁ N.U i) le_rfl (x.s () i)) =
              pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) :=
          pb_id_comp _ _ _ _ _ _ _
        have h4 : pb (𝟙 Z) (b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) le_rfl (s i)⁻¹ = (s i)⁻¹ := pb_id _ _
        have h5 : pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) =
            (s i)⁻¹ := h3.symm.trans (this.trans h4)
        rw [pb_inv_val, h5, inv_inv]
    obtain ⟨g0, hg0⟩ := hsurj y
    exact ⟨g0, (key g0).2 hg0, fun g hg => hinj _ _ (((key g).1 hg).trans hg0.symm)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageComponentwiseSubgroupEqProdStatement
section
open Filter GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupAverage_componentwiseSubgroup_eq_prod : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) (u : ∀ i, KH i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ i, (rStab (u i)).index ≠ 0) → (∀ᶠ i in cofinite, ∀ k, u i k = 1) → avg (fun k : K => ∏ᶠ i, u i ⟨p i k, (hK k).1 k.2 i⟩) = ∏ᶠ i, avg (u i) := by
  first | exact @GlobalTheory.AvgRestr.avg_restrProd | exact GlobalTheory.AvgRestr.avg_restrProd | (intros; apply GlobalTheory.AvgRestr.avg_restrProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageRestrictedProductMaxCompactProdStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupAverage_restrictedProduct_maxCompact_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (u : ∀ v, K v → ℂ), (∀ v, (rStab (u v)).index ≠ 0) → (∀ᶠ v in cofinite, ∀ k, u v k = 1) → avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) = ∏ᶠ v, avg (u v) := by
  first | exact @GlobalTheory.AvgRestr.avg_restr_prod | exact GlobalTheory.AvgRestr.avg_restr_prod | (intros; apply GlobalTheory.AvgRestr.avg_restr_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicExtremalNegativeFirstStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_extremal_negative_first : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (h : D.what₂.Tau → HCParam D.R) (p q : ℕ), IsInfFam θ → p + q = D.R.r → V.rank = D.R.r → (∀ ρ, S ρ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q)) → ∀ v : M.Vec, IsExtVec M v → ∃ x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, NegFirst V q x ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → IsHolFor θ V x (fun ρ c => wtCol (h ρ) p q c) (T v) := by
  first | exact @GlobalTheory.HolRead.isHolFor_extVec_holPar | exact GlobalTheory.HolRead.isHolFor_extVec_holPar | (intros; apply GlobalTheory.HolRead.isHolFor_extVec_holPar <;> assumption)
end

