import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0038
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetTranslateProjectedVacuumLe
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpacesStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_familyUnif_isTypeFn_card_comp_le : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty ∧ Fintype.card U.Comp ≤ F.n := by
  first | exact @GlobalTheory.card_comp_le_periodSpaces | exact GlobalTheory.card_comp_le_periodSpaces | (intros; apply GlobalTheory.card_comp_le_periodSpaces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSpan

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.GradedWeylDivisibility
open scoped Classical Pointwise Matrix

theorem coeff_mem_of_eval_mem {K A : Type} [Field K] [CharZero K] [CommRing A] [Algebra K A] (M : Submodule K A)
    (p : Polynomial A) (h : ∀ c : ℕ, p.eval (c : A) ∈ M) (k : ℕ) : p.coeff k ∈ M := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  set q : Polynomial K := ∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.monomial i (φ (p.coeff i)) with hq
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := Set.range (fun c : ℕ => (c : K))) ?_
      (Set.infinite_range_of_injective Nat.cast_injective)
    rintro _ ⟨c, rfl⟩
    have h1 := hφ _ (h c)
    rw [Polynomial.eval_eq_sum_range, map_sum] at h1
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hq, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : p.coeff i * (c : A) ^ i = ((c : K) ^ i) • p.coeff i := by
      rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  by_cases hk : k ≤ p.natDegree
  · have := congrArg (fun r => r.coeff k) hq0
    simp only [hq, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range,
      Polynomial.coeff_zero] at this
    rwa [if_pos (by omega)] at this
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

theorem eval_rowGen {K : Type} [Field K] {r n : ℕ} (a b : Fin r) (c : K) (f : MvPolynomial (Fin r × Fin n) K) :
    (rowGen K a b f).eval (C c) = rowAct K (1 + Matrix.single b a c) f := by
  induction f using MvPolynomial.induction_on with
  | C x => simp [rowGen, rowAct]
  | add f g hf hg => simp only [map_add, Polynomial.eval_add, hf, hg]
  | mul_X f v hf =>
    simp only [map_mul, Polynomial.eval_mul, hf]
    congr 1
    simp only [rowGen, rowAct, aeval_X, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib,
      Polynomial.eval_add, Polynomial.eval_C]
    congr 1
    · rw [Finset.sum_eq_single v.1]
      · simp
      · intro x _ hx
        simp [Matrix.one_apply, Ne.symm hx]
      · simp
    · rw [Finset.sum_eq_single a]
      · by_cases hv : v.1 = b
        · simp only [hv, if_true, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
            Matrix.single_apply_same]
        · simp [hv, Matrix.single, Ne.symm hv]
      · intro x _ hx
        simp [Matrix.single, Ne.symm hx]
      · simp

theorem isUnit_elem {K : Type} [Field K] [CharZero K] {r : ℕ} (a b : Fin r) (c : ℕ) :
    IsUnit (1 + Matrix.single b a (c : K)) := by
  by_cases h : a = b
  · subst h
    have hc : (1 + c : K) ≠ 0 := by exact_mod_cast (by omega : 1 + c ≠ 0)
    refine IsUnit.of_mul_eq_one (1 + Matrix.single a a (-(c : K) / (1 + c))) ?_
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.single_mul_single_same, add_assoc,
      ← Matrix.single_add, ← Matrix.single_add]
    have : -(c : K) / (1 + c) + (c + c * (-(c : K) / (1 + c))) = 0 := by field_simp; ring
    rw [this]; simp
  · refine IsUnit.of_mul_eq_one (1 + Matrix.single b a (-(c : K))) ?_
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.single_mul_single_of_ne _ _ _ _ h, add_zero,
      add_assoc, ← Matrix.single_add]
    simp

def trGL {K : Type} [Field K] {r : ℕ} (g : GL (Fin r) K) : GL (Fin r) K := inside₂ K r g⁻¹

theorem trGL_coe {K : Type} [Field K] {r : ℕ} (g : GL (Fin r) K) :
    (trGL g : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K)ᵀ := by
  simp [trGL, inside₂]

theorem rowDiv_mem_of_stable {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K))
    (hst : ∀ u : GL (Fin r) K, ∀ f ∈ M, rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈ M)
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin m) K) (hf : f ∈ M) : rowDiv K a b k f ∈ M := by
  unfold rowDiv
  refine coeff_mem_of_eval_mem M _ (fun c => ?_) k
  have h1 := eval_rowGen a b (c : K) f
  rw [map_natCast] at h1
  rw [h1]
  obtain ⟨u, hu⟩ := isUnit_elem (K := K) a b c
  rw [← hu]
  exact hst u f hf

theorem applyWord_mem_of_stable {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K))
    (hst : ∀ u : GL (Fin r) K, ∀ f ∈ M, rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈ M)
    (f : MvPolynomial (Fin r × Fin m) K) (hf : f ∈ M) (w : List (Fin r × Fin r × ℕ)) : applyWord K w f ∈ M := by
  unfold applyWord
  induction w with
  | nil => rw [List.foldr_nil]; exact hf
  | cons x w ih => rw [List.foldr_cons]; exact rowDiv_mem_of_stable M hst _ _ _ _ ih

theorem rowAct_one {K : Type} [Field K] {r m : ℕ} :
    rowAct K (n := m) (1 : Matrix (Fin r) (Fin r) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, aeval_X, Matrix.one_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem orbit_stable {K : Type} [Field K] {r m : ℕ} (v : MvPolynomial (Fin r × Fin m) K) (u : GL (Fin r) K)
    (f : MvPolynomial (Fin r × Fin m) K)
    (hf : f ∈ Submodule.span K (Set.range fun g : GL (Fin r) K => rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ v)) :
    rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈
      Submodule.span K (Set.range fun g : GL (Fin r) K => rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ v) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    refine Submodule.subset_span ⟨trGL u * g, ?_⟩
    have := DFunLike.congr_fun
      (rowActMul K r m (u : Matrix (Fin r) (Fin r) K) (g : Matrix (Fin r) (Fin r) K)ᵀ) v
    rw [AlgHom.comp_apply] at this
    beta_reduce
    rw [this, Units.val_mul, trGL_coe, Matrix.transpose_mul, Matrix.transpose_transpose]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem dualWeyl_le_span_orbit (K : Type) [Field K] [CharZero K] {r m : ℕ} (hm : m ≤ r) (ν : Fin m → ℕ)
    (hν : Antitone ν) :
    dualWeyl K r m ν ≤ Submodule.span K (Set.range fun g : GL (Fin r) K =>
      rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ (hw K hm ν)) := by
  rw [Formalism.L2.Col.dualWeyl_eq_weyl K hm ν hν, weyl, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  generalize hw K hm ν = v
  refine applyWord_mem_of_stable _ (orbit_stable v) v (Submodule.subset_span ⟨1, ?_⟩) w
  beta_reduce
  rw [Units.val_one, Matrix.transpose_one, rowAct_one, AlgHom.id_apply]

theorem prod_mem_span_prod {K A ι : Type} [Field K] [CommRing A] [Algebra K A] (s : Finset ι) (S : ι → Set A)
    (x : ι → A) (hx : ∀ i, x i ∈ Submodule.span K (S i)) : ∏ i ∈ s, x i ∈ Submodule.span K (∏ i ∈ s, S i) := by
  induction s using Finset.induction_on with
  | empty => exact Submodule.subset_span (by simp)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← Submodule.span_mul_span]
    exact Submodule.mul_mem_mul (hx a) ih

theorem trAct_ten {K : Type} [Field K] {Ix : Type} [Fintype Ix] {n : ℕ} (g : Ix → GL (Fin n) K)
    (f : Ix → MvPolynomial (Fin n × Fin n) K) :
    trAct g (ten f) = ten fun t => rowAct K (g t : Matrix (Fin n) (Fin n) K)ᵀ (f t) := by
  unfold trAct ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun t _ =>
    (blockActTensor K K Ix n n (fun τ => (g τ : Matrix (Fin n) (Fin n) K)ᵀ)).1 t (f t)

theorem VV_eq_span_orbit (K : Type) [Field K] [CharZero K] (Ix : Type) [Fintype Ix] (n : ℕ)
    (lam : Ix → DomWeight n) :
    VV K lam = Submodule.span K
      (Set.range fun g : Ix → GL (Fin n) K => actP lam g (ten fun t => extremal K n (lam t))) := by
  apply le_antisymm
  · rw [VV, tensorLat, Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    have h1 := prod_mem_span_prod (K := K) Finset.univ
      (fun t => blockEmb K t '' (Set.range fun g : GL (Fin n) K =>
        rowAct K (g : Matrix (Fin n) (Fin n) K)ᵀ (extremal K n (lam t))))
      (fun t => blockEmb K t (F t)) (fun t => by
        have := dualWeyl_le_span_orbit K le_rfl (lam t).natW (Formalism.L2.Col.natW_anti (lam t)) (hF t)
        exact Submodule.apply_mem_span_image_of_mem_span (blockEmb K t).toLinearMap this)
    refine Submodule.span_le.mpr ?_ h1
    intro y hy
    rw [Set.mem_fintype_prod] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    choose w hw hw' using hz
    choose g hg using hw
    have hd : detTwK lam g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => Units.ne_zero _
    have h2 : ∏ t, z t = (detTwK lam g)⁻¹ • actP lam g (ten fun t => extremal K n (lam t)) := by
      simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_smul, inv_mul_cancel₀ hd, one_smul,
        trAct_ten]
      unfold ten
      exact Finset.prod_congr rfl fun t _ => by rw [← hw', ← hg]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    refine polyAction_mem_VV lam g (Submodule.subset_span ⟨_, fun t => ?_, rfl⟩)
    exact Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (Formalism.L2.Col.natW_anti (lam t)) (Submodule.subset_span ⟨[], rfl⟩)

end GlobalTheory.OrbitSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FramedBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_algebraMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem isTanAt_pull {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, spMap_spMap, dualMap_comp_algebraMap, ← spMap_spMap,
      Category.assoc]
  · rw [← Category.assoc, spMap_spMap, fstHom_comp_dualMap, ← spMap_spMap, Category.assoc, h2]
    have e : (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ≫
        (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := by
      simp [Hom.one_def]
    rw [← e, Over.comp_left]
    rfl

theorem isEigAt_pull {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_spMap, dualMap_epsMul, ← spMap_spMap,
    Category.assoc]
  congr 3
  exact ψ.commutes _

theorem exists_frMap : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap ψ y z := by
  intro hLaws E _ _ _ H Dw l Xo c S T _ _ _ _ ψ y
  let h : ptO Xo (spMap ψ.toRingHom ≫ y.x) ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) rfl
  obtain ⟨s', hs'⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G)
    (whiskerRight_snd _ _) y.s
  refine ⟨
    { x := spMap ψ.toRingHom ≫ y.x
      x_over := by
        rw [Category.assoc, y.x_over]
        unfold sOf
        rw [spMap_spMap, ← RingHom.comp_assoc]
        congr 2
        ext r
        simp
      u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i
      tan := fun τ i => isTanAt_pull ψ.toRingHom (y.tan τ i)
      eig := fun τ i => isEigAt_pull ψ τ (y.eig τ i)
      basis := fun τ w hw he => GlobalTheory.T.existsUnique_isCombAt_baseChange_of_isEigAt E H Dw l Xo c S T ψ y τ w hw he
      s := s'
      gen := GlobalTheory.T.framedPoint_generator_ringBaseChange hLaws E H Dw l Xo c S T ψ.toRingHom y h rfl s' hs' },
    rfl, fun _ _ => rfl, (h ▷ Xo.univ.t.G).left, ?_, ?_, fun i hi => ?_⟩
  · rw [← Over.comp_left, whiskerRight_snd]
  · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    rfl
  · exact (hs' i).symm

end GlobalTheory.FramedBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramesCubeDefectAlongChartOverRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frames_cubeDefect_along_chart_over_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∃ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e := by
  first | exact @GlobalTheory.ChartFrames.exists_frames | exact GlobalTheory.ChartFrames.exists_frames | (intros; apply GlobalTheory.ChartFrames.exists_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetDataFromHalfConjugateEmbeddingsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.NetNorms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_netData_from_half_conjugate_embeddings : ∀ (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (good : (B.KO →+* ℂ) → Prop), (∀ σ, good σ ↔ ¬ good (ComplexEmbedding.conjugate σ)) → (∀ σ F, B.supN j ka (ComplexEmbedding.conjugate σ) F = B.supN j ka σ F) → ∀ (n : (B.KO →+* ℂ) → ℕ) (ev : ∀ σ, Fin (n σ) → (B.Cusp j ka →ₛₗ[σ] ℂ)) (C : ℝ), (∀ σ, good σ → (∀ F, ∃ y, B.supN j ka σ F / 4 ≤ ‖ev σ y F‖) ∧ (∀ y F, ‖ev σ y F‖ ≤ B.supN j ka σ F) ∧ Real.log (16 * (n σ : ℝ)) ≤ C ∧ ∀ (m : ℕ) (F : Fin m → B.Cusp j ka), LinearIndependent B.KO F → LinearIndependent ℂ (fun i => fun y => ev σ y (F i))) → ∃ Nt : NetData B j ka, NetMax Nt ∧ NetLeSup Nt ∧ NetSize Nt C ∧ ∀ σ, NetInj Nt σ := by
  first | exact @GlobalTheory.exists_netData_of_readings_on_half | exact GlobalTheory.exists_netData_of_readings_on_half | (intros; apply GlobalTheory.exists_netData_of_readings_on_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObjectStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translation_sections_universal_object : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)), (∀ (ok : (T ⟶ Xo.univ.t.G) → Prop) (t t' : T ⟶ Xo.univ.t.G), t' ^ N = t → t' ^ (N ^ 2) = 1 → ok t' → ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok s t F) ∧ ∀ x₁ x₂ : T ⟶ Xo.univ.t.G, x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → ∃! F, IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F := by
  first | exact @GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver | exact GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver | (intros; apply GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameLetterGLActionRepresentationKeepsHarmonic
section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

namespace GlobalTheory.FrameRead

open GlobalTheory.Harm Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix] {pl : Ix → (E →+* ℂ)}

noncomputable def IsEnum.idx (h : IsEnum H pl) (t : {τ : E →+* ℂ // InPsi H τ}) : Ix :=
  ((h.2 t.1).1 t.2).choose

omit [Fintype Ix] in

theorem IsEnum.pl_idx (h : IsEnum H pl) (t : {τ : E →+* ℂ // InPsi H τ}) : pl (h.idx t) = t.1 :=
  ((h.2 t.1).1 t.2).choose_spec

theorem rename_letAct (h : IsEnum H pl) {K : Type} [Field K] (g : Ix → GL (Fin n) K)
    (P : MvPolynomial (LtN Dw n) K) :
    rename (thetaLetterEquiv Dw n) (letAct Dw pl K g P) =
      colSubst (fun t => (g (h.idx t) : Matrix (Fin n) (Fin n) K)ᵀ)
        (fun t => (((g (h.idx t))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)
        (rename (thetaLetterEquiv Dw n) P) := by
  refine DFunLike.congr_fun (?_ : (rename (thetaLetterEquiv Dw n)).comp (letAct Dw pl K g) =
    (colSubst _ _).comp (rename (thetaLetterEquiv Dw n))) P
  refine MvPolynomial.algHom_ext fun ⟨τ, i, b⟩ => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, letAct, aeval_X]
  rcases half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) τ with hτ | ⟨τ, hτ, rfl⟩
  · have h1 : ∃ t, pl t = τ := (h.2 τ).1 hτ
    rw [dif_pos h1, thetaLetterEquiv_of_mem Dw hτ, colSubst_X_xVar, xForm_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_of_mem Dw hτ]
    rfl
  · have h1 : ¬ ∃ t, pl t = ComplexEmbedding.conjugate τ := fun h1 =>
      ((not_mem_hostType_iff H τ).2 ((h.2 _).2 h1)) hτ
    have h2 : ∃ t, ComplexEmbedding.conjugate (pl t) = ComplexEmbedding.conjugate τ :=
      ⟨h.idx ⟨τ, hτ⟩, by rw [h.pl_idx]⟩
    have h3 : h2.choose = h.idx ⟨τ, hτ⟩ := h.1 (by
      rw [h.pl_idx]
      exact (ComplexEmbedding.involutive_conjugate E).injective h2.choose_spec)
    rw [dif_neg h1, dif_pos h2, thetaLetterEquiv_conjugate Dw hτ, colSubst_X_yVar, yForm_apply,
      map_sum, h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_conjugate Dw hτ]
    rfl

theorem letAct_mul_one_mem_HHa :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (K : Type) [Field K] [CharZero K] (a : (E →+* ℂ) × ℕ → ℕ), (∀ g g' : Ix → GL (Fin n) K, letAct Dw pl K (g * g') = (letAct Dw pl K g).comp (letAct Dw pl K g')) ∧ letAct Dw pl K (1 : Ix → GL (Fin n) K) = AlgHom.id K _ ∧ ∀ (g : Ix → GL (Fin n) K), ∀ P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), letAct Dw pl K g P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  intro E _ _ _ H Dw n Ix _ pl h _ K _ _ a
  have hinj := rename_injective (R := K) _ (thetaLetterEquiv Dw n).injective
  refine ⟨fun g g' => AlgHom.ext fun P => hinj ?_, AlgHom.ext fun P => hinj ?_, fun g P hP => ?_⟩
  · rw [AlgHom.comp_apply, rename_letAct Dw h, rename_letAct Dw h, rename_letAct Dw h,
      ← AlgHom.comp_apply (colSubst _ _) (colSubst _ _), colSubst_comp]
    simp only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, transpose_mul]
  · rw [rename_letAct Dw h]
    simp only [Pi.one_apply, inv_one, Units.val_one, transpose_one, colSubst_one, AlgHom.id_apply]
  · have key := mem_HHa_iff_rename (Ψ := InPsi H) (dim := Dw.mult) (n := n) (K := K)
      (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H)
      (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw) (fun τ i => a (τ, i))
    obtain ⟨h₁, h₂, h₃⟩ := (key P).1 hP
    refine (key _).2 ?_
    have e := rename_letAct Dw h g P
    unfold thetaLetterEquiv at e
    rw [e]
    exact ⟨h₁.colSubst fun t => by rw [← transpose_mul, Units.inv_mul, transpose_one],
      fun t r => colSubst_isWeightedHomogeneous _ _ _ (h₂ t r),
      fun t r r' hr s => by rw [rowAdd_colSubst _ _ t hr.isLeft_eq, h₃ t r r' hr]⟩

end GlobalTheory.FrameRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InPsiOrInPsiConjugate
section
set_option autoImplicit false

namespace GlobalTheory.CMTypeOrConjugate

open NumberField

theorem conj_eq_neg_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2 := by
    rw [← map_pow, hz, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exfalso
    obtain ⟨x, rfl⟩ := Complex.conj_eq_iff_real.mp h
    have h2 : x ^ 2 = -(d : ℝ) := by exact_mod_cast hz
    have h3 : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg x]
  · exact h

theorem inPsi_or_inPsi_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    Formalism.L2.Pj.InPsi H τ ∨ Formalism.L2.Pj.InPsi H (ComplexEmbedding.conjugate τ) := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have h := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at h
    exact h
  have hz : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hE, map_neg, map_natCast]
  unfold Formalism.L2.Pj.InPsi
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hz.trans H.sqrt_neg_disc_sq.symm) with h | h
  · exact Or.inl h
  · right
    rw [ComplexEmbedding.conjugate_coe_eq, conj_eq_neg_of_sq H.d_prime.pos hz, h, neg_neg]

end GlobalTheory.CMTypeOrConjugate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetTranslateProjectedVacuumLeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_translate_projected_vacuum_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ lam : ℝ, 0 < lam → (∀ u ∈ L, u ≠ 0 → lam ^ 2 ≤ (hx X bas idx x (pv X idx x u) (pv X idx x u)).re) → ∀ (y : Matrix (Fin n) (Fin r) E) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (d : ℕ), P.IsHomogeneous d → ‖κ * thP X hr bas idx (heisG X bas y (projA X bas (w : E) (tens Λ L) v)) P x‖ * Real.sqrt ((((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup) : ℝ) ^ r) ≤ (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * g * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (g * n) := by
  first | exact @GlobalTheory.Dict.VacJet.jet_projA_le | exact GlobalTheory.Dict.VacJet.jet_projA_le | (intros; apply GlobalTheory.Dict.VacJet.jet_projA_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeviLogThetaSumStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_log_theta_sum_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ ps : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)) → ∀ x0 ∈ X.dom, ∀ z, cpt X.toData x0 z ∈ X.dom → ∀ ξ : Fin (nd X.toData) → ℂ, -((r : ℝ) / 2 * leviM X.toData (phla X.toData (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1)) x0 z ξ) ≤ leviM X.toData ps x0 z ξ := by
  first | exact @GlobalTheory.ThetaSumLevi.levi_log_theta_sum | exact GlobalTheory.ThetaSumLevi.levi_log_theta_sum | (intros; apply GlobalTheory.ThetaSumLevi.levi_log_theta_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogThetaSumInvariantSmoothStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_theta_sum_invariant_smooth_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ ps : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)) → IsInvFn X.toData ps ∧ ∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps (cpt X.toData x0 z)) {z | cpt X.toData x0 z ∈ X.dom} := by
  first | exact @GlobalTheory.ThetaLogSum.log_theta_sum_invariant_smooth | exact GlobalTheory.ThetaLogSum.log_theta_sum_invariant_smooth | (intros; apply GlobalTheory.ThetaLogSum.log_theta_sum_invariant_smooth <;> assumption)
end

