import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialBaseChange

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField
section
namespace GroundTheory.Global

open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

section Descent

variable (E : WeierstrassCurve F) [E.IsElliptic]

theorem exists_eq_add_mul_genY (c : E.toAffine.FunctionField) :
    ∃ r s : E.toAffine.FunctionField, r ∈ F⟮genX E⟯ ∧ s ∈ F⟮genX E⟯ ∧ c = r + s * genY E := by
  set F₁ := F⟮genX E⟯
  have hfin : FiniteDimensional F₁ E.toAffine.FunctionField :=
    Module.finite_of_finrank_pos (by rw [finrank_adjoin_genX E]; norm_num)
  have hint : IsIntegral F₁ (genY E) := Algebra.IsIntegral.isIntegral _
  have htop : F₁⟮genY E⟯ = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := F),
      IntermediateField.adjoin_simple_adjoin_simple]
    exact adjoin_genX_genY E
  have hdeg : (minpoly F₁ (genY E)).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top',
      finrank_adjoin_genX E]
  have hc : c ∈ (F₁⟮genY E⟯).toSubalgebra := by rw [htop]; trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hc
  obtain ⟨p, rfl⟩ := hc
  have hm1 : minpoly F₁ (genY E) ≠ 1 := fun h => by rw [h, natDegree_one] at hdeg; omega
  have hq : (p %ₘ minpoly F₁ (genY E)).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p (minpoly.monic hint) hm1
    omega
  have hval : aeval (genY E) p = aeval (genY E) (p %ₘ minpoly F₁ (genY E)) :=
    (aeval_modByMonic_eq_self_of_root (minpoly.aeval F₁ (genY E))).symm
  obtain ⟨q, hqdef⟩ : ∃ q, q = p %ₘ minpoly F₁ (genY E) := ⟨_, rfl⟩
  rw [← hqdef] at hq hval
  refine ⟨(q.coeff 0 : E.toAffine.FunctionField), (q.coeff 1 : E.toAffine.FunctionField),
    (q.coeff 0).2, (q.coeff 1).2, ?_⟩
  change aeval (genY E) p = _
  rw [hval, eq_X_add_C_of_natDegree_le_one hq]
  simp only [map_add, map_mul, aeval_C, aeval_X, coeff_add, coeff_C_mul_X, coeff_C]
  simp
  ring

variable {F' : Type u} [Field F'] [Algebra F F']

theorem exists_algebraMap_eq_of_bcEmb {c : E.toAffine.FunctionField} {a : F'}
    (h : bcEmb (F' := F') E c = algebraMap F' (E.baseChange F').toAffine.FunctionField a) :
    ∃ a₀ : F, algebraMap F E.toAffine.FunctionField a₀ = c := by
  set K' := (E.baseChange F').toAffine.FunctionField
  have hinj : Function.Injective (bcEmb (F' := F') E) := (bcEmb (F' := F') E).toRingHom.injective
  have hmap : ∀ w ∈ F⟮genX E⟯, bcEmb (F' := F') E w ∈ F'⟮genX (E.baseChange F')⟯ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx, bcEmb_genX]; exact mem_adjoin_simple_self F' _
    | algebraMap x =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' K']
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  obtain ⟨r, s, hr, hs, rfl⟩ := exists_eq_add_mul_genY E c
  rw [map_add, map_mul, bcEmb_genY] at h
  have hs0 : bcEmb (F' := F') E s = 0 := by
    by_contra hne
    apply genY_not_mem (E.baseChange F')
    have e : genY (E.baseChange F') =
        (algebraMap F' K' a - bcEmb (F' := F') E r) / bcEmb (F' := F') E s := by
      rw [eq_div_iff hne]; linear_combination h
    rw [e]
    exact div_mem (sub_mem (IntermediateField.algebraMap_mem _ a) (hmap r hr)) (hmap s hs)
  have hs00 : s = 0 := hinj (by rw [hs0, map_zero])
  rw [hs0, zero_mul, add_zero] at h
  rw [hs00, zero_mul, add_zero]
  obtain ⟨p, q, rfl⟩ := (mem_adjoin_simple_iff F r).mp hr
  by_cases hq0 : aeval (genX E) q = 0
  · exact ⟨0, by rw [hq0, div_zero, map_zero]⟩
  have hq : q ≠ 0 := fun h0 => hq0 (by rw [h0, map_zero])
  have hq0' : aeval (genX (E.baseChange F')) q ≠ 0 := by
    rw [← bcEmb_genX, aeval_algHom_apply]
    exact fun h0 => hq0 (hinj (by rw [h0, map_zero]))
  rw [map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, bcEmb_genX, div_eq_iff hq0'] at h
  have key : aeval (genX (E.baseChange F'))
      (p.map (algebraMap F F') - C a * q.map (algebraMap F F')) = 0 := by
    rw [map_sub, map_mul, aeval_C, aeval_map_algebraMap, aeval_map_algebraMap]
    linear_combination h
  rw [aeval_genX_eq_zero_iff] at key
  have hcoeff : ∀ j, algebraMap F F' (p.coeff j) = a * algebraMap F F' (q.coeff j) := by
    intro j
    have := congrArg (coeff · j) key
    simp only [coeff_sub, coeff_map, coeff_C_mul, coeff_zero] at this
    linear_combination this
  have hqi : q.coeff q.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hq
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : F, a₀ = p.coeff q.natDegree / q.coeff q.natDegree := ⟨_, rfl⟩
  have ha : a = algebraMap F F' a₀ := by
    rw [ha₀, map_div₀, hcoeff, mul_div_cancel_right₀ _ ((_root_.map_ne_zero _).mpr hqi)]
  have hp : p = C a₀ * q := by
    ext j
    apply (algebraMap F F').injective
    rw [coeff_C_mul, map_mul, hcoeff j, ← ha]
  refine ⟨a₀, ?_⟩
  rw [hp, map_mul, aeval_C, mul_div_cancel_right₀ _ hq0]

end Descent

section Constant

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem exists_algebraMap_eq_isogCoeff (φ : Isogeny E E') :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = isogCoeff φ := by
  classical
  obtain ⟨b, hb⟩ := exists_isogCoeff_eq_algebraMap
    (isogBaseChange (F' := AlgebraicClosure F) φ)
  rw [isogCoeff_isogBaseChange] at hb
  exact exists_algebraMap_eq_of_bcEmb E hb.symm

noncomputable def invConst (φ : Isogeny E E') : F :=
  (exists_algebraMap_eq_isogCoeff φ).choose

theorem algebraMap_invConst (φ : Isogeny E E') :
    algebraMap F E.toAffine.FunctionField (invConst φ) = isogCoeff φ :=
  (exists_algebraMap_eq_isogCoeff φ).choose_spec

theorem isogenyPullback_eq_invConst_smul (φ : Isogeny E E') :
    isogenyPullback φ (invariantDifferential E') = invConst φ • invariantDifferential E := by
  rw [isogenyPullback_invariantDifferential_eq_smul, ← algebraMap_invConst, algebraMap_smul]

theorem invConst_add {φ ψ χ : Isogeny E E'} (h : χ.1 = φ.1 + ψ.1) :
    invConst χ = invConst φ + invConst ψ :=
  (algebraMap F E.toAffine.FunctionField).injective (by
    rw [map_add, algebraMap_invConst, algebraMap_invConst, algebraMap_invConst, isogCoeff_add h])

variable (E) in

theorem invConst_mulIsogeny (n : ℤ) (hn : n ≠ 0) : invConst (mulIsogeny E n hn) = n :=
  (algebraMap F E.toAffine.FunctionField).injective (by
    rw [algebraMap_invConst, isogCoeff_mulIsogeny, map_intCast])

theorem isSeparable_iff_invConst_ne_zero (φ : Isogeny E E') :
    φ.IsSeparable ↔ invConst φ ≠ 0 := by
  rw [isSeparable_iff_isogCoeff_ne_zero, ← algebraMap_invConst, ne_eq, ne_eq,
    map_eq_zero_iff _ (algebraMap F E.toAffine.FunctionField).injective]

theorem invConst_isogBaseChange {F' : Type u} [Field F'] [Algebra F F'] [DecidableEq F']
    (φ : Isogeny E E') :
    invConst (isogBaseChange (F' := F') φ) = algebraMap F F' (invConst φ) :=
  (algebraMap F' (E.baseChange F').toAffine.FunctionField).injective (by
    rw [algebraMap_invConst, isogCoeff_isogBaseChange, ← algebraMap_invConst, AlgHom.commutes,
      IsScalarTower.algebraMap_apply F F' (E.baseChange F').toAffine.FunctionField])

end Constant

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.DualDescentField
section
namespace GroundTheory.Global

open Polynomial GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff CoordinateRing)
open scoped Polynomial.Bivariate

universe u

section Coord

theorem eq_zero_of_aeval_genX_add_mul_genY {K : Type*} [Field K] (V : WeierstrassCurve K)
    {P Q : K[X]} (h : aeval (genX V) P + aeval (genX V) Q * genY V = 0) : P = 0 ∧ Q = 0 := by
  apply CoordinateRing.smul_basis_eq_zero (W' := V.toAffine)
  apply IsFractionRing.injective V.toAffine.CoordinateRing V.toAffine.FunctionField
  rw [map_zero, ← h, map_add, Algebra.smul_def, Algebra.smul_def, mul_one, map_mul,
    genX_eq, aeval_algebraMap_apply, aeval_algebraMap_apply, aeval_X_left_apply,
    aeval_X_left_apply, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rfl

end Coord

section LinearDisjoint

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] (W : WeierstrassCurve F)

theorem bcEmb_algebraMap_smul_basis (p q : F[X]) :
    bcEmb (F' := Ω) W (algebraMap W.toAffine.CoordinateRing _
      (p • 1 + q • CoordinateRing.mk W.toAffine Y)) =
      aeval (genX (W.baseChange Ω)) (p.map (algebraMap F Ω)) +
        aeval (genX (W.baseChange Ω)) (q.map (algebraMap F Ω)) * genY (W.baseChange Ω) := by
  have e : ∀ t : F[X], algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap F[X] W.toAffine.CoordinateRing t) = aeval (genX W) t := by
    intro t
    rw [← IsScalarTower.algebraMap_apply, genX_eq, aeval_algebraMap_apply, aeval_X_left_apply]
  rw [map_add, Algebra.smul_def, Algebra.smul_def, mul_one, map_add, map_mul, e, e,
    show algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (CoordinateRing.mk W.toAffine Y) = genY W from rfl, map_mul, ← aeval_algHom_apply,
    ← aeval_algHom_apply, bcEmb_genX, bcEmb_genY, aeval_map_algebraMap, aeval_map_algebraMap]

theorem coordinateRing_eq_zero_of_sum {ι : Type*} (s : Finset ι) {ω : ι → Ω}
    (hω : LinearIndependent F ω) (r : ι → W.toAffine.CoordinateRing)
    (h : ∑ i ∈ s, bcEmb (F' := Ω) W (algebraMap _ _ (r i)) * algebraMap Ω _ (ω i) = 0) :
    ∀ i ∈ s, r i = 0 := by
  choose p q hpq using fun i => CoordinateRing.exists_smul_basis_eq (r i)
  have e : ∀ i, bcEmb (F' := Ω) W (algebraMap _ _ (r i)) * algebraMap Ω _ (ω i) =
      aeval (genX (W.baseChange Ω)) (C (ω i) * (p i).map (algebraMap F Ω)) +
        aeval (genX (W.baseChange Ω)) (C (ω i) * (q i).map (algebraMap F Ω)) *
          genY (W.baseChange Ω) := by
    intro i
    rw [← hpq i, bcEmb_algebraMap_smul_basis]
    simp only [map_mul, aeval_C]
    ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum] at h
  obtain ⟨hP, hQ⟩ := eq_zero_of_aeval_genX_add_mul_genY _ h
  have hcoef : ∀ (t : ι → F[X]), ∑ i ∈ s, C (ω i) * (t i).map (algebraMap F Ω) = 0 →
      ∀ i ∈ s, t i = 0 := by
    intro t ht i hi
    ext n
    have hn := congrArg (coeff · n) ht
    simp only [finsetSum_coeff, coeff_C_mul, coeff_map, coeff_zero] at hn
    have hn' : ∑ j ∈ s, (t j).coeff n • ω j = 0 := by
      rw [← hn]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    rw [coeff_zero]
    exact linearIndependent_iff'.mp hω s (fun j => (t j).coeff n) hn' i hi
  intro i hi
  rw [← hpq i, hcoef p hP i hi, hcoef q hQ i hi, zero_smul, zero_smul, add_zero]

theorem linearDisjoint_bcEmb : (bcEmb (F' := Ω) W).fieldRange.LinearDisjoint Ω := by
  classical
  apply LinearDisjoint.of_basis_right' (Module.Basis.ofVectorSpace F Ω)
  rw [linearIndependent_iff']
  intro s g hg i hi
  choose α hα using fun j => AlgHom.mem_fieldRange.mp (g j).2
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors W.toAffine.CoordinateRing) s α
  choose! r hr using hc
  have hc0 : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (c : _) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors c.2
  have hsum : ∑ j ∈ s, bcEmb (F' := Ω) W (algebraMap _ _ (r j)) *
      algebraMap Ω _ (Module.Basis.ofVectorSpace F Ω j) = 0 := by
    have : ∀ j ∈ s, bcEmb (F' := Ω) W (algebraMap _ _ (r j)) *
        algebraMap Ω _ (Module.Basis.ofVectorSpace F Ω j) =
        bcEmb (F' := Ω) W (algebraMap W.toAffine.CoordinateRing _ c) *
          (g j • (algebraMap Ω _ ∘ Module.Basis.ofVectorSpace F Ω) j) := by
      intro j hj
      rw [hr j hj, Algebra.smul_def, map_mul, Function.comp_apply, Algebra.smul_def,
        mul_assoc]
      congr 2
      exact hα j
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hg, mul_zero]
  have h0 := coordinateRing_eq_zero_of_sum W s (Module.Basis.ofVectorSpace F Ω).linearIndependent r hsum i hi
  have : α i = 0 := by
    have := hr i hi
    rw [h0, map_zero, Algebra.smul_def] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hc0
  exact Subtype.ext (by rw [← hα i, this, map_zero]; rfl)

end LinearDisjoint

section Sup

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] (W : WeierstrassCurve F)

theorem sup_bcEmb_eq_top :
    (bcEmb (F' := Ω) W).fieldRange ⊔
      (IsScalarTower.toAlgHom F Ω (W.baseChange Ω).toAffine.FunctionField).fieldRange = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  have hz : z ∈ IntermediateField.adjoin Ω {genX (W.baseChange Ω), genY (W.baseChange Ω)} := by
    rw [adjoin_genX_genY]; trivial
  induction hz using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact (le_sup_left : (bcEmb (F' := Ω) W).fieldRange ≤ _) ⟨genX W, bcEmb_genX W⟩
    · exact (le_sup_left : (bcEmb (F' := Ω) W).fieldRange ≤ _) ⟨genY W, bcEmb_genY W⟩
  | algebraMap x =>
    exact (le_sup_right : (IsScalarTower.toAlgHom F Ω _).fieldRange ≤ _) ⟨x, rfl⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | inv x _ hx => exact inv_mem hx
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem sup_toSubalgebra_bcEmb_eq_top [Algebra.IsAlgebraic F Ω] :
    (bcEmb (F' := Ω) W).fieldRange.toSubalgebra ⊔
      (IsScalarTower.toAlgHom F Ω (W.baseChange Ω).toAffine.FunctionField).fieldRange.toSubalgebra =
        ⊤ := by
  have : Algebra.IsAlgebraic F
      (IsScalarTower.toAlgHom F Ω (W.baseChange Ω).toAffine.FunctionField).fieldRange :=
    ⟨fun ⟨x, hx⟩ => by
      obtain ⟨ω, rfl⟩ := AlgHom.mem_fieldRange.mp hx
      exact isAlgebraic_iff.mpr ((Algebra.IsAlgebraic.isAlgebraic ω).algHom _)⟩
  rw [← sup_toSubalgebra_of_isAlgebraic_right, sup_bcEmb_eq_top, top_toSubalgebra]

end Sup

section Descent

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
  {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem comap_isogBaseChange_bcEmb (φ : Isogeny E E') (g : E'.toAffine.FunctionField) :
    (isogBaseChange (F' := Ω) φ).comap (bcEmb (F' := Ω) E' g) = bcEmb (F' := Ω) E (φ.comap g) := by
  obtain ⟨⟨x, y, h, he, -⟩, -⟩ := φ.2
  have hx : (isogBaseChange (F' := Ω) φ).x = bcEmb (F' := Ω) E φ.x := by
    simp only [Isogeny.x, isogBaseChange_val, he]
    rfl
  have hy : (isogBaseChange (F' := Ω) φ).y = bcEmb (F' := Ω) E φ.y := by
    simp only [Isogeny.y, isogBaseChange_val, he]
    rfl
  have : ((isogBaseChange (F' := Ω) φ).comap.restrictScalars F).comp (bcEmb (F' := Ω) E') =
      (bcEmb (F' := Ω) E).comp φ.comap := by
    apply algHom_ext_gen E'
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, bcEmb_genX, Isogeny.comap_genX, hx]
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, bcEmb_genY, Isogeny.comap_genY, hy]
  exact DFunLike.congr_fun this g

theorem mem_fieldRange_comap_of_bcEmb [Algebra.IsAlgebraic F Ω] (φ : Isogeny E E')
    {f : E.toAffine.FunctionField}
    (hf : bcEmb (F' := Ω) E f ∈ (isogBaseChange (F' := Ω) φ).comap.fieldRange) :
    f ∈ φ.comap.fieldRange := by
  classical
  set ι := bcEmb (F' := Ω) E
  set ψ := isogBaseChange (F' := Ω) φ
  set Ω₁ := (IsScalarTower.toAlgHom F Ω (E.baseChange Ω).toAffine.FunctionField).fieldRange
  have H : ι.fieldRange.LinearDisjoint Ω₁ :=
    linearDisjoint_iff'.2 (by rw [AlgHom.fieldRange_toSubalgebra]; exact linearDisjoint_bcEmb E)
  set b := Module.Basis.ofVectorSpace F Ω₁
  set bb := H.basisOfBasisRight (sup_toSubalgebra_bcEmb_eq_top E) b
  have hrepr : ∀ (x : Ω₁) (i : Module.Basis.ofVectorSpaceIndex F Ω₁),
      ((bb.repr (x : (E.baseChange Ω).toAffine.FunctionField) i : ι.fieldRange) :
        (E.baseChange Ω).toAffine.FunctionField) = algebraMap F _ (b.repr x i) :=
    fun x i => H.algebraMap_basisOfBasisRight_repr_apply _ b x i
  obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : b.repr 1 = 0 := Finsupp.ext hcon
    exact one_ne_zero (b.repr.injective (h1.trans (map_zero _).symm))
  set N₁ := (ι.comp φ.comap).fieldRange
  set c : (E.baseChange Ω).toAffine.FunctionField →ₗ[ι.fieldRange] ι.fieldRange := bb.coord i
  have hc : ∀ (a : ι.fieldRange) (z : (E.baseChange Ω).toAffine.FunctionField),
      ((c ((a : (E.baseChange Ω).toAffine.FunctionField) * z) : ι.fieldRange) :
        (E.baseChange Ω).toAffine.FunctionField) = a * (c z : (E.baseChange Ω).toAffine.FunctionField) := by
    intro a z
    change ((c (a • z) : ι.fieldRange) : (E.baseChange Ω).toAffine.FunctionField) = _
    rw [map_smul, smul_eq_mul, IntermediateField.coe_mul]
  have hcΩ : ∀ ω : Ω, ((c (algebraMap Ω (E.baseChange Ω).toAffine.FunctionField ω) : ι.fieldRange) :
      (E.baseChange Ω).toAffine.FunctionField) ∈ N₁ := by
    intro ω
    have := hrepr ⟨algebraMap Ω _ ω, ⟨ω, rfl⟩⟩ i
    change ((c (algebraMap Ω (E.baseChange Ω).toAffine.FunctionField ω) : ι.fieldRange) :
      (E.baseChange Ω).toAffine.FunctionField) = _ at this
    rw [this]
    exact IntermediateField.algebraMap_mem N₁ _

  set T : (E'.baseChange Ω).toAffine.FunctionField →ₗ[F] (E.baseChange Ω).toAffine.FunctionField :=
    (ι.fieldRange.val.toLinearMap.comp (c.restrictScalars F)).comp
      (ψ.comap.restrictScalars F).toLinearMap
  have hT : ∀ z, T z = ((c (ψ.comap z) : ι.fieldRange) : (E.baseChange Ω).toAffine.FunctionField) :=
    fun z => rfl
  have hle : Subalgebra.toSubmodule (bcEmb (F' := Ω) E').fieldRange.toSubalgebra *
      Subalgebra.toSubmodule
        (IsScalarTower.toAlgHom F Ω (E'.baseChange Ω).toAffine.FunctionField).fieldRange.toSubalgebra ≤
      (Subalgebra.toSubmodule N₁.toSubalgebra).comap T := by
    rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨a, rfl⟩ := AlgHom.mem_fieldRange.mp hm
    obtain ⟨ω, rfl⟩ := AlgHom.mem_fieldRange.mp hn
    rw [Submodule.mem_comap, Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra]
    have e1 : ψ.comap (bcEmb (F' := Ω) E' a *
        IsScalarTower.toAlgHom F Ω (E'.baseChange Ω).toAffine.FunctionField ω) =
        ι (φ.comap a) * algebraMap Ω (E.baseChange Ω).toAffine.FunctionField ω := by
      rw [map_mul, comap_isogBaseChange_bcEmb, IsScalarTower.coe_toAlgHom', AlgHom.commutes]
    rw [hT, e1, hc ⟨ι (φ.comap a), ⟨φ.comap a, rfl⟩⟩]
    exact mul_mem ⟨a, rfl⟩ (hcΩ ω)
  obtain ⟨z, hz⟩ := AlgHom.mem_fieldRange.mp hf
  have hzT : T z ∈ N₁ := by
    have h3 : z ∈ Subalgebra.toSubmodule (bcEmb (F' := Ω) E').fieldRange.toSubalgebra *
        Subalgebra.toSubmodule
          (IsScalarTower.toAlgHom F Ω (E'.baseChange Ω).toAffine.FunctionField).fieldRange.toSubalgebra := by
      rw [Subalgebra.mul_toSubmodule, sup_toSubalgebra_bcEmb_eq_top]
      trivial
    have h4 := hle h3
    rwa [Submodule.mem_comap, Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra] at h4
  have e2 : T z = ι f * algebraMap F _ (b.repr 1 i) := by
    have h1 := hc ⟨ι f, ⟨f, rfl⟩⟩ 1
    rw [mul_one] at h1
    rw [hT, hz, h1]
    congr 1
    exact hrepr 1 i
  have hmem : ι f ∈ N₁ := by
    have := mul_mem hzT (IntermediateField.algebraMap_mem N₁ (b.repr 1 i)⁻¹)
    rwa [e2, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one] at this
  obtain ⟨g, hg⟩ := AlgHom.mem_fieldRange.mp hmem
  exact ⟨g, ι.injective hg⟩

end Descent

end GroundTheory.Global
end

