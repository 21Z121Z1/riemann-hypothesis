import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Formalism.HermitianLattices.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometry
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TupleJac

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_int_basis [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∃ c : Module.Basis (Fin 2) F E, (∀ x, x ∈ L.O ↔ ∀ i, c.repr x i ∈ 𝒪[F]) ∧
      ∀ x, algebraMap F E (Algebra.norm F x) = x * L.cj x := by
  obtain ⟨ω, hω, e, he, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hu : IsUnit (ω - L.cj ω) := IsUnit.of_mul_eq_one e hωe
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    simp only [Algebra.smul_def, mul_one] at h
    have h' := congrArg L.cj h
    simp only [map_add, map_mul, AlgEquiv.commutes, map_zero] at h'
    have hb : algebraMap F E b = 0 := hu.mul_left_eq_zero.1 (by linear_combination h - h')
    have ha : algebraMap F E a = 0 := by rw [hb] at h; simpa using h
    exact ⟨hinj (by simpa using ha), hinj (by simpa using hb)⟩
  let c : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [L.rank])
  have hc0 : c 0 = 1 := by simp [c]
  have hc1 : c 1 = ω := by simp [c]
  have hx : ∀ x, x = algebraMap F E (c.repr x 0) + algebraMap F E (c.repr x 1) * ω := by
    intro x
    have := c.sum_repr x
    simp only [Fin.sum_univ_two, hc0, hc1, Algebra.smul_def, mul_one] at this
    exact this.symm
  have hr : ∀ a b : F, c.repr (algebraMap F E a + algebraMap F E b * ω) 0 = a ∧
      c.repr (algebraMap F E a + algebraMap F E b * ω) 1 = b := by
    intro a b
    have : algebraMap F E a + algebraMap F E b * ω = a • c 0 + b • c 1 := by
      simp [hc0, hc1, Algebra.smul_def]
    rw [this]
    simp
  refine ⟨c, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · have h1 := congrArg L.cj (hx x)
    simp only [map_add, map_mul, AlgEquiv.commutes] at h1
    have hb : algebraMap F E (c.repr x 1) ∈ L.O := by
      have : algebraMap F E (c.repr x 1) = (x - L.cj x) * e := by
        linear_combination (-e) * hx x + e * h1 - algebraMap F E (c.repr x 1) * hωe
      rw [this]
      exact L.O.mul_mem (L.O.sub_mem h (GlobalTheory.UnramOrder.cj_mem L h)) he
    have ha : algebraMap F E (c.repr x 0) ∈ L.O := by
      have : algebraMap F E (c.repr x 0) = x - algebraMap F E (c.repr x 1) * ω := by
        linear_combination - hx x
      rw [this]
      exact L.O.sub_mem h (L.O.mul_mem hb hω)
    intro i
    fin_cases i
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 ha
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 hb
  · rw [hx x]
    exact L.O.add_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (h 0))
      (L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (h 1)) hω)
  · obtain ⟨t, ht⟩ := (L.cj_fix (ω + L.cj ω)).1 (by simp [L.cj_cj, add_comm])
    obtain ⟨N, hN⟩ := (L.cj_fix (ω * L.cj ω)).1 (by simp [L.cj_cj, mul_comm])
    obtain ⟨a, b, rfl⟩ : ∃ a b : F, x = algebraMap F E a + algebraMap F E b * ω := ⟨_, _, hx x⟩
    have h2 : (algebraMap F E a + algebraMap F E b * ω) * ω
        = algebraMap F E (-(b * N)) + algebraMap F E (a + b * t) * ω := by
      simp only [map_add, map_mul, map_neg, ht, hN]; ring
    rw [Algebra.norm_eq_matrix_det c, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hc0, hc1, mul_one, h2, (hr _ _).1, (hr _ _).2]
    simp only [map_add, map_mul, map_neg, map_sub, ht, hN, AlgEquiv.commutes]
    ring

theorem exists_lat_basis [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (hH : IsHermND L Hm) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) :
    ∃ B : Module.Basis (Fin n) E (Fin n → E), ∀ x, x ∈ Λ ↔ ∀ i, B.repr x i ∈ L.O := by
  obtain ⟨b, hb, rfl⟩ := (GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).1 Λ hΛ
  have hli : LinearIndependent E b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    let f : (Fin n → E) →ₗ[E] E :=
      { toFun := fun x => hf L Hm x (b j)
        map_add' := fun x y => by simp [hf, add_mul, Finset.sum_add_distrib]
        map_smul' := fun c x => by simp [hf, Finset.mul_sum, mul_assoc] }
    have hfb : ∀ i, f (b i) = if i = j then 1 else 0 := fun i => hb i j
    have := congrArg f hg
    simpa [map_sum, hfb] using this
  have hsp : ⊤ ≤ Submodule.span E (Set.range b) := by
    rw [← hΛ.1.2, Submodule.span_span_of_tower]
  refine ⟨Module.Basis.mk hli hsp, fun x => ?_⟩
  set B := Module.Basis.mk hli hsp with hB
  have hBb : ∀ i, B i = b i := fun i => by simp [hB]
  constructor
  · intro hx i
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    have : ∑ j, c j • b j = ∑ j, (c j : E) • B j := by simp only [hBb]; rfl
    rw [this, B.repr_sum_self]
    exact (c i).2
  · intro hx
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨_, hx i⟩, ?_⟩
    conv_rhs => rw [← B.sum_repr x]
    simp only [hBb]; rfl

theorem cont_linearEquiv [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (ϖ : 𝒪[F])
    (hϖ : Irreducible ϖ) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (hH : IsHermND L Hm) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) (m : ℕ) (φ : (Fin m → Fin n → E) ≃ₗ[E] (Fin m → Fin n → E))
    (a : ℤ) (u : (𝒪[F])ˣ)
    (hd : LinearMap.det φ.toLinearMap * L.cj (LinearMap.det φ.toLinearMap)
      = algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F))) :
    ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) (φ '' T) ∧
      cont (tupLat L Λ m) (φ '' T) = (resQ ϖ : ℝ) ^ (-a) * cont (tupLat L Λ m) T := by
  obtain ⟨c, hc, hN⟩ := exists_int_basis L
  obtain ⟨B, hB⟩ := exists_lat_basis L Hm hH Λ hΛ
  have := L.free
  have h := GlobalTheory.T.relative_lattice_volume_of_det_valuation ϖ hϖ (Pi.basis fun _ : Fin m => c.smulTower B) (φ.restrictScalars F) a u
    (by
      apply GlobalTheory.UnramOrder.algebraMap_inj L
      rw [← hd, ← hN, ← LinearMap.det_restrictScalars]
      rfl) (tupLat L Λ m) (by
      intro x
      simp only [tupLat, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff,
        Submodule.mem_toAddSubgroup, hB, hc, Pi.basis_repr, Module.Basis.smulTower_repr]
      exact ⟨fun h i => h _ _ _, fun h j i k => h ⟨j, (k, i)⟩⟩)
  intro T hT
  have h2 := GlobalTheory.HL.ContAut.cont_image (tupLat L Λ m) (φ.restrictScalars F).toAddEquiv h.1 h.2.1 T hT
  rw [h.2.2] at h2
  exact h2

def rmulL {n m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    (Fin m → Fin n → E) →ₗ[E] (Fin m → Fin n → E) where
  toFun x := rmul x A
  map_add' x y := by ext j k; simp [rmul, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext j k; simp [rmul, Finset.mul_sum, mul_left_comm]

def swapL (n m : ℕ) : (Fin n → Fin m → E) ≃ₗ[E] (Fin m → Fin n → E) where
  toFun x := fun j k => x k j
  invFun x := fun j k => x k j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [TopologicalSpace E] in
theorem det_rmulL {n m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (rmulL (n := n) A) = A.det ^ n := by
  have h : rmulL (n := n) A = (swapL n m).toLinearMap ∘ₗ
      (LinearMap.pi fun i : Fin n => (Matrix.toLin' A.transpose) ∘ₗ LinearMap.proj i) ∘ₗ
      (swapL n m).symm.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    ext j k
    simp [rmulL, rmul, swapL, Matrix.mulVec, dotProduct]
  rw [h, LinearMap.det_conj, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

theorem det_isom (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (hH : IsUnit Hm.det)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (hg : g ∈ isomG L Hm) :
    LinearMap.det g.toLinearMap * L.cj (LinearMap.det g.toLinearMap) = 1 := by
  set M := LinearMap.toMatrix' g.toLinearMap with hM
  have h : M.transpose * Hm * (L.cj.toRingEquiv.toRingHom.mapMatrix M) = Hm := by
    ext i j
    have h1 := hg (Pi.single i 1) (Pi.single j 1)
    have h2 : hf L Hm (Pi.single i 1) (Pi.single j 1) = Hm i j := by
      simp [hf, Pi.single_apply, apply_ite L.cj]
    rw [h2] at h1
    rw [← h1, hf, Finset.sum_comm]
    simp [hM, Matrix.mul_apply, Finset.sum_mul, LinearMap.toMatrix'_apply]
  have h3 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, hM,
    LinearMap.det_toMatrix'] at h3
  refine hH.mul_left_cancel ?_
  rw [mul_one]
  conv_rhs => rw [← h3]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
    AlgEquiv.toRingEquiv_eq_coe]
  ring

end GlobalTheory.HL.TupleJac

theorem GlobalTheory.HL.TupleJac.tuple_jacobian : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ m : ℕ, (∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x => rmul x A) '' T) ∧ cont (tupLat L Λ m) ((fun x => rmul x A) '' T) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * n)) * cont (tupLat L Λ m) T) ∧ ∀ g ∈ isomG L Hm, ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x a => g (x a)) '' T) ∧ cont (tupLat L Λ m) ((fun x a => g (x a)) '' T) = cont (tupLat L Λ m) T := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λ hΛ m
  refine ⟨fun A hA => ?_, fun g hg T hT => ?_⟩
  · obtain ⟨N, hN⟩ := (L.cj_fix (A.det * L.cj A.det)).1 (by simp [L.cj_cj, mul_comm])
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
    have hN0 : N ≠ 0 := by
      rintro rfl
      rw [map_zero] at hN
      exact (hA.mul (hA.map L.cj)).ne_zero hN.symm
    obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).2.2.2 N hN0
    have hdet : IsUnit (LinearMap.det (TupleJac.rmulL (n := n) A)) := by
      rw [TupleJac.det_rmulL]; exact hA.pow n
    have hφ : (LinearMap.equivOfIsUnitDet hdet).toLinearMap = TupleJac.rmulL (n := n) A :=
      LinearMap.coe_equivOfIsUnitDet hdet
    have key := TupleJac.cont_linearEquiv L ϖ hϖ Hm hH Λ hΛ m (LinearMap.equivOfIsUnitDet hdet)
      (vE L ϖ (A.det * L.cj A.det) * n) (u ^ n) (by
        rw [hφ, TupleJac.det_rmulL, map_pow, ← mul_pow, ← hN, ← map_pow]
        congr 1
        conv_lhs => rw [hu]
        rw [mul_pow, zpow_mul, zpow_natCast]
        simp)
    have hfun : (LinearMap.equivOfIsUnitDet hdet : _ → _) = fun x => rmul x A :=
      funext fun x => LinearMap.congr_fun hφ x
    rw [hfun] at key
    exact key
  · have key := TupleJac.cont_linearEquiv L ϖ hϖ Hm hH Λ hΛ m
      (LinearEquiv.piCongrRight fun _ => g) 0 1 (by
        have h : (LinearEquiv.piCongrRight fun _ : Fin m => g).toLinearMap =
            LinearMap.pi fun i : Fin m => g.toLinearMap ∘ₗ LinearMap.proj i := rfl
        rw [h, LinearMap.det_pi, Finset.prod_const, map_pow, ← mul_pow,
          TupleJac.det_isom L Hm hH.2 g hg]
        simp) T hT
    rw [neg_zero, zpow_zero, one_mul] at key
    exact key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularCloseToOneInverseClose
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

theorem unitriangular_inv_close {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (M : Matrix (Fin n) (Fin n) E) (t : E) (ht : t ∈ L.O) (hlow : ∀ i j, j < i → M i j = 0) (hdiag : ∀ i, M i i = 1) (hcl : ∀ i j, ∃ o ∈ L.O, (M - 1) i j = t * o) : ∃ Mi : Matrix (Fin n) (Fin n) E, Mi * M = 1 ∧ M * Mi = 1 ∧ ∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o := by
  have hMO : ∀ i j, M i j ∈ L.O := by
    intro i j
    obtain ⟨o, ho, he⟩ := hcl i j
    have : M i j = t * o + (1 : Matrix (Fin n) (Fin n) E) i j := by
      rw [← he]; simp
    rw [this]
    refine L.O.add_mem (L.O.mul_mem ht ho) ?_
    by_cases h : i = j
    · subst h; simp [L.O.one_mem]
    · simp [h, L.O.zero_mem]
  let f : L.O →+* E := L.O.subtype
  let M' : Matrix (Fin n) (Fin n) L.O := Matrix.of fun i j => ⟨M i j, hMO i j⟩
  have hM' : f.mapMatrix M' = M := by
    ext i j; rfl
  have hdet : M'.det = 1 := by
    apply Subtype.ext
    have h1 : f M'.det = (f.mapMatrix M').det := RingHom.map_det f M'
    have h2 : M.det = 1 := by
      rw [Matrix.det_of_upperTriangular (M := M) (fun i j hij => hlow i j hij)]
      simp [hdiag]
    change f M'.det = f 1
    rw [h1, hM', h2, map_one]
  have hu : IsUnit M'.det := by rw [hdet]; exact isUnit_one
  refine ⟨f.mapMatrix M'⁻¹, ?_, ?_, ?_⟩
  · rw [← hM', ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
  · rw [← hM', ← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]
  · intro i j
    set Mi := f.mapMatrix M'⁻¹ with hMi
    have hinv : Mi * M = 1 := by
      rw [hMi, ← hM', ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
    have key : Mi - 1 = -(Mi * (M - 1)) := by
      rw [Matrix.mul_sub, hinv, Matrix.mul_one]; abel
    choose o ho he using hcl
    refine ⟨-(∑ k, (M'⁻¹ i k : E) * o k j), ?_, ?_⟩
    · exact L.O.neg_mem (L.O.sum_mem fun k _ => L.O.mul_mem (M'⁻¹ i k).2 (ho k j))
    · rw [key, Matrix.neg_apply, Matrix.mul_apply]
      simp only [he]
      rw [mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hMi, f]
      ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumePosSimplexLe
section
open MeasureTheory NumberField Finset

namespace GlobalTheory.SimplexVolume

theorem volume_l1_ball (ι : Type) [Fintype ι] [Nonempty ι] (L : ℝ) (hL : 0 ≤ L) :
    volume {x : ι → ℝ | ∑ i, |x i| ≤ L} =
      2 ^ Fintype.card ι * ENNReal.ofReal (L ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  have h := MeasureTheory.volume_sum_rpow_le ι (p := 1) le_rfl L
  simp only [Real.rpow_one, div_one, one_add_one_eq_two, Real.Gamma_two, mul_one,
    Real.Gamma_nat_eq_factorial] at h
  rw [h, ← ENNReal.ofReal_pow hL, ← ENNReal.ofReal_mul (by positivity)]
  have h2 : (2 : ENNReal) ^ Fintype.card ι = ENNReal.ofReal (2 ^ Fintype.card ι) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [h2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem volume_pos_simplex_le (ι : Type) [Fintype ι] [Nonempty ι] (L : ℝ) (hL : 0 ≤ L) :
    volume {x : ι → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i ≤ L} ≤
      ENNReal.ofReal (L ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  classical
  set S : Set (ι → ℝ) := {x : ι → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i ≤ L} with hS
  have hSm : MeasurableSet S := by
    rw [hS]
    measurability
  let f : (ι → Bool) → ι → ℝ → ℝ := fun e i y => if e i then y else -y
  have hf : ∀ e i, MeasurePreserving (f e i) volume volume := by
    intro e i
    by_cases h : e i
    · simp only [f, h, if_true]
      exact MeasurePreserving.id (volume : Measure ℝ)
    · simpa [f, h] using Measure.measurePreserving_neg (volume : Measure ℝ)
  let R : (ι → Bool) → (ι → ℝ) → (ι → ℝ) := fun e x i => f e i (x i)
  have hR : ∀ e, MeasurePreserving (R e) volume volume := fun e =>
    volume_preserving_pi (fun i => hf e i)
  have hdisj : Pairwise (Function.onFun Disjoint fun e => R e ⁻¹' S) := by
    intro e e' hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    apply hne
    funext i
    have h1 := hx.1 i
    have h2 := hx'.1 i
    simp only [R, f] at h1 h2
    cases he : e i <;> cases he' : e' i <;> simp [he, he'] at h1 h2 ⊢ <;> linarith
  have hsub : (⋃ e, R e ⁻¹' S) ⊆ {x : ι → ℝ | ∑ i, |x i| ≤ L} := by
    intro x hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.1 hx
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) he.2
    have h1 := he.1 i
    rw [← abs_of_pos h1]
    simp only [R, f]
    split_ifs <;> simp
  have hU : volume (⋃ e, R e ⁻¹' S) = 2 ^ Fintype.card ι * volume S := by
    rw [measure_iUnion hdisj (fun e => (hR e).measurable hSm)]
    simp only [fun e => (hR e).measure_preimage hSm.nullMeasurableSet]
    simp [tsum_fintype]
  have hle := measure_mono (μ := volume) hsub
  rw [hU, volume_l1_ball ι L hL] at hle
  exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 hle

theorem volume_simplex_le (ι : Type) [Fintype ι] (a : ι → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    volume {t : ι → ℝ | (∀ i, a i ≤ t i) ∧ ∑ i, (t i - a i) ≤ L} ≤
      ENNReal.ofReal (L ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine le_trans (measure_mono (Set.subset_univ _)) ?_
    simp [volume_pi]
  · have hsub : {t : ι → ℝ | (∀ i, a i ≤ t i) ∧ ∑ i, (t i - a i) ≤ L} ⊆
        ((fun t => t - a) ⁻¹' {x : ι → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i ≤ L}) ∪
          ⋃ i, {t : ι → ℝ | t i = a i} := by
      intro t ht
      by_cases h : ∃ i, t i = a i
      · exact Or.inr (Set.mem_iUnion.2 h)
      · push Not at h
        refine Or.inl ⟨fun i => ?_, ht.2⟩
        exact sub_pos.2 (lt_of_le_of_ne (ht.1 i) (h i).symm)
    have hnull : volume (⋃ i, {t : ι → ℝ | t i = a i}) = 0 :=
      measure_iUnion_null fun i => Measure.pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) i (a i)
    refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
    rw [hnull, add_zero]
    simp only [sub_eq_add_neg]
    rw [measure_preimage_add_right]
    exact volume_pos_simplex_le ι L hL

end GlobalTheory.SimplexVolume
end

