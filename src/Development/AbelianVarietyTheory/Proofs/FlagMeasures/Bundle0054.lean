import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
import Formalism.HermitianLattices.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandardStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_unipotent_translate_standard : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ Λ, IsSD L S.Hm Λ → ∀ n ∈ S.Nof g, (∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g (r + 1)) ↔ x ∈ Submodule.span L.O (Set.range fun b => n (g b))) → ∃ A, S.IsInner g gs A ∧ ∃ n₁ ∈ S.Nof g, (∀ b, n₁ (g b) = n (g b)) ∧ Λ = n₁ • S.stdLat g gs A := by
  first | exact @GlobalTheory.HL.FrameLift.lift | exact GlobalTheory.HL.FrameLift.lift | (intros; apply GlobalTheory.HL.FrameLift.lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanEqMap
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.MatrixIndex

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_basis [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∃ b : Module.Basis (Fin 2) F E, (∀ x, x ∈ L.O ↔ ∀ i, b.repr x i ∈ 𝒪[F]) ∧
      ∀ x, algebraMap F E (Algebra.norm F x) = x * L.cj x := by
  obtain ⟨ω, hω, e, he, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hint : ∀ a : F, a ∈ 𝒪[F] → algebraMap F E a ∈ L.O := fun a h =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 h
  have he' : (L.cj ω - ω) * L.cj e = 1 := by simpa [L.cj_cj] using congrArg L.cj hωe
  have hce : L.cj e = -e := by linear_combination (-e) * he' - (L.cj e) * hωe
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    simp only [Algebra.smul_def, mul_one] at h
    have h' := congrArg L.cj h
    simp only [map_add, map_mul, AlgEquiv.commutes, map_zero] at h'
    have ht : algebraMap F E t = 0 := by
      linear_combination e * h - e * h' - algebraMap F E t * hωe
    have hs : algebraMap F E s = 0 := by rw [ht] at h; simpa using h
    exact ⟨GlobalTheory.UnramOrder.algebraMap_inj L (by simpa using hs),
      GlobalTheory.UnramOrder.algebraMap_inj L (by simpa using ht)⟩
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [L.rank])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = ω := by simp [b]
  have hx : ∀ x, x = algebraMap F E (b.repr x 0) + algebraMap F E (b.repr x 1) * ω := by
    intro x
    have := b.sum_repr x
    rw [Fin.sum_univ_two, hb0, hb1] at this
    simpa [Algebra.smul_def] using this.symm
  refine ⟨b, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · have h1 := hx x
    have h2 := congrArg L.cj h1
    simp only [map_add, map_mul, AlgEquiv.commutes] at h2
    have h3 : algebraMap F E (b.repr x 1) = (x - L.cj x) * e := by
      linear_combination -e * h1 + e * h2 - algebraMap F E (b.repr x 1) * hωe
    have h4 : algebraMap F E (b.repr x 1) ∈ L.O := by
      rw [h3]
      exact L.O.mul_mem (L.O.sub_mem h (GlobalTheory.UnramOrder.cj_mem L h)) he
    have h5 : algebraMap F E (b.repr x 0) ∈ L.O := by
      have : algebraMap F E (b.repr x 0) = x - algebraMap F E (b.repr x 1) * ω := by
        linear_combination -h1
      rw [this]
      exact L.O.sub_mem h (L.O.mul_mem h4 hω)
    intro i
    fin_cases i
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 h5
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 h4
  · rw [hx x]
    exact L.O.add_mem (hint _ (h 0)) (L.O.mul_mem (hint _ (h 1)) hω)
  · rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, mul_one, map_sub, map_mul]
    have h1 := hx x
    have h2 := congrArg L.cj h1
    have h3 := hx (x * ω)
    have h4 := congrArg L.cj h3
    simp only [map_add, map_mul, AlgEquiv.commutes] at h2 h4
    generalize algebraMap F E (b.repr x 0) = a at *
    generalize algebraMap F E (b.repr x 1) = c at *
    generalize algebraMap F E (b.repr (x * ω) 0) = a' at *
    generalize algebraMap F E (b.repr (x * ω) 1) = c' at *
    have key : (ω - L.cj ω) * (a * c' - a' * c - x * L.cj x) = 0 := by
      linear_combination (-(L.cj x)) * h3 + x * h4 + (a' + c' * L.cj ω) * h1 - (a' + c' * ω) * h2
    linear_combination e * key - (a * c' - a' * c - x * L.cj x) * hωe

theorem span_eq_map (L : LocE F E) {n m : ℕ} (y : Fin m → Fin n → E) :
    (Submodule.span L.O (Set.range y)).toAddSubgroup =
      (AddSubgroup.pi Set.univ fun _ : Fin m => L.O.toAddSubgroup).map
        (Fintype.linearCombination E y).toAddMonoidHom := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun,
    AddSubgroup.mem_map, AddSubgroup.mem_pi, Set.mem_univ, forall_true_left,
    LinearMap.toAddMonoidHom_coe, Fintype.linearCombination_apply, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c i, fun i => (c i).2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun i => ⟨c i, hc i⟩, rfl⟩

theorem index_rmul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n m : ℕ} (y : Fin m → Fin n → E), LinearIndependent E y → ∀ A : Matrix (Fin m) (Fin m) E, IsIntM L A → IsUnit A.det → 0 ≤ vE L ϖ (A.det * L.cj A.det) ∧ (Submodule.span L.O (Set.range (rmul y A))).toAddSubgroup.relIndex (Submodule.span L.O (Set.range y)).toAddSubgroup = resQ ϖ ^ (vE L ϖ (A.det * L.cj A.det)).toNat := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n m y hy A hA hu
  obtain ⟨b, hbO, hnorm⟩ := exists_basis L
  have := L.free
  have : Module.Finite F E := Module.Finite.of_basis b
  obtain ⟨-, -, hv3, hv4⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  have hdO : A.det ∈ L.O := by
    rw [Matrix.det_apply']
    exact L.O.sum_mem fun σ _ => L.O.mul_mem (intCast_mem _ _) (L.O.prod_mem fun i _ => hA _ _)
  have hN0 : Algebra.norm F A.det ≠ 0 := (hu.map (Algebra.norm F)).ne_zero
  have hNO : Algebra.norm F A.det ∈ 𝒪[F] := by
    rw [← GlobalTheory.UnramOrder.algebraMap_mem_iff L, hnorm]
    exact L.O.mul_mem hdO (GlobalTheory.UnramOrder.cj_mem L hdO)
  rw [← hnorm]
  have ha := (hv3 _ hN0).2 hNO
  obtain ⟨u, hu'⟩ := hv4 _ hN0
  refine ⟨ha, ?_⟩
  generalize vE L ϖ (algebraMap F E (Algebra.norm F A.det)) = a at *
  let φ : (Fin m → E) ≃ₗ[F] (Fin m → E) :=
    (Matrix.toLinearEquiv (Pi.basisFun E (Fin m)) A hu).restrictScalars F
  have hφ : ∀ v, φ v = A.mulVec v := fun v => by
    simp [φ, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin']
  have hdet : LinearMap.det (φ : (Fin m → E) →ₗ[F] (Fin m → E)) = Algebra.norm F A.det := by
    have : (φ : (Fin m → E) →ₗ[F] (Fin m → E)) = (Matrix.toLin' A).restrictScalars F := by
      ext1 v; exact LinearMap.ext fun w => hφ _
    rw [this, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  set W0 := (AddSubgroup.pi Set.univ fun _ : Fin m => L.O.toAddSubgroup) with hW0
  have hmem : ∀ x, x ∈ W0 ↔ ∀ i, x i ∈ L.O := fun x => by
    simp [hW0, AddSubgroup.mem_pi]
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.relative_lattice_volume_of_det_valuation ϖ hϖ (Pi.basis fun _ : Fin m => b) φ a u (hdet.trans hu') W0
    (fun x => by
      simp only [hmem, hbO, Pi.basis_repr, Sigma.forall])
  have hle : W0.map φ.toAddEquiv.toAddMonoidHom ≤ W0 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hmem]
    intro i
    change φ v i ∈ _
    rw [hφ, Matrix.mulVec, dotProduct]
    exact L.O.sum_mem fun j _ => L.O.mul_mem (hA _ _) ((hmem v).1 hv j)
  have hcomp : (Fintype.linearCombination E (rmul y A)).toAddMonoidHom =
      (Fintype.linearCombination E y).toAddMonoidHom.comp φ.toAddEquiv.toAddMonoidHom := by
    refine AddMonoidHom.ext fun v => ?_
    change Fintype.linearCombination E (rmul y A) v = Fintype.linearCombination E y (φ v)
    rw [hφ]
    simp only [Fintype.linearCombination_apply, rmul, Matrix.mulVec, dotProduct, Finset.smul_sum,
      Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hinj : Function.Injective (Fintype.linearCombination E y).toAddMonoidHom := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact funext (Fintype.linearIndependent_iff.1 hy v hv)
  rw [span_eq_map, span_eq_map, ← hW0, hcomp, ← AddSubgroup.map_map,
    AddSubgroup.relIndex_map_map_of_injective _ _
      hinj]
  rw [relVol, AddSubgroup.relIndex_eq_one.2 hle] at h3
  lift a to ℕ using ha
  rw [zpow_neg, zpow_natCast, Nat.cast_one, one_div, inv_inj] at h3
  rw [Int.toNat_natCast]
  exact_mod_cast h3

end GlobalTheory.MatrixIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumAbsNormRpowNegLeDedekindZetaBound
section
open MeasureTheory NumberField Finset
open scoped ArithmeticFunction.zeta

namespace GlobalTheory.IdealZetaSum

theorem sum_Ioc_rpow_neg_le {s : ℝ} (hs : 1 < s) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) ≤ s / (s - 1) := by
  have hs1 : 0 < s - 1 := by linarith
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Ioc_self, sum_empty]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y _ hxy
    have : (1 : ℝ) ≤ x := by simpa using hx.1
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
  have h := AntitoneOn.sum_le_integral_Ico hN hanti
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le (by simpa using hN1)]; simp⟩)] at h
  have e : ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s)
      = 1 + ∑ i ∈ Ico 1 N, (((i + 1 : ℕ) : ℝ)) ^ (-s) := by
    rw [sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ (-s)) 1 N 1]
    have : Ioc 0 N = insert 1 (Ico (1 + 1) (N + 1)) := by
      ext n; simp only [mem_Ioc, mem_insert, mem_Ico]; omega
    rw [this, sum_insert (by simp)]
    simp
  rw [e]
  have hpos : 0 ≤ (N : ℝ) ^ (-s + 1) := by positivity
  have h2 : ((N : ℝ) ^ (-s + 1) - ((1 : ℕ) : ℝ) ^ (-s + 1)) / (-s + 1) ≤ 1 / (s - 1) := by
    rw [Nat.cast_one, Real.one_rpow, show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div]
    rw [show -s + 1 = -(s - 1) by ring] at hpos
    exact div_le_div_of_nonneg_right (by linarith) hs1.le
  have h3 : s / (s - 1) = 1 + 1 / (s - 1) := by field_simp; ring
  linarith

theorem sum_zeta_pow_mul_rpow_le (s : ℝ) (N k : ℕ) :
    ∑ n ∈ Ioc 0 N, (((ζ ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ) * (n : ℝ) ^ (-s)
      ≤ (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s)) ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ite_mul, one_mul, zero_mul, sum_ite_eq']
    split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s))]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right ih (sum_nonneg fun n _ => by positivity))
    rw [sum_mul_sum, ← sum_product', pow_succ]
    have e : ∀ n ∈ Ioc 0 N, (((ζ ^ k * ζ : ArithmeticFunction ℕ) n : ℕ) : ℝ) * (n : ℝ) ^ (-s)
        = ∑ x ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun x => x.1 * x.2 = n),
          (((ζ ^ k : ArithmeticFunction ℕ) x.1 : ℕ) : ℝ) * (x.1 : ℝ) ^ (-s) * (x.2 : ℝ) ^ (-s) := by
      intro n hn
      rw [mem_Ioc] at hn
      rw [ArithmeticFunction.mul_apply, Nat.cast_sum, sum_mul]
      refine sum_congr ?_ ?_
      · ext x
        simp only [Nat.mem_divisorsAntidiagonal, mem_filter, mem_product, mem_Ioc]
        constructor
        · rintro ⟨h, h0⟩
          have h1 : 0 < x.1 := Nat.pos_of_ne_zero (by rintro h1; rw [h1] at h; omega)
          have h2 : 0 < x.2 := Nat.pos_of_ne_zero (by rintro h1; rw [h1] at h; omega)
          refine ⟨⟨⟨h1, ?_⟩, h2, ?_⟩, h⟩ <;> nlinarith
        · rintro ⟨_, h⟩
          exact ⟨h, by omega⟩
      · intro x hx
        simp only [mem_filter, mem_product, mem_Ioc] at hx
        rw [← hx.2, Nat.cast_mul, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity),
          ArithmeticFunction.zeta_apply_ne hx.1.2.1.ne']
        simp [mul_assoc]
    rw [sum_congr rfl e, sum_fiberwise_eq_sum_filter]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ => by positivity

theorem sum_absNorm_rpow_neg_le : ∀ (K : Type) [Field K] [NumberField K] (s : ℝ), 1 < s →
    ∀ (S : Finset (Ideal (𝓞 K))), (∀ I ∈ S, I ≠ ⊥) →
      ∑ I ∈ S, (Ideal.absNorm I : ℝ) ^ (-s) ≤ (s / (s - 1)) ^ Module.finrank ℚ K := by
  intro K _ _ s hs S hS
  classical
  set N := S.sup (fun I => Ideal.absNorm I) with hN
  refine le_trans ?_ (pow_le_pow_left₀ (sum_nonneg fun n _ => by positivity)
    (sum_Ioc_rpow_neg_le hs N) _)
  refine le_trans ?_ (sum_zeta_pow_mul_rpow_le s N _)
  rw [← sum_fiberwise_of_maps_to (s := S) (t := Ioc 0 N) (g := fun I => Ideal.absNorm I)]
  · refine sum_le_sum fun n hn => ?_
    rw [sum_congr rfl (g := fun _ => (n : ℝ) ^ (-s))
      (fun I hI => by rw [(mem_filter.mp hI).2]), sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Nat.cast_le]
    refine le_trans ?_ (ncard_ideal_absNorm_eq_le K (mem_Ioc.mp hn).1.ne')
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun I hI => (mem_filter.mp (mem_coe.mp hI)).2)
      (Ideal.finite_setOfPred_absNorm_eq n)
  · intro I hI
    rw [mem_Ioc]
    exact ⟨Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hS I hI),
      le_sup (f := fun I => Ideal.absNorm I) hI⟩

end GlobalTheory.IdealZetaSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFramesCongrModThetaUnitriangular
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameChange

theorem coef_zero {ι M R : Type*} [CommRing R] [AddCommGroup M] [Module R M] {v : ι → M}
    (hv : LinearIndependent R v) {s : Set ι} {x : ι} (hx : x ∉ s) {c : R}
    (h : c • v x ∈ Submodule.span R (v '' s)) : c = 0 := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, e⟩ := h
  have h2 : Finsupp.single x c = l := hv (by rw [e, Finsupp.linearCombination_single])
  have h3 := congrArg (fun l : ι →₀ R => l x) h2
  simp only [Finsupp.single_eq_same] at h3
  rw [h3]
  exact (Finsupp.mem_supported' _ _).1 hl x hx

theorem diag_mul {m : ℕ} {R : Type*} [CommRing R] {P Q : Matrix (Fin m) (Fin m) R}
    (hP : P.BlockTriangular id) (hQ : Q.BlockTriangular id) (a : Fin m) :
    (P * Q) a a = P a a * Q a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hP h, zero_mul]
    · rw [hQ h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem sum_mem_spanTo (g g' : Fin (r + 1) → S.V) (hg' : ∀ a : Fin (r + 1), g' a ∈ S.spanTo g (a + 1))
    (c : Fin (r + 1) → E) (j : ℕ) (hc : ∀ a : Fin (r + 1), j ≤ (a : ℕ) → c a = 0) :
    ∑ a, c a • g' a ∈ S.spanTo g j :=
  Submodule.sum_mem _ fun a _ => by
    by_cases h : (a : ℕ) < j
    · exact Submodule.smul_mem _ _ (TermBasic.spanTo_mono S g (by omega) (hg' a))
    · rw [hc a (by omega), zero_smul]; exact Submodule.zero_mem _

theorem coeffs (g : Fin (r + 1) → S.V) (j : ℕ) (v : S.V)
    (hv : v ∈ Submodule.span L.O (g '' {i | (i : ℕ) < j})) :
    ∃ c : Fin (r + 1) → L.O, (∀ a : Fin (r + 1), j ≤ (a : ℕ) → c a = 0) ∧
      v = ∑ a, ((c a : L.O) : E) • g a := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  refine ⟨l, fun a ha => (Finsupp.mem_supported' _ _).1 hl a (by simp; omega), ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  rfl

end GlobalTheory.HL.FrameChange

namespace GlobalTheory.HL.FrameChange

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem tri_coeffs {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
    (hli : LinearIndependent E g) {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V}
    (t : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g j) ↔
      x ∈ Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}))
    (z : Fin (r + 1) → S.V) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hB0 : ∀ a b, b < a → B a b = 0) (hB1 : ∀ a, B a a = 1) (hz : ∀ b, z b = ∑ a, B a b • g a)
    (hzΛ : ∀ b, z b ∈ Λ) :
    ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) L.O, (∀ a b, b < a → C a b = 0) ∧ (∀ a, C a a = 1) ∧
      ∀ b, z b = ∑ a, ((C a b : L.O) : E) • n (g a) := by
  have hself : ∀ a : Fin (r + 1), g a ∈ S.spanTo g (a + 1) := fun a =>
    TermBasic.self_mem S g (by omega)
  have hmem : ∀ a : Fin (r + 1), n (g a) ∈ S.spanTo g (a + 1) := fun a =>
    TermBasic.map_mem hg hn _ (hself a)
  have key : ∀ b : Fin (r + 1), ∃ c : Fin (r + 1) → L.O, (∀ a : Fin (r + 1), (b : ℕ) + 1 ≤ (a : ℕ) → c a = 0) ∧
      z b = ∑ a, ((c a : L.O) : E) • n (g a) := fun b => by
    have h1 : z b ∈ S.spanTo g (b + 1) := by
      rw [hz b]
      exact sum_mem_spanTo S g g hself _ _ fun a ha => hB0 a b (Fin.lt_def.2 (by omega))
    exact coeffs S _ _ _ ((t _ (by omega) _).1 ⟨hzΛ b, h1⟩)
  choose c hc0 hc using key
  refine ⟨Matrix.of fun a b => c b a, fun a b h => hc0 b a (by rw [Fin.lt_def] at h; omega),
    fun b => ?_, fun b => hc b⟩
  show c b b = 1
  apply Subtype.ext
  have e1 : z b - g b ∈ S.spanTo g b := by
    have : z b - g b = ∑ a, (B a b - if a = b then 1 else 0) • g a := by
      rw [hz b]; simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [this]
    refine sum_mem_spanTo S g g hself _ _ fun a ha => ?_
    by_cases hab : a = b
    · subst hab; simp [hB1]
    · have : b < a := Fin.lt_def.2 (by have := Fin.val_ne_of_ne hab; omega)
      simp [hab, hB0 a b this]
  have e2 : z b - ((c b b : L.O) : E) • n (g b) ∈ S.spanTo g b := by
    have : z b - ((c b b : L.O) : E) • n (g b) =
        ∑ a, (((c b a : L.O) : E) - if a = b then ((c b b : L.O) : E) else 0) • n (g a) := by
      rw [hc b]; simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [this]
    refine sum_mem_spanTo S g _ hmem _ _ fun a ha => ?_
    by_cases hab : a = b
    · subst hab; simp
    · have := Fin.val_ne_of_ne hab
      simp [hab, hc0 b a (by omega)]
  have e3 : n (g b) - g b ∈ S.spanTo g b := TermBasic.sub_mem hg hn b
  have e4 : (((c b b : L.O) : E) - 1) • g b = (z b - g b) - (z b - ((c b b : L.O) : E) • n (g b)) -
      ((c b b : L.O) : E) • (n (g b) - g b) := by
    simp only [sub_smul, smul_sub, one_smul]; abel
  have h5 := (S.spanTo g b).sub_mem ((S.spanTo g b).sub_mem e1 e2) ((S.spanTo g b).smul_mem ((c b b : L.O) : E) e3)
  rw [← e4] at h5
  have h6 := coef_zero hli (s := {i | (i : ℕ) < b}) (x := b) (by simp) h5
  simpa [sub_eq_zero] using h6

end GlobalTheory.HL.FrameChange

namespace GlobalTheory.HL.FrameChange

theorem frames_congr : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : GlobalTheory.HL.Frames L r k) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (y x : Fin (r + 1) → S.V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a, B a a = 1) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = 1) → (∀ b, y b = ∑ a, B a b • S.f a) → (∀ b, x b = ∑ a, B' a b • S.f' a) → (∀ a, y a ∈ Λ) → (∀ b, x b ∈ Λ) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, S.InTh Λ (x b - ∑ a, ξ a b • y a) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT y x B B' hB0 hB1 hB'0 hB'1 hy hx hyΛ hxΛ
  obtain ⟨-, hW, -, t, t', hli, -, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hn, hn', -, -, hth, -⟩ := hW
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  have hl1 : LinearIndependent E (S.fr d Λ) := hli.comp Sum.inl Sum.inl_injective
  have hl2 : LinearIndependent E (S.fr' d Λ) := hli.comp Sum.inr Sum.inr_injective
  have hlf : LinearIndependent E S.f := by
    have := hl1.map' (S.wit d Λ).1.symm.toLinearMap (LinearEquiv.ker _)
    have e : S.f = ⇑((S.wit d Λ).1.symm.toLinearMap) ∘ S.fr d Λ := by
      funext a; simp [Frames.fr]
    rw [e]; exact this
  have hlf' : LinearIndependent E S.f' := by
    have := hl2.map' (S.wit d Λ).2.symm.toLinearMap (LinearEquiv.ker _)
    have e : S.f' = ⇑((S.wit d Λ).2.symm.toLinearMap) ∘ S.fr' d Λ := by
      funext a; simp [Frames.fr']
    rw [e]; exact this
  obtain ⟨C, hC0, hC1, hCy⟩ := tri_coeffs S hg hlf hn t y B hB0 hB1 hy hyΛ
  obtain ⟨C', hC'0, hC'1, hC'x⟩ := tri_coeffs S hg' hlf' hn' t' x B' hB'0 hB'1 hx hxΛ
  have hCt : C.BlockTriangular id := fun a b h => hC0 a b h
  have hC't : C'.BlockTriangular id := fun a b h => hC'0 a b h
  have hdet : C.det = 1 := by
    rw [Matrix.det_of_upperTriangular hCt]; simp [hC1]
  letI : Invertible C := Matrix.invertibleOfIsUnitDet C (by rw [hdet]; exact isUnit_one)
  have hCit : C⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hCt
  have hCi1 : ∀ a, C⁻¹ a a = 1 := fun a => by
    have h1 := diag_mul hCit hCt a
    rw [Matrix.inv_mul_of_invertible, hC1, mul_one] at h1
    simpa using h1.symm
  set D := C⁻¹ * C' with hD
  have hDt : D.BlockTriangular id := hCit.mul hC't
  have hCD : C * D = C' := by rw [hD, ← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
  choose w hwΛ hw using hth
  refine ⟨Matrix.of fun a b => ((D a b : L.O) : E), fun a b => (D a b).2, fun a b h => ?_, fun a => ?_,
    fun b => ?_⟩
  · simp [hDt h]
  · simp [hD, diag_mul hCit hC't, hCi1, hC'1]
  · have e1 : ∑ a, (Matrix.of fun a b => ((D a b : L.O) : E)) a b • y a =
        ∑ c, ((C' c b : L.O) : E) • (S.wit d Λ).1 (S.f c) := by
      simp only [Matrix.of_apply, hCy, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_smul, ← hCD, Matrix.mul_apply]
      push_cast
      simp only [mul_comm]
    refine ⟨∑ c, ((C' c b : L.O) : E) • w c, Λ.sum_mem fun c _ => Λ.smul_mem (C' c b) (hwΛ c), ?_⟩
    rw [e1, hC'x b, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← smul_sub, hw c, smul_comm]

end GlobalTheory.HL.FrameChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnessesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_invariants_independent_of_witnesses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ d Λ n n', S.IsTermW d Λ n n' → S.om d Λ = S.psi n * (S.psi' n')⁻¹ ∧ S.M d Λ = S.Mof (fun b => n (S.f b)) (fun b => n' (S.f' b)) ∧ S.Fr d Λ = S.frameCls (fun b => n (S.f b)) (fun b => n' (S.f' b)) ∧ (∀ y, S.lev (S.fr d Λ) (S.fr' d Λ) y = S.lev (fun b => n (S.f b)) (fun b => n' (S.f' b)) y) ∧ ‖S.om d Λ‖ = 1 := by
  first | exact @GlobalTheory.HL.WitIndep.witness_independence | exact GlobalTheory.HL.WitIndep.witness_independence | (intros; apply GlobalTheory.HL.WitIndep.witness_independence <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryConjugatorOfSplitIdempotentsStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_conjugator_of_split_idempotents : ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ a, σ (σ a) = a) → ∀ (m n : ℕ) (ι : Type) [Fintype ι] (ε : ι → R), (∀ j, ε j * ε j = ε j) → (∀ j, ε j * σ (ε j) = 0) → (∀ j k, j ≠ k → ε j * ε k = 0 ∧ ε j * σ (ε k) = 0) → ∀ (Z P : Matrix (Fin m) (Fin n) R) (Z' P' : Matrix (Fin n) (Fin m) R), Z * Z' = 1 → Z' * Z = 1 → P * P' = 1 → P' * P = 1 → ∃ c : GL (Fin n) R, (c : Matrix (Fin n) (Fin n) R) * ReciprocityTheory.Aut.conjT σ (c : Matrix (Fin n) (Fin n) R) = 1 ∧ ∀ j, ε j • (Z * (c : Matrix (Fin n) (Fin n) R)) = ε j • P ∧ ε j • (((c⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * Z') = ε j • P' := by
  first | exact @GlobalTheory.unitary_conjugator_of_split_idempotents | exact GlobalTheory.unitary_conjugator_of_split_idempotents | (intros; apply GlobalTheory.unitary_conjugator_of_split_idempotents <;> assumption)
end

