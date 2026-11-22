import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0010

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodREp
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem memO_iff {K : Type} [Field K] [ValuativeRel K] (x : K) : x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := by
  rw [Valuation.mem_integer_iff, Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K), map_one]

theorem iotaF_mem_cof (D : Formalism.BasicNotions.D7) (x : D.host.F) :
    ∀ᶠ p in Filter.cofinite, (D.s.atP p).ιF x ∈ 𝒪[(D.s.atP p).Fp] := by
  have hfin := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 D.host.F) x
  refine hfin.eventually_cofinite_notMem.mono fun p hp => ?_
  rw [memO_iff, ← map_one (D.s.atP p).ιF, (D.s.atP p).val, map_one]
  exact not_lt.mp hp

theorem vec_mem_of {K : Type} [Field K] (R : Subring K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (hM : ∀ i j, M i j ∈ R) (hd : M.det ≠ 0) (hdi : (M.det)⁻¹ ∈ R) (c : ι → K)
    (hc : ∀ j, Matrix.vecMul c M j ∈ R) : ∀ i, c i ∈ R := by
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd)
  have hc' : c = Matrix.vecMul (Matrix.vecMul c M) M⁻¹ := by
    rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  have hMinv : ∀ i j, M⁻¹ i j ∈ R := by
    intro i j
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    refine R.mul_mem ?_ ?_
    · simpa [Ring.inverse_eq_inv'] using hdi
    · rw [Matrix.adjugate_apply, Matrix.det_apply]
      refine R.sum_mem fun σ _ => ?_
      refine R.zsmul_mem (R.prod_mem fun k _ => ?_) _
      rw [Matrix.updateRow_apply]
      split_ifs
      · rw [Pi.single_apply]
        split_ifs
        · exact R.one_mem
        · exact R.zero_mem
      · exact hM _ _
  intro i
  rw [hc', Matrix.vecMul, dotProduct]
  exact R.sum_mem fun j _ => R.mul_mem (hc j) (hMinv j i)

theorem iotaE_mem_of_int (D : Formalism.BasicNotions.D7) (p : PlF D) {w : D.host.E} (hw : IsIntegral ℤ w) :
    (D.s.atP p).ιE w ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  exact (hw.map (D.s.atP p).ιE.toIntAlgHom).tower_top

theorem alg_mem_O (D : Formalism.BasicNotions.D7) (p : PlF D) {c : (D.s.atP p).Fp} (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  exact isIntegral_algebraMap (R := 𝒪[(D.s.atP p).Fp]) (x := ⟨c, hc⟩)

theorem exists_theta (D : Formalism.BasicNotions.D7) :
    ∃ θ : D.host.E, IsIntegral ℤ θ ∧ θ ∉ (algebraMap D.host.F D.host.E).range := by
  haveI := D.host.isCMField_hostE
  obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hc : (NumberField.InfinitePlace.mk φ).IsComplex := NumberField.IsTotallyComplex.isComplex _
  have hnr : ¬ NumberField.ComplexEmbedding.IsReal φ := by
    rwa [← NumberField.InfinitePlace.isReal_mk_iff, NumberField.InfinitePlace.not_isReal_iff_isComplex]
  obtain ⟨x, hx⟩ : ∃ x, star (φ x) ≠ φ x := by
    by_contra h
    push_neg at h
    exact hnr (RingHom.ext h)
  have hxF : x ∉ (algebraMap D.host.F D.host.E).range := by
    rintro ⟨f, rfl⟩
    exact hx ((NumberField.mem_maximalRealSubfield_iff _).1 f.2 φ)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  by_cases ha : algebraMap (𝓞 D.host.E) D.host.E a ∈ (algebraMap D.host.F D.host.E).range
  · refine ⟨algebraMap (𝓞 D.host.E) D.host.E b, NumberField.RingOfIntegers.isIntegral_coe b, fun hbF => hxF ?_⟩
    obtain ⟨f1, hf1⟩ := ha
    obtain ⟨f2, hf2⟩ := hbF
    exact ⟨f1 / f2, by rw [map_div₀, hf1, hf2]⟩
  · exact ⟨algebraMap (𝓞 D.host.E) D.host.E a, NumberField.RingOfIntegers.isIntegral_coe a, ha⟩

theorem epsilonDual_almost_all : EpDualCof := by
  intro D
  haveI := D.host.isCMField_hostE
  have h2 : Module.finrank D.host.F D.host.E = 2 :=
    (NumberField.IsCMField.isQuadraticExtension D.host.E).finrank_eq_two
  haveI : FiniteDimensional D.host.F D.host.E := Module.finite_of_finrank_eq_succ h2
  obtain ⟨θ, hθ, hθF⟩ := exists_theta D
  have hli : LinearIndependent D.host.F ![(1 : D.host.E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hθF
      refine ⟨-s / t, ?_⟩
      have hta : algebraMap D.host.F D.host.E t ≠ 0 := (map_ne_zero _).mpr ht
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      rw [map_div₀, map_neg, div_eq_iff hta]
      linear_combination -hst
    subst ht
    simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
    exact ⟨hst, rfl⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, h2])
  have hb : ∀ i, b i = ![(1 : D.host.E), θ] i := fun i => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hbint : ∀ i, IsIntegral ℤ (b i) := by
    intro i
    rw [hb]
    fin_cases i
    · exact isIntegral_one
    · exact hθ
  have hdisc : (Algebra.traceMatrix D.host.F b).det ≠ 0 := Algebra.discr_not_zero_of_basis D.host.F b
  have hev : ∀ᶠ p in Filter.cofinite,
      (∀ i j, (D.s.atP p).ιF (Algebra.traceMatrix D.host.F b i j) ∈ 𝒪[(D.s.atP p).Fp]) ∧
        (D.s.atP p).ιF ((Algebra.traceMatrix D.host.F b).det)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by
    have h1 : ∀ᶠ p in Filter.cofinite,
        ∀ i j, (D.s.atP p).ιF (Algebra.traceMatrix D.host.F b i j) ∈ 𝒪[(D.s.atP p).Fp] := by
      simp only [Filter.eventually_all]
      exact fun i j => iotaF_mem_cof D _
    exact h1.and (iotaF_mem_cof D _)
  refine hev.mono fun p hp z hz => ?_
  obtain ⟨hT, hTd⟩ := hp
  have hbL : ∀ i, PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 i = (D.s.atP p).ιE (b i) := fun i =>
    PI.ProdFormulaE.Base.basisE_apply (D.s.atP p) b h2 i
  have hM : ∀ i j, Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep
      (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 i * PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 j) =
      (D.s.atP p).ιF (Algebra.traceMatrix D.host.F b i j) := by
    intro i j
    rw [hbL, hbL, ← map_mul, PI.ProdFormulaE.Base.trace_ιE (D.s.atP p) h2, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply]
  have hdet : ((Algebra.traceMatrix D.host.F b).map (D.s.atP p).ιF).det =
      (D.s.atP p).ιF (Algebra.traceMatrix D.host.F b).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hc := vec_mem_of 𝒪[(D.s.atP p).Fp] ((Algebra.traceMatrix D.host.F b).map (D.s.atP p).ιF)
    (fun i j => hT i j) (by rw [hdet]; exact (map_ne_zero _).mpr hdisc)
    (by rw [hdet, ← map_inv₀]; exact hTd)
    (fun i => (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2).repr z i) (fun j => by
      have hsum : Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep
          (z * PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 j) =
          ∑ i, (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2).repr z i *
            Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep
              (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 i * PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 j) := by
        conv_lhs => rw [← (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2).sum_repr z]
        rw [Finset.sum_mul, map_sum]
        simp only [smul_mul_assoc, map_smul, smul_eq_mul]
      have hmem := hz (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 j)
        (by rw [hbL]; exact iotaE_mem_of_int D p (hbint j))
      rw [hsum] at hmem
      simp only [hM] at hmem
      simpa [Matrix.vecMul, dotProduct, Matrix.map_apply] using hmem)
  rw [← (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2).sum_repr z]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (alg_mem_O D p (hc i)) (by rw [hbL]; exact iotaE_mem_of_int D p (hbint i))

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramIff
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

section Coord2

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

theorem gram_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F)
    (hes : ∀ x, e (M.L.cj x) = (e x).swap)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F)) (Ph : Matrix (Fin n) (Fin n) 𝒪[F])
    (hπ : IsSplitCoord e H Λ π Ph) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E)
    (h1 : ∀ a b, G₀ a b ∈ M.L.O) (h2 : ∀ a b, G₀ b a = M.L.cj (G₀ a b)) (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    (∀ a b, H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}) ↔
      ∀ a b, resF F (∑ k, ∑ l, (π (v b)).1 k * (Ph k l : F) * (π (v a)).2 l) = resF F ((e (G₀ a b)).1) := by
  have hform := hπ.2.2.2
  have hL := fun a => (hπ.2.1 (v a)).1 (hv a)
  have hc : ∀ a b, InP ϖ (e (H.h (v b) (v a) - G₀ a b)).1 ↔
      resF F (∑ k, ∑ l, (π (v b)).1 k * (Ph k l : F) * (π (v a)).2 l) = resF F ((e (G₀ a b)).1) := by
    intro a b
    rw [map_sub, Prod.fst_sub, hform]
    exact inP_sub_iff hϖ (bil_mem _ _ (hL b).1 (hL a).2 Ph) ((hO _).1 (h1 a b)).1
  have hc2 : ∀ a b, (e (H.h (v b) (v a) - G₀ a b)).2 = (e (H.h (v a) (v b) - G₀ b a)).1 := by
    intro a b
    have hg : e (G₀ a b) = (e (G₀ b a)).swap := by rw [h2 b a, hes]
    rw [map_sub, map_sub, Prod.snd_sub, Prod.fst_sub, hform, hform, hg]
    rfl
  constructor
  · intro h a b
    exact (hc a b).1 ((mem_span_irr_iff e hO ϖ _).1 (h a b)).1
  · intro h a b
    rw [mem_span_irr_iff e hO ϖ]
    exact ⟨(hc a b).2 (h a b), by rw [hc2]; exact (hc b a).2 (h b a)⟩

theorem pi_sum (e : E ≃ₐ[F] F × F) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) :
    π (∑ i, c i • v i) = (∑ i, (e (c i)).1 • (π (v i)).1, ∑ i, (e (c i)).2 • (π (v i)).2) := by
  rw [map_sum]
  simp only [hπa]
  exact Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])

theorem prim_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    H.Prim Λ v ↔ LinearIndependent 𝓀[F] (redM F fun a => (π (v a)).1) ∧
      LinearIndependent 𝓀[F] (redM F fun a => (π (v a)).2) := by
  set X : ι → Fin n → F := fun a => (π (v a)).1 with hXd
  set Y : ι → Fin n → F := fun a => (π (v a)).2 with hYd
  have hX : ∀ a k, X a k ∈ 𝒪[F] := fun a k => ((hπL (v a)).1 (hv a)).1 k
  have hY : ∀ a k, Y a k ∈ 𝒪[F] := fun a k => ((hπL (v a)).1 (hv a)).2 k
  have hsum := pi_sum e π hπa v
  have hpiS : ∀ u w : Fin n → F, π (π.symm (u, w)) = (u, w) := fun u w => AddEquiv.apply_symm_apply _ _

  have hLI : LinearIndependent E v ↔ LinearIndependent F X ∧ LinearIndependent F Y := by
    constructor
    · intro hind
      constructor
      · rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h0 := Fintype.linearIndependent_iff.1 hind (fun i => e.symm (c i, 0)) (by
          apply π.injective
          rw [hsum, map_zero]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          ext k
          · simpa [hXd] using congrFun hc k
          · simp) i
        have := congrArg (fun z => (e z).1) h0
        simpa using this
      · rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h0 := Fintype.linearIndependent_iff.1 hind (fun i => e.symm (0, c i)) (by
          apply π.injective
          rw [hsum, map_zero]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          ext k
          · simp
          · simpa [hYd] using congrFun hc k) i
        have := congrArg (fun z => (e z).2) h0
        simpa using this
    · rintro ⟨hXi, hYi⟩
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h0 := congrArg π hc
      rw [hsum, map_zero] at h0
      have a1 := Fintype.linearIndependent_iff.1 hXi (fun i => (e (c i)).1) (congrArg Prod.fst h0) i
      have a2 := Fintype.linearIndependent_iff.1 hYi (fun i => (e (c i)).2) (congrArg Prod.snd h0) i
      apply e.injective
      rw [map_zero]
      exact Prod.ext a1 a2

  have hSat : (∀ x ∈ Λ, x ∈ Submodule.span E (Set.range v) → x ∈ Submodule.span M.L.O (Set.range v)) ↔
      SatF F X ∧ SatF F Y := by
    have hOsum : ∀ d : ι → M.L.O, ∑ i, d i • v i = ∑ i, (d i : E) • v i := fun d => rfl
    constructor
    · intro hs
      constructor
      · rintro u hu ⟨c, hc⟩
        have hxL : π.symm (u, 0) ∈ Λ := (hπL _).2 (by rw [hpiS]; exact ⟨hu, fun k => Subring.zero_mem _⟩)
        have hxs : π.symm (u, 0) ∈ Submodule.span E (Set.range v) := by
          rw [Submodule.mem_span_range_iff_exists_fun]
          refine ⟨fun i => e.symm (c i, 0), ?_⟩
          apply π.injective
          rw [hsum, hpiS]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          rw [← hc]
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hs _ hxL hxs)
        refine ⟨fun i => (e (d i)).1, fun i => ((hO _).1 (d i).2).1, ?_⟩
        have h0 := congrArg (fun z => (π z).1) hd
        simp only [hOsum, hsum, hpiS] at h0
        exact h0
      · rintro u hu ⟨c, hc⟩
        have hxL : π.symm (0, u) ∈ Λ := (hπL _).2 (by rw [hpiS]; exact ⟨fun k => Subring.zero_mem _, hu⟩)
        have hxs : π.symm (0, u) ∈ Submodule.span E (Set.range v) := by
          rw [Submodule.mem_span_range_iff_exists_fun]
          refine ⟨fun i => e.symm (0, c i), ?_⟩
          apply π.injective
          rw [hsum, hpiS]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          rw [← hc]
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hs _ hxL hxs)
        refine ⟨fun i => (e (d i)).2, fun i => ((hO _).1 (d i).2).2, ?_⟩
        have h0 := congrArg (fun z => (π z).2) hd
        simp only [hOsum, hsum, hpiS] at h0
        exact h0
    · rintro ⟨sX, sY⟩ x hx hxs
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
      have hπx := hsum c
      rw [hc] at hπx
      have hxc := (hπL x).1 hx
      obtain ⟨c1, hc1, hs1⟩ := sX (π x).1 hxc.1 ⟨_, (congrArg Prod.fst hπx).symm⟩
      obtain ⟨c2, hc2, hs2⟩ := sY (π x).2 hxc.2 ⟨_, (congrArg Prod.snd hπx).symm⟩
      have hmem : ∀ i, e.symm (c1 i, c2 i) ∈ M.L.O := fun i => by
        rw [hO, AlgEquiv.apply_symm_apply]; exact ⟨hc1 i, hc2 i⟩
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => ⟨_, hmem i⟩, ?_⟩
      rw [hOsum]
      apply π.injective
      rw [hsum]
      simp only [AlgEquiv.apply_symm_apply]
      exact Prod.ext hs1 hs2
  have hP : H.Prim Λ v ↔ (LinearIndependent F X ∧ LinearIndependent F Y) ∧ (SatF F X ∧ SatF F Y) := by
    unfold Loc.HermSp.Prim
    rw [← hLI, ← hSat]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hv, h.1, h.2⟩⟩
  rw [hP, ← dvr_prim_iff hϖ X hX, ← dvr_prim_iff hϖ Y hY]
  tauto

end Coord2

end PI.UnitaryGroupMassFormula.CntFormula
end
end

