import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIwahoriContractionHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0542
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0857
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0865
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0864
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0867

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceExists
section
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitLevel

theorem exists_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G)
    (hc : IsCompact (K : Set G)) (ho : IsOpen (K' : Set G)) :
    ∃ X : Finset G, (∀ x ∈ X, x ∈ K) ∧ ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K' := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  have hop : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact ho.preimage continuous_subtype_val
  haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hop
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  refine ⟨Finset.univ.image fun q : K ⧸ K'.subgroupOf K => ((q.out : K) : G), ?_, ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact q.out.2
  · intro k hk
    let q₀ : K ⧸ K'.subgroupOf K := QuotientGroup.mk ⟨k, hk⟩
    refine ⟨((q₀.out : K) : G), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have h : (q₀.out)⁻¹ * ⟨k, hk⟩ ∈ K'.subgroupOf K := QuotientGroup.eq.1 (QuotientGroup.out_eq' q₀)
      exact Subgroup.mem_subgroupOf.1 h
    · rintro x ⟨hx, hxk⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
      have h : q = q₀ := by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)
      rw [h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_conj (w : Pl E) (n m : ℕ) : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ GlobalTheory.PrincCong.congSub w n m,
    k * k' * k⁻¹ ∈ GlobalTheory.PrincCong.congSub w n m := by
  rintro _ ⟨h, rfl⟩ _ ⟨h', hh', rfl⟩
  refine ⟨h * h' * h⁻¹, ?_, by simp⟩
  exact Subgroup.Normal.conj_mem inferInstance h' hh' h

def lev (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (m b : ℕ) : Subgroup (GLw b w) :=
  GlobalTheory.PrincCong.congSub w b m ⊓ μ.ker.comap GeneralLinearGroup.det

theorem continuous_det (w : Pl E) (b : ℕ) :
    Continuous (GeneralLinearGroup.det : GLw b w → (w.adicCompletion E)ˣ) :=
  Units.continuous_iff.2 ⟨Continuous.matrix_det Units.continuous_val,
    Continuous.matrix_det (Units.continuous_val.comp continuous_inv)⟩

theorem isLevel_lev (w : Pl E) (hw : IsSplitAt w) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : IsOpen (μ.ker : Set (w.adicCompletion E)ˣ)) (m b : ℕ) :
    GlobalTheory.BCT.IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) (lev w μ m b) := by
  refine ⟨?_, fun g hg => ((GlobalTheory.PrincCong.mem_congSub_iff w b m g).1 hg.1).1, fun k hk => ?_⟩
  · exact (GlobalTheory.PrincCong.isOpen_congSub w b m).inter (hμ.preimage (continuous_det w b))
  · have ht : thL b w = MonoidHom.id _ := by unfold thL; rw [if_pos hw]
    rw [ht]
    exact hk

theorem blk_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : ℕ) (y : GLw a w × GLw b w)
    (h1 : y.1 ∈ GlobalTheory.PrincCong.congSub w a m) (h2 : y.2 ∈ GlobalTheory.PrincCong.congSub w b m) :
    blk h w y 0 ∈ GlobalTheory.PrincCong.congSub w n m := by
  rw [GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blk_zero_eq, GlobalTheory.PrincCong.mem_congSub_iff]
  obtain ⟨k1, e1⟩ := (GlobalTheory.PrincCong.mem_congSub_iff w a m _).1 h1
  obtain ⟨k2, e2⟩ := (GlobalTheory.PrincCong.mem_congSub_iff w b m _).1 h2
  have hI1 := GlobalTheory.AdelicU.mem_GLint_iff.1 k1
  have hI2 := GlobalTheory.AdelicU.mem_GLint_iff.1 k2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [CtLevel.dgM_val]
    exact CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ hI1.1 hI2.1 i j
  · rw [← map_inv, CtLevel.dgM_val]
    exact CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ hI1.2 hI2.2 i j
  · obtain ⟨i', rfl⟩ := (CtLevel.blkEq h).surjective i
    obtain ⟨j', rfl⟩ := (CtLevel.blkEq h).surjective j
    have hone : ∀ p q, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (CtLevel.blkEq h p) (CtLevel.blkEq h q) =
        (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (w.adicCompletion E)) p q := by
      intro p q
      simp [Matrix.one_apply, (CtLevel.blkEq h).injective.eq_iff]
    rw [hone]
    rcases i' with i' | i' <;> rcases j' with j' | j'
    · rw [(GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.dgM_entries h w y).1]
      simpa [Matrix.one_apply] using e1 i' j'
    · rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
      simp
    · rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
      simp
    · rw [(GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.dgM_entries h w y).2]
      simpa [Matrix.one_apply] using e2 i' j'

theorem splitEx : SplitEx := by
  intro E _ _ _ n w hw μ hμ m hm KB hKB
  have hKc := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2
  have ho := GlobalTheory.PrincCong.isOpen_congSub w n m
  have hle : GlobalTheory.PrincCong.congSub w n m ≤ GlobalTheory.LFun.KGL w n :=
    fun g hg => ((GlobalTheory.PrincCong.mem_congSub_iff w n m g).1 hg).1
  have hcl : IsClosed (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) := Subgroup.isClosed_of_isOpen _ ho
  have hc : IsCompact (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) := hKc.of_isClosed_subset hcl hle
  obtain ⟨X, hX, hXu⟩ := exists_reps (GlobalTheory.LFun.KGL w n) (GlobalTheory.PrincCong.congSub w n m) hKc ho
  refine ⟨GlobalTheory.PrincCong.congSub w n m, X, (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)).indicator 1,
    fun a => (lev w μ m a).prod (lev w μ m (n - a)), ?_, ho, hle, congSub_conj w n m, hX, hXu, ?_, ?_⟩
  · ext k
    rw [Subgroup.mem_subgroupOf, GlobalTheory.PrincCong.mem_congSub_iff, hKB k]
    exact Iff.rfl
  · refine ⟨ho, hc, ?_, fun k₁ hk₁ k₂ hk₂ g => ?_⟩
    · refine HasCompactSupport.of_support_subset_isCompact hc ?_
      intro g hg
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    · have hiff : k₁ * g * k₂ ∈ GlobalTheory.PrincCong.congSub w n m ↔ g ∈ GlobalTheory.PrincCong.congSub w n m := by
        rw [Subgroup.mul_mem_cancel_right _ hk₂, Subgroup.mul_mem_cancel_left _ hk₁]
      by_cases hg : g ∈ GlobalTheory.PrincCong.congSub w n m
      · rw [Set.indicator_of_mem (show _ ∈ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hiff.2 hg),
          Set.indicator_of_mem (show _ ∈ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hg)]
        rfl
      · rw [Set.indicator_of_notMem (show _ ∉ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from fun h => hg (hiff.1 h)),
          Set.indicator_of_notMem (show _ ∉ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hg)]
  · intro a ha
    refine ⟨⟨_, _, rfl, isLevel_lev w hw μ hμ m a, isLevel_lev w hw μ hμ m (n - a)⟩, fun y hy => ⟨?_, ?_⟩⟩
    · exact blk_mem (Nat.add_sub_of_le ha) w m y hy.1.1 hy.2.1
    · have d1 : μ (GeneralLinearGroup.det y.1) = 1 := hy.1.2
      have d2 : μ (GeneralLinearGroup.det y.2) = 1 := hy.2.2
      rw [map_mul, map_pow, map_pow, d1, d2, one_pow, one_pow, one_mul]

end GlobalTheory.CompanionTheory.SplitLevel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExists
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

namespace GlobalTheory.CompanionTheory.UnifFix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conj_real (x : maximalRealSubfield E) :
    IsCMField.complexConj E (algebraMap (maximalRealSubfield E) E x) = algebraMap (maximalRealSubfield E) E x := by
  exact (IsCMField.complexConj E).commutes x

theorem cj_real (w : Pl E) (x : maximalRealSubfield E) :
    GlobalTheory.BCT.cj w (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E x)) =
      algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E x) := by
  unfold GlobalTheory.BCT.cj
  split_ifs with h
  · rw [h.choose_spec.2, conj_real]
  · rfl

theorem valuation_up (hU : GlobalTheory.BCT.Unr E) (w : Pl E) (x : maximalRealSubfield E) :
    w.valuation E (algebraMap (maximalRealSubfield E) E x) =
      (w.under (𝓞 (maximalRealSubfield E))).valuation (maximalRealSubfield E) x := by
  have := hU w
  have h1 := HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 (maximalRealSubfield E))) w x
  have he : (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx]
    · exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    · exact (w.under _).ne_bot
  rw [← h1, he, pow_one]

theorem neg_toAdd_unzero (a : WithZero (Multiplicative ℤ)) (h : a ≠ 0) (ha : a = WithZero.exp (-1 : ℤ)) :
    -Multiplicative.toAdd (WithZero.unzero h) = 1 := by
  subst ha
  rfl

theorem unifEx : UnifEx := by
  intro E _ _ _ hU w
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (maximalRealSubfield E)
    (w.under (𝓞 (maximalRealSubfield E)))
  have hy : w.valuation E (algebraMap (maximalRealSubfield E) E π) = WithZero.exp (-1) := by
    rw [valuation_up hU w π, hπ]
  have hy0 : algebraMap (maximalRealSubfield E) E π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact WithZero.zero_ne_coe hy
  have hne : algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π) ≠ 0 :=
    (map_ne_zero _).2 hy0
  have hv : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) =
      WithZero.exp (-1) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion (𝓞 E) E w, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hy]
  have hv0 : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) ≠ 0 := by
    rw [hv]
    exact WithZero.coe_ne_zero
  refine ⟨Units.mk0 _ hne, ⟨?_, ?_⟩, ?_⟩
  · show Formalism.UG.ordL (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) = 1
    unfold Formalism.UG.ordL
    rw [dif_neg hv0]
    exact neg_toAdd_unzero _ hv0 hv
  · exact cj_real w π
  · exact hv

end GlobalTheory.CompanionTheory.UnifFix
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VLtOneOfOrdLEqOne
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.IwahoriContraction

open PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_iwGL_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ iwGL n w ↔ g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) (w.adicCompletion E) := by
  rw [(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1]
  show _ ↔ g ∈ PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (w.adicCompletion E) ∧ _
  rw [GlobalTheory.CompanionTheory.TfLoc.Iw.mem_unitGL_iff, and_assoc]
  simp only [GlobalTheory.CompanionTheory.IwEntries.rel_le_one_iff, GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff]

omit [IsCMField E] in

theorem v_le_of_ordL_eq_one (w : Pl E) {ϖ x : w.adicCompletion E} (h0 : ϖ ≠ 0) (h1 : ordL ϖ = 1)
    (hx : Valued.v x < 1) : Valued.v x ≤ Valued.v ϖ := by
  have h0' : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h0'
  have hu1 : Multiplicative.toAdd u = -1 := by
    have := GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_of_eq hu.symm
    omega
  by_cases hx0 : Valued.v x = 0
  · rw [hx0]
    exact zero_le
  obtain ⟨c, hc⟩ := WithZero.ne_zero_iff_exists.1 hx0
  rw [← hu, ← hc]
  rw [← hc] at hx
  have hc1 : c < 1 := by exact_mod_cast hx
  have hc2 : Multiplicative.toAdd c < 0 := hc1
  have : c ≤ u := by
    show Multiplicative.toAdd c ≤ Multiplicative.toAdd u
    omega
  exact_mod_cast this

omit [IsCMField E] in

theorem v_lt_one_of_ordL_eq_one (w : Pl E) {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (h1 : ordL ϖ = 1) :
    Valued.v ϖ < 1 := by
  have h0' : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h0'
  have hu1 : Multiplicative.toAdd u = -1 := by
    have := GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_of_eq hu.symm
    omega
  rw [← hu]
  have : u < 1 := by
    show Multiplicative.toAdd u < 0
    omega
  exact_mod_cast this

omit [IsCMField E] in

theorem torusO_subset_TO (w : Pl E) (n : ℕ) (t : GLw n w)
    (ht : t ∈ PositivityTheory.Rg.Tf.Loc.torusO (n := n) (w.adicCompletion E)) : t ∈ TO n w := by
  obtain ⟨hu, hd⟩ := ht
  obtain ⟨h1, h2⟩ := (GlobalTheory.CompanionTheory.TfLoc.Iw.mem_unitGL_iff t).1 hu
  refine ⟨hd, fun i => ?_⟩
  have hmul : ((t⁻¹ : GLw n w).val * t.val) i i = 1 := by
    have : (t⁻¹ : GLw n w).val * t.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun j _ hj => by rw [hd j i hj, mul_zero])
    (fun h => absurd (Finset.mem_univ i) h)] at hmul
  have ha := (GlobalTheory.CompanionTheory.IwEntries.rel_le_one_iff w _).1 (h1 i i)
  have hb := (GlobalTheory.CompanionTheory.IwEntries.rel_le_one_iff w _).1 (h2 i i)
  have hv : Valued.v ((t⁻¹ : GLw n w).val i i) * Valued.v (t.val i i) = 1 := by
    rw [← map_mul, hmul, map_one]
  refine le_antisymm ha ?_
  calc (1 : _) = Valued.v ((t⁻¹ : GLw n w).val i i) * Valued.v (t.val i i) := hv.symm
    _ ≤ 1 * Valued.v (t.val i i) := mul_le_mul' hb le_rfl
    _ = _ := one_mul _

theorem contr_id : PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw.P_contr_id := by
  intro E _ _ _ w ϖ hϖ n y hy δ hδ
  have hδ' : ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, δ = x * tdiag ϖ y * z := by
    by_contra h
    exact hδ (if_neg h)
  obtain ⟨a, ha, b, hb, hab⟩ := hδ'
  obtain ⟨⟨U, hU⟩, -, hcpt, -⟩ := GlobalTheory.CompanionTheory.TfLoc.Iw.iwahori_compact_open_galois.1 (w.adicCompletion E) n
  have hcomp : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hequiv := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v
  have hϖ0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  have hmap : ∀ g : GL (Fin n) (w.adicCompletion E),
      Matrix.GeneralLinearGroup.map ((RingEquiv.refl (w.adicCompletion E) : _ ≃+* _) : _ →+* _) g = g := by
    intro g
    apply Units.ext
    ext i j
    rfl
  have hρ1 : ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1 :=
    (GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).2 (v_lt_one_of_ordL_eq_one w hϖ0 hϖ.1)
  have hunif : ∀ x : w.adicCompletion E, ValuativeRel.valuation (w.adicCompletion E) x < 1 →
      ValuativeRel.valuation (w.adicCompletion E) x ≤
        ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) := fun x hx =>
    (hequiv.le_iff_le).2 (v_le_of_ordL_eq_one w hϖ0 hϖ.1 ((GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).1 hx))
  let e : Fin n → w.adicCompletion E := fun i => ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  have he : ∀ i, e i ≠ 0 := fun i => Units.ne_zero _
  have hc : ∀ i l, i < l → ValuativeRel.valuation (w.adicCompletion E) (e i) ≤
      ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) *
        ValuativeRel.valuation (w.adicCompletion E) (e l) := fun i l h => by
    obtain ⟨c, hcn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ y i - y l - 1 by have := hy h; omega)
    have hyi : y i = y l + ((c + 1 : ℕ) : ℤ) := by push_cast; omega
    have hei : e i = e l * (ϖ : w.adicCompletion E) ^ (c + 1) := by
      show ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = ((ϖ ^ y l : (w.adicCompletion E)ˣ) : w.adicCompletion E) * _
      rw [hyi, _root_.zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hei, map_mul, map_pow, mul_comm]
    refine mul_le_mul' ?_ le_rfl
    calc ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ (c + 1)
        ≤ ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ 1 :=
          pow_le_pow_right_of_le_one' hρ1.le (Nat.succ_le_succ (Nat.zero_le c))
      _ = _ := pow_one _
  have hx : ((tdiag ϖ y : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal e := by
    rw [tdiag, GlobalTheory.SmGL.val_diagT]
  have hδI : δ ∈ PositivityTheory.Rg.Tf.Loc.iwDouble (w.adicCompletion E) (tdiag ϖ y : GLw n w) :=
    ⟨a, (mem_iwGL_iff w n a).1 ha, b, (mem_iwGL_iff w n b).1 hb, hab⟩
  obtain ⟨m, hm, t, ht, h⟩ := GlobalTheory.CompanionTheory.TwContraction.contraction U hU hcpt (RingEquiv.refl _)
    (fun _ => rfl) (fun g hg => by rw [hmap]; exact hg) _ hρ1 hunif e he hc _ hx δ hδI
  rw [hmap] at h
  exact ⟨m, (mem_iwGL_iff w n m).2 hm, t, torusO_subset_TO w n t ht, h⟩

end GlobalTheory.CompanionTheory.IwahoriContraction
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VbOfEquiv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.PerfVB

theorem vb_of_equiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) {g : ℕ} (h : VB R M g) : VB R N g := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Module.Finite.equiv E, Module.Projective.of_equiv E, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E]
  exact h3 p

theorem vb_pure {R P₀ P₁ P₂ : Type} [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁]
    [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] [Module.Finite R P₀]
    [Module.Projective R P₀] [Module.Finite R P₁] [Module.Projective R P₁] [Module.Finite R P₂]
    [Module.Projective R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (hc : a₁ ∘ₗ a₀ = 0) (g : ℕ)
    (e : P₀) (he : a₀ e = 0)
    (hE : ∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 →
      ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e))
    (hG : ∀ (k : Type) [Field k] [Algebra R k],
      Module.finrank k (Hc (a₀.baseChange k) (a₁.baseChange k)) = g)
    (hL : SmallLift a₀ a₁) : VB R (Hc (a₀.baseChange R) (a₁.baseChange R)) g := by
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_generalized_inverse_of_unit_kernel R P₀ P₁ a₀ e he hE
  obtain ⟨s, hs⟩ := GlobalTheory.T.local_splitting_global_generalized_inverse R P₁ P₂ a₁ (fun m _ => by
    haveI : Module.Free (Localization.AtPrime m) (TensorProduct R (Localization.AtPrime m) P₁) :=
      Module.free_of_flat_of_isLocalRing
    haveI : Module.Free (Localization.AtPrime m) (TensorProduct R (Localization.AtPrime m) P₂) :=
      Module.free_of_flat_of_isLocalRing
    exact GlobalTheory.T.generalized_inverse_of_lift_local _ _ _ _ (GlobalTheory.T.small_lift_base_change_local R P₀ P₁ P₂ _ a₀ a₁ hc hL))
  obtain ⟨j, π, h, h', hπj, haj, hπa, hsum⟩ := GlobalTheory.T.split_complex_homotopy_data R P₀ P₁ P₂ a₀ a₁ t s hc ht hs
  have hP := Module.Projective.of_split j π hπj
  have hsurj : Function.Surjective π := fun x => ⟨j x, by simpa using LinearMap.congr_fun hπj x⟩
  have hF := Module.Finite.of_surjective π hsurj
  obtain ⟨eR⟩ := GlobalTheory.T.homotopy_data_cohomology_base_change R P₀ P₁ P₂ _ R a₀ a₁ j π h h' hc hπj haj hπa hsum
  refine vb_of_equiv (eR.trans (TensorProduct.lid R _)).symm ⟨hF, hP, GlobalTheory.T.constant_fibre_rank_stalk_rank R _ g ?_⟩
  intro k _ _
  obtain ⟨ek⟩ := GlobalTheory.T.homotopy_data_cohomology_base_change R P₀ P₁ P₂ _ k a₀ a₁ j π h h' hc hπj haj hπa hsum
  rw [← ek.finrank_eq]
  exact hG k

theorem small_lift {R C P₀ P₁ P₂ : Type} [CommRing R] [Category.{0} C]
    (hbij : ∀ (S : Type) [CommRing S] [Algebra R S] (F : C ⥤ CommAlgCat.{0} R)
      (F' : C ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧
        Function.Bijective (th1 m) ∧ Function.Bijective (th2 m))
    (F : C ⥤ CommAlgCat.{0} R) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀]
    [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F)
    (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (hM : IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂)
    (hs : ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (t : B),
      (∀ x, ¬ IsUnit x → x * t = 0) →
      ∃ (F' : C ⥤ CommAlgCat.{0} B) (_ : BC F F') (F'' : C ⥤ CommAlgCat.{0} (B ⧸ Ideal.span {t}))
        (m : BC F' F''), Function.Surjective m.coef.pull1) : SmallLift a₀ a₁ := by
  intro B _ _ _ t ht z hz
  obtain ⟨F', m0, F'', m, hsurj⟩ := hs B t ht
  obtain ⟨l, hl⟩ := GlobalTheory.T.base_change_map_composition R B (B ⧸ Ideal.span {t}) C F F' F'' m0 m
  obtain ⟨b0', b1', b2'⟩ := hbij B F F' m0
  obtain ⟨b0'', b1'', b2''⟩ := hbij (B ⧸ Ideal.span {t}) F F'' l
  obtain ⟨e', he'⟩ := GlobalTheory.T.model_comparison_degree_one_bijective R B C P₀ P₁ P₂ F F' a₀ a₁ ψ₀ ψ₁ ψ₂ m0 hM b0' b1' b2'
  obtain ⟨e'', he''⟩ :=
    GlobalTheory.T.model_comparison_degree_one_bijective R (B ⧸ Ideal.span {t}) C P₀ P₁ P₂ F F'' a₀ a₁ ψ₀ ψ₁ ψ₂ l hM b0'' b1'' b2''
  have hmk : (Ideal.Quotient.mkₐ R (Ideal.span {t})) = IsScalarTower.toAlgHom R B (B ⧸ Ideal.span {t}) := by
    ext b
    rfl
  have hzk : z ∈ (LinearMap.baseChange (B ⧸ Ideal.span {t}) a₁).ker := LinearMap.mem_ker.2 hz
  obtain ⟨w, hw⟩ := hsurj (e'' (Submodule.Quotient.mk ⟨z, hzk⟩))
  obtain ⟨q, rfl⟩ := e'.surjective w
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hxk : LinearMap.lTensor B a₁ x = 0 := LinearMap.mem_ker.1 hx
  have hxbk : LinearMap.rTensor P₁ (IsScalarTower.toAlgHom R B (B ⧸ Ideal.span {t})).toLinearMap x ∈
      (LinearMap.baseChange (B ⧸ Ideal.span {t}) a₁).ker := by
    rw [LinearMap.mem_ker]
    change LinearMap.lTensor (B ⧸ Ideal.span {t}) a₁ _ = 0
    rw [GlobalTheory.CompanionTheory.PerfVB.lTensor_rTensor_apply, hxk, map_zero]
  have key : e'' (Submodule.Quotient.mk ⟨_, hxbk⟩) = e'' (Submodule.Quotient.mk ⟨z, hzk⟩) := by
    rw [← hw]
    obtain ⟨hw1, h1⟩ := he'' _ hxbk
    obtain ⟨hw2, h2⟩ := he' x hx
    rw [h1, h2]
    have hp : ∀ c, m.coef.pull1 (GlobalTheory.CatCoh.H1.mk F' c) = GlobalTheory.CatCoh.H1.mk F'' (m.coef.pullbackOneCocycle c) :=
      fun c => rfl
    rw [hp]
    congr 1
    apply Subtype.ext
    show th1 l _ = c1 m (th1 m0 _)
    rw [← GlobalTheory.T.comparison_degree_one_tower_formula R B (B ⧸ Ideal.span {t}) C F F' F'' m0 m l hl]
    congr 1
    exact GlobalTheory.CompanionTheory.PerfVB.lTensor_rTensor_apply _ _ _
  have hq := (Submodule.Quotient.eq _).1 (e''.injective key)
  rw [Submodule.mem_comap] at hq
  obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hq
  refine ⟨x, y, hxk, ?_⟩
  rw [hmk]
  rw [map_sub, Submodule.subtype_apply, Submodule.subtype_apply] at hy
  exact hy.symm

theorem perfVB : PerfVBSt := by
  unfold MainStatements.Hodge.PerfVBSt MainStatements.Hodge.AllFin
  intro R _ P _ _ F g hPerf hSt hfib hsm
  obtain ⟨P₀, P₁, P₂, P₃, a₀, a₁, a₂, ψ₀, ψ₁, ψ₂, ⟨f0, p0⟩, ⟨f1, p1⟩, ⟨f2, p2⟩, ⟨f3, p3⟩, h10, h21, hψ1, hψ2,
    ⟨ψ₃, hψ3⟩, hQ⟩ := hPerf
  have hMod : IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ := ⟨h10, hψ1, hψ2, fun M => ⟨(hQ M).1, (hQ M).2.1⟩⟩
  obtain ⟨e, he, hψe⟩ := GlobalTheory.T.model_complex_unit_element R Pᵒᵖ P₀ P₁ P₂ F a₀ a₁ ψ₀ ψ₁ ψ₂ hMod
  have hbij : ∀ (S : Type) [CommRing S] [Algebra R S] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)
      (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧
        Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
    intro S _ _ F F' m
    exact GlobalTheory.T.comparison_maps_bijective_finite R S P F F' m
  have hE : ∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 →
      ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e) := by
    intro k _ _ x hx
    obtain ⟨F', m, hS⟩ := hSt k
    exact GlobalTheory.T.model_stein_of_comparison R k Pᵒᵖ P₀ P₁ P₂ F F' a₀ a₁ ψ₀ ψ₁ ψ₂ m e hMod (hbij k F F' m).1 hS he hψe x hx
  have hG : ∀ (k : Type) [Field k] [Algebra R k],
      Module.finrank k (Hc (a₀.baseChange k) (a₁.baseChange k)) = g := by
    intro k _ _
    obtain ⟨F', m, hm⟩ := hfib k
    obtain ⟨b0, b1, b2⟩ := hbij k F F' m
    obtain ⟨ek, -⟩ := GlobalTheory.T.model_comparison_degree_one_bijective R k Pᵒᵖ P₀ P₁ P₂ F F' a₀ a₁ ψ₀ ψ₁ ψ₂ m hMod b0 b1 b2
    rw [ek.finrank_eq]
    exact hm
  have hL : SmallLift a₀ a₁ := small_lift hbij F a₀ a₁ ψ₀ ψ₁ ψ₂ hMod (fun B _ _ _ t ht => hsm B t ht)
  haveI := f0
  haveI := p0
  haveI := f1
  haveI := p1
  haveI := f2
  haveI := p2
  have hv := vb_pure a₀ a₁ h10 g e he hE hG hL
  obtain ⟨l, -⟩ := GlobalTheory.T.base_change_map_identity R Pᵒᵖ F
  obtain ⟨c0, c1, c2⟩ := hbij R F F l
  obtain ⟨eR, -⟩ := GlobalTheory.T.model_comparison_degree_one_bijective R R Pᵒᵖ P₀ P₁ P₂ F F a₀ a₁ ψ₀ ψ₁ ψ₂ l hMod c0 c1 c2
  exact vb_of_equiv eR hv

end GlobalTheory.CompanionTheory.PerfVB
end
end

