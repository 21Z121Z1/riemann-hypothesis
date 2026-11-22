import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0618
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1510
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0796
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0791
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0698
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0699
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0008
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0867

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharpolyConjDiagonal
section
open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

namespace GlobalTheory.CompanionTheory.UnitarySide

theorem charpoly_conj_diagonal {K : Type} [Field K] {n : ℕ} (c D g : GL (Fin n) K) (d : Fin n → K)
    (hD : D.val = Matrix.diagonal d) (hg : g = c * D * c⁻¹) :
    g.val.charpoly = ∏ i, (X - C (d i)) := by
  subst hg
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, hD,
    Matrix.charpoly_diagonal]

open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hasVals_conj_diag (w : Pl E) (n : ℕ) (c : GLw n w) (u : Fin n → (w.adicCompletion E)ˣ)
    (a : Fin n → ℤ) (hu : ∀ i, ordL (u i : w.adicCompletion E) = a i) (g : GLw n w)
    (hg : g = c * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * c⁻¹) :
    HasVals g.val.charpoly a :=
  ⟨fun i => (u i : w.adicCompletion E),
    charpoly_conj_diagonal c _ g _ (GlobalTheory.SmGL.val_diagT _ _) hg,
    fun i => ⟨(u i).ne_zero, hu i⟩⟩

theorem s2 : P_contr_id → DiagonalConjDistinctValuations → Hilbert90InertPlace → P_iwU_facts → UnitaryHeckeSingleCoset := by
  intro hcontr _ _ hiw E _ _ _ hU w hw n b hb ϖ hϖ l hl γ hP
  have hyp : ∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 →
      ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧
        ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ := by
    intro y hy δ hδ
    obtain ⟨m, hm, τ, hτ, e⟩ := hcontr w ϖ hϖ n y hy δ hδ
    exact ⟨m, hm, τ, hτ, e⟩
  obtain ⟨p₀, u, hu, hγ0, hsupp, hcpt⟩ :=
    GlobalTheory.CompanionTheory.SuppCent.main E hU w hw n b hb ϖ hϖ l hl hyp γ hP
  obtain ⟨-, hKc, -, -, -⟩ := hiw w hw n b hb ϖ l
  obtain ⟨-, -, hWc, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hle : cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ (iwU n w b).map (MulAut.conj p₀).toMonoidHom := by
    rw [hcpt]
    exact inf_le_right
  refine ⟨⟨p₀, fun p => ?_, hle⟩, fun x => ⟨?_, ?_⟩, ?_⟩
  · exact hsupp p
  · exact GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj _ hKc x)
  · exact GlobalTheory.LocFin.relIndex_cptPart_ne_zero _ _ _
      (GlobalTheory.LocFin.isOpen_map_conj _ (GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b) x)
      (GlobalTheory.LocFin.isCompact_map_conj _ hWc p₀) hle
  · have hγ : γ.1 = (p₀.1 * b) * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * (p₀.1 * b)⁻¹ := by
      have e : γ.1 = p₀.1 * (p₀⁻¹ * γ * p₀).1 * p₀.1⁻¹ := by
        change γ.1 = p₀.1 * (p₀.1⁻¹ * γ.1 * p₀.1) * p₀.1⁻¹
        group
      rw [e, hγ0]
      group
    exact hasVals_conj_diag w n _ u _ hu _ hγ

end GlobalTheory.CompanionTheory.UnitarySide
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactLevelExists
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open GlobalTheory.PrincCong (congSub mem_congSub_iff isOpen_congSub exists_mat_subset)
open GlobalTheory.LFun.ConjPlace (invT invT_val mem_iff_invT map_mem_Ov_iff)
open GlobalTheory.ThetaSatake (cw cloc)
open GlobalTheory.CompanionTheory.ThetaSatPair (embT_cw invT_symm)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.KExLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_le_KGL (w : Pl E) (n k : ℕ) : congSub w n k ≤ KGL w n :=
  fun g hg => ((mem_congSub_iff w n k g).1 hg).1

theorem eventually_congSub_le (w : Pl E) (a : ℕ) (U : Subgroup (GLw a w)) (hU : IsOpen (U : Set (GLw a w))) :
    ∀ᶠ k in atTop, congSub w a k ≤ U := by
  have hVn : (U : Set (GLw a w)) ∈ 𝓝 (1 : GLw a w) := hU.mem_nhds U.one_mem
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap] at hVn
  obtain ⟨t, htn, htV⟩ := Filter.mem_comap.1 hVn
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 htn
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨N₀, hN₀⟩ := exists_mat_subset w a (Filter.inter_mem hA hB')
  filter_upwards [eventually_ge_atTop N₀] with m hm γ hγ
  have a1 := hN₀ m hm _ ((mem_congSub_iff w a _ _).1 hγ).2
  have a2 := hN₀ m hm _ ((mem_congSub_iff w a _ _).1 (inv_mem hγ)).2
  exact htV (hAB ⟨a1.1, a2.2⟩)

theorem continuous_detGL (w : Pl E) (a : ℕ) :
    Continuous (GeneralLinearGroup.det : GLw a w → (w.adicCompletion E)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_det Units.continuous_val
  · have e : (fun g : GLw a w => (((GeneralLinearGroup.det g)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E)) =
        fun g => ((g⁻¹ : GLw a w) : Matrix (Fin a) (Fin a) _).det := by
      funext g
      rw [← map_inv]
      rfl
    exact e ▸ Continuous.matrix_det (Units.continuous_val.comp continuous_inv)

theorem eventually_det (w : Pl E) (a : ℕ) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : IsOpen (μ.ker : Set (w.adicCompletion E)ˣ)) :
    ∀ᶠ k in atTop, ∀ g ∈ congSub w a k, μ (GeneralLinearGroup.det g) = 1 := by
  have hU : IsOpen ((μ.ker.comap GeneralLinearGroup.det : Subgroup (GLw a w)) : Set (GLw a w)) :=
    hμ.preimage (continuous_detGL w a)
  filter_upwards [eventually_congSub_le w a _ hU] with k hk g hg
  exact hk hg

theorem isCompact_congSub (w : Pl E) (n k : ℕ) : IsCompact (congSub w n k : Set (GLw n w)) :=
  (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_congSub w n k)) (congSub_le_KGL w n k)

theorem blocks_mem_congSub {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) {k : ℕ} (hg : blk h w m X ∈ congSub w n k) :
    m.1 ∈ congSub w a k ∧ m.2 ∈ congSub w b k := by
  obtain ⟨hK, hc⟩ := (mem_congSub_iff w n k _).1 hg
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hK
  have v := GlobalTheory.CompanionTheory.CtS.blk_val_eq h w m X
  have iv := GlobalTheory.CompanionTheory.CtS.blk_inv_val h w m X
  let e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  have v11 : ∀ i j, (blk h w m X).val (e (Sum.inl i)) (e (Sum.inl j)) = m.1.val i j := fun i j => by
    rw [v]; simp [e, reindex_apply, submatrix_apply]
  have v22 : ∀ i j, (blk h w m X).val (e (Sum.inr i)) (e (Sum.inr j)) = m.2.val i j := fun i j => by
    rw [v]; simp [e, reindex_apply, submatrix_apply]
  have i11 : ∀ i j, ((blk h w m X)⁻¹).val (e (Sum.inl i)) (e (Sum.inl j)) = (m.1⁻¹).val i j := fun i j => by
    rw [iv]; simp [e, reindex_apply, submatrix_apply]
  have i22 : ∀ i j, ((blk h w m X)⁻¹).val (e (Sum.inr i)) (e (Sum.inr j)) = (m.2⁻¹).val i j := fun i j => by
    rw [iv]; simp [e, reindex_apply, submatrix_apply]
  have o11 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (e (Sum.inl i)) (e (Sum.inl j)) =
      (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := fun i j => by
    simp [Matrix.one_apply, e.injective.eq_iff]
  have o22 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (e (Sum.inr i)) (e (Sum.inr j)) =
      (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j := fun i j => by
    simp [Matrix.one_apply, e.injective.eq_iff]
  refine ⟨(mem_congSub_iff w a k _).2 ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩,
    (mem_congSub_iff w b k _).2 ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩⟩
  · rw [← v11]; exact h1 _ _
  · rw [← i11]; exact h2 _ _
  · rw [← v11, ← o11]; exact hc _ _
  · rw [← v22]; exact h1 _ _
  · rw [← i22]; exact h2 _ _
  · rw [← v22, ← o22]; exact hc _ _

theorem conj_mem_congSub (w : Pl E) (n k : ℕ) {x g : GLw n w} (hx : x ∈ KGL w n) (hg : g ∈ congSub w n k) :
    x * g * x⁻¹ ∈ congSub w n k := by
  obtain ⟨y, hy, rfl⟩ := hg
  obtain ⟨z, rfl⟩ := hx
  exact ⟨z * y * z⁻¹, (MonoidHom.normal_ker _).conj_mem y hy z, by simp only [map_mul, map_inv]⟩

theorem invT_mem_congSub {u w : Pl E} (c : u.adicCompletion E ≃+* w.adicCompletion E)
    (hc : ∀ x, Valued.v (c x) = Valued.v x) (a k : ℕ) {g : GLw a u} (hg : g ∈ congSub u a k) :
    invT c a g ∈ congSub w a k := by
  have h1 := (mem_congSub_iff u a k _).1 hg
  have h2 := (mem_congSub_iff u a k _).1 (inv_mem hg)
  refine (mem_congSub_iff w a k _).2 ⟨(mem_iff_invT c (map_mem_Ov_iff c hc) g).1 h1.1, fun i j => ?_⟩
  have e : (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j =
      c ((1 : Matrix (Fin a) (Fin a) (u.adicCompletion E)) j i) := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  rw [invT_val, e, ← map_sub, hc]
  exact h2.2 j i

theorem under_cw (w : Pl E) :
    (cw w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) :=
  ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) (cw w) w).2
    (Or.inr (conjPl_conjSrc _ w))).symm

end GlobalTheory.CompanionTheory.KExLevel

namespace GlobalTheory.CompanionTheory.KExLevel

theorem kEx : KEx := by
  intro E _ _ _ n Sec _ R _ μ hμ L hL
  let T : Finset (Pl E) := R ∪ R.image cw
  have A : ∀ a ∈ Finset.range (n + 1), ∀ w ∈ R, ∀ᶠ k in atTop, ∀ m : GLw a w × GLw (n - a) w,
      m.1 ∈ congSub w a k → m.2 ∈ congSub w (n - a) k → m ∈ L a w := by
    intro a ha w hw
    obtain ⟨L₁, L₂, e, l1, l2⟩ := hL a (Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)) w hw
    filter_upwards [eventually_congSub_le w a L₁ l1.1, eventually_congSub_le w (n - a) L₂ l2.1] with k h1 h2 m m1 m2
    rw [e]
    exact ⟨h1 m1, h2 m2⟩
  have B : ∀ a ∈ Finset.range (n + 1), ∀ w ∈ T, ∀ᶠ k in atTop, ∀ m : GLw a w × GLw (n - a) w,
      m.1 ∈ congSub w a k → m.2 ∈ congSub w (n - a) k →
        μ w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1 := by
    intro a _ w _
    filter_upwards [eventually_det w a (μ w) (hμ w), eventually_det w (n - a) (μ w) (hμ w)] with k h1 h2 m m1 m2
    rw [map_mul, map_pow, map_pow, h1 _ m1, h2 _ m2, one_pow, one_pow, one_mul]
  obtain ⟨M, hA, hB⟩ := (((Filter.eventually_all_finset _).2 fun a ha =>
    (Filter.eventually_all_finset _).2 (A a ha)).and ((Filter.eventually_all_finset _).2 fun a ha =>
    (Filter.eventually_all_finset _).2 (B a ha))).exists
  have hT : ∀ w, w ∈ T → (if w ∈ T then congSub w n M else KGL w n) = congSub w n M := fun w hw => if_pos hw
  refine ⟨fun w => if w ∈ T then congSub w n M else KGL w n, ⟨fun w => ?_, ?_⟩, fun w => ?_, fun w hw => ?_,
    fun a ha w hw m X hm => ?_, fun a ha w hw hs u hc m X hm => ?_⟩
  · by_cases h : w ∈ T
    · simp only [if_pos h]; exact isOpen_congSub w n M
    · simp only [if_neg h]; exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1
  · refine Filter.eventually_cofinite.2 (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    refine hw ?_
    have h' : w ∉ T := h
    simp only [if_neg h']
    exact le_rfl
  · by_cases h : w ∈ T
    · simp only [if_pos h]; exact isCompact_congSub w n M
    · simp only [if_neg h]; exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  · refine if_neg fun h => ?_
    rcases Finset.mem_union.1 h with h | h
    · exact hw w h rfl
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 h
      exact hw r hr (under_cw r).symm
  · have hwT : w ∈ T := Finset.mem_union_left _ hw
    have ha' : a ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_iff.2 ha)
    simp only [if_pos hwT] at hm
    obtain ⟨b1, b2⟩ := blocks_mem_congSub _ w m X hm
    exact ⟨hA a ha' w hw m b1 b2, hB a ha' w hwT m b1 b2⟩
  · have hu : u = cw w := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hc
    have huT : u ∈ T := Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hw, hu.symm⟩)
    have hw' : w = cw u := by rw [hu]; exact (GlobalTheory.ThetaPull.conjSrc_conjSrc w).symm
    have ha' : a ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_iff.2 ha)
    simp only [if_pos huT] at hm
    obtain ⟨b1, b2⟩ := blocks_mem_congSub _ u m X hm
    clear hu hc
    subst hw'
    have hv : ∀ x, Valued.v ((cloc u).symm x) = Valued.v x := fun x => by
      have := (GlobalTheory.CuspRep.conjLoc_spec (IsCMField.complexConj E).toRingEquiv u).2.2 ((cloc u).symm x)
      have e : GlobalTheory.CuspRep.conjLoc (IsCMField.complexConj E).toRingEquiv u ((cloc u).symm x) = x :=
        (cloc u).apply_symm_apply x
      rw [e] at this
      exact this.symm
    let p : ∀ c : ℕ, GLw c u → GLw c (cw u) := fun c g =>
      (invT (cloc u) c).symm ((PhiU c (u.adicCompletion E))⁻¹ * g * PhiU c (u.adicCompletion E))
    have hp : ∀ c (g : GLw c u), g ∈ congSub u c M → p c g ∈ congSub (cw u) c M := fun c g hg => by
      have hk : (PhiU c (u.adicCompletion E))⁻¹ ∈ KGL u c := inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ c)
      have h1 := conj_mem_congSub u c M hk hg
      rw [inv_inv] at h1
      change (invT (cloc u) c).symm _ ∈ _
      rw [invT_symm]
      exact invT_mem_congSub (cloc u).symm hv c M h1
    have he : ∀ c (g : GLw c u), embW c u g = embT c (cw u) (p c g) := fun c g => by
      rw [embT_cw]
      simp only [p, MulEquiv.apply_symm_apply]
      congr 1
      group
    exact ⟨hB a ha' u huT m b1 b2, (p a m.1, p (n - a) m.2), hA a ha' (cw u) hw _ (hp _ _ b1) (hp _ _ b2),
      he _ _, he _ _⟩

end GlobalTheory.CompanionTheory.KExLevel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicativeStatement
section
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_multiplicative : CtMul := by
  first | exact @GlobalTheory.CompanionTheory.CtMulSplit.ctMul | exact GlobalTheory.CompanionTheory.CtMulSplit.ctMul | (intros; apply GlobalTheory.CompanionTheory.CtMulSplit.ctMul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCj
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwUFacts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

theorem iwU_facts : P_iwU_facts := by
  intro E _ _ _ w hw n b hb ϖ l
  have hc : Continuous (cj w) := continuous_cj w
  exact ⟨GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w, GlobalTheory.CompanionTheory.IwLevels.isCompact_KL hw n hc,
    ⟨GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b, GlobalTheory.CompanionTheory.IwLevels.iwU_le_KL n w b hb.1, fun k hk => hk⟩,
    GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero (GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b)
      (GlobalTheory.CompanionTheory.IwLevels.isCompact_KL hw n hc),
    GlobalTheory.CompanionTheory.IwLevels.isCompact_support_fU hw n b ϖ l hc⟩

end GlobalTheory.CompanionTheory.IwUFacts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpiOfFiniteFlat
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.Dblock

theorem epiOfFF : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  intro R _ A B A' l hf hs hq g₁ g₂ h
  have : EffectiveEpi l.left := inferInstance
  have : Epi l.left := inferInstance
  apply Over.OverMorphism.ext
  rw [← cancel_epi l.left]
  simpa using congrArg (fun k => k.left) h

end GlobalTheory.CompanionTheory.Dblock
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorThroughFiniteFlat
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp)

namespace GlobalTheory.CompanionTheory.FlatFactor

theorem ext_of_affine_points {R : Type} [CommRing R] {W X : Over (Sp R)} (u v : W ⟶ X)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (t : sp (R₀ := R) S ⟶ W), t ≫ u = t ≫ v) : u = v := by
  have key : ∀ (B : CommRingCat.{0}) (j₀ : Spec B ⟶ W.left), j₀ ≫ u.left = j₀ ≫ v.left := by
    intro B j₀
    letI : Algebra R B := (Spec.preimage (j₀ ≫ W.hom)).hom.toAlgebra
    let j : sp (R₀ := R) B ⟶ W := Over.homMk j₀ (Spec.map_preimage (j₀ ≫ W.hom)).symm
    exact congrArg CommaMorphism.left (h B j)
  apply Over.OverMorphism.ext
  exact Scheme.Cover.hom_ext W.left.affineCover _ _ fun i => key _ _

theorem comp_eq_of_comp_eq {R : Type} [CommRing R] {A B A' : Over (Sp R)} [GrpObj A] [GrpObj B] [GrpObj A']
    (l : A ⟶ B) (f : A ⟶ A') [IsMonHom l] [IsMonHom f]
    (hk : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A), z ≫ l = 1 → z ≫ f = 1)
    {W : Over (Sp R)} (a b : W ⟶ A) (h : a ≫ l = b ≫ l) : a ≫ f = b ≫ f := by
  refine ext_of_affine_points _ _ fun S _ _ t => ?_
  have h1 : ((t ≫ a) / (t ≫ b)) ≫ l = 1 := by
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, h, div_self']
  have h2 := hk S _ h1
  rw [GrpObj.div_comp, div_eq_one] at h2
  simpa using h2

theorem factorThroughFF : PositivityTheory.Tls2.Zar3.Ch1.FactorThroughFF := by
  intro R _ A B A' _ _ _ l f hl hf hfl hsl hql hk
  have hc : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ A.left), g ≫ l.left = g' ≫ l.left →
      g ≫ f.left = g' ≫ f.left := by
    intro Z g g' h
    have hw : g' ≫ A.hom = g ≫ A.hom := by
      rw [← Over.w l, ← Category.assoc, ← h, Category.assoc]
    have := comp_eq_of_comp_eq l f hk (W := Over.mk (g ≫ A.hom))
      (Over.homMk g rfl) (Over.homMk g' hw) (Over.OverMorphism.ext h)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac l.left f.left hc
  let g : B ⟶ A' := Over.homMk (EffectiveEpi.desc l.left f.left hc) (by
    rw [← cancel_epi l.left, ← Category.assoc, hfac, Over.w, Over.w])
  have hg : l ≫ g = f := Over.OverMorphism.ext hfac
  refine ⟨g, ⟨?_, ?_⟩, hg⟩
  · rw [← IsMonHom.one_hom l, Category.assoc, hg, IsMonHom.one_hom]
  · have := GlobalTheory.FlatQuotient.epi_tensorHom l l
    rw [← cancel_epi (l ⊗ₘ l), ← IsMonHom.mul_hom_assoc, hg, tensorHom_comp_tensorHom_assoc, hg,
      IsMonHom.mul_hom]

end GlobalTheory.CompanionTheory.FlatFactor
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfFiniteFibres
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.AbFibre

theorem isPullback_baseChange {S T : Scheme.{0}} (s : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback ((Over.pullback s).map f).left (pullback.fst X.hom s) (pullback.fst Y.hom s) f.left := by
  have h1 : ((Over.pullback s).map f).left ≫ pullback.snd Y.hom s = pullback.snd X.hom s := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_snd _ _ _
  have h2 : ((Over.pullback s).map f).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ f.left := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hX : f.left ≫ Y.hom = X.hom := Over.w f
  refine IsPullback.of_right ?_ h2 (IsPullback.of_hasPullback Y.hom s).flip
  rw [h1, hX]
  exact (IsPullback.of_hasPullback X.hom s).flip

theorem exists_geometric_point {S : Scheme.{0}} (Y : Over S) (y : Y.left) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (s : Spec (.of Ω) ⟶ S) (w : ↥(pullback Y.hom s)),
      pullback.fst Y.hom s w = y := by
  let Ω := AlgebraicClosure (Y.left.residueField y)
  let g : Spec (.of Ω) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) Ω)) ≫ Y.left.fromSpecResidueField y
  let L : Spec (.of Ω) ⟶ pullback Y.hom (g ≫ Y.hom) := pullback.lift g (𝟙 _) (by simp)
  let pt : ↥(Spec (.of Ω)) := IsLocalRing.closedPoint Ω
  refine ⟨Ω, inferInstance, inferInstance, g ≫ Y.hom, L pt, ?_⟩
  change (L ≫ pullback.fst Y.hom (g ≫ Y.hom)) pt = y
  rw [pullback.lift_fst]
  exact Scheme.fromSpecResidueField_apply y _

theorem finiteOfFibres : PositivityTheory.Tls2.Zar3.Ch1.FiniteOfFibres := by
  intro R _ A B _ _ l hA hB _ hfib
  haveI := hA
  haveI := hB
  have hcomp : l.left ≫ B.hom = A.hom := Over.w l
  haveI : IsProper A.hom := IsAbelianScheme.proper (A := A)
  haveI : IsProper B.hom := IsAbelianScheme.proper (A := B)
  haveI : IsProper (l.left ≫ B.hom) := by rw [hcomp]; infer_instance
  haveI : IsProper l.left := IsProper.of_comp l.left B.hom
  have lift : ∀ {T : Scheme.{0}} (s : T ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (x : ↥A.left)
      (w : ↥(pullback B.hom s)), pullback.fst B.hom s w = l.left x →
      ∃ v, ((Over.pullback s).map l).left v = w ∧ pullback.fst A.hom s v = x := by
    intro T s x w hxw
    have h := isPullback_baseChange s l
    obtain ⟨z, hz1, hz2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := pullback.fst B.hom s) (g := l.left) w x hxw
    refine ⟨h.isoPullback.inv z, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz1]
    · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz2]
  have hfin : ∀ y : ↥B.left, (l.left ⁻¹' {y}).Finite := by
    intro y
    obtain ⟨Ω, _, _, s, w, hw⟩ := exists_geometric_point B y
    have hF : IsFinite ((Over.pullback s).map l).left := (hfib Ω s).1
    refine ((Scheme.Hom.finite_preimage_singleton ((Over.pullback s).map l).left w).image
      (pullback.fst A.hom s)).subset ?_
    intro x hx
    have hx' : l.left x = y := hx
    obtain ⟨v, hv1, hv2⟩ := lift s x w (by rw [hw, hx'])
    exact ⟨v, hv1, hv2⟩
  have hsurj : Surjective l.left := by
    refine ⟨fun y => ?_⟩
    obtain ⟨Ω, _, _, s, w, hw⟩ := exists_geometric_point B y
    have hS : Surjective ((Over.pullback s).map l).left := (hfib Ω s).2
    obtain ⟨v, hv⟩ := hS.surj w
    refine ⟨pullback.fst A.hom s v, ?_⟩
    have hsq := (isPullback_baseChange s l).w
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply, hv, hw]
  haveI : LocallyQuasiFinite l.left := LocallyQuasiFinite.of_finite_preimage_singleton l.left hfin
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite l.left, hsurj⟩

end GlobalTheory.CompanionTheory.AbFibre
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfFibresFinite
section
namespace GlobalTheory.CompanionTheory.FlatFib

theorem flatOfFibresFinite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  intro R _ X Y f h1 h0 h2 h3 H
  exact GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ X Y f h1 h0 h2 h3 H

end GlobalTheory.CompanionTheory.FlatFib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSplitOfStatement
section
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_split_of : MatchSplitOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf | exact GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf | (intros; apply GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf <;> assumption)
end

