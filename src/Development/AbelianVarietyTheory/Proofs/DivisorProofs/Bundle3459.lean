import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinOrderSpanningFamilyPosDefMatrix
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

open Matrix

namespace GlobalTheory.ZarhinFam.SpanFam

def colL (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 (quat d)ᵀ 0 ((d : ℤ) • 1)

def colR (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 0 (quat d) 1

theorem colL_mul_transpose {d : ℕ} (hd : 0 < d) : colL d * (colL d)ᵀ = (d : ℤ) • form d := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [colL, form, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul]
  congr 1
  · rw [transpose_transpose, quat_transpose_mul, h1]; simp [sub_smul, smul_smul]
  · simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, transpose_zero, transpose_smul, transpose_one]
  · simp
  · simp [smul_smul]

theorem colR_mul_transpose {d : ℕ} (hd : 0 < d) : colR d * (colR d)ᵀ = form d := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [colR, form, fromBlocks_transpose, fromBlocks_multiply]
  congr 1
  · simp
  · simp
  · simp
  · rw [quat_mul_transpose, h1]; simp [sub_smul]

def col (d : ℕ) (q : Fin 4 ⊕ Fin 4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  Sum.elim (fun _ => colL d) (fun _ => colR d) q

def famM (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  col d t.2 * single t.1 t.2 1

theorem famM_apply (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) (p q : Fin 4 ⊕ Fin 4) :
    famM d t p q = if q = t.2 then col d t.2 p t.1 else 0 := by
  unfold famM
  split_ifs with h
  · subst h; simp
  · exact mul_single_apply_of_ne _ _ _ _ _ h _

theorem famM_mem (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) : famM d t ∈ ord d := by
  intro i j
  rw [famM_apply]
  obtain ⟨k, q⟩ := t
  split_ifs with h
  · simp only at h
    subst h
    rcases k with k | k
    · simp only [col, colL, Sum.elim_inl, fromBlocks_apply₂₁, Matrix.zero_apply]; exact dvd_zero _
    · simp only [col, colL, Sum.elim_inl, fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
  · exact dvd_zero _

theorem famM_form_transpose {d : ℕ} (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) :
    famM d t * form d * (famM d t)ᵀ = col d t.2 * single t.1 t.1 (form d t.2 t.2) * (col d t.2)ᵀ := by
  calc famM d t * form d * (famM d t)ᵀ
      = col d t.2 * (single t.1 t.2 1 * form d * single t.2 t.1 1) * (col d t.2)ᵀ := by
        simp only [famM, transpose_mul, transpose_single, Matrix.mul_assoc]
    _ = _ := by rw [single_mul_mul_single, _root_.one_mul, _root_.mul_one]

theorem sum_single_diag' (c : ℤ) : ∑ k : Fin 4 ⊕ Fin 4, single k k c = c • (1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) := by
  ext a b
  rw [Matrix.sum_apply]
  by_cases h : a = b
  · subst h; simp [single_apply]
  · rw [Finset.sum_eq_zero (fun k _ => by rw [single_apply]; exact if_neg (fun hk => h (hk.1.symm.trans hk.2)))]
    simp [Matrix.one_apply, h]

theorem sum_famM {d : ℕ} (hd : 0 < d) :
    ∑ t, famM d t * form d * (famM d t)ᵀ = ((8 * d : ℕ) : ℤ) • form d := by
  simp_rw [famM_form_transpose]
  rw [Fintype.sum_prod_type_right]
  have hq : ∀ q : Fin 4 ⊕ Fin 4, ∑ k : Fin 4 ⊕ Fin 4, col d q * single k k (form d q q) * (col d q)ᵀ
      = form d q q • (col d q * (col d q)ᵀ) := by
    intro q
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_single_diag', Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]
  simp_rw [hq]
  rw [Fintype.sum_sum_type]
  simp only [col, Sum.elim_inl, Sum.elim_inr, colL_mul_transpose hd, colR_mul_transpose hd, smul_smul]
  have e1 : ∀ j : Fin 4, form d (Sum.inl j) (Sum.inl j) = 1 := fun j => by simp [form]
  have e2 : ∀ j : Fin 4, form d (Sum.inr j) (Sum.inr j) = d := fun j => by
    simp only [form, fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, _root_.mul_one]
  simp only [e1, e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← add_smul, smul_smul]
  rw [_root_.one_mul, ← add_nsmul, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
  congr 1

def fam (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) : ord d := ⟨famM d t, famM_mem d t⟩

def coef (d : ℕ) (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) : (Fin 4 ⊕ Fin 4) → (Fin 4 ⊕ Fin 4) → ℤ
  | Sum.inr m, Sum.inl j => N (Sum.inr m) (Sum.inl j) / d
  | Sum.inl m, Sum.inl j => N (Sum.inl m) (Sum.inl j) - ∑ s, quat d s m * (N (Sum.inr s) (Sum.inl j) / d)
  | Sum.inl m, Sum.inr j => N (Sum.inl m) (Sum.inr j)
  | Sum.inr m, Sum.inr j => N (Sum.inr m) (Sum.inr j) - ∑ s, quat d m s * N (Sum.inl s) (Sum.inr j)

theorem sum_coef_famM {d : ℕ} {N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ} (hN : N ∈ ord d) (p q : Fin 4 ⊕ Fin 4) :
    ∑ t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4), coef d N t.1 t.2 * famM d t p q = N p q := by
  simp only [famM_apply, mul_ite, mul_zero]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hdiv : ∀ m j, (d : ℤ) * (N (Sum.inr m) (Sum.inl j) / d) = N (Sum.inr m) (Sum.inl j) :=
    fun m j => Int.mul_ediv_cancel' (hN m j)
  rcases q with j | j <;> rcases p with m | m <;>
    simp [Fintype.sum_sum_type, col, colL, colR, coef, Matrix.one_apply, Matrix.smul_one_eq_diagonal, Matrix.diagonal_apply, hdiv, mul_comm]
  all_goals done

end GlobalTheory.ZarhinFam.SpanFam

namespace GlobalTheory.ZarhinFam.SpanFam

theorem span_fam_eq_top {d : ℕ} : Submodule.span ℤ (Set.range (fam d)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  rintro ⟨N, hN⟩
  have hx : (⟨N, hN⟩ : ord d) = ∑ t, coef d N t.1 t.2 • fam d t := by
    apply Subtype.ext
    ext p q
    change N p q = ((∑ t, coef d N t.1 t.2 • fam d t : ord d) : Matrix _ _ ℤ) p q
    rw [← sum_coef_famM hN p q]
    simp only [fam, AddSubmonoidClass.coe_finset_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [AddSubgroupClass.coe_zsmul, Matrix.smul_apply, smul_eq_mul]
  rw [hx]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

theorem sum_fam_mul_bar {d : ℕ} (hd : 0 < d) :
    ∑ t, fam d t * bar d (fam d t) = ((8 * d : ℕ) : ord d) := by
  apply Subtype.ext
  have h : ∑ t, famM d t * form d * (famM d t)ᵀ * formInv d = ((8 * d : ℕ) : ℤ) • (1 : Matrix _ _ ℤ) := by
    rw [← Finset.sum_mul, sum_famM hd, Matrix.smul_mul, form_mul_formInv hd]
  simp only [fam, bar_coe, Subring.coe_mul, Matrix.mul_assoc] at h ⊢
  simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, bar_coe, Matrix.mul_assoc]
  rw [h]
  simp only [Subring.coe_natCast]
  rw [Nat.cast_smul_eq_nsmul ℤ, nsmul_one]

end GlobalTheory.ZarhinFam.SpanFam

namespace GlobalTheory.ZarhinFam

theorem exists_spanning_family_posDef :
    ∀ (d : ℕ), 0 < d → ∃ (r : ℕ) (eO : Fin r → GlobalTheory.ZarhinFam.ord d) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * GlobalTheory.ZarhinFam.bar d (eO i)) = (d₀ : GlobalTheory.ZarhinFam.ord d) := by
  intro d hd
  let e := Fintype.equivFin ((Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4))
  refine ⟨_, fun i => SpanFam.fam d (e.symm i), 1, 8 * d, ?_, ?_, by omega, ?_⟩
  · have hc : (fun i => SpanFam.fam d (e.symm i)) = SpanFam.fam d ∘ e.symm := rfl
    rw [hc, e.symm.surjective.range_comp]
    exact SpanFam.span_fam_eq_top
  · rw [transpose_one, Matrix.map_add _ Int.cast_add, Matrix.map_one _ Int.cast_zero Int.cast_one]
    exact Matrix.PosDef.one.add Matrix.PosDef.one
  · simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← SpanFam.sum_fam_mul_bar hd]
    exact Equiv.sum_comp e.symm (fun t => SpanFam.fam d t * bar d (SpanFam.fam d t))

end GlobalTheory.ZarhinFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantAbsLeNineExplicit
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.ShortGenComp

set_option maxHeartbeats 1000000 in

theorem short_gen_comp : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 10 * Lb → ∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) (abelian₂ : ℝ), CompHt.IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) w abelian₂ ∧ Real.log abelian₂ ≤ C * (((D.R.f : ℝ) * D.R.r * Lb) ^ 3 * (∑ τ, ∑ k, |(la τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * Lb) ^ 5) ∧ Real.log n ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro hP
  obtain ⟨C2, hC2, h2⟩ := GlobalTheory.T.flat_constant_abs_le_nine_deep hP
  obtain ⟨Cb, hCb, hb⟩ := GlobalTheory.T.antitone_weight_log_bound hP
  refine ⟨2000 + Cb + C2, by positivity, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hfs hfr ho c₁ hc₁ hc₁b la hla hgap hsz Z
  have hgood := (GlobalTheory.T.good_weight_antitone_gap hP D T hT j hp hq hE hj Y e o hY la hla fun τ =>
    le_trans (by exact_mod_cast (by omega : 1 ≤ 8 * D.R.f * D.R.r + 10)) (hgap τ)).2 Z
  obtain ⟨s, hsL, hsp, hsn⟩ := h2 D T hT j hp hq hE hj Y e o hY Lb hLb hM hfs hfr ho c₁ hc₁ hc₁b la hla hgap hsz Z
  haveI : FiniteDimensional Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) :=
    hgood.1.some.2.1.1.finiteDimensional_of_finite
  obtain ⟨n, w, abelian₂, hsg, hLam, hn⟩ := GlobalTheory.T.exists_short_generators_of_short_spanning_family Y.d.c₂.F _
    (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) s _
    hgood.2.1 (fun σ f => AllWt.petAt_nonneg _ _ _ _ _ _ _)
    (fun σ a f => AllWt.petOn_smul _ _ _ _ Z _ σ a f) (GlobalTheory.T.petersson_norm_component_add_le_of_gramFrame _ _ _ _ Z _ hgood) hsL hsp hsn
  refine ⟨n, w, abelian₂, hsg, ?_⟩

  have hf1 : 1 ≤ D.R.f ∧ 1 ≤ D.R.r := by
    have hn : 1 ≤ D.R.ord := D.R.ord_pos
    have hf : D.R.f = 2 * D.R.ord := rfl
    have hk := D.R.f_le_k
    have ht := D.R.rank_add_five_le
    exact ⟨by omega, by unfold Ranks.r; omega⟩
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1.1
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hf1.2
  set X : ℝ := (D.R.f : ℝ) * D.R.r * Lb with hXdef
  set S : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)| with hSdef
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hfR hrR) hLb
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hX2 : X ^ 2 ≤ X ^ 5 := pow_le_pow_right₀ hX (by norm_num)
  have hX3 : X ^ 3 ≤ X ^ 5 := pow_le_pow_right₀ hX (by norm_num)
  have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hX (by norm_num)
  have hX1 : 1 ≤ X ^ 3 := one_le_pow₀ hX
  have hXS : 0 ≤ X ^ 3 * S := mul_nonneg (by positivity) hS
  have hrhs : 0 ≤ (2000 + Cb + C2) * (X ^ 3 * S + X ^ 5) := by positivity
  have hlogd : Real.log (Module.finrank ℚ Y.d.c₂.F : ℝ) ≤ o := hY.deg
  have hdpos : (0 : ℝ) < Module.finrank ℚ Y.d.c₂.F := by exact_mod_cast Module.finrank_pos
  have hdisc : (0 : ℝ) < |((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero Y.d.c₂.F)
  have hlrd : Real.log (|((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ Y.d.c₂.F : ℝ))) ≤ o := by
    rw [Real.log_rpow hdisc, one_div, inv_mul_le_iff₀ hdpos, mul_comm]
    exact hY.rd
  have hberg := (hb D T hT j hp hq hE hj Y e o hY Lb hLb hM hfs hfr ho la hla (by linarith) Z).2.2
  have hm : Real.log (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) ≤ Cb * X ^ 3 := hberg
  have ho' : o ≤ 391 * X ^ 2 := ho
  have hCbX : Cb * X ^ 3 ≤ Cb * X ^ 5 := mul_le_mul_of_nonneg_left hX3 hCb
  constructor
  · have hL1 : 1 ≤ abelian₂ := hsg.one_le
    rcases le_or_gt ((Module.finrank ℚ Y.d.c₂.F : ℝ) ^ 4 * (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) *
        |((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ Y.d.c₂.F : ℝ)) *
        Real.exp (C2 * (X ^ 3 * S + X ^ 5))) 1 with hB | hB
    · have : abelian₂ = 1 := le_antisymm (hLam.trans (max_le le_rfl hB)) hL1
      rw [this, Real.log_one]; exact hrhs
    · have hLB := hLam.trans (le_of_eq (max_eq_right hB.le))
      have hmpos : (0 : ℝ) < (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) := by
        rcases (Nat.cast_nonneg (α := ℝ) (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)))).lt_or_eq with h | h
        · exact h
        · rw [← h] at hB; simp at hB; linarith
      have hrd : 0 < |((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ Y.d.c₂.F : ℝ)) :=
        Real.rpow_pos_of_pos hdisc _
      have hlog := Real.log_le_log (by linarith) hLB
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity) hrd.ne',
        Real.log_mul (by positivity) hmpos.ne', Real.log_pow, Real.log_exp] at hlog
      have hC2X : C2 * (X ^ 3 * S + X ^ 5) ≤ C2 * (X ^ 3 * S + X ^ 5) := le_rfl
      nlinarith
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; positivity
    · have hnR : (n : ℝ) ≤ 2 * (Module.finrank ℚ Y.d.c₂.F : ℝ) * (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) := by
        exact_mod_cast hn
      have hmpos : (0 : ℝ) < (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) := by
        have : 0 < Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) := by
          rcases Nat.eq_zero_or_pos (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0))) with h | h
          · rw [h] at hn; omega
          · exact h
        exact_mod_cast this
      have hlog := Real.log_le_log (by exact_mod_cast hpos) hnR
      rw [Real.log_mul (by positivity) hmpos.ne', Real.log_mul (by norm_num) hdpos.ne'] at hlog
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9; linarith
      have hC2X3 : 0 ≤ C2 * X ^ 3 := by positivity
      nlinarith

end GlobalTheory.ShortGenComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeUnitHasGeneratorWeightOnPreimages
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.Gauge

theorem isWt_zero_pbT_factor {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {Z : Scheme.{0}} (m₁ : Y.H.left ⟶ Z) (τ : Q.P.A.left ⟶ Z)
    (hm : m₁ = Y.q.left ≫ τ) {U : Z.Opens} (s : Γ(Z, U)) {V : Y.H.left.Opens} (hV : V ≤ m₁ ⁻¹ᵁ U) :
    IsWt Y 0 V (pbT m₁ s V) := by
  intro S _ φ z z' c a a' ha ha' h1 h2 hq hc
  have e : a' ≫ m₁ = a ≫ m₁ := by
    subst ha ha' hm
    have := congrArg CommaMorphism.left hq
    simp only [Over.comp_left] at this
    rw [← Category.assoc, this, Category.assoc]
  rw [GlobalTheory.HeatGlue.valR_pbT a' m₁ hV h2, GlobalTheory.HeatGlue.valR_pbT a m₁ hV h1, e, GlobalTheory.Heat.WtAlg.c_zero z z' c hc,
    Units.val_one, _root_.one_mul]

end GlobalTheory.Heat.Gauge

open GlobalTheory.Heat.Gauge in

theorem GlobalTheory.Heat.Gauge.gU_isWt : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (dd : Fin n → Fld Y.H.left) (D : R → R) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D) (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∀ (p : h₁.J × (Fin 2 → Q.P.L.ι)) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ GlobalTheory.Heat.Gauge.W Y.q.left h₁ p → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (GlobalTheory.Heat.Gauge.gU Y.q.left h₁ e p).val (Y.q.left ⁻¹ᵁ V)) := by
  intro R _ _ Q O _ _ _ oa Y n dd D x h₁ e β hwe p V hV
  obtain ⟨τ, hτ⟩ := trans_factor Q oa Y x
  have hW := W_le_wchart Y.q.left h₁ p
  have hm := W_le_m₁ Y.q.left h₁ p
  have key : rsT (gU Y.q.left h₁ e p).val (Y.q.left ⁻¹ᵁ V) =
      pbT ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) (Q.P.L.g (p.2 1) (h₁.j p.1)).val (Y.q.left ⁻¹ᵁ V) *
        rsT (e.s p.2).val (Y.q.left ⁻¹ᵁ V) := by
    rw [gU, Units.val_mul, GlobalTheory.KS.AdjDlog.val_res_pullU]
    erw [GlobalTheory.KS.AdjDlog.val_res hW]
    rw [GlobalTheory.KS.rsT_mul,
      GlobalTheory.KS.rsT_rsT hW hV, GlobalTheory.KS.rsT_pbT _ hm hV]
    exact mul_comm _ _
  rw [key]
  exact GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul
    (isWt_zero_pbT_factor Y _ τ hτ _ (hV.trans hm))
    (hwe p.2 V (hV.trans hW))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeUnitsTransitionRelationOnOverlaps
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.Gauge

theorem gU_transition : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), L.IsLB → e.IsGen → ∀ (p p' : h₁.J × (Fin 2 → L.ι)) (O : G.left.Opens), O ≤ GlobalTheory.Heat.Gauge.W m h₁ p ⊓ GlobalTheory.Heat.Gauge.W m h₁ p' → pbT m (L.g (p.2 0) (p'.2 0)).val O * rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p').val O = rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O * pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O := by
  intro R _ G _ _ n X m m₁ L dd D h₁ e hL he p p' O hO
  have hWp : O ≤ W m h₁ p := hO.trans inf_le_left
  have hWp' : O ≤ W m h₁ p' := hO.trans inf_le_right
  have gv : ∀ q, O ≤ W m h₁ q → rsT (gU m h₁ e q).val O =
      rsT (e.s q.2).val O * pbT m₁ (L.g (q.2 1) (h₁.j q.1)).val O := by
    intro q hq
    rw [gU, Units.val_mul, GlobalTheory.KS.rsT_mul, GlobalTheory.KS.AdjDlog.val_res_pullU m₁ (W_le_m₁ m h₁ q),
      GlobalTheory.KS.rsT_pbT m₁ (W_le_m₁ m h₁ q) hq]
    have a : rsT (res (W_le_wchart m h₁ q) (e.s q.2)).val O = rsT (e.s q.2).val O :=
      (congrArg (fun s => rsT s O) (GlobalTheory.KS.AdjDlog.val_res (W_le_wchart m h₁ q) (e.s q.2))).trans
        (GlobalTheory.KS.rsT_rsT (W_le_wchart m h₁ q) hq _)
    exact congrArg (· * _) a
  have hj : O ≤ LB.wchart L ![m, m₁] p.2 ⊓ LB.wchart L ![m, m₁] p'.2 :=
    le_inf (hWp.trans (W_le_wchart m h₁ p)) (hWp'.trans (W_le_wchart m h₁ p'))
  have hj' : O ≤ (LB.LinComb L ![m, m₁] ![1, -1]).U p.2 ⊓ (LB.LinComb L ![m, m₁] ![1, -1]).U p'.2 := hj
  have g1 : rsT (e.s p.2).val O = (res hj' ((LB.LinComb L ![m, m₁] ![1, -1]).g p.2 p'.2)).val * rsT (e.s p'.2).val O := by
    have g0 := congrArg (fun u => (res hj' u).val) (he p.2 p'.2)
    simp only [map_mul, Units.val_mul, GlobalTheory.KS.AdjDlog.res_res'] at g0
    rw [GlobalTheory.KS.AdjDlog.val_res hj']
    simpa only [GlobalTheory.KS.AdjDlog.val_res] using g0
  have le : ∀ k : Fin 2, O ≤ (![m, m₁] k) ⁻¹ᵁ (L.U (p.2 k) ⊓ L.U (p'.2 k)) := fun k =>
    le_inf ((hj.trans inf_le_left).trans (LB.wchart_le L _ _ k)) ((hj.trans inf_le_right).trans (LB.wchart_le L _ _ k))
  have ec : res hj' ((LB.LinComb L ![m, m₁] ![1, -1]).g p.2 p'.2) =
      ∏ k, res (le k) (pullU _ _ (L.g (p.2 k) (p'.2 k))) ^ (![(1 : ℤ), -1] k) := by
    refine (map_prod (res hj') _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow (res hj') _ _).trans ?_)
    exact congrArg (fun u => u ^ (![(1 : ℤ), -1] k)) (GlobalTheory.KS.AdjDlog.res_res' _ hj' _)
  have v0 : (res (le 0) (pullU (![m, m₁] 0) _ (L.g (p.2 0) (p'.2 0)))).val = pbT m (L.g (p.2 0) (p'.2 0)).val O :=
    GlobalTheory.KS.AdjDlog.val_res_pullU _ (le 0) _
  have v1 : (res (le 1) (pullU (![m, m₁] 1) _ (L.g (p.2 1) (p'.2 1)))).val = pbT m₁ (L.g (p.2 1) (p'.2 1)).val O :=
    GlobalTheory.KS.AdjDlog.val_res_pullU _ (le 1) _
  have hv : (res hj' ((LB.LinComb L ![m, m₁] ![1, -1]).g p.2 p'.2)).val * pbT m₁ (L.g (p.2 1) (p'.2 1)).val O =
      pbT m (L.g (p.2 0) (p'.2 0)).val O := by
    rw [ec, Fin.prod_univ_two, ← v0, ← v1]
    rw [show (![(1 : ℤ), -1] 0) = 1 from rfl, show (![(1 : ℤ), -1] 1) = -1 from rfl, zpow_one, zpow_neg_one,
      ← Units.val_mul, inv_mul_cancel_right]
  have m1p := hWp.trans (W_le_m₁ m h₁ p)
  have m1p' := hWp'.trans (W_le_m₁ m h₁ p')
  have coc1 := GlobalTheory.Heat.Glue.pbT_cocycle hL m₁ (p.2 1) (h₁.j p.1) (h₁.j p'.1)
    (O := O) (fun y hy => ⟨⟨(m1p hy).1, (m1p hy).2⟩, (m1p' hy).2⟩)
  have coc2 := GlobalTheory.Heat.Glue.pbT_cocycle hL m₁ (p.2 1) (p'.2 1) (h₁.j p'.1)
    (O := O) (fun y hy => ⟨⟨(m1p hy).1, (m1p' hy).1⟩, (m1p' hy).2⟩)
  rw [gv p hWp, gv p' hWp']
  linear_combination -(rsT (e.s p'.2).val O * pbT m₁ (L.g (p'.2 1) (h₁.j p'.1)).val O) * hv +
    ((res hj' ((LB.LinComb L ![m, m₁] ![1, -1]).g p.2 p'.2)).val * rsT (e.s p'.2).val O) * coc2 -
    pbT m₁ (L.g (p.2 1) (h₁.j p'.1)).val O * g1 - rsT (e.s p.2).val O * coc1

end GlobalTheory.Heat.Gauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedChartFunctionEqGaugePowerMul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

theorem chart_fn_mul_gen_pow : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), L.IsLB → e.IsGen → ∀ (k : ℕ) (σ : SecM m₁ L k) (ρ : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → ∀ (p : h₁.J × (Fin 2 → L.ι)), rsT (ρ.f fun _ => p.2 0) (GlobalTheory.Heat.Gauge.W m h₁ p) = (GlobalTheory.Heat.Gauge.gU m h₁ e p).val ^ k * rsT (σ.f fun _ => h₁.j p.1) (GlobalTheory.Heat.Gauge.W m h₁ p) := by
  intro R _ G _ _ n X m m₁ L dd D h₁ e hL he k σ ρ hρ p
  have le₀ : W m h₁ p ≤ LB.wchart L (K := Fin 1) (fun _ => m) (fun _ => p.2 0) :=
    fun y hy => Set.mem_iInter.2 fun _ => W_le_m m h₁ p hy
  have le₁ : W m h₁ p ≤ LB.wchart L (K := Fin 1) (fun _ => m₁) (fun _ => h₁.j p.1) :=
    fun y hy => Set.mem_iInter.2 fun _ => (W_le_m₁ m h₁ p hy).2
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : G.left ⟶ X => exists_chart hL (χ y)
  have hJ' : Good L y J := hJ
  have hy' : (𝟙 G.left : G.left ⟶ G.left) y ∈ W m h₁ p := hy
  have e₀ : gs (𝟙 G.left) y _ (rsT (ρ.f fun _ => p.2 0) (W m h₁ p)) =
      (trF (fun _ : Fin 1 => m) (fun _ => (k : ℤ)) (𝟙 G.left) y (fun _ => p.2 0) (fun _ => J (𝟙 G.left ≫ m))).val *
        sval ρ (𝟙 G.left) y J :=
    (congrArg (gs (𝟙 G.left) y _) (GlobalTheory.KS.rsT_of_le le₀ _)).trans ((gs_res (𝟙 G.left) y le₀ hy' _).trans
      (sec_trans ρ (𝟙 G.left) y (le₀ hy) (hJ'.mem _ (𝟙 G.left))))
  have e₁ : gs (𝟙 G.left) y _ (rsT (σ.f fun _ => h₁.j p.1) (W m h₁ p)) =
      (trF (fun _ : Fin 1 => m₁) (fun _ => (k : ℤ)) (𝟙 G.left) y (fun _ => h₁.j p.1) (fun _ => J (𝟙 G.left ≫ m₁))).val *
        sval σ (𝟙 G.left) y J :=
    (congrArg (gs (𝟙 G.left) y _) (GlobalTheory.KS.rsT_of_le le₁ _)).trans ((gs_res (𝟙 G.left) y le₁ hy' _).trans
      (sec_trans σ (𝟙 G.left) y (le₁ hy) (hJ'.mem _ (𝟙 G.left))))
  have e₂ : gm (𝟙 G.left) y _ (gU m h₁ e p) =
      (trF ![m, m₁] ![1, -1] (𝟙 G.left) y p.2 (fun a => J (𝟙 G.left ≫ ![m, m₁] a)) * val e (𝟙 G.left) y J) *
        gm (𝟙 G.left ≫ m₁) y _ (L.g (p.2 1) (h₁.j p.1)) :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 G.left) y (W_le_wchart m h₁ p) hy' _).trans
        (gen_trans he (𝟙 G.left) y (W_le_wchart m h₁ p hy) (hJ'.mem _ (𝟙 G.left))))
      ((gm_res (𝟙 G.left) y (W_le_m₁ m h₁ p) hy' _).trans (gm_pull (𝟙 G.left) m₁ y _ (W_le_m₁ m h₁ p hy) _)))
  have e₃ : gs (𝟙 G.left) y _ ((gU m h₁ e p).val ^ k) = (gm (𝟙 G.left) y _ (gU m h₁ e p) ^ k).val := by
    rw [← Units.val_pow_eq_pow_val, gs_unit _ _ _ hy', map_pow]
  have hc := gm_cocycle hL (𝟙 G.left ≫ m₁) y (W_le_m₁ m h₁ p hy).1 (W_le_m₁ m h₁ p hy).2 (hJ (𝟙 G.left ≫ m₁))
  rw [gs_mul _ _ _ hy', e₀, e₁, e₃, e₂, hρ _ _ y J hJ', ← _root_.mul_assoc, ← _root_.mul_assoc, mul_right_comm, ← Units.val_mul,
    ← Units.val_mul]
  congr 2
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_natCast,
    zpow_one, zpow_neg]
  rw [← mul_pow, ← mul_pow]
  congr 1
  rw [_root_.mul_assoc _ (gm _ _ _ (L.g (p.2 1) _)), hc]
  rw [mul_right_comm _ (val e _ y J)]
  exact congrArg (· * val e _ y J) (inv_mul_cancel_right _ _).symm

end GlobalTheory.Heat.Gauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreInvariantVectorFieldsAtGenericPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_invariant_vectorFields_at_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) → ξ ≫ P.A.A.hom = spMap ψ → ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' → (∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∃ (v : Module.Basis (Fin n) (FractionRing R) (TanM (𝟙 (Sp (FractionRing R))) P.A.A)) (dd : Fin n → Fld P.A.A.left), (∀ a, IsInv P.A.A (v a) (dd a)) ∧ ∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δL a (valR ξ O f) := by
  first | exact @GlobalTheory.GenFields.main | exact GlobalTheory.GenFields.main | (intros; apply GlobalTheory.GenFields.main <;> assumption)
end

