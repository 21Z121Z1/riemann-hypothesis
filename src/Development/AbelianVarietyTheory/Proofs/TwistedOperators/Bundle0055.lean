import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbXMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulMemOfHatCosetIndNeZero
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.StepData

open MeasureTheory ValuativeRel Matrix in
private theorem sigmaCompactSpace_of_isNonarchimedeanLocalField' (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : SigmaCompactSpace k := by
  obtain ⟨a, ha0, ha1⟩ := Valuation.RankOne.nontrivial (valuation k)
  obtain ⟨b, hb0, hb1⟩ : ∃ b : k, valuation k b ≠ 0 ∧ valuation k b < 1 := by
    rcases lt_or_gt_of_ne ha1 with h | h
    · exact ⟨a, ha0, h⟩
    · refine ⟨a⁻¹, by simpa using ha0, ?_⟩
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ h
  have hb : b ≠ 0 := by
    intro h
    simp [h] at hb0
  refine ⟨⟨fun m : ℕ => (fun x => (b ^ m)⁻¹ * x) '' (𝒪[k] : Set k),
    fun m => (_root_.GlobalTheory.SplitWeil.isCompact_int k).image (continuous_const.mul continuous_id), ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  set S := (IsRankLeOne.nonempty (R := k)).some
  have hf := S.strictMono
  obtain ⟨m, hm⟩ : ∃ m : ℕ, S.emb (valuation k b) ^ m * S.emb (valuation k x) ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, by simp⟩
    have hpos : 0 < S.emb (valuation k x) := by
      rw [← map_zero S.emb]
      exact hf (zero_lt_iff.2 (by simpa using hx))
    have hlt : S.emb (valuation k b) < 1 := by
      rw [← map_one S.emb]
      exact hf hb1
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hlt
    refine ⟨m, ?_⟩
    calc _ ≤ (S.emb (valuation k x))⁻¹ * S.emb (valuation k x) := by gcongr
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨m, b ^ m * x, ?_, by field_simp⟩
  rw [SetLike.mem_coe, Valuation.mem_integer_iff, ← hf.le_iff_le, map_one, map_mul, map_mul,
    map_pow, map_pow]
  exact hm

open MeasureTheory ValuativeRel Matrix in

theorem _root_.GlobalTheory.StepData.mul_mem_of_hat_cosetInd_ne_zero : ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ψ : AddChar k Circle) (_ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : kˣ) (ε : k)
    (yb : (n → k) ⧸ _root_.GlobalTheory.StepData.box n c) (η : n → k),
    _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb) η ≠ 0 →
    ∀ i, ε * η i * (c : k) ∈ 𝒪[k] := by
  intro k _ _ _ _ _ _ ψ hψ ν _ n _ _ c ε yb η hne i
  haveI := sigmaCompactSpace_of_isNonarchimedeanLocalField' k
  by_contra hx
  obtain ⟨t, ht, hψt⟩ : ∃ t ∈ 𝒪[k], ψ (t * (ε * η i * c)) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hx (_root_.GlobalTheory.RootEx.Unram.mem_of_psi hψ h)
  have hvmem : Pi.single i ((c : k) * t) ∈ _root_.GlobalTheory.StepData.box n c := by
    show ∀ j, valuation k (Pi.single (M := fun _ => k) i ((c : k) * t) j) ≤ valuation k (c : k)
    intro j
    rcases eq_or_ne j i with rfl | hj
    · simp only [Pi.single_eq_same, map_mul]
      exact mul_le_of_le_one_right' ht
    · simp [Pi.single_eq_of_ne hj]
  apply hne
  unfold _root_.GlobalTheory.StepData.hat
  set g : (n → k) → ℂ := fun y => _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb y *
    (ψ (ε * η ⬝ᵥ y) : ℂ) with hg
  have hshift : ∀ y, g (y + Pi.single i ((c : k) * t)) = (ψ (t * (ε * η i * c)) : ℂ) * g y := by
    intro y
    have hind : _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb
        (y + Pi.single i ((c : k) * t)) =
          _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb y := by
      unfold _root_.GlobalTheory.StepData.cosetInd
      simp only [Set.indicator]
      have hq : Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n c)
          (y + Pi.single i ((c : k) * t)) = Submodule.Quotient.mk y := by
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hvmem, add_zero]
      have hv0 := (Submodule.Quotient.mk_eq_zero _).2 hvmem
      split_ifs with h₁ h₂ h₂
      · rfl
      · exact absurd (hq.symm.trans h₁) h₂
      · exact absurd (hq.trans h₂) h₁
      · rfl
    simp only [hg, hind, dotProduct_add, dotProduct_single, mul_add, AddChar.map_add_eq_mul,
      Circle.coe_mul]
    have hr : ε * (η i * ((c : k) * t)) = t * (ε * η i * c) := by ring
    rw [hr]
    ring
  have h1 := integral_add_right_eq_self (μ := Measure.pi fun _ : n => ν) g
    (Pi.single i ((c : k) * t))
  simp only [hshift, integral_const_mul] at h1
  have hne1 : (ψ (t * (ε * η i * c)) : ℂ) ≠ 1 := by
    intro h
    exact hψt (Circle.ext_iff.mpr (by simpa using h))
  have hzero : ((ψ (t * (ε * η i * c)) : ℂ) - 1) * (∫ y, g y ∂Measure.pi fun _ => ν) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 hzero).resolve_left (sub_ne_zero.2 hne1)

end GlobalTheory.StepData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseDisjointParahoricTorusDoubleCosetAntiton
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.CellDisjoint

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def reix {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m) :
    GL n k →* GL m k :=
  Units.map (Matrix.reindexAlgEquiv k k e).toAlgHom.toMonoidHom

theorem reix_val {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (g : GL n k) : (reix e g).1 = g.1.submatrix e.symm e.symm := rfl

theorem reix_mem_KO {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    {g : GL n k} (hg : g ∈ KO k n) : reix e g ∈ KO k m := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨Units.map (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] e).toAlgHom.toMonoidHom h, Units.ext ?_⟩
  ext i j
  rfl

theorem reix_torusElt {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (ϖ : kˣ) (f : n → ℤ) : reix e (torusElt k n ϖ f) = torusElt k m ϖ (f ∘ e.symm) := by
  ext1
  rw [reix_val, val_torusElt, val_torusElt, submatrix_diagonal_equiv]
  rfl

theorem perm_of_eq {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (a b : Fin N → ℤ)
    (x y : GL (Fin N) k) (hx : x ∈ KO k (Fin N)) (hy : y ∈ KO k (Fin N))
    (h : x * torusElt k (Fin N) ϖ a * y = torusElt k (Fin N) ϖ b) :
    List.Perm (List.ofFn a) (List.ofFn b) := by
  let σ := Tuple.sort (fun i => -a i)
  let τ := Tuple.sort (fun i => -b i)
  have ha : Antitone (a ∘ σ) := fun i j hij => by
    have := Tuple.monotone_sort (fun i => -a i) hij
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact this
  have hb : Antitone (b ∘ τ) := fun i j hij => by
    have := Tuple.monotone_sort (fun i => -b i) hij
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact this
  obtain ⟨S₁, h₁, e₁⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] σ.symm
  obtain ⟨S₂, h₂, e₂⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] σ
  obtain ⟨T₁, h₃, e₃⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] τ.symm
  obtain ⟨T₂, h₄, e₄⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] τ
  have hA : torusElt k (Fin N) ϖ a = S₁ * torusElt k (Fin N) ϖ (a ∘ σ) * S₂ := by
    ext1
    simp only [Units.val_mul, val_torusElt, e₁, e₂]
    exact Formalism.UG.P.cartan_diag_perm (fun i => (ϖ : k) ^ a i) σ
  have hB : torusElt k (Fin N) ϖ b = T₁ * torusElt k (Fin N) ϖ (b ∘ τ) * T₂ := by
    ext1
    simp only [Units.val_mul, val_torusElt, e₃, e₄]
    exact Formalism.UG.P.cartan_diag_perm (fun i => (ϖ : k) ^ b i) τ
  have E : (T₁⁻¹ * x * S₁) * torusElt k (Fin N) ϖ (a ∘ σ) * (S₂ * y * T₂⁻¹) =
      torusElt k (Fin N) ϖ (b ∘ τ) := by
    have h' : torusElt k (Fin N) ϖ (b ∘ τ) = T₁⁻¹ * torusElt k (Fin N) ϖ b * T₂⁻¹ := by
      rw [hB]; group
    rw [h', ← h, hA]; group
  have hab : a ∘ σ = b ∘ τ := by
    refine Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
      (hϖ ▸ uniformizer_lt_one) (a ∘ σ) (b ∘ τ) ha hb (T₁⁻¹ * x * S₁)
      (mul_mem (mul_mem (inv_mem h₃) hx) h₁) (S₂ * y * T₂⁻¹) (mul_mem (mul_mem h₂ hy) (inv_mem h₄)) ?_
    have := congrArg Units.val E
    simp only [Units.val_mul, val_torusElt] at this
    simpa only [Units.val_mul, Matrix.mul_assoc] using this
  exact (Equiv.Perm.ofFn_comp_perm σ a).symm.trans (hab ▸ Equiv.Perm.ofFn_comp_perm τ b)

end GlobalTheory.CellDisjoint

namespace GlobalTheory.CellDisjoint

theorem dcell_pairwise_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (r l t : ℕ),
    Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
      (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  intro k _ _ _ _ ϖ hϖ r l t a b hab
  refine Set.disjoint_left.2 fun g ha hb => hab (Subtype.ext ?_)
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 ha
  obtain ⟨x', hx', y', hy', e⟩ := DoubleCoset.mem_doubleCoset.1 hb
  have hK : ∀ z : GL (Fin r ⊕ Blocks l t) k, z ∈ (parahoric k (Fin r) (Blocks l t) : Set _) →
      z ∈ KO k (Fin r ⊕ Blocks l t) := fun z hz => (mem_parahoric.1 hz).1
  have e' : (x'⁻¹ * x) * mtor ϖ (a.1 ∘ (blkEquiv l t).symm) * (y * y'⁻¹) =
      mtor ϖ (b.1 ∘ (blkEquiv l t).symm) := by
    calc _ = x'⁻¹ * (x * mtor ϖ (a.1 ∘ (blkEquiv l t).symm) * y) * y'⁻¹ := by group
      _ = _ := by rw [e]; group
  let ρ : Fin (r + l * t) ≃ Fin r ⊕ Blocks l t :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin r)) (blkEquiv l t))
  have hρ : ∀ f : Fin (l * t) → ℤ,
      (Sum.elim (0 : Fin r → ℤ) (f ∘ (blkEquiv l t).symm)) ∘ ρ.symm.symm = Fin.append (0 : Fin r → ℤ) f := by
    intro f
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [ρ]
    · simp [ρ]
  have e'' := congrArg (reix (k := k) ρ.symm) e'
  simp only [map_mul, mtor, reix_torusElt, hρ] at e''
  have hp := perm_of_eq hϖ _ _ _ _ (mul_mem (reix_mem_KO _ (inv_mem (hK _ hx'))) (reix_mem_KO _ (hK _ hx)))
    (mul_mem (reix_mem_KO _ (hK _ hy)) (reix_mem_KO _ (inv_mem (hK _ hy')))) e''
  rw [List.ofFn_fin_append, List.ofFn_fin_append, List.perm_append_left_iff] at hp
  exact List.ofFn_injective (List.Perm.eq_of_sortedGE (List.sortedGE_ofFn_iff.2 a.2)
    (List.sortedGE_ofFn_iff.2 b.2) hp)

end GlobalTheory.CellDisjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoric
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.DatumEigen

variable {k : Type} [Field k] [ValuativeRel k]

theorem val_det_sub_lt {m : Type} [Fintype m] [DecidableEq m] {M N : Matrix m m k}
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hN : ∀ i j, N i j ∈ 𝒪[k]) (h : ∀ i j, valuation k (M i j - N i j) < 1) :
    valuation k (M.det - N.det) < 1 := by
  have key : ∀ x : 𝒪[k], IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩
  let M' : Matrix m m 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  let N' : Matrix m m 𝒪[k] := fun i j => ⟨N i j, hN i j⟩
  have eM : M = (algebraMap 𝒪[k] k).mapMatrix M' := rfl
  have eN : N = (algebraMap 𝒪[k] k).mapMatrix N' := rfl
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix M' = (IsLocalRing.residue 𝒪[k]).mapMatrix N' := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, key]
    exact h i j
  rw [eM, eN, ← RingHom.map_det, ← RingHom.map_det, ← map_sub, ← key, map_sub, RingHom.map_det,
    RingHom.map_det, hres, sub_self]

theorem val_mul_lt {a b : k} (ha : valuation k a ≤ 1) (hb : valuation k b < 1) : valuation k (a * b) < 1 := by
  rw [map_mul]
  exact (mul_le_of_le_one_left' ha).trans_lt hb

theorem det_int {m : Type} [Fintype m] [DecidableEq m] {M : Matrix m m k} (hM : ∀ i j, M i j ∈ 𝒪[k]) :
    M.det ∈ 𝒪[k] := by
  let M' : Matrix m m 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  have eM : M = (algebraMap 𝒪[k] k).mapMatrix M' := rfl
  rw [eM, ← RingHom.map_det]
  exact (M'.det).2

theorem eq_one_of_mul {a b : ValueGroupWithZero k} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  by_contra hlt
  replace hlt := not_le.1 hlt
  have : a * b < 1 := (mul_le_of_le_one_right' hb).trans_lt hlt
  exact this.ne h

theorem tame_eq {ξ : kˣ →* ℂˣ} (hξ : IsTame ξ) {a b : kˣ} (hb : valuation k (b : k) = 1)
    (h : valuation k ((a : k) - b) < 1) : ξ a = ξ b := by
  have hb0 : (b : k) ≠ 0 := b.ne_zero
  have h1 : ξ (a * b⁻¹) = 1 := by
    apply hξ
    have e : ((a * b⁻¹ : kˣ) : k) - 1 = ((a : k) - b) * (b : k)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
    rw [e, map_mul, map_inv₀, hb, inv_one, mul_one]
    exact h
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Blocks

variable {A D E : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem int_of_mem {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) (i l : A ⊕ D) : j.val i l ∈ 𝒪[k] :=
  ((GlobalTheory.SplitFlip.mem_KO_iff j).1 (mem_parahoric.1 hj).1).1 i l

theorem det_cong {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) :
    valuation k (j.val.det - j.val.toBlocks₁₁.det * j.val.toBlocks₂₂.det) < 1 := by
  have hJ := int_of_mem hj
  have hl := (mem_parahoric.1 hj).2
  rw [← det_fromBlocks_zero₂₁ j.val.toBlocks₁₁ j.val.toBlocks₁₂ j.val.toBlocks₂₂]
  refine val_det_sub_lt hJ ?_ ?_
  · rintro (i | i) (l | l) <;> simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₂, hJ]
  · rintro (i | i) (l | l) <;> simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₂, hl]

theorem val_det_blocks {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) :
    valuation k j.val.toBlocks₁₁.det = 1 ∧ valuation k j.val.toBlocks₂₂.det = 1 := by
  have hJ := int_of_mem hj
  have h1 : valuation k j.val.det = 1 := by
    have := nabs_det_of_mem_KO (mem_parahoric.1 hj).1
    rwa [nabs_eq_one_iff] at this
  have h2 := Valuation.map_eq_of_sub_lt _ (show valuation k (j.val.toBlocks₁₁.det * j.val.toBlocks₂₂.det
      - j.val.det) < valuation k j.val.det by
    rw [h1, ← Valuation.map_neg, neg_sub]; exact det_cong hj)
  rw [h1, map_mul] at h2
  have i11 : valuation k j.val.toBlocks₁₁.det ≤ 1 := det_int fun i l => hJ _ _
  have i22 : valuation k j.val.toBlocks₂₂.det ≤ 1 := det_int fun i l => hJ _ _
  exact ⟨eq_one_of_mul i11 i22 h2, eq_one_of_mul i22 i11 (by rw [mul_comm]; exact h2)⟩

omit [Fintype E] [DecidableEq E] in

theorem inSupp_mul {x : Matrix (A ⊕ E) (A ⊕ D) k} (hx : InSupp x) {j : GL (A ⊕ D) k}
    (hj : j ∈ parahoric k A D) : InSupp (x * j.val) ∧
      valuation k ((x * j.val).toBlocks₁₁.det - x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1 := by
  have hJ := int_of_mem hj
  have hl := (mem_parahoric.1 hj).2
  obtain ⟨hxi, hxd, hxl⟩ := hx
  have hprod : ∀ i l, (x * j.val) i l ∈ 𝒪[k] := fun i l => by
    rw [mul_apply]; exact sum_mem fun m _ => mul_mem (hxi i m) (hJ m l)
  have hcong : valuation k ((x * j.val).toBlocks₁₁.det - x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1 := by
    rw [← det_mul]
    refine val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)
    · rw [mul_apply]; exact sum_mem fun m _ => mul_mem (hxi _ _) (hJ _ _)
    · simp only [toBlocks₁₁, of_apply, mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]
      exact Valuation.map_sum_lt _ one_ne_zero fun m _ => val_mul_lt (hxi _ _) (hl _ _)
  have hd1 : valuation k (x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) = 1 := by
    rw [map_mul, hxd, one_mul, (val_det_blocks hj).1]
  refine ⟨⟨hprod, ?_, ?_⟩, hcong⟩
  · rw [← hd1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd1]; exact hcong
  · intro e a
    rw [mul_apply, Fintype.sum_sum_type]
    refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
      (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
    · rw [mul_comm]; exact val_mul_lt (hJ _ _) (hxl _ _)
    · exact val_mul_lt (hxi _ _) (hl _ _)

end Blocks

theorem om_datum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ₀ : kˣ →* ℂˣ), IsTame ξ → IsUnram μ₀ →
    ∀ j ∈ parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    om (μ₀ * ξ) j (1 : GL (A ⊕ E) k) (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ) = fun x => (ξ d : ℂ) * datum ξ x := by
  intro k _ _ _ _ A D E _ _ _ _ _ _ ξ μ₀ hξ hμ j hj d hd
  funext x
  have hK := (mem_parahoric.1 hj).1
  have hdetv : valuation k (GeneralLinearGroup.det j : k) = 1 := (nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hK)
  have hμj : μ₀ (GeneralLinearGroup.det j) = 1 := hμ _ hdetv
  simp only [om, nabs_det_of_mem_KO hK, MonoidHom.mul_apply, hμj, one_mul, map_one, mul_one, inv_one,
    Units.val_one, Real.one_rpow, Complex.ofReal_one]
  rw [show nabs k 1 = 1 by simp [nabs], Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.one_mul]
  unfold datum
  obtain ⟨h11, h22⟩ := val_det_blocks hj
  by_cases hx : InSupp x
  · obtain ⟨hs, hc⟩ := inSupp_mul hx hj
    have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
    set u : kˣ := Units.mk0 _ n11 with hu
    have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
    have t1 : ξ (GeneralLinearGroup.det j) = ξ (u * d) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
      rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
      exact det_cong hj
    have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (Units.mk0 _ hx.det_ne * u) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, Units.val_mk0, hx.2.1, one_mul]; exact h11) ?_
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
      exact hc
    rw [dif_pos hs, dif_pos hx, t1, t2, map_mul, map_mul]
    simp only [Units.val_mul, _root_.mul_inv_rev, Units.val_inv_eq_inv_val]
    have a1 : (ξ u : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  · have hs : ¬ InSupp (x * j.val) := fun hs => by
      have := (inSupp_mul hs (inv_mem hj)).1
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
      exact hx this
    rw [dif_neg hs, dif_neg hx, mul_zero, mul_zero]

end GlobalTheory.DatumEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumTorusIntegrandEqIndicator
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.TorusIntegrand

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mtor_val {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    (mtor ϖ e : GL (A ⊕ D) k).val = diagonal (Sum.elim (fun _ => (1 : k)) (fun d => (ϖ : k) ^ e d)) := by
  unfold mtor
  rw [val_torusElt]
  congr 1
  funext i
  cases i <;> simp

theorem integral_and_iff (ϖ : kˣ) (hϖ : (ϖ : k) ∈ 𝒪[k]) (y : k) (n : ℤ) :
    (y ∈ 𝒪[k] ∧ y * (ϖ : k) ^ n ∈ 𝒪[k]) ↔ y * (ϖ : k) ^ (-max 0 (-n)) ∈ 𝒪[k] := by
  rcases le_or_gt 0 n with h | h
  · have h0 : -max 0 (-n) = 0 := by omega
    rw [h0, zpow_zero, mul_one]
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [zpow_natCast]
    exact ⟨fun h => h.1, fun hy => ⟨hy, Subring.mul_mem _ hy (Subring.pow_mem _ hϖ m)⟩⟩
  · have h0 : -max 0 (-n) = n := by omega
    rw [h0]
    refine ⟨fun h => h.2, fun hy => ⟨?_, hy⟩⟩
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -n by omega)
    have hne : (ϖ : k) ≠ 0 := ϖ.ne_zero
    have : y = y * (ϖ : k) ^ n * (ϖ : k) ^ m := by
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hne, ← hm, add_neg_cancel, zpow_zero, mul_one]
    rw [this]
    exact Subring.mul_mem _ hy (Subring.pow_mem _ hϖ m)

theorem integrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
    ∀ (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ : kˣ →* ℂˣ), IsUnitaryChar ξ → ∀ (e : D → ℤ) (x : Matrix (A ⊕ E) (A ⊕ D) k),
    datum ξ (x * (mtor ϖ e : GL (A ⊕ D) k).val) * starRingEnd ℂ (datum ξ x) =
      Set.indicator {y : Matrix (A ⊕ E) (A ⊕ D) k | InSupp (y * (mtor ϖ (fun i => -max 0 (-e i)) : GL (A ⊕ D) k).val)}
        (fun _ => (1 : ℂ)) x := by
  intro k _ _ _ _ ϖ hϖv A D E _ _ _ _ _ _ ξ hξ e x
  have hϖ : (ϖ : k) ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, hϖv]
    exact uniformizer_lt_one.le
  have hA : ∀ (M : Matrix (A ⊕ E) (A ⊕ D) k) (g : D → ℤ) i a,
      (M * (mtor ϖ g : GL (A ⊕ D) k).val) i (.inl a) = M i (.inl a) := by
    intro M g i a
    rw [mtor_val, mul_diagonal]
    simp
  have hD : ∀ (M : Matrix (A ⊕ E) (A ⊕ D) k) (g : D → ℤ) i d,
      (M * (mtor ϖ g : GL (A ⊕ D) k).val) i (.inr d) = M i (.inr d) * (ϖ : k) ^ g d := by
    intro M g i d
    rw [mtor_val, mul_diagonal]
    simp
  have h11 : ∀ (M : Matrix (A ⊕ E) (A ⊕ D) k) (g : D → ℤ),
      (M * (mtor ϖ g : GL (A ⊕ D) k).val).toBlocks₁₁ = M.toBlocks₁₁ := by
    intro M g
    ext i j
    simp [toBlocks₁₁, hA]
  have hsupp : ∀ M : Matrix (A ⊕ E) (A ⊕ D) k, InSupp M ↔
      (∀ i a, M i (.inl a) ∈ 𝒪[k]) ∧ (∀ i d, M i (.inr d) ∈ 𝒪[k]) ∧
        valuation k M.toBlocks₁₁.det = 1 ∧ ∀ i j, valuation k (M (.inr i) (.inl j)) < 1 := by
    intro M
    unfold InSupp
    simp only [Sum.forall, forall_and]
    tauto
  have hsuppm : ∀ (M : Matrix (A ⊕ E) (A ⊕ D) k) (g : D → ℤ), InSupp (M * (mtor ϖ g : GL (A ⊕ D) k).val) ↔
      (∀ i a, M i (.inl a) ∈ 𝒪[k]) ∧ (∀ i d, M i (.inr d) * (ϖ : k) ^ g d ∈ 𝒪[k]) ∧
        valuation k M.toBlocks₁₁.det = 1 ∧ ∀ i j, valuation k (M (.inr i) (.inl j)) < 1 := by
    intro M g
    rw [hsupp, h11]
    simp only [hA, hD]
  have hQ : ((∀ i d, x i (.inr d) ∈ 𝒪[k]) ∧ ∀ i d, x i (.inr d) * (ϖ : k) ^ e d ∈ 𝒪[k]) ↔
      ∀ i d, x i (.inr d) * (ϖ : k) ^ (-max 0 (-e d)) ∈ 𝒪[k] := by
    simp only [← forall_and]
    exact forall_congr' fun i => forall_congr' fun d => integral_and_iff ϖ hϖ _ _
  have hboth : (InSupp x ∧ InSupp (x * (mtor ϖ e : GL (A ⊕ D) k).val)) ↔
      InSupp (x * (mtor ϖ (fun i => -max 0 (-e i)) : GL (A ⊕ D) k).val) := by
    rw [hsupp, hsuppm, hsuppm, ← hQ]
    tauto
  set S := {y : Matrix (A ⊕ E) (A ⊕ D) k | InSupp (y * (mtor ϖ (fun i => -max 0 (-e i)) : GL (A ⊕ D) k).val)} with hS
  unfold datum
  by_cases h2 : InSupp x
  · by_cases h1 : InSupp (x * (mtor ϖ e : GL (A ⊕ D) k).val)
    · rw [dif_pos h1, dif_pos h2, Set.indicator_of_mem (show x ∈ S from hboth.1 ⟨h2, h1⟩)]
      have hu : Units.mk0 _ h1.det_ne = Units.mk0 _ h2.det_ne := by
        ext
        simp [h11]
      rw [hu, ← map_inv, Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ]
      simp
    · rw [dif_neg h1, Set.indicator_of_notMem (show x ∉ S from fun h => h1 (hboth.2 h).2)]
      simp
  · rw [dif_neg h2, Set.indicator_of_notMem (show x ∉ S from fun h => h2 (hboth.2 h).1)]
    simp

end GlobalTheory.TorusIntegrand
end
end

