import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittEmbeddingsCompatible
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalFactorsOfParahoricVectorTwoBlockProduct
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ParahoricSph

open Matrix

section Contract

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

lemma rid_lTensor_map (φ : W →ₗ[ℂ] ℂ) (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) (y : V ⊗[ℂ] W) :
    TensorProduct.rid ℂ V (φ.lTensor V (TensorProduct.map A B y)) =
      A (TensorProduct.rid ℂ V ((φ ∘ₗ B).lTensor V y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add y z hy hz => simp only [map_add, hy, hz]

lemma lid_rTensor_map (ψ : V →ₗ[ℂ] ℂ) (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) (y : V ⊗[ℂ] W) :
    TensorProduct.lid ℂ W (ψ.rTensor W (TensorProduct.map A B y)) =
      B (TensorProduct.lid ℂ W ((ψ ∘ₗ A).rTensor W y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add y z hy hz => simp only [map_add, hy, hz]

lemma exists_rid_ne_zero {x : V ⊗[ℂ] W} (hx : x ≠ 0) :
    ∃ φ : W →ₗ[ℂ] ℂ, TensorProduct.rid ℂ V (φ.lTensor V x) ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have he : e x ≠ 0 := by
    intro h; exact hx (e.injective (by rw [h, map_zero]))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he
  refine ⟨b.coord i, ?_⟩
  have key : ∀ w : V ⊗[ℂ] W, TensorProduct.rid ℂ V ((b.coord i).lTensor V w) = e w i := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v y => simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add y z hy hz => simp only [map_add, hy, hz, Finsupp.add_apply]
  rw [key]; simpa using hi

lemma exists_lid_ne_zero {x : V ⊗[ℂ] W} (hx : x ≠ 0) :
    ∃ ψ : V →ₗ[ℂ] ℂ, TensorProduct.lid ℂ W (ψ.rTensor W x) ≠ 0 := by
  have hc : TensorProduct.comm ℂ V W x ≠ 0 := fun h =>
    hx ((TensorProduct.comm ℂ V W).injective (by rw [h, map_zero]))
  obtain ⟨ψ, hψ⟩ := exists_rid_ne_zero hc
  refine ⟨ψ, ?_⟩
  have key : ∀ y : V ⊗[ℂ] W, TensorProduct.lid ℂ W (ψ.rTensor W y) =
      TensorProduct.rid ℂ W (ψ.lTensor W (TensorProduct.comm ℂ V W y)) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [key]; exact hψ

end Contract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_det_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {g : GL n k}
    (hg : g ∈ KO k n) : valuation k ((GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  obtain ⟨g, rfl⟩ := hg
  have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem emb₂_mem_KO {r t : ℕ} {m₁ : GL (Fin r) k} {m₂ : GL (Fin t) k} (h₁ : m₁ ∈ KO k (Fin r))
    (h₂ : m₂ ∈ KO k (Fin t)) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂) ∈ KO k (Fin (r + t)) := by
  obtain ⟨g₁, rfl⟩ := h₁
  obtain ⟨g₂, rfl⟩ := h₂
  refine ⟨emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (g₁, g₂), ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective i
  obtain ⟨j, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective j
  have hv := val_emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (g₁, g₂)
  have hw := val_emb₂ k (stdSum (rfl : r + t = r + t)) (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₁, GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₂)
  show algebraMap 𝒪[k] k ((emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (g₁, g₂)).val _ _) = _
  rw [hv, hw]
  rcases i with i | i <;> rcases j with j | j <;> simp [GeneralLinearGroup.map]

theorem extTensor_apply_eq {r t : ℕ} {χ : kˣ →* ℂˣ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ₁ : Representation ℂ (GL (Fin r) k) V}
    {σ₂ : Representation ℂ (GL (Fin t) k) W} {f : _} (hf : IsParahoricVec χ (prod₂ σ₁ σ₂) f)
    {m₁ : GL (Fin r) k} {m₂ : GL (Fin t) k} (h₁ : m₁ ∈ KO k (Fin r)) (h₂ : m₂ ∈ KO k (Fin t)) :
    extTensor σ₁ σ₂ (m₁, m₂) (f.1.1 1) = (χ (GeneralLinearGroup.det m₂) : ℂ) • f.1.1 1 := by
  have hmem := emb₂_mem_KO h₁ h₂
  have hv := val_emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)
  have hll : ∀ (i : Fin t) (j : Fin r),
      valuation k ((emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val (Fin.natAdd r i) (Fin.castAdd t j)) < 1 := by
    intro i j
    have h0 : (emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
      have hi : Fin.natAdd r i = (stdSum (rfl : r + t = r + t)) (Sum.inr i) := by ext; simp
      have hj : Fin.castAdd t j = (stdSum (rfl : r + t = r + t)) (Sum.inl j) := by ext; simp
      rw [hv, hi, hj]
      simp
    rw [h0, map_zero]
    exact zero_lt_one
  have hdet : ((GeneralLinearGroup.det m₂ : kˣ) : k) =
      ((emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    have hs : (emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val.submatrix (Fin.natAdd r) (Fin.natAdd r) = m₂.val := by
      ext i j
      have hi : Fin.natAdd r i = (stdSum (rfl : r + t = r + t)) (Sum.inr i) := by ext; simp
      have hj : Fin.natAdd r j = (stdSum (rfl : r + t = r + t)) (Sum.inr j) := by ext; simp
      rw [submatrix_apply, hv, hi, hj]
      simp
    rw [hs]
    rfl
  have H := congrArg (fun F => F.1.1 (1 : GL (Fin (r + t)) k)) (hf _ hmem hll _ hdet)
  let p : parab k (two (stdSum (rfl : r + t = r + t))) := ⟨leviEmb k (two (stdSum (rfl : r + t = r + t))) (leviTwo k (Fin r) (Fin t) (m₁, m₂)),
    leviEmb_mem_parab k (two (stdSum (rfl : r + t = r + t))) _⟩
  have H2 := parInd_law (two (stdSum (rfl : r + t = r + t)))
    ((extTensor σ₁ σ₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) f p 1
  have hδ : (deltaHalf k (Two (Fin r) (Fin t)) (leviTwo k (Fin r) (Fin t) (m₁, m₂)) : ℂ) = 1 := by
    rw [deltaHalf_two, isUnram_absPow k _ _ (valuation_det_of_mem_KO h₁),
      isUnram_absPow k _ _ (valuation_det_of_mem_KO h₂), mul_one, Units.val_one]
  rw [leviProj_leviEmb, hδ, one_smul] at H2
  have E1 : f.1.1 ((p : GL (Fin (r + t)) k) * 1) = f.1.1 (1 * emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)) := by
    rw [mul_one, one_mul]; rfl
  rw [E1] at H2
  change f.1.1 (1 * emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)) = (χ _ : ℂ) • f.1.1 1 at H
  rw [H] at H2
  rw [H2]
  simp

theorem isSpherical_of_isParahoricVec : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V)
    (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), IsParahoricVec χ (prod₂ σ₁ σ₂) f →
    f.1.1 1 ≠ 0 → IsSpherical σ₁ ∧ IsSpherical (twist σ₂ (detChar (Fin t) χ⁻¹)) := by
  intro k _ _ _ _ r t χ V _ _ W _ _ σ₁ σ₂ f hf h0
  constructor
  · obtain ⟨φ, hφ⟩ := exists_rid_ne_zero h0
    refine (Submodule.ne_bot_iff _).2 ⟨_, ?_, hφ⟩
    rintro ⟨m, hm⟩
    have H := extTensor_apply_eq hf hm (one_mem (KO k (Fin t)))
    change TensorProduct.map (σ₁ m) (σ₂ 1) (f.1.1 1) = _ at H
    show σ₁ m _ = ((1 : KO k (Fin r) →* ℂˣ) ⟨m, hm⟩ : ℂ) • _
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    have H' := congrArg (fun y => TensorProduct.rid ℂ V (φ.lTensor V y)) H
    rw [rid_lTensor_map] at H'
    simpa [Module.End.one_eq_id] using H'
  · obtain ⟨ψ, hψ⟩ := exists_lid_ne_zero h0
    refine (Submodule.ne_bot_iff _).2 ⟨_, ?_, hψ⟩
    rintro ⟨m, hm⟩
    have H := extTensor_apply_eq hf (one_mem (KO k (Fin r))) hm
    change TensorProduct.map (σ₁ 1) (σ₂ m) (f.1.1 1) = _ at H
    show twist σ₂ (detChar (Fin t) χ⁻¹) m _ = ((1 : KO k (Fin t) →* ℂˣ) ⟨m, hm⟩ : ℂ) • _
    rw [MonoidHom.one_apply, Units.val_one, one_smul, twist_apply]
    have H' := congrArg (fun y => TensorProduct.lid ℂ W (ψ.rTensor W y)) H
    rw [lid_rTensor_map] at H'
    simp [Module.End.one_eq_id] at H'
    rw [H', smul_smul, ← Units.val_mul]
    simp

end GlobalTheory.ParahoricSph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumAltSignRange
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwV.Xc

theorem sum_alt_sign_range (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), (if i % 2 = 1 then (-1 : ℤ) else 1) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    simp [h1, h2]

theorem sum_alt_sign_pos (n' : ℕ) (hn : Even n') :
    ∑ s : Fin n', (if IsOddPos s then (-1 : ℤ) else 1) = 0 := by
  obtain ⟨m, rfl⟩ := hn
  calc (∑ s : Fin (m + m), (if IsOddPos s then (-1 : ℤ) else 1))
        = ∑ i ∈ Finset.range (m + m), (if i % 2 = 1 then (-1 : ℤ) else 1) := by
          rw [← Fin.sum_univ_eq_sum_range]; rfl
    _ = 0 := by simpa [two_mul] using sum_alt_sign_range m

theorem vm_eq_of_shift (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (l : ℕ) (e : Fin (X.G.P.n' v) → ℤ) (k : ℤ)
    (hk : ∀ s, X.w v l s = e s - k) :
    X.vm v l = ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e s := by
  have hw : ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * X.w v l s = X.vm v l := by
    unfold Sys.vm
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : IsOddPos s <;> simp [h]
  rw [← hw]
  have e1 : ∀ s, (if IsOddPos s then (-1 : ℤ) else 1) * X.w v l s =
      (if IsOddPos s then -1 else 1) * e s - (if IsOddPos s then (-1 : ℤ) else 1) * k := by
    intro s; rw [hk s]; ring
  rw [Finset.sum_congr rfl (fun s _ => e1 s), Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_alt_sign_pos _ (X.G.P.setting v).even, zero_mul, sub_zero]

theorem vm_shift_cancels : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (l : ℕ) (e : Fin (X.G.P.n' v) → ℤ) (k : ℤ),
    (∀ s, X.w v l s = e s - k) → X.vm v l = ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e s :=
  fun p _ X v l e k hk => vm_eq_of_shift p X v l e k hk

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriTorusCharVectorOfParahoricDetCharVect
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

noncomputable section

namespace GlobalTheory.TameParahoric

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_val_lt (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem val_det_sub_one_lt {m : Type} [Fintype m] [LinearOrder m] (A : Matrix m m 𝒪[k])
    (hl : ∀ i j, j < i → valuation k (algebraMap 𝒪[k] k (A i j)) < 1)
    (hd : ∀ i, valuation k (algebraMap 𝒪[k] k (A i i) - 1) < 1) :
    valuation k ((A.map (algebraMap 𝒪[k] k)).det - 1) < 1 := by
  have h1 : (A.map (IsLocalRing.residue 𝒪[k])).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      have := (residue_eq_zero_iff_val_lt (A i i - 1)).2 (by simpa using hd i)
      rw [map_sub, map_one, sub_eq_zero] at this
      simpa using this
    · intro i j hij
      exact (residue_eq_zero_iff_val_lt _).2 (hl i j hij)
  have h2 : IsLocalRing.residue 𝒪[k] (A.det - 1) = 0 := by
    rw [map_sub, map_one, RingHom.map_det, sub_eq_zero]
    simpa using h1
  have := (residue_eq_zero_iff_val_lt _).1 h2
  rwa [map_sub, map_one, RingHom.map_det] at this

theorem isIwVec_of_isParahoricVec (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V) (hχ : IsTame χ) (hv : IsParahoricVec χ π v) :
    IsIwVec (Fin.append (fun _ : Fin r => (1 : kˣ →* ℂˣ)) (fun _ : Fin t => χ)) π v := by
  have hlt : ∀ (i : Fin t) (j : Fin r), Fin.castAdd t j < Fin.natAdd r i := by
    intro i j
    rw [Fin.lt_iff_val_lt_val]
    simp only [Fin.coe_castAdd, Fin.coe_natAdd]
    omega
  refine ⟨fun h hK hl hd => ?_, fun s hs => ?_⟩
  · obtain ⟨h₀, hh⟩ := hK
    have hval : ∀ i j, h.val i j = algebraMap 𝒪[k] k (h₀.val i j) := by
      intro i j
      rw [← hh]
      rfl
    have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) =
        (h₀.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).map (algebraMap 𝒪[k] k) := by
      ext i j
      simp [hval]
    have hdet : valuation k ((h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1) < 1 := by
      rw [hsub]
      refine val_det_sub_one_lt _ (fun i j hij => ?_) (fun i => ?_)
      · simpa [hval] using hl (Fin.natAdd r i) (Fin.natAdd r j) (by simpa using hij)
      · simpa [hval] using hd (Fin.natAdd r i)
    have hne : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hdet
      exact lt_irrefl _ hdet
    have hu : χ (Units.mk0 _ hne) = 1 := hχ _ (by simpa using hdet)
    rw [hv h ⟨h₀, hh⟩ (fun i j => hl _ _ (hlt i j)) (Units.mk0 _ hne) rfl, hu]
    simp
  · have hD : ((∏ j : Fin t, s (Fin.natAdd r j) : kˣ) : k) =
        ((diagT k (Fin (r + t)) s).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
      rw [val_diagT, Matrix.submatrix_diagonal _ _ (Fin.natAdd_injective _ _), Matrix.det_diagonal]
      simp [Units.coe_prod]
    have hlow : ∀ (i : Fin t) (j : Fin r),
        valuation k ((diagT k (Fin (r + t)) s).val (Fin.natAdd r i) (Fin.castAdd t j)) < 1 := by
      intro i j
      rw [val_diagT, Matrix.diagonal_apply_ne _ (hlt i j).ne']
      simp
    rw [hv _ (iwahori_le_KO k (Fin (r + t)) (diagT_mem_iwahori hs)) hlow _ hD]
    congr 2
    rw [torusChar_apply, Fin.prod_univ_add, map_prod]
    simp [Fin.append_left, Fin.append_right]

end GlobalTheory.TameParahoric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalDualPairSwapHermitianAdjointStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedLocalDualPair_swap_hermitianAdjoint : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω →
    GlobalTheory.Hk3.LocPair ϖ σ q (-δ) JT JS ψ
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)))
      (ω.comp (MulEquiv.prodComm : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) × Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) ≃* _).toMonoidHom) ∧
    (∀ s : M, GlobalTheory.Hk3.LocVac ρ s → GlobalTheory.Hk3.LocVac
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L))) s) ∧
    ∀ s : M, Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n') L =>
      ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)) s) = ⊤ := by
  first | exact @GlobalTheory.Hk3.HoweSwap.locPair_swap | exact GlobalTheory.Hk3.HoweSwap.locPair_swap | (intros; apply GlobalTheory.Hk3.HoweSwap.locPair_swap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VEqKZeroOfNormOne
section
noncomputable section

namespace GlobalTheory.UnitK

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem vEqK_zero_of_norm_one : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (x : X.G.Kf), ‖E.iK x‖ = 1 → X.vEqK x 0 := by
  intro p _ X hfr E x hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨N, hN⟩ := Formalism.MainNotions.FormalGroupSystem.Pf.exists_rep X hfr hx0

  have hint : ∀ y : X.G.Kf, ‖E.iK y‖ = 1 → y ∈ X.intK := fun y hy =>
    (E.mem_iff y).1 (by rw [mem_OcC]; exact hy.le)
  have h1 : X.vGeK x 0 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_zero_iff X).2 (hint x hx)
  have h2 : X.vGeK x⁻¹ 0 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_zero_iff X).2 (hint x⁻¹ (by rw [map_inv₀, norm_inv, hx, inv_one]))
  have hN1 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_iff_of_rep X hfr hN 0).1 h1
  have hN2 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_iff_of_rep X hfr (Formalism.MainNotions.FormalGroupSystem.Pf.Rep.inv X hN) 0).1 h2
  simp only [zero_mul] at hN1 hN2
  have hN0 : N = 0 := by
    have a : (0 : ℤ) ≤ N := by exact_mod_cast hN1
    have b : (0 : ℤ) ≤ -N := by exact_mod_cast hN2
    omega

  have he : 0 < X.eO := by
    rcases Nat.eq_zero_or_pos X.eO with h0 | h0
    · exfalso
      obtain ⟨u, hu⟩ := X.eO_spec
      rw [h0, pow_zero] at hu

      have hpu : IsUnit (p : X.G.O) := by
        exact IsUnit.of_mul_eq_one _ hu
      obtain ⟨w, hw⟩ := hpu.exists_right_inv
      have hb := E.int w
      have hmul : E.iK (algebraMap X.G.O X.G.Kf (p : X.G.O)) * E.iK (algebraMap X.G.O X.G.Kf w) = 1 := by
        rw [← map_mul, ← map_mul, hw, map_one, map_one]
      have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
        have : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
        rw [this, norm_algebraMap', Padic.norm_p]
      rw [map_natCast, map_natCast] at hmul
      have hn2 := congrArg norm hmul
      rw [norm_mul, norm_one, hn] at hn2
      have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      have hp0 : (0 : ℝ) < p := by linarith
      have : ‖E.iK (algebraMap X.G.O X.G.Kf w)‖ = p := by
        field_simp at hn2
        linarith
      linarith
    · exact h0
  exact (Formalism.MainNotions.FormalGroupSystem.Pf.vEqK_iff_of_rep X hfr hN 0).2 ⟨he, by simp [hN0]⟩

end GlobalTheory.UnitK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumTranslateRelationMapPreservingVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem locVac_rel_map : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ φ : M →ₗ[ℂ] M, (∀ s, LocVac ρ s → LocVac ρ (φ s)) → ∀ f : Matrix (Fin n') (Fin n) L →₀ M, (∀ x, LocVac ρ (f x)) → (f.sum fun x m => ρ x m) = 0 → (f.sum fun x m => ρ x (φ m)) = 0 := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP φ hφ f hf hsum
  classical
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hshift : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) t = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x t := by
    intro t ht x u hu
    have h1 : ρ x t = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) t := by
      have := congrArg (fun f => f t) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [ht u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x t) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x t := by
    intro t ht x u hu
    have := congrArg (fun f => f t) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift t ht x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  have hdist : ∀ x y : Matrix (Fin n') (Fin n) L, (∀ u ∈ intMatSub (L := L) n n',
      ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) = ψ (locH σ δ JS JT u y + σ (locH σ δ JS JT u y))) →
      x - y ∈ intMatSub (L := L) n n' := by
    intro x y hxy
    refine intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne (x - y) (fun u hu => ?_)
    have e : locH σ δ JS JT u (x - y) + σ (locH σ δ JS JT u (x - y)) =
        (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) + -(locH σ δ JS JT u y + σ (locH σ δ JS JT u y)) := by
      rw [locH_sub_right, map_sub]; ring
    rw [e, AddChar.map_add_eq_mul, hxy u hu, hψinv]

  have hinj : ∀ x t, ρ x t = 0 → t = 0 := by
    intro x t h0
    have := congrArg (fun f => f t) (hρ (-x) x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, h0, map_zero, neg_add_cancel, hρ0,
      Module.End.one_apply] at this
    have hne : ψ ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2) ≠ 0 := by
      intro h; have := hψinv ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2); rw [h, zero_mul] at this
      exact zero_ne_one this
    exact (smul_eq_zero.mp this.symm).resolve_left hne

  set Λ := intMatSub (L := L) n n' with hΛ
  have hmem : ∀ x : Matrix (Fin n') (Fin n) L, -(QuotientAddGroup.mk x : _ ⧸ Λ).out + x ∈ Λ := by
    intro x
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  set κ : Matrix (Fin n') (Fin n) L → ℂ := fun x =>
    ψ (-((locH σ δ JS JT (QuotientAddGroup.mk x : _ ⧸ Λ).out (-(QuotientAddGroup.mk x : _ ⧸ Λ).out + x) +
      σ (locH σ δ JS JT (QuotientAddGroup.mk x : _ ⧸ Λ).out (-(QuotientAddGroup.mk x : _ ⧸ Λ).out + x))) / 2)) with hκ
  have hdec1 : ∀ t, LocVac ρ t → ∀ x, ρ x t = κ x • ρ (QuotientAddGroup.mk x : _ ⧸ Λ).out t := by
    intro t ht x
    have := hshift t ht (QuotientAddGroup.mk x : _ ⧸ Λ).out _ (hmem x)
    rwa [add_neg_cancel_left] at this
  set I : Finset (Matrix (Fin n') (Fin n) L ⧸ Λ) := f.support.image (fun x => (QuotientAddGroup.mk x : _ ⧸ Λ)) with hI

  let cl : (Matrix (Fin n') (Fin n) L → M) → (Matrix (Fin n') (Fin n) L ⧸ Λ) → M := fun g y =>
    ∑ x ∈ f.support with (QuotientAddGroup.mk x : _ ⧸ Λ) = y, κ x • g x
  have hdec : ∀ g : Matrix (Fin n') (Fin n) L → M, (∀ x, LocVac ρ (g x)) →
      ∑ x ∈ f.support, ρ x (g x) = ∑ y ∈ I, ρ y.out (cl g y) := by
    intro g hg
    have e1 : ∑ x ∈ f.support, ρ x (g x) =
        ∑ x ∈ f.support, κ x • ρ (QuotientAddGroup.mk x : _ ⧸ Λ).out (g x) :=
      Finset.sum_congr rfl fun x _ => hdec1 _ (hg x) x
    rw [e1, ← Finset.sum_fiberwise_of_maps_to (s := f.support) (t := I) (g := fun x => (QuotientAddGroup.mk x : _ ⧸ Λ))
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [cl, map_sum, map_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2]
  have hclvac : ∀ y, LocVac ρ (cl f y) := by
    intro y u hu
    simp only [cl, map_sum, map_smul]
    exact Finset.sum_congr rfl fun x _ => by rw [hf x u hu]

  have hcl0 : ∀ y ∈ I, cl f y = 0 := by
    intro y hy
    have hsum' : ∑ y ∈ I, ρ y.out (cl f y) = 0 := by
      rw [← hdec f hf]; exact hsum
    have hind := GlobalTheory.joint_eigenvectors_eq_zero_of_sum_eq_zero Λ (Matrix (Fin n') (Fin n) L ⧸ Λ) M
      (fun u : Λ => ρ (u : Matrix (Fin n') (Fin n) L))
      (fun (y : Matrix (Fin n') (Fin n) L ⧸ Λ) (u : Λ) =>
        ψ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out + σ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out)))
      (fun y => ρ y.out (cl f y)) I (fun y _ u => heig _ (hclvac y) y.out u u.2)
      (by
        intro y _ y' _ hyy
        have hm := hdist y.out y'.out (fun u hu => congrFun hyy ⟨u, hu⟩)
        rw [← QuotientAddGroup.out_eq' y, ← QuotientAddGroup.out_eq' y', QuotientAddGroup.eq_iff_sub_mem]
        exact hm)
      hsum' y hy
    exact hinj _ _ hind
  have hφcl : ∀ y, cl (fun x => φ (f x)) y = φ (cl f y) := by
    intro y
    simp only [cl, map_sum, map_smul]
  show ∑ x ∈ f.support, ρ x (φ (f x)) = 0
  rw [hdec (fun x => φ (f x)) (fun x => hφ _ (hf x))]
  exact Finset.sum_eq_zero fun y hy => by rw [hφcl, hcl0 y hy, map_zero, map_zero]

end GlobalTheory.Hk3
end

