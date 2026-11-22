import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1772
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormBaseChangeMatrixStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_base_change_matrix : ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S) {α α' β : Type} [Fintype α] [Fintype α'] [Fintype β]
    (JA : Matrix α α S) (JB : Matrix β β S) (P : Matrix α α' S) (z z' : Matrix α' β S),
    symp c ξ JA JB (P * z) (P * z') = symp c ξ (Pᵀ * JA * P.map c) JB z z' := by
  first | exact @GlobalTheory.symp_mul_left | exact GlobalTheory.symp_mul_left | (intros; apply GlobalTheory.symp_mul_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementary
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChangeGen

open Matrix GlobalTheory.SympChange

variable {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]

def upM (T : Matrix κ κ K) : Matrix (κ ⊕ κ) (κ ⊕ κ) K := fromBlocks 1 T 0 1

theorem weylM_mem : (weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inr rfl)

theorem leviM_mem (A : Matrix κ κ K) (h : IsUnit A.det) :
    leviM A ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inl (Or.inl ⟨A, h, rfl⟩))

theorem unipM_mem (S : Matrix κ κ K) (h : Sᵀ = S) :
    unipM S ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨S, h, rfl⟩))

theorem upM_eq (T : Matrix κ κ K) :
    upM T = weylM * unipM (-T) * (weylM * weylM * weylM) := by
  simp [upM, weylM, unipM, fromBlocks_multiply]

theorem upM_mem (T : Matrix κ κ K) (h : Tᵀ = T) :
    upM T ∈ Submonoid.closure (gens (F := K) (κ := κ)) := by
  rw [upM_eq]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ weylM_mem (unipM_mem _ (by rw [transpose_neg, h])))
    (Submonoid.mul_mem _ (Submonoid.mul_mem _ weylM_mem weylM_mem) weylM_mem)

theorem isSymp_mul {G H : Matrix (κ ⊕ κ) (κ ⊕ κ) K} (hG : IsSymp G) (hH : IsSymp H) :
    IsSymp (G * H) := by
  unfold IsSymp at *
  calc (G * H)ᵀ * weylM * (G * H) = Hᵀ * (Gᵀ * weylM * G) * H := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = weylM := by rw [hG, hH]

theorem isSymp_upM (T : Matrix κ κ K) (h : Tᵀ = T) : IsSymp (upM T) := by
  simp [IsSymp, upM, weylM, fromBlocks_transpose, fromBlocks_multiply, h]

theorem weyl_sq : (weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * weylM = -1 := by
  simp [weylM, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem exists_sym_isUnit (a c : Matrix κ κ K) (hs : aᵀ * c = cᵀ * a)
    (hinj : ∀ x, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0) :
    ∃ T : Matrix κ κ K, Tᵀ = T ∧ IsUnit (a + T * c).det := by
  classical
  let P : Finset κ → Prop := fun s => ∀ y, (∀ i ∉ s, (a *ᵥ y) i = 0) → a *ᵥ y = 0
  have hP0 : P ∅ := fun y hy => funext fun i => hy i (Finset.notMem_empty i)
  obtain ⟨s, hs_mem, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, hP0⟩⟩
  have hsP : P s := (Finset.mem_filter.1 hs_mem).2
  have key : ∀ z : κ → K, (∀ i ∈ s, z i = 0) → (∀ y, z ⬝ᵥ (a *ᵥ y) = 0) → z = 0 := by
    intro z hzs hzo
    funext j
    by_cases hj : j ∈ s
    · exact hzs j hj
    · have hnot : ¬ P (insert j s) := by
        intro hP'
        have := hmax (insert j s) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP'⟩)
        rw [Finset.card_insert_of_notMem hj] at this
        omega
      simp only [P, not_forall] at hnot
      obtain ⟨y, hy, hne⟩ := hnot
      have hvj : (a *ᵥ y) j ≠ 0 := by
        intro h0
        apply hne
        apply hsP y
        intro i hi
        by_cases hij : i = j
        · rw [hij]; exact h0
        · exact hy i (by simp [hij, hi])
      have hsum : z ⬝ᵥ (a *ᵥ y) = z j * (a *ᵥ y) j := by
        unfold dotProduct
        apply Finset.sum_eq_single j
        · intro i _ hij
          by_cases his : i ∈ s
          · rw [hzs i his, zero_mul]
          · rw [hy i (by simp [hij, his]), mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have h0 := hzo y
      rw [hsum] at h0
      exact (mul_eq_zero.1 h0).resolve_right hvj
  set T : Matrix κ κ K := diagonal fun i => if i ∈ s then 1 else 0 with hTdef
  have hTe : ∀ w : κ → K, ∀ i, (T *ᵥ w) i = (if i ∈ s then 1 else 0) * w i := fun w i => by
    simp [hTdef, mulVec_diagonal]
  have hx : ∀ x, (a + T * c) *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [add_mulVec, ← mulVec_mulVec] at hx
    have hx2 : ∀ i, (a *ᵥ x) i + (if i ∈ s then 1 else 0) * (c *ᵥ x) i = 0 := fun i => by
      rw [← hTe]; exact congrFun hx i
    have hax : a *ᵥ x = 0 := hsP x (fun i hi => by
      have := hx2 i
      rwa [if_neg hi, zero_mul, add_zero] at this)
    have hcs : ∀ i ∈ s, (c *ᵥ x) i = 0 := fun i hi => by
      have := hx2 i
      rwa [if_pos hi, one_mul, hax, Pi.zero_apply, zero_add] at this
    have horth : ∀ y, (c *ᵥ x) ⬝ᵥ (a *ᵥ y) = 0 := fun y => by
      calc (c *ᵥ x) ⬝ᵥ (a *ᵥ y) = x ⬝ᵥ ((cᵀ * a) *ᵥ y) := by
            rw [← mulVec_mulVec, dotProduct_mulVec x cᵀ, vecMul_transpose]
        _ = x ⬝ᵥ ((aᵀ * c) *ᵥ y) := by rw [hs]
        _ = (a *ᵥ x) ⬝ᵥ (c *ᵥ y) := by
            rw [← mulVec_mulVec, dotProduct_mulVec x aᵀ, vecMul_transpose]
        _ = 0 := by rw [hax, zero_dotProduct]
    exact hinj x hax (key _ hcs horth)
  refine ⟨T, by simp [hTdef], isUnit_iff_ne_zero.2 fun hdet => ?_⟩
  obtain ⟨v, hv, hmv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  exact hv (hx v hmv)

theorem symp_blocks {a b c d : Matrix κ κ K} (h : IsSymp (fromBlocks a b c d)) :
    aᵀ * c = cᵀ * a ∧ aᵀ * d = 1 + cᵀ * b ∧ bᵀ * d = dᵀ * b := by
  simp only [IsSymp, weylM, fromBlocks_transpose, fromBlocks_multiply] at h
  obtain ⟨h11, h12, -, h22⟩ := fromBlocks_inj.1 h
  simp at h11 h12 h22
  refine ⟨(neg_add_eq_zero.1 h11).symm, ?_, (neg_add_eq_zero.1 h22).symm⟩
  rw [← h12]; abel

theorem mem_of_isUnit {a b c d : Matrix κ κ K} (h : IsSymp (fromBlocks a b c d)) (ha : IsUnit a.det) :
    fromBlocks a b c d ∈ Submonoid.closure (gens (F := K) (κ := κ)) := by
  obtain ⟨e1, e2, e3⟩ := symp_blocks h
  have haa : a * a⁻¹ = 1 := mul_nonsing_inv a ha
  have hai : a⁻¹ * a = 1 := nonsing_inv_mul a ha
  have hT1 : a⁻¹ᵀ * aᵀ = 1 := by rw [← transpose_mul, haa, transpose_one]
  have hT2 : aᵀ * a⁻¹ᵀ = 1 := by rw [← transpose_mul, hai, transpose_one]
  set Y := c * a⁻¹ with hYdef
  have hY : Yᵀ = Y := by
    rw [hYdef, transpose_mul]
    calc a⁻¹ᵀ * cᵀ = a⁻¹ᵀ * cᵀ * (a * a⁻¹) := by rw [haa, Matrix.mul_one]
      _ = a⁻¹ᵀ * (cᵀ * a) * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = a⁻¹ᵀ * (aᵀ * c) * a⁻¹ := by rw [e1]
      _ = (a⁻¹ᵀ * aᵀ) * c * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = c * a⁻¹ := by rw [hT1, Matrix.one_mul]
  have hd : d = a⁻¹ᵀ + Y * b := by
    calc d = (a⁻¹ᵀ * aᵀ) * d := by rw [hT1, Matrix.one_mul]
      _ = a⁻¹ᵀ * (aᵀ * d) := by rw [Matrix.mul_assoc]
      _ = a⁻¹ᵀ + (a⁻¹ᵀ * cᵀ) * b := by rw [e2, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
      _ = a⁻¹ᵀ + Y * b := by rw [← transpose_mul, ← hYdef, hY]
  set X := a⁻¹ * b with hXdef
  have hX : Xᵀ = X := by
    have e3' := e3
    rw [hd, Matrix.mul_add, transpose_add, Matrix.add_mul, transpose_mul, hY, transpose_transpose] at e3'
    simp only [← Matrix.mul_assoc] at e3'
    rw [hXdef, transpose_mul]
    exact add_right_cancel e3'
  have hG : fromBlocks a b c d = unipM Y * leviM a * upM X := by
    simp only [unipM, leviM, upM, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
    congr 1
    · rw [hXdef, ← Matrix.mul_assoc, haa, Matrix.one_mul]
    · rw [hYdef, Matrix.mul_assoc, hai, Matrix.mul_one]
    · rw [hd, hXdef, hYdef, add_comm]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc a a⁻¹ b, haa, Matrix.one_mul]
  rw [hG]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (unipM_mem _ hY) (leviM_mem _ ha)) (upM_mem _ hX)

theorem mem_closure_gens : ∀ (K : Type) [Field K] [CharZero K] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix (κ ⊕ κ) (κ ⊕ κ) K),
    GlobalTheory.SympChange.IsSymp G → G ∈ Submonoid.closure (GlobalTheory.SympChange.gens (F := K) (κ := κ)) := by
  intro K _ _ κ _ _ G hG
  rw [← fromBlocks_toBlocks G] at hG ⊢
  set a := G.toBlocks₁₁
  set b := G.toBlocks₁₂
  set c := G.toBlocks₂₁
  set d := G.toBlocks₂₂
  obtain ⟨e1, -, -⟩ := symp_blocks hG

  have hL : (-(weylM * (fromBlocks a b c d)ᵀ * weylM)) * fromBlocks a b c d = 1 := by
    have h := hG
    unfold IsSymp at h
    have e : weylM * (fromBlocks a b c d)ᵀ * weylM * fromBlocks a b c d
        = weylM * ((fromBlocks a b c d)ᵀ * weylM * fromBlocks a b c d) := by simp only [Matrix.mul_assoc]
    rw [Matrix.neg_mul, e, h, weyl_sq, neg_neg]
  have hinj : ∀ x, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0 := by
    intro x hax hcx
    have hv : fromBlocks a b c d *ᵥ Sum.elim x 0 = 0 := by
      rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, hax, hcx, mulVec_zero, mulVec_zero]
      simp
    have h0 : Sum.elim x (0 : κ → K) = 0 := by
      rw [← Matrix.one_mulVec (Sum.elim x 0), ← hL, ← mulVec_mulVec, hv, mulVec_zero]
    funext i
    exact congrFun h0 (Sum.inl i)
  obtain ⟨T, hT, hu⟩ := exists_sym_isUnit a c e1 hinj
  have hH : upM T * fromBlocks a b c d = fromBlocks (a + T * c) (b + T * d) c d := by
    simp [upM, fromBlocks_multiply]
  have hHs : IsSymp (fromBlocks (a + T * c) (b + T * d) c d) := hH ▸ isSymp_mul (isSymp_upM T hT) hG
  have hinv : upM (-T) * upM T = (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) := by
    simp [upM, fromBlocks_multiply]
  have : fromBlocks a b c d = upM (-T) * fromBlocks (a + T * c) (b + T * d) c d := by
    rw [← hH, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  rw [this]
  exact Submonoid.mul_mem _ (upM_mem _ (by rw [transpose_neg, hT])) (mem_of_isUnit hHs hu)

end GlobalTheory.SympChangeGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedLeviLowerUnipotentWeyl
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

open private exists_symmetric_X_isUnit_det_add_mul_of_symplectic from Mathlib.LinearAlgebra.SymplecticGroup

namespace GlobalTheory.SpGen
open Matrix

theorem upper_unipotent_eq {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) :
    (fromBlocks 1 s 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 0 1 (-1) 0 * fromBlocks 1 0 (-s) 1 * fromBlocks 0 1 (-1) 0 *
        fromBlocks (-1) 0 0 (-1) := by
  simp [fromBlocks_multiply]

theorem symplectic_generated_levi_lower_weyl :
    ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] [DecidableEq κ] (P : Matrix (κ ⊕ κ) (κ ⊕ κ) K → Prop),
    (∀ a b, P a → P b → P (a * b)) → (∀ g h : Matrix κ κ K, gᵀ * h = 1 → P (Matrix.fromBlocks g 0 0 h)) →
    (∀ b : Matrix κ κ K, bᵀ = b → P (Matrix.fromBlocks 1 0 b 1)) → P (Matrix.fromBlocks 0 1 (-1) 0) →
    ∀ a : Matrix (κ ⊕ κ) (κ ⊕ κ) K, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → P a := by
  intro K _ κ _ _ P hmul hlevi hlow hJ a ha
  have hup : ∀ s : Matrix κ κ K, sᵀ = s → P (fromBlocks 1 s 0 1) := by
    intro s hs
    rw [upper_unipotent_eq]
    exact hmul _ _ (hmul _ _ (hmul _ _ hJ (hlow _ (by simp [hs]))) hJ) (hlevi _ _ (by simp))
  have hJ0 : (fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) = -J κ K := by
    simp [J, fromBlocks_neg]
  have hsp : a ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.mem_iff']
    rw [hJ0] at ha
    simpa [Matrix.mul_neg, Matrix.neg_mul] using ha
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, a = fromBlocks A B C D :=
    ⟨_, _, _, _, a.fromBlocks_toBlocks.symm⟩
  obtain ⟨X, hX, hu⟩ := exists_symmetric_X_isUnit_det_add_mul_of_symplectic hsp
  have hUX : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    simp [SymplecticGroup.fromBlocks_mem_iff, hX.eq]
  have hprod : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks A B C D =
      fromBlocks (A + X * C) (B + X * D) C D := by
    simp [fromBlocks_multiply]
  generalize hc : A + X * C = c at hu hprod
  have hcT : IsUnit cᵀ.det := by rwa [det_transpose]
  have hLev : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    refine ⟨by simp, by simp, ?_⟩
    rw [transpose_nonsing_inv]
    simp [nonsing_inv_mul _ hcT]
  have hnsp := mul_mem (mul_mem hLev hUX) hsp
  have hn : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 *
      fromBlocks A B C D = fromBlocks 1 (c⁻¹ * (B + X * D)) (cᵀ * C) (cᵀ * D) := by
    rw [Matrix.mul_assoc, hprod, fromBlocks_multiply]
    simp [nonsing_inv_mul _ hu]
  rw [hn] at hnsp
  generalize c⁻¹ * (B + X * D) = Z at hn hnsp
  generalize cᵀ * C = Wm at hn hnsp
  generalize cᵀ * D = V at hn hnsp
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hnsp
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one] at h1 h3
  have hW : Wmᵀ = Wm := h1.symm
  rw [hW] at h3
  have hV : V = Wm * Z + 1 := by rw [← h3]; abel
  have hZ : Zᵀ = Z := by
    rw [hV, transpose_add, transpose_mul, hW, transpose_one, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc] at h2
    simpa using h2
  have hfac : (fromBlocks 1 Z Wm V : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 1 0 Wm 1 * fromBlocks 1 Z 0 1 := by
    rw [fromBlocks_multiply, hV]; simp
  have e2 : (fromBlocks c 0 0 cᵀ⁻¹ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks c⁻¹ 0 0 cᵀ = 1 := by
    rw [fromBlocks_multiply]
    simp [mul_nonsing_inv _ hu, nonsing_inv_mul _ hcT]
  have e3 : (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 = 1 := by
    simp [fromBlocks_multiply]
  have hdec : fromBlocks A B C D = (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) *
      fromBlocks c 0 0 cᵀ⁻¹ * (fromBlocks c⁻¹ 0 0 cᵀ * fromBlocks 1 X 0 1 * fromBlocks A B C D) := by
    rw [Matrix.mul_assoc (fromBlocks 1 (-X) 0 1), ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹),
      ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹), e2, Matrix.one_mul, ← Matrix.mul_assoc, e3,
      Matrix.one_mul]
  rw [hdec, hn, hfac]
  refine hmul _ _ (hmul _ _ (hup _ (by simp [hX.eq])) (hlevi _ _ ?_)) (hmul _ _ (hlow _ hW) (hup _ hZ))
  exact mul_nonsing_inv _ hcT

end GlobalTheory.SpGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentConstantPathEqZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_constantPath_eq_zero : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G), Mono i → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ w : Fin r → E, HasTan G (spMap (algebraMap K E) ≫ x) (triv G (spMap (algebraMap K E) ≫ x)) (fun j => i.app V₀ (s j)) w → w = 0 := by
  first | exact @GlobalTheory.Nef.tan_triv_eq_zero | exact GlobalTheory.Nef.tan_triv_eq_zero | (intros; apply GlobalTheory.Nef.tan_triv_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGeneratoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLatticeAtFinitePlace_eq_integral_span_generators : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → Y.L.IsLattice E → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    ∃ (M : Type) (_ : Fintype M) (g : M → Matrix (Fin n) (Fin d) E), ∀ γ,
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v ↔ ∃ a : M → v.adicCompletionIntegers F,
        γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m) := by
  first | exact @GlobalTheory.LatParam.latAtV_param | exact GlobalTheory.LatParam.latAtV_param | (intros; apply GlobalTheory.LatParam.latAtV_param <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlacePartsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLatticeAtFinitePlace_eq_sum_splitPlace_parts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v), ∀ γ ∈ latAtV X W v,
      ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, γ = γ₁ + γ₂ ∧ γ₁.map (piW (t.comp σ)) = 0 ∧ γ₂.map (piW t) = 0 := by
  first | exact @GlobalTheory.LatSplit.latAtV_decomp | exact GlobalTheory.LatSplit.latAtV_decomp | (intros; apply GlobalTheory.LatSplit.latAtV_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LatBound

theorem exists_mul_mem_integers {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {T : Type} [Fintype T] (w : T → Fv F v) :
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ t, c * w t ∈ v.adicCompletionIntegers F := by
  classical
  have key : ∀ x : Fv F v, ∃ c : Fv F v, c ≠ 0 ∧ c ∈ v.adicCompletionIntegers F ∧
      c * x ∈ v.adicCompletionIntegers F := by
    intro x
    by_cases hx : x ∈ v.adicCompletionIntegers F
    · exact ⟨1, one_ne_zero, one_mem _, by simpa using hx⟩
    · have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
      refine ⟨x⁻¹, inv_ne_zero hx0, ?_, by rw [inv_mul_cancel₀ hx0]; exact one_mem _⟩
      exact ((v.adicCompletionIntegers F).mem_or_inv_mem x).resolve_left hx
  choose cw hcw0 hcwO hcw using key
  refine ⟨∏ t, cw (w t), Finset.prod_ne_zero_iff.2 fun t _ => hcw0 _, fun t => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun t => cw (w t)) (Finset.mem_univ t), mul_comm (cw (w t)), mul_assoc]
  exact mul_mem (prod_mem fun t' _ => hcwO _) (hcw _)

theorem locCo_latAtV_bounded : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {B : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → AF F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ), X.L.IsLattice E → Y.L.IsLattice E →
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ i,
      c * (GlobalTheory.LatVac.locCo co v γ).1 i ∈ v.adicCompletionIntegers F ∧
      c * (GlobalTheory.LatVac.locCo co v γ).2 i ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ n d X Y v B κ _ co hX hY
  obtain ⟨M, _, g, hg⟩ := GlobalTheory.LatParam.latAtV_param X Y hX hY v
  obtain ⟨c, hc0, hc⟩ := exists_mul_mem_integers v
    (fun t : Bool × M × κ => if t.1 then (GlobalTheory.LatVac.locCo co v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g t.2.1))).1 t.2.2
      else (GlobalTheory.LatVac.locCo co v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g t.2.1))).2 t.2.2)
  have hsmul : ∀ (t : Fv F v) z, GlobalTheory.LatVac.locCo co v (GlobalTheory.EmbChart.atPlace v t • z) =
      t • GlobalTheory.LatVac.locCo co v z := by
    intro t z
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
    ext k <;> simp [smul_eq_mul, map_mul, GlobalTheory.EmbChart.evFin_atPlace]
  refine ⟨c, hc0, fun γ hγ i => ?_⟩
  obtain ⟨a, rfl⟩ := (hg γ).1 hγ
  simp only [map_sum, hsmul, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  constructor
  · refine sum_mem fun m _ => ?_
    rw [mul_left_comm]
    exact mul_mem (a m).2 (by simpa using hc (true, m, i))
  · refine sum_mem fun m _ => ?_
    rw [mul_left_comm]
    exact mul_mem (a m).2 (by simpa using hc (false, m, i))

end GlobalTheory.LatBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPlacesPrimeToLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_places_prime_to_level : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ w ∈ ch.G.pl.W0,
    ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  first | exact @GlobalTheory.PlacesPrime.places_prime_to_level | exact GlobalTheory.PlacesPrime.places_prime_to_level | (intros; apply GlobalTheory.PlacesPrime.places_prime_to_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharacterQuotientNotUnramifiedOverBasePStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_unrAt_of_under_eq_v0 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = G.pl.v0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  first | exact @GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace | exact GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace | (intros; apply GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFrames
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IoExtStd

theorem thetaIoExtension_of_weakCharacterisation_frames : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧ (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)) → IoExt R.toRealDat := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hC hE hF
  have hB := GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D G Pl0 I0 T0 A3 Ks R F hC hE
  have hcore := hB.1
  have hsh := GlobalTheory.DefLift.holShape_fixed D G Pl0 T0 A3.A Ks R.toRealDat hcore.models.order
  exact GlobalTheory.AdTh.IoExtCore.ioExt_core D G Pl0 T0 A3.A Ks R.toRealDat F.lv2 hcore
    (fun i => GlobalTheory.StdFrame.vStd_of_orthonormal_span D i (hF i))
    (fun i => ⟨GlobalTheory.LowSmooth.lowSm_MW D G Pl0 T0 A3.A Ks R.toRealDat i _,
      GlobalTheory.HolLowOnce.extLine_of_holShape D _ _ _ (hsh i).1⟩)

end GlobalTheory.IoExtStd
end

