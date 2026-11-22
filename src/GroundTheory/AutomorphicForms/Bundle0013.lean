import Mathlib
import GroundTheory.AutomorphicForms.Iwasawa
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
import GroundTheory.AutomorphicForms.TraceClass
import GroundTheory.AutomorphicForms.UnitaryRepresentations

-- bundled from GroundTheory.AutomorphicForms.InductionParabolicGroups
section
noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa

variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)

def blockDiagPart (A : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if β i = β j then A i j else 0

variable {F n β}

theorem blockDiagPart_apply (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    blockDiagPart F n β A i j = if β i = β j then A i j else 0 := rfl

theorem blockDiagPart_one : blockDiagPart F n β 1 = 1 := by
  ext i j
  rw [blockDiagPart_apply]
  split_ifs with h
  · rfl
  · rw [one_apply_ne fun hij => h (by rw [hij])]

theorem blockDiagPart_mul {A B : Matrix (Fin n) (Fin n) F} (hA : A.BlockTriangular β)
    (hB : B.BlockTriangular β) :
    blockDiagPart F n β (A * B) = blockDiagPart F n β A * blockDiagPart F n β B := by
  ext i j
  simp only [blockDiagPart_apply, mul_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : β i = β k
    · rw [if_pos hk, if_pos (hk.symm.trans h)]
    · rw [if_neg hk, zero_mul]
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [hB (h ▸ hlt : β j < β k), mul_zero]
      · rw [hA hlt, zero_mul]
  · refine (Finset.sum_eq_zero fun k _ => ?_).symm
    by_cases hk : β i = β k
    · rw [if_neg fun h' => h (hk.trans h'), mul_zero]
    · rw [if_neg hk, zero_mul]

theorem blockDiagPart_of_forall {A : Matrix (Fin n) (Fin n) F}
    (hA : ∀ i j, β i ≠ β j → A i j = 0) : blockDiagPart F n β A = A := by
  ext i j
  rw [blockDiagPart_apply]
  split_ifs with h
  · rfl
  · exact (hA i j h).symm

variable (F n β)

def levi : Subgroup (GL (Fin n) F) :=
  blockUpper F n β ⊓ blockUpper F n (OrderDual.toDual ∘ β)

variable {F n β}

theorem mem_levi {g : GL (Fin n) F} :
    g ∈ levi F n β ↔ ∀ i j, β i ≠ β j → g i j = 0 := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2 (show OrderDual.toDual (β j) < OrderDual.toDual (β i) from h)
    · exact h1 h
  · intro h
    exact ⟨fun i j hij => h i j hij.ne', fun i j hij => h i j
      (show β i < β j from hij).ne⟩

theorem levi_le_blockUpper : levi F n β ≤ blockUpper F n β := inf_le_left

theorem diagGL_mem_levi (d : Fin n → Fˣ) : diagGL F n d ∈ levi F n β := by
  rw [mem_levi]
  intro i j hij
  have : i ≠ j := fun h => hij (h ▸ rfl)
  simp [diagonal_apply_ne _ this]

def leviProjFun (p : blockUpper F n β) : GL (Fin n) F where
  val := blockDiagPart F n β (p : GL (Fin n) F)
  inv := blockDiagPart F n β ((p⁻¹ : blockUpper F n β) : GL (Fin n) F)
  val_inv := by
    rw [← blockDiagPart_mul p.2 (p⁻¹).2, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, blockDiagPart_one]
  inv_val := by
    rw [← blockDiagPart_mul (p⁻¹).2 p.2, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, Units.val_one, blockDiagPart_one]

theorem leviProjFun_mem (p : blockUpper F n β) : leviProjFun p ∈ levi F n β := by
  rw [mem_levi]
  intro i j hij
  show blockDiagPart F n β _ i j = 0
  rw [blockDiagPart_apply, if_neg hij]

variable (F n β)

def leviProj : blockUpper F n β →* levi F n β where
  toFun p := ⟨leviProjFun p, leviProjFun_mem p⟩
  map_one' := Subtype.ext (Units.ext (by
    show blockDiagPart F n β ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
    rw [Units.val_one, blockDiagPart_one]))
  map_mul' p q := Subtype.ext (Units.ext (by
    show blockDiagPart F n β (((p * q : blockUpper F n β) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = blockDiagPart F n β (p : GL (Fin n) F) *
        blockDiagPart F n β (q : GL (Fin n) F)
    rw [Subgroup.coe_mul, Units.val_mul, blockDiagPart_mul p.2 q.2]))

variable {F n β}

theorem leviProj_apply (p : blockUpper F n β) (i j : Fin n) :
    ((leviProj F n β p : levi F n β) : GL (Fin n) F) i j =
      if β i = β j then (p : GL (Fin n) F) i j else 0 := rfl

theorem leviProj_of_mem_levi {m : GL (Fin n) F} (hm : m ∈ levi F n β) :
    leviProj F n β ⟨m, levi_le_blockUpper hm⟩ = ⟨m, hm⟩ :=
  Subtype.ext (Units.ext (blockDiagPart_of_forall (mem_levi.1 hm)))

def leviIncl : levi F n β →* blockUpper F n β :=
  Subgroup.inclusion levi_le_blockUpper

theorem leviProj_leviIncl (m : levi F n β) : leviProj F n β (leviIncl m) = m :=
  leviProj_of_mem_levi m.2

variable (F n β)

def unipotentRadical : Subgroup (GL (Fin n) F) :=
  (leviProj F n β).ker.map (blockUpper F n β).subtype

def oppositeUnipotentRadical : Subgroup (GL (Fin n) F) :=
  unipotentRadical F n (OrderDual.toDual ∘ β)

variable {F n β}

theorem mem_unipotentRadical {g : GL (Fin n) F} :
    g ∈ unipotentRadical F n β ↔ g ∈ blockUpper F n β ∧
      ∀ i j, β i = β j → g i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.2, fun i j hij => ?_⟩
    have h := congrArg (fun m : levi F n β => ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)
      ((leviProj F n β).mem_ker.1 hp)
    simp only [leviProj_apply, if_pos hij] at h
    simpa using h
  · rintro ⟨hP, h⟩
    refine ⟨⟨g, hP⟩, (leviProj F n β).mem_ker.2 (Subtype.ext (Units.ext ?_)), rfl⟩
    ext i j
    show (if β i = β j then g i j else 0) = ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j
    split_ifs with hij
    · rw [h i j hij, Units.val_one]
    · rw [Units.val_one, one_apply_ne fun e => hij (by rw [e])]

theorem mem_oppositeUnipotentRadical {g : GL (Fin n) F} :
    g ∈ oppositeUnipotentRadical F n β ↔ (∀ i j, β i < β j → g i j = 0) ∧
      ∀ i j, β i = β j → g i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  rw [oppositeUnipotentRadical, mem_unipotentRadical, mem_blockUpper]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 (show OrderDual.toDual (β j) < OrderDual.toDual (β i)
      from hij), fun i j hij => h2 i j (by simpa using hij)⟩,
    fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 i j hij, fun i j hij => h2 i j (by simpa using hij)⟩⟩

theorem unipotentRadical_le_blockUpper : unipotentRadical F n β ≤ blockUpper F n β :=
  fun _ hg => (mem_unipotentRadical.1 hg).1

theorem mem_unipotentRadical_iff_leviProj {p : blockUpper F n β} :
    (p : GL (Fin n) F) ∈ unipotentRadical F n β ↔ leviProj F n β p = 1 := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    rw [← (Subtype.ext hqp : q = p)]
    exact hq
  · intro h
    exact ⟨p, h, rfl⟩

theorem conj_mem_unipotentRadical {p u : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (hu : u ∈ unipotentRadical F n β) : p * u * p⁻¹ ∈ unipotentRadical F n β := by
  have huP := unipotentRadical_le_blockUpper hu
  have h := (mem_unipotentRadical_iff_leviProj (p := ⟨u, huP⟩)).1 hu
  have hm : p * u * p⁻¹ ∈ blockUpper F n β :=
    (blockUpper F n β).mul_mem ((blockUpper F n β).mul_mem hp huP) ((blockUpper F n β).inv_mem hp)
  refine (mem_unipotentRadical_iff_leviProj (p := ⟨_, hm⟩)).2 ?_
  have : (⟨p * u * p⁻¹, hm⟩ : blockUpper F n β) = ⟨p, hp⟩ * ⟨u, huP⟩ * (⟨p, hp⟩)⁻¹ := rfl
  rw [this, map_mul, map_mul, h, mul_one, map_inv, mul_inv_cancel]

theorem leviProj_inv_mul_mem (p : blockUpper F n β) :
    ((leviIncl (leviProj F n β p))⁻¹ * p : blockUpper F n β).1 ∈ unipotentRadical F n β := by
  rw [mem_unipotentRadical_iff_leviProj, map_mul, map_inv, leviProj_leviIncl, inv_mul_cancel]

variable (F n) in
theorem diagGL_conj_apply (d : Fin n → Fˣ) (g : GL (Fin n) F) (i j : Fin n) :
    (diagGL F n d * g * (diagGL F n d)⁻¹ : GL (Fin n) F) i j =
      (d i : F) * g i j * ((d j)⁻¹ : Fˣ) := by
  rw [← map_inv]
  show ((diagGL F n d : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) *
    (diagGL F n d⁻¹ : Matrix (Fin n) (Fin n) F)) i j = _
  rw [coe_diagGL, coe_diagGL, mul_diagonal, diagonal_mul]
  rfl

variable (F n) in
theorem diagGL_inv_conj_apply (d : Fin n → Fˣ) (g : GL (Fin n) F) (i j : Fin n) :
    ((diagGL F n d)⁻¹ * g * diagGL F n d : GL (Fin n) F) i j =
      (((d i)⁻¹ : Fˣ) : F) * g i j * (d j : F) := by
  rw [← map_inv]
  show ((diagGL F n d⁻¹ : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) *
    (diagGL F n d : Matrix (Fin n) (Fin n) F)) i j = _
  rw [coe_diagGL, coe_diagGL, mul_diagonal, diagonal_mul]
  rfl

variable (β) in

def blockRank (i : Fin n) : ℕ := (Finset.univ.filter fun j => β j < β i).card

theorem blockRank_lt {i j : Fin n} (h : β i < β j) : blockRank β i < blockRank β j := by
  refine Finset.card_lt_card ⟨fun k hk => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans h
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
    simp at this

theorem blockRank_eq {i j : Fin n} (h : β i = β j) : blockRank β i = blockRank β j := by
  simp [blockRank, h]

end Parabolic

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.TraceFormulaSpectral
section
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace InnerProduct

namespace GroundTheory.Automorphic

noncomputable section

section Intermediate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem two_mul_traceNorm_comp_le_of_hilbertSchmidt (A : K →L[ℂ] H) (B : H →L[ℂ] K) :
    2 * traceNorm (A.comp B) ≤ hsNormSq A + hsNormSq B := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (A.comp B)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  calc 2 * traceNorm (A.comp B) ≤ 2 * ∑' i, ‖⟪V (b i), A (B (b i))⟫_ℂ‖ₑ := by
        gcongr; exact traceNorm_le_of_adjoint_comp b hV
    _ ≤ ∑' i, (‖((A†).comp V) (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2) := by
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← adjoint_inner_left, ← comp_apply (A†) V]
        calc 2 * ‖⟪((A†).comp V) (b i), B (b i)⟫_ℂ‖ₑ
            ≤ 2 * (‖((A†).comp V) (b i)‖ₑ * ‖B (b i)‖ₑ) := by gcongr; exact enorm_inner_le _ _
          _ ≤ _ := ennreal_two_mul_le_sq_add_sq _ _
    _ = hsNormSq ((A†).comp V) + hsNormSq B := by
        rw [ENNReal.tsum_add, hsNormSq_eq_tsum b, hsNormSq_eq_tsum b]
    _ ≤ ‖V‖ₑ ^ 2 * hsNormSq (A†) + hsNormSq B := by gcongr; exact hsNormSq_comp_right_le _ _
    _ ≤ 1 ^ 2 * hsNormSq (A†) + hsNormSq B := by gcongr
    _ = hsNormSq A + hsNormSq B := by rw [one_pow, one_mul, hsNormSq_adjoint]

theorem isTraceClass_comp_of_isHilbertSchmidt {A : K →L[ℂ] H} {B : H →L[ℂ] K}
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) : IsTraceClass (A.comp B) := by
  have h := (two_mul_traceNorm_comp_le_of_hilbertSchmidt A B).trans_lt
    (ENNReal.add_lt_top.2 ⟨hA, hB⟩)
  rw [IsTraceClass]
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.mul_top two_ne_zero] at h
  exact lt_irrefl _ h

theorem isTraceClass_and_trace_eq_of_conj (e : H ≃ₗᵢ[ℂ] K) {T : H →L[ℂ] H} {S : K →L[ℂ] K}
    (hT : IsTraceClass T) (hS : ∀ v, S (e v) = e (T v)) : IsTraceClass S ∧ trace S = trace T := by
  have hS' : S = ((e : H →L[ℂ] K).comp T).comp (e.symm : K →L[ℂ] H) := by
    ext w
    obtain ⟨v, rfl⟩ := e.surjective w
    simp [hS]
  have hSc : IsTraceClass S := by
    obtain ⟨A, B, hA, hB, hAB⟩ := hT.exists_comp
    rw [hS', hAB, ← comp_assoc, comp_assoc]
    exact isTraceClass_comp_of_isHilbertSchmidt (hA.comp_left _) (hB.comp_right _)
  refine ⟨hSc, ?_⟩
  let b := stdHilbertBasis ℂ H
  let b' : HilbertBasis _ ℂ K := HilbertBasis.ofRepr (e.symm.trans b.repr)
  have hb' : ∀ i, b' i = e (b i) := fun i => rfl
  have h1 := hSc.hasSum_trace b'
  have h2 := hT.hasSum_trace b
  refine h1.unique (h2.congr_fun fun i => ?_)
  rw [hb', hS, LinearIsometryEquiv.inner_map_map]

end Intermediate

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

section Equiv

variable {μ : Measure G} {σ : UnitaryRep G K} {τ : UnitaryRep G L}

theorem Equiv.isTraceClass_integrated_and_trace_eq (e : σ.Equiv τ) (f : G →₁[μ] ℂ)
    (h : IsTraceClass (σ.integrated μ f)) :
    IsTraceClass (τ.integrated μ f) ∧ trace (τ.integrated μ f) = trace (σ.integrated μ f) := by
  refine isTraceClass_and_trace_eq_of_conj e.toLinearIsometryEquiv h fun v => ?_
  have := comp_integrated_of_mem_intertwiners σ μ e.mem_intertwiners f
  exact (congrArg (fun T : K →L[ℂ] L => T v) this).symm

theorem Equiv.trace_integrated (e : σ.Equiv τ) (f : G →₁[μ] ℂ)
    (h : IsTraceClass (σ.integrated μ f)) :
    trace (τ.integrated μ f) = trace (σ.integrated μ f) :=
  (e.isTraceClass_integrated_and_trace_eq f h).2

end Equiv

section Decomposition

variable (π : UnitaryRep G H) (μ : Measure G) (f : G →₁[μ] ℂ)
variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))

theorem integrated_restrict_apply (j : J) (v : V j) :
    (((π.restrict (V j) (hinv j)).integrated μ f v : V j) : H) = π.integrated μ f (v : H) := by
  have := comp_integrated_of_mem_intertwiners (π.restrict (V j) (hinv j)) μ
    (subtypeL_mem_intertwiners π (V j) (hinv j)) f
  exact congrArg (fun T : V j →L[ℂ] H => T v) this

variable {π μ f}

theorem isTraceClass_integrated_restrict (hT : IsTraceClass (π.integrated μ f)) (j : J) :
    IsTraceClass ((π.restrict (V j) (hinv j)).integrated μ f) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := hT.exists_comp
  set ι : V j →L[ℂ] H := (V j).subtypeL
  have hιι : ∀ x : V j, (ι†) (ι x) = x := fun x =>
    ext_inner_left ℂ fun w => by
      rw [adjoint_inner_right]
      rfl
  have heq : (π.restrict (V j) (hinv j)).integrated μ f = ((ι†).comp A).comp (B.comp ι) := by
    ext1 x
    simp only [comp_apply]
    rw [← hιι ((π.restrict (V j) (hinv j)).integrated μ f x)]
    congr 1
    change (((π.restrict (V j) (hinv j)).integrated μ f x : V j) : H) = _
    rw [integrated_restrict_apply, hAB]
    rfl
  rw [heq]
  exact isTraceClass_comp_of_isHilbertSchmidt (hA.comp_left _) (hB.comp_right _)

variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)

def collectedHilbertBasis : HilbertBasis (Σ j, (exists_hilbertBasis ℂ (V j)).choose) ℂ H :=
  HilbertBasis.mk (v := fun a => (V a.1).subtypeₗᵢ (stdHilbertBasis ℂ (V a.1) a.2))
    (hsum.OrthogonalFamily.orthonormal_sigma_orthonormal fun j =>
      (stdHilbertBasis ℂ (V j)).orthonormal) (by
    refine le_trans (top_le_topologicalClosure_iSup hsum) (Submodule.topologicalClosure_minimal _
      (iSup_le fun j => ?_) (Submodule.isClosed_topologicalClosure _))
    intro v hv
    have hd := (stdHilbertBasis ℂ (V j)).dense_span
    have hmem : (⟨v, hv⟩ : V j) ∈
        (Submodule.span ℂ (Set.range (stdHilbertBasis ℂ (V j)))).topologicalClosure := by
      rw [hd]; trivial
    have h1 := Submodule.topologicalClosure_map (V j).subtypeL
      (Submodule.span ℂ (Set.range (stdHilbertBasis ℂ (V j))))
    have h2 : v ∈ ((Submodule.span ℂ (Set.range (stdHilbertBasis ℂ (V j)))).map
        ((V j).subtypeL : V j →ₗ[ℂ] H)).topologicalClosure :=
      h1 ⟨⟨v, hv⟩, hmem, rfl⟩
    refine Submodule.topologicalClosure_mono ?_ h2
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨j, i⟩, rfl⟩)

theorem collectedHilbertBasis_apply (a : Σ j, (exists_hilbertBasis ℂ (V j)).choose) :
    collectedHilbertBasis hsum a = ((stdHilbertBasis ℂ (V a.1) a.2 : V a.1) : H) := by
  rw [collectedHilbertBasis, HilbertBasis.coe_mk]
  rfl

include hsum in

theorem hasSum_trace_integrated_restrict (hT : IsTraceClass (π.integrated μ f)) :
    HasSum (fun j => trace ((π.restrict (V j) (hinv j)).integrated μ f))
      (trace (π.integrated μ f)) := by
  have h1 := hT.hasSum_trace (collectedHilbertBasis hsum)
  refine h1.sigma fun j => ?_
  refine ((isTraceClass_integrated_restrict hinv hT j).hasSum_trace
    (stdHilbertBasis ℂ (V j))).congr_fun fun i => ?_
  rw [collectedHilbertBasis_apply, ← integrated_restrict_apply π μ f hinv j]
  rfl

variable (π) in

def restrictSetoid : Setoid J where
  r j k := (π.restrict (V j) (hinv j)).IsEquivalent (π.restrict (V k) (hinv k))
  iseqv := ⟨fun _ => IsEquivalent.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

variable (π) in

def multiplicity (c : Quotient (restrictSetoid π hinv)) : ℕ :=
  Nat.card {j : J // (Quotient.mk (restrictSetoid π hinv) j) = c}

include hsum in

theorem hasSum_multiplicity_mul_trace (hT : IsTraceClass (π.integrated μ f))
    (hfin : ∀ j, {k : J | (π.restrict (V k) (hinv k)).IsEquivalent
      (π.restrict (V j) (hinv j))}.Finite) :
    HasSum (fun c : Quotient (restrictSetoid π hinv) => (multiplicity π hinv c : ℂ) *
        trace ((π.restrict (V c.out) (hinv c.out)).integrated μ f))
      (trace (π.integrated μ f)) := by
  set S := restrictSetoid π hinv
  have h0 := hasSum_trace_integrated_restrict hinv hsum hT
  let e := Equiv.sigmaFiberEquiv (Quotient.mk S)
  have h1 : HasSum (fun a : Σ c : Quotient S, {j : J // Quotient.mk S j = c} =>
      trace ((π.restrict (V (e a)) (hinv (e a))).integrated μ f)) (trace (π.integrated μ f)) :=
    (e.hasSum_iff).2 h0
  refine h1.sigma fun c => ?_
  have hfc : Set.Finite {j : J | Quotient.mk S j = c} := by
    refine (hfin c.out).subset fun j hj => ?_
    have : Quotient.mk S j = Quotient.mk S c.out := by rw [show Quotient.mk S j = c from hj]; exact c.out_eq.symm
    exact Quotient.exact this
  have : Finite {j : J // Quotient.mk S j = c} := hfc.to_subtype
  have : Fintype {j : J // Quotient.mk S j = c} := Fintype.ofFinite _
  have hconst : ∀ a : {j : J // Quotient.mk S j = c},
      trace ((π.restrict (V (e ⟨c, a⟩)) (hinv (e ⟨c, a⟩))).integrated μ f) =
        trace ((π.restrict (V c.out) (hinv c.out)).integrated μ f) := by
    intro a
    have hja : Quotient.mk S a.1 = Quotient.mk S c.out := by rw [a.2]; exact c.out_eq.symm
    obtain ⟨eq⟩ := (Quotient.exact hja : S a.1 c.out)
    exact (eq.trace_integrated f (isTraceClass_integrated_restrict hinv hT a.1)).symm
  have h2 := hasSum_fintype (fun a : {j : J // Quotient.mk S j = c} =>
    trace ((π.restrict (V (e ⟨c, a⟩)) (hinv (e ⟨c, a⟩))).integrated μ f))
  convert h2 using 1
  rw [Finset.sum_congr rfl fun a _ => hconst a, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    multiplicity, Nat.card_eq_fintype_card]

end Decomposition

end UnitaryRep

end

end GroundTheory.Automorphic
end

