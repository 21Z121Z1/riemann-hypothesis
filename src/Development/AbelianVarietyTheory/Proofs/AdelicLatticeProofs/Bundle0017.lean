import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorSLOrbitMapProperOfIsClosed
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.OrbitProper

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma tpow_mul' (n : ℕ) (y z : Matrix ι ι ℂ) : tpow n (y * z) = tpow n y * tpow n z := by
  classical
  ext a b
  simp only [tpow, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp [Finset.prod_mul_distrib]

lemma tpow_one' (n : ℕ) : tpow n (1 : Matrix ι ι ℂ) = 1 := by
  ext a b
  simp only [tpow, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

variable {m : ℕ} (d : Fin m → ℕ)

omit [DecidableEq ι] in
lemma act_mul' (t : TIdx ι d → ℂ) (y z : Matrix ι ι ℂ) :
    act d t (y * z) = act d (act d t y) z := by
  funext k
  simp only [act, tpow_mul', ← Matrix.vecMul_vecMul]

lemma act_one' (t : TIdx ι d → ℂ) : act d t 1 = t := by
  funext k
  simp [act, tpow_one']

omit [DecidableEq ι] in
lemma continuous_act_right (t : TIdx ι d → ℂ) : Continuous (act d t) := by
  refine continuous_pi fun k => ?_
  simp only [act, Matrix.vecMul, dotProduct, tpow, Matrix.of_apply]
  fun_prop

omit [DecidableEq ι] in
lemma continuous_act_left (y : Matrix ι ι ℂ) : Continuous (fun t : TIdx ι d → ℂ => act d t y) := by
  refine continuous_pi fun k => ?_
  simp only [act, Matrix.vecMul, dotProduct, tpow, Matrix.of_apply]
  fun_prop

def box (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℝ) : Set (Matrix ι ι ℂ) :=
  {y | y.det = 1 ∧ ∀ i j, ‖y i j‖ ≤ N}

lemma isCompact_box (N : ℝ) : IsCompact (box ι N) := by
  have h1 : IsCompact (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Metric.closedBall (0 : ℂ) N) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have h2 : IsClosed {y : Matrix ι ι ℂ | y.det = 1} :=
    isClosed_eq (continuous_id.matrix_det) continuous_const
  have h3 := IsCompact.inter_left (X := Matrix ι ι ℂ) h1 h2
  convert h3 using 1
  ext y
  exact ⟨fun h => ⟨h.1, fun i _ j _ => mem_closedBall_zero_iff.2 (h.2 i j)⟩,
    fun h => ⟨h.1, fun i j => mem_closedBall_zero_iff.1 (h.2 i trivial j trivial)⟩⟩

lemma box_mono {N M : ℝ} (h : N ≤ M) : box ι N ⊆ box ι M :=
  fun _ hy => ⟨hy.1, fun i j => (hy.2 i j).trans h⟩

lemma box_mul (N : ℝ) (g : Matrix ι ι ℂ) (hg : g.det = 1) : ∃ M : ℝ, ∀ a ∈ box ι N, a * g ∈ box ι M := by
  refine ⟨∑ j, ∑ k, |N| * ‖g k j‖, fun a ha => ⟨by rw [Matrix.det_mul, ha.1, hg, one_mul], fun i j => ?_⟩⟩
  calc ‖(a * g) i j‖ ≤ ∑ k, |N| * ‖g k j‖ := by
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right ((ha.2 i k).trans (le_abs_self N)) (norm_nonneg _)
    _ ≤ _ := Finset.single_le_sum (f := fun j => ∑ k, |N| * ‖g k j‖)
        (fun j _ => Finset.sum_nonneg fun k _ => by positivity) (Finset.mem_univ j)

lemma det_adj {y : Matrix ι ι ℂ} (hy : y.det = 1) : y.adjugate.det = 1 := by
  rw [Matrix.det_adjugate, hy, one_pow]

lemma adj_mul {y : Matrix ι ι ℂ} (hy : y.det = 1) : y.adjugate * y = 1 := by
  rw [Matrix.adjugate_mul, hy, one_smul]

lemma mul_adj {y : Matrix ι ι ℂ} (hy : y.det = 1) : y * y.adjugate = 1 := by
  rw [Matrix.mul_adjugate, hy, one_smul]

lemma exists_interior (v : TIdx ι d → ℂ) (hX : IsClosed (orb d v)) :
    ∃ (n : ℝ) (O : Set (TIdx ι d → ℂ)) (y₀ : Matrix ι ι ℂ), IsOpen O ∧ y₀.det = 1 ∧ act d v y₀ ∈ O ∧
      ∀ w ∈ O, w ∈ orb d v → w ∈ act d v '' box ι n := by
  haveI : CompleteSpace (orb d v) := hX.completeSpace_coe
  haveI : Nonempty (orb d v) := ⟨⟨act d v 1, 1, Matrix.det_one, rfl⟩⟩
  obtain ⟨n, x, hx⟩ := nonempty_interior_of_iUnion_of_closed (X := orb d v)
    (f := fun n : ℕ => Subtype.val ⁻¹' (act d v '' box ι n))
    (fun n => ((isCompact_box (n : ℝ)).image (continuous_act_right d v)).isClosed.preimage
      continuous_subtype_val)
    (by
      refine Set.eq_univ_of_forall fun ⟨w, y, hy, hw⟩ => ?_
      obtain ⟨M, hM⟩ := box_mul (ι := ι) 1 y hy
      have h1 : (1 : Matrix ι ι ℂ) ∈ box ι 1 := ⟨Matrix.det_one, fun i j => by
        rw [Matrix.one_apply]; split_ifs <;> simp⟩
      have := hM 1 h1
      rw [one_mul] at this
      exact Set.mem_iUnion.2 ⟨⌈M⌉₊, y, box_mono (Nat.le_ceil M) this, hw.symm⟩)
  rw [mem_interior] at hx
  obtain ⟨t, hts, hto, hxt⟩ := hx
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hto
  obtain ⟨x, y₀, hy₀, rfl⟩ := x
  exact ⟨n, O, y₀, hO, hy₀, hxt, fun w hw hwX => hts (a := ⟨w, hwX⟩) hw⟩

lemma locally_box (v : TIdx ι d → ℂ) (hX : IsClosed (orb d v)) (w : TIdx ι d → ℂ) (hw : w ∈ orb d v) :
    ∃ O : Set (TIdx ι d → ℂ), IsOpen O ∧ w ∈ O ∧ ∃ N : ℝ, O ∩ orb d v ⊆ act d v '' box ι N := by
  obtain ⟨n, O, y₀, hO, hy₀, hmem, hsub⟩ := exists_interior d v hX
  obtain ⟨y, hy, rfl⟩ := hw
  obtain ⟨M, hM⟩ := box_mul (ι := ι) n (y₀.adjugate * y)
    (by rw [Matrix.det_mul, det_adj hy₀, hy, one_mul])
  refine ⟨(fun t => act d t (y.adjugate * y₀)) ⁻¹' O, hO.preimage (continuous_act_left d _), ?_, M, ?_⟩
  · show act d (act d v y) (y.adjugate * y₀) ∈ O
    rwa [← act_mul', ← mul_assoc, mul_adj hy, one_mul]
  · rintro w ⟨hwO, z, hz, rfl⟩
    obtain ⟨a, ha, hav⟩ := hsub _ hwO ⟨z * (y.adjugate * y₀),
      by rw [Matrix.det_mul, Matrix.det_mul, det_adj hy, hy₀, hz]; simp, (act_mul' d v _ _).symm⟩
    refine ⟨_, hM a ha, ?_⟩
    simp only at hav
    rw [act_mul', hav, ← act_mul', mul_assoc, ← mul_assoc y₀, mul_adj hy₀, one_mul, adj_mul hy, act_one']

lemma isCompact_nsq {κ : Type} [Fintype κ] (C : ℝ) : IsCompact {w : κ → ℂ | nsq w ≤ C} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine isClosed_le ?_ continuous_const
    unfold nsq
    fun_prop
  · refine (Metric.isBounded_closedBall (x := (0 : κ → ℂ)) (r := Real.sqrt C)).subset fun w hw => ?_
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro k
    refine Real.le_sqrt_of_sq_le (le_trans ?_ hw)
    exact Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)

end GlobalTheory.ClassFin.OrbitProper

open GlobalTheory.ClassFin.OrbitProper in

theorem GlobalTheory.ClassFin.orbit_proper_of_isClosed : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), IsClosed (orb d v) → ∀ C : ℝ, ∃ C' : ℝ, ∀ y : Matrix ι ι ℂ, y.det = 1 → nsq (act d v y) ≤ C → ∃ h : Matrix ι ι ℂ, h.det = 1 ∧ act d v h = v ∧ ∀ i j, ‖(h * y) i j‖ ≤ C' := by
  intro ι _ _ m d v hX C
  have hK : IsCompact (orb d v ∩ {w | nsq w ≤ C}) := (isCompact_nsq C).inter_left hX
  have key : ∃ N : ℝ, orb d v ∩ {w | nsq w ≤ C} ⊆ act d v '' box ι N := by
    refine hK.induction_on (p := fun s => ∃ N : ℝ, s ⊆ act d v '' box ι N) ⟨0, Set.empty_subset _⟩
      (fun s t hst ⟨N, hN⟩ => ⟨N, hst.trans hN⟩) ?_ ?_
    · rintro s t ⟨N, hN⟩ ⟨M, hM⟩
      exact ⟨max N M, Set.union_subset (hN.trans (Set.image_mono (box_mono (le_max_left _ _))))
        (hM.trans (Set.image_mono (box_mono (le_max_right _ _))))⟩
    · intro w hw
      obtain ⟨O, hO, hwO, N, hN⟩ := locally_box d v hX w hw.1
      refine ⟨O ∩ orb d v, ?_, N, hN⟩
      exact mem_nhdsWithin.2 ⟨O, hO, hwO, fun x hx => ⟨hx.1, hx.2.1⟩⟩
  obtain ⟨N, hN⟩ := key
  refine ⟨N, fun y hy hC => ?_⟩
  obtain ⟨a, ha, hav⟩ := hN (a := act d v y) ⟨⟨y, hy, rfl⟩, hC⟩
  refine ⟨a * y.adjugate, by rw [Matrix.det_mul, ha.1, det_adj hy, one_mul], ?_, ?_⟩
  · rw [act_mul', hav, ← act_mul', mul_adj hy, act_one']
  · rw [mul_assoc, adj_mul hy, mul_one]
    exact ha.2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitary
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Calc

variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)

theorem hf_add_left (x x' y : Fin n → R) : hf σ G (x + x') y = hf σ G x y + hf σ G x' y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y y' : Fin n → R) : hf σ G x (y + y') = hf σ G x y + hf σ G x y' := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (c : R) (x y : Fin n → R) : hf σ G (c • x) y = c * hf σ G x y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (c : R) (x y : Fin n → R) : hf σ G x (c • y) = σ c * hf σ G x y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hf_conj (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a) (x y : Fin n → R) :
    σ (hf σ G x y) = hf σ G y x := by
  simp only [hf, map_sum, map_mul, hσ, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem tv_mulVec (x : Fin n → R) (t : R) (v : Fin n → R) :
    tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  funext a
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, hf, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem ext_mulVec {A B : Matrix (Fin n) (Fin n) R} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

theorem tv_mul (x : Fin n → R) (t t' : R) :
    tv σ G x t * tv σ G x t' = tv σ G x (t + t' + t * t' * hf σ G x x) := by
  refine ext_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, tv_mulVec, hf_add_left, hf_smul_left,
    add_assoc, ← add_smul]
  congr 2
  ring

theorem tv_det (x : Fin n → R) (t : R) : (tv σ G x t).det = 1 + t * hf σ G x x := by
  have h : tv σ G x t = 1 + Matrix.replicateCol Unit (t • x) *
      Matrix.replicateRow Unit (fun b => ∑ e, G b e * σ (x e)) := by
    rw [tv]
    congr 1
    ext a b
    simp [Matrix.mul_apply]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp only [dotProduct, hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem isU_tv (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a) (x : Fin n → R) (t : R)
    (h : t + σ t + t * σ t * hf σ G x x = 0) : IsU σ G (tv σ G x t) := by
  intro v w
  rw [tv_mulVec, tv_mulVec]
  simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, map_mul, hf_conj σ G hσ hG]
  linear_combination (hf σ G v x * hf σ G x w) * h

theorem conj_tv (γ : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (t : R) (h : IsU σ G γ) :
    γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ := by
  refine ext_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, h, Matrix.mulVec_add,
    Matrix.mulVec_smul]

theorem tv_smul (a : R) (x : Fin n → R) (t : R) :
    tv σ G (a • x) t = tv σ G x (t * a * σ a) := by
  refine ext_mulVec fun v => ?_
  rw [tv_mulVec, tv_mulVec, hf_smul_right, smul_smul]
  congr 2
  ring

theorem isU_mul (γ γ' : Matrix (Fin n) (Fin n) R) (h : IsU σ G γ) (h' : IsU σ G γ') :
    IsU σ G (γ * γ') := by
  intro v w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, h']

theorem calculus : ∀ (R : Type) [CommRing R] (n : ℕ) (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R), (∀ a, σ (σ a) = a) → (∀ a b, σ (G a b) = G b a) → (∀ x y, σ (hf σ G x y) = hf σ G y x) ∧ (∀ x t v, tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x) ∧ (∀ x t t', tv σ G x t * tv σ G x t' = tv σ G x (t + t' + t * t' * hf σ G x x)) ∧ (∀ x t, (tv σ G x t).det = 1 + t * hf σ G x x) ∧ (∀ x t, t + σ t + t * σ t * hf σ G x x = 0 → IsU σ G (tv σ G x t)) ∧ (∀ γ x t, IsU σ G γ → γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ) ∧ (∀ (a : R) x t, tv σ G (a • x) t = tv σ G x (t * a * σ a)) ∧ (∀ γ γ', IsU σ G γ → IsU σ G γ' → IsU σ G (γ * γ')) :=
  fun _ _ _ σ G hσ hG => ⟨hf_conj σ G hσ hG, tv_mulVec σ G, tv_mul σ G, tv_det σ G, isU_tv σ G hσ hG,
    conj_tv σ G, tv_smul σ G, isU_mul σ G⟩

end GlobalTheory.UTrans.Calc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulIndexSqsInvolution
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem mem_sqs_iff_exists_sq {G : Type} [CommGroup G] (U : Subgroup G) (x : G) :
    x ∈ sqs U ↔ ∃ y ∈ U, y ^ 2 = x := by
  simp [sqs, Subgroup.mem_map]

theorem two_mul_index_sqs_involution :
    ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) →
      (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε →
      (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) →
      2 * (sqs (⊤ : Subgroup A)).index =
        (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) *
          (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker := by
  intro A _ σ ε hσ h90 hε1 hε2 hσε h2
  set B : Subgroup A := σ.eqLocus (MonoidHom.id A) with hB
  set N : Subgroup A := (MonoidHom.id A * σ).ker with hN
  set S : Subgroup A := sqs (⊤ : Subgroup A) with hS
  have memB : ∀ a, a ∈ B ↔ σ a = a := fun a => Iff.rfl
  have memN : ∀ a, a ∈ N ↔ a * σ a = 1 := fun a => Iff.rfl
  have memS : ∀ a, a ∈ S ↔ ∃ y, y ^ 2 = a := fun a => by
    rw [hS, mem_sqs_iff_exists_sq]; simp
  let f : A →* A := MonoidHom.id A / σ
  have hf : ∀ a, f a = a / σ a := fun a => rfl
  have hker : ∀ a, f a = 1 ↔ a ∈ B := fun a => by
    rw [hf, memB, div_eq_one, eq_comm]
  have hrange : f.range = N := by
    ext x
    rw [memN, MonoidHom.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      rw [hf, map_div, hσ]; simp
    · intro hx
      obtain ⟨b, hb⟩ := h90 x hx
      exact ⟨b, hb.symm⟩
  have hcomap : B ⊔ S = (sqs N).comap f := by
    apply le_antisymm
    · apply sup_le
      · intro a ha
        rw [Subgroup.mem_comap, (hker a).2 ha]
        exact one_mem _
      · intro a ha
        obtain ⟨y, rfl⟩ := (memS a).1 ha
        rw [Subgroup.mem_comap, mem_sqs_iff_exists_sq]
        exact ⟨f y, hrange ▸ ⟨y, rfl⟩, (map_pow f y 2).symm⟩
    · intro a ha
      rw [Subgroup.mem_comap, mem_sqs_iff_exists_sq] at ha
      obtain ⟨c, hc, hca⟩ := ha
      rw [← hrange] at hc
      obtain ⟨b, rfl⟩ := hc
      have h1 : a / b ^ 2 ∈ B := by
        rw [← hker, map_div, map_pow, hca, div_self']
      have : a = a / b ^ 2 * b ^ 2 := by simp
      rw [this]
      exact Subgroup.mul_mem_sup h1 ((memS _).2 ⟨b, rfl⟩)
  have e1 : (B ⊔ S).index = (sqs N).relIndex N := by
    rw [hcomap, Subgroup.index_comap, hrange]
  have e2 : S.relIndex (B ⊔ S) * (B ⊔ S).index = S.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have e3 : S.relIndex (B ⊔ S) = S.relIndex B := Subgroup.relIndex_sup_right B S
  have hle : sqs B ≤ S ⊓ B := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := (mem_sqs_iff_exists_sq _ _).1 ha
    exact ⟨(memS _).2 ⟨y, rfl⟩, pow_mem hy 2⟩
  have e4 : (sqs B).relIndex (S ⊓ B) * (S ⊓ B).relIndex B = (sqs B).relIndex B :=
    Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_right
  have e5 : (S ⊓ B).relIndex B = S.relIndex B := Subgroup.inf_relIndex_right S B
  have hεB : ε ∈ B := hσε
  have key : ∀ y, y ^ 2 ∈ sqs B ↔ f y = 1 := by
    intro y
    rw [mem_sqs_iff_exists_sq, hker]
    constructor
    · rintro ⟨b, hb, hby⟩
      have : (y / b) ^ 2 = 1 := by rw [div_pow, hby, div_self']
      have hyb : y / b ∈ B := by
        rcases h2 _ this with h | h
        · rw [h]; exact one_mem _
        · rw [h]; exact hεB
      simpa using mul_mem hyb hb
    · intro hy
      exact ⟨y, hy, rfl⟩
  obtain ⟨a0, ha0⟩ := h90 ε (by rw [hσε, ← sq, hε2])
  rw [← hf] at ha0
  have e6 : (sqs B).relIndex (S ⊓ B) = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    have h0 : a0 ^ 2 ∈ S ⊓ B :=
      ⟨(memS _).2 ⟨a0, rfl⟩, (hker _).1 (by rw [map_pow, ← ha0, hε2])⟩
    refine ⟨⟨a0 ^ 2, h0⟩, ?_⟩
    rintro ⟨x, hxS, hxB⟩
    obtain ⟨y, rfl⟩ := (memS x).1 hxS
    have hy : f y ^ 2 = 1 := by rw [← map_pow]; exact (hker _).2 hxB
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rw [← mul_pow, key, key, map_mul, ← ha0]
    rcases h2 _ hy with h | h
    · rw [h, one_mul]
      exact Or.inr ⟨rfl, hε1⟩
    · rw [h, ← sq]
      exact Or.inl ⟨hε2, hε1⟩
  rw [← e2, e1, e3, ← e4, e5, e6, mul_assoc]

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowCardLeIndexIInf
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_pow_card_le_index_iInf :
    ∀ (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G),
      (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 →
        2 ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  intro G ι _ _ K h hidx
  classical
  choose x hx hx' using h
  have key : ∀ (A : Finset ι) (j : ι), (∏ i ∈ A, x i) ∈ K j ↔ j ∉ A := by
    intro A j
    constructor
    · intro hm hj
      rw [← Finset.mul_prod_erase A x hj] at hm
      have h2 : (∏ i ∈ A.erase j, x i) ∈ K j :=
        Subgroup.prod_mem _ fun i hi => hx' i j (Finset.ne_of_mem_erase hi).symm
      exact hx j ((Subgroup.mul_mem_cancel_right _ h2).1 hm)
    · intro hj
      exact Subgroup.prod_mem _ fun i hi => hx' i j (fun e => hj (e ▸ hi))
  haveI : Finite (G ⧸ ⨅ i, K i) := Nat.finite_of_card_ne_zero hidx
  have inj : Function.Injective
      (fun A : Finset ι => ((∏ i ∈ A, x i : G) : G ⧸ ⨅ i, K i)) := by
    intro A B hAB
    have hm : (∏ i ∈ A, x i)⁻¹ * (∏ i ∈ B, x i) ∈ ⨅ i, K i := QuotientGroup.eq.1 hAB
    ext j
    have hj : (∏ i ∈ A, x i)⁻¹ * (∏ i ∈ B, x i) ∈ K j := (Subgroup.mem_iInf.1 hm) j
    have hiff : (∏ i ∈ A, x i) ∈ K j ↔ (∏ i ∈ B, x i) ∈ K j := by
      constructor
      · intro ha
        exact (Subgroup.mul_mem_cancel_left _ (inv_mem ha)).1 hj
      · intro hb
        exact inv_mem_iff.1 ((Subgroup.mul_mem_cancel_right _ hb).1 hj)
    rw [key, key] at hiff
    exact not_iff_not.1 hiff
  have := Nat.card_le_card_of_injective _ inj
  rwa [Nat.card_eq_fintype_card, Fintype.card_finset] at this

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnipotentUpperSizeReduction
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem unipotent_size_reduction_column {N : ℕ} (n : Matrix (Fin N) (Fin N) ℝ)
    (h1 : ∀ i, n i i = 1) (h0 : ∀ i j, j < i → n i j = 0) (j : Fin N) (k : ℕ) :
    ∃ z : Fin N → ℤ, z j = 1 ∧ (∀ l, j < l → z l = 0) ∧
      ∀ i, i < j → (j : ℕ) ≤ i + k → |∑ l, n i l * (z l : ℝ)| ≤ 1 / 2 := by
  induction k with
  | zero =>
    refine ⟨Pi.single j 1, by simp, fun l hl => by simp [Pi.single_apply, hl.ne'], ?_⟩
    intro i hi hk
    exact absurd hk (by have : (i : ℕ) < j := hi; omega)
  | succ k ih =>
    obtain ⟨z, hz1, hz0, hz⟩ := ih
    by_cases hk : k + 1 ≤ (j : ℕ)
    · let i0 : Fin N := ⟨j - (k + 1), by have := j.2; omega⟩
      have hi0v : (i0 : ℕ) = j - (k + 1) := rfl
      have hi0 : i0 < j := by
        show (i0 : ℕ) < j
        omega
      set c : ℤ := -round (∑ l, n i0 l * (z l : ℝ)) with hc
      have key : ∀ i, ∑ l, n i l * (((z + Pi.single i0 c : Fin N → ℤ) l : ℤ) : ℝ)
          = ∑ l, n i l * (z l : ℝ) + n i i0 * c := by
        intro i
        simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single i0]
        · simp
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · simp
      refine ⟨z + Pi.single i0 c, ?_, ?_, ?_⟩
      · simp [Pi.single_apply, hi0.ne', hz1]
      · intro l hl
        simp [Pi.single_apply, (hi0.trans hl).ne', hz0 l hl]
      · intro i hi hik
        rw [key]
        by_cases h : i = i0
        · subst h
          rw [h1, one_mul, hc, Int.cast_neg, ← sub_eq_add_neg]
          exact abs_sub_round _
        · have hne : (i : ℕ) ≠ i0 := fun e => h (Fin.ext e)
          have hlt : i0 < i := by
            show (i0 : ℕ) < i
            omega
          rw [h0 i i0 hlt, zero_mul, add_zero]
          exact hz i hi (by omega)
    · exact ⟨z, hz1, hz0, fun i hi _ => hz i hi (by omega)⟩

theorem unipotent_size_reduction :
    ∀ (N : ℕ) (n : Matrix (Fin N) (Fin N) ℝ), (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) →
      ∃ ν : Matrix (Fin N) (Fin N) ℤ, (∀ i, ν i i = 1) ∧ (∀ i j, j < i → ν i j = 0) ∧
        ∀ i j, i < j → |(n * ν.map (Int.cast : ℤ → ℝ)) i j| ≤ 1 / 2 := by
  intro N n h1 h0
  choose z hz1 hz0 hz using fun j => unipotent_size_reduction_column n h1 h0 j N
  refine ⟨Matrix.of fun i j => z j i, fun i => hz1 i, fun i j h => hz0 j i h, ?_⟩
  intro i j hij
  rw [Matrix.mul_apply]
  exact hz j i hij (by have := j.2; omega)

end GlobalTheory.ClassFin
end

