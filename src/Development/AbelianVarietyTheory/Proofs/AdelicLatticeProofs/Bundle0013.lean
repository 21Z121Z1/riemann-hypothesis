import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAutStableSLMatrixGroupImageBlockDiagPart
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

private lemma idempotent_corner_part_mul {A : Type} [Ring A] (E g h : A) (hE : E * E = E)
    (hg : (1 - E) * g * E = 0) (hh : (1 - E) * h * E = 0) :
    (E * g * E + (1 - E) * g * (1 - E)) * (E * h * E + (1 - E) * h * (1 - E)) =
      E * (g * h) * E + (1 - E) * (g * h) * (1 - E) := by
  have h1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h3 : (1 - E) * (1 - E) = 1 - E := by rw [mul_sub, mul_one, h2, sub_zero]
  set F := 1 - E with hF
  have hs : E + F = 1 := by rw [hF]; abel
  have a1 : E * (g * h) * E = E * g * E * h * E := by
    calc E * (g * h) * E = E * g * (E + F) * h * E := by rw [hs]; noncomm_ring
      _ = E * g * E * h * E + E * g * (F * h * E) := by noncomm_ring
      _ = _ := by rw [hh, mul_zero, add_zero]
  have a2 : F * (g * h) * F = F * g * F * h * F := by
    calc F * (g * h) * F = F * g * (E + F) * h * F := by rw [hs]; noncomm_ring
      _ = (F * g * E) * h * F + F * g * F * h * F := by noncomm_ring
      _ = _ := by rw [hg, zero_mul, zero_mul, zero_add]
  rw [a1, a2]
  calc _ = E * g * (E * E) * h * E + E * g * (E * F) * h * F + F * g * (F * E) * h * E
        + F * g * (F * F) * h * F := by noncomm_ring
    _ = _ := by rw [hE, h1, h2, h3]; noncomm_ring

private lemma idempotent_corner_sum_one {A : Type} [Ring A] (E : A) (hE : E * E = E) :
    E * 1 * E + (1 - E) * 1 * (1 - E) = 1 := by
  have : E * 1 * E + (1 - E) * 1 * (1 - E) = 1 + 2 * (E * E - E) := by noncomm_ring
  rw [this, hE, sub_self, mul_zero, add_zero]

private lemma idempotent_corner_part_inv {A : Type} [Ring A] (E g h : A) (hE : E * E = E)
    (hg : (1 - E) * g * E = 0) (hh : (1 - E) * h * E = 0) (hgh : g * h = 1) :
    g * (E * h * E + (1 - E) * h * (1 - E)) = 1 + E * (-(g * E * h) * (1 - E)) := by
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  set F := 1 - E with hF
  have hs : E + F = 1 := by rw [hF]; abel
  have a1 : E * g * E = g * E := by
    calc E * g * E = E * g * E + F * g * E := by rw [hg, add_zero]
      _ = (E + F) * g * E := by noncomm_ring
      _ = _ := by rw [hs, one_mul]
  have a2 : h = (E * h * E + F * h * F) + E * h * F := by
    calc h = (E + F) * h * (E + F) := by rw [hs, one_mul, mul_one]
      _ = (E * h * E + F * h * F) + E * h * F + F * h * E := by noncomm_ring
      _ = _ := by rw [hh, add_zero]
  have a3 : g * (E * h * E + F * h * F) + g * (E * h * F) = 1 := by
    rw [← mul_add, ← a2, hgh]
  calc g * (E * h * E + F * h * F) = 1 - g * E * h * F := by
        rw [← a3]; noncomm_ring
    _ = 1 - E * g * E * h * F := by rw [a1]
    _ = _ := by noncomm_ring

theorem isPre_blk_image :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsPre Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → IsPre (blk e '' Γ) := by
  intro ι _ _ Γ e hΓ he htri
  have hE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, he]
  have hmul : ∀ g ∈ Γ, ∀ h ∈ Γ, blk e g * blk e h = blk e (g * h) := fun g hg h hh =>
    idempotent_corner_part_mul _ g h hE (htri g hg) (htri h hh)
  have hone : blk e (1 : Matrix ι ι ℂ) = 1 := idempotent_corner_sum_one _ hE
  have hga : ∀ g ∈ Γ, g * g.adjugate = 1 := fun g hg => by
    rw [Matrix.mul_adjugate, hΓ.det_eq g hg, one_smul]
  have hinv : ∀ g ∈ Γ, blk e g * blk e g.adjugate = 1 := fun g hg => by
    rw [hmul g hg _ (hΓ.adj_mem g hg), hga g hg, hone]
  have hdet : ∀ g ∈ Γ, (blk e g).det = 1 := fun g hg => by
    have h1 := idempotent_corner_part_inv _ g g.adjugate hE (htri g hg) (htri _ (hΓ.adj_mem g hg)) (hga g hg)
    have h2 : (g * blk e g.adjugate).det = 1 := by
      unfold blk
      rw [h1, Matrix.det_one_add_mul_comm, mul_assoc, sub_mul, one_mul, hE, sub_self, mul_zero,
        add_zero, Matrix.det_one]
    rw [Matrix.det_mul, hΓ.det_eq g hg, one_mul] at h2
    have h3 := congrArg Matrix.det (hinv g hg)
    rwa [Matrix.det_mul, h2, mul_one, Matrix.det_one] at h3
  refine ⟨⟨1, hΓ.one_mem, hone⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    exact ⟨g * h, hΓ.mul_mem g hg h hh, (hmul g hg h hh).symm⟩
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨g.adjugate, hΓ.adj_mem g hg, ?_⟩
    calc blk e g.adjugate = ((blk e g).adjugate * blk e g) * blk e g.adjugate := by
          rw [Matrix.adjugate_mul, hdet g hg, one_smul, one_mul]
      _ = _ := by rw [mul_assoc, hinv g hg, mul_one]
  · rintro _ ⟨g, hg, rfl⟩
    exact hdet g hg
  · rintro σ _ ⟨g, hg, rfl⟩
    refine ⟨g.map σ, hΓ.aut_mem σ g hg, ?_⟩
    have hσ : (σ : ℂ →+* ℂ).mapMatrix (e.map (algebraMap ℚ ℂ)) = e.map (algebraMap ℚ ℂ) := by
      ext i j
      simp
    change _ = (σ : ℂ →+* ℂ).mapMatrix (blk e g)
    unfold blk
    rw [map_add, map_mul, map_mul, map_mul, map_mul, map_sub, map_one, hσ]
    rfl

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsClosedImageSLUnderGeneratingInvariants
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open MvPolynomial

variable {ι : Type}

theorem evC_aeval_invariants {κ : Type} (Φ : κ → MvPolynomial (ι × ι) ℂ) (P : MvPolynomial κ ℂ)
    (y : Matrix ι ι ℂ) : evC (aeval Φ P) y = eval (fun k => evC (Φ k) y) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq => simp only [evC, map_add] at *; rw [hp, hq]
  | mul_X p n hp => simp only [evC, map_mul, aeval_X, eval_X] at *; rw [hp]

theorem evC_det_generic [Fintype ι] [DecidableEq ι] (y : Matrix ι ι ℂ) :
    evC (Matrix.of fun i j : ι => (X (i, j) : MvPolynomial (ι × ι) ℂ)).det y = y.det := by
  unfold evC
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem exists_evC_eq_of_relations [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ]
    (Φ : κ → MvPolynomial (ι × ι) ℂ) (hR : IsReynolds Γ Rey) (hΦ : ∀ k, IsInv Γ (Φ k))
    (hgen : ∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) (z : κ → ℂ)
    (hz : ∀ P : MvPolynomial κ ℂ, aeval Φ P = 0 → eval z P = 0) :
    ∃ y : Matrix ι ι ℂ, z = fun k => evC (Φ k) y := by
  set I : Ideal (MvPolynomial (ι × ι) ℂ) := Ideal.span (Set.range fun k => Φ k - C (z k)) with hI
  have hne : I ≠ ⊤ := by
    intro h
    have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ I := h ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    have hinv : ∀ k, IsInv Γ (Φ k - C (z k)) := by
      intro k g hg y
      have := hΦ k g hg y
      simp only [evC, map_sub, eval_C] at *
      rw [this]
    have hone : Rey 1 = 1 := hR.fix 1 (fun g hg y => by simp [evC])
    have h2 : ∑ k, (Φ k - C (z k)) * Rey (a k) = 1 := by
      rw [← hone, ← ha, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, mul_comm (a k), hR.mul _ _ (hinv k)]
    have h3 : ∀ k, ∃ P : MvPolynomial κ ℂ, aeval Φ P = Rey (a k) := by
      intro k
      have := hgen _ (hR.inv (a k))
      rw [Algebra.adjoin_range_eq_range_aeval] at this
      exact this
    choose P hP using h3
    have h4 := hz (∑ k, (X k - C (z k)) * P k - 1) (by
      simp only [map_sub, map_sum, map_mul, aeval_X, aeval_C, map_one, hP, algebraMap_eq]
      rw [h2, sub_self])
    simp at h4
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨Matrix.of fun i j => x (i, j), funext fun k => ?_⟩
  have hk : Φ k - C (z k) ∈ M := hIM (Ideal.subset_span ⟨k, rfl⟩)
  rw [hx, mem_vanishingIdeal_singleton_iff] at hk
  simp only [map_sub, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, coe_aeval_eq_eval] at hk
  have : evC (Φ k) (Matrix.of fun i j => x (i, j)) = aeval x (Φ k) := rfl
  rw [this]
  exact (sub_eq_zero.1 hk).symm

theorem isClosed_image_invariants :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ] (Φ : κ → MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → (∀ g ∈ Γ, g.det = 1) → (∀ k, IsInv Γ (Φ k)) → (∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) → IsClosed {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} := by
  intro ι _ _ Γ Rey κ _ Φ hR hdet hΦ hgen
  have hD : IsInv Γ (Matrix.of fun i j : ι => (X (i, j) : MvPolynomial (ι × ι) ℂ)).det := by
    intro g hg y
    rw [evC_det_generic, evC_det_generic, det_mul, hdet g hg, one_mul]
  have hD' := hgen _ hD
  rw [Algebra.adjoin_range_eq_range_aeval] at hD'
  obtain ⟨Q, hQ⟩ := hD'
  have hQ' : ∀ y : Matrix ι ι ℂ, eval (fun k => evC (Φ k) y) Q = y.det := by
    intro y
    rw [← evC_aeval_invariants, ← evC_det_generic y, ← hQ]
    rfl
  have hset : {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} =
      {z | eval z Q = 1} ∩ ⋂ P : MvPolynomial κ ℂ, ⋂ _ : aeval Φ P = 0, {z | eval z P = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨by rw [hQ', hy], fun P hP => ?_⟩
      rw [← evC_aeval_invariants, hP]
      simp [evC]
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := exists_evC_eq_of_relations Γ Rey κ Φ hR hΦ hgen z h2
      exact ⟨y, by rw [← hQ', h1], rfl⟩
  rw [hset]
  exact (isClosed_eq (MvPolynomial.continuous_eval Q) continuous_const).inter
    (isClosed_iInter fun P => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval P) continuous_const)

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompletelyReducibleMatrixSetTransposeImage
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private noncomputable def dotPerp (U : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) :=
  U.dualAnnihilator.comap (dotProductEquiv ℂ ι).toLinearMap

private theorem mem_dotPerp (U : Submodule ℂ (ι → ℂ)) (v : ι → ℂ) :
    v ∈ dotPerp U ↔ ∀ w ∈ U, v ⬝ᵥ w = 0 := by
  simp [dotPerp, Submodule.mem_dualAnnihilator, dotProductEquiv]

private theorem dotPerp_isCompl {U U' : Submodule ℂ (ι → ℂ)} (h : IsCompl U U') :
    IsCompl (dotPerp U) (dotPerp U') :=
  (Submodule.orderIsoMapComap (dotProductEquiv ℂ ι)).symm.isCompl (Subspace.isCompl_dualAnnihilator h)

private theorem dotPerp_dotPerp (U : Submodule ℂ (ι → ℂ)) : dotPerp (dotPerp U) = U := by
  ext v
  constructor
  · intro hv
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := U), Submodule.mem_dualCoannihilator]
    intro φ hφ
    obtain ⟨w, rfl⟩ := (dotProductEquiv ℂ ι).surjective φ
    have h := (mem_dotPerp _ v).1 hv w hφ
    rw [dotProduct_comm] at h
    simpa [dotProductEquiv] using h
  · intro hv
    rw [mem_dotPerp]
    intro w hw
    rw [dotProduct_comm]
    exact (mem_dotPerp _ w).1 hw v hv

private theorem dotPerp_invariant (U : Submodule ℂ (ι → ℂ)) (g : Matrix ι ι ℂ)
    (h : ∀ v ∈ U, g *ᵥ v ∈ U) : ∀ v ∈ dotPerp U, gᵀ *ᵥ v ∈ dotPerp U := by
  intro v hv
  rw [mem_dotPerp] at hv ⊢
  intro w hw
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  exact hv _ (h w hw)

theorem ss_transpose :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), SS Γ → SS (Matrix.transpose '' Γ) := by
  intro ι _ _ Γ hΓ W hW
  obtain ⟨U', hU', hc⟩ := hΓ (dotPerp W) (fun g hg => by
    simpa using dotPerp_invariant W gᵀ (hW _ ⟨g, hg, rfl⟩))
  refine ⟨dotPerp U', ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact dotPerp_invariant U' g (hU' g hg)
  · have := dotPerp_isCompl hc
    rwa [dotPerp_dotPerp] at this

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsFiniteAdeleLikePairElementary
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem AdelicPair.exists_mul_mem {R : Type} [CommRing R] [Algebra ℚ R] {R₀ : Subring R}
    (h : AdelicPair R R₀) (r : R) : ∃ M : ℕ, 0 < M ∧ (M : R) * r ∈ R₀ := by
  obtain ⟨q, a, ha, e⟩ := h.approx 1 one_pos r
  refine ⟨q.den, q.den_pos, ?_⟩
  have h1 : (q.den : R) * algebraMap ℚ R q = (q.num : R) := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, ← map_intCast (algebraMap ℚ R)]
    congr 1
    exact Rat.den_mul_eq_num q
  rw [e, mul_add, h1]
  exact R₀.add_mem (intCast_mem R₀ _)
    (R₀.mul_mem (natCast_mem R₀ _) (R₀.mul_mem (natCast_mem R₀ _) ha))

theorem AdelicPair.exists_mul_mem_family {R : Type} [CommRing R] [Algebra ℚ R] {R₀ : Subring R}
    (h : AdelicPair R R₀) (κ : Type) [Fintype κ] (r : κ → R) :
    ∃ M : ℕ, 0 < M ∧ ∀ k, (M : R) * r k ∈ R₀ := by
  classical
  choose m hm hmem using fun k => h.exists_mul_mem (r k)
  refine ⟨∏ k, m k, Finset.prod_pos fun k _ => hm k, fun k => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ m (Finset.mem_univ k), Nat.cast_mul, mul_assoc]
  exact R₀.mul_mem (natCast_mem R₀ _) (hmem k)

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_pos_nat_clearing_rat_denominators {κ : Type} [Fintype κ] (q : κ → ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∀ k, ∃ z : ℤ, (M : ℚ) * q k = z := by
  refine ⟨∏ k, (q k).den, Finset.prod_pos fun k _ => (q k).pos, fun k => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun k => (q k).den) (Finset.mem_univ k)
  refine ⟨m * (q k).num, ?_⟩
  rw [hm]
  push_cast
  calc ((q k).den : ℚ) * m * q k = m * (q k * (q k).den) := by ring
    _ = m * (q k).num := by rw [Rat.mul_den_eq_num]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.adelicPair_elementary : ∀ (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), _root_.GlobalTheory.ClassFin.AdelicPair R R₀ → (∀ M : ℕ, 0 < M → ∀ r ∈ R₀, ∃ z : ℤ, ∃ a ∈ R₀, r = (z : R) + (M : R) * a) ∧ (∀ (κ : Type) [Fintype κ] (r : κ → R), ∃ M : ℕ, 0 < M ∧ ∀ k, (M : R) * r k ∈ R₀) ∧ Function.Injective (algebraMap ℚ R) := by
  intro R _ _ R₀ hR
  refine ⟨fun M hM r hr => ?_, fun κ _ r => ?_, ?_⟩
  · obtain ⟨q, a, ha, hra⟩ := hR.approx M hM r
    have hq : algebraMap ℚ R q ∈ R₀ := by
      have h : algebraMap ℚ R q = r - (M : R) * a := by rw [hra]; ring
      rw [h]
      exact R₀.sub_mem hr (R₀.mul_mem (natCast_mem R₀ M) ha)
    obtain ⟨z, rfl⟩ := hR.int_of_mem q hq
    exact ⟨z, a, ha, by rw [hra, map_intCast]⟩
  · choose q a ha hra using fun k => hR.approx 1 one_pos (r k)
    obtain ⟨M, hM, hMq⟩ := exists_pos_nat_clearing_rat_denominators q
    refine ⟨M, hM, fun k => ?_⟩
    obtain ⟨z, hz⟩ := hMq k
    have h : (M : R) * r k = (z : R) + (M : R) * a k := by
      rw [hra k, Nat.cast_one, one_mul, mul_add, ← map_natCast (algebraMap ℚ R) M, ← map_mul, hz,
        map_intCast]
    rw [h]
    exact R₀.add_mem (intCast_mem R₀ z) (R₀.mul_mem (natCast_mem R₀ M) (ha k))
  · have : Nontrivial R := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      obtain ⟨z, hz⟩ := hR.int_of_mem (1 / 2)
        (by rw [Subsingleton.elim (algebraMap ℚ R (1 / 2)) 0]; exact R₀.zero_mem)
      have h2 : (1 : ℚ) = 2 * z := by rw [← hz]; norm_num
      have h3 : (1 : ℤ) = 2 * z := by exact_mod_cast h2
      omega
    exact (algebraMap ℚ R).injective

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsLogKronecker
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem isLog_kronecker {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} [Fintype κ] [DecidableEq κ]
    {H A : Matrix ι ι ℂ} {H' A' : Matrix κ κ ℂ} (h : IsLog H A) (h' : IsLog H' A') :
    IsLog (H ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ H') (A ⊗ₖ A') := by
  obtain ⟨U, d, hU, rfl, rfl⟩ := h
  obtain ⟨U', d', hU', rfl, rfl⟩ := h'
  refine ⟨U ⊗ₖ U', fun p => d p.1 + d' p.2, ?_, ?_, ?_⟩
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, hU', one_kronecker_one]
  · have e : (diagonal (fun p : ι × κ => ((d p.1 + d' p.2 : ℝ) : ℂ))) =
        diagonal (fun i => (d i : ℂ)) ⊗ₖ (1 : Matrix κ κ ℂ) +
          (1 : Matrix ι ι ℂ) ⊗ₖ diagonal (fun i => (d' i : ℂ)) := by
      rw [← diagonal_one, ← diagonal_one, diagonal_kronecker_diagonal, diagonal_kronecker_diagonal,
        diagonal_add]
      congr 1
      funext p
      simp
    rw [e, conjTranspose_kronecker, Matrix.mul_add, Matrix.add_mul, ← mul_kronecker_mul,
      ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one,
      hU, hU']
  · have e : (diagonal (fun p : ι × κ => ((Real.exp (d p.1 + d' p.2) : ℝ) : ℂ))) =
        diagonal (fun i => (Real.exp (d i) : ℂ)) ⊗ₖ diagonal (fun i => (Real.exp (d' i) : ℂ)) := by
      rw [diagonal_kronecker_diagonal]
      congr 1
      funext p
      rw [Real.exp_add, Complex.ofReal_mul]
    rw [e, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

theorem harm_kronecker : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ) (g' : σ → Matrix κ κ ℂ), Harm g → Harm g' → Harm (fun s => g s ⊗ₖ g' s) := by
  intro ι _ _ κ _ _ σ _ g g' ⟨H, hH, hs⟩ ⟨H', hH', hs'⟩
  refine ⟨fun s => H s ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ H' s, fun s => ?_, ?_⟩
  · have := isLog_kronecker (hH s) (hH' s)
    simpa only [conjTranspose_kronecker, ← mul_kronecker_mul] using this
  · ext ⟨i, k⟩ ⟨j, l⟩
    have h1 : ∑ s, H s i j = 0 := by
      have := congrFun (congrFun hs i) j
      simpa [Matrix.sum_apply] using this
    have h2 : ∑ s, H' s k l = 0 := by
      have := congrFun (congrFun hs' k) l
      simpa [Matrix.sum_apply] using this
    simp only [Matrix.sum_apply, Matrix.add_apply, kroneckerMap_apply, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, h1, h2, Matrix.zero_apply]
    simp

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNilpotentTmulSubTmulOfConstOnFibres
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem isNilpotent_of_forall_algHom_eq_zero (T : Type) [CommRing T] [Algebra ℂ T]
    [Algebra.FiniteType ℂ T] (x : T) (h : ∀ ω : T →ₐ[ℂ] ℂ, ω x = 0) : IsNilpotent x := by
  have hJ : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := ℂ)
  have h1 : x ∈ Ideal.jacobson (⊥ : Ideal T) := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    let := Ideal.Quotient.field m
    have hfin : Module.Finite ℂ (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (T ⧸ m)
    have hb : Function.Bijective (algebraMap ℂ (T ⧸ m)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : ℂ ≃ₐ[ℂ] (T ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (T ⧸ m)) hb
    have := h ((e.symm : (T ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m))
    have h0 : e.symm (Ideal.Quotient.mk m x) = 0 := this
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff _ e.symm.injective).mp h0)
  have h2 : x ∈ Ideal.radical (⊥ : Ideal T) := by
    have := IsJacobsonRing.out hJ (Ideal.radical_isRadical (⊥ : Ideal T))
    rw [← this]
    exact Ideal.jacobson_mono Ideal.le_radical h1
  exact h2

theorem isNilpotent_tmul_sub_tmul_of_const_on_fibres :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A] [Algebra.FiniteType ℂ A] (f : A), (∀ χ χ' : A →ₐ[ℂ] ℂ, (∀ b : B, χ (algebraMap B A b) = χ' (algebraMap B A b)) → χ f = χ' f) → IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f) := by
  intro B A _ _ _ _ _ _ _ f h
  have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ B A
  have : Algebra.FiniteType A (A ⊗[B] A) := inferInstance
  have : Algebra.FiniteType ℂ (A ⊗[B] A) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  apply isNilpotent_of_forall_algHom_eq_zero
  intro ω
  let l : A →ₐ[ℂ] A ⊗[B] A := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[ℂ] A ⊗[B] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A).restrictScalars ℂ
  have := h (ω.comp l) (ω.comp r) (fun b => by
    simp only [AlgHom.comp_apply, l, r, Algebra.TensorProduct.includeLeft_apply,
      AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])
  rw [map_sub, sub_eq_zero]
  exact this

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationOfISupRangeEquivariant
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range :
    ∀ (G : Type) [Group G] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Type) (V : J → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (r : ∀ j, Representation ℂ G (V j)) (p : ∀ j, V j →ₗ[ℂ] W), (∀ j, (r j).IsSemisimpleRepresentation) → (∀ j g v, p j (r j g v) = ρ g (p j v)) → (⨆ j, LinearMap.range (p j)) = ⊤ → ρ.IsSemisimpleRepresentation := by
  intro G _ W _ _ ρ J V _ _ r p hr hp htop
  let f : ∀ j, (r j).IntertwiningMap ρ := fun j => ⟨p j, fun g => LinearMap.ext fun v => hp j g v⟩
  let F : ∀ j, (r j).asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule :=
    fun j => Representation.IntertwiningMap.equivLinearMapAsModule (r j) ρ (f j)
  have hF : ∀ j (v : V j), F j v = p j v := fun j v => rfl
  have hs : ∀ j, IsSemisimpleModule (MonoidAlgebra ℂ G) (LinearMap.range (F j)) := by
    intro j
    haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule (r j)).mp
      (hr j)
    exact IsSemisimpleModule.range (F j)
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' hs ?_
  rw [eq_top_iff]
  intro x _
  have hx : (show W from x) ∈ ⨆ j, LinearMap.range (p j) := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction (fun j => LinearMap.range (p j))
    (motive := fun y : W => (show ρ.asModule from y) ∈ ⨆ j, LinearMap.range (F j)) hx ?_ ?_ ?_
  · rintro j y ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem j ⟨v, hF j v⟩
  · exact Submodule.zero_mem _
  · intro y z hy hz
    exact Submodule.add_mem _ hy hz

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRatZariskiClosurePointsIffOfIsReduced
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem mem_pts_zeroSet_of_isReduced :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S' : Set (MvPolynomial (ι × ι) ℚ)) (R : Type) [CommRing R]
      [Algebra ℚ R] (y : Matrix ι ι R),
      (y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R → ∀ f ∈ S', ev f y = 0) ∧
      (IsReduced R → (∀ f ∈ S', ev f y = 0) → y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R) := by
  intro ι _ _ S' R _ _ y
  refine ⟨fun hy f hf => hy f (fun g hg => hg f hf), fun hR hy f hf => ?_⟩
  have hrad : f ∈ (Ideal.span S').radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    have hx' := MvPolynomial.mem_zeroLocus_iff.1 hx
    exact hf (Matrix.of fun i j => x (i, j)) (fun p hp => hx' p (Ideal.subset_span hp))
  obtain ⟨n, hn⟩ := hrad
  have hle : Ideal.span S' ≤
      RingHom.ker (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => y ij.1 ij.2)) :=
    Ideal.span_le.2 fun p hp => hy p hp
  have h0 := hle hn
  rw [RingHom.mem_ker, map_pow] at h0
  exact IsReduced.eq_zero _ ⟨n, h0⟩

end GlobalTheory.ClassFin
end

