import ReciprocityTheory.DualLattices.IsUnitOfNotMem
import ReciprocityTheory.DualLattices.Bundle0003
import Lemmata.MiscLemmasL.Imports

-- bundled from ReciprocityTheory.DualLattices.EigPowEqOne
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem smul_cancel (hv : v.Integers R) {n : Type} {e : Matrix n n R} (he : e ≠ 0) {x y : R}
    (h : x • e = y • e) : x = y := by
  obtain ⟨i, j, hij⟩ : ∃ i j, e i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact he (Matrix.ext hc)
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1
  have h2 := congrArg (algebraMap R C) h1
  rw [map_mul, map_mul] at h2
  have hne : algebraMap R C (e i j) ≠ 0 := by
    intro h0
    rw [← map_zero (algebraMap R C)] at h0
    exact hij (hv.hom_inj h0)
  exact hv.hom_inj (mul_right_cancel₀ hne h2)

theorem eig_pow_eq_one (hv : v.Integers R) {p : ℕ} [Fact p.Prime] {n : Type} [Fintype n] [DecidableEq n]
    [Algebra ℤ_[p] R] (N : Matrix n n ℤ_[p]) (e : Matrix n n R) (he : e ≠ 0) (x : R)
    (h : N.map (algebraMap ℤ_[p] R) * e = x • e) {m : ℕ} (hN : N ^ m = 1) : x ^ m = 1 := by
  have hpow : ∀ k : ℕ, (N.map (algebraMap ℤ_[p] R)) ^ k * e = x ^ k • e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, h, Matrix.mul_smul, ih, smul_smul, ← pow_succ']
  have hN' : (N.map (algebraMap ℤ_[p] R)) ^ m = 1 := by
    have := congrArg (algebraMap ℤ_[p] R).mapMatrix hN
    rwa [map_pow, map_one, RingHom.mapMatrix_apply] at this
  have h1 := hpow m
  rw [hN', one_mul] at h1
  exact (smul_cancel hv he (by rw [one_smul]; exact h1)).symm

theorem fermat (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] (z : ℤ_[p]) :
    res hv (algebraMap ℤ_[p] R z) ^ p = res hv (algebraMap ℤ_[p] R z) := by
  have hz : z ^ p - z ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
      ZMod.pow_card, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hz
  have hp0 : res hv (p : R) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hpv
  have h0 : res hv (algebraMap ℤ_[p] R (z ^ p - z)) = 0 := by
    rw [← hw, map_mul, map_mul, map_natCast (algebraMap ℤ_[p] R), hp0, mul_zero]
  rw [map_sub, map_sub, map_pow, map_pow, sub_eq_zero] at h0
  exact h0

theorem proj (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Type} [CommGroup G] [Fintype G] (hG : IsUnit (Fintype.card G : R))
    (A : G → Matrix n n ℤ_[p]) (hA : ∀ γ γ', A (γ * γ') = A γ * A γ') (hA1 : A 1 = 1)
    (εT : ι → Matrix n n R) (horth : ∀ i j, εT i * εT j = if i = j then εT i else 0)
    (hsum : ∑ i, εT i = 1) (ψ : ι → G → R)
    (heig : ∀ j γ, (A γ).map (algebraMap ℤ_[p] R) * εT j = ψ j γ • εT j)
    (hsep : ∀ j k, εT j ≠ 0 → εT k ≠ 0 → j ≠ k → ∃ γ, ψ j γ ≠ ψ k γ)
    (i : ι) (hi : εT i ≠ 0) : ∃ j, εT j ≠ 0 ∧ ∀ γ, ψ j γ = ψ i γ ^ p := by
  classical
  have hApow : ∀ γ (k : ℕ), A (γ ^ k) = A γ ^ k := by
    intro γ k
    induction k with
    | zero => simp [hA1]
    | succ k ih => rw [pow_succ, hA, ih, pow_succ]
  have hmul : ∀ j, εT j ≠ 0 → ∀ γ γ', ψ j (γ * γ') = ψ j γ * ψ j γ' := by
    intro j hj γ γ'
    apply smul_cancel hv hj
    have e1 := heig j (γ * γ')
    rw [hA, Matrix.map_mul, Matrix.mul_assoc, heig j γ', Matrix.mul_smul, heig j γ, smul_smul] at e1
    rw [← e1, mul_comm (ψ j γ')]
  have hn1 : 1 ≤ Fintype.card G := Fintype.card_pos
  have hpowG : ∀ j, εT j ≠ 0 → ∀ γ, ψ j γ ^ Fintype.card G = 1 := fun j hj γ =>
    eig_pow_eq_one hv (A γ) (εT j) hj (ψ j γ) (heig j γ) (by rw [← hApow, pow_card_eq_one, hA1])
  have hiv : ∀ j, εT j ≠ 0 → ∀ γ, ψ j γ ^ (Fintype.card G - 1) * ψ j γ = 1 := by
    intro j hj γ
    rw [← pow_succ, Nat.sub_add_cancel hn1, hpowG j hj γ]
  have hsum0 : ∀ χ : G → R, (∀ γ γ', χ (γ * γ') = χ γ * χ γ') → ∀ γ0, χ γ0 ≠ 1 →
      ∑ γ, χ γ = 0 := by
    intro χ hχ γ0 h0
    have e : ∑ γ, χ γ = χ γ0 * ∑ γ, χ γ := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_bijective (γ0 * ·) (Group.mulLeft_bijective γ0) (fun γ => χ γ0 * χ γ) χ
        (fun γ => (hχ γ0 γ).symm)).symm
    have e2 : (1 - χ γ0) * ∑ γ, χ γ = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    have e3 := congrArg (algebraMap R C) e2
    rw [map_mul, map_zero] at e3
    rcases mul_eq_zero.mp e3 with h | h
    · exact absurd (sub_eq_zero.mp (hv.hom_inj (h.trans (map_zero _).symm))).symm h0
    · exact hv.hom_inj (h.trans (map_zero _).symm)
  have hPe : ∀ (c : G → R) j, (∑ γ, c γ • (A γ).map (algebraMap ℤ_[p] R)) * εT j =
      (∑ γ, c γ * ψ j γ) • εT j := by
    intro c j
    rw [Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Matrix.smul_mul, heig, smul_smul]
  have hdecomp : ∀ M : Matrix n n R, M = ∑ j, M * εT j := fun M => by
    rw [← Finset.mul_sum, hsum, Matrix.mul_one]
  by_contra hcon
  push_neg at hcon
  have hP'0 : (∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p • (A γ).map (algebraMap ℤ_[p] R)) = 0 := by
    rw [hdecomp (∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p • (A γ).map (algebraMap ℤ_[p] R))]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : εT j = 0
    · rw [hj, Matrix.mul_zero]
    · rw [hPe (fun γ => (ψ i γ ^ (Fintype.card G - 1)) ^ p) j]
      obtain ⟨γ0, hγ0⟩ := hcon j hj
      have hz := hsum0 (fun γ => (ψ i γ ^ (Fintype.card G - 1)) ^ p * ψ j γ)
        (fun γ γ' => by simp only [hmul i hi, hmul j hj]; ring) γ0 (by
          intro h1
          apply hγ0
          try simp only at h1
          calc ψ j γ0 = (ψ i γ0 ^ (Fintype.card G - 1) * ψ i γ0) ^ p * ψ j γ0 := by
                rw [hiv i hi, one_pow, one_mul]
            _ = ((ψ i γ0 ^ (Fintype.card G - 1)) ^ p * ψ j γ0) * ψ i γ0 ^ p := by ring
            _ = ψ i γ0 ^ p := by rw [h1, one_mul])
      try simp only at hz
      rw [hz, zero_smul]
  have hPi : (∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)) =
      (Fintype.card G : R) • εT i := by
    rw [hdecomp (∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)),
      Finset.sum_eq_single i]
    · rw [hPe (fun γ => ψ i γ ^ (Fintype.card G - 1)) i]
      simp only [hiv i hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · intro j _ hji
      by_cases hj : εT j = 0
      · rw [hj, Matrix.mul_zero]
      · rw [hPe (fun γ => ψ i γ ^ (Fintype.card G - 1)) j]
        obtain ⟨γ0, hγ0⟩ := hsep j i hj hi hji
        have hz := hsum0 (fun γ => ψ i γ ^ (Fintype.card G - 1) * ψ j γ)
          (fun γ γ' => by simp only [hmul i hi, hmul j hj]; ring) γ0 (by
            intro h1
            apply hγ0
            try simp only at h1
            calc ψ j γ0 = (ψ i γ0 ^ (Fintype.card G - 1) * ψ i γ0) * ψ j γ0 := by
                  rw [hiv i hi, one_mul]
              _ = (ψ i γ0 ^ (Fintype.card G - 1) * ψ j γ0) * ψ i γ0 := by ring
              _ = ψ i γ0 := by rw [h1, one_mul])
        try simp only at hz
        rw [hz, zero_smul]
    · simp
  obtain ⟨a, b, hab⟩ : ∃ a b, εT i a b ∉ mI hv := by
    by_contra hc
    push_neg at hc
    exact hi (idem_eq_zero hv (εT i) (by rw [horth, if_pos rfl]) hc)
  haveI := charP p hv hpv
  have hfrob : res hv ((∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p •
      (A γ).map (algebraMap ℤ_[p] R)) a b) =
      res hv ((∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)) a b) ^ p := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum, map_mul,
      map_pow]
    rw [sum_pow_char]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [mul_pow, fermat p hv hpv]
  have hres_n : res hv (Fintype.card G : R) ≠ 0 := by
    intro h0
    have h1 : IsUnit (res hv (Fintype.card G : R)) := hG.map (res hv)
    rw [h0] at h1
    exact not_isUnit_zero h1
  have hres_e : res hv (εT i a b) ≠ 0 := by
    intro h0
    exact hab (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  rw [hP'0, hPi] at hfrob
  simp only [Matrix.zero_apply, map_zero, Matrix.smul_apply, smul_eq_mul, map_mul] at hfrob
  exact pow_ne_zero p (mul_ne_zero hres_n hres_e) hfrob.symm

end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
end
end

-- bundled from ReciprocityTheory.DualLattices.ExistsSmulMemOfMemSpan
section
noncomputable section

namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

open Module

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem exists_smul_mem_of_mem_span [IsDomain R] [IsFractionRing R C]
    {V : Type} [AddCommGroup V] [Module C V] [Module R V] [IsScalarTower R C V]
    (S : Submodule R V) {x : V} (hx : x ∈ Submodule.span C (S : Set V)) :
    ∃ r : R, r ≠ 0 ∧ r • x ∈ S := by
  exact Bl.SecondBlockLemmaM.goal1 (C := C) S hx

theorem free_of_finite_torsionFree [IsDomain R] [ValuationRing R] (P : Type) [AddCommGroup P]
    [Module R P] [Module.Finite R P] (h : ∀ (r : R) (x : P), r ≠ 0 → r • x = 0 → x = 0) :
    Module.Free R P := by
  have : Module.Flat R P := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
    exact h a x (nonZeroDivisors.ne_zero a.2) ha
  exact Module.free_of_flat_of_isLocalRing

theorem algebraMap_ne_zero [IsFractionRing R C] {r : R} (hr : r ≠ 0) : algebraMap R C r ≠ 0 := by
  intro h0
  exact hr ((IsFractionRing.injective R C) (by simpa using h0))

theorem isLat_of_fg [IsDomain R] [ValuationRing R] [IsFractionRing R C]
    {X : Type} [Fintype X] [DecidableEq X] (M : Submodule R (X → C)) (hfg : M.FG)
    (hsp : Submodule.span C (M : Set (X → C)) = ⊤) : IsLat R M := by
  have : Module.Finite R M := Module.Finite.iff_fg.2 hfg
  have : Module.Free R M := free_of_finite_torsionFree M (by
    rintro r ⟨x, hx⟩ hr h
    have h' : (r • x : X → C) = 0 := by simpa using congrArg Subtype.val h
    rw [← algebraMap_smul C r x] at h'
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left (algebraMap_ne_zero hr)))
  let b := Module.Free.chooseBasis R M
  let v : Module.Free.ChooseBasisIndex R M → X → C := fun i => (b i : X → C)
  have hR : LinearIndependent R v := b.linearIndependent.map' M.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent C v := (LinearIndependent.iff_fractionRing R C).1 hR
  have hspR : Submodule.span R (Set.range v) = M := by
    have : Set.range v = M.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspC : Submodule.span C (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower R, hspR, hsp]
  let bC := Basis.mk hC (by rw [hspC])
  have hcard : Fintype.card X = Fintype.card (Module.Free.ChooseBasisIndex R M) := by
    rw [← Module.finrank_fintype_fun_eq_card (R := C), Module.finrank_eq_card_basis bC]
  let e : X ≃ Module.Free.ChooseBasisIndex R M := Fintype.equivOfCardEq hcard
  refine ⟨fun x j => v (e j) x, ?_, ?_⟩
  · have hli : LinearIndependent C (fun j x => v (e j) x) := hC.comp e e.injective
    have hu := (Matrix.linearIndependent_cols_iff_isUnit (A := (fun x j => v (e j) x : Matrix X X C))).1
      (by convert hli using 1; rfl)
    exact (Matrix.isUnit_iff_isUnit_det _).1 hu
  · have : Set.range (fun j x => v (e j) x) = Set.range v := by
      ext f; constructor
      · rintro ⟨j, rfl⟩; exact ⟨e j, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨e.symm i, by simp⟩
    rw [this, hspR]

theorem fg_of_isLat {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)}
    (h : IsLat R M) : M.FG := by
  obtain ⟨B, -, rfl⟩ := h
  exact Submodule.fg_span (Set.finite_range _)

theorem span_top_of_isLat {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)}
    (h : IsLat R M) : Submodule.span C (M : Set (X → C)) = ⊤ := by
  obtain ⟨B, hB, rfl⟩ := h
  rw [Submodule.span_span_of_tower]
  have hli : LinearIndependent C (fun j x => B x j) := by
    have := (Matrix.linearIndependent_cols_iff_isUnit (A := B)).2 ((Matrix.isUnit_iff_isUnit_det B).2 hB)
    convert this using 1; rfl
  exact hli.span_eq_top_of_card_eq_finrank' (by simp)

theorem exists_proj [IsDomain R] [ValuationRing R] [IsFractionRing R C]
    {X : Type} [Fintype X] (A : Submodule R (X → C)) (hfg : A.FG)
    (hsp : Submodule.span C (A : Set (X → C)) = ⊤) (W : Submodule C (X → C)) :
    ∃ E : (X → C) →ₗ[C] (X → C), (∀ f ∈ A, E f ∈ A ∧ E f ∈ W) ∧ ∀ f ∈ W, E f = f := by
  classical
  let P : Submodule R A := (W.restrictScalars R).comap A.subtype
  have : Module.Finite R A := Module.Finite.iff_fg.2 hfg
  have : Module.Free R (A ⧸ P) := free_of_finite_torsionFree _ (by
    intro r x hr hx
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective P x
    rw [← map_smul, ← LinearMap.mem_ker, Submodule.ker_mkQ] at hx
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    have hx' : ((r • a : A) : X → C) ∈ W := hx
    show (a : X → C) ∈ W
    have : (a : X → C) = (algebraMap R C r)⁻¹ • ((r • a : A) : X → C) := by
      rw [Submodule.coe_smul, ← algebraMap_smul C r (a : X → C), smul_smul,
        inv_mul_cancel₀ (algebraMap_ne_zero hr), one_smul]
    rw [this]; exact W.smul_mem _ hx')
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ LinearMap.id
    (Submodule.mkQ_surjective P)
  have hs' : ∀ y, P.mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  let S : Submodule R (X → C) := LinearMap.range (A.subtype ∘ₗ s)
  let W' : Submodule C (X → C) := Submodule.span C (S : Set (X → C))
  have hdec : ∀ a : A, ((a - s (P.mkQ a) : A) : X → C) ∈ W := by
    intro a
    have h2 : P.mkQ (a - s (P.mkQ a)) = 0 := by rw [map_sub, hs', sub_self]
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at h2
    exact h2
  have hSW' : ∀ a : A, ((s (P.mkQ a) : A) : X → C) ∈ W' :=
    fun a => Submodule.subset_span ⟨P.mkQ a, rfl⟩
  have hcompl : IsCompl W W' := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxW hxW'
      obtain ⟨r, hr, hrx⟩ := exists_smul_mem_of_mem_span S hxW'
      obtain ⟨y, hy⟩ := hrx
      have hyW : ((s y : A) : X → C) ∈ W := by
        have : ((s y : A) : X → C) = r • x := hy
        rw [this, ← algebraMap_smul C r x]; exact W.smul_mem _ hxW
      have hy0 : y = 0 := by
        rw [← hs' y, ← LinearMap.mem_ker, Submodule.ker_mkQ]; exact hyW
      have : r • x = 0 := by rw [← hy]; simp [hy0]
      rw [← algebraMap_smul C r x] at this
      exact (smul_eq_zero.1 this).resolve_left (algebraMap_ne_zero hr)
    · rw [codisjoint_iff, eq_top_iff, ← hsp, Submodule.span_le]
      intro f hf
      have : f = ((⟨f, hf⟩ - s (P.mkQ ⟨f, hf⟩) : A) : X → C) + ((s (P.mkQ ⟨f, hf⟩) : A) : X → C) := by
        simp
      rw [this]
      exact Submodule.add_mem_sup (hdec _) (hSW' _)
  have hc : IsCompl (LinearMap.range W.subtype) W' := by rw [Submodule.range_subtype]; exact hcompl
  let E : (X → C) →ₗ[C] (X → C) :=
    W.subtype ∘ₗ LinearMap.linearProjOfIsCompl W' W.subtype W.injective_subtype hc
  have hEW : ∀ f ∈ W, E f = f := by
    intro f hf
    have : E (W.subtype ⟨f, hf⟩) = W.subtype ⟨f, hf⟩ := by
      simp only [E, LinearMap.comp_apply, LinearMap.linearProjOfIsCompl_apply_left]
    simpa using this
  have hEW' : ∀ f ∈ W', E f = 0 := by
    intro f hf
    simp only [E, LinearMap.comp_apply,
      LinearMap.linearProjOfIsCompl_apply_right' W' W.subtype W.injective_subtype hc f hf, map_zero]
  refine ⟨E, ?_, hEW⟩
  intro f hf
  have hsplit : f = ((⟨f, hf⟩ - s (P.mkQ ⟨f, hf⟩) : A) : X → C) + ((s (P.mkQ ⟨f, hf⟩) : A) : X → C) := by
    simp
  have : E f = ((⟨f, hf⟩ - s (P.mkQ ⟨f, hf⟩) : A) : X → C) := by
    conv_lhs => rw [hsplit]
    rw [map_add, hEW _ (hdec _), hEW' _ (hSW' _), add_zero]
  rw [this]
  exact ⟨Subtype.prop _, hdec _⟩

end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
end
end

-- bundled from ReciprocityTheory.DualLattices.MapSmulOneMulVec
section
namespace ReciprocityTheory.PGsh

open Matrix

private theorem smul_one_mulVec_dual_lattices {D n : Type*} [CommRing D] [Fintype n] [DecidableEq n] (c : D)
    (v : n → D) : (c • (1 : Matrix n n D)) *ᵥ v = c • v := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

private lemma map_smul_one_mulVec {D K n : Type*} [CommRing D] [Field K] [Algebra D K]
    [Fintype n] [DecidableEq n] (c : D) (v : n → K) :
    ((c • (1 : Matrix n n D)).map (algebraMap D K)) *ᵥ v = c • v := by
  have h : ((c • (1 : Matrix n n D)).map (algebraMap D K)) = (algebraMap D K c) • (1 : Matrix n n K) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [h, smul_one_mulVec_dual_lattices, algebraMap_smul]

private theorem exists_mulVec_eq_smul_of_mul_eq_smul_one {D p n : Type*} [CommRing D] [Fintype n] [Fintype p]
    [DecidableEq p] (H : Matrix p n D) (L : Matrix n p D) (c : D) (h : H * L = c • 1) (f : p → D) :
    ∃ t : n → D, H *ᵥ t = c • f :=
  ⟨L *ᵥ f, by rw [Matrix.mulVec_mulVec, h, smul_one_mulVec_dual_lattices]⟩

private theorem exists_integral_smul_of_mulVec_integral {D K p n : Type*} [CommRing D] [Field K] [Algebra D K]
    [Fintype n] [Fintype p] [DecidableEq p] (B : Matrix p n D) (W : Matrix n p D) (c : D)
    (h : B * W = c • 1) (x : p → K) (w : n → D)
    (hx : W.map (algebraMap D K) *ᵥ x = algebraMap D K ∘ w) :
    ∃ y : p → D, c • x = algebraMap D K ∘ y := by
  refine ⟨B *ᵥ w, ?_⟩
  rw [← map_smul_one_mulVec c x, ← h, Matrix.map_mul, ← Matrix.mulVec_mulVec, hx]
  funext i
  exact (RingHom.map_mulVec (algebraMap D K) B w i).symm

private theorem exists_mulVec_eq_of_mulVec_eq_zero {D K p n : Type*} [CommRing D] [Field K] [Algebra D K]
    [IsFractionRing D K] [Fintype n] [DecidableEq n] [Fintype p] (H B : Matrix p n D)
    (L W : Matrix n p D) (c : D) (hc : c ≠ 0) (h : L * H + W * B = c • 1) (t : n → K)
    (ht : H.map (algebraMap D K) *ᵥ t = 0) :
    ∃ x : p → K, W.map (algebraMap D K) *ᵥ x = t := by
  have hc' : algebraMap D K c ≠ 0 := by
    intro h0
    exact hc (IsFractionRing.injective D K (h0.trans (map_zero _).symm))
  have hmap : L.map (algebraMap D K) * H.map (algebraMap D K)
      + W.map (algebraMap D K) * B.map (algebraMap D K)
      = (c • (1 : Matrix n n D)).map (algebraMap D K) := by
    rw [← h, Matrix.map_add _ (fun a b => map_add (algebraMap D K) a b), Matrix.map_mul,
      Matrix.map_mul]
  have e1 : (L.map (algebraMap D K) * H.map (algebraMap D K)) *ᵥ t = 0 := by
    rw [← Matrix.mulVec_mulVec, ht, Matrix.mulVec_zero]
  have hWB : c • t = (W.map (algebraMap D K) * B.map (algebraMap D K)) *ᵥ t := by
    rw [← map_smul_one_mulVec c t, ← hmap, Matrix.add_mulVec, e1, zero_add]
  refine ⟨(algebraMap D K c)⁻¹ • (B.map (algebraMap D K) *ᵥ t), ?_⟩
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hWB, ← algebraMap_smul K c t,
    inv_smul_smul₀ hc']

theorem a1 : ExistsPointLeviLogNormSqPos := by
  unfold ExistsPointLeviLogNormSqPos
  intro D _ _ g E Φ c hE hdiag hdet hc hΦ
  dsimp only
  have hEinv : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E hdet
  have hF : (Eᵀ)⁻¹ = -E⁻¹ := by
    rw [hE]
    exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, hEinv])
  obtain ⟨N, hN⟩ : ∃ N, N = E⁻¹ * Φᵀ * stdJ D g := ⟨_, rfl⟩
  have hNΦ : N * Φ = c • (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) := by
    rw [hN, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Φᵀ, hΦ, Matrix.mul_smul, hEinv]
  have hdetΦ : Φ.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hNΦ
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have hΦN : Φ * N = c • (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) := by
    have h2 : (Φ * N - c • 1) * Φ = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hNΦ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h3 : Φ.det • (Φ * N - c • 1) = 0 := by
      rw [← Matrix.mul_one (Φ * N - c • 1), ← Matrix.mul_smul, ← Matrix.mul_adjugate Φ,
        ← Matrix.mul_assoc (Φ * N - c • 1) Φ (Matrix.adjugate Φ), h2, Matrix.zero_mul]
    have h4 : Φ * N - c • 1 = 0 := by
      ext i j
      have := congrFun (congrFun h3 i) j
      simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_left hdetΦ
    exact sub_eq_zero.mp h4
  have hJJ : stdJ D g * stdJ D g = -1 := by
    rw [stdJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have hG : Φ * E⁻¹ * Φᵀ = -(c • stdJ D g) := by
    have h := congrArg (· * stdJ D g) hΦN
    simp only [hN, Matrix.mul_assoc, hJJ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_neg,
      Matrix.mul_one] at h
    rw [← h, neg_neg, Matrix.mul_assoc]
  have hsub : ∀ r s : Fin g → Fin g ⊕ Fin g,
      Φ.submatrix r id * E⁻¹ * (Φ.submatrix s id)ᵀ = (-(c • stdJ D g)).submatrix r s := by
    intro r s
    rw [← hG]
    ext a b
    rfl
  have hHH : Φ.submatrix Sum.inl id * E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ = 0 := by
    rw [hsub]; ext a b; simp [stdJ]
  have hBH : Φ.submatrix Sum.inr id * E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ
      = -(c • (1 : Matrix (Fin g) (Fin g) D)) := by
    rw [hsub]; ext a b; by_cases h : a = b <;> simp [stdJ, h]
  have hHB : Φ.submatrix Sum.inl id * E⁻¹ * (Φ.submatrix Sum.inr id)ᵀ
      = c • (1 : Matrix (Fin g) (Fin g) D) := by
    rw [hsub]; ext a b; by_cases h : a = b <;> simp [stdJ, h]
  have hJΦ1 : ∀ a j, (stdJ D g * Φ) (Sum.inl a) j = -Φ (Sum.inr a) j := by
    intro a j; simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hJΦ2 : ∀ a j, (stdJ D g * Φ) (Sum.inr a) j = Φ (Sum.inl a) j := by
    intro a j; simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hform : (Φ.submatrix Sum.inr id)ᵀ * Φ.submatrix Sum.inl id
      - (Φ.submatrix Sum.inl id)ᵀ * Φ.submatrix Sum.inr id = c • E := by
    rw [← hΦ]
    ext i j
    rw [Matrix.mul_assoc Φᵀ, Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [hJΦ1, hJΦ2]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      id_eq, mul_neg, Finset.sum_neg_distrib]
    ring
  have hkey : E⁻¹ * (Φ.submatrix Sum.inr id)ᵀ * Φ.submatrix Sum.inl id
      + (-E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ) * Φ.submatrix Sum.inr id = c • 1 := by
    have h := congrArg (E⁻¹ * ·) hform
    simp only [Matrix.mul_sub, Matrix.mul_smul, hEinv] at h
    rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← sub_eq_add_neg]
    exact h
  have h2 : Φ.submatrix Sum.inl id * (-E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ) = 0 := by
    rw [Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hHH, neg_zero]
  have h3 : Φ.submatrix Sum.inr id * (-E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ)
      = c • (1 : Matrix (Fin g) (Fin g) D) := by
    rw [Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hBH, neg_neg]
  have hT : (-E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ)ᵀ = Φ.submatrix Sum.inl id * E⁻¹ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_neg,
      Matrix.transpose_nonsing_inv, hF, neg_neg]
  rw [hF]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exists_mulVec_eq_smul_of_mul_eq_smul_one _ (E⁻¹ * (Φ.submatrix Sum.inr id)ᵀ) c
      (by rw [← Matrix.mul_assoc]; exact hHB)
  · exact h2
  · exact h3
  · rw [hT, Matrix.mul_assoc (Φ.submatrix Sum.inl id) E⁻¹ E, hEinv, Matrix.mul_one]
    exact h2
  · intro t ht
    exact exists_mulVec_eq_of_mulVec_eq_zero _ _ _ _ c hc hkey t ht
  · rintro x ⟨w, hw⟩
    exact exists_integral_smul_of_mulVec_integral _ _ c h3 x w hw

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.SubgroupQuotientStatement
section
noncomputable section

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def SubgroupQuotientStatement : Prop :=
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
    (AA : HopfOrder (C := C) R N),
    (∃ AK : HopfOrder (C := C) R K, AK.carrier = AA.carrier.map (resK K)) ∧
    (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = AA.carrier.comap (pullQ K)) ∧
    dualLat (AA.carrier.map (resK (R := R) K)) = (dualLat AA.carrier).comap (extK K) ∧
    dualLat (AA.carrier.comap (pullQ (R := R) K)) = (dualLat AA.carrier).map (pushQ K)

end ReciprocityTheory.PGsh.L2
end
end

