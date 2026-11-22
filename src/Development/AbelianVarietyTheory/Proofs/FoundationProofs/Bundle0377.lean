import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergOrdinaryOfVanishingOnCycloKernel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GrOfKill

theorem exists_unit_one_add (l : ℕ) [Fact l.Prime] : ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = ((1 + l : ℕ) : ℤ_[l]) := by
  have hu : IsUnit (((1 + l : ℕ) : ℤ_[l])) := by
    push_cast
    rw [← sub_neg_eq_add]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h =>
      PadicInt.irreducible_p.not_isUnit ((IsUnit.neg_iff _).1 h)
  exact ⟨hu.unit, rfl⟩

theorem gr_of_vanish_on_trivial : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W), (∀ g ∈ N0g W, y g = 0) → Gr W A y := by
  intro l _ Ω _ _ _ e S A W hW y hy hN
  set D := Dec (F := ℚ) A with hDdef
  have hup : ∀ s ∈ D, mat W s 1 0 = 0 := hW.upper
  have hmul : ∀ s t, mat W (s * t) = mat W s * mat W t := fun s t => by simp [mat]
  have hone : mat W 1 = 1 := by simp [mat]
  have h00 : ∀ s t, t ∈ D → mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0 := by
    intro s t ht; rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, hup t ht]; ring
  have h11 : ∀ s t, s ∈ D → mat W (s * t) 1 1 = mat W s 1 1 * mat W t 1 1 := by
    intro s t hs; rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, hup s hs]; ring
  have h01 : ∀ s t, t ∈ D → mat W (s * t) 0 1 = mat W s 0 0 * mat W t 0 1 + mat W s 0 1 * mat W t 1 1 := by
    intro s t ht; rw [hmul, Matrix.mul_apply, Fin.sum_univ_two]
  have hcoc : ∀ s t, y (s * t) = y s + mat W s *ᵥ y t := fun s t => by
    have := hy.2 s t
    rw [this]; rfl
  have hy1 : y 1 = 0 := by
    have := hcoc 1 1
    simpa [hone] using this
  have hb : ∀ s t, s ∈ D → y (s * t) 1 = y s 1 + mat W s 1 1 * y t 1 := by
    intro s t hs; rw [hcoc]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hup s hs]

  let P : G ℚ Ω → Prop := fun u => u ∈ D ∧ mat W u 0 0 = 1 ∧ mat W u 1 1 = 1 ∧ cycBar ℚ Ω l u = 1

  have hfac : ∀ u v, P u → P v → mat W u 0 1 = mat W v 0 1 → y u = y v := by
    rintro u v ⟨huD, hu0, hu1, huc⟩ ⟨hvD, hv0, hv1, hvc⟩ h
    have hm : mat W u = mat W v := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [hu0, hv0]
      · exact h
      · simp [hup u huD, hup v hvD]
      · simp [hu1, hv1]
    have hW' : W u = W v := Units.ext hm
    have hn : u⁻¹ * v ∈ N0g W := by
      refine ⟨?_, ?_⟩
      · simp [MonoidHom.mem_ker, map_mul, map_inv, huc, hvc]
      · simp [MonoidHom.mem_ker, map_mul, map_inv, hW']
    have e1 : v = u * (u⁻¹ * v) := by group
    rw [e1, hcoc, hN _ hn, Matrix.mulVec_zero, add_zero]
  have hPmul : ∀ u v, P u → P v → P (u * v) ∧ mat W (u * v) 0 1 = mat W u 0 1 + mat W v 0 1 ∧
      y (u * v) 1 = y u 1 + y v 1 := by
    rintro u v ⟨huD, hu0, hu1, huc⟩ ⟨hvD, hv0, hv1, hvc⟩
    refine ⟨⟨D.mul_mem huD hvD, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [h00 u v hvD, hu0, hv0, one_mul]
    · rw [h11 u v huD, hu1, hv1, one_mul]
    · rw [map_mul, huc, hvc, one_mul]
    · rw [h01 u v hvD, hu0, hv1]; ring
    · rw [hb u v huD, hu1, one_mul]
  have hPpow : ∀ u, P u → ∀ n : ℕ, P (u ^ n) ∧ mat W (u ^ n) 0 1 = n * mat W u 0 1 ∧
      y (u ^ n) 1 = n * y u 1 := by
    intro u hu n
    induction n with
    | zero =>
      refine ⟨⟨D.one_mem, by simp [hone], by simp [hone], by simp⟩, by simp [hone], by simp [hy1]⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := hPmul _ _ ih.1 hu
      rw [pow_succ]
      refine ⟨h1, ?_, ?_⟩
      · rw [h2, ih.2.1]; push_cast; ring
      · rw [h3, ih.2.2]; push_cast; ring

  have hv : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hA, hlv⟩ := hW.atL
    simpa using (hA _).2 hlv
  obtain ⟨u0, hu0⟩ := exists_unit_one_add l
  obtain ⟨t, htI, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u0
  have heps : eps l t = ((1 + l : ℕ) : Qbar l) := by
    simp [eps, cycBar, htu, hu0]
  obtain ⟨m, hm1, hm⟩ := hW.wt
  have htD : t ∈ D := Ine_le_Dec A htI
  have hpow00 : ∀ s ∈ D, ∀ n : ℕ, mat W (s ^ n) 0 0 = mat W s 0 0 ^ n := by
    intro s hs n
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, h00 _ _ hs, ih, pow_succ]
  set T := t ^ (2 * m) with hTdef
  have hTD : T ∈ D := D.pow_mem htD _
  set Nq : ℕ := (1 + l) ^ (2 * (e * m)) with hNq
  have hT00 : mat W T 0 0 = (Nq : Qbar l) := by
    rw [hTdef, hpow00 t htD, pow_mul', hm t htI, heps, hNq]; push_cast; ring
  have hdet : mat W T 0 0 * mat W T 1 1 = 1 := by
    have h2 : dt W t ^ 2 = 1 := by
      have := congrArg (fun f => f t) hW.det2
      simpa using this
    have hdT : dt W T = 1 := by
      rw [hTdef, map_pow, pow_mul, h2, one_pow]
    have h3 : ((dt W T : (Qbar l)ˣ) : Qbar l) = (mat W T).det := rfl
    rw [hdT, Units.val_one, Matrix.det_fin_two, hup T hTD] at h3
    linear_combination -h3
  have hNqne : ∀ k : ℕ, 1 ≤ k → ((Nq ^ k : ℕ) : Qbar l) ≠ 1 := by
    intro k hk h
    have h' : Nq ^ k = 1 := by exact_mod_cast h
    have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
    have hpos : 2 * (e * m) ≠ 0 := by
      have := hW.e_pos; positivity
    have : 1 < Nq ^ k := by
      rw [hNq, ← pow_mul]
      exact Nat.one_lt_pow (by positivity) (by omega)
    omega
  have hTi : T * T⁻¹ = 1 := mul_inv_cancel T
  have hTiD : T⁻¹ ∈ D := D.inv_mem hTD
  have hTi11 : mat W T⁻¹ 1 1 = (Nq : Qbar l) := by
    have := h11 T T⁻¹ hTD
    rw [hTi, hone] at this
    rw [Matrix.one_apply_eq] at this
    linear_combination (-(mat W T⁻¹ 1 1)) * hdet - (mat W T 0 0) * this + hT00
  have hi11 : mat W T 1 1 * mat W T⁻¹ 1 1 = 1 := by
    have := h11 T T⁻¹ hTD
    rw [hTi, hone, Matrix.one_apply_eq] at this
    exact this.symm
  have hinvy : y T 1 + mat W T 1 1 * y T⁻¹ 1 = 0 := by
    have := hb T T⁻¹ hTD
    rw [hTi, hy1] at this
    simpa using this.symm

  have hPconj : ∀ u, P u → P (T * u * T⁻¹) ∧ mat W (T * u * T⁻¹) 0 1 = ((Nq * Nq : ℕ) : Qbar l) * mat W u 0 1 ∧
      y (T * u * T⁻¹) 1 = mat W T 1 1 * y u 1 := by
    rintro u ⟨huD, hu0', hu1, huc⟩
    have hTuD : T * u ∈ D := D.mul_mem hTD huD
    have hi00 : mat W T 0 0 * mat W T⁻¹ 0 0 = 1 := by
      have := h00 T T⁻¹ hTiD
      rw [hTi, hone, Matrix.one_apply_eq] at this
      exact this.symm
    have hi01 : mat W T 0 0 * mat W T⁻¹ 0 1 + mat W T 0 1 * mat W T⁻¹ 1 1 = 0 := by
      have := h01 T T⁻¹ hTiD
      rw [hTi, hone, Matrix.one_apply_ne (by decide)] at this
      exact this.symm
    refine ⟨⟨D.mul_mem hTuD hTiD, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [h00 _ _ hTiD, h00 _ _ huD, hu0', mul_one, hi00]
    · rw [h11 _ _ hTuD, h11 _ _ hTD, hu1, mul_one, hi11]
    · simp [map_mul, map_inv, huc]
    · rw [h01 _ _ hTiD, h01 _ _ huD, h00 _ _ huD, hu0', hu1]
      push_cast
      linear_combination hi01 + mat W u 0 1 * mat W T⁻¹ 1 1 * hT00 + mat W u 0 1 * (Nq : Qbar l) * hTi11
    · rw [mul_assoc, hb T _ hTD, hb u T⁻¹ huD, hu1]
      linear_combination hinvy

  have hvan : ∀ u, P u → y u 1 = 0 := by
    intro u hu
    obtain ⟨hc1, hc2, hc3⟩ := hPconj u hu
    obtain ⟨hp1, hp2, hp3⟩ := hPpow u hu (Nq * Nq)
    have h3 := hfac _ _ hc1 hp1 (by rw [hc2, hp2])
    have h4 : mat W T 1 1 * y u 1 = ((Nq * Nq : ℕ) : Qbar l) * y u 1 := by rw [← hc3, ← hp3, h3]
    have h5 : (((Nq ^ 3 : ℕ) : Qbar l) - 1) * y u 1 = 0 := by
      push_cast at h4 ⊢
      linear_combination (-(Nq : Qbar l)) * h4 + y u 1 * hdet - y u 1 * mat W T 1 1 * hT00
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd (sub_eq_zero.1 h) (hNqne 3 (by norm_num))
    · exact h

  have hT11ne : mat W T 1 1 - 1 ≠ 0 := by
    intro h
    have h' : mat W T 1 1 = 1 := sub_eq_zero.1 h
    rw [h', mul_one, hT00] at hdet
    exact hNqne 1 (by norm_num) (by simpa using hdet)
  refine ⟨y T 1 / (mat W T 1 1 - 1), fun s hs => ?_⟩
  have hsT : s * T ∈ D := D.mul_mem hs hTD
  have hTs : T * s ∈ D := D.mul_mem hTD hs
  have hsTi : (s * T)⁻¹ ∈ D := D.inv_mem hsT
  have hinv00 : mat W (s * T)⁻¹ 0 0 * mat W (s * T) 0 0 = 1 := by
    have := h00 (s * T)⁻¹ (s * T) hsT
    rw [inv_mul_cancel, hone, Matrix.one_apply_eq] at this
    exact this.symm
  have hinv11 : mat W (s * T)⁻¹ 1 1 * mat W (s * T) 1 1 = 1 := by
    have := h11 (s * T)⁻¹ (s * T) hsTi
    rw [inv_mul_cancel, hone, Matrix.one_apply_eq] at this
    exact this.symm
  have hcP : P ((s * T)⁻¹ * (T * s)) := by
    refine ⟨D.mul_mem hsTi hTs, ?_, ?_, ?_⟩
    · rw [h00 _ _ hTs, h00 _ _ hs]
      linear_combination hinv00 - mat W (s * T)⁻¹ 0 0 * h00 s T hTD
    · rw [h11 _ _ hsTi, h11 _ _ hTD]
      linear_combination hinv11 - mat W (s * T)⁻¹ 1 1 * h11 s T hs
    · have hcs : cycBar ℚ Ω l (T * s) = cycBar ℚ Ω l (s * T) := by rw [map_mul, map_mul, mul_comm]
      rw [map_mul, map_inv, hcs, inv_mul_cancel]
  have hyc := hvan _ hcP
  have e1 : (s * T) * ((s * T)⁻¹ * (T * s)) = T * s := by group
  have h6 := hb (s * T) ((s * T)⁻¹ * (T * s)) hsT
  rw [e1, hyc, mul_zero, add_zero, hb T s hTD, hb s T hs] at h6
  have hinv := mul_inv_cancel₀ hT11ne
  rw [div_eq_mul_inv]
  linear_combination (mat W T 1 1 - 1)⁻¹ * h6 - y s 1 * hinv

end GlobalTheory.Ord2.GrOfKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixesRootOfUnity
section
namespace GlobalTheory.InertiaRootOfUnity

theorem eq_one_of_val_sub_lt {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ)
    (N : ℕ) (hN : ¬ w (N : K) < 1) (u : K) (hu : u ^ N = 1) (h : w (u - 1) < 1) : u = 1 := by
  by_contra hne
  have hx : u - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hw1 : w u = 1 := by
    have h' := Valuation.map_add_eq_of_lt_right w (x := u - 1) (y := 1) (by rw [map_one]; exact h)
    rwa [sub_add_cancel, map_one] at h'
  have hpow : ∀ i : ℕ, w (u ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hr : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1) := by ring
      rw [hr]
      refine Valuation.map_add_lt w ?_ h
      rw [map_mul, hw1, one_mul]
      exact ih
  have hsum : ∑ i ∈ Finset.range N, u ^ i = 0 := by
    have hg := geom_sum_mul u N
    rw [hu, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right hx
  have hNeq : (N : K) = -∑ i ∈ Finset.range N, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  apply hN
  rw [hNeq, Valuation.map_neg]
  exact w.map_sum_lt one_ne_zero fun i _ => hpow i

theorem inertia_fixes_root_of_unity {Ω : Type} [Field Ω] [Algebra ℚ Ω] (N : ℕ) (v : GlobalTheory.Ord2.Pl)
    (B : ValuationSubring Ω) (hB : Formalism.ConjugateSelfDual.IsPlaceOver B v)
    (hN : ¬ ((N : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal))
    (s : Formalism.ConjugateSelfDual.G ℚ Ω) (hs : s ∈ ReciprocityTheory.Gal.Ine B) (ζ : Ω) (hζ : ζ ^ N = 1) : s ζ = ζ := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simpa using v.asIdeal.zero_mem)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp [zero_pow hN0] at hζ
  have hwζ : B.valuation ζ = 1 := by
    have hp : B.valuation ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
    rcases lt_trichotomy (B.valuation ζ) 1 with hlt | heq | hgt
    · exact absurd hp (pow_lt_one₀ zero_le' hlt hN0).ne
    · exact heq
    · exact absurd hp (one_lt_pow₀ hgt hN0).ne'
  have hI := (ReciprocityTheory.Gal.mem_Ine.mp hs).2 ζ hwζ.le
  have hsζ : s ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
  have hone := eq_one_of_val_sub_lt B.valuation N ?_ (s ζ * ζ⁻¹) ?_ ?_
  · exact (mul_inv_eq_one₀ hζ0).mp hone
  · intro hlt
    exact hN ((hB N).mp (by simpa using hlt))
  · rw [mul_pow, hsζ, inv_pow, hζ, inv_one, mul_one]
  · have hr : s ζ * ζ⁻¹ - 1 = (s ζ - ζ) * ζ⁻¹ := by field_simp
    rw [hr, map_mul, map_inv₀, hwζ, inv_one, mul_one]
    exact hI

end GlobalTheory.InertiaRootOfUnity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenKerAndIsLocallyConstant
section
namespace GlobalTheory.OpenKernelLocallyConstant

theorem isOpen_ker_and_isLocallyConstant {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (C : Type) [Group C] (N : ℕ) (ψ : Formalism.ConjugateSelfDual.G ℚ Ω →* C) (hN : N ≠ 0)
    (hψ : UpperTheory.V.Af.KillsMu N ψ) :
    IsOpen (↑(MonoidHom.ker ψ) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) ∧
      IsLocallyConstant (⇑ψ : Formalism.ConjugateSelfDual.G ℚ Ω → C) := by
  classical
  have hopen : IsOpen (↑(MonoidHom.ker ψ) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) := by
    have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    let S : Set Ω := {z | z ^ N = 1}
    have hS : S.Finite := by
      refine (Polynomial.nthRoots N (1 : Ω)).toFinset.finite_toSet.subset ?_
      intro z hz
      have hz' : z ^ N = 1 := hz
      simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hN)] using hz'
    have : Finite S := hS.to_subtype
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => (halg.isAlgebraic x).isIntegral
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ S).fixingSubgroup) ?_
      (IntermediateField.fixingSubgroup_isOpen _)
    intro s hs
    rw [MonoidHom.mem_ker]
    refine hψ s ?_
    intro z hz
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs z
      (IntermediateField.subset_adjoin ℚ S hz)
  refine ⟨hopen, ?_⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (MonoidHom.ker ψ : Set (Formalism.ConjugateSelfDual.G ℚ Ω)),
    hopen.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
  intro y hy
  have h : ψ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h.symm

end GlobalTheory.OpenKernelLocallyConstant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsUnitOfForallMaximal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.OddInvolution

theorem exists_pos_pow_idem {M : Type} [Monoid M] [Finite M] (x : M) :
    ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m) := by
  have key : ∀ i d : ℕ, 0 < d → x ^ (i + d) = x ^ i → ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m) := by
    intro i d hd h
    have h1 : ∀ t k : ℕ, x ^ (i + k + t * d) = x ^ (i + k) := by
      intro t k
      induction t with
      | zero => simp
      | succ t ih =>
        have : i + k + (t + 1) * d = (i + d) + (k + t * d) := by ring
        rw [this, pow_add, h, ← pow_add, ← add_assoc, ih]
    have hle : i ≤ (i + 1) * d := by nlinarith
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨(i + 1) * d, by positivity, ?_⟩
    unfold IsIdempotentElem
    rw [← pow_add]
    have := h1 (i + 1) k
    rw [← hk] at this
    exact this
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i (j - i) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h.symm)
  · exact key j (i - j) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h)

theorem pow_idem_field {F : Type} [Field F] {u : F} {m : ℕ} (hm : 0 < m)
    (he : IsIdempotentElem (u ^ m)) : (u = 0 → u ^ m = 0) ∧ (u ≠ 0 → u ^ m = 1) := by
  refine ⟨fun h => by rw [h, zero_pow hm.ne'], fun h => ?_⟩
  have h2 : u ^ m * u ^ m = u ^ m * 1 := by rw [mul_one]; exact he
  exact mul_left_cancel₀ (pow_ne_zero _ h) h2

theorem isUnit_of_forall_maximal {R : Type} [CommRing R] {s : R}
    (h : ∀ m : Ideal R, m.IsMaximal → Ideal.Quotient.mk m s ≠ 0) : IsUnit s := by
  by_contra hs
  obtain ⟨m, hm, hsm⟩ := exists_max_ideal_of_mem_nonunits (show s ∈ nonunits R from hs)
  exact h m hm (Ideal.Quotient.eq_zero_iff_mem.mpr hsm)

theorem exists_anticommuting {R : Type} [CommRing R] [Finite R] (h2 : IsUnit (2 : R))
    (a b c : R) (h : a * a + b * c = 1) :
    ∃ p q r : R, IsUnit (p * p + q * r) ∧ 2 * a * p + b * r + c * q = 0 := by
  obtain ⟨n1, hn1, he1⟩ := exists_pos_pow_idem (b * c)
  obtain ⟨n2, hn2, he2⟩ := exists_pos_pow_idem ((b + c) ^ 2 + 4 * a ^ 2)
  set e1 := (b * c) ^ n1 with he1d
  set e2 := ((b + c) ^ 2 + 4 * a ^ 2) ^ n2 with he2d
  refine ⟨(1 - e1) * e2 * (b + c) + (1 - e1) * (1 - e2) * (b - c),
    e1 * b + (1 - e1) * e2 * (-2 * a) + (1 - e1) * (1 - e2) * (2 * a),
    e1 * (-c) + (1 - e1) * e2 * (-2 * a) + (1 - e1) * (1 - e2) * (-2 * a), ?_, by ring⟩
  apply isUnit_of_forall_maximal
  intro m hm
  letI := Ideal.Quotient.field m
  have h2' : Ideal.Quotient.mk m (2 : R) ≠ 0 := (h2.map (Ideal.Quotient.mk m)).ne_zero
  have hh := congrArg (Ideal.Quotient.mk m) h
  have q1 : Ideal.Quotient.mk m e1 = (Ideal.Quotient.mk m (b * c)) ^ n1 := by rw [he1d, map_pow]
  have q2 : Ideal.Quotient.mk m e2 = (Ideal.Quotient.mk m ((b + c) ^ 2 + 4 * a ^ 2)) ^ n2 := by
    rw [he2d, map_pow]
  have k1 := pow_idem_field hn1 (q1 ▸ he1.map (Ideal.Quotient.mk m))
  have k2 := pow_idem_field hn2 (q2 ▸ he2.map (Ideal.Quotient.mk m))
  rw [← q1] at k1
  rw [← q2] at k2
  simp only [map_add, map_mul, map_sub, map_one, map_neg, map_pow, map_ofNat] at hh k1 k2 h2' ⊢
  generalize Ideal.Quotient.mk m e1 = E1 at k1 k2 ⊢
  generalize Ideal.Quotient.mk m e2 = E2 at k1 k2 ⊢
  generalize Ideal.Quotient.mk m a = A at hh k1 k2 ⊢
  generalize Ideal.Quotient.mk m b = B at hh k1 k2 ⊢
  generalize Ideal.Quotient.mk m c = C at hh k1 k2 ⊢
  have h8 : (2 : R ⧸ m) * 2 * 2 ≠ 0 := by simp [h2']
  by_cases hBC : B * C = 0
  · rw [k1.1 hBC]
    by_cases hU : (B + C) ^ 2 + 4 * A ^ 2 = 0
    · rw [k2.1 hU]
      intro hz
      apply h8
      linear_combination -hz + hU - 8 * hh + 4 * hBC
    · rw [k2.2 hU]
      intro hz
      apply hU
      linear_combination hz
  · rw [k1.2 hBC]
    intro hz
    apply hBC
    linear_combination -hz

theorem exists_swap {R : Type} [CommRing R] [Finite R] (X : Matrix (Fin 2) (Fin 2) R)
    (h2 : IsUnit (2 : R)) (hdet : X.det = -1) (htr : X.trace = 0) :
    ∃ (Y : Matrix (Fin 2) (Fin 2) R) (s : R), IsUnit s ∧ Y * Y = s • (1 : Matrix (Fin 2) (Fin 2) R) ∧
      X * Y = -(Y * X) := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  have hd : X 1 1 = -X 0 0 := by linear_combination htr
  have h : X 0 0 * X 0 0 + X 0 1 * X 1 0 = 1 := by
    rw [hd] at hdet; linear_combination -hdet
  obtain ⟨p, q, r, hs, hanti⟩ := exists_anticommuting h2 (X 0 0) (X 0 1) (X 1 0) h
  refine ⟨!![p, q; r, -p], p * p + q * r, hs, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hd, Matrix.vecMul, dotProduct] <;>
      first | linear_combination hanti | ring

theorem card_fixed_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [Finite R]
    (X : Matrix (Fin 2) (Fin 2) R) (h2 : IsUnit (2 : R)) (hXX : X * X = 1) (hdet : X.det = -1)
    (htr : X.trace = 0) : Nat.card {v : Fin 2 → R // X *ᵥ v = v} = Nat.card R := by
  obtain ⟨Y, s, hs, hYY, hXY⟩ := exists_swap X h2 hdet htr
  have hXXv : ∀ v : Fin 2 → R, X *ᵥ (X *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hXX, Matrix.one_mulVec]
  have hYYv : ∀ v : Fin 2 → R, Y *ᵥ (Y *ᵥ v) = s • v := fun v => by
    rw [Matrix.mulVec_mulVec, hYY]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
  have hXYv : ∀ v : Fin 2 → R, X *ᵥ (Y *ᵥ v) = -(Y *ᵥ (X *ᵥ v)) := fun v => by
    rw [Matrix.mulVec_mulVec, hXY, Matrix.neg_mulVec, Matrix.mulVec_mulVec]
  have hsu : ((hs.unit⁻¹ : Rˣ) : R) * s = 1 := by simp
  let e : {v : Fin 2 → R // X *ᵥ v = v} ≃ {v : Fin 2 → R // X *ᵥ v = -v} :=
    { toFun := fun v => ⟨Y *ᵥ v.1, by rw [hXYv, v.2]⟩
      invFun := fun w => ⟨((hs.unit⁻¹ : Rˣ) : R) • (Y *ᵥ w.1), by
        rw [Matrix.mulVec_smul, hXYv, w.2, Matrix.mulVec_neg, neg_neg]⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp only [hYYv, smul_smul, hsu, one_smul]
      right_inv := fun w => by
        apply Subtype.ext
        simp only [Matrix.mulVec_smul, hYYv, smul_smul, hsu, one_smul] }
  have ht : ((h2.unit⁻¹ : Rˣ) : R) * 2 = 1 := by simp
  set t : R := ((h2.unit⁻¹ : Rˣ) : R)
  let f : (Fin 2 → R) ≃ {v : Fin 2 → R // X *ᵥ v = v} × {v : Fin 2 → R // X *ᵥ v = -v} :=
    { toFun := fun v => (⟨t • (v + X *ᵥ v), by
          rw [Matrix.mulVec_smul, Matrix.mulVec_add, hXXv, add_comm]⟩,
        ⟨t • (v - X *ᵥ v), by
          rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hXXv, ← smul_neg, neg_sub]⟩)
      invFun := fun pq => pq.1.1 + pq.2.1
      left_inv := fun v => by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        linear_combination (v i) * ht
      right_inv := fun pq => by
        obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := pq
        ext i
        · simp only [Matrix.mulVec_add, hp, hq, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
            smul_eq_mul]
          linear_combination (p i) * ht
        · simp only [Matrix.mulVec_add, hp, hq, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
            Pi.sub_apply, smul_eq_mul]
          linear_combination (q i) * ht }
  have h1 : Nat.card (Fin 2 → R) =
      Nat.card {v : Fin 2 → R // X *ᵥ v = v} * Nat.card {v : Fin 2 → R // X *ᵥ v = -v} := by
    rw [Nat.card_congr f, Nat.card_prod]
  have h3 : Nat.card (Fin 2 → R) = Nat.card R * Nat.card R := by
    rw [Nat.card_fun]; simp [sq]
  have hsq : Nat.card {v : Fin 2 → R // X *ᵥ v = v} * Nat.card {v : Fin 2 → R // X *ᵥ v = v} =
      Nat.card R * Nat.card R := by
    rw [← h3, h1, Nat.card_congr e]
  exact Nat.mul_self_inj.mp hsq

theorem card_fixed (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [Finite R]
    (X : Matrix (Fin 2) (Fin 2) R) : IsUnit (2 : R) → X * X = 1 → X.det = -1 → X.trace = 0 →
      Nat.card {v : Fin 2 → R // X *ᵥ v = v} = Nat.card R :=
  fun h2 hXX hdet htr => card_fixed_eq l R X h2 hXX hdet htr

end GlobalTheory.OddInvolution
end

