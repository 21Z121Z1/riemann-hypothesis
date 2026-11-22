import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0035

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralUnitPairingOfIrreducibleReductionA
section
open GlobalTheory.Cong

namespace GlobalTheory.Cong.UnitPairing

open IsLocalRing

variable {R k : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field k]
  [Algebra R k] [IsFractionRing R k] {a : ℕ}

noncomputable def intLattice (W : Submodule k (Fin a → k)) : Submodule R (Fin a → R) :=
  (W.restrictScalars R).comap ((Algebra.linearMap R k).compLeft (Fin a))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R k] in
lemma mem_intLattice {W : Submodule k (Fin a → k)} {x : Fin a → R} :
    x ∈ intLattice (R := R) W ↔ (fun i => algebraMap R k (x i)) ∈ W := Iff.rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma mem_intLattice_of_smul {W : Submodule k (Fin a → k)} {r : R} (hr : r ≠ 0)
    {x : Fin a → R} (h : r • x ∈ intLattice (R := R) W) : x ∈ intLattice (R := R) W := by
  rw [mem_intLattice] at *
  have h' : algebraMap R k r • (fun i => algebraMap R k (x i)) ∈ W := by
    convert h using 1
    ext i
    simp [Algebra.smul_def]
  exact (W.smul_mem_iff ((map_ne_zero_iff _ (IsFractionRing.injective R k)).mpr hr)).mp h'

omit [IsDiscreteValuationRing R] in
lemma exists_integral_multiple (y : Fin a → k) :
    ∃ d : R, d ≠ 0 ∧ ∃ x : Fin a → R,
      (fun i => algebraMap R k (x i)) = algebraMap R k d • y := by
  classical
  obtain ⟨⟨b, hb⟩, h⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ y
  choose x hx using fun i => h i (Finset.mem_univ i)
  refine ⟨b, nonZeroDivisors.ne_zero hb, x, ?_⟩
  ext i
  rw [hx i]
  simp [Algebra.smul_def]

noncomputable def redLattice (L : Submodule R (Fin a → R)) :
    Submodule (ResidueField R) (Fin a → ResidueField R) where
  carrier := {v | ∃ x ∈ L, (fun i => residue R (x i)) = v}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, L.add_mem hx hy, by ext i; simp⟩
  zero_mem' := ⟨0, L.zero_mem, by ext i; simp⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨r • x, L.smul_mem r hx, by ext i; simp⟩

omit [IsFractionRing R k] in
lemma exists_eq_smul_of_residue_eq_zero {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ})
    {x : Fin a → R} (h : (fun i => residue R (x i)) = 0) : ∃ z : Fin a → R, x = ϖ • z := by
  have : ∀ i, ϖ ∣ x i := fun i => by
    have h1 : residue R (x i) = 0 := congrFun h i
    rw [residue_eq_zero_iff, hϖ, Ideal.mem_span_singleton] at h1
    exact h1
  choose z hz using this
  exact ⟨z, funext fun i => by simp [hz i]⟩

theorem main (B : Matrix (Fin a) (Fin a) R)
    (hB : ∀ W : Submodule (ResidueField R) (Fin a → ResidueField R),
      (∀ v ∈ W, (B.map (residue R)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule k (Fin a → k)) (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) :
    ∃ w f : Fin a → R, (fun i => algebraMap R k (w i)) ∈ W ∧
      (∀ y ∈ W, (fun i => algebraMap R k (f i)) ⬝ᵥ y = 0) ∧ IsUnit (f ⬝ᵥ B.mulVec w) := by
  classical
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ : maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  have hϖ0 : ϖ ≠ 0 := hϖirr.ne_zero
  have hϖm : ϖ ∈ maximalIdeal R := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  have hϖres : residue R ϖ = 0 := (residue_eq_zero_iff ϖ).mpr hϖm
  have hinj := IsFractionRing.injective R k
  set L := intLattice (R := R) W with hLdef
  haveI : NoZeroSMulDivisors R ((Fin a → R) ⧸ L) := by
    refine ⟨fun {r q} h => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L q
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      exact (Submodule.Quotient.mk_eq_zero L).mpr (mem_intLattice_of_smul hr h)
  haveI : Module.Free R ((Fin a → R) ⧸ L) := Module.free_of_finite_type_torsion_free'
  have hmemL : ∀ {y : Fin a → k}, y ∈ W → ∀ {d : R} {x : Fin a → R},
      (fun i => algebraMap R k (x i)) = algebraMap R k d • y → x ∈ L := by
    intro y hy d x hx
    show (fun i => algebraMap R k (x i)) ∈ W
    rw [hx]
    exact W.smul_mem _ hy

  have hA : redLattice L ≠ ⊥ := by
    intro hbot
    have hle : L ≤ maximalIdeal R • L := by
      intro x hx
      have h0 : (fun i => residue R (x i)) = 0 := by
        have hm : (fun i => residue R (x i)) ∈ redLattice L := ⟨x, hx, rfl⟩
        rw [hbot] at hm
        exact (Submodule.mem_bot _).mp hm
      obtain ⟨z, rfl⟩ := exists_eq_smul_of_residue_eq_zero hϖ h0
      exact Submodule.smul_mem_smul hϖm (mem_intLattice_of_smul hϖ0 hx)
    have hL : L = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) L
      (IsNoetherian.noetherian L) hle (maximalIdeal_le_jacobson _)
    obtain ⟨y, hyW, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨d, hd, x, hx⟩ := exists_integral_multiple (R := R) y
    have hxL := hmemL hyW hx
    rw [hL, Submodule.mem_bot] at hxL
    subst hxL
    have h2 : algebraMap R k d • y = 0 := by
      rw [← hx]
      ext i
      simp
    rcases smul_eq_zero.mp h2 with h | h
    · exact hd (hinj (by simpa using h))
    · exact hy0 h

  have hT : redLattice L ≠ ⊤ := by
    intro htop
    have hle : (⊤ : Submodule R ((Fin a → R) ⧸ L)) ≤ maximalIdeal R • ⊤ := by
      intro q _
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L q
      have hm : (fun i => residue R (x i)) ∈ redLattice L := htop ▸ Submodule.mem_top
      obtain ⟨l, hl, hlx⟩ := hm
      have h0 : (fun i => residue R ((x - l) i)) = 0 := by
        ext i
        have := congrFun hlx i
        simp only [Pi.sub_apply, map_sub, Pi.zero_apply] at this ⊢
        rw [this, sub_self]
      obtain ⟨z, hz⟩ := exists_eq_smul_of_residue_eq_zero hϖ h0
      have hq : Submodule.Quotient.mk (p := L) x = ϖ • Submodule.Quotient.mk z := by
        rw [← Submodule.Quotient.mk_smul, ← hz, Submodule.Quotient.eq, sub_sub_cancel]
        exact hl
      rw [hq]
      exact Submodule.smul_mem_smul hϖm Submodule.mem_top
    have htopQ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤
      Module.Finite.fg_top hle (maximalIdeal_le_jacobson _)
    apply hWt
    rw [eq_top_iff]
    intro y _
    obtain ⟨d, hd, x, hx⟩ := exists_integral_multiple (R := R) y
    have hxL : x ∈ L := by
      have h1 : Submodule.Quotient.mk (p := L) x ∈ (⊤ : Submodule R ((Fin a → R) ⧸ L)) :=
        Submodule.mem_top
      rw [htopQ] at h1
      exact (Submodule.Quotient.mk_eq_zero L).mp ((Submodule.mem_bot _).mp h1)
    have hdy : algebraMap R k d • y ∈ W := by
      rw [← hx]
      exact hxL
    exact (W.smul_mem_iff ((map_ne_zero_iff _ hinj).mpr hd)).mp hdy

  have hnot : ∃ v ∈ redLattice L, (B.map (residue R)).mulVec v ∉ redLattice L := by
    by_contra hcon
    push_neg at hcon
    rcases hB _ hcon with h | h
    · exact hA h
    · exact hT h
  obtain ⟨_, ⟨w, hwL, rfl⟩, hBw⟩ := hnot
  have hres : (B.map (residue R)).mulVec (fun i => residue R (w i)) =
      fun i => residue R (B.mulVec w i) := by
    ext i
    exact (RingHom.map_mulVec (residue R) B w i).symm
  rw [hres] at hBw
  have hnotsmul : ∀ z : Fin a → R,
      Submodule.Quotient.mk (p := L) (B.mulVec w) ≠ ϖ • Submodule.Quotient.mk z := by
    intro z hz
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hz
    apply hBw
    refine ⟨B.mulVec w - ϖ • z, hz, ?_⟩
    ext i
    simp [hϖres]
  let b := Module.Free.chooseBasis R ((Fin a → R) ⧸ L)
  have hj : ∃ j, b.repr (Submodule.Quotient.mk (B.mulVec w)) j ∉ maximalIdeal R := by
    by_contra hcon
    push_neg at hcon
    have hdv : ∀ j, ϖ ∣ b.repr (Submodule.Quotient.mk (B.mulVec w)) j := fun j => by
      have := hcon j
      rwa [hϖ, Ideal.mem_span_singleton] at this
    choose c hc using hdv
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective L
      (b.repr.symm (Finsupp.equivFunOnFinite.symm c))
    apply hnotsmul z
    apply b.repr.injective
    ext j
    rw [hc j, hz, map_smul, LinearEquiv.apply_symm_apply, Finsupp.smul_apply, smul_eq_mul]
    simp
  obtain ⟨j, hjm⟩ := hj
  let φ : (Fin a → R) →ₗ[R] R := (b.coord j).comp L.mkQ
  have hφ : ∀ x, φ x = b.repr (Submodule.Quotient.mk x) j := fun x => by
    simp [φ, Module.Basis.coord_apply]
  let f : Fin a → R := fun i => φ (fun j' => if i = j' then 1 else 0)
  have hf : ∀ x, f ⬝ᵥ x = φ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ φ x, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [f, smul_eq_mul, mul_comm]
  refine ⟨w, f, hwL, ?_, ?_⟩
  · intro y hy
    obtain ⟨d, hd, x, hx⟩ := exists_integral_multiple (R := R) y
    have hxL := hmemL hy hx
    have hφx : φ x = 0 := by
      rw [hφ, (Submodule.Quotient.mk_eq_zero L).mpr hxL, map_zero, Finsupp.zero_apply]
    have e1 : (fun i => algebraMap R k (f i)) ⬝ᵥ (fun i => algebraMap R k (x i)) =
        algebraMap R k (f ⬝ᵥ x) := by
      simp [dotProduct, map_sum, map_mul]
    rw [hx, dotProduct_smul, smul_eq_mul, hf, hφx, map_zero] at e1
    rcases mul_eq_zero.mp e1 with h | h
    · exact absurd h ((map_ne_zero_iff _ hinj).mpr hd)
    · exact h
  · rw [hf, hφ]
    by_contra hu
    exact hjm ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu))

end GlobalTheory.Cong.UnitPairing

namespace GlobalTheory.Cong

theorem exists_integral_unit_pairing_of_irreducible_reduction : ∀ (R k : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field k] [Algebra R k] [IsFractionRing R k] (a : ℕ) (B : Matrix (Fin a) (Fin a) R), (∀ W : Submodule (IsLocalRing.ResidueField R) (Fin a → IsLocalRing.ResidueField R), (∀ v ∈ W, (B.map (IsLocalRing.residue R)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ W : Submodule k (Fin a → k), W ≠ ⊥ → W ≠ ⊤ → ∃ w f : Fin a → R, (fun i => algebraMap R k (w i)) ∈ W ∧ (∀ y ∈ W, (fun i => algebraMap R k (f i)) ⬝ᵥ y = 0) ∧ IsUnit (f ⬝ᵥ B.mulVec w) := by
  intro R k _ _ _ _ _ _ a B hB W hW0 hWt
  exact UnitPairing.main B hB W hW0 hWt

end GlobalTheory.Cong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantLiftOfTrivial
section
open GlobalTheory.Cong

namespace GlobalTheory

theorem exists_leftInv_rightEquivariant (G A : Type) [Group G] [AddCommGroup A] (Γ C : Subgroup G)
    (lam : C →* Multiplicative A)
    (h : ∀ g : G, ∀ γ ∈ Γ, ∀ c : C, γ * g = g * c → lam c = 1) :
    ∃ ℓ : G → A, (∀ γ ∈ Γ, ∀ g, ℓ (γ * g) = ℓ g) ∧
      ∀ g (c : C), ℓ (g * c) = ℓ g + Multiplicative.toAdd (lam c) := by

  have key : ∀ (s γ γ' : G), γ ∈ Γ → γ' ∈ Γ → ∀ c c' : C,
      γ * s * c = γ' * s * c' → lam c = lam c' := by
    intro s γ γ' hγ hγ' c c' e
    have e2 : (γ'⁻¹ * γ) * s = s * ((c' * c⁻¹ : C) : G) := by
      push_cast
      calc γ'⁻¹ * γ * s = γ'⁻¹ * (γ * s * c) * (c : G)⁻¹ := by group
        _ = γ'⁻¹ * (γ' * s * c') * (c : G)⁻¹ := by rw [e]
        _ = s * ((c' : G) * (c : G)⁻¹) := by group
    have := h s _ (Γ.mul_mem (Γ.inv_mem hγ') hγ) _ e2
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    exact this.symm
  let S : Setoid G :=
    { r := fun a b => ∃ γ ∈ Γ, ∃ c : C, b = γ * a * c
      iseqv := by
        refine ⟨fun a => ⟨1, Γ.one_mem, 1, by simp⟩, ?_, ?_⟩
        · rintro a b ⟨γ, hγ, c, rfl⟩
          exact ⟨γ⁻¹, Γ.inv_mem hγ, c⁻¹, by push_cast; group⟩
        · rintro a b d ⟨γ, hγ, c, rfl⟩ ⟨γ', hγ', c', rfl⟩
          exact ⟨γ' * γ, Γ.mul_mem hγ' hγ, c * c', by push_cast; group⟩ }
  let rep : G → G := fun g => (Quotient.mk S g).out
  have hrep : ∀ g, ∃ c : C, ∃ γ ∈ Γ, g = γ * rep g * c := by
    intro g
    obtain ⟨γ, hγ, c, e⟩ := Quotient.mk_out (s := S) g
    exact ⟨c, γ, hγ, e⟩
  have rep_eq : ∀ a b, S.r a b → rep a = rep b := by
    intro a b hab
    simp only [rep]
    rw [Quotient.sound hab]
  let cf : G → C := fun g => Classical.choose (hrep g)
  have hcf : ∀ g, ∃ γ ∈ Γ, g = γ * rep g * cf g := fun g => Classical.choose_spec (hrep g)
  refine ⟨fun g => Multiplicative.toAdd (lam (cf g)), ?_, ?_⟩
  · intro γ hγ g
    simp only
    congr 1
    have hr : rep (γ * g) = rep g := (rep_eq _ _ ⟨γ, hγ, 1, by simp⟩).symm
    obtain ⟨γ1, hγ1, e1⟩ := hcf (γ * g)
    obtain ⟨γ2, hγ2, e2⟩ := hcf g
    rw [hr] at e1
    apply key (rep g) (γ⁻¹ * γ1) γ2 (Γ.mul_mem (Γ.inv_mem hγ) hγ1) hγ2
    calc γ⁻¹ * γ1 * rep g * (cf (γ * g) : G) = γ⁻¹ * (γ1 * rep g * cf (γ * g)) := by group
      _ = g := by rw [← e1]; group
      _ = γ2 * rep g * cf g := e2
  · intro g c
    simp only
    rw [← toAdd_mul]
    congr 1
    have hr : rep (g * c) = rep g := (rep_eq _ _ ⟨1, Γ.one_mem, c, by simp⟩).symm
    obtain ⟨γ1, hγ1, e1⟩ := hcf (g * c)
    obtain ⟨γ2, hγ2, e2⟩ := hcf g
    rw [hr] at e1
    have := key (rep g) γ1 γ2 hγ1 hγ2 (cf (g * c) * c⁻¹) (cf g) (by
      push_cast
      calc γ1 * rep g * ((cf (g * c) : G) * (c : G)⁻¹) = (γ1 * rep g * cf (g * c)) * (c : G)⁻¹ := by group
        _ = g := by rw [← e1]; group
        _ = γ2 * rep g * cf g := e2)
    rw [map_mul, map_inv] at this
    rw [← this]; group

example : ∀ (G A : Type) [Group G] [AddCommGroup A] (Γ C : Subgroup G) (lam : C →* Multiplicative A), (∀ g : G, ∀ γ ∈ Γ, ∀ c : C, γ * g = g * c → lam c = 1) → ∃ ℓ : G → A, (∀ γ ∈ Γ, ∀ g, ℓ (γ * g) = ℓ g) ∧ ∀ g (c : C), ℓ (g * c) = ℓ g + Multiplicative.toAdd (lam c) := exists_leftInv_rightEquivariant

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixNoInvariantSubspaceFiniteField
section
open GlobalTheory.Cong

namespace GlobalTheory

theorem exists_matrix_no_invariant_subspace :
    ∀ (κ : Type) [Field κ] [Finite κ] (a : ℕ), 1 ≤ a → ∃ B : Matrix (Fin a) (Fin a) κ,
      ∀ W : Submodule κ (Fin a → κ), (∀ v ∈ W, B.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro κ _ _ a ha
  obtain ⟨p, hp⟩ := CharP.exists κ
  haveI : Fact p.Prime := ⟨CharP.char_is_prime κ p⟩
  haveI : NeZero a := ⟨by omega⟩
  let L := FiniteField.Extension κ p a
  let b : Module.Basis (Fin a) κ L :=
    Module.finBasisOfFinrankEq κ L (FiniteField.finrank_extension κ p a)
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Lˣ)
  let β : L := (g : L)
  refine ⟨LinearMap.toMatrix b b (Algebra.lmul κ L β), fun W hW => ?_⟩

  let e := b.equivFun
  have key : ∀ x : L, (LinearMap.toMatrix b b (Algebra.lmul κ L β)).mulVec (e x) = e (β * x) := by
    intro x
    simpa [e, Module.Basis.equivFun_apply] using LinearMap.toMatrix_mulVec_repr b b (Algebra.lmul κ L β) x

  have stepβ : ∀ x : L, e x ∈ W → e (β * x) ∈ W := fun x hx => key x ▸ hW _ hx
  have stepPow : ∀ n : ℕ, ∀ x : L, e x ∈ W → e (β ^ n * x) ∈ W := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have := stepβ _ (ih x hx)
      simpa [pow_succ', mul_assoc] using this
  have stepAll : ∀ y x : L, e x ∈ W → e (y * x) ∈ W := by
    intro y x hx
    by_cases hy : y = 0
    · subst hy; simpa using W.zero_mem
    · obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg (Units.mk0 y hy))
      have : β ^ n = y := by
        have := congrArg (fun u : Lˣ => (u : L)) hn
        simpa [β] using this
      rw [← this]; exact stepPow n x hx
  by_cases h : W = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hx0 : e.symm v ≠ 0 := by
      intro h0; apply hv0; simpa using congrArg e h0
    have hxW : e (e.symm v) ∈ W := by simpa using hvW
    rw [eq_top_iff]
    intro u _
    have := stepAll (e.symm u * (e.symm v)⁻¹) (e.symm v) hxW
    rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one] at this
    simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqFixedUnitHenselian
section
open Polynomial

namespace GlobalTheory.HenselianNorm

theorem exists_mem_add_mul_sq_eq {R : Type*} [CommRing R] (I : Ideal R) [HenselianRing R I]
    (n : R) {e : R} (he : e ∈ I) : ∃ t ∈ I, t + n * t ^ 2 = e := by
  obtain ⟨s, hs, hsI⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 + X - C (n * e))
    (by monicity!) 0
    (by
      simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C]
      simpa using I.mul_mem_left n he)
    (by simp)
  have h0 : eval s (X ^ 2 + X - C (n * e)) = 0 := hs
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h0
  rw [sub_zero] at hsI
  obtain ⟨U, hU⟩ := (Ideal.mem_jacobson_bot.mp (HenselianRing.jac hsI)) 1
  have hinv : (s + 1) * (↑U⁻¹ : R) = 1 := by
    rw [show s + 1 = (U : R) by rw [hU]; ring]
    exact U.mul_inv
  have hnt : n * (e * ↑U⁻¹) = s := by
    linear_combination (-(↑U⁻¹ : R)) * h0 + s * hinv
  refine ⟨e * ↑U⁻¹, I.mul_mem_right _ he, ?_⟩
  linear_combination (e * ↑U⁻¹) * hnt + e * hinv

theorem exists_norm_eq_one_add {R : Type*} [CommRing R] (I : Ideal R) [HenselianRing R I]
    (c : R →+* R) (hc : ∀ x, c (c x) = x) (hI : ∀ x ∈ I, c x ∈ I) {w : R} (hw : w + c w = 1)
    {e : R} (he : e ∈ I) (hce : c e = e) : ∃ x, x * c x = 1 + e := by
  obtain ⟨t, htI, ht⟩ := exists_mem_add_mul_sq_eq I (w * c w) he
  have hct : c t = t := by
    have h1 : c t + w * c w * c t ^ 2 = e := by
      have h := congrArg c ht
      simp only [map_add, map_mul, map_pow, hc, hce] at h
      linear_combination h
    have hm : w * c w * (t + c t) ∈ I := I.mul_mem_left _ (I.add_mem htI (hI t htI))
    obtain ⟨U, hU⟩ := (Ideal.mem_jacobson_bot.mp (HenselianRing.jac hm)) 1
    have hz : (t - c t) * (U : R) = 0 := by
      rw [hU]
      linear_combination ht - h1
    have h2 := (U.isUnit.mul_left_eq_zero).mp hz
    linear_combination -h2
  refine ⟨1 + w * t, ?_⟩
  rw [map_add, map_one, map_mul, hct]
  linear_combination ht + t * hw

theorem exists_norm_eq : ∀ (R : Type) [CommRing R] (I : Ideal R) [HenselianRing R I]
    [Finite (R ⧸ I)] (c : R →+* R), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) →
    (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  intro R _ I _ _ c hc hI hω u hcu hu
  obtain ⟨ω, D, hD⟩ := hω
  have hcD : (c ω - ω) * c ↑D⁻¹ = 1 := by
    have h := congrArg c D.mul_inv
    rw [map_mul, map_one, hD, map_sub, hc] at h
    exact h
  have hw : ω * ↑D⁻¹ + c (ω * ↑D⁻¹) = 1 := by
    have hinv : (↑D⁻¹ : R) * (ω - c ω) = 1 := by rw [← hD]; exact D.inv_mul
    rw [map_mul]
    linear_combination (1 - ω * ↑D⁻¹) * hcD - ω * c ↑D⁻¹ * hinv
  have hI' : I ≤ I.comap c := fun x hx => hI x hx
  let cb : R ⧸ I →+* R ⧸ I := Ideal.quotientMap I c hI'
  have hmk : ∀ x, cb (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (c x) :=
    fun x => Ideal.quotientMap_mk
  have hcb : ∀ x, cb (cb x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hmk, hmk, hc]
  have hunit : IsUnit (Ideal.Quotient.mk I ω - cb (Ideal.Quotient.mk I ω)) := by
    rw [hmk, ← map_sub, ← hD]
    exact D.isUnit.map _
  obtain ⟨xb, hxb⟩ := GlobalTheory.T.finite_involution_fixed_unit_eq_mul_conj (R ⧸ I) cb hcb ⟨_, hunit⟩ (Ideal.Quotient.mk I u)
    (by rw [hmk, hcu]) (hu.map _)
  obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective xb
  rw [hmk, ← map_mul] at hxb
  have hmem : x₀ * c x₀ - u ∈ I := Ideal.Quotient.eq.mp hxb
  obtain ⟨U, rfl⟩ := hu
  have hcU : c ↑U⁻¹ = ↑U⁻¹ := by
    have h : (U : R) * c ↑U⁻¹ = 1 := by
      rw [← hcu, ← map_mul, U.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h).symm
  obtain ⟨a, ha⟩ : ∃ a, a = (x₀ * c x₀ - ↑U) * ↑U⁻¹ := ⟨_, rfl⟩
  have haI : a ∈ I := ha ▸ I.mul_mem_right _ hmem
  have hca : c a = a := by
    rw [ha]
    simp only [map_mul, map_sub, hc, hcu, hcU]
    ring
  obtain ⟨V, hV⟩ := (Ideal.mem_jacobson_bot.mp (HenselianRing.jac haI)) 1
  have hcV : c ↑V = ↑V := by rw [hV, map_add, map_mul, map_one, hca]
  have hcVi : c ↑V⁻¹ = ↑V⁻¹ := by
    have h : (V : R) * c ↑V⁻¹ = 1 := by
      rw [← hcV, ← map_mul, V.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h).symm
  have heI : (↑V⁻¹ : R) - 1 ∈ I := by
    have h : (↑V⁻¹ : R) - 1 = -(↑V⁻¹ * a) := by
      linear_combination (-(↑V⁻¹ : R)) * hV + V.inv_mul
    rw [h]
    exact I.neg_mem (I.mul_mem_left _ haI)
  obtain ⟨y, hy⟩ := exists_norm_eq_one_add I c hc hI hw heI (by rw [map_sub, hcVi, map_one])
  have hvU : x₀ * c x₀ = ↑U * ↑V := by
    rw [hV, ha]
    linear_combination (-(x₀ * c x₀ - ↑U)) * U.mul_inv
  refine ⟨x₀ * y, ?_⟩
  rw [map_mul]
  linear_combination (x₀ * c x₀) * hy + (↑V⁻¹ : R) * hvU + (↑U : R) * V.mul_inv

end GlobalTheory.HenselianNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsUnramifiedAtOfSqEqNegPrimeStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isUnramifiedAt_of_sq_eq_neg_prime : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ discr E → ∀ δ : K, δ ^ 2 = -(p : K) → ∀ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal → ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  first | exact @GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg | exact GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg | (intros; apply GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticExistsIntegralGeneratorCommonDenominatoStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_generator_common_denom_of_isQuadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E], ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧ ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  first | exact @GlobalTheory.quadratic_exists_integral_generator_common_denominator | exact GlobalTheory.quadratic_exists_integral_generator_common_denominator | (intros; apply GlobalTheory.quadratic_exists_integral_generator_common_denominator <;> assumption)
end

