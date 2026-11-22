import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealNormEquationFromLocalAssociates
section
open scoped TensorProduct

namespace GlobalTheory.CmIdealGlue

variable {Λ : Type} [CommRing Λ]

theorem natCast_tmul (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (b : Λ) :
    ((n : ℤ_[ℓ]) ⊗ₜ[ℤ] b) = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] ((n : Λ) * b) := by
  rw [← nsmul_one, TensorProduct.smul_tmul, nsmul_eq_mul]

theorem natCast_eq (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    ((n : ℤ_[ℓ] ⊗[ℤ] Λ)) = (n : ℤ_[ℓ]) ⊗ₜ[ℤ] (1 : Λ) := by
  rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast]

theorem exists_decomp (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (x : ℤ_[ℓ] ⊗[ℤ] Λ) :
    ∃ a : Λ, ∃ r : ℤ_[ℓ] ⊗[ℤ] Λ, x = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a + ((ℓ : ℤ_[ℓ] ⊗[ℤ] Λ) ^ k) * r := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul z b =>
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec k z)
    refine ⟨(PadicInt.appr z k : Λ) * b, w ⊗ₜ[ℤ] b, ?_⟩
    have hz : z = (PadicInt.appr z k : ℤ_[ℓ]) + (ℓ : ℤ_[ℓ]) ^ k * w := by rw [mul_comm, hw]; ring
    conv_lhs => rw [hz]
    have hl : ((ℓ : ℤ_[ℓ] ⊗[ℤ] Λ)) ^ k = ((ℓ : ℤ_[ℓ]) ^ k) ⊗ₜ[ℤ] (1 : Λ) := by
      rw [natCast_eq, Algebra.TensorProduct.tmul_pow, one_pow]
    rw [TensorProduct.add_tmul, natCast_tmul, hl, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy =>
    obtain ⟨a, r, rfl⟩ := hx
    obtain ⟨a', r', rfl⟩ := hy
    exact ⟨a + a', r + r', by rw [TensorProduct.tmul_add]; ring⟩

theorem isUnit_natCast (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (n : ℕ) (hn : ¬ ℓ ∣ n) :
    IsUnit (n : ℤ_[ℓ] ⊗[ℤ] Λ) := by
  have h : IsUnit (n : ℤ_[ℓ]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ.out).mpr hn))
  simpa using h.map (Algebra.TensorProduct.includeLeftRingHom : ℤ_[ℓ] →+* ℤ_[ℓ] ⊗[ℤ] Λ)

theorem castRingHom_pow_eq_zero (ℓ k : ℕ) :
    (Int.castRingHom (Λ ⧸ Ideal.span {((ℓ ^ k : ℕ) : Λ)})) ((ℓ ^ k : ℕ) : ℤ) = 0 := by
  rw [eq_intCast, Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

noncomputable def padicToQuot (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) :
    ℤ_[ℓ] →+* Λ ⧸ Ideal.span {((ℓ ^ k : ℕ) : Λ)} :=
  ((Ideal.Quotient.lift (Ideal.span {((ℓ ^ k : ℕ) : ℤ)})
      (Int.castRingHom (Λ ⧸ Ideal.span {((ℓ ^ k : ℕ) : Λ)})) (fun a ha => by
        obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [map_mul, castRingHom_pow_eq_zero, mul_zero])).comp
    (Int.quotientSpanNatEquivZMod (ℓ ^ k)).symm.toRingHom).comp (PadicInt.toZModPow k)

noncomputable def toQuot (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) :
    ℤ_[ℓ] ⊗[ℤ] Λ →+* Λ ⧸ Ideal.span {((ℓ ^ k : ℕ) : Λ)} :=
  (Algebra.TensorProduct.lift (padicToQuot ℓ k).toIntAlgHom (Ideal.Quotient.mk _).toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

theorem toQuot_tmul (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (a : Λ) :
    toQuot ℓ k ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a) = Ideal.Quotient.mk _ a := by
  simp [toQuot]

theorem exists_coprime_mul_mem (J : Ideal Λ) (m : ℕ) (hm : 0 < m) (hmJ : (m : Λ) ∈ J) (x : Λ)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
    (hx : (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ) x ∈
      J.map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom) :
    ∃ n : ℕ, 0 < n ∧ ¬ ℓ ∣ n ∧ (n : Λ) * x ∈ J := by
  obtain ⟨k, n, hn, hmn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' ℓ hℓ.out.one_lt.ne'
  refine ⟨n, Nat.pos_of_ne_zero (by rintro rfl; simp at hmn; omega), hn, ?_⟩
  have h1 := Ideal.mem_map_of_mem (toQuot (Λ := Λ) ℓ k) hx
  rw [Ideal.map_map] at h1
  have hcomp : (toQuot (Λ := Λ) ℓ k).comp
      (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom = Ideal.Quotient.mk _ := by
    ext a; simp [toQuot_tmul]
  rw [hcomp] at h1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    toQuot_tmul] at h1
  obtain ⟨j, hj, hjx⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hjx.symm)
  have : (n : Λ) * x = n * j + t * m := by
    rw [hmn, Nat.cast_mul]
    have : x = j + t * ((ℓ ^ k : ℕ) : Λ) := by rw [ht]; ring
    rw [this]; ring
  rw [this]
  exact J.add_mem (J.mul_mem_left _ hj) (J.mul_mem_left _ hmJ)

theorem mem_of_forall_map (J : Ideal Λ) (m : ℕ) (hm : 0 < m) (hmJ : (m : Λ) ∈ J) (x : Λ)
    (hx : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ) x ∈
      J.map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom) :
    x ∈ J := by
  classical
  have hex : ∃ g : ℕ, 0 < g ∧ (g : Λ) * x ∈ J := ⟨m, hm, J.mul_mem_right _ hmJ⟩
  set g := Nat.find hex with hg
  obtain ⟨hg0, hgJ⟩ := Nat.find_spec hex

  have hdvd : ∀ n : ℕ, 0 < n → (n : Λ) * x ∈ J → g ∣ n := by
    intro n hn hnJ
    have hgcd0 : 0 < Nat.gcd g n := Nat.gcd_pos_of_pos_left _ hg0
    have hgcdJ : ((Nat.gcd g n : ℕ) : Λ) * x ∈ J := by
      have e := Nat.gcd_eq_gcd_ab g n
      have e' : ((Nat.gcd g n : ℕ) : Λ) = (g : Λ) * ((Nat.gcdA g n : ℤ) : Λ) + (n : Λ) * ((Nat.gcdB g n : ℤ) : Λ) := by
        have := congrArg (fun z : ℤ => (z : Λ)) e
        push_cast at this
        exact this
      rw [e', add_mul]
      refine J.add_mem ?_ ?_
      · rw [mul_comm (g : Λ), mul_assoc]; exact J.mul_mem_left _ hgJ
      · rw [mul_comm (n : Λ), mul_assoc]; exact J.mul_mem_left _ hnJ
    have hle : g ≤ Nat.gcd g n := Nat.find_min' hex ⟨hgcd0, hgcdJ⟩
    have hge : Nat.gcd g n ≤ g := Nat.le_of_dvd hg0 (Nat.gcd_dvd_left g n)
    have : Nat.gcd g n = g := le_antisymm hge hle
    rw [← this]; exact Nat.gcd_dvd_right g n
  have hg1 : g = 1 := by
    by_contra hne
    have hp : (Nat.minFac g).Prime := Nat.minFac_prime hne
    haveI : Fact (Nat.minFac g).Prime := ⟨hp⟩
    obtain ⟨n, hn0, hnd, hnJ⟩ := exists_coprime_mul_mem J m hm hmJ x (Nat.minFac g) (hx _)
    exact hnd ((Nat.minFac_dvd g).trans (hdvd n hn0 hnJ))
  rw [← hg, hg1, Nat.cast_one, one_mul] at hgJ
  exact hgJ

theorem natCast_eq_tmul (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    (n : ℤ_[ℓ] ⊗[ℤ] Λ) = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] (n : Λ) := by
  rw [← Algebra.TensorProduct.includeRight_apply (R := ℤ) (A := ℤ_[ℓ]), map_natCast]

theorem natCast_mem_span_of_assoc (ℓ : ℕ) [Fact ℓ.Prime] {d e : ℤ_[ℓ] ⊗[ℤ] Λ} {D : Λ} {m : ℕ}
    (hmD : (m : Λ) ∈ Ideal.span {D}) (h : Associated (d * e) ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D)) :
    (m : ℤ_[ℓ] ⊗[ℤ] Λ) ∈ Ideal.span {d} := by
  rw [Ideal.mem_span_singleton]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmD
  obtain ⟨u, hu⟩ := h
  refine ⟨e * u * ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] t), ?_⟩
  rw [natCast_eq_tmul, ← ht, ← one_mul (1 : ℤ_[ℓ]), ← Algebra.TensorProduct.tmul_mul_tmul, ← hu]
  ring

noncomputable def glued (δ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℤ_[ℓ] ⊗[ℤ] Λ) : Ideal Λ :=
  ⨅ (ℓ : ℕ) (_ : Fact ℓ.Prime), (Ideal.span {δ ℓ}).comap
    (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom

theorem mem_glued (δ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℤ_[ℓ] ⊗[ℤ] Λ) (x : Λ) :
    x ∈ glued δ ↔ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] x ∈ Ideal.span {δ ℓ} := by
  simp [glued, Ideal.mem_iInf]

theorem glue : ∀ (Λ : Type) [CommRing Λ] (c : Λ →+* Λ) (D : Λ) (m : ℕ), 0 < m → (m : Λ) ∈ Ideal.span {D} →
    ∀ (δ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℤ_[ℓ] ⊗[ℤ] Λ),
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], Associated
      (δ ℓ * Algebra.TensorProduct.map (AlgHom.id ℤ_[ℓ] ℤ_[ℓ]) c.toIntAlgHom (δ ℓ)) ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D)) →
    ∃ 𝔫 : Ideal Λ, 𝔫 * 𝔫.map c = Ideal.span {D} ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      𝔫.map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom = Ideal.span {δ ℓ} := by
  intro Λ _ c D m hm hmD δ hδ
  have hmδ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (m : ℤ_[ℓ] ⊗[ℤ] Λ) ∈ Ideal.span {δ ℓ} :=
    fun ℓ _ => natCast_mem_span_of_assoc ℓ hmD (hδ ℓ)
  have hmN : (m : Λ) ∈ glued δ := by
    rw [mem_glued]; intro ℓ _
    rw [← natCast_eq_tmul]; exact hmδ ℓ
  have hloc : ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      (glued δ).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom =
        Ideal.span {δ ℓ} := by
    intro ℓ hℓ
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [mem_glued] at hx
      simpa using hx ℓ
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      obtain ⟨k, n, hn, hmn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' ℓ hℓ.out.one_lt.ne'
      obtain ⟨a, r, hdec⟩ := exists_decomp ℓ k (δ ℓ)
      have hnu : IsUnit (n : ℤ_[ℓ] ⊗[ℤ] Λ) := isUnit_natCast ℓ n hn
      have hna : (n : Λ) * a ∈ glued δ := by
        rw [mem_glued]; intro ℓ' hℓ'
        rw [Ideal.mem_span_singleton]
        have hm' := hmδ ℓ'
        rw [Ideal.mem_span_singleton, hmn, Nat.cast_mul] at hm'
        have e : (1 : ℤ_[ℓ']) ⊗ₜ[ℤ] ((n : Λ) * a) = (n : ℤ_[ℓ'] ⊗[ℤ] Λ) * ((1 : ℤ_[ℓ']) ⊗ₜ[ℤ] a) := by
          rw [natCast_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [e]
        by_cases h : ℓ' = ℓ
        · subst h
          have hk : δ ℓ' ∣ ((ℓ' ^ k : ℕ) : ℤ_[ℓ'] ⊗[ℤ] Λ) := (IsUnit.dvd_mul_right hnu).mp hm'
          have e2 : (1 : ℤ_[ℓ']) ⊗ₜ[ℤ] a = δ ℓ' - ((ℓ' ^ k : ℕ) : ℤ_[ℓ'] ⊗[ℤ] Λ) * r := by
            rw [hdec]; push_cast; ring
          rw [e2]
          exact Dvd.dvd.mul_left (dvd_sub dvd_rfl (hk.mul_right r)) _
        · have hku : IsUnit ((ℓ ^ k : ℕ) : ℤ_[ℓ'] ⊗[ℤ] Λ) := isUnit_natCast ℓ' _ (fun hd =>
            h ((Nat.prime_dvd_prime_iff_eq hℓ'.out hℓ.out).mp (hℓ'.out.dvd_of_dvd_pow hd)))
          have : δ ℓ' ∣ (n : ℤ_[ℓ'] ⊗[ℤ] Λ) := (IsUnit.dvd_mul_left hku).mp hm'
          exact this.mul_right _
      have h1 : (n : ℤ_[ℓ] ⊗[ℤ] Λ) * ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a) ∈
          (glued δ).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom := by
        have := Ideal.mem_map_of_mem
          (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom hna
        simpa [natCast_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul] using this
      have h2 : ((ℓ ^ k : ℕ) : ℤ_[ℓ] ⊗[ℤ] Λ) * (n : ℤ_[ℓ] ⊗[ℤ] Λ) ∈
          (glued δ).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom := by
        have := Ideal.mem_map_of_mem
          (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom hmN
        rw [map_natCast, hmn, Nat.cast_mul] at this
        exact this
      have h1' := (Ideal.unit_mul_mem_iff_mem _ hnu).mp h1
      have h2' := (Ideal.mul_unit_mem_iff_mem _ hnu).mp h2
      rw [hdec]
      push_cast at h2'
      exact Ideal.add_mem _ h1' (Ideal.mul_mem_right _ _ h2')
  refine ⟨glued δ, ?_, hloc⟩
  have hJ1 : ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      (glued δ * (glued δ).map c).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom =
        Ideal.span {(1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D} := by
    intro ℓ _
    have hc : (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom.comp c =
        (Algebra.TensorProduct.map (AlgHom.id ℤ_[ℓ] ℤ_[ℓ]) c.toIntAlgHom).toRingHom.comp
          (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom := by
      ext a; simp
    rw [Ideal.map_mul, Ideal.map_map, hc, ← Ideal.map_map, hloc ℓ, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
    obtain ⟨u, hu⟩ := hδ ℓ
    rw [← hu, Ideal.span_singleton_mul_right_unit u.isUnit]
    rfl
  have hJ2 : ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      (Ideal.span {D}).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom =
        Ideal.span {(1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D} := by
    intro ℓ _
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  apply le_antisymm
  · intro x hx
    apply mem_of_forall_map _ m hm hmD x
    intro ℓ _
    rw [hJ2 ℓ, ← hJ1 ℓ]
    exact Ideal.mem_map_of_mem _ hx
  · intro x hx
    have hmm : (((m * m : ℕ)) : Λ) ∈ glued δ * (glued δ).map c := by
      rw [Nat.cast_mul]
      refine Ideal.mul_mem_mul hmN ?_
      have := Ideal.mem_map_of_mem c hmN
      rwa [map_natCast] at this
    apply mem_of_forall_map _ (m * m) (Nat.mul_pos hm hm) hmm x
    intro ℓ _
    rw [hJ1 ℓ, ← hJ2 ℓ]
    exact Ideal.mem_map_of_mem _ hx

end GlobalTheory.CmIdealGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafGlueOfOpenImmersions
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace GlobalTheory.IdealGlue

lemma res_bijective {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (e : U = V) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  subst e
  have : homOfLE h = 𝟙 U := Subsingleton.elim _ _
  rw [this, op_id, X.presheaf.map_id]
  exact Function.bijective_id

lemma app_bijective {Q X : Scheme.{u}} (f : Q ⟶ X) [IsOpenImmersion f] (W : X.Opens)
    (hW : W ≤ f.opensRange) : Function.Bijective (f.app W).hom := by
  have h2 : f.app W = X.presheaf.map (homOfLE (f.image_preimage_le W)).op ≫
      (f.appIso (f ⁻¹ᵁ W)).hom := by
    rw [← Category.comp_id (f.app W), ← Iso.inv_hom_id (f.appIso (f ⁻¹ᵁ W)), ← Category.assoc,
      f.app_appIso_inv]
    rfl
  rw [h2, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Bijective.comp (f.appIso (f ⁻¹ᵁ W)).commRingCatIsoToRingEquiv.bijective
    (res_bijective _ ?_)
  rw [f.image_preimage_eq_opensRange_inf]
  exact inf_eq_right.mpr hW

noncomputable def loc {P X : Scheme.{u}} (f : P ⟶ X) (J : P.IdealSheafData) (W : X.affineOpens)
    (h : IsAffineOpen (f ⁻¹ᵁ W.1)) : Ideal Γ(X, W) :=
  (J.ideal ⟨f ⁻¹ᵁ W.1, h⟩).comap (f.app W.1).hom

lemma loc_congr {P X : Scheme.{u}} {f f' : P ⟶ X} (hf : f = f') {J J' : P.IdealSheafData}
    (hJ : J = J') (W : X.affineOpens) (h : IsAffineOpen (f ⁻¹ᵁ W.1))
    (h' : IsAffineOpen (f' ⁻¹ᵁ W.1)) : loc f J W h = loc f' J' W h' := by
  subst hf hJ; rfl

lemma loc_comap {Q X : Scheme.{u}} (f : Q ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData)
    (W : X.affineOpens) (hW : W.1 ≤ f.opensRange) (h : IsAffineOpen (f ⁻¹ᵁ W.1)) :
    loc f (I.comap f) W h = I.ideal W := by
  unfold loc
  have hle : (⟨f ''ᵁ f ⁻¹ᵁ W.1, h.image_of_isOpenImmersion f⟩ : X.affineOpens) ≤ W :=
    f.image_preimage_le W.1
  have e1 := I.ideal_comap_of_isOpenImmersion f ⟨f ⁻¹ᵁ W.1, h⟩
  have e2 := I.map_ideal hle
  rw [e1, Ideal.comap_comap, ← CommRingCat.hom_comp, f.app_appIso_inv]
  refine Eq.trans ?_ (Ideal.comap_map_of_bijective _ (res_bijective (f.image_preimage_le W.1) (by
    rw [f.image_preimage_eq_opensRange_inf]; exact inf_eq_right.mpr hW)) (I := I.ideal W))
  exact congrArg _ e2.symm

lemma loc_comp {Q' Q X : Scheme.{u}} (g : Q' ⟶ Q) (f : Q ⟶ X) [IsOpenImmersion g]
    [IsOpenImmersion f] (J : Q.IdealSheafData) (W : X.affineOpens)
    (hW : W.1 ≤ (g ≫ f).opensRange) (h1 : IsAffineOpen ((g ≫ f) ⁻¹ᵁ W.1))
    (h2 : IsAffineOpen (f ⁻¹ᵁ W.1)) :
    loc (g ≫ f) (J.comap g) W h1 = loc f J W h2 := by
  have hle : f ⁻¹ᵁ W.1 ≤ g.opensRange := by
    intro y hy
    obtain ⟨z, hz⟩ := hW hy
    refine ⟨z, f.isOpenEmbedding.injective ?_⟩
    simpa using hz
  have := loc_comap g J ⟨f ⁻¹ᵁ W.1, h2⟩ hle
    (by simpa [Scheme.Hom.comp_preimage] using h1)
  unfold loc at this ⊢
  calc _ = (((J.comap g).ideal ⟨(g ≫ f) ⁻¹ᵁ W.1, h1⟩).comap
        (g.app (f ⁻¹ᵁ W.1)).hom).comap (f.app W.1).hom := by
          exact (congrArg (fun φ => Ideal.comap (CommRingCat.Hom.hom φ)
            ((J.comap g).ideal ⟨(g ≫ f) ⁻¹ᵁ W.1, h1⟩)) (Scheme.Hom.comp_app g f W.1)).trans rfl
    _ = _ := congrArg (Ideal.comap (f.app W.1).hom) this

end GlobalTheory.IdealGlue

namespace GlobalTheory.IdealGlue

lemma ideal_transfer {A A' B B' : CommRingCat.{u}} (φ : A ⟶ B) (φ' : A' ⟶ B') (ρ : A ⟶ A')
    (ρ' : B ⟶ B') (hc : ρ ≫ φ' = φ ≫ ρ') (hb : Function.Bijective φ.hom)
    (hb' : Function.Bijective φ'.hom) (𝔞 : Ideal B) :
    (𝔞.comap φ.hom).map ρ.hom = (𝔞.map ρ'.hom).comap φ'.hom := by
  calc (𝔞.comap φ.hom).map ρ.hom
      = (((𝔞.comap φ.hom).map ρ.hom).map φ'.hom).comap φ'.hom :=
        (Ideal.comap_map_of_bijective _ hb').symm
    _ = (((𝔞.comap φ.hom).map φ.hom).map ρ'.hom).comap φ'.hom := by
        rw [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hc]
    _ = (𝔞.map ρ'.hom).comap φ'.hom := by rw [Ideal.map_comap_of_surjective _ hb.2]

lemma loc_map {P X : Scheme.{u}} (f : P ⟶ X) [IsOpenImmersion f] (J : P.IdealSheafData)
    (W W' : X.affineOpens) (hle : W' ≤ W) (hW : W.1 ≤ f.opensRange)
    (h : IsAffineOpen (f ⁻¹ᵁ W.1)) (h' : IsAffineOpen (f ⁻¹ᵁ W'.1)) :
    (loc f J W h).map (X.presheaf.map (homOfLE hle).op).hom = loc f J W' h' := by
  have hW' : W'.1 ≤ f.opensRange := (show W'.1 ≤ W.1 from hle).trans hW
  have hJ := J.map_ideal' (U := ⟨f ⁻¹ᵁ W'.1, h'⟩) (V := ⟨f ⁻¹ᵁ W.1, h⟩)
    ((TopologicalSpace.Opens.map f.base).map (homOfLE hle).op.unop).op
  exact (ideal_transfer _ _ _ _ (f.naturality (homOfLE hle).op) (app_bijective f W.1 hW)
    (app_bijective f W'.1 hW') _).trans (congrArg _ hJ)

lemma loc_indep {X : Scheme.{u}} {ι : Type*} (P : ι → Scheme.{u}) (e : ∀ i, P i ⟶ X)
    [∀ i, IsOpenImmersion (e i)] (K : ∀ i, (P i).IdealSheafData)
    (hK : ∀ i j (Q : Scheme.{u}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j →
      (K i).comap a = (K j).comap b)
    (i j : ι) (W : X.affineOpens) (hi : W.1 ≤ (e i).opensRange) (hj : W.1 ≤ (e j).opensRange)
    (h : IsAffineOpen ((e i) ⁻¹ᵁ W.1)) (h' : IsAffineOpen ((e j) ⁻¹ᵁ W.1)) :
    loc (e i) (K i) W h = loc (e j) (K j) W h' := by
  have hc := pullback.condition (f := e i) (g := e j)
  have hr : W.1 ≤ (pullback.fst (e i) (e j) ≫ e i).opensRange := by
    intro x hx
    have : x ∈ Set.range (pullback.fst (e i) (e j) ≫ e i) := by
      rw [IsOpenImmersion.range_pullback_to_base_of_left]
      exact ⟨hi hx, hj hx⟩
    exact this
  have hr' : W.1 ≤ (pullback.snd (e i) (e j) ≫ e j).opensRange := by
    intro x hx
    have : x ∈ Set.range (pullback.snd (e i) (e j) ≫ e j) := by
      rw [← hc]
      exact hr hx
    exact this
  rw [← loc_comp (pullback.fst (e i) (e j)) (e i) (K i) W hr
      (W.2.preimage_of_isOpenImmersion _ hr) h,
    ← loc_comp (pullback.snd (e i) (e j)) (e j) (K j) W hr'
      (W.2.preimage_of_isOpenImmersion _ hr') h']
  exact loc_congr hc (hK i j _ _ _ hc) _ _ _

theorem idealSheaf_glue_of_openImmersions :
    (∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) →
      (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)),
      (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W),
        (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') →
      ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W) →
    ∀ {X : Scheme.{0}} {ι : Type*} (P : ι → Scheme.{0}) (e : ∀ i, P i ⟶ X),
      (∀ i, IsOpenImmersion (e i)) → (∀ x : X, ∃ i, x ∈ Set.range (e i)) →
      ∀ (K : ∀ i, (P i).IdealSheafData),
      (∀ i j (Q : Scheme.{0}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j →
        (K i).comap a = (K j).comap b) →
      ∃ I : X.IdealSheafData, ∀ i, I.comap (e i) = K i := by
  intro hA X ι P e he hcov K hK
  classical
  have haff : ∀ i (W : X.affineOpens), W.1 ≤ (e i).opensRange → IsAffineOpen ((e i) ⁻¹ᵁ W.1) :=
    fun i W hW => W.2.preimage_of_isOpenImmersion (e i) hW
  let k : ∀ W : X.affineOpens, Ideal Γ(X, W) := fun W =>
    if hex : ∃ i, W.1 ≤ (e i).opensRange then
      loc (e hex.choose) (K hex.choose) W (haff _ W hex.choose_spec) else ⊤
  have hk : ∀ i (W : X.affineOpens) (hW : W.1 ≤ (e i).opensRange),
      k W = loc (e i) (K i) W (haff i W hW) := by
    intro i W hW
    have hex : ∃ i, W.1 ≤ (e i).opensRange := ⟨i, hW⟩
    simp only [k, dif_pos hex]
    exact loc_indep P e K hK _ _ W hex.choose_spec hW _ _
  have hcov' : ∀ x : X, ∃ W : X.affineOpens, ∃ i, W.1 ≤ (e i).opensRange ∧ x ∈ W.1 := by
    intro x
    obtain ⟨i, y, rfl⟩ := hcov x
    obtain ⟨W, hW, hxW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show e i y ∈ (e i).opensRange from ⟨y, rfl⟩)
    exact ⟨⟨W, hW⟩, i, hWle, hxW⟩
  obtain ⟨I, hI⟩ := hA {W | ∃ i, W.1 ≤ (e i).opensRange}
    (fun W ⟨i, hi⟩ W' hW' => ⟨i, (show W'.1 ≤ W.1 from hW').trans hi⟩)
    (fun x => by
      obtain ⟨W, i, hi, hx⟩ := hcov' x
      exact ⟨W, ⟨i, hi⟩, hx⟩)
    k
    (fun W ⟨i, hi⟩ W' hW' => by
      have hi' : W'.1 ≤ (e i).opensRange := (show W'.1 ≤ W.1 from hW').trans hi
      rw [hk i W hi, hk i W' hi']
      exact loc_map (e i) (K i) W W' hW' hi _ _)
  refine ⟨I, fun i => ?_⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {W : X.affineOpens // W.1 ≤ (e i).opensRange})
    (fun W => ⟨(e i) ⁻¹ᵁ W.1.1, haff i W.1 W.2⟩) ?_ ?_
  · rw [eq_top_iff]
    intro y _
    obtain ⟨W, hW, hyW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show e i y ∈ (e i).opensRange from ⟨y, rfl⟩)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWle⟩, hyW⟩
  · intro W
    apply Ideal.comap_injective_of_surjective _ (app_bijective (e i) W.1.1 W.2).2
    have h1 := loc_comap (e i) I W.1 W.2 (haff i W.1 W.2)
    have h2 := hk i W.1 W.2
    have h3 := hI W.1 ⟨i, W.2⟩
    exact h1.trans (h3.trans h2)

end GlobalTheory.IdealGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisSide
section
namespace GlobalTheory.PositiveFormRecursion

theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have h1 : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (3/2 : ℝ) ≤ ‖w + 1‖ := by
    have e : (2 : ℂ) = (w + 1) - (w - 1) := by ring
    have h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
      rw [e]; exact norm_sub_le _ _
    have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
    linarith
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (w - 1)]

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ (2 : ℕ) ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  have key : ∀ n : ℕ, (3/2 : ℝ) ^ n * ‖z - 1‖ ≤ ‖z ^ (2 : ℕ) ^ n - 1‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : z ^ (2 : ℕ) ^ (n + 1) = (z ^ (2 : ℕ) ^ n) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e]
      have hs := step (z ^ (2 : ℕ) ^ n) (hz n)
      calc (3/2 : ℝ) ^ (n + 1) * ‖z - 1‖ = (3/2) * ((3/2) ^ n * ‖z - 1‖) := by ring
        _ ≤ (3/2) * ‖z ^ (2 : ℕ) ^ n - 1‖ := by gcongr
        _ ≤ _ := hs
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3/2)
  have hn' := (div_lt_iff₀ (by positivity)).mp hn
  have h1 := key n
  have h2 := hz n
  nlinarith

end GlobalTheory.PositiveFormRecursion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraAlt
section
namespace GlobalTheory.TargetLemmaCollection

open NumberField

theorem main {K : Type} [Field K] [NumberField K] {Z : Type} [AddCommGroup Z] [Module K Z]
    [Module (RingOfIntegers K) Z] [IsScalarTower (RingOfIntegers K) K Z]
    {A : Submodule (RingOfIntegers K) Z} {x : Z} (hx : x ∈ Submodule.span K (A : Set Z)) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    have e1 : (d₁ * d₂) • y = d₂ • (d₁ • y) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • z = d₁ • (d₂ • z) := by rw [mul_smul]
    rw [e1, e2]
    exact A.add_mem (A.smul_mem _ h₁) (A.smul_mem _ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) c
    simp only at hab
    have hb : (b : RingOfIntegers K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : RingOfIntegers K) * d, mul_ne_zero hb hd, ?_⟩
    have key : ((b : RingOfIntegers K) * d) • (c • y) = a • (d • y) := by
      rw [← smul_assoc, Algebra.smul_def, map_mul, mul_comm (algebraMap _ K (b : RingOfIntegers K)),
        mul_assoc, mul_comm _ c, hab, ← map_mul, algebraMap_smul, mul_comm, mul_smul]
    rw [key]
    exact A.smul_mem _ h

end GlobalTheory.TargetLemmaCollection

theorem GlobalTheory.TargetLemmaCollection.target : ∀ {K : Type} [inst : Field K] [NumberField K] {Z : Type} [inst_2 : AddCommGroup Z] [inst_3 : Module K Z] [inst_4 : Module (NumberField.RingOfIntegers K) Z] [IsScalarTower (NumberField.RingOfIntegers K) K Z] {A : Submodule (NumberField.RingOfIntegers K) Z} {x : Z}, x ∈ Submodule.span K (↑A : Set Z) → ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ A :=
  fun hx => GlobalTheory.TargetLemmaCollection.main hx
end

