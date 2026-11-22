import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CountingPairs
section
noncomputable def UpperTheory.Reformulated.B.CountingPairs.rhoPair :
    {n : ℕ} → (Fin n → ℤ) → ℤ :=
    fun {n : ℕ} (l : Fin n → ℤ) ↦ ∑ i : Fin n, ((↑n : ℤ) - (1 : ℤ) - (2 : ℤ) * (↑(↑i : ℕ) : ℤ)) * l i

namespace UpperTheory.Reformulated.B.CountingPairs.Priv

private lemma cntGt {k : ℕ} (i : Fin k) :
    (∑ c : Fin k, if i < c then (1:ℤ) else 0) = (k:ℤ) - 1 - i := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun c : Fin k => i < c)) = Finset.Ioi i := by
    ext c; simp
  rw [this, Fin.card_Ioi]
  have := i.isLt
  push_cast [Nat.sub_sub, show 1 + (i:ℕ) ≤ k by omega]
  ring

private lemma cntLt {k : ℕ} (c : Fin k) :
    (∑ i : Fin k, if i < c then (1:ℤ) else 0) = (c:ℤ) := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun i : Fin k => i < c)) = Finset.Iio c := by
    ext i; simp
  rw [this, Fin.card_Iio]

end UpperTheory.Reformulated.B.CountingPairs.Priv

open UpperTheory.Reformulated.B.CountingPairs.Priv in
theorem UpperTheory.Reformulated.B.CountingPairs.main :
    ∀ {k : ℕ} (l : Fin k → ℤ),
      (∑ c : Fin k, ∑ i : Fin k, if i < c then l i - l c else (0 : ℤ)) = UpperTheory.Reformulated.B.CountingPairs.rhoPair l := by
  intro k l
  have h1 : ∀ c i : Fin k, (if i < c then l i - l c else (0:ℤ))
      = (if i < c then (1:ℤ) else 0) * l i - (if i < c then (1:ℤ) else 0) * l c := by
    intro c i; split_ifs <;> simp
  simp_rw [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun c i => (if i < c then (1:ℤ) else 0) * l i)]
  simp_rw [← Finset.sum_mul, cntGt, cntLt]
  unfold UpperTheory.Reformulated.B.CountingPairs.rhoPair
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CuspidalIrreducibleSubrep
section
noncomputable def UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev :
    {I : Type} →
      [Fintype I] →
        {W : I → Type} →
          [inst : (i : I) → AddCommGroup (W i)] →
            [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
              ((i : I) → Module.Dual ℂ (W i)) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] ℂ :=
    fun {I : Type} [Fintype I] {W : I → Type} [(i : I) → AddCommGroup (W i)] [(i : I) → _root_.Module ℂ (W i)]
        (f : (i : I) → Module.Dual ℂ (W i)) ↦
      (PiTensorProduct.lift : MultilinearMap ℂ W ℂ → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] ℂ)
        ((MultilinearMap.mkPiAlgebra ℂ I ℂ).compLinearMap f)

theorem UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev_tprod :
    ∀ {I : Type} [inst : Fintype I] [dI : DecidableEq I] {W : I → Type} [inst_1 : (i : I) → AddCommGroup (W i)]
      [inst_2 : (i : I) → _root_.Module ℂ (W i)] (f : (i : I) → Module.Dual ℂ (W i)) (m : (i : I) → W i),
      (UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev f : (PiTensorProduct ℂ fun (i : I) ↦ W i) → ℂ)
          ((PiTensorProduct.tprod ℂ : ((i : I) → W i) → PiTensorProduct ℂ fun (i : I) ↦ W i) m) =
        ∏ i : I, (f i : W i → ℂ) (m i) := by
  intro I _ _ W _ _ f m
  simp [UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CutSub
section
noncomputable def UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub :
    (K : Type) → [inst : Field K] → [NumberField K] → (r : ℕ) → ℕ → Submodule (NumberField.RingOfIntegers K) (Fin r → K) :=
  fun K _ _ r n =>
    { carrier := {v : Fin r → K | ∀ i : Fin r, n ≤ (i : ℕ) → v i = 0}
      add_mem' := by
        intro v w hv hw i hi
        rw [Pi.add_apply, hv i hi, hw i hi, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := by
        intro c v hv i hi
        rw [Pi.smul_apply, hv i hi, smul_zero] }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclicSubtraction
section
noncomputable def UpperTheory.Reformulated.B.CyclicSubtraction.cycSub.{u_1, u_2} :
    {G : Type u_1} → {M : Type u_2} → [inst : Group G] → [inst_1 : AddCommGroup M] → Representation ℤ G M → G → M →+ M :=
    fun {G : Type u_1} {M : Type u_2} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) (σ : G) ↦
      ((ρ : G → M →ₗ[ℤ] M) σ - LinearMap.id).toAddMonoidHom

theorem UpperTheory.Reformulated.B.CyclicSubtraction.apply_eq_of_cycSub_eq_zero.{u_1, u_2} :
    ∀ {G : Type u_1} {M : Type u_2} [inst : Group G] [inst_1 : AddCommGroup M] (ρ : Representation ℤ G M) {σ : G},
      (∀ (g : G), g ∈ Subgroup.zpowers σ) →
        ∀ {x : M}, (UpperTheory.Reformulated.B.CyclicSubtraction.cycSub ρ σ : M → M) x = (0 : M) → ∀ (g : G), ((ρ : G → M →ₗ[ℤ] M) g : M → M) x = x := by
  intro G M _ _ ρ σ hσ x hx g
  have h0 : ρ σ x - x = 0 := hx
  have h1 : ρ σ x = x := sub_eq_zero.mp h0
  let H : Subgroup G :=
    { carrier := {g | ρ g x = x}
      one_mem' := by
        show ρ 1 x = x
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha']
          _ = ρ (a⁻¹ * a) x := by rw [map_mul, Module.End.mul_apply]
          _ = x := by
            rw [inv_mul_cancel, map_one]
            rfl }
  have hle : Subgroup.zpowers σ ≤ H := (Subgroup.zpowers_le).mpr h1
  exact hle (hσ g)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclicTrivialInductionRing
section
private theorem UpperTheory.cyclic_trivial_induction_ring {R : Type} [Ring R] (hR : ∀ c : R, ∃ m : ℤ, c = m) :
    ∀ {H : Type} [Monoid H] (n : ℕ) (P : Rep.{0, 0, 0} R H → Prop),
        (∀ C : Rep.{0, 0, 0} R H, Finite C.V → IsAddCyclic C.V →
          (∀ (g : H) (c : C.V), C.ρ g c = c) → (∀ c : C.V, n • c = 0) → P C) →
        (∀ (A B C : Rep.{0, 0, 0} R H) (f : A ⟶ B) (g : B ⟶ C),
          (∀ (h : H) (a : A.V), A.ρ h a = a) → (∀ (h : H) (c : C.V), C.ρ h c = c) →
          Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
          P A → P C → P B) →
        ∀ A : Rep.{0, 0, 0} R H, Finite A.V →
          (∀ (g : H) (a : A.V), A.ρ g a = a) → (∀ a : A.V, n • a = 0) → P A := by
  intro H _ n P hcyc hext A
  induction hk : Nat.card A.V using Nat.strong_induction_on generalizing A with
  | _ k ih =>
    intro hfin htriv htors
    by_cases hne : ∃ a : A.V, a ≠ 0
    · obtain ⟨a, ha⟩ := hne
      let B : Submodule R A.V := Submodule.span _ {a}
      let S : Rep.{0, 0, 0} R H := Rep.of (Representation.trivial R H B)
      let Q : Rep.{0, 0, 0} R H :=
        Rep.of (Representation.trivial R H (A.V ⧸ B))
      let f : S ⟶ A := Rep.ofHom (ρ := Representation.trivial R H B) (σ := A.ρ)
        (B.subtype.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => by
          simpa using (htriv g v.1).symm))
      let g : A ⟶ Q := Rep.ofHom (ρ := A.ρ) (σ := Representation.trivial R H (A.V ⧸ B))
        (B.mkQ.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => by
          simp [htriv g v]))
      have hlt : Nat.card (A.V ⧸ B) < Nat.card A.V := by
        by_contra hcon
        have hbij := (Submodule.mkQ_surjective B).bijective_of_nat_card_le (not_lt.mp hcon)
        have hmem : a ∈ B := Submodule.mem_span_singleton_self a
        have h0 : B.mkQ a = B.mkQ 0 := by
          simpa using (Submodule.Quotient.mk_eq_zero B).2 hmem
        exact ha (hbij.1 h0)
      have hS : P S := by
        refine hcyc S (inferInstanceAs (Finite B)) ?_ (fun _ _ => rfl) ?_
        · refine (⟨⟨⟨a, Submodule.mem_span_singleton_self a⟩, fun x => ?_⟩⟩ : IsAddCyclic B)
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 x.2
          obtain ⟨m, rfl⟩ := hR c
          refine AddSubgroup.mem_zmultiples_iff.2 ⟨m, Subtype.ext ?_⟩
          rw [← hc, Int.cast_smul_eq_zsmul]
          rfl
        · intro c
          exact Subtype.ext (htors c.1)
      have hQ : P Q := by
        refine ih (Nat.card (A.V ⧸ B)) (hk ▸ hlt) Q rfl
          (Finite.of_surjective B.mkQ (Submodule.mkQ_surjective B))
          (fun _ _ => rfl) ?_
        intro c
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective B c
        have : n • B.mkQ x = B.mkQ (n • x) := (map_nsmul B.mkQ n x).symm
        exact this.trans (by rw [htors x, map_zero])
      exact hext S A Q f g (fun _ _ => rfl) (fun _ _ => rfl) (Subtype.val_injective)
        (LinearMap.exact_subtype_mkQ B) (Submodule.mkQ_surjective B) hS hQ
    · have : Subsingleton A.V := ⟨fun x y => by
        push_neg at hne
        rw [hne x, hne y]⟩
      exact hcyc A hfin inferInstance htriv htors

theorem UpperTheory.cyclic_trivial_induction :
    ∀ {H : Type} [Monoid H] (n : ℕ) (P : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H → Prop),
        (∀ C : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H, Finite C.V → IsAddCyclic C.V →
          (∀ (g : H) (c : C.V), C.ρ g c = c) → (∀ c : C.V, n • c = 0) → P C) →
        (∀ (A B C : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H) (f : A ⟶ B) (g : B ⟶ C),
          (∀ (h : H) (a : A.V), A.ρ h a = a) → (∀ (h : H) (c : C.V), C.ρ h c = c) →
          Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
          P A → P C → P B) →
        ∀ A : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H, Finite A.V →
          (∀ (g : H) (a : A.V), A.ρ g a = a) → (∀ a : A.V, n • a = 0) → P A := by
  intro H _
  exact UpperTheory.cyclic_trivial_induction_ring (R := ULift.{0, 0} ℤ) (fun c => ⟨c.down, ULift.ext _ _ (by simp)⟩)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicBarContinuous
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicBarContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicBarContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicBarContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicBarContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicBarContinuous.cont_cycBar :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicBarContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have hZ : Continuous (UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have hι : Continuous
      (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
        ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Units.continuous_map hι).comp hZ
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterContinuous
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cont_cyc :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous (fun x : ℤ_[l] ↦ algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l])) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterFirst
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G E Ω →* (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)).comp
        (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cyc_continuous :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycBar F Ω l) : UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G F Ω → (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous ((algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)).comp PadicInt.Coe.ringHom) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterFourth
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cyc_cont :
    ∀ {E Ω : Type} [inst : Field E] [NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] {l : ℕ}
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycBar E Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G E Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)ˣ) := by
  intro E Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycZ E Ω l) := cyclotomicCharacter.continuous l E Ω
  have h2 : Continuous ((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)).comp
      (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l])) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterSecond
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G E Ω →* (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp
        (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cyc_cont :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycBar F Ω l) : UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω → (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous
      (((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp PadicInt.Coe.ringHom :
        ℤ_[l] →* UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l) : ℤ_[l] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterThird
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cyc_cont :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous (algebraMap ℚ_[l] (PadicAlgCl l)) :=
    (algebraMap_isometry ℚ_[l] (PadicAlgCl l)).continuous
  have h3 : Continuous
      (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
        ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l) :=
    h2.comp continuous_subtype_val
  exact (Continuous.units_map _ h3).comp h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcAevalIntertwine
section
theorem UpperTheory.Reformulated.B.Qj10.dc_aeval_intertwine.{u_1, u_2} :
    ∀ {Y : Type u_1} {Z : Type u_2} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y] [inst_2 : AddCommGroup Z]
    [inst_3 : _root_.Module ℂ Z] (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z),
    (∀ (y : Y), (ψ : Y → Z) ((A : Y → Y) y) = (B : Z → Z) ((ψ : Y → Z) y)) →
      ∀ (p : Polynomial ℂ) (y : Y),
        (ψ : Y → Z) (((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) p : Y → Y) y) =
          ((Polynomial.aeval B : Polynomial ℂ → Module.End ℂ Z) p : Z → Z) ((ψ : Y → Z) y) := by
  intro Y Z _ _ _ _ ψ A B h p y
  have hpow : ∀ (n : ℕ) (x : Y), ψ ((A ^ n) x) = (B ^ n) (ψ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
end

