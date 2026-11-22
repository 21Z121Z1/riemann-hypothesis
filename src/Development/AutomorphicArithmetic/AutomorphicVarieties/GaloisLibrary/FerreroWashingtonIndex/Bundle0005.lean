import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HomCyc
section
open UpperTheory.V.FW

private theorem card_hom_surj (l : ℕ) {G A : Type} [Group G] [Group A] (π : G →* A) (hπ : Function.Surjective π)
    (P : G → Prop) (hP : ∀ u, P u ↔ π u = 1) :
    Nat.card {φ : G → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u, P u → φ u = 0} =
      Nat.card (A →* Multiplicative (ZMod l)) := by
  have key : ∀ (φ : G → ZMod l), (∀ a b, φ (a * b) = φ a + φ b) → (∀ u, P u → φ u = 0) →
      ∀ x y, π x = π y → φ x = φ y := by
    intro φ hadd hker x y hxy
    have h0 : φ (y⁻¹ * x) = 0 := hker _ ((hP _).mpr (by rw [map_mul, map_inv, hxy, inv_mul_cancel]))
    calc φ x = φ (y * (y⁻¹ * x)) := by rw [mul_inv_cancel_left]
      _ = φ y := by rw [hadd, h0, add_zero]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun f => ⟨fun g => Multiplicative.toAdd (f (π g)), ?_, ?_⟩) ⟨?_, ?_⟩
  · intro a b
    simp [map_mul]
  · intro u hu
    show Multiplicative.toAdd (f (π u)) = 0
    rw [(hP u).mp hu, map_one, toAdd_one]
  · intro f f' h
    ext a
    obtain ⟨g, rfl⟩ := hπ a
    have := congrArg (fun φ => φ.1 g) h
    simpa using this
  · rintro ⟨φ, hadd, hker⟩
    refine ⟨{ toFun := fun a => Multiplicative.ofAdd (φ (Function.surjInv hπ a)), map_one' := ?_, map_mul' := ?_ }, ?_⟩
    · show Multiplicative.ofAdd (φ (Function.surjInv hπ 1)) = 1
      rw [key φ hadd hker _ 1 (by rw [Function.surjInv_eq hπ, map_one]), hker 1 ((hP 1).mpr (map_one π)), ofAdd_zero]
    · intro a b
      show Multiplicative.ofAdd (φ (Function.surjInv hπ (a * b))) =
        Multiplicative.ofAdd (φ (Function.surjInv hπ a)) * Multiplicative.ofAdd (φ (Function.surjInv hπ b))
      have e : φ (Function.surjInv hπ (a * b)) = φ (Function.surjInv hπ a * Function.surjInv hπ b) :=
        key φ hadd hker _ _ (by simp only [map_mul, Function.surjInv_eq hπ])
      rw [e, hadd, ofAdd_add]
    · apply Subtype.ext
      funext g
      show Multiplicative.toAdd (Multiplicative.ofAdd (φ (Function.surjInv hπ (π g)))) = φ g
      rw [toAdd_ofAdd]
      exact key φ hadd hker _ _ (Function.surjInv_eq hπ _)

private theorem card_hom_sub_le (l : ℕ) [Fact l.Prime] (A : Type) [CommGroup A] [Finite A] (B : Subgroup A) :
    Nat.card (B →* Multiplicative (ZMod l)) ≤ Nat.card (A →* Multiplicative (ZMod l)) := by
  rw [(cardTors B).2 l, (cardTors A).2 l, (cardTors B).1 l, (cardTors A).1 l]
  refine Nat.card_le_card_of_injective (fun x => ⟨((x : B) : A), ?_⟩) ?_
  · have hx := x.2
    rw [MonoidHom.mem_ker] at hx ⊢
    simp only [powMonoidHom_apply] at hx ⊢
    rw [← Subgroup.coe_pow, hx, Subgroup.coe_one]
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h

theorem UpperTheory.V.FW.homCyc :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (U N : Subgroup Γ) [U.Normal] [N.Normal] [N.FiniteIndex], N ≤ U → IsCyclic (Γ ⧸ U) → (∀ g, ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ N) → Nat.card {φ : U → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u : U, u.1 ∈ N → φ u = 0} ≤ Nat.card {φ : Γ → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ N, φ u = 0} := by
  intro l _ Γ _ U N _ _ _ hNU hcyc hcomm
  have hU : ∀ (h : Γ ⧸ N) (u : Γ), u ∈ U → Commute h (u : Γ ⧸ N) := by
    intro h u hu
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
    have := hcomm g u hu
    rw [← QuotientGroup.eq_one_iff] at this
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  obtain ⟨gU, hgen⟩ := IsCyclic.exists_generator (α := Γ ⧸ U)
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective gU
  have hdecomp : ∀ x : Γ, ∃ i : ℤ, ∃ u ∈ U, x = g0 ^ i * u := by
    intro x
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen (x : Γ ⧸ U))
    refine ⟨i, (g0 ^ i)⁻¹ * x, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [← QuotientGroup.mk_zpow] at hi
    exact QuotientGroup.eq.mp hi
  have hcomm' : ∀ a b : Γ ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨i, u1, hu1, rfl⟩ := hdecomp x
    obtain ⟨j, u2, hu2, rfl⟩ := hdecomp y
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
    have c12 : Commute ((g0 : Γ ⧸ N) ^ i) ((g0 : Γ ⧸ N) ^ j) := Commute.zpow_zpow_self _ _ _
    apply Commute.eq
    exact Commute.mul_left (c12.mul_right (hU _ u2 hu2))
      (((hU _ u1 hu1).symm).mul_right (hU _ u2 hu2))
  letI : CommGroup (Γ ⧸ N) := { (inferInstance : Group (Γ ⧸ N)) with mul_comm := hcomm' }
  let f : U →* Γ ⧸ N := (QuotientGroup.mk' N).comp U.subtype
  have h1 := card_hom_surj l f.rangeRestrict f.rangeRestrict_surjective (fun u : U => u.1 ∈ N) (by
    intro u
    rw [← Subtype.coe_inj]
    simp [f, QuotientGroup.eq_one_iff])
  have h2 := card_hom_surj l (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (fun u => u ∈ N)
    (by intro u; simp [QuotientGroup.eq_one_iff])
  beta_reduce at h1 h2
  rw [h1, h2]
  exact card_hom_sub_le l (Γ ⧸ N) f.range
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnAlg
section
open UpperTheory.V.FW

private theorem gen2 {G Q W : Type} [Group G] [Finite Q] [AddCommGroup W] (h2 : ∀ w : W, 2 • w = 0)
    (ψ : MonoidAlgebra ℤ G →+ W) (hψ : Function.Surjective ψ) (p : G → Q) (v : Q → W)
    (hv : ∀ g, ψ (MonoidAlgebra.single g 1) = v (p g)) :
    Finite W ∧ Nat.card W ≤ 2 ^ Nat.card Q := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Module (ZMod 2) W := AddCommGroup.zmodModule h2
  let φ : (Q → ZMod 2) →ₗ[ZMod 2] W := Fintype.linearCombination (ZMod 2) v
  have hs : Function.Surjective φ := by
    intro w
    obtain ⟨x, rfl⟩ := hψ w
    change ψ x ∈ (LinearMap.range φ).toAddSubgroup
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | single g n =>
      have : (MonoidAlgebra.single g n : MonoidAlgebra ℤ G) = n • MonoidAlgebra.single g 1 := by simp
      rw [this, map_zsmul]
      refine zsmul_mem ?_ _
      rw [hv]
      exact ⟨Pi.single (p g) 1, by simp [φ]⟩
  refine ⟨Finite.of_surjective φ hs, ?_⟩
  have := Nat.card_le_card_of_surjective φ hs
  simpa [Nat.card_fun] using this

private noncomputable def kap {G : Type} [CommGroup G] (J : G) : MonoidAlgebra ℤ G →+ (G → ZMod 2) where
  toFun x := fun g => (((x * (1 + MonoidAlgebra.of ℤ G J)).coeff g : ℤ) : ZMod 2)
  map_zero' := by ext g; simp
  map_add' a b := by ext g; simp [add_mul]

private theorem kap_apply {G : Type} [CommGroup G] {J : G} (hJ : J * J = 1) (x : MonoidAlgebra ℤ G) (g : G) :
    kap J x g = (x.coeff g : ZMod 2) + (x.coeff (J * g) : ZMod 2) := by
  have : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJ
  simp [kap, mul_add, this, mul_comm J g]

private theorem kap_single_mul {G : Type} [CommGroup G] {J : G} (hJ : J * J = 1) (x : MonoidAlgebra ℤ G) (g : G) :
    kap J (MonoidAlgebra.single g 1 * x) = fun h => kap J x (g⁻¹ * h) := by
  ext h
  simp [kap_apply hJ, mul_left_comm]

private theorem kap_range {G : Type} [CommGroup G] [Finite G] {J : G} (hJ : J * J = 1) (hJ1 : J ≠ 1) :
    (kap J).range = evenF J := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩ g
    rw [kap_apply hJ, kap_apply hJ, ← mul_assoc, hJ, one_mul, add_comm]
  · intro f hf
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
    refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => if e g < e (J * g) then ((f g).val : ℤ) else 0), ?_⟩
    ext g
    have hne : e g ≠ e (J * g) := fun h => hJ1 (by simpa using e.injective h)
    have hfg : f (J * g) = f g := hf g
    rw [kap_apply hJ]
    simp only [MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm, ← mul_assoc, hJ, one_mul]
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h, h.le]
    · simp [h, h.le, hfg]

theorem UpperTheory.V.FW.sgnAlg :
    ∀ (G : Type) [CommGroup G] [Finite G] (J γ : G) (θ : MonoidAlgebra ℤ G) (N : ℕ) (S : AddSubgroup (G → ZMod 2)), J * J = 1 → J ≠ 1 → (∀ f ∈ S, ∀ g, (fun x => f (g * x)) ∈ S) → (fun g => (((θ * (1 + MonoidAlgebra.of ℤ G J)).coeff g : ℤ) : ZMod 2)) ∈ S → (MonoidAlgebra.of ℤ G γ - 1) ^ N ∈ Ideal.span {θ, 1 + MonoidAlgebra.of ℤ G J, ((2 : ℕ) : MonoidAlgebra ℤ G)} → S.relIndex (evenF J) ≤ (2 ^ (Subgroup.zpowers γ).index) ^ N := by
  intro G _ _ J γ θ N S hJ hJ1 hS hθ hN
  have hdbl : ∀ y, kap J (y + y) ∈ S := fun y => by
    have : kap J (y + y) = 0 := by
      rw [map_add]; ext g; simp [CharTwo.add_self_eq_zero]
    rw [this]; exact zero_mem _
  let I : Ideal (MonoidAlgebra ℤ G) :=
    { (S.comap (kap J)).toAddSubmonoid with
      smul_mem' := fun r x hx => by
        change kap J (r * x) ∈ S
        induction r using MonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => rw [add_mul, map_add]; exact add_mem ha hb
        | single g n =>
          have : (MonoidAlgebra.single g n : MonoidAlgebra ℤ G) = n • MonoidAlgebra.single g 1 := by simp
          rw [this, smul_mul_assoc, map_zsmul, kap_single_mul hJ]
          exact zsmul_mem (hS _ hx _) _ }
  have hI : ∀ x, x ∈ I ↔ kap J x ∈ S := fun x => Iff.rfl
  have hNI : (MonoidAlgebra.of ℤ G γ - 1) ^ N ∈ I := by
    refine Ideal.span_le.2 ?_ hN
    rintro x (rfl | rfl | rfl)
    · exact hθ
    · change kap J _ ∈ S
      have : kap J (1 + MonoidAlgebra.of ℤ G J) = kap J (1 + 1) := by
        ext g
        have h1 : MonoidAlgebra.of ℤ G J * MonoidAlgebra.of ℤ G J = 1 := by rw [← map_mul, hJ, map_one]
        have : (1 + MonoidAlgebra.of ℤ G J) * (1 + MonoidAlgebra.of ℤ G J) = (1 + 1) * (1 + MonoidAlgebra.of ℤ G J) := by
          linear_combination h1
        simp only [kap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, this]
      rw [this]; exact hdbl 1
    · change kap J _ ∈ S
      have : ((2 : ℕ) : MonoidAlgebra ℤ G) = 1 + 1 := by norm_num
      rw [this]; exact hdbl 1
  have hidx : S.relIndex (evenF J) = Nat.card (MonoidAlgebra ℤ G ⧸ I) := by
    rw [← kap_range hJ hJ1, ← AddSubgroup.index_comap]
    rfl
  have h2 : ∀ w : MonoidAlgebra ℤ G ⧸ I, 2 • w = 0 := fun w => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [two_nsmul, ← map_add, Ideal.Quotient.eq_zero_iff_mem]
    exact hdbl x
  haveI hfin : Finite (MonoidAlgebra ℤ G ⧸ I) :=
    (gen2 h2 (Ideal.Quotient.mk I).toAddMonoidHom Ideal.Quotient.mk_surjective id
      (fun g => Ideal.Quotient.mk I (MonoidAlgebra.single g 1)) fun _ => rfl).1
  set t : MonoidAlgebra ℤ G ⧸ I := Ideal.Quotient.mk I (MonoidAlgebra.of ℤ G γ - 1) with ht
  let T : AddMonoid.End (MonoidAlgebra ℤ G ⧸ I) := Module.toAddMonoidEnd (MonoidAlgebra ℤ G ⧸ I) (MonoidAlgebra ℤ G ⧸ I) t
  have hT : T ^ N = 0 := by
    have : t ^ N = 0 := by rw [ht, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hNI
    rw [← map_pow, this, map_zero]
  rw [hidx]
  refine (nilCard _ T N hT).trans (Nat.pow_le_pow_left ?_ N)
  let ψ : MonoidAlgebra ℤ G →+ (MonoidAlgebra ℤ G ⧸ I) ⧸ AddMonoidHom.range T :=
    (QuotientAddGroup.mk' _).comp (Ideal.Quotient.mk I).toAddMonoidHom
  have hstep : ∀ g, ψ (MonoidAlgebra.single (γ * g) 1) = ψ (MonoidAlgebra.single g 1) := fun g => by
    rw [← sub_eq_zero, ← map_sub]
    refine (QuotientAddGroup.eq_zero_iff _).2 ⟨Ideal.Quotient.mk I (MonoidAlgebra.single g 1), ?_⟩
    change t * _ = Ideal.Quotient.mk I _
    rw [ht, ← map_mul, sub_mul]
    simp [MonoidAlgebra.single_mul_single]
  have hpow : ∀ (n : ℕ) g, ψ (MonoidAlgebra.single (γ ^ n * g) 1) = ψ (MonoidAlgebra.single g 1) := fun n g => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, hstep, ih]
  refine (gen2 (Q := G ⧸ Subgroup.zpowers γ) ?_ ψ ?_ QuotientGroup.mk
    (fun q => ψ (MonoidAlgebra.single q.out 1)) ?_).2
  · intro w
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ w
    rw [← map_nsmul, h2, map_zero]
  · exact (QuotientAddGroup.mk'_surjective _).comp Ideal.Quotient.mk_surjective
  · intro g
    obtain ⟨⟨h, hh⟩, e⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.zpowers γ) g
    obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers.2 hh)
    simp only at e ⊢
    rw [e, mul_comm, hpow]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ThetaFull
section
open UpperTheory.V.FW

private theorem coeff_thetaH (M c : ℕ) [NeZero M] (s : (ZMod M)ˣ) :
    (thetaH M c).coeff s = if 2 * (s : ZMod M).val < M then gc M c s else 0 := by
  classical
  simp [thetaH, Finsupp.single_apply, Finset.sum_ite_eq']

private theorem coeff_mul_J (M : ℕ) [NeZero M] (f : MonoidAlgebra ℤ (ZMod M)ˣ) (s : (ZMod M)ˣ) :
    (f * MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ)).coeff s = f.coeff (-s) := by
  rw [show MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ) = MonoidAlgebra.single (-1) 1 from rfl]
  rw [MonoidAlgebra.coeff_mul_single_eq_coeff_mul (-s), mul_one]
  intro m _
  rw [mul_neg_one, neg_eq_iff_eq_neg]

private theorem half (M : ℕ) [NeZero M] (hM : 2 < M) (s : (ZMod M)ˣ) :
    (s : ZMod M) ≠ 0 ∧ (2 * (-(s : ZMod M)).val < M ↔ ¬ 2 * (s : ZMod M).val < M) := by
  have hs0 : (s : ZMod M) ≠ 0 := by
    haveI : Fact (1 < M) := ⟨by omega⟩
    exact s.ne_zero
  refine ⟨hs0, ?_⟩
  rw [ZMod.neg_val, if_neg hs0]
  have hlt := ZMod.val_lt (s : ZMod M)
  have hne : 2 * (s : ZMod M).val ≠ M := by
    intro h
    have h2 : (2 : ZMod M) * (s : ZMod M) = 0 := by
      have : ((2 * (s : ZMod M).val : ℕ) : ZMod M) = 0 := by
        rw [h]
        exact ZMod.natCast_self M
      push_cast at this
      rwa [ZMod.natCast_zmod_val] at this
    have h3 : (2 : ZMod M) = 0 := by
      have := congrArg (· * ((s⁻¹ : (ZMod M)ˣ) : ZMod M)) h2
      simpa [mul_assoc] using this
    have h4 : ((2 : ℕ) : ZMod M) = 0 := by exact_mod_cast h3
    rw [ZMod.natCast_eq_zero_iff] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  omega

theorem UpperTheory.V.FW.thetaFull :
    ∀ (M c : ℕ) [NeZero M], c.Coprime M → Odd c → 2 < M → thetaH M c * (1 - MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ)) = ∑ s : (ZMod M)ˣ, MonoidAlgebra.single s (gc M c s) ∧ ∀ s : (ZMod M)ˣ, (((thetaH M c * (1 + MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ))).coeff s : ℤ) : ZMod 2) = (gc M c s : ZMod 2) := by
  intro M c _ hc hodd hM
  have key : ∀ s : (ZMod M)ˣ, (thetaH M c).coeff (-s) = if 2 * (s : ZMod M).val < M then 0 else -gc M c s := by
    intro s
    obtain ⟨hs0, hiff⟩ := half M hM s
    rw [coeff_thetaH, Units.val_neg]
    by_cases h : 2 * (s : ZMod M).val < M
    · rw [if_neg (fun h' => hiff.mp h' h), if_pos h]
    · rw [if_pos (hiff.mpr h), if_neg h, gcNeg M c _ hc hodd hs0]
  constructor
  · rw [mul_sub, mul_one, sub_eq_iff_eq_add]
    refine MonoidAlgebra.ext (Finsupp.ext fun s => ?_)
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_J, key, coeff_thetaH]
    classical
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    split_ifs <;> simp
  · intro s
    rw [mul_add, mul_one, MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_J, key, coeff_thetaH]
    split_ifs
    · simp
    · push_cast
      simp [ZMod.neg_eq_self_mod_two]
end

