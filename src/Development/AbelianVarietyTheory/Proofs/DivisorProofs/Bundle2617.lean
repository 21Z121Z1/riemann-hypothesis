import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2499
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2500
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2501

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEvenCubicalValuesNotMemMaximalIdealPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.QuadTend

theorem dickson_fin {J : Type*} (n : ℕ) (f : J → Fin n → ℕ) :
    ∃ F : Finset J, ∀ i, ∃ j ∈ F, f j ≤ f i := by
  classical
  set s : Set (Fin n → ℕ) := Set.range f
  have hpwo : s.IsPWO := Set.isPWO_of_wellQuasiOrderedLE s
  set m : Set (Fin n → ℕ) := {x | Minimal (· ∈ s) x}
  have hm : m.Finite := (setOf_minimal_antichain (· ∈ s)).finite_of_partiallyWellOrderedOn
    (hpwo.mono (fun x hx => hx.prop))
  have hpre : ∀ x ∈ m, ∃ j, f j = x := fun x hx => hx.prop
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact ⟨∅, fun i => isEmptyElim i⟩
  choose! g hg using hpre
  refine ⟨hm.toFinset.image g, fun i => ?_⟩
  obtain ⟨x, hxi, hx⟩ := hpwo.exists_le_minimal (Set.mem_range_self i)
  exact ⟨g x, Finset.mem_image_of_mem g (hm.mem_toFinset.mpr hx), by rw [hg x hx]; exact hxi⟩

section Cl

variable {G X : Type*} [CommGroup G] [AddCommGroup X] (κ : X → G)

def defect (a b : X) : G := κ (a + b) / (κ a * κ b)

variable {κ}

theorem kappa_zero (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) :
    κ 0 = 1 := by
  have h := hc 0 0 0
  simp only [add_zero] at h
  have h2 : κ 0 * (κ 0 * κ 0 * κ 0) = 1 * (κ 0 * κ 0 * κ 0) := by
    rw [_root_.one_mul]; simpa only [_root_.mul_assoc] using h
  exact mul_right_cancel h2

theorem defect_add_left (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    (a a' b : X) : defect κ (a + a') b = defect κ a b * defect κ a' b := by
  unfold defect
  rw [div_mul_div_comm, div_eq_div_iff_mul_eq_mul]
  have h := hc a a' b
  calc κ (a + a' + b) * (κ a * κ b * (κ a' * κ b)) = (κ (a + a' + b) * κ a * κ a' * κ b) * κ b := by
        simp only [mul_comm, _root_.mul_assoc, _root_.mul_left_comm]
    _ = (κ (a + a') * κ (a + b) * κ (a' + b)) * κ b := by rw [h]
    _ = κ (a + b) * κ (a' + b) * (κ (a + a') * κ b) := by simp only [mul_comm, _root_.mul_assoc, _root_.mul_left_comm]

theorem defect_comm (a b : X) : defect κ a b = defect κ b a := by
  unfold defect; rw [add_comm, _root_.mul_comm]

theorem defect_zero_left (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    (b : X) : defect κ 0 b = 1 := by
  have h := defect_add_left hc 0 0 b
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem defect_neg_left (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    (a b : X) : defect κ (-a) b = (defect κ a b)⁻¹ := by
  have h := defect_add_left hc a (-a) b
  rw [add_neg_cancel, defect_zero_left hc] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem kappa_add (a b : X) : κ (a + b) = κ a * κ b * defect κ a b := by
  unfold defect; rw [mul_div_cancel]

theorem mem_closure_of_gen (hn : ∀ a, κ (-a) = κ a)
    (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    {J : Type*} (e : J → X) (he : AddSubgroup.closure (Set.range e) = ⊤) (a : X) :
    κ a ∈ Subgroup.closure (Set.range (Sum.elim (fun i => κ (e i)) (fun p : J × J => κ (e p.1 + e p.2)))) := by
  set H := Subgroup.closure (Set.range (Sum.elim (fun i => κ (e i)) (fun p : J × J => κ (e p.1 + e p.2))))
  have hk : ∀ i, κ (e i) ∈ H := fun i => Subgroup.subset_closure ⟨Sum.inl i, rfl⟩
  have hg : ∀ i j, defect κ (e i) (e j) ∈ H := fun i j =>
    H.div_mem (Subgroup.subset_closure ⟨Sum.inr (i, j), rfl⟩) (H.mul_mem (hk i) (hk j))
  have mem : ∀ x : X, x ∈ AddSubgroup.closure (Set.range e) := fun x => he ▸ AddSubgroup.mem_top x
  have step1 : ∀ i b, defect κ (e i) b ∈ H := by
    intro i b
    induction mem b using AddSubgroup.closure_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hg i j
    | zero => rw [defect_comm, defect_zero_left hc]; exact H.one_mem
    | add x y _ _ hx hy =>
      rw [defect_comm, defect_add_left hc, defect_comm x, defect_comm y]; exact H.mul_mem hx hy
    | neg x _ hx => rw [defect_comm, defect_neg_left hc, defect_comm]; exact H.inv_mem hx
  have step2 : ∀ a b, defect κ a b ∈ H := by
    intro a b
    induction mem a using AddSubgroup.closure_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact step1 j b
    | zero => rw [defect_zero_left hc]; exact H.one_mem
    | add x y _ _ hx hy => rw [defect_add_left hc]; exact H.mul_mem hx hy
    | neg x _ hx => rw [defect_neg_left hc]; exact H.inv_mem hx
  induction mem a using AddSubgroup.closure_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hk j
  | zero => rw [kappa_zero hc]; exact H.one_mem
  | add x y _ _ hx hy => rw [kappa_add (κ := κ)]; exact H.mul_mem (H.mul_mem hx hy) (step2 x y)
  | neg x _ hx => rw [hn]; exact hx

end Cl

theorem finite_not_mem_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ n : ℕ, {a | ¬ ∃ s ∈ maximalIdeal R ^ n, (κ a : FractionRing R) = algebraMap R _ s}.Finite := by
  intro R _ _ _ _ _ X _ _ κ hneg hcube hm n
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top (R := ℤ) (M := X))
  have hcl : AddSubgroup.closure (Set.range (fun x : S => (x : X))) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Subtype.range_coe_subtype, Finset.setOf_mem, hS]; rfl
  have hΓ := mem_closure_of_gen hneg hcube (fun x : S => (x : X)) hcl
  set gg := Sum.elim (fun i : S => κ (i : X)) (fun p : S × S => κ ((p.1 : X) + p.2))
  set Γ := Subgroup.closure (Set.range gg)
  obtain ⟨s, v, hv1, hv2⟩ := GlobalTheory.T.exists_heightOne_valuations_control_subgroup R (S ⊕ (S × S)) gg
  set K := FractionRing R
  let w : Kˣ → Fin s → ℤ := fun x i => Multiplicative.toAdd (v i x)
  have wmul : ∀ x y i, w (x * y) i = w x i + w y i := fun x y i => by simp [w]
  have winv : ∀ x i, w x⁻¹ i = - w x i := fun x i => by simp [w]
  have wone : ∀ i, w 1 i = 0 := fun i => by simp [w]
  have hk0 := kappa_zero hcube
  have wκ : ∀ a i, 0 ≤ w (κ a) i := by
    intro a i
    by_cases ha : a = 0
    · rw [ha, hk0, wone]
    · obtain ⟨t, -, ht⟩ := hm a ha
      exact hv1 i (κ a) t ht

  have unitOf : ∀ x ∈ Γ, (∀ i, w x i = 0) → ∃ r : R, IsUnit r ∧ (x : K) = algebraMap R K r := by
    intro x hx h0
    obtain ⟨r, hr⟩ := hv2 x hx (fun i => (h0 i).ge)
    obtain ⟨r', hr'⟩ := hv2 x⁻¹ (Γ.inv_mem hx) (fun i => show 0 ≤ w x⁻¹ i by rw [winv, h0 i, neg_zero])
    have hrr : r * r' = 1 := IsFractionRing.injective R K (by
      rw [map_mul, ← hr, ← hr', map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
    exact ⟨r, ⟨Units.mkOfMulEqOne r r' hrr, rfl⟩, hr⟩
  let q : X → ℤ := fun a => ∑ i, w (κ a) i
  have hqneg : ∀ a, q (-a) = q a := fun a => by simp only [q, hneg]
  have hqcube : ∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b) := by
    intro a a' b
    have h := congrArg (fun x => ∑ i, w x i) (hcube a a' b)
    simp only [wmul, Finset.sum_add_distrib] at h
    simpa only [q] using h
  have hqpos : ∀ a, a ≠ 0 → 1 ≤ q a := by
    intro a ha
    obtain ⟨t, htm, ht⟩ := hm a ha
    by_contra hlt
    have hsum0 : q a = 0 := le_antisymm (by omega) (Finset.sum_nonneg fun i _ => wκ a i)
    have hall : ∀ i, w (κ a) i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => wκ a i)).mp hsum0 i (Finset.mem_univ i)
    obtain ⟨r, hru, hr⟩ := unitOf (κ a) (hΓ a) hall
    have : t = r := IsFractionRing.injective R K (ht.symm.trans hr)
    exact (IsLocalRing.mem_maximalIdeal t).mp htm (this ▸ hru)

  let P := {x : Kˣ // x ∈ Γ ∧ (∀ i, 0 ≤ w x i) ∧ 0 < ∑ i, w x i}
  obtain ⟨F, hF⟩ := dickson_fin s (fun x : P => fun i => (w x.1 i).toNat)
  set C : ℤ := 1 + ∑ j ∈ F, ∑ i, w j.1 i
  have hC : ∀ j ∈ F, ∑ i, w j.1 i + 1 ≤ C := by
    intro j hj
    have := Finset.single_le_sum (f := fun j : P => ∑ i, w j.1 i)
      (fun j _ => Finset.sum_nonneg fun i _ => j.2.2.1 i) hj
    omega
  have hC1 : 1 ≤ C := by
    have := Finset.sum_nonneg (s := F) (f := fun j : P => ∑ i, w j.1 i) (fun j _ => Finset.sum_nonneg fun i _ => j.2.2.1 i)
    simp only [C]; omega
  have hPm : ∀ j : P, ∃ t ∈ maximalIdeal R, (j.1 : K) = algebraMap R K t := by
    intro j
    obtain ⟨t, ht⟩ := hv2 j.1 j.2.1 j.2.2.1
    refine ⟨t, ?_, ht⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, rfl⟩ := hu
    have hinv : ((j.1⁻¹ : Kˣ) : K) = algebraMap R K (u⁻¹ : Rˣ) := by
      rw [Units.val_inv_eq_inv_val, ht]; symm; apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    have hle : ∀ i, w j.1 i ≤ 0 := fun i => by
      have := hv1 i j.1⁻¹ _ hinv
      have h2 := winv j.1 i
      simp only [w] at h2 ⊢; omega
    have := j.2.2.2
    have := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hle i)
    omega
  have key : ∀ k : ℕ, ∀ x ∈ Γ, (∀ i, 0 ≤ w x i) → C * k ≤ ∑ i, w x i →
      ∃ t ∈ maximalIdeal R ^ k, (x : K) = algebraMap R K t := by
    intro k
    induction k with
    | zero =>
      intro x hx h0 _
      obtain ⟨t, ht⟩ := hv2 x hx h0
      exact ⟨t, by simp, ht⟩
    | succ k ih =>
      intro x hx h0 hsum
      have hpos : 0 < ∑ i, w x i := by push_cast at hsum; nlinarith
      obtain ⟨j, hjF, hjle⟩ := hF ⟨x, hx, h0, hpos⟩
      have hle : ∀ i, w j.1 i ≤ w x i := by
        intro i
        have h1 := hjle i
        have h2 := j.2.2.1 i
        have h3 := h0 i
        simp only at h1
        omega
      have hjC := hC j hjF
      obtain ⟨t', ht'm, ht'⟩ := ih (x * j.1⁻¹) (Γ.mul_mem hx (Γ.inv_mem j.2.1))
        (fun i => by rw [wmul, winv]; linarith [hle i])
        (by
          simp only [wmul, winv, Finset.sum_add_distrib, Finset.sum_neg_distrib]
          push_cast at hsum ⊢
          nlinarith)
      obtain ⟨t, htm, ht⟩ := hPm j
      refine ⟨t' * t, ?_, ?_⟩
      · rw [pow_succ]; exact Ideal.mul_mem_mul ht'm htm
      · rw [map_mul, ← ht', ← ht, ← Units.val_mul, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
  apply (GlobalTheory.T.finite_sublevel_of_int_quadratic_ge_one X q hqneg hqcube hqpos (C * n)).subset
  intro a ha
  by_contra hlt
  exact ha (key n (κ a) (hΓ a) (wκ a) (le_of_lt (not_le.mp hlt)))

end GlobalTheory.QuadTend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsPosCombinationDefiniteSum
section
open GlobalTheory.PolFan GlobalTheory.LocM

noncomputable section

namespace GlobalTheory.Poinc.MinSysLat

theorem finite_of_pos_lat {Y : Type} [AddCommGroup Y] {n : ℕ} (eb : Y ≃ₗ[ℤ] (Fin n → ℤ))
    (G : LinearMap.BilinForm ℤ Y) (hs : ∀ a b, G a b = G b a)
    (hn : ∀ x, 0 ≤ G x x) (hp : ∀ x, x ≠ 0 → 0 < G x x) (B : ℤ) : {x | G x x ≤ B}.Finite := by
  set G' : LinearMap.BilinForm ℤ (Fin n → ℤ) :=
    LinearMap.compl₁₂ G eb.symm.toLinearMap eb.symm.toLinearMap with hG'
  have happ : ∀ a b, G' a b = G (eb.symm a) (eb.symm b) := fun a b => rfl
  have h := GlobalTheory.Poinc.MinSys.finite_of_pos G' (fun a b => by rw [happ, happ, hs])
    (fun x => by rw [happ]; exact hn _)
    (fun x hx => by rw [happ]; exact hp _ (by simpa using hx)) B
  refine (h.preimage eb.injective.injOn).subset fun x hx => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq, happ, LinearEquiv.symm_apply_apply]
  exact hx

theorem finite_minimiser_systems_lat : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N] (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ Y), (∀ j x y, γ j x y = γ j y x) → (∀ j y, 0 ≤ γ j y y) → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ (b : LinearMap.BilinForm ℤ Y) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → μ ∈ S := by
  intro Y _ n N _ eb m γ hsym hnn hdef
  classical
  set G : LinearMap.BilinForm ℤ Y := ∑ j, γ j with hG
  have hGapp : ∀ a b, G a b = ∑ j, γ j a b := fun a b => by simp [hG, LinearMap.sum_apply]
  have hGsym : ∀ a b, G a b = G b a := fun a b => by simp only [hGapp, hsym _ a b]
  have hGnn : ∀ y, 0 ≤ G y y := fun y => by rw [hGapp]; exact Finset.sum_nonneg fun j _ => hnn j y
  have hGpos : ∀ x, x ≠ 0 → 0 < G x x := fun x hx => by rw [hGapp]; exact hdef x hx
  let T : (Fin n → ZMod N) → Type := fun c =>
    {α : Y // ∀ i, ((eb α i : ℤ) : ZMod N) = c i}
  have hD : ∀ c, ∃ F : Finset (T c), ∀ α : T c, ∃ β ∈ F,
      (fun j => (γ j β.1 β.1).toNat) ≤ (fun j => (γ j α.1 α.1).toNat) :=
    fun c => GlobalTheory.dickson_finite_below_every m (fun (α : T c) j => (γ j α.1 α.1).toNat)
  choose F hF using hD
  let Bd : (Fin n → ZMod N) → ℤ := fun c => ∑ β ∈ F c, G β.1 β.1
  have hfin : {μ : (Fin n → ZMod N) → Y | ∀ c, μ c ∈ {α | G α α ≤ Bd c}}.Finite :=
    Set.Finite.pi' fun c => finite_of_pos_lat eb G hGsym hGnn hGpos (Bd c)
  refine ⟨hfin.toFinset, fun b k cf hk hcf hkb μ hμ hmin => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro c
  obtain ⟨β, hβF, hβ⟩ := hF c ⟨μ c, hμ c⟩
  have hle : ∀ j, γ j β.1 β.1 ≤ γ j (μ c) (μ c) := fun j => by
    have h1 : (γ j β.1 β.1).toNat ≤ (γ j (μ c) (μ c)).toNat := hβ j
    have := hnn j β.1
    have := hnn j (μ c)
    omega
  have hkq : ∀ α, (k : ℤ) * b α α = ∑ j, (cf j : ℤ) * γ j α α := fun α => by
    have := congrArg (fun f : LinearMap.BilinForm ℤ Y => f α α) hkb
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] using this
  have h2 : ∑ j, (cf j : ℤ) * γ j (μ c) (μ c) ≤ ∑ j, (cf j : ℤ) * γ j β.1 β.1 := by
    rw [← hkq, ← hkq]
    exact mul_le_mul_of_nonneg_left (hmin c β.1 β.2) (by positivity)
  have h3 : ∀ j, γ j (μ c) (μ c) - γ j β.1 β.1 ≤
      (cf j : ℤ) * γ j (μ c) (μ c) - (cf j : ℤ) * γ j β.1 β.1 := fun j => by
    have h4 := hle j
    have h5 : (1 : ℤ) ≤ cf j := by exact_mod_cast hcf j
    nlinarith
  have h6 : ∑ j, γ j (μ c) (μ c) ≤ ∑ j, γ j β.1 β.1 := by
    have h7 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h3 j
    simp only [Finset.sum_sub_distrib] at h7
    linarith
  have h8 : G β.1 β.1 ≤ Bd c :=
    Finset.single_le_sum (f := fun β : T c => G β.1 β.1)
      (fun β _ => hGnn β.1) hβF
  rw [hGapp] at h8 ⊢
  linarith

end GlobalTheory.Poinc.MinSysLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedTorsionTransferJointlyMonicHomsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedTorsion_transfer_jointlyMonic_homs : ∀ (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (io : V →+* W) (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∀ (G : Over (Sp V)) [GrpObj G] (H : Over (Sp W)) [GrpObj H] (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), (∀ k, IsMonHom (r k)) → (∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y) → ∀ σ : F ≃+* F, (∀ w : W, σ (algebraMap (FractionRing W) F (algebraMap W _ w)) = algebraMap (FractionRing W) F (algebraMap W _ w)) → ∀ m : ℕ, (∀ y : TF (R := V) F ⟶ G, y ^ m = 1 → spMap σ.toRingHom ≫ y.left = y.left) → ∀ x : TF (R := W) F ⟶ H, x ^ m = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.TorsionTransfer.fixed_of_jointlyMonic | exact GlobalTheory.TorsionTransfer.fixed_of_jointlyMonic | (intros; apply GlobalTheory.TorsionTransfer.fixed_of_jointlyMonic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsAfterBaseChange
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBaseChange

variable {P Y B T T' : Scheme.{0}}

theorem pullbackComp_assoc_app (f : T' ⟶ P) (g : P ⟶ Y) (h : Y ⟶ B) (M : B.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M =
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫ eqToHom (by simp) := by
  have e := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at e
  rw [← e]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  simp

theorem pullbackCongr_hom_app {f f' : P ⟶ B} (H : f = f') (M : B.Modules) :
    (Scheme.Modules.pullbackCongr H).hom.app M = eqToHom (by rw [H]) := by
  subst H; simp [Scheme.Modules.pullbackCongr]

theorem pullbackComp_congr_app (v : T' ⟶ P) {k k' : P ⟶ B} (H : k = k') (M : B.Modules) :
    (Scheme.Modules.pullback v).map ((Scheme.Modules.pullbackCongr H).hom.app M) ≫
      (Scheme.Modules.pullbackComp v k').hom.app M =
    (Scheme.Modules.pullbackComp v k).hom.app M ≫ eqToHom (by rw [H]) := by
  subst H; simp [Scheme.Modules.pullbackCongr]

def baseIso (f₁ : P ⟶ Y) (p : Y ⟶ B) (f₂ : P ⟶ T) (q : T ⟶ B) (cond : f₁ ≫ p = f₂ ≫ q) (M : B.Modules) :
    (Scheme.Modules.pullback f₁).obj ((Scheme.Modules.pullback p).obj M) ≅
      (Scheme.Modules.pullback f₂).obj ((Scheme.Modules.pullback q).obj M) :=
  (Scheme.Modules.pullbackComp f₁ p).app M ≪≫ (Scheme.Modules.pullbackCongr cond).app M ≪≫
    ((Scheme.Modules.pullbackComp f₂ q).app M).symm

theorem baseIso_coherence (f₁ : P ⟶ Y) (p : Y ⟶ B) (f₂ : P ⟶ T) (q : T ⟶ B) (cond : f₁ ≫ p = f₂ ≫ q)
    (v : T' ⟶ P) (w : (v ≫ f₁) ≫ p = (v ≫ f₂) ≫ q) (M : B.Modules) :
    (Scheme.Modules.pullback v).map (baseIso f₁ p f₂ q cond M).hom ≫
        (Scheme.Modules.pullbackComp v f₂).hom.app _ ≫ (Scheme.Modules.pullbackComp (v ≫ f₂) q).hom.app M =
      (Scheme.Modules.pullbackComp v f₁).hom.app _ ≫ (Scheme.Modules.pullbackComp (v ≫ f₁) p).hom.app M ≫
        (Scheme.Modules.pullbackCongr w).hom.app M := by
  rw [pullbackComp_assoc_app, ← Category.assoc ((Scheme.Modules.pullbackComp v f₁).hom.app _),
    pullbackComp_assoc_app]
  simp only [baseIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc (Scheme.Modules.pullback v) ((Scheme.Modules.pullbackComp f₂ q).inv.app M),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc
      ((Scheme.Modules.pullback v).map ((Scheme.Modules.pullbackCongr cond).hom.app M)),
    pullbackComp_congr_app, pullbackCongr_hom_app]
  simp

def sqFlag (f₁ : P ⟶ Y) (p : Y ⟶ B) (f₂ : P ⟶ T) (q : T ⟶ B) (cond : f₁ ≫ p = f₂ ≫ q) {M : B.Modules} {n : ℕ}
    (fl : Vert.Flag ((Scheme.Modules.pullback p).obj M) n) :
    Vert.Flag ((Scheme.Modules.pullback f₂).obj ((Scheme.Modules.pullback q).obj M)) n :=
  (fl.pull f₁).ofIso (baseIso f₁ p f₂ q cond M)

theorem sqFlag_iff (f₁ : P ⟶ Y) (p : Y ⟶ B) (f₂ : P ⟶ T) (q : T ⟶ B) (cond : f₁ ≫ p = f₂ ≫ q)
    {M : B.Modules} {n : ℕ} (fl : Vert.Flag ((Scheme.Modules.pullback p).obj M) n)
    (v : T' ⟶ P) (h : T' ⟶ T) (hv : v ≫ f₂ = h) (w : (v ≫ f₁) ≫ p = h ≫ q)
    (fl'' : Vert.Flag ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback q).obj M)) n) (i : Fin (n + 1)) :
    (∃ e : (Scheme.Modules.pullback v).obj ((sqFlag f₁ p f₂ q cond fl).F i) ≅ fl''.F i,
      e.hom ≫ fl''.ι i = (Scheme.Modules.pullback v).map ((sqFlag f₁ p f₂ q cond fl).ι i) ≫
        (Scheme.Modules.pullbackComp v f₂).hom.app _ ≫ (Scheme.Modules.pullbackCongr hv).hom.app _) ↔
    (∃ e : (Scheme.Modules.pullback (v ≫ f₁)).obj (fl.F i) ≅
        (fl''.ofIso ((Scheme.Modules.pullbackComp h q).app M)).F i,
      e.hom ≫ (fl''.ofIso ((Scheme.Modules.pullbackComp h q).app M)).ι i =
        (Scheme.Modules.pullback (v ≫ f₁)).map (fl.ι i) ≫
          (Scheme.Modules.pullbackComp (v ≫ f₁) p).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M) := by
  subst hv
  have coh := baseIso_coherence f₁ p f₂ q cond v w M
  have nat := (Scheme.Modules.pullbackComp v f₁).hom.naturality (fl.ι i)
  simp only [Functor.comp_map] at nat
  constructor
  · rintro ⟨e, he⟩
    refine ⟨((Scheme.Modules.pullbackComp v f₁).app _).symm ≪≫ e, ?_⟩
    erw [Iso.trans_hom]
    simp only [Vert.Flag.ofIso, sqFlag, Vert.Flag.pull, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
      Category.assoc] at he ⊢
    rw [reassoc_of% he, pullbackCongr_hom_app (f := v ≫ f₂)]
    simp only [eqToHom_refl, Category.id_comp, Functor.map_comp, Category.assoc]
    rw [coh, reassoc_of% nat, Iso.inv_hom_id_app_assoc]
  · rintro ⟨e, he⟩
    refine ⟨(Scheme.Modules.pullbackComp v f₁).app _ ≪≫ e, ?_⟩
    erw [Iso.trans_hom]
    simp only [Vert.Flag.ofIso, sqFlag, Vert.Flag.pull, Iso.app_hom, Category.assoc] at he ⊢
    rw [← cancel_mono ((Scheme.Modules.pullbackComp (v ≫ f₂) q).hom.app M)]
    simp only [Category.assoc]
    rw [he, pullbackCongr_hom_app (f := v ≫ f₂)]
    simp only [eqToHom_refl, Category.id_comp, Functor.map_comp, Category.assoc]
    rw [coh, reassoc_of% nat]

theorem isFlagBundle_pullback_snd : ∀ (B Y T : Scheme.{0}) (π : Y ⟶ B) (g : T ⟶ B) (ι : Type) [Fintype ι]
    (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
    IsFlagBundle π E r fl → ∃ fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback (pullback.snd π g)).obj
      ((Scheme.Modules.pullback g).obj (E a))) (r a),
      IsFlagBundle (pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r fl' := by
  intro B Y T π g ι _ E r fl hfl
  refine ⟨fun a => sqFlag (pullback.fst π g) π (pullback.snd π g) g pullback.condition (fl a), ?_⟩
  intro T' h fl''
  obtain ⟨u, ⟨wu, hu⟩, huniq⟩ := hfl T' (h ≫ g)
    (fun a => (fl'' a).ofIso ((Scheme.Modules.pullbackComp h g).app (E a)))
  have hfst := pullback.lift_fst u h wu
  refine ⟨pullback.lift u h wu, ⟨pullback.lift_snd _ _ _, fun a i => ?_⟩, ?_⟩
  · rw [sqFlag_iff _ _ _ _ _ (fl a) _ h (pullback.lift_snd _ _ _) (by rw [hfst]; exact wu)]
    have key : ∀ (u' : T' ⟶ Y) (e : u' = u) (w' : u' ≫ π = h ≫ g),
        ∃ e : (Scheme.Modules.pullback u').obj ((fl a).F i) ≅
          ((fl'' a).ofIso ((Scheme.Modules.pullbackComp h g).app (E a))).F i,
        e.hom ≫ ((fl'' a).ofIso ((Scheme.Modules.pullbackComp h g).app (E a))).ι i =
          (Scheme.Modules.pullback u').map ((fl a).ι i) ≫
            (Scheme.Modules.pullbackComp u' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w').hom.app (E a) := by
      intro u' e w'
      subst e
      exact hu a i
    exact key _ hfst _
  · rintro v ⟨hv, hprop⟩
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      have w : (v ≫ pullback.fst π g) ≫ π = h ≫ g := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hv]
      exact huniq _ ⟨w, fun a i => (sqFlag_iff _ _ _ _ pullback.condition (fl a) v h hv w (fl'' a) i).1
        (hprop a i)⟩
    · rw [pullback.lift_snd]
      exact hv

end GlobalTheory.FlagBaseChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFramesTriangularComponentStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagBundlePointFramesTriangular_component : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C := by
  first | exact @GlobalTheory.VarFlag.carriesTri | exact GlobalTheory.VarFlag.carriesTri | (intros; apply GlobalTheory.VarFlag.carriesTri <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChartFramesEigenFramesLocalRingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagChartFrames_eigenFrames_localRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X := by
  first | exact @GlobalTheory.VarFlag.framesExist_flagCover | exact GlobalTheory.VarFlag.framesExist_flagCover | (intros; apply GlobalTheory.VarFlag.framesExist_flagCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.Mean4O GlobalTheory.TrueGeo GlobalTheory.ProjVar

namespace GlobalTheory.FlagInd

def FlagInduces {F : Type} [Field F] [NumberField F] {C : CxSt F} (Yv : Var F) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 F))
    {ι : Type} (E : ι → Bs.Modules) (n : ι → ℕ) (h : ∀ a, VMetric q (E a) (n a)) (H : ∀ a, (h a).IsCInf)
    (A : ∀ a, Fin (n a) → Adl C Yv) (Y : Scheme.{0}) [IsIntegral Y] (π : Y ⟶ Bs)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (arY : IsArithVar (π ≫ q) Yv.dim)
    (nY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y) : Prop :=
  ∃ (G : Scheme.{0}) (_ : IsIntegral G) (j : G ⟶ Y) (πG : G ⟶ Yv.X)
    (pb : IsPullback j (πG ≫ Yv.str) (π ≫ q) (spMap (algebraMap (𝓞 F) F)))
    (_ : IsFinite πG) (_ : Surjective πG) (φ : Yv.Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ Yv.X.fromSpecStalk (genericPoint Yv.X)),
    ∀ (a : ι) (i : Fin (n a)),
      (@Cover.mk _ _ Yv Y _ (π ≫ q) arY nY G _ j πG pb _ _ φ φs).Induces (A a i)
        (VMetric.grLB (fl a) i ((H a).pull π rfl)) 1

end GlobalTheory.FlagInd

end
end

