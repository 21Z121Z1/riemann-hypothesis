import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusOrbitLatticeCountBoundedByRho
section
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.TorusOrbitLat

section General

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

theorem mem_stabLat_iff (t : Aˣ) (L : Submodule O A) :
    t ∈ stabLat O L ↔ ∀ y, y ∈ L ↔ (t : A) * y ∈ L := Iff.rfl

theorem mem_intUnits_iff (t : Aˣ) :
    t ∈ intUnits O A ↔ IsIntegral O (t : A) ∧ IsIntegral O ((t⁻¹ : Aˣ) : A) := Iff.rfl

theorem mem_mulLat_unit (u : Aˣ) (L : Submodule O A) (w : A) :
    w ∈ mulLat O (u : A) L ↔ ((u⁻¹ : Aˣ) : A) * w ∈ L := by
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem mulLat_eq_iff (u v : Aˣ) (L : Submodule O A) :
    mulLat O (u : A) L = mulLat O (v : A) L ↔ u⁻¹ * v ∈ stabLat O L := by
  rw [mem_stabLat_iff]
  constructor
  · intro h y
    calc y ∈ L ↔ (v : A) * y ∈ mulLat O (v : A) L := by rw [mem_mulLat_unit]; simp
      _ ↔ (v : A) * y ∈ mulLat O (u : A) L := by rw [h]
      _ ↔ ((u⁻¹ * v : Aˣ) : A) * y ∈ L := by rw [mem_mulLat_unit, Units.val_mul, mul_assoc]
  · intro h
    ext w
    rw [mem_mulLat_unit, mem_mulLat_unit, h (((v⁻¹ : Aˣ) : A) * w)]
    simp [mul_assoc]

theorem isIntegral_inv_mul_iff (t u : Aˣ) (hu : u ∈ intUnits O A) (w : A) :
    IsIntegral O ((((t * u)⁻¹ : Aˣ) : A) * w) ↔ IsIntegral O (((t⁻¹ : Aˣ) : A) * w) := by
  rw [mem_intUnits_iff] at hu
  rw [mul_inv_rev, Units.val_mul, mul_assoc]
  constructor
  · intro h
    have := hu.1.mul h
    simpa using this
  · intro h
    exact hu.2.mul h

end General

section Main

variable {K : UQ} (B : InvAlg K)

theorem rho_cond_mk (t : B.T) (w : B.A) :
    IsIntegral K.O (((((Quotient.out (QuotientGroup.mk t : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T) : B.T) :
      B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w) ↔ IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((intUnits K.O B.A).subgroupOf B.T) t
  rw [hh, Subgroup.coe_mul]
  exact isIntegral_inv_mul_iff _ _ (Subgroup.mem_subgroupOf.mp h.2) w

theorem orbit_count : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A → (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 → ∀ a : K.O, (∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j)) → ∀ m k : ℕ, m ≤ k → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ m * y ∈ L) → (∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ m * y)) → Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k - m)) ≤ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ≤ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k + m)) := by
  intro K B L hSle hidx a hrho m k hmk hin hout
  set w : B.A := algebraMap K.O B.A a with hw
  set H : Subgroup B.T := (stabLat K.O L).subgroupOf B.T with hH
  set Kc : Subgroup B.T := (intUnits K.O B.A).subgroupOf B.T with hKc
  have hHK : H ≤ Kc := by
    intro x hx
    rw [hH, Subgroup.mem_subgroupOf] at hx
    rw [hKc, Subgroup.mem_subgroupOf]
    exact hSle ⟨hx, x.2⟩
  have hidx_eq : (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) = (H.subgroupOf Kc).index := by
    rw [← Subgroup.relIndex_subgroupOf (inf_le_right : intUnits K.O B.A ⊓ B.T ≤ B.T),
      Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_right]
    rfl
  have hQfin : Finite (Kc ⧸ H.subgroupOf Kc) := by
    rw [← Subgroup.index_ne_zero_iff_finite, ← hidx_eq]; exact hidx
  have hRfin : ∀ j, Finite {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ j : B.A)} :=
    fun j => (Nat.card_pos_iff.mp (hrho j)).2
  have hrho_eq : ∀ j, B.rho (w ^ j) = Nat.card {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ j : B.A)} :=
    fun j => rfl
  let e := Subgroup.quotientEquivProdOfLE hHK
  have he1 : ∀ g : B.T, (e (QuotientGroup.mk g)).1 = QuotientGroup.mk g := fun g => rfl

  let Y := {c : B.T ⧸ H // w ^ k ∈ mulLat K.O (((Quotient.out c : B.T) : B.Aˣ) : B.A) L}
  let fY : Y → {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ w ^ k ∈ M} :=
    fun c => ⟨mulLat K.O (((Quotient.out c.1 : B.T) : B.Aˣ) : B.A) L, ⟨_, (Quotient.out c.1).2, rfl⟩, c.2⟩
  have hfY : Function.Bijective fY := by
    constructor
    · rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
      have h' : mulLat K.O (((Quotient.out c : B.T) : B.Aˣ) : B.A) L = mulLat K.O (((Quotient.out c' : B.T) : B.Aˣ) : B.A) L :=
        congrArg Subtype.val h
      rw [mulLat_eq_iff] at h'
      apply Subtype.ext
      change c = c'
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using h')
    · rintro ⟨M, ⟨t, ht, rfl⟩, hM⟩
      have hc := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨t, ht⟩ : B.T ⧸ H))
      rw [hH, Subgroup.mem_subgroupOf] at hc
      have key : mulLat K.O (((Quotient.out (QuotientGroup.mk ⟨t, ht⟩ : B.T ⧸ H) : B.T) : B.Aˣ) : B.A) L =
          mulLat K.O (t : B.A) L := by
        rw [mulLat_eq_iff]; simpa using hc
      exact ⟨⟨_, key ▸ hM⟩, Subtype.ext key⟩
  have hcardXY := Nat.card_congr (Equiv.ofBijective fY hfY)

  have key1 : ∀ g : B.T, ((((g : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w ^ k ∈ L) →
      IsIntegral K.O ((((Quotient.out (e (QuotientGroup.mk g)).1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k + m) : B.A) := by
    intro g hg
    rw [he1 g, rho_cond_mk]
    have := hout _ hg
    convert this using 1
    rw [pow_add]; ring
  let U : Y → {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k + m) : B.A)} ×
      (Kc ⧸ H.subgroupOf Kc) := fun c =>
    (⟨(e c.1).1, by
      have := key1 (Quotient.out c.1) (by rw [← mem_mulLat_unit]; exact c.2)
      rwa [QuotientGroup.out_eq'] at this⟩, (e c.1).2)
  have hU : Function.Injective U := by
    intro c c' h
    apply Subtype.ext
    apply e.injective
    have h1 := congrArg (fun p => p.1.1) h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 h2
  have hYfin : Finite Y := by
    haveI := hRfin (k + m)
    exact Finite.of_injective U hU

  have key2 : ∀ g : B.T,
      IsIntegral K.O ((((Quotient.out (e (QuotientGroup.mk g)).1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k - m) : B.A) →
      w ^ k ∈ mulLat K.O ((g : B.Aˣ) : B.A) L := by
    intro g hg
    rw [he1 g, rho_cond_mk] at hg
    rw [mem_mulLat_unit]
    have := hin _ hg
    convert this using 1
    rw [← Nat.add_sub_cancel' hmk, pow_add, Nat.add_sub_cancel_left]; ring
  let D : {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k - m) : B.A)} ×
      (Kc ⧸ H.subgroupOf Kc) → Y := fun p =>
    ⟨e.symm (p.1.1, p.2), by
      have hc : e (e.symm (p.1.1, p.2)) = (p.1.1, p.2) := e.apply_symm_apply _
      apply key2
      rw [QuotientGroup.out_eq', hc]
      exact p.1.2⟩
  have hD : Function.Injective D := by
    intro p p' h
    have h' := e.symm.injective (congrArg Subtype.val h)
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact Prod.ext (Subtype.ext h1) h2
  refine ⟨?_, ?_, ?_⟩
  · exact Finite.of_equiv Y (Equiv.ofBijective fY hfY)
  · rw [← hcardXY, hidx_eq, hrho_eq, mul_comm]
    exact (Nat.card_prod _ _).symm.trans_le (Nat.card_le_card_of_injective D hD)
  · rw [← hcardXY, hidx_eq, hrho_eq, mul_comm]
    haveI := hRfin (k + m)
    exact (Nat.card_le_card_of_injective U hU).trans_eq (Nat.card_prod _ _)

end Main

end GlobalTheory.TorusOrbitLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportSelfDualHaarMeasureKernelAddEquiv
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TransportSD

theorem map_map_equiv_left {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (e : α ≃ᵐ β) (g : β → γ) : (μ.map e).map g = μ.map (g ∘ e) := by
  by_cases hg : AEMeasurable g (μ.map e)
  · exact AEMeasurable.map_map_of_aemeasurable hg e.measurable.aemeasurable
  · have hg' : ¬ AEMeasurable (g ∘ e) μ := by rwa [← aemeasurable_map_equiv_iff e]
    rw [Measure.map_of_not_aemeasurable hg, Measure.map_of_not_aemeasurable hg']

theorem map_map_equiv_right {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (T : α → β) (e : β ≃ᵐ γ) : (μ.map T).map e = μ.map (e ∘ T) := by
  by_cases hT : AEMeasurable T μ
  · exact AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hT
  · have hT' : ¬ AEMeasurable (e ∘ T) μ := by
      intro h
      apply hT
      have := e.symm.measurable.comp_aemeasurable h
      simpa [Function.comp_def] using this
    rw [Measure.map_of_not_aemeasurable hT, Measure.map_of_not_aemeasurable hT', Measure.map_zero]

end GlobalTheory.TransportSD

open GlobalTheory.TransportSD in
theorem GlobalTheory.transport_selfDual_fourB : ∀ {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] (h : V' ≃+ V), Continuous h → Continuous h.symm → ∀ (μ : Measure V) (B : V → V → ℂ), (SelfDual μ B → SelfDual (Measure.map h.symm μ) (fun x y => B (h x) (h y))) ∧ ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
  intro V V' _ _ _ _ _ _ _ _ h hc hs μ B
  let he : V ≃ₜ V' := { toEquiv := h.symm.toEquiv, continuous_toFun := hs, continuous_invFun := hc }
  let e : V ≃ᵐ V' := he.toMeasurableEquiv
  have he_eq : (e : V → V') = h.symm := rfl
  have hμ : Measure.map h.symm μ = Measure.map e μ := by rw [he_eq]
  have four : ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
    intro f y
    unfold fourB
    rw [hμ, integral_map_equiv]
    congr 1
    funext v
    rw [he_eq]
    simp
  refine ⟨fun hsd => ⟨?_, ?_⟩, four⟩
  · obtain ⟨hH, -⟩ := hsd
    rw [hμ]
    have h1 : IsFiniteMeasureOnCompacts (Measure.map e μ) := by
      refine ⟨fun K hK => ?_⟩
      rw [MeasurableEquiv.map_apply]
      have : (e : V → V') ⁻¹' K = h '' K := by
        ext v; rw [he_eq]; simp [Set.mem_image]
        constructor
        · intro hv; exact ⟨h.symm v, hv, by simp⟩
        · rintro ⟨w, hw, rfl⟩; simpa using hw
      rw [this]
      exact (hK.image hc).measure_lt_top
    have h2 : (Measure.map e μ).IsAddLeftInvariant := by
      refine ⟨fun x' => ?_⟩
      rw [map_map_equiv_left]
      have hcomp : (fun y' => x' + y') ∘ (e : V → V') = (e : V → V') ∘ (fun v => h x' + v) := by
        funext v; rw [he_eq]; simp
      rw [hcomp, ← map_map_equiv_right, hH.toIsAddLeftInvariant.map_add_left_eq_self (h x')]
    have h3 : (Measure.map e μ).IsOpenPosMeasure := by
      refine ⟨fun U hU hne => ?_⟩
      rw [MeasurableEquiv.map_apply]
      have hU' : IsOpen ((e : V → V') ⁻¹' U) := hU.preimage (by rw [he_eq]; exact hs)
      have hne' : ((e : V → V') ⁻¹' U).Nonempty := by
        obtain ⟨u, hu⟩ := hne
        exact ⟨h u, by rw [he_eq]; simpa using hu⟩
      exact hU'.measure_ne_zero μ hne'
    exact { toIsFiniteMeasureOnCompacts := h1, toIsAddLeftInvariant := h2, toIsOpenPosMeasure := h3 }
  · intro f hf y
    have hf' : IsTest (fun v => f (h.symm v)) :=
      ⟨hf.1.comp_continuous hs, hf.2.comp_homeomorph he⟩
    rw [four]
    have : (fun v => fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f (h.symm v)) =
        fourB μ B (fun v => f (h.symm v)) := by
      funext v; rw [four]; simp
    rw [this, hsd.2 _ hf' (h y)]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
section
open GlobalTheory.Tw Matrix Polynomial

noncomputable section

namespace GlobalTheory.Tw.CentralizerAdjoin

section Dual
variable {n : ℕ} {R : Type} [CommRing R]

def dm (U V : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) (DualNumber R) :=
  Matrix.of fun i j => TrivSqZeroExt.inl (U i j) + TrivSqZeroExt.inr (V i j)

theorem dm_fst (U V : Matrix (Fin n) (Fin n) R) : (dm U V).map TrivSqZeroExt.fst = U := by
  ext i j; simp [dm]

theorem dm_snd (U V : Matrix (Fin n) (Fin n) R) : (dm U V).map TrivSqZeroExt.snd = V := by
  ext i j; simp [dm]

theorem dm_one : dm (1 : Matrix (Fin n) (Fin n) R) 0 = 1 := by
  ext i j : 1
  refine TrivSqZeroExt.ext ?_ ?_ <;> by_cases h : i = j <;> simp [dm, Matrix.one_apply, h]

theorem dm_mul (U V U' V' : Matrix (Fin n) (Fin n) R) :
    dm U V * dm U' V' = dm (U * U') (U * V' + V * U') := by
  ext i j : 1
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [dm, Matrix.mul_apply, TrivSqZeroExt.fst_sum]
  · simp [dm, Matrix.mul_apply, TrivSqZeroExt.snd_sum, Finset.sum_add_distrib, mul_comm]

theorem dm_smul (a : DualNumber R) (U V : Matrix (Fin n) (Fin n) R) :
    a • dm U V = dm (a.fst • U) (a.fst • V + a.snd • U) := by
  ext i j : 1
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [dm]
  · simp [dm, mul_comm]

theorem dm_pow (N g : Matrix (Fin n) (Fin n) R) (hc : g * N = N * g) (k : ℕ) :
    dm N g ^ (k + 1) = dm (N ^ (k + 1)) (((k + 1 : ℕ) : R) • (N ^ k * g)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, dm_mul]
    congr 1
    rw [Matrix.smul_mul, Matrix.mul_assoc (N ^ k) g N, hc, ← Matrix.mul_assoc, ← pow_succ]
    rw [show (((k + 1 + 1 : ℕ) : R)) = ((k + 1 : ℕ) : R) + 1 by push_cast; ring, add_smul, one_smul]
    abel
end Dual
end GlobalTheory.Tw.CentralizerAdjoin

namespace GlobalTheory.Tw.CentralizerAdjoin
section Comm
variable {n : ℕ} {R : Type} [CommRing R]

theorem snd_aeval (N g : Matrix (Fin n) (Fin n) R) (hc : g * N = N * g) (P : (DualNumber R)[X]) :
    ∃ Q : R[X], (aeval (dm N g) P).map TrivSqZeroExt.snd =
      aeval N (derivative (P.map (TrivSqZeroExt.fstHom R R R).toRingHom)) * g + aeval N Q := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨Q1, h1⟩ := hp
    obtain ⟨Q2, h2⟩ := hq
    refine ⟨Q1 + Q2, ?_⟩
    rw [map_add, Matrix.map_add _ TrivSqZeroExt.snd_add, h1, h2, Polynomial.map_add, derivative_add,
      map_add, map_add, Matrix.add_mul]
    abel
  | monomial k a =>
    cases k with
    | zero =>
      refine ⟨C a.snd, ?_⟩
      rw [aeval_monomial, pow_zero, mul_one, Algebra.algebraMap_eq_smul_one, ← dm_one, dm_smul, dm_snd]
      simp [Algebra.algebraMap_eq_smul_one]
    | succ k =>
      refine ⟨monomial (k + 1) a.snd, ?_⟩
      rw [aeval_monomial, ← Algebra.smul_def, dm_pow N g hc, dm_smul, dm_snd, Polynomial.map_monomial,
        derivative_monomial, aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply, add_tsub_cancel_right,
        smul_zero, zero_add, Matrix.smul_mul, smul_smul]

theorem mem_adjoin_of_commute (N g : Matrix (Fin n) (Fin n) R) (hs : N.charpoly.Separable)
    (hc : g * N = N * g) : g ∈ Algebra.adjoin R {N} := by
  obtain ⟨Q, hQ⟩ := snd_aeval N g hc (dm N g).charpoly
  have hf : (dm N g).map (TrivSqZeroExt.fstHom R R R).toRingHom = N := dm_fst N g
  rw [← Matrix.charpoly_map, hf, Matrix.aeval_self_charpoly, Matrix.map_zero _ rfl] at hQ
  obtain ⟨a, b, hab⟩ := hs
  have h1 : aeval N b * aeval N (derivative N.charpoly) = 1 := by
    have := congrArg (aeval N) hab
    rwa [map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, Matrix.mul_zero, zero_add, map_one] at this
  have h2 : g = - aeval N (b * Q) := by
    rw [map_mul, ← Matrix.mul_neg, ← eq_neg_iff_add_eq_zero.mpr hQ.symm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [h2]
  exact neg_mem (aeval_mem_adjoin_singleton R N)

end Comm
end GlobalTheory.Tw.CentralizerAdjoin

namespace GlobalTheory.Tw.CentralizerAdjoin
section Tw
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model

theorem inv_mem_adjoin_of_isUnit {N : Matrix (Fin n) (Fin n) R} (hN : IsUnit N) :
    N⁻¹ ∈ Algebra.adjoin R {N} := by
  have hd := (Matrix.isUnit_iff_isUnit_det N).mp hN
  have hc : IsUnit (N.charpoly.coeff 0) := by
    rw [Matrix.det_eq_sign_charpoly_coeff] at hd
    exact isUnit_of_mul_isUnit_right hd
  have key := congrArg (aeval N) (Polynomial.X_mul_divX_add N.charpoly)
  rw [Matrix.aeval_self_charpoly, map_add, map_mul, aeval_X, aeval_C] at key
  have hinv : N⁻¹ = -((hc.unit⁻¹ : Rˣ) : R) • aeval N (divX N.charpoly) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, eq_neg_iff_add_eq_zero.mpr key, smul_neg, neg_smul, neg_neg,
      Algebra.algebraMap_eq_smul_one, smul_smul, hc.val_inv_mul, one_smul]
  rw [hinv]
  exact Subalgebra.smul_mem _ (aeval_mem_adjoin_singleton R N) _

theorem adj_mul' {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (g h : Matrix (Fin n) (Fin n) R) :
    adj δ (g * h) = adj δ h * adj δ g := by
  have hd := (Matrix.isUnit_iff_isUnit_det δ).mp hδ
  simp only [adj, conjTranspose_mul, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd, ← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R),
    transpose_mul_Phi, Matrix.one_mul]

theorem adj_semi (δ : Matrix (Fin n) (Fin n) R) (c : R) (g h : Matrix (Fin n) (Fin n) R) :
    adj δ (c • g + h) = star c • adj δ g + adj δ h := by
  simp only [adj, conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem adj_one' {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : adj δ 1 = 1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det δ).mp hδ
  rw [adj, conjTranspose_one, Matrix.mul_one, Matrix.mul_assoc δ, Phi_mul_transpose, Matrix.mul_one,
    Matrix.mul_nonsing_inv _ hd]

theorem adj_algebraMap {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (r : R) :
    adj δ (algebraMap R _ r) = algebraMap R _ (star r) := by
  have h := adj_semi δ r 1 0
  rw [add_zero, adj_one' hδ] at h
  have h0 : adj δ 0 = 0 := by simp [adj]
  rw [h0, add_zero] at h
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, h]

theorem isUnit_theta' {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : IsUnit (theta δ) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse (theta_mul_theta_inv hδ))

theorem isUnit_nrm {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : IsUnit (nrm δ) :=
  hδ.mul (isUnit_theta' hδ)

theorem adj_nrm {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : adj δ (nrm δ) = (nrm δ)⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det δ).mp hδ
  rw [adj_eq hδ (isUnit_nrm hδ)]
  congr 1
  rw [nrm, theta_mul, theta_theta hδ]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

theorem commute_of_mem (N g : Matrix (Fin n) (Fin n) R) (hg : g ∈ Algebra.adjoin R {N}) :
    g * N = N * g := by
  induction hg using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]
  | algebraMap r => exact Algebra.commutes r N
  | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
  | mul x y _ _ hx hy => rw [Matrix.mul_assoc, hy, ← Matrix.mul_assoc, hx, Matrix.mul_assoc]

theorem adj_adjoin {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (g : Matrix (Fin n) (Fin n) R)
    (hg : g ∈ Algebra.adjoin R {nrm δ}) :
    adj δ g ∈ Algebra.adjoin R {nrm δ} ∧ adj δ (adj δ g) = g := by
  have hN := isUnit_nrm hδ
  have hNd := (Matrix.isUnit_iff_isUnit_det _).mp hN
  have hadd : ∀ x y : Matrix (Fin n) (Fin n) R, adj δ (x + y) = adj δ x + adj δ y := fun x y => by
    simpa using adj_semi δ 1 x y
  have hinvN : adj δ (nrm δ)⁻¹ = nrm δ := by
    have h1 : adj δ (nrm δ)⁻¹ * (nrm δ)⁻¹ = 1 := by
      calc adj δ (nrm δ)⁻¹ * (nrm δ)⁻¹ = adj δ (nrm δ)⁻¹ * adj δ (nrm δ) := by rw [adj_nrm hδ]
        _ = adj δ (nrm δ * (nrm δ)⁻¹) := (adj_mul' hδ _ _).symm
        _ = 1 := by rw [Matrix.mul_nonsing_inv _ hNd, adj_one' hδ]
    calc adj δ (nrm δ)⁻¹ = adj δ (nrm δ)⁻¹ * (nrm δ)⁻¹ * nrm δ := by
          rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hNd, Matrix.mul_one]
      _ = nrm δ := by rw [h1, Matrix.one_mul]
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx, adj_nrm hδ, hinvN]
    exact ⟨inv_mem_adjoin_of_isUnit hN, rfl⟩
  | algebraMap r =>
    rw [adj_algebraMap hδ, adj_algebraMap hδ, star_star]
    exact ⟨Subalgebra.algebraMap_mem _ _, rfl⟩
  | add x y _ _ hx hy =>
    rw [hadd, hadd, hx.2, hy.2]
    exact ⟨add_mem hx.1 hy.1, rfl⟩
  | mul x y _ _ hx hy =>
    rw [adj_mul' hδ, adj_mul' hδ, hx.2, hy.2]
    exact ⟨mul_mem hy.1 hx.1, rfl⟩

end Tw
end GlobalTheory.Tw.CentralizerAdjoin

namespace GlobalTheory.Tw.CentralizerAdjoin
section Cent
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model

theorem cent_eq {δ : Matrix (Fin n) (Fin n) R} (hδ : Reg δ) :
    cent δ = {g | g ∈ Algebra.adjoin R {nrm δ} ∧ g * adj δ g = 1} := by
  have hu := hδ.1
  have hd := (Matrix.isUnit_iff_isUnit_det δ).mp hu
  ext g
  constructor
  · rintro ⟨hgU, hgd⟩
    have hc : g * nrm δ = nrm δ * g :=
      calc g * nrm δ = g * δ * theta δ := by rw [nrm, Matrix.mul_assoc]
        _ = δ * theta g * theta δ := by rw [hgd]
        _ = δ * theta (g * δ) := by rw [theta_mul, Matrix.mul_assoc]
        _ = δ * theta (δ * theta g) := by rw [hgd]
        _ = nrm δ * g := by rw [theta_mul, theta_theta hgU, nrm, Matrix.mul_assoc]
    refine ⟨mem_adjoin_of_commute _ g hδ.2 hc, ?_⟩
    rw [adj_eq hu hgU, ← hgd, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hgU)]
  · rintro ⟨-, h⟩
    have hgd := Matrix.isUnit_det_of_right_inverse h
    have hgU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr hgd
    have hU1 : IsUnit (δ * theta g * δ⁻¹) :=
      (hu.mul (isUnit_theta' hgU)).mul (Matrix.isUnit_nonsing_inv_iff.mpr hu)
    have h2 : (δ * theta g * δ⁻¹)⁻¹ = g⁻¹ := by
      rw [← adj_eq hu hgU]; exact (Matrix.inv_eq_right_inv h).symm
    have e := congrArg Inv.inv h2
    rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU1),
      Matrix.nonsing_inv_nonsing_inv _ hgd] at e
    refine ⟨hgU, ?_⟩
    calc g * δ = δ * theta g * δ⁻¹ * δ := by rw [e]
      _ = δ * theta g := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]

end Cent
end GlobalTheory.Tw.CentralizerAdjoin

open GlobalTheory.Tw.CentralizerAdjoin in

theorem GlobalTheory.Tw.twisted_centraliser :
    ∀ (n : ℕ) (R : Type) [CommRing R] [StarRing R] [IsArtinianRing R] [IsReduced R] (δ : Matrix (Fin n) (Fin n) R),
      Reg δ → (∀ g h, adj δ (g * h) = adj δ h * adj δ g) ∧ (∀ (c : R) g h, adj δ (c • g + h) = star c • adj δ g + adj δ h) ∧
        adj δ (nrm δ) = (nrm δ)⁻¹ ∧
        (∀ g ∈ Algebra.adjoin R {nrm δ}, adj δ g ∈ Algebra.adjoin R {nrm δ} ∧ adj δ (adj δ g) = g) ∧
        (∀ g, g * nrm δ = nrm δ * g ↔ g ∈ Algebra.adjoin R {nrm δ}) ∧
        cent δ = {g | g ∈ Algebra.adjoin R {nrm δ} ∧ g * adj δ g = 1} := by
  intro n R _ _ _ _ δ hδ
  exact ⟨adj_mul' hδ.1, adj_semi δ, adj_nrm hδ.1, adj_adjoin hδ.1,
    fun g => ⟨mem_adjoin_of_commute _ g hδ.2, commute_of_mem _ g⟩, cent_eq hδ⟩
end
end

