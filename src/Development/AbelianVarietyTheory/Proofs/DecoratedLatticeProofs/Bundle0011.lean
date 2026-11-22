import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchrodingerIntertwinerIntegralMatrices
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducedBasisIntegralConjEntriesBounded
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetEqSumIndicatorOfPeriodic
section
open ValuativeRel Matrix GlobalTheory.SplitWeil
open scoped Topology

namespace GlobalTheory.RootEx

theorem exists_finset_eq_sum_indicator_of_periodic {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] {Φ : X → ℂ} (hcs : IsCompact (tsupport Φ)) (V : AddSubgroup X)
    (hV : IsOpen (V : Set X)) (hper : ∀ x, ∀ y ∈ V, Φ (x + y) = Φ x) :
    ∃ s : Finset X, ∀ t, Φ t = ∑ a ∈ s, Φ a * (V : Set X).indicator (fun _ => (1 : ℂ)) (t - a) := by
  classical
  obtain ⟨s0, -, hcov⟩ := hcs.elim_nhds_subcover (fun a => {x | x - a ∈ V}) (fun a _ =>
    (hV.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp [V.zero_mem]))
  refine ⟨(s0.image (fun a : X => (QuotientAddGroup.mk a : X ⧸ V))).image Quotient.out, fun t => ?_⟩
  have hmk : ∀ a : X, t - a ∈ V → (a : X ⧸ V) = (t : X ⧸ V) := fun a h => by
    rw [QuotientAddGroup.eq]; simpa [sub_eq_neg_add] using h
  have huniq : ∀ a ∈ (s0.image (fun a : X => (QuotientAddGroup.mk a : X ⧸ V))).image Quotient.out,
      ∀ b ∈ (s0.image (fun a : X => (QuotientAddGroup.mk a : X ⧸ V))).image Quotient.out, t - a ∈ V → t - b ∈ V → a = b := by
    intro a ha b hb hta htb
    obtain ⟨qa, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨qb, -, rfl⟩ := Finset.mem_image.1 hb
    have h1 := hmk _ hta
    have h2 := hmk _ htb
    rw [QuotientAddGroup.out_eq'] at h1 h2
    rw [h1, h2]
  by_cases h : ∃ a ∈ (s0.image (fun a : X => (QuotientAddGroup.mk a : X ⧸ V))).image Quotient.out, t - a ∈ V
  · obtain ⟨a, ha, hta⟩ := h
    rw [Finset.sum_eq_single a (fun b hb hba => by
      rw [Set.indicator_of_notMem (fun htb => hba (huniq b hb a ha htb hta)), mul_zero])
      (fun h' => absurd ha h'), Set.indicator_of_mem hta, mul_one]
    have := hper a (t - a) hta
    rwa [add_sub_cancel] at this
  · push_neg at h
    rw [Finset.sum_eq_zero (fun b hb => by rw [Set.indicator_of_notMem (h b hb), mul_zero])]
    by_contra hne
    have ht : t ∈ tsupport Φ := subset_tsupport _ hne
    obtain ⟨a0, ha0, hta0⟩ := Set.mem_iUnion₂.1 (hcov ht)
    have hT : (a0 : X ⧸ V) ∈ s0.image (fun a : X => (QuotientAddGroup.mk a : X ⧸ V)) := Finset.mem_image_of_mem _ ha0
    refine h (Quotient.out (a0 : X ⧸ V)) (Finset.mem_image_of_mem _ hT) ?_
    have h1 : ((Quotient.out (a0 : X ⧸ V) : X) : X ⧸ V) = (t : X ⧸ V) := by
      rw [QuotientAddGroup.out_eq']; exact hmk a0 hta0
    rw [QuotientAddGroup.eq] at h1
    simpa [sub_eq_neg_add] using h1

end GlobalTheory.RootEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProductStatement
section
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_of_bilinear_schwartzBruhatProduct : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (M : Type) [AddCommGroup M] [Module ℂ M] (B : SB X →ₗ[ℂ] SB Y →ₗ[ℂ] M), ∃ l : SB (X × Y) →ₗ[ℂ] M, ∀ f g, l (prodSB f g) = B f g := by
  first | exact @GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB | exact GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB | (intros; apply GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchrodingerIntertwinerIntegralMatricesStatement
section
open ValuativeRel GlobalTheory.SplitWeil Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schrodinger_intertwiner_integralMatrices : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Z : Type) [AddCommGroup Z] (χ : Matrix Y Y' k → Z → ℂ), (∀ a b z, χ (a + b) z = χ a z * χ b z) → (∀ a z z', χ a (z + z') = χ a z * χ a z') → (∀ z, χ 0 z = 1) → (∀ a, χ a 0 = 1) → (∀ n : ℕ, 0 < n → ∀ z : Z, ∃ z' : Z, n • z' = z) → (∀ n : ℕ, 0 < n → Function.Injective fun z : Z => n • z) → (∀ x : Matrix Y Y' k, (∀ z, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1) → χ x z = 1) → ∀ r q, x r q ∈ 𝒪[k]) → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Matrix Y Y' k → M →ₗ[ℂ] M) (μ : Z → M →ₗ[ℂ] M), (∀ x x' f, τ x (τ x' f) = τ (x + x') f) → (∀ z z' f, μ z (μ z' f) = μ (z + z') f) → (∀ x z f, τ x (μ z f) = χ x z • μ z (τ x f)) → (∀ f, τ 0 f = f) → (∀ f, μ 0 f = f) → ∀ f₀ : M, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → τ u f₀ = f₀) → (∀ z, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1) → μ z f₀ = f₀) → ∃ Tm : SB (Matrix Y Y' k) →ₗ[ℂ] M, (∀ (x : Matrix Y Y' k) (Φ Φ' : SB (Matrix Y Y' k)), (∀ t, Φ'.1 t = Φ.1 (t + x)) → Tm Φ' = τ x (Tm Φ)) ∧ (∀ (z : Z) (Φ Φ' : SB (Matrix Y Y' k)), (∀ t, Φ'.1 t = χ t z * Φ.1 t) → Tm Φ' = μ z (Tm Φ)) ∧ (∀ Φ : SB (Matrix Y Y' k), Φ.1 = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) → Tm Φ = f₀) ∧ ∀ Φ, Tm Φ ∈ Submodule.span ℂ (Set.range fun w : Matrix Y Y' k × Z => τ w.1 (μ w.2 f₀)) := by
  first | exact @GlobalTheory.SchrodExist.exists_intertwiner_matrix | exact GlobalTheory.SchrodExist.exists_intertwiner_matrix | (intros; apply GlobalTheory.SchrodExist.exists_intertwiner_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
section
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology

namespace GlobalTheory.LocMod.Inhab

theorem exists_fixed {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] {χ : G → G → ℂ} (h : IsBichar χ)
    (ρ σ : G → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f) (hσ : ∀ y f, σ y f = 0 → f = 0)
    (hc : ∀ x y f, ρ x (σ y f) = χ x y • σ y (ρ x f)) (L K : AddSubgroup G) [Finite (L ⧸ K.addSubgroupOf L)]
    (hsep : ∀ u ∈ L, u ∉ K → ∃ y, (∀ κ ∈ K, χ κ y = 1) ∧ χ u y ≠ 1) (P : Submodule ℂ V)
    (hP : ∀ u ∈ L, ∀ f ∈ P, ρ u f ∈ P) (hP' : ∀ y, ∀ f ∈ P, σ y f ∈ P) {f : V} (hf : f ∈ P) (f0 : f ≠ 0)
    (hK : ∀ κ ∈ K, ρ κ f = f) : ∃ g ∈ P, g ≠ 0 ∧ ∀ u ∈ L, ρ u g = g := by
  classical
  letI : Fintype (L ⧸ K.addSubgroupOf L) := Fintype.ofFinite _
  let A : AddSubgroup G :=
    { carrier := {y | ∀ κ ∈ K, χ κ y = 1}
      zero_mem' := fun κ _ => h.zero_right κ
      add_mem' := fun {a b} ha hb κ hκ => by rw [h.right, ha κ hκ, hb κ hκ, mul_one]
      neg_mem' := fun {a} ha κ hκ => by
        have := h.right κ a (-a)
        rwa [add_neg_cancel, h.zero_right, ha κ hκ, one_mul, eq_comm] at this }
  have hcl : ∀ g : V, (∀ κ ∈ K, ρ κ g = g) → ∀ a b : L,
      (QuotientAddGroup.mk a : L ⧸ K.addSubgroupOf L) = QuotientAddGroup.mk b → ρ a g = ρ b g := fun g hg a b hab => by
    have : -(a : G) + b ∈ K := (QuotientAddGroup.eq (s := K.addSubgroupOf L)).1 hab
    rw [← hg _ this, hρ, add_neg_cancel_left, hg _ this]
  by_contra hcon
  have hz : ∀ y ∈ A, ∑ q : L ⧸ K.addSubgroupOf L, χ (q.out : L) y • ρ (q.out : L) f = 0 := fun y hy => by
    have hfix : ∀ κ ∈ K, ρ κ (σ y f) = σ y f := fun κ hκ => by rw [hc, hy κ hκ, hK κ hκ, one_smul]
    refine hσ y _ ?_
    simp only [map_sum, map_smul, ← hc]
    by_contra hne
    refine hcon ⟨_, P.sum_mem fun q _ => hP _ (q.out : L).2 _ (hP' y f hf), hne, fun u hu => ?_⟩
    rw [map_sum]
    refine Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk (⟨u, hu⟩ : L))) _ _ fun q => ?_
    rw [hρ]
    refine hcl _ hfix (⟨u, hu⟩ + q.out) _ ?_
    simp
  let ch : (L ⧸ K.addSubgroupOf L) → (Multiplicative A →* ℂ) := fun q =>
    { toFun := fun y => χ (q.out : L) (y.toAdd : A)
      map_one' := h.zero_right _
      map_mul' := fun a b => h.right _ _ _ }
  have hinj : Function.Injective ch := by
    intro q q' hq
    rw [← q.out_eq', ← q'.out_eq', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    by_contra hn
    obtain ⟨y, hy, hne⟩ := hsep _ (-q.out + q'.out : L).2 hn
    have e : χ (q.out : L) y = χ (q'.out : L) y := DFunLike.congr_fun hq (Multiplicative.ofAdd ⟨y, hy⟩)
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, h.left, ← e, h.neg_mul] at hne
    exact hne rfl
  have hli := (linearIndependent_monoidHom (Multiplicative A) ℂ).comp ch hinj
  rw [Fintype.linearIndependent_iff] at hli
  refine f0 ((Module.forall_dual_apply_eq_zero_iff ℂ f).1 fun ℓ => ?_)
  have := hli (fun q => ℓ (ρ (q.out : L) f)) (by
    funext y
    have := congrArg ℓ (hz _ y.toAdd.2)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    rw [Finset.sum_apply]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) this
    simp [ch, mul_comm]) (QuotientAddGroup.mk 0)
  rwa [hcl f hK _ 0 (QuotientAddGroup.out_eq' _), hK ((0 : L) : G) K.zero_mem] at this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

variable (Y Y') in

def box (a : kˣ) : AddSubgroup (Matrix Y Y' k) where
  carrier := {x | ∀ r q, valuation k (x r q) ≤ valuation k (a : k)}
  zero_mem' := fun r q => by simp
  add_mem' := fun ha hb r q => Valuation.map_add_le _ (ha r q) (hb r q)
  neg_mem' := fun ha r q => by simpa using ha r q

theorem box_eq (a : kˣ) :
    (box Y Y' a : Set (Matrix Y Y' k)) = Set.pi Set.univ fun _ : Y => Set.pi Set.univ fun _ : Y' => cball a := by
  ext x
  exact ⟨fun h r _ q _ => h r q, fun h r q => h r trivial q trivial⟩

theorem isCompact_box (a : kˣ) : IsCompact (box Y Y' a : Set (Matrix Y Y' k)) := by
  rw [box_eq]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball a

theorem isOpen_box (a : kˣ) : IsOpen (box Y Y' a : Set (Matrix Y Y' k)) := by
  rw [box_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball a

theorem finite_box (a b : kˣ) : Finite (box Y Y' a ⧸ (box Y Y' b).addSubgroupOf (box Y Y' a)) := by
  haveI : CompactSpace (box Y Y' a) := isCompact_iff_compactSpace.1 (isCompact_box a)
  exact AddSubgroup.quotient_finite_of_isOpen _ ((isOpen_box b).preimage continuous_subtype_val)

theorem exists_box_subset {U : Set (Matrix Y Y' k)} (hU : U ∈ 𝓝 0) : ∃ a : kˣ, ∀ x ∈ box Y Y' a, x ∈ U := by
  have h := (isCompact_box (Y := Y) (Y' := Y') (1 : kˣ)).eventually_forall_of_forall_eventually (x₀ := (0 : k))
    (P := fun c x => c • x ∈ U) fun x _ =>
      (continuous_smul.tendsto' ((0 : k), x) 0 (zero_smul _ _)).eventually hU
  obtain ⟨s, hs⟩ := exists_cball_subset h
  refine ⟨s, fun x hx => ?_⟩
  have := hs (show (s : k) ∈ cball s from le_refl (valuation k (s : k))) ((s : k)⁻¹ • x) fun r q => by
    have h0 : valuation k (s : k) ≠ 0 := by simp
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, Units.val_one, map_one]
    exact inv_mul_le_one_of_le₀ (hx r q) zero_le'
  rwa [smul_inv_smul₀ s.ne_zero] at this

def pairing (ψ : AddChar k Circle) (t b : Matrix Y Y' k) : ℂ := ψ (∑ r, ∑ q, b r q * t r q)

theorem pairing_comm (ψ : AddChar k Circle) (t b : Matrix Y Y' k) : pairing ψ t b = pairing ψ b t := by
  simp only [pairing, mul_comm]

theorem isBichar_pairing (ψ : AddChar k Circle) : IsBichar (pairing (Y := Y) (Y' := Y') ψ) where
  left a b y := by simp [pairing, mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
  right a b y := by simp [pairing, add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
  zero_left y := by simp [pairing]
  zero_right y := by simp [pairing]

theorem pairing_single (ψ : AddChar k Circle) (t : Matrix Y Y' k) (r : Y) (q : Y') (c : k) :
    pairing ψ t (Matrix.single r q c) = ψ (c * t r q) := by
  unfold pairing
  rw [Finset.sum_eq_single r, Finset.sum_eq_single q]
  · simp
  · intro q' _ h; simp [h.symm]
  · simp
  · intro r' _ h; simp [h.symm]
  · simp

theorem pairing_eq_one {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {t b : Matrix Y Y' k}
    (h : ∀ r q, valuation k (b r q * t r q) ≤ valuation k (d : k)) : pairing ψ t b = 1 := by
  rw [pairing, (hd d).2 le_rfl _ (Valuation.map_sum_le _ fun r _ => Valuation.map_sum_le _ fun q _ => h r q)]
  rfl

theorem exists_sep {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) (a : kˣ) {u : Matrix Y Y' k}
    (hu : u ∉ box Y Y' a) : ∃ y ∈ box Y Y' (d / a), pairing ψ u y ≠ 1 := by
  obtain ⟨r, q, h⟩ : ∃ r q, valuation k (a : k) < valuation k (u r q) := by
    by_contra hh
    push Not at hh
    exact hu hh
  have ha : 0 < valuation k (a : k) := zero_lt_iff.2 (by simp)
  have hd0 : 0 < valuation k (d : k) := zero_lt_iff.2 (by simp)
  have hu0 : 0 < valuation k (u r q) := ha.trans h
  have hne : u r q ≠ 0 := fun e => by simp [e] at hu0
  have : ¬ ∀ z : k, valuation k z ≤ valuation k (u r q * (d / a)) → ψ z = 1 := fun hh => by
    have := (hd _).1 hh
    rw [map_mul, map_div₀, mul_div_left_comm, mul_le_iff_le_one_right hd0, div_le_one₀ ha] at this
    exact absurd h (not_lt.2 this)
  push Not at this
  obtain ⟨z, hz, hz1⟩ := this
  refine ⟨Matrix.single r q (z / u r q), fun r' q' => ?_, ?_⟩
  · rw [Matrix.single_apply]
    split_ifs
    · rw [map_div₀, div_le_iff₀ hu0, mul_comm, ← map_mul]
      simpa using hz
    · simp
  · rw [pairing_single, div_mul_cancel₀ _ hne]
    exact fun e => hz1 (Subtype.ext e)

theorem pairing_box {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {a : kˣ} {u y : Matrix Y Y' k}
    (hu : u ∈ box Y Y' a) (hy : y ∈ box Y Y' (d / a)) : pairing ψ u y = 1 :=
  pairing_eq_one hd fun r q => by
    rw [map_mul]
    refine (mul_le_mul' (hy r q) (hu r q)).trans_eq ?_
    rw [← map_mul, ← Units.val_mul, div_mul_cancel]

theorem exists_vacuum {V : Type} [AddCommGroup V] [Module ℂ V] {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (ρ σ : Matrix Y Y' k → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f)
    (hσ : ∀ x x' f, σ x (σ x' f) = σ (x + x') f) (ρ0 : ∀ f, ρ 0 f = f) (σ0 : ∀ f, σ 0 f = f)
    (hc : ∀ x y f, ρ x (σ y f) = pairing ψ x y • σ y (ρ x f)) (P : Submodule ℂ V)
    (hP : ∀ x, ∀ f ∈ P, ρ x f ∈ P) (hP' : ∀ y, ∀ f ∈ P, σ y f ∈ P)
    (sm : ∀ f ∈ P, ∀ᶠ x in 𝓝 0, ρ x f = f) (sm' : ∀ f ∈ P, ∀ᶠ x in 𝓝 0, σ x f = f) {f : V} (hf : f ∈ P) (f0 : f ≠ 0) :
    ∃ g ∈ P, g ≠ 0 ∧ (∀ x ∈ box Y Y' (1 : kˣ), ρ x g = g) ∧
      ∀ y, (∀ x ∈ box Y Y' (1 : kˣ), pairing ψ x y = 1) → σ y g = g := by
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hb := isBichar_pairing (Y := Y) (Y' := Y') ψ
  obtain ⟨a, ha⟩ := exists_box_subset (sm f hf)
  haveI := finite_box (Y := Y) (Y' := Y') 1 a
  obtain ⟨g, hg, g0, hg1⟩ := exists_fixed hb ρ σ hρ
    (fun y f h => by rw [← σ0 f, ← neg_add_cancel y, ← hσ, h, map_zero]) hc (box Y Y' 1) (box Y Y' a)
    (fun u _ hu => let ⟨y, hy, hne⟩ := exists_sep hd a hu; ⟨y, fun κ hκ => pairing_box hd hκ hy, hne⟩)
    P (fun u _ => hP u) hP' hf f0 ha
  obtain ⟨b, hb'⟩ := exists_box_subset (sm' g hg)
  haveI := finite_box (Y := Y) (Y' := Y') (d / 1) b
  let Q : Submodule ℂ V :=
    { carrier := {v | v ∈ P ∧ ∀ x ∈ box Y Y' (1 : kˣ), ρ x v = v}
      zero_mem' := ⟨P.zero_mem, fun _ _ => map_zero _⟩
      add_mem' := fun h h' => ⟨P.add_mem h.1 h'.1, fun x hx => by rw [map_add, h.2 x hx, h'.2 x hx]⟩
      smul_mem' := fun c _ h => ⟨P.smul_mem c h.1, fun x hx => by rw [map_smul, h.2 x hx]⟩ }
  have hb2 : IsBichar fun y x : Matrix Y Y' k => pairing ψ (-x) y :=
    ⟨fun a b y => hb.right _ _ _, fun a y z => by rw [neg_add, hb.left], fun y => hb.zero_right _,
      fun a => by rw [neg_zero, hb.zero_left]⟩
  obtain ⟨g', hg', g0', hg2⟩ := exists_fixed hb2 σ ρ hσ
    (fun y f h => by rw [← ρ0 f, ← neg_add_cancel y, ← hρ, h, map_zero])
    (fun y x f => by rw [hc, smul_smul, hb.neg_mul, one_smul]) (box Y Y' (d / 1)) (box Y Y' b)
    (fun u _ hu => by
      obtain ⟨y, hy, hne⟩ := exists_sep hd b hu
      refine ⟨-y, fun κ hκ => ?_, ?_⟩
      · rw [neg_neg, pairing_comm]
        exact pairing_box hd hκ hy
      · rwa [neg_neg, pairing_comm])
    Q (fun u hu v hv => ⟨hP' u v hv.1, fun x hx => by rw [hc, pairing_box hd hx hu, hv.2 x hx, one_smul]⟩)
    (fun y v hv => ⟨hP y v hv.1, fun x hx => by rw [hρ, add_comm, ← hρ, hv.2 x hx]⟩) ⟨hg, hg1⟩ g0 hb'
  refine ⟨g', hg'.1, g0', hg'.2, fun y hy => hg2 y ?_⟩
  by_contra hn
  obtain ⟨x, hx, hne⟩ := exists_sep hd _ hn
  rw [div_one, div_self'] at hx
  exact hne ((pairing_comm ψ y x).trans (hy x hx))

end GlobalTheory.LocMod.Inhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PadicResidueFieldCardAndPrimeIrreducibleStatement
section
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_residueField_card_and_prime_irreducible : ∀ (T : ℕ) [Fact T.Prime], Nat.card (IsLocalRing.ResidueField 𝒪[ℚ_[T]]) = T ∧ Irreducible ((T : 𝒪[ℚ_[T]])) := by
  first | exact @GlobalTheory.TAdicInt.card_residueField_and_irreducible | exact GlobalTheory.TAdicInt.card_residueField_and_irreducible | (intros; apply GlobalTheory.TAdicInt.card_residueField_and_irreducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducedBasisIntegralConjEntriesBoundedStatement
section
open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedBasis_integral_conj_entries_bounded : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ) (M M' : Matrix (Fin N) (Fin N) ℤ), (∀ i j, |X i j| ≤ R) → (k * diagonal a * n) * M.map (Int.cast : ℤ → ℝ) = X * (k * diagonal a * n) → (k * diagonal a * n) * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * (k * diagonal a * n) → ∀ i j, |(M i j : ℝ)| ≤ C' := by
  first | exact @GlobalTheory.ReducedBasisBound.integral_conj_bounded | exact GlobalTheory.ReducedBasisBound.integral_conj_bounded | (intros; apply GlobalTheory.ReducedBasisBound.integral_conj_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreducStatement
section
open ValuativeRel GlobalTheory.SplitWeil Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_matrix_translation_modulation_irreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ W : Submodule ℂ (Matrix Y Y' k → ℂ), W ≤ SB (Matrix Y Y' k) → (∀ Φ ∈ W, ∀ x : Matrix Y Y' k, (fun t => Φ (t + x)) ∈ SB (Matrix Y Y' k) → (fun t => Φ (t + x)) ∈ W) → (∀ Φ ∈ W, ∀ b : Matrix Y Y' k, (fun t => (ψk (∑ r, ∑ q, b r q * t r q) : ℂ) * Φ t) ∈ SB (Matrix Y Y' k) → (fun t => (ψk (∑ r, ∑ q, b r q * t r q) : ℂ) * Φ t) ∈ W) → ∀ Φ₀ ∈ W, Φ₀ ≠ 0 → W = SB (Matrix Y Y' k) := by
  first | exact @GlobalTheory.IrredSB.sb_irreducible | exact GlobalTheory.IrredSB.sb_irreducible | (intros; apply GlobalTheory.IrredSB.sb_irreducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelReducedIntegralFormBoundedEntries
section
open Matrix GlobalTheory.ClassFin

namespace GlobalTheory.RedBound

lemma entry_bound {N : ℕ} (P Z Q : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (c : ℝ)
    (h : ∀ p q, |P i p * Z p q * Q q j| ≤ c) : |(P * Z * Q) i j| ≤ N * N * c := by
  have e : (P * Z * Q) i j = ∑ q, ∑ p, P i p * Z p q * Q q j := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [e]
  calc |∑ q, ∑ p, P i p * Z p q * Q q j| ≤ ∑ q, |∑ p, P i p * Z p q * Q q j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q : Fin N, ∑ _p : Fin N, c := by
        refine Finset.sum_le_sum fun q _ => ?_
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => h p q)
    _ = N * N * c := by simp [Finset.sum_const, Finset.card_fin]; ring

lemma orth_entry_le {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (h : kᵀ * k = 1) (p q : Fin N) :
    |k p q| ≤ 1 := by
  have h1 : ∑ r, k r q * k r q = 1 := by
    have := congrFun (congrFun h q) q
    simpa [Matrix.mul_apply] using this
  have h2 : k p q * k p q ≤ ∑ r, k r q * k r q :=
    Finset.single_le_sum (f := fun r => k r q * k r q) (fun r _ => mul_self_nonneg _)
      (Finset.mem_univ p)
  rw [h1] at h2
  have h3 : |k p q| ^ 2 ≤ 1 := by rw [sq_abs, sq]; exact h2
  nlinarith [abs_nonneg (k p q)]

lemma le_of_le_idx {N : ℕ} {C Cm : ℝ} {k : Matrix (Fin N) (Fin N) ℝ} {a : Fin N → ℝ}
    {n : Matrix (Fin N) (Fin N) ℝ} (hS : IsSiegel C k a n) (h1 : 1 ≤ Cm) (hC : C ≤ Cm)
    {i p : Fin N} (h : i ≤ p) : a i ≤ Cm * a p := by
  rcases h.lt_or_eq with h | h
  · exact (hS.le i p h).trans (mul_le_mul_of_nonneg_right hC (hS.pos p).le)
  · subst h; exact le_mul_of_one_le_left (hS.pos i).le h1

lemma prod_le {N : ℕ} {C Cm : ℝ} {k : Matrix (Fin N) (Fin N) ℝ} {a : Fin N → ℝ}
    {n : Matrix (Fin N) (Fin N) ℝ} (hS : IsSiegel C k a n) (h1 : 1 ≤ Cm) (hC : C ≤ Cm)
    {p q r s : Fin N} (hr : p ≤ r) (hs : q ≤ s) : a p * a q ≤ Cm ^ 2 * (a r * a s) := by
  have har := le_of_le_idx hS h1 hC hr
  have has := le_of_le_idx hS h1 hC hs
  have h0 : 0 ≤ Cm * a r := mul_nonneg (by linarith) (hS.pos r).le
  calc a p * a q ≤ (Cm * a r) * (Cm * a s) := mul_le_mul har has (hS.pos q).le h0
    _ = Cm ^ 2 * (a r * a s) := by ring

end GlobalTheory.RedBound

namespace GlobalTheory.RedBound

theorem reduced_bound : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ)
    (B B' : Matrix (Fin N) (Fin N) ℤ) (μ : ℝ), μ ≠ 0 → |μ| ≤ R → (∀ i j, |X i j| ≤ R) →
    B.map (Int.cast : ℤ → ℝ) = (k * diagonal a * n)ᵀ * X * (k * diagonal a * n) →
    (k * diagonal a * n) * B'.map (Int.cast : ℤ → ℝ) * (k * diagonal a * n)ᵀ = μ • X →
    ∀ i j, |(B i j : ℝ)| ≤ C' := by
  intro N C R
  obtain ⟨M, hM⟩ := GlobalTheory.T.unipotent_upper_inv_upperTriangular_bounded N C
  obtain ⟨Cm, hCm1, hCC⟩ : ∃ Cm : ℝ, 1 ≤ Cm ∧ C ≤ Cm := ⟨max C 1, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨M₀, hM₀, hMM⟩ : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ M ≤ M₀ := ⟨max M 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨R₀, hR₀, hRR⟩ : ∃ R₀ : ℝ, 0 ≤ R₀ ∧ R ≤ R₀ := ⟨max R 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = N * N * (1 * R₀ * 1) := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = M₀ * (Cm ^ 2 * (R₀ * R')) * M₀ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = N * N * K₁ + 1 := ⟨_, rfl⟩
  have hCm0 : 0 < Cm := lt_of_lt_of_le one_pos hCm1
  have hR'0 : 0 ≤ R' := by rw [hR']; positivity
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hT0 : 0 < T := by rw [hT]; positivity
  refine ⟨N * N * (Cm * (Cm ^ 2 * T * R') * Cm), ?_⟩
  intro k a n hS X B B' μ hμ hμR hX hB hB' i j
  obtain ⟨m, hmn, _hnm, hmlow, hmb⟩ := hM n hS.diag hS.lower hS.bdd
  have hmb' : ∀ p q, |m p q| ≤ M₀ := fun p q => (hmb p q).trans hMM
  have hnb : ∀ p q, |n p q| ≤ Cm := fun p q => (hS.bdd p q).trans hCC
  have hμ₀ : |μ| ≤ R₀ := hμR.trans hRR
  have hk : ∀ p q, |k p q| ≤ 1 := orth_entry_le k hS.orth
  obtain ⟨X', hX'def⟩ : ∃ X', X' = kᵀ * X * k := ⟨_, rfl⟩
  have hX' : ∀ p q, |X' p q| ≤ R' := by
    intro p q
    rw [hX'def, hR']
    apply entry_bound
    intro r s
    rw [abs_mul, abs_mul, Matrix.transpose_apply]
    exact mul_le_mul (mul_le_mul (hk r p) ((hX r s).trans hRR) (abs_nonneg _) zero_le_one)
      (hk s q) (abs_nonneg _) (by positivity)
  obtain ⟨Br', hBr'⟩ : ∃ Br', Br' = B'.map (Int.cast : ℤ → ℝ) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = n * Br' * nᵀ := ⟨_, rfl⟩
  have hWeq : diagonal a * W * diagonal a = μ • X' := by
    have h1 : kᵀ * ((k * diagonal a * n) * Br' * (k * diagonal a * n)ᵀ) * k = μ • X' := by
      rw [hBr', hB', hX'def, Matrix.mul_smul, Matrix.smul_mul]
    rw [← h1, hWdef]
    have h2 : kᵀ * ((k * diagonal a * n) * Br' * (k * diagonal a * n)ᵀ) * k =
        (kᵀ * k) * (diagonal a * (n * Br' * nᵀ) * diagonal a) * (kᵀ * k) := by
      simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [h2, hS.orth, Matrix.one_mul, Matrix.mul_one]
  have hWent : ∀ p q, a p * W p q * a q = μ * X' p q := by
    intro p q
    have := congrFun (congrFun hWeq p) q
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have hBm : Br' = m * W * mᵀ := by
    rw [hWdef]
    calc Br' = (m * n) * Br' * (m * n)ᵀ := by rw [hmn]; simp
      _ = m * (n * Br' * nᵀ) * mᵀ := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hZ : B.map (Int.cast : ℤ → ℝ) = nᵀ * (diagonal a * X' * diagonal a) * n := by
    rw [hB, hX'def]
    simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hA : ∀ p q, T ≤ a p * a q → B' p q = 0 := by
    intro p q hpq
    have hpos : 0 < a p * a q := mul_pos (hS.pos p) (hS.pos q)
    have hb : |Br' p q| ≤ N * N * (K₁ / (a p * a q)) := by
      rw [hBm]
      apply entry_bound
      intro r s
      rw [le_div_iff₀ hpos, Matrix.transpose_apply]
      by_cases hr : r < p
      · rw [hmlow p r hr]; simp; positivity
      by_cases hs : s < q
      · rw [hmlow q s hs]; simp; positivity
      push_neg at hr hs
      have hWb : |W r s| * (a r * a s) ≤ R₀ * R' := by
        calc |W r s| * (a r * a s) = |a r * W r s * a s| := by
              rw [abs_mul, abs_mul, abs_of_pos (hS.pos r), abs_of_pos (hS.pos s)]; ring
          _ = |μ| * |X' r s| := by rw [hWent r s, abs_mul]
          _ ≤ R₀ * R' := mul_le_mul hμ₀ (hX' r s) (abs_nonneg _) hR₀
      have hapq := prod_le hS hCm1 hCC hr hs
      rw [abs_mul, abs_mul, hK₁]
      calc |m p r| * |W r s| * |m q s| * (a p * a q)
          ≤ |m p r| * |W r s| * |m q s| * (Cm ^ 2 * (a r * a s)) :=
            mul_le_mul_of_nonneg_left hapq (by positivity)
        _ = |m p r| * (Cm ^ 2 * (|W r s| * (a r * a s))) * |m q s| := by ring
        _ ≤ M₀ * (Cm ^ 2 * (R₀ * R')) * M₀ :=
            mul_le_mul (mul_le_mul (hmb' p r) (mul_le_mul_of_nonneg_left hWb (by positivity))
              (mul_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _) (mul_pos (hS.pos r) (hS.pos s)).le)) hM₀) (hmb' q s) (abs_nonneg _) (by positivity)
    have hlt : |Br' p q| < 1 := by
      have e : (N : ℝ) * N * (K₁ / (a p * a q)) = (N * N * K₁) / (a p * a q) := by ring
      rw [e] at hb
      exact hb.trans_lt ((div_lt_one hpos).mpr (by linarith))
    have h3 : |((B' p q : ℤ) : ℝ)| < 1 := by rw [hBr'] at hlt; simpa using hlt
    have h4 : |B' p q| < 1 := by exact_mod_cast h3
    exact Int.abs_lt_one_iff.mp h4
  have hBz : ∀ p q, Cm ^ 2 * T ≤ a p * a q → W p q = 0 := by
    intro p q h
    rw [hWdef]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_eq_zero
    intro s _
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r < p
    · rw [hS.lower p r hr]; ring
    by_cases hs : s < q
    · rw [hS.lower q s hs]; ring
    push_neg at hr hs
    have hapq := prod_le hS hCm1 hCC hr hs
    have hT' : T ≤ a r * a s := by
      have : Cm ^ 2 * T ≤ Cm ^ 2 * (a r * a s) := h.trans hapq
      exact le_of_mul_le_mul_left this (by positivity)
    have h0 := hA r s hT'
    simp [hBr', h0]
  have hZb : ∀ p q, |a p * X' p q * a q| ≤ Cm ^ 2 * T * R' := by
    intro p q
    by_cases h : Cm ^ 2 * T ≤ a p * a q
    · have e := hWent p q
      rw [hBz p q h] at e
      have h0 : μ * X' p q = 0 := by rw [← e]; ring
      have hx : X' p q = 0 := (mul_eq_zero.mp h0).resolve_left hμ
      rw [hx]; simp; positivity
    · push_neg at h
      calc |a p * X' p q * a q| = (a p * a q) * |X' p q| := by
            rw [abs_mul, abs_mul, abs_of_pos (hS.pos p), abs_of_pos (hS.pos q)]; ring
        _ ≤ (Cm ^ 2 * T) * R' := mul_le_mul h.le (hX' p q) (abs_nonneg _) (by positivity)
  have hBe : (B i j : ℝ) = (nᵀ * (diagonal a * X' * diagonal a) * n) i j := by
    rw [← hZ]; simp
  rw [hBe]
  apply entry_bound
  intro r s
  have hZe : (diagonal a * X' * diagonal a) r s = a r * X' r s * a s := by
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Matrix.transpose_apply, hZe, abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hnb r i) (hZb r s) (abs_nonneg _) hCm0.le) (hnb s j)
    (abs_nonneg _) (by positivity)

end GlobalTheory.RedBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothOfLimitClassStableUnderDirectionalDerivsStatement
section
open scoped ContDiff Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_of_limit_class_stable_under_directional_derivs : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by
  first | exact @GlobalTheory.contDiff_of_class_tendstoLocallyUniformly | exact GlobalTheory.contDiff_of_class_tendstoLocallyUniformly | (intros; apply GlobalTheory.contDiff_of_class_tendstoLocallyUniformly <;> assumption)
end

