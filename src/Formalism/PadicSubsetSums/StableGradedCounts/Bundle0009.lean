import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral
import Mathlib

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.TWIndexAdditive
section
open Module

namespace Formalism.IrreducibleCountingLemmas.TW

namespace Idx

section General

variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]

theorem relLen_of_le {M N : Submodule O V} (h : M ≤ N) : relLen M N = 0 := by
  unfold relLen
  have : N.comap M.subtype = ⊤ := by
    rw [eq_top_iff]; intro x _; exact h x.2
  rw [this]
  exact Module.length_eq_zero

theorem relLen_inf (M N : Submodule O V) : relLen M (M ⊓ N) = relLen M N := by
  unfold relLen
  have : (M ⊓ N).comap M.subtype = N.comap M.subtype := by
    ext x; simp
  rw [this]

theorem relLen_tower {A B C : Submodule O V} (hAB : A ≤ B) (hBC : B ≤ C) :
    relLen C A = relLen B A + relLen C B := by
  unfold relLen
  have h1 : A.comap B.subtype ≤ (A.comap C.subtype).comap (Submodule.inclusion hBC) := by
    intro x hx; exact hx
  have h2 : A.comap C.subtype ≤ B.comap C.subtype := Submodule.comap_mono hAB
  refine Module.length_eq_add_of_exact (Submodule.mapQ _ _ (Submodule.inclusion hBC) h1)
    (Submodule.factor h2) ?_ (Submodule.factor_surjective h2) ?_
  · rw [injective_iff_map_eq_zero]
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    intro hx
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hfac : Submodule.factor h2 (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := rfl
    rw [hfac, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hy
      exact ⟨Submodule.Quotient.mk ⟨y.1, hy⟩, by rw [Submodule.mapQ_apply]; rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hx
      have h3 : (x : V) - y ∈ A := hx
      have h4 : (y : V) = x - (x - y) := by abel
      show (y : V) ∈ B
      rw [h4]
      exact B.sub_mem x.2 (hAB h3)

end General

section LenDet

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]

theorem ord_prod {ι : Type} (s : Finset ι) (a : ι → O) (ha : ∀ i, a i ≠ 0) :
    Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha i)), ih]

theorem length_quot_range {B ι : Type} [AddCommGroup B] [Module O B] [Fintype ι]
    (b : Basis ι O B) (f : B →ₗ[O] B) (hf : Function.Injective f) :
    Module.length O (B ⧸ LinearMap.range f) = Ring.ord O (LinearMap.det f) := by
  classical
  have h : finrank O (LinearMap.range f) = finrank O B :=
    (LinearEquiv.ofInjective f hf).finrank_eq.symm
  rw [(Submodule.quotientEquivPiSpan _ b h).length_eq, Module.length_pi_of_fintype]
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  have hne := Submodule.smithNormalFormCoeffs_ne_zero b h
  generalize Submodule.smithNormalFormCoeffs b h = a at *
  generalize Submodule.smithNormalFormTopBasis b h = b' at *
  generalize Submodule.smithNormalFormBotBasis b h = ab at *
  let e' : B ≃ₗ[O] LinearMap.range f := b'.equiv ab (Equiv.refl _)
  have hass : Associated (LinearMap.det f)
      (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (e' : B →ₗ[O] LinearMap.range f))) := by
    have := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
      (LinearEquiv.ofInjective f hf) e'
    convert this using 2
    ext x; rfl
  have hg : LinearMap.det ((LinearMap.range f).subtype ∘ₗ (e' : B →ₗ[O] LinearMap.range f))
      = ∏ i, a i := by
    have : (LinearMap.range f).subtype ∘ₗ (e' : B →ₗ[O] LinearMap.range f)
        = Matrix.toLin b' b' (Matrix.diagonal a) := by
      apply b'.ext; intro i
      simp [e', ab_eq, Matrix.toLin_self, Matrix.diagonal_apply]
    rw [this, LinearMap.det_toLin, Matrix.det_diagonal]
  rw [Ring.ord_eq_of_associated hass, hg, ord_prod _ _ hne]
  rfl

end LenDet

section Lat

variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]

theorem isLattice_of_isLat {M : Submodule O V} (h : IsLat O K M) : Submodule.IsLattice K M :=
  ⟨h.1, h.2⟩

theorem isLat_of_isLattice (M : Submodule O V) [Submodule.IsLattice K M] : IsLat O K M :=
  ⟨Submodule.IsLattice.fg, Submodule.IsLattice.span_eq_top⟩

theorem ord_unit_mul_pow {ϖ : O} (hϖ : Irreducible ϖ) (u : Oˣ) (n : ℕ) :
    Ring.ord O ((u : O) * ϖ ^ n) = n := by
  rw [Ring.ord_mul_of_isUnit_left u.isUnit,
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), Ring.ord_of_irreducible hϖ]
  simp

theorem exists_basis {M : Submodule O V} (h : IsLat O K M) :
    ∃ (n : ℕ) (β : Basis (Fin n) K V), Submodule.span O (Set.range β) = M := by
  have := isLattice_of_isLat h
  have : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O K V
  obtain ⟨n, c⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := M)
  refine ⟨n, c.extendOfIsLattice K, ?_⟩
  have : Set.range (c.extendOfIsLattice K) = M.subtype '' Set.range c := by
    rw [← Set.range_comp]; congr 1; ext i; simp
  rw [this, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem isLat_span_basis {d : ℕ} (b : Basis (Fin d) K V) :
    IsLat O K (Submodule.span O (Set.range b)) := by
  refine ⟨Submodule.fg_span (Set.finite_range b), ?_⟩
  rw [Submodule.span_span_of_tower, b.span_eq]

theorem relLen_span_of_le {d : ℕ} (b : Basis (Fin d) K V) (w : Fin d → V)
    (hw : Submodule.span O (Set.range w) ≤ Submodule.span O (Set.range b))
    (hdet : b.det w ≠ 0) :
    ∃ D : O, algebraMap O K D = b.det w ∧
      relLen (Submodule.span O (Set.range b)) (Submodule.span O (Set.range w)) = Ring.ord O D := by
  let bO := b.restrictScalars O
  let w' : Fin d → Submodule.span O (Set.range b) :=
    fun i => ⟨w i, hw (Submodule.subset_span ⟨i, rfl⟩)⟩
  let f : Submodule.span O (Set.range b) →ₗ[O] Submodule.span O (Set.range b) := bO.constr O w'
  have hD : algebraMap O K (LinearMap.det f) = b.det w := by
    rw [← LinearMap.det_toMatrix bO, RingHom.map_det, Basis.det_apply]
    congr 1
    ext i j
    simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply, f, w', bO]
  have hne : LinearMap.det f ≠ 0 := by
    intro h; rw [h, map_zero] at hD; exact hdet hD.symm
  have hinj : Function.Injective f := by
    intro x y hxy
    have hM : (LinearMap.toMatrix bO bO f).det ≠ 0 := by rwa [LinearMap.det_toMatrix]
    have := Matrix.mulVec_injective_of_det_ne_zero hM (a₁ := bO.repr x) (a₂ := bO.repr y)
      (by rw [LinearMap.toMatrix_mulVec_repr, LinearMap.toMatrix_mulVec_repr, hxy])
    exact bO.repr.injective (DFunLike.coe_injective this)
  have hrange : (Submodule.span O (Set.range w)).comap (Submodule.span O (Set.range b)).subtype
      = LinearMap.range f := by
    rw [Basis.constr_range]
    apply Submodule.map_injective_of_injective (Submodule.span O (Set.range b)).injective_subtype
    rw [Submodule.map_comap_subtype, Submodule.map_span, ← Set.range_comp, inf_eq_right.2 hw]
    rfl
  refine ⟨_, hD, ?_⟩
  unfold relLen
  rw [hrange]
  exact length_quot_range bO f hinj

theorem ord_ne_top' {D : O} (hD : D ≠ 0) : Ring.ord O D ≠ ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hD hϖ
  rw [ord_unit_mul_pow hϖ]
  exact ENat.natCast_ne_top n

theorem relLen_ne_top_of_le {M N : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N)
    (hle : N ≤ M) : relLen M N ≠ ⊤ := by
  obtain ⟨n, β, rfl⟩ := exists_basis hM
  obtain ⟨n', γ, rfl⟩ := exists_basis hN
  have hn : n' = n := by
    have h1 := Module.finrank_eq_card_basis β
    have h2 := Module.finrank_eq_card_basis γ
    simpa using h2.symm.trans h1
  subst hn
  obtain ⟨D, hD, hlen⟩ := relLen_span_of_le (O := O) β γ hle (β.isUnit_det γ).ne_zero
  rw [hlen]
  apply ord_ne_top'
  rintro rfl
  rw [map_zero] at hD
  exact (β.isUnit_det γ).ne_zero hD.symm

variable [FiniteDimensional K V]

theorem isLat_inf {M N : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N) :
    IsLat O K (M ⊓ N) := by
  have := isLattice_of_isLat hM
  have := isLattice_of_isLat hN
  exact isLat_of_isLattice _

theorem relLen_ne_top {M N : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N) :
    relLen M N ≠ ⊤ := by
  rw [← relLen_inf]
  exact relLen_ne_top_of_le hM (isLat_inf hM hN) inf_le_left

theorem sIdx_eq_sub {M N Q : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N)
    (hQ : IsLat O K Q) (hQM : Q ≤ M) (hQN : Q ≤ N) :
    sIdx M N = ((relLen M Q).toNat : ℤ) - ((relLen N Q).toNat : ℤ) := by
  have h1 := relLen_tower (le_inf hQM hQN) (inf_le_left : M ⊓ N ≤ M)
  have h2 := relLen_tower (le_inf hQM hQN) (inf_le_right : M ⊓ N ≤ N)
  rw [relLen_inf] at h1
  rw [inf_comm, relLen_inf] at h2
  have f0 := relLen_ne_top (isLat_inf hN hM) hQ
  have f1 := relLen_ne_top hM hN
  have f2 := relLen_ne_top hN hM
  rw [inf_comm] at h1
  unfold sIdx
  rw [h1, h2, ENat.toNat_add f0 f1, ENat.toNat_add f0 f2]
  push_cast
  ring

end Lat

end Idx

theorem index_additive : IndexAdditive := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ M N P hM hN hP
  refine ⟨Idx.relLen_ne_top hM hN, ?_⟩
  have hQ := Idx.isLat_inf (Idx.isLat_inf hM hN) hP
  have q1 : M ⊓ N ⊓ P ≤ M := inf_le_left.trans inf_le_left
  have q2 : M ⊓ N ⊓ P ≤ N := inf_le_left.trans inf_le_right
  have q3 : M ⊓ N ⊓ P ≤ P := inf_le_right
  rw [Idx.sIdx_eq_sub hM hN hQ q1 q2, Idx.sIdx_eq_sub hN hP hQ q2 q3, Idx.sIdx_eq_sub hM hP hQ q1 q3]
  ring

end Formalism.IrreducibleCountingLemmas.TW
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.TWUnitBallLattice
section
open Module

namespace Formalism.IrreducibleCountingLemmas.TW

namespace UnitBall

variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]

noncomputable abbrev ballRing (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] :
    ValuationSubring K :=
  (NormedField.valuation (K := K)).valuationSubring

lemma mem_ballRing (x : K) : x ∈ ballRing K ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
  exact_mod_cast Iff.rfl

lemma norm_unif_pos (ϖ : K) (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n) : 0 < ‖ϖ‖ := by
  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
    linarith
  obtain ⟨n, hn⟩ := hd x hx0
  by_contra h
  have h0 : ‖ϖ‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
  rw [h0] at hn
  rcases eq_or_ne n 0 with rfl | hn0
  · simp at hn; linarith
  · rw [zero_zpow _ hn0] at hn; linarith

lemma exists_nat_pow (ϖ : K) (h1 : ‖ϖ‖ < 1) (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n)
    (x : K) (hx0 : x ≠ 0) (hx : ‖x‖ ≤ 1) : ∃ n : ℕ, ‖x‖ = ‖ϖ‖ ^ n := by
  have h0 := norm_unif_pos ϖ hd
  obtain ⟨n, hn⟩ := hd x hx0
  have hn0 : 0 ≤ n := by
    by_contra h
    have := one_lt_zpow_of_neg₀ h0 h1 (not_le.mp h)
    linarith
  refine ⟨n.toNat, ?_⟩
  rw [hn, ← zpow_natCast, Int.toNat_of_nonneg hn0]

lemma ballRing_pid (ϖ : K) (h1 : ‖ϖ‖ < 1) (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n) :
    IsPrincipalIdealRing (ballRing K) := by
  classical
  have h0 := norm_unif_pos ϖ hd
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · subst hI; exact bot_isPrincipal
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hex : ∃ n : ℕ, ∃ x ∈ I, ‖(x : K)‖ = ‖ϖ‖ ^ n := by
    obtain ⟨n, hn⟩ := exists_nat_pow ϖ h1 hd (y : K) (by simpa using hy0) ((mem_ballRing _).mp y.2)
    exact ⟨n, y, hyI, hn⟩
  obtain ⟨x0, hx0I, hx0⟩ := Nat.find_spec hex
  have hx00 : (x0 : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx0
    exact absurd hx0 (pow_pos h0 _).ne
  refine ⟨⟨x0, le_antisymm ?_ ?_⟩⟩
  · intro z hz
    rw [Submodule.mem_span_singleton]
    by_cases hz0 : z = 0
    · exact ⟨0, by simp [hz0]⟩
    obtain ⟨m, hm⟩ := exists_nat_pow ϖ h1 hd (z : K) (by simpa using hz0) ((mem_ballRing _).mp z.2)
    have hle : Nat.find hex ≤ m := Nat.find_min' hex ⟨z, hz, hm⟩
    have hq : (z : K) / x0 ∈ ballRing K := by
      rw [mem_ballRing, norm_div, hm, hx0, div_le_one (pow_pos h0 _)]
      exact pow_le_pow_of_le_one h0.le h1.le hle
    refine ⟨⟨_, hq⟩, ?_⟩
    apply Subtype.ext
    simp [div_mul_cancel₀ _ hx00]
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hx0I

end UnitBall

open UnitBall in

theorem unit_ball_is_lattice : UnitBallLattice := by
  intro K V _ _ _ _ _ _ _ ϖ h1 hd
  classical
  have h0 := norm_unif_pos ϖ hd
  have := ballRing_pid ϖ h1 hd
  let A := ballRing K
  let M : Submodule A V :=
    { carrier := {v | ‖v‖ ≤ 1}
      add_mem' := fun {a b} ha hb =>
        (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := fun c v hv => by
        show ‖(c : K) • v‖ ≤ 1
        rw [norm_smul]
        exact mul_le_one₀ ((mem_ballRing _).mp c.2) (norm_nonneg _) hv }
  have hM : ∀ v : V, v ∈ M ↔ ‖v‖ ≤ 1 := fun v => Iff.rfl

  have hfg : M.FG := by
    let e := Module.finBasis K V
    let f : Fin (finrank K V) → (V →L[K] K) := fun i => LinearMap.toContinuousLinearMap (e.coord i)
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (∑ i, ‖f i‖)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hc
      exact absurd hc (not_lt.mpr (Finset.sum_nonneg fun i _ => norm_nonneg _))
    refine Submodule.FG.of_le (T := Submodule.span A (Set.range fun i => c • e i))
      (Submodule.fg_span (Set.finite_range _)) ?_
    intro v hv
    have hcoef : ∀ i, e.repr v i / c ∈ A := by
      intro i
      rw [mem_ballRing, norm_div, div_le_one (norm_pos_iff.mpr hc0)]
      have h2 : ‖f i v‖ ≤ ‖f i‖ * ‖v‖ := (f i).le_opNorm v
      have h3 : ‖f i‖ * ‖v‖ ≤ ‖f i‖ := mul_le_of_le_one_right (norm_nonneg _) hv
      have h4 : ‖f i‖ ≤ ∑ j, ‖f j‖ :=
        Finset.single_le_sum (f := fun j => ‖f j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      have h5 : f i v = e.repr v i := rfl
      rw [← h5]
      linarith
    have hv' : v = ∑ i, (⟨_, hcoef i⟩ : A) • (c • e i) := by
      conv_lhs => rw [← e.sum_repr v]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = (e.repr v i / c) • (c • e i)
      rw [smul_smul, div_mul_cancel₀ _ hc0]
    rw [hv']
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span K (M : Set V) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K ‖v‖
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hc
      exact absurd hc (not_lt.mpr (norm_nonneg _))
    have hmem : c⁻¹ • v ∈ M := by
      rw [hM, norm_smul, norm_inv, inv_mul_le_one₀ (norm_pos_iff.mpr hc0)]
      exact hc.le
    have : v = c • (c⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have : Submodule.IsLattice K M := ⟨hfg, hspan⟩
  let b0 := Module.Free.chooseBasis A M
  let b1 := b0.extendOfIsLattice K
  have hb1 : ∀ j, b1 j = (b0 j : V) := fun j => Module.Basis.extendOfIsLattice_apply K b0 j
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A M) = finrank K V :=
    (Module.finrank_eq_card_basis b1).symm
  let eq := Fintype.equivFinOfCardEq hcard
  refine ⟨b1.reindex eq, fun v => ?_⟩
  simp only [Module.Basis.repr_reindex_apply]
  rw [eq.symm.forall_congr_right (q := fun j => ‖b1.repr v j‖ ≤ 1)]
  constructor
  · intro hv j
    let w : M := ⟨v, hv⟩
    have hsum : v = ∑ j, ((b0.repr w j : A) : K) • b1 j := by
      have h := congrArg (Subtype.val) (b0.sum_repr w)
      rw [Submodule.coe_sum] at h
      rw [← show (w : V) = v from rfl, ← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hb1]
      rfl
    have hr : b1.repr v j = ((b0.repr w j : A) : K) := by
      conv_lhs => rw [hsum]
      rw [b1.repr_sum_self]
    rw [hr]
    exact (mem_ballRing _).mp (b0.repr w j).2
  · intro h
    rw [← hM, ← b1.sum_repr v]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [hb1]
    exact M.smul_mem (⟨_, (mem_ballRing _).mpr (h j)⟩ : A) (b0 j).2

end Formalism.IrreducibleCountingLemmas.TW
end

