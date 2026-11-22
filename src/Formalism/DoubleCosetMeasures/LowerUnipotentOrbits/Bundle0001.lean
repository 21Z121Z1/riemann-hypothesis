import Formalism.DoubleCosetMeasures.Statement

-- bundled from Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.DoubleCosetEqPreimage
section
noncomputable section

open MeasureTheory

namespace Formalism.DoubleCosetMeasures.P

section Generic

variable {X : Type}

def cls (r : Setoid X) (q : Quotient r) : Set X := Quotient.mk r ⁻¹' {q}

theorem mem_cls {r : Setoid X} {q : Quotient r} {y : X} :
    y ∈ cls r q ↔ Quotient.mk r y = q := Iff.rfl

variable [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem support_out_finite (r : Setoid X) (hr : ∀ q, IsOpen (cls r q)) (f : X → E)
    (hc : HasCompactSupport f) :
    (Function.support (fun q : Quotient r => f q.out)).Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (cls r) hr (by
    intro x _; exact Set.mem_iUnion.2 ⟨Quotient.mk r x, rfl⟩)
  refine t.finite_toSet.subset ?_
  intro q hq
  obtain ⟨q', hq', hm⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport f hq))
  have hqq : q = q' := (Quotient.out_eq q).symm.trans hm
  exact hqq ▸ hq'

theorem eq_sum_indicator (r : Setoid X) (f : X → E)
    (hf : ∀ x y, Quotient.mk r x = Quotient.mk r y → f x = f y)
    (t : Finset (Quotient r)) (ht : Function.support (fun q : Quotient r => f q.out) ⊆ t) :
    f = fun x => ∑ q ∈ t, (cls r q).indicator (fun _ => f q.out) x := by
  classical
  funext x
  have hx : f x = f (Quotient.mk r x).out := hf _ _ (Quotient.out_eq _).symm
  simp only [Set.indicator_apply, mem_cls]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact hx
  · rw [hx]
    by_contra hne
    exact h (ht hne)

theorem integral_eq_finsum (r : Setoid X) (hr : ∀ q, IsOpen (cls r q)) (μ : Measure X)
    (f : X → E) (hf : ∀ x y, Quotient.mk r x = Quotient.mk r y → f x = f y)
    (hc : HasCompactSupport f)
    (hμ : (∀ q, μ (cls r q) < ⊤) ∨ (∀ q, μ (cls r q) = ⊤)) :
    ∫ x, f x ∂μ = ∑ᶠ q : Quotient r, (μ (cls r q)).toReal • f q.out := by
  classical
  have hfin := support_out_finite r hr f hc
  have ht : Function.support (fun q : Quotient r => f q.out) ⊆ (hfin.toFinset : Set _) := by
    simp
  have hsupp : Function.support (fun q : Quotient r => (μ (cls r q)).toReal • f q.out) ⊆
      (hfin.toFinset : Set _) := fun q hq => ht (fun h => hq (by simp [h]))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rcases hμ with hμ | hμ
  · conv_lhs => rw [eq_sum_indicator r f hf hfin.toFinset ht]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ ((hr q).measurableSet)]
      rfl
    · intro q _
      exact (integrable_indicator_iff (hr q).measurableSet).2 (integrableOn_const (hμ q).ne)
  · have h0 : ∀ q, (μ (cls r q)).toReal • f q.out = 0 := fun q => by simp [hμ q]
    simp only [h0, Finset.sum_const_zero]
    by_cases hz : ∀ q : Quotient r, f q.out = 0
    · have : f = 0 := funext fun x => (hf _ _ (Quotient.out_eq _).symm).trans (hz _)
      simp [this]
    · push Not at hz
      obtain ⟨q, hq⟩ := hz
      apply integral_undef
      intro hint
      have hlt := hint.measure_norm_ge_lt_top (ε := ‖f q.out‖) (norm_pos_iff.2 hq)
      have hsub : cls r q ⊆ {x | ‖f q.out‖ ≤ ‖f x‖} := fun x hx => by
        show ‖f q.out‖ ≤ ‖f x‖
        rw [hf x q.out (hx.trans (Quotient.out_eq q).symm)]
      exact absurd (hμ q) ((measure_mono hsub).trans_lt hlt).ne

end Generic

section Left

variable {G : Type} [Group G]

theorem cls_leftRel (K₀ : Subgroup G) (q : G ⧸ K₀) :
    cls (QuotientGroup.leftRel K₀) q = (fun z => q.out⁻¹ * z) ⁻¹' (K₀ : Set G) := by
  ext y
  simp only [Set.mem_preimage, SetLike.mem_coe]
  rw [mem_cls]
  constructor
  · intro h
    have h' : (y : G ⧸ K₀) = ((q.out : G) : G ⧸ K₀) := h.trans (Quotient.out_eq q).symm
    rw [QuotientGroup.eq] at h'
    simpa using K₀.inv_mem h'
  · intro h
    have h' : ((q.out : G) : G ⧸ K₀) = (y : G ⧸ K₀) := by
      rw [QuotientGroup.eq]; exact h
    exact h'.symm.trans (Quotient.out_eq q)

end Left

theorem intRightInv : Formalism.DoubleCosetMeasures.IntRightInv := by
  intro G _ _ _ _ _ μ _ K₀ hK E _ _ _ f hf hc
  have hr : ∀ q, IsOpen (cls (QuotientGroup.leftRel K₀) q) := fun q => by
    rw [cls_leftRel]; exact hK.preimage (continuous_const.mul continuous_id)
  have hμq : ∀ q : G ⧸ K₀, μ (cls (QuotientGroup.leftRel K₀) q) = μ (K₀ : Set G) := fun q => by
    rw [cls_leftRel, measure_preimage_mul]
  have hf' : ∀ x y : G, Quotient.mk (QuotientGroup.leftRel K₀) x =
      Quotient.mk (QuotientGroup.leftRel K₀) y → f x = f y := by
    intro x y h
    have h' : (x : G ⧸ K₀) = (y : G ⧸ K₀) := h
    rw [QuotientGroup.eq] at h'
    have := hf x _ h'
    rw [mul_inv_cancel_left] at this
    exact this.symm
  refine ⟨support_out_finite _ hr f hc, ?_⟩
  rw [integral_eq_finsum _ hr μ f hf' hc]
  · exact finsum_congr fun q => by rw [hμq]
  · by_cases h : μ (K₀ : Set G) < ⊤
    · exact Or.inl fun q => (hμq q).symm ▸ h
    · exact Or.inr fun q => (hμq q).trans (not_lt_top_iff.1 h)

section Doset

variable {G : Type} [Group G]

def dcMap (K₀ : Subgroup G) (g : G) (k : K₀) : G ⧸ K₀ := ((k : G) * g : G)

theorem doubleCoset_eq_preimage (K₀ : Subgroup G) (g : G) :
    DoubleCoset.doubleCoset g (K₀ : Set G) K₀ =
      (QuotientGroup.mk : G → G ⧸ K₀) ⁻¹' Set.range (dcMap K₀ g) := by
  ext y
  rw [DoubleCoset.mem_doubleCoset]
  simp only [Set.mem_preimage, Set.mem_range, dcMap, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hb
  · rintro ⟨k, hk⟩
    rw [QuotientGroup.eq] at hk
    exact ⟨k, k.2, _, hk, by group⟩

theorem dcMap_eq_iff (K₀ : Subgroup G) (g : G) (k k' : K₀) :
    dcMap K₀ g k = dcMap K₀ g k' ↔
      k⁻¹ * k' ∈ (K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  simp only [dcMap, QuotientGroup.eq]
  simp [mul_assoc]

theorem card_range_dcMap (K₀ : Subgroup G) (g : G) :
    Nat.card (Set.range (dcMap K₀ g)) = (K₀.map (MulAut.conj g).toMonoidHom).relIndex K₀ := by
  have hker : Setoid.ker (dcMap K₀ g) =
      QuotientGroup.leftRel ((K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀) := by
    ext k k'
    rw [Setoid.ker_def, QuotientGroup.leftRel_apply]
    exact dcMap_eq_iff K₀ g k k'
  rw [Subgroup.relIndex, Subgroup.index,
    ← Nat.card_congr (Setoid.quotientKerEquivRange (dcMap K₀ g)), hker]
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem relIndex_conj_ne_zero (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G))
    (hc : IsCompact (K₀ : Set G)) (g : G) :
    (K₀.map (MulAut.conj g).toMonoidHom).relIndex K₀ ≠ 0 := by
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 hc
  have hopen : IsOpen (((K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ : Subgroup K₀) :
      Set K₀) := by
    have : (((K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ : Subgroup K₀) : Set K₀) =
        Subtype.val ⁻¹' ((fun x => g⁻¹ * x * g) ⁻¹' (K₀ : Set G)) := by
      ext k
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [this]
    exact (hK.preimage (by fun_prop)).preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ hopen
  exact Subgroup.index_ne_zero_of_finite

theorem isOpen_cls_leftRel (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G)) (q : G ⧸ K₀) :
    IsOpen (cls (QuotientGroup.leftRel K₀) q) := by
  rw [cls_leftRel]; exact hK.preimage (continuous_const.mul continuous_id)

variable [MeasurableSpace G] [BorelSpace G]

theorem measure_preimage_mk (μ : Measure G) [μ.IsMulLeftInvariant] (K₀ : Subgroup G)
    (hK : IsOpen (K₀ : Set G)) (S : Set (G ⧸ K₀)) (hS : S.Finite) :
    μ ((QuotientGroup.mk : G → G ⧸ K₀) ⁻¹' S) = (Nat.card S : ENNReal) * μ (K₀ : Set G) := by
  classical
  have hU : (QuotientGroup.mk : G → G ⧸ K₀) ⁻¹' S =
      ⋃ q ∈ hS.toFinset, cls (QuotientGroup.leftRel K₀) q := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.Finite.mem_toFinset, mem_cls,
      exists_prop, exists_eq_right']
  rw [hU, measure_biUnion_finset]
  · simp_rw [cls_leftRel, measure_preimage_mul]
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card S hS]
  · intro q _ q' _ hne
    exact Set.disjoint_left.2 fun x hx hx' => hne (hx.symm.trans hx')
  · exact fun q _ => (isOpen_cls_leftRel K₀ hK q).measurableSet

end Doset

theorem dosetVol : Formalism.DoubleCosetMeasures.DosetVol := by
  intro G _ _ _ _ _ μ _ K₀ hK hc g
  have hne := relIndex_conj_ne_zero K₀ hK hc g
  refine ⟨hne, ?_⟩
  have hfin : (Set.range (dcMap K₀ g)).Finite := by
    have : Finite (Set.range (dcMap K₀ g)) := Nat.finite_of_card_ne_zero (by
      rw [card_range_dcMap]; exact hne)
    exact Set.toFinite _
  rw [doubleCoset_eq_preimage, measure_preimage_mk μ K₀ hK _ hfin, card_range_dcMap]

theorem cls_double {G : Type} [Group G] (K₀ : Subgroup G)
    (q : Quotient (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G))) :
    cls (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) q =
      DoubleCoset.doubleCoset (Quotient.out q) (K₀ : Set G) K₀ := by
  ext y
  rw [mem_cls]
  exact (DoubleCoset.mem_quotToDoubleCoset_iff (H := K₀) (K := K₀) q y).symm

theorem intBiInv : Formalism.DoubleCosetMeasures.IntBiInv := by
  intro G _ _ _ _ _ μ _ K₀ hK hc E _ _ _ f hf hcs
  have hr : ∀ q, IsOpen (cls (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) q) := fun q => by
    rw [cls_double]
    exact hK.mul_left
  have hμq : ∀ q, μ (cls (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) q) =
      ((K₀.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex K₀ : ENNReal) *
        μ (K₀ : Set G) := fun q => by
    rw [cls_double]; exact (dosetVol G μ K₀ hK hc _).2
  have hf' : ∀ x y : G, Quotient.mk (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) x =
      Quotient.mk (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) y → f x = f y := by
    intro x y h
    obtain ⟨a, ha, b, hb, rfl⟩ := (DoubleCoset.eq K₀ K₀ x y).1 h
    exact (hf a ha b hb x).symm
  refine ⟨support_out_finite _ hr f hcs, ?_⟩
  rw [integral_eq_finsum _ hr μ f hf' hcs]
  · exact finsum_congr fun q => by rw [hμq, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  · by_cases h : μ (K₀ : Set G) < ⊤
    · exact Or.inl fun q => (hμq q).symm ▸ ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) h
    · refine Or.inr fun q => ?_
      rw [hμq, not_lt_top_iff.1 h]
      exact ENNReal.mul_top (Nat.cast_ne_zero.2 (relIndex_conj_ne_zero K₀ hK hc _))

end Formalism.DoubleCosetMeasures.P
end
end

-- bundled from Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsIntOfLatOfLe
section
set_option maxHeartbeats 400000

noncomputable section

open Matrix

namespace Formalism.DoubleCosetMeasures.P

open Formalism.DoubleCosetMeasures

theorem uniGroup : Formalism.DoubleCosetMeasures.UniGroup := by
  intro K _ n x y
  exact ⟨fun hx hy => isLowUni_mul K hx hy, fun hx hy => isUpUni_mul K hx hy,
    fun hx => ⟨isLowUni_inv K hx, isLowUni_det K hx⟩,
    fun hx => ⟨isUpUni_inv K hx, isUpUni_det K hx⟩⟩

section Simple

variable {K : Type} [CommRing K] {n : ℕ}

theorem low_simple_entry {x y : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) (hy : IsLowUni y)
    (j : Fin n) (h : j.val + 1 < n) :
    (x * y) ⟨j.val + 1, h⟩ j = x ⟨j.val + 1, h⟩ j + y ⟨j.val + 1, h⟩ j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add j ⟨j.val + 1, h⟩
    (by intro e; simp [Fin.ext_iff] at e)]
  · rw [hy.2 j, hx.2 _]; ring
  · rintro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hlt | hgt
    · have : y k j = 0 := hy.1 (by simpa using hlt)
      simp [this]
    · have hlt : (⟨j.val + 1, h⟩ : Fin n) < k := by
        rw [Fin.lt_def] at hgt ⊢
        have : k.val ≠ j.val + 1 := fun e => hk2 (Fin.ext e)
        simp only
        omega
      have : x ⟨j.val + 1, h⟩ k = 0 := hx.1 (by simpa using hlt)
      simp [this]

theorem up_simple_entry {x y : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x) (hy : IsUpUni y)
    (j : Fin n) (h : j.val + 1 < n) :
    (x * y) j ⟨j.val + 1, h⟩ = x j ⟨j.val + 1, h⟩ + y j ⟨j.val + 1, h⟩ := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add j ⟨j.val + 1, h⟩
    (by intro e; simp [Fin.ext_iff] at e)]
  · rw [hx.2 j, hy.2 _]; ring
  · rintro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hlt | hgt
    · have : x j k = 0 := hx.1 (by simpa using hlt)
      simp [this]
    · have hlt : (⟨j.val + 1, h⟩ : Fin n) < k := by
        rw [Fin.lt_def] at hgt ⊢
        have : k.val ≠ j.val + 1 := fun e => hk2 (Fin.ext e)
        simp only
        omega
      have : y k ⟨j.val + 1, h⟩ = 0 := hy.1 (by simpa using hlt)
      simp [this]

end Simple

theorem simpleAdd : Formalism.DoubleCosetMeasures.SimpleAdd := by
  intro K _ n x y
  constructor
  · intro hx hy
    unfold sLow
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val + 1 < n
    · simp only [dif_pos h]; exact low_simple_entry hx hy j h
    · simp [dif_neg h]
  · intro hx hy
    unfold sUp
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val + 1 < n
    · simp only [dif_pos h]; exact up_simple_entry hx hy j h
    · simp [dif_neg h]

section Int

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem isInt_mul {A B : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) (hB : IsInt R B) :
    IsInt R (A * B) := by
  intro a b
  rw [Matrix.mul_apply]
  exact R.sum_mem fun k _ => R.mul_mem (hA a k) (hB k b)

theorem isInt_adjugate {A : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) :
    IsInt R A.adjugate := by
  let A' : Matrix (Fin n) (Fin n) R := fun a b => ⟨A a b, hA a b⟩
  have hmap : R.subtype.mapMatrix A' = A := by ext a b; rfl
  intro a b
  rw [← hmap, ← RingHom.map_adjugate]
  exact (A'.adjugate a b).2

theorem isInt_inv {A : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) (hd : A.det = 1) :
    IsInt R A⁻¹ := by
  rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul]
  exact isInt_adjugate R hA

end Int

theorem intInv : Formalism.DoubleCosetMeasures.IntInv := by
  intro K _ R n a b Z ha hb haR hbR
  have hda : IsUnit a.det := by simp [isLowUni_det K ha]
  have hdb : IsUnit b.det := by simp [isUpUni_det K hb]
  constructor
  · intro h
    have hZ : Z = a⁻¹ * (a * Z * b) * b⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv b hdb, Matrix.mul_one,
        ← Matrix.mul_assoc, Matrix.nonsing_inv_mul a hda, Matrix.one_mul]
    rw [hZ]
    exact isInt_mul R (isInt_mul R (isInt_inv R haR (isLowUni_det K ha)) h)
      (isInt_inv R hbR (isUpUni_det K hb))
  · intro h
    exact isInt_mul R (isInt_mul R haR h) hbR

section Lat

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem mem_latOf (g : GL (Fin n) K) (w : Fin n → K) :
    w ∈ latOf R g ↔ ∃ v : Fin n → R, (g : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => (v j : K)) = w := by
  unfold latOf
  simp only [Submodule.mem_map, Submodule.mem_top, true_and]
  rfl

theorem latOf_le (g h : GL (Fin n) K)
    (hM : IsInt R (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) :
    latOf R h ≤ latOf R g := by
  intro w hw
  obtain ⟨v, rfl⟩ := (mem_latOf R h w).1 hw
  rw [mem_latOf]
  set M : Matrix (Fin n) (Fin n) K := ((g⁻¹ * h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMdef
  refine ⟨fun i => ⟨(M *ᵥ (fun j => (v j : K))) i, ?_⟩, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact R.sum_mem fun k _ => R.mul_mem (hM i k) (v k).2
  · have hgM : (g : Matrix (Fin n) (Fin n) K) * M = h := by
      rw [hMdef, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    change (g : Matrix (Fin n) (Fin n) K) *ᵥ (M *ᵥ (fun j => (v j : K))) = _
    rw [Matrix.mulVec_mulVec, hgM]

theorem isInt_of_latOf_le (g h : GL (Fin n) K) (hle : latOf R h ≤ latOf R g) :
    IsInt R (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
  intro i j
  have hmem : (h : Matrix (Fin n) (Fin n) K) *ᵥ (fun k => ((Pi.single j (1 : R) : Fin n → R) k : K))
      ∈ latOf R h := (mem_latOf R h _).2 ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := (mem_latOf R g _).1 (hle hmem)
  have hcoe : (fun k => ((Pi.single j (1 : R) : Fin n → R) k : K)) = Pi.single j (1 : K) := by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [hcoe] at hv
  have key : (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j (1 : K) =
      fun k => (v k : K) := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hv, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have := congrFun key i
  rw [Matrix.mulVec_single_one] at this
  simp only [Matrix.col_apply] at this
  rw [this]
  exact (v i).2

end Lat

theorem latticeCoset : Formalism.DoubleCosetMeasures.LatticeCoset := by
  intro K _ R n g h
  constructor
  · intro e
    exact ⟨isInt_of_latOf_le R g h (le_of_eq e.symm), isInt_of_latOf_le R h g (le_of_eq e)⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm (latOf_le R h g h2) (latOf_le R g h h1)

end Formalism.DoubleCosetMeasures.P
end
end

