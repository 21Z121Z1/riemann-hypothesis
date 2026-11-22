import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
import Mathlib.Topology.Algebra.ClopenNhdofOne

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.GenOfMax
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem gen_of_max {A : Type} [CommGroup A] (l : ℕ)
    (hl : ∀ s t : A, s ^ l = 1 → t ^ l = 1 → s ≠ 1 → ∃ n : ℕ, t = s ^ n)
    (a : ℕ) (z : A) (h1 : z ^ l ^ (a + 1) = 1) (h0 : z ^ l ^ a ≠ 1) :
    ∀ b, b ≤ a + 1 → ∀ s : A, s ^ l ^ b = 1 → s ∈ Subgroup.zpowers z := by
  intro b
  induction b with
  | zero => intro _ s hs; simp at hs; simp [hs]
  | succ b ih =>
    intro hb s hs
    obtain ⟨n, hn⟩ := hl (z ^ l ^ a) (s ^ l ^ b) (by rw [← pow_mul, ← pow_succ, h1])
      (by rw [← pow_mul, ← pow_succ, hs]) h0
    obtain ⟨c, rfl⟩ : ∃ c, a = c + b := ⟨a - b, by omega⟩
    have h2 : (s / z ^ (l ^ c * n)) ^ l ^ b = 1 := by
      rw [div_pow, hn, ← pow_mul, ← pow_mul, pow_add, mul_right_comm, div_self']
    have h3 := ih (by omega) _ h2
    have h4 := mul_mem h3 (Subgroup.npow_mem_zpowers z (l ^ c * n))
    rwa [div_mul_cancel] at h4

private theorem cyc_abs {A : Type} [CommGroup A] (l : ℕ) (hp : l.Prime)
    (hres : ∀ x : A, x ≠ 1 → ∃ U : Subgroup A, U.index ≠ 0 ∧ x ∉ U)
    (hl : ∀ s t : A, s ^ l = 1 → t ^ l = 1 → s ≠ 1 → ∃ n : ℕ, t = s ^ n) :
    ∃ z : A, (∃ a, z ^ l ^ a = 1) ∧ ∀ s : A, (∃ a, s ^ l ^ a = 1) → ∃ n : ℕ, s = z ^ n := by
  classical
  by_cases hx : ∃ x : A, x ^ l = 1 ∧ x ≠ 1
  · obtain ⟨x, hx1, hx0⟩ := hx
    obtain ⟨U, hU, hxU⟩ := hres x hx0
    let P : ℕ → Prop := fun a => ∃ s : A, s ^ l ^ (a + 1) = 1 ∧ s ^ l ^ a ≠ 1
    have hP0 : P 0 := ⟨x, by simpa using hx1, by simpa using hx0⟩
    have hbd : ∀ a, P a → a ≤ U.index := by
      rintro a ⟨s, h1, h0⟩
      by_contra hlt
      obtain ⟨n, hn⟩ := hl (s ^ l ^ a) x (by rw [← pow_mul, ← pow_succ, h1]) hx1 h0
      apply hxU
      rw [hn]
      apply pow_mem
      have d1 : orderOf (QuotientGroup.mk' U s) ∣ l ^ (a + 1) := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← map_pow, h1, map_one]
      have d2 : orderOf (QuotientGroup.mk' U s) ∣ U.index := orderOf_dvd_natCard _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 d1
      have d3 : l ^ j ≤ U.index := hj ▸ Nat.le_of_dvd (Nat.pos_of_ne_zero hU) d2
      have d4 : j < l ^ j := Nat.lt_pow_self hp.one_lt
      have d5 : orderOf (QuotientGroup.mk' U s) ∣ l ^ a := hj ▸ pow_dvd_pow l (by omega)
      have d6 := orderOf_dvd_iff_pow_eq_one.1 d5
      rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at d6
      exact d6
    obtain ⟨z, h1, h0⟩ : P (Nat.findGreatest P U.index) := Nat.findGreatest_spec (Nat.zero_le _) hP0
    refine ⟨z, ⟨_, h1⟩, ?_⟩
    rintro s ⟨c, hc⟩
    have key : ∀ c, s ^ l ^ c = 1 → s ^ l ^ (Nat.findGreatest P U.index + 1) = 1 := by
      intro c
      induction c with
      | zero => intro h; simp at h; simp [h]
      | succ c ih =>
        intro h
        by_cases h' : s ^ l ^ c = 1
        · exact ih h'
        · have hPc : P c := ⟨s, h, h'⟩
          have := Nat.le_findGreatest (hbd c hPc) hPc
          exact orderOf_dvd_iff_pow_eq_one.1
            ((orderOf_dvd_of_pow_eq_one h).trans (pow_dvd_pow l (by omega)))
    have hm := gen_of_max l hl _ z h1 h0 _ le_rfl s (key c hc)
    have hf : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos hp.pos _, h1⟩
    obtain ⟨n, hn⟩ := hf.mem_powers_iff_mem_zpowers.2 hm
    exact ⟨n, hn.symm⟩
  · refine ⟨1, ⟨0, by simp⟩, ?_⟩
    rintro s ⟨c, hc⟩
    refine ⟨0, ?_⟩
    rw [pow_zero]
    induction c with
    | zero => simpa using hc
    | succ c ih =>
      apply ih
      by_contra h
      exact hx ⟨_, by rw [← pow_mul, ← pow_succ, hc], h⟩

theorem UpperTheory.V.Ws.X1.muCyc :
    ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (l : ℕ) [Fact l.Prime] (H : Subgroup Γ), IsClosed (H : Set Γ) → (∀ s ∈ H, ∀ t ∈ H, s ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → t ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → s ∉ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → ∃ n : ℕ, t * (s ^ n)⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure) → ∃ ζ, MuGen H (muOf l H) ζ := by
  intro Γ _ _ _ _ _ _ l hp H hH hl
  unfold MuGen muOf
  have hcl : IsClosed (((⁅H, H⁆ : Subgroup Γ).topologicalClosure : Subgroup Γ) : Set Γ) :=
    Subgroup.isClosed_topologicalClosure _
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure :=
    fun a ha b hb => Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator ha hb)
  generalize (⁅H, H⁆ : Subgroup Γ).topologicalClosure = C at hl hcl hcomm ⊢
  haveI hN : (C.subgroupOf H).Normal := ⟨fun c hc h => by
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    simpa using mul_mem (hcomm h h.2 c c.2) hc⟩
  let π := QuotientGroup.mk' (C.subgroupOf H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have h1 : ∀ x : H, π x = 1 ↔ (x : Γ) ∈ C := fun x => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
  have h2 : ∀ x y : H, π x = π y ↔ (x : Γ) * (y : Γ)⁻¹ ∈ C := fun x y => by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, h1]; simp
  letI : CommGroup (H ⧸ C.subgroupOf H) :=
    { (inferInstance : Group (H ⧸ C.subgroupOf H)) with
      mul_comm := fun a b => by
        obtain ⟨a, rfl⟩ := hπ a
        obtain ⟨b, rfl⟩ := hπ b
        rw [← map_mul, ← map_mul, h2]
        simpa [mul_assoc] using hcomm a a.2 b b.2 }
  refine (cyc_abs (A := H ⧸ C.subgroupOf H) l hp.out ?_ ?_).elim ?_
  rotate_left 2
  · rintro z ⟨⟨a, ha⟩, hz⟩
    obtain ⟨z, rfl⟩ := hπ z
    refine ⟨z, ⟨z.2, a, ?_⟩, ?_⟩
    · rw [← map_pow, h1] at ha
      simpa using ha
    · rintro s ⟨hs, c, hc⟩
      obtain ⟨n, hn⟩ := hz (π ⟨s, hs⟩) ⟨c, by rw [← map_pow, h1]; simpa using hc⟩
      rw [← map_pow, h2] at hn
      exact ⟨n, by simpa using hn⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := hπ x
    have ho : IsOpen {g : Γ | (x : Γ) * g ∉ C} :=
      hcl.isOpen_compl.preimage (continuous_const_mul (x : Γ))
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
      (by simpa [← h1] using hx)
    refine ⟨(N.toSubgroup.subgroupOf H).map π, ?_, ?_⟩
    · refine ne_zero_of_dvd_ne_zero ?_ (Subgroup.index_map_dvd _ hπ)
      haveI : Finite (Γ ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
      haveI : N.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      exact Subgroup.FiniteIndex.index_ne_zero
    · rintro ⟨n, hn, e⟩
      have hn' : (n : Γ)⁻¹ ∈ N.toSubgroup := inv_mem (Subgroup.mem_subgroupOf.1 hn)
      exact hN hn' ((h2 x n).1 e.symm)
  · intro s t hs ht h0
    obtain ⟨s, rfl⟩ := hπ s
    obtain ⟨t, rfl⟩ := hπ t
    rw [← map_pow, h1] at hs ht
    obtain ⟨n, hn⟩ := hl s s.2 t t.2 (by simpa using hs) (by simpa using ht) (by rwa [← h1])
    exact ⟨n, by rw [← map_pow, h2]; simpa using hn⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.LowLift
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

variable {A R : Type} [CommRing A] [CommRing R]

private def lowOf (a b c d : A) : M4 A := !![1, 0, 0, 0; a, 1, 0, 0; b, c, 1, 0; d, b - a * c, -a, 1]

private theorem lowOf_low (a b c d : A) : IsLow (lowOf a b c d) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsGSp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj, lowOf, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, Matrix.one_apply] <;> ring
  · intro i
    fin_cases i <;> simp [lowOf]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [lowOf] <;> omega

private theorem eq_lowOf {n : M4 A} (h : IsLow n) : n = lowOf (n 1 0) (n 2 0) (n 2 1) (n 3 0) := by
  obtain ⟨hg, hd, hu⟩ := h
  have h01 := hu 0 1 (by decide); have h02 := hu 0 2 (by decide); have h03 := hu 0 3 (by decide)
  have h12 := hu 1 2 (by decide); have h13 := hu 1 3 (by decide); have h23 := hu 2 3 (by decide)
  have d0 := hd 0; have d1 := hd 1; have d2 := hd 2; have d3 := hd 3
  have e1 := congrFun (congrFun hg 1) 0
  have e4 := congrFun (congrFun hg 3) 1
  simp [adj, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, Matrix.one_apply, h01, h02, h03, h12, h13,
    h23, d0, d1, d2, d3] at e1 e4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowOf, h01, h02, h03, h12, h13, h23, d0, d1, d2, d3]
  · linear_combination e4
  · linear_combination e1

private theorem low_mul {m n : M4 A} (hm : IsLow m) (hn : IsLow n) : IsLow (m * n) := by
  refine ⟨by simpa using (grp A).2.2.2.2.2.2.2.1 1 1 m n hm.1 hn.1, ?_, ?_⟩
  · intro i
    rw [eq_lowOf hm, eq_lowOf hn]
    fin_cases i <;> simp [lowOf, Matrix.mul_apply, Fin.sum_univ_four]
  · intro i j hij
    rw [eq_lowOf hm, eq_lowOf hn]
    fin_cases i <;> fin_cases j <;> simp_all [lowOf, Matrix.mul_apply, Fin.sum_univ_four] <;> omega

private theorem up_adj {b : M4 A} (h : IsUp b) : IsUp (adj b) := by
  intro i j hij
  rw [adj_apply, h j.rev i.rev (by simpa [Fin.lt_def, Fin.val_rev] using (by omega : (3 : ℕ) - i.val < 3 - j.val)), smul_zero]

private theorem aux (p : A →+* R) (hp : ∀ x y, p x = 0 → p y = 0 → x * y = 0) (n' : M4 A) (hn : IsGSp 1 n')
    (hl : IsLow (n'.map p)) :
    ∃ m b : M4 A, IsLow m ∧ IsGSp 1 b ∧ IsUp b ∧ IsUp (adj b) ∧ m.map p = n'.map p ∧ m = n' * b := by
  obtain ⟨-, -, hadd, hsmul, hone, hmap, -, hgsp, -⟩ := grp A
  have kz : ∀ X Z : M4 A, X.map p = 0 → Z.map p = 0 → X * Z = 0 := by
    intro X Z hX hZ
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ =>
      hp _ _ (by simpa using congrFun (congrFun hX i) k) (by simpa using congrFun (congrFun hZ k) j)
  have adj0 : adj (0 : M4 A) = 0 := by simpa using hsmul 0 (0 : M4 A)
  have adjneg : ∀ X : M4 A, adj (-X) = -adj X := by
    intro X
    simpa using hsmul (-1) X
  have madj : ∀ X : M4 A, X.map p = 0 → (adj X).map p = 0 := by
    intro X hX
    rw [← hmap R p X, hX]
    simpa using (grp R).2.2.2.1 (0 : R) (0 : M4 R)
  set m0 := lowOf (n' 1 0) (n' 2 0) (n' 2 1) (n' 3 0) with hm0d
  have hm0 : IsLow m0 := lowOf_low _ _ _ _
  have hm0l : adj m0 * m0 = 1 := by simpa [IsGSp] using hm0.1
  have hm0r : m0 * adj m0 = 1 := mul_eq_one_comm.mp hm0l
  have hmap0 : m0.map p = n'.map p := by
    rw [eq_lowOf hl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hm0d, lowOf]
  have hN : adj (n'.map p) * n'.map p = 1 := by simpa [IsGSp] using hl.1
  set Y := adj m0 * n' - 1 with hYd
  have hY : Y.map p = 0 := by
    show p.mapMatrix Y = 0
    rw [hYd, map_sub, map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← hmap R p m0,
      hmap0, hN, sub_self]
  have h1Y : adj m0 * n' = 1 + Y := by rw [hYd]; abel
  have ha : IsGSp 1 (adj m0) := by
    show adj (adj m0) * adj m0 = (1 : A) • 1
    rw [(grp A).2.1, hm0r, one_smul]
  have hadjY : adj Y + Y = 0 := by
    have g : IsGSp 1 (adj m0 * n') := by simpa using hgsp 1 1 _ _ ha hn
    have g' : adj (1 + Y) * (1 + Y) = 1 := by simpa [IsGSp, h1Y] using g
    rw [hadd, hone] at g'
    have e : (1 + adj Y) * (1 + Y) = 1 + (adj Y + Y) + adj Y * Y := by noncomm_ring
    rw [e, kz _ _ (madj Y hY) hY, add_zero] at g'
    simpa using g'
  set Yu : M4 A := Matrix.of fun i j => if i ≤ j then Y i j else 0 with hYud
  have hYu : Yu.map p = 0 := by
    ext i j
    have := congrFun (congrFun hY i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    simp only [hYud, Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]
    split_ifs <;> simp [this]
  have hadjYu : adj Yu + Yu = 0 := by
    ext i j
    have h := congrFun (congrFun hadjY i) j
    simp only [Matrix.add_apply, adj_apply, Matrix.zero_apply] at h
    simp only [Matrix.add_apply, adj_apply, Matrix.zero_apply, hYud, Matrix.of_apply, Fin.rev_le_rev]
    split_ifs <;> simp_all
  set b : M4 A := 1 - Yu with hbd
  have hbup : IsUp b := by
    intro i j hij
    simp [hbd, hYud, Matrix.one_apply, hij.ne', not_le.mpr hij]
  have hbg : IsGSp 1 b := by
    show adj b * b = (1 : A) • 1
    have ea : adj b = 1 - adj Yu := by
      rw [hbd, sub_eq_add_neg, hadd, adjneg, hone, ← sub_eq_add_neg]
    rw [ea, one_smul]
    have e : (1 - adj Yu) * (1 - Yu) = 1 - (adj Yu + Yu) + adj Yu * Yu := by noncomm_ring
    rw [e, hadjYu, kz _ _ (madj Yu hYu) hYu]
    simp
  have hbmap : p.mapMatrix b = 1 := by
    rw [hbd, map_sub, map_one, RingHom.mapMatrix_apply, hYu, sub_zero]
  have e1 : adj m0 * n' * b = 1 + (Y - Yu) := by
    rw [h1Y, hbd]
    have e : (1 + Y) * (1 - Yu) = 1 + (Y - Yu) - Y * Yu := by noncomm_ring
    rw [e, kz _ _ hY hYu, sub_zero]
  have hlow : IsLow (adj m0 * n' * b) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa using hgsp _ _ _ _ (by simpa using hgsp 1 1 _ _ ha hn) hbg
    · intro i
      rw [e1]
      simp [hYud]
    · intro i j hij
      rw [e1]
      simp [hYud, Matrix.one_apply, hij.ne, hij.le]
  have hm := low_mul hm0 hlow
  have hmeq : m0 * (adj m0 * n' * b) = n' * b := by
    rw [← mul_assoc, ← mul_assoc, hm0r, one_mul]
  refine ⟨m0 * (adj m0 * n' * b), b, hm, hbg, hbup, up_adj hbup, ?_, hmeq⟩
  rw [hmeq]
  show p.mapMatrix (n' * b) = p.mapMatrix n'
  rw [map_mul, hbmap, mul_one]

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.lowLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ n' : M4 A, IsGSp 1 n' → IsLow (n'.map p) → ∃ m b : M4 A, IsLow m ∧ IsGSp 1 b ∧ IsUp b ∧ IsUp (adj b) ∧ m.map p = n'.map p ∧ m = n' * b := by
  intro Λ _ _ _ _ A R _ _ _ _ _ _ p _ hker n' hn hl
  have hle : RingHom.ker p ≤ maximalIdeal A := by
    apply IsLocalRing.le_maximalIdeal
    intro htop
    have h1 : (1 : A) ∈ RingHom.ker p := by rw [htop]; trivial
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  refine aux (p : A →+* R) (fun x y hx hy => ?_) n' hn hl
  have hm : x * y ∈ maximalIdeal A * RingHom.ker p :=
    Ideal.mul_mem_mul (hle (by simpa [RingHom.mem_ker] using hx)) (by simpa [RingHom.mem_ker] using hy)
  rw [hker] at hm
  simpa using hm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.PresQuot
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.presQuot :
    ∀ (Λ R' R : Type) [CommRing Λ] [CommRing R'] [Algebra Λ R'] [CommRing R] [Algebra Λ R] (a b : ℕ) (τ : Type) [Finite τ] (g : R' →ₐ[Λ] R) (e : τ → R'), HasPres Λ R' a b → Function.Surjective g → RingHom.ker g = Ideal.span (Set.range e) → HasPres Λ R a (b + Nat.card τ) := by
  intro Λ R' R _ _ _ _ _ a b τ _ g e hP hg he
  obtain ⟨π, f, hπ, hk⟩ := hP
  obtain ⟨σ⟩ : Nonempty (τ ≃ Fin (Nat.card τ)) := ⟨Finite.equivFin τ⟩
  choose l hl using fun t => hπ (e t)
  refine ⟨g.comp π, Fin.append f (l ∘ σ.symm), hg.comp hπ, ?_⟩
  have hrange : Set.range (Fin.append f (l ∘ σ.symm)) = Set.range f ∪ Set.range l := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i => exact Or.inl ⟨i, by simp⟩
      | right i => exact Or.inr ⟨σ.symm i, by simp⟩
    · rintro (⟨i, rfl⟩ | ⟨t, rfl⟩)
      · exact ⟨Fin.castAdd _ i, by simp⟩
      · exact ⟨Fin.natAdd _ (σ t), by simp⟩
  have hker : RingHom.ker (g.comp π) = Ideal.comap π (RingHom.ker g) := by
    ext x
    simp [RingHom.mem_ker]
  have hmap : Ideal.span (Set.range e) = Ideal.map π (Ideal.span (Set.range l)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext t
    exact (hl t).symm
  rw [hker, he, hmap, Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, hk, hrange,
    Ideal.span_union, sup_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.RankAdjLe
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

private theorem rank_adj_le {k : Type} [Field k] (X : M4 k) : (adj X).rank ≤ X.rank := by
  have e : adj X = Matrix.diagonal (fun i => (sgn i : k)) * ((Matrix.transpose X).submatrix Fin.rev Fin.rev) * Matrix.diagonal (fun i => (sgn i : k)) := by
    ext i j
    rw [adj_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.transpose_apply, zsmul_eq_mul]
    push_cast
    ring
  rw [e]
  calc _ ≤ (Matrix.diagonal (fun i => (sgn i : k)) * ((Matrix.transpose X).submatrix Fin.rev Fin.rev)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ ((Matrix.transpose X).submatrix Fin.rev Fin.rev).rank := Matrix.rank_mul_le_right _ _
    _ = X.rank := by
      rw [← Matrix.rank_transpose X]
      exact Matrix.rank_submatrix (Matrix.transpose X) Fin.revPerm Fin.revPerm

private noncomputable def cmp {k : Type} [Field k] (p : M4 k) :
    M4 k →ₗ[k] (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin) where
  toFun X := p.mulVecLin.rangeRestrict ∘ₗ X.mulVecLin ∘ₗ (LinearMap.range p.mulVecLin).subtype
  map_add' X Y := by
    rw [Matrix.mulVecLin_add, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' a X := by
    ext v i
    simp [Matrix.smul_mulVec, Matrix.mulVec_smul]

private theorem cmp_zero {k : Type} [Field k] (p X : M4 k) (h : cmp p X = 0) : p * X * p = 0 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun w => ?_
  simp only [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h2 := congrArg Subtype.val (LinearMap.congr_fun h ⟨Matrix.mulVec p w, w, rfl⟩)
  simpa [cmp] using h2

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.ccDim :
    ∀ {k Γ : Type} [Field k] [Group Γ] (r : Γ →* M4 k) (h : ∀ g, ∃ x, IsGSp x (r g)), (2 : k) ≠ 0 → ∀ s : Γ, s * s = 1 → IsGSp (-1) (r s) → Module.finrank k (LinearMap.ker (adSp r h s - 1)) ≤ 4 := by
  intro k Γ _ _ r h h2 s hss hs
  set g := r s with hgdef
  have adj_mul := (grp k).1
  have adj_adj := (grp k).2.1
  have adj_add := (grp k).2.2.1
  have adj_smul := (grp k).2.2.2.1
  have adj_one := (grp k).2.2.2.2.1
  have hg2 : g * g = 1 := by rw [hgdef, ← r.map_mul, hss, r.map_one]
  have hsi : s⁻¹ = s := (eq_inv_of_mul_eq_one_left hss).symm
  have hadj : adj g = -g := by
    have e : adj g * g = (-1 : k) • 1 := hs
    calc adj g = adj g * g * g := by rw [Matrix.mul_assoc, hg2, Matrix.mul_one]
      _ = -g := by rw [e]; simp
  set c : k := (2 : k)⁻¹ with hc
  have hc2 : c * 2 = 1 := inv_mul_cancel₀ h2
  set p : M4 k := c • (1 + g) with hp
  set q : M4 k := c • (1 - g) with hq
  have hpq : p + q = 1 := by
    rw [hp, hq, ← smul_add]
    have e : (1 + g) + (1 - g) = (2 : k) • (1 : M4 k) := by rw [two_smul]; abel
    rw [e, smul_smul, hc2, one_smul]
  have hadjp : adj p = q := by
    rw [hp, hq, adj_smul, adj_add, adj_one, hadj, sub_eq_add_neg]
  have hadjq : adj q = p := by rw [← hadjp, adj_adj]
  have hpq0 : p * q = 0 := by
    have e : (1 + g) * (1 - g) = 0 := by
      rw [add_mul, mul_sub, mul_sub, hg2]
      simp
    rw [hp, hq, smul_mul_assoc, mul_smul_comm, e]
    simp
  have hpp : p * p = p := by
    have e : p * p = p * (p + q) := by rw [mul_add, hpq0, add_zero]
    rw [e, hpq, mul_one]
  have hrk : p.rank ≤ 2 := by
    have h1 : q.rank ≤ p.rank := by rw [← hadjp]; exact rank_adj_le p
    have h1' : p.rank ≤ q.rank := by rw [← hadjq]; exact rank_adj_le q
    have hle : LinearMap.range q.mulVecLin ≤ LinearMap.ker p.mulVecLin := by
      rintro _ ⟨w, rfl⟩
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hpq0, Matrix.zero_mulVec]
    have hmono := Submodule.finrank_mono hle
    have hsum := LinearMap.finrank_range_add_finrank_ker p.mulVecLin
    rw [Module.finrank_fin_fun] at hsum
    have eq1 : q.rank = Module.finrank k (LinearMap.range q.mulVecLin) := rfl
    have eq2 : p.rank = Module.finrank k (LinearMap.range p.mulVecLin) := rfl
    omega
  let K := LinearMap.ker (adSp r h s - 1)
  let ψ : K →ₗ[k] (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin) :=
    cmp p ∘ₗ (sp4 k).subtype ∘ₗ K.subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨Y, hYsp⟩, hYk⟩ hY
    have hYa : adj Y = -Y := hYsp
    have hfix : g * Y * g = Y := by
      have e := LinearMap.mem_ker.mp hYk
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at e
      have e2 := congrArg Subtype.val e
      rw [adSp_val, hsi] at e2
      exact e2
    have hcomm : g * Y = Y * g := by
      calc g * Y = g * Y * (g * g) := by rw [hg2, Matrix.mul_one]
        _ = (g * Y * g) * g := by simp only [Matrix.mul_assoc]
        _ = Y * g := by rw [hfix]
    have hpY : p * Y = Y * p := by
      rw [hp, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hcomm]
    have hz : p * Y * p = 0 := cmp_zero p Y hY
    have hYp : Y * p = 0 := by
      rw [hpY, Matrix.mul_assoc, hpp] at hz
      exact hz
    have h0 : adj (0 : M4 k) = 0 := by simpa using adj_smul 0 0
    have hqY : q * Y = 0 := by
      have e := congrArg adj hYp
      rw [adj_mul, hadjp, hYa, h0, Matrix.mul_neg, neg_eq_zero] at e
      exact e
    have hq' : q = 1 - p := eq_sub_of_add_eq' hpq
    have hYq : Y * q = 0 := by
      rw [hq'] at hqY ⊢
      rw [Matrix.mul_sub, Matrix.mul_one, ← hpY]
      rw [Matrix.sub_mul, Matrix.one_mul] at hqY
      exact hqY
    have hY0 : Y = 0 := by
      calc Y = Y * (p + q) := by rw [hpq, Matrix.mul_one]
        _ = 0 := by rw [Matrix.mul_add, hYp, hYq, add_zero]
    apply Subtype.ext
    apply Subtype.ext
    exact hY0
  calc Module.finrank k K ≤ Module.finrank k (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = p.rank * p.rank := by rw [Module.finrank_linearMap]; rfl
    _ ≤ 2 * 2 := Nat.mul_le_mul hrk hrk
    _ = 4 := rfl
end

