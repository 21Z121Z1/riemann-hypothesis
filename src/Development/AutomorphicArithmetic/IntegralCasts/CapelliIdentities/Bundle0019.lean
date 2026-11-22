import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsIndepOfSat
section
theorem UpperTheory.Reformulated.B.Ud9.exists_indep_of_sat :
    ∀ {R E : Type} [inst : CommRing R] [IsDomain R] [IsNoetherianRing R]
    [inst_3 : AddCommGroup E] [inst_4 : _root_.Module R E] [Module.Finite R E] [Module.IsTorsionFree R E] (T : Set E)
    (F : Submodule R E),
    (∀ (x : E), x ∈ F ↔ ∃ (a : R), a ≠ (0 : R) ∧ a • x ∈ Submodule.span R T) →
      ∃ (f : Fin (Module.finrank R ↥F) → E), (∀ (j : Fin (Module.finrank R ↥F)), f j ∈ T) ∧ LinearIndependent R f := by
  intro R E _ _ _ _ _ _ _ T F hF
  obtain ⟨I, hI, hmax⟩ := exists_maximal_linearIndepOn R (Subtype.val : T → E)
  set S : Submodule R E := Submodule.span R ((Subtype.val : T → E) '' I) with hS
  have hT : ∀ y ∈ Submodule.span R T, ∃ b : R, b ≠ 0 ∧ b • y ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      by_cases h : (⟨x, hx⟩ : T) ∈ I
      · exact ⟨1, one_ne_zero, by
          rw [one_smul]; exact Submodule.subset_span ⟨⟨x, hx⟩, h, rfl⟩⟩
      · exact hmax ⟨x, hx⟩ h
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [smul_add]
      refine S.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact S.smul_mem _ hax
      · rw [mul_smul]; exact S.smul_mem _ hby
    | smul c x _ hx =>
      obtain ⟨a, ha, hax⟩ := hx
      refine ⟨a, ha, ?_⟩
      rw [smul_comm]; exact S.smul_mem _ hax
  let N : Submodule R F := S.comap F.subtype
  have h0 : Module.rank R (F ⧸ N) = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    obtain ⟨a, ha, hax⟩ := (hF x).1 x.2
    obtain ⟨b, hb, hbx⟩ := hT _ hax
    refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    change (b * a) • (x : E) ∈ S
    rwa [mul_smul]
  have h1 : Module.rank R F = Module.rank R N := by
    rw [← rank_quotient_add_rank_of_isDomain N, h0, zero_add]
  have h2 : Module.rank R N ≤ Module.rank R S := by
    let g : N →ₗ[R] S := (F.subtype.comp N.subtype).codRestrict S (fun x => x.2)
    refine LinearMap.rank_le_of_injective g ?_
    intro x y hxy
    have h : ((g x : S) : E) = ((g y : S) : E) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have h3 : Module.rank R S ≤ Cardinal.mk I :=
    (rank_span_le _).trans Cardinal.mk_image_le
  have h4 : Cardinal.mk (Fin (Module.finrank R F)) ≤ Cardinal.mk I := by
    rw [Cardinal.mk_fin, Module.finrank_eq_rank, h1]
    exact h2.trans h3
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 h4
  exact ⟨fun j => ((e j : T) : E), fun j => (e j : T).2, LinearIndependent.comp hI e e.injective⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsInvariantSubspace
section
theorem UpperTheory.exists_invariant_subspace :
    ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (G ι : Type) [Fintype ι] (K : Set G)
        (σ : G → H →ₗ[ℂ] H) (S : Submodule ℂ H) (E : ι → Module.End ℂ S) (c : G → ι → ι → ℂ),
        (∀ g ∈ K, ∀ v ∈ S, σ g v ∈ S) →
        (∀ g ∈ K, ∀ (i : ι) (v w : S), (w : H) = σ g (v : H) →
          σ g ((E i v : S) : H) = ∑ j, c g i j • ((E j w : S) : H)) →
        ∃ V₀ : Submodule ℂ S,
          (∀ x : S, x ∈ V₀ ↔ ∃ T : Submodule ℂ H, FiniteDimensional ℂ T ∧ (x : H) ∈ T ∧
            ∀ g ∈ K, ∀ v ∈ T, σ g v ∈ T) ∧
          ∀ i, ∀ x ∈ V₀, E i x ∈ V₀ := by
  intro H _ _ G ι _ K σ S E c hS hE
  refine ⟨{ carrier := {x : S | ∃ T : Submodule ℂ H, FiniteDimensional ℂ T ∧ (x : H) ∈ T ∧
              ∀ g ∈ K, ∀ v ∈ T, σ g v ∈ T}
            add_mem' := ?_
            zero_mem' := ?_
            smul_mem' := ?_ }, fun x => Iff.rfl, ?_⟩
  · rintro a b ⟨T₁, f₁, ha, h₁⟩ ⟨T₂, f₂, hb, h₂⟩
    refine ⟨T₁ ⊔ T₂, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩
    intro g hg v hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (h₁ g hg y hy) (h₂ g hg z hz)
  · refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
    intro g _ v hv
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]
    exact Submodule.zero_mem _
  · rintro r x ⟨T, f, hx, h⟩
    exact ⟨T, f, T.smul_mem r hx, h⟩
  · rintro i x ⟨T, f, hx, h⟩
    have fU : FiniteDimensional ℂ (T.comap S.subtype) :=
      FiniteDimensional.of_injective (S.subtype.submoduleComap T) (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun t : T => (t : H)) hab)
    have hmem : ∀ (j : ι) (u : S), (u : H) ∈ T →
        ((E j u : S) : H) ∈ ⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k) := fun j u hu =>
      Submodule.mem_iSup_of_mem j ⟨u, hu, rfl⟩
    refine ⟨⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k), inferInstance, hmem i x hx, ?_⟩
    intro g hg v hv
    have hle : (⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k)) ≤
        (⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k)).comap (σ g) := by
      refine iSup_le fun j => ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply]
      rw [hE g hg j u ⟨σ g u, hS g hg u u.2⟩ rfl]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (hmem k _ (h g hg u hu))
    exact hle hv
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsKill
section
theorem UpperTheory.Reformulated.B.Qk55.exists_kill.{u_1} :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {H : Type u_1}
    [inst_1 : AddCommGroup H] [inst_2 : _root_.Module ℤ_[l] H] (h : H),
    (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] h = (0 : TensorProduct ℤ_[l] ℚ_[l] H) → ∃ (b : ℕ), l ^ b • h = (0 : H) := by
  intro l _ H _ _ h hh
  have h0 : TensorProduct.mk ℤ_[l] ℚ_[l] H 1 h = 0 := hh
  obtain ⟨s, hs⟩ :=
    (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] H 1)).1 h0
  have hs0 : (s : ℤ_[l]) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hs' : (s : ℤ_[l]) • h = 0 := hs
  refine ⟨(s : ℤ_[l]).valuation, ?_⟩
  rw [PadicInt.unitCoeff_spec hs0, mul_smul] at hs'
  have h2 : ((l : ℤ_[l]) ^ (s : ℤ_[l]).valuation) • h = 0 :=
    (IsUnit.smul_eq_zero (Units.isUnit _)).1 hs'
  rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLimitOfApprox
section
theorem UpperTheory.Reformulated.B.Qp1.exists_limit_of_approx.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R)
    [IsPrecomplete I R] (P : ℕ → R → Prop),
    (∀ (n : ℕ) (x : R), P n x → ∃ (y : R), y - x ∈ I ^ n ∧ P (n + (1 : ℕ)) y) →
      ∀ {x₀ : R}, P (0 : ℕ) x₀ → ∃ (x : R), ∀ (n : ℕ), ∃ (y : R), P n y ∧ x - y ∈ I ^ n := by
  intro R _ I hI P h x₀ h₀
  choose g hg hP using h
  let f : (n : ℕ) → {x : R // P n x} := fun n =>
    Nat.rec (motive := fun n => {x : R // P n x}) ⟨x₀, h₀⟩
      (fun n x => ⟨g n x.1 x.2, hP n x.1 x.2⟩) n
  have hstep : ∀ n, (f (n + 1)).1 - (f n).1 ∈ I ^ n := fun n => hg n (f n).1 (f n).2
  have hdiff : ∀ m n, m ≤ n → (f n).1 - (f m).1 ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : (f (n + 1)).1 - (f n).1 ∈ I ^ m := Ideal.pow_le_pow_right hmn (hstep n)
      have h2 := (I ^ m).add_mem h1 ih
      rwa [sub_add_sub_cancel] at h2
  have htop : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hI (f := fun n => (f n).1) (by
    intro m n hmn
    refine SModEq.symm ?_
    rw [SModEq.sub_mem, htop]
    exact hdiff m n hmn)
  refine ⟨L, fun n => ⟨(f n).1, (f n).2, ?_⟩⟩
  have h3 := (hL n).symm
  rwa [SModEq.sub_mem, htop] at h3
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLocalGenerator
section
theorem UpperTheory.Reformulated.B.ExistsLocalGenerator.exists_local_generator :
    ∀ {B : Type} [inst : CommRing B] [IsDedekindDomain B] (I p : Ideal B) [hp : p.IsPrime],
      ∃ π ∈ I, ∃ s ∉ p, ∀ x ∈ I, s * x ∈ Ideal.span {π} := by
  intro B _ _ I p hp
  by_cases hI : I = ⊥
  · refine ⟨0, I.zero_mem, 1, (Ideal.ne_top_iff_one p).mp hp.ne_top, fun x hx => ?_⟩
    rw [hI, Ideal.mem_bot] at hx
    simp [hx]
  have hne : ¬ I ≤ I * p := by
    intro h
    have h1 : I * p = I * 1 := by
      rw [mul_one]
      exact le_antisymm Ideal.mul_le_left h
    have h2 : p = 1 := mul_left_cancel₀ (show I ≠ 0 from hI) h1
    exact hp.ne_top (by rw [h2, Ideal.one_eq_top])
  obtain ⟨π, hπ, hπ'⟩ := SetLike.not_le_iff_exists.mp hne
  have hle : Ideal.span {π} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hπ
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJp : ¬ J ≤ p := by
    intro h
    apply hπ'
    have : π ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self π
    exact Ideal.mul_mono_right h this
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp hJp
  refine ⟨π, hπ, s, hs', fun x hx => ?_⟩
  rw [hJ, mul_comm s x]
  exact Ideal.mul_mem_mul hx hs
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNatMulMem
section
theorem UpperTheory.Reformulated.B.ExistsNatMulMem.exists_nat_mul_mem :
    ∀ (F : Type) [inst : Field F] [NumberField F] (x : F),
    ∃ (m : ℕ), (0 : ℕ) < m ∧ ∃ (r : NumberField.RingOfIntegers F), (↑r : F) = (↑m : F) * x := by
  intro F _ _ x
  have hx : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, hint⟩ := hx.exists_integral_multiple
  have h2 : IsIntegral ℤ (((y.natAbs : ℕ) : F) * x) := by
    rcases Int.natAbs_eq y with h | h
    · have e : ((y.natAbs : ℕ) : F) * x = y • x := by
        rw [zsmul_eq_mul]
        congr 1
        have := congrArg (Int.cast : ℤ → F) h
        rw [Int.cast_natCast] at this
        exact this.symm
      rw [e]; exact hint
    · have e : ((y.natAbs : ℕ) : F) * x = -(y • x) := by
        rw [zsmul_eq_mul, ← neg_mul]
        congr 1
        have := congrArg (Int.cast : ℤ → F) h
        rw [Int.cast_neg, Int.cast_natCast] at this
        rw [this, neg_neg]
      rw [e]; exact hint.neg
  exact ⟨y.natAbs, Int.natAbs_pos.mpr hy, ⟨_, h2⟩, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNsmulMemClosure
section
theorem UpperTheory.Reformulated.B.ExistsNsmulMemClosure.exists_nsmul_mem_closure.{u_1} :
    ∀ {V : Type u_1} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℚ V] (s : Set V),
    ∀ w ∈ Submodule.span ℚ s, ∃ (k : ℕ), (0 : ℕ) < k ∧ k • w ∈ AddSubgroup.closure s := by
  intro V _ _ s w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using AddSubgroup.subset_closure hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have h : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [h]
    exact add_mem (nsmul_mem hx b) (nsmul_mem hy a)
  | smul q x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    refine ⟨q.den * a, Nat.mul_pos q.den_pos ha, ?_⟩
    have h : (q.den * a) • (q • x) = q.num • (a • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ a x,
        ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
      congr 1
      rw [← Rat.mul_den_eq_num q]
      push_cast
      ring
    rw [h]
    exact zsmul_mem hx _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsOfLi
section
theorem UpperTheory.Reformulated.B.Qe54.exists_of_li :
    ∀ {Q ι : Type} [inst : AddCommGroup Q]
    [inst_1 : _root_.Module ℂ Q] [Finite ι] (f : ι → Q →ₗ[ℂ] ℂ),
    LinearIndependent ℂ f → ∀ (v : ι → ℂ), ∃ (q : Q), ∀ (i : ι), (f i : Q → ℂ) q = v i := by
  intro Q ι _ _ _ f hf v
  classical
  have := Fintype.ofFinite ι
  have hs : Function.Surjective (LinearMap.pi f : Q →ₗ[ℂ] (ι → ℂ)) := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro φ hφ
    have hsum : ∑ i, φ (fun j => if i = j then 1 else 0) • f i = 0 := by
      ext q
      have h1 : φ (LinearMap.pi f q) = 0 := LinearMap.congr_fun hφ q
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [LinearMap.sum_apply, mul_comm] using h1
    have h0 := Fintype.linearIndependent_iff.1 hf _ hsum
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp [h0]
  obtain ⟨q, hq⟩ := hs v
  exact ⟨q, fun i => congrFun hq i⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsOrthonormalBasisSesquilinear
section
theorem UpperTheory.Reformulated.B.Qh52.exists_orthonormal_basis_sesquilinear :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V]
    [FiniteDimensional ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ (a b : V), ((B : V → V →ₗ⋆[ℂ] ℂ) b : V → ℂ) a = Star.star (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) b)) →
      (∀ (a : V), a ≠ (0 : V) → (0 : ℝ) < (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) a).re) →
        ∃ (e : Fin (Module.finrank ℂ V) → V),
          (∀ (i : Fin (Module.finrank ℂ V)), ((B : V → V →ₗ⋆[ℂ] ℂ) (e i) : V → ℂ) (e i) = (1 : ℂ)) ∧
            (∀ (x y : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) y =
                  ∑ i : Fin (Module.finrank ℂ V),
                    ((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) (e i) * ((B : V → V →ₗ⋆[ℂ] ℂ) (e i) : V → ℂ) y) ∧
              ∀ (x y : V),
                ‖((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤
                  (((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) x).re * (((B : V → V →ₗ⋆[ℂ] ℂ) y : V → ℂ) y).re := by
  intro V _ _ _ B hs hp
  let c : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => B y x
      conj_inner_symm := fun x y => (hs x y).symm
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · exact (hp x h).le
      add_left := fun x y z => map_add (B z) x y
      smul_left := fun x y r => by simp
      definite := fun x h => by
        by_contra hx
        have h1 := hp x hx
        have h2 : B x x = 0 := h
        rw [h2] at h1
        simp at h1 }
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have hB : ∀ x y : V, B x y = inner ℂ y x := fun _ _ => rfl
  let b := stdOrthonormalBasis ℂ V
  refine ⟨b, fun i => ?_, fun x y => ?_, fun x y => ?_⟩
  · rw [hB]
    exact b.inner_eq_one i
  · simp only [hB]
    rw [← b.sum_inner_mul_inner y x]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · simp only [hB]
    have h := inner_mul_inner_self_le (𝕜 := ℂ) y x
    rw [norm_inner_symm x y] at h
    rw [sq, mul_comm (inner ℂ x x).re]
    exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPermOfMapEq
section
theorem UpperTheory.Reformulated.B.Qh57.exists_perm_of_map_eq :
    ∀ {n : ℕ} (a b : Fin n → ℂ),
    Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val →
      ∃ (e : Equiv.Perm (Fin n)), ∀ (i : Fin n), b ((e : Fin n → Fin n) i) = a i := by
  intro n a b h
  classical
  have key : ∀ (f : Fin n → ℂ) (c : ℂ),
      Fintype.card {i // f i = c} = Multiset.count c (Multiset.map f Finset.univ.val) := by
    intro f c
    rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun _ _ => eq_comm)
  have hc : ∀ c : ℂ, Fintype.card {i // a i = c} = Fintype.card {i // b i = c} := by
    intro c
    rw [key a c, key b c, h]
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPlace
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.ExistsPlace.Plc :
    (E : Type) → [Field E] → Type :=
    fun (E : Type) [Field E] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

theorem UpperTheory.Reformulated.B.ExistsPlace.exists_place :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsCMField E] (q : ℕ),
      Nat.Prime q → ∃ (w : UpperTheory.Reformulated.B.ExistsPlace.Plc E), (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal := by
  intro E _ _ _ q hq
  have hne : (q : NumberField.RingOfIntegers E) ≠ 0 := by
    exact_mod_cast hq.ne_zero
  have hnu : ¬ IsUnit (q : NumberField.RingOfIntegers E) := by
    intro h
    have h1 := h.map (Algebra.norm ℤ (S := NumberField.RingOfIntegers E))
    have h2 : Algebra.norm ℤ (q : NumberField.RingOfIntegers E) =
        (q : ℤ) ^ Module.finrank ℤ (NumberField.RingOfIntegers E) := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := NumberField.RingOfIntegers E) (q : ℤ)
      simpa using this
    rw [h2] at h1
    have hpos : Module.finrank ℤ (NumberField.RingOfIntegers E) ≠ 0 := Module.finrank_pos.ne'
    have h3 : IsUnit (q : ℤ) := (isUnit_pow_iff hpos).1 h1
    exact hq.not_isUnit (Int.ofNat_isUnit.1 h3)
  obtain ⟨M, hM, hqM⟩ := exists_max_ideal_of_mem_nonunits hnu
  refine ⟨⟨M, hM.isPrime, ?_⟩, hqM⟩
  intro h
  rw [h] at hqM
  exact hne (by simpa using hqM)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPowMemOfMulMemPow
section
theorem UpperTheory.Reformulated.B.Qg1.exists_pow_mem_of_mul_mem_pow :
    ∀ {A : Type} [inst : CommRing A] [IsNoetherianRing A] (m : Ideal A) (δ : A),
    (∀ (a : A), δ * a = (0 : A) → a = (0 : A)) → ∀ (j : ℕ), ∃ (k : ℕ), j ≤ k ∧ ∀ (a : A), δ * a ∈ m ^ k → a ∈ m ^ j := by
  intro A _ _ m δ hδ j
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul m (Ideal.span {δ} : Submodule A A)
  refine ⟨j + c, Nat.le_add_right j c, fun a ha => ?_⟩
  have h1 : δ * a ∈ (m ^ (j + c) • ⊤ ⊓ (Ideal.span {δ} : Submodule A A) : Submodule A A) := by
    refine ⟨?_, Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self δ)⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact ha
  rw [hc (j + c) (Nat.le_add_left c j), Nat.add_sub_cancel] at h1
  have h2 : δ * a ∈ Ideal.span {δ} * m ^ j := by
    rw [mul_comm (Ideal.span {δ}), ← Ideal.smul_eq_mul]
    exact Submodule.smul_mono le_rfl inf_le_right h1
  obtain ⟨z, hz, hza⟩ := Ideal.mem_span_singleton_mul.mp h2
  have h3 : a - z = 0 := hδ _ (by rw [mul_sub, hza, sub_self])
  rw [sub_eq_zero.mp h3]
  exact hz
end

