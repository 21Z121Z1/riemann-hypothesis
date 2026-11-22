import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0019
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0018
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0001
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0020

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormDiscrIdealOfLe
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem det_update_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (x : ι → V)
    (a : ι → K) (i : ι) : b.det (Function.update x i (∑ k, a k • x k)) = a i * b.det x := by
  rw [Basis.det_apply, Basis.det_apply, ← Matrix.det_transpose,
    ← Matrix.det_transpose (b.toMatrix x)]
  have e : Matrix.transpose (b.toMatrix (Function.update x i (∑ k, a k • x k))) =
      (Matrix.transpose (b.toMatrix x)).updateRow i (∑ k, a k • Matrix.transpose (b.toMatrix x) k) := by
    ext r s
    rcases eq_or_ne r i with rfl | hr
    · simp [Basis.toMatrix_apply, Matrix.updateRow_self, Finset.sum_apply, map_sum, map_smul]
    · simp [Basis.toMatrix_apply, Matrix.updateRow_ne hr, Function.update_apply, hr]
  rw [e, Matrix.det_updateRow_sum, smul_eq_mul]

theorem exists_adjust (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {c : 𝓞 K}
    (hc : c ∉ P) : ∃ π ∈ P, c + π ∉ P ∧ c + π ∉ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  have hadd : ∀ π ∈ P, c + π ∉ P := fun π hπ h => hc (by simpa using P.sub_mem h hπ)
  have hle2 : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≤ P.comap (conjO K) := by
    refine Ideal.span_le.2 ?_
    rintro r ⟨s, hs, hrs⟩
    show conjO K r ∈ P
    have e : conjO K r = s := by
      apply IsFractionRing.injective (𝓞 K) K
      have e1 : algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r) := by
        first | rfl | simp [conjO]
      rw [e1, hrs, star_star]
    rw [e]
    exact hs
  have hne_top : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 K) ∈ P.comap (conjO K) := hle2 (by rw [htop]; exact Submodule.mem_top)
    rw [Ideal.mem_comap, map_one] at h1
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
  by_cases hc' : c ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P
  · have hnle : ¬ P ≤ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
      intro hle
      have hPe := hP.eq_of_le hne_top hle
      exact hc (by rw [hPe]; exact hc')
    obtain ⟨π, hπ, hπ'⟩ := SetLike.not_le_iff_exists.1 hnle
    refine ⟨π, hπ, hadd π hπ, fun h => hπ' ?_⟩
    have h3 := (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).sub_mem h hc'
    simpa using h3
  · exact ⟨0, P.zero_mem, by simpa using hc, by simpa using hc'⟩

theorem step_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {A B : Submodule (𝓞 K) V} {y : V} (S : IsStep P A B y)
    (hB : Formalism.HermitianLatticesTheory.IsIntegralLat h B) (b : Basis (Fin (finrank K V)) K V) :
    discrIdeal h A ≤ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * discrIdeal h B := by
  refine discrIdeal_le b fun x hx z hz => ?_
  have hxB : ∀ i, x i ∈ B := fun i => S.le (hx i)
  by_cases hδ : b.det x = 0
  · have : z = 0 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [hz, hδ, mul_zero, map_zero]
    rw [this]; exact Ideal.zero_mem _
  have hbas := (b.is_basis_iff_det).2 (isUnit_iff_ne_zero.2 hδ)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
    (hbas.2 ▸ Submodule.mem_top : y ∈ Submodule.span K (Set.range x))
  let f : Option (Fin (finrank K V)) → K := fun o => o.elim 1 a
  obtain ⟨t, c, hc, j, hj⟩ := exists_prim f (j₀ := none) (by simp [f]) hP.ne_top
  have hf0 : f none = 1 := rfl
  have hfs : ∀ i, f (some i) = a i := fun i => rfl
  have hc0 : c none ∈ P := by
    apply S.mem_of_smul_mem hP
    have : c none • y = ∑ i, c (some i) • x i := by
      rw [← algebraMap_smul K, hc none, ← ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul K (c (some i)), hc (some i), smul_smul, hf0, hfs, mul_one]
    rw [this]; exact A.sum_mem fun i _ => A.smul_mem _ (hx i)
  obtain ⟨i, rfl⟩ : ∃ i, j = some i := by
    cases j with
    | none => exact absurd hc0 hj
    | some i => exact ⟨i, rfl⟩
  have hδi : b.det (Function.update x i y) = a i * b.det x := by rw [← ha, det_update_sum]
  have hrel : algebraMap (𝓞 K) K (c (some i)) * b.det x =
      algebraMap (𝓞 K) K (c none) * b.det (Function.update x i y) := by
    rw [hc, hc, hδi, hf0, hfs]; ring
  obtain ⟨π, hπ, hcP, hcQ⟩ := exists_adjust hK hP hj
  set c₁ := c (some i) + π with hc₁
  set c₀ := c none with hc₀
  have hcδ : algebraMap (𝓞 K) K c₁ * b.det x =
      algebraMap (𝓞 K) K c₀ * b.det (Function.update x i y) + algebraMap (𝓞 K) K π * b.det x := by
    rw [hc₁, map_add, add_mul, hrel]
  have hxk : ∀ k, k ≠ i → x k ∈ B := fun k _ => hxB k
  have huy := update_mem hxk S.mem
  obtain ⟨zyy, hyy⟩ := exists_mixed hB b huy huy
  obtain ⟨zyx, hyx⟩ := exists_mixed hB b huy hxB
  obtain ⟨zxy, hxy⟩ := exists_mixed hB b hxB huy
  have myy := mem_discrIdeal b huy hyy
  have mxx := mem_discrIdeal b hxB hz
  have myx : zyx ∈ discrIdeal h B :=
    mixed_mem hK hB b hxk S.mem (hxB i) (by rw [Function.update_eq_self]; exact hyx)
  have mxy : zxy ∈ discrIdeal h B :=
    mixed_mem hK hB b hxk (hxB i) S.mem (by rw [Function.update_eq_self]; exact hxy)
  have heq : conjO K c₁ * c₁ * z = conjO K c₀ * c₀ * zyy + conjO K c₀ * π * zyx +
      conjO K π * c₀ * zxy + conjO K π * π * z := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    simp only [map_add, map_mul, algebraMap_conjO, hz, hyy, hyx, hxy]
    have h1 : star (algebraMap (𝓞 K) K c₁) * algebraMap (𝓞 K) K c₁ *
        (star (b.det x) * gdet h b * b.det x) =
        star (algebraMap (𝓞 K) K c₁ * b.det x) * gdet h b * (algebraMap (𝓞 K) K c₁ * b.det x) := by
      rw [star_mul']; ring
    rw [h1, hcδ, star_add, star_mul', star_mul']
    ring
  have hmem : conjO K c₁ * c₁ ∈ col (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * discrIdeal h B) z := by
    rw [mem_col, heq]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (term_mem hc0 hc0 myy)
      (term_mem hc0 hπ myx)) (term_mem hπ hc0 mxy)) (term_mem hπ hπ mxx)
  have hPP : P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≤
      col (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * discrIdeal h B) z :=
    fun r hr => Ideal.mul_mem_mul hr mxx
  apply mem_of_col_eq_top
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hcc : ∀ w : 𝓞 K, conjO K w ∈ P → w ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    intro w hw; rw [conjIdeal_eq_comap, Ideal.mem_comap]; exact hw
  have hcc' : ∀ w : 𝓞 K, conjO K w ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P → w ∈ P := by
    intro w hw; rw [conjIdeal_eq_comap, Ideal.mem_comap, conjO_conjO] at hw; exact hw
  rcases hM.isPrime.mul_le.1 (hPP.trans hle) with h1 | h1
  · have hMP := hP.eq_of_le hM.ne_top h1
    rcases hM.isPrime.mem_or_mem (hle hmem) with h2 | h2
    · exact hcQ (hcc _ (hMP ▸ h2))
    · exact hcP (hMP ▸ h2)
  · have hMP := (conjIdeal_isMaximal hK hP).eq_of_le hM.ne_top h1
    rcases hM.isPrime.mem_or_mem (hle hmem) with h2 | h2
    · exact hcP (hcc' _ (hMP ▸ h2))
    · exact hcQ (hMP ▸ h2)

omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem IsStep.relIndex {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {A B : Submodule (𝓞 K) V} {y : V}
    (S : IsStep P A B y) : A.toAddSubgroup.relIndex B.toAddSubgroup = Ideal.absNorm P := by
  classical
  let f : 𝓞 K →+ B.toAddSubgroup :=
    { toFun := fun c => ⟨c • y, B.smul_mem c S.mem⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp [add_smul] }
  let g : 𝓞 K →+ B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup :=
    (QuotientAddGroup.mk' _).comp f
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨c, hc⟩ := S.gen x.1 x.2
    refine ⟨c, ?_⟩
    simp only [g, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simpa [f, neg_add_eq_sub] using hc
  have hker : g.ker = P.toAddSubgroup := by
    ext c
    simp only [AddMonoidHom.mem_ker, g, f, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact ⟨fun h => S.mem_of_smul_mem hP h, fun h => S.smul c h⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card,
    ← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv, hker,
    Ideal.absNorm_apply]
  rfl

theorem absNorm_discrIdeal_of_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {B : Submodule (𝓞 K) V} (hB : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    (b : Basis (Fin (finrank K V)) K V) :
    ∀ (n : ℕ) (A : Submodule (𝓞 K) V), A ≤ B → A.toAddSubgroup.relIndex B.toAddSubgroup = n →
      n ≠ 0 → Ideal.absNorm (discrIdeal h A) = n ^ 2 * Ideal.absNorm (discrIdeal h B) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hAB hn hn0
  by_cases hBA : B ≤ A
  · have : A = B := le_antisymm hAB hBA
    subst this
    rw [AddSubgroup.relIndex_self] at hn
    rw [← hn, one_pow, one_mul]
  obtain ⟨y₀, hy₀B, hy₀A⟩ := SetLike.not_le_iff_exists.1 hBA
  let J : Ideal (𝓞 K) := A.comap (LinearMap.toSpanSingleton (𝓞 K) V y₀)
  have hJ : ∀ c, c ∈ J ↔ c • y₀ ∈ A := fun c => Iff.rfl
  have hJtop : J ≠ ⊤ := by
    intro hJt
    have : (1 : 𝓞 K) ∈ J := hJt ▸ Submodule.mem_top
    rw [hJ, one_smul] at this
    exact hy₀A this
  have hJbot : J ≠ ⊥ := by
    intro hJb
    obtain ⟨k, hk0, -, hk⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero
      (H := A.toAddSubgroup) (K := B.toAddSubgroup) (hn ▸ hn0) (a := y₀) hy₀B
    have h1 : (k : 𝓞 K) ∈ J := by
      rw [hJ, Nat.cast_smul_eq_nsmul]
      exact hk.1
    rw [hJb, Ideal.mem_bot] at h1
    exact hk0.ne' (by exact_mod_cast h1)
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJtop
  obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.2 hJP
  have hJ'0 : J' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hJ'
    exact hJbot hJ'
  have hnle : ¬ J' ≤ J := by
    intro hle
    have h1 : P * J' = 1 * J' := by
      rw [one_mul, ← hJ']
      exact le_antisymm (hJ' ▸ Ideal.mul_le_right) hle
    exact hP.ne_top (by rw [mul_right_cancel₀ hJ'0 h1, Ideal.one_eq_top])
  obtain ⟨c, hcJ', hcJ⟩ := SetLike.not_le_iff_exists.1 hnle
  have S : IsStep P A (A ⊔ Submodule.span (𝓞 K) {c • y₀}) (c • y₀) := by
    refine ⟨le_sup_left, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), hcJ,
      fun π hπ => ?_, fun x hx => ?_⟩
    · rw [smul_smul, ← hJ, hJ']
      exact Ideal.mul_mem_mul hπ hcJ'
    · obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.1 hw
      exact ⟨e, by rwa [add_sub_cancel_right]⟩
  have hA'B : A ⊔ Submodule.span (𝓞 K) {c • y₀} ≤ B :=
    sup_le hAB ((Submodule.span_singleton_le_iff_mem _ _).2 (B.smul_mem c hy₀B))
  have hA' : Formalism.HermitianLatticesTheory.IsIntegralLat h (A ⊔ Submodule.span (𝓞 K) {c • y₀}) :=
    fun x hx w hw => hB x (hA'B hx) w (hA'B hw)
  have hmul := AddSubgroup.relIndex_mul_relIndex A.toAddSubgroup
    (A ⊔ Submodule.span (𝓞 K) {c • y₀}).toAddSubgroup B.toAddSubgroup S.le hA'B
  rw [S.relIndex hP, hn] at hmul
  have hq1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  have hq0 : Ideal.absNorm P ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hmul; exact hn0 hmul.symm
  have hn'0 : (A ⊔ Submodule.span (𝓞 K) {c • y₀}).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact hn0 hmul.symm
  have hlt : (A ⊔ Submodule.span (𝓞 K) {c • y₀}).toAddSubgroup.relIndex B.toAddSubgroup < n := by
    rw [← hmul]
    have h2 : 2 ≤ Ideal.absNorm P := by omega
    nlinarith [Nat.pos_of_ne_zero hn'0]
  have hI : discrIdeal h A = P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P *
      discrIdeal h (A ⊔ Submodule.span (𝓞 K) {c • y₀}) :=
    le_antisymm (step_le hK hP S hA' b) (step_ge hK hP S hA' b)
  rw [hI, map_mul, map_mul, absNorm_conjIdeal hK, ih _ hlt _ hA'B rfl hn'0, ← hmul]
  ring

end Formalism.HermitianLattices.Ext.L3.BallB
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsAddConjTransposeEq
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_add_conj_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (a : 𝓞 F) :
    ∃ z : 𝓞 K, z + conjO K z = algebraMap (𝓞 F) (𝓞 K) a := by
  have htop : LinearMap.range (idealPowerSpanBounds.trF hF) = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_le_maximal (LinearMap.range (idealPowerSpanBounds.trF hF)) hne
    obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
    have hmem : ∀ z : 𝓞 K, z + conjO K z ∈ extP K 𝔭 := fun z => by
      rw [← idealPowerSpanBounds.trF_spec hF]
      exact Ideal.mem_map_of_mem _ (hle ⟨z, rfl⟩)
    have h2 : (2 : 𝓞 K) ∈ extP K 𝔭 := by
      have := hmem 1
      rwa [map_one, one_add_one_eq_two] at this
    have hsq : (θ - conjO K θ) * (θ - conjO K θ) ∈ extP K 𝔭 := by
      have : (θ - conjO K θ) * (θ - conjO K θ) =
          (θ + conjO K θ) * (θ + conjO K θ) - 2 * (2 * (θ * conjO K θ)) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ (hmem θ)) (Ideal.mul_mem_right _ _ h2)
    have h1 : (θ - conjO K θ) ∈ extP K 𝔭 ^ 1 := idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by rwa [pow_one])
    have h0 : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 := idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by rwa [mul_one])
    have h3 := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 1).1 (by rwa [map_one])
    rw [pow_one] at h3
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  obtain ⟨z, hz⟩ : a ∈ LinearMap.range (idealPowerSpanBounds.trF hF) := htop ▸ Submodule.mem_top
  exact ⟨z, by rw [← idealPowerSpanBounds.trF_spec hF, hz]⟩

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsASDOfTuple
section
noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA Module

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem gram_det_smul_orth {n : ℕ} {y : Fin n → V} (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0)
    (d : Fin n → K) :
    (gram h fun i => d i • y i).det = (∏ i, star (d i) * d i) * ∏ i, h (y i) (y i) := by
  have hg : (gram h fun i => d i • y i) =
      Matrix.diagonal fun i => star (d i) * d i * h (y i) (y i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [gram]
      simp only [starRingEnd_apply]
      ring
    · simp [gram, Matrix.diagonal_apply_ne _ hij, horth i j hij]
  rw [hg, Matrix.det_diagonal, Finset.prod_mul_distrib]

theorem gram_det_orth {n : ℕ} {y : Fin n → V} (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0) :
    (gram h y).det = ∏ i, h (y i) (y i) := by
  have hg : gram h y = Matrix.diagonal fun i => h (y i) (y i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [gram]
    · simp [gram, Matrix.diagonal_apply_ne _ hij, horth i j hij]
  rw [hg, Matrix.det_diagonal]

theorem expand_orth [FiniteDimensional K V] {y : Fin (finrank K V) → V}
    (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0) (hne : ∀ i, h (y i) (y i) ≠ 0) (v : V) :
    v = ∑ i, (h (y i) v * (h (y i) (y i))⁻¹) • y i := by
  have hli : LinearIndependent K y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hj := congrArg (h (y j)) hg
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hj
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero])
      (by simp)] at hj
    exact (mul_eq_zero.mp hj).resolve_right (hne j)
  by_cases h0 : finrank K V = 0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    exact Subsingleton.elim _ _
  haveI : Nonempty (Fin (finrank K V)) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩
  set b := basisOfLinearIndependentOfCardEqFinrank hli (Fintype.card_fin _) with hb
  have hbi : ∀ i, b i = y i := fun i => by
    rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hv : ∑ i, b.repr v i • y i = v := by
    simp_rw [← hbi]
    exact b.sum_repr v
  have hc : ∀ j, b.repr v j = h (y j) v * (h (y j) (y j))⁻¹ := by
    intro j
    rw [eq_mul_inv_iff_mul_eq₀ (hne j)]
    have hj := congrArg (h (y j)) hv
    simp only [map_sum, map_smul, smul_eq_mul] at hj
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero])
      (by simp)] at hj
    exact hj
  calc v = ∑ i, b.repr v i • y i := hv.symm
    _ = _ := Finset.sum_congr rfl fun i _ => by rw [hc i]

theorem exists_isASD_of_tuple [FiniteDimensional K V] (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {M : AddSubgroup V} (hM : IsLatIn S h ⊤ M)
    (x : Fin (finrank K V) → V) (hx : ∀ i, x i ∈ M)
    (hdet : ¬ Dv S π ((gram h x).det * π⁻¹))
    (hall : ∀ t : Fin (finrank K V) → V, (∀ i, t i ∈ M) → (∀ i j, i ≠ j → h (t i) (t j) = 0) →
      Dv S π (gram h t).det) :
    ∃ z, IsASD S π h ⊤ M z := by
  obtain ⟨y, horth, hspan⟩ := exists_orth_tuple hS hπ hs _ x
    (fun i j => hM.int _ (hx i) _ (hx j)) hdet
  have hyM : ∀ i, y i ∈ M := by
    intro i
    have h1 : y i ∈ spanS S x := by rw [← hspan]; exact mem_spanS y i
    exact spanS_induction (p := fun v => v ∈ M) M.zero_mem (fun a b => M.add_mem)
      (fun c hc a ha => hM.smul_mem c hc a ha) hx _ h1
  have haS : ∀ i, h (y i) (y i) ∈ S := fun i => hM.int _ (hyM i) _ (hyM i)
  obtain ⟨c, hcS, hcdet⟩ := gram_det_of_le (h := h) hS
    (fun i => by rw [hspan]; exact mem_spanS x i : ∀ i, x i ∈ spanS S y)
  rw [gram_det_orth horth] at hcdet
  have hPd : Dv S π (∏ i, h (y i) (y i)) := by
    rw [← gram_det_orth horth]; exact hall y hyM horth
  have hPn : ¬ Dv S π ((∏ i, h (y i) (y i)) * π⁻¹) := by
    intro hdv
    apply hdet
    rw [hcdet, mul_assoc]
    exact hdv.mul_left hcS
  have hPf : star ((∏ i, h (y i) (y i)) * π⁻¹) = (∏ i, h (y i) (y i)) * π⁻¹ := by
    rw [star_mul', star_inv₀, hπ.fix, ← starRingEnd_apply, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun i _ => hs.eq _ _
  have hPu : IsUnitIn S ((∏ i, h (y i) (y i)) * π⁻¹) := unit_of_not_dv hπ hPd hPf hPn
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, ¬ IsUnitIn S (h (y i₁) (y i₁)) := by
    by_contra hcon
    push Not at hcon
    exact unit_not_dv hπ (LocF.isUnitIn_prod Finset.univ _ fun i _ => hcon i) hPd
  have hd₁ : Dv S π (h (y i₁) (y i₁)) := dv_of_not_unit hπ (haS i₁) (hs.eq _ _) hi₁
  have hQS : ∏ i ∈ Finset.univ.erase i₁, h (y i) (y i) ∈ S := S.prod_mem fun i _ => haS i
  have hsplit : (∏ i, h (y i) (y i)) * π⁻¹ =
      h (y i₁) (y i₁) * π⁻¹ * ∏ i ∈ Finset.univ.erase i₁, h (y i) (y i) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₁)]
    ring
  have hQu : IsUnitIn S (∏ i ∈ Finset.univ.erase i₁, h (y i) (y i)) :=
    isUnitIn_of_mul hd₁ hQS (hsplit ▸ hPu)
  have hzu : IsUnitIn S (h (y i₁) (y i₁) * π⁻¹) :=
    isUnitIn_of_mul hQS hd₁ (by rw [mul_comm, ← hsplit]; exact hPu)
  have hau : ∀ i, i ≠ i₁ → IsUnitIn S (h (y i) (y i)) := by
    intro i hi
    have hmem : i ∈ Finset.univ.erase i₁ := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
    have e := Finset.mul_prod_erase (Finset.univ.erase i₁) (fun i => h (y i) (y i)) hmem
    refine isUnitIn_of_mul (S.prod_mem fun j _ => haS j :
      ∏ j ∈ (Finset.univ.erase i₁).erase i, h (y j) (y j) ∈ S) (haS i) ?_
    rw [mul_comm, e]
    exact hQu
  have hne : ∀ i, h (y i) (y i) ≠ 0 := by
    intro i
    by_cases hi : i = i₁
    · rw [hi]; exact left_ne_zero_of_mul hzu.1
    · exact (hau i hi).1
  have hexp := expand_orth horth hne

  have hprim : ∀ c : K, c • y i₁ ∈ M → c ∈ S := by
    have hy0 : y i₁ ≠ 0 := by
      intro h0
      apply hne i₁
      rw [h0]; simp
    obtain ⟨l, hl0, hl, hdiv⟩ := exists_primitive hS hd hM (Submodule.mem_top : y i₁ ∈ ⊤) hy0
    have hli : l⁻¹ ∈ S := by
      have := hdiv 1 (by rw [one_smul]; exact hyM i₁)
      rwa [one_mul] at this
    have hNl : star l * l ∈ S := by
      have h1 := hall (fun i => (if i = i₁ then l else 1) • y i) (by
        intro i
        by_cases hi : i = i₁
        · simp only [hi, if_true]; exact hl
        · simp only [hi, if_false, one_smul]; exact hyM i) (by
        intro i j hij
        simp only [map_smulₛₗ, LinearMap.smul_apply, horth i j hij, smul_zero])
      rw [gram_det_smul_orth horth] at h1
      have e : (∏ i, star (if i = i₁ then l else 1) * (if i = i₁ then l else 1)) = star l * l := by
        rw [Finset.prod_eq_single i₁]
        · simp
        · intro j _ hj; simp [hj]
        · intro hi; exact absurd (Finset.mem_univ i₁) hi
      rw [e] at h1
      unfold Dv at h1
      have h2 := S.mul_mem h1 hPu.2.2
      have h0 := hPu.1
      have e2 : star l * l * (∏ i, h (y i) (y i)) * π⁻¹ * ((∏ i, h (y i) (y i)) * π⁻¹)⁻¹ =
          star l * l := by
        rw [mul_assoc (star l * l), mul_assoc, mul_inv_cancel₀ h0, mul_one]
      rwa [e2] at h2
    have hlS : l ∈ S := by
      have hu : IsUnitIn S (star l⁻¹ * l⁻¹) := by
        refine ⟨mul_ne_zero (star_ne_zero.mpr (inv_ne_zero hl0)) (inv_ne_zero hl0),
          S.mul_mem (hS.star_mem _ hli) hli, ?_⟩
        rw [star_inv₀, mul_inv, inv_inv, inv_inv]
        exact hNl
      have := (isUnitIn_of_mul (hS.star_mem _ hli) hli hu).2.2
      rwa [inv_inv] at this
    intro c hc
    have := S.mul_mem (hdiv c hc) hlS
    rwa [mul_assoc, inv_mul_cancel₀ hl0, mul_one] at this
  refine ⟨y i₁, hM, hyM i₁, hzu, ?_, ?_⟩
  · intro m hm
    have hcS : ∀ i, i ≠ i₁ → h (y i) m * (h (y i) (y i))⁻¹ ∈ S := fun i hi =>
      S.mul_mem (hM.int _ (hyM i) _ hm) (hau i hi).2.2
    have h1 : (h (y i₁) m * (h (y i₁) (y i₁))⁻¹) • y i₁ ∈ M := by
      have e := Finset.add_sum_erase Finset.univ
        (fun i => (h (y i) m * (h (y i) (y i))⁻¹) • y i) (Finset.mem_univ i₁)
      rw [← hexp m] at e
      rw [eq_sub_of_add_eq e]
      exact M.sub_mem hm (M.sum_mem fun i hi =>
        hM.smul_mem _ (hcS i (Finset.mem_erase.mp hi).1) _ (hyM i))
    have h2 := hd₁.mul_left (hprim _ h1)
    rwa [mul_assoc, inv_mul_cancel₀ (hne i₁), mul_one] at h2
  · intro v _ hzv hv
    rw [hexp v]
    refine M.sum_mem fun i _ => ?_
    by_cases hi : i = i₁
    · rw [hi, hzv, zero_mul, zero_smul]; exact M.zero_mem
    · exact hM.smul_mem _ (S.mul_mem (hv _ (hyM i)) (hau i hi).2.2) _ (hyM i)

end Formalism.HermitianLattices.Ext.L3.U0
end
end

