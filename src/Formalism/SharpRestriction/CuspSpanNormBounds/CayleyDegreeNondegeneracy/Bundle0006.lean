import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0005
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.CardOrbitMulCardStabilizer
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

section Abstract

open MulAction

variable {Γ 𝒳 𝒴 : Type} [Group Γ] [MulAction Γ 𝒳] [MulAction Γ 𝒴]

theorem card_orbit_mul_card_stabilizer (A : Subgroup Γ) (x : 𝒳) (hle : stabilizer Γ x ≤ A) :
    Nat.card (orbit A x) * Nat.card (stabilizer Γ x) = Nat.card A := by
  have h1 : Nat.card (orbit A x) = Nat.card (A ⧸ stabilizer A x) :=
    Nat.card_congr (orbitEquivQuotientStabilizer A x)
  have h2 : stabilizer A x = (stabilizer Γ x).subgroupOf A := by
    ext a
    simp [mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]
  have h3 : Nat.card (stabilizer A x) = Nat.card (stabilizer Γ x) := by
    rw [h2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h1, ← h3, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

theorem card_stabilizer_smul_eq (g : Γ) (y : 𝒳) :
    Nat.card (stabilizer Γ (g • y)) = Nat.card (stabilizer Γ y) :=
  Nat.card_congr (stabilizerEquivStabilizerOfOrbitRel (G := Γ) (a := g • y) (b := y) ⟨g, rfl⟩).toEquiv

theorem sum_fibre_inv_card_stabilizer (m : 𝒳 → 𝒴) (hm : ∀ (γ : Γ) x, m (γ • x) = γ • m x) (R : Set 𝒳)
    (hR : ∀ (γ : Γ), ∀ x ∈ R, γ • x ∈ R) (s : Finset 𝒳) (hsR : ∀ x ∈ s, x ∈ R)
    (hs : ∀ x ∈ R, ∃! y, y ∈ s ∧ ∃ γ : Γ, γ • y = x) (M : 𝒴) (hA : Finite (stabilizer Γ M))
    (hfin : {x | x ∈ R ∧ m x = M}.Finite) [DecidablePred fun y : 𝒳 => ∃ γ : Γ, γ • M = m y] :
    ∑ y ∈ s.filter (fun y => ∃ γ : Γ, γ • M = m y), ((Nat.card (stabilizer Γ y) : ℕ) : ℝ)⁻¹ =
      ({x | x ∈ R ∧ m x = M}.ncard : ℝ) / (Nat.card (stabilizer Γ M) : ℝ) := by
  classical
  let O : 𝒳 → Set 𝒳 := fun y => {x | (x ∈ R ∧ m x = M) ∧ ∃ γ : Γ, γ • y = x}
  have hOfin : ∀ y, (O y).Finite := fun y => hfin.subset fun x hx => hx.1
  have hApos : (0 : ℝ) < (Nat.card (stabilizer Γ M) : ℝ) := by exact_mod_cast Nat.card_pos
  have hcard : ∀ y ∈ s.filter (fun y => ∃ γ : Γ, γ • M = m y),
      (O y).ncard * Nat.card (stabilizer Γ y) = Nat.card (stabilizer Γ M) := by
    intro y hy
    obtain ⟨hys, γ0, hγ0⟩ := Finset.mem_filter.1 hy
    have hmx : m (γ0⁻¹ • y) = M := by rw [hm, ← hγ0, inv_smul_smul]
    have hle : stabilizer Γ (γ0⁻¹ • y) ≤ stabilizer Γ M := by
      intro γ hγ
      rw [mem_stabilizer_iff] at hγ ⊢
      rw [← hmx, ← hm, hγ]
    have hO : O y = orbit (stabilizer Γ M) (γ0⁻¹ • y) := by
      ext x
      constructor
      · rintro ⟨⟨_, hxM⟩, γ, rfl⟩
        refine ⟨⟨γ * γ0, ?_⟩, ?_⟩
        · rw [mem_stabilizer_iff, mul_smul, hγ0, ← hm, hxM]
        · change (γ * γ0) • γ0⁻¹ • y = γ • y
          rw [mul_smul, smul_inv_smul]
      · rintro ⟨⟨a, ha⟩, rfl⟩
        rw [mem_stabilizer_iff] at ha
        refine ⟨⟨hR a _ (hR _ _ (hsR y hys)), ?_⟩, a * γ0⁻¹, ?_⟩
        · change m (a • γ0⁻¹ • y) = M
          rw [hm, hmx, ha]
        · change (a * γ0⁻¹) • y = a • γ0⁻¹ • y
          rw [mul_smul]
    rw [hO, ← card_stabilizer_smul_eq γ0⁻¹ y, ← Nat.card_coe_set_eq]
    exact card_orbit_mul_card_stabilizer _ _ hle
  have hpart : {x | x ∈ R ∧ m x = M}.ncard = ∑ y ∈ s.filter (fun y => ∃ γ : Γ, γ • M = m y), (O y).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    have hU : hfin.toFinset = (s.filter (fun y => ∃ γ : Γ, γ • M = m y)).biUnion fun y => (hOfin y).toFinset := by
      ext x
      simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hx
        obtain ⟨y, ⟨hy, γ, hγ⟩, _⟩ := hs x hx.1
        refine ⟨y, ⟨hy, γ⁻¹, ?_⟩, hx, γ, hγ⟩
        rw [← hx.2, ← hγ, hm, inv_smul_smul]
      · rintro ⟨y, _, hx, _⟩
        exact hx
    rw [hU, Finset.card_biUnion]
    · exact Finset.sum_congr rfl fun y _ => (Set.ncard_eq_toFinset_card _ (hOfin y)).symm
    · intro y hy y' hy' hne
      rw [Function.onFun, Finset.disjoint_left]
      rw [Finset.mem_coe] at hy hy'
      intro x hx hx'
      rw [Set.Finite.mem_toFinset] at hx hx'
      obtain ⟨y0, _, huniq⟩ := hs x hx.1.1
      exact hne ((huniq y ⟨(Finset.mem_filter.1 hy).1, hx.2⟩).trans
        (huniq y' ⟨(Finset.mem_filter.1 hy').1, hx'.2⟩).symm)
  rw [hpart, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h := hcard y hy
  have h' : ((O y).ncard : ℝ) * (Nat.card (stabilizer Γ y) : ℝ) = (Nat.card (stabilizer Γ M) : ℝ) := by
    exact_mod_cast h
  have hs0 : (Nat.card (stabilizer Γ y) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h'
    exact hApos.ne h'
  rw [← h']
  have hO0 : ((O y).ncard : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h'
    exact hApos.ne h'
  field_simp

end Abstract

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfPositions
section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem c3eqv_mem_orth (U : Submodule E S.V) (x : S.V) : x ∈ orth S U ↔ ∀ v ∈ U, S.hT v x = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem c3eqv_gmap_iff (n : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap n Λ = Λ ↔ (∀ y ∈ Λ, n y ∈ Λ) ∧ ∀ y ∈ Λ, n.symm y ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rw [← h]
      exact ⟨y, hy, rfl⟩
    · rw [← h] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simpa using hz
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact h1 z hz
    · intro y hy
      exact ⟨n.symm y, h2 y hy, by simp⟩

theorem c3eqv_symm_mem (n : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) (h : ∀ x ∈ U, n x ∈ U) :
    ∀ x ∈ U, n.symm x ∈ U := by
  have hle : U.map (n : S.V →ₗ[E] S.V) ≤ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : U.map (n : S.V →ₗ[E] S.V) = U :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n U)
  intro x hx
  have hx' : x ∈ U.map (n : S.V →ₗ[E] S.V) := heq.symm ▸ hx
  obtain ⟨y, hy, rfl⟩ := hx'
  simpa using hy

theorem c3eqv_isom_symm {n : S.V ≃ₗ[E] S.V} (h : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) : n.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  have hiso : ∀ x y, S.hT (n x) (n y) = S.hT x y := h
  show ∀ x y, S.hT (n.symm x) (n.symm y) = S.hT x y
  intro x y
  have := hiso (n.symm x) (n.symm y)
  simp only [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem c3eqv_isom_trans {n m : S.V ≃ₗ[E] S.V} (h : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (h' : m ∈ Formalism.HermitianLatticesTheory.isom S.hT) :
    n.trans m ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  have hiso : ∀ x y, S.hT (n x) (n y) = S.hT x y := h
  have hiso' : ∀ x y, S.hT (m x) (m y) = S.hT x y := h'
  show ∀ x y, S.hT ((n.trans m) x) ((n.trans m) y) = S.hT x y
  intro x y
  simp only [LinearEquiv.trans_apply, hiso', hiso]

theorem c3eqv_orth_map {n : S.V ≃ₗ[E] S.V} (h : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (U₁ U₂ : Submodule E S.V)
    (hU : ∀ v ∈ U₂, n.symm v ∈ U₁) {x : S.V} (hx : x ∈ orth S U₁) : n x ∈ orth S U₂ := by
  rw [c3eqv_mem_orth] at hx ⊢
  intro v hv
  have hiso : ∀ x y, S.hT (n x) (n y) = S.hT x y := h
  have := hiso (n.symm v) x
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this]
  exact hx _ (hU v hv)

variable {T : E} (F : LFlag S r T)

theorem c3eqv_Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  unfold Xflag Formalism.MainNotions.S.FlagG.Xa
  exact Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < j) => Nat.lt_succ_of_lt hi)

theorem c3eqv_Xflag_zero : Xflag F 0 = ⊥ := by
  unfold Xflag Formalism.MainNotions.S.FlagG.Xa
  simp

theorem c3eqv_Xsp_eq : Xsp F = Xflag F r := by
  unfold Xsp Xflag Formalism.MainNotions.S.FlagG.X Formalism.MainNotions.S.FlagG.Xa
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq, Fin.is_lt, true_and]

variable {F} {Λ : Submodule (𝓞 E) S.V}

theorem c3eqv_N_flag {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (j : ℕ) : ∀ x ∈ Xflag F j, n x ∈ Xflag F j := by
  unfold NLam at hn
  simp only [Set.mem_setOf_eq] at hn
  obtain ⟨_, h1, _⟩ := hn
  intro x hx
  cases j with
  | zero =>
    rw [c3eqv_Xflag_zero] at hx ⊢
    rw [(Submodule.mem_bot E).1 hx, map_zero]
    exact Submodule.zero_mem _
  | succ j =>
    have h2 := c3eqv_Xflag_mono F j (h1 j x hx)
    have e : n x = (n x - x) + x := by abel
    rw [e]
    exact Submodule.add_mem _ h2 hx

theorem c3eqv_N_X {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : ∀ x ∈ Xsp F, n x ∈ Xsp F := by
  rw [c3eqv_Xsp_eq]
  exact c3eqv_N_flag hn r

theorem c3eqv_N_orth {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : ∀ x ∈ orth S (Xsp F), n x ∈ orth S (Xsp F) := by
  have hX := c3eqv_N_X hn
  have h' := hn
  unfold NLam at h'
  simp only [Set.mem_setOf_eq] at h'
  unfold IsAutLam at h'
  exact fun x hx => c3eqv_orth_map h'.1.1 _ _ (c3eqv_symm_mem n _ hX) hx

theorem c3eqv_NLam_trans {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F) : n.trans m ∈ NLam Λ F := by
  have hnf := c3eqv_N_flag hn
  have hno := c3eqv_N_orth hn
  have hn' := hn
  have hm' := hm
  unfold NLam at hn' hm' ⊢
  simp only [Set.mem_setOf_eq] at hn' hm' ⊢
  unfold IsAutLam at hn' hm' ⊢
  obtain ⟨⟨hni, hng⟩, hn1, hn2⟩ := hn'
  obtain ⟨⟨hmi, hmg⟩, hm1, hm2⟩ := hm'
  refine ⟨⟨c3eqv_isom_trans hni hmi, ?_⟩, ?_, ?_⟩
  · rw [c3eqv_gmap_iff] at hng hmg ⊢
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · simp only [LinearEquiv.trans_apply]
      exact hmg.1 _ (hng.1 _ hy)
    · simp only [LinearEquiv.symm_trans_apply]
      exact hng.2 _ (hmg.2 _ hy)
  · intro j x hx
    have e : (n.trans m) x - x = (m (n x) - n x) + (n x - x) := by
      simp only [LinearEquiv.trans_apply]; abel
    rw [e]
    exact Submodule.add_mem _ (hm1 j _ (hnf (j + 1) x hx)) (hn1 j x hx)
  · intro x hx
    have e : (n.trans m) x - x = (m (n x) - n x) + (n x - x) := by
      simp only [LinearEquiv.trans_apply]; abel
    rw [e]
    exact Submodule.add_mem _ (hm2 _ (hno x hx)) (hn2 x hx)

theorem c3eqv_NLam_symm {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : n.symm ∈ NLam Λ F := by
  have hnf := c3eqv_N_flag hn
  have hno := c3eqv_N_orth hn
  have hn' := hn
  unfold NLam at hn' ⊢
  simp only [Set.mem_setOf_eq] at hn' ⊢
  unfold IsAutLam at hn' ⊢
  obtain ⟨⟨hni, hng⟩, hn1, hn2⟩ := hn'
  refine ⟨⟨c3eqv_isom_symm hni, ?_⟩, ?_, ?_⟩
  · rw [c3eqv_gmap_iff] at hng ⊢
    rw [LinearEquiv.symm_symm]
    exact ⟨hng.2, hng.1⟩
  · intro j x hx
    have hy := c3eqv_symm_mem n _ (hnf (j + 1)) x hx
    have e : n.symm x - x = -(n (n.symm x) - n.symm x) := by
      rw [LinearEquiv.apply_symm_apply]; abel
    rw [e]
    exact Submodule.neg_mem _ (hn1 j _ hy)
  · intro x hx
    have hy := c3eqv_symm_mem n _ hno x hx
    have e : n.symm x - x = -(n (n.symm x) - n.symm x) := by
      rw [LinearEquiv.apply_symm_apply]; abel
    rw [e]
    exact Submodule.neg_mem _ (hn2 _ hy)

def isUnitriangularIntegral {N : ℕ} (ξ : Matrix (Fin N) (Fin N) (𝓞 E)) : Prop :=
  (∀ a b, b < a → ξ a b = 0) ∧ ∀ a, ξ a a = 1

end Gen

section D7

variable (D : D7)

variable (Λ : LatV D) {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T)

end D7

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MemSupIsotropicOfDualPairing
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section One

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem star_mem_one_submodule {t : E} (h : t ∈ (1 : Submodule (𝓞 E) E)) : star t ∈ (1 : Submodule (𝓞 E) E) := by
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 h
  obtain ⟨o', ho'⟩ := i_star_int o
  exact Submodule.mem_one.2 ⟨o', ho'⟩

theorem mul_mem_one_submodule {s t : E} (hs : s ∈ (1 : Submodule (𝓞 E) E)) (h : t ∈ (1 : Submodule (𝓞 E) E)) :
    s * t ∈ (1 : Submodule (𝓞 E) E) := by
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hs
  obtain ⟨o', rfl⟩ := Submodule.mem_one.1 h
  exact Submodule.mem_one.2 ⟨o * o', by simp⟩

end One

section Lat

variable {D : D7} {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u) (Λ : LatV D)

theorem isotropic_le_orth_self : Xsp (lf D F0) ≤ orth (hS D) (Xsp (lf D F0)) :=
  fun _ hx => c_mem_orth.2 fun _ hv => p_X_iso (lf D F0) hv hx

theorem mem_Lsub_iff_sup_and_orth {v : (hS D).V} : v ∈ Lsub Λ (lf D F0) ↔
    v ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) ∧ v ∈ orth (hS D) (Xsp (lf D F0)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hle : Lrep Λ (lf D F0) ⊔ toO (hS D) (Xsp (lf D F0)) ≤ Λ ⊔ toO (hS D) (Xsp (lf D F0)) :=
      sup_le_sup_right (inf_le_left : Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))) ≤ Λ) _
    exact ⟨hle h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 h1
    refine Submodule.mem_sup.2 ⟨l, ⟨hl, ?_⟩, ξ, hξ, e⟩
    have : l = v - ξ := by rw [← e]; abel
    rw [this]
    exact (orth (hS D) (Xsp (lf D F0))).sub_mem h2 (isotropic_le_orth_self F0 hξ)

include he hz in
theorem orth_embedding_mem_orth_isotropic (x : (D.sp.X 0).V) : D.sp.iXY 0 x ∈ orth (hS D) (Xsp (lf D F0)) :=
  c_orth_anti (le_sup_left : Xsp (lf D F0) ≤ Xplus (lf D F0)) (orth_embedding_mem_orth_plus F0 he hz x)

include he hz in
theorem inner_z_orth_embedding_eq_zero (x : (D.sp.X 0).V) : (hS D).hT F0.z (D.sp.iXY 0 x) = 0 :=
  c_mem_orth.1 (orth_embedding_mem_orth_plus F0 he hz x) F0.z
    ((le_sup_right : _ ≤ Xplus (lf D F0)) (Submodule.mem_span_singleton_self _))

include he hz in

theorem mem_orthLattice_iff_image_mem_sup {x : (D.sp.X 0).V} :
    x ∈ L0X D Λ (lf D F0) ↔ D.sp.iXY 0 x ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) := by
  rw [mem_orthLattice_iff_mem_sub]
  constructor
  · intro h
    exact ((mem_Lsub_iff_sup_and_orth F0 Λ).1 h.1).1
  · intro h
    exact ⟨(mem_Lsub_iff_sup_and_orth F0 Λ).2 ⟨h, orth_embedding_mem_orth_isotropic F0 he hz x⟩, inner_z_orth_embedding_eq_zero F0 he hz x⟩

include he hz in
theorem exists_smul_mem_orthLattice (hΛ : Submodule.IsLattice D.host.E Λ) (x : (D.sp.X 0).V) :
    ∃ c : 𝓞 D.host.E, c ≠ 0 ∧ c • x ∈ L0X D Λ (lf D F0) := by
  obtain ⟨c, hc, hcx⟩ := a_exists_smul_mem Λ hΛ (D.sp.iXY 0 x)
  refine ⟨c, hc, (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_⟩
  rw [LinearMap.map_smul_of_tower]
  exact Submodule.mem_sup_left hcx

include he hz in

theorem orthLattice_isLattice (hΛ : Submodule.IsLattice D.host.E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) :
    Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)) := by
  choose c hc hcM using fun i => exists_smul_mem_orthLattice F0 he hz Λ hΛ ((D.sp.X 0).frame i)
  set M₁ : Submodule (𝓞 D.host.E) (D.sp.X 0).V :=
    Submodule.span (𝓞 D.host.E) (Set.range fun i => c i • (D.sp.X 0).frame i) with hM₁def
  have hM₁ : M₁ ≤ L0X D Λ (lf D F0) := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hcM i)
  have hfg : M₁.FG := Submodule.fg_span (Set.finite_range _)
  have hs : spanE (D.sp.X 0) M₁ = ⊤ := by
    rw [eq_top_iff, ← (D.sp.X 0).frame.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hc1 : algebraMap (𝓞 D.host.E) D.host.E (c i) ≠ 0 := by simpa using hc i
    have h2 : (algebraMap (𝓞 D.host.E) D.host.E (c i))⁻¹ • (c i • (D.sp.X 0).frame i) = (D.sp.X 0).frame i := by
      rw [← algebraMap_smul D.host.E (c i), smul_smul, inv_mul_cancel₀ hc1, one_smul]
    rw [← h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
  have hU : (⊤ : Submodule D.host.E (D.sp.X 0).V) ⊓ orth (D.sp.X 0) ⊤ = ⊥ := by
    rw [top_inf_eq, eq_bot_iff]
    intro y hy
    exact (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 y fun x => c_mem_orth.1 hy x trivial)
  obtain ⟨hdfg, -, -⟩ := g_dual_facts g_starInt hU hfg hs
  have hle : L0X D Λ (lf D F0) ≤ dualIn (D.sp.X 0) M₁ := by
    intro x hx
    refine g_mem_dualIn.2 ⟨fun y hy => ?_, by rw [hs]; trivial⟩
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu y (hM₁ hy) x hx)
    exact ⟨o, ho⟩
  refine ⟨?_, ?_⟩
  · exact isNoetherian_submodule.1 (isNoetherian_of_fg_of_noetherian _ hdfg) _ hle
  · exact eq_top_iff.2 (hs ▸ Submodule.span_mono hM₁)

include he in

theorem mem_sup_isotropic_of_dual_pairing (hΛ : Submodule.IsLattice D.host.E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ)
    (y : (hS D).V)
    (hy : ∀ m ∈ Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))), (hS D).hT m y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) :
    y ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) := by
  have DL := Formalism.HermitianLatticesTheory.dualLattice (𝓞 D.host.E) D.host.E (hS D).V (hS D).hT (hS D).herm (hS D).nondeg i_star_int
  have hlat : ∀ N : LatV D, N.FG → Submodule.IsLattice D.host.E (Λ ⊔ N) := fun N hN =>
    ⟨hΛ.fg.sup hN, eq_top_iff.2 (hΛ.span_eq_top ▸ Submodule.span_mono (le_sup_left : Λ ≤ Λ ⊔ N))⟩
  have hΛ₂ := (DL _ (hlat (Submodule.span (𝓞 D.host.E) {y}) (Submodule.fg_span (Set.finite_singleton y)))).1
  choose c hc hcf using fun a => a_exists_smul_mem _ hΛ₂ (D.sp.hypF a)
  set ε : 𝓞 D.host.E := ∏ a, c a with hε
  have hε0 : ε ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hε1 : algebraMap (𝓞 D.host.E) D.host.E ε ≠ 0 := by simpa using hε0
  have hg : ∀ a, ε • D.sp.hypF a ∈
      Formalism.HermitianLatticesTheory.dual (hS D).hT (Λ ⊔ Submodule.span (𝓞 D.host.E) {y}) := by
    intro a
    rw [hε, ← Finset.prod_erase_mul _ _ (Finset.mem_univ a), mul_smul]
    exact Submodule.smul_mem _ _ (hcf a)
  have hgΛ : ∀ a, ε • D.sp.hypF a ∈ Λ := by
    intro a
    rw [← hu]
    exact (i_mem_dual _ _).2 fun l hl => (i_mem_dual _ _).1 (hg a) l (Submodule.mem_sup_left hl)
  have hgy : ∀ a, (hS D).hT (ε • D.sp.hypF a) y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro a
    rw [← c_herm]
    exact star_mem_one_submodule ((i_mem_dual _ _).1 (hg a) y
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)))
  set δ : D.host.E := (star (algebraMap (𝓞 D.host.E) D.host.E ε))⁻¹ with hδ
  set N : LatV D := Submodule.span (𝓞 D.host.E) (Set.range fun a => δ • D.sp.hypE a) with hN
  have hB := (DL _ (hlat N (Submodule.fg_span (Set.finite_range _)))).2.1
  have hyB : y ∈ Λ ⊔ N := by
    rw [← hB]
    refine (i_mem_dual _ _).2 fun l hl => ?_
    have hlΛ : l ∈ Λ := by
      rw [← hu]
      exact (i_mem_dual _ _).2 fun l' hl' => (i_mem_dual _ _).1 hl l' (Submodule.mem_sup_left hl')
    have ho : ∀ a, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o =
        (algebraMap (𝓞 D.host.E) D.host.E ε)⁻¹ * (hS D).hT (D.sp.hypE a) l := by
      intro a
      have h1 := (i_mem_dual _ _).1 hl (δ • D.sp.hypE a)
        (Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩))
      rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hδ, star_inv₀, star_star] at h1
      exact Submodule.mem_one.1 h1
    choose o ho using ho
    set l' : (hS D).V := ∑ a, o a • (ε • D.sp.hypF a) with hl'
    have hl'Λ : l' ∈ Λ := Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hgΛ a)
    have hm : l - l' ∈ Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))) := by
      refine ⟨Λ.sub_mem hlΛ hl'Λ, ?_⟩
      show l - l' ∈ orth (hS D) (Submodule.span D.host.E (Set.range F0.e))
      rw [he]
      refine a_orth_of_frame _ _ fun b => ?_
      rw [map_sub, hl', map_sum, sub_eq_zero]
      have : ∀ a, (hS D).hT (D.sp.hypE b) (o a • (ε • D.sp.hypF a)) =
          if b = a then algebraMap (𝓞 D.host.E) D.host.E (o a) * algebraMap (𝓞 D.host.E) D.host.E ε else 0 := by
        intro a
        rw [← algebraMap_smul D.host.E (o a), ← algebraMap_smul D.host.E ε, map_smul, map_smul, D.sp.hyp_ef]
        split_ifs <;> simp
      simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [ho b]
      field_simp
    have e : l = (l - l') + l' := by abel
    rw [e, map_add, LinearMap.add_apply]
    refine Submodule.add_mem _ (hy _ hm) ?_
    rw [hl', map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [← algebraMap_smul D.host.E (o a), map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
    exact mul_mem_one_submodule (star_mem_one_submodule (Submodule.mem_one.2 ⟨o a, rfl⟩)) (hgy a)
  have hNX : N ≤ toO (hS D) (Xsp (lf D F0)) := ?_
  · exact (sup_le_sup_left hNX Λ) hyB
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  show δ • D.sp.hypE a ∈ Submodule.span D.host.E (Set.range F0.e)
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Lat

end Formalism.MainNotions.BridgeLemma₂

end
end

