import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0004
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0002
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0042

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.HighestWeightModuleBounds
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_mem_weightSp (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

theorem v2rep_comm (E : GLOps n K V) (hR : SatisfiesGLRelations E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have h := congrArg (fun f : Module.End K V => f x) (hR a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [sub_eq_iff_eq_add'] at h
  rw [h]
  congr 1
  split_ifs <;> simp

theorem v2rep_shift (E : GLOps n K V) (hR : SatisfiesGLRelations E) (a b : Fin n) (ν : Fin n → ℤ) (x : V)
    (hx : x ∈ weightSp E ν) : E a b x ∈ weightSp E (ν + rootW a b) := by
  rw [v2rep_mem_weightSp] at hx ⊢
  intro c
  rw [v2rep_comm E hR c c a b x, hx c, map_smul]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb
    simp [rootW]
  · subst hca
    simp [rootW, hcb, Ne.symm hcb]
    module
  · subst hcb
    simp [rootW, hca]
    module
  · simp [rootW, hca, hcb, Ne.symm hcb]

def cyclicLevelSubmodule (E : GLOps n K V) (v : V) : ℕ → Submodule K V
  | 0 => Submodule.span K {v}
  | k + 1 => cyclicLevelSubmodule E v k ⊔ ⨆ ab : Fin n × Fin n, ⨆ (_ : ab.2 < ab.1), (cyclicLevelSubmodule E v k).map (E ab.1 ab.2)

theorem v2rep_Y_le (E : GLOps n K V) (v : V) (k : ℕ) : cyclicLevelSubmodule E v k ≤ cyclicLevelSubmodule E v (k + 1) := by
  exact le_sup_left

theorem v2rep_Y_low (E : GLOps n K V) (v : V) (k : ℕ) (a b : Fin n) (h : b < a) (x : V) (hx : x ∈ cyclicLevelSubmodule E v k) :
    E a b x ∈ cyclicLevelSubmodule E v (k + 1) := by
  show E a b x ∈ cyclicLevelSubmodule E v k ⊔ _
  refine Submodule.mem_sup_right ?_
  refine Submodule.mem_iSup_of_mem (a, b) ?_
  refine Submodule.mem_iSup_of_mem h ?_
  exact Submodule.mem_map_of_mem hx

theorem v2rep_Y_up (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) (k : ℕ) :
    ∀ c d : Fin n, c ≤ d → ∀ x ∈ cyclicLevelSubmodule E v k, E c d x ∈ cyclicLevelSubmodule E v k := by
  induction k with
  | zero =>
    intro c d hcd x hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    rcases hcd.lt_or_eq with hlt | heq
    · rw [hv.2.2 c d hlt]
      exact Submodule.zero_mem _
    · subst heq
      rw [(v2rep_mem_weightSp E mu v).1 hv.2.1 c]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  | succ k ih =>
    have hany : ∀ p q : Fin n, ∀ y ∈ cyclicLevelSubmodule E v k, E p q y ∈ cyclicLevelSubmodule E v (k + 1) := by
      intro p q y hy
      rcases lt_or_ge q p with hqp | hpq
      · exact v2rep_Y_low E v k p q hqp y hy
      · exact v2rep_Y_le E v k (ih p q hpq y hy)
    intro c d hcd
    suffices hs : cyclicLevelSubmodule E v (k + 1) ≤ (cyclicLevelSubmodule E v (k + 1)).comap (E c d) from fun x hx => hs hx
    refine sup_le (fun y hy => v2rep_Y_le E v k (ih c d hcd y hy)) ?_
    refine iSup_le fun ab => iSup_le fun hab => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, Submodule.mem_comap, v2rep_comm E hR c d ab.1 ab.2 y]
    refine Submodule.add_mem _ (v2rep_Y_low E v k ab.1 ab.2 hab _ (ih c d hcd y hy)) ?_
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact hany c ab.2 y hy
      · exact Submodule.zero_mem _
    · split_ifs
      · exact hany ab.1 d y hy
      · exact Submodule.zero_mem _

theorem v2rep_Y_all (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) (k : ℕ)
    (a b : Fin n) (y : V) (hy : y ∈ cyclicLevelSubmodule E v k) : E a b y ∈ cyclicLevelSubmodule E v (k + 1) := by
  rcases lt_or_ge b a with hba | hab
  · exact v2rep_Y_low E v k a b hba y hy
  · exact v2rep_Y_le E v k (v2rep_Y_up E hR mu v hv k a b hab y hy)

theorem v2rep_Umon_Y (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v)
    (u : Module.End K V) (hu : u ∈ Umon E) : ∀ k, ∀ x ∈ cyclicLevelSubmodule E v k, ∃ k', u x ∈ cyclicLevelSubmodule E v k' := by
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    obtain ⟨ab, rfl⟩ := hu
    intro k x hx
    exact ⟨k + 1, v2rep_Y_all E hR mu v hv k ab.1 ab.2 x hx⟩
  | one =>
    intro k x hx
    exact ⟨k, hx⟩
  | mul u₁ u₂ _ _ h₁ h₂ =>
    intro k x hx
    obtain ⟨k₂, hk₂⟩ := h₂ k x hx
    obtain ⟨k₁, hk₁⟩ := h₁ k₂ _ hk₂
    exact ⟨k₁, hk₁⟩

def dominantWeightSubmodule [NeZero n] (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  ⨆ ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}, weightSp E ν

theorem v2rep_Good_low [NeZero n] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (a b : Fin n) (h : b < a) :
    dominantWeightSubmodule E mu ≤ (dominantWeightSubmodule E mu).comap (E a b) := by
  refine iSup₂_le fun ν hν => ?_
  intro x hx
  rw [Submodule.mem_comap]
  have hs := v2rep_shift E hR a b ν x hx
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at h
    exact absurd h (Fin.not_lt_zero b)
  have hbl : b ≠ lastIdx n := by
    intro hb
    have : (a : ℕ) ≤ n - 1 := Nat.le_sub_one_of_lt a.2
    have h2 : (b : ℕ) < a := h
    rw [hb] at h2
    simp [lastIdx] at h2
    omega
  refine (le_iSup₂ (f := fun ν (_ : ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}) =>
    weightSp E ν) (ν + rootW a b) ?_) hs
  obtain ⟨h1, h2⟩ := hν
  refine ⟨?_, ?_⟩
  · simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply, Ne.symm hbl, if_false, sub_zero]
    split_ifs <;> omega
  · simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply, Ne.symm ha0, if_false, zero_sub]
    split_ifs <;> omega

theorem v2rep_Y_Good [NeZero n] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v)
    (k : ℕ) : cyclicLevelSubmodule E v k ≤ dominantWeightSubmodule E mu := by
  induction k with
  | zero =>
    refine (Submodule.span_singleton_le_iff_mem _ _).2 ?_
    exact (le_iSup₂ (f := fun ν (_ : ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}) =>
      weightSp E ν) mu ⟨le_rfl, le_rfl⟩) hv.2.1
  | succ k ih =>
    refine sup_le ih (iSup_le fun ab => iSup_le fun hab => ?_)
    rw [Submodule.map_le_iff_le_comap]
    exact ih.trans (v2rep_Good_low E hR mu ab.1 ab.2 hab)

theorem highest_weight_module_bounds : HighestWeightModuleWeightBounds := by
  intro K V _ _ _ _ n _ E hR mu v hv u hu
  obtain ⟨k, hk⟩ := v2rep_Umon_Y E hR mu v hv u hu 0 v (Submodule.mem_span_singleton_self v)
  exact v2rep_Y_Good E hR mu v hv k hk

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralEnvelopingPreservesStable
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem dvr_fraction_field_charZero {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  haveI hc := ringChar.charP O
  have hO : CharZero O := by
    rcases CharP.char_is_prime_or_zero O (ringChar O) with hq | hq
    · exfalso
      by_cases hpq : p = ringChar O
      · apply S.p_ne
        rw [hpq]
        exact CharP.cast_eq_zero O (ringChar O)
      · have hcop : Nat.Coprime p (ringChar O) := (Nat.coprime_primes hp hq).mpr hpq
        have h := Nat.gcd_eq_gcd_ab p (ringChar O)
        rw [hcop.gcd_eq_one] at h
        have h' := congrArg (Int.cast : ℤ → O) h
        push_cast at h'
        rw [CharP.cast_eq_zero O (ringChar O), zero_mul, add_zero] at h'
        exact (IsLocalRing.mem_maximalIdeal _).mp S.p_mem (IsUnit.of_mul_eq_one _ h'.symm)
    · rw [hq] at hc
      exact CharP.charP_to_charZero O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pow_preserves_stable (f : Module.End K V) (W : Submodule K V) (hf : ∀ x ∈ W, f x ∈ W) (k : ℕ) :
    ∀ x ∈ W, (f ^ k) x ∈ W := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hf _ ih

theorem list_prod_preserves_stable (l : List (Module.End K V)) (W : Submodule K V) (hl : ∀ f ∈ l, ∀ x ∈ W, f x ∈ W) :
    ∀ x ∈ W, l.prod x ∈ W := by
  revert hl
  induction l with
  | nil =>
    intro _ x hx
    simpa using hx
  | cons f l ih =>
    intro hl x hx
    rw [List.prod_cons, Module.End.mul_apply]
    exact hl f (List.mem_cons.mpr (Or.inl rfl)) _
      (ih (fun g hg => hl g (List.mem_cons.mpr (Or.inr hg))) x hx)

theorem integral_enveloping_preserves_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ x ∈ W, E a b x ∈ W) :
    ∀ u ∈ UZmon E, ∀ x ∈ W, u x ∈ W := by
  intro u hu
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    rcases hu with ⟨a, b, k, -, rfl⟩ | ⟨a, k, rfl⟩
    · intro x hx
      simp only [divPowE, LinearMap.smul_apply]
      exact W.smul_mem _ (pow_preserves_stable _ W (hW a b) k x hx)
    · intro x hx
      simp only [binomE, LinearMap.smul_apply]
      refine W.smul_mem _ (list_prod_preserves_stable _ W ?_ x hx)
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨j, -, rfl⟩ := hf
      intro y hy
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact W.sub_mem (hW a a y hy) (W.smul_mem _ hy)
  | one =>
    intro x hx
    simpa using hx
  | mul u v _ _ hu hv =>
    intro x hx
    rw [Module.End.mul_apply]
    exact hu _ (hv _ hx)

theorem generated_subrep_operator_stable (E : GLOps n K V) (h : V) : ∀ a b, ∀ x ∈ generatedSubrep E h, E a b x ∈ generatedSubrep E h := by
  intro a b x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact Submodule.subset_span
      ⟨E a b * u, Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

theorem isHWV_mem_highestWeightSpace (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) (hv : IsHWV E lam v) : v ∈ highestWeightVectors E lam := by
  refine Submodule.mem_inf.mpr ⟨hv.2.1, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  exact fun a b hab => hv.2.2 a b hab

theorem highestWeight_mem_weightSpace (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) (hv : v ∈ highestWeightVectors E lam) : v ∈ weightSp E lam :=
  (Submodule.mem_inf.mp hv).1

theorem weight_projection_generated_scalar (E : GLOps n K V) (lam : Fin n → ℤ) (π : Module.End K V) (hπ : IsWtProj E lam π) (h : V)
    (hh : h ∈ highestWeightVectors E lam)
    (hB : generatedSubrep E h ≤ Submodule.span K {h} ⊔
      ⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h))
    (y : V) (hy : y ∈ generatedSubrep E h) : ∃ a : K, π y = a • h := by
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp (hB hy)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
  have hker : (⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)) ≤ LinearMap.ker π := by
    refine iSup₂_le fun mu hmu => ?_
    intro z hz
    exact hπ.2 mu hmu z (Submodule.mem_inf.mp hz).1
  refine ⟨a, ?_⟩
  rw [map_add, LinearMap.mem_ker.mp (hker ht), add_zero, map_smul, hπ.1 h (highestWeight_mem_weightSpace E lam h hh)]

theorem isotypic_sum_generated_subreps (E : GLOps n K V) (lam : Fin n → ℤ) {k : ℕ} (h : Fin k → V)
    (hspan : highestWeightVectors E lam ≤ Submodule.span K (Set.range h)) (Y : V) (hY : Y ∈ isoSub E lam) :
    ∃ y : Fin k → V, (∀ j, y j ∈ generatedSubrep E (h j)) ∧ Y = ∑ j, y j := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hspan (isHWV_mem_highestWeightSpace E lam v hv))
    refine ⟨fun j => c j • u (h j), fun j => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, hu, rfl⟩), ?_⟩
    rw [← hc, map_sum]
    simp only [map_smul]
  | zero => exact ⟨0, fun j => Submodule.zero_mem _, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hz
    exact ⟨y + y', fun j => Submodule.add_mem _ (hy j) (hy' j), by simp [Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨a • y, fun j => Submodule.smul_mem _ a (hy j), by simp [Finset.smul_sum]⟩

end

theorem isotypic_lattice_of_five_parts (D : Formalism.BasicNotions.D7) (hA : IsotypicProjectorFixedMem) (hB : GeneratedMultipleOfHWV) (hC1 : DualLatticeDivisibility) (hC2 : LatticeSubspaceBasis) (hD : GeneratedLatticeCorollary) :
    TranslateCorollaryField D := by
  intro p n' O _ _ _ S hG n _ V _ _ _ _ _ E hE M hM hMQ lam hlam e he π hπ c Y _ heY hyp
  have := dvr_fraction_field_charZero S hG.prime
  have hp0 : (p : KK O) ≠ 0 := by exact_mod_cast hG.prime.ne_zero
  have hpc : (p : KK O) ^ c ≠ 0 := zpow_ne_zero _ hp0
  have hYiso : Y ∈ isoSub E lam := hA (KK O) V n E hE lam e he Y heY
  obtain ⟨k, h, hh, hli, hspan, hint⟩ := hC2 O V M hM.2 hMQ (highestWeightVectors E lam)
  obtain ⟨y, hy, hYsum⟩ := isotypic_sum_generated_subreps E lam h hspan Y hYiso
  have hkey : ∀ j, ∀ u ∈ UZmon E, ∃ o : O, π (u (y j)) = ((p : KK O) ^ c * algebraMap O (KK O) o) • h j := by
    intro j0 u hu
    have hex : ∀ j, ∃ a : KK O, π (u (y j)) = a • h j := fun j =>
      weight_projection_generated_scalar E lam π hπ (h j) (hh j).2 (hB (KK O) V n E hE lam (h j) (hh j).2) _
        (integral_enveloping_preserves_stable E _ (generated_subrep_operator_stable E (h j)) u hu _ (hy j))
    choose a ha using hex
    have hz : π (u Y) = ∑ j, a j • h j := by
      rw [hYsum, map_sum, map_sum]
      exact Finset.sum_congr rfl fun j _ => ha j
    obtain ⟨m, hmM, hm⟩ := hC1 O V M hM.2 hMQ ((p : KK O) ^ c) (π (u Y)) (hyp u hu)
    have hzHW : π (u Y) ∈ highestWeightVectors E lam := by
      rw [hz]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hh j).2
    have hmHW : m ∈ highestWeightVectors E lam := by
      have : m = ((p : KK O) ^ c)⁻¹ • π (u Y) := by rw [hm, smul_smul, inv_mul_cancel₀ hpc, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hzHW
    obtain ⟨o, ho⟩ := hint m hmM hmHW
    refine ⟨o j0, ?_⟩
    have hsum : ∑ j, (a j - (p : KK O) ^ c * algebraMap O (KK O) (o j)) • h j = 0 := by
      have h1 : ∑ j, ((p : KK O) ^ c * algebraMap O (KK O) (o j)) • h j = π (u Y) := by
        rw [hm, ho, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_smul, algebraMap_smul]
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [h1, hz, sub_self]
    have := Fintype.linearIndependent_iff.1 hli _ hsum j0
    rw [ha j0, sub_eq_zero.1 this]
  have hfin : ∀ j, ∃ m ∈ M, y j = ((p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ))) • m := fun j =>
    hD p n' O S hG n V E hE M hM lam hlam π hπ (h j) (hh j).1 (hh j).2 (hli.ne_zero j) c (y j) (hy j) (hkey j)
  choose m hmM hm using hfin
  refine ⟨∑ j, m j, Submodule.sum_mem _ fun j _ => hmM j, ?_⟩
  rw [hYsum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => hm j

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorSelfAdjoint
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section abs

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem isotypic_stable_gl_operator (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) (x : V) (hx : x ∈ isoSub E mu) :
    E a b x ∈ isoSub E mu := by
  first | exact UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator .. | (apply UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a b x hx | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a b x | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n

theorem commuting_enveloping_monoid (E : GLOps n K V) (X : Module.End K V) (hX : ∀ c d, X * E c d = E c d * X)
    (u : Module.End K V) (hu : u ∈ Umon E) : X * u = u * X := by
  unfold Umon at hu
  induction hu using Submonoid.closure_induction with
  | mem u hu => obtain ⟨ab, rfl⟩ := hu; exact hX _ _
  | one => simp
  | mul u v _ _ hu hv => rw [← mul_assoc, hu, mul_assoc, hv, mul_assoc]

theorem isotypic_stable_commuting (E : GLOps n K V) (X : Module.End K V) (hX : ∀ c d, X * E c d = E c d * X)
    (mu : Fin n → ℤ) (x : V) (hx : x ∈ isoSub E mu) : X x ∈ isoSub E mu := by
  unfold isoSub at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    have h1 : X (u v) = u (X v) := by
      have := congrArg (fun f : Module.End K V => f v) (commuting_enveloping_monoid E X hX u hu)
      simpa using this
    rw [h1]
    by_cases h0 : X v = 0
    · rw [h0, map_zero]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨u, hu, X v, ⟨h0, ?_, ?_⟩, rfl⟩
      · rw [mem_weightSpace_iff_diag]
        intro a
        have h2 := congrArg (fun f : Module.End K V => f v) (hX a a)
        have h3 := (mem_weightSpace_iff_diag E mu v).1 hv.2.1 a
        simp only [Module.End.mul_apply] at h2
        rw [← h2, h3, map_smul]
      · intro a b hab
        have h2 := congrArg (fun f : Module.End K V => f v) (hX a b)
        simp only [Module.End.mul_apply] at h2
        rw [← h2, hv.2.2 a b hab, map_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem isotypic_projector_commutes (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤) (lam : Fin n → ℤ)
    (e : Module.End K V) (he : IsIsoProj E lam e) (X : Module.End K V)
    (hX : ∀ mu, ∀ x ∈ isoSub E mu, X x ∈ isoSub E mu) : e * X = X * e := by
  ext x
  have hx : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  simp only [Module.End.mul_apply]
  induction hx using Submodule.iSup_induction' with
  | mem mu x hx =>
    by_cases h : mu = lam
    · subst h
      rw [he.1 x hx, he.1 _ (hX _ x hx)]
    · rw [he.2 mu h x hx, he.2 mu h _ (hX _ x hx), map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]

theorem isotypic_projector_selfAdjoint (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤) (lam : Fin n → ℤ)
    (e : Module.End K V) (he : IsIsoProj E lam e) (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ lam mu : Fin n → ℤ, lam ≠ mu → ∀ x ∈ isoSub E lam, ∀ y ∈ isoSub E mu, B x y = 0) (x y : V) :
    B (e x) y = B x (e y) := by
  have hx : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  have hy : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  induction hx using Submodule.iSup_induction' with
  | mem mu x hx =>
    induction hy using Submodule.iSup_induction' with
    | mem nu y hy =>
      by_cases h : mu = lam
      · subst h
        rw [he.1 x hx]
        by_cases h' : nu = mu
        · subst h'; rw [he.1 y hy]
        · rw [he.2 nu h' y hy, map_zero, hB mu nu (Ne.symm h') x hx y hy]
      · rw [he.2 mu h x hx, map_zero, LinearMap.zero_apply]
        by_cases h' : nu = lam
        · subst h'; rw [he.1 y hy, hB mu nu h x hx y hy]
        · rw [he.2 nu h' y hy, map_zero]
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

end abs

end Formalism.MainNotions.G.GLWeightTheory
end
end

