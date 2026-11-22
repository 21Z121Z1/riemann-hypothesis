import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001
import Lemmata.SimultaneousEigenvectors.BlSimeig

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCasA
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section AlgGen

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}

theorem sum_compact_swap {R : Type*} [AddCommMonoid R] (f : Fin n → Fin n → R) :
    ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), f a b =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), f b a := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [eq_comm]

theorem isGlRep_add {A B : Fin n → Fin n → Module.End ℂ X} (hA : IsGlRep A) (hB : IsGlRep B)
    (hAB : ∀ a b c d, A a b * B c d = B c d * A a b) : IsGlRep (A + B) := by
  intro a b c d
  simp only [Pi.add_apply]
  have h1 := hA a b c d
  have h2 := hB a b c d
  have h3 := hAB a b c d
  have h4 := hAB c d a b
  have : (A a b + B a b) * (A c d + B c d) - (A c d + B c d) * (A a b + B a b) =
      (A a b * A c d - A c d * A a b) + (B a b * B c d - B c d * B a b) := by
    simp only [add_mul, mul_add]
    rw [h3, h4]
    abel
  rw [this, h1, h2]
  split_ifs <;> (try simp only [sub_zero, zero_sub, add_zero]) <;> abel

theorem casimirK_add (A B : Fin n → Fin n → Module.End ℂ X)
    (hAB : ∀ a b c d, A a b * B c d = B c d * A a b) :
    casimirK ε (A + B) = casimirK ε A + casimirK ε B +
      2 • ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), B a b * A b a := by
  unfold casimirK
  simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  have : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), A a b * B b a =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), B a b * A b a := by
    rw [sum_compact_swap]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hAB b a a b
  rw [this, two_nsmul]
  abel

theorem commute_casimirK {A : Fin n → Fin n → Module.End ℂ X} {Z : Module.End ℂ X}
    (h : ∀ c d, Commute Z (A c d)) : Commute Z (casimirK ε A) := by
  unfold casimirK
  exact Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ => (h a b).mul_right (h b a)

end AlgGen

section Slots

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem big_ext {k : ℕ} {F G : Big n k M} (h : ∀ κ, F κ = G κ) : F = G :=
  (WithLp.ext_iff 2).2 (funext h)

theorem ofCoords_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) (x : X) (κ : Fin k → Fin n × Fin n) :
    (ofCoords k f x) κ = f κ x := rfl

theorem mAct_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    mAct E k a b F κ = E a b (F κ) := rfl

theorem factorAd_apply (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    factorAd k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  show (ofCoords k _ F) κ = _
  rw [ofCoords_apply, LinearMap.sub_apply]
  split_ifs <;> rfl

theorem mem_ncV_iff {k : ℕ} {F : Big n k M} : F ∈ ncV ε V k ↔
    ∀ κ : Fin k → Fin n × Fin n, ((∀ i, ε (κ i).1 ≠ ε (κ i).2) → F κ ∈ V) ∧
      ((¬ ∀ i, ε (κ i).1 ≠ ε (κ i).2) → F κ = 0) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap]
  refine forall_congr' fun κ => ?_
  split_ifs with h <;> simp [h] <;> rfl

theorem mAct_comm_factorAd (k : ℕ) (i : Fin k) (a b c d : Fin n) :
    mAct E k a b * factorAd k i c d = factorAd k i c d * mAct E k a b := by
  ext F : 1
  refine big_ext fun κ => ?_
  simp only [Module.End.mul_apply, mAct_apply, factorAd_apply, map_sub]
  split_ifs <;> simp

theorem factorAd_comm_factorAd {k : ℕ} {i j : Fin k} (hij : i ≠ j) (a b c d : Fin n) :
    factorAd (M := M) k i a b * factorAd k j c d = factorAd k j c d * factorAd k i a b := by
  ext F : 1
  refine big_ext fun κ => ?_
  simp only [Module.End.mul_apply, factorAd_apply, Function.update_of_ne hij.symm,
    Function.update_of_ne hij, Function.update_comm hij]
  split_ifs <;> abel

theorem mAct_isGlRep (hE : IsGlRep E) (k : ℕ) : IsGlRep (mAct E k) := by
  intro a b c d
  ext F : 1
  refine big_ext fun κ => ?_
  have := LinearMap.congr_fun (hE a b c d) (F κ)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this ⊢
  split_ifs at this ⊢ <;> simpa [mAct_apply, PiLp.sub_apply] using this

theorem isGlRep_factorAd (k : ℕ) (i : Fin k) : IsGlRep (n := n) (fun a b => factorAd (M := M) k i a b) := by
  intro a b c d
  ext F : 1
  refine big_ext fun κ => ?_
  rcases hx : κ i with ⟨x, y⟩
  have hz : ∀ p : Prop, ∀ _ : Decidable p, ∀ f : Module.End ℂ (Big n k M),
      ((if p then f else 0) F) κ = if p then f F κ else 0 := by
    intro p _ f; split_ifs <;> rfl
  simp only [LinearMap.sub_apply, Module.End.mul_apply, PiLp.sub_apply, hz, factorAd_apply,
    Function.update_self, Function.update_idem, hx]
  split_ifs <;> (try subst_vars) <;> (try contradiction) <;> abel

def positionPerm {k : ℕ} (i : Fin k) (τ : Equiv.Perm (Fin n × Fin n)) :
    Equiv.Perm (Fin k → Fin n × Fin n) where
  toFun κ := Function.update κ i (τ (κ i))
  invFun κ := Function.update κ i (τ.symm (κ i))
  left_inv κ := by simp
  right_inv κ := by simp

theorem positionPerm_apply {k : ℕ} (i : Fin k) (τ : Equiv.Perm (Fin n × Fin n)) (κ : Fin k → Fin n × Fin n) :
    positionPerm i τ κ = Function.update κ i (τ (κ i)) := rfl

theorem inner_ite_left (p : Prop) [Decidable p] (x y : M) :
    inner ℂ (if p then x else 0) y = if p then inner ℂ x y else 0 := by
  split_ifs <;> simp

theorem inner_ite_right (p : Prop) [Decidable p] (x y : M) :
    inner ℂ x (if p then y else 0) = if p then inner ℂ x y else 0 := by
  split_ifs <;> simp

theorem factorAd_adjoint (k : ℕ) (i : Fin k) (a b : Fin n) (F G : Big n k M) :
    inner ℂ (factorAd k i a b F) G = inner ℂ F (factorAd k i b a G) := by
  simp only [PiLp.inner_apply, factorAd_apply, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib,
    inner_ite_left, inner_ite_right]
  congr 1
  · refine Fintype.sum_equiv (positionPerm i (Equiv.prodCongr (Equiv.swap a b) (Equiv.refl _))) _ _
      fun κ => ?_
    rcases hx : κ i with ⟨x, y⟩
    simp only [positionPerm_apply, Function.update_self, Function.update_idem, hx, Equiv.prodCongr_apply,
      Prod.map, Equiv.refl_apply]
    by_cases h : x = a
    · subst h
      simp only [Equiv.swap_apply_left, if_true]
      rw [← hx, Function.update_eq_self]
    · have : Equiv.swap a b x ≠ b := by
        rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]; exact h
      simp [h, this]
  · refine Fintype.sum_equiv (positionPerm i (Equiv.prodCongr (Equiv.refl _) (Equiv.swap a b))) _ _
      fun κ => ?_
    rcases hx : κ i with ⟨x, y⟩
    simp only [positionPerm_apply, Function.update_self, Function.update_idem, hx, Equiv.prodCongr_apply,
      Prod.map, Equiv.refl_apply]
    by_cases h : y = b
    · subst h
      simp only [Equiv.swap_apply_right, if_true]
      rw [← hx, Function.update_eq_self]
    · have : Equiv.swap a b y ≠ a := by
        rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]; exact h
      simp [h, this]

theorem mAct_adj (hU : IsInfUnitary ε E) (k : ℕ) {a b : Fin n} (hab : ε a = ε b) (F G : Big n k M) :
    inner ℂ (mAct E k a b F) G = inner ℂ F (mAct E k b a G) := by
  simp only [PiLp.inner_apply, mAct_apply, hU a b, adjSign, hab, if_true, one_mul]

theorem factorAd_mem_ncV {k : ℕ} (i : Fin k) {a b : Fin n} (hab : ε a = ε b) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : factorAd k i a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  rcases hx : κ i with ⟨x, y⟩
  simp only [factorAd_apply, hx]
  constructor
  · intro hκ
    have hxy : ε x ≠ ε y := by simpa [hx] using hκ i
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs with h <;> try exact Submodule.zero_mem _
    · refine (hF _).1 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [← hab, ← h]; exact hxy
      · rw [Function.update_of_ne hj]; exact hκ j
    · refine (hF _).1 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [hab, ← h]; exact hxy
      · rw [Function.update_of_ne hj]; exact hκ j
  · intro hκ
    push Not at hκ
    obtain ⟨j, hj⟩ := hκ
    have key : ∀ p : Fin n × Fin n, ε p.1 = ε p.2 → (¬ ∀ l, ε ((Function.update κ i p) l).1 ≠
        ε ((Function.update κ i p) l).2) := by
      intro p hp h
      by_cases hji : j = i
      · subst hji; exact h j (by simpa using hp)
      · exact h j (by rw [Function.update_of_ne hji]; exact hj)
    have hxy : j = i → ε x = ε y := by intro hji; subst hji; simpa [hx] using hj
    have hc : ∀ p : Fin n × Fin n, (j = i → ε p.1 = ε p.2) → F (Function.update κ i p) = 0 := by
      intro p hp
      by_cases hji : j = i
      · exact (hF _).2 (key p (hp hji))
      · refine (hF _).2 fun h => h j ?_
        rw [Function.update_of_ne hji]; exact hj
    rw [ite_eq_right_iff.2 ?_, ite_eq_right_iff.2 ?_, sub_zero]
    · intro h; subst h; exact hc _ fun hji => by show ε x = ε a; rw [hxy hji, ← hab]
    · intro h; subst h; exact hc _ fun hji => by show ε b = ε y; rw [← hab, hxy hji]

theorem mAct_mem_ncV (hV : IsKStableSub ε E V) (k : ℕ) {a b : Fin n} (hab : ε a = ε b)
    {F : Big n k M} (hF : F ∈ ncV ε V k) : mAct E k a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  simp only [mAct_apply]
  exact ⟨fun h => hV a b hab _ ((hF κ).1 h), fun h => by rw [(hF κ).2 h, map_zero]⟩

end Slots

end ReciprocityTheory.ChartRestriction.DS.BigCasimir
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section KUnit

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

def IsKUnitary (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ X) : Prop :=
  ∀ a b, ε a = ε b → ∀ x y : X, inner ℂ (A a b x) y = inner ℂ x (A b a y)

theorem isKUnitary_of_isInfUnitary (hU : IsInfUnitary ε A) : IsKUnitary ε A := by
  intro a b h x y
  rw [hU a b x y]
  simp [adjSign, h]

def kUnitNatB (a b : Fin 2) : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  LinearMap.smulRight (EuclideanSpace.proj b : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).toLinearMap
    (EuclideanSpace.single a 1)

theorem kUnit_diag_comm (hA : IsGlRep A) (a c : Fin n) (v : X) :
    A a a (A c c v) = A c c (A a a v) := by
  have h := LinearMap.congr_fun (hA a a c c) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  by_cases hac : a = c
  · subst hac; rfl
  · simp only [if_neg hac, if_neg (Ne.symm hac), LinearMap.zero_apply, sub_zero, sub_eq_zero] at h
    exact h

theorem kUnit_weight_shift (hA : IsGlRep A) {μ : Fin n → ℝ} {w : X} (hw : ∀ c, A c c w = (μ c : ℂ) • w)
    {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    A c c (A a b w) = ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • A a b w := by
  have h := LinearMap.congr_fun (hA c c a b) w
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hw c, map_smul] at h
  by_cases hca : c = a
  · subst hca
    simp [hab, Ne.symm hab] at h ⊢
    linear_combination (norm := module) h
  · by_cases hcb : c = b
    · subst hcb
      simp [hca] at h ⊢
      linear_combination (norm := module) h
    · simp [hca, hcb, Ne.symm hcb] at h ⊢
      linear_combination (norm := module) h

theorem kUnit_exists_joint (hA : IsGlRep A) (s : Finset (Fin n)) :
    ∀ T : Submodule ℂ X, FiniteDimensional ℂ T → (∀ c, ∀ v ∈ T, A c c v ∈ T) → T ≠ ⊥ →
      ∃ w ∈ T, w ≠ 0 ∧ ∃ μ : Fin n → ℂ, ∀ c ∈ s, A c c w = μ c • w := by
  first | exact Bl.SimultaneousEigenvectors.goal1 .. | (apply Bl.SimultaneousEigenvectors.goal1 <;> assumption) | (intros; apply Bl.SimultaneousEigenvectors.goal1 <;> assumption)

theorem kUnit_eig_real (hU : IsKUnitary ε A) {c : Fin n} {w : X} (hw0 : w ≠ 0) {z : ℂ}
    (hw : A c c w = z • w) : z = ((z.re : ℝ) : ℂ) := by
  have h := hU c c rfl w w
  rw [hw, inner_smul_left, inner_smul_right] at h
  have hne : inner ℂ w w ≠ (0 : ℂ) := inner_self_ne_zero.mpr hw0
  have h2 : (starRingEnd ℂ) z = z := mul_right_cancel₀ hne h
  exact (Complex.conj_eq_iff_re.mp h2).symm

def kUnitWtLin (μ : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((n : ℝ) - ((c : ℕ) : ℝ)) * μ c

theorem kUnitWtLin_shift (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    kUnitWtLin μ < kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  have h : kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) =
      kUnitWtLin μ + ((n : ℝ) - ((a : ℕ) : ℝ)) - ((n : ℝ) - ((b : ℕ) : ℝ)) := by
    simp only [kUnitWtLin, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  linarith

theorem exists_khw (hA : IsGlRep A) (hU : IsKUnitary ε A) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ w ∈ S, w ≠ 0 ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε A μ w := by
  classical
  have hSc : ∀ c, ∀ v ∈ S, A c c v ∈ S := fun c => hS c c rfl
  let P : Set (Fin n → ℝ) := {μ | ∃ w ∈ S, w ≠ 0 ∧ ∀ c, A c c w = (μ c : ℂ) • w}
  have hPfin : P.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (r : ℂ)})
      (fun c => (Module.End.finite_hasEigenvalue _).preimage
        (Complex.ofReal_injective.injOn))).subset ?_
    rintro μ ⟨w, hw, hw0, hμ⟩ c -
    show Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (μ c : ℂ)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa using hμ c)
    · intro h
      exact hw0 (congrArg Subtype.val h)
  have hPne : P.Nonempty := by
    obtain ⟨w, hw, hw0, z, hz⟩ := kUnit_exists_joint hA Finset.univ S hfd hSc hne
    refine ⟨fun c => (z c).re, w, hw, hw0, fun c => ?_⟩
    rw [hz c (Finset.mem_univ c)]
    congr 1
    exact kUnit_eig_real hU hw0 (hz c (Finset.mem_univ c))
  obtain ⟨μ, ⟨w, hw, hw0, hμ⟩, hmax⟩ := Set.exists_max_image P kUnitWtLin hPfin hPne
  refine ⟨w, hw, hw0, μ, hμ, ?_⟩
  intro a b hab hεab
  by_contra h
  have hmem : (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) ∈ P :=
    ⟨A a b w, hS a b hεab w hw, h, fun c => kUnit_weight_shift hA hμ (ne_of_lt hab) c⟩
  exact absurd (hmax _ hmem) (not_le.mpr (kUnitWtLin_shift μ hab))

theorem orthogonal_kStable (hU : IsKUnitary ε A) {S : Submodule ℂ X} (hS : IsKStableSub ε A S) :
    IsKStableSub ε A Sᗮ := by
  intro a b hab v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← hU b a hab.symm u v]
  exact hv _ (hS b a hab.symm u hu)

theorem starProjection_comm (hU : IsKUnitary ε A) {S : Submodule ℂ X} [S.HasOrthogonalProjection]
    (hS : IsKStableSub ε A S) {a b : Fin n} (hab : ε a = ε b) (x : X) :
    S.starProjection (A a b x) = A a b (S.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hS a b hab _ (Submodule.starProjection_apply_mem S x)
  · intro w hw
    rw [← map_sub]
    have h1 : x - S.starProjection x ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have h2 := orthogonal_kStable hU hS a b hab _ h1
    rw [Submodule.mem_orthogonal] at h2
    rw [inner_eq_zero_symm]
    exact h2 w hw

end KUnit

end ReciprocityTheory.ChartRestriction.DS
end
end

