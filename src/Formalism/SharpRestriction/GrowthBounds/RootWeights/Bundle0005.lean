import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0004
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0002
import Lemmata.GeneralBFactLeftVersion.Imports

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialPreservesDiagonalStable
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem isotypic_stable_under_gl_operator (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) :
    ∀ x ∈ isoSub E mu, E a b x ∈ isoSub E mu := by
  unfold isoSub
  intro x hx
  have hle : Submodule.span K {x | ∃ u ∈ Umon E, ∃ v, IsHWV E mu v ∧ x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, ∃ v, IsHWV E mu v ∧ x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    refine ⟨E a b * u, ?_, v, hv, rfl⟩
    unfold Umon at hu ⊢
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  exact hle hx

theorem isotypic_sum_stable_gl_operator (E : GLOps n K V) (a b : Fin n) :
    ∀ x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu), E a b x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by
  intro x hx
  have hle : (⨆ mu : Fin n → ℤ, isoSub E mu) ≤ (⨆ mu : Fin n → ℤ, isoSub E mu).comap (E a b) :=
    iSup_le fun mu y hy =>
      Submodule.mem_comap.mpr (Submodule.mem_iSup_of_mem mu (isotypic_stable_under_gl_operator E mu a b y hy))
  exact hle hx

theorem list_prod_preserves_submodule (W : Submodule K V) (l : List (Module.End K V))
    (h : ∀ u ∈ l, ∀ x ∈ W, u x ∈ W) : ∀ x ∈ W, l.prod x ∈ W := by
  induction l with
  | nil =>
    intro x hx
    simpa using hx
  | cons u l ih =>
    intro x hx
    rw [List.prod_cons]
    show u (l.prod x) ∈ W
    exact h u (by simp) _ (ih (fun v hv => h v (by simp [hv])) x hx)

theorem binomial_preserves_diagonal_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (a : Fin n) (k : ℕ) : ∀ x ∈ W, binomE E a k x ∈ W := by
  unfold binomE
  intro x hx
  rw [LinearMap.smul_apply]
  apply W.smul_mem
  refine list_prod_preserves_submodule W _ ?_ x hx
  intro u hu
  simp only [List.mem_map, List.mem_range] at hu
  obtain ⟨j, -, rfl⟩ := hu
  intro y hy
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  exact W.sub_mem (hW a y hy) (W.smul_mem _ (by simpa using hy))

theorem binomial_subring_preserves_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (u : Module.End K V) (hu : u ∈ binomialDiagonalSubring E) : ∀ x ∈ W, u x ∈ W := by
  unfold binomialDiagonalSubring at hu
  let S : Subring (Module.End K V) :=
    { carrier := {u | ∀ x ∈ W, u x ∈ W}
      mul_mem' := fun {u v} hu hv x hx => hu _ (hv x hx)
      one_mem' := fun x hx => hx
      add_mem' := fun {u v} hu hv x hx => W.add_mem (hu x hx) (hv x hx)
      zero_mem' := fun x _ => W.zero_mem
      neg_mem' := fun {u} hu x hx => W.neg_mem (hu x hx) }
  have hle : Subring.closure {u | ∃ a k, u = binomE E a k} ≤ S := by
    rw [Subring.closure_le]
    rintro v ⟨a, k, rfl⟩
    exact binomial_preserves_diagonal_stable E W hW a k
  intro x hx
  exact (hle hu : u ∈ S) x hx

theorem weight_projection_mem_weightSpace (E : GLOps n K V) (hE : IsGLRep E) (Θ : (Fin n → ℤ) → Module.End K V)
    (hΘ : ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0) (μ : Fin n → ℤ) (x : V) :
    Θ μ x ∈ weightSp E μ := by
  unfold IsGLRep at hE
  have hx : x ∈ ⨆ ν, weightSp E ν := by
    rw [hE.2.2]
    exact Submodule.mem_top
  have hle : (⨆ ν, weightSp E ν) ≤ (weightSp E μ).comap (Θ μ) := by
    refine iSup_le fun ν y hy => ?_
    rw [Submodule.mem_comap, hΘ μ ν y hy]
    split_ifs with h
    · subst h
      exact hy
    · exact Submodule.zero_mem _
  exact hle hx

theorem sum_weight_projections_eq_self (E : GLOps n K V) (hE : IsGLRep E) (Θ : (Fin n → ℤ) → Module.End K V)
    (hΘ : ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0) (box : Finset (Fin n → ℤ))
    (hbox : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box) (x : V) : ∑ μ ∈ box, Θ μ x = x := by
  unfold IsGLRep at hE
  have hx : x ∈ ⨆ ν, weightSp E ν := by
    rw [hE.2.2]
    exact Submodule.mem_top
  have hle : (⨆ ν, weightSp E ν) ≤ LinearMap.ker ((∑ μ ∈ box, Θ μ) - 1) := by
    refine iSup_le fun ν y hy => ?_
    have hy' : ∀ μ, Θ μ y = if ν = μ then y else 0 := fun μ => hΘ μ ν y hy
    rw [LinearMap.mem_ker]
    by_cases hν : weightSp E ν = ⊥
    · have h0 : y = 0 := by
        rw [hν] at hy
        exact (Submodule.mem_bot K).mp hy
      subst h0
      simp
    · simp [hy', hbox ν hν]
  have h := hle hx
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

def negHeightFunctional (ν : Fin n → ℤ) : ℤ := - ∑ c : Fin n, ((c : ℕ) : ℤ) * ν c

theorem negHeight_add_root (ν : Fin n → ℤ) (a b : Fin n) :
    negHeightFunctional (ν + rootW a b) = negHeightFunctional ν + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) := by
  unfold negHeightFunctional rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end

theorem sum_isotypic_top_of_weight_data (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E) (hs : OperatorsShiftWeightsByRoots E)
    (hb : WeightsBounded E) (hθ : WeightProjectionsIntegralBinomial E) : IsotypicComponentsSpanModule E := by
  classical
  unfold IsotypicComponentsSpanModule
  obtain ⟨W', hc, hW'⟩ := h2 K V n E hE (⨆ mu : Fin n → ℤ, isoSub E mu) (fun a b => isotypic_sum_stable_gl_operator E a b)
  by_contra hne
  have hW'ne : W' ≠ ⊥ := by
    intro h0
    rw [h0] at hc
    exact hne (by simpa using hc.sup_eq_top)
  obtain ⟨x, hxW', hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'ne
  obtain ⟨m, hm⟩ := hb
  obtain ⟨Θ, hΘm, hΘ⟩ := hθ
  set box : Finset (Fin n → ℤ) := Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(m : ℤ)) m) with hboxdef
  have hbox : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box := by
    intro ν hν
    rw [hboxdef, Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    exact abs_le.1 (hm ν hν a)
  have hsum := sum_weight_projections_eq_self E hE Θ hΘ box hbox x
  have hex : ∃ ν ∈ box, Θ ν x ≠ 0 := by
    apply Finset.exists_ne_zero_of_sum_ne_zero
    rw [hsum]; exact hx0
  set S : Finset (Fin n → ℤ) := box.filter (fun ν => W' ⊓ weightSp E ν ≠ ⊥) with hS
  have hSne : S.Nonempty := by
    obtain ⟨ν, hν, hν0⟩ := hex
    refine ⟨ν, ?_⟩
    rw [hS, Finset.mem_filter]
    refine ⟨hν, fun hbot => hν0 ?_⟩
    have : Θ ν x ∈ W' ⊓ weightSp E ν :=
      ⟨binomial_subring_preserves_stable E W' (fun a => hW' a a) (Θ ν) (hΘm ν) x hxW', weight_projection_mem_weightSpace E hE Θ hΘ ν x⟩
    rw [hbot] at this
    simpa using this
  obtain ⟨ν, hνS, hmax⟩ := Finset.exists_max_image S negHeightFunctional hSne
  rw [hS, Finset.mem_filter] at hνS
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hνS.2
  have hraise : ∀ a b : Fin n, a < b → E a b y = 0 := by
    intro a b hab
    by_contra hne0
    have hmem : E a b y ∈ W' ⊓ weightSp E (ν + rootW a b) := ⟨hW' a b y hy.1, hs a b ν y hy.2⟩
    have h1 : W' ⊓ weightSp E (ν + rootW a b) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hmem
      exact hne0 (by simpa using hmem)
    have h2' : weightSp E (ν + rootW a b) ≠ ⊥ := by
      intro hbot
      rw [hbot] at h1
      exact h1 (by simp)
    have h3 : ν + rootW a b ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨hbox _ h2', h1⟩
    have h4 := hmax _ h3
    rw [negHeight_add_root] at h4
    have h5 : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
    linarith
  have hhw : IsHWV E ν y := ⟨hy0, hy.2, hraise⟩
  have hyiso : y ∈ isoSub E ν := Submodule.subset_span ⟨1, (Umon E).one_mem, y, hhw, rfl⟩
  have hyW : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := (le_iSup (fun mu : Fin n → ℤ => isoSub E mu) ν) hyiso
  have : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) ⊓ W' := ⟨hyW, hy.1⟩
  rw [hc.inf_eq_bot] at this
  exact hy0 (by simpa using this)

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.CyclicSubmoduleIsSubrepresentation
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem charZero_fraction_field_of_setting {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  have hO : CharZero O := by
    rcases S with ⟨w, hw, hpm, hp0, -⟩
    rcases CharP.char_is_prime_or_zero O (ringChar O) with hq | hq
    · exfalso
      have hne : p ≠ ringChar O := by
        rintro h
        apply hp0
        rw [h]
        exact CharP.cast_eq_zero O (ringChar O)
      have hcop : Nat.gcd p (ringChar O) = 1 := (Nat.coprime_primes hp hq).mpr hne
      have key : (1 : O) = (p : O) * (Nat.gcdA p (ringChar O) : O) := by
        have h := congrArg (fun z : ℤ => (z : O)) (Nat.gcd_eq_gcd_ab p (ringChar O))
        simp only [hcop, Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
          CharP.cast_eq_zero, zero_mul, add_zero] at h
        exact h
      have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := key ▸ Ideal.mul_mem_right _ _ hpm
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    · haveI : CharP O 0 := hq ▸ ringChar.charP O
      exact CharP.charP_to_charZero O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))

theorem cyclicSubmodule_isSubrepresentation {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (v : V) :
    IsSubrepresentation E (cyclicSubmodule E v) := by
  unfold IsSubrepresentation cyclicSubmodule
  intro a b x hx
  have hle : Submodule.span K {x | ∃ u ∈ Umon E, x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    refine ⟨E a b * u, ?_, rfl⟩
    unfold Umon at hu ⊢
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  exact hle hx

theorem log_bound_monotone (p n : ℕ) {k l : ℕ} (h : k ≤ l) : deF p n k ≤ deF p n l := by
  unfold deF
  exact Nat.log_mono_right (by omega)

theorem pow_smul_mem_of_le' {O W : Type} [CommRing O] [AddCommGroup W] [Module O W] (M : Submodule O W) (c : O) {a b : ℕ}
    (hab : a ≤ b) {z : W} (h : c ^ a • z ∈ M) : c ^ b • z ∈ M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_comm, mul_smul]
  exact M.smul_mem _ h

theorem lattice_theorem_single_rep (h : InvariantDenominatorEllPBound) (hTop : IsotypicSubmodulesSpanTop) (hRes : RestrictionIsRepresentation) (hHom : HomSpaceIsRepresentation) (hInv : InvariantProjectionExists)
    (hTh : IsotypicProjectorTraceFormula) (hB : LatticeAdaptedBasisExists) (hLat : HomLatticeDividedPowerStable) (hEll : HomRepEllBoundedByTarget)
    (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S : UniformizedDVR p O)
    (hG : AdmissibleDVR p n' O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V) (hE : IsGLRep E)
    (M : Submodule O V) (hM : UZLattice E M) (hMQ : MQ (K := KK O) M = ⊤)
    (lam : Fin n → ℤ) (e : Module.End (KK O) V) (he : IsIsoProj E lam e) (x : V) (hx : x ∈ M) :
    ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M)))) • e x ∈ M := by
  haveI : CharZero (KK O) := charZero_fraction_field_of_setting S hG.prime
  by_cases hv : ∃ v0, IsHWV E lam v0
  · obtain ⟨v0, hv0⟩ := hv
    have hL := cyclicSubmodule_isSubrepresentation E v0
    obtain ⟨d, b, hbM, hbc⟩ := hB O V M hM.2 hMQ (cyclicSubmodule E v0)
    have hEH : IsGLRep (homRepresentation (restrictRepresentation E _ hL) E) :=
      hHom n (KK O) _ V _ E (hRes n (KK O) V E hE _ hL) hE
    obtain ⟨P, hP⟩ := hInv n (KK O) _ _ hEH
    obtain ⟨hl1, hl2⟩ := hLat O n V E hE M hM hMQ _ hL
    have key : ∀ i, ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M)))) • P ((b.coord i).smulRight x) (b i) ∈ M := by
      intro i
      have hf : (b.coord i).smulRight x ∈ homLattice M (cyclicSubmodule E v0) := by
        intro y hy
        obtain ⟨o, ho⟩ := hbc y hy i
        rw [LinearMap.smulRight_apply, ho, algebraMap_smul]
        exact M.smul_mem _ hx
      have h1 := h p n' O S hG n _ _ hEH _ hl1 hl2 P hP _ hf
      have h2 := h1 (b i) (hbM i)
      rw [LinearMap.smul_apply] at h2
      refine pow_smul_mem_of_le' M _ ?_ h2
      refine Nat.mul_le_mul_left _ (log_bound_monotone p n ?_)
      rw [hl2, hMQ]
      exact hEll n (KK O) V E hE _ hL
    rw [← hTh n (KK O) V E hE lam e he v0 hv0 hL P hP (Fin d) b x, Nat.cast_smul_eq_nsmul, smul_comm,
      Finset.smul_sum]
    exact M.smul_of_tower_mem _ (M.sum_mem fun i _ => key i)
  · have h0 : e x = 0 := by
      have hle : (⨆ mu, isoSub E mu) ≤ LinearMap.ker e := by
        refine iSup_le fun mu => ?_
        by_cases hmu : mu = lam
        · subst hmu
          refine Submodule.span_le.2 ?_
          rintro y ⟨u, _, v, hv', _⟩
          exact absurd ⟨v, hv'⟩ hv
        · intro y hy
          exact he.2 mu hmu y hy
      have : x ∈ (⨆ mu, isoSub E mu) := by rw [hTop n (KK O) V E hE]; trivial
      exact hle this
    rw [h0, smul_zero]; exact M.zero_mem

theorem lattice_theorem_of_interfaces (D : Formalism.BasicNotions.D7) (h : InvariantDenominatorEllPBound) (hTop : IsotypicSubmodulesSpanTop) (hRes : RestrictionIsRepresentation) (hHom : HomSpaceIsRepresentation)
    (hInv : InvariantProjectionExists) (hTh : IsotypicProjectorTraceFormula) (hB : LatticeAdaptedBasisExists) (hLat : HomLatticeDividedPowerStable) (hEll : HomRepEllBoundedByTarget) :
    IsotypicProjectorTheoremField D := by
  unfold IsotypicProjectorTheoremField
  intro p n' O _ _ _ S hG n _ V _ _ _ _ _ E hE M hM hMQ Sw _ e he x hx
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun lam hlam => ?_
  have h1 := lattice_theorem_single_rep h hTop hRes hHom hInv hTh hB hLat hEll p n' O S hG n V E hE M hM hMQ lam (e lam)
    (he lam hlam) x hx
  refine pow_smul_mem_of_le' M (p : O) ?_ h1
  calc N0 n * deF p n (ellOf E (MQ M)) ≤ N0 n * deF p n (ellOf E (MQ M) + ellWt lam) :=
        Nat.mul_le_mul_left _ (log_bound_monotone p n (Nat.le_add_right _ _))
    _ ≤ _ := Finset.le_sup (f := fun lam => N0 n * deF p n (ellOf E (MQ M) + ellWt lam)) hlam

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivationFinsetSumApply
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem derivation_finset_sum_apply {σ α : Type} (s : Finset α)
    (D : α → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (F : MvPolynomial σ K) :
    (∑ l ∈ s, D l) F = ∑ l ∈ s, D l F := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

open Classical in

def glDerivation (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) :=
  ∑ l : ι, if l ∈ S then
      (if LL.vec l then (X (l, a) : MvPolynomial (ι × Fin n) K) • pderiv (l, b)
       else -((X (l, b) : MvPolynomial (ι × Fin n) K) • pderiv (l, a)))
    else 0

theorem gl_action_eq_derivation (LL : Letters ι) (S : Set ι) (a b : Fin n) (F : MvPolynomial (ι × Fin n) K) :
    glAct K LL S a b F = glDerivation K LL S a b F := by
  unfold glAct glDerivation
  rw [LinearMap.sum_apply, derivation_finset_sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

open Classical in
theorem gl_derivation_variable (LL : Letters ι) (S : Set ι) (a b : Fin n) (l : ι) (c : Fin n) :
    glDerivation K LL S a b (X (l, c)) =
      if l ∈ S then (if LL.vec l then (if c = b then X (l, a) else 0) else (if c = a then -X (l, b) else 0))
      else 0 := by
  unfold glDerivation
  rw [derivation_finset_sum_apply, Finset.sum_eq_single l]
  · split_ifs <;> simp_all [pderiv_X, Pi.single_apply]
  · intro l' _ hl'
    split_ifs <;> simp [pderiv_X, Pi.single_apply, Ne.symm hl']
  · simp

theorem gl_derivation_lie_bracket (LL : Letters ι) (S : Set ι) (a b c d : Fin n) :
    ⁅glDerivation K LL S a b, glDerivation K LL S c d⁆ =
      (if b = c then glDerivation K LL S a d else 0) - (if d = a then glDerivation K LL S c b else 0) := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨l, e⟩
  rw [Derivation.commutator_apply]
  by_cases hl : l ∈ S
  · by_cases hv : LL.vec l = true
    · simp only [gl_derivation_variable, hl, hv, if_true, apply_ite (glDerivation K LL S a b), apply_ite (glDerivation K LL S c d),
        map_zero, Derivation.coe_sub, Pi.sub_apply]
      by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : e = d <;> by_cases h4 : e = b <;>
        subst_vars <;> simp_all [gl_derivation_variable] <;> grind
    · simp only [gl_derivation_variable, hl, hv, if_true, apply_ite (glDerivation K LL S a b), apply_ite (glDerivation K LL S c d),
        map_zero, map_neg, Derivation.coe_sub, Pi.sub_apply]
      by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : e = c <;> by_cases h4 : e = a <;>
        subst_vars <;> simp_all [gl_derivation_variable]
  · by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [gl_derivation_variable, hl, h1, h2]

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsNonzeroMultipleMemLattice
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem finite_full_submodule_isLattice {O : Type} [CommRing O] [IsDomain O]
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (M : Submodule O V) (hfg : M.FG) (hM : MQ (K := KK O) M = ⊤) : Submodule.IsLattice (KK O) M :=
  ⟨hfg, hM⟩

theorem exists_nonzero_multiple_mem_lattice {O : Type} [CommRing O] [IsDomain O]
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (M : Submodule O V) (hM : MQ (K := KK O) M = ⊤) (x : V) : ∃ a : O, a ≠ 0 ∧ a • x ∈ M := by
  first | exact Bl.general_b_fact_left_version.goal1 .. | (apply Bl.general_b_fact_left_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_version.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_version.goal1 <;> first | assumption | infer_instance)

theorem dual_lattice_values_mem_scaled : DualLatticeDivisibility := by
  intro O _ _ _ V _ _ _ _ _ M hfg hM t z hz
  have : Submodule.IsLattice (KK O) M := finite_full_submodule_isLattice M hfg hM
  let b := Module.finBasis O M
  let B := b.extendOfIsLattice (KK O)
  have hB : ∀ i, B i = ((b i : M) : V) := fun i => Module.Basis.extendOfIsLattice_apply (KK O) b i
  have hcoord : ∀ i, ∀ x ∈ M, ∃ o : O, B.coord i x = algebraMap O (KK O) o := by
    intro i x hx
    refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 : x = ∑ j, (algebraMap O (KK O) (b.repr ⟨x, hx⟩ j)) • B j := by
      have h2 := congrArg (fun y : M => (y : V)) (b.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      refine h2.symm.trans ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hB, algebraMap_smul]
    conv_lhs => rw [h1]
    simp [Module.Basis.coord_apply, Finsupp.single_apply, Algebra.algebraMap_eq_smul_one]
  choose o ho using fun i => hz (B.coord i) (hcoord i)
  refine ⟨∑ i, o i • ((b i : M) : V), M.sum_mem fun i _ => M.smul_mem _ (b i).2, ?_⟩
  rw [← B.sum_repr z, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := ho i
  rw [Module.Basis.coord_apply] at this
  rw [this, hB, mul_smul, algebraMap_smul]

theorem lattice_inter_subspace_basis : LatticeSubspaceBasis := by
  intro O _ _ _ V _ _ _ _ _ M hfg hM H
  let N : Submodule O H := M.comap (H.subtype.restrictScalars O)
  have hmemN : ∀ x : H, x ∈ N ↔ (x : V) ∈ M := fun x => Iff.rfl
  have hNoeM : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hfg
  let φ : N →ₗ[O] M :=
    { toFun := fun x => ⟨((x : H) : V), (hmemN x.1).1 x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hφ : Function.Injective φ := by
    intro x y hxy
    have : ((x : H) : V) = ((y : H) : V) := congrArg (fun w : M => (w : V)) hxy
    exact Subtype.ext (Subtype.ext this)
  have hNoeN : IsNoetherian O N := isNoetherian_of_injective φ hφ
  have hNfg : N.FG := (Module.Finite.iff_fg).1 inferInstance
  have hNspan : Submodule.span (KK O) (N : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_nonzero_multiple_mem_lattice M hM (x : V)
    have ha1 : algebraMap O (KK O) a ≠ 0 :=
      (map_ne_zero_iff (algebraMap O (KK O)) (IsFractionRing.injective O (KK O))).2 ha
    have hmem : a • x ∈ N := (hmemN _).2 (by simpa using hax)
    have hx : x = (algebraMap O (KK O) a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul (KK O) a x, smul_smul, inv_mul_cancel₀ ha1, one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have : Submodule.IsLattice (KK O) N := ⟨hNfg, hNspan⟩
  let b := Module.finBasis O N
  let B := b.extendOfIsLattice (KK O)
  have hB : ∀ i, B i = ((b i : N) : H) := fun i => Module.Basis.extendOfIsLattice_apply (KK O) b i
  refine ⟨Module.finrank O N, fun j => (((b j : N) : H) : V), fun j => ⟨(hmemN _).1 (b j).2, (b j : H).2⟩, ?_, ?_, ?_⟩
  · have h1 := B.linearIndependent.map' H.subtype (Submodule.ker_subtype H)
    have h2 : (fun j => (((b j : N) : H) : V)) = (H.subtype ∘ B) := by
      funext j
      simp [hB]
    rw [h2]
    exact h1
  · intro x hx
    have h1 := congrArg (fun y : H => (y : V)) (B.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [← h1]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_⟩)
    simp [hB]
  · intro x hxM hxH
    refine ⟨fun j => b.repr ⟨⟨x, hxH⟩, (hmemN _).2 hxM⟩ j, ?_⟩
    have h1 := congrArg (fun y : N => ((y : H) : V)) (b.sum_repr ⟨⟨x, hxH⟩, (hmemN _).2 hxM⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm

end Formalism.MainNotions.G.GLWeightTheory
end
end

