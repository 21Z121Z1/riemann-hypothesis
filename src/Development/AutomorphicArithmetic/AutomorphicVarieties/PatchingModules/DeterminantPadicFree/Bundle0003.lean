import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.Module.Lattice

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FiniteOfGeneratedByOneElement
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.sqExt :
    ∀ {K : Type} [Field K], ∃ j : PowerSeries K →+* PowerSeries K, Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ j PowerSeries.X = PowerSeries.X ^ 2 := by
  intro K _
  refine ⟨(PowerSeries.expand 2 two_ne_zero (R := K)).toRingHom, ?_, ?_, ?_, by simp⟩
  · intro f g h
    ext m
    have h1 := congrArg (PowerSeries.coeff (2 * m)) h
    simpa using h1
  · refine ⟨fun f hf => ?_⟩
    rw [PowerSeries.isUnit_iff_constantCoeff] at hf ⊢
    simpa using hf
  · classical
    letI inst : Module (PowerSeries K) (PowerSeries K) :=
      (PowerSeries.expand 2 two_ne_zero (R := K)).toRingHom.toAlgebra.toModule
    have hs : Submodule.span (PowerSeries K) ({1, PowerSeries.X} : Set (PowerSeries K)) = ⊤ := by
      rw [eq_top_iff]
      intro f _
      rw [Submodule.mem_span_pair]
      refine ⟨PowerSeries.mk fun m => PowerSeries.coeff (2 * m) f,
        PowerSeries.mk fun m => PowerSeries.coeff (2 * m + 1) f, ?_⟩
      change PowerSeries.expand 2 two_ne_zero (PowerSeries.mk fun m => PowerSeries.coeff (2 * m) f) * 1 +
        PowerSeries.expand 2 two_ne_zero (PowerSeries.mk fun m => PowerSeries.coeff (2 * m + 1) f) *
          PowerSeries.X = f
      ext n
      rw [mul_one, map_add, ← pow_one (PowerSeries.X (R := K)), PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_expand, PowerSeries.coeff_expand]
      simp only [PowerSeries.coeff_mk]
      split_ifs <;> first | omega | (simp only [add_zero, zero_add]; congr; omega)
    exact ⟨⟨{1, PowerSeries.X}, by rw [Finset.coe_insert, Finset.coe_singleton]; exact hs⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FlagFDiagonalise
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem flagF_diag_mul {F : Type} [Field F] {n : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA (show id k < id i from h), zero_mul]
    · rw [hB (show id i < id k from h), mul_zero]
  · simp

private theorem flagF_tri {F H : Type} [Field F] {n : ℕ} (T : H → Matrix (Fin n) (Fin n) F)
    (E : Matrix (Fin n) (Fin n) F) (hT : ∀ s, (T s).BlockTriangular id)
    (hsep : ∀ i j, i ≠ j → ∃ s, T s i i ≠ T s j j) (hc : ∀ s, T s * E = E * T s) :
    E.BlockTriangular id := by
  have key : ∀ m : ℕ, ∀ i j : Fin n, j < i → n + (j : ℕ) ≤ i + m → E i j = 0 := by
    intro m
    induction m with
    | zero => intro i j _ h; have := i.2; omega
    | succ m ih =>
      intro i j hji h
      obtain ⟨s, hs⟩ := hsep i j hji.ne'
      have h1 : (T s * E) i j = T s i i * E i j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · intro k _ hk
          rcases lt_or_gt_of_ne hk with h' | h'
          · rw [hT s (show id k < id i from h'), zero_mul]
          · rw [ih k j (hji.trans h') (by rw [Fin.lt_def] at h'; omega), mul_zero]
        · simp
      have h2 : (E * T s) i j = E i j * T s j j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single j]
        · intro k _ hk
          rcases lt_or_gt_of_ne hk with h' | h'
          · rw [ih i k (h'.trans hji) (by rw [Fin.lt_def] at h'; omega), zero_mul]
          · rw [hT s (show id j < id k from h'), mul_zero]
        · simp
      rw [hc, h2, mul_comm] at h1
      by_contra h0
      exact hs (mul_right_cancel₀ h0 h1).symm
  intro i j hji
  exact key n i j hji (by have : (j : ℕ) < i := hji; omega)

private theorem flagF_diagonalise {F : Type} [Field F] {n : ℕ} (E : Matrix (Fin n) (Fin n) F)
    (hE : E.BlockTriangular id) (hEE : E * E = E) :
    ∃ U : Matrix (Fin n) (Fin n) F, U.BlockTriangular id ∧ (∀ i, U i i = 1) ∧
      E * U = U * diagonal (fun i => E i i) := by
  have hd : ∀ i, E i i * E i i = E i i := fun i => by rw [← flagF_diag_mul hE hE, hEE]
  have hDD : diagonal (fun i => E i i) * diagonal (fun i => E i i) = diagonal (fun i => E i i) := by
    rw [diagonal_mul_diagonal]; simp only [hd]
  have hD : (diagonal (fun i => E i i)).BlockTriangular id := blockTriangular_diagonal _
  have h1 : (1 : Matrix (Fin n) (Fin n) F).BlockTriangular id := blockTriangular_one
  refine ⟨E * diagonal (fun i => E i i) + (1 - E) * (1 - diagonal (fun i => E i i)),
    (hE.mul hD).add ((h1.sub hE).mul (h1.sub hD)), fun i => ?_, ?_⟩
  · rw [Matrix.add_apply, flagF_diag_mul hE hD, flagF_diag_mul (h1.sub hE) (h1.sub hD)]
    simp only [Matrix.sub_apply, diagonal_apply_eq, one_apply_eq]
    linear_combination 2 * hd i
  · generalize diagonal (fun i => E i i) = D at hDD
    have a1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hEE, sub_self]
    have a2 : (1 - D) * D = 0 := by rw [sub_mul, one_mul, hDD, sub_self]
    rw [mul_add, add_mul, ← mul_assoc, ← mul_assoc, hEE, a1, zero_mul, mul_assoc, mul_assoc, hDD, a2,
      mul_zero]

theorem UpperTheory.V.Pa.Det.flagF :
    ∀ {F H : Type} [Field F] [Infinite F] [Group H] {n a : ℕ} (r : H →* GL (Fin n) F) (ψ : Fin n → H →* Fˣ), (∀ g, mat r g ∈ Ev F F n a) → Function.Injective ψ → HasFlag r ψ → ∃ (w : GL (Fin n) F) (ty : Fin n → Bool), (∀ i j : Fin n, decide ((i : ℕ) < a) ≠ ty j → w i j = 0) ∧ ∀ g, (∀ i j, j < i → (w⁻¹ * r g * w : GL (Fin n) F) i j = 0) ∧ ∀ i, (w⁻¹ * r g * w : GL (Fin n) F) i i = (ψ i g : F) := by
  intro F H _ _ _ n a r ψ hev hinj ⟨g, hg⟩
  classical
  set e : Matrix (Fin n) (Fin n) F := diagonal fun i => if (i : ℕ) < a then 1 else 0 with he
  have hee : e * e = e := by
    rw [he, diagonal_mul_diagonal]; congr 1; ext i; split_ifs <;> simp
  have hce : ∀ s, (r s : Matrix (Fin n) (Fin n) F) * e = e * r s := by
    intro s
    ext i j
    rw [he, mul_diagonal, diagonal_mul]
    have h : ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → (r s : Matrix (Fin n) (Fin n) F) i j = 0 :=
      fun h => (Submodule.mem_bot F).1 ((hev s i j).2 h)
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] at h ⊢ <;> simp [h]
  set E : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) * e * (g⁻¹ : GL (Fin n) F) with hE
  have hEE : E * E = E := by
    simp only [hE, mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc e, hee]
  have hT : ∀ s, ((g * r s * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id :=
    fun s i j h => (hg s).1 i j h
  have hEt : E.BlockTriangular id := by
    refine flagF_tri (fun s => ((g * r s * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) E hT ?_ ?_
    · intro i j hij
      by_contra hcon
      push Not at hcon
      refine hij (hinj (MonoidHom.ext fun s => Units.ext ?_))
      rw [← (hg s).2 i, ← (hg s).2 j]
      exact hcon s
    · intro s
      simp only [hE, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
      rw [← mul_assoc (r s : Matrix (Fin n) (Fin n) F), hce, mul_assoc]
  obtain ⟨U, hU, hU1, hEU⟩ := flagF_diagonalise E hEt hEE
  have hdet : U.det ≠ 0 := by rw [det_of_upperTriangular hU]; simp [hU1]
  obtain ⟨u, rfl⟩ : ∃ u : GL (Fin n) F, (u : Matrix (Fin n) (Fin n) F) = U :=
    ⟨GeneralLinearGroup.mkOfDetNeZero U hdet, rfl⟩
  have hUi : ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id := by
    letI := u.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hU
  refine ⟨g⁻¹ * u, fun j => decide (E j j = 1), fun i j hij => ?_, fun s => ?_⟩
  · have h : e * ((g⁻¹ * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ((g⁻¹ * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * diagonal (fun i => E i i) := by
      rw [Units.val_mul, mul_assoc, ← hEU]
      simp only [hE, mul_assoc, Units.inv_mul_cancel_left]
    have h2 := congrFun (congrFun h i) j
    rw [he, mul_diagonal, diagonal_mul, mul_comm] at h2
    by_contra h0
    have h3 := mul_left_cancel₀ h0 h2
    apply hij
    by_cases hi : (i : ℕ) < a
    · simp [hi] at h3 ⊢; exact h3.symm
    · simp [hi] at h3 ⊢; simp [← h3]
  · have e1 : (g⁻¹ * u)⁻¹ * r s * (g⁻¹ * u) = u⁻¹ * ((g * r s * g⁻¹) * u) := by group
    have t1 : ((u⁻¹ * ((g * r s * g⁻¹) * u) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id := by
      rw [Units.val_mul, Units.val_mul]
      exact hUi.mul ((hT s).mul hU)
    rw [e1]
    refine ⟨fun i j h => t1 h, fun i => ?_⟩
    have h1 := flagF_diag_mul hU t1 i
    rw [← Units.val_mul, mul_inv_cancel_left, Units.val_mul, flagF_diag_mul (hT s) hU, hU1, mul_one,
      one_mul] at h1
    rw [← (hg s).2 i]
    exact h1.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.LatInt
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem exists_stable_lattice {A F G : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Group G] {m : ℕ} (r : G →* GL (Fin m) F) (d : A)
    (hd : d ≠ 0) (h : ∀ g i j, ∃ a : A, algebraMap A F d * r g i j = algebraMap A F a) :
    ∃ L : Submodule A (Fin m → F), Submodule.IsLattice F L ∧
      ∀ g, ∀ x ∈ L, (r g : Matrix (Fin m) (Fin m) F) *ᵥ x ∈ L := by
  classical
  let S : Set (Fin m → F) :=
    Set.range fun p : G × Fin m => (r p.1 : Matrix (Fin m) (Fin m) F) *ᵥ (Pi.single p.2 1)
  have hd' : algebraMap A F d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective A F)]
  refine ⟨Submodule.span A S, ⟨?_, ?_⟩, ?_⟩
  · let N : Submodule A (Fin m → F) :=
      Submodule.span A (Set.range fun i : Fin m => (Pi.single i (algebraMap A F d)⁻¹ : Fin m → F))
    have hN : N.FG := Submodule.fg_span (Set.finite_range _)
    refine hN.of_le ?_
    rw [Submodule.span_le]
    rintro _ ⟨⟨g, j⟩, rfl⟩
    choose a ha using h g
    have e : (r g : Matrix (Fin m) (Fin m) F) *ᵥ (Pi.single j 1) =
        ∑ i, a i j • (Pi.single i (algebraMap A F d)⁻¹ : Fin m → F) := by
      funext k
      simp only [Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_apply, Pi.smul_apply,
        Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Algebra.smul_def, ← ha]
      field_simp
    simp only [SetLike.mem_coe]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => N.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [eq_top_iff, ← (Pi.basisFun F (Fin m)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(1, i), by
      simp only [map_one, Units.val_one, Matrix.one_mulVec, Pi.basisFun_apply]⟩
  · intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g', i⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * g', i), by
        simp only [map_mul, Units.val_mul, Matrix.mulVec_mulVec]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx

theorem UpperTheory.V.Pa.Det.latInt :
    ∀ {A F G : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F] [Algebra A F] [IsFractionRing A F] [Group G] {m : ℕ} (r : G →* GL (Fin m) F) (d : A), d ≠ 0 → (∀ g i j, ∃ a : A, algebraMap A F d * r g i j = algebraMap A F a) → ∃ (Q : GL (Fin m) F) (r₀ : G →* GL (Fin m) A), ∀ g, r g * Q = Q * pushRep (algebraMap A F) r₀ g := by
  intro A F G _ _ _ _ _ _ _ m r d hd h
  classical
  obtain ⟨L, hL, hst⟩ := exists_stable_lattice r d hd h
  have hr : Module.finrank A L = m := by
    simpa using Submodule.IsLattice.finrank_of_pi F L
  let bL : Module.Basis (Fin m) A L := Module.finBasisOfFinrankEq A L hr
  let b : Module.Basis (Fin m) F (Fin m → F) := bL.extendOfIsLattice F
  let Q₀ : Matrix (Fin m) (Fin m) F := (Pi.basisFun F (Fin m)).toMatrix b
  have hQ : IsUnit Q₀ := by
    letI := (Pi.basisFun F (Fin m)).invertibleToMatrix b
    exact isUnit_of_invertible _
  have hQa : ∀ i j, Q₀ i j = (bL j : Fin m → F) i := fun i j => by
    simp [Q₀, b, Module.Basis.toMatrix_apply]
  let M : G → Matrix (Fin m) (Fin m) A := fun g k j => bL.repr ⟨_, hst g _ (bL j).2⟩ k
  have hM : ∀ g, (r g : Matrix (Fin m) (Fin m) F) * Q₀ = Q₀ * (M g).map (algebraMap A F) := by
    intro g
    ext i j
    have e := congrArg (fun x : L => (x : Fin m → F) i) (bL.sum_repr ⟨_, hst g _ (bL j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      Algebra.smul_def] at e
    simp only [Matrix.mul_apply, hQa, Matrix.map_apply]
    refine Eq.trans e.symm ?_
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have inj : ∀ X Y : Matrix (Fin m) (Fin m) A,
      Q₀ * X.map (algebraMap A F) = Q₀ * Y.map (algebraMap A F) → X = Y := fun X Y hXY =>
    Matrix.map_injective (IsFractionRing.injective A F) (hQ.mul_left_cancel hXY)
  let M' : G →* Matrix (Fin m) (Fin m) A :=
    { toFun := M
      map_one' := inj _ _ (by rw [← hM]; simp)
      map_mul' := fun g g' => inj _ _ (by
        rw [← hM, Matrix.map_mul, ← mul_assoc, ← hM, mul_assoc, ← hM, map_mul, Units.val_mul,
          mul_assoc]) }
  refine ⟨hQ.unit, M'.toHomUnits, fun g => Units.ext ?_⟩
  exact hM g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.LocallyConstantCocyclesFiniteOfPhi
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem eq_zero_of_forall_hom_zmod_eq_zero_of_module_zmod {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] [Module (ZMod l) M] (v : M)
    (hv : ∀ f : M →+ ZMod l, f v = 0) : v = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod l)]
  intro f
  exact hv (LinearMap.toAddMonoidHom f)

theorem UpperTheory.V.Pa.Det.locallyConstant_cocycles_finite_of_phi :
    ∀ (l : ℕ) [Fact l.Prime] {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [AddCommGroup M] [Finite M] (ρ : G →* AddMonoid.End M), PhiCond G l → (∀ m : M, l • m = 0) → (∀ m, IsLocallyConstant fun g => ρ g m) → {z : G → M | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g (z h)}.Finite := by
  intro l _ G M _ _ _ _ _ _ _ ρ hΦ hl hc
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  set S := {z : G → M | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g (z h)} with hS
  have hker : IsOpen (ρ.ker : Set G) := by
    have he : (ρ.ker : Set G) = ⋂ m, {g | ρ g m = m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        ext m
        exact h m
    rw [he]
    exact isOpen_iInter_of_finite fun m => (hc m).isOpen_fiber m
  haveI : Finite (G ⧸ ρ.ker) := Subgroup.quotient_finite_of_isOpen _ hker
  haveI := hΦ ρ.ker hker
  haveI : Finite (M →+ ZMod l) :=
    Finite.of_injective (fun f : M →+ ZMod l => (⇑f : M → ZMod l))
      (fun a b hab => AddMonoidHom.ext (congrFun hab))
  have h1 : ∀ z ∈ S, z 1 = 0 := by
    intro z hz
    have h11 : z 1 = z 1 + z 1 := by
      have := hz.2 1 1
      rw [one_mul, map_one] at this
      exact this
    exact add_left_cancel (h11.symm.trans (add_zero _).symm)
  have hH : ∀ z ∈ S, ∀ a b : G, a ∈ ρ.ker → z (a * b) = z a + z b := by
    intro z hz a b ha
    rw [hz.2, MonoidHom.mem_ker.mp ha]
    rfl
  let φ : ∀ z ∈ S, (M →+ ZMod l) →
      {φ : ρ.ker →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set ρ.ker)} := fun z hz f =>
    ⟨{ toFun := fun h => Multiplicative.ofAdd (f (z h))
       map_one' := by simp [h1 z hz]
       map_mul' := fun a b => by simp [hH z hz a b a.2, ofAdd_add] },
     by
       have hlc : IsLocallyConstant (fun h : ρ.ker => Multiplicative.ofAdd (f (z h))) :=
         (hz.1.comp_continuous continuous_subtype_val).comp _
       exact hlc.isOpen_fiber 1⟩
  let F : S → ((G ⧸ ρ.ker) → M) × ((M →+ ZMod l) →
      {φ : ρ.ker →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set ρ.ker)}) :=
    fun z => (fun q => z.1 (Quotient.out q), φ z.1 z.2)
  have hinj : Function.Injective F := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
    have hq : (fun q : G ⧸ ρ.ker => z (Quotient.out q)) = fun q => z' (Quotient.out q) := congrArg Prod.fst hzz
    have hf : φ z hz = φ z' hz' := congrArg Prod.snd hzz
    have hHeq : ∀ h ∈ ρ.ker, z h = z' h := by
      intro h hh
      rw [← sub_eq_zero]
      apply @eq_zero_of_forall_hom_zmod_eq_zero_of_module_zmod l _ M _ (AddCommGroup.zmodModule hl)
      intro f
      have hx := congrArg (fun p => (p.1 ⟨h, hh⟩ : Multiplicative (ZMod l))) (congrFun hf f)
      change Multiplicative.ofAdd (f (z h)) = Multiplicative.ofAdd (f (z' h)) at hx
      rw [map_sub, sub_eq_zero]
      exact Multiplicative.ofAdd.injective hx
    apply Subtype.ext
    funext g
    show z g = z' g
    obtain ⟨h0, hh0⟩ := QuotientGroup.mk_out_eq_mul ρ.ker g
    have hg : g = Quotient.out (g : G ⧸ ρ.ker) * (h0 : G)⁻¹ := by
      rw [hh0, mul_inv_cancel_right]
    have hr := congrFun hq (g : G ⧸ ρ.ker)
    rw [hg, hz.2, hz'.2, hr, hHeq _ (inv_mem h0.2)]
  exact Set.finite_coe_iff.mp (Finite.of_injective F hinj)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.MapSpan
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem mem_ev_iff_apply_eq_zero_off_diagonal_blocks {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (n a : ℕ)
    (Z : Matrix (Fin n) (Fin n) R) :
    Z ∈ Ev A R n a ↔ ∀ i j : Fin n, ¬((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j = 0 := by
  constructor
  · intro h i j hij
    exact (Submodule.mem_bot A).1 ((h i j).2 hij)
  · intro h i j
    exact ⟨fun _ => Submodule.mem_top, fun hij => by rw [h i j hij]; exact Submodule.zero_mem _⟩

theorem UpperTheory.V.Pa.Det.detFr :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n), l ≠ 2 → (∃ g : F.G₀, PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → ∃ D : DetFr (FractionRing x.A) F.G₀ n, D.a = x.a ∧ D.G' = F.G' ∧ (∀ g, D.r g = x.ρX (FractionRing x.A) g) ∧ D.σ = F.conj ∧ ∀ g : F.G₀, D.χF g = algebraMap x.A (FractionRing x.A) (algebraMap ℤ_[l] x.A (F.ε g : ℤ_[l])) := by
  intro l _ F n x hl hg
  obtain ⟨g₀, hg₀⟩ := hg
  have hev : ∀ g : F.G₀, (mat x.ρ g).map (algebraMap x.A (FractionRing x.A)) ∈
      Ev (FractionRing x.A) (FractionRing x.A) n x.a := by
    intro g
    rw [mem_ev_iff_apply_eq_zero_off_diagonal_blocks]
    intro i j hij
    have h0 := (mem_ev_iff_apply_eq_zero_off_diagonal_blocks _ _ _).1 (x.blk g) i j hij
    rw [Matrix.map_apply, h0, map_zero]
  have hmap : ∀ M ∈ Submodule.span x.A ((mat x.ρ) '' (F.G' : Set F.G₀)),
      M.map (algebraMap x.A (FractionRing x.A)) ∈ Submodule.span (FractionRing x.A)
        ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, hg, rfl⟩ := hM
      exact Submodule.subset_span ⟨g, hg, rfl⟩
    | zero =>
      have h0 : (0 : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A (FractionRing x.A)) = 0 := by
        ext i j
        simp
      rw [h0]
      exact Submodule.zero_mem _
    | add M N _ _ hM hN =>
      have h0 : (M + N).map (algebraMap x.A (FractionRing x.A)) =
          M.map (algebraMap x.A (FractionRing x.A)) + N.map (algebraMap x.A (FractionRing x.A)) := by
        ext i j
        simp
      rw [h0]
      exact Submodule.add_mem _ hM hN
    | smul c M _ hM =>
      have h0 : (c • M).map (algebraMap x.A (FractionRing x.A)) =
          algebraMap x.A (FractionRing x.A) c • M.map (algebraMap x.A (FractionRing x.A)) := by
        ext i j
        simp
      rw [h0]
      exact Submodule.smul_mem _ _ hM
  have hsingle : ∀ i j : Fin n, ((i : ℕ) < x.a ↔ (j : ℕ) < x.a) →
      Matrix.single i j (1 : FractionRing x.A) ∈ Submodule.span (FractionRing x.A)
        ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) := by
    intro i j hij
    have hZ : Matrix.single i j (1 : x.A) ∈ Ev x.A x.A n x.a := by
      rw [mem_ev_iff_apply_eq_zero_off_diagonal_blocks]
      intro k m hkm
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hkm hij
    obtain ⟨s, hs⟩ := x.span _ hZ
    have key := hmap _ hs
    have h1 : ((PowerSeries.X : x.A) ^ s • Matrix.single i j (1 : x.A)).map
        (algebraMap x.A (FractionRing x.A)) =
        algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s) • Matrix.single i j (1 : FractionRing x.A) := by
      ext k m
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [h1] at key
    have hne : algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s) ≠ 0 := by
      intro h
      apply pow_ne_zero s (PowerSeries.X_ne_zero (R := x.K))
      apply IsFractionRing.injective x.A (FractionRing x.A)
      rw [h, map_zero]
    have h2 := Submodule.smul_mem _ (algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s))⁻¹ key
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  have hspan : Submodule.span (FractionRing x.A)
      ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) =
      Ev (FractionRing x.A) (FractionRing x.A) n x.a := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, -, rfl⟩
      exact hev g
    · intro Z hZ
      rw [Matrix.matrix_eq_sum_single Z]
      refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => ?_))
      by_cases hij : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)
      · have h3 : Matrix.single i j (Z i j) = Z i j • Matrix.single i j (1 : FractionRing x.A) := by
          rw [Matrix.smul_single, smul_eq_mul, mul_one]
        rw [h3]
        exact Submodule.smul_mem _ _ (hsingle i j hij)
      · rw [(mem_ev_iff_apply_eq_zero_off_diagonal_blocks _ _ _).1 hZ i j hij, Matrix.single_zero]
        exact Submodule.zero_mem _
  have h2 : IsUnit (2 : ℤ_[l]) := by
    by_contra h
    have hm : (2 : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal _).2 h
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hm
    have h4 : ((2 : ℕ) : ZMod l) = 0 := by
      rw [Nat.cast_ofNat, ← hm, map_ofNat]
    have h5 : l ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).1 h4
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h5)
  have hc : ∀ g : F.G₀, F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ) := by
    intro g
    show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = F.ε (g : F.Γ)
    rw [map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_inv_cancel_right]
  refine ⟨DetFr.mk ?_ x.a x.a_pos x.a_le F.G' ?_ (F.eps x.A (FractionRing x.A)) ?_ g₀ ?_
    ((algebraMap x.A (FractionRing x.A)).mapMatrix.toMonoidHom.comp (mat x.ρ)) hspan hev F.conj ?_ ?_
    (fun g => Units.map (algebraMap x.A (FractionRing x.A)).toMonoidHom
      ((F.eps ℤ_[l] x.A g) ^ (1 - (n : ℤ)))) ?_, rfl, rfl, fun g => rfl, rfl, fun g => rfl⟩
  · have h6 := (h2.map ((algebraMap x.A (FractionRing x.A)).comp (algebraMap ℤ_[l] x.A))).ne_zero
    rw [RingHom.comp_apply, map_ofNat, map_ofNat] at h6
    exact h6
  · intro g h
    rw [GFrame.G', MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul, mul_comm]
  · intro g hg
    rw [GFrame.G', MonoidHom.mem_ker] at hg
    show Units.map _ ((F.ε.comp F.η.ker.subtype) g) = 1
    rw [hg, map_one]
  · intro h
    apply hg₀
    have h7 := congrArg Units.val h
    change algebraMap x.A (FractionRing x.A) (algebraMap ℤ_[l] x.A ((F.ε g₀ : ℤ_[l]ˣ) : ℤ_[l])) = 1 at h7
    have h8 : ((F.ε g₀ : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈
        RingHom.ker ((algebraMap x.A (FractionRing x.A)).comp (algebraMap ℤ_[l] x.A)) := by
      rw [RingHom.mem_ker, map_sub, RingHom.comp_apply, h7, map_one, sub_self]
    have h9 := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) h8
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h9
    exact h9
  · intro g
    apply Subtype.ext
    show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = (g : F.Γ)
    calc F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = (F.c * F.c) * (g : F.Γ) * (F.c * F.c)⁻¹ := by group
      _ = (g : F.Γ) := by rw [F.c_sq]; group
  · intro g
    show Units.map _ ((F.ε.comp F.η.ker.subtype) (F.conj g)) = Units.map _ ((F.ε.comp F.η.ker.subtype) g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact congrArg _ (hc g)
  · intro g
    show ((mat x.ρ g).map (algebraMap x.A (FractionRing x.A)))ᵀ *
        (mat x.ρ (F.conj g)).map (algebraMap x.A (FractionRing x.A)) =
        (algebraMap x.A (FractionRing x.A) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A)) • 1
    have h0 := x.form g
    rw [Units.val_one, Matrix.mul_one] at h0
    rw [← Matrix.transpose_map, ← Matrix.map_mul, h0]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
end

