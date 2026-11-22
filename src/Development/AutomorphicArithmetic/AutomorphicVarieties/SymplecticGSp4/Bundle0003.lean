import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0052

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompMap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

section

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem adj_map' (f : R →+* R') (X : M4 R) : adj (f.mapMatrix X) = f.mapMatrix (adj X) := by
  ext i j
  simp [adj_apply, RingHom.mapMatrix_apply]

private theorem smul_map' (f : R →+* R') (a : R) (X : M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp [RingHom.mapMatrix_apply]

private theorem isGSp_map (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) : IsGSp (f ν) (f.mapMatrix g) := by
  unfold IsGSp at h ⊢
  have h2 := congrArg f.mapMatrix h
  rw [map_mul, smul_map', map_one, ← adj_map'] at h2
  exact h2

private theorem aeval_map' (f : R →+* R') (X : M4 R) (p : Polynomial R) :
    Polynomial.aeval (f.mapMatrix X) (p.map f) = f.mapMatrix (Polynomial.aeval X p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, hp, hq, map_add]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp

private theorem prj_map (f : R →+* R') (c : Fin 4 → R) (X : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix X) i = f.mapMatrix (prj c X i) := by
  simp only [prj]
  rw [← aeval_map']
  congr 1
  simp [Polynomial.map_prod]

private theorem ord_map {H : Type} [Group H] (f : R →+* R') {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H}
    {r : H →* M4 R} {r' : H →* M4 R'} (hr : ∀ g, r' g = f.mapMatrix (r g)) {ps' : Fin 4 → H → R'}
    (hps : ∀ i g, ps' i g = f (ps i g)) (h : Ord I ps s₀ r) : Ord I ps' s₀ r' := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hr, hps]
    rw [RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod]
    simp
  · intro g i j hij
    simp only [hr, hps]
    rw [prj_map, prj_map, ← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · intro s hs i
    simp only [hr, hps]
    have e : f.mapMatrix (r s) - f (ps i s) • (1 : M4 R') = f.mapMatrix (r s - ps i s • 1) := by
      rw [map_sub, smul_map', map_one]
    rw [prj_map, e, ← map_mul, ← map_mul, h.inert s hs i, map_zero]

end

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] {R' : Type} [CommRing R'] [Algebra c.O R'] [IsCO c.O R']

private theorem condL_map (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt l) R) (h : D.condL R ρ) :
    D.condL R' (ρ.map f) := by
  unfold Raw.condL at h ⊢
  obtain ⟨h1, h2⟩ := h
  have hr : ∀ g, (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := by
    intro g
    ext a b
    rw [Lift.map_hom]
    rfl
  refine ⟨fun g => ?_, ord_map (f : R →+* R') hr (fun i g => (f.commutes _).symm) h2⟩
  rw [hr, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h1 g)

private theorem condP_map (p : ℕ) (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt p) R) (h : D.condP p R ρ) :
    D.condP p R' (ρ.map f) := by
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · have := isGSp_map (f : R →+* R') (h.1 g)
    rw [RingHom.coe_coe, f.commutes] at this
    exact this
  · show (f : R →+* R').mapMatrix (ρ.hom g) = 1
    rw [h.2 g hg, map_one]

private theorem mult_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Mult ρ.hom) : D.Mult (ρ.map f).hom := by
  intro g
  have hr : (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := by
    ext a b
    rw [Lift.map_hom]
    rfl
  rw [hr, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h g)

private theorem unr_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.UnrT ρ.hom 1) :
    D.UnrT (ρ.map f).hom 1 := by
  intro A hA g hg h1
  show (f : R →+* R').mapMatrix (ρ.hom g) = 1
  rw [h A hA g hg h1, map_one]

private theorem hEl_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (i j : Fin 4) :
    D.hEl (ρ.map f).hom i j = f (D.hEl ρ.hom i j) := by
  simp [Raw.hEl, Lift.map_hom, map_add, map_mul, f.commutes]

private theorem loc_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (v : ℕ) :
    D.loc (ρ.map f) v = (D.loc ρ v).map f := by
  apply Lift.ext
  rfl

private theorem nrm_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Nrm ρ.hom) : D.Nrm (ρ.map f).hom := by
  refine ⟨fun i j hij => ?_, ?_, ?_⟩
  · rw [Lift.map_hom, h.1 i j hij, map_zero]
  · rw [hEl_map, h.2.1, map_zero]
  · rw [hEl_map, h.2.2, map_zero]

end

private theorem onComp_map {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ]
    [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)} {P : Cond O rbar} {ρ₀ : Γ →* Matrix ι ι O}
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R']
    (f : R →ₐ[O] R') {r : Lift O rbar R} (h : OnComp P ρ₀ r) : OnComp P ρ₀ (r.map f) := by
  obtain ⟨B, i1, i2, i3, i4, ρ', hP, hρ, y, hy⟩ := h
  refine ⟨B, i1, i2, i3, i4, ρ', hP, hρ, f.comp y, ?_⟩
  subst hy
  apply Lift.ext
  ext g a b
  simp [Lift.map_hom]

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptMap :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : Lift c.O D.rbar R), (D.IsPt ρ → D.IsEq ρ) ∧ ∀ (R' : Type) [CommRing R'] [Algebra c.O R'] [IsCO c.O R'] (f : R →ₐ[c.O] R'), (D.IsPt ρ → D.IsPt (ρ.map f)) ∧ (D.IsEq ρ → D.IsEq (ρ.map f)) := by
  intro Ω _ _ _ l _ c D _ R _ _ _ ρ
  have hL : ∀ {S : Type} [CommRing S] [Algebra c.O S] [IsCO c.O S] (r : Lift c.O (D.rbarAt l) S),
      OnComp D.condL (D.r0At l) r → D.condL S r := by
    intro S _ _ _ r hr
    obtain ⟨B, i1, i2, i3, i4, ρ', hP, _, y, rfl⟩ := hr
    exact condL_map D y ρ' hP
  have hP : ∀ (p : ℕ) {S : Type} [CommRing S] [Algebra c.O S] [IsCO c.O S] (r : Lift c.O (D.rbarAt p) S),
      OnComp (D.condP p) (D.r0At p) r → D.condP p S r := by
    intro p S _ _ _ r hr
    obtain ⟨B, i1, i2, i3, i4, ρ', hQ, _, y, rfl⟩ := hr
    exact condP_map D p y ρ' hQ
  refine ⟨fun h => ⟨h.mult, h.unr, h.nrm, hL _ h.atL, fun p hp => hP p _ (h.atP p hp)⟩, ?_⟩
  intro R' _ _ _ f
  refine ⟨fun h => ⟨mult_map D f ρ h.mult, unr_map D f ρ h.unr, nrm_map D f ρ h.nrm, ?_, fun p hp => ?_⟩,
    fun h => ⟨mult_map D f ρ h.mult, unr_map D f ρ h.unr, nrm_map D f ρ h.nrm, ?_, fun p hp => ?_⟩⟩
  · rw [loc_map]
    exact onComp_map f h.atL
  · rw [loc_map]
    exact onComp_map f (h.atP p hp)
  · rw [loc_map]
    exact condL_map D f _ h.atL
  · rw [loc_map]
    exact condP_map D p f _ (h.atP p hp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OrdFlag
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.ordFlag_diag {K : Type} [Field K] (c : Fin 4 → K) (hc : Function.Injective c) (X : M4 K)
    (h : X.charpoly = ∏ j, (Polynomial.X - Polynomial.C (c j))) :
    ∃ P : (M4 K)ˣ, X * (P : M4 K) = (P : M4 K) * Matrix.diagonal c :=
  _root_.UpperTheory.Reformulated.B.OrderedFlagDiagonal.ordFlag_diag c hc X h

private theorem UpperTheory.V.GradeZeroInterpolatingElement.ordFlag_aeval {K : Type} [Field K] (c : Fin 4 → K) (X P : M4 K)
    (h : X * P = P * Matrix.diagonal c) (p : Polynomial K) :
    Polynomial.aeval X p * P = P * Matrix.diagonal fun k => p.eval (c k) := by
  induction p using Polynomial.induction_on with
  | C a =>
    ext i j
    simp [Matrix.mul_diagonal, Algebra.algebraMap_eq_smul_one, mul_comm]
  | add p q hp hq =>
    rw [map_add, add_mul, hp, hq, ← mul_add, Matrix.diagonal_add]
    simp
  | monomial n a hn =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, mul_assoc, h, ← mul_assoc, hn, mul_assoc,
      Matrix.diagonal_mul_diagonal]
    simp

theorem UpperTheory.V.GradeZeroInterpolatingElement.ordFlag :
    ∀ {H : Type} [Group H] (I : Subgroup H) (K : Type) [Field K] (ps : Fin 4 → H → K) (s₀ : H) (r : H →* M4 K), Function.Injective (fun i => ps i s₀) → Ord I ps s₀ r → ∃ (u : (M4 K)ˣ) (κ : Fin 4 → H →* Kˣ), (∀ g i j, j < i → ((u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ)) i j = 0) ∧ (∀ g i, ((u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ)) i i = κ i g) ∧ (∀ i, ∀ s ∈ I, (κ i s : K) = ps i s) ∧ ∀ i g, (∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀)) * (κ i g : K) = (prj (fun a => ps a s₀) (r s₀) i * r g).trace := by
  intro H _ I K _ ps s₀ r hc ho
  obtain ⟨P, hP⟩ := ordFlag_diag _ hc (r s₀) ho.charpoly
  set d : Fin 4 → K := fun i => ∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀) with hd
  have hd0 : ∀ i, d i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr fun e => (Finset.mem_erase.mp hj).1 (hc e).symm
  have hprj : ∀ i, prj (fun a => ps a s₀) (r s₀) i
      = (P : M4 K) * Matrix.diagonal (Pi.single i (d i)) * ((P⁻¹ : (M4 K)ˣ) : M4 K) := by
    intro i
    rw [Units.eq_mul_inv_iff_mul_eq, prj, ordFlag_aeval _ _ _ hP]
    congr 2
    funext k
    rw [Polynomial.eval_prod]
    by_cases hk : k = i
    · subst hk; simp [hd]
    · rw [Pi.single_eq_of_ne hk]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (by simp)
  have key : ∀ (Y : M4 K) i j, prj (fun a => ps a s₀) (r s₀) i * Y * prj (fun a => ps a s₀) (r s₀) j = 0 →
      (((P⁻¹ : (M4 K)ˣ) : M4 K) * Y * (P : M4 K)) i j = 0 := by
    intro Y i j h
    have h2 : Matrix.diagonal (Pi.single i (d i)) * (((P⁻¹ : (M4 K)ˣ) : M4 K) * Y * (P : M4 K)) *
        Matrix.diagonal (Pi.single j (d j)) = 0 := by
      have := congrArg (fun Z : M4 K => ((P⁻¹ : (M4 K)ˣ) : M4 K) * Z * (P : M4 K)) h
      simpa [hprj, mul_assoc] using this
    have h3 := congrFun (congrFun h2 i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h3
    simpa [hd0] using h3
  set M : H → M4 K := fun g => ((P⁻¹ : (M4 K)ˣ) : M4 K) * r g * (P : M4 K) with hM
  have htri : ∀ g i j, j < i → M g i j = 0 := fun g i j hij => key _ i j (ho.stable g j i hij)
  have hmul : ∀ g h, M (g * h) = M g * M h := by
    intro g h
    simp [hM, mul_assoc]
  let κ₀ : Fin 4 → H →* K := fun i =>
    { toFun := fun g => M g i i
      map_one' := by simp [hM]
      map_mul' := by
        intro g h
        rw [hmul, Matrix.mul_apply]
        refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
        rcases lt_or_gt_of_ne hk with hk | hk
        · rw [htri g i k hk, zero_mul]
        · rw [htri h k i hk, mul_zero] }
  refine ⟨P⁻¹, fun i => (κ₀ i).toHomUnits, ?_, ?_, ?_, ?_⟩
  · intro g i j hij
    rw [inv_inv]
    exact htri g i j hij
  · intro g i
    rw [inv_inv]
    rfl
  · intro i s hs
    have h1 := key _ i i (ho.inert s hs i)
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, Units.inv_mul, Matrix.sub_apply, sub_eq_zero] at h1
    show M s i i = _
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
    exact h1
  · intro i g
    show d i * M g i i = _
    rw [hprj, mul_assoc, mul_assoc, Matrix.trace_mul_comm, mul_assoc]
    show _ = (Matrix.diagonal (Pi.single i (d i)) * M g).trace
    simp [Matrix.trace, Matrix.diagonal_mul, Pi.single_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OrdLocal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement.OrdinaryLocal

open Polynomial

variable {B : Type} [CommRing B]

private theorem aeval_conj (u : (M4 B)ˣ) (X : M4 B) (p : B[X]) :
    aeval ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) p = (u : M4 B) * aeval X p * (u⁻¹ : (M4 B)ˣ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, add_mul]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Units.conj_pow, ← Algebra.smul_def, ← Algebra.smul_def, mul_smul_comm,
      smul_mul_assoc]

private theorem prj_conj (c : Fin 4 → B) (u : (M4 B)ˣ) (X : M4 B) (i : Fin 4) :
    prj c ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) i = (u : M4 B) * prj c X i * (u⁻¹ : (M4 B)ˣ) :=
  aeval_conj u X _

private theorem eig_left (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) :
    (X - c i • (1 : M4 B)) * prj c X i = 0 := by
  have h1 := Matrix.aeval_self_charpoly X
  rw [h, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] at h1
  exact h1

private theorem eig_right (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) :
    prj c X i * (X - c i • (1 : M4 B)) = 0 := by
  have h1 := Matrix.aeval_self_charpoly X
  rw [h, ← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i), map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] at h1
  exact h1

private theorem aeval_sub (X : M4 B) (a : B) (p : B[X]) :
    ∃ Y : M4 B, aeval X p - p.eval a • (1 : M4 B) = Y * (X - a • (1 : M4 B)) := by
  obtain ⟨s, hs⟩ : Polynomial.X - C a ∣ p - C (p.eval a) := X_sub_C_dvd_sub_C_eval
  refine ⟨aeval X s, ?_⟩
  have h := congrArg (aeval X) hs
  rw [mul_comm, map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one] at h
  exact h

private theorem prj_sub (c : Fin 4 → B) (X : M4 B) (i j : Fin 4) :
    ∃ Y : M4 B, prj c X i - (∏ a ∈ Finset.univ.erase i, (c j - c a)) • (1 : M4 B) = Y * (X - c j • (1 : M4 B)) := by
  obtain ⟨Y, hY⟩ := aeval_sub X (c j) (∏ a ∈ Finset.univ.erase i, (Polynomial.X - C (c a)))
  refine ⟨Y, ?_⟩
  rw [← hY, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rfl

private theorem prj_mul (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i j : Fin 4) :
    prj c X i * prj c X j = (∏ a ∈ Finset.univ.erase i, (c j - c a)) • prj c X j := by
  obtain ⟨Y, hY⟩ := prj_sub c X i j
  have h1 := congrArg (· * prj c X j) hY
  simp only [mul_assoc, eig_left c X h j, mul_zero, sub_mul, smul_mul_assoc, one_mul] at h1
  exact sub_eq_zero.mp h1

private theorem unit_d (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (i : Fin 4) :
    IsUnit (∏ a ∈ Finset.univ.erase i, (c i - c a)) :=
  IsUnit.prod_iff.mpr fun a ha => hc i a (Finset.ne_of_mem_erase ha).symm

private theorem zero_d (c : Fin 4 → B) {i j : Fin 4} (hij : j ≠ i) :
    (∏ a ∈ Finset.univ.erase i, (c j - c a)) = 0 :=
  Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩) (sub_self _)

private theorem det_eig (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) :
    (X - c i • (1 : M4 B)).det = 0 := by
  have h1 := Matrix.eval_charpoly X (c i)
  rw [h, eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp)] at h1
  have h2 : X - c i • (1 : M4 B) = -(Matrix.scalar (Fin 4) (c i) - X) := by
    rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [h2, Matrix.det_neg, ← h1, mul_zero]

private theorem exists_unit [IsLocalRing B] (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (X : M4 B)
    (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) : ∃ ab : Fin 4 × Fin 4, IsUnit (prj c X i ab.1 ab.2) := by
  by_contra hn
  push Not at hn
  obtain ⟨Y, hY⟩ := prj_sub c X i i
  have h1 := congrArg Matrix.det hY
  rw [Matrix.det_mul, det_eig c X h i, mul_zero] at h1
  have h2 := congrArg (residue B) h1
  set d := ∏ a ∈ Finset.univ.erase i, (c i - c a) with hd
  have h3 : (residue B).mapMatrix (prj c X i - d • (1 : M4 B)) = Matrix.diagonal fun _ => -residue B d := by
    ext a b
    have h0 : residue B (prj c X i a b) = 0 := (residue_eq_zero_iff _).mpr (hn (a, b))
    by_cases hab : a = b
    · subst hab; simp [h0]
    · simp [h0, hab]
  rw [RingHom.map_det, h3, Matrix.det_diagonal, map_zero, Finset.prod_eq_zero_iff] at h2
  obtain ⟨_, -, h4⟩ := h2
  exact ((unit_d c hc i).map (residue B)).ne_zero (neg_eq_zero.mp h4)

private theorem diagonalize [IsLocalRing B] (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (X : M4 B)
    (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) :
    ∃ u : (M4 B)ˣ, (u : M4 B) * X * (u⁻¹ : (M4 B)ˣ) = Matrix.diagonal c := by
  choose ab hab using exists_unit c hc X h
  let P : M4 B := Matrix.of fun x j => prj c X j x (ab j).2
  let Q : M4 B := Matrix.of fun i x => prj c X i (ab i).1 x
  have hQP : Q * P = Matrix.diagonal fun i => (∏ a ∈ Finset.univ.erase i, (c i - c a)) * prj c X i (ab i).1 (ab i).2 := by
    ext i j
    have h1 : (Q * P) i j = (prj c X i * prj c X j) (ab i).1 (ab j).2 := rfl
    rw [h1, prj_mul c X h]
    by_cases hij : i = j
    · subst hij; simp
    · rw [zero_d c (Ne.symm hij), Matrix.diagonal_apply_ne _ hij]; simp
  have hdet : IsUnit (Q * P).det := by
    rw [hQP, Matrix.det_diagonal]
    exact IsUnit.prod_iff.mpr fun a _ => (unit_d c hc a).mul (hab a)
  rw [Matrix.det_mul] at hdet
  obtain ⟨v, hv⟩ := (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_of_mul_isUnit_right hdet)
  have hXP : X * P = P * Matrix.diagonal c := by
    ext x j
    have h1 : (X * P) x j = (X * prj c X j) x (ab j).2 := rfl
    have h2 := eig_left c X h j
    rw [sub_mul, sub_eq_zero, smul_mul_assoc, one_mul] at h2
    rw [h1, h2, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
    rfl
  refine ⟨v⁻¹, ?_⟩
  rw [inv_inv, mul_assoc, hv, hXP, ← hv, Units.inv_mul_cancel_left]

private theorem prj_diag (c : Fin 4 → B) (i : Fin 4) :
    prj c (Matrix.diagonal c) i = Matrix.diagonal fun x => ∏ a ∈ Finset.univ.erase i, (c x - c a) := by
  have h1 : Matrix.diagonal c = Matrix.diagonalAlgHom B c := rfl
  unfold prj
  rw [h1, aeval_algHom_apply]
  show Matrix.diagonal _ = _
  congr 1
  funext x
  rw [map_prod, Finset.prod_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp

private theorem sandwich (c : Fin 4 → B) (u : (M4 B)ˣ) (X Y : M4 B) (i j : Fin 4) :
    prj c ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) j * ((u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ)) *
      prj c ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) i = (u : M4 B) * (prj c X j * Y * prj c X i) * (u⁻¹ : (M4 B)ˣ) := by
  rw [prj_conj, prj_conj]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

private theorem entry_zero (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (u : (M4 B)ˣ) (X Y : M4 B)
    (hu : (u : M4 B) * X * (u⁻¹ : (M4 B)ˣ) = Matrix.diagonal c) (i j : Fin 4) (h : prj c X j * Y * prj c X i = 0) :
    ((u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ)) j i = 0 := by
  have h1 := sandwich c u X Y i j
  rw [h, mul_zero, zero_mul, hu, prj_diag, prj_diag] at h1
  have h2 := congrFun (congrFun h1 j) i
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply, (unit_d c hc i).mul_left_eq_zero,
    (unit_d c hc j).mul_right_eq_zero] at h2
  exact h2

private theorem row_zero (T P : M4 B) (hT : ∀ i j, j < i → T i j = 0) (hP : T * P = 0) (i : Fin 4)
    (hu : ∀ a, i < a → IsUnit (T a a)) (b a : Fin 4) : i < a → P a b = 0 := by
  induction a using WellFoundedGT.induction with
  | ind a ih =>
    intro ha
    have h1 := congrFun (congrFun hP a) b
    rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.zero_apply, (hu a ha).mul_right_eq_zero] at h1
    · exact h1
    · intro x _ hx
      rcases lt_or_gt_of_ne hx with h | h
      · rw [hT a x h, zero_mul]
      · rw [ih x h (ha.trans h), mul_zero]
    · simp

private theorem col_zero (T P : M4 B) (hT : ∀ i j, j < i → T i j = 0) (hP : P * T = 0) (i : Fin 4)
    (hu : ∀ a, a < i → IsUnit (T a a)) (b a : Fin 4) : a < i → P b a = 0 := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro ha
    have h1 := congrFun (congrFun hP b) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.zero_apply, (hu a ha).mul_left_eq_zero] at h1
    · exact h1
    · intro x _ hx
      rcases lt_or_gt_of_ne hx with h | h
      · rw [ih x h (h.trans ha), zero_mul]
      · rw [hT x a h, mul_zero]
    · simp

private theorem charpoly_tri (c : Fin 4 → B) (T : M4 B) (hT : ∀ i j, j < i → T i j = 0) (hd : ∀ i, T i i = c i) :
    T.charpoly = ∏ j, (Polynomial.X - C (c j)) := by
  rw [Matrix.charpoly_of_upperTriangular T (fun i j h => hT i j h)]
  simp only [hd]

private theorem tri_zero (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (T R : M4 B)
    (hT : ∀ i j, j < i → T i j = 0) (hd : ∀ i, T i i = c i) (hR : ∀ i j, j < i → R i j = 0) (i j : Fin 4) (hij : i ≤ j)
    (h0 : R j i = 0) : prj c T j * R * prj c T i = 0 := by
  have hch := charpoly_tri c T hT hd
  have hT' : ∀ k i j, j < i → (T - c k • (1 : M4 B)) i j = 0 := fun k i j h => by
    simp [hT i j h, Matrix.one_apply_ne h.ne']
  have hu : ∀ k a, a ≠ k → IsUnit ((T - c k • (1 : M4 B)) a a) := fun k a h => by
    simpa [hd] using hc a k h
  have hrow := row_zero _ _ (hT' i) (eig_left c T hch i) i fun a h => hu i a h.ne'
  have hcol := col_zero _ _ (hT' j) (eig_right c T hch j) j fun a h => hu j a h.ne
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  rcases lt_or_ge i y with hy | hy
  · rw [hrow b y hy, mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro x _
    rcases lt_or_ge x j with hx | hx
    · rw [hcol a x hx, zero_mul]
    · rcases lt_or_ge y x with hxy | hxy
      · rw [hR x y hxy, mul_zero]
      · have e1 : x = j := le_antisymm (hxy.trans (hy.trans hij)) hx
        have e2 : y = i := le_antisymm hy (hij.trans (hx.trans hxy))
        rw [e1, e2, h0, mul_zero]

private theorem conj_sub (u : (M4 B)ˣ) (Y : M4 B) (a : B) :
    (u : M4 B) * (Y - a • (1 : M4 B)) * (u⁻¹ : (M4 B)ˣ) = (u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ) - a • (1 : M4 B) := by
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]

private theorem conj_zero (u : (M4 B)ˣ) (Y : M4 B) (h : (u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ) = 0) : Y = 0 := by
  rwa [Units.mul_left_eq_zero, Units.mul_right_eq_zero] at h

end UpperTheory.V.GradeZeroInterpolatingElement.OrdinaryLocal

open UpperTheory.V.GradeZeroInterpolatingElement.OrdinaryLocal in
theorem UpperTheory.V.GradeZeroInterpolatingElement.ordLocal :
    ∀ {H : Type} [Group H] (I : Subgroup H) (B : Type) [CommRing B] [IsLocalRing B] (ps : Fin 4 → H → B) (s₀ : H) (r : H →* M4 B), s₀ ∈ I → (∀ i j, i ≠ j → IsUnit (ps i s₀ - ps j s₀)) → (Ord I ps s₀ r ↔ ∃ u : (M4 B)ˣ, (∀ g i j, j < i → ((u : M4 B) * r g * (u⁻¹ : (M4 B)ˣ)) i j = 0) ∧ ∀ s ∈ I, ∀ i, ((u : M4 B) * r s * (u⁻¹ : (M4 B)ˣ)) i i = ps i s) := by
  intro H _ I B _ _ ps s₀ r hs₀ hc
  constructor
  · intro h
    obtain ⟨u, hu⟩ := diagonalize (fun a => ps a s₀) hc (r s₀) h.charpoly
    refine ⟨u, fun g i j hij => entry_zero _ hc u _ _ hu j i (h.stable g j i hij), fun s hs i => ?_⟩
    have h1 := entry_zero _ hc u _ _ hu i i (h.inert s hs i)
    rw [conj_sub, Matrix.sub_apply, sub_eq_zero] at h1
    simpa using h1
  · rintro ⟨u, h1, h2⟩
    refine ⟨?_, fun g i j hij => ?_, fun s hs i => ?_⟩
    · have h3 := charpoly_tri (fun a => ps a s₀) _ (h1 s₀) (h2 s₀ hs₀)
      rw [← h3, Matrix.coe_units_inv]
      exact (Matrix.charpoly_units_conj u (r s₀)).symm
    · apply conj_zero u
      rw [← sandwich]
      exact tri_zero _ hc _ _ (h1 s₀) (h2 s₀ hs₀) (h1 g) i j hij.le (h1 g j i hij)
    · apply conj_zero u
      rw [← sandwich, conj_sub]
      refine tri_zero _ hc _ _ (h1 s₀) (h2 s₀ hs₀) (fun a b hab => ?_) i i le_rfl ?_
      · rw [Matrix.sub_apply, h1 s a b hab]
        simp [Matrix.one_apply_ne hab.ne']
      · rw [Matrix.sub_apply, h2 s hs i]
        simp
end

