import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralStmt
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralClass
section
noncomputable section

open NumberField

namespace Formalism.MainNotions.Gaps.MI

open Formalism.MainNotions.Inhab Formalism.BasicNotions Formalism.MainNotions.StandardLattice

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K]

theorem stdForm_apply' (n : ℕ) (x y : Fin n → K) :
    stdForm K n x y = ∑ i, star (x i) * y i := rfl

theorem stdForm_isSymm (n : ℕ) : (stdForm K n).IsSymm := by
  first
    | (intro x y
       simp only [stdForm_apply', map_sum, starRingEnd_apply, star_mul', star_star]
       exact Finset.sum_congr rfl (fun i _ => mul_comm _ _))
    | (refine ⟨fun x y => ?_⟩
       simp only [stdForm_apply', map_sum, starRingEnd_apply, star_mul', star_star]
       exact Finset.sum_congr rfl (fun i _ => mul_comm _ _))

theorem stdLat_isLattice' (n : ℕ) : Submodule.IsLattice K (stdLat K n) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [stdLat, Submodule.span_span_of_tower]
    have h : (fun i : Fin n => (Pi.single i 1 : Fin n → K)) = Pi.basisFun K (Fin n) := by
      funext i
      simp [Pi.basisFun_apply]
    rw [h]
    exact (Pi.basisFun K (Fin n)).span_eq

variable (hc : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))

include hc in
theorem trace_star_mul_pos (a : K) (ha : a ≠ 0) : 0 < Algebra.trace ℚ K (star a * a) := by
  classical
  have hsum : (algebraMap ℚ ℂ) (Algebra.trace ℚ K (star a * a)) =
      ((∑ σ : K →ₐ[ℚ] ℂ, Complex.normSq (σ a) : ℝ) : ℂ) := by
    rw [trace_eq_sum_embeddings (E := ℂ), Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    have h1 : σ (star a) = starRingEnd ℂ (σ a) := hc σ.toRingHom a
    rw [map_mul, h1, Complex.normSq_eq_conj_mul_self]
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, Complex.normSq (σ a) := by
    have σ0 : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
    refine Finset.sum_pos' (fun σ _ => Complex.normSq_nonneg _) ⟨σ0, Finset.mem_univ _, ?_⟩
    exact Complex.normSq_pos.mpr ((map_ne_zero σ0).mpr ha)
  have hq : ((Algebra.trace ℚ K (star a * a) : ℚ) : ℝ) =
      ∑ σ : K →ₐ[ℚ] ℂ, Complex.normSq (σ a) := by
    apply Complex.ofReal_injective
    rw [← hsum]
    simp
  have h2 : (0 : ℝ) < ((Algebra.trace ℚ K (star a * a) : ℚ) : ℝ) := by
    rw [hq]
    exact hpos
  exact_mod_cast h2

include hc in
theorem trace_star_mul_nonneg (a : K) : 0 ≤ Algebra.trace ℚ K (star a * a) := by
  by_cases ha : a = 0
  · subst ha
    simp
  · exact le_of_lt (trace_star_mul_pos K hc a ha)

include hc in
theorem stdForm_def (n : ℕ) (x : Fin n → K) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (stdForm K n x x) := by
  rw [stdForm_apply', map_sum]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  exact Finset.sum_pos' (fun j _ => trace_star_mul_nonneg K hc (x j))
    ⟨i, Finset.mem_univ _, trace_star_mul_pos K hc (x i) hi⟩

include hc in
theorem std_class (n : ℕ) :
    (∃ s, Formalism.ThetaLiftIndependence.IsClassReps (stdForm K n) (stdLat K n) s) ∧
    (∀ s, Formalism.ThetaLiftIndependence.IsClassReps (stdForm K n) (stdLat K n) s →
      Formalism.HermitianLatticesTheory.mass (stdForm K n) (stdLat K n) =
        ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm K n) M) : ℕ) : ℝ)⁻¹) ∧
    (∀ M ∈ Formalism.HermitianLatticesTheory.genus (stdForm K n) (stdLat K n),
      0 < Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm K n) M)) ∧
    0 < Formalism.HermitianLatticesTheory.mass (stdForm K n) (stdLat K n) := by
  have hS := stdForm_isSymm K n
  have hD : ∀ x : Fin n → K, x ≠ 0 → 0 < Algebra.trace ℚ K (stdForm K n x x) :=
    stdForm_def K hc n
  have hL := stdLat_isLattice' K n
  obtain ⟨h1, h2, h3⟩ :=
    Formalism.HermitianLatticesTheory.massBasic K (Fin n → K) (stdForm K n) hS hD (stdLat K n) hL
  obtain ⟨-, h4, -⟩ :=
    Formalism.ThetaLiftIndependence.classRepsDefinite K (Fin n → K) (stdForm K n) hS hD (stdLat K n) hL
  refine ⟨h1, h2, ?_, h3⟩
  intro M hM
  obtain ⟨m, hm, hw⟩ := h4 M hM
  unfold Formalism.ThetaLiftIndependence.latWt at hw
  have e1 : ((Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm K n) M) : ℕ) : ℂ) = (m : ℂ) := inv_injective hw
  have e2 : Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm K n) M) = m := by exact_mod_cast e1
  rw [e2]
  exact hm

end Std

theorem mIClass : MIClass := by
  intro K H k
  letI := H.cmStar
  haveI := H.isCMField_hostE
  exact std_class H.E (fun φ a => NumberField.IsCMField.complexEmbedding_complexConj H.E φ a) k

end Formalism.MainNotions.Gaps.MI
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralIdx
section
noncomputable section

namespace Formalism.MainNotions.Gaps.MI

open Formalism.MainNotions.Inhab Formalism.BasicNotions Formalism.MainNotions.StandardLattice

section aux

variable {F : Type} [CommRing F] {k : ℕ}

def StrictUp (d : ℕ) (A : Matrix (Fin k) (Fin k) F) : Prop :=
  ∀ i j : Fin k, j.val < i.val + d → A i j = 0

theorem strictUp_mul {d : ℕ} {A B : Matrix (Fin k) (Fin k) F} (hA : StrictUp d A)
    (hB : StrictUp 1 B) : StrictUp (d + 1) (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l.val < i.val + d
  · rw [hA i l hl, zero_mul]
  · rw [hB l j (by omega), mul_zero]

theorem strictUp_pow {A : Matrix (Fin k) (Fin k) F} (hA : StrictUp 1 A) (d : ℕ) :
    StrictUp d (A ^ d) := by
  induction d with
  | zero =>
    intro i j hij
    rw [pow_zero, Matrix.one_apply_ne]
    intro h
    subst h
    omega
  | succ d ih =>
    rw [pow_succ]
    exact strictUp_mul ih hA

theorem strictUp_pow_eq_zero {A : Matrix (Fin k) (Fin k) F} (hA : StrictUp 1 A) {d : ℕ}
    (hd : k ≤ d) : A ^ d = 0 := by
  ext i j
  exact strictUp_pow hA d i j (by have := j.isLt; omega)

theorem isUnitri_one : IsUnitri (1 : Matrix (Fin k) (Fin k) F) :=
  ⟨fun _ _ hij => Matrix.one_apply_ne (ne_of_gt hij), fun i => Matrix.one_apply_eq i⟩

theorem isUnitri_mul {A B : Matrix (Fin k) (Fin k) F} (hA : IsUnitri A) (hB : IsUnitri B) :
    IsUnitri (A * B) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l < i
    · rw [hA.1 i l hl, zero_mul]
    · rw [hB.1 l j (lt_of_lt_of_le hij (not_lt.mp hl)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, mul_one]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hA.1 i l h, zero_mul]
      · rw [hB.1 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem isUnitri_pow {A : Matrix (Fin k) (Fin k) F} (hA : IsUnitri A) (d : ℕ) :
    IsUnitri (A ^ d) := by
  induction d with
  | zero => rw [pow_zero]; exact isUnitri_one
  | succ d ih => rw [pow_succ]; exact isUnitri_mul ih hA

theorem strictUp_sub_one {A : Matrix (Fin k) (Fin k) F} (hA : IsUnitri A) :
    StrictUp 1 (A - 1) := by
  intro i j hij
  rw [Matrix.sub_apply]
  rcases Nat.lt_or_ge j.val i.val with h | h
  · have h' : j < i := h
    rw [hA.1 i j h', Matrix.one_apply_ne (ne_of_gt h'), sub_zero]
  · have h' : i = j := Fin.ext (by omega)
    subst h'
    rw [hA.2 i, Matrix.one_apply_eq, sub_self]

theorem isUnitri_pow_char (g : ℕ) [Fact g.Prime] [CharP F g] [Nontrivial F]
    {A : Matrix (Fin k) (Fin k) F} (hA : IsUnitri A) : A ^ (g ^ k) = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Subsingleton.elim _ _
  · have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    have h1 : (A - 1) ^ (g ^ k) = A ^ (g ^ k) - 1 ^ (g ^ k) :=
      sub_pow_char_pow_of_commute (h := Commute.one_right A) ..
    have h2 : (A - 1) ^ (g ^ k) = 0 :=
      strictUp_pow_eq_zero (strictUp_sub_one hA)
        (le_of_lt (Nat.lt_pow_self (Fact.out : g.Prime).one_lt))
    rw [h2, one_pow] at h1
    exact (sub_eq_zero.mp h1.symm)

end aux

theorem idxFacts : IdxFacts := by
  refine ⟨fun g k hg => ?_, ?_⟩
  · have : Fact g.Prime := ⟨hg⟩
    have hpow : ∀ x : GL (Fin k) (ZMod g), IsUnitri (x : Matrix (Fin k) (Fin k) (ZMod g)) →
        x ^ (g ^ k) = 1 := by
      intro x hx
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact isUnitri_pow_char g hx
    let U : Subgroup (GL (Fin k) (ZMod g)) :=
      { carrier := {x | IsUnitri (x : Matrix (Fin k) (Fin k) (ZMod g))}
        mul_mem' := fun {a b} ha hb => by
          show IsUnitri ((a * b : GL (Fin k) (ZMod g)) : Matrix (Fin k) (Fin k) (ZMod g))
          rw [Units.val_mul]
          exact isUnitri_mul ha hb
        one_mem' := by
          show IsUnitri ((1 : GL (Fin k) (ZMod g)) : Matrix (Fin k) (Fin k) (ZMod g))
          rw [Units.val_one]
          exact isUnitri_one
        inv_mem' := fun {a} ha => by
          show IsUnitri ((a⁻¹ : GL (Fin k) (ZMod g)) : Matrix (Fin k) (Fin k) (ZMod g))
          have hpos : 0 < g ^ k := pow_pos hg.pos k
          have h1 : a ^ (g ^ k - 1) * a = 1 := by
            rw [← pow_succ, Nat.sub_add_cancel hpos]
            exact hpow a ha
          have h2 : a⁻¹ = a ^ (g ^ k - 1) := (eq_inv_of_mul_eq_one_left h1).symm
          rw [h2, Units.val_pow_eq_pow_val]
          exact isUnitri_pow ha _ }
    have hmem : ∀ x, x ∈ U ↔ IsUnitri (x : Matrix (Fin k) (Fin k) (ZMod g)) := fun x => Iff.rfl
    have hcard : Nat.card U =
        Nat.card {A : GL (Fin k) (ZMod g) // IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} := rfl
    have hUpos : 0 < Nat.card U := Nat.card_pos
    have hidx : U.index * Nat.card U = Nat.card (GL (Fin k) (ZMod g)) := U.index_mul_card
    refine ⟨U, hmem, ?_, ?_, fun x hx => ⟨k, hpow x hx⟩⟩
    · unfold idxColLoc idxLoc
      rw [← hcard, ← hidx, Nat.cast_mul, mul_div_assoc, div_self, mul_one]
      exact_mod_cast hUpos.ne'
    · exact Nat.pos_of_ne_zero U.index_ne_zero_of_finite
  · intro G X _ _ _ _ hfree
    classical
    have : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X), Nat.card_sigma]
    refine Finset.dvd_sum fun ω _ => ?_
    have hb : MulAction.stabilizer G ω.out = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      exact Subgroup.mem_bot.mpr (hfree _ a (MulAction.mem_stabilizer_iff.mp ha))
    rw [hb]
    have : Nat.card (G ⧸ (⊥ : Subgroup G)) = Nat.card G := Subgroup.index_bot
    rw [this]

end Formalism.MainNotions.Gaps.MI
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralRed
section
noncomputable section

open NumberField

namespace Formalism.MainNotions.Gaps.MI

theorem one_add_pow_expand {A : Type*} [Ring A] (X : A) (t : ℕ) :
    ∃ P : A, (1 + X) ^ t = 1 + t • X + X * X * P := by
  induction t with
  | zero => exact ⟨0, by simp⟩
  | succ t ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P + t • (1 : A) + P * X, ?_⟩
    rw [pow_succ, hP, succ_nsmul]
    simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
    abel

theorem mat_eq_one {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n R) (t : ℕ) (ht : IsUnit (t : R)) (hC : C ^ t = 1)
    (hmod : ∀ i j, (C - 1) i j ∈ Ideal.jacobson (⊥ : Ideal R)) : C = 1 := by
  set X : Matrix n n R := C - 1 with hX
  have hCX : C = 1 + X := by rw [hX]; abel
  set I : Ideal R := Ideal.span (Set.range fun p : n × n => X p.1 p.2) with hI
  have hmem : ∀ i j, X i j ∈ I := fun i j => Ideal.subset_span ⟨(i, j), rfl⟩
  obtain ⟨P, hP⟩ := one_add_pow_expand X t
  rw [← hCX, hC] at hP
  have h0 : t • X + X * X * P = 0 := by
    have : (1 : Matrix n n R) + (t • X + X * X * P) = 1 + 0 := by
      rw [add_zero, ← add_assoc]; exact hP.symm
    exact add_left_cancel this
  have hXX : ∀ i j, (X * X) i j ∈ I * I := by
    intro i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_mul (hmem i l) (hmem l j)
  have hXXP : ∀ i j, (X * X * P) i j ∈ I * I := by
    intro i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hXX i l)
  have hle : I ≤ I • I := by
    rw [hI, Ideal.span_le, ← hI]
    rintro _ ⟨p, rfl⟩
    obtain ⟨u, hu⟩ := ht
    have h1 : (t : R) * X p.1 p.2 = - (X * X * P) p.1 p.2 := by
      have := congrFun (congrFun h0 p.1) p.2
      rw [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, Matrix.zero_apply] at this
      linear_combination this
    have h2 : X p.1 p.2 = (↑u⁻¹ : R) * (- (X * X * P) p.1 p.2) := by
      rw [← h1, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    show X p.1 p.2 ∈ I * I
    rw [h2]
    exact Ideal.mul_mem_left _ _ (neg_mem (hXXP _ _))
  have hIj : I ≤ Ideal.jacobson ⊥ := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    exact hmod p.1 p.2
  have hfg : I.FG := Submodule.fg_span (Set.finite_range _)
  have hbot : I = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I I hfg hle hIj
  have hX0 : X = 0 := by
    ext i j
    have := hmem i j
    rw [hbot] at this
    simpa using this
  rw [hCX, hX0, add_zero]

theorem red_local {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (k g : ℕ) (hg : g.Prime)
    (φ : R →+* ZMod g) (hφ : ∀ x, φ x ≠ 0 → IsUnit x)
    (L : Submodule R (Fin k → K)) [Submodule.IsLattice K L]
    (G : Subgroup ((Fin k → K) ≃ₗ[K] (Fin k → K)))
    (hG : ∀ a ∈ G, ∀ x ∈ L, a x ∈ L) :
    ∃ ρ : G →* GL (Fin k) (ZMod g), ∀ a : G, IsOfFinOrder a →
      (∃ N : ℕ, ρ a ^ (g ^ N) = 1) → ∃ N : ℕ, a ^ (g ^ N) = 1 := by
  have : Fact g.Prime := ⟨hg⟩
  let f : G →* Module.End R L :=
    { toFun := fun a =>
        ((a : (Fin k → K) ≃ₗ[K] (Fin k → K)).toLinearMap.restrictScalars R).restrict (hG a a.2)
      map_one' := by ext x; rfl
      map_mul' := fun a b => by ext x; rfl }
  have hfin : Module.finrank R L = k := by
    rw [Submodule.IsLattice.finrank_of_pi K L, Fintype.card_fin]
  let b : Module.Basis (Fin k) R L := Module.finBasisOfFinrankEq R L hfin
  let T : G →* Matrix (Fin k) (Fin k) R :=
    ((LinearMap.toMatrixAlgEquiv b : Module.End R L ≃ₐ[R] Matrix (Fin k) (Fin k) R) :
      Module.End R L →* Matrix (Fin k) (Fin k) R).comp f
  let Tφ : G →* Matrix (Fin k) (Fin k) (ZMod g) :=
    ((φ.mapMatrix : Matrix (Fin k) (Fin k) R →+* Matrix (Fin k) (Fin k) (ZMod g)) :
      Matrix (Fin k) (Fin k) R →* Matrix (Fin k) (Fin k) (ZMod g)).comp T
  have hTinj : ∀ c : G, T c = 1 → c = 1 := by
    intro c hc
    have h1 : f c = 1 := by
      have : (LinearMap.toMatrixAlgEquiv b) (f c) = (LinearMap.toMatrixAlgEquiv b) 1 := by
        rw [map_one]; exact hc
      exact (LinearMap.toMatrixAlgEquiv b).injective this
    have h2 : ∀ x ∈ L, (c : (Fin k → K) ≃ₗ[K] (Fin k → K)) x = x := by
      intro x hx
      have := congrArg (fun e : Module.End R L => ((e ⟨x, hx⟩ : L) : Fin k → K)) h1
      exact this
    have h3 : (c : (Fin k → K) ≃ₗ[K] (Fin k → K)).toLinearMap = LinearMap.id :=
      LinearMap.ext_on (Submodule.IsLattice.span_eq_top (M := L)) (fun x hx => h2 x hx)
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    exact h3
  refine ⟨Tφ.toHomUnits, ?_⟩
  rintro a ⟨n, hn, han⟩ ⟨N, hN⟩
  have han' : a ^ n = 1 := by simpa [Function.IsPeriodicPt, Function.IsFixedPt] using han
  obtain ⟨s, t, htg, hnt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' g hg.ne_one
  refine ⟨N + s, hTinj _ ?_⟩
  have htu : IsUnit ((t : ℕ) : R) := by
    apply hφ
    rw [map_natCast]
    intro h0
    exact htg ((ZMod.natCast_eq_zero_iff t g).1 h0)
  apply mat_eq_one _ t htu
  · rw [← map_pow, ← pow_mul, pow_add, mul_assoc, ← hnt, mul_comm, pow_mul, han', one_pow, map_one]
  · intro i j
    have h1 : Tφ (a ^ g ^ (N + s)) = 1 := by
      have h2 : Tφ a ^ (g ^ N) = 1 := by
        have := congrArg (fun u : GL (Fin k) (ZMod g) => (u : Matrix (Fin k) (Fin k) (ZMod g))) hN
        simpa using this
      rw [pow_add, pow_mul, map_pow, map_pow, h2, one_pow]
    have h3 : φ ((T (a ^ g ^ (N + s)) - 1) i j) = 0 := by
      have := congrFun (congrFun h1 i) j
      have h4 : φ (T (a ^ g ^ (N + s)) i j) = (1 : Matrix (Fin k) (Fin k) (ZMod g)) i j := this
      rw [Matrix.sub_apply, map_sub, h4]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij]
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    intro hu
    have := hu.map φ
    rw [h3] at this
    exact not_isUnit_zero this

theorem redHomGen : RedHomGen := by
  intro E _ _ k g hg v hv he M hM G hG _
  obtain ⟨e⟩ := he
  have hvbot : v ≠ ⊥ := by
    intro h
    apply NumberField.RingOfIntegers.not_isField E
    rw [Ring.isField_iff_maximal_bot]
    exact h ▸ hv
  have hS : v.primeCompl ≤ nonZeroDivisors (𝓞 E) := Ideal.primeCompl_le_nonZeroDivisors v
  let R : Subalgebra (𝓞 E) E := Localization.subalgebra.ofField E v.primeCompl hS
  have hloc : IsLocalization.AtPrime R v :=
    Localization.subalgebra.isLocalization_ofField E v.primeCompl hS
  have hlr : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R v
  have hdvr : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) hvbot R
  let φ : R →+* ZMod g :=
    ((e : (𝓞 E ⧸ v) →+* ZMod g).comp
      ((IsLocalization.AtPrime.equivQuotMaximalIdeal v R).symm :
        (R ⧸ IsLocalRing.maximalIdeal R) →+* (𝓞 E ⧸ v))).comp
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
  have hφ : ∀ x, φ x ≠ 0 → IsUnit x := by
    intro x hx
    by_contra hnu
    apply hx
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal x).2 hnu)
    simp [φ, h0]
  let L : Submodule R (Fin k → E) := Submodule.span R (M : Set (Fin k → E))
  have hL : Submodule.IsLattice E L :=
    { fg := by
        obtain ⟨s, hs⟩ := hM.fg
        refine ⟨s, ?_⟩
        rw [← Submodule.span_span_of_tower (𝓞 E) R (s : Set (Fin k → E)), hs]
      span_eq_top := by
        rw [Submodule.span_span_of_tower R E (M : Set (Fin k → E))]
        exact hM.span_eq_top }
  have hGL : ∀ a ∈ G, ∀ x ∈ L, a x ∈ L := by
    intro a ha
    have : L ≤ L.comap (a.toLinearMap.restrictScalars R) :=
      Submodule.span_le.2 fun x hx => Submodule.subset_span (hG a ha x hx)
    exact fun x hx => this hx
  exact red_local k g hg φ hφ L G hGL

end Formalism.MainNotions.Gaps.MI
end
end

