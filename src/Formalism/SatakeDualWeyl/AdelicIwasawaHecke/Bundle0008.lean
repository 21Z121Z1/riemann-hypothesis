import Formalism.SatakeDualWeyl.Bundle0002
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0004
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
import Formalism.SatakeDualWeyl.Bundle0001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LocalAlgebraInertPrime
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Gen

variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

theorem gLoc_bc_coe (e : A →+* L) (g : GL n A) :
    ((bc (n := n) e g : GL n L) : Matrix n n L) = (g : Matrix n n A).map e := rfl

theorem gLoc_bc_symm (e : A ≃+* L) (g : GL n L) :
    bc (n := n) (e : A →+* L) (bc (n := n) (e.symm : L →+* A) g) = g := by
  ext i j
  simp [bc]

theorem gLoc_bc_inj (e : A ≃+* L) : Function.Injective (bc (n := n) (e : A →+* L)) := by
  intro g h hgh
  ext i j
  have := congrArg (fun u : GL n L => (u : Matrix n n L) i j) hgh
  simpa [bc] using this

theorem gLoc_mem_one_iff (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L)
    (he : ∀ x, e (σA x) = σL (e x)) (g : GL n A) :
    g ∈ UJ σA (1 : Matrix n n A) ↔ bc (e : A →+* L) g ∈ UJ σL (1 : Matrix n n L) := by
  set f : A →+* L := (e : A →+* L)
  have hf : Function.Injective f := e.injective
  have hc : (RingHom.mapMatrix f) (cT σA (g : Matrix n n A)) =
      cT σL (RingHom.mapMatrix f (g : Matrix n n A)) := by
    ext i j
    simp [cT, f, he]
  show cT σA (g : Matrix n n A) * 1 * (g : Matrix n n A) = 1 ↔
    cT σL (RingHom.mapMatrix f (g : Matrix n n A)) * 1 * RingHom.mapMatrix f (g : Matrix n n A) = 1
  rw [← hc, ← map_one (RingHom.mapMatrix f), ← map_mul, ← map_mul, map_one]
  constructor
  · intro h
    rw [h, map_one]
  · intro h
    apply Matrix.map_injective hf
    simpa [RingHom.mapMatrix_apply] using h

theorem gLoc_conj_iff (σL : L →+* L) (J : Matrix n n L) (P : GL n L)
    (hP : cT σL (P : Matrix n n L) * (P : Matrix n n L) = J) (g : GL n L) :
    g ∈ UJ σL (1 : Matrix n n L) ↔ P⁻¹ * g * P ∈ UJ σL J := by
  set p : Matrix n n L := (P : Matrix n n L)
  set q : Matrix n n L := ((P⁻¹ : GL n L) : Matrix n n L)
  set G : Matrix n n L := (g : Matrix n n L)
  have hpq : p * q = 1 := by
    simp only [p, q]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hqp : q * p = 1 := by
    simp only [p, q]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have cq : cT σL q * cT σL p = 1 := by rw [← cT_mul, hpq, cT_one]
  have cancel : ∀ X, cT σL q * (cT σL p * X * p) * q = X := fun X => by
    calc cT σL q * (cT σL p * X * p) * q = (cT σL q * cT σL p) * X * (p * q) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [cq, hpq, Matrix.one_mul, Matrix.mul_one]
  have inj : ∀ X Y, cT σL p * X * p = cT σL p * Y * p → X = Y := fun X Y h => by
    rw [← cancel X, ← cancel Y, h]
  have E : cT σL (q * G * p) * (cT σL p * p) * (q * G * p) = cT σL p * (cT σL G * G) * p := by
    rw [cT_mul, cT_mul]
    calc cT σL p * (cT σL G * cT σL q) * (cT σL p * p) * (q * G * p)
        = cT σL p * (cT σL G * ((cT σL q * cT σL p) * (p * q)) * G) * p := by
          simp only [Matrix.mul_assoc]
      _ = cT σL p * (cT σL G * G) * p := by rw [cq, hpq, Matrix.one_mul, Matrix.mul_one]
  show cT σL G * 1 * G = 1 ↔
    cT σL (((P⁻¹ * g * P : GL n L)) : Matrix n n L) * J * ((P⁻¹ * g * P : GL n L) : Matrix n n L) = J
  rw [show (((P⁻¹ * g * P : GL n L)) : Matrix n n L) = q * G * p by simp only [Units.val_mul, p, q, G]]
  rw [← hP, E, Matrix.mul_one]
  constructor
  · intro h
    rw [h, Matrix.mul_one]
  · intro h
    exact inj _ _ (by rw [h, Matrix.mul_one])

end Gen

section Int

variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

theorem gLoc_range_subtype {R : Type} [CommRing R] (S : Subring R) (x : R) :
    x ∈ Set.range S.subtype ↔ x ∈ S := by
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem gLoc_int_iff (e : A ≃+* L) (T : Subring A) (O : Subring L) (hT : ∀ x, x ∈ T ↔ e x ∈ O)
    (g : GL n A) :
    g ∈ (bc (n := n) T.subtype).range ↔ bc (e : A →+* L) g ∈ (bc (n := n) O.subtype).range := by
  have key : ∀ {B : Type} [CommRing B] (S : Subring B) (u : GL n B),
      u ∈ (bc (n := n) S.subtype).range ↔ (∀ i j, (u : Matrix n n B) i j ∈ S) ∧
        (∀ i j, ((u⁻¹ : GL n B) : Matrix n n B) i j ∈ S) := by
    intro B _ S u
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · simp [bc]
      · rw [← map_inv]
        simp [bc]
    · rintro ⟨h1, h2⟩
      have hinj : Function.Injective (RingHom.mapMatrix S.subtype : Matrix n n S → Matrix n n B) :=
        Matrix.map_injective Subtype.val_injective
      let Am : Matrix n n S := Matrix.of fun i j => ⟨(u : Matrix n n B) i j, h1 i j⟩
      let Bm : Matrix n n S := Matrix.of fun i j => ⟨((u⁻¹ : GL n B) : Matrix n n B) i j, h2 i j⟩
      have hA : RingHom.mapMatrix S.subtype Am = (u : Matrix n n B) := by ext i j; rfl
      have hB : RingHom.mapMatrix S.subtype Bm = ((u⁻¹ : GL n B) : Matrix n n B) := by ext i j; rfl
      refine ⟨⟨Am, Bm, hinj ?_, hinj ?_⟩, ?_⟩
      · rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      · rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      · ext i j
        rfl
  rw [key T g, key O (bc (e : A →+* L) g), ← map_inv]
  simp only [gLoc_bc_coe, Matrix.map_apply, RingEquiv.coe_toRingHom, ← hT]

theorem gLoc_conj_mem {G : Type} [Group G] (K : Subgroup G) (P : G) (hP : P ∈ K) (g : G) :
    g ∈ K ↔ P⁻¹ * g * P ∈ K := by
  constructor
  · intro h
    exact K.mul_mem (K.mul_mem (K.inv_mem hP) h) hP
  · intro h
    have := K.mul_mem (K.mul_mem hP h) (K.inv_mem hP)
    simpa [mul_assoc] using this

end Int

section Main

variable {A L : Type} [CommRing A] [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}

def gLoc_hom (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L) (he : ∀ x, e (σA x) = σL (e x))
    (P : GL (Fin m) L)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A)) :
    H →* GU σL m where
  toFun x := ⟨P⁻¹ * bc (e : A →+* L) (x : GL (Fin m) A) * P,
    (gLoc_conj_iff σL _ P hP _).1 ((gLoc_mem_one_iff σA σL e he _).1 ((hH _).1 x.2))⟩
  map_one' := by
    apply Subtype.ext
    show P⁻¹ * bc (e : A →+* L) (1 : GL (Fin m) A) * P = 1
    rw [map_one, mul_one, inv_mul_cancel]
  map_mul' a b := by
    apply Subtype.ext
    show P⁻¹ * bc (e : A →+* L) ((a : GL (Fin m) A) * (b : GL (Fin m) A)) * P =
      (P⁻¹ * bc (e : A →+* L) (a : GL (Fin m) A) * P) * (P⁻¹ * bc (e : A →+* L) (b : GL (Fin m) A) * P)
    rw [map_mul]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem gLoc_hom_apply (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L) (he : ∀ x, e (σA x) = σL (e x))
    (P : GL (Fin m) L)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A))
    (x : H) :
    ((gLoc_hom σA σL e he P hP H hH x : GU σL m) : GL (Fin m) L) =
      P⁻¹ * bc (e : A →+* L) (x : GL (Fin m) A) * P := rfl

theorem gLoc_hom_bij (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L) (he : ∀ x, e (σA x) = σL (e x))
    (P : GL (Fin m) L)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A)) :
    Function.Bijective (gLoc_hom σA σL e he P hP H hH) := by
  constructor
  · intro x y hxy
    have h1 := congrArg (fun z : GU σL m => P * (z : GL (Fin m) L) * P⁻¹) hxy
    simp only [gLoc_hom_apply] at h1
    have h2 : bc (e : A →+* L) (x : GL (Fin m) A) = bc (e : A →+* L) (y : GL (Fin m) A) := by
      simpa [mul_assoc] using h1
    exact Subtype.ext (gLoc_bc_inj e h2)
  · intro y
    have hbg : bc (e : A →+* L) (bc (e.symm : L →+* A) (P * (y : GL (Fin m) L) * P⁻¹)) =
        P * (y : GL (Fin m) L) * P⁻¹ := gLoc_bc_symm e _
    have hmem : bc (e.symm : L →+* A) (P * (y : GL (Fin m) L) * P⁻¹) ∈ H := by
      rw [hH, gLoc_mem_one_iff σA σL e he, hbg, gLoc_conj_iff σL _ P hP]
      simpa [mul_assoc] using y.2
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [gLoc_hom_apply, hbg]
    group

theorem gLoc_level (e : A ≃+* L) (T : Subring A) (hT : ∀ x, x ∈ T ↔ e x ∈ intL L) (P : GL (Fin m) L)
    (hPO : P ∈ (bc (n := Fin m) (intL L).subtype).range) {σL : L →+* L}
    (H Lv : Subgroup (GL (Fin m) A))
    (hLv : ∀ g, g ∈ Lv ↔ g ∈ H ∧ g ∈ (bc (n := Fin m) T.subtype).range)
    (f : H ≃* GU σL m) (hf : ∀ x, ((f x : GU σL m) : GL (Fin m) L) = P⁻¹ * bc (e : A →+* L) x * P) :
    (Lv.subgroupOf H).map f.toMonoidHom = KU σL m := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨-, hxT⟩ := (hLv _).mp (Subgroup.mem_subgroupOf.mp hx)
    rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf]
    refine ⟨(f x).2, ?_⟩
    show ((f x : GU σL m) : GL (Fin m) L) ∈ _
    rw [hf]
    exact (gLoc_conj_mem _ P hPO _).mp ((gLoc_int_iff e T (intL L) hT _).mp hxT)
  · intro hy
    obtain ⟨x, rfl⟩ := f.surjective y
    refine ⟨x, ?_, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ((hLv _).mpr ⟨x.2, ?_⟩)
    rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf] at hy
    have h2 := hy.2
    change ((f x : GU σL m) : GL (Fin m) L) ∈ _ at h2
    rw [hf] at h2
    exact (gLoc_int_iff e T (intL L) hT _).mpr ((gLoc_conj_mem _ P hPO _).mpr h2)

theorem gLoc_main (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L) (he : ∀ x, e (σA x) = σL (e x))
    (T : Subring A) (hT : ∀ x, x ∈ T ↔ e x ∈ intL L) (P : GL (Fin m) L)
    (hPO : P ∈ (bc (n := Fin m) (intL L).subtype).range)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H Lv : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A))
    (hLv : ∀ g, g ∈ Lv ↔ g ∈ H ∧ g ∈ (bc (n := Fin m) T.subtype).range) :
    ∃ f : H ≃* GU σL m,
      (∀ x, ((f x : GU σL m) : GL (Fin m) L) = P⁻¹ * bc (e : A →+* L) x * P) ∧
      (Lv.subgroupOf H).map f.toMonoidHom = KU σL m := by
  refine ⟨MulEquiv.ofBijective (gLoc_hom σA σL e he P hP H hH) (gLoc_hom_bij σA σL e he P hP H hH),
    fun x => rfl, ?_⟩
  exact gLoc_level e T hT P hPO H Lv hLv _ (fun x => rfl)

end Main

theorem local_algebra_inert_prime : Formalism.UG.LocInert := by
  intro F E _ _ _ _ _ σ n v L _ _ _ e σw P he hT hPO hP
  have hH : ∀ g, g ∈ UPts σ (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) ↔
      g ∈ UJ (sigR σ (v.adicCompletion F)) (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) := by
    intro g
    rw [UPts, Matrix.map_one _ (map_zero _) (map_one _)]
  have hLv : ∀ g, g ∈ levelV σ (1 : Matrix (Fin n) (Fin n) E) v ↔
      g ∈ UPts σ (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) ∧
      g ∈ (bc (n := Fin n) (tensInt (F := F) (v.adicCompletion F) (intOE E) (Ov F v)).subtype).range := by
    intro g
    rw [levelV, level, Subgroup.mem_inf,
      stabilizer_standard_lattice _ _ (Fin n) (fun a b h => Subtype.ext h)]
    rfl
  obtain ⟨f, hf1, hf2⟩ := gLoc_main (sigR σ (v.adicCompletion F)) σw e he _ hT P hPO hP _ _ hH hLv
  exact ⟨f, hf1, hf2⟩

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
section
open NumberField IsDedekindDomain Formalism.UG

namespace Formalism.UG.P

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private lemma exists_GLint_of_integral_inverse {n : ℕ} (A B : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hA : ∀ i j, A i j ∈ Ov F v) (hB : ∀ i j, B i j ∈ Ov F v) (hAB : A * B = 1) (hBA : B * A = 1) :
    ∃ k ∈ GLint (Fin n) (Ov F v), (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = A := by
  let A' : Matrix (Fin n) (Fin n) (Ov F v) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix (Fin n) (Fin n) (Ov F v) := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have hinj : ∀ M N : Matrix (Fin n) (Fin n) (Ov F v),
      RingHom.mapMatrix (Ov F v).subtype M = RingHom.mapMatrix (Ov F v).subtype N → M = N := by
    intro M N h
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  have hmA : RingHom.mapMatrix (Ov F v).subtype A' = A := Matrix.ext fun i j => rfl
  have hmB : RingHom.mapMatrix (Ov F v).subtype B' = B := Matrix.ext fun i j => rfl
  have hAB' : A' * B' = 1 := hinj _ _ (by rw [map_mul, map_one, hmA, hmB, hAB])
  have hBA' : B' * A' = 1 := hinj _ _ (by rw [map_mul, map_one, hmA, hmB, hBA])
  let u : GL (Fin n) (Ov F v) := ⟨A', B', hAB', hBA'⟩
  exact ⟨bc (Ov F v).subtype u, ⟨u, rfl⟩, Matrix.ext fun i j => rfl⟩

private lemma mul_column_operation_apply {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (r : Fin n)
    (c : Fin n → R) (x b : Fin n) :
    (M * Matrix.of fun a b => (if a = b then (1 : R) else 0) + (if a = r ∧ b ≠ r then c b else 0)) x b =
      M x b + (if b ≠ r then M x r * c b else 0) := by
  by_cases hb : b = r
  · subst hb
    simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply, hb, mul_add, Finset.sum_add_distrib]

private lemma column_operation_mul_neg_eq_one {R : Type*} [CommRing R] {n : ℕ} (r : Fin n) (c : Fin n → R) :
    (Matrix.of fun a b => (if a = b then (1 : R) else 0) + (if a = r ∧ b ≠ r then c b else 0)) *
      (Matrix.of fun a b => (if a = b then (1 : R) else 0) + (if a = r ∧ b ≠ r then -c b else 0)) = 1 := by
  ext a b
  rw [mul_column_operation_apply _ r (fun b => -c b)]
  by_cases hbr : b = r
  · subst hbr
    simp [Matrix.one_apply]
  · by_cases har : a = r
    · subst har
      have hne : a ≠ b := fun h => hbr h.symm
      simp [Matrix.one_apply, hbr, hne]
    · simp [Matrix.one_apply, hbr, har]

private lemma exists_GLint_eq_column_operation {n : ℕ} (r : Fin n) (c : Fin n → v.adicCompletion F)
    (hc : ∀ b, c b ∈ Ov F v) :
    ∃ k ∈ GLint (Fin n) (Ov F v), (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      Matrix.of fun a b => (if a = b then (1 : v.adicCompletion F) else 0) +
        (if a = r ∧ b ≠ r then c b else 0) := by
  refine exists_GLint_of_integral_inverse F v _
    (Matrix.of fun a b => (if a = b then (1 : v.adicCompletion F) else 0) + (if a = r ∧ b ≠ r then -c b else 0))
    ?_ ?_ (column_operation_mul_neg_eq_one r c) ?_
  · intro i j
    simp only [Matrix.of_apply]
    refine Subring.add_mem _ ?_ ?_
    · split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · split_ifs
      · exact hc j
      · exact Subring.zero_mem _
  · intro i j
    simp only [Matrix.of_apply]
    refine Subring.add_mem _ ?_ ?_
    · split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · split_ifs
      · exact Subring.neg_mem _ (hc j)
      · exact Subring.zero_mem _
  · have h := column_operation_mul_neg_eq_one r (fun b => -c b)
    simpa using h

private lemma mem_Ov_of_valuation_le_one (x : v.adicCompletion F) (h : Valued.v x ≤ 1) : x ∈ Ov F v := by
  change x ∈ v.adicCompletionIntegers F
  exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h

private lemma exists_GLint_mul_clears_below_diag_from {n : ℕ} (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (i0 : Fin n)
    (hM : ∀ i j : Fin n, i0 < i → j < i → M i j = 0) :
    ∃ k ∈ GLint (Fin n) (Ov F v), ∀ i j : Fin n, i0 ≤ i → j < i →
      (M * (k : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i j = 0 := by
  classical
  by_cases hz : ∀ j, j < i0 → M i0 j = 0
  · refine ⟨1, Subgroup.one_mem _, fun i j hi hj => ?_⟩
    simp only [Units.val_one, Matrix.mul_one]
    rcases hi.lt_or_eq with h | h
    · exact hM i j h hj
    · subst h
      exact hz j hj
  push_neg at hz
  obtain ⟨j1, hj1, hj1ne⟩ := hz
  obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image (Finset.univ.filter (fun j => j ≤ i0))
    (fun j => Valued.v (M i0 j)) ⟨i0, by simp⟩
  have hp : p ≤ i0 := (Finset.mem_filter.mp hpS).2
  have hmax : ∀ j, j ≤ i0 → Valued.v (M i0 j) ≤ Valued.v (M i0 p) := fun j hj => hpmax j (by simp [hj])
  have hppos : 0 < Valued.v (M i0 p) :=
    lt_of_lt_of_le ((Valuation.pos_iff _).mpr hj1ne) (hmax j1 hj1.le)
  obtain ⟨k1, hk1, hrows1, hpiv1, hne1⟩ : ∃ k1 ∈ GLint (Fin n) (Ov F v),
      (∀ i j : Fin n, i0 < i → j < i →
        (M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i j = 0) ∧
      (∀ j, j ≤ i0 → Valued.v ((M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i0 j) ≤
        Valued.v ((M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i0 i0)) ∧
      (M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i0 i0 ≠ 0 := by
    by_cases heq : Valued.v (M i0 i0) = Valued.v (M i0 p)
    · refine ⟨1, Subgroup.one_mem _, ?_, ?_, ?_⟩
      · simpa using hM
      · intro j hj
        simpa [heq] using hmax j hj
      · simp only [Units.val_one, Matrix.mul_one]
        intro h0
        rw [h0, map_zero] at heq
        exact (ne_of_lt hppos) heq
    · have hlt : Valued.v (M i0 i0) < Valued.v (M i0 p) := lt_of_le_of_ne (hmax i0 le_rfl) heq
      have hpi0 : p ≠ i0 := fun h => heq (by rw [h])
      obtain ⟨k1, hk1, hk1eq⟩ := exists_GLint_eq_column_operation F v p (fun b => if b = i0 then 1 else 0) (fun b => by
        split_ifs
        · exact Subring.one_mem _
        · exact Subring.zero_mem _)
      have hdiag : (M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i0 i0 = M i0 i0 + M i0 p := by
        rw [hk1eq, mul_column_operation_apply]
        simp [Ne.symm hpi0]
      refine ⟨k1, hk1, ?_, ?_, ?_⟩
      · intro i j hi hj
        rw [hk1eq, mul_column_operation_apply, hM i j hi hj, hM i p hi (lt_of_le_of_lt hp hi)]
        simp
      · intro j hj
        rw [hdiag, Valuation.map_add_eq_of_lt_right _ hlt]
        by_cases hji : j = i0
        · subst hji
          rw [hdiag, Valuation.map_add_eq_of_lt_right _ hlt]
        · rw [hk1eq, mul_column_operation_apply]
          simp only [hji, if_false, mul_zero, ite_self, add_zero]
          exact hmax j hj
      · rw [hdiag]
        intro h0
        have h1 := Valuation.map_add_eq_of_lt_right Valued.v hlt
        rw [h0, map_zero] at h1
        exact (ne_of_lt hppos) h1
  set M1 := M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) with hM1
  obtain ⟨k2, hk2, hk2eq⟩ := exists_GLint_eq_column_operation F v i0
    (fun b => if b < i0 then -(M1 i0 b / M1 i0 i0) else 0) (fun b => by
      split_ifs with hb
      · apply mem_Ov_of_valuation_le_one
        rw [Valuation.map_neg, map_div₀]
        exact div_le_one_of_le₀ (hpiv1 b hb.le) zero_le'
      · exact Subring.zero_mem _)
  refine ⟨k1 * k2, Subgroup.mul_mem _ hk1 hk2, fun i j hi hj => ?_⟩
  rw [Units.val_mul, ← Matrix.mul_assoc, ← hM1, hk2eq, mul_column_operation_apply]
  rcases hi.lt_or_eq with h | h
  · rw [hrows1 i j h hj, hrows1 i i0 h h]
    simp
  · subst h
    have hji : j ≠ i0 := ne_of_lt hj
    simp only [hji, ne_eq, not_false_eq_true, if_true, hj]
    field_simp
    ring

theorem spherical_iwasawa {n : ℕ} (g : GL (Fin n) (v.adicCompletion F)) :
    ∃ b k : GL (Fin n) (v.adicCompletion F),
      (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id ∧
      k ∈ GLint (Fin n) (Ov F v) ∧ g = b * k := by
  classical
  have key : ∀ r, r ≤ n → ∃ k ∈ GLint (Fin n) (Ov F v), ∀ i j : Fin n, n - r ≤ i.val → j < i →
      ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (k : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i j = 0 := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨1, Subgroup.one_mem _, fun i j hi _ => ?_⟩
      have := i.isLt
      omega
    | succ r ih =>
      intro hr
      obtain ⟨k, hk, hup⟩ := ih (by omega)
      obtain ⟨k2, hk2, h2⟩ := exists_GLint_mul_clears_below_diag_from F v
        ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
        ⟨n - r - 1, by omega⟩ (fun i j hi hj => hup i j (by rw [Fin.lt_def] at hi; simp at hi; omega) hj)
      refine ⟨k * k2, Subgroup.mul_mem _ hk hk2, fun i j hi hj => ?_⟩
      rw [Units.val_mul, ← Matrix.mul_assoc]
      exact h2 i j (by rw [Fin.le_def]; simp; omega) hj
  obtain ⟨k, hk, hup⟩ := key n le_rfl
  refine ⟨g * k, k⁻¹, ?_, Subgroup.inv_mem _ hk, by group⟩
  rw [← spherical_upper_iff]
  intro i j hji
  rw [Units.val_mul]
  exact hup i j (by omega) hji

theorem spherical_wd {n : ℕ} (α : Fin n → ℂ) (hα : ∀ i, α i ≠ 0) (b b' k k' : GL (Fin n) (v.adicCompletion F))
    (hb : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hb' : (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hk : k ∈ GLint (Fin n) (Ov F v)) (hk' : k' ∈ GLint (Fin n) (Ov F v)) (h : b * k = b' * k') :
    chiDelta F v α b = chiDelta F v α b' := by
  have hq : b'⁻¹ * b = k' * k⁻¹ := by
    calc b'⁻¹ * b = b'⁻¹ * (b * k) * k⁻¹ := by group
      _ = b'⁻¹ * (b' * k') * k⁻¹ := by rw [h]
      _ = k' * k⁻¹ := by group
  have hup : ((b'⁻¹ * b : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id :=
    spherical_upper_mul _ _ (spherical_upper_inv _ hb') hb
  have hint : b'⁻¹ * b ∈ GLint (Fin n) (Ov F v) := by
    rw [hq]
    exact Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk)
  have hb_eq : b = b' * (b'⁻¹ * b) := by group
  rw [hb_eq, spherical_chiDelta_mul F v α hα b' _ hb' hup, spherical_chiDelta_int F v α _ hup hint, mul_one]

theorem exists_spherical_function : Formalism.UG.SphericalExists := by
  intro F _ _ v n α hα
  classical
  have dec := fun g : GL (Fin n) (v.adicCompletion F) => spherical_iwasawa F v g
  let φ : GL (Fin n) (v.adicCompletion F) → ℂ := fun g => chiDelta F v α (Classical.choose (dec g))
  have hφ : ∀ g b k : GL (Fin n) (v.adicCompletion F),
      (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id →
      k ∈ GLint (Fin n) (Ov F v) → g = b * k → φ g = chiDelta F v α b := by
    intro g b k hb hk hg
    obtain ⟨k0, hb0, hk0, hg0⟩ := Classical.choose_spec (dec g)
    exact spherical_wd F v α hα _ _ _ _ hb0 hb hk0 hk (hg0.symm.trans hg)
  have hone : ((1 : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id :=
    (spherical_upper_iff 1).mp (fun i j h => by simp [Matrix.one_apply_ne (ne_of_gt h)])
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro b g k hb hk
    have hb' := (spherical_upper_iff b).mp hb
    obtain ⟨b0, k0, hb0, hk0, hg0⟩ := dec g
    rw [hφ g b0 k0 hb0 hk0 hg0,
      hφ (b * g * k) (b * b0) (k0 * k) (spherical_upper_mul b b0 hb' hb0)
        (Subgroup.mul_mem _ hk0 hk) (by rw [hg0]; group),
      spherical_chiDelta_mul F v α hα b b0 hb' hb0]
  · rw [hφ 1 1 1 hone (Subgroup.one_mem _) (by simp)]
    exact spherical_chiDelta_int F v α 1 hone (Subgroup.one_mem _)
  · intro ψ hψ
    funext g
    obtain ⟨b0, k0, hb0, hk0, hg0⟩ := dec g
    have h1 := hψ b0 1 k0 ((spherical_upper_iff b0).mpr hb0) hk0
    rw [mul_one] at h1
    rw [hg0, hφ (b0 * k0) b0 k0 hb0 hk0 rfl, h1, mul_comm]

end Formalism.UG.P
end

