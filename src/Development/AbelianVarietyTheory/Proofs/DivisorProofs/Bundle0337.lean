import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0136
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContCxOfDegreewise
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CochainLim

universe v u w w'
variable {C : Type u} [Category.{v} C] [Preadditive C]

def pb {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z : Cochain B L n) : Cochain A L n :=
  (Cochain.ofHom f).comp z (zero_add n)

theorem pb_v {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z : Cochain B L n) (p q : ℤ)
    (h : p + n = q) : (pb f z).v p q h = f.f p ≫ z.v p q h := by
  simp [pb]

theorem pb_pb {A B D L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (g : B ⟶ D) (z : Cochain D L n) :
    pb f (pb g z) = pb (f ≫ g) z := by
  ext p q h; simp [pb_v]

theorem pb_add {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z z' : Cochain B L n) :
    pb f (z + z') = pb f z + pb f z' := by simp [pb]

theorem pb_sub {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z z' : Cochain B L n) :
    pb f (z - z') = pb f z - pb f z' := by simp [pb]

theorem pb_zero {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) :
    pb f (0 : Cochain B L n) = 0 := by simp [pb]

theorem δ_pb {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z : Cochain B L n) (m : ℤ) :
    δ n m (pb f z) = pb f (δ n m z) := by simp [pb]

section Rel
variable {I : Type w} [Category.{w'} I] [IsCofiltered I] {K : I ⥤ CochainComplex C ℤ} (c : Cone K)
  (L : CochainComplex C ℤ)

def Q (n m a : ℤ) : Prop :=
  ∀ (i : I) (w : Cochain (K.obj i) L m) (z : Cochain c.pt L n), δ m (m + 1) w = 0 →
    δ n m z = pb (c.π.app i) w → (∀ p q (h : p + m = q), a < p → w.v p q h = 0) →
    (∀ p q (h : p + n = q), a < p → z.v p q h = 0) →
    ∃ (k : I) (f : k ⟶ i) (b : Cochain (K.obj k) L n) (y : Cochain c.pt L (n - 1)),
      δ n m b = pb (K.map f) w ∧ pb (c.π.app k) b = z + δ (n - 1) n y

theorem Q_base (hL : ∀ p : ℤ, p < 0 → IsZero (L.X p)) (n m a : ℤ) (ham : a + m < 0) (han : a + n < 0) :
    Q c L n m a := by
  intro i w z hw hz hw0 hz0
  have w0 : w = 0 := by
    ext p q h
    rw [Cochain.zero_v]
    by_cases hp : a < p
    · exact hw0 p q h hp
    · exact (hL q (by omega)).eq_of_tgt _ _
  have z0 : z = 0 := by
    ext p q h
    rw [Cochain.zero_v]
    by_cases hp : a < p
    · exact hz0 p q h hp
    · exact (hL q (by omega)).eq_of_tgt _ _
  exact ⟨i, 𝟙 i, 0, 0, by simp [w0, pb_zero], by simp [z0, pb_zero]⟩

end Rel

section Step
variable {I : Type w} [Category.{w'} I] [IsCofiltered I] {K : I ⥤ CochainComplex C ℤ} (c : Cone K)
  (L : CochainComplex C ℤ)

theorem Q_of_Q_sub_one
    (hA : ∀ (p s s' : ℤ), s' + 1 = s → ∀ t : c.pt.X p ⟶ L.X s', t ≫ L.d s' s = 0 →
      ∃ (i : I) (u : (K.obj i).X p ⟶ L.X s') (y : c.pt.X p ⟶ L.X (s' - 1)),
        u ≫ L.d s' s = 0 ∧ (c.π.app i).f p ≫ u = t + y ≫ L.d (s' - 1) s')
    (hB : ∀ (p s : ℤ) (i : I) (u : (K.obj i).X p ⟶ L.X s), u ≫ L.d s (s + 1) = 0 →
      (∃ y : c.pt.X p ⟶ L.X (s - 1), (c.π.app i).f p ≫ u = y ≫ L.d (s - 1) s) →
      ∃ (k : I) (f : k ⟶ i) (y : (K.obj k).X p ⟶ L.X (s - 1)), (K.map f).f p ≫ u = y ≫ L.d (s - 1) s)
    (n m : ℤ) (hnm : n + 1 = m) (p : ℤ) (ih : Q c L n m (p - 1)) : Q c L n m p := by
  intro i w z hw hz hw0 hz0
  obtain ⟨s, hs⟩ : ∃ s, p + m = s := ⟨_, rfl⟩
  have hwc : w.v p s hs ≫ L.d s (s + 1) = 0 := by
    have := Cochain.congr_v hw p (s + 1) (by omega)
    rw [δ_v m (m + 1) rfl w p (s + 1) (by omega) s (p + 1) (by omega) rfl, Cochain.zero_v,
      hw0 (p + 1) (s + 1) (by omega) (by omega), comp_zero, smul_zero, add_zero] at this
    exact this
  have hzw : (c.π.app i).f p ≫ w.v p s hs = z.v p (s - 1) (by omega) ≫ L.d (s - 1) s := by
    have := Cochain.congr_v hz p s hs
    rw [δ_v n m hnm z p s hs (s - 1) (p + 1) rfl rfl,
      hz0 (p + 1) s (by omega) (by omega), comp_zero, smul_zero, add_zero, pb_v] at this
    exact this.symm
  obtain ⟨k, f, y', hy'⟩ := hB p s i (w.v p s hs) hwc ⟨_, hzw⟩
  have hδσ := Cochain.δ_single y' n m hnm (p - 1) s (by omega) (by omega)
  set σ : Cochain (K.obj k) L n := Cochain.single y' n with hσ
  set w' := pb (K.map f) w - δ n m σ with hw'def
  set z' := z - pb (A := c.pt) (c.π.app k) σ with hz'def
  have hw' : δ m (m + 1) w' = 0 := by
    simp only [hw'def, δ_sub, δ_pb, hw, pb_zero, δ_δ, sub_zero]
  have hz' : δ n m z' = pb (c.π.app k) w' := by
    simp only [hz'def, hw'def, δ_sub, δ_pb, hz, pb_sub, pb_pb, c.w f]
  have hw'0 : ∀ p'' q (h : p'' + m = q), p - 1 < p'' → w'.v p'' q h = 0 := by
    intro p'' q h hp''
    by_cases hpp : p'' = p
    · subst hpp
      obtain rfl : q = s := by omega
      simp only [hw'def, hδσ, Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v, pb_v, hy',
        Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p'' - 1 by omega), smul_zero,
        add_zero, sub_self]
    · simp only [hw'def, hδσ, Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v, pb_v,
        hw0 p'' q h (by omega), Cochain.single_v_eq_zero _ _ _ _ _ hpp,
        Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p - 1 by omega), smul_zero, add_zero, comp_zero,
        sub_self]
  have hz'0 : ∀ p'' q (h : p'' + n = q), p < p'' → z'.v p'' q h = 0 := by
    intro p'' q h hp''
    simp only [hz'def, hσ, Cochain.sub_v, pb_v, hz0 p'' q h hp'',
      Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p by omega), comp_zero, sub_self]
  have hz'c : z'.v p (s - 1) (by omega) ≫ L.d (s - 1) s = 0 := by
    have := Cochain.congr_v hz' p s hs
    rw [δ_v n m hnm z' p s hs (s - 1) (p + 1) rfl rfl,
      hz'0 (p + 1) s (by omega) (by omega), comp_zero, smul_zero, add_zero, pb_v,
      hw'0 p s hs (by omega), comp_zero] at this
    exact this
  obtain ⟨j, u2, y2, hu2c, hu2⟩ := hA p s (s - 1) (by omega) _ hz'c
  let l := IsCofiltered.min j k
  let g : l ⟶ j := IsCofiltered.minToLeft j k
  let h : l ⟶ k := IsCofiltered.minToRight j k
  have hδv := Cochain.δ_single ((K.map g).f p ≫ u2) n m hnm (p - 1) s (by omega) (by omega)
  rw [Category.assoc, hu2c, comp_zero, Cochain.single_zero, zero_add] at hδv
  set v : Cochain (K.obj l) L n := Cochain.single ((K.map g).f p ≫ u2) n with hv
  have hδρ := Cochain.δ_single y2 (n - 1) n (by omega) (p - 1) (s - 1) (by omega) (by omega)
  set ρ : Cochain c.pt L (n - 1) := Cochain.single y2 (n - 1) with hρ
  set w'' := pb (K.map h) w' - δ n m v with hw''def
  set z'' := z' - pb (A := c.pt) (c.π.app l) v + δ (n - 1) n ρ with hz''def
  have hw'' : δ m (m + 1) w'' = 0 := by
    simp only [hw''def, δ_sub, δ_pb, hw', pb_zero, δ_δ, sub_zero]
  have hz'' : δ n m z'' = pb (c.π.app l) w'' := by
    simp only [hz''def, hw''def, δ_add, δ_sub, δ_pb, hz', δ_δ, add_zero, pb_sub, pb_pb, c.w h]
  have hw''0 : ∀ p'' q (hh : p'' + m = q), p - 1 < p'' → w''.v p'' q hh = 0 := by
    intro p'' q hh hp''
    simp only [hw''def, hδv, Cochain.sub_v, Cochain.units_smul_v, pb_v, hw'0 p'' q hh hp'',
      Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p - 1 by omega), smul_zero, comp_zero, sub_self]
  have hz''0 : ∀ p'' q (hh : p'' + n = q), p - 1 < p'' → z''.v p'' q hh = 0 := by
    intro p'' q hh hp''
    by_cases hpp : p'' = p
    · subst hpp
      obtain rfl : q = s - 1 := by omega
      simp only [hz''def, hv, hδρ, Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v, pb_v,
        Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p'' - 1 by omega), smul_zero,
        add_zero]
      rw [← Category.assoc, ← HomologicalComplex.comp_f, c.w g, hu2]
      abel
    · simp only [hz''def, hv, hδρ, Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v, pb_v,
        hz'0 p'' q hh (by omega), Cochain.single_v_eq_zero _ _ _ _ _ hpp,
        Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p - 1 by omega), smul_zero, add_zero, comp_zero,
        sub_self]
  obtain ⟨k', f', b'', y'', hb'', hby''⟩ := ih l w'' z'' hw'' hz'' hw''0 hz''0
  refine ⟨k', f' ≫ h ≫ f, b'' + pb (K.map f') v + pb (K.map (f' ≫ h)) σ, y'' + ρ, ?_, ?_⟩
  · simp only [δ_add, δ_pb, hb'', hw''def, hw'def, pb_sub, pb_pb, Functor.map_comp, Category.assoc]
    abel
  · simp only [pb_add, pb_pb, c.w, hby'', hz''def, hz'def, δ_add]
    abel

end Step

section Main
variable {I : Type w} [Category.{w'} I] [IsCofiltered I] {K : I ⥤ CochainComplex C ℤ} (c : Cone K)
  (L : CochainComplex C ℤ)

theorem relative
    (hK : ∀ i (p : ℤ), 0 < p → IsZero ((K.obj i).X p)) (hc : ∀ p : ℤ, 0 < p → IsZero (c.pt.X p))
    (hL : ∀ p : ℤ, p < 0 → IsZero (L.X p))
    (hA : ∀ (p s : ℤ) (t : c.pt.X p ⟶ L.X s), t ≫ L.d s (s + 1) = 0 →
      ∃ (i : I) (u : (K.obj i).X p ⟶ L.X s) (y : c.pt.X p ⟶ L.X (s - 1)),
        u ≫ L.d s (s + 1) = 0 ∧ (c.π.app i).f p ≫ u = t + y ≫ L.d (s - 1) s)
    (hB : ∀ (p s : ℤ) (i : I) (u : (K.obj i).X p ⟶ L.X s), u ≫ L.d s (s + 1) = 0 →
      (∃ y : c.pt.X p ⟶ L.X (s - 1), (c.π.app i).f p ≫ u = y ≫ L.d (s - 1) s) →
      ∃ (k : I) (f : k ⟶ i) (y : (K.obj k).X p ⟶ L.X (s - 1)), (K.map f).f p ≫ u = y ≫ L.d (s - 1) s)
    (n m : ℤ) (hnm : n + 1 = m) (i : I) (w : Cochain (K.obj i) L m) (z : Cochain c.pt L n)
    (hw : δ m (m + 1) w = 0) (hz : δ n m z = pb (c.π.app i) w) :
    ∃ (k : I) (f : k ⟶ i) (b : Cochain (K.obj k) L n) (y : Cochain c.pt L (n - 1)),
      δ n m b = pb (K.map f) w ∧ pb (c.π.app k) b = z + δ (n - 1) n y := by
  have hA' : ∀ (p s s' : ℤ), s' + 1 = s → ∀ t : c.pt.X p ⟶ L.X s', t ≫ L.d s' s = 0 →
      ∃ (i : I) (u : (K.obj i).X p ⟶ L.X s') (y : c.pt.X p ⟶ L.X (s' - 1)),
        u ≫ L.d s' s = 0 ∧ (c.π.app i).f p ≫ u = t + y ≫ L.d (s' - 1) s' := by
    intro p s s' h
    subst h
    exact hA p s'
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = -|m| - 2 := ⟨_, rfl⟩
  have hall : ∀ k : ℕ, Q c L n m (a + k) := by
    intro k
    induction k with
    | zero =>
      simpa using Q_base c L hL n m a (by linarith [le_abs_self m]) (by linarith [le_abs_self m])
    | succ k ih =>
      have := Q_of_Q_sub_one c L hA' hB n m hnm (a + (k + 1 : ℕ)) (by
        rw [show a + ((k + 1 : ℕ) : ℤ) - 1 = a + k by push_cast; ring]; exact ih)
      exact this
  have h0 := hall (-a).toNat
  rw [show a + ((-a).toNat : ℤ) = 0 by
    have : 0 ≤ -a := by rw [ha]; linarith [abs_nonneg m]
    omega] at h0
  exact h0 i w z hw hz (fun p q h hp => (hK i p hp).eq_of_src _ _) (fun p q h hp => (hc p hp).eq_of_src _ _)

end Main

end GlobalTheory.CochainLim

open GlobalTheory.CochainLim in

theorem GlobalTheory.EtC.cont_cx_of_degreewise : ∀ (R : Type) [CommRing R] (I : Type) [SmallCategory I] [IsCofiltered I] (K : I ⥤ Cx R) (c : Cone K) (L : Cx R), (∀ i (p : ℤ), 0 < p → IsZero ((K.obj i).X p)) → (∀ p : ℤ, 0 < p → IsZero (c.pt.X p)) → (∀ p : ℤ, p < 0 → IsZero (L.X p)) → (∀ p s : ℤ, (∀ t : c.pt.X p ⟶ L.X s, t ≫ L.d s (s + 1) = 0 → ∃ (i : I) (u : (K.obj i).X p ⟶ L.X s) (y : c.pt.X p ⟶ L.X (s - 1)), u ≫ L.d s (s + 1) = 0 ∧ (c.π.app i).f p ≫ u = t + y ≫ L.d (s - 1) s) ∧ ∀ (i : I) (u : (K.obj i).X p ⟶ L.X s), u ≫ L.d s (s + 1) = 0 → (∃ y : c.pt.X p ⟶ L.X (s - 1), (c.π.app i).f p ≫ u = y ≫ L.d (s - 1) s) → ∃ (k : I) (f : k ⟶ i) (y : (K.obj k).X p ⟶ L.X (s - 1)), (K.map f).f p ≫ u = y ≫ L.d (s - 1) s) → ∀ n : ℤ, (∀ x : CohomologyClass c.pt L n, ∃ (i : I) (y : CohomologyClass (K.obj i) L n), cpre (Cocycle.ofHom (c.π.app i)) L n n (zero_add n) y = x) ∧ ∀ (i : I) (y : CohomologyClass (K.obj i) L n), cpre (Cocycle.ofHom (c.π.app i)) L n n (zero_add n) y = 0 → ∃ (k : I) (f : k ⟶ i), cpre (Cocycle.ofHom (K.map f)) L n n (zero_add n) y = 0 := by
  intro R _ I _ _ K c L hK hc hL hAB n
  have rel := relative c L hK hc hL (fun p s => (hAB p s).1) (fun p s => (hAB p s).2)
  constructor
  · intro x
    obtain ⟨ζ, rfl⟩ := x.mk_surjective
    obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
    obtain ⟨k, f, b, y, hb, hby⟩ := rel n (n + 1) rfl i 0 ζ.1 (by simp)
      (by rw [Cocycle.δ_eq_zero, pb_zero])
    rw [pb_zero] at hb
    refine ⟨k, CohomologyClass.mk (Cocycle.mk b (n + 1) rfl hb), ?_⟩
    rw [cpre_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨y, ?_⟩
    rw [Cocycle.coe_sub]
    change _ = pb (A := c.pt) (c.π.app k) b - ζ.1
    rw [hby]
    abel
  · intro i y hy
    obtain ⟨β, rfl⟩ := y.mk_surjective
    rw [cpre_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hy
    obtain ⟨γ, hγ⟩ := hy
    obtain ⟨k, f, b, y, hb, -⟩ := rel (n - 1) n (by omega) i β.1 γ (Cocycle.δ_eq_zero _ _) hγ
    refine ⟨k, f, ?_⟩
    rw [cpre_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨b, hb⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingBound
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem isEtaleAt_closure_of_disjoint : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    ∀ (Q : Ideal (GlobalTheory.KeyOriginNoeth.closure A R D)) [Q.IsPrime],
      (∀ a : A, a ≠ 0 → algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a) ∉ Q) →
      Algebra.IsEtaleAt R Q := by
  intro A R D _ _ _ _ _ _ _ _
  letI := closureAlg A R D
  intro Q _ hQ
  letI : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let SR : Submonoid R := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  let SC : Submonoid (closure A R D) := Algebra.algebraMapSubmonoid (closure A R D) SR
  have hCD : ∀ r : R, algebraMap (closure A R D) D (algebraMap R (closure A R D) r) = algebraMap R D r :=
    fun _ => rfl
  haveI : IsScalarTower R (closure A R D) D := IsScalarTower.of_algebraMap_eq (fun r => (hCD r).symm)
  have hunit : ∀ a : A, a ∈ nonZeroDivisors A → IsUnit (algebraMap R D (algebraMap A R a)) := by
    intro a ha
    have h1 : IsUnit (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) (algebraMap A R a)) :=
      IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A R) (⟨algebraMap A R a, a, ha, rfl⟩ : SR)
    rw [IsScalarTower.algebraMap_apply R (GlobalTheory.LocAcyc.GenFib A R) D]
    exact h1.map _
  haveI hloc : IsLocalization SC D := by
    refine (isLocalization_iff SC D).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩⟩
      exact hCD _ ▸ hunit a ha
    · intro d
      have hd : IsIntegral (GlobalTheory.LocAcyc.GenFib A R) d := Algebra.IsIntegral.isIntegral d
      obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization SR
        (Rₘ := GlobalTheory.LocAcyc.GenFib A R) d hd
      obtain ⟨a, ha, rfl⟩ := hm
      refine ⟨(⟨_, hmi⟩, ⟨algebraMap R (closure A R D) (algebraMap A R a), _, ⟨a, ha, rfl⟩, rfl⟩), ?_⟩
      show d * algebraMap (closure A R D) D (algebraMap R (closure A R D) (algebraMap A R a)) = _
      rw [hCD, mul_comm, ← Algebra.smul_def]
      rfl
    · intro x y h
      exact ⟨1, by rw [Subtype.ext h]⟩
  have hle : SC ≤ Q.primeCompl := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact hQ a (nonZeroDivisors.ne_zero ha)
  letI : Algebra D (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : IsScalarTower (closure A R D) D (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : IsLocalization (Algebra.algebraMapSubmonoid D Q.primeCompl) (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : Algebra.FormallyEtale D (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid D Q.primeCompl)
  haveI : Algebra.FormallyEtale R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.FormallyEtale.of_isLocalization SR
  haveI : Algebra.FormallyEtale R D := Algebra.FormallyEtale.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : IsScalarTower R D (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R (closure A R D) (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply (closure A R D) D (Localization.AtPrime Q), hCD])
  exact Algebra.FormallyEtale.comp R D (Localization.AtPrime Q)

end GlobalTheory.KeyOriginNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicPrimitiveRootsFilteredColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.PrimColim

variable {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}

theorem nat_apply {j k : J} (f : j ⟶ k) (a : D.obj j) :
    (c.ι.app k).hom ((D.map f).hom a) = (c.ι.app j).hom a := by
  rw [← c.w f]; rfl

theorem exists_rep (hc : IsColimit c) (x : c.pt) : ∃ (j : J) (y : D.obj j), (c.ι.app j).hom y = x := by
  obtain ⟨j, y, h⟩ := Concrete.isColimit_exists_rep D hc x
  exact ⟨j, y, h⟩

theorem exists_eq (hc : IsColimit c) {j : J} (a b : D.obj j) (h : (c.ι.app j).hom a = (c.ι.app j).hom b) :
    ∃ (k : J) (f : j ⟶ k), (D.map f).hom a = (D.map f).hom b := by
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc a b h
  refine ⟨IsFiltered.coeq f g, f ≫ IsFiltered.coeqHom f g, ?_⟩
  have hfg' : (D.map f).hom a = (D.map g).hom b := hfg
  have e := IsFiltered.coeq_condition f g
  calc (D.map (f ≫ IsFiltered.coeqHom f g)).hom a
      = (D.map (IsFiltered.coeqHom f g)).hom ((D.map f).hom a) := by rw [D.map_comp]; rfl
    _ = (D.map (IsFiltered.coeqHom f g)).hom ((D.map g).hom b) := by rw [hfg']
    _ = (D.map (g ≫ IsFiltered.coeqHom f g)).hom b := by rw [D.map_comp]; rfl
    _ = (D.map (f ≫ IsFiltered.coeqHom f g)).hom b := by rw [e]

theorem aeval_ringHom {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (a : A) (p : Polynomial ℤ) :
    Polynomial.aeval (φ a) p = φ (Polynomial.aeval a p) :=
  Polynomial.aeval_algHom_apply φ.toIntAlgHom a p

end GlobalTheory.EtC.PrimColim

open GlobalTheory.EtC.PrimColim in
theorem GlobalTheory.EtC.prim_filtered_colimit : ∀ (q : ℕ) (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ ζ : Prim q c.pt, ∃ (j : J) (ξ : Prim q (D.obj j)), Prim.map (c.ι.app j).hom ξ = ζ) ∧ ∀ (j : J) (ξ ξ' : Prim q (D.obj j)), Prim.map (c.ι.app j).hom ξ = Prim.map (c.ι.app j).hom ξ' → ∃ (k : J) (f : j ⟶ k), Prim.map (D.map f).hom ξ = Prim.map (D.map f).hom ξ' := by
  intro q J _ _ D c hc
  refine ⟨fun ζ => ?_, fun j ξ ξ' h => ?_⟩
  · obtain ⟨u, hu⟩ := ζ.2.1.exists_right_inv
    obtain ⟨j1, x, hx⟩ := exists_rep hc ζ.1
    obtain ⟨j2, y, hy⟩ := exists_rep hc u
    set k := IsFiltered.max j1 j2
    set x' := (D.map (IsFiltered.leftToMax j1 j2)).hom x
    set y' := (D.map (IsFiltered.rightToMax j1 j2)).hom y
    have hx' : (c.ι.app k).hom x' = ζ.1 := by rw [nat_apply, hx]
    have hy' : (c.ι.app k).hom y' = u := by rw [nat_apply, hy]
    have e1 : (c.ι.app k).hom ((q : D.obj k) * y') = (c.ι.app k).hom 1 := by
      rw [map_mul, map_natCast, hy', map_one, hu]
    obtain ⟨k1, f1, hf1⟩ := exists_eq hc _ _ e1
    set x1 := (D.map f1).hom x'
    have hx1 : (c.ι.app k1).hom x1 = ζ.1 := by rw [nat_apply, hx']
    have e2 : (c.ι.app k1).hom (Polynomial.aeval x1 (Polynomial.cyclotomic q ℤ)) = (c.ι.app k1).hom 0 := by
      rw [map_zero, ← aeval_ringHom, hx1]; exact ζ.2.2
    obtain ⟨k2, f2, hf2⟩ := exists_eq hc _ _ e2
    have hu1 : (q : D.obj k1) * (D.map f1).hom y' = 1 := by
      simpa only [map_mul, map_natCast, map_one] using hf1
    have hu2 : (q : D.obj k2) * (D.map f2).hom ((D.map f1).hom y') = 1 := by
      have := congrArg (D.map f2).hom hu1
      simpa only [map_mul, map_natCast, map_one] using this
    have hr : Polynomial.aeval ((D.map f2).hom x1) (Polynomial.cyclotomic q ℤ) = 0 := by
      rw [aeval_ringHom, hf2, map_zero]
    refine ⟨k2, ⟨(D.map f2).hom x1, IsUnit.of_mul_eq_one _ hu2, hr⟩, ?_⟩
    apply Subtype.ext
    change (c.ι.app k2).hom ((D.map f2).hom x1) = ζ.1
    rw [nat_apply, hx1]
  · have h1 : (c.ι.app j).hom ξ.1 = (c.ι.app j).hom ξ'.1 := congrArg Subtype.val h
    obtain ⟨k, f, hf⟩ := exists_eq hc _ _ h1
    exact ⟨k, f, Subtype.ext hf⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivCompM
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

variable {A B R : Type} [CommRing A] [CommRing B] [CommRing R]

def IsRingHomMod (π : B →+* A) (β : B →+* R) (n : ℕ) (φ : A → PowerSeries R) : Prop :=
  (∀ f g, (X : PowerSeries R) ^ n ∣ φ (f * g) - φ f * φ g) ∧
  (∀ f g, (X : PowerSeries R) ^ n ∣ φ (f + g) - (φ f + φ g)) ∧
  (X : PowerSeries R) ^ n ∣ φ 1 - 1 ∧
  (∀ b, (X : PowerSeries R) ^ n ∣ φ (π b) - C (β b))

def IsJet (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R) (n : ℕ)
    (φ : A → PowerSeries R) : Prop :=
  IsRingHomMod π β n φ ∧
  (∀ f, (X : PowerSeries R) ^ n ∣ φ (m f) - rescale 2 (φ f)) ∧
  (∀ f, constantCoeff (φ f) = β (ε f)) ∧
  (∀ f, coeff 1 (φ f) = δ f)

theorem deriv_comp_m (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (E : A →+ R)
    (hεπ : ε.comp π = RingHom.id B) (hmπ : m.comp π = π)
    (hm2 : ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2)
    (hE : ∀ f g, E (f * g) = β (ε f) * E g + β (ε g) * E f) (hEπ : ∀ a, E (π a) = 0) (f : A) :
    E (m f) = 2 * E f := by
  have hsq : ∀ x ∈ RingHom.ker ε ^ 2, E x = 0 := by
    intro x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [RingHom.mem_ker] at ha hb
      rw [hE, ha, hb]; simp
    · rw [map_add, ha, hb, add_zero]
  have hk : f - π (ε f) ∈ RingHom.ker ε := by
    rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply ε π, hεπ, RingHom.id_apply, sub_self]
  have h1 : m f = π (ε f) + (m (f - π (ε f)) - 2 * (f - π (ε f))) + (f - π (ε f)) + (f - π (ε f)) := by
    have : m (π (ε f)) = π (ε f) := by rw [← RingHom.comp_apply m π, hmπ]
    rw [map_sub, this]; ring
  have h2 : f = π (ε f) + (f - π (ε f)) := by ring
  rw [h1, map_add, map_add, map_add, hEπ, hsq _ (hm2 _ hk)]
  conv_rhs => rw [h2, map_add, hEπ]
  ring

end GlobalTheory.Nef.PathJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrRepEigenspacesSpanTop
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem eigenspaces_span_of_integral_action : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), (⨆ σ : Λ →+* O, eig C (⇑ρ) σ) = ⊤ := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ h ρ
  have hscal : ∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = padicToO p O c • (1 : Matrix (Fin h) (Fin h) O) :=
    fun c => (GlobalTheory.T.padic_ring_hom_unique_adic_complete p O).2 h (ρ.comp (algebraMap ℤ_[p] Λ)) c
  have hkill := GlobalTheory.T.scalar_rep_commute_and_annihilate C O Λ h ℤ_[p] (padicToO p O) ρ hscal
  have hdiag := GlobalTheory.T.commuting_semisimple_eigenspaces_span C (Fin h → C) Λ
    (fun a => Matrix.toLin' ((ρ a).map (algebraMap O C))) hkill.1 (fun a => by
      obtain ⟨f, hf, hsep⟩ := GlobalTheory.T.exists_separable_annihilating_poly p C ((algebraMap O C).comp (padicToO p O)) Λ a
      exact ⟨f.map ((algebraMap O C).comp (padicToO p O)), hsep, hkill.2 a f hf⟩)
  refine eq_top_iff.2 (hdiag ▸ iSup_le fun χ => ?_)
  by_cases hne : (⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C))) (χ a)) = ⊥
  · rw [hne]; exact bot_le
  · obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_ring_hom_of_joint_eigenvalue C v O Λ h hv ρ χ hne
    have hχ : χ = fun a => algebraMap O C (σ a) := funext fun a => (hσ a).symm
    subst hχ
    exact le_iSup_of_le σ le_rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfIsAffineOpenOfRingKrullDimLeOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory

theorem isIso_of_isAffine_of_coheight_le_one {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] [IsAffine X] [IsAffine Y] (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Set.range f) : IsIso f := by
  have h : IsIso (f.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_app_of_coheight_le_one f hf ⊤)
  have : IsIso (Spec.map f.appTop) := inferInstance
  have e : f = Y.isoSpec.hom ≫ Spec.map f.appTop ≫ X.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp
  rw [e]
  infer_instance

theorem eq_of_isAffineOpen_of_ringKrullDim_le_one (X : Scheme.{0}) [IsLocallyNoetherian X]
    [X.IsSeparated] (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (V V' : X.Opens)
    (hV : IsAffineOpen V) (hle : V ≤ V')
    (h : ∀ z ∈ V', ringKrullDim (X.presheaf.stalk z) ≤ 1 → z ∈ V) : V' = V := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  refine le_antisymm (fun z hz ↦ ?_) hle
  obtain ⟨_, ⟨N, hN, rfl⟩, hzN, hNV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz V'.isOpen
  have hN' : IsAffineOpen N := hN
  have hNV' : IsAffineOpen (N ⊓ V) := hN'.inf hV
  have : IsAffine N := hN'
  have : IsAffine (N ⊓ V : X.Opens) := hNV'
  have hiso : IsIso (X.homOfLE (inf_le_left : N ⊓ V ≤ N)) := by
    refine isIso_of_isAffine_of_coheight_le_one _ fun x hx ↦ ?_
    have hx' : Order.coheight (Scheme.Opens.ι N x) ≤ 1 := by rwa [coheight_apply_of_isOpenImmersion]
    have hxV : Scheme.Opens.ι N x ∈ V := h _ (hNV x.2) ((ringKrullDim_stalk_le_one_iff _).mpr hx')
    exact ⟨⟨x.1, x.2, hxV⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  obtain ⟨y, hy⟩ := (X.homOfLE (inf_le_left : N ⊓ V ≤ N)).surjective ⟨z, hzN⟩
  have hyz : y.1 = z := (Scheme.homOfLE_apply _ y).symm.trans (congrArg Subtype.val hy)
  exact hyz ▸ y.2.2

end GlobalTheory
end

