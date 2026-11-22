import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.IntegralFamilyFirstZeroSecond

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MemHHaOfCoeffFunctional
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoeffFunctional

open MvPolynomial

variable {σ K L : Type} [Field K] [Field L] [Algebra K L]

def coeffMap (φ : L →ₗ[K] K) (P : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ μ ∈ P.support, monomial μ (φ (P.coeff μ))

theorem coeff_coeffMap (φ : L →ₗ[K] K) (P : MvPolynomial σ L) (μ : σ →₀ ℕ) :
    (coeffMap φ P).coeff μ = φ (P.coeff μ) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

theorem coeffMap_add (φ : L →ₗ[K] K) (P Q : MvPolynomial σ L) :
    coeffMap φ (P + Q) = coeffMap φ P + coeffMap φ Q := by
  ext μ
  simp [coeff_coeffMap]

theorem coeffMap_zero (φ : L →ₗ[K] K) : coeffMap φ (0 : MvPolynomial σ L) = 0 := by
  ext μ
  simp [coeff_coeffMap]

theorem coeffMap_map_mul_C (φ : L →ₗ[K] K) (A : MvPolynomial σ K) (c : L) :
    coeffMap φ (MvPolynomial.C c * MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.C (φ c) * A := by
  ext μ
  rw [coeff_coeffMap, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm c, ← Algebra.smul_def,
    map_smul, smul_eq_mul, mul_comm]

theorem coeffMap_comm (φ : L →ₗ[K] K) (f : MvPolynomial σ L →ₗ[L] MvPolynomial σ L)
    (g : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (h : ∀ A, f (MvPolynomial.map (algebraMap K L) A) = MvPolynomial.map (algebraMap K L) (g A))
    (P : MvPolynomial σ L) : coeffMap φ (f P) = g (coeffMap φ P) := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, coeffMap_add, coeffMap_add, map_add, hp, hq]
  | monomial μ c =>
    have e : (monomial μ c : MvPolynomial σ L) =
        MvPolynomial.C c * MvPolynomial.map (algebraMap K L) (monomial μ 1) := by
      rw [map_monomial, map_one, C_mul_monomial, mul_one]
    rw [e, coeffMap_map_mul_C, C_mul', map_smul, h, ← C_mul', coeffMap_map_mul_C, C_mul', C_mul',
      map_smul]

variable {T : Type} (r : T → ℕ) (n : ℕ)

theorem lap_one_map (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ'))
    (A : MvPolynomial (Letter T r n) K) :
    lap r n L 1 τ τ' a a' (MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.map (algebraMap K L) (lap r n K 1 τ τ' a a' A) := by
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  by_cases hb : b = b'
  · subst hb
    simp [pderiv_map]
  · simp [Matrix.one_apply_ne hb]

theorem rowShift_map (s : T) (i i' : Fin (r s)) (t : K) (A : MvPolynomial (Letter T r n) K) :
    rowShift r n L s i i' (algebraMap K L t) (MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.map (algebraMap K L) (rowShift r n K s i i' t A) := by
  induction A using MvPolynomial.induction_on with
  | C c => simp [rowShift]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p l hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [rowShift, aeval_X]
    split_ifs <;> simp

theorem mem_HHa_of_coeff_functional :
    ∀ (T : Type) (r : T → ℕ) (n : ℕ) (K C : Type) [Field K] [Field C] [Algebra K C] (φ : C →ₗ[K] K) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) C) (Q : MvPolynomial (Letter T r n) K), (∀ μ, Q.coeff μ = φ (P.coeff μ)) → P ∈ HHa r n C cc isX a → Q ∈ HHa r n K cc isX a := by
  intro T r n K L _ _ _ φ cc isX a P Q hQ hP
  have hQ' : Q = coeffMap φ P := by
    ext μ
    rw [hQ, coeff_coeffMap]
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ b b'
    rw [hQ', ← coeffMap_comm φ _ _ (lap_one_map r n τ (cc τ) b b') P, h1 τ hτ b b', coeffMap_zero]
  · intro s i i' hi t
    have := coeffMap_comm φ (rowShift r n L s i i' (algebraMap K L t)).toLinearMap
      (rowShift r n K s i i' t).toLinearMap (rowShift_map r n s i i' t) P
    simp only [AlgHom.toLinearMap_apply] at this
    rw [hQ', ← this, h2 s i i' hi]
  · intro m hm
    refine h3 m ?_
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [hQ, h0, map_zero])

end GlobalTheory.CoeffFunctional
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NablaValueCopiesBilinear
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

section NabLin

variable {R : Type} [CommRing R] {d n : ℕ}

theorem dofN_add (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (f g : PS R n d) :
    DofN F b u (f + g) = DofN F b u f + DofN F b u g := by
  simp only [DofN, map_add, mul_add, Finset.sum_add_distrib]

theorem dofN_smul (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (t : R) (f : PS R n d) :
    DofN F b u (t • f) = t • DofN F b u f := by
  simp only [DofN, Derivation.map_smul, map_smul, mul_smul_comm, Finset.smul_sum]

theorem dofN_iterate_add (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (f g : PS R n d) :
    (DofN F b u)^[k] (f + g) = (DofN F b u)^[k] f + (DofN F b u)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, dofN_add]

theorem dofN_iterate_smul (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (t : R) (f : PS R n d) :
    (DofN F b u)^[k] (t • f) = t • (DofN F b u)^[k] f := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, dofN_smul]

variable {ι : Type} [Fintype ι]

theorem dmonN_add (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ)
    (f g : PS R n d) :
    DmonN F cp u m (f + g) = DmonN F cp u m f + DmonN F cp u m g := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, dofN_iterate_add]

theorem dmonN_smul (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ)
    (t : R) (f : PS R n d) :
    DmonN F cp u m (t • f) = t • DmonN F cp u m f := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, dofN_iterate_smul]

theorem dpolyN_eq_sum_of_subset (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f : PS R n d) (s : Finset (ι →₀ ℕ)) (hs : P.support ⊆ s) :
    DpolyN F cp u P f = ∑ m ∈ s, MvPowerSeries.C (P.coeff m) * DmonN F cp u m f := by
  unfold DpolyN
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.mp hm, map_zero, zero_mul]

theorem dpolyN_add_right (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f g : PS R n d) :
    DpolyN F cp u P (f + g) = DpolyN F cp u P f + DpolyN F cp u P g := by
  simp only [DpolyN, dmonN_add, mul_add, Finset.sum_add_distrib]

theorem dpolyN_smul_right (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (t : R) (f : PS R n d) :
    DpolyN F cp u P (t • f) = t • DpolyN F cp u P f := by
  simp only [DpolyN, dmonN_smul, mul_smul_comm, Finset.smul_sum]

theorem dpolyN_add_left (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P Q : MvPolynomial ι R) (f : PS R n d) :
    DpolyN F cp u (P + Q) f = DpolyN F cp u P f + DpolyN F cp u Q f := by
  classical
  rw [dpolyN_eq_sum_of_subset F cp u (P + Q) f (P.support ∪ Q.support) MvPolynomial.support_add,
    dpolyN_eq_sum_of_subset F cp u P f (P.support ∪ Q.support) Finset.subset_union_left,
    dpolyN_eq_sum_of_subset F cp u Q f (P.support ∪ Q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, map_add, add_mul]

theorem dpolyN_C_mul_left (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (t : R) (P : MvPolynomial ι R) (f : PS R n d) :
    DpolyN F cp u (MvPolynomial.C t * P) f = MvPowerSeries.C t * DpolyN F cp u P f := by
  have hs : (MvPolynomial.C t * P).support ⊆ P.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [MvPolynomial.coeff_C_mul, h0, mul_zero])
  rw [dpolyN_eq_sum_of_subset F cp u _ f P.support hs, DpolyN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul, mul_assoc]

end NabLin

theorem nabValN_bilinear : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), (∀ (f g : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (f + g) cp u P = nabValN B K h w0 m f cp u P + nabValN B K h w0 m g cp u P) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (t • f) cp u P = t * nabValN B K h w0 m f cp u P) ∧ (∀ (f : PS K n d) (P Q : MvPolynomial ι K), nabValN B K h w0 m f cp u (P + Q) = nabValN B K h w0 m f cp u P + nabValN B K h w0 m f cp u Q) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m f cp u (MvPolynomial.C t * P) = t * nabValN B K h w0 m f cp u P) := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u
  refine ⟨fun f g P => ?_, fun t f P => ?_, fun f P Q => ?_, fun t f P => ?_⟩
  · simp only [nabValN, add_mul, dpolyN_add_right, map_add]
  · simp only [nabValN]
    rw [smul_mul_assoc, dpolyN_smul_right, MvPowerSeries.smul_eq_C_mul, map_mul,
      MvPowerSeries.constantCoeff_C]
  · simp only [nabValN, dpolyN_add_left, map_add]
  · simp only [nabValN]
    rw [dpolyN_C_mul_left, map_mul, MvPowerSeries.constantCoeff_C]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PderivEvSecond
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.GaugeSecondDeriv

variable {k : Type} [CommRing k] {d : ℕ}

theorem cz12 : CZ (![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) :=
  CZ.cons (cc_pt 1) (CZ.cons (cc_pt 2) CZ.nil)

theorem pderiv_ev_second (h : PS k 2 d) (q : Pt k 3 d) (hq : ∀ c, constantCoeff (q c) = 0) (b : Fin d) :
    pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, q] h) =
      ∑ j, ev (n := 3) ![pt k d 0, q] (pderiv k ((1 : Fin 2), j) h) * pderiv k ((2 : Fin 3), b) (q j) := by
  have hc : CZ (![pt k (n := 3) d 0, q] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 0) (CZ.cons hq CZ.nil)
  rw [pderiv_ev hc, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [pderiv_pt]

theorem ev_pderiv_add (F : PS k 2 d) (b : Fin d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0]
      (pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 1, pt k d 2] F)) =
      ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) F) := by
  rw [pderiv_ev cz12, Fintype.sum_prod_type, Fin.sum_univ_two]
  have e : ((1 : Fin 3) = 2) = False := by simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_pt, Prod.mk.injEq, e, false_and,
    if_false, mul_zero, Finset.sum_const_zero, zero_add, true_and, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [ev_ev czZ cz12]
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czZ]

theorem ev_add_axis (G : FGLaw k d) (c : Fin d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] (G.F c)) =
      pt k (n := 2) d 1 c := by
  have h1 : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt 1) CZ.nil
  have e := congrArg (ev (n := 2) ![pt k d 1]) (formalGroupLaw_ev_x_zero G c)
  rw [ev_ev h1 cz1, ev_X h1] at e
  rw [ev_ev czZ cz12]
  refine Eq.trans ?_ e
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czZ, ev_X h1, ev_zero' h1]

theorem main : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ b : Fin d, ∃ K : PS R 2 d, ∑ j, ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) (B.FK k j)) * pderiv k ((1 : Fin 2), j) h =
    FB.toK k K + ev (n := 2) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) h)) := by
  intro R _ d O _ _ k _ _ _ B h hc b
  have hA : ∀ c, constantCoeff (addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2) c) = 0 :=
    fun c => constantCoeff_ev cz12 ((lawK k B).const c)
  have c02 : CZ (![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have cA : CZ (![pt k (n := 3) d 0, addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2)] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons hA CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
      ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h) = 0 := by
    rw [map_sub, map_add, cc_ev' cz01, cc_ev' c02, cc_ev' cA, cc_h hc]
    simp
  have hH := ig_dlog B.ph2 (constantCoeff_second_factor B) _ hH0 hc.ph2 ((2 : Fin 3), b)
  have h2 := ig_ev czZ integral_family_pair_zero hH
  have t1 : pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 1] h) = 0 :=
    pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  have t2 : ev (n := 2) ![pt k d 0, pt k d 1, 0]
      (pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 2] h)) =
      ev (n := 2) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) h) := by
    rw [pderiv_ev_second h _ (cc_pt 2)]
    simp only [pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ev_ev czZ c02]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X czZ]
  have t3 : ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), b)
      (ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)) =
      ∑ j, ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) (B.FK k j)) *
        pderiv k ((1 : Fin 2), j) h := by
    rw [pderiv_ev_second h _ hA, ev_sum czZ]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : (fun i c => ev (n := 2) ![pt k d 0, pt k d 1, 0]
        ((![pt k (n := 3) d 0, addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2)] : Fin 2 → Pt k 3 d) i c)) =
        fun i => pt k (n := 2) d i := by
      funext i c
      fin_cases i
      · simp [pt_apply, ev_X czZ]
      · exact ev_add_axis (lawK k B) c
    rw [ev_mul czZ, ev_ev czZ cA, e, ev_pt, mul_comm]
    congr 1
    exact ev_pderiv_add (B.FK k j) b
  rw [map_sub, map_add, t1, zero_add, ev_sub czZ, t2, t3] at h2
  obtain ⟨K, hK⟩ := RingHom.mem_range.1 h2
  refine ⟨-K, ?_⟩
  rw [FB.toK, map_neg, hK]
  ring

end GlobalTheory.GaugeSecondDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SaturatedBlocksSummand
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.SatBlocks

def intRing {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {z | (0 : WithTop ℝ) ≤ v z}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [v.map_mul]; exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    exact v.map_le_add ha hb
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rwa [v.map_neg]

theorem mem_intRing {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (z : C) :
    z ∈ intRing v ↔ ((0 : ℝ) : WithTop ℝ) ≤ v z := Iff.rfl

theorem ne_zero_of_val_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {z : C}
    (h : v z = 0) : z ≠ 0 := by
  rintro rfl
  simp at h

theorem inv_mem_of_val_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {z : C}
    (h : v z = 0) : z⁻¹ ∈ intRing v := by
  have h1 : v (z * z⁻¹) = 0 := by rw [mul_inv_cancel₀ (ne_zero_of_val_zero v h)]; simp
  rw [v.map_mul, h, zero_add] at h1
  exact h1.ge

theorem exists_projector {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {O A : Type}
    [DecidableEq A] {n : A → ℕ} {d : ℕ} (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C)
    (u : (Σ a : A, Fin (n a)) → Fin d → C)
    (hM : ∀ x i j, M x i j ∈ intRing v) (he : ∀ a x, em a x ∈ intRing v)
    (hu : ∀ x q, (M x).mulVec (u q) = em q.1 x • u q)
    (hs : ∀ a a', a ≠ a' → ∃ x, v (em a x - em a' x) = 0) (a : A) (S : Finset A) (ha : a ∉ S) :
    ∃ (P : Matrix (Fin d) (Fin d) C) (c : A → C), (∀ i j, P i j ∈ intRing v) ∧
      (∀ q, P.mulVec (u q) = c q.1 • u q) ∧ c a = 1 ∧ ∀ b ∈ S, c b = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ => 1, ?_, by simp, rfl, by simp⟩
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | insert b S hb ih =>
    rw [Finset.mem_insert, not_or] at ha
    obtain ⟨P, c, hP, hPu, hca, hcS⟩ := ih ha.2
    obtain ⟨x, hx⟩ := hs a b ha.1
    refine ⟨((em a x - em b x)⁻¹ • (M x - em b x • (1 : Matrix (Fin d) (Fin d) C))) * P,
      fun e => (em a x - em b x)⁻¹ * (em e x - em b x) * c e, ?_, ?_, ?_, ?_⟩
    · intro i j
      rw [Matrix.mul_apply]
      refine sum_mem fun k _ => mul_mem ?_ (hP k j)
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      refine mul_mem (inv_mem_of_val_zero v hx) (sub_mem (hM x i k) (mul_mem (he b x) ?_))
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro q
      rw [← Matrix.mulVec_mulVec, hPu, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, hu]
      ext k
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    · simp only [hca, mul_one]
      exact inv_mul_cancel₀ (ne_zero_of_val_zero v hx)
    · intro e he'
      rcases Finset.mem_insert.1 he' with rfl | h
      · simp
      · simp [hcS e h]

theorem saturated_blocks_summand : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (O A : Type) [Fintype A] [DecidableEq A] (n : A → ℕ) (d : ℕ) (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C) (u : (Σ a : A, Fin (n a)) → Fin d → C), (∀ x i j, ((0 : ℝ) : WithTop ℝ) ≤ v (M x i j)) → (∀ a x, ((0 : ℝ) : WithTop ℝ) ≤ v (em a x)) → (∀ x q, (M x).mulVec (u q) = em q.1 x • u q) → (∀ a a', a ≠ a' → ∃ x, v (em a x - em a' x) = 0) → (∀ a, ∃ w : Fin d → Fin (n a) → C, (∀ s i, ((0 : ℝ) : WithTop ℝ) ≤ v (w s i)) ∧ ∀ i i', ∑ s, u ⟨a, i⟩ s * w s i' = if i = i' then 1 else 0) → ∃ w : Fin d → (Σ a : A, Fin (n a)) → C, (∀ s q, ((0 : ℝ) : WithTop ℝ) ≤ v (w s q)) ∧ ∀ q q', ∑ s, u q s * w s q' = if q = q' then 1 else 0 := by
  intro C _ v O A _ _ n d M em u hM he hu hs hw
  choose w hwi hw using hw
  have key := fun a : A => exists_projector v M em u hM he hu hs a (Finset.univ.erase a)
    (Finset.notMem_erase a _)
  choose P c hP hPu hca hcS using key
  refine ⟨fun s q => ∑ t, P q.1 t s * w q.1 t q.2, ?_, ?_⟩
  · intro s q
    exact (mem_intRing v _).1
      (sum_mem fun t _ => mul_mem (hP _ _ _) ((mem_intRing v _).2 (hwi _ _ _)))
  · rintro ⟨b, j⟩ ⟨a, i⟩
    have h1 : ∑ s, u ⟨b, j⟩ s * ∑ t, P a t s * w a t i
        = ∑ t, (P a).mulVec (u ⟨b, j⟩) t * w a t i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
    dsimp only
    rw [h1, hPu]
    by_cases hba : b = a
    · subst hba
      simp only [hca, one_smul, hw]
      simp
    · have h0 : c a b = 0 := hcS a b (by simp [hba])
      rw [if_neg (fun h => hba (congrArg Sigma.fst h))]
      simp [h0]

end GlobalTheory.SatBlocks
end

