import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetOneAddSmulBlkMem
section
open scoped BigOperators
open Polynomial

namespace GlobalTheory.BlockDet

def blk {B : Type} {g n : ℕ} (M : Fin g → Fin g → Matrix (Fin n) (Fin n) B) :
    Matrix (Fin g × Fin n) (Fin g × Fin n) B :=
  Matrix.of fun pa qb => M pa.1 qb.1 pa.2 qb.2

def splitIdx (g n : ℕ) : Fin n ⊕ (Fin g × Fin n) ≃ Fin (g + 1) × Fin n where
  toFun := Sum.elim (fun a => (0, a)) (fun pa => (pa.1.succ, pa.2))
  invFun := fun pa => Fin.cases (motive := fun _ => Fin n ⊕ (Fin g × Fin n)) (Sum.inl pa.2)
    (fun p => Sum.inr (p, pa.2)) pa.1
  left_inv := by rintro (a | ⟨p, a⟩) <;> simp
  right_inv := by
    rintro ⟨p, a⟩
    refine Fin.cases ?_ (fun p => ?_) p <;> simp

theorem det_one_add_smul_blk_mem {B : Type} [CommRing B] {n : ℕ} (S : Subring B)
    (A : Subring (Matrix (Fin n) (Fin n) B)) (hdet : ∀ a ∈ A, a.det ∈ S) (e : B)
    (he : IsNilpotent e) (heA : ∀ a ∈ A, e • a ∈ A) (g : ℕ) :
    ∀ Θ : Fin g → Fin g → Matrix (Fin n) (Fin n) B, (∀ p q, Θ p q ∈ A) →
      (1 + e • blk Θ).det ∈ S := by
  induction g with
  | zero => intro Θ _; rw [Matrix.det_isEmpty]; exact S.one_mem
  | succ g ih =>
    intro Θ hΘ
    have hnil : IsNilpotent (⟨e • Θ 0 0, heA _ (hΘ 0 0)⟩ : A) := by
      obtain ⟨k, hk⟩ := he
      refine ⟨k, Subtype.ext ?_⟩
      simp [_root_.smul_pow, hk]
    obtain ⟨w, hw⟩ := hnil.isUnit_one_add
    set u : Matrix (Fin n) (Fin n) B := ((w⁻¹ : Aˣ) : A).1 with hu
    have huA : u ∈ A := ((w⁻¹ : Aˣ) : A).2
    have hw' : ((w : A) : Matrix (Fin n) (Fin n) B) = 1 + e • Θ 0 0 := by rw [hw]; rfl
    letI : Invertible (1 + e • Θ 0 0) :=
      ⟨u, by rw [← hw', hu, ← Subring.coe_mul]; simp, by rw [← hw', hu, ← Subring.coe_mul]; simp⟩
    have hinv : ⅟(1 + e • Θ 0 0) = u := rfl
    let Bm : Matrix (Fin n) (Fin g × Fin n) B := Matrix.of fun a qb => Θ 0 qb.1.succ a qb.2
    let Cm : Matrix (Fin g × Fin n) (Fin n) B := Matrix.of fun pa b => Θ pa.1.succ 0 pa.2 b
    have h1 : (1 + e • blk Θ).submatrix (splitIdx g n) (splitIdx g n) =
        Matrix.fromBlocks (1 + e • Θ 0 0) (e • Bm) (e • Cm)
          (1 + e • blk (fun p q => Θ p.succ q.succ)) := by
      ext (a | ⟨p, a⟩) (b | ⟨q, b⟩) <;>
        simp [splitIdx, blk, Bm, Cm, Matrix.one_apply, (Fin.succ_ne_zero _).symm]
    have h2 : (1 + e • blk (fun p q => Θ p.succ q.succ)) - (e • Cm) * u * (e • Bm) =
        1 + e • blk (fun p q => Θ p.succ q.succ - e • (Θ p.succ 0 * u * Θ 0 q.succ)) := by
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, add_sub_assoc, ← smul_sub]
      congr 2
    rw [← Matrix.det_submatrix_equiv_self (splitIdx g n), h1, Matrix.det_fromBlocks₁₁, hinv, h2]
    refine S.mul_mem (hdet _ (A.add_mem A.one_mem (heA _ (hΘ 0 0)))) (ih _ fun p q => ?_)
    exact A.sub_mem (hΘ _ _) (heA _ (A.mul_mem (A.mul_mem (hΘ _ _) huA) (hΘ _ _)))

def swapM {O X : Type} {n : ℕ} (a : X → Matrix (Fin n) (Fin n) O) :
    Matrix (Fin n) (Fin n) (X → O) :=
  Matrix.of fun i j x => a x i j

theorem det_sum_smul_mem {O X B : Type} [CommRing O] [CommRing B] (T : Subalgebra O (X → O))
    {n : ℕ} (ι : (X → O) →+* B) (S : Subring B) (hS : ∀ t ∈ T, ι t ∈ S) {m : ℕ}
    (a : Fin m → X → Matrix (Fin n) (Fin n) O)
    (h : ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det
      (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T)
    (c : Fin m → B) (hc : ∀ k, c k ∈ S) :
    (∑ k, c k • (swapM (a k)).map ι).det ∈ S := by
  set D : MvPolynomial (Fin m) (X → O) := Matrix.det
    (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) • (swapM (a k)).map MvPolynomial.C)
    with hD
  have hco : ∀ d, MvPolynomial.coeff d D ∈ T := by
    intro d
    convert h d using 1
    funext x
    have : MvPolynomial.coeff d D x =
        MvPolynomial.coeff d (MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x) D) := by
      rw [MvPolynomial.coeff_map]; rfl
    rw [this, hD, RingHom.map_det]
    congr 2
    ext i j : 1
    simp [swapM, Matrix.sum_apply]
  have hev : (∑ k, c k • (swapM (a k)).map ι).det = MvPolynomial.eval₂Hom ι c D := by
    rw [hD, RingHom.map_det]
    congr 1
    ext i j : 1
    simp [Matrix.sum_apply]
  rw [hev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  exact S.sum_mem fun d _ => S.mul_mem (hS _ (hco d)) (S.prod_mem fun k _ => S.pow_mem (hc k) _)

theorem main : ∀ {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (n : ℕ) (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O)), (∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T) → ∀ (g : ℕ) (Θ : Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ p q, Θ p q ∈ R) → (fun x => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => Θ pa.1 qb.1 x pa.2 qb.2)) ∈ T := by
  intro O X _ T n R hR g Θ hΘ
  set N := Fintype.card (Fin g × Fin n) with hN
  let I : Ideal (X → O)[X] := Ideal.span {Polynomial.X ^ (N + 1)}
  let π : (X → O)[X] →+* (X → O)[X] ⧸ I := Ideal.Quotient.mk I
  let ι : (X → O) →+* (X → O)[X] ⧸ I := π.comp Polynomial.C
  let S : Subring ((X → O)[X] ⧸ I) := (π.comp (Polynomial.mapRingHom T.val.toRingHom)).range
  have hS : ∀ t ∈ T, ι t ∈ S := fun t ht => ⟨Polynomial.C ⟨t, ht⟩, by simp [ι]⟩
  have heS : π Polynomial.X ∈ S := ⟨Polynomial.X, by simp⟩
  have he : IsNilpotent (π Polynomial.X) :=
    ⟨N + 1, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)⟩
  let G : Set (Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) :=
    {M | ∃ a ∈ R, (swapM a).map ι = M}
  have hone : (1 : Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) ∈ G := by
    refine ⟨1, R.one_mem, ?_⟩
    have : swapM (1 : X → Matrix (Fin n) (Fin n) O) = 1 := by
      ext i j x
      simp [swapM, Matrix.one_apply, apply_ite (fun f : X → O => f x)]
    rw [this, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hmul : ∀ M ∈ G, ∀ M' ∈ G, M * M' ∈ G := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨a * b, R.mul_mem ha hb, ?_⟩
    rw [← Matrix.map_mul]
    congr 1
    ext i j x
    simp [swapM, Matrix.mul_apply]
  let A : Subalgebra S (Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) :=
    (Submodule.span S G).toSubalgebra (Submodule.subset_span hone) (by
      intro x y hx hy
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨M, hM, M', hM', rfl⟩
      exact hmul M hM M' hM')
  have hdet : ∀ a ∈ A.toSubring, a.det ∈ S := by
    intro a ha
    obtain ⟨m, c, f, rfl⟩ := Submodule.mem_span_set'.1 (show a ∈ Submodule.span S G from ha)
    choose b hb hbf using fun k => (f k).2
    have := det_sum_smul_mem T ι S hS b (hR m b hb) (fun k => c k) (fun k => (c k).2)
    simp only [hbf] at this
    exact this
  have key := det_one_add_smul_blk_mem S A.toSubring hdet (π Polynomial.X) he
    (fun a ha => A.smul_mem ha (⟨_, heS⟩ : S)) g (fun p q => (swapM (Θ p q)).map ι)
    (fun p q => Submodule.subset_span (R := S) (s := G) ⟨_, hΘ p q, rfl⟩)
  set M : Matrix (Fin g × Fin n) (Fin g × Fin n) (X → O) := blk fun p q => swapM (Θ p q) with hM
  set F : (X → O)[X] := Matrix.det ((Polynomial.X : (X → O)[X]) • M.map Polynomial.C +
    (1 : Matrix (Fin g × Fin n) (Fin g × Fin n) (X → O)).map Polynomial.C) with hF
  have hπ : (1 + π Polynomial.X • blk fun p q => (swapM (Θ p q)).map ι).det = π F := by
    rw [hF, RingHom.map_det, Matrix.map_one _ (map_zero _) (map_one _), map_add, map_one, add_comm]
    congr 2
  rw [hπ] at key
  obtain ⟨t, ht⟩ := key
  have hdvd : Polynomial.X ^ (N + 1) ∣ t.map T.val.toRingHom - F :=
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 ht)
  have hc := Polynomial.X_pow_dvd_iff.1 hdvd N (Nat.lt_succ_self N)
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, hF, hN, Polynomial.coeff_det_X_add_C_card,
    sub_eq_zero] at hc
  have hmem : M.det ∈ T := by rw [← hc]; exact (t.coeff _).2
  convert hmem using 1
  funext x
  exact ((Pi.evalRingHom (fun _ : X => O) x).map_det M).symm

end GlobalTheory.BlockDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetTraceGramBlockMatrix
section
open Matrix

namespace GlobalTheory

theorem det_traceGram_blockMatrix {E E' : Type} [Field E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] {d n : ℕ}
    (w : Module.Basis (Fin d) E E') (H : Matrix (Fin n) (Fin n) E') (v : Fin d → E') :
    (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1)).det
      = (Matrix.of fun k l => Algebra.trace E E' (w k * v l)).det ^ n * Algebra.norm E H.det := by
  classical
  set D : Matrix (Fin d) (Fin d) E := Matrix.of fun k m => Algebra.trace E E' (w k * w m) with hD
  set C : Matrix (Fin d) (Fin d) E := w.toMatrix v with hC
  set Λ : Matrix (Fin d × Fin n) (Fin d × Fin n) E :=
    Matrix.of fun p q => Algebra.leftMulMatrix w (H p.2 q.2) p.1 q.1 with hΛ

  have htr : ∀ k (y : E'), Algebra.trace E E' (w k * y) = ∑ m, D k m * w.repr y m := by
    intro k y
    calc Algebra.trace E E' (w k * y) = Algebra.trace E E' (w k * ∑ m, w.repr y m • w m) := by
          rw [w.sum_repr y]
      _ = ∑ m, D k m * w.repr y m := by
          simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul, hD, of_apply]
          exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hrep : ∀ (x y : E') m, w.repr (x * y) m = ∑ s, Algebra.leftMulMatrix w x m s * w.repr y s := by
    intro x y m
    have := congrFun (Algebra.leftMulMatrix_mulVec_repr w x y) m
    rw [← this]; simp [Matrix.mulVec, dotProduct]
  have hDC : D * C = Matrix.of fun k l => Algebra.trace E E' (w k * v l) := by
    ext k l
    simp [Matrix.mul_apply, htr, hC, Module.Basis.toMatrix_apply]
  have hM : (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1))
      = blockDiagonal (fun _ : Fin n => D) * Λ * blockDiagonal (fun _ : Fin n => C) := by
    ext ⟨k, i⟩ ⟨l, j⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul, mul_ite, zero_mul,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, of_apply, hΛ]
    rw [mul_assoc, htr]
    simp only [hrep, hC, Module.Basis.toMatrix_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hΛdet : Λ.det = Algebra.norm E H.det := by
    let bt := w.smulTower (Pi.basisFun E' (Fin n))
    have hmat : LinearMap.toMatrix bt bt ((Matrix.toLin' H).restrictScalars E) = Λ := by
      ext ⟨k, i⟩ ⟨l, j⟩
      simp [LinearMap.toMatrix_apply, bt, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr, hΛ,
        Algebra.leftMulMatrix_eq_repr_mul, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [mul_comm]
    rw [← hmat, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  rw [hM, det_mul, det_mul, det_blockDiagonal, det_blockDiagonal, hΛdet, ← hDC, det_mul]
  simp [Finset.prod_const, mul_pow]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubIffMapMkEq
section
universe u_1 u_2 u_3

namespace GlobalTheory.DvdSubMapMk

theorem dvd_sub_iff_map_mk_eq {R : Type u_1} [inst : CommRing R] {p : Type u_2} {q : Type u_3}
    (a : R) (A B : Matrix p q R) :
    (∀ (i : p) (j : q), a ∣ (A - B) i j) ↔
      Matrix.map A (⇑(Ideal.Quotient.mk (Ideal.span {a})) : R → R ⧸ Ideal.span {a}) =
        Matrix.map B (⇑(Ideal.Quotient.mk (Ideal.span {a})) : R → R ⧸ Ideal.span {a}) := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton,
    Matrix.sub_apply]

end GlobalTheory.DvdSubMapMk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
section
noncomputable section

open PowerSeries

namespace GlobalTheory.NB.LT

def F (R : Type) [CommRing R] (l : ℕ) : Polynomial R :=
  Polynomial.X * (Polynomial.X + Polynomial.C (l : R)) ^ (l - 1)

def P (R : Type) [CommRing R] (l k : ℕ) : Polynomial R :=
  Nat.rec (Polynomial.X + Polynomial.C (l : R)) (fun _ p => p.comp (F R l)) k

abbrev EE (R : Type) [CommRing R] (l : ℕ) : Type :=
  AdicCompletion (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) (Localization.Away (X : R⟦X⟧))

variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
private lemma subsingleton_of_isHausdorff_whole_ideal {I : Ideal R} [IsHausdorff I R] (h : I = ⊤) :
    Subsingleton R := by
  subst h
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : R, z = 0 := fun z =>
    IsHausdorff.haus ‹_› z fun n => by simp [Ideal.top_pow, SModEq.top]
  rw [key x, key y]

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
private lemma order_map_toNat_eq_natDegree_of_isDistinguishedAt {I : Ideal R} {p : Polynomial R}
    (H : p.IsDistinguishedAt I) (hI : I ≠ ⊤) :
    ((map (Ideal.Quotient.mk I)) (p : R⟦X⟧)).order.toNat = p.natDegree := by
  have h1 : constantCoeff (1 : R⟦X⟧) ∉ I := by
    simpa [Ideal.eq_top_iff_one] using hI
  have := H.coe_natDegree_eq_order_map (p : R⟦X⟧) 1 h1 (by simp)
  rw [← this]
  simp

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in

theorem _root_.GlobalTheory.NB.LT.exists_poly_mod [Nontrivial R] {I : Ideal R} [IsAdicComplete I R] {p : Polynomial R}
    (H : p.IsDistinguishedAt I) (a : R⟦X⟧) :
    ∃ r : Polynomial R, r.degree < p.degree ∧ (p : R⟦X⟧) ∣ a - r := by
  have hI : I ≠ ⊤ := by
    intro h
    have := subsingleton_of_isHausdorff_whole_ideal (I := I) h
    exact not_subsingleton R this
  have D := H.isWeierstrassDivisorAt' (I := I)
  have hd := D.isWeierstrassDivisionAt_div_mod a
  refine ⟨D.mod a, ?_, D.div a, sub_eq_iff_eq_add.mpr hd.eq_mul_add⟩
  have hlt := hd.degree_lt
  rw [order_map_toNat_eq_natDegree_of_isDistinguishedAt H hI] at hlt
  rwa [Polynomial.degree_eq_natDegree (Polynomial.Monic.ne_zero H.monic)]

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in

theorem _root_.GlobalTheory.NB.LT.poly_dvd_of_dvd {I : Ideal R} [IsAdicComplete I R] {p : Polynomial R}
    (H : p.IsDistinguishedAt I) {r : Polynomial R} (h : (p : R⟦X⟧) ∣ (r : R⟦X⟧)) : p ∣ r := by
  by_cases hI : I = ⊤
  · have := subsingleton_of_isHausdorff_whole_ideal (I := I) hI
    rw [Subsingleton.elim r 0]
    exact dvd_zero p
  have hm := H.monic
  obtain ⟨h, hh⟩ := h
  have D := H.isWeierstrassDivisorAt' (I := I)
  have hdeg : (r %ₘ p).degree < ((map (Ideal.Quotient.mk I)) (p : R⟦X⟧)).order.toNat := by
    rw [order_map_toNat_eq_natDegree_of_isDistinguishedAt H hI]
    by_cases hs : Nontrivial R
    · exact (Polynomial.degree_modByMonic_lt r hm).trans_le Polynomial.degree_le_natDegree
    · rw [not_nontrivial_iff_subsingleton] at hs
      rw [Subsingleton.elim (r %ₘ p) 0]
      simp
  have hmul : (p : R⟦X⟧) * (h - ((r /ₘ p : Polynomial R) : R⟦X⟧)) = ((r %ₘ p : Polynomial R) : R⟦X⟧) := by
    have e := Polynomial.modByMonic_add_div r p
    have e' : ((r %ₘ p : Polynomial R) : R⟦X⟧) + (p : R⟦X⟧) * ((r /ₘ p : Polynomial R) : R⟦X⟧)
        = (r : R⟦X⟧) := by
      rw [← Polynomial.coe_mul, ← Polynomial.coe_add, e]
    rw [mul_sub, ← hh, ← e']
    ring
  have := (D.eq_zero_of_mul_eq hdeg hmul).2
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hm).mp this

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
theorem _root_.GlobalTheory.NB.LT.algHom_coe {B : Type} [CommRing B] [Algebra R B] (σ : R⟦X⟧ →ₐ[R] B) (r : Polynomial R) :
    σ (r : R⟦X⟧) = Polynomial.aeval (σ X) r := by
  have e : σ.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (σ X) :=
    Polynomial.algHom_ext (by simp)
  simpa using DFunLike.congr_fun e r

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
private lemma X_pow_dvd_sub_aeval_trunc (ρ : R⟦X⟧ →ₐ[R] R⟦X⟧) (hρ : X ∣ ρ X) (n : ℕ)
    (f : R⟦X⟧) : X ^ n ∣ ρ f - Polynomial.aeval (ρ X) (trunc n f) := by
  obtain ⟨g, hg⟩ : X ^ n ∣ f - (trunc n f : R⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [coeff_trunc, hm]
  have e : ρ f - Polynomial.aeval (ρ X) (trunc n f) = ρ (X ^ n) * ρ g := by
    rw [← _root_.GlobalTheory.NB.LT.algHom_coe ρ, ← map_sub, hg, map_mul]
  rw [e, map_pow]
  exact (pow_dvd_pow_of_dvd hρ n).mul_right _

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in

theorem _root_.GlobalTheory.NB.LT.algHom_ext_X (σ τ : R⟦X⟧ →ₐ[R] R⟦X⟧) (h : σ X = τ X) (hX : X ∣ σ X) : σ = τ := by
  refine AlgHom.ext fun f => PowerSeries.ext fun m => ?_
  have h1 := X_pow_dvd_sub_aeval_trunc σ hX (m + 1) f
  have h2 := X_pow_dvd_sub_aeval_trunc τ (h ▸ hX) (m + 1) f
  rw [h] at h1
  have h3 := dvd_sub h1 h2
  rw [sub_sub_sub_cancel_right] at h3
  have := (X_pow_dvd_iff.mp h3) m (Nat.lt_succ_self m)
  rwa [map_sub, sub_eq_zero] at this

end GlobalTheory.NB.LT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrMatrixProjPreimage
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem dvr_matrix_proj_preimage (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] (n : Type) [Fintype n] [DecidableEq n]
    (S : Submodule K (n → K)) :
    ∃ P : Matrix n n O, (∀ v : n → O, (fun i => algebraMap O K ((P.mulVec v) i)) ∈ S) ∧
      ∀ u : n → O, (fun i => algebraMap O K (u i)) ∈ S → P.mulVec u = u := by
  classical
  let f : (n → O) →ₗ[O] (n → K) := LinearMap.compLeft (Algebra.linearMap O K) n
  let U : Submodule O (n → O) := (S.restrictScalars O).comap f
  have hmem : ∀ v : n → O, v ∈ U ↔ (fun i => algebraMap O K (v i)) ∈ S := fun v => Iff.rfl
  have htf : NoZeroSMulDivisors O ((n → O) ⧸ U) := by
    constructor
    intro c x hcx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U x
    by_cases hc : c = 0
    · left; exact hc
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcx
    rw [Submodule.Quotient.mk_eq_zero]
    rw [hmem] at hcx ⊢
    have e : (fun i => algebraMap O K ((c • v) i)) = algebraMap O K c • (fun i => algebraMap O K (v i)) := by
      funext i; simp [Algebra.smul_def]
    rw [e] at hcx
    have hc' : algebraMap O K c ≠ 0 := by
      intro h; exact hc ((IsFractionRing.injective O K) (by rw [h, map_zero]))
    have := S.smul_mem (algebraMap O K c)⁻¹ hcx
    rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
  haveI : Module.Free O ((n → O) ⧸ U) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Projective O ((n → O) ⧸ U) := Module.Projective.of_free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property U.mkQ LinearMap.id (Submodule.mkQ_surjective U)
  let π : (n → O) →ₗ[O] (n → O) := LinearMap.id - s ∘ₗ U.mkQ
  have hπU : ∀ v, π v ∈ U := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hs (U.mkQ v)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.Quotient.mk_sub]
    rw [← Submodule.mkQ_apply U (s _), this, Submodule.mkQ_apply, sub_self]
  have hπfix : ∀ u ∈ U, π u = u := by
    intro u hu
    have h0 : U.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hu
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero, sub_zero]
  refine ⟨LinearMap.toMatrix' π, ?_, ?_⟩
  · intro v
    rw [LinearMap.toMatrix'_mulVec]
    exact hπU v
  · intro u hu
    rw [LinearMap.toMatrix'_mulVec]
    exact hπfix u hu

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvectorMemOfSumMem
section
namespace GlobalTheory.EigenvectorOfSum

theorem eigenvector_mem_of_sum_mem {L Y I α : Type} [Field L] [AddCommGroup Y] [Module L Y]
    (T : I → Y →ₗ[L] Y) (χ : α → I → L) (hχ : Function.Injective χ) (U : Submodule L Y)
    (hU : ∀ (g : I), ∀ y ∈ U, (T g : Y → Y) y ∈ U) (S : Finset α) (y : α → Y)
    (hy : ∀ a ∈ S, ∀ (g : I), (T g : Y → Y) (y a) = χ a g • y a)
    (hs : ∑ a ∈ S, y a ∈ U) : ∀ a ∈ S, y a ∈ U := by
  classical
  induction S using Finset.strongInduction generalizing y with
  | H S ih =>
  intro a ha
  by_cases hex : ∃ b ∈ S, b ≠ a
  · obtain ⟨b, hb, hba⟩ := hex
    obtain ⟨g, hg⟩ : ∃ g, χ a g ≠ χ b g := by
      by_contra hcon
      simp only [ne_eq, not_exists, not_not] at hcon
      exact hba (hχ (funext hcon)).symm
    set y' : α → Y := fun c => (χ c g - χ b g) • y c with hyq
    have hy' : ∀ c ∈ S.erase b, ∀ g', (T g' : Y → Y) (y' c) = χ c g' • y' c := by
      intro c hc g'
      rw [hyq, map_smul, hy c (Finset.mem_of_mem_erase hc) g', smul_comm]
    have hs' : ∑ c ∈ S.erase b, y' c ∈ U := by
      have h1 : (T g : Y → Y) (∑ c ∈ S, y c) - χ b g • ∑ c ∈ S, y c ∈ U :=
        U.sub_mem (hU g _ hs) (U.smul_mem _ hs)
      have h2 : (T g : Y → Y) (∑ c ∈ S, y c) - χ b g • ∑ c ∈ S, y c = ∑ c ∈ S.erase b, y' c := by
        rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_erase_add _ _ hb]
        have hb0 : (T g : Y → Y) (y b) - χ b g • y b = 0 := by rw [hy b hb g, sub_self]
        rw [hb0, add_zero]
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [hyq]
        dsimp only
        rw [sub_smul, hy c (Finset.mem_of_mem_erase hc) g]
      rwa [h2] at h1
    have hmem := ih (S.erase b) (Finset.erase_ssubset hb) y' hy' hs' a
      (Finset.mem_erase.2 ⟨hba.symm, ha⟩)
    have hne : χ a g - χ b g ≠ 0 := sub_ne_zero.2 hg
    have h3 := U.smul_mem (χ a g - χ b g)⁻¹ hmem
    rwa [hyq, smul_smul, inv_mul_cancel₀ hne, one_smul] at h3
  · simp only [ne_eq, not_exists, not_and, not_not] at hex
    have hS : S = {a} := Finset.eq_singleton_iff_unique_mem.2 ⟨ha, hex⟩
    subst hS
    simpa using hs

end GlobalTheory.EigenvectorOfSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfNodupSumMultisetOfEq
section
namespace GlobalTheory

theorem eq_of_nodup_sum_multiset_of_eq (ι : Type) [Fintype ι] [DecidableEq ι]
    (B : ι → Multiset ℂ) (h : (∑ i, B i).Nodup) (i j : ι) (hi : B i ≠ 0) (hij : B i = B j) :
    i = j := by
  by_contra hne
  have hle : B i + B j ≤ ∑ k, B k := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hnd : (B i + B j).Nodup := Multiset.nodup_of_le hle h
  rw [← hij] at hnd
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hi
  exact Multiset.disjoint_left.1 (Multiset.nodup_add.1 hnd).2.2 ha ha

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfPowEqOneOfCharpoly
section
open Polynomial

namespace GlobalTheory.FinOrd

theorem eq_one_of_pow_eq_one_of_charpoly (K : Type) [Field K] [CharZero K] (N : ℕ)
    (M : Matrix (Fin N) (Fin N) K) (h : ∃ m : ℕ, 0 < m ∧ M ^ m = 1)
    (hc : M.charpoly = (X - 1) ^ N) : M = 1 := by
  obtain ⟨m, hm, hM⟩ := h
  have hpr : Prime (X - 1 : K[X]) := by simpa using prime_X_sub_C (1 : K)

  have hsep : (X ^ m - 1 : K[X]).Separable := by
    simpa using separable_X_pow_sub_C (1 : K) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero
  have h1 : minpoly K M ∣ X ^ m - 1 := minpoly.dvd_iff.2 (by simp [hM])

  have h2 : minpoly K M ∣ (X - 1) ^ N := by
    rw [← hc]; exact minpoly.dvd_iff.2 (Matrix.aeval_self_charpoly M)
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hpr N).1 h2

  have hsi : ((X - 1 : K[X]) ^ i).Separable := hsep.of_dvd (hi.symm.dvd.trans h1)
  have hle : minpoly K M ∣ X - 1 := by
    rcases hsi.of_pow' with hu | ⟨-, rfl⟩ | rfl
    · exact absurd hu hpr.not_unit
    · simpa using hi.dvd
    · exact hi.dvd.trans (by simp)
  have h0 : Polynomial.aeval M (X - 1 : K[X]) = 0 := minpoly.dvd_iff.1 hle
  simpa [sub_eq_zero] using h0

end GlobalTheory.FinOrd
end

