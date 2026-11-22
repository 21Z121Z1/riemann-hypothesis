import ReciprocityTheory.DualLattices.Bundle0024
import ReciprocityTheory.DualLattices.Bundle0025
import ReciprocityTheory.DualLattices.Bundle0011
import ReciprocityTheory.DualLattices.FormalChartAtZero

-- bundled from ReciprocityTheory.DualLattices.AinfTower
section
noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

namespace Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

abbrev R0 (ε : PreTilt O p) := A p O ⧸ span {xi p O ε ^ 2}

abbrev Rn (n : ℕ) := O ⧸ span {(p : O) ^ (n + 1)}

abbrev R'n (ε : PreTilt O p) (n : ℕ) := R0 p O ε ⧸ span {(p : R0 p O ε) ^ (n + 1)}

lemma hpRn (n : ℕ) : (p : Rn p O n) ^ (n + 1) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})) p, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

lemma hpR' (ε : PreTilt O p) (n : ℕ) : (p : R'n p O ε n) ^ (n + 1) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (span {(p : R0 p O ε) ^ (n + 1)})) p, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

lemma Rn_local (hv : v.Integers O) (n : ℕ) : IsLocalRing (Rn p O n) := by
  haveI := O_local O hv
  haveI : Nontrivial (Rn p O n) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 : (1 : O) ∈ span {(p : O) ^ (n + 1)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]; exact h.symm
    rw [Ideal.mem_span_singleton'] at h1
    obtain ⟨a, ha⟩ := h1
    exact (Fact.out : ¬IsUnit (p : O))
      ((isUnit_pow_iff (Nat.succ_ne_zero n)).1 (IsUnit.of_mul_eq_one_right a ha))
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

lemma one_add_unit {S : Type} [CommRing S] (a b : S) (hb : b * b = 0) : IsUnit (1 + a * b) := by
  exact IsUnit.of_mul_eq_one (1 - a * b) (by linear_combination (-a ^ 2) * hb)

variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

def thetaBar : R0 p O ε →+* O :=
  Ideal.Quotient.lift _ (fontaineTheta O p) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, theta_xi p O hv ε hε, zero_pow two_ne_zero, mul_zero])

def algO : Algebra (R0 p O ε) O := (thetaBar p O hv ε hε).toAlgebra

def algRn (n : ℕ) : Algebra (R0 p O ε) (Rn p O n) :=
  ((Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})).comp (thetaBar p O hv ε hε)).toAlgebra

def piRing (n : ℕ) : R'n p O ε n →+* Rn p O n :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})).comp
    (thetaBar p O hv ε hε)) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast, hpRn, mul_zero])

lemma piRing_mk (n : ℕ) (a : A p O) :
    piRing p O hv ε hε n (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a)) =
      Ideal.Quotient.mk _ (fontaineTheta O p a) := rfl

lemma piRing_surj (n : ℕ) : Function.Surjective (piRing p O hv ε hε n) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, rfl⟩ := theta_surj p O hv x
  exact ⟨_, piRing_mk p O hv ε hε n a⟩

def xiR (n : ℕ) : R'n p O ε n :=
  Ideal.Quotient.mk (span {(p : R0 p O ε) ^ (n + 1)}) (Ideal.Quotient.mk (span {xi p O ε ^ 2}) (xi p O ε))

lemma ker_pi (n : ℕ) : RingHom.ker (piRing p O hv ε hε n) = span {xiR p O ε n} := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [piRing_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
    obtain ⟨o, ho⟩ := hx
    obtain ⟨b, rfl⟩ := theta_surj p O hv o
    have hk : a - b * (p : A p O) ^ (n + 1) ∈ RingHom.ker (fontaineTheta O p) := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_pow, map_natCast, ho, sub_self]
    rw [ker_theta p O hv ε hε, Ideal.mem_span_singleton'] at hk
    obtain ⟨c, hc⟩ := hk
    have ha : a = c * xi p O ε + b * (p : A p O) ^ (n + 1) := by rw [hc]; ring
    rw [Ideal.mem_span_singleton']
    refine ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk _ c), ?_⟩
    rw [ha]
    simp only [xiR, map_add, map_mul, map_pow, map_natCast, hpR', mul_zero, add_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, xiR, piRing_mk,
      theta_xi p O hv ε hε, map_zero]

lemma xi_sq' (n : ℕ) : xiR p O ε n * xiR p O ε n = 0 := by
  unfold xiR
  rw [← map_mul, ← map_mul]
  have h : (Ideal.Quotient.mk (span {xi p O ε ^ 2})) (xi p O ε * xi p O ε) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨1, by ring⟩)
  rw [h, map_zero]

lemma R'n_local (n : ℕ) : IsLocalRing (R'n p O ε n) := by
  haveI := Rn_local p O hv n
  haveI : Nontrivial (R'n p O ε n) := (piRing p O hv ε hε n).domain_nontrivial
  have key : ∀ a : R'n p O ε n, IsUnit (piRing p O hv ε hε n a) → IsUnit a := by
    intro a ha
    obtain ⟨u, hu⟩ := ha.exists_right_inv
    obtain ⟨u', rfl⟩ := piRing_surj p O hv ε hε n u
    have hk : a * u' - 1 ∈ RingHom.ker (piRing p O hv ε hε n) := by
      rw [RingHom.mem_ker, map_sub, map_mul, hu, map_one, sub_self]
    rw [ker_pi, Ideal.mem_span_singleton'] at hk
    obtain ⟨k, hk⟩ := hk
    have h1 : a * u' = 1 + k * xiR p O ε n := by rw [hk]; ring
    have h2 := one_add_unit k (xiR p O ε n) (xi_sq' p O hv ε hε n)
    rw [← h1] at h2
    exact isUnit_of_mul_isUnit_left h2
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self (fun a => ?_)
  have h : piRing p O hv ε hε n a + piRing p O hv ε hε n (1 - a) = 1 := by
    rw [← map_add, add_sub_cancel, map_one]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h with h | h
  · exact Or.inl (key a h)
  · exact Or.inr (key _ h)

lemma ann' (n : ℕ) (a : R'n p O ε n) (ha : a * xiR p O ε n = 0) :
    a ∈ span {xiR p O ε n} := by
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  have hp0 : (p : O) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h'
    exact hp.out.ne_zero (by exact_mod_cast h')
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  unfold xiR at ha
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at ha
  obtain ⟨d0, hd0⟩ := ha
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d0
  rw [← map_natCast (Ideal.Quotient.mk (span {xi p O ε ^ 2})) p, ← map_pow, ← map_mul,
    Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hd0
  obtain ⟨c, hc⟩ := hd0
  have h1 : fontaineTheta O p d * (p : O) ^ (n + 1) = 0 := by
    have h' := congrArg (fontaineTheta O p) hc
    simp only [map_mul, map_sub, map_pow, map_natCast, theta_xi p O hv ε hε] at h'
    linear_combination -h'
  have h2 : fontaineTheta O p d = 0 := (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ hp0)
  have h3 : d ∈ RingHom.ker (fontaineTheta O p) := h2
  rw [ker_theta p O hv ε hε, Ideal.mem_span_singleton'] at h3
  obtain ⟨e0, rfl⟩ := h3
  have h4 : (y - (e0 * (p : A p O) ^ (n + 1) - c * xi p O ε)) * xi p O ε = 0 := by
    linear_combination hc
  have h5 := xi_nzd p O hv ε hε _ h4
  rw [sub_eq_zero] at h5
  rw [h5, Ideal.mem_span_singleton']
  refine ⟨-(Ideal.Quotient.mk _ (Ideal.Quotient.mk _ c)), ?_⟩
  simp only [xiR, map_sub, map_mul, map_pow, map_natCast, hpR', mul_zero, zero_sub, neg_mul]

def zv (n : ℕ) : R'n p O ε n :=
  Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (teichmuller p (root p O ε (n + 1))))

def nuR (n : ℕ) : R'n p O ε n := Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (nu p O ε))

lemma zv_pow (n : ℕ) :
    zv p O ε n ^ p ^ (n + 1) = 1 + nuR p O ε n * xiR p O ε n := by
  unfold zv nuR xiR
  rw [← map_pow, ← map_pow, ← map_pow, root_pow, teich_eps p O hv ε hε, map_add, map_add, map_one,
    map_one, map_mul, map_mul]

lemma zv_unit (n : ℕ) : IsUnit (zv p O ε n) := by
  have hne : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  refine (isUnit_pow_iff hne).1 ?_
  rw [zv_pow p O hv ε hε n]
  exact one_add_unit _ _ (xi_sq' p O hv ε hε n)

def zetaV (n : ℕ) : O := fontaineTheta O p (teichmuller p (root p O ε (n + 1)))

lemma zeta_unit (n : ℕ) : IsUnit (zetaV p O ε n) := by
  have hne : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have h : zetaV p O ε n ^ p ^ (n + 1) = 1 := by
    unfold zetaV
    rw [← map_pow, ← map_pow, root_pow, teich_eps p O hv ε hε, map_add, map_one, map_mul,
      theta_xi p O hv ε hε, mul_zero, add_zero]
  refine IsUnit.of_mul_eq_one (zetaV p O ε n ^ (p ^ (n + 1) - 1)) ?_
  rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hne), h]

def LO : LAlg (R0 p O ε) := { carrier := O, alg := algO p O hv ε hε, loc := O_local O hv }

def LR (n : ℕ) : LAlg (R0 p O ε) :=
  { carrier := Rn p O n, alg := algRn p O hv ε hε n, loc := Rn_local p O hv n }

def LR' (n : ℕ) : LAlg (R0 p O ε) := { carrier := R'n p O ε n, loc := R'n_local p O hv ε hε n }

lemma q_surj (n : ℕ) : Function.Surjective (Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})) := by
  exact Ideal.Quotient.mk_surjective

def ainfTower : ATower (R0 p O ε) p where
  O := LO p O hv ε hε
  R' n := LR' p O hv ε hε n
  R n := LR p O hv ε hε n
  π n := ⟨{ toRingHom := piRing p O hv ε hε n, commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (piRing_surj p O hv ε hε n)⟩
  q n := ⟨{ toRingHom := Ideal.Quotient.mk (span {(p : O) ^ (n + 1)}), commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (q_surj p O hv ε hε n)⟩
  ξ n := xiR p O ε n
  surj n := piRing_surj p O hv ε hε n
  ker_eq n := ker_pi p O hv ε hε n
  ξ_sq n := xi_sq' p O hv ε hε n
  ann n a ha := ann' p O hv ε hε n a ha
  char n := by rw [Nat.cast_pow]; exact hpR' p O ε n
  sep a ha := sepO p O a fun n =>
    (Ideal.Quotient.eq_zero_iff_mem (I := span {(p : O) ^ (n + 1)})).1 (ha n)
  c := fontaineTheta O p (nu p O ε)
  cp n := nuR p O ε n
  cp_spec n := rfl
  zh n := (zv_unit p O hv ε hε n).unit
  zh_pow n := by rw [IsUnit.unit_spec]; exact zv_pow p O hv ε hε n
  ζ n := (zeta_unit p O hv ε hε n).unit
  ζ_spec n := by rw [IsUnit.unit_spec, IsUnit.unit_spec]; rfl

theorem ainfTower_c_ne_zero : (ainfTower p O hv ε hε).c ≠ 0 := by
  exact theta_nu p O hv ε hε

theorem ainfTower_isDomain : IsDomain ((ainfTower p O hv ε hε).O : Type) := by
  show IsDomain O
  exact Function.Injective.isDomain (algebraMap O C) hv.hom_inj

theorem thmA_ainf (B : BX (R0 p O ε)) (hB1 : PairingPropertiesStatement B) (hB3 : TangentPairingStatement B) :
    ThmAFullStatement B (ainfTower p O hv ε hε) := by
  exact thmAFull B hB1 hB3 _

end Ainf

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.ColengthSqMulLeProd
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

variable {C : Type} [Field C] {v : Valuation C NNReal}

def blkLat {n s : ℕ} (Ls : Fin n → Lat v (Fin s)) : Lat v (Fin n × Fin s) where
  B := Matrix.of fun x y => if x.1 = y.1 then (Ls x.1).B x.2 y.2 else 0
  det_ne := by
    have h : (Matrix.of fun x y : Fin n × Fin s => if x.1 = y.1 then (Ls x.1).B x.2 y.2 else 0) =
        (Matrix.blockDiagonal fun τ => (Ls τ).B).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
      ext x y
      simp [Matrix.blockDiagonal_apply, eq_comm]
    rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (Ls τ).det_ne

lemma blkLat_det {n s : ℕ} (Ls : Fin n → Lat v (Fin s)) :
    (blkLat Ls).B.det = ∏ τ, (Ls τ).B.det := by
  have h : (blkLat Ls).B =
      (Matrix.blockDiagonal fun τ => (Ls τ).B).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext x y
    simp [blkLat, Matrix.blockDiagonal_apply, eq_comm]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]

lemma blkLat_pts {n s : ℕ} (Ls : Fin n → Lat v (Fin s)) : (blkLat Ls).pts = sumPts Ls := by
  have hmv : ∀ c : Fin n × Fin s → C, (blkLat Ls).B *ᵥ c =
      fun y => ((Ls y.1).B *ᵥ fun j => c (y.1, j)) y.2 := by
    intro c
    ext ⟨τ, i⟩
    simp only [blkLat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type, ite_mul,
      zero_mul]
    rw [Finset.sum_eq_single τ]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  ext w
  simp only [ReciprocityTheory.PGsh.Lat.pts, sumPts, Set.mem_setOf_eq, hmv]
  constructor
  · rintro ⟨c, hc, rfl⟩ τ
    exact ⟨fun j => c (τ, j), fun j => hc (τ, j), rfl⟩
  · intro hw
    choose c hc hce using hw
    refine ⟨fun y => c y.1 y.2, fun y => hc y.1 y.2, ?_⟩
    funext y
    exact congrFun (hce y.1) y.2

lemma colen_blk {n s : ℕ} (L's Ls : Fin n → Lat v (Fin s)) :
    colen (blkLat L's) (blkLat Ls) = ∏ τ, colen (L's τ) (Ls τ) := by
  simp only [ReciprocityTheory.PGsh.colen, blkLat_det, map_prod]
  rw [Finset.prod_div_distrib]

theorem colength_sq_mul_le_prod (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type)
    [CommRing R] [Algebra R C] (hv : v.Integers R) (hnt : ∃ c : C, 0 < v c ∧ v c < 1)
    (n : ℕ) (a : Fin n → C) (hinj : Function.Injective a) (hint : ∀ τ, v (a τ) ≤ 1)
    (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C) (F : Lat v (Fin n × Fin h))
    (M M' : Lat v (Fin n × Fin s)) (Mτ M'τ : Fin n → Lat v (Fin s)) (hF : F.B = freeMat a h)
    (hA : ∀ τ, Function.Surjective (A τ).mulVec)
    (hM' : M'.pts = (fun w : Fin n × Fin h → C => fun y : Fin n × Fin s =>
        ∑ l, A y.1 y.2 l * w (y.1, l)) '' F.pts)
    (hMst : IsLaStable a M) (hMτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ)
    (hM'τ : ∀ τ, (M'τ τ).pts = projPts M'.pts τ) :
    colen M' M ^ 2 * v (discr a) ^ h ≤ (∏ τ, colen (M'τ τ) (Mτ τ)) ^ 2 * v (discr a) ^ s := by
  have hdet : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι), v L.B.det ≠ 0 :=
    fun L => (map_ne_zero v).2 L.det_ne
  set S : Lat v (Fin n × Fin s) := blkLat Mτ
  set S' : Lat v (Fin n × Fin s) := blkLat M'τ
  have h2 := valuation_pairwiseDifferenceProduct_pow_le_colength_sq C v n a s M S Mτ hMst hMτ (blkLat_pts Mτ)
  have h3 := colength_sq_mul_le a hinj hint s h A F M' S' M'τ hF hM' hM'τ (blkLat_pts M'τ)
  have hP : colen S' S = ∏ τ, colen (M'τ τ) (Mτ τ) := colen_blk M'τ Mτ
  have hid : colen M' M * colen M S = colen M' S' * colen S' S := by
    simp only [ReciprocityTheory.PGsh.colen]
    rw [div_mul_div_cancel₀ (hdet M), div_mul_div_cancel₀ (hdet S')]
  have hc : 0 < colen M S ^ 2 := by
    have : colen M S ≠ 0 := div_ne_zero (hdet M) (hdet S)
    positivity
  rw [← hP]
  refine le_of_mul_le_mul_right ?_ hc
  calc colen M' M ^ 2 * v (discr a) ^ h * colen M S ^ 2
      = colen M' S' ^ 2 * v (discr a) ^ h * colen S' S ^ 2 := by
        rw [show colen M' M ^ 2 * v (discr a) ^ h * colen M S ^ 2 =
          (colen M' M * colen M S) ^ 2 * v (discr a) ^ h by ring, hid]; ring
    _ ≤ v (discr a) ^ (2 * s) * colen S' S ^ 2 := by gcongr
    _ = colen S' S ^ 2 * v (discr a) ^ s * v (discr a) ^ s := by ring
    _ ≤ colen S' S ^ 2 * v (discr a) ^ s * colen M S ^ 2 := by gcongr

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.DualPairInh
section
noncomputable section

open Polynomial

namespace ReciprocityTheory.PGsh

namespace DualNum

variable {R₀ : Type} [CommRing R₀] (R : LAlg R₀)

abbrev DN := (R : Type)[X] ⧸ Ideal.span {(X : (R : Type)[X]) ^ 2}

def ev : DN R →+* (R : Type) :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom 0) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp)

lemma ev_mk (f : (R : Type)[X]) : ev R (Ideal.Quotient.mk _ f) = f.eval 0 := rfl

lemma ev_surj : Function.Surjective (ev R) := fun r => ⟨Ideal.Quotient.mk _ (C r), by rw [ev_mk, eval_C]⟩

def eta : DN R := Ideal.Quotient.mk _ X

lemma eta_sq : eta R * eta R = 0 := by
  unfold eta
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_two]
  exact Ideal.mem_span_singleton_self _

lemma ker_ev : RingHom.ker (ev R) = Ideal.span {eta R} := by
  apply le_antisymm
  · intro y hy
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker, ev_mk] at hy
    have hX : (X : (R : Type)[X]) ∣ f := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
      exact hy
    obtain ⟨g, rfl⟩ := hX
    rw [map_mul]
    exact Ideal.mem_span_singleton.2 (dvd_mul_right (eta R) _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show ev R (eta R) = 0
    rw [eta, ev_mk, eval_X]

lemma isLocal : IsLocalRing (DN R) := by
  have hnt : Nontrivial (DN R) := (ev R).domain_nontrivial
  have hunit : ∀ y : DN R, IsUnit (ev R y) → IsUnit y := by
    intro y hy
    obtain ⟨u, hu⟩ : ∃ u : DN R, u = Ideal.Quotient.mk _ (C (ev R y)) := ⟨_, rfl⟩
    have hev : ev R u = ev R y := by rw [hu, ev_mk, eval_C]
    have hk : y - u ∈ RingHom.ker (ev R) := by rw [RingHom.mem_ker, map_sub, hev, sub_self]
    rw [ker_ev, Ideal.mem_span_singleton] at hk
    obtain ⟨c, hc⟩ := hk
    have hn : IsNilpotent (y - u) := ⟨2, by rw [hc, mul_pow, pow_two (eta R), eta_sq, zero_mul]⟩
    have hu' : IsUnit u := by
      have e : u = ((Ideal.Quotient.mk _).comp Polynomial.C) (ev R y) := hu
      rw [e]
      exact hy.map _
    have h := hn.isUnit_add_left_of_commute hu' (Commute.all _ _)
    rwa [add_sub_cancel] at h
  exact IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    (IsLocalRing.isUnit_or_isUnit_one_sub_self (ev R a)).imp (hunit a)
      fun h => hunit (1 - a) (by rwa [map_sub, map_one])

lemma ev_algebraMap (r : (R : Type)) : ev R (algebraMap (R : Type) (DN R) r) = r := by
  rw [← Ideal.Quotient.mk_algebraMap, ev_mk]
  simp

def evAlg : DN R →ₐ[R₀] (R : Type) :=
  { ev R with
    commutes' := fun r => by
      show ev R (algebraMap R₀ (DN R) r) = _
      rw [← Ideal.Quotient.mk_algebraMap, ev_mk, Polynomial.algebraMap_apply, eval_C] }

def D : LAlg R₀ := { carrier := DN R, loc := isLocal R }

def dualPair : DualPair R where
  D := D R
  π := ⟨evAlg R, TowerExample.isLocalHom_of_surj _ (ev_surj R)⟩
  σ := ⟨IsScalarTower.toAlgHom R₀ (R : Type) (DN R),
    ⟨fun r hr => by
      have h := hr.map (ev R)
      have e : ev R ((IsScalarTower.toAlgHom R₀ (R : Type) (DN R) : (R : Type) →+* DN R) r) = r :=
        ev_algebraMap R r
      convert h using 1
      exact e.symm⟩⟩
  η := eta R
  sect r := ev_algebraMap R r
  η_sq := eta_sq R
  ker_eq := ker_ev R
  free r h := by
    change algebraMap (R : Type) (DN R) r * eta R = 0 at h
    rw [← Ideal.Quotient.mk_algebraMap, eta, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, X_pow_dvd_iff] at h
    have h1 := h 1 (by norm_num)
    simpa [Polynomial.algebraMap_apply] using h1

end DualNum

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.TowerZeroSurjective
section
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]

structure Dat (p : ℕ) [Fact p.Prime] (g : ℕ) (B : BX R₀) (Tw : ATowerL R₀ p) (Dt : DualTower Tw)
    [Algebra ℤ_[p] (Tw.O : Type)] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe)
    (cp : (Tw.O : Type)) where
  K : LAlg R₀
  ρO : LHom Tw.O K
  ch : FormalChartAtZero B K g
  wd : WData Tw K

  ρO_eq : wd.ρ1.comp (Tw.q 0) = ρO
  sm : SM B K wd.W wd.ρW
  fin : FIN B Tw.O p
  A : OAct B Tw.O p Oe
  H : HodgeTateData p g (Tw.O : Type) Oe σ cp
  L : Link B Tw Dt H ch.gb A

  tower_zero_surjective : Function.Surjective (Tw.q 0).1

  tower_zero_ker : RingHom.ker (Tw.q 0).1 = Ideal.span {((p : ℕ) : (Tw.O : Type))}

  zeta0 : p = 2 → ((Tw.ζ 0 : (Tw.O : Type)ˣ) : (Tw.O : Type)) = -1

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

namespace Dat

variable (D : Dat p g B Tw Dt Oe σ cp)

lemma pt_p (t : Nb p g) : p • ptOf B D.L.τ t = 0 := by
  have h0 : ∀ j, p • D.L.τ j 0 = 0 := fun j => by simpa using D.L.τ_tors j 0
  simp only [ptOf, Finset.smul_sum]
  exact Finset.sum_eq_zero fun j _ => by rw [smul_comm, h0, smul_zero]

def ptIdx (t : Nb p g) : D.fin.ι :=
  Classical.choose (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t))

def ptMap (t : Nb p g) : LHom (D.fin.AAx (D.ptIdx t)) Tw.O :=
  Classical.choose (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))

def evAll (C : Type) [Field C] [Algebra (Tw.O : Type) C] (F : ∀ i, (D.fin.AAx i : Type)) :
    Nb p g → C :=
  fun t => algebraMap (Tw.O : Type) C ((D.ptMap t).1 (F (D.ptIdx t)))

def evImg (C : Type) [Field C] [Algebra (Tw.O : Type) C] : Submodule (Tw.O : Type) (Nb p g → C) :=
  Submodule.span (Tw.O : Type) (Set.range (D.evAll C))

end Dat

end ReciprocityTheory.PGsh.Be2
end
end

