import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalCoefficientElementarySymm
section
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.SphPar

theorem dualLab_splitLab_getD (n k : ℕ) (i : ℕ) :
    (dualLab (splitLab n k)).getD i 0 = if i < k then 1 else 0 := by
  have h : dualLab (splitLab n k) = List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0 := by
    simp [dualLab, splitLab]
  rw [h]
  split_ifs with hi
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl

theorem diagonal_dualLab_splitLab {L : Type} [Field L] (n k : ℕ) (ϖ : L) :
    Matrix.diagonal (fun i : Fin n => ϖ ^ (dualLab (splitLab n k)).getD i 0) = diagJ n ϖ k := by
  unfold diagJ
  congr 1
  funext i
  rw [dualLab_splitLab_getD]
  split_ifs <;> simp

theorem exists_isUnifV (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    ∃ ϖ : P.adicCompletion E, IsUnifV E P ϖ := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  refine ⟨(π : P.adicCompletion E), ?_⟩
  unfold IsUnifV
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  rfl

theorem Tj_eq_of_isUnifV (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n k : ℕ)
    {ϖ ϖ' : P.adicCompletion E} (h : IsUnifV E P ϖ) (h' : IsUnifV E P ϖ') :
    Tj ℂ n (Ov E P) ϖ' k = Tj ℂ n (Ov E P) ϖ k := by
  unfold IsUnifV at h h'
  have hv0 : Valued.v ϖ ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  have hv0' : Valued.v ϖ' ≠ 0 := by rw [h']; exact WithZero.coe_ne_zero
  have h0 : ϖ ≠ 0 := fun e => hv0 (by rw [e, map_zero])
  have h0' : ϖ' ≠ 0 := fun e => hv0' (by rw [e, map_zero])
  have hu : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, h', ← h, div_self hv0]
  have e : ϖ' = ϖ' / ϖ * ϖ := (div_mul_cancel₀ _ h0).symm
  rw [e]
  refine Final.TjIndep _ _ _ _ _ _ _ ?_ ?_ (div_ne_zero h0' h0)
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu.le
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hu, inv_one])

theorem divInd_dualLab_splitLab (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n k : ℕ)
    {ϖ : P.adicCompletion E} (h : IsUnifV E P ϖ) :
    divInd (n := n) (Ov E P) (dualLab (splitLab n k)) = Tj ℂ n (Ov E P) ϖ k := by
  funext g
  by_cases hg : HasDiv (Ov E P) (dualLab (splitLab n k)) g
  · obtain ⟨ϖ', h', hab⟩ := id hg
    rw [diagonal_dualLab_splitLab] at hab
    rw [← Tj_eq_of_isUnifV E P n k h h', divInd, Tj, Set.indicator_of_mem (by exact hg),
      Set.indicator_of_mem (by exact hab)]
  · rw [divInd, Tj, Set.indicator_of_notMem (by exact hg), Set.indicator_of_notMem]
    intro hab
    refine hg ⟨ϖ, h, ?_⟩
    rw [diagonal_dualLab_splitLab]
    exact hab

theorem parGL_dualLab_splitLab (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) (k : ℕ) (hs : ParGL P n lab c s) (hk : k ≤ n)
    (hl : lab (dualLab (splitLab n k))) :
    c (dualLab (splitLab n k)) = (qV E P : ℂ) ^ (((k : ℂ) * ((n : ℂ) - k)) / 2) * s.esymm k := by
  obtain ⟨hcard, h0, hpar⟩ := hs
  obtain ⟨α, hα⟩ : ∃ α : Fin n → ℂ, Finset.univ.val.map α = s := by
    induction s using Quotient.inductionOn with
    | h l =>
      have hl' : l.length = n := by simpa using hcard
      subst hl'
      refine ⟨l.get, ?_⟩
      rw [Fin.univ_val_map, List.ofFn_get]
      rfl
  have hne : ∀ i, α i ≠ 0 := fun i e => h0 (by
    rw [← hα]; exact Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, e⟩)
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExists E P n α hne
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV E P
  have hO : ϖ ∈ Ov E P := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by
    unfold IsUnifV at hϖ
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    omega)
  have h2 := hpar α hα φ hφ _ hl
  rw [divInd_dualLab_splitLab E P n k hϖ, Final.SatakeTj E P n ϖ hO hϖ α hne φ hφ k hk, hα] at h2
  simpa [h1] using h2.symm

end GlobalTheory.SphPar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalFunctionDualLabel
section
noncomputable section

open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.InvTranspose

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

def flipM (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := A.transpose.submatrix Fin.rev Fin.rev

theorem flipM_apply (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) : flipM A i j = A j.rev i.rev := rfl

theorem flipM_mul (A B : Matrix (Fin n) (Fin n) R) : flipM (A * B) = flipM B * flipM A := by
  unfold flipM
  rw [Matrix.transpose_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ (Fin.revPerm : Fin n ≃ Fin n) _).symm

theorem flipM_one : flipM (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  simp [flipM_apply, Matrix.one_apply, eq_comm]

theorem flipM_flipM (A : Matrix (Fin n) (Fin n) R) : flipM (flipM A) = A := by
  ext i j
  simp [flipM_apply]

theorem flipM_diagonal (a : Fin n → R) : flipM (Matrix.diagonal a) = Matrix.diagonal (fun i => a i.rev) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [flipM_apply]
  · have h' : j.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
    simp [flipM_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h']

def theta : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨flipM ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R), flipM (g : Matrix (Fin n) (Fin n) R),
    by rw [← flipM_mul, Units.mul_inv, flipM_one], by rw [← flipM_mul, Units.inv_mul, flipM_one]⟩
  map_one' := by
    apply Units.ext
    simp [flipM_one]
  map_mul' g h := by
    apply Units.ext
    simp only [mul_inv_rev, Units.val_mul, flipM_mul]

theorem coe_theta (g : GL (Fin n) R) :
    (theta g : Matrix (Fin n) (Fin n) R) = flipM ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := rfl

theorem theta_theta (g : GL (Fin n) R) : theta (theta g) = g := by
  apply Units.ext
  rw [coe_theta]
  exact flipM_flipM _

end Ring

section Field

variable {L : Type} [Field L] {n : ℕ}

theorem theta_mem {O : Subring L} {g : GL (Fin n) L} (hg : g ∈ GLint (Fin n) O) : theta g ∈ GLint (Fin n) O := by
  obtain ⟨k, rfl⟩ := hg
  refine ⟨theta k, ?_⟩
  apply Units.ext
  rw [coe_theta, ← map_inv]
  rfl

theorem theta_upper {b : GL (Fin n) L} (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((theta b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  intro i j hij
  rw [coe_theta, flipM_apply]
  exact Formalism.UG.P.spherical_upper_inv b hb (Fin.rev_lt_rev.2 hij)

theorem theta_diag {b : GL (Fin n) L} (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id) (i : Fin n) :
    ((theta b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * (b : Matrix (Fin n) (Fin n) L) i.rev i.rev = 1 := by
  rw [coe_theta, flipM_apply, ← Formalism.UG.P.spherical_diag_mul _ _ (Formalism.UG.P.spherical_upper_inv b hb) hb,
    Units.inv_mul, Matrix.one_apply_eq]

theorem getD_dualLab' (d : List ℤ) (hd : d.length = n) (i : Fin n) :
    (dualLab d).getD i.1 0 = -(d.getD i.rev.1 0) := by
  subst hd
  have h1 : i.1 < (dualLab d).length := by simp only [dualLab, List.length_reverse, List.length_map]; exact i.2
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.rev.2]
  simp only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]
  congr 2
  omega

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem hasDiv_theta {O : Subring L} {d : List ℤ} (hd : d.length = n) {g : GL (Fin n) L} (h : HasDiv O d g) :
    HasDiv O (dualLab d) (theta g) := by
  obtain ⟨ϖ, hϖ, a, ha, b, hb, e⟩ := h
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  let D : GL (Fin n) L := ⟨Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0),
    Matrix.diagonal (fun i : Fin n => ϖ ^ (-(d.getD i 0))),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i
       rw [← zpow_add₀ h0, add_neg_cancel, zpow_zero],
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i
       rw [← zpow_add₀ h0, neg_add_cancel, zpow_zero]⟩
  have hg : g = a * D * b := Units.ext e
  refine ⟨ϖ, hϖ, theta a, theta_mem ha, theta b, theta_mem hb, ?_⟩
  rw [hg, map_mul, map_mul, Units.val_mul, Units.val_mul]
  congr 2
  rw [coe_theta]
  change flipM (Matrix.diagonal (fun i : Fin n => ϖ ^ (-(d.getD i 0)))) = _
  rw [flipM_diagonal]
  congr 1
  funext i
  rw [getD_dualLab' d hd]

theorem divInd_theta (O : Subring L) {d : List ℤ} (hd : d.length = n) (g : GL (Fin n) L) :
    divInd O (dualLab d) g = divInd O d (theta g) := by
  have hdd : dualLab (dualLab d) = d := by simp [dualLab, List.map_reverse]
  have : HasDiv O (dualLab d) g ↔ HasDiv O d (theta g) := by
    constructor
    · intro h
      have := hasDiv_theta (by simpa [dualLab] using hd) h
      rwa [hdd] at this
    · intro h
      have := hasDiv_theta hd h
      rwa [theta_theta] at this
  unfold divInd
  by_cases h : HasDiv O d (theta g)
  · rw [Set.indicator_of_mem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_mem (s := {g | HasDiv O (dualLab d) g}) (this.2 h)]
    rfl
  · rw [Set.indicator_of_notMem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_notMem (s := {g | HasDiv O (dualLab d) g}) (fun h' => h (this.1 h'))]

theorem hasDiv_mul_right {O : Subring L} {d : List ℤ} {g k : GL (Fin n) L} (hk : k ∈ GLint (Fin n) O) (h : HasDiv O d g) :
    HasDiv O d (g * k) := by
  obtain ⟨ϖ, hϖ, a, ha, b, hb, e⟩ := h
  refine ⟨ϖ, hϖ, a, ha, b * k, mul_mem hb hk, ?_⟩
  rw [Units.val_mul, Units.val_mul, e]
  simp only [Matrix.mul_assoc]

theorem divInd_mul_right (O : Subring L) (d : List ℤ) (g k : GL (Fin n) L) (hk : k ∈ GLint (Fin n) O) :
    divInd O d (g * k) = divInd O d g := by
  unfold divInd
  by_cases h : HasDiv O d g
  · rw [Set.indicator_of_mem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_mem (s := {g | HasDiv O d g}) (hasDiv_mul_right hk h)]
    rfl
  · rw [Set.indicator_of_notMem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_notMem (s := {g | HasDiv O d g})]
    intro h'
    have := hasDiv_mul_right (inv_mem hk) h'
    rw [mul_inv_cancel_right] at this
    exact h this

end Field

theorem finsum_out_involution {G : Type} [Group G] (K : Subgroup G) (t : G →* G) (ht : ∀ g, t (t g) = g)
    (hK : ∀ k ∈ K, t k ∈ K) (F : G → ℂ) (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) :
    ∑ᶠ x : G ⧸ K, F (t x.out) = ∑ᶠ x : G ⧸ K, F x.out := by
  have hF' : ∀ g : G, F (QuotientGroup.mk (s := K) g).out = F g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, hF _ _ k.2]
  let m : G ⧸ K → G ⧸ K := fun x => QuotientGroup.mk (t x.out)
  have hm : Function.Involutive m := fun x => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (t x.out)
    simp only [m]
    rw [hk, map_mul, ht, QuotientGroup.mk_mul_of_mem _ (hK _ k.2), QuotientGroup.out_eq']
  rw [← finsum_comp_equiv (hm.toPerm m) (f := fun x : G ⧸ K => F x.out)]
  exact finsum_congr fun x => (hF' _).symm

section Global

variable (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}

theorem ordV_of_mul_eq_one {x y : P.adicCompletion E} (h : x * y = 1) : ordV E P x = -ordV E P y := by
  have hx : x ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hy : y ≠ 0 := right_ne_zero_of_mul_eq_one h
  have h1 := Formalism.UG.P.spherical_ordV_mul E P x y hx hy
  have h2 := Formalism.UG.P.spherical_ordV_unit E P 1 1 (one_mem _) (one_mem _) (mul_one 1)
  rw [h, h2] at h1
  omega

theorem chiDelta_theta (α : Fin n → ℂ) {b : GL (Fin n) (P.adicCompletion E)}
    (hb : (b : Matrix (Fin n) (Fin n) (P.adicCompletion E)).BlockTriangular id) :
    chiDelta E P α (theta b) = chiDelta E P (fun i => (α i.rev)⁻¹) b := by
  unfold chiDelta
  rw [← Equiv.prod_comp (Fin.revPerm : Fin n ≃ Fin n) (fun i : Fin n => (α i.rev)⁻¹ ^ _ * _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ordV_of_mul_eq_one E P (theta_diag hb i)]
  simp only [Fin.revPerm_apply, Fin.rev_rev, inv_zpow']
  congr 2
  have : ((i.rev : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℂ) := by
    rw [Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [this]
  push_cast
  ring

end Global

theorem exists_spherical_dual : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (α : Fin n → ℂ) (φ : GL (Fin n) (P.adicCompletion E) → ℂ), (∀ i, α i ≠ 0) → IsSpherical E P α φ → ∃ φ' : GL (Fin n) (P.adicCompletion E) → ℂ, IsSpherical E P (fun i => (α i.rev)⁻¹) φ' ∧ φ' 1 = φ 1 ∧ ∀ d : List ℤ, d.length = n → hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) (dualLab d)) φ' 1 = hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) d) φ 1 := by
  intro E _ _ P n α φ _ hφ
  refine ⟨fun g => φ (theta g), ?_, by simp, ?_⟩
  · intro b g k hb hk
    have hb' := (Formalism.UG.P.spherical_upper_iff b).1 hb
    simp only [map_mul]
    rw [hφ _ _ _ ((Formalism.UG.P.spherical_upper_iff _).2 (theta_upper hb')) (theta_mem hk), chiDelta_theta E P α hb']
  · intro d hd
    have h1 : ((1 : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)).BlockTriangular id :=
      Matrix.blockTriangular_one
    have hr : ∀ g, ∀ k ∈ GLint (Fin n) (Ov E P), φ (g * k) = φ g := fun g k hk => by
      have := hφ 1 g k ((Formalism.UG.P.spherical_upper_iff _).2 h1) hk
      rwa [one_mul, Formalism.UG.P.spherical_chiDelta_int E P α 1 h1 (one_mem _), one_mul] at this
    unfold hAct
    simp only [one_mul, divInd_theta _ hd]
    exact finsum_out_involution _ theta theta_theta (fun k => theta_mem)
      (fun g => divInd (Ov E P) d g • φ g) (fun g k hk => by rw [divInd_mul_right _ _ _ _ hk, hr g k hk])

end GlobalTheory.InvTranspose

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitDetOfSplitDetermines
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev IsDedekindDomain NumberField Polynomial
open scoped Pointwise

namespace GlobalTheory.PartsCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section Poly

variable {K L : Type} [Field K] [Field L]

theorem dualPoly_map (φ : K →+* L) (s : K) (p : K[X]) : (dualPoly s p).map φ = dualPoly (φ s) (p.map φ) := by
  ext i
  rw [coeff_map, coeff_dualPoly, coeff_dualPoly, natDegree_map, leadingCoeff_map, coeff_map]
  simp

theorem dualPoly_comp {a : K} (ha : a ≠ 0) (s : K) (p : K[X]) :
    dualPoly s (p.comp (C a⁻¹ * X)) = dualPoly (s * a) p := by
  have hd : (p.comp (C a⁻¹ * X)).natDegree = p.natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero ha), mul_one]
  have hl : (p.comp (C a⁻¹ * X)).leadingCoeff = p.leadingCoeff * a⁻¹ ^ p.natDegree := by
    rw [leadingCoeff, hd, comp_C_mul_X_coeff, leadingCoeff]
  ext i
  by_cases hi : i ≤ p.natDegree
  · rw [coeff_dualPoly_of_le _ _ (hd ▸ hi), coeff_dualPoly_of_le _ _ hi, hl, hd, comp_C_mul_X_coeff]
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi
    rw [hj, Nat.add_sub_cancel_left, pow_add, mul_pow]
    have h1 : a⁻¹ ^ i * a ^ i = 1 := by rw [← mul_pow, inv_mul_cancel₀ ha, one_pow]
    have h2 : a⁻¹ ^ j ≠ 0 := pow_ne_zero _ (inv_ne_zero ha)
    have h3 : (a⁻¹ ^ i)⁻¹ = a ^ i := by rw [inv_pow, inv_inv]
    rw [mul_inv, mul_inv, h3]
    field_simp
  · have hi' := not_le.1 hi
    rw [coeff_dualPoly_of_lt _ _ (hd ▸ hi'), coeff_dualPoly_of_lt _ _ hi']

theorem coeff_heckePolyOf (n q : ℕ) (a : ℕ → K) (i : ℕ) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff i =
      if i ≤ n then (-1) ^ i * (q : K) ^ (i * (i - 1) / 2) * a i else 0 := by
  unfold Formalism.L2.Col.heckePolyOf
  simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range,
    Nat.lt_succ_iff]

theorem tri_add (i j : ℕ) : (i + j) * (i + j - 1) / 2 + i * (i - 1) / 2 = j * (j - 1) / 2 + (i + j - 1) * i := by
  have h : ∀ n : ℕ, 2 * (n * (n - 1) / 2) + n = n * n := by
    intro n
    rw [Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
    cases n with
    | zero => rfl
    | succ m => simp; ring
  have h1 := h (i + j)
  have h2 := h i
  have h3 := h j
  have h4 : (i + j - 1) * i + i = (i + j) * i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have : m + 1 + j - 1 = m + j := by omega
      rw [this]; ring
  nlinarith

theorem heckePolyOf_dual {n q : ℕ} (hq : (q : K) ≠ 0) {a b : ℕ → K} (h0 : a 0 = 1)
    (h : ∀ k ≤ n, a n * b k = a (n - k)) :
    Formalism.L2.Col.heckePolyOf n q b = dualPoly ((q : K) ^ (n - 1)) (Formalism.L2.Col.heckePolyOf n q a) := by
  have hn : a n ≠ 0 := by
    have := h n le_rfl
    rw [Nat.sub_self, h0] at this
    exact left_ne_zero_of_mul_eq_one this
  have htop : (Formalism.L2.Col.heckePolyOf n q a).coeff n ≠ 0 := by
    rw [coeff_heckePolyOf, if_pos le_rfl]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) (pow_ne_zero _ hq)) hn
  have hd : (Formalism.L2.Col.heckePolyOf n q a).natDegree = n :=
    le_antisymm (natDegree_le_iff_coeff_eq_zero.2 fun i hi => by rw [coeff_heckePolyOf, if_neg (not_le.2 hi)])
      (le_natDegree_of_ne_zero htop)
  ext i
  by_cases hi : i ≤ n
  · rw [coeff_dualPoly_of_le _ _ (by rw [hd]; exact hi), leadingCoeff, hd, eq_inv_mul_iff_mul_eq₀ htop,
      coeff_heckePolyOf, coeff_heckePolyOf, coeff_heckePolyOf, if_pos le_rfl, if_pos hi, if_pos (Nat.sub_le _ _),
      ← h i hi]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Nat.add_sub_cancel_left, ← pow_mul]
    have e := congrArg (fun m => (q : K) ^ m) (tri_add i j)
    simp only [pow_add] at e
    have e2 : ((-1 : K) ^ i) * (-1) ^ i = 1 := by rw [← mul_pow]; simp
    rw [pow_add]
    linear_combination ((-1 : K) ^ j * a (i + j) * b i * ((-1) ^ i * (-1) ^ i)) * e +
      ((-1 : K) ^ j * a (i + j) * b i * ((q : K) ^ (j * (j - 1) / 2) * (q : K) ^ ((i + j - 1) * i))) * e2
  · rw [coeff_dualPoly_of_lt _ _ (by rw [hd]; exact not_le.1 hi), coeff_heckePolyOf, if_neg hi]

end Poly

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem mem_ok_iff {R : RealDat D A Ks} {F : Face D A} (h : R.Char F) (P : Pl0) :
    P ∈ A.ok A.μ0 ↔ Formalism.IndefR.Bridge.SplitOff (R.pl P) (R.Sb : Set (Pl D.host.E)) := by
  obtain ⟨_, _, _, ht⟩ := h.fam.tie
  have hQ : R.Q A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
    refine (h.lev.Q_ram A.μ0 PP).2 (Or.inl hP) ?_
    rw [h.lev.xi_base]
    intro x _
    rfl
  rw [ht.ok, hQ, Finset.coe_empty, Set.union_empty]

theorem q_ne_zero {s : ℕ} (h : A.fam.Ok s) {P : Pl0} (hP : P ∈ A.ok A.μ0) : A.q P ≠ 0 :=
  ((h.what₂ A.μ0).q_pos ⟨P, hP⟩).ne'

theorem polW_eq (p : Pl0 → D.what₂.LL[X]) {P : Pl0} (hq : A.q P ≠ 0) :
    RealDat.polW (A := A) p P = dualPoly ((A.q P : ℂ) ^ (D.R.r - 1)) (RealDat.polE (A := A) p P) := by
  unfold RealDat.polW RealDat.polE
  rw [dualPoly_comp (pow_ne_zero _ (Nat.cast_ne_zero.2 hq)), dualPoly_map, map_pow, map_natCast, pow_add]

theorem polE_coeff_zero {R : RealDat D A Ks} {F : Face D A} (h : R.Char F) (p : A.fam.base.Ix) (P : Pl0) :
    (RealDat.polE (A := A) p.1 P).coeff 0 = 1 := by
  unfold RealDat.polE
  rw [comp_C_mul_X_coeff, coeff_map, A.const_of (fun P => (h.fam.degR A.μ0 P).1) p.1 p.2 P]
  simp

def DualPol (R : RealDat D A Ks) (c : PolarisedDualSystem.Sys D) : Prop :=
  ∀ P ∈ A.ok A.μ0, (PolarisedDualSystem.polAt R (PolarisedDualSystem.dualSys c) P).coeff 0 = 1 ∧
    PolarisedDualSystem.polAt R c P = dualPoly ((A.q P : ℂ) ^ (D.R.r - 1)) (PolarisedDualSystem.polAt R (PolarisedDualSystem.dualSys c) P)

def CentralRel (R : RealDat D A Ks) (c : PolarisedDualSystem.Sys D) : Prop :=
  ∀ P ∈ A.ok A.μ0, c (R.pl P) (splitLab D.R.r 0) = 1 ∧ ∀ k ≤ D.R.r,
    c (R.pl P) (splitLab D.R.r D.R.r) * c (R.pl P) (dualLab (splitLab D.R.r k)) = c (R.pl P) (splitLab D.R.r (D.R.r - k))

section Label

variable {R : RealDat D A Ks} {F : Face D A} {s : ℕ} (hs : A.fam.Ok s) (h : R.Char F)
include hs h

variable {X : DivX D} {E : EigIdx D X} {sys : E.Pi → PolarisedDualSystem.Sys D} {jE : D.what₂.EE →ₗ[ℂ] R.HE.H}
  {jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H}

end Label

def SameIndex (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ c, PolarisedDualSystem.Occ R c ↔ ∃ i, BaseSetLabels.OccW R (PolarisedDualSystem.badF R) i (BaseSetLabels.conjugateBaseLevel R F) c

section Ties

variable {R : RealDat D A Ks} {F : Face D A} {X : DivX D} {E : EigIdx D X} {sys : E.Pi → PolarisedDualSystem.Sys D}
  {jE : D.what₂.EE →ₗ[ℂ] R.HE.H} {jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H}

end Ties

def PartsStAt (R : RealDat D A Ks) (F : Face D A) {X : DivX D} (E : EigIdx D X) : Prop :=
  ∀ (s : ℕ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (eig : E.Pi → BaseSetLabels.Eig D) (jE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    (jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H),
    A.fam.Ok s → R.Char F → BaseSetLabels.Tied R F S E eig jE jW → BaseSetLabels.PartsAt R E eig jE jW

def Bridge (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ s : ℕ, A.fam.Ok s → R.Char F → SameIndex R F ∧ ∀ c, PolarisedDualSystem.Occ R c → CentralRel R c

def SplitDetRow (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ s : ℕ, A.fam.Ok s → R.Char F → PolarisedDualSystem.SplitDet R

def TieExists (R : RealDat D A Ks) (F : Face D A) {X : DivX D} (E : EigIdx D X) : Prop :=
  ∃ S eig jE jW, BaseSetLabels.Tied R F S E eig jE jW

section Main

variable {R : RealDat D A Ks} {F : Face D A} {X : DivX D} {E : EigIdx D X}

end Main

end GlobalTheory.PartsCompare

end
end

