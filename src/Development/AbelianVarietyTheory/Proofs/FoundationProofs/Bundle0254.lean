import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLattice
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NormSum.MovedTheta

open Matrix GlobalTheory.NormSum.AdLattice

variable {D : D7} {N N' : ℕ}

def mv (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) (AE D) :=
  ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
    (g : Matrix (Fin N) (Fin N) (AE D))

theorem mv_zero (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) : mv g g' 0 = 0 := by
  unfold mv
  rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]

theorem mv_add (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (z + w) = mv g g' z + mv g g' w := by
  unfold mv
  rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

theorem mv_smul (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (e : D.host.E)
    (z : Matrix (Fin N') (Fin N) D.host.E) : mv g g' (e • z) = inc D e • mv g g' z := by
  unfold mv
  have : (e • z).map (inc D) = inc D e • z.map (inc D) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem inc_int (o : 𝓞 D.host.E) : inc D (o : D.host.E) ∈ OhE D :=
  (incl_mem_iff (F := ℚ) (o : D.host.E)).2 ⟨o, rfl⟩

theorem mulVec_mem_of_span {R m n : Type} [CommRing R] [Fintype n] {S : Subring R} (M : Matrix m n R) (i : m)
    {T : Set (n → R)} (hT : ∀ u ∈ T, (M *ᵥ u) i ∈ S) {u : n → R} (hu : u ∈ Submodule.span S T) :
    (M *ᵥ u) i ∈ S := by
  induction hu using Submodule.span_induction with
  | mem u hu => exact hT u hu
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mulVec_add]; exact add_mem hu hv
  | smul s u _ hu =>
    have e : s • u = (s : R) • u := rfl
    rw [e, mulVec_smul]
    exact mul_mem s.2 hu

theorem mv_int_of_maps {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : ∀ x ∈ L, A.mulVec x ∈ L') (i : Fin N') (j : Fin N) : mv g g' A i j ∈ OhE D := by
  have hL : L = lat g := by
    ext x
    exact (h x).trans (mem_lat g x).symm
  have h1 := (lat_span g ((g : Matrix (Fin N) (Fin N) (AE D)) *ᵥ Pi.single j 1)).2 (by
    intro k
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _)
  have h3 := mulVec_mem_of_span
    (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * A.map (inc D)) i (by
      rintro _ ⟨x, hx, rfl⟩
      have h2 := (h' _).1 (hA x (hL ▸ hx)) i
      have e : (fun j => inc D ((A *ᵥ x) j)) = A.map (inc D) *ᵥ (fun j => inc D (x j)) := by
        ext k; rw [RingHom.map_mulVec]; rfl
      rw [e, mulVec_mulVec] at h2
      exact h2) h1
  rw [mulVec_mulVec, mulVec_single_one] at h3
  exact h3

theorem mv_int_of_hom {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D L L') (i : Fin N') (j : Fin N) : mv g g' A i j ∈ OhE D := by
  induction hA using Submodule.span_induction with
  | mem A hA => exact mv_int_of_maps h h' hA i j
  | zero => rw [mv_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mv_add]; exact add_mem hu hv
  | smul o u _ hu =>
    have e : o • u = (o : D.host.E) • u := rfl
    rw [e, mv_smul]
    exact mul_mem (inc_int o) hu

theorem mul_mem_IhE {cc : Ideal (𝓞 D.host.K)} {s y : AE D} (hs : s ∈ OhE D) (hy : y ∈ IhE D cc) :
    s * y ∈ IhE D cc := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, t, ht, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * t, mul_mem hs ht, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | neg u _ hu => rw [mul_neg]; exact neg_mem hu

theorem mv_mem_IhE {cc : Ideal (𝓞 D.host.K)} {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {c : 𝓞 D.host.K} (hc : c ∈ cc)
    {B : Matrix (Fin N') (Fin N) D.host.E} (hB : B ∈ YYl D L L') (i : Fin N') (j : Fin N) :
    mv g g' (((c : D.host.K) : D.host.E) • B) i j ∈ IhE D cc := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    rw [smul_smul, mv_smul]
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, _, mv_int_of_hom h h' hA i j, rfl⟩
  | zero => rw [smul_zero, mv_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [smul_add, mv_add]; exact add_mem hu hv
  | smul o u _ hu =>
    have e : o • u = (o : D.host.E) • u := rfl
    rw [e, smul_comm, mv_smul]
    exact mul_mem_IhE (inc_int o) hu

theorem pt_zero (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt, embV, tor0]

theorem pt_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + w) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w := by
  funext τ i j
  simp [pt, embV, tor0, mul_add]

theorem pt_neg (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (-z) = -pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp [pt, embV, tor0]

theorem mv_neg (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (-z) = -mv g g' z := by
  rw [← neg_one_smul D.host.E z, mv_smul, map_neg, map_one, neg_one_smul]

end GlobalTheory.NormSum.MovedTheta

open GlobalTheory.NormSum.MovedTheta in

theorem GlobalTheory.NormSum.exists_pt_of_mem_La_moved : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧ ∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc := by
  intro D hG cc δ _ N N' g g' L L' h h' x hx
  let P : VC D N N' → Prop := fun x => ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧
    ∀ i j, mv (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) z i j ∈ IhE D cc
  have h0 : P 0 := ⟨0, (pt_zero cc δ).symm, fun i j => by rw [mv_zero]; exact zero_mem _⟩
  have hadd : ∀ u v, P u → P v → P (u + v) := by
    rintro _ _ ⟨z, rfl, hz⟩ ⟨w, rfl, hw⟩
    exact ⟨z + w, (pt_add cc δ z w).symm, fun i j => by rw [mv_add]; exact add_mem (hz i j) (hw i j)⟩
  have hneg : ∀ u, P u → P (-u) := by
    rintro _ ⟨z, rfl, hz⟩
    exact ⟨-z, (pt_neg cc δ z).symm, fun i j => by rw [mv_neg]; exact neg_mem (hz i j)⟩
  show P x
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    change w ∈ lamOf D cc δ at hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, rfl⟩ := hw
      refine ⟨((c : D.host.K) : D.host.E) • A, ?_, mv_mem_IhE h h' hc hA⟩
      funext τ i j
      have e := hG.1 τ (c : D.host.K)
      simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      rw [e, mul_assoc]
    | zero => rw [zero_smul]; exact h0
    | add u v _ _ hu hv => rw [add_smul]; exact hadd _ _ hu hv
    | neg u _ hu => rw [neg_smul]; exact hneg _ hu
  | zero => exact h0
  | add u v _ _ hu hv => exact hadd _ _ hu hv
  | neg u _ hu => exact hneg _ hu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.InertSign

abbrev Lat (D : D7) (n : ℕ) : Type := Submodule (𝓞 D.host.E) (Fin n → D.host.E)

def hE (D : D7) {n : ℕ} (x y : Fin n → D.host.E) : D.host.E := ∑ i, x i * D.host.conj (y i)

def IntE (D : D7) (e : D.host.E) : Prop := e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def sgO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  MulSemiringAction.toRingHom (D.host.E ≃ₐ[ℚ] D.host.E) (𝓞 D.host.E) D.host.conj

theorem sgO_coe (D : D7) (a : 𝓞 D.host.E) : ((sgO D a : 𝓞 D.host.E) : D.host.E) = D.host.conj a := rfl

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  letI := D.host.cmStar
  rw [← AdLattice.star_eq_conj, ← AdLattice.star_eq_conj]
  exact star_star x

theorem sgO_sgO (D : D7) (a : 𝓞 D.host.E) : sgO D (sgO D a) = a :=
  Subtype.ext (conj_conj D a)

theorem embT_conj (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = (starRingEnd ℂ) (embT D τ x) := by
  letI := D.host.isCMField_hostE
  rw [← AdLattice.star_eq_conj]
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E (embT D τ) x

theorem conj_hE (D : D7) {n : ℕ} (x y : Fin n → D.host.E) : D.host.conj (hE D x y) = hE D y x := by
  simp only [hE, map_sum, map_mul, conj_conj, mul_comm]

theorem hE_add_left (D : D7) {n : ℕ} (x x' y : Fin n → D.host.E) : hE D (x + x') y = hE D x y + hE D x' y := by
  simp only [hE, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hE_add_right (D : D7) {n : ℕ} (x y y' : Fin n → D.host.E) : hE D x (y + y') = hE D x y + hE D x y' := by
  simp only [hE, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hE_smul_left (D : D7) {n : ℕ} (a : D.host.E) (x y : Fin n → D.host.E) : hE D (a • x) y = a * hE D x y := by
  simp only [hE, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hE_smul_right (D : D7) {n : ℕ} (a : D.host.E) (x y : Fin n → D.host.E) :
    hE D x (a • y) = D.host.conj a * hE D x y := by
  simp only [hE, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem IntE.conj {D : D7} {e : D.host.E} (h : IntE D e) : IntE D (D.host.conj e) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨sgO D a, rfl⟩

theorem sd_iff (D : D7) {n : ℕ} (L : Lat D n) : SD D L ↔
    L.FG ∧ Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤ ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IntE D (hE D y x) := by
  unfold SD IsSDLat
  simp only [stdH, AdLattice.star_eq_conj, IntE, hE, mul_comm]

def nbM (D : D7) {n : ℕ} (B : Lat D n) (x : Fin n → D.host.E) : Lat D n where
  carrier := {y | y ∈ B ∧ IntE D (hE D y x)}
  add_mem' := fun {a b} ha hb => ⟨B.add_mem ha.1 hb.1, by rw [hE_add_left]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨B.zero_mem, by simp only [hE, Pi.zero_apply, zero_mul, Finset.sum_const_zero]; exact zero_mem _⟩
  smul_mem' := fun c a ha => ⟨B.smul_mem c ha.1, by
    rw [← algebraMap_smul D.host.E c a, hE_smul_left]; exact mul_mem ⟨c, rfl⟩ ha.2⟩

theorem mem_nbM {D : D7} {n : ℕ} {B : Lat D n} {x y : Fin n → D.host.E} :
    y ∈ nbM D B x ↔ y ∈ B ∧ IntE D (hE D y x) := Iff.rfl

def nbr (D : D7) {n : ℕ} (B : Lat D n) (x : Fin n → D.host.E) : Lat D n :=
  nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {x}

def NbD (D : D7) {n : ℕ} (P : Ideal (𝓞 D.host.E)) (B : Lat D n) (x : Fin n → D.host.E) : Prop :=
  x ∉ B ∧ (∀ p ∈ P, p • x ∈ B) ∧ IntE D (hE D x x)

def Tri (D : D7) {n : ℕ} (P : Ideal (𝓞 D.host.E)) (A B C : Lat D n) : Prop :=
  SD D A ∧ SD D B ∧ SD D C ∧ ∃ (M : Lat D n) (b x : Fin n → D.host.E),
    A = M ⊔ Submodule.span (𝓞 D.host.E) {b + x} ∧ B = M ⊔ Submodule.span (𝓞 D.host.E) {b} ∧
    C = M ⊔ Submodule.span (𝓞 D.host.E) {x} ∧ (∀ p ∈ P, p • b ∈ M ∧ p • x ∈ M) ∧ ¬ IntE D (hE D b x)

def Bet (D : D7) {n : ℕ} (L₁ L₂ L₃ : Lat D n) : Prop := L₂ ≤ (L₁ ⊓ L₂) ⊔ (L₂ ⊓ L₃) ∧ L₁ ⊓ L₃ ≤ L₂

def cT (D : D7) {m n : ℕ} (s : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E :=
  (s.map D.host.conj).transpose

def SAt (D : D7) {n : ℕ} (q : ℕ) (s : Matrix (Fin n) (Fin n) D.host.E) (L L₁ : Lat D n) : Prop :=
  ∃ m : ℕ, Nat.Coprime m q ∧ (∀ v ∈ L, (m : D.host.E) • s.mulVec v ∈ L₁) ∧
    ∀ v ∈ L₁, (m : D.host.E) • (cT D s).mulVec v ∈ L

def Iid (D : D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {t | ∃ c ∈ cc, ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
    t = ((c : D.host.K) : D.host.E) * a}

def RL (D : D7) (cc : Ideal (𝓞 D.host.K)) {N N' : ℕ} (L : Lat D N) (L' : Lat D N') :
    Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
  Submodule.span (𝓞 D.host.E) {z | ∃ t ∈ Iid D cc, ∃ A ∈ homL D L L', z = t • A}

def bc (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * Complex.I *
    ((Real.sqrt D.host.d * (Hf D T x y).re + (Hf D T x y).im : ℝ) : ℂ))

theorem Hf_add_left (D : D7) (T : Tor D) {N N' : ℕ} (x x' y : VC D N N') :
    Hf D T (x + x') y = Hf D T x y + Hf D T x' y := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_add_right (D : D7) (T : Tor D) {N N' : ℕ} (x y y' : VC D N N') :
    Hf D T x (y + y') = Hf D T x y + Hf D T x y' := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]

theorem Hf_conj (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') :
    (starRingEnd ℂ) (Hf D T x y) = Hf D T y x := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

theorem bc_ne_zero (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : bc D T x y ≠ 0 := Complex.exp_ne_zero _

theorem bc_add_left (D : D7) (T : Tor D) {N N' : ℕ} (x x' y : VC D N N') :
    bc D T (x + x') y = bc D T x y * bc D T x' y := by
  rw [bc, bc, bc, ← Complex.exp_add, Hf_add_left, Complex.add_re, Complex.add_im]
  congr 1; push_cast; ring

theorem bc_add_right (D : D7) (T : Tor D) {N N' : ℕ} (x y y' : VC D N N') :
    bc D T x (y + y') = bc D T x y * bc D T x y' := by
  rw [bc, bc, bc, ← Complex.exp_add, Hf_add_right, Complex.add_re, Complex.add_im]
  congr 1; push_cast; ring

theorem bc_zero_left (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') : bc D T 0 y = 1 := by
  have h := bc_add_left D T 0 0 y
  rw [add_zero] at h
  exact (mul_eq_left₀ (bc_ne_zero D T 0 y)).1 h.symm

theorem bc_zero_right (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : bc D T x 0 = 1 := by
  have h := bc_add_right D T x 0 0
  rw [add_zero] at h
  exact (mul_eq_left₀ (bc_ne_zero D T x 0)).1 h.symm

theorem bc_comm (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') :
    bc D T x y = Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T x y).im : ℂ)) * bc D T y x := by
  rw [bc, bc, ← Complex.exp_add, ← Hf_conj D T x y, Complex.conj_re, Complex.conj_im]
  congr 1; push_cast; ring

theorem Wd_Wd (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (F : VC D N N' → ℂ) :
    Wd D T x (Wd D T y F) = bc D T x y • Wd D T (x + y) F := by
  funext z
  have hc := Hf_conj D T x y
  have hre : (Hf D T y x).re = (Hf D T x y).re := by rw [← hc, Complex.conj_re]
  have h2 : Hf D T y x = Hf D T x y - 2 * Complex.I * ((Hf D T x y).im : ℂ) := by
    rw [← hc]; apply Complex.ext <;> simp <;> ring
  simp only [Wd, U, wdPh, ee, bc, qH, Pi.smul_apply, smul_eq_mul, Hf_add_left, Hf_add_right, Complex.add_re, hre,
    add_assoc]
  rw [h2]
  have key : ∀ a b c d' e f g' : ℂ, ∀ v : ℂ, a + b + c + d' = e + f + g' →
      Complex.exp a * (Complex.exp b * (v * Complex.exp c) * Complex.exp d') =
        Complex.exp e * (Complex.exp f * (v * Complex.exp g')) := by
    intro a b c d' e f g' v h
    have := congrArg Complex.exp h
    simp only [Complex.exp_add] at this
    linear_combination v * this
  apply key
  push_cast; ring

theorem Wd_add (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (F G : VC D N N' → ℂ) :
    Wd D T x (F + G) = Wd D T x F + Wd D T x G := by
  funext z; simp only [Wd, U, Pi.add_apply]; ring

theorem Wd_smul (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (a : ℂ) (F : VC D N N' → ℂ) :
    Wd D T x (a • F) = a • Wd D T x F := by
  funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring

theorem Wd_zero (D : D7) (T : Tor D) {N N' : ℕ} (F : VC D N N' → ℂ) : Wd D T 0 F = F := by
  funext z; simp [Wd, U, wdPh, ee, qH, Hf]

def Nice (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) : Prop :=
  (∀ x ∈ A, ∀ F, Wd D T x F = fun z => al D T x * U D T x F z) ∧ (∀ x ∈ A, ∀ y ∈ A, bc D T x y = 1) ∧
    ∀ x, (∀ y ∈ A, bc D T x y = bc D T y x) → x ∈ A

theorem Nice.mem_ThSp {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')} (h : Nice D T A)
    (F : VC D N N' → ℂ) : F ∈ ThSp D T A ↔ Differentiable ℂ F ∧ ∀ x ∈ A, Wd D T x F = F := by
  refine and_congr_right fun _ => forall₂_congr fun x hx => ?_
  rw [h.1 x hx, funext_iff]

theorem Nice.Iop_eq {D : D7} {T : Tor D} {N N' : ℕ} (A : AddSubgroup (VC D N N')) {B : AddSubgroup (VC D N N')}
    (h : Nice D T B) (F : VC D N N' → ℂ) :
    Iop D T A B F = fun z => ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) *
      ∑ᶠ q : B ⧸ A.addSubgroupOf B, Wd D T ((Quotient.out q : B) : VC D N N') F z := by
  funext z
  simp only [Iop]
  congr 1
  exact finsum_congr fun q => by rw [h.1 _ (Quotient.out q : B).2]

def Trip (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ) : Prop :=
  Nice D T A₁ ∧ Nice D T A₂ ∧ Nice D T A₃ ∧ (A₁.addSubgroupOf A₂).index ≠ 0 ∧ (A₂.addSubgroupOf A₃).index ≠ 0 ∧
    (A₁.addSubgroupOf A₃).index ≠ 0 ∧ e ∈ ThSp D T A₁ ∧ e ≠ 0 ∧ μ ^ 8 = 1 ∧
    Iop D T A₂ A₃ (Iop D T A₁ A₂ e) = fun z => μ * Iop D T A₁ A₃ e z

def Dist {V : Type} [AddCommGroup V] (A₁ A₂ A₃ : AddSubgroup V) : Prop :=
  ∀ x ∈ A₂, ∀ y ∈ A₃, x + y ∈ A₁ → x ∈ (A₁ ⊓ A₂) ⊔ (A₂ ⊓ A₃)

def TriDat (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (P : Ideal (𝓞 D.host.E)) (r : ℕ) : Prop :=
  ∃ (X Y : Fin r → 𝓞 D.host.E →+ VC D N N') (φ : Fin r → 𝓞 D.host.E →+ ℂ),
    (∀ i j a a', Hf D T (Y i a') (X j a) = if i = j then φ i (a' * sgO D a) else 0) ∧
    (∀ i a, X i a ∈ A₂ ∧ Y i a ∈ A₃ ∧ X i a + Y i a ∈ A₁) ∧
    (∀ i, ∀ p ∈ P, X i p ∈ A₁ ⊓ A₃ ∧ Y i p ∈ A₁ ⊓ A₂) ∧
    (∀ z ∈ A₂, ∃ a : Fin r → 𝓞 D.host.E, z - ∑ i, X i (a i) ∈ A₁ ⊓ A₃) ∧
    (∀ z ∈ A₃, ∃ a : Fin r → 𝓞 D.host.E, z - ∑ i, Y i (a i) ∈ A₁ ⊓ A₂) ∧
    (∀ a : Fin r → 𝓞 D.host.E, ∑ i, X i (a i) ∈ A₁ → ∀ i, a i ∈ P) ∧
    (∀ a : Fin r → 𝓞 D.host.E, ∑ i, Y i (a i) ∈ A₂ → ∀ i, a i ∈ P)

end GlobalTheory.InertSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImConjMulEqIntMulArea
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TransInv

theorem im_conj_mul_ne_zero {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 := by
  intro h0
  rw [LinearIndependent.pair_iff] at h
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  have h1 := h w₂.im (-w₁.im) (by
    apply Complex.ext <;> simp <;> linarith)
  have h2 := h w₂.re (-w₁.re) (by
    apply Complex.ext <;> simp <;> linarith)
  have h3 := h 1 0 (by
    apply Complex.ext <;> simp <;> linarith [h1.2, h2.2])
  exact one_ne_zero h3.1

theorem im_conj_mul_mem {w₁ w₂ u v : ℂ} (hu : u ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ))
    (hv : v ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)) :
    ∃ k : ℤ, ((starRingEnd ℂ) u * v).im = k * ((starRingEnd ℂ) w₁ * w₂).im := by
  obtain ⟨a, b, rfl⟩ := AddSubgroup.mem_closure_pair.1 hu
  obtain ⟨c, d, rfl⟩ := AddSubgroup.mem_closure_pair.1 hv
  refine ⟨a * d - b * c, ?_⟩
  simp
  ring

theorem area_closure_pair {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    area (AddSubgroup.closure ({w₁, w₂} : Set ℂ)) = |((starRingEnd ℂ) w₁ * w₂).im| := by
  have h0 := im_conj_mul_ne_zero h
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨abs_pos.2 h0, w₁, AddSubgroup.subset_closure (by simp), w₂,
    AddSubgroup.subset_closure (by simp), rfl⟩, ?_⟩
  rintro a ⟨ha, u, hu, v, hv, rfl⟩
  obtain ⟨k, hk⟩ := im_conj_mul_mem hu hv
  rw [hk] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  rw [abs_mul]
  nlinarith [abs_nonneg ((starRingEnd ℂ) w₁ * w₂).im]

theorem im_conj_mul_eq_int_mul_area {Λ : AddSubgroup ℂ}
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    0 < area Λ ∧ ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ k : ℤ, ((starRingEnd ℂ) u * v).im = k * area Λ := by
  obtain ⟨w₁, w₂, h, rfl⟩ := hΛ
  rw [area_closure_pair h]
  refine ⟨abs_pos.2 (im_conj_mul_ne_zero h), fun u hu v hv => ?_⟩
  obtain ⟨k, hk⟩ := im_conj_mul_mem hu hv
  rcases abs_cases ((starRingEnd ℂ) w₁ * w₂).im with h1 | h1
  · exact ⟨k, by rw [hk, h1.1]⟩
  · exact ⟨-k, by rw [hk, h1.1]; push_cast; ring⟩

theorem translate_add_of_fixed {Λ : AddSubgroup ℂ} (hA : area Λ ≠ 0) (G : ℂ → ℂ) (x η : ℂ) (k : ℤ)
    (hη : ∀ z, U1 Λ η G z = G z) (hk : ((starRingEnd ℂ) η * x).im = 2 * k * area Λ) :
    U1 Λ (x + η) G = U1 Λ x G := by
  funext z
  have h := hη (z + x)
  have hA' : (area Λ : ℂ) ≠ 0 := by exact_mod_cast hA
  have hs := Complex.sub_conj ((starRingEnd ℂ) η * x)
  rw [hk, map_mul, Complex.conj_conj] at hs
  push_cast at hs
  unfold U1 at h ⊢
  rw [← h, mul_assoc (G (z + x + η)), ← Complex.exp_add, ← add_assoc]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  rw [map_add]
  field_simp
  linear_combination hs

theorem translate_sigma_star_period {Λ : AddSubgroup ℂ}
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂})
    (x ω : ℂ) (m : ℕ) (hx : (m : ℂ) * (x / 2) ∈ Λ) (hω : ω ∈ Λ) :
    U1 Λ (x + 2 * (m : ℂ) * ω) (sgStar Λ) = U1 Λ x (sgStar Λ) := by
  obtain ⟨hA, hint⟩ := im_conj_mul_eq_int_mul_area hΛ
  obtain ⟨k, hk⟩ := hint ω hω _ hx
  have hm : (m : ℂ) * ω ∈ Λ := by simpa using Λ.nsmul_mem hω m
  have h2 : 2 * (m : ℂ) * ω ∈ Λ := by
    have := Λ.add_mem hm hm
    convert this using 1
    ring
  have h3 : 2 * (m : ℂ) * ω / 2 ∈ Λ := by
    convert hm using 1
    ring
  refine translate_add_of_fixed hA.ne' _ x _ (2 * k) (fun z => ?_) ?_
  · rw [(GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.2.2 _ h2 z, if_pos h3, one_mul]
  · have e : (starRingEnd ℂ) (2 * (m : ℂ) * ω) * x =
        ((4 : ℝ) : ℂ) * ((starRingEnd ℂ) ω * ((m : ℂ) * (x / 2))) := by
      simp only [map_mul, map_ofNat, map_natCast]
      push_cast
      ring
    rw [e, Complex.im_ofReal_mul, hk]
    push_cast
    ring

theorem transInv_all : ∀ D : D7, transInv D := fun D cc δ hc x ω m _ hx hω =>
  translate_sigma_star_period (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc).1 x ω m hx hω

end GlobalTheory.TransInv
end

