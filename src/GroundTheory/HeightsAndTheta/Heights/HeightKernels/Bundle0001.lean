import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ExtendedDataRemainder
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open MvPolynomial

noncomputable section

abbrev RootPoly (f N : ℕ) : Type := MvPolynomial (Fin f × Fin N) ℚ

def alternant {R : Type*} [CommRing R] {m : ℕ} (e : Fin m → ℕ) (v : Fin m → R) : R :=
  (Matrix.of fun i j : Fin m => v i ^ e j).det

def staircase (m : ℕ) : Fin m → ℕ := fun j => m - 1 - (j : ℕ)

def blockRoots (f N : ℕ) (τ : Fin f) : Fin N → RootPoly f N := fun i => X (τ, i)

def antisymBlocks (f N : ℕ) (H : RootPoly f N) : RootPoly f N :=
  ∑ w : Fin f → Equiv.Perm (Fin N),
    (∏ τ, ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℚ) • rename (fun p => (p.1, w p.1 p.2)) H

def divDiff (f N : ℕ) (H : RootPoly f N) : RootPoly f N := by
  classical
  exact if h : ∃ P, antisymBlocks f N H = (∏ τ, alternant (staircase N) (blockRoots f N τ)) * P
    then h.choose else 0

def flagInt (f N : ℕ) (H : RootPoly f N) : ℚ := constantCoeff (divDiff f N H)

def blockPsum (f N : ℕ) (k : ℕ) (τ : Fin f) : RootPoly f N := ∑ i : Fin N, X (τ, i) ^ k

inductive SmallCase
  | last
  | first

def smallRoots (f r a : ℕ) : SmallCase → Fin f → Fin r → RootPoly f (r + a)
  | .last, τ, i => X (τ, ⟨a + i, by omega⟩)
  | .first, τ, i => -X (τ, ⟨i, by omega⟩)

def otherRoots (f r a : ℕ) : SmallCase → Fin f → Fin a → RootPoly f (r + a)
  | .last, τ, i => X (τ, ⟨i, by omega⟩)
  | .first, τ, i => X (τ, ⟨r + i, by omega⟩)

def smallMu (f r a : ℕ) (c : SmallCase) : RootPoly f (r + a) :=
  ∑ τ, ∑ i, smallRoots f r a c τ i

def fibClass (f r a : ℕ) (c : SmallCase) : RootPoly f (r + a) :=
  ∏ τ, alternant (staircase r) (smallRoots f r a c τ) * alternant (staircase a) (otherRoots f r a c τ)

def restPoly (f r a : ℕ) (c : SmallCase) : RootPoly f (r + a) :=
  smallMu f r a c ^ (f * (r * a) + 1) * fibClass f r a c

def restJ (f r a : ℕ) (c : SmallCase) : ℚ :=
  flagInt f (r + a) (smallMu f r a c ^ (f * (r * a)) * fibClass f r a c)

def IsPsumDecomposition (f N : ℕ) (F : RootPoly f N) (Q : ℕ → Fin f → RootPoly f N) : Prop :=
  F = ∑ k ∈ Finset.Icc 1 N, ∑ τ, blockPsum f N k τ * Q k τ

def termT (f N : ℕ) (Q : ℕ → Fin f → RootPoly f N) (k : ℕ) (τ : Fin f) (G : RootPoly f N) : ℚ :=
  k * flagInt f N (G * Q k τ)

def restAtPrime (f r a : ℕ) (c : SmallCase) (Q : ℕ → Fin f → RootPoly f (r + a))
    (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ) (p : ℕ) : ℝ :=
  Real.log p * ∑ τ, ∑ k ∈ Finset.Icc 2 (r + a), ∑' n' : ℕ,
    ((p : ℝ) ^ ((n' + 1) * k))⁻¹ *
      ((termT f (r + a) Q k τ
        (C (e p (n' + 1) τ k) * ∑ i, smallRoots f r a c (s p (n' + 1) τ) i ^ (k - 1)) : ℚ) : ℝ)

def S9.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f r a : ℕ) (c : SmallCase) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    (∃ Q, IsPsumDecomposition f (r + a) (restPoly f r a c) Q) ∧
    ∀ Q : ℕ → Fin f → RootPoly f (r + a), IsPsumDecomposition f (r + a) (restPoly f r a c) Q →
    ∀ (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ),
      (∀ p n' τ k, e p n' τ k = 1 ∨ e p n' τ k = -1) → ∀ S : Set ℕ,
      Summable (fun p : {p : ℕ // p ∈ S ∧ p.Prime ∧ B₀ < p} => |restAtPrime f r a c Q s e p|) ∧
      |∑' p : {p : ℕ // p ∈ S ∧ p.Prime ∧ B₀ < p}, restAtPrime f r a c Q s e p| ≤
        C * r * ((f * (r * a) + 1 : ℕ) : ℝ) * |(restJ f r a c : ℝ)|

def inhQ : ℕ → Fin 1 → RootPoly 1 (1 + 1) :=
  fun k _ => if k = 1 then C (2⁻¹ : ℚ) * (X (0, 1) - X (0, 0)) else if k = 2 then C (2⁻¹ : ℚ) else 0

theorem S9.hypotheses_inhabited :
    4 * ((1 : ℕ) : ℝ) * ((1 + 1 : ℕ) : ℝ) ^ 2 ≤ 16 ∧
      IsPsumDecomposition 1 (1 + 1) (restPoly 1 1 1 .last) inhQ ∧
      ∀ (p n' : ℕ) (τ : Fin 1) (k : ℕ), (fun _ _ _ _ => (1 : ℚ)) p n' τ k = 1 ∨
        (fun _ _ _ _ => (1 : ℚ)) p n' τ k = -1 := by
  refine ⟨by norm_num, ?_, fun _ _ _ _ => Or.inl rfl⟩
  have hI : Finset.Icc 1 (1 + 1) = ({1, 2} : Finset ℕ) := by decide
  simp only [IsPsumDecomposition, restPoly, smallMu, fibClass, alternant, smallRoots,
    otherRoots, hI, inhQ, blockPsum, Matrix.det_unique, Finset.univ_unique, Finset.sum_singleton,
    Finset.prod_singleton]
  rw [Finset.sum_pair (by norm_num)]
  simp [staircase, Fin.sum_univ_succ]
  have h2 : (C (2⁻¹ : ℚ) : RootPoly 1 (1 + 1)) * 2 = 1 := by
    rw [show (2 : RootPoly 1 (1 + 1)) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
  linear_combination (-X ((0 : Fin 1), (1 : Fin (1 + 1))) ^ 2) * h2

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.IsSiegelReducedCoordinates
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open Matrix MeasureTheory

noncomputable section

def qf {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (Y *ᵥ v)

def intVec {ι : Type*} (v : ι → ℤ) : ι → ℝ := fun i => (v i : ℝ)

def firstMinSq {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) : ℝ :=
  ⨅ v : {v : ι → ℤ // v ≠ 0}, qf G (intVec v.1)

def siegelGram {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ (Y⁻¹ * X) (X * Y⁻¹) (Y + X * Y⁻¹ * X)

def S1.Statement : Prop :=
  ∀ (g : ℕ) (hg : 0 < g) (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ),
    G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
    firstMinSq G ≤ 2 * g ∧
    ∃ M ∈ symplecticGroup (Fin g) ℤ,
      let G' := (M.map (Int.cast : ℤ → ℝ))ᵀ * G * M.map (Int.cast : ℤ → ℝ)
      G' (Sum.inl ⟨0, hg⟩) (Sum.inl ⟨0, hg⟩) = firstMinSq G ∧
      G'.toBlocks₁₁.det ≤ firstMinSq G * (2 * g) ^ (g - 1) ∧
      ∃ X Y : Matrix (Fin g) (Fin g) ℝ, X.IsSymm ∧ Y.PosDef ∧ G' = siegelGram X Y

def S2.Statement : Prop :=
  ∀ (g : ℕ) (hg : 0 < g) (Y : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → ∀ v : Fin g → ℝ,
    v ⟨0, hg⟩ ^ 2 / Y⁻¹ ⟨0, hg⟩ ⟨0, hg⟩ ≤ qf Y v

def S3.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) → ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => Real.exp (-(Real.pi / 2) * qf Y (intVec k + u))) ∧
      ∑' k : Fin g → ℤ, Real.exp (-(Real.pi / 2) * qf Y (intVec k + u)) ≤
        (C * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g

def tauOf {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℂ :=
  X.map (fun x : ℝ => (x : ℂ)) + Complex.I • Y.map (fun x : ℝ => (x : ℂ))

def cvec {g : ℕ} (v : Fin g → ℝ) : Fin g → ℂ := fun i => (v i : ℂ)

def thetaChar {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ) : ℂ :=
  ∑' k : Fin g → ℤ,
    Complex.exp (Real.pi * Complex.I *
        (cvec (intVec k + a) ⬝ᵥ (tauOf X Y *ᵥ cvec (intVec k + a))) +
      2 * Real.pi * Complex.I * (cvec (intVec k + a) ⬝ᵥ (z + cvec b)))

def thetaN {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (u₁ u₂ : Fin g → ℝ) : ℝ :=
  ‖thetaChar X Y a b (tauOf X Y *ᵥ cvec u₁ + cvec u₂)‖ * Real.exp (-Real.pi * qf Y u₁)

def thetaBeta {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) : ℝ :=
  ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ))

def distInt (x : ℝ) : ℝ := |x - round x|

def IsHalfIntegral {g : ℕ} (a : Fin g → ℝ) : Prop := ∀ i, ∃ m : ℤ, a i = m / 2

def IsSiegelReducedCoordinates {g : ℕ} (hg : 0 < g) (X Y : Matrix (Fin g) (Fin g) ℝ) : Prop :=
  Y⁻¹ ⟨0, hg⟩ ⟨0, hg⟩ = firstMinSq (siegelGram X Y) ∧
    (Y⁻¹).det ≤ firstMinSq (siegelGram X Y) * (2 * g) ^ (g - 1)

def errE (C : ℝ) (g : ℕ) (ρ : ℝ) : ℝ :=
  g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g)

def S4.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) (hg : 0 < g) (X Y : Matrix (Fin g) (Fin g) ℝ),
    X.IsSymm → Y.PosDef → IsSiegelReducedCoordinates hg X Y → ∀ a b : Fin g → ℝ,
      IsHalfIntegral a → IsHalfIntegral b →
      (∫ u in Set.Icc (0 : (Fin g → ℝ) × (Fin g → ℝ)) 1, thetaN X Y a b u.1 u.2 ^ 2) =
          thetaBeta Y ^ 2 ∧
      ∀ u₁ u₂ : Fin g → ℝ,
        thetaN X Y a b u₁ u₂ ≤ thetaBeta Y * Real.exp
          (-(Real.pi / (2 * Y⁻¹ ⟨0, hg⟩ ⟨0, hg⟩)) * distInt (u₁ ⟨0, hg⟩ + a ⟨0, hg⟩) ^ 2 +
            errE C g (Real.sqrt (Y⁻¹ ⟨0, hg⟩ ⟨0, hg⟩)))

def mean {σ : Type*} [Fintype σ] (f : σ → ℝ) : ℝ := (∑ s, f s) / Fintype.card σ

def S5.Statement : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) (σ : Type) [Fintype σ] [Nonempty σ] (ρ : σ → ℝ) (Φ : ℝ),
      (∀ s, 0 < ρ s ∧ ρ s ≤ Real.sqrt (2 * g)) → 0 ≤ Φ →
      mean (fun s => Real.pi / 96 * (ρ s)⁻¹ ^ 2 - errE C₀ g (ρ s)) ≤ Φ →
      mean (fun s => (ρ s)⁻¹ ^ 2) ≤ C * (Φ + (g : ℝ) ^ 2 * Real.log (2 * g)) ∧
      mean (fun s => errE C₀ g (ρ s)) ≤ C * (Φ + (g : ℝ) ^ 2 * Real.log (2 * g)) ∧
      mean (fun s => max (Real.log (ρ s)⁻¹) 0) ≤
        1 / 2 * Real.log (1 + mean (fun s => (ρ s)⁻¹ ^ 2))

def firstMinimum {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ⨅ v : {v : L // v ≠ 0}, ‖(v.1 : EuclideanSpace ℝ (Fin n))‖

def shortVectorsIn {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {v | v ∈ L ∧ v ∈ V ∧ ‖v‖ ≤ r ∧ v ≠ 0}

def S8.Statement : Prop :=
  ∀ (n : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L],
    (firstMinimum L / Real.sqrt n) ^ n ≤ ZLattice.covolume L ∧
    ∀ (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℝ), firstMinimum L ≤ r →
      (shortVectorsIn L V r).Finite ∧
      ((shortVectorsIn L V r).ncard : ℝ) ≤ (3 * r / firstMinimum L) ^ Module.finrank ℝ V - 1

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.QuotientLiftInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace GenericFibreModelTransport

open MvPolynomial

theorem adjoin_transport {k₁ A₁ k₂ A₂ : Type*} [Field k₁] [Field A₁] [Algebra k₁ A₁] [Field k₂] [Field A₂]
    [Algebra k₂ A₂] (i : k₁ ≃+* k₂) (h : A₁ →+* A₂)
    (hc : (algebraMap k₂ A₂).comp i.toRingHom = h.comp (algebraMap k₁ A₁)) (s : Set A₁) (a : A₁) :
    Module.finrank k₁ (Algebra.adjoin k₁ s) = Module.finrank k₂ (Algebra.adjoin k₂ (h '' s)) ∧
      (Transcendental (Algebra.adjoin k₁ s) a ↔ Transcendental (Algebra.adjoin k₂ (h '' s)) (h a)) := by
  have hring : (Algebra.adjoin k₂ (h '' s)).toSubring = (Algebra.adjoin k₁ s).toSubring.map h := by
    rw [Algebra.adjoin_eq_ring_closure, Algebra.adjoin_eq_ring_closure, RingHom.map_closure, Set.image_union]
    congr 2
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨algebraMap k₁ A₁ (i.symm c), ⟨_, rfl⟩, by simpa using (congr($hc (i.symm c))).symm⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨i c, by simpa using congr($hc c)⟩
  have hmem : ∀ y, y ∈ Algebra.adjoin k₂ (h '' s) ↔ ∃ x ∈ Algebra.adjoin k₁ s, h x = y := fun y => by
    rw [← Subalgebra.mem_toSubring, hring, Subring.mem_map]; rfl
  let g : Algebra.adjoin k₁ s →+* Algebra.adjoin k₂ (h '' s) :=
    (h.comp (Algebra.adjoin k₁ s).val.toRingHom).codRestrict (Algebra.adjoin k₂ (h '' s))
      (fun x => (hmem _).2 ⟨x, x.2, rfl⟩)
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => Subtype.ext (h.injective (congr_arg Subtype.val hxy)), fun y => ?_⟩
    obtain ⟨x, hx, e⟩ := (hmem y).1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  let j := RingEquiv.ofBijective g hg
  refine ⟨Algebra.finrank_eq_of_equiv_equiv i j (RingHom.ext fun c => Subtype.ext congr($hc c)),
    (transcendental_ringHom_iff_of_comp_eq j h h.injective (RingHom.ext fun x => rfl)).symm⟩

theorem eval₂_mem_closure {σ F : Type*} [Field F] (c : ℤ →+* F) (y : σ → F) (f : MvPolynomial σ ℤ) :
    eval₂ c y f ∈ Subfield.closure (Set.range y) := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [eval₂_C, eq_intCast]; exact intCast_mem _ a
  | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
  | mul_X p n hp => rw [eval₂_mul, eval₂_X]; exact mul_mem hp (Subfield.subset_closure ⟨n, rfl⟩)

theorem quotient_lift_injective {A F : Type*} [CommRing A] [Field F] (φ : A →+* F) (P : Ideal A)
    (h : RingHom.ker φ = P) (hP : ∀ a ∈ P, φ a = 0) : Function.Injective (Ideal.Quotient.lift P φ hP) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.lift_mk] at ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ← h]
  exact ha

theorem subfield_equiv {L A Φ : Type*} [Field L] [Field A] [Field Φ] (k : Subfield L) (α : L →+* A)
    (ι : Φ →+* A) (hr : ι.fieldRange = k.map α) : ∃ e : k ≃+* Φ, ∀ c, ι (e c) = α c := by
  let g : k →+* ι.fieldRange :=
    (α.comp k.subtype).codRestrict ι.fieldRange (fun c => hr ▸ Subfield.mem_map.2 ⟨c, c.2, rfl⟩)
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => Subtype.ext (α.injective (congr_arg Subtype.val hxy)), fun y => ?_⟩
    have hy : (y : A) ∈ k.map α := hr ▸ y.2
    obtain ⟨x, hx, e⟩ := Subfield.mem_map.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  exact ⟨(RingEquiv.ofBijective g hg).trans ι.rangeRestrictFieldEquiv.symm, fun c =>
    RingHom.rangeRestrictFieldEquiv_apply_symm_apply ι (g c)⟩

end GenericFibreModelTransport

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset
open scoped ComplexOrder

noncomputable section

def onePipe {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R) :
    Matrix (Fin j) (Fin (j + m)) R :=
  Matrix.of fun a => Fin.append ((1 : Matrix (Fin j) (Fin j) R) a) (Z a)

def colsOf {R : Type*} {j N : ℕ} (A : Matrix (Fin j) (Fin N) R)
    (I : {I : Finset (Fin N) // I.card = j}) : Matrix (Fin j) (Fin j) R :=
  A.submatrix id (I.1.orderEmbOfFin I.2)

def rowsOf {R : Type*} {j N : ℕ} (B : Matrix (Fin N) (Fin j) R)
    (I : {I : Finset (Fin N) // I.card = j}) : Matrix (Fin j) (Fin j) R :=
  B.submatrix (I.1.orderEmbOfFin I.2) id

def CauchyBinet.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (j N : ℕ) (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R),
    (A * B).det = ∑ I : {I : Finset (Fin N) // I.card = j}, (colsOf A I).det * (rowsOf B I).det

def PlueckerNormSq.Statement : Prop :=
  ∀ (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ),
    ((∑ I : {I : Finset (Fin (j + m)) // I.card = j}, ‖(colsOf (onePipe Z) I).det‖ ^ 2 : ℝ) : ℂ) =
      (1 + Z * Zᴴ).det

def HadamardPSD.Statement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef → ‖A.det‖ ≤ ∏ i, ‖A i i‖

def PlueckerUnitBound.Statement : Prop :=
  ∀ (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ), (∀ a b, ‖Z a b‖ = 1) →
    ‖(1 + Z * Zᴴ).det‖ ≤ (1 + m : ℝ) ^ j

def PlueckerKernel.Statement : Prop :=
  ∀ (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ), (∀ a b, ‖Z a b‖ = 1) →
    ∑ I : {I : Finset (Fin (j + m)) // I.card = j}, ‖(colsOf (onePipe Z) I).det‖ ^ 2 ≤
      (1 + m : ℝ) ^ j

def RootsOfUnityDense.Statement : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℂ),
    (∀ z : Fin n → ℂ, (∀ i, ∃ k : ℕ, 0 < k ∧ z i ^ k = 1) → MvPolynomial.eval z P = 0) → P = 0

example : ∀ a b, ‖(!![1, Complex.I] : Matrix (Fin 1) (Fin 2) ℂ) a b‖ = 1 := by
  intro a b
  fin_cases a; fin_cases b <;> simp

example : (1 : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := PosSemidef.one

example (Z : Matrix (Fin 1) (Fin 2) ℂ) : (1 + Z * Zᴴ).PosSemidef :=
  PosSemidef.one.add (posSemidef_self_mul_conjTranspose Z)

example : ∀ i, ∃ k : ℕ, 0 < k ∧ (![1, -1] : Fin 2 → ℂ) i ^ k = 1 := by
  intro i
  refine ⟨2, by norm_num, ?_⟩
  fin_cases i <;> simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsHermFormCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

noncomputable section

def HermFormCompare.Statement : Prop :=
  ∀ (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℂ), M.PosDef → N.PosDef →
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℂ, (star x ⬝ᵥ (M *ᵥ x)).re ≤ c * (star x ⬝ᵥ (N *ᵥ x)).re

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin 2) (Fin 2) ℂ).PosDef ∧
    (1 : Matrix (Fin 2) (Fin 2) ℂ).PosDef :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLogCardLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open Classical in

def locLen {R : Type*} [CommRing R] (m : Ideal R) (N : Type*) [AddCommGroup N] [Module R N] : ℕ :=
  if h : m.IsPrime then
    haveI := h
    (Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N)).toNat
  else 0

def LogCardLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [Finite N],
    Real.log (Nat.card N) =
      ∑ᶠ (m : Ideal R) (_ : m.IsMaximal), (locLen m N : ℝ) * Real.log (Nat.card (R ⧸ m))

end

end GroundTheory.Heights₂.Heights
end

