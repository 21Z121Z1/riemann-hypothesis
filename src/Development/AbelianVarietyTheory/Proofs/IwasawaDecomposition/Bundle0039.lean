import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagMatLower

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimAffinePoints
section
open Module TopologicalSpace GlobalTheory.FlagPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPts

open MvPolynomial

variable {k : Type} [Field k] {J : Type}

def affPtsVanIdeal (x : AffPts k J) : PrimeSpectrum (MvPolynomial J k) :=
  ⟨RingHom.ker (MvPolynomial.eval (show J → k from x)), RingHom.ker_isPrime _⟩

theorem mem_affPtsVanIdeal_preimage_basicOpen (p : MvPolynomial J k) (x : AffPts k J) :
    x ∈ affPtsVanIdeal ⁻¹' (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum (MvPolynomial J k))) ↔
      MvPolynomial.eval x p ≠ 0 := by
  simp [affPtsVanIdeal, PrimeSpectrum.mem_basicOpen]

theorem isInducing_affPtsVanIdeal : Topology.IsInducing (affPtsVanIdeal (k := k) (J := J)) := by
  rw [Topology.isInducing_iff, PrimeSpectrum.isTopologicalBasis_basic_opens.eq_generateFrom,
    induced_generateFrom_eq]
  show TopologicalSpace.generateFrom _ = _
  congr 1
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨_, ⟨p, rfl⟩, by ext x; exact mem_affPtsVanIdeal_preimage_basicOpen p x⟩
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, by ext x; exact mem_affPtsVanIdeal_preimage_basicOpen p x⟩

theorem topologicalKrullDim_affPts_le [Fintype J] :
    topologicalKrullDim (AffPts k J) ≤ (Fintype.card J : ℕ) := by
  refine isInducing_affPtsVanIdeal.topologicalKrullDim_le.trans ?_
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card]
  simp

theorem isTopologicalBasis_affPts :
    IsTopologicalBasis (Set.preimage (affPtsVanIdeal (k := k) (J := J)) ''
      Set.range fun p : MvPolynomial J k ↦ (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum (MvPolynomial J k)))) :=
  PrimeSpectrum.isTopologicalBasis_basic_opens.isInducing isInducing_affPtsVanIdeal

theorem isIrreducible_univ_affPts [Infinite k] : IsIrreducible (Set.univ : Set (AffPts k J)) := by
  refine ⟨⟨fun _ ↦ 0, trivial⟩, ?_⟩
  rintro u v hu hv ⟨x, -, hx⟩ ⟨y, -, hy⟩
  obtain ⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, hxp, hpu⟩ := isTopologicalBasis_affPts.exists_subset_of_mem_open hx hu
  obtain ⟨_, ⟨_, ⟨q, rfl⟩, rfl⟩, hyq, hqv⟩ := isTopologicalBasis_affPts.exists_subset_of_mem_open hy hv
  rw [mem_affPtsVanIdeal_preimage_basicOpen] at hxp hyq
  have hp : p ≠ 0 := by rintro rfl; simp at hxp
  have hq : q ≠ 0 := by rintro rfl; simp at hyq
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  obtain ⟨z, hz⟩ : ∃ z : AffPts k J, MvPolynomial.eval z (p * q) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hpq (MvPolynomial.funext fun z ↦ by simpa using h z)
  rw [map_mul] at hz
  refine ⟨z, trivial, hpu ?_, hqv ?_⟩
  · exact (mem_affPtsVanIdeal_preimage_basicOpen p z).2 (left_ne_zero_of_mul hz)
  · exact (mem_affPtsVanIdeal_preimage_basicOpen q z).2 (right_ne_zero_of_mul hz)

open Classical in

def affPtsProj (S : Set J) (x : AffPts k J) : AffPts k J := fun j ↦ if j ∈ S then x j else 0

open Classical in
theorem eval_affPtsProj (S : Set J) (x : AffPts k J) (p : MvPolynomial J k) :
    MvPolynomial.eval (affPtsProj S x) p =
      MvPolynomial.eval x (MvPolynomial.bind₁ (fun j ↦ if j ∈ S then (X j : MvPolynomial J k) else 0) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.bind₁_C_right]
    exact (MvPolynomial.eval_C (f := affPtsProj S x) a).trans (MvPolynomial.eval_C (f := x) a).symm
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, map_mul, hp, MvPolynomial.bind₁_X_right]
    congr 1
    rw [MvPolynomial.eval_X (f := affPtsProj S x)]
    by_cases hj : j ∈ S
    · rw [if_pos hj, MvPolynomial.eval_X (f := x)]
      show (if j ∈ S then x j else 0) = x j
      rw [if_pos hj]
    · rw [if_neg hj, map_zero]
      show (if j ∈ S then x j else 0) = 0
      rw [if_neg hj]

theorem continuous_affPtsProj (S : Set J) : Continuous (affPtsProj (k := k) S) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨p, rfl⟩
  classical
  convert isOpen_affPts_ne_zero (k := k)
    (MvPolynomial.bind₁ (fun j ↦ if j ∈ S then (X j : MvPolynomial J k) else 0) p) using 1
  ext x
  show MvPolynomial.eval (affPtsProj S x) p ≠ 0 ↔ _
  rw [eval_affPtsProj]
  rfl

theorem range_affPtsProj (S : Set J) :
    Set.range (affPtsProj (k := k) S) = {x : AffPts k J | ∀ j, j ∉ S → x j = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ j hj
    simp [affPtsProj, hj]
  · intro hx
    refine ⟨x, funext fun j ↦ ?_⟩
    by_cases hj : j ∈ S
    · simp [affPtsProj, hj]
    · simp [affPtsProj, hj, hx j hj]

theorem isClosed_coordSubspace (S : Set J) : IsClosed {x : AffPts k J | ∀ j, j ∉ S → x j = 0} := by
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦ ?_
  rw [← isOpen_compl_iff]
  have : ({x : AffPts k J | x j = 0}ᶜ : Set (AffPts k J)) =
      {x : AffPts k J | MvPolynomial.eval x (X j : MvPolynomial J k) ≠ 0} := by
    ext x
    exact Iff.not (Eq.to_iff (congrArg (· = (0 : k)) (MvPolynomial.eval_X (f := x) j).symm))
  rw [this]
  exact isOpen_affPts_ne_zero _

def coordSubspace [Infinite k] (S : Set J) : IrreducibleCloseds (AffPts k J) :=
  ⟨{x : AffPts k J | ∀ j, j ∉ S → x j = 0},
    by
      rw [← range_affPtsProj, ← Set.image_univ]
      exact isIrreducible_univ_affPts.image _ (continuous_affPtsProj S).continuousOn,
    isClosed_coordSubspace S⟩

theorem le_topologicalKrullDim_affPts [Infinite k] [Fintype J] :
    ((Fintype.card J : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (AffPts k J) := by
  classical
  set e := Fintype.equivFin J
  set n := Fintype.card J
  let f : Fin (n + 1) → IrreducibleCloseds (AffPts k J) :=
    fun m ↦ coordSubspace {j | (e j : ℕ) < m}
  have hf : StrictMono f := by
    intro a b hab
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun x hx j hj ↦ hx j fun h ↦ hj ?_, ?_⟩
    · exact lt_trans (Set.mem_setOf.1 h) hab
    have ha : (a : ℕ) < n := lt_of_lt_of_le hab (Nat.lt_succ_iff.1 b.2)
    refine ⟨fun j ↦ if (e j : ℕ) = a then 1 else 0, ?_, ?_⟩
    · intro j hj
      have : (e j : ℕ) ≠ a := fun h ↦ hj (by simp only [Set.mem_setOf_eq, h]; exact hab)
      simp [this]
    · intro hx
      have := hx (e.symm ⟨a, ha⟩) (by simp)
      simp at this
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk n f hf)

theorem topologicalKrullDim_affPts_eq_card :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J],
      topologicalKrullDim (AffPts k J) = (Fintype.card J : ℕ) := by
  intro k _ _ J _
  haveI : Infinite k := inferInstance
  exact le_antisymm topologicalKrullDim_affPts_le le_topologicalKrullDim_affPts

end GlobalTheory.FlagPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TruncMatMemSubalgebra
section
set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

def truncMat {R : Type} [CommRing R] {d : ℕ} (m : ℕ) (M : Matrix (Fin d) (Fin d) R) :
    Matrix (Fin d) (Fin d) R :=
  fun c e => if (c : ℕ) < m ∧ (e : ℕ) < m then M c e else if c = e then 1 else 0

theorem truncMat_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ} (m : ℕ)
    (M : Matrix (Fin d) (Fin d) R) : (truncMat m M).map f = truncMat m (M.map f) := by
  ext c e
  simp only [truncMat, Matrix.map_apply]
  split_ifs <;> simp

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def frameMat (b g : Frames k V) (i : ι) : Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k :=
  fun c e => (b i).repr (g i e) c

def lowMat (b g : Frames k V) (i : ι) : Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k :=
  fun c a => (frameMat b g i * (truncMat ((a : ℕ) + 1) (frameMat b g i))⁻¹) c a

open Classical in

def flagLow (b : Frames k V) (F : Flags k V) (i : ι) :
    Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k :=
  fun c a => if h : ∃! v : V i, v ∈ F.step i ((a : ℕ) + 1) ∧ (b i).repr v a = 1 ∧
      ∀ c' : Fin (finrank k (V i)), c' < a → (b i).repr v c' = 0
    then (b i).repr h.exists.choose c else 0

def coordOf (j : ℕ) (L : ∀ i, Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k) :
    LocIdx k V j → k :=
  fun x => if ((x.2.1.2 : ℕ) < j ↔ (x.2.1.1 : ℕ) < j) then L x.1 x.2.1.1 x.2.1.2
    else (L x.1 * (truncMat j (L x.1)).adjugate) x.2.1.1 x.2.1.2

def chartInv (j : ℕ) (b : Frames k V) (F : Flags k V) : LocIdx k V j → k := coordOf j (flagLow b F)

def cellDisc [Fintype ι] (b g : Frames k V) : k :=
  ∏ i, ∏ m : Fin (finrank k (V i) + 1), (truncMat (m : ℕ) (frameMat b g i)).det

theorem det_mem_subalgebra {X : Type} {n : Type} [Fintype n] [DecidableEq n]
    (A : Subalgebra k (X → k)) (M : X → Matrix n n k) (h : ∀ c e, (fun x => M x c e) ∈ A) :
    (fun x => (M x).det) ∈ A := by
  simp only [Matrix.det_apply]
  have : (fun x => ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ c, M x (σ c) c) =
      ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ c, (fun x => M x (σ c) c) := by
    ext x
    simp [Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact Subalgebra.sum_mem _ fun σ _ => Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun c _ => h _ _) _

theorem frameMat_mem_regFns (b : Frames k V) (i : ι) (c e : Fin (finrank k (V i))) :
    (fun g : Frames k V => frameMat b g i c e) ∈ regFns k V :=
  Algebra.subset_adjoin (.inl ⟨i, (b i).coord c, e, rfl⟩)

theorem truncMat_mem_subalgebra {X : Type} {d : ℕ} (A : Subalgebra k (X → k)) (m : ℕ)
    (M : X → Matrix (Fin d) (Fin d) k) (h : ∀ c e, (fun x => M x c e) ∈ A) (c e : Fin d) :
    (fun x => truncMat m (M x) c e) ∈ A := by
  simp only [truncMat]
  split_ifs
  · exact h c e
  · exact (show (fun _ : X => (1 : k)) = 1 from rfl) ▸ one_mem A
  · exact (show (fun _ : X => (0 : k)) = 0 from rfl) ▸ zero_mem A

theorem cellDisc_mem_regFns [Fintype ι] (b : Frames k V) : (fun g => cellDisc b g) ∈ regFns k V := by
  have : (fun g => cellDisc b g) = ∏ i, ∏ m : Fin (finrank k (V i) + 1),
      (fun g : Frames k V => (truncMat (m : ℕ) (frameMat b g i)).det) := by
    ext g
    simp [cellDisc, Finset.prod_apply]
  rw [this]
  exact Subalgebra.prod_mem _ fun i _ => Subalgebra.prod_mem _ fun m _ =>
    det_mem_subalgebra _ _ (truncMat_mem_subalgebra _ _ _ (frameMat_mem_regFns b i))

def fracAlg [Fintype ι] (b : Frames k V) : Subalgebra k (Frames k V → k) where
  carrier := {f | ∃ R ∈ regFns k V, ∃ K : ℕ, ∀ g, cellDisc b g ≠ 0 → f g * cellDisc b g ^ K = R g}
  mul_mem' := by
    rintro f₁ f₂ ⟨R₁, hR₁, K₁, h₁⟩ ⟨R₂, hR₂, K₂, h₂⟩
    refine ⟨R₁ * R₂, mul_mem hR₁ hR₂, K₁ + K₂, fun g hg => ?_⟩
    simp only [Pi.mul_apply, ← h₁ g hg, ← h₂ g hg]
    ring
  add_mem' := by
    rintro f₁ f₂ ⟨R₁, hR₁, K₁, h₁⟩ ⟨R₂, hR₂, K₂, h₂⟩
    have hD := cellDisc_mem_regFns b
    refine ⟨R₁ * (fun g => cellDisc b g) ^ K₂ + R₂ * (fun g => cellDisc b g) ^ K₁,
      add_mem (mul_mem hR₁ (pow_mem hD _)) (mul_mem hR₂ (pow_mem hD _)), K₁ + K₂, fun g hg => ?_⟩
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, ← h₁ g hg, ← h₂ g hg]
    ring
  algebraMap_mem' := fun r =>
    ⟨algebraMap k _ r, Subalgebra.algebraMap_mem _ r, 0, fun g _ => by simp⟩

theorem regFns_le_fracAlg [Fintype ι] (b : Frames k V) : regFns k V ≤ fracAlg b :=
  fun f hf => ⟨f, hf, 0, fun g _ => by simp⟩

example [Fintype ι] (b : Frames k V) : cellDisc b b = 1 := by
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun m _ => ?_
  have : truncMat (m : ℕ) (frameMat b b i) = 1 := by
    ext c e
    simp only [truncMat, frameMat, Basis.repr_self, Matrix.one_apply]
    by_cases h : e = c
    · subst h; simp
    · simp [Finsupp.single_apply, h, Ne.symm h]
  rw [this, Matrix.det_one]

end GlobalTheory.FlagPts
end
end

