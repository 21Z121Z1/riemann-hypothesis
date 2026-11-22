import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.GlGeneratedTransvectionsDiag
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
section
noncomputable section
namespace GlobalTheory.GLGen
open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

theorem single_neg' (x y : Fin n) (a : R) : single x y (-a) = -single x y a := by
  ext p q; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp

theorem diag_transv_diag (a b : Fin n → R) (hab : ∀ k, a k * b k = 1) {i j : Fin n} (hij : i ≠ j) (c : R) :
    diagonal a * transvection i j c * diagonal b = transvection i j (a i * c * b j) := by
  have h1 : diagonal a * diagonal b = (1 : Matrix (Fin n) (Fin n) R) := by
    rw [diagonal_mul_diagonal]; simp [hab]
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
  congr 1
  ext x y
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs with h <;> simp_all

theorem w_eq {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    transvection i j (u : R) * transvection j i (-((u⁻¹ : Rˣ) : R)) * transvection i j (u : R) =
      1 + single i j (u : R) + single j i (-((u⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1 := by
  have z1 : ∀ (a b : R) (x l : Fin n), single x j a * single j l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z2 : ∀ (a b : R) (x l : Fin n), single x i a * single i l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z3 : ∀ (a b : R) (x l : Fin n), single x j a * single i l b = 0 := fun a b x l => single_mul_single_of_ne a x j i hij.symm b
  have z4 : ∀ (a b : R) (x l : Fin n), single x i a * single j l b = 0 := fun a b x l => single_mul_single_of_ne a x i j hij b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, z1, z2, z3, z4]
  simp only [mul_neg, neg_mul, Units.mul_inv, Units.inv_mul, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left, single_neg', Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, one_mul, mul_one]
  abel

theorem ww_eq {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    (1 + single i j (u : R) + single j i (-((u⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1) *
      (1 + single i j ((-1 : Rˣ) : R) + single j i (-(((-1 : Rˣ)⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1) =
      diagonal (fun k => if k = i then (u : R) else if k = j then ((u⁻¹ : Rˣ) : R) else 1) := by
  have z1 : ∀ (a b : R) (x l : Fin n), single x j a * single j l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z2 : ∀ (a b : R) (x l : Fin n), single x i a * single i l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z3 : ∀ (a b : R) (x l : Fin n), single x j a * single i l b = 0 := fun a b x l => single_mul_single_of_ne a x j i hij.symm b
  have z4 : ∀ (a b : R) (x l : Fin n), single x i a * single j l b = 0 := fun a b x l => single_mul_single_of_ne a x i j hij b
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, z1, z2, z3, z4]
  clear z1 z2 z3 z4
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have hji : j ≠ i := Ne.symm hij
  by_cases hpq : p = q
  · subst hpq
    by_cases hpi : p = i
    · subst hpi; simp [hij, hji]
    · by_cases hpj : p = j
      · subst hpj; simp [hij, hji]
      · simp [hpi, hpj, Ne.symm hpi, Ne.symm hpj]
  · by_cases hpi : p = i <;> by_cases hqi : q = i <;> by_cases hpj : p = j <;> by_cases hqj : q = j <;>
      simp_all [eq_comm]

def diagU (u : Fin n → Rˣ) : GL (Fin n) R :=
  ⟨diagonal (fun k => (u k : R)), diagonal (fun k => (((u k)⁻¹ : Rˣ) : R)),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

theorem diagU_val (u : Fin n → Rˣ) : ((diagU u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal (fun k => (u k : R)) := rfl

theorem diagU_inv_val (u : Fin n → Rˣ) :
    (((diagU u)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal (fun k => (((u k)⁻¹ : Rˣ) : R)) := rfl

theorem diagU_mul (u v : Fin n → Rˣ) : diagU (u * v) = diagU u * diagU v := by
  ext : 1
  simp only [Units.val_mul, diagU_val, diagonal_mul_diagonal, Pi.mul_apply]

theorem diagU_one : diagU (1 : Fin n → Rˣ) = 1 := by
  ext : 1
  simp [diagU_val]

def transvGL {i j : Fin n} (hij : i ≠ j) (c : R) : GL (Fin n) R :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same (h := hij), neg_add_cancel, transvection_zero]⟩

def transvSet (R : Type) [CommRing R] (n : ℕ) : Set (GL (Fin n) R) :=
  {g | ∃ i j c, i ≠ j ∧ (g : Matrix (Fin n) (Fin n) R) = transvection i j c}

def elem (R : Type) [CommRing R] (n : ℕ) : Subgroup (GL (Fin n) R) := Subgroup.closure (transvSet R n)

theorem transvGL_mem {i j : Fin n} (hij : i ≠ j) (c : R) : transvGL hij c ∈ elem R n :=
  Subgroup.subset_closure ⟨i, j, c, hij, rfl⟩

theorem conj_mem (u : Fin n → Rˣ) {e : GL (Fin n) R} (he : e ∈ elem R n) :
    diagU u * e * (diagU u)⁻¹ ∈ elem R n := by
  have hle : elem R n ≤ (elem R n).comap (MulAut.conj (diagU u)).toMonoidHom := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro g ⟨i, j, c, hij, hg⟩
    simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨i, j, (u i : R) * c * ((u j)⁻¹ : Rˣ), hij, ?_⟩
    rw [Units.val_mul, Units.val_mul, hg, diagU_val, diagU_inv_val]
    exact diag_transv_diag _ _ (fun k => Units.mul_inv (u k)) hij c
  simpa using hle he

theorem whitehead_mem {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    diagU (fun k => if k = i then u else if k = j then u⁻¹ else 1) ∈ elem R n := by
  have e : diagU (fun k => if k = i then u else if k = j then u⁻¹ else 1) =
      transvGL hij (u : R) * transvGL hij.symm (-((u⁻¹ : Rˣ) : R)) * transvGL hij (u : R) *
      (transvGL hij ((-1 : Rˣ) : R) * transvGL hij.symm (-(((-1 : Rˣ)⁻¹ : Rˣ) : R)) *
        transvGL hij ((-1 : Rˣ) : R)) := by
    ext : 1
    simp only [Units.val_mul, transvGL, diagU_val]
    rw [w_eq hij u, w_eq hij (-1), ww_eq hij u]
    congr 1
    funext k
    split_ifs <;> rfl
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) <;> exact transvGL_mem _ _

theorem diagU_inv (u : Fin n → Rˣ) : diagU u⁻¹ = (diagU u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← diagU_mul, inv_mul_cancel, diagU_one])

def diagHomU : (Fin n → Rˣ) →* GL (Fin n) R where
  toFun := diagU
  map_one' := diagU_one
  map_mul' := diagU_mul

theorem pair_mem_elem (i j : Fin n) (a : Rˣ) :
    diagU (Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Rˣ) ∈ elem R n := by
  by_cases hij : i = j
  · subst hij
    have : (Pi.mulSingle i a * Pi.mulSingle i a⁻¹ : Fin n → Rˣ) = 1 := by
      rw [← Pi.mulSingle_mul]; simp
    rw [this, diagU_one]
    exact one_mem _
  · have hji : j ≠ i := fun h => hij h.symm
    have : (Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Rˣ) =
        fun k => if k = i then a else if k = j then a⁻¹ else 1 := by
      funext k
      by_cases hki : k = i
      · subst hki; simp [hij]
      · by_cases hkj : k = j
        · subst hkj; simp [hki]
        · simp [hki, hkj]
    rw [this]
    exact whitehead_mem hij a

theorem diag_mem_of_prod (u : Fin n → Rˣ) (hu : ∏ k, u k = 1) : diagU u ∈ elem R n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : diagU u = 1 := Units.ext (Subsingleton.elim _ _)
    rw [this]
    exact one_mem _
  · let j : Fin n := ⟨0, hpos⟩
    have key : u = ∏ k, (Pi.mulSingle k (u k) * Pi.mulSingle j (u k)⁻¹ : Fin n → Rˣ) := by
      rw [Finset.prod_mul_distrib, Finset.univ_prod_mulSingle]
      have : (∏ k, (Pi.mulSingle j (u k)⁻¹ : Fin n → Rˣ)) = 1 := by
        have h := map_prod (MonoidHom.mulSingle (fun _ : Fin n => Rˣ) j) (fun k => (u k)⁻¹)
          Finset.univ
        rw [Finset.prod_inv_distrib, hu, inv_one, map_one] at h
        exact h.symm
      rw [this, mul_one]
    have : u ∈ (elem R n).comap (diagHomU (R := R) (n := n)) := by
      rw [key]
      exact Subgroup.prod_mem _ (fun k _ => pair_mem_elem k j (u k))
    exact this

theorem det_eq_one_of_mem {e : GL (Fin n) R} (he : e ∈ elem R n) : GeneralLinearGroup.det e = 1 := by
  have hle : elem R n ≤ (GeneralLinearGroup.det : GL (Fin n) R →* Rˣ).ker := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro g ⟨i, j, c, hij, hg⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext
    rw [GeneralLinearGroup.val_det_apply, hg, det_transvection_of_ne _ _ hij]
    rfl
  exact hle he

theorem mem_of_det_eq_one : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)) →
    ∀ (n : ℕ) (H : Subgroup (GL (Fin n) R)), (∀ (i j : Fin n), i ≠ j → ∀ (t : R) (u : GL (Fin n) R),
      u.1 = Matrix.transvection i j t → u ∈ H) → ∀ a : GL (Fin n) R, Matrix.GeneralLinearGroup.det a = 1 → a ∈ H := by
  intro R _ hsr n H hH a ha
  have hEH : elem R n ≤ H := Subgroup.closure_le _ |>.2 (by
    rintro g ⟨i, j, c, hij, hg⟩; exact hH i j hij c g hg)
  have hSR : PI.VolSemiDirect.W.Cj.HasStableRangeOne R := fun a b x y h =>
    hsr a b ⟨x, y, by rw [← h]; ring⟩
  have hmem := PI.VolSemiDirect.W.Cj.gl_generated_transvections_diag R hSR n a
  have key : ∀ g ∈ Subgroup.closure ({g : GL (Fin n) R | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin n) (Fin n) R) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin n → R, (g : Matrix (Fin n) (Fin n) R) = Matrix.diagonal d}),
      ∃ u : Fin n → Rˣ, g * diagU u ∈ elem R n := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with ⟨i, j, c, hij, hg⟩ | ⟨d, hd⟩
      · exact ⟨1, by rw [diagU_one, mul_one]; exact Subgroup.subset_closure ⟨i, j, c, hij, hg⟩⟩
      · have hu : ∀ k, IsUnit (d k) := fun k => by
          have h : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          have h' := congrFun (congrFun h k) k
          rw [hd, Matrix.mul_diagonal, one_apply_eq] at h'
          exact ⟨⟨d k, _, by rw [mul_comm]; exact h', h'⟩, rfl⟩
        refine ⟨fun k => (hu k).unit⁻¹, ?_⟩
        have e : g * diagU (fun k => (hu k).unit⁻¹) = 1 := by
          ext : 1
          rw [Units.val_mul, hd, diagU_val, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
          congr 1
          funext k
          exact (hu k).mul_val_inv
        rw [e]; exact Subgroup.one_mem _
    | one => exact ⟨1, by rw [diagU_one, mul_one]; exact Subgroup.one_mem _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨v * u, ?_⟩
      have h := Subgroup.mul_mem _ hu (conj_mem u⁻¹ hv)
      rw [diagU_inv, inv_inv] at h
      convert h using 1
      rw [diagU_mul]
      group
    | inv x _ hx =>
      obtain ⟨u, hu⟩ := hx
      refine ⟨u⁻¹, ?_⟩
      have h := conj_mem u (Subgroup.inv_mem _ hu)
      rw [diagU_inv]
      convert h using 1
      group
  obtain ⟨u, hu⟩ := key a hmem
  have h1 := det_eq_one_of_mem hu
  rw [map_mul, ha, one_mul] at h1
  have hprod : ∏ k, u k = 1 := by
    have h2 := congrArg Units.val h1
    rw [GeneralLinearGroup.val_det_apply, diagU_val, det_diagonal] at h2
    ext
    rw [Units.coe_prod]
    simpa using h2
  have hd := diag_mem_of_prod u hprod
  have e : a = (a * diagU u) * (diagU u)⁻¹ := by group
  rw [e]
  exact hEH (Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hd))

end GlobalTheory.GLGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLoc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeckeSplitAll

def splitLoc (D : D7) : Set (AE D)ˣ :=
  {x | ∃ e, IsSplitIdem D e ∧ (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1}

def modSet (D : D7) (N : ℕ) : Set (AE D)ˣ :=
  {x | infPart D (x : AE D) = 1 ∧
    (∃ r ∈ intAE D, finPart D (x : AE D) - 1 = (N : Af D.host.F ⊗[D.host.F] D.host.E) * r) ∧
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D}

def grpH (D : D7) (N : ℕ) : Subgroup (AE D)ˣ :=
  Subgroup.closure (Set.range (Units.map (incA D).toMonoidHom) ∪ splitLoc D ∪ modSet D N)

end GlobalTheory.HeckeSplitAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalComponentsOneMulInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section
namespace GlobalTheory.LocOm

theorem isLoc_one_mul_inv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z), p.IsLoc F 1 1 ∧ (∀ (g g' : GA D V) (gk gk' : GL Z k), p.IsLoc F g gk → p.IsLoc F g' gk' → p.IsLoc F (g * g') (gk * gk')) ∧ ∀ (g : GA D V) (gk : GL Z k), p.IsLoc F g gk → p.IsLoc F g⁻¹ gk⁻¹ := by
  intro D k _ _ _ _ p V Z _ _ F
  have hmul : ∀ g g' : GA D V, (mt V (g * g')).map p.π = (mt V g).map p.π * (mt V g').map p.π := fun g g' => by
    rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.map_mul]
  refine ⟨⟨GlobalTheory.SplitLinear.suppAt_one _ _, ?_⟩, fun g g' gk gk' h h' => ⟨GlobalTheory.SplitLinear.suppAt_mul h.1 h'.1, ?_⟩,
    fun g gk h => ⟨GlobalTheory.SplitLinear.suppAt_inv h.1, ?_⟩⟩
  · rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero p.π) (map_one p.π), Units.val_one, Matrix.mul_one, F.βγ]
  · rw [hmul, h.2, h'.2, Units.val_mul]
    rw [Matrix.mul_assoc (F.β * gk.val), ← Matrix.mul_assoc F.γ, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  · have e1 : (mt V g⁻¹).map p.π * (F.β * gk.val * F.γ) = 1 := by
      rw [← h.2, ← hmul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero p.π) (map_one p.π)]
    have e2 : (F.β * gk.val * F.γ) * (F.β * (gk⁻¹).val * F.γ) = 1 := by
      rw [Matrix.mul_assoc (F.β * gk.val), ← Matrix.mul_assoc F.γ, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul,
        Matrix.mul_assoc F.β, ← Matrix.mul_assoc gk.val, Units.mul_inv, Matrix.one_mul, F.βγ]
    calc (mt V g⁻¹).map p.π = (mt V g⁻¹).map p.π * ((F.β * gk.val * F.γ) * (F.β * (gk⁻¹).val * F.γ)) := by
          rw [e2, Matrix.mul_one]
      _ = F.β * (gk⁻¹).val * F.γ := by rw [← Matrix.mul_assoc, e1, Matrix.one_mul]

end GlobalTheory.LocOm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceFrameLattice_of_movedLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (γ : GA D S) (L M : Lat S) (Λ : Submodule 𝒪[k] (n → k)), Moves S γ L M (· = p.v) → β.IsLatMoved γ L Λ → β.IsLat M Λ := by
  first | exact @GlobalTheory.FinPl.Frame.isLat_of_isLatMoved | exact GlobalTheory.FinPl.Frame.isLat_of_isLatMoved | (intros; apply GlobalTheory.FinPl.Frame.isLat_of_isLatMoved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearLawHalfVacuum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
  GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinearHalf

open GlobalTheory.SplitLinear GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.VecInv

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {ΛS : Submodule (NumberField.RingOfIntegers D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (NumberField.RingOfIntegers D.host.E) (Fin T.rank → D.host.E)}
  {a : AE D} {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {e : AE D}

section Model

variable (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (ha : a * a = a)
  (hinf : infPart D a = 0) (hc : a * cA D a = 0) (hf : IsThetaFunO ψ S T f₀)
  (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
  (he : IsSplitIdem D e) (hae : a * e = e)
  (hfix : ∀ u ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀)

include hW hS hT ha hinf hc hf hTm he hae hfix

theorem base_enlarge {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {x y : (AE D)ˣ}
    (hx : IsDetAt e S g x) (hy : IsDetAt e T h y)
    (hle : ∀ w ∈ latO S T ΛS ΛT fun _ => True, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT fun _ => True) :
    om (g, h) f₀ = ((splitFacO χS χT x y : ℂ) * ((Real.sqrt ((((latO S T ΛS ΛT fun _ => True) ⊓ half S T e).relIndex
      ((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹) ⊓ half S T e) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹) •
      Tm fun t => halfInd a (latO S T ΛS ΛT fun _ => True) (actO S T g⁻¹ h⁻¹ t) := by
  haveI := finite_enlarge hS.1 hT.1 he.1 hle
  obtain ⟨R, r1, r2, r3⟩ := exists_reps ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e)
    ((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹) ⊓ half S T e)
  have hR : ∀ u ∈ R, actO S T g⁻¹ h⁻¹ u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e u := fun u hu =>
    ⟨(r2 u hu).1, (isHalf_iff S T).2 (r2 u hu).2⟩
  have hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT (fun _ => True) → IsHalf e w →
      ∃! v, v ∈ R ∧ w - v ∈ latO S T ΛS ΛT (fun _ => True) := fun w hw hwe =>
    (existsUnique_congr fun v => and_congr_right fun hv =>
      ⟨fun h => h.1, fun h => ⟨h, (isHalf_iff S T).1 (GlobalTheory.SplitScalar.isHalf_sub hwe (hR v hv).2)⟩⟩).1
      (r3 w ⟨hw, (isHalf_iff S T).1 hwe⟩)
  rw [om_eq_sum_lattice hW hS hT he hf hfix hg hh hx hy hR hRu hle, r1,
    model_sum hTm fun u hu => isHalf_mono hae (hR u hu).2,
    sum_halfInd he.1 hc hae (GlobalTheory.SplitScalar.idem_smul_mem he.1) (suppAt_inv hg) (suppAt_inv hh) hR hRu hle]

theorem law_enlarge' {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h)
    (hle : ∀ w ∈ latO S T ΛS ΛT fun _ => True, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT fun _ => True) :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm g h (fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h)) := by
  have h1 := base_enlarge hW hS hT ha hinf hc hf hTm he hae hfix hg hh
    (isDetAt_detAt e he.1 S g) (isDetAt_detAt e he.1 T h) hle
  rw [← Complex.ofReal_inv, sqrt_index hS.1 hT.1 he (isDetAt_detAt e he.1 S g) (isDetAt_detAt e he.1 T h) hle] at h1
  exact om_model_of_base D ψ S T χS χT om ΛS ΛT a f₀ Tm hW hS hT ha hinf hf hTm g h _ h1

theorem law_place' {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm g h (fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h)) := by
  obtain ⟨N, hN, h1⟩ := exists_nsmul_actO hS.1 hT.1 g⁻¹ h⁻¹
  obtain ⟨z, z1, z2⟩ := exists_scalar he T hN
  have z4 : SuppAt e T z⁻¹ := suppAt_of (GlobalTheory.SplitScalar.off_smul_mt_inv z1)
  have l1 := law_enlarge' hW hS hT ha hinf hc hf hTm he hae hfix hg (suppAt_mul hh z4) fun w hw hwe => by
    rw [actO_scalar' z2 g h hwe]
    exact h1 w hw
  have l2 := law_enlarge' hW hS hT ha hinf hc hf hTm he hae hfix (suppAt_one e S) z4 fun w hw hwe => by
    rw [inv_one, inv_inv, actO_scalar z2 hwe]
    exact nsmul_mem hw N
  have l3 := l1.mul hS.1 hT.1 (l2.inv hS.1 hT.1 (fac_ne_zero _ _))
  have e1 : fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T (h * z⁻¹)) =
      fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h) * fac S T χS χT (detAt e he.1 S 1) (detAt e he.1 T z⁻¹) := by
    rw [← fac_mul, ← MonoidHom.map_mul, ← MonoidHom.map_mul, mul_one]
  exact l3.congr (by rw [inv_one, mul_one]) (mul_inv_cancel_right _ _)
    (by rw [e1, mul_inv_cancel_right₀ (fac_ne_zero _ _)])

end Model

theorem detAt_eq {V : HSp D} (he : e * e = e) {g : GA D V} {x : (AE D)ˣ} (hx : IsDetAt e V g x) :
    x = detAt e he V g :=
  Units.ext (hx.trans (isDetAt_detAt e he V g).symm)

theorem law_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Lat S)
    (ΛT : Lat T) (e : AE D) (f₀ : WO S T → ℂ)
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsSplitIdem D e → IsThetaFunO ψ S T f₀ →
    (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀) →
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
    ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
    ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) Φ →
      om (g, h) (Tm Φ) = GlobalTheory.SplitLinear.fac S T χS χT x y • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) := by
  intro D ψ S T χS χT om ΛS ΛT e f₀ Tm hW hS hT he hf hfix hTm g h hg hh x y hx hy Φ hΦ
  have hinf : infPart D e = 0 := GlobalTheory.PlaceModelSum.IsOrthSum.infPart_eq
    ⟨Unit, {()}, fun _ => e, fun _ _ => he, fun _ _ _ _ h => absurd rfl h, (Finset.sum_singleton (fun _ => e) ()).symm⟩
  rw [detAt_eq he.1 hx, detAt_eq he.1 hy]
  exact law_place' hW hS hT he.1 hinf he.2.1 hf hTm he he.1 hfix hg hh Φ hΦ

end GlobalTheory.SplitLinearHalf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBesselStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) , (∀ (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y), (∀ gk : GL Y k, ∃! g, p.IsLoc F g gk) ∧ (∀ g, SuppAt p.e S g → ∃ gk, p.IsLoc F g gk) ∧ ∀ g gk h hk, p.IsLoc F g gk → p.IsLoc F h hk → p.IsLoc F (g * h) (gk * hk)) ∧ (∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)), p.IsJacFrame J s hh F₀ F → ∀ g β q, q ∈ R k n c (ρ + 1) → p.IsLoc F g (colE c (ρ + 1) β * q) → g ∈ jacGrp J.d) ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA F → ∀ g q, q ∈ R k n c (ρ + 1) → p.IsLoc F g q → g ∈ besGrp B.d B.o := by
  first | exact @GlobalTheory.LocGrp.local_groups | exact GlobalTheory.LocGrp.local_groups | (intros; apply GlobalTheory.LocGrp.local_groups <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumOfCarriesLatticeCompletionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLatticeVacuum_of_carriesLatticeCompletions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (f : WO S T → ℂ), Vac ψ S T LS LT P f → ∀ (g : GA D S) (h : GA D T) (MS : Lat S) (MT : Lat T), IsSelfDualC S MS → IsSelfDualC T MT → Moves S g LS MS P → Moves T h LT MT P → Vac ψ S T MS MT P (om (g, h) f) := by
  first | exact @GlobalTheory.VacMove.vac_of_moves | exact GlobalTheory.VacMove.vac_of_moves | (intros; apply GlobalTheory.VacMove.vac_of_moves <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsPrimeWeightSizes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem GlobalTheory.CoreHt.sizes_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → (∀ u, 4 * L.sc.a < (((I.rec7 l Z).mem u).A.T : ℝ)) → Formalism.L2.Col.Sizes (B.primes X) B.wts L.sc.a := by
  intro B X I h l Z L CY hR hX' hx hT
  have hW := (GlobalTheory.Mem.wts_ok_and_sizes B X).2
  have hF := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).2
  obtain ⟨P⟩ := hR.1
  have hfN := GlobalTheory.ColumnNormCompare.SizeRows.f_mul_N_le_b P hR.2.2.2.1.1
  have hb1 := GlobalTheory.ColumnNormCompare.SizeRows.one_le_b L.sc
  refine ⟨hW.g_big, fun u => hT u, ?_, GlobalTheory.T.trueColumnWeight_spread_le_two_mul_scale I h l Z L CY hR hX' hx⟩
  have hab : 2 * L.sc.b ≤ L.sc.a := by
    show 2 * L.sc.b ≤ L.sc.x * L.sc.b
    nlinarith
  have hfN' : ((B.fields.f : ℝ)) * (B.R.N B.R.m : ℝ) ≤ L.sc.b := by
    rw [hF]; exact hfN
  push_cast
  linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicEqComponentAtPlaceMulOffPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelic_eq_componentAtPlace_mul_offPlace : ∀ (D : D7) (S : HSp D) (h : GA D S) (v : Pl D), ∃ hv ∈ grpAt S (· = v), ∃ h' ∈ grpOff S (· = v), h = hv * h' := by
  first | exact @GlobalTheory.FinPl.decompAt | exact GlobalTheory.FinPl.decompAt | (intros; apply GlobalTheory.FinPl.decompAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicTrivialAtPlacesSubgroupAntitoneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicTrivialAtPlacesSubgroup_antitone : ∀ (D : D7) (S : HSp D) (P Q : Pl D → Prop), (∀ v, Q v → P v) → grpOff S P ≤ grpOff S Q := by
  first | exact @GlobalTheory.FinPl.grpOff_anti | exact GlobalTheory.FinPl.grpOff_anti | (intros; apply GlobalTheory.FinPl.grpOff_anti <;> assumption)
end

