import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0025
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0030
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0026
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005
import Development.WeilBound.CoreStatements.AmpleLineBundles.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeightPolynomialWeightForm
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace FlLines

section Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_integralCombination_of_mem_completedLattice {A B D : Type} [Fintype A] [Fintype B] [Fintype D] (ca : A → ℤ) (bb : A → D → ℤ) (P : B → ℤ)
    (G : D → B → ℤ) :
    ∑ k, (∑ a, ca a * bb a k) * ∑ w, P w * G k w = ∑ a, ∑ w, (P w * ca a) * ∑ k, bb a k * G k w := by
  have h1 : ∀ k, (∑ a, ca a * bb a k) * ∑ w, P w * G k w = ∑ a, ∑ w, (ca a * bb a k) * (P w * G k w) :=
    fun k => Finset.sum_mul_sum _ _ _ _
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => by ring

theorem geoNum_polar {σ : Type} [Fintype σ] (n : ℕ) (V : Ideal (MRing ι)) (c : Fin n → σ → ℤ) (b : σ → K → ℤ) :
    geoNum n V (fun r k => ∑ a, c r a * b a k) =
      ∑ w : Fin n → σ, (∏ r, c r (w r)) * geoNum n V (fun r => b (w r)) := by
  classical
  induction n generalizing V with
  | zero =>
    have h : ∀ a a' : Fin 0 → K → ℤ, geoNum 0 V a = geoNum 0 V a' := fun a a' => by
      rw [Subsingleton.elim a a']
    simp only [Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact h _ _
  | succ n ih =>
    by_cases hV : IsRelevant V
    · rw [← (Fin.snocEquiv (fun _ => σ)).sum_comp, Fintype.sum_prod_type]
      simp only [geoNum, dif_pos hV]
      have hin : ∀ (a : σ) (w' : Fin n → σ),
          Fin.init (fun r => b ((Fin.snocEquiv (fun _ => σ)) (a, w') r)) = fun r => b (w' r) := by
        intro a w'
        funext r
        simp [Fin.init, Fin.snocEquiv]
      have hla : ∀ (a : σ) (w' : Fin n → σ), (Fin.snocEquiv (fun _ => σ)) (a, w') (Fin.last n) = a := by
        intro a w'
        simp [Fin.snocEquiv]
      have hca : ∀ (a : σ) (w' : Fin n → σ) (r : Fin n),
          (Fin.snocEquiv (fun _ => σ)) (a, w') r.castSucc = w' r := by
        intro a w' r
        simp [Fin.snocEquiv]
      have hi2 : Fin.init (fun r k => ∑ a, c r a * b a k) =
          fun (r : Fin n) k => ∑ a, c r.castSucc a * b a k := by
        funext r k
        simp [Fin.init]
      simp only [hin, hla, Fin.prod_univ_castSucc, hca, hi2]
      have e : ∀ (k : K) (f : Ideal (MRing ι) → ℤ),
          ∑ᶠ W ∈ divSupp V (X ⟨k, (hV k).choose⟩ : MRing ι), f W =
            ∑ W ∈ (divSupp_finite V (X ⟨k, (hV k).choose⟩ : MRing ι)).toFinset, f W :=
        fun k f => finsum_mem_eq_finite_toFinset_sum f (divSupp_finite _ _)
      simp only [e]
      simp only [ih _ (fun r => c r.castSucc)]
      rw [← exists_integralCombination_of_mem_completedLattice (fun a => c (Fin.last n) a) b (fun w' : Fin n → σ => ∏ r, c r.castSucc (w' r))]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun W _ => ?_
      ring
    · have e : ∀ a, geoNum (n + 1) V a = 0 := fun a => by simp only [geoNum, dif_neg hV]
      simp [e]

theorem degSum_polar {σ : Type} [Fintype σ] (e : ℕ) (S : Set (Ideal (MRing ι))) (hS : S.Finite)
    (m : Ideal (MRing ι) → ℝ) (lam : σ → ℤ) (b : σ → K → ℤ) :
    ∑ w : Fin e → σ, (∏ r, (lam (w r) : ℝ)) * ∑ᶠ V ∈ S, m V * (geoNum e V (fun r => b (w r)) : ℝ) =
      ∑ᶠ V ∈ S, m V * (geoNum e V (fun _ k => ∑ a, lam a * b a k) : ℝ) := by
  have e' : ∀ f : Ideal (MRing ι) → ℝ, ∑ᶠ V ∈ S, f V = ∑ V ∈ hS.toFinset, f V :=
    fun f => finsum_mem_eq_finite_toFinset_sum f hS
  have hp : ∀ V : Ideal (MRing ι), geoNum e V (fun _ k => ∑ a, lam a * b a k) =
      ∑ w : Fin e → σ, (∏ r, lam (w r)) * geoNum e V (fun r => b (w r)) :=
    fun V => geoNum_polar e V (fun _ => lam) b
  simp only [e', hp]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun V _ => Finset.sum_congr rfl fun w _ => ?_
  ring

end Geo

section Wt

variable {Ψ : Type} {N : ℕ}

def gapZ (lam : Ψ × Fin N → ℤ) (p : Ψ × Fin N) : ℤ :=
  lam p - if h : (p.2 : ℕ) + 1 < N then lam (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0

theorem gap_cast (lam : Ψ × Fin N → ℤ) (p : Ψ × Fin N) :
    gap (fun q => (lam q : ℝ)) p = (gapZ lam p : ℝ) := by
  unfold gap gapX gapZ
  split_ifs <;> simp

theorem formPoly_eq_toWt [Fintype Ψ] (n : ℕ) (ax ay : (Fin n → Ψ × Fin N) → ℝ)
    (h : ∀ lam : Ψ × Fin N → ℤ, ∑ w, (∏ r, (lam (w r) : ℝ)) * ax w = ∑ w, (∏ r, (gapZ lam (w r) : ℝ)) * ay w) :
    formPoly n ax = toWt (formPoly n ay) := by
  refine MvPolynomial.funext_set (fun _ => Set.range (fun z : ℤ => (z : ℝ)))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective) ?_
  intro x hx
  choose lam hlam using fun i => hx i (Set.mem_univ i)
  have hxl : x = fun p => (lam p : ℝ) := funext fun p => (hlam p).symm
  rw [hxl, eval_toWt_gap, (formPoly_isHomogeneous_and_eval _ n ax).2, (formPoly_isHomogeneous_and_eval _ n ay).2]
  simp only [gap_cast]
  simpa only [mul_comm] using h lam

end Wt

section Flag

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def yDeg (p : Ψ × Fin N) : FlBlock Ψ N → ℤ :=
  fun q => if q.1 = p.1 ∧ (q.2 : ℕ) = p.2 then 1 else 0

variable {Ψ N}

theorem deg_abel (lam : Ψ × Fin N → ℤ) (q : FlBlock Ψ N) :
    ∑ p, lam p * xDeg Ψ N p q = ∑ p, gapZ lam p * yDeg Ψ N p q := by
  classical
  obtain ⟨τ, i⟩ := q
  have hi : (i : ℕ) + 1 < N := by have := i.2; omega
  have hi0 : (i : ℕ) < N := by omega
  have hx : ∀ p : Ψ × Fin N, xDeg Ψ N p (τ, i) =
      (if p = (τ, ⟨(i : ℕ), hi0⟩) then 1 else 0) - (if p = (τ, ⟨(i : ℕ) + 1, hi⟩) then 1 else 0) := by
    rintro ⟨τ', a⟩
    by_cases ht : τ = τ'
    · subst ht
      simp [xDeg, Fin.ext_iff, eq_comm]
    · simp [xDeg, ht, Ne.symm ht]
  have hy : ∀ p : Ψ × Fin N, yDeg Ψ N p (τ, i) = if p = (τ, ⟨(i : ℕ), hi0⟩) then 1 else 0 := by
    rintro ⟨τ', a⟩
    by_cases ht : τ = τ'
    · subst ht
      simp [yDeg, Fin.ext_iff, eq_comm]
    · simp [yDeg, ht, Ne.symm ht]
  simp only [hx, hy, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp [gapZ, hi]

theorem deg_abel_smul (lam : Ψ × Fin N → ℤ) :
    ∑ p, lam p • xDeg Ψ N p = ∑ p, gapZ lam p • yDeg Ψ N p := by
  funext q
  simpa [Finset.sum_apply] using deg_abel lam q

end Flag

end FlLines

open FlLines

theorem flLines_polys : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) → hFlPoly Ψ N II = toWt (formPoly (antisymDegree Ψ N + 1) fun w => II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1) fun r => yLineFl Ψ N (w r)) ∧ degFlPoly Ψ N = toWt (formPoly (antisymDegree Ψ N) fun w => ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) fun _ => 1) := by
  intro hIn II hII Ψ _ _ _ N _ hP
  have hI := hII.1 (FlBlock Ψ N) (FlIdx Ψ N)
  refine ⟨formPoly_eq_toWt _ _ _ fun lam => ?_, formPoly_eq_toWt _ _ _ fun lam => ?_⟩
  · have h1 := FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ => lam) (xDeg Ψ N)
    have h2 := FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ => gapZ lam) (yDeg Ψ N)
    rw [deg_abel_smul lam, h2] at h1
    exact h1.symm
  · set S : Set (Ideal (MRing (FlIdx Ψ N))) := divSupp (PFl Ψ N) (C (((2 : ℕ) : ℤ))) with hSdef
    have hS : S.Finite := divSupp_finite _ _
    set m : Ideal (MRing (FlIdx Ψ N)) → ℝ :=
      fun V => (multAt (PFl Ψ N ⊔ Ideal.span {C (((2 : ℕ) : ℤ))}) V : ℝ) with hm
    have hD : ∀ L : Fin (antisymDegree Ψ N) → HermLine (FlIdx Ψ N), (∀ j, IsSmoothHerm (L j)) →
        ptsIntegral (PFl Ψ N) (pot L) (fun _ => 1) = ∑ᶠ V ∈ S, m V * (geoNum _ V (fun j => (L j).a) : ℝ) :=
      fun L hL => hIn.degree _ _ _ _ L 2 hP hL Nat.prime_two
    have hsm : ∀ a : FlBlock Ψ N → ℤ, IsSmoothHerm (fsHerm (FlIdx Ψ N) a) :=
      FlagHeightMultilinear.isSmoothHerm_fsHerm
    have h1 := degSum_polar (antisymDegree Ψ N) S hS m lam (xDeg Ψ N)
    have h2 := degSum_polar (antisymDegree Ψ N) S hS m (gapZ lam) (yDeg Ψ N)
    have hv : (fun (_ : Fin (antisymDegree Ψ N)) k => ∑ a, lam a * xDeg Ψ N a k) =
        fun _ k => ∑ a, gapZ lam a * yDeg Ψ N a k := by
      funext _ k
      exact deg_abel lam k
    rw [hv, ← h2] at h1
    have ex : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
        ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) (fun _ => 1) =
          ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => xDeg Ψ N (w r)) : ℝ) :=
      fun w => hD _ fun _ => hsm _
    have ey : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
        ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) (fun _ => 1) =
          ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => yDeg Ψ N (w r)) : ℝ) :=
      fun w => hD _ fun _ => hsm _
    simp only [ex, ey]
    exact h1

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagAlgebraicallyIndependent
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem IsGenericFlag.indep_twist_mul_genUp : ∀ (Ω Φ : Type) [Field Ω] [Field Φ] [Algebra Ω Φ] (Ψ : Type) (N j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) Φ) (T : Ψ → Matrix (Fin N) (Fin N) Ω), (∀ τ, IsBlockDiag j (g τ)) → IsGenericFlag Ω j g → (∀ τ, IsBlockDiag j (T τ) ∧ (T τ).det ≠ 0) → AlgebraicIndependent Ω (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ))) * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2) := by
  intro Ω Φ _ _ _ Ψ N j g T hg hgen hT
  have hTu : ∀ τ, IsUnit (T τ).det := fun τ => isUnit_iff_ne_zero.mpr (hT τ).2
  have hM : ∀ τ, IsBlockDiag j ((g τ).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j τ) :=
    fun τ => IsBlockDiag.mul (IsBlockDiag.map (hg τ) (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ))
      (genUp_blockDiag (R := Φ) τ)
  have key : ∀ (R : Type) [CommRing R] [Algebra Ω R] (f : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] R)
      (Z : Ψ → Matrix (Fin N) (Fin N) R), (∀ τ, IsBlockDiag j (Z τ)) →
      (∀ q : inertBlockIndex Ψ N j, f (X q) = Z q.1.1 q.1.2.1 q.1.2.2) →
      ∀ τ c b, f (genericBlockMatrix Ω N j τ c b) = Z τ c b := by
    intro R _ _ f Z hZ hf τ c b
    exact congrFun (congrFun (generic_block_matrix_map f.toRingHom hZ hf τ) c) b
  have hlin : ∀ (R : Type) [CommRing R] [Algebra Ω R] (f : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] R)
      (U : Matrix (Fin N) (Fin N) Ω) (G : Matrix (Fin N) (Fin N) (MvPolynomial (inertBlockIndex Ψ N j) Ω)) (a b : Fin N),
      f ((U.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * G) a b)
        = (U.map (algebraMap Ω R) * G.map f) a b := by
    intro R _ _ f U G a b
    simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  obtain ⟨φ, hφ⟩ : ∃ φ : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] MvPolynomial (inertBlockIndex Ψ N j) Ω,
      ∀ q : inertBlockIndex Ψ N j, φ (X q) = ((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2 :=
    ⟨MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => ((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2), fun q => MvPolynomial.aeval_X _ q⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] MvPolynomial (inertBlockIndex Ψ N j) Ω,
      ∀ q : inertBlockIndex Ψ N j, ψ (X q) = ((T q.1.1).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2 :=
    ⟨MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => ((T q.1.1).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2), fun q => MvPolynomial.aeval_X _ q⟩
  have hZ : ∀ τ, IsBlockDiag j ((T τ).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * genericBlockMatrix Ω N j τ) :=
    fun τ => IsBlockDiag.mul (IsBlockDiag.map (hT τ).1 (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)))
      (generic_block_matrix_isBlockDiag (R := Ω) τ)
  have hψg := key _ ψ _ hZ hψ
  have hGψ : ∀ τ, (genericBlockMatrix Ω N j τ).map ψ
      = (T τ).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * genericBlockMatrix Ω N j τ :=
    fun τ => Matrix.ext fun c b => by rw [Matrix.map_apply]; exact hψg τ c b
  have hcomp : ∀ p, ψ (φ p) = p := by
    have hc : ψ.comp φ = AlgHom.id Ω _ := by
      apply MvPolynomial.algHom_ext
      intro q
      rw [AlgHom.comp_apply, AlgHom.id_apply, hφ, hlin _ ψ, hGψ, ← Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul _ (hTu _),
        show ((1 : Matrix (Fin N) (Fin N) Ω).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))) = 1 from
          (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)).mapMatrix.map_one,
        Matrix.one_mul, generic_block_matrix_apply]
    intro p
    exact DFunLike.congr_fun hc p
  have hx := IsGenericFlag.indep_mul_genUp hg hgen
  have hxg := key _ (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
      ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2)) _ hM
    (fun q => MvPolynomial.aeval_X _ q)
  have hGx : ∀ τ, (genericBlockMatrix Ω N j τ).map (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
      ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2))
      = (g τ).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j τ :=
    fun τ => Matrix.ext fun c b => by rw [Matrix.map_apply]; exact hxg τ c b
  have h1 : ∀ r, MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ)))
        * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2) r
      = MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
        ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2) (φ r) := by
    have hc : (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ)))
        * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2))
      = (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
        ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2)).comp φ := by
      apply MvPolynomial.algHom_ext
      intro q
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, hφ, hlin, hGx]
    intro r
    exact DFunLike.congr_fun hc r
  rw [algebraicIndependent_iff_injective_aeval] at hx ⊢
  intro p p' hpp
  have h2 : φ p = φ p' := hx (by rw [← h1, ← h1]; exact hpp)
  calc p = ψ (φ p) := (hcomp p).symm
    _ = ψ (φ p') := by rw [h2]
    _ = p' := hcomp p'

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GlobalRegularizationStatementHolds
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem regGlobalStatement_holds : RegGlobalStatement := by
  intro e X _ _ _ A B Θ L s n m W hΘ hΘpos hL hS hSNC hs hAd th ph C₅ hSW hGB
  obtain ⟨B', x, hAd', hGB', hsrc⟩ := GlobalTheory.T.refine_adapted_atlas_with_gradient A B L th s ph C₅ hs hAd hGB
  obtain ⟨hAB, h2, hcov, M, hM⟩ := hAd'
  choose S mm hm1 hbd hrl using hM
  have hcl : IsClosed (bdry s) := LeviFormBoundaryTopology.isClosed_bdry hS
  obtain ⟨hth, hphs, hpsh, hb⟩ := hSW
  obtain ⟨C₅', hC₅'0, hconv⟩ := GlobalTheory.T.log_bound_transfer_between_radii C₅ M
  obtain ⟨hlogd, hmono, hle, htend, hsmall, hmin⟩ := GlobalTheory.T.epsilon_schedule_properties
  have hrWge : ∀ y, Real.exp 1 ≤ rW L s y := rW_ge L s hs
  have h2le : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hball : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      z ∈ (B'.chart j).target ∧ (B'.chart j).symm z ∉ bdry s := by
    intro j z hz
    have hzt : z ∈ (B'.chart j).target := h2 j (ball_subset_closedBall hz.1)
    exact ⟨hzt, fun hzb => hz.2 ((hbd j z hzt).1 hzb)⟩
  have hq : ∀ j, ContDiffOn ℝ ∞ (fun z => th.φ (x j) ((B'.chart j).symm z)) (ball (0 : Fin e → ℂ) 2) :=
    fun j => (smoothOn_of_compatible hAB (th.isOpen_U (x j)) (hth.1 (x j)) j).mono fun z hz =>
      ⟨h2 j (ball_subset_closedBall hz),
        hsrc j ((B'.chart j).map_target (h2 j (ball_subset_closedBall hz)))⟩
  have hphj : ∀ j, ContDiffOn ℝ ∞ (ph ∘ (B'.chart j).symm)
      (ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j)) :=
    fun j => (smoothOn_of_compatible hAB hcl.isOpen_compl hphs j).mono fun z hz => hball j z hz
  have hlevi : ∀ j, ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j))
      (fun z => (fun z => th.φ (x j) ((B'.chart j).symm z)) z + (ph ∘ (B'.chart j).symm) z) := by
    intro j
    refine ⟨(((hq j).mono Set.diff_subset).add (hphj j)).of_le h2le, fun z hz w => ?_⟩
    exact GlobalTheory.T.levi_nonneg_in_chart_of_psh A B' th ph (bdry s)ᶜ (x j) j hAB hth hcl.isOpen_compl hphs hpsh (hsrc j) z (hball j z hz) w
  have hbnd : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      -C₅' * Real.log (rLoc (S j) (mm j) z) ≤ (ph ∘ (B'.chart j).symm) z ∧
        (ph ∘ (B'.chart j).symm) z ≤ C₅' := by
    intro j z hz
    obtain ⟨-, hzb⟩ := hball j z hz
    have hr := hrl j z (ball_subset_closedBall hz.1) hzb
    have hrl' := RegularChartScaling.rLoc_ge (S j) (mm j) (RegularChartScaling.norm_coord_le_of_ball le_rfl hz.1)
    exact (hconv _ _ (ph ((B'.chart j).symm z)) 0 (hrWge _) hrl' hr).1 (hb _ hzb).1 (hb _ hzb).2
  have hgrad : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      ‖fderiv ℝ (ph ∘ (B'.chart j).symm) z‖ ≤
        C₅' * rLoc (S j) (mm j) z ^ C₅' * Real.exp (rLoc (S j) (mm j) z / 2) := by
    intro j z hz
    have hz2 : z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j) :=
      ⟨ball_subset_ball (by norm_num) hz.1, hz.2⟩
    obtain ⟨-, hzb⟩ := hball j z hz2
    have hr := hrl j z (ball_subset_closedBall hz2.1) hzb
    have hrl' := RegularChartScaling.rLoc_ge (S j) (mm j) (RegularChartScaling.norm_coord_le_of_ball le_rfl hz2.1)
    exact (hconv _ _ 0 _ (hrWge _) hrl' hr).2 (hGB' j z hz.1 hzb)
  have hch := fun j => GlobalTheory.T.local_levi_psh_regularization e (S j) (mm j) (fun z => th.φ (x j) ((B'.chart j).symm z))
    (ph ∘ (B'.chart j).symm) C₅' M (hm1 j) (hq j) (hphj j) (hlevi j) (hbnd j) (hgrad j)
  choose Cj tj g hCj1 htj0 htje hgt hgC2 using hch

  obtain ⟨C', t', ht'0, hcmp⟩ := GlobalTheory.T.glued_local_regularizations_on_atlas A B' L th s ph C₅ M x S mm hAB h2 hsrc hs hcl hbd hrl
    ⟨hth, hphs, hpsh, hb⟩
  set Cm : ℝ := 1 + ∑ j, |Cj j| with hCmdef
  have hCm : ∀ j, Cj j ≤ Cm := fun j => by
    have h1 := Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h2' := le_abs_self (Cj j)
    linarith
  have hCm1 : 1 ≤ Cm := by
    have : 0 ≤ ∑ j, |Cj j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  set Cl : ℝ := |C'| + Cm with hCldef
  have hCl1 : 1 ≤ Cl := by have := abs_nonneg C'; linarith
  have hClj : ∀ j, Cj j ≤ Cl := fun j => by have := abs_nonneg C'; linarith [hCm j]
  obtain ⟨a, ha0, ha⟩ := hsmall Cl
  obtain ⟨tm, htm0, htm⟩ := hmin B'.n tj htj0
  set t₀ : ℝ := min (min tm t') (min a (Real.exp (-Real.exp 1))) with ht₀def
  have ht₀0 : 0 < t₀ := lt_min (lt_min htm0 ht'0) (lt_min ha0 (Real.exp_pos _))
  have ht₀j : ∀ j, t₀ ≤ tj j := fun j => ((min_le_left _ _).trans (min_le_left _ _)).trans (htm j)
  have ht₀' : t₀ ≤ t' := (min_le_left _ _).trans (min_le_right _ _)
  have ht₀a : t₀ ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have ht₀e : t₀ ≤ Real.exp (-Real.exp 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hLL : ∀ t, 0 < t → t ≤ t₀ → 0 ≤ Real.log (Real.log (1 / t)) := fun t ht htt => by
    have := (log_inv_bounds ht (htt.trans ht₀e)).2; linarith

  have hy54 : ∀ j, ∀ y ∈ chartBall B' j (5 / 4), B'.chart j y ∈ ball (0 : Fin e → ℂ) (5 / 4) ∧
      B'.chart j y ∈ closedBall (0 : Fin e → ℂ) 2 ∧ (B'.chart j).symm (B'.chart j y) = y := by
    intro j y hy
    exact ⟨hy.2, ball_subset_closedBall (ball_subset_ball (by norm_num) hy.2), (B'.chart j).left_inv hy.1⟩
  have hsand : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      polyMaxOff (S j) (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z))
          (B'.chart j y) t - epsT (Cj j) t ≤ th.φ (x j) y + g j t (B'.chart j y) ∧
        th.φ (x j) y + g j t (B'.chart j y) ≤ polyMaxOff (S j)
          (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z)) (B'.chart j y) t := by
    intro t ht htt j y hy
    obtain ⟨hz, -, hsy⟩ := hy54 j y hy
    have h := ((hgt j t ht (htt.trans (ht₀j j))).2.2.2.2.1 (B'.chart j y) hz)
    have h' : polyMaxOff (S j) (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z))
          (B'.chart j y) t - epsT (Cj j) t ≤ th.φ (x j) ((B'.chart j).symm (B'.chart j y)) + g j t (B'.chart j y) ∧
        th.φ (x j) ((B'.chart j).symm (B'.chart j y)) + g j t (B'.chart j y) ≤ polyMaxOff (S j)
          (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z)) (B'.chart j y) t := h
    rw [hsy] at h'
    exact h'
  have hloc : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      (g j t ∘ B'.chart j) y ≤ Cl ∧ -Cl * Real.log (Real.log (1 / t)) ≤ (g j t ∘ B'.chart j) y ∧
        (y ∉ bdry s → ph y ≤ (g j t ∘ B'.chart j) y ∧
          (rW L s y ≤ Real.log (1 / t) → (g j t ∘ B'.chart j) y ≤ ph y + t ^ ((1 : ℝ) / 3))) := by
    intro t ht htt j y hy
    obtain ⟨hz, hz2, hsy⟩ := hy54 j y hy
    obtain ⟨-, -, hgb, hgn, -, -⟩ := hgt j t ht (htt.trans (ht₀j j))
    obtain ⟨hb1, hb2⟩ := hgb _ hz
    have hll := hLL t ht htt
    refine ⟨hb1.trans (hClj j), le_trans ?_ hb2, fun hyb => ?_⟩
    · have := mul_le_mul_of_nonneg_right (hClj j) hll
      show -Cl * _ ≤ -Cj j * _
      linarith
    · have hzt : B'.chart j y ∈ (B'.chart j).target := h2 j hz2
      have hzc : B'.chart j y ∉ ReciprocityTheory.AnForm.A.coordDiv (S j) := fun hc =>
        hyb (hsy ▸ (hbd j _ hzt).2 hc)
      obtain ⟨hn1, hn2⟩ := hgn _ ⟨hz, hzc⟩
      have hr := hrl j _ hz2 (by rw [hsy]; exact hyb)
      rw [hsy] at hr
      simp only [Function.comp_apply, hsy] at hn1 hn2 ⊢
      refine ⟨hn1, fun hrw => hn2 ?_⟩
      have := (abs_le.1 hr).1
      linarith
  have hmono' : ∀ t t', 0 < t → t ≤ t' → t' ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      (g j t ∘ B'.chart j) y ≤ (g j t' ∘ B'.chart j) y + epsT Cl t' := by
    intro t t'' ht htt' ht'' j y hy
    obtain ⟨hz, -, -⟩ := hy54 j y hy
    have h := (hgt j t ht ((htt'.trans ht'').trans (ht₀j j))).2.2.2.2.2 t'' htt' (ht''.trans (ht₀j j)) _ hz
    have := epsT_le_epsT (hClj j) (ht.trans_le htt') (ht''.trans ht₀e)
    simp only [Function.comp_apply]
    linarith

  obtain ⟨K, hK0, hgl⟩ := GlobalTheory.T.regularization_glue_C2_explicit A B' Θ th s ph hAB hcov h2 hΘ hΘpos hth hcl hphs
  have hback : ∀ t, 0 < t → t ≤ t₀ → ∀ j, A.SmoothOn (chartBall B' j (5 / 4)) (g j t ∘ B'.chart j) ∧
      IsPshOn A (chartBall B' j (5 / 4)) (th + LocPot.ofFun (g j t ∘ B'.chart j)) := by
    intro t ht htt j
    obtain ⟨hgs, hglevi, -⟩ := hgt j t ht (htt.trans (ht₀j j))
    exact GlobalTheory.T.smoothOn_of_chart_levi_nonneg A B' th (x j) j (ball (0 : Fin e → ℂ) (5 / 4)) (g j t) hAB hth (hsrc j) isOpen_ball
      (fun z hz => h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) hz))) hgs hglevi.2
  have hov : ∀ t, 0 < t → t ≤ t₀ → ∀ j k, ∀ y ∈ chartBall B' j (5 / 4) ∩ chartBall B' k (5 / 4),
      |(g j t ∘ B'.chart j) y - (g k t ∘ B'.chart k) y| ≤ epsT Cl t := by
    intro t ht htt j k y hy
    obtain ⟨sj1, sj2⟩ := hsand t ht htt j y hy.1
    obtain ⟨sk1, sk2⟩ := hsand t ht htt k y hy.2
    have hc := abs_le.1 (hcmp t ht (htt.trans ht₀') j k y hy)
    have hte := htt.trans ht₀e
    have e1 := epsT_le_epsT (hCm j) ht hte
    have e2 := epsT_le_epsT (hCm k) ht hte
    have e3 := epsT_le_epsT (le_abs_self C') ht hte
    have e4 : epsT Cl t = epsT |C'| t + epsT Cm t := by
      simp only [hCldef, epsT]; ring
    simp only [Function.comp_apply]
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2]
  obtain ⟨F, hF, hFC2⟩ := hgl t₀ (epsT Cl) (fun t j => g j t ∘ B'.chart j) ht₀0 (htend Cl)
    (fun t ht htt => ⟨hle Cl t hCl1 ht (htt.trans ht₀e), ha t ht (htt.trans ht₀a),
      fun j => (hback t ht htt j).1,
      ⟨Cl + Cl * Real.log (Real.log (1 / t)), fun j y hy => by
        obtain ⟨h1, h2', -⟩ := hloc t ht htt j y hy
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ Cl) (hLL t ht htt)
        rw [abs_le]; constructor <;> linarith⟩,
      fun j => (hback t ht htt j).2, hov t ht htt⟩)
    (fun j K' hK' hK'c => by
      have hsub : K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv (S j) := by
        intro z hz
        have hzt : z ∈ (B'.chart j).target :=
          h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) (hK' hz).1))
        exact ⟨(hK' hz).1, fun hc => (hK' hz).2 ((hbd j z hzt).2 hc)⟩
      exact GlobalTheory.T.C2_tendsto_pullback_through_chart (B'.chart j) (g j) (ph ∘ (B'.chart j).symm) K'
        (fun z hz => h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) (hK' hz).1)))
        (hgC2 j K' hsub hK'c))
  obtain ⟨C, hC⟩ := GlobalTheory.T.regularization_glue_bounds A B' Θ L th s ph C₅ K Cl t₀ (fun t j => g j t ∘ B'.chart j) F hΘ hΘpos hth hs hcov
    (fun y hy => (hb y hy).1) hK0 hCl1 ht₀0 ht₀e hF hloc hmono'
  exact ⟨C, t₀, F, hC, hFC2⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeBoundedMap
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.MapCompare

theorem main : ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ), Function.Injective φ → 0 < c → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) → (∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c) ∧ E.slopeMax ≤ E'.slopeMax + ((Real.log c / 2 : ℝ) : EReal) :=
  CoverDenseAlt.normDegree_le_of_metric_bounded_map

end GlobalTheory.CompanionTheory.Ar.MapCompare
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralConjLineEqStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptsIntegral_conjLine_eq : PtsIndepStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn Q A s → ptsIntegral Q (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) = ptsIntegral Q (pot L) (logNorm A s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.ptsIntegral_conjLine | exact GlobalTheory.CompanionTheory.Ar.Tw.ptsIntegral_conjLine | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.ptsIntegral_conjLine <;> assumption)
end

