import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySymm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergySymmetry

theorem cxHessian_sub {D : ℕ} {f g : (Fin D → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (y : Fin D → ℂ) : cxHessian (fun y' => f y' - g y') y = cxHessian f y - cxHessian g y := by
  have h1 : fderiv ℝ (fun y' => f y' - g y') = fun z => fderiv ℝ f z - fderiv ℝ g z := by
    funext z
    exact fderiv_sub (hf.differentiable (by norm_num) z) (hg.differentiable (by norm_num) z)
  have hf' : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg' : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun y' => f y' - g y')) y =
      fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ g) y := by
    rw [h1]
    exact fderiv_sub (hf' y) (hg' y)
  ext i j
  simp only [cxHessian, h2, _root_.sub_apply, Matrix.sub_apply]
  push_cast
  ring

theorem mixedDisc_update_sub {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (X - Y)) =
      mixedDisc (Function.update A k X) - mixedDisc (Function.update A k Y) := by
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  have e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C := fun C => by
    rw [MultilinearMap.toLinearMap_apply, hM]
    rfl
  simp only [e, map_sub]

theorem maDensity_update_sub {D : ℕ} (Φ : Fin D → (Fin D → ℂ) → ℝ) (p : Fin D) {f g : (Fin D → ℂ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (y : Fin D → ℂ) :
    maDensity (Function.update Φ p f) y - maDensity (Function.update Φ p g) y =
      maDensity (Function.update Φ p fun y' => f y' - g y') y := by
  have key : ∀ h : (Fin D → ℂ) → ℝ, (fun k => cxHessian (Function.update Φ p h k) y) =
      Function.update (fun k => cxHessian (Φ k) y) p (cxHessian h y) := fun h => by
    funext k
    exact Function.apply_update (fun _ h' => cxHessian h' y) Φ p h k
  simp only [maDensity, key, cxHessian_sub hf hg y, mixedDisc_update_sub, Complex.sub_re]
  ring

theorem update_comp_swap {α : Type*} {n : ℕ} (Φ : Fin (n + 1) → α) (p : Fin (n + 1)) (f : α) :
    Function.update Φ p f ∘ Equiv.swap 0 p = Fin.cons f (fun i => Φ (Equiv.swap 0 p i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp only [Function.comp_apply, Fin.cons_succ]
    rw [Function.update_of_ne]
    intro h
    have h' := congrArg (Equiv.swap 0 p) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
    exact Fin.succ_ne_zero i h'

end ChartEnergySymmetry

open ChartEnergySymmetry in

theorem ChartEnergySymm.proof (hI : ChartIbpSymm.Statement) : ChartEnergySymm.Statement := by
  intro e A B C D T p hA hB hC hD hT
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by have := p.pos; omega⟩
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p with hσ
  set T' : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ := fun i => T (σ i.succ) with hT'def
  have hT' : ∀ i, (T' i).PosDef := fun i => hT _
  have hpot : ∀ X, (fun j => hermChartPot (Function.update T p X j)) =
      Function.update (fun j => hermChartPot (T j)) p (hermChartPot X) := fun X => by
    funext j
    exact Function.apply_update (fun _ M => hermChartPot M) T p X j
  have hdiff : ∀ X Y : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ, X.PosDef → Y.PosDef → ∀ y,
      maDensity (fun j => hermChartPot (Function.update T p X j)) y -
          maDensity (fun j => hermChartPot (Function.update T p Y j)) y =
        maDensity (Fin.cons (fun y' => hermChartPot X y' - hermChartPot Y y')
          fun i => hermChartPot (T' i)) y := by
    intro X Y hX hY y
    rw [hpot, hpot, maDensity_update_sub _ _ (ChartEnergySwapHessian.contDiff_hermChartPot X hX)
      (ChartEnergySwapHessian.contDiff_hermChartPot Y hY), ← Inter.maDensity_comp_perm _ σ, update_comp_swap]
  simp_rw [hdiff C D hC hD, hdiff A B hA hB]
  exact hI n A B C D T' hA hB hC hD hT'

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLinesProj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace GrassmannianLinesProjective

def single (m : ℕ) (c : Fin (m + 1)) : PlIdx 1 m :=
  ⟨{Fin.cast (Nat.add_comm m 1) c}, Finset.card_singleton _⟩

theorem single_injective (m : ℕ) : Function.Injective (single m) := by
  intro c c' h
  have := congrArg Subtype.val h
  simpa [single] using this

theorem single_surjective (m : ℕ) : Function.Surjective (single m) := by
  rintro ⟨I, hI⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hI
  exact ⟨Fin.cast (Nat.add_comm 1 m) a, Subtype.ext (by simp [single])⟩

def blk : Unit → Fin 1 := fun _ => 0

def coordMap (m : ℕ) : (Σ _ : Unit, Fin (m + 1)) → (Σ _ : Fin 1, PlIdx 1 m) :=
  fun p => ⟨0, single m p.2⟩

theorem coordMap_surjective (m : ℕ) : Function.Surjective (coordMap m) := by
  rintro ⟨k, I⟩
  obtain ⟨c, rfl⟩ := single_surjective m I
  refine ⟨⟨(), c⟩, ?_⟩
  rw [Subsingleton.elim k 0]
  rfl

theorem isBlockMap (m : ℕ) : IsBlockMap blk (coordMap m) := by
  refine ⟨fun _ _ _ => Subsingleton.elim _ _, ?_, fun _ => rfl, fun q _ => coordMap_surjective m q⟩
  rintro ⟨⟨⟩, c⟩ ⟨⟨⟩, c'⟩ h
  simp only [coordMap, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  rw [single_injective m h]

theorem card_plIdx (m : ℕ) : Fintype.card (PlIdx 1 m) = m + 1 := by
  rw [Fintype.card_subtype, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, Nat.choose_one_right, add_comm]

theorem ringKrullDim_mring {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ringKrullDim (MRing ι) = ((1 + Fintype.card (Σ k, ι k) : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField,
    Nat.card_eq_fintype_card]
  push_cast
  rfl

theorem grassIdeal_eq_bot (m : ℕ) : grassIdeal 1 1 m = ⊥ := by
  have hA := GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 m le_rfl
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hle := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (grassIdeal 1 1 m))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hx0) (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  rw [hA.2.2.2, ringKrullDim_mring, Fintype.card_sigma] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, card_plIdx, smul_eq_mul] at hle
  have h' : ((1 * 1 * m + 1 + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((1 + 1 * (m + 1) : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast hle
  have h'' : 1 * 1 * m + 1 + 1 + 1 ≤ 1 + 1 * (m + 1) := by exact_mod_cast h'
  omega

theorem isArithVar_bot (m : ℕ) : IsArithVar (⊥ : Ideal (MRing (PBlk (m + 1)))) (m + 1) := by
  refine ⟨⟨()⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ringKrullDim_mring]
    congr 1
    simp
    omega

theorem isPullHerm (m : ℕ) :
    IsPullHerm blk (coordMap m) (fsMulti (PBlk (m + 1))) (fsMulti (plBlocks 1 1 m)) := by
  refine ⟨?_, fun z => ?_⟩
  · funext k
    rw [Subsingleton.elim k (blk ())]
    show (1 : ℤ) = Function.extend blk (fun _ => (1 : ℤ)) 0 (blk ())
    exact (Function.Injective.extend_apply (f := blk) (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ => (1 : ℤ)) (0 : Fin 1 → ℤ) ()).symm
  · simp only [fsMulti, HermLine.ofMetrics, fsMetric, Fintype.prod_unique, zpow_one, coordMap]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact ((Equiv.ofBijective _ ⟨single_injective m, single_surjective m⟩).sum_comp
      (fun i => ‖z ⟨0, i⟩‖ ^ 2)).symm

theorem blockFnField_le (m : ℕ) :
    blockFnField (grassCoord 1 1 m) ≤ blockFnField (grassCoord 1 1 m ∘ coordMap m) := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro t ⟨p, q, -, rfl⟩
  obtain ⟨p', rfl⟩ := coordMap_surjective m p
  obtain ⟨q', rfl⟩ := coordMap_surjective m q
  exact IntermediateField.subset_adjoin _ _ ⟨p', q', Subsingleton.elim _ _, rfl⟩

end GrassmannianLinesProjective

open GrassmannianLinesProjective in

theorem GrassLinesProj.proof (hPF : PFCoordStatement) : GrassLinesProj.Statement := by
  intro m II hII
  have hd : 1 * 1 * m + 1 = m + 1 := by ring
  have hA : IsArithVar (grassIdeal 1 1 m) (m + 1) := by
    rw [← hd]
    exact GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 m le_rfl
  have himg : imageZ (coordMap m) (grassIdeal 1 1 m) = ⊥ := by
    rw [grassIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (rename_injective _ (isBlockMap m).2.1)
  have hB : IsArithVar (imageZ (coordMap m) (grassIdeal 1 1 m)) (m + 1) := by
    rw [himg]
    exact isArithVar_bot m
  have h := hPF II hII Unit (PBlk (m + 1)) (Fin 1) (plBlocks 1 1 m) blk (coordMap m) (GrassField 1 1 m)
    (grassCoord 1 1 m) (m + 1) (fun _ => fsMulti (PBlk (m + 1))) (fun _ => fsMulti (plBlocks 1 1 m))
    (isBlockMap m) hA hB (fun _ => FsLineSmooth.proof _ _) (fun _ => isPullHerm m)
  rw [IntermediateField.relfinrank_eq_one_iff.mpr (blockFnField_le m),
    show mCoordIdeal (grassCoord 1 1 m) = grassIdeal 1 1 m from rfl, himg, Nat.cast_one, one_mul] at h
  rw [hd]
  exact h

example : IsBlockMap GrassmannianLinesProjective.blk (GrassmannianLinesProjective.coordMap 1) :=
  GrassmannianLinesProjective.isBlockMap 1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def stackedBase {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) : Ideal (MRing (stackedBlocks T)) :=
  stackedGraph b' a ⊔ Ideal.span (Set.range fun t => C (a t) * graphFirst t)

def IsStackedExc {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (E : Ideal (MRing (stackedBlocks T))) :
    Prop :=
  E ∈ (stackedBase b' a).minimalPrimes ∧ IsRelevant E

def DualStackedExcCycle.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∃ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E ∧ ¬ IsHorizontal E ∧
      ∀ t : T,
        ((divCycle (stackedGraph b' a) (C (a t) * graphFirst t) E : ℤ) =
            divCycle (stackedGraph b' a) (graphSecond t) E + 1) ∧
        ∀ W : Ideal (MRing (stackedBlocks T)), ¬ IsHorizontal W → W ≠ E →
          divCycle (stackedGraph b' a) (C (a t) * graphFirst t) W = divCycle (stackedGraph b' a) (graphSecond t) W

def DualStackedExcGeoSecond.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      (geoNum (i - 1) E (fun _ => degSecond) : ℝ) * Real.log (charOf E) =
        Real.log (F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup)

def DualStackedExcGeoFirst.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      ∀ d : Fin (i - 1) → Unit ⊕ Unit → ℤ, (∀ j, d j = degFirst ∨ d j = degSecond) → (∃ j, d j = degFirst) →
        geoNum (i - 1) E d = 0

namespace DualStackedExcExample

open DualTopSimpleSubExample

theorem dualIdeal_eq_bot {F : HermLattice ℚ 1} {T : Type} [Fintype T] [Subsingleton T] (t₀ : T)
    (b : Module.Basis T ℤ (dualLattice F)) : dualIdeal b = ⊥ := by
  set c : ℚ := (b t₀ : Fin 1 → ℚ) 0 with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply b.ne_zero t₀
    apply Subtype.ext
    funext j
    fin_cases j
    simpa using h0
  let φ : MRing (dualBlocks T) →ₐ[ℤ] MvPolynomial (Fin 1) ℚ := aeval fun _ => C c * X 0
  let ψ : MvPolynomial (Fin 1) ℚ →ₐ[ℚ] MvPolynomial (Fin 1) ℚ := aeval fun _ => C c⁻¹ * X 0
  have hcomp : ψ.toRingHom.comp φ.toRingHom =
      (map (Int.castRingHom ℚ)).comp (rename fun _ : (Σ _ : Unit, T) => (0 : Fin 1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · intro p
      simp only [AlgHom.toRingHom_eq_coe, RingHom.comp_apply, AlgHom.coe_toRingHom, φ, ψ, aeval_X, map_mul,
        aeval_C, rename_X, map_X, MvPolynomial.algebraMap_eq]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, one_mul]
  have hinj : Function.Injective φ := by
    have h2 : Function.Injective
        ((map (Int.castRingHom ℚ)).comp (rename fun _ : (Σ _ : Unit, T) => (0 : Fin 1)).toRingHom) :=
      (map_injective _ Int.cast_injective).comp (rename_injective _ fun x y _ => by
        obtain ⟨⟨⟩, s⟩ := x
        obtain ⟨⟨⟩, s'⟩ := y
        rw [Subsingleton.elim s s'])
    rw [← hcomp, RingHom.coe_comp] at h2
    exact Function.Injective.of_comp h2
  have hev : ∀ f : MRing (dualBlocks T),
      MvPolynomial.eval (fun _ : Unit => (1 : ProjField ℚ 1)) (mConeMap (dualLatticeCoord b) f) =
        algebraMap (MvPolynomial (Fin 1) ℚ) (ProjField ℚ 1) (φ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C n => simp [mConeMap, φ]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p q hp =>
      have hq : q.2 = t₀ := Subsingleton.elim _ _
      simp only [map_mul, hp]
      congr 1
      simp [mConeMap, φ, dualLatticeCoord, hq, hc]
  rw [dualIdeal, mCoordIdeal, eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  apply hinj
  rw [map_zero]
  apply IsFractionRing.injective (MvPolynomial (Fin 1) ℚ) (ProjField ℚ 1)
  rw [map_zero, ← hev, RingHom.mem_ker.mp hf, map_zero]

theorem graphIdeal_bot {T : Type} [Fintype T] [DecidableEq T] [Subsingleton T] (t₀ : T) (a : T → ℤ)
    (ha : a t₀ ≠ 0) :
    graphIdeal (⊥ : Ideal (MRing (dualBlocks T))) (linForm (stackedDiag a)) = ⊥ := by
  set u : MRing (stackedBlocks T) := C (a t₀) * graphFirst t₀ with hu_def
  have hu : u ≠ 0 := mul_ne_zero (fun h => ha (C_eq_zero.mp h)) (X_ne_zero _)
  let θ : MRing (dualBlocks T) ⧸ (⊥ : Ideal (MRing (dualBlocks T))) →+* Localization.Away u :=
    (algebraMap (MRing (stackedBlocks T)) (Localization.Away u)).comp
      (Ideal.Quotient.lift ⊥ (rename fun p : (Σ _ : Unit, T) => (⟨Sum.inl (), p.2⟩ : Σ k, stackedBlocks T k)).toRingHom
        fun f hf => by rw [Submodule.mem_bot] at hf; rw [hf, map_zero])
  let ρ : MvPolynomial Unit (MRing (dualBlocks T) ⧸ (⊥ : Ideal (MRing (dualBlocks T)))) →+*
      Localization.Away u :=
    eval₂Hom θ fun _ => algebraMap _ _ (graphSecond t₀) * IsLocalization.Away.invSelf u
  have hρ : ρ.comp (graphMap ⊥ (linForm (stackedDiag a))) =
      algebraMap (MRing (stackedBlocks T)) (Localization.Away u) := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · rintro ⟨(u | u), t⟩ <;> obtain ⟨⟩ := u
      · simp [ρ, θ, graphMap]
      · obtain rfl : t₀ = t := Subsingleton.elim (α := T) _ _
        have hg : linForm (ι := dualBlocks T) (ι₂ := dualBlocks T) (stackedDiag a) ⟨(), t₀⟩ =
            C (a t₀) * X ⟨(), t₀⟩ := by
          simp [linForm, stackedDiag, apply_ite C, ite_mul, Finset.sum_ite_eq]
        have h1 : graphMap ⊥ (linForm (stackedDiag a)) (X ⟨Sum.inr (), t₀⟩) =
            C (Ideal.Quotient.mk ⊥ (C (a t₀) * X ⟨(), t₀⟩)) * X () := by
          simp [graphMap, hg]
        have h2 : ρ (C (Ideal.Quotient.mk ⊥ (C (a t₀) * X ⟨(), t₀⟩))) =
            algebraMap (MRing (stackedBlocks T)) (Localization.Away u) u := by
          simp only [ρ, θ, coe_eval₂Hom, eval₂_C, RingHom.comp_apply, Ideal.Quotient.lift_mk,
            AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, rename_C, rename_X]
          rw [← map_mul]
          rfl
        have h3 : ρ (X ()) = algebraMap (MRing (stackedBlocks T)) (Localization.Away u) (graphSecond t₀) *
            IsLocalization.Away.invSelf u := by
          simp [ρ]
        rw [RingHom.comp_apply, h1, map_mul, h2, h3, mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]
        rfl
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  have h0 : algebraMap (MRing (stackedBlocks T)) (Localization.Away u) f = 0 := by
    rw [← hρ, RingHom.comp_apply, RingHom.mem_ker.mp hf, map_zero]
  exact IsLocalization.injective (Localization.Away u) (powers_le_nonZeroDivisors_of_noZeroDivisors hu)
    (h0.trans (map_zero _).symm)

theorem isStackedExc_reduction {T : Type} [Fintype T] [DecidableEq T] [Subsingleton T] (t₀ : T)
    {F' : HermLattice ℚ 1} (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (ha : a t₀ ≠ 0) (q : ℕ)
    [Fact q.Prime] (hdvd : (q : ℤ) ∣ a t₀) :
    IsStackedExc b' a (RingHom.ker (MvPolynomial.map (Int.castRingHom (ZMod q)) :
      MRing (stackedBlocks T) →+* MvPolynomial (Σ k, stackedBlocks T k) (ZMod q))) := by
  set E := RingHom.ker (MvPolynomial.map (Int.castRingHom (ZMod q)) :
      MRing (stackedBlocks T) →+* MvPolynomial (Σ k, stackedBlocks T k) (ZMod q)) with hE_def
  have hΓ : stackedGraph b' a = ⊥ := by
    rw [stackedGraph, dualIdeal_eq_bot t₀ b']
    exact graphIdeal_bot t₀ a ha
  have hX : ∀ p, (X p : MRing (stackedBlocks T)) ∉ E := fun p h =>
    X_ne_zero (R := ZMod q) p (by simp only [hE_def, RingHom.mem_ker, map_X] at h; exact h)
  have hEprime : E.IsPrime := RingHom.ker_isPrime _
  have hbase : stackedBase b' a ≤ E := by
    rw [stackedBase, hΓ, bot_sup_eq, Ideal.span_le]
    rintro _ ⟨t, rfl⟩
    obtain rfl : t = t₀ := Subsingleton.elim _ _
    show _ ∈ RingHom.ker _
    have h0 : (Int.castRingHom (ZMod q)) (a t) = 0 := by
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    rw [RingHom.mem_ker, map_mul, map_C, h0, C_0, zero_mul]
  refine ⟨⟨⟨hEprime, hbase⟩, fun Q ⟨hQ, hQb⟩ hQE => ?_⟩, fun k => ?_⟩
  · have hu : C (a t₀) * graphFirst t₀ ∈ Q :=
      hQb (Ideal.mem_sup_right (Ideal.subset_span ⟨t₀, rfl⟩))
    have hCa : (C (a t₀) : MRing (stackedBlocks T)) ∈ Q :=
      (hQ.mem_or_mem hu).resolve_right fun h => hX _ (hQE h)
    have hcomQ : (Q.comap (C : ℤ →+* MRing (stackedBlocks T))).IsMaximal := by
      refine Ideal.IsPrime.isMaximal (Ideal.IsPrime.comap _) fun hb => ha ?_
      have h1 : a t₀ ∈ Q.comap (C : ℤ →+* MRing (stackedBlocks T)) := hCa
      rw [hb] at h1
      exact h1
    have hne : E.comap (C : ℤ →+* MRing (stackedBlocks T)) ≠ ⊤ := fun h => by
      have h1 : (1 : ℤ) ∈ E.comap (C : ℤ →+* MRing (stackedBlocks T)) := h ▸ Submodule.mem_top
      exact hEprime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using h1))
    have hq : (q : ℤ) ∈ Q.comap (C : ℤ →+* MRing (stackedBlocks T)) := by
      rw [hcomQ.eq_of_le hne (Ideal.comap_mono hQE)]
      simp [hE_def, RingHom.mem_ker, Ideal.mem_comap]
    rw [hE_def, MvPolynomial.ker_map, Ideal.map_le_iff_le_comap, ZMod.ker_intCastRingHom, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hq
  · rcases k with ⟨⟩ | ⟨⟩
    · exact ⟨t₀, hX _⟩
    · exact ⟨t₀, hX _⟩

end DualStackedExcExample

end

end GroundTheory.Heights₂.Heights
end

