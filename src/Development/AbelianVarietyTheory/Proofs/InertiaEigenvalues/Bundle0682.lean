import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorForms
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.LieTensor

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in

theorem exists_curve {a : ℕ} (Z : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).val) (toL Z) 0 ∧
      (Z.conjTranspose = -Z → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) := by
  refine ⟨fun t => (Matrix.isUnit_exp (t • Z)).unit, Units.ext (by simp), ?_, fun hZ t => ?_⟩
  · open scoped Matrix.Norms.Operator in
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  · rw [IsUnit.unit_spec, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hZ, star_trivial, smul_neg,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem lie_skew_mem_span {N : ℕ} (ψ : Sm E N)
    (hψ : ψ ∈ finVec (cptRep E N)) (S : Matrix (Fin N) (Fin N) (Cinf E)) (hS : S.conjTranspose = -S) :
    lie E N (toL S) ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E N k ψ) := by
  obtain ⟨c, h0, hc, hu⟩ := exists_curve S
  set W := Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)
  have hf : FiniteDimensional ℂ W := hψ
  let W' : Submodule ℂ (GA E N → ℂ) := W.map (Sm E N).subtype
  have hcl : IsClosed (W' : Set (GA E N → ℂ)) := W'.closed_of_finiteDimensional
  let F : ℝ → GA E N → ℂ := fun t g => ψ.1 (g * infGL E N (c t))
  have hF : ∀ t, F t ∈ W' := fun t =>
    ⟨cptRep E N ⟨(c t).val, hu hS t⟩ ψ, Submodule.subset_span ⟨_, rfl⟩, funext fun g => by
      have : Unitary.toUnits (⟨(c t).val, hu hS t⟩ : Kinf E N) = c t := Units.ext rfl
      change ψ.1 (g * infGL E N (Unitary.toUnits _)) = _
      rw [this]⟩
  have hd : Filter.Tendsto (slope F 0) (nhdsWithin 0 {0}ᶜ) (nhds (lieD (toL S) ψ.1)) :=
    tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_curve ψ g c (toL S) h0 hc)
  have hm : lieD (toL S) ψ.1 ∈ W' := hcl.mem_of_tendsto hd (Filter.Eventually.of_forall fun t =>
    W'.smul_of_tower_mem _ (W'.sub_mem (hF t) (hF 0)))
  obtain ⟨w, hw, e⟩ := hm
  rwa [show lie E N (toL S) ψ = w from Subtype.ext e.symm]

theorem map_leviEmb {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) {c N : ℕ} {n : Fin c → ℕ}
    (e : (Σ i, Fin (n i)) ≃ Fin N) (x : ∀ i, GL (Fin (n i)) R) :
    Matrix.GeneralLinearGroup.map p (leviEmb R e x) = leviEmb S e fun i => Matrix.GeneralLinearGroup.map p (x i) := by
  ext a b
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective a
  obtain ⟨⟨j, b⟩, rfl⟩ := e.surjective b
  change p ((leviEmb R e x).val _ _) = _
  by_cases h : i = j
  · subst h
    rw [leviEmb_apply_same, leviEmb_apply_same]
    rfl
  · rw [leviEmb_apply_ne _ _ _ h, leviEmb_apply_ne _ _ _ h, map_zero]

theorem infGL_leviEmb {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N) (x : ∀ i, GL (Fin (n i)) (Cinf E)) :
    infGL E N (leviEmb (Cinf E) e x) = leviEmb (Ad E) e fun i => infGL E (n i) (x i) := by
  refine ga_ext ?_ ?_
  · simp only [map_leviEmb, pInf_infGL]
  · simp only [map_leviEmb, pFin_infGL]
    exact (map_one (leviEmb (Af E) e)).symm

theorem exists_deriv_tensorForms {c : ℕ} {n : Fin c → ℕ} (π : ∀ i, CuspSub E (n i))
    (γ : ∀ i, ℝ → GL (Fin (n i)) (Cinf E)) (Z : ∀ i, Lie E (n i)) (h0 : ∀ i, γ i 0 = 1)
    (hγ : ∀ i, HasDerivAt (fun t => toL (γ i t).val) (Z i) 0) {F : (∀ i, GA E (n i)) → ℂ} (hF : F ∈ tensorForms π) :
    ∃ G ∈ tensorForms π, ∀ m, HasDerivAt (fun t => F fun i => m i * infGL E (n i) (γ i t)) (G m) 0 := by
  classical
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ, rfl⟩ := hF
    refine ⟨∑ i, fun m => ∏ j, (Function.update φ i ⟨_, (π i).stable (.lie (Z i)) _ (φ i).2⟩ j).1.1 (m j),
      Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, rfl⟩, fun m => ?_⟩
    have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
      fun i _ => hasDerivAt_curve (φ i).1 (m i) (γ i) (Z i) (h0 i) (hγ i)
    refine h.congr_deriv (Eq.symm ?_)
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Function.update_self, smul_eq_mul]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), h0, map_one, mul_one]
  | zero => exact ⟨0, zero_mem _, fun m => hasDerivAt_const _ _⟩
  | add F F' _ _ hF hF' =>
    obtain ⟨G, hG, h⟩ := hF
    obtain ⟨G', hG', h'⟩ := hF'
    exact ⟨G + G', add_mem hG hG', fun m => (h m).add (h' m)⟩
  | smul z F _ hF =>
    obtain ⟨G, hG, h⟩ := hF
    exact ⟨z • G, Submodule.smul_mem _ z hG, fun m => (h m).const_mul z⟩

theorem lie_block_tensor {c N : ℕ} (n : Fin c → ℕ)
    (e : (Σ i, Fin (n i)) ≃ Fin N) (π : ∀ i, CuspSub E (n i)) (ψ : Sm E N)
    (hψ : (fun m => ψ.1 (leviEmb (Ad E) e m)) ∈ tensorForms π)
    (Z : ∀ i, Matrix (Fin (n i)) (Fin (n i)) (Cinf E)) :
    (fun m => (lie E N (toL (Matrix.reindex e e (Matrix.blockDiagonal' Z))) ψ).1 (leviEmb (Ad E) e m))
      ∈ tensorForms π := by
  choose γ h0 hγ _ using fun i => exists_curve (Z i)
  obtain ⟨G, hG, h⟩ := exists_deriv_tensorForms π γ (fun i => toL (Z i)) h0 hγ hψ
  have hc : HasDerivAt (fun t => toL (leviEmb (Cinf E) e fun i => γ i t).val)
      (toL (Matrix.reindex e e (Matrix.blockDiagonal' Z))) 0 := by
    refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
    obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective a
    obtain ⟨⟨j, b⟩, rfl⟩ := e.surjective b
    change HasDerivAt (fun t => (leviEmb (Cinf E) e fun i => γ i t).val (e ⟨i, a⟩) (e ⟨j, b⟩))
      (Matrix.reindex e e (Matrix.blockDiagonal' Z) (e ⟨i, a⟩) (e ⟨j, b⟩)) 0
    by_cases hij : i = j
    · subst hij
      simp only [leviEmb_apply_same, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.blockDiagonal'_apply_eq]
      exact hasDerivAt_pi.1 (hasDerivAt_pi.1 (hγ i) a) b
    · simp only [leviEmb_apply_ne _ _ _ hij, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.blockDiagonal'_apply_ne _ _ _ hij]
      exact hasDerivAt_const _ _
  convert hG using 1
  funext m
  have h1 := hasDerivAt_curve ψ (leviEmb (Ad E) e m) (fun t => leviEmb (Cinf E) e fun i => γ i t) _
    (by simp only [h0]; exact map_one _) hc
  refine h1.unique ?_
  simp only [infGL_leviEmb, ← map_mul]
  exact h m

omit [IsTotallyComplex E] in

theorem exists_decomp {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N)
    (Y : Matrix (Fin N) (Fin N) (Cinf E)) :
    ∃ (S : Matrix (Fin N) (Fin N) (Cinf E)) (Z : ∀ i, Matrix (Fin (n i)) (Fin (n i)) (Cinf E))
      (U : Matrix (Fin N) (Fin N) (Cinf E)),
      S.conjTranspose = -S ∧ (∀ p q, ¬ blk e p < blk e q → U p q = 0) ∧
      Y = S + Matrix.reindex e e (Matrix.blockDiagonal' Z) + U := by
  let L : Matrix (Fin N) (Fin N) (Cinf E) := Matrix.of fun p q => if blk e q < blk e p then Y p q else 0
  let S := L - L.conjTranspose
  let Z : ∀ i, Matrix (Fin (n i)) (Fin (n i)) (Cinf E) := fun i => Matrix.of fun a b => (Y - S) (e ⟨i, a⟩) (e ⟨i, b⟩)
  refine ⟨S, Z, Y - S - Matrix.reindex e e (Matrix.blockDiagonal' Z), ?_, ?_, by abel⟩
  · simp only [S, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, neg_sub]
  · intro p q hpq
    obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨j, b⟩, rfl⟩ := e.surjective q
    simp only [blk_apply, not_lt] at hpq
    rcases hpq.lt_or_eq with h | h
    · have hij : i ≠ j := h.ne'
      simp [S, L, Z, Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.blockDiagonal'_apply, hij, h, not_lt_of_gt h]
    · subst h
      simp [Z, Matrix.blockDiagonal'_apply]

def LeviTensor {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N) (π : ∀ i, CuspSub E (n i)) (ψ : Sm E N)
    (A : Matrix (Fin N) (Fin N) (Cinf E)) : Prop :=
  (fun m => (lie E N (toL A) ψ).1 (leviEmb (Ad E) e m)) ∈ tensorForms π

theorem leviTensor_zero {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N) (π : ∀ i, CuspSub E (n i))
    (ψ : Sm E N) : LeviTensor e π ψ 0 := by
  have : (fun m => (lie E N (toL (0 : Matrix (Fin N) (Fin N) (Cinf E))) ψ).1 (leviEmb (Ad E) e m)) = 0 := by
    funext m
    rw [show toL (0 : Matrix (Fin N) (Fin N) (Cinf E)) = 0 from rfl, map_zero]
    rfl
  unfold LeviTensor
  rw [this]
  exact zero_mem _

theorem leviTensor_add {c N : ℕ} {n : Fin c → ℕ} {e : (Σ i, Fin (n i)) ≃ Fin N} {π : ∀ i, CuspSub E (n i)}
    {ψ : Sm E N} {A B : Matrix (Fin N) (Fin N) (Cinf E)} (hA : LeviTensor e π ψ A) (hB : LeviTensor e π ψ B) :
    LeviTensor e π ψ (A + B) := by
  have : (fun m => (lie E N (toL (A + B)) ψ).1 (leviEmb (Ad E) e m)) =
      (fun m => (lie E N (toL A) ψ).1 (leviEmb (Ad E) e m)) + (fun m => (lie E N (toL B) ψ).1 (leviEmb (Ad E) e m)) := by
    funext m
    rw [show toL (A + B) = toL A + toL B from rfl, map_add]
    rfl
  unfold LeviTensor
  rw [this]
  exact add_mem hA hB

theorem leviTensor_sum {c N : ℕ} {n : Fin c → ℕ} {e : (Σ i, Fin (n i)) ≃ Fin N} {π : ∀ i, CuspSub E (n i)}
    {ψ : Sm E N} {ι : Type} (s : Finset ι) (A : ι → Matrix (Fin N) (Fin N) (Cinf E))
    (h : ∀ i ∈ s, LeviTensor e π ψ (A i)) : LeviTensor e π ψ (∑ i ∈ s, A i) :=
  Finset.sum_induction A (LeviTensor e π ψ) (fun _ _ => leviTensor_add) (leviTensor_zero e π ψ) h

theorem leviTensor_all {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N) (π : ∀ i, CuspSub E (n i))
    (ψ : Sm E N) (h1 : ∀ u ∈ unipRad (Ad E) e, ∀ g, ψ.1 (u * g) = ψ.1 g)
    (h2 : ∀ w ∈ Submodule.span ℂ (Set.range fun k => cptRep E N k ψ),
      (fun m => w.1 (leviEmb (Ad E) e m)) ∈ tensorForms π)
    (h3 : ψ ∈ finVec (cptRep E N)) (Y : Matrix (Fin N) (Fin N) (Cinf E)) : LeviTensor e π ψ Y := by
  obtain ⟨S, Z, U, hS, hU, rfl⟩ := exists_decomp e Y
  refine leviTensor_add (leviTensor_add ?_ ?_) ?_
  · exact h2 _ (lie_skew_mem_span ψ h3 S hS)
  · exact lie_block_tensor n e π ψ (h2 ψ (Submodule.subset_span ⟨1, by simp⟩)) Z
  · rw [Matrix.matrix_eq_sum_single U]
    refine leviTensor_sum _ _ fun p _ => leviTensor_sum _ _ fun q _ => ?_
    by_cases hpq : blk e p < blk e q
    · have : (fun m => (lie E N (toL (Matrix.single p q (U p q))) ψ).1 (leviEmb (Ad E) e m)) = 0 :=
        funext fun m => GlobalTheory.UnipZero.lieD_single_leviEmb_eq_zero E n e ψ h1 p q hpq (U p q) m
      unfold LeviTensor
      rw [this]
      exact zero_mem _
    · rw [hU p q hpq, Matrix.single_zero]
      exact leviTensor_zero e π ψ

theorem lie_tensorForms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (X : Lie E N) (φ : Sm E N), φ ∈ indForms h π →
    ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)),
      (fun m => (lie E N X φ).1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g)))
        ∈ tensorForms π := by
  intro E _ _ _ c N n h π X φ hφ k g
  have hφ' := fin_mem_indForms hφ g
  set ψ' : Sm E N := act (.fin g) φ with hψ'
  set y := Unitary.toUnits k with hy
  set ψ : Sm E N := rt E N (infGL E N y) ψ' with hψ
  have key : ∀ x, (lie E N X φ).1 (x * (infGL E N y * finGL E N g)) =
      (lie E N (toL (y.val * Matrix.of X * (y⁻¹).val)) ψ).1 x := by
    intro x
    have h1 := congrArg (fun f : Module.End ℂ (Sm E N) => (f ψ').1 x) (GlobalTheory.CapAdInv.rt_lie (E := E) y (Matrix.of X))
    have h2 := congrArg (fun f : Module.End ℂ (Sm E N) => (f φ).1 (x * infGL E N y)) (lie_rt_fin (E := E) X g)
    simp only [Module.End.mul_apply, rt_apply] at h1 h2
    rw [← mul_assoc, ← h2]
    exact h1
  have hfun : (fun m => (lie E N X φ).1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N y * finGL E N g))) =
      fun m => (lie E N (toL (y.val * Matrix.of X * (y⁻¹).val)) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) :=
    funext fun m => key _
  rw [hfun]
  have hψv : ∀ x, ψ.1 x = φ.1 (x * (infGL E N y * finGL E N g)) := fun x => by
    rw [← mul_assoc]; rfl
  refine leviTensor_all (stdBlocks n h) π ψ (fun u hu x => ?_) (fun w hw => ?_) ?_ _
  · rw [hψv, hψv, mul_assoc, hφ.1 u hu]
  · induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k', rfl⟩ := hw
      have := hφ.2.2.2 (k' * k) g
      convert this using 2 with m
      change ψ.1 (_ * infGL E N (Unitary.toUnits k')) = _
      rw [hψv, map_mul, map_mul, mul_assoc, mul_assoc]
    | zero => exact zero_mem _
    | add w w' _ _ hw hw' => exact add_mem hw hw'
    | smul z w _ hw => exact Submodule.smul_mem _ z hw
  · have hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ')) := hφ'.2.2.1
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E N k ψ'))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k', rfl⟩
    refine Submodule.subset_span ⟨k' * k, ?_⟩
    show cptRep E N (k' * k) ψ' = cptRep E N k' ψ
    rw [map_mul]
    rfl

end GlobalTheory.LieTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst

namespace GlobalTheory.GalOfCusp

def LocalGlobalAboveL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a → ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)), w ∈ placesOver E l → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
      (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
      ∀ rc : IrrGL (w.adicCompletion E) → WD h, IsRec h rc →
        wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

end GlobalTheory.GalOfCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeckeSumPreservesPrincipalLevelForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.LocalHeckeLevel

theorem sum_mul_left_eq {Gp M : Type} [Group Gp] [AddCommMonoid M] (K : Subgroup Gp) (α : Gp) (C : Finset Gp)
    (h1 : ∀ γ ∈ C, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂)
    (h2 : ∀ x : Gp, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ C ∧ γ⁻¹ * x ∈ K)
    (F : Gp → M) (hF : ∀ x, ∀ κ ∈ K, F (x * κ) = F x) {k₀ : Gp} (hk₀ : k₀ ∈ K) :
    ∑ δ ∈ C, F (k₀ * δ) = ∑ δ ∈ C, F δ := by
  classical
  have hmem : ∀ k ∈ K, ∀ δ ∈ C, ∃ k₁ ∈ K, ∃ k₂ ∈ K, k * δ = k₁ * α * k₂ := by
    intro k hk δ hδ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h1 δ hδ
    exact ⟨k * k₁, K.mul_mem hk hk₁, k₂, hk₂, by simp only [mul_assoc]⟩
  let s : Gp → Gp → Gp := fun k δ =>
    if h : ∃ k₁ ∈ K, ∃ k₂ ∈ K, k * δ = k₁ * α * k₂ then (h2 _ h).exists.choose else δ
  have hs : ∀ k ∈ K, ∀ δ ∈ C, s k δ ∈ C ∧ (s k δ)⁻¹ * (k * δ) ∈ K := by
    intro k hk δ hδ
    have h := hmem k hk δ hδ
    have e : s k δ = (h2 _ h).exists.choose := dif_pos h
    rw [e]
    exact (h2 _ h).exists.choose_spec
  have huniq : ∀ k ∈ K, ∀ δ ∈ C, ∀ γ ∈ C, γ⁻¹ * (k * δ) ∈ K → s k δ = γ := by
    intro k hk δ hδ γ hγ hγK
    exact (h2 _ (hmem k hk δ hδ)).unique (hs k hk δ hδ) ⟨hγ, hγK⟩
  have hinv : ∀ δ ∈ C, s k₀⁻¹ (s k₀ δ) = δ := by
    intro δ hδ
    obtain ⟨hm, hK⟩ := hs k₀ hk₀ δ hδ
    apply huniq _ (K.inv_mem hk₀) _ hm _ hδ
    have e : δ⁻¹ * (k₀⁻¹ * s k₀ δ) = ((s k₀ δ)⁻¹ * (k₀ * δ))⁻¹ := by group
    rw [e]
    exact K.inv_mem hK
  have hinv' : ∀ δ ∈ C, s k₀ (s k₀⁻¹ δ) = δ := by
    intro δ hδ
    obtain ⟨hm, hK⟩ := hs k₀⁻¹ (K.inv_mem hk₀) δ hδ
    apply huniq _ hk₀ _ hm _ hδ
    have e : δ⁻¹ * (k₀ * s k₀⁻¹ δ) = ((s k₀⁻¹ δ)⁻¹ * (k₀⁻¹ * δ))⁻¹ := by group
    rw [e]
    exact K.inv_mem hK
  refine Finset.sum_nbij' (s k₀) (s k₀⁻¹) (fun δ hδ => (hs k₀ hk₀ δ hδ).1)
    (fun δ hδ => (hs _ (K.inv_mem hk₀) δ hδ).1) hinv hinv' ?_
  intro δ hδ
  obtain ⟨_, hK⟩ := hs k₀ hk₀ δ hδ
  calc F (k₀ * δ) = F (s k₀ δ * ((s k₀ δ)⁻¹ * (k₀ * δ))) := by rw [mul_inv_cancel_left]
    _ = F (s k₀ δ) := hF _ _ hK

variable {D : D7}

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem mt_injective (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.val_injective (Units.ext h)

theorem suppF_mul {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : SuppF V f b) :
    SuppF V f (a * b) := by
  intro i j
  have e : mt V (a * b) - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by
    rw [mt_mul, sub_mul, one_mul]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, ha i l]

theorem suppF_inv {V : HSp D} {f : AE D} {a : GA D V} (ha : SuppF V f a) : SuppF V f a⁻¹ := by
  intro i j
  have e : mt V a⁻¹ - 1 = -(mt V a⁻¹ * (mt V a - 1)) := by
    rw [mul_sub, ← mt_mul, inv_mul_cancel, mt_one, mul_one]; abel
  rw [e, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, ha l j]

theorem suppF_one (V : HSp D) (f : AE D) : SuppF V f (1 : GA D V) := by
  intro i j
  simp [mt_one]

def suppSub (V : HSp D) (f : AE D) : Subgroup (GA D V) where
  carrier := {g | SuppF V f g}
  mul_mem' := suppF_mul
  one_mem' := suppF_one V f
  inv_mem' := suppF_inv

theorem comm_of_suppF_trivAt {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : TrivAt V f b) :
    a * b = b * a := by
  apply mt_injective
  have hAB : (mt V a - 1) * (mt V b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha i l, mul_assoc, mul_left_comm, hb l j, mul_zero]
  have hBA : (mt V b - 1) * (mt V a - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha l j, mul_left_comm, ← mul_assoc, hb i l, zero_mul]
  have e1 : mt V a * mt V b = (mt V a - 1) * (mt V b - 1) + mt V a + mt V b - 1 := by noncomm_ring
  have e2 : mt V b * mt V a = (mt V b - 1) * (mt V a - 1) + mt V b + mt V a - 1 := by noncomm_ring
  rw [mt_mul, mt_mul, e1, e2, hAB, hBA, zero_add, zero_add, add_comm (mt V a)]

theorem heckeOn_mem_wall : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ (α : GA D (Wc D i)), SuppF (Wc D i) f α → ∀ (C : Finset (GA D (Wc D i))), (∀ γ ∈ C, SuppF (Wc D i) f γ) → IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C → ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hLP v f hf α _ C hC hrep Tm hT
  obtain ⟨hle, hchi, cmp, hcmp1, hcmp2⟩ := hLP
  have hT' : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) Tm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hT
  refine (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).2
    (GlobalTheory.HeckeParts.isMultMap_heckeOn hT' (fun γ hγ => (hrep.1 γ hγ).1) ?_)
  intro w κ hκ g
  have hκ' : κ ∈ levW R i := hκ
  rw [hchi κ hκ', one_mul]
  show ∑ δ ∈ C, Tm w (g * κ * δ) = ∑ δ ∈ C, Tm w (g * δ)
  have hF : ∀ x, ∀ c ∈ levW R i, Tm w (x * c) = Tm w x := fun x c hc => by
    rw [hT'.lev w c hc x, hchi c hc, one_mul]
  obtain ⟨hs, ht⟩ := hcmp1 v f hf κ
  have hkv : cmp v κ ∈ levW R i := ((hcmp2 κ (hle hκ')).1.1 hκ') v
  have hk' : κ * (cmp v κ)⁻¹ ∈ levW R i := mul_mem hκ' (inv_mem hkv)
  calc ∑ δ ∈ C, Tm w (g * κ * δ) = ∑ δ ∈ C, Tm w (g * (κ * (cmp v κ)⁻¹) * (cmp v κ * δ)) :=
        Finset.sum_congr rfl fun δ _ => by group
    _ = ∑ δ ∈ C, Tm w (g * (κ * (cmp v κ)⁻¹) * δ) :=
        sum_mul_left_eq (levW R i ⊓ suppSub (Wc D i) f) α C (fun γ hγ => (hrep.1 γ hγ).2)
          (fun x hx => hrep.2 x hx) (fun x => Tm w (g * (κ * (cmp v κ)⁻¹) * x))
          (fun x c hc => by simp only [← mul_assoc]; exact hF _ c hc.1) (k₀ := cmp v κ) ⟨hkv, hs⟩
    _ = ∑ δ ∈ C, Tm w (g * δ) := Finset.sum_congr rfl fun δ hδ => by
        rw [mul_assoc, ← comm_of_suppF_trivAt (hC δ hδ) ht, ← mul_assoc, hF _ _ hk']

end GlobalTheory.LocalHeckeLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingOfEtaleExactDeRhamCrystallineConstStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralityFromMetric_of_160_le : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ CA CB CK C : ℝ, 160 ≤ C → ElementDenominator.IntegralityFromMetric D HW F Cm CA CB CK C := by
  first | exact @GlobalTheory.TheoremAFinal.integralityFromMetric_of_le | exact GlobalTheory.TheoremAFinal.integralityFromMetric_of_le | (intros; apply GlobalTheory.TheoremAFinal.integralityFromMetric_of_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyDiscPeriodAinfBasisDataOfIsPerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_discPeriodAinfBasisData_of_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ s : Seed bk d ρ τ, Nonempty (Height s) := by
  first | exact @GlobalTheory.BSP.HeightEx.nonempty_height | exact GlobalTheory.BSP.HeightEx.nonempty_height | (intros; apply GlobalTheory.BSP.HeightEx.nonempty_height <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismComparisonMatrixPowSmulBoundedOnDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prism_comparisonMatrix_pow_smul_bounded_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀), ht.Rel (BK.hf f X) f g ε → ∃ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A), x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε := by
  first | exact @GlobalTheory.BSP.comparisonMatrix_bounded | exact GlobalTheory.BSP.comparisonMatrix_bounded | (intros; apply GlobalTheory.BSP.comparisonMatrix_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatSpanOfLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RatSpanProof

theorem ratSpan_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RatSpan R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t
  exact GlobalTheory.HeckeClassSums.span_jV hL.models.HV hL.models.jV i t

end GlobalTheory.RatSpanProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalSourceActsOnOrientedThetaBySubstitutionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_source_acts_on_orientedTheta_by_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ x, ω (γ, 1) f x = f (actO S T γ⁻¹ 1 x) := by
  first | exact @GlobalTheory.RatSubst.om_rat_left_apply | exact GlobalTheory.RatSubst.om_rat_left_apply | (intros; apply GlobalTheory.RatSubst.om_rat_left_apply <;> assumption)
end

