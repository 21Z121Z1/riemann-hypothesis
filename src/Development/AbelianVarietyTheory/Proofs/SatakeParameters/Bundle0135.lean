import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordFreeNumberLeOrbitBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0101
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.Bundle0002
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0115
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0126
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0121

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixCharpolySmul
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTieLP

open GlobalTheory.WeilDeligne

theorem matrix_charpoly_smul {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (c : ℂ) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  by_cases hc : c = 0
  · subst hc
    ext i
    rw [zero_smul, Matrix.charpoly_zero, coeff_scaleRoots, M.charpoly_natDegree_eq_dim, coeff_X_pow]
    by_cases hi : i = Fintype.card n
    · subst hi
      have := M.charpoly_monic.coeff_natDegree
      rw [M.charpoly_natDegree_eq_dim] at this
      simp [this]
    · rcases lt_or_gt_of_ne hi with h | h
      · have : Fintype.card n - i ≠ 0 := by omega
        simp [hi, this]
      · simp [hi, coeff_eq_zero_of_natDegree_lt (p := M.charpoly) (by rwa [M.charpoly_natDegree_eq_dim])]
  · apply Polynomial.funext
    intro t
    have h1 : (M.charpoly.scaleRoots c).eval (c * (t / c)) = c ^ M.charpoly.natDegree * M.charpoly.eval (t / c) := by
      simpa using scaleRoots_eval₂_mul (RingHom.id ℂ) (t / c) c (p := M.charpoly)
    rw [mul_div_cancel₀ _ hc, M.charpoly_natDegree_eq_dim] at h1
    rw [h1, Matrix.eval_charpoly, Matrix.eval_charpoly, ← Matrix.det_smul]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.diagonal_apply, mul_sub]
    split_ifs <;> field_simp

theorem charpoly_smul_end {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (c : ℂ) : (c • f).charpoly = f.charpoly.scaleRoots c := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, matrix_charpoly_smul,
    LinearMap.charpoly_toMatrix]

theorem charpoly_map_line {V L : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup L] [Module ℂ L] [FiniteDimensional ℂ L] (hL : Module.finrank ℂ L = 1)
    (f : Module.End ℂ V) (c : ℂ) :
    (TensorProduct.map f (c • (1 : Module.End ℂ L))).charpoly = f.charpoly.scaleRoots c := by
  let e : L ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq L ℂ (by simp [hL])
  let E : TensorProduct ℂ V L ≃ₗ[ℂ] V :=
    (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  have key : ∀ x, E (TensorProduct.map f (c • (1 : Module.End ℂ L)) x) = (c • f) (E x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v l =>
      simp [E, TensorProduct.map_tmul, smul_comm c, map_smul]
  have h2 : E.conj (TensorProduct.map f (c • (1 : Module.End ℂ L))) = c • f := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := E.surjective v
    simpa [LinearEquiv.conj_apply] using key x
  rw [← charpoly_smul_end, ← h2, LinearEquiv.charpoly_conj]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem inePol_char {a c : WD h} (hc : c.lpDim = 1) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B)
    {z : ℂ} (hz : c.inePol σ = X - C z) : (a.lpChar c).inePol σ = (a.inePol σ).scaleRoots z := by
  induction a using WD.ind with
  | hP m a =>
  induction c using WD.ind with
  | hP n c =>
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk] at hz
    rw [WD.lpDim_mk] at hc
    have h1 := LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))
    rw [hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h1
    rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.charPol_mk,
      WDRep.tensor_ρ, h1, charpoly_map_line hc]

end GlobalTheory.RowTieLP

theorem GlobalTheory.RowTieLP.main : ∀ (D : D7), WDTie D.nd D.naut → Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut := by
  intro D T w a b χ χ' s h1 h2
  obtain ⟨l1, l2, l3, l4, l5⟩ := (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ _ _ T).2.1 w a b χ χ' s h1 h2
  refine ⟨l1, l2, l3, l4, l5, fun σ hσ => ⟨⟨?_, ?_⟩, fun c hc => ?_⟩⟩
  · rw [T.inePol w a σ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ]
    exact GlobalTheory.WeilDeligne.WD.charPol_monic _ _
  · rw [T.inePol w a σ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ, GlobalTheory.WeilDeligne.WD.charPol_natDegree, T.dim]
  · rw [T.inePol w χ σ hσ] at hc
    have hd : (T.e w χ).lpDim = 1 := by rw [T.dim, h1]
    rw [T.inePol w _ σ hσ, T.char _ _ _ h1, T.inePol w a σ hσ]
    exact GlobalTheory.RowTieLP.inePol_char hd hσ hc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexIntegralTranslationInvariance
section
noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mulVec_mem_intVec_of_int {a b : ℕ} {M : Matrix (Fin a) (Fin b) L}
    (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) {v : Fin b → L} (hv : v ∈ intVec L b) :
    M.mulVec v ∈ intVec L a := by
  rw [mem_intVec] at hv ⊢
  intro i
  change (∑ j, M i j * v j) ∈ Formalism.UG.intL L
  exact sum_mem fun j _ => mul_mem (hM i j) (hv j)

theorem entry_mem_of_mem_GLint {n : ℕ} {g : GL (Fin n) L} (hg : g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L))
    (i j : Fin n) : (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  obtain ⟨g0, rfl⟩ := hg
  exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2

theorem latIdx_add_int {a b : ℕ} (x u : Matrix (Fin a) (Fin b) L) (hu : u ∈ intMat L a b) :
    latIdx (x + u) = latIdx x := by
  have hf : (fun v : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec (x + u) (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a)) =
      fun v : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a) := by
    funext v
    rw [Matrix.add_mulVec, QuotientAddGroup.mk_add,
      (QuotientAddGroup.eq_zero_iff _).2 (mulVec_mem_intVec_of_int ((mem_intMat u).1 hu) v.2), add_zero]
  unfold latIdx
  rw [hf]

def quotMul {a : ℕ} (M : Matrix (Fin a) (Fin a) L) (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) :
    (Fin a → L) ⧸ intVec L a →+ (Fin a → L) ⧸ intVec L a :=
  QuotientAddGroup.map (intVec L a) (intVec L a) (Matrix.mulVecLin M).toAddMonoidHom
    fun _ hv => mulVec_mem_intVec_of_int hM hv

theorem quotMul_mk {a : ℕ} (M : Matrix (Fin a) (Fin a) L) (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) (v : Fin a → L) :
    quotMul M hM (QuotientAddGroup.mk v) = QuotientAddGroup.mk (M.mulVec v) := rfl

theorem latIdx_GLint_mul {a b : ℕ} (x : Matrix (Fin a) (Fin b) L) (h : GL (Fin a) L)
    (hh : h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L)) :
    latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = latIdx x := by
  have h1 := entry_mem_of_mem_GLint hh
  have h2 := entry_mem_of_mem_GLint (inv_mem hh)
  have hinj : Function.Injective (quotMul (h : Matrix (Fin a) (Fin a) L) h1) := by
    have hl : Function.LeftInverse (quotMul ((h⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) h2)
        (quotMul (h : Matrix (Fin a) (Fin a) L) h1) := by
      intro q
      induction q using QuotientAddGroup.induction_on with
      | H v =>
        rw [quotMul_mk, quotMul_mk, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
    exact hl.injective
  have hr : (Set.range fun v : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec ((h : Matrix (Fin a) (Fin a) L) * x) (v : Fin b → L)) :
        (Fin a → L) ⧸ intVec L a)) =
      quotMul (h : Matrix (Fin a) (Fin a) L) h1 '' Set.range fun v : intVec L b =>
        (QuotientAddGroup.mk (Matrix.mulVec x (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a) := by
    rw [← Set.range_comp]
    congr 1
    funext v
    simp only [Function.comp_apply, quotMul_mk, Matrix.mulVec_mulVec]
  unfold latIdx
  rw [hr, Nat.card_image_of_injective hinj]

theorem latIdx_invariance : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) (x : Matrix (Fin a) (Fin b) L),
    (∀ u ∈ GlobalTheory.Hk3.HoweDuality.intMat L a b, GlobalTheory.Hk3.HoweDuality.latIdx (x + u) = GlobalTheory.Hk3.HoweDuality.latIdx x) ∧
    ∀ h : GL (Fin a) L, h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      GlobalTheory.Hk3.HoweDuality.latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = GlobalTheory.Hk3.HoweDuality.latIdx x :=
  fun _ _ _ _ _ x => ⟨fun u hu => latIdx_add_int x u hu, fun h hh => latIdx_GLint_mul x h hh⟩

end GlobalTheory.Hk3.HoweDuality

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIInfOfApply
section
namespace GlobalTheory.IndependentInfimum

open Module

theorem le_of_indep {K V X : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : X → Submodule K V) (hW : iSupIndep W) (hUW : ∀ x, U x ≤ W x)
    (hU : ⨆ x, U x = ⊤) (x : X) : W x ≤ U x := by
  classical
  intro w hw
  have htop : w ∈ ⨆ y, U y := by rw [hU]; exact Submodule.mem_top
  have hsplit : (⨆ y, U y) = U x ⊔ ⨆ (y) (_ : y ≠ x), U y := by
    apply le_antisymm
    · refine iSup_le fun y => ?_
      by_cases hy : y = x
      · subst hy
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le y hy le_rfl)
    · exact sup_le (le_iSup U x) (iSup₂_le fun y _ => le_iSup U y)
  rw [hsplit] at htop
  obtain ⟨u, hu, w', hw', hsum⟩ := Submodule.mem_sup.1 htop
  have hw'W : w' ∈ ⨆ (y) (_ : y ≠ x), W y :=
    (iSup₂_mono fun y _ => hUW y) hw'
  have hdiff : w - u ∈ W x := W x |>.sub_mem hw (hUW x hu)
  have heq : w - u = w' := by rw [← hsum]; abel
  have hdis := (hW x).le_bot (Submodule.mem_inf.2 ⟨hdiff, heq ▸ hw'W⟩)
  rw [Submodule.mem_bot, sub_eq_zero] at hdis
  rw [hdis]
  exact hu

theorem mem_iInf_of_apply {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : I → Module.End K V) (x : I → K) (v : V) (hv : ∀ i, A i v = x i • v) :
    v ∈ ⨅ i, (A i).maxGenEigenspace (x i) := Submodule.mem_iInf _ |>.2 fun i =>
  Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 (hv i))

theorem main {E I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hE : ⨆ (c : C), Ec c = LinearMap.range e)
    (hl : ∀ (c : C), ∀ w ∈ Ec c, ∀ (i : I), (h i : E → E) w = lab c i • w) :
    (Formalism.L2.Col.PairComm fun (i : I) ↦ h i * e) ∧ ∀ (Q : (I → ℂ) → Prop), ¬Q (0 : I → ℂ) →
      Formalism.L2.Col.eigSum (fun (i : I) ↦ h i * e) Q = ⨆ (c : C), ⨆ (_ : Q (lab c)), Ec c := by
  classical
  have hee : ∀ v, e (e v) = e v := fun v => by
    have := congrArg (fun f : Module.End ℂ E => f v) he
    simpa using this
  have hfix : ∀ c, ∀ w ∈ Ec c, e w = w := by
    intro c w hw
    have : w ∈ LinearMap.range e := hE ▸ Submodule.mem_iSup_of_mem c hw
    obtain ⟨u, rfl⟩ := this
    exact hee u
  have hA : ∀ c, ∀ w ∈ Ec c, ∀ i, (h i * e) w = lab c i • w := by
    intro c w hw i
    rw [Module.End.mul_apply, hfix c w hw, hl c w hw]
  have hcomm : ∀ i j, Commute (h i * e) (h j * e) := by
    intro i j
    have key : ∀ w ∈ ⨆ c, Ec c, (h i * e) ((h j * e) w) = (h j * e) ((h i * e) w) := by
      intro w hw
      induction hw using Submodule.iSup_induction' with
      | mem c w hw =>
        rw [hA c w hw j, hA c w hw i, map_smul, map_smul, hA c w hw j, hA c w hw i, smul_comm]
      | zero => simp
      | add a b _ _ ha hb => simp only [map_add, ha, hb]
    ext v
    have hv : e v ∈ ⨆ c, Ec c := by rw [hE]; exact ⟨v, rfl⟩
    have := key _ hv
    simpa [Module.End.mul_apply, hee] using this
  refine ⟨hcomm, fun Q hQ => ?_⟩
  have hind : iSupIndep fun x : I → ℂ => ⨅ i, (h i * e).maxGenEigenspace (x i) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun i => h i * e)
      fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  let U : (I → ℂ) → Submodule ℂ E := fun x =>
    (⨆ (c : C) (_ : lab c = x), Ec c) ⊔ ⨆ (_ : x = 0), LinearMap.ker e
  have hUW : ∀ x, U x ≤ ⨅ i, (h i * e).maxGenEigenspace (x i) := by
    intro x
    refine sup_le (iSup₂_le fun c hc w hw => ?_) (iSup_le fun hx w hw => ?_)
    · exact mem_iInf_of_apply (fun i => h i * e) x w fun i => hc ▸ hA c w hw i
    · refine mem_iInf_of_apply (fun i => h i * e) x w fun i => ?_
      rw [LinearMap.mem_ker] at hw
      simp [hx, Module.End.mul_apply, hw]
  have hU : ⨆ x, U x = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : LinearMap.range e ≤ ⨆ x, U x := by
      rw [← hE]
      exact iSup_le fun c => le_iSup_of_le (lab c)
        (le_sup_of_le_left (le_iSup₂_of_le (f := fun c' (_ : lab c' = lab c) => Ec c') c rfl le_rfl))
    have h2 : LinearMap.ker e ≤ ⨆ x, U x :=
      le_iSup_of_le 0 (le_sup_of_le_right
        (le_iSup_of_le (f := fun _ : (0 : I → ℂ) = 0 => LinearMap.ker e) rfl le_rfl))
    have h3 : v - e v ∈ LinearMap.ker e := by simp [LinearMap.mem_ker, hee]
    have := Submodule.add_mem _ (h1 ⟨v, rfl⟩) (h2 h3)
    simpa using this
  unfold Formalism.L2.Col.eigSum Formalism.L2.Col.eigAt
  apply le_antisymm
  · refine iSup₂_le fun x hx => (le_of_indep U _ hind hUW hU x).trans ?_
    refine sup_le (iSup₂_le fun c hc => ?_) (iSup_le fun h0 => absurd (h0 ▸ hx) hQ)
    exact le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c (hc ▸ hx) le_rfl
  · refine iSup₂_le fun c hc => ?_
    refine le_iSup₂_of_le
      (f := fun (x : I → ℂ) (_ : Q x) => ⨅ i, (h i * e).maxGenEigenspace (x i)) (lab c) hc ?_
    intro w hw
    exact mem_iInf_of_apply (fun i => h i * e) (lab c) w (hA c w hw)

end GlobalTheory.IndependentInfimum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralFiniteAdelesTensorIffLocalOrders
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp.IntLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_int_generators (E : Type) [Field E] [NumberField E] :
    ∃ (k : ℕ) (x : Fin k → 𝓞 E), ∀ w : 𝓞 E, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  refine ⟨k, s, fun w => ?_⟩
  have : w ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  exact ⟨n, hn.symm⟩

omit [NumberField E] in

theorem mem_addClosure_of_mem_ordAt (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E)
    (hy : y ∈ ordAt E v) :
    y ∈ AddSubgroup.closure
      {y : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  have h := Subring.mem_closure_iff.1 hy
  refine AddSubgroup.closure_mono ?_ h
  intro z hz
  induction hz using Submonoid.closure_induction with
  | mem z hz => exact hz
  | one => exact ⟨1, one_mem _, 1, rfl⟩
  | mul z w _ _ hz hw =>
    obtain ⟨a, ha, x, rfl⟩ := hz
    obtain ⟨b, hb, x', rfl⟩ := hw
    exact ⟨a * b, mul_mem ha hb, x * x', by
      rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl⟩

omit [NumberField E] in

theorem exists_coeff {k : ℕ} (x : Fin k → 𝓞 E)
    (hx : ∀ w : 𝓞 E, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j) (v : HeightOneSpectrum (𝓞 F))
    (y : Fv F v ⊗[F] E) (hy : y ∈ ordAt E v) :
    ∃ a : Fin k → Fv F v, (∀ j, a j ∈ v.adicCompletionIntegers F) ∧
      y = ∑ j, a j ⊗ₜ[F] (x j : E) := by
  have hy' := mem_addClosure_of_mem_ordAt v y hy
  clear hy
  induction hy' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, w, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := hx w
    refine ⟨fun j => n j • a, fun j => zsmul_mem ha _, ?_⟩
    show a ⊗ₜ[F] (algebraMap (𝓞 E) E (∑ j, n j • x j)) =
      ∑ j, (n j • a) ⊗ₜ[F] (algebraMap (𝓞 E) E (x j))
    simp only [map_sum, map_zsmul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul]
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, ea⟩ := hy
    obtain ⟨b, hb, eb⟩ := hz
    exact ⟨a + b, fun j => add_mem (ha j) (hb j), by
      simp only [Pi.add_apply, ea, eb, TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
  | neg y _ hy =>
    obtain ⟨a, ha, ea⟩ := hy
    exact ⟨-a, fun j => neg_mem (ha j), by
      simp only [Pi.neg_apply, ea, TensorProduct.neg_tmul, Finset.sum_neg_distrib]⟩

theorem mem_intA_iff :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (z : Af F ⊗[F] E),
      z ∈ intA F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), evF E v z ∈ ordAt E v := by
  intro F E _ _ _ _ _ z
  constructor
  · intro hz v
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      exact Subring.subset_closure ⟨_, ha v, x, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  · intro h
    obtain ⟨k, x, hx⟩ := exists_int_generators E
    choose a ha ea using fun v => exists_coeff x hx v _ (h v)
    let A : Fin k → Af F := fun j =>
      ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩
    have e : z = ∑ j, A j ⊗ₜ[F] (x j : E) := by
      apply evF_ext
      intro v
      rw [ea v, map_sum]
      exact Finset.sum_congr rfl fun j _ => rfl
    rw [e]
    exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨A j, fun v => ha v j, x j, rfl⟩

end GlobalTheory.PlaceComp.IntLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundStandardSeriesInertPlaces
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.OrbitBoundStdRec

theorem kvalGe_le {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) {B B' : ℝ} (h : B' ≤ B) (H : product_zeroth_first_parts.KvalGe N0 N1 l nu Th B) :
    product_zeroth_first_parts.KvalGe N0 N1 l nu Th B' := fun I m =>
  (H I m).trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (Fact.out : l.Prime).one_lt.le) (neg_le_neg h))

theorem orbit_bound_rec : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Ee : OrbitPlaces.Ent D), OrbitPlaces.Shape D L X Ee →
    (∀ u, ∀ i < D.R.m, ∀ t ∈ D.host.TT, Ee.row u i (false, t) 0 - Ee.row u i (false, t) 1 ≤ 2 * L.sc.a) → 5 ≤ K.dl1 → 4 ≤ K.dl2 →
    BeFam D Ee.ep Ee.be → (Ee.sg = fun _ _ => -1) → OrbitPlaces.OrbitBoundWithoutOperator Ee X K := by
  intro D L X K Ee hS hG hd1 hd2 hBe hsg
  intro w h hC0 hh hX u j hj t0 ht0 Th hB
  have hEv : HEv D (D.what₂.places.resChar w) := by
    have he := h.even
    unfold nP at he
    rw [if_neg (GlobalTheory.KerStd.WordFree.not_signal hC0)] at he
    exact he
  obtain ⟨hep, hbe⟩ := hBe w (Or.inl ⟨hC0, hEv⟩)
  have hs : Ee.sg w (false, t0) = -1 := by rw [hsg]
  rw [hs] at hB
  have z0 := GlobalTheory.T.standardOrbitSeries_valuationBound_zero (OrbitPlaces.orbLoc Ee _ h u j (false, t0) Th) _ _ hep (hbe (false, t0)) hB
  have z1 := GlobalTheory.T.kvalGe_orbitGainWithoutOperator (OrbitPlaces.orbLoc Ee _ h u j (false, t0) Th) _ _ hep (hbe (false, t0)) hB
  have z2 := GlobalTheory.KerStd.WordFree.wordFreeNumber_le_orbitBound D L X K Ee hS hG hd1 hd2 _ h hC0 hh hX u j hj t0 ht0 Th
  rcases le_total (g0 X K (aL L) (bL L) (D.what₂.places.resChar w) (j + 1) t0) 0 with hm | hm
  · rw [max_eq_right hm]
    exact z0
  · rw [max_eq_left hm]
    exact kvalGe_le _ _ _ _ _ z2 z1

end GlobalTheory.OrbitBoundStdRec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormLeOneHostBaseModuleAtDStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_norm_le_one_host_base_module_at_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (φ : D.host.E →+* ℂ_[p]) (a : D.host.E), a ∈ D.host.AA0 → ‖φ a‖ ≤ 1 := by
  first | exact @GlobalTheory.IntegralAtPlace.norm_le_one | exact GlobalTheory.IntegralAtPlace.norm_le_one | (intros; apply GlobalTheory.IntegralAtPlace.norm_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairEmbeddingsCongrModRootMinusDStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_embeddings_congr_mod_root_minus_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (ι : ℂ ≃+* ℂ_[p]) (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) → δ ^ 2 = -(p : D.host.E) → s δ = -δ → (∀ y, s (s y) = y) → (∀ (t : HH D) (y : D.host.E), TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) → (∀ (τ : D.what₂.Tau) (y : D.host.E), s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) → (‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ ≤ 1 ∧ ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) ≠ 0) ∧ ∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ := by
  first | exact @GlobalTheory.DFrame.congr_at_d | exact GlobalTheory.DFrame.congr_at_d | (intros; apply GlobalTheory.DFrame.congr_at_d <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointInFamilyCrystalline
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem pointInputAwayFromTypePrimes : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (X : KillingConditions.HubData D), GlobalTheory.PtCore.PtFam D X.r X.ρ → AdmissibleParameterJ.DeRhamFamilyAway D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, GlobalTheory.HTW.RecS.PtIn i (X.r i) (X.ρ i) π := by
  intro hF D X hX hG i hl π hπ
  have hZ := LargeLevelLemmas.zgoodSubsetZ i hπ
  have hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (X.r i) (X.ρ i) π := by
    obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
    exact ⟨e, fun g u => he g u⟩
  have h0 : D.nd.l i ≠ D.host.g 0 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have h1 : D.nd.l i ≠ D.host.g 1 := fun h => hl (by simp [TwistedPlaces.gset, h])
  exact ⟨hX.good i, fun x => (hX.good i x).1, hZ, hd, hX.cont i π, fun w hw C x =>
    ((GlobalTheory.T.coefficient_extension_decomposition hF D i _ _ π (hX.good i) (hG i _ (hX.good i)) h0 h1 hd w hw C).2 x).2⟩

end GlobalTheory
end

