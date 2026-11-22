import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0281
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerLeFinset
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.Chain.IoLift.Factor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem kerLe_finset {A B Z₁ Z₂ σ : Type} [AddCommMonoid Z₁] [AddCommMonoid Z₂] {q₁ : A → B → Z₁} {q₂ : A → B → Z₂}
    (h : KerLe q₁ q₂) (s : Finset σ) (a : σ → A) (b : σ → B) (h0 : ∑ r ∈ s, q₁ (a r) (b r) = 0) :
    ∑ r ∈ s, q₂ (a r) (b r) = 0 := by
  have e := s.equivFin.symm
  rw [← Finset.sum_coe_sort s, ← e.sum_comp] at h0 ⊢
  exact h _ (fun k => a (e k)) (fun k => b (e k)) h0

theorem section_eq {ι : Type} [Fintype ι] {N K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (α : ∀ i, N i →ₗ[ℂ] K i) (s : ∀ i, K i →ₗ[ℂ] N i) (hs : ∀ i x, α i (s i x) = x)
    (M : MultilinearMap ℂ N Z) (hM : ∀ n i z, α i z = 0 → M (Function.update n i z) = 0) (n : ∀ i, N i) :
    M (fun i => s i (α i (n i))) = M n := by
  have key : ∀ S : Finset ι, M (S.piecewise (fun i => s i (α i (n i))) n) = M n := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      rw [Finset.piecewise_insert, ← ih]
      have h1 := hM (S.piecewise (fun i => s i (α i (n i))) n) j (s j (α j (n j)) - n j) (by simp [hs])
      rw [MultilinearMap.map_update_sub, sub_eq_zero] at h1
      rw [h1]
      congr 1
      rw [Function.update_eq_self_iff, Finset.piecewise_eq_of_notMem _ _ _ hj]
  simpa using key Finset.univ

theorem factor :
    ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (P Y : ι → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] (A : ∀ i, P i →ₗ[ℂ] Y i →ₗ[ℂ] K i), (∀ i, Submodule.span ℂ {x | ∃ p y, A i p y = x} = ⊤) → Submodule.span ℂ {x : ⨂[ℂ] i, K i | ∃ (p : ∀ i, P i) (y : ∀ i, Y i), PiTensorProduct.tprod ℂ (fun i => A i (p i) (y i)) = x} = ⊤ ∧ ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (B : MultilinearMap ℂ P (MultilinearMap ℂ Y Z)), (∀ i p y, KerLe (fun x z => A i x z) fun x z => B (Function.update p i x) (Function.update y i z)) → ∃ T : (⨂[ℂ] i, K i) →ₗ[ℂ] Z, ∀ p y, T (PiTensorProduct.tprod ℂ fun i => A i (p i) (y i)) = B p y := by
  intro ι _ K _ _ P Y _ _ _ _ A hA
  let α : ∀ i, (P i × Y i →₀ ℂ) →ₗ[ℂ] K i := fun i => Finsupp.linearCombination ℂ fun r => A i r.1 r.2
  have hα : ∀ i, LinearMap.range (α i) = ⊤ := by
    intro i
    rw [Finsupp.range_linearCombination, ← hA i]
    congr 1
    ext x
    simp
  choose s hs using fun i => (α i).exists_rightInverse_of_surjective (hα i)
  have hs' : ∀ i x, α i (s i x) = x := fun i x => LinearMap.congr_fun (hs i) x
  let b0 : ∀ i, Module.Basis (P i × Y i) ℂ (P i × Y i →₀ ℂ) := fun i => Finsupp.basisSingleOne
  have hb0 : ∀ i r, α i (b0 i r) = A i r.1 r.2 := by
    intro i r
    simp [α, b0]
  let b := Basis.piTensorProduct b0
  refine ⟨?_, ?_⟩
  · have hsurj : LinearMap.range (PiTensorProduct.map α) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro t
      refine ⟨PiTensorProduct.map s t, ?_⟩
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      simp [hs]
    rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span] at hsurj
    rw [eq_top_iff, ← hsurj]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨fun i => (q i).1, fun i => (q i).2, ?_⟩
    simp [b, hb0]
  · intro Z _ _ B hB
    let M : MultilinearMap ℂ (fun i => P i × Y i →₀ ℂ) Z :=
      (b.constr ℂ fun q => B (fun i => (q i).1) (fun i => (q i).2)).compMultilinearMap (PiTensorProduct.tprod ℂ)
    have hMb : ∀ q : ∀ i, P i × Y i, M (fun i => b0 i (q i)) = B (fun i => (q i).1) (fun i => (q i).2) := by
      intro q
      simp only [M, LinearMap.compMultilinearMap_apply]
      rw [← Basis.piTensorProduct_apply b0 q]
      exact b.constr_basis ℂ _ q
    have hM0 : ∀ (q : ∀ i, P i × Y i) i z, α i z = 0 → M (Function.update (fun i => b0 i (q i)) i z) = 0 := by
      intro q i z hz
      have h1 : ∀ r, M (Function.update (fun i => b0 i (q i)) i (b0 i r)) =
          B (Function.update (fun i => (q i).1) i r.1) (Function.update (fun i => (q i).2) i r.2) := by
        intro r
        have := hMb (Function.update q i r)
        convert this using 2 <;> [skip; congr 1; skip] <;> funext j <;> by_cases h : j = i <;>
          first | (subst h; simp) | simp [h]
      have h2 : M (Function.update (fun i => b0 i (q i)) i z) = ∑ r ∈ z.support,
          B (Function.update (fun i => (q i).1) i (z r • r.1)) (Function.update (fun i => (q i).2) i r.2) := by
        have hz' : z = ∑ r ∈ z.support, z r • b0 i r := by
          conv_lhs => rw [← Finsupp.sum_single z]
          simp [Finsupp.sum, b0]
        conv_lhs => rw [hz']
        rw [MultilinearMap.map_update_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [MultilinearMap.map_update_smul, MultilinearMap.map_update_smul, h1]
        rfl
      rw [h2]
      refine kerLe_finset (hB i (fun i => (q i).1) (fun i => (q i).2)) z.support (fun r => z r • r.1)
        (fun r => r.2) ?_
      simpa [α, Finsupp.linearCombination_apply, Finsupp.sum] using hz
    have hM : ∀ n i z, α i z = 0 → M (Function.update n i z) = 0 := by
      intro n i z hz
      let φ : (P i × Y i →₀ ℂ) →ₗ[ℂ] (P i × Y i →₀ ℂ) := Finsupp.linearCombination ℂ fun _ => z
      have hφ : ∀ r, φ (b0 i r) = z := by
        intro r
        simp [φ, b0]
      let f : ∀ j, (P j × Y j →₀ ℂ) →ₗ[ℂ] (P j × Y j →₀ ℂ) := Function.update (fun j => LinearMap.id) i φ
      have hf : ∀ m : ∀ j, (P j × Y j →₀ ℂ), (fun j => f j (m j)) = Function.update m i (φ (m i)) := by
        intro m
        funext j
        by_cases h : j = i
        · subst h; simp [f]
        · simp [f, h]
      have h0 : M.compLinearMap f = 0 := by
        refine Module.Basis.ext_multilinear b0 fun q => ?_
        rw [MultilinearMap.compLinearMap_apply, hf, hφ]
        exact hM0 q i z hz
      have := congrArg (fun F => F (Function.update n i (b0 i 0))) h0
      simpa [hf, hφ] using this
    refine ⟨PiTensorProduct.lift (M.compLinearMap s), fun p y => ?_⟩
    rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, ← hMb fun i => (p i, y i),
      ← section_eq α s hs' M hM fun i => b0 i (p i, y i)]
    simp only [hb0]

end GlobalTheory.Chain.IoLift.Factor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizerAtPlaceMemDepthCongruenceGridNoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabilizerAtPlace_mem_depthCongruence_gridNode : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → ∀ v, v ∉ G.pl.S0 → ∀ κ, InK (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) κ → κ ∈ lev G (.grid i 0) := by
  first | exact @GlobalTheory.LevelOffS.inK_mem_lev | exact GlobalTheory.LevelOffS.inK_mem_lev | (intros; apply GlobalTheory.LevelOffS.inK_mem_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumLongVectorsDecayWeightLe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

variable {D : D7}

def compVec (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) :
    (Fin V.rank → D.host.E) →+ (D.what₂.Tau → EuclideanSpace ℂ (Fin V.rank)) where
  toFun w τ := WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (w i)))
  map_zero' := by
    funext τ
    have h : (fun i => tauE D τ ((0 : Fin V.rank → D.host.E) i)) = 0 := by
      funext i; simp
    show WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ ((0 : Fin V.rank → D.host.E) i))) = 0
    rw [h, Matrix.mulVec_zero, Matrix.mulVec_zero]
    rfl
  map_add' x y := by
    funext τ
    have h : (fun i => tauE D τ ((x + y) i)) = (fun i => tauE D τ (x i)) + fun i => tauE D τ (y i) := by
      funext i; simp
    show WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ ((x + y) i))) =
      WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (x i))) +
        WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (y i)))
    rw [h, Matrix.mulVec_add, Matrix.mulVec_add, WithLp.toLp_add]

theorem norm_compVec (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (w : Fin V.rank → D.host.E) (τ : D.what₂.Tau) :
    ‖compVec θ V B g w τ‖ = nrm θ B g τ w := by
  rw [EuclideanSpace.norm_eq]; rfl

theorem latSum_le : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (L : Lat V) (R : ℝ), 1 ≤ V.rank → 1 < R → (∀ w ∈ L, w ≠ 0 → R ≤ ∏ τ, nrm θ B g τ w) → ∀ s : Finset (Fin V.rank → D.host.E), (∀ w ∈ s, w ∈ L ∧ w ≠ 0) → ∑ w ∈ s, ∏ τ, (((1 + nrm θ B g τ w) / 3) ^ (2 * V.rank + 5))⁻¹ ≤ Real.exp ((6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) / R := by
  intro D θ V B g L R hn hR hL s hs
  classical
  have hnorm : ∀ w τ, ‖compVec θ V B g w τ‖ = nrm θ B g τ w := norm_compVec θ V B g
  by_cases hι : IsEmpty D.what₂.Tau
  · have hs0 : s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      have h1 := hL w (hs w hw).1 (hs w hw).2
      rw [Finset.univ_eq_empty, Finset.prod_empty] at h1
      linarith
    subst hs0
    rw [Finset.sum_empty]
    exact div_nonneg (Real.exp_pos _).le (by linarith)
  · haveI : Nonempty D.what₂.Tau := not_isEmpty_iff.mp hι
    have hzero : ∀ w, compVec θ V B g w = 0 → ∏ τ, nrm θ B g τ w = 0 := by
      intro w h0
      refine Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary _)) ?_
      rw [← hnorm, h0, Pi.zero_apply, norm_zero]
    have hinj : Set.InjOn (compVec θ V B g) (s : Set _) := by
      intro x hx y hy hxy
      by_contra hne
      have hm : x - y ∈ L := L.sub_mem (hs x hx).1 (hs y hy).1
      have h1 := hL _ hm (sub_ne_zero.mpr hne)
      have hz : compVec θ V B g (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      rw [hzero _ hz] at h1
      linarith
    have key := GlobalTheory.T.lattice_sum_prod_norm_le_of_prod_norm_lower_bound D.what₂.Tau V.rank (L.toAddSubgroup.map (compVec θ V B g)) R hn hR ?_
      (s.image (compVec θ V B g)) ?_
    · rw [Finset.sum_image hinj] at key
      simpa only [hnorm] using key
    · intro v hv hv0
      obtain ⟨w, hwL, rfl⟩ := AddSubgroup.mem_map.mp hv
      have hwL' : w ∈ L := hwL
      have hw0 : w ≠ 0 := by rintro rfl; exact hv0 (map_zero _)
      simpa only [hnorm] using hL w hwL' hw0
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      refine ⟨AddSubgroup.mem_map_of_mem _ (hs w hw).1, ?_⟩
      intro h0
      have h1 := hL w (hs w hw).1 (hs w hw).2
      rw [hzero w h0] at h1
      linarith

end GlobalTheory.SepPer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorFiniteDatumIsThetaVacuumOff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.VacOff

variable {D : D7}

theorem placeIdem_smul_off {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v w : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D w ε) (hwv : w ≠ v) {u : WO S T}
    (hu : u ∈ latO S T LS LT fun x => x = v) : algebraMap (AF D.host.F) (AE D) ε • u = 0 := by
  obtain ⟨β, rfl, -, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hx
    have hβα : β * α = 0 := by
      refine RestrictedProduct.ext _ _ fun y => ?_
      change evalV D.host.F y (β * α) = evalV D.host.F y 0
      rw [map_mul, map_zero]
      by_cases hy : y = w
      · subst hy; rw [hP y hwv, mul_zero]
      · rw [h0 y hy, zero_mul]
    have hp : pairA D.host.F 0 β * pairA D.host.F 0 α = 0 := Prod.ext (mul_zero _) hβα
    ext i j
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = (0 : AE D)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp, TensorProduct.zero_tmul]
  | zero => rw [smul_zero]
  | add x x' _ _ h h' => rw [smul_add, h, h', add_zero]
  | neg x _ h => rw [smul_neg, h, neg_zero]

theorem idemSum_mul_off {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} {Pset : Finset (Pl D.host.E)} (he : IsIdemSum e Pset)
    (hv : ∀ PP ∈ Pset, PP.under (𝓞 D.host.F) ≠ v) {u : WO S T} (hu : u ∈ latO S T LS LT fun x => x = v) (a b) :
    e * u a b = 0 ∧ cA D e * u a b = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have key : ∀ PP ∈ Pset, es PP * u a b = 0 ∧ cA D (es PP) * u a b = 0 := by
    intro PP hPP
    obtain ⟨⟨a1, a2, w, ε, hε, a3⟩, -⟩ := hes PP hPP
    have hw : w ≠ v := fun h => hv PP hPP (by
      rw [← h]; exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP w ε (hes PP hPP) hε a3)
    have h0 := congrFun (congrFun (placeIdem_smul_off hε hw hu) a) b
    rw [Matrix.smul_apply, smul_eq_mul, ← a3, Matrix.zero_apply] at h0
    have c1 : cA D (es PP) * cA D (es PP) = cA D (es PP) := by rw [← map_mul, a1]
    have c2 : cA D (es PP) * es PP = 0 := by rw [mul_comm, a2]
    refine ⟨?_, ?_⟩
    · linear_combination es PP * h0 - u a b * a1 - u a b * a2
    · linear_combination cA D (es PP) * h0 - u a b * c1 - u a b * c2
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).1
  · rw [map_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).2

end GlobalTheory.FinZeta.VacOff

open GlobalTheory.FinZeta.VacOff in

theorem GlobalTheory.FinZeta.levVec_vacFin : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ v ∉ finS R t, VacFin R.ψ (Vc D i) (Wc D i) v f := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h
  obtain ⟨hC, -, -, -, -, -, -, hlv, hpt, -, -⟩ := h
  have hθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := by
    have := hpt 1
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  refine ⟨hθ, fun v hv => ⟨hθ, ?_⟩⟩
  obtain ⟨hf₀, e, he, hth⟩ := hlv
  have hV : (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (frameLat (Vc D i) : Set _) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.baseLat_eq hC.lev i, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
  have hW : (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = (frameLat (Wc D i) : Set _) := by
    rw [← GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
    obtain ⟨c, -, -, -, h1, h2⟩ := hC.lev.βW i
    ext x
    constructor
    · intro hx
      simpa using h2 x hx
    · intro hx
      simpa using h1 x hx
  have hlat := hf₀.2.lat
  have hle : latO (Vc D i) (Wc D i) (frameLat (Vc D i) : Set _) (frameLat (Wc D i) : Set _) (fun u => u = v) ≤
      latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
    rw [hV, hW]
    exact GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  have hoff : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t, PP.under (𝓞 D.host.F) ≠ v := fun PP hPP h0 =>
    hv (Finset.mem_image.2 ⟨PP, hPP, h0⟩)
  have hz : ∀ u ∈ latO (Vc D i) (Wc D i) (frameLat (Vc D i) : Set _) (frameLat (Wc D i) : Set _) (fun u => u = v),
      ∀ a b, cA D e * u a b = 0 ∧ cA D (cA D e) * u a b = 0 := fun u hu a b => by
    obtain ⟨h1, h2⟩ := idemSum_mul_off he hoff hu a b
    rw [GlobalTheory.DualPairCheck.cA_cA]
    exact ⟨h2, h1⟩
  refine ⟨fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hth (2 • u)
      (hz _ (AddSubgroup.nsmul_mem _ hu 2)) (hlat.1 u (hle hu))
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hth u (hz u hu) (hlat.2 e' he' u (hle hu) hh)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDenseStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_submodule_dense : GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.LeviSubmoduleDense := by
  first | exact @GlobalTheory.LeviDense.leviSubmoduleDense | exact GlobalTheory.LeviDense.leviSubmoduleDense | (intros; apply GlobalTheory.LeviDense.leviSubmoduleDense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineVectorsInvertibleOnThetaFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedLineVectors_invertible_on_theta_functions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (L L' S : HSp D) (ζ : Fin L.rank → D.host.E) (ζ' : Fin L'.rank → D.host.E), IsLineVec L ζ → IsLineVec L' ζ' → ∀ l : Lnk L ζ L' ζ', l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram ∧ ∀ Φ₀, IsThetaFunO ψ S L' Φ₀ → ∃ Ξ, IsThetaFunO ψ L S Ξ ∧ Φ₀ = fun w => star (Ξ (l.κ S w)) := by
  first | exact @GlobalTheory.LinkInvTheta.link_inv_theta | exact GlobalTheory.LinkInvTheta.link_inv_theta | (intros; apply GlobalTheory.LinkInvTheta.link_inv_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralThetaLiftTermSumNeTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ThetaLiftBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_rat_height_le {D : D7} (W : HSp D) (h : GA D W) :
    ∃ γ ∈ GQ W, GlobalTheory.Grow.height W (γ * h) ≤ 2 * GlobalTheory.Grow.quotHeight W h := by
  have hq := GlobalTheory.Grow.one_le_quotHeight W h
  by_contra hne
  push_neg at hne
  have : 2 * GlobalTheory.Grow.quotHeight W h ≤ GlobalTheory.Grow.quotHeight W h :=
    (GlobalTheory.Grow.le_quotHeight_iff W).2 fun γ hγ => (hne γ hγ).le
  linarith

theorem bound_pow (c a b M q : ℝ) (A : ℕ) (ha : 1 ≤ a) (haM : a ≤ M) (hb : 1 ≤ b) (hbq : b ≤ 2 * q) :
    c * (a * b) ^ A ≤ max c 0 * (M * (2 * q)) ^ A := by
  have hX : a * b ≤ M * (2 * q) := mul_le_mul haM hbq (by linarith) (by linarith)
  have hXp : (a * b) ^ A ≤ (M * (2 * q)) ^ A := pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hX A
  exact (mul_le_mul_of_nonneg_right (le_max_left c 0) (pow_nonneg (mul_nonneg (by linarith) (by linarith)) A)).trans
    (mul_le_mul_of_nonneg_left hXp (le_max_right c 0))

theorem bound_mul (c M q f C' : ℝ) (A : ℕ) (hM : 0 ≤ M) (hq : 0 ≤ q) (hf : 0 ≤ f) (hF : f * q ^ A ≤ C') :
    max c 0 * (M * (2 * q)) ^ A * f ≤ max c 0 * (2 * M) ^ A * max C' 0 := by
  have e : max c 0 * (M * (2 * q)) ^ A * f = max c 0 * (2 * M) ^ A * (f * q ^ A) := by
    rw [mul_pow, mul_pow, mul_pow]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (hF.trans (le_max_left _ _))
    (mul_nonneg (le_max_right c 0) (pow_nonneg (by linarith) A))

theorem lintegral_ne_top : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → ∀ (Sg : GA D V × GA D W → ℝ≥0∞), (∀ n ∈ NI V C, n ∈ GQ V → ∀ a b, Sg (n * a, b) = Sg (a, b)) → (∀ γ ∈ GQ W, ∀ a b, Sg (a, γ * b) = Sg (a, b)) → ∀ (A : ℕ) (c : ℝ), (∀ a b, Sg (a, b) ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V a * GlobalTheory.Grow.height W b) ^ A)) → ∀ g : GA D V, ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤ := by
  intro D V W r C hC κ 𝓝 hκ h𝓝 ν 𝓕 hν h𝓕 F hF Sg h1 h2 A c hc g
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩).2
  obtain ⟨M, hM⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V
    (hK.image (f := fun k : NI V C => (k : GA D V) * g) (by fun_prop))
  obtain ⟨C', hC'⟩ := hF.2.2 A
  have hbound : ∀ n : NI V C, ∀ h, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ≤
      ENNReal.ofReal (max c 0 * (2 * M) ^ A * max C' 0) := by
    intro n h
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    obtain ⟨γ', hγ', hh⟩ := exists_rat_height_le W h
    have e1 : Sg (((γ * k : NI V C) : GA D V) * g, h) = Sg ((k : GA D V) * g, γ' * h) := by
      rw [Subgroup.coe_mul, mul_assoc, h1 _ γ.2 (Subgroup.mem_subgroupOf.1 hγ), h2 _ hγ']
    rw [e1]
    have hkM : GlobalTheory.Grow.height V ((k : GA D V) * g) ≤ M := hM _ ⟨k, hk, rfl⟩
    have hV1 := GlobalTheory.Grow.one_le_height V ((k : GA D V) * g)
    have hW1 := GlobalTheory.Grow.one_le_height W (γ' * h)
    have hq1 := GlobalTheory.Grow.one_le_quotHeight W h
    have hc1 := bound_pow c _ _ M (GlobalTheory.Grow.quotHeight W h) A hV1 hkM hW1 hh
    have hb := bound_mul c M (GlobalTheory.Grow.quotHeight W h) ‖F h‖ C' A (by linarith) (by linarith) (norm_nonneg _) (hC' h)
    calc Sg ((k : GA D V) * g, γ' * h) * ‖F h‖ₑ
        ≤ ENNReal.ofReal (max c 0 * (M * (2 * GlobalTheory.Grow.quotHeight W h)) ^ A) * ENNReal.ofReal ‖F h‖ := by
          rw [ofReal_norm_eq_enorm]
          exact mul_le_mul' ((hc _ _).trans (ENNReal.ofReal_le_ofReal hc1)) le_rfl
      _ = ENNReal.ofReal (max c 0 * (M * (2 * GlobalTheory.Grow.quotHeight W h)) ^ A * ‖F h‖) :=
          (ENNReal.ofReal_mul (mul_nonneg (le_max_right c 0)
            (pow_nonneg (mul_nonneg (by linarith) (by linarith)) A))).symm
      _ ≤ ENNReal.ofReal (max c 0 * (2 * M) ^ A * max C' 0) := ENNReal.ofReal_le_ofReal hb
  have hν𝓕 := (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W ν 𝓕 hν h𝓕).ne
  have hκ𝓝 := GlobalTheory.TowerCT.vol D V r C hC κ 𝓝 hκ h𝓝
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun n => lintegral_mono fun h => hbound n h)
  rw [setLIntegral_const, setLIntegral_const]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hν𝓕) hκ𝓝

end GlobalTheory.ThetaLiftBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIsoStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ → (∀ v, ContinuousOn (fun g => ρ g v) (UJset ε)) → (∀ k ∈ Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → S ≠ ⊥ → IsKStableOn ε ρ S → (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S) → ∃ Λ, IsKTypeOf ε ρ Λ S) ∧ ∀ (Λ : Fin n → ℝ) (S S' : Submodule ℂ H), IsKTypeOf ε ρ Λ S → IsKTypeOf ε ρ Λ S' → ∃ B : H →L[ℂ] H, (∀ k ∈ Kset ε, ∀ u, B (ρ k u) = ρ k (B u)) ∧ S.map (B : H →ₗ[ℂ] H) = S' := by
  first | exact @GlobalTheory.KTypeHighest.ktype_highest_weight | exact GlobalTheory.KTypeHighest.ktype_highest_weight | (intros; apply GlobalTheory.KTypeHighest.ktype_highest_weight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLatticeOfRationalMemCompletionAllPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt intAt latV latA)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lattice_of_rational_mem_completion_all_places : ∀ (D : D7) (S : HSp D) (L : Lat S), Submodule.IsLattice D.host.E L → ∀ z : Fin S.rank → D.host.E, (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True) → z ∈ L := by
  first | exact @GlobalTheory.RatLat.mem_of_mem_latV | exact GlobalTheory.RatLat.mem_of_mem_latV | (intros; apply GlobalTheory.RatLat.mem_of_mem_latV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfLevelDatumNeZeroTranslateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_of_levelDatum_ne_zero_translate : ∀ (D : D7) (S T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC T ΛT → IsFrame βT ΛT → T.rank ≤ S.rank → LT.Q = ∅ → IsIdemSum e Z → (∀ PP, PP ∈ Z ↔ PP ∈ LT.Pg ∨ PP ∈ Q) → ∀ g ∈ GfC T, ∀ x, levDatum S T βS βT LT Q m e x ≠ 0 → levDatum S T βS βT LT Q m e (actO S T 1 g x) ≠ 0 → ∃ k ∈ levG T βT LT, ∀ PP ∈ Z, projV T (PP.under (𝓞 D.host.F)) g = projV T (PP.under (𝓞 D.host.F)) k := by
  first | exact @GlobalTheory.SuppLev.supp_level | exact GlobalTheory.SuppLev.supp_level | (intros; apply GlobalTheory.SuppLev.supp_level <;> assumption)
end

