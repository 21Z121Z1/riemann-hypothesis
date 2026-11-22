import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0008
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SymplOInv

theorem sum_four_eq_trace {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (P : Matrix (Fin n) (Fin n) A)
    (Q : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a = (P * (y.map σ)ᵀ * Q * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Eq.symm ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

theorem sum_unitary {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (Q g : Matrix (Fin m) (Fin m) A)
    (P P' k : Matrix (Fin n) (Fin n) A) (hP : P * P' = 1) (hg : (g.map σ)ᵀ * Q * g = Q)
    (hk : (k.map σ)ᵀ * P' * k = P') (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ ((g * y * k) c b) * Q c d * (g * x * k) d a =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a := by
  have h1 : (P * (k.map σ)ᵀ * P') * k = 1 := by
    rw [Matrix.mul_assoc P, Matrix.mul_assoc P, hk, hP]
  have h2 : k * (P * (k.map σ)ᵀ * P') = 1 := mul_eq_one_comm.1 h1
  have hP' : P' * P = 1 := mul_eq_one_comm.1 hP
  have hk' : k * P * (k.map σ)ᵀ = P := by
    calc k * P * (k.map σ)ᵀ = k * P * (k.map σ)ᵀ * (P' * P) := by rw [hP', Matrix.mul_one]
      _ = (k * (P * (k.map σ)ᵀ * P')) * P := by simp only [Matrix.mul_assoc]
      _ = P := by rw [h2, Matrix.one_mul]
  have e : P * ((g * y * k).map σ)ᵀ * Q * (g * x * k) =
      (P * (k.map σ)ᵀ * ((y.map σ)ᵀ * ((g.map σ)ᵀ * Q * g) * x)) * k := by
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [sum_four_eq_trace, sum_four_eq_trace, e, hg, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc k, hk']
  simp only [Matrix.mul_assoc]

theorem hO_actO {D : D7} (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    hO S T (actO S T g h x) (actO S T g h y) = hO S T x y := by
  have h1 : S.gram⁻¹.map (incA D) * S.gram.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]
    exact Matrix.map_one _ (incA D).map_zero (incA D).map_one
  exact sum_unitary (cA D) (T.gram.map (incA D)) (mt T h) (S.gram⁻¹.map (incA D)) (S.gram.map (incA D)) (mt S g⁻¹)
    h1 h.2 (g⁻¹).2 x y

theorem symplO_actO : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T), symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y := by
  intro D S T g h x y
  unfold symplO
  rw [hO_actO]

end GlobalTheory.SymplOInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThAHeisEntireLinearInjective
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem thA_heis_entire_linear_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ φ : TF n g, GlobalTheory.SW.IsSB φ → (∀ (y : Matrix (Fin n) (Fin r) E) (z : Fin n → Fin g → ℂ), GlobalTheory.SW.IsSB (heisG X bas y φ) ∧ thA X bas idx (heisG X bas y φ) x z = cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (y b)) (pv X idx x (y b)))) * thA X bas idx φ x (fun b => z b + pv X idx x (y b))) ∧ Differentiable ℂ (thA X bas idx φ x) ∧ (∀ φ' : TF n g, GlobalTheory.SW.IsSB φ' → (∀ a b : ℂ, GlobalTheory.SW.IsSB (a • φ + b • φ') ∧ thA X bas idx (a • φ + b • φ') x = a • thA X bas idx φ x + b • thA X bas idx φ' x) ∧ (thA X bas idx φ x = thA X bas idx φ' x → φ = φ')) := by
  intro E _ _ _ r g n X bas idx hs hn x hd φ hφ
  refine ⟨fun y z => ?_, GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hφ hd, fun ψ hψ => ⟨fun a b => ?_, ?_⟩⟩
  · obtain ⟨h1, -, -, -, h2⟩ := (GlobalTheory.SW.heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ
    exact ⟨h1, h2 x hd z⟩
  · have h1 : GlobalTheory.SW.IsSB (a • φ) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ hφ hφ).2.1 a
    have h2 : GlobalTheory.SW.IsSB (b • ψ) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ hψ hψ).2.1 b
    refine ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ h1 h2).1, ?_⟩
    rw [GlobalTheory.SW.UnAct.thA_add idx hs hd h1 h2, GlobalTheory.SW.UnAct.thA_smul, GlobalTheory.SW.UnAct.thA_smul]
  · exact GlobalTheory.SW.UnAct.eq_of_thA_eq idx hs hd hφ hψ

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFiresIffThetaMultExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.ThetaFiresOfMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 1000000 in

theorem exists_isThetaMult_of_firesAt {R : RealDat D A Ks} {i : Fin D.R.m} {t : T}
    (h : ∀ x, FiresAt R i t x) : ∃ y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A)), IsThetaMult R i t y :=
  GlobalTheory.ThetaFiresLinear.exists_linear_lift (lowT (R.MW i (sg0 D A))) (R.Wall i (sg0 D A)) (R.νV i t) (R.fdV i t)
    (kernel R i t) (R.ptP i t) (GlobalTheory.ThetaFiresLinear.kernelL R i t)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t))
    (fun _ _ _ => rfl) (fun _ => rfl) (R.ioP i) (R.extV i t) h

end GlobalTheory.ThetaFiresOfMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRingOfIntegersActionSumEmbeddingsEigenspace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section
namespace GlobalTheory.UPel.HT.LieType

open Polynomial in

theorem toLin'_map_aeval_int {F : Type} [Field F] [NumberField F] {g : ℕ}
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (x : 𝓞 F) (p : ℤ[X]) :
    Matrix.toLin' (φ (aeval x p)) = aeval (Matrix.toLin' (φ x)) (p.map (algebraMap ℤ ℂ)) := by
  have h1 : φ (aeval x p) = aeval (φ x) p := (Polynomial.aeval_algHom_apply φ.toIntAlgHom x p).symm
  rw [h1, ← Polynomial.aeval_map_algebraMap ℂ (φ x) p]
  exact (Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)) (φ x) _).symm

open Polynomial in

theorem trace_eq_sum_finrank_eigSp : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ)
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F),
    (φ c).trace = ∑ τ : F →+* ℂ, (Module.finrank ℂ (eigSp φ τ) : ℂ) * τ (c : F) := by
  intro F _ _ g φ c
  classical
  obtain ⟨α, hinj, ⟨f, hf0, hfmap⟩, hmul⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := F) (F := ℂ)
    (RingHom.id ℂ) (fun τ => τ.comp (algebraMap (𝓞 F) F)) (fun _ _ => rfl)
  simp only [RingHom.comp_apply] at hinj hfmap
  set L : Module.End ℂ (Fin g → ℂ) := Matrix.toLin' (φ α) with hL

  have hLf : aeval L (∏ τ : F →+* ℂ, (X - C (τ ((α : 𝓞 F) : F)))) = 0 := by
    rw [← hfmap, ← algebraMap_int_eq, hL, ← toLin'_map_aeval_int, hf0, map_zero, map_zero]
  have hss : L.IsSemisimple := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero ?_ hLf
    exact (Polynomial.separable_prod_X_sub_C_iff'.2 fun x _ y _ h => hinj h).squarefree

  have hW : ∀ τ : F →+* ℂ, eigSp φ τ = L.eigenspace (τ ((α : 𝓞 F) : F)) := by
    intro τ
    ext u
    rw [Module.End.mem_eigenspace_iff, mem_eigSp, hL, Matrix.toLin'_apply]
    refine ⟨fun h => h α, fun h c' => ?_⟩
    obtain ⟨N, p, hN, hp⟩ := hmul c'
    have hNC : (N : ℂ) ≠ 0 := Int.cast_ne_zero.2 hN
    have key : φ ((N : 𝓞 F) * c') *ᵥ u = τ (((N : 𝓞 F) * c' : 𝓞 F) : F) • u := by
      rw [hp, ← Matrix.toLin'_apply, toLin'_map_aeval_int]
      by_cases hu : u = 0
      · simp [hu]
      have hev : L.HasEigenvector (τ ((α : 𝓞 F) : F)) u :=
        ⟨Module.End.mem_eigenspace_iff.2 (by rw [hL, Matrix.toLin'_apply]; exact h), hu⟩
      rw [← hL, Module.End.aeval_apply_of_hasEigenvector hev]
      congr 1
      have h2 : (τ.comp (algebraMap (𝓞 F) F)) (aeval α p) = aeval ((τ.comp (algebraMap (𝓞 F) F)) α) p :=
        (Polynomial.aeval_algHom_apply (τ.comp (algebraMap (𝓞 F) F)).toIntAlgHom α p).symm
      simp only [RingHom.comp_apply] at h2
      rw [RingOfIntegers.coe_eq_algebraMap, h2, Polynomial.eval_map_algebraMap]
    have e1 : φ ((N : 𝓞 F) * c') = (N : ℂ) • φ c' := by
      rw [map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    have e2 : τ (((N : 𝓞 F) * c' : 𝓞 F) : F) = (N : ℂ) * τ (c' : F) := by
      simp
    rw [e1, e2, Matrix.smul_mulVec, mul_smul] at key
    exact smul_right_injective _ hNC key

  have hind : iSupIndep (eigSp φ) := by
    have := iSupIndep.comp (Module.End.eigenspaces_iSupIndep L) hinj
    convert this using 1
    funext τ
    exact hW τ
  have htop : ⨆ τ, eigSp φ τ = ⊤ := by
    rw [eq_top_iff, ← hss.iSup_eigenspace_eq_top, iSup_le_iff]
    intro m
    by_cases hm : L.eigenspace m = ⊥
    · rw [hm]; exact bot_le
    · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      have hev : L.HasEigenvector m u := ⟨hu, hu0⟩
      have h0 := Module.End.aeval_apply_of_hasEigenvector hev
        (p := ∏ τ : F →+* ℂ, (X - C (τ ((α : 𝓞 F) : F))))
      rw [hLf, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h0
      have hroot := h0.resolve_right hu0
      rw [eval_prod, Finset.prod_eq_zero_iff] at hroot
      obtain ⟨τ, -, hτ⟩ := hroot
      rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hτ
      rw [hτ, ← hW τ]
      exact le_iSup (eigSp φ) τ
  have hint : DirectSum.IsInternal (eigSp φ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have hmaps : ∀ τ, Set.MapsTo (Matrix.toLin' (φ c)) (eigSp φ τ) (eigSp φ τ) := by
    intro τ u hu
    have hu' := (mem_eigSp φ τ u).1 hu
    show Matrix.toLin' (φ c) u ∈ eigSp φ τ
    rw [Matrix.toLin'_apply, hu' c]
    exact (eigSp φ τ).smul_mem _ hu
  rw [← Matrix.trace_toLin'_eq, LinearMap.trace_eq_sum_trace_restrict hint hmaps]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hres : (Matrix.toLin' (φ c)).restrict (hmaps τ) = τ (c : F) • LinearMap.id := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have hv := (mem_eigSp φ τ v).1 v.2
    show Matrix.toLin' (φ c) (v : Fin g → ℂ) = τ (c : F) • (v : Fin g → ℂ)
    rw [Matrix.toLin'_apply, hv c]
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

end GlobalTheory.UPel.HT.LieType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypeCharacterConjugateInverse
section
open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.TypeCharacterConjugateInverse

theorem toSquareBlock_mul_of_blockTriangular {r : ℕ} {k : Type} [Field k] {A B : Matrix (Fin r) (Fin r) k}
    {b : Fin r → Fin r} (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (c : Fin r)
    [Fintype {i : Fin r // b i = c}] :
    A.toSquareBlock b c * B.toSquareBlock b c = (A * B).toSquareBlock b c := by
  classical
  ext i j
  simp only [Matrix.toSquareBlock_def, Matrix.mul_apply, Matrix.of_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun l => b l = c) (p := fun l => b l = c) (by simp)
    (fun l => A i.1 l * B l j.1)]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => ?_
  have hl' : b l ≠ c := by simpa using hl
  rcases lt_or_gt_of_ne hl' with h | h
  · rw [hA (show b l < b i.1 by rw [i.2]; exact h), zero_mul]
  · rw [hB (show b j.1 < b l by rw [j.2]; exact h), mul_zero]

theorem blockTriangular_inv {r : ℕ} {k : Type} [Field k] {b : Fin r → Fin r} (z : GL (Fin r) k)
    (hz : (z : Matrix (Fin r) (Fin r) k).BlockTriangular b) :
    ((z⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).BlockTriangular b := by
  letI := z.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hz

theorem toSquareBlock_mul_inv {r : ℕ} {k : Type} [Field k] {b : Fin r → Fin r} (z : GL (Fin r) k)
    (hz : (z : Matrix (Fin r) (Fin r) k).BlockTriangular b) (c : Fin r)
    [Fintype {i : Fin r // b i = c}] [DecidableEq {i : Fin r // b i = c}] :
    (z : Matrix (Fin r) (Fin r) k).toSquareBlock b c *
      ((z⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).toSquareBlock b c = 1 := by
  rw [toSquareBlock_mul_of_blockTriangular hz (blockTriangular_inv z hz), ← Units.val_mul, mul_inv_cancel,
    Units.val_one]
  ext i j
  simp [Matrix.toSquareBlock_def, Matrix.one_apply, Subtype.ext_iff]

theorem typeChar_conj_inv : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (r : ℕ) (s : LevelCuspCharacters.SSParam p K r),
    (∀ x y : GL (Fin r) (ZMod p), IsConj x y → LevelCuspCharacters.typeChar s x = LevelCuspCharacters.typeChar s y) ∧
    ∀ x : GL (Fin r) (ZMod p),
      LevelCuspCharacters.typeChar (⟨s.1, fun c => (s.2 c)⁻¹⟩ : LevelCuspCharacters.SSParam p K r) x = LevelCuspCharacters.typeChar s x⁻¹ := by
  intro p _ K _ r s
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    unfold LevelCuspCharacters.typeChar
    congr 1
    letI := Fintype.ofFinite (GL (Fin r) (ZMod p))
    refine Fintype.sum_equiv (Equiv.mulLeft c) _ _ fun y => ?_
    have h : (Equiv.mulLeft c y)⁻¹ * (c * x * c⁻¹) * (Equiv.mulLeft c y) = y⁻¹ * x * y := by
      simp only [Equiv.coe_mulLeft]
      group
    rw [h]
  · unfold LevelCuspCharacters.typeChar
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    have h : y⁻¹ * x⁻¹ * y = (y⁻¹ * x * y)⁻¹ := by group
    rw [h]
    generalize y⁻¹ * x * y = z
    by_cases hz : (z : Matrix (Fin r) (Fin r) (ZMod p)).BlockTriangular s.1
    · rw [if_pos hz, if_pos (blockTriangular_inv z hz)]
      refine Finset.prod_congr rfl fun c _ => ?_
      exact GlobalTheory.T.greenCuspidalCharacterCoxeterTorus_inv_eq_at_inverse p K _ (s.2 c) _ _ (toSquareBlock_mul_inv z hz c.1)
    · rw [if_neg hz, if_neg fun h' => hz (by simpa using blockTriangular_inv z⁻¹ h')]

end GlobalTheory.TypeCharacterConjugateInverse
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
open scoped Pointwise

namespace GlobalTheory.TypePlaces

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem not_isConjPl : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (Pl D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl PP PP' := by
  intro D Pb Pg hPg PP hP PP' hP' hc
  obtain ⟨k, hk⟩ := (hPg PP).1 hP
  obtain ⟨k', hk'⟩ := (hPg PP').1 hP'
  have hle : D.host.conj • PP.asIdeal ≤ PP'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hzv, hz⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext
      ((hz.trans (star_eq_conj D _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
    exact e ▸ hzv
  have hmax : (D.host.conj • PP.asIdeal).IsMaximal := by
    have := PP.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => PP.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have heq : D.host.conj • PP.asIdeal = PP'.asIdeal := hmax.eq_of_le PP'.isPrime.ne_top hle
  obtain ⟨ho, hm⟩ := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP
    (Pb.overP hk)).2.2.2 (Pb.pb k) (Pb.pb_over k) PP' ((GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj PP PP').2 heq)
  have hkk : k ≠ k' := by
    rintro rfl
    exact hm.1 hk hk'
  have ho' := Pb.overP hk'
  have hne : D.host.g k ≠ D.host.g k' := by
    have := D.host.g_ne
    fin_cases k <;> fin_cases k'
    · exact absurd rfl hkk
    · exact this
    · exact this.symm
    · exact absurd rfl hkk
  have hco : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.g k' : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime k) (D.host.g_prime k')).2 hne)
  obtain ⟨a, b, hab⟩ := hco
  apply PP'.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ ho) (Ideal.mul_mem_left _ _ ho')

end GlobalTheory.TypePlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorDualLabelStatement
section
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_divisor_dual_label : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (d : List ℤ) (g : GL (Fin n) L), (∀ x, Valued.v (σ x) = Valued.v x) → d.length = n → g ∈ GU σ n → HasDiv (intL L) d g → HasDiv (intL L) (dualLab d) g := by
  first | exact @GlobalTheory.DualDivU.hasDiv_dualLab | exact GlobalTheory.DualDivU.hasDiv_dualLab | (intros; apply GlobalTheory.DualDivU.hasDiv_dualLab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationRingPrimeDominanceStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_ring_prime_dominance : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (A : Type) [CommRing A] [Algebra O A] [Algebra.FiniteType O A] (K : Type) [Field K] [Algebra A K] [Algebra O K] [IsScalarTower O A K], Function.Injective (algebraMap O K) → (∀ x : K, ∃ a b : A, algebraMap A K b ≠ 0 ∧ x * algebraMap A K b = algebraMap A K a) → ∀ p : Ideal A, p.IsPrime → RingHom.ker (algebraMap A K) ≤ p → (maximalIdeal O).map (algebraMap O A) ≤ p → ∀ d : ℕ, (d : Cardinal) ≤ Algebra.trdeg O K → ∃ (T : CDVR) (f : A →+* T.V) (ψ : K →+* T.Fr), (algebraMap T.V T.Fr).comp f = ψ.comp (algebraMap A K) ∧ IsLocalHom (f.comp (algebraMap O A)) ∧ TrdegGe ((maximalIdeal T.V).comap f).ResidueField d := by
  first | exact @GlobalTheory.GenericCentre.exists_cdvr_centred_generic | exact GlobalTheory.GenericCentre.exists_cdvr_centred_generic | (intros; apply GlobalTheory.GenericCentre.exists_cdvr_centred_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPSubTwoMulUnit
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem eq_of_sq_mul_eq_cube {α : Type*} [LinearOrderedCommGroupWithZero α] {a b c : α} (hc : c ≠ 0)
    (ha : a ≤ c) (hb : b ≤ c) (h : a ^ 2 * b = c ^ 3) : a = c := by
  by_contra hne
  have hlt : a < c := lt_of_le_of_ne ha hne
  have hc0 : 0 < c := zero_lt_iff.mpr hc
  have h1 : a ^ 2 * b ≤ a ^ 2 * c := by gcongr
  have h2 : a ^ 2 < c ^ 2 := pow_lt_pow_left₀ hlt zero_le' two_ne_zero
  have h3 : a ^ 2 * c < c ^ 2 * c := mul_lt_mul_of_pos_right h2 hc0
  have h4 : c ^ 2 * c = c ^ 3 := by rw [pow_succ c 2]
  rw [h4] at h3
  rw [h] at h1
  exact lt_irrefl _ (lt_of_le_of_lt h1 h3)

theorem natCast_mul_intCast_mul_mem (L : PeriodPair) {N : ℕ} {z : ℂ} (hN : (N : ℂ) * z ∈ L.lattice) (k : ℤ) :
    (N : ℂ) * ((k : ℂ) * z) ∈ L.lattice := by
  have e : (N : ℂ) * ((k : ℂ) * z) = k • ((N : ℂ) * z) := by rw [zsmul_eq_mul]; ring
  rw [e]
  exact L.lattice.smul_mem k hN

theorem mem_lattice_of_coprime (L : PeriodPair) {N k : ℕ} (hNk : Nat.Coprime N k) {z : ℂ}
    (hN : (N : ℂ) * z ∈ L.lattice) (hk : (k : ℂ) * z ∈ L.lattice) : z ∈ L.lattice := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hNk
  have hab' : (a : ℂ) * (N : ℂ) + (b : ℂ) * (k : ℂ) = 1 := by exact_mod_cast hab
  have e : z = a • ((N : ℂ) * z) + b • ((k : ℂ) * z) := by
    rw [zsmul_eq_mul, zsmul_eq_mul]
    linear_combination (-z) * hab'
  rw [e]
  exact L.lattice.add_mem (L.lattice.smul_mem a hN) (L.lattice.smul_mem b hk)

theorem weierstrassP_sub_two_mul_unit : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ¬ 3 ∣ N → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → 2 * z ∉ L.lattice ∧ V.valuation (L.weierstrassP z - L.weierstrassP (2 * z)) = V.valuation u ^ 2 := by
  intro L β u V N hβ hβim hu hN hodd h3 z hz hNz
  have cop2 : Nat.Coprime N 2 := (Nat.coprime_two_left.mpr hodd).symm
  have cop3 : Nat.Coprime N 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  have h2z : 2 * z ∉ L.lattice := fun h =>
    hz (mem_lattice_of_coprime L cop2 hNz (by push_cast; exact h))
  have h3z : 3 * z ∉ L.lattice := fun h =>
    hz (mem_lattice_of_coprime L cop3 hNz (by push_cast; exact h))
  have hN2z : (N : ℂ) * (2 * z) ∈ L.lattice := by
    simpa using natCast_mul_intCast_mul_mem L hNz 2
  have hN3z : (N : ℂ) * (3 * z) ∈ L.lattice := by
    simpa using natCast_mul_intCast_mul_mem L hNz 3
  refine ⟨h2z, ?_⟩
  have e1 : 2 * z - z = z := by ring
  have e2 : 2 * z + z = 3 * z := by ring
  have hd := GlobalTheory.T.weierstrassP_sub_sq_mul_add_sub_eq_neg_deriv_mul L (2 * z) z h2z hz (by rw [e1]; exact hz) (by rw [e2]; exact h3z)
  rw [e1, e2] at hd
  have d1 := GlobalTheory.T.valuation_derivWeierstrassP_oddTorsion L β u V N hβ hβim hu hN hodd z hz hNz
  have d2 := GlobalTheory.T.valuation_derivWeierstrassP_oddTorsion L β u V N hβ hβim hu hN hodd (2 * z) h2z hN2z
  have m1 := (GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hβ hβim hu hN z (2 * z) hz h2z hNz hN2z).2
  have m2 := (GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hβ hβim hu hN (3 * z) z h3z hz hN3z hNz).2
  have hv : V.valuation u ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at hu
    exact latticeCurve_Δ_ne_zero L ((Valuation.zero_iff _).mp hu.symm)
  have hv2 : 0 < V.valuation u ^ 2 := zero_lt_iff.mpr (pow_ne_zero 2 hv)
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀, map_pow, div_le_one₀ hv2] at m1 m2
  have hval := congrArg V.valuation hd
  rw [map_mul, map_pow, Valuation.map_neg, map_mul, d1, d2,
    Valuation.map_sub_swap V.valuation (L.weierstrassP (2 * z))] at hval
  refine eq_of_sq_mul_eq_cube (pow_ne_zero 2 hv) m1 m2 ?_
  rw [hval, ← pow_add, ← pow_mul]

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingBirigidifiedTrivialOnAxesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_birigidified_trivial_on_axes : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), (Out.WeilIs (G2 A) P n (lift u 1) (lift v 1) c → c = 1) ∧ (Out.WeilIs (G2 A) P n (lift 1 u) (lift 1 v) c → c = 1) := by
  first | (exact @GlobalTheory.AxisPairing.axes) | (exact GlobalTheory.AxisPairing.axes) | (intros; apply GlobalTheory.AxisPairing.axes  <;> assumption)
end

