import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0779
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0780
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0717
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedBundleOfDescentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_birigidified_bundle_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsMonHom ψ → ∀ (m : ℕ) (P₀ : LB (G2 A').left), P₀.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent) | (exact GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflectionStatement
section
open Matrix Formalism.IndefR.Datum
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_comm_quasiReflection : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), Gᴴ = G → G.det ≠ 0 → ∀ x : Fin n → ℂ, star x ⬝ᵥ G *ᵥ x ≠ 0 → ∃ s, IsCartanInv G s ∧ ∀ c : ℂ, s * (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) = (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) * s := by
  first | exact @GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection | exact GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection | (intros; apply GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCbData
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

noncomputable section

namespace GlobalTheory.DefRowsCB

theorem exists_cbData : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (m : ℕ) (c : Fin (m + 1) → ℕ) (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ) (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K) (t : Fin m → InfinitePlace K → ℝ), (∀ i v, IsUnit (Xc i v).det) → (∀ j v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v ((Kj j).mulVec x) ^ 2 ≤ Real.exp (t j v) * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc) v x ^ 2) → ∃ cb : CBData Xc Kj, ∀ j v, Real.log (cb.sq j v) ≤ t j v := by
  intro K _ _ _ _ m c Xc Kj t hX h
  refine ⟨{
    AA := fun _ => Unit
    Cl := fun _ _ => Unit
    W := fun i _ => EuclideanSpace ℂ (Fin (c i))
    γ := fun _ _ => 1
    Φ := fun i v x _ => WithLp.toLp 2 ((Xc i v)⁻¹.mulVec x)
    ε := fun _ _ _ _ => 1
    T := fun j v _ _ => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
      ((Xc j.succ v)⁻¹ * (Kj j).map v.embedding * Xc j.castSucc v))
    hcl := fun _ => 1
    tmax := fun j v => Real.exp (t j v)
    hyp := ⟨hX, fun _ _ => ⟨one_pos, le_rfl⟩, ?_, ?_, fun _ _ _ _ => norm_one, ?_,
      fun _ _ => (Real.exp_pos _).le, fun _ _ => by simp⟩ }, ?_⟩
  · intro i v x
    rw [Formalism.DivisionValues.fnorm, Formalism.HN.PlaceOperatorNorms.cnorm_eq]
    simp
  · intro j v x
    funext q
    simp only [Formalism.DimensionVariation.liftOp, Fintype.sum_sigma, Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one,
      mul_one, one_smul, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX _ v), Matrix.mul_one]
  · intro j v _ _
    have key := Formalism.BasicNotions.opNormAt_sq_le (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) (hX _) v (IsTotallyComplex.isComplex v)
      (Matrix.mulVecLin (Kj j)) (Real.exp (t j v)) (Real.exp_pos _).le (fun x => by
        rw [← Formalism.BasicNotions.normAt_sq_eq_majAt, ← Formalism.BasicNotions.normAt_sq_eq_majAt]
        exact h j v x)
    have hm : LinearMap.toMatrix (Pi.basisFun K (Fin (c j.castSucc))) (Pi.basisFun K (Fin (c j.succ)))
        (Matrix.mulVecLin (Kj j)) = Kj j := by
      ext a b
      simp [LinearMap.toMatrix_apply]
    have e : Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
        (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) =
        ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((Xc j.succ v)⁻¹ *
          (LinearMap.toMatrix (Pi.basisFun K (Fin (c j.castSucc))) (Pi.basisFun K (Fin (c j.succ)))
            (Matrix.mulVecLin (Kj j))).map v.embedding * Xc j.castSucc v))‖ := rfl
    rw [e, hm] at key
    exact key
  · intro j v
    show Real.log (Formalism.DimensionVariation.cbSq (Fintype.card Unit) (Fintype.card Unit) 1 1 (Real.exp (t j v))) ≤ t j v
    simp [Formalism.DimensionVariation.cbSq]

end GlobalTheory.DefRowsCB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonHermitianGramDetTwoVectorsNe
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GramVec

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}
  {J : Matrix (Fin M) (Fin M) E}

theorem hE_add_smul_right (z u v : Fin M → E) (c : E) :
    hE σ J z (u + c • v) = hE σ J z u + c * hE σ J z v := by
  simp only [hE, Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_add_smul_left (z u v : Fin M → E) (c : E) :
    hE σ J (u + c • v) z = hE σ J u z + σ c * hE σ J v z := by
  simp only [hE, Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, map_add, map_mul, RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_add_smul_self (u v : Fin M → E) (c : E) :
    hE σ J (u + c • v) (u + c • v) =
      hE σ J u u + c * hE σ J u v + σ c * hE σ J v u + σ c * c * hE σ J v v := by
  rw [hE, GlobalTheory.HermLineZeros.hform_expand]
  rfl

theorem hE_single (i j : Fin M) : hE σ J (Pi.single i 1) (Pi.single j 1) = J i j :=
  GlobalTheory.HermLineZeros.hform_single _ J i j

theorem hermitianGramDetTwoVectors_comm (x z : Fin M → E) : gram2E σ J x z = gram2E σ J z x := by
  unfold gram2E; ring

noncomputable def gramPoly (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (z a b : Fin M → E) : Polynomial E :=
  Polynomial.C (hE σ J z z) * (Polynomial.C (hE σ J a a) + Polynomial.X * Polynomial.C (hE σ J a b + hE σ J b a)
      + Polynomial.X ^ 2 * Polynomial.C (hE σ J b b))
    - (Polynomial.C (hE σ J z a) + Polynomial.X * Polynomial.C (hE σ J z b))
      * (Polynomial.C (hE σ J a z) + Polynomial.X * Polynomial.C (hE σ J b z))

theorem hermitianGramDetTwoVectors_eval_line (z a b : Fin M → E) (t : E) (ht : σ t = t) :
    gram2E σ J z (a + t • b) = (gramPoly σ J z a b).eval t := by
  unfold gram2E gramPoly
  rw [hE_add_smul_self, hE_add_smul_right, hE_add_smul_left, ht]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  ring

section CM

variable [NumberField F] [NumberField E]

theorem exists_gram2E_ne (h : IsCMExt F E σ) (hM : 2 ≤ M) (hJ : IsHermND σ J)
    (z : Fin M → E) (hz : hE σ J z z ≠ 0) : ∃ w, gram2E σ J z w ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne h
  set a : Fin M → E := fun i => hE σ J (Pi.single i 1) z
  set b : Fin M → E := fun j => hE σ J z (Pi.single j 1)
  have hdiag : ∀ i, hE σ J z z * J i i - b i * a i = 0 := fun i => by
    have := hc (Pi.single i 1)
    simpa [gram2E, hE_single] using this
  have key : hE σ J z z • J = Matrix.vecMulVec a b := by
    ext i j
    have e1 := hc (Pi.single i 1 + (1 : E) • Pi.single j 1)
    have e2 := hc (Pi.single i 1 + d • Pi.single j 1)
    simp only [gram2E, hE_add_smul_self, hE_add_smul_right, hE_add_smul_left, hE_single,
      map_one] at e1 e2
    have e0i := hdiag i
    have e0j := hdiag j
    have : (d - σ d) * (hE σ J z z * J i j - a i * b j) = 0 := by
      simp only [a, b] at e0i e0j ⊢
      linear_combination e2 - e0i - σ d * d * e0j - σ d * (e1 - e0i - e0j)
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (sub_eq_zero.1 h0).symm hd
    · simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
      exact sub_eq_zero.1 h0
  have hdet : (hE σ J z z • J).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hz) hJ.2
  have hunit : IsUnit (hE σ J z z • J) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hr := Matrix.rank_of_isUnit _ hunit
  have hle : (Matrix.vecMulVec a b).rank ≤ 1 := by
    rw [Matrix.vecMulVec_eq Unit]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
  rw [key, Fintype.card_fin] at hr
  omega

end CM

end GlobalTheory.GramVec

open GlobalTheory.GramVec in
theorem GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → E, gram2E σ J x w ≠ 0 ∧ gram2E σ J w y ≠ 0 := by
  intro F E _ _ _ _ _ σ h M J hM hJ x y hx hy
  obtain ⟨w0, h0⟩ := exists_gram2E_ne h hM hJ x hx
  obtain ⟨w1, h1⟩ := exists_gram2E_ne h hM hJ y hy
  set Px := gramPoly σ J x w0 (w1 - w0)
  set Py := gramPoly σ J y w0 (w1 - w0)
  have hPx : Px ≠ 0 := by
    intro h0'
    apply h0
    have := hermitianGramDetTwoVectors_eval_line (σ := σ) (J := J) x w0 (w1 - w0) 0 (map_zero σ)
    rw [zero_smul, add_zero] at this
    rw [this]; change Polynomial.eval 0 Px = 0; rw [h0', Polynomial.eval_zero]
  have hPy : Py ≠ 0 := by
    intro h1'
    apply h1
    have := hermitianGramDetTwoVectors_eval_line (σ := σ) (J := J) y w0 (w1 - w0) 1 (map_one σ)
    rw [one_smul, add_sub_cancel] at this
    rw [this]; change Polynomial.eval 1 Py = 0; rw [h1', Polynomial.eval_zero]
  have hfin : {f : F | Px.IsRoot (algebraMap F E f) ∨ Py.IsRoot (algebraMap F E f)}.Finite := by
    have := ((Polynomial.finite_setOf_isRoot hPx).union (Polynomial.finite_setOf_isRoot hPy)).preimage
      (FaithfulSMul.algebraMap_injective F E).injOn
    exact this
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨f, hf⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, Polynomial.IsRoot.def] at hf
  have hfix : σ (algebraMap F E f) = algebraMap F E f := σ.commutes f
  refine ⟨w0 + algebraMap F E f • (w1 - w0), ?_, ?_⟩
  · rw [hermitianGramDetTwoVectors_eval_line _ _ _ _ hfix]; exact hf.1
  · rw [hermitianGramDetTwoVectors_comm, hermitianGramDetTwoVectors_eval_line _ _ _ _ hfix]; exact hf.2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetUnitaryHermitianRealStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_set_unitary_hermitian_real : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ u : Fin M → K ⊗[F] E, hR K σ J u u = 0 → u = 0) → ∃ C : Set (K ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (K ⊗[F] E), Formalism.UG.cT (sigR K σ) g * JR K J * g = JR K J → ∀ i j, g i j ∈ C := by
  first | exact @GlobalTheory.AnisoCpt.exists_isCompact_entries_of_anisotropic | exact GlobalTheory.AnisoCpt.exists_isCompact_entries_of_anisotropic | (intros; apply GlobalTheory.AnisoCpt.exists_isCompact_entries_of_anisotropic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroup
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.FinConj

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem finEmb_eq_finGL (E : Type) [Field E] [NumberField E] (a : ℕ) (l : GL (Fin a) (Af E)) :
    finEmb E a l = finGL E a l := by
  have k1 : ∀ (c : Ad E) (x y : Af E), (c - sFin E y + sFin E x).1 = c.1 - 0 + 0 := fun _ _ _ => rfl
  have k2 : ∀ (c : Ad E) (x y : Af E), (c - sFin E y + sFin E x).2 = c.2 - y + x := fun _ _ _ => rfl
  apply (AdelicGLn.prodEquiv E a).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · rw [AdelicGLn.prodEquiv_apply_fst]
    change (1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j = ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (sFin E) ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) + sFin E (l i j)).1
    rw [k1, sub_zero, add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rfl
    · rfl
  · rw [AdelicGLn.prodEquiv_apply_snd]
    change (l : Matrix (Fin a) (Fin a) (Af E)) i j = ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (sFin E) ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) + sFin E (l i j)).2
    rw [k2, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rw [adele_one_snd, sub_self, zero_add]
    · rw [adele_zero_snd, sub_self, zero_add]

theorem unip_eq_unipGL (E : Type) [Field E] [NumberField E] (a r : ℕ) (z : BlockIx a r → Ad E) :
    (unip z : GA E a) = unipGL z := Units.ext rfl

theorem exists_conj_unip_mem :
    ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ ω : Set (GA E a), IsCompact ω →
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
      ∀ z : BlockIx a r → Ad E, (∀ p, (z p).1 = 0) →
      (∀ p, ∃ c ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, (z p).2 = (M : Af E) * c) →
      ∃ l ∈ L, (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k)⁻¹ * unip z *
        (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k) = finGL E a l := by
  intro E _ _ a r L hL ω hω
  set U : Subgroup (AdelicGLn.integralFiniteGL E a) := L.comap (AdelicGLn.integralFiniteGL E a).subtype
  have hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL E a)) := hL.preimage continuous_subtype_val
  obtain ⟨M, hM, h⟩ := exists_natCast_conj_unipGL_mem (K := E) (n := a) U hU hω r
  refine ⟨M, hM, fun b hb ρ hρ k hk z hz1 hz2 => ?_⟩
  obtain ⟨u, hu⟩ := h b hb ρ hρ k hk z hz1 hz2
  refine ⟨((u : AdelicGLn.integralFiniteGL E a) : GL (Fin a) (Af E)), u.2, ?_⟩
  rw [unip_eq_unipGL, ← finEmb_eq_finGL]
  exact hu

end GlobalTheory.FinConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocalStatement
section
open IsLocalRing GlobalTheory.Toroidal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_etaleCompletion_to_complete_local : ∀ (O R' E Ω : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [Field Ω] (φ' : O →+* R') (ψ : O →+* E) (u' : R' →+* Ω) (v : E →+* Ω), IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified → IsAdicComplete (maximalIdeal E) E → IsLocalHom ψ → RingHom.ker u' = maximalIdeal R' → RingHom.ker v = maximalIdeal E → v.comp ψ = u'.comp φ' → (∀ r : R', u' r ∈ v.range) → ∃ b : R' →+* E, b.comp φ' = ψ ∧ v.comp b = u' := by
  first | exact @GlobalTheory.EtaleCompletionLift.exists_extension | exact GlobalTheory.EtaleCompletionLift.exists_extension | (intros; apply GlobalTheory.EtaleCompletionLift.exists_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusMatrixQuasiLogarithmBasisStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_matrix_quasiLogarithm_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∃ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, ∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
  first | exact @GlobalTheory.QLog.exists_frob_matrix | exact GlobalTheory.QLog.exists_frob_matrix | (intros; apply GlobalTheory.QLog.exists_frob_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem f_eq_of_pt_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z Y : Scheme.{0}} {x x' : Pt A B L M Z} (h : x = x') (p : Y ⟶ pullback A.hom x.t)
    (q : Y ⟶ pullback A.hom x'.t) (h1 : p ≫ pullback.fst _ _ = q ≫ pullback.fst _ _)
    (h2 : p ≫ pullback.snd _ _ = q ≫ pullback.snd _ _) : p ≫ x.f = q ≫ x'.f := by
  subst h
  rw [pullback.hom_ext h1 h2]

theorem exists_glue_data : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (x : ∀ i, HomGlue.Pt A B L M (𝒰.X i)), (∀ i j (T : Scheme.{0}) (b : T ⟶ 𝒰.X i) (c : T ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → (x i).map hL hM b = (x j).map hL hM c) → ∃ (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left), ∀ i, 𝒰.f i ≫ t = (x i).t ∧ ∀ e : pullback A.hom (x i).t ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = pullback.fst _ _ → e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝒰.f i → e ≫ f = (x i).f := by
  intro S A B _ _ L M hL hM Z 𝒰 x hx
  have hxt : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (x i).t = pullback.snd (𝒰.f i) (𝒰.f j) ≫ (x j).t :=
    fun i j => congrArg Pt.t (hx i j _ _ _ pullback.condition)
  obtain ⟨t, ht⟩ : ∃ t : Z ⟶ S, ∀ i, 𝒰.f i ≫ t = (x i).t :=
    ⟨_, fun i => 𝒰.ι_glueMorphisms _ hxt i⟩
  have c1 : ∀ i, pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.snd A.hom t = pullback.snd (pullback.snd A.hom t) (𝒰.f i) ≫ 𝒰.f i := fun i => pullback.condition
  have hw : ∀ i, (pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.fst A.hom t) ≫ A.hom = pullback.snd (pullback.snd A.hom t) (𝒰.f i) ≫ (x i).t := by
    intro i
    rw [Category.assoc, pullback.condition, ← Category.assoc, c1, Category.assoc, ht]
  have hu1 : ∀ i, pullback.lift _ _ (hw i) ≫ pullback.fst A.hom (x i).t = pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.fst A.hom t :=
    fun i => pullback.lift_fst _ _ _
  have hu2 : ∀ i, pullback.lift _ _ (hw i) ≫ pullback.snd A.hom (x i).t = pullback.snd (pullback.snd A.hom t) (𝒰.f i) := fun i => pullback.lift_snd _ _ _
  have hc : ∀ i j, pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ (pullback.lift _ _ (hw i) ≫ (x i).f) = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ (pullback.lift _ _ (hw j) ≫ (x j).f) := by
    intro i j
    have c3 : pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.fst (pullback.snd A.hom t) (𝒰.f i) = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.fst (pullback.snd A.hom t) (𝒰.f j) := pullback.condition
    have hbc : (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ 𝒰.f i = (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← c1, ← c1, ← Category.assoc, ← Category.assoc, c3]
    have H := hx i j _ _ _ hbc
    have e1 : (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw i) ≫ pullback.fst _ _) ≫ A.hom = 𝟙 _ ≫ (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ (x i).t := by
      rw [Category.id_comp, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (pullback.lift _ _ (hw i)),
        hu2, Category.assoc]
    have e2 : (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw j) ≫ pullback.fst _ _) ≫ A.hom = 𝟙 _ ≫ (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ (x j).t := by
      rw [Category.id_comp, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (pullback.lift _ _ (hw j)),
        hu2, Category.assoc]
    obtain ⟨p, hp1, hp2⟩ : ∃ p : pullback (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ⟶ pullback A.hom ((pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ (x i).t),
        p ≫ pullback.fst _ _ = pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw i) ≫ pullback.fst _ _ ∧ p ≫ pullback.snd _ _ = 𝟙 _ :=
      ⟨pullback.lift _ _ e1, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain ⟨q, hq1, hq2⟩ : ∃ q : pullback (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ⟶ pullback A.hom ((pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ (x j).t),
        q ≫ pullback.fst _ _ = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw j) ≫ pullback.fst _ _ ∧ q ≫ pullback.snd _ _ = 𝟙 _ :=
      ⟨pullback.lift _ _ e2, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have h1 : p ≫ pullback.fst _ _ = q ≫ pullback.fst _ _ := by
      rw [hp1, hq1, hu1, hu1, ← Category.assoc, ← Category.assoc, c3]
    have h2 : p ≫ pullback.snd _ _ = q ≫ pullback.snd _ _ := by rw [hp2, hq2]
    have K : p ≫ pmap A (x i).t (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ (x i).f = q ≫ pmap A (x j).t (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ (x j).f :=
      f_eq_of_pt_eq H p q h1 h2
    have p1 : p ≫ pmap A (x i).t (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) = pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw i) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hp1, Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hp2, Category.id_comp, Category.assoc, hu2]
    have p2 : q ≫ pmap A (x j).t (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw j) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hq1, Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hq2, Category.id_comp, Category.assoc, hu2]
    rw [← Category.assoc, ← Category.assoc, ← p1, ← p2]
    exact (Category.assoc _ _ _).trans (K.trans (Category.assoc _ _ _).symm)
  let 𝒱 := 𝒰.pullback₁ (pullback.snd A.hom t)
  refine ⟨t, Scheme.Cover.glueMorphisms 𝒱 (fun i => pullback.lift _ _ (hw i) ≫ (x i).f) hc, fun i => ⟨ht i, fun e he1 he2 => ?_⟩⟩
  have hι : pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ Scheme.Cover.glueMorphisms 𝒱 (fun i => pullback.lift _ _ (hw i) ≫ (x i).f) hc = pullback.lift _ _ (hw i) ≫ (x i).f :=
    Scheme.Cover.ι_glueMorphisms 𝒱 _ hc i
  have hv : e ≫ pullback.snd A.hom t = pullback.snd A.hom (x i).t ≫ 𝒰.f i := he2
  obtain ⟨v, hv1, hv2⟩ : ∃ v : pullback A.hom (x i).t ⟶ pullback (pullback.snd A.hom t) (𝒰.f i),
      v ≫ pullback.fst (pullback.snd A.hom t) (𝒰.f i) = e ∧ v ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i) = pullback.snd A.hom (x i).t :=
    ⟨pullback.lift e _ hv, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hvu : v ≫ pullback.lift _ _ (hw i) = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hu1, ← Category.assoc, hv1, he1, Category.id_comp]
    · rw [Category.assoc, hu2, hv2, Category.id_comp]
  rw [← hv1, Category.assoc, hι, ← Category.assoc, hvu, Category.id_comp]

end GlobalTheory.EndLoc.HomGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFamilyGivenCharactersMultiplicityOne
section
noncomputable section

open Formalism.L2.DIV NumberField

namespace GlobalTheory.GoodFamilyOfChars

theorem nOf_eq_nS {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) (P0 : Subgroup G)
    [Fintype P0] (ψ0 : P0 →* Kˣ) (s : T.S) :
    Formalism.IndefR.IndefiniteEpsilonOperator.nOf (T.tau s) ⟨P0, ψ0⟩ = Formalism.MainNotions.PrimeDegreeVariant.nS T ⟨P0, ψ0⟩ s := by
  classical
  have e : Formalism.IndefR.IndefiniteEpsilonOperator.epOp (T.tau s) ⟨P0, ψ0⟩ = (T.tau s).asAlgebraHom (Formalism.MainNotions.PrimeDegreeVariant.eps ⟨P0, ψ0⟩) := by
    rw [Formalism.MainNotions.PrimeDegreeVariant.eps, map_smul, map_sum, Formalism.IndefR.IndefiniteEpsilonOperator.epOp]
    congr 1
    have hsub : (Finset.univ.map (Function.Embedding.subtype (· ∈ P0))) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_subset hsub (fun x _ hx => by
      have : x ∉ P0 := fun h => hx (Finset.mem_map.2 ⟨⟨x, h⟩, Finset.mem_univ _, rfl⟩)
      simp [this]), Finset.sum_map]
    simp only [Function.Embedding.subtype_apply]
    refine Finset.sum_congr (by convert rfl) fun h _ => ?_
    simp [h.2, Representation.asAlgebraHom_of, map_inv]
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.IndefiniteEpsilonOperator.epSp Formalism.MainNotions.PrimeDegreeVariant.nS
  rw [e]

variable {K : Type} [Field K] {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module K W]

theorem asAlg_mem (τ : Representation K G W) (U : Submodule K W) (hU : ∀ g : G, ∀ w ∈ U, τ g w ∈ U)
    (a : MonoidAlgebra K G) : ∀ w ∈ U, τ.asAlgebraHom a w ∈ U := by
  induction a using MonoidAlgebra.induction_on with
  | of g => intro w hw; simpa [Representation.asAlgebraHom_of] using hU g w hw
  | add a b ha hb => intro w hw; simpa using U.add_mem (ha w hw) (hb w hw)
  | smul r a ha => intro w hw; simpa using U.smul_mem r (ha w hw)

theorem asAlg_comm (τ : Representation K G W) (f : W →ₗ[K] W) (hf : ∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f)
    (a : MonoidAlgebra K G) : f * τ.asAlgebraHom a = τ.asAlgebraHom a * f := by
  induction a using MonoidAlgebra.induction_on with
  | of g => simpa [Representation.asAlgebraHom_of, Module.End.mul_eq_comp] using hf g
  | add a b ha hb => simp [map_add, mul_add, add_mul, ha, hb]
  | smul r a ha => simp [map_smul, ha]

theorem irr_of_surj (τ : Representation K G W) (hs : Function.Surjective τ.asAlgebraHom)
    (U : Submodule K W) (hU : ∀ g : G, ∀ w ∈ U, τ g w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hc)
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha⟩ := hs ((φ w)⁻¹ • φ.smulRight v)
  have := asAlg_mem τ U hU a w hw
  rw [ha] at this
  simpa [hφ] using this

theorem scalar_of_surj (τ : Representation K G W) (hs : Function.Surjective τ.asAlgebraHom)
    (f : W →ₗ[K] W) (hf : ∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f) : ∃ c : K, f = c • LinearMap.id := by
  have hc : f ∈ Set.center (Module.End K W) := by
    rw [Semigroup.mem_center_iff]
    intro e
    obtain ⟨a, rfl⟩ := hs e
    exact (asAlg_comm τ f hf a).symm
  obtain ⟨α, hα, rfl⟩ := Module.End.mem_center_iff.1 hc
  exact ⟨α, by ext x; simp⟩

theorem exists_goodFamily : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P0 : Subgroup G) [Fintype P0] (ψ0 : P0 →* Kˣ), (∀ χ ∈ X, ∑ h : P0, χ (h : G) * (((ψ0 h)⁻¹ : Kˣ) : K) = (Fintype.card P0 : K)) → ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module K (Ws s)) (_ : ∀ s, FiniteDimensional K (Ws s)) (τ : ∀ s, Representation K G (Ws s)), Formalism.IndefR.TransferLatticeStatement.IsGood τ ∧ (∀ χ : G → K, χ ∈ X ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ) ∧ Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ := by
  intro K _ _ G _ _ X hX P0 _ ψ0 h1
  obtain ⟨T, hT, hM, -⟩ := GlobalTheory.GoodSetOfChars.exists_goodSet K G X hX ⟨P0, ψ0⟩ h1
  have hch : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) = fun g => LinearMap.trace K (T.W s) (T.tau s g) := fun s => rfl
  have hmem : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) ∈ X := fun s => (hT _).2 ⟨s, (hch s)⟩
  refine ⟨T.S, inferInstance, T.W, inferInstance, inferInstance, inferInstance, T.tau,
    ⟨fun s => inferInstance, fun s U hU => irr_of_surj (T.tau s) (T.irr s) U hU,
     fun s f hf => scalar_of_surj (T.tau s) (T.irr s) f hf, fun s t h => T.inj h⟩,
    fun χ => ⟨fun h => ?_, ?_⟩, fun s => ?_⟩
  · obtain ⟨s, hs⟩ := (hT χ).1 h
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact hmem s
  · rw [nOf_eq_nS]
    exact hM s

end GlobalTheory.GoodFamilyOfChars
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullbackStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s' : Over (Sp R')), IsGrpPullback (Over.mk s' : Over (Sp R')) A (spMap σ) φ ∧ (IsAbelianScheme A → IsAbelianScheme (Over.mk s' : Over (Sp R'))) ∧ ∀ g, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g s' := by
  first | exact @GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback | exact GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback | (intros; apply GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarIntegralEqUnitriangularChartStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haarIntegral_eq_unitriangularChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r), ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ HaarChart X c := by
  first | exact @GlobalTheory.FlagQuotHaar.exists_haarChart | exact GlobalTheory.FlagQuotHaar.exists_haarChart | (intros; apply GlobalTheory.FlagQuotHaar.exists_haarChart <;> assumption)
end

