import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0009
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsCommonNaturalRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableSumU
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerFinEntire

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem differentiable_opU (H : Sesq V) {F : V → ℂ} (hF : Differentiable ℂ F) (x : V) :
    Differentiable ℂ (opU H x F) := by
  have h : Differentiable ℂ fun z => H z x := (LinearMap.toContinuousLinearMap (H.flip x)).differentiable
  unfold opU
  fun_prop

theorem differentiable_sumU (H : Sesq V) (α : V → ℂ) (S : Finset V) {F : V → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (sumU H α S F) := by
  unfold sumU
  exact Differentiable.fun_sum fun x _ => (differentiable_opU H hF x).const_mul _

theorem differentiable_xiL (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V) (Φ : V → ℂ) {e : V → ℂ}
    (he : Differentiable ℂ e) : Differentiable ℂ (xiL H α vol SX SA SB Φ e) := by
  unfold xiL xiS
  exact Differentiable.fun_sum fun x _ => (differentiable_opU H (differentiable_sumU H _ SB he) x).const_mul _

end General

theorem differentiable_thC {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ) (Ξ : HomE E a b → ℂ) {θ : VV ι a b → ℂ}
    (hθ : Differentiable ℂ θ) : Differentiable ℂ (thC emb δ d sc AA0 SS N N' c Ξ θ) := by
  unfold thC xiV
  exact differentiable_xiL _ _ _ _ _ _ _ hθ

theorem kerFin_entire : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → ∀ (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (c : ℕ) (Ξ : HomE X.E a b → ℂ), Differentiable ℂ (thC (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).d (ambOf s B χ cD : Amb X).sc (ambOf s B χ cD : Amb X).AA SS N N' c Ξ ((ambOf s B χ cD : Amb X).e a b N N')) := by
  intro D X s cc δ B χ cD _ hcc hδ hχ a b N N' hA SS c Ξ
  have hE : Differentiable ℂ (B.eNat χ a b (s.lat N) (s.lat N')) :=
    (B.vec_mem_ne hcc hδ (Formalism.L2.Ker.KS.Lat.delta_ne hcc hδ) (B.stdOK hcc hδ) χ hχ a b _ _ hA).1.1
  let T : VCx X.Tau a b →L[ℂ] TaylorLogMetric.VC D a b := ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (s.iT.symm τ)
  have he : Differentiable ℂ ((ambOf s B χ cD : Amb X).e a b N N') := hE.comp T.differentiable
  exact differentiable_thC _ _ _ _ _ _ _ _ _ _ he

end GlobalTheory.KerFinEntire
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsInvHeckeElementSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDivisors

section Algebra

variable {R : Type} [CommRing R] {n : ℕ} {ε : R} {A B C : Matrix (Fin n) (Fin n) R}

theorem conj_diag_inv (h1 : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R))
    (h2 : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d d' : Fin n → R) (hd : ∀ i, d i * d' i = 1) :
    ε • ((B * Matrix.diagonal d * C) * (B * Matrix.diagonal d' * C)) = ε • (1 : Matrix (Fin n) (Fin n) R) := by
  have h3 : Matrix.diagonal d * Matrix.diagonal d' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hd)
  calc ε • ((B * Matrix.diagonal d * C) * (B * Matrix.diagonal d' * C))
      = B * Matrix.diagonal d * (ε • (C * B)) * Matrix.diagonal d' * C := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = ε • (B * (Matrix.diagonal d * Matrix.diagonal d') * C) := by
        rw [h2]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by rw [h3, Matrix.mul_one, h1]

theorem conj_diag_mulVec (h2 : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d : Fin n → R)
    (hA : ε • A = ε • (B * Matrix.diagonal d * C)) {y z : Fin n → R}
    (h : (fun a => ε * y a) = fun a => ε * B.mulVec z a) :
    (fun a => ε * A.mulVec y a) = fun a => ε * B.mulVec (fun i => d i * z i) a := by
  have h' : ε • y = ε • B.mulVec z := h
  have h3 : (fun i => d i * z i) = (Matrix.diagonal d).mulVec z := funext fun i => (Matrix.mulVec_diagonal d z i).symm
  show ε • A.mulVec y = ε • B.mulVec (fun i => d i * z i)
  rw [← Matrix.smul_mulVec, hA, Matrix.smul_mulVec, ← Matrix.mulVec_smul, h', Matrix.mulVec_smul, h3,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec, Matrix.mul_assoc _ C,
    ← Matrix.mul_smul, h2, Matrix.mul_smul, Matrix.mul_one]

theorem conj_diag_scale (hε : ε * ε = ε) (h2 : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d d' : Fin n → R)
    (x : R) (hd : ∀ i, d i * d' i = x) (hA : ε • A = ε • (B * Matrix.diagonal d * C)) {y z : Fin n → R}
    (h : (fun a => ε * y a) = fun a => ε * B.mulVec z a) :
    (fun a => ε * (x * y a)) = fun a => ε * A.mulVec (fun a => ε * B.mulVec (fun i => d' i * z i) a) a := by
  rw [conj_diag_mulVec h2 d hA (z := fun i => d' i * z i) (funext fun a => by rw [← mul_assoc, hε])]
  have h1 : (fun i => d i * (d' i * z i)) = x • z := funext fun i => by
    rw [← mul_assoc, hd, Pi.smul_apply, smul_eq_mul]
  rw [h1, Matrix.mulVec_smul]
  funext a
  rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, congrFun h a, mul_left_comm]

theorem det_congr (hε : ε * ε = ε) (h : ε • A = ε • B) : ε * A.det = ε * B.det := by
  have h1 : ε * ε ^ Fintype.card (Fin n) = ε := by
    rw [← pow_succ']; exact IsIdempotentElem.pow_succ_eq _ hε
  have h2 := congrArg (fun M => ε * Matrix.det M) h
  simpa only [Matrix.det_smul, ← mul_assoc, h1] using h2

theorem conj_diag_det (hε : ε * ε = ε) (h1 : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d : Fin n → R)
    (hA : ε • A = ε • (B * Matrix.diagonal d * C)) : ε * A.det = ε * ∏ i, d i := by
  have h2 := det_congr hε h1
  rw [Matrix.det_mul, Matrix.det_one] at h2
  rw [det_congr hε hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  linear_combination (∏ i, d i) * h2

end Algebra

theorem getD_label (n k i : ℕ) :
    (List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0).getD i 0 = if i < k then 1 else 0 := by
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_append_right _ _ _ _ (by simpa using h)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl

theorem dualLab_label (n k : ℕ) : dualLab (List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0) = splitLab n k := by
  simp [dualLab, splitLab]

theorem prod_label {R : Type} [CommRing R] (x : R) {n k : ℕ} (h : k ≤ n) :
    (∏ i : Fin n, if i.1 < k then x else 1) = x ^ k := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Fin.card_filter_val_lt, min_eq_right h]

theorem int_mul_mem (D : D7) (u : 𝓞 D.host.E) {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    finPart D (incA D (u : D.host.E)) * y ∈ intAE D := by
  refine AddSubgroup.closure_induction (p := fun y _ => finPart D (incA D (u : D.host.E)) * y ∈ intAE D) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨b, hb, u * v, ?_⟩
    show ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (u : D.host.E)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x _ h; rw [mul_neg]; exact neg_mem h

theorem one_mem_int (D : D7) : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, 1, rfl⟩

set_option maxHeartbeats 1000000 in

theorem exists_model {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D)
    (ϖ : 𝓞 D.host.E) (k : ℕ) (he : IsIdemAt e P) (h0 : (ϖ : D.host.E) ≠ 0) (hk : k ≤ V.rank) :
    ∃ α : GA D V, IsHeckeElt V e (ϖ : D.host.E) k α ∧
      DivAt V e (ϖ : D.host.E) (List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0) α := by
  obtain ⟨B, hB1, hB2⟩ := GlobalTheory.T.exists_completedLattice_basis_at_prime V P e he
  have hε : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he.1.1]
  obtain ⟨C, hC1, hC2⟩ := (GlobalTheory.T.completedLattice_integrality V).2.2 (finPart D e) B hε fun y hy => (hB2 y hy).imp fun _ h => h.2
  obtain ⟨d, hd⟩ : ∃ d : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
    ∀ i, d i = if i.1 < k then finPart D (incA D (ϖ : D.host.E)) else 1 := ⟨_, fun _ => rfl⟩
  have hdc : ∀ i : Fin V.rank, finPart D (incA D ((ϖ : D.host.E) ^
      ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0))) = d i := fun i => by
    rw [getD_label, hd]
    split_ifs
    · rw [zpow_one]
    · rw [zpow_zero, RingHom.map_one, RingHom.map_one]
  obtain ⟨α, hs, hα⟩ := GlobalTheory.T.exists_adelic_unitary_split_place_component V e he.1 (B * Matrix.diagonal d * C) _
    (conj_diag_inv hC1 hC2 d (fun i => if i.1 < k then finPart D (incA D (ϖ : D.host.E)⁻¹) else 1) fun i => by
      rw [hd]
      split_ifs
      · rw [← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ h0, RingHom.map_one, RingHom.map_one]
      · exact mul_one _)
  have idem : ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (fun a => finPart D e * (finPart D e * y a)) = fun a => finPart D e * y a := fun y =>
    funext fun a => by rw [← mul_assoc, hε]
  refine ⟨α, ⟨((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e (e + cA D e) (Or.inl ⟨he, rfl⟩)).2.2.1 α hs, hs, fun y hy => ?_,
    fun y hy => ?_, 1, 1, ?_, ?_, ?_, ?_⟩, ?_, B, hB1, hB2, fun y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨z, hz, h⟩ := hB2 y hy
    rw [conj_diag_mulVec hC2 d hα h]
    refine hB1 _ fun i => ?_
    rw [hd]
    split_ifs
    · exact int_mul_mem D ϖ (hz i)
    · rw [one_mul]; exact hz i
  · obtain ⟨z, hz, h⟩ := hB2 y hy
    refine ⟨_, hB1 (fun i => (if i.1 < k then 1 else finPart D (incA D (ϖ : D.host.E))) * z i) fun i => ?_, ?_⟩
    · beta_reduce
      split_ifs
      · rw [one_mul]; exact hz i
      · exact int_mul_mem D ϖ (hz i)
    · refine conj_diag_scale hε hC2 d _ _ (fun i => ?_) hα h
      rw [hd]
      split_ifs
      · exact mul_one _
      · exact one_mul _
  · rw [RingHom.map_one]; exact one_mem_int D
  · rw [RingHom.map_one]; exact one_mem_int D
  · rw [mul_one, mul_one]
  · refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he.1, zero_mul]
    · have h1 := conj_diag_det hε hC1 d hα
      rw [funext hd, prod_label _ hk] at h1
      rw [mul_one, (finPart D).map_mul, (finPart D).map_mul, (finPart D).map_pow, (finPart D).map_det]
      exact h1
  · rw [List.length_append, List.length_replicate, List.length_replicate]; omega
  · obtain ⟨z, hz, h⟩ := hB2 y hy
    refine ⟨z, hz, ?_⟩
    simp only [hdc]
    exact conj_diag_mulVec hC2 d hα h
  · refine ⟨_, hB1 z hz, ?_⟩
    simp only [hdc]
    exact conj_diag_mulVec hC2 d hα (idem _)

theorem divAt_inv_of_isHeckeElt : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → k ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) k α → DivAt V e (ϖ : D.host.E) (splitLab V.rank k) α⁻¹ := by
  intro D V P e ϖ k α he h1 h2 hk hα
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]; exact zero_mem _)
  obtain ⟨α₀, hH, hD⟩ := exists_model V P e ϖ k he h0 hk
  obtain ⟨a, ha, b, hb, rfl⟩ := (((GlobalTheory.T.involution_spherical_hecke_anti V P e he).2.2 ϖ h1 h2).2 k α₀ hH).2 ϖ α h1 h2 hα
  rw [← dualLab_label]
  exact (GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul V e _ _ _ he.1.1 h0 ((GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul V e _ _ _ he.1.1 h0 hD).2 a ha.1 b hb.1)).1

end GlobalTheory.SplitDivisors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoprimeMulIsIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

noncomputable section

namespace GlobalTheory.KerTie.MuqUnit

theorem dvd_absNorm_of_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (h : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal) : p ∣ Ideal.absNorm P.asIdeal := by
  by_contra hn
  have hc : IsCoprime ((p : ℤ)) ((Ideal.absNorm P.asIdeal : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 E))
  have h1 : (1 : 𝓞 E) ∈ P.asIdeal := by
    rw [← hab]
    refine P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ ?_) (P.asIdeal.mul_mem_left _ ?_)
    · simpa using h
    · simpa using Ideal.absNorm_mem P.asIdeal
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem exists_coprime_mul_isIntegral {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (x : K)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → w.valuation K x ≤ 1) :
    ∃ M : ℕ, M.Coprime p ∧ IsIntegral ℤ ((M : K) * x) := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  have hd0 : y.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hy0
  have hdint : IsIntegral ℤ ((y.natAbs : K) * x) := by
    rcases Int.natAbs_eq y with e | e
    · have e2 : ((y.natAbs : ℤ) : K) = (y : K) := congrArg (fun z : ℤ => (z : K)) e.symm
      have : (y.natAbs : K) * x = y • x := by
        rw [zsmul_eq_mul, ← e2, Int.cast_natCast]
      rw [this]; exact hyint
    · have : (y.natAbs : K) * x = -(y • x) := by
        rw [zsmul_eq_mul, ← neg_mul]; congr 1
        have e' : (y : K) = -((y.natAbs : ℤ) : K) := by
          have := congrArg (fun z : ℤ => (z : K)) e
          simpa using this
        rw [e', neg_neg, Int.cast_natCast]
      rw [this]; exact hyint.neg
  obtain ⟨e, M, hpM, hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
  refine ⟨M, (Nat.Prime.coprime_iff_not_dvd hp).2 hpM |>.symm, ?_⟩
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((M : K) * x) fun w => by
    by_cases hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal
    · rw [map_mul]
      refine mul_le_one' ?_ (h w hw)
      have := w.valuation_le_one (K := K) (M : 𝓞 K)
      simpa using this
    · obtain ⟨s, hs⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((y.natAbs : K) * x) fun v => by
        obtain ⟨t, ht⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K) (R := ℤ) (B := K)).1 hdint
        rw [← ht]; exact v.valuation_le_one t
      have hp1 : w.valuation K (p : K) = 1 := by
        have := (w.intValuation_eq_one_iff (x := ((p : ℕ) : 𝓞 K))).2 hw
        rw [← map_natCast (algebraMap (𝓞 K) K), HeightOneSpectrum.valuation_of_algebraMap]
        exact this
      have hle : w.valuation K ((y.natAbs : K) * x) ≤ 1 := by rw [← hs]; exact w.valuation_le_one s
      rw [hd, Nat.cast_mul, Nat.cast_pow, mul_assoc, map_mul, map_pow, hp1, one_pow, one_mul] at hle
      exact hle
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

theorem intOff_of_val {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (S : Finset ℕ) (x : K)
    (h : ∀ p : ℕ, p.Prime → p ∉ S → ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → w.valuation K x ≤ 1) :
    IntOff S (σ x) := by
  have hQ : σ x ∈ TaylorLogMetric.Qbar := by
    rw [TaylorLogMetric.Qbar, mem_algebraicClosure_iff']
    exact (Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom
  refine ⟨hQ, fun p hp lam hpS => ?_⟩
  rw [lamC_of_mem lam hQ]
  obtain ⟨M, hM, hint⟩ := exists_coprime_mul_isIntegral hp.out x (h p hp.out hpS)
  have h1 : IsIntegral ℤ ((M : ℂ) * σ x) := by
    have := map_isIntegral_int σ hint
    simpa using this
  have h2 : IsIntegral ℤ ((M : TaylorLogMetric.Qbar) * (⟨σ x, hQ⟩ : TaylorLogMetric.Qbar)) :=
    (isIntegral_algHom_iff ((algebraMap TaylorLogMetric.Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 (by simpa using h1)
  exact GlobalTheory.HeckeVal.norm_le_one_of_denom lam hM h2

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie.MuqUnit

open GlobalTheory.CharVal

variable {X : Fields} {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ} {j : Fin m}
  {μ : Formalism.L2.Host.HChar X.E}

theorem mu_core_of_conj (hconj : ∀ τ (x : X.E), X.embC σ₀ τ (star x) = starRingEnd ℂ (X.embC σ₀ τ x)) (hPr : Pr.Ok)
    (hμ : IsMu0 Ch σ₀ e j μ) (P : HeightOneSpectrum (𝓞 X.E)) (k : X.Eˣ) {c : X.K}
    (hc : σ₀ c = ((μ.locK P k : ℂˣ) : ℂ)) :
    ∃ (M : ℕ) (z : X.E) (n : X.Tau → ℤ), 0 < M ∧ (∀ τ, (n τ : ℚ) = 2 * e τ) ∧ P.valuation X.E z = P.valuation X.E (k : X.E) ^ M ∧
      (∀ Q : HeightOneSpectrum (𝓞 X.E), Q ≠ P → Q.valuation X.E z = 1) ∧ c ^ (2 * M) = ∏ τ, X.emb τ (z / star z) ^ n τ := by
  classical
  have hg : ∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := fun i => by exact_mod_cast (hPr.g_prime i).ne_zero
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf X.E μ (divs ((Pr.g 0 : ℕ) : 𝓞 X.E) ∪ divs ((Pr.g 1 : ℕ) : 𝓞 X.E))
    (productRule μ) (fun v hv => hμ.unr v fun i hi => hv (by
      rw [Finset.mem_union, mem_divs (hg 0), mem_divs (hg 1)]
      fin_cases i
      exacts [Or.inl hi, Or.inr hi])) hμ.tame P k
  obtain ⟨n, hn, hinf⟩ := hμ.inf
  refine ⟨M, z, fun τ => -n τ, hM, fun τ => by push_cast; rw [hn]; ring, h1, h2, σ₀.injective ?_⟩
  have h4 : ((μ.locK P k : ℂˣ) : ℂ) ^ M = (((μ.inf z : ℂˣ) : ℂ))⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, eq_inv_of_mul_eq_one_left h3, Units.val_inv_eq_inv_val]
  rw [map_pow, hc, mul_comm 2 M, pow_mul, h4, hinf z, ← Finset.prod_inv_distrib, ← Finset.prod_pow, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, ← zpow_neg, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  congr 1
  change _ = X.embC σ₀ τ (z / star (z : X.E))
  have h0 : X.embC σ₀ τ (z : X.E) ≠ 0 := by simp
  rw [map_div₀, hconj, div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem mu_unit_of_conj (hconj : ∀ τ (x : X.E), X.embC σ₀ τ (star x) = starRingEnd ℂ (X.embC σ₀ τ x)) (hPr : Pr.Ok)
    (hμ : IsMu0 Ch σ₀ e j μ) {P : HeightOneSpectrum (𝓞 X.E)} (k : X.Eˣ) {c : X.K}
    (hc : σ₀ c = ((μ.locK P k : ℂˣ) : ℂ)) {p : ℕ} (hP : ((p : ℕ) : 𝓞 X.E) ∉ P.asIdeal) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) : w.valuation X.K c = 1 := by
  obtain ⟨M, z, n, hM, -, -, h2, h3⟩ := mu_core_of_conj hconj hPr hμ P k hc
  refine unit_of_pow (M := 2 * M) (by omega) ?_
  rw [h3]
  refine val_prod_unit w (fun τ => ?_) n
  have h4 := (natCast_mem_pullW τ w p).2 hw
  rw [map_div₀, ← valuation_conjP, h2 _ (fun e' => hP (e' ▸ h4)), h2 _ (fun e' => hP (e' ▸ (natCast_mem_conjP _ p).2 h4)), div_one]

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie.MuqUnit

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

theorem embC_star (t : KerEntTied ex) (τ : t.X.Tau) (x : t.X.E) :
    t.X.embC t.seam.σ₀ τ (star x) = starRingEnd ℂ (t.X.embC t.seam.σ₀ τ x) := by
  change t.seam.σ₀ (t.X.emb τ (star x)) = starRingEnd ℂ (t.seam.σ₀ (t.X.emb τ x))
  rw [t.seam_ok.1, t.seam_ok.1, t.seam_ok.2]
  exact D.host.conjE_apply (TaylorLogMetric.embT D (t.seam.iT τ)) (t.seam.iE x)

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie

open MuqUnit

theorem muq_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < D.R.m → ∀ P : rowSG t.Pr t.sel (t.tup μ), P.1 ∉ t.Pr.vGs → IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).muq (i + 1) P)) ∧ IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).muq (i + 1) P)⁻¹) := by
  intro D L hT Gi Gl K Y cX ex t hmu hval u μ hQg i hi P hP
  have hPQ : P.1 ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K) := (Finset.mem_union.1 P.2).resolve_left hP
  have hg : ∀ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal := fun k hk =>
    hQg k (t.g_rec k ▸ (t.Q_rec μ (t.Pr.g k)).2 ⟨t.pr_ok.g_prime k, P.1, hPQ, hk⟩)
  have hq := (t.idx_ok μ).muqQ i hi P hP
  have key : ∀ p : ℕ, p.Prime → p ∉ (t.O u μ).S → ∀ w : HeightOneSpectrum (𝓞 t.X.K), ((p : ℕ) : 𝓞 t.X.K) ∈ w.asIdeal →
      w.valuation t.X.K ((t.cst μ).muq (i + 1) P) = 1 := by
    intro p hp hpS w hw
    have hpP : ((p : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal := fun h =>
      hpS ((sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P).2 p hp (dvd_absNorm_of_mem P.1 hp h))
    obtain ⟨e, he⟩ := hmu ⟨i, hi⟩
    have hm := mu_unit_of_conj (embC_star t) t.pr_ok he (Formalism.L2.Host.unif P.1) (hval ⟨i, hi⟩ P.1 hg) hpP hw
    have htw := (GlobalTheory.ColPeriod.twistUnit t.X.F t.X.E t.X.K t.S (t.tup μ) P.1 w).2
    rw [hq, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, hm, htw]
    simp
  refine ⟨intOff_of_val _ _ _ fun p hp hpS w hw => (key p hp hpS w hw).le, ?_⟩
  have h2 := intOff_of_val t.seam.σ₀ (t.O u μ).S ((t.cst μ).muq (i + 1) P)⁻¹ fun p hp hpS w hw => by
    rw [map_inv₀, key p hp hpS w hw, inv_one]
  exact h2

end GlobalTheory.KerTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHyperspecialDoubleCosetOfElementaryDivisorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hyperspecial_doubleCoset_of_elementaryDivisors : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E) (d : List ℤ) (α α' : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → Formalism.L2.Theta.SuppAt e V α → Formalism.L2.Theta.SuppAt e V α' → DivAt V e (ϖ : D.host.E) d α → DivAt V e (ϖ' : D.host.E) d α' → ∃ a ∈ locPart V (KsphC V ∅) e, ∃ b ∈ locPart V (KsphC V ∅) e, α' = a * α * b := by
  first | exact @GlobalTheory.SplitLabel.split_label | exact GlobalTheory.SplitLabel.split_label | (intros; apply GlobalTheory.SplitLabel.split_label <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralDualOfIndependentModUniformizerStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_dual_of_independentModUniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (m : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → Fin m → L), (∀ i r, z i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    ∃ a : ι → Fin m → L, (∀ i r, a i r ∈ Formalism.UG.intL L) ∧ ∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.Hk3.IntWitt.exists_dual_of_indepMod | exact GlobalTheory.Hk3.IntWitt.exists_dual_of_indepMod | (intros; apply GlobalTheory.Hk3.IntWitt.exists_dual_of_indepMod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituentsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_subquotient_twoBlockConstituents : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U : Type) [AddCommGroup U] [Module ℂ U] (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) k) U) (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W), π.IsIrreducible → IsSmooth A → IsSmooth B → HasFiniteLength A → HasFiniteLength B → IsSubquotient π (prod₂ A B) → ∃ (σ₁ : Irr k r) (σ₂ : Irr k t), IsSubquotient σ₁.π A ∧ IsSubquotient σ₂.π B ∧ IsSubquotient π (prod₂ σ₁.π σ₂.π) := by
  first | exact @GlobalTheory.ParIndExact.exists_irr_isSubquotient_prod₂ | exact GlobalTheory.ParIndExact.exists_irr_isSubquotient_prod₂ | (intros; apply GlobalTheory.ParIndExact.exists_irr_isSubquotient_prod₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLongOrbitWordConditionsOfLargeScale
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem jointB_of_large : ∀ eps ez C₂ A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L)
    (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D →
    (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointB L HW C₂ := by
  intro eps ez C₂ A heps hez
  obtain ⟨x1, h1⟩ := GlobalTheory.HTW.roomy_of_large eps (max 100 (2 * C₂)) A heps (le_max_left _ _)
  obtain ⟨x2, h2⟩ := GlobalTheory.InertPrimeEleven.eleven_le ez hez
  refine ⟨max x1 x2, ?_⟩
  intro D L Pm HW hE hZ hA hx hadm hfont hJ i hin hrow r ρ π hPt w hw
  have hR : Roomy L (max 100 (2 * C₂)) := h1 D L Pm hE hA (le_trans (le_max_left _ _) hx)
  have h11 : 11 ≤ D.nd.l i :=
    h2 D L (D.nd.l i) hZ (le_trans (le_max_right _ _) hx) Fact.out hin
  refine ⟨GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd D.nbr i w hw hin.1 hin.2.1 hin.2.2.1, ?_⟩
  intro Cx hG
  obtain ⟨ε, g, hg, hB⟩ := GlobalTheory.T.wordConditions_common_natural_representation L _ HW i r ρ π w hw Cx hG hR hadm hfont hJ hPt hin.1 hin.2.1 hin.2.2.1
  have hWB : WordsB L (D.nd.l i) C₂ (recWord L (liftIdx D i) ε g) := by
    refine GlobalTheory.T.twistedDualSizeWord_long_orbit_small_prime L Pm _ C₂ _ ε g _ (D.nd.l i) hR hg (le_max_right _ _) h11 hrow.1 ?_
    rw [Prod.snd_inv, orderOf_inv]
    exact hrow.lt_orderOf
  refine ⟨_, hB, GlobalTheory.T.thickLetterWord_hypotheses_of_common_conditions L HW i r ρ π w hw Cx hG _ hin.ne_two hB, h11, hWB.j_lt, hWB.par, ?_⟩
  intro t ht
  exact GlobalTheory.T.cyclicWordMarkedClusters_letterwise _ _ hWB.clusters t ht

end GlobalTheory.HTW.RecS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KappaNormAtSplitPrimesStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_norm_at_splitPrimes : ∀ D : D7, KappaSplit D := by
  first | exact @GlobalTheory.kappaSplit_all | exact GlobalTheory.kappaSplit_all | (intros; apply GlobalTheory.kappaSplit_all <;> assumption)
end

