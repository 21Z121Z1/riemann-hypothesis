import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.JstTranspose
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LWa1

theorem dense_loc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (hc : ∀ x, σ (σ x) = x) (hne : ∃ z, σ z ≠ z) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Formalism.UG.cT (σ : E →+* E) J = J) (hdet : J.det ≠ 0) :
    Dense {h : HA (Fv F v) σ J | HA.mat (Fv F v) σ J h ∈ HFin (Fv F v) σ J} := by
  classical
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  have : Nontrivial (Fv F v ⊗[F] E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := Fv F v) (B := E)
      (algebraMap F E).injective).nontrivial
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have b1 : IsOpen {x : Fv F v | IsUnit x} := by
    simp only [isUnit_iff_ne_zero]
    exact isOpen_ne
  have b2 : ∀ x : Fv F v, IsUnit x → ContinuousAt Ring.inverse x := by
    intro x hx
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hx.ne_zero
  obtain ⟨h1, h2⟩ := GlobalTheory.RealApprox.units_of_free (A := Fv F v) (R := Fv F v ⊗[F] E)
    (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)) b1 b2
  refine GlobalTheory.RealApprox.dense_unitary (inclR (F := F) (Fv F v)) (σ : E →+* E) (sigR (Fv F v) σ) (fun x => ?_) hc
    hne (fun x => ?_) ?_ (fun y => ?_) h1 h2 J hJ hdet
  · simp [sigR, inclR]
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [sigR, hc]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ).toLinearMap
  · let S : AddSubgroup (Fv F v ⊗[F] E) :=
      (inclR (F := F) (E := E) (Fv F v)).toAddMonoidHom.range.topologicalClosure
    have hS : IsClosed (S : Set (Fv F v ⊗[F] E)) := AddSubgroup.isClosed_topologicalClosure _
    show y ∈ S
    induction y using TensorProduct.induction_on with
    | zero => exact S.zero_mem
    | add a b ha hb => exact S.add_mem ha hb
    | tmul a x =>
      have hc : Continuous fun a : Fv F v => a ⊗ₜ[F] x := by
        have : (fun a : Fv F v => a ⊗ₜ[F] x) = fun a : Fv F v => a • ((1 : Fv F v) ⊗ₜ[F] x) := by
          funext a
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Continuous.smul (f := fun a : Fv F v => a)
          (g := fun _ : Fv F v => ((1 : Fv F v) ⊗ₜ[F] x : Fv F v ⊗[F] E)) continuous_id continuous_const
      refine DenseRange.induction_on (HeightOneSpectrum.denseRange_algebraMap F v) a
        (p := fun a => a ⊗ₜ[F] x ∈ S) (hS.preimage hc) fun f => ?_
      refine AddSubgroup.le_topologicalClosure _ ⟨f • x, ?_⟩
      show (1 : Fv F v) ⊗ₜ[F] (f • x) = algebraMap F _ f ⊗ₜ[F] x
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem uj_smul {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) {δ : A}
    (hδ : IsUnit δ) : Formalism.UG.UJ σ (δ • J) = Formalism.UG.UJ σ J := by
  ext g
  show Formalism.UG.cT σ g.1 * (δ • J) * g.1 = δ • J ↔ Formalism.UG.cT σ g.1 * J * g.1 = J
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hδ.smul_left_cancel

theorem jst_cases (D : D7) (n : ℕ) (P : Fin (n + n) → Fin (n + n) → Prop)
    (h : ∀ a b, P (finSumFinEquiv a) (finSumFinEquiv b)) : ∀ i j, P i j := by
  intro i j
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  exact h a b

theorem jst_transpose (D : D7) (n : ℕ) : (Jst D n)ᵀ = -Jst D n := by
  ext i j
  revert i j
  refine jst_cases D n _ fun a b => ?_
  simp only [Jst, blk4, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.neg_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply, eq_comm]

theorem jst_map (D : D7) (n : ℕ) : (Jst D n).map (D.sp.cm.sig : D.host.E →+* D.host.E) = Jst D n := by
  ext i j
  revert i j
  refine jst_cases D n _ fun a b => ?_
  simp only [Jst, blk4, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply, apply_ite]

theorem jst_mul (D : D7) (n : ℕ) : Jst D n * Jst D n = -1 := by
  simp only [Jst, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  ext i j
  revert i j
  refine jst_cases D n _ fun a b => ?_
  simp only [Matrix.submatrix_apply, Matrix.neg_apply, Equiv.symm_apply_apply]
  rw [← Matrix.submatrix_one_equiv (finSumFinEquiv.symm : Fin (n + n) ≃ Fin n ⊕ Fin n)]
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply, Equiv.eq_symm_apply, Equiv.symm_apply_eq, Fin.ext_iff] <;> omega

theorem jst_det (D : D7) (n : ℕ) : (Jst D n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (jst_mul D n)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg, Matrix.det_one, mul_one] at this
  exact (neg_one_pow_ne_zero (R := D.host.E) _) this.symm

theorem sig_sig (D : D7) (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  simp [Formalism.BasicNotions.CMData.sig]

theorem sig_ne (D : D7) : ∃ z, D.sp.cm.sig z ≠ z := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  have hall : ∀ a : D.host.E, a ∈ (algebraMap D.host.F D.host.E).range := fun a =>
    (D.sp.cm.fixed a).1 (by simpa [Formalism.BasicNotions.CMData.sig, starRingEnd_apply] using h a)
  have hbot : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
    ext a
    simp only [Algebra.mem_top, iff_true, Algebra.mem_bot]
    obtain ⟨b, hb⟩ := hall a
    exact ⟨b, hb⟩
  have := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
  rw [D.sp.cm.deg2] at this
  norm_num at this

theorem exists_skew (D : D7) : ∃ δ : D.host.E, δ ≠ 0 ∧ D.sp.cm.sig δ = -δ := by
  obtain ⟨z, hz⟩ := sig_ne D
  refine ⟨z - D.sp.cm.sig z, sub_ne_zero.2 (Ne.symm hz), ?_⟩
  rw [map_sub, sig_sig]
  ring

theorem approx_loc (D : D7) (n : ℕ) (v : Pl D) (x : GLoc D.sp.cm.sig (Jst D n) v)
    (O : Set (GLoc D.sp.cm.sig (Jst D n) v)) (hO : IsOpen O) (hx : x ∈ O) :
    ∃ γ : GRat D.sp.cm.sig (Jst D n), ratLoc D.sp.cm.sig (Jst D n) v γ ∈ O := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_skew D
  have hJ' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (δ • Jst D n) = δ • Jst D n := by
    have e1 : ∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n j i) = -Jst D n i j := by
      intro i j
      have a1 := congrFun (congrFun (jst_map D n) j) i
      have a2 := congrFun (congrFun (jst_transpose D n) i) j
      simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply] at a1 a2
      rw [a1, a2]
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [e1]
    have hδ' : (D.sp.cm.sig : D.host.E →+* D.host.E) δ = -δ := hδ
    rw [hδ', neg_mul_neg]
  have hdet' : (δ • Jst D n).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hδ0) (jst_det D n)
  have hE : Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (δ • Jst D n) =
      Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := uj_smul _ _ (Ne.isUnit hδ0)
  have hR : HR (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n) = HR (Fv D.host.F v) D.sp.cm.sig (Jst D n) := by
    show Formalism.UG.UJ _ (JR _ _) = Formalism.UG.UJ _ (JR _ _)
    have e : JR (F := D.host.F) (Fv D.host.F v) (δ • Jst D n) =
        inclR (F := D.host.F) (Fv D.host.F v) δ • JR (F := D.host.F) (Fv D.host.F v) (Jst D n) := by
      ext i j
      simp [JR, map_mul]
    rw [e]
    exact uj_smul _ _ ((Ne.isUnit hδ0).map _)
  have hd := dense_loc D.host.F D.host.E v D.sp.cm.sig (sig_sig D) (sig_ne D) (δ • Jst D n) hJ' hdet'
  have hind := (isEmbedding_matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)).isInducing
  have hind' := (isEmbedding_matHom (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n)).isInducing
  obtain ⟨O₀, hO₀, rfl⟩ := hind.isOpen_iff.1 hO
  let x' : HA (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n) :=
    (⟨matHom _ _ _ x, by rw [hR]; exact x.2⟩ : HR (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n))
  have hU : IsOpen (matHom (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n) ⁻¹' O₀) := hind'.continuous.isOpen_preimage _ hO₀
  obtain ⟨h', h'O, h'A⟩ := hd.inter_open_nonempty _ hU ⟨x', hx⟩
  obtain ⟨γ', hγ', e⟩ := Subgroup.mem_map.1 h'A
  refine ⟨⟨γ', hE ▸ hγ'⟩, ?_⟩
  show matHom _ _ _ _ ∈ O₀
  have e2 : matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) (ratLoc D.sp.cm.sig (Jst D n) v ⟨γ', hE ▸ hγ'⟩) =
      Formalism.UG.bc (inclR (F := D.host.F) (Fv D.host.F v)) γ' := rfl
  rw [e2, e]
  exact h'O

end PositivityTheory.Rg.Rsw.L.LWa1

namespace PositivityTheory.Rg.Rsw.L

open LWa1 in
theorem wa1 : WeakApproximationFinitePlace := by
  intro D n v U hU g
  set x := proj D.sp.cm.sig (Jst D n) v g with hxdef
  let V : Subgroup (GLoc D.sp.cm.sig (Jst D n) v) := U.comap (emb D.sp.cm.sig (Jst D n) v)
  have hV : IsOpen (V : Set (GLoc D.sp.cm.sig (Jst D n) v)) := hU.preimage (continuous_emb _ _ v)
  have hO : IsOpen {y : GLoc D.sp.cm.sig (Jst D n) v | y⁻¹ * x ∈ V} :=
    hV.preimage (continuous_inv.mul continuous_const)
  obtain ⟨γ, hγ⟩ := approx_loc D n v x _ hO (by simp [V])
  set k := emb D.sp.cm.sig (Jst D n) v ((ratLoc D.sp.cm.sig (Jst D n) v γ)⁻¹ * x) with hk
  refine ⟨ratEmb D.sp.cm.sig (Jst D n) γ, ?_, (ratEmb D.sp.cm.sig (Jst D n) γ)⁻¹ * g * k⁻¹, ?_, k, hγ, ?_, by group⟩
  · show _ ∈ ratPts _ _
    rw [← range_ratEmb]
    exact ⟨γ, rfl⟩
  · rw [map_mul, map_mul, map_inv, map_inv, proj_ratEmb, hk, proj_emb_self, ← hxdef]
    group
  · rw [← range_emb]
    exact ⟨_, rfl⟩

end PositivityTheory.Rg.Rsw.L
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LBumpExA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.Rsw.L.LBumpEx

variable {D : D7}

abbrev AfE (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

abbrev Ev (D : D7) (v : Pl D) : Type := Fv D.host.F v ⊗[D.host.F] D.host.E

def cf (v : Pl D) : AfE D →ₐ[D.host.F] Ev D v :=
  Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)

theorem cf_tmul (v : Pl D) (a : Af D.host.F) (x : D.host.E) : cf v (a ⊗ₜ[D.host.F] x) = evalV D.host.F v a ⊗ₜ[D.host.F] x :=
  rfl

theorem cv_eq (v : Pl D) (x : AE D) : cv D v x = cf v (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, map_zero]
  | tmul a y => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, map_add, hx, hy]

theorem cf_mem_of_mem {z : AfE D} (hz : z ∈ intAE D) (v : Pl D) : cf v z ∈ intLoc D.host.F D.host.E v := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    rw [cf_tmul]
    exact tmul_mem_intLoc (ha v) x
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

def pr (φ : D.host.E →ₗ[D.host.F] D.host.F) : AfE D →ₗ[D.host.F] Af D.host.F :=
  (TensorProduct.rid D.host.F (Af D.host.F)).toLinearMap ∘ₗ φ.lTensor (Af D.host.F)

theorem pr_tmul (φ : D.host.E →ₗ[D.host.F] D.host.F) (a : Af D.host.F) (x : D.host.E) :
    pr φ (a ⊗ₜ[D.host.F] x) = φ x • a := by
  rw [pr, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

def aux₃ (φ : D.host.E →ₗ[D.host.F] D.host.F) (v : Pl D) : Ev D v →ₗ[D.host.F] Fv D.host.F v :=
  (TensorProduct.rid D.host.F (Fv D.host.F v)).toLinearMap ∘ₗ φ.lTensor (Fv D.host.F v)

theorem trace_projection_tmul (φ : D.host.E →ₗ[D.host.F] D.host.F) (v : Pl D) (a : Fv D.host.F v) (x : D.host.E) :
    aux₃ φ v (a ⊗ₜ[D.host.F] x) = φ x • a := by
  rw [aux₃, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

theorem evalV_pr (φ : D.host.E →ₗ[D.host.F] D.host.F) (v : Pl D) (y : AfE D) :
    evalV D.host.F v (pr φ y) = aux₃ φ v (cf v y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, map_zero, map_zero, LinearMap.map_zero]
  | tmul a x => rw [pr_tmul, cf_tmul, trace_projection_tmul, AlgHom.map_smul_of_tower]
  | add y y' hy hy' => rw [LinearMap.map_add, map_add, map_add, LinearMap.map_add, hy, hy']

theorem trace_projection_mem_integers (φ : D.host.E →ₗ[D.host.F] D.host.F) (hφ : ∀ x : 𝓞 D.host.E, φ x ∈ (algebraMap (𝓞 D.host.F) D.host.F).range)
    (v : Pl D) {w : Ev D v} (hw : w ∈ intLoc D.host.F D.host.E v) : aux₃ φ v w ∈ v.adicCompletionIntegers D.host.F := by
  refine intLoc_induction (p := fun w => aux₃ φ v w ∈ v.adicCompletionIntegers D.host.F) (fun a ha x => ?_) ?_
    (fun y z hy hz => ?_) (fun y hy => ?_) hw
  · obtain ⟨r, hr⟩ := hφ x
    rw [trace_projection_tmul, ← hr, Algebra.smul_def]
    exact mul_mem (v.coe_mem_adicCompletionIntegers r) ha
  · rw [LinearMap.map_zero]; exact zero_mem _
  · rw [LinearMap.map_add]; exact add_mem hy hz
  · rw [LinearMap.map_neg]; exact neg_mem hy

theorem sum_pr {k : ℕ} (s : Fin k → 𝓞 D.host.E) (φ : Fin k → D.host.E →ₗ[D.host.F] D.host.F)
    (hsum : ∀ x, ∑ j, φ j x • (s j : D.host.E) = x) (y : AfE D) :
    ∑ j, pr (φ j) y ⊗ₜ[D.host.F] ((s j : D.host.E)) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero]
  | tmul a x =>
    simp only [pr_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, hsum x]
  | add y y' hy hy' => simp only [LinearMap.map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hy, hy']

theorem mem_of_cf_mem {z : AfE D} (hz : ∀ v : Pl D, cf v z ∈ intLoc D.host.F D.host.E v) : z ∈ intAE D := by
  obtain ⟨k, s, φ, hφ, hsum⟩ := GlobalTheory.AdelicU.SelfDual.exists_dualFamily_integers (F := D.host.F) (E := D.host.E)
  rw [← sum_pr s φ hsum z]
  refine sum_mem fun j _ => AddSubgroup.subset_closure ⟨pr (φ j) z, fun v => ?_, s j, rfl⟩
  rw [evalV_pr]
  exact trace_projection_mem_integers (φ j) (fun x => hφ x j) v (hz v)

theorem exists_nat_mul_mem {Q : Set (AfE D)} (hQ : IsCompact Q) :
    ∃ N : ℕ, 0 < N ∧ ∀ q ∈ Q, (N : AfE D) * q ∈ intAE D := by
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover (fun n : ℕ => {q : AfE D | ((n + 1 : ℕ) : AfE D) * q ∈ intAE D})
    (fun n => (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage (continuous_const.mul continuous_id))
    (fun q _ => by
      obtain ⟨n, hn, h⟩ := GlobalTheory.IwaPlace.SdComap.exists_natCast_mul_mem_intAE q
      exact Set.mem_iUnion.2 ⟨n - 1, by rwa [Nat.sub_add_cancel hn]⟩)
  refine ⟨∏ n ∈ t, (n + 1), Finset.prod_pos fun _ _ => Nat.succ_pos _, fun q hq => ?_⟩
  obtain ⟨n, hn, hq'⟩ := Set.mem_iUnion₂.1 (ht hq)
  rw [← Finset.mul_prod_erase t _ hn, Nat.cast_mul, mul_comm ((n + 1 : ℕ) : AfE D), mul_assoc]
  exact GlobalTheory.HostAdeleIso.intAE_mul_mem D (GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE _) hq'

def U (S : Finset (Pl D)) (ef : AfE D) (N m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (AfE D)) where
  carrier := {w | (∀ v ∉ S, ∀ i j, cf v (w i j) ∈ intLoc D.host.F D.host.E v) ∧ ∀ i j, (N : AfE D) * (ef * w i j) ∈ intAE D}
  add_mem' := fun {a b} ha hb => ⟨fun v hv i j => by
      rw [Matrix.add_apply, map_add]; exact add_mem (ha.1 v hv i j) (hb.1 v hv i j),
    fun i j => by rw [Matrix.add_apply, mul_add, mul_add]; exact add_mem (ha.2 i j) (hb.2 i j)⟩
  zero_mem' := ⟨fun v _ i j => by rw [Matrix.zero_apply, map_zero]; exact zero_mem _,
    fun i j => by rw [Matrix.zero_apply, mul_zero, mul_zero]; exact zero_mem _⟩
  neg_mem' := fun {a} ha => ⟨fun v hv i j => by rw [Matrix.neg_apply, map_neg]; exact neg_mem (ha.1 v hv i j),
    fun i j => by rw [Matrix.neg_apply, mul_neg, mul_neg]; exact neg_mem (ha.2 i j)⟩

theorem mem_U {S : Finset (Pl D)} {ef : AfE D} {N m n : ℕ} {w : Matrix (Fin m) (Fin n) (AfE D)} :
    w ∈ U S ef N m n ↔ (∀ v ∉ S, ∀ i j, cf v (w i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, (N : AfE D) * (ef * w i j) ∈ intAE D := Iff.rfl

open Classical in

theorem mem_U_iff {S : Finset (Pl D)} {ef : AfE D} (hef : ef * ef = ef)
    (hS : ∀ v : Pl D, cf v ef = if v ∈ S then 1 else 0) {N m n : ℕ} {w : Matrix (Fin m) (Fin n) (AfE D)}
    (hw : ∀ v ∉ S, ∀ i j, cf v (w i j) ∈ intLoc D.host.F D.host.E v) :
    w ∈ U S ef N m n ↔ (Matrix.of fun i j => ef * w i j) ∈ U S ef N m n := by
  have h2 : ∀ i j, (N : AfE D) * (ef * (Matrix.of fun i j => ef * w i j) i j) = (N : AfE D) * (ef * w i j) :=
    fun i j => by rw [Matrix.of_apply, ← mul_assoc ef ef, hef]
  rw [mem_U, mem_U]
  simp only [h2]
  refine ⟨fun h => ⟨fun v hv i j => ?_, h.2⟩, fun h => ⟨hw, h.2⟩⟩
  rw [Matrix.of_apply, map_mul, hS v, if_neg hv, zero_mul]
  exact zero_mem _

end PositivityTheory.Rg.Rsw.L.LBumpEx

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfInv
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LCfInv

variable {D : D7} {n : ℕ}

theorem fam_mul {H : G D n → ℝ≥0} {φ : G D n → ℂ} {u : G D n} (hH : ∀ g, H (g * u) = H g)
    (hφ : ∀ g, φ (g * u) = φ g) (s₁ z : ℂ) (g : G D n) : fam H φ s₁ z (g * u) = fam H φ s₁ z g := by
  simp only [fam, hH, hφ]

theorem eisS_mul {f : G D n → ℂ} {u : G D n} (hf : ∀ g, f (g * u) = f g) (g : G D n) :
    eisS f (g * u) = eisS f g := by
  unfold eisS GlobalTheory.Eis.cosetSum
  refine tsum_congr fun q => ?_
  simp only [GlobalTheory.Eis.term, ← mul_assoc, hf]

theorem E_mul {H : G D n → ℝ≥0} {φ : G D n → ℂ} {s₀ : ℂ} {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G D n → ℂ} {σ : ℝ}
    (hc : IsCont H φ s₀ U d E σ) {u : G D n} (hH : ∀ g, H (g * u) = H g) (hφ : ∀ g, φ (g * u) = φ g) (g : G D n) :
    ∀ z ∈ U, E z (g * u) = E z g := by
  have ah : AnalyticOnNhd ℂ (E · (g * u)) U := (hc.hol (g * u)).analyticOnNhd hc.isOpen
  have ag : AnalyticOnNhd ℂ (E · g) U := (hc.hol g).analyticOnNhd hc.isOpen
  obtain ⟨τ, hτ⟩ := hc.right.1
  have hx : ((max τ σ + 1 : ℝ) : ℂ) ∈ rightOf (max τ σ) := by simp
  have hxU : ((max τ σ + 1 : ℝ) : ℂ) ∈ U := hτ (rightOf_subset (le_max_left _ _) hx)
  have ev : (E · (g * u)) =ᶠ[𝓝 ((max τ σ + 1 : ℝ) : ℂ)] (E · g) := by
    filter_upwards [(isOpen_rightOf (max τ σ)).mem_nhds hx] with w hw
    have hw' : σ < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    simp only [hc.eq w hw', eisS_mul (fam_mul hH hφ s₀ w)]
  exact fun z hz => ah.eqOn_of_preconnected_of_eventuallyEq ag hc.right.isPreconnected hxU ev hz

end PositivityTheory.Rg.Rsw.L.LCfInv

namespace PositivityTheory.Rg.Rsw.L

open LCfInv in
theorem cfInv : CfInv := by
  intro D n H s₀ φ U d E σ hc ε hε u hH hφ k g
  unfold cf
  congr 1
  refine circleIntegral.integral_congr hε.1.le fun z hz => ?_
  have hzU : z ∈ U := hε.2.1 (Metric.sphere_subset_closedBall hz)
  simp only [E_mul hc hH hφ g z hzU]

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LWMajD
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LWMaj

variable {D : D7}

theorem unifLevel {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (C : Set (GA D S)) (hC : IsCompact C) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ g ∈ C, om (g, 1) f ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
  obtain ⟨U, hUo, hU⟩ := hf.level

  let a : GA D S → WO S T →+ WO S T := fun g =>
    { toFun := fun u => actO S T g⁻¹ 1 u
      map_zero' := by simp [actO]
      map_add' := fun u v => by simp [actO, Matrix.mul_add, Matrix.add_mul] }
  let U' : AddSubgroup (WO S T) := ⨅ g ∈ C, U.comap (a g)
  have hcont : Continuous fun p : GA D S × WO S T => actO S T p.1⁻¹ 1 p.2 := by
    simp only [actO, inv_inv]
    exact (continuous_const.matrix_mul continuous_snd).matrix_mul ((GlobalTheory.MixModel.continuous_mt S).comp continuous_fst)
  have hmem : ∀ u, u ∈ U' ↔ ∀ g ∈ C, actO S T g⁻¹ 1 u ∈ U := fun u => by
    rw [AddSubgroup.mem_iInf]
    exact forall_congr' fun g => by rw [AddSubgroup.mem_iInf]; rfl
  have hopen : IsOpen (U' : Set (WO S T)) := by
    have hn : C ×ˢ ({0} : Set (WO S T)) ⊆ (fun p : GA D S × WO S T => actO S T p.1⁻¹ 1 p.2) ⁻¹' U := by
      rintro ⟨g, u⟩ ⟨-, hu⟩
      simp only [Set.mem_singleton_iff] at hu
      subst hu
      simp [actO, U.zero_mem]
    obtain ⟨s, v, -, hv, hCs, h0v, hsv⟩ :=
      generalized_tube_lemma hC isCompact_singleton (hUo.preimage hcont) hn
    refine AddSubgroup.isOpen_of_mem_nhds U' (g := 0) ?_
    refine Filter.mem_of_superset (hv.mem_nhds (h0v rfl)) fun u hu => ?_
    refine (hmem u).2 fun g hg => ?_
    have h := hsv (Set.mk_mem_prod (hCs hg) hu)
    rw [Set.mem_preimage] at h
    exact h
  refine ⟨U', hopen, fun g hg => ⟨hom.om_pres _ _ hf, fun u hu h0 => ?_⟩⟩
  have hu' : actO S T g⁻¹ 1 u ∈ U := by
    exact (hmem u).1 hu g hg
  have h0' : (actO S T g⁻¹ 1 u).map (infPart D) = 0 := by
    simp only [actO, Matrix.map_mul, h0, Matrix.zero_mul, Matrix.mul_zero]
  have h1 := hom.om_heis g 1 (actO S T g⁻¹ 1 u) f hf
  rw [hU _ hu' h0'] at h1
  have h2 : actO S T g 1 (actO S T g⁻¹ 1 u) = u := by
    simp only [actO, inv_inv, GlobalTheory.MixModel.mt_one, Matrix.one_mul, Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul_inv,
      Matrix.mul_one]
  rw [h2] at h1
  exact h1.symm

end PositivityTheory.Rg.Rsw.L.LWMaj

end
end

