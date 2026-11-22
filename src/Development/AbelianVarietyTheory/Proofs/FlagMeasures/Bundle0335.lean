import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0326
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0322
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProof
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0327
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMulEquivCongruenceTopologyAdelic
section
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

namespace GlobalTheory.CongTop.Swap

section Abstract

variable {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem bc_mem_UJ (φ : A →+* B) {σ : A →+* A} {τ : B →+* B} (h : ∀ x, φ (σ x) = τ (φ x))
    {J : Matrix n n A} {J' : Matrix n n B} (hJ : J.map φ = J') {g : GL n A} (hg : g ∈ Formalism.UG.UJ σ J) :
    Formalism.UG.bc φ g ∈ Formalism.UG.UJ τ J' := by
  have hg' : Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  have key : Formalism.UG.cT τ ((g : Matrix n n A).map φ) = (Formalism.UG.cT σ (g : Matrix n n A)).map φ := by
    unfold Formalism.UG.cT
    ext i j
    simp [h]
  subst hJ
  change Formalism.UG.cT τ ((g : Matrix n n A).map φ) * J.map φ * (g : Matrix n n A).map φ = J.map φ
  rw [key, ← Matrix.map_mul, ← Matrix.map_mul, hg']

end Abstract

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (topTens)
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology

theorem mem_lamAf_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E ⊗[F] Af F) :
    y ∈ lamAf (F := F) L ↔ (fun i => Algebra.TensorProduct.comm F E (Af F) (y i)) ∈
      Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  have hcc : ∀ z : E ⊗[F] Af F,
      Algebra.TensorProduct.comm F (Af F) E (Algebra.TensorProduct.comm F E (Af F) z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp [ha, hb]
  have key := GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf F E n L
    (fun i => Algebra.TensorProduct.comm F E (Af F) (y i))
  simp only [hcc] at key
  exact key.symm

private theorem tensorComm_sigR_eq_sigR_tensorComm (I : AutInst) (a : I.E ⊗[I.F] Af I.F) :
    Algebra.TensorProduct.comm I.F I.E (Af I.F) (Formalism.UG.sigR I.cm.sig (Af I.F) a) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig (Algebra.TensorProduct.comm I.F I.E (Af I.F) a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem J_map_inclE_comm (I : AutInst) :
    (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map (Algebra.TensorProduct.comm I.F I.E (Af I.F)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Af I.F) I.J := by
  ext i j
  simp [Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

private theorem tensorComm_mulVec_map_eq (I : AutInst) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    (M.map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) *ᵥ
        (fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F) (v i)) =
      fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F) ((M *ᵥ v) i) := by
  ext i
  simp [Matrix.mulVec, dotProduct, map_sum]

private theorem adLat_hat_eq_latHat (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] {m : ℕ}
    (L : Set (Fin m → E)) : GlobalTheory.AdLat.hat F L = Formalism.MainNotions.StandardLattice.latHat F E L := by
  unfold GlobalTheory.AdLat.hat Formalism.MainNotions.StandardLattice.latHat
  congr 1

private theorem stabilizes_lamAf_iff (I : AutInst) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    (∀ y, y ∈ lamAf (F := I.F) I.L ↔ M *ᵥ y ∈ lamAf (F := I.F) I.L) ↔
      GlobalTheory.Mem.Vol.StabHat I.F (I.L : Set (Fin I.n → I.E))
        (M.map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) := by
  constructor
  · intro h z
    have h1 := h (fun i => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (z i))
    have e1 : (fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F)
        ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (z i))) = z :=
      funext fun i => AlgEquiv.apply_symm_apply _ _
    have e2 : M.map (Algebra.TensorProduct.comm I.F I.E (Af I.F)) *ᵥ z =
        fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F)
          ((M *ᵥ fun i => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (z i)) i) := by
      rw [← tensorComm_mulVec_map_eq I M]
      congr 1
      exact e1.symm
    rw [mem_lamAf_iff, mem_lamAf_iff, e1, ← e2] at h1
    exact h1
  · intro h y
    rw [mem_lamAf_iff, mem_lamAf_iff, ← tensorComm_mulVec_map_eq I M]
    exact h _

theorem exists_continuousMulEquiv_adelic : ∀ (I : AutInst), ∃ e : I.Gf ≃ₜ* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J, (∀ x, ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J (e x) : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) = (I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) ∧ ∀ x, x ∈ I.Kset ↔ GlobalTheory.Mem.Vol.StabHat I.F (I.L : Set (Fin I.n → I.E)) ((I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) := by
  intro I
  classical
  obtain ⟨hT2, -, -, -, hKo, ⟨K0, hK0⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have hone : (1 : I.Gf) ∈ I.Kset := by
    have h1 : (1 : I.Gf) ∈ (K0 : Set I.Gf) := K0.one_mem
    rwa [hK0] at h1
  haveI : IsModuleTopology (Af I.F) (Af I.F ⊗[I.F] I.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af I.F ⊗[I.F] I.E) := IsModuleTopology.isTopologicalRing (Af I.F) _
  haveI : IsTopologicalGroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J) :=
    inferInstanceAs (IsTopologicalGroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Af I.F) I.cm.sig I.J))
  obtain ⟨KH, hKH, hKHo, hKHc⟩ := GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab I.F I.E I.cm.sig I.n I.J I.L
    I.L_fg I.L_span
  let φ : I.E ⊗[I.F] Af I.F →+* Af I.F ⊗[I.F] I.E :=
    (Algebra.TensorProduct.comm I.F I.E (Af I.F)).toRingEquiv.toRingHom
  let ψ : Af I.F ⊗[I.F] I.E →+* I.E ⊗[I.F] Af I.F :=
    (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm.toRingEquiv.toRingHom
  have hψφ : ∀ a, ψ (φ a) = a := fun a => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm_apply_apply a
  have hφψ : ∀ b, φ (ψ b) = b := fun b => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).apply_symm_apply b
  have hsig : ∀ a, φ (Formalism.UG.sigR I.cm.sig (Af I.F) a) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig (φ a) := fun a => tensorComm_sigR_eq_sigR_tensorComm I a
  have hsig' : ∀ b, ψ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig b) =
      Formalism.UG.sigR I.cm.sig (Af I.F) (ψ b) := by
    intro b
    have h2 := congrArg ψ (hsig (ψ b))
    rw [hψφ, hφψ] at h2
    exact h2.symm
  have hJ : (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map φ = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Af I.F) I.J :=
    J_map_inclE_comm I
  have hJ' : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Af I.F) I.J).map ψ = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    rw [← hJ, Matrix.map_map]
    ext i j
    simp only [Matrix.map_apply, Function.comp_apply, hψφ]
  have hmem : ∀ x : I.Gf, Formalism.UG.bc φ (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Af I.F) I.cm.sig I.J := fun x => bc_mem_UJ φ hsig hJ x.2
  have hmem' : ∀ h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J,
      Formalism.UG.bc ψ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h) ∈
        Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    fun h => bc_mem_UJ ψ hsig' hJ'
      (Subtype.property (p := fun g => g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Af I.F) I.cm.sig I.J) h)
  have hl : ∀ g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F), Formalism.UG.bc ψ (Formalism.UG.bc φ g) = g := by
    intro g
    ext i j
    simp [Formalism.UG.bc, hψφ]
  have hr : ∀ g : GL (Fin I.n) (Af I.F ⊗[I.F] I.E), Formalism.UG.bc φ (Formalism.UG.bc ψ g) = g := by
    intro g
    ext i j
    simp [Formalism.UG.bc, hφψ]
  let e₀ : I.Gf ≃* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J :=
    { toFun := fun x => (⟨Formalism.UG.bc φ (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)), hmem x⟩ :
        ↥(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Af I.F) I.cm.sig I.J))
      invFun := fun h => ⟨Formalism.UG.bc ψ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h), hmem' h⟩
      left_inv := fun x => Subtype.ext (hl (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)))
      right_inv := fun h => Subtype.ext (hr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h))
      map_mul' := fun x y => Subtype.ext (map_mul (Formalism.UG.bc φ) (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
        (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))) }
  have hK : ∀ x : I.Gf, x ∈ I.Kset ↔ GlobalTheory.Mem.Vol.StabHat I.F (I.L : Set (Fin I.n → I.E))
      ((I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) := fun x => stabilizes_lamAf_iff I (I.fmat x)
  have hKe : ∀ x : I.Gf, x ∈ I.Kset ↔ e₀ x ∈ KH := fun x => (hK x).trans (hKH (e₀ x)).symm
  have hmat : ∀ x : I.Gf, ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J (e₀ x) :
      GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) =
      (I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F)) := fun x => rfl
  have hcont_inv : Continuous (e₀.symm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J → I.Gf) := by
    apply continuous_of_continuousAt_one e₀.symm
    rw [ContinuousAt, Filter.tendsto_def]
    intro W hW
    simp only [map_one] at hW
    obtain ⟨g, hg1, hgW⟩ := I.topf_basis W hW
    have hN := GlobalTheory.Mem.Vol.StabGroup.congr_mem_nhds I.F I.E I.n I.L I.L_fg I.L_span g hg1
    have hmatc : Continuous (fun h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J =>
        ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
          Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E))) :=
      Units.continuous_val.comp continuous_subtype_val
    have h1 := hmatc.continuousAt (x := 1) |>.preimage_mem_nhds hN
    filter_upwards [h1, hKHo.mem_nhds KH.one_mem] with h hh hk
    apply hgW
    have hx : (I.fmat (e₀.symm h)).map (Algebra.TensorProduct.comm I.F I.E (Af I.F)) =
        ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
          Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) := by
      rw [← hmat, MulEquiv.apply_symm_apply]
    refine ⟨(hK (e₀.symm h)).2 (hx ▸ (hKH h).1 hk), ?_⟩
    intro y hy
    have hy' := (mem_lamAf_iff I.L y).1 hy
    rw [← adLat_hat_eq_latHat] at hy'
    obtain ⟨w, hw, hwe⟩ := hh _ hy'
    refine ⟨fun i => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (w i), ?_, ?_⟩
    · rw [mem_lamAf_iff]
      have e1 : (fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F)
          ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (w i))) = w :=
        funext fun i => AlgEquiv.apply_symm_apply _ _
      rw [e1, ← adLat_hat_eq_latHat]
      exact hw
    · funext i
      apply (Algebra.TensorProduct.comm I.F I.E (Af I.F)).injective
      have e3 := congrFun hwe i
      beta_reduce at e3
      rw [← hx, tensorComm_mulVec_map_eq] at e3
      simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at e3
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, map_sub, smul_eq_mul,
        map_mul, map_natCast, AlgEquiv.apply_symm_apply, e3]
  have hcont : Continuous (e₀ : I.Gf → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J) := by
    apply continuous_of_continuousAt_one e₀
    rw [ContinuousAt, Filter.tendsto_def]
    intro V hV
    simp only [map_one] at hV
    obtain ⟨V', hV'V, hV'o, hV'1⟩ := mem_nhds_iff.1 hV
    have hC : IsCompact ((KH : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J)) \ V') := hKHc.diff hV'o
    have hCi : IsClosed (e₀.symm '' ((KH : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J)) \ V')) :=
      (hC.image hcont_inv).isClosed
    have hO : IsOpen (I.Kset ∩ (e₀.symm '' ((KH : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J)) \ V'))ᶜ) :=
      hKo.inter hCi.isOpen_compl
    have h1O : (1 : I.Gf) ∈ I.Kset ∩ (e₀.symm '' ((KH : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J)) \ V'))ᶜ := by
      refine ⟨hone, ?_⟩
      rintro ⟨c, ⟨-, hcV⟩, hc1⟩
      apply hcV
      have hc : c = 1 := by simpa using congrArg e₀ hc1
      rw [hc]
      exact hV'1
    refine Filter.mem_of_superset (hO.mem_nhds h1O) ?_
    rintro x ⟨hxK, hxC⟩
    show e₀ x ∈ V
    apply hV'V
    by_contra hxV
    exact hxC ⟨e₀ x, ⟨(hKe x).1 hxK, hxV⟩, e₀.symm_apply_apply x⟩
  exact ⟨{ toMulEquiv := e₀, continuous_toFun := hcont, continuous_invFun := hcont_inv },
    fun x => rfl, hK⟩

end GlobalTheory.CongTop.Swap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralPointsAlgebraSubgroupStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_points_algebra_subgroup : ∀ (I : AutInst) (xf : I.Gf) (A : InfinitePlace I.F → Submodule ℂ (Matrix (Fin I.n) (Fin I.n) ℂ)), (∀ v, ∀ X ∈ A v, ∀ Y ∈ A v, X * Y ∈ A v) → (∀ v, ∀ X ∈ A v, Formalism.REAL.Jm (I.ε v) * Xᴴ * Formalism.REAL.Jm (I.ε v) ∈ A v) → ∃ Γ : Subgroup I.Ginf, (Γ : Set I.Ginf) = {g | g ∈ latGroup I xf ∧ ∀ v, uMat (g v) - 1 ∈ A v} := by
  first | exact @GlobalTheory.AlgCutSubgroup.exists_subgroup | exact GlobalTheory.AlgCutSubgroup.exists_subgroup | (intros; apply GlobalTheory.AlgCutSubgroup.exists_subgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameComplementRealPlacesStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormalFrame_complement_realPlaces : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ o : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), (∀ τ, (o.1 τ)ᴴ * Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D) τ * o.1 τ = 1) ∧ ∀ s ∈ Hinf X u, ∃ m : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ, ∀ τ, m τ ∈ Matrix.unitaryGroup (Fin (D.R.N 0)) ℂ ∧ (m τ).submatrix (Fin.cast D.R.N_zero.symm) (Fin.cast D.R.N_zero.symm) = matW X.B.I (X.wfr u (X.pl.symm τ)) (X.pl.symm τ) s ∧ sTil X wt s τ = o.1 τ * m τ * (o.1 τ)⁻¹ := by
  first | exact @GlobalTheory.St.CFrame.frame_of_type | exact GlobalTheory.St.CFrame.frame_of_type | (intros; apply GlobalTheory.St.CFrame.frame_of_type <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrder
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CompletedSelfDual

open GlobalTheory.AdelicU GlobalTheory.AdelicU.SelfDual GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces

theorem mem_maxOrder_iff_mem_intLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    z ∈ maxOrder F E v ↔ z ∈ intLoc F E v := by
  constructor
  · intro hz
    rw [mem_intLoc_iff_absFin_le_one, absFin_le_iff]
    intro τ
    obtain ⟨p, hp, hpz⟩ := (mem_maxOrder F E v z).1 hz
    let f : v.adicCompletionIntegers F →+* (valBar F v).integer :=
      ((algebraMap (Fv F v) (FvBar F v)).comp (v.adicCompletionIntegers F).subtype).codRestrict _ fun a => by
        change absBar F v (algebraMap (Fv F v) (FvBar F v) a) ≤ 1
        rw [absBar_algebraMap]
        exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 a.2
    refine (Valuation.integer.integers (valBar F v)).mem_of_integral (x := finEmb F v τ z)
      ⟨p.map f, hp.map _, ?_⟩
    have := congrArg (finEmb F v τ : Fv F v ⊗[F] E →+* FvBar F v) hpz
    rw [Polynomial.hom_eval₂, map_zero] at this
    rw [Polynomial.eval₂_map, ← this]
    congr 1
    ext a
    exact ((finEmb F v τ).commutes (a : Fv F v)).symm
  · refine intLoc_induction (p := fun z => z ∈ maxOrder F E v) (fun a ha x => ?_) (zero_mem _)
      (fun _ _ => add_mem) (fun _ => neg_mem)
    have h1 : (1 : Fv F v) ⊗ₜ[F] (x : E) ∈ maxOrder F E v := by
      letI := (intToEv F E v).toAlgebra
      exact (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (algebraMap ℤ _) (inclR (F := F) (E := E) (Fv F v))
        (RingHom.ext_int _ _)
    have h2 : a ⊗ₜ[F] (1 : E) ∈ maxOrder F E v :=
      RingHom.isIntegralElem_map (intToEv F E v) (x := ⟨a, ha⟩)
    simpa using mul_mem h2 h1

theorem exists_isSelfDualLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), IsHermND σ J → Submodule.IsLattice E L → (∀ y : Fin n → E, y ∈ L ↔ ∀ x ∈ L, hE σ J x y ∈ (algebraMap (𝓞 E) E).range) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ Lv : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin n → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v Lv ∧ ∀ y, y ∈ Lv ↔ y ∈ GlobalTheory.AdelicU.latLoc F L v := by
  intro F E _ _ _ _ _ σ n J L hJ hL hsd v
  classical
  let Lv : Submodule (maxOrder F E v) (Fin n → Fv F v ⊗[F] E) :=
    { carrier := latLoc F L v
      zero_mem' := zero_mem _
      add_mem' := fun h h' => add_mem h h'
      smul_mem' := fun c _ hy =>
        (latLoc F L v).smul_mem ⟨c.1, (mem_maxOrder_iff_mem_intLoc v _).1 c.2⟩ hy }
  have hmem : ∀ y, y ∈ Lv ↔ y ∈ latLoc F L v := fun _ => Iff.rfl
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := exists_frame L hL
  have h2 := map_mul_eq_one (F := F) (Fv F v) h1
  have hcol : ∀ j, (fun i => S.map (inclR (F := F) (Fv F v)) i j) ∈ Lv := fun j =>
    tmul_mem_latLoc (one_mem _) (hS j)
  refine ⟨Lv, ⟨?_, ?_, fun y => ?_⟩, hmem⟩
  · refine ⟨Finset.univ.image fun j i => S.map (inclR (F := F) (Fv F v)) i j, le_antisymm ?_ fun y hy => ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      exact hcol j
    · rw [eq_sum_col h2 y]
      refine sum_mem fun j _ => ?_
      exact Submodule.smul_mem _ (⟨_, (mem_maxOrder_iff_mem_intLoc v _).2
        ((mem_latLoc_iff_of_frame h1 hS hΦ v y).1 hy j)⟩ : maxOrder F E v)
        (Submodule.subset_span (Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩))
  · refine eq_top_iff.2 fun y _ => ?_
    rw [eq_sum_col h2 y]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hcol j))
  · have h3 : latLoc F L v = dualLoc σ J L v := (forall_isSelfDualAt_iff hJ.2 hL).2 hsd v
    simp only [mem_maxOrder_iff_mem_intLoc]
    rw [hmem, h3]
    exact Iff.rfl

end GlobalTheory.CompletedSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmulLocalWittFreeTupleGramStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_localWitt_free_tuple_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y := by
  first | exact @GlobalTheory.LocalWittFree.exists_smul_ratTup_eq | exact GlobalTheory.LocalWittFree.exists_smul_ratTup_eq | (intros; apply GlobalTheory.LocalWittFree.exists_smul_ratTup_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentQuotientInvariantProbabilityStatement
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentQuotient_invariant_probability : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)), I.IsIsot W → ∃ ν : Measure I.GA, IsProbabilityMeasure ν ∧ I.IsNQuotMeas W ν ∧ ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ν Cpᶜ = 0 := by
  first | exact @GlobalTheory.UnipQuot.exists_quot_prob | exact GlobalTheory.UnipQuot.exists_quot_prob | (intros; apply GlobalTheory.UnipQuot.exists_quot_prob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWeakIntegralOfStronglyContinuous
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_weakIntegral_of_stronglyContinuous {X H : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure X) (R : X → (H →L[ℂ] H)) (hn : ∀ x F, ‖R x F‖ = ‖F‖)
    (hc : ∀ F, Continuous fun x => R x F) (φ : X → ℂ) (hφ : Integrable φ μ) :
    ∃ T : H →L[ℂ] H, ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, φ g * ⟪x, R g y⟫_ℂ ∂μ := by
  have hint : ∀ y : H, Integrable (fun g => φ g • R g y) μ := fun y =>
    (hφ.norm.mul_const ‖y‖).mono' (hφ.aestronglyMeasurable.smul (hc y).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun g => by rw [norm_smul, hn])
  let Tl : H →ₗ[ℂ] H :=
    { toFun := fun y => ∫ g, φ g • R g y ∂μ
      map_add' := fun y z => by
        simp only [map_add, smul_add]
        exact integral_add (hint y) (hint z)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        congr 1
        ext g
        rw [smul_comm] }
  refine ⟨Tl.mkContinuous (∫ g, ‖φ g‖ ∂μ) fun y => ?_, fun x y => ?_⟩
  · calc ‖Tl y‖ = ‖∫ g, φ g • R g y ∂μ‖ := rfl
      _ ≤ ∫ g, ‖φ g • R g y‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖φ g‖ * ‖y‖ ∂μ := by
        congr 1
        ext g
        rw [norm_smul, hn]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖y‖ := integral_mul_const _ _
  · show ⟪x, ∫ g, φ g • R g y ∂μ⟫_ℂ = _
    rw [← integral_inner (hint y)]
    congr 1
    ext g
    rw [inner_smul_right]

theorem AutInst_exists_isRConvF_and_isRConv : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → (∀ e : I.Gf → ℂ, Integrable e μf → ∃ T, I.IsRConvF μf fund R e T) ∧ ∀ φ : I.GA → ℂ, Integrable φ (I.muA μf) → ∃ T, I.IsRConv μf fund R φ T := by
  intro I μf _ _ fund hfund R hR
  obtain ⟨-, -, hn, hc⟩ := GlobalTheory.T.rightRegularRepresentation_unitary_mul_continuous I μf fund hfund R hR
  haveI := GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints I
  refine ⟨fun e he => ?_, fun φ hφ => ?_⟩
  · obtain ⟨T, hT⟩ := exists_weakIntegral_of_stronglyContinuous μf (fun g => R (1, g))
      (fun g F => hn _ F) (fun F => (hc F).comp (by fun_prop)) e he
    exact ⟨T, he, hT⟩
  · obtain ⟨T, hT⟩ := exists_weakIntegral_of_stronglyContinuous (I.muA μf) R hn hc φ hφ
    exact ⟨T, hφ, hT⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFrameSelfNormalFormExists_proof : GlobalTheory.TypeAsm.IdNFC := by
  first | exact @GlobalTheory.IdNF.idNFC_holds | exact GlobalTheory.IdNF.idNFC_holds | (intros; apply GlobalTheory.IdNF.idNFC_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitaryStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), WittX X u wt → IsAdeleIso X ιA → (∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a)) → ∃ (Φ : Hfin X u ≃* Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ (h : Hfin X u) y, RepF X wt ιA (h : X.B.I.Gf) y ↔ Φ h = y) := by
  first | exact @GlobalTheory.frame_action_mulEquiv | exact GlobalTheory.frame_action_mulEquiv | (intros; apply GlobalTheory.frame_action_mulEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairChangedDualVectorsStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePair_changed_dualVectors : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), ∃ (P₂ : LocNG.FPair H r) (c₂ : Coord P₂ S) (φ : LocNG.Datum P ≃ LocNG.Datum P₂), c₂.e = c.e ∧ P₂.St = P.St ∧ P₂.K0 = P.K0 ∧ P₂.UW0 = P.UW0 ∧ P₂.Hp = P.Hp ∧ (P₂.PrimeTo ↔ P.PrimeTo) ∧ (∀ d, c₂.dat (φ d) = c.dat d) ∧ (∀ d t, LocNG.IsTermOver P d t ↔ LocNG.IsTermOver P₂ (φ d) t) ∧ (∀ d t, LocNG.IsTermOver P d t → LocNG.om P₂ t = LocNG.om P t) ∧ ∀ g d d', LocNG.Datum.Moves g d d' ↔ LocNG.Datum.Moves g (φ d) (φ d') := by
  first | exact @GlobalTheory.HL.ToC.changed_duals | exact GlobalTheory.HL.ToC.changed_duals | (intros; apply GlobalTheory.HL.ToC.changed_duals <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianRapidDecay
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussDecay

theorem isCMFam_of_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) : GlobalTheory.Mem.Vol.IsCMFam φ := by
  obtain ⟨hF, hE, h2, -⟩ := h
  unfold GlobalTheory.Mem.Vol.IsCMFam
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · have key : ∀ v, (InfinitePlace.mk (φ v)).comap (algebraMap F E) = v := by
      intro v
      rw [InfinitePlace.comap_mk, show (φ v).comp (algebraMap F E) = v.embedding from RingHom.ext (hφ v),
        InfinitePlace.mk_embedding]
    intro v w hvw
    rw [← key v, ← key w]
    exact congrArg (fun x : InfinitePlace E => x.comap (algebraMap F E)) hvw
  · have a1 := IsTotallyComplex.finrank E
    have a2 := IsTotallyReal.finrank F
    have a3 := Module.finrank_mul_finrank ℚ F E
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
      IsTotallyComplex.nrRealPlaces_eq_zero E]
    rw [h2] at a3
    omega

end GlobalTheory.GaussDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.IotaSigmaCompatibility

theorem iotaA_sigA : ∀ (D : D7) (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA →
    ∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a) := by
  intro D X ιA h a
  have he : ∀ x : X.B.I.E, X.ιE (X.B.I.cm.sig x) = Formalism.L2.Forms.sigD D (X.ιE x) := by
    intro x
    have h1 : X.B.I.cm.sig x = star x := rfl
    have h2 : Formalism.L2.Forms.sigD D (X.ιE x) = star (X.ιE x) := rfl
    rw [h1, h2, X.ιE_conj, Formalism.BasicNotions.bridge_star_holds D.R D.host]
  exact GlobalTheory.St.G.IotaConj.iota_sigR X.B.I.F X.B.I.E D.host.F D.host.E X.B.I.cm.sig
    (Formalism.L2.Forms.sigD D) X.ιE ιA he h.1 h.2 a

end GlobalTheory.St.G.IotaSigmaCompatibility
end

