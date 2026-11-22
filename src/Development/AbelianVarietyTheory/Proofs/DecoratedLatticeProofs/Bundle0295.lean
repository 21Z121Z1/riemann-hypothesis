import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0281
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctions
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceCouplingIndexFiniteLevelStable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.CoupStab
open GlobalTheory.StepData GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_mem_box {n : Type} [Fintype n] {M : Matrix n n k} (hM : IntM M) {c : kˣ} {y : n → k}
    (hy : y ∈ box n c) : M *ᵥ y ∈ box n c := by
  rw [mem_box] at hy ⊢
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hM i j) (hy j)

theorem toBlocks₁₁_mul {n : Type} [Fintype n] (M N : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  ext i j; simp [Matrix.mul_apply, Matrix.toBlocks₁₁, Fintype.sum_sum_type]

theorem toBlocks₁₁_one {n : Type} [Fintype n] [DecidableEq n] :
    (1 : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k).toBlocks₁₁ = 1 := by
  ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem withCol_mul {n n' : Type} [Fintype n] (κ : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) (x₀ : Matrix n n' k)
    (y : n → k) : κ * withCol x₀ y = withCol (κ.toBlocks₁₁ * x₀) (κ.toBlocks₁₁ *ᵥ y) := by
  ext (r | r) (c | c)
  · simp [withCol, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁]
  · simp [withCol, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.mulVec, dotProduct]
  · exact r.elim0
  · exact r.elim0

theorem box_eq_preimage {n : Type} (c : kˣ) :
    (box n c : Set (n → k)) = (fun y : n → k => ((c⁻¹ : kˣ) : k) • y) ⁻¹' Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
  ext y
  simp only [SetLike.mem_coe, mem_box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Pi.smul_apply,
    smul_eq_mul]
  refine forall_congr' fun i => ?_
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  have hc : 0 < valuation k (c : k) := by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 c.ne_zero
  rw [inv_mul_le_iff₀ hc, mul_one]

theorem isOpen_box {n : Type} [Fintype n] (c : kˣ) : IsOpen (box n c : Set (n → k)) := by
  rw [box_eq_preimage]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => (valuation k).isOpen_integer).preimage (continuous_const_smul _)

theorem isCompact_box {n : Type} [Fintype n] (c : kˣ) : IsCompact (box n c : Set (n → k)) := by
  have hK : IsCompact (𝒪[k] : Set k) := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))
  have e : (box n c : Set (n → k)) = (fun y : n → k => (c : k) • y) '' Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
    rw [box_eq_preimage, Set.image_eq_preimage_of_inverse]
    · intro y; simp [smul_smul]
    · intro y; simp [smul_smul]
  rw [e]
  exact (isCompact_univ_pi fun _ => hK).image (continuous_const_smul _)

theorem finite_image_box {n : Type} [Fintype n] (c₁ c₂ : kˣ) :
    ((Submodule.Quotient.mk (p := box n c₂)) '' (box n c₁ : Set (n → k))).Finite := by
  obtain ⟨t, -, ht⟩ := (isCompact_box (n := n) c₁).elim_nhds_subcover
    (fun y => (fun z => z - y) ⁻¹' (box n c₂ : Set (n → k)))
    (fun y _ => ((isOpen_box c₂).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by show y - y ∈ box n c₂; rw [sub_self]; exact zero_mem _))
  refine (t.finite_toSet.image (Submodule.Quotient.mk (p := box n c₂))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine ⟨z, hz, (Submodule.Quotient.eq _).2 ?_⟩
  rw [← neg_sub]; exact neg_mem hyz

theorem om_one_ne {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (h : GL b k) (Φ : Matrix b a k → ℂ) (x : Matrix b a k) (hx : om μ 1 h Φ x ≠ 0) : Φ ((h⁻¹ : GL b k).val * x) ≠ 0 := by
  unfold om at hx
  have := right_ne_zero_of_mul hx
  simpa using this

theorem om_g_ne {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (Φ : Matrix b a k → ℂ) (x x' : Matrix b a k) (hx : om μ g 1 Φ x ≠ 0)
    (h : Φ (x * g.val) ≠ 0 → Φ (x' * g.val) ≠ 0) : om μ g 1 Φ x' ≠ 0 := by
  unfold om at *
  simp only [inv_one, Units.val_one, Matrix.one_mul] at *
  exact mul_ne_zero (left_ne_zero_of_mul hx) (h (right_ne_zero_of_mul hx))

end GlobalTheory.QPl.CoupStab

namespace GlobalTheory.QPl.CoupStab
open GlobalTheory.StepData GlobalTheory.SplitWeil

theorem psi_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
    (T : Chain k s X Z) (hL : T.Laws) {κ : GL (X (s + 1) ⊕ Fin 0) k} (hκ : κ ∈ (T.lev (s + 1) 0 rfl).J)
    (g : GL (X s ⊕ Fin (0 + 1)) k) (x₀ : Matrix (X (s + 1)) (X s) k) (y : X (s + 1) → k) (h : T.Psi g x₀ y ≠ 0) :
    T.Psi g (κ.val.toBlocks₁₁ * x₀) (κ.val.toBlocks₁₁ *ᵥ y) ≠ 0 := by
  have hPhi : ∀ x, T.Phi s 0 rfl x ≠ 0 → T.Phi s 0 rfl (κ.val * x) ≠ 0 := by
    intro x hx
    have e := congrFun ((hL.1 s 0 rfl).2 ⟨κ⁻¹, inv_mem hκ⟩) x
    have hr : om (T.mu (s + 1)) 1 (κ⁻¹ : GL (X (s + 1) ⊕ Fin 0) k) (T.Phi s 0 rfl) x ≠ 0 := by
      rw [e, Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero (Units.ne_zero _) hx
    simpa using om_one_ne _ _ _ _ hr
  unfold Chain.Psi at *
  refine om_g_ne _ _ _ _ _ h fun h' => ?_
  rw [← withCol_mul, Matrix.mul_assoc]
  exact hPhi _ h'

theorem coupIdx_stab : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), (Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)).Finite ∧ (∀ yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb) ∧ (∀ yb yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb) ∧ (∀ yb yb' yb'', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb'' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb'') ∧ ∀ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂), ∀ yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → yb' ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := by
  intro D c v χ Q
  have hB : ∀ {g : GL (Q.X (Q.s + 1) ⊕ Fin 0) Q.k}, g ∈ (Q.T.lev (Q.s + 1) 0 rfl).J → IntM g.val.toBlocks₁₁ :=
    fun hg i j => intM_of_mem_KO (Q.le _ _ _ hg) (.inl i) (.inl j)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (finite_image_box Q.c₁ Q.c₂).subset (by rintro _ ⟨y, hy, rfl, -⟩; exact ⟨y, hy, rfl⟩)
  · intro yb
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ yb
    refine ⟨1, one_mem _, y, rfl, ?_⟩
    rw [Units.val_one, toBlocks₁₁_one, Matrix.one_mulVec]
  · rintro _ _ ⟨g, hg, y, rfl, rfl⟩
    refine ⟨g⁻¹, inv_mem hg, _, rfl, ?_⟩
    rw [Matrix.mulVec_mulVec, ← toBlocks₁₁_mul, Units.inv_mul, toBlocks₁₁_one, Matrix.one_mulVec]
  · rintro _ _ _ ⟨g, hg, y, rfl, h1⟩ ⟨g', hg', y', h2, h3⟩
    refine ⟨g' * g, mul_mem hg' hg, y, rfl, ?_⟩
    rw [← h3, Units.val_mul, toBlocks₁₁_mul, ← Matrix.mulVec_mulVec]
    refine (Submodule.Quotient.eq _).2 ?_
    rw [← Matrix.mulVec_sub]
    exact mulVec_mem_box (hB hg') ((Submodule.Quotient.eq _).1 (h1.trans h2.symm))
  · rintro _ ⟨y₁, -, rfl, g, hg, x₀, hΨ⟩ _ ⟨κ, hκ, y, hy, rfl⟩
    have hd : y - y₁ ∈ box _ Q.c₂ := (Submodule.Quotient.eq _).1 hy
    have hΨy : Q.T.Psi g x₀ y ≠ 0 := by
      rw [show y = y₁ + (y - y₁) by abel, (Q.adapt g hg x₀ y₁).2 _ hd]; exact hΨ
    exact ⟨_, mulVec_mem_box (hB hκ) ((Q.adapt g hg x₀ y).1 hΨy), rfl, g, hg, _,
      psi_ne Q.T Q.laws hκ g x₀ y hΨy⟩

end GlobalTheory.QPl.CoupStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoLevelIndicesNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl

theorem relIndex_KO_ne_zero {k n : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Fintype n] [DecidableEq n] (J : Subgroup (GL n k)) (hJ : IsOpen (J : Set (GL n k))) : J.relIndex (KO k n) ≠ 0 := by
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := n))
  haveI : Finite (KO k n ⧸ J.subgroupOf (KO k n)) :=
    Subgroup.quotient_finite_of_isOpen _ (hJ.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem QAt.idx_last_ne_zero : ∀ (D : D7) (c : Comm D) (v : VCom c) (χ : ℕ → (AE D)ˣ →* Circle) (Q : QAt v χ), Q.idx (Q.s + 1) ≠ 0 ∧ Q.idx (Q.s + 1 + 1) ≠ 0 := by
  intro D c v χ Q
  refine ⟨?_, ?_⟩
  · rw [Q.idx_mid (Q.s + 1) 0 rfl]
    exact relIndex_KO_ne_zero _ (Q.reg.2.2 _ _ _).1
  · rw [Q.idx_top]
    exact relIndex_KO_ne_zero _ Q.openT

end GlobalTheory.QPl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoStepEntriesSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QPl.LastTwo

theorem entries_mem_SB : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ) α yb, Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb ∈ SB _ ∧ Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb ∈ SB _ := by
  intro D c v χ Q α yb
  have hreg := Q.reg
  constructor
  · haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.X (Q.s + 1)) (n' := Q.X Q.s)
    refine GlobalTheory.FinPl.Comm.comp_mem_SB (om_mem_SB (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (hreg.1 Q.s 0 rfl))
      (p := fun x₀ => withCol x₀ (Quotient.out yb)) (s := fun x => x.toBlocks₁₁) ?_ ?_ fun x => rfl
    · unfold withCol; fun_prop
    · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))
  · haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.Z ⊕ Unit) (n' := Q.X (Q.s + 1))
    have hv1 : valuation Q.k (-1 : Q.k) = 1 := by simp
    have hh := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol Q.k Q.ψk Q.ν (-1) Q.cond Q.unitVol hv1 (Q.X (Q.s + 1)) 1 1 _
      (cosetInd_mem_SB Q.c₂ yb)).1
    refine GlobalTheory.FinPl.Comm.prod_mem_SB hreg.2.1 hh
      (p := fun x : Matrix (Q.Z ⊕ Unit) (Q.X (Q.s + 1)) Q.k => fromCols x.toRows₁ (0 : Matrix Q.Z (Fin 0) Q.k))
      (r := fun x => x (Sum.inr ()))
      (s := fun z => fromRows z.1.toCols₁ (Matrix.of fun (_ : Unit) => z.2)) ?_ ?_ ?_ ?_
    · exact continuous_pi fun i => continuous_pi fun j => by
        rcases j with j | j
        · exact (continuous_apply j).comp (continuous_apply (Sum.inl i))
        · exact j.elim0
    · exact continuous_apply _
    · exact continuous_pi fun i => continuous_pi fun j => by
        rcases i with i | i
        · exact (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
        · exact (continuous_apply j).comp continuous_snd
    · intro x; ext (i | i) j <;> rfl

end GlobalTheory.QPl.LastTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceNormalisedCombinationsPreserveThetaFun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.ThetaPin

variable {D : D7}

theorem isFinComb_of_half {S T : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (c : WO S T →₀ ℂ)
    (hc : ∀ u ∈ c.support, IsHalf (algebraMap (AF D.host.F) (AE D) ε) u) : IsFinComb c := by
  intro u hu
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    obtain ⟨α, rfl, -, -⟩ := hε
    show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] _ = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rw [← hc u hu i j, map_mul, h0, zero_mul]

theorem aconv_support {G : Type} [AddMonoid G] (P : AddSubmonoid G) :
    ∀ (l : List (G →₀ ℂ)), (∀ e ∈ l, ∀ g ∈ e.support, g ∈ P) → ∀ g ∈ (aconv l).support, g ∈ P
  | [], _, g, hg => by
    have : g = 0 := by
      simpa [aconv] using Finsupp.support_single_subset hg
    rw [this]; exact P.zero_mem
  | e :: l, hl, g, hg => by
    classical
    have ih := aconv_support P l (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
    have he := hl e List.mem_cons_self
    change g ∈ (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).support at hg
    obtain ⟨x, hx, hg⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hg)
    obtain ⟨y, hy, hg⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hg)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]
    exact P.add_mem (he x hx) (ih y hy)

def finSub (S T : HSp D) : AddSubmonoid (WO S T) where
  carrier := {u | u.map (infPart D) = 0}
  zero_mem' := by ext i j; simp
  add_mem' {a b} ha hb := by
    change Matrix.map a (infPart D) = 0 at ha
    change Matrix.map b (infPart D) = 0 at hb
    change Matrix.map (a + b) (infPart D) = 0
    rw [Matrix.map_add (infPart D) (fun x y => RingHom.map_add (infPart D) x y) a b, ha, hb, add_zero]

theorem isFinComb_aconv {S T : HSp D} (l : List (WO S T →₀ ℂ)) (hl : ∀ e ∈ l, IsFinComb e) : IsFinComb (aconv l) :=
  aconv_support (finSub S T) l hl

theorem isFinComb_cast {c : Comm D} {a b : ℕ} (e : a = b) (x : WO (c.V (a + 1)) c.T →₀ ℂ) (hx : IsFinComb x) :
    IsFinComb (e ▸ x : WO (c.V (b + 1)) c.T →₀ ℂ) := by
  subst e; exact hx

end GlobalTheory.QPl.ThetaPin

open GlobalTheory.QPl.ThetaPin in
theorem GlobalTheory.QPl.pins_keep_theta : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → F.Pins w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQ j) Ψ₁) ∧ IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQT j h) Ψ₂) := by
  intro D c v t w F hc hP j h Ψ₁ Ψ₂ h1 h2
  have hs : ∀ i, (F.Q i).s = j := fun i => by have := (F.Q i).hs; omega
  refine ⟨?_, ?_⟩
  · rw [hP.eQ j (by omega)]
    refine (GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 _ _ h1 ?_ hc.std
    refine isFinComb_aconv _ fun e he => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    obtain ⟨ε, hε, hsum⟩ := (F.Q i).q.above
    have hat := ((F.Q i).eL_at j 0 (by have := hs i; omega)).1
    exact isFinComb_of_half hε _ fun u hu => hsum ▸ hat u hu
  · rw [hP.eQT j h]
    refine (GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 _ _ h2 ?_ hc.std
    refine isFinComb_aconv _ fun e he => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    obtain ⟨ε, hε, hsum⟩ := (F.Q i).q.above
    have hat := (F.Q i).eLT_at.1
    unfold QAt.eT
    exact isFinComb_cast _ _ (isFinComb_of_half hε _ fun u hu => hsum ▸ hat u hu)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeRationalCosetSameOrbitIffLevel
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.SymBridge (toLoc IsOrd yPos xPos IsCompl)

noncomputable section
namespace GlobalTheory.TwBridge.LevOrb
open GlobalTheory.TwBridge.Lev

theorem inX_zero {E : Type} [Field E] (n : ℕ) (x : Fin n → E) : Loc.inX E n 0 x = x := by
  funext l
  simp [Loc.inX, show l.1 < n from l.2]

theorem mem_prX_zero {E : Type} [Field E] {n : ℕ} (J : Subgroup ((Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E)))
    (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : κ ∈ Loc.prX (Loc.Cbe J 1) ↔ (show (Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E) from κ) ∈ J := by
  have hR : ∀ γ : (Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E), Loc.R1cond E n 0 γ := fun γ => by
    rw [r1cond_iff]
    intro l l' h
    have := l.2
    have := l'.2
    omega
  constructor
  · rintro ⟨r, hr, hx⟩
    have h2 : r ∈ J := by simpa [MulAut.conj_apply] using hr.2
    have : r = κ := LinearEquiv.ext fun x => by simpa only [inX_zero] using hx x
    exact this ▸ h2
  · intro h
    refine ⟨κ, ⟨⟨hR _, hR _⟩, ?_⟩, fun x => by rw [inX_zero, inX_zero]⟩
    simpa [MulAut.conj_apply] using h

section Orb
variable {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} {A : Type} [Fintype A] [DecidableEq A] {n : ℕ}

omit [Fintype A] [DecidableEq A] in
theorem mem_box_iff (hc : IsCompl P q ι ϖ) (e : A ≃ Fin n) (M : ℕ) (v : Sp E n) :
    (fun r => ι (v (e r))) ∈ box A (ϖ ^ M) ↔ ((q : E) ^ M)⁻¹ • v ∈ stdAt E n P := by
  rw [stdAt, StabRef.mem_locStd, mem_box]
  have key : ∀ a : E, valuation k (ι a) ≤ valuation k ((ϖ ^ M : kˣ) : k) ↔ IntAt P (((q : E) ^ M)⁻¹ * a) := fun a => by
    rw [← hc.int, map_mul, map_inv₀, map_pow, ← hc.unif, Valuation.mem_integer_iff, map_mul, map_inv₀, Units.val_pow_eq_pow_val,
      inv_mul_le_iff₀ (zero_lt_iff.2 (by simp)), mul_one]
  refine ⟨fun h l => ?_, fun h r => (key _).2 (h (e r))⟩
  obtain ⟨r, rfl⟩ := e.surjective l
  exact (key _).1 (h r)

omit [NumberField E] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem phi_mulVec (e : A ≃ Fin n) (e' : A ⊕ Fin 0 ≃ Fin n) (he : ∀ a, e' (.inl a) = e a) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (z : Fin n → E) : (phi ι e' γ).val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) = fun r => ι (γ z (e r)) := by
  funext r
  rw [apply_sum γ z, map_sum, ← e.sum_comp]
  simp [mulVec, dotProduct, toBlocks₁₁, phi_val, toLoc, he]

theorem mulVec_mem_box {g : GL (A ⊕ Fin 0) k} (hg : g ∈ KO k _) (a : kˣ) {y : A → k} (hy : y ∈ box A a) :
    g.val.toBlocks₁₁ *ᵥ y ∈ box A a := fun i => by
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le ((mem_KO.1 hg).1 (Sum.inl i) (Sum.inl j)) (hy j)

theorem sameOrb_iff (hc : IsCompl P q ι ϖ) (e : A ≃ Fin n) (e' : A ⊕ Fin 0 ≃ Fin n) (he : ∀ a, e' (.inl a) = e a)
    (J : Subgroup (GL (A ⊕ Fin 0) k)) (h1 : KOne k _ ≤ J) (h2 : J ≤ KO k _) (M : ℕ) (z z' : Sp E n) :
    GlobalTheory.QPl.SameOrb J (box _ (ϖ ^ M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔
      ∃ γ : Sp E n ≃ₗ[E] Sp E n, phi ι e' γ ∈ J ∧ ((q : E) ^ M)⁻¹ • (γ z - z') ∈ stdAt E n P := by
  have hsub : ∀ γ : Sp E n ≃ₗ[E] Sp E n, (phi ι e' γ).val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) =
      fun r => ι ((γ z - z') (e r)) := fun γ => by
    rw [phi_mulVec e e' he]
    funext r
    simp
  constructor
  · rintro ⟨g, hg, y, hy, hy'⟩
    rw [Submodule.Quotient.eq] at hy hy'
    have h0 : g.val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) ∈ box A (ϖ ^ M) := by
      have := sub_mem hy' (mulVec_mem_box (h2 hg) _ hy)
      rw [mulVec_sub] at this
      convert this using 1
      abel
    have hU1 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k | MaxM ((g⁻¹).val * N - 1)} := by
      simp only [MaxM, Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
      exact IsOpen.preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => ((g⁻¹).val * N - 1) i j)
        (t := {z | valuation k z < 1}) (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)
    have ho : IsOpen ((box A (ϖ ^ M) : Submodule 𝒪[k] (A → k)) : Set (A → k)) := by
      convert (isOpen_set_pi Set.finite_univ fun (_ : A) _ => isOpen_cball (ϖ ^ M)) using 1
      ext z; simp [mem_box, cball]
    have hU2 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k |
        N.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) ∈ box A (ϖ ^ M)} := by
      refine ho.preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k =>
        N.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r)))) ?_
      have hb : Continuous fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => N.toBlocks₁₁ :=
        continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inl i) (Sum.inl j)
      exact (hb.matrix_mulVec continuous_const).sub continuous_const
    obtain ⟨M₀, ⟨a1, a2⟩, -⟩ := exists_approx ι hc.dense g.val (hU1.inter hU2) ⟨by
      change MaxM _
      rw [Units.inv_mul, sub_self]
      exact maxM_zero, h0⟩
    obtain ⟨u, hu, eu⟩ := exists_mem_KOne a1
    have ev : (g * u).val = M₀.map ι := by
      rw [Units.val_mul, eu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    obtain ⟨γ, hγ⟩ := exists_phi ι e' M₀ _ ev
    refine ⟨γ, hγ ▸ mul_mem hg (h1 hu), (mem_box_iff hc e M _).1 ?_⟩
    rw [← hsub, hγ, ev]
    exact a2
  · rintro ⟨γ, hγ, h⟩
    refine ⟨_, hγ, _, rfl, (Submodule.Quotient.eq _).2 ?_⟩
    rw [hsub]
    exact (mem_box_iff hc e M _).2 h

end Orb

theorem mem_prX_JQ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q kj n c : ℕ) (hc : c = 0)
    (κ : Sp E n ≃ₗ[E] Sp E n) : κ ∈ Loc.prX (Loc.Cbe (LocE.JQ P q kj n c) 1) ↔
      (show Sp E (n + 0) ≃ₗ[E] Sp E (n + 0) from κ) ∈ LocE.JQ P q kj n 0 := by
  subst hc
  exact mem_prX_zero _ κ

theorem sameOrb_iff_level : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k), AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → ∀ (b : L.β (s + 1)) (hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ z z' : Sp X.E (R.N (s + 1)), (GlobalTheory.QPl.SameOrb ((W.T s R).lev (s + 1) 0 rfl).J (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔ ∃ κ ∈ (L.levQ (s + 1) b ⟨P.1, hQ⟩).H, ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 z - z') ∈ stdAt X.E (R.N (s + 1)) P.1) := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W hA L G hL b hQ e he z z'
  have hc : cOf R (s + 1) = 0 := by have := hA.steps; unfold cOf; omega
  have hn : R.N (s + 1) = R.k + (s + 1) * (R.t + 1) := rfl
  let e' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + 0) := (Equiv.sumEmpty _ _).trans e
  have he' : IsOrd (yPos xPos (R.N (s + 1))) e' := by
    rintro (a | a)
    · exact he a
    · exact a.elim0
  set o := stdOrd (Fin R.k) (Fin R.t) (s + 1) 0 (rfl : s + 1 + 0 = s + 1) with ho
  have hconj : ∀ g : GL _ k, (plainFrame (k := k) o).conj.symm g = (reGL o).symm g := fun g => by
    rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply, show (plainFrame (k := k) o).bas = 1 from rfl,
      show (plainFrame (k := k) o).ord = o from rfl, MulEquiv.apply_symm_apply]
    simp
  have hJ : ∀ g, g ∈ ((W.T s R).lev (s + 1) 0 rfl).J ↔ (reGL o).symm g ∈ (parahoric _ (Fin (s + 1) × Fin R.t) W.δ W.tame).J :=
    fun g => by rw [← hconj]; rfl
  have hmem : ∀ γ : Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Sp X.E (R.N (s + 1)), phi ι e' γ ∈ ((W.T s R).lev (s + 1) 0 rfl).J ↔
      γ ∈ prCat (Pr := Pr) cst.sharp (s + 1) P.1 (L.h (s + 1) b P) := fun γ => by
    rw [hJ, hL.last_h, prCat, Jat, if_neg hA.nmem, mem_prX_JQ _ _ _ _ _ hc]
    exact mem_par_iff (c := 0) (s := s) hA.compl W.unif rfl hn he' W.tame γ
  have hle : ((W.T s R).lev (s + 1) 0 rfl).J ≤ KO k _ := fun g hg => by
    have h := (mem_parahoric.1 ((hJ g).1 hg)).1
    rw [mem_KO] at h ⊢
    rw [← map_inv] at h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa [reGL_symm_val] using h.1 (o.symm i) (o.symm j)
    · simpa [reGL_symm_val] using h.2 (o.symm i) (o.symm j)
  rw [sameOrb_iff hA.compl e e' (fun _ => rfl) _
    (fun u hu => (hJ u).2 (((parahoric _ (Fin (s + 1) × Fin R.t) W.δ W.tame).reindex o).KOne_le hu)) hle, hL.grpQ]
  constructor
  · rintro ⟨γ, h1, h2⟩
    have h3 := (hmem γ).1 h1
    exact ⟨⟨γ, hL.int _ b P h3⟩, h3, h2⟩
  · rintro ⟨κ, h1, h2⟩
    exact ⟨κ.1, (hmem _).2 h1, h2⟩

end GlobalTheory.TwBridge.LevOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainChartParahoricEqLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chain_chart_parahoric_eq_level : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s j φ ι → ∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t) := by
  first | exact @GlobalTheory.chart_level_iff | exact GlobalTheory.chart_level_iff | (intros; apply GlobalTheory.chart_level_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2 := by
  first | exact @GlobalTheory.WeilSlice.weilSlice_theta | exact GlobalTheory.WeilSlice.weilSlice_theta | (intros; apply GlobalTheory.WeilSlice.weilSlice_theta <;> assumption)
end

