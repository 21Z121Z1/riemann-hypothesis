import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupOpenCompact
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto.Topo

open GlobalTheory.SplitWeil Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def nearSet (s : kˣ) (m : ℕ) : Set (Matrix (Fin m) (Fin m) k) := {A | NearOne s A}

def ballMat (s : kˣ) (m : ℕ) : Set (Matrix (Fin m) (Fin m) k) := {B | ∀ a b, B a b ∈ cball s}

theorem ballMat_eq (s : kˣ) (m : ℕ) : ballMat (k := k) s m =
    (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => cball s : Set (Fin m → Fin m → k)) :=
  Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩

theorem isOpen_ballMat (s : kˣ) (m : ℕ) : IsOpen (ballMat (k := k) s m) := by
  simp only [ballMat, Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (isOpen_cball s).preimage (f := fun A : Matrix (Fin m) (Fin m) k => A i j) (by fun_prop)

theorem isCompact_ballMat (s : kˣ) (m : ℕ) : IsCompact (ballMat (k := k) s m) := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => cball s :
      Set (Fin m → Fin m → k)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball s
  rw [ballMat_eq]; exact h

theorem nearSet_eq (s : kˣ) (m : ℕ) : nearSet (k := k) s m =
    (Homeomorph.subRight (1 : Matrix (Fin m) (Fin m) k)) ⁻¹' ballMat s m := by
  ext A
  simp only [nearSet, NearOne, ballMat, Set.mem_setOf_eq, Set.mem_preimage, Homeomorph.subRight_apply,
    Matrix.sub_apply]

theorem isOpen_nearSet (s : kˣ) (m : ℕ) : IsOpen (nearSet (k := k) s m) := by
  rw [nearSet_eq]
  exact (isOpen_ballMat s m).preimage (Homeomorph.continuous _)

theorem isCompact_nearSet (s : kˣ) (m : ℕ) : IsCompact (nearSet (k := k) s m) := by
  rw [nearSet_eq]
  exact (Homeomorph.subRight (1 : Matrix (Fin m) (Fin m) k)).isCompact_preimage.2 (isCompact_ballMat s m)

theorem congGL_eq (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (m : ℕ) :
    (congGL k s hs m : Set (GL (Fin m) k)) =
      (fun g : GL (Fin m) k => (g : Matrix (Fin m) (Fin m) k)) ⁻¹' nearSet s m ∩
        (fun g : GL (Fin m) k => ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) ⁻¹' nearSet s m :=
  rfl

theorem isOpen_congGL (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (m : ℕ) :
    IsOpen (congGL k s hs m : Set (GL (Fin m) k)) := by
  rw [congGL_eq]
  exact ((isOpen_nearSet s m).preimage Units.continuous_val).inter
    ((isOpen_nearSet s m).preimage Units.continuous_coe_inv)

theorem isCompact_congGL (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (m : ℕ) :
    IsCompact (congGL k s hs m : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hK := isCompact_nearSet (k := k) s m
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin m) (Fin m) k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [congGL_eq, Set.mem_inter_iff, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]

end GlobalTheory.CompanionTheory.BZPhiPG.Onto.Topo

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem congM_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1),
  IsOpen (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) ∧ IsCompact (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) := by
  intro k _ _ _ _ n s hs
  have e : (congM k s hs n : Set (Mir k n)) =
      (Subtype.val : Mir k n → GL (Fin (n + 1)) k) ⁻¹' (congGL k s hs (n + 1) : Set (GL (Fin (n + 1)) k)) := rfl
  rw [e]
  exact ⟨(Topo.isOpen_congGL s hs (n + 1)).preimage continuous_subtype_val,
    (GlobalTheory.CompanionTheory.BZMirOnto.isClosed_Mir k n).isClosedEmbedding_subtypeVal.isCompact_preimage
      (Topo.isCompact_congGL s hs (n + 1))⟩

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugateInverseRightAction
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD

noncomputable section

namespace GlobalTheory.CompanionTheory.DualMapAct

theorem act_dual : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ (o : Op E a) (φ : Sm E a)
    (h1 : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a)
    (h2 : (fun g => star ((act (invTOp o) φ).1 (invA E a g))) ∈ Sm E a),
    act o (⟨fun g => star (φ.1 (invA E a g)), h1⟩ : Sm E a) =
      ⟨fun g => star ((act (invTOp o) φ).1 (invA E a g)), h2⟩ :=
  fun o φ _ _ => GlobalTheory.CompanionTheory.DualAct.act_star_invT o φ _ _ (fun _ => rfl) (fun _ => rfl)

end GlobalTheory.CompanionTheory.DualMapAct

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugationInvariantValuationField
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.FieldVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem injective_of_isField {K L : Type} [CommRing K] [Ring L] [Nontrivial L] (hK : IsField K)
    (f : K →+* L) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun y hy => ?_
  by_contra hne
  obtain ⟨z, hz⟩ := hK.mul_inv_cancel hne
  have : f (y * z) = 1 := by rw [hz, map_one]
  rw [map_mul, hy, zero_mul] at this
  exact zero_ne_one this

theorem absBar_finEmb_eq (hK : IsField (Fv F v ⊗[F] E)) (τ τ' : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    absBar F v (finEmb F v τ y) = absBar F v (finEmb F v τ' y) := by
  have h1 := minpoly.algHom_eq (finEmb F v τ) (injective_of_isField hK (finEmb F v τ).toRingHom) y
  have h2 := minpoly.algHom_eq (finEmb F v τ') (injective_of_isField hK (finEmb F v τ').toRingHom) y
  apply NNReal.eq
  change spectralNorm (Fv F v) (FvBar F v) _ = spectralNorm (Fv F v) (FvBar F v) _
  unfold spectralNorm
  rw [h1, h2]

theorem absFin_eq (hK : IsField (Fv F v ⊗[F] E)) (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    absFin F v y = absBar F v (finEmb F v τ y) := by
  refine le_antisymm ((absFin_le_iff F v).2 fun τ' => (absBar_finEmb_eq v hK τ' τ y).le) (le_absFin F v τ y)

theorem finEmb_sigR (σ : E →ₐ[F] E) (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    finEmb F v τ (sigR (Fv F v) σ y) = finEmb F v (τ.comp σ) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

theorem exists_valuation : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), IsField (Fv F v ⊗[F] E) →
    ∃ W : Valuation (Fv F v ⊗[F] E) ℝ≥0, (∀ a, W a = absFin F v a) ∧ ∀ a, W (sigR (Fv F v) σ a) = W a := by
  intro F E _ _ _ _ _ σ _ v hK
  let τ₀ : E →ₐ[F] FvBar F v := IsAlgClosed.lift
  refine ⟨(valBar F v).comap (finEmb F v τ₀).toRingHom, fun a => ?_, fun a => ?_⟩
  · exact (absFin_eq v hK τ₀ a).symm
  · change absBar F v (finEmb F v τ₀ (sigR (Fv F v) σ a)) = absBar F v (finEmb F v τ₀ a)
    rw [finEmb_sigR]
    exact absBar_finEmb_eq v hK _ _ a

end GlobalTheory.CompanionTheory.KFin.FieldVal

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.GL3BlockMatrixLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_zero_eq {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    blk h w m 0 = CtLevel.dgM h w m := by
  ext1
  rw [CtLevel.blk_val, CtLevel.dgM_val, CtLevel.dgMat, Matrix.mul_zero]

theorem continuous_dgM {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous (CtLevel.dgM h w : GLw a w × GLw b w → GLw n w) := by
  have e : (CtLevel.dgM h w : GLw a w × GLw b w → GLw n w) = fun k =>
      ((CtLevel.dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) k.1 *
        ((CtLevel.dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) k.2 := by
    funext k
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply, ← map_mul]
    simp
  rw [e]
  exact ((CtLevel.continuous_dgM_inl h w).comp continuous_fst).mul
    ((CtLevel.continuous_dgM_inr h w).comp continuous_snd)

theorem dgM_entries {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w) :
    (∀ i j, (CtLevel.dgM h w k).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = k.1.val i j) ∧
      ∀ i j, (CtLevel.dgM h w k).val (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = k.2.val i j := by
  constructor <;> intro i j <;>
    rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply] <;> simp

theorem blocks_mem_KGL {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w)
    (hk : CtLevel.dgM h w k ∈ GlobalTheory.LFun.KGL w n) : k.1 ∈ GlobalTheory.LFun.KGL w a ∧ k.2 ∈ GlobalTheory.LFun.KGL w b := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  rw [← map_inv] at h2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · have := h1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(dgM_entries h w k).1] at this
  · have := h2 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(dgM_entries h w k⁻¹).1] at this
  · have := h1 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(dgM_entries h w k).2] at this
  · have := h2 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(dgM_entries h w k⁻¹).2] at this

theorem constant_term_bi_invariant {a b n : ℕ} (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w))
    (hKK : K' ≤ GlobalTheory.LFun.KGL w n) (hN : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K')
    (f : GLw n w → ℂ) (hf : ∀ k₁ ∈ K', ∀ k₂ ∈ K', ∀ g, f (k₁ * g * k₂) = f g)
    (x y : GLw n w) (hx : x ∈ GlobalTheory.LFun.KGL w n) (hy : y ∈ GlobalTheory.LFun.KGL w n)
    (k₁ k₂ : GLw a w × GLw b w) (hk₁ : k₁ ∈ leviOf h w K') (hk₂ : k₂ ∈ leviOf h w K')
    (m : GLw a w × GLw b w) : phi3 h w f x y (k₁ * m * k₂) = phi3 h w f x y m := by
  have hd₁ : CtLevel.dgM h w k₁ ∈ K' := by
    have : blk h w k₁ 0 ∈ K' := hk₁
    rwa [blk_zero_eq] at this
  have hd₂ : CtLevel.dgM h w k₂ ∈ K' := by
    have : blk h w k₂ 0 ∈ K' := hk₂
    rwa [blk_zero_eq] at this
  obtain ⟨h11, h12⟩ := blocks_mem_KGL h w k₁ (hKK hd₁)
  obtain ⟨h21, h22⟩ := blocks_mem_KGL h w k₂ (hKK hd₂)
  have hab : absHalf w ((k₁ * m * k₂).1.val.det ^ b / (k₁ * m * k₂).2.val.det ^ a) =
      absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
    rw [(absHalf_blockDet_KGL_invariant E a b w (k₁ * m) k₂ h21 h22).2]
    exact (absHalf_blockDet_KGL_invariant E a b w m k₁ h11 h12).1
  have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      f (x⁻¹ * blk h w (k₁ * m * k₂) (Multiplicative.toAdd X) * y)) =
      fun X => (fun Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y))
        (Multiplicative.ofAdd (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val)) := by
    funext X
    rw [(CtLevel.blk_mul_dgM E a b n h w (k₁ * m) k₂ _).2, (CtLevel.blk_mul_dgM E a b n h w m k₁ _).1]
    have hc₁ : x⁻¹ * CtLevel.dgM h w k₁ * x ∈ K' := by
      simpa using hN x⁻¹ (inv_mem hx) _ hd₁
    have hc₂ : y⁻¹ * CtLevel.dgM h w k₂ * y ∈ K' := by
      simpa using hN y⁻¹ (inv_mem hy) _ hd₂
    have e2 : x⁻¹ * (CtLevel.dgM h w k₁ * blk h w m (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val) *
        CtLevel.dgM h w k₂) * y =
        (x⁻¹ * CtLevel.dgM h w k₁ * x) *
          (x⁻¹ * blk h w m (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val) * y) *
          (y⁻¹ * CtLevel.dgM h w k₂ * y) := by group
    rw [e2, hf _ hc₁ _ hc₂]
    rfl
  unfold phi3
  rw [hab, e, HintInv.hint_intMat_mul_mul E a b w (fun Y => f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y))
    k₂.1 k₂.2⁻¹ h21 (inv_mem h22)]

theorem constant_term_support {a b n : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (x y : GLw n w)
    (m : GLw a w × GLw b w) (hm : phi3 h w f x y m ≠ 0) :
    ∃ X, blk h w m X ∈ ({x} : Set (GLw n w)) * tsupport f * {y⁻¹} := by
  obtain ⟨X, hX⟩ := CtLevel.exists_ne_zero_of_hint_ne_zero _ _ (right_ne_zero_of_mul hm)
  refine ⟨Multiplicative.toAdd X, ?_⟩
  have e : blk h w m (Multiplicative.toAdd X) =
      x * (x⁻¹ * blk h w m (Multiplicative.toAdd X) * y) * y⁻¹ := by group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul rfl (subset_tsupport _ hX)) rfl

theorem constant_term_compact_support {a b n : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ)
    (hf : HasCompactSupport f) (x y : GLw n w) : HasCompactSupport (phi3 h w f x y) := by
  set C : Set (GLw n w) := ({x} : Set (GLw n w)) * tsupport f * {y⁻¹} with hCdef
  have hC : IsCompact C := (isCompact_singleton.mul hf).mul isCompact_singleton
  let ψ : GLw n w → ((Matrix (Fin a) (Fin a) (w.adicCompletion E) × (Matrix (Fin a) (Fin a) (w.adicCompletion E))ᵐᵒᵖ) ×
      (Matrix (Fin b) (Fin b) (w.adicCompletion E) × (Matrix (Fin b) (Fin b) (w.adicCompletion E))ᵐᵒᵖ)) :=
    fun g => ((CtLevel.blkTL h g.val, MulOpposite.op (CtLevel.blkTL h (g⁻¹).val)),
      (CtLevel.blkBR h g.val, MulOpposite.op (CtLevel.blkBR h (g⁻¹).val)))
  have hψ : Continuous ψ := by
    refine ((((CtLevel.continuous_blkTL h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((CtLevel.continuous_blkTL h).comp Units.continuous_coe_inv))).prodMk
      (((CtLevel.continuous_blkBR h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((CtLevel.continuous_blkBR h).comp Units.continuous_coe_inv))))
  let ι : GLw a w × GLw b w → _ := Prod.map (Units.embedProduct (Matrix (Fin a) (Fin a) (w.adicCompletion E)))
    (Units.embedProduct (Matrix (Fin b) (Fin b) (w.adicCompletion E)))
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct
  have hιψ : ∀ m X, ι m = ψ (blk h w m X) := by
    intro m X
    simp only [ι, ψ, Prod.map, Units.embedProduct_apply, CtLevel.blk_inv, CtLevel.blkTL_blk, CtLevel.blkBR_blk,
      Prod.fst_inv, Prod.snd_inv]
  have hT : IsCompact (ψ '' C) := hC.image hψ
  refine HasCompactSupport.intro' (hι.isCompact_preimage hT) (hT.isClosed.preimage hι.continuous) ?_
  intro m hm
  by_contra hne
  obtain ⟨X, hX⟩ := constant_term_support h w f x y m hne
  exact hm ⟨blk h w m X, hX, (hιψ m X).symm⟩

theorem constant_term_locally_constant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f : GLw n w → ℂ, IsHk K' f → ∀ x ∈ X, ∀ y ∈ X, IsLocallyConstant (phi3 h w f x y) ∧ HasCompactSupport (phi3 h w f x y) ∧ ∀ k₁ ∈ leviOf h w K', ∀ k₂ ∈ leviOf h w K', ∀ m, phi3 h w f x y (k₁ * m * k₂) = phi3 h w f x y m := by
  intro E _ _ _ n a b h w K' hKo hKK hN X hXK _ f hf x hx y hy
  have hbi := constant_term_bi_invariant h w K' hKK hN f hf.2.2.2 x y (hXK x hx) (hXK y hy)
  refine ⟨?_, constant_term_compact_support h w f hf.2.2.1 x y, fun k₁ h₁ k₂ h₂ m => hbi k₁ k₂ h₁ h₂ m⟩
  have hL : IsOpen (leviOf h w K') := by
    have e : leviOf h w K' = (CtLevel.dgM h w) ⁻¹' (K' : Set (GLw n w)) := by
      ext m
      simp only [leviOf, Set.mem_setOf_eq, Set.mem_preimage, blk_zero_eq, SetLike.mem_coe]
    rw [e]
    exact hKo.preimage (continuous_dgM h w)
  have h1 : (1 : GLw a w × GLw b w) ∈ leviOf h w K' := by
    show blk h w 1 0 ∈ K'
    rw [blk_zero_eq, map_one]
    exact K'.one_mem
  rw [IsLocallyConstant.iff_exists_open]
  intro m
  refine ⟨(fun m' => m⁻¹ * m') ⁻¹' leviOf h w K', hL.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using h1
  · intro m' hm'
    have := hbi 1 (m⁻¹ * m') h1 hm' m
    simpa [mul_assoc] using this

end GlobalTheory.CompanionTheory.GL3BlockMatrixLocal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffAdjugateEntry
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp GlobalTheory.CompanionTheory.WaveCp.Rep GlobalTheory.CompanionTheory.WaveCp.Rep.Mol
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Mol.HfSmooth

theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y i j) :=
  contDiff_apply_apply ℝ ℂ i j

theorem contDiff_det {n : ℕ} {M : Mat n → Mat n} (hM : ∀ i j, ContDiff ℝ ∞ (fun y => M y i j)) :
    ContDiff ℝ ∞ (fun y => (M y).det) := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => hM _ _

theorem contDiff_adjugate_entry {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ∞ (fun y : Mat n => y.adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det fun a b => ?_
  by_cases h : a = j
  · subst h
    simpa [Matrix.updateRow_self] using contDiff_const
  · simpa [Matrix.updateRow_ne h] using contDiff_entry a b

theorem contDiffOn_inv {n : ℕ} : ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹) (GLs n) := by
  have hd : ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹) (GLs n) :=
    (contDiff_det (M := id) contDiff_entry).contDiffOn.inv (fun y hy => hy)
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  refine (hd.mul (contDiff_adjugate_entry i j).contDiffOn).congr fun y _ => ?_
  simp [Matrix.inv_def, Ring.inverse_eq_inv]

end GlobalTheory.CompanionTheory.WaveCp.Rep.Mol.HfSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkOneVal
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.UnipLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_one_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w 1 X)⁻¹ = blk h w 1 (-X) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [GlobalTheory.LeviFubini.blk_mul_blk]
  simpa using GlobalTheory.LeviFubini.blk_one_zero h w

theorem blk_one_corner {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (i : Fin a) (j : Fin b) :
    (blk h w 1 X).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j)) = X i j := by
  rw [CtLevel.blk_val]
  simp

theorem continuous_blk_one_val {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (blk h w 1 X).val := by
  refine continuous_matrix fun i j => ?_
  obtain ⟨i, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j, rfl⟩ := (CtLevel.blkEq h).surjective j
  simp only [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · simpa using continuous_const
  · simpa using continuous_id.matrix_elem i j
  · simpa using continuous_const
  · simpa using continuous_const

theorem continuous_blk_one {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => blk h w 1 X := by
  refine Units.continuous_iff.2 ⟨continuous_blk_one_val h w, ?_⟩
  have e : (fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (((blk h w 1 X)⁻¹ : GLw n w)).val) =
      (fun X => (blk h w 1 X).val) ∘ fun X => -X := by
    funext X
    simp [blk_one_inv]
  exact e ▸ (continuous_blk_one_val h w).comp continuous_neg

def intSub (a b : ℕ) (w : Pl E) : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) where
  carrier := {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}
  one_mem' := fun i j => by simp
  mul_mem' := fun {X Y} hX hY i j => by
    simpa using (Valued.v.map_add _ _).trans (max_le (hX i j) (hY i j))
  inv_mem' := fun {X} hX i j => by simpa using hX i j

theorem intMat_eq_intSub (a b : ℕ) (w : Pl E) : intMat a b w = intSub a b w := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun X hX => hX) fun X hX => Subgroup.subset_closure hX

theorem isCompact_intSub (a b : ℕ) (w : Pl E) :
    IsCompact (intSub a b w : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) := by
  have e : (intSub a b w : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) =
      Multiplicative.toAdd ⁻¹' (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ
        fun _ : Fin b => ((w.adicCompletionIntegers E : Set (w.adicCompletion E)))) := by
    ext X
    exact ⟨fun hX i _ j _ => hX i j, fun hX i j => hX i trivial j trivial⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers w

theorem unip_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) ≤ intMat a b w ∧ ((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w)).relIndex (intMat a b w) ≠ 0 := by
  intro E _ _ _ a b n h w K' hK' hKK
  have hmem : ∀ X, X ∈ (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) ↔
      blk h w 1 (Multiplicative.toAdd X) ∈ K' := fun X => Iff.rfl
  refine ⟨fun X hX => ?_, ?_⟩
  · rw [intMat_eq_intSub]
    intro i j
    obtain ⟨u, hu⟩ := hKK ((hmem X).1 hX)
    have h1 : Valued.v ((blk h w 1 (Multiplicative.toAdd X)).val (CtLevel.blkEq h (Sum.inl i))
        (CtLevel.blkEq h (Sum.inr j))) ≤ 1 := by
      rw [← hu]
      exact (u.val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j))).2
    rwa [blk_one_corner] at h1
  · have hopen : IsOpen (((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) :
        Subgroup _) : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) :=
      hK'.preimage ((continuous_blk_one h w).comp continuous_toAdd)
    rw [intMat_eq_intSub]
    haveI : CompactSpace (intSub a b w) := isCompact_iff_compactSpace.1 (isCompact_intSub a b w)
    haveI : Finite ((intSub a b w) ⧸ ((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w)).subgroupOf (intSub a b w)) :=
      Subgroup.quotient_finite_of_isOpen _ (hopen.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.UnipLevel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_levi_unipotent_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (levi k n) ∧ Continuous (uM k n) ∧ Continuous (mirabolicProjection k n) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj | exact GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirabolicEmbeddingStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_mirabolic_embedding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (embedding₂ k n) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM | exact GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousParabolicProjStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi | exact GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi <;> assumption)
end

